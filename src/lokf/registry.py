"""Cross-bundle federation: a registry of LOKF bundles (*meta-lokf*).

A registry (``lokf-registry.yaml``) maps each member bundle's ``base_iri`` to
where its exported artifacts and source documents live. The one load-bearing
operation is :meth:`Registry.owner` — longest-``base_iri``-prefix routing, the
exact inverse of :meth:`lokf.model.Bundle.iri` minting — so following an IRI
from one bundle into another is pure string math: no network, no shared
database. See SPEC §11.

This module is the offline core (Phase 1): loading/saving the manifest,
building an entry from a local bundle or a released bundle archive, and
resolving an IRI to its owning bundle + Concept ID + source URL. Harvesting
remote artifacts and traversing a federated store land in later phases.
"""
from __future__ import annotations

import dataclasses
import hashlib
import pathlib
import re
import shutil
import tempfile
import urllib.request
import zipfile
from collections import Counter
from dataclasses import dataclass, field

import yaml

#: The ontology ``@vocab``. Never a repo ``base_iri`` — an IRI under it that no
#: (strictly longer) member owns is a vocabulary term, not a foreign concept.
VOCAB_NS = "https://w3id.org/lokf/"
REGISTRY_VERSION = "0.1"
DEFAULT_REGISTRY = "lokf-registry.yaml"
#: Ceiling on a bundle archive's size, downloaded and unpacked, so a hostile
#: zip or an endless response cannot fill the disk.
MAX_ARCHIVE_BYTES = 1 << 30
_CHECKSUM = re.compile(r"^(?:sha256:)?([0-9a-fA-F]{64})$")


@dataclass
class RepoEntry:
    """One member bundle. ``base_iri`` is its identity and routing key."""

    base_iri: str
    title: str = ""
    repo: str | None = None
    source_base: str = ""
    path: str | None = None
    distribution: dict = field(default_factory=dict)
    checksum: str | None = None  # "sha256:<hex>" of the archive it was registered from
    void: dict = field(default_factory=dict)
    id_index: dict = field(default_factory=dict)  # explicit-id IRI -> Concept ID
    sensitivity: str | None = None
    status: str = "ok"


@dataclass
class Resolution:
    """The result of resolving an IRI against a registry."""

    iri: str
    entry: RepoEntry | None
    concept_id: str | None
    source_url: str | None
    via: str | None  # "prefix" | "id_index" | None

    @property
    def external(self) -> bool:
        """True when no member owns the IRI (a tolerated dangling link)."""
        return self.entry is None


def _source_url(entry: RepoEntry, concept_id: str | None) -> str | None:
    """A concept's source-markdown URL: ``source_base``/``concept_id``.md.

    Returns ``None`` when the entry has no ``source_base`` or the IRI is the
    bundle's namespace root (empty Concept ID) — neither names a document.
    """
    if not entry.source_base or not concept_id:
        return None
    return entry.source_base.rstrip("/") + "/" + concept_id + ".md"


@dataclass
class Registry:
    """A registry of LOKF bundles, loaded from ``lokf-registry.yaml``."""

    path: pathlib.Path
    id: str = ""
    title: str = ""
    publisher: dict = field(default_factory=dict)
    version: str = REGISTRY_VERSION
    repos: list[RepoEntry] = field(default_factory=list)

    # -- resolution ---------------------------------------------------------
    def _match(self, iri: str) -> tuple[RepoEntry | None, str | None, str | None]:
        """(entry, via, concept_id) for *iri*, or (None, None, None).

        Longest-``base_iri``-prefix wins; another member's ``id_index`` is
        only a *fallback* for an IRI that no base_iri prefixes (SPEC §11 rule
        1), so a stale index entry can never hijack an IRI a member owns by
        prefix. The owner's own ``id_index`` does name the concept, though: an
        explicit ``id`` under its base_iri that differs from base_iri + Concept
        ID would otherwise route to a document that does not exist.
        """
        best: RepoEntry | None = None
        for e in self.repos:
            if e.base_iri and iri.startswith(e.base_iri):
                if best is None or len(e.base_iri) > len(best.base_iri):
                    best = e
        if best is not None:
            if iri in best.id_index:
                return best, "id_index", best.id_index[iri]
            return best, "prefix", iri[len(best.base_iri):].lstrip("/")
        for e in self.repos:
            if iri in e.id_index:
                return e, "id_index", e.id_index[iri]
        return None, None, None

    def owner(self, iri: str) -> RepoEntry | None:
        """The member bundle that owns *iri*, or ``None`` if external."""
        return self._match(iri)[0]

    def resolve(self, iri: str) -> Resolution:
        """Resolve *iri* to its owning bundle, Concept ID, and source URL."""
        entry, via, concept_id = self._match(iri)
        return Resolution(
            iri=iri,
            entry=entry,
            concept_id=concept_id,
            source_url=_source_url(entry, concept_id) if entry else None,
            via=via,
        )

    # -- mutation -----------------------------------------------------------
    def add(self, entry: RepoEntry) -> None:
        """Validate and append *entry*. Raises ``ValueError`` on conflict.

        A base_iri must be non-empty, end in a path separator (``/`` or ``#``)
        so prefix routing respects segment boundaries (``…/team/`` never
        captures ``…/team-archive/``), stay clear of the vocabulary namespace,
        and neither duplicate nor nest with an existing member (either would
        make routing ambiguous).
        """
        b = entry.base_iri
        if not b:
            raise ValueError("entry has no base_iri")
        if not b.endswith(("/", "#")):
            raise ValueError(f"base_iri must end with '/' or '#': {b!r}")
        if VOCAB_NS.startswith(b):
            raise ValueError(
                f"base_iri {b!r} captures the vocabulary namespace {VOCAB_NS}; "
                "a member base_iri must be strictly longer"
            )
        for e in self.repos:
            if e.base_iri == b:
                raise ValueError(f"base_iri already registered: {b}")
            if b.startswith(e.base_iri) or e.base_iri.startswith(b):
                raise ValueError(
                    f"base_iri {b!r} nests with registered {e.base_iri!r}; "
                    "base_iris must not be prefixes of one another"
                )
        # An explicit id may lie outside its own base_iri (SPEC §11.3 rule 1),
        # but never inside another member's namespace or the vocabulary's, in
        # either order of registration: prefix routing would win and the index
        # entry would never route, or it would claim a namespace it does not own.
        for iri in entry.id_index:
            if iri.startswith(VOCAB_NS):
                raise ValueError(f"explicit id {iri} lies in the vocabulary namespace")
            for e in self.repos:
                if iri.startswith(e.base_iri):
                    raise ValueError(
                        f"explicit id {iri} lies in registered {e.base_iri!r}"
                    )
        for e in self.repos:
            for iri in e.id_index:
                if iri.startswith(b):
                    raise ValueError(
                        f"base_iri {b!r} captures explicit id {iri} "
                        f"of registered {e.base_iri!r}"
                    )
        self.repos.append(entry)

    def to_dict(self) -> dict:
        """The manifest as a plain dict for YAML serialization."""
        d: dict = {"lokf_registry_version": self.version, "type": "dcat:Catalog"}
        if self.id:
            d["id"] = self.id
        if self.title:
            d["title"] = self.title
        if self.publisher:
            d["publisher"] = self.publisher
        d["repos"] = [_entry_dict(e) for e in self.repos]
        return d

    def save(self) -> None:
        """Write the manifest back to :attr:`path` (block-style YAML)."""
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.path.write_text(
            yaml.safe_dump(self.to_dict(), sort_keys=False, allow_unicode=True),
            encoding="utf-8",
        )


_FIELDS = dataclasses.fields(RepoEntry)
_ENTRY_FIELDS = {f.name for f in _FIELDS}
_ENTRY_DEFAULTS = {
    f.name: (f.default_factory() if f.default_factory is not dataclasses.MISSING else f.default)
    for f in _FIELDS
}


def _entry_dict(entry: RepoEntry) -> dict:
    """A RepoEntry as a dict, dropping fields left at their default value."""
    out = {}
    for k, v in dataclasses.asdict(entry).items():
        if k != "base_iri" and v == _ENTRY_DEFAULTS.get(k):
            continue
        out[k] = v
    return out


def load_registry(path: str | pathlib.Path) -> Registry:
    """Load ``lokf-registry.yaml`` with a plain YAML reader (no LinkML).

    Tolerant of a hand-edited manifest: a null ``repos:`` or null field values
    fall back to defaults rather than crashing a later lookup.
    """
    p = pathlib.Path(path)
    try:
        data = yaml.safe_load(p.read_text(encoding="utf-8")) or {}
    except yaml.YAMLError as exc:
        raise ValueError(f"{p}: not valid YAML: {exc}") from None
    if not isinstance(data, dict):
        raise ValueError(f"{p}: registry must be a YAML mapping, got {type(data).__name__}")
    entries = data.get("repos") or []
    if not isinstance(entries, list):
        raise ValueError(f"{p}: 'repos' must be a list")
    repos = [
        RepoEntry(**{k: v for k, v in (r or {}).items() if k in _ENTRY_FIELDS and v is not None})
        for r in entries
    ]
    return Registry(
        path=p,
        id=data.get("id") or "",
        title=data.get("title") or "",
        publisher=data.get("publisher") or {},
        version=str(data.get("lokf_registry_version") or REGISTRY_VERSION),
        repos=repos,
    )


def entry_for_bundle(
    bundle_dir: str | pathlib.Path,
    source_base: str | None = None,
    allow_foreign_ids: bool = False,
) -> RepoEntry:
    """Build a :class:`RepoEntry` from a local bundle directory.

    Derives ``base_iri``/``title``/``publisher`` from the bundle's ``index.md``,
    computes a VoID planning index (triple + per-type counts), and harvests an
    ``id_index`` of explicit-``id`` IRIs that diverge from ``base_iri`` +
    Concept ID (so they still route). ``path`` records the local directory only
    when no ``source_base`` is given, since the directory then is the source.

    Raises ``ValueError`` if the bundle has no ``base_iri``, or if an explicit
    ``id`` lies outside ``base_iri`` and *allow_foreign_ids* is false: a bundle
    must declare that it mints IRIs in a namespace it does not route by prefix
    (SPEC §11.3 rule 3).
    """
    from lokf.model import load_bundle

    bundle = load_bundle(bundle_dir)
    base_iri = bundle.base_iri
    if not base_iri:
        raise ValueError(f"{bundle_dir}: bundle index.md has no base_iri; cannot federate")

    id_index: dict[str, str] = {}
    for c in bundle.concepts:
        actual = bundle.iri(c)
        if actual != base_iri + c.concept_id:  # explicit id diverges from the mint rule
            id_index[actual] = c.concept_id

    foreign = sorted(iri for iri in id_index if not iri.startswith(base_iri))
    if foreign and not allow_foreign_ids:
        raise ValueError(
            f"{len(foreign)} explicit id(s) lie outside base_iri {base_iri}, "
            f"first {foreign[0]}; allow foreign ids to index them"
        )

    part = Counter(c.type for c in bundle.concepts)
    void = {"triples": len(bundle.graph()), "class_partition": dict(part)}

    root = pathlib.Path(bundle_dir).resolve()
    return RepoEntry(
        base_iri=base_iri,
        title=bundle.meta.get("title") or base_iri,
        source_base=source_base or root.as_uri(),
        path=None if source_base else str(root),
        void=void,
        id_index=id_index,
    )


def is_url(source: str) -> bool:
    """True when *source* names an archive to download rather than a local path."""
    return source.startswith(("https://", "http://"))


def _sha256(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return "sha256:" + h.hexdigest()


def _download(url: str, dest: pathlib.Path) -> None:
    """Stream *url* into *dest*, refusing more than :data:`MAX_ARCHIVE_BYTES`."""
    with urllib.request.urlopen(url, timeout=60) as resp, dest.open("wb") as out:
        total = 0
        for chunk in iter(lambda: resp.read(1 << 20), b""):
            total += len(chunk)
            if total > MAX_ARCHIVE_BYTES:
                raise ValueError(f"{url} is larger than {MAX_ARCHIVE_BYTES} bytes")
            out.write(chunk)


def _unpack(archive: pathlib.Path, dest: pathlib.Path) -> pathlib.Path:
    """Unpack a bundle zip into *dest* and return the bundle's root directory.

    The root is *dest* itself when the zip carries ``index.md`` at its top, or
    the one top-level directory that does (a KTL release zip's ``knowledge/``).
    Members with absolute or ``..`` paths, and zips that unpack to more than
    :data:`MAX_ARCHIVE_BYTES`, are refused before anything is written.
    """
    if not zipfile.is_zipfile(archive):
        raise ValueError(f"{archive.name} is not a zip archive")
    dest.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(archive) as zf:
        infos = zf.infolist()
        for info in infos:
            parts = pathlib.PurePosixPath(info.filename).parts
            if info.filename.startswith(("/", "\\")) or ".." in parts:
                raise ValueError(f"{archive.name}: unsafe member path {info.filename!r}")
        if sum(i.file_size for i in infos) > MAX_ARCHIVE_BYTES:
            raise ValueError(f"{archive.name} unpacks to more than {MAX_ARCHIVE_BYTES} bytes")
        zf.extractall(dest)
    if (dest / "index.md").is_file():
        return dest
    roots = [d for d in dest.iterdir() if d.is_dir() and (d / "index.md").is_file()]
    if len(roots) != 1:
        raise ValueError(
            f"{archive.name}: expected index.md at the top or in one top-level "
            f"directory, found {len(roots)}"
        )
    return roots[0]


def entry_for_archive(
    source: str | pathlib.Path,
    source_base: str | None = None,
    checksum: str | None = None,
    allow_foreign_ids: bool = False,
) -> RepoEntry:
    """Build a :class:`RepoEntry` from a released bundle zip, local or at a URL.

    The zip is unpacked to a temporary directory and registered from there, so
    the entry never records a ``path``. Its digest goes in ``checksum``; when
    *checksum* is given (``sha256:<hex>`` or bare hex) a mismatch is refused.
    A URL is recorded as ``distribution.archive``; a local zip's location is
    not, since it is rarely where a reader would find it. Without
    *source_base* the entry has no source URL, as an unpacked copy is gone.
    """
    expected = None
    if checksum:
        m = _CHECKSUM.match(checksum.strip())
        if not m:
            raise ValueError(f"checksum must be sha256:<64 hex digits>, got {checksum!r}")
        expected = "sha256:" + m.group(1).lower()

    tmp = pathlib.Path(tempfile.mkdtemp(prefix="lokf-registry-"))
    try:
        if is_url(str(source)):
            archive = tmp / "bundle.zip"
            _download(str(source), archive)
        else:
            archive = pathlib.Path(source)
        digest = _sha256(archive)
        if expected and digest != expected:
            raise ValueError(f"checksum mismatch: expected {expected}, got {digest}")
        root = _unpack(archive, tmp / "unpacked")
        entry = entry_for_bundle(
            root, source_base=source_base, allow_foreign_ids=allow_foreign_ids
        )
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    entry.path = None
    entry.source_base = source_base or ""
    entry.checksum = digest
    if is_url(str(source)):
        entry.distribution = {"archive": str(source)}
    return entry
