# Source identities and build instructions

## Verify the sources

From the repository root, run:

```sh
python -I -B scripts/check_sources.py
```

This verifies the SHA-256 and byte length of all 2,205 proof files and the two
copied Rocq environment records. It also detects extra proof files in the
distributed source trees. Python 3.10 or later is sufficient; no third-party
Python packages are required.

[SOURCE_MANIFEST.json](SOURCE_MANIFEST.json) maps each distributed proof file
to its path within one of three frozen releases. It records the SHA-256 of
each original release manifest. All selected source files were checked against
those manifests during packaging. The new repository documentation, licence,
build configuration, and source-check script are outside that source manifest.
Git records their versions.

## Lean

The committed configuration pins:

- Lean `leanprover/lean4:v4.31.0`.
- Mathlib commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- The eight transitive Git dependency revisions in
  [`lean/lake-manifest.json`](lean/lake-manifest.json), copied from the frozen
  Mathlib dependency lock.

With `elan` installed, the project build command is:

```sh
cd lean
lake build
```

The default library target selects every submodule of `Sharpness`, covering
all 957 Lean source modules. Keep the committed lockfile when reproducing this
revision; do not run an unrestricted `lake update`.

The first invocation can download a missing toolchain or dependency and can
start a substantial dependency compilation. The original validation used
pinned library builds. It does not certify a fresh dependency bootstrap or
this new repository layout. No toolchain installation, dependency download,
Lake configuration elaboration, or Lean build was performed for publication.

## Rocq

Use Linux or WSL with the following installed environment:

| Component | Version |
| --- | --- |
| Rocq | 9.1.0 |
| Rocq Stdlib | 9.0.0 |
| Mathematical Components | 2.5.0 |
| MathComp Analysis and Classical | 1.16.0 |
| Hierarchy Builder | 1.10.2 |
| OCaml | 4.14.2 |

[`toolchain/rocq-switch.export`](toolchain/rocq-switch.export) is the unchanged
opam switch export from the baseline release.
[`toolchain/rocq-installed-packages.json`](toolchain/rocq-installed-packages.json)
records the complete installed package versions. These are environment records;
the dependencies and compiled libraries themselves are not vendored.

From the repository root, with the pinned environment active and GNU Make
installed, generate the build rules and compile:

```sh
cd rocq
coq_makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq -j2
```

[`rocq/_CoqProject`](rocq/_CoqProject) explicitly lists all 1,248 sources and
maps the five directories to their original logical prefixes. Generated rules
resolve compilation order. The paths are relative to `rocq`; run the commands
from that directory. Generated makefiles and build products are ignored by Git.

These commands describe an ordinary project compilation. They do not recreate
the historical type/assumption queries, dependency audits, or the separately
recorded dependency-inclusive kernel checks. The new `_CoqProject` has been
checked for complete file coverage and relative paths, but has not been built.

## Scope of this distribution

The repository contains unchanged proof sources, pinned environment records,
and build instructions. It excludes the nested release ZIPs, vendored libraries,
compiled objects, manuscript, report, and private working records. Historical
release validators depend on the complete original archive and evidence layout;
they are not included as builders for this source distribution.

The historical release manifests are identified in `SOURCE_MANIFEST.json` as:

| Release | Manifest SHA-256 |
| --- | --- |
| v2.8 b2 and E3 | `a33910da2d37b261ae82aadb34534c8626e0e6835998f0fbeddcf2f19d8c7822` |
| v2.9 alignment | `36cb807254674c5b7d242c17f9e764a45f3efd2fb156e0e12cdc6bea364bab6c` |
| BLO centralizer supplement | `012a0ee56a65ea7221bbafb35ae94c3e5c0d1818c06f559f53c477ae5ba93ff5` |

The new source-layout checks establish byte identity and packaging consistency.
They do not constitute a fresh compilation or proof validation.
