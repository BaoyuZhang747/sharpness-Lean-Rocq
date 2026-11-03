# Sharpness formalisation in Lean and Rocq

This repository contains the formalisation sources for Díaz–Park sharpness,
the right Kan cohomology supplement, the v2.9 alignment layer, and the BLO
centralizer sharpness supplement. It includes **957 Lean modules** and
**1,248 Rocq modules**.

The proof files are unchanged copies from the frozen releases identified in
[SOURCE_MANIFEST.json](SOURCE_MANIFEST.json). Repository layout and build
configuration have been prepared for this distribution. The formalisation
report will be added separately.

## Source layout

| Component | Lean modules | Rocq modules |
| --- | ---: | ---: |
| v2.8 baseline, including b2 and E3 | 906 | 1,173 |
| v2.9 alignment | 28 | 42 |
| BLO centralizer supplement | 23 | 33 |

Lean sources share the [`Sharpness`](lean/Sharpness) namespace. Rocq sources
retain the logical prefixes `DiazPark`, `DiazParkV16b`, `DiazParkV28`,
`DiazParkV29`, and `DiazParkBLO` under [`rocq`](rocq).

Useful entry points include:

- Main theorem and manuscript alignment: [Lean](lean/Sharpness/V29/Main.lean)
  and [Rocq](rocq/DiazParkV29/MainManuscript.v).
- Right Kan cohomology: [Lean](lean/Sharpness/V28/RightKanCohomology.lean)
  and [Rocq](rocq/DiazParkV28/RightKanCohomology.v).
- BLO centralizer sharpness: [Lean](lean/Sharpness/BLO/BLOEdgeSharpness.lean)
  and [Rocq](rocq/DiazParkBLO/BLOEdgeFinal.v).

The declarations in these files specify their mathematical hypotheses and
conclusions. The BLO supplement concerns cohomology, higher limits, and the
canonical edge map; it does not assert a homotopy equivalence or a p-completion
theorem.

## Check and build

Check the frozen source identities with Python 3.10 or later:

```sh
python -I -B scripts/check_sources.py
```

This command checks hashes and the proof-source inventory. It does not invoke
a proof assistant or download dependencies.

The Lean toolchain is **4.31.0**. The Rocq toolchain is **9.1.0**, with the
library versions recorded in [`toolchain`](toolchain). See
[REPRODUCE.md](REPRODUCE.md) for dependency pins and build commands.

The publication checks covered source identities, source inventory, and build
configuration consistency. **No new formalisation build or kernel replay was
run for this repository layout.** The frozen release manifests identify the
original packages; their historical validation records and compiled objects
are not included here.

## Licence

The project code and repository build instructions are licensed under
[Apache 2.0](LICENSE). See [NOTICE](NOTICE). External libraries retain their
own licences. The manuscript and formalisation report are not included in this
code distribution.
