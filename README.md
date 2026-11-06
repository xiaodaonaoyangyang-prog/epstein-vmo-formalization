# Epstein–VMO formalization (Lean 4)

A Lean 4 formalization of the paper *Horoball gaps of quasicircles: curvature, volume, and BMO and VMO
characterizations* (sections 1–13): every definition, lemma, proposition and theorem of the paper is stated in
Lean, and the main theorems are proved.

## Status (2026-11-06)

- **Theorem A is proved.** `EpsteinVMO.thm_A` (`EpsteinVMO/S06_Lower.lean`): for every `K ≥ 1` there are
  `c(K) > 0` and `C(K) < ∞` such that for every `K`-quasicircle, every label and every `p ∈ Ω`,
  `c(K)(K_H(p) + K_*(p)) ≤ K_V(p) ≤ C(K)(K_H(p) + K_*(p))`.
- **Theorem B is proved.** `EpsteinVMO.thm_B_i` / `thm_B_ii` and `cor_B_outer_i` / `cor_B_outer_ii`
  (`EpsteinVMO/S08_ThmB.lean`): BMO and VMO characterizations of bounded quasicircles by the horoball gap volume.
  The proof includes the Shen–Wei characterizations `thm_shen_wei_B5` / `thm_shen_wei_V5`. The BMO half follows
  Bishop–Jones and Astala–Zinsmeister (`EpsteinVMO/S07d_BMO.lean`). The VMO half uses a Fefferman–Kenig–Pipher
  small-perturbation argument (`EpsteinVMO/S07c_FKPSmall.lean`).
- `#print axioms` for `thm_A`, `thm_B_i`, `thm_B_ii`, `cor_B_outer_i` and `cor_B_outer_ii` reports only `propext`,
  `Classical.choice` and `Quot.sound`.
- **23 `sorry` remain**, in later sections only. None of them is used by Theorems A or B.

  | module | sorry | topic |
  |---|---|---|
  | `S04_Tube` | 1 | `lem_Cj` (a leaf, not used elsewhere) |
  | `S09_Ambient` | 7 | Theorem E line, ambient comparisons |
  | `S10_Sharp` | 7 | Theorems C and D: interior Schauder estimates, duality |
  | `S11_HalfPlane` | 8 | half-plane welding and VMOA lemmas |

  `collaboration/DEEP_WALLS.md` explains, for each one, the external theory it needs.
- Size: about 127k lines of Lean in `EpsteinVMO/`, with about 3.1k theorems (counting helpers).

## Statement fidelity

- `ERRATA.md` lists the paper statements that are false or imprecise as written. No paper theorem was found to be
  false. Three statements are formalized with an evident missing hypothesis added. It also lists the gaps found in
  cited sources.
- `collaboration/STATEMENT_CHANGES.md` logs corrections to Lean statements made during the proof phase.
- `STATUS.md` is a snapshot from 2026-11-04, taken before Theorem B was completed.

## Layout

| path | contents |
|---|---|
| `EpsteinVMO/Defs.lean` | basic definitions: upper half-space, horoballs, gaps, Epstein surfaces, Carleson/BMOA/VMOA |
| `EpsteinVMO/S02_Prelim.lean` … `S13_Open.lean` | one module per paper section |
| `EpsteinVMO/S07b_ShenWei.lean`, `S07c_FKPSmall.lean`, `S07d_BMO.lean` | Shen–Wei characterizations, FKP small perturbation, BMO route |
| `EpsteinVMO/PDE_Dirichlet.lean` | the Dirichlet problem input used in §5 |
| `TauCeti/`, `VanishingCarleson/`, `DouadyEarleExt/` | vendored libraries; see `VENDORED.md` |

## Building

The project uses Lean `v4.36.0-rc2` (`lean-toolchain`) and Mathlib at tag `v4.36.0-rc2` (commit `9d581dff`). It
depends on two companion projects:

- [Li-Zhong-QC-formalization](https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization) (`LiZhongQC`);
- [takhtajan_teo_wp](https://github.com/xiaodaonaoyangyang-prog/takhtajan_teo_wp) (`TakhtajanTeo`).

`lakefile.toml` points to local checkouts (`D:/lean/...`). To build elsewhere, replace the three path `[[require]]`
blocks with git requirements, and delete the `packagesDir` line:

```toml
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "v4.36.0-rc2"

[[require]]
name = "lizhong_quasiconformal_teichmuller"
git = "https://github.com/xiaodaonaoyangyang-prog/Li-Zhong-QC-formalization"
rev = "main"

[[require]]
name = "takhtajan_teo_wp"
git = "https://github.com/xiaodaonaoyangyang-prog/takhtajan_teo_wp"
rev = "main"
```

Each companion project also points to a local Mathlib checkout. Apply the same Mathlib replacement in those projects,
as described in their READMEs. Then run:

```
lake update
lake exe cache get
lake build
```

Building LiZhongQC and TakhtajanTeo from source takes several hours.

## License

Apache License 2.0 (`LICENSE`). The vendored `TauCeti/` files are Apache 2.0 by their authors (`TauCeti/LICENSE`;
provenance in `VENDORED.md`).
