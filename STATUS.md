# Epstein–VMO formalization: status (2026-11-04)

**Paper.** *Horoball gaps of quasicircles: curvature, volume, and BMO and VMO characterizations*, located at
`D:\study\study\ocr\专题-horofunction边界与Gromov紧化\正式稿-Epstein-VMO`.

**Project.** `D:\lean\epstein_vmo`, built with Lean v4.36.0-rc2. It depends on Mathlib, on LiZhongQC and on
TakhtajanTeo, and it vendors VanishingCarleson and DouadyEarleExt (see `VENDORED.md`).

## Build

**2026-11-05 integration build:** `integration_build.ps1`, all 14 modules + root, **0 errors**; 33 `sorry` warnings
(S02 2, S04 1, S07 4, S08 4, S09 7, S10 7, S11 8); `thm_A` axiom-clean against the rebuilt tree
(`collaboration/integ_axioms.log`). The table below is the earlier (127-sorry) build.

The final integration build was run with `collaboration/integration_build.ps1` over all 13 modules and the root
`EpsteinVMO.lean`. It finished with **0 errors**.

| module | sorry | module | sorry |
|---|---|---|---|
| Defs | 0 | S08 Theorem B | 5 |
| S02 Prelim | 7 | S09 Ambient (Thm E) | 11 |
| S03 Coarse | **0** | S10 Sharp (Thm C, D) | 18 |
| S04 Tube | 7 | S11 Half-plane | 29 |
| S05 Upper | 17 | S12 Counter | 10 |
| S06 Lower (Thm A) | 3 | S13 Open problems | 1 |
| S07 Transfer | 19 | **total** | **127** |

- The source contains about 970 `theorem` declarations in about 29k lines. These counts include helpers.
- The skeleton stage started with **291 sorry**; the proof stage closed 164 of them. §3 (coarse geometry) is
  completely proved.
- Every proved declaration that was checked depends only on `[propext, Classical.choice, Quot.sound]`. The checks are
  the per-worker axcheck runs listed in `collaboration/ax_*`.

## Statement fidelity

- **`ERRATA.md`.** No paper theorem was found to be false, so nothing was skipped. Three statements are false as
  literally written and were formalized with the evident missing hypothesis:
  - `lem:jacobian`;
  - `lem:test-functions(b)`;
  - `rem:hp-compatible`.
- **`collaboration/STATEMENT_CHANGES.md`.** Lean-side defects in our own skeleton, fixed after acceptance. Examples are
  `rem_hp_infinity_i_affine`, the relative closedness in `eq_def_D`, and `IsStronglyQS` now requiring a circle
  homeomorphism.
- **Modelling conventions.** These are in the docstring of `EpsteinVMO/Defs.lean`:
  - Möbius-invariant statements are made for curves through ∞;
  - bounded curves are transported by `invAt x₀`;
  - kernel quantities are `ℝ≥0∞`-valued lower integrals.

## What is proved (highlights)

- **§2.** All of these are proved:
  - the Poincaré density formulas, Koebe/Busemann bounds and Epstein-point position;
  - the normal geodesics, `lem_normal_a–d` and the first fundamental form `lem_fff*`;
  - the Grunsky separation `prop_separation_a/b/c/a_infty`, so U ∩ U* = ∅;
  - Borel labels, properness and `eq_dist_U`;
  - the convex-hull inclusion and Möbius naturality.
- **§3 (complete).** All of these are proved:
  - the quasiconformal extension and the three-point condition;
  - the corkscrew and width lemmas;
  - the quasi-isometric Epstein maps, including the 5/2 bound;
  - the quasi-isometric label map R and label-change invariance;
  - convexity along ρ-geodesics and the uniqueness of labels.
- **§5/§6.** Proved items:
  - the test functions, the comparison principle and `eq_adjoint`;
  - `lem_grunsky` (d(B_w,U*) ≥ s²/9, with the constant 1/9 checked), `lem_strips` and `lem_local_mass`;
  - the good-domain lemmas.
- **§7/§8.** Proved items:
  - the kernel test for Carleson and vanishing Carleson measures;
  - `lem_one_sided`, `prop_opposite_b` and the SQS/SS composition and Möbius invariance;
  - the power-map examples;
  - the quantitative remarks on Theorem B.
- **§9.** Proved items:
  - the kernel lemmas and Möbius naturality of V and H, including independence of x₀ for bounded curves;
  - the dictionary lemmas, the box comparisons and the circle case.
- **§10.** Proved items:
  - the plane Green function lemmas (a–f) and `rem_H_finite`;
  - the Ahlfors–Weill lemma `lem_aw`;
  - parts 1 and 3 of Theorem D.
- **§11/§12.** Proved items:
  - the half-plane kernel and Carleson estimates, the A∞/BMO facts and `eq_hp_s`;
  - `lem_hp_label_a/c` and `set_hp_extension`;
  - the cusp example in full, the sector and spacing remarks.

## What remains (127)

Each owner's catalogue gives one line per remaining sorry: `collaboration/REMAINING_w1.md` … `REMAINING_w6.md`.
They fall into three groups.

1. **Infrastructure walls** (new theory that is not in Mathlib or the project):
   - W-COMP: compactness of normalized K-qc Epstein surfaces, the Carathéodory kernel theorem with derivatives, and
     C^j control. This wall blocks `lem_tube`, so all of S04, and `prop_mass_volume`.
   - W-PDE/W-DIV: the Dirichlet problem and the divergence theorem on smooth domains. These block the §5 upper bound.
   - W-MC: linearization of mean curvature.
   - Hyperbolic Morse lemma.
   - Arclength theory.
   - Hyperbolic Green representation.
   - `prop_curvature`: the shape operator.
2. **External citations** that the paper uses without proof:
   - Shen–Wei (BMOA/VMOA ⇔ Carleson ⇔ SQS/SS);
   - [TWS, Prop. 3.5];
   - the Douady–Earle bi-Lipschitz bound;
   - the A∞ inverse theorem;
   - WMUC Lemmas 13/14 and Cor. 10;
   - GCRF reverse Hölder and Hardy–Littlewood;
   - Bishop–Jones / GM X.6.2;
   - Astala–Zinsmeister;
   - Gilbarg–Trudinger Schauder estimates.
3. **Assemblies over 1 and 2.** These include the main theorems themselves:
   - Theorem A needs `thm_upper` and `thm_lower`;
   - Theorem B needs Shen–Wei and the transfer;
   - Theorem C needs the Schauder estimates;
   - Theorem D part 2 needs the injectivity of the kernel transform;
   - Theorem E needs Theorem A's machinery.

## Next-step candidates

These are self-contained items that were estimated but not funded:

| item | lines | effect |
|---|---|---|
| `thm_plane_ratio_a` + `lem_plane_green_g`, then `b`/`c`/`rem_linear_model` | ~2000 | Proves the optimal linearized constants 2(1−log 2) and 1 |
| `prop_opposite_a` (S07) | 650–1050, 2 imports | Elementary route around NOTES gap 14 |
| `lem_counting`, `lem_reproduction` (S05) | 700–900, 300–500 | Closes isolated sorries; their consumers are walled |
| `rem_sector_scope_iii` (S12) | ~400 | Isolated |
| `prop_curvature` (S02) | 600–1500 | Unlocks `lem_shape_b` |
