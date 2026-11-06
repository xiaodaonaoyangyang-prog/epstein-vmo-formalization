# Vendored libraries

The leader vendored these two libraries on 2026-11-03, at the user's prompt to reference `D:\lean\vanishing_carleson`. They
cannot be a lake path dependency: their lakefiles require the git packages `checkdecls` and `doc-gen4`, which are not in
the shared packages directory.

## `VanishingCarleson/` (11 modules)

- **Source.** `D:/lean/vanishing_carleson`. That project is the formalization of *Vanishing Carleson measures for the
  Douady–Earle extension of strongly symmetric homeomorphisms of the real line* (`D:/lean/theorem3_reorganized.tex`).
  Its main theorem strengthens `[WMUC]` Thm 3 by dropping the uniform-continuity hypothesis.
  - It is **not** a formalization of `[WMUC]` itself: Lemmas 13/14, Cor. 10 and Prop. 8 are absent.
  - Correction by w6, 2026-11-04.
- **Changes.** The files are copied verbatim, with no edits.
- **Namespace.** `VanishingCarleson`.
- **Status.** The main theorem `VanishingCarleson.main_theorem` depends only on `[propext, Classical.choice, Quot.sound]`.
- **Reusable material.** BMO/VMO on ℝ, `A_∞` weights, half-plane Carleson boxes and vanishing Carleson measures, the
  Cayley transform, the Douady–Earle extension `e(h)` on ℍ, `SS(ℝ) ⇒ QS`, and John–Nirenberg.

## `DouadyEarleExt/` (6 modules)

- **Source.** `D:/lean/Conformally_natural_extension_of_homeomorphisms_of_the_circle` (git
  `e0459d96159919a0d3ca83352d30c4ead2659613`). The vendored modules are the import closure of
  `DouadyEarleExt.ImplicitZero`, which `VanishingCarleson.Cayley` needs.
- **Changes.** The files are copied verbatim, with one exception (bypass V1, below).
- **Non-verbatim change: bypass V1** (approved by the leader 2026-11-05, Round B lane C; SCOPE_w4_B5V5.md §3; done by w6).
  - `DouadyEarleExt/Quasiconformal.lean:66`: `import DouadyEarleExt.Extension` → `import DouadyEarle.Extension`
    (LZ's vendored copy). Nothing else changed; CRLF line endings kept. md5 888f4476 → 840a46eb. The original and
    the diff are in `collaboration/w6_vcB/` (`Quasiconformal.lean.orig_888f4476`, `Quasiconformal_V1.diff`).
  - Why: Ext `Basic`/`Extension` declare the same names as LZ `DouadyEarle.Basic`/`.Extension`, which every file
    from S02 on sees through TT. Ext `Basic.lean` is byte-identical to LZ's (f4f4771f), and Ext `Extension.lean`
    differs from LZ's only in its line 93 import, so both are the same code. The same one-line change was already
    made by LZ (`DouadyEarle/PROVENANCE.md`).
  - Effect: `DouadyEarleExt.Basic` and `DouadyEarleExt.Extension` are no longer in the import closure of
    `VanishingCarleson.MainTheorem`. The two files stay in the folder but nothing imports them. VC's
    `extension` is now the same constant as LZ's.
  - Rebuilt: Ext `AhlforsBers`, `Quasiconformal`, `Analytic`, `ImplicitZero` and VC `Cayley` … `MainTheorem`
    (14 modules), 0 errors, by `collaboration/w6_vcB/w6_vendor_build.ps1`. That script is the same command as
    `vendor_build.ps1`, but runs in the w6 slot and only on these modules. Logs are in `collaboration/w6_vcB/vlogs/`.
- **Known `sorry`.** `Quasiconformal.lean:1779` (`sigmaMap_uniformlyContinuousOn`; the docstring starts at 1775) is
  the upstream `sorry`. It is outside the closure of the VanishingCarleson main theorem.
- **Do not reuse uncritically.** Check `#print axioms` before using any DouadyEarleExt result.

## Building

The oleans are built with `lake env lean -o` by `collaboration/vendor_build.ps1`, using the upstream default options
(`autoImplicit` on), in the order given by `collaboration/vendor_order.txt`.

Caution: LiZhong's own vendored `DouadyEarle` library (sections 1–4 of the same sister project) shares root-namespace
names with `DouadyEarleExt.Basic`/`.Extension`. Do not import those two modules. Since bypass V1, the other Ext modules
and all of VC import LZ's copy instead.

## `TauCeti/` (import closure for W-PDE1 and thm_injective)

- **Source.** `D:/lean/external/TauCeti`, commit `a3d94a3f`, licensed Apache 2.0. Its Mathlib revision `9d581dff` is
  identical to ours (`D:/lean/mathlib4-v436rc2`), and the vendored part has no `sorry`, axiom or `native_decide`.
- **Authorization.** The user approved vendoring on 2026-11-04 (route V of `collaboration/w2_pde_INTERFACE.md`), as an
  exception to the "reference only" rule for the other external libraries.
- **Changes.** None: the files are copied byte-for-byte by `collaboration/w2_vendor_verbatim.py`, and the Lean module
  system is kept. Non-module EpsteinVMO files import them like Mathlib (checked in
  `collaboration/w2_vendorC_import_test.lean`).
  - A first attempt that stripped the module syntax was abandoned. It exposed definition bodies the module system
    keeps opaque, and `EnergyForm.Continuity` then timed out in `isDefEq`.
  - The per-file md5 list is in `collaboration/w2_vendorC_*changes.tsv`.
- **Size.** 277 files, 66340 lines.
  - 220 files form the W-PDE1 closure (`w2_vendorC_full_changes.tsv`).
  - 50 more files, 9875 lines, form the `thm_injective` closure (`w2_vendorC_add50_changes.tsv`, 49c8b58f; added
    2026-11-04). They built 50/50 with 0 warnings, and `collaboration/w2_vendorC_collide270.lean` (all 270 modules +
    PDE_Dirichlet + S05/S06/TT/LZ) compiles with 0 errors.
  - 7 more files, 1685 lines, form the W-FKPH (lane F) closure of `GreenFunction.Disk`, `Harnack.Planar` and
    `MeasureTheory.Integral.MaximalFunction` (`w3_vendor_fkph_changes.tsv`, 92c90ae0; added 2026-11-05 by w3, user-
    approved via the leader). The other 9 modules of that closure were already vendored. Upstream has no `sorry`,
    axiom or `native_decide` in them. They built 7/7 with 0 errors, in the order of
    `w3_work/fkph/vendor_order.txt`; there is one deprecation warning (`ENNReal.tsum_le_tsum`, MaximalFunction:290).
    `collaboration/w3_vendor_fkph_collide.lean` (all 277 modules + S05/S06/S07b 89089e52/S11 + TT/LZ) compiles with
    0 errors. `TauCeti.measure_lt_maximalFunction_le`, `TauCeti.eLpNorm_maximalFunction_le` and
    `InnerProductSpace.HarmonicOnNhd.harnack_inequality` are axiom-clean.
- **Options.** `autoImplicit` is on, as in upstream, which uses the Lean defaults.
- **Namespace.** `TauCeti` (module names `TauCeti.*`, unchanged).
- **Building.** Oleans are built with `lake env lean -o` through the slot script, in the order of
  `collaboration/w2_vendor_full_order.txt`.
- **Name clashes.** Collision tests import TauCeti together with S05/S06 and the TT and LZ modules used by EpsteinVMO
  (`collaboration/w2_vendor_collide.lean`).
