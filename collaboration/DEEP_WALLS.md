# Deep walls (NO-GO, kept as honest `sorry`; user decision pending)

Each entry is a statement whose proof needs a large external theory that is not in Mathlib, LiZhongQC, TT or the
vendored libraries. Each one is kept as a `sorry` with the wall named.

| item | file | wall | estimate | source |
|---|---|---|---|---|
| `thm_shen_wei_B5`, `thm_shen_wei_V5`; `prop_opposite_c/d` (S07); hence `thm_B_i/ii` (⇐) (S08) | S02, S07, S08 | **W-FKPH**: Carleson dilatation ⇒ welding is SQS (SW B1/B2⇒B5, V2⇒V5; Fefferman–Kenig–Pipher, via elliptic-measure perturbation). Also blocks the W5 step of `lem_hp_welding`. The other walls have now gone or shrunk: W-AZ is done; W-WELD existence is available; the easy half of W-FKP is VC main_theorem. | ≥6–12k for W-FKPH alone; the ⇐ direction of B5 is 3.9–6.7k more and V5 1.2–2k more | w4, SCOPE_w4_B5V5.md (3f6e5bc3), 2026-11-04 |
| **Update 2026-11-05 (Round B, user decision):** W-FKPH split. VMO half (V2⇒V5) is now FUNDED as Lane F (≈10–13k; DESIGN_w4_FKPH.md f9a3ef63). The BMO half (B2⇒B5; hence `thm_shen_wei_B5` (→), `s07_opp_two_sided_bmo`, `prop_opposite_c/d_bmo`, `thm_B_i` (⇐), `cor_B_outer_i`) stays a deep wall: it needs Hardy H¹ / F.&M. Riesz / Lavrentiev (BJ Thm 4, AZ Thm 4), absent from Mathlib and TauCeti | S02/S07/S08 | **W-FKPH-BMO** | ≈12–18k + theory wall | w4, DESIGN_w4_FKPH.md, 2026-11-05 |
| `ex_nonrect` | S09 | AZ §3 Schottky construction: dim_H L(G) > 1, Fefferman–Kenig–Pipher, Carleson criterion for SQ welding (AZ Thm 4); the Thm 6 route also needs FKP | ≥4–6k | w4, S09_PLAN.md §8 (61450b4b), 2026-11-04 |
| `rem_ambient_intrinsic` (a) | S09 | chord-arc ⇒ BMO quasicircle: harmonic measure is A∞ on Lavrentiev domains (Jerison–Kenig) | 2.5–4k | same |
| `lem_hp_welding` (blocks the last clause of `prop_hp_w0`, `thm_hp_one_sided`, `cor_hp_volume_b`) | S11 | needs, by direction: (⇐) WMUC Prop 8 ⇐ (Shen heat-kernel Beurling–Ahlfors) and ShenVMO Thm 2.2; (⇒) ShenVMO Thm 7.5 (hard direction), MW Thm 1.4 (Loewner chains) and WMUC Prop 8 ⇒ (FKP type). Each wall is a whole paper | — | w3, S11_WMUC_SCOPE.md (a9bbb941), 2026-11-04 |
| `lem_hp_vmoa` | S11 | CM₀ ⇒ VMOA (ShenVMO Thm 7.5). The elementary half, VMOA ⇒ CM₀, is 400–700 lines but not funded, because the only user needs the hard half | — | same |
| ~~`s05_smooth_exhaustion`~~ **CLOSED 2026-11-04** (w4, 267 lines, S05_candEXH 1efd0f3b) (single isolation point; used by `prop_dirichlet_b` via W4, so **on the thm_upper path**, and by `s05_dinv_nonneg` → `eq_t_bound`) | S05 | **W-EXH**: every open D ⊆ ℂ has a smooth exhaustion (needs a regular-value theorem; Mathlib has only equal-dimension easy Sard). Route C (w4): Morse perturbation f + ⟨a,·⟩, isolated critical points, finitely many critical values on compacts. | 800–1500 (rough; scope pending) | w3, w4, 2026-11-04 |
| `lem_Cj` | S04 | W-CJ plus W-ODE; a leaf, used nowhere in Lean | 2500–3000 | w3, TRIAGE_w3_S04S05.md, 2026-11-04 |
| `lem_schauder` | S10 | interior Schauder estimates [GT Thm 6.2]; not in Mathlib or TauCeti | >1.5k | REMAINING_w5.md |
| `rem_ambient_intrinsic` (b), (c) | S09 | 60–100 and 40–80 lines once `ex_nonrect` is proved | — | same |

**2026-11-05 Round BMO started (user go):** W-FKPH-BMO now being attacked; see collaboration/ROUND_BMO.md.

**2026-11-06: W-FKPH-BMO CLOSED** (Round BMO, route R1 = Bishop–Jones + Astala–Zinsmeister, module S07d_BMO). Theorem B fully proved, axiom-clean.
