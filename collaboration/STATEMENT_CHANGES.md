# Statement changes after acceptance

This file lists formalization defects or refinements in Lean statements that were changed after the skeleton was
accepted. Paper errors go in `../ERRATA.md` instead. Every change is approved by the leader.

| statement | file | change | reason | approved |
|---|---|---|---|---|
| `prop_global_graph` | S10 | `∃ t N` replaced by `t := slabTop`, `N := slabMap`; the conclusion uses `jacN`. | Closer to the paper's intrinsic objects. | 2026-11-03 |
| `prob_sech4_a` | S13 | Uses `slabTop` and `sigmaSrc` instead of an arbitrary `(t, N)`. | Same reason. | 2026-11-03 |
| `rem_hp_infinity_i_affine` | S11 | Adds `Tendsto (invFunOn f upperHalf) (cocompact ℂ ⊓ 𝓟 Ω) (cocompact ℂ)`, and the same for `f'`. | Formalization defect (w6). With only `f → ∞` the statement is false: on a strip, `log` and `log(−1/z)` are both conformal, but they do not differ by a real affine map. The paper's setting, a Jordan domain through ∞ with boundary correspondence `f(∞) = ∞`, implies the added condition. | 2026-11-03 |
| `eq_def_D` (2nd conjunct) | S05 | `IsClosed (Ω ∩ ⋃ b ∈ S, rhoClosedBall Ω (ℓ b) 2)` becomes `closure (⋃ …) ∩ Ω ⊆ ⋃ …`, i.e. relatively closed in Ω. | Formalization defect (found by w2). Closedness in ℂ fails: for a quasidisk with a corner, the net is infinite and the labels `ℓ_b` accumulate at a boundary point outside Ω. The paper's "their union is closed" means closed in Ω. | 2026-11-04 |
| `IsStronglyQS` | S02 | Now includes `IsCircleHomeo h` (a lift-based orientation-preserving homeomorphism). The data variant is `IsStronglyQSWith`. | The original was satisfied by constant maps. | 2026-11-03 (skeleton phase) |
