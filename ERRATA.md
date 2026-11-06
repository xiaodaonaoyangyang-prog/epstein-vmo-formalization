# ERRATA: paper statements that are false or imprecise as written

This file follows the user's rule. A theorem that is false is **not** formalized and is listed in §1. A statement that is
only true after an evident minimal repair is formalized in its repaired form and listed in §2. The leader verifies every
entry.

## 1. False statements (skipped)

None so far.

## 2. Repaired statements (formalized with an added hypothesis)

| label | source | defect | repair in Lean | found by |
|---|---|---|---|---|
| `lem:jacobian` (also used in `lem:source`) | sec04-tube.tex | The lower bound `(1 − Cε)² ≤ J_N` is false when `Cε > 2`, because the left side then exceeds 1 again. The paper means small ε. | The conjunct is guarded by `C * ε ≤ 1`. `lem:source` uses `Cε < 1`. | w2 |
| `rem:hp-compatible` | sec11-halfplane.tex:524 | "For a fixed measure, the proof gives `λ_F ∈ CM₀(ℍ)` under the weaker condition `lim_{r→0} sup_{|I|≤r} ‖λ\|_{Q_{α h⁻¹(I)}}‖_CM = 0`." Read literally, without `λ ∈ CM(ℍ)`, this is false. Since `CM₀` includes `CM` (eq:hp-CM), take `F = id`, `m = 1_{y>1} dA_ρ`, so `λ = 1_{y>1} dx dy/y`. For `\|I\| < 1/α` the weaker condition holds trivially. But `λ(Q_I)/\|I\| = log \|I\| → ∞`, so `λ_F = λ ∉ CM₀`. The leader checked this against eq:hp-CM (sec11:122–127). The intended reading probably assumes `λ ∈ CM`. | Hypothesis `IsHPCarleson (hpWeight m)` (`λ ∈ CM(ℍ)`) added in `rem_hp_compatible`. | w6 |
| `lem:test-functions` (b) | sec05-upper.tex | Claims `(5/4 − C₀ε')φ ≥ φ` under `ε' ≤ 1/8`. This needs `C₀ε' ≤ 1/4`, which `ε' ≤ 1/8` does not give with `C₀ = 11`. Every application uses `C₀ε' ≤ 1/8`, so nothing later is affected. | The conjunct is guarded by `11 ε' ≤ 1/4`. | w2 |

## 3. Gaps in cited sources (statements unaffected)

| cited result | used in | gap | handling in Lean | found by |
|---|---|---|---|---|
| [GM X] §6, the step after (6.10) (Lemma 6.3) | `lem_length` (via `s09_len_bad`) | The closing arc-ratio contradiction never uses the normalization (6.9), and without it the claim is false: Ω = 𝔻, f = (z+a)/(1+az) has Sf ≡ 0, pre-Schwarzian 2a at u = −a, and \|u\| → 1. GM (6.4) also controls the Schwarzian only on a Whitney preimage, but the argument needs it on a larger hyperbolic ball. | The stub `s09_len_bad` takes the Schwarzian bound on a pseudo-hyperbolic disc and adds a corkscrew normalization that forces a ≤ 1 − 2c. The proof uses a neck argument against the quasisymmetry of the global K-q.c. map (`lem_three_point`), not GM's last step. | w4, S09_PLAN §9 |
