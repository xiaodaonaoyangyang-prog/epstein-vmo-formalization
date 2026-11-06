import EpsteinVMO.S10_Sharp
import EpsteinVMO.S09_Ambient
import EpsteinVMO.S11_HalfPlane

/-!
# §13 Open problems

Source: `sec13-open.tex`.  Each problem is a `def … : Prop` (not proved).  Curves are Jordan curves
through `∞` (Convention 2.1 of `Defs.lean`).

## Modelling choices

* `prob:constants`: `V/H` is taken only at points with `0 < H(P) < ∞` (the paper shows `H > 0` for
  non-circles; the extra condition only rules out the junk value `V/0`).
* `prob:sech4` (a): the hypotheses of `prop:global-graph` are read as "`sup s, sup s* < η₀` for some
  `η₀ > 0`"; `t = slabTop` and `σ = sigmaSrc` (with `N = slabMap`) are §4's (`S04_Tube`), as in
  `prop_global_graph`.
* `prob:one-sided`: Convention 11.x (`set:hp`) is encoded by a conformal `f : ℍ → Ω` that extends to
  a homeomorphism of `ℂ` (hence `f(∞) = ∞`); the half-plane Carleson classes (`eq:hp-CM`) and
  `λ_f = y³|Sf|² dx dy` (`eq:hp-mf`) are §11's `IsHPVanishingCarleson` and `hpSchwarzCarleson`.
* `rem:open-boxes` (i) is stated for curves through `∞` only (the paper allows any upper
  half-space position); it uses `boxAvg`, `boxAvgH` of §9.

## Not formalized

* `prob:constants` (b) ("can `s_δ` be given explicitly, and at which rates …") is not a precise
  mathematical statement.
* `rem:open-boxes` (ii) needs the hyperbolic convex hull `CH(Γ)` (`lem:gap-hull`, §2, w1) and
  Example `ex:nonrect` (§12, w6); deferred until those are published.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace EpsteinVMO

open LiZhongQC

/-! ## §13.1 The renormalized quantity -/

/-- **Problem 13.1 (a)**, `prob:ren-sign`, `sec13-open.tex:18`: is `Ren(P) ≥ 0` for every
quasicircle and every `P` with `H(P) < ∞`? -/
def prob_ren_sign_a : Prop :=
  ∀ (Ω Ωs : Set ℂ) (K : ℝ), IsKQuasiPair Ω Ωs K → ∀ P ∈ UHS, ambH Ω Ωs P < ⊤ →
    0 ≤ ren Ω Ωs P

/-- **Problem 13.1 (b)**, `prob:ren-sign`, `sec13-open.tex:22`: is there, for every `K ≥ 1`, a
`c(K) > 0` with `Ren(P) ≥ c(K) H(P)` for every `K`-quasicircle and every `P` with `H(P) < ∞`? -/
def prob_ren_sign_b : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ∀ P ∈ UHS,
    ambH Ω Ωs P < ⊤ → ((c * (ambH Ω Ωs P).toReal : ℝ) : EReal) ≤ ren Ω Ωs P

/-- **Problem 13.2**, `prob:rigidity`, `sec13-open.tex:41`: if `H(P₀) < ∞` for some `P₀` and
`Ren(P₁) = 0` at one point, must `Γ` be a circle? -/
def prob_rigidity : Prop :=
  ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → (∃ P₀ ∈ UHS, ambH Ω Ωs P₀ < ⊤) →
    ∀ P₁ ∈ UHS, ren Ω Ωs P₁ = 0 → IsLinePair Ω Ωs

/-- The class `𝒞_η` of Problem 13.3: Jordan curves that are not circles with `sup_Ω s < η` and
`sup_{Ω*} s* < η`. -/
def curveClassC (η : ℝ) : Set (Set ℂ × Set ℂ) :=
  {p | IsJordanPair p.1 p.2 ∧ ¬ IsLinePair p.1 p.2 ∧ SchwarzSupLt p.1 η ∧ SchwarzSupLt p.2 η}

/-- The ratios `V(P)/H(P)` over `Γ ∈ 𝒞_η` and `P` with `0 < H(P) < ∞`. -/
def ratioSetC (η : ℝ) : Set ℝ≥0∞ :=
  {x | ∃ p ∈ curveClassC η, ∃ P ∈ UHS, ambH p.1 p.2 P < ⊤ ∧ ambH p.1 p.2 P ≠ 0 ∧
    x = ambV p.1 p.2 P / ambH p.1 p.2 P}

/-- `m(η) = inf V/H` (Problem 13.3). -/
def ratioInfC (η : ℝ) : ℝ≥0∞ := sInf (ratioSetC η)

/-- `M(η) = sup V/H` (Problem 13.3). -/
def ratioSupC (η : ℝ) : ℝ≥0∞ := sSup (ratioSetC η)

/-- **Problem 13.3 (a)**, `prob:constants`, `sec13-open.tex:59`: is
`lim_{η→0} m(η) = 2(1 - log 2)` and `lim_{η→0} M(η) = 1`? -/
def prob_constants_a : Prop :=
  Tendsto ratioInfC (𝓝[>] 0) (𝓝 (ENNReal.ofReal (2 * (1 - Real.log 2)))) ∧
    Tendsto ratioSupC (𝓝[>] 0) (𝓝 1)

/-! ## §13.2 Thickness of the gap -/

/-- **Problem 13.4 (a)**, `prob:sech4`, `sec13-open.tex:100`, (13.1): for curves with small
Schwarzian norms (hypotheses of `prop:global-graph`), is there `C` with
`t(p) ≤ C ∫_Ω k_p(w)² σ(w) dâ(w)`? -/
def prob_sech4_a : Prop :=
  ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ C : ℝ, ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ¬ IsLinePair Ω Ωs →
    SchwarzSupLt Ω η₀ → SchwarzSupLt Ωs η₀ →
      ∀ p ∈ Ω, ENNReal.ofReal (slabTop Ω Ωs p) ≤ ENNReal.ofReal C *
        ∫⁻ w, ENNReal.ofReal (intrKernel Ω p w ^ 2 * sigmaSrc Ω Ωs w) ∂hypArea Ω

/-- **Problem 13.4 (b)**, `prob:sech4`, `sec13-open.tex:107`, (13.2): is there, for every `K ≥ 1`,
`C(K)` with `d(X(p), U*) ≤ C(K)(∫_Ω k_p² s² dâ + ∫_{Ω*} k_p(R z*)² s*(z*)² dâ*(z*))` for every
`K`-quasicircle that is not a circle (`R = w ∘ X*` for a label `w`)? -/
def prob_sech4_b : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
    ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab → ∀ p ∈ Ω,
      ENNReal.ofReal (sInf (hdist (epstein Ω p) '' horoUnion Ωs)) ≤ ENNReal.ofReal C *
        ((∫⁻ w, ENNReal.ofReal (intrKernel Ω p w ^ 2) ∂curvMass Ω) +
          ∫⁻ z, ENNReal.ofReal (intrKernel Ω p (lab (epstein Ωs z)) ^ 2) ∂curvMass Ωs)

/-! ## §13.3 One-sided vanishing -/

/-- The conclusion of Problem 13.5: `lim_{r→0} sup_{Im a ≤ r} K*(f(a)) = 0` (for every label). -/
def KstVanishesAtBoundary (Ω Ωs : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab → ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧
    ∀ a ∈ upperHalf, a.im ≤ r → Kst Ω Ωs lab (f a) ≤ ENNReal.ofReal ε

/-- **Problem 13.5**, `prob:one-sided`, `sec13-open.tex:185`: in the setting of Convention 11.x,
does `λ_f ∈ CM₀(ℍ)` imply `lim_{r→0} sup_{Im a ≤ r} K*(f(a)) = 0`? -/
def prob_one_sided : Prop :=
  ∀ (K : ℝ) (Ω Ωs : Set ℂ), IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
    ∀ f : ℂ → ℂ, IsConformalOnto f upperHalf Ω → (∃ F : ℂ ≃ₜ ℂ, EqOn F f upperHalf) →
      IsHPVanishingCarleson (hpSchwarzCarleson f) → KstVanishesAtBoundary Ω Ωs f

/-- `a_n = 12n² + 10n` (Proposition 11.x, `prop:hp-w0`). -/
def w0Node (n : ℕ) : ℝ := 12 * (n : ℝ) ^ 2 + 10 * n

/-- For `y ≥ 0`, the index `n ≥ 1` with `a_{n-1} ≤ y ≤ a_n` (the least `n ≥ 1` with `y ≤ a_n`). -/
def w0Index (y : ℝ) : ℕ := max 1 ⌈(Real.sqrt (100 + 48 * y) - 10) / 24⌉₊

/-- The even function `ω₀(x) = (1 + |x - c_n|)/(12n)` for `a_{n-1} ≤ |x| ≤ a_n`,
`c_n = (a_{n-1} + a_n)/2` (`eq:hp-omega0`). -/
def w0Density (x : ℝ) : ℝ :=
  (1 + |(|x|) - (w0Node (w0Index |x| - 1) + w0Node (w0Index |x|)) / 2|) / (12 * (w0Index |x| : ℝ))

/-- The welding `w₀(x) = ∫₀ˣ ω₀` of Proposition 11.x (`prop:hp-w0`). -/
def w0 (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, w0Density t

/-- **Problem 13.5**, `prob:one-sided`, `sec13-open.tex:188` ("in particular"): does the conclusion
hold for the quasicircles of Proposition 11.x, i.e. those whose welding `g⁻¹ ∘ f|_ℝ` is `w₀`? -/
def prob_one_sided_w0 : Prop :=
  ∀ (K : ℝ) (Ω Ωs : Set ℂ), IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
    (∃ (f g : ℂ → ℂ) (F G : ℂ ≃ₜ ℂ), IsConformalOnto f upperHalf Ω ∧
      IsConformalOnto g lowerHalf Ωs ∧ EqOn F f upperHalf ∧ EqOn G g lowerHalf ∧
      ∀ x : ℝ, F x = G (w0 x)) →
    ∀ f : ℂ → ℂ, IsConformalOnto f upperHalf Ω → (∃ F : ℂ ≃ₜ ℂ, EqOn F f upperHalf) →
      KstVanishesAtBoundary Ω Ωs f

/-! ## §13.4 Box averages and the convex hull -/

/-- **Remark 13.6 (i)**, `rem:open-boxes`, `sec13-open.tex:217` (proved claim, curves through `∞`):
`A_{vol|𝒩}(x,r) ≤ 5 C_K (A_{μ_H}(x,r) + 4 ∑_{j≥1} 2^{-j} A_{μ_H}(x, 2^j r))`. -/
theorem rem_open_boxes_i :
    ∀ K : ℝ, 1 ≤ K → ∃ CK : ℝ, 0 < CK ∧ ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
      ∀ (x : ℂ) (r : ℝ), 0 < r →
        boxAvg (hvol.restrict (gap Ω Ωs)) x r ≤ ENNReal.ofReal (5 * CK) *
          (boxAvgH Ω Ωs x r +
            4 * ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (j + 1) * boxAvgH Ω Ωs x (2 ^ (j + 1) * r)) := by
  intro K hK
  obtain ⟨_c, C, -, hamb⟩ := thm_ambient K hK
  refine ⟨(C : ℝ) + 1, by positivity, fun Ω Ωs h x r hr => ?_⟩
  have hJ := s03_b0_jordanPair h
  have hΩ := s02_jordanPair_riemannMap hJ
  have hΩs := s02_jordanPair_riemannMap (s02_jordanPair_symm hJ)
  set T := boxAvgH Ω Ωs x r +
    4 * ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (j + 1) * boxAvgH Ω Ωs x (2 ^ (j + 1) * r) with hT
  have hCK : ENNReal.ofReal (5 * ((C : ℝ) + 1)) = 5 * ((C : ℝ≥0∞) + 1) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add C.coe_nonneg zero_le_one,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  rw [hCK]
  -- (9.x) for `vol|𝒩`, `K_{vol|𝒩} = V`, `thm_ambient` (upper), (9.x) for `μ_H`
  calc boxAvg (hvol.restrict (gap Ω Ωs)) x r
      ≤ (5 / 4 : ℝ≥0∞) * boxKernel (hvol.restrict (gap Ω Ωs)) x r :=
        s09_boxAvg_le_kernel' _ x r hr
    _ = (5 / 4 : ℝ≥0∞) * ambV Ω Ωs (x, r) := by rw [s09_bx_kernel_vol]
    _ ≤ (5 / 4 : ℝ≥0∞) * ((C : ℝ≥0∞) * ambH Ω Ωs (x, r)) :=
        mul_le_mul_of_nonneg_left (hamb Ω Ωs h (x, r) hr).2 zero_le
    _ ≤ (5 / 4 : ℝ≥0∞) * ((C : ℝ≥0∞) * (4 * T)) := by
        gcongr
        calc ambH Ω Ωs (x, r) ≤ 4 * boxAvgH Ω Ωs x r +
              16 * ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (j + 1) * boxAvgH Ω Ωs x (2 ^ (j + 1) * r) :=
              s09_bx_H_le hΩ hΩs x r hr
          _ = 4 * T := by rw [hT]; ring
    _ = 5 * (C : ℝ≥0∞) * T := by
        rw [show (5 / 4 : ℝ≥0∞) * ((C : ℝ≥0∞) * (4 * T)) = 5 / 4 * 4 * (C : ℝ≥0∞) * T by ring,
          ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
    _ ≤ 5 * ((C : ℝ≥0∞) + 1) * T := by
        gcongr
        exact le_self_add

/-- **Remark 13.6 (i)**, `rem:open-boxes`, `sec13-open.tex:226` (open question): are there
`M(K) ≥ 1` and `C(K)` with `A_{vol|𝒩}(x,r) ≤ C(K) A_{μ_H}(x, M(K) r)` for every `K`-quasicircle and
all `x ∈ ℂ`, `r > 0`? -/
def rem_open_boxes_i_question : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∃ M C : ℝ, 1 ≤ M ∧ ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
    ∀ (x : ℂ) (r : ℝ), 0 < r →
      boxAvg (hvol.restrict (gap Ω Ωs)) x r ≤ ENNReal.ofReal C * boxAvgH Ω Ωs x (M * r)

end EpsteinVMO
