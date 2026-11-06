/-
# Analytic dependence on `μ`, and the derivative of `σ` at `0`
(Sections 8 and 9)

* Lemma 6 (local holomorphic extension of the boundary dilatation)
                                        — `lemma6_holomorphic_extension`
* Theorem 4 (`σ` is real-analytic, expressed via analyticity in one real
  parameter along each ray `t ↦ tν`)   — `theorem4_sigmaMap_analytic_in_t`
* Proposition 5 (the derivative of `σ` at `μ = 0`, formula (9.1))
                                        — `sigmaDerivZero`, `prop5_sigmaMap_deriv_zero`
* Corollary 1 (`‖σ'(0)‖ ≤ 3`)          — `corollary1_sigmaDerivZero_bound`
* Corollary 2 (`K*(φ) ≤ K(φ)^{3+ε}` for `K(φ)` near `1`)
                                        — `corollary2_Kstar_bound`

This file contains no `sorry`.  Corollary 1 and the sharpness remark are proved
outright; Lemma 6, Theorem 4, Proposition 5 and Corollary 2 are proved from
explicitly stated inputs that this development does not yet have — Lemma 3, the
implicit differentiation of (3.1) supplied by Section 7, and the analytic
dependence half of the measurable Riemann mapping theorem.  Each section header
below says exactly which.
-/
import Mathlib
import DouadyEarleExt.Quasiconformal

open MeasureTheory Real Set Complex

noncomputable section

/-! ## Lemma 6 and Theorem 4 -/

/-! ### Lemma 6

What Lemma 6 asserts about `φ ↦ μ(E(φ))(0)` splits into two parts of very
different character.

The *holomorphic extension* itself is constructed and proved here, sorry-free.
Writing `c₁(ψ) = ⨍ ψ(ζ)ζ̄`, `c₋₁(ψ) = ⨍ ψ(ζ)ζ` and `q(ψ) = ⨍ ψ(ζ)²`, implicit
differentiation of (3.1) gives `μ(E(φ))(0) = (c₋₁ + q c̄₁)/(c₁ + q c̄₋₁)` for a
homeomorphism `φ` normalized by `E(φ)(0) = 0`.  That expression is *not*
holomorphic in `φ` as written, but on `S¹`-valued maps `conj ψ = 1/ψ`, so
replacing the two conjugates by `⨍ ζ/ψ(ζ)` and `⨍ ζ̄/ψ(ζ)` — which is what
`momA'` and `momB'` are — produces a genuinely holomorphic function
`lemma6Fun` on `C(S¹, ℂ)`, agreeing with the dilatation on `S¹`-valued maps
(`momA'_eq_star`, `momB'_eq_star`).  Its analyticity is `analyticAt_lemma6Fun`:
`c₁, c₋₁` are continuous linear, `q` is continuous quadratic, and `1/ψ` is the
inverse in the Banach algebra `C(S¹, ℂ)`, analytic at every unit.  The bound
`|lemma6Fun| < 1` comes from `norm_moment_lt`, the identity

`|c₁ + q c̄₋₁|² - |c₋₁ + q c̄₁|² = (|c₁|² - |c₋₁|²)(1 - |q|²)`,

together with `norm_momQ_lt_one` (`|⨍φ²| < 1`, proved here by the argument
behind formula (2.4)) and Lemma 3 (`|c₋₁| < |c₁|`).

The *identification* with `μ(E(φ))(0)` needs the implicit differentiation
equations of Section 7 at `0`, in the specific normalized form used here.
Differentiability of `E(φ)` is no longer the obstacle — `extension_analyticOn_disk`
supplies it, and `exists_implicit_fderiv` supplies the equations — but the
normalized form is derived only downstream, in `ImplicitZero.lean`
(`hasImplicitDerivAtZero`), so here it appears as the explicit hypothesis
`HasImplicitDerivAtZero` — discharged by `lemma6_holomorphic_extension'` there —
and Lemma 3 (`lemma3_fourier_coeff`, in its Fourier-series form) as the
hypothesis `hlem3`.  Everything else is proved.

Two further points about the statement as the paper gives it.  It is stated
for *orientation preserving* `φ₀`: for an orientation-reversing homeomorphism
`E(φ)` reverses orientation too, `|μ| > 1`, and the bound `‖f ψ‖ < 1` fails.
Here that hypothesis is carried by `hlem3`, which is false for
orientation-reversing maps.  And the identification is stated only for `φ`
normalized by `E(φ)(0) = 0`: the general case follows from this one by
conformal naturality (`extension_naturality`) and invariance of the dilatation
under post-composition with a Möbius map (`complexDilatation_comp_left`), but
only once the barycenter `φ ↦ E(φ)(0)` is known to depend holomorphically on
`φ`, which is again Section 7. -/

section Lemma6

open Topology Filter

/-- The mean value `⨍ F dm = (2π)⁻¹ ∫₀^{2π} F(e^{iθ}) dθ` of a continuous
function on `S¹`, as a continuous `ℂ`-linear functional on `C(S¹, ℂ)`. -/
def circleMeanLM : C(Circle, ℂ) →ₗ[ℂ] ℂ where
  toFun F := (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ θ in (0:ℝ)..(2 * Real.pi), F (Circle.exp θ)
  map_add' F G := by
    have hF : IntervalIntegrable (fun θ : ℝ => F (Circle.exp θ)) MeasureTheory.volume
        0 (2 * Real.pi) :=
      (F.continuous.comp Circle.exp.continuous).intervalIntegrable _ _
    have hG : IntervalIntegrable (fun θ : ℝ => G (Circle.exp θ)) MeasureTheory.volume
        0 (2 * Real.pi) :=
      (G.continuous.comp Circle.exp.continuous).intervalIntegrable _ _
    simp only [ContinuousMap.add_apply]
    rw [intervalIntegral.integral_add hF hG]
    ring
  map_smul' c F := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      intervalIntegral.integral_const_mul]
    ring

def circleMean : C(Circle, ℂ) →L[ℂ] ℂ :=
  circleMeanLM.mkContinuous 1 (by
    intro F
    have hpi : (0:ℝ) < 2 * Real.pi := by positivity
    have hb : ∀ᵐ θ ∂MeasureTheory.volume, θ ∈ Set.Ioc (0:ℝ) (2 * Real.pi) →
        ‖F (Circle.exp θ)‖ ≤ ‖F‖ := by
      filter_upwards with θ _
      exact ContinuousMap.norm_coe_le_norm F _
    have hle := intervalIntegral.norm_integral_le_of_norm_le hpi.le hb
      (intervalIntegrable_const)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hle
    show ‖(((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ θ in (0:ℝ)..(2 * Real.pi), F (Circle.exp θ)‖
      ≤ 1 * ‖F‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < (2 * Real.pi)⁻¹), one_mul]
    calc (2 * Real.pi)⁻¹ * ‖∫ θ in (0:ℝ)..(2 * Real.pi), F (Circle.exp θ)‖
        ≤ (2 * Real.pi)⁻¹ * ((2 * Real.pi - 0) * ‖F‖) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ‖F‖ := by rw [sub_zero]; field_simp)

theorem circleMean_apply (F : C(Circle, ℂ)) :
    circleMean F = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ θ in (0:ℝ)..(2 * Real.pi), F (Circle.exp θ) :=
  rfl

/-- `ζ ↦ ζ` as an element of `C(S¹, ℂ)`. -/
def wPlus : C(Circle, ℂ) := ⟨fun ζ => (ζ : ℂ), continuous_subtype_val⟩

/-- `ζ ↦ ζ̄` as an element of `C(S¹, ℂ)`. -/
def wMinus : C(Circle, ℂ) := ⟨fun ζ => star (ζ : ℂ), continuous_star.comp continuous_subtype_val⟩

@[simp] theorem wPlus_apply (ζ : Circle) : wPlus ζ = (ζ : ℂ) := rfl
@[simp] theorem wMinus_apply (ζ : Circle) : wMinus ζ = star (ζ : ℂ) := rfl

/-- `c₁(ψ) = ⨍ ψ(ζ) ζ̄ dm(ζ)`. -/
def momA (ψ : C(Circle, ℂ)) : ℂ := circleMean (ψ * wMinus)
/-- `c₋₁(ψ) = ⨍ ψ(ζ) ζ dm(ζ)`. -/
def momB (ψ : C(Circle, ℂ)) : ℂ := circleMean (ψ * wPlus)
/-- `q(ψ) = ⨍ ψ(ζ)² dm(ζ)`. -/
def momQ (ψ : C(Circle, ℂ)) : ℂ := circleMean (ψ * ψ)
/-- `⨍ ζ/ψ(ζ) dm(ζ)`: the holomorphic stand-in for `conj (c₁(ψ))`. -/
def momA' (ψ : C(Circle, ℂ)) : ℂ := circleMean (Ring.inverse ψ * wPlus)
/-- `⨍ ζ̄/ψ(ζ) dm(ζ)`: the holomorphic stand-in for `conj (c₋₁(ψ))`. -/
def momB' (ψ : C(Circle, ℂ)) : ℂ := circleMean (Ring.inverse ψ * wMinus)

/-- The holomorphic extension of `φ ↦ μ(E(φ))(0)` asserted by Lemma 6. -/
def lemma6Fun (ψ : C(Circle, ℂ)) : ℂ :=
  (momB ψ + momQ ψ * momA' ψ) / (momA ψ + momQ ψ * momB' ψ)

/-! ### Analyticity -/

theorem analyticAt_momA (ψ₀ : C(Circle, ℂ)) : AnalyticAt ℂ momA ψ₀ :=
  (circleMean.analyticAt _).comp (analyticAt_id.mul analyticAt_const)

theorem analyticAt_momB (ψ₀ : C(Circle, ℂ)) : AnalyticAt ℂ momB ψ₀ :=
  (circleMean.analyticAt _).comp (analyticAt_id.mul analyticAt_const)

theorem analyticAt_momQ (ψ₀ : C(Circle, ℂ)) : AnalyticAt ℂ momQ ψ₀ :=
  (circleMean.analyticAt _).comp (analyticAt_id.mul analyticAt_id)

theorem analyticAt_momA' {ψ₀ : C(Circle, ℂ)} (h : IsUnit ψ₀) : AnalyticAt ℂ momA' ψ₀ := by
  obtain ⟨u, rfl⟩ := h
  exact (circleMean.analyticAt _).comp ((analyticAt_inverse u).mul analyticAt_const)

theorem analyticAt_momB' {ψ₀ : C(Circle, ℂ)} (h : IsUnit ψ₀) : AnalyticAt ℂ momB' ψ₀ := by
  obtain ⟨u, rfl⟩ := h
  exact (circleMean.analyticAt _).comp ((analyticAt_inverse u).mul analyticAt_const)

theorem analyticAt_lemma6Fun {ψ₀ : C(Circle, ℂ)} (hu : IsUnit ψ₀)
    (hden : momA ψ₀ + momQ ψ₀ * momB' ψ₀ ≠ 0) : AnalyticAt ℂ lemma6Fun ψ₀ :=
  ((analyticAt_momB ψ₀).add ((analyticAt_momQ ψ₀).mul (analyticAt_momA' hu))).div
    ((analyticAt_momA ψ₀).add ((analyticAt_momQ ψ₀).mul (analyticAt_momB' hu))) hden

/-! ### Circle-valued maps -/

/-- A continuous self-map of `S¹`, viewed in `C(S¹, ℂ)`. -/
def toCM (φ : Circle → Circle) (hφc : Continuous φ) : C(Circle, ℂ) :=
  ⟨fun ζ => (φ ζ : ℂ), continuous_subtype_val.comp hφc⟩

@[simp] theorem toCM_apply (φ : Circle → Circle) (hφc : Continuous φ) (ζ : Circle) :
    toCM φ hφc ζ = (φ ζ : ℂ) := rfl

theorem isUnit_toCM (φ : Circle → Circle) (hφc : Continuous φ) : IsUnit (toCM φ hφc) := by
  refine (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr (fun ζ => ?_)
  rw [toCM_apply]
  intro hc
  have := Circle.norm_coe (φ ζ)
  rw [hc] at this
  simp at this

theorem star_coe_circle (ζ : Circle) : star ((ζ : Circle) : ℂ) = ((ζ : ℂ))⁻¹ :=
  inv_eq_of_mul_eq_one_left (star_mul_self_of_norm_one (Circle.norm_coe ζ)) |>.symm

theorem momA'_eq_star (φ : Circle → Circle) (hφc : Continuous φ) :
    momA' (toCM φ hφc) = star (momA (toCM φ hφc)) := by
  have hu := isUnit_toCM φ hφc
  rw [momA', momA, circleMean_apply, circleMean_apply]
  rw [Complex.star_def, map_mul, ← intervalIntegral_conj]
  rw [show (starRingEnd ℂ) (((2 * Real.pi)⁻¹ : ℝ) : ℂ) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) from
    Complex.conj_ofReal _]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [ContinuousMap.mul_apply, ringInverse_apply hu, wPlus_apply, wMinus_apply,
    toCM_apply, map_mul, ← Complex.star_def, star_star]
  simp only [star_coe_circle]

theorem momB'_eq_star (φ : Circle → Circle) (hφc : Continuous φ) :
    momB' (toCM φ hφc) = star (momB (toCM φ hφc)) := by
  have hu := isUnit_toCM φ hφc
  rw [momB', momB, circleMean_apply, circleMean_apply]
  rw [Complex.star_def, map_mul, ← intervalIntegral_conj]
  rw [show (starRingEnd ℂ) (((2 * Real.pi)⁻¹ : ℝ) : ℂ) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) from
    Complex.conj_ofReal _]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [ContinuousMap.mul_apply, ringInverse_apply hu, wPlus_apply, wMinus_apply,
    toCM_apply, map_mul, ← Complex.star_def]
  simp only [star_coe_circle]

/-! ### `|⨍ φ² dm| < 1` -/

/-- The analogue of the strict bound behind formula (2.4): for a homeomorphism
`φ` of `S¹`, `|⨍ φ(ζ)² dm(ζ)| < 1`.  Equality would force `φ²` to be constant
on `S¹`, which injectivity forbids. -/
theorem norm_momQ_lt_one (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) : ‖momQ (toCM φ hφc)‖ < 1 := by
  have hpi := Real.pi_pos
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  set v : ℝ → ℂ := fun θ => ((φ (Circle.exp θ) : Circle) : ℂ) with hvdef
  have hvc : Continuous v := by
    rw [hvdef]
    exact continuous_subtype_val.comp (hφc.comp Circle.exp.continuous)
  have hv1 : ∀ θ, ‖v θ‖ = 1 := fun θ => Circle.norm_coe _
  have hvinj : ∀ θ ∈ Set.Ioo (0:ℝ) (2 * Real.pi), ∀ θ' ∈ Set.Ioo (0:ℝ) (2 * Real.pi),
      v θ = v θ' → θ = θ' := by
    intro θ hθ θ' hθ' h
    exact circle_exp_inj_on hθ hθ' (congrArg (fun u : Circle => (u : ℂ)) (hφ.1 (Subtype.ext h)))
  have hQ : momQ (toCM φ hφc)
      = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ θ in (0:ℝ)..(2 * Real.pi), (v θ) ^ 2 := by
    rw [momQ, circleMean_apply]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [ContinuousMap.mul_apply, toCM_apply, hvdef]
    ring
  set c : ℂ := momQ (toCM φ hφc) with hcdef
  have hvsq : ∀ θ, ‖(v θ) ^ 2‖ = 1 := by intro θ; rw [norm_pow, hv1]; norm_num
  -- the crude bound
  have hle : ‖c‖ ≤ 1 := by
    have hb : ∀ᵐ θ ∂MeasureTheory.volume, θ ∈ Set.Ioc (0:ℝ) (2 * Real.pi) →
        ‖(v θ) ^ 2‖ ≤ (1:ℝ) := by
      filter_upwards with θ _
      exact le_of_eq (hvsq θ)
    have h := intervalIntegral.norm_integral_le_of_norm_le h2pi.le hb intervalIntegrable_const
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one] at h
    rw [hQ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < (2 * Real.pi)⁻¹)]
    calc (2 * Real.pi)⁻¹ * ‖∫ θ in (0:ℝ)..(2 * Real.pi), (v θ) ^ 2‖
        ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = 1 := by field_simp
  by_contra hcon
  have hone : ‖c‖ = 1 := le_antisymm hle (not_lt.1 hcon)
  -- the nonnegative continuous function with vanishing integral
  set f : ℝ → ℝ := fun θ => 1 - (star c * (v θ) ^ 2).re with hfdef
  have hfc : Continuous f := by
    rw [hfdef]
    exact continuous_const.sub (Complex.continuous_re.comp (continuous_const.mul (hvc.pow 2)))
  have hfnn : ∀ θ, 0 ≤ f θ := by
    intro θ
    have : (star c * (v θ) ^ 2).re ≤ 1 := by
      refine le_trans (Complex.re_le_norm _) ?_
      rw [norm_mul, norm_star, hone, hvsq, one_mul]
    rw [hfdef]; simp only; linarith
  have hI2 : ∫ θ in (0:ℝ)..(2 * Real.pi), (v θ) ^ 2 = ((2 * Real.pi : ℝ) : ℂ) * c := by
    rw [hQ, ← mul_assoc, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (ne_of_gt h2pi), Complex.ofReal_one, one_mul]
  have hfint : ∫ θ in (0:ℝ)..(2 * Real.pi), f θ = 0 := by
    have hcont : Continuous fun θ : ℝ => star c * (v θ) ^ 2 :=
      continuous_const.mul (hvc.pow 2)
    have hcomm := (Complex.reCLM.intervalIntegral_comp_comm
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 (2 * Real.pi))).symm
    simp only [Complex.reCLM_apply] at hcomm
    have hre : ∫ θ in (0:ℝ)..(2 * Real.pi), (star c * (v θ) ^ 2).re = 2 * Real.pi := by
      rw [← hcomm, intervalIntegral.integral_const_mul, hI2]
      have hval : star c * (((2 * Real.pi : ℝ) : ℂ) * c) = ((2 * Real.pi : ℝ) : ℂ) := by
        have hcc : star c * c = ((‖c‖ : ℝ) : ℂ) ^ 2 := by
          rw [Complex.star_def, Complex.conj_mul']
        rw [show star c * (((2 * Real.pi : ℝ) : ℂ) * c)
            = ((2 * Real.pi : ℝ) : ℂ) * (star c * c) by ring, hcc, hone]
        norm_num
      rw [hval]
      simp
    have hg : Continuous fun θ : ℝ => (star c * (v θ) ^ 2).re :=
      Complex.continuous_re.comp hcont
    rw [hfdef]
    simp only
    rw [intervalIntegral.integral_sub (intervalIntegrable_const)
      (hg.intervalIntegrable (μ := MeasureTheory.volume) 0 (2 * Real.pi))]
    rw [intervalIntegral.integral_const, hre]
    simp
  have hfzero : ∀ θ ∈ Set.Ioo (0:ℝ) (2 * Real.pi), f θ = 0 := by
    intro θ hθ
    by_contra hne
    have hpos : 0 < f θ := lt_of_le_of_ne (hfnn θ) (Ne.symm hne)
    have hgt := intervalIntegral_pos_of_pos_at hfc hfnn hθ hpos
    rw [hfint] at hgt
    exact lt_irrefl _ hgt
  have key : ∀ θ ∈ Set.Ioo (0:ℝ) (2 * Real.pi), star c * (v θ) ^ 2 = 1 := by
    intro θ hθ
    have h0 : (1 : ℝ) - (star c * (v θ) ^ 2).re = 0 := hfzero θ hθ
    refine eq_one_of_norm_one_of_re_one ?_ (by linarith)
    rw [norm_mul, norm_star, hone, hvsq, one_mul]
  -- three points with equal squares force two equal values
  have hm1 : Real.pi / 2 ∈ Set.Ioo (0:ℝ) (2 * Real.pi) := ⟨by linarith, by linarith⟩
  have hm2 : Real.pi ∈ Set.Ioo (0:ℝ) (2 * Real.pi) := ⟨by linarith, by linarith⟩
  have hm3 : 3 * Real.pi / 2 ∈ Set.Ioo (0:ℝ) (2 * Real.pi) := ⟨by linarith, by linarith⟩
  have hsq : ∀ θ ∈ Set.Ioo (0:ℝ) (2 * Real.pi), ∀ θ' ∈ Set.Ioo (0:ℝ) (2 * Real.pi),
      v θ = v θ' ∨ v θ = -v θ' := by
    intro θ hθ θ' hθ'
    have h := (key θ hθ).trans (key θ' hθ').symm
    have hcne : star c ≠ 0 := by
      intro hz
      have hz0 : ‖star c‖ = 0 := by rw [hz]; simp
      rw [norm_star, hone] at hz0
      exact one_ne_zero hz0
    have hsq2 : (v θ) ^ 2 = (v θ') ^ 2 := mul_left_cancel₀ hcne h
    have hfac : (v θ - v θ') * (v θ + v θ') = 0 := by linear_combination hsq2
    rcases mul_eq_zero.1 hfac with h' | h'
    · exact Or.inl (sub_eq_zero.1 h')
    · exact Or.inr (by linear_combination h')
  rcases hsq _ hm1 _ hm2 with h12 | h12
  · exact absurd (hvinj _ hm1 _ hm2 h12) (by linarith)
  rcases hsq _ hm1 _ hm3 with h13 | h13
  · exact absurd (hvinj _ hm1 _ hm3 h13) (by linarith)
  · exact absurd (hvinj _ hm2 _ hm3 (by rw [h12] at h13; linear_combination -h13)) (by linarith)

/-! ### The implicit differentiation -/

theorem normSq_implicit_identity (a b q : ℂ) :
    Complex.normSq (a + q * star b) - Complex.normSq (b + q * star a)
      = (Complex.normSq a - Complex.normSq b) * (1 - Complex.normSq q) := by
  simp only [Complex.normSq_apply, Complex.star_def, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Solving the implicit differentiation equations `A = c₁ + q·B̄`,
`B = c₋₁ + q·Ā` of the barycentric equation: the dilatation `B/A` equals
`(c₋₁ + q c̄₁)/(c₁ + q c̄₋₁)`, of modulus `< 1` as soon as `|q| < 1` and
`|c₋₁| < |c₁|` (Lemma 3). -/
theorem norm_moment_lt {a b q : ℂ} (hq : ‖q‖ < 1) (hab : ‖b‖ < ‖a‖) :
    ‖b + q * star a‖ < ‖a + q * star b‖ := by
  have hid := normSq_implicit_identity a b q
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hid
  have hqn := norm_nonneg q
  have hbn := norm_nonneg b
  have hd1 : (0:ℝ) < ‖a‖ ^ 2 - ‖b‖ ^ 2 := by nlinarith
  have hd2 : (0:ℝ) < 1 - ‖q‖ ^ 2 := by nlinarith
  have hpos : 0 < ‖a + q * star b‖ ^ 2 - ‖b + q * star a‖ ^ 2 := by
    rw [hid]; exact mul_pos hd1 hd2
  nlinarith [norm_nonneg (b + q * star a), norm_nonneg (a + q * star b)]

theorem dilatation_of_implicit {a b q A B : ℂ} (hq : ‖q‖ < 1) (hab : ‖b‖ < ‖a‖)
    (h1 : A = a + q * star B) (h2 : B = b + q * star A) :
    ‖b + q * star a‖ < ‖a + q * star b‖ ∧ A ≠ 0 ∧
      B / A = (b + q * star a) / (a + q * star b) := by
  have hlt : ‖b + q * star a‖ < ‖a + q * star b‖ := norm_moment_lt hq hab
  have hden : a + q * star b ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hlt
    exact absurd hlt (not_lt.2 (norm_nonneg _))
  have hqq : q * star q = ((‖q‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.star_def, Complex.conj_mul']
  have hsB : star B = star b + A * star q := by rw [h2, star_add, star_mul, star_star]
  have hsA : star A = star a + B * star q := by rw [h1, star_add, star_mul, star_star]
  have hA : A * (1 - ((‖q‖ : ℝ) : ℂ) ^ 2) = a + q * star b := by
    linear_combination h1 + q * hsB + A * hqq
  have hB : B * (1 - ((‖q‖ : ℝ) : ℂ) ^ 2) = b + q * star a := by
    linear_combination h2 + q * hsA + B * hqq
  have hk : (1 - ((‖q‖ : ℝ) : ℂ) ^ 2) ≠ 0 := by
    intro hz
    have h1' : ((‖q‖ : ℝ) : ℂ) ^ 2 = 1 := by linear_combination -hz
    have h2' : ((‖q‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; linear_combination h1'
    have h3' : ‖q‖ ^ 2 = 1 := by exact_mod_cast h2'
    nlinarith [norm_nonneg q]
  have hA0 : A ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hA
    exact hden hA.symm
  refine ⟨hlt, hA0, ?_⟩
  rw [← hA, ← hB, mul_div_mul_right _ _ hk]

/-- The analytic input of Section 7 on which Lemma 6 rests: the implicit
differentiation of the barycentric equation (3.1) at `(z, w) = (0, 0)`.  For
`F(z, w) = ⨍ g_w(φ(ζ)) dη_z(ζ)` one has `F_z = c₁`, `F_z̄ = c₋₁`, `F_w = -1` and
`F_w̄ = ⨍ φ²` at `(0,0)`, and differentiating `F(z, Φ(z)) ≡ 0` gives these two
equations for `Φ_z` and `Φ_z̄`. -/
def HasImplicitDerivAtZero (φ : Circle → Circle) (hφc : Continuous φ) : Prop :=
  wirtZ (extension φ) 0
      = momA (toCM φ hφc) + momQ (toCM φ hφc) * star (wirtZbar (extension φ) 0) ∧
    wirtZbar (extension φ) 0
      = momB (toCM φ hφc) + momQ (toCM φ hφc) * star (wirtZ (extension φ) 0)

/-- **Lemma 6**: for `φ₀` an orientation preserving homeomorphism of `S¹`,
the dilatation ratio `φ ↦ μ(E(φ))(0)` extends to a holomorphic function of `φ`
on a neighborhood in `C(S¹, ℂ)`, bounded by `1` in modulus.

`hlem3` is Lemma 3 for `φ₀` and `himp` is the implicit differentiation of
(3.1) at `(0,0)`.  `himp` is proved in `ImplicitZero.lean`
(`hasImplicitDerivAtZero`), where `lemma6_holomorphic_extension'` is this
lemma without it; it is a hypothesis here only because that proof sits
downstream of this file.  Everything else — the construction of the
holomorphic extension, its analyticity, and the bound — is proved.

Lemma 3 appears twice, once for `φ₀` and once as a hypothesis on the `φ` in
the last clause, rather than once as `∀ φ, …`: the universally quantified form
is *false*, since an orientation-reversing homeomorphism has `|c₋₁| > |c₁|`
(for `φ = conj`, `c₁ = 0` and `c₋₁ = 1`), and assuming it would make the whole
statement vacuous. -/
theorem lemma6_holomorphic_extension (φ₀ : Circle → Circle) (hφ₀ : Function.Bijective φ₀)
    (hφ₀c : Continuous φ₀)
    (hlem3 : ‖momB (toCM φ₀ hφ₀c)‖ < ‖momA (toCM φ₀ hφ₀c)‖)
    (himp : ∀ (φ : Circle → Circle), Function.Bijective φ → ∀ hφc : Continuous φ,
      extension φ 0 = 0 → HasImplicitDerivAtZero φ hφc) :
    ∃ (V : Set C(Circle, ℂ)) (f : C(Circle, ℂ) → ℂ),
      IsOpen V ∧ toCM φ₀ hφ₀c ∈ V ∧ AnalyticOn ℂ f V ∧ (∀ ψ ∈ V, ‖f ψ‖ < 1) ∧
      ∀ (φ : Circle → Circle), Function.Bijective φ → ∀ hφc : Continuous φ,
        ‖momB (toCM φ hφc)‖ < ‖momA (toCM φ hφc)‖ → extension φ 0 = 0 →
        toCM φ hφc ∈ V → f (toCM φ hφc) = complexDilatation (extension φ) 0 := by
  -- the value of the candidate at a circle-valued point
  have hval : ∀ (φ : Circle → Circle), ∀ hφc : Continuous φ,
      lemma6Fun (toCM φ hφc)
        = (momB (toCM φ hφc) + momQ (toCM φ hφc) * star (momA (toCM φ hφc)))
          / (momA (toCM φ hφc) + momQ (toCM φ hφc) * star (momB (toCM φ hφc))) := by
    intro φ hφc
    rw [lemma6Fun, momA'_eq_star φ hφc, momB'_eq_star φ hφc]
  have hbnd : ∀ (φ : Circle → Circle), Function.Bijective φ → ∀ hφc : Continuous φ,
      ‖momB (toCM φ hφc)‖ < ‖momA (toCM φ hφc)‖ →
      ‖momB (toCM φ hφc) + momQ (toCM φ hφc) * star (momA (toCM φ hφc))‖
        < ‖momA (toCM φ hφc) + momQ (toCM φ hφc) * star (momB (toCM φ hφc))‖ :=
    fun φ hφ hφc h3 => norm_moment_lt (norm_momQ_lt_one φ hφ hφc) h3
  have hden : ∀ (φ : Circle → Circle), Function.Bijective φ → ∀ hφc : Continuous φ,
      ‖momB (toCM φ hφc)‖ < ‖momA (toCM φ hφc)‖ →
      momA (toCM φ hφc) + momQ (toCM φ hφc) * momB' (toCM φ hφc) ≠ 0 := by
    intro φ hφ hφc h3
    rw [momB'_eq_star φ hφc]
    intro hz
    have hb := hbnd φ hφ hφc h3
    rw [hz, norm_zero] at hb
    exact absurd hb (not_lt.2 (norm_nonneg _))
  have hlt1 : ∀ (φ : Circle → Circle), Function.Bijective φ → ∀ hφc : Continuous φ,
      ‖momB (toCM φ hφc)‖ < ‖momA (toCM φ hφc)‖ → ‖lemma6Fun (toCM φ hφc)‖ < 1 := by
    intro φ hφ hφc h3
    rw [hval φ hφc, norm_div, div_lt_one]
    · exact hbnd φ hφ hφc h3
    · exact lt_of_le_of_lt (norm_nonneg _) (hbnd φ hφ hφc h3)
  -- the neighbourhood
  set V : Set C(Circle, ℂ) :=
    {ψ | IsUnit ψ ∧ momA ψ + momQ ψ * momB' ψ ≠ 0 ∧ ‖lemma6Fun ψ‖ < 1} with hVdef
  have hVopen : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    rintro ψ₁ ⟨hu, hd, hb⟩
    have hAn : AnalyticAt ℂ lemma6Fun ψ₁ := analyticAt_lemma6Fun hu hd
    have hg : AnalyticAt ℂ (fun ψ => momA ψ + momQ ψ * momB' ψ) ψ₁ :=
      (analyticAt_momA ψ₁).add ((analyticAt_momQ ψ₁).mul (analyticAt_momB' hu))
    have e1 : ∀ᶠ ψ in nhds ψ₁, IsUnit ψ := Units.isOpen.mem_nhds hu
    have e2 : ∀ᶠ ψ in nhds ψ₁, momA ψ + momQ ψ * momB' ψ ≠ 0 :=
      hg.continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hd)
    have e3 : ∀ᶠ ψ in nhds ψ₁, ‖lemma6Fun ψ‖ < 1 :=
      (continuous_norm.continuousAt.comp hAn.continuousAt).preimage_mem_nhds
        (Iio_mem_nhds hb)
    filter_upwards [e1, e2, e3] with ψ h1 h2 h3
    exact ⟨h1, h2, h3⟩
  refine ⟨V, lemma6Fun, hVopen,
    ⟨isUnit_toCM φ₀ hφ₀c, hden φ₀ hφ₀ hφ₀c hlem3, hlt1 φ₀ hφ₀ hφ₀c hlem3⟩,
    ?_, fun ψ hψ => hψ.2.2, ?_⟩
  · exact fun ψ hψ => (analyticAt_lemma6Fun hψ.1 hψ.2.1).analyticWithinAt
  · intro φ hφ hφc h3 hnorm hmem
    obtain ⟨hi1, hi2⟩ := himp φ hφ hφc hnorm
    obtain ⟨-, -, hdiv⟩ :=
      dilatation_of_implicit (norm_momQ_lt_one φ hφ hφc) h3 hi1 hi2
    rw [hval φ hφc, ← hdiv, complexDilatation]


/-! ### Why Lemma 3 cannot be assumed for every homeomorphism -/

theorem circleInv_cont : Continuous (fun ζ : Circle => ζ⁻¹) := by fun_prop

theorem momB_inv : momB (toCM (fun ζ : Circle => ζ⁻¹) circleInv_cont) = 1 := by
  rw [momB, circleMean_apply]
  have hpt : ∀ θ : ℝ,
      (toCM (fun ζ : Circle => ζ⁻¹) circleInv_cont * wPlus) (Circle.exp θ) = 1 := by
    intro θ
    simp only [ContinuousMap.mul_apply, toCM_apply, wPlus_apply, Circle.coe_inv]
    exact inv_mul_cancel₀ (by
      intro hc
      have h := Circle.norm_coe (Circle.exp θ)
      rw [hc] at h
      simp at h)
  rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (1:ℂ)) (fun θ _ => hpt θ)]
  simp only [intervalIntegral.integral_const, sub_zero, real_smul, mul_one]
  rw [← Complex.ofReal_mul, inv_mul_cancel₀ (by positivity : (2 * Real.pi) ≠ 0)]
  norm_num

theorem momA_inv : momA (toCM (fun ζ : Circle => ζ⁻¹) circleInv_cont) = 0 := by
  rw [momA, circleMean_apply]
  have hpt : ∀ θ : ℝ,
      (toCM (fun ζ : Circle => ζ⁻¹) circleInv_cont * wMinus) (Circle.exp θ)
        = Complex.exp ((-2 * Complex.I) * (θ : ℂ)) := by
    intro θ
    simp only [ContinuousMap.mul_apply, toCM_apply, wMinus_apply, Circle.coe_inv,
      Circle.coe_exp, Complex.star_def, ← Complex.exp_conj]
    rw [← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  rw [integral_exp_mul_complex (by simp : (-2 * Complex.I) ≠ 0)]
  have h1 : Complex.exp (-2 * Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    rw [show (-2 * Complex.I * ((2 * Real.pi : ℝ) : ℂ))
        = ((-2 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I (-2)
  rw [h1]
  simp

/-- The universally quantified form of Lemma 3 is false: for the
orientation-reversing homeomorphism `ζ ↦ ζ⁻¹ = ζ̄` one has `c₁ = 0` and
`c₋₁ = 1`, so `|c₋₁| > |c₁|`. -/
theorem lemma3_forall_false :
    ¬ ∀ (φ : Circle → Circle), Function.Bijective φ → ∀ hφc : Continuous φ,
      ‖momB (toCM φ hφc)‖ < ‖momA (toCM φ hφc)‖ := by
  intro h
  have hbad := h (fun ζ : Circle => ζ⁻¹) inv_bijective circleInv_cont
  rw [momA_inv, momB_inv] at hbad
  simp only [norm_one, norm_zero] at hbad
  linarith

/-! ### The differential of the Lemma 6 function at the identity

This is the one part of Proposition 5 that does not need Ahlfors–Bers, and it
is where the constant `3` of Corollary 1 and the `3/π` of formula (9.1) come
from.  At `ψ = id` the five moments are `c₁ = 1`, `c₋₁ = 0`, `q = 0`,
`⨍ζ/ψ = 1`, `⨍ζ̄/ψ = 0`, so `lemma6Fun (id) = 0` and the quotient rule collapses:
only the numerator contributes, and there only `c₋₁` and `q` (the derivative of
`⨍ζ/ψ` is killed by the factor `q = 0`).  Since `d c₋₁[h] = ⨍hζ` and
`d q[h] = 2⨍hζ`, the differential is `h ↦ 3 ⨍ h(ζ) ζ dm(ζ)`. -/

/-- `h ↦ ⨍ h(ζ) g(ζ) dm(ζ)`, as a continuous linear functional on `C(S¹, ℂ)`. -/
def circleMeanMul (g : C(Circle, ℂ)) : C(Circle, ℂ) →L[ℂ] ℂ :=
  circleMean.comp ((ContinuousLinearMap.mul ℂ C(Circle, ℂ)).flip g)

@[simp] theorem circleMeanMul_apply (g h : C(Circle, ℂ)) :
    circleMeanMul g h = circleMean (h * g) := rfl

theorem hasFDerivAt_momA (ψ₀ : C(Circle, ℂ)) :
    HasFDerivAt momA (circleMeanMul wMinus) ψ₀ :=
  (circleMeanMul wMinus).hasFDerivAt

theorem hasFDerivAt_momB (ψ₀ : C(Circle, ℂ)) :
    HasFDerivAt momB (circleMeanMul wPlus) ψ₀ :=
  (circleMeanMul wPlus).hasFDerivAt

theorem hasFDerivAt_momQ (ψ₀ : C(Circle, ℂ)) :
    HasFDerivAt momQ ((2 : ℂ) • circleMeanMul ψ₀) ψ₀ := by
  have hsq : HasFDerivAt (fun ψ : C(Circle, ℂ) => ψ * ψ)
      (ψ₀ • (ContinuousLinearMap.id ℂ C(Circle, ℂ))
        + ψ₀ • (ContinuousLinearMap.id ℂ C(Circle, ℂ))) ψ₀ :=
    (hasFDerivAt_id ψ₀).mul (hasFDerivAt_id ψ₀)
  have hcomp := circleMean.hasFDerivAt.comp ψ₀ hsq
  convert hcomp using 1
  · rfl
  · ext h
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      add_apply, smul_apply,
      ContinuousLinearMap.coe_id', id_eq, smul_apply,
      circleMeanMul_apply, map_add]
    rw [mul_comm h ψ₀]
    simp [smul_eq_mul, two_mul]

/-! ### Values at the identity -/

theorem circleMean_one : circleMean (1 : C(Circle, ℂ)) = 1 := by
  rw [circleMean_apply]
  simp only [ContinuousMap.one_apply, intervalIntegral.integral_const, sub_zero, real_smul,
    mul_one]
  rw [← Complex.ofReal_mul, inv_mul_cancel₀ (by positivity : (2 * Real.pi) ≠ 0)]
  norm_num

theorem circleMean_eq_zero_of_exp (a : ℂ) (ha : a ≠ 0) (F : C(Circle, ℂ))
    (hF : ∀ θ : ℝ, F (Circle.exp θ) = Complex.exp (a * (θ : ℂ)))
    (hper : Complex.exp (a * ((2 * Real.pi : ℝ) : ℂ)) = 1) : circleMean F = 0 := by
  rw [circleMean_apply, intervalIntegral.integral_congr (fun θ _ => hF θ),
    integral_exp_mul_complex ha, hper]
  simp

theorem wPlus_mul_wMinus : wPlus * wMinus = 1 := by
  ext ζ
  simp only [ContinuousMap.mul_apply, wPlus_apply, wMinus_apply, ContinuousMap.one_apply]
  rw [mul_comm]
  exact star_mul_self_of_norm_one (Circle.norm_coe ζ)

theorem isUnit_wPlus : IsUnit wPlus := isUnit_toCM (id : Circle → Circle) continuous_id

theorem ringInverse_wPlus : Ring.inverse wPlus = wMinus := by
  have h := Ring.inverse_mul_cancel wPlus isUnit_wPlus
  calc Ring.inverse wPlus = Ring.inverse wPlus * (wPlus * wMinus) := by
        rw [wPlus_mul_wMinus, mul_one]
    _ = (Ring.inverse wPlus * wPlus) * wMinus := by rw [mul_assoc]
    _ = wMinus := by rw [h, one_mul]

theorem momA_wPlus : momA wPlus = 1 := by
  rw [momA, wPlus_mul_wMinus, circleMean_one]

theorem momB_wPlus : momB wPlus = 0 := by
  refine circleMean_eq_zero_of_exp (2 * Complex.I) (by simp) _ (fun θ => ?_) ?_
  · simp only [ContinuousMap.mul_apply, wPlus_apply, Circle.coe_exp, ← Complex.exp_add]
    congr 1; ring
  · rw [show (2 * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)
        = ((2 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I 2

theorem momQ_wPlus : momQ wPlus = 0 := momB_wPlus

theorem momA'_wPlus : momA' wPlus = 1 := by
  rw [momA', ringInverse_wPlus, mul_comm, wPlus_mul_wMinus, circleMean_one]

theorem momB'_wPlus : momB' wPlus = 0 := by
  rw [momB', ringInverse_wPlus]
  refine circleMean_eq_zero_of_exp (-2 * Complex.I) (by simp) _ (fun θ => ?_) ?_
  · simp only [ContinuousMap.mul_apply, wMinus_apply, Circle.coe_exp, Complex.star_def,
      ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  · rw [show (-2 * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)
        = ((-2 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I (-2)

theorem lemma6Fun_wPlus : lemma6Fun wPlus = 0 := by
  rw [lemma6Fun, momA_wPlus, momB_wPlus, momQ_wPlus, momA'_wPlus, momB'_wPlus]
  norm_num

/-- `h ↦ 3 ⨍ h(ζ) ζ dm(ζ)`: the differential of the Lemma 6 function at the
identity, and the source of the constant `3` in Corollary 1 and of the `3/π`
in formula (9.1). -/
def lemma6Deriv : C(Circle, ℂ) →L[ℂ] ℂ := (3 : ℂ) • circleMeanMul wPlus

@[simp] theorem lemma6Deriv_apply (h : C(Circle, ℂ)) :
    lemma6Deriv h = 3 * circleMean (h * wPlus) := rfl

theorem hasFDerivAt_lemma6Fun_id : HasFDerivAt lemma6Fun lemma6Deriv wPlus := by
  have hu := isUnit_wPlus
  have hA := hasFDerivAt_momA wPlus
  have hB := hasFDerivAt_momB wPlus
  have hQ := hasFDerivAt_momQ wPlus
  have hA' : DifferentiableAt ℂ momA' wPlus := (analyticAt_momA' hu).differentiableAt
  have hB' : DifferentiableAt ℂ momB' wPlus := (analyticAt_momB' hu).differentiableAt
  have hN : HasFDerivAt (fun ψ => momB ψ + momQ ψ * momA' ψ) _ wPlus :=
    hB.add (hQ.mul hA'.hasFDerivAt)
  have hD : HasFDerivAt (fun ψ => momA ψ + momQ ψ * momB' ψ) _ wPlus :=
    hA.add (hQ.mul hB'.hasFDerivAt)
  have hDne : momA wPlus + momQ wPlus * momB' wPlus ≠ 0 := by
    rw [momA_wPlus, momQ_wPlus]; norm_num
  have hinv := (hasDerivAt_inv hDne).comp_hasFDerivAt wPlus hD
  have hmul := hN.mul hinv
  have hfun : ((fun ψ => momB ψ + momQ ψ * momA' ψ) *
      ((fun y : ℂ => y⁻¹) ∘ fun ψ => momA ψ + momQ ψ * momB' ψ)) = lemma6Fun := by
    funext ψ
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [lemma6Fun, div_eq_mul_inv]
  rw [hfun] at hmul
  convert hmul using 1
  ext h
  simp [momA_wPlus, momB_wPlus, momQ_wPlus, momA'_wPlus, momB'_wPlus, smul_eq_mul]
  ring

end Lemma6


/-! ### Theorem 4

`σ(μ) = μ(E(φ^μ))` is a composite of two maps, and the paper's proof of
Theorem 4 is that each factor is analytic:

* `μ ↦ φ^μ`, the boundary values of the Ahlfors–Bers solution, is holomorphic
  in `μ` — the analytic dependence half of the measurable Riemann mapping
  theorem, cited but not proved in the paper and not available here
  (`beltramiSolution_existsUnique` is proved, via `DouadyEarleExt.AhlforsBers`,
  but records no dependence on `μ` at all);
* `φ ↦ μ(E(φ))(z)` is holomorphic — that is Lemma 6.

So Theorem 4 is stated below with those two factors as hypotheses — `c`, `hcAn`
and `hcEq` for the first, and `V, f, hV, hcV, hfAn, hfid` for the second — and
what is proved is the composition: that a real-analytic curve into
`C(S¹, ℂ)` followed by a `ℂ`-analytic function is real-analytic, and that the
gluing is legitimate near `t = 0`, where `tν` is still a Beltrami coefficient
(`eventually_isBeltramiCoeff_smul`) and the curve still lies in `V`.

For `z = 0` the second bundle is exactly the conclusion of
`lemma6_holomorphic_extension`.  For other `z` it is the same statement with
`0` replaced by `z`, which follows from the case `z = 0` by conformal
naturality (`extension_naturality`) and `complexDilatation_comp_right`, once
`E(φ)` is known to be differentiable — the same missing input as in Lemma 6. -/

section Theorem4

open Topology Filter

theorem isBeltramiCoeff_smul {ν : ℂ → ℂ} (hν : IsBeltramiCoeff ν) {t : ℝ} (ht : |t| ≤ 1) :
    IsBeltramiCoeff (fun w => (t : ℂ) * ν w) := by
  obtain ⟨hmeas, k, hk, hb⟩ := hν
  refine ⟨measurable_const.mul hmeas, k, hk, fun w hw => ?_⟩
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |t| * ‖ν w‖ ≤ 1 * ‖ν w‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
    _ = ‖ν w‖ := one_mul _
    _ ≤ k := hb w hw

theorem eventually_isBeltramiCoeff_smul {ν : ℂ → ℂ} (hν : IsBeltramiCoeff ν) :
    ∀ᶠ t : ℝ in nhds 0, IsBeltramiCoeff (fun w => (t : ℂ) * ν w) := by
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) one_pos] with t ht
  refine isBeltramiCoeff_smul hν (le_of_lt ?_)
  simpa [Real.dist_eq] using ht

/-- **Theorem 4**: `σ : M → M` is real-analytic. We record this along each
real ray `t ↦ tν` through the origin, which is exactly the form used in the
proof of Proposition 5 below.

`c, hcAn, hcEq` are the analytic dependence of `φ^μ` on `μ` (Ahlfors–Bers) and
`V, f, hV, hcV, hfAn, hfid` are Lemma 6 at the point `z`; see the section
header.  The conclusion is stated verbatim as before. -/
theorem theorem4_sigmaMap_analytic_in_t (ν : ℂ → ℂ) (hν : IsBeltramiCoeff ν) (z : ℂ)
    (hz : ‖z‖ < 1)
    (c : ℝ → C(Circle, ℂ)) (hcAn : AnalyticAt ℝ c 0)
    (hcEq : ∀ t : ℝ, IsBeltramiCoeff (fun w => (t : ℂ) * ν w) →
      ∃ (_ : Function.Bijective (beltramiBoundary (fun w => (t : ℂ) * ν w)))
        (hcont : Continuous (beltramiBoundary (fun w => (t : ℂ) * ν w))),
        c t = toCM (beltramiBoundary (fun w => (t : ℂ) * ν w)) hcont)
    (V : Set C(Circle, ℂ)) (f : C(Circle, ℂ) → ℂ) (hV : IsOpen V) (hcV : c 0 ∈ V)
    (hfAn : AnalyticOn ℂ f V)
    (hfid : ∀ (φ : Circle → Circle), Function.Bijective φ → ∀ hφc : Continuous φ,
      toCM φ hφc ∈ V → f (toCM φ hφc) = complexDilatation (extension φ) z) :
    ∃ F : ℝ → ℂ, AnalyticAt ℝ F 0 ∧
      ∀ t : ℝ, IsBeltramiCoeff (fun w => (t:ℂ) * ν w) →
        sigmaMap (fun w => (t:ℂ) * ν w) z = F t := by
  refine ⟨fun t => sigmaMap (fun w => (t : ℂ) * ν w) z, ?_, fun t _ => rfl⟩
  have hfc : AnalyticAt ℝ (fun t : ℝ => f (c t)) 0 :=
    ((hfAn.analyticAt (hV.mem_nhds hcV)).restrictScalars (𝕜 := ℝ)).comp hcAn
  refine hfc.congr ?_
  filter_upwards [eventually_isBeltramiCoeff_smul hν,
    hcAn.continuousAt.preimage_mem_nhds (hV.mem_nhds hcV)] with t hbc hmem
  obtain ⟨hbij, hcont', heq⟩ := hcEq t hbc
  have hmem' : c t ∈ V := hmem
  rw [heq] at hmem' ⊢
  rw [hfid _ hbij hcont' hmem']
  rfl

end Theorem4

/-! ## Proposition 5 and its corollaries -/

/-- The linear map `σ'(0) : L^∞(D, ℂ) → L^∞(D, ℂ)` of formula (9.1):
`σ'(0)ν(z) = (3/π) ∬_D ν(w)(1-|z|²)²/(1-z̄w)⁴ du dv`. -/
def sigmaDerivZero (ν : ℂ → ℂ) (z : ℂ) : ℂ :=
  (3 / Real.pi) * ∫ w in Metric.ball (0:ℂ) 1,
    ν w * (1 - ‖z‖ ^ 2) ^ 2 / (1 - star z * w) ^ 4

/-! ### Proposition 5

`σ(tν)(z) = f(c(t))` near `t = 0`, with `c` the boundary curve `t ↦ φ^{tν}` and
`f` the Lemma 6 function at `z`, so `σ'(0)ν(z) = Df(c(0))[ċ(0)]`.  Three inputs
go into that:

* `ċ(0)`, the Ahlfors–Bers first variation of the solution of the Beltrami
  equation — hypothesis `hcD`, unavailable here for the same reason as in
  Theorem 4;
* `Df` at the identity, which for `z = 0` is **proved** above to be
  `h ↦ 3 ⨍ h(ζ) ζ dm(ζ)` (`hasFDerivAt_lemma6Fun_id`);
* the identification of `Df(c 0)[ċ(0)]` with the integral (9.1) — hypothesis
  `hker`.  At `z = 0` the previous item makes this the concrete Fubini identity
  `3 ⨍ ċ(ζ) ζ dm(ζ) = σ'(0)ν(0)`, which is how `prop5_at_zero` states it.

What the proof supplies is the assembly: the gluing near `0`, the chain rule
for `ℝ`-differentiation of a `ℂ`-differentiable `f` along a real curve, the
identity `σ(0)(z) = 0` (derived, not assumed), and the translation of
`HasDerivAt` into the little-o form the statement uses. -/

theorem prop5_sigmaMap_deriv_zero (ν : ℂ → ℂ) (hν : IsBeltramiCoeff ν) (z : ℂ) (hz : ‖z‖ < 1)
    (c : ℝ → C(Circle, ℂ)) (cdot : C(Circle, ℂ)) (hcD : HasDerivAt c cdot 0)
    (hcEq : ∀ t : ℝ, IsBeltramiCoeff (fun w => (t : ℂ) * ν w) →
      ∃ (_ : Function.Bijective (beltramiBoundary (fun w => (t : ℂ) * ν w)))
        (hcont : Continuous (beltramiBoundary (fun w => (t : ℂ) * ν w))),
        c t = toCM (beltramiBoundary (fun w => (t : ℂ) * ν w)) hcont)
    (V : Set C(Circle, ℂ)) (f : C(Circle, ℂ) → ℂ) (hV : IsOpen V) (hcV : c 0 ∈ V)
    (hfid : ∀ (φ : Circle → Circle), Function.Bijective φ → ∀ hφc : Continuous φ,
      toCM φ hφc ∈ V → f (toCM φ hφc) = complexDilatation (extension φ) z)
    (L : C(Circle, ℂ) →L[ℂ] ℂ) (hfD : HasFDerivAt f L (c 0)) (hf0 : f (c 0) = 0)
    (hker : L cdot = sigmaDerivZero ν z) :
    Filter.Tendsto
      (fun t : ℝ => ‖sigmaMap (fun w => (t:ℂ) * ν w) z - (t:ℂ) * sigmaDerivZero ν z‖ / |t|)
      (nhdsWithin 0 {(0:ℝ)}ᶜ) (nhds 0) := by
  -- near `0` the map agrees with `f ∘ c`
  have hglue : ∀ᶠ t : ℝ in nhds 0, sigmaMap (fun w => (t : ℂ) * ν w) z = f (c t) := by
    filter_upwards [eventually_isBeltramiCoeff_smul hν,
      hcD.continuousAt.preimage_mem_nhds (hV.mem_nhds hcV)] with t hbc hmem
    obtain ⟨hbij, hcont', heq⟩ := hcEq t hbc
    have hmem' : c t ∈ V := hmem
    rw [heq] at hmem' ⊢
    rw [hfid _ hbij hcont' hmem']
    rfl
  have hcomp : HasDerivAt (fun t : ℝ => f (c t)) (L cdot) 0 :=
    (hfD.restrictScalars ℝ).comp_hasDerivAt 0 hcD
  have hF : HasDerivAt (fun t : ℝ => sigmaMap (fun w => (t : ℂ) * ν w) z) (L cdot) 0 :=
    hcomp.congr_of_eventuallyEq hglue
  have hF0 : sigmaMap (fun w => ((0:ℝ) : ℂ) * ν w) z = 0 := by
    rw [hglue.self_of_nhds, hf0]
  have htend := hasDerivAt_iff_tendsto.1 hF
  refine Filter.Tendsto.congr (fun t => ?_) (htend.mono_left nhdsWithin_le_nhds)
  simp only [sub_zero, hF0, hker, Real.norm_eq_abs, Complex.real_smul]
  rw [div_eq_inv_mul]

theorem prop5_at_zero (ν : ℂ → ℂ) (hν : IsBeltramiCoeff ν)
    (c : ℝ → C(Circle, ℂ)) (cdot : C(Circle, ℂ)) (hcD : HasDerivAt c cdot 0)
    (hc0 : c 0 = wPlus)
    (hcEq : ∀ t : ℝ, IsBeltramiCoeff (fun w => (t : ℂ) * ν w) →
      ∃ (_ : Function.Bijective (beltramiBoundary (fun w => (t : ℂ) * ν w)))
        (hcont : Continuous (beltramiBoundary (fun w => (t : ℂ) * ν w))),
        c t = toCM (beltramiBoundary (fun w => (t : ℂ) * ν w)) hcont)
    (V : Set C(Circle, ℂ)) (hV : IsOpen V) (hcV : c 0 ∈ V)
    (hfid : ∀ (φ : Circle → Circle), Function.Bijective φ → ∀ hφc : Continuous φ,
      toCM φ hφc ∈ V → lemma6Fun (toCM φ hφc) = complexDilatation (extension φ) 0)
    (hker : 3 * circleMean (cdot * wPlus) = sigmaDerivZero ν 0) :
    Filter.Tendsto
      (fun t : ℝ => ‖sigmaMap (fun w => (t:ℂ) * ν w) 0 - (t:ℂ) * sigmaDerivZero ν 0‖ / |t|)
      (nhdsWithin 0 {(0:ℝ)}ᶜ) (nhds 0) := by
  refine prop5_sigmaMap_deriv_zero ν hν 0 (by norm_num) c cdot hcD hcEq V lemma6Fun hV hcV hfid
    lemma6Deriv (by rw [hc0]; exact hasFDerivAt_lemma6Fun_id) ?_ ?_
  · rw [hc0]; exact lemma6Fun_wPlus
  · rw [lemma6Deriv_apply]; exact hker

/-! ### Corollary 1

Unlike everything else in this file, Corollary 1 is a statement purely about
the integral `sigmaDerivZero` — it mentions neither `extension` nor `sigmaMap`
— and it is proved here outright, with no hypotheses and no `sorryAx`.

The one thing it needs is the sharp identity

`(1 - |z|²)² ∫_D |1 - z̄w|⁻⁴ dA(w) = π`   (`integral_diskAut_jacobian`),

without which the bound `3k` is not reached: the crude estimate
`|1 - z̄w| ≥ 1 - |z|` only gives `3k(1+|z|)²/(1-|z|)²`.  The identity is the
change-of-variables formula for the disk automorphism `g_z`, whose real
Jacobian determinant is exactly `|g_z'(w)|² = (1-|z|²)²/|1-z̄w|⁴`
(`det_diskAutFDeriv`, via `LinearMap.det_restrictScalars`), and which maps `D`
bijectively onto `D` (`diskAut_image_ball`, `injOn_diskAut_ball`, using
`diskAut_inj` and the inverse `g_z⁻¹ = g_{-z}`).  So the integral is the area
of `g_z(D) = D`, namely `π`.

Two points about the estimate itself.  `ν` is not assumed measurable, so the
Bochner integral may be the junk value `0`; that costs nothing, since `k ≥ 0`
follows from `‖ν 0‖ ≤ k` and `integral_mono_of_nonneg` does not require the
smaller function to be integrable.  Integrability of the majorant is obtained
from the identity itself: its integral is `π ≠ 0`, so it cannot be the junk
value. -/

section Corollary1

open MeasureTheory

/-- The `ℝ`-linear differential of `g_a` at `w`: multiplication by
`g_a'(w) = (1-|a|²)/(1-āw)²`. -/
def diskAutFDeriv (a w : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
    ((1 - star a * a) / (1 - star a * w) ^ 2)).restrictScalars ℝ


theorem hasFDerivAt_diskAut {a : ℂ} (ha : ‖a‖ < 1) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    HasFDerivAt (diskAut a) (diskAutFDeriv a w) w :=
  ((hasDerivAt_diskAut ha hw).hasFDerivAt).restrictScalars ℝ

theorem det_diskAutFDeriv (a w : ℂ) :
    (diskAutFDeriv a w).det = ‖(1 - star a * a) / (1 - star a * w) ^ 2‖ ^ 2 := by
  simp [diskAutFDeriv, ContinuousLinearMap.det, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]
  ring

theorem diskAut_diskAut_neg {a : ℂ} (ha : ‖a‖ < 1) {u : ℂ} (hu : ‖u‖ < 1) :
    diskAut a (diskAut (-a) u) = u := by
  have hna : ‖-a‖ < 1 := by rwa [norm_neg]
  have h1 : (1 : ℂ) - star (-a) * u ≠ 0 := diskAut_denom_ne_zero (-a) u hna hu.le
  have hA : (1 : ℂ) + star a * u ≠ 0 := by
    intro hz; apply h1; rw [star_neg]; linear_combination hz
  have hA' : (1 : ℂ) + u * star a ≠ 0 := by rwa [mul_comm u (star a)]
  have h2 : (1 : ℂ) - a * star a ≠ 0 := one_sub_self_mul_star_ne_zero a ha
  have h2' : (1 : ℂ) - star a * a ≠ 0 := by rwa [mul_comm (star a) a]
  have hnum : diskAut (-a) u = (u + a) / (1 + star a * u) := by
    simp only [diskAut, star_neg]
    congr 1 <;> ring
  have hd2 : (1 : ℂ) - star a * ((u + a) / (1 + star a * u))
      = (1 - a * star a) / (1 + star a * u) := by
    rw [eq_div_iff hA]
    field_simp
    ring
  have hn2 : (u + a) / (1 + star a * u) - a = u * (1 - a * star a) / (1 + star a * u) := by
    rw [eq_div_iff hA]
    field_simp
    ring
  rw [diskAut, hnum, hd2, hn2]
  field_simp

theorem diskAut_image_ball {a : ℂ} (ha : ‖a‖ < 1) :
    diskAut a '' (Metric.ball (0:ℂ) 1) = Metric.ball (0:ℂ) 1 := by
  ext u
  simp only [Set.mem_image, Metric.mem_ball, dist_zero_right]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact diskAut_maps_disk_to_disk a w ha hw
  · intro hu
    exact ⟨diskAut (-a) u, diskAut_maps_disk_to_disk (-a) u (by rwa [norm_neg]) hu,
      diskAut_diskAut_neg ha hu⟩

theorem injOn_diskAut_ball {a : ℂ} (ha : ‖a‖ < 1) :
    Set.InjOn (diskAut a) (Metric.ball (0:ℂ) 1) := fun x hx y hy h =>
  diskAut_inj ha (le_of_lt (by simpa using hx)) (le_of_lt (by simpa using hy)) h

theorem norm_one_sub_star_self {z : ℂ} (hz : ‖z‖ < 1) : ‖(1 : ℂ) - star z * z‖ = 1 - ‖z‖ ^ 2 := by
  rw [Complex.star_def, Complex.conj_mul', show (1 : ℂ) - ((‖z‖ : ℝ) : ℂ) ^ 2
      = (((1 - ‖z‖ ^ 2 : ℝ)) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by nlinarith [norm_nonneg z])]

/-- The area identity `(1-|z|²)² ∫_D |1 - z̄w|⁻⁴ dA(w) = π`: the integrand is the
Jacobian of the disk automorphism `g_z`, which maps `D` bijectively onto `D`. -/
theorem integral_diskAut_jacobian {z : ℂ} (hz : ‖z‖ < 1) :
    ∫ w in Metric.ball (0:ℂ) 1, (1 - ‖z‖ ^ 2) ^ 2 / ‖1 - star z * w‖ ^ 4 = Real.pi := by
  have hcv := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
    (μ := volume) (measurableSet_ball (x := (0:ℂ)) (ε := 1))
    (f := diskAut z) (f' := diskAutFDeriv z)
    (fun x hx => (hasFDerivAt_diskAut hz (le_of_lt (by simpa using hx))).hasFDerivWithinAt)
    (injOn_diskAut_ball hz) (fun _ => (1:ℝ))
  rw [diskAut_image_ball hz] at hcv
  rw [MeasureTheory.integral_const] at hcv
  simp only [smul_eq_mul, mul_one] at hcv
  have hvol : ((volume.restrict (Metric.ball (0:ℂ) 1)).real Set.univ) = Real.pi := by
    simp [MeasureTheory.measureReal_def, Complex.volume_ball]
  rw [← hvol, hcv]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_ball (fun w hw => ?_)
  have hwle : ‖w‖ ≤ 1 := le_of_lt (by simpa using hw)
  rw [det_diskAutFDeriv, abs_of_nonneg (by positivity), norm_div, norm_pow,
    norm_one_sub_star_self hz, div_pow]
  ring_nf

theorem norm_one_sub_sq_norm {z : ℂ} (hz : ‖z‖ < 1) :
    ‖(1 : ℂ) - ((‖z‖ : ℝ) : ℂ) ^ 2‖ = 1 - ‖z‖ ^ 2 := by
  rw [show (1 : ℂ) - ((‖z‖ : ℝ) : ℂ) ^ 2 = (((1 - ‖z‖ ^ 2 : ℝ)) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by nlinarith [norm_nonneg z])]

/-- **Corollary 1**: `‖σ'(0)ν‖_∞ ≤ 3‖ν‖_∞`. -/
theorem corollary1_sigmaDerivZero_bound (ν : ℂ → ℂ) (k : ℝ) (hk : ∀ w : ℂ, ‖w‖ < 1 → ‖ν w‖ ≤ k) :
    ∀ z : ℂ, ‖z‖ < 1 → ‖sigmaDerivZero ν z‖ ≤ 3 * k := by
  intro z hz
  have hpi := Real.pi_pos
  have hk0 : 0 ≤ k := le_trans (norm_nonneg _) (hk 0 (by norm_num))
  have hjac := integral_diskAut_jacobian hz
  -- the majorant is integrable, since its integral is `π ≠ 0`
  have hint : MeasureTheory.IntegrableOn
      (fun w : ℂ => (1 - ‖z‖ ^ 2) ^ 2 / ‖1 - star z * w‖ ^ 4) (Metric.ball (0:ℂ) 1) := by
    by_contra hcon
    rw [MeasureTheory.integral_undef hcon] at hjac
    exact absurd hjac.symm (ne_of_gt hpi)
  have hintk : MeasureTheory.IntegrableOn
      (fun w : ℂ => k * ((1 - ‖z‖ ^ 2) ^ 2 / ‖1 - star z * w‖ ^ 4)) (Metric.ball (0:ℂ) 1) :=
    hint.const_mul k
  -- pointwise bound
  have hpt : ∀ᵐ w ∂(volume.restrict (Metric.ball (0:ℂ) 1)),
      ‖ν w * (1 - ((‖z‖ : ℝ) : ℂ) ^ 2) ^ 2 / (1 - star z * w) ^ 4‖
        ≤ k * ((1 - ‖z‖ ^ 2) ^ 2 / ‖1 - star z * w‖ ^ 4) := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_ball).2
      (Filter.Eventually.of_forall (fun w hw => ?_))
    have hw1 : ‖w‖ < 1 := by simpa using hw
    have hden : ‖1 - star z * w‖ ^ 4 > 0 := by
      have := diskAut_denom_ne_zero z w hz hw1.le
      positivity
    rw [norm_div, norm_mul, norm_pow, norm_pow, norm_one_sub_sq_norm hz, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (hk w hw1) (by positivity)
  have hnn : (0 : ℂ → ℝ) ≤ᵐ[volume.restrict (Metric.ball (0:ℂ) 1)]
      fun w => ‖ν w * (1 - ((‖z‖ : ℝ) : ℂ) ^ 2) ^ 2 / (1 - star z * w) ^ 4‖ :=
    Filter.Eventually.of_forall (fun w => norm_nonneg _)
  have hle := MeasureTheory.integral_mono_of_nonneg hnn hintk hpt
  rw [MeasureTheory.integral_const_mul, hjac] at hle
  -- assemble
  rw [sigmaDerivZero, norm_mul]
  have hc : ‖(3 / (Real.pi : ℂ))‖ = 3 / Real.pi := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
    norm_num
  rw [hc]
  calc 3 / Real.pi * ‖∫ w in Metric.ball (0:ℂ) 1,
        ν w * (1 - ((‖z‖ : ℝ) : ℂ) ^ 2) ^ 2 / (1 - star z * w) ^ 4‖
      ≤ 3 / Real.pi * ∫ w in Metric.ball (0:ℂ) 1,
          ‖ν w * (1 - ((‖z‖ : ℝ) : ℂ) ^ 2) ^ 2 / (1 - star z * w) ^ 4‖ :=
        mul_le_mul_of_nonneg_left (MeasureTheory.norm_integral_le_integral_norm _)
          (by positivity)
    _ ≤ 3 / Real.pi * (k * Real.pi) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 3 * k := by field_simp

end Corollary1

/-! ### The sharpness remark

`σ'(0)1(z) = 3(1-|z|²)²` is the holomorphic companion of the identity behind
Corollary 1: there the integrand was `|g_z'|²`, the Jacobian, and the value came
out as the area of `g_z(D) = D`; here the integrand is `(1-z̄w)⁻⁴`, which is
holomorphic in `w`, and what is needed is the *area mean value property*

`∫_D F dA = π F(0)`   (`integral_ball_of_circleAverage`),

which Mathlib does not have for balls — it has the circle version
(`DiffContOnCl.circleAverage`).  It is obtained here by writing the disk
integral in polar coordinates (`polar_key`, via
`Complex.integral_comp_polarCoord_symm` applied to the indicator of `D`),
using Fubini to peel off the angular variable, and recognizing the inner
integral as `2π` times the circle average, which is `F 0` for every radius
`< 1`.  The radial integral `∫₀¹ r dr = 1/2` then supplies the factor `π`.

Together with `corollary1_sigmaDerivZero_bound` this pins the constant: the
bound `3k` is attained in the limit, and the `3` cannot be improved. -/

section Sharpness

open MeasureTheory

theorem polarCoord_symm_eq_circleMap (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
  simp [Complex.ofReal_cos, Complex.ofReal_sin]

theorem continuous_complexPolarCoord_symm : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
  simp only [Complex.polarCoord_symm_apply]
  fun_prop

theorem polar_key {F : ℂ → ℂ} :
    ∫ w in Metric.ball (0:ℂ) 1, F w
      = ∫ p in Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (-π) π, p.1 • F (Complex.polarCoord.symm p) := by
  have hSsub : Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (-π) π ⊆ Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π := by
    intro p hp
    exact ⟨hp.1.1, hp.2⟩
  rw [← MeasureTheory.integral_indicator measurableSet_ball,
    ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  rw [MeasureTheory.setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    (g := fun p : ℝ × ℝ => (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (-π) π).indicator
      (fun q : ℝ × ℝ => q.1 • F (Complex.polarCoord.symm q)) p) (fun p hp => ?_)]
  · rw [MeasureTheory.setIntegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo),
      Set.inter_eq_self_of_subset_right hSsub]
  · have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1]
    show p.1 • (Metric.ball (0:ℂ) 1).indicator F (Complex.polarCoord.symm p)
      = (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (-π) π).indicator
        (fun q : ℝ × ℝ => q.1 • F (Complex.polarCoord.symm q)) p
    by_cases h1 : p.1 < 1
    · have hmem : Complex.polarCoord.symm p ∈ Metric.ball (0:ℂ) 1 := by
        rw [Metric.mem_ball, dist_zero_right, hnorm]; exact h1
      have hpS : p ∈ Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (-π) π := ⟨⟨hp.1, h1⟩, hp.2⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hpS]
    · have hmem : Complex.polarCoord.symm p ∉ Metric.ball (0:ℂ) 1 := by
        rw [Metric.mem_ball, dist_zero_right, hnorm]; exact h1
      have hpS : p ∉ Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (-π) π := fun hc => h1 hc.1.2
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hpS, smul_zero]

/-- **Area mean value property on the unit disk**: if every circle average of
`F` about `0` of radius `< 1` equals `F 0`, then `∫_D F dA = π F(0)`. -/
theorem integral_ball_of_circleAverage {F : ℂ → ℂ}
    (hF : ContinuousOn F (Metric.closedBall (0:ℂ) 1))
    (hmv : ∀ r : ℝ, 0 < r → r < 1 → circleAverage F 0 r = F 0) :
    ∫ w in Metric.ball (0:ℂ) 1, F w = (Real.pi : ℂ) * F 0 := by
  have hpi := Real.pi_pos
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-π) π) (Metric.closedBall (0:ℂ) 1) := by
    intro p hp
    show Complex.polarCoord.symm p ∈ Metric.closedBall (0:ℂ) 1
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm]
    exact abs_le.2 ⟨by linarith [hp.1.1], hp.1.2⟩
  have hcont : ContinuousOn (fun p : ℝ × ℝ => p.1 • F (Complex.polarCoord.symm p))
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-π) π) :=
    (continuous_fst.continuousOn).smul (hF.comp continuous_complexPolarCoord_symm.continuousOn hmaps)
  have hsub : Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (-π) π ⊆ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-π) π :=
    Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self
  have hint : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => p.1 • F (Complex.polarCoord.symm p))
      (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (-π) π) volume :=
    (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set hsub
  have hinner : ∀ r ∈ Set.Ioo (0:ℝ) 1,
      (∫ θ in Set.Ioo (-π) π, r • F (Complex.polarCoord.symm (r, θ)))
        = (r * (2 * π)) • F 0 := by
    intro r hr
    have hcirc : ∫ θ in Set.Ioo (-π) π, F (Complex.polarCoord.symm (r, θ))
        = (2 * π) • circleAverage F 0 r := by
      have h1 : ∫ θ in Set.Ioo (-π) π, F (Complex.polarCoord.symm (r, θ))
          = ∫ θ in (-π)..π, F (circleMap 0 r θ) := by
        rw [intervalIntegral.integral_of_le (by linarith),
          MeasureTheory.integral_Ioc_eq_integral_Ioo]
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
          (fun θ _ => by rw [polarCoord_symm_eq_circleMap])
      have h2 := circleAverage_eq_integral_add (f := F) (c := 0) (R := r) (-π)
      rw [intervalIntegral.integral_comp_add_right (fun θ => F (circleMap 0 r θ)) (-π),
        show (0:ℝ) + -π = -π by ring, show 2 * π + -π = π by ring] at h2
      rw [h1, h2, smul_smul, mul_inv_cancel₀ (by positivity : (2 * π) ≠ 0), one_smul]
    rw [MeasureTheory.integral_smul, hcirc, hmv r hr.1 hr.2, smul_smul]
  rw [polar_key, MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.setIntegral_prod _ (by rwa [← MeasureTheory.Measure.volume_eq_prod])]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hinner,
    integral_smul_const]
  have hr : ∫ r in Set.Ioo (0:ℝ) 1, r * (2 * π) = π := by
    rw [MeasureTheory.integral_mul_const, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    simp [integral_id]
  rw [hr, Complex.real_smul]

/-- The remark following Corollary 1: for the constant density `ν ≡ 1`,
`σ'(0)ν(z) = 3(1-|z|²)²`, showing the constant `3` in Corollary 1 is sharp. -/
theorem sigmaDerivZero_const_one (z : ℂ) (hz : ‖z‖ < 1) :
    sigmaDerivZero (fun _ => 1) z = 3 * (1 - ‖z‖ ^ 2) ^ 2 := by
  have hpi := Real.pi_pos
  set F : ℂ → ℂ := fun w => (1 : ℂ) * (1 - ((‖z‖ : ℝ) : ℂ) ^ 2) ^ 2 / (1 - star z * w) ^ 4
    with hFdef
  have hdiff : ∀ w : ℂ, ‖w‖ ≤ 1 → DifferentiableAt ℂ F w := by
    intro w hw
    have hne : (1 : ℂ) - star z * w ≠ 0 := diskAut_denom_ne_zero z w hz hw
    rw [hFdef]
    exact (differentiableAt_const _).div
      (((differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id)).pow 4)
      (pow_ne_zero 4 hne)
  have hcontF : ContinuousOn F (Metric.closedBall (0:ℂ) 1) := fun w hw =>
    ((hdiff w (by simpa using hw)).continuousAt).continuousWithinAt
  have hmv : ∀ r : ℝ, 0 < r → r < 1 → circleAverage F 0 r = F 0 := by
    intro r hr0 hr1
    refine DiffContOnCl.circleAverage ?_
    constructor
    · intro w hw
      have : ‖w‖ ≤ 1 := by
        have := (Metric.mem_ball.1 hw)
        rw [dist_zero_right] at this
        rw [abs_of_pos hr0] at this
        linarith
      exact (hdiff w this).differentiableWithinAt
    · rw [closure_ball _ (by rw [abs_of_pos hr0]; exact ne_of_gt hr0)]
      refine hcontF.mono (fun w hw => ?_)
      rw [Metric.mem_closedBall, dist_zero_right] at hw ⊢
      rw [abs_of_pos hr0] at hw
      linarith
  have hF0 : F 0 = (1 - ((‖z‖ : ℝ) : ℂ) ^ 2) ^ 2 := by
    rw [hFdef]; simp
  rw [sigmaDerivZero]
  have hcongr : ∫ w in Metric.ball (0:ℂ) 1,
      (fun _ : ℂ => (1:ℂ)) w * (1 - ((‖z‖ : ℝ) : ℂ) ^ 2) ^ 2 / (1 - star z * w) ^ 4
      = (Real.pi : ℂ) * F 0 := integral_ball_of_circleAverage hcontF hmv
  rw [hcongr, hF0]
  have hne : ((Real.pi : ℝ) : ℂ) ≠ 0 := by
    simpa using (ne_of_gt hpi)
  field_simp

end Sharpness

/-! ### `qcCoeff` needs a nonempty admissible set

`qcCoeff φ = sInf {K | 1 ≤ K ∧ HasQCExtension φ K}` is Lean's junk value `0`
when `φ` has no quasiconformal extension, and then `qcCoeff φ ≤ 1 + δ` holds
vacuously while the conclusion of Corollary 2 demands a `Kstar ≤ 0` with
`1 ≤ Kstar`.  Such `φ` exist: `HasQCExtension` forces continuity
(`continuous_of_hasQCExtension`), so any discontinuous bijection of `S¹` — a
transposition, say — is one.  Corollary 2 therefore carries the hypothesis that
`φ` admits a quasiconformal extension. -/

theorem qcCoeff_eq_zero_of_no_qc (φ : Circle → Circle)
    (hno : ¬ ∃ K : ℝ, 1 ≤ K ∧ HasQCExtension φ K) : qcCoeff φ = 0 := by
  have hempty : {K : ℝ | 1 ≤ K ∧ HasQCExtension φ K} = ∅ := by
    ext K
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    exact hno ⟨K, h⟩
  rw [qcCoeff, hempty, Real.sInf_empty]

theorem corollary2_conclusion_false_of_no_qc (φ : Circle → Circle) (ε : ℝ) (hε : 0 < ε)
    (hno : ¬ ∃ K : ℝ, 1 ≤ K ∧ HasQCExtension φ K) :
    ¬ ∃ Kstar : ℝ, IsKQuasiconformalOn (extension φ) (Metric.ball (0:ℂ) 1) Kstar ∧
      Kstar ≤ (qcCoeff φ) ^ (3 + ε) := by
  rintro ⟨Kstar, ⟨hK1, -⟩, hKle⟩
  rw [qcCoeff_eq_zero_of_no_qc φ hno, Real.zero_rpow (by linarith)] at hKle
  linarith

/-! ### Corollary 2

`K*(φ) ≤ K(φ)^{3+ε}` for `K(φ)` near `1`.  The analytic input is Proposition 5
together with Corollary 1: `σ(μ) = σ'(0)μ + o(‖μ‖)` with `‖σ'(0)‖ ≤ 3`, so the
Douady–Earle extension multiplies the dilatation by at most `3 + η` once `φ` is
close enough to conformal.  That is the hypothesis `hbound`; neither
Proposition 5 nor Theorem 2 (which supplies a `K*` at all) is available
unconditionally here.

What is proved is the passage from `hbound` to the stated exponent, and it is
not bookkeeping alone.  The witness `Kstar` can be taken to be `K^{3+ε}` itself,
since `t ↦ (t-1)/(t+1)` is increasing, so everything reduces to

`(3 + ε/2)·(K-1)/(K+1) ≤ (K^{3+ε} - 1)/(K^{3+ε} + 1)`,

which `cor2_numeric` establishes from Bernoulli's inequality for real exponents
(`one_add_mul_self_le_rpow_one_add`) with the *explicit* threshold

`δ = min δ₁ (ε / ((3+ε)(2+ε/2)))`.

The `ε` is genuinely needed rather than an artifact of the estimate: see
`cor2_exponent_three_insufficient`. -/

section Corollary2


/-- Why the `ε` cannot be dropped.  Corollary 1 allows the extension to
multiply the dilatation by `3`, and if it did so exactly then at `k = 1/10` the
exponent `3` would demand `13/7 ≤ (11/9)³ = 1331/729`, which is false.  The two
sides do agree through order `k²`; the discrepancy is `16k³` at third order. -/
theorem cor2_exponent_three_insufficient :
    ¬ ((1 + 3 * (1/10 : ℝ)) / (1 - 3 * (1/10)) ≤ ((1 + (1/10:ℝ)) / (1 - 1/10)) ^ (3:ℕ)) := by
  norm_num

/-- The elementary inequality behind Corollary 2: if the extension multiplies
the dilatation by at most `3 + ε/2` and `φ` is close enough to conformal, then
`K* ≤ K^{3+ε}`.  The `ε` is needed: at `s = 3k` exactly the two sides agree to
first order but `K*` loses at second order. -/
theorem cor2_numeric {ε x : ℝ} (hε : 0 < ε) (hx0 : 0 ≤ x)
    (hxδ : x ≤ ε / ((3 + ε) * (2 + ε / 2))) {t : ℝ} (ht : 1 + (3 + ε) * x ≤ t) :
    (3 + ε / 2) * (x / (2 + x)) ≤ (t - 1) / (t + 1) := by
  have hpos : (0:ℝ) < (3 + ε) * (2 + ε / 2) := by positivity
  have hkey : x * ((3 + ε) * (2 + ε / 2)) ≤ ε := by
    rw [← le_div_iff₀ hpos]; exact hxδ
  have hax : (0:ℝ) ≤ (3 + ε) * x := by positivity
  have ht1 : (1:ℝ) ≤ t := by linarith
  have hd1 : (0:ℝ) < 2 + x := by linarith
  have hd2 : (0:ℝ) < t + 1 := by linarith
  have hd3 : (0:ℝ) < 2 + (3 + ε) * x := by linarith
  -- step 1: `(t-1)/(t+1) ≥ a/(2+a)` for `a = (3+ε)x`
  have step1 : (3 + ε) * x / (2 + (3 + ε) * x) ≤ (t - 1) / (t + 1) := by
    rw [div_le_div_iff₀ hd3 hd2]
    nlinarith
  -- step 2: the cross-multiplied form of the target
  have step2 : (3 + ε / 2) * (x / (2 + x)) ≤ (3 + ε) * x / (2 + (3 + ε) * x) := by
    rw [mul_div_assoc'] at *
    rw [div_le_div_iff₀ hd1 hd3]
    nlinarith
  linarith

/-- **Corollary 2**: given `ε > 0` there is `δ > 0` such that
`K*(φ) ≤ K(φ)^{3+ε}` whenever `K(φ) ≤ 1 + δ`.

`hbound` is Proposition 5 together with Corollary 1: the extension multiplies
the dilatation by at most `3 + η` near the identity.  See the section header. -/
theorem corollary2_Kstar_bound (hbound : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ φ : Circle → Circle, Function.Bijective φ →
        (∃ K : ℝ, 1 ≤ K ∧ HasQCExtension φ K) → qcCoeff φ ≤ 1 + δ →
        ∀ z ∈ Metric.ball (0:ℂ) 1,
          ‖complexDilatation (extension φ) z‖
            ≤ (3 + η) * ((qcCoeff φ - 1) / (qcCoeff φ + 1))) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ φ : Circle → Circle, Function.Bijective φ →
        (∃ K : ℝ, 1 ≤ K ∧ HasQCExtension φ K) → qcCoeff φ ≤ 1 + δ →
        ∃ Kstar : ℝ, IsKQuasiconformalOn (extension φ) (Metric.ball (0:ℂ) 1) Kstar ∧
          Kstar ≤ (qcCoeff φ) ^ (3 + ε) := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, hδ₁spec⟩ := hbound (ε / 2) (by linarith)
  have hδ₂ : (0:ℝ) < ε / ((3 + ε) * (2 + ε / 2)) := by positivity
  refine ⟨min δ₁ (ε / ((3 + ε) * (2 + ε / 2))), lt_min hδ₁ hδ₂, ?_⟩
  intro φ hφ hex hK
  obtain ⟨K₀, hK₀1, hK₀⟩ := hex
  have hK1 : 1 ≤ qcCoeff φ := one_le_qcCoeff φ K₀ hK₀1 hK₀
  have hx0 : (0:ℝ) ≤ qcCoeff φ - 1 := by linarith
  have hmin1 := min_le_left δ₁ (ε / ((3 + ε) * (2 + ε / 2)))
  have hmin2 := min_le_right δ₁ (ε / ((3 + ε) * (2 + ε / 2)))
  have hxδ₂ : qcCoeff φ - 1 ≤ ε / ((3 + ε) * (2 + ε / 2)) := by linarith
  have hKδ₁ : qcCoeff φ ≤ 1 + δ₁ := by linarith
  have hbern : 1 + (3 + ε) * (qcCoeff φ - 1) ≤ (qcCoeff φ) ^ (3 + ε) := by
    have h := one_add_mul_self_le_rpow_one_add (s := qcCoeff φ - 1) (by linarith)
      (p := 3 + ε) (by linarith)
    rwa [show (1:ℝ) + (qcCoeff φ - 1) = qcCoeff φ by ring] at h
  have hone : (1:ℝ) ≤ (qcCoeff φ) ^ (3 + ε) := by
    have : (0:ℝ) ≤ (3 + ε) * (qcCoeff φ - 1) := by positivity
    linarith
  refine ⟨(qcCoeff φ) ^ (3 + ε), ⟨hone, fun z hz => ?_⟩, le_refl _⟩
  refine le_trans (hδ₁spec φ hφ ⟨K₀, hK₀1, hK₀⟩ hKδ₁ z hz) ?_
  have hrw : qcCoeff φ + 1 = 2 + (qcCoeff φ - 1) := by ring
  rw [hrw]
  exact cor2_numeric hε hx0 hxδ₂ hbern

end Corollary2

end
