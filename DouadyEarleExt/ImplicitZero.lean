/-
# Implicit differentiation of the barycentric equation at the origin

`HasImplicitDerivAtZero φ` (`Analytic.lean`) records the two linear equations
that the Wirtinger derivatives of `E(φ)` satisfy at `0` when `E(φ)(0) = 0`:

  `Φ_z(0) = c₁ + q · conj Φ_z̄(0)`,  `Φ_z̄(0) = c₋₁ + q · conj Φ_z(0)`,

with `c₁ = ⨍ φ ζ̄`, `c₋₁ = ⨍ φ ζ`, `q = ⨍ φ²`.  This file proves it for every
homeomorphism with `E(φ)(0) = 0`, by implicit differentiation of the
barycentric equation (`exists_implicit_fderiv`, `wirt_implicit_of_graph_eq_zero`).
Orientation plays no role: the two equations hold whenever `E(φ)` solves (3.1)
near `0`.

Two consequences:

* **Lemma 6** loses its hypothesis `himp` (`lemma6_holomorphic_extension'`);
* it is the input of the pointwise formula `μ_{E(g)}(0) = N/D` in the forward
  inequality of the vanishing-Carleson development (`VanishingCarleson`).
-/
import Mathlib
import DouadyEarleExt.Analytic

open Complex

noncomputable section

/-- **Implicit differentiation of (3.1) at `(0, 0)`.**  For a homeomorphism
`φ` of `S¹` whose extension vanishes at the origin, the Wirtinger derivatives of
`E(φ)` at `0` satisfy the two linear equations of `HasImplicitDerivAtZero`. -/
theorem hasImplicitDerivAtZero (φ : Circle → Circle) (hφ : Function.Bijective φ)
    (hφc : Continuous φ) (h0 : extension φ 0 = 0) :
    HasImplicitDerivAtZero φ hφc := by
  have hz0 : ‖(0:ℂ)‖ < 1 := by simp
  obtain ⟨L, M, hΦ, hF, hMw, -⟩ := exists_implicit_fderiv φ hφ hφc 0 hz0
  set u : C(Circle, ℂ) := toComplexMap ⟨φ, hφc⟩ with hudef
  -- the three moments, in the normalizations of `Analytic.lean`
  have hA1 : meanCLM (u * iotaBarX) = momA (toCM φ hφc) := by
    rw [meanCLM_apply, momA, circleMean_apply]
    congr 1
  have hB1 : meanCLM (u * iotaX) = momB (toCM φ hφc) := by
    rw [meanCLM_apply, momB, circleMean_apply]
    congr 1
  have hQ1 : harmonicMeasureAvg 0 (fun ζ => (diskAut 0 ((φ ζ : Circle) : ℂ)) ^ 2)
      = momQ (toCM φ hφc) := by
    rw [harmonicMeasureAvg_zero_eq, momQ, circleMean_apply]
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp [diskAut, sq]
  -- the `z`-partial of `M`: formula (3.2) at the origin
  have hF0 := hF
  rw [h0] at hF0
  have hMz : ∀ v : ℂ, M (v, 0)
      = momA (toCM φ hφc) * v + momB (toCM φ hφc) * star v := by
    have hsl : HasFDerivAt (fun ξ : ℂ => ((ξ, 0) : ℂ × ℂ))
        (ContinuousLinearMap.inl ℝ ℂ ℂ) (0:ℂ) :=
      (hasFDerivAt_id (0:ℂ)).prodMk (hasFDerivAt_const (0:ℂ) (0:ℂ))
    have hcomp := HasFDerivAt.comp (f := fun ξ : ℂ => ((ξ, 0) : ℂ × ℂ)) (0:ℂ) hF0 hsl
    have hD : HasFDerivAt ((fun p : ℂ × ℂ => baryFn φ p.1 p.2) ∘ fun ξ : ℂ => ((ξ, 0) : ℂ × ℂ))
        ((meanCLM (u * iotaBarX)) • (ContinuousLinearMap.id ℝ ℂ)
          + (meanCLM (u * iotaX)) • ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)) 0 :=
      ZDeriv.hasFDerivAt_baryFnMap_z_zero u
    have heq := hcomp.unique hD
    intro v
    have hval := congrArg (fun T : ℂ →L[ℝ] ℂ => T v) heq
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.inl_apply, add_apply,
      smul_apply, ContinuousLinearMap.coe_id', id_eq,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, smul_eq_mul] at hval
    rw [hval, hA1, hB1, Complex.star_def]
  -- the `w`-partial of `M`: formula (2.1) with the coefficients of Lemma 4.1
  have hMw0 : ∀ v : ℂ, M (0, v) = -v + momQ (toCM φ hφc) * star v := by
    intro v
    have h := hMw v
    rw [h0, hQ1] at h
    rw [h]
    simp
  -- implicit differentiation of `F(z, Φ(z)) = 0`
  have hc1 : momA (toCM φ hφc) = (M (1, 0) - Complex.I * M (Complex.I, 0)) / 2 := by
    rw [hMz, hMz]
    simp only [star_one, mul_one, show star Complex.I = -Complex.I from by simp]
    linear_combination ((momA (toCM φ hφc) - momB (toCM φ hφc)) / 2) * Complex.I_mul_I
  have hcm1 : momB (toCM φ hφc) = (M (1, 0) + Complex.I * M (Complex.I, 0)) / 2 := by
    rw [hMz, hMz]
    simp only [star_one, mul_one, show star Complex.I = -Complex.I from by simp]
    linear_combination (-(momA (toCM φ hφc) - momB (toCM φ hφc)) / 2) * Complex.I_mul_I
  have hP : (-1 : ℂ) = (M (0, 1) - Complex.I * M (0, Complex.I)) / 2 := by
    rw [hMw0, hMw0]
    simp only [star_one, mul_one, show star Complex.I = -Complex.I from by simp]
    linear_combination (-(1 + momQ (toCM φ hφc)) / 2) * Complex.I_mul_I
  have hQ : momQ (toCM φ hφc) = (M (0, 1) + Complex.I * M (0, Complex.I)) / 2 := by
    rw [hMw0, hMw0]
    simp only [star_one, mul_one, show star Complex.I = -Complex.I from by simp]
    linear_combination ((1 + momQ (toCM φ hφc)) / 2) * Complex.I_mul_I
  obtain ⟨e1, e2⟩ := wirt_implicit_of_graph_eq_zero
    (baryFn_hasFDerivAt_graph φ hφ hφc hz0 hΦ hF) hc1 hcm1 hP hQ rfl rfl
  unfold HasImplicitDerivAtZero wirtZ wirtZbar
  rw [hΦ.fderiv]
  exact ⟨by linear_combination -e1, by linear_combination -e2⟩

/-- **Lemma 6**, with the implicit differentiation at the origin supplied by
`hasImplicitDerivAtZero`: for `φ₀` an orientation preserving homeomorphism of
`S¹` (in the form `|c₋₁(φ₀)| < |c₁(φ₀)|`, Lemma 3), the dilatation ratio
`φ ↦ μ(E(φ))(0)` extends to a holomorphic function of `φ` on a neighborhood in
`C(S¹, ℂ)`, bounded by `1` in modulus. -/
theorem lemma6_holomorphic_extension' (φ₀ : Circle → Circle) (hφ₀ : Function.Bijective φ₀)
    (hφ₀c : Continuous φ₀)
    (hlem3 : ‖momB (toCM φ₀ hφ₀c)‖ < ‖momA (toCM φ₀ hφ₀c)‖) :
    ∃ (V : Set C(Circle, ℂ)) (f : C(Circle, ℂ) → ℂ),
      IsOpen V ∧ toCM φ₀ hφ₀c ∈ V ∧ AnalyticOn ℂ f V ∧ (∀ ψ ∈ V, ‖f ψ‖ < 1) ∧
      ∀ (φ : Circle → Circle), Function.Bijective φ → ∀ hφc : Continuous φ,
        ‖momB (toCM φ hφc)‖ < ‖momA (toCM φ hφc)‖ → extension φ 0 = 0 →
        toCM φ hφc ∈ V → f (toCM φ hφc) = complexDilatation (extension φ) 0 :=
  lemma6_holomorphic_extension φ₀ hφ₀ hφ₀c hlem3
    fun φ hφ hφc h0 => hasImplicitDerivAtZero φ hφ hφc h0

end
