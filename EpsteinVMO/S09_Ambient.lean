import EpsteinVMO.Defs
import EpsteinVMO.S02_Prelim
import EpsteinVMO.S05_Upper
import EpsteinVMO.S03_Coarse
import EpsteinVMO.S06_Lower
import EpsteinVMO.S07_Transfer

/-!
# §9 The ambient comparison (Theorem E)

Source: `sec09-ambient.tex` of the paper.  The lower bound of Theorem E uses
`prop:mass-volume` (`sec06-lower.tex:103`), which is stated in `S06_Lower`.

## Conventions (see `EpsteinVMO.Defs`)

* Curves through `∞` are pairs `(Ω, Ωs)` (`IsKQuasiPair`, `IsJordanPair`).  A bounded curve is a
  pair `(Ω, Ωs)` with `Ω` the bounded and `Ωs` the unbounded component (as subsets of `ℂ`); its
  ambient quantities are **defined by transport** through `invAt x₀`, `x₀ ∈ Γ`
  (`ambVBdd`, `ambHBdd`).  For the *bounded* component itself `H^Ω` can be computed directly
  (`ambHside Ω`), since `Ω ⊂ ℂ` is a genuine hyperbolic simply connected domain.
* `μ_H` is never formed as a `Measure.map`; its integrals are written as the explicit
  pull-back integrals (Convention 2.2, multiplicity kept), e.g. `ambHside`, `boxAvgH`.
* The Riemannian Hessian of `ℍ³` is written in half-space coordinates (`hypHess`, with the
  Christoffel symbols of `ξ⁻²(|dW|² + dξ²)`), and `g` is `hypMetric`.

## Not stated here (they need the objects of §5, owned by `S05_Upper`)

`lem:ambient-adjoint`, `lem:net-ambient`, `lem:cutoff`, `lem:weighted-dirichlet` and
`eq:hessian-composite` are statements about the operator `𝓛`, the good set `G₀`, the
thickness `t`, the source `σ`, the bad net `{Bᵢ}` and the Green operator `𝒢_D` of §5.  They
are internal to the proof of the upper bound and are to be stated once those objects exist.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace EpsteinVMO

open LiZhongQC

/-! ## Section-local definitions -/

/-- `H^{Ω'}(P) = ∫_{Ω'} k_P(Ep_{Ω'}(w)) s_{Ω'}(w)² dâ_{Ω'}(w)`, the contribution of one
complementary component (`sec09-ambient.tex:18`). -/
def ambHside (Ω : Set ℂ) (P : ℂ × ℝ) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal (ambKernel P (epstein Ω w)) ∂curvMass Ω

/-- `(Ω, Ωs)` are the bounded and the unbounded component of a bounded Jordan curve
(Schoenflies form). -/
def IsBoundedJordanPair (Ω Ωs : Set ℂ) : Prop :=
  ∃ F : ℂ ≃ₜ ℂ, F '' unitDisc = Ω ∧ F '' unitDiscExterior = Ωs

/-- `V(P)` for a bounded curve, by transport through `invAt x₀` (`x₀ ∈ Γ`). -/
def ambVBdd (Ω Ωs : Set ℂ) (x₀ : ℂ) (P : ℂ × ℝ) : ℝ≥0∞ :=
  ambV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) (invExt x₀ P)

/-- `H(P)` for a bounded curve, by transport through `invAt x₀` (`x₀ ∈ Γ`). -/
def ambHBdd (Ω Ωs : Set ℂ) (x₀ : ℂ) (P : ℂ × ℝ) : ℝ≥0∞ :=
  ambH (invPairΩ Ω x₀) (invPairΩs Ωs x₀) (invExt x₀ P)

/-- The Euclidean inner product of `ℂ × ℝ ≅ ℝ³`. -/
def eucInner (v w : ℂ × ℝ) : ℝ := v.1.re * w.1.re + v.1.im * w.1.im + v.2 * w.2

/-- The hyperbolic metric `g_Q(v, w) = ⟨v, w⟩ / ξ²` at `Q = (W, ξ)`. -/
def hypMetric (Q v w : ℂ × ℝ) : ℝ := eucInner v w / Q.2 ^ 2

/-- The Riemannian Hessian of `f` for the metric of `ℍ³` in half-space coordinates:
`∇²f(v,w) = D²f(v,w) + ξ⁻¹ (w_ξ df(v) + v_ξ df(w) - ⟨v,w⟩ ∂_ξ f)`. -/
def hypHess (f : ℂ × ℝ → ℝ) (Q v w : ℂ × ℝ) : ℝ :=
  fderiv ℝ (fderiv ℝ f) Q v w +
    (w.2 * fderiv ℝ f Q v + v.2 * fderiv ℝ f Q w - eucInner v w * fderiv ℝ f Q (0, 1)) / Q.2

/-- The Euclidean standard basis of `ℂ × ℝ`. -/
def eucBasis : Fin 3 → ℂ × ℝ := ![(1, 0), (I, 0), (0, 1)]

/-- The Carleson box `Q(x, r) = D(x, r) × (0, r]`. -/
def carlesonBox (x : ℂ) (r : ℝ) : Set (ℂ × ℝ) := ball x r ×ˢ Ioc 0 r

/-- `A_μ(x, r) = r⁻¹ ∫_{Q(x,r)} ξ dμ(W, ξ)`. -/
def boxAvg (μ : Measure (ℂ × ℝ)) (x : ℂ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal r⁻¹ * ∫⁻ q in carlesonBox x r, ENNReal.ofReal q.2 ∂μ

/-- `K_μ(x, r) = ∫_{ℍ³} k_{(x,r)} dμ`. -/
def boxKernel (μ : Measure (ℂ × ℝ)) (x : ℂ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ q in UHS, ENNReal.ofReal (ambKernel (x, r) q) ∂μ

/-- `A_{μ_H}(x, r)`, written as the pull-back integral of `μ_H = X_*(s² dâ) + X*_*(s*² dâ*)`. -/
def boxAvgH (Ω Ωs : Set ℂ) (x : ℂ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal r⁻¹ *
    ((∫⁻ w, (carlesonBox x r).indicator (fun q => ENNReal.ofReal q.2) (epstein Ω w)
        ∂curvMass Ω) +
      ∫⁻ z, (carlesonBox x r).indicator (fun q => ENNReal.ofReal q.2) (epstein Ωs z)
        ∂curvMass Ωs)

/-- A bounded Jordan curve: a continuous injective image of the circle. -/
def IsJordanCurveC (Γ : Set ℂ) : Prop :=
  ∃ g : Circle → ℂ, Continuous g ∧ Function.Injective g ∧ range g = Γ

/-- `γ` is an arc of `Γ` from `x` to `y`. -/
def IsArcOf (Γ : Set ℂ) (x y : ℂ) (γ : Set ℂ) : Prop :=
  γ ⊆ Γ ∧ ∃ g : ℝ → ℂ, ContinuousOn g (Icc 0 1) ∧ InjOn g (Icc 0 1) ∧ g 0 = x ∧ g 1 = y ∧
    g '' Icc 0 1 = γ

/-- `Γ` is Ahlfors regular with constant `A`: `Λ¹(Γ ∩ D(z, r)) ≤ A r`. -/
def IsAhlforsRegular (Γ : Set ℂ) (A : ℝ) : Prop :=
  ∀ z : ℂ, ∀ r : ℝ, 0 < r → μH[1] (Γ ∩ ball z r) ≤ ENNReal.ofReal (A * r)

/-- `Γ` is chord-arc with constant `C`: rectifiable, and the shorter arc between `x` and `y`
has length `≤ C |x - y|` (lengths of arcs are `Λ¹`). -/
def IsChordArc (Γ : Set ℂ) (C : ℝ) : Prop :=
  μH[1] Γ < ⊤ ∧ ∀ x ∈ Γ, ∀ y ∈ Γ, x ≠ y →
    ∃ γ, IsArcOf Γ x y γ ∧ μH[1] γ ≤ ENNReal.ofReal (C * dist x y)

/-- `Γ` has bounded turning with constant `C`: one of the arcs between `x` and `y` has
diameter `≤ C |x - y|`. -/
def HasBoundedTurning (Γ : Set ℂ) (C : ℝ) : Prop :=
  ∀ x ∈ Γ, ∀ y ∈ Γ, x ≠ y → ∃ γ, IsArcOf Γ x y γ ∧ Metric.diam γ ≤ C * dist x y

/-- `μ_Ω = d(w) s(w)² dâ(w)` on the bounded component, `d(w) = dist(w, Γ)`. -/
def muOmega (Ω Ωs : Set ℂ) : Measure ℂ :=
  (curvMass Ω).withDensity fun w => ENNReal.ofReal (infDist w (curveOf Ω Ωs))

/-- `‖μ‖_* = sup {μ(Ω ∩ D(z, r))/r : z ∈ Γ, 0 < r < diam Γ}`. -/
def starNorm (μ : Measure ℂ) (Ω Γ : Set ℂ) : ℝ≥0∞ :=
  ⨆ z ∈ Γ, ⨆ (r : ℝ) (_ : r ∈ Ioo 0 (Metric.diam Γ)), μ (Ω ∩ ball z r) / ENNReal.ofReal r

/-- `m(w) = (1 - |z|²) |f'(z)|` for `w = f(z)`. -/
def confRad (f : ℂ → ℂ) (w : ℂ) : ℝ :=
  (1 - ‖Function.invFunOn f unitDisc w‖ ^ 2) * ‖deriv f (Function.invFunOn f unitDisc w)‖

/-! ## Theorem E -/

/-- `H = H^Ω + H^{Ω*}` (`sec09-ambient.tex:16`). -/
theorem ambH_eq_ambHside_add (Ω Ωs : Set ℂ) (P : ℂ × ℝ) :
    ambH Ω Ωs P = ambHside Ω P + ambHside Ωs P := rfl

/-- Change of variables for `curvMass` under a measurable embedding `M` with complex derivative
`M'` on `Ω'`, given the transformation law of `s² λ²`. -/

theorem s09_curvMass_map (Ω' : Set ℂ) (hΩ'm : MeasurableSet Ω') (M M' : ℂ → ℂ)
    (hM : MeasurableEmbedding M) (hd : ∀ w ∈ Ω', HasDerivAt M (M' w) w)
    (hρ : ∀ w ∈ Ω', schwarzNorm (M '' Ω') (M w) ^ 2 * poincareDensity (M '' Ω') (M w) ^ 2 *
      ‖M' w‖ ^ 2 = schwarzNorm Ω' w ^ 2 * poincareDensity Ω' w ^ 2) :
    curvMass (M '' Ω') = Measure.map M (curvMass Ω') := by
  ext S hS
  have hpre : MeasurableSet (M ⁻¹' S ∩ Ω') := (hM.measurable hS).inter hΩ'm
  rw [Measure.map_apply hM.measurable hS]
  unfold curvMass
  rw [withDensity_apply _ hS, withDensity_apply _ (hM.measurable hS),
    Measure.restrict_restrict hS, Measure.restrict_restrict (hM.measurable hS)]
  have hset : S ∩ M '' Ω' = M '' (M ⁻¹' S ∩ Ω') := by
    rw [inter_comm (M ⁻¹' S), image_inter_preimage, inter_comm]
  rw [hset, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hpre
    (fun w hw => ((hd w hw.2).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    hM.injective.injOn]
  refine setLIntegral_congr_fun hpre (fun w hw => ?_)
  rw [s09_det_cmul, abs_of_nonneg (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  rw [← hρ w hw.2]
  ring

/-- Transport of `H^Ω` under a measurable embedding with the change-of-variables data. -/
theorem s09_ambHside_map (Ω' : Set ℂ) (hΩ'm : MeasurableSet Ω') (M M' : ℂ → ℂ)
    (hM : MeasurableEmbedding M) (hd : ∀ w ∈ Ω', HasDerivAt M (M' w) w)
    (hρ : ∀ w ∈ Ω', schwarzNorm (M '' Ω') (M w) ^ 2 * poincareDensity (M '' Ω') (M w) ^ 2 *
      ‖M' w‖ ^ 2 = schwarzNorm Ω' w ^ 2 * poincareDensity Ω' w ^ 2) (P P' : ℂ × ℝ)
    (hk : ∀ w ∈ Ω', ambKernel P' (epstein (M '' Ω') (M w)) = ambKernel P (epstein Ω' w)) :
    ambHside (M '' Ω') P' = ambHside Ω' P := by
  unfold ambHside
  rw [s09_curvMass_map Ω' hΩ'm M M' hM hd hρ, hM.lintegral_map]
  have hae : ∀ᵐ w ∂curvMass Ω', w ∈ Ω' := by
    unfold curvMass
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩ'm)
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with w hw
  rw [hk w hw]

theorem s09_epstein_pos (Ω : Set ℂ) (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) (w : ℂ)
    (hw : w ∈ Ω) : 0 < (epstein Ω w).2 := by
  have h := s02_poincareDensity_pos hΩ hw
  unfold epstein
  dsimp only
  positivity

theorem s09_ambKernel_invExt (x₀ : ℂ) (P Q : ℂ × ℝ) (hP : 0 < P.2) (hQ : 0 < Q.2) :
    ambKernel (invExt x₀ P) (invExt x₀ Q) = ambKernel P Q := by
  unfold ambKernel hdist
  rw [s02_coshDist_invExt x₀ hP hQ]

theorem s09_ambKernel_aff (a b : ℂ) (ha : a ≠ 0) (P Q : ℂ × ℝ) (hP : 0 < P.2) (hQ : 0 < Q.2) :
    ambKernel (a * P.1 + b, ‖a‖ * P.2) (a * Q.1 + b, ‖a‖ * Q.2) = ambKernel P Q := by
  have hc : coshDist (a * P.1 + b, ‖a‖ * P.2) (a * Q.1 + b, ‖a‖ * Q.2) = coshDist P Q := by
    unfold coshDist
    dsimp only
    have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
    rw [show a * P.1 + b - (a * Q.1 + b) = a * (P.1 - Q.1) by ring, norm_mul]
    field_simp
  unfold ambKernel hdist
  rw [hc]

/-- (9.1) `eq:ambient-natural`, inversion part (`sec09-ambient.tex:28`): for a Möbius map
`M = invAt x₀` whose pole is off the component, `H^{M(Ω')}(MP) = H^{Ω'}(P)`. -/
theorem eq_ambient_natural_side_inv (Ω' : Set ℂ) (hΩ' : ∃ f, IsConformalOnto f unitDisc Ω')
    (x₀ : ℂ) (hx₀ : x₀ ∉ Ω') (P : ℂ × ℝ) (hP : P ∈ UHS) :
    ambHside (invAt x₀ '' Ω') (invExt x₀ P) = ambHside Ω' P := by
  have hΩ'm : MeasurableSet Ω' := by
    obtain ⟨f, hf⟩ := hΩ'
    exact (hf.isOpen Metric.isOpen_ball).measurableSet
  have hne : ∀ w ∈ Ω', w ≠ x₀ := fun w hw h => hx₀ (h ▸ hw)
  let e : ℂ ≃ᵐ ℂ :=
    { toFun := invAt x₀
      invFun := fun v => v⁻¹ + x₀
      left_inv := fun z => by simp [invAt]
      right_inv := fun v => by simp [invAt]
      measurable_toFun := by
        show Measurable fun z : ℂ => (z - x₀)⁻¹
        fun_prop
      measurable_invFun := by
        show Measurable fun v : ℂ => v⁻¹ + x₀
        fun_prop }
  refine s09_ambHside_map Ω' hΩ'm (invAt x₀) (fun w => -((w - x₀) ^ 2)⁻¹) e.measurableEmbedding
    (fun w hw => by
      have h1 : HasDerivAt (fun y : ℂ => y - x₀) 1 w := (hasDerivAt_id w).sub_const x₀
      have h2 := (hasDerivAt_inv (sub_ne_zero.mpr (hne w hw))).comp w h1
      rw [mul_one] at h2
      exact h2) (fun w hw => ?_) P (invExt x₀ P)
    (fun w hw => ?_)
  · obtain ⟨hl, hs⟩ := subsec_poincare_natural_inv hΩ' hx₀ hw
    rw [hs, ← hl, norm_neg, norm_inv, norm_pow]
    ring
  · rw [subsec_epstein_natural_inv hΩ' hx₀ hw]
    exact s09_ambKernel_invExt x₀ P _ hP (s09_epstein_pos Ω' hΩ' w hw)

/-- (9.1) `eq:ambient-natural`, affine part (`sec09-ambient.tex:28`): the Poincaré extension
of `z ↦ a z + b` is `(W, ξ) ↦ (a W + b, |a| ξ)`. -/
theorem eq_ambient_natural_side_aff (Ω' : Set ℂ) (hΩ' : ∃ f, IsConformalOnto f unitDisc Ω')
    (a b : ℂ) (ha : a ≠ 0) (P : ℂ × ℝ) (hP : P ∈ UHS) :
    ambHside ((fun z => a * z + b) '' Ω') (a * P.1 + b, ‖a‖ * P.2) = ambHside Ω' P := by
  have hΩ'm : MeasurableSet Ω' := by
    obtain ⟨f, hf⟩ := hΩ'
    exact (hf.isOpen Metric.isOpen_ball).measurableSet
  let e : ℂ ≃ᵐ ℂ :=
    { toFun := fun z => a * z + b
      invFun := fun v => (v - b) / a
      left_inv := fun z => by
        simp only
        field_simp
        ring
      right_inv := fun v => by
        simp only
        field_simp
        ring
      measurable_toFun := by
        show Measurable fun z : ℂ => a * z + b
        fun_prop
      measurable_invFun := by
        show Measurable fun v : ℂ => (v - b) / a
        fun_prop }
  refine s09_ambHside_map Ω' hΩ'm (fun z => a * z + b) (fun _ => a) e.measurableEmbedding
    (fun w _ => ((hasDerivAt_id w).const_mul a).add_const b |>.congr_deriv (mul_one a))
    (fun w hw => ?_) P (a * P.1 + b, ‖a‖ * P.2) (fun w hw => ?_)
  · obtain ⟨hl, hs⟩ := subsec_poincare_natural_affine hΩ' (b := b) ha hw
    rw [hs, ← hl]
    ring
  · rw [subsec_epstein_natural_affine hΩ' ha hw]
    exact s09_ambKernel_aff a b ha P _ hP (s09_epstein_pos Ω' hΩ' w hw)

/-- A Jordan pair through `∞` gives a conformal map of `𝔻` onto each component. -/
theorem s09_jordan_conformal (Ω Ωs : Set ℂ) (hΓ : IsJordanPair Ω Ωs) :
    (∃ f, IsConformalOnto f unitDisc Ω) ∧ ∃ f, IsConformalOnto f unitDisc Ωs := by
  have key : ∀ U V : Set ℂ, IsJordanPair U V → ∃ f, IsConformalOnto f unitDisc U := by
    intro U V h
    obtain ⟨φ, hφ⟩ := s05_jordan_riemann h
    exact ⟨_, hφ.symm (s05_jordan_isOpen h)⟩
  refine ⟨key Ω Ωs hΓ, key Ωs Ω ?_⟩
  obtain ⟨F, h1, h2⟩ := hΓ
  have hc : ∀ S T : Set ℂ, (∀ z, z ∈ S ↔ conj z ∈ T) →
      (Complex.conjCLE.toHomeomorph.trans F) '' S = F '' T := by
    intro S T hST
    rw [show ((Complex.conjCLE.toHomeomorph.trans F) : ℂ → ℂ) = F ∘ (fun z => conj z) from rfl,
      image_comp]
    congr 1
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hST y).mp hy
    · intro hz
      refine ⟨conj z, (hST _).mpr (by simpa using hz), by simp⟩
  refine ⟨Complex.conjCLE.toHomeomorph.trans F, ?_, ?_⟩
  · rw [hc upperHalf lowerHalf (fun z => by simp [upperHalf, lowerHalf]), h2]
  · rw [hc lowerHalf upperHalf (fun z => by simp [upperHalf, lowerHalf]), h1]

theorem s09_invExt_zero_invol (v : ℂ × ℝ) : invExt 0 (invExt 0 v) = v := by
  obtain ⟨c, t⟩ := v
  unfold invExt
  simp only [sub_zero]
  set N : ℝ := ‖c‖ ^ 2 + t ^ 2 with hN
  rcases eq_or_ne N 0 with h0 | h0
  · have hc : ‖c‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖c‖, sq_nonneg t]
    have ht : t ^ 2 = 0 := by nlinarith [sq_nonneg ‖c‖, sq_nonneg t]
    have hc0 : c = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hc)
    have ht0 : t = 0 := pow_eq_zero_iff two_ne_zero |>.mp ht
    subst hc0 ht0
    simp
  · have hNp : 0 < N := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast h0
    have hn1 : ‖conj c / (N : ℂ)‖ = ‖c‖ / N := by
      rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hNp.le]
    have hN' : ‖conj c / (N : ℂ)‖ ^ 2 + (t / N) ^ 2 = N⁻¹ := by
      rw [hn1, div_pow, div_pow, ← add_div, ← hN]
      field_simp
    simp only [hN']
    ext
    · simp only
      rw [map_div₀, Complex.conj_conj, Complex.conj_ofReal]
      push_cast
      field_simp
    · simp only
      field_simp

theorem s09_invExt_eq (x₀ : ℂ) (q : ℂ × ℝ) : invExt x₀ q = invExt 0 (q.1 - x₀, q.2) := by
  unfold invExt
  simp

theorem s09_invExt_meas (x₀ : ℂ) : MeasurableEmbedding (invExt x₀) := by
  have hm0 : Measurable (invExt 0) := by
    unfold invExt
    fun_prop
  let e : (ℂ × ℝ) ≃ᵐ (ℂ × ℝ) :=
    { toFun := invExt x₀
      invFun := fun v => ((invExt 0 v).1 + x₀, (invExt 0 v).2)
      left_inv := fun q => by
        show ((invExt 0 (invExt x₀ q)).1 + x₀, (invExt 0 (invExt x₀ q)).2) = q
        rw [s09_invExt_eq x₀ q, s09_invExt_zero_invol]
        simp
      right_inv := fun v => by
        simp only
        rw [s09_invExt_eq]
        simp only [add_sub_cancel_right]
        exact s09_invExt_zero_invol v
      measurable_toFun := by
        show Measurable (invExt x₀)
        unfold invExt
        fun_prop
      measurable_invFun := by
        show Measurable fun v => ((invExt 0 v).1 + x₀, (invExt 0 v).2)
        fun_prop }
  exact e.measurableEmbedding

theorem s09_invExt_surj (x₀ : ℂ) : Function.Surjective (invExt x₀) := by
  intro v
  refine ⟨((invExt 0 v).1 + x₀, (invExt 0 v).2), ?_⟩
  rw [s09_invExt_eq]
  simp only [add_sub_cancel_right]
  exact s09_invExt_zero_invol v

theorem s09_invExt_UHS (x₀ : ℂ) : invExt x₀ ⁻¹' UHS = UHS := by
  ext q
  show 0 < q.2 / (‖q.1 - x₀‖ ^ 2 + q.2 ^ 2) ↔ 0 < q.2
  constructor
  · intro h
    by_contra hq
    push Not at hq
    have : q.2 / (‖q.1 - x₀‖ ^ 2 + q.2 ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hq (by positivity)
    linarith
  · intro h
    positivity

/-- The Jacobian core: `det (n⁻¹ id + (-(n²)⁻¹ DN) ⊗ y) = -n⁻³` when `DN y = 2 n`. -/
theorem s09_det_inv_core (y : ℂ × ℝ) (n : ℝ) (hn : n ≠ 0) (DN : (ℂ × ℝ) →L[ℝ] ℝ)
    (hDN : DN y = 2 * n) :
    (n⁻¹ • ContinuousLinearMap.id ℝ (ℂ × ℝ) + (-(n ^ 2)⁻¹ • DN).smulRight y).det =
      -(n⁻¹) ^ 3 := by
  have hfr : Module.finrank ℝ (ℂ × ℝ) = 3 := by
    rw [Module.finrank_prod, Complex.finrank_real_complex, Module.finrank_self]
  have hL : ((n⁻¹ • ContinuousLinearMap.id ℝ (ℂ × ℝ) + (-(n ^ 2)⁻¹ • DN).smulRight y :
      (ℂ × ℝ) →L[ℝ] (ℂ × ℝ)) : (ℂ × ℝ) →ₗ[ℝ] (ℂ × ℝ)) =
      n⁻¹ • LinearMap.transvection (n • (-(n ^ 2)⁻¹ • (DN : (ℂ × ℝ) →ₗ[ℝ] ℝ))) y := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.smul_apply, LinearMap.transvection.apply]
    simp only [ContinuousLinearMap.coe_add, ContinuousLinearMap.coe_smul, LinearMap.add_apply,
      LinearMap.smul_apply, ContinuousLinearMap.coe_id, LinearMap.id_apply,
      ContinuousLinearMap.coe_smulRight, smul_add, smul_smul]
    congr 1
    rw [LinearMap.smulRight_apply]
    congr 1
    simp only [ContinuousLinearMap.smul_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      smul_eq_mul]
    field_simp
  rw [ContinuousLinearMap.det, hL, LinearMap.det_smul, hfr, LinearMap.transvection.det]
  simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, hDN, smul_eq_mul]
  field_simp
  ring

/-- `hvol` is invariant under `invExt x₀`. -/
theorem s09_hvol_map_inv (x₀ : ℂ) : Measure.map (invExt x₀) hvol = hvol := by
  have hT := s09_invExt_meas x₀
  have hU : MeasurableSet UHS := measurableSet_lt measurable_const measurable_snd
  have : (volume : Measure (ℂ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  set N : ℂ × ℝ → ℝ := fun y => ‖y.1‖ ^ 2 + y.2 * y.2 with hNdef
  let RL : (ℂ × ℝ) →L[ℝ] (ℂ × ℝ) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).prodMap (ContinuousLinearMap.id ℝ ℝ)
  have hfac : ∀ q : ℂ × ℝ, invExt x₀ q = RL ((N (q - (x₀, 0)))⁻¹ • (q - (x₀, 0))) := by
    intro q
    ext
    · show conj (q.1 - x₀) / ((‖q.1 - x₀‖ ^ 2 + q.2 ^ 2 : ℝ) : ℂ) =
        conj (((‖q.1 - x₀‖ ^ 2 + (q.2 - 0) * (q.2 - 0))⁻¹ : ℝ) • (q.1 - x₀))
      rw [sub_zero, Complex.real_smul, map_mul, Complex.conj_ofReal, sq q.2]
      push_cast
      ring
    · show q.2 / (‖q.1 - x₀‖ ^ 2 + q.2 ^ 2) = (‖q.1 - x₀‖ ^ 2 + (q.2 - 0) * (q.2 - 0))⁻¹ • (q.2 - 0)
      rw [smul_eq_mul, sub_zero, div_eq_inv_mul, sq q.2]
  have hderiv : ∀ q : ℂ × ℝ, 0 < q.2 → ∃ L : (ℂ × ℝ) →L[ℝ] (ℂ × ℝ),
      HasFDerivAt (invExt x₀) L q ∧
        |L.det| = ((‖q.1 - x₀‖ ^ 2 + q.2 ^ 2) ^ 3)⁻¹ := by
    intro q hq
    set y : ℂ × ℝ := q - (x₀, 0) with hy
    have hny : N y ≠ 0 := by
      have : 0 < N y := by
        simp only [hNdef, hy, Prod.snd_sub, sub_zero]
        positivity
      exact this.ne'
    set DN : (ℂ × ℝ) →L[ℝ] ℝ := 2 • (innerSL ℝ y.1).comp (ContinuousLinearMap.fst ℝ ℂ ℝ) +
      (2 * y.2) • ContinuousLinearMap.snd ℝ ℂ ℝ with hDNdef
    have hN : HasFDerivAt N DN y := by
      have h1 := (hasFDerivAt_fst (𝕜 := ℝ) (p := y)).norm_sq
      have h2 := (hasFDerivAt_snd (𝕜 := ℝ) (p := y)).mul (hasFDerivAt_snd (𝕜 := ℝ) (p := y))
      refine (h1.add h2).congr_fderiv ?_
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [hDNdef, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        smul_eq_mul]
      ring
    have hDN : DN y = 2 * N y := by
      simp only [hDNdef, hNdef, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd', innerSL_apply_apply, real_inner_self_eq_norm_sq,
        smul_eq_mul]
      ring
    have hS : HasFDerivAt (fun z : ℂ × ℝ => (N z)⁻¹ • z)
        ((N y)⁻¹ • ContinuousLinearMap.id ℝ (ℂ × ℝ) + (-(N y ^ 2)⁻¹ • DN).smulRight y) y := by
      have hinv := (hasFDerivAt_inv hny).comp y hN
      refine (hinv.smul (hasFDerivAt_id y)).congr_fderiv ?_
      refine ContinuousLinearMap.ext fun v => ?_
      simp [ContinuousLinearMap.smulRight_apply, mul_comm]
    have hTr : HasFDerivAt (fun z : ℂ × ℝ => z - (x₀, 0)) (ContinuousLinearMap.id ℝ _) q :=
      (hasFDerivAt_id q).sub_const _
    have hfull := RL.hasFDerivAt.comp q (hS.comp q hTr)
    have hfun : invExt x₀ = RL ∘ (fun z : ℂ × ℝ => (N z)⁻¹ • z) ∘ fun z => z - (x₀, 0) := by
      funext z
      exact hfac z
    rw [hfun]
    refine ⟨_, hfull, ?_⟩
    · set X : (ℂ × ℝ) →L[ℝ] (ℂ × ℝ) := (N y)⁻¹ • ContinuousLinearMap.id ℝ (ℂ × ℝ) +
        (-(N y ^ 2)⁻¹ • DN).smulRight y with hX
      have hX' : X.det = -(N y)⁻¹ ^ 3 := s09_det_inv_core y (N y) hny DN hDN
      rw [ContinuousLinearMap.comp_id, ContinuousLinearMap.det,
        show ((RL.comp X : (ℂ × ℝ) →L[ℝ] (ℂ × ℝ)) : (ℂ × ℝ) →ₗ[ℝ] (ℂ × ℝ)) =
          (RL : (ℂ × ℝ) →ₗ[ℝ] (ℂ × ℝ)).comp (X : (ℂ × ℝ) →ₗ[ℝ] (ℂ × ℝ)) from rfl,
        LinearMap.det_comp, (by rw [← ContinuousLinearMap.det]; exact hX' :
          LinearMap.det (X : (ℂ × ℝ) →ₗ[ℝ] (ℂ × ℝ)) = -(N y)⁻¹ ^ 3)]
      have hRL : LinearMap.det (RL : (ℂ × ℝ) →ₗ[ℝ] (ℂ × ℝ)) = -1 := by
        simp only [RL, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap,
          ContinuousLinearMap.coe_id, LinearMap.det_id, mul_one]
        exact Complex.det_conjAe
      rw [hRL]
      have hNy : N y = ‖q.1 - x₀‖ ^ 2 + q.2 ^ 2 := by
        simp only [hNdef, hy, Prod.fst_sub, Prod.snd_sub, sub_zero]
        ring
      rw [hNy]
      have hpos : 0 < ‖q.1 - x₀‖ ^ 2 + q.2 ^ 2 := by positivity
      rw [show -1 * -(‖q.1 - x₀‖ ^ 2 + q.2 ^ 2)⁻¹ ^ 3 =
          ((‖q.1 - x₀‖ ^ 2 + q.2 ^ 2) ^ 3)⁻¹ by rw [inv_pow]; ring,
        abs_of_pos (by positivity)]
  choose! L hL hLdet using hderiv
  ext S hS
  have hpre : MeasurableSet (invExt x₀ ⁻¹' S ∩ UHS) := (hT.measurable hS).inter hU
  rw [Measure.map_apply hT.measurable hS]
  unfold hvol
  rw [withDensity_apply _ hS, withDensity_apply _ (hT.measurable hS),
    Measure.restrict_restrict hS, Measure.restrict_restrict (hT.measurable hS)]
  have hset : S ∩ UHS = invExt x₀ '' (invExt x₀ ⁻¹' S ∩ UHS) := by
    conv_rhs => rw [← s09_invExt_UHS x₀]
    rw [← preimage_inter, image_preimage_eq _ (s09_invExt_surj x₀)]
  rw [hset, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hpre
    (fun q hq => (hL q hq.2).hasFDerivWithinAt) hT.injective.injOn]
  refine (setLIntegral_congr_fun hpre (fun q hq => ?_)).symm
  have hq : 0 < q.2 := hq.2
  rw [hLdet q hq, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  show (((‖q.1 - x₀‖ ^ 2 + q.2 ^ 2) ^ 3)⁻¹ * ((q.2 / (‖q.1 - x₀‖ ^ 2 + q.2 ^ 2)) ^ 3)⁻¹ =
    (q.2 ^ 3)⁻¹)
  have hpos : 0 < ‖q.1 - x₀‖ ^ 2 + q.2 ^ 2 := by positivity
  field_simp

/-- Distance identity for the Poincaré extension of an inversion. -/
theorem s09_invExt_dist (a c : ℂ) (t : ℝ) (hc : c ≠ 0) (ht : 0 < t) :
    ‖conj a / ((‖a‖ ^ 2 + t ^ 2 : ℝ) : ℂ) - c⁻¹‖ ^ 2 + (t / (‖a‖ ^ 2 + t ^ 2)) ^ 2 =
      (‖a - c‖ ^ 2 + t ^ 2) / ((‖a‖ ^ 2 + t ^ 2) * ‖c‖ ^ 2) := by
  have hM : 0 < ‖a‖ ^ 2 + t ^ 2 := by positivity
  have hcn : normSq c ≠ 0 := by
    rw [Ne, Complex.normSq_eq_zero]
    exact hc
  simp only [Complex.sq_norm] at hM ⊢
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply] at *
  simp only [Complex.sub_re, Complex.sub_im, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.conj_re, Complex.conj_im, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
  have hM' : a.re * a.re + a.im * a.im + t ^ 2 ≠ 0 := hM.ne'
  have hM2 : a.re ^ 2 + a.im ^ 2 + t ^ 2 ≠ 0 := by rw [sq, sq]; exact hM'
  have hc2 : c.re ^ 2 + c.im ^ 2 ≠ 0 := by rw [sq, sq]; exact hcn
  simp only [← sq]
  field_simp
  ring

/-- Horoball functions are natural under the Poincaré extension of `invAt x₀`. -/
theorem s09_horoPhi_inv (Ω : Set ℂ) (hΩ : ∃ f, IsConformalOnto f unitDisc Ω) (x₀ : ℂ)
    (hx₀ : x₀ ∉ Ω) (q : ℂ × ℝ) (hq : 0 < q.2) (w : ℂ) (hw : w ∈ Ω) :
    horoPhi (invAt x₀ '' Ω) (invExt x₀ q) (invAt x₀ w) = horoPhi Ω q w := by
  have hl := (subsec_poincare_natural_inv hΩ hx₀ hw).1
  have hc : w - x₀ ≠ 0 := sub_ne_zero.mpr fun h => hx₀ (h ▸ hw)
  have hcn : 0 < ‖w - x₀‖ ^ 2 := by positivity
  have hl' : poincareDensity (invAt x₀ '' Ω) (invAt x₀ w) =
      poincareDensity Ω w * ‖w - x₀‖ ^ 2 := by
    rw [← hl]
    field_simp
  have hM : 0 < ‖q.1 - x₀‖ ^ 2 + q.2 ^ 2 := by positivity
  unfold horoPhi
  rw [hl']
  show poincareDensity Ω w * ‖w - x₀‖ ^ 2 *
      (‖conj (q.1 - x₀) / ((‖q.1 - x₀‖ ^ 2 + q.2 ^ 2 : ℝ) : ℂ) - (w - x₀)⁻¹‖ ^ 2 +
        (q.2 / (‖q.1 - x₀‖ ^ 2 + q.2 ^ 2)) ^ 2) /
      (2 * (q.2 / (‖q.1 - x₀‖ ^ 2 + q.2 ^ 2))) = _
  rw [s09_invExt_dist (q.1 - x₀) (w - x₀) q.2 hc hq,
    show q.1 - x₀ - (w - x₀) = q.1 - w by ring]
  field_simp

/-- Horoball unions are natural under the Poincaré extension of `invAt x₀`. -/
theorem s09_horoUnion_inv (Ω : Set ℂ) (hΩ : ∃ f, IsConformalOnto f unitDisc Ω) (x₀ : ℂ)
    (hx₀ : x₀ ∉ Ω) : invExt x₀ ⁻¹' horoUnion (invAt x₀ '' Ω) = horoUnion Ω := by
  have hUq : ∀ q : ℂ × ℝ, invExt x₀ q ∈ UHS ↔ q ∈ UHS := fun q => by
    rw [← mem_preimage, s09_invExt_UHS]
  ext q
  simp only [mem_preimage, horoUnion, mem_iUnion₂, horoball, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, hq1, hq2⟩
    have hq : q ∈ UHS := (hUq q).mp hq1
    exact ⟨w, hw, hq, by rwa [s09_horoPhi_inv Ω hΩ x₀ hx₀ q hq w hw] at hq2⟩
  · rintro ⟨w, hw, hq, hq2⟩
    refine ⟨invAt x₀ w, ⟨w, hw, rfl⟩, (hUq q).mpr hq, ?_⟩
    rwa [s09_horoPhi_inv Ω hΩ x₀ hx₀ q hq w hw]

/-- (9.1) `eq:ambient-natural`, `V` under an inversion at a point of a curve through `∞`
(`sec09-ambient.tex:28`): `V_{M(Γ)}(MP) = V_Γ(P)`. -/
theorem eq_ambient_natural_V_inv (Ω Ωs : Set ℂ) (hΓ : IsJordanPair Ω Ωs) (x₀ : ℂ)
    (hx₀ : x₀ ∈ curveOf Ω Ωs) (P : ℂ × ℝ) (hP : P ∈ UHS) :
    ambV (invAt x₀ '' Ω) (invAt x₀ '' Ωs) (invExt x₀ P) = ambV Ω Ωs P := by
  obtain ⟨hΩ, hΩs⟩ := s09_jordan_conformal Ω Ωs hΓ
  have hx : x₀ ∉ Ω ∧ x₀ ∉ Ωs := by
    have := hx₀
    simp only [curveOf, mem_compl_iff, mem_union, not_or] at this
    exact this
  have hT := s09_invExt_meas x₀
  have hU : MeasurableSet UHS := measurableSet_lt measurable_const measurable_snd
  have hgap : invExt x₀ ⁻¹' gap (invAt x₀ '' Ω) (invAt x₀ '' Ωs) = gap Ω Ωs := by
    unfold gap
    rw [preimage_sdiff, preimage_union, s09_invExt_UHS, s09_horoUnion_inv Ω hΩ x₀ hx.1,
      s09_horoUnion_inv Ωs hΩs x₀ hx.2]
  unfold ambV
  calc ∫⁻ q in gap (invAt x₀ '' Ω) (invAt x₀ '' Ωs),
        ENNReal.ofReal (ambKernel (invExt x₀ P) q) ∂hvol
      = ∫⁻ q in gap (invAt x₀ '' Ω) (invAt x₀ '' Ωs),
          ENNReal.ofReal (ambKernel (invExt x₀ P) q) ∂(Measure.map (invExt x₀) hvol) := by
        rw [s09_hvol_map_inv x₀]
    _ = ∫⁻ q in gap Ω Ωs, ENNReal.ofReal (ambKernel (invExt x₀ P) (invExt x₀ q)) ∂hvol := by
        rw [hT.restrict_map, hT.lintegral_map, hgap]
    _ = ∫⁻ q in gap Ω Ωs, ENNReal.ofReal (ambKernel P q) ∂hvol := by
        refine lintegral_congr_ae ?_
        have hae : ∀ᵐ q ∂hvol.restrict (gap Ω Ωs), q ∈ UHS :=
          ae_mono (Measure.restrict_mono sdiff_subset le_rfl) (ae_restrict_mem hU)
        filter_upwards [hae] with q hq
        rw [s09_ambKernel_invExt x₀ P q hP hq]

/-- (9.1) `eq:ambient-natural`, `V` under an affine map (`sec09-ambient.tex:28`). -/
theorem eq_ambient_natural_V_aff (Ω Ωs : Set ℂ) (hΓ : IsJordanPair Ω Ωs) (a b : ℂ)
    (ha : a ≠ 0) (P : ℂ × ℝ) (hP : P ∈ UHS) :
    ambV ((fun z => a * z + b) '' Ω) ((fun z => a * z + b) '' Ωs) (a * P.1 + b, ‖a‖ * P.2) =
      ambV Ω Ωs P := by
  obtain ⟨hΩ, hΩs⟩ := s09_jordan_conformal Ω Ωs hΓ
  set T : ℂ × ℝ → ℂ × ℝ := fun q => (a * q.1 + b, ‖a‖ * q.2) with hTdef
  have hT := s09_affExt_meas a b ha
  have hU : MeasurableSet UHS := measurableSet_lt measurable_const measurable_snd
  have hgap : T ⁻¹' gap ((fun z => a * z + b) '' Ω) ((fun z => a * z + b) '' Ωs) =
      gap Ω Ωs := by
    unfold gap
    rw [preimage_sdiff, preimage_union, s09_affExt_UHS a b ha, s09_horoUnion_aff Ω hΩ a b ha,
      s09_horoUnion_aff Ωs hΩs a b ha]
  unfold ambV
  calc ∫⁻ q in gap ((fun z => a * z + b) '' Ω) ((fun z => a * z + b) '' Ωs),
        ENNReal.ofReal (ambKernel (a * P.1 + b, ‖a‖ * P.2) q) ∂hvol
      = ∫⁻ q in gap ((fun z => a * z + b) '' Ω) ((fun z => a * z + b) '' Ωs),
          ENNReal.ofReal (ambKernel (a * P.1 + b, ‖a‖ * P.2) q) ∂(Measure.map T hvol) := by
        rw [hTdef, s09_hvol_map_aff a b ha]
    _ = ∫⁻ q in gap Ω Ωs, ENNReal.ofReal (ambKernel (a * P.1 + b, ‖a‖ * P.2) (T q)) ∂hvol := by
        rw [hT.restrict_map, hT.lintegral_map, hgap]
    _ = ∫⁻ q in gap Ω Ωs, ENNReal.ofReal (ambKernel P q) ∂hvol := by
        refine lintegral_congr_ae ?_
        have hae : ∀ᵐ q ∂hvol.restrict (gap Ω Ωs), q ∈ UHS :=
          ae_mono (Measure.restrict_mono sdiff_subset le_rfl) (ae_restrict_mem hU)
        filter_upwards [hae] with q hq
        rw [hTdef]
        dsimp only
        rw [s09_ambKernel_aff a b ha P q hP hq]

theorem s09_norm_sub_I_sq (z : ℂ) : ‖z - I‖ ^ 2 = ‖z‖ ^ 2 - 2 * z.im + 1 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
  ring

theorem s09_norm_add_I_sq (z : ℂ) : ‖z + I‖ ^ 2 = ‖z‖ ^ 2 + 2 * z.im + 1 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
  ring

/-- `|z - i| < |z + i|` exactly on the upper half-plane. -/
theorem s09_norm_sub_I_lt (z : ℂ) : ‖z - I‖ < ‖z + I‖ ↔ 0 < z.im := by
  rw [← pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero,
    s09_norm_sub_I_sq, s09_norm_add_I_sq]
  constructor <;> intro h <;> linarith

/-- `|z + i| < |z - i|` exactly on the lower half-plane. -/
theorem s09_norm_add_I_lt (z : ℂ) : ‖z + I‖ < ‖z - I‖ ↔ z.im < 0 := by
  rw [← pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero,
    s09_norm_sub_I_sq, s09_norm_add_I_sq]
  constructor <;> intro h <;> linarith

/-- A bounded Jordan pair transported by `invAt x₀` (`x₀` on the curve) is a Jordan pair
through `∞`. -/
theorem s09_bdd_pair (Ω Ωs : Set ℂ) (hΓ : IsBoundedJordanPair Ω Ωs) (x₀ : ℂ)
    (hx₀ : x₀ ∈ curveOf Ω Ωs) : IsJordanPair (invPairΩ Ω x₀) (invPairΩs Ωs x₀) := by
  obtain ⟨F, hF1, hF2⟩ := hΓ
  have hx : x₀ ∉ Ω ∧ x₀ ∉ Ωs := by
    have := hx₀
    simp only [curveOf, mem_compl_iff, mem_union, not_or] at this
    exact this
  set ζ := F.symm x₀ with hζdef
  have hFζ : F ζ = x₀ := F.apply_symm_apply x₀
  have hζ1 : ‖ζ‖ = 1 := by
    apply le_antisymm
    · by_contra h
      exact hx.2 (by rw [← hF2]; exact ⟨ζ, lt_of_not_ge h, hFζ⟩)
    · by_contra h
      exact hx.1 (by rw [← hF1]; exact ⟨ζ, mem_ball_zero_iff.mpr (lt_of_not_ge h), hFζ⟩)
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hζ1
    exact zero_ne_one hζ1
  have hc0 : (2 * I * ζ : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hζ0
  let C : ℂ → ℂ := fun z => ζ - ((2 * I * ζ)⁻¹ * (z + I))⁻¹
  let Ci : ℂ → ℂ := fun v => -I - 2 * I * ζ * (v - ζ)⁻¹
  have hzI : ∀ z : ℂ, z ≠ -I → z + I ≠ 0 := fun z hz h => hz (eq_neg_of_add_eq_zero_left h)
  have hCne : ∀ z, z ≠ -I → C z ≠ ζ := by
    intro z hz h
    have h' : ((2 * I * ζ)⁻¹ * (z + I))⁻¹ = 0 := by
      have : ζ - ((2 * I * ζ)⁻¹ * (z + I))⁻¹ = ζ := h
      linear_combination -this
    rw [inv_eq_zero, mul_eq_zero, inv_eq_zero] at h'
    rcases h' with h' | h'
    · exact hc0 h'
    · exact hzI z hz h'
  have hCiC : ∀ z, z ≠ -I → Ci (C z) = z := by
    intro z hz
    have h1 := hzI z hz
    simp only [C, Ci]
    rw [show ζ - ((2 * I * ζ)⁻¹ * (z + I))⁻¹ - ζ = -((2 * I * ζ)⁻¹ * (z + I))⁻¹ by ring,
      inv_neg, inv_inv]
    field_simp
    ring
  have hCi_ne : ∀ v, v ≠ ζ → Ci v ≠ -I := by
    intro v hv h
    have hv' : v - ζ ≠ 0 := sub_ne_zero.mpr hv
    have : 2 * I * ζ * (v - ζ)⁻¹ = 0 := by
      have : -I - 2 * I * ζ * (v - ζ)⁻¹ = -I := h
      linear_combination -this
    rw [mul_eq_zero, inv_eq_zero] at this
    rcases this with h' | h'
    · exact hc0 h'
    · exact hv' h'
  have hCCi : ∀ v, v ≠ ζ → C (Ci v) = v := by
    intro v hv
    have hv' : v - ζ ≠ 0 := sub_ne_zero.mpr hv
    simp only [C, Ci]
    rw [show -I - 2 * I * ζ * (v - ζ)⁻¹ + I = -(2 * I * ζ * (v - ζ)⁻¹) by ring]
    field_simp
    ring
  have hCnorm : ∀ z, z ≠ -I → ‖C z‖ = ‖z - I‖ / ‖z + I‖ := by
    intro z hz
    have h1 := hzI z hz
    have : C z = ζ * ((z - I) / (z + I)) := by
      simp only [C]
      rw [mul_inv, inv_inv]
      field_simp
      ring
    rw [this, norm_mul, hζ1, one_mul, norm_div]
  have hFC : ∀ z, z ≠ -I → F (C z) ≠ x₀ := by
    intro z hz h
    rw [← hFζ] at h
    exact hCne z hz (F.injective h)
  let G : ℂ → ℂ := fun z => if z = -I then 0 else invAt x₀ (F (C z))
  let Gi : ℂ → ℂ := fun u => if u = 0 then -I else Ci (F.symm (x₀ + u⁻¹))
  have hGi_ne : ∀ u : ℂ, u ≠ 0 → F.symm (x₀ + u⁻¹) ≠ ζ := by
    intro u hu h
    have : x₀ + u⁻¹ = x₀ := by
      have h2 := congrArg F h
      rwa [F.apply_symm_apply, hFζ] at h2
    exact inv_ne_zero hu (by linear_combination this)
  have hleft : ∀ z, Gi (G z) = z := by
    intro z
    by_cases hz : z = -I
    · simp [G, Gi, hz]
    · have hne : invAt x₀ (F (C z)) ≠ 0 := inv_ne_zero (sub_ne_zero.mpr (hFC z hz))
      simp only [G, Gi, if_neg hz, if_neg hne]
      unfold invAt
      rw [inv_inv, add_sub_cancel, F.symm_apply_apply, hCiC z hz]
  have hright : ∀ u, G (Gi u) = u := by
    intro u
    by_cases hu : u = 0
    · simp [G, Gi, hu]
    · have hv := hGi_ne u hu
      simp only [Gi, if_neg hu, G, if_neg (hCi_ne _ hv), hCCi _ hv]
      unfold invAt
      rw [F.apply_symm_apply, add_sub_cancel_left, inv_inv]
  have hcob : Bornology.cobounded ℂ = cocompact ℂ := Metric.cobounded_eq_cocompact
  have hGc : Continuous G := by
    refine continuous_iff_continuousAt.mpr fun z => ?_
    by_cases hz : z = -I
    · subst hz
      rw [← continuousWithinAt_compl_self]
      have h1 : Tendsto (fun z : ℂ => (2 * I * ζ)⁻¹ * (z + I)) (𝓝[≠] (-I)) (𝓝[≠] 0) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have : Continuous fun z : ℂ => (2 * I * ζ)⁻¹ * (z + I) := by fun_prop
          have h := this.tendsto (-I)
          simp only [neg_add_cancel, mul_zero] at h
          exact h.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with z hz
          exact mul_ne_zero (inv_ne_zero hc0) (hzI z hz)
      have h2 : Tendsto C (𝓝[≠] (-I)) (cocompact ℂ) := by
        rw [← hcob]
        exact (tendsto_const_sub_cobounded ζ).comp (tendsto_inv₀_nhdsNE_zero.comp h1)
      have h3 : Tendsto (fun w => invAt x₀ w) (cocompact ℂ) (𝓝 0) := by
        rw [← hcob]
        exact tendsto_inv₀_cobounded.comp (tendsto_sub_const_cobounded x₀)
      have h4 := h3.comp ((show Tendsto F (cocompact ℂ) (cocompact ℂ) from F.map_cocompact.le).comp h2)
      show Tendsto G (𝓝[≠] (-I)) (𝓝 (G (-I)))
      rw [show G (-I) = 0 from if_pos rfl]
      refine h4.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (if_neg hz).symm
    · have hev : (fun z' => invAt x₀ (F (C z'))) =ᶠ[𝓝 z] G := by
        filter_upwards [isOpen_ne.mem_nhds hz] with z' hz'
        exact (if_neg hz').symm
      refine ContinuousAt.congr ?_ hev
      have hCc : ContinuousAt C z := by
        refine continuousAt_const.sub (ContinuousAt.inv₀ ?_ ?_)
        · fun_prop
        · exact mul_ne_zero (inv_ne_zero hc0) (hzI z hz)
      have hinv : ContinuousAt (fun w => invAt x₀ w) (F (C z)) := by
        unfold invAt
        exact (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr (hFC z hz))
      exact ContinuousAt.comp (g := fun w => invAt x₀ w) hinv (ContinuousAt.comp (g := F) (f := C) F.continuous.continuousAt hCc)
  have hGic : Continuous Gi := by
    refine continuous_iff_continuousAt.mpr fun u => ?_
    by_cases hu : u = 0
    · subst hu
      rw [← continuousWithinAt_compl_self]
      have h1 : Tendsto (fun u : ℂ => F.symm (x₀ + u⁻¹)) (𝓝[≠] 0) (cocompact ℂ) := by
        refine (show Tendsto F.symm (cocompact ℂ) (cocompact ℂ) from F.symm.map_cocompact.le).comp ?_
        rw [← hcob]
        exact (tendsto_const_add_cobounded x₀).comp tendsto_inv₀_nhdsNE_zero
      have h2 : Tendsto Ci (cocompact ℂ) (𝓝 (-I)) := by
        rw [← hcob]
        have := (tendsto_inv₀_cobounded.comp (tendsto_sub_const_cobounded ζ)).const_mul
          (2 * I * ζ)
        have := (tendsto_const_nhds (x := -I)).sub this
        simpa using this
      show Tendsto Gi (𝓝[≠] 0) (𝓝 (Gi 0))
      rw [show Gi 0 = -I from if_pos rfl]
      refine (h2.comp h1).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (if_neg hu).symm
    · have hev : (fun u' => Ci (F.symm (x₀ + u'⁻¹))) =ᶠ[𝓝 u] Gi := by
        filter_upwards [isOpen_ne.mem_nhds hu] with u' hu'
        exact (if_neg hu').symm
      refine ContinuousAt.congr ?_ hev
      have hin : ContinuousAt (fun u' : ℂ => x₀ + u'⁻¹) u :=
        continuousAt_const.add (continuousAt_inv₀ hu)
      have hCic : ContinuousAt Ci (F.symm (x₀ + u⁻¹)) := by
        refine continuousAt_const.sub (continuousAt_const.mul (ContinuousAt.inv₀ ?_ ?_))
        · fun_prop
        · exact sub_ne_zero.mpr (hGi_ne u hu)
      exact ContinuousAt.comp (g := Ci) hCic (ContinuousAt.comp (g := F.symm) (f := fun u' : ℂ => x₀ + u'⁻¹)
        F.symm.continuous.continuousAt hin)
  let H : ℂ ≃ₜ ℂ :=
    { toFun := G
      invFun := Gi
      left_inv := hleft
      right_inv := hright
      continuous_toFun := hGc
      continuous_invFun := hGic }
  have hInI : -I ∉ upperHalf := by
    show ¬ 0 < (-I).im
    simp
  refine ⟨H, ?_, ?_⟩
  · show G '' upperHalf = invAt x₀ '' Ω
    ext u
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ≠ -I := fun h => hInI (h ▸ hz)
      have hd : C z ∈ unitDisc := by
        refine mem_ball_zero_iff.mpr ?_
        rw [hCnorm z hz', div_lt_one (norm_pos_iff.mpr (hzI z hz'))]
        exact (s09_norm_sub_I_lt z).mpr hz
      refine ⟨F (C z), by rw [← hF1]; exact ⟨C z, hd, rfl⟩, ?_⟩
      exact (if_neg hz').symm
    · rintro ⟨w, hw, rfl⟩
      rw [← hF1] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      have hv1 : ‖v‖ < 1 := mem_ball_zero_iff.mp hv
      have hvζ : v ≠ ζ := fun h => by rw [h, hζ1] at hv1; exact lt_irrefl _ hv1
      have hz' := hCi_ne v hvζ
      refine ⟨Ci v, ?_, ?_⟩
      · show 0 < (Ci v).im
        rw [← s09_norm_sub_I_lt, ← div_lt_one (norm_pos_iff.mpr (hzI _ hz')), ← hCnorm _ hz',
          hCCi v hvζ]
        exact hv1
      · show (if Ci v = -I then 0 else invAt x₀ (F (C (Ci v)))) = invAt x₀ (F v)
        rw [if_neg hz', hCCi v hvζ]
  · show G '' lowerHalf = invAt x₀ '' Ωs ∪ {0}
    ext u
    constructor
    · rintro ⟨z, hz, rfl⟩
      by_cases hz' : z = -I
      · right
        exact if_pos hz'
      · left
        have hd : C z ∈ unitDiscExterior := by
          show 1 < ‖C z‖
          rw [hCnorm z hz', one_lt_div (norm_pos_iff.mpr (hzI z hz'))]
          exact (s09_norm_add_I_lt z).mpr hz
        refine ⟨F (C z), by rw [← hF2]; exact ⟨C z, hd, rfl⟩, ?_⟩
        exact (if_neg hz').symm
    · rintro (⟨w, hw, rfl⟩ | hu)
      · rw [← hF2] at hw
        obtain ⟨v, hv, rfl⟩ := hw
        have hv1 : 1 < ‖v‖ := hv
        have hvζ : v ≠ ζ := fun h => by rw [h, hζ1] at hv1; exact lt_irrefl _ hv1
        have hz' := hCi_ne v hvζ
        refine ⟨Ci v, ?_, ?_⟩
        · show (Ci v).im < 0
          rw [← s09_norm_add_I_lt, ← one_lt_div (norm_pos_iff.mpr (hzI _ hz')), ← hCnorm _ hz',
            hCCi v hvζ]
          exact hv1
        · show (if Ci v = -I then 0 else invAt x₀ (F (C (Ci v)))) = invAt x₀ (F v)
          rw [if_neg hz', hCCi v hvζ]
      · rw [mem_singleton_iff] at hu
        subst hu
        refine ⟨-I, ?_, if_pos rfl⟩
        show (-I).im < 0
        simp

/-- Jordan pairs through `∞` are preserved by affine maps. -/
theorem s09_jordan_affine (Ω Ωs : Set ℂ) (hΓ : IsJordanPair Ω Ωs) (a b : ℂ) (ha : a ≠ 0) :
    IsJordanPair ((fun z => a * z + b) '' Ω) ((fun z => a * z + b) '' Ωs) := by
  obtain ⟨F, h1, h2⟩ := hΓ
  let A : ℂ ≃ₜ ℂ :=
    { toFun := fun z => a * z + b
      invFun := fun z => (z - b) / a
      left_inv := fun z => by
        show (a * z + b - b) / a = z
        field_simp
        ring
      right_inv := fun z => by
        show a * ((z - b) / a) + b = z
        field_simp
        ring
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨F.trans A, ?_, ?_⟩
  · rw [← h1, ← image_comp]
    rfl
  · rw [← h2, ← image_comp]
    rfl

/-- The Möbius map `invAt x₁ ∘ (invAt x₀)⁻¹`, written as an affine map after `invAt p`,
`p = 1/(x₁ - x₀)`. -/
theorem s09_mobius_pt (x₀ x₁ w : ℂ) (hne : x₀ ≠ x₁) (h0 : w ≠ x₀) (h1 : w ≠ x₁) :
    -((x₁ - x₀) ^ 2)⁻¹ * invAt (x₁ - x₀)⁻¹ (invAt x₀ w) + -(x₁ - x₀)⁻¹ = invAt x₁ w := by
  unfold invAt
  rw [show w - x₁ = (w - x₀) - (x₁ - x₀) by ring]
  have hc : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hne.symm
  have hu : w - x₀ ≠ 0 := sub_ne_zero.mpr h0
  have huc : w - x₀ - (x₁ - x₀) ≠ 0 := by
    rw [show w - x₀ - (x₁ - x₀) = w - x₁ by ring]
    exact sub_ne_zero.mpr h1
  generalize w - x₀ = u at hu huc ⊢
  generalize x₁ - x₀ = c at hc huc ⊢
  have hcu : c - u ≠ 0 := fun h => huc (by linear_combination -h)
  have hinv : u⁻¹ - c⁻¹ = (c - u) / (u * c) := by
    field_simp
  rw [hinv, inv_div]
  field_simp
  ring

theorem s09_mobius_zero (x₀ x₁ : ℂ) (hne : x₀ ≠ x₁) :
    -((x₁ - x₀) ^ 2)⁻¹ * invAt (x₁ - x₀)⁻¹ 0 + -(x₁ - x₀)⁻¹ = 0 := by
  unfold invAt
  have hc : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hne.symm
  generalize x₁ - x₀ = c at hc ⊢
  rw [zero_sub, inv_neg, inv_inv]
  field_simp
  ring

theorem s09_mobius_image (x₀ x₁ : ℂ) (hne : x₀ ≠ x₁) (S : Set ℂ) (hS0 : x₀ ∉ S)
    (hS1 : x₁ ∉ S) :
    (fun z => -((x₁ - x₀) ^ 2)⁻¹ * z + -(x₁ - x₀)⁻¹) '' (invAt (x₁ - x₀)⁻¹ '' (invAt x₀ '' S)) =
      invAt x₁ '' S := by
  rw [image_image, image_image]
  exact image_congr fun w hw =>
    s09_mobius_pt x₀ x₁ w hne (fun h => hS0 (h ▸ hw)) (fun h => hS1 (h ▸ hw))

/-- The Poincaré extensions compose like the boundary maps. -/
theorem s09_invExt_mobius (x₀ x₁ : ℂ) (hne : x₀ ≠ x₁) (P : ℂ × ℝ) (hP : 0 < P.2) :
    (-((x₁ - x₀) ^ 2)⁻¹ * (invExt (x₁ - x₀)⁻¹ (invExt x₀ P)).1 + -(x₁ - x₀)⁻¹,
      ‖-((x₁ - x₀) ^ 2)⁻¹‖ * (invExt (x₁ - x₀)⁻¹ (invExt x₀ P)).2) = invExt x₁ P := by
  have hc : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hne.symm
  obtain ⟨W, t⟩ := P
  have ht : 0 < t := hP
  have hdist := s09_invExt_dist (W - x₀) (x₁ - x₀) t hc ht
  unfold invExt
  dsimp only
  rw [hdist, show W - x₁ = (W - x₀) - (x₁ - x₀) by ring]
  generalize W - x₀ = u
  generalize x₁ - x₀ = c at hc ⊢
  have hN : 0 < ‖u‖ ^ 2 + t ^ 2 := by positivity
  have hN1 : 0 < ‖u - c‖ ^ 2 + t ^ 2 := by positivity
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  ext
  · dsimp only
    have hN' : u * conj u + (t : ℂ) ^ 2 ≠ 0 := by
      rw [mul_conj']
      exact_mod_cast hN.ne'
    have hN1' : (u - c) * (conj u - conj c) + (t : ℂ) ^ 2 ≠ 0 := by
      rw [← map_sub, mul_conj']
      exact_mod_cast hN1.ne'
    have hcc : conj c ≠ 0 := (map_ne_zero _).mpr hc
    push_cast
    rw [← mul_conj' u, ← mul_conj' c, ← mul_conj' (u - c)]
    simp only [map_sub, map_div₀, map_inv₀, conj_conj, Complex.conj_ofReal, map_add, map_mul,
      map_pow]
    field_simp
    ring
  · dsimp only
    rw [norm_neg, norm_inv, norm_pow]
    field_simp

/-- (9.1) `eq:ambient-natural` for bounded curves (`sec09-ambient.tex:28`): the transported
quantities do not depend on the base point `x₀ ∈ Γ`. -/
theorem eq_ambient_natural_bdd (Ω Ωs : Set ℂ) (hΓ : IsBoundedJordanPair Ω Ωs) (x₀ x₁ : ℂ)
    (hx₀ : x₀ ∈ curveOf Ω Ωs) (hx₁ : x₁ ∈ curveOf Ω Ωs) (P : ℂ × ℝ) (hP : P ∈ UHS) :
    ambVBdd Ω Ωs x₀ P = ambVBdd Ω Ωs x₁ P ∧ ambHBdd Ω Ωs x₀ P = ambHBdd Ω Ωs x₁ P := by
  by_cases hne : x₀ = x₁
  · subst hne
    exact ⟨rfl, rfl⟩
  have hc : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hx₀' : x₀ ∉ Ω ∧ x₀ ∉ Ωs := by
    have := hx₀
    simp only [curveOf, mem_compl_iff, mem_union, not_or] at this
    exact this
  have hx₁' : x₁ ∉ Ω ∧ x₁ ∉ Ωs := by
    have := hx₁
    simp only [curveOf, mem_compl_iff, mem_union, not_or] at this
    exact this
  set p : ℂ := (x₁ - x₀)⁻¹ with hpdef
  set a : ℂ := -((x₁ - x₀) ^ 2)⁻¹ with hadef
  set b : ℂ := -(x₁ - x₀)⁻¹ with hbdef
  have ha : a ≠ 0 := neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hc))
  have hJ0 := s09_bdd_pair Ω Ωs hΓ x₀ hx₀
  have hJ1 := s09_bdd_pair Ω Ωs hΓ x₁ hx₁
  -- `p = invAt x₀ x₁` lies on the transported curve
  have hpS : ∀ S : Set ℂ, x₁ ∉ S → p ∉ invAt x₀ '' S := by
    rintro S hS ⟨w, hw, hwp⟩
    have : w - x₀ = x₁ - x₀ := inv_injective hwp
    exact hS (by rw [show w = x₁ by linear_combination this] at hw; exact hw)
  have hp0 : p ≠ 0 := inv_ne_zero hc
  have hp : p ∈ curveOf (invPairΩ Ω x₀) (invPairΩs Ωs x₀) := by
    simp only [curveOf, invPairΩ, invPairΩs, mem_compl_iff, mem_union, mem_singleton_iff, not_or]
    exact ⟨hpS Ω hx₁'.1, hpS Ωs hx₁'.2, hp0⟩
  have himΩ : (fun z => a * z + b) '' (invAt p '' invPairΩ Ω x₀) = invPairΩ Ω x₁ :=
    s09_mobius_image x₀ x₁ hne Ω hx₀'.1 hx₁'.1
  have himΩs : (fun z => a * z + b) '' (invAt p '' invPairΩs Ωs x₀) = invPairΩs Ωs x₁ := by
    unfold invPairΩs
    rw [image_union, image_union, image_singleton, image_singleton,
      s09_mobius_image x₀ x₁ hne Ωs hx₀'.2 hx₁'.2, s09_mobius_zero x₀ x₁ hne]
  have hmid : IsJordanPair (invAt p '' invPairΩ Ω x₀) (invAt p '' invPairΩs Ωs x₀) := by
    have h := s09_jordan_affine _ _ hJ1 a⁻¹ (-(a⁻¹ * b)) (inv_ne_zero ha)
    have hback : ∀ S : Set ℂ,
        (fun z => a⁻¹ * z + -(a⁻¹ * b)) '' ((fun z => a * z + b) '' S) = S := by
      intro S
      rw [image_image]
      conv_rhs => rw [← image_id S]
      refine image_congr fun z _ => ?_
      show a⁻¹ * (a * z + b) + -(a⁻¹ * b) = z
      field_simp
      ring
    rw [← himΩ, ← himΩs, hback, hback] at h
    exact h
  have hUHS : ∀ y : ℂ, ∀ q : ℂ × ℝ, q ∈ UHS → invExt y q ∈ UHS := fun y q hq => by
    rw [← mem_preimage, s09_invExt_UHS]
    exact hq
  have hP0 := hUHS x₀ P hP
  have hQ := hUHS p _ hP0
  have hpt : (a * (invExt p (invExt x₀ P)).1 + b, ‖a‖ * (invExt p (invExt x₀ P)).2) =
      invExt x₁ P := s09_invExt_mobius x₀ x₁ hne P hP
  obtain ⟨hc0, hcs0⟩ := s09_jordan_conformal _ _ hJ0
  obtain ⟨hcm, hcsm⟩ := s09_jordan_conformal _ _ hmid
  have hpc : p ∉ invPairΩ Ω x₀ ∧ p ∉ invPairΩs Ωs x₀ := by
    have := hp
    simp only [curveOf, mem_compl_iff, mem_union, not_or] at this
    exact this
  constructor
  · unfold ambVBdd
    rw [← hpt, ← himΩ, ← himΩs, eq_ambient_natural_V_aff _ _ hmid a b ha _ hQ,
      eq_ambient_natural_V_inv _ _ hJ0 p hp _ hP0]
  · unfold ambHBdd
    show ambHside _ _ + ambHside _ _ = ambHside _ _ + ambHside _ _
    rw [← hpt, ← himΩ, ← himΩs, eq_ambient_natural_side_aff _ hcm a b ha _ hQ,
      eq_ambient_natural_side_aff _ hcsm a b ha _ hQ,
      eq_ambient_natural_side_inv _ hc0 p hpc.1 _ hP0,
      eq_ambient_natural_side_inv _ hcs0 p hpc.2 _ hP0]

/-! ## The ambient kernel (Lemma 9.3) -/

theorem s09_cosh_half_sq (x : ℝ) : Real.cosh (x / 2) ^ 2 = (1 + Real.cosh x) / 2 := by
  have h := Real.cosh_two_mul (x / 2)
  have h2 := Real.cosh_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  linarith

theorem s09_one_le_coshDist (P Q : ℂ × ℝ) (hP : P ∈ UHS) (hQ : Q ∈ UHS) :
    1 ≤ coshDist P Q := by
  have hP' : 0 < P.2 := hP
  have hQ' : 0 < Q.2 := hQ
  unfold coshDist
  have : 0 ≤ (‖P.1 - Q.1‖ ^ 2 + (P.2 - Q.2) ^ 2) / (2 * P.2 * Q.2) := by positivity
  linarith

theorem s09_ambKernel_eq_inv (P Q : ℂ × ℝ) (h : 1 ≤ coshDist P Q) :
    ambKernel P Q = 2 / (1 + coshDist P Q) := by
  unfold ambKernel hdist
  rw [inv_pow, s09_cosh_half_sq, Real.cosh_arcosh h, inv_div]

theorem s09_ambKernel_eq (P Q : ℂ × ℝ) (hP : P ∈ UHS) (hQ : Q ∈ UHS) :
    ambKernel P Q = 4 * Q.2 * P.2 / (‖Q.1 - P.1‖ ^ 2 + (Q.2 + P.2) ^ 2) := by
  have hP' : 0 < P.2 := hP
  have hQ' : 0 < Q.2 := hQ
  rw [s09_ambKernel_eq_inv P Q (s09_one_le_coshDist P Q hP hQ)]
  unfold coshDist
  rw [norm_sub_rev]
  have h1 : 0 < ‖Q.1 - P.1‖ ^ 2 + (Q.2 + P.2) ^ 2 := by positivity
  field_simp
  ring

/-- Lemma 9.3(a) `lem:ambient-kernel` (`sec09-ambient.tex:66`): `k_P` is smooth on `ℍ³`,
`0 < k ≤ 1`, and (9.2) `eq:kernel-halfspace`
`k_P(W, ξ) = 4 ξ ξ₀ / (|W - x₀|² + (ξ + ξ₀)²)`. -/
theorem lem_ambient_kernel_a (P : ℂ × ℝ) (hP : P ∈ UHS) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ambKernel P) UHS ∧
      ∀ Q ∈ UHS, 0 < ambKernel P Q ∧ ambKernel P Q ≤ 1 ∧
        ambKernel P Q = 4 * Q.2 * P.2 / (‖Q.1 - P.1‖ ^ 2 + (Q.2 + P.2) ^ 2) := by
  have hP' : 0 < P.2 := hP
  refine ⟨?_, fun Q hQ => ?_⟩
  · refine (ContDiffOn.div ?_ ?_ ?_).congr (fun Q hQ => s09_ambKernel_eq P Q hP hQ)
    · exact ((contDiff_const.mul contDiff_snd).mul contDiff_const).contDiffOn
    · exact (((contDiff_fst.sub contDiff_const).norm_sq ℝ).add
        ((contDiff_snd.add contDiff_const).pow 2)).contDiffOn
    · intro Q hQ
      have hQ' : 0 < Q.2 := hQ
      positivity
  · have hQ' : 0 < Q.2 := hQ
    have h1 : 0 < ‖Q.1 - P.1‖ ^ 2 + (Q.2 + P.2) ^ 2 := by positivity
    rw [s09_ambKernel_eq P Q hP hQ]
    refine ⟨by positivity, ?_, rfl⟩
    rw [div_le_one h1]
    nlinarith [sq_nonneg (Q.2 - P.2), sq_nonneg ‖Q.1 - P.1‖]

/-- Directional derivative along a line. -/
theorem s09_fderiv_eq_deriv_line {g : ℂ × ℝ → ℝ} {Q : ℂ × ℝ} (hg : DifferentiableAt ℝ g Q)
    (v : ℂ × ℝ) : fderiv ℝ g Q v = deriv (fun t : ℝ => g (Q + t • v)) 0 := by
  have hl : HasDerivAt (fun t : ℝ => Q + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add Q
  have := (hg.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp))
  exact this.deriv.symm

/-- `HasDerivAt` of `arcosh` at `x > 1`. -/
theorem s09_hasDerivAt_arcosh {x : ℝ} (hx : 1 < x) :
    HasDerivAt Real.arcosh (Real.sqrt (x ^ 2 - 1))⁻¹ x := by
  have h1 : 0 < Real.arcosh x := Real.arcosh_pos hx
  have hs : Real.sinh (Real.arcosh x) = Real.sqrt (x ^ 2 - 1) := Real.sinh_arcosh hx.le
  have hne : Real.sqrt (x ^ 2 - 1) ≠ 0 := by
    rw [← hs]; exact (Real.sinh_pos_iff.mpr h1).ne'
  have hc : ContinuousAt Real.arcosh x :=
    (Real.continuousOn_arcosh.continuousAt (Ici_mem_nhds hx))
  refine HasDerivAt.of_local_left_inverse (f := Real.cosh) hc ?_ hne ?_
  · rw [← hs]; exact Real.hasDerivAt_cosh _
  · filter_upwards [Ici_mem_nhds hx] with y hy
    exact Real.cosh_arcosh hy

theorem s09_isOpen_UHS : IsOpen UHS := isOpen_lt continuous_const continuous_snd

theorem s09_eventually_line_mem (Q v : ℂ × ℝ) (hQ : Q ∈ UHS) :
    ∀ᶠ t in 𝓝 (0 : ℝ), Q + t • v ∈ UHS := by
  have hcont : Tendsto (fun t : ℝ => Q + t • v) (𝓝 0) (𝓝 Q) := by
    have hc : Continuous fun t : ℝ => Q + t • v := by fun_prop
    convert hc.tendsto 0 using 2
    simp
  exact hcont.eventually (s09_isOpen_UHS.mem_nhds hQ)

/-- `cosh d(P, Q + t v)` along a line, in real coordinates. -/
theorem s09_coshDist_line (P Q v : ℂ × ℝ) (t : ℝ) :
    coshDist P (Q + t • v) = 1 + ((P.1.re - Q.1.re - t * v.1.re) ^ 2 +
      (P.1.im - Q.1.im - t * v.1.im) ^ 2 + (P.2 - Q.2 - t * v.2) ^ 2) /
        (2 * P.2 * (Q.2 + t * v.2)) := by
  simp only [coshDist, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

theorem s09_hasDerivAt_c_line (A B C a b s ξ₀ ξ : ℝ) (hξ₀ : ξ₀ ≠ 0) (hξ : ξ ≠ 0) :
    HasDerivAt (fun t : ℝ => 1 + ((A - t * a) ^ 2 + (B - t * b) ^ 2 + (C - t * s) ^ 2) /
        (2 * ξ₀ * (ξ + t * s)))
      (-(A * a + B * b + C * s) / (ξ₀ * ξ) - (A ^ 2 + B ^ 2 + C ^ 2) * s / (2 * ξ₀ * ξ ^ 2))
      0 := by
  have hA := ((hasDerivAt_mul_const (x := (0 : ℝ)) a).const_sub A).pow 2
  have hB := ((hasDerivAt_mul_const (x := (0 : ℝ)) b).const_sub B).pow 2
  have hC := ((hasDerivAt_mul_const (x := (0 : ℝ)) s).const_sub C).pow 2
  have hd := ((hasDerivAt_mul_const (x := (0 : ℝ)) s).const_add ξ).const_mul (2 * ξ₀)
  have h := (((hA.add hB).add hC).div hd (by simp [hξ₀, hξ])).const_add 1
  convert h using 1
  simp only [Pi.add_apply, Pi.pow_apply, zero_mul, sub_zero, add_zero]
  field_simp
  ring

theorem s09_hasDerivAt_G_line (A B C a b s a' b' s' ξ₀ ξ : ℝ) (hξ₀ : ξ₀ ≠ 0) (hξ : ξ ≠ 0) :
    HasDerivAt (fun t : ℝ => -((A - t * a) * a' + (B - t * b) * b' + (C - t * s) * s') /
          (ξ₀ * (ξ + t * s)) -
        ((A - t * a) ^ 2 + (B - t * b) ^ 2 + (C - t * s) ^ 2) * s' /
          (2 * ξ₀ * (ξ + t * s) ^ 2))
      ((a * a' + b * b' + s * s') / (ξ₀ * ξ) + (A * a' + B * b' + C * s') * s / (ξ₀ * ξ ^ 2) +
        (A * a + B * b + C * s) * s' / (ξ₀ * ξ ^ 2) +
        (A ^ 2 + B ^ 2 + C ^ 2) * s * s' / (ξ₀ * ξ ^ 3)) 0 := by
  have hA := (hasDerivAt_mul_const (x := (0 : ℝ)) a).const_sub A
  have hB := (hasDerivAt_mul_const (x := (0 : ℝ)) b).const_sub B
  have hC := (hasDerivAt_mul_const (x := (0 : ℝ)) s).const_sub C
  have hl := (hasDerivAt_mul_const (x := (0 : ℝ)) s).const_add ξ
  have h1 := ((((hA.mul_const a').add (hB.mul_const b')).add (hC.mul_const s')).neg).div
    (hl.const_mul ξ₀) (by simp [hξ₀, hξ])
  have h2 := ((((hA.pow 2).add (hB.pow 2)).add (hC.pow 2)).mul_const s').div
    ((hl.pow 2).const_mul (2 * ξ₀)) (by simp [hξ₀, hξ])
  convert h1.sub h2 using 1
  simp only [Pi.add_apply, Pi.pow_apply, Pi.neg_apply, zero_mul, sub_zero, add_zero]
  field_simp
  ring

theorem s09_contDiffAt_coshDist (P Q : ℂ × ℝ) (hP : P.2 ≠ 0) (hQ : Q.2 ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (coshDist P) Q := by
  have e : coshDist P = fun Q => 1 + (‖P.1 - Q.1‖ ^ 2 + (P.2 - Q.2) ^ 2) / (2 * P.2 * Q.2) := rfl
  rw [e]
  refine contDiffAt_const.add (ContDiffAt.div ?_ ?_ ?_)
  · exact (((contDiff_const.sub contDiff_fst).norm_sq ℝ).add
      ((contDiff_const.sub contDiff_snd).pow 2)).contDiffAt
  · exact (contDiff_const.mul contDiff_snd).contDiffAt
  · exact mul_ne_zero (mul_ne_zero two_ne_zero hP) hQ

theorem s09_fderiv_coshDist (P Q w : ℂ × ℝ) (hP : P ∈ UHS) (hQ : Q ∈ UHS) :
    fderiv ℝ (coshDist P) Q w =
      -((P.1.re - Q.1.re) * w.1.re + (P.1.im - Q.1.im) * w.1.im + (P.2 - Q.2) * w.2) /
          (P.2 * Q.2) -
        ((P.1.re - Q.1.re) ^ 2 + (P.1.im - Q.1.im) ^ 2 + (P.2 - Q.2) ^ 2) * w.2 /
          (2 * P.2 * Q.2 ^ 2) := by
  have hP' : 0 < P.2 := hP
  have hQ' : 0 < Q.2 := hQ
  rw [s09_fderiv_eq_deriv_line
    ((s09_contDiffAt_coshDist P Q hP'.ne' hQ'.ne').differentiableAt (by simp)) w]
  rw [show (fun t : ℝ => coshDist P (Q + t • w)) = _ from funext (s09_coshDist_line P Q w)]
  exact (s09_hasDerivAt_c_line _ _ _ _ _ _ _ _ hP'.ne' hQ'.ne').deriv

theorem s09_hasDerivAt_coshDist_line (P Q v : ℂ × ℝ) (hP : P ∈ UHS) (hQ : Q ∈ UHS) :
    HasDerivAt (fun t : ℝ => coshDist P (Q + t • v)) (fderiv ℝ (coshDist P) Q v) 0 := by
  have hP' : 0 < P.2 := hP
  have hQ' : 0 < Q.2 := hQ
  rw [s09_fderiv_coshDist P Q v hP hQ,
    show (fun t : ℝ => coshDist P (Q + t • v)) = _ from funext (s09_coshDist_line P Q v)]
  exact s09_hasDerivAt_c_line _ _ _ _ _ _ _ _ hP'.ne' hQ'.ne'

theorem s09_fderiv_fderiv_coshDist (P Q v w : ℂ × ℝ) (hP : P ∈ UHS) (hQ : Q ∈ UHS) :
    fderiv ℝ (fderiv ℝ (coshDist P)) Q v w =
      (v.1.re * w.1.re + v.1.im * w.1.im + v.2 * w.2) / (P.2 * Q.2) +
        ((P.1.re - Q.1.re) * w.1.re + (P.1.im - Q.1.im) * w.1.im + (P.2 - Q.2) * w.2) * v.2 /
          (P.2 * Q.2 ^ 2) +
        ((P.1.re - Q.1.re) * v.1.re + (P.1.im - Q.1.im) * v.1.im + (P.2 - Q.2) * v.2) * w.2 /
          (P.2 * Q.2 ^ 2) +
        ((P.1.re - Q.1.re) ^ 2 + (P.1.im - Q.1.im) ^ 2 + (P.2 - Q.2) ^ 2) * v.2 * w.2 /
          (P.2 * Q.2 ^ 3) := by
  have hP' : 0 < P.2 := hP
  have hQ' : 0 < Q.2 := hQ
  have hcd := s09_contDiffAt_coshDist P Q hP'.ne' hQ'.ne'
  have hD : DifferentiableAt ℝ (fderiv ℝ (coshDist P)) Q :=
    (hcd.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt (by simp)
  have e1 : fderiv ℝ (fderiv ℝ (coshDist P)) Q v w =
      fderiv ℝ (fun Q' => fderiv ℝ (coshDist P) Q' w) Q v := by
    rw [fderiv_clm_apply hD (differentiableAt_const w)]
    simp
  rw [e1, s09_fderiv_eq_deriv_line (hD.clm_apply (differentiableAt_const w)) v]
  have hev : (fun t : ℝ => fderiv ℝ (coshDist P) (Q + t • v) w) =ᶠ[𝓝 0]
      fun t : ℝ => -((P.1.re - Q.1.re - t * v.1.re) * w.1.re +
          (P.1.im - Q.1.im - t * v.1.im) * w.1.im + (P.2 - Q.2 - t * v.2) * w.2) /
            (P.2 * (Q.2 + t * v.2)) -
        ((P.1.re - Q.1.re - t * v.1.re) ^ 2 + (P.1.im - Q.1.im - t * v.1.im) ^ 2 +
          (P.2 - Q.2 - t * v.2) ^ 2) * w.2 / (2 * P.2 * (Q.2 + t * v.2) ^ 2) := by
    filter_upwards [s09_eventually_line_mem Q v hQ] with t ht
    rw [s09_fderiv_coshDist P _ w hP ht]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    ring_nf
  rw [hev.deriv_eq]
  exact (s09_hasDerivAt_G_line _ _ _ _ _ _ _ _ _ _ _ hP'.ne' hQ'.ne').deriv

theorem s09_contDiffOn_ambKernel (P : ℂ × ℝ) (hP : P ∈ UHS) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ambKernel P) UHS :=
  (lem_ambient_kernel_a P hP).1

theorem s09_hasDerivAt_line {g : ℂ × ℝ → ℝ} {Q : ℂ × ℝ} (hg : DifferentiableAt ℝ g Q)
    (v : ℂ × ℝ) : HasDerivAt (fun t : ℝ => g (Q + t • v)) (fderiv ℝ g Q v) 0 := by
  have hl : HasDerivAt (fun t : ℝ => Q + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add Q
  exact hg.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)

theorem s09_fderiv_clm_apply_const {f : ℂ × ℝ → ℝ} {Q : ℂ × ℝ}
    (hD : DifferentiableAt ℝ (fderiv ℝ f) Q) (v w : ℂ × ℝ) :
    fderiv ℝ (fun Q' => fderiv ℝ f Q' w) Q v = fderiv ℝ (fderiv ℝ f) Q v w := by
  rw [fderiv_clm_apply hD (differentiableAt_const w)]
  simp

theorem s09_ambKernel_eventually (P Q : ℂ × ℝ) (hP : P ∈ UHS) (hQ : Q ∈ UHS) :
    ambKernel P =ᶠ[𝓝 Q] fun Q' => 2 / (1 + coshDist P Q') := by
  filter_upwards [s09_isOpen_UHS.mem_nhds hQ] with Q' hQ'
  exact s09_ambKernel_eq_inv P Q' (s09_one_le_coshDist P Q' hP hQ')

theorem s09_fderiv_ambKernel (P Q w : ℂ × ℝ) (hP : P ∈ UHS) (hQ : Q ∈ UHS) :
    fderiv ℝ (ambKernel P) Q w =
      -2 / (1 + coshDist P Q) ^ 2 * fderiv ℝ (coshDist P) Q w := by
  have hP' : 0 < P.2 := hP
  have hQ' : 0 < Q.2 := hQ
  have hc1 := s09_one_le_coshDist P Q hP hQ
  have hcd : HasFDerivAt (coshDist P) (fderiv ℝ (coshDist P) Q) Q :=
    ((s09_contDiffAt_coshDist P Q hP'.ne' hQ'.ne').differentiableAt (by simp)).hasFDerivAt
  have hφ : HasDerivAt (fun x : ℝ => 2 / (1 + x)) (-2 / (1 + coshDist P Q) ^ 2)
      (coshDist P Q) := by
    have h := (hasDerivAt_const (coshDist P Q) (2 : ℝ)).div
      ((hasDerivAt_id (coshDist P Q)).const_add 1) (by simp; linarith)
    convert h using 1
    · funext x
      simp
    · simp only [id]
      ring
  have hcomp : HasFDerivAt (fun Q' => 2 / (1 + coshDist P Q'))
      ((-2 / (1 + coshDist P Q) ^ 2) • fderiv ℝ (coshDist P) Q) Q :=
    hφ.comp_hasFDerivAt Q hcd
  rw [(s09_ambKernel_eventually P Q hP hQ).fderiv_eq, hcomp.fderiv]
  simp [smul_eq_mul]

theorem s09_fderiv_fderiv_ambKernel (P Q v w : ℂ × ℝ) (hP : P ∈ UHS) (hQ : Q ∈ UHS) :
    fderiv ℝ (fderiv ℝ (ambKernel P)) Q v w =
      4 / (1 + coshDist P Q) ^ 3 * (fderiv ℝ (coshDist P) Q v * fderiv ℝ (coshDist P) Q w) +
        -2 / (1 + coshDist P Q) ^ 2 * fderiv ℝ (fderiv ℝ (coshDist P)) Q v w := by
  have hP' : 0 < P.2 := hP
  have hQ' : 0 < Q.2 := hQ
  have hc1 := s09_one_le_coshDist P Q hP hQ
  have hk : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ambKernel P) Q :=
    (s09_contDiffOn_ambKernel P hP).contDiffAt (s09_isOpen_UHS.mem_nhds hQ)
  have hD : DifferentiableAt ℝ (fderiv ℝ (ambKernel P)) Q :=
    (hk.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt (by simp)
  have hcd := s09_contDiffAt_coshDist P Q hP'.ne' hQ'.ne'
  have hDc : DifferentiableAt ℝ (fderiv ℝ (coshDist P)) Q :=
    (hcd.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt (by simp)
  rw [← s09_fderiv_clm_apply_const hD,
    s09_fderiv_eq_deriv_line (hD.clm_apply (differentiableAt_const w)) v]
  have hev : (fun t : ℝ => fderiv ℝ (ambKernel P) (Q + t • v) w) =ᶠ[𝓝 0]
      fun t : ℝ => -2 / (1 + coshDist P (Q + t • v)) ^ 2 *
        fderiv ℝ (coshDist P) (Q + t • v) w := by
    filter_upwards [s09_eventually_line_mem Q v hQ] with t ht
    exact s09_fderiv_ambKernel P _ w hP ht
  rw [hev.deriv_eq]
  have hψ : HasDerivAt (fun x : ℝ => -2 / (1 + x) ^ 2) (4 / (1 + coshDist P Q) ^ 3)
      (coshDist P Q) := by
    have h := (hasDerivAt_const (coshDist P Q) (-2 : ℝ)).div
      (((hasDerivAt_id (coshDist P Q)).const_add 1).pow 2) (by simp; positivity)
    convert h using 1
    · funext x
      simp
    · simp only [id, Pi.pow_apply]
      norm_num
      field_simp
      ring
  have hcl := s09_hasDerivAt_coshDist_line P Q v hP hQ
  have h1 : HasDerivAt (fun t : ℝ => -2 / (1 + coshDist P (Q + t • v)) ^ 2)
      (4 / (1 + coshDist P Q) ^ 3 * fderiv ℝ (coshDist P) Q v) 0 :=
    hψ.comp_of_eq (0 : ℝ) hcl (by simp)
  have h2 : HasDerivAt (fun t : ℝ => fderiv ℝ (coshDist P) (Q + t • v) w)
      (fderiv ℝ (fderiv ℝ (coshDist P)) Q v w) 0 := by
    have := s09_hasDerivAt_line (hDc.clm_apply (differentiableAt_const w)) v
    rwa [s09_fderiv_clm_apply_const hDc] at this
  have h12 : HasDerivAt (fun t : ℝ => -2 / (1 + coshDist P (Q + t • v)) ^ 2 *
      fderiv ℝ (coshDist P) (Q + t • v) w)
      (4 / (1 + coshDist P Q) ^ 3 * fderiv ℝ (coshDist P) Q v *
          fderiv ℝ (coshDist P) (Q + (0 : ℝ) • v) w +
        -2 / (1 + coshDist P (Q + (0 : ℝ) • v)) ^ 2 *
          fderiv ℝ (fderiv ℝ (coshDist P)) Q v w) 0 := h1.mul h2
  rw [h12.deriv]
  simp only [zero_smul, add_zero]
  ring

/-- `∇² cosh d(P, ·) = cosh d(P, ·) g`. -/
theorem s09_hypHess_coshDist (P Q v w : ℂ × ℝ) (hP : P ∈ UHS) (hQ : Q ∈ UHS) :
    hypHess (coshDist P) Q v w = coshDist P Q * hypMetric Q v w := by
  have hP' : 0 < P.2 := hP
  have hQ' : 0 < Q.2 := hQ
  unfold hypHess
  rw [s09_fderiv_fderiv_coshDist P Q v w hP hQ, s09_fderiv_coshDist P Q v hP hQ,
    s09_fderiv_coshDist P Q w hP hQ, s09_fderiv_coshDist P Q (0, 1) hP hQ]
  simp only [hypMetric, eucInner, coshDist, Complex.sq_norm, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.zero_re, Complex.zero_im]
  field_simp
  ring

theorem s09_hypHess_ambKernel (P Q v w : ℂ × ℝ) (hP : P ∈ UHS) (hQ : Q ∈ UHS) :
    hypHess (ambKernel P) Q v w =
      -2 * coshDist P Q / (1 + coshDist P Q) ^ 2 * hypMetric Q v w +
        4 / (1 + coshDist P Q) ^ 3 *
          (fderiv ℝ (coshDist P) Q v * fderiv ℝ (coshDist P) Q w) := by
  have h := s09_hypHess_coshDist P Q v w hP hQ
  unfold hypHess at h ⊢
  rw [s09_fderiv_fderiv_ambKernel P Q v w hP hQ, s09_fderiv_ambKernel P Q v hP hQ,
    s09_fderiv_ambKernel P Q w hP hQ, s09_fderiv_ambKernel P Q (0, 1) hP hQ]
  have hc1 := s09_one_le_coshDist P Q hP hQ
  have hD : (1 + coshDist P Q) ≠ 0 := by linarith
  have hQ' : Q.2 ≠ 0 := (show (0 : ℝ) < Q.2 from hQ).ne'
  rw [show fderiv ℝ (fderiv ℝ (coshDist P)) Q v w = coshDist P Q * hypMetric Q v w -
    (w.2 * fderiv ℝ (coshDist P) Q v + v.2 * fderiv ℝ (coshDist P) Q w -
      eucInner v w * fderiv ℝ (coshDist P) Q (0, 1)) / Q.2 by linarith]
  ring

theorem s09_one_lt_coshDist (P Q : ℂ × ℝ) (hP : P ∈ UHS) (hQ : Q ∈ UHS) (hne : Q ≠ P) :
    1 < coshDist P Q := by
  have hP' : 0 < P.2 := hP
  have hQ' : 0 < Q.2 := hQ
  have hN : 0 < ‖P.1 - Q.1‖ ^ 2 + (P.2 - Q.2) ^ 2 := by
    by_contra h
    push_neg at h
    have h1 : ‖P.1 - Q.1‖ = 0 := by
      nlinarith [sq_nonneg ‖P.1 - Q.1‖, sq_nonneg (P.2 - Q.2), norm_nonneg (P.1 - Q.1)]
    have h2 : P.2 - Q.2 = 0 := by nlinarith [sq_nonneg ‖P.1 - Q.1‖, sq_nonneg (P.2 - Q.2)]
    exact hne (Prod.ext (sub_eq_zero.mp (norm_eq_zero.mp h1)).symm (sub_eq_zero.mp h2).symm)
  unfold coshDist
  have : 0 < (‖P.1 - Q.1‖ ^ 2 + (P.2 - Q.2) ^ 2) / (2 * P.2 * Q.2) := by positivity
  linarith

theorem s09_fderiv_hdist (P Q v : ℂ × ℝ) (hP : P ∈ UHS) (hQ : Q ∈ UHS) (hne : Q ≠ P) :
    fderiv ℝ (hdist P) Q v =
      (Real.sqrt (coshDist P Q ^ 2 - 1))⁻¹ * fderiv ℝ (coshDist P) Q v := by
  have hP' : 0 < P.2 := hP
  have hQ' : 0 < Q.2 := hQ
  have hcd : HasFDerivAt (coshDist P) (fderiv ℝ (coshDist P) Q) Q :=
    ((s09_contDiffAt_coshDist P Q hP'.ne' hQ'.ne').differentiableAt (by simp)).hasFDerivAt
  have h := (s09_hasDerivAt_arcosh (s09_one_lt_coshDist P Q hP hQ hne)).comp_hasFDerivAt Q hcd
  have e : hdist P = Real.arcosh ∘ coshDist P := rfl
  rw [e, h.fderiv]
  simp [smul_eq_mul]

theorem s09_fderiv_coshDist_self (P v : ℂ × ℝ) (hP : P ∈ UHS) :
    fderiv ℝ (coshDist P) P v = 0 := by
  rw [s09_fderiv_coshDist P P v hP hP]
  simp

theorem s09_coshDist_self (P : ℂ × ℝ) : coshDist P P = 1 := by
  simp [coshDist]

/-- Lemma 9.3(b) `lem:ambient-kernel`, (9.3) `eq:ambient-hessian` (`sec09-ambient.tex:73`):
`∇²k = (-k + ½k²) g + 2k(1-k) dr ⊗ dr` off `P`, and `∇²k(P) = -½ g`. -/
theorem lem_ambient_kernel_b (P : ℂ × ℝ) (hP : P ∈ UHS) :
    (∀ Q ∈ UHS, Q ≠ P → ∀ v w : ℂ × ℝ,
      hypHess (ambKernel P) Q v w =
        (-ambKernel P Q + ambKernel P Q ^ 2 / 2) * hypMetric Q v w +
          2 * ambKernel P Q * (1 - ambKernel P Q) *
            (fderiv ℝ (hdist P) Q v * fderiv ℝ (hdist P) Q w)) ∧
      ∀ v w : ℂ × ℝ, hypHess (ambKernel P) P v w = -(1 / 2) * hypMetric P v w := by
  refine ⟨fun Q hQ hne v w => ?_, fun v w => ?_⟩
  · have hc := s09_one_lt_coshDist P Q hP hQ hne
    rw [s09_hypHess_ambKernel P Q v w hP hQ, s09_fderiv_hdist P Q v hP hQ hne,
      s09_fderiv_hdist P Q w hP hQ hne,
      s09_ambKernel_eq_inv P Q (s09_one_le_coshDist P Q hP hQ)]
    have hs : Real.sqrt (coshDist P Q ^ 2 - 1) ^ 2 = coshDist P Q ^ 2 - 1 :=
      Real.sq_sqrt (by nlinarith)
    have hs0 : Real.sqrt (coshDist P Q ^ 2 - 1) ≠ 0 := by
      rw [Real.sqrt_ne_zero']; nlinarith
    have hD : (1 + coshDist P Q) ≠ 0 := by linarith
    have hD' : coshDist P Q - 1 ≠ 0 := by linarith
    field_simp
    rw [hs]
    ring
  · rw [s09_hypHess_ambKernel P P v w hP hP, s09_fderiv_coshDist_self P v hP,
      s09_coshDist_self]
    ring

/-- The Euclidean gradient of `cosh d(P, ·)` at `Q`, with `ξ² |G|² = cosh² d - 1`. -/
theorem s09_dc_grad (P Q : ℂ × ℝ) (hP : P ∈ UHS) (hQ : Q ∈ UHS) :
    ∃ g1 g2 g3 : ℝ, (∀ v : ℂ × ℝ,
        fderiv ℝ (coshDist P) Q v = g1 * v.1.re + g2 * v.1.im + g3 * v.2) ∧
      Q.2 ^ 2 * (g1 ^ 2 + g2 ^ 2 + g3 ^ 2) = coshDist P Q ^ 2 - 1 := by
  have hP' : 0 < P.2 := hP
  have hQ' : 0 < Q.2 := hQ
  have hP0 : P.2 ≠ 0 := hP'.ne'
  have hQ0 : Q.2 ≠ 0 := hQ'.ne'
  refine ⟨-(P.1.re - Q.1.re) / (P.2 * Q.2), -(P.1.im - Q.1.im) / (P.2 * Q.2),
    -(P.2 - Q.2) / (P.2 * Q.2) -
      ((P.1.re - Q.1.re) ^ 2 + (P.1.im - Q.1.im) ^ 2 + (P.2 - Q.2) ^ 2) / (2 * P.2 * Q.2 ^ 2),
    fun v => ?_, ?_⟩
  · rw [s09_fderiv_coshDist P Q v hP hQ]
    ring
  · simp only [coshDist, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    field_simp
    ring

theorem s09_cs3 (g1 g2 g3 a b s : ℝ) :
    (g1 * a + g2 * b + g3 * s) ^ 2 ≤ (g1 ^ 2 + g2 ^ 2 + g3 ^ 2) * (a * a + b * b + s * s) := by
  nlinarith [sq_nonneg (g1 * b - g2 * a), sq_nonneg (g1 * s - g3 * a), sq_nonneg (g2 * s - g3 * b)]

/-- Bessel's inequality in `ℝ³` for an orthogonal pair of vectors of squared length `t`. -/
theorem s09_bessel3 (t g1 g2 g3 a1 b1 s1 a2 b2 s2 : ℝ) (ht : 0 < t)
    (h₁ : a1 * a1 + b1 * b1 + s1 * s1 = t) (h₂ : a2 * a2 + b2 * b2 + s2 * s2 = t)
    (h₁₂ : a1 * a2 + b1 * b2 + s1 * s2 = 0) :
    (g1 * a1 + g2 * b1 + g3 * s1) ^ 2 + (g1 * a2 + g2 * b2 + g3 * s2) ^ 2 ≤
      t * (g1 ^ 2 + g2 ^ 2 + g3 ^ 2) := by
  have hw : 0 ≤ (t * g1 - (g1 * a1 + g2 * b1 + g3 * s1) * a1 - (g1 * a2 + g2 * b2 + g3 * s2) * a2) ^ 2 +
      (t * g2 - (g1 * a1 + g2 * b1 + g3 * s1) * b1 - (g1 * a2 + g2 * b2 + g3 * s2) * b2) ^ 2 +
      (t * g3 - (g1 * a1 + g2 * b1 + g3 * s1) * s1 - (g1 * a2 + g2 * b2 + g3 * s2) * s2) ^ 2 := by
    positivity
  have e : t * (t * (g1 ^ 2 + g2 ^ 2 + g3 ^ 2) - (g1 * a1 + g2 * b1 + g3 * s1) ^ 2 -
      (g1 * a2 + g2 * b2 + g3 * s2) ^ 2) =
      (t * g1 - (g1 * a1 + g2 * b1 + g3 * s1) * a1 - (g1 * a2 + g2 * b2 + g3 * s2) * a2) ^ 2 +
      (t * g2 - (g1 * a1 + g2 * b1 + g3 * s1) * b1 - (g1 * a2 + g2 * b2 + g3 * s2) * b2) ^ 2 +
      (t * g3 - (g1 * a1 + g2 * b1 + g3 * s1) * s1 - (g1 * a2 + g2 * b2 + g3 * s2) * s2) ^ 2 := by
    linear_combination (-(g1 * a1 + g2 * b1 + g3 * s1) ^ 2) * h₁ +
      (-(g1 * a2 + g2 * b2 + g3 * s2) ^ 2) * h₂ +
      (-2 * (g1 * a1 + g2 * b1 + g3 * s1) * (g1 * a2 + g2 * b2 + g3 * s2)) * h₁₂
  by_contra hneg
  push_neg at hneg
  have := mul_neg_of_pos_of_neg ht (by linarith :
    t * (g1 ^ 2 + g2 ^ 2 + g3 ^ 2) - (g1 * a1 + g2 * b1 + g3 * s1) ^ 2 -
      (g1 * a2 + g2 * b2 + g3 * s2) ^ 2 < 0)
  linarith

/-- Cauchy–Schwarz: `(d cosh d(P, ·)(v))² ≤ (cosh² d - 1) g(v, v)`, i.e. `|∇r| = 1`. -/
theorem s09_dc_sq_le (P Q v : ℂ × ℝ) (hP : P ∈ UHS) (hQ : Q ∈ UHS) :
    fderiv ℝ (coshDist P) Q v ^ 2 ≤ (coshDist P Q ^ 2 - 1) * hypMetric Q v v := by
  obtain ⟨g1, g2, g3, hdc, hS⟩ := s09_dc_grad P Q hP hQ
  have hQ0 : Q.2 ≠ 0 := (show (0 : ℝ) < Q.2 from hQ).ne'
  have e : (coshDist P Q ^ 2 - 1) * hypMetric Q v v =
      (g1 ^ 2 + g2 ^ 2 + g3 ^ 2) * (v.1.re * v.1.re + v.1.im * v.1.im + v.2 * v.2) := by
    rw [← hS]
    unfold hypMetric eucInner
    field_simp
  rw [e, hdc]
  exact s09_cs3 g1 g2 g3 _ _ _

/-- Bessel: for a `g`-orthonormal pair, `dc(e₁)² + dc(e₂)² ≤ cosh² d - 1`. -/
theorem s09_dc_bessel (P Q : ℂ × ℝ) (hP : P ∈ UHS) (hQ : Q ∈ UHS)
    (e₁ e₂ : ℂ × ℝ) (h₁ : hypMetric Q e₁ e₁ = 1) (h₂ : hypMetric Q e₂ e₂ = 1)
    (h₁₂ : hypMetric Q e₁ e₂ = 0) :
    fderiv ℝ (coshDist P) Q e₁ ^ 2 + fderiv ℝ (coshDist P) Q e₂ ^ 2 ≤ coshDist P Q ^ 2 - 1 := by
  obtain ⟨g1, g2, g3, hdc, hS⟩ := s09_dc_grad P Q hP hQ
  have ht : (0 : ℝ) < Q.2 ^ 2 := by
    have : (0 : ℝ) < Q.2 := hQ
    positivity
  unfold hypMetric eucInner at h₁ h₂ h₁₂
  rw [div_eq_one_iff_eq ht.ne'] at h₁ h₂
  rw [div_eq_zero_iff, or_iff_left ht.ne'] at h₁₂
  rw [hdc, hdc, ← hS]
  exact s09_bessel3 _ g1 g2 g3 _ _ _ _ _ _ ht h₁ h₂ h₁₂

theorem s09_hs_bound (c u1 u2 u3 : ℝ) (hc : 1 ≤ c)
    (hS : u1 ^ 2 + u2 ^ 2 + u3 ^ 2 = c ^ 2 - 1) :
    (-2 * c / (1 + c) ^ 2 + 4 / (1 + c) ^ 3 * (u1 * u1)) ^ 2 +
        (4 / (1 + c) ^ 3 * (u1 * u2)) ^ 2 + (4 / (1 + c) ^ 3 * (u1 * u3)) ^ 2 +
        (4 / (1 + c) ^ 3 * (u2 * u1)) ^ 2 +
        (-2 * c / (1 + c) ^ 2 + 4 / (1 + c) ^ 3 * (u2 * u2)) ^ 2 +
        (4 / (1 + c) ^ 3 * (u2 * u3)) ^ 2 + (4 / (1 + c) ^ 3 * (u3 * u1)) ^ 2 +
        (4 / (1 + c) ^ 3 * (u3 * u2)) ^ 2 +
        (-2 * c / (1 + c) ^ 2 + 4 / (1 + c) ^ 3 * (u3 * u3)) ^ 2 ≤
      3 * (2 / (1 + c)) ^ 2 := by
  have hD : 0 < 1 + c := by linarith
  have hD' : 1 + c ≠ 0 := hD.ne'
  have e : (-2 * c / (1 + c) ^ 2 + 4 / (1 + c) ^ 3 * (u1 * u1)) ^ 2 +
        (4 / (1 + c) ^ 3 * (u1 * u2)) ^ 2 + (4 / (1 + c) ^ 3 * (u1 * u3)) ^ 2 +
        (4 / (1 + c) ^ 3 * (u2 * u1)) ^ 2 +
        (-2 * c / (1 + c) ^ 2 + 4 / (1 + c) ^ 3 * (u2 * u2)) ^ 2 +
        (4 / (1 + c) ^ 3 * (u2 * u3)) ^ 2 + (4 / (1 + c) ^ 3 * (u3 * u1)) ^ 2 +
        (4 / (1 + c) ^ 3 * (u3 * u2)) ^ 2 +
        (-2 * c / (1 + c) ^ 2 + 4 / (1 + c) ^ 3 * (u3 * u3)) ^ 2 =
      3 * (-2 * c / (1 + c) ^ 2) ^ 2 +
        2 * (4 / (1 + c) ^ 3) * (-2 * c / (1 + c) ^ 2) * (u1 ^ 2 + u2 ^ 2 + u3 ^ 2) +
        (4 / (1 + c) ^ 3) ^ 2 * (u1 ^ 2 + u2 ^ 2 + u3 ^ 2) ^ 2 := by ring
  rw [e, hS, ← sub_nonneg]
  have e2 : 3 * (2 / (1 + c)) ^ 2 - (3 * (-2 * c / (1 + c) ^ 2) ^ 2 +
      2 * (4 / (1 + c) ^ 3) * (-2 * c / (1 + c) ^ 2) * (c ^ 2 - 1) +
      (4 / (1 + c) ^ 3) ^ 2 * (c ^ 2 - 1) ^ 2) = (40 * c - 4) / (1 + c) ^ 4 := by
    field_simp
    ring
  rw [e2]
  exact div_nonneg (by linarith) (by positivity)

/-- Lemma 9.3(c) `lem:ambient-kernel` (`sec09-ambient.tex:78`): `|∇k| ≤ k`, the eigenvalues of
`∇²k` lie in `[-k, k]`, and the Hilbert–Schmidt norm (in a `g`-orthonormal frame
`ξ eᵢ`) is `≤ √3 k ≤ 2k`. -/
theorem lem_ambient_kernel_c (P : ℂ × ℝ) (hP : P ∈ UHS) (Q : ℂ × ℝ) (hQ : Q ∈ UHS) :
    (∀ v : ℂ × ℝ, (fderiv ℝ (ambKernel P) Q v) ^ 2 ≤ ambKernel P Q ^ 2 * hypMetric Q v v) ∧
      (∀ v : ℂ × ℝ, |hypHess (ambKernel P) Q v v| ≤ ambKernel P Q * hypMetric Q v v) ∧
      Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
          (Q.2 ^ 2 * hypHess (ambKernel P) Q (eucBasis i) (eucBasis j)) ^ 2) ≤
        Real.sqrt 3 * ambKernel P Q ∧
      Real.sqrt 3 * ambKernel P Q ≤ 2 * ambKernel P Q := by
  have hc1 := s09_one_le_coshDist P Q hP hQ
  have hD : 0 < 1 + coshDist P Q := by linarith
  have hD' : 1 + coshDist P Q ≠ 0 := hD.ne'
  have hk := s09_ambKernel_eq_inv P Q hc1
  have hQ0 : Q.2 ≠ 0 := (show (0 : ℝ) < Q.2 from hQ).ne'
  have hg : ∀ v : ℂ × ℝ, 0 ≤ hypMetric Q v v := by
    intro v
    unfold hypMetric eucInner
    apply div_nonneg _ (sq_nonneg _)
    nlinarith [mul_self_nonneg v.1.re, mul_self_nonneg v.1.im, mul_self_nonneg v.2]
  have hk0 : 0 ≤ ambKernel P Q := by
    rw [hk]
    exact div_nonneg (by norm_num) hD.le
  refine ⟨fun v => ?_, fun v => ?_, ?_, ?_⟩
  · rw [s09_fderiv_ambKernel P Q v hP hQ, hk]
    have h := s09_dc_sq_le P Q v hP hQ
    have hgv := hg v
    have e : (2 / (1 + coshDist P Q)) ^ 2 * hypMetric Q v v -
        (-2 / (1 + coshDist P Q) ^ 2 * fderiv ℝ (coshDist P) Q v) ^ 2 =
        4 / (1 + coshDist P Q) ^ 4 * ((1 + coshDist P Q) ^ 2 * hypMetric Q v v -
          fderiv ℝ (coshDist P) Q v ^ 2) := by
      field_simp
      ring
    rw [← sub_nonneg, e]
    apply mul_nonneg (by positivity)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 + 2 * coshDist P Q) hgv]
  · rw [s09_hypHess_ambKernel P Q v v hP hQ, hk]
    have h := s09_dc_sq_le P Q v hP hQ
    have hgv := hg v
    have hα : 0 ≤ 4 / (1 + coshDist P Q) ^ 3 := div_nonneg (by norm_num) (pow_nonneg hD.le 3)
    rw [abs_le]
    constructor
    · have e : -2 * coshDist P Q / (1 + coshDist P Q) ^ 2 * hypMetric Q v v +
          4 / (1 + coshDist P Q) ^ 3 *
            (fderiv ℝ (coshDist P) Q v * fderiv ℝ (coshDist P) Q v) -
          -(2 / (1 + coshDist P Q) * hypMetric Q v v) =
          2 / (1 + coshDist P Q) ^ 2 * hypMetric Q v v +
            4 / (1 + coshDist P Q) ^ 3 * fderiv ℝ (coshDist P) Q v ^ 2 := by
        field_simp
        ring
      have : 0 ≤ 2 / (1 + coshDist P Q) ^ 2 * hypMetric Q v v +
          4 / (1 + coshDist P Q) ^ 3 * fderiv ℝ (coshDist P) Q v ^ 2 :=
        add_nonneg (mul_nonneg (by positivity) hgv) (mul_nonneg hα (sq_nonneg _))
      linarith
    · have e : 2 / (1 + coshDist P Q) * hypMetric Q v v -
          (-2 * coshDist P Q / (1 + coshDist P Q) ^ 2 * hypMetric Q v v +
            4 / (1 + coshDist P Q) ^ 3 *
              (fderiv ℝ (coshDist P) Q v * fderiv ℝ (coshDist P) Q v)) =
          6 / (1 + coshDist P Q) ^ 2 * hypMetric Q v v +
            4 / (1 + coshDist P Q) ^ 3 *
              ((coshDist P Q ^ 2 - 1) * hypMetric Q v v - fderiv ℝ (coshDist P) Q v ^ 2) := by
        field_simp
        ring
      have : 0 ≤ 6 / (1 + coshDist P Q) ^ 2 * hypMetric Q v v +
            4 / (1 + coshDist P Q) ^ 3 *
              ((coshDist P Q ^ 2 - 1) * hypMetric Q v v - fderiv ℝ (coshDist P) Q v ^ 2) :=
        add_nonneg (mul_nonneg (by positivity) hgv) (mul_nonneg hα (by linarith))
      linarith
  · obtain ⟨g1, g2, g3, hdc, hS⟩ := s09_dc_grad P Q hP hQ
    have hM : ∀ v w : ℂ × ℝ, Q.2 ^ 2 * hypHess (ambKernel P) Q v w =
        -2 * coshDist P Q / (1 + coshDist P Q) ^ 2 * eucInner v w +
          4 / (1 + coshDist P Q) ^ 3 *
            ((Q.2 * fderiv ℝ (coshDist P) Q v) * (Q.2 * fderiv ℝ (coshDist P) Q w)) := by
      intro v w
      rw [s09_hypHess_ambKernel P Q v w hP hQ]
      unfold hypMetric
      field_simp
    have hR : Real.sqrt 3 * ambKernel P Q =
        Real.sqrt (3 * (2 / (1 + coshDist P Q)) ^ 2) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (div_nonneg (by norm_num) hD.le), hk]
    rw [hR]
    apply Real.sqrt_le_sqrt
    simp only [hM, hdc, Fin.sum_univ_three, eucBasis, eucInner, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.zero_re,
      Complex.zero_im]
    refine le_trans (le_of_eq ?_) (s09_hs_bound (coshDist P Q) (Q.2 * g1) (Q.2 * g2)
      (Q.2 * g3) hc1 (by rw [← hS]; ring))
    ring
  · have hs : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    exact mul_le_mul_of_nonneg_right hs hk0

/-- Lemma 9.3(d) `lem:ambient-kernel`, (9.4) `eq:trace-plane` (`sec09-ambient.tex:81`): for a
`g`-orthonormal pair `e₁, e₂` spanning `T ⊂ T_Q ℍ³`,
`tr_T ∇²k = -k² - 2k(1-k) |(∇r)^⊥|² ≤ -k²`, where `|(∇r)^⊥|² = 1 - dr(e₁)² - dr(e₂)²`; at
`Q = P` the trace is `-k(P)² = -1`. -/
theorem lem_ambient_kernel_d (P : ℂ × ℝ) (hP : P ∈ UHS) (Q : ℂ × ℝ) (hQ : Q ∈ UHS)
    (e₁ e₂ : ℂ × ℝ) (h₁ : hypMetric Q e₁ e₁ = 1) (h₂ : hypMetric Q e₂ e₂ = 1)
    (h₁₂ : hypMetric Q e₁ e₂ = 0) :
    (Q ≠ P →
      hypHess (ambKernel P) Q e₁ e₁ + hypHess (ambKernel P) Q e₂ e₂ =
          -ambKernel P Q ^ 2 - 2 * ambKernel P Q * (1 - ambKernel P Q) *
            (1 - fderiv ℝ (hdist P) Q e₁ ^ 2 - fderiv ℝ (hdist P) Q e₂ ^ 2) ∧
        hypHess (ambKernel P) Q e₁ e₁ + hypHess (ambKernel P) Q e₂ e₂ ≤ -ambKernel P Q ^ 2) ∧
      (Q = P →
        hypHess (ambKernel P) Q e₁ e₁ + hypHess (ambKernel P) Q e₂ e₂ = -ambKernel P Q ^ 2) := by
  refine ⟨fun hne => ?_, fun heq => ?_⟩
  · have hb := (lem_ambient_kernel_b P hP).1 Q hQ hne
    have htr : hypHess (ambKernel P) Q e₁ e₁ + hypHess (ambKernel P) Q e₂ e₂ =
        -ambKernel P Q ^ 2 - 2 * ambKernel P Q * (1 - ambKernel P Q) *
          (1 - fderiv ℝ (hdist P) Q e₁ ^ 2 - fderiv ℝ (hdist P) Q e₂ ^ 2) := by
      rw [hb, hb, h₁, h₂]
      ring
    refine ⟨htr, ?_⟩
    rw [htr]
    have hc := s09_one_lt_coshDist P Q hP hQ hne
    have hka := (lem_ambient_kernel_a P hP).2 Q hQ
    have hB := s09_dc_bessel P Q hP hQ e₁ e₂ h₁ h₂ h₁₂
    have hS : 0 < coshDist P Q ^ 2 - 1 := by nlinarith
    have hr : 0 ≤ 1 - fderiv ℝ (hdist P) Q e₁ ^ 2 - fderiv ℝ (hdist P) Q e₂ ^ 2 := by
      rw [s09_fderiv_hdist P Q e₁ hP hQ hne, s09_fderiv_hdist P Q e₂ hP hQ hne, mul_pow, mul_pow,
        inv_pow, Real.sq_sqrt hS.le]
      have : (coshDist P Q ^ 2 - 1)⁻¹ * (fderiv ℝ (coshDist P) Q e₁ ^ 2 +
          fderiv ℝ (coshDist P) Q e₂ ^ 2) ≤ 1 := by
        rw [inv_mul_le_iff₀ hS]
        linarith
      linarith [mul_add (coshDist P Q ^ 2 - 1)⁻¹ (fderiv ℝ (coshDist P) Q e₁ ^ 2)
        (fderiv ℝ (coshDist P) Q e₂ ^ 2)]
    have : 0 ≤ 2 * ambKernel P Q * (1 - ambKernel P Q) *
        (1 - fderiv ℝ (hdist P) Q e₁ ^ 2 - fderiv ℝ (hdist P) Q e₂ ^ 2) :=
      mul_nonneg (mul_nonneg (by linarith [hka.1]) (by linarith [hka.2.1])) hr
    linarith
  · rw [heq] at h₁ h₂ ⊢
    have hb := (lem_ambient_kernel_b P hP).2
    have hk1 : ambKernel P P = 1 := by
      rw [s09_ambKernel_eq_inv P P (by rw [s09_coshDist_self]), s09_coshDist_self]
      norm_num
    rw [hb, hb, h₁, h₂, hk1]
    norm_num

theorem s09_abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  have h1 := Real.cosh_sq x
  have h2 := Real.cosh_pos x
  rw [abs_le]
  constructor <;> nlinarith

theorem s09_cosh_add_le (x t : ℝ) : Real.cosh (x + t) ≤ Real.exp |t| * Real.cosh x := by
  rw [Real.cosh_add]
  have hc := Real.cosh_pos x
  have h1 : Real.sinh x * Real.sinh t ≤ Real.cosh x * |Real.sinh t| := by
    calc Real.sinh x * Real.sinh t ≤ |Real.sinh x * Real.sinh t| := le_abs_self _
      _ = |Real.sinh x| * |Real.sinh t| := abs_mul _ _
      _ ≤ Real.cosh x * |Real.sinh t| :=
          mul_le_mul_of_nonneg_right (s09_abs_sinh_le_cosh x) (abs_nonneg _)
  have h2 : Real.cosh t + |Real.sinh t| = Real.exp |t| := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr ht), abs_of_nonneg ht, Real.cosh_add_sinh]
    · have hs : Real.sinh t ≤ 0 := by
        have := Real.sinh_nonneg_iff.mpr (neg_nonneg.mpr ht)
        rw [Real.sinh_neg] at this
        linarith
      rw [abs_of_nonpos hs, abs_of_nonpos ht, ← sub_eq_add_neg, Real.cosh_sub_sinh]
  calc Real.cosh x * Real.cosh t + Real.sinh x * Real.sinh t
      ≤ Real.cosh x * Real.cosh t + Real.cosh x * |Real.sinh t| := by linarith
    _ = Real.exp |t| * Real.cosh x := by rw [← h2]; ring

theorem s09_kernel_ratio (d1 d2 D : ℝ) (h : |d2 - d1| ≤ D) :
    (Real.cosh (d1 / 2))⁻¹ ^ 2 ≤ Real.exp D * (Real.cosh (d2 / 2))⁻¹ ^ 2 := by
  have hc1 := Real.cosh_pos (d1 / 2)
  have hc2 := Real.cosh_pos (d2 / 2)
  have key := s09_cosh_add_le (d1 / 2) ((d2 - d1) / 2)
  rw [show d1 / 2 + (d2 - d1) / 2 = d2 / 2 by ring] at key
  have habs : |(d2 - d1) / 2| ≤ D / 2 := by
    rw [abs_div, abs_two]
    linarith
  have key2 : Real.cosh (d2 / 2) ≤ Real.exp (D / 2) * Real.cosh (d1 / 2) :=
    le_trans key (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr habs) hc1.le)
  have hE : Real.exp (D / 2) ^ 2 = Real.exp D := by
    rw [sq, ← Real.exp_add, add_halves]
  have key3 : Real.cosh (d2 / 2) ^ 2 ≤ Real.exp D * Real.cosh (d1 / 2) ^ 2 := by
    rw [← hE]
    nlinarith [key2, hc2.le, Real.exp_pos (D / 2)]
  rw [inv_pow, inv_pow, ← div_eq_mul_inv, inv_eq_one_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

theorem s09_kernel_exp_bounds (d : ℝ) (hd : 0 ≤ d) :
    Real.exp (-d) ≤ (Real.cosh (d / 2))⁻¹ ^ 2 ∧
      (Real.cosh (d / 2))⁻¹ ^ 2 ≤ 4 * Real.exp (-d) := by
  have e1 : Real.exp (-d) = (Real.exp (d / 2) ^ 2)⁻¹ := by
    rw [sq, ← Real.exp_add, add_halves, Real.exp_neg]
  rw [e1, Real.cosh_eq, Real.exp_neg]
  have hu : 1 ≤ Real.exp (d / 2) := Real.one_le_exp (by linarith)
  generalize Real.exp (d / 2) = u at hu ⊢
  have hu0 : 0 < u := by linarith
  have hu0' : u ≠ 0 := hu0.ne'
  have h1 : u ^ 2 + 1 ≠ 0 := by positivity
  have e2 : ((u + u⁻¹) / 2)⁻¹ ^ 2 = 4 * u ^ 2 / (u ^ 2 + 1) ^ 2 := by
    field_simp
    ring
  rw [e2]
  have hu2 : 1 ≤ u ^ 2 := by nlinarith
  constructor
  · rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hu2) (by positivity : (0 : ℝ) ≤ 3 * u ^ 2 + 1)]
  · rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg u]

/-- Lemma 9.3(e) `lem:ambient-kernel` (`sec09-ambient.tex:87`): symmetry, the two Lipschitz
bounds for `log k`, and `e^{-d} ≤ k_P(Q) ≤ 4 e^{-d}`. -/
theorem lem_ambient_kernel_e (P Q Q' P' : ℂ × ℝ) (hP : P ∈ UHS) (hQ : Q ∈ UHS)
    (hQ' : Q' ∈ UHS) (hP' : P' ∈ UHS) :
    ambKernel P Q = ambKernel Q P ∧
      ambKernel P Q ≤ Real.exp (hdist Q Q') * ambKernel P Q' ∧
      ambKernel P Q ≤ Real.exp (hdist P P') * ambKernel P' Q ∧
      Real.exp (-hdist P Q) ≤ ambKernel P Q ∧ ambKernel P Q ≤ 4 * Real.exp (-hdist P Q) := by
  have hd : 0 ≤ hdist P Q := Real.arcosh_nonneg (s09_one_le_coshDist P Q hP hQ)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold ambKernel
    rw [s02_hdist_comm]
  · unfold ambKernel
    apply s09_kernel_ratio
    rw [abs_le]
    constructor
    · have := s02_hdist_triangle hP hQ' hQ
      rw [s02_hdist_comm Q' Q] at this
      linarith
    · have := s02_hdist_triangle hP hQ hQ'
      linarith
  · unfold ambKernel
    apply s09_kernel_ratio
    rw [abs_le]
    constructor
    · have := s02_hdist_triangle hP hP' hQ
      linarith
    · have := s02_hdist_triangle hP' hP hQ
      rw [s02_hdist_comm P' P] at this
      linarith
  · unfold ambKernel
    exact (s09_kernel_exp_bounds _ hd).1
  · unfold ambKernel
    exact (s09_kernel_exp_bounds _ hd).2

/-! ## Local area -/

/-- `ρ`-area does not see the complement of `Ω`. -/
theorem s09_hypArea_compl {Ω : Set ℂ} (hΩ : IsOpen Ω) : hypArea Ω Ωᶜ = 0 := by
  unfold hypArea
  rw [withDensity_apply _ hΩ.measurableSet.compl,
    Measure.restrict_restrict hΩ.measurableSet.compl, compl_inter_self, Measure.restrict_empty,
    lintegral_zero_measure]

/-- The `ρ`-area of the image of a closed disc `|z| ≤ t < 1` under a Riemann map:
`area_ρ(f(\bar D_t)) ≤ 4/(1-t²)² · area(\bar D_t)`. -/
theorem s09_la_disc {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {t : ℝ}
    (ht1 : t < 1) :
    hypArea Ω (f '' closedBall 0 t) ≤
      ENNReal.ofReal (4 / (1 - t ^ 2) ^ 2) * volume (closedBall (0 : ℂ) t) := by
  have hsub : closedBall (0 : ℂ) t ⊆ unitDisc := closedBall_subset_ball ht1
  have hDo : IsOpen unitDisc := isOpen_ball
  have hT : MeasurableSet (f '' closedBall 0 t) :=
    ((isCompact_closedBall 0 t).image_of_continuousOn
      (hf.1.continuousOn.mono hsub)).isClosed.measurableSet
  have hTΩ : f '' closedBall 0 t ∩ Ω = f '' closedBall 0 t :=
    inter_eq_left.mpr (hf.2.2 ▸ image_mono hsub)
  have hder : ∀ x ∈ closedBall (0 : ℂ) t, HasFDerivWithinAt f
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f x)).restrictScalars ℝ)
      (closedBall (0 : ℂ) t) x := fun x hx =>
    ((hf.1.differentiableAt (hDo.mem_nhds (hsub hx))).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt
  unfold hypArea
  rw [withDensity_apply _ hT, Measure.restrict_restrict hT, hTΩ,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_closedBall hder
      (hf.2.1.mono hsub)]
  calc ∫⁻ x in closedBall (0 : ℂ) t, ENNReal.ofReal |((ContinuousLinearMap.smulRight
          (1 : ℂ →L[ℂ] ℂ) (deriv f x)).restrictScalars ℝ).det| *
          ENNReal.ofReal (poincareDensity Ω (f x) ^ 2)
      ≤ ∫⁻ _ in closedBall (0 : ℂ) t, ENNReal.ofReal (4 / (1 - t ^ 2) ^ 2) := by
        refine setLIntegral_mono measurable_const ?_
        intro z hz
        rw [s02_pullback_det, abs_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hzt : ‖z‖ ≤ t := mem_closedBall_zero_iff.mp hz
        have hl := eq_lambda_f hf (hsub hz)
        have hu0 : 0 < 1 - t ^ 2 := by nlinarith [norm_nonneg z]
        have hut : 1 - t ^ 2 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
        calc ‖deriv f z‖ ^ 2 * poincareDensity Ω (f z) ^ 2 =
              (poincareDensity Ω (f z) * ‖deriv f z‖) ^ 2 := by ring
          _ = 4 / (1 - ‖z‖ ^ 2) ^ 2 := by rw [hl, div_pow]; norm_num
          _ ≤ 4 / (1 - t ^ 2) ^ 2 := by gcongr
    _ = ENNReal.ofReal (4 / (1 - t ^ 2) ^ 2) * volume (closedBall (0 : ℂ) t) :=
        setLIntegral_const _ _

/-- With `t = (e^R - 1)/(e^R + 1)`: `t/(1-t²) = sinh(R)/2`. -/
theorem s09_la_sinh {R : ℝ} :
    (Real.exp R - 1) / (Real.exp R + 1) / (1 - ((Real.exp R - 1) / (Real.exp R + 1)) ^ 2) =
      Real.sinh R / 2 := by
  have he : 0 < Real.exp R := Real.exp_pos R
  have h1 : 1 - ((Real.exp R - 1) / (Real.exp R + 1)) ^ 2 = 4 * Real.exp R / (Real.exp R + 1) ^ 2 := by
    field_simp
    ring
  rw [h1, Real.sinh_eq, Real.exp_neg]
  field_simp
  ring

/-- One side of Lemma 9.5. -/
theorem s09_la_side (K : ℝ) : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ a : ℝ, 0 < a →
    ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ∀ P ∈ UHS,
      hypArea Ω (epstein Ω ⁻¹' hball P a) ≤
        ENNReal.ofReal (4 * π * Real.sinh (2 * a * A + B) ^ 2) := by
  obtain ⟨A, B, hA, hl⟩ := s03_qi_lower K
  refine ⟨A, max B 0, hA, le_max_right _ _, fun a ha Ω Ωs h P hP => ?_⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 2 * a * A + max B 0 := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; have := le_max_right B 0; positivity
  obtain ⟨t, htd⟩ : ∃ t : ℝ, t = (Real.exp R - 1) / (Real.exp R + 1) := ⟨_, rfl⟩
  have he : 1 ≤ Real.exp R := Real.one_le_exp hR0
  have ht1 : t < 1 := by rw [htd, div_lt_one (by linarith)]; linarith
  have ht0 : 0 ≤ t := by rw [htd]; exact div_nonneg (by linarith) (by linarith)
  have hu0 : 0 < 1 - t ^ 2 := by nlinarith
  -- the disc bound, in closed form
  have hbound : ENNReal.ofReal (4 / (1 - t ^ 2) ^ 2) * volume (closedBall (0 : ℂ) t) ≤
      ENNReal.ofReal (4 * π * Real.sinh (2 * a * A + max B 0) ^ 2) := by
    rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow ht0, ← ENNReal.ofReal_coe_nnreal,
      NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hk : t / (1 - t ^ 2) = Real.sinh R / 2 := by rw [htd]; exact s09_la_sinh
    have hs0 : 0 ≤ Real.sinh R := Real.sinh_nonneg_iff.mpr hR0
    rw [← hR]
    calc 4 / (1 - t ^ 2) ^ 2 * (t ^ 2 * π) = 4 * π * (t / (1 - t ^ 2)) ^ 2 := by
          field_simp
      _ = 4 * π * (Real.sinh R / 2) ^ 2 := by rw [hk]
      _ ≤ 4 * π * Real.sinh R ^ 2 := by
          have : (Real.sinh R / 2) ^ 2 ≤ Real.sinh R ^ 2 := by nlinarith
          have := Real.pi_pos
          nlinarith
  obtain ⟨hΩo, -, -, -⟩ := s03_b0_basic h
  have hc := s09_hypArea_compl hΩo
  by_cases hE : (epstein Ω ⁻¹' hball P a ∩ Ω).Nonempty
  · obtain ⟨w0, hw0E, hw0⟩ := hE
    obtain ⟨f, hf, hf0⟩ := s02_riemannMap_at (s03_b0_jordanPair h) hw0
    have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
    have hsub : epstein Ω ⁻¹' hball P a ⊆ f '' closedBall 0 t ∪ Ωᶜ := by
      intro w hwE
      by_cases hw : w ∈ Ω
      · left
        obtain ⟨z, hz, rfl⟩ : w ∈ f '' unitDisc := by rw [hf.2.2]; exact hw
        refine ⟨z, ?_, rfl⟩
        have hd : hdist (epstein Ω w0) (epstein Ω (f z)) ≤ 2 * a := by
          have tr := s02_hdist_triangle hw0E.1 hP hwE.1
          rw [s02_hdist_comm (epstein Ω w0) P] at tr
          linarith [hw0E.2, hwE.2]
        have hq := hl Ω Ωs h w0 hw0 (f z) hw
        rw [← hf0, subsec_poincare_dist hf h0 hz,
          s05_diskDist_zero (mem_ball_zero_iff.mp hz)] at hq
        have hqR : logRatio ‖z‖ ≤ R := by
          rw [hR]
          rw [← hf0] at hd
          have := le_max_left B 0
          nlinarith [mul_le_mul_of_nonneg_left hd hA]
        rw [mem_closedBall_zero_iff, htd]
        exact s06_lm_radius (mem_ball_zero_iff.mp hz) hqR
      · right; exact hw
    calc hypArea Ω (epstein Ω ⁻¹' hball P a) ≤ hypArea Ω (f '' closedBall 0 t ∪ Ωᶜ) :=
          measure_mono hsub
      _ ≤ hypArea Ω (f '' closedBall 0 t) + hypArea Ω Ωᶜ := measure_union_le _ _
      _ ≤ _ := by rw [hc, add_zero]; exact (s09_la_disc hf ht1).trans hbound
  · have hsub : epstein Ω ⁻¹' hball P a ⊆ Ωᶜ := fun w hw hwΩ => hE ⟨w, hw, hwΩ⟩
    calc hypArea Ω (epstein Ω ⁻¹' hball P a) ≤ hypArea Ω Ωᶜ := measure_mono hsub
      _ = 0 := hc
      _ ≤ _ := bot_le

/-- Lemma 9.5 `lem:local-area` (`sec09-ambient.tex:325`): with the constants `A_K, B_K` of
(3.x) `eq:qi`, the sets `X⁻¹(B(x, a))` and `(X*)⁻¹(B(x, a))` have `ρ`-area, resp. `ρ*`-area,
at most `M_{K,a} = 4π sinh²((2a A_K + B_K)/2)`. -/
theorem lem_local_area :
    ∀ K : ℝ, 1 ≤ K → ∃ A B : ℝ, ∀ a : ℝ, 0 < a → ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
      ∀ x ∈ UHS,
        hypArea Ω (epstein Ω ⁻¹' hball x a) ≤
            ENNReal.ofReal (4 * π * Real.sinh ((2 * a * A + B) / 2) ^ 2) ∧
          hypArea Ωs (epstein Ωs ⁻¹' hball x a) ≤
            ENNReal.ofReal (4 * π * Real.sinh ((2 * a * A + B) / 2) ^ 2) := by
  intro K _
  obtain ⟨A, B, -, -, hside⟩ := s09_la_side K
  -- the crude disc bound `π sinh² R` is absorbed by doubling the constants
  refine ⟨2 * A, 2 * B, fun a ha Ω Ωs h x hx => ?_⟩
  have e : (2 * a * (2 * A) + 2 * B) / 2 = 2 * a * A + B := by ring
  rw [e]
  exact ⟨hside a ha Ω Ωs h x hx, hside a ha Ωs Ω (s03_qce_swap h) x hx⟩

/-- Helper for `s09_amb_upper`, Lemma 9.6 `lem:net-ambient` (`sec09-ambient.tex:342`): for the
`1`-net `S = {Bᵢ}` of the bad set `𝔅` of §5, `∑ᵢ k_P(Bᵢ) ≤ C(K) H(P)`.  As in `lem_counting`, with the
ambient kernel (Lemma 9.3(e)) in place of the intrinsic one; no label is needed (the labels `ℓ`, `lab`
only enter through `IsBadNet`), and the paper's hypothesis `𝔅 ≠ ∅` is dropped (for `S = ∅` the sum
is `0`). -/
theorem s09_au_net : ∀ K : ℝ, 1 ≤ K → ∀ η R : ℝ, 0 < η → η < 1 / 4 → 0 < R →
    ∃ C : ℝ≥0, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ (lab : ℂ × ℝ → ℂ) (S : Set (ℂ × ℝ)) (ℓ : ℂ × ℝ → ℂ), IsBadNet Ω Ωs lab η R S ℓ →
        ∀ P ∈ UHS, ∑' b : S, ENNReal.ofReal (ambKernel P b) ≤ (C : ℝ≥0∞) * ambH Ω Ωs P := by
  intro K _ η R hη hη1 hR
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = η ^ 2 * π * (3 * η / 16) ^ 2 / 16 := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = 23328 * Real.cosh (R + 4 + 1 / 3) ^ 6 := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; positivity
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  refine ⟨Real.toNNReal (N * Real.exp (R + 4) / m), ?_⟩
  intro Ω Ωs h hnl lab S ℓ hS P hP
  have hJ := s03_b0_jordanPair h
  have hJs := s03_b0_jordanPair (s03_qce_swap h)
  have hΩ := s02_jordanPair_riemannMap hJ
  have hΩs := s02_jordanPair_riemannMap hJs
  have hXU : ∀ w ∈ Ω, epstein Ω w ∈ UHS := fun w hw => s09_epstein_pos Ω hΩ w hw
  have hXsU : ∀ z ∈ Ωs, epstein Ωs z ∈ UHS := fun z hz => s09_epstein_pos Ωs hΩs z hz
  have hSU : S ⊆ UHS := by
    intro b hb
    rcases (hS.1 hb).1 with ⟨w, hw, rfl⟩ | ⟨z, hz, rfl⟩
    · exact hXU w hw
    · exact hXsU z hz
  have hup := s03_qi_upper K Ω Ωs h hnl
  have hk0 : ∀ Q, 0 ≤ ambKernel P Q := fun Q => sq_nonneg _
  -- Lemma 9.3(e): `e^{-(R+4)} k_P(b) ≤ k_P(Q)` when `d(Q, b) ≤ R + 4`
  have hkt : ∀ b Q, b ∈ UHS → Q ∈ UHS → hdist Q b ≤ R + 4 →
      ENNReal.ofReal (Real.exp (-(R + 4)) * ambKernel P b) ≤ ENNReal.ofReal (ambKernel P Q) := by
    intro b Q hb hQ hd
    refine ENNReal.ofReal_le_ofReal ?_
    have hl := (lem_ambient_kernel_e P b Q P hP hb hQ hP).2.1
    have he : Real.exp (hdist b Q) ≤ Real.exp (R + 4) :=
      Real.exp_le_exp.mpr (by rw [s02_hdist_comm]; exact hd)
    calc Real.exp (-(R + 4)) * ambKernel P b
        ≤ Real.exp (-(R + 4)) * (Real.exp (R + 4) * ambKernel P Q) :=
          mul_le_mul_of_nonneg_left (hl.trans (mul_le_mul_of_nonneg_right he (hk0 _)))
            (Real.exp_pos _).le
      _ = ambKernel P Q := by rw [← mul_assoc, ← Real.exp_add]; simp
  have hconst : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x =
      ENNReal.ofReal (Real.exp (R + 4) / m) *
        (ENNReal.ofReal (Real.exp (-(R + 4)) * x) * ENNReal.ofReal m) := by
    intro x hx
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.exp_neg]
    field_simp
  -- one net point `b`: the sets `P_b ⊆ Ω`, `P*_b ⊆ Ω*` of the paper (one of them empty)
  have hb : ∀ b ∈ S, ∃ Pw Pz : Set ℂ,
      ENNReal.ofReal (ambKernel P b) ≤ ENNReal.ofReal (Real.exp (R + 4) / m) *
        ((∫⁻ w, Pw.indicator (fun w => ENNReal.ofReal (ambKernel P (epstein Ω w))) w ∂curvMass Ω) +
          ∫⁻ z, Pz.indicator (fun z => ENNReal.ofReal (ambKernel P (epstein Ωs z))) z
            ∂curvMass Ωs) ∧
      (∀ w ∈ Pw, w ∈ Ω ∧ hdist (epstein Ω w) b ≤ R + 4) ∧
      (∀ z ∈ Pz, z ∈ Ωs ∧ hdist (epstein Ωs z) b ≤ R + 4) := by
    intro b hbS
    have hbU := hSU hbS
    obtain ⟨a, ha, hba⟩ := s05_ct_near_A hR.le (hS.1 hbS)
    rcases ha with ⟨z, hz, hsz, rfl⟩ | ⟨z, hz, hsz, rfl⟩
    · have hdw : ∀ w ∈ Ω, poincareDist Ω z w < 3 * η / 16 →
          hdist (epstein Ω w) b ≤ R + 4 := by
        intro w hw hd
        have t := s02_hdist_triangle (hXU w hw) (hXU z hz) hbU
        have h1 := hup.1 w hw z hz
        rw [s02_poincareDist_comm hΩ hw hz] at h1
        rw [s02_hdist_comm (epstein Ω z) b] at t
        linarith
      have hmass := s05_ct_mass_lower hJ hz hη hη1 hsz
        (g := fun w => ENNReal.ofReal (ambKernel P (epstein Ω w)))
        (a := ENNReal.ofReal (Real.exp (-(R + 4)) * ambKernel P b))
        (fun w hw hd => hkt b (epstein Ω w) hbU (hXU w hw) (hdw w hw hd))
      rw [← hm] at hmass
      refine ⟨{w | w ∈ Ω ∧ poincareDist Ω z w < 3 * η / 16}, ∅, ?_,
        fun w hw => ⟨hw.1, hdw w hw.1 hw.2⟩, fun _ h => absurd h (notMem_empty _)⟩
      calc ENNReal.ofReal (ambKernel P b)
          = ENNReal.ofReal (Real.exp (R + 4) / m) *
              (ENNReal.ofReal (Real.exp (-(R + 4)) * ambKernel P b) * ENNReal.ofReal m) :=
            hconst _ (hk0 _)
        _ ≤ ENNReal.ofReal (Real.exp (R + 4) / m) *
              ∫⁻ w, {w | w ∈ Ω ∧ poincareDist Ω z w < 3 * η / 16}.indicator
                (fun w => ENNReal.ofReal (ambKernel P (epstein Ω w))) w ∂curvMass Ω :=
            mul_le_mul' le_rfl hmass
        _ ≤ _ := mul_le_mul' le_rfl le_self_add
    · have hdz : ∀ z' ∈ Ωs, poincareDist Ωs z z' < 3 * η / 16 →
          hdist (epstein Ωs z') b ≤ R + 4 := by
        intro z' hz' hd
        have t := s02_hdist_triangle (hXsU z' hz') (hXsU z hz) hbU
        have h1 := hup.2 z' hz' z hz
        rw [s02_poincareDist_comm hΩs hz' hz] at h1
        rw [s02_hdist_comm (epstein Ωs z) b] at t
        linarith
      have hmass := s05_ct_mass_lower hJs hz hη hη1 hsz
        (g := fun z' => ENNReal.ofReal (ambKernel P (epstein Ωs z')))
        (a := ENNReal.ofReal (Real.exp (-(R + 4)) * ambKernel P b))
        (fun z' hz' hd => hkt b (epstein Ωs z') hbU (hXsU z' hz') (hdz z' hz' hd))
      rw [← hm] at hmass
      refine ⟨∅, {z' | z' ∈ Ωs ∧ poincareDist Ωs z z' < 3 * η / 16}, ?_,
        fun _ h => absurd h (notMem_empty _), fun z' hz' => ⟨hz'.1, hdz z' hz'.1 hz'.2⟩⟩
      calc ENNReal.ofReal (ambKernel P b)
          = ENNReal.ofReal (Real.exp (R + 4) / m) *
              (ENNReal.ofReal (Real.exp (-(R + 4)) * ambKernel P b) * ENNReal.ofReal m) :=
            hconst _ (hk0 _)
        _ ≤ ENNReal.ofReal (Real.exp (R + 4) / m) *
              ∫⁻ z', {z' | z' ∈ Ωs ∧ poincareDist Ωs z z' < 3 * η / 16}.indicator
                (fun z => ENNReal.ofReal (ambKernel P (epstein Ωs z))) z' ∂curvMass Ωs :=
            mul_le_mul' le_rfl hmass
        _ ≤ _ := mul_le_mul' le_rfl le_add_self
  choose! Pw Pz hPk hPw hPz using hb
  -- multiplicity (packing in `ℍ³`, `s05_pk_tsum_le`)
  have hI : ∀ w, ∑' b : S, (Pw b).indicator (fun w => ENNReal.ofReal (ambKernel P (epstein Ω w))) w ≤
      ENNReal.ofReal N * ENNReal.ofReal (ambKernel P (epstein Ω w)) := by
    intro w
    by_cases hw : w ∈ Ω
    · rw [hN]
      exact s05_pk_tsum_le hSU hS.2.1 (hXU w hw) (R + 4) Pw _ w
        (fun b hb hwb => (hPw b hb w hwb).2)
    · have h0 : ∀ b : S,
          (Pw b).indicator (fun w => ENNReal.ofReal (ambKernel P (epstein Ω w))) w = 0 :=
        fun b => indicator_of_notMem (fun h' => hw (hPw b b.2 w h').1) _
      simp only [h0, tsum_zero, zero_le]
  have hJ' : ∀ z, ∑' b : S, (Pz b).indicator
      (fun z => ENNReal.ofReal (ambKernel P (epstein Ωs z))) z ≤
      ENNReal.ofReal N * ENNReal.ofReal (ambKernel P (epstein Ωs z)) := by
    intro z
    by_cases hz : z ∈ Ωs
    · rw [hN]
      exact s05_pk_tsum_le hSU hS.2.1 (hXsU z hz) (R + 4) Pz _ z
        (fun b hb hzb => (hPz b hb z hzb).2)
    · have h0 : ∀ b : S,
          (Pz b).indicator (fun z => ENNReal.ofReal (ambKernel P (epstein Ωs z))) z = 0 :=
        fun b => indicator_of_notMem (fun h' => hz (hPz b b.2 z h').1) _
      simp only [h0, tsum_zero, zero_le]
  -- summing over the net (Tonelli without measurability, `s05_ct_tsum_lintegral_le`)
  show _ ≤ ENNReal.ofReal (N * Real.exp (R + 4) / m) *
    ((∫⁻ w, ENNReal.ofReal (ambKernel P (epstein Ω w)) ∂curvMass Ω) +
      ∫⁻ z, ENNReal.ofReal (ambKernel P (epstein Ωs z)) ∂curvMass Ωs)
  calc ∑' b : S, ENNReal.ofReal (ambKernel P b)
      ≤ ∑' b : S, ENNReal.ofReal (Real.exp (R + 4) / m) *
          ((∫⁻ w, (Pw b).indicator
              (fun w => ENNReal.ofReal (ambKernel P (epstein Ω w))) w ∂curvMass Ω) +
            ∫⁻ z, (Pz b).indicator
              (fun z => ENNReal.ofReal (ambKernel P (epstein Ωs z))) z ∂curvMass Ωs) :=
        tsum_le_tsum fun b => hPk b b.2
    _ = ENNReal.ofReal (Real.exp (R + 4) / m) *
          ((∑' b : S, ∫⁻ w, (Pw b).indicator
              (fun w => ENNReal.ofReal (ambKernel P (epstein Ω w))) w ∂curvMass Ω) +
            ∑' b : S, ∫⁻ z, (Pz b).indicator
              (fun z => ENNReal.ofReal (ambKernel P (epstein Ωs z))) z ∂curvMass Ωs) := by
        rw [ENNReal.tsum_mul_left, tsum_add]
    _ ≤ ENNReal.ofReal (Real.exp (R + 4) / m) *
          ((∫⁻ w, ENNReal.ofReal N * ENNReal.ofReal (ambKernel P (epstein Ω w)) ∂curvMass Ω) +
            ∫⁻ z, ENNReal.ofReal N * ENNReal.ofReal (ambKernel P (epstein Ωs z)) ∂curvMass Ωs) := by
        gcongr
        · exact (s05_ct_tsum_lintegral_le _ _).trans (lintegral_mono hI)
        · exact (s05_ct_tsum_lintegral_le _ _).trans (lintegral_mono hJ')
    _ = ENNReal.ofReal (N * Real.exp (R + 4) / m) *
          ((∫⁻ w, ENNReal.ofReal (ambKernel P (epstein Ω w)) ∂curvMass Ω) +
            ∫⁻ z, ENNReal.ofReal (ambKernel P (epstein Ωs z)) ∂curvMass Ωs) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_add, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

/-- Helper for `lem_model_lower_b`: in dimension 2 the trace of the Christoffel term vanishes
(`Γ(1,1) + Γ(i,i) = 0`), so `Δ_ρ u = λ⁻² Δu` with `Δ` the Euclidean Laplacian. -/
theorem s10_mlb_rhoLap (Ω : Set ℂ) {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ 2 u U) {w : ℂ} (hw : w ∈ U) :
    rhoLaplacian Ω u w = Laplacian.laplacian u w / poincareDensity Ω w ^ 2 := by
  have hc := hu.contDiffAt (hU.mem_nhds hw)
  have hd : DifferentiableAt ℝ (fderiv ℝ u) w := (s05_D2_sub hc hc 0).1
  have hΓ : rhoChristoffel Ω w (frameVec 0) (frameVec 0) +
      rhoChristoffel Ω w (frameVec 1) (frameVec 1) = 0 := by
    unfold rhoChristoffel frameVec
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hl := (fderiv ℝ u w).map_add (rhoChristoffel Ω w (frameVec 0) (frameVec 0))
    (rhoChristoffel Ω w (frameVec 1) (frameVec 1))
  rw [hΓ, map_zero] at hl
  unfold rhoLaplacian
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  beta_reduce
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  simp only [Fin.sum_univ_two, s05_hess_D2 hd, Matrix.cons_val_zero, Matrix.cons_val_one]
  have e0 : frameVec 0 = 1 := rfl
  have e1 : frameVec 1 = I := rfl
  rw [e0, e1] at hl ⊢
  congr 1
  linarith

/-- Helper (W1a) for `lem:ambient-adjoint`: the Euclidean Laplacian of `k ∘ X`, `X : ℂ → ℍ³`,
in half-space coordinates: `Δ(k∘X) = Σ_e ∇²k(dX e, dX e) + dk(N)`, `e ∈ {1, i}`, with
`N = Σ_e (D²X(e, e) + Γ(dX e, dX e))` the (Euclidean-frame) tension field. No `ξ ≠ 0` is needed. -/
theorem s09_au_chain {k : ℂ × ℝ → ℝ} {X : ℂ → ℂ × ℝ} {w : ℂ} (hk : ContDiffAt ℝ 2 k (X w))
    (hX : ContDiffAt ℝ 2 X w) :
    Laplacian.laplacian (fun x => k (X x)) w =
      hypHess k (X w) (fderiv ℝ X w 1) (fderiv ℝ X w 1) +
        hypHess k (X w) (fderiv ℝ X w I) (fderiv ℝ X w I) +
        fderiv ℝ k (X w) (fderiv ℝ (fderiv ℝ X) w 1 1 + fderiv ℝ (fderiv ℝ X) w I I +
          hypChristoffel (X w) (fderiv ℝ X w 1) (fderiv ℝ X w 1) +
          hypChristoffel (X w) (fderiv ℝ X w I) (fderiv ℝ X w I)) := by
  -- first derivatives near `w`
  have hkd : DifferentiableAt ℝ (fderiv ℝ k) (X w) :=
    (hk.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hXd : DifferentiableAt ℝ (fderiv ℝ X) w :=
    (hX.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hev : fderiv ℝ (fun x => k (X x)) =ᶠ[𝓝 w]
      fun x => (fderiv ℝ k (X x)).comp (fderiv ℝ X x) := by
    filter_upwards [hX.eventually (by decide), hX.continuousAt.eventually (hk.eventually (by decide))] with x hx hkx
    exact fderiv_comp x (hkx.differentiableAt (by norm_num)) (hx.differentiableAt (by norm_num))
  have hc : HasFDerivAt (fun x => fderiv ℝ k (X x))
      ((fderiv ℝ (fderiv ℝ k) (X w)).comp (fderiv ℝ X w)) w :=
    hkd.hasFDerivAt.comp w (hX.differentiableAt (by norm_num)).hasFDerivAt
  have hD := (hc.clm_comp hXd.hasFDerivAt).fderiv
  -- the second derivative of `k ∘ X` along `v`
  have hsec : ∀ v : ℂ, fderiv ℝ (fderiv ℝ (fun x => k (X x))) w v v =
      fderiv ℝ (fderiv ℝ k) (X w) (fderiv ℝ X w v) (fderiv ℝ X w v) +
        fderiv ℝ k (X w) (fderiv ℝ (fderiv ℝ X) w v v) := by
    intro v
    rw [hev.fderiv_eq, hD]
    simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
    ring
  -- `∇²k(v, v) + dk(Γ(v, v)) = D²k(v, v)`
  have hH : ∀ v : ℂ × ℝ, fderiv ℝ (fderiv ℝ k) (X w) v v =
      hypHess k (X w) v v + fderiv ℝ k (X w) (hypChristoffel (X w) v v) := by
    intro v
    unfold hypHess hypChristoffel eucInner
    simp only [map_add, map_smul, smul_eq_mul, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    simp only [div_eq_mul_inv]
    ring
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  beta_reduce
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hsec 1, hsec I, hH, hH, map_add, map_add, map_add]
  ring

/-- Helper (W1a) for `lem:ambient-adjoint` (b): `|dk_P(ν)| ≤ k_P` at `X(w)` (`g(ν, ν) = 1`,
`lem_shape_a` at `τ = 0`, and `lem_ambient_kernel_c`). -/
theorem s09_au_normal {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {P : ℂ × ℝ} (hP : P ∈ UHS)
    {w : ℂ} (hw : w ∈ Ω) (hs : schwarzNorm Ω w ≠ 1) :
    |fderiv ℝ (ambKernel P) (epstein Ω w) (normalVec Ω w)| ≤ ambKernel P (epstein Ω w) := by
  obtain ⟨f, hf, -⟩ := s02_riemannMap_at hJ hw
  have hnb := lem_normal_b ⟨f, hf⟩ hw
  have hQ : epstein Ω w ∈ UHS := by
    have := hnb.1 0
    rwa [hnb.2.2] at this
  have hg := (lem_shape_a Ω Ωs hJ w hw hs 0).1
  rw [hnb.2.2] at hg
  -- `g(ν, ν) = 1`
  have hg' : hypMetric (epstein Ω w) (normalVec Ω w) (normalVec Ω w) = 1 := by
    rw [← hg]
    unfold hypMetric eucInner hypInner normalVec
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have h1 := (lem_ambient_kernel_c P hP _ hQ).1 (normalVec Ω w)
  rw [hg', mul_one] at h1
  have hk := ((lem_ambient_kernel_a P hP).2 _ hQ).1
  have h2 := sq_le_sq.mp h1
  rwa [abs_of_pos hk] at h2

/-- Helper (W1a) for `lem:ambient-adjoint` (b): the trace of `∇²k_P` over a nearly conformal pair
`a, b` (Gram matrix `l² (Id + O(s))`) is at most `l² (−k² + 64 s k)` (Gram–Schmidt,
`lem_ambient_kernel_d` for the orthonormal pair, `lem_ambient_kernel_c` for the error). -/
theorem s09_au_trace {P Q a b : ℂ × ℝ} (hP : P ∈ UHS) (hQ : Q ∈ UHS) {l s : ℝ} (hl : 0 < l)
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 4) (haa : |hypMetric Q a a - l ^ 2| ≤ 3 * s * l ^ 2)
    (hbb : |hypMetric Q b b - l ^ 2| ≤ 3 * s * l ^ 2) (hab : |hypMetric Q a b| ≤ 2 * s * l ^ 2) :
    hypHess (ambKernel P) Q a a + hypHess (ambKernel P) Q b b ≤
      l ^ 2 * (-ambKernel P Q ^ 2 + 64 * s * ambKernel P Q) := by
  obtain ⟨hk0, hk1, -⟩ := (lem_ambient_kernel_a P hP).2 Q hQ
  have hHv := (lem_ambient_kernel_c P hP Q hQ).2.1
  have hl2 : 0 < l ^ 2 := by positivity
  -- bilinearity of `g_Q` and `∇²k_P` on `span(a, b)`
  have hgb : ∀ p q r t : ℝ, hypMetric Q (p • a + q • b) (r • a + t • b) =
      p * r * hypMetric Q a a + (p * t + q * r) * hypMetric Q a b + q * t * hypMetric Q b b := by
    intro p q r t
    unfold hypMetric eucInner
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Complex.add_re,
      Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring
  have hHb : ∀ p q r t : ℝ, hypHess (ambKernel P) Q (p • a + q • b) (r • a + t • b) =
      p * r * hypHess (ambKernel P) Q a a + p * t * hypHess (ambKernel P) Q a b +
        q * r * hypHess (ambKernel P) Q b a + q * t * hypHess (ambKernel P) Q b b := by
    intro p q r t
    unfold hypHess eucInner
    simp only [map_add, map_smul, add_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Complex.add_re,
      Complex.add_im, Complex.smul_re, Complex.smul_im]
    ring
  rw [abs_le] at haa hbb hab
  rcases lt_or_ge s (1 / 16) with hs16 | hs16
  swap
  · -- `s ≥ 1/16`: the trivial bound `∇²k(v, v) ≤ k g(v, v)` suffices
    have h1 := (abs_le.mp (hHv a)).2
    have h2 := (abs_le.mp (hHv b)).2
    linarith [mul_le_mul_of_nonneg_left haa.2 hk0.le, mul_le_mul_of_nonneg_left hbb.2 hk0.le,
      mul_nonneg (mul_nonneg hl2.le hk0.le) (by linarith : (0 : ℝ) ≤ 58 * s - 3),
      mul_nonneg (mul_nonneg hl2.le hk0.le) (by linarith : (0 : ℝ) ≤ 1 - ambKernel P Q)]
  obtain ⟨A, hA⟩ : ∃ A, hypMetric Q a a = A := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, hypMetric Q b b = B := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, hypMetric Q a b = G := ⟨_, rfl⟩
  rw [hA] at haa
  rw [hB] at hbb
  rw [hG] at hab
  have hAl : 13 / 16 * l ^ 2 ≤ A := by nlinarith
  have hBl : 13 / 16 * l ^ 2 ≤ B := by nlinarith
  have hBu : B ≤ 19 / 16 * l ^ 2 := by nlinarith
  have hApos : 0 < A := by linarith
  have hGabs : |G| ≤ 2 * s * l ^ 2 := abs_le.mpr hab
  -- Gram–Schmidt: `e₁ = c₁ a`, `e₂ = c₂ (b − t a)`
  obtain ⟨t, htA⟩ : ∃ t : ℝ, t * A = G := ⟨G / A, div_mul_cancel₀ G hApos.ne'⟩
  have htGA : |t| * A = |G| := by rw [← abs_of_pos hApos, ← abs_mul, htA]
  have hT : |t| * 13 ≤ 32 * s := by
    have h2 : |t| * (13 / 16 * l ^ 2) ≤ |t| * A := mul_le_mul_of_nonneg_left hAl (abs_nonneg t)
    nlinarith
  have htG0 : 0 ≤ t * G := by rw [← htA]; nlinarith [sq_nonneg t]
  have htG : t * G ≤ 4 / 13 * s * l ^ 2 := by
    have h2 : t * G ≤ |t| * |G| := by rw [← abs_mul]; exact le_abs_self _
    have h3 : |t| * |G| ≤ 32 * s / 13 * (2 * s * l ^ 2) :=
      mul_le_mul (by linarith) hGabs (abs_nonneg G) (by positivity)
    nlinarith [mul_nonneg (mul_nonneg hs0 hl2.le) (by linarith : (0 : ℝ) ≤ 1 / 16 - s)]
  have htAB : |t| * (A + B) ≤ 2 * s * l ^ 2 + 38 / 13 * s * l ^ 2 := by
    have h2 : |t| * B ≤ |t| * (19 / 16 * l ^ 2) := mul_le_mul_of_nonneg_left hBu (abs_nonneg t)
    have h3 : |t| * (19 / 16 * l ^ 2) ≤ 32 * s / 13 * (19 / 16 * l ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    rw [mul_add, htGA]
    linarith
  have hU : 0 < B - t * G := by nlinarith
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℝ, c ^ 2 * A = 1 :=
    ⟨(Real.sqrt A)⁻¹, by rw [inv_pow, Real.sq_sqrt hApos.le, inv_mul_cancel₀ hApos.ne']⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c : ℝ, c ^ 2 * (B - t * G) = 1 :=
    ⟨(Real.sqrt (B - t * G))⁻¹, by rw [inv_pow, Real.sq_sqrt hU.le, inv_mul_cancel₀ hU.ne']⟩
  have h11 : hypMetric Q (c₁ • a + (0 : ℝ) • b) (c₁ • a + (0 : ℝ) • b) = 1 := by
    rw [hgb, hA, hG, hB]
    linear_combination hc₁
  have h22 : hypMetric Q ((-(c₂ * t)) • a + c₂ • b) ((-(c₂ * t)) • a + c₂ • b) = 1 := by
    rw [hgb, hA, hG, hB]
    linear_combination hc₂ + c₂ ^ 2 * t * htA
  have h12 : hypMetric Q (c₁ • a + (0 : ℝ) • b) ((-(c₂ * t)) • a + c₂ • b) = 0 := by
    rw [hgb, hA, hG, hB]
    linear_combination (-(c₁ * c₂)) * htA
  have kd := lem_ambient_kernel_d P hP Q hQ _ _ h11 h22 h12
  have htr : hypHess (ambKernel P) Q (c₁ • a + (0 : ℝ) • b) (c₁ • a + (0 : ℝ) • b) +
      hypHess (ambKernel P) Q ((-(c₂ * t)) • a + c₂ • b) ((-(c₂ * t)) • a + c₂ • b) ≤
        -ambKernel P Q ^ 2 := by
    by_cases hQP : Q = P
    · exact (kd.2 hQP).le
    · exact (kd.1 hQP).2
  have hx := hHv (c₁ • a + (0 : ℝ) • b)
  have hy := hHv ((-(c₂ * t)) • a + c₂ • b)
  rw [h11, mul_one] at hx
  rw [h22, mul_one] at hy
  rw [hHb] at hx hy
  rw [hHb, hHb] at htr
  -- `|∇²k(a, b) + ∇²k(b, a)| ≤ k (g(a, a) + g(b, b))` by polarization
  have hM : |hypHess (ambKernel P) Q a b + hypHess (ambKernel P) Q b a| ≤
      ambKernel P Q * (A + B) := by
    have hp := hHv ((1 : ℝ) • a + (1 : ℝ) • b)
    have hm := hHv ((1 : ℝ) • a + (-1 : ℝ) • b)
    rw [hHb, hgb, hA, hB, hG] at hp hm
    rw [abs_le] at hp hm ⊢
    constructor <;> linarith [hp.1, hp.2, hm.1, hm.2]
  -- `x = ∇²k(e₁, e₁)`, `y = ∇²k(e₂, e₂)`
  obtain ⟨x, hxd⟩ : ∃ x, c₁ * c₁ * hypHess (ambKernel P) Q a a +
      c₁ * 0 * hypHess (ambKernel P) Q a b + 0 * c₁ * hypHess (ambKernel P) Q b a +
        0 * 0 * hypHess (ambKernel P) Q b b = x := ⟨_, rfl⟩
  obtain ⟨y, hyd⟩ : ∃ y, -(c₂ * t) * -(c₂ * t) * hypHess (ambKernel P) Q a a +
      -(c₂ * t) * c₂ * hypHess (ambKernel P) Q a b + c₂ * -(c₂ * t) * hypHess (ambKernel P) Q b a +
        c₂ * c₂ * hypHess (ambKernel P) Q b b = y := ⟨_, rfl⟩
  rw [hxd, hyd] at htr
  rw [hxd] at hx
  rw [hyd] at hy
  have hAx : hypHess (ambKernel P) Q a a = A * x := by
    rw [← hxd]
    linear_combination (-hypHess (ambKernel P) Q a a) * hc₁
  have hUy : t ^ 2 * hypHess (ambKernel P) Q a a -
      t * (hypHess (ambKernel P) Q a b + hypHess (ambKernel P) Q b a) +
        hypHess (ambKernel P) Q b b = (B - t * G) * y := by
    rw [← hyd]
    linear_combination (-(t ^ 2 * hypHess (ambKernel P) Q a a -
      t * (hypHess (ambKernel P) Q a b + hypHess (ambKernel P) Q b a) +
        hypHess (ambKernel P) Q b b)) * hc₂
  -- the trace, `S = l² (x + y) + (A − l²) x + (U − l²) y + t M − t² A x`
  have hS : hypHess (ambKernel P) Q a a + hypHess (ambKernel P) Q b b =
      l ^ 2 * (x + y) + (A - l ^ 2) * x + (B - t * G - l ^ 2) * y +
        t * (hypHess (ambKernel P) Q a b + hypHess (ambKernel P) Q b a) - t ^ 2 * A * x := by
    linear_combination hUy + (1 - t ^ 2) * hAx
  have hxa := abs_le.mp hx
  have e1 : l ^ 2 * (x + y) ≤ l ^ 2 * -ambKernel P Q ^ 2 := mul_le_mul_of_nonneg_left htr hl2.le
  have e2 : (A - l ^ 2) * x ≤ |A - l ^ 2| * ambKernel P Q := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  have e3 : (B - t * G - l ^ 2) * y ≤ |B - t * G - l ^ 2| * ambKernel P Q := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
  have e4 : t * (hypHess (ambKernel P) Q a b + hypHess (ambKernel P) Q b a) ≤
      |t| * (ambKernel P Q * (A + B)) := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hM (abs_nonneg _)
  have e5 : -(t ^ 2 * A * x) ≤ t * G * ambKernel P Q := by
    have h' : t ^ 2 * A = t * G := by rw [← htA]; ring
    have h := mul_le_mul_of_nonneg_left (neg_le.mpr hxa.1) (mul_nonneg (sq_nonneg t) hApos.le)
    rw [h'] at h ⊢
    linarith
  have hA' : |A - l ^ 2| ≤ 3 * s * l ^ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hU' : |B - t * G - l ^ 2| ≤ 3 * s * l ^ 2 + 4 / 13 * s * l ^ 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have f1 := mul_le_mul_of_nonneg_right hA' hk0.le
  have f2 := mul_le_mul_of_nonneg_right hU' hk0.le
  have f3 := mul_le_mul_of_nonneg_left htAB hk0.le
  have f4 := mul_le_mul_of_nonneg_right htG hk0.le
  have f5 : 0 ≤ s * l ^ 2 * ambKernel P Q := by positivity
  rw [hS]
  linarith

/-! Helpers (W1a) for `s09_au_tension`: Wirtinger data `dF(v) = a v + b v̄` (`a = ∂F`, `b = ∂̄F`)
and its closure under the field operations, `conj`, `re` and holomorphic maps. -/

theorem s09_au_wd_const (c x : ℂ) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun _ : ℂ => c) L x ∧ ∀ v, L v = 0 * v + 0 * conj v :=
  ⟨0, hasFDerivAt_const c x, fun v => by simp⟩

theorem s09_au_wd_id (x : ℂ) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun y : ℂ => y) L x ∧ ∀ v, L v = 1 * v + 0 * conj v :=
  ⟨ContinuousLinearMap.id ℝ ℂ, hasFDerivAt_id x, fun v => by simp⟩

theorem s09_au_wd_add {F G : ℂ → ℂ} {x a b c d : ℂ}
    (hF : ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt F L x ∧ ∀ v, L v = a * v + b * conj v)
    (hG : ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt G L x ∧ ∀ v, L v = c * v + d * conj v) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun y => F y + G y) L x ∧
      ∀ v, L v = (a + c) * v + (b + d) * conj v := by
  obtain ⟨L, hL, hLv⟩ := hF
  obtain ⟨M, hM, hMv⟩ := hG
  exact ⟨L + M, hL.add hM, fun v => by rw [add_apply, hLv, hMv]; ring⟩

theorem s09_au_wd_sub {F G : ℂ → ℂ} {x a b c d : ℂ}
    (hF : ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt F L x ∧ ∀ v, L v = a * v + b * conj v)
    (hG : ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt G L x ∧ ∀ v, L v = c * v + d * conj v) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun y => F y - G y) L x ∧
      ∀ v, L v = (a - c) * v + (b - d) * conj v := by
  obtain ⟨L, hL, hLv⟩ := hF
  obtain ⟨M, hM, hMv⟩ := hG
  exact ⟨L - M, hL.sub hM, fun v => by rw [sub_apply, hLv, hMv]; ring⟩

theorem s09_au_wd_mul {F G : ℂ → ℂ} {x a b c d : ℂ}
    (hF : ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt F L x ∧ ∀ v, L v = a * v + b * conj v)
    (hG : ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt G L x ∧ ∀ v, L v = c * v + d * conj v) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun y => F y * G y) L x ∧
      ∀ v, L v = (a * G x + F x * c) * v + (b * G x + F x * d) * conj v := by
  obtain ⟨L, hL, hLv⟩ := hF
  obtain ⟨M, hM, hMv⟩ := hG
  refine ⟨_, hL.mul hM, fun v => ?_⟩
  rw [add_apply, smul_apply, smul_apply, hLv, hMv,
    smul_eq_mul, smul_eq_mul]
  ring

theorem s09_au_wd_inv {F : ℂ → ℂ} {x a b : ℂ}
    (hF : ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt F L x ∧ ∀ v, L v = a * v + b * conj v) (hx : F x ≠ 0) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun y => (F y)⁻¹) L x ∧
      ∀ v, L v = (-a / F x ^ 2) * v + (-b / F x ^ 2) * conj v := by
  obtain ⟨L, hL, hLv⟩ := hF
  have h := ((hasDerivAt_inv hx).hasFDerivAt.restrictScalars ℝ).comp x hL
  refine ⟨_, h, fun v => ?_⟩
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, hLv]
  field_simp
  ring

theorem s09_au_wd_conj {F : ℂ → ℂ} {x a b : ℂ}
    (hF : ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt F L x ∧ ∀ v, L v = a * v + b * conj v) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun y => conj (F y)) L x ∧
      ∀ v, L v = conj b * v + conj a * conj v := by
  obtain ⟨L, hL, hLv⟩ := hF
  refine ⟨_, (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt.comp x hL, fun v => ?_⟩
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply,
    Complex.conjCLE_apply, hLv, map_add, map_mul, Complex.conj_conj]
  ring

theorem s09_au_wd_holo {F : ℂ → ℂ} {x : ℂ} (hF : DifferentiableAt ℂ F x) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt F L x ∧ ∀ v, L v = deriv F x * v + 0 * conj v := by
  refine ⟨_, hF.hasDerivAt.hasFDerivAt.restrictScalars ℝ, fun v => ?_⟩
  simp only [ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  ring

theorem s09_au_wd_ofReal {φ : ℂ → ℝ} {Lφ : ℂ →L[ℝ] ℝ} {x c : ℂ} (hφ : HasFDerivAt φ Lφ x)
    (hv : ∀ v, Lφ v = 2 * (c * v).re) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun y => (φ y : ℂ)) L x ∧ ∀ v, L v = c * v + conj c * conj v := by
  refine ⟨_, Complex.ofRealCLM.hasFDerivAt.comp x hφ, fun v => ?_⟩
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, Complex.ofRealCLM_apply, hv]
  push_cast
  rw [Complex.re_eq_add_conj, map_mul]
  ring

theorem s09_au_wd_re {F : ℂ → ℂ} {x a b : ℂ}
    (hF : ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt F L x ∧ ∀ v, L v = a * v + b * conj v) :
    ∃ L : ℂ →L[ℝ] ℝ, HasFDerivAt (fun y => (F y).re) L x ∧ ∀ v, L v = (a * v + b * conj v).re := by
  obtain ⟨L, hL, hLv⟩ := hF
  exact ⟨_, Complex.reCLM.hasFDerivAt.comp x hL, fun v => by
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, Complex.reCLM_apply, hLv]⟩

/-- Helper (W1a) for `s09_au_tension`: the Laplacian plus Christoffel sum over `e ∈ {1, i}` for a
map with `dX(v) = (P v + Q v̄, Re(2 R v))` and `D²X(v, v)` from the Wirtinger data of `P, Q, R`:
`ΔX + Σ Γ(dXe, dXe) = (2∂̄P + 2∂Q − 4(RQ + R̄P)/ξ, 4 Re ∂̄R + (2|P|² + 2|Q|² − 4|R|²)/ξ)`. -/
theorem s09_au_tn_sum (q : ℂ × ℝ) (P Q R aP bP aQ bQ aR bR : ℂ) :
    (((aP * 1 + bP * conj 1) * 1 + (aQ * 1 + bQ * conj 1) * conj 1,
        (2 * ((aR * 1 + bR * conj 1) * 1)).re) : ℂ × ℝ) +
      ((aP * I + bP * conj I) * I + (aQ * I + bQ * conj I) * conj I,
        (2 * ((aR * I + bR * conj I) * I)).re) +
      hypChristoffel q (P * 1 + Q * conj 1, (2 * (R * 1)).re) (P * 1 + Q * conj 1, (2 * (R * 1)).re) +
      hypChristoffel q (P * I + Q * conj I, (2 * (R * I)).re) (P * I + Q * conj I, (2 * (R * I)).re) =
    (2 * bP + 2 * aQ - ((4 / q.2 : ℝ) : ℂ) * (R * Q + conj R * P),
      4 * bR.re + (2 * ‖P‖ ^ 2 + 2 * ‖Q‖ ^ 2 - 4 * ‖R‖ ^ 2) / q.2) := by
  unfold hypChristoffel
  refine Prod.ext ?_ ?_
  · apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;> ring
  · simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sq_norm,
      Complex.normSq_apply]
    ring

/-- Helper (W1a) for `s09_au_tension`: on `Ω`, `dX(v) = (P v + Q v̄, Re(2 R v))` with
`P = 2(λ⁴ − 4SĀ²)/D²`, `Q = 2λ²(S̄ − 4Ā²)/D²`, `R = −4λ(λ²A + SĀ)/D²`, `D = λ² + 4AĀ`, where
`A = ∂ log λ` and `S = S(ψ)`, `ψ = f⁻¹` (`∂λ = λA`, `∂A = A² + S/2`, `∂̄A = λ²/4`). -/
theorem s09_au_tn_dX {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {x : ℂ}
    (hx : x ∈ Ω) (v : ℂ) :
    fderiv ℝ (epstein Ω) x v =
      (2 * ((poincareDensity Ω x : ℂ) ^ 4 - 4 * schwarzian (Function.invFunOn f unitDisc) x *
            conj (logDensityDz Ω x) ^ 2) /
          ((poincareDensity Ω x : ℂ) ^ 2 + 4 * (logDensityDz Ω x * conj (logDensityDz Ω x))) ^ 2 * v +
        2 * (poincareDensity Ω x : ℂ) ^ 2 * (conj (schwarzian (Function.invFunOn f unitDisc) x) -
            4 * conj (logDensityDz Ω x) ^ 2) /
          ((poincareDensity Ω x : ℂ) ^ 2 + 4 * (logDensityDz Ω x * conj (logDensityDz Ω x))) ^ 2 *
            conj v,
        (2 * (-4 * (poincareDensity Ω x : ℂ) * ((poincareDensity Ω x : ℂ) ^ 2 * logDensityDz Ω x +
            schwarzian (Function.invFunOn f unitDisc) x * conj (logDensityDz Ω x)) /
          ((poincareDensity Ω x : ℂ) ^ 2 + 4 * (logDensityDz Ω x * conj (logDensityDz Ω x))) ^ 2 *
            v)).re) := by
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hx
  obtain ⟨Ll, hLl, hLlv⟩ := s02_fff_hasFDerivAt_lambda hf hx
  obtain ⟨LA, hLA, hLAv⟩ := s02_fff_hasFDerivAt_A hf hx
  have dl := s09_au_wd_ofReal hLl (c := (poincareDensity Ω x : ℂ) * logDensityDz Ω x)
    (fun v => by rw [hLlv, mul_assoc, Complex.re_ofReal_mul]; ring)
  have dA : ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (logDensityDz Ω) L x ∧ ∀ v, L v =
      (logDensityDz Ω x ^ 2 + schwarzian (Function.invFunOn f unitDisc) x / 2) * v +
        ((poincareDensity Ω x ^ 2 / 4 : ℝ) : ℂ) * conj v := ⟨LA, hLA, hLAv⟩
  have dB := s09_au_wd_conj dA
  have dD := s09_au_wd_add (s09_au_wd_mul dl dl)
    (s09_au_wd_mul (s09_au_wd_const 4 x) (s09_au_wd_mul dA dB))
  -- `D = λ² + 4|A|² > 0`
  have hDr : ∀ y, ((poincareDensity Ω y ^ 2 + 4 * ‖logDensityDz Ω y‖ ^ 2 : ℝ) : ℂ) =
      (poincareDensity Ω y : ℂ) * (poincareDensity Ω y : ℂ) +
        4 * (logDensityDz Ω y * conj (logDensityDz Ω y)) := by
    intro y
    push_cast
    rw [Complex.mul_conj']
    ring
  have hD0 : (poincareDensity Ω x : ℂ) * (poincareDensity Ω x : ℂ) +
      4 * (logDensityDz Ω x * conj (logDensityDz Ω x)) ≠ 0 := by
    rw [← hDr]
    exact_mod_cast (by positivity : (0 : ℝ) < poincareDensity Ω x ^ 2 +
      4 * ‖logDensityDz Ω x‖ ^ 2).ne'
  have hD1 : (poincareDensity Ω x : ℂ) ^ 2 +
      4 * (logDensityDz Ω x * conj (logDensityDz Ω x)) ≠ 0 := by
    rw [sq]; exact hD0
  have hl0 : (poincareDensity Ω x : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have dDi := s09_au_wd_inv dD hD0
  have dX1 := s09_au_wd_add (s09_au_wd_id x)
    (s09_au_wd_mul (s09_au_wd_mul (s09_au_wd_const 4 x) dB) dDi)
  have dX2 := s09_au_wd_re (s09_au_wd_mul (s09_au_wd_mul (s09_au_wd_const 2 x) dl) dDi)
  obtain ⟨L1, hL1, hL1v⟩ := dX1
  obtain ⟨L2, hL2, hL2v⟩ := dX2
  have hX : HasFDerivAt (epstein Ω) (L1.prod L2) x := by
    refine (hL1.prodMk hL2).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    refine Prod.ext ?_ ?_
    · show y + 4 * conj (logDensityDz Ω y) /
          ((poincareDensity Ω y ^ 2 + 4 * ‖logDensityDz Ω y‖ ^ 2 : ℝ) : ℂ) = _
      rw [hDr, div_eq_mul_inv]
    · show 2 * poincareDensity Ω y / (poincareDensity Ω y ^ 2 + 4 * ‖logDensityDz Ω y‖ ^ 2) = _
      simp only []
      rw [← hDr, ← Complex.ofReal_inv, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
        ← Complex.ofReal_mul, Complex.ofReal_re, div_eq_mul_inv]
  have hre : ∀ z : ℂ, (2 * z).re = (z + conj z).re := fun z => by
    rw [Complex.add_re, Complex.conj_re, two_mul, Complex.add_re]
  rw [hX.fderiv, ContinuousLinearMap.prod_apply, hL1v, hL2v, Prod.mk.injEq, hre]
  refine ⟨?_, congrArg Complex.re ?_⟩
  all_goals
    rw [show (poincareDensity Ω x : ℂ) ^ 2 + 4 * (logDensityDz Ω x * conj (logDensityDz Ω x)) =
      (poincareDensity Ω x : ℂ) * (poincareDensity Ω x : ℂ) +
        4 * (logDensityDz Ω x * conj (logDensityDz Ω x)) by ring]
    have hDc : conj ((poincareDensity Ω x : ℂ) * (poincareDensity Ω x : ℂ) +
        4 * (logDensityDz Ω x * conj (logDensityDz Ω x))) =
        (poincareDensity Ω x : ℂ) * (poincareDensity Ω x : ℂ) +
          4 * (logDensityDz Ω x * conj (logDensityDz Ω x)) := by
      simp only [map_add, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_conj]
      ring
    generalize hDd : (poincareDensity Ω x : ℂ) * (poincareDensity Ω x : ℂ) +
      4 * (logDensityDz Ω x * conj (logDensityDz Ω x)) = D at hD0 hDc ⊢
    simp only [map_add, map_mul, map_div₀, map_pow, map_ofNat, map_neg,
      Complex.conj_ofReal, Complex.conj_conj, hDc]
    push_cast
    field_simp
    subst hDd
    ring

/-- Helper (W1a) for `s09_au_tension`: names the Wirtinger data of `F`. -/
theorem s09_au_wd_name {F : ℂ → ℂ} {x a b : ℂ}
    (h : ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt F L x ∧ ∀ v, L v = a * v + b * conj v) :
    ∃ a' b' : ℂ, a' = a ∧ b' = b ∧
      ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt F L x ∧ ∀ v, L v = a' * v + b' * conj v :=
  ⟨a, b, rfl, rfl, h⟩

/-- Helper (W1a) for `lem:ambient-adjoint` (b): the tension field of the Epstein–Poincaré map
is normal, `N = −2 s² λ² ν` (`tr_ρ 𝒟 = 0`; only `λ, A, S` enter, `∂̄` kills `S`). -/
theorem s09_au_tension {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (hΩ : IsOpen Ω) {w : ℂ} (hw : w ∈ Ω) :
    fderiv ℝ (fderiv ℝ (epstein Ω)) w 1 1 + fderiv ℝ (fderiv ℝ (epstein Ω)) w I I +
        hypChristoffel (epstein Ω w) (fderiv ℝ (epstein Ω) w 1) (fderiv ℝ (epstein Ω) w 1) +
        hypChristoffel (epstein Ω w) (fderiv ℝ (epstein Ω) w I) (fderiv ℝ (epstein Ω) w I) =
      (-2 * schwarzNorm Ω w ^ 2 * poincareDensity Ω w ^ 2) • normalVec Ω w := by
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hw
  have hlΩ : ∀ y ∈ Ω, 0 < poincareDensity Ω y := fun y hy => s02_poincareDensity_pos ⟨f, hf⟩ hy
  obtain ⟨Ll, hLl, hLlv⟩ := s02_fff_hasFDerivAt_lambda hf hw
  obtain ⟨LA, hLA, hLAv⟩ := s02_fff_hasFDerivAt_A hf hw
  -- `S = S(ψ)` is holomorphic on `Ω`
  have hSd : DifferentiableAt ℂ (schwarzian (Function.invFunOn f unitDisc)) w := by
    have hψ : IsConformalOnto (Function.invFunOn f unitDisc) Ω unitDisc := hf.symm isOpen_ball
    have hψ'ne : ∀ x ∈ Ω, deriv (Function.invFunOn f unitDisc) x ≠ 0 := fun x hx =>
      deriv_ne_zero_of_injOn hΩ hψ.1 hψ.2.1 hx
    have h0 : DifferentiableOn ℂ (Function.invFunOn f unitDisc) Ω := hψ.1
    have h1 := h0.deriv hΩ
    have hg := (h1.deriv hΩ).div h1 hψ'ne
    have hS := (hg.deriv hΩ).sub ((hg.pow 2).const_mul (1 / 2 : ℂ))
    refine (hS.congr fun x hx => ?_).differentiableAt (hΩ.mem_nhds hw)
    exact schwarzian_of_analyticAt (h0.analyticAt (hΩ.mem_nhds hx))
  have hdX := fun y (hy : y ∈ Ω) v => s09_au_tn_dX hf hy v
  have hXd : DifferentiableAt ℝ (fderiv ℝ (epstein Ω)) w := by
    have hc : ContDiffAt ℝ 2 (epstein Ω) w :=
      ((lem_fff_smooth ⟨f, hf⟩).contDiffAt (hΩ.mem_nhds hw)).of_le (by simp)
    exact (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hq : (epstein Ω w).2 = 2 * poincareDensity Ω w /
      (poincareDensity Ω w ^ 2 + 4 * ‖logDensityDz Ω w‖ ^ 2) := rfl
  rw [normalVec, (s02_hasDerivAt_normalGeod Ω w hl).deriv, eq_def_s hf hw]
  generalize schwarzian (Function.invFunOn f unitDisc) = S at hLAv hSd hdX ⊢
  generalize epstein Ω = X at hdX hXd hq ⊢
  generalize logDensityDz Ω = A at hLlv hLA hLAv hdX hq ⊢
  generalize poincareDensity Ω = lam at hl hlΩ hLl hLlv hLAv hdX hq ⊢
  -- `D = λ² + 4AĀ`
  have hDr : ∀ y, ((lam y ^ 2 + 4 * ‖A y‖ ^ 2 : ℝ) : ℂ) = (lam y : ℂ) * lam y + 4 * (A y * conj (A y)) := by
    intro y
    push_cast
    rw [Complex.mul_conj']
    ring
  have hDpos : ∀ y ∈ Ω, (lam y : ℂ) * lam y + 4 * (A y * conj (A y)) ≠ 0 := fun y hy => by
    rw [← hDr]
    exact_mod_cast (by have := hlΩ y hy; positivity : (0 : ℝ) < lam y ^ 2 + 4 * ‖A y‖ ^ 2).ne'
  -- Wirtinger data at `w`
  have dl := s09_au_wd_ofReal hLl (c := (lam w : ℂ) * A w)
    (fun v => by rw [hLlv, mul_assoc, Complex.re_ofReal_mul]; ring)
  have dA : ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt A L w ∧ ∀ v, L v =
      (A w ^ 2 + S w / 2) * v + ((lam w ^ 2 / 4 : ℝ) : ℂ) * conj v := ⟨LA, hLA, hLAv⟩
  have dB := s09_au_wd_conj dA
  have dS := s09_au_wd_holo hSd
  have dSb := s09_au_wd_conj dS
  have dD := s09_au_wd_add (s09_au_wd_mul dl dl)
    (s09_au_wd_mul (s09_au_wd_const 4 w) (s09_au_wd_mul dA dB))
  have dDD := s09_au_wd_mul (s09_au_wd_inv dD (hDpos w hw)) (s09_au_wd_inv dD (hDpos w hw))
  obtain ⟨aP, bP, -, hbP, dP⟩ := s09_au_wd_name (s09_au_wd_mul (s09_au_wd_mul
    (s09_au_wd_const 2 w) (s09_au_wd_sub (s09_au_wd_mul (s09_au_wd_mul dl dl) (s09_au_wd_mul dl dl))
      (s09_au_wd_mul (s09_au_wd_const 4 w) (s09_au_wd_mul dS (s09_au_wd_mul dB dB))))) dDD)
  obtain ⟨aQ, bQ, haQ, -, dQ⟩ := s09_au_wd_name (s09_au_wd_mul (s09_au_wd_mul
    (s09_au_wd_mul (s09_au_wd_const 2 w) (s09_au_wd_mul dl dl))
      (s09_au_wd_sub dSb (s09_au_wd_mul (s09_au_wd_const 4 w) (s09_au_wd_mul dB dB)))) dDD)
  obtain ⟨aR, bR, -, hbR, dR⟩ := s09_au_wd_name (s09_au_wd_mul (s09_au_wd_mul
    (s09_au_wd_mul (s09_au_wd_const (-4) w) dl)
      (s09_au_wd_add (s09_au_wd_mul (s09_au_wd_mul dl dl) dA) (s09_au_wd_mul dS dB))) dDD)
  -- `D²X(v, v)` from the data of `P, Q, R`
  have key : ∀ v : ℂ, fderiv ℝ (fderiv ℝ X) w v v =
      ((aP * v + bP * conj v) * v + (aQ * v + bQ * conj v) * conj v,
        (2 * ((aR * v + bR * conj v) * v)).re) := by
    intro v
    obtain ⟨L1, hL1, hL1v⟩ := s09_au_wd_add (s09_au_wd_mul dP (s09_au_wd_const v w))
      (s09_au_wd_mul dQ (s09_au_wd_const (conj v) w))
    obtain ⟨L2, hL2, hL2v⟩ := s09_au_wd_re (s09_au_wd_mul (s09_au_wd_const 2 w)
      (s09_au_wd_mul dR (s09_au_wd_const v w)))
    have hU : HasFDerivAt (fun y => fderiv ℝ X y v) (L1.prod L2) w := by
      refine (hL1.prodMk hL2).congr_of_eventuallyEq ?_
      filter_upwards [hΩ.mem_nhds hw] with y hy
      have hD := hDpos y hy
      rw [hdX y hy v, Prod.mk.injEq]
      refine ⟨?_, congrArg Complex.re ?_⟩
      all_goals
        rw [show (lam y : ℂ) ^ 2 + 4 * (A y * conj (A y)) =
          (lam y : ℂ) * lam y + 4 * (A y * conj (A y)) by ring]
        generalize (lam y : ℂ) * lam y + 4 * (A y * conj (A y)) = D at hD ⊢
        field_simp
    have h2 := congrArg (fun L : ℂ →L[ℝ] ℂ × ℝ => L v)
      ((hXd.hasFDerivAt.clm_apply (hasFDerivAt_const v w)).unique hU)
    beta_reduce at h2
    rw [add_apply, ContinuousLinearMap.comp_zero, zero_apply, zero_add,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.prod_apply, hL1v, hL2v] at h2
    rw [h2, Prod.mk.injEq]
    exact ⟨by ring, by ring_nf⟩
  rw [key 1, key I, hdX w hw 1, hdX w hw I, s09_au_tn_sum, hq]
  subst hbP haQ hbR
  -- in terms of `D` only
  have hDw := hDr w
  have hD0 : (0 : ℝ) < lam w ^ 2 + 4 * ‖A w‖ ^ 2 := by positivity
  rw [show ‖A w‖ ^ 2 + (lam w / 2) ^ 2 = (lam w ^ 2 + 4 * ‖A w‖ ^ 2) / 4 by ring,
    show (lam w / 2) ^ 2 - ‖A w‖ ^ 2 = (2 * lam w ^ 2 - (lam w ^ 2 + 4 * ‖A w‖ ^ 2)) / 4 by ring]
  rw [show (lam w : ℂ) ^ 2 + 4 * (A w * conj (A w)) = (lam w : ℂ) * lam w + 4 * (A w * conj (A w))
    by ring, ← hDw]
  generalize lam w ^ 2 + 4 * ‖A w‖ ^ 2 = Dr at hD0 hDw ⊢
  have hl0 : (lam w : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hDr0 : (Dr : ℂ) ≠ 0 := by exact_mod_cast hD0.ne'
  refine Prod.ext ?_ ?_
  · simp only [Prod.smul_fst, Complex.real_smul]
    push_cast
    simp only [div_pow, ← Complex.mul_conj', map_add, map_mul, map_div₀, map_pow,
      map_ofNat, map_neg, map_zero, Complex.conj_ofReal, Complex.conj_conj]
    field_simp
    rw [hDw]
    ring
  · simp only [Prod.smul_snd, smul_eq_mul]
    apply Complex.ofReal_injective
    push_cast
    rw [Complex.re_eq_add_conj]
    simp only [div_pow, ← Complex.mul_conj', map_add, map_mul, map_div₀, map_inv₀, map_pow,
      map_ofNat, map_neg, map_sub, map_zero, Complex.conj_ofReal, Complex.conj_conj]
    field_simp
    rw [hDw]
    ring

/-- Lemma 9.4 `lem:ambient-adjoint` (b) (`sec09-ambient.tex:213`), pointwise form: for
`κ = k_P ∘ X`, `Δ_ρ κ ≤ −κ² + C₂ s κ` wherever `s ≤ 1/4`; `C₂` is absolute.  (On `G₀`, where
`s < η < ε`, this is the paper's `Δ_ρ κ ≤ −κ² + C₂ ε κ`; it is also used in §10.) -/
theorem s09_au_lap : ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ P ∈ UHS,
    ∀ w ∈ Ω, schwarzNorm Ω w ≤ 1 / 4 →
      rhoLaplacian Ω (fun x => ambKernel P (epstein Ω x)) w ≤
        -ambKernel P (epstein Ω w) ^ 2 + C₂ * schwarzNorm Ω w * ambKernel P (epstein Ω w) := by
  refine ⟨65, by norm_num, fun Ω Ωs hJ P hP w hw hs => ?_⟩
  obtain ⟨f, hf, -⟩ := s02_riemannMap_at hJ hw
  have hΩ : IsOpen Ω := hf.isOpen isOpen_ball
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hw
  have hXU : ∀ x ∈ Ω, epstein Ω x ∈ UHS := fun x hx => by
    have h := lem_normal_b ⟨f, hf⟩ hx
    rw [← h.2.2]
    exact h.1 0
  have hXs := lem_fff_smooth ⟨f, hf⟩
  have hks := (lem_ambient_kernel_a P hP).1
  have hu : ContDiffOn ℝ 2 (fun x => ambKernel P (epstein Ω x)) Ω :=
    (hks.comp hXs fun x hx => hXU x hx).of_le (by simp)
  have hQ := hXU w hw
  have hkc : ContDiffAt ℝ 2 (ambKernel P) (epstein Ω w) :=
    (hks.contDiffAt (s09_isOpen_UHS.mem_nhds hQ)).of_le (by simp)
  have hXc : ContDiffAt ℝ 2 (epstein Ω) w := (hXs.contDiffAt (hΩ.mem_nhds hw)).of_le (by simp)
  rw [s10_mlb_rhoLap Ω hΩ hu hw, s09_au_chain hkc hXc, s09_au_tension hf hΩ hw, map_smul,
    smul_eq_mul]
  -- `|S(ψ)| = s λ²`
  have hS := eq_def_s hf hw
  have hl2 : 0 < poincareDensity Ω w ^ 2 := by positivity
  have hSn : ‖schwarzian (Function.invFunOn f unitDisc) w‖ =
      schwarzNorm Ω w * poincareDensity Ω w ^ 2 := by
    rw [hS]
    field_simp
  have hs0 : 0 ≤ schwarzNorm Ω w := by rw [hS]; positivity
  have hN := s09_au_normal hJ hP hw (by linarith : schwarzNorm Ω w < 1).ne
  obtain ⟨hk0, -, -⟩ := (lem_ambient_kernel_a P hP).2 _ hQ
  -- the Gram matrix of `dX(1), dX(i)` (`s02_curv_fI`)
  have hgi : ∀ a b, hypMetric (epstein Ω w) a b = hypInner (epstein Ω w) a b := by
    intro a b
    unfold hypMetric eucInner hypInner
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hg := s02_curv_fI hf hw
  have hre := Complex.abs_re_le_norm (schwarzian (Function.invFunOn f unitDisc) w)
  have him := Complex.abs_im_le_norm (schwarzian (Function.invFunOn f unitDisc) w)
  rw [hSn] at hre him
  have hss : schwarzNorm Ω w ^ 2 ≤ schwarzNorm Ω w / 4 := by nlinarith
  have hss' : schwarzNorm Ω w ^ 2 * poincareDensity Ω w ^ 2 ≤
      schwarzNorm Ω w / 4 * poincareDensity Ω w ^ 2 := mul_le_mul_of_nonneg_right hss hl2.le
  have haa : |hypMetric (epstein Ω w) (fderiv ℝ (epstein Ω) w 1) (fderiv ℝ (epstein Ω) w 1) -
      poincareDensity Ω w ^ 2| ≤ 3 * schwarzNorm Ω w * poincareDensity Ω w ^ 2 := by
    rw [hgi, hg]
    simp only [map_one, mul_one, Complex.one_re]
    rw [abs_le] at hre ⊢
    constructor <;> nlinarith
  have hbb : |hypMetric (epstein Ω w) (fderiv ℝ (epstein Ω) w I) (fderiv ℝ (epstein Ω) w I) -
      poincareDensity Ω w ^ 2| ≤ 3 * schwarzNorm Ω w * poincareDensity Ω w ^ 2 := by
    rw [hgi, hg]
    have e1 : (I * conj I).re = 1 := by simp
    have e2 : (schwarzian (Function.invFunOn f unitDisc) w * I * I).re =
        -(schwarzian (Function.invFunOn f unitDisc) w).re := by simp [mul_assoc]
    rw [e1, e2]
    rw [abs_le] at hre ⊢
    constructor <;> nlinarith
  have hab : |hypMetric (epstein Ω w) (fderiv ℝ (epstein Ω) w 1) (fderiv ℝ (epstein Ω) w I)| ≤
      2 * schwarzNorm Ω w * poincareDensity Ω w ^ 2 := by
    rw [hgi, hg]
    have e1 : ((1 : ℂ) * conj I).re = 0 := by simp
    have e2 : (schwarzian (Function.invFunOn f unitDisc) w * 1 * I).re =
        -(schwarzian (Function.invFunOn f unitDisc) w).im := by simp
    rw [e1, e2]
    rw [abs_le] at him ⊢
    constructor <;> nlinarith
  have htr := s09_au_trace hP hQ hl hs0 hs haa hbb hab
  -- `dk(N) = −2 s² λ² dk(ν) ≤ 2 s² λ² k`
  have hNb := (abs_le.mp hN).1
  have hNk : -2 * schwarzNorm Ω w ^ 2 * poincareDensity Ω w ^ 2 *
      fderiv ℝ (ambKernel P) (epstein Ω w) (normalVec Ω w) ≤
        schwarzNorm Ω w * poincareDensity Ω w ^ 2 * ambKernel P (epstein Ω w) := by
    have h1 : 0 ≤ schwarzNorm Ω w ^ 2 * poincareDensity Ω w ^ 2 := by positivity
    have h2 := mul_le_mul_of_nonneg_left (neg_le.mpr hNb) h1
    have h3 := mul_le_mul_of_nonneg_right hss' hk0.le
    nlinarith
  rw [div_le_iff₀ hl2]
  nlinarith

/-- Lemma 9.4 `lem:ambient-adjoint` (a), first half (`sec09-ambient.tex:211`): `|∇κ| ≤ (5/2) κ`
on `Ω`, i.e. `|dκ(v)| ≤ (5/2) κ ρ(v)^{1/2}` (`lem_ambient_kernel_c`, `eq_dX_norm_always`). -/
theorem s09_au_grad {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {P : ℂ × ℝ}
    (hP : P ∈ UHS) {w : ℂ} (hw : w ∈ Ω) (v : ℂ) :
    |fderiv ℝ (fun x => ambKernel P (epstein Ω x)) w v| ≤
      5 / 2 * ambKernel P (epstein Ω w) * (poincareDensity Ω w * ‖v‖) := by
  have hQ : epstein Ω w ∈ UHS := by
    have h := lem_normal_b hΩ hw
    rw [← h.2.2]
    exact h.1 0
  have hkd : DifferentiableAt ℝ (ambKernel P) (epstein Ω w) :=
    ((lem_ambient_kernel_a P hP).1.contDiffAt (s09_isOpen_UHS.mem_nhds hQ)).differentiableAt
      (by simp)
  have hcomp : fderiv ℝ (fun x => ambKernel P (epstein Ω x)) w v =
      fderiv ℝ (ambKernel P) (epstein Ω w) (fderiv ℝ (epstein Ω) w v) := by
    rw [show (fun x => ambKernel P (epstein Ω x)) = ambKernel P ∘ epstein Ω from rfl,
      fderiv_comp w hkd (s02_epstein_differentiableAt hΩ hw)]
    rfl
  have hg : hypMetric (epstein Ω w) (fderiv ℝ (epstein Ω) w v) (fderiv ℝ (epstein Ω) w v) =
      hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w v) (fderiv ℝ (epstein Ω) w v) := by
    unfold hypMetric eucInner hypInner
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have h1 := (lem_ambient_kernel_c P hP _ hQ).1 (fderiv ℝ (epstein Ω) w v)
  obtain ⟨hk0, -, -⟩ := (lem_ambient_kernel_a P hP).2 _ hQ
  rw [hcomp]
  calc |fderiv ℝ (ambKernel P) (epstein Ω w) (fderiv ℝ (epstein Ω) w v)|
      ≤ √(ambKernel P (epstein Ω w) ^ 2 *
          hypMetric (epstein Ω w) (fderiv ℝ (epstein Ω) w v) (fderiv ℝ (epstein Ω) w v)) :=
        Real.abs_le_sqrt h1
    _ = ambKernel P (epstein Ω w) *
          √(hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w v) (fderiv ℝ (epstein Ω) w v)) := by
        rw [hg, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hk0.le]
    _ ≤ ambKernel P (epstein Ω w) * (5 / 2 * (poincareDensity Ω w * ‖v‖)) :=
        mul_le_mul_of_nonneg_left (eq_dX_norm_always hΩ hw v) hk0.le
    _ = 5 / 2 * ambKernel P (epstein Ω w) * (poincareDensity Ω w * ‖v‖) := by ring

/-- Helper for `thm_ambient`, the right inequality (`sec09-ambient.tex:495`, W-AMBUP): for a
`K`-quasicircle that is not a circle, `V(P) ≤ C_K H(P)`.  The paper's proof is the adjoint
argument of §9.3–9.6 (Lemmas 9.4–9.8 on the good domain `G₁` of §5, with the Dirichlet solution
and comparison of §5); it does not reduce to `thm_upper` (the ambient and intrinsic kernels are
not comparable, `rem_ambient_intrinsic_c`). -/
theorem s09_amb_upper :
    ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ≥0, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ P ∈ UHS, ambV Ω Ωs P ≤ (C : ℝ≥0∞) * ambH Ω Ωs P := by
  sorry

/-- Helper for `thm_ambient`, the cell estimate of the left inequality (`sec09-ambient.tex:149`):
for a `K`-quasicircle that is not a circle and `b ∈ ℍ³`, the `μ_H`-integral of `k_P` over the
cell `X⁻¹ B(b, 1)` is at most `e^{1+R_K} C(K) ∫_{𝒩 ∩ B(b, R_K)} k_P dvol`
(`lem_ambient_kernel_e` and `prop_mass_volume`). -/
theorem s09_amb_cell :
    ∀ K : ℝ, 1 ≤ K → ∃ R C : ℝ≥0, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ P ∈ UHS, ∀ b ∈ UHS,
        (∫⁻ w in Ω ∩ epstein Ω ⁻¹' hball b 1, ENNReal.ofReal (ambKernel P (epstein Ω w))
            ∂curvMass Ω) +
          ∫⁻ z in Ωs ∩ epstein Ωs ⁻¹' hball b 1, ENNReal.ofReal (ambKernel P (epstein Ωs z))
            ∂curvMass Ωs ≤
        (C : ℝ≥0∞) * ∫⁻ q in gap Ω Ωs ∩ hball b R, ENNReal.ofReal (ambKernel P q) ∂hvol := by
  intro K hK
  obtain ⟨R, C, -, hmv⟩ := prop_mass_volume K hK
  refine ⟨R, (Real.exp 1 * Real.exp R).toNNReal * C, fun Ω Ωs h hl P hP b hb => ?_⟩
  have hk0 : ∀ Q, 0 ≤ ambKernel P Q := fun Q => by
    unfold ambKernel
    positivity
  -- on the cell, `k_P(X w) ≤ e k_P(b)` (Lemma 9.3(e), `d(X w, b) ≤ 1`)
  have hcellΩ : ∀ Ω' : Set ℂ, (∫⁻ w in Ω' ∩ epstein Ω' ⁻¹' hball b 1,
      ENNReal.ofReal (ambKernel P (epstein Ω' w)) ∂curvMass Ω') ≤
      ENNReal.ofReal (Real.exp 1 * ambKernel P b) * curvMass Ω' (epstein Ω' ⁻¹' hball b 1) := by
    intro Ω'
    calc (∫⁻ w in Ω' ∩ epstein Ω' ⁻¹' hball b 1,
          ENNReal.ofReal (ambKernel P (epstein Ω' w)) ∂curvMass Ω')
        ≤ ∫⁻ _ in Ω' ∩ epstein Ω' ⁻¹' hball b 1,
            ENNReal.ofReal (Real.exp 1 * ambKernel P b) ∂curvMass Ω' := by
          refine setLIntegral_mono measurable_const fun w hw => ENNReal.ofReal_le_ofReal ?_
          have hQ : epstein Ω' w ∈ hball b 1 := hw.2
          have hd : hdist (epstein Ω' w) b ≤ 1 := by
            rw [s02_hdist_comm]
            exact hQ.2
          exact ((lem_ambient_kernel_e P (epstein Ω' w) b P hP hQ.1 hb hP).2.1).trans
            (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hd) (hk0 b))
      _ = ENNReal.ofReal (Real.exp 1 * ambKernel P b) *
            curvMass Ω' (Ω' ∩ epstein Ω' ⁻¹' hball b 1) := setLIntegral_const _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (measure_mono inter_subset_right) zero_le
  -- on `B(b, R)`, `k_P(b) ≤ e^R k_P(q)`
  have hG : MeasurableSet (gap Ω Ωs ∩ hball b R) :=
    (s06_tl_gap_meas h hl).inter (s05_pk_hball_meas b R)
  have hvb : ENNReal.ofReal (ambKernel P b) * hvol (gap Ω Ωs ∩ hball b R) ≤
      ENNReal.ofReal (Real.exp R) *
        ∫⁻ q in gap Ω Ωs ∩ hball b R, ENNReal.ofReal (ambKernel P q) ∂hvol := by
    rw [← setLIntegral_const, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' hG fun q hq => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hq2 : q ∈ hball b R := hq.2
    exact ((lem_ambient_kernel_e P b q P hP hb hq2.1 hP).2.1).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hq2.2) (hk0 q))
  calc _ ≤ ENNReal.ofReal (Real.exp 1 * ambKernel P b) * curvMass Ω (epstein Ω ⁻¹' hball b 1) +
        ENNReal.ofReal (Real.exp 1 * ambKernel P b) * curvMass Ωs (epstein Ωs ⁻¹' hball b 1) :=
        add_le_add (hcellΩ Ω) (hcellΩ Ωs)
    _ = ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal (ambKernel P b) *
          (curvMass Ω (epstein Ω ⁻¹' hball b 1) + curvMass Ωs (epstein Ωs ⁻¹' hball b 1)) := by
        rw [← mul_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ ≤ ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal (ambKernel P b) *
          ((C : ℝ≥0∞) * hvol (gap Ω Ωs ∩ hball b R)) :=
        mul_le_mul_of_nonneg_left (hmv Ω Ωs h hl b hb) zero_le
    _ = ENNReal.ofReal (Real.exp 1) * C *
          (ENNReal.ofReal (ambKernel P b) * hvol (gap Ω Ωs ∩ hball b R)) := by ring
    _ ≤ ENNReal.ofReal (Real.exp 1) * C * (ENNReal.ofReal (Real.exp R) *
          ∫⁻ q in gap Ω Ωs ∩ hball b R, ENNReal.ofReal (ambKernel P q) ∂hvol) :=
        mul_le_mul_of_nonneg_left hvb zero_le
    _ = (((Real.exp 1 * Real.exp R).toNNReal * C : ℝ≥0) : ℝ≥0∞) *
          ∫⁻ q in gap Ω Ωs ∩ hball b R, ENNReal.ofReal (ambKernel P q) ∂hvol := by
        rw [ENNReal.coe_mul]
        change _ = ENNReal.ofReal (Real.exp 1 * Real.exp R) * _ * _
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
        ring

/-- Helper for `thm_ambient`, the left inequality (`sec09-ambient.tex:149`): for a
`K`-quasicircle that is not a circle, `H(P) ≤ C_K V(P)` (a `1`-net of `ℍ³`, `s09_amb_cell`, and
the bounded multiplicity of the balls `B(P_j, R_K)`). -/
theorem s09_amb_lower :
    ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ≥0, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ P ∈ UHS, ambH Ω Ωs P ≤ (C : ℝ≥0∞) * ambV Ω Ωs P := by
  intro K hK
  obtain ⟨R, C, hcell⟩ := s09_amb_cell K hK
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = 23328 * Real.cosh (R + 1 / 3) ^ 6 := ⟨_, rfl⟩
  refine ⟨C * N.toNNReal, fun Ω Ωs h hl P hP => ?_⟩
  obtain ⟨S, hSU, hS, hcov⟩ := s06_tl_net
  have hSc := s06_tl_countable hSU hS
  have hJ := s03_b0_jordanPair h
  have hJs := s03_b0_jordanPair (s03_qce_swap h)
  have hKH := s06_tl_cover hJ hSc hcov (fun w => ENNReal.ofReal (ambKernel P (epstein Ω w)))
  have hKs := s06_tl_cover hJs hSc hcov (fun z => ENNReal.ofReal (ambKernel P (epstein Ωs z)))
  obtain ⟨g, hg⟩ : ∃ g : ℂ × ℝ → ℝ≥0∞, g = fun q => ENNReal.ofReal (ambKernel P q) := ⟨_, rfl⟩
  -- multiplicity: a point of `ℍ³` lies in at most `N` of the balls `B(b, R)`
  have hmult : ∀ q, ∑' b : S, (hball (b : ℂ × ℝ) R).indicator g q ≤ ENNReal.ofReal N * g q := by
    intro q
    by_cases hq : q ∈ UHS
    · rw [hN]
      exact s05_pk_tsum_le hSU hS hq R (fun b => hball b R) g q fun b _ hb => by
        rw [s02_hdist_comm]
        exact hb.2
    · have h0 : ∀ b : S, (hball (b : ℂ × ℝ) R).indicator g q = 0 := fun b =>
        indicator_of_notMem (fun h : q ∈ hball (b : ℂ × ℝ) R => hq h.1) _
      simp only [h0, tsum_zero]
      exact bot_le
  calc ambH Ω Ωs P
      ≤ ∑' b : S, ((∫⁻ w in Ω ∩ epstein Ω ⁻¹' hball b 1,
            ENNReal.ofReal (ambKernel P (epstein Ω w)) ∂curvMass Ω) +
          ∫⁻ z in Ωs ∩ epstein Ωs ⁻¹' hball b 1,
            ENNReal.ofReal (ambKernel P (epstein Ωs z)) ∂curvMass Ωs) := by
        rw [ENNReal.tsum_add]
        exact add_le_add hKH hKs
    _ ≤ ∑' b : S, (C : ℝ≥0∞) * ∫⁻ q in gap Ω Ωs ∩ hball b R, g q ∂hvol := by
        rw [hg]
        exact tsum_le_tsum fun b => hcell Ω Ωs h hl P hP b (hSU b.2)
    _ = (C : ℝ≥0∞) *
          ∑' b : S, ∫⁻ q, (hball (b : ℂ × ℝ) R).indicator g q ∂(hvol.restrict (gap Ω Ωs)) := by
        rw [ENNReal.tsum_mul_left]
        congr 1
        refine tsum_congr fun b => ?_
        rw [lintegral_indicator (s05_pk_hball_meas _ _),
          Measure.restrict_restrict (s05_pk_hball_meas _ _), inter_comm]
    _ ≤ (C : ℝ≥0∞) *
          ∫⁻ q, ∑' b : S, (hball (b : ℂ × ℝ) R).indicator g q ∂(hvol.restrict (gap Ω Ωs)) := by
        gcongr
        exact s05_ct_tsum_lintegral_le _ _
    _ ≤ (C : ℝ≥0∞) * ∫⁻ q, ENNReal.ofReal N * g q ∂(hvol.restrict (gap Ω Ωs)) := by
        gcongr with q
        exact hmult q
    _ = ((C * N.toNNReal : ℝ≥0) : ℝ≥0∞) * ambV Ω Ωs P := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ENNReal.coe_mul, hg]
        rfl

/-- The circle case of Theorem 9.1 (`sec09-ambient.tex:45`): if `Γ` is a circle then
`H ≡ 0` and `V ≡ 0`. -/
theorem thm_ambient_circle (Ω Ωs : Set ℂ) (hΓ : IsLinePair Ω Ωs) (P : ℂ × ℝ) (hP : P ∈ UHS) :
    ambH Ω Ωs P = 0 ∧ ambV Ω Ωs P = 0 := by
  -- `hP` is not needed: for a line pair both `H` and `V` vanish at every `P`.
  have _hP := hP
  obtain ⟨a, b, ha, rfl, rfl⟩ := hΓ
  have hU := s02_halfplane a b ha 1 (Or.inl rfl) {z | 0 < (a * z + b).im} (fun z => by simp)
  have hL := s02_halfplane a b ha (-1) (Or.inr rfl) {z | (a * z + b).im < 0}
    (fun z => by
      show (a * z + b).im < 0 ↔ 0 < -1 * (a * z + b).im
      rw [neg_one_mul, neg_pos])
  have hmU : MeasurableSet {z : ℂ | 0 < (a * z + b).im} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hmL : MeasurableSet {z : ℂ | (a * z + b).im < 0} :=
    measurableSet_lt (by fun_prop) measurable_const
  constructor
  · unfold ambH
    rw [s02_curvMass_eq_zero _ hmU hU.1, s02_curvMass_eq_zero _ hmL hL.1]
    simp
  · unfold ambV
    rw [s02_line_gap_empty a b ha, Measure.restrict_empty, lintegral_zero_measure]

/-- Theorem 9.1 `thm:ambient` (`sec09-ambient.tex:36`), for curves through `∞`:
`c_K H(P) ≤ V(P) ≤ C_K H(P)` as extended integrals. -/
theorem thm_ambient :
    ∀ K : ℝ, 1 ≤ K → ∃ c C : ℝ≥0, 0 < c ∧ ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
      ∀ P ∈ UHS, (c : ℝ≥0∞) * ambH Ω Ωs P ≤ ambV Ω Ωs P ∧
        ambV Ω Ωs P ≤ (C : ℝ≥0∞) * ambH Ω Ωs P := by
  intro K hK
  obtain ⟨Cu, hu⟩ := s09_amb_upper K hK
  obtain ⟨Cl, hl⟩ := s09_amb_lower K hK
  have hm : (0 : ℝ≥0) < max Cl 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(max Cl 1)⁻¹, Cu, inv_pos.mpr hm, fun Ω Ωs hΩ P hP => ?_⟩
  by_cases hline : IsLinePair Ω Ωs
  · obtain ⟨h1, h2⟩ := thm_ambient_circle Ω Ωs hline P hP
    rw [h1, h2, mul_zero, mul_zero]
    exact ⟨le_rfl, le_rfl⟩
  refine ⟨?_, hu Ω Ωs hΩ hline P hP⟩
  calc (((max Cl 1)⁻¹ : ℝ≥0) : ℝ≥0∞) * ambH Ω Ωs P
      ≤ (((max Cl 1)⁻¹ : ℝ≥0) : ℝ≥0∞) * (((max Cl 1 : ℝ≥0) : ℝ≥0∞) * ambV Ω Ωs P) := by
        gcongr
        calc ambH Ω Ωs P ≤ (Cl : ℝ≥0∞) * ambV Ω Ωs P := hl Ω Ωs hΩ hline P hP
          _ ≤ _ := by
            gcongr
            exact_mod_cast le_max_left _ _
    _ = ambV Ω Ωs P := by
        rw [← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hm.ne', ENNReal.coe_one, one_mul]

/-- Theorem E (`sec01-intro.tex:334`) = Theorem 9.1 `thm:ambient`. -/
theorem thm_E :
    ∀ K : ℝ, 1 ≤ K → ∃ c C : ℝ≥0, 0 < c ∧ ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
      ∀ P ∈ UHS, (c : ℝ≥0∞) * ambH Ω Ωs P ≤ ambV Ω Ωs P ∧
        ambV Ω Ωs P ≤ (C : ℝ≥0∞) * ambH Ω Ωs P :=
  thm_ambient

/-- Theorem 9.1 `thm:ambient` (`sec09-ambient.tex:36`) for bounded `K`-quasicircles
(quantities transported through `invAt x₀`, `x₀ ∈ Γ`). -/
theorem thm_ambient_bdd :
    ∀ K : ℝ, 1 ≤ K → ∃ c C : ℝ≥0, 0 < c ∧ ∀ Ω Ωs : Set ℂ, IsBoundedKQuasicircle Ω Ωs K →
      ∀ x₀ ∈ curveOf Ω Ωs, ∀ P ∈ UHS, (c : ℝ≥0∞) * ambHBdd Ω Ωs x₀ P ≤ ambVBdd Ω Ωs x₀ P ∧
        ambVBdd Ω Ωs x₀ P ≤ (C : ℝ≥0∞) * ambHBdd Ω Ωs x₀ P := by
  intro K hK
  obtain ⟨c, C, hc, h⟩ := thm_ambient K hK
  refine ⟨c, C, hc, fun Ω Ωs hΓ x₀ hx₀ P hP => ?_⟩
  have hP' : invExt x₀ P ∈ UHS := by
    rw [← Set.mem_preimage, s09_invExt_UHS]
    exact hP
  exact h _ _ (s03_invPair_isKQuasiPair hΓ hx₀) _ hP'

/-- Remark 9.2 `rem:ambient-ren` (`sec09-ambient.tex:52`): with the constants of
Theorem 9.1, if `H(P) < ∞` then `(c_K - ½) H(P) ≤ Ren(P) ≤ (C_K - ½) H(P)`. -/
theorem rem_ambient_ren :
    ∀ K : ℝ, 1 ≤ K → ∃ c C : ℝ≥0, 0 < c ∧ ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
      ∀ P ∈ UHS, ((c : ℝ≥0∞) * ambH Ω Ωs P ≤ ambV Ω Ωs P ∧
          ambV Ω Ωs P ≤ (C : ℝ≥0∞) * ambH Ω Ωs P) ∧
        (ambH Ω Ωs P < ⊤ →
          ((((c : ℝ) - 1 / 2) * (ambH Ω Ωs P).toReal : ℝ) : EReal) ≤ ren Ω Ωs P ∧
            ren Ω Ωs P ≤ ((((C : ℝ) - 1 / 2) * (ambH Ω Ωs P).toReal : ℝ) : EReal)) := by
  intro K hK
  obtain ⟨c, C, hc, h⟩ := thm_ambient K hK
  refine ⟨c, C, hc, fun Ω Ωs hΓ P hP => ⟨h Ω Ωs hΓ P hP, fun hH => ?_⟩⟩
  obtain ⟨h1, h2⟩ := h Ω Ωs hΓ P hP
  have hCH : (C : ℝ≥0∞) * ambH Ω Ωs P ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hH.ne
  have hV : ambV Ω Ωs P ≠ ⊤ := ne_top_of_le_ne_top hCH h2
  have hH2 : ambH Ω Ωs P / 2 ≠ ⊤ := ENNReal.div_ne_top hH.ne two_ne_zero
  have e1 : ((ambV Ω Ωs P).toReal : EReal) = (ambV Ω Ωs P : EReal) :=
    EReal.coe_ennreal_toReal hV
  have e2 : (((ambH Ω Ωs P / 2).toReal : ℝ) : EReal) = ((ambH Ω Ωs P / 2 : ℝ≥0∞) : EReal) :=
    EReal.coe_ennreal_toReal hH2
  have e3 : (ambH Ω Ωs P / 2).toReal = (ambH Ω Ωs P).toReal / 2 := by
    rw [ENNReal.toReal_div]
    simp
  have hl : (c : ℝ) * (ambH Ω Ωs P).toReal ≤ (ambV Ω Ωs P).toReal := by
    have := ENNReal.toReal_mono hV h1
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal] at this
  have hu : (ambV Ω Ωs P).toReal ≤ (C : ℝ) * (ambH Ω Ωs P).toReal := by
    have := ENNReal.toReal_mono hCH h2
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal] at this
  unfold ren
  rw [← e1, ← e2, e3, ← EReal.coe_sub]
  constructor
  · exact EReal.coe_le_coe_iff.mpr (by linarith)
  · exact EReal.coe_le_coe_iff.mpr (by linarith)

/-! ## Consequences -/

/-- Corollary 9.8 `cor:ambient-families` (`sec09-ambient.tex:623`): `sup_α V(P_α) < ∞` iff
`sup_α H(P_α) < ∞`, and for sequences `V(P_n) → 0` iff `H(P_n) → 0`. -/
theorem cor_ambient_families {ι : Type*} (K : ℝ) (hK : 1 ≤ K) (Ω Ωs : Set ℂ)
    (hΓ : IsKQuasiPair Ω Ωs K) :
    (∀ P : ι → ℂ × ℝ, (∀ i, P i ∈ UHS) →
        ((⨆ i, ambV Ω Ωs (P i)) < ⊤ ↔ (⨆ i, ambH Ω Ωs (P i)) < ⊤)) ∧
      ∀ P : ℕ → ℂ × ℝ, (∀ n, P n ∈ UHS) →
        (Tendsto (fun n => ambV Ω Ωs (P n)) atTop (𝓝 0) ↔
          Tendsto (fun n => ambH Ω Ωs (P n)) atTop (𝓝 0)) := by
  obtain ⟨c, C, hc, h⟩ := thm_ambient K hK
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  have hci : (c : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hc0
  have hHV : ∀ P ∈ UHS, ambH Ω Ωs P ≤ (c : ℝ≥0∞)⁻¹ * ambV Ω Ωs P := by
    intro P hP
    calc ambH Ω Ωs P = (c : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) * ambH Ω Ωs P) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top, one_mul]
      _ ≤ (c : ℝ≥0∞)⁻¹ * ambV Ω Ωs P := by gcongr; exact (h Ω Ωs hΓ P hP).1
  have hVH : ∀ P ∈ UHS, ambV Ω Ωs P ≤ (C : ℝ≥0∞) * ambH Ω Ωs P := fun P hP =>
    (h Ω Ωs hΓ P hP).2
  refine ⟨fun P hP => ⟨fun hs => ?_, fun hs => ?_⟩, fun P hP => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  · refine lt_of_le_of_lt (iSup_le fun i => ?_) (ENNReal.mul_lt_top hci.lt_top hs)
    exact (hHV _ (hP i)).trans (by gcongr; exact le_iSup (fun i => ambV Ω Ωs (P i)) i)
  · refine lt_of_le_of_lt (iSup_le fun i => ?_)
      (ENNReal.mul_lt_top (ENNReal.coe_lt_top (r := C)) hs)
    exact (hVH _ (hP i)).trans (by gcongr; exact le_iSup (fun i => ambH Ω Ωs (P i)) i)
  · have := ENNReal.Tendsto.const_mul ht (Or.inr hci)
    rw [mul_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this
      (fun n => zero_le) (fun n => hHV _ (hP n))
  · have := ENNReal.Tendsto.const_mul ht (Or.inr (ENNReal.coe_ne_top (r := C)))
    rw [mul_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this
      (fun n => zero_le) (fun n => hVH _ (hP n))

theorem s09_box_kernel_formula (x : ℂ) (r : ℝ) (hr : 0 < r) (q : ℂ × ℝ) (hq : q ∈ UHS) :
    ambKernel (x, r) q = 4 * q.2 * r / (‖q.1 - x‖ ^ 2 + (q.2 + r) ^ 2) :=
  ((lem_ambient_kernel_a (x, r) hr).2 q hq).2.2

theorem s09_box_kernel_lower (x : ℂ) (r : ℝ) (hr : 0 < r) (q : ℂ × ℝ)
    (hq : q ∈ carlesonBox x r) : 4 / 5 * (q.2 / r) ≤ ambKernel (x, r) q := by
  simp only [carlesonBox, Set.mem_prod, Metric.mem_ball, Set.mem_Ioc] at hq
  obtain ⟨h1, hq0, hqr⟩ := hq
  rw [s09_box_kernel_formula x r hr q hq0]
  have hd : ‖q.1 - x‖ < r := by rw [← dist_eq_norm]; exact h1
  have hD : 0 < ‖q.1 - x‖ ^ 2 + (q.2 + r) ^ 2 := by positivity
  rw [le_div_iff₀ hD]
  have h5 : ‖q.1 - x‖ ^ 2 + (q.2 + r) ^ 2 ≤ 5 * r ^ 2 := by
    nlinarith [norm_nonneg (q.1 - x)]
  calc 4 / 5 * (q.2 / r) * (‖q.1 - x‖ ^ 2 + (q.2 + r) ^ 2) ≤ 4 / 5 * (q.2 / r) * (5 * r ^ 2) := by
        gcongr
    _ = 4 * q.2 * r := by field_simp

theorem s09_box_kernel_upper0 (x : ℂ) (r : ℝ) (hr : 0 < r) (q : ℂ × ℝ) (hq : q ∈ UHS) :
    ambKernel (x, r) q ≤ 4 * (q.2 / r) := by
  have hq0 : 0 < q.2 := hq
  rw [s09_box_kernel_formula x r hr q hq]
  have hD : 0 < ‖q.1 - x‖ ^ 2 + (q.2 + r) ^ 2 := by positivity
  rw [div_le_iff₀ hD]
  calc 4 * q.2 * r = 4 * (q.2 / r) * r ^ 2 := by field_simp
    _ ≤ 4 * (q.2 / r) * (‖q.1 - x‖ ^ 2 + (q.2 + r) ^ 2) := by
        gcongr
        nlinarith [sq_nonneg ‖q.1 - x‖]

theorem s09_box_kernel_shell (x : ℂ) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (q : ℂ × ℝ)
    (hq : q ∈ UHS) (hns : q ∉ carlesonBox x s) :
    ambKernel (x, r) q ≤ 4 * q.2 * r / s ^ 2 := by
  have hq0 : 0 < q.2 := hq
  rw [s09_box_kernel_formula x r hr q hq]
  simp only [carlesonBox, Set.mem_prod, Metric.mem_ball, Set.mem_Ioc, not_and, not_le] at hns
  have hD : s ^ 2 ≤ ‖q.1 - x‖ ^ 2 + (q.2 + r) ^ 2 := by
    by_cases h : dist q.1 x < s
    · have h2 := hns h hq0
      nlinarith [sq_nonneg ‖q.1 - x‖]
    · push_neg at h
      rw [dist_eq_norm] at h
      nlinarith [sq_nonneg (q.2 + r)]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hD

theorem s09_tsum_inv_two_pow_succ : ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (j + 1) = 1 := by
  rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem s09_box_pointwise (x : ℂ) (r : ℝ) (hr : 0 < r) (q : ℂ × ℝ) (hq : q ∈ UHS) :
    ENNReal.ofReal (ambKernel (x, r) q) ≤
      4 * (ENNReal.ofReal r⁻¹ *
          (carlesonBox x r).indicator (fun q : ℂ × ℝ => ENNReal.ofReal q.2) q) +
        16 * ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (j + 1) * (ENNReal.ofReal (2 ^ (j + 1) * r)⁻¹ *
          (carlesonBox x (2 ^ (j + 1) * r)).indicator (fun q : ℂ × ℝ => ENNReal.ofReal q.2) q) := by
  have hq0 : 0 < q.2 := hq
  by_cases h0 : q ∈ carlesonBox x r
  · rw [Set.indicator_of_mem h0]
    refine le_trans ?_ le_self_add
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le), show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    apply ENNReal.ofReal_le_ofReal
    rw [← div_eq_inv_mul]
    exact s09_box_kernel_upper0 x r hr q hq
  · have hex : ∃ m : ℕ, q ∈ carlesonBox x (2 ^ m * r) := by
      obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ((max (dist q.1 x) q.2 + 1) / r)
        (by norm_num : (1 : ℝ) < 2)
      refine ⟨m, ?_⟩
      simp only [carlesonBox, Set.mem_prod, Metric.mem_ball, Set.mem_Ioc]
      have : max (dist q.1 x) q.2 + 1 < 2 ^ m * r := by rwa [div_lt_iff₀ hr] at hm
      exact ⟨by linarith [le_max_left (dist q.1 x) q.2], hq0,
        by linarith [le_max_right (dist q.1 x) q.2]⟩
    classical
    obtain ⟨m, hm, hmin⟩ : ∃ m, q ∈ carlesonBox x (2 ^ m * r) ∧
        ∀ k < m, q ∉ carlesonBox x (2 ^ k * r) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hm
      exact h0 hm
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := Nat.exists_eq_succ_of_ne_zero hm0
    have hnj : q ∉ carlesonBox x (2 ^ j * r) := hmin j (by omega)
    refine le_trans ?_ le_add_self
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (ENNReal.le_tsum j) zero_le)
    rw [Set.indicator_of_mem hm]
    have e : (16 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ (j + 1) *
        (ENNReal.ofReal (2 ^ (j + 1) * r)⁻¹ * ENNReal.ofReal q.2)) =
        ENNReal.ofReal (16 * ((2 : ℝ)⁻¹ ^ (j + 1) * ((2 ^ (j + 1) * r)⁻¹ * q.2))) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (j + 1)),
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 ^ (j + 1) * r)⁻¹),
        ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2⁻¹),
        ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [e]
    apply ENNReal.ofReal_le_ofReal
    have hs := s09_box_kernel_shell x r (2 ^ j * r) hr (by positivity) q hq hnj
    refine le_trans hs (le_of_eq ?_)
    rw [inv_pow]
    field_simp
    ring

theorem s09_measurable_boxInd (x : ℂ) (s : ℝ) :
    Measurable ((carlesonBox x s).indicator (fun q : ℂ × ℝ => ENNReal.ofReal q.2)) :=
  (measurable_snd.ennreal_ofReal).indicator (measurableSet_ball.prod measurableSet_Ioc)

theorem s09_boxAvg_eq (μ : Measure (ℂ × ℝ)) (x : ℂ) (s : ℝ) :
    boxAvg μ x s = ∫⁻ q, ENNReal.ofReal s⁻¹ *
      (carlesonBox x s).indicator (fun q : ℂ × ℝ => ENNReal.ofReal q.2) q ∂μ := by
  have hQ : MeasurableSet (carlesonBox x s) := measurableSet_ball.prod measurableSet_Ioc
  rw [lintegral_const_mul _ (s09_measurable_boxInd x s), lintegral_indicator hQ]
  rfl

theorem s09_boxKernel_le (μ : Measure (ℂ × ℝ)) (x : ℂ) (r : ℝ) (hr : 0 < r) :
    boxKernel μ x r ≤ 4 * boxAvg μ x r +
      16 * ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (j + 1) * boxAvg μ x (2 ^ (j + 1) * r) := by
  have hm := s09_measurable_boxInd x
  unfold boxKernel
  refine le_trans (setLIntegral_mono' s09_isOpen_UHS.measurableSet
    (fun q hq => s09_box_pointwise x r hr q hq)) (le_trans (setLIntegral_le_lintegral _ _) ?_)
  rw [lintegral_add_left (((hm r).const_mul _).const_mul _),
    lintegral_const_mul _ ((hm r).const_mul _),
    lintegral_const_mul _ (Measurable.ennreal_tsum fun j => ((hm _).const_mul _).const_mul _),
    lintegral_tsum (fun j => (((hm _).const_mul _).const_mul _).aemeasurable),
    ← s09_boxAvg_eq]
  refine le_of_eq (congrArg (fun t => 4 * boxAvg μ x r + 16 * t) (tsum_congr fun j => ?_))
  rw [lintegral_const_mul _ ((hm _).const_mul _), ← s09_boxAvg_eq]

theorem s09_boxAvg_le_kernel (μ : Measure (ℂ × ℝ)) (x : ℂ) (r : ℝ) (hr : 0 < r) :
    (4 / 5 : ℝ≥0∞) * boxAvg μ x r ≤ boxKernel μ x r := by
  have hQ : MeasurableSet (carlesonBox x r) := measurableSet_ball.prod measurableSet_Ioc
  have hQU : carlesonBox x r ⊆ UHS := fun q hq => hq.2.1
  unfold boxAvg boxKernel
  rw [← mul_assoc, ← lintegral_const_mul _ measurable_snd.ennreal_ofReal]
  refine le_trans (setLIntegral_mono' hQ fun q hq => ?_) (lintegral_mono_set hQU)
  have h45 : (4 / 5 : ℝ≥0∞) = ENNReal.ofReal (4 / 5) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [h45, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4 / 5),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 / 5 * r⁻¹)]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_assoc, ← div_eq_inv_mul]
  exact s09_box_kernel_lower x r hr q hq

/-- Corollary 9.9(a) `cor:boxes`, (9.x) `eq:box-kernel` (`sec09-ambient.tex:644`): for every
positive Borel measure `μ` on `ℍ³`,
`⅘ A_μ(x,r) ≤ K_μ(x,r) ≤ 4 A_μ(x,r) + 16 ∑_{j≥1} 2^{-j} A_μ(x, 2^j r)`, hence
`⅘ sup A_μ ≤ sup K_μ ≤ 20 sup A_μ`. -/
theorem cor_boxes_a (μ : Measure (ℂ × ℝ)) :
    (∀ x : ℂ, ∀ r : ℝ, 0 < r →
      (4 / 5 : ℝ≥0∞) * boxAvg μ x r ≤ boxKernel μ x r ∧
        boxKernel μ x r ≤ 4 * boxAvg μ x r +
          16 * ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (j + 1) * boxAvg μ x (2 ^ (j + 1) * r)) ∧
      (4 / 5 : ℝ≥0∞) * (⨆ (x : ℂ) (r : ℝ) (_ : 0 < r), boxAvg μ x r) ≤
          ⨆ (x : ℂ) (r : ℝ) (_ : 0 < r), boxKernel μ x r ∧
        (⨆ (x : ℂ) (r : ℝ) (_ : 0 < r), boxKernel μ x r) ≤
          20 * ⨆ (x : ℂ) (r : ℝ) (_ : 0 < r), boxAvg μ x r := by
  refine ⟨fun x r hr => ⟨s09_boxAvg_le_kernel μ x r hr, s09_boxKernel_le μ x r hr⟩, ?_, ?_⟩
  · rw [ENNReal.mul_iSup]
    refine iSup_mono fun x => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_mono fun r => ?_
    rw [ENNReal.mul_iSup]
    exact iSup_mono fun hr => s09_boxAvg_le_kernel μ x r hr
  · have hS : ∀ y : ℂ, ∀ s : ℝ, 0 < s →
        boxAvg μ y s ≤ ⨆ (x : ℂ) (r : ℝ) (_ : 0 < r), boxAvg μ x r :=
      fun y s hs => le_iSup₂_of_le y s (le_iSup_of_le hs le_rfl)
    refine iSup_le fun x => iSup_le fun r => iSup_le fun hr => ?_
    refine le_trans (s09_boxKernel_le μ x r hr) ?_
    refine le_trans (add_le_add (mul_le_mul_of_nonneg_left (hS x r hr) zero_le)
      (mul_le_mul_of_nonneg_left (tsum_le_tsum fun j =>
        mul_le_mul_of_nonneg_left (hS x _ (by positivity)) zero_le) zero_le)) (le_of_eq ?_)
    rw [ENNReal.tsum_mul_right, s09_tsum_inv_two_pow_succ]
    ring

theorem s09_boxAvg_le_kernel' (μ : Measure (ℂ × ℝ)) (x : ℂ) (r : ℝ) (hr : 0 < r) :
    boxAvg μ x r ≤ (5 / 4 : ℝ≥0∞) * boxKernel μ x r := by
  have h45 : (4 / 5 : ℝ≥0∞) = ENNReal.ofReal (4 / 5) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have h54 : (5 / 4 : ℝ≥0∞) = ENNReal.ofReal (5 / 4) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have h1 : (5 / 4 : ℝ≥0∞) * (4 / 5) = 1 := by
    rw [h45, h54, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  calc boxAvg μ x r = (5 / 4 : ℝ≥0∞) * ((4 / 5) * boxAvg μ x r) := by
        rw [← mul_assoc, h1, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (s09_boxAvg_le_kernel μ x r hr) zero_le

theorem s09_tendsto_scale (c : ℝ) (hc : 0 < c) :
    Tendsto (fun r : ℝ => c * r) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have := ((tendsto_id (x := 𝓝 (0 : ℝ))).mono_left (nhdsWithin_le_nhds (s := Ioi 0))).const_mul c
    rwa [mul_zero] at this
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_pos hc hr

/-- Corollary 9.9(b) `cor:boxes` (`sec09-ambient.tex:651`): if `sup A_μ < ∞`, then
`sup_x K_μ(x,r) → 0` as `r → 0` iff `sup_x A_μ(x,r) → 0`. -/
theorem cor_boxes_b (μ : Measure (ℂ × ℝ))
    (hμ : (⨆ (x : ℂ) (r : ℝ) (_ : 0 < r), boxAvg μ x r) < ⊤) :
    Tendsto (fun r => ⨆ x : ℂ, boxKernel μ x r) (𝓝[>] 0) (𝓝 0) ↔
      Tendsto (fun r => ⨆ x : ℂ, boxAvg μ x r) (𝓝[>] 0) (𝓝 0) := by
  set M := ⨆ (x : ℂ) (r : ℝ) (_ : 0 < r), boxAvg μ x r with hMdef
  have hS : ∀ s : ℝ, 0 < s → (⨆ x : ℂ, boxAvg μ x s) ≤ M :=
    fun s hs => iSup_le fun y => le_iSup₂_of_le y s (le_iSup_of_le hs le_rfl)
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  constructor
  · intro hK
    have h2 : Tendsto (fun r => (5 / 4 : ℝ≥0∞) * ⨆ x : ℂ, boxKernel μ x r) (𝓝[>] 0) (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul hK (Or.inr (ENNReal.div_ne_top (by norm_num) (by norm_num) : (5 / 4 : ℝ≥0∞) ≠ ⊤))
      rwa [mul_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
      (Eventually.of_forall fun r => zero_le) ?_
    filter_upwards [hpos] with r hr
    exact iSup_le fun x => le_trans (s09_boxAvg_le_kernel' μ x r hr)
      (mul_le_mul_of_nonneg_left (le_iSup (fun y => boxKernel μ y r) x) zero_le)
  · intro hA
    have hT : Tendsto (fun r => ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (j + 1) *
        ⨆ x : ℂ, boxAvg μ x (2 ^ (j + 1) * r)) (𝓝[>] 0) (𝓝 0) := by
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
      have hgeo : Tendsto (fun N : ℕ => (2 : ℝ≥0∞)⁻¹ ^ N * M) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.mul_const
          (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1))
          (Or.inr hμ.ne)
        rwa [zero_mul] at this
      obtain ⟨N, hN⟩ := (hgeo.eventually (eventually_le_nhds hε2)).exists
      have hhead : Tendsto (fun r => ∑ j ∈ Finset.range N, (2 : ℝ≥0∞)⁻¹ ^ (j + 1) *
          ⨆ x : ℂ, boxAvg μ x (2 ^ (j + 1) * r)) (𝓝[>] 0) (𝓝 0) := by
        have := tendsto_finsetSum (Finset.range N) (fun j _ =>
          ENNReal.Tendsto.const_mul (hA.comp (s09_tendsto_scale (2 ^ (j + 1)) (by positivity)))
            (Or.inr (by simp : (2 : ℝ≥0∞)⁻¹ ^ (j + 1) ≠ ⊤)))
        simp only [mul_zero, Finset.sum_const_zero] at this
        exact this
      filter_upwards [hpos, (ENNReal.tendsto_nhds_zero.mp hhead) (ε / 2) hε2] with r hr hr2
      have htail : ∑' i : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (i + N + 1) *
          (⨆ x : ℂ, boxAvg μ x (2 ^ (i + N + 1) * r)) ≤ ε / 2 := by
        calc ∑' i : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (i + N + 1) * (⨆ x : ℂ, boxAvg μ x (2 ^ (i + N + 1) * r))
            ≤ ∑' i : ℕ, (2 : ℝ≥0∞)⁻¹ ^ N * ((2 : ℝ≥0∞)⁻¹ ^ (i + 1) * M) := by
              refine tsum_le_tsum fun i => ?_
              have e : (2 : ℝ≥0∞)⁻¹ ^ (i + N + 1) = (2 : ℝ≥0∞)⁻¹ ^ N * (2 : ℝ≥0∞)⁻¹ ^ (i + 1) := by
                rw [← pow_add]
                congr 1
                ring
              rw [e, mul_assoc]
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (hS _ (by positivity)) zero_le) zero_le
          _ = (2 : ℝ≥0∞)⁻¹ ^ N * M := by
              rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, s09_tsum_inv_two_pow_succ, one_mul]
          _ ≤ ε / 2 := hN
      rw [← (CompleteLattice.summable).sum_add_tsum_nat_add' (k := N)]
      exact le_trans (add_le_add hr2 htail) (ENNReal.add_halves ε).le
    have hF : Tendsto (fun r => 4 * (⨆ x : ℂ, boxAvg μ x r) + 16 * ∑' j : ℕ,
        (2 : ℝ≥0∞)⁻¹ ^ (j + 1) * ⨆ x : ℂ, boxAvg μ x (2 ^ (j + 1) * r)) (𝓝[>] 0) (𝓝 0) := by
      have := (ENNReal.Tendsto.const_mul hA (Or.inr (by norm_num : (4 : ℝ≥0∞) ≠ ⊤))).add
        (ENNReal.Tendsto.const_mul hT (Or.inr (by norm_num : (16 : ℝ≥0∞) ≠ ⊤)))
      rwa [mul_zero, mul_zero, add_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hF
      (Eventually.of_forall fun r => zero_le) ?_
    filter_upwards [hpos] with r hr
    refine iSup_le fun x => le_trans (s09_boxKernel_le μ x r hr) ?_
    exact add_le_add (mul_le_mul_of_nonneg_left (le_iSup (fun y => boxAvg μ y r) x) zero_le)
      (mul_le_mul_of_nonneg_left (tsum_le_tsum fun j => mul_le_mul_of_nonneg_left
        (le_iSup (fun y => boxAvg μ y (2 ^ (j + 1) * r)) x) zero_le) zero_le)

/-- Helper for `cor_boxes_c` (W-EPMEAS): `arcosh` is measurable. -/
theorem s09_bx_measurable_arcosh : Measurable Real.arcosh := by
  show Measurable fun x : ℝ => Real.log (x + √(x ^ 2 - 1))
  fun_prop

/-- Helper for `cor_boxes_c`: the kernel `q ↦ k_P(q)` is measurable. -/
theorem s09_bx_measurable_ambKernel (P : ℂ × ℝ) : Measurable (ambKernel P) := by
  have h := s09_bx_measurable_arcosh
  show Measurable fun q : ℂ × ℝ => ((Real.cosh (Real.arcosh
    (1 + (‖P.1 - q.1‖ ^ 2 + (P.2 - q.2) ^ 2) / (2 * P.2 * q.2)) / 2))⁻¹) ^ 2
  fun_prop

/-- Helper for `cor_boxes_c`: the curvature mass is absolutely continuous w.r.t. area on `Ω`. -/
theorem s09_bx_curvMass_ac (Ω : Set ℂ) : curvMass Ω ≪ volume.restrict Ω :=
  withDensity_absolutelyContinuous _ _

/-- Helper for `cor_boxes_c` (W-EPMEAS): the Epstein–Poincaré map of a simply connected `Ω` is
a.e.-measurable for the curvature mass (`λ_Ω` is continuous on `Ω`, and `∂_w log λ_Ω` is built
from Fréchet derivatives, which are measurable unconditionally). -/
theorem s09_bx_epstein_aemeas {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) :
    AEMeasurable (epstein Ω) (curvMass Ω) := by
  have hΩo : IsOpen Ω := by
    obtain ⟨f, hf⟩ := hΩ
    exact hf.isOpen isOpen_ball
  have hl : AEMeasurable (poincareDensity Ω) (volume.restrict Ω) :=
    (continuousOn_of_forall_continuousAt fun w hw =>
      s02_continuousAt_poincareDensity hΩ hw).aemeasurable hΩo.measurableSet
  have hA : Measurable (logDensityDz Ω) := by
    have h1 := measurable_fderiv_apply_const (𝕜 := ℝ)
      (f := fun x => Real.log (poincareDensity Ω x)) (1 : ℂ)
    have h2 := measurable_fderiv_apply_const (𝕜 := ℝ)
      (f := fun x => Real.log (poincareDensity Ω x)) I
    show Measurable fun w => (((fderiv ℝ (fun x => Real.log (poincareDensity Ω x)) w 1 : ℝ) : ℂ) -
      I * ((fderiv ℝ (fun x => Real.log (poincareDensity Ω x)) w I : ℝ) : ℂ)) / 2
    fun_prop
  have hg := hl.measurable_mk
  have hX : AEMeasurable (epstein Ω) (volume.restrict Ω) := by
    refine ⟨fun w => (w + 4 * conj (logDensityDz Ω w) /
        ((hl.mk _ w ^ 2 + 4 * ‖logDensityDz Ω w‖ ^ 2 : ℝ) : ℂ),
      2 * hl.mk _ w / (hl.mk _ w ^ 2 + 4 * ‖logDensityDz Ω w‖ ^ 2)), ?_, ?_⟩
    · fun_prop
    · filter_upwards [hl.ae_eq_mk] with w hw
      unfold epstein
      rw [hw]
  exact hX.mono_ac (s09_bx_curvMass_ac Ω)

/-- Helper for `cor_boxes_c`: the Epstein–Poincaré map of a simply connected `Ω` lands in `ℍ³`
for a.e. point of the curvature mass. -/
theorem s09_bx_epstein_ae_UHS {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) :
    ∀ᵐ w ∂curvMass Ω, epstein Ω w ∈ UHS := by
  have hΩo : IsOpen Ω := by
    obtain ⟨f, hf⟩ := hΩ
    exact hf.isOpen isOpen_ball
  have h1 : ∀ᵐ w ∂(volume.restrict Ω), w ∈ Ω := ae_restrict_mem hΩo.measurableSet
  filter_upwards [(s09_bx_curvMass_ac Ω).ae_le h1] with w hw
  exact s09_epstein_pos Ω hΩ w hw

/-- Helper for `cor_boxes_c`: `A_{μ_H} = A_μ` for the measure `μ = X_*(s² dâ) + X*_*(s*² dâ*)`
(the pull-back form of `boxAvgH`, made a push-forward by W-EPMEAS). -/
theorem s09_bx_boxAvgH_eq {Ω Ωs : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    (hΩs : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ωs) (x : ℂ) (r : ℝ) :
    boxAvgH Ω Ωs x r =
      boxAvg ((curvMass Ω).map (epstein Ω) + (curvMass Ωs).map (epstein Ωs)) x r := by
  have hQ : MeasurableSet (carlesonBox x r) := measurableSet_ball.prod measurableSet_Ioc
  unfold boxAvgH boxAvg
  rw [Measure.restrict_add, lintegral_add_measure, ← lintegral_indicator hQ,
    ← lintegral_indicator hQ,
    lintegral_map' (s09_measurable_boxInd x r).aemeasurable (s09_bx_epstein_aemeas hΩ),
    lintegral_map' (s09_measurable_boxInd x r).aemeasurable (s09_bx_epstein_aemeas hΩs)]

/-- Helper for `cor_boxes_c`: `K_{μ_H}(x, r) = H(x, r)` for `μ_H = X_*(s² dâ) + X*_*(s*² dâ*)`. -/
theorem s09_bx_kernel_eq {Ω Ωs : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    (hΩs : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ωs) (x : ℂ) (r : ℝ) :
    boxKernel ((curvMass Ω).map (epstein Ω) + (curvMass Ωs).map (epstein Ωs)) x r =
      ambH Ω Ωs (x, r) := by
  have hU : MeasurableSet UHS := measurableSet_lt measurable_const measurable_snd
  have hm : Measurable (UHS.indicator fun q => ENNReal.ofReal (ambKernel (x, r) q)) :=
    (s09_bx_measurable_ambKernel (x, r)).ennreal_ofReal.indicator hU
  unfold boxKernel ambH
  rw [Measure.restrict_add, lintegral_add_measure, ← lintegral_indicator hU,
    ← lintegral_indicator hU, lintegral_map' hm.aemeasurable (s09_bx_epstein_aemeas hΩ),
    lintegral_map' hm.aemeasurable (s09_bx_epstein_aemeas hΩs)]
  congr 1
  · refine lintegral_congr_ae ?_
    filter_upwards [s09_bx_epstein_ae_UHS hΩ] with w hw
    exact indicator_of_mem hw _
  · refine lintegral_congr_ae ?_
    filter_upwards [s09_bx_epstein_ae_UHS hΩs] with w hw
    exact indicator_of_mem hw _

/-- Helper for `cor_boxes_c`: `K_{vol|𝒩}(x, r) = V(x, r)` (`𝒩 ⊆ ℍ³`). -/
theorem s09_bx_kernel_vol (Ω Ωs : Set ℂ) (x : ℂ) (r : ℝ) :
    boxKernel (hvol.restrict (gap Ω Ωs)) x r = ambV Ω Ωs (x, r) := by
  have hU : MeasurableSet UHS := measurableSet_lt measurable_const measurable_snd
  unfold boxKernel ambV
  rw [Measure.restrict_restrict hU,
    inter_eq_right.mpr (show gap Ω Ωs ⊆ UHS from fun q hq => hq.1)]

/-- Helper for `cor_boxes_c`, the `μ_H` case of (9.x): `H(x, r) ≤ 4 A_H(x, r) +
16 Σ_j 2^{-j-1} A_H(x, 2^{j+1} r)`. -/
theorem s09_bx_H_le {Ω Ωs : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    (hΩs : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ωs) (x : ℂ) (r : ℝ) (hr : 0 < r) :
    ambH Ω Ωs (x, r) ≤ 4 * boxAvgH Ω Ωs x r +
      16 * ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (j + 1) * boxAvgH Ω Ωs x (2 ^ (j + 1) * r) := by
  simp only [s09_bx_boxAvgH_eq hΩ hΩs]
  rw [← s09_bx_kernel_eq hΩ hΩs]
  exact s09_boxKernel_le _ x r hr

/-- Helper for `cor_boxes_c`, the `μ_H` case of (9.x): `A_H(x, r) ≤ (5/4) H(x, r)`. -/
theorem s09_bx_AH_le {Ω Ωs : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    (hΩs : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ωs) (x : ℂ) (r : ℝ) (hr : 0 < r) :
    boxAvgH Ω Ωs x r ≤ (5 / 4 : ℝ≥0∞) * ambH Ω Ωs (x, r) := by
  rw [s09_bx_boxAvgH_eq hΩ hΩs, ← s09_bx_kernel_eq hΩ hΩs]
  exact s09_boxAvg_le_kernel' _ x r hr

/-- Helper for `cor_boxes_c`: `K_μ(x, r) ≤ 20 sup A_μ` (from (9.x), `Σ_j 2^{-j-1} = 1`). -/
theorem s09_bx_kernel_le_sup (μ : Measure (ℂ × ℝ)) (x : ℂ) (r : ℝ) (hr : 0 < r) :
    boxKernel μ x r ≤ 20 * ⨆ (y : ℂ) (s : ℝ) (_ : 0 < s), boxAvg μ y s := by
  set M := ⨆ (y : ℂ) (s : ℝ) (_ : 0 < s), boxAvg μ y s with hMdef
  have hS : ∀ y : ℂ, ∀ s : ℝ, 0 < s → boxAvg μ y s ≤ M :=
    fun y s hs => le_iSup₂_of_le y s (le_iSup_of_le hs le_rfl)
  calc boxKernel μ x r ≤ 4 * boxAvg μ x r +
        16 * ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (j + 1) * boxAvg μ x (2 ^ (j + 1) * r) :=
        s09_boxKernel_le μ x r hr
    _ ≤ 4 * M + 16 * ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (j + 1) * M :=
        add_le_add (mul_le_mul_of_nonneg_left (hS x r hr) zero_le)
          (mul_le_mul_of_nonneg_left (tsum_le_tsum fun j => mul_le_mul_of_nonneg_left
            (hS x _ (by positivity)) zero_le) zero_le)
    _ = 20 * M := by
        rw [ENNReal.tsum_mul_right, s09_tsum_inv_two_pow_succ, one_mul]
        ring

/-- Helper for `cor_boxes_c`: `(5/4) · 20 = 25` in `ℝ≥0∞`. -/
theorem s09_bx_25 : (5 / 4 : ℝ≥0∞) * 20 = 25 := by
  rw [show (20 : ℝ≥0∞) = 4 * 5 by norm_num, ← mul_assoc,
    ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
  norm_num

/-- Corollary 9.9(c) `cor:boxes` (`sec09-ambient.tex:653`), for curves through `∞`: with the
constants `c_K, C_K` of Theorem 9.1, `sup A_{vol|𝒩} ≤ 25 C_K sup A_{μ_H}` and
`sup A_{μ_H} ≤ 25 c_K⁻¹ sup A_{vol|𝒩}`; if these suprema are finite, the vanishing of
`sup_x A(x, r)` as `r → 0` is equivalent for the two measures.

Stated only for curves through `∞` (pairs `(Ω, Ωs)`).  The paper's "in any position" also covers
bounded curves in their original coordinates; that needs the gap and `μ_H` of a bounded curve in
original coordinates (the inverse Poincaré extension of `invAt x₀`), which are not defined. -/
theorem cor_boxes_c :
    ∀ K : ℝ, 1 ≤ K → ∃ c C : ℝ≥0, 0 < c ∧ (∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
      ∀ P ∈ UHS, (c : ℝ≥0∞) * ambH Ω Ωs P ≤ ambV Ω Ωs P ∧
        ambV Ω Ωs P ≤ (C : ℝ≥0∞) * ambH Ω Ωs P) ∧
      ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
        (⨆ (x : ℂ) (r : ℝ) (_ : 0 < r), boxAvg (hvol.restrict (gap Ω Ωs)) x r) ≤
            25 * (C : ℝ≥0∞) * ⨆ (x : ℂ) (r : ℝ) (_ : 0 < r), boxAvgH Ω Ωs x r ∧
          (⨆ (x : ℂ) (r : ℝ) (_ : 0 < r), boxAvgH Ω Ωs x r) ≤
            25 * (c : ℝ≥0∞)⁻¹ * ⨆ (x : ℂ) (r : ℝ) (_ : 0 < r),
              boxAvg (hvol.restrict (gap Ω Ωs)) x r ∧
          ((⨆ (x : ℂ) (r : ℝ) (_ : 0 < r), boxAvg (hvol.restrict (gap Ω Ωs)) x r) < ⊤ →
            (⨆ (x : ℂ) (r : ℝ) (_ : 0 < r), boxAvgH Ω Ωs x r) < ⊤ →
            (Tendsto (fun r => ⨆ x : ℂ, boxAvg (hvol.restrict (gap Ω Ωs)) x r) (𝓝[>] 0)
                (𝓝 0) ↔
              Tendsto (fun r => ⨆ x : ℂ, boxAvgH Ω Ωs x r) (𝓝[>] 0) (𝓝 0))) := by
  intro K hK
  obtain ⟨c, C, hc, hamb⟩ := thm_ambient K hK
  refine ⟨c, C, hc, hamb, fun Ω Ωs h => ?_⟩
  have hJ := s03_b0_jordanPair h
  have hΩ := s02_jordanPair_riemannMap hJ
  have hΩs := s02_jordanPair_riemannMap (s02_jordanPair_symm hJ)
  obtain ⟨μH, hμH⟩ : ∃ μ : Measure (ℂ × ℝ),
      μ = (curvMass Ω).map (epstein Ω) + (curvMass Ωs).map (epstein Ωs) := ⟨_, rfl⟩
  have hAeq : ∀ x r, boxAvgH Ω Ωs x r = boxAvg μH x r := fun x r => by
    rw [hμH]
    exact s09_bx_boxAvgH_eq hΩ hΩs x r
  have hKeq : ∀ x r, boxKernel μH x r = ambH Ω Ωs (x, r) := fun x r => by
    rw [hμH]
    exact s09_bx_kernel_eq hΩ hΩs x r
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  have hHV : ∀ x : ℂ, ∀ r : ℝ, 0 < r →
      ambH Ω Ωs (x, r) ≤ (c : ℝ≥0∞)⁻¹ * ambV Ω Ωs (x, r) := fun x r hr => by
    calc ambH Ω Ωs (x, r) = (c : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) * ambH Ω Ωs (x, r)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top, one_mul]
      _ ≤ (c : ℝ≥0∞)⁻¹ * ambV Ω Ωs (x, r) :=
          mul_le_mul_of_nonneg_left (hamb Ω Ωs h (x, r) hr).1 zero_le
  simp only [hAeq]
  refine ⟨?_, ?_, ?_⟩
  · refine iSup_le fun x => iSup_le fun r => iSup_le fun hr => ?_
    calc boxAvg (hvol.restrict (gap Ω Ωs)) x r
        ≤ (5 / 4 : ℝ≥0∞) * boxKernel (hvol.restrict (gap Ω Ωs)) x r :=
          s09_boxAvg_le_kernel' _ x r hr
      _ = (5 / 4 : ℝ≥0∞) * ambV Ω Ωs (x, r) := by rw [s09_bx_kernel_vol]
      _ ≤ (5 / 4 : ℝ≥0∞) * ((C : ℝ≥0∞) * boxKernel μH x r) := by
          rw [hKeq]
          exact mul_le_mul_of_nonneg_left (hamb Ω Ωs h (x, r) hr).2 zero_le
      _ ≤ (5 / 4 : ℝ≥0∞) * ((C : ℝ≥0∞) * (20 * ⨆ (y : ℂ) (s : ℝ) (_ : 0 < s), boxAvg μH y s)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (s09_bx_kernel_le_sup μH x r hr) zero_le) zero_le
      _ = 25 * (C : ℝ≥0∞) * ⨆ (y : ℂ) (s : ℝ) (_ : 0 < s), boxAvg μH y s := by
          rw [← s09_bx_25]
          ring
  · refine iSup_le fun x => iSup_le fun r => iSup_le fun hr => ?_
    calc boxAvg μH x r ≤ (5 / 4 : ℝ≥0∞) * boxKernel μH x r := s09_boxAvg_le_kernel' _ x r hr
      _ = (5 / 4 : ℝ≥0∞) * ambH Ω Ωs (x, r) := by rw [hKeq]
      _ ≤ (5 / 4 : ℝ≥0∞) * ((c : ℝ≥0∞)⁻¹ * boxKernel (hvol.restrict (gap Ω Ωs)) x r) := by
          rw [s09_bx_kernel_vol]
          exact mul_le_mul_of_nonneg_left (hHV x r hr) zero_le
      _ ≤ (5 / 4 : ℝ≥0∞) * ((c : ℝ≥0∞)⁻¹ *
            (20 * ⨆ (y : ℂ) (s : ℝ) (_ : 0 < s), boxAvg (hvol.restrict (gap Ω Ωs)) y s)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (s09_bx_kernel_le_sup _ x r hr) zero_le) zero_le
      _ = 25 * (c : ℝ≥0∞)⁻¹ *
            ⨆ (y : ℂ) (s : ℝ) (_ : 0 < s), boxAvg (hvol.restrict (gap Ω Ωs)) y s := by
          rw [← s09_bx_25]
          ring
  · intro hV hH
    rw [← cor_boxes_b _ hV, ← cor_boxes_b _ hH]
    simp only [hKeq, s09_bx_kernel_vol]
    have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
    constructor
    · intro hT
      have h2 := ENNReal.Tendsto.const_mul hT (Or.inr (ENNReal.inv_ne_top.mpr hc0))
      rw [mul_zero] at h2
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
        (Eventually.of_forall fun r => zero_le) ?_
      filter_upwards [hpos] with r hr
      exact iSup_le fun x => (hHV x r hr).trans (mul_le_mul_of_nonneg_left
        (le_iSup (fun y => ambV Ω Ωs (y, r)) x) zero_le)
    · intro hT
      have h2 := ENNReal.Tendsto.const_mul hT (Or.inr (ENNReal.coe_ne_top (r := C)))
      rw [mul_zero] at h2
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
        (Eventually.of_forall fun r => zero_le) ?_
      filter_upwards [hpos] with r hr
      exact iSup_le fun x => (hamb Ω Ωs h (x, r) hr).2.trans (mul_le_mul_of_nonneg_left
        (le_iSup (fun y => ambH Ω Ωs (y, r)) x) zero_le)

/-! ## Chord-arc curves -/

/-- Hausdorff length bound for a holomorphic map on a convex piece with bounded derivative. -/
theorem s09_af0_piece (F : ℂ → ℂ) (O B S : Set ℂ) (hO : IsOpen O) (hF : DifferentiableOn ℂ F O)
    (hB : Convex ℝ B) (hBO : B ⊆ O) (K : ℝ) (hK : ∀ x ∈ B, ‖deriv F x‖ ≤ K) (hSB : S ⊆ B) :
    μH[1] (F '' S) ≤ ENNReal.ofReal K * μH[1] S := by
  have hL : LipschitzOnWith K.toNNReal F B := by
    refine hB.lipschitzOnWith_of_nnnorm_deriv_le (fun x hx => hF.differentiableAt
      (hO.mem_nhds (hBO hx))) (fun x hx => ?_)
    calc ‖deriv F x‖₊ = (‖deriv F x‖).toNNReal := by rw [← coe_nnnorm, Real.toNNReal_coe]
      _ ≤ K.toNNReal := Real.toNNReal_le_toNNReal (hK x hx)
  have := (hL.mono hSB).hausdorffMeasure_image_le (d := 1) zero_le_one
  rwa [ENNReal.rpow_one] at this

/-- For every `η > 0`, `Λ¹(F(E)) ≤ (M + η) Λ¹(E)` when `|F'| ≤ M` on `closure E`. -/
theorem s09_af0_eta (F : ℂ → ℂ) (O E : Set ℂ) (hO : IsOpen O) (hF : DifferentiableOn ℂ F O)
    (hE : IsCompact (closure E)) (hEO : closure E ⊆ O) (M : ℝ)
    (hM : ∀ z ∈ closure E, ‖deriv F z‖ ≤ M) (hcont : ContinuousOn (fun z => ‖deriv F z‖) O)
    (η : ℝ) (hη : 0 < η) :
    μH[1] (F '' E) ≤ ENNReal.ofReal (M + η) * μH[1] E := by
  set G := O ∩ (fun z => ‖deriv F z‖) ⁻¹' Iio (M + η) with hGdef
  have hG : IsOpen G := hcont.isOpen_inter_preimage hO isOpen_Iio
  have hEG : closure E ⊆ G := fun z hz => ⟨hEO hz, by
    show ‖deriv F z‖ < M + η
    linarith [hM z hz]⟩
  obtain ⟨δ, hδ, hthick⟩ := hE.exists_thickening_subset_open hG hEG
  set u := TopologicalSpace.denseSeq ℂ
  set B : ℕ → Set ℂ := fun n => ball (u n) (δ / 2) with hBdef
  have hBcov : ⋃ n, B n = univ := by
    refine eq_univ_of_forall fun z => ?_
    obtain ⟨n, hn⟩ := Metric.denseRange_iff.mp (TopologicalSpace.denseRange_denseSeq ℂ) z
      (δ / 2) (by positivity)
    exact mem_iUnion.mpr ⟨n, hn⟩
  set P := disjointed B with hPdef
  have hPcov : ⋃ n, P n = univ := by rw [hPdef, iUnion_disjointed, hBcov]
  have hPm : ∀ n, MeasurableSet (P n) := MeasurableSet.disjointed fun n => measurableSet_ball
  set T := toMeasurable μH[1] E with hTdef
  have hpiece : ∀ n, μH[1] (F '' (E ∩ P n)) ≤ ENNReal.ofReal (M + η) * μH[1] (T ∩ P n) := by
    intro n
    by_cases hne : (E ∩ B n).Nonempty
    · obtain ⟨e, heE, heB⟩ := hne
      have hBe : B n ⊆ ball e δ := by
        refine ball_subset_ball' ?_
        have : dist (u n) e < δ / 2 := by
          rw [dist_comm]
          exact heB
        linarith
      have hBG : B n ⊆ G := hBe.trans ((ball_subset_thickening (subset_closure heE) δ).trans
        hthick)
      refine (s09_af0_piece F O (B n) (E ∩ P n) hO hF (convex_ball _ _)
        (fun x hx => (hBG hx).1) (M + η) (fun x hx => (hBG hx).2.le)
        ((inter_subset_right).trans (disjointed_subset B n))).trans ?_
      gcongr
      exact subset_toMeasurable (μH[1] : Measure ℂ) E
    · have : E ∩ P n = ∅ := by
        rw [not_nonempty_iff_eq_empty] at hne
        exact subset_empty_iff.mp (hne ▸ inter_subset_inter_right _ (disjointed_subset B n))
      rw [this, image_empty]
      simp
  have hcovE : F '' E ⊆ ⋃ n, F '' (E ∩ P n) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hPcov ▸ mem_univ z : z ∈ ⋃ n, P n)
    exact mem_iUnion.mpr ⟨n, z, ⟨hz, hn⟩, rfl⟩
  have hsum : ∑' n, μH[1] (T ∩ P n) = μH[1] E := by
    rw [← measure_iUnion (fun i j hij => ((disjoint_disjointed B hij).mono inter_subset_right
      inter_subset_right)) (fun n => (measurableSet_toMeasurable _ _).inter (hPm n)),
      ← inter_iUnion, hPcov, inter_univ, measure_toMeasurable]
  calc μH[1] (F '' E) ≤ μH[1] (⋃ n, F '' (E ∩ P n)) := measure_mono hcovE
    _ ≤ ∑' n, μH[1] (F '' (E ∩ P n)) := measure_iUnion_le _
    _ ≤ ∑' n, ENNReal.ofReal (M + η) * μH[1] (T ∩ P n) := tsum_le_tsum hpiece
    _ = ENNReal.ofReal (M + η) * μH[1] E := by rw [ENNReal.tsum_mul_left, hsum]

/-- If `F' = 0` on `E ⊆ O`, then `F(E)` is countable, hence `Λ¹`-null. -/
theorem s09_af0_null (F : ℂ → ℂ) (O E : Set ℂ) (hO : IsOpen O) (hF : DifferentiableOn ℂ F O)
    (hEO : E ⊆ O) (h0 : ∀ z ∈ E, deriv F z = 0) : μH[1] (F '' E) = 0 := by
  have hA : AnalyticOnNhd ℂ (deriv F) O := (hF.analyticOnNhd hO).deriv
  have hloc : ∀ z : E, ∃ U : Set ℂ, IsOpen U ∧ (z : ℂ) ∈ U ∧ ∀ w ∈ E ∩ U, F w = F z := by
    intro z
    rcases (hA z (hEO z.2)).eventually_eq_zero_or_eventually_ne_zero with h1 | h2
    · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp
        (h1.and (hO.mem_nhds (hEO z.2)))
      have hL : LipschitzOnWith 0 F (ball (z : ℂ) ε) := by
        refine (convex_ball (z : ℂ) ε).lipschitzOnWith_of_nnnorm_deriv_le
          (fun x hx => hF.differentiableAt (hO.mem_nhds (hball x hx).2)) (fun x hx => ?_)
        rw [(hball x hx).1, nnnorm_zero]
      refine ⟨ball (z : ℂ) ε, isOpen_ball, mem_ball_self hε, fun w hw => ?_⟩
      have := hL.dist_le_mul _ hw.2 _ (mem_ball_self hε)
      simp only [NNReal.coe_zero, zero_mul] at this
      exact dist_le_zero.mp this
    · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp
        (eventually_nhdsWithin_iff.mp h2)
      refine ⟨ball (z : ℂ) ε, isOpen_ball, mem_ball_self hε, fun w hw => ?_⟩
      by_cases hwz : w = z
      · rw [hwz]
      · exact absurd (h0 w hw.1) (hball w hw.2 hwz)
  choose U hUo hzU hUF using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
  have hsub : F '' E ⊆ (fun z : E => F z) '' T := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w ∈ ⋃ i ∈ T, U i := by
      rw [hTU]
      exact mem_iUnion.mpr ⟨⟨w, hw⟩, hzU _⟩
    obtain ⟨i, hi, hwi⟩ := mem_iUnion₂.mp hw'
    exact ⟨i, hi, (hUF i w ⟨hw, hwi⟩).symm⟩
  have := Measure.nullSingletonClass_hausdorff ℂ (d := 1) one_pos
  exact measure_mono_null hsub ((hTc.image _).measure_zero _)

/-- Lemma 9.10(0) `lem:arc-facts` (`sec09-ambient.tex:718`): for `F` holomorphic on an open
`O` and `E` with compact closure in `O`, `Λ¹(F(E)) ≤ (sup_E |F'|) Λ¹(E)`. -/
theorem lem_arc_facts_0 (F : ℂ → ℂ) (O E : Set ℂ) (hO : IsOpen O)
    (hF : DifferentiableOn ℂ F O) (hE : IsCompact (closure E)) (hEO : closure E ⊆ O) :
    μH[1] (F '' E) ≤ ENNReal.ofReal (sSup ((fun z => ‖deriv F z‖) '' E)) * μH[1] E := by
  set M := sSup ((fun z => ‖deriv F z‖) '' E) with hMdef
  have hcont : ContinuousOn (fun z => ‖deriv F z‖) O :=
    (hF.analyticOnNhd hO).deriv.continuousOn.norm
  have hbdd : BddAbove ((fun z => ‖deriv F z‖) '' E) :=
    (hE.image_of_continuousOn (hcont.mono hEO)).bddAbove.mono (image_mono subset_closure)
  have hMcl : ∀ z ∈ closure E, ‖deriv F z‖ ≤ M := by
    intro z hz
    have h1 : (fun z => ‖deriv F z‖) '' closure E ⊆ closure ((fun z => ‖deriv F z‖) '' E) :=
      (hcont.mono hEO).image_closure
    have h2 : closure ((fun z => ‖deriv F z‖) '' E) ⊆ Iic M :=
      closure_minimal (fun _ hy => le_csSup hbdd hy) isClosed_Iic
    exact h2 (h1 ⟨z, hz, rfl⟩)
  rcases eq_or_ne (μH[1] E) ⊤ with htop | hfin
  · by_cases hM : 0 < M
    · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hM).ne']
      exact le_top
    · replace hM := not_lt.mp hM
      rw [s09_af0_null F O E hO hF (subset_closure.trans hEO) (fun z hz =>
        norm_le_zero_iff.mp ((hMcl z (subset_closure hz)).trans hM))]
      exact zero_le
  · have hlim : Tendsto (fun η : ℝ => ENNReal.ofReal (M + η) * μH[1] E) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal M * μH[1] E)) := by
      refine ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal ?_) (Or.inr hfin)
      have := ((tendsto_id (x := 𝓝 (0 : ℝ))).mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))).const_add M
      rwa [add_zero] at this
    exact ge_of_tendsto hlim (by
      filter_upwards [self_mem_nhdsWithin] with η hη
      exact s09_af0_eta F O E hO hF hE hEO M hMcl hcont η hη)

/-- Helper for `lem_arc_facts_1`: a Jordan curve `Γ ∋ x` is the image of `[0,1]` under a
continuous `φ` with `φ 0 = φ 1 = x`, injective on `[0,1)`. -/
theorem s09_af1_param (Γ : Set ℂ) (hΓ : IsJordanCurveC Γ) (x : ℂ) (hx : x ∈ Γ) :
    ∃ φ : ℝ → ℂ, Continuous φ ∧ φ 0 = x ∧ φ 1 = x ∧ InjOn φ (Ico 0 1) ∧ φ '' Icc 0 1 = Γ := by
  obtain ⟨g, hg, hgi, hrange⟩ := hΓ
  obtain ⟨c₀, rfl⟩ : ∃ c₀, g c₀ = x := by
    rw [← hrange] at hx
    exact hx
  have hpi : (0 : ℝ) < 2 * π := by positivity
  refine ⟨fun t => g (c₀ * Circle.exp (2 * π * t)), ?_, ?_, ?_, ?_, ?_⟩
  · exact hg.comp (continuous_const.mul
      (Circle.exp.continuous.comp (continuous_const.mul continuous_id)))
  · show g (c₀ * Circle.exp (2 * π * 0)) = g c₀
    rw [mul_zero, Circle.exp_zero, mul_one]
  · show g (c₀ * Circle.exp (2 * π * 1)) = g c₀
    rw [mul_one, ← zero_add (2 * π), Circle.exp_add_two_pi, Circle.exp_zero, mul_one]
  · intro a ha b hb hab
    have h1 : c₀ * Circle.exp (2 * π * a) = c₀ * Circle.exp (2 * π * b) := hgi hab
    have h2 : Circle.exp (2 * π * a) = Circle.exp (2 * π * b) := mul_left_cancel h1
    have hIco : ∀ t ∈ Ico (0 : ℝ) 1, 2 * π * t ∈ Ico (0 : ℝ) (2 * π) := fun t ht =>
      ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
    have h3 := Circle.exp_injOn_Ico (a := 0) (b := 2 * π) (by linarith) (hIco a ha)
      (hIco b hb) h2
    exact mul_left_cancel₀ hpi.ne' h3
  · rw [← hrange]
    apply Subset.antisymm
    · rintro _ ⟨t, -, rfl⟩
      exact mem_range_self _
    · rintro _ ⟨c, rfl⟩
      obtain ⟨θ, hθ⟩ := Circle.exp_surjective (c₀⁻¹ * c)
      have hm := toIcoMod_mem_Ico hpi 0 θ
      rw [zero_add] at hm
      have hsub := toIcoMod_sub_self hpi 0 θ
      rw [zsmul_eq_mul] at hsub
      refine ⟨toIcoMod hpi 0 θ / (2 * π), ⟨div_nonneg hm.1 hpi.le, ?_⟩, ?_⟩
      · rw [div_le_one hpi]
        exact hm.2.le
      · show g (c₀ * Circle.exp (2 * π * (toIcoMod hpi 0 θ / (2 * π)))) = g c
        rw [mul_div_cancel₀ _ hpi.ne']
        have he : Circle.exp (toIcoMod hpi 0 θ) = Circle.exp θ := by
          refine Circle.exp_eq_exp.2 ⟨-toIcoDiv hpi 0 θ, ?_⟩
          push_cast at hsub ⊢
          linarith
        rw [he, hθ, mul_inv_cancel_left]

/-- Helper for `lem_arc_facts_1`: an arc of `Γ = φ([0,1])` from `φ 0` to `φ s`, `0 < s < 1`,
contains one of the two sub-arcs `φ([0,s])`, `φ([s,1])` (by connectedness). -/
theorem s09_af1_contain (Γ : Set ℂ) (φ : ℝ → ℂ) (hφ : Continuous φ) (h10 : φ 1 = φ 0)
    (hinj : InjOn φ (Ico 0 1)) (hΓ : φ '' Icc 0 1 = Γ) (s : ℝ) (hs : s ∈ Ioo 0 1) (γ : Set ℂ)
    (hγ : IsArcOf Γ (φ 0) (φ s) γ) : φ '' Icc 0 s ⊆ γ ∨ φ '' Icc s 1 ⊆ γ := by
  -- `hs` is not needed: the cut points `p₁ < s < p₂` found below already force `0 < s < 1`.
  have _h := hs
  obtain ⟨hγΓ, h, hhc, -, hh0, hh1, hhim⟩ := hγ
  have hγc : IsPreconnected γ := by
    rw [← hhim]
    exact isPreconnected_Icc.image _ hhc
  have h0γ : φ 0 ∈ γ := by
    rw [← hhim]
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, hh0⟩
  have hsγ : φ s ∈ γ := by
    rw [← hhim]
    exact ⟨1, ⟨zero_le_one, le_rfl⟩, hh1⟩
  by_contra hcon
  rw [not_or, not_subset, not_subset] at hcon
  obtain ⟨⟨_, ⟨p₁, hp₁, rfl⟩, hp₁γ⟩, ⟨_, ⟨p₂, hp₂, rfl⟩, hp₂γ⟩⟩ := hcon
  have hp₁0 : 0 < p₁ := lt_of_le_of_ne hp₁.1 (fun e => hp₁γ (by rw [← e]; exact h0γ))
  have hp₁s : p₁ < s := lt_of_le_of_ne hp₁.2 (fun e => hp₁γ (by rw [e]; exact hsγ))
  have hp₂s : s < p₂ := lt_of_le_of_ne hp₂.1 (fun e => hp₂γ (by rw [← e]; exact hsγ))
  have hp₂1 : p₂ < 1 := lt_of_le_of_ne hp₂.2 (fun e => hp₂γ (by rw [e, h10]; exact h0γ))
  -- the two closed pieces of `Γ` cut at `φ p₁`, `φ p₂`
  have hclaim : ∀ a ∈ Icc (0 : ℝ) p₁ ∪ Icc p₂ 1, ∀ b ∈ Icc p₁ p₂, φ a = φ b →
      b = p₁ ∨ b = p₂ := by
    intro a ha b hb hab
    have hbI : b ∈ Ico (0 : ℝ) 1 := ⟨by linarith [hb.1], by linarith [hb.2]⟩
    rcases eq_or_ne a 1 with ha1 | ha1
    · rw [ha1, h10] at hab
      have := hinj ⟨le_rfl, zero_lt_one⟩ hbI hab
      linarith [hb.1]
    · have haI : a ∈ Ico (0 : ℝ) 1 := by
        rcases ha with ha | ha
        · exact ⟨ha.1, by linarith [ha.2]⟩
        · exact ⟨by linarith [ha.1], lt_of_le_of_ne ha.2 ha1⟩
      have hab' := hinj haI hbI hab
      rcases ha with ha | ha
      · left
        linarith [ha.2, hb.1]
      · right
        linarith [ha.1, hb.2]
  have hK₁ : IsCompact (φ '' (Icc (0 : ℝ) p₁ ∪ Icc p₂ 1)) :=
    (isCompact_Icc.union isCompact_Icc).image hφ
  have hK₂ : IsCompact (φ '' Icc p₁ p₂) := isCompact_Icc.image hφ
  obtain ⟨w, hwγ, hw1, hw2⟩ := hγc _ _ hK₁.isClosed.isOpen_compl hK₂.isClosed.isOpen_compl
    (by
      intro w hwγ
      by_contra hw
      rw [mem_union, mem_compl_iff, mem_compl_iff, not_or, not_not, not_not] at hw
      obtain ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩ := hw
      rcases hclaim a ha b hb hab.symm with e | e
      · rw [e] at hab
        exact hp₁γ (hab ▸ hwγ)
      · rw [e] at hab
        exact hp₂γ (hab ▸ hwγ))
    ⟨φ s, hsγ, by
      rintro ⟨a, ha, hab⟩
      rcases hclaim a ha s ⟨hp₁s.le, hp₂s.le⟩ hab with e | e
      · linarith
      · linarith⟩
    ⟨φ 0, h0γ, by
      rintro ⟨b, hb, hab⟩
      rcases hclaim 0 (Or.inl ⟨le_rfl, hp₁0.le⟩) b hb hab.symm with e | e
      · rw [e] at hab
        exact hp₁γ (hab ▸ h0γ)
      · rw [e] at hab
        exact hp₂γ (hab ▸ h0γ)⟩
  have hwΓ := hγΓ hwγ
  rw [← hΓ] at hwΓ
  obtain ⟨t, ht, rfl⟩ := hwΓ
  rcases le_or_gt t p₁ with h1 | h1
  · exact hw1 ⟨t, Or.inl ⟨ht.1, h1⟩, rfl⟩
  rcases le_or_gt t p₂ with h2 | h2
  · exact hw2 ⟨t, ⟨h1.le, h2⟩, rfl⟩
  · exact hw1 ⟨t, Or.inr ⟨h2.le, ht.2⟩, rfl⟩

/-- Helper for `lem_arc_facts_1`: the union of a monotone real-indexed family of sets over any
index set `S` has measure at most a common bound of the members (no measurability). -/
theorem s09_af1_mono_union {X : Type*} [MeasurableSpace X] (μ : Measure X) (F : ℝ → Set X)
    (hF : Monotone F) (S : Set ℝ) (B : ℝ≥0∞) (hB : ∀ s ∈ S, μ (F s) ≤ B) :
    μ (⋃ s ∈ S, F s) ≤ B := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, biUnion_empty, measure_empty]
    exact zero_le
  obtain ⟨u, huS, hcof⟩ : ∃ u : ℕ → ℝ, (∀ n, u n ∈ S) ∧ ∀ s ∈ S, ∃ n, s ≤ u n := by
    by_cases hb : BddAbove S
    · by_cases hm : sSup S ∈ S
      · exact ⟨fun _ => sSup S, fun _ => hm, fun s hs => ⟨0, le_csSup hb hs⟩⟩
      · obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sSup hS hb
        refine ⟨u, huS, fun s hs => ?_⟩
        have hlt : s < sSup S := lt_of_le_of_ne (le_csSup hb hs) (fun e => hm (e ▸ hs))
        obtain ⟨n, hn⟩ := (hu.eventually (lt_mem_nhds hlt)).exists
        exact ⟨n, hn.le⟩
    · have hex : ∀ n : ℕ, ∃ t ∈ S, (n : ℝ) < t := fun n => by
        by_contra hn
        simp only [not_exists, not_and, not_lt] at hn
        exact hb ⟨n, fun t ht => hn t ht⟩
      choose u huS hu using hex
      refine ⟨u, huS, fun s hs => ?_⟩
      obtain ⟨n, hn⟩ := exists_nat_ge s
      exact ⟨n, hn.trans (hu n).le⟩
  have hsub : (⋃ s ∈ S, F s) ⊆ ⋃ n, F (u n) := by
    intro y hy
    obtain ⟨s, hs, hys⟩ := mem_iUnion₂.mp hy
    obtain ⟨n, hn⟩ := hcof s hs
    exact mem_iUnion.mpr ⟨n, hF hn hys⟩
  have hdir : Directed (· ⊆ ·) (fun n => F (u n)) := fun m n => by
    rcases le_total (u m) (u n) with h | h
    · exact ⟨n, hF h, le_rfl⟩
    · exact ⟨m, le_rfl, hF h⟩
  calc μ (⋃ s ∈ S, F s) ≤ μ (⋃ n, F (u n)) := measure_mono hsub
    _ = ⨆ n, μ (F (u n)) := hdir.measure_iUnion
    _ ≤ B := iSup_le fun n => hB _ (huS n)

/-- Lemma 9.10(1) `lem:arc-facts` (`sec09-ambient.tex:721`): chord-arc with constant `C`
implies Ahlfors regular with constant `4C`. -/
theorem lem_arc_facts_1 (Γ : Set ℂ) (hΓ : IsJordanCurveC Γ) (C : ℝ) (h : IsChordArc Γ C) :
    IsAhlforsRegular Γ (4 * C) := by
  intro z r hr
  rcases (Γ ∩ ball z r).eq_empty_or_nonempty with he | ⟨x, hxΓ, hxb⟩
  · rw [he, measure_empty]
    exact zero_le
  obtain ⟨φ, hφ, hφ0, hφ1, hinj, hφΓ⟩ := s09_af1_param Γ hΓ x hxΓ
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ≥0∞, B = ENNReal.ofReal (2 * C * r) := ⟨_, rfl⟩
  have hB : ∀ s ∈ Ioo (0 : ℝ) 1, φ s ∈ ball z r →
      μH[1] (φ '' Icc 0 s) ≤ B ∨ μH[1] (φ '' Icc s 1) ≤ B := by
    intro s hs hsb
    have hsΓ : φ s ∈ Γ := by
      rw [← hφΓ]
      exact mem_image_of_mem φ (Ioo_subset_Icc_self hs)
    have hne : x ≠ φ s := by
      intro h'
      have h0s : (0 : ℝ) = s :=
        hinj ⟨le_rfl, one_pos⟩ ⟨hs.1.le, hs.2⟩ (hφ0.trans h')
      exact hs.1.ne h0s
    obtain ⟨γ, hγ, hγμ⟩ := h.2 x hxΓ (φ s) hsΓ hne
    have hdist : dist x (φ s) < 2 * r := by
      calc dist x (φ s) ≤ dist x z + dist (φ s) z := dist_triangle_right _ _ _
        _ < r + r := add_lt_add (mem_ball.mp hxb) (mem_ball.mp hsb)
        _ = 2 * r := by ring
    have hle : ENNReal.ofReal (C * dist x (φ s)) ≤ B := by
      rw [hBdef]
      rcases le_or_gt 0 C with hC | hC
      · apply ENNReal.ofReal_le_ofReal
        have := mul_le_mul_of_nonneg_left hdist.le hC
        linarith
      · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hC.le dist_nonneg)]
        exact zero_le
    rw [← hφ0] at hγ
    rcases s09_af1_contain Γ φ hφ (hφ1.trans hφ0.symm) hinj hφΓ s hs γ hγ with hc | hc
    · exact Or.inl ((measure_mono hc).trans (hγμ.trans hle))
    · exact Or.inr ((measure_mono hc).trans (hγμ.trans hle))
  have hcov : Γ ∩ ball z r ⊆ ({x} ∪ ⋃ s ∈ {s ∈ Ioo (0 : ℝ) 1 | μH[1] (φ '' Icc 0 s) ≤ B},
      φ '' Icc 0 s) ∪ ⋃ s ∈ {s : ℝ | -s ∈ Ioo (0 : ℝ) 1 ∧ μH[1] (φ '' Icc (-s) 1) ≤ B},
      φ '' Icc (-s) 1 := by
    rintro y ⟨hyΓ, hyb⟩
    rw [← hφΓ] at hyΓ
    obtain ⟨s, hs, rfl⟩ := hyΓ
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · left
      left
      rw [← h0, hφ0]
      rfl
    rcases eq_or_lt_of_le hs.2 with h1 | h1
    · left
      left
      rw [h1, hφ1]
      rfl
    rcases hB s ⟨h0, h1⟩ hyb with hL | hR
    · left
      right
      exact mem_biUnion (x := s) ⟨⟨h0, h1⟩, hL⟩ ⟨s, ⟨h0.le, le_rfl⟩, rfl⟩
    · right
      refine mem_biUnion (x := -s) ⟨?_, ?_⟩ ?_
      · rw [neg_neg]
        exact ⟨h0, h1⟩
      · rw [neg_neg]
        exact hR
      · rw [neg_neg]
        exact ⟨s, ⟨le_rfl, h1.le⟩, rfl⟩
  have hmono1 : Monotone fun s : ℝ => φ '' Icc 0 s :=
    fun a b hab => image_mono (Icc_subset_Icc le_rfl hab)
  have hmono2 : Monotone fun s : ℝ => φ '' Icc (-s) 1 :=
    fun a b hab => image_mono (Icc_subset_Icc (neg_le_neg hab) le_rfl)
  have hU1 := s09_af1_mono_union μH[1] _ hmono1
    {s ∈ Ioo (0 : ℝ) 1 | μH[1] (φ '' Icc 0 s) ≤ B} B (fun s hs => hs.2)
  have hU2 := s09_af1_mono_union μH[1] _ hmono2
    {s : ℝ | -s ∈ Ioo (0 : ℝ) 1 ∧ μH[1] (φ '' Icc (-s) 1) ≤ B} B (fun s hs => hs.2)
  have hx0 : μH[1] ({x} : Set ℂ) = 0 := by
    have := Measure.nullSingletonClass_hausdorff ℂ (d := 1) one_pos
    exact measure_singleton x
  calc μH[1] (Γ ∩ ball z r)
      ≤ μH[1] (({x} ∪ ⋃ s ∈ {s ∈ Ioo (0 : ℝ) 1 | μH[1] (φ '' Icc 0 s) ≤ B},
          φ '' Icc 0 s) ∪ ⋃ s ∈ {s : ℝ | -s ∈ Ioo (0 : ℝ) 1 ∧ μH[1] (φ '' Icc (-s) 1) ≤ B},
          φ '' Icc (-s) 1) := measure_mono hcov
    _ ≤ μH[1] ({x} : Set ℂ) + μH[1] (⋃ s ∈ {s ∈ Ioo (0 : ℝ) 1 | μH[1] (φ '' Icc 0 s) ≤ B},
          φ '' Icc 0 s) + μH[1] (⋃ s ∈ {s : ℝ | -s ∈ Ioo (0 : ℝ) 1 ∧
            μH[1] (φ '' Icc (-s) 1) ≤ B}, φ '' Icc (-s) 1) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ 0 + B + B := add_le_add (add_le_add hx0.le hU1) hU2
    _ = ENNReal.ofReal (4 * C * r) := by
        rw [zero_add, hBdef]
        rcases le_or_gt 0 C with hC | hC
        · rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
        · rw [ENNReal.ofReal_of_nonpos (by nlinarith), ENNReal.ofReal_of_nonpos (by nlinarith),
            add_zero]

/-- Lemma 9.10(2) `lem:arc-facts` (`sec09-ambient.tex:723`): Ahlfors regular (`A`) and bounded
turning (`C_bt`) imply chord-arc with constant `A C_bt`. -/
theorem lem_arc_facts_2 (Γ : Set ℂ) (hΓ : IsJordanCurveC Γ) (A Cbt : ℝ)
    (hA : IsAhlforsRegular Γ A) (hbt : HasBoundedTurning Γ Cbt) :
    IsChordArc Γ (A * Cbt) := by
  obtain ⟨g, hg, -, hrange⟩ := hΓ
  have hcpt : IsCompact Γ := by
    rw [← hrange]
    exact isCompact_range hg
  refine ⟨?_, fun x hx y hy hxy => ?_⟩
  · obtain ⟨R, hR⟩ := hcpt.isBounded.subset_ball 0
    have hR0 : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    calc μH[1] Γ = μH[1] (Γ ∩ ball 0 (max R 1)) := by
          rw [inter_eq_left.mpr (hR.trans (ball_subset_ball (le_max_left _ _)))]
      _ ≤ ENNReal.ofReal (A * max R 1) := hA 0 _ hR0
      _ < ⊤ := ENNReal.ofReal_lt_top
  · obtain ⟨γ, hγ, hdiam⟩ := hbt x hx y hy hxy
    refine ⟨γ, hγ, ?_⟩
    obtain ⟨hγΓ, g', hg'c, -, hg'0, -, hg'im⟩ := hγ
    have hγc : IsCompact γ := by
      rw [← hg'im]
      exact isCompact_Icc.image_of_continuousOn hg'c
    have hxγ : x ∈ γ := by
      rw [← hg'im]
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, hg'0⟩
    have hdn : 0 ≤ Metric.diam γ := Metric.diam_nonneg
    have hle : ∀ ε : ℝ, 0 < ε → μH[1] γ ≤ ENNReal.ofReal (A * (Metric.diam γ + ε)) := by
      intro ε hε
      have hsub : γ ⊆ Γ ∩ ball x (Metric.diam γ + ε) := fun z hz => ⟨hγΓ hz, by
        rw [mem_ball]
        linarith [dist_le_diam_of_mem hγc.isBounded hz hxγ]⟩
      exact (measure_mono hsub).trans (hA x _ (by linarith))
    have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (A * (Metric.diam γ + ε))) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal (A * Metric.diam γ))) := by
      apply ENNReal.tendsto_ofReal
      have := (((tendsto_id (x := 𝓝 (0 : ℝ))).mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))).const_add (Metric.diam γ)).const_mul A
      rwa [add_zero] at this
    have h1 : μH[1] γ ≤ ENNReal.ofReal (A * Metric.diam γ) :=
      ge_of_tendsto hlim (by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        exact hle ε hε)
    refine h1.trans ?_
    by_cases hA0 : 0 ≤ A
    · apply ENNReal.ofReal_le_ofReal
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hdiam hA0
    · rw [ENNReal.ofReal_of_nonpos (by nlinarith)]
      exact zero_le

/-- Bound of `lem_arc_facts_0` with an explicit bound `K` on `|F'|` over `E`. -/
theorem s09_af0_bound (F : ℂ → ℂ) (O E : Set ℂ) (hO : IsOpen O) (hF : DifferentiableOn ℂ F O)
    (hE : IsCompact (closure E)) (hEO : closure E ⊆ O) (K : ℝ)
    (hK : ∀ z ∈ E, ‖deriv F z‖ ≤ K) : μH[1] (F '' E) ≤ ENNReal.ofReal K * μH[1] E := by
  rcases E.eq_empty_or_nonempty with h | h
  · subst h
    simp
  · refine (lem_arc_facts_0 F O E hO hF hE hEO).trans ?_
    gcongr
    refine csSup_le (h.image _) ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hK z hz

theorem s09_invAt_hasDerivAt (c z : ℂ) (hz : z ≠ c) :
    HasDerivAt (invAt c) (-((z - c) ^ 2)⁻¹) z := by
  have h1 : HasDerivAt (fun y : ℂ => y - c) 1 z := (hasDerivAt_id z).sub_const c
  have h2 := (hasDerivAt_inv (sub_ne_zero.mpr hz)).comp z h1
  rw [mul_one] at h2
  exact h2

theorem s09_invAt_deriv_norm (c z : ℂ) (hz : z ≠ c) :
    ‖deriv (invAt c) z‖ = ‖invAt c z‖ ^ 2 := by
  rw [(s09_invAt_hasDerivAt c z hz).deriv]
  unfold invAt
  rw [norm_neg, norm_inv, norm_inv, norm_pow, inv_pow]

theorem s09_invAt_norm_mul (c z : ℂ) (hz : z ≠ c) : ‖z - c‖ * ‖invAt c z‖ = 1 := by
  unfold invAt
  rw [norm_inv, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz))]

/-- One step of `lem_arc_facts_3`: a piece `E ⊆ Γ ∩ D(x, R)` with `|τ|² ≤ K` on it. -/
theorem s09_af3_step (Γ : Set ℂ) (hΓc : IsCompact Γ) (c : ℂ) (hc : c ∉ Γ) (a : ℝ≥0∞)
    (hA : ∀ z : ℂ, ∀ r : ℝ, 0 < r → μH[1] (Γ ∩ ball z r) ≤ a * ENNReal.ofReal r)
    (E : Set ℂ) (hEΓ : E ⊆ Γ) (x : ℂ) (R : ℝ) (hR : 0 < R) (hEx : E ⊆ ball x R) (K : ℝ)
    (hK0 : 0 ≤ K) (hK : ∀ z ∈ E, ‖invAt c z‖ ^ 2 ≤ K) :
    μH[1] (invAt c '' E) ≤ a * ENNReal.ofReal (K * R) := by
  have hne : ∀ z ∈ Γ, z ≠ c := fun z hz h => hc (h ▸ hz)
  have hdiff : DifferentiableOn ℂ (invAt c) {c}ᶜ := fun z hz =>
    (s09_invAt_hasDerivAt c z hz).differentiableAt.differentiableWithinAt
  have hEO : closure E ⊆ {c}ᶜ := fun z hz =>
    hne z (closure_minimal hEΓ hΓc.isClosed hz)
  calc μH[1] (invAt c '' E) ≤ ENNReal.ofReal K * μH[1] E :=
        s09_af0_bound (invAt c) {c}ᶜ E isOpen_compl_singleton hdiff
          (hΓc.closure_of_subset hEΓ) hEO K (fun z hz => by
            rw [s09_invAt_deriv_norm c z (hne z (hEΓ hz))]
            exact hK z hz)
    _ ≤ ENNReal.ofReal K * (a * ENNReal.ofReal R) := by
        gcongr
        exact (measure_mono (subset_inter hEΓ hEx)).trans (hA x R hR)
    _ = a * ENNReal.ofReal (K * R) := by
        rw [ENNReal.ofReal_mul hK0]
        ring

/-- Lemma 9.10(3) `lem:arc-facts` (`sec09-ambient.tex:725`): if `Γ` is Ahlfors regular (`A`)
and `c ∉ Γ`, then `τ(Γ)`, `τ(z) = 1/(z - c)`, is a bounded Jordan curve, Ahlfors regular with
constant `24A`. -/
theorem lem_arc_facts_3 (Γ : Set ℂ) (hΓ : IsJordanCurveC Γ) (A : ℝ) (hA : IsAhlforsRegular Γ A)
    (c : ℂ) (hc : c ∉ Γ) :
    IsJordanCurveC (invAt c '' Γ) ∧ IsAhlforsRegular (invAt c '' Γ) (24 * A) := by
  have hΓc : IsCompact Γ := by
    obtain ⟨g, hg, -, hr⟩ := hΓ
    rw [← hr]
    exact isCompact_range hg
  have hne : ∀ z ∈ Γ, z ≠ c := fun z hz h => hc (h ▸ hz)
  refine ⟨?_, ?_⟩
  · obtain ⟨g, hg, hinj, hr⟩ := hΓ
    refine ⟨invAt c ∘ g, ?_, ?_, ?_⟩
    · show Continuous fun t => (g t - c)⁻¹
      exact (hg.sub continuous_const).inv₀
        (fun t => sub_ne_zero.mpr (hne _ (hr ▸ mem_range_self t)))
    · intro s t hst
      have h : (g s - c)⁻¹ = (g t - c)⁻¹ := hst
      exact hinj (sub_left_injective (inv_injective h))
    · rw [range_comp, hr]
  · set a := ENNReal.ofReal A with hadef
    have hA' : ∀ z : ℂ, ∀ r : ℝ, 0 < r → μH[1] (Γ ∩ ball z r) ≤ a * ENNReal.ofReal r :=
      fun z r hr => (hA z r hr).trans (le_of_eq (ENNReal.ofReal_mul' hr.le))
    intro u₀ ρ hρ
    rw [← image_inter_preimage]
    set E := Γ ∩ invAt c ⁻¹' ball u₀ ρ with hEdef
    have hEΓ : E ⊆ Γ := inter_subset_left
    have key : μH[1] (invAt c '' E) ≤ a * ENNReal.ofReal (24 * ρ) := by
      rcases le_or_gt (2 * ρ) ‖u₀‖ with h1 | h2
      · have hu : 0 < ‖u₀‖ := by linarith
        have hu0 : u₀ ≠ 0 := norm_pos_iff.mp hu
        refine (s09_af3_step Γ hΓc c hc a hA' E hEΓ (c + u₀⁻¹) (2 * ρ / ‖u₀‖ ^ 2)
          (by positivity) ?_ ((3 / 2 * ‖u₀‖) ^ 2) (by positivity) ?_).trans ?_
        · intro z hz
          obtain ⟨hzΓ, hzb⟩ := hz
          rw [mem_preimage, mem_ball, dist_eq_norm] at hzb
          set w := invAt c z with hw
          have hlt : ‖u₀ - w‖ < ρ := by
            rw [norm_sub_rev]
            exact hzb
          have hwlow : ‖u₀‖ / 2 < ‖w‖ := by
            have := norm_sub_norm_le u₀ w
            linarith
          have hw0 : w ≠ 0 := norm_pos_iff.mp (by linarith)
          have hzc : z - c = w⁻¹ := by
            rw [hw]
            unfold invAt
            rw [inv_inv]
          rw [mem_ball, dist_eq_norm, show z - (c + u₀⁻¹) = w⁻¹ - u₀⁻¹ by rw [← hzc]; ring,
            inv_sub_inv hw0 hu0, norm_div, norm_mul, div_lt_div_iff₀ (by positivity)
              (by positivity)]
          nlinarith [mul_lt_mul_of_pos_right hlt (pow_pos hu 2),
            mul_le_mul_of_nonneg_left hwlow.le (by positivity : (0 : ℝ) ≤ 2 * ρ * ‖u₀‖),
            norm_nonneg (u₀ - w)]
        · intro z hz
          obtain ⟨-, hzb⟩ := hz
          rw [mem_preimage, mem_ball, dist_eq_norm] at hzb
          have h3 : ‖invAt c z‖ ≤ 3 / 2 * ‖u₀‖ := by
            have := norm_sub_norm_le (invAt c z) u₀
            linarith
          exact pow_le_pow_left₀ (norm_nonneg _) h3 2
        · rw [show (3 / 2 * ‖u₀‖) ^ 2 * (2 * ρ / ‖u₀‖ ^ 2) = 9 / 2 * ρ by
            field_simp
            ring]
          exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (by linarith)) zero_le
      · set Ej : ℕ → Set ℂ := fun n =>
          E ∩ {z | (2 : ℝ) ^ n ≤ 3 * ρ * ‖z - c‖ ∧ 3 * ρ * ‖z - c‖ < 2 ^ (n + 1)} with hEj
        have hcov : E ⊆ ⋃ n, Ej n := by
          intro z hz
          have hz' := hz
          obtain ⟨hzΓ, hzb⟩ := hz'
          rw [mem_preimage, mem_ball, dist_eq_norm] at hzb
          have hzc := hne z hzΓ
          have hprod := s09_invAt_norm_mul c z hzc
          have hw3 : ‖invAt c z‖ < 3 * ρ := by
            have := norm_sub_norm_le (invAt c z) u₀
            linarith
          have hpos : 0 < ‖z - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzc)
          have h1le : 1 ≤ 3 * ρ * ‖z - c‖ := by
            nlinarith [mul_lt_mul_of_pos_left hw3 hpos]
          obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near h1le (by norm_num : (1 : ℝ) < 2)
          exact mem_iUnion.mpr ⟨n, hz, hn1, hn2⟩
        have hpiece : ∀ n, μH[1] (invAt c '' Ej n) ≤
            a * ENNReal.ofReal (6 * ρ * ((1 : ℝ) / 2) ^ n) := by
          intro n
          refine (s09_af3_step Γ hΓc c hc a hA' (Ej n) (fun z hz => hz.1.1) c
            (2 ^ (n + 1) / (3 * ρ)) (by positivity) ?_ ((3 * ρ / 2 ^ n) ^ 2) (by positivity)
            ?_).trans (le_of_eq ?_)
          · intro z hz
            rw [mem_ball, dist_eq_norm, lt_div_iff₀ (by positivity)]
            linarith [hz.2.2]
          · intro z hz
            obtain ⟨⟨hzΓ, -⟩, h1, -⟩ := hz
            have hprod := s09_invAt_norm_mul c z (hne z hzΓ)
            have h3 : ‖invAt c z‖ ≤ 3 * ρ / 2 ^ n := by
              rw [le_div_iff₀ (by positivity)]
              nlinarith [mul_le_mul_of_nonneg_left h1 (norm_nonneg (invAt c z))]
            exact pow_le_pow_left₀ (norm_nonneg _) h3 2
          · congr 2
            rw [one_div_pow]
            field_simp
            ring
        have hsum : ∑' n, a * ENNReal.ofReal (6 * ρ * ((1 : ℝ) / 2) ^ n) =
            a * ENNReal.ofReal (12 * ρ) := by
          rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
            (summable_geometric_two.mul_left (6 * ρ)), tsum_mul_left, tsum_geometric_two,
            show 6 * ρ * 2 = 12 * ρ by ring]
        calc μH[1] (invAt c '' E) ≤ μH[1] (⋃ n, invAt c '' Ej n) := by
              rw [← image_iUnion]
              exact measure_mono (image_mono hcov)
          _ ≤ ∑' n, μH[1] (invAt c '' Ej n) := measure_iUnion_le _
          _ ≤ ∑' n, a * ENNReal.ofReal (6 * ρ * ((1 : ℝ) / 2) ^ n) :=
              tsum_le_tsum hpiece
          _ = a * ENNReal.ofReal (12 * ρ) := hsum
          _ ≤ a * ENNReal.ofReal (24 * ρ) :=
              mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (by linarith)) zero_le
    refine key.trans ?_
    rcases le_or_gt 0 A with h | h
    · rw [hadef, ← ENNReal.ofReal_mul h]
      exact le_of_eq (congrArg ENNReal.ofReal (by ring))
    · rw [hadef, ENNReal.ofReal_of_nonpos h.le, zero_mul]
      exact zero_le

theorem s09_norm_one_sub_exp_sq (φ : ℝ) : ‖1 - exp (φ * I)‖ ^ 2 = 2 - 2 * Real.cos φ := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  nlinarith [Real.sin_sq_add_cos_sq φ]

/-- On the shorter circle arc from `a` to `a e^{iθ}`, chords from `a` grow with the angle. -/
theorem s09_chord_le (a : ℂ) (ha : ‖a‖ = 1) (θ : ℝ) (hθ1 : -π < θ) (hθ2 : θ ≤ π) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖a - a * exp ((θ * t : ℝ) * I)‖ ≤ ‖a - a * exp (θ * I)‖ := by
  have e : ∀ φ : ℝ, ‖a - a * exp (φ * I)‖ = ‖1 - exp (φ * I)‖ := fun φ => by
    rw [show a - a * exp (φ * I) = a * (1 - exp (φ * I)) by ring, norm_mul, ha, one_mul]
  rw [e, e, ← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero,
    s09_norm_one_sub_exp_sq, s09_norm_one_sub_exp_sq]
  have habs : |θ| ≤ π := abs_le.mpr ⟨by linarith, hθ2⟩
  have hle : |θ * t| ≤ |θ| := by
    rw [abs_mul, abs_of_nonneg ht0]
    exact mul_le_of_le_one_right (abs_nonneg _) ht1
  have := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) habs hle
  rw [Real.cos_abs, Real.cos_abs] at this
  linarith

/-- Lemma 9.10(4) `lem:arc-facts` (`sec09-ambient.tex:728`): a bounded `K`-quasicircle has
bounded turning with a constant depending only on `K` (the paper: `2η_K(1)`, `η_K` of
`lem:three-point`). -/
theorem lem_arc_facts_4 :
    ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ, ∀ Ω Ωs : Set ℂ, IsBoundedKQuasicircle Ω Ωs K →
      HasBoundedTurning (curveOf Ω Ωs) C := by
  intro K hK
  obtain ⟨C₀, hC₀, h3⟩ := lem_three_point K hK
  refine ⟨2 * C₀, fun Ω Ωs hΓ => ?_⟩
  obtain ⟨F, hF, hFu, hF1, hF2⟩ := hΓ
  have hFc : Continuous F := continuousOn_univ.mp hF.2.2.1.1
  have hFi : Function.Injective F := injOn_univ.mp hF.2.2.1.2.1
  have hcurve : ∀ z : ℂ, ‖z‖ = 1 → F z ∈ curveOf Ω Ωs := by
    intro z hz
    simp only [curveOf, mem_compl_iff, mem_union, not_or]
    constructor
    · rw [← hF1]
      rintro ⟨v, hv, hFv⟩
      rw [hFi hFv] at hv
      have := mem_ball_zero_iff.mp hv
      linarith
    · rw [← hF2]
      rintro ⟨v, hv, hFv⟩
      rw [hFi hFv] at hv
      have : 1 < ‖z‖ := hv
      linarith
  have hpre : ∀ x ∈ curveOf Ω Ωs, ∃ a : ℂ, ‖a‖ = 1 ∧ F a = x := by
    intro x hx
    obtain ⟨a, -, rfl⟩ : x ∈ F '' univ := by
      rw [hFu]
      trivial
    refine ⟨a, ?_, rfl⟩
    simp only [curveOf, mem_compl_iff, mem_union, not_or] at hx
    apply le_antisymm
    · by_contra h
      exact hx.2 (by rw [← hF2]; exact ⟨a, lt_of_not_ge h, rfl⟩)
    · by_contra h
      exact hx.1 (by rw [← hF1]; exact ⟨a, mem_ball_zero_iff.mpr (lt_of_not_ge h), rfl⟩)
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := hpre x hx
  obtain ⟨b, hb, rfl⟩ := hpre y hy
  have hab : a ≠ b := fun h => hxy (by rw [h])
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    exact zero_ne_one ha
  set θ : ℝ := arg (b / a) with hθ
  have hθ1 : -π < θ := neg_pi_lt_arg _
  have hθ2 : θ ≤ π := arg_le_pi _
  have hexp : a * exp (θ * I) = b := by
    have h := Complex.norm_mul_exp_arg_mul_I (b / a)
    rw [norm_div, ha, hb, div_one, ofReal_one, one_mul, ← hθ] at h
    rw [h]
    field_simp
  have hθ0 : θ ≠ 0 := by
    intro h
    apply hab
    rw [← hexp, h, ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  let c : ℝ → ℂ := fun t => a * exp ((θ * t : ℝ) * I)
  have hcn : ∀ t, ‖c t‖ = 1 := fun t => by
    simp only [c]
    rw [norm_mul, ha, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hrange : ∀ s ∈ Icc (0 : ℝ) 1, -π < θ * s ∧ θ * s ≤ π := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    rcases le_or_gt 0 θ with h | h
    · constructor <;> nlinarith [Real.pi_pos]
    · constructor <;> nlinarith [Real.pi_pos]
  have hFab : 0 < ‖F a - F b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hab (hFi h))
  have hab' : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have key : ∀ t ∈ Icc (0 : ℝ) 1, ‖F a - F (c t)‖ ≤ C₀ * ‖F a - F b‖ := by
    intro t ht
    have h := (h3 F hF hFu a (c t) b hab).1
    have hch : ‖a - c t‖ ≤ ‖a - b‖ := by
      have := s09_chord_le a ha θ hθ1 hθ2 t ht.1 ht.2
      rwa [hexp] at this
    have hr : ‖a - c t‖ / ‖a - b‖ ≤ 1 := div_le_one_of_le₀ hch hab'.le
    have hr0 : 0 ≤ ‖a - c t‖ / ‖a - b‖ := by positivity
    have hmax : max ((‖a - c t‖ / ‖a - b‖) ^ (1 / K)) ((‖a - c t‖ / ‖a - b‖) ^ K) ≤ 1 :=
      max_le (Real.rpow_le_one hr0 hr (by positivity)) (Real.rpow_le_one hr0 hr (by linarith))
    rw [div_le_iff₀ hFab] at h
    calc ‖F a - F (c t)‖
        ≤ C₀ * max ((‖a - c t‖ / ‖a - b‖) ^ (1 / K)) ((‖a - c t‖ / ‖a - b‖) ^ K) *
            ‖F a - F b‖ := h
      _ ≤ C₀ * 1 * ‖F a - F b‖ := by gcongr
      _ = C₀ * ‖F a - F b‖ := by ring
  refine ⟨F '' (c '' Icc 0 1), ⟨?_, fun t => F (c t), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨_, ⟨t, -, rfl⟩, rfl⟩
    exact hcurve _ (hcn t)
  · exact (hFc.comp (by fun_prop : Continuous c)).continuousOn
  · intro s hs t ht hst
    have h1 : c s = c t := hFi hst
    have h2 : exp ((θ * s : ℝ) * I) = exp ((θ * t : ℝ) * I) := by
      simp only [c] at h1
      exact mul_left_cancel₀ ha0 h1
    have h3' := Complex.exp_inj_of_neg_pi_lt_of_le_pi
      (by simpa using (hrange s hs).1) (by simpa using (hrange s hs).2)
      (by simpa using (hrange t ht).1) (by simpa using (hrange t ht).2) h2
    have h4 : θ * s = θ * t := by
      have := congrArg Complex.im h3'
      simpa using this
    exact mul_left_cancel₀ hθ0 h4
  · show F (a * exp ((θ * 0 : ℝ) * I)) = F a
    rw [mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  · show F (a * exp ((θ * 1 : ℝ) * I)) = F b
    rw [mul_one, hexp]
  · rw [image_image]
  · refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩ _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    calc dist (F (c s)) (F (c t)) ≤ dist (F (c s)) (F a) + dist (F a) (F (c t)) :=
          dist_triangle _ _ _
      _ ≤ C₀ * ‖F a - F b‖ + C₀ * ‖F a - F b‖ := by
          gcongr
          · rw [dist_comm, dist_eq_norm]
            exact key s hs
          · rw [dist_eq_norm]
            exact key t ht
      _ = 2 * C₀ * dist (F a) (F b) := by
          rw [dist_eq_norm]
          ring

/-- Basic topology of a bounded Jordan pair. -/
theorem s09_bjp_basic (Ω Ωs : Set ℂ) (hΓ : IsBoundedJordanPair Ω Ωs) :
    IsOpen Ω ∧ IsOpen Ωs ∧ Disjoint Ω Ωs ∧ Bornology.IsBounded Ω ∧
      Bornology.IsBounded (curveOf Ω Ωs) ∧ IsClosed (curveOf Ω Ωs) := by
  obtain ⟨F, h1, h2⟩ := hΓ
  have hK : Bornology.IsBounded (F '' closedBall (0 : ℂ) 1) :=
    ((isCompact_closedBall 0 1).image F.continuous).isBounded
  have hD : IsOpen unitDisc := Metric.isOpen_ball
  have hE : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hO : IsOpen Ω := h1 ▸ F.isOpenMap _ hD
  have hOs : IsOpen Ωs := h2 ▸ F.isOpenMap _ hE
  refine ⟨hO, hOs, ?_, ?_, ?_, (hO.union hOs).isClosed_compl⟩
  · rw [← h1, ← h2, Set.disjoint_image_iff F.injective, Set.disjoint_left]
    intro z hz1 hz2
    have h1' : ‖z‖ < 1 := by simpa [unitDisc] using hz1
    have h2' : 1 < ‖z‖ := hz2
    linarith
  · refine hK.subset ?_
    rw [← h1]
    exact image_mono ball_subset_closedBall
  · refine hK.subset fun z hz => ⟨F.symm z, ?_, F.apply_symm_apply z⟩
    simp only [curveOf, mem_compl_iff, mem_union, not_or] at hz
    rw [mem_closedBall, dist_zero_right]
    by_contra hlt
    push_neg at hlt
    apply hz.2
    rw [← h2]
    exact ⟨F.symm z, hlt, F.apply_symm_apply z⟩

/-- A preconnected set missing `Γ` and meeting `Ω` lies in `Ω`. -/
theorem s09_bjp_preconn (Ω Ωs : Set ℂ) (hΓ : IsBoundedJordanPair Ω Ωs) (S : Set ℂ)
    (hS : IsPreconnected S) (hSΓ : ∀ z ∈ S, z ∉ curveOf Ω Ωs) (w : ℂ) (hwS : w ∈ S)
    (hw : w ∈ Ω) : S ⊆ Ω := by
  obtain ⟨hO, hOs, hdis, -, -, -⟩ := s09_bjp_basic Ω Ωs hΓ
  refine hS.subset_left_of_subset_union hO hOs hdis (fun z hz => ?_) ⟨w, hwS, hw⟩
  have := hSΓ z hz
  simp only [curveOf, mem_compl_iff, not_not] at this
  exact this

theorem s09_norm_line (w y : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    ‖w + (t : ℂ) * (w - y) - y‖ = (1 + t) * ‖w - y‖ := by
  rw [show w + (t : ℂ) * (w - y) - y = ((1 + t : ℝ) : ℂ) * (w - y) by push_cast; ring,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]

/-- Lemma 9.11(a) `lem:dictionary` (`sec09-ambient.tex:807`): `Ω ⊂ D(x, δ)` and
`d(w) ≤ δ/2`, `δ = diam Γ`. -/
theorem lem_dictionary_a (Ω Ωs : Set ℂ) (hΓ : IsBoundedJordanPair Ω Ωs) (x : ℂ)
    (hx : x ∈ curveOf Ω Ωs) :
    Ω ⊆ ball x (Metric.diam (curveOf Ω Ωs)) ∧
      ∀ w ∈ Ω, infDist w (curveOf Ω Ωs) ≤ Metric.diam (curveOf Ω Ωs) / 2 := by
  obtain ⟨hO, hOs, hdis, hOb, hΓb, hΓc⟩ := s09_bjp_basic Ω Ωs hΓ
  have hnotΓ : ∀ w ∈ Ω, w ∉ curveOf Ω Ωs := fun w hw h => by
    simp only [curveOf, mem_compl_iff, mem_union, not_or] at h
    exact h.1 hw
  have hpart1 : ∀ y ∈ curveOf Ω Ωs, Ω ⊆ ball y (Metric.diam (curveOf Ω Ωs)) := by
    intro y hy w hw
    rw [mem_ball]
    by_contra hge
    push_neg at hge
    have hwy : w ≠ y := fun h => hnotΓ w hw (h ▸ hy)
    have hpos : 0 < ‖w - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwy)
    rw [dist_eq_norm] at hge
    have hR : (fun t : ℝ => w + (t : ℂ) * (w - y)) '' Ici 0 ⊆ Ω := by
      refine s09_bjp_preconn Ω Ωs hΓ _
        (isPreconnected_Ici.image _ (Continuous.continuousOn (by fun_prop))) ?_ w
        ⟨0, mem_Ici.mpr le_rfl, by simp⟩ hw
      rintro z ⟨t, ht, rfl⟩ hzΓ
      have h1 := dist_le_diam_of_mem hΓb hzΓ hy
      rw [dist_eq_norm, s09_norm_line w y t ht] at h1
      have ht0 : t = 0 := by
        have : t * ‖w - y‖ ≤ 0 := by nlinarith
        have := nonpos_of_mul_nonpos_left this hpos
        exact le_antisymm this ht
      subst ht0
      exact hnotΓ w hw (by simpa using hzΓ)
    obtain ⟨C, hC⟩ := hOb.subset_closedBall y
    set t : ℝ := max C 0 / ‖w - y‖ + 1 with htdef
    have ht : 0 ≤ t := by positivity
    have hmem := hC (hR ⟨t, ht, rfl⟩)
    rw [mem_closedBall, dist_eq_norm, s09_norm_line w y t ht] at hmem
    have e : t * ‖w - y‖ = max C 0 + ‖w - y‖ := by
      rw [htdef]
      field_simp
    nlinarith [le_max_left C 0]
  refine ⟨hpart1 x hx, fun w hw => ?_⟩
  have hΓcpt : IsCompact (curveOf Ω Ωs) := Metric.isCompact_of_isClosed_isBounded hΓc hΓb
  obtain ⟨x', hx', hd⟩ := hΓcpt.exists_infDist_eq_dist ⟨x, hx⟩ w
  by_contra hgt
  push_neg at hgt
  have hδ : 0 ≤ Metric.diam (curveOf Ω Ωs) := Metric.diam_nonneg
  have hρ : 0 < infDist w (curveOf Ω Ωs) := by linarith
  have hball : ball w (infDist w (curveOf Ω Ωs)) ⊆ Ω := by
    refine s09_bjp_preconn Ω Ωs hΓ _ (convex_ball w _).isPreconnected (fun z hz hzΓ => ?_) w
      (mem_ball_self hρ) hw
    have := infDist_le_dist_of_mem hzΓ (x := w)
    rw [mem_ball, dist_comm] at hz
    linarith
  set c : ℝ := Metric.diam (curveOf Ω Ωs) / 2 / infDist w (curveOf Ω Ωs) with hcdef
  have hc : 0 ≤ c := by positivity
  have hcρ : c * infDist w (curveOf Ω Ωs) = Metric.diam (curveOf Ω Ωs) / 2 := by
    rw [hcdef]
    field_simp
  have hzw : dist (w + (c : ℂ) * (w - x')) w = Metric.diam (curveOf Ω Ωs) / 2 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hc, ← dist_eq_norm, ← hd, hcρ]
  have hzΩ : w + (c : ℂ) * (w - x') ∈ Ω := hball (by rw [mem_ball, hzw]; linarith)
  have hzx := hpart1 x' hx' hzΩ
  rw [mem_ball, dist_eq_norm, s09_norm_line w x' c hc, ← dist_eq_norm, ← hd] at hzx
  nlinarith

/-- The bounded component of a bounded Jordan pair has a Riemann map from `𝔻`. -/
theorem s09_bdd_riemann (Ω Ωs : Set ℂ) (hΓ : IsBoundedJordanPair Ω Ωs) :
    ∃ f, IsConformalOnto f unitDisc Ω := by
  obtain ⟨hO, -, hdis, -, -, -⟩ := s09_bjp_basic Ω Ωs hΓ
  obtain ⟨F, hF, hF2⟩ := hΓ
  have hne : unitDisc.Nonempty := ⟨0, mem_ball_self one_pos⟩
  have hcv : Convex ℝ unitDisc := convex_ball (0 : ℂ) 1
  obtain ⟨φ, hφ⟩ : ∃ φ : ℂ → ℂ, IsConformalOnto φ Ω unitDisc := by
    apply lehto_exists_conformal
    refine ⟨hO, ?_, ?_, ?_⟩
    · rw [← hF]
      exact (hcv.isConnected hne).image F F.continuous.continuousOn
    · rw [← hF]
      have : ContractibleSpace unitDisc := hcv.contractibleSpace hne
      exact ContinuousMap.HomotopyEquiv.simplyConnectedSpace
        (F.image unitDisc).symm.toHomotopyEquiv
    · intro hu
      have h2 : F 2 ∈ Ωs := by
        rw [← hF2]
        refine ⟨2, ?_, rfl⟩
        show 1 < ‖(2 : ℂ)‖
        norm_num
      exact Set.disjoint_right.mp hdis h2 (hu ▸ mem_univ _)
  exact ⟨_, hφ.symm hO⟩

/-- For `w ∈ Ω`, the distance to `Ωᶜ` is the distance to the curve. -/
theorem s09_infDist_compl (Ω Ωs : Set ℂ) (hΓ : IsBoundedJordanPair Ω Ωs) (x : ℂ)
    (hx : x ∈ curveOf Ω Ωs) (w : ℂ) (hw : w ∈ Ω) :
    infDist w Ωᶜ = infDist w (curveOf Ω Ωs) := by
  have hsub : curveOf Ω Ωs ⊆ Ωᶜ := fun z hz h => by
    simp only [curveOf, mem_compl_iff, mem_union, not_or] at hz
    exact hz.1 h
  refine le_antisymm (infDist_le_infDist_of_subset hsub ⟨x, hx⟩) ?_
  refine (le_infDist ⟨x, hsub hx⟩).mpr fun z hz => ?_
  by_contra hlt
  have hseg : segment ℝ w z ⊆ Ω := by
    refine s09_bjp_preconn Ω Ωs hΓ _ (convex_segment w z).isPreconnected (fun p hp hpΓ => ?_)
      w (left_mem_segment ℝ w z) hw
    have h1 := infDist_le_dist_of_mem (x := w) hpΓ
    have h2 := dist_add_dist_of_mem_segment hp
    have h3 := dist_nonneg (x := p) (y := z)
    exact hlt (by linarith)
  exact hz (hseg (right_mem_segment ℝ w z))

/-- Lemma 9.11(b) `lem:dictionary` (`sec09-ambient.tex:808`):
`k_{(x,δ)}(X(w)) ≥ (4/65) d(w)/δ`, hence `μ_Ω(Ω) ≤ (65/4) δ H^Ω((x, δ))`. -/
theorem lem_dictionary_b (Ω Ωs : Set ℂ) (hΓ : IsBoundedJordanPair Ω Ωs) (x : ℂ)
    (hx : x ∈ curveOf Ω Ωs) :
    (∀ w ∈ Ω, 4 / 65 * infDist w (curveOf Ω Ωs) / Metric.diam (curveOf Ω Ωs) ≤
        ambKernel (x, Metric.diam (curveOf Ω Ωs)) (epstein Ω w)) ∧
      muOmega Ω Ωs univ ≤ ENNReal.ofReal (65 / 4 * Metric.diam (curveOf Ω Ωs)) *
        ambHside Ω (x, Metric.diam (curveOf Ω Ωs)) := by
  obtain ⟨hO, -, -, -, -, hΓc⟩ := s09_bjp_basic Ω Ωs hΓ
  obtain ⟨hball, hhalf⟩ := lem_dictionary_a Ω Ωs hΓ x hx
  have hR := s09_bdd_riemann Ω Ωs hΓ
  set δ := Metric.diam (curveOf Ω Ωs) with hδ
  have key : ∀ w ∈ Ω, 4 / 65 * infDist w (curveOf Ω Ωs) / δ ≤
      ambKernel (x, δ) (epstein Ω w) := by
    intro w hw
    have hnot : w ∉ curveOf Ω Ωs := fun h => by
      simp only [curveOf, mem_compl_iff, mem_union, not_or] at h
      exact h.1 hw
    set d := infDist w (curveOf Ω Ωs) with hd
    have hd0 : 0 < d := (hΓc.notMem_iff_infDist_pos ⟨x, hx⟩).mp hnot
    have hdδ : d ≤ δ / 2 := hhalf w hw
    have hδ0 : 0 < δ := by linarith
    obtain ⟨-, -, -, e4, e5, e6⟩ := lem_ep_position hR hw
    rw [s09_infDist_compl Ω Ωs hΓ x hx w hw] at e4 e5 e6
    set Q := epstein Ω w with hQ
    have hQ2 : 0 < Q.2 := by linarith
    have hwx : ‖w - x‖ < δ := by
      have := hball hw
      rwa [mem_ball, dist_eq_norm] at this
    have hWx : ‖Q.1 - x‖ ≤ 2 * δ := by
      calc ‖Q.1 - x‖ = ‖(Q.1 - w) + (w - x)‖ := by ring_nf
        _ ≤ ‖Q.1 - w‖ + ‖w - x‖ := norm_add_le _ _
        _ ≤ 2 * δ := by linarith
    rw [s09_ambKernel_eq (x, δ) Q hδ0 hQ2]
    show 4 / 65 * d / δ ≤ 4 * Q.2 * δ / (‖Q.1 - x‖ ^ 2 + (Q.2 + δ) ^ 2)
    have hden : ‖Q.1 - x‖ ^ 2 + (Q.2 + δ) ^ 2 ≤ 13 * δ ^ 2 := by
      have h1 : ‖Q.1 - x‖ ^ 2 ≤ (2 * δ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hWx 2
      have h2 : (Q.2 + δ) ^ 2 ≤ (3 * δ) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      nlinarith
    have hden0 : 0 < ‖Q.1 - x‖ ^ 2 + (Q.2 + δ) ^ 2 := by positivity
    calc 4 / 65 * d / δ = 4 * (d / 5) * δ / (13 * δ ^ 2) := by
          field_simp
          ring
      _ ≤ 4 * Q.2 * δ / (13 * δ ^ 2) := by gcongr
      _ ≤ 4 * Q.2 * δ / (‖Q.1 - x‖ ^ 2 + (Q.2 + δ) ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) hden0 hden
  refine ⟨key, ?_⟩
  have hOm : MeasurableSet Ω := hO.measurableSet
  have hae : ∀ᵐ w ∂curvMass Ω, w ∈ Ω :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hOm)
  unfold muOmega ambHside
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [hae] with w hw
  have hk := key w hw
  have hd0 : 0 ≤ infDist w (curveOf Ω Ωs) := infDist_nonneg
  have hδ0 : 0 < δ := by
    have hnot : w ∉ curveOf Ω Ωs := fun h => by
      simp only [curveOf, mem_compl_iff, mem_union, not_or] at h
      exact h.1 hw
    have := (hΓc.notMem_iff_infDist_pos ⟨x, hx⟩).mp hnot
    linarith [hhalf w hw]
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ hδ0] at hk
  nlinarith

/-- The curve of a bounded Jordan pair is nonempty (it contains `F 1`). -/
theorem s09_bjp_curve_nonempty (Ω Ωs : Set ℂ) (hΓ : IsBoundedJordanPair Ω Ωs) :
    (curveOf Ω Ωs).Nonempty := by
  obtain ⟨F, hF1, hF2⟩ := hΓ
  refine ⟨F 1, ?_⟩
  simp only [curveOf, mem_compl_iff, mem_union, not_or]
  constructor
  · rw [← hF1]
    rintro ⟨v, hv, hFv⟩
    rw [F.injective hFv] at hv
    have := mem_ball_zero_iff.mp hv
    simp at this
  · rw [← hF2]
    rintro ⟨v, hv, hFv⟩
    rw [F.injective hFv] at hv
    have : 1 < ‖(1 : ℂ)‖ := hv
    simp at this

/-- Koebe: `d(w) ≤ m(w) ≤ 4 d(w)` on the bounded component. -/
theorem s09_confRad_bounds (Ω Ωs : Set ℂ) (hΓ : IsBoundedJordanPair Ω Ωs) (f : ℂ → ℂ)
    (hf : IsConformalOnto f unitDisc Ω) :
    ∀ w ∈ Ω, infDist w (curveOf Ω Ωs) ≤ confRad f w ∧
      confRad f w ≤ 4 * infDist w (curveOf Ω Ωs) := by
  obtain ⟨x, hx⟩ := s09_bjp_curve_nonempty Ω Ωs hΓ
  intro w hw
  have hex : ∃ a ∈ unitDisc, f a = w := by
    rw [← hf.2.2] at hw
    exact hw
  have hg := Function.invFunOn_mem hex
  have hfg : f (Function.invFunOn f unitDisc w) = w := Function.invFunOn_eq hex
  obtain ⟨k1, k2, -, -⟩ := lem_koebe_a hf hg
  rw [hfg, s09_infDist_compl Ω Ωs hΓ x hx w hw] at k1 k2
  exact ⟨k1, k2⟩

/-- Change of variables: `∫ φ∘f |f'| dω_f = ∫ φ · 4m dm_Ω`. -/
theorem s09_dict_c_cov (Ω : Set ℂ) (f : ℂ → ℂ) (hf : IsConformalOnto f unitDisc Ω)
    (φ : ℂ → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ z, φ (f z) * ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f =
      ∫⁻ w, φ w * ENNReal.ofReal (4 * confRad f w) ∂curvMass Ω := by
  classical
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hDo : IsOpen unitDisc := isOpen_ball
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hΩm : MeasurableSet Ω := hΩo.measurableSet
  set g := Function.invFunOn f unitDisc with hgdef
  have hgc : ContinuousOn g Ω := (hf.symm isOpen_ball).1.continuousOn
  set G : ℂ → ℂ := Ω.piecewise g 0 with hGdef
  have hGm : Measurable G := hgc.measurable_piecewise continuousOn_const hΩm
  have hGeq : ∀ w ∈ Ω, G w = g w := fun w hw => by simp [hGdef, hw]
  set ψ : ℂ → ℝ≥0∞ := fun w =>
    φ w * ENNReal.ofReal (4 * ((1 - ‖G w‖ ^ 2) * ‖deriv f (G w)‖)) with hψdef
  have hψm : Measurable ψ := by
    have h1 : Measurable (deriv f) := measurable_deriv f
    exact hφ.mul (ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((measurable_const.sub (hGm.norm.pow_const 2)).mul (h1.comp hGm).norm)))
  have hae : ∀ᵐ w ∂curvMass Ω, w ∈ Ω := by
    unfold curvMass
    exact (withDensity_absolutelyContinuous (volume.restrict Ω) _).ae_le (ae_restrict_mem hΩm)
  have hRHS : ∫⁻ w, φ w * ENNReal.ofReal (4 * confRad f w) ∂curvMass Ω =
      ∫⁻ w, ψ w ∂curvMass Ω := by
    refine lintegral_congr_ae (hae.mono fun w hw => ?_)
    show φ w * ENNReal.ofReal (4 * confRad f w) =
      φ w * ENNReal.ofReal (4 * ((1 - ‖G w‖ ^ 2) * ‖deriv f (G w)‖))
    rw [hGeq w hw]
    rfl
  rw [hRHS, eq_pullback_mass_a hf hψm]
  set c : ℂ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (‖schwarzianHol f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) with hcdef
  have hcm : Measurable c := by
    have := s02_pullback_measurable_schwarzianHol f
    simp only [hcdef]
    fun_prop
  have hSch : ∀ z ∈ unitDisc, schwarzian f z = schwarzianHol f z := fun z hz =>
    schwarzian_of_analyticAt (hf.1.analyticAt (hDo.mem_nhds hz))
  have hR : schwarzCarlesonMeasure f = (volume.restrict unitDisc).withDensity c := by
    unfold schwarzCarlesonMeasure
    refine withDensity_congr_ae ((ae_restrict_mem hD).mono fun z hz => ?_)
    simp only [hcdef, hSch z hz]
  rw [hR, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hcm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setLIntegral_congr_fun hD (fun z hz => ?_)
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have ht : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hfz : f z ∈ Ω := hf.2.2 ▸ mem_image_of_mem f hz
  have hgz : g (f z) = z := hf.2.1.leftInvOn_invFunOn hz
  simp only [hψdef, Pi.mul_apply, hGeq (f z) hfz, hgz, hcdef, hSch z hz]
  have e : (‖schwarzianHol f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) * ‖deriv f z‖ =
      (4 * ((1 - ‖z‖ ^ 2) * ‖deriv f z‖)) *
        (‖schwarzianHol f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 / 4) := by ring
  calc _ = φ (f z) * ENNReal.ofReal
        ((‖schwarzianHol f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) * ‖deriv f z‖) := by
        rw [ENNReal.ofReal_mul (p := ‖schwarzianHol f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) (by positivity)]
        ring
    _ = _ := by
        rw [e, ENNReal.ofReal_mul (p := 4 * ((1 - ‖z‖ ^ 2) * ‖deriv f z‖)) (by positivity)]
        ring

/-- Lemma 9.11(c) `lem:dictionary` (`sec09-ambient.tex:810`): `(f⁻¹)^* ω_f = 4 m s² dâ`
(tested on Borel `φ ≥ 0`), `d ≤ m ≤ 4d`, `∫_𝔻 |f'| |Sf|² (1-|z|²)³ dA ≤ 16 μ_Ω(Ω)` and
`4 μ_Ω ≤ (f⁻¹)^* ω_f ≤ 16 μ_Ω`. -/
theorem lem_dictionary_c (Ω Ωs : Set ℂ) (hΓ : IsBoundedJordanPair Ω Ωs) (f : ℂ → ℂ)
    (hf : IsConformalOnto f unitDisc Ω) :
    (∀ φ : ℂ → ℝ≥0∞, Measurable φ →
      ∫⁻ z, φ (f z) * ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f =
        ∫⁻ w, φ w * ENNReal.ofReal (4 * confRad f w) ∂curvMass Ω) ∧
      (∀ w ∈ Ω, infDist w (curveOf Ω Ωs) ≤ confRad f w ∧
        confRad f w ≤ 4 * infDist w (curveOf Ω Ωs)) ∧
      ∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f ≤ 16 * muOmega Ω Ωs univ ∧
      ∀ φ : ℂ → ℝ≥0∞, Measurable φ →
        4 * ∫⁻ w, φ w ∂muOmega Ω Ωs ≤
            ∫⁻ z, φ (f z) * ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f ∧
          ∫⁻ z, φ (f z) * ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f ≤
            16 * ∫⁻ w, φ w ∂muOmega Ω Ωs := by
  have h1 := s09_dict_c_cov Ω f hf
  have h2 := s09_confRad_bounds Ω Ωs hΓ f hf
  have hΩm : MeasurableSet Ω := (hf.isOpen isOpen_ball).measurableSet
  have hae : ∀ᵐ w ∂curvMass Ω, w ∈ Ω :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩm)
  have hdm : Measurable fun w => ENNReal.ofReal (infDist w (curveOf Ω Ωs)) :=
    ENNReal.measurable_ofReal.comp (continuous_infDist_pt _).measurable
  have hmu : ∀ φ : ℂ → ℝ≥0∞, Measurable φ → ∫⁻ w, φ w ∂muOmega Ω Ωs =
      ∫⁻ w, ENNReal.ofReal (infDist w (curveOf Ω Ωs)) * φ w ∂curvMass Ω := fun φ hφ => by
    unfold muOmega
    rw [lintegral_withDensity_eq_lintegral_mul _ hdm hφ]
    rfl
  refine ⟨h1, h2, ?_, fun φ hφ => ⟨?_, ?_⟩⟩
  · have e := h1 (fun _ => 1) measurable_const
    simp only [one_mul] at e
    rw [e, show muOmega Ω Ωs univ = ∫⁻ _, 1 ∂muOmega Ω Ωs from lintegral_one.symm,
      hmu _ measurable_const, ← lintegral_const_mul' _ _ (by norm_num)]
    refine lintegral_mono_ae (hae.mono fun w hw => ?_)
    simp only [mul_one]
    rw [← ENNReal.ofReal_ofNat 16, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by linarith [(h2 w hw).2])
  · rw [hmu φ hφ, h1 φ hφ, ← lintegral_const_mul' _ _ (by norm_num)]
    refine lintegral_mono_ae (hae.mono fun w hw => ?_)
    calc 4 * (ENNReal.ofReal (infDist w (curveOf Ω Ωs)) * φ w) =
          φ w * ENNReal.ofReal (4 * infDist w (curveOf Ω Ωs)) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
          ring
      _ ≤ φ w * ENNReal.ofReal (4 * confRad f w) :=
          mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (by linarith [(h2 w hw).1])) (by positivity)
  · rw [hmu φ hφ, h1 φ hφ, ← lintegral_const_mul' _ _ (by norm_num)]
    refine lintegral_mono_ae (hae.mono fun w hw => ?_)
    calc φ w * ENNReal.ofReal (4 * confRad f w) ≤
          φ w * ENNReal.ofReal (16 * infDist w (curveOf Ω Ωs)) :=
          mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (by linarith [(h2 w hw).2])) (by positivity)
      _ = 16 * (ENNReal.ofReal (infDist w (curveOf Ω Ωs)) * φ w) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
          ring

/-- `μ_Ω` lives on `Ω`. -/
theorem s09_muOmega_inter (Ω Ωs : Set ℂ) (hΩm : MeasurableSet Ω) (S : Set ℂ) :
    muOmega Ω Ωs S ≤ muOmega Ω Ωs (Ω ∩ S) := by
  have hac : muOmega Ω Ωs ≪ volume.restrict Ω := by
    unfold muOmega curvMass
    exact (withDensity_absolutelyContinuous _ _).trans (withDensity_absolutelyContinuous _ _)
  have h0 : muOmega Ω Ωs (S \ Ω) = 0 := hac (by
    rw [Measure.restrict_apply' hΩm, sdiff_inter_self, measure_empty])
  rw [← measure_inter_add_sdiff S hΩm, h0, add_zero, inter_comm]

/-- The defining bound of `‖μ‖_*` at one centre and one radius. -/
theorem s09_starNorm_le (μ : Measure ℂ) (Ω Γ : Set ℂ) (z : ℂ) (hz : z ∈ Γ) (r : ℝ)
    (hr : 0 < r) (hrδ : r < Metric.diam Γ) :
    μ (Ω ∩ ball z r) ≤ starNorm μ Ω Γ * ENNReal.ofReal r := by
  have h : μ (Ω ∩ ball z r) / ENNReal.ofReal r ≤ starNorm μ Ω Γ := by
    unfold starNorm
    exact le_iSup₂_of_le z hz (le_iSup₂_of_le r ⟨hr, hrδ⟩ le_rfl)
  rwa [ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top] at h

/-- Step 1 of Lemma 9.11(d): `μ_Ω(D(x₀, r)) ≤ M r` for all centres, `M = max{3‖μ_Ω‖_*, 9π}`. -/
theorem s09_dict_d_ball (Ω Ωs : Set ℂ) (hΓ : IsBoundedJordanPair Ω Ωs) (x₀ : ℂ) (r : ℝ)
    (hr : 0 < r) :
    muOmega Ω Ωs (ball x₀ r) ≤
      max (3 * starNorm (muOmega Ω Ωs) Ω (curveOf Ω Ωs)) (ENNReal.ofReal (9 * π)) *
        ENNReal.ofReal r := by
  obtain ⟨hO, -, -, -, -, hΓc⟩ := s09_bjp_basic Ω Ωs hΓ
  have hΩm : MeasurableSet Ω := hO.measurableSet
  obtain ⟨y, hy⟩ := s09_bjp_curve_nonempty Ω Ωs hΓ
  have hnotΓ : ∀ w ∈ Ω, w ∉ curveOf Ω Ωs := fun w hw h => by
    simp only [curveOf, mem_compl_iff, mem_union, not_or] at h
    exact h.1 hw
  have hdpos : ∀ w ∈ Ω, 0 < infDist w (curveOf Ω Ωs) := fun w hw =>
    (hΓc.notMem_iff_infDist_pos ⟨y, hy⟩).mp (hnotΓ w hw)
  rcases le_or_gt (2 * r) (infDist x₀ (curveOf Ω Ωs)) with hfar | hnear
  · -- far from `Γ`: Nehari and Koebe bound the density by `9/r`
    obtain ⟨f, hf⟩ := s09_bdd_riemann Ω Ωs hΓ
    have hρ : ∀ w ∈ Ω, ENNReal.ofReal (schwarzNorm Ω w ^ 2 * poincareDensity Ω w ^ 2) ≤
        ENNReal.ofReal (9 / infDist w (curveOf Ω Ωs) ^ 2) := by
      intro w hw
      refine ENNReal.ofReal_le_ofReal ?_
      have hex : ∃ a ∈ unitDisc, f a = w := by
        rw [← hf.2.2] at hw
        exact hw
      have hfg : f (Function.invFunOn f unitDisc w) = w := Function.invFunOn_eq hex
      obtain ⟨-, -, k3, k4⟩ := lem_koebe_a hf (Function.invFunOn_mem hex)
      rw [hfg, s09_infDist_compl Ω Ωs hΓ y hy w hw] at k3 k4
      obtain ⟨s0, s1⟩ := eq_nehari ⟨f, hf⟩ hw
      have hd := hdpos w hw
      have hl0 : 0 ≤ poincareDensity Ω w := le_trans (by positivity) k3
      have hs2 : schwarzNorm Ω w ^ 2 ≤ 9 / 4 := by nlinarith
      have hl2 : poincareDensity Ω w ^ 2 ≤ 4 / infDist w (curveOf Ω Ωs) ^ 2 := by
        calc poincareDensity Ω w ^ 2 ≤ (2 / infDist w (curveOf Ω Ωs)) ^ 2 :=
              pow_le_pow_left₀ hl0 k4 2
          _ = 4 / infDist w (curveOf Ω Ωs) ^ 2 := by ring
      calc schwarzNorm Ω w ^ 2 * poincareDensity Ω w ^ 2 ≤
            9 / 4 * (4 / infDist w (curveOf Ω Ωs) ^ 2) :=
            mul_le_mul hs2 hl2 (by positivity) (by norm_num)
        _ = 9 / infDist w (curveOf Ω Ωs) ^ 2 := by ring
    have hcm : curvMass Ω ≤ (volume.restrict Ω).withDensity
        fun w => ENNReal.ofReal (9 / infDist w (curveOf Ω Ωs) ^ 2) := by
      unfold curvMass
      exact withDensity_mono ((ae_restrict_mem hΩm).mono fun w hw => hρ w hw)
    have hS : MeasurableSet (ball x₀ r) := measurableSet_ball
    have hρ'm : Measurable fun w => ENNReal.ofReal (9 / infDist w (curveOf Ω Ωs) ^ 2) :=
      ENNReal.measurable_ofReal.comp
        (measurable_const.div ((continuous_infDist_pt _).measurable.pow_const 2))
    have hdm : Measurable fun w => ENNReal.ofReal (infDist w (curveOf Ω Ωs)) :=
      ENNReal.measurable_ofReal.comp (continuous_infDist_pt _).measurable
    calc muOmega Ω Ωs (ball x₀ r) =
          ∫⁻ w in ball x₀ r, ENNReal.ofReal (infDist w (curveOf Ω Ωs)) ∂curvMass Ω := by
          unfold muOmega
          rw [withDensity_apply _ hS]
      _ ≤ ∫⁻ w in ball x₀ r, ENNReal.ofReal (infDist w (curveOf Ω Ωs)) ∂((volume.restrict Ω).withDensity
            fun w => ENNReal.ofReal (9 / infDist w (curveOf Ω Ωs) ^ 2)) :=
          lintegral_mono' (Measure.restrict_mono le_rfl hcm) le_rfl
      _ = ∫⁻ w in ball x₀ r, ENNReal.ofReal (9 / infDist w (curveOf Ω Ωs) ^ 2) *
            ENNReal.ofReal (infDist w (curveOf Ω Ωs)) ∂(volume.restrict Ω) := by
          rw [restrict_withDensity hS, lintegral_withDensity_eq_lintegral_mul _ hρ'm hdm]
          rfl
      _ ≤ ∫⁻ _ in ball x₀ r, ENNReal.ofReal (9 / r) ∂(volume.restrict Ω) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae (ae_restrict_mem hΩm)] with
            w hwS hwΩ
          have hd := hdpos w hwΩ
          have hdr : r < infDist w (curveOf Ω Ωs) := by
            have h1 := infDist_le_infDist_add_dist (x := x₀) (y := w) (s := curveOf Ω Ωs)
            have h2 : dist x₀ w < r := by
              rw [dist_comm]
              exact hwS
            linarith
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [pow_two, div_mul_eq_mul_div, mul_div_mul_right _ _ hd.ne']
          exact div_le_div_of_nonneg_left (by norm_num) hr hdr.le
      _ = ENNReal.ofReal (9 / r) * volume (ball x₀ r ∩ Ω) := by
          rw [setLIntegral_const, Measure.restrict_apply hS]
      _ ≤ ENNReal.ofReal (9 / r) * volume (ball x₀ r) :=
          mul_le_mul_of_nonneg_left (measure_mono inter_subset_left) (by positivity)
      _ = ENNReal.ofReal (9 * π) * ENNReal.ofReal r := by
          rw [Complex.volume_ball, ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_coe_nnreal,
            NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
          try ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · -- near `Γ`: compare with a disk centred on `Γ`
    obtain ⟨z, hz, hxz⟩ := (Metric.infDist_lt_iff ⟨y, hy⟩).mp hnear
    have hsub : ball x₀ r ⊆ ball z (3 * r) := fun w hw => by
      rw [mem_ball] at hw ⊢
      linarith [dist_triangle w x₀ z]
    have hmono : muOmega Ω Ωs (ball x₀ r) ≤ muOmega Ω Ωs (Ω ∩ ball z (3 * r)) :=
      (measure_mono hsub).trans (s09_muOmega_inter Ω Ωs hΩm _)
    have hN3 : starNorm (muOmega Ω Ωs) Ω (curveOf Ω Ωs) * ENNReal.ofReal (3 * r) ≤
        max (3 * starNorm (muOmega Ω Ωs) Ω (curveOf Ω Ωs)) (ENNReal.ofReal (9 * π)) *
          ENNReal.ofReal r := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ← mul_assoc,
        mul_comm (starNorm _ _ _) 3]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    rcases lt_or_ge (3 * r) (Metric.diam (curveOf Ω Ωs)) with hsm | hbig
    · exact hmono.trans ((s09_starNorm_le _ _ _ z hz _ (by positivity) hsm).trans hN3)
    · obtain ⟨hball, hhalf⟩ := lem_dictionary_a Ω Ωs hΓ z hz
      obtain ⟨F, hF1, -⟩ := id hΓ
      have hw0 : F 0 ∈ Ω := hF1 ▸ mem_image_of_mem F (mem_ball_self one_pos)
      have hδ0 : 0 < Metric.diam (curveOf Ω Ωs) := by
        have := hhalf _ hw0
        have := hdpos _ hw0
        linarith
      set δ := Metric.diam (curveOf Ω Ωs) with hδ
      let s : ℕ → Set ℂ := fun n => Ω ∩ ball z (δ - δ / ((n : ℝ) + 2))
      have hsm : Monotone s := by
        intro m n hmn
        refine inter_subset_inter_right _ (ball_subset_ball ?_)
        have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
        have := div_le_div_of_nonneg_left hδ0.le (by positivity : (0 : ℝ) < (m : ℝ) + 2)
          (by linarith : (m : ℝ) + 2 ≤ n + 2)
        linarith
      have hU : Ω = ⋃ n, s n := by
        ext w
        simp only [mem_iUnion]
        constructor
        · intro hw
          have hd : dist w z < δ := hball hw
          have hpos : 0 < δ - dist w z := by linarith
          obtain ⟨n, hn⟩ := exists_nat_gt (δ / (δ - dist w z))
          refine ⟨n, hw, ?_⟩
          show dist w z < δ - δ / ((n : ℝ) + 2)
          have h1 : δ / ((n : ℝ) + 2) < δ - dist w z := by
            rw [div_lt_iff₀ (by positivity)]
            rw [div_lt_iff₀ hpos] at hn
            nlinarith
          linarith
        · rintro ⟨n, hw, -⟩
          exact hw
      have hΩle : muOmega Ω Ωs Ω ≤ starNorm (muOmega Ω Ωs) Ω (curveOf Ω Ωs) * ENNReal.ofReal δ := by
        rw [congrArg (muOmega Ω Ωs) hU, hsm.measure_iUnion]
        refine iSup_le fun n => ?_
        have hq : δ / ((n : ℝ) + 2) ≤ δ / 2 :=
          div_le_div_of_nonneg_left hδ0.le (by norm_num)
            (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
        have hq0 : 0 < δ / ((n : ℝ) + 2) := by positivity
        exact (s09_starNorm_le _ _ _ z hz _ (by linarith) (by linarith)).trans
          (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (by linarith)) (by positivity))
      calc muOmega Ω Ωs (ball x₀ r) ≤ muOmega Ω Ωs (Ω ∩ ball x₀ r) := s09_muOmega_inter Ω Ωs hΩm _
        _ ≤ muOmega Ω Ωs Ω := measure_mono inter_subset_left
        _ ≤ starNorm (muOmega Ω Ωs) Ω (curveOf Ω Ωs) * ENNReal.ofReal δ := hΩle
        _ ≤ starNorm (muOmega Ω Ωs) Ω (curveOf Ω Ωs) * ENNReal.ofReal (3 * r) :=
          mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hbig) (by positivity)
        _ ≤ _ := hN3

/-- Step 2 of Lemma 9.11(d): `k_P(X(w)) ≤ 3200 d(w) ξ₀ / (|w - x₀| + ξ₀)²`. -/
theorem s09_dict_d_kernel (Ω Ωs : Set ℂ) (hΓ : IsBoundedJordanPair Ω Ωs) (P : ℂ × ℝ)
    (hP : P ∈ UHS) (w : ℂ) (hw : w ∈ Ω) :
    ambKernel P (epstein Ω w) ≤
      3200 * infDist w (curveOf Ω Ωs) * P.2 / (‖w - P.1‖ + P.2) ^ 2 := by
  obtain ⟨-, -, -, -, -, hΓc⟩ := s09_bjp_basic Ω Ωs hΓ
  obtain ⟨y, hy⟩ := s09_bjp_curve_nonempty Ω Ωs hΓ
  have hR := s09_bdd_riemann Ω Ωs hΓ
  obtain ⟨-, -, -, e4, e5, e6⟩ := lem_ep_position hR hw
  rw [s09_infDist_compl Ω Ωs hΓ y hy w hw] at e4 e5 e6
  have hnot : w ∉ curveOf Ω Ωs := fun h => by
    simp only [curveOf, mem_compl_iff, mem_union, not_or] at h
    exact h.1 hw
  have hd0 : 0 < infDist w (curveOf Ω Ωs) := (hΓc.notMem_iff_infDist_pos ⟨y, hy⟩).mp hnot
  have hP2 : 0 < P.2 := hP
  have hQ2 : 0 < (epstein Ω w).2 := by linarith
  rw [s09_ambKernel_eq P (epstein Ω w) hP hQ2]
  set d := infDist w (curveOf Ω Ωs)
  set a := ‖(epstein Ω w).1 - P.1‖ with ha
  set b := (epstein Ω w).2
  set c := P.2
  set t := ‖w - P.1‖ with ht
  have ha0 : 0 ≤ a := norm_nonneg _
  have ht0 : 0 ≤ t := norm_nonneg _
  have htb : t ≤ a + 10 * b := by
    have := norm_sub_le_norm_sub_add_norm_sub w (epstein Ω w).1 P.1
    rw [norm_sub_rev w (epstein Ω w).1] at this
    linarith
  have h1 : (t + c) ^ 2 ≤ 200 * (a ^ 2 + (b + c) ^ 2) := by
    have h2 : t + c ≤ 10 * (a + (b + c)) := by linarith
    have h3 : (t + c) ^ 2 ≤ (10 * (a + (b + c))) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    nlinarith [sq_nonneg (a - (b + c))]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc 4 * b * c * (t + c) ^ 2 ≤ 4 * b * c * (200 * (a ^ 2 + (b + c) ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 4 * (4 * d) * c * (200 * (a ^ 2 + (b + c) ^ 2)) := by
        have : 0 ≤ c * (200 * (a ^ 2 + (b + c) ^ 2)) := by positivity
        nlinarith
    _ = 3200 * d * c * (a ^ 2 + (b + c) ^ 2) := by ring

/-- Step 3 of Lemma 9.11(d), pointwise: the dyadic majorant of `ξ₀ / (|w - x₀| + ξ₀)²`. -/
theorem s09_dyadic_le (x₀ w : ℂ) (c : ℝ) (hc : 0 < c) :
    ENNReal.ofReal (c / (‖w - x₀‖ + c) ^ 2) ≤
      (ball x₀ c).indicator (fun _ => ENNReal.ofReal (1 / c)) w +
        ∑' j : ℕ, (ball x₀ (2 ^ (j + 1) * c)).indicator
          (fun _ => ENNReal.ofReal ((1 / 4) ^ j / c)) w := by
  have ht := norm_nonneg (w - x₀)
  by_cases h0 : w ∈ ball x₀ c
  · rw [indicator_of_mem h0]
    refine le_add_right (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_div_iff₀ (by positivity) hc]
    nlinarith
  · have h1 : 1 ≤ ‖w - x₀‖ / c := by
      rw [le_div_iff₀ hc, one_mul]
      rw [mem_ball, dist_eq_norm, not_lt] at h0
      exact h0
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near h1 (by norm_num : (1 : ℝ) < 2)
    have hmem : w ∈ ball x₀ (2 ^ (j + 1) * c) := by
      rw [mem_ball, dist_eq_norm]
      rwa [div_lt_iff₀ hc] at hj2
    refine le_add_left (le_trans ?_ (ENNReal.le_tsum j))
    rw [indicator_of_mem hmem]
    refine ENNReal.ofReal_le_ofReal ?_
    have hj : 2 ^ j * c ≤ ‖w - x₀‖ := by rwa [le_div_iff₀ hc] at hj1
    have hpos : 0 < 2 ^ j * c := by positivity
    have e : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    calc c / (‖w - x₀‖ + c) ^ 2 ≤ c / (2 ^ j * c) ^ 2 :=
          div_le_div_of_nonneg_left hc.le (by positivity)
            (pow_le_pow_left₀ hpos.le (by linarith) 2)
      _ = (1 / 4) ^ j / c := by
          rw [mul_pow, e, div_pow, one_pow]
          field_simp
          try ring

/-- Lemma 9.11(d) `lem:dictionary` (`sec09-ambient.tex:814`): if `‖μ_Ω‖_* < ∞` then
`H^Ω(P) ≤ 16000 max{3 ‖μ_Ω‖_*, 9π}` for every `P ∈ ℍ³`. -/
theorem lem_dictionary_d (Ω Ωs : Set ℂ) (hΓ : IsBoundedJordanPair Ω Ωs)
    (h : starNorm (muOmega Ω Ωs) Ω (curveOf Ω Ωs) < ⊤) :
    ∀ P ∈ UHS, ambHside Ω P ≤
      16000 * max (3 * starNorm (muOmega Ω Ωs) Ω (curveOf Ω Ωs)) (ENNReal.ofReal (9 * π)) := by
  -- `h` is not needed: when `‖μ_Ω‖_* = ⊤` the right-hand side is `⊤`
  have _h := h
  intro P hP
  obtain ⟨hO, -, -, -, -, -⟩ := s09_bjp_basic Ω Ωs hΓ
  have hΩm : MeasurableSet Ω := hO.measurableSet
  set M := max (3 * starNorm (muOmega Ω Ωs) Ω (curveOf Ω Ωs)) (ENNReal.ofReal (9 * π)) with hM
  have hP2 : 0 < P.2 := hP
  have hae : ∀ᵐ w ∂curvMass Ω, w ∈ Ω :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩm)
  have hdm : Measurable fun w => ENNReal.ofReal (infDist w (curveOf Ω Ωs)) :=
    ENNReal.measurable_ofReal.comp (continuous_infDist_pt _).measurable
  set g : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (P.2 / (‖w - P.1‖ + P.2) ^ 2) with hg
  have hgm : Measurable g :=
    ENNReal.measurable_ofReal.comp (measurable_const.div
      (((measurable_id.sub measurable_const).norm.add measurable_const).pow_const 2))
  have step1 : ambHside Ω P ≤ 3200 * ∫⁻ w, g w ∂muOmega Ω Ωs := by
    unfold muOmega
    rw [lintegral_withDensity_eq_lintegral_mul _ hdm hgm,
      ← lintegral_const_mul' _ _ (by norm_num)]
    unfold ambHside
    refine lintegral_mono_ae (hae.mono fun w hw => ?_)
    simp only [Pi.mul_apply, hg]
    rw [← ENNReal.ofReal_mul infDist_nonneg, ← ENNReal.ofReal_ofNat 3200,
      ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ((s09_dict_d_kernel Ω Ωs hΓ P hP w hw).trans (le_of_eq ?_))
    ring
  have hb := fun r (hr : 0 < r) => s09_dict_d_ball Ω Ωs hΓ P.1 r hr
  have hI : ∀ (S : Set ℂ) (hS : MeasurableSet S) (v : ℝ≥0∞),
      Measurable (S.indicator fun _ => v) := fun S hS v => measurable_const.indicator hS
  have step2 : ∫⁻ w, g w ∂muOmega Ω Ωs ≤ 5 * M := by
    calc ∫⁻ w, g w ∂muOmega Ω Ωs ≤ ∫⁻ w, ((ball P.1 P.2).indicator
            (fun _ => ENNReal.ofReal (1 / P.2)) w + ∑' j : ℕ, (ball P.1 (2 ^ (j + 1) * P.2)).indicator
              (fun _ => ENNReal.ofReal ((1 / 4) ^ j / P.2)) w) ∂muOmega Ω Ωs :=
          lintegral_mono fun w => s09_dyadic_le P.1 w P.2 hP2
      _ = ENNReal.ofReal (1 / P.2) * muOmega Ω Ωs (ball P.1 P.2) + ∑' j : ℕ,
            ENNReal.ofReal ((1 / 4) ^ j / P.2) * muOmega Ω Ωs (ball P.1 (2 ^ (j + 1) * P.2)) := by
          rw [lintegral_add_left (hI _ measurableSet_ball _),
            lintegral_tsum (fun j => (hI _ measurableSet_ball _).aemeasurable),
            lintegral_indicator_const measurableSet_ball]
          congr 1
          exact tsum_congr fun j => lintegral_indicator_const measurableSet_ball _
      _ ≤ ENNReal.ofReal (1 / P.2) * (M * ENNReal.ofReal P.2) + ∑' j : ℕ,
            ENNReal.ofReal ((1 / 4) ^ j / P.2) * (M * ENNReal.ofReal (2 ^ (j + 1) * P.2)) :=
          add_le_add (mul_le_mul_of_nonneg_left (hb _ hP2) (by positivity))
            (ENNReal.tsum_le_tsum fun j =>
              mul_le_mul_of_nonneg_left (hb _ (by positivity)) (by positivity))
      _ = M + M * 4 := by
          have e0 : ENNReal.ofReal (1 / P.2) * (M * ENNReal.ofReal P.2) = M := by
            rw [mul_left_comm, ← ENNReal.ofReal_mul (p := 1 / P.2) (by positivity),
              one_div_mul_cancel hP2.ne', ENNReal.ofReal_one, mul_one]
          have ej : ∀ j : ℕ, ENNReal.ofReal ((1 / 4) ^ j / P.2) *
              (M * ENNReal.ofReal (2 ^ (j + 1) * P.2)) =
                M * ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ j) := by
            intro j
            rw [mul_left_comm, ← ENNReal.ofReal_mul (p := (1 / 4) ^ j / P.2) (by positivity)]
            congr 2
            have h4 : (1 / 4 : ℝ) ^ j = ((1 / 2) ^ j) ^ 2 := by
              rw [← pow_mul, mul_comm, pow_mul]
              norm_num
            have huv : (1 / 2 : ℝ) ^ j * 2 ^ j = 1 := by
              rw [← mul_pow]
              norm_num
            calc (1 / 4 : ℝ) ^ j / P.2 * (2 ^ (j + 1) * P.2) =
                  (1 / 4 : ℝ) ^ j * 2 ^ (j + 1) * (P.2 / P.2) := by ring
              _ = 2 * (1 / 2 : ℝ) ^ j := by
                  rw [div_self hP2.ne', mul_one, h4, pow_succ]
                  linear_combination (2 * (1 / 2 : ℝ) ^ j) * huv
          have hs : ∑' j : ℕ, ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ j) = 4 := by
            rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
              (summable_geometric_two.mul_left 2), tsum_mul_left, tsum_geometric_two,
              show (2 : ℝ) * 2 = 4 by norm_num, ENNReal.ofReal_ofNat]
          rw [e0, tsum_congr ej, ENNReal.tsum_mul_left, hs]
      _ = 5 * M := by ring
  calc ambHside Ω P ≤ 3200 * ∫⁻ w, g w ∂muOmega Ω Ωs := step1
    _ ≤ 3200 * (5 * M) := mul_le_mul_of_nonneg_left step2 (by positivity)
    _ = 16000 * M := by ring

/-- Helper for `lem_length` (L1a, Carathéodory): the Riemann map of the bounded component of a
bounded `K`-quasicircle extends continuously to `𝔻̄` and maps `∂𝔻` onto `Γ`
(`caratheodory_jordan_clean`). -/
theorem s09_len_ext {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) :
    ∃ φ : ℂ → ℂ, ContinuousOn φ (closedBall 0 1) ∧ EqOn φ f unitDisc ∧
      φ '' sphere 0 1 = curveOf Ω Ωs := by
  obtain ⟨F, hFq, hFs, hF1, hF2⟩ := hΓ
  obtain ⟨E, rfl⟩ := t1_homeomorph hFq hFs
  obtain ⟨φ, hφc, -, hφf, hφs⟩ :=
    s07_carath_core E.continuous.continuousOn E.injective.injOn hF1 hf
  refine ⟨φ, hφc, fun z hz => hφf z hz, ?_⟩
  rw [hφs, s03_cb_curve E.injective hFs hF1 hF2]
  congr 1
  ext z
  exact mem_sphere_zero_iff_norm

/-- Helper for `lem_length` (L1b): `Λ¹(γ([a, b])) ≤ Var_{[a,b]} γ` for a continuous curve
(natural parametrization, 1-Lipschitz on `[0, Var γ]`). -/
theorem s09_len_hausdorff_le {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) :
    μH[1] (γ '' Icc a b) ≤ eVariationOn γ (Icc a b) := by
  -- the continuity hypothesis `hγ` is not needed: `Λ¹(γ(I)) ≤ Var_I γ` holds for every curve
  have _h := hγ
  set s := Icc a b with hs
  rcases eq_top_or_lt_top (eVariationOn γ s) with hV | hV
  · rw [hV]
    exact le_top
  have hbv : LocallyBoundedVariationOn γ s :=
    BoundedVariationOn.locallyBoundedVariationOn hV.ne
  have has : a ∈ s := left_mem_Icc.mpr hab
  have hbs : b ∈ s := right_mem_Icc.mpr hab
  set v := variationOnFromTo γ s a with hv
  set ψ := naturalParameterization γ s a with hψ
  -- `γ = ψ ∘ v` on `s`, and `ψ` has unit speed on `v '' s`
  have himg : γ '' s = ψ '' (v '' s) := by
    rw [image_image]
    exact image_congr fun x hx =>
      (edist_eq_zero.mp (edist_naturalParameterization_eq_zero hbv has hx)).symm
  have hu := has_unit_speed_naturalParameterization γ hbv has
  have key : ∀ x ∈ v '' s, ∀ y ∈ v '' s, x ≤ y → edist (ψ x) (ψ y) ≤ edist x y := by
    intro x hx y hy hxy
    calc edist (ψ x) (ψ y) ≤ eVariationOn ψ (v '' s ∩ Icc x y) :=
          eVariationOn.edist_le ψ ⟨hx, le_rfl, hxy⟩ ⟨hy, hxy, le_rfl⟩
      _ = ENNReal.ofReal ((1 : ℝ≥0) * (y - x)) := hu hx hy
      _ = edist x y := by
          rw [NNReal.coe_one, one_mul, edist_dist, Real.dist_eq, abs_sub_comm,
            abs_of_nonneg (sub_nonneg.mpr hxy)]
  have hlip : LipschitzOnWith 1 ψ (v '' s) := by
    intro x hx y hy
    rw [ENNReal.coe_one, one_mul]
    rcases le_total x y with hxy | hxy
    · exact key x hx y hy hxy
    · rw [edist_comm, edist_comm x]
      exact key y hy x hx hxy
  have hsub : v '' s ⊆ Icc 0 (eVariationOn γ s).toReal := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := variationOnFromTo.monotoneOn hbv has has hx hx.1
    have h2 := variationOnFromTo.monotoneOn hbv has hx hbs hx.2
    rw [variationOnFromTo.self] at h1
    rw [variationOnFromTo.eq_of_le γ s hab, inter_self] at h2
    exact ⟨h1, h2⟩
  rw [himg]
  refine (hlip.hausdorffMeasure_image_le zero_le_one).trans ?_
  rw [ENNReal.coe_one, ENNReal.one_rpow, one_mul]
  calc μH[1] (v '' s) ≤ μH[1] (Icc 0 (eVariationOn γ s).toReal) := measure_mono hsub
    _ = eVariationOn γ s := by
        rw [hausdorffMeasure_real, Real.volume_Icc, sub_zero, ENNReal.ofReal_toReal hV.ne]

/-- Helper for `lem_length` (L1c): for `0 ≤ r < 1`, the variation of `t ↦ f(r e^{it})` on
`[0, 2π]` is at most `∫₀^{2π} r |f'(r e^{it})| dt`. -/
theorem s09_len_var_circle {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    eVariationOn (fun t => f (circleMap 0 r t)) (Icc 0 (2 * π)) ≤
      ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (r * ‖deriv f (circleMap 0 r t)‖) := by
  set g : ℝ → ℂ := fun t => f (circleMap 0 r t) with hg
  set F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (r * ‖deriv f (circleMap 0 r t)‖) with hF
  set g' : ℝ → ℂ := fun t => deriv f (circleMap 0 r t) * (circleMap 0 r t * I) with hg'
  have hmemD : ∀ t, circleMap 0 r t ∈ unitDisc := by
    intro t
    show circleMap 0 r t ∈ ball (0 : ℂ) 1
    rw [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr0]
    exact hr1
  have hA : AnalyticOnNhd ℂ f unitDisc := hf.analyticOnNhd (show IsOpen unitDisc from isOpen_ball)
  have hder : ∀ t, HasDerivAt g (g' t) t := fun t =>
    (hA _ (hmemD t)).differentiableAt.hasDerivAt.comp t (hasDerivAt_circleMap 0 r t)
  have hgc : Continuous g' :=
    (hA.deriv.continuousOn.comp_continuous (continuous_circleMap 0 r) hmemD).mul
      ((continuous_circleMap 0 r).mul continuous_const)
  have hnorm : ∀ t, ‖g' t‖ = r * ‖deriv f (circleMap 0 r t)‖ := by
    intro t
    show ‖deriv f (circleMap 0 r t) * (circleMap 0 r t * I)‖ = _
    rw [norm_mul, norm_mul, norm_I, norm_circleMap_zero, abs_of_nonneg hr0, mul_one, mul_comm]
  -- `|g(y) - g(x)| ≤ ∫_x^y |g'|`
  have hstep : ∀ x y : ℝ, x ≤ y → edist (g y) (g x) ≤ ∫⁻ t in Ioc x y, F t := by
    intro x y hxy
    have hint : ∫ t in x..y, g' t = g y - g x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t) (hgc.intervalIntegrable x y)
    have hnn : 0 ≤ᵐ[volume.restrict (Ioc x y)] fun t => ‖g' t‖ :=
      Eventually.of_forall fun t => norm_nonneg _
    have hI : Integrable (fun t => ‖g' t‖) (volume.restrict (Ioc x y)) :=
      (hgc.norm.integrableOn_Icc (a := x) (b := y)).mono_set Ioc_subset_Icc_self
    calc edist (g y) (g x) = ENNReal.ofReal ‖∫ t in x..y, g' t‖ := by
          rw [hint, edist_dist, dist_eq_norm]
      _ ≤ ENNReal.ofReal (∫ t in x..y, ‖g' t‖) :=
          ENNReal.ofReal_le_ofReal (intervalIntegral.norm_integral_le_integral_norm hxy)
      _ = ∫⁻ t in Ioc x y, ENNReal.ofReal ‖g' t‖ := by
          rw [intervalIntegral.integral_of_le hxy, ofReal_integral_eq_lintegral_ofReal hI hnn]
      _ = ∫⁻ t in Ioc x y, F t := lintegral_congr fun t => congrArg ENNReal.ofReal (hnorm t)
  -- partition sums telescope into `∫_{u 0}^{u n}`
  have htel : ∀ u : ℕ → ℝ, Monotone u → ∀ n : ℕ,
      ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) ≤ ∫⁻ t in Ioc (u 0) (u n), F t := by
    intro u hu n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ← Ioc_union_Ioc_eq_Ioc (hu (Nat.zero_le n)) (hu n.le_succ),
        lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)]
      exact add_le_add ih (hstep _ _ (hu n.le_succ))
  show (⨆ p : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc 0 (2 * π)},
    ∑ i ∈ Finset.range p.1, edist (g (p.2.1 (i + 1))) (g (p.2.1 i))) ≤ _
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, hus⟩ := p
  refine (htel u hu n).trans (lintegral_mono_set ?_)
  intro t ht
  exact ⟨(hus 0).1.trans_lt ht.1, ht.2.trans (hus n).2⟩

/-- Helper for `lem_length` (L1, `Λ¹ ≤ ‖φ'‖_{H¹}`): for the Riemann map `f` of the bounded
component, `Λ¹(Γ) ≤ sup_{0<r<1} ∫₀^{2π} |f'(r e^{it})| r dt`.  `Γ = φ(∂𝔻)` for the continuous
extension `φ` (L1a); `Λ¹ ≤ Var` (L1b); the variation is lower semicontinuous under the pointwise
convergence `φ(r e^{it}) → φ(e^{it})` as `r → 1⁻`; and L1c on each circle. -/
theorem s09_len_radial {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) :
    μH[1] (curveOf Ω Ωs) ≤ ⨆ r ∈ Ioo (0 : ℝ) 1,
      ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (r * ‖deriv f (circleMap 0 r t)‖) := by
  obtain ⟨φ, hφc, hφf, hφΓ⟩ := s09_len_ext hΓ hf
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  -- `Γ = γ₁([0, 2π])` with `γ_r t = φ(r e^{it})`
  have hΓeq : curveOf Ω Ωs = (fun t => φ (circleMap 0 1 t)) '' Icc 0 (2 * π) := by
    rw [← hφΓ]
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ∈ range (circleMap 0 1) := by
        rw [range_circleMap, abs_one]
        exact hz
      obtain ⟨t, rfl⟩ := hz'
      obtain ⟨s, hs, hst⟩ := (periodic_circleMap 0 1).exists_mem_Ico₀ Real.two_pi_pos t
      exact ⟨s, Ico_subset_Icc_self hs, by rw [hst]⟩
    · rintro ⟨t, -, rfl⟩
      refine ⟨circleMap 0 1 t, ?_, rfl⟩
      simp
  have hmem : ∀ {r : ℝ}, 0 ≤ r → r ≤ 1 → ∀ t, circleMap 0 r t ∈ closedBall (0 : ℂ) 1 := by
    intro r hr0 hr1 t
    rw [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr0]
    exact hr1
  have hγc : ContinuousOn (fun t => φ (circleMap 0 1 t)) (Icc 0 (2 * π)) :=
    hφc.comp_continuous (continuous_circleMap 0 1) (hmem zero_le_one le_rfl) |>.continuousOn
  rw [hΓeq]
  refine (s09_len_hausdorff_le h2π hγc).trans (le_of_forall_lt fun v hv => ?_)
  -- lower semicontinuity of the variation as `r → 1⁻`
  have hconv : ∀ t ∈ Icc 0 (2 * π), Tendsto (fun r : ℝ => φ (circleMap 0 r t)) (𝓝[<] 1)
      (𝓝 (φ (circleMap 0 1 t))) := by
    intro t _
    have hc : Tendsto (fun r : ℝ => circleMap 0 r t) (𝓝[<] 1)
        (𝓝[closedBall (0 : ℂ) 1] (circleMap 0 1 t)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hcr : Continuous (fun r : ℝ => circleMap 0 r t) := by
          show Continuous (fun r : ℝ => (0 : ℂ) + (r : ℂ) * Complex.exp (t * I))
          fun_prop
        exact (hcr.tendsto 1).mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos)] with r hr
        exact hmem hr.1.le hr.2.le t
    exact (hφc _ (hmem zero_le_one le_rfl t)).tendsto.comp hc
  obtain ⟨r, hvr, hr⟩ := ((eVariationOn.lowerSemicontinuous_aux hconv hv).and
    (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos))).exists
  have heq : eVariationOn (fun t => φ (circleMap 0 r t)) (Icc 0 (2 * π)) =
      eVariationOn (fun t => f (circleMap 0 r t)) (Icc 0 (2 * π)) := by
    refine eVariationOn.eq_of_eqOn fun t _ => hφf ?_
    show circleMap 0 r t ∈ ball (0 : ℂ) 1
    rw [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos hr.1]
    exact hr.2
  calc v < eVariationOn (fun t => f (circleMap 0 r t)) (Icc 0 (2 * π)) := heq ▸ hvr
    _ ≤ ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (r * ‖deriv f (circleMap 0 r t)‖) :=
        s09_len_var_circle hf.1 hr.1.le hr.2
    _ ≤ _ := le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) 1) =>
        ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (r * ‖deriv f (circleMap 0 r t)‖)) r hr

/-- Helper for `lem_length` (L2a): `f'` has a holomorphic square root on `𝔻` for a conformal
`f` (`deriv_ne_zero_of_injOn`, `kb_exists_sqrt`). -/
theorem s09_len_sqrt {f : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F unitDisc ∧ ∀ z ∈ unitDisc, F z ^ 2 = deriv f z :=
  kb_exists_sqrt (hf.1.deriv isOpen_ball) fun _ hz =>
    deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz

/-- Helper for `lem_length` (L2b, Parseval on circles, upper half): for `G` holomorphic on `𝔻`
and `0 ≤ r < 1`, `∫₀^{2π} |G(r e^{it})|² dt ≤ 2π Σ |a_n|² r^{2n}` with `a_n = G⁽ⁿ⁾(0)/n!`
(Taylor polynomials: `s12_circle_parseval`; pointwise `hasSum_taylorSeries_on_ball`; Fatou). -/
theorem s09_len_parseval {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G unitDisc) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (‖G (circleMap 0 r t)‖ ^ 2) ≤
      ENNReal.ofReal (2 * π) *
        ∑' n : ℕ, ENNReal.ofReal (‖iteratedDeriv n G 0 / (n.factorial : ℂ)‖ ^ 2 * r ^ (2 * n)) := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, c = fun n => iteratedDeriv n G 0 / (n.factorial : ℂ) :=
    ⟨_, rfl⟩
  have hmemD : ∀ t, circleMap 0 r t ∈ unitDisc := by
    intro t
    show circleMap 0 r t ∈ ball (0 : ℂ) 1
    rw [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr0]
    exact hr1
  have hs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (G z) := by
    intro z hz
    have h := Complex.hasSum_taylorSeries_on_ball hG hz
    simp only [sub_zero, smul_eq_mul] at h
    convert h using 2 with n
    rw [hc]
    ring
  have hcont : ∀ N : ℕ,
      Continuous fun t => ‖∑ n ∈ Finset.range N, c n * circleMap 0 r t ^ n‖ ^ 2 := fun N =>
    (continuous_finsetSum _ fun n _ =>
      continuous_const.mul ((continuous_circleMap 0 r).pow n)).norm.pow 2
  -- Parseval for the Taylor polynomials
  have hpoly : ∀ N : ℕ, ∫⁻ t in Ioc 0 (2 * π),
      ENNReal.ofReal (‖∑ n ∈ Finset.range N, c n * circleMap 0 r t ^ n‖ ^ 2) =
      ENNReal.ofReal (2 * π * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 * r ^ (2 * n)) := by
    intro N
    have h := s12_circle_parseval (Finset.range N) id (injOn_id _) c hr0
    rw [Real.circleAverage_def, smul_eq_mul] at h
    simp only [id_eq] at h
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((hcont N).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (Eventually.of_forall fun t => sq_nonneg _),
      ← intervalIntegral.integral_of_le (by positivity), ← h, ← mul_assoc,
      mul_inv_cancel₀ (by positivity), one_mul]
  -- pointwise convergence and Fatou
  have hpt : ∀ t, Tendsto (fun N : ℕ => ENNReal.ofReal
      (‖∑ n ∈ Finset.range N, c n * circleMap 0 r t ^ n‖ ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (‖G (circleMap 0 r t)‖ ^ 2))) := fun t =>
    (ENNReal.continuous_ofReal.tendsto _).comp
      (((hs _ (hmemD t)).tendsto_sum_nat).norm.pow 2)
  have hmeas : ∀ N : ℕ, AEMeasurable (fun t => ENNReal.ofReal
      (‖∑ n ∈ Finset.range N, c n * circleMap 0 r t ^ n‖ ^ 2)) (volume.restrict (Ioc 0 (2 * π))) :=
    fun N => (ENNReal.continuous_ofReal.comp (hcont N)).measurable.aemeasurable
  calc ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (‖G (circleMap 0 r t)‖ ^ 2)
      = ∫⁻ t in Ioc 0 (2 * π), liminf (fun N : ℕ => ENNReal.ofReal
          (‖∑ n ∈ Finset.range N, c n * circleMap 0 r t ^ n‖ ^ 2)) atTop :=
        lintegral_congr fun t => ((hpt t).liminf_eq).symm
    _ ≤ liminf (fun N : ℕ => ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal
          (‖∑ n ∈ Finset.range N, c n * circleMap 0 r t ^ n‖ ^ 2)) atTop :=
        lintegral_liminf_le' hmeas
    _ ≤ _ := by
        refine liminf_le_of_frequently_le' (Frequently.of_forall fun N => ?_)
        rw [hpoly N, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_sum_of_nonneg fun n _ => by positivity]
        subst hc
        exact mul_le_mul_of_nonneg_left (sum_le_tsum _) (by positivity)

/-- Helper for `lem_length` (L2d, area integral by coefficients, lower half): for `F`
holomorphic on `𝔻`, `2π Σ_m |F^{(m+2)}(0)/m!|² · 3/((m+1)(m+2)(m+3)(m+4)) ≤ ∫_𝔻 |F''|² (1 - |z|²)³`
(dilations `F''(ρ·)`: `s02_vd_disc_parseval`, `s02_vd_radial3`, `s02_vd_lim`; `s02_vd_scale`;
`ρ → 1` on each partial sum). -/
theorem s09_len_area {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F unitDisc) :
    ENNReal.ofReal (2 * π) * ∑' m : ℕ, ENNReal.ofReal
        (‖iteratedDeriv (m + 2) F 0 / (m.factorial : ℂ)‖ ^ 2 *
          (3 / (((m : ℝ) + 1) * (m + 2) * (m + 3) * (m + 4)))) ≤
      ∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv (deriv F) z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, c = fun n => iteratedDeriv n F 0 / (n.factorial : ℂ) :=
    ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℂ, b = fun m => iteratedDeriv (m + 2) F 0 / (m.factorial : ℂ) :=
    ⟨_, rfl⟩
  have hs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (F z) := by
    intro z hz
    have h := Complex.hasSum_taylorSeries_on_ball hF hz
    simp only [sub_zero, smul_eq_mul] at h
    convert h using 2 with n
    rw [hc]
    ring
  have hbcoef : ∀ n : ℕ, b n = c (n + 1 + 1) * ((n + 1 + 1 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) := by
    intro n
    rw [hb, hc]
    have h1 : ((n + 1 + 1).factorial : ℂ) =
        ((n : ℂ) + 1 + 1) * ((n : ℂ) + 1) * (n.factorial : ℂ) := by
      rw [Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have h2 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have h3 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have h4 : (n : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
    show iteratedDeriv (n + 2) F 0 / (n.factorial : ℂ) =
      iteratedDeriv (n + 1 + 1) F 0 / ((n + 1 + 1).factorial : ℂ) * ((n + 1 + 1 : ℕ) : ℂ) *
        ((n + 1 : ℕ) : ℂ)
    rw [h1]
    push_cast
    field_simp
  have hs2 : ∀ z ∈ unitDisc, HasSum (fun n => b n * z ^ n) (deriv (deriv F) z) := by
    intro z hz
    have h1 : ∀ w ∈ unitDisc,
        HasSum (fun n => c (n + 1) * ((n + 1 : ℕ) : ℂ) * w ^ n) (deriv F w) :=
      fun w hw => TakhtajanTeo.Ch2.faber_powerSeries_deriv hs hw
    have h2 := TakhtajanTeo.Ch2.faber_powerSeries_deriv h1 hz
    convert h2 using 2 with n
    rw [hbcoef n]
  have hsub : unitDisc ⊆ closedBall (0 : ℂ) 1 := ball_subset_closedBall
  have hw : ∀ z ∈ unitDisc, 0 ≤ 1 - ‖z‖ ^ 2 := fun z hz => by
    have := mem_ball_zero_iff.mp hz
    nlinarith [norm_nonneg z]
  -- for a dilation `0 < ρ < 1`
  have hρ : ∀ M : ℕ, ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ENNReal.ofReal (ρ ^ 2 * (2 * π * ∑ n ∈ Finset.range M, ‖b n * (ρ : ℂ) ^ n‖ ^ 2 *
        (3 / (((n : ℝ) + 1) * (n + 2) * (n + 3) * (n + 4))))) ≤
      ∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv (deriv F) z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) := by
    intro M ρ hρ0 hρ1
    have hU := TakhtajanTeo.Ch2.bergmanTaylorPoly_dilate_uniform hs2 hρ0 hρ1
    simp only [TakhtajanTeo.Ch2.bergmanTaylorPoly_eval] at hU
    have hmaps : MapsTo (fun z : ℂ => (ρ : ℂ) * z) (closedBall 0 1) unitDisc := by
      intro z hz
      apply mem_ball_zero_iff.mpr
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
      exact (mul_le_of_le_one_right hρ0.le (mem_closedBall_zero_iff.mp hz)).trans_lt hρ1
    have hcF : ContinuousOn (fun z => deriv (deriv F) ((ρ : ℂ) * z)) (closedBall 0 1) :=
      ((hF.deriv isOpen_ball).deriv isOpen_ball).continuousOn.comp (by fun_prop) hmaps
    have hL := s02_vd_lim (fun t => (1 - t ^ 2) ^ 3) (by fun_prop)
      (fun N => continuous_finsetSum _ fun n _ => by fun_prop) hcF hU
    have hpar : ∀ N : ℕ, ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 3 *
        ‖∑ n ∈ Finset.range N, b n * (ρ : ℂ) ^ n * z ^ n‖ ^ 2 =
        2 * π * ∑ n ∈ Finset.range N, ‖b n * (ρ : ℂ) ^ n‖ ^ 2 *
          (3 / (((n : ℝ) + 1) * (n + 2) * (n + 3) * (n + 4))) := by
      intro N
      have h := s02_vd_disc_parseval (fun t => (1 - t ^ 2) ^ 3) (by fun_prop)
        (fun n => b n * (ρ : ℂ) ^ n) N
      rw [h]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [s02_vd_radial3]
    have hreal : 2 * π * ∑ n ∈ Finset.range M, ‖b n * (ρ : ℂ) ^ n‖ ^ 2 *
        (3 / (((n : ℝ) + 1) * (n + 2) * (n + 3) * (n + 4))) ≤
        ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 3 * ‖deriv (deriv F) ((ρ : ℂ) * z)‖ ^ 2 := by
      refine ge_of_tendsto hL (eventually_atTop.2 ⟨M, fun N hN => ?_⟩)
      rw [hpar N]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono hN) fun n _ _ => by positivity) (by positivity)
    have hcont : ContinuousOn (fun z => (1 - ‖z‖ ^ 2) ^ 3 *
        ‖(ρ : ℂ) * deriv (deriv F) ((ρ : ℂ) * z)‖ ^ 2) (closedBall 0 1) :=
      (by fun_prop : Continuous fun z : ℂ => (1 - ‖z‖ ^ 2) ^ 3).continuousOn.mul
        ((continuousOn_const.mul hcF).norm.pow 2)
    have hR : ρ ^ 2 * ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 3 *
        ‖deriv (deriv F) ((ρ : ℂ) * z)‖ ^ 2 =
        ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 3 * ‖(ρ : ℂ) * deriv (deriv F) ((ρ : ℂ) * z)‖ ^ 2 := by
      rw [← integral_const_mul]
      congr 1
      funext z
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
      ring
    have hnn : 0 ≤ᵐ[volume.restrict unitDisc] fun z => (1 - ‖z‖ ^ 2) ^ 3 *
        ‖(ρ : ℂ) * deriv (deriv F) ((ρ : ℂ) * z)‖ ^ 2 :=
      (ae_restrict_iff' (measurableSet_ball : MeasurableSet unitDisc)).mpr
        (ae_of_all _ fun z hz => mul_nonneg (pow_nonneg (hw z hz) 3) (sq_nonneg _))
    calc ENNReal.ofReal (ρ ^ 2 * (2 * π * ∑ n ∈ Finset.range M, ‖b n * (ρ : ℂ) ^ n‖ ^ 2 *
          (3 / (((n : ℝ) + 1) * (n + 2) * (n + 3) * (n + 4)))))
        ≤ ENNReal.ofReal (∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 3 *
            ‖(ρ : ℂ) * deriv (deriv F) ((ρ : ℂ) * z)‖ ^ 2) := by
          rw [← hR]
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hreal (by positivity))
      _ = ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 *
            ‖(ρ : ℂ) * deriv (deriv F) ((ρ : ℂ) * z)‖ ^ 2) :=
          ofReal_integral_eq_lintegral_ofReal
            (hcont.integrableOn_compact (isCompact_closedBall 0 1) |>.mono_set hsub) hnn
      _ ≤ ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 * ‖deriv (deriv F) z‖ ^ 2) :=
          s02_vd_scale (measurable_deriv _) hρ0 hρ1.le
      _ = _ := lintegral_congr fun z => by rw [mul_comm]
  -- `ρ → 1` on each partial sum
  have hpart : ∀ M : ℕ, ENNReal.ofReal (2 * π * ∑ n ∈ Finset.range M, ‖b n‖ ^ 2 *
      (3 / (((n : ℝ) + 1) * (n + 2) * (n + 3) * (n + 4)))) ≤
      ∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv (deriv F) z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) := by
    intro M
    have hfc : Continuous fun ρ : ℝ => ENNReal.ofReal (ρ ^ 2 * (2 * π *
        ∑ n ∈ Finset.range M, ‖b n * (ρ : ℂ) ^ n‖ ^ 2 *
          (3 / (((n : ℝ) + 1) * (n + 2) * (n + 3) * (n + 4))))) :=
      ENNReal.continuous_ofReal.comp ((continuous_pow 2).mul (continuous_const.mul
        (continuous_finsetSum _ fun n _ =>
          ((continuous_const.mul (Complex.continuous_ofReal.pow n)).norm.pow 2).mul
            continuous_const)))
    have h := le_of_tendsto ((hfc.tendsto 1).mono_left nhdsWithin_le_nhds)
      (by
        filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos)] with ρ hρ'
        exact hρ M ρ hρ'.1 hρ'.2)
    simp only [Complex.ofReal_one, one_pow, mul_one, one_mul] at h
    exact h
  -- the `iSup` over partial sums
  have key : ENNReal.ofReal (2 * π) * ∑' m : ℕ, ENNReal.ofReal (‖b m‖ ^ 2 *
      (3 / (((m : ℝ) + 1) * (m + 2) * (m + 3) * (m + 4)))) ≤
      ∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv (deriv F) z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) := by
    rw [ENNReal.tsum_eq_iSup_nat, ENNReal.mul_iSup]
    refine iSup_le fun M => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun n _ => by positivity,
      ← ENNReal.ofReal_mul (by positivity)]
    exact hpart M
  subst hb
  exact key

/-- Helper for `lem_length` (L2, Littlewood–Paley by coefficients): for `F` holomorphic on `𝔻`
and `0 ≤ r < 1`, `∫₀^{2π} |F(r e^{it})|² dt ≤ 2π(|F(0)|² + |F'(0)|²) + 2 ∫_𝔻 |F''|² (1-|z|²)³`.
By L2b (upper) and L2d (lower), termwise: `|a_n|² r^{2n} ≤ |a_n|²`, and for `n = m + 2`,
`|a_n|² ≤ 2 |F^{(n)}(0)/m!|² · 3/((m+1)(m+2)(m+3)(m+4))` since
`(m+3)(m+4) ≤ 6 (m+1)(m+2)`. -/
theorem s09_len_L2 {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F unitDisc) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (‖F (circleMap 0 r t)‖ ^ 2) ≤
      ENNReal.ofReal (2 * π * (‖F 0‖ ^ 2 + ‖deriv F 0‖ ^ 2)) +
        2 * ∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv (deriv F) z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) := by
  refine (s09_len_parseval hF hr0 hr1).trans ?_
  refine le_trans ?_ (add_le_add le_rfl (mul_le_mul_of_nonneg_left (s09_len_area hF) (by positivity)))
  rw [tsum_eq_zero_add' CompleteLattice.summable, tsum_eq_zero_add' CompleteLattice.summable]
  have hr : ∀ n : ℕ, r ^ (2 * n) ≤ 1 := fun n => pow_le_one₀ hr0 hr1.le
  have h0 : ENNReal.ofReal (‖iteratedDeriv 0 F 0 / ((Nat.factorial 0 : ℕ) : ℂ)‖ ^ 2 *
      r ^ (2 * 0)) ≤ ENNReal.ofReal (‖F 0‖ ^ 2) := by
    refine ENNReal.ofReal_le_ofReal ?_
    rw [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    exact mul_le_of_le_one_right (sq_nonneg _) (hr 0)
  have h1 : ENNReal.ofReal (‖iteratedDeriv (0 + 1) F 0 / ((Nat.factorial (0 + 1) : ℕ) : ℂ)‖ ^ 2 *
      r ^ (2 * (0 + 1))) ≤ ENNReal.ofReal (‖deriv F 0‖ ^ 2) := by
    refine ENNReal.ofReal_le_ofReal ?_
    rw [zero_add, iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, div_one]
    exact mul_le_of_le_one_right (sq_nonneg _) (hr 1)
  have hterm : ∀ m : ℕ,
      ENNReal.ofReal (‖iteratedDeriv (m + 1 + 1) F 0 / ((Nat.factorial (m + 1 + 1) : ℕ) : ℂ)‖ ^ 2 *
        r ^ (2 * (m + 1 + 1))) ≤
      2 * ENNReal.ofReal (‖iteratedDeriv (m + 2) F 0 / (m.factorial : ℂ)‖ ^ 2 *
          (3 / (((m : ℝ) + 1) * (m + 2) * (m + 3) * (m + 4)))) := by
    intro m
    have hfac : (m + 1 + 1).factorial = (m + 2) * (m + 1) * m.factorial := by
      rw [Nat.factorial_succ, Nat.factorial_succ]
      ring
    rw [hfac, show m + 1 + 1 = m + 2 from rfl, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_div, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    push_cast
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    have hN : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    set A := ‖iteratedDeriv (m + 2) F 0‖ with hA
    set N := (m.factorial : ℝ) with hNdef
    have hX : 0 ≤ (A / N) ^ 2 := sq_nonneg _
    calc (A / (((m : ℝ) + 2) * (m + 1) * N)) ^ 2 * r ^ (2 * (m + 2))
        ≤ (A / (((m : ℝ) + 2) * (m + 1) * N)) ^ 2 := mul_le_of_le_one_right (sq_nonneg _) (hr _)
      _ = (A / N) ^ 2 * (1 / (((m : ℝ) + 1) * (m + 2)) ^ 2) := by
          field_simp
      _ ≤ (A / N) ^ 2 * (6 / (((m : ℝ) + 1) * (m + 2) * (m + 3) * (m + 4))) := by
          refine mul_le_mul_of_nonneg_left ?_ hX
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_nonneg hm hm, mul_nonneg (mul_nonneg hm hm) hm,
            mul_nonneg (mul_nonneg hm hm) (mul_nonneg hm hm)]
      _ = 2 * ((A / N) ^ 2 * (3 / (((m : ℝ) + 1) * (m + 2) * (m + 3) * (m + 4)))) := by ring
  calc _ ≤ ENNReal.ofReal (2 * π) * (ENNReal.ofReal (‖F 0‖ ^ 2) +
          (ENNReal.ofReal (‖deriv F 0‖ ^ 2) + ∑' m : ℕ, 2 * ENNReal.ofReal
            (‖iteratedDeriv (m + 2) F 0 / (m.factorial : ℂ)‖ ^ 2 *
              (3 / (((m : ℝ) + 1) * (m + 2) * (m + 3) * (m + 4)))))) :=
        mul_le_mul_of_nonneg_left (add_le_add h0 (add_le_add h1 (tsum_le_tsum hterm)))
          (by positivity)
    _ = _ := by
        rw [ENNReal.tsum_mul_left, ENNReal.ofReal_mul (p := 2 * π) (q := ‖F 0‖ ^ 2 + ‖deriv F 0‖ ^ 2)
          (by positivity),
          ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
        ring

/-- Shared helper (Cauchy estimate on Whitney discs; used by `lem_length` and §10): if `φ` is
holomorphic on `𝔻` with `(1 - |w|²)² |φ(w)| ≤ M`, then `(1 - |z|²)³ |φ'(z)| ≤ 64 M` (Cauchy on the
circle of radius `(1 - |z|)/2` about `z`). -/
theorem s09_cauchy_disk {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {M : ℝ}
    (hM : ∀ w ∈ unitDisc, (1 - ‖w‖ ^ 2) ^ 2 * ‖φ w‖ ≤ M) :
    ∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) ^ 3 * ‖deriv φ z‖ ≤ 64 * M := by
  intro z hz
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hd : 0 < 1 - ‖z‖ := by linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (1 - ‖z‖) / 2 := ⟨_, rfl⟩
  have hR0 : 0 < R := by rw [hR]; positivity
  have hcl : ∀ w ∈ closedBall z R, (1 - ‖z‖) / 2 ≤ 1 - ‖w‖ ^ 2 ∧ w ∈ unitDisc := by
    intro w hw
    have h1 : ‖w - z‖ ≤ R := mem_closedBall_iff_norm.mp hw
    have h2 := norm_le_norm_add_norm_sub' w z
    rw [hR] at h1
    have hw1 : ‖w‖ < 1 := by linarith
    exact ⟨by nlinarith [norm_nonneg w], mem_ball_zero_iff.mpr hw1⟩
  have hdc : DiffContOnCl ℂ φ (ball z R) :=
    (hφ.mono fun w hw => (hcl w (by rwa [closure_ball z hR0.ne'] at hw)).2).diffContOnCl
  have hM0 : 0 ≤ M := le_trans (by positivity) (hM 0 (mem_ball_self one_pos))
  have hC : ∀ w ∈ sphere z R, ‖φ w‖ ≤ 4 * M / (1 - ‖z‖) ^ 2 := by
    intro w hw
    obtain ⟨h1, hwD⟩ := hcl w (sphere_subset_closedBall hw)
    have h2 := hM w hwD
    have h3 : ((1 - ‖z‖) / 2) ^ 2 ≤ (1 - ‖w‖ ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    rw [le_div_iff₀ (by positivity)]
    nlinarith [norm_nonneg (φ w)]
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR0 hdc hC
  have e : 4 * M / (1 - ‖z‖) ^ 2 / R = 8 * M / (1 - ‖z‖) ^ 3 := by
    rw [hR]
    field_simp
    ring
  rw [e, le_div_iff₀ (by positivity)] at h
  have hw3 : (1 - ‖z‖ ^ 2) ^ 3 ≤ 8 * (1 - ‖z‖) ^ 3 := by
    have h1 : 1 - ‖z‖ ^ 2 ≤ 2 * (1 - ‖z‖) := by nlinarith [norm_nonneg z]
    have h0 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    calc (1 - ‖z‖ ^ 2) ^ 3 ≤ (2 * (1 - ‖z‖)) ^ 3 := pow_le_pow_left₀ h0 h1 3
      _ = 8 * (1 - ‖z‖) ^ 3 := by ring
  nlinarith [mul_le_mul_of_nonneg_right hw3 (norm_nonneg (deriv φ z))]

/-- Shared helper (Cauchy estimate in `ρ`-form; used by `lem:ambient-adjoint` (a)): if
`s = |S(f⁻¹)|/λ² ≤ M` on `Ω`, then `λ⁻³ |∂_w S(f⁻¹)| ≤ 38 M` on `Ω`. From `s09_cauchy_disk` for
`Sf` (`(1-|z|²)² |Sf| ≤ 4M`), the chain rule for `S(f⁻¹)(f z) f'(z)² = -Sf(z)`
(`s02_schwarzian_inv_comp`) and Koebe `(1-|z|²)|f''/f'| ≤ 6` (`lem_koebe_b`):
`λ⁻³|∂S(f⁻¹)|(f z) = (1-|z|²)³ |(Sf)' - 2 Sf f''/f'| / 8 ≤ (256 + 48) M / 8`. -/
theorem s09_cauchy_rho {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {M : ℝ}
    (hM : ∀ w ∈ Ω, schwarzNorm Ω w ≤ M) {w : ℂ} (hw : w ∈ Ω) :
    ‖deriv (schwarzian (Function.invFunOn f unitDisc)) w‖ ≤ 38 * M * poincareDensity Ω w ^ 3 := by
  set ψ := Function.invFunOn f unitDisc with hψdef
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hψ : IsConformalOnto ψ Ω unitDisc := hf.symm isOpen_ball
  -- `S(ψ)` is holomorphic near `w`
  have hψ'ne : ∀ x ∈ Ω, deriv ψ x ≠ 0 := fun x hx =>
    deriv_ne_zero_of_injOn hΩo hψ.1 hψ.2.1 hx
  have h0 : DifferentiableOn ℂ ψ Ω := hψ.1
  have h1 : DifferentiableOn ℂ (deriv ψ) Ω := h0.deriv hΩo
  have h2 : DifferentiableOn ℂ (deriv (deriv ψ)) Ω := h1.deriv hΩo
  have hg : DifferentiableOn ℂ (fun w => deriv (deriv ψ) w / deriv ψ w) Ω :=
    h2.div h1 hψ'ne
  have hS : DifferentiableOn ℂ (fun w => deriv (fun w => deriv (deriv ψ) w / deriv ψ w) w -
      (1 / 2) * (deriv (deriv ψ) w / deriv ψ w) ^ 2) Ω :=
    (hg.deriv hΩo).sub ((hg.pow 2).const_mul _)
  have hTeq : schwarzian ψ =ᶠ[𝓝 w] fun w => deriv (fun w => deriv (deriv ψ) w / deriv ψ w) w -
      (1 / 2) * (deriv (deriv ψ) w / deriv ψ w) ^ 2 := by
    filter_upwards [hΩo.mem_nhds hw] with x hx
    exact schwarzian_of_analyticAt (h0.analyticAt (hΩo.mem_nhds hx))
  have hTd : HasDerivAt (schwarzian ψ) (deriv (schwarzian ψ) w) w :=
    ((hS.differentiableAt (hΩo.mem_nhds hw)).congr_of_eventuallyEq hTeq).hasDerivAt
  -- the point `z = ψ w` of `𝔻`
  have hwi : w ∈ f '' unitDisc := hf.2.2.symm ▸ hw
  have hz : ψ w ∈ unitDisc := hψ.2.2 ▸ mem_image_of_mem ψ hw
  have hfz : f (ψ w) = w := Function.invFunOn_eq hwi
  set z := ψ w with hzdef
  have hzn : ∀ᶠ ζ in 𝓝 z, ζ ∈ unitDisc := isOpen_ball.mem_nhds hz
  have hfd : HasDerivAt f (deriv f z) z := (hf.1.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hf1 : DifferentiableOn ℂ (deriv f) unitDisc := hf.1.deriv isOpen_ball
  have hf2d : HasDerivAt (deriv f) (deriv (deriv f) z) z :=
    (hf1.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hf'ne : deriv f z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz
  have hTd' : HasDerivAt (schwarzian ψ) (deriv (schwarzian ψ) w) (f z) := by
    rw [hfz]
    exact hTd
  -- differentiate `S(ψ)(f ζ) f'(ζ)² = -Sf(ζ)` at `z`
  have hL := (hTd'.comp z hfd).mul (hf2d.pow 2)
  have hR : HasDerivAt (fun ζ => -schwarzian f ζ) (-deriv (schwarzian f) z) z :=
    ((s02_va_schwarz_diff hf).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.neg
  have heq : (fun ζ => -schwarzian f ζ) =ᶠ[𝓝 z]
      fun ζ => (schwarzian ψ ∘ f) ζ * deriv f ζ ^ 2 := by
    filter_upwards [hzn] with ζ hζ
    exact (s02_schwarzian_inv_comp hf hζ).symm
  have key := hR.unique (hL.congr_of_eventuallyEq heq)
  simp only [Function.comp_apply, Pi.pow_apply] at key
  rw [hfz] at key
  norm_num at key
  have hT0 := s02_schwarzian_inv_comp hf hz
  rw [hfz] at hT0
  set a := deriv f z with hadef
  set b := deriv (deriv f) z with hbdef
  set S := schwarzian f z with hSdef
  set S' := deriv (schwarzian f) z with hS'def
  set T' := deriv (schwarzian ψ) w with hT'def
  set T0 := schwarzian ψ w with hT0def
  have hTa : T' * a ^ 3 = -S' + 2 * S * (b / a) := by
    have hS0 : S = -(T0 * a ^ 2) := by linear_combination hT0
    have e2 : S * (b / a) = -(T0 * a * b) := by
      rw [hS0]
      field_simp
    rw [mul_assoc, e2]
    linear_combination -key
  set q := b / a with hqdef
  -- the three bounds
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  set d := 1 - ‖z‖ ^ 2 with hddef
  have hd : 0 < d := by nlinarith [norm_nonneg z]
  have hM0 : 0 ≤ M := by
    refine le_trans ?_ (hM w hw)
    rw [eq_def_s hf hw]
    positivity
  have hM4 : ∀ ζ ∈ unitDisc, (1 - ‖ζ‖ ^ 2) ^ 2 * ‖schwarzian f ζ‖ ≤ 4 * M := by
    intro ζ hζ
    have h := hM (f ζ) (hf.2.2 ▸ mem_image_of_mem f hζ)
    rw [eq_s_disk hf hζ, div_le_iff₀ (by norm_num)] at h
    linarith
  have hC := s09_cauchy_disk (s02_va_schwarz_diff hf) hM4 z hz
  have hSd : d ^ 2 * ‖S‖ ≤ 4 * M := hM4 z hz
  have hK : d * ‖q‖ ≤ 6 := by
    have hk := (lem_koebe_b hf hz).1
    have e : (1 - ‖z‖ ^ 2 : ℂ) * b / a = ((d : ℝ) : ℂ) * q := by
      rw [hddef, hqdef]
      push_cast
      ring
    rw [e] at hk
    have h2 : ‖((d : ℝ) : ℂ) * q‖ ≤ 4 + ‖2 * conj z‖ :=
      (norm_le_norm_add_norm_sub' _ _).trans (by linarith)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hd.le, norm_mul, Complex.norm_conj,
      show ‖(2 : ℂ)‖ = 2 by norm_num] at h2
    linarith
  have hnorm : ‖T'‖ * ‖a‖ ^ 3 ≤ ‖S'‖ + 2 * ‖S‖ * ‖q‖ := by
    rw [← norm_pow, ← norm_mul, hTa]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_mul, norm_mul]
    norm_num
  have hprod : d ^ 2 * ‖S‖ * (d * ‖q‖) ≤ 4 * M * 6 :=
    mul_le_mul hSd hK (by positivity) (by positivity)
  have htot : ‖T'‖ * (d ^ 3 * ‖a‖ ^ 3) ≤ 304 * M := by
    have h3 := mul_le_mul_of_nonneg_left hnorm (pow_nonneg hd.le 3)
    calc ‖T'‖ * (d ^ 3 * ‖a‖ ^ 3) = d ^ 3 * (‖T'‖ * ‖a‖ ^ 3) := by ring
      _ ≤ d ^ 3 * (‖S'‖ + 2 * ‖S‖ * ‖q‖) := h3
      _ = d ^ 3 * ‖S'‖ + 2 * (d ^ 2 * ‖S‖ * (d * ‖q‖)) := by ring
      _ ≤ 64 * (4 * M) + 2 * (4 * M * 6) := add_le_add hC (by linarith)
      _ = 304 * M := by ring
  -- `λ(w) = 2/((1-|z|²)|f'(z)|)`
  have hlam := eq_lambda_f hf hz
  rw [hfz] at hlam
  have ha : 0 < ‖a‖ := norm_pos_iff.mpr hf'ne
  have hlame : poincareDensity Ω w = 2 / (d * ‖a‖) := by
    rw [eq_div_iff (by positivity)]
    have e : poincareDensity Ω w * ‖a‖ = 2 / d := hlam
    calc poincareDensity Ω w * (d * ‖a‖) = poincareDensity Ω w * ‖a‖ * d := by ring
      _ = 2 := by rw [e]; field_simp
  rw [hlame, show 38 * M * (2 / (d * ‖a‖)) ^ 3 = 304 * M / (d ^ 3 * ‖a‖ ^ 3) by
    field_simp
    ring, le_div_iff₀ (by positivity)]
  exact htot

/-! W1b helpers: weighted Wirtinger data `‖F‖ ≤ p λ^k`, `‖∂F‖ + ‖∂̄F‖ ≤ q λ^{k+1}`. -/

theorem s09_au_wb_const (c x : ℂ) {l : ℝ} :
    ∃ a b : ℂ, (∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun _ : ℂ => c) L x ∧ ∀ v, L v = a * v + b * conj v) ∧
      ‖c‖ ≤ ‖c‖ * l ^ (0 : ℤ) ∧ ‖a‖ + ‖b‖ ≤ 0 * l ^ ((0 : ℤ) + 1) :=
  ⟨0, 0, s09_au_wd_const c x, by simp, by simp⟩

theorem s09_au_wb_add {F G : ℂ → ℂ} {x : ℂ} {l : ℝ} {k k' : ℤ} {p q p' q' : ℝ}
    (hF : ∃ a b : ℂ, (∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt F L x ∧ ∀ v, L v = a * v + b * conj v) ∧
      ‖F x‖ ≤ p * l ^ k ∧ ‖a‖ + ‖b‖ ≤ q * l ^ (k + 1))
    (hG : ∃ a b : ℂ, (∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt G L x ∧ ∀ v, L v = a * v + b * conj v) ∧
      ‖G x‖ ≤ p' * l ^ k' ∧ ‖a‖ + ‖b‖ ≤ q' * l ^ (k' + 1)) (hk : k' = k) :
    ∃ a b : ℂ, (∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun y => F y + G y) L x ∧
        ∀ v, L v = a * v + b * conj v) ∧
      ‖F x + G x‖ ≤ (p + p') * l ^ k ∧ ‖a‖ + ‖b‖ ≤ (q + q') * l ^ (k + 1) := by
  subst hk
  obtain ⟨a, b, hd, h1, h2⟩ := hF
  obtain ⟨c, d, hd', h1', h2'⟩ := hG
  refine ⟨_, _, s09_au_wd_add hd hd', ?_, ?_⟩
  · calc ‖F x + G x‖ ≤ ‖F x‖ + ‖G x‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  · have := norm_add_le a c
    have := norm_add_le b d
    linarith

theorem s09_au_wb_sub {F G : ℂ → ℂ} {x : ℂ} {l : ℝ} {k k' : ℤ} {p q p' q' : ℝ}
    (hF : ∃ a b : ℂ, (∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt F L x ∧ ∀ v, L v = a * v + b * conj v) ∧
      ‖F x‖ ≤ p * l ^ k ∧ ‖a‖ + ‖b‖ ≤ q * l ^ (k + 1))
    (hG : ∃ a b : ℂ, (∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt G L x ∧ ∀ v, L v = a * v + b * conj v) ∧
      ‖G x‖ ≤ p' * l ^ k' ∧ ‖a‖ + ‖b‖ ≤ q' * l ^ (k' + 1)) (hk : k' = k) :
    ∃ a b : ℂ, (∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun y => F y - G y) L x ∧
        ∀ v, L v = a * v + b * conj v) ∧
      ‖F x - G x‖ ≤ (p + p') * l ^ k ∧ ‖a‖ + ‖b‖ ≤ (q + q') * l ^ (k + 1) := by
  subst hk
  obtain ⟨a, b, hd, h1, h2⟩ := hF
  obtain ⟨c, d, hd', h1', h2'⟩ := hG
  refine ⟨_, _, s09_au_wd_sub hd hd', ?_, ?_⟩
  · calc ‖F x - G x‖ ≤ ‖F x‖ + ‖G x‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  · have := norm_sub_le a c
    have := norm_sub_le b d
    linarith

theorem s09_au_wb_mul {F G : ℂ → ℂ} {x : ℂ} {l : ℝ} (hl : 0 < l) {k k' : ℤ} {p q p' q' : ℝ}
    (hF : ∃ a b : ℂ, (∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt F L x ∧ ∀ v, L v = a * v + b * conj v) ∧
      ‖F x‖ ≤ p * l ^ k ∧ ‖a‖ + ‖b‖ ≤ q * l ^ (k + 1))
    (hG : ∃ a b : ℂ, (∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt G L x ∧ ∀ v, L v = a * v + b * conj v) ∧
      ‖G x‖ ≤ p' * l ^ k' ∧ ‖a‖ + ‖b‖ ≤ q' * l ^ (k' + 1)) :
    ∃ a b : ℂ, (∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun y => F y * G y) L x ∧
        ∀ v, L v = a * v + b * conj v) ∧
      ‖F x * G x‖ ≤ (p * p') * l ^ (k + k') ∧
        ‖a‖ + ‖b‖ ≤ (q * p' + p * q') * l ^ (k + k' + 1) := by
  obtain ⟨a, b, hd, h1, h2⟩ := hF
  obtain ⟨c, d, hd', h1', h2'⟩ := hG
  have hl0 := hl.ne'
  have e1 : l ^ (k + k') = l ^ k * l ^ k' := zpow_add₀ hl0 k k'
  have e2 : l ^ (k + k' + 1) = l ^ k * l ^ k' * l := by rw [zpow_add_one₀ hl0, e1]
  have e3 : l ^ (k + 1) = l ^ k * l := zpow_add_one₀ hl0 k
  have e4 : l ^ (k' + 1) = l ^ k' * l := zpow_add_one₀ hl0 k'
  have hF0 : 0 ≤ p * l ^ k := (norm_nonneg _).trans h1
  have hab : 0 ≤ ‖a‖ + ‖b‖ := by positivity
  have hcd : 0 ≤ ‖c‖ + ‖d‖ := by positivity
  refine ⟨_, _, s09_au_wd_mul hd hd', ?_, ?_⟩
  · rw [norm_mul, e1]
    calc ‖F x‖ * ‖G x‖ ≤ (p * l ^ k) * (p' * l ^ k') :=
          mul_le_mul h1 h1' (norm_nonneg _) hF0
      _ = _ := by ring
  · calc ‖a * G x + F x * c‖ + ‖b * G x + F x * d‖
        ≤ (‖a‖ + ‖b‖) * ‖G x‖ + ‖F x‖ * (‖c‖ + ‖d‖) := by
          have h3 := norm_add_le (a * G x) (F x * c)
          have h4 := norm_add_le (b * G x) (F x * d)
          simp only [norm_mul] at h3 h4
          linarith
      _ ≤ (q * l ^ (k + 1)) * (p' * l ^ k') + (p * l ^ k) * (q' * l ^ (k' + 1)) :=
          add_le_add (mul_le_mul h2 h1' (norm_nonneg _) (hab.trans h2))
            (mul_le_mul h1 h2' hcd hF0)
      _ = _ := by rw [e2, e3, e4]; ring

theorem s09_au_wb_inv {F : ℂ → ℂ} {x : ℂ} {l : ℝ} (hl : 0 < l) {k : ℤ} {p q m : ℝ}
    (hF : ∃ a b : ℂ, (∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt F L x ∧ ∀ v, L v = a * v + b * conj v) ∧
      ‖F x‖ ≤ p * l ^ k ∧ ‖a‖ + ‖b‖ ≤ q * l ^ (k + 1))
    (hm : 0 < m) (hlow : m * l ^ k ≤ ‖F x‖) :
    ∃ a b : ℂ, (∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun y => (F y)⁻¹) L x ∧
        ∀ v, L v = a * v + b * conj v) ∧
      ‖(F x)⁻¹‖ ≤ (1 / m) * l ^ (-k) ∧ ‖a‖ + ‖b‖ ≤ (q / m ^ 2) * l ^ (-k + 1) := by
  obtain ⟨a, b, hd, -, h2⟩ := hF
  have hl0 := hl.ne'
  have hlk : 0 < l ^ k := zpow_pos hl k
  have hml : 0 < m * l ^ k := mul_pos hm hlk
  have hFn : 0 < ‖F x‖ := hml.trans_le hlow
  have hF0 : F x ≠ 0 := norm_pos_iff.mp hFn
  have en : l ^ (-k) = (l ^ k)⁻¹ := zpow_neg l k
  have en1 : l ^ (-k + 1) = (l ^ k)⁻¹ * l := by rw [zpow_add_one₀ hl0, en]
  have e3 : l ^ (k + 1) = l ^ k * l := zpow_add_one₀ hl0 k
  refine ⟨_, _, s09_au_wd_inv hd hF0, ?_, ?_⟩
  · rw [norm_inv, en]
    calc ‖F x‖⁻¹ ≤ (m * l ^ k)⁻¹ := inv_anti₀ hml hlow
      _ = _ := by field_simp
  · rw [norm_div, norm_div, norm_neg, norm_neg, norm_pow, ← add_div]
    calc (‖a‖ + ‖b‖) / ‖F x‖ ^ 2 ≤ (q * l ^ (k + 1)) / (m * l ^ k) ^ 2 :=
          div_le_div₀ ((by positivity : (0 : ℝ) ≤ ‖a‖ + ‖b‖).trans h2) h2 (by positivity)
            (pow_le_pow_left₀ hml.le hlow 2)
      _ = _ := by rw [en1, e3]; field_simp

theorem s09_au_wb_conj {F : ℂ → ℂ} {x : ℂ} {l : ℝ} {k : ℤ} {p q : ℝ}
    (hF : ∃ a b : ℂ, (∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt F L x ∧ ∀ v, L v = a * v + b * conj v) ∧
      ‖F x‖ ≤ p * l ^ k ∧ ‖a‖ + ‖b‖ ≤ q * l ^ (k + 1)) :
    ∃ a b : ℂ, (∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun y => conj (F y)) L x ∧
        ∀ v, L v = a * v + b * conj v) ∧
      ‖conj (F x)‖ ≤ p * l ^ k ∧ ‖a‖ + ‖b‖ ≤ q * l ^ (k + 1) := by
  obtain ⟨a, b, hd, h1, h2⟩ := hF
  refine ⟨_, _, s09_au_wd_conj hd, by rwa [Complex.norm_conj], ?_⟩
  rw [Complex.norm_conj, Complex.norm_conj]
  linarith

/-- Helper (W1b) for `s09_au_hess`: `|D²X(u, v)| ≤ 2100 λ |u| |v|` (in the sum norm
`‖·.1‖ + |·.2|`) where `|A| ≤ λ` and `s ≤ 1/4`; from the weighted data of `P, Q, R`. -/
theorem s09_au_hs_D2X {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) (hA : ‖logDensityDz Ω w‖ ≤ poincareDensity Ω w) (hs : schwarzNorm Ω w ≤ 1 / 4)
    (u v : ℂ) :
    ‖(fderiv ℝ (fderiv ℝ (epstein Ω)) w u v).1‖ + |(fderiv ℝ (fderiv ℝ (epstein Ω)) w u v).2| ≤
      2100 * poincareDensity Ω w * ‖u‖ * ‖v‖ := by
  have hΩ : IsOpen Ω := hf.isOpen isOpen_ball
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hw
  have hlΩ : ∀ y ∈ Ω, 0 < poincareDensity Ω y := fun y hy => s02_poincareDensity_pos ⟨f, hf⟩ hy
  obtain ⟨Ll, hLl, hLlv⟩ := s02_fff_hasFDerivAt_lambda hf hw
  obtain ⟨LA, hLA, hLAv⟩ := s02_fff_hasFDerivAt_A hf hw
  have hSd : DifferentiableAt ℂ (schwarzian (Function.invFunOn f unitDisc)) w := by
    have hψ : IsConformalOnto (Function.invFunOn f unitDisc) Ω unitDisc := hf.symm isOpen_ball
    have hψ'ne : ∀ x ∈ Ω, deriv (Function.invFunOn f unitDisc) x ≠ 0 := fun x hx =>
      deriv_ne_zero_of_injOn hΩ hψ.1 hψ.2.1 hx
    have h0 : DifferentiableOn ℂ (Function.invFunOn f unitDisc) Ω := hψ.1
    have h1 := h0.deriv hΩ
    have hg := (h1.deriv hΩ).div h1 hψ'ne
    have hS := (hg.deriv hΩ).sub ((hg.pow 2).const_mul (1 / 2 : ℂ))
    refine (hS.congr fun x hx => ?_).differentiableAt (hΩ.mem_nhds hw)
    exact schwarzian_of_analyticAt (h0.analyticAt (hΩ.mem_nhds hx))
  have hdX := fun y (hy : y ∈ Ω) v => s09_au_tn_dX hf hy v
  have hXd : DifferentiableAt ℝ (fderiv ℝ (epstein Ω)) w := by
    have hc : ContDiffAt ℝ 2 (epstein Ω) w :=
      ((lem_fff_smooth ⟨f, hf⟩).contDiffAt (hΩ.mem_nhds hw)).of_le (by simp)
    exact (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  -- `|S| ≤ λ²/4`, `|∂S| ≤ 57 λ³`
  have hSn : ‖schwarzian (Function.invFunOn f unitDisc) w‖ ≤ 1 / 4 * poincareDensity Ω w ^ 2 := by
    rw [eq_def_s hf hw, div_le_iff₀ (by positivity)] at hs
    linarith
  have hS' := s09_cauchy_rho hf (fun y hy => (eq_nehari ⟨f, hf⟩ hy).2) hw
  generalize schwarzian (Function.invFunOn f unitDisc) = S at hSd hdX hSn hS' hLAv ⊢
  generalize epstein Ω = X at hdX hXd ⊢
  generalize logDensityDz Ω = A at hLlv hLA hLAv hdX hA ⊢
  generalize poincareDensity Ω = lam at hl hlΩ hLl hLlv hLAv hdX hA hSn hS' ⊢
  have hDr : ∀ y, ((lam y ^ 2 + 4 * ‖A y‖ ^ 2 : ℝ) : ℂ) =
      (lam y : ℂ) * lam y + 4 * (A y * conj (A y)) := by
    intro y
    push_cast
    rw [Complex.mul_conj']
    ring
  have hDpos : ∀ y ∈ Ω, (lam y : ℂ) * lam y + 4 * (A y * conj (A y)) ≠ 0 := fun y hy => by
    rw [← hDr]
    exact_mod_cast (by have := hlΩ y hy; positivity : (0 : ℝ) < lam y ^ 2 + 4 * ‖A y‖ ^ 2).ne'
  have hl2 : lam w ^ ((1 : ℤ) + 1) = lam w ^ 2 := by norm_num
  have hl3 : lam w ^ ((2 : ℤ) + 1) = lam w ^ 3 := by norm_num
  -- weighted Wirtinger data at `w`
  have bl : ∃ a b : ℂ, (∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun y => (lam y : ℂ)) L w ∧
      ∀ v, L v = a * v + b * conj v) ∧ ‖(lam w : ℂ)‖ ≤ 1 * lam w ^ (1 : ℤ) ∧
        ‖a‖ + ‖b‖ ≤ 2 * lam w ^ ((1 : ℤ) + 1) := by
    refine ⟨_, _, s09_au_wd_ofReal hLl (c := (lam w : ℂ) * A w)
      (fun v => by rw [hLlv, mul_assoc, Complex.re_ofReal_mul]; ring), ?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_of_nonneg hl.le]; simp
    · rw [Complex.norm_conj, norm_mul, Complex.norm_real, Real.norm_of_nonneg hl.le, hl2]
      nlinarith
  have bA : ∃ a b : ℂ, (∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt A L w ∧
      ∀ v, L v = a * v + b * conj v) ∧ ‖A w‖ ≤ 1 * lam w ^ (1 : ℤ) ∧
        ‖a‖ + ‖b‖ ≤ 2 * lam w ^ ((1 : ℤ) + 1) := by
    refine ⟨_, _, ⟨LA, hLA, hLAv⟩, by simpa using hA, ?_⟩
    rw [hl2, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have h1 := norm_add_le (A w ^ 2) (S w / 2)
    rw [norm_pow, norm_div, Complex.norm_ofNat] at h1
    have h2 : ‖A w‖ ^ 2 ≤ lam w ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
    nlinarith
  have bB := s09_au_wb_conj bA
  have bS : ∃ a b : ℂ, (∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt S L w ∧
      ∀ v, L v = a * v + b * conj v) ∧ ‖S w‖ ≤ 1 / 4 * lam w ^ (2 : ℤ) ∧
        ‖a‖ + ‖b‖ ≤ 57 * lam w ^ ((2 : ℤ) + 1) := by
    refine ⟨_, _, s09_au_wd_holo hSd, by simpa using hSn, ?_⟩
    rw [hl3, norm_zero, add_zero]
    linarith
  have bSb := s09_au_wb_conj bS
  have hlow : 1 * lam w ^ ((1 : ℤ) + 1) ≤ ‖(lam w : ℂ) * lam w + 4 * (A w * conj (A w))‖ := by
    rw [← hDr, Complex.norm_real, Real.norm_of_nonneg (by positivity), hl2]
    nlinarith [norm_nonneg (A w)]
  have bD := s09_au_wb_add (s09_au_wb_mul hl bl bl)
    (s09_au_wb_mul hl (s09_au_wb_const 4 w) (s09_au_wb_mul hl bA bB)) (by norm_num)
  have bDi := s09_au_wb_inv hl bD one_pos hlow
  have bDD := s09_au_wb_mul hl bDi bDi
  obtain ⟨aP, bP, dP, -, hP⟩ := s09_au_wb_mul hl (s09_au_wb_mul hl (s09_au_wb_const 2 w)
    (s09_au_wb_sub (s09_au_wb_mul hl (s09_au_wb_mul hl bl bl) (s09_au_wb_mul hl bl bl))
      (s09_au_wb_mul hl (s09_au_wb_const 4 w) (s09_au_wb_mul hl bS (s09_au_wb_mul hl bB bB)))
      (by norm_num))) bDD
  obtain ⟨aQ, bQ, dQ, -, hQ⟩ := s09_au_wb_mul hl (s09_au_wb_mul hl
    (s09_au_wb_mul hl (s09_au_wb_const 2 w) (s09_au_wb_mul hl bl bl))
      (s09_au_wb_sub bSb (s09_au_wb_mul hl (s09_au_wb_const 4 w) (s09_au_wb_mul hl bB bB))
        (by norm_num))) bDD
  obtain ⟨aR, bR, dR, -, hR⟩ := s09_au_wb_mul hl (s09_au_wb_mul hl
    (s09_au_wb_mul hl (s09_au_wb_const (-4) w) bl)
      (s09_au_wb_add (s09_au_wb_mul hl (s09_au_wb_mul hl bl bl) bA) (s09_au_wb_mul hl bS bB)
        (by norm_num))) bDD
  norm_num at hP hQ hR
  -- `D²X(u, v)` from the data of `P, Q, R`
  obtain ⟨L1, hL1, hL1v⟩ := s09_au_wd_add (s09_au_wd_mul dP (s09_au_wd_const v w))
    (s09_au_wd_mul dQ (s09_au_wd_const (conj v) w))
  obtain ⟨L2, hL2, hL2v⟩ := s09_au_wd_re (s09_au_wd_mul (s09_au_wd_const 2 w)
    (s09_au_wd_mul dR (s09_au_wd_const v w)))
  have hU : HasFDerivAt (fun y => fderiv ℝ X y v) (L1.prod L2) w := by
    refine (hL1.prodMk hL2).congr_of_eventuallyEq ?_
    filter_upwards [hΩ.mem_nhds hw] with y hy
    have hD := hDpos y hy
    rw [hdX y hy v, Prod.mk.injEq]
    refine ⟨?_, congrArg Complex.re ?_⟩
    all_goals
      rw [show (lam y : ℂ) ^ 2 + 4 * (A y * conj (A y)) =
        (lam y : ℂ) * lam y + 4 * (A y * conj (A y)) by ring]
      generalize (lam y : ℂ) * lam y + 4 * (A y * conj (A y)) = D at hD ⊢
      field_simp
  have h2 := congrArg (fun L : ℂ →L[ℝ] ℂ × ℝ => L u)
    ((hXd.hasFDerivAt.clm_apply (hasFDerivAt_const v w)).unique hU)
  beta_reduce at h2
  rw [add_apply, ContinuousLinearMap.comp_zero, zero_apply, zero_add,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.prod_apply, hL1v, hL2v] at h2
  rw [h2]
  simp only [mul_zero, zero_add, add_zero, zero_mul]
  -- the bound
  have hu := norm_nonneg u
  have hv := norm_nonneg v
  have e1 : ‖(aP * v + aQ * conj v) * u + (bP * v + bQ * conj v) * conj u‖ ≤
      (‖aP‖ + ‖bP‖) * ‖u‖ * ‖v‖ + (‖aQ‖ + ‖bQ‖) * ‖u‖ * ‖v‖ := by
    rw [show (aP * v + aQ * conj v) * u + (bP * v + bQ * conj v) * conj u =
      (aP * u + bP * conj u) * v + (aQ * u + bQ * conj u) * conj v by ring]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_conj]
    have h3 := norm_add_le (aP * u) (bP * conj u)
    have h4 := norm_add_le (aQ * u) (bQ * conj u)
    simp only [norm_mul, Complex.norm_conj] at h3 h4
    nlinarith [mul_le_mul_of_nonneg_right h3 hv, mul_le_mul_of_nonneg_right h4 hv]
  have e2 : |(2 * (aR * v) * u + 2 * (bR * v) * conj u).re| ≤
      2 * ((‖aR‖ + ‖bR‖) * ‖u‖ * ‖v‖) := by
    rw [show 2 * (aR * v) * u + 2 * (bR * v) * conj u = 2 * ((aR * u + bR * conj u) * v) by ring]
    refine (Complex.abs_re_le_norm _).trans ?_
    simp only [norm_mul, Complex.norm_ofNat]
    have h3 := norm_add_le (aR * u) (bR * conj u)
    simp only [norm_mul, Complex.norm_conj] at h3
    nlinarith [mul_le_mul_of_nonneg_right h3 hv]
  have huv : 0 ≤ ‖u‖ * ‖v‖ := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hP huv, mul_le_mul_of_nonneg_right hQ huv,
    mul_le_mul_of_nonneg_right hR huv]

/-- Helper (W1b) for `s09_au_hess`: polarization, `|∇²k(U, V)| ≤ c (g(U,U) + g(V,V))/2` from the
diagonal bound, for a symmetric second derivative. -/
theorem s09_au_hs_pol {k : ℂ × ℝ → ℝ} {Q : ℂ × ℝ} (hs : IsSymmSndFDerivAt ℝ k Q) {c : ℝ}
    (hb : ∀ V, |hypHess k Q V V| ≤ c * hypMetric Q V V) (U V : ℂ × ℝ) :
    |hypHess k Q U V| ≤ c * (hypMetric Q U U + hypMetric Q V V) / 2 := by
  have e : hypHess k Q (U + V) (U + V) - hypHess k Q (U - V) (U - V) = 4 * hypHess k Q U V := by
    unfold hypHess eucInner
    simp only [map_add, map_sub, add_apply, sub_apply, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub, Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im]
    rw [hs V U]
    ring
  have e' : c * hypMetric Q (U + V) (U + V) + c * hypMetric Q (U - V) (U - V) =
      2 * (c * (hypMetric Q U U + hypMetric Q V V)) := by
    unfold hypMetric eucInner
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Complex.add_re,
      Complex.sub_re, Complex.add_im, Complex.sub_im]
    ring
  have h1 := hb (U + V)
  have h2 := hb (U - V)
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith

/-- Helper (W1b) for `s09_au_hess`: `|dk_P(W)| ≤ k_P (‖W₁‖ + |W₂|)/ξ`
(`lem_ambient_kernel_c` (i)). -/
theorem s09_au_hs_dk {P : ℂ × ℝ} (hP : P ∈ UHS) {Q : ℂ × ℝ} (hQ : Q ∈ UHS) (W : ℂ × ℝ) :
    |fderiv ℝ (ambKernel P) Q W| ≤ ambKernel P Q * (‖W.1‖ + |W.2|) / Q.2 := by
  have hQ2 : (0 : ℝ) < Q.2 := hQ
  obtain ⟨hk0, -, -⟩ := (lem_ambient_kernel_a P hP).2 Q hQ
  have h1 := (lem_ambient_kernel_c P hP Q hQ).1 W
  have hW : hypMetric Q W W ≤ ((‖W.1‖ + |W.2|) / Q.2) ^ 2 := by
    unfold hypMetric eucInner
    rw [div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hn : W.1.re * W.1.re + W.1.im * W.1.im = ‖W.1‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
    have ha : W.2 * W.2 = |W.2| ^ 2 := by rw [sq_abs]; ring
    rw [hn, ha]
    nlinarith [norm_nonneg W.1, abs_nonneg W.2]
  have h2 : fderiv ℝ (ambKernel P) Q W ^ 2 ≤ (ambKernel P Q * ((‖W.1‖ + |W.2|) / Q.2)) ^ 2 := by
    rw [mul_pow]
    exact h1.trans (mul_le_mul_of_nonneg_left hW (sq_nonneg _))
  have h3 := Real.abs_le_sqrt h2
  rw [Real.sqrt_sq (by positivity)] at h3
  rw [mul_div_assoc]
  exact h3

/-- Helper (W1b) for `s09_au_hess`: `g(dX u, dX u) ≤ (5λ|u|/2)²` and
`‖(dX u)₁‖ + |(dX u)₂| ≤ 4 ξ λ |u|`
(`eq_dX_norm_always`). -/
theorem s09_au_hs_dX {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) (hQ : (0 : ℝ) < (epstein Ω w).2) (u : ℂ) :
    hypMetric (epstein Ω w) (fderiv ℝ (epstein Ω) w u) (fderiv ℝ (epstein Ω) w u) ≤
        (5 / 2 * (poincareDensity Ω w * ‖u‖)) ^ 2 ∧
      ‖(fderiv ℝ (epstein Ω) w u).1‖ + |(fderiv ℝ (epstein Ω) w u).2| ≤
        4 * (epstein Ω w).2 * poincareDensity Ω w * ‖u‖ := by
  have h := eq_dX_norm_always hΩ hw u
  set a := fderiv ℝ (epstein Ω) w u
  set q := epstein Ω w
  have hgi : hypMetric q a a = hypInner q a a := by
    unfold hypMetric eucInner hypInner
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have h0 : 0 ≤ hypInner q a a := by
    rw [← hgi]
    unfold hypMetric eucInner
    apply div_nonneg _ (sq_nonneg _)
    nlinarith [mul_self_nonneg a.1.re, mul_self_nonneg a.1.im, mul_self_nonneg a.2]
  have hg : hypInner q a a ≤ (5 / 2 * (poincareDensity Ω w * ‖u‖)) ^ 2 := by
    rw [← Real.sq_sqrt h0]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  refine ⟨hgi ▸ hg, ?_⟩
  have hn : hypInner q a a = (‖a.1‖ ^ 2 + |a.2| ^ 2) / q.2 ^ 2 := by
    unfold hypInner
    rw [Complex.mul_conj', sq_abs]
    norm_cast
    ring
  rw [hn, div_le_iff₀ (by positivity)] at hg
  have hl := s02_poincareDensity_pos hΩ hw
  have hN : (‖a.1‖ + |a.2|) ^ 2 ≤ (4 * q.2 * poincareDensity Ω w * ‖u‖) ^ 2 := by
    nlinarith [sq_nonneg (‖a.1‖ - |a.2|), sq_nonneg (q.2 * poincareDensity Ω w * ‖u‖)]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hN

/-- Helper (W1b) for `s09_au_hess`: `‖Γ_ℍ(U, V)‖ ≤ 3 ‖U‖ ‖V‖ / ξ` in the sum norm. -/
theorem s09_au_hs_hypChr (q U V : ℂ × ℝ) (hq : 0 < q.2) :
    ‖(hypChristoffel q U V).1‖ + |(hypChristoffel q U V).2| ≤
      3 * ((‖U.1‖ + |U.2|) * (‖V.1‖ + |V.2|)) / q.2 := by
  have hq0 := hq.ne'
  have e1 : (hypChristoffel q U V).1 = (-(U.2 / q.2)) • V.1 + (-(V.2 / q.2)) • U.1 := by
    simp [hypChristoffel]
  have e2 : (hypChristoffel q U V).2 = ((conj U.1 * V.1).re - U.2 * V.2) / q.2 := by
    simp only [hypChristoffel, Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_one]
    field_simp
    ring
  have h1 : ‖(hypChristoffel q U V).1‖ ≤ (|U.2| * ‖V.1‖ + |V.2| * ‖U.1‖) / q.2 := by
    rw [e1]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_neg, abs_div,
      abs_div, abs_of_pos hq]
    ring
  have h2 : |(hypChristoffel q U V).2| ≤ (‖U.1‖ * ‖V.1‖ + |U.2| * |V.2|) / q.2 := by
    rw [e2, abs_div, abs_of_pos hq]
    apply div_le_div_of_nonneg_right _ hq.le
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    have := Complex.abs_re_le_norm (conj U.1 * V.1)
    rw [norm_mul, Complex.norm_conj] at this
    linarith
  have h3 : (|U.2| * ‖V.1‖ + |V.2| * ‖U.1‖) / q.2 + (‖U.1‖ * ‖V.1‖ + |U.2| * |V.2|) / q.2 ≤
      3 * ((‖U.1‖ + |U.2|) * (‖V.1‖ + |V.2|)) / q.2 := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hq.le
    nlinarith [norm_nonneg U.1, norm_nonneg V.1, abs_nonneg U.2, abs_nonneg V.2,
      mul_nonneg (norm_nonneg U.1) (norm_nonneg V.1), mul_nonneg (abs_nonneg U.2) (abs_nonneg V.2),
      mul_nonneg (norm_nonneg U.1) (abs_nonneg V.2), mul_nonneg (abs_nonneg U.2) (norm_nonneg V.1)]
  linarith

/-- Helper (W1b) for `s09_au_hess`: `|Γ_ρ(X, Y)| ≤ 12 λ |X| |Y|` where `|A| ≤ λ`
(`∇ log λ = dφ(1) + dφ(i) i`, `dφ(v) = 2 Re(A v)`). -/
theorem s09_au_hs_rhoChr {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) (hA : ‖logDensityDz Ω w‖ ≤ poincareDensity Ω w) (X Y : ℂ) :
    ‖rhoChristoffel Ω w X Y‖ ≤ 12 * poincareDensity Ω w * ‖X‖ * ‖Y‖ := by
  obtain ⟨L, hL⟩ := s02_fff_hasFDerivAt_log hf hw
  have hd : ∀ v, |fderiv ℝ (fun x => Real.log (poincareDensity Ω x)) w v| ≤
      2 * poincareDensity Ω w * ‖v‖ := by
    intro v
    rw [hL.fderiv, s02_fff_wirtinger hL v, abs_mul, abs_two]
    have h1 := Complex.abs_re_le_norm (wirtingerDz (fun x => Real.log (poincareDensity Ω x)) w * v)
    rw [norm_mul] at h1
    have h2 : ‖wirtingerDz (fun x => Real.log (poincareDensity Ω x)) w‖ ≤ poincareDensity Ω w := hA
    nlinarith [mul_le_mul_of_nonneg_right h2 (norm_nonneg v)]
  have hg : ‖logDensityGrad Ω w‖ ≤ 4 * poincareDensity Ω w := by
    unfold logDensityGrad
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := hd 1
    have h2 := hd I
    rw [norm_one] at h1
    rw [Complex.norm_I] at h2
    linarith
  have hr : ∀ a b : ℂ, ‖(((conj a * b).re : ℝ) : ℂ)‖ ≤ ‖a‖ * ‖b‖ := fun a b => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have := Complex.abs_re_le_norm (conj a * b)
    rwa [norm_mul, Complex.norm_conj] at this
  unfold rhoChristoffel
  have n := norm_sub_le ((((conj (logDensityGrad Ω w) * X).re : ℝ) : ℂ) * Y +
    (((conj (logDensityGrad Ω w) * Y).re : ℝ) : ℂ) * X)
    ((((conj X * Y).re : ℝ) : ℂ) * logDensityGrad Ω w)
  have n2 := norm_add_le ((((conj (logDensityGrad Ω w) * X).re : ℝ) : ℂ) * Y)
    ((((conj (logDensityGrad Ω w) * Y).re : ℝ) : ℂ) * X)
  simp only [norm_mul] at n n2
  have hX := norm_nonneg X
  have hY := norm_nonneg Y
  have hG := norm_nonneg (logDensityGrad Ω w)
  have t1 := mul_le_mul_of_nonneg_right (hr (logDensityGrad Ω w) X) hY
  have t2 := mul_le_mul_of_nonneg_right (hr (logDensityGrad Ω w) Y) hX
  have t3 := mul_le_mul_of_nonneg_right (hr X Y) hG
  have t4 : ‖logDensityGrad Ω w‖ * ‖X‖ * ‖Y‖ ≤ 4 * poincareDensity Ω w * ‖X‖ * ‖Y‖ := by
    have := mul_le_mul_of_nonneg_right hg (mul_nonneg hX hY)
    linarith [this]
  nlinarith

/-- Helper (W1b) for `s09_au_hess`: the off-trace chain rule
`D²(k∘X)(u, v) = ∇²k(dX u, dX v) + dk(D²X(u, v) + Γ_ℍ(dX u, dX v))`. -/
theorem s09_au_hs_chain2 {k : ℂ × ℝ → ℝ} {X : ℂ → ℂ × ℝ} {w : ℂ} (hk : ContDiffAt ℝ 2 k (X w))
    (hX : ContDiffAt ℝ 2 X w) (u v : ℂ) :
    fderiv ℝ (fderiv ℝ (fun x => k (X x))) w u v =
      hypHess k (X w) (fderiv ℝ X w u) (fderiv ℝ X w v) +
        fderiv ℝ k (X w) (fderiv ℝ (fderiv ℝ X) w u v +
          hypChristoffel (X w) (fderiv ℝ X w u) (fderiv ℝ X w v)) := by
  have hkd : DifferentiableAt ℝ (fderiv ℝ k) (X w) :=
    (hk.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hXd : DifferentiableAt ℝ (fderiv ℝ X) w :=
    (hX.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hev : fderiv ℝ (fun x => k (X x)) =ᶠ[𝓝 w]
      fun x => (fderiv ℝ k (X x)).comp (fderiv ℝ X x) := by
    filter_upwards [hX.eventually (by decide),
      hX.continuousAt.eventually (hk.eventually (by decide))] with x hx hkx
    exact fderiv_comp x (hkx.differentiableAt (by norm_num)) (hx.differentiableAt (by norm_num))
  have hc : HasFDerivAt (fun x => fderiv ℝ k (X x))
      ((fderiv ℝ (fderiv ℝ k) (X w)).comp (fderiv ℝ X w)) w :=
    hkd.hasFDerivAt.comp w (hX.differentiableAt (by norm_num)).hasFDerivAt
  have hD := (hc.clm_comp hXd.hasFDerivAt).fderiv
  rw [hev.fderiv_eq, hD]
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  unfold hypHess hypChristoffel eucInner
  simp only [map_add, map_smul, smul_eq_mul, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  simp only [div_eq_mul_inv]
  ring

/-- Lemma 9.4 `lem:ambient-adjoint` (a), second half (`sec09-ambient.tex:211`), pointwise form:
`|∇²κ|_ρ ≤ C₂ κ` wherever `s ≤ 1/4`, `κ = k_P ∘ X`; `C₂` is absolute.  (On `G₀`, where `s < ε`,
this is the paper's bound.) -/
theorem s09_au_hess : ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ P ∈ UHS,
    ∀ w ∈ Ω, schwarzNorm Ω w ≤ 1 / 4 →
      rhoTensorNorm Ω (rhoHess Ω (fun x => ambKernel P (epstein Ω x))) w ≤
        C₂ * ambKernel P (epstein Ω w) := by
  refine ⟨10680, by norm_num, fun Ω Ωs hJ P hP w hw hs => ?_⟩
  obtain ⟨f, hf, hf0⟩ := s02_riemannMap_at hJ hw
  have hΩ : IsOpen Ω := hf.isOpen isOpen_ball
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hw
  have hA : ‖logDensityDz Ω w‖ ≤ poincareDensity Ω w := by
    have h := (lem_koebe_b hf (Metric.mem_ball_self one_pos)).2
    rwa [hf0] at h
  have hXU : ∀ x ∈ Ω, epstein Ω x ∈ UHS := fun x hx => by
    have h := lem_normal_b ⟨f, hf⟩ hx
    rw [← h.2.2]
    exact h.1 0
  have hQ := hXU w hw
  have hQ2 : (0 : ℝ) < (epstein Ω w).2 := hQ
  have hkc : ContDiffAt ℝ 2 (ambKernel P) (epstein Ω w) :=
    (((lem_ambient_kernel_a P hP).1).contDiffAt (s09_isOpen_UHS.mem_nhds hQ)).of_le (by simp)
  have hXc : ContDiffAt ℝ 2 (epstein Ω) w :=
    ((lem_fff_smooth ⟨f, hf⟩).contDiffAt (hΩ.mem_nhds hw)).of_le (by simp)
  have hκd : DifferentiableAt ℝ (fderiv ℝ (fun x => ambKernel P (epstein Ω x))) w :=
    ((hkc.comp w hXc).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsym : IsSymmSndFDerivAt ℝ (ambKernel P) (epstein Ω w) := hkc.isSymmSndFDerivAt (by simp)
  obtain ⟨hk0, -, -⟩ := (lem_ambient_kernel_a P hP).2 _ hQ
  -- `ξ ≥ 2/(5λ)`
  have hξ : 2 ≤ 5 * poincareDensity Ω w * (epstein Ω w).2 := by
    have e : (epstein Ω w).2 = 2 * poincareDensity Ω w /
        (poincareDensity Ω w ^ 2 + 4 * ‖logDensityDz Ω w‖ ^ 2) := rfl
    have hA2 : ‖logDensityDz Ω w‖ ^ 2 ≤ poincareDensity Ω w ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hA 2
    rw [e, mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith
  -- each entry: `|∇²κ(X₀, Y₀)| ≤ 5340 λ² κ` for `|X₀|, |Y₀| ≤ 1`
  have hent : ∀ X0 Y0 : ℂ, ‖X0‖ ≤ 1 → ‖Y0‖ ≤ 1 →
      |rhoHess Ω (fun x => ambKernel P (epstein Ω x)) w ![X0, Y0]| ≤
        5340 * poincareDensity Ω w ^ 2 * ambKernel P (epstein Ω w) := by
    intro X0 Y0 hX0 hY0
    rw [s05_hess_D2 hκd, s09_au_hs_chain2 hkc hXc, map_add]
    obtain ⟨hgU, hNU⟩ := s09_au_hs_dX ⟨f, hf⟩ hw hQ2 X0
    obtain ⟨hgV, hNV⟩ := s09_au_hs_dX ⟨f, hf⟩ hw hQ2 Y0
    generalize fderiv ℝ (epstein Ω) w X0 = U at hgU hNU ⊢
    generalize fderiv ℝ (epstein Ω) w Y0 = V at hgV hNV ⊢
    have hlX : poincareDensity Ω w * ‖X0‖ ≤ poincareDensity Ω w := mul_le_of_le_one_right hl.le hX0
    have hlY : poincareDensity Ω w * ‖Y0‖ ≤ poincareDensity Ω w := mul_le_of_le_one_right hl.le hY0
    have hlX0 : 0 ≤ poincareDensity Ω w * ‖X0‖ := by positivity
    have hlY0 : 0 ≤ poincareDensity Ω w * ‖Y0‖ := by positivity
    -- `∇²k(U, V)`
    have b1 : |hypHess (ambKernel P) (epstein Ω w) U V| ≤
        25 / 4 * poincareDensity Ω w ^ 2 * ambKernel P (epstein Ω w) := by
      have t1 := s09_au_hs_pol hsym (c := ambKernel P (epstein Ω w))
        (fun V => (lem_ambient_kernel_c P hP _ hQ).2.1 V) U V
      have gU : hypMetric (epstein Ω w) U U ≤ 25 / 4 * poincareDensity Ω w ^ 2 :=
        hgU.trans (by nlinarith)
      have gV : hypMetric (epstein Ω w) V V ≤ 25 / 4 * poincareDensity Ω w ^ 2 :=
        hgV.trans (by nlinarith)
      refine t1.trans ?_
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add gU gV) hk0.le]
    -- `dk(Γ_ℍ(U, V))`
    have hNU' : ‖U.1‖ + |U.2| ≤ 4 * (epstein Ω w).2 * poincareDensity Ω w :=
      hNU.trans (by nlinarith)
    have hNV' : ‖V.1‖ + |V.2| ≤ 4 * (epstein Ω w).2 * poincareDensity Ω w :=
      hNV.trans (by nlinarith)
    have b2 : |fderiv ℝ (ambKernel P) (epstein Ω w) (hypChristoffel (epstein Ω w) U V)| ≤
        48 * poincareDensity Ω w ^ 2 * ambKernel P (epstein Ω w) := by
      have hNG : ‖(hypChristoffel (epstein Ω w) U V).1‖ + |(hypChristoffel (epstein Ω w) U V).2| ≤
          48 * (epstein Ω w).2 * poincareDensity Ω w ^ 2 := by
        refine (s09_au_hs_hypChr (epstein Ω w) U V hQ2).trans ?_
        rw [div_le_iff₀ hQ2]
        have := mul_le_mul hNU' hNV' (by positivity) (by positivity)
        nlinarith
      refine (s09_au_hs_dk hP hQ _).trans ?_
      rw [div_le_iff₀ hQ2]
      nlinarith [mul_le_mul_of_nonneg_left hNG hk0.le]
    -- `dk(D²X(X₀, Y₀))`
    have b3 : |fderiv ℝ (ambKernel P) (epstein Ω w) (fderiv ℝ (fderiv ℝ (epstein Ω)) w X0 Y0)| ≤
        5250 * poincareDensity Ω w ^ 2 * ambKernel P (epstein Ω w) := by
      have hN := s09_au_hs_D2X hf hw hA hs X0 Y0
      have hN' : ‖(fderiv ℝ (fderiv ℝ (epstein Ω)) w X0 Y0).1‖ +
          |(fderiv ℝ (fderiv ℝ (epstein Ω)) w X0 Y0).2| ≤ 2100 * poincareDensity Ω w := by
        refine hN.trans ?_
        have := mul_le_mul hX0 hY0 (norm_nonneg _) zero_le_one
        nlinarith [mul_le_mul_of_nonneg_left this
          (by positivity : (0 : ℝ) ≤ 2100 * poincareDensity Ω w)]
      refine (s09_au_hs_dk hP hQ _).trans ?_
      rw [div_le_iff₀ hQ2]
      nlinarith [mul_le_mul_of_nonneg_left hN' hk0.le, mul_le_mul_of_nonneg_left hξ
        (by positivity : (0 : ℝ) ≤ 1050 * poincareDensity Ω w * ambKernel P (epstein Ω w))]
    -- `dκ(Γ_ρ(X₀, Y₀))`
    have b4 : |fderiv ℝ (fun x => ambKernel P (epstein Ω x)) w (rhoChristoffel Ω w X0 Y0)| ≤
        30 * poincareDensity Ω w ^ 2 * ambKernel P (epstein Ω w) := by
      have t4 := s09_au_grad ⟨f, hf⟩ hP hw (rhoChristoffel Ω w X0 Y0)
      have t4' := s09_au_hs_rhoChr hf hw hA X0 Y0
      have h12 : ‖rhoChristoffel Ω w X0 Y0‖ ≤ 12 * poincareDensity Ω w := by
        refine t4'.trans ?_
        have := mul_le_mul hX0 hY0 (norm_nonneg _) zero_le_one
        nlinarith [mul_le_mul_of_nonneg_left this
          (by positivity : (0 : ℝ) ≤ 12 * poincareDensity Ω w)]
      refine t4.trans ?_
      nlinarith [mul_le_mul_of_nonneg_left h12
        (by positivity : (0 : ℝ) ≤ 5 / 2 * ambKernel P (epstein Ω w) * poincareDensity Ω w)]
    have c1 := abs_le.mp b1
    have c2 := abs_le.mp b2
    have c3 := abs_le.mp b3
    have c4 := abs_le.mp b4
    have hpos : 0 ≤ poincareDensity Ω w ^ 2 * ambKernel P (epstein Ω w) := by positivity
    rw [abs_le]
    constructor <;> linarith
  -- the Hilbert–Schmidt norm
  have hn : ∀ j, ‖frameVec j‖ ≤ 1 := by intro j; fin_cases j <;> simp [frameVec]
  have hc : Fintype.card (Fin (0 + 2) → Fin 2) = 4 := by simp
  rw [rhoTensorNorm, div_le_iff₀ (by positivity)]
  have hsq : ∑ idx : Fin (0 + 2) → Fin 2,
      (rhoHess Ω (fun x => ambKernel P (epstein Ω x)) w fun i => frameVec (idx i)) ^ 2 ≤
        ∑ _idx : Fin (0 + 2) → Fin 2,
          (5340 * poincareDensity Ω w ^ 2 * ambKernel P (epstein Ω w)) ^ 2 := by
    refine Finset.sum_le_sum fun idx _ => ?_
    have e : (fun i => frameVec (idx i)) = ![frameVec (idx 0), frameVec (idx 1)] := by
      ext i; fin_cases i <;> rfl
    rw [e]
    have h := abs_le.mp (hent (frameVec (idx 0)) (frameVec (idx 1)) (hn (idx 0)) (hn (idx 1)))
    exact sq_le_sq' h.1 h.2
  rw [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul] at hsq
  calc √(∑ idx : Fin (0 + 2) → Fin 2,
        (rhoHess Ω (fun x => ambKernel P (epstein Ω x)) w fun i => frameVec (idx i)) ^ 2)
      ≤ √((2 * (5340 * poincareDensity Ω w ^ 2 * ambKernel P (epstein Ω w))) ^ 2) :=
        Real.sqrt_le_sqrt (hsq.trans (le_of_eq (by push_cast; ring)))
    _ = 2 * (5340 * poincareDensity Ω w ^ 2 * ambKernel P (epstein Ω w)) :=
        Real.sqrt_sq (by positivity)
    _ = 10680 * ambKernel P (epstein Ω w) * poincareDensity Ω w ^ (0 + 2) := by ring

/-- Helper (W1b) for `s09_au_adjoint`: a frame entry of a `2`-tensor is bounded by its
pointwise `ρ`-norm, `|T(eᵢ, eⱼ)| ≤ |T|_ρ λ²`. -/
theorem s09_au_ad_entry2 (Ω : Set ℂ) (T : TensorField 2) (w : ℂ) (hl : 0 < poincareDensity Ω w)
    (i j : Fin 2) :
    |T w ![frameVec i, frameVec j]| ≤ rhoTensorNorm Ω T w * poincareDensity Ω w ^ 2 := by
  rw [rhoTensorNorm, div_mul_cancel₀ _ (by positivity), ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  have e : (fun k => frameVec (![i, j] k)) = ![frameVec i, frameVec j] := by
    ext k; fin_cases k <;> rfl
  have h := Finset.single_le_sum
    (f := fun idx : Fin 2 → Fin 2 => (T w fun k => frameVec (idx k)) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ ![i, j])
  simp only [e] at h
  exact h

/-- Helper (W1b) for `s09_au_adjoint`: `|T(eᵢ)| ≤ |T|_ρ λ` for a `1`-tensor. -/
theorem s09_au_ad_entry1 (Ω : Set ℂ) (T : TensorField 1) (w : ℂ) (hl : 0 < poincareDensity Ω w)
    (i : Fin 2) :
    |T w ![frameVec i]| ≤ rhoTensorNorm Ω T w * poincareDensity Ω w := by
  rw [rhoTensorNorm, pow_one, div_mul_cancel₀ _ hl.ne', ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  have e : (fun k => frameVec (![i] k)) = ![frameVec i] := by
    ext k; fin_cases k; rfl
  have h := Finset.single_le_sum
    (f := fun idx : Fin 1 → Fin 2 => (T w fun k => frameVec (idx k)) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ ![i])
  simp only [e] at h
  exact h

/-- Lemma 9.4 `lem:ambient-adjoint` (c) (`sec09-ambient.tex:214`), pointwise form: for an
`ε'`-admissible `𝓛` on `D`, `𝓛*κ ≥ (2 - C₂ (s + ε')) κ` at every `w ∈ D` with `s ≤ 1/4`;
`C₂` is absolute.  (On `G₀`, where `s < ε` and `ε' = C₁ ε`, this is the paper's
`𝓛*κ ≥ (2 - C₂ ε) κ`.)  From `eq_adjoint`, `s09_au_lap`, `s09_au_grad`, `s09_au_hess`. -/
theorem s09_au_adjoint : ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs →
    ∀ (D : Set ℂ) (ε' : ℝ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ)
      (c : ℂ → ℝ), IsAdmissibleOp Ω D ε' aUp bUp c → ∀ P ∈ UHS, ∀ w ∈ D,
        schwarzNorm Ω w ≤ 1 / 4 →
          (2 - C₂ * (schwarzNorm Ω w + ε')) * ambKernel P (epstein Ω w) ≤
            ellOpAdj Ω aUp bUp c (fun x => ambKernel P (epstein Ω x)) w := by
  obtain ⟨Cl, hCl, hlap⟩ := s09_au_lap
  obtain ⟨Ch, hCh, hhess⟩ := s09_au_hess
  refine ⟨Cl + 4 * Ch + 25, by positivity, fun Ω Ωs hJ D ε' aUp bUp c h P hP w hwD hs => ?_⟩
  have hw : w ∈ Ω := h.2.2.2.1 hwD
  have hε : 0 < ε' := h.1
  obtain ⟨f, hf, -⟩ := s02_riemannMap_at hJ hw
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hw
  have hs0 : 0 ≤ schwarzNorm Ω w := (eq_nehari ⟨f, hf⟩ hw).1
  have hQ : epstein Ω w ∈ UHS := by
    have h := lem_normal_b ⟨f, hf⟩ hw
    rw [← h.2.2]
    exact h.1 0
  obtain ⟨hk0, -, -⟩ := (lem_ambient_kernel_a P hP).2 _ hQ
  -- the inputs
  have hL := hlap Ω Ωs hJ P hP w hw hs
  have hH := hhess Ω Ωs hJ P hP w hw hs
  obtain ⟨hc, hb⟩ := (eq_adjoint Ω Ωs hJ D ε' aUp bUp c h).2 w hwD
  have hT : rhoTensorNorm Ω (lowerA Ω aUp - rhoMetricT Ω) w ≤ ε' := by
    have h1 : ENNReal.ofReal
        (rhoTensorNorm Ω (rhoIterCovDeriv Ω 0 (lowerA Ω aUp - rhoMetricT Ω)) w) ≤
        rhoCjNorm Ω 2 (lowerA Ω aUp - rhoMetricT Ω) D :=
      le_iSup_of_le 0 (le_iSup_of_le (Nat.zero_le 2) (le_iSup_of_le w (le_iSup_of_le hwD le_rfl)))
    have h2 := h.2.2.2.2.2
    exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp
      (h1.trans ((le_add_right (le_add_right le_rfl)).trans h2))
  set κ := fun x => ambKernel P (epstein Ω x) with hκ
  set l := poincareDensity Ω w with hldef
  -- frame entries
  have hLA : ∀ i j : Fin 2, (lowerA Ω aUp - rhoMetricT Ω) w ![frameVec i, frameVec j] =
      l ^ 4 * aUp w i j - l ^ 2 * (if i = j then 1 else 0) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [lowerA, rhoMetricT, cvec, frameVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two, l]
  have hLB : ∀ i : Fin 2, lowerB Ω (adjCoeffB Ω aUp bUp) w ![frameVec i] =
      l ^ 2 * adjCoeffB Ω aUp bUp w i := by
    intro i
    fin_cases i <;> simp [lowerB, cvec, frameVec, dotProduct, Fin.sum_univ_two, l]
  -- `|a_{ij} H_{ij} - δ_{ij} H_{ij}/λ²| ≤ C_h ε' κ`
  have key : ∀ i j : Fin 2, ∀ d : ℝ, (if i = j then 1 else 0) = d →
      aUp w i j * rhoHess Ω κ w ![frameVec i, frameVec j] ≤
        d * rhoHess Ω κ w ![frameVec i, frameVec j] / l ^ 2 + Ch * ε' * κ w := by
    intro i j d hd
    have hTij := s09_au_ad_entry2 Ω (lowerA Ω aUp - rhoMetricT Ω) w hl i j
    rw [hLA, hd] at hTij
    have hHij := s09_au_ad_entry2 Ω (rhoHess Ω κ) w hl i j
    set H := rhoHess Ω κ w ![frameVec i, frameVec j]
    have e : aUp w i j * H - d * H / l ^ 2 = (l ^ 4 * aUp w i j - l ^ 2 * d) * H / l ^ 4 := by
      field_simp
    have h1 : |(l ^ 4 * aUp w i j - l ^ 2 * d) * H| ≤ (ε' * l ^ 2) * (Ch * κ w * l ^ 2) := by
      rw [abs_mul]
      exact mul_le_mul (hTij.trans (mul_le_mul_of_nonneg_right hT (by positivity)))
        (hHij.trans (mul_le_mul_of_nonneg_right hH (by positivity))) (abs_nonneg _)
        (by positivity)
    have h2 : aUp w i j * H - d * H / l ^ 2 ≤ Ch * ε' * κ w := by
      rw [e, div_le_iff₀ (by positivity)]
      have := (abs_le.mp h1).2
      nlinarith
    linarith
  -- `|b*_i dκ(eᵢ)| ≤ 10 ε' κ`
  have keyb : ∀ i : Fin 2, adjCoeffB Ω aUp bUp w i * fderiv ℝ κ w (frameVec i) ≤
      10 * ε' * κ w := by
    intro i
    have hBi := s09_au_ad_entry1 Ω (lowerB Ω (adjCoeffB Ω aUp bUp)) w hl i
    rw [hLB] at hBi
    have hn : ‖frameVec i‖ = 1 := by fin_cases i <;> simp [frameVec]
    have hg := s09_au_grad ⟨f, hf⟩ hP hw (frameVec i)
    rw [hn, mul_one] at hg
    have hb' : |adjCoeffB Ω aUp bUp w i| * l ≤ 4 * ε' := by
      have := hBi.trans (mul_le_mul_of_nonneg_right hb hl.le)
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < l ^ 2)] at this
      nlinarith
    have h1 : |adjCoeffB Ω aUp bUp w i * fderiv ℝ κ w (frameVec i)| ≤ 10 * ε' * κ w := by
      rw [abs_mul]
      have := mul_le_mul hb' hg (abs_nonneg _) (by positivity)
      nlinarith [abs_nonneg (adjCoeffB Ω aUp bUp w i)]
    exact (abs_le.mp h1).2
  -- assemble
  have hc' : (2 - 5 * ε') * κ w ≤ adjCoeffC Ω aUp bUp c w * κ w :=
    mul_le_mul_of_nonneg_right (by linarith [(abs_le.mp hc).1]) hk0.le
  have k00 := key 0 0 1 (by simp)
  have k01 := key 0 1 0 (by simp)
  have k10 := key 1 0 0 (by simp)
  have k11 := key 1 1 1 (by simp)
  have b0 := keyb 0
  have b1 := keyb 1
  have hΔ : rhoLaplacian Ω κ w = rhoHess Ω κ w ![frameVec 0, frameVec 0] / l ^ 2 +
      rhoHess Ω κ w ![frameVec 1, frameVec 1] / l ^ 2 := by
    rw [rhoLaplacian, Fin.sum_univ_two, add_div]
  rw [hΔ] at hL
  simp only [ellOpAdj, ellOp, Fin.sum_univ_two]
  simp only [zero_mul, zero_div, one_mul] at k00 k01 k10 k11
  have hκw : κ w = ambKernel P (epstein Ω w) := rfl
  rw [hκw] at k00 k01 k10 k11 b0 b1 hc'
  have hsκ : 0 ≤ schwarzNorm Ω w * ambKernel P (epstein Ω w) := mul_nonneg hs0 hk0.le
  have hεκ : 0 ≤ ε' * ambKernel P (epstein Ω w) := mul_nonneg hε.le hk0.le
  rw [hκw]
  have hmain : adjCoeffC Ω aUp bUp c w * ambKernel P (epstein Ω w) -
      (aUp w 0 0 * rhoHess Ω κ w ![frameVec 0, frameVec 0] +
        aUp w 0 1 * rhoHess Ω κ w ![frameVec 0, frameVec 1] +
        (aUp w 1 0 * rhoHess Ω κ w ![frameVec 1, frameVec 0] +
          aUp w 1 1 * rhoHess Ω κ w ![frameVec 1, frameVec 1])) -
      (adjCoeffB Ω aUp bUp w 0 * fderiv ℝ κ w (frameVec 0) +
        adjCoeffB Ω aUp bUp w 1 * fderiv ℝ κ w (frameVec 1)) ≥
      (2 - 5 * ε') * ambKernel P (epstein Ω w) + ambKernel P (epstein Ω w) ^ 2 -
        Cl * schwarzNorm Ω w * ambKernel P (epstein Ω w) -
        4 * (Ch * ε' * ambKernel P (epstein Ω w)) -
        20 * ε' * ambKernel P (epstein Ω w) := by
    linarith
  refine le_trans ?_ hmain
  nlinarith [mul_nonneg hCl hεκ, mul_nonneg hCh hsκ, sq_nonneg (ambKernel P (epstein Ω w)),
    mul_nonneg hCh hεκ]

/-- Helper for `lem_length` (Stage A, Littlewood–Paley, polynomials): with `b_m = (m+1) a_{m+1}`,
`∫_𝔻 (1-|z|²) |Σ_{m<N} b_m z^m|² = π Σ (m+1)/(m+2) |a_{m+1}|² ≤ π Σ_{n≤N} |a_n|²`. -/
theorem s09_len_lp_poly (a : ℕ → ℂ) (N : ℕ) :
    ∫ z in unitDisc, (1 - ‖z‖ ^ 2) *
        ‖∑ m ∈ Finset.range N, ((m + 1 : ℕ) : ℂ) * a (m + 1) * z ^ m‖ ^ 2 ≤
      π * ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2 := by
  have h := s02_vd_disc_parseval (fun t => 1 - t ^ 2) (by fun_prop)
    (fun m => ((m + 1 : ℕ) : ℂ) * a (m + 1)) N
  refine h.trans_le ?_
  show 2 * π * ∑ m ∈ Finset.range N, ‖((m + 1 : ℕ) : ℂ) * a (m + 1)‖ ^ 2 *
      ∫ r in (0 : ℝ)..1, r * (1 - r ^ 2) * r ^ (2 * m) ≤ _
  simp only [s02_vd_radial1]
  have hterm : ∀ m : ℕ, ‖((m + 1 : ℕ) : ℂ) * a (m + 1)‖ ^ 2 *
      (1 / (2 * ((m : ℝ) + 1) * ((m : ℝ) + 2))) ≤ ‖a (m + 1)‖ ^ 2 / 2 := by
    intro m
    rw [norm_mul, Complex.norm_natCast, mul_pow]
    have hk : ((m + 1 : ℕ) : ℝ) ^ 2 * (1 / (2 * ((m : ℝ) + 1) * ((m : ℝ) + 2))) ≤ 1 / 2 := by
      push_cast
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith [sq_nonneg ‖a (m + 1)‖]
  rw [Finset.sum_range_succ']
  have hs := Finset.sum_le_sum fun m (_ : m ∈ Finset.range N) => hterm m
  rw [← Finset.sum_div] at hs
  nlinarith [Real.pi_pos, sq_nonneg ‖a 0‖]

/-- Helper for `lem_length` (Stage A, Parseval on the unit circle, polynomials):
`∫₀^{2π} |Σ_{n<K} a_n e^{int}|² dt = 2π Σ_{n<K} |a_n|²` (`s12_circle_parseval`). -/
theorem s09_len_lp_cpoly (a : ℕ → ℂ) (K : ℕ) :
    ∫ t in Ioc 0 (2 * π), ‖∑ n ∈ Finset.range K, a n * circleMap 0 1 t ^ n‖ ^ 2 =
      2 * π * ∑ n ∈ Finset.range K, ‖a n‖ ^ 2 := by
  have h := s12_circle_parseval (Finset.range K) id (injOn_id _) a zero_le_one
  rw [Real.circleAverage_def, smul_eq_mul] at h
  simp only [id_eq, one_pow, mul_one] at h
  rw [← intervalIntegral.integral_of_le (by positivity), ← h, ← mul_assoc,
    mul_inv_cancel₀ (by positivity), one_mul]

/-- Helper for `lem_length` (Stage A): uniform convergence on `D̄` passes to the limit in
`∫₀^{2π} |P_N(e^{it})|² dt` (dominated convergence). -/
theorem s09_len_lp_circ {P : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hP : ∀ N, Continuous (P N))
    (hf : ContinuousOn f (closedBall 0 1)) (hU : TendstoUniformlyOn P f atTop (closedBall 0 1)) :
    Tendsto (fun N => ∫ t in Ioc 0 (2 * π), ‖P N (circleMap 0 1 t)‖ ^ 2) atTop
      (𝓝 (∫ t in Ioc 0 (2 * π), ‖f (circleMap 0 1 t)‖ ^ 2)) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hf
  have hmem : ∀ t, circleMap 0 1 t ∈ closedBall (0 : ℂ) 1 := fun t => by
    rw [mem_closedBall_zero_iff, norm_circleMap_zero, abs_one]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (M + 1) ^ 2) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun N =>
      (((hP N).comp (continuous_circleMap 0 1)).norm.pow 2).aestronglyMeasurable
  · filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hU) 1 one_pos] with N hN
    refine Eventually.of_forall fun t => ?_
    have h1 : ‖P N (circleMap 0 1 t)‖ ≤ M + 1 := by
      have := hN _ (hmem t)
      rw [dist_eq_norm] at this
      linarith [norm_sub_norm_le (P N (circleMap 0 1 t)) (f (circleMap 0 1 t)), hM _ (hmem t),
        norm_sub_rev (f (circleMap 0 1 t)) (P N (circleMap 0 1 t))]
    rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  · exact continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · exact Eventually.of_forall fun t => (hU.tendsto_at (hmem t)).norm.pow 2

/-- Helper for `lem_length` (Stage A, Littlewood–Paley for dilations): for `0 < r < 1`,
`∫_𝔻 (1-|z|²) |(F_r)'(z)|² ≤ ½ ∫₀^{2π} |F(r e^{it})|² dt` (`s09_len_lp_poly`,
`s09_len_lp_cpoly` for the dilated Taylor polynomials, limits by `s02_vd_lim`, `s09_len_lp_circ`). -/
theorem s09_len_lp_dil {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F unitDisc) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) :
    ∫ z in unitDisc, (1 - ‖z‖ ^ 2) * ‖(r : ℂ) * deriv F ((r : ℂ) * z)‖ ^ 2 ≤
      (∫ t in Ioc 0 (2 * π), ‖F (circleMap 0 r t)‖ ^ 2) / 2 := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, c = fun n => ((n.factorial : ℂ))⁻¹ * iteratedDeriv n F 0 :=
    ⟨_, rfl⟩
  have hs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (F z) := by
    intro z hz
    have h := hasSum_taylorSeries_on_ball hF hz
    simp only [sub_zero, smul_eq_mul] at h
    convert h using 2 with n
    simp only [hc]
    ring
  have hs' : ∀ z ∈ unitDisc,
      HasSum (fun n => c (n + 1) * ((n + 1 : ℕ) : ℂ) * z ^ n) (deriv F z) :=
    fun z hz => TakhtajanTeo.Ch2.faber_powerSeries_deriv hs hz
  have hU1 := TakhtajanTeo.Ch2.bergmanTaylorPoly_dilate_uniform hs hr0 hr1
  have hU2 := TakhtajanTeo.Ch2.bergmanTaylorPoly_dilate_uniform
    (f := deriv F) (c := fun n => c (n + 1) * ((n + 1 : ℕ) : ℂ)) hs' hr0 hr1
  simp only [TakhtajanTeo.Ch2.bergmanTaylorPoly_eval] at hU1 hU2
  have hmaps : MapsTo (fun z : ℂ => (r : ℂ) * z) (closedBall 0 1) unitDisc := by
    intro z hz
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    exact (mul_le_of_le_one_right hr0.le (mem_closedBall_zero_iff.mp hz)).trans_lt hr1
  have hc1 : ContinuousOn (fun z => F ((r : ℂ) * z)) (closedBall 0 1) :=
    hF.continuousOn.comp (by fun_prop) hmaps
  have hc2 : ContinuousOn (fun z => deriv F ((r : ℂ) * z)) (closedBall 0 1) :=
    (hF.deriv isOpen_ball).continuousOn.comp (by fun_prop) hmaps
  have hC := (s09_len_lp_circ (fun N => continuous_finsetSum _ fun n _ => by fun_prop) hc1
    hU1).comp (tendsto_add_atTop_nat 1)
  have hL2 := s02_vd_lim (fun t => 1 - t ^ 2) (by fun_prop)
    (fun N => continuous_finsetSum _ fun n _ => by fun_prop) hc2 hU2
  have hQ : ∀ (N : ℕ) (z : ℂ), ‖∑ m ∈ Finset.range N,
      ((m + 1 : ℕ) : ℂ) * (c (m + 1) * (r : ℂ) ^ (m + 1)) * z ^ m‖ ^ 2 =
      r ^ 2 * ‖∑ m ∈ Finset.range N, c (m + 1) * ((m + 1 : ℕ) : ℂ) * (r : ℂ) ^ m * z ^ m‖ ^ 2 := by
    intro N z
    rw [show (∑ m ∈ Finset.range N, ((m + 1 : ℕ) : ℂ) * (c (m + 1) * (r : ℂ) ^ (m + 1)) * z ^ m) =
        (r : ℂ) * ∑ m ∈ Finset.range N, c (m + 1) * ((m + 1 : ℕ) : ℂ) * (r : ℂ) ^ m * z ^ m by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le, mul_pow]
  have hpN : ∀ N : ℕ, r ^ 2 * ∫ z in unitDisc, (1 - ‖z‖ ^ 2) *
      ‖∑ m ∈ Finset.range N, c (m + 1) * ((m + 1 : ℕ) : ℂ) * (r : ℂ) ^ m * z ^ m‖ ^ 2 ≤
      (∫ t in Ioc 0 (2 * π), ‖∑ n ∈ Finset.range (N + 1),
        c n * (r : ℂ) ^ n * circleMap 0 1 t ^ n‖ ^ 2) / 2 := by
    intro N
    have h := s09_len_lp_poly (fun n => c n * (r : ℂ) ^ n) N
    have e : ∫ z in unitDisc, (1 - ‖z‖ ^ 2) * ‖∑ m ∈ Finset.range N,
        ((m + 1 : ℕ) : ℂ) * (c (m + 1) * (r : ℂ) ^ (m + 1)) * z ^ m‖ ^ 2 =
        r ^ 2 * ∫ z in unitDisc, (1 - ‖z‖ ^ 2) *
          ‖∑ m ∈ Finset.range N, c (m + 1) * ((m + 1 : ℕ) : ℂ) * (r : ℂ) ^ m * z ^ m‖ ^ 2 := by
      rw [← integral_const_mul]
      congr 1
      funext z
      rw [hQ]
      ring
    rw [e] at h
    rw [s09_len_lp_cpoly (fun n => c n * (r : ℂ) ^ n) (N + 1)]
    linarith
  have hR : ∫ z in unitDisc, (1 - ‖z‖ ^ 2) * ‖(r : ℂ) * deriv F ((r : ℂ) * z)‖ ^ 2 =
      r ^ 2 * ∫ z in unitDisc, (1 - ‖z‖ ^ 2) * ‖deriv F ((r : ℂ) * z)‖ ^ 2 := by
    rw [← integral_const_mul]
    congr 1
    funext z
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    ring
  have hcm : ∀ t, (r : ℂ) * circleMap 0 1 t = circleMap 0 r t := fun t => by
    simp [circleMap]
  rw [hR, show (∫ t in Ioc 0 (2 * π), ‖F (circleMap 0 r t)‖ ^ 2) =
      ∫ t in Ioc 0 (2 * π), ‖F ((r : ℂ) * circleMap 0 1 t)‖ ^ 2 by simp only [hcm]]
  exact le_of_tendsto_of_tendsto' (hL2.const_mul (r ^ 2)) (hC.div_const 2) hpN

/-- Helper for `lem_length` (Stage A, S1, upper Littlewood–Paley): for `F` holomorphic on `𝔻`,
`∫_𝔻 |F'|² (1-|z|²) dA ≤ sup_s ∫₀^{2π} |F(s e^{it})|² dt` (in coefficients
`π Σ n/(n+1) |a_n|² ≤ 2π Σ |a_n|²`; area Parseval `s02_vd_disc_parseval`, circle Bessel). -/
theorem s09_len_lp_upper {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F unitDisc) :
    ∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv F z‖ ^ 2 * (1 - ‖z‖ ^ 2)) ≤
      ⨆ s ∈ Ioo (0 : ℝ) 1,
        ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (‖F (circleMap 0 s t)‖ ^ 2) := by
  obtain ⟨rs, hrs⟩ : ∃ rs : ℕ → ℝ, rs = fun k : ℕ => 1 - 1 / 2 * (1 / ((k : ℝ) + 1)) := ⟨_, rfl⟩
  have hk1 : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ 1 := fun k => by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hr0 : ∀ k, 0 < rs k := fun k => by
    rw [hrs]
    linarith [hk1 k]
  have hr1 : ∀ k, rs k < 1 := fun k => by
    rw [hrs]
    have : 0 < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  have hlim : Tendsto rs atTop (𝓝 1) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 2 : ℝ)).const_sub (1 : ℝ)
    rw [mul_zero, sub_zero] at this
    rw [hrs]
    exact this
  have hsub : unitDisc ⊆ closedBall (0 : ℂ) 1 := ball_subset_closedBall
  have hw : ∀ z ∈ unitDisc, 0 ≤ 1 - ‖z‖ ^ 2 := fun z hz => by
    have := mem_ball_zero_iff.mp hz
    nlinarith [norm_nonneg z]
  have hmaps : ∀ k, MapsTo (fun z : ℂ => (rs k : ℂ) * z) (closedBall 0 1) unitDisc := by
    intro k z hz
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hr0 k).le]
    exact (mul_le_of_le_one_right (hr0 k).le (mem_closedBall_zero_iff.mp hz)).trans_lt (hr1 k)
  have hc1 : ∀ k, ContinuousOn (fun z => (1 - ‖z‖ ^ 2) * ‖(rs k : ℂ) * deriv F ((rs k : ℂ) * z)‖ ^ 2)
      (closedBall 0 1) := fun k =>
    (by fun_prop : Continuous fun z : ℂ => 1 - ‖z‖ ^ 2).continuousOn.mul
      ((continuousOn_const.mul
        ((hF.deriv isOpen_ball).continuousOn.comp (by fun_prop) (hmaps k))).norm.pow 2)
  have hcirc : ∀ k, Continuous fun t => ‖F (circleMap 0 (rs k) t)‖ ^ 2 := fun k =>
    ((hF.continuousOn.comp_continuous (continuous_circleMap 0 (rs k)) fun t => by
      show _ ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos (hr0 k)]
      exact hr1 k).norm.pow 2)
  -- the dilated bound
  have hk : ∀ k, ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) *
      ‖(rs k : ℂ) * deriv F ((rs k : ℂ) * z)‖ ^ 2) ≤
      ⨆ s ∈ Ioo (0 : ℝ) 1, ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (‖F (circleMap 0 s t)‖ ^ 2) := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((hc1 k).integrableOn_compact (isCompact_closedBall 0 1) |>.mono_set hsub)
      ((ae_restrict_iff' (measurableSet_ball : MeasurableSet unitDisc)).mpr
        (ae_of_all _ fun z hz => mul_nonneg (hw z hz) (sq_nonneg _)))]
    refine (ENNReal.ofReal_le_ofReal ((s09_len_lp_dil hF (hr0 k) (hr1 k)).trans
      (half_le_self (integral_nonneg fun t => sq_nonneg _)))).trans ?_
    rw [ofReal_integral_eq_lintegral_ofReal
      ((hcirc k).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (Eventually.of_forall fun t => sq_nonneg _)]
    exact le_iSup₂ (f := fun s (_ : s ∈ Ioo (0 : ℝ) 1) =>
      ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (‖F (circleMap 0 s t)‖ ^ 2)) (rs k) ⟨hr0 k, hr1 k⟩
  -- pointwise convergence and Fatou
  have hpt : ∀ z ∈ unitDisc, Tendsto (fun k => ENNReal.ofReal ((1 - ‖z‖ ^ 2) *
      ‖(rs k : ℂ) * deriv F ((rs k : ℂ) * z)‖ ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (‖deriv F z‖ ^ 2 * (1 - ‖z‖ ^ 2)))) := by
    intro z hz
    have h1 : Tendsto (fun k => (rs k : ℂ) * z) atTop (𝓝 z) := by
      have := ((Complex.continuous_ofReal.tendsto 1).comp hlim).mul_const z
      simpa using this
    have hFz : ContinuousAt (deriv F) z :=
      (hF.deriv isOpen_ball).continuousOn.continuousAt (isOpen_ball.mem_nhds hz)
    have h2 : Tendsto (fun k => (rs k : ℂ) * deriv F ((rs k : ℂ) * z)) atTop (𝓝 (deriv F z)) := by
      have := ((Complex.continuous_ofReal.tendsto 1).comp hlim).mul (hFz.tendsto.comp h1)
      simpa using this
    rw [mul_comm (‖deriv F z‖ ^ 2)]
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((h2.norm.pow 2).const_mul _)
  have hmeas : ∀ k, AEMeasurable (fun z => ENNReal.ofReal ((1 - ‖z‖ ^ 2) *
      ‖(rs k : ℂ) * deriv F ((rs k : ℂ) * z)‖ ^ 2)) (volume.restrict unitDisc) := fun k =>
    (ENNReal.continuous_ofReal.comp_continuousOn ((hc1 k).mono hsub)).aemeasurable
      (measurableSet_ball : MeasurableSet unitDisc)
  calc ∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv F z‖ ^ 2 * (1 - ‖z‖ ^ 2))
      = ∫⁻ z in unitDisc, liminf (fun k => ENNReal.ofReal ((1 - ‖z‖ ^ 2) *
          ‖(rs k : ℂ) * deriv F ((rs k : ℂ) * z)‖ ^ 2)) atTop := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet unitDisc)] with z hz
        exact (hpt z hz).liminf_eq.symm
    _ ≤ liminf (fun k => ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) *
          ‖(rs k : ℂ) * deriv F ((rs k : ℂ) * z)‖ ^ 2)) atTop := lintegral_liminf_le' hmeas
    _ ≤ _ := liminf_le_of_frequently_le' (Frequently.of_forall hk)

/-- Helper for `lem_length` (Stage A, S2, [GM X (6.1)]): for `F² = f'` on `𝔻` and `g = log f'`,
`|F|² = |f'|`, `|F'|² = |f'| |g'|²/4` and `F'' = F (Sf + g'²)/2`, so
`|F''|² ≤ |f'| (|Sf|² + |g'|⁴)/2`. -/
theorem s09_len_pointwise {f F : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (hF : DifferentiableOn ℂ F unitDisc) (hFf : ∀ z ∈ unitDisc, F z ^ 2 = deriv f z) {z : ℂ}
    (hz : z ∈ unitDisc) :
    ‖F z‖ ^ 2 = ‖deriv f z‖ ∧
      ‖deriv F z‖ ^ 2 = ‖deriv f z‖ * ‖deriv (deriv f) z / deriv f z‖ ^ 2 / 4 ∧
      ‖deriv (deriv F) z‖ ^ 2 ≤
        ‖deriv f z‖ * (‖schwarzian f z‖ ^ 2 + ‖deriv (deriv f) z / deriv f z‖ ^ 4) / 2 := by
  have hU : IsOpen unitDisc := isOpen_ball
  have hf1 : DifferentiableOn ℂ (deriv f) unitDisc := hf.1.deriv hU
  have hf2 : DifferentiableOn ℂ (deriv (deriv f)) unitDisc := hf1.deriv hU
  have hF1 : DifferentiableOn ℂ (deriv F) unitDisc := hF.deriv hU
  have hne : deriv f z ≠ 0 := deriv_ne_zero_of_injOn hU hf.1 hf.2.1 hz
  -- `f'' = 2 F F'` on `𝔻`
  have hd2 : ∀ w ∈ unitDisc, deriv (deriv f) w = 2 * F w * deriv F w := by
    intro w hw
    have he : (fun v => F v ^ 2) =ᶠ[𝓝 w] deriv f :=
      Filter.eventually_of_mem (hU.mem_nhds hw) hFf
    have hd : HasDerivAt (fun v => F v ^ 2) _ w :=
      (hF.differentiableAt (hU.mem_nhds hw)).hasDerivAt.pow 2
    rw [← he.deriv_eq, hd.deriv]
    push_cast
    ring
  -- `f''' = 2 F'² + 2 F F''` at `z`
  have hd3 : deriv (deriv (deriv f)) z = 2 * deriv F z * deriv F z + 2 * F z * deriv (deriv F) z := by
    have he : deriv (deriv f) =ᶠ[𝓝 z] fun w => 2 * F w * deriv F w :=
      Filter.eventually_of_mem (hU.mem_nhds hz) hd2
    have hd : HasDerivAt (fun w => 2 * F w * deriv F w) _ z :=
      ((hF.differentiableAt (hU.mem_nhds hz)).hasDerivAt.const_mul 2).mul
        (hF1.differentiableAt (hU.mem_nhds hz)).hasDerivAt
    rw [he.deriv_eq, hd.deriv]
  -- the Schwarzian
  have hS : schwarzian f z = (deriv (deriv (deriv f)) z * deriv f z -
      deriv (deriv f) z * deriv (deriv f) z) / deriv f z ^ 2 -
        1 / 2 * (deriv (deriv f) z / deriv f z) ^ 2 := by
    rw [schwarzian_of_analyticAt (hf.1.analyticAt (hU.mem_nhds hz))]
    show deriv (fun w => deriv (deriv f) w / deriv f w) z -
      (1 / 2) * (deriv (deriv f) z / deriv f z) ^ 2 = _
    have hd : HasDerivAt (fun w => deriv (deriv f) w / deriv f w) _ z :=
      ((hf2.differentiableAt (hU.mem_nhds hz)).hasDerivAt).div
        ((hf1.differentiableAt (hU.mem_nhds hz)).hasDerivAt) hne
    rw [hd.deriv]
  have h1 := hFf z hz
  have h2 := hd2 z hz
  have hA : F z ≠ 0 := fun h => hne (by rw [← h1, h, zero_pow two_ne_zero])
  -- `F'' = F (Sf + g'²)/2` and `F'² = f' g'²/4`
  have keyC : deriv (deriv F) z = F z * (schwarzian f z + (deriv (deriv f) z / deriv f z) ^ 2) / 2 := by
    rw [hS, hd3, h2, ← h1]
    field_simp
    ring
  have keyB : deriv F z ^ 2 = deriv f z * (deriv (deriv f) z / deriv f z) ^ 2 / 4 := by
    rw [h2, ← h1]
    field_simp
    ring
  refine ⟨by rw [← h1, norm_pow], ?_, ?_⟩
  · rw [← norm_pow, keyB, norm_div, norm_mul, norm_pow]
    norm_num
  · have hC : ‖deriv (deriv F) z‖ ≤
        ‖F z‖ * (‖schwarzian f z‖ + ‖deriv (deriv f) z / deriv f z‖ ^ 2) / 2 := by
      rw [keyC, norm_div, norm_mul]
      have h3 : ‖schwarzian f z + (deriv (deriv f) z / deriv f z) ^ 2‖ ≤
          ‖schwarzian f z‖ + ‖deriv (deriv f) z / deriv f z‖ ^ 2 :=
        (norm_add_le _ _).trans_eq (by rw [norm_pow])
      have h4 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h4]
      gcongr
    have hfA : ‖deriv f z‖ = ‖F z‖ ^ 2 := by rw [← h1, norm_pow]
    rw [hfA]
    have hC2 := pow_le_pow_left₀ (norm_nonneg _) hC 2
    nlinarith [mul_nonneg (sq_nonneg ‖F z‖)
      (sq_nonneg (‖schwarzian f z‖ - ‖deriv (deriv f) z / deriv f z‖ ^ 2))]

/-- Helper for `lem_length` (Stage A, L3, Koebe distortion): for a conformal `f` on `𝔻`,
`|f'(z)| (1-|z|)³ ≤ 2 |f'(0)|` (integrate `lem_koebe_b` along the radius). -/
theorem s09_len_distort {f : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω) {z : ℂ}
    (hz : z ∈ unitDisc) :
    ‖deriv f z‖ * (1 - ‖z‖) ^ 3 ≤ 2 * ‖deriv f 0‖ := by
  have hU : IsOpen unitDisc := isOpen_ball
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hd : DifferentiableOn ℂ f (ball (0 : ℂ) 1) := hf.1
  have hi : InjOn f (ball (0 : ℂ) 1) := hf.2.1
  have ha : deriv f 0 ≠ 0 := deriv_ne_zero_of_injOn hU hf.1 hf.2.1 h0
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  -- the normalization `g = f / f'(0)`
  have hdg : ∀ w, deriv (fun w => f w / deriv f 0) w = deriv f w / deriv f 0 :=
    fun w => deriv_div_const _
  have hgd : DifferentiableOn ℂ (fun w => f w / deriv f 0) (ball (0 : ℂ) 1) :=
    hd.div_const _
  have hgi : InjOn (fun w => f w / deriv f 0) (ball (0 : ℂ) 1) := fun x hx y hy hxy =>
    hi hx hy (by simpa [div_left_inj' ha] using hxy)
  have hg1 : deriv (fun w => f w / deriv f 0) 0 = 1 := by rw [hdg, div_self ha]
  have hgne : ∀ w ∈ ball (0 : ℂ) 1, deriv (fun w => f w / deriv f 0) w ≠ 0 := fun w hw => by
    rw [hdg]
    exact div_ne_zero (deriv_ne_zero_of_injOn hU hf.1 hf.2.1 hw) ha
  have hb := kb_d2_deriv_bound hgd hg1 hgne (fun w hw => kb_koebe_transform_ineq hgd hgi hw) hz1
    (s := 1) ⟨zero_le_one, le_rfl⟩
  rw [Complex.ofReal_one, one_mul, one_mul, hdg, norm_div] at hb
  have hpos : 0 < ‖deriv f 0‖ := norm_pos_iff.mpr ha
  have hr : 0 < 1 - ‖z‖ := by linarith
  rw [div_le_div_iff₀ hpos (by positivity)] at hb
  nlinarith [norm_nonneg z, norm_nonneg (deriv f z), pow_pos hr 3]

/-- Helper for `lem_length` (Stage A, case (ii)): `Sf` is holomorphic on `𝔻` for conformal `f`. -/
theorem s09_len_c2_sd {f : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω) :
    DifferentiableOn ℂ (schwarzian f) unitDisc := by
  intro z hz
  have hn : unitDisc ∈ 𝓝 z := isOpen_ball.mem_nhds hz
  have he : schwarzian f =ᶠ[𝓝 z] schwarzianHol f :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) fun w hw =>
      schwarzian_of_analyticAt (hf.1.analyticAt (isOpen_ball.mem_nhds hw))
  exact ((analyticAt_schwarzianHol (hf.1.analyticAt hn)
    (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz)).differentiableAt.congr_of_eventuallyEq
      he).differentiableWithinAt

/-- Helper for `lem_length` (Stage A, case (ii)): Kraus–Nehari `|Sf(z)| (1 - |z|²)² ≤ 6`
(`eq_nehari`, `eq_s_disk`). -/
theorem s09_len_c2_kraus {f : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω) {z : ℂ}
    (hz : z ∈ unitDisc) : ‖schwarzian f z‖ * (1 - ‖z‖ ^ 2) ^ 2 ≤ 6 := by
  have hN := (eq_nehari ⟨f, hf⟩ (hf.2.2 ▸ mem_image_of_mem f hz)).2
  rw [eq_s_disk hf hz] at hN
  linarith

/-- Helper for `lem_length` (Stage A, case (ii)): for `|ζ - u| ≤ t (1 - |u|)`,
`(1 - t)(1 - |u|) ≤ 1 - |ζ| ≤ (1 + t)(1 - |u|)`. -/
theorem s09_len_c2_geo {u ζ : ℂ} {t : ℝ} (h : ‖ζ - u‖ ≤ t * (1 - ‖u‖)) :
    (1 - t) * (1 - ‖u‖) ≤ 1 - ‖ζ‖ ∧ 1 - ‖ζ‖ ≤ (1 + t) * (1 - ‖u‖) := by
  have h1 := norm_le_norm_add_norm_sub' ζ u
  have h2 := norm_sub_norm_le u ζ
  rw [norm_sub_rev] at h2
  constructor <;> nlinarith

/-- Helper for `lem_length` (Stage A, case (ii)): the arithmetic of `s09_len_c2_lip`. -/
theorem s09_len_c2_arith {a b sz sw D A k : ℝ} (hA : 0 < A) (hk : 0 < k) (hk1 : k ≤ 1)
    (ha0 : 0 ≤ a) (hD : 0 ≤ D) (hsz : 0 ≤ sz) (hsw : sw ≤ sz + 384 / (k * A) ^ 3 * D)
    (ha : a ≤ 16 * A ^ 2) (hab : a - b ≤ 16 * A * D) (hszb : sz ≤ 6 / (k * A) ^ 2) :
    a * sw ≤ b * sz + 6240 * D / (k ^ 3 * A) := by
  have e1 : 16 * A ^ 2 * (384 / (k * A) ^ 3 * D) = 6144 * D / (k ^ 3 * A) := by
    field_simp
    ring
  have e2 : 16 * A * D * (6 / (k * A) ^ 2) = 96 * D / (k ^ 2 * A) := by
    field_simp
    ring
  have e3 : 96 * D / (k ^ 2 * A) ≤ 96 * D / (k ^ 3 * A) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : k ^ 3 ≤ k ^ 2 := pow_le_pow_of_le_one hk.le hk1 (by norm_num)
    exact mul_le_mul_of_nonneg_right this hA.le
  have e4 : 6240 * D / (k ^ 3 * A) = 6144 * D / (k ^ 3 * A) + 96 * D / (k ^ 3 * A) := by ring
  have hB0 : 0 ≤ 384 / (k * A) ^ 3 * D := by positivity
  have t1 : a * sw ≤ a * sz + 16 * A ^ 2 * (384 / (k * A) ^ 3 * D) := by
    nlinarith [mul_le_mul_of_nonneg_left hsw ha0, mul_le_mul_of_nonneg_right ha hB0]
  have hC0 : (0 : ℝ) ≤ 16 * A * D := by positivity
  have t2 : a * sz ≤ b * sz + 16 * A * D * (6 / (k * A) ^ 2) := by
    rcases le_or_gt 0 (a - b) with h | h
    · nlinarith [mul_le_mul hab hszb hsz hC0]
    · nlinarith [(by positivity : (0 : ℝ) ≤ 16 * A * D * (6 / (k * A) ^ 2))]
  rw [e4]
  linarith

/-- Helper for `lem_length` (Stage A, case (ii), Lipschitz bound): for `0 ≤ κ < 1` and
`z, w ∈ B(u, κ(1-|u|))`, `(1-|w|²)²|Sf(w)| ≤ (1-|z|²)²|Sf(z)| + 6240 |z - w|/((1-κ)³(1-|u|))`
(`s09_cauchy_disk` with Kraus–Nehari, then the mean value theorem on the ball). -/
theorem s09_len_c2_lip {f : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω) {u : ℂ}
    (hu : u ∈ unitDisc) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) {z w : ℂ}
    (hz : ‖z - u‖ < κ * (1 - ‖u‖)) (hw : ‖w - u‖ < κ * (1 - ‖u‖)) :
    (1 - ‖w‖ ^ 2) ^ 2 * ‖schwarzian f w‖ ≤
      (1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzian f z‖ + 6240 * ‖z - w‖ / ((1 - κ) ^ 3 * (1 - ‖u‖)) := by
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  have hd0 : 0 < 1 - ‖u‖ := by linarith
  have hk : 0 < 1 - κ := by linarith
  -- on the ball, `(1-κ)(1-|u|) ≤ 1 - |ζ|²` and `ζ ∈ 𝔻`
  have hlow : ∀ ζ, ‖ζ - u‖ < κ * (1 - ‖u‖) →
      (1 - κ) * (1 - ‖u‖) ≤ 1 - ‖ζ‖ ^ 2 ∧ ζ ∈ unitDisc := fun ζ hζ => by
    have := (s09_len_c2_geo hζ.le).1
    have hζ1 : ‖ζ‖ < 1 := by nlinarith
    exact ⟨by nlinarith [norm_nonneg ζ], mem_ball_zero_iff.mpr hζ1⟩
  have hSd := s09_len_c2_sd hf
  have hcd := s09_cauchy_disk hSd (M := 6) fun ξ hξ => by
    rw [mul_comm]; exact s09_len_c2_kraus hf hξ
  have hder : ∀ ξ ∈ ball u (κ * (1 - ‖u‖)),
      ‖deriv (schwarzian f) ξ‖ ≤ 384 / ((1 - κ) * (1 - ‖u‖)) ^ 3 := by
    intro ξ hξ
    obtain ⟨hl, hξD⟩ := hlow ξ (mem_ball_iff_norm.mp hξ)
    have h1 := hcd ξ hξD
    have h2 : ((1 - κ) * (1 - ‖u‖)) ^ 3 ≤ (1 - ‖ξ‖ ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) hl 3
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h2 (norm_nonneg (deriv (schwarzian f) ξ))]
  have hmvt := (convex_ball u (κ * (1 - ‖u‖))).norm_image_sub_le_of_norm_deriv_le
    (fun ζ hζ => hSd.differentiableAt
      (isOpen_ball.mem_nhds (hlow ζ (mem_ball_iff_norm.mp hζ)).2))
    hder (mem_ball_iff_norm.mpr hz) (mem_ball_iff_norm.mpr hw)
  have hsw : ‖schwarzian f w‖ ≤ ‖schwarzian f z‖ +
      384 / ((1 - κ) * (1 - ‖u‖)) ^ 3 * ‖z - w‖ := by
    rw [norm_sub_rev w z] at hmvt
    linarith [norm_sub_norm_le (schwarzian f w) (schwarzian f z)]
  obtain ⟨hlz, hzD⟩ := hlow z hz
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hzD
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp (hlow w hw).2
  have gz := (s09_len_c2_geo hz.le).2
  have gw := (s09_len_c2_geo hw.le).2
  have ha : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hb : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have haw : 1 - ‖w‖ ^ 2 ≤ 4 * (1 - ‖u‖) := by nlinarith [norm_nonneg w]
  have hbz : 1 - ‖z‖ ^ 2 ≤ 4 * (1 - ‖u‖) := by nlinarith [norm_nonneg z]
  have hzw : |‖z‖ - ‖w‖| ≤ ‖z - w‖ := abs_norm_sub_norm_le z w
  have hdiff : (1 - ‖w‖ ^ 2) ^ 2 - (1 - ‖z‖ ^ 2) ^ 2 ≤ 16 * (1 - ‖u‖) * ‖z - w‖ := by
    have e : (1 - ‖w‖ ^ 2) ^ 2 - (1 - ‖z‖ ^ 2) ^ 2 =
        ((1 - ‖w‖ ^ 2) + (1 - ‖z‖ ^ 2)) * ((‖z‖ - ‖w‖) * (‖z‖ + ‖w‖)) := by ring
    rw [e]
    have h1 : (‖z‖ - ‖w‖) * (‖z‖ + ‖w‖) ≤ 2 * ‖z - w‖ := by
      have := abs_le.mp hzw
      nlinarith [norm_nonneg z, norm_nonneg w, norm_nonneg (z - w)]
    have h2 : 0 ≤ (1 - ‖w‖ ^ 2) + (1 - ‖z‖ ^ 2) := by linarith
    calc ((1 - ‖w‖ ^ 2) + (1 - ‖z‖ ^ 2)) * ((‖z‖ - ‖w‖) * (‖z‖ + ‖w‖))
        ≤ ((1 - ‖w‖ ^ 2) + (1 - ‖z‖ ^ 2)) * (2 * ‖z - w‖) := mul_le_mul_of_nonneg_left h1 h2
      _ ≤ (8 * (1 - ‖u‖)) * (2 * ‖z - w‖) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 16 * (1 - ‖u‖) * ‖z - w‖ := by ring
  have hw16 : (1 - ‖w‖ ^ 2) ^ 2 ≤ 16 * (1 - ‖u‖) ^ 2 := by nlinarith
  have hszb : ‖schwarzian f z‖ ≤ 6 / ((1 - κ) * (1 - ‖u‖)) ^ 2 := by
    have hK := s09_len_c2_kraus hf hzD
    have := pow_le_pow_left₀ (by positivity) hlz 2
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left this (norm_nonneg (schwarzian f z))]
  exact s09_len_c2_arith hd0 hk (by linarith) (sq_nonneg _) (norm_nonneg _) (norm_nonneg _) hsw
    hw16 hdiff hszb

/-- Helper for `lem_length` (Stage A, case (ii), pseudo-hyperbolic discs): for `u, w ∈ 𝔻` with
`|w - u| < b |1 - ū w|` (`0 < b < 1`) and `m = (1+b)/(1-b)`, `1 ≤ m` and
`|w - u| ≤ (m-1)(1-|u|)`, `|w - u| ≤ (m-1)(1-|w|)` (from `|1 - ū w| ≤ (1-|u|²) + |w - u|` and
`|1 - ū w| ≤ (1-|w|²) + |w - u|`). -/
theorem s09_len_c2_ph {u w : ℂ} {b m : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hm : m = (1 + b) / (1 - b)) (hu : u ∈ unitDisc) (hw : w ∈ unitDisc)
    (h : ‖w - u‖ < b * ‖1 - (starRingEnd ℂ) u * w‖) :
    1 ≤ m ∧ ‖w - u‖ ≤ (m - 1) * (1 - ‖u‖) ∧ ‖w - u‖ ≤ (m - 1) * (1 - ‖w‖) := by
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hb' : 0 < 1 - b := by linarith
  have em : m - 1 = 2 * b / (1 - b) := by
    rw [hm]
    field_simp
    ring
  have hm1 : 1 ≤ m := by
    have : 0 ≤ 2 * b / (1 - b) := div_nonneg (by linarith) hb'.le
    linarith
  have hcu : ‖(1 : ℂ) - (starRingEnd ℂ) u * w‖ ≤ (1 - ‖u‖ ^ 2) + ‖w - u‖ := by
    have e : (1 : ℂ) - (starRingEnd ℂ) u * w =
        ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) + (starRingEnd ℂ) u * (u - w) := by
      push_cast
      rw [← Complex.conj_mul' u]
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_of_nonneg (by nlinarith [norm_nonneg u]), norm_mul, Complex.norm_conj,
      norm_sub_rev u w]
    nlinarith [norm_nonneg (w - u), norm_nonneg u]
  have hcw : ‖(1 : ℂ) - (starRingEnd ℂ) u * w‖ ≤ (1 - ‖w‖ ^ 2) + ‖w - u‖ := by
    have e : (1 : ℂ) - (starRingEnd ℂ) u * w =
        ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) + (starRingEnd ℂ) (w - u) * w := by
      push_cast
      rw [← Complex.conj_mul' w, map_sub]
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_of_nonneg (by nlinarith [norm_nonneg w]), norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg (w - u), norm_nonneg w]
  have key : ∀ d : ℝ, 0 ≤ d → d ≤ 1 →
      ‖(1 : ℂ) - (starRingEnd ℂ) u * w‖ ≤ (1 - d ^ 2) + ‖w - u‖ → ‖w - u‖ ≤ (m - 1) * (1 - d) := by
    intro d hd0 hd1 hc
    rw [em, div_mul_eq_mul_div, le_div_iff₀ hb']
    have h1 : b * ‖(1 : ℂ) - (starRingEnd ℂ) u * w‖ ≤ b * ((1 - d ^ 2) + ‖w - u‖) :=
      mul_le_mul_of_nonneg_left hc hb0.le
    have h2 : b * (1 - d) * (1 + d) ≤ b * (1 - d) * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hb0.le (by linarith))
    nlinarith
  exact ⟨hm1, key _ (norm_nonneg u) hu1.le hcu, key _ (norm_nonneg w) hw1.le hcw⟩

/-- Helper for `lem_length` (Stage A, case (ii), hyperbolic distortion): for `u, z ∈ 𝔻` with
`|z - u| ≤ A(1-|u|)` and `c(1-|u|) ≤ 1-|z|` (`0 < c ≤ 1`), `|f'(z)| ≥ e^{-6A/c} |f'(u)|`
(integrate `|f''/f'| ≤ 6/(1-|ξ|²)`, `s02_sw_bloch`, along `[u, z]`, for a logarithm of `f'` on
`𝔻` from `kb_exists_log`). -/
theorem s09_len_c2_dist {f : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω) {u z : ℂ}
    (hu : u ∈ unitDisc) (hz : z ∈ unitDisc) {A c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hA : ‖z - u‖ ≤ A * (1 - ‖u‖)) (hcz : c * (1 - ‖u‖) ≤ 1 - ‖z‖) :
    Real.exp (-(6 * A / c)) * ‖deriv f u‖ ≤ ‖deriv f z‖ := by
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  have hd0 : 0 < 1 - ‖u‖ := by linarith
  have hcd : 0 < c * (1 - ‖u‖) := mul_pos hc0 hd0
  have hf1 : DifferentiableOn ℂ (deriv f) (ball (0 : ℂ) 1) := hf.1.deriv isOpen_ball
  have hne : ∀ ζ ∈ ball (0 : ℂ) 1, deriv f ζ ≠ 0 := fun ζ hζ =>
    deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hζ
  obtain ⟨L, hLd, hLe⟩ := kb_exists_log hf1 hne
  have hcu : c * (1 - ‖u‖) ≤ 1 - ‖u‖ := by nlinarith
  have hS : ∀ ζ ∈ segment ℝ u z, ‖ζ‖ ≤ 1 - c * (1 - ‖u‖) := by
    intro ζ hζ
    have hu' : u ∈ closedBall (0 : ℂ) (1 - c * (1 - ‖u‖)) :=
      mem_closedBall_zero_iff.mpr (by linarith)
    have hz' : z ∈ closedBall (0 : ℂ) (1 - c * (1 - ‖u‖)) :=
      mem_closedBall_zero_iff.mpr (by linarith)
    have hsub := (convex_closedBall (0 : ℂ) (1 - c * (1 - ‖u‖))).segment_subset hu' hz'
    exact mem_closedBall_zero_iff.mp (hsub hζ)
  have hSD : ∀ ζ ∈ segment ℝ u z, ζ ∈ ball (0 : ℂ) 1 := fun ζ hζ =>
    mem_ball_zero_iff.mpr (by linarith [hS ζ hζ])
  have hLd' : ∀ ζ ∈ ball (0 : ℂ) 1, deriv L ζ = deriv (deriv f) ζ / deriv f ζ := by
    intro ζ hζ
    have hLa : HasDerivAt L (deriv L ζ) ζ :=
      (hLd.differentiableAt (isOpen_ball.mem_nhds hζ)).hasDerivAt
    have he : (fun v => Complex.exp (L v)) =ᶠ[𝓝 ζ] deriv f :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hζ) hLe
    have h1 : deriv (fun v => Complex.exp (L v)) ζ = Complex.exp (L ζ) * deriv L ζ :=
      hLa.cexp.deriv
    rw [he.deriv_eq, hLe ζ hζ] at h1
    rw [h1, mul_div_cancel_left₀ _ (hne ζ hζ)]
  have hbound : ∀ ζ ∈ segment ℝ u z, ‖deriv L ζ‖ ≤ 6 / (c * (1 - ‖u‖)) := by
    intro ζ hζ
    have hζD := hSD ζ hζ
    have hζ1 := hS ζ hζ
    have hb := s02_sw_bloch hf hζD
    rw [hLd' ζ hζD, le_div_iff₀ hcd]
    have hl : c * (1 - ‖u‖) ≤ 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
    nlinarith [mul_le_mul_of_nonneg_left hl (norm_nonneg (deriv (deriv f) ζ / deriv f ζ))]
  have hmvt := (convex_segment u z).norm_image_sub_le_of_norm_deriv_le
    (fun ζ hζ => hLd.differentiableAt (isOpen_ball.mem_nhds (hSD ζ hζ))) hbound
    (left_mem_segment ℝ u z) (right_mem_segment ℝ u z)
  have hE : 6 / (c * (1 - ‖u‖)) * ‖z - u‖ ≤ 6 * A / c := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hcd hc0]
    nlinarith [mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 6 * c)]
  have hre : (L u).re - 6 * A / c ≤ (L z).re := by
    have := (Complex.abs_re_le_norm (L z - L u)).trans (hmvt.trans hE)
    rw [Complex.sub_re] at this
    linarith [abs_le.mp this]
  rw [← hLe u hu, ← hLe z hz, Complex.norm_exp, Complex.norm_exp, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- Helper for `lem_length` (Stage A, case (ii)): pointwise arithmetic,
`δ² G/(8kD) ≤ p² s³ F` from `δ/2 ≤ s² p`, `0 < s ≤ 2kD` and `0 ≤ G ≤ F`. -/
theorem s09_len_c2_arith2 {p s F G D k δ : ℝ} (hδ : 0 < δ) (hs : 0 < s) (hk : 0 < k) (hD : 0 < D)
    (hsD : s ≤ 2 * k * D) (hp : δ / 2 ≤ s ^ 2 * p) (hG : 0 ≤ G) (hF : G ≤ F) :
    δ ^ 2 * G / (8 * k * D) ≤ p ^ 2 * s ^ 3 * F := by
  have h0 : 0 ≤ p ^ 2 * s ^ 3 := by positivity
  have h1 : δ ^ 2 / (8 * k * D) ≤ p ^ 2 * s ^ 3 := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : (δ / 2) ^ 2 ≤ (s ^ 2 * p) ^ 2 := pow_le_pow_left₀ (by positivity) hp 2
    have h3 : 4 * (p ^ 2 * s ^ 3) * s ≤ 4 * (p ^ 2 * s ^ 3) * (2 * k * D) :=
      mul_le_mul_of_nonneg_left hsD (by positivity)
    nlinarith
  calc δ ^ 2 * G / (8 * k * D) = δ ^ 2 / (8 * k * D) * G := by ring
    _ ≤ p ^ 2 * s ^ 3 * G := mul_le_mul_of_nonneg_right h1 hG
    _ ≤ p ^ 2 * s ^ 3 * F := mul_le_mul_of_nonneg_left hF h0

/-- Helper for `lem_length` (Stage A, case (ii)): `F q⁴ s³ ≤ 6⁴ F/d` from `s q ≤ 6` and
`0 < d ≤ s` (the Bloch bound turned into `|f'| |f''/f'|⁴ (1-|u|²)³ ≤ 6⁴ |f'|/(1-|u|)`). -/
theorem s09_len_c2_arith3 {F q s d : ℝ} (hF : 0 ≤ F) (hq : 0 ≤ q) (hd : 0 < d) (hds : d ≤ s)
    (hb : s * q ≤ 6) : F * q ^ 4 * s ^ 3 ≤ 6 ^ 4 * F / d := by
  have hs : 0 < s := lt_of_lt_of_le hd hds
  rw [le_div_iff₀ hd]
  have h1 : (s * q) ^ 4 ≤ 6 ^ 4 := pow_le_pow_left₀ (by positivity) hb 4
  have h2 : q ^ 4 * s ^ 3 * d ≤ q ^ 4 * s ^ 3 * s := mul_le_mul_of_nonneg_left hds (by positivity)
  calc F * q ^ 4 * s ^ 3 * d = F * (q ^ 4 * s ^ 3 * d) := by ring
    _ ≤ F * (q ^ 4 * s ^ 3 * s) := mul_le_mul_of_nonneg_left h2 hF
    _ = F * (s * q) ^ 4 := by ring
    _ ≤ F * 6 ^ 4 := mul_le_mul_of_nonneg_left h1 hF
    _ = 6 ^ 4 * F := by ring

/-- Helper for `lem_length` (Stage A, case (ii)): the constant bookkeeping of
`s09_len_c2_peru` (with `D ≤ m D_w`). -/
theorem s09_len_c2_arith4 {P δ E η k D Dw F m : ℝ} (hP : 0 < P) (hδ : 0 < δ) (hE : 0 < E)
    (hη : 0 < η) (hk : 0 < k) (hD : 0 < D) (hDw : 0 < Dw) (hm : 0 < m) (hF : 0 ≤ F)
    (hDm : D ≤ m * Dw) :
    6 ^ 4 * F / D ≤ 6 ^ 4 * 8 * k * m ^ 2 / (P * δ ^ 2 * E * η ^ 2) *
      (1 / D ^ 2 * (δ ^ 2 * (E * F) / (8 * k * D)) * ((η * Dw) ^ 2 * P)) := by
  have e : 6 ^ 4 * 8 * k * m ^ 2 / (P * δ ^ 2 * E * η ^ 2) *
      (1 / D ^ 2 * (δ ^ 2 * (E * F) / (8 * k * D)) * ((η * Dw) ^ 2 * P)) =
        6 ^ 4 * F / D * (m * Dw / D) ^ 2 := by
    field_simp
  rw [e]
  refine le_mul_of_one_le_right (div_nonneg (by positivity) hD.le) (one_le_pow₀ ?_)
  rw [le_div_iff₀ hD]
  linarith

/-- Helper for `lem_length` (Stage A, case (ii), pointwise lower bound): with `m = (1+b)/(1-b)`
and `η = min(1/2, δ/99840)`, if `|w - u| < b |1 - ū w|`, `δ ≤ (1-|w|²)²|Sf(w)|` and
`|z - w| < η(1-|w|)`, then `|z - u| < 3m(1-|u|)`, `1-|u| < 4m(1-|z|)`, `z ∈ 𝔻` and
`δ² e^{-24m²} |f'(u)|/(16m(1-|u|)) ≤ |Sf(z)|² (1-|z|²)³ |f'(z)|`
(`s09_len_c2_ph`, `s09_len_c2_lip` at `w`, `s09_len_c2_dist`). -/
theorem s09_len_c2_ptw {f : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω) {b δ m η : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1) (hδ : 0 < δ) (hm : m = (1 + b) / (1 - b))
    (hη : η = min (1 / 2) (δ / 99840)) {u w z : ℂ} (hu : u ∈ unitDisc) (hw : w ∈ unitDisc)
    (hwu : ‖w - u‖ < b * ‖1 - (starRingEnd ℂ) u * w‖)
    (hφ : δ ≤ (1 - ‖w‖ ^ 2) ^ 2 * ‖schwarzian f w‖) (hz : ‖z - w‖ < η * (1 - ‖w‖)) :
    ‖z - u‖ < 3 * m * (1 - ‖u‖) ∧ 1 - ‖u‖ < 4 * m * (1 - ‖z‖) ∧ z ∈ unitDisc ∧
      δ ^ 2 * (Real.exp (-(6 * (2 * m) / (1 / (2 * m)))) * ‖deriv f u‖) /
          (8 * (2 * m) * (1 - ‖u‖)) ≤
        ‖schwarzian f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3 * ‖deriv f z‖ := by
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hdu : 0 < 1 - ‖u‖ := by linarith
  have hdw : 0 < 1 - ‖w‖ := by linarith
  obtain ⟨hm1, P1, P2⟩ := s09_len_c2_ph hb0 hb1 hm hu hw hwu
  have hm0 : 0 < m := by linarith
  have hη1 : η ≤ 1 / 2 := by rw [hη]; exact min_le_left _ _
  have hη2 : η ≤ δ / 99840 := by rw [hη]; exact min_le_right _ _
  have P3 : 1 - ‖u‖ ≤ m * (1 - ‖w‖) := by
    have := norm_sub_norm_le w u
    linarith
  have P4 : 1 - ‖w‖ ≤ m * (1 - ‖u‖) := by
    have := norm_sub_norm_le u w
    rw [norm_sub_rev] at this
    linarith
  obtain ⟨g1, g2⟩ := s09_len_c2_geo hz.le
  have hηw : η * (1 - ‖w‖) ≤ 1 / 2 * (1 - ‖w‖) := mul_le_mul_of_nonneg_right hη1 hdw.le
  have hdz : 1 / 2 * (1 - ‖w‖) ≤ 1 - ‖z‖ := by linarith
  have hz1 : ‖z‖ < 1 := by linarith
  have hzD : z ∈ unitDisc := mem_ball_zero_iff.mpr hz1
  have hzu0 : ‖z - u‖ ≤ ‖z - w‖ + ‖w - u‖ := norm_sub_le_norm_sub_add_norm_sub z w u
  have hmu := mul_pos hm0 hdu
  have hzu2 : ‖z - u‖ ≤ 2 * m * (1 - ‖u‖) := by linarith
  have hzu : ‖z - u‖ < 3 * m * (1 - ‖u‖) := by linarith
  have hmz : m * (1 / 2 * (1 - ‖w‖)) ≤ m * (1 - ‖z‖) := mul_le_mul_of_nonneg_left hdz hm0.le
  have hmz0 : 0 < m * (1 - ‖z‖) := mul_pos hm0 (by linarith)
  have huz : 1 - ‖u‖ < 4 * m * (1 - ‖z‖) := by linarith
  refine ⟨hzu, huz, hzD, ?_⟩
  have hww : ‖w - w‖ < 1 / 2 * (1 - ‖w‖) := by rw [sub_self, norm_zero]; linarith
  have hlip := s09_len_c2_lip hf hw (κ := 1 / 2) (by norm_num) (by norm_num)
    (show ‖z - w‖ < 1 / 2 * (1 - ‖w‖) by linarith) hww
  have hL : 6240 * ‖z - w‖ / ((1 - 1 / 2) ^ 3 * (1 - ‖w‖)) ≤ δ / 2 := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hdw)]
    have h3 : ‖z - w‖ ≤ δ / 99840 * (1 - ‖w‖) :=
      hz.le.trans (mul_le_mul_of_nonneg_right hη2 hdw.le)
    linarith
  have hc : 1 / (2 * m) * (1 - ‖u‖) ≤ 1 - ‖z‖ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    linarith
  have hdist := s09_len_c2_dist hf hu hzD (A := 2 * m) (c := 1 / (2 * m)) (by positivity)
    (by rw [div_le_iff₀ (by linarith)]; linarith) hzu2 hc
  have hs : 0 < 1 - ‖z‖ ^ 2 := sub_pos.mpr (pow_lt_one₀ (norm_nonneg z) hz1 two_ne_zero)
  have hs2 : 1 - ‖z‖ ^ 2 ≤ 2 * (1 - ‖z‖) := by
    have := sq_nonneg (1 - ‖z‖)
    linarith
  have hsD : 1 - ‖z‖ ^ 2 ≤ 2 * (2 * m) * (1 - ‖u‖) := by linarith
  exact s09_len_c2_arith2 hδ hs (by linarith) hdu hsD (by linarith) (by positivity) hdist

/-- Helper for `lem_length` (Stage A, case (ii), Fubini weight): for `1 ≤ m` and `z ∈ 𝔻`,
`∫ 1{|z - u| < 3m(1-|u|), 1-|u| < 4m(1-|z|)} (1-|u|)⁻² du ≤ 2304 π m⁶`. -/
theorem s09_len_c2_inner {m : ℝ} (hm : 1 ≤ m) {z : ℂ} (hz : z ∈ unitDisc) :
    ∫⁻ u, ENNReal.ofReal (1 / (1 - ‖u‖) ^ 2) *
        {p : ℂ × ℂ | ‖p.2 - p.1‖ < 3 * m * (1 - ‖p.1‖) ∧
          1 - ‖p.1‖ < 4 * m * (1 - ‖p.2‖)}.indicator 1 (u, z) ≤
      ENNReal.ofReal (2304 * π * m ^ 6) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hdz : 0 < 1 - ‖z‖ := by linarith
  have hm0 : 0 < m := by linarith
  have hR : 0 ≤ 12 * m ^ 2 * (1 - ‖z‖) := by positivity
  have hpt : ∀ u, ENNReal.ofReal (1 / (1 - ‖u‖) ^ 2) *
        {p : ℂ × ℂ | ‖p.2 - p.1‖ < 3 * m * (1 - ‖p.1‖) ∧
          1 - ‖p.1‖ < 4 * m * (1 - ‖p.2‖)}.indicator 1 (u, z) ≤
      (ball z (12 * m ^ 2 * (1 - ‖z‖))).indicator
        (fun _ => ENNReal.ofReal (16 * m ^ 2 / (1 - ‖z‖) ^ 2)) u := by
    intro u
    by_cases hS : (u, z) ∈ {p : ℂ × ℂ | ‖p.2 - p.1‖ < 3 * m * (1 - ‖p.1‖) ∧
        1 - ‖p.1‖ < 4 * m * (1 - ‖p.2‖)}
    · have hS' : ‖z - u‖ < 3 * m * (1 - ‖u‖) ∧ 1 - ‖u‖ < 4 * m * (1 - ‖z‖) := hS
      obtain ⟨hzu, huz⟩ := hS'
      have hdu : 0 < 1 - ‖u‖ := by
        by_contra hc
        have hc' := not_lt.mp hc
        nlinarith [norm_nonneg (z - u), mul_le_mul_of_nonneg_left hc' hm0.le]
      have h1 := norm_sub_norm_le u z
      rw [norm_sub_rev] at h1
      have hmu : 1 - ‖u‖ ≤ m * (1 - ‖u‖) := by nlinarith
      have hzu4 : 1 - ‖z‖ ≤ 4 * m * (1 - ‖u‖) := by nlinarith
      have hmem : u ∈ ball z (12 * m ^ 2 * (1 - ‖z‖)) := by
        rw [mem_ball_iff_norm, norm_sub_rev]
        have h2 : 3 * m * (1 - ‖u‖) ≤ 3 * m * (4 * m * (1 - ‖z‖)) :=
          mul_le_mul_of_nonneg_left huz.le (by positivity)
        nlinarith
      rw [Set.indicator_of_mem hS, Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_div_iff₀ (pow_pos hdu 2) (pow_pos hdz 2), one_mul]
      have h := pow_le_pow_left₀ hdz.le hzu4 2
      nlinarith
    · rw [Set.indicator_of_notMem hS, mul_zero]
      exact zero_le
  calc _ ≤ ∫⁻ u, (ball z (12 * m ^ 2 * (1 - ‖z‖))).indicator
          (fun _ => ENNReal.ofReal (16 * m ^ 2 / (1 - ‖z‖) ^ 2)) u := lintegral_mono hpt
    _ = ENNReal.ofReal (16 * m ^ 2 / (1 - ‖z‖) ^ 2) *
          (ENNReal.ofReal (12 * m ^ 2 * (1 - ‖z‖)) ^ 2 * NNReal.pi) := by
        rw [lintegral_indicator_const measurableSet_ball, Complex.volume_ball]
    _ = ENNReal.ofReal (2304 * π * m ^ 6) := by
        rw [← ENNReal.ofReal_coe_nnreal (p := NNReal.pi), NNReal.coe_real_pi,
          ← ENNReal.ofReal_pow hR,
          ← ENNReal.ofReal_mul (p := (12 * m ^ 2 * (1 - ‖z‖)) ^ 2) (by positivity),
          ← ENNReal.ofReal_mul (p := 16 * m ^ 2 / (1 - ‖z‖) ^ 2) (by positivity)]
        congr 1
        field_simp
        ring

/-- Helper for `lem_length` (Stage A, case (ii), one point): for `u ∈ 𝔻` with a witness
`w ∈ 𝔻` (`|w - u| < b |1 - ū w|`, `δ ≤ (1-|w|²)²|Sf(w)|`),
`|f'(u)| |f''/f'(u)|⁴ (1-|u|²)³ ≤ C₀ ∫_𝔻 (1-|u|)⁻² 1_S(u, z) |Sf|²(1-|z|²)³ |f'| dz`
(integrate `s09_len_c2_ptw` over `B(w, η(1-|w|))`; Bloch `s02_sw_bloch` on the left). -/
theorem s09_len_c2_peru {f : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω) {b δ m η : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1) (hδ : 0 < δ) (hm : m = (1 + b) / (1 - b))
    (hη : η = min (1 / 2) (δ / 99840)) {u w : ℂ} (hu : u ∈ unitDisc) (hw : w ∈ unitDisc)
    (hwu : ‖w - u‖ < b * ‖1 - (starRingEnd ℂ) u * w‖)
    (hφ : δ ≤ (1 - ‖w‖ ^ 2) ^ 2 * ‖schwarzian f w‖) :
    ENNReal.ofReal (‖deriv f u‖ * ‖deriv (deriv f) u / deriv f u‖ ^ 4 * (1 - ‖u‖ ^ 2) ^ 3) ≤
      ENNReal.ofReal (6 ^ 4 * 8 * (2 * m) * m ^ 2 /
          (π * δ ^ 2 * Real.exp (-(6 * (2 * m) / (1 / (2 * m)))) * η ^ 2)) *
        ∫⁻ z in unitDisc, ENNReal.ofReal (1 / (1 - ‖u‖) ^ 2) *
          {p : ℂ × ℂ | ‖p.2 - p.1‖ < 3 * m * (1 - ‖p.1‖) ∧
            1 - ‖p.1‖ < 4 * m * (1 - ‖p.2‖)}.indicator 1 (u, z) *
          (ENNReal.ofReal (‖schwarzianHol f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) *
            ENNReal.ofReal ‖deriv f z‖) := by
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hd0 : 0 < 1 - ‖u‖ := by linarith
  have hdw : 0 < 1 - ‖w‖ := by linarith
  obtain ⟨hm1, -, P2⟩ := s09_len_c2_ph hb0 hb1 hm hu hw hwu
  have hm0 : 0 < m := by linarith
  have P3 : 1 - ‖u‖ ≤ m * (1 - ‖w‖) := by
    have := norm_sub_norm_le w u
    nlinarith
  have hη0 : 0 < η := by
    rw [hη]
    exact lt_min (by norm_num) (by positivity)
  have hg0 : 0 ≤ 1 / (1 - ‖u‖) ^ 2 * (δ ^ 2 * (Real.exp (-(6 * (2 * m) / (1 / (2 * m)))) *
      ‖deriv f u‖) / (8 * (2 * m) * (1 - ‖u‖))) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) (by positivity))
  have hCu0 : 0 ≤ 6 ^ 4 * 8 * (2 * m) * m ^ 2 /
      (π * δ ^ 2 * Real.exp (-(6 * (2 * m) / (1 / (2 * m)))) * η ^ 2) :=
    div_nonneg (by positivity) (by positivity)
  have hlow : ∫⁻ z in ball w (η * (1 - ‖w‖)), ENNReal.ofReal (1 / (1 - ‖u‖) ^ 2 *
        (δ ^ 2 * (Real.exp (-(6 * (2 * m) / (1 / (2 * m)))) * ‖deriv f u‖) /
          (8 * (2 * m) * (1 - ‖u‖)))) ≤
      ∫⁻ z in unitDisc, ENNReal.ofReal (1 / (1 - ‖u‖) ^ 2) *
          {p : ℂ × ℂ | ‖p.2 - p.1‖ < 3 * m * (1 - ‖p.1‖) ∧
            1 - ‖p.1‖ < 4 * m * (1 - ‖p.2‖)}.indicator 1 (u, z) *
          (ENNReal.ofReal (‖schwarzianHol f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) *
            ENNReal.ofReal ‖deriv f z‖) := by
    have hB : ball w (η * (1 - ‖w‖)) ⊆ unitDisc := fun z hz =>
      (s09_len_c2_ptw hf hb0 hb1 hδ hm hη hu hw hwu hφ (mem_ball_iff_norm.mp hz)).2.2.1
    refine (setLIntegral_mono' measurableSet_ball fun z hz => ?_).trans (lintegral_mono_set hB)
    obtain ⟨hzu, huz, hzD, hlb⟩ :=
      s09_len_c2_ptw hf hb0 hb1 hδ hm hη hu hw hwu hφ (mem_ball_iff_norm.mp hz)
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hzD
    have hs0 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have hSch : schwarzian f z = schwarzianHol f z :=
      schwarzian_of_analyticAt (hf.1.analyticAt (isOpen_ball.mem_nhds hzD))
    have hmem : (u, z) ∈ {p : ℂ × ℂ | ‖p.2 - p.1‖ < 3 * m * (1 - ‖p.1‖) ∧
        1 - ‖p.1‖ < 4 * m * (1 - ‖p.2‖)} := ⟨hzu, huz⟩
    rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one, ← hSch,
      ← ENNReal.ofReal_mul (p := ‖schwarzian f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3)
        (mul_nonneg (sq_nonneg _) (pow_nonneg hs0 3)),
      ← ENNReal.ofReal_mul (p := 1 / (1 - ‖u‖) ^ 2) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hlb (by positivity))
  have hρ : 0 ≤ η * (1 - ‖w‖) := mul_nonneg hη0.le hdw.le
  have hreal : ‖deriv f u‖ * ‖deriv (deriv f) u / deriv f u‖ ^ 4 * (1 - ‖u‖ ^ 2) ^ 3 ≤
      6 ^ 4 * 8 * (2 * m) * m ^ 2 /
          (π * δ ^ 2 * Real.exp (-(6 * (2 * m) / (1 / (2 * m)))) * η ^ 2) *
        (1 / (1 - ‖u‖) ^ 2 * (δ ^ 2 * (Real.exp (-(6 * (2 * m) / (1 / (2 * m)))) *
          ‖deriv f u‖) / (8 * (2 * m) * (1 - ‖u‖))) * ((η * (1 - ‖w‖)) ^ 2 * π)) :=
    (s09_len_c2_arith3 (norm_nonneg _) (norm_nonneg _) hd0 (by nlinarith [norm_nonneg u])
      (s02_sw_bloch hf hu)).trans
      (s09_len_c2_arith4 Real.pi_pos hδ (Real.exp_pos _) hη0 (by linarith) hd0 hdw hm0
        (norm_nonneg _) P3)
  calc _ ≤ ENNReal.ofReal (6 ^ 4 * 8 * (2 * m) * m ^ 2 /
          (π * δ ^ 2 * Real.exp (-(6 * (2 * m) / (1 / (2 * m)))) * η ^ 2) *
        (1 / (1 - ‖u‖) ^ 2 * (δ ^ 2 * (Real.exp (-(6 * (2 * m) / (1 / (2 * m)))) *
          ‖deriv f u‖) / (8 * (2 * m) * (1 - ‖u‖))) * ((η * (1 - ‖w‖)) ^ 2 * π))) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (6 ^ 4 * 8 * (2 * m) * m ^ 2 /
          (π * δ ^ 2 * Real.exp (-(6 * (2 * m) / (1 / (2 * m)))) * η ^ 2)) *
        ∫⁻ z in ball w (η * (1 - ‖w‖)), ENNReal.ofReal (1 / (1 - ‖u‖) ^ 2 *
          (δ ^ 2 * (Real.exp (-(6 * (2 * m) / (1 / (2 * m)))) * ‖deriv f u‖) /
            (8 * (2 * m) * (1 - ‖u‖)))) := by
        rw [setLIntegral_const, Complex.volume_ball,
          ← ENNReal.ofReal_coe_nnreal (p := NNReal.pi), NNReal.coe_real_pi,
          ← ENNReal.ofReal_pow hρ,
          ← ENNReal.ofReal_mul (p := (η * (1 - ‖w‖)) ^ 2) (by positivity),
          ← ENNReal.ofReal_mul hg0, ← ENNReal.ofReal_mul hCu0]
    _ ≤ _ := mul_le_mul_right hlow _

/-- Helper for `lem_length` (Stage A, S3, case (ii)): on the points `u` near which the Schwarzian
is not small (`δ ≤ (1-|w|²)² |Sf(w)|` for some `|w - u| < b |1 - ū w|`),
`∫ |f'| |g'|⁴ (1-|u|²)³ ≤ C(b, δ) ∫ |f'| |Sf|² (1-|z|²)³` (Bloch `s02_sw_bloch`, Kraus, a Cauchy
estimate for `Sf`, `s09_len_distort`-type comparability of `|f'|` on Whitney discs, Fubini). -/
theorem s09_len_case_ii (b δ : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hδ : 0 < δ) :
    ∃ C : ℝ≥0, ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsConformalOnto f unitDisc Ω →
      ∫⁻ u in {u | u ∈ unitDisc ∧ ∃ w ∈ unitDisc, ‖w - u‖ < b * ‖1 - (starRingEnd ℂ) u * w‖ ∧
          δ ≤ (1 - ‖w‖ ^ 2) ^ 2 * ‖schwarzian f w‖},
        ENNReal.ofReal (‖deriv f u‖ * ‖deriv (deriv f) u / deriv f u‖ ^ 4 * (1 - ‖u‖ ^ 2) ^ 3) ≤
      (C : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f := by
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (1 + b) / (1 - b) := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min (1 / 2) (δ / 99840) := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by
    rw [hm, le_div_iff₀ (by linarith)]
    linarith
  obtain ⟨Cu, hCu⟩ : ∃ Cu : ℝ, Cu = 6 ^ 4 * 8 * (2 * m) * m ^ 2 /
      (π * δ ^ 2 * Real.exp (-(6 * (2 * m) / (1 / (2 * m)))) * η ^ 2) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = 2304 * π * m ^ 6 := ⟨_, rfl⟩
  have hCu0 : 0 ≤ Cu := by
    rw [hCu]
    exact div_nonneg (by have := hm1; positivity) (by positivity)
  refine ⟨Real.toNNReal (Cu * Q), fun Ω f hf => ?_⟩
  have hSm := s02_pullback_measurable_schwarzianHol f
  have hDm := measurable_deriv f
  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℝ≥0∞, H = fun z =>
      ENNReal.ofReal (‖schwarzianHol f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) * ENNReal.ofReal ‖deriv f z‖ :=
    ⟨_, rfl⟩
  have hHm : Measurable H := by
    rw [hH]
    fun_prop
  have hSo : IsOpen {p : ℂ × ℂ | ‖p.2 - p.1‖ < 3 * m * (1 - ‖p.1‖) ∧
      1 - ‖p.1‖ < 4 * m * (1 - ‖p.2‖)} :=
    (isOpen_lt (continuous_snd.sub continuous_fst).norm
      (continuous_const.mul (continuous_const.sub continuous_fst.norm))).inter
    (isOpen_lt (continuous_const.sub continuous_fst.norm)
      (continuous_const.mul (continuous_const.sub continuous_snd.norm)))
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ → ℝ≥0∞, G = fun u z => ENNReal.ofReal (1 / (1 - ‖u‖) ^ 2) *
      {p : ℂ × ℂ | ‖p.2 - p.1‖ < 3 * m * (1 - ‖p.1‖) ∧
        1 - ‖p.1‖ < 4 * m * (1 - ‖p.2‖)}.indicator 1 (u, z) * H z := ⟨_, rfl⟩
  have hGm : Measurable (Function.uncurry G) := by
    rw [hG]
    show Measurable fun p : ℂ × ℂ => ENNReal.ofReal (1 / (1 - ‖p.1‖) ^ 2) *
      {p : ℂ × ℂ | ‖p.2 - p.1‖ < 3 * m * (1 - ‖p.1‖) ∧
        1 - ‖p.1‖ < 4 * m * (1 - ‖p.2‖)}.indicator 1 (p.1, p.2) * H p.2
    exact ((by fun_prop : Measurable fun p : ℂ × ℂ => ENNReal.ofReal (1 / (1 - ‖p.1‖) ^ 2)).mul
      (measurable_one.indicator hSo.measurableSet)).mul (hHm.comp measurable_snd)
  have hGi : Measurable fun u => ∫⁻ z in unitDisc, G u z := hGm.lintegral_prod_right'
  have hper : ∀ u w : ℂ, u ∈ unitDisc → w ∈ unitDisc →
      ‖w - u‖ < b * ‖1 - (starRingEnd ℂ) u * w‖ →
      δ ≤ (1 - ‖w‖ ^ 2) ^ 2 * ‖schwarzian f w‖ →
      ENNReal.ofReal (‖deriv f u‖ * ‖deriv (deriv f) u / deriv f u‖ ^ 4 * (1 - ‖u‖ ^ 2) ^ 3) ≤
        ENNReal.ofReal Cu * ∫⁻ z in unitDisc, G u z := by
    intro u w hu hw hwu hφ
    rw [hG, hH, hCu]
    exact s09_len_c2_peru hf hb0 hb1 hδ hm hη hu hw hwu hφ
  have hinner : ∀ z ∈ unitDisc, ∫⁻ u, G u z ≤ ENNReal.ofReal Q * H z := by
    intro z hz
    have hHt : H z ≠ ⊤ := by
      rw [hH]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    rw [hG]
    show ∫⁻ u, ENNReal.ofReal (1 / (1 - ‖u‖) ^ 2) *
        {p : ℂ × ℂ | ‖p.2 - p.1‖ < 3 * m * (1 - ‖p.1‖) ∧
          1 - ‖p.1‖ < 4 * m * (1 - ‖p.2‖)}.indicator 1 (u, z) * H z ≤ _
    rw [lintegral_mul_const' _ _ hHt, hQ]
    exact mul_le_mul_left (s09_len_c2_inner hm1 hz) _
  have hSch : ∀ z ∈ unitDisc, schwarzian f z = schwarzianHol f z := fun z hz =>
    schwarzian_of_analyticAt (hf.1.analyticAt (isOpen_ball.mem_nhds hz))
  have hcm : Measurable fun z => ENNReal.ofReal (‖schwarzianHol f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) := by
    fun_prop
  have hRHS : ∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f =
      ∫⁻ z in unitDisc, H z := by
    have hR : schwarzCarlesonMeasure f = (volume.restrict unitDisc).withDensity
        fun z => ENNReal.ofReal (‖schwarzianHol f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) := by
      unfold schwarzCarlesonMeasure
      refine withDensity_congr_ae ((ae_restrict_mem measurableSet_ball).mono fun z hz => ?_)
      simp only [hSch z hz]
    rw [hR, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hcm
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), hH]
    rfl
  refine (setLIntegral_mono (hGi.const_mul (ENNReal.ofReal Cu)) fun u hu => ?_).trans ?_
  · obtain ⟨huD, w, hwD, hwu, hφ⟩ := hu
    exact hper u w huD hwD hwu hφ
  calc _ ≤ ∫⁻ u, ENNReal.ofReal Cu * ∫⁻ z in unitDisc, G u z := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal Cu * ∫⁻ u, ∫⁻ z in unitDisc, G u z :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal Cu * ∫⁻ z in unitDisc, ∫⁻ u, G u z := by
        rw [lintegral_lintegral_swap hGm.aemeasurable]
    _ ≤ ENNReal.ofReal Cu * ∫⁻ z in unitDisc, ENNReal.ofReal Q * H z :=
        mul_le_mul_right (setLIntegral_mono (hHm.const_mul _) hinner) _
    _ = ENNReal.ofReal Cu * (ENNReal.ofReal Q * ∫⁻ z in unitDisc, H z) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by
        rw [hRHS, ← mul_assoc, ← ENNReal.ofReal_mul hCu0]
        rfl

/-- Helper for `s09_len_bad` (Stage B, B1a, Gronwall for `y'' = -(S/2) y`): if `y` is holomorphic on
`𝔻`, `y'' = -(S/2) y` there and `|S| ≤ Q` on `|z| ≤ r < 1`, then on `|z| ≤ r` the solution stays
close to its tangent line: `|y(z) - y(0) - y'(0) z| ≤ (|y(0)| + |y'(0)|) Q e^{1+Q}` (along
`t ↦ y(tz)`, `norm_le_gronwallBound_of_norm_deriv_right_le` for `(φ - α - βzt, φ' - βz)`). -/
theorem s09_bad_ode {y S : ℂ → ℂ} {r Q : ℝ} (hr : r < 1) (hQ : 0 ≤ Q)
    (hy : DifferentiableOn ℂ y unitDisc)
    (hode : ∀ z ∈ unitDisc, deriv (deriv y) z = -(S z / 2) * y z)
    (hS : ∀ z : ℂ, ‖z‖ ≤ r → ‖S z‖ ≤ Q) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖y z - (y 0 + deriv y 0 * z)‖ ≤ (‖y 0‖ + ‖deriv y 0‖) * Q * Real.exp (1 + Q) := by
  -- along the path `t ↦ t z`, `t ∈ [0, 1]`
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz hr
  have hnr : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖(t : ℂ) * z‖ ≤ r := by
    intro t ht
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z)
      _ = ‖z‖ := one_mul _
      _ ≤ r := hz
  have hmem : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → (t : ℂ) * z ∈ unitDisc := fun t ht =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (hnr t ht) hr)
  have hyd : ∀ w ∈ unitDisc, HasDerivAt y (deriv y w) w := fun w hw =>
    (hy.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
  have hy'd : ∀ w ∈ unitDisc, HasDerivAt (deriv y) (deriv (deriv y) w) w := fun w hw =>
    ((hy.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
  have hlin : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ) * z) z t := by
    intro t
    have := ((hasDerivAt_id t).ofReal_comp).mul_const z
    simpa using this
  -- `e = (y(tz) - y(0) - y'(0) t z, z y'(tz) - z y'(0))`
  obtain ⟨e, he⟩ : ∃ e : ℝ → ℂ × ℂ, e = fun t : ℝ =>
      (y ((t : ℂ) * z) - (y 0 + deriv y 0 * ((t : ℂ) * z)),
        z * deriv y ((t : ℂ) * z) - z * deriv y 0) := ⟨_, rfl⟩
  obtain ⟨e', he'⟩ : ∃ e' : ℝ → ℂ × ℂ, e' = fun t : ℝ =>
      (z * deriv y ((t : ℂ) * z) - z * deriv y 0, z * (z * deriv (deriv y) ((t : ℂ) * z))) :=
    ⟨_, rfl⟩
  have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt e (e' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => y ((s : ℂ) * z)) (deriv y ((t : ℂ) * z) * z) t :=
      HasDerivAt.comp (h₂ := y) t (hyd _ (hmem t ht)) (hlin t)
    have h2 : HasDerivAt (fun s : ℝ => deriv y ((s : ℂ) * z))
        (deriv (deriv y) ((t : ℂ) * z) * z) t :=
      HasDerivAt.comp (h₂ := deriv y) t (hy'd _ (hmem t ht)) (hlin t)
    have k1 : HasDerivAt (fun s : ℝ => y ((s : ℂ) * z) - (y 0 + deriv y 0 * ((s : ℂ) * z)))
        (z * deriv y ((t : ℂ) * z) - z * deriv y 0) t :=
      (h1.sub (((hlin t).const_mul (deriv y 0)).const_add (y 0))).congr_deriv (by ring)
    have k2 : HasDerivAt (fun s : ℝ => z * deriv y ((s : ℂ) * z) - z * deriv y 0)
        (z * (z * deriv (deriv y) ((t : ℂ) * z))) t :=
      ((h2.const_mul z).sub_const (z * deriv y 0)).congr_deriv (by ring)
    rw [he, he']
    exact k1.prodMk k2
  have he0 : e 0 = 0 := by
    rw [he]
    simp
  have hM : 0 ≤ ‖y 0‖ + ‖deriv y 0‖ := by positivity
  have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hbound : ∀ x ∈ Ico (0 : ℝ) 1,
      ‖e' x‖ ≤ (1 + Q / 2) * ‖e x‖ + Q / 2 * (‖y 0‖ + ‖deriv y 0‖) := by
    intro x hx
    have hxI : x ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hx
    have hw := hmem x hxI
    have hwr := hnr x hxI
    have hw1 : ‖(x : ℂ) * z‖ ≤ 1 := hwr.trans hr.le
    have hSw := hS _ hwr
    have hn1 : ‖(e x).1‖ ≤ ‖e x‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    have hn2 : ‖(e x).2‖ ≤ ‖e x‖ := by rw [Prod.norm_def]; exact le_max_right _ _
    have he1 : (e x).1 = y ((x : ℂ) * z) - (y 0 + deriv y 0 * ((x : ℂ) * z)) := by rw [he]
    have he2 : (e x).2 = z * deriv y ((x : ℂ) * z) - z * deriv y 0 := by rw [he]
    have he'x : e' x = (z * deriv y ((x : ℂ) * z) - z * deriv y 0,
        z * (z * deriv (deriv y) ((x : ℂ) * z))) := by rw [he']
    have hyw : ‖y ((x : ℂ) * z)‖ ≤ ‖e x‖ + (‖y 0‖ + ‖deriv y 0‖) := by
      have h1 : y ((x : ℂ) * z) = (e x).1 + (y 0 + deriv y 0 * ((x : ℂ) * z)) := by
        rw [he1]
        ring
      have h2 := norm_add_le (e x).1 (y 0 + deriv y 0 * ((x : ℂ) * z))
      have h3 := norm_add_le (y 0) (deriv y 0 * ((x : ℂ) * z))
      have h4 : ‖deriv y 0 * ((x : ℂ) * z)‖ ≤ ‖deriv y 0‖ := by
        rw [norm_mul]
        calc ‖deriv y 0‖ * ‖(x : ℂ) * z‖ ≤ ‖deriv y 0‖ * 1 :=
              mul_le_mul_of_nonneg_left hw1 (norm_nonneg _)
          _ = ‖deriv y 0‖ := mul_one _
      rw [h1]
      linarith
    have hsec : ‖z * (z * deriv (deriv y) ((x : ℂ) * z))‖ ≤
        Q / 2 * (‖e x‖ + (‖y 0‖ + ‖deriv y 0‖)) := by
      rw [hode _ hw, norm_mul, norm_mul, norm_mul, norm_neg, norm_div, h2n]
      have a1 : ‖S ((x : ℂ) * z)‖ / 2 * ‖y ((x : ℂ) * z)‖ ≤
          Q / 2 * (‖e x‖ + (‖y 0‖ + ‖deriv y 0‖)) :=
        mul_le_mul (by linarith) hyw (norm_nonneg _) (by linarith)
      have a0 : 0 ≤ ‖S ((x : ℂ) * z)‖ / 2 * ‖y ((x : ℂ) * z)‖ := by positivity
      have a2 : ‖z‖ * (‖S ((x : ℂ) * z)‖ / 2 * ‖y ((x : ℂ) * z)‖) ≤
          ‖S ((x : ℂ) * z)‖ / 2 * ‖y ((x : ℂ) * z)‖ := mul_le_of_le_one_left a0 hz1.le
      have a3 : ‖z‖ * (‖z‖ * (‖S ((x : ℂ) * z)‖ / 2 * ‖y ((x : ℂ) * z)‖)) ≤
          ‖z‖ * (‖S ((x : ℂ) * z)‖ / 2 * ‖y ((x : ℂ) * z)‖) :=
        mul_le_of_le_one_left (mul_nonneg (norm_nonneg z) a0) hz1.le
      linarith
    have hq1 : 0 ≤ Q / 2 * ‖e x‖ := by positivity
    have hq2 : 0 ≤ Q / 2 * (‖y 0‖ + ‖deriv y 0‖) := by positivity
    have hen := norm_nonneg (e x)
    rw [he'x, Prod.norm_mk, ← he2]
    refine max_le ?_ ?_
    · linarith
    · linarith
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := e) (f' := e') (δ := 0)
    (K := 1 + Q / 2) (ε := Q / 2 * (‖y 0‖ + ‖deriv y 0‖)) (a := 0) (b := 1)
    (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hder t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by rw [he0, norm_zero]) hbound 1 (right_mem_Icc.mpr zero_le_one)
  rw [gronwallBound_of_K_ne_0 (by positivity)] at hgr
  simp only [sub_zero, mul_one, zero_mul, zero_add] at hgr
  have hε' : 0 ≤ Q / 2 * (‖y 0‖ + ‖deriv y 0‖) := by positivity
  have hK1 : 1 ≤ 1 + Q / 2 := by linarith
  have hexp : Real.exp (1 + Q / 2) - 1 ≤ Real.exp (1 + Q) := by
    have := Real.exp_le_exp.mpr (by linarith : 1 + Q / 2 ≤ 1 + Q)
    linarith
  have hexp0 : 0 ≤ Real.exp (1 + Q / 2) - 1 := by
    have := Real.add_one_le_exp (1 + Q / 2)
    linarith
  have hfin : ‖e 1‖ ≤ Q / 2 * (‖y 0‖ + ‖deriv y 0‖) * Real.exp (1 + Q) :=
    hgr.trans (mul_le_mul (div_le_self hε' hK1) hexp hexp0 hε')
  have he1' : (e 1).1 = y z - (y 0 + deriv y 0 * z) := by
    rw [he]
    simp
  have hn1 : ‖(e 1).1‖ ≤ ‖e 1‖ := by rw [Prod.norm_def]; exact le_max_left _ _
  have hlast : 0 ≤ Q * (‖y 0‖ + ‖deriv y 0‖) * Real.exp (1 + Q) :=
    mul_nonneg (mul_nonneg hQ hM) (Real.exp_pos _).le
  rw [← he1']
  linarith

/-- Helper for `s09_len_bad` (Stage B, B1b, [GM X, proof of Lemma 4.3]): for `h` conformal on `𝔻`
and `F² = h'`, every `y = (α + β h)/F` solves `y'' = -(Sh/2) y`, with
`y' = β F - (α + β h) F'/F²` and `2 F F' = h''`. -/
theorem s09_bad_sol {h F : ℂ → ℂ} {Ω : Set ℂ} (hh : IsConformalOnto h unitDisc Ω)
    (hF : DifferentiableOn ℂ F unitDisc) (hFh : ∀ z ∈ unitDisc, F z ^ 2 = deriv h z) (α β : ℂ)
    {z : ℂ} (hz : z ∈ unitDisc) :
    deriv (fun w => (α + β * h w) / F w) z = β * F z - (α + β * h z) * deriv F z / F z ^ 2 ∧
      deriv (deriv fun w => (α + β * h w) / F w) z =
        -(schwarzian h z / 2) * ((α + β * h z) / F z) ∧
      2 * F z * deriv F z = deriv (deriv h) z := by
  have hzo : unitDisc ∈ 𝓝 z := isOpen_ball.mem_nhds hz
  have hFne : ∀ w ∈ unitDisc, F w ≠ 0 := by
    intro w hw h0
    apply deriv_ne_zero_of_injOn isOpen_ball hh.1 hh.2.1 hw
    rw [← hFh w hw, h0]
    ring
  have hFz := hFne z hz
  have hFd : ∀ w ∈ unitDisc, HasDerivAt F (deriv F w) w := fun w hw =>
    (hF.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
  have hF'd : ∀ w ∈ unitDisc, HasDerivAt (deriv F) (deriv (deriv F) w) w := fun w hw =>
    ((hF.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
  have hhd : ∀ w ∈ unitDisc, HasDerivAt h (deriv h w) w := fun w hw =>
    (hh.1.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
  have hsq : ∀ w ∈ unitDisc, HasDerivAt (fun v => F v ^ 2) (2 * F w * deriv F w) w := by
    intro w hw
    have h2 : HasDerivAt (fun v => F v * F v) (deriv F w * F w + F w * deriv F w) w :=
      (hFd w hw).mul (hFd w hw)
    have he : (fun v => F v ^ 2) = fun v => F v * F v := funext fun v => sq (F v)
    rw [he]
    exact h2.congr_deriv (by ring)
  -- `h' = F²` near each point, so `h'' = 2 F F'`
  have h3 : ∀ w ∈ unitDisc, 2 * F w * deriv F w = deriv (deriv h) w := by
    intro w hw
    have hev : deriv h =ᶠ[𝓝 w] fun v => F v ^ 2 := by
      filter_upwards [isOpen_ball.mem_nhds hw] with v hv
      exact (hFh v hv).symm
    rw [hev.deriv_eq, (hsq w hw).deriv]
  -- first derivative
  have hy1 : ∀ w ∈ unitDisc, HasDerivAt (fun v => (α + β * h v) / F v)
      (β * F w - (α + β * h w) * deriv F w / F w ^ 2) w := by
    intro w hw
    have hd : HasDerivAt (fun v => (α + β * h v) / F v) _ w :=
      ((hasDerivAt_const w α).add ((hhd w hw).const_mul β)).div (hFd w hw) (hFne w hw)
    refine hd.congr_deriv ?_
    simp only [Pi.add_apply]
    rw [← hFh w hw]
    field_simp [hFne w hw]
    ring
  refine ⟨(hy1 z hz).deriv, ?_, h3 z hz⟩
  -- second derivative
  have hev : deriv (fun v => (α + β * h v) / F v) =ᶠ[𝓝 z]
      fun v => β * F v - (α + β * h v) * deriv F v / F v ^ 2 := by
    filter_upwards [hzo] with v hv
    exact (hy1 v hv).deriv
  have hy2 : HasDerivAt (fun v => β * F v - (α + β * h v) * deriv F v / F v ^ 2) _ z :=
    ((hFd z hz).const_mul β).sub
      ((((hasDerivAt_const z α).add ((hhd z hz).const_mul β)).mul (hF'd z hz)).div
        (hsq z hz) (pow_ne_zero 2 hFz))
  -- the Schwarzian through `h''/h' = 2F'/F`
  have hS : schwarzian h z = 2 * deriv (deriv F) z / F z - 4 * deriv F z ^ 2 / F z ^ 2 := by
    rw [schwarzian_of_analyticAt (hh.1.analyticAt hzo)]
    have hpre : (fun w => deriv (deriv h) w / deriv h w) =ᶠ[𝓝 z]
        fun w => 2 * F w * deriv F w / F w ^ 2 := by
      filter_upwards [hzo] with w hw
      rw [← h3 w hw, ← hFh w hw]
    have hpd : HasDerivAt (fun w => 2 * F w * deriv F w / F w ^ 2) _ z :=
      (((hFd z hz).const_mul 2).mul (hF'd z hz)).div (hsq z hz) (pow_ne_zero 2 hFz)
    show deriv (fun w => deriv (deriv h) w / deriv h w) z -
        (1 / 2) * (deriv (deriv h) z / deriv h z) ^ 2 = _
    rw [hpre.deriv_eq, hpd.deriv, ← h3 z hz, ← hFh z hz]
    simp only [Pi.mul_apply]
    field_simp
    ring
  rw [hev.deriv_eq, hy2.deriv, hS, ← hFh z hz]
  simp only [Pi.add_apply, Pi.mul_apply]
  field_simp
  ring

/-- Helper for `s09_len_bad` (Stage B, B2, recentering at `u`): for `h = f ∘ σ`,
`σ(z) = (z + u)/(1 + ū z)`, the pre-Schwarzian at `0` is `(1-|u|²) f''/f'(u) - 2ū`, and the
invariant Schwarzian is carried over: `(1-|z|²)² |Sh(z)| = (1-|σz|²)² |Sf(σz)|`
(`schwarzian_mobius_comp`-type chain rule, `σ'(z)(1-|z|²) = 1-|σz|²`). -/
theorem s09_bad_rec {f : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω) {u : ℂ}
    (hu : u ∈ unitDisc) :
    deriv (deriv (f ∘ blaschke (-u))) 0 / deriv (f ∘ blaschke (-u)) 0 =
        ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) * (deriv (deriv f) u / deriv f u) - 2 * (starRingEnd ℂ) u ∧
      ∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzian (f ∘ blaschke (-u)) z‖ =
        (1 - ‖blaschke (-u) z‖ ^ 2) ^ 2 * ‖schwarzian f (blaschke (-u) z)‖ := by
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  have hnu : ‖-u‖ < 1 := by rwa [norm_neg]
  have hsu : (1 : ℝ) - ‖u‖ ^ 2 ≠ 0 :=
    (sub_pos.mpr (pow_lt_one₀ (norm_nonneg u) hu1 two_ne_zero)).ne'
  constructor
  · have hTeq : blaschke (-u) = fun ζ => (ζ + u) / (1 + (starRingEnd ℂ) u * ζ) := by
      rw [s05_blaschke_neg_eq u]
      funext ζ
      show (1 * ζ + u) / ((starRingEnd ℂ) u * ζ + 1) = (ζ + u) / (1 + (starRingEnd ℂ) u * ζ)
      rw [one_mul, add_comm ((starRingEnd ℂ) u * ζ) 1]
    rw [hTeq]
    have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
    have hs_eq : ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) = 1 - (starRingEnd ℂ) u * u := by
      rw [Complex.conj_mul']
      push_cast
      ring
    have hs0 : ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsu
    have hf'u : deriv f u ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hu
    have hTmaps := kb_d1_mapsTo hu1
    have hTd : ∀ ζ ∈ ball (0 : ℂ) 1, HasDerivAt (fun ζ => (ζ + u) / (1 + (starRingEnd ℂ) u * ζ))
        ((1 - (starRingEnd ℂ) u * u) / (1 + (starRingEnd ℂ) u * ζ) ^ 2) ζ := fun ζ hζ =>
      kb_d1_hasDerivAt_T u ζ (kb_d1_denom_ne_zero hu1 (mem_ball_zero_iff.1 hζ))
    have hT0 : ((0 : ℂ) + u) / (1 + (starRingEnd ℂ) u * 0) = u := by simp
    have hT'0 : (1 - (starRingEnd ℂ) u * u) / (1 + (starRingEnd ℂ) u * 0) ^ 2 =
        ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) := by
      rw [hs_eq]
      simp
    have hder : ∀ ζ ∈ ball (0 : ℂ) 1,
        HasDerivAt (f ∘ fun ζ => (ζ + u) / (1 + (starRingEnd ℂ) u * ζ))
          (deriv f ((ζ + u) / (1 + (starRingEnd ℂ) u * ζ)) *
            ((1 - (starRingEnd ℂ) u * u) / (1 + (starRingEnd ℂ) u * ζ) ^ 2)) ζ := by
      intro ζ hζ
      have hfT : HasDerivAt f (deriv f ((ζ + u) / (1 + (starRingEnd ℂ) u * ζ)))
          ((ζ + u) / (1 + (starRingEnd ℂ) u * ζ)) :=
        (hf.1.differentiableAt (isOpen_ball.mem_nhds (hTmaps hζ))).hasDerivAt
      exact hfT.comp ζ (hTd ζ hζ)
    have hev : deriv (f ∘ fun ζ => (ζ + u) / (1 + (starRingEnd ℂ) u * ζ)) =ᶠ[𝓝 0]
        fun ζ => deriv f ((ζ + u) / (1 + (starRingEnd ℂ) u * ζ)) *
          ((1 - (starRingEnd ℂ) u * u) / (1 + (starRingEnd ℂ) u * ζ) ^ 2) := by
      filter_upwards [isOpen_ball.mem_nhds h0mem] with ζ hζ
      exact (hder ζ hζ).deriv
    have hf'd : HasDerivAt (deriv f) (deriv (deriv f) u)
        (((0 : ℂ) + u) / (1 + (starRingEnd ℂ) u * 0)) := by
      rw [hT0]
      exact ((hf.1.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hu)).hasDerivAt
    have hc : HasDerivAt (fun ζ => deriv f ((ζ + u) / (1 + (starRingEnd ℂ) u * ζ)))
        (deriv (deriv f) u * ((1 - (starRingEnd ℂ) u * u) / (1 + (starRingEnd ℂ) u * 0) ^ 2)) 0 :=
      HasDerivAt.comp (h₂ := deriv f) (0 : ℂ) hf'd (hTd 0 h0mem)
    have hG : HasDerivAt (fun ζ => deriv f ((ζ + u) / (1 + (starRingEnd ℂ) u * ζ)) *
        ((1 - (starRingEnd ℂ) u * u) / (1 + (starRingEnd ℂ) u * ζ) ^ 2)) _ 0 :=
      hc.mul (kb_d1_hasDerivAt_T' u)
    rw [hev.deriv_eq, hG.deriv, (hder 0 h0mem).deriv]
    rw [hT0, hT'0, ← hs_eq]
    field_simp
    ring
  · intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hσ1 := blaschke_mem_unitDisc hnu hz1
    have hσD : blaschke (-u) z ∈ unitDisc := mem_ball_zero_iff.mpr hσ1
    have hBA : AnalyticAt ℂ (blaschke (-u)) z :=
      (differentiableOn_blaschke hnu).analyticAt (isOpen_ball.mem_nhds hz)
    have hnd := s05_norm_deriv_blaschke_neg hu1 hz1
    have hpos : 0 < 1 - ‖blaschke (-u) z‖ ^ 2 :=
      sub_pos.mpr (pow_lt_one₀ (norm_nonneg _) hσ1 two_ne_zero)
    have hB' : deriv (blaschke (-u)) z ≠ 0 := by
      intro h0
      rw [h0, norm_zero, zero_mul] at hnd
      linarith
    have hfA : AnalyticAt ℂ f (blaschke (-u) z) := hf.1.analyticAt (isOpen_ball.mem_nhds hσD)
    have hf' : deriv f (blaschke (-u) z) ≠ 0 :=
      deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hσD
    have hchain := eq19_1_chain_rule hBA hB' hfA hf'
    have hS0 : schwarzian (blaschke (-u)) z = 0 := by
      rw [s05_blaschke_neg_eq u]
      apply schwarzian_mobius
      rw [Complex.mul_conj', one_mul]
      exact_mod_cast hsu
    rw [hchain, hS0, add_zero, norm_mul, norm_pow, ← hnd]
    ring

/-- Helper for `s09_len_bad` (Stage B, B2, Möbius identities): for `σ(z) = (z + u)/(1 + ū z)`,
`σ(𝔻) ⊆ 𝔻`, `σz - u = z (1 - ū σz)` (so `σ(b𝔻)` is the pseudo-hyperbolic disc of radius `b`
about `u`) and `|u - σz| |1 + ū z| = (1-|u|²)|z|`. -/
theorem s09_bad_mob {u z : ℂ} (hu : ‖u‖ < 1) (hz : ‖z‖ < 1) :
    ‖blaschke (-u) z‖ < 1 ∧
      ‖blaschke (-u) z - u‖ = ‖z‖ * ‖1 - (starRingEnd ℂ) u * blaschke (-u) z‖ ∧
      ‖u - blaschke (-u) z‖ * ‖1 + (starRingEnd ℂ) u * z‖ = (1 - ‖u‖ ^ 2) * ‖z‖ := by
  have hnu : ‖-u‖ < 1 := by rwa [norm_neg]
  have hden : 1 + (starRingEnd ℂ) u * z ≠ 0 := kb_d1_denom_ne_zero hu hz
  have hden' : 1 + z * (starRingEnd ℂ) u ≠ 0 := by rwa [mul_comm]
  have hb : blaschke (-u) z = (z + u) / (1 + (starRingEnd ℂ) u * z) := by
    rw [s05_blaschke_neg_eq u]
    show (1 * z + u) / ((starRingEnd ℂ) u * z + 1) = _
    rw [one_mul, add_comm ((starRingEnd ℂ) u * z) 1]
  have hid : blaschke (-u) z - u = z * (1 - (starRingEnd ℂ) u * blaschke (-u) z) := by
    rw [hb]
    field_simp
    ring
  have hid2 : (u - blaschke (-u) z) * (1 + (starRingEnd ℂ) u * z) =
      -(z * (1 - (starRingEnd ℂ) u * u)) := by
    rw [hb]
    field_simp
    ring
  have hnn : ‖1 - (starRingEnd ℂ) u * u‖ = 1 - ‖u‖ ^ 2 := by
    rw [Complex.conj_mul', show (1 : ℂ) - (‖u‖ : ℂ) ^ 2 = ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg
        (sub_pos.mpr (pow_lt_one₀ (norm_nonneg u) hu two_ne_zero)).le]
  refine ⟨blaschke_mem_unitDisc hnu hz, ?_, ?_⟩
  · rw [hid, norm_mul]
  · have := congrArg norm hid2
    rw [norm_mul, norm_neg, norm_mul, hnn] at this
    rw [this, mul_comm]

/-- Helper for `s09_len_bad` (Stage B, B3, wall; GM's "(VII.2.5) for `φ(∂B)`" read as quasisymmetry
of the extension): a corkscrew-normalized Riemann map of a `K`-quasidisc is quasisymmetric on `𝔻`
with `η(t) = C max(t^{1/Q}, t^Q)`. Route: `F⁻¹ ∘ f` is a `K`-q.c. self-map of `𝔻` whose value at `0`
is `c`-deep (quasisymmetry of `F⁻¹`); move it to `0` by a q.c. self-map of the plane preserving
`𝔻` (constant depending on `K, c`), reflect across `∂𝔻`, compose with `F`: a q.c. homeomorphism of
`ℂ` extending `f`, then `lem_three_point`, whose conclusion for a `Q`-q.c. homeomorphism `F` of
`ℂ` reads `‖F a - F b‖ / ‖F a - F c‖ ≤ C * max ((‖a - b‖ / ‖a - c‖) ^ (1 / Q))
((‖a - b‖ / ‖a - c‖) ^ Q)` (and the same for `F⁻¹` at `F a, F b, F c`). Without the corkscrew
normalization this is false (`f(z) = (z + a)/(1 + az)`, `a → 1`). -/
theorem s09_bad_qs (K : ℝ) (hK : 1 ≤ K) (c : ℝ) (hc : 0 < c) :
    ∃ C Q : ℝ, 0 < C ∧ 1 ≤ Q ∧ ∀ (Ω Ωs : Set ℂ) (f : ℂ → ℂ), IsBoundedKQuasicircle Ω Ωs K →
      IsConformalOnto f unitDisc Ω →
      c * Metric.diam (curveOf Ω Ωs) ≤ infDist (f 0) (curveOf Ω Ωs) →
      ∀ a ∈ unitDisc, ∀ b ∈ unitDisc, ∀ d ∈ unitDisc, a ≠ d →
        ‖f a - f b‖ / ‖f a - f d‖ ≤
          C * max ((‖a - b‖ / ‖a - d‖) ^ (1 / Q)) ((‖a - b‖ / ‖a - d‖) ^ Q) := by
  sorry

/-- Helper for `s09_len_bad` (Stage B, assembly arithmetic): the final comparison of the two
image distances against the quasisymmetry bound `ε/1280`. -/
theorem s09_bad_ar {ε κ τ y1b dB y1c dC : ℝ} (hε : 0 < ε) (hκ : κ ≤ ε / 48) (hκ4 : κ ≤ 1 / 4)
    (hκ0 : 0 ≤ κ) (hτ : τ ≤ ε / 240) (hτ0 : 0 ≤ τ) (hε6 : ε ≤ 6) (hy1b : 1 - κ - τ ≤ y1b)
    (hdB : dB ≤ 5 + 5 * τ) (hy1c : y1c ≤ 1 + τ) (hy1c0 : 0 ≤ y1c)
    (hdC : (1 - κ) * ε / 2 - 2 * κ - 5 * τ ≤ dC) :
    ε / 1280 * (y1c * dB) < y1b * dC := by
  -- `hκ0` is not needed (the upper bounds on `κ` suffice); the statement stays true without it.
  have _h := hκ0
  have hτ1 : τ ≤ 1 / 40 := by linarith
  have hκε2 : κ * ε ≤ 1 / 4 * ε := mul_le_mul_of_nonneg_right hκ4 hε.le
  have hdC' : 5 * ε / 16 ≤ dC := by linarith
  have hy1b' : 29 / 40 ≤ y1b := by linarith
  have h1 : 29 / 40 * (5 * ε / 16) ≤ y1b * dC :=
    mul_le_mul hy1b' hdC' (by positivity) (by linarith)
  have h2 : y1c * dB ≤ y1c * (5 + 5 * τ) := mul_le_mul_of_nonneg_left hdB hy1c0
  have h3 : y1c * (5 + 5 * τ) ≤ (1 + τ) * (5 + 5 * τ) :=
    mul_le_mul_of_nonneg_right hy1c (by linarith)
  have h4 : (1 + τ) * (5 + 5 * τ) ≤ 6 := by nlinarith
  have h5 : ε / 1280 * (y1c * dB) ≤ ε / 1280 * 6 :=
    mul_le_mul_of_nonneg_left (h2.trans (h3.trans h4)) (by positivity)
  linarith

/-- Helper for `s09_len_bad` (Stage B, assembly): the Schwarzian of `f ∘ σ` is `≤ m` on
`|z| ≤ 1 - κ` when the invariant Schwarzian of `f` is `< (1-(1-κ)²)² m` on the pseudo-hyperbolic
disc of radius `1 - κ/2` about `u` (`s09_bad_rec`, `s09_bad_mob`). -/
theorem s09_bad_sb {f : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω) {u : ℂ}
    (hu : u ∈ unitDisc) {κ m : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hS : ∀ w ∈ unitDisc, ‖w - u‖ < (1 - κ / 2) * ‖1 - (starRingEnd ℂ) u * w‖ →
      (1 - ‖w‖ ^ 2) ^ 2 * ‖schwarzian f w‖ < (1 - (1 - κ) ^ 2) ^ 2 * m)
    {z : ℂ} (hz : ‖z‖ ≤ 1 - κ) : ‖schwarzian (f ∘ blaschke (-u)) z‖ ≤ m := by
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  have hz1 : ‖z‖ < 1 := by linarith
  have hr2 : 0 < 1 - (1 - κ) ^ 2 :=
    sub_pos.mpr (pow_lt_one₀ (by linarith) (by linarith) two_ne_zero)
  obtain ⟨hσ1, hσu, -⟩ := s09_bad_mob hu1 hz1
  have hσD : blaschke (-u) z ∈ unitDisc := mem_ball_zero_iff.mpr hσ1
  have hpos : 0 < ‖1 - (starRingEnd ℂ) u * blaschke (-u) z‖ := by
    have h1 : ‖(starRingEnd ℂ) u * blaschke (-u) z‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      calc ‖u‖ * ‖blaschke (-u) z‖ ≤ 1 * ‖blaschke (-u) z‖ :=
            mul_le_mul_of_nonneg_right hu1.le (norm_nonneg _)
        _ < 1 := by rw [one_mul]; exact hσ1
    have := norm_sub_norm_le (1 : ℂ) ((starRingEnd ℂ) u * blaschke (-u) z)
    rw [norm_one] at this
    linarith
  have hin : ‖blaschke (-u) z - u‖ < (1 - κ / 2) * ‖1 - (starRingEnd ℂ) u * blaschke (-u) z‖ := by
    rw [hσu]
    exact mul_lt_mul_of_pos_right (by linarith) hpos
  have hlt := hS _ hσD hin
  rw [← (s09_bad_rec hf hu).2 z (mem_ball_zero_iff.mpr hz1)] at hlt
  have hz2 : (1 - (1 - κ) ^ 2) ^ 2 ≤ (1 - ‖z‖ ^ 2) ^ 2 := by
    have : ‖z‖ ^ 2 ≤ (1 - κ) ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
    exact pow_le_pow_left₀ hr2.le (by linarith) 2
  have hlt' : (1 - (1 - κ) ^ 2) ^ 2 * ‖schwarzian (f ∘ blaschke (-u)) z‖ <
      (1 - (1 - κ) ^ 2) ^ 2 * m :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hz2 (norm_nonneg _)) hlt
  exact (lt_of_mul_lt_mul_left hlt' (pow_pos hr2 2).le).le

/-- Helper for `s09_len_bad` (Stage B, assembly): the normalized solutions
`Y₁ = (h - h(0))/(F(0) F)` and `Y₂ = (F(0) + γ (h - h(0)))/F`, `γ = F'(0)/F(0)²`, stay within
`m e^{1+m}` of `z` and `1` on `|z| ≤ r` (`s09_bad_sol`, `s09_bad_ode`). -/
theorem s09_bad_yy {h F : ℂ → ℂ} {Ω : Set ℂ} (hh : IsConformalOnto h unitDisc Ω)
    (hFd : DifferentiableOn ℂ F unitDisc) (hF2 : ∀ z ∈ unitDisc, F z ^ 2 = deriv h z)
    (hFne : ∀ z ∈ unitDisc, F z ≠ 0) {r m : ℝ} (hr : r < 1) (hm : 0 ≤ m)
    (hSb : ∀ z : ℂ, ‖z‖ ≤ r → ‖schwarzian h z‖ ≤ m) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖(-h 0 / F 0 + 1 / F 0 * h z) / F z - z‖ ≤ m * Real.exp (1 + m) ∧
      ‖(F 0 - deriv F 0 / F 0 ^ 2 * h 0 + deriv F 0 / F 0 ^ 2 * h z) / F z - 1‖ ≤
        m * Real.exp (1 + m) := by
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hF0 := hFne 0 h0D
  have hdiff : ∀ α β : ℂ, DifferentiableOn ℂ (fun w => (α + β * h w) / F w) unitDisc :=
    fun α β => ((differentiableOn_const α).add ((differentiableOn_const β).mul hh.1)).div hFd hFne
  have hsol := fun (α β : ℂ) (w : ℂ) (hw : w ∈ unitDisc) => s09_bad_sol hh hFd hF2 α β hw
  constructor
  · have hode := s09_bad_ode hr hm (hdiff (-h 0 / F 0) (1 / F 0))
      (fun w hw => (hsol _ _ w hw).2.1) hSb hz
    have hv0 : (-h 0 / F 0 + 1 / F 0 * h 0) / F 0 = 0 := by ring
    have hd0 : deriv (fun w => (-h 0 / F 0 + 1 / F 0 * h w) / F w) 0 = 1 := by
      rw [(hsol (-h 0 / F 0) (1 / F 0) 0 h0D).1]
      field_simp
      ring
    simp only [hv0, hd0, zero_add, one_mul, norm_zero, norm_one] at hode
    exact hode
  · have hode := s09_bad_ode hr hm (hdiff (F 0 - deriv F 0 / F 0 ^ 2 * h 0) (deriv F 0 / F 0 ^ 2))
      (fun w hw => (hsol _ _ w hw).2.1) hSb hz
    have hv0 : (F 0 - deriv F 0 / F 0 ^ 2 * h 0 + deriv F 0 / F 0 ^ 2 * h 0) / F 0 = 1 := by
      rw [sub_add_cancel, div_self hF0]
    have hd0 : deriv (fun w => (F 0 - deriv F 0 / F 0 ^ 2 * h 0 + deriv F 0 / F 0 ^ 2 * h w) / F w)
        0 = 0 := by
      rw [(hsol (F 0 - deriv F 0 / F 0 ^ 2 * h 0) (deriv F 0 / F 0 ^ 2) 0 h0D).1, sub_add_cancel]
      field_simp
      ring
    simp only [hv0, hd0, zero_mul, add_zero, norm_zero, norm_one, one_mul] at hode
    exact hode

/-- Helper for `s09_len_bad` (Stage B, assembly algebra): `(h - h(0)) (Y₂ - a Y₁) = F(0)² Y₁`
with `a = F'(0)/F(0)` (`Y₂ - a Y₁ = F(0)/F`). -/
theorem s09_bad_alg {h0 hz F0 F1 Fz : ℂ} (hF0 : F0 ≠ 0) (hFz : Fz ≠ 0) :
    (hz - h0) * ((F0 - F1 / F0 ^ 2 * h0 + F1 / F0 ^ 2 * hz) / Fz -
        F1 / F0 * ((-h0 / F0 + 1 / F0 * hz) / Fz)) =
      F0 ^ 2 * ((-h0 / F0 + 1 / F0 * hz) / Fz) := by
  field_simp
  ring

/-- Helper for `s09_len_bad` (Stage B, assembly geometry): `z_b = (1-κ) u/|u|` has `|z_b| = 1-κ`,
`ū z_b = (1-κ)|u|`, and `|u - σ z_b| ≤ (1 - (1-κ)|u|) |u - σ(-z_b)|` with `u ≠ σ(-z_b)`. -/
theorem s09_bad_pt {u : ℂ} {κ : ℝ} (hκ4 : κ ≤ 1 / 4) (hu : 1 - κ < ‖u‖)
    (hu1 : ‖u‖ < 1) :
    ‖(((1 - κ) / ‖u‖ : ℝ) : ℂ) * u‖ = 1 - κ ∧
      (starRingEnd ℂ) u * ((((1 - κ) / ‖u‖ : ℝ) : ℂ) * u) = (((1 - κ) * ‖u‖ : ℝ) : ℂ) ∧
      0 < ‖u - blaschke (-u) (-((((1 - κ) / ‖u‖ : ℝ) : ℂ) * u))‖ ∧
      ‖u - blaschke (-u) ((((1 - κ) / ‖u‖ : ℝ) : ℂ) * u)‖ ≤
        (1 - (1 - κ) * ‖u‖) * ‖u - blaschke (-u) (-((((1 - κ) / ‖u‖ : ℝ) : ℂ) * u))‖ := by
  obtain ⟨zb, hzb⟩ : ∃ z : ℂ, z = (((1 - κ) / ‖u‖ : ℝ) : ℂ) * u := ⟨_, rfl⟩
  rw [← hzb]
  have hu0 : 0 < ‖u‖ := by linarith
  have hzbn : ‖zb‖ = 1 - κ := by
    rw [hzb, norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (by linarith) hu0.le),
      div_mul_cancel₀ _ hu0.ne']
  have hcz : (starRingEnd ℂ) u * zb = (((1 - κ) * ‖u‖ : ℝ) : ℂ) := by
    rw [hzb, mul_left_comm, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    congr 1
    rw [pow_two, ← mul_assoc, div_mul_cancel₀ _ hu0.ne']
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (1 - κ) * ‖u‖ := ⟨_, rfl⟩
  rw [← hp] at hcz ⊢
  have hp1 : p ≤ 1 := by
    rw [hp]
    calc (1 - κ) * ‖u‖ ≤ 1 * 1 := mul_le_mul (by linarith) hu1.le hu0.le (by norm_num)
      _ = 1 := one_mul 1
  have hp0 : 0 ≤ p := by rw [hp]; exact mul_nonneg (by linarith) hu0.le
  have hp1' : p < 1 := by
    rw [hp]
    calc (1 - κ) * ‖u‖ < 1 * 1 := mul_lt_mul' (by linarith) hu1 hu0.le one_pos
      _ = 1 := one_mul 1
  obtain ⟨-, -, hmb⟩ := s09_bad_mob (u := u) (z := zb) hu1 (by linarith)
  obtain ⟨-, -, hmc⟩ := s09_bad_mob (u := u) (z := -zb) hu1 (by rw [norm_neg]; linarith)
  rw [hcz] at hmb
  rw [mul_neg, hcz, ← sub_eq_add_neg] at hmc
  have hnb : ‖(1 : ℂ) + p‖ = 1 + p := by
    rw [show (1 : ℂ) + p = ((1 + p : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have hnc : ‖(1 : ℂ) - p‖ = 1 - p := by
    rw [show (1 : ℂ) - p = ((1 - p : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [hnb, hzbn] at hmb
  rw [hnc, norm_neg, hzbn] at hmc
  have hX : 0 < (1 - ‖u‖ ^ 2) * (1 - κ) := by
    have : ‖u‖ ^ 2 < 1 := pow_lt_one₀ hu0.le hu1 two_ne_zero
    exact mul_pos (by linarith) (by linarith)
  have hdc : 0 < ‖u - blaschke (-u) (-zb)‖ := by
    rcases (norm_nonneg (u - blaschke (-u) (-zb))).lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0, zero_mul] at hmc
      linarith
  refine ⟨hzbn, hcz, hdc, ?_⟩
  have hb0 := norm_nonneg (u - blaschke (-u) zb)
  calc ‖u - blaschke (-u) zb‖ ≤ ‖u - blaschke (-u) zb‖ * (1 + p) :=
        le_mul_of_one_le_right hb0 (by linarith)
    _ = (1 - p) * ‖u - blaschke (-u) (-zb)‖ := by rw [hmb, ← hmc, mul_comm]

/-- Helper for `s09_len_bad` (Stage B, assembly linear terms): with `a = V/2 - ū`, `ū z_b = p`,
`|z_b| = 1-κ` and `ε ≤ |V| ≤ 6`: `|a| ≤ 4`, `|1 - a z_b| ≤ 5`, `|1 + a z_b| ≥ ε(1-κ)/2 - (1-p)`. -/
theorem s09_bad_lin {a V u zb : ℂ} {p ε κ : ℝ} (ha : a = V / 2 - (starRingEnd ℂ) u)
    (hcz : (starRingEnd ℂ) u * zb = (p : ℂ)) (hzb : ‖zb‖ = 1 - κ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hVε : ε ≤ ‖V‖) (hV6 : ‖V‖ ≤ 6) (hu1 : ‖u‖ ≤ 1) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    ‖a‖ ≤ 4 ∧ ‖1 - a * zb‖ ≤ 5 ∧ ε * (1 - κ) / 2 - (1 - p) ≤ ‖1 - a * -zb‖ := by
  have hnb : ‖(1 : ℂ) + p‖ = 1 + p := by
    rw [show (1 : ℂ) + p = ((1 + p : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have hnc : ‖(1 : ℂ) - p‖ = 1 - p := by
    rw [show (1 : ℂ) - p = ((1 - p : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hVz : ‖V / 2 * zb‖ = ‖V‖ * (1 - κ) / 2 := by
    rw [norm_mul, norm_div, hzb, h2n]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [ha]
    have h1 := norm_sub_le (V / 2) ((starRingEnd ℂ) u)
    rw [norm_div, Complex.norm_conj, h2n] at h1
    linarith
  · rw [ha, sub_mul, hcz, show (1 : ℂ) - (V / 2 * zb - p) = (1 + p) - V / 2 * zb by ring]
    have h1 := norm_sub_le ((1 : ℂ) + p) (V / 2 * zb)
    rw [hnb, hVz] at h1
    have : ‖V‖ * (1 - κ) ≤ 6 * 1 := mul_le_mul hV6 (by linarith) (by linarith) (by norm_num)
    linarith
  · rw [ha, mul_neg, sub_mul, hcz,
      show (1 : ℂ) - -(V / 2 * zb - p) = V / 2 * zb + (1 - p) by ring]
    have h1 := norm_sub_norm_le (V / 2 * zb) (-((1 : ℂ) - p))
    rw [sub_neg_eq_add, norm_neg, hnc, hVz] at h1
    have : ε * (1 - κ) ≤ ‖V‖ * (1 - κ) := mul_le_mul_of_nonneg_right hVε (by linarith)
    linarith

/-- Helper for `s09_len_bad` (Stage B, assembly): `|(y₂ - a y₁) - (1 - a z)| ≤ 5τ` when `|a| ≤ 4`,
`|y₁ - z| ≤ τ`, `|y₂ - 1| ≤ τ`. -/
theorem s09_bad_dd {a y1 y2 z : ℂ} {τ : ℝ} (ha : ‖a‖ ≤ 4) (h1 : ‖y1 - z‖ ≤ τ)
    (h2 : ‖y2 - 1‖ ≤ τ) : ‖(y2 - a * y1) - (1 - a * z)‖ ≤ 5 * τ := by
  rw [show (y2 - a * y1) - (1 - a * z) = (y2 - 1) - a * (y1 - z) by ring]
  have h3 := norm_sub_le (y2 - 1) (a * (y1 - z))
  rw [norm_mul] at h3
  have h4 : ‖a‖ * ‖y1 - z‖ ≤ 4 * τ := mul_le_mul ha h1 (norm_nonneg _) (by norm_num)
  linarith

/-- Helper for `lem_length` (Stage B stub, S4, [GM X, Lemma 6.3 and (6.9)–(6.10)]): for a
`K`-quasidisc and `f(0)` a corkscrew point (`c δ ≤ dist(f 0, Γ)`), a point `u` with
`|g'(u)|(1-|u|²) ≥ ε` near which the Schwarzian is small (`(1-|w|²)²|Sf(w)| < δ` for
`|w - u| < b |1 - ū w|`) lies in `|u| ≤ 1 - η` (near-Möbius approximation [GM X, Lemma 4.3], the
three-point condition for `f`(circles) and the pole estimate (4.10)). -/
theorem s09_len_bad (K : ℝ) (hK : 1 ≤ K) (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) :
    ∃ b δ η : ℝ, 0 < b ∧ b < 1 ∧ 0 < δ ∧ 0 < η ∧
      ∀ (Ω Ωs : Set ℂ) (f : ℂ → ℂ), IsBoundedKQuasicircle Ω Ωs K →
        IsConformalOnto f unitDisc Ω →
        c * Metric.diam (curveOf Ω Ωs) ≤ infDist (f 0) (curveOf Ω Ωs) →
        ∀ u ∈ unitDisc, ε ≤ (1 - ‖u‖ ^ 2) * ‖deriv (deriv f) u / deriv f u‖ →
          (∀ w ∈ unitDisc, ‖w - u‖ < b * ‖1 - (starRingEnd ℂ) u * w‖ →
            (1 - ‖w‖ ^ 2) ^ 2 * ‖schwarzian f w‖ < δ) →
          ‖u‖ ≤ 1 - η := by
  obtain ⟨C, Q, hC, hQ1, hqs⟩ := s09_bad_qs K hK c hc
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (ε / (1280 * C)) ^ Q := ⟨_, rfl⟩
  have hεC : 0 < ε / (1280 * C) := by positivity
  have hs0 : 0 < s := by rw [hs]; exact Real.rpow_pos_of_pos hεC Q
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = min (min (ε / 48) (s / 2)) (1 / 4) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by
    rw [hκ]; exact lt_min (lt_min (by positivity) (by positivity)) (by norm_num)
  have hκε : κ ≤ ε / 48 := by rw [hκ]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hκs : κ ≤ s / 2 := by rw [hκ]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hκ4 : κ ≤ 1 / 4 := by rw [hκ]; exact min_le_right _ _
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = min 1 (ε / (240 * Real.exp 2)) := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; exact lt_min one_pos (by positivity)
  have hm1 : m ≤ 1 := by rw [hm]; exact min_le_left _ _
  have hmε : m ≤ ε / (240 * Real.exp 2) := by rw [hm]; exact min_le_right _ _
  have hr2 : 0 < 1 - (1 - κ) ^ 2 :=
    sub_pos.mpr (pow_lt_one₀ (by linarith) (by linarith) two_ne_zero)
  refine ⟨1 - κ / 2, (1 - (1 - κ) ^ 2) ^ 2 * m, κ, by linarith, by linarith, mul_pos (pow_pos hr2 2) hm0, hκ0, ?_⟩
  intro Ω Ωs f hΩ hf hnorm u hu hεu hSf
  by_contra hcon
  have hcon' : 1 - κ < ‖u‖ := lt_of_not_ge hcon
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  -- the Schwarzian of `h = f ∘ σ` on `|z| ≤ 1 - κ`
  have hSb := fun z (hz : ‖z‖ ≤ 1 - κ) => s09_bad_sb hf hu hκ0 (by linarith) hSf hz
  -- recentering: `h 0 = f u`, `h''/h'(0) = V - 2ū`
  obtain ⟨hh, hh0, -⟩ := s02_disc_recenter hf hu
  have hA := (s09_bad_rec hf hu).1
  obtain ⟨h, hhd⟩ : ∃ g : ℂ → ℂ, g = f ∘ blaschke (-u) := ⟨_, rfl⟩
  rw [← hhd] at hh hh0 hA hSb
  have hhz : ∀ z, h z = f (blaschke (-u) z) := fun z => by rw [hhd]; rfl
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  obtain ⟨F, hFd, hF2⟩ := s09_len_sqrt hh
  have hFne : ∀ z ∈ unitDisc, F z ≠ 0 := by
    intro z hz h0
    apply deriv_ne_zero_of_injOn isOpen_ball hh.1 hh.2.1 hz
    rw [← hF2 z hz, h0]
    ring
  have hF0 := hFne 0 h0D
  -- Gronwall: `|Y1 z - z| ≤ τ`, `|Y2 z - 1| ≤ τ` on `|z| ≤ 1 - κ`
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = m * Real.exp (1 + m) := ⟨_, rfl⟩
  have hτ0 : 0 ≤ τ := by rw [hτ]; exact mul_nonneg hm0.le (Real.exp_pos _).le
  have hτε : τ ≤ ε / 240 := by
    have he : Real.exp (1 + m) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
    have he0 : 0 < Real.exp 2 := Real.exp_pos 2
    calc τ ≤ ε / (240 * Real.exp 2) * Real.exp 2 :=
          by rw [hτ]; exact mul_le_mul hmε he (Real.exp_pos _).le (by positivity)
      _ = ε / 240 := by field_simp
  have hYY := fun z (hz : ‖z‖ ≤ 1 - κ) =>
    s09_bad_yy hh hFd hF2 hFne (by linarith : 1 - κ < 1) hm0.le hSb hz
  rw [← hτ] at hYY
  obtain ⟨Y1, hY1⟩ : ∃ y : ℂ → ℂ, y = fun w => (-h 0 / F 0 + 1 / F 0 * h w) / F w := ⟨_, rfl⟩
  obtain ⟨Y2, hY2⟩ : ∃ y : ℂ → ℂ,
      y = fun w => (F 0 - deriv F 0 / F 0 ^ 2 * h 0 + deriv F 0 / F 0 ^ 2 * h w) / F w := ⟨_, rfl⟩
  have hY1z : ∀ z : ℂ, ‖z‖ ≤ 1 - κ → ‖Y1 z - z‖ ≤ τ := fun z hz => by rw [hY1]; exact (hYY z hz).1
  have hY2z : ∀ z : ℂ, ‖z‖ ≤ 1 - κ → ‖Y2 z - 1‖ ≤ τ := fun z hz => by rw [hY2]; exact (hYY z hz).2
  have hprod : ∀ z ∈ unitDisc, (h z - h 0) * (Y2 z - deriv F 0 / F 0 * Y1 z) = F 0 ^ 2 * Y1 z :=
    fun z hz => by rw [hY1, hY2]; exact s09_bad_alg hF0 (hFne z hz)
  -- `a = F'(0)/F(0) = V/2 - ū`, `ε ≤ |V| ≤ 6`
  obtain ⟨V, hV⟩ : ∃ V : ℂ, V = ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) * (deriv (deriv f) u / deriv f u) :=
    ⟨_, rfl⟩
  have hVn : ‖V‖ = (1 - ‖u‖ ^ 2) * ‖deriv (deriv f) u / deriv f u‖ := by
    have : ‖u‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg u) hu1 two_ne_zero
    rw [hV, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hVε : ε ≤ ‖V‖ := by rw [hVn]; exact hεu
  have hV6 : ‖V‖ ≤ 6 := by rw [hVn]; exact s02_sw_bloch hf hu
  have ha : deriv F 0 / F 0 = V / 2 - (starRingEnd ℂ) u := by
    have h3 := (s09_bad_sol hh hFd hF2 0 1 h0D).2.2
    rw [← hV, ← h3, ← hF2 0 h0D] at hA
    have hV' : V = 2 * F 0 * deriv F 0 / F 0 ^ 2 + 2 * (starRingEnd ℂ) u := by
      rw [hA]
      ring
    rw [hV']
    field_simp
    ring
  -- the two points `z_b`, `-z_b`
  obtain ⟨hzbn, hcz, hdc, htb⟩ := s09_bad_pt hκ4 hcon' hu1
  obtain ⟨zb, hzb⟩ : ∃ z : ℂ, z = (((1 - κ) / ‖u‖ : ℝ) : ℂ) * u := ⟨_, rfl⟩
  rw [← hzb] at hzbn hcz hdc htb
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (1 - κ) * ‖u‖ := ⟨_, rfl⟩
  rw [← hp] at hcz htb
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
  have hp0 : 0 ≤ p := by rw [hp]; exact mul_nonneg (by linarith) hu0
  have hp1 : p ≤ 1 := by
    rw [hp]
    calc (1 - κ) * ‖u‖ ≤ 1 * 1 := mul_le_mul (by linarith) hu1.le hu0 (by norm_num)
      _ = 1 := one_mul 1
  have hp2 : 1 - p ≤ 2 * κ := by
    have h1 : (1 - κ) * (1 - κ) ≤ p := by
      rw [hp]; exact mul_le_mul_of_nonneg_left hcon'.le (by linarith)
    have h2 : (1 - κ) * (1 - κ) = 1 - 2 * κ + κ * κ := by ring
    have h3 : 0 ≤ κ * κ := mul_self_nonneg κ
    linarith
  have hzcn : ‖-zb‖ = 1 - κ := by rw [norm_neg, hzbn]
  have hzbD : zb ∈ unitDisc := mem_ball_zero_iff.mpr (by linarith)
  have hzcD : -zb ∈ unitDisc := mem_ball_zero_iff.mpr (by linarith)
  obtain ⟨ha4, hlb, hlc⟩ := s09_bad_lin ha hcz hzbn hp0 hp1 hVε hV6 hu1.le hκ0.le (by linarith)
  -- quasisymmetry at `(u, σ z_b, σ(-z_b))`
  have hσbD : blaschke (-u) zb ∈ unitDisc :=
    mem_ball_zero_iff.mpr (s09_bad_mob hu1 (by linarith : ‖zb‖ < 1)).1
  have hσcD : blaschke (-u) (-zb) ∈ unitDisc :=
    mem_ball_zero_iff.mpr (s09_bad_mob hu1 (by linarith : ‖-zb‖ < 1)).1
  have hne : u ≠ blaschke (-u) (-zb) := fun he => by
    rw [← he, sub_self, norm_zero] at hdc
    exact lt_irrefl 0 hdc
  have hq := hqs Ω Ωs f hΩ hf hnorm u hu _ hσbD _ hσcD hne
  rw [← hhz, ← hhz, ← hh0] at hq
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ‖u - blaschke (-u) zb‖ / ‖u - blaschke (-u) (-zb)‖ := ⟨_, rfl⟩
  rw [← ht] at hq
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg (norm_nonneg _) hdc.le
  have hts : t ≤ min 1 s := by
    rw [ht, div_le_iff₀ hdc]
    refine htb.trans (mul_le_mul_of_nonneg_right (le_min (by linarith) (by linarith)) hdc.le)
  have hQ0 : 0 < Q := by linarith
  have hmax : C * max (t ^ (1 / Q)) (t ^ Q) ≤ ε / 1280 := by
    have h1 : t ^ Q ≤ t ^ (1 / Q) :=
      Real.rpow_le_rpow_of_exponent_ge' ht0 (hts.trans (min_le_left _ _)) (by positivity)
        (by rw [div_le_iff₀ hQ0]; exact one_le_mul_of_one_le_of_one_le hQ1 hQ1)
    have h2 : t ^ (1 / Q) ≤ ε / (1280 * C) := by
      calc t ^ (1 / Q) ≤ s ^ (1 / Q) :=
            Real.rpow_le_rpow ht0 (hts.trans (min_le_right _ _)) (by positivity)
        _ = ε / (1280 * C) := by rw [hs, one_div, Real.rpow_rpow_inv hεC.le hQ0.ne']
    rw [max_eq_left h1]
    calc C * t ^ (1 / Q) ≤ C * (ε / (1280 * C)) := mul_le_mul_of_nonneg_left h2 hC.le
      _ = ε / 1280 := by field_simp
  have hhc : 0 < ‖h 0 - h (-zb)‖ := by
    refine norm_pos_iff.mpr (sub_ne_zero.mpr fun he => ?_)
    have := hh.2.1 h0D hzcD he
    rw [← this, norm_zero] at hzcn
    linarith
  have hratio : ‖h zb - h 0‖ ≤ ε / 1280 * ‖h (-zb) - h 0‖ := by
    rw [norm_sub_rev (h zb), norm_sub_rev (h (-zb))]
    exact (div_le_iff₀ hhc).mp (hq.trans hmax)
  -- bounds at the two points
  have hdb := s09_bad_dd ha4 (hY1z zb hzbn.le) (hY2z zb hzbn.le)
  have hdcc := s09_bad_dd ha4 (hY1z (-zb) hzcn.le) (hY2z (-zb) hzcn.le)
  have hdB : ‖Y2 zb - deriv F 0 / F 0 * Y1 zb‖ ≤ 5 + 5 * τ := by
    have := norm_le_insert' (Y2 zb - deriv F 0 / F 0 * Y1 zb) (1 - deriv F 0 / F 0 * zb)
    linarith
  have hdC : (1 - κ) * ε / 2 - 2 * κ - 5 * τ ≤ ‖Y2 (-zb) - deriv F 0 / F 0 * Y1 (-zb)‖ := by
    have := norm_sub_norm_le (1 - deriv F 0 / F 0 * -zb) (1 - deriv F 0 / F 0 * -zb -
      (Y2 (-zb) - deriv F 0 / F 0 * Y1 (-zb)))
    rw [sub_sub_cancel, norm_sub_rev (1 - deriv F 0 / F 0 * -zb)] at this
    have h1 : ε * (1 - κ) / 2 = (1 - κ) * ε / 2 := by ring
    linarith
  have hy1b : 1 - κ - τ ≤ ‖Y1 zb‖ := by
    have := norm_sub_norm_le zb (zb - Y1 zb)
    rw [sub_sub_cancel, norm_sub_rev zb] at this
    linarith [hY1z zb hzbn.le]
  have hy1c : ‖Y1 (-zb)‖ ≤ 1 + τ := by
    have := norm_le_insert' (Y1 (-zb)) (-zb)
    linarith [hY1z (-zb) hzcn.le]
  have hε6 : ε ≤ 6 := hVε.trans hV6
  have har := s09_bad_ar hε hκε hκ4 hκ0.le hτε hτ0 hε6 hy1b hdB hy1c (norm_nonneg _) hdC
  -- `|F 0|² |Y1 z_b| |D(-z_b)| ≤ ε/1280 |F 0|² |Y1 (-z_b)| |D z_b|`, against `har`
  have pb := congrArg norm (hprod zb hzbD)
  have pc := congrArg norm (hprod (-zb) hzcD)
  simp only [norm_mul, norm_pow] at pb pc
  have hF0n : 0 < ‖F 0‖ ^ 2 := pow_pos (norm_pos_iff.mpr hF0) 2
  obtain ⟨dB, hdBd⟩ : ∃ x : ℝ, x = ‖Y2 zb - deriv F 0 / F 0 * Y1 zb‖ := ⟨_, rfl⟩
  obtain ⟨dC, hdCd⟩ : ∃ x : ℝ, x = ‖Y2 (-zb) - deriv F 0 / F 0 * Y1 (-zb)‖ := ⟨_, rfl⟩
  rw [← hdBd] at pb har
  rw [← hdCd] at pc har
  have hdB0 : 0 ≤ dB := by rw [hdBd]; exact norm_nonneg _
  have hdC0 : 0 ≤ dC := by rw [hdCd]; exact norm_nonneg _
  have key : ‖F 0‖ ^ 2 * (‖Y1 zb‖ * dC) ≤ ‖F 0‖ ^ 2 * (ε / 1280 * (‖Y1 (-zb)‖ * dB)) := by
    calc ‖F 0‖ ^ 2 * (‖Y1 zb‖ * dC) = ‖h zb - h 0‖ * dB * dC := by rw [pb]; ring
      _ ≤ ε / 1280 * ‖h (-zb) - h 0‖ * dB * dC := by gcongr
      _ = ε / 1280 * dB * (‖h (-zb) - h 0‖ * dC) := by ring
      _ = ‖F 0‖ ^ 2 * (ε / 1280 * (‖Y1 (-zb)‖ * dB)) := by rw [pc]; ring
  have := le_of_mul_le_mul_left key hF0n
  linarith

/-- Helper for `lem_length` (Stage A, S5): the pointwise arithmetic of the three-case split. With
`d = 1-|z|² ≤ e = 1-|w|²`, `|F''|² ≤ a (S² + q⁴)/2` and `P₂ = a q⁴` when `e q ≥ 1/4`,
`ρ⁴ |F''|² d³ ≤ d³ ρ² a S² + d³ ρ² P₂ + (ρ² a q²/4) d / 8`. -/
theorem s09_len_core_ar {ρ d e a S q F2 P2 : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hd : 0 ≤ d)
    (hde : d ≤ e) (ha : 0 ≤ a) (hq : 0 ≤ q) (hF2 : F2 ≤ a * (S ^ 2 + q ^ 4) / 2)
    (hP2 : 0 ≤ P2) (hcase : 1 / 4 ≤ e * q → P2 = a * q ^ 4) :
    ρ ^ 4 * F2 * d ^ 3 ≤
      d ^ 3 * (ρ ^ 2 * (a * S ^ 2)) + (d ^ 3 * (ρ ^ 2 * P2) + 1 / 8 * (ρ ^ 2 * (a * q ^ 2 / 4) * d)) := by
  have hρ2 : ρ ^ 2 ≤ 1 := pow_le_one₀ hρ0 hρ1
  have hρ4 : ρ ^ 4 ≤ ρ ^ 2 := by
    have : ρ ^ 4 = ρ ^ 2 * ρ ^ 2 := by ring
    rw [this]
    exact mul_le_of_le_one_right (sq_nonneg ρ) hρ2
  have hk1 : ρ ^ 4 * F2 * d ^ 3 ≤ ρ ^ 4 * d ^ 3 * (a * (S ^ 2 + q ^ 4) / 2) := by
    have := mul_le_mul_of_nonneg_left hF2 (by positivity : (0 : ℝ) ≤ ρ ^ 4 * d ^ 3)
    linarith
  have hS1 : ρ ^ 4 * d ^ 3 * (a * S ^ 2) ≤ ρ ^ 2 * d ^ 3 * (a * S ^ 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρ4 (by positivity)) (by positivity)
  have hS0 : 0 ≤ ρ ^ 2 * d ^ 3 * (a * S ^ 2) := by positivity
  have hT0 : 0 ≤ 1 / 8 * (ρ ^ 2 * (a * q ^ 2 / 4) * d) := by positivity
  by_cases h : 1 / 4 ≤ e * q
  · rw [hcase h]
    have hQ1 : ρ ^ 4 * d ^ 3 * (a * q ^ 4) ≤ ρ ^ 2 * d ^ 3 * (a * q ^ 4) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρ4 (by positivity)) (by positivity)
    have hQ0 : 0 ≤ ρ ^ 2 * d ^ 3 * (a * q ^ 4) := by positivity
    linarith
  · have hdq : d * q ≤ 1 / 4 := (mul_le_mul_of_nonneg_right hde hq).trans (not_le.mp h).le
    have hdq2 : (d * q) ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ (by positivity) hdq 2
    have hX : ρ ^ 4 * d ^ 3 * (a * q ^ 4) ≤ ρ ^ 2 * (a * q ^ 2 * d) * (1 / 16) := by
      have h1 : ρ ^ 4 * d ^ 3 * (a * q ^ 4) = ρ ^ 2 * (a * q ^ 2 * d) * (ρ ^ 2 * (d * q) ^ 2) := by
        ring
      have h2 : ρ ^ 2 * (d * q) ^ 2 ≤ 1 / 16 :=
        (mul_le_of_le_one_left (sq_nonneg _) hρ2).trans (by linarith)
      rw [h1]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have hP0 : 0 ≤ d ^ 3 * (ρ ^ 2 * P2) := by positivity
    linarith

/-- Helper for `lem_length` (Stage A, S5): far from the boundary, `|f'| |g'|⁴ (1-|w|²)³` is bounded
by `2·6⁴/η⁴ |f'(0)|` for `|w| ≤ 1 - η` (Bloch `s02_sw_bloch`, `s09_len_distort`). -/
theorem s09_len_core_far {f : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω) {η : ℝ}
    (hη : 0 < η) {w : ℂ} (hw : w ∈ unitDisc) (hwη : ‖w‖ ≤ 1 - η) :
    ‖deriv f w‖ * ‖deriv (deriv f) w / deriv f w‖ ^ 4 * (1 - ‖w‖ ^ 2) ^ 3 ≤
      2 * 6 ^ 4 / η ^ 4 * ‖deriv f 0‖ := by
  have hB := s02_sw_bloch hf hw
  have hD := s09_len_distort hf hw
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have ht : η ≤ 1 - ‖w‖ := by linarith
  have hte : 1 - ‖w‖ ≤ 1 - ‖w‖ ^ 2 := by
    have := norm_nonneg w
    nlinarith
  have hq := norm_nonneg (deriv (deriv f) w / deriv f w)
  have he0 : 0 ≤ 1 - ‖w‖ ^ 2 := by linarith
  have h1 : ((1 - ‖w‖ ^ 2) * ‖deriv (deriv f) w / deriv f w‖) ^ 4 ≤ 6 ^ 4 :=
    pow_le_pow_left₀ (by positivity) hB 4
  have h2 : η ^ 4 ≤ (1 - ‖w‖ ^ 2) * (1 - ‖w‖) ^ 3 := by
    calc η ^ 4 ≤ (1 - ‖w‖) ^ 4 := pow_le_pow_left₀ hη.le ht 4
      _ = (1 - ‖w‖) * (1 - ‖w‖) ^ 3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hte (by have := hη.le; positivity)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  calc ‖deriv f w‖ * ‖deriv (deriv f) w / deriv f w‖ ^ 4 * (1 - ‖w‖ ^ 2) ^ 3 * η ^ 4
      ≤ ‖deriv f w‖ * ‖deriv (deriv f) w / deriv f w‖ ^ 4 * (1 - ‖w‖ ^ 2) ^ 3 *
          ((1 - ‖w‖ ^ 2) * (1 - ‖w‖) ^ 3) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ((1 - ‖w‖ ^ 2) * ‖deriv (deriv f) w / deriv f w‖) ^ 4 * (‖deriv f w‖ * (1 - ‖w‖) ^ 3) := by
        ring
    _ ≤ 6 ^ 4 * (2 * ‖deriv f 0‖) := mul_le_mul h1 hD (by positivity) (by norm_num)
    _ = _ := by ring

/-- Helper for `lem_length` (Stage A, S5): the Schwarzian Carleson integral of `|f'|` as an area
integral, `∫ |f'| dμ_f = ∫_𝔻 |Sf|² (1-|z|²)³ |f'| dA` (with the holomorphic `schwarzianHol`). -/
theorem s09_len_core_carl {f : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω) :
    ∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f =
      ∫⁻ z in unitDisc, ENNReal.ofReal (‖schwarzianHol f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) *
        ENNReal.ofReal ‖deriv f z‖ := by
  have hSm := s02_pullback_measurable_schwarzianHol f
  have hSch : ∀ z ∈ unitDisc, schwarzian f z = schwarzianHol f z := fun z hz =>
    schwarzian_of_analyticAt (hf.1.analyticAt (isOpen_ball.mem_nhds hz))
  have hcm : Measurable fun z => ENNReal.ofReal (‖schwarzianHol f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) := by
    fun_prop
  have hR : schwarzCarlesonMeasure f = (volume.restrict unitDisc).withDensity
      fun z => ENNReal.ofReal (‖schwarzianHol f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) := by
    unfold schwarzCarlesonMeasure
    refine withDensity_congr_ae ((ae_restrict_mem measurableSet_ball).mono fun z hz => ?_)
    simp only [hSch z hz]
  rw [hR, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hcm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rfl

/-- Helper for `lem_length` (Stage A, S5): for the dilation `G = F(ρ ·)` of `F = √f'`,
`|G''(z)|² (1-|z|²)³` is bounded by the three pieces of the split at `w = ρ z`: the Schwarzian
term `|ρ Ψ₁(ρz)|²`, the large-pre-Schwarzian term `|ρ Ψ₂(ρz)|²`, and `|G'(z)|² (1-|z|²)/8`
(`s09_len_pointwise`, `s09_len_core_ar`). -/
theorem s09_len_core_ptw {f F G Ψ₁ Ψ₂ : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (hF : DifferentiableOn ℂ F unitDisc) (hFf : ∀ z ∈ unitDisc, F z ^ 2 = deriv f z) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hG : G = fun z => F ((ρ : ℂ) * z))
    (hΨ₁ : ∀ w ∈ unitDisc, ‖Ψ₁ w‖ ^ 2 = ‖deriv f w‖ * ‖schwarzian f w‖ ^ 2)
    (hΨ₂ : ∀ w ∈ unitDisc, 1 / 4 ≤ (1 - ‖w‖ ^ 2) * ‖deriv (deriv f) w / deriv f w‖ →
      ‖Ψ₂ w‖ ^ 2 = ‖deriv f w‖ * ‖deriv (deriv f) w / deriv f w‖ ^ 4) {z : ℂ}
    (hz : z ∈ unitDisc) :
    ENNReal.ofReal (‖deriv (deriv G) z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) ≤
      ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 * ‖(ρ : ℂ) * Ψ₁ ((ρ : ℂ) * z)‖ ^ 2) +
        (ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 * ‖(ρ : ℂ) * Ψ₂ ((ρ : ℂ) * z)‖ ^ 2) +
          ENNReal.ofReal (1 / 8) * ENNReal.ofReal (‖deriv G z‖ ^ 2 * (1 - ‖z‖ ^ 2))) := by
  subst hG
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hnw : ‖(ρ : ℂ) * z‖ = ρ * ‖z‖ := by
    rw [norm_mul, Complex.norm_of_nonneg hρ0.le]
  have hwz : ‖(ρ : ℂ) * z‖ ≤ ‖z‖ := by
    rw [hnw]
    exact mul_le_of_le_one_left (norm_nonneg z) hρ1
  have hw : (ρ : ℂ) * z ∈ unitDisc := mem_ball_zero_iff.mpr (hwz.trans_lt hz1)
  have hd1 : deriv (fun z => F ((ρ : ℂ) * z)) = fun z => (ρ : ℂ) * deriv F ((ρ : ℂ) * z) := by
    funext x
    rw [deriv_comp_mul_left, smul_eq_mul]
  have hd2 : deriv (deriv (fun z => F ((ρ : ℂ) * z))) z =
      (ρ : ℂ) * ((ρ : ℂ) * deriv (deriv F) ((ρ : ℂ) * z)) := by
    rw [hd1, deriv_const_mul_field']
    beta_reduce
    rw [deriv_comp_mul_left, smul_eq_mul]
  have hnρ : ‖(ρ : ℂ)‖ = ρ := Complex.norm_of_nonneg hρ0.le
  obtain ⟨-, hp2, hp3⟩ := s09_len_pointwise hf hF hFf hw
  have hP2 : 0 ≤ ‖Ψ₂ ((ρ : ℂ) * z)‖ ^ 2 := sq_nonneg _
  have hde : 1 - ‖z‖ ^ 2 ≤ 1 - ‖(ρ : ℂ) * z‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hwz 2
    linarith
  have hd0 : 0 ≤ 1 - ‖z‖ ^ 2 := by
    have := pow_lt_one₀ (norm_nonneg z) hz1 two_ne_zero
    linarith
  have key := s09_len_core_ar hρ0.le hρ1 hd0 hde (norm_nonneg _) (norm_nonneg _)
    hp3 hP2 (hΨ₂ _ hw)
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hd2, hd1]
  simp only [norm_mul, hnρ, mul_pow]
  rw [hΨ₁ _ hw, hp2]
  calc ρ ^ 2 * (ρ ^ 2 * ‖deriv (deriv F) ((ρ : ℂ) * z)‖ ^ 2) * (1 - ‖z‖ ^ 2) ^ 3
      = ρ ^ 4 * ‖deriv (deriv F) ((ρ : ℂ) * z)‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3 := by ring
    _ ≤ _ := key
    _ = _ := by ring

/-- Helper for `lem_length` (Stage A, S5): `ρ · circleMap 0 s t = circleMap 0 (ρ s) t`. -/
theorem s09_len_core_circ (ρ s t : ℝ) : (ρ : ℂ) * circleMap 0 s t = circleMap 0 (ρ * s) t := by
  simp only [circleMap, zero_add]
  push_cast
  ring

/-- Helper for `lem_length` (Stage A, S5, [GM X, Theorem 6.2] left inequality): for a
`K`-quasidisc and a corkscrew-normalized conformal `f`,
`∫₀^{2π} r |f'(r e^{it})| dt ≤ C (|f'(0)| + ∫ |f'| |Sf|² (1-|z|²)³)` uniformly in `r ∈ (0, 1)`
(dilations `F(ρ·)`, `s09_len_L2`, the three-case split with `s09_len_case_ii` and
`s09_len_bad`, absorption by `s09_len_lp_upper`). -/
theorem s09_len_core (K : ℝ) (hK : 1 ≤ K) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ≥0, ∀ (Ω Ωs : Set ℂ) (f : ℂ → ℂ), IsBoundedKQuasicircle Ω Ωs K →
      IsConformalOnto f unitDisc Ω →
      c * Metric.diam (curveOf Ω Ωs) ≤ infDist (f 0) (curveOf Ω Ωs) →
      ∀ r ∈ Ioo (0 : ℝ) 1,
        ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (r * ‖deriv f (circleMap 0 r t)‖) ≤
          (C : ℝ≥0∞) * (ENNReal.ofReal ‖deriv f 0‖ +
            ∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f) := by
  obtain ⟨b, δ, η, hb0, hb1, hδ, hη, hbad⟩ := s09_len_bad K hK c hc (1 / 4) (by norm_num)
  obtain ⟨Cii, hCii⟩ := s09_len_case_ii b δ hb0 hb1 hδ
  have hV : volume unitDisc ≠ ⊤ := measure_ball_lt_top.ne
  have hDs : MeasurableSet unitDisc := measurableSet_ball
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ≥0∞, C₁ = ENNReal.ofReal (20 * π) +
      2 * (ENNReal.ofReal (2 * 6 ^ 4 / η ^ 4) * volume unitDisc) + 2 + 2 * (Cii : ℝ≥0∞) :=
    ⟨_, rfl⟩
  have hC₁t : C₁ ≠ ⊤ := by
    rw [hC₁]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV)⟩, by norm_num⟩,
      ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top⟩
  refine ⟨(ENNReal.ofReal (4 / 3) * C₁).toNNReal, fun Ω Ωs f hΓ hf hcork r hr => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC₁t)]
  obtain ⟨F, hF, hFf⟩ := s09_len_sqrt hf
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (1 + r) / 2 := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; linarith [hr.1]
  have hρ1 : ρ < 1 := by rw [hρ]; linarith [hr.2]
  have hrρ : r < ρ := by rw [hρ]; linarith [hr.2]
  obtain ⟨G, hGd⟩ : ∃ G : ℂ → ℂ, G = fun z => F ((ρ : ℂ) * z) := ⟨_, rfl⟩
  have hmaps : MapsTo (fun z : ℂ => (ρ : ℂ) * z) unitDisc unitDisc := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    refine mem_ball_zero_iff.mpr ?_
    rw [norm_mul, Complex.norm_of_nonneg hρ0.le]
    nlinarith [norm_nonneg z]
  have hG : DifferentiableOn ℂ G unitDisc := by
    rw [hGd]
    exact hF.comp (by fun_prop) hmaps
  -- `Y = sup_s ∫ |G(s e^{it})|²` is finite: `F` is bounded on `closedBall 0 ρ`.
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ≥0∞, Y = ⨆ s ∈ Ioo (0 : ℝ) 1,
      ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (‖G (circleMap 0 s t)‖ ^ 2) := ⟨_, rfl⟩
  have hYt : Y ≠ ⊤ := by
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn
      (hF.continuousOn.mono (closedBall_subset_ball hρ1))
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := M ^ 2))
      (measure_Ioc_lt_top : volume (Ioc (0 : ℝ) (2 * π)) < ⊤).ne) ?_
    rw [hY]
    refine iSup₂_le fun s hs => ?_
    rw [← setLIntegral_const]
    refine lintegral_mono fun t => ENNReal.ofReal_le_ofReal ?_
    have hmem : (ρ : ℂ) * circleMap 0 s t ∈ closedBall (0 : ℂ) ρ := by
      rw [s09_len_core_circ, mem_closedBall_zero_iff, norm_circleMap_zero,
        abs_of_pos (mul_pos hρ0 hs.1)]
      exact mul_le_of_le_one_right hρ0.le hs.2.le
    rw [hGd]
    exact pow_le_pow_left₀ (norm_nonneg _) (hM _ hmem) 2
  -- the three pieces
  obtain ⟨Ψ₁, hΨ₁d⟩ : ∃ Ψ₁ : ℂ → ℂ, Ψ₁ = fun w =>
      ((Real.sqrt ‖deriv f w‖ : ℝ) : ℂ) * schwarzianHol f w := ⟨_, rfl⟩
  obtain ⟨Ψ₂, hΨ₂d⟩ : ∃ Ψ₂ : ℂ → ℂ, Ψ₂ =
      {w | 1 / 4 ≤ (1 - ‖w‖ ^ 2) * ‖deriv (deriv f) w / deriv f w‖}.indicator fun w =>
        ((Real.sqrt ‖deriv f w‖ : ℝ) : ℂ) * (deriv (deriv f) w / deriv f w) ^ 2 := ⟨_, rfl⟩
  have hSm := s02_pullback_measurable_schwarzianHol f
  have hDm := measurable_deriv f
  have hDDm := measurable_deriv (deriv f)
  have hΨ₁m : Measurable Ψ₁ := by
    rw [hΨ₁d]
    fun_prop
  have hΨ₂m : Measurable Ψ₂ := by
    rw [hΨ₂d]
    exact Measurable.indicator (by fun_prop) (measurableSet_le measurable_const (by fun_prop))
  have hsq : ∀ w, ‖((Real.sqrt ‖deriv f w‖ : ℝ) : ℂ)‖ ^ 2 = ‖deriv f w‖ := fun w => by
    rw [Complex.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (norm_nonneg _)]
  have hΨ₁n : ∀ w ∈ unitDisc, ‖Ψ₁ w‖ ^ 2 = ‖deriv f w‖ * ‖schwarzian f w‖ ^ 2 := by
    intro w hw
    rw [hΨ₁d, schwarzian_of_analyticAt (hf.1.analyticAt (isOpen_ball.mem_nhds hw))]
    simp only [norm_mul, mul_pow, hsq]
  have hΨ₂n : ∀ w ∈ unitDisc, 1 / 4 ≤ (1 - ‖w‖ ^ 2) * ‖deriv (deriv f) w / deriv f w‖ →
      ‖Ψ₂ w‖ ^ 2 = ‖deriv f w‖ * ‖deriv (deriv f) w / deriv f w‖ ^ 4 := by
    intro w _ hp
    rw [hΨ₂d, Set.indicator_of_mem (show w ∈ {w | 1 / 4 ≤ (1 - ‖w‖ ^ 2) *
      ‖deriv (deriv f) w / deriv f w‖} from hp)]
    simp only [norm_mul, mul_pow, hsq, norm_pow]
    ring
  -- piece 1: the Schwarzian term is the Carleson integral
  have hI1 : ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 * ‖(ρ : ℂ) * Ψ₁ ((ρ : ℂ) * z)‖ ^ 2) ≤
      ∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f := by
    refine (s02_vd_scale hΨ₁m hρ0 hρ1.le).trans ?_
    rw [s09_len_core_carl hf]
    refine setLIntegral_mono' hDs fun w hw => ?_
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have hw2 : 0 ≤ 1 - ‖w‖ ^ 2 := by
      have := pow_lt_one₀ (norm_nonneg w) hw1 two_ne_zero
      linarith
    rw [← ENNReal.ofReal_mul (by positivity), hΨ₁d]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    simp only [norm_mul, mul_pow, hsq]
    ring
  -- piece 2: large pre-Schwarzian, split by `s09_len_bad` into far points and case (ii)
  have hI2 : ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 * ‖(ρ : ℂ) * Ψ₂ ((ρ : ℂ) * z)‖ ^ 2) ≤
      ENNReal.ofReal (2 * 6 ^ 4 / η ^ 4 * ‖deriv f 0‖) * volume unitDisc +
        (Cii : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f := by
    refine (s02_vd_scale hΨ₂m hρ0 hρ1.le).trans ?_
    refine (setLIntegral_mono' hDs (g := fun w =>
      ENNReal.ofReal (2 * 6 ^ 4 / η ^ 4 * ‖deriv f 0‖) +
        {u | u ∈ unitDisc ∧ ∃ w ∈ unitDisc, ‖w - u‖ < b * ‖1 - (starRingEnd ℂ) u * w‖ ∧
          δ ≤ (1 - ‖w‖ ^ 2) ^ 2 * ‖schwarzian f w‖}.indicator (fun u => ENNReal.ofReal
            (‖deriv f u‖ * ‖deriv (deriv f) u / deriv f u‖ ^ 4 * (1 - ‖u‖ ^ 2) ^ 3)) w)
      fun w hw => ?_).trans ?_
    · by_cases hp : 1 / 4 ≤ (1 - ‖w‖ ^ 2) * ‖deriv (deriv f) w / deriv f w‖
      · rw [hΨ₂n w hw hp]
        by_cases hW : w ∈ {u | u ∈ unitDisc ∧ ∃ w ∈ unitDisc,
            ‖w - u‖ < b * ‖1 - (starRingEnd ℂ) u * w‖ ∧ δ ≤ (1 - ‖w‖ ^ 2) ^ 2 * ‖schwarzian f w‖}
        · rw [Set.indicator_of_mem hW]
          exact le_add_left (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))
        · have hfar : ‖w‖ ≤ 1 - η := hbad Ω Ωs f hΓ hf hcork w hw hp fun w' hw' hnear =>
            not_le.mp fun hge => hW ⟨hw, w', hw', hnear, hge⟩
          refine le_add_right (ENNReal.ofReal_le_ofReal ?_)
          calc (1 - ‖w‖ ^ 2) ^ 3 * (‖deriv f w‖ * ‖deriv (deriv f) w / deriv f w‖ ^ 4)
              = ‖deriv f w‖ * ‖deriv (deriv f) w / deriv f w‖ ^ 4 * (1 - ‖w‖ ^ 2) ^ 3 := by ring
            _ ≤ _ := s09_len_core_far hf hη hw hfar
      · rw [hΨ₂d, Set.indicator_of_notMem (show w ∉ {w | 1 / 4 ≤ (1 - ‖w‖ ^ 2) *
          ‖deriv (deriv f) w / deriv f w‖} from hp)]
        simp
    · rw [lintegral_add_left' aemeasurable_const, setLIntegral_const]
      refine add_le_add le_rfl ((setLIntegral_le_lintegral _ _).trans
        ((lintegral_indicator_le _ _).trans (hCii Ω f hf)))
  -- piece 3: absorbed by the upper Littlewood–Paley bound
  have hI3 : ∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv G z‖ ^ 2 * (1 - ‖z‖ ^ 2)) ≤ Y := by
    rw [hY]
    exact s09_len_lp_upper hG
  have hm1 : AEMeasurable (fun z => ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 *
      ‖(ρ : ℂ) * Ψ₁ ((ρ : ℂ) * z)‖ ^ 2)) (volume.restrict unitDisc) := by
    exact Measurable.aemeasurable (by fun_prop)
  have hm2 : AEMeasurable (fun z => ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 *
      ‖(ρ : ℂ) * Ψ₂ ((ρ : ℂ) * z)‖ ^ 2)) (volume.restrict unitDisc) := by
    exact Measurable.aemeasurable (by fun_prop)
  have hint : ∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv (deriv G) z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) ≤
      ∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f +
        (ENNReal.ofReal (2 * 6 ^ 4 / η ^ 4 * ‖deriv f 0‖) * volume unitDisc +
          (Cii : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f) +
        ENNReal.ofReal (1 / 8) * Y := by
    refine (setLIntegral_mono' hDs fun z hz =>
      s09_len_core_ptw hf hF hFf hρ0 hρ1.le hGd hΨ₁n hΨ₂n hz).trans ?_
    rw [lintegral_add_left' hm1, lintegral_add_left' hm2,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← add_assoc]
    exact add_le_add (add_le_add hI1 hI2) (mul_le_mul_right hI3 _)
  -- the constant terms at `0`
  obtain ⟨hn0, hn1, -⟩ := s09_len_pointwise hf hF hFf (mem_ball_self one_pos)
  have hB0 := s02_sw_bloch hf (mem_ball_self one_pos)
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
    one_mul] at hB0
  have hG0 : G 0 = F 0 := by simp only [hGd, mul_zero]
  have hG'0 : deriv G 0 = (ρ : ℂ) * deriv F 0 := by
    rw [hGd, deriv_comp_mul_left, smul_eq_mul, mul_zero]
  have hX0 : ENNReal.ofReal (2 * π * (‖G 0‖ ^ 2 + ‖deriv G 0‖ ^ 2)) ≤
      ENNReal.ofReal (20 * π) * ENNReal.ofReal ‖deriv f 0‖ := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hG0, hG'0, norm_mul, mul_pow, Complex.norm_of_nonneg hρ0.le, hn0, hn1]
    have hq2 : ‖deriv (deriv f) 0 / deriv f 0‖ ^ 2 ≤ 6 ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hB0 2
    have hρ2 : ρ ^ 2 ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
    have ha := norm_nonneg (deriv f 0)
    have h1 : ρ ^ 2 * (‖deriv f 0‖ * ‖deriv (deriv f) 0 / deriv f 0‖ ^ 2 / 4) ≤
        ‖deriv f 0‖ * ‖deriv (deriv f) 0 / deriv f 0‖ ^ 2 / 4 :=
      mul_le_of_le_one_left (by positivity) hρ2
    have h2 : ‖deriv f 0‖ * ‖deriv (deriv f) 0 / deriv f 0‖ ^ 2 ≤ ‖deriv f 0‖ * 6 ^ 2 :=
      mul_le_mul_of_nonneg_left hq2 ha
    have h3 : 0 ≤ π := Real.pi_pos.le
    nlinarith
  -- absorption
  have hYA : Y ≤ (ENNReal.ofReal (2 * π * (‖G 0‖ ^ 2 + ‖deriv G 0‖ ^ 2)) +
      2 * (∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f +
        (ENNReal.ofReal (2 * 6 ^ 4 / η ^ 4 * ‖deriv f 0‖) * volume unitDisc +
          (Cii : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f))) +
      ENNReal.ofReal (1 / 4) * Y := by
    have h2q : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 8) = ENNReal.ofReal (1 / 4) := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num
    conv_lhs => rw [hY]
    refine iSup₂_le fun s hs => ?_
    refine (s09_len_L2 hG hs.1.le hs.2).trans ?_
    calc _ ≤ ENNReal.ofReal (2 * π * (‖G 0‖ ^ 2 + ‖deriv G 0‖ ^ 2)) +
          2 * (∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f +
            (ENNReal.ofReal (2 * 6 ^ 4 / η ^ 4 * ‖deriv f 0‖) * volume unitDisc +
              (Cii : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f) +
            ENNReal.ofReal (1 / 8) * Y) := add_le_add le_rfl (mul_le_mul_right hint 2)
      _ = _ := by rw [mul_add _ _ (ENNReal.ofReal (1 / 8) * Y), ← mul_assoc, h2q, add_assoc]
  obtain ⟨A, hA⟩ : ∃ A : ℝ≥0∞, A = ENNReal.ofReal (2 * π * (‖G 0‖ ^ 2 + ‖deriv G 0‖ ^ 2)) +
      2 * (∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f +
        (ENNReal.ofReal (2 * 6 ^ 4 / η ^ 4 * ‖deriv f 0‖) * volume unitDisc +
          (Cii : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f)) :=
    ⟨_, rfl⟩
  rw [← hA] at hYA
  have hYle : Y ≤ ENNReal.ofReal (4 / 3) * A := by
    have hsplit : Y = ENNReal.ofReal (3 / 4) * Y + ENNReal.ofReal (1 / 4) * Y := by
      rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    have h34 : ENNReal.ofReal (3 / 4) * Y ≤ A := by
      refine ENNReal.le_of_add_le_add_right (a := ENNReal.ofReal (1 / 4) * Y)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hYt) ?_
      rw [← hsplit]
      exact hYA
    calc Y = ENNReal.ofReal (4 / 3) * (ENNReal.ofReal (3 / 4) * Y) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
      _ ≤ _ := mul_le_mul_right h34 _
  -- `A ≤ C₁ (|f'(0)| + ∫ |f'| dμ_f)`
  have hAC : A ≤ C₁ * (ENNReal.ofReal ‖deriv f 0‖ +
      ∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f) := by
    rw [hA, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * 6 ^ 4 / η ^ 4)]
    calc _ ≤ ENNReal.ofReal (20 * π) * ENNReal.ofReal ‖deriv f 0‖ +
          2 * (∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f +
            (ENNReal.ofReal (2 * 6 ^ 4 / η ^ 4) * ENNReal.ofReal ‖deriv f 0‖ * volume unitDisc +
              (Cii : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f)) :=
          add_le_add hX0 le_rfl
      _ ≤ ENNReal.ofReal (20 * π) * ENNReal.ofReal ‖deriv f 0‖ +
          2 * (∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f +
            (ENNReal.ofReal (2 * 6 ^ 4 / η ^ 4) * ENNReal.ofReal ‖deriv f 0‖ * volume unitDisc +
              (Cii : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f)) +
          ((2 + 2 * (Cii : ℝ≥0∞)) * ENNReal.ofReal ‖deriv f 0‖ +
            (ENNReal.ofReal (20 * π) + 2 * (ENNReal.ofReal (2 * 6 ^ 4 / η ^ 4) *
              volume unitDisc)) *
              ∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f) := le_self_add
      _ = _ := by
          rw [hC₁]
          ring
  calc _ ≤ ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (‖G (circleMap 0 (r / ρ) t)‖ ^ 2) := by
        refine lintegral_mono fun t => ENNReal.ofReal_le_ofReal ?_
        have hρr : ρ * (r / ρ) = r := by field_simp
        have hmem : circleMap 0 r t ∈ unitDisc := by
          refine mem_ball_zero_iff.mpr ?_
          rw [norm_circleMap_zero, abs_of_pos hr.1]
          exact hr.2
        rw [hGd]
        show r * _ ≤ ‖F ((ρ : ℂ) * circleMap 0 (r / ρ) t)‖ ^ 2
        rw [s09_len_core_circ, hρr, (s09_len_pointwise hf hF hFf hmem).1]
        exact mul_le_of_le_one_left (norm_nonneg _) hr.2.le
    _ ≤ Y := by
        rw [hY]
        exact le_iSup₂_of_le (r / ρ) ⟨div_pos hr.1 hρ0, (div_lt_one hρ0).mpr hrρ⟩ le_rfl
    _ ≤ ENNReal.ofReal (4 / 3) * A := hYle
    _ ≤ ENNReal.ofReal (4 / 3) * (C₁ * (ENNReal.ofReal ‖deriv f 0‖ +
          ∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f)) := mul_le_mul_right hAC _
    _ = _ := by rw [mul_assoc]

/-- Lemma 9.12 `lem:length` (`sec09-ambient.tex:876`): for a bounded `K`-quasicircle,
`x ∈ Γ`, `δ = diam Γ`, `P_* = (x, δ)`: `Λ¹(Γ) ≤ C_GM(K) (1 + 260 H^Ω(P_*)) δ`, with
`C_GM(K)` the constant of [GM, Theorem X.6.2]. -/
theorem lem_length :
    ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ≥0, ∀ Ω Ωs : Set ℂ, IsBoundedKQuasicircle Ω Ωs K →
      ∀ x ∈ curveOf Ω Ωs,
        μH[1] (curveOf Ω Ωs) ≤ (C : ℝ≥0∞) *
          (1 + 260 * ambHside Ω (x, Metric.diam (curveOf Ω Ωs))) *
            ENNReal.ofReal (Metric.diam (curveOf Ω Ωs)) := by
  intro K hK
  obtain ⟨c₂, hc₂, hcork⟩ := lem_corkscrew_bounded K
  obtain ⟨C, hC⟩ := s09_len_core K hK (c₂ / 2) (by positivity)
  refine ⟨4 * C, fun Ω Ωs hΓ x hx => ?_⟩
  have hbjp : IsBoundedJordanPair Ω Ωs := by
    obtain ⟨F, hF, hFs, h1, h2⟩ := id hΓ
    obtain ⟨e, rfl⟩ := t1_homeomorph hF hFs
    exact ⟨e, h1, h2⟩
  obtain ⟨-, -, -, -, -, hΓc⟩ := s09_bjp_basic Ω Ωs hbjp
  obtain ⟨hball, hhalf⟩ := lem_dictionary_a Ω Ωs hbjp x hx
  obtain ⟨-, hmu⟩ := lem_dictionary_b Ω Ωs hbjp x hx
  have hxΩ : x ∈ Ωᶜ := fun h => hx (mem_union_left _ h)
  obtain ⟨f₀, hf₀⟩ := s07_exists_riemannMap hΓ
  have hw0 : f₀ 0 ∈ Ω := hf₀.2.2 ▸ mem_image_of_mem f₀ (mem_ball_self one_pos)
  have hδ0 : 0 < Metric.diam (curveOf Ω Ωs) := by
    have h1 : 0 < infDist (f₀ 0) (curveOf Ω Ωs) :=
      (hΓc.notMem_iff_infDist_pos ⟨x, hx⟩).mp fun h => h (mem_union_left _ hw0)
    linarith [hhalf _ hw0]
  obtain ⟨yp, hyp, ym, -, -, -, -, -, hyp', -⟩ :=
    hcork Ω Ωs hΓ x hx (Metric.diam (curveOf Ω Ωs) / 2) (by positivity) le_rfl
  obtain ⟨p, hp, hpy⟩ : yp ∈ f₀ '' unitDisc := by rw [hf₀.2.2]; exact hyp
  obtain ⟨hf, hf0, -⟩ := s02_disc_recenter hf₀ hp
  generalize f₀ ∘ blaschke (-p) = f at hf hf0
  have hnorm : c₂ / 2 * Metric.diam (curveOf Ω Ωs) ≤ infDist (f 0) (curveOf Ω Ωs) := by
    rw [hf0, hpy]
    linarith
  have hd0 : ‖deriv f 0‖ ≤ 4 * Metric.diam (curveOf Ω Ωs) := by
    have h := (lem_koebe_a hf (mem_ball_self one_pos)).2.1
    have h2 : infDist (f 0) Ωᶜ ≤ dist (f 0) x := infDist_le_dist_of_mem hxΩ
    have h3 : dist (f 0) x < Metric.diam (curveOf Ω Ωs) :=
      hball (hf.2.2 ▸ mem_image_of_mem f (mem_ball_self one_pos))
    norm_num at h
    linarith
  obtain ⟨-, -, hI, -⟩ := lem_dictionary_c Ω Ωs hbjp f hf
  have e1 : (16 : ℝ≥0∞) * ENNReal.ofReal (65 / 4 * Metric.diam (curveOf Ω Ωs)) =
      260 * ENNReal.ofReal (Metric.diam (curveOf Ω Ωs)) := by
    rw [← ENNReal.ofReal_ofNat 16, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_ofNat 260, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  have e2 : ENNReal.ofReal (4 * Metric.diam (curveOf Ω Ωs)) =
      4 * ENNReal.ofReal (Metric.diam (curveOf Ω Ωs)) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  calc μH[1] (curveOf Ω Ωs)
      ≤ ⨆ r ∈ Ioo (0 : ℝ) 1,
          ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal (r * ‖deriv f (circleMap 0 r t)‖) :=
        s09_len_radial hΓ hf
    _ ≤ (C : ℝ≥0∞) * (ENNReal.ofReal ‖deriv f 0‖ +
          ∫⁻ z, ENNReal.ofReal ‖deriv f z‖ ∂schwarzCarlesonMeasure f) :=
        iSup₂_le (hC Ω Ωs f hΓ hf hnorm)
    _ ≤ (C : ℝ≥0∞) * (ENNReal.ofReal (4 * Metric.diam (curveOf Ω Ωs)) +
          16 * (ENNReal.ofReal (65 / 4 * Metric.diam (curveOf Ω Ωs)) *
            ambHside Ω (x, Metric.diam (curveOf Ω Ωs)))) :=
        by
          gcongr _ * (?_ + ?_)
          · exact ENNReal.ofReal_le_ofReal hd0
          · exact hI.trans (by gcongr)
    _ ≤ ((4 * C : ℝ≥0) : ℝ≥0∞) * (1 + 260 * ambHside Ω (x, Metric.diam (curveOf Ω Ωs))) *
          ENNReal.ofReal (Metric.diam (curveOf Ω Ωs)) := by
        rw [← mul_assoc 16, e1, e2]
        push_cast
        calc (C : ℝ≥0∞) * (4 * ENNReal.ofReal (Metric.diam (curveOf Ω Ωs)) +
              260 * ENNReal.ofReal (Metric.diam (curveOf Ω Ωs)) *
                ambHside Ω (x, Metric.diam (curveOf Ω Ωs)))
            ≤ (C : ℝ≥0∞) * (4 * ENNReal.ofReal (Metric.diam (curveOf Ω Ωs)) +
              4 * (260 * ENNReal.ofReal (Metric.diam (curveOf Ω Ωs)) *
                ambHside Ω (x, Metric.diam (curveOf Ω Ωs)))) := by
              refine mul_le_mul_of_nonneg_left (add_le_add le_rfl
                (le_mul_of_one_le_left' (show (1 : ℝ≥0∞) ≤ 4 by norm_num))) (by positivity)
          _ = _ := by ring

/-- Helper for `prop_chord_arc_quant`: a bounded `K`-quasicircle pair is a bounded Jordan pair. -/
theorem s09_cq_bjp {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K) :
    IsBoundedJordanPair Ω Ωs := by
  obtain ⟨F, hF, hFs, h1, h2⟩ := hΓ
  obtain ⟨e, rfl⟩ := t1_homeomorph hF hFs
  exact ⟨e, h1, h2⟩

/-- Helper for `prop_chord_arc_quant`: the curve of a bounded `K`-quasicircle pair is a Jordan
curve. -/
theorem s09_cq_jordanC {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K) :
    IsJordanCurveC (curveOf Ω Ωs) := by
  obtain ⟨F, hF, hFs, h1, h2⟩ := hΓ
  have hFc : Continuous F := continuousOn_univ.mp hF.2.2.1.1
  have hFi : Function.Injective F := injOn_univ.mp hF.2.2.1.2.1
  refine ⟨fun u : Circle => F u, hFc.comp continuous_subtype_val, fun u v h => ?_, ?_⟩
  · exact Subtype.ext (hFi h)
  · ext w
    constructor
    · rintro ⟨u, rfl⟩
      simp only [curveOf, mem_compl_iff, mem_union, not_or]
      have hu : ‖(u : ℂ)‖ = 1 := Circle.norm_coe u
      constructor
      · rw [← h1]
        rintro ⟨d, hd, hdu⟩
        have := mem_ball_zero_iff.mp hd
        rw [hFi hdu] at this
        linarith
      · rw [← h2]
        rintro ⟨d, hd, hdu⟩
        have hd' : 1 < ‖d‖ := hd
        rw [hFi hdu] at hd'
        linarith
    · intro hw
      simp only [curveOf, mem_compl_iff, mem_union, not_or] at hw
      obtain ⟨z, -, rfl⟩ : w ∈ F '' univ := by
        rw [hFs]
        exact mem_univ w
      have hz : ‖z‖ = 1 := by
        rcases lt_trichotomy ‖z‖ 1 with h | h | h
        · exact absurd (by rw [← h1]; exact mem_image_of_mem F (mem_ball_zero_iff.mpr h)) hw.1
        · exact h
        · exact absurd (by rw [← h2]; exact mem_image_of_mem F (show z ∈ unitDiscExterior from h))
            hw.2
      exact ⟨⟨z, mem_sphere_zero_iff_norm.mpr hz⟩, rfl⟩

/-- The disk automorphism `σ z = a + c (z - a)⁻¹`, `c = a (|a|² - 1)/ā`, `|a| > 1`, used for
`s09_cq_inv_qc`: `|σ z| |z - a| = |ā z - 1|` and `|ā z - 1|² - |z - a|² = (|a|² - 1)(|z|² - 1)`. -/
theorem s09_cq_sigma_norm {a : ℂ} (ha : a ≠ 0) {z : ℂ} (hz : z ≠ a) :
    ‖a + a * ((‖a‖ ^ 2 - 1 : ℝ) : ℂ) / conj a * (z - a)⁻¹‖ ^ 2 * ‖z - a‖ ^ 2 -
        ‖z - a‖ ^ 2 = (‖a‖ ^ 2 - 1) * (‖z‖ ^ 2 - 1) := by
  have hza : z - a ≠ 0 := sub_ne_zero.mpr hz
  have hca : conj a ≠ 0 := (map_ne_zero _).mpr ha
  have key : (a + a * ((‖a‖ ^ 2 - 1 : ℝ) : ℂ) / conj a * (z - a)⁻¹) * (z - a) =
      a / conj a * (conj a * z - 1) := by
    have hnc : ((‖a‖ : ℝ) : ℂ) ^ 2 = a * conj a := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    field_simp
    push_cast
    linear_combination hnc
  have hsq : ∀ w : ℂ, ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := fun w => by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have h1 : ‖a / conj a‖ = 1 := by
    rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr ha)]
  rw [← mul_pow, ← norm_mul, key, norm_mul, h1, one_mul, hsq, hsq, hsq, hsq]
  simp only [sub_re, sub_im, mul_re, mul_im, conj_re, conj_im, one_re, one_im]
  ring

/-- Helper for `prop_chord_arc_quant` (W-QCMOB): inverting a bounded `K`-quasicircle pair at a
point `y` of the unbounded component gives a bounded `K`-quasicircle pair, with bounded
component `τ(Ω)`, `τ = invAt y` (`τ(y) = ∞`; Lean's `invAt y y = 0` is the image of `∞`). -/
theorem s09_cq_inv_qc {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K) {y : ℂ}
    (hy : y ∈ Ωs) : IsBoundedKQuasicircle (invAt y '' Ω) (invAt y '' Ωs) K := by
  -- the same conjugation as `s03_invPair_isKQuasiPair` (S03), with the Cayley map `T` replaced
  -- by the disk automorphism `σ` exchanging `a = F⁻¹ y` and `∞`
  obtain ⟨F, hF, hFs, h1, h2⟩ := hΓ
  obtain ⟨a, ha1, rfl⟩ : y ∈ F '' unitDiscExterior := by
    rw [h2]
    exact hy
  have ha1' : 1 < ‖a‖ := ha1
  have ha : a ≠ 0 := ne_zero_of_norm_ne_zero (by linarith)
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = a * ((‖a‖ ^ 2 - 1 : ℝ) : ℂ) / conj a := ⟨_, rfl⟩
  have hc : c ≠ 0 := by
    rw [hcdef]
    refine div_ne_zero (mul_ne_zero ha ?_) ((map_ne_zero _).mpr ha)
    exact_mod_cast (show ‖a‖ ^ 2 - 1 ≠ 0 by nlinarith)
  obtain ⟨σ, hσ⟩ : ∃ σ : ℂ → ℂ, σ = fun z => a + c * (z - a)⁻¹ := ⟨_, rfl⟩
  have hσa : σ a = a := by
    rw [hσ]
    simp
  have hσne : ∀ z, z ≠ a → σ z ≠ a := fun z hz h => by
    rw [hσ] at h
    simp only [add_eq_left, mul_eq_zero, inv_eq_zero, sub_eq_zero] at h
    exact h.elim hc hz
  have hσσ : ∀ z, σ (σ z) = z := fun z => by
    rcases eq_or_ne z a with rfl | hz
    · rw [hσa, hσa]
    · have hza : z - a ≠ 0 := sub_ne_zero.mpr hz
      rw [hσ]
      simp only [add_sub_cancel_left, mul_inv, inv_inv]
      field_simp
      ring
  have hσn : ∀ z, z ≠ a → (‖σ z‖ < 1 ↔ ‖z‖ < 1) ∧ (1 < ‖σ z‖ ↔ 1 < ‖z‖) := fun z hz => by
    have hid := s09_cq_sigma_norm ha hz
    rw [← hcdef] at hid
    have hpos : 0 < ‖z - a‖ ^ 2 := by
      have := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
      positivity
    have hA : 0 < ‖a‖ ^ 2 - 1 := by nlinarith
    have hσz : σ z = a + c * (z - a)⁻¹ := by rw [hσ]
    rw [← hσz] at hid
    have hs0 := norm_nonneg (σ z)
    have hz0 := norm_nonneg z
    constructor
    · constructor
      · intro h
        by_contra h'
        have hn2 : 1 ≤ ‖z‖ ^ 2 := by nlinarith [not_lt.mp h']
        have hs2 : ‖σ z‖ ^ 2 < 1 := by nlinarith
        have p1 := mul_pos (sub_pos.mpr hs2) hpos
        have p2 := mul_nonneg hA.le (sub_nonneg.mpr hn2)
        linarith
      · intro h
        by_contra h'
        have hs2 : 1 ≤ ‖σ z‖ ^ 2 := by nlinarith [not_lt.mp h']
        have hn2 : ‖z‖ ^ 2 < 1 := by nlinarith
        have p1 := mul_nonneg (sub_nonneg.mpr hs2) hpos.le
        have p2 := mul_pos hA (sub_pos.mpr hn2)
        linarith
    · constructor
      · intro h
        by_contra h'
        have hn2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [not_lt.mp h']
        have hs2 : 1 < ‖σ z‖ ^ 2 := by nlinarith
        have p1 := mul_pos (sub_pos.mpr hs2) hpos
        have p2 := mul_nonneg hA.le (sub_nonneg.mpr hn2)
        linarith
      · intro h
        by_contra h'
        have hs2 : ‖σ z‖ ^ 2 ≤ 1 := by nlinarith [not_lt.mp h']
        have hn2 : 1 < ‖z‖ ^ 2 := by nlinarith
        have p1 := mul_nonneg (sub_nonneg.mpr hs2) hpos.le
        have p2 := mul_pos hA (sub_pos.mpr hn2)
        linarith
  have himD : σ '' unitDisc = unitDisc := by
    have hD : ∀ z ∈ unitDisc, σ z ∈ unitDisc := fun z hz => by
      have hz1 := mem_ball_zero_iff.mp hz
      have hza : z ≠ a := fun h => by rw [h] at hz1; linarith
      exact mem_ball_zero_iff.mpr ((hσn z hza).1.2 hz1)
    exact Subset.antisymm (image_subset_iff.mpr hD)
      fun w hw => ⟨σ w, hD w hw, hσσ w⟩
  have himE : σ '' unitDiscExterior = unitDiscExterior := by
    have hE : ∀ z ∈ unitDiscExterior, σ z ∈ unitDiscExterior := fun z hz => by
      rcases eq_or_ne z a with rfl | hza
      · rw [hσa]
        exact hz
      · exact (hσn z hza).2.2 hz
    exact Subset.antisymm (image_subset_iff.mpr hE)
      fun w hw => ⟨σ w, hE w hw, hσσ w⟩
  -- quasiconformality off `a`
  have hq1 := thm7_1_comp (tp_b1_M_isKQC a a hc) hF (subset_univ _)
  have hsub : (F ∘ fun z : ℂ => a + c * (z - a)⁻¹) '' {a}ᶜ ⊆ {F a}ᶜ := by
    rintro _ ⟨z, hz, rfl⟩ h
    have heq := hF.2.2.1.2.1 (mem_univ _) (mem_univ _) (mem_singleton_iff.mp h)
    have hz' : z ≠ a := hz
    exact hσne z hz' (by rw [hσ]; exact heq)
  have hq2 := thm7_1_comp hq1 (tp_b1_M_isKQC (F a) 0 one_ne_zero) hsub
  rw [one_mul, mul_one] at hq2
  -- homeomorphism of the plane (the `nxInvConj` trick of `tp_b1_conj_isHomeomorphOnto`)
  obtain ⟨e, he⟩ := t1_homeomorph hF hFs
  set e₁ : ℂ ≃ₜ ℂ := ((Homeomorph.mulLeft₀ c hc).trans (Homeomorph.addLeft a)).trans
    (e.trans (Homeomorph.subRight (e a))) with he₁
  have h0 : e₁ 0 = 0 := by simp [he₁]
  obtain ⟨E, hE⟩ := nxI1_exists_homeo e₁ h0
  obtain ⟨G, hG⟩ : ∃ G : ℂ ≃ₜ ℂ, G = (Homeomorph.subRight a).trans E := ⟨_, rfl⟩
  have hGz : ∀ z, G z = invAt (F a) (F (σ z)) := fun z => by
    rw [hG, hσ, ← he]
    simp [hE, nxInvConj, he₁, invAt]
  have hGf : (⇑G : ℂ → ℂ) = fun z : ℂ => 0 + 1 * ((F ∘ fun z : ℂ => a + c * (z - a)⁻¹) z - F a)⁻¹ := by
    funext z
    rw [hGz, hσ]
    simp [invAt]
  have hHom := nxI1_isHomeomorphOnto_of_homeomorph G
  refine ⟨G, b4_isKQC_univ_of_punctured hHom (by rw [hGf]; exact hq2), hHom.2.2.1, ?_, ?_⟩
  · rw [show (⇑G) '' unitDisc = invAt (F a) '' (F '' (σ '' unitDisc)) by
      rw [image_image, image_image]
      exact image_congr fun z _ => hGz z, himD, h1]
  · rw [show (⇑G) '' unitDiscExterior = invAt (F a) '' (F '' (σ '' unitDiscExterior)) by
      rw [image_image, image_image]
      exact image_congr fun z _ => hGz z, himE, h2]

/-- Helper for `prop_chord_arc_quant`: `invAt y` is a bijection of `ℂ`, so it maps the curve
of a pair onto the curve of the image pair. -/
theorem s09_cq_curve (Ω Ωs : Set ℂ) (y : ℂ) :
    curveOf (invAt y '' Ω) (invAt y '' Ωs) = invAt y '' curveOf Ω Ωs := by
  have hbij : Function.Bijective (invAt y) := by
    refine ⟨fun u v h => ?_, fun w => ⟨w⁻¹ + y, ?_⟩⟩
    · have h' : (u - y)⁻¹ = (v - y)⁻¹ := h
      exact sub_left_injective (inv_injective h')
    · show (w⁻¹ + y - y)⁻¹ = w
      rw [add_sub_cancel_right, inv_inv]
  show (invAt y '' Ω ∪ invAt y '' Ωs)ᶜ = invAt y '' (Ω ∪ Ωs)ᶜ
  rw [← image_union, image_compl_eq hbij]

/-- Helper for `prop_chord_arc_quant`: `H^Ω(P) ≤ H(P)` for a bounded `K`-quasicircle, `H` the
quantity transported through `invAt x₀`, `x₀ ∈ Γ` (`eq_ambient_natural_side_inv`). -/
theorem s09_cq_side_le {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K) {x₀ : ℂ}
    (hx₀ : x₀ ∈ curveOf Ω Ωs) (P : ℂ × ℝ) (hP : P ∈ UHS) :
    ambHside Ω P ≤ ambHBdd Ω Ωs x₀ P := by
  have hx₀Ω : x₀ ∉ Ω := by
    simp only [curveOf, mem_compl_iff, mem_union, not_or] at hx₀
    exact hx₀.1
  have h := eq_ambient_natural_side_inv Ω (s09_bdd_riemann Ω Ωs (s09_cq_bjp hΓ)) x₀ hx₀Ω P hP
  show ambHside Ω P ≤ ambHside (invAt x₀ '' Ω) (invExt x₀ P) + _
  rw [h]
  exact le_self_add

/-- Helper for `prop_chord_arc_quant`: `diam τ(Γ) ≤ 2 / dist(y, Γ)` for `τ = invAt y`. -/
theorem s09_cq_diam (Γ : Set ℂ) (y : ℂ) (hd : 0 < infDist y Γ) :
    Metric.diam (invAt y '' Γ) ≤ 2 / infDist y Γ := by
  have hb : ∀ w ∈ invAt y '' Γ, ‖w‖ ≤ 1 / infDist y Γ := by
    rintro _ ⟨z, hz, rfl⟩
    have hle : infDist y Γ ≤ ‖z - y‖ := by
      rw [← dist_eq_norm, dist_comm]
      exact infDist_le_dist_of_mem hz
    have hpos : 0 < ‖z - y‖ := hd.trans_le hle
    show ‖(z - y)⁻¹‖ ≤ 1 / infDist y Γ
    rw [norm_inv, ← one_div]
    exact one_div_le_one_div_of_le hd hle
  refine Metric.diam_le_of_forall_dist_le (by positivity) fun u hu v hv => ?_
  calc dist u v ≤ ‖u‖ + ‖v‖ := by
        rw [dist_eq_norm]
        exact norm_sub_le u v
    _ ≤ 1 / infDist y Γ + 1 / infDist y Γ := add_le_add (hb u hu) (hb v hv)
    _ = 2 / infDist y Γ := by ring

/-- Helper for `prop_chord_arc_quant`: `lem_length` (with its constant `C`) under `H^Ω ≤ S` on
`ℍ³`: `Λ¹(Γ) ≤ C (1 + 260 S) diam Γ`. -/
theorem s09_cq_len {K : ℝ} (C : ℝ≥0) (hC : ∀ Ω Ωs : Set ℂ, IsBoundedKQuasicircle Ω Ωs K →
      ∀ x ∈ curveOf Ω Ωs,
        μH[1] (curveOf Ω Ωs) ≤ (C : ℝ≥0∞) *
          (1 + 260 * ambHside Ω (x, Metric.diam (curveOf Ω Ωs))) *
            ENNReal.ofReal (Metric.diam (curveOf Ω Ωs)))
    {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K) {S : ℝ} (hS : 0 ≤ S)
    (hSle : ∀ P ∈ UHS, ambHside Ω P ≤ ENNReal.ofReal S) {x : ℂ} (hx : x ∈ curveOf Ω Ωs) :
    μH[1] (curveOf Ω Ωs) ≤
      ENNReal.ofReal ((C : ℝ) * (1 + 260 * S) * Metric.diam (curveOf Ω Ωs)) := by
  have h := hC Ω Ωs hΓ x hx
  have he : ENNReal.ofReal ((C : ℝ) * (1 + 260 * S) * Metric.diam (curveOf Ω Ωs)) =
      (C : ℝ≥0∞) * (1 + 260 * ENNReal.ofReal S) * ENNReal.ofReal (Metric.diam (curveOf Ω Ωs)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul C.coe_nonneg,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_add zero_le_one (by positivity),
      ENNReal.ofReal_one, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [he]
  rcases eq_or_lt_of_le (Metric.diam_nonneg (s := curveOf Ω Ωs)) with hd | hd
  · rw [← hd, ENNReal.ofReal_zero, mul_zero] at h ⊢
    exact h
  · refine h.trans ?_
    gcongr
    exact hSle _ hd

/-- Helper for `prop_chord_arc_quant`: `H^Ω ≤ S` on `ℍ³` passes to `τ(Ω)`, `τ = invAt y`,
`y ∈ Ω*` (`eq_ambient_natural_side_inv`; `invExt y` maps `ℍ³` onto itself). -/
theorem s09_cq_side_inv {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K) {y : ℂ}
    (hy : y ∈ Ωs) {S : ℝ} (hSle : ∀ P ∈ UHS, ambHside Ω P ≤ ENNReal.ofReal S) :
    ∀ Q ∈ UHS, ambHside (invAt y '' Ω) Q ≤ ENNReal.ofReal S := by
  intro Q hQ
  obtain ⟨P, rfl⟩ := s09_invExt_surj y Q
  have hP : P ∈ UHS := by
    rw [← s09_invExt_UHS y]
    exact hQ
  obtain ⟨-, -, hdis, -⟩ := s09_bjp_basic Ω Ωs (s09_cq_bjp hΓ)
  have hyΩ : y ∉ Ω := fun h => hdis.ne_of_mem h hy rfl
  rw [eq_ambient_natural_side_inv Ω (s09_bdd_riemann Ω Ωs (s09_cq_bjp hΓ)) y hyΩ P hP]
  exact hSle P hP

/-- Helper for `prop_chord_arc_quant`, the proof of (i) ⇒ (iii) of `prop:chord-arc`
(`sec09-ambient.tex:925`): if `H^Ω ≤ S` on `ℍ³`, a bounded `K`-quasicircle is Ahlfors regular
with constant `β_K (1 + 260 S)` (corkscrew point `y ∈ Ω*`, `lem_length` for `invAt y` of the
curve, `lem_arc_facts_0` for the inverse map; the large-ball case by `lem_length` itself). -/
theorem s09_cq_ahlfors :
    ∀ K : ℝ, 1 ≤ K → ∃ β : ℝ, 0 < β ∧ ∀ Ω Ωs : Set ℂ, IsBoundedKQuasicircle Ω Ωs K →
      ∀ S : ℝ, 0 ≤ S → (∀ P ∈ UHS, ambHside Ω P ≤ ENNReal.ofReal S) →
        IsAhlforsRegular (curveOf Ω Ωs) (β * (1 + 260 * S)) := by
  intro K hK
  obtain ⟨c₂, hc₂, hcork⟩ := lem_corkscrew_bounded K
  obtain ⟨C, hC⟩ := lem_length K hK
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 2 * (C : ℝ) * (1 + 1 / c₂) ^ 2 / c₂ := ⟨_, rfl⟩
  have hA : 0 ≤ A := by
    rw [hAdef]
    positivity
  have hC0 : (0 : ℝ) ≤ C := C.coe_nonneg
  refine ⟨2 * A + 4 * C + 1, by positivity, fun Ω Ωs hΓ S hS hSle z r hr => ?_⟩
  have hS1 : 0 ≤ 1 + 260 * S := by positivity
  rcases (curveOf Ω Ωs ∩ ball z r).eq_empty_or_nonempty with he | ⟨x, hxΓ, hxb⟩
  · rw [he, measure_empty]
    exact zero_le
  have hsub : curveOf Ω Ωs ∩ ball z r ⊆ curveOf Ω Ωs ∩ ball x (2 * r) := by
    rintro w ⟨hwΓ, hwb⟩
    refine ⟨hwΓ, ?_⟩
    rw [mem_ball] at hwb hxb ⊢
    calc dist w x ≤ dist w z + dist x z := dist_triangle_right _ _ _
      _ < 2 * r := by linarith
  rcases le_or_gt (2 * r) (Metric.diam (curveOf Ω Ωs) / 2) with hcase | hcase
  · -- small balls: corkscrew point `y ∈ Ω*`, `lem_length` for `invAt y` of the curve, and
    -- `lem_arc_facts_0` for the inverse map `u ↦ u⁻¹ + y`
    obtain ⟨-, -, ym, hym, -, -, -, hhi, -, hinf⟩ :=
      hcork Ω Ωs hΓ x hxΓ (2 * r) (by positivity) hcase
    have hd0 : 0 < c₂ * (2 * r) := by positivity
    have hd : 0 < infDist ym (curveOf Ω Ωs) := hd0.trans_le hinf
    have hwd : ∀ w ∈ curveOf Ω Ωs, c₂ * (2 * r) ≤ ‖w - ym‖ := fun w hw => hinf.trans (by
      rw [← dist_eq_norm, dist_comm]
      exact infDist_le_dist_of_mem hw)
    have hwR : ∀ w ∈ curveOf Ω Ωs ∩ ball x (2 * r), ‖w - ym‖ < 2 * r * (1 + 1 / c₂) := by
      rintro w ⟨-, hwb⟩
      have h1 : ‖w - x‖ < 2 * r := by
        rw [← dist_eq_norm]
        exact mem_ball.mp hwb
      have h2 : 2 * r * (1 + 1 / c₂) = 2 * r + 2 * r / c₂ := by ring
      calc ‖w - ym‖ = ‖(w - x) - (ym - x)‖ := by rw [sub_sub_sub_cancel_right]
        _ ≤ ‖w - x‖ + ‖ym - x‖ := norm_sub_le _ _
        _ < 2 * r * (1 + 1 / c₂) := by linarith
    have hτx : invAt ym x ∈ curveOf (invAt ym '' Ω) (invAt ym '' Ωs) := by
      rw [s09_cq_curve]
      exact mem_image_of_mem _ hxΓ
    have hL := s09_cq_len C hC (s09_cq_inv_qc hΓ hym) hS (s09_cq_side_inv hΓ hym hSle) hτx
    rw [s09_cq_curve] at hL
    have hdiam : Metric.diam (invAt ym '' curveOf Ω Ωs) ≤ 2 / (c₂ * (2 * r)) :=
      (s09_cq_diam _ ym hd).trans (div_le_div_of_nonneg_left (by norm_num) hd0 hinf)
    obtain ⟨E, hEdef⟩ : ∃ E : Set ℂ, E = invAt ym '' (curveOf Ω Ωs ∩ ball x (2 * r)) :=
      ⟨_, rfl⟩
    have hFE : curveOf Ω Ωs ∩ ball x (2 * r) ⊆ (fun u : ℂ => u⁻¹ + ym) '' E := fun w hw => by
      refine ⟨invAt ym w, by rw [hEdef]; exact mem_image_of_mem _ hw, ?_⟩
      show (w - ym)⁻¹⁻¹ + ym = w
      rw [inv_inv, sub_add_cancel]
    have hET : E ⊆ {u : ℂ | 1 / (2 * r * (1 + 1 / c₂)) ≤ ‖u‖} ∩
        closedBall 0 (1 / (c₂ * (2 * r))) := by
      rw [hEdef]
      rintro _ ⟨w, hw, rfl⟩
      have hlo := hwd w hw.1
      have hpos : 0 < ‖w - ym‖ := hd0.trans_le hlo
      have hn : ‖invAt ym w‖ = 1 / ‖w - ym‖ := by
        show ‖(w - ym)⁻¹‖ = _
        rw [norm_inv, one_div]
      refine ⟨?_, ?_⟩
      · show 1 / (2 * r * (1 + 1 / c₂)) ≤ ‖invAt ym w‖
        rw [hn]
        exact one_div_le_one_div_of_le hpos (hwR w hw).le
      · rw [mem_closedBall_zero_iff, hn]
        exact one_div_le_one_div_of_le hd0 hlo
    have hTc : IsClosed ({u : ℂ | 1 / (2 * r * (1 + 1 / c₂)) ≤ ‖u‖} ∩
        closedBall 0 (1 / (c₂ * (2 * r)))) :=
      (isClosed_le continuous_const continuous_norm).inter isClosed_closedBall
    have hclE := closure_minimal hET hTc
    have hEc : IsCompact (closure E) :=
      ((isCompact_closedBall 0 _).inter_left
        (isClosed_le continuous_const continuous_norm)).of_isClosed_subset isClosed_closure hclE
    have hEO : closure E ⊆ {0}ᶜ := fun u hu h0 => by
      have h : 1 / (2 * r * (1 + 1 / c₂)) ≤ ‖u‖ := (hclE hu).1
      rw [mem_singleton_iff.mp h0, norm_zero] at h
      have : 0 < 1 / (2 * r * (1 + 1 / c₂)) := by positivity
      linarith
    have hFd : DifferentiableOn ℂ (fun u : ℂ => u⁻¹ + ym) {0}ᶜ := fun u hu =>
      ((differentiableAt_inv (mem_compl_singleton_iff.mp hu)).add_const ym).differentiableWithinAt
    have hAF := lem_arc_facts_0 (fun u : ℂ => u⁻¹ + ym) {0}ᶜ E isOpen_compl_singleton hFd hEc hEO
    have hder : ∀ u ∈ E, ‖deriv (fun u : ℂ => u⁻¹ + ym) u‖ ≤ (2 * r * (1 + 1 / c₂)) ^ 2 := by
      rw [hEdef]
      rintro _ ⟨w, hw, rfl⟩
      rw [deriv_add_const, deriv_inv, norm_neg, norm_inv, norm_pow]
      show (‖(w - ym)⁻¹‖ ^ 2)⁻¹ ≤ _
      rw [norm_inv, inv_pow, inv_inv]
      exact pow_le_pow_left₀ (norm_nonneg _) (hwR w hw).le 2
    have hsup : sSup ((fun u => ‖deriv (fun u : ℂ => u⁻¹ + ym) u‖) '' E) ≤
        (2 * r * (1 + 1 / c₂)) ^ 2 :=
      Real.sSup_le (by rintro _ ⟨u, hu, rfl⟩; exact hder u hu) (by positivity)
    have hEb : μH[1] E ≤ ENNReal.ofReal ((C : ℝ) * (1 + 260 * S) * (2 / (c₂ * (2 * r)))) := by
      refine (measure_mono ?_).trans (hL.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hdiam (by positivity))))
      rw [hEdef]
      exact image_mono inter_subset_left
    have heq : (2 * r * (1 + 1 / c₂)) ^ 2 * ((C : ℝ) * (1 + 260 * S) * (2 / (c₂ * (2 * r)))) =
        2 * A * (1 + 260 * S) * r := by
      have hc₂' : c₂ ≠ 0 := hc₂.ne'
      have hr' : r ≠ 0 := hr.ne'
      rw [hAdef]
      field_simp
    calc μH[1] (curveOf Ω Ωs ∩ ball z r) ≤ μH[1] (curveOf Ω Ωs ∩ ball x (2 * r)) :=
          measure_mono hsub
      _ ≤ μH[1] ((fun u : ℂ => u⁻¹ + ym) '' E) := measure_mono hFE
      _ ≤ ENNReal.ofReal (sSup ((fun u => ‖deriv (fun u : ℂ => u⁻¹ + ym) u‖) '' E)) *
          μH[1] E := hAF
      _ ≤ ENNReal.ofReal ((2 * r * (1 + 1 / c₂)) ^ 2) *
          ENNReal.ofReal ((C : ℝ) * (1 + 260 * S) * (2 / (c₂ * (2 * r)))) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hsup) hEb
      _ = ENNReal.ofReal (2 * A * (1 + 260 * S) * r) := by
          rw [← ENNReal.ofReal_mul (by positivity), heq]
      _ ≤ ENNReal.ofReal ((2 * A + 4 * C + 1) * (1 + 260 * S) * r) := by
          apply ENNReal.ofReal_le_ofReal
          have h3 : 0 ≤ (1 + 260 * S) * r := by positivity
          nlinarith [mul_nonneg hC0 h3]
  · -- large balls: `Λ¹(Γ ∩ D(z, r)) ≤ Λ¹(Γ)`, `lem_length` itself, `diam Γ < 4 r`
    have hL := s09_cq_len C hC hΓ hS hSle hxΓ
    calc μH[1] (curveOf Ω Ωs ∩ ball z r) ≤ μH[1] (curveOf Ω Ωs) :=
          measure_mono inter_subset_left
      _ ≤ ENNReal.ofReal ((C : ℝ) * (1 + 260 * S) * Metric.diam (curveOf Ω Ωs)) := hL
      _ ≤ ENNReal.ofReal ((2 * A + 4 * C + 1) * (1 + 260 * S) * r) := by
          apply ENNReal.ofReal_le_ofReal
          have h1 : Metric.diam (curveOf Ω Ωs) ≤ 4 * r := by linarith
          have h2 : (C : ℝ) * (1 + 260 * S) * Metric.diam (curveOf Ω Ωs) ≤
              C * (1 + 260 * S) * (4 * r) := mul_le_mul_of_nonneg_left h1 (by positivity)
          have h3 : 0 ≤ (1 + 260 * S) * r := by positivity
          nlinarith [mul_nonneg hA h3]

/-- Proposition 9.13 `prop:chord-arc` (`sec09-ambient.tex:898`): for a bounded
`K`-quasicircle, (i) `sup_P H(P) < ∞` ⟺ (ii) `sup_P V(P) < ∞` ⟺ (iii) `Γ` is chord-arc. -/
theorem prop_chord_arc (K : ℝ) (hK : 1 ≤ K) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    (x₀ : ℂ) (hx₀ : x₀ ∈ curveOf Ω Ωs) :
    ((⨆ P ∈ UHS, ambHBdd Ω Ωs x₀ P) < ⊤ ↔ (⨆ P ∈ UHS, ambVBdd Ω Ωs x₀ P) < ⊤) ∧
      ((⨆ P ∈ UHS, ambHBdd Ω Ωs x₀ P) < ⊤ ↔ ∃ C : ℝ, IsChordArc (curveOf Ω Ωs) C) := by
  sorry

/-- Proposition 9.13 `prop:chord-arc`, quantitative part (`sec09-ambient.tex:905`): if
`S_H = sup H < ∞`, `Γ` is chord-arc with constant `4η_K(1) A₁`,
`A₁ = 2c₂⁻¹(1 + c₂⁻¹)² C_GM(K)(1 + 260 S_H)`, i.e. `α_K (1 + 260 S_H)` with `α_K` depending
only on `K`. -/
theorem prop_chord_arc_quant :
    ∀ K : ℝ, 1 ≤ K → ∃ α : ℝ, 0 < α ∧ ∀ Ω Ωs : Set ℂ, IsBoundedKQuasicircle Ω Ωs K →
      ∀ x₀ ∈ curveOf Ω Ωs, (⨆ P ∈ UHS, ambHBdd Ω Ωs x₀ P) < ⊤ →
        IsChordArc (curveOf Ω Ωs) (α * (1 + 260 * (⨆ P ∈ UHS, ambHBdd Ω Ωs x₀ P).toReal)) := by
  intro K hK
  obtain ⟨β, hβ, hA⟩ := s09_cq_ahlfors K hK
  obtain ⟨Cbt, hbt⟩ := lem_arc_facts_4 K hK
  refine ⟨β * max Cbt 1, mul_pos hβ (lt_of_lt_of_le one_pos (le_max_right _ _)),
    fun Ω Ωs hΓ x₀ hx₀ hfin => ?_⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = (⨆ P ∈ UHS, ambHBdd Ω Ωs x₀ P).toReal := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hSdef]
    exact ENNReal.toReal_nonneg
  have hSle : ∀ P ∈ UHS, ambHside Ω P ≤ ENNReal.ofReal S := by
    intro P hP
    rw [hSdef, ENNReal.ofReal_toReal hfin.ne]
    exact (s09_cq_side_le hΓ hx₀ P hP).trans (le_iSup₂_of_le P hP le_rfl)
  have hAR := hA Ω Ωs hΓ S hS0 hSle
  have hbt' : HasBoundedTurning (curveOf Ω Ωs) (max Cbt 1) := by
    intro x hx y hy hxy
    obtain ⟨γ, hγ, hdiam⟩ := hbt Ω Ωs hΓ x hx y hy hxy
    exact ⟨γ, hγ, hdiam.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)⟩
  have hca := lem_arc_facts_2 _ (s09_cq_jordanC hΓ) _ _ hAR hbt'
  rw [← hSdef]
  have e : β * max Cbt 1 * (1 + 260 * S) = β * (1 + 260 * S) * max Cbt 1 := by ring
  rw [e]
  exact hca

/-- Example 9.15 `ex:nonrect` (`sec09-ambient.tex:988`): there is a bounded BMO quasicircle
with `H(P) = V(P) = ∞` for every `P`, while `sup_{p ∈ Ω} K_V(p) < ∞` (for every label). -/
theorem ex_nonrect :
    ∃ Ω Ωs : Set ℂ, IsBMOQuasicircle Ω Ωs ∧
      (∀ x₀ ∈ curveOf Ω Ωs, ∀ P ∈ UHS, ambHBdd Ω Ωs x₀ P = ⊤ ∧ ambVBdd Ω Ωs x₀ P = ⊤) ∧
      ∀ x₀ ∈ curveOf Ω Ωs, ∀ lab : ℂ × ℝ → ℂ, IsLabel (invPairΩ Ω x₀) lab →
        (⨆ p ∈ Ω, KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ p)) < ⊤ := by
  sorry

/-- Remark 9.16 `rem:ambient-intrinsic` (`sec09-ambient.tex:1023`): chord-arc bounded
quasicircles are BMO quasicircles. -/
theorem rem_ambient_intrinsic_a (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    (h : ∃ C : ℝ, IsChordArc (curveOf Ω Ωs) C) : IsBMOQuasicircle Ω Ωs := by
  sorry

/-- Remark 9.16 `rem:ambient-intrinsic` (`sec09-ambient.tex:1031`): the inclusion of chord-arc
curves in BMO quasicircles is strict. -/
theorem rem_ambient_intrinsic_b :
    ∃ Ω Ωs : Set ℂ, IsBMOQuasicircle Ω Ωs ∧ ¬ ∃ C : ℝ, IsChordArc (curveOf Ω Ωs) C := by
  sorry

/-- Remark 9.16 `rem:ambient-intrinsic` (`sec09-ambient.tex:1039`): there is no inequality
`V(P) ≤ C K_V(p)` for any assignment `P ↦ p` and any constant `C`, even for BMO
quasicircles. -/
theorem rem_ambient_intrinsic_c :
    ∃ Ω Ωs : Set ℂ, IsBMOQuasicircle Ω Ωs ∧ ∀ x₀ ∈ curveOf Ω Ωs, ∀ lab : ℂ × ℝ → ℂ,
      IsLabel (invPairΩ Ω x₀) lab → ∀ C : ℝ≥0, ∀ π' : ℂ × ℝ → ℂ, (∀ P ∈ UHS, π' P ∈ Ω) →
        ∃ P ∈ UHS, ¬ ambVBdd Ω Ωs x₀ P ≤
          (C : ℝ≥0∞) * KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ (π' P)) := by
  sorry

end EpsteinVMO
