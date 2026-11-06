import EpsteinVMO.S04_Tube
import TauCeti.Analysis.PDE.MaximumPrinciple.Drift
import TauCeti.Analysis.PDE.Regularity.Smooth
import TauCeti.Analysis.Sobolev.Wkp.Leibniz
import TauCeti.MeasureTheory.Function.LocalRepresentative
import TauCeti.Analysis.PDE.Regularity.HalfSpace
import TauCeti.Analysis.PDE.Regularity.DifferentiatedEquation
import TauCeti.Analysis.Sobolev.W1p.ChangeOfVariables
import TauCeti.Analysis.Sobolev.W1p.Localization
import TauCeti.Analysis.Sobolev.Trace.Continuous

/-! # W-PDE1: the bridge `ℂ ≃ ℝ²` and the weak Dirichlet problem

Stages P1 and P2 of W-PDE1 (see `collaboration/w2_pde_INTERFACE.md`).

* P1: the isometry `e = Complex.orthonormalBasisOneI.repr : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)`
  carries the frame `(1, i)` (`frameVec`) to the standard basis, preserves Lebesgue measure and
  transports open sets, closures and smoothness.
* P2: weak existence and uniqueness in `H¹₀(Ω)` on a bounded open `Ω ⊆ ℝ²` for
  `-∂ᵢ(Aⁱʲ∂ⱼu) + βʲ∂ⱼu + γu = f`, with `A` continuous on `Ω̄` and `ε'`-close to the identity,
  `β`, `γ` continuous on `Ω̄` and `γ ≥ 0`. The drift may be of any size: this is the vendored
  TauCeti theorem `UniformlyEllipticOn.existsUnique_isWeakSolutionDirichlet_of_mass_nonneg`
  (`TauCeti/Analysis/PDE/MaximumPrinciple/Drift.lean`, from `D:/lean/external/TauCeti`, a3d94a3f).
* P3: interior regularity. If moreover `A`, `β`, `γ` and the data are smooth on `Ω`, the weak
  solution has a representative smooth on `Ω` solving the equation pointwise (bootstrap with
  TauCeti's interior `H^{k+2}` theorem, `Regularity/HigherOrder.lean`, and smooth representatives,
  `Regularity/Smooth.lean`).
-/

open Complex Set Metric Filter Topology MeasureTheory TopologicalSpace Matrix
open scoped ENNReal NNReal Real ContDiff

noncomputable section

namespace EpsteinVMO

/-- W-PDE1 P1-1: the isometry `e = Complex.orthonormalBasisOneI.repr : ℂ ≃ ℝ²` maps the frame
`(1, i)` to the standard basis. -/
theorem pde_e_frame (j : Fin 2) :
    Complex.orthonormalBasisOneI.repr (frameVec j) = EuclideanSpace.single j 1 := by
  ext i
  fin_cases j <;> fin_cases i <;> simp [frameVec]

/-- W-PDE1 P1-2: derivatives of a pulled-back function in the frame `(1, i)` are the partial
derivatives on `ℝ²`. -/
theorem pde_fderiv_comp {v : EuclideanSpace ℝ (Fin 2) → ℝ} {z : ℂ}
    (hv : DifferentiableAt ℝ v (Complex.orthonormalBasisOneI.repr z)) (j : Fin 2) :
    fderiv ℝ (fun z => v (Complex.orthonormalBasisOneI.repr z)) z (frameVec j) =
      fderiv ℝ v (Complex.orthonormalBasisOneI.repr z) (EuclideanSpace.single j 1) := by
  have _hv := hv
  have h := (Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv).comp_right_fderiv
    (f := v) (x := z)
  change fderiv ℝ (v ∘ Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv) z
    (frameVec j) = _
  rw [h]
  simp [pde_e_frame]

/-- W-PDE1 P1-3: `e` preserves Lebesgue measure. -/
theorem pde_e_measurePreserving :
    MeasurePreserving Complex.orthonormalBasisOneI.repr
      (volume : Measure ℂ) (volume : Measure (EuclideanSpace ℝ (Fin 2))) :=
  Complex.orthonormalBasisOneI.repr.measurePreserving

/-- W-PDE1 P1-4: images of open sets with compact closure. -/
theorem pde_e_image {D' : Set ℂ} (hD' : IsOpen D') (hc : IsCompact (closure D')) :
    IsOpen (Complex.orthonormalBasisOneI.repr '' D') ∧
      Bornology.IsBounded (Complex.orthonormalBasisOneI.repr '' D') ∧
      closure (Complex.orthonormalBasisOneI.repr '' D') =
        Complex.orthonormalBasisOneI.repr '' closure D' := by
  set h := Complex.orthonormalBasisOneI.repr.toHomeomorph
  refine ⟨h.isOpenMap _ hD', ?_, (h.image_closure D').symm⟩
  exact ((hc.image h.continuous).isBounded).subset (image_mono subset_closure)

/-- W-PDE1 P1-5: smoothness transfers along `e⁻¹`. -/
theorem pde_contDiffOn_comp_symm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℂ → F} {D : Set ℂ} (hg : ContDiffOn ℝ ∞ g D) :
    ContDiffOn ℝ ∞ (fun x => g (Complex.orthonormalBasisOneI.repr.symm x))
      (Complex.orthonormalBasisOneI.repr '' D) := by
  refine hg.comp Complex.orthonormalBasisOneI.repr.symm.contDiff.contDiffOn ?_
  rintro _ ⟨z, hz, rfl⟩
  simpa using hz

/-- W-PDE1 P2 helper: on `EuclideanSpace ℝ (Fin 2)` the squared norm is the self dot product. -/
theorem pde_norm_sq_eq_dot (ξ : EuclideanSpace ℝ (Fin 2)) : ‖ξ‖ ^ 2 = ⇑ξ ⬝ᵥ ⇑ξ := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- W-PDE1 P2/P3 helper: a coefficient matrix continuous on `Ω̄` and `ε'`-close to the identity
(`ε' < 1`) is uniformly elliptic on the bounded open set `Ω`, with ellipticity constant `1 - ε'`
and an upper constant that also bounds the operator norm of the associated bilinear forms. -/
theorem pde_uniformlyEllipticOn {Ω : Opens (EuclideanSpace ℝ (Fin 2))}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 2)))) {ε' : ℝ} (hε : ε' < 1)
    {A : EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ∀ i j, ContinuousOn (fun x => A x i j) (closure (Ω : Set (EuclideanSpace ℝ (Fin 2)))))
    (hell : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin 2))), ∀ ξ : Fin 2 → ℝ,
      |ξ ⬝ᵥ (A x *ᵥ ξ) - ξ ⬝ᵥ ξ| ≤ ε' * (ξ ⬝ᵥ ξ)) :
    ∃ Lam : ℝ, TauCeti.PDE.UniformlyEllipticOn (Ω : Set (EuclideanSpace ℝ (Fin 2))) A (1 - ε') Lam ∧
      ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin 2))), ‖TauCeti.PDE.matrixBilinearForm (A x)‖ ≤ Lam := by
  set S := closure (Ω : Set (EuclideanSpace ℝ (Fin 2)))
  have hS : IsCompact S := hb.isCompact_closure
  have hΩS : (Ω : Set (EuclideanSpace ℝ (Fin 2))) ⊆ S := subset_closure
  -- an entrywise bound for `A` on the compact closure
  obtain ⟨K, hK⟩ := hS.exists_bound_of_continuousOn
    (f := fun x => ∑ i, ∑ j, |A x i j|)
    (continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => (hA i j).abs)
  have hnorm : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin 2))),
      ‖TauCeti.PDE.matrixBilinearForm (A x)‖ ≤ max (1 - ε') K := by
    intro x hx
    have h1 := TauCeti.PDE.norm_matrixBilinearForm_le_sum_abs (A x)
    have h2 : ‖∑ i, ∑ j, |A x i j|‖ ≤ K := hK x (hΩS hx)
    rw [Real.norm_of_nonneg (by positivity)] at h2
    exact h1.trans (h2.trans (le_max_right _ _))
  refine ⟨max (1 - ε') K, ?_, hnorm⟩
  refine TauCeti.PDE.UniformlyEllipticOn.of_bounds (by linarith) (le_max_left _ _)
    (fun {x} hx ξ => ?_) (fun {x} hx η ξ => ?_)
  · rw [Matrix.toQuadraticForm'_apply, pde_norm_sq_eq_dot]
    have h1 := hell x hx ξ
    have h2 := (abs_le.1 h1).1
    nlinarith
  · have h3 := (TauCeti.PDE.matrixBilinearForm (A x)).le_opNorm₂ η ξ
    rw [TauCeti.PDE.matrixBilinearForm_apply, Real.norm_eq_abs] at h3
    refine h3.trans ?_
    gcongr
    exact hnorm x hx

/-- W-PDE1 P2 deliverable: weak existence and uniqueness on `ℝ²` for
`-∂ᵢ(Aⁱʲ∂ⱼu) + βʲ∂ⱼu + γu = f`, `u ∈ H¹₀(Ω)`, with `A` continuous on `Ω̄` and `ε'`-close to `I`
(`ε' < 1`), `β`, `γ` continuous on `Ω̄` and `γ ≥ 0`; `Ω` bounded. The drift may be of any size
(TauCeti `UniformlyEllipticOn.existsUnique_isWeakSolutionDirichlet_of_mass_nonneg`, vendored). -/
theorem pde_weak_exists_unique {Ω : Opens (EuclideanSpace ℝ (Fin 2))}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 2)))) {ε' : ℝ} (hε0 : 0 ≤ ε')
    (hε : ε' < 1) {A : EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ}
    {β : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)} {γ : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hA : ∀ i j, ContinuousOn (fun x => A x i j) (closure (Ω : Set (EuclideanSpace ℝ (Fin 2)))))
    (hβ : ContinuousOn β (closure (Ω : Set (EuclideanSpace ℝ (Fin 2)))))
    (hγ : ContinuousOn γ (closure (Ω : Set (EuclideanSpace ℝ (Fin 2)))))
    (hell : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin 2))), ∀ ξ : Fin 2 → ℝ,
      |ξ ⬝ᵥ (A x *ᵥ ξ) - ξ ⬝ᵥ ξ| ≤ ε' * (ξ ⬝ᵥ ξ))
    (hγ0 : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin 2))), 0 ≤ γ x)
    (f : Lp ℝ 2 ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω)) :
    ∃! u : TauCeti.W1p0 (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω 2,
      TauCeti.PDE.IsWeakSolutionDirichlet A β γ f u := by
  have _hε0 := hε0
  set S := closure (Ω : Set (EuclideanSpace ℝ (Fin 2)))
  have hS : IsCompact S := hb.isCompact_closure
  have hΩS : (Ω : Set (EuclideanSpace ℝ (Fin 2))) ⊆ S := subset_closure
  have hAc : ContinuousOn A S := continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hA i j
  -- bounds for `β` and `γ` on the compact closure; uniform ellipticity of `A`
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hβ
  obtain ⟨G, hG⟩ := hS.exists_bound_of_continuousOn hγ
  obtain ⟨Lam, hell', -⟩ := pde_uniformlyEllipticOn hb hε hA hell
  have hmeas : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin 2))) := Ω.isOpen.measurableSet
  -- `Matrix` carries no global metric; borrow the product one (as TauCeti `Regularity/Basic`)
  let : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℝ))
  exact hell'.existsUnique_isWeakSolutionDirichlet_of_mass_nonneg
    ((hAc.mono hΩS).aestronglyMeasurable hmeas) ((hβ.mono hΩS).aestronglyMeasurable hmeas)
    ((hγ.mono hΩS).aestronglyMeasurable hmeas) (fun x hx => hB x (hΩS hx))
    (fun x hx => hG x (hΩS hx)) hγ0 hb f

local notation "X" => EuclideanSpace ℝ (Fin 2)

/-- W-PDE1 P3-1: with bounded measurable coefficients, the drift and mass terms of the energy
form split off as an integral: `a(u, v) = ∫ ⟨A∇u, ∇v⟩ + ∫ (⟪β, ∇u⟫ + γ u) v`. -/
theorem pde_energy_split {Ω : Opens X} {A : X → Matrix (Fin 2) (Fin 2) ℝ} {β : X → X} {γ : X → ℝ}
    {K B G : ℝ} (hAm : AEStronglyMeasurable (fun x => TauCeti.PDE.matrixBilinearForm (A x))
      ((volume : Measure X).restrict Ω))
    (hβm : AEStronglyMeasurable β ((volume : Measure X).restrict Ω))
    (hγm : AEStronglyMeasurable γ ((volume : Measure X).restrict Ω))
    (hA : ∀ x ∈ (Ω : Set X), ‖TauCeti.PDE.matrixBilinearForm (A x)‖ ≤ K)
    (hβ : ∀ x ∈ (Ω : Set X), ‖β x‖ ≤ B) (hγ : ∀ x ∈ (Ω : Set X), |γ x| ≤ G)
    (u v : TauCeti.W1p (volume : Measure X) Ω 2) :
    TauCeti.PDE.energyFormH1 A β γ u v =
      TauCeti.PDE.energyFormH1 A 0 0 u v +
        ∫ x in (Ω : Set X), (inner ℝ (β x) (TauCeti.W1p.gradient u x) +
          γ x * TauCeti.W1p.value u x) * TauCeti.W1p.value v x := by
  let : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℝ))
  -- the entries of `A` are the bilinear form on the standard basis
  have hM : Continuous fun T : X →L[ℝ] X →L[ℝ] ℝ =>
      Matrix.of fun i j => T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
    continuous_matrix fun i j =>
      ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))).comp
        (ContinuousLinearMap.apply ℝ _ (EuclideanSpace.single i (1 : ℝ)))).continuous
  have hAm' : AEStronglyMeasurable A ((volume : Measure X).restrict Ω) := by
    refine (hM.comp_aestronglyMeasurable hAm).congr (ae_of_all _ fun x => ?_)
    ext i j
    simp [TauCeti.PDE.matrixBilinearForm_apply]
  have hK : 0 ≤ max K 0 := le_max_right _ _
  have hAb : ∀ x ∈ (Ω : Set X), ∀ η ξ : X, |η ⬝ᵥ (A x *ᵥ ξ)| ≤ max K 0 * ‖η‖ * ‖ξ‖ := by
    intro x hx η ξ
    have h := (TauCeti.PDE.matrixBilinearForm (A x)).le_opNorm₂ η ξ
    rw [TauCeti.PDE.matrixBilinearForm_apply, Real.norm_eq_abs] at h
    refine h.trans ?_
    gcongr
    exact (hA x hx).trans (le_max_left _ _)
  have hP := TauCeti.PDE.integrable_energyIntegrand_jetField
    (TauCeti.PDE.memLp_energyIntegrand_of_bounds (b := fun _ => 0) (c := fun _ => 0)
      (beta := 0) (gamma := 0) hK hAm' aestronglyMeasurable_const aestronglyMeasurable_const hAb
      (fun _ _ => by simp) (fun _ _ => by simp)) u v
  have hL := TauCeti.PDE.integrable_energyIntegrand_jetField
    (TauCeti.PDE.memLp_energyIntegrand_of_bounds (a := fun _ => 0) (Lam := 0) le_rfl
      aestronglyMeasurable_const hβm hγm (fun _ _ _ _ => by simp) hβ
      (fun x hx => by simpa [Real.norm_eq_abs] using hγ x hx)) u v
  have hL' : Integrable (fun x => (inner ℝ (β x) (TauCeti.W1p.gradient u x) +
      γ x * TauCeti.W1p.value u x) * TauCeti.W1p.value v x) ((volume : Measure X).restrict Ω) := by
    refine hL.congr (ae_of_all _ fun x => ?_)
    simp [TauCeti.PDE.energyIntegrand_apply, TauCeti.PDE.matrixBilinearForm_apply]
    ring
  rw [TauCeti.PDE.energyFormH1_def, TauCeti.PDE.energyFormH1_def]
  simp only [Pi.zero_apply]
  rw [← integral_add hP hL']
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [TauCeti.PDE.energyIntegrand_apply, TauCeti.PDE.matrixBilinearForm_apply]
  ring

/-- W-PDE1 P3 helper: on an open set of finite measure, the constant `1` lies in every
`W^{k,2}`. -/
theorem pde_wkp_one {V : Opens X} (hV : (volume : Measure X) V < ⊤) (k : ℕ) :
    ∃ w : TauCeti.Wkp (volume : Measure X) V 2 k,
      (TauCeti.Wkp.value k w : X → ℝ) =ᵐ[(volume : Measure X).restrict V] fun _ => 1 := by
  have : IsFiniteMeasure ((volume : Measure X).restrict V) := isFiniteMeasure_restrict.2 hV.ne
  have h1 : MemLp (fun _ : X => (1 : ℝ)) 2 ((volume : Measure X).restrict V) := memLp_const 1
  cases k with
  | zero => exact ⟨h1.toLp _, by rw [TauCeti.Wkp.value_zero]; exact h1.coeFn_toLp⟩
  | succ k =>
    have hd : ∀ i, ∃ d : TauCeti.Wkp (volume : Measure X) V 2 k,
        TauCeti.HasWeakLineDerivOn (volume : Measure X) V (h1.toLp _ : X → ℝ)
          (TauCeti.Wkp.value k d) (EuclideanSpace.basisFun (Fin 2) ℝ i) := fun i => by
      refine ⟨0, ((TauCeti.hasWeakLineDerivOn_const (1 : ℝ)).congr_ae
        h1.coeFn_toLp.symm).congr_ae_deriv ?_⟩
      rw [← TauCeti.Wkp.valueL_apply, map_zero]
      exact (Lp.coeFn_zero _ _ _).symm
    obtain ⟨w, hw⟩ := TauCeti.Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn
      (EuclideanSpace.basisFun (Fin 2) ℝ) _ k hd
    exact ⟨w, by rw [hw]; exact h1.coeFn_toLp⟩

/-- W-PDE1 P3-2 (one bootstrap step for the data): on `V ⋐ Ω`, if `u ∈ H^{k+1}(V)` then the
effective right-hand side `F - ⟪β, ∇u⟫ - γ u` lies in `H^k(V)`, for `β`, `γ`, `F` smooth on `Ω`. -/
theorem pde_rhs_Wk {Ω V : Opens X} (hV : IsCompact (closure (V : Set X)))
    (hVΩ : closure (V : Set X) ⊆ Ω) {β : X → X} {γ F : X → ℝ}
    (hβ : ContDiffOn ℝ ∞ β Ω) (hγ : ContDiffOn ℝ ∞ γ Ω) (hF : ContDiffOn ℝ ∞ F Ω)
    {u : TauCeti.W1p (volume : Measure X) Ω 2} (k : ℕ)
    (hu : ∃ w : TauCeti.Wkp (volume : Measure X) V 2 (k + 1),
      (TauCeti.Wkp.value (k + 1) w : X → ℝ) =ᵐ[(volume : Measure X).restrict V]
        TauCeti.W1p.value u) :
    ∃ g : TauCeti.Wkp (volume : Measure X) V 2 k,
      (TauCeti.Wkp.value k g : X → ℝ) =ᵐ[(volume : Measure X).restrict V]
        fun x => F x - inner ℝ (β x) (TauCeti.W1p.gradient u x) - γ x * TauCeti.W1p.value u x := by
  obtain ⟨w, hw⟩ := hu
  have hVle : V ≤ Ω := fun x hx => hVΩ (subset_closure hx)
  have hVfin : (volume : Measure X) V < ⊤ :=
    lt_of_le_of_lt (measure_mono subset_closure) hV.measure_lt_top
  -- the data term
  obtain ⟨o, ho⟩ := pde_wkp_one hVfin k
  obtain ⟨gF, hgF⟩ := TauCeti.Wkp.exists_value_ae_eq_mul_of_contDiffOn Ω.isOpen hV hVΩ k hF o
  -- the mass term
  obtain ⟨gγ, hgγ⟩ := TauCeti.Wkp.exists_value_ae_eq_mul_of_contDiffOn Ω.isOpen hV hVΩ k hγ
    (TauCeti.Wkp.lowerOrder k w)
  -- the drift term, one direction at a time
  have hdir : ∀ j : Fin 2, ∃ m : TauCeti.Wkp (volume : Measure X) V 2 k,
      (TauCeti.Wkp.value k m : X → ℝ) =ᵐ[(volume : Measure X).restrict V]
        fun x => β x j * TauCeti.W1p.gradient u x j := by
    intro j
    obtain ⟨d, hd⟩ := TauCeti.Wkp.exists_hasWeakLineDerivOn_value k w (EuclideanSpace.single j 1)
    have hu' := ((TauCeti.W1p.hasWeakFDerivOn u).mono hVle).hasWeakLineDerivOn
      (EuclideanSpace.single j (1 : ℝ))
    have hde := hd.ae_eq (hu'.congr_ae hw.symm)
    have hβj : ContDiffOn ℝ ∞ (fun x => β x j) Ω :=
      (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn hβ
    obtain ⟨m, hm⟩ := TauCeti.Wkp.exists_value_ae_eq_mul_of_contDiffOn Ω.isOpen hV hVΩ k hβj d
    refine ⟨m, ?_⟩
    filter_upwards [hm, hde] with x hx hx'
    rw [hx, hx']
    simp [EuclideanSpace.inner_single_right]
  obtain ⟨m0, hm0⟩ := hdir 0
  obtain ⟨m1, hm1⟩ := hdir 1
  refine ⟨gF - (m0 + m1) - gγ, ?_⟩
  have hval : TauCeti.Wkp.value k (gF - (m0 + m1) - gγ) =
      TauCeti.Wkp.value k gF - (TauCeti.Wkp.value k m0 + TauCeti.Wkp.value k m1) -
        TauCeti.Wkp.value k gγ := by
    simp only [← TauCeti.Wkp.valueL_apply, map_sub, map_add]
  rw [hval]
  filter_upwards [Lp.coeFn_sub (TauCeti.Wkp.value k gF - (TauCeti.Wkp.value k m0 +
      TauCeti.Wkp.value k m1)) (TauCeti.Wkp.value k gγ),
    Lp.coeFn_sub (TauCeti.Wkp.value k gF) (TauCeti.Wkp.value k m0 + TauCeti.Wkp.value k m1),
    Lp.coeFn_add (TauCeti.Wkp.value k m0) (TauCeti.Wkp.value k m1), hgF, ho, hgγ, hm0, hm1, hw]
    with x h1 h2 h3 hF' ho' hγ' h0 h1' hw'
  rw [h1, Pi.sub_apply, h2, Pi.sub_apply, h3, Pi.add_apply, hF', ho', hγ', h0, h1',
    ← TauCeti.Wkp.value_succ, hw']
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
  ring

/-- W-PDE1 P3-3 (bootstrap): a weak solution of `-∂ᵢ(Aⁱʲ∂ⱼu) = F - ⟪β, ∇u⟫ - γ u` on `Ω`, with
`A` uniformly elliptic and smooth and `β`, `γ`, `F` smooth on `Ω`, lies in `H^{k+1}(V)` for every
`k` and every `V ⋐ Ω`. -/
theorem pde_Hk_loc {Ω : Opens X} {A : X → Matrix (Fin 2) (Fin 2) ℝ} {lam Lam : ℝ}
    (hell : TauCeti.PDE.UniformlyEllipticOn (Ω : Set X) A lam Lam)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) Ω) {β : X → X} {γ F : X → ℝ}
    (hβ : ContDiffOn ℝ ∞ β Ω) (hγ : ContDiffOn ℝ ∞ γ Ω) (hF : ContDiffOn ℝ ∞ F Ω)
    {u : TauCeti.W1p (volume : Measure X) Ω 2}
    (hu : ∀ v : TauCeti.W1p0 (volume : Measure X) Ω 2,
      TauCeti.PDE.energyFormH1 A 0 0 u (v : TauCeti.W1p (volume : Measure X) Ω 2) =
        ∫ x in (Ω : Set X), (F x - inner ℝ (β x) (TauCeti.W1p.gradient u x) -
          γ x * TauCeti.W1p.value u x) *
            TauCeti.W1p.value (v : TauCeti.W1p (volume : Measure X) Ω 2) x)
    (k : ℕ) {V : Opens X} (hV : IsCompact (closure (V : Set X)))
    (hVΩ : closure (V : Set X) ⊆ Ω) :
    ∃ w : TauCeti.Wkp (volume : Measure X) V 2 (k + 1),
      (TauCeti.Wkp.value (k + 1) w : X → ℝ) =ᵐ[(volume : Measure X).restrict V]
        TauCeti.W1p.value u := by
  induction k generalizing V with
  | zero =>
    have hVle : V ≤ Ω := fun x hx => hVΩ (subset_closure hx)
    let w : TauCeti.Wkp (volume : Measure X) V 2 1 := TauCeti.W1p.restrictL hVle u
    refine ⟨w, ?_⟩
    change (TauCeti.Wkp.value 1 w : X → ℝ) =ᵐ[(volume : Measure X).restrict V] _
    rw [TauCeti.Wkp.value_one]
    exact TauCeti.W1p.value_restrictL_ae hVle u
  | succ k ih =>
    obtain ⟨V', hV'o, hVV', hV'Ω, hV'c⟩ :=
      exists_open_between_and_isCompact_closure hV Ω.isOpen hVΩ
    set W : Opens X := ⟨V', hV'o⟩
    have hWle : W ≤ Ω := fun x hx => hV'Ω (subset_closure hx)
    have hWΩ : (W : Set X) ⊆ Ω := fun x hx => hWle hx
    -- the effective data lies in `H^k(W)` because `u ∈ H^{k+1}(W)`
    obtain ⟨G, hG⟩ := pde_rhs_Wk (V := W) hV'c hV'Ω hβ hγ hF k (ih hV'c hV'Ω)
    have huW : ∀ v : TauCeti.W1p0 (volume : Measure X) W 2,
        TauCeti.PDE.energyFormH1 A 0 0 (TauCeti.W1p.restrictL hWle u)
          (v : TauCeti.W1p (volume : Measure X) W 2) =
        ∫ x in (W : Set X), TauCeti.Wkp.value k G x *
          TauCeti.W1p.value (v : TauCeti.W1p (volume : Measure X) W 2) x := by
      intro v
      rw [TauCeti.PDE.energyFormH1_restrictL_eq_setIntegral hWle hu v]
      refine integral_congr_ae ?_
      filter_upwards [hG] with x hx
      rw [hx]
    -- interior `H^{k+2}` regularity on `V ⋐ W` (TauCeti `Regularity/HigherOrder.lean`)
    obtain ⟨U, hU⟩ := (hell.mono_set hWΩ).exists_value_eq_value_restrictL_of_contDiffOn
      (fun i j => (hA i j).mono hWΩ) k huW hV hVV'
    refine ⟨U, ?_⟩
    rw [hU]
    have hVW : V ≤ W := SetLike.coe_subset_coe.mp (subset_closure.trans hVV')
    have h1 := TauCeti.W1p.value_restrictL_ae hVW (TauCeti.W1p.restrictL hWle u)
    have h2 : (TauCeti.W1p.value (TauCeti.W1p.restrictL hWle u) : X → ℝ)
        =ᵐ[(volume : Measure X).restrict V] TauCeti.W1p.value u :=
      ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hVV')
        (TauCeti.W1p.value_restrictL_ae hWle u)
    exact h1.trans h2

/-- W-PDE1 P3-4: a function in `H^k_loc(Ω)` for every `k` has a representative smooth on `Ω`. -/
theorem pde_smooth_rep {Ω : Opens X} {u : X → ℝ}
    (hu : ∀ (k : ℕ) (V : Opens X), IsCompact (closure (V : Set X)) → closure (V : Set X) ⊆ Ω →
      ∃ w : TauCeti.Wkp (volume : Measure X) V 2 k,
        (TauCeti.Wkp.value k w : X → ℝ) =ᵐ[(volume : Measure X).restrict V] u) :
    ∃ g : X → ℝ, ContDiffOn ℝ ∞ g Ω ∧ u =ᵐ[(volume : Measure X).restrict Ω] g := by
  refine TauCeti.exists_contDiffOn_ae_eq_of_locally Ω.isOpen fun x hx => ?_
  obtain ⟨r, hr, hrΩ⟩ := nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds hx)
  set V : Opens X := ⟨ball x r, isOpen_ball⟩
  have hVc : closure (V : Set X) ⊆ closedBall x r := closure_ball_subset_closedBall
  obtain ⟨g, hg, hug⟩ := TauCeti.exists_contDiffOn_ae_eq_of_forall_wkp (Omega := V) fun k =>
    hu k V ((isCompact_closedBall x r).of_isClosed_subset isClosed_closure hVc) (hVc.trans hrΩ)
  exact ⟨V, isOpen_ball.mem_nhds (mem_ball_self hr), g, hg, hug⟩

/-- W-PDE1 P3-5 (weak = classical): if `u ∈ H¹(Ω)` has a representative `g` smooth on `Ω` and
solves the split weak equation of P3-3, then `g` solves
`-∂ᵢ(Aⁱʲ∂ⱼg) + βʲ∂ⱼg + γ g = F` pointwise on `Ω`. -/
theorem pde_classical {Ω : Opens X} {A : X → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) Ω) {β : X → X} {γ F : X → ℝ}
    (hβ : ContDiffOn ℝ ∞ β Ω) (hγ : ContDiffOn ℝ ∞ γ Ω) (hF : ContDiffOn ℝ ∞ F Ω)
    {u : TauCeti.W1p (volume : Measure X) Ω 2}
    (hu : ∀ v : TauCeti.W1p0 (volume : Measure X) Ω 2,
      TauCeti.PDE.energyFormH1 A 0 0 u (v : TauCeti.W1p (volume : Measure X) Ω 2) =
        ∫ x in (Ω : Set X), (F x - inner ℝ (β x) (TauCeti.W1p.gradient u x) -
          γ x * TauCeti.W1p.value u x) *
            TauCeti.W1p.value (v : TauCeti.W1p (volume : Measure X) Ω 2) x)
    {g : X → ℝ} (hg : ContDiffOn ℝ ∞ g Ω)
    (hug : TauCeti.W1p.value u =ᵐ[(volume : Measure X).restrict Ω] g) :
    ∀ x ∈ (Ω : Set X),
      -(∑ i : Fin 2, fderiv ℝ (fun y => ∑ j : Fin 2, A y i j * fderiv ℝ g y
          (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) +
        ∑ j : Fin 2, β x j * fderiv ℝ g x (EuclideanSpace.single j 1) + γ x * g x = F x := by
  have hΩ : IsOpen (Ω : Set X) := Ω.isOpen
  have hms : MeasurableSet (Ω : Set X) := hΩ.measurableSet
  have hgd : ∀ x ∈ (Ω : Set X), DifferentiableAt ℝ g x := fun x hx =>
    (hg.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hx)
  have hg1 : ContDiffOn ℝ ∞ (fderiv ℝ g) Ω :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).1 hg).2
  have hdg : ∀ j : Fin 2,
      ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y (EuclideanSpace.single j 1)) Ω := fun j =>
    hg1.clm_apply contDiffOn_const
  -- the conormal components `qᵢ = Σⱼ Aⁱʲ ∂ⱼg`, smooth on `Ω`
  obtain ⟨q, hq_def⟩ : ∃ q : Fin 2 → X → ℝ,
      q = fun i y => ∑ j : Fin 2, A y i j * fderiv ℝ g y (EuclideanSpace.single j 1) := ⟨_, rfl⟩
  have hq : ∀ i, ContDiffOn ℝ ∞ (q i) Ω := fun i => by
    rw [hq_def]
    exact ContDiffOn.sum fun j _ => (hA i j).mul (hdg j)
  have hqd : ∀ i, ∀ x ∈ (Ω : Set X), DifferentiableAt ℝ (q i) x := fun i x hx =>
    ((hq i).differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hx)
  have hD : ∀ i, ContinuousOn (fun y => fderiv ℝ (q i) y (EuclideanSpace.single i 1)) Ω :=
    fun i => (((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).1 (hq i)).2.clm_apply
      contDiffOn_const).continuousOn
  have hqweak : ∀ i, TauCeti.HasWeakLineDerivOn volume Ω (q i)
      (fun x => fderiv ℝ (q i) x (EuclideanSpace.single i 1)) (EuclideanSpace.single i 1) :=
    fun i => TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt
      ((hq i).continuousOn.locallyIntegrableOn hms) ((hD i).locallyIntegrableOn hms)
      fun x hx => (hqd i x hx).hasFDerivAt.hasLineDerivAt _
  obtain ⟨Ds, hDs_def⟩ : ∃ Ds : X → ℝ,
      Ds = fun y => ∑ i : Fin 2, fderiv ℝ (q i) y (EuclideanSpace.single i 1) := ⟨_, rfl⟩
  obtain ⟨H, hH_def⟩ : ∃ H : X → ℝ, H = fun x =>
      F x - ∑ j : Fin 2, β x j * fderiv ℝ g x (EuclideanSpace.single j 1) - γ x * g x :=
    ⟨_, rfl⟩
  have hDs : ContinuousOn Ds Ω := by
    rw [hDs_def]
    exact continuousOn_finsetSum _ fun i _ => hD i
  have hβj : ∀ j : Fin 2, ContinuousOn (fun x => β x j) Ω := fun j =>
    (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp_continuousOn hβ.continuousOn
  have hH : ContinuousOn H Ω := by
    rw [hH_def]
    exact (hF.continuousOn.sub (continuousOn_finsetSum _ fun j _ =>
      (hβj j).mul (hdg j).continuousOn)).sub (hγ.continuousOn.mul hg.continuousOn)
  -- the weak gradient of `u` is the classical gradient of `g`
  have hgrad : ∀ j : Fin 2, ∀ᵐ x ∂(volume : Measure X).restrict Ω,
      TauCeti.W1p.gradient u x j = fderiv ℝ g x (EuclideanSpace.single j 1) := by
    intro j
    have h1 := ((TauCeti.W1p.hasWeakFDerivOn u).hasWeakLineDerivOn
      (EuclideanSpace.single j (1 : ℝ))).congr_ae hug
    have h2 := h1.ae_eq_lineDeriv
      (((hdg j).continuousOn.congr fun x hx =>
        (hgd x hx).lineDeriv_eq_fderiv).locallyIntegrableOn hms)
      (fun x hx => (hgd x hx).lineDifferentiableAt)
    filter_upwards [h2, ae_restrict_mem hms] with x hx hxΩ
    rw [innerSL_apply_apply, EuclideanSpace.inner_single_right,
      (hgd x hxΩ).lineDeriv_eq_fderiv] at hx
    simpa using hx
  -- testing against `φ ∈ 𝓓(Ω)` and integrating by parts gives `∫ φ (Ds + H) = 0`
  have key : ∀ᵐ x ∂(volume : Measure X), x ∈ (Ω : Set X) → Ds x + H x = 0 := by
    refine hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hDs.add hH).locallyIntegrableOn (μ := (volume : Measure X)) hms) ?_
    intro ψ hψ hψc hψs
    let φ : TestFunction Ω ℝ ⊤ := ⟨ψ, hψ, hψc, hψs⟩
    have hφ0 : ∀ x, x ∉ (Ω : Set X) → (φ : X → ℝ) x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (φ.tsupport_subset h)
    have hdφ0 : ∀ x, x ∉ (Ω : Set X) → fderiv ℝ (φ : X → ℝ) x = 0 := fun x hx =>
      fderiv_of_notMem_tsupport ℝ fun h => hx (φ.tsupport_subset h)
    have hφd : ∀ x v, lineDeriv ℝ (φ : X → ℝ) x v = fderiv ℝ (φ : X → ℝ) x v := fun x _ =>
      (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv
    let v : TauCeti.W1p0 (volume : Measure X) Ω 2 :=
      ⟨TauCeti.W1p.ofTestFunctionₗ volume Ω 2 φ, TauCeti.W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩
    have hvv : (v : TauCeti.W1p (volume : Measure X) Ω 2) =
        TauCeti.W1p.ofTestFunctionₗ volume Ω 2 φ := rfl
    have hv := hu v
    rw [TauCeti.PDE.energyFormH1_zero_zero_eq_setIntegral, hvv,
      TauCeti.W1p.gradient_ofTestFunctionₗ] at hv
    have hL : ∀ᵐ x ∂(volume : Measure X).restrict Ω,
        TauCeti.PDE.matrixBilinearForm (A x)
          (TauCeti.gradientTestFunctionLp (mu := volume) 2 φ x) (TauCeti.W1p.gradient u x) =
        ∑ i : Fin 2, fderiv ℝ (φ : X → ℝ) x (EuclideanSpace.single i 1) * q i x := by
      filter_upwards [TauCeti.gradientTestFunctionLp_apply_ae (mu := volume) 2 φ, hgrad 0,
        hgrad 1] with x hx h0 h1
      have hc : ∀ i : Fin 2, gradient (φ : X → ℝ) x i =
          fderiv ℝ (φ : X → ℝ) x (EuclideanSpace.single i 1) := fun i => by
        rw [← inner_gradient_left, EuclideanSpace.inner_single_right]
        simp
      rw [hx, TauCeti.PDE.matrixBilinearForm_apply]
      simp only [dotProduct, mulVec, Fin.sum_univ_two, hc, h0, h1, hq_def]
    have hR : ∀ᵐ x ∂(volume : Measure X).restrict Ω,
        (F x - inner ℝ (β x) (TauCeti.W1p.gradient u x) - γ x * TauCeti.W1p.value u x) *
          TauCeti.W1p.value (TauCeti.W1p.ofTestFunctionₗ volume Ω 2 φ) x =
        (φ : X → ℝ) x * H x := by
      filter_upwards [TauCeti.W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := 2) φ, hgrad 0,
        hgrad 1, hug] with x hx h0 h1 h2
      rw [hx, h2, hH_def]
      simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial, h0, h1]
      ring
    rw [integral_congr_ae hL, integral_congr_ae hR,
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hdφ0 x hx]),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hφ0 x hx])] at hv
    -- integrate the conormal components by parts
    have hint : ∀ i : Fin 2, Integrable
        (fun x => fderiv ℝ (φ : X → ℝ) x (EuclideanSpace.single i 1) * q i x) := fun i => by
      simpa only [smul_eq_mul, hφd] using TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn
        (hqweak i).locallyIntegrableOn φ (EuclideanSpace.single i 1)
    have hint' : ∀ i : Fin 2, Integrable
        (fun x => (φ : X → ℝ) x * fderiv ℝ (q i) x (EuclideanSpace.single i 1)) := fun i => by
      simpa only [smul_eq_mul] using
        TauCeti.integrable_smul_of_locallyIntegrableOn ((hD i).locallyIntegrableOn hms) φ
    have hibp : ∀ i : Fin 2,
        ∫ x, fderiv ℝ (φ : X → ℝ) x (EuclideanSpace.single i 1) * q i x =
          -∫ x, (φ : X → ℝ) x * fderiv ℝ (q i) x (EuclideanSpace.single i 1) := fun i => by
      simpa only [smul_eq_mul, hφd] using
        (hqweak i).integral_lineDeriv_smul_eq_neg_integral_smul φ
    rw [integral_finsetSum _ fun i _ => hint i] at hv
    simp only [hibp, Finset.sum_neg_distrib] at hv
    rw [← integral_finsetSum _ fun i _ => hint' i] at hv
    have hiD := TauCeti.integrable_smul_of_locallyIntegrableOn
      (hDs.locallyIntegrableOn (μ := volume) hms) φ
    have hiH := TauCeti.integrable_smul_of_locallyIntegrableOn
      (hH.locallyIntegrableOn (μ := volume) hms) φ
    simp only [smul_eq_mul] at hiD hiH
    have hsum : ∀ x, ∑ i : Fin 2, (φ : X → ℝ) x * fderiv ℝ (q i) x (EuclideanSpace.single i 1) =
        (φ : X → ℝ) x * Ds x := fun x => by
      rw [hDs_def, Finset.mul_sum]
    simp only [hsum] at hv
    have h3 : ∫ x, (φ : X → ℝ) x * (Ds x + H x) = 0 := by
      simp only [mul_add]
      rw [integral_add hiD hiH]
      linarith
    simp only [smul_eq_mul]
    exact h3
  have hEq := Measure.eqOn_open_of_ae_eq (μ := volume) (f := fun x => Ds x + H x)
    (g := fun _ => 0) ((ae_restrict_iff' hms).2 key) hΩ (hDs.add hH) continuousOn_const
  intro x hx
  have h := hEq hx
  simp only [hDs_def, hH_def, hq_def] at h
  linarith

/-- W-PDE1 P3 helper: with bounded measurable coefficients and data `f =ᵐ F`, a weak solution of
the Dirichlet problem solves the split weak equation of P3-3 (drift and mass terms on the
right-hand side). -/
theorem pde_split_of_weak {Ω : Opens X} {A : X → Matrix (Fin 2) (Fin 2) ℝ} {β : X → X}
    {γ F : X → ℝ} {K B G : ℝ}
    (hAm : AEStronglyMeasurable (fun x => TauCeti.PDE.matrixBilinearForm (A x))
      ((volume : Measure X).restrict Ω))
    (hβm : AEStronglyMeasurable β ((volume : Measure X).restrict Ω))
    (hγm : AEStronglyMeasurable γ ((volume : Measure X).restrict Ω))
    (hAn : ∀ x ∈ (Ω : Set X), ‖TauCeti.PDE.matrixBilinearForm (A x)‖ ≤ K)
    (hβb : ∀ x ∈ (Ω : Set X), ‖β x‖ ≤ B) (hγb : ∀ x ∈ (Ω : Set X), |γ x| ≤ G)
    (f : Lp ℝ 2 ((volume : Measure X).restrict Ω))
    (hfF : (f : X → ℝ) =ᵐ[(volume : Measure X).restrict Ω] F)
    {u : TauCeti.W1p0 (volume : Measure X) Ω 2}
    (hu : TauCeti.PDE.IsWeakSolutionDirichlet A β γ f u)
    (v : TauCeti.W1p0 (volume : Measure X) Ω 2) :
    TauCeti.PDE.energyFormH1 A 0 0 (u : TauCeti.W1p (volume : Measure X) Ω 2)
        (v : TauCeti.W1p (volume : Measure X) Ω 2) =
      ∫ x in (Ω : Set X), (F x - inner ℝ (β x)
        (TauCeti.W1p.gradient (u : TauCeti.W1p (volume : Measure X) Ω 2) x) -
        γ x * TauCeti.W1p.value (u : TauCeti.W1p (volume : Measure X) Ω 2) x) *
          TauCeti.W1p.value (v : TauCeti.W1p (volume : Measure X) Ω 2) x := by
  have h1 := (TauCeti.PDE.isWeakSolutionDirichlet_iff f u).1 hu v
  rw [pde_energy_split hAm hβm hγm hAn hβb hγb (u : TauCeti.W1p (volume : Measure X) Ω 2)
    (v : TauCeti.W1p (volume : Measure X) Ω 2)] at h1
  -- `f v` is integrable as a product of two `L²` functions
  have hfv : Integrable (fun x => f x *
      TauCeti.W1p.value (v : TauCeti.W1p (volume : Measure X) Ω 2) x)
      ((volume : Measure X).restrict Ω) :=
    (Lp.memLp f).integrable_mul (Lp.memLp _)
  -- the drift and mass terms are integrable since `β`, `γ` are bounded on `Ω`
  have hL := TauCeti.PDE.integrable_energyIntegrand_jetField
    (TauCeti.PDE.memLp_energyIntegrand_of_bounds (a := fun _ => 0) (Lam := 0) le_rfl
      aestronglyMeasurable_const hβm hγm (fun _ _ _ _ => by simp) hβb
      (fun x hx => by simpa [Real.norm_eq_abs] using hγb x hx))
    (u : TauCeti.W1p (volume : Measure X) Ω 2) (v : TauCeti.W1p (volume : Measure X) Ω 2)
  have hdv : Integrable (fun x => (inner ℝ (β x)
      (TauCeti.W1p.gradient (u : TauCeti.W1p (volume : Measure X) Ω 2) x) +
      γ x * TauCeti.W1p.value (u : TauCeti.W1p (volume : Measure X) Ω 2) x) *
        TauCeti.W1p.value (v : TauCeti.W1p (volume : Measure X) Ω 2) x)
      ((volume : Measure X).restrict Ω) := by
    refine hL.congr (ae_of_all _ fun x => ?_)
    simp [TauCeti.PDE.energyIntegrand_apply, TauCeti.PDE.matrixBilinearForm_apply]
    ring
  have h2 : ∫ x in (Ω : Set X), (F x - inner ℝ (β x)
        (TauCeti.W1p.gradient (u : TauCeti.W1p (volume : Measure X) Ω 2) x) -
        γ x * TauCeti.W1p.value (u : TauCeti.W1p (volume : Measure X) Ω 2) x) *
          TauCeti.W1p.value (v : TauCeti.W1p (volume : Measure X) Ω 2) x =
      (∫ x in (Ω : Set X), f x *
        TauCeti.W1p.value (v : TauCeti.W1p (volume : Measure X) Ω 2) x) -
      ∫ x in (Ω : Set X), (inner ℝ (β x)
        (TauCeti.W1p.gradient (u : TauCeti.W1p (volume : Measure X) Ω 2) x) +
        γ x * TauCeti.W1p.value (u : TauCeti.W1p (volume : Measure X) Ω 2) x) *
          TauCeti.W1p.value (v : TauCeti.W1p (volume : Measure X) Ω 2) x := by
    rw [← integral_sub hfv hdv]
    refine integral_congr_ae ?_
    filter_upwards [hfF] with x hx
    linear_combination
      (-TauCeti.W1p.value (v : TauCeti.W1p (volume : Measure X) Ω 2) x) * hx
  rw [h2]
  exact eq_sub_of_add_eq h1

/-- W-PDE1 P3 deliverable (interior regularity, in the setting of P2): in addition to the
hypotheses of `pde_weak_exists_unique`, let `A`, `β`, `γ` be smooth on `Ω` and let the data
`f ∈ L²(Ω)` agree a.e. on `Ω` with a function `F` smooth on `Ω`. Then the weak solution `u` has a
representative `g` smooth on `Ω` that solves `-∂ᵢ(Aⁱʲ∂ⱼg) + βʲ∂ⱼg + γ g = F` pointwise on `Ω`. -/
theorem pde_weak_sol_smooth_interior {Ω : Opens X}
    (hb : Bornology.IsBounded (Ω : Set X)) {ε' : ℝ} (hε0 : 0 ≤ ε')
    (hε : ε' < 1) {A : X → Matrix (Fin 2) (Fin 2) ℝ} {β : X → X} {γ : X → ℝ}
    (hA : ∀ i j, ContinuousOn (fun x => A x i j) (closure (Ω : Set X)))
    (hβ : ContinuousOn β (closure (Ω : Set X)))
    (hγ : ContinuousOn γ (closure (Ω : Set X)))
    (hell : ∀ x ∈ (Ω : Set X), ∀ ξ : Fin 2 → ℝ,
      |ξ ⬝ᵥ (A x *ᵥ ξ) - ξ ⬝ᵥ ξ| ≤ ε' * (ξ ⬝ᵥ ξ))
    (hγ0 : ∀ x ∈ (Ω : Set X), 0 ≤ γ x)
    (hAs : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) Ω) (hβs : ContDiffOn ℝ ∞ β Ω)
    (hγs : ContDiffOn ℝ ∞ γ Ω) {F : X → ℝ} (hF : ContDiffOn ℝ ∞ F Ω)
    (f : Lp ℝ 2 ((volume : Measure X).restrict Ω))
    (hfF : (f : X → ℝ) =ᵐ[(volume : Measure X).restrict Ω] F)
    {u : TauCeti.W1p0 (volume : Measure X) Ω 2}
    (hu : TauCeti.PDE.IsWeakSolutionDirichlet A β γ f u) :
    ∃ g : X → ℝ, ContDiffOn ℝ ∞ g Ω ∧
      TauCeti.W1p.value (u : TauCeti.W1p (volume : Measure X) Ω 2)
        =ᵐ[(volume : Measure X).restrict Ω] g ∧
      ∀ x ∈ (Ω : Set X),
        -(∑ i : Fin 2, fderiv ℝ (fun y => ∑ j : Fin 2, A y i j * fderiv ℝ g y
            (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) +
          ∑ j : Fin 2, β x j * fderiv ℝ g x (EuclideanSpace.single j 1) + γ x * g x = F x := by
  have _hε0 := hε0
  have _hγ0 := hγ0
  have hS : IsCompact (closure (Ω : Set X)) := hb.isCompact_closure
  have hΩS : (Ω : Set X) ⊆ closure (Ω : Set X) := subset_closure
  have hms : MeasurableSet (Ω : Set X) := Ω.isOpen.measurableSet
  obtain ⟨Lam, hell', hAn⟩ := pde_uniformlyEllipticOn hb hε hA hell
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hβ
  obtain ⟨G, hG⟩ := hS.exists_bound_of_continuousOn hγ
  have hβb : ∀ x ∈ (Ω : Set X), ‖β x‖ ≤ B := fun x hx => hB x (hΩS hx)
  have hγb : ∀ x ∈ (Ω : Set X), |γ x| ≤ G := fun x hx => by
    simpa [Real.norm_eq_abs] using hG x (hΩS hx)
  have hAc : ContinuousOn A (Ω : Set X) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hA i j).mono hΩS
  -- `Matrix` carries no global metric; borrow the product one (as in the proof of P2)
  let : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℝ))
  have hAm : AEStronglyMeasurable (fun x => TauCeti.PDE.matrixBilinearForm (A x))
      ((volume : Measure X).restrict Ω) :=
    TauCeti.PDE.continuous_matrixBilinearForm.comp_aestronglyMeasurable
      (hAc.aestronglyMeasurable hms)
  have hβm : AEStronglyMeasurable β ((volume : Measure X).restrict Ω) :=
    (hβ.mono hΩS).aestronglyMeasurable hms
  have hγm : AEStronglyMeasurable γ ((volume : Measure X).restrict Ω) :=
    (hγ.mono hΩS).aestronglyMeasurable hms
  -- the weak equation with the drift and mass terms moved to the right-hand side
  have hsplit := pde_split_of_weak hAm hβm hγm hAn hβb hγb f hfF hu
  -- `u ∈ H^k_loc(Ω)` for every `k`, hence `u` has a representative smooth on `Ω`
  have hk : ∀ (k : ℕ) (V : Opens X), IsCompact (closure (V : Set X)) →
      closure (V : Set X) ⊆ Ω → ∃ w : TauCeti.Wkp (volume : Measure X) V 2 k,
        (TauCeti.Wkp.value k w : X → ℝ) =ᵐ[(volume : Measure X).restrict V]
          TauCeti.W1p.value (u : TauCeti.W1p (volume : Measure X) Ω 2) := by
    intro k V hV hVΩ
    cases k with
    | zero =>
      obtain ⟨w, hw⟩ := pde_Hk_loc hell' hAs hβs hγs hF hsplit 0 hV hVΩ
      refine ⟨TauCeti.Wkp.lowerOrder 0 w, ?_⟩
      rw [← TauCeti.Wkp.value_succ]
      exact hw
    | succ k => exact pde_Hk_loc hell' hAs hβs hγs hF hsplit k hV hVΩ
  obtain ⟨g, hg, hug⟩ := pde_smooth_rep hk
  exact ⟨g, hg, hug, pde_classical hAs hβs hγs hF hsplit hg hug⟩

/-! ### W-PDE1 P4 (pilot): `H²` up to a flat boundary, and flattening charts

P4-1 `pde_hs_H2`: TauCeti's tangential difference-quotient theorem for Lipschitz coefficients plus a
variable-coefficient normal step (`pde_hs_normal`; TauCeti's `HalfSpace.lean` has the normal step
only for constant coefficients). P4-3 `pde_flat_chart`: inverse function theorem. -/

local notation "𝐞" => EuclideanSpace.basisFun (Fin 2) ℝ

/-- W-PDE1 P4-1 helper: a smooth function that is constant off a compact set is bounded, with
bounded derivative. -/
theorem pde_hs_bound {φ : X → ℝ} (hφ : ContDiff ℝ ∞ φ) {c : ℝ}
    (hc : HasCompactSupport (fun x => φ x - c)) :
    ∃ M, ∀ x, |φ x| ≤ M ∧ ‖fderiv ℝ φ x‖ ≤ M := by
  have hψ : ContDiff ℝ ∞ (fun x => φ x - c) := hφ.sub contDiff_const
  obtain ⟨C₁, hC₁⟩ := hc.exists_bound_of_continuous hψ.continuous
  obtain ⟨C₂, hC₂⟩ := (hc.fderiv ℝ).exists_bound_of_continuous (hψ.continuous_fderiv (by simp))
  refine ⟨C₁ + |c| + C₂, fun x => ⟨?_, ?_⟩⟩
  · have h1 := hC₁ x
    have h2 := hC₂ x
    have h3 := abs_add_le (φ x - c) c
    rw [sub_add_cancel] at h3
    rw [Real.norm_eq_abs] at h1
    have := norm_nonneg (fderiv ℝ (fun x => φ x - c) x)
    linarith
  · have h1 := hC₁ x
    have h2 := hC₂ x
    rw [fderiv_sub_const] at h2
    have := norm_nonneg (φ x - c)
    have := abs_nonneg c
    linarith

/-- W-PDE1 P4-1 helper: smooth coefficients that equal the identity off a compact set have a
globally Lipschitz bilinear form. -/
theorem pde_hs_lip {A : X → Matrix (Fin 2) (Fin 2) ℝ} (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hAc : ∀ i j, HasCompactSupport (fun x => A x i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)) :
    ∃ K, LipschitzWith K (fun x => TauCeti.PDE.matrixBilinearForm (A x)) := by
  choose K hK using fun i j =>
    ContDiff.lipschitzWith_of_hasCompactSupport (hAc i j) ((hA i j).sub contDiff_const) (by simp)
  refine ⟨∑ i, ∑ j, K i j, LipschitzWith.of_dist_le_mul fun y z => ?_⟩
  rw [dist_eq_norm, ← TauCeti.PDE.matrixBilinearForm_sub]
  refine (TauCeti.PDE.norm_matrixBilinearForm_le_sum_abs _).trans ?_
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  have h := (hK i j).dist_le_mul y z
  rw [Real.dist_eq, sub_sub_sub_cancel_right] at h
  rwa [Matrix.sub_apply]

/-- W-PDE1 P4-1 helper: a coefficient bounded and continuous on `S` maps `L²(S)` to `L²(S)`. -/
theorem pde_memLp_smul {S : Set X} (hS : MeasurableSet S) {c g : X → ℝ} {M : ℝ}
    (hc : ContinuousOn c S) (hM : ∀ x ∈ S, |c x| ≤ M)
    (hg : MemLp g 2 ((volume : Measure X).restrict S)) :
    MemLp (fun x => c x • g x) 2 ((volume : Measure X).restrict S) :=
  hg.of_le_mul (c := M) ((hc.aestronglyMeasurable hS).smul hg.aestronglyMeasurable)
    ((ae_restrict_mem hS).mono fun x hx => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg _))

open TauCeti TauCeti.PDE in
open scoped InnerProductSpace in
/-- W-PDE1 P4-1 helper (copy of the private TauCeti lemma
`energyFormH1_ofTestFunctionₗ_eq_sum_sum`, `DifferentiatedEquation.lean`): the
drift- and mass-free energy form against a test function, entry by entry. -/
theorem pde_energy_sum_sum {Ω : Opens X} {A : X → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ∀ i j, ContinuousOn (fun x => A x i j) Ω) (w : W1p (volume : Measure X) Ω 2)
    (φ : TestFunction Ω ℝ ⊤) :
    energyFormH1 A 0 0 w (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      ∑ i, ∑ j, ∫ x, lineDeriv ℝ (φ : X → ℝ) x (𝐞 i) •
        (A x i j • innerSL ℝ (W1p.gradient w x) (𝐞 j)) := by
  have hloc : ∀ i j, LocallyIntegrableOn
      (fun x => A x i j • innerSL ℝ (W1p.gradient w x) (𝐞 j)) Ω volume := fun i j =>
    ((W1p.hasWeakFDerivOn w).hasWeakLineDerivOn (𝐞 j)).locallyIntegrableOn_deriv.continuousOn_smul
      Ω.isOpen.isLocallyClosed (hA i j)
  have hB : ∀ (M : Matrix (Fin 2) (Fin 2) ℝ) (η ξ : X), matrixBilinearForm M η ξ =
      ∑ i, ∑ j, ⟪η, 𝐞 i⟫_ℝ * (M i j * innerSL ℝ ξ (𝐞 j)) := fun M η ξ => by
    simp only [innerSL_apply_apply, EuclideanSpace.inner_basisFun_real, matrixBilinearForm_apply,
      dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [energyFormH1_zero_zero_eq_setIntegral]
  calc ∫ x in Ω, matrixBilinearForm (A x)
        (W1p.gradient (W1p.ofTestFunctionₗ volume Ω 2 φ) x) (W1p.gradient w x)
      = ∫ x in Ω, ∑ i, ∑ j, lineDeriv ℝ (φ : X → ℝ) x (𝐞 i) •
          (A x i j • innerSL ℝ (W1p.gradient w x) (𝐞 j)) := by
        refine integral_congr_ae ?_
        filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) 2 φ] with x hx
        rw [W1p.gradient_ofTestFunctionₗ, hx, hB]
        simp only [smul_eq_mul, inner_gradient_left,
          (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv]
    _ = ∑ i, ∑ j, ∫ x in Ω, lineDeriv ℝ (φ : X → ℝ) x (𝐞 i) •
          (A x i j • innerSL ℝ (W1p.gradient w x) (𝐞 j)) := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          (integrable_lineDeriv_smul_of_locallyIntegrableOn (hloc i j) φ (𝐞 i)).restrict]
        exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ =>
          (integrable_lineDeriv_smul_of_locallyIntegrableOn (hloc i j) φ (𝐞 i)).restrict
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul φ (𝐞 i)

open TauCeti TauCeti.PDE in
open scoped InnerProductSpace in
/-- W-PDE1 P4-1 helper (the variable-coefficient normal step): if `u` solves
`-∂ᵢ(Aⁱʲ∂ⱼu) = f` against test functions and the fluxes `A⁰⁰∂₀u`, `A⁰¹∂₁u` (in the direction
`e₀`) and `A¹⁰∂₀u` (in the direction `e₁`) have weak derivatives `F₀₀`, `F₀₁`, `F₁₀`, then
`A¹¹∂₁u` has the weak derivative `-(f + F₀₀ + F₀₁ + F₁₀)` in the direction `e₁`. -/
theorem pde_hs_normal {Ω : Opens X} {A : X → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ∀ i j, ContinuousOn (fun x => A x i j) Ω) {f : X → ℝ}
    (hf : LocallyIntegrableOn f Ω volume) {U : W1p (volume : Measure X) Ω 2}
    (hU : ∀ φ : TestFunction Ω ℝ ⊤,
      energyFormH1 A 0 0 U (W1p.ofTestFunctionₗ volume Ω 2 φ) = ∫ x in Ω, f x * φ x)
    {F₀₀ F₀₁ F₁₀ : X → ℝ}
    (h₀₀ : HasWeakLineDerivOn volume Ω (fun x => A x 0 0 • ⟪W1p.gradient U x, 𝐞 0⟫_ℝ) F₀₀ (𝐞 0))
    (h₀₁ : HasWeakLineDerivOn volume Ω (fun x => A x 0 1 • ⟪W1p.gradient U x, 𝐞 1⟫_ℝ) F₀₁ (𝐞 0))
    (h₁₀ : HasWeakLineDerivOn volume Ω (fun x => A x 1 0 • ⟪W1p.gradient U x, 𝐞 0⟫_ℝ) F₁₀ (𝐞 1)) :
    HasWeakLineDerivOn volume Ω (fun x => A x 1 1 • ⟪W1p.gradient U x, 𝐞 1⟫_ℝ)
      (fun x => -(f x + F₀₀ x + F₀₁ x + F₁₀ x)) (𝐞 1) := by
  have hloc : LocallyIntegrableOn (fun x => ⟪W1p.gradient U x, 𝐞 1⟫_ℝ) Ω volume := by
    simpa only [innerSL_apply_apply] using
      ((W1p.hasWeakFDerivOn U).hasWeakLineDerivOn (𝐞 1)).locallyIntegrableOn_deriv
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨inferInstance,
    hloc.continuousOn_smul Ω.isOpen.isLocallyClosed (hA 1 1), ?_, fun φ => ?_⟩
  · exact (((hf.add h₀₀.locallyIntegrableOn_deriv).add h₀₁.locallyIntegrableOn_deriv).add
      h₁₀.locallyIntegrableOn_deriv).neg
  have heq := hU φ
  rw [pde_energy_sum_sum hA] at heq
  simp only [Fin.sum_univ_two, innerSL_apply_apply] at heq
  have e₀₀ := h₀₀.integral_lineDeriv_smul_eq_neg_integral_smul φ
  have e₀₁ := h₀₁.integral_lineDeriv_smul_eq_neg_integral_smul φ
  have e₁₀ := h₁₀.integral_lineDeriv_smul_eq_neg_integral_smul φ
  have iF := integrable_smul_of_locallyIntegrableOn hf φ
  have i₀₀ := integrable_smul_of_locallyIntegrableOn h₀₀.locallyIntegrableOn_deriv φ
  have i₀₁ := integrable_smul_of_locallyIntegrableOn h₀₁.locallyIntegrableOn_deriv φ
  have i₁₀ := integrable_smul_of_locallyIntegrableOn h₁₀.locallyIntegrableOn_deriv φ
  have hF : ∫ x in Ω, f x * φ x = ∫ x, (φ : X → ℝ) x • f x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      simp [φ.zero_on_compl hx]]
    simp only [smul_eq_mul, mul_comm]
  have hsum : ∫ x, (φ : X → ℝ) x • -(f x + F₀₀ x + F₀₁ x + F₁₀ x) =
      -((∫ x, (φ : X → ℝ) x • f x) + (∫ x, (φ : X → ℝ) x • F₀₀ x) +
        (∫ x, (φ : X → ℝ) x • F₀₁ x) + ∫ x, (φ : X → ℝ) x • F₁₀ x) := by
    have h₁ : ∫ x, ((φ : X → ℝ) x • f x + (φ : X → ℝ) x • F₀₀ x) =
        (∫ x, (φ : X → ℝ) x • f x) + ∫ x, (φ : X → ℝ) x • F₀₀ x := integral_add iF i₀₀
    have h₂ : ∫ x, ((φ : X → ℝ) x • f x + (φ : X → ℝ) x • F₀₀ x + (φ : X → ℝ) x • F₀₁ x) =
        (∫ x, ((φ : X → ℝ) x • f x + (φ : X → ℝ) x • F₀₀ x)) + ∫ x, (φ : X → ℝ) x • F₀₁ x :=
      integral_add (iF.add i₀₀) i₀₁
    have h₃ : ∫ x, ((φ : X → ℝ) x • f x + (φ : X → ℝ) x • F₀₀ x + (φ : X → ℝ) x • F₀₁ x +
        (φ : X → ℝ) x • F₁₀ x) = (∫ x, ((φ : X → ℝ) x • f x + (φ : X → ℝ) x • F₀₀ x +
          (φ : X → ℝ) x • F₀₁ x)) + ∫ x, (φ : X → ℝ) x • F₁₀ x :=
      integral_add ((iF.add i₀₀).add i₀₁) i₁₀
    rw [← h₁, ← h₂, ← h₃, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul]
    ring
  rw [hsum, neg_neg]
  linear_combination heq - e₀₀ - e₀₁ - e₁₀ + hF

open TauCeti TauCeti.PDE in
open scoped InnerProductSpace in
/-- W-PDE1 P4-1 (flat model, `H²` up to the boundary): on the half-plane `H = {0 < y₁}`, let `A`
be smooth, uniformly elliptic, and equal to the identity outside a compact set. The `H¹₀(H)` weak
solution of `-∂ᵢ(Aⁱʲ∂ⱼw) = g`, `g ∈ L²(H)`, lies in `H²(H)`. -/
theorem pde_hs_H2 {H : Opens X} (hH : (H : Set X) = {y | 0 < y 1})
    {A : X → Matrix (Fin 2) (Fin 2) ℝ} {lam Lam : ℝ}
    (hell : TauCeti.PDE.UniformlyEllipticOn (H : Set X) A lam Lam)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hAc : ∀ i j, HasCompactSupport (fun x => A x i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j))
    (g : Lp ℝ 2 ((volume : Measure X).restrict H)) {w : TauCeti.W1p0 (volume : Measure X) H 2}
    (hw : TauCeti.PDE.IsWeakSolutionDirichlet A 0 0 g w) :
    ∃ W : TauCeti.Wkp (volume : Measure X) H 2 2,
      (TauCeti.Wkp.value 2 W : X → ℝ) =ᵐ[(volume : Measure X).restrict H]
        TauCeti.W1p.value (w : TauCeti.W1p (volume : Measure X) H 2) := by
  classical
  set U : W1p (volume : Measure X) H 2 := (w : W1p (volume : Measure X) H 2)
  have hHm : MeasurableSet (H : Set X) := H.isOpen.measurableSet
  have hlam : 0 < lam := hell.1
  have hAs : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) H := fun i j => (hA i j).contDiffOn
  have hHν : ∀ x, x ∈ H ↔ (0 : ℝ) < ⟪x, 𝐞 1⟫_ℝ := fun x => by
    rw [← SetLike.mem_coe, hH, EuclideanSpace.inner_basisFun_real]
    rfl
  -- the first derivatives of `u` and their commutation
  have hfd : ∀ z, HasWeakLineDerivOn volume H (W1p.value U)
      (fun x => ⟪W1p.gradient U x, z⟫_ℝ) z := fun z => by
    simpa only [innerSL_apply_apply] using (W1p.hasWeakFDerivOn U).hasWeakLineDerivOn z
  -- tangential directions: the difference-quotient theorem for Lipschitz coefficients
  obtain ⟨K, hK⟩ := pde_hs_lip hA hAc
  have htan : ∀ y : X, ∃ G : Lp ℝ 2 ((volume : Measure X).restrict H),
      HasWeakLineDerivOn volume H (fun x => ⟪W1p.gradient U x, y⟫_ℝ) G (𝐞 0) := fun y => by
    obtain ⟨G, -, hG⟩ := hell.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzOnWith_of_mapsTo
      (TauCeti.mapsTo_add_smul_of_halfSpace hHν (show ⟪𝐞 0, 𝐞 1⟫_ℝ = 0 by rw [EuclideanSpace.inner_basisFun_real]; simp)) hK.lipschitzOnWith hw y
    exact ⟨G, hG⟩
  obtain ⟨P, hP⟩ := htan (𝐞 0)
  obtain ⟨Q, hQ⟩ := htan (𝐞 1)
  have hQ' := (hfd (𝐞 1)).comm hQ (hfd (𝐞 0))
  -- the equation against test functions
  have hcoeff : MemLp (fun x => energyIntegrand (A x) ((0 : X → X) x) ((0 : X → ℝ) x)) ⊤
      ((volume : Measure X).restrict H) :=
    memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0) (hlam.le.trans hell.2.1)
      (Continuous.aestronglyMeasurable (β := Fin 2 → Fin 2 → ℝ)
        (continuous_pi fun i => continuous_pi fun j => (hA i j).continuous))
      aestronglyMeasurable_const aestronglyMeasurable_const
      (fun x hx => (hell.2.2 hx).2) (fun _ _ => by simp) (fun _ _ => by simp)
  have hU := (forall_energyFormH1_eq_setIntegral_iff_forall_testFunction hcoeff g U).1
    ((isWeakSolutionDirichlet_iff g w).1 hw)
  -- the normal step
  have hn := pde_hs_normal (fun i j => (hAs i j).continuousOn) (Lp.locallyIntegrableOn g (by norm_num))
    hU (hP.contDiffOn_smul (hAs 0 0)) (hQ.contDiffOn_smul (hAs 0 1)) (hQ'.contDiffOn_smul (hAs 1 0))
  -- `A¹¹ ≥ λ` on `H`
  have hA11 : ∀ x ∈ (H : Set X), lam ≤ A x 1 1 := fun x hx => by
    have h := (hell.2.2 hx).1 (𝐞 1)
    simpa [Matrix.toQuadraticForm'_apply, dotProduct, Matrix.mulVec, Fin.sum_univ_two] using h
  have hne : ∀ x ∈ (H : Set X), A x 1 1 ≠ 0 := fun x hx => (hlam.trans_le (hA11 x hx)).ne'
  have hinv : ContDiffOn ℝ ∞ (fun x => (A x 1 1)⁻¹) H := (hAs 1 1).inv hne
  have hn2 := (hn.contDiffOn_smul hinv).congr_ae (w := fun x => ⟪W1p.gradient U x, 𝐞 1⟫_ℝ)
    ((ae_restrict_mem hHm).mono fun x hx => by
      simp only [smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (hne x hx), one_mul])
  -- the `L²` bounds
  choose M hM using fun i j => pde_hs_bound (hA i j) (hAc i j)
  have hgj : ∀ j, MemLp (fun x => ⟪W1p.gradient U x, 𝐞 j⟫_ℝ) 2 ((volume : Measure X).restrict H) :=
    fun j => (Lp.memLp (W1p.gradient U)).of_le_mul (c := 1)
      ((Lp.aestronglyMeasurable _).inner aestronglyMeasurable_const)
      (ae_of_all _ fun x => by simpa using norm_inner_le_norm (𝕜 := ℝ) (W1p.gradient U x) (𝐞 j))
  have mA : ∀ i j {h : X → ℝ}, MemLp h 2 ((volume : Measure X).restrict H) →
      MemLp (fun x => A x i j • h x) 2 ((volume : Measure X).restrict H) := fun i j _ hh =>
    pde_memLp_smul hHm (hA i j).continuous.continuousOn (fun x _ => (hM i j x).1) hh
  have mD : ∀ i j k {h : X → ℝ}, MemLp h 2 ((volume : Measure X).restrict H) →
      MemLp (fun x => fderiv ℝ (fun y => A y i j) x (𝐞 k) • h x) 2
        ((volume : Measure X).restrict H) := fun i j k _ hh =>
    pde_memLp_smul hHm
      (((hA i j).continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn
      (fun x _ => by
        have h1 := (fderiv ℝ (fun y => A y i j) x).le_opNorm (𝐞 k)
        rw [Real.norm_eq_abs] at h1
        simpa using h1.trans (by simpa using (hM i j x).2))
      hh
  have hR := ((((Lp.memLp g).add ((mA 0 0 (Lp.memLp P)).add (mD 0 0 0 (hgj 0)))).add
    ((mA 0 1 (Lp.memLp Q)).add (mD 0 1 0 (hgj 1)))).add
    ((mA 1 0 (Lp.memLp Q)).add (mD 1 0 1 (hgj 0)))).neg
  have hD1 : MemLp (fun x => fderiv ℝ (fun y => (A y 1 1)⁻¹) x (𝐞 1) •
      (A x 1 1 • ⟪W1p.gradient U x, 𝐞 1⟫_ℝ)) 2 ((volume : Measure X).restrict H) :=
    pde_memLp_smul hHm (M := M 1 1 * (lam ^ 2)⁻¹)
      ((hinv.continuousOn_fderiv_of_isOpen H.isOpen (by simp)).clm_apply continuousOn_const)
      (fun x hx => by
        have hd : fderiv ℝ (fun y => (A y 1 1)⁻¹) x =
            (ContinuousLinearMap.toSpanSingleton ℝ (-(A x 1 1 ^ 2)⁻¹)).comp
              (fderiv ℝ (fun y => A y 1 1) x) :=
          ((hasFDerivAt_inv (hne x hx)).comp x
            (((hA 1 1).differentiable (by simp)) x).hasFDerivAt).fderiv
        rw [hd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
          smul_eq_mul, abs_mul, abs_neg, abs_inv, abs_pow]
        have h1 := (fderiv ℝ (fun y => A y 1 1) x).le_opNorm (𝐞 1)
        rw [Real.norm_eq_abs] at h1
        have h2 : |fderiv ℝ (fun y => A y 1 1) x (𝐞 1)| ≤ M 1 1 := by
          simpa using h1.trans (by simpa using (hM 1 1 x).2)
        have h3 : (|A x 1 1| ^ 2)⁻¹ ≤ (lam ^ 2)⁻¹ := by
          rw [abs_of_pos (hlam.trans_le (hA11 x hx))]
          exact inv_anti₀ (pow_pos hlam 2) (pow_le_pow_left₀ hlam.le (hA11 x hx) 2)
        exact mul_le_mul h2 h3 (by positivity) ((abs_nonneg _).trans h2))
      (mA 1 1 (hgj 1))
  have hD0 : MemLp (fun x => (A x 1 1)⁻¹ • -(g x +
      (A x 0 0 • P x + fderiv ℝ (fun y => A y 0 0) x (𝐞 0) • ⟪W1p.gradient U x, 𝐞 0⟫_ℝ) +
      (A x 0 1 • Q x + fderiv ℝ (fun y => A y 0 1) x (𝐞 0) • ⟪W1p.gradient U x, 𝐞 1⟫_ℝ) +
      (A x 1 0 • Q x + fderiv ℝ (fun y => A y 1 0) x (𝐞 1) • ⟪W1p.gradient U x, 𝐞 0⟫_ℝ)))
      2 ((volume : Measure X).restrict H) :=
    pde_memLp_smul hHm (M := lam⁻¹) hinv.continuousOn
      (fun x hx => by
        rw [abs_inv, abs_of_pos (hlam.trans_le (hA11 x hx))]
        exact inv_anti₀ hlam (hA11 x hx))
      hR
  have hDn := hD0.add hD1
  have hd : ∀ i j, ∃ G : Lp ℝ 2 ((volume : Measure X).restrict H),
      HasWeakLineDerivOn volume H (fun x => ⟪W1p.gradient U x, 𝐞 j⟫_ℝ) G (𝐞 i) := by
    intro i j
    fin_cases i
    · exact htan (𝐞 j)
    fin_cases j
    · exact ⟨Q, hQ'⟩
    · exact ⟨hDn.toLp _, hn2.congr_ae_deriv hDn.coeFn_toLp.symm⟩
  obtain ⟨W, hW⟩ := W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn U 𝐞 hd
  refine ⟨W, ?_⟩
  rw [show Wkp.value 2 W = Wkp.value 1 (Wkp.lowerOrder 1 W) from rfl, Wkp.value_one, hW]

/-- W-PDE1 P4-2 helper: tangential translations map the half-plane `H = {0 < y₁}` into itself. -/
theorem pde_hk_maps {H : Opens X} (hH : (H : Set X) = {y | 0 < y 1}) (t : ℝ) :
    MapsTo (· + t • 𝐞 0) (H : Set X) (H : Set X) := by
  intro x hx
  rw [hH] at hx ⊢
  simpa using hx

/-- W-PDE1 P4-2 helper: the preimage of `H` under a tangential translation is `H`. -/
theorem pde_hk_preimage {H : Opens X} (hH : (H : Set X) = {y | 0 < y 1}) (t : ℝ) :
    (· + t • 𝐞 0) ⁻¹' (H : Set X) = (H : Set X) := by
  ext x
  simp only [mem_preimage, hH, mem_ofPred_eq]
  simp

/-- W-PDE1 P4-2 helper: a tangential translation preserves `volume` restricted to `H`. -/
theorem pde_hk_mp {H : Opens X} (hH : (H : Set X) = {y | 0 < y 1}) (t : ℝ) :
    MeasurePreserving (· + t • 𝐞 0) ((volume : Measure X).restrict H)
      ((volume : Measure X).restrict H) := by
  have h := (measurePreserving_add_right (volume : Measure X) (t • 𝐞 0)).restrict_preimage
    H.isOpen.measurableSet
  rwa [pde_hk_preimage hH t] at h

open TauCeti in
open scoped InnerProductSpace in
/-- W-PDE1 P4-2 helper: on `H`, the tangential difference quotients of `u ∈ W^{1,2}(H)` are
bounded in `L²(H)` by the tangential derivative. -/
theorem pde_hk_dq_bound {H : Opens X} (hH : (H : Set X) = {y | 0 < y 1})
    (u : W1p (volume : Measure X) H 2) (t : ℝ) :
    eLpNorm (fun x => t⁻¹ * (W1p.value u (x + t • 𝐞 0) - W1p.value u x)) 2
        ((volume : Measure X).restrict H) ≤
      eLpNorm (fun x => ⟪𝐞 0, W1p.gradient u x⟫_ℝ) 2 ((volume : Measure X).restrict H) := by
  set K : ℕ → Set X := fun n => closedBall (0 : X) n ∩ {y | 1 / ((n : ℝ) + 1) ≤ y 1} with hKdef
  have hKc : ∀ n, IsCompact (K n) := fun n =>
    (isCompact_closedBall (0 : X) (n : ℝ)).inter_right (isClosed_le continuous_const (by fun_prop))
  have hKH : ∀ n, K n ⊆ (H : Set X) := fun n x hx => by
    rw [hH]
    have h2 : (1 : ℝ) / ((n : ℝ) + 1) ≤ x 1 := hx.2
    show 0 < x 1
    exact lt_of_lt_of_le (by positivity) h2
  have hn : ∀ n, eLpNorm (fun x => t⁻¹ * (W1p.value u (x + t • 𝐞 0) - W1p.value u x)) 2
      ((volume : Measure X).restrict (K n)) ≤
        eLpNorm (fun x => ⟪𝐞 0, W1p.gradient u x⟫_ℝ) 2 ((volume : Measure X).restrict H) :=
    fun n => W1p.eLpNorm_inv_mul_value_comp_add_smul_sub_le (by norm_num) u (𝐞 0) t (hKc n)
      subset_rfl fun x hx s _ => by
        have h := hKH n hx
        rw [hH] at h ⊢
        simpa using h
  have hmono : Monotone K := fun n m hnm x hx => by
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    refine ⟨closedBall_subset_closedBall hnm' hx.1, ?_⟩
    have h2 : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    exact h2.trans hx.2
  have hU : (H : Set X) = ⋃ n, K n := by
    ext x
    constructor
    · intro hx
      rw [hH] at hx
      have hx' : 0 < x 1 := hx
      obtain ⟨n, hn⟩ := exists_nat_ge (max ‖x‖ (1 / x 1))
      refine mem_iUnion.2 ⟨n, ?_, ?_⟩
      · rw [mem_closedBall, dist_zero_right]
        exact (le_max_left _ _).trans hn
      · show 1 / ((n : ℝ) + 1) ≤ x 1
        rw [div_le_iff₀ (by positivity)]
        have h1 : 1 / x 1 ≤ n := (le_max_right _ _).trans hn
        rw [div_le_iff₀ hx'] at h1
        nlinarith
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.1 hx
      exact hKH n hn
  have hrep : ∀ (μ : Measure X) (f : X → ℝ), AEStronglyMeasurable f μ →
      eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹ := by
    intro μ f hf
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf]
    simp only [ENNReal.toReal_ofNat, one_div]
  have hmH : AEStronglyMeasurable (fun x => t⁻¹ * (W1p.value u (x + t • 𝐞 0) - W1p.value u x))
      ((volume : Measure X).restrict H) :=
    (Lp.aestronglyMeasurable _).congr
      (W1p.value_differenceQuotient_ae le_rfl (𝐞 0) t (pde_hk_maps hH t) u)
  have hmG : AEStronglyMeasurable (fun x => ⟪𝐞 0, W1p.gradient u x⟫_ℝ)
      ((volume : Measure X).restrict H) := (Lp.aestronglyMeasurable _).const_inner
  have hn' : ∀ n, ∫⁻ x in K n, ‖t⁻¹ * (W1p.value u (x + t • 𝐞 0) - W1p.value u x)‖ₑ ^ (2 : ℝ) ≤
      ((∫⁻ x in (H : Set X), ‖⟪𝐞 0, W1p.gradient u x⟫_ℝ‖ₑ ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹) ^ (2 : ℝ) :=
    fun n => by
      have h := hn n
      rw [hrep _ _ (hmH.mono_measure (Measure.restrict_mono (hKH n) le_rfl)), hrep _ _ hmG] at h
      exact (ENNReal.rpow_inv_le_iff (by norm_num)).1 h
  rw [hrep _ _ hmH, hrep _ _ hmG]
  set F : X → ℝ≥0∞ := fun x =>
    ‖t⁻¹ * (W1p.value u (x + t • 𝐞 0) - W1p.value u x)‖ₑ ^ (2 : ℝ) with hF
  have hsup : ∫⁻ x in (H : Set X), F x = ⨆ n, ∫⁻ x in K n, F x := by
    rw [hU, setLIntegral_iUnion_of_directed _ hmono.directed_le]
  rw [hsup, ENNReal.rpow_inv_le_iff (by norm_num)]
  exact iSup_le hn'

open TauCeti in
open scoped InnerProductSpace in
/-- W-PDE1 P4-2 helper: test functions on `Ω` are dense in `L²(Ω)`. -/
theorem pde_hk_test_dense {Ω : Opens X} (y : Lp ℝ 2 ((volume : Measure X).restrict Ω)) {ε : ℝ}
    (hε : 0 < ε) : ∃ φ : TestFunction Ω ℝ ⊤,
      ‖y - W1p.value (W1p.ofTestFunctionₗ volume Ω 2 φ)‖ < ε := by
  obtain ⟨u₀, hu₀⟩ := (W1p0.denseRange_valueL_two (mu := (volume : Measure X)) (Omega := Ω)).exists_dist_lt
    y (half_pos hε)
  have hmem : (u₀ : W1p (volume : Measure X) Ω 2) ∈
      closure (Set.range (W1p.ofTestFunctionₗ volume Ω 2)) := by
    rw [← coe_w1p0Submodule]
    exact u₀.2
  obtain ⟨_, ⟨φ, rfl⟩, hφ⟩ := Metric.mem_closure_iff.1 hmem (ε / 2) (half_pos hε)
  refine ⟨φ, ?_⟩
  rw [W1p0.valueL_apply, dist_eq_norm] at hu₀
  rw [dist_eq_norm] at hφ
  have h1 : ‖W1p.value (u₀ : W1p (volume : Measure X) Ω 2) -
      W1p.value (W1p.ofTestFunctionₗ volume Ω 2 φ)‖ < ε / 2 := by
    rw [← W1p.valueL_apply, ← W1p.valueL_apply, ← map_sub]
    exact (W1p.norm_value_le _).trans_lt hφ
  calc ‖y - W1p.value (W1p.ofTestFunctionₗ volume Ω 2 φ)‖
      ≤ ‖y - W1p.value (u₀ : W1p (volume : Measure X) Ω 2)‖ +
          ‖W1p.value (u₀ : W1p (volume : Measure X) Ω 2) -
            W1p.value (W1p.ofTestFunctionₗ volume Ω 2 φ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hu₀ h1
    _ = ε := add_halves ε

open TauCeti in
open scoped InnerProductSpace in
/-- W-PDE1 P4-2 helper: tangential difference quotients of `u ∈ W^{1,2}(H)` converge in `L²(H)` to
the tangential derivative. (Weak convergence from test functions and the uniform bound, then
`‖aₜ - b‖² ≤ 2‖b‖² - 2⟪aₜ, b⟫ → 0`.) -/
theorem pde_hk_dq_tendsto {H : Opens X} (hH : (H : Set X) = {y | 0 < y 1})
    (u : W1p (volume : Measure X) H 2) :
    Tendsto (fun t => ‖W1p.value (W1p.differenceQuotient le_rfl (𝐞 0) t (pde_hk_maps hH t) u) -
      (innerSL ℝ (𝐞 0)).compLp (W1p.gradient u)‖) (𝓝[≠] 0) (𝓝 0) := by
  set a : ℝ → Lp ℝ 2 ((volume : Measure X).restrict H) := fun t =>
    W1p.value (W1p.differenceQuotient le_rfl (𝐞 0) t (pde_hk_maps hH t) u) with ha
  set b : Lp ℝ 2 ((volume : Measure X).restrict H) :=
    (innerSL ℝ (𝐞 0)).compLp (W1p.gradient u) with hb
  have hbae : (b : X → ℝ) =ᵐ[(volume : Measure X).restrict H]
      fun x => ⟪𝐞 0, W1p.gradient u x⟫_ℝ := by
    filter_upwards [(innerSL ℝ (𝐞 0)).coeFn_compLp (W1p.gradient u)] with x hx
    rw [hx, innerSL_apply_apply]
  -- the uniform bound `‖aₜ‖ ≤ ‖b‖`
  have hbd : ∀ t, ‖a t‖ ≤ ‖b‖ := fun t => by
    rw [Lp.norm_def, Lp.norm_def]
    refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top b) ?_
    rw [eLpNorm_congr_ae (W1p.value_differenceQuotient_ae le_rfl (𝐞 0) t (pde_hk_maps hH t) u),
      eLpNorm_congr_ae hbae]
    exact pde_hk_dq_bound hH u t
  -- convergence against test functions
  have hfd : HasWeakLineDerivOn (volume : Measure X) H (W1p.value u)
      (fun x => ⟪W1p.gradient u x, 𝐞 0⟫_ℝ) (𝐞 0) := by
    simpa only [innerSL_apply_apply] using (W1p.hasWeakFDerivOn u).hasWeakLineDerivOn (𝐞 0)
  have htest : ∀ φ : TestFunction H ℝ ⊤, Tendsto
      (fun t => ⟪a t, W1p.value (W1p.ofTestFunctionₗ volume H 2 φ)⟫_ℝ) (𝓝[≠] 0)
      (𝓝 ⟪b, W1p.value (W1p.ofTestFunctionₗ volume H 2 φ)⟫_ℝ) := by
    intro φ
    have hzero : ∀ (F : X → ℝ), ∫ x in (H : Set X), F x * φ x = ∫ x, F x * φ x := fun F =>
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [φ.zero_on_compl hx]
    have hlim := integral_inv_mul_sub_mul_tendsto_neg_integral_lineDeriv_mul
      (Lp.locallyIntegrableOn (W1p.value u) (by norm_num)) φ (𝐞 0)
    have hw := hfd.integral_lineDeriv_smul_eq_neg_integral_smul φ
    simp only [smul_eq_mul] at hw
    have hL : ∀ t, ⟪a t, W1p.value (W1p.ofTestFunctionₗ volume H 2 φ)⟫_ℝ =
        ∫ x, t⁻¹ * (W1p.value u (x + t • 𝐞 0) - W1p.value u x) * φ x := fun t => by
      rw [L2.inner_def, ← hzero]
      refine integral_congr_ae ?_
      filter_upwards [W1p.value_differenceQuotient_ae le_rfl (𝐞 0) t (pde_hk_maps hH t) u,
        W1p.value_ofTestFunctionₗ_ae (mu := (volume : Measure X)) (p := 2) φ] with x h1 h2
      rw [h1, h2]
      simp [mul_comm]
    have hR : ⟪b, W1p.value (W1p.ofTestFunctionₗ volume H 2 φ)⟫_ℝ =
        -∫ x, lineDeriv ℝ (φ : X → ℝ) x (𝐞 0) * W1p.value u x := by
      rw [hw, neg_neg, L2.inner_def]
      calc ∫ x in (H : Set X), ⟪b x, W1p.value (W1p.ofTestFunctionₗ volume H 2 φ) x⟫_ℝ
          = ∫ x in (H : Set X), ⟪W1p.gradient u x, 𝐞 0⟫_ℝ * φ x := by
            refine integral_congr_ae ?_
            filter_upwards [hbae,
              W1p.value_ofTestFunctionₗ_ae (mu := (volume : Measure X)) (p := 2) φ] with x h1 h2
            rw [h1, h2, real_inner_comm (W1p.gradient u x) (𝐞 0)]
            simp
            ring
        _ = ∫ x, (φ : X → ℝ) x * ⟪W1p.gradient u x, 𝐞 0⟫_ℝ := by
            rw [hzero]
            exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    rw [hR]
    exact hlim.congr fun t => (hL t).symm
  -- weak convergence against every `y`
  have hweak : ∀ y, Tendsto (fun t => ⟪a t, y⟫_ℝ) (𝓝[≠] 0) (𝓝 ⟪b, y⟫_ℝ) := by
    intro y
    rw [Metric.tendsto_nhds]
    intro ε hε
    set M := ‖b‖
    have hδ : 0 < ε / (4 * (M + 1)) := by positivity
    obtain ⟨φ, hφ⟩ := pde_hk_test_dense y hδ
    set ψ := W1p.value (W1p.ofTestFunctionₗ volume H 2 φ)
    filter_upwards [Metric.tendsto_nhds.1 (htest φ) (ε / 2) (half_pos hε)] with t ht
    rw [Real.dist_eq] at ht ⊢
    have hsplit : ⟪a t, y⟫_ℝ - ⟪b, y⟫_ℝ = ⟪a t - b, y - ψ⟫_ℝ + (⟪a t, ψ⟫_ℝ - ⟪b, ψ⟫_ℝ) := by
      simp only [inner_sub_left, inner_sub_right]
      ring
    have h1 : |⟪a t - b, y - ψ⟫_ℝ| ≤ 2 * M * (ε / (4 * (M + 1))) := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      have hab : ‖a t - b‖ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith [hbd t])
      exact mul_le_mul hab hφ.le (norm_nonneg _) (by positivity)
    have h2 : 2 * M * (ε / (4 * (M + 1))) < ε / 2 := by
      have hM : 0 ≤ M := norm_nonneg _
      rw [show 2 * M * (ε / (4 * (M + 1))) = ε / 2 * (M / (M + 1)) by field_simp; ring]
      exact mul_lt_of_lt_one_right (half_pos hε) ((div_lt_one (by positivity)).2 (by linarith))
    rw [hsplit]
    calc |⟪a t - b, y - ψ⟫_ℝ + (⟪a t, ψ⟫_ℝ - ⟪b, ψ⟫_ℝ)|
        ≤ |⟪a t - b, y - ψ⟫_ℝ| + |⟪a t, ψ⟫_ℝ - ⟪b, ψ⟫_ℝ| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add (h1.trans_lt h2) ht
      _ = ε := add_halves ε
  -- strong convergence
  have hsq : ∀ t, ‖a t - b‖ ≤ Real.sqrt (2 * ‖b‖ ^ 2 - 2 * ⟪a t, b⟫_ℝ) := fun t => by
    refine Real.le_sqrt_of_sq_le ?_
    rw [norm_sub_sq_real]
    have := hbd t
    nlinarith [norm_nonneg (a t), norm_nonneg b]
  have hlim : Tendsto (fun t => Real.sqrt (2 * ‖b‖ ^ 2 - 2 * ⟪a t, b⟫_ℝ)) (𝓝[≠] 0) (𝓝 0) := by
    have h := ((hweak b).const_mul 2).const_sub (2 * ‖b‖ ^ 2)
    rw [real_inner_self_eq_norm_sq] at h
    simpa using h.sqrt
  exact squeeze_zero (fun t => norm_nonneg _) hsq hlim

open scoped InnerProductSpace in
/-- W-PDE1 P4-2 helper: `‖v‖ ≤ |v₀| + |v₁|` in the plane. -/
theorem pde_hk_norm_le (v : X) : ‖v‖ ≤ ‖⟪v, 𝐞 0⟫_ℝ‖ + ‖⟪v, 𝐞 1⟫_ℝ‖ := by
  have h0 : ‖⟪v, 𝐞 0⟫_ℝ‖ = ‖v 0‖ := by simp [EuclideanSpace.inner_single_right]
  have h1 : ‖⟪v, 𝐞 1⟫_ℝ‖ = ‖v 1‖ := by simp [EuclideanSpace.inner_single_right]
  rw [h0, h1, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  calc √(‖v 0‖ ^ 2 + ‖v 1‖ ^ 2) ≤ √((‖v 0‖ + ‖v 1‖) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [norm_nonneg (v 0), norm_nonneg (v 1)])
    _ = ‖v 0‖ + ‖v 1‖ := Real.sqrt_sq (by positivity)

open TauCeti in
open scoped InnerProductSpace in
/-- W-PDE1 P4-2 helper: if `w ∈ W^{1,2}(H)` has first derivatives `c j ∈ W^{1,2}(H)`, the
`j`-th component of the gradient error of the tangential difference quotient of `w` against
`∇c₀` is the difference-quotient error of `c j` (using `∂ⱼ c₀ = ∂₀ cⱼ`). -/
theorem pde_hk_grad_comp {H : Opens X} (hH : (H : Set X) = {y | 0 < y 1})
    (w : W1p (volume : Measure X) H 2) (c : Fin 2 → W1p (volume : Measure X) H 2)
    (hc : ∀ j, (W1p.value (c j) : X → ℝ) =ᵐ[(volume : Measure X).restrict H]
      fun x => ⟪W1p.gradient w x, 𝐞 j⟫_ℝ) (t : ℝ) (j : Fin 2) :
    ∀ᵐ x ∂(volume : Measure X).restrict H,
      ⟪(W1p.gradient (W1p.differenceQuotient le_rfl (𝐞 0) t (pde_hk_maps hH t) w) -
          W1p.gradient (c 0) : Lp X 2 ((volume : Measure X).restrict H)) x, 𝐞 j⟫_ℝ =
        (W1p.value (W1p.differenceQuotient le_rfl (𝐞 0) t (pde_hk_maps hH t) (c j)) -
          (innerSL ℝ (𝐞 0)).compLp (W1p.gradient (c j)) :
            Lp ℝ 2 ((volume : Measure X).restrict H)) x := by
  have hfd : ∀ (u : W1p (volume : Measure X) H 2) (i : Fin 2),
      HasWeakLineDerivOn (volume : Measure X) H (W1p.value u)
        (fun x => ⟪W1p.gradient u x, 𝐞 i⟫_ℝ) (𝐞 i) := fun u i => by
    simpa only [innerSL_apply_apply] using (W1p.hasWeakFDerivOn u).hasWeakLineDerivOn (𝐞 i)
  have hcw : ∀ i, HasWeakLineDerivOn (volume : Measure X) H (W1p.value w) (W1p.value (c i)) (𝐞 i) :=
    fun i => (hfd w i).congr_ae_deriv (hc i).symm
  -- `∂ⱼ c₀ = ∂₀ cⱼ`
  have hmix : (fun x => ⟪W1p.gradient (c 0) x, 𝐞 j⟫_ℝ) =ᵐ[(volume : Measure X).restrict H]
      fun x => ⟪W1p.gradient (c j) x, 𝐞 0⟫_ℝ :=
    (hfd (c 0) j).ae_eq ((hcw j).comm (hfd (c j) 0) (hcw 0))
  have htr : ∀ᵐ x ∂(volume : Measure X).restrict H,
      W1p.value (c j) (x + t • 𝐞 0) = ⟪W1p.gradient w (x + t • 𝐞 0), 𝐞 j⟫_ℝ :=
    (pde_hk_mp hH t).quasiMeasurePreserving.ae_eq_comp (hc j)
  filter_upwards [Lp.coeFn_sub
      (W1p.gradient (W1p.differenceQuotient le_rfl (𝐞 0) t (pde_hk_maps hH t) w))
      (W1p.gradient (c 0)),
    W1p.gradient_differenceQuotient_ae le_rfl (𝐞 0) t (pde_hk_maps hH t) w, hc j, htr, hmix,
    Lp.coeFn_sub (W1p.value (W1p.differenceQuotient le_rfl (𝐞 0) t (pde_hk_maps hH t) (c j)))
      ((innerSL ℝ (𝐞 0)).compLp (W1p.gradient (c j))),
    W1p.value_differenceQuotient_ae le_rfl (𝐞 0) t (pde_hk_maps hH t) (c j),
    (innerSL ℝ (𝐞 0)).coeFn_compLp (W1p.gradient (c j))] with x h1 h2 h3 h4 h5 h6 h7 h8
  rw [h1, h6]
  simp only [Pi.sub_apply]
  rw [h2, h7, h8, innerSL_apply_apply, inner_sub_left, real_inner_smul_left, inner_sub_left,
    ← h3, ← h4, h5, real_inner_comm (W1p.gradient (c j) x)]

open TauCeti in
open scoped InnerProductSpace in
/-- W-PDE1 P4-2 helper: if `w ∈ W^{1,2}_0(H)` has first derivatives `c j ∈ W^{1,2}(H)`, then the
tangential derivative `c 0` lies in `W^{1,2}_0(H)`: it is the `W^{1,2}` limit of the tangential
difference quotients of `w`, which lie in the closed subspace `W^{1,2}_0(H)`. -/
theorem pde_hk_mem_w1p0 {H : Opens X} (hH : (H : Set X) = {y | 0 < y 1})
    {w : W1p (volume : Measure X) H 2} (hw : w ∈ w1p0Submodule (volume : Measure X) H 2)
    (c : Fin 2 → W1p (volume : Measure X) H 2)
    (hc : ∀ j, (W1p.value (c j) : X → ℝ) =ᵐ[(volume : Measure X).restrict H]
      fun x => ⟪W1p.gradient w x, 𝐞 j⟫_ℝ) :
    c 0 ∈ w1p0Submodule (volume : Measure X) H 2 := by
  have hback : ∀ t : ℝ, ∀ x, x + t • 𝐞 0 ∈ H → x ∈ H := fun t x hx => by
    have hx' : x + t • 𝐞 0 ∈ (H : Set X) := hx
    show x ∈ (H : Set X)
    rw [hH] at hx' ⊢
    simpa using hx'
  have hmem : ∀ t, W1p.differenceQuotient le_rfl (𝐞 0) t (pde_hk_maps hH t) w ∈
      w1p0Submodule (volume : Measure X) H 2 := fun t =>
    W1p.differenceQuotient_mem_w1p0Submodule (by norm_num) (pde_hk_maps hH t) (hback t) hw
  have hval : W1p.value (c 0) = (innerSL ℝ (𝐞 0)).compLp (W1p.gradient w) := by
    refine Lp.ext ?_
    filter_upwards [hc 0, (innerSL ℝ (𝐞 0)).coeFn_compLp (W1p.gradient w)] with x h1 h2
    rw [h1, h2, innerSL_apply_apply, real_inner_comm]
  have hgrad : ∀ t : ℝ,
      ‖W1p.gradient (W1p.differenceQuotient le_rfl (𝐞 0) t (pde_hk_maps hH t) w) -
          W1p.gradient (c 0)‖ ≤
        1 * ‖W1p.value (W1p.differenceQuotient le_rfl (𝐞 0) t (pde_hk_maps hH t) (c 0)) -
            (innerSL ℝ (𝐞 0)).compLp (W1p.gradient (c 0))‖ +
          1 * ‖W1p.value (W1p.differenceQuotient le_rfl (𝐞 0) t (pde_hk_maps hH t) (c 1)) -
            (innerSL ℝ (𝐞 0)).compLp (W1p.gradient (c 1))‖ := fun t =>
    TauCeti.Lp.norm_le_add_of_ae_norm_le zero_le_one zero_le_one (by
      filter_upwards [pde_hk_grad_comp hH w c hc t 0, pde_hk_grad_comp hH w c hc t 1]
        with x h0 h1
      rw [one_mul, one_mul, ← h0, ← h1]
      exact pde_hk_norm_le _)
  have hsplit : ∀ t : ℝ, ‖W1p.differenceQuotient le_rfl (𝐞 0) t (pde_hk_maps hH t) w - c 0‖ ≤
      ‖W1p.value (W1p.differenceQuotient le_rfl (𝐞 0) t (pde_hk_maps hH t) w) - W1p.value (c 0)‖ +
        ‖W1p.gradient (W1p.differenceQuotient le_rfl (𝐞 0) t (pde_hk_maps hH t) w) -
          W1p.gradient (c 0)‖ := fun t => by
    have h := W1p.norm_le_norm_value_add_norm_gradient
      (W1p.differenceQuotient le_rfl (𝐞 0) t (pde_hk_maps hH t) w - c 0)
    have hv : W1p.value (W1p.differenceQuotient le_rfl (𝐞 0) t (pde_hk_maps hH t) w - c 0) =
        W1p.value (W1p.differenceQuotient le_rfl (𝐞 0) t (pde_hk_maps hH t) w) - W1p.value (c 0) :=
      map_sub W1p.valueL _ _
    rw [hv, W1p.gradient_sub] at h
    exact h
  have hlim : Tendsto (fun t => W1p.differenceQuotient le_rfl (𝐞 0) t (pde_hk_maps hH t) w)
      (𝓝[≠] 0) (𝓝 (c 0)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h := (pde_hk_dq_tendsto hH w).add
      ((pde_hk_dq_tendsto hH (c 0)).add (pde_hk_dq_tendsto hH (c 1)))
    simp only [add_zero] at h
    refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) h
    have h2 := hgrad t
    rw [one_mul, one_mul] at h2
    refine (hsplit t).trans ?_
    rw [hval]
    exact add_le_add le_rfl h2
  exact (w1p0Submodule (volume : Measure X) H 2).isClosed.mem_of_tendsto hlim
    (Eventually.of_forall hmem)

/-- W-PDE1 P4-2 helper: a directional derivative of a smooth function that is constant outside a
compact set is smooth with compact support. -/
theorem pde_hk_cderiv {psi : X → ℝ} (hpsi : ContDiff ℝ ∞ psi) {c : ℝ}
    (hc : HasCompactSupport (fun x => psi x - c)) (v : X) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ psi x v) ∧
      HasCompactSupport (fun x => fderiv ℝ psi x v - 0) := by
  refine ⟨(hpsi.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, ?_⟩
  simp only [sub_zero]
  simpa only [fderiv_sub_const] using hc.fderiv_apply (𝕜 := ℝ) v

open TauCeti in
/-- W-PDE1 P4-2 helper: multiplication by a smooth `ψ` that is constant outside a compact set
preserves `W^{k,2}(Ω)`. Adapted from TauCeti `Wkp.exists_value_ae_eq_mul_of_contDiffOn`, whose
compact-closure hypothesis on `Ω` fails for the half-plane. -/
theorem pde_wkp_mul {Ω : Opens X} (k : ℕ) {psi : X → ℝ} (hpsi : ContDiff ℝ ∞ psi) {c : ℝ}
    (hc : HasCompactSupport (fun x => psi x - c)) (u : Wkp (volume : Measure X) Ω 2 k) :
    ∃ w : Wkp (volume : Measure X) Ω 2 k,
      (Wkp.value k w : X → ℝ) =ᵐ[(volume : Measure X).restrict Ω]
        fun x => psi x * Wkp.value k u x := by
  have hLp : ∀ {phi : X → ℝ} {c' : ℝ}, Continuous phi → HasCompactSupport (fun x => phi x - c') →
      ∀ f : Lp ℝ 2 ((volume : Measure X).restrict Ω),
        ∃ g : Lp ℝ 2 ((volume : Measure X).restrict Ω),
          (g : X → ℝ) =ᵐ[(volume : Measure X).restrict Ω] fun x => phi x * f x :=
    fun {phi} {c'} hphi hc' f => by
      obtain ⟨C, hC⟩ := hc'.exists_bound_of_continuous (hphi.sub continuous_const)
      have htop : MemLp phi ⊤ ((volume : Measure X).restrict Ω) :=
        memLp_top_of_bound hphi.aestronglyMeasurable (C + ‖c'‖) (ae_of_all _ fun x => by
          have h := hC x
          calc ‖phi x‖ = ‖(phi x - c') + c'‖ := by rw [sub_add_cancel]
            _ ≤ ‖phi x - c'‖ + ‖c'‖ := norm_add_le _ _
            _ ≤ C + ‖c'‖ := by linarith)
      have h : MemLp (fun x => phi x * f x) 2 ((volume : Measure X).restrict Ω) :=
        htop.fun_mul (Lp.memLp f)
      exact ⟨h.toLp _, h.coeFn_toLp⟩
  induction k generalizing psi c with
  | zero => simpa only [Wkp.value_zero] using hLp hpsi.continuous hc (Wkp.value 0 u)
  | succ k ih =>
    obtain ⟨g, hg⟩ := hLp hpsi.continuous hc (Wkp.value (k + 1) u)
    set b := stdOrthonormalBasis ℝ X
    refine (Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn b g k fun i => ?_).imp
      fun w (hw : Wkp.value (k + 1) w = g) => hw ▸ hg
    -- `∂ᵢ(ψ u) = ψ ∂ᵢu + (∂ᵢψ) u`, and both summands lie in `W^{k,2}(Ω)` by induction.
    obtain ⟨d, hd⟩ := Wkp.exists_hasWeakLineDerivOn_value k u (b i)
    obtain ⟨w₁, hw₁⟩ := ih hpsi hc d
    obtain ⟨hdc, hds⟩ := pde_hk_cderiv hpsi hc (b i)
    obtain ⟨w₂, hw₂⟩ := ih hdc hds (Wkp.lowerOrder k u)
    refine ⟨w₁ + w₂, (((hd.contDiffOn_smul hpsi.contDiffOn).congr_ae ?_).congr_ae_deriv ?_)⟩
    · filter_upwards [hg] with x hx
      rw [hx, smul_eq_mul]
    · filter_upwards [Wkp.value_add k w₁ w₂ ▸ Lp.coeFn_add (Wkp.value k w₁) (Wkp.value k w₂),
        hw₁, hw₂] with x hx h₁ h₂
      rw [hx, Pi.add_apply, h₁, h₂, ← Wkp.value_succ, smul_eq_mul, smul_eq_mul]

open TauCeti in
/-- W-PDE1 P4-2 helper: the Leibniz rule in `W^{k,2}`: if `u, ∂ᵥu ∈ W^{k,2}(Ω)` and `ψ` is smooth
and constant outside a compact set, then `∂ᵥ(ψ u) ∈ W^{k,2}(Ω)`. -/
theorem pde_wkp_leibniz {Ω : Opens X} (k : ℕ) {psi : X → ℝ} (hpsi : ContDiff ℝ ∞ psi) {c : ℝ}
    (hc : HasCompactSupport (fun x => psi x - c)) {u u' : X → ℝ} {v : X}
    (hu : HasWeakLineDerivOn (volume : Measure X) Ω u u' v)
    (U U' : Wkp (volume : Measure X) Ω 2 k)
    (hU : (Wkp.value k U : X → ℝ) =ᵐ[(volume : Measure X).restrict Ω] u)
    (hU' : (Wkp.value k U' : X → ℝ) =ᵐ[(volume : Measure X).restrict Ω] u') :
    ∃ M : Wkp (volume : Measure X) Ω 2 k,
      HasWeakLineDerivOn (volume : Measure X) Ω (fun x => psi x * u x) (Wkp.value k M) v := by
  obtain ⟨w₁, hw₁⟩ := pde_wkp_mul k hpsi hc U'
  obtain ⟨hdc, hds⟩ := pde_hk_cderiv hpsi hc v
  obtain ⟨w₂, hw₂⟩ := pde_wkp_mul k hdc hds U
  refine ⟨w₁ + w₂, ((hu.contDiffOn_smul hpsi.contDiffOn).congr_ae ?_).congr_ae_deriv ?_⟩
  · exact Eventually.of_forall fun x => smul_eq_mul _ _
  · filter_upwards [Wkp.value_add k w₁ w₂ ▸ Lp.coeFn_add (Wkp.value k w₁) (Wkp.value k w₂),
      hw₁, hw₂, hU, hU'] with x hx h₁ h₂ h₃ h₄
    rw [hx, Pi.add_apply, h₁, h₂, h₃, h₄, smul_eq_mul, smul_eq_mul]

/-- W-PDE1 P4-2 helper: for `a` smooth and equal to `1` outside a compact set, a smooth `θ`, equal
to `1` outside a compact set, with `θ a = 1` wherever `a ≥ λ > 0`. -/
theorem pde_hk_theta {a : X → ℝ} (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport (fun x => a x - 1))
    {lam : ℝ} (hlam : 0 < lam) :
    ∃ θ : X → ℝ, ContDiff ℝ ∞ θ ∧ HasCompactSupport (fun x => θ x - 1) ∧
      ∀ x, lam ≤ a x → θ x * a x = 1 := by
  obtain ⟨m, hm0, hm1, hml⟩ : ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ m ≤ lam :=
    ⟨min lam 1, lt_min hlam one_pos, min_le_right _ _, min_le_left _ _⟩
  -- `T s = s` for `s ≥ m` and `T ≥ m / 2`
  have hTc : ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (2 * s / m - 1) * s +
      (1 - Real.smoothTransition (2 * s / m - 1)) * (m / 2)) := by
    have h : ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (2 * s / m - 1)) :=
      Real.smoothTransition.contDiff.comp (by fun_prop)
    exact (h.mul contDiff_id).add ((contDiff_const.sub h).mul contDiff_const)
  have hTeq : ∀ s, m ≤ s → Real.smoothTransition (2 * s / m - 1) * s +
      (1 - Real.smoothTransition (2 * s / m - 1)) * (m / 2) = s := fun s hs => by
    rw [Real.smoothTransition.one_of_one_le]
    · ring
    · rw [le_sub_iff_add_le, le_div_iff₀ hm0]
      linarith
  have hTpos : ∀ s, m / 2 ≤ Real.smoothTransition (2 * s / m - 1) * s +
      (1 - Real.smoothTransition (2 * s / m - 1)) * (m / 2) := fun s => by
    by_cases hs : m / 2 ≤ s
    · have h0 := Real.smoothTransition.nonneg (2 * s / m - 1)
      nlinarith [mul_nonneg h0 (sub_nonneg.2 hs)]
    · rw [Real.smoothTransition.zero_of_nonpos]
      · ring_nf
        exact le_rfl
      · rw [sub_nonpos, div_le_one hm0]
        linarith
  have hT0 : ∀ s, Real.smoothTransition (2 * s / m - 1) * s +
      (1 - Real.smoothTransition (2 * s / m - 1)) * (m / 2) ≠ 0 := fun s =>
    (lt_of_lt_of_le (half_pos hm0) (hTpos s)).ne'
  refine ⟨fun x => (Real.smoothTransition (2 * a x / m - 1) * a x +
      (1 - Real.smoothTransition (2 * a x / m - 1)) * (m / 2))⁻¹,
    (hTc.comp ha).inv fun x => hT0 (a x), ?_, ?_⟩
  · refine hac.mono' fun x hx => subset_tsupport _ ?_
    rw [Function.mem_support] at hx ⊢
    dsimp only at hx
    intro h1
    apply hx
    have h1' : a x = 1 := sub_eq_zero.1 h1
    simp only [h1', hTeq 1 hm1, inv_one, sub_self]
  · intro x hx
    dsimp only
    rw [hTeq _ (hml.trans hx), inv_mul_cancel₀ (by linarith)]

open TauCeti TauCeti.PDE in
open scoped InnerProductSpace in
/-- W-PDE1 P4-2 helper: tangential differentiation of the equation, adapted from TauCeti
`PDE.exists_hasWeakLineDerivOn_and_energyFormH1_eq_setIntegral_of_contDiffOn` (with `pde_wkp_mul`
in place of the compact-closure multiplication lemma): if `u ∈ H^{k+2}(Ω)` solves
`-∂ᵢ(aⁱʲ∂ⱼu) = F` with `F ∈ W^{k+1,2}(Ω)`, then `∂ₑu ∈ H^{k+1}(Ω)` solves the equation with data in
`W^{k,2}(Ω)`. -/
theorem pde_hk_diff_eq {Ω : Opens X} {a : X → Matrix (Fin 2) (Fin 2) ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    (hac : ∀ i j, HasCompactSupport (fun x => a x i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j))
    (hcoeff : MemLp (fun x => energyIntegrand (a x) ((0 : X → X) x) ((0 : X → ℝ) x)) ⊤
      ((volume : Measure X).restrict Ω))
    (k : ℕ) {F : Wkp (volume : Measure X) Ω 2 (k + 1)} {u : W1p (volume : Measure X) Ω 2}
    (w : Wkp (volume : Measure X) Ω 2 (k + 2)) (hw : Wkp.value (k + 2) w = W1p.value u)
    (hu : ∀ v : W1p0 (volume : Measure X) Ω 2,
      energyFormH1 a 0 0 u (v : W1p (volume : Measure X) Ω 2) =
        ∫ x in Ω, Wkp.value (k + 1) F x * W1p.value (v : W1p (volume : Measure X) Ω 2) x)
    (e : X) :
    ∃ (De : Wkp (volume : Measure X) Ω 2 (k + 1)) (G : Wkp (volume : Measure X) Ω 2 k),
      HasWeakLineDerivOn (volume : Measure X) Ω (W1p.value u) (Wkp.value (k + 1) De) e ∧
      ∀ v : W1p0 (volume : Measure X) Ω 2,
        energyFormH1 a 0 0 (Wkp.firstOrder k De) (v : W1p (volume : Measure X) Ω 2) =
          ∫ x in Ω, Wkp.value k G x * W1p.value (v : W1p (volume : Measure X) Ω 2) x := by
  have haΩ : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) Ω := fun i j => (ha i j).contDiffOn
  -- The first and second weak derivatives of `u`, from `u ∈ H^{k+2}(Ω)`.
  choose D hD using fun j => Wkp.exists_hasWeakLineDerivOn_value (k + 1) w (𝐞 j)
  choose E hE using fun i j => Wkp.exists_hasWeakLineDerivOn_value k (D j) (𝐞 i)
  obtain ⟨De, hDe⟩ := Wkp.exists_hasWeakLineDerivOn_value (k + 1) w e
  obtain ⟨Fe, hFe⟩ := Wkp.exists_hasWeakLineDerivOn_value k F e
  rw [hw] at hD hDe
  have hD' : ∀ j, HasWeakLineDerivOn (volume : Measure X) Ω (W1p.value u)
      (W1p.value (Wkp.firstOrder k (D j))) (𝐞 j) := fun j => by
    rw [Wkp.value_firstOrder]; exact hD j
  -- The commutator terms `∂ᵢ∂ₑaⁱʲ ∂ⱼu` and `∂ₑaⁱʲ ∂ᵢ∂ⱼu` lie in `W^{k,2}(Ω)`.
  have hc₁ := fun i j => pde_hk_cderiv (ha i j) (hac i j) e
  have hc₂ := fun i j => pde_hk_cderiv (hc₁ i j).1 (hc₁ i j).2 (𝐞 i)
  choose M₁ hM₁ using fun i j => pde_wkp_mul k (hc₂ i j).1 (hc₂ i j).2 (Wkp.lowerOrder k (D j))
  choose M₂ hM₂ using fun i j => pde_wkp_mul k (hc₁ i j).1 (hc₁ i j).2 (E i j)
  have hd : HasWeakLineDerivOn (volume : Measure X) Ω (W1p.value u)
      (W1p.value (Wkp.firstOrder k De)) e := by
    rw [Wkp.value_firstOrder]; exact hDe
  refine ⟨De, Fe + ∑ i, ∑ j, (M₁ i j + M₂ i j), hDe, ?_⟩
  -- The differentiated equation, tested on test functions.
  have hut := (forall_energyFormH1_eq_setIntegral_iff_forall_testFunction hcoeff _ u).1 hu
  refine (forall_energyFormH1_eq_setIntegral_iff_forall_testFunction hcoeff _ _).2 fun φ => ?_
  rw [energyFormH1_ofTestFunctionₗ_eq_setIntegral_of_hasWeakLineDerivOn haΩ hut hd hD' hFe φ]
  refine integral_congr_ae ?_
  -- Identify the commutator terms with the values of `M₁` and `M₂`.
  have hu₁ : ∀ᵐ x ∂(volume : Measure X).restrict Ω, ∀ i j, Wkp.value k (M₁ i j) x =
      fderiv ℝ (fun y => fderiv ℝ (fun z => a z i j) y e) x (𝐞 i) *
        ⟪W1p.gradient u x, 𝐞 j⟫_ℝ := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    filter_upwards [hM₁ i j, (hD j).ae_eq ((W1p.hasWeakFDerivOn u).hasWeakLineDerivOn (𝐞 j))]
      with x h₁ h₂
    rw [h₁, ← Wkp.value_succ, h₂, innerSL_apply_apply]
  have hu₂ : ∀ᵐ x ∂(volume : Measure X).restrict Ω, ∀ i j, Wkp.value k (M₂ i j) x =
      fderiv ℝ (fun y => a y i j) x e *
        ⟪W1p.gradient (Wkp.firstOrder k (D j)) x, 𝐞 i⟫_ℝ := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    have h := (W1p.hasWeakFDerivOn (Wkp.firstOrder k (D j))).hasWeakLineDerivOn (𝐞 i)
    rw [Wkp.value_firstOrder] at h
    filter_upwards [hM₂ i j, (hE i j).ae_eq h] with x h₁ h₂
    rw [h₁, h₂, innerSL_apply_apply]
  rw [Wkp.value_add]
  filter_upwards [Lp.coeFn_add (Wkp.value k Fe) _,
    Wkp.value_finsetSum_ae k Finset.univ fun i => ∑ j, (M₁ i j + M₂ i j),
    Filter.eventually_all.2 fun i => Wkp.value_finsetSum_ae k Finset.univ fun j => M₁ i j + M₂ i j,
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      Lp.coeFn_add (Wkp.value k (M₁ i j)) (Wkp.value k (M₂ i j)), hu₁, hu₂]
    with x h₁ h₂ h₃ h₄ h₅ h₆
  rw [h₁, Pi.add_apply, h₂]
  simp only [h₃, Wkp.value_add, h₄, Pi.add_apply, h₅, h₆]

open TauCeti TauCeti.PDE in
open scoped InnerProductSpace in
/-- W-PDE1 P4-2 helper (tangential step): if every solution with data in `W^{k,2}(H)` lies in
`H^{k+2}(H)`, and `w ∈ H^{k+2}(H) ∩ H¹₀(H)` solves the equation with data in `W^{k+1,2}(H)`, then
`∂₀w ∈ H^{k+2}(H)`: `∂₀w` lies in `H¹₀(H)` (`pde_hk_mem_w1p0`) and solves the differentiated
equation (`pde_hk_diff_eq`). -/
theorem pde_hk_tan {H : Opens X} (hH : (H : Set X) = {y | 0 < y 1})
    {A : X → Matrix (Fin 2) (Fin 2) ℝ} (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hAc : ∀ i j, HasCompactSupport (fun x => A x i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j))
    (hcoeff : MemLp (fun x => energyIntegrand (A x) ((0 : X → X) x) ((0 : X → ℝ) x)) ⊤
      ((volume : Measure X).restrict H)) (k : ℕ)
    (ih : ∀ (g' : Lp ℝ 2 ((volume : Measure X).restrict H)) {w' : W1p0 (volume : Measure X) H 2},
      IsWeakSolutionDirichlet A 0 0 g' w' →
      (∃ G : Wkp (volume : Measure X) H 2 k,
        (Wkp.value k G : X → ℝ) =ᵐ[(volume : Measure X).restrict H] g') →
      ∃ W : Wkp (volume : Measure X) H 2 (k + 2),
        (Wkp.value (k + 2) W : X → ℝ) =ᵐ[(volume : Measure X).restrict H]
          W1p.value (w' : W1p (volume : Measure X) H 2))
    {w : W1p0 (volume : Measure X) H 2} {G : Wkp (volume : Measure X) H 2 (k + 1)}
    (hu : ∀ v : W1p0 (volume : Measure X) H 2,
      energyFormH1 A 0 0 (w : W1p (volume : Measure X) H 2) (v : W1p (volume : Measure X) H 2) =
        ∫ x in H, Wkp.value (k + 1) G x * W1p.value (v : W1p (volume : Measure X) H 2) x)
    (W : Wkp (volume : Measure X) H 2 (k + 2))
    (hWU : Wkp.value (k + 2) W = W1p.value (w : W1p (volume : Measure X) H 2)) :
    ∃ Wd : Wkp (volume : Measure X) H 2 (k + 2), HasWeakLineDerivOn volume H
      (W1p.value (w : W1p (volume : Measure X) H 2)) (Wkp.value (k + 2) Wd) (𝐞 0) := by
  set U : W1p (volume : Measure X) H 2 := (w : W1p (volume : Measure X) H 2) with hUdef
  have hfd : ∀ z, HasWeakLineDerivOn volume H (W1p.value U)
      (fun x => ⟪W1p.gradient U x, z⟫_ℝ) z := fun z => by
    simpa only [innerSL_apply_apply] using (W1p.hasWeakFDerivOn U).hasWeakLineDerivOn z
  obtain ⟨De, Gt, hDe, hdeq⟩ := pde_hk_diff_eq hA hAc hcoeff k W hWU hu (𝐞 0)
  obtain ⟨D1, hD1⟩ := Wkp.exists_hasWeakLineDerivOn_value (k + 1) W (𝐞 1)
  rw [hWU] at hD1
  have hc0 : (Wkp.value (k + 1) De : X → ℝ) =ᵐ[(volume : Measure X).restrict H]
      fun x => ⟪W1p.gradient U x, 𝐞 0⟫_ℝ := hDe.ae_eq (hfd (𝐞 0))
  have hc1 : (Wkp.value (k + 1) D1 : X → ℝ) =ᵐ[(volume : Measure X).restrict H]
      fun x => ⟪W1p.gradient U x, 𝐞 1⟫_ℝ := hD1.ae_eq (hfd (𝐞 1))
  obtain ⟨cc, hcc⟩ : ∃ cc : Fin 2 → W1p (volume : Measure X) H 2,
      cc = ![Wkp.firstOrder k De, Wkp.firstOrder k D1] := ⟨_, rfl⟩
  have hcc' : ∀ j, (W1p.value (cc j) : X → ℝ) =ᵐ[(volume : Measure X).restrict H]
      fun x => ⟪W1p.gradient U x, 𝐞 j⟫_ℝ := by
    intro j
    rw [hcc]
    fin_cases j
    · show (W1p.value (Wkp.firstOrder k De) : X → ℝ) =ᵐ[(volume : Measure X).restrict H]
        fun x => ⟪W1p.gradient U x, 𝐞 0⟫_ℝ
      rw [Wkp.value_firstOrder]; exact hc0
    · show (W1p.value (Wkp.firstOrder k D1) : X → ℝ) =ᵐ[(volume : Measure X).restrict H]
        fun x => ⟪W1p.gradient U x, 𝐞 1⟫_ℝ
      rw [Wkp.value_firstOrder]; exact hc1
  have hwmem : U ∈ w1p0Submodule (volume : Measure X) H 2 :=
    (ClosedSubmodule.mem_toSubmodule_iff _ _).1 w.2
  have hmem : Wkp.firstOrder k De ∈ w1p0Submodule (volume : Measure X) H 2 := by
    have h := pde_hk_mem_w1p0 hH hwmem cc hcc'
    rwa [hcc] at h
  -- `∂₀w ∈ H¹₀` solves the differentiated equation, so `∂₀w ∈ H^{k+2}` by hypothesis
  obtain ⟨Wd, hWd⟩ := ih (Wkp.value k Gt)
    (w' := ⟨Wkp.firstOrder k De, (ClosedSubmodule.mem_toSubmodule_iff _ _).2 hmem⟩)
    ((isWeakSolutionDirichlet_iff _ _).2 hdeq) ⟨Gt, EventuallyEq.rfl⟩
  have hWd' : (Wkp.value (k + 2) Wd : X → ℝ) =ᵐ[(volume : Measure X).restrict H]
      Wkp.value (k + 1) De := by
    have h := hWd
    rwa [show ((⟨Wkp.firstOrder k De, (ClosedSubmodule.mem_toSubmodule_iff _ _).2 hmem⟩ :
      W1p0 (volume : Measure X) H 2) : W1p (volume : Measure X) H 2) = Wkp.firstOrder k De from rfl,
      Wkp.value_firstOrder] at h
  exact ⟨Wd, hDe.congr_ae_deriv hWd'.symm⟩

open TauCeti TauCeti.PDE in
open scoped InnerProductSpace in
/-- W-PDE1 P4-2 helper (normal step): if `w ∈ H^{k+2}(H)` solves the equation with data in
`W^{k+1,2}(H)` and `∂₀w ∈ H^{k+2}(H)`, then `∂₁w ∈ H^{k+2}(H)`: the strong form of the equation
(`pde_hs_normal`) gives `∂₁(A¹¹∂₁w) ∈ H^{k+1}`, and `∂₁w = θ A¹¹∂₁w` with `θ = 1/A¹¹` on `H`. -/
theorem pde_hk_nor {H : Opens X} {A : X → Matrix (Fin 2) (Fin 2) ℝ} {lam Lam : ℝ}
    (hell : TauCeti.PDE.UniformlyEllipticOn (H : Set X) A lam Lam)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hAc : ∀ i j, HasCompactSupport (fun x => A x i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j))
    (hcoeff : MemLp (fun x => energyIntegrand (A x) ((0 : X → X) x) ((0 : X → ℝ) x)) ⊤
      ((volume : Measure X).restrict H))
    (g : Lp ℝ 2 ((volume : Measure X).restrict H)) {w : W1p0 (volume : Measure X) H 2}
    (hw : IsWeakSolutionDirichlet A 0 0 g w) (k : ℕ) (G : Wkp (volume : Measure X) H 2 (k + 1))
    (hG : (Wkp.value (k + 1) G : X → ℝ) =ᵐ[(volume : Measure X).restrict H] g)
    (W : Wkp (volume : Measure X) H 2 (k + 2))
    (hWU : Wkp.value (k + 2) W = W1p.value (w : W1p (volume : Measure X) H 2))
    (Wd : Wkp (volume : Measure X) H 2 (k + 2))
    (hdx0 : HasWeakLineDerivOn volume H (W1p.value (w : W1p (volume : Measure X) H 2))
      (Wkp.value (k + 2) Wd) (𝐞 0)) :
    ∃ C1 : Wkp (volume : Measure X) H 2 (k + 2), HasWeakLineDerivOn volume H
      (W1p.value (w : W1p (volume : Measure X) H 2)) (Wkp.value (k + 2) C1) (𝐞 1) := by
  set U : W1p (volume : Measure X) H 2 := (w : W1p (volume : Measure X) H 2) with hUdef
  have hHm : MeasurableSet (H : Set X) := H.isOpen.measurableSet
  have hlam : 0 < lam := hell.1
  have hA11 : ∀ x ∈ (H : Set X), lam ≤ A x 1 1 := fun x hx => by
    have h := (hell.2.2 hx).1 (𝐞 1)
    simpa [Matrix.toQuadraticForm'_apply, dotProduct, Matrix.mulVec, Fin.sum_univ_two] using h
  obtain ⟨θ, hθ, hθc, hθA⟩ := pde_hk_theta (hA 1 1) (hAc 1 1) hlam
  have hfd : ∀ z, HasWeakLineDerivOn volume H (W1p.value U)
      (fun x => ⟪W1p.gradient U x, z⟫_ℝ) z := fun z => by
    simpa only [innerSL_apply_apply] using (W1p.hasWeakFDerivOn U).hasWeakLineDerivOn z
  obtain ⟨D1, hD1⟩ := Wkp.exists_hasWeakLineDerivOn_value (k + 1) W (𝐞 1)
  rw [hWU] at hD1
  have hc1 : (Wkp.value (k + 1) D1 : X → ℝ) =ᵐ[(volume : Measure X).restrict H]
      fun x => ⟪W1p.gradient U x, 𝐞 1⟫_ℝ := hD1.ae_eq (hfd (𝐞 1))
  have hc0' : (Wkp.value (k + 2) Wd : X → ℝ) =ᵐ[(volume : Measure X).restrict H]
      fun x => ⟪W1p.gradient U x, 𝐞 0⟫_ℝ := hdx0.ae_eq (hfd (𝐞 0))
  -- second derivatives; `∂₀∂₁w = ∂₁∂₀w`
  obtain ⟨E00, hE00⟩ := Wkp.exists_hasWeakLineDerivOn_value (k + 1) Wd (𝐞 0)
  obtain ⟨E01, hE01⟩ := Wkp.exists_hasWeakLineDerivOn_value (k + 1) Wd (𝐞 1)
  have hD10 : HasWeakLineDerivOn volume H (Wkp.value (k + 1) D1) (Wkp.value (k + 1) E01)
      (𝐞 0) :=
    hdx0.comm hE01 hD1
  -- the strong form of the equation in the normal direction
  obtain ⟨M00, hM00⟩ := pde_wkp_leibniz (k + 1) (hA 0 0) (hAc 0 0) (hE00.congr_ae hc0')
    (Wkp.lowerOrder (k + 1) Wd) E00 hc0' EventuallyEq.rfl
  obtain ⟨M01, hM01⟩ := pde_wkp_leibniz (k + 1) (hA 0 1) (hAc 0 1) (hD10.congr_ae hc1)
    D1 E01 hc1 EventuallyEq.rfl
  obtain ⟨M10, hM10⟩ := pde_wkp_leibniz (k + 1) (hA 1 0) (hAc 1 0) (hE01.congr_ae hc0')
    (Wkp.lowerOrder (k + 1) Wd) E01 hc0' EventuallyEq.rfl
  have hUt := (forall_energyFormH1_eq_setIntegral_iff_forall_testFunction hcoeff g U).1
    ((isWeakSolutionDirichlet_iff g w).1 hw)
  have hn := pde_hs_normal (fun i j => (hA i j).continuous.continuousOn)
    (Lp.locallyIntegrableOn g (by norm_num)) hUt
    (by simpa only [smul_eq_mul] using hM00) (by simpa only [smul_eq_mul] using hM01)
    (by simpa only [smul_eq_mul] using hM10)
  -- the data of the normal derivative lies in `H^{k+1}`
  have hR : (Wkp.value (k + 1) ((-1 : ℝ) • (G + M00 + M01 + M10)) : X → ℝ)
      =ᵐ[(volume : Measure X).restrict H]
      fun x => -(g x + Wkp.value (k + 1) M00 x + Wkp.value (k + 1) M01 x +
        Wkp.value (k + 1) M10 x) := by
    rw [Wkp.value_smul, Wkp.value_add, Wkp.value_add, Wkp.value_add]
    filter_upwards [Lp.coeFn_smul (-1 : ℝ) (Wkp.value (k + 1) G + Wkp.value (k + 1) M00 +
        Wkp.value (k + 1) M01 + Wkp.value (k + 1) M10),
      Lp.coeFn_add (Wkp.value (k + 1) G + Wkp.value (k + 1) M00 + Wkp.value (k + 1) M01)
        (Wkp.value (k + 1) M10),
      Lp.coeFn_add (Wkp.value (k + 1) G + Wkp.value (k + 1) M00) (Wkp.value (k + 1) M01),
      Lp.coeFn_add (Wkp.value (k + 1) G) (Wkp.value (k + 1) M00), hG] with x h1 h2 h3 h4 h5
    rw [h1, Pi.smul_apply, h2, Pi.add_apply, h3, Pi.add_apply, h4, Pi.add_apply, h5, smul_eq_mul,
      neg_one_mul]
  obtain ⟨P, hP⟩ := pde_wkp_mul (k + 1) (hA 1 1) (hAc 1 1) D1
  have hP' : (Wkp.value (k + 1) P : X → ℝ) =ᵐ[(volume : Measure X).restrict H]
      fun x => A x 1 1 * ⟪W1p.gradient U x, 𝐞 1⟫_ℝ := by
    filter_upwards [hP, hc1] with x h1 h2
    rw [h1, h2]
  obtain ⟨M11, hM11⟩ := pde_wkp_leibniz (k + 1) hθ hθc
    (by simpa only [smul_eq_mul] using hn) P ((-1 : ℝ) • (G + M00 + M01 + M10)) hP' hR
  have hD11 : HasWeakLineDerivOn volume H (Wkp.value (k + 1) D1) (Wkp.value (k + 1) M11)
      (𝐞 1) :=
    hM11.congr_ae (by
      filter_upwards [ae_restrict_mem hHm, hc1] with x hx h1
      rw [h1, ← mul_assoc, hθA x (hA11 x hx), one_mul])
  -- `∂₁w ∈ H^{k+2}`
  obtain ⟨C1, hC1⟩ := Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn 𝐞
    (Wkp.value (k + 1) D1) (k + 1) (Fin.forall_fin_two.2 ⟨⟨E01, hD10⟩, ⟨M11, hD11⟩⟩)
  refine ⟨C1, ?_⟩
  rw [hC1]
  exact hD1

open TauCeti TauCeti.PDE in
open scoped InnerProductSpace in
/-- W-PDE1 P4-2 (flat model, higher order): in the setting of P4-1, if moreover `g ∈ H^k(H)`,
then `w ∈ H^{k+2}(H)`. -/
theorem pde_hs_Hk {H : Opens X} (hH : (H : Set X) = {y | 0 < y 1})
    {A : X → Matrix (Fin 2) (Fin 2) ℝ} {lam Lam : ℝ}
    (hell : TauCeti.PDE.UniformlyEllipticOn (H : Set X) A lam Lam)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hAc : ∀ i j, HasCompactSupport (fun x => A x i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j))
    (g : Lp ℝ 2 ((volume : Measure X).restrict H)) {w : TauCeti.W1p0 (volume : Measure X) H 2}
    (hw : TauCeti.PDE.IsWeakSolutionDirichlet A 0 0 g w) (k : ℕ)
    (hg : ∃ G : TauCeti.Wkp (volume : Measure X) H 2 k,
      (TauCeti.Wkp.value k G : X → ℝ) =ᵐ[(volume : Measure X).restrict H] g) :
    ∃ W : TauCeti.Wkp (volume : Measure X) H 2 (k + 2),
      (TauCeti.Wkp.value (k + 2) W : X → ℝ) =ᵐ[(volume : Measure X).restrict H]
        TauCeti.W1p.value (w : TauCeti.W1p (volume : Measure X) H 2) := by
  have hlam : 0 < lam := hell.1
  have hcoeff : MemLp (fun x => energyIntegrand (A x) ((0 : X → X) x) ((0 : X → ℝ) x)) ⊤
      ((volume : Measure X).restrict H) :=
    memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0) (hlam.le.trans hell.2.1)
      (Continuous.aestronglyMeasurable (β := Fin 2 → Fin 2 → ℝ)
        (continuous_pi fun i => continuous_pi fun j => (hA i j).continuous))
      aestronglyMeasurable_const aestronglyMeasurable_const
      (fun x hx => (hell.2.2 hx).2) (fun _ _ => by simp) (fun _ _ => by simp)
  induction k generalizing g w with
  | zero =>
    obtain ⟨W, hW⟩ := pde_hs_H2 hH hell hA hAc g hw
    exact ⟨W, hW⟩
  | succ k ih =>
    obtain ⟨G, hG⟩ := hg
    -- `w ∈ H^{k+2}` by the induction hypothesis
    obtain ⟨W, hW⟩ := ih g hw ⟨Wkp.lowerOrder k G, hG⟩
    have hWU : Wkp.value (k + 2) W = W1p.value (w : W1p (volume : Measure X) H 2) := Lp.ext hW
    have hu : ∀ v : W1p0 (volume : Measure X) H 2,
        energyFormH1 A 0 0 (w : W1p (volume : Measure X) H 2) (v : W1p (volume : Measure X) H 2) =
          ∫ x in H, Wkp.value (k + 1) G x * W1p.value (v : W1p (volume : Measure X) H 2) x :=
      fun v => by
        rw [(isWeakSolutionDirichlet_iff g w).1 hw v]
        refine integral_congr_ae ?_
        filter_upwards [hG] with x hx
        rw [hx]
    -- `∂₀w, ∂₁w ∈ H^{k+2}`, so `w ∈ H^{k+3}`
    obtain ⟨Wd, hdx0⟩ := pde_hk_tan hH hA hAc hcoeff k (fun g' _ hw' hg' => ih g' hw' hg') hu W hWU
    obtain ⟨C1, hdx1⟩ := pde_hk_nor hell hA hAc hcoeff g hw k G hG W hWU Wd hdx0
    obtain ⟨W', hW'⟩ := Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn 𝐞
      (W1p.value (w : W1p (volume : Measure X) H 2)) (k + 2)
      (Fin.forall_fin_two.2 ⟨⟨Wd, hdx0⟩, ⟨C1, hdx1⟩⟩)
    exact ⟨W', by rw [hW']⟩

/-- W-PDE1 P4-3 (flattening chart): near a regular point `x₀` of the zero set of a smooth `ψ`
there is a smooth chart `e`, with smooth inverse, sending `x₀` to `0` and `ψ` to `-y₁`. -/
theorem pde_flat_chart {ψ : X → ℝ} (hψ : ContDiff ℝ ∞ ψ) {x₀ : X} (hx₀ : ψ x₀ = 0)
    (hd : fderiv ℝ ψ x₀ ≠ 0) :
    ∃ e : OpenPartialHomeomorph X X, x₀ ∈ e.source ∧ e x₀ = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ x ∈ e.source, ψ x = -(e x) 1 := by
  set e0 : X := EuclideanSpace.single 0 1
  set e1 : X := EuclideanSpace.single 1 1
  have hdec : ∀ v : X, v = v 0 • e0 + v 1 • e1 := fun v => by
    ext i
    fin_cases i <;> simp [e0, e1]
  set D := fderiv ℝ ψ x₀ with hD_def
  -- `n` represents `Dψ(x₀)`, so `Dψ(x₀) n = |∇ψ(x₀)|² ≠ 0`
  set n : X := D e0 • e0 + D e1 • e1 with hn_def
  have hDn : D n ≠ 0 := by
    have h : D n = D e0 ^ 2 + D e1 ^ 2 := by
      simp only [hn_def, map_add, map_smul, smul_eq_mul]
      ring
    rw [h]
    intro h0
    apply hd
    have ha : D e0 = 0 := by nlinarith [sq_nonneg (D e0), sq_nonneg (D e1)]
    have hb : D e1 = 0 := by nlinarith [sq_nonneg (D e0), sq_nonneg (D e1)]
    ext v
    rw [hdec v, map_add, map_smul, map_smul, ha, hb]
    simp
  -- the chart `Φ x = (P (x - x₀), -ψ x)`, with `P` vanishing on `n`
  set P : X →L[ℝ] ℝ := D e0 • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2) -
    D e1 • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) with hP_def
  have hPv : ∀ v : X, P v = D e0 * v 1 - D e1 * v 0 := fun v => by
    simp [hP_def]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : X → X, Φ = fun x => (P x - P x₀) • e0 + (-ψ x) • e1 := ⟨_, rfl⟩
  have hΦ1 : ∀ x, Φ x 1 = -ψ x := fun x => by
    simp [hΦ, e0, e1]
  have hΦx₀ : Φ x₀ = 0 := by
    simp [hΦ, hx₀]
  have hΦc : ContDiff ℝ ∞ Φ := by
    rw [hΦ]
    exact ((P.contDiff.sub contDiff_const).smul contDiff_const).add
      (hψ.neg.smul contDiff_const)
  obtain ⟨L, hL⟩ : ∃ L : X → X →L[ℝ] X,
      L = fun x => P.smulRight e0 + (-fderiv ℝ ψ x).smulRight e1 := ⟨_, rfl⟩
  have hΦd : ∀ x, HasFDerivAt Φ (L x) x := fun x => by
    rw [hΦ, hL]
    exact ((P.hasFDerivAt.sub_const _).smul_const e0).add
      ((hψ.differentiable (by simp) x).hasFDerivAt.neg.smul_const e1)
  -- the derivative is invertible wherever `Dψ(x) n ≠ 0`
  set W : Set X := {x | fderiv ℝ ψ x n ≠ 0} with hW_def
  have hW : IsOpen W :=
    isOpen_ne_fun ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const) continuous_const
  have hx₀W : x₀ ∈ W := hDn
  have hinj : ∀ x ∈ W, Function.Injective (L x) := by
    intro x hx
    refine (injective_iff_map_eq_zero (L x)).2 fun v hv => ?_
    have hv' : P v • e0 + (-fderiv ℝ ψ x v) • e1 = 0 := by
      simpa [hL] using hv
    have c0 := congrArg (fun z : X => z 0) hv'
    have c1 := congrArg (fun z : X => z 1) hv'
    simp [e0, e1, hPv] at c0 c1
    have hDv : v 0 * fderiv ℝ ψ x e0 + v 1 * fderiv ℝ ψ x e1 = 0 := by
      have h := hdec v
      rw [h, map_add, map_smul, map_smul] at c1
      simpa using c1
    have hnn : fderiv ℝ ψ x n = D e0 * fderiv ℝ ψ x e0 + D e1 * fderiv ℝ ψ x e1 := by
      simp only [hn_def, map_add, map_smul, smul_eq_mul]
    have hx' : D e0 * fderiv ℝ ψ x e0 + D e1 * fderiv ℝ ψ x e1 ≠ 0 := hnn ▸ hx
    have h0 : v 0 * (D e0 * fderiv ℝ ψ x e0 + D e1 * fderiv ℝ ψ x e1) = 0 := by
      linear_combination D e0 * hDv - fderiv ℝ ψ x e1 * c0
    have h1 : v 1 * (D e0 * fderiv ℝ ψ x e0 + D e1 * fderiv ℝ ψ x e1) = 0 := by
      linear_combination D e1 * hDv + fderiv ℝ ψ x e0 * c0
    have hv0 : v 0 = 0 := (mul_eq_zero.1 h0).resolve_right hx'
    have hv1 : v 1 = 0 := (mul_eq_zero.1 h1).resolve_right hx'
    rw [hdec v, hv0, hv1]
    simp
  have hequiv : ∀ x ∈ W, ∃ L' : X ≃L[ℝ] X, HasFDerivAt Φ (L' : X →L[ℝ] X) x := by
    intro x hx
    refine ⟨(LinearEquiv.ofInjectiveEndo (L x).toLinearMap (hinj x hx)).toContinuousLinearEquiv,
      ?_⟩
    have hcoe : (((LinearEquiv.ofInjectiveEndo (L x).toLinearMap
        (hinj x hx)).toContinuousLinearEquiv : X ≃L[ℝ] X) : X →L[ℝ] X) = L x :=
      ContinuousLinearMap.ext fun _ => rfl
    rw [hcoe]
    exact hΦd x
  obtain ⟨L₀, hL₀⟩ := hequiv x₀ hx₀W
  let e₀ := (hΦc.contDiffAt (x := x₀)).toOpenPartialHomeomorph Φ hL₀ (by simp)
  let e := e₀.restrOpen W hW
  refine ⟨e, ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ hL₀ (by simp), hx₀W⟩, hΦx₀,
    hΦc.contDiffOn, fun a ha => ?_, fun x _ => ?_⟩
  · have hxs : e.symm a ∈ e.source := e.map_target ha
    obtain ⟨L', hL'⟩ := hequiv (e.symm a) hxs.2
    exact (e.contDiffAt_symm ha hL' hΦc.contDiffAt).contDiffWithinAt
  · change ψ x = -(Φ x 1)
    rw [hΦ1]
    ring


/-- W-PDE1 P4 helper: a smooth `κ` with support inside an open set on which `f` is smooth makes
`κ f` smooth everywhere. -/
theorem pde_bd_cs {S : Set X} (hS : IsOpen S) {κ f : X → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (hκS : tsupport κ ⊆ S) (hf : ContDiffOn ℝ ∞ f S) : ContDiff ℝ ∞ (fun x => κ x * f x) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ S
  · exact hκ.contDiffAt.mul (hf.contDiffAt (hS.mem_nhds hx))
  · have hxt : x ∉ tsupport κ := fun h => hx (hκS h)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport κ).isOpen_compl.mem_nhds hxt] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]

open TauCeti in
/-- W-PDE1 P4 helper (zero extension in `W^{k,2}`): for `V ≤ W` and a smooth compactly supported
`κ` whose support meets `W` only inside `V`, `κ u` extended by zero lies in `W^{k,2}(W)` whenever
`u ∈ W^{k,2}(V)`. -/
theorem pde_bd_ext {V W : Opens X} (hVW : V ≤ W) (k : ℕ) {κ : X → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (hκc : HasCompactSupport κ) (hs : (W : Set X) ∩ tsupport κ ⊆ V)
    (u : Wkp (volume : Measure X) V 2 k) :
    ∃ w : Wkp (volume : Measure X) W 2 k,
      (Wkp.value k w : X → ℝ) =ᵐ[(volume : Measure X).restrict W]
        fun x => κ x * Wkp.value k u x := by
  have hVm : MeasurableSet (V : Set X) := V.isOpen.measurableSet
  have hVsub : (V : Set X) ⊆ W := hVW
  -- the `L²` step: `φ f`, extended by zero, for `φ` bounded with support meeting `W` inside `V`
  have hLp : ∀ {φ : X → ℝ}, Continuous φ → HasCompactSupport φ →
      (W : Set X) ∩ tsupport φ ⊆ V → ∀ f : Lp ℝ 2 ((volume : Measure X).restrict V),
        ∃ g : Lp ℝ 2 ((volume : Measure X).restrict W),
          (g : X → ℝ) =ᵐ[(volume : Measure X).restrict W] fun x => φ x * f x := by
    intro φ hφ hφc hφs f
    obtain ⟨C, hC⟩ := hφc.exists_bound_of_continuous hφ
    have h1 : MemLp (fun x => φ x * f x) 2 ((volume : Measure X).restrict V) :=
      (memLp_top_of_bound hφ.aestronglyMeasurable C (ae_of_all _ hC)).fun_mul (Lp.memLp f)
    have h2 : MemLp ((V : Set X).indicator fun x => φ x * f x) 2
        ((volume : Measure X).restrict W) := by
      rw [memLp_indicator_iff_restrict hVm.nullMeasurableSet, Measure.restrict_restrict hVm,
        inter_eq_left.2 hVsub]
      exact h1
    refine ⟨h2.toLp _, h2.coeFn_toLp.trans
      ((ae_restrict_mem W.isOpen.measurableSet).mono fun x hxW => ?_)⟩
    by_cases hxV : x ∈ (V : Set X)
    · rw [indicator_of_mem hxV]
    · rw [indicator_of_notMem hxV]
      show (0 : ℝ) = φ x * f x
      rw [image_eq_zero_of_notMem_tsupport (fun h => hxV (hφs ⟨hxW, h⟩)), zero_mul]
  induction k generalizing κ with
  | zero => simpa only [Wkp.value_zero] using hLp hκ.continuous hκc hs (Wkp.value 0 u)
  | succ k ih =>
    obtain ⟨g, hg⟩ := hLp hκ.continuous hκc hs (Wkp.value (k + 1) u)
    set b := stdOrthonormalBasis ℝ X
    refine (Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn b g k fun i => ?_).imp
      fun w (hw : Wkp.value (k + 1) w = g) => hw ▸ hg
    -- `∂ᵢ(κ u) = κ ∂ᵢu + (∂ᵢκ) u` on `V`, extended by zero to `W`
    obtain ⟨d, hd⟩ := Wkp.exists_hasWeakLineDerivOn_value k u (b i)
    obtain ⟨w₁, hw₁⟩ := ih hκ hκc hs d
    have hdc : ContDiff ℝ ∞ (fun x => fderiv ℝ κ x (b i)) :=
      (hκ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hdt : tsupport (fun x => fderiv ℝ κ x (b i)) ⊆ tsupport κ :=
      tsupport_fderiv_apply_subset ℝ (b i)
    obtain ⟨w₂, hw₂⟩ := ih hdc (hκc.fderiv_apply (𝕜 := ℝ) (b i))
      (fun x hx => hs ⟨hx.1, hdt hx.2⟩) (Wkp.lowerOrder k u)
    have hz : ∀ x, x ∉ tsupport κ → κ x = 0 ∧ fderiv ℝ κ x (b i) = 0 := fun x hx =>
      ⟨image_eq_zero_of_notMem_tsupport hx,
        image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ κ x (b i)) fun h => hx (hdt h)⟩
    have hD := (hd.contDiffOn_smul hκ.contDiffOn).indicator_of_isClosed (V := W)
      (isClosed_tsupport κ) hs (ae_of_all _ fun x hx => by simp [(hz x hx).1])
      (ae_of_all _ fun x hx => by simp [(hz x hx).1, (hz x hx).2])
    refine ⟨w₁ + w₂, (hD.congr_ae ?_).congr_ae_deriv ?_⟩
    · filter_upwards [hg, ae_restrict_mem W.isOpen.measurableSet] with x hx hxW
      rw [hx]
      by_cases hxV : x ∈ (V : Set X)
      · rw [indicator_of_mem hxV, smul_eq_mul]
      · rw [indicator_of_notMem hxV, (hz x fun h => hxV (hs ⟨hxW, h⟩)).1, zero_mul]
    · filter_upwards [Wkp.value_add k w₁ w₂ ▸ Lp.coeFn_add (Wkp.value k w₁) (Wkp.value k w₂),
        hw₁, hw₂, ae_restrict_mem W.isOpen.measurableSet] with x hx h₁ h₂ hxW
      rw [hx, Pi.add_apply, h₁, h₂]
      by_cases hxV : x ∈ (V : Set X)
      · rw [indicator_of_mem hxV, ← Wkp.value_succ, smul_eq_mul, smul_eq_mul]
      · obtain ⟨h0, h0'⟩ := hz x fun h => hxV (hs ⟨hxW, h⟩)
        rw [indicator_of_notMem hxV, h0, h0', zero_mul, zero_mul, add_zero]

open TauCeti in
open scoped InnerProductSpace in
/-- W-PDE1 P4 helper (data in `W^{k,2}`, up to the boundary): if `v ∈ H^{k+1}(V)` and the
coefficients are smooth with supports meeting `W` only inside `V`, then
`κ₀ + ⟪κ, ∇v⟫ + κ₁ v`, extended by zero, lies in `W^{k,2}(W)`. -/
theorem pde_bd_rhs {V Ω W : Opens X} (hVΩ : V ≤ Ω) (hVW : V ≤ W)
    (hVm : (volume : Measure X) V < ⊤) (v : W1p (volume : Measure X) Ω 2) (k : ℕ)
    (hv : ∃ Wv : Wkp (volume : Measure X) V 2 (k + 1),
      (Wkp.value (k + 1) Wv : X → ℝ) =ᵐ[(volume : Measure X).restrict V] W1p.value v)
    {κ₀ κ₁ : X → ℝ} {κ : X → X}
    (h₀ : ContDiff ℝ ∞ κ₀) (h₀c : HasCompactSupport κ₀) (h₀s : (W : Set X) ∩ tsupport κ₀ ⊆ V)
    (h : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ) (hs : (W : Set X) ∩ tsupport κ ⊆ V)
    (h₁ : ContDiff ℝ ∞ κ₁) (h₁c : HasCompactSupport κ₁) (h₁s : (W : Set X) ∩ tsupport κ₁ ⊆ V) :
    ∃ G : Wkp (volume : Measure X) W 2 k,
      (Wkp.value k G : X → ℝ) =ᵐ[(volume : Measure X).restrict W]
        fun y => κ₀ y + ⟪κ y, W1p.gradient v y⟫_ℝ + κ₁ y * W1p.value v y := by
  obtain ⟨w, hw⟩ := hv
  have hVm' : MeasurableSet (V : Set X) := V.isOpen.measurableSet
  have hsupp : ∀ j : Fin 2, Function.support (fun y => κ y j) ⊆ tsupport κ := fun j y hy =>
    subset_tsupport _ fun h0 => hy (by simp [h0])
  obtain ⟨o, ho⟩ := pde_wkp_one hVm k
  obtain ⟨g₀, hg₀⟩ := pde_bd_ext hVW k h₀ h₀c h₀s o
  obtain ⟨g₁, hg₁⟩ := pde_bd_ext hVW k h₁ h₁c h₁s (Wkp.lowerOrder k w)
  -- the drift term, one direction at a time
  have hdir : ∀ j : Fin 2, ∃ m : Wkp (volume : Measure X) W 2 k,
      ∃ d : Wkp (volume : Measure X) V 2 k,
        (Wkp.value k m : X → ℝ) =ᵐ[(volume : Measure X).restrict W]
          (fun x => κ x j * Wkp.value k d x) ∧
        (Wkp.value k d : X → ℝ) =ᵐ[(volume : Measure X).restrict V]
          fun x => W1p.gradient v x j := by
    intro j
    obtain ⟨d, hd⟩ := Wkp.exists_hasWeakLineDerivOn_value k w (EuclideanSpace.single j 1)
    have hu' := ((W1p.hasWeakFDerivOn v).mono hVΩ).hasWeakLineDerivOn
      (EuclideanSpace.single j (1 : ℝ))
    have hde := hd.ae_eq (hu'.congr_ae hw.symm)
    obtain ⟨m, hm⟩ := pde_bd_ext (κ := fun x => κ x j) hVW k
      ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp h) (hc.mono' (hsupp j))
      (fun x hx => hs ⟨hx.1, closure_minimal (hsupp j) (isClosed_tsupport _) hx.2⟩) d
    refine ⟨m, d, hm, ?_⟩
    filter_upwards [hde] with x hx
    rw [hx]
    simp [EuclideanSpace.inner_single_right]
  obtain ⟨m0, d0, hm0, hd0⟩ := hdir 0
  obtain ⟨m1, d1, hm1, hd1⟩ := hdir 1
  refine ⟨g₀ + (m0 + m1) + g₁, ?_⟩
  have hval : Wkp.value k (g₀ + (m0 + m1) + g₁) =
      Wkp.value k g₀ + (Wkp.value k m0 + Wkp.value k m1) + Wkp.value k g₁ := by
    simp only [← Wkp.valueL_apply, map_add]
  rw [hval]
  have hVae : ∀ᵐ x ∂(volume : Measure X).restrict W, x ∈ (V : Set X) →
      Wkp.value k o x = 1 ∧ Wkp.value k d0 x = W1p.gradient v x 0 ∧
        Wkp.value k d1 x = W1p.gradient v x 1 ∧
          Wkp.value k (Wkp.lowerOrder k w) x = W1p.value v x :=
    ae_restrict_of_ae ((ae_restrict_iff' hVm').1 (by
      filter_upwards [ho, hd0, hd1, hw] with x a b c d
      exact ⟨a, b, c, d⟩))
  filter_upwards [Lp.coeFn_add (Wkp.value k g₀ + (Wkp.value k m0 + Wkp.value k m1))
      (Wkp.value k g₁), Lp.coeFn_add (Wkp.value k g₀) (Wkp.value k m0 + Wkp.value k m1),
    Lp.coeFn_add (Wkp.value k m0) (Wkp.value k m1), hg₀, hg₁, hm0, hm1, hVae,
    ae_restrict_mem W.isOpen.measurableSet] with x e1 e2 e3 e4 e5 e6 e7 hV' hxW
  rw [e1, Pi.add_apply, e2, Pi.add_apply, e3, Pi.add_apply, e4, e5, e6, e7]
  by_cases hxV : x ∈ (V : Set X)
  · obtain ⟨a, b, c, d⟩ := hV' hxV
    rw [a, b, c, d]
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
    ring
  · have z0 : κ₀ x = 0 := image_eq_zero_of_notMem_tsupport fun h' => hxV (h₀s ⟨hxW, h'⟩)
    have z1 : κ₁ x = 0 := image_eq_zero_of_notMem_tsupport fun h' => hxV (h₁s ⟨hxW, h'⟩)
    have z : κ x = 0 := image_eq_zero_of_notMem_tsupport fun h' => hxV (hs ⟨hxW, h'⟩)
    simp [z0, z1, z]

open TauCeti TauCeti.PDE InnerProductSpace in
open scoped InnerProductSpace in
/-- W-PDE1 P4 helper, adapted from the private TauCeti lemma `setIntegral_value_mul_eq_neg`
(`Regularity/Interior.lean`): integration by parts against the conormal field of a cutoff `ψ`
that meets `H` only inside `Ω`, for a test function `φ` on `H`. -/
theorem pde_bd_cut_ibp {Ω H : Opens X} {a : X → Matrix (Fin 2) (Fin 2) ℝ} {K : ℝ≥0} {M : ℝ}
    (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x)) (u : W1p (volume : Measure X) Ω 2)
    {ψ : X → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : (H : Set X) ∩ tsupport ψ ⊆ Ω) (φ : TestFunction H ℝ ⊤) :
    ∫ x in Ω, W1p.value u x * (matrixBilinearForm (a x) (gradient φ x) (gradient ψ x)
        + φ x * divMatrixGradient a ψ x)
      = -∫ x in Ω, φ x * matrixBilinearForm (a x) (W1p.gradient u x) (gradient ψ x) := by
  set b := EuclideanSpace.basisFun (Fin 2) ℝ
  set h : Fin 2 → X → ℝ := fun i y => matrixBilinearForm (a y) (b i) (gradient ψ y)
  choose Lh hLh using fun i => exists_lipschitzWith_matrixBilinearForm_gradient hM hK hψ hψc (b i)
  have hhc : ∀ i, HasCompactSupport (h i) := fun i =>
    hψc.mono' ((subset_tsupport _).trans (tsupport_matrixBilinearForm_gradient_subset ψ (b i)))
  choose Ch hCh using fun i => (hLh i).continuous.bounded_above_of_compact_support (hhc i)
  obtain ⟨Lφ, hLφ⟩ := φ.contDiff.lipschitzWith_of_hasCompactSupport φ.hasCompactSupport (by simp)
  obtain ⟨Cφ, hCφ⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  set g : Fin 2 → X → ℝ := fun i y => φ y * h i y
  have hLg : ∀ i, LipschitzWith _ (g i) := fun i =>
    holderWith_one.1 ((ContinuousLinearMap.mul ℝ ℝ).holderWith_comp₂ (holderWith_one.2 hLφ)
      (holderWith_one.2 (hLh i)) (Mf := Cφ.toNNReal) (Mg := (Ch i).toNNReal)
      (fun x => (hCφ x).trans (Real.le_coe_toNNReal _))
      (fun x => (hCh i x).trans (Real.le_coe_toNNReal _)))
  have hsupp : ∀ i, Function.support (g i) ⊆ tsupport ψ := fun i x hx =>
    tsupport_matrixBilinearForm_gradient_subset (a := a) ψ (b i)
      (subset_tsupport _ fun h0 => hx (by simp only [g, h, h0, mul_zero]))
  have hsupp' : ∀ i, Function.support (g i) ⊆ tsupport φ := fun i x hx =>
    subset_tsupport _ fun h0 => hx (by simp only [g, h0, zero_mul])
  have hgc : ∀ i, HasCompactSupport (g i) := fun i => hψc.mono' (hsupp i)
  -- the only change: `φ ψ` has support in `H ∩ tsupport ψ ⊆ Ω`
  have hgs : ∀ i, tsupport (g i) ⊆ Ω := fun i x hx =>
    hts ⟨φ.tsupport_subset (closure_minimal (hsupp' i) (isClosed_tsupport _) hx),
      closure_minimal (hsupp i) (isClosed_tsupport ψ) hx⟩
  have key : ∀ i, ∫ x in Ω, lineDeriv ℝ (g i) x (b i) * W1p.value u x =
      -∫ x in Ω, g i x * ⟪W1p.gradient u x, b i⟫_ℝ := fun i =>
    W1p.setIntegral_lineDeriv_mul_value_eq_neg (by norm_num) u (hLg i) (hgc i) (hgs i) (b i)
  have hderiv : ∀ᵐ x ∂(volume : Measure X), ∀ i, lineDeriv ℝ (g i) x (b i)
      = ⟪gradient φ x, b i⟫_ℝ * h i x + φ x * lineDeriv ℝ (h i) x (b i) := by
    refine ae_all_iff.2 fun i => (hLh i).ae_differentiableAt.mono fun x hhx => ?_
    have hφx : DifferentiableAt ℝ φ x := (φ.contDiff.differentiable (by simp)) x
    have hmul : DifferentiableAt ℝ (fun y => φ y * h i y) x := hφx.mul hhx
    rw [hmul.lineDeriv_eq_fderiv, hhx.lineDeriv_eq_fderiv, fderiv_fun_mul hφx hhx,
      inner_gradient_left]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hint1 : ∀ i, Integrable (fun x => lineDeriv ℝ (g i) x (b i) * W1p.value u x)
      ((volume : Measure X).restrict Ω) := fun i => by
    have hdgc : HasCompactSupport fun x => lineDeriv ℝ (g i) x (b i) :=
      (hgc i).mono' fun x hx => by_contra fun hx' => hx (lineDeriv_of_notMem_tsupport hx' _)
    exact ((hdgc.memLp_of_bound (p := 2)
      (aestronglyMeasurable_lineDeriv (hLg i).continuous volume) _
      (.of_forall fun _ => norm_lineDeriv_le_of_lipschitz ℝ (hLg i))).restrict _).integrable_mul
        (Lp.memLp (W1p.value u))
  have hint2 : ∀ i, Integrable (fun x => g i x * ⟪W1p.gradient u x, b i⟫_ℝ)
      ((volume : Measure X).restrict Ω) := fun i =>
    (((hLg i).continuous.memLp_of_hasCompactSupport (p := 2) (hgc i)).restrict _).integrable_mul
      ((Lp.memLp (W1p.gradient u)).inner_const (b i))
  calc ∫ x in Ω, W1p.value u x * (matrixBilinearForm (a x) (gradient φ x) (gradient ψ x)
        + φ x * divMatrixGradient a ψ x)
      = ∫ x in Ω, ∑ i, lineDeriv ℝ (g i) x (b i) * W1p.value u x := by
        refine integral_congr_ae ((ae_restrict_of_ae hderiv).mono fun x hx => ?_)
        simp only [hx, divMatrixGradient_def]
        rw [← sum_inner_mul_matrixBilinearForm (A := a x)]
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, mul_add, add_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [h]
        ring
    _ = ∑ i, ∫ x in Ω, lineDeriv ℝ (g i) x (b i) * W1p.value u x :=
        integral_finsetSum _ fun i _ => hint1 i
    _ = ∑ i, -∫ x in Ω, g i x * ⟪W1p.gradient u x, b i⟫_ℝ :=
        Finset.sum_congr rfl fun i _ => key i
    _ = -∫ x in Ω, ∑ i, g i x * ⟪W1p.gradient u x, b i⟫_ℝ := by
        rw [integral_finsetSum _ fun i _ => hint2 i, Finset.sum_neg_distrib]
    _ = -∫ x in Ω, φ x * matrixBilinearForm (a x) (W1p.gradient u x) (gradient ψ x) := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        dsimp only
        rw [← sum_inner_mul_matrixBilinearForm (A := a x), Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [g, h]
        ring

open TauCeti TauCeti.PDE in
/-- W-PDE1 P4 helper, adapted from the private TauCeti lemma
`setIntegral_matrixBilinearForm_smul_add_eq` (`Regularity/Interior.lean`): the weak equation on
`Ω` tested against `ψ φ`, for a test function `φ` on `H ≥ Ω` and a cutoff `ψ` meeting `H` only
inside `Ω`. -/
theorem pde_bd_cut_test {Ω H : Opens X} (hΩH : Ω ≤ H) {a : X → Matrix (Fin 2) (Fin 2) ℝ}
    {f : Lp ℝ 2 ((volume : Measure X).restrict Ω)} {u : W1p (volume : Measure X) Ω 2}
    (hu : ∀ v : W1p0 (volume : Measure X) Ω 2,
      energyFormH1 a 0 0 u (v : W1p (volume : Measure X) Ω 2) =
        ∫ x in Ω, f x * W1p.value (v : W1p (volume : Measure X) Ω 2) x)
    {ψ : X → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : (H : Set X) ∩ tsupport ψ ⊆ Ω) (φ : TestFunction H ℝ ⊤) :
    ∫ x in Ω, matrixBilinearForm (a x) (ψ x • gradient φ x + φ x • gradient ψ x)
        (W1p.gradient u x) =
      ∫ x in Ω, ψ x * f x * φ x := by
  obtain ⟨N, hN, hψN, hgradN⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hψc
  have hψN' : ∀ x ∈ Ω, |ψ x| ≤ N := fun x _ => hψN x
  have hgradN' : ∀ x ∈ Ω, ‖gradient ψ x‖ ≤ N := fun x _ => hgradN x
  have hΩ : (Ω : Set X) ⊆ H := hΩH
  set φΩ := W1p.restrictL hΩH (W1p.ofTestFunctionₗ volume H 2 φ)
  have hφv : ∀ᵐ x ∂(volume : Measure X).restrict Ω, W1p.value φΩ x = φ x := by
    filter_upwards [W1p.value_restrictL_ae hΩH (W1p.ofTestFunctionₗ volume H 2 φ),
      ae_restrict_of_ae_restrict_of_subset hΩ
        (testFunctionLp_apply_ae (mu := (volume : Measure X)) 2 φ)]
      with x h1 h2
    rw [h1, W1p.value_ofTestFunctionₗ, h2]
  have hφg : ∀ᵐ x ∂(volume : Measure X).restrict Ω, W1p.gradient φΩ x = gradient φ x := by
    filter_upwards [W1p.gradient_restrictL_ae hΩH (W1p.ofTestFunctionₗ volume H 2 φ),
      ae_restrict_of_ae_restrict_of_subset hΩ
        (gradientTestFunctionLp_apply_ae (mu := (volume : Measure X)) 2 φ)]
      with x h1 h2
    rw [h1, W1p.gradient_ofTestFunctionₗ, h2]
  set v := W1p.contDiffSMul ψ hψ hN hψN' hgradN' φΩ
  -- the change: `ψ φ` vanishes off the compact `tsupport ψ ∩ tsupport φ ⊆ Ω`
  have hKc : IsCompact (tsupport ψ ∩ tsupport φ) :=
    IsCompact.inter_right hψc (isClosed_tsupport _)
  have hKΩ : tsupport ψ ∩ tsupport φ ⊆ Ω := fun x hx => hts ⟨φ.tsupport_subset hx.2, hx.1⟩
  have hv : v ∈ w1p0Submodule (volume : Measure X) Ω 2 := by
    refine W1p.mem_w1p0Submodule_of_isCompact (by norm_num) hKc hKΩ ?_
    filter_upwards [W1p.value_contDiffSMul_ae hψ hN hψN' hgradN' φΩ, hφv] with x h1 h2 hx
    rw [h1, h2, smul_eq_mul]
    by_cases hψx : x ∈ tsupport ψ
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx ⟨hψx, h⟩), mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hψx, zero_mul]
  have h := hu ⟨v, hv⟩
  simp only at h
  rw [energyFormH1_zero_zero_eq_setIntegral] at h
  calc _ = ∫ x in Ω, matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x) := by
        refine integral_congr_ae ?_
        filter_upwards [W1p.gradient_contDiffSMul_ae hψ hN hψN' hgradN' φΩ, hφv, hφg]
          with x h1 h2 h3
        rw [h1, h2, h3]
    _ = ∫ x in Ω, f x * W1p.value v x := h
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [W1p.value_contDiffSMul_ae hψ hN hψN' hgradN' φΩ, hφv] with x h1 h2
        rw [h1, h2, smul_eq_mul]
        ring

open TauCeti TauCeti.PDE in
/-- W-PDE1 P4 helper, adapted from the private TauCeti lemma
`setIntegral_matrixBilinearForm_cutoff_eq` (`Regularity/Interior.lean`): the localized weak
equation on `Ω`, tested against a test function on `H ≥ Ω`, for a cutoff `ψ` meeting `H` only
inside `Ω`. -/
theorem pde_bd_cut_eq {Ω H : Opens X} (hΩH : Ω ≤ H) {a : X → Matrix (Fin 2) (Fin 2) ℝ}
    {K : ℝ≥0} {M : ℝ} (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x))
    {f : Lp ℝ 2 ((volume : Measure X).restrict Ω)} {u : W1p (volume : Measure X) Ω 2}
    (hu : ∀ v : W1p0 (volume : Measure X) Ω 2,
      energyFormH1 a 0 0 u (v : W1p (volume : Measure X) Ω 2) =
        ∫ x in Ω, f x * W1p.value (v : W1p (volume : Measure X) Ω 2) x)
    {ψ : X → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : (H : Set X) ∩ tsupport ψ ⊆ Ω) (φ : TestFunction H ℝ ⊤) :
    ∫ x in Ω, matrixBilinearForm (a x) (gradient φ x)
        (ψ x • W1p.gradient u x + W1p.value u x • gradient ψ x)
      = ∫ x in Ω, localizedForcing a ψ f u x * φ x := by
  have hE1 := pde_bd_cut_test hΩH hu hψ hψc hts φ
  have hE2 := pde_bd_cut_ibp hM hK u hψ hψc hts φ
  have hBc := hK.continuous
  have hψ' := hψ.continuous
  have hφ' := φ.continuous
  have hgψ := ContDiff.continuous_gradient hψ
  have hgφ := ContDiff.continuous_gradient φ.contDiff
  have hBn : Continuous fun x => ‖matrixBilinearForm (a x)‖ :=
    Continuous.norm (E := X →L[ℝ] X →L[ℝ] ℝ) hBc
  obtain ⟨C, hC⟩ := exists_norm_divMatrixGradient_le hM hK hψ hψc
  obtain ⟨Cφ, hCφ⟩ := hφ'.bounded_above_of_compact_support φ.hasCompactSupport
  have hcs : ∀ W : X → ℝ, (∀ x, ψ x = 0 → gradient ψ x = 0 →
      divMatrixGradient a ψ x = 0 → W x = 0) → HasCompactSupport W := fun W hW =>
    hψc.mono' fun x hx => by_contra fun hxψ => hx (hW x (image_eq_zero_of_notMem_tsupport hxψ)
      (gradient_of_notMem_tsupport hxψ)
      (divMatrixGradient_eq_zero_of_notMem_tsupport hxψ))
  have hu_m := Lp.aestronglyMeasurable (W1p.value u)
  have hgu_m := Lp.aestronglyMeasurable (W1p.gradient u)
  have hint : ∀ {F W g : X → ℝ}, MemLp F 2 ((volume : Measure X).restrict Ω) →
      MemLp W 2 ((volume : Measure X).restrict Ω) →
      AEStronglyMeasurable g ((volume : Measure X).restrict Ω) →
      (∀ x, ‖g x‖ ≤ W x * F x) → Integrable g ((volume : Measure X).restrict Ω) :=
    fun hF hW hg hle => (hW.integrable_mul hF).mono' hg (Filter.Eventually.of_forall hle)
  have hcont : ∀ {W : X → ℝ}, Continuous W → HasCompactSupport W →
      MemLp W 2 ((volume : Measure X).restrict Ω) := fun hW hWc =>
    (hW.memLp_of_hasCompactSupport hWc).restrict _
  have hφD : MemLp (fun x => φ x * divMatrixGradient a ψ x) 2
      ((volume : Measure X).restrict Ω) :=
    ((hcs _ fun x _ _ h3 => by simp [h3]).memLp_of_bound
      (hφ'.measurable.mul (measurable_divMatrixGradient hBc hψ)).aestronglyMeasurable (Cφ * C)
      (Filter.Eventually.of_forall fun x => by
        simp only [Pi.mul_apply, norm_mul]
        exact mul_le_mul (hCφ x) (hC x) (norm_nonneg _) ((norm_nonneg _).trans (hCφ x)))).restrict _
  have hT1 : Integrable (fun x => matrixBilinearForm (a x) (ψ x • gradient φ x +
      φ x • gradient ψ x) (W1p.gradient u x)) ((volume : Measure X).restrict Ω) :=
    hint (Lp.memLp (W1p.gradient u)).norm
      (hcont (W := fun x => ‖matrixBilinearForm (a x)‖ *
          ‖ψ x • gradient φ x + φ x • gradient ψ x‖)
        (hBn.mul ((hψ'.smul hgφ).add (hφ'.smul hgψ)).norm)
        (hcs _ fun x h1 h2 _ => by simp [h1, h2]))
      (aestronglyMeasurable_matrixBilinearForm_apply hBc.aestronglyMeasurable
        (Continuous.aestronglyMeasurable (by fun_prop)) hgu_m)
      (fun x => (matrixBilinearForm (a x)).le_opNorm₂ _ _)
  have hT2 : Integrable (fun x => φ x * matrixBilinearForm (a x) (gradient ψ x)
      (W1p.gradient u x)) ((volume : Measure X).restrict Ω) :=
    hint (Lp.memLp (W1p.gradient u)).norm
      (hcont (W := fun x => ‖φ x‖ * (‖matrixBilinearForm (a x)‖ * ‖gradient ψ x‖))
        (hφ'.norm.mul (hBn.mul hgψ.norm)) (hcs _ fun x _ h2 _ => by simp [h2]))
      ((Continuous.aestronglyMeasurable (by fun_prop)).mul
        (aestronglyMeasurable_matrixBilinearForm_apply hBc.aestronglyMeasurable
          (Continuous.aestronglyMeasurable (by fun_prop)) hgu_m))
      (fun x => by
        rw [norm_mul, mul_assoc]
        gcongr
        exact (matrixBilinearForm (a x)).le_opNorm₂ _ _)
  have hQ : Integrable (fun x => φ x * matrixBilinearForm (a x) (W1p.gradient u x)
      (gradient ψ x)) ((volume : Measure X).restrict Ω) :=
    hint (Lp.memLp (W1p.gradient u)).norm
      (hcont (W := fun x => ‖φ x‖ * (‖matrixBilinearForm (a x)‖ * ‖gradient ψ x‖))
        (hφ'.norm.mul (hBn.mul hgψ.norm)) (hcs _ fun x _ h2 _ => by simp [h2]))
      ((Continuous.aestronglyMeasurable (by fun_prop)).mul
        (aestronglyMeasurable_matrixBilinearForm_apply hBc.aestronglyMeasurable hgu_m
          (Continuous.aestronglyMeasurable (by fun_prop))))
      (fun x => by
        rw [norm_mul, mul_assoc]
        gcongr
        exact ((matrixBilinearForm (a x)).le_opNorm₂ _ _).trans_eq (by ring))
  have hT4 : Integrable (fun x => W1p.value u x * (φ x * divMatrixGradient a ψ x))
      ((volume : Measure X).restrict Ω) :=
    (Lp.memLp (W1p.value u)).integrable_mul hφD
  have hT3 : Integrable (fun x => W1p.value u x * (matrixBilinearForm (a x) (gradient φ x)
      (gradient ψ x) + φ x * divMatrixGradient a ψ x)) ((volume : Measure X).restrict Ω) := by
    have hT3' : Integrable (fun x => W1p.value u x * matrixBilinearForm (a x) (gradient φ x)
        (gradient ψ x)) ((volume : Measure X).restrict Ω) :=
      hint (Lp.memLp (W1p.value u)).norm
        (hcont (W := fun x => ‖matrixBilinearForm (a x) (gradient φ x) (gradient ψ x)‖)
          (by fun_prop) (hcs _ fun x _ h2 _ => by simp [h2]))
        (hu_m.mul (Continuous.aestronglyMeasurable (by fun_prop)))
        (fun x => by rw [norm_mul, mul_comm])
    exact (hT3'.add hT4).congr (.of_forall fun x => by simp only [Pi.add_apply, mul_add])
  have hP : Integrable (fun x => ψ x * f x * φ x) ((volume : Measure X).restrict Ω) :=
    hint (Lp.memLp f).norm (hcont (W := fun x => ‖ψ x * φ x‖)
      (by fun_prop) (hcs _ fun x h1 _ _ => by simp [h1]))
      (((Continuous.aestronglyMeasurable (by fun_prop)).mul (Lp.aestronglyMeasurable f)).mul
        (Continuous.aestronglyMeasurable (by fun_prop)))
      (fun x => by
        simp only [norm_mul]
        exact le_of_eq (by ring))
  calc ∫ x in Ω, matrixBilinearForm (a x) (gradient φ x)
        (ψ x • W1p.gradient u x + W1p.value u x • gradient ψ x)
      = ∫ x in Ω, (matrixBilinearForm (a x) (ψ x • gradient φ x + φ x • gradient ψ x)
            (W1p.gradient u x)
          - φ x * matrixBilinearForm (a x) (gradient ψ x) (W1p.gradient u x)
          + W1p.value u x * (matrixBilinearForm (a x) (gradient φ x) (gradient ψ x)
            + φ x * divMatrixGradient a ψ x)
          - W1p.value u x * (φ x * divMatrixGradient a ψ x)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [map_add, map_smul, add_apply,
          smul_apply, smul_eq_mul]
        ring
    _ = (∫ x in Ω, ψ x * f x * φ x)
          - (∫ x in Ω, φ x * matrixBilinearForm (a x) (W1p.gradient u x) (gradient ψ x))
          - (∫ x in Ω, φ x * matrixBilinearForm (a x) (gradient ψ x) (W1p.gradient u x))
          - ∫ x in Ω, W1p.value u x * (φ x * divMatrixGradient a ψ x) := by
        rw [integral_sub ?_ hT4, integral_add ?_ hT3, integral_sub hT1 hT2, hE1, hE2]
        · ring
        · exact hT1.sub hT2
        · exact (hT1.sub hT2).add hT3
    _ = ∫ x in Ω, (ψ x * f x * φ x
          - φ x * matrixBilinearForm (a x) (W1p.gradient u x) (gradient ψ x)
          - φ x * matrixBilinearForm (a x) (gradient ψ x) (W1p.gradient u x)
          - W1p.value u x * (φ x * divMatrixGradient a ψ x)) := by
        rw [integral_sub ?_ hT4, integral_sub ?_ hT2, integral_sub hP hQ]
        · exact hP.sub hQ
        · exact (hP.sub hQ).sub hT2
    _ = ∫ x in Ω, localizedForcing a ψ f u x * φ x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [localizedForcing_def]
        ring

open TauCeti TauCeti.PDE in
/-- W-PDE1 P4 helper (the localized equation up to a flat boundary), adapted from TauCeti
`exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul` (`Regularity/Interior.lean`), whose
cutoff must have support inside `Ω`: here `Ω ≤ H` and the cutoff need only meet `H` inside `Ω`.
If `u` solves `-div(a ∇u) = f` weakly on `Ω`, then the zero extension `w` of `ψ u` satisfies
`-div(a ∇w) = localizedForcing a ψ f u` against every test function on `H`. -/
theorem pde_bd_cutoff {Ω H : Opens X} (hΩH : Ω ≤ H) {a : X → Matrix (Fin 2) (Fin 2) ℝ} {K : ℝ≥0}
    {M : ℝ} (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x))
    {f : Lp ℝ 2 ((volume : Measure X).restrict Ω)} {u : W1p (volume : Measure X) Ω 2}
    (hu : ∀ v : W1p0 (volume : Measure X) Ω 2,
      energyFormH1 a 0 0 u (v : W1p (volume : Measure X) Ω 2) =
        ∫ x in Ω, f x * W1p.value (v : W1p (volume : Measure X) Ω 2) x)
    {ψ : X → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : (H : Set X) ∩ tsupport ψ ⊆ Ω) {w : W1p (volume : Measure X) H 2}
    (hwg : W1p.gradient w =ᵐ[(volume : Measure X).restrict H] (Ω : Set X).indicator
      (fun y => ψ y • W1p.gradient u y + W1p.value u y • gradient ψ y))
    {g : X → ℝ}
    (hg : g =ᵐ[(volume : Measure X).restrict H] (Ω : Set X).indicator (localizedForcing a ψ f u))
    (φ : TestFunction H ℝ ⊤) :
    energyFormH1 a 0 0 w (W1p.ofTestFunctionₗ volume H 2 φ) = ∫ x in H, g x * φ x := by
  have hΩ := Ω.isOpen.measurableSet
  have hΩH' : (Ω : Set X) ⊆ H := hΩH
  have hφg := gradientTestFunctionLp_apply_ae (mu := (volume : Measure X)) 2 φ
  rw [energyFormH1_zero_zero_eq_setIntegral]
  have hR := setIntegral_indicator (μ := (volume : Measure X)) (s := (H : Set X))
    (f := fun x => localizedForcing a ψ f u x * φ x) hΩ
  rw [inter_eq_right.2 hΩH'] at hR
  calc ∫ x in H, matrixBilinearForm (a x)
          (W1p.gradient (W1p.ofTestFunctionₗ volume H 2 φ) x) (W1p.gradient w x)
      = ∫ x in H, (Ω : Set X).indicator (fun y => matrixBilinearForm (a y)
          (gradient φ y) (ψ y • W1p.gradient u y + W1p.value u y • gradient ψ y)) x := by
        refine integral_congr_ae ?_
        filter_upwards [hφg, hwg] with x h1 h2
        rw [W1p.gradient_ofTestFunctionₗ, h1, h2]
        by_cases hxΩ : x ∈ (Ω : Set X)
        · rw [indicator_of_mem hxΩ, indicator_of_mem hxΩ]
        · rw [indicator_of_notMem hxΩ, indicator_of_notMem hxΩ, map_zero]
    _ = ∫ x in Ω, localizedForcing a ψ f u x * φ x := by
        rw [setIntegral_indicator hΩ, inter_eq_right.2 hΩH']
        exact pde_bd_cut_eq hΩH hM hK hu hψ hψc hts φ
    _ = ∫ x in H, g x * φ x := by
        rw [← hR]
        refine integral_congr_ae ?_
        filter_upwards [hg] with x h
        rw [h]
        by_cases hxΩ : x ∈ (Ω : Set X)
        · rw [indicator_of_mem hxΩ, indicator_of_mem hxΩ]
        · rw [indicator_of_notMem hxΩ, indicator_of_notMem hxΩ, zero_mul]

open TauCeti in
/-- W-PDE1 P4 helper: transporting `H¹₀(Ω)` through a chart and cutting off near a flat boundary
piece lands in `H¹₀(H)`, provided the cut-off pull-back of every compact subset of `Ω` stays in a
compact subset of `H`. -/
theorem pde_bd_w1p0 {Ω V H : Opens X} (hVH : V ≤ H) {Φ : X → X} {L c : ℝ}
    (hd : DifferentiableOn ℝ Φ V) (hinj : InjOn Φ V) (hmaps : MapsTo Φ V Ω)
    (hL : ∀ y ∈ (V : Set X), ‖fderiv ℝ Φ y‖ ≤ L) (hc : 0 < c)
    (hdet : ∀ y ∈ (V : Set X), c ≤ |(fderiv ℝ Φ y).det|)
    {ζ : X → ℝ} (hζ : ContDiff ℝ ∞ ζ) {M : ℝ} (hM : 0 ≤ M) (hζM : ∀ x ∈ V, |ζ x| ≤ M)
    (hgM : ∀ x ∈ V, ‖gradient ζ x‖ ≤ M) (hs : (H : Set X) ∩ tsupport ζ ⊆ V)
    (hK : ∀ C : Set X, IsCompact C → C ⊆ Ω →
      ∃ K : Set X, IsCompact K ∧ K ⊆ H ∧ ∀ y ∈ (V : Set X), ζ y ≠ 0 → Φ y ∈ C → y ∈ K)
    {u : W1p (volume : Measure X) Ω 2} (hu : u ∈ w1p0Submodule (volume : Measure X) Ω 2) :
    W1p.localizeL hVH ζ hζ hM hζM hgM hs
        (W1p.compL Φ (p := 2) (by norm_num) hd hinj hmaps hL hc hdet u) ∈
      w1p0Submodule (volume : Measure X) H 2 := by
  let T : W1p (volume : Measure X) Ω 2 →L[ℝ] W1p (volume : Measure X) H 2 :=
    (W1p.localizeL hVH ζ hζ hM hζM hgM hs).comp
      (W1p.compL Φ (p := 2) (by norm_num) hd hinj hmaps hL hc hdet)
  change T u ∈ _
  refine w1p0Submodule_subset_of_isClosed
    ((w1p0Submodule (volume : Measure X) H 2).isClosed.preimage T.continuous) (fun φ => ?_) hu
  obtain ⟨K, hK, hKH, hKy⟩ := hK (tsupport φ) φ.hasCompactSupport φ.tsupport_subset
  refine W1p.mem_w1p0Submodule_of_isCompact (by norm_num) hK hKH ?_
  have hcv := W1p.value_compL_ae Φ (p := 2) (by norm_num) hd hinj hmaps hL hc hdet
    (W1p.ofTestFunctionₗ volume Ω 2 φ)
  have hlv := W1p.value_localizeL_ae hVH hζ hM hζM hgM hs
    (W1p.compL Φ (p := 2) (by norm_num) hd hinj hmaps hL hc hdet
      (W1p.ofTestFunctionₗ volume Ω 2 φ))
  -- `Φ` pulls null sets of `Ω` back to null sets of `V`
  have htr : ∀ᵐ y ∂(volume : Measure X).restrict V,
      W1p.value (W1p.ofTestFunctionₗ volume Ω 2 φ) (Φ y) = φ (Φ y) :=
    ae_comp_of_map_absolutelyContinuous (hd.continuousOn.aemeasurable V.isOpen.measurableSet)
      (Measure.absolutelyContinuous_of_le_smul
        (map_restrict_le_smul_restrict_of_differentiableOn volume V.isOpen hd hinj hmaps hc hdet))
      (W1p.value_ofTestFunctionₗ_ae φ)
  have hVae : ∀ᵐ y ∂(volume : Measure X).restrict H, y ∈ (V : Set X) →
      W1p.value (W1p.compL Φ (p := 2) (by norm_num) hd hinj hmaps hL hc hdet
        (W1p.ofTestFunctionₗ volume Ω 2 φ)) y = φ (Φ y) :=
    ae_restrict_of_ae ((ae_restrict_iff' V.isOpen.measurableSet).1 (by
      filter_upwards [hcv, htr] with y a b
      rw [a, b]))
  filter_upwards [hlv, hVae] with y h1 h2 hyK
  change W1p.value (W1p.localizeL hVH ζ hζ hM hζM hgM hs
    (W1p.compL Φ (p := 2) (by norm_num) hd hinj hmaps hL hc hdet
      (W1p.ofTestFunctionₗ volume Ω 2 φ))) y = 0
  rw [h1]
  by_cases hyV : y ∈ (V : Set X)
  · rw [indicator_of_mem hyV, h2 hyV]
    by_cases hζy : ζ y = 0
    · rw [hζy, zero_smul]
    · rw [image_eq_zero_of_notMem_tsupport fun h => hyK (hKy y hyV hζy h), smul_zero]
  · rw [indicator_of_notMem hyV]

/-- W-PDE1 P4 helper (chart at a boundary point): a flattening chart inside `U`, with a closed
disc of radius `2ρ` in its target. -/
theorem pde_bd_chart {Ω U : Opens X} (hΩU : closure (Ω : Set X) ⊆ U) {ψ : X → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hΩψ : (Ω : Set X) = {x | ψ x < 0})
    (hψ0 : ∀ x, ψ x = 0 → fderiv ℝ ψ x ≠ 0) {x₀ : X} (hx₀ : x₀ ∈ frontier (Ω : Set X)) :
    ∃ (e : OpenPartialHomeomorph X X) (ρ : ℝ), 0 < ρ ∧ x₀ ∈ e.source ∧ e x₀ = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧ e.source ⊆ U ∧
      closedBall 0 (2 * ρ) ⊆ e.target ∧ ∀ x ∈ e.source, x ∈ (Ω : Set X) ↔ 0 < (e x) 1 := by
  have hx₀c : x₀ ∈ closure (Ω : Set X) := frontier_subset_closure hx₀
  have hψx₀ : ψ x₀ = 0 := by
    have h1 : closure (Ω : Set X) ⊆ {x | ψ x ≤ 0} :=
      closure_minimal (by rw [hΩψ]; exact fun x (hx : ψ x < 0) => (le_of_lt hx : ψ x ≤ 0))
        (isClosed_le hψ.continuous continuous_const)
    have h2 : ¬ ψ x₀ < 0 := fun h => hx₀.2 (by rw [Ω.isOpen.interior_eq, hΩψ]; exact h)
    have h3 : ψ x₀ ≤ 0 := h1 hx₀c
    linarith [not_lt.1 h2]
  obtain ⟨e₁, hx₁, he₁0, he₁, he₁s, he₁ψ⟩ := pde_flat_chart hψ hψx₀ (hψ0 x₀ hψx₀)
  set e := e₁.restrOpen U U.isOpen with he_def
  have htgt : e.target ⊆ e₁.target := fun y hy => hy.1
  have hx₀e : x₀ ∈ e.source := ⟨hx₁, hΩU hx₀c⟩
  have h0t : (0 : X) ∈ e.target := by
    have h := e.map_source hx₀e
    rwa [show e x₀ = 0 from he₁0] at h
  obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.1 e.open_target 0 h0t
  refine ⟨e, r / 4, by positivity, hx₀e, he₁0, he₁.mono inter_subset_left, he₁s.mono htgt,
    inter_subset_right, (closedBall_subset_ball (by linarith)).trans hrt, fun x hx => ?_⟩
  rw [hΩψ]
  show ψ x < 0 ↔ 0 < (e₁ x) 1
  rw [he₁ψ x hx.1]
  constructor <;> intro h <;> linarith

/-- W-PDE1 P4 helper: the derivatives of a smooth chart and of its inverse are mutually inverse. -/
theorem pde_bd_inv {e : OpenPartialHomeomorph X X} (he : ContDiffOn ℝ ∞ e e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target) {y : X} (hy : y ∈ e.target) :
    (fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y) = ContinuousLinearMap.id ℝ X ∧
      (fderiv ℝ e.symm y).comp (fderiv ℝ e (e.symm y)) = ContinuousLinearMap.id ℝ X := by
  have hx : e.symm y ∈ e.source := e.map_target hy
  have hdx : DifferentiableAt ℝ e (e.symm y) :=
    (he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)
  have hdy : DifferentiableAt ℝ e.symm y :=
    (hes.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)
  constructor
  · have h1 : HasFDerivAt (e ∘ e.symm) ((fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y)) y :=
      hdx.hasFDerivAt.comp y hdy.hasFDerivAt
    have h2 : HasFDerivAt (e ∘ e.symm) (ContinuousLinearMap.id ℝ X) y :=
      (hasFDerivAt_id y).congr_of_eventuallyEq
        (Filter.mem_of_superset (e.open_target.mem_nhds hy) fun z hz => e.right_inv hz)
    exact h1.unique h2
  · have hg : HasFDerivAt e.symm (fderiv ℝ e.symm y) (e (e.symm y)) := by
      rw [e.right_inv hy]
      exact hdy.hasFDerivAt
    have h1 : HasFDerivAt (e.symm ∘ e) ((fderiv ℝ e.symm y).comp (fderiv ℝ e (e.symm y)))
        (e.symm y) := hg.comp (e.symm y) hdx.hasFDerivAt
    have h2 : HasFDerivAt (e.symm ∘ e) (ContinuousLinearMap.id ℝ X) (e.symm y) :=
      (hasFDerivAt_id (e.symm y)).congr_of_eventuallyEq
        (Filter.mem_of_superset (e.open_source.mem_nhds hx) fun z hz => e.left_inv hz)
    exact h1.unique h2

/-- W-PDE1 P4 helper: the determinant of a linear endomorphism of `ℝ²` in coordinates. -/
theorem pde_bd_det2 (f : X →L[ℝ] X) :
    f.det = f (𝐞 0) 0 * f (𝐞 1) 1 - f (𝐞 1) 0 * f (𝐞 0) 1 := by
  rw [ContinuousLinearMap.det,
    ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply]

/-- W-PDE1 P4 helper: the inverse of a smooth chart has invertible derivative on the target. -/
theorem pde_bd_detne {e : OpenPartialHomeomorph X X} (he : ContDiffOn ℝ ∞ e e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target) {y : X} (hy : y ∈ e.target) :
    (fderiv ℝ e.symm y).det ≠ 0 := by
  intro h0
  have h := congrArg ContinuousLinearMap.det (pde_bd_inv he hes hy).1
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id] at h h0
  have h2 : LinearMap.det ((fderiv ℝ e (e.symm y) : X →ₗ[ℝ] X) ∘ₗ
      (fderiv ℝ e.symm y : X →ₗ[ℝ] X)) = 1 := h
  rw [LinearMap.det_comp, h0, mul_zero] at h2
  exact zero_ne_one h2

/-- W-PDE1 P4 helper: the Jacobian `|det D(e⁻¹)|` and `De ∘ e⁻¹` are smooth on the target. -/
theorem pde_bd_smooth {e : OpenPartialHomeomorph X X} (he : ContDiffOn ℝ ∞ e e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (fun y => |(fderiv ℝ e.symm y).det|) e.target ∧
      ContDiffOn ℝ ∞ (fun y => fderiv ℝ e (e.symm y)) e.target := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ e.symm) e.target :=
    hes.fderiv_of_isOpen e.open_target (by simp)
  have hc : ∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun y => fderiv ℝ e.symm y (𝐞 j) i) e.target :=
    fun i j => (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn
      (hD.clm_apply contDiffOn_const)
  have hf : ContDiffOn ℝ ∞ (fun y => (fderiv ℝ e.symm y).det) e.target := by
    simp_rw [pde_bd_det2]
    exact ((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))
  refine ⟨fun y hy => (((hf y hy).contDiffAt (e.open_target.mem_nhds hy)).abs
    (pde_bd_detne he hes hy)).contDiffWithinAt, ?_⟩
  exact (he.fderiv_of_isOpen e.open_source (by simp)).comp hes fun y hy => e.map_target hy

/-- W-PDE1 P4 helper: on a compact subset of the target, `D(e⁻¹)` is bounded and its determinant
is bounded away from `0`. -/
theorem pde_bd_jbounds {e : OpenPartialHomeomorph X X} (he : ContDiffOn ℝ ∞ e e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target) {C : Set X} (hC : IsCompact C)
    (hCt : C ⊆ e.target) :
    ∃ L c : ℝ, 0 < c ∧ ∀ y ∈ C, ‖fderiv ℝ e.symm y‖ ≤ L ∧ c ≤ |(fderiv ℝ e.symm y).det| := by
  obtain ⟨L, hL⟩ := hC.exists_bound_of_continuousOn
    ((hes.continuousOn_fderiv_of_isOpen e.open_target (by simp)).mono hCt)
  have hJ := (pde_bd_smooth he hes).1.continuousOn.mono hCt
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn
    (hJ.inv₀ fun y hy => abs_ne_zero.2 (pde_bd_detne he hes (hCt hy)))
  refine ⟨L, (max B 1)⁻¹, by positivity, fun y hy => ⟨hL y hy, ?_⟩⟩
  have hpos : 0 < |(fderiv ℝ e.symm y).det| := abs_pos.2 (pde_bd_detne he hes (hCt hy))
  have h1 : ‖|(fderiv ℝ e.symm y).det|⁻¹‖ ≤ B := hB y hy
  rw [norm_inv, Real.norm_eq_abs, abs_abs] at h1
  rw [inv_le_comm₀ (by positivity) hpos]
  exact h1.trans (le_max_left _ _)

open TauCeti.PDE in
/-- W-PDE1 P4 helper: the transformed coefficient matrix `J T A Tᵀ` represents the bilinear form
`J ⟨A T* ·, T* ·⟩`. -/
theorem pde_bd_mbf (T : X →L[ℝ] X) (J : ℝ) (B N : Matrix (Fin 2) (Fin 2) ℝ)
    (hN : ∀ i j, N i j = J * ∑ k, ∑ l, T (𝐞 k) i * B k l * T (𝐞 l) j) (a b : X) :
    matrixBilinearForm N a b =
      J * matrixBilinearForm B ((ContinuousLinearMap.adjoint T) a)
        ((ContinuousLinearMap.adjoint T) b) := by
  have hc : ∀ (z : X) (k : Fin 2), (ContinuousLinearMap.adjoint T z) k =
      z 0 * T (𝐞 k) 0 + z 1 * T (𝐞 k) 1 := fun z k => by
    have h := ContinuousLinearMap.adjoint_inner_left T (𝐞 k) z
    simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right, one_mul,
      conj_trivial] at h
    rw [h]
    simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]
  rw [matrixBilinearForm_apply, matrixBilinearForm_apply]
  simp only [dotProduct, mulVec, Fin.sum_univ_two, hc, hN]
  ring

open TauCeti.PDE in
/-- W-PDE1 P4 helper: the transformed coefficients are uniformly elliptic and bounded on every
compact subset of the target of the chart. -/
theorem pde_bd_tell {U : Opens X} {A : X → Matrix (Fin 2) (Fin 2) ℝ} {lam Lam : ℝ}
    (hell : UniformlyEllipticOn (U : Set X) A lam Lam) {e : OpenPartialHomeomorph X X}
    (he : ContDiffOn ℝ ∞ e e.source) (hes : ContDiffOn ℝ ∞ e.symm e.target)
    (heU : e.source ⊆ U) {C : Set X} (hC : IsCompact C) (hCt : C ⊆ e.target)
    {At : X → Matrix (Fin 2) (Fin 2) ℝ}
    (hAt : ∀ y ∈ C, ∀ i j, At y i j = |(fderiv ℝ e.symm y).det| *
      ∑ k, ∑ l, fderiv ℝ e (e.symm y) (𝐞 k) i * A (e.symm y) k l * fderiv ℝ e (e.symm y) (𝐞 l) j) :
    ∃ l L : ℝ, 0 < l ∧ ∀ y ∈ C, (∀ ξ : X, l * ‖ξ‖ ^ 2 ≤ matrixBilinearForm (At y) ξ ξ) ∧
      ∀ η ξ : X, |matrixBilinearForm (At y) η ξ| ≤ L * ‖η‖ * ‖ξ‖ := by
  obtain ⟨L₁, c, hc, hb⟩ := pde_bd_jbounds he hes hC hCt
  obtain ⟨Jm, hJm⟩ := hC.exists_bound_of_continuousOn
    ((pde_bd_smooth he hes).1.continuousOn.mono hCt)
  obtain ⟨Tm, hTm⟩ := hC.exists_bound_of_continuousOn
    ((pde_bd_smooth he hes).2.continuousOn.mono hCt)
  have hlam := hell.pos
  set M₁ := max L₁ 1 with hM₁_def
  have hM₁ : 0 < M₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨c * lam / M₁ ^ 2, (Jm * Lam) * Tm ^ 2, by positivity, fun y hy => ?_⟩
  set T := fderiv ℝ e (e.symm y) with hT_def
  set J := |(fderiv ℝ e.symm y).det| with hJ_def
  have hx : e.symm y ∈ (U : Set X) := heU (e.map_target (hCt hy))
  have hrep := pde_bd_mbf T J (A (e.symm y)) (At y) (hAt y hy)
  have hJ0 : 0 ≤ J := abs_nonneg _
  have hJm' : J ≤ Jm := by simpa [Real.norm_eq_abs, J] using hJm y hy
  have hTm' : ‖T‖ ≤ Tm := hTm y hy
  have hJm0 : 0 ≤ Jm := hJ0.trans hJm'
  have hTm0 : 0 ≤ Tm := (norm_nonneg _).trans hTm'
  constructor
  · intro ξ
    rw [hrep]
    have h1 : lam * ‖ContinuousLinearMap.adjoint T ξ‖ ^ 2 ≤ matrixBilinearForm (A (e.symm y))
        (ContinuousLinearMap.adjoint T ξ) (ContinuousLinearMap.adjoint T ξ) := by
      have h := hell.lower_bound hx (ContinuousLinearMap.adjoint T ξ)
      rwa [Matrix.toQuadraticForm'_apply, ← matrixBilinearForm_apply] at h
    have hinv : ContinuousLinearMap.adjoint (fderiv ℝ e.symm y)
        (ContinuousLinearMap.adjoint T ξ) = ξ :=
      ext_inner_right ℝ fun z => by
        rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
          ← ContinuousLinearMap.comp_apply, (pde_bd_inv he hes (hCt hy)).1,
          ContinuousLinearMap.id_apply]
    have h2 : ‖ξ‖ ≤ M₁ * ‖ContinuousLinearMap.adjoint T ξ‖ := by
      calc ‖ξ‖ = ‖ContinuousLinearMap.adjoint (fderiv ℝ e.symm y)
            (ContinuousLinearMap.adjoint T ξ)‖ := by rw [hinv]
        _ ≤ ‖ContinuousLinearMap.adjoint (fderiv ℝ e.symm y)‖ *
            ‖ContinuousLinearMap.adjoint T ξ‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ M₁ * ‖ContinuousLinearMap.adjoint T ξ‖ := by
          rw [LinearIsometryEquiv.norm_map]
          gcongr
          exact (hb y hy).1.trans (le_max_left _ _)
    have h3 : ‖ξ‖ ^ 2 ≤ M₁ ^ 2 * ‖ContinuousLinearMap.adjoint T ξ‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) h2 2
    have hcJ : c ≤ J := (hb y hy).2
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have p1 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ c * lam)
    have p2 := mul_le_mul_of_nonneg_right hcJ
      (by positivity : (0 : ℝ) ≤ lam * ‖ContinuousLinearMap.adjoint T ξ‖ ^ 2 * M₁ ^ 2)
    have p3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ J * M₁ ^ 2)
    nlinarith
  · intro η ξ
    rw [hrep, abs_mul, abs_of_nonneg hJ0]
    have h1 : |matrixBilinearForm (A (e.symm y)) (ContinuousLinearMap.adjoint T η)
        (ContinuousLinearMap.adjoint T ξ)| ≤
          Lam * ‖ContinuousLinearMap.adjoint T η‖ * ‖ContinuousLinearMap.adjoint T ξ‖ := by
      rw [matrixBilinearForm_apply]
      exact hell.upper_bound hx _ _
    have hadj : ∀ z : X, ‖ContinuousLinearMap.adjoint T z‖ ≤ Tm * ‖z‖ := fun z =>
      (ContinuousLinearMap.le_opNorm _ _).trans (by rw [LinearIsometryEquiv.norm_map]; gcongr)
    have hLam0 : 0 ≤ Lam := hlam.le.trans hell.le
    calc J * |matrixBilinearForm (A (e.symm y)) (ContinuousLinearMap.adjoint T η)
          (ContinuousLinearMap.adjoint T ξ)| ≤
        Jm * (Lam * ‖ContinuousLinearMap.adjoint T η‖ * ‖ContinuousLinearMap.adjoint T ξ‖) :=
          mul_le_mul hJm' h1 (abs_nonneg _) hJm0
      _ ≤ Jm * (Lam * (Tm * ‖η‖) * (Tm * ‖ξ‖)) := by
          gcongr
          · exact hadj η
          · exact hadj ξ
      _ = (Jm * Lam) * Tm ^ 2 * ‖η‖ * ‖ξ‖ := by ring

open TauCeti.PDE in
/-- W-PDE1 P4 helper: blending elliptic coefficients with the identity by a cutoff `0 ≤ χ ≤ 1`
keeps uniform ellipticity. -/
theorem pde_bd_ell {At : X → Matrix (Fin 2) (Fin 2) ℝ} {χ : X → ℝ} {C : Set X} {l L : ℝ}
    (hl : 0 < l) (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) (hχC : ∀ x, χ x ≠ 0 → x ∈ C)
    (hAt : ∀ y ∈ C, (∀ ξ : X, l * ‖ξ‖ ^ 2 ≤ matrixBilinearForm (At y) ξ ξ) ∧
      ∀ η ξ : X, |matrixBilinearForm (At y) η ξ| ≤ L * ‖η‖ * ‖ξ‖) (S : Set X) :
    UniformlyEllipticOn S (fun y => χ y • At y + (1 - χ y) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (min l 1) (max L 1) := by
  have hq : ∀ (y η ξ : X), η ⬝ᵥ ((χ y • At y + (1 - χ y) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ ξ)
      = χ y * matrixBilinearForm (At y) η ξ + (1 - χ y) * inner ℝ η ξ := by
    intro y η ξ
    rw [matrixBilinearForm_apply, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec,
      dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    congr 2
    simp [dotProduct, PiLp.inner_apply, Fin.sum_univ_two, mul_comm]
  refine UniformlyEllipticOn.of_bounds (lt_min hl one_pos)
    ((min_le_right _ _).trans (le_max_right _ _)) (fun x _ ξ => ?_) (fun x _ η ξ => ?_)
  · rw [Matrix.toQuadraticForm'_apply, hq, real_inner_self_eq_norm_sq]
    have h2 := mul_nonneg (mul_nonneg (sub_nonneg.2 (hχ1 x)) (sq_nonneg ‖ξ‖))
      (sub_nonneg.2 (min_le_right l 1))
    by_cases h0 : χ x = 0
    · rw [h0]
      nlinarith
    · have h1 := mul_le_mul_of_nonneg_left ((hAt x (hχC x h0)).1 ξ) (hχ0 x)
      have h3 := mul_nonneg (mul_nonneg (hχ0 x) (sq_nonneg ‖ξ‖)) (sub_nonneg.2 (min_le_left l 1))
      nlinarith
  · rw [hq]
    have hn := abs_real_inner_le_norm η ξ
    have hN : 0 ≤ ‖η‖ * ‖ξ‖ := by positivity
    have hχ' := sub_nonneg.2 (hχ1 x)
    have h4 := mul_le_mul_of_nonneg_right (le_max_right L 1) (mul_nonneg hχ' hN)
    have h5 := mul_le_mul_of_nonneg_left hn hχ'
    have h6 : |χ x * matrixBilinearForm (At x) η ξ + (1 - χ x) * inner ℝ η ξ| ≤
        χ x * |matrixBilinearForm (At x) η ξ| + (1 - χ x) * |inner ℝ η ξ| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (hχ0 x), abs_of_nonneg hχ']
    by_cases h0 : χ x = 0
    · rw [h0] at h6 h4 h5 ⊢
      nlinarith
    · have h1 := mul_le_mul_of_nonneg_left ((hAt x (hχC x h0)).2 η ξ) (hχ0 x)
      have h7 := mul_le_mul_of_nonneg_right (le_max_left L 1) (mul_nonneg (hχ0 x) hN)
      nlinarith

open TauCeti TauCeti.PDE in
/-- W-PDE1 P4 helper: `div(a ∇ζ)` is smooth with support in that of `ζ`, for smooth `a`, `ζ`. -/
theorem pde_bd_div {a : X → Matrix (Fin 2) (Fin 2) ℝ} (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    {ζ : X → ℝ} (hζ : ContDiff ℝ ∞ ζ) :
    ContDiff ℝ ∞ (divMatrixGradient a ζ) ∧ tsupport (divMatrixGradient a ζ) ⊆ tsupport ζ := by
  have hgr : ∀ y (j : Fin 2), gradient ζ y j = fderiv ℝ ζ y (𝐞 j) := fun y j => by
    have h : inner ℝ (gradient ζ y) (𝐞 j) = gradient ζ y j := by
      rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right]
      simp only [one_mul, conj_trivial]
    rw [← h, gradient, InnerProductSpace.toDual_symm_apply]
  have hg : ∀ i : Fin 2,
      ContDiff ℝ ∞ (fun y => matrixBilinearForm (a y) (𝐞 i) (gradient ζ y)) := by
    intro i
    have h : (fun y => matrixBilinearForm (a y) (𝐞 i) (gradient ζ y)) =
        fun y => a y i 0 * fderiv ℝ ζ y (𝐞 0) + a y i 1 * fderiv ℝ ζ y (𝐞 1) := by
      funext y
      rw [matrixBilinearForm_apply]
      fin_cases i <;> simp [dotProduct, mulVec, Fin.sum_univ_two, hgr]
    have hd : ∀ j : Fin 2, ContDiff ℝ ∞ (fun y => fderiv ℝ ζ y (𝐞 j)) := fun j =>
      (hζ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    rw [h]
    exact ((ha i 0).mul (hd 0)).add ((ha i 1).mul (hd 1))
  have heq : divMatrixGradient a ζ =
      fun x => ∑ i : Fin 2, fderiv ℝ (fun y => matrixBilinearForm (a y) (𝐞 i) (gradient ζ y)) x
        (𝐞 i) := by
    funext x
    rw [divMatrixGradient_def]
    exact Finset.sum_congr rfl fun i _ =>
      ((hg i).differentiable (by simp) x).lineDeriv_eq_fderiv
  refine ⟨?_, closure_minimal (fun x hx => by_contra fun h =>
    hx (divMatrixGradient_eq_zero_of_notMem_tsupport h)) (isClosed_tsupport ζ)⟩
  rw [heq]
  exact ContDiff.sum fun i _ => ((hg i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

open TauCeti in
/-- W-PDE1 P4 helper (change of variables through a chart): an integral over `Ω` of a function
vanishing on `Ω` off `e⁻¹(V)` is the integral over `V` of its pull-back times `|det D(e⁻¹)|`. -/
theorem pde_bd_cov {Ω V : Opens X} {e : OpenPartialHomeomorph X X}
    (hes : ContDiffOn ℝ ∞ e.symm e.target) (hVt : (V : Set X) ⊆ e.target)
    (hVΩ : e.symm '' (V : Set X) ⊆ Ω) {g : X → ℝ}
    (hg : ∀ x ∈ (Ω : Set X), x ∉ e.symm '' (V : Set X) → g x = 0) :
    ∫ x in Ω, g x = ∫ y in V, |(fderiv ℝ e.symm y).det| * g (e.symm y) := by
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Ω.isOpen.measurableSet hVΩ
    (fun x hx => hg x hx.1 hx.2),
    integral_image_eq_integral_abs_det_fderiv_smul volume V.isOpen.measurableSet
      (fun y hy => ((hes.contDiffAt (e.open_target.mem_nhds (hVt hy))).differentiableAt
        (by simp)).hasFDerivAt.hasFDerivWithinAt) (e.symm.injOn.mono hVt)]
  simp only [smul_eq_mul]

/-- W-PDE1 P4 helper (pulling a test function back through a chart): `φ ∘ e`, extended by zero,
is a test function on `Ω`; along `e⁻¹(V)` it equals `φ` with gradient `(De)* ∇φ`, and it vanishes
with its gradient off `e⁻¹(V)`. -/
theorem pde_bd_pull {Ω V : Opens X} {e : OpenPartialHomeomorph X X}
    (he : ContDiffOn ℝ ∞ e e.source) (hes : ContDiffOn ℝ ∞ e.symm e.target)
    (hVt : (V : Set X) ⊆ e.target) (hVΩ : e.symm '' (V : Set X) ⊆ Ω) (φ : TestFunction V ℝ ⊤) :
    ∃ ψ : TestFunction Ω ℝ ⊤, (∀ y ∈ (V : Set X), ψ (e.symm y) = φ y ∧
      gradient ψ (e.symm y) =
        ContinuousLinearMap.adjoint (fderiv ℝ e (e.symm y)) (gradient φ y)) ∧
      ∀ x ∉ e.symm '' (V : Set X), ψ x = 0 ∧ gradient ψ x = 0 := by
  have hφV : tsupport φ ⊆ (V : Set X) := φ.tsupport_subset
  have hKc : IsCompact (e.symm '' tsupport φ) := φ.hasCompactSupport.isCompact.image_of_continuousOn
    (hes.continuousOn.mono (hφV.trans hVt))
  have hKV : e.symm '' tsupport φ ⊆ e.symm '' (V : Set X) := image_mono hφV
  have hKs : e.symm '' tsupport φ ⊆ e.source := by
    rintro x ⟨y, hy, rfl⟩
    exact e.map_target (hVt (hφV hy))
  let f : X → ℝ := e.source.indicator (fun x => φ (e x))
  have hf0 : ∀ x ∉ e.symm '' tsupport φ, f x = 0 := by
    intro x hx
    by_cases hxs : x ∈ e.source
    · show e.source.indicator (fun x => φ (e x)) x = 0
      rw [indicator_of_mem hxs]
      exact image_eq_zero_of_notMem_tsupport fun h => hx ⟨e x, h, e.left_inv hxs⟩
    · show e.source.indicator (fun x => φ (e x)) x = 0
      rw [indicator_of_notMem hxs]
  have hfK : ∀ x ∉ e.symm '' tsupport φ, f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := fun x hx =>
    Filter.mem_of_superset (hKc.isClosed.isOpen_compl.mem_nhds hx) fun z hz => hf0 z hz
  have hfe : ∀ x ∈ e.source, f =ᶠ[𝓝 x] fun z => φ (e z) := fun x hx =>
    Filter.mem_of_superset (e.open_source.mem_nhds hx) fun z hz => by
      show e.source.indicator (fun x => φ (e x)) z = φ (e z)
      rw [indicator_of_mem hz]
  have hcd : ContDiff ℝ ∞ f := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ e.source
    · exact ((φ.contDiff.contDiffAt).comp x
        (he.contDiffAt (e.open_source.mem_nhds hx))).congr_of_eventuallyEq (hfe x hx)
    · exact contDiffAt_const.congr_of_eventuallyEq (hfK x fun h => hx (hKs h))
  refine ⟨⟨f, hcd, HasCompactSupport.intro hKc hf0,
    (closure_minimal (fun x (hx : x ∈ Function.support f) => by_contra fun h =>
      Function.mem_support.1 hx (hf0 x h)) hKc.isClosed).trans
      (hKV.trans hVΩ)⟩, fun y hy => ?_, fun x hx => ?_⟩
  · have hx : e.symm y ∈ e.source := e.map_target (hVt hy)
    have hey : e (e.symm y) = y := e.right_inv (hVt hy)
    refine ⟨show f (e.symm y) = φ y by rw [(hfe _ hx).eq_of_nhds, hey], ?_⟩
    have hde : DifferentiableAt ℝ e (e.symm y) :=
      (he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)
    have hdφ : DifferentiableAt ℝ φ (e (e.symm y)) := φ.contDiff.differentiable (by simp) _
    have hd : fderiv ℝ f (e.symm y) = (fderiv ℝ φ y).comp (fderiv ℝ e (e.symm y)) := by
      rw [(hfe _ hx).fderiv_eq, show (fun z => φ (e z)) = ⇑φ ∘ ⇑e from rfl,
        fderiv_comp _ hdφ hde, hey]
    show gradient f (e.symm y) = _
    refine ext_inner_right ℝ fun z => ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp only [gradient, InnerProductSpace.toDual_symm_apply, hd, ContinuousLinearMap.comp_apply]
  · have hxK : x ∉ e.symm '' tsupport φ := fun h => hx (hKV h)
    refine ⟨hf0 x hxK, ?_⟩
    show gradient f x = 0
    rw [gradient, (hfK x hxK).fderiv_eq, fderiv_const_apply, map_zero]

open TauCeti TauCeti.PDE in
/-- W-PDE1 P4 helper (transport of the energy form through a chart). -/
theorem pde_bd_trL {Ω V : Opens X} {A At : X → Matrix (Fin 2) (Fin 2) ℝ}
    {e : OpenPartialHomeomorph X X} (he : ContDiffOn ℝ ∞ e e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target) (hVt : (V : Set X) ⊆ e.target)
    (hVΩ : e.symm '' (V : Set X) ⊆ Ω) {u : W1p (volume : Measure X) Ω 2}
    {v : W1p (volume : Measure X) V 2}
    (hvg : W1p.gradient v =ᵐ[(volume : Measure X).restrict V]
      fun y => ContinuousLinearMap.adjoint (fderiv ℝ e.symm y) (W1p.gradient u (e.symm y)))
    (hAt : ∀ y ∈ (V : Set X), ∀ i j, At y i j = |(fderiv ℝ e.symm y).det| *
      ∑ k, ∑ l, fderiv ℝ e (e.symm y) (𝐞 k) i * A (e.symm y) k l * fderiv ℝ e (e.symm y) (𝐞 l) j)
    (φ : TestFunction V ℝ ⊤) (ψ : TestFunction Ω ℝ ⊤)
    (hψ : ∀ y ∈ (V : Set X), gradient ψ (e.symm y) =
      ContinuousLinearMap.adjoint (fderiv ℝ e (e.symm y)) (gradient φ y))
    (hψ0 : ∀ x ∉ e.symm '' (V : Set X), gradient ψ x = 0) :
    energyFormH1 At 0 0 v (W1p.ofTestFunctionₗ volume V 2 φ) =
      energyFormH1 A 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 ψ) := by
  have hφg := gradientTestFunctionLp_apply_ae (mu := (volume : Measure X)) 2 φ
  have hψg := gradientTestFunctionLp_apply_ae (mu := (volume : Measure X)) 2 ψ
  rw [energyFormH1_zero_zero_eq_setIntegral, energyFormH1_zero_zero_eq_setIntegral]
  have h1 : ∫ x in Ω, matrixBilinearForm (A x)
      (W1p.gradient (W1p.ofTestFunctionₗ volume Ω 2 ψ) x) (W1p.gradient u x) =
      ∫ x in Ω, matrixBilinearForm (A x) (gradient ψ x) (W1p.gradient u x) :=
    integral_congr_ae (by
      filter_upwards [hψg] with x h
      rw [W1p.gradient_ofTestFunctionₗ, h])
  rw [h1]
  refine Eq.trans ?_ (pde_bd_cov hes hVt hVΩ ?_).symm
  · refine integral_congr_ae ?_
    filter_upwards [hφg, hvg, ae_restrict_mem V.isOpen.measurableSet] with y h1 h2 hy
    have hinv : ∀ g : X, ContinuousLinearMap.adjoint (fderiv ℝ e (e.symm y))
        (ContinuousLinearMap.adjoint (fderiv ℝ e.symm y) g) = g := fun g =>
      ext_inner_right ℝ fun z => by
        rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
          ← ContinuousLinearMap.comp_apply, (pde_bd_inv he hes (hVt hy)).2,
          ContinuousLinearMap.id_apply]
    beta_reduce
    rw [W1p.gradient_ofTestFunctionₗ, h1, h2, pde_bd_mbf _ _ _ _ (hAt y hy), hψ y hy, hinv]
  · intro x _ hx
    beta_reduce
    rw [hψ0 x hx]
    simp

open TauCeti TauCeti.PDE in
open scoped InnerProductSpace in
/-- W-PDE1 P4 helper (transport of the right-hand side through a chart). -/
theorem pde_bd_trR {Ω V : Opens X} {β : X → X} {γ F : X → ℝ}
    {e : OpenPartialHomeomorph X X} (he : ContDiffOn ℝ ∞ e e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target) (hVt : (V : Set X) ⊆ e.target)
    (hVΩ : e.symm '' (V : Set X) ⊆ Ω) {u : W1p (volume : Measure X) Ω 2}
    {v : W1p (volume : Measure X) V 2}
    (hvv : W1p.value v =ᵐ[(volume : Measure X).restrict V] fun y => W1p.value u (e.symm y))
    (hvg : W1p.gradient v =ᵐ[(volume : Measure X).restrict V]
      fun y => ContinuousLinearMap.adjoint (fderiv ℝ e.symm y) (W1p.gradient u (e.symm y)))
    {φ : TestFunction V ℝ ⊤} (ψ : TestFunction Ω ℝ ⊤)
    (hψ : ∀ y ∈ (V : Set X), ψ (e.symm y) = φ y) (hψ0 : ∀ x ∉ e.symm '' (V : Set X), ψ x = 0) :
    ∫ x in Ω, (F x - ⟪β x, W1p.gradient u x⟫_ℝ - γ x * W1p.value u x) *
        W1p.value (W1p.ofTestFunctionₗ volume Ω 2 ψ) x =
      ∫ y in V, (|(fderiv ℝ e.symm y).det| * F (e.symm y) -
        ⟪|(fderiv ℝ e.symm y).det| • fderiv ℝ e (e.symm y) (β (e.symm y)), W1p.gradient v y⟫_ℝ -
          |(fderiv ℝ e.symm y).det| * γ (e.symm y) * W1p.value v y) * φ y := by
  have h1 : ∫ x in Ω, (F x - ⟪β x, W1p.gradient u x⟫_ℝ - γ x * W1p.value u x) *
      W1p.value (W1p.ofTestFunctionₗ volume Ω 2 ψ) x =
      ∫ x in Ω, (F x - ⟪β x, W1p.gradient u x⟫_ℝ - γ x * W1p.value u x) * ψ x :=
    integral_congr_ae (by
      filter_upwards [W1p.value_ofTestFunctionₗ_ae (mu := (volume : Measure X)) (p := 2) ψ]
        with x h
      rw [h])
  rw [h1]
  refine (pde_bd_cov hes hVt hVΩ ?_).trans (integral_congr_ae ?_)
  · intro x _ hx
    beta_reduce
    rw [hψ0 x hx, mul_zero]
  · filter_upwards [hvv, hvg, ae_restrict_mem V.isOpen.measurableSet] with y h1 h2 hy
    beta_reduce
    rw [h1, h2, hψ y hy, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.comp_apply, (pde_bd_inv he hes (hVt hy)).2,
      ContinuousLinearMap.id_apply]
    ring

open TauCeti TauCeti.PDE in
open scoped InnerProductSpace in
/-- W-PDE1 P4 helper (transport of the weak equation through a chart): pulling the split weak
equation on `Ω` back by `e⁻¹` to a set `V` on the flat side gives the weak equation with
coefficients `J T A Tᵀ` (`J = |det D(e⁻¹)|`, `T = De ∘ e⁻¹`), drift `J T β` and mass `J γ`. -/
theorem pde_bd_transport {Ω : Opens X} {A : X → Matrix (Fin 2) (Fin 2) ℝ} {β : X → X}
    {γ F : X → ℝ} {u : W1p (volume : Measure X) Ω 2}
    (hu : ∀ v : W1p0 (volume : Measure X) Ω 2,
      energyFormH1 A 0 0 u (v : W1p (volume : Measure X) Ω 2) =
        ∫ x in Ω, (F x - ⟪β x, W1p.gradient u x⟫_ℝ - γ x * W1p.value u x) *
          W1p.value (v : W1p (volume : Measure X) Ω 2) x)
    {e : OpenPartialHomeomorph X X} (he : ContDiffOn ℝ ∞ e e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target) (hΩe : ∀ x ∈ e.source, x ∈ (Ω : Set X) ↔ 0 < (e x) 1)
    {V : Opens X} (hVt : (V : Set X) ⊆ e.target) (hVH : ∀ y ∈ (V : Set X), 0 < y 1)
    {v : W1p (volume : Measure X) V 2}
    (hvv : W1p.value v =ᵐ[(volume : Measure X).restrict V] fun y => W1p.value u (e.symm y))
    (hvg : W1p.gradient v =ᵐ[(volume : Measure X).restrict V]
      fun y => ContinuousLinearMap.adjoint (fderiv ℝ e.symm y) (W1p.gradient u (e.symm y)))
    {At : X → Matrix (Fin 2) (Fin 2) ℝ}
    (hAt : ∀ y ∈ (V : Set X), ∀ i j, At y i j = |(fderiv ℝ e.symm y).det| *
      ∑ k, ∑ l, fderiv ℝ e (e.symm y) (𝐞 k) i * A (e.symm y) k l * fderiv ℝ e (e.symm y) (𝐞 l) j)
    (φ : TestFunction V ℝ ⊤) :
    energyFormH1 At 0 0 v (W1p.ofTestFunctionₗ volume V 2 φ) =
      ∫ y in V, (|(fderiv ℝ e.symm y).det| * F (e.symm y) -
        ⟪|(fderiv ℝ e.symm y).det| • fderiv ℝ e (e.symm y) (β (e.symm y)), W1p.gradient v y⟫_ℝ -
          |(fderiv ℝ e.symm y).det| * γ (e.symm y) * W1p.value v y) * φ y := by
  have hVΩ : e.symm '' (V : Set X) ⊆ Ω := by
    rintro x ⟨y, hy, rfl⟩
    exact (hΩe _ (e.map_target (hVt hy))).2 (by rw [e.right_inv (hVt hy)]; exact hVH y hy)
  obtain ⟨ψ, hψ, hψ0⟩ := pde_bd_pull he hes hVt hVΩ φ
  refine (pde_bd_trL he hes hVt hVΩ hvg hAt φ ψ (fun y hy => (hψ y hy).2)
    (fun x hx => (hψ0 x hx).2)).trans
      ((hu ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule ψ⟩).trans ?_)
  exact pde_bd_trR he hes hVt hVΩ hvv hvg ψ (fun y hy => (hψ y hy).1) (fun x hx => (hψ0 x hx).1)

open TauCeti TauCeti.PDE in
/-- W-PDE1 P4 helper (bootstrap step, the weak equation): a cutoff `w` of a weak solution `v` on
`Ω₂ ≤ H`, with the gradient of `ψ v` extended by zero, solves `-div(a ∇w) = g` on `H` in the
Dirichlet sense, with `g` the zero extension of `localizedForcing a ζ f₂ v`. -/
theorem pde_bd_keyW {H Ω₂ : Opens X} (hΩ₂H : Ω₂ ≤ H) {a : X → Matrix (Fin 2) (Fin 2) ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    (hac : ∀ i j, HasCompactSupport (fun x => a x i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j))
    {v : W1p (volume : Measure X) Ω₂ 2} (f₂ : Lp ℝ 2 ((volume : Measure X).restrict Ω₂))
    (hv : ∀ v' : W1p0 (volume : Measure X) Ω₂ 2,
      energyFormH1 a 0 0 v (v' : W1p (volume : Measure X) Ω₂ 2) =
        ∫ y in Ω₂, f₂ y * W1p.value (v' : W1p (volume : Measure X) Ω₂ 2) y)
    {ζ : X → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
    (hHt : (H : Set X) ∩ tsupport ζ ⊆ Ω₂) (w : W1p (volume : Measure X) H 2)
    (hw0 : w ∈ w1p0Submodule (volume : Measure X) H 2)
    (hwg : W1p.gradient w =ᵐ[(volume : Measure X).restrict H] (Ω₂ : Set X).indicator
      (fun y => ζ y • W1p.gradient v y + W1p.value v y • gradient ζ y)) :
    ∃ g : Lp ℝ 2 ((volume : Measure X).restrict H),
      IsWeakSolutionDirichlet a 0 0 g (⟨w, hw0⟩ : W1p0 (volume : Measure X) H 2) ∧
      (g : X → ℝ) =ᵐ[(volume : Measure X).restrict H]
        (Ω₂ : Set X).indicator (localizedForcing a ζ f₂ v) := by
  have hΩ₂m : MeasurableSet (Ω₂ : Set X) := Ω₂.isOpen.measurableSet
  have hΩ₂H' : (Ω₂ : Set X) ⊆ H := hΩ₂H
  have hKl := pde_hs_lip ha hac
  have hK := hKl.choose_spec
  have hMa : ∀ x, ‖matrixBilinearForm (a x)‖ ≤
      ∑ i, ∑ j, (pde_hs_bound (ha i j) (hac i j)).choose := fun x =>
    (norm_matrixBilinearForm_le_sum_abs _).trans
      (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        ((pde_hs_bound (ha i j) (hac i j)).choose_spec x).1)
  have hcut := pde_bd_cutoff hΩ₂H hMa hK hv hζ hζc hHt (w := w) hwg
    (g := (Ω₂ : Set X).indicator (localizedForcing a ζ f₂ v)) EventuallyEq.rfl
  have hGm : MemLp ((Ω₂ : Set X).indicator (localizedForcing a ζ f₂ v)) 2
      ((volume : Measure X).restrict H) := by
    rw [memLp_indicator_iff_restrict hΩ₂m.nullMeasurableSet, Measure.restrict_restrict hΩ₂m,
      inter_eq_left.2 hΩ₂H']
    exact memLp_localizedForcing hMa hK hζ hζc f₂ v
  have hcoeff := memLp_energyIntegrand_of_continuous (mu := (volume : Measure X)) hMa
    hK.continuous H
  refine ⟨hGm.toLp _, (isWeakSolutionDirichlet_iff_forall_testFunction hcoeff _ _).2 fun φ => ?_,
    hGm.coeFn_toLp⟩
  rw [hcut φ]
  refine integral_congr_ae ?_
  filter_upwards [hGm.coeFn_toLp] with x hx
  rw [hx]

open TauCeti TauCeti.PDE in
open scoped InnerProductSpace in
/-- W-PDE1 P4 helper (bootstrap step, the forcing term): on `H`, the zero extension of
`localizedForcing a ζ f₂ v`, for `f₂ = F₂ - ⟪b₂, ∇v⟫ - c₂ v` on `Ω₂`, is `κ₀ + ⟪κ, ∇v⟫ + κ₁ v` for
smooth `κ`'s supported in `tsupport ζ`, whose supports thus meet `H` inside `B(0, s₃) ∩ H`. -/
theorem pde_bd_keyK {H Ω₂ V₃ : Opens X} (hH : (H : Set X) = {y | 0 < y 1})
    {a : X → Matrix (Fin 2) (Fin 2) ℝ} (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    {S : Set X} (hS : IsOpen S) {F₂ c₂ : X → ℝ} {b₂ : X → X}
    (hF₂ : ContDiffOn ℝ ∞ F₂ S) (hb₂ : ContDiffOn ℝ ∞ b₂ S) (hc₂ : ContDiffOn ℝ ∞ c₂ S)
    {v : W1p (volume : Measure X) Ω₂ 2} (f₂ : Lp ℝ 2 ((volume : Measure X).restrict Ω₂))
    (hf₂ : (f₂ : X → ℝ) =ᵐ[(volume : Measure X).restrict Ω₂]
      fun y => F₂ y - ⟪b₂ y, W1p.gradient v y⟫_ℝ - c₂ y * W1p.value v y)
    {s₃ r : ℝ} (hrs₃ : r < s₃) (hV₃ : (V₃ : Set X) = ball 0 s₃ ∩ {y | 0 < y 1}) {ζ : X → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζt : tsupport ζ = closedBall 0 r) (hζc : HasCompactSupport ζ)
    (hζS : tsupport ζ ⊆ S) (hHt : (H : Set X) ∩ tsupport ζ ⊆ Ω₂) :
    ∃ (κ₀ κ₁ : X → ℝ) (κ : X → X),
      (ContDiff ℝ ∞ κ₀ ∧ HasCompactSupport κ₀ ∧ (H : Set X) ∩ tsupport κ₀ ⊆ V₃) ∧
      (ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧ (H : Set X) ∩ tsupport κ ⊆ V₃) ∧
      (ContDiff ℝ ∞ κ₁ ∧ HasCompactSupport κ₁ ∧ (H : Set X) ∩ tsupport κ₁ ⊆ V₃) ∧
      (Ω₂ : Set X).indicator (localizedForcing a ζ f₂ v) =ᵐ[(volume : Measure X).restrict H]
        fun y => κ₀ y + ⟪κ y, W1p.gradient v y⟫_ℝ + κ₁ y * W1p.value v y := by
  have hΩ₂m : MeasurableSet (Ω₂ : Set X) := Ω₂.isOpen.measurableSet
  have hHt₃ : ∀ T : Set X, T ⊆ tsupport ζ → (H : Set X) ∩ T ⊆ V₃ := by
    rintro T hT y ⟨hy1, hy2⟩
    have hy2' := hT hy2
    rw [hV₃]
    rw [hH] at hy1
    rw [hζt] at hy2'
    exact ⟨mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hy2') hrs₃), hy1⟩
  have hgr : ∀ y (j : Fin 2), gradient ζ y j = fderiv ℝ ζ y (𝐞 j) := fun y j => by
    have h : inner ℝ (gradient ζ y) (𝐞 j) = gradient ζ y j := by
      rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right]
      simp only [one_mul, conj_trivial]
    rw [← h, gradient, InnerProductSpace.toDual_symm_apply]
  have hgd : ∀ j : Fin 2, ContDiff ℝ ∞ (fun y => gradient ζ y j) := fun j => by
    simp_rw [hgr]
    exact (hζ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hzero : ∀ F : X → ℝ, (∀ y, ζ y = 0 → gradient ζ y = 0 →
      divMatrixGradient a ζ y = 0 → F y = 0) → Function.support F ⊆ tsupport ζ :=
    fun F hF y hy => by_contra fun h => hy (hF y (image_eq_zero_of_notMem_tsupport h)
      (gradient_of_notMem_tsupport h) (divMatrixGradient_eq_zero_of_notMem_tsupport h))
  have hzero' : ∀ F : X → X, (∀ y, ζ y = 0 → gradient ζ y = 0 → F y = 0) →
      Function.support F ⊆ tsupport ζ :=
    fun F hF y hy => by_contra fun h => hy (hF y (image_eq_zero_of_notMem_tsupport h)
      (gradient_of_notMem_tsupport h))
  set c : Fin 2 → X → ℝ := fun i y =>
    -(ζ y * b₂ y i) - ∑ j, (a y i j + a y j i) * gradient ζ y j with hc_def
  have hcd : ∀ i, ContDiff ℝ ∞ (c i) := fun i =>
    (pde_bd_cs hS hζ hζS ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hb₂)).neg.sub
      (ContDiff.sum fun j _ => ((ha i j).add (ha j i)).mul (hgd j))
  set κ₀ : X → ℝ := fun y => ζ y * F₂ y with hκ₀_def
  set κ₁ : X → ℝ := fun y => -(ζ y * c₂ y) - divMatrixGradient a ζ y with hκ₁_def
  set κ : X → X := fun y => ∑ i, c i y • 𝐞 i with hκ_def
  have h₀s : Function.support κ₀ ⊆ tsupport ζ :=
    hzero _ fun y h0 _ _ => by simp only [hκ₀_def, h0, zero_mul]
  have h₁s : Function.support κ₁ ⊆ tsupport ζ :=
    hzero _ fun y h0 _ h2 => by simp only [hκ₁_def, h0, h2, zero_mul, neg_zero, sub_zero]
  have hs' : Function.support κ ⊆ tsupport ζ :=
    hzero' _ fun y h0 h1 => by simp [hκ_def, hc_def, h0, h1]
  have hts : ∀ {F : X → ℝ}, Function.support F ⊆ tsupport ζ → tsupport F ⊆ tsupport ζ :=
    fun h => closure_minimal h (isClosed_tsupport ζ)
  refine ⟨κ₀, κ₁, κ,
    ⟨pde_bd_cs hS hζ hζS hF₂, hζc.mono' h₀s, hHt₃ _ (hts h₀s)⟩,
    ⟨ContDiff.sum fun i _ => (hcd i).smul contDiff_const, hζc.mono' hs',
      hHt₃ _ (closure_minimal hs' (isClosed_tsupport ζ))⟩,
    ⟨(pde_bd_cs hS hζ hζS hc₂).neg.sub (pde_bd_div ha hζ).1, hζc.mono' h₁s,
      hHt₃ _ (hts h₁s)⟩, ?_⟩
  filter_upwards [ae_restrict_of_ae ((ae_restrict_iff' hΩ₂m).1 hf₂),
    ae_restrict_mem H.isOpen.measurableSet] with x h2 hxH
  by_cases hx : x ∈ (Ω₂ : Set X)
  · rw [indicator_of_mem hx, localizedForcing_def, h2 hx]
    simp only [hκ₀_def, hκ₁_def, hκ_def, hc_def, matrixBilinearForm_apply, dotProduct, mulVec,
      Fin.sum_univ_two, EuclideanSpace.basisFun_apply, PiLp.inner_apply, RCLike.inner_apply,
      conj_trivial]
    simp
    ring
  · have hxζ : x ∉ tsupport ζ := fun h => hx (hHt ⟨hxH, h⟩)
    have z : ζ x = 0 := image_eq_zero_of_notMem_tsupport hxζ
    have z1 : gradient ζ x = 0 := gradient_of_notMem_tsupport hxζ
    have z2 : divMatrixGradient a ζ x = 0 := divMatrixGradient_eq_zero_of_notMem_tsupport hxζ
    rw [indicator_of_notMem hx]
    simp [hκ₀_def, hκ₁_def, hκ_def, hc_def, z, z1, z2]

open TauCeti TauCeti.PDE in
open scoped InnerProductSpace in
/-- W-PDE1 P4 helper (one bootstrap step, for a given cutoff `ζ` with bounds `M`): assembles
`pde_bd_keyW` and `pde_bd_keyK` for `w = ζ v` extended by zero. -/
theorem pde_bd_key2 {H Ω₂ : Opens X} (hH : (H : Set X) = {y | 0 < y 1}) (hΩ₂H : Ω₂ ≤ H)
    {ρ : ℝ} (hΩ₂ : (Ω₂ : Set X) = ball 0 ρ ∩ {y | 0 < y 1})
    {a : X → Matrix (Fin 2) (Fin 2) ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    (hac : ∀ i j, HasCompactSupport (fun x => a x i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j))
    {S : Set X} (hS : IsOpen S) (hρS : closedBall 0 ρ ⊆ S) {F₂ c₂ : X → ℝ} {b₂ : X → X}
    (hF₂ : ContDiffOn ℝ ∞ F₂ S) (hb₂ : ContDiffOn ℝ ∞ b₂ S) (hc₂ : ContDiffOn ℝ ∞ c₂ S)
    {v : W1p (volume : Measure X) Ω₂ 2} (f₂ : Lp ℝ 2 ((volume : Measure X).restrict Ω₂))
    (hf₂ : (f₂ : X → ℝ) =ᵐ[(volume : Measure X).restrict Ω₂]
      fun y => F₂ y - ⟪b₂ y, W1p.gradient v y⟫_ℝ - c₂ y * W1p.value v y)
    (hv : ∀ v' : W1p0 (volume : Measure X) Ω₂ 2,
      energyFormH1 a 0 0 v (v' : W1p (volume : Measure X) Ω₂ 2) =
        ∫ y in Ω₂, f₂ y * W1p.value (v' : W1p (volume : Measure X) Ω₂ 2) y)
    (hv0 : ∀ (ζ : X → ℝ) (hζ : ContDiff ℝ ∞ ζ) (M : ℝ) (hM : 0 ≤ M)
      (hζM : ∀ x ∈ Ω₂, |ζ x| ≤ M) (hgM : ∀ x ∈ Ω₂, ‖gradient ζ x‖ ≤ M)
      (hs : (H : Set X) ∩ tsupport ζ ⊆ Ω₂), tsupport ζ ⊆ ball 0 ρ →
        W1p.localizeL hΩ₂H ζ hζ hM hζM hgM hs v ∈ w1p0Submodule (volume : Measure X) H 2)
    {s s₃ : ℝ} (hsρ : s < ρ) (hs₃ : s₃ < ρ) (V V₃ : Opens X)
    (hV : (V : Set X) = ball 0 s ∩ {y | 0 < y 1})
    (hV₃ : (V₃ : Set X) = ball 0 s₃ ∩ {y | 0 < y 1}) {r : ℝ} (hrs₃ : r < s₃) {ζ : X → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζt : tsupport ζ = closedBall 0 r) (hζc : HasCompactSupport ζ)
    (hζ1 : ∀ y ∈ closedBall (0 : X) s, ζ y = 1) {M : ℝ} (hM0 : 0 ≤ M)
    (hζM : ∀ x, |ζ x| ≤ M) (hgζ : ∀ x, ‖gradient ζ x‖ ≤ M) :
    ∃ (w : W1p0 (volume : Measure X) H 2) (g : Lp ℝ 2 ((volume : Measure X).restrict H))
      (κ₀ κ₁ : X → ℝ) (κ : X → X),
      IsWeakSolutionDirichlet a 0 0 g w ∧
      W1p.value (w : W1p (volume : Measure X) H 2) =ᵐ[(volume : Measure X).restrict V]
        W1p.value v ∧
      (ContDiff ℝ ∞ κ₀ ∧ HasCompactSupport κ₀ ∧ (H : Set X) ∩ tsupport κ₀ ⊆ V₃) ∧
      (ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧ (H : Set X) ∩ tsupport κ ⊆ V₃) ∧
      (ContDiff ℝ ∞ κ₁ ∧ HasCompactSupport κ₁ ∧ (H : Set X) ∩ tsupport κ₁ ⊆ V₃) ∧
      (g : X → ℝ) =ᵐ[(volume : Measure X).restrict H]
        fun y => κ₀ y + ⟪κ y, W1p.gradient v y⟫_ℝ + κ₁ y * W1p.value v y := by
  have hΩ₂H' : (Ω₂ : Set X) ⊆ H := hΩ₂H
  have hHt : (H : Set X) ∩ tsupport ζ ⊆ Ω₂ := by
    rintro y ⟨hy1, hy2⟩
    rw [hΩ₂]
    rw [hH] at hy1
    rw [hζt] at hy2
    exact ⟨mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hy2) (by linarith)), hy1⟩
  have hζS : tsupport ζ ⊆ S := by
    rw [hζt]
    exact (closedBall_subset_closedBall (by linarith)).trans hρS
  have hVΩ₂ : (V : Set X) ⊆ Ω₂ := by
    rw [hV, hΩ₂]
    exact inter_subset_inter_left _ (ball_subset_ball (by linarith))
  have hW := pde_bd_keyW hΩ₂H ha hac f₂ hv hζ hζc hHt _
    (hv0 ζ hζ M hM0 (fun x _ => hζM x) (fun x _ => hgζ x) hHt
      (by rw [hζt]; exact closedBall_subset_ball (by linarith)))
    (W1p.gradient_localizeL_ae hΩ₂H hζ hM0 (fun x _ => hζM x) (fun x _ => hgζ x) hHt v)
  have hK := pde_bd_keyK hH ha hS hF₂ hb₂ hc₂ f₂ hf₂ hrs₃ hV₃ hζ hζt hζc hζS hHt
  have hwv := W1p.value_localizeL_ae hΩ₂H hζ hM0 (fun x _ => hζM x) (fun x _ => hgζ x) hHt v
  refine ⟨_, hW.choose, hK.choose, hK.choose_spec.choose, hK.choose_spec.choose_spec.choose,
    hW.choose_spec.1, ?_, hK.choose_spec.choose_spec.choose_spec.1,
    hK.choose_spec.choose_spec.choose_spec.2.1, hK.choose_spec.choose_spec.choose_spec.2.2.1,
    hW.choose_spec.2.trans hK.choose_spec.choose_spec.choose_spec.2.2.2⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (hVΩ₂.trans hΩ₂H') hwv,
    ae_restrict_mem V.isOpen.measurableSet] with x h1 hxV
  rw [h1, indicator_of_mem (hVΩ₂ hxV)]
  have hx1 : ζ x = 1 := hζ1 x
    (ball_subset_closedBall (by rw [hV] at hxV; exact hxV.1))
  rw [hx1, one_smul]

open TauCeti TauCeti.PDE in
open scoped InnerProductSpace in
/-- W-PDE1 P4 helper (one bootstrap step on the flat side): in the setting of `pde_bd_loc`, for
`s < s₃ < ρ` a cutoff `ζ = 1` on `B(0, s)` with support in `B(0, s₃)` turns `v` into a weak
solution `w ∈ H¹₀(H)` of `-div(a ∇w) = g`, with `w = v` on `V = B(0, s) ∩ H` and
`g = κ₀ + ⟪κ, ∇v⟫ + κ₁ v` for smooth `κ`'s whose supports meet `H` inside `B(0, s₃) ∩ H`. -/
theorem pde_bd_key {H Ω₂ : Opens X} (hH : (H : Set X) = {y | 0 < y 1}) (hΩ₂H : Ω₂ ≤ H)
    {ρ : ℝ} (hΩ₂ : (Ω₂ : Set X) = ball 0 ρ ∩ {y | 0 < y 1})
    {a : X → Matrix (Fin 2) (Fin 2) ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    (hac : ∀ i j, HasCompactSupport (fun x => a x i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j))
    {S : Set X} (hS : IsOpen S) (hρS : closedBall 0 ρ ⊆ S) {F₂ c₂ : X → ℝ} {b₂ : X → X}
    (hF₂ : ContDiffOn ℝ ∞ F₂ S) (hb₂ : ContDiffOn ℝ ∞ b₂ S) (hc₂ : ContDiffOn ℝ ∞ c₂ S)
    {v : W1p (volume : Measure X) Ω₂ 2} (f₂ : Lp ℝ 2 ((volume : Measure X).restrict Ω₂))
    (hf₂ : (f₂ : X → ℝ) =ᵐ[(volume : Measure X).restrict Ω₂]
      fun y => F₂ y - ⟪b₂ y, W1p.gradient v y⟫_ℝ - c₂ y * W1p.value v y)
    (hv : ∀ v' : W1p0 (volume : Measure X) Ω₂ 2,
      energyFormH1 a 0 0 v (v' : W1p (volume : Measure X) Ω₂ 2) =
        ∫ y in Ω₂, f₂ y * W1p.value (v' : W1p (volume : Measure X) Ω₂ 2) y)
    (hv0 : ∀ (ζ : X → ℝ) (hζ : ContDiff ℝ ∞ ζ) (M : ℝ) (hM : 0 ≤ M)
      (hζM : ∀ x ∈ Ω₂, |ζ x| ≤ M) (hgM : ∀ x ∈ Ω₂, ‖gradient ζ x‖ ≤ M)
      (hs : (H : Set X) ∩ tsupport ζ ⊆ Ω₂), tsupport ζ ⊆ ball 0 ρ →
        W1p.localizeL hΩ₂H ζ hζ hM hζM hgM hs v ∈ w1p0Submodule (volume : Measure X) H 2)
    {s s₃ : ℝ} (hs0 : 0 < s) (hss : s < s₃) (hs₃ : s₃ < ρ) (V V₃ : Opens X)
    (hV : (V : Set X) = ball 0 s ∩ {y | 0 < y 1})
    (hV₃ : (V₃ : Set X) = ball 0 s₃ ∩ {y | 0 < y 1}) :
    ∃ (w : W1p0 (volume : Measure X) H 2) (g : Lp ℝ 2 ((volume : Measure X).restrict H))
      (κ₀ κ₁ : X → ℝ) (κ : X → X),
      IsWeakSolutionDirichlet a 0 0 g w ∧
      W1p.value (w : W1p (volume : Measure X) H 2) =ᵐ[(volume : Measure X).restrict V]
        W1p.value v ∧
      (ContDiff ℝ ∞ κ₀ ∧ HasCompactSupport κ₀ ∧ (H : Set X) ∩ tsupport κ₀ ⊆ V₃) ∧
      (ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧ (H : Set X) ∩ tsupport κ ⊆ V₃) ∧
      (ContDiff ℝ ∞ κ₁ ∧ HasCompactSupport κ₁ ∧ (H : Set X) ∩ tsupport κ₁ ⊆ V₃) ∧
      (g : X → ℝ) =ᵐ[(volume : Measure X).restrict H]
        fun y => κ₀ y + ⟪κ y, W1p.gradient v y⟫_ℝ + κ₁ y * W1p.value v y := by
  set r := (s + s₃) / 2 with hr_def
  have hsr : s < r := by rw [hr_def]; linarith
  have hrs₃ : r < s₃ := by rw [hr_def]; linarith
  obtain ⟨ζ, hζ, hζt, hζc, hζ1⟩ : ∃ ζ : X → ℝ, ContDiff ℝ ∞ ζ ∧ tsupport ζ = closedBall 0 r ∧
      HasCompactSupport ζ ∧ ∀ y ∈ closedBall (0 : X) s, ζ y = 1 := by
    let ζb : ContDiffBump (0 : X) := ⟨s, r, hs0, hsr⟩
    exact ⟨ζb, ζb.contDiff, ζb.tsupport_eq, ζb.hasCompactSupport,
      fun y hy => ζb.one_of_mem_closedBall hy⟩
  have hcc : HasCompactSupport (fun x => ζ x - 0) := by simpa only [sub_zero] using hζc
  have hb : ∃ M, ∀ x, |ζ x| ≤ M ∧ ‖fderiv ℝ ζ x‖ ≤ M := pde_hs_bound hζ hcc
  have hMζ := hb.choose_spec
  have hM0 : 0 ≤ hb.choose := (abs_nonneg _).trans (hMζ 0).1
  have hgζ : ∀ x, ‖gradient ζ x‖ ≤ hb.choose := fun x => by
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact (hMζ x).2
  exact pde_bd_key2 hH hΩ₂H hΩ₂ ha hac hS hρS hF₂ hb₂ hc₂ f₂ hf₂ hv hv0 (by linarith) hs₃ V V₃
    hV hV₃ hrs₃ hζ hζt hζc hζ1 hM0 (fun x => (hMζ x).1) hgζ

open TauCeti TauCeti.PDE in
open scoped InnerProductSpace in
/-- W-PDE1 P4 helper (bootstrap on the flat side): let `v ∈ H¹(Ω₂)`, `Ω₂ = B(0, ρ) ∩ H`, solve
`-div(a ∇v) = F₂ - ⟪b₂, ∇v⟫ - c₂ v` weakly on `Ω₂` (no boundary condition), with `a` smooth,
uniformly elliptic on `H` and equal to the identity outside a compact set, the lower-order data
smooth near `B̄(0, ρ)`, and every cutoff of `v` supported in `B(0, ρ)` in `H¹₀(H)`. Then
`v ∈ H^{k+1}(B(0, s) ∩ H)` for every `k` and `s < ρ`. -/
theorem pde_bd_loc {H Ω₂ : Opens X} (hH : (H : Set X) = {y | 0 < y 1}) (hΩ₂H : Ω₂ ≤ H)
    {ρ : ℝ} (hΩ₂ : (Ω₂ : Set X) = ball 0 ρ ∩ {y | 0 < y 1})
    {a : X → Matrix (Fin 2) (Fin 2) ℝ} {lam Lam : ℝ}
    (hell : UniformlyEllipticOn (H : Set X) a lam Lam)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    (hac : ∀ i j, HasCompactSupport (fun x => a x i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j))
    {S : Set X} (hS : IsOpen S) (hρS : closedBall 0 ρ ⊆ S) {F₂ c₂ : X → ℝ} {b₂ : X → X}
    (hF₂ : ContDiffOn ℝ ∞ F₂ S) (hb₂ : ContDiffOn ℝ ∞ b₂ S) (hc₂ : ContDiffOn ℝ ∞ c₂ S)
    {v : W1p (volume : Measure X) Ω₂ 2} (f₂ : Lp ℝ 2 ((volume : Measure X).restrict Ω₂))
    (hf₂ : (f₂ : X → ℝ) =ᵐ[(volume : Measure X).restrict Ω₂]
      fun y => F₂ y - ⟪b₂ y, W1p.gradient v y⟫_ℝ - c₂ y * W1p.value v y)
    (hv : ∀ v' : W1p0 (volume : Measure X) Ω₂ 2,
      energyFormH1 a 0 0 v (v' : W1p (volume : Measure X) Ω₂ 2) =
        ∫ y in Ω₂, f₂ y * W1p.value (v' : W1p (volume : Measure X) Ω₂ 2) y)
    (hv0 : ∀ (ζ : X → ℝ) (hζ : ContDiff ℝ ∞ ζ) (M : ℝ) (hM : 0 ≤ M)
      (hζM : ∀ x ∈ Ω₂, |ζ x| ≤ M) (hgM : ∀ x ∈ Ω₂, ‖gradient ζ x‖ ≤ M)
      (hs : (H : Set X) ∩ tsupport ζ ⊆ Ω₂), tsupport ζ ⊆ ball 0 ρ →
        W1p.localizeL hΩ₂H ζ hζ hM hζM hgM hs v ∈ w1p0Submodule (volume : Measure X) H 2)
    (k : ℕ) {s : ℝ} (hs0 : 0 < s) (hsρ : s < ρ) (V : Opens X)
    (hV : (V : Set X) = ball 0 s ∩ {y | 0 < y 1}) :
    ∃ W : Wkp (volume : Measure X) V 2 (k + 1),
      (Wkp.value (k + 1) W : X → ℝ) =ᵐ[(volume : Measure X).restrict V] W1p.value v := by
  have hHo : ∀ t : ℝ, IsOpen (ball (0 : X) t ∩ (H : Set X)) := fun t => isOpen_ball.inter H.isOpen
  have hQ : ∀ k : ℕ, ∀ s : ℝ, 0 < s → s < ρ → ∀ V : Opens X,
      (V : Set X) = ball 0 s ∩ {y | 0 < y 1} →
      ∃ W : Wkp (volume : Measure X) V 2 (k + 2),
        (Wkp.value (k + 2) W : X → ℝ) =ᵐ[(volume : Measure X).restrict V] W1p.value v := by
    intro k
    induction k with
    | zero =>
      intro s hs0 hsρ V hV
      have hVH : V ≤ H := fun y hy => by
        have hy' : y ∈ (V : Set X) := hy
        rw [hV] at hy'
        change y ∈ (H : Set X)
        rw [hH]
        exact hy'.2
      obtain ⟨w, g, κ₀, κ₁, κ, hsol, hwv, -⟩ := pde_bd_key hH hΩ₂H hΩ₂ ha hac hS hρS hF₂ hb₂ hc₂
        f₂ hf₂ hv hv0 hs0 (s₃ := (s + ρ) / 2) (by linarith) (by linarith) V
        ⟨_, hHo ((s + ρ) / 2)⟩ hV (by change _ ∩ _ = _; rw [hH])
      obtain ⟨W, hW⟩ := pde_hs_Hk hH hell ha hac g hsol 0 ⟨g, EventuallyEq.rfl⟩
      have hW' : (Wkp.value 2 W : X → ℝ) =ᵐ[(volume : Measure X).restrict V]
          W1p.value (w : W1p (volume : Measure X) H 2) :=
        ae_restrict_of_ae_restrict_of_subset hVH hW
      exact ⟨Wkp.restrictL hVH 2 W, (Wkp.value_restrictL_ae hVH 2 W).trans (hW'.trans hwv)⟩
    | succ k ih =>
      intro s hs0 hsρ V hV
      have hVH : V ≤ H := fun y hy => by
        have hy' : y ∈ (V : Set X) := hy
        rw [hV] at hy'
        change y ∈ (H : Set X)
        rw [hH]
        exact hy'.2
      set s₃ := (s + ρ) / 2 with hs₃_def
      let V₃ : Opens X := ⟨_, hHo s₃⟩
      have hV₃ : (V₃ : Set X) = ball 0 s₃ ∩ {y | 0 < y 1} := by
        change _ ∩ _ = _
        rw [hH]
      have hV₃Ω₂ : V₃ ≤ Ω₂ := fun y hy => by
        have hy' : y ∈ (V₃ : Set X) := hy
        change y ∈ (Ω₂ : Set X)
        rw [hΩ₂]
        rw [hV₃] at hy'
        exact ⟨ball_subset_ball (by linarith) hy'.1, hy'.2⟩
      have hV₃H : V₃ ≤ H := hV₃Ω₂.trans hΩ₂H
      have hV₃m : (volume : Measure X) V₃ < ⊤ :=
        (measure_mono inter_subset_left).trans_lt measure_ball_lt_top
      obtain ⟨Wv, hWv⟩ := ih s₃ (by linarith) (by linarith) V₃ hV₃
      obtain ⟨w, g, κ₀, κ₁, κ, hsol, hwv, ⟨h₀, h₀c, h₀s⟩, ⟨h, hc, hs⟩, ⟨h₁, h₁c, h₁s⟩, hgκ⟩ :=
        pde_bd_key hH hΩ₂H hΩ₂ ha hac hS hρS hF₂ hb₂ hc₂ f₂ hf₂ hv hv0 hs0 (s₃ := s₃)
          (by linarith) (by linarith) V V₃ hV hV₃
      obtain ⟨G, hG⟩ := pde_bd_rhs hV₃Ω₂ hV₃H hV₃m v (k + 1) ⟨Wv, hWv⟩ h₀ h₀c h₀s h hc hs
        h₁ h₁c h₁s
      obtain ⟨W, hW⟩ := pde_hs_Hk hH hell ha hac g hsol (k + 1) ⟨G, hG.trans hgκ.symm⟩
      have hW' : (Wkp.value (k + 1 + 2) W : X → ℝ) =ᵐ[(volume : Measure X).restrict V]
          W1p.value (w : W1p (volume : Measure X) H 2) :=
        ae_restrict_of_ae_restrict_of_subset hVH hW
      exact ⟨Wkp.restrictL hVH (k + 1 + 2) W,
        (Wkp.value_restrictL_ae hVH (k + 1 + 2) W).trans (hW'.trans hwv)⟩
  obtain ⟨W, hW⟩ := hQ k s hs0 hsρ V hV
  exact ⟨Wkp.lowerOrder (k + 1) W, hW⟩

open TauCeti.PDE in
/-- W-PDE1 P4 helper (flat-side coefficients): blending the transported coefficients
`J T A Tᵀ` with the identity by a bump equal to `1` on `B̄(0, ρ)` gives smooth, uniformly elliptic
coefficients equal to the identity off a compact set and to `J T A Tᵀ` on `B̄(0, ρ)`. -/
theorem pde_bd_acoef {U : Opens X} {A : X → Matrix (Fin 2) (Fin 2) ℝ} {lam Lam : ℝ}
    (hell : UniformlyEllipticOn (U : Set X) A lam Lam)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U) {e : OpenPartialHomeomorph X X}
    (he : ContDiffOn ℝ ∞ e e.source) (hes : ContDiffOn ℝ ∞ e.symm e.target) (heU : e.source ⊆ U)
    {ρ : ℝ} (hρ : 0 < ρ) (hρt : closedBall (0 : X) (2 * ρ) ⊆ e.target) :
    ∃ a : X → Matrix (Fin 2) (Fin 2) ℝ, (∀ i j, ContDiff ℝ ∞ (fun x => a x i j)) ∧
      (∀ i j, HasCompactSupport (fun x => a x i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
      (∃ l L : ℝ, ∀ S : Set X, UniformlyEllipticOn S a l L) ∧
      ∀ y ∈ closedBall (0 : X) ρ, ∀ i j, a y i j = |(fderiv ℝ e.symm y).det| *
        ∑ k, ∑ l, fderiv ℝ e (e.symm y) (𝐞 k) i * A (e.symm y) k l *
          fderiv ℝ e (e.symm y) (𝐞 l) j := by
  let At : X → Matrix (Fin 2) (Fin 2) ℝ := fun y => Matrix.of fun i j =>
    |(fderiv ℝ e.symm y).det| * ∑ k, ∑ l, fderiv ℝ e (e.symm y) (𝐞 k) i * A (e.symm y) k l *
      fderiv ℝ e (e.symm y) (𝐞 l) j
  let χb : ContDiffBump (0 : X) := ⟨ρ, 3 * ρ / 2, hρ, by linarith⟩
  have hCt : closedBall (0 : X) (3 * ρ / 2) ⊆ e.target :=
    (closedBall_subset_closedBall (by linarith)).trans hρt
  have hχt : tsupport (χb : X → ℝ) ⊆ e.target := by
    rw [χb.tsupport_eq]
    exact hCt
  obtain ⟨l, L, hl, hlL⟩ := pde_bd_tell hell he hes heU (isCompact_closedBall (0 : X) (3 * ρ / 2))
    hCt (At := At) (fun y _ i j => rfl)
  have hD : ∀ k i : Fin 2, ContDiffOn ℝ ∞ (fun y => fderiv ℝ e (e.symm y) (𝐞 k) i) e.target :=
    fun k i => (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn
      ((pde_bd_smooth he hes).2.clm_apply contDiffOn_const)
  have hAΦ : ∀ k l, ContDiffOn ℝ ∞ (fun y => A (e.symm y) k l) e.target := fun k l =>
    (hA k l).comp hes fun y hy => heU (e.map_target hy)
  have hAt : ∀ i j, ContDiffOn ℝ ∞ (fun y => At y i j) e.target := fun i j =>
    (pde_bd_smooth he hes).1.mul (ContDiffOn.sum fun k _ => ContDiffOn.sum fun l _ =>
      ((hD k i).mul (hAΦ k l)).mul (hD l j))
  refine ⟨fun y => χb y • At y + (1 - χb y) • (1 : Matrix (Fin 2) (Fin 2) ℝ), fun i j => ?_,
    fun i j => ?_, ⟨min l 1, max L 1, fun S => pde_bd_ell hl (fun x => χb.nonneg)
      (fun x => χb.le_one) (fun x hx => by_contra fun h => hx
        (image_eq_zero_of_notMem_tsupport (by rwa [χb.tsupport_eq]))) hlL S⟩,
    fun y hy i j => ?_⟩
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact (pde_bd_cs e.open_target χb.contDiff hχt (hAt i j)).add
      ((contDiff_const.sub χb.contDiff).mul contDiff_const)
  · refine HasCompactSupport.intro (χb.hasCompactSupport : IsCompact (tsupport (χb : X → ℝ)))
      fun x hx => ?_
    have h0 : χb x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [h0]
  · have h1 : χb y = 1 := χb.one_of_mem_closedBall hy
    beta_reduce
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, h1]
    simp [At]

open TauCeti in
open scoped InnerProductSpace in
/-- W-PDE1 P4 helper (flat-side data in `L²`): lower-order data continuous on a compact set
containing `Ω₂` give an `L²(Ω₂)` right-hand side `F₂ - ⟪b₂, ∇v⟫ - c₂ v`. -/
theorem pde_bd_fdata {Ω₂ : Opens X} {S : Set X} (hΩ₂S : (Ω₂ : Set X) ⊆ S) (hS : IsCompact S)
    {F₂ c₂ : X → ℝ} {b₂ : X → X} (hF : ContinuousOn F₂ S) (hb : ContinuousOn b₂ S)
    (hc : ContinuousOn c₂ S) (v : W1p (volume : Measure X) Ω₂ 2) :
    ∃ f₂ : Lp ℝ 2 ((volume : Measure X).restrict Ω₂),
      (f₂ : X → ℝ) =ᵐ[(volume : Measure X).restrict Ω₂]
        fun y => F₂ y - ⟪b₂ y, W1p.gradient v y⟫_ℝ - c₂ y * W1p.value v y := by
  have hms := Ω₂.isOpen.measurableSet
  have : IsFiniteMeasure ((volume : Measure X).restrict Ω₂) :=
    isFiniteMeasure_restrict.2 ((measure_mono hΩ₂S).trans_lt hS.measure_lt_top).ne
  obtain ⟨BF, hBF⟩ := hS.exists_bound_of_continuousOn hF
  obtain ⟨Bb, hBb⟩ := hS.exists_bound_of_continuousOn hb
  obtain ⟨Bc, hBc⟩ := hS.exists_bound_of_continuousOn hc
  have hae := ae_restrict_mem (μ := (volume : Measure X)) hms
  have h1 : MemLp F₂ 2 ((volume : Measure X).restrict Ω₂) :=
    (memLp_top_of_bound ((hF.mono hΩ₂S).aestronglyMeasurable hms) BF
      (hae.mono fun x hx => hBF x (hΩ₂S hx))).mono_exponent le_top
  have hg := Lp.memLp (W1p.gradient v)
  have h2 : MemLp (fun y => ⟪b₂ y, W1p.gradient v y⟫_ℝ) 2 ((volume : Measure X).restrict Ω₂) :=
    hg.of_le_mul (c := Bb) (((hb.mono hΩ₂S).aestronglyMeasurable hms).inner hg.aestronglyMeasurable)
      (hae.mono fun x hx => (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hBb x (hΩ₂S hx)) (norm_nonneg _)))
  have h3 : MemLp (fun y => c₂ y * W1p.value v y) 2 ((volume : Measure X).restrict Ω₂) :=
    (memLp_top_of_bound ((hc.mono hΩ₂S).aestronglyMeasurable hms) Bc
      (hae.mono fun x hx => hBc x (hΩ₂S hx))).fun_mul (Lp.memLp (W1p.value v))
  have h := (h1.sub h2).sub h3
  exact ⟨h.toLp _, h.coeFn_toLp⟩

open TauCeti in
/-- W-PDE1 P4 helper (the cutoff condition of `pde_bd_loc`): cutoffs, supported in `B(0, ρ)`, of
the pull-back of `u ∈ H¹₀(Ω)` by the chart lie in `H¹₀(H)`. -/
theorem pde_bd_v0 {Ω H Ω₂ : Opens X} (hH : (H : Set X) = {y | 0 < y 1}) (hΩ₂H : Ω₂ ≤ H)
    {ρ : ℝ} {e : OpenPartialHomeomorph X X} (hes : ContDiffOn ℝ ∞ e.symm e.target)
    (hρt : closedBall (0 : X) ρ ⊆ e.target) (hΩe : ∀ x ∈ e.source, x ∈ (Ω : Set X) ↔ 0 < (e x) 1)
    {L c : ℝ} (hd : DifferentiableOn ℝ e.symm Ω₂) (hinj : InjOn e.symm Ω₂)
    (hmaps : MapsTo e.symm Ω₂ Ω) (hL : ∀ y ∈ (Ω₂ : Set X), ‖fderiv ℝ e.symm y‖ ≤ L) (hc : 0 < c)
    (hdet : ∀ y ∈ (Ω₂ : Set X), c ≤ |(fderiv ℝ e.symm y).det|)
    {u : W1p (volume : Measure X) Ω 2} (hu : u ∈ w1p0Submodule (volume : Measure X) Ω 2)
    (ζ : X → ℝ) (hζ : ContDiff ℝ ∞ ζ) (M : ℝ) (hM : 0 ≤ M) (hζM : ∀ x ∈ Ω₂, |ζ x| ≤ M)
    (hgM : ∀ x ∈ Ω₂, ‖gradient ζ x‖ ≤ M) (hs : (H : Set X) ∩ tsupport ζ ⊆ Ω₂)
    (hζρ : tsupport ζ ⊆ ball 0 ρ) :
    W1p.localizeL hΩ₂H ζ hζ hM hζM hgM hs
        (W1p.compL e.symm (p := 2) (by norm_num) hd hinj hmaps hL hc hdet u) ∈
      w1p0Submodule (volume : Measure X) H 2 := by
  refine pde_bd_w1p0 hΩ₂H hd hinj hmaps hL hc hdet hζ hM hζM hgM hs (fun C hC hCΩ => ?_) hu
  have hst : tsupport ζ ⊆ e.target := hζρ.trans (ball_subset_closedBall.trans hρt)
  have hcl : IsClosed (tsupport ζ ∩ e.symm ⁻¹' C) :=
    (hes.continuousOn.mono hst).preimage_isClosed_of_isClosed (isClosed_tsupport ζ) hC.isClosed
  refine ⟨tsupport ζ ∩ e.symm ⁻¹' C, (isCompact_closedBall (0 : X) ρ).of_isClosed_subset hcl
    fun y hy => ball_subset_closedBall (hζρ hy.1), fun y hy => ?_,
    fun y _ hζy hyC => ⟨subset_tsupport ζ hζy, hyC⟩⟩
  have hyt := hst hy.1
  have h := (hΩe _ (e.map_target hyt)).1 (hCΩ hy.2)
  rw [e.right_inv hyt] at h
  show y ∈ (H : Set X)
  rw [hH]
  exact h

open TauCeti TauCeti.PDE in
open scoped InnerProductSpace in
/-- W-PDE1 P4 helper: with coefficients and data smooth on `U ⊇ Ω̄`, `Ω̄` compact, a weak
solution of the Dirichlet problem solves the split weak equation. -/
theorem pde_bd_split {Ω U : Opens X} (hΩc : IsCompact (closure (Ω : Set X)))
    (hΩU : closure (Ω : Set X) ⊆ U) {A : X → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U) {β : X → X} {γ F : X → ℝ}
    (hβ : ContDiffOn ℝ ∞ β U) (hγ : ContDiffOn ℝ ∞ γ U)
    (f : Lp ℝ 2 ((volume : Measure X).restrict Ω))
    (hfF : (f : X → ℝ) =ᵐ[(volume : Measure X).restrict Ω] F) {u : W1p0 (volume : Measure X) Ω 2}
    (hu : IsWeakSolutionDirichlet A β γ f u) (v : W1p0 (volume : Measure X) Ω 2) :
    energyFormH1 A 0 0 (u : W1p (volume : Measure X) Ω 2) (v : W1p (volume : Measure X) Ω 2) =
      ∫ x in Ω, (F x - ⟪β x, W1p.gradient (u : W1p (volume : Measure X) Ω 2) x⟫_ℝ -
        γ x * W1p.value (u : W1p (volume : Measure X) Ω 2) x) *
          W1p.value (v : W1p (volume : Measure X) Ω 2) x := by
  have hΩS : (Ω : Set X) ⊆ closure (Ω : Set X) := subset_closure
  have hms := Ω.isOpen.measurableSet
  have hAc : ∀ i j, ContinuousOn (fun x => A x i j) (closure (Ω : Set X)) := fun i j =>
    (hA i j).continuousOn.mono hΩU
  choose BA hBA using fun i j => hΩc.exists_bound_of_continuousOn (hAc i j)
  obtain ⟨B, hB⟩ := hΩc.exists_bound_of_continuousOn (hβ.continuousOn.mono hΩU)
  obtain ⟨G, hG⟩ := hΩc.exists_bound_of_continuousOn (hγ.continuousOn.mono hΩU)
  have hAo : ContinuousOn A (Ω : Set X) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hAc i j).mono hΩS
  let : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℝ))
  exact pde_split_of_weak (continuous_matrixBilinearForm.comp_aestronglyMeasurable
      (hAo.aestronglyMeasurable hms))
    ((hβ.continuousOn.mono (hΩS.trans hΩU)).aestronglyMeasurable hms)
    ((hγ.continuousOn.mono (hΩS.trans hΩU)).aestronglyMeasurable hms)
    (K := ∑ i, ∑ j, BA i j) (fun x hx => (norm_matrixBilinearForm_le_sum_abs _).trans
      (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
        simpa [Real.norm_eq_abs] using hBA i j x (hΩS hx)))
    (fun x hx => hB x (hΩS hx)) (fun x hx => by simpa [Real.norm_eq_abs] using hG x (hΩS hx))
    f hfF hu v

open TauCeti TauCeti.PDE in
open scoped InnerProductSpace in
/-- W-PDE1 P4 helper (the flat-side weak equation): the pull-back `v` of a solution of the split
weak equation solves the transported equation on `Ω₂`, against all of `H¹₀(Ω₂)`. -/
theorem pde_bd_veq {Ω Ω₂ : Opens X} {A a : X → Matrix (Fin 2) (Fin 2) ℝ} {β : X → X}
    {γ F : X → ℝ} {u : W1p (volume : Measure X) Ω 2}
    (hsplit : ∀ v : W1p0 (volume : Measure X) Ω 2,
      energyFormH1 A 0 0 u (v : W1p (volume : Measure X) Ω 2) =
        ∫ x in Ω, (F x - ⟪β x, W1p.gradient u x⟫_ℝ - γ x * W1p.value u x) *
          W1p.value (v : W1p (volume : Measure X) Ω 2) x)
    {e : OpenPartialHomeomorph X X} (he : ContDiffOn ℝ ∞ e e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target) (hΩe : ∀ x ∈ e.source, x ∈ (Ω : Set X) ↔ 0 < (e x) 1)
    (hΩ₂t : (Ω₂ : Set X) ⊆ e.target) (hΩ₂H : ∀ y ∈ (Ω₂ : Set X), 0 < y 1)
    {v : W1p (volume : Measure X) Ω₂ 2}
    (hvv : W1p.value v =ᵐ[(volume : Measure X).restrict Ω₂] fun y => W1p.value u (e.symm y))
    (hvg : W1p.gradient v =ᵐ[(volume : Measure X).restrict Ω₂]
      fun y => ContinuousLinearMap.adjoint (fderiv ℝ e.symm y) (W1p.gradient u (e.symm y)))
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    (hac : ∀ i j, HasCompactSupport (fun x => a x i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j))
    (haeq : ∀ y ∈ (Ω₂ : Set X), ∀ i j, a y i j = |(fderiv ℝ e.symm y).det| *
      ∑ k, ∑ l, fderiv ℝ e (e.symm y) (𝐞 k) i * A (e.symm y) k l * fderiv ℝ e (e.symm y) (𝐞 l) j)
    (f₂ : Lp ℝ 2 ((volume : Measure X).restrict Ω₂))
    (hf₂ : (f₂ : X → ℝ) =ᵐ[(volume : Measure X).restrict Ω₂] fun y =>
      |(fderiv ℝ e.symm y).det| * F (e.symm y) -
        ⟪|(fderiv ℝ e.symm y).det| • fderiv ℝ e (e.symm y) (β (e.symm y)), W1p.gradient v y⟫_ℝ -
          |(fderiv ℝ e.symm y).det| * γ (e.symm y) * W1p.value v y)
    (v' : W1p0 (volume : Measure X) Ω₂ 2) :
    energyFormH1 a 0 0 v (v' : W1p (volume : Measure X) Ω₂ 2) =
      ∫ y in Ω₂, f₂ y * W1p.value (v' : W1p (volume : Measure X) Ω₂ 2) y := by
  have hMa : ∀ x, ‖matrixBilinearForm (a x)‖ ≤
      ∑ i, ∑ j, (pde_hs_bound (ha i j) (hac i j)).choose := fun x =>
    (norm_matrixBilinearForm_le_sum_abs _).trans
      (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        ((pde_hs_bound (ha i j) (hac i j)).choose_spec x).1)
  have hcoeff := memLp_energyIntegrand_of_continuous (mu := (volume : Measure X)) hMa
    (pde_hs_lip ha hac).choose_spec.continuous Ω₂
  refine (forall_energyFormH1_eq_setIntegral_iff_forall_testFunction hcoeff f₂ v).2
    (fun φ => ?_) v'
  refine (pde_bd_transport hsplit he hes hΩe hΩ₂t hΩ₂H hvv hvg haeq φ).trans ?_
  refine integral_congr_ae ?_
  filter_upwards [hf₂] with y hy
  rw [hy]

/-- W-PDE1 P4 deliverable (`H^k` up to the boundary, in charts): let `Ω = {ψ < 0}` be bounded
with `∇ψ ≠ 0` on `{ψ = 0}`, let the coefficients and `F` be smooth and `A` uniformly elliptic on
an open `U ⊇ Ω̄`, and let `u ∈ H¹₀(Ω)` be the weak solution with data `f =ᵐ F`. Every boundary
point has a flattening chart `e` and a radius `r` such that `u ∘ e⁻¹ ∈ H^k` on the half-disc
`B(0, r) ∩ {0 < y₁}` for every `k`. -/
theorem pde_boundary_Hk {Ω U : Opens X} (hΩc : IsCompact (closure (Ω : Set X)))
    (hΩU : closure (Ω : Set X) ⊆ U) {ψ : X → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hΩψ : (Ω : Set X) = {x | ψ x < 0}) (hψ0 : ∀ x, ψ x = 0 → fderiv ℝ ψ x ≠ 0)
    {A : X → Matrix (Fin 2) (Fin 2) ℝ} {lam Lam : ℝ}
    (hell : TauCeti.PDE.UniformlyEllipticOn (U : Set X) A lam Lam)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U) {β : X → X} {γ F : X → ℝ}
    (hβ : ContDiffOn ℝ ∞ β U) (hγ : ContDiffOn ℝ ∞ γ U) (hF : ContDiffOn ℝ ∞ F U)
    (f : Lp ℝ 2 ((volume : Measure X).restrict Ω))
    (hfF : (f : X → ℝ) =ᵐ[(volume : Measure X).restrict Ω] F)
    {u : TauCeti.W1p0 (volume : Measure X) Ω 2}
    (hu : TauCeti.PDE.IsWeakSolutionDirichlet A β γ f u)
    {x₀ : X} (hx₀ : x₀ ∈ frontier (Ω : Set X)) :
    ∃ (e : OpenPartialHomeomorph X X) (r : ℝ), 0 < r ∧ x₀ ∈ e.source ∧ e x₀ = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧ ball 0 r ⊆ e.target ∧
      (∀ x ∈ e.source, x ∈ (Ω : Set X) ↔ 0 < (e x) 1) ∧
      ∀ (k : ℕ) (V : Opens X), (V : Set X) = ball 0 r ∩ {y | 0 < y 1} →
        ∃ w : TauCeti.Wkp (volume : Measure X) V 2 k,
          (TauCeti.Wkp.value k w : X → ℝ) =ᵐ[(volume : Measure X).restrict V]
            fun y => TauCeti.W1p.value (u : TauCeti.W1p (volume : Measure X) Ω 2) (e.symm y) := by
  obtain ⟨e, ρ, hρ, hx₀e, he0, he, hes, heU, hρt, hΩe⟩ := pde_bd_chart hΩU hψ hΩψ hψ0 hx₀
  have hsplit := pde_bd_split hΩc hΩU hA hβ hγ f hfF hu
  have hρt' : closedBall (0 : X) ρ ⊆ e.target :=
    (closedBall_subset_closedBall (by linarith)).trans hρt
  refine ⟨e, ρ / 2, by positivity, hx₀e, he0, he, hes,
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hρt', hΩe,
    fun k V hV => ?_⟩
  let H : Opens X := ⟨{y | 0 < y 1}, isOpen_lt continuous_const (by fun_prop)⟩
  let Ω₂ : Opens X := ⟨ball 0 ρ ∩ {y | 0 < y 1}, isOpen_ball.inter H.isOpen⟩
  have hmem : ∀ y ∈ (Ω₂ : Set X), y ∈ ball (0 : X) ρ ∧ 0 < y 1 := fun y hy => hy
  have hΩ₂H : Ω₂ ≤ H := fun y hy => (hmem y hy).2
  have hΩ₂t : (Ω₂ : Set X) ⊆ e.target := fun y hy => hρt' (ball_subset_closedBall (hmem y hy).1)
  have hΩ₂Ω : MapsTo e.symm Ω₂ Ω := fun y hy => (hΩe _ (e.map_target (hΩ₂t hy))).2
    (by rw [e.right_inv (hΩ₂t hy)]; exact (hmem y hy).2)
  obtain ⟨L, c, hc, hLc⟩ := pde_bd_jbounds he hes (isCompact_closedBall (0 : X) ρ) hρt'
  have hd : DifferentiableOn ℝ e.symm Ω₂ := (hes.differentiableOn (by simp)).mono hΩ₂t
  have hinj : InjOn e.symm Ω₂ := e.symm.injOn.mono hΩ₂t
  have hL : ∀ y ∈ (Ω₂ : Set X), ‖fderiv ℝ e.symm y‖ ≤ L := fun y hy =>
    (hLc y (ball_subset_closedBall (hmem y hy).1)).1
  have hdet : ∀ y ∈ (Ω₂ : Set X), c ≤ |(fderiv ℝ e.symm y).det| := fun y hy =>
    (hLc y (ball_subset_closedBall (hmem y hy).1)).2
  have hmU : MapsTo e.symm e.target U := fun y hy => heU (e.map_target hy)
  obtain ⟨a, ha, hac, ⟨l, L', hell'⟩, haeq⟩ := pde_bd_acoef hell hA he hes heU hρ hρt
  have hF₂ : ContDiffOn ℝ ∞ (fun y => |(fderiv ℝ e.symm y).det| * F (e.symm y)) e.target :=
    (pde_bd_smooth he hes).1.mul (hF.comp hes hmU)
  have hb₂ : ContDiffOn ℝ ∞
      (fun y => |(fderiv ℝ e.symm y).det| • fderiv ℝ e (e.symm y) (β (e.symm y))) e.target :=
    (pde_bd_smooth he hes).1.smul ((pde_bd_smooth he hes).2.clm_apply (hβ.comp hes hmU))
  have hc₂ : ContDiffOn ℝ ∞ (fun y => |(fderiv ℝ e.symm y).det| * γ (e.symm y)) e.target :=
    (pde_bd_smooth he hes).1.mul (hγ.comp hes hmU)
  obtain ⟨f₂, hf₂⟩ := pde_bd_fdata (Ω₂ := Ω₂) (fun y hy => ball_subset_closedBall (hmem y hy).1)
    (isCompact_closedBall (0 : X) ρ) (hF₂.continuousOn.mono hρt') (hb₂.continuousOn.mono hρt')
    (hc₂.continuousOn.mono hρt')
    (TauCeti.W1p.compL e.symm (p := 2) (by norm_num) hd hinj hΩ₂Ω hL hc hdet
      (u : TauCeti.W1p (volume : Measure X) Ω 2))
  have hv := pde_bd_veq hsplit he hes hΩe hΩ₂t (fun y hy => (hmem y hy).2)
    (TauCeti.W1p.value_compL_ae e.symm (p := 2) (by norm_num) hd hinj hΩ₂Ω hL hc hdet _)
    (TauCeti.W1p.gradient_compL_ae e.symm (p := 2) (by norm_num) hd hinj hΩ₂Ω hL hc hdet _)
    ha hac (fun y hy => haeq y (ball_subset_closedBall (hmem y hy).1)) f₂ hf₂
  obtain ⟨W, hW⟩ := pde_bd_loc (H := H) rfl hΩ₂H rfl (hell' (H : Set X)) ha hac e.open_target
    hρt' hF₂ hb₂ hc₂ f₂ hf₂ hv (fun ζ hζ M hM hζM hgM hs hζρ => pde_bd_v0 rfl hΩ₂H hes hρt' hΩe
      hd hinj hΩ₂Ω hL hc hdet u.2 ζ hζ M hM hζM hgM hs hζρ) k (s := ρ / 2) (by positivity)
    (by linarith) V hV
  have hVΩ₂ : (V : Set X) ⊆ Ω₂ := by
    rw [hV]
    exact fun y hy => ⟨ball_subset_ball (by linarith) hy.1, hy.2⟩
  exact ⟨TauCeti.Wkp.lowerOrder k W, hW.trans (ae_restrict_of_ae_restrict_of_subset hVΩ₂
    (TauCeti.W1p.value_compL_ae e.symm (p := 2) (by norm_num) hd hinj hΩ₂Ω hL hc hdet _))⟩

/-- W-PDE1 P5 helper: the distance from `y` to its foot `(y₀, 0)` on the line `{y₁ = 0}`. -/
theorem pde_hx_dist (y : X) : dist y (WithLp.toLp 2 ![y 0, 0]) = |y 1| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp [Real.sqrt_sq_eq_abs]

/-- W-PDE1 P5 helper: a `C¹` function with compact support vanishing on `{y₁ = 0}` is bounded by
`L |y₁|`. -/
theorem pde_hx_lip_line {χ : X → ℝ} {L : ℝ≥0} (hL : LipschitzWith L χ)
    (h0 : ∀ y : X, y 1 = 0 → χ y = 0) (y : X) : |χ y| ≤ L * |y 1| := by
  have hy' : χ (WithLp.toLp 2 ![y 0, 0]) = 0 := h0 _ (by simp)
  have h := hL.dist_le_mul y (WithLp.toLp 2 ![y 0, 0])
  rw [Real.dist_eq, hy', sub_zero, pde_hx_dist] at h
  exact h

/-- W-PDE1 P5 helper (integration by parts up to the flat boundary; a rewrite on `X`, with normal
coordinate `y 1` and the half-disc `V`, of the private TauCeti theorem
`TauCeti.integral_fderiv_mul_eq_neg_of_halfSpace`, `Analysis/Sobolev/Trace/Reflection.lean`).
Let `u`, `g` be integrable with `∫ ∂_v φ · u = -∫ φ g` for the test functions `φ` of `V`. Then the
identity holds on the upper half-plane against every smooth compactly supported `χ` with support
in the disc, provided `v` is tangent to the boundary or `χ` vanishes on it. -/
theorem pde_hx_ibp {r : ℝ} {V : Opens X} (hV : (V : Set X) = ball 0 r ∩ {y | 0 < y 1})
    {u g : X → ℝ} (hu : Integrable u) (hg : Integrable g) {v : X}
    (hw : ∀ φ : X → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      ∫ y, fderiv ℝ φ y v * u y = -∫ y, φ y * g y)
    {χ : X → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχr : tsupport χ ⊆ ball 0 r)
    (hv : v 1 = 0 ∨ ∀ y : X, y 1 = 0 → χ y = 0) :
    ∫ y, {y : X | 0 < y 1}.indicator (fun y => fderiv ℝ χ y v * u y) y =
      -∫ y, {y : X | 0 < y 1}.indicator (fun y => χ y * g y) y := by
  set p1 : X →L[ℝ] ℝ := EuclideanSpace.proj (1 : Fin 2) with hp1
  have hc1 : ContDiff ℝ ∞ fun y : X => y 1 := p1.contDiff
  have hp1v : ∀ w : X, p1 w = w 1 := fun w => rfl
  -- the boundary cutoffs `η n` and the normal derivatives `D n` of them
  set η : ℕ → X → ℝ := fun n y => Real.smoothTransition (((n : ℝ) + 1) * y 1 - 1) with hη
  set D : ℕ → X → ℝ := fun n y =>
    deriv Real.smoothTransition (((n : ℝ) + 1) * y 1 - 1) * (((n : ℝ) + 1) * v 1) with hD
  have hηd : ∀ (n : ℕ) (y : X), HasFDerivAt (η n)
      (deriv Real.smoothTransition (((n : ℝ) + 1) * y 1 - 1) • (((n : ℝ) + 1) • p1)) y :=
    fun n y => ((p1.hasFDerivAt.const_mul ((n : ℝ) + 1)).sub_const 1).smoothTransition
  have hηs : ∀ n : ℕ, ContDiff ℝ ∞ (η n) := fun n =>
    (Real.smoothTransition.contDiff (n := ⊤)).comp ((contDiff_const.mul hc1).sub contDiff_const)
  have hχd : ∀ y, HasFDerivAt χ (fderiv ℝ χ y) y := fun y =>
    ((hχ.differentiable (by simp)) y).hasFDerivAt
  have hfd : ∀ (n : ℕ) (y : X),
      fderiv ℝ (fun y => η n y * χ y) y v = η n y * fderiv ℝ χ y v + χ y * D n y := by
    intro n y
    have h := ((hηd n y).mul (hχd y)).fderiv
    rw [show (fun y => η n y * χ y) = η n * χ from rfl, h]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, hp1v, hD]
  -- the cutoff test functions lie in `V`
  have hts : ∀ n : ℕ, tsupport (fun y => η n y * χ y) ⊆ V := by
    intro n y hy
    have h1 : tsupport (η n) ⊆ {y : X | 1 ≤ ((n : ℝ) + 1) * y 1} := by
      refine closure_minimal (fun y hy => ?_) (isClosed_le continuous_const
        (continuous_const.mul hc1.continuous))
      by_contra hn
      exact hy (Real.smoothTransition.zero_of_nonpos (by simp only [mem_ofPred_eq] at hn; linarith))
    have hy1 : 1 ≤ ((n : ℝ) + 1) * y 1 := h1 (tsupport_mul_subset_left hy)
    have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [SetLike.mem_coe, ← SetLike.mem_coe, hV]
    refine ⟨hχr (tsupport_mul_subset_right hy), ?_⟩
    show 0 < y 1
    by_contra hn
    push Not at hn
    nlinarith
  have hweak : ∀ n : ℕ, ∫ y, (η n y * fderiv ℝ χ y v + χ y * D n y) * u y =
      -∫ y, (η n y * χ y) * g y := by
    intro n
    rw [← hw _ ((hηs n).mul hχ) hχc.mul_left (hts n)]
    exact integral_congr_ae (Eventually.of_forall fun y => by simp only [hfd])
  -- bounds
  have hcf : Continuous fun y => fderiv ℝ χ y v :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨K1, hK1⟩ := hcf.bounded_above_of_compact_support (hχc.fderiv_apply (𝕜 := ℝ) v)
  obtain ⟨Kχ, hKχ⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  obtain ⟨B, hB⟩ := ((Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
    ).bounded_above_of_compact_support Real.smoothTransition.hasCompactSupport_deriv
  obtain ⟨L, hL⟩ := hχ.lipschitzWith_of_hasCompactSupport hχc (by simp)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hD0 : ∀ (n : ℕ) (y : X), ¬ 0 < y 1 → η n y = 0 ∧ D n y = 0 := by
    intro n y hy
    have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have ht : ((n : ℝ) + 1) * y 1 - 1 < 0 := by nlinarith
    exact ⟨Real.smoothTransition.zero_of_nonpos ht.le, by
      simp only [hD, Real.smoothTransition.deriv_of_neg ht, zero_mul]⟩
  have hD1 : ∀ y : X, 0 < y 1 → ∀ᶠ n : ℕ in atTop, η n y = 1 ∧ D n y = 0 := by
    intro y hy
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / y 1)
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
    have h2 : 2 < ((n : ℝ) + 1) * y 1 := by
      rw [div_lt_iff₀ hy] at hN
      nlinarith
    exact ⟨Real.smoothTransition.one_of_one_le (by linarith), by
      simp only [hD, Real.smoothTransition.deriv_of_one_lt (by linarith : 1 < ((n : ℝ) + 1) * y 1 - 1),
        zero_mul]⟩
  have hDb : ∀ (n : ℕ) (y : X), |χ y * D n y| ≤ 2 * L * B * |v 1| := by
    intro n y
    have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    set t := ((n : ℝ) + 1) * y 1 - 1 with ht
    rcases lt_or_ge t 0 with h | h
    · simp only [hD, ← ht, Real.smoothTransition.deriv_of_neg h, zero_mul, mul_zero, abs_zero]
      positivity
    rcases lt_or_ge 1 t with h' | h'
    · simp only [hD, ← ht, Real.smoothTransition.deriv_of_one_lt h', zero_mul, mul_zero, abs_zero]
      positivity
    have hy0 : 0 ≤ y 1 := by nlinarith
    rcases hv with hv | hv
    · simp only [hD, hv, mul_zero, abs_zero]
      positivity
    have hχy := pde_hx_lip_line hL hv y
    rw [abs_of_nonneg hy0] at hχy
    have hBt : |deriv Real.smoothTransition t| ≤ B := hB t
    simp only [hD, ← ht, abs_mul, abs_of_pos hn0]
    have hL0 : (0 : ℝ) ≤ L := L.2
    calc |χ y| * (|deriv Real.smoothTransition t| * (((n : ℝ) + 1) * |v 1|))
        ≤ (L * y 1) * (B * (((n : ℝ) + 1) * |v 1|)) := by gcongr
      _ = L * B * |v 1| * (((n : ℝ) + 1) * y 1) := by ring
      _ ≤ L * B * |v 1| * 2 := by gcongr; linarith
      _ = 2 * L * B * |v 1| := by ring
  -- measurability of the cutoffs
  have hcη : ∀ n : ℕ, Continuous (η n) := fun n => (hηs n).continuous
  have hcD : ∀ n : ℕ, Continuous (D n) := fun n =>
    (((Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).comp
      ((continuous_const.mul hc1.continuous).sub continuous_const)).mul continuous_const
  -- the left side converges
  have hlim1 : Tendsto (fun n : ℕ => ∫ y, (η n y * fderiv ℝ χ y v + χ y * D n y) * u y) atTop
      (𝓝 (∫ y, {y : X | 0 < y 1}.indicator (fun y => fderiv ℝ χ y v * u y) y)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => (K1 + 2 * L * B * |v 1|) * ‖u y‖)
      (fun n => (((hcη n).mul hcf).add (hχ.continuous.mul (hcD n))).aestronglyMeasurable.mul hu.1)
      (hu.norm.const_mul _) (fun n => Eventually.of_forall fun y => ?_)
      (Eventually.of_forall fun y => ?_)
    · rw [norm_mul]
      gcongr
      have hη1 : |η n y| ≤ 1 := by
        rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
        exact Real.smoothTransition.le_one _
      calc ‖η n y * fderiv ℝ χ y v + χ y * D n y‖ ≤ |η n y| * |fderiv ℝ χ y v| + |χ y * D n y| := by
            rw [Real.norm_eq_abs, ← abs_mul]
            exact abs_add_le _ _
        _ ≤ 1 * K1 + 2 * L * B * |v 1| := by
            gcongr
            · exact hK1 y
            · exact hDb n y
        _ = K1 + 2 * L * B * |v 1| := by ring
    · by_cases hy : 0 < y 1
      · rw [indicator_of_mem (show y ∈ {y : X | 0 < y 1} from hy)]
        exact tendsto_const_nhds.congr' ((hD1 y hy).mono fun n hn => by
          simp only [hn.1, hn.2]; ring)
      · rw [indicator_of_notMem (show y ∉ {y : X | 0 < y 1} from hy)]
        exact tendsto_const_nhds.congr' (Eventually.of_forall fun n => by
          simp only [(hD0 n y hy).1, (hD0 n y hy).2]; ring)
  -- the right side converges
  have hlim2 : Tendsto (fun n : ℕ => ∫ y, (η n y * χ y) * g y) atTop
      (𝓝 (∫ y, {y : X | 0 < y 1}.indicator (fun y => χ y * g y) y)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => Kχ * ‖g y‖)
      (fun n => ((hcη n).mul hχ.continuous).aestronglyMeasurable.mul hg.1)
      (hg.norm.const_mul _) (fun n => Eventually.of_forall fun y => ?_)
      (Eventually.of_forall fun y => ?_)
    · rw [norm_mul]
      gcongr
      rw [norm_mul]
      calc ‖η n y‖ * ‖χ y‖ ≤ 1 * Kχ := by
            gcongr
            · rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
              exact Real.smoothTransition.le_one _
            · exact hKχ y
        _ = Kχ := one_mul _
    · by_cases hy : 0 < y 1
      · rw [indicator_of_mem (show y ∈ {y : X | 0 < y 1} from hy)]
        exact tendsto_const_nhds.congr' ((hD1 y hy).mono fun n hn => by
          simp only [hn.1]; ring)
      · rw [indicator_of_notMem (show y ∉ {y : X | 0 < y 1} from hy)]
        exact tendsto_const_nhds.congr' (Eventually.of_forall fun n => by
          simp only [(hD0 n y hy).1]; ring)
  exact tendsto_nhds_unique hlim1 ((hlim2.neg).congr fun n => (hweak n).symm)


/-- W-PDE1 P5 helper: the normal scaling `T_σ z = (z₀, -σ z₁)` is a linear automorphism of `X`
with determinant `-σ`. -/
theorem pde_hx_T {σ : ℝ} (hσ : 0 < σ) :
    ∃ T : X ≃ₗ[ℝ] X, (∀ z : X, T z = WithLp.toLp 2 ![z 0, -(σ * z 1)]) ∧
      LinearMap.det (T : X →ₗ[ℝ] X) = -σ := by
  let T : X ≃ₗ[ℝ] X :=
    { toFun := fun z => WithLp.toLp 2 ![z 0, -(σ * z 1)]
      invFun := fun y => WithLp.toLp 2 ![y 0, -(y 1 / σ)]
      map_add' := fun a b => by
        ext i
        fin_cases i <;> simp
        ring
      map_smul' := fun c a => by
        ext i
        fin_cases i <;> simp
        ring
      left_inv := fun z => by
        ext i
        fin_cases i <;> simp
        field_simp
      right_inv := fun y => by
        ext i
        fin_cases i <;> simp
        field_simp }
  refine ⟨T, fun z => rfl, ?_⟩
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, T]

/-- W-PDE1 P5 helper (change of variables under `T_σ`): `∫ F = σ ∫ F ∘ T_σ`. -/
theorem pde_hx_cov {σ : ℝ} (hσ : 0 < σ) (F : X → ℝ) :
    ∫ y, F y = σ * ∫ z : X, F (WithLp.toLp 2 ![z 0, -(σ * z 1)]) := by
  obtain ⟨T, hT, hdet⟩ := pde_hx_T hσ
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure X))
    (f := (T : X →ₗ[ℝ] X)) (by rw [hdet]; linarith)
  have hemb : MeasurableEmbedding (T : X → X) :=
    T.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have h := hemb.integral_map (μ := (volume : Measure X)) F
  rw [show Measure.map (T : X → X) volume = Measure.map ((T : X →ₗ[ℝ] X) : X → X) volume from rfl,
    hmap, integral_smul_measure, hdet] at h
  simp only [hT] at h
  rw [← h, abs_inv, abs_neg, abs_of_pos hσ, ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hσ.ne', one_mul]

/-- W-PDE1 P5 helper: composing with `T_σ` preserves integrability. -/
theorem pde_hx_int_T {σ : ℝ} (hσ : 0 < σ) {B : X → ℝ} (hB : Integrable B) :
    Integrable fun z : X => B (WithLp.toLp 2 ![z 0, -(σ * z 1)]) := by
  obtain ⟨T, hT, hdet⟩ := pde_hx_T hσ
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure X))
    (f := (T : X →ₗ[ℝ] X)) (by rw [hdet]; linarith)
  have hemb : MeasurableEmbedding (T : X → X) :=
    T.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have h1 : Integrable B (Measure.map (T : X → X) volume) := by
    rw [show (T : X → X) = ((T : X →ₗ[ℝ] X) : X → X) from rfl, hmap]
    exact hB.smul_measure ENNReal.ofReal_ne_top
  have h2 := hemb.integrable_map_iff.1 h1
  simp only [Function.comp_def, hT] at h2
  exact h2

/-- W-PDE1 P5 helper: the line `{y₁ = 0}` is a null set. -/
theorem pde_hx_line_null : (volume : Measure X) {y : X | y 1 = 0} = 0 := by
  have h := Measure.addHaar_submodule (volume : Measure X)
    (LinearMap.ker (EuclideanSpace.proj (1 : Fin 2) : X →L[ℝ] ℝ).toLinearMap) (by
      intro htop
      have h1 : (EuclideanSpace.single (1 : Fin 2) (1 : ℝ) : X) ∈
          LinearMap.ker (EuclideanSpace.proj (1 : Fin 2) : X →L[ℝ] ℝ).toLinearMap := by
        rw [htop]; trivial
      simp at h1)
  exact h


/-- W-PDE1 P5 helper: the lower half-plane pulled back to the upper one by `T_σ`, with
`R_σ (T_σ z) = z`. -/
theorem pde_hx_low {σ : ℝ} (hσ : 0 < σ) (A B : X → ℝ) :
    ∫ y, {y : X | 0 < y 1}ᶜ.indicator (fun y => A y * B (WithLp.toLp 2 ![y 0, -(y 1 / σ)])) y =
      σ * ∫ z, {z : X | 0 < z 1}.indicator
        (fun z => A (WithLp.toLp 2 ![z 0, -(σ * z 1)]) * B z) z := by
  rw [pde_hx_cov hσ]
  congr 1
  refine integral_congr_ae ?_
  have hnull : ∀ᵐ z ∂(volume : Measure X), z 1 ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.1 pde_hx_line_null
  filter_upwards [hnull] with z hz
  have hRT : (WithLp.toLp 2 ![(WithLp.toLp 2 ![z 0, -(σ * z 1)] : X) 0,
      -((WithLp.toLp 2 ![z 0, -(σ * z 1)] : X) 1 / σ)] : X) = z := by
    ext i
    fin_cases i <;> simp
    field_simp
  by_cases h : 0 < z 1
  · have h' : ¬ 0 < (WithLp.toLp 2 ![z 0, -(σ * z 1)] : X) 1 := by
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
      nlinarith
    rw [indicator_of_mem (show (WithLp.toLp 2 ![z 0, -(σ * z 1)] : X) ∈ {y : X | 0 < y 1}ᶜ from h'),
      indicator_of_mem (show z ∈ {z : X | 0 < z 1} from h), hRT]
  · have h1 : z 1 < 0 := lt_of_le_of_ne (not_lt.1 h) hz
    have h' : 0 < (WithLp.toLp 2 ![z 0, -(σ * z 1)] : X) 1 := by
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
      nlinarith
    rw [indicator_of_notMem (show (WithLp.toLp 2 ![z 0, -(σ * z 1)] : X) ∉ {y : X | 0 < y 1}ᶜ from
      fun hh => hh h'), indicator_of_notMem (show z ∉ {z : X | 0 < z 1} from h)]

/-- W-PDE1 P5 helper: a bounded continuous factor with compact support times an integrable
function, restricted to a measurable set, is integrable. -/
theorem pde_hx_int_bdd {f u : X → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hu : Integrable u) {S : Set X} (hS : MeasurableSet S) :
    Integrable (S.indicator fun y => f y * u y) := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
  exact (hu.bdd_mul hf.aestronglyMeasurable (Eventually.of_forall hC)).indicator hS

/-- W-PDE1 P5 helper: composing with `R_σ y = (y₀, -y₁/σ)` preserves integrability. -/
theorem pde_hx_int_R {σ : ℝ} (hσ : 0 < σ) {B : X → ℝ} (hB : Integrable B) :
    Integrable fun y : X => B (WithLp.toLp 2 ![y 0, -(y 1 / σ)]) := by
  have h := pde_hx_int_T (inv_pos.2 hσ) hB
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [div_eq_inv_mul]

/-- W-PDE1 P5 helper (one reflected piece): for `σ ≥ 1` and `T_σ v = κ v`, the function equal to
`u` on the upper half-plane and to `u ∘ R_σ` below, `R_σ y = (y₀, -y₁/σ)`, satisfies the weak
derivative identity in direction `v` with derivative `g` above and `κ⁻¹ g ∘ R_σ` below, against
every test function supported in the disc; `v` tangential, or `κ = -σ` (normal direction). -/
theorem pde_hx_pair {r σ κ : ℝ} (hσ : 1 ≤ σ) (hκ : κ ≠ 0) {V : Opens X}
    (hV : (V : Set X) = ball 0 r ∩ {y | 0 < y 1}) {u g : X → ℝ} (hu : Integrable u)
    (hg : Integrable g) {v : X}
    (hw : ∀ φ : X → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      ∫ y, fderiv ℝ φ y v * u y = -∫ y, φ y * g y)
    (hTv : (WithLp.toLp 2 ![v 0, -(σ * v 1)] : X) = κ • v) (hv : v 1 = 0 ∨ κ = -σ)
    {φ : X → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφr : tsupport φ ⊆ ball 0 r) :
    ∫ y, fderiv ℝ φ y v * (if 0 < y 1 then u y else u (WithLp.toLp 2 ![y 0, -(y 1 / σ)])) =
      -∫ y, φ y * (if 0 < y 1 then g y else κ⁻¹ * g (WithLp.toLp 2 ![y 0, -(y 1 / σ)])) := by
  have hσ0 : 0 < σ := by linarith
  have hc1 : Continuous fun y : X => y 1 :=
    (EuclideanSpace.proj (1 : Fin 2) : X →L[ℝ] ℝ).continuous
  have hPm : MeasurableSet {y : X | 0 < y 1} := (isOpen_lt continuous_const hc1).measurableSet
  have hPcm : MeasurableSet {y : X | 0 < y 1}ᶜ := hPm.compl
  have hcpt : ∀ f : X → ℝ, tsupport f ⊆ ball 0 r → HasCompactSupport f := fun f hf =>
    (isCompact_closedBall (0 : X) r).of_isClosed_subset (isClosed_tsupport f)
      (hf.trans ball_subset_closedBall)
  have hφc := hcpt φ hφr
  obtain ⟨T, hT, -⟩ := pde_hx_T hσ0
  set Tc : X →L[ℝ] X := LinearMap.toContinuousLinearMap (T : X →ₗ[ℝ] X) with hTc
  have hTcv : ∀ z, Tc z = WithLp.toLp 2 ![z 0, -(σ * z 1)] := fun z => hT z
  -- `ψ = φ ∘ T_σ`
  set ψ : X → ℝ := fun z => φ (WithLp.toLp 2 ![z 0, -(σ * z 1)]) with hψ
  have hψe : ψ = φ ∘ Tc := funext fun z => by simp only [hψ, Function.comp_apply, hTcv]
  have hψs : ContDiff ℝ ∞ ψ := by
    rw [hψe]
    exact hφ.comp Tc.contDiff
  have hnorm : ∀ z : X, ‖z‖ ≤ ‖(WithLp.toLp 2 ![z 0, -(σ * z 1)] : X)‖ := by
    intro z
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_two]
    apply Real.sqrt_le_sqrt
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Real.norm_eq_abs, sq_abs]
    have hσ2 : 1 ≤ σ * σ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hσ2 (sq_nonneg (z 1))]
  have hψr : tsupport ψ ⊆ ball 0 r := by
    have hsub : tsupport ψ ⊆ (fun z : X => (WithLp.toLp 2 ![z 0, -(σ * z 1)] : X)) ⁻¹' tsupport φ :=
      closure_minimal (fun z hz => subset_tsupport φ hz)
        ((isClosed_tsupport φ).preimage (Tc.continuous.congr hTcv))
    intro z hz
    have h1 := hφr (hsub hz)
    rw [mem_ball_zero_iff] at h1 ⊢
    exact lt_of_le_of_lt (hnorm z) h1
  have hψc := hcpt ψ hψr
  have hψd : ∀ z, fderiv ℝ ψ z v = κ * fderiv ℝ φ (WithLp.toLp 2 ![z 0, -(σ * z 1)]) v := by
    intro z
    have h := (((hφ.differentiable (by simp)) (Tc z)).hasFDerivAt.comp z Tc.hasFDerivAt).fderiv
    rw [← hψe] at h
    rw [h, ContinuousLinearMap.comp_apply, hTcv, hTcv, hTv, map_smul, smul_eq_mul]
  have hTline : ∀ z : X, z 1 = 0 → (WithLp.toLp 2 ![z 0, -(σ * z 1)] : X) = z := by
    intro z hz
    ext i
    fin_cases i <;> simp [hz]
  -- `χ = φ + σ κ⁻¹ ψ`
  set χ : X → ℝ := fun z => φ z + σ * κ⁻¹ * ψ z with hχ
  have hχs : ContDiff ℝ ∞ χ := hφ.add (contDiff_const.mul hψs)
  have hχr : tsupport χ ⊆ ball 0 r := by
    refine (tsupport_add φ fun z => σ * κ⁻¹ * ψ z).trans (union_subset hφr ?_)
    exact (tsupport_mul_subset_right).trans hψr
  have hχd : ∀ z, fderiv ℝ χ z v = fderiv ℝ φ z v + σ * κ⁻¹ * fderiv ℝ ψ z v := by
    intro z
    have h := (((hφ.differentiable (by simp)) z).hasFDerivAt.add
      (((hψs.differentiable (by simp)) z).hasFDerivAt.const_mul (σ * κ⁻¹))).fderiv
    rw [show (φ + fun y => σ * κ⁻¹ * ψ y) = χ from rfl] at h
    rw [h]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  have hv' : v 1 = 0 ∨ ∀ z : X, z 1 = 0 → χ z = 0 := by
    rcases hv with hv | hv
    · exact Or.inl hv
    · refine Or.inr fun z hz => ?_
      simp only [hχ, hψ, hTline z hz, hv]
      field_simp
      ring
  have hibp := pde_hx_ibp hV hu hg hw hχs (hcpt χ hχr) hχr hv'
  -- integrability of the pieces
  have hcfφ : Continuous fun y => fderiv ℝ φ y v :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcfψ : Continuous fun y => fderiv ℝ ψ y v :=
    (hψs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsφ : HasCompactSupport fun y => fderiv ℝ φ y v := hφc.fderiv_apply (𝕜 := ℝ) v
  have hsψ : HasCompactSupport fun y => fderiv ℝ ψ y v := hψc.fderiv_apply (𝕜 := ℝ) v
  have iA := pde_hx_int_bdd hcfφ hsφ hu hPm
  have iB := pde_hx_int_bdd hcfψ hsψ hu hPm
  have iC := pde_hx_int_bdd hφ.continuous hφc hg hPm
  have iD := pde_hx_int_bdd hψs.continuous hψc hg hPm
  have iL1 := pde_hx_int_bdd hcfφ hsφ (pde_hx_int_R hσ0 hu) hPcm
  have iL2 := pde_hx_int_bdd hφ.continuous hφc ((pde_hx_int_R hσ0 hg).const_mul κ⁻¹) hPcm
  -- split the two sides into upper and lower parts
  have hsplit : ∀ A a b : X → ℝ, (fun y => A y * (if 0 < y 1 then a y else b y)) =
      fun y => {y : X | 0 < y 1}.indicator (fun y => A y * a y) y +
        {y : X | 0 < y 1}ᶜ.indicator (fun y => A y * b y) y := by
    intro A a b
    funext y
    by_cases h : 0 < y 1 <;> simp [h]
  have hL : ∫ y, fderiv ℝ φ y v * (if 0 < y 1 then u y else u (WithLp.toLp 2 ![y 0, -(y 1 / σ)])) =
      (∫ y, {y : X | 0 < y 1}.indicator (fun y => fderiv ℝ φ y v * u y) y) +
        σ * κ⁻¹ * ∫ y, {y : X | 0 < y 1}.indicator (fun y => fderiv ℝ ψ y v * u y) y := by
    have e1 := hsplit (fun y => fderiv ℝ φ y v) u (fun y => u (WithLp.toLp 2 ![y 0, -(y 1 / σ)]))
    beta_reduce at e1
    have hlow := pde_hx_low hσ0 (fun y => fderiv ℝ φ y v) u
    beta_reduce at hlow
    rw [e1, integral_add iA iL1, hlow, mul_assoc]
    congr 2
    rw [← integral_const_mul]
    congr 1
    funext z
    by_cases h : 0 < z 1
    · simp only [indicator_of_mem (show z ∈ {z : X | 0 < z 1} from h), hψd]
      field_simp
    · simp only [indicator_of_notMem (show z ∉ {z : X | 0 < z 1} from h), mul_zero]
  have hR : ∫ y, φ y * (if 0 < y 1 then g y else κ⁻¹ * g (WithLp.toLp 2 ![y 0, -(y 1 / σ)])) =
      (∫ y, {y : X | 0 < y 1}.indicator (fun y => φ y * g y) y) +
        σ * κ⁻¹ * ∫ y, {y : X | 0 < y 1}.indicator (fun y => ψ y * g y) y := by
    have e2 := hsplit φ g (fun y => κ⁻¹ * g (WithLp.toLp 2 ![y 0, -(y 1 / σ)]))
    beta_reduce at e2
    have hlow := pde_hx_low hσ0 φ (fun w => κ⁻¹ * g w)
    beta_reduce at hlow
    rw [e2, integral_add iC iL2, hlow, mul_assoc]
    congr 2
    rw [← integral_const_mul]
    congr 1
    funext z
    by_cases h : 0 < z 1
    · simp only [indicator_of_mem (show z ∈ {z : X | 0 < z 1} from h), hψ]
      ring
    · simp only [indicator_of_notMem (show z ∉ {z : X | 0 < z 1} from h), mul_zero]
  have hIL : ∫ y, {y : X | 0 < y 1}.indicator (fun y => fderiv ℝ χ y v * u y) y =
      (∫ y, {y : X | 0 < y 1}.indicator (fun y => fderiv ℝ φ y v * u y) y) +
        σ * κ⁻¹ * ∫ y, {y : X | 0 < y 1}.indicator (fun y => fderiv ℝ ψ y v * u y) y := by
    rw [← integral_const_mul, ← integral_add iA (iB.const_mul _)]
    congr 1
    funext z
    by_cases h : 0 < z 1
    · simp only [indicator_of_mem (show z ∈ {z : X | 0 < z 1} from h), hχd]
      ring
    · simp only [indicator_of_notMem (show z ∉ {z : X | 0 < z 1} from h), mul_zero, add_zero]
  have hIR : ∫ y, {y : X | 0 < y 1}.indicator (fun y => χ y * g y) y =
      (∫ y, {y : X | 0 < y 1}.indicator (fun y => φ y * g y) y) +
        σ * κ⁻¹ * ∫ y, {y : X | 0 < y 1}.indicator (fun y => ψ y * g y) y := by
    rw [← integral_const_mul, ← integral_add iC (iD.const_mul _)]
    congr 1
    funext z
    by_cases h : 0 < z 1
    · simp only [indicator_of_mem (show z ∈ {z : X | 0 < z 1} from h), hχ]
      ring
    · simp only [indicator_of_notMem (show z ∉ {z : X | 0 < z 1} from h), mul_zero, add_zero]
  rw [hL, hR]
  rw [hIL, hIR] at hibp
  linarith


/-- W-PDE1 P5 helper: a function equal to an integrable `a` on the upper half-plane and to an
integrable `b` below is integrable. -/
theorem pde_hx_int_ite {a b : X → ℝ} (ha : Integrable a) (hb : Integrable b) :
    Integrable fun y : X => if 0 < y 1 then a y else b y := by
  have hc1 : Continuous fun y : X => y 1 :=
    (EuclideanSpace.proj (1 : Fin 2) : X →L[ℝ] ℝ).continuous
  have hPm : MeasurableSet {y : X | 0 < y 1} := (isOpen_lt continuous_const hc1).measurableSet
  refine ((ha.indicator hPm).add (hb.indicator hPm.compl)).congr (Eventually.of_forall fun y => ?_)
  by_cases h : 0 < y 1 <;> simp [h]

/-- W-PDE1 P5 helper (sum of the reflected pieces): with `∑_{j<M} c j = 1` and
`T_{j+1} v = k j • v`, the extension `E_c u` satisfies the weak derivative identity in direction
`v`, with derivative `g` above and `∑_j c j (k j)⁻¹ g ∘ R_{j+1}` below, against every test
function supported in the disc. -/
theorem pde_hx_sum {r : ℝ} {V : Opens X} (hV : (V : Set X) = ball 0 r ∩ {y | 0 < y 1})
    {u g : X → ℝ} (hu : Integrable u) (hg : Integrable g) {v : X}
    (hw : ∀ φ : X → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      ∫ y, fderiv ℝ φ y v * u y = -∫ y, φ y * g y)
    (M : ℕ) (c : ℕ → ℝ) (hc : ∑ j ∈ Finset.range M, c j = 1) (k : ℕ → ℝ) (hk0 : ∀ j, k j ≠ 0)
    (hk : ∀ j : ℕ, (WithLp.toLp 2 ![v 0, -(((j : ℝ) + 1) * v 1)] : X) = k j • v)
    (hkv : ∀ j : ℕ, v 1 = 0 ∨ k j = -((j : ℝ) + 1))
    {φ : X → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφr : tsupport φ ⊆ ball 0 r) :
    ∫ y, fderiv ℝ φ y v * (if 0 < y 1 then u y else
        ∑ j ∈ Finset.range M, c j * u (WithLp.toLp 2 ![y 0, -(y 1 / (j + 1))])) =
      -∫ y, φ y * (if 0 < y 1 then g y else
        ∑ j ∈ Finset.range M, c j * ((k j)⁻¹ * g (WithLp.toLp 2 ![y 0, -(y 1 / (j + 1))]))) := by
  have hφc : HasCompactSupport φ :=
    (isCompact_closedBall (0 : X) r).of_isClosed_subset (isClosed_tsupport φ)
      (hφr.trans ball_subset_closedBall)
  have hσ : ∀ j : ℕ, (0 : ℝ) < (j : ℝ) + 1 := fun j => by positivity
  have hpair := fun j : ℕ => pde_hx_pair (σ := (j : ℝ) + 1) (κ := k j)
    (by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith) (hk0 j) hV hu hg hw (hk j) (hkv j)
    hφ hφr
  have hcf : Continuous fun y => fderiv ℝ φ y v :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨C₁, hC₁⟩ := hcf.bounded_above_of_compact_support (hφc.fderiv_apply (𝕜 := ℝ) v)
  obtain ⟨C₂, hC₂⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have iP : ∀ j : ℕ, Integrable fun y => fderiv ℝ φ y v *
      (if 0 < y 1 then u y else u (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))])) := fun j =>
    (pde_hx_int_ite hu (pde_hx_int_R (hσ j) hu)).bdd_mul hcf.aestronglyMeasurable
      (Eventually.of_forall hC₁)
  have iQ : ∀ j : ℕ, Integrable fun y => φ y *
      (if 0 < y 1 then g y else (k j)⁻¹ * g (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))])) :=
    fun j => (pde_hx_int_ite hg ((pde_hx_int_R (hσ j) hg).const_mul _)).bdd_mul
      hφ.continuous.aestronglyMeasurable (Eventually.of_forall hC₂)
  have e1 : (fun y => fderiv ℝ φ y v * (if 0 < y 1 then u y else
        ∑ j ∈ Finset.range M, c j * u (WithLp.toLp 2 ![y 0, -(y 1 / (j + 1))]))) =
      fun y => ∑ j ∈ Finset.range M, c j * (fderiv ℝ φ y v *
        (if 0 < y 1 then u y else u (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))]))) := by
    funext y
    by_cases h : 0 < y 1
    · simp only [h, ↓reduceIte]
      rw [← Finset.sum_mul, hc, one_mul]
    · simp only [h, ↓reduceIte]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : (fun y => φ y * (if 0 < y 1 then g y else
        ∑ j ∈ Finset.range M, c j * ((k j)⁻¹ * g (WithLp.toLp 2 ![y 0, -(y 1 / (j + 1))])))) =
      fun y => ∑ j ∈ Finset.range M, c j * (φ y *
        (if 0 < y 1 then g y else (k j)⁻¹ * g (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))]))) := by
    funext y
    by_cases h : 0 < y 1
    · simp only [h, ↓reduceIte]
      rw [← Finset.sum_mul, hc, one_mul]
    · simp only [h, ↓reduceIte]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, integral_finsetSum _ fun j _ => (iP j).const_mul (c j),
    integral_finsetSum _ fun j _ => (iQ j).const_mul (c j), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_const_mul, hpair j, mul_neg]

/-- W-PDE1 P5 helper (one direction of the gluing): if `u ∈ L²(V)` has the weak derivative
`g ∈ L²(V)` in direction `v`, with `T_{j+1} v = k j • v` (`v` tangential or `k j = -(j+1)`), and
`∑_{j<M} c j = 1`, then `E_c u` has on the disc the weak derivative equal to `g` above and to
`∑_j c j (k j)⁻¹ g ∘ R_{j+1}` below. -/
theorem pde_hx_dir {r : ℝ} {V W : Opens X}
    (hV : (V : Set X) = ball 0 r ∩ {y | 0 < y 1}) (hW : (W : Set X) = ball 0 r)
    (M : ℕ) (c : ℕ → ℝ) (hc : ∑ j ∈ Finset.range M, c j = 1) {u g : X → ℝ}
    (hu : MemLp u 2 ((volume : Measure X).restrict V))
    (hg : MemLp g 2 ((volume : Measure X).restrict V)) {v : X}
    (h : TauCeti.HasWeakLineDerivOn (volume : Measure X) V u g v)
    (k : ℕ → ℝ) (hk0 : ∀ j, k j ≠ 0)
    (hk : ∀ j : ℕ, (WithLp.toLp 2 ![v 0, -(((j : ℝ) + 1) * v 1)] : X) = k j • v)
    (hkv : ∀ j : ℕ, v 1 = 0 ∨ k j = -((j : ℝ) + 1)) :
    TauCeti.HasWeakLineDerivOn (volume : Measure X) W
      (fun y => if 0 < y 1 then u y else
        ∑ j ∈ Finset.range M, c j * u (WithLp.toLp 2 ![y 0, -(y 1 / (j + 1))]))
      (fun y => if 0 < y 1 then g y else
        ∑ j ∈ Finset.range M, c j * ((k j)⁻¹ * g (WithLp.toLp 2 ![y 0, -(y 1 / (j + 1))])))
      v := by
  have hVm : MeasurableSet (V : Set X) := V.isOpen.measurableSet
  have hWm : MeasurableSet (W : Set X) := W.isOpen.measurableSet
  have hVb : (V : Set X) ⊆ ball 0 r := by rw [hV]; exact inter_subset_left
  have hfin : (volume : Measure X) V ≠ ⊤ :=
    ((measure_mono hVb).trans_lt measure_ball_lt_top).ne
  have : IsFiniteMeasure ((volume : Measure X).restrict V) := isFiniteMeasure_restrict.2 hfin
  have iu : Integrable ((V : Set X).indicator u) :=
    (show IntegrableOn u V volume from hu.integrable one_le_two).integrable_indicator hVm
  have ig : Integrable ((V : Set X).indicator g) :=
    (show IntegrableOn g V volume from hg.integrable one_le_two).integrable_indicator hVm
  have hσ : ∀ j : ℕ, (0 : ℝ) < (j : ℝ) + 1 := fun j => by positivity
  have hφ0 : ∀ φ : X → ℝ, ∀ y, y ∉ tsupport φ → φ y = 0 ∧ fderiv ℝ φ y = 0 := fun φ y hy =>
    ⟨image_eq_zero_of_notMem_tsupport hy,
      Function.notMem_support.1 fun h' => hy (support_fderiv_subset ℝ h')⟩
  have hld : ∀ φ : X → ℝ, ContDiff ℝ ∞ φ → ∀ y, lineDeriv ℝ φ y v = fderiv ℝ φ y v :=
    fun φ hφ y => ((hφ.differentiable (by simp)) y).lineDeriv_eq_fderiv
  -- the weak identity for the extensions by zero of `u`, `g`
  have hw : ∀ φ : X → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      ∫ y, fderiv ℝ φ y v * (V : Set X).indicator u y =
        -∫ y, φ y * (V : Set X).indicator g y := by
    intro φ hφ hφc hφs
    have h' := (TauCeti.hasWeakLineDerivOn_iff h.locallyIntegrableOn
      h.locallyIntegrableOn_deriv).1 h φ hφ hφc hφs
    have ea : (fun y => fderiv ℝ φ y v * (V : Set X).indicator u y) =
        fun y => lineDeriv ℝ φ y v • u y := by
      funext y
      rw [hld φ hφ y, smul_eq_mul]
      by_cases hy : y ∈ (V : Set X)
      · rw [indicator_of_mem hy]
      · rw [indicator_of_notMem hy, (hφ0 φ y fun h'' => hy (hφs h'')).2]
        simp
    have eb : (fun y => φ y * (V : Set X).indicator g y) = fun y => φ y • g y := by
      funext y
      rw [smul_eq_mul]
      by_cases hy : y ∈ (V : Set X)
      · rw [indicator_of_mem hy]
      · rw [indicator_of_notMem hy, (hφ0 φ y fun h'' => hy (hφs h'')).1]
        simp
    rw [ea, eb, h']
  -- the reflected points of the lower half-disc lie in `V`
  have hRV : ∀ y : X, y ∈ ball (0 : X) r → y 1 < 0 → ∀ j : ℕ,
      (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))] : X) ∈ (V : Set X) := by
    intro y hy h1 j
    rw [hV]
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff] at hy ⊢
      refine lt_of_le_of_lt ?_ hy
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_two]
      apply Real.sqrt_le_sqrt
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
      have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
      rw [neg_sq, div_pow]
      have : y 1 ^ 2 / ((j : ℝ) + 1) ^ 2 ≤ y 1 ^ 2 := div_le_self (sq_nonneg _) (one_le_pow₀ hj)
      linarith
    · show 0 < (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))] : X) 1
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have : y 1 / ((j : ℝ) + 1) < 0 := div_neg_of_neg_of_pos h1 (hσ j)
      linarith
  -- on the disc off the line, the extension of `1_V f` is the extension of `f`
  have hE : ∀ (f : X → ℝ) (F : ℕ → ℝ → ℝ) (y : X), y ∈ ball (0 : X) r → y 1 ≠ 0 →
      (if 0 < y 1 then (V : Set X).indicator f y else ∑ j ∈ Finset.range M,
          F j ((V : Set X).indicator f (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))]))) =
        (if 0 < y 1 then f y else ∑ j ∈ Finset.range M,
          F j (f (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))]))) := by
    intro f F y hy h1
    by_cases hp : 0 < y 1
    · have hyV : y ∈ (V : Set X) := by rw [hV]; exact ⟨hy, hp⟩
      simp only [hp, ↓reduceIte, indicator_of_mem hyV]
    · have hneg : y 1 < 0 := lt_of_le_of_ne (not_lt.1 hp) h1
      simp only [hp, ↓reduceIte]
      exact Finset.sum_congr rfl fun j _ => by rw [indicator_of_mem (hRV y hy hneg j)]
  have hnull : ∀ᵐ y ∂(volume : Measure X), y 1 ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.1 pde_hx_line_null
  have hIu : Integrable fun y : X => if 0 < y 1 then (V : Set X).indicator u y else
      ∑ j ∈ Finset.range M,
        c j * (V : Set X).indicator u (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))]) :=
    pde_hx_int_ite iu (integrable_finsetSum _ fun j _ => (pde_hx_int_R (hσ j) iu).const_mul (c j))
  have hIg : Integrable fun y : X => if 0 < y 1 then (V : Set X).indicator g y else
      ∑ j ∈ Finset.range M, c j * ((k j)⁻¹ *
        (V : Set X).indicator g (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))])) :=
    pde_hx_int_ite ig (integrable_finsetSum _ fun j _ =>
      ((pde_hx_int_R (hσ j) ig).const_mul (k j)⁻¹).const_mul (c j))
  have hEu : ∀ y : X, y ∈ ball (0 : X) r → y 1 ≠ 0 →
      (if 0 < y 1 then (V : Set X).indicator u y else ∑ j ∈ Finset.range M,
          c j * (V : Set X).indicator u (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))])) =
        (if 0 < y 1 then u y else ∑ j ∈ Finset.range M,
          c j * u (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))])) :=
    fun y hy h1 => hE u (fun j t => c j * t) y hy h1
  have hEg : ∀ y : X, y ∈ ball (0 : X) r → y 1 ≠ 0 →
      (if 0 < y 1 then (V : Set X).indicator g y else ∑ j ∈ Finset.range M,
          c j * ((k j)⁻¹ * (V : Set X).indicator g (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))]))) =
        (if 0 < y 1 then g y else ∑ j ∈ Finset.range M,
          c j * ((k j)⁻¹ * g (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))]))) :=
    fun y hy h1 => hE g (fun j t => c j * ((k j)⁻¹ * t)) y hy h1
  refine (TauCeti.hasWeakLineDerivOn_iff ?_ ?_).2 fun φ hφ hφc hφs => ?_
  · refine (hIu.locallyIntegrable.locallyIntegrableOn _).congr ?_
    refine (ae_restrict_iff' hWm).2 (hnull.mono fun y h1 hyW => ?_)
    exact hEu y (by rw [← hW]; exact hyW) h1
  · refine (hIg.locallyIntegrable.locallyIntegrableOn _).congr ?_
    refine (ae_restrict_iff' hWm).2 (hnull.mono fun y h1 hyW => ?_)
    exact hEg y (by rw [← hW]; exact hyW) h1
  · have hφr : tsupport φ ⊆ ball 0 r := by rw [← hW]; exact hφs
    have hs := pde_hx_sum hV iu ig hw M c hc k hk0 hk hkv hφ hφr
    have ea : (fun y => lineDeriv ℝ φ y v • (if 0 < y 1 then u y else ∑ j ∈ Finset.range M,
          c j * u (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))]))) =ᵐ[volume]
        fun y => fderiv ℝ φ y v * (if 0 < y 1 then (V : Set X).indicator u y else
          ∑ j ∈ Finset.range M,
            c j * (V : Set X).indicator u (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))])) := by
      filter_upwards [hnull] with y h1
      rw [hld φ hφ y, smul_eq_mul]
      by_cases hy : y ∈ ball (0 : X) r
      · rw [hEu y hy h1]
      · rw [(hφ0 φ y fun h'' => hy (hφr h'')).2]
        simp
    have eb : (fun y => φ y * (if 0 < y 1 then (V : Set X).indicator g y else
          ∑ j ∈ Finset.range M, c j * ((k j)⁻¹ *
            (V : Set X).indicator g (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))])))) =ᵐ[volume]
        fun y => φ y • (if 0 < y 1 then g y else ∑ j ∈ Finset.range M,
          c j * ((k j)⁻¹ * g (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))]))) := by
      filter_upwards [hnull] with y h1
      rw [smul_eq_mul]
      by_cases hy : y ∈ ball (0 : X) r
      · rw [hEg y hy h1]
      · rw [(hφ0 φ y fun h'' => hy (hφr h'')).1]
        simp
    rw [integral_congr_ae ea, hs, integral_congr_ae eb]

/-- W-PDE1 P5 (one-step gluing, the hard core): if `∑_{j<M} c j = 1` and `u ∈ W^{1,2}` of the
half-disc `V`, with weak derivatives `g₀`, `g₁` in the directions `e₀`, `e₁`, then the extension
`E_c u` to the disc `W` has weak derivatives `E_c g₀` in direction `e₀` and `E_{c'} g₁` in
direction `e₁`, where `c' j = -(c j / (j + 1))`. -/
theorem pde_hx_glue {r : ℝ} (hr : 0 < r) {V W : Opens X}
    (hV : (V : Set X) = ball 0 r ∩ {y | 0 < y 1}) (hW : (W : Set X) = ball 0 r)
    (M : ℕ) (c : ℕ → ℝ) (hc : ∑ j ∈ Finset.range M, c j = 1) {u g₀ g₁ : X → ℝ}
    (hu : MemLp u 2 ((volume : Measure X).restrict V))
    (hg₀ : MemLp g₀ 2 ((volume : Measure X).restrict V))
    (hg₁ : MemLp g₁ 2 ((volume : Measure X).restrict V))
    (h₀ : TauCeti.HasWeakLineDerivOn (volume : Measure X) V u g₀ (EuclideanSpace.basisFun (Fin 2) ℝ 0))
    (h₁ : TauCeti.HasWeakLineDerivOn (volume : Measure X) V u g₁ (EuclideanSpace.basisFun (Fin 2) ℝ 1)) :
    TauCeti.HasWeakLineDerivOn (volume : Measure X) W
        (fun y => if 0 < y 1 then u y else
          ∑ j ∈ Finset.range M, c j * u (WithLp.toLp 2 ![y 0, -(y 1 / (j + 1))]))
        (fun y => if 0 < y 1 then g₀ y else
          ∑ j ∈ Finset.range M, c j * g₀ (WithLp.toLp 2 ![y 0, -(y 1 / (j + 1))]))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) ∧
      TauCeti.HasWeakLineDerivOn (volume : Measure X) W
        (fun y => if 0 < y 1 then u y else
          ∑ j ∈ Finset.range M, c j * u (WithLp.toLp 2 ![y 0, -(y 1 / (j + 1))]))
        (fun y => if 0 < y 1 then g₁ y else
          ∑ j ∈ Finset.range M, -(c j / (j + 1)) * g₁ (WithLp.toLp 2 ![y 0, -(y 1 / (j + 1))]))
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) := by
  -- `hr` is not needed: for `r ≤ 0` the sets `V`, `W` are empty and the statement holds as well.
  have _h := hr
  refine ⟨?_, ?_⟩
  · have h := pde_hx_dir hV hW M c hc hu hg₀ h₀ (fun _ => 1) (fun _ => one_ne_zero)
      (fun j => by ext i; fin_cases i <;> simp) (fun j => Or.inl (by simp))
    have e : (fun y : X => if 0 < y 1 then g₀ y else
        ∑ j ∈ Finset.range M, c j * g₀ (WithLp.toLp 2 ![y 0, -(y 1 / (j + 1))])) =
        fun y => if 0 < y 1 then g₀ y else
          ∑ j ∈ Finset.range M, c j * ((1 : ℝ)⁻¹ * g₀ (WithLp.toLp 2 ![y 0, -(y 1 / (j + 1))])) := by
      simp only [inv_one, one_mul]
    rw [e]
    exact h
  · have h := pde_hx_dir hV hW M c hc hu hg₁ h₁ (fun j => -((j : ℝ) + 1))
      (fun j => by have : (0 : ℝ) < (j : ℝ) + 1 := by positivity
                   exact neg_ne_zero.2 this.ne')
      (fun j => by ext i; fin_cases i <;> simp) (fun j => Or.inr rfl)
    have e : (fun y : X => if 0 < y 1 then g₁ y else
        ∑ j ∈ Finset.range M, -(c j / (j + 1)) * g₁ (WithLp.toLp 2 ![y 0, -(y 1 / (j + 1))])) =
        fun y => if 0 < y 1 then g₁ y else
          ∑ j ∈ Finset.range M,
            c j * ((-((j : ℝ) + 1))⁻¹ * g₁ (WithLp.toLp 2 ![y 0, -(y 1 / (j + 1))])) := by
      funext y
      by_cases hp : 0 < y 1
      · simp only [hp, ↓reduceIte]
      · simp only [hp, ↓reduceIte]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [inv_neg, div_eq_mul_inv]
        ring
    rw [e]
    exact h


/-- W-PDE1 P5 helper: on the disc off the line `{y₁ = 0}`, the extension (with any weights `F`) of
`1_V f` is the extension of `f`; the reflected points of the lower half-disc lie in `V`. -/
theorem pde_hx_ext_ind {r : ℝ} {V : Opens X} (hV : (V : Set X) = ball 0 r ∩ {y | 0 < y 1})
    (M : ℕ) (F : ℕ → ℝ → ℝ) (f : X → ℝ) {y : X} (hy : y ∈ ball (0 : X) r) (h1 : y 1 ≠ 0) :
    (if 0 < y 1 then (V : Set X).indicator f y else ∑ j ∈ Finset.range M,
        F j ((V : Set X).indicator f (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))]))) =
      (if 0 < y 1 then f y else ∑ j ∈ Finset.range M,
        F j (f (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))]))) := by
  by_cases hp : 0 < y 1
  · have hyV : y ∈ (V : Set X) := by rw [hV]; exact ⟨hy, hp⟩
    simp only [hp, ↓reduceIte, indicator_of_mem hyV]
  · have hneg : y 1 < 0 := lt_of_le_of_ne (not_lt.1 hp) h1
    simp only [hp, ↓reduceIte]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
    have hRV : (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))] : X) ∈ (V : Set X) := by
      rw [hV]
      refine ⟨?_, ?_⟩
      · rw [mem_ball_zero_iff] at hy ⊢
        refine lt_of_le_of_lt ?_ hy
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_two]
        apply Real.sqrt_le_sqrt
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
        rw [neg_sq, div_pow]
        have : y 1 ^ 2 / ((j : ℝ) + 1) ^ 2 ≤ y 1 ^ 2 := div_le_self (sq_nonneg _) (one_le_pow₀ hj)
        linarith
      · show 0 < (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))] : X) 1
        simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
        have : y 1 / ((j : ℝ) + 1) < 0 := div_neg_of_neg_of_pos hneg (by linarith)
        linarith
    rw [indicator_of_mem hRV]

/-- W-PDE1 P5 helper: composing with `R_σ y = (y₀, -y₁/σ)` preserves `L²`. -/
theorem pde_hx_memLp_R {σ : ℝ} (hσ : 0 < σ) {B : X → ℝ} (hB : MemLp B 2 (volume : Measure X)) :
    MemLp (fun y : X => B (WithLp.toLp 2 ![y 0, -(y 1 / σ)])) 2 (volume : Measure X) := by
  obtain ⟨T, hT, hdet⟩ := pde_hx_T (inv_pos.2 hσ)
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure X))
    (f := (T : X →ₗ[ℝ] X)) (by rw [hdet]; exact neg_ne_zero.2 (inv_pos.2 hσ).ne')
  have hemb : MeasurableEmbedding (T : X → X) :=
    T.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have h1 : MemLp B 2 (Measure.map (T : X → X) volume) := by
    rw [show Measure.map (T : X → X) volume = Measure.map ((T : X →ₗ[ℝ] X) : X → X) volume
      from rfl, hmap]
    exact hB.smul_measure ENNReal.ofReal_ne_top
  refine (hemb.memLp_map_measure_iff.1 h1).ae_eq (Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply, hT, div_eq_inv_mul]

/-- W-PDE1 P5 helper: the extension `E_c` maps `L²` of the half-disc into `L²` of the disc. -/
theorem pde_hx_memLp_ext {r : ℝ} {V W : Opens X}
    (hV : (V : Set X) = ball 0 r ∩ {y | 0 < y 1}) (hW : (W : Set X) = ball 0 r)
    (M : ℕ) (c : ℕ → ℝ) {f : X → ℝ} (hf : MemLp f 2 ((volume : Measure X).restrict V)) :
    MemLp (fun y => if 0 < y 1 then f y else
      ∑ j ∈ Finset.range M, c j * f (WithLp.toLp 2 ![y 0, -(y 1 / (j + 1))]))
      2 ((volume : Measure X).restrict W) := by
  have hc1 : Continuous fun y : X => y 1 :=
    (EuclideanSpace.proj (1 : Fin 2) : X →L[ℝ] ℝ).continuous
  have hPm : MeasurableSet {y : X | 0 < y 1} := (isOpen_lt continuous_const hc1).measurableSet
  have hWm : MeasurableSet (W : Set X) := W.isOpen.measurableSet
  have hf' : MemLp ((V : Set X).indicator f) 2 (volume : Measure X) :=
    (memLp_indicator_iff_restrict V.isOpen.measurableSet.nullMeasurableSet).2 hf
  have hE : MemLp (fun y : X => if 0 < y 1 then (V : Set X).indicator f y else
      ∑ j ∈ Finset.range M,
        c j * (V : Set X).indicator f (WithLp.toLp 2 ![y 0, -(y 1 / ((j : ℝ) + 1))]))
      2 (volume : Measure X) := by
    refine ((hf'.indicator hPm.nullMeasurableSet).add
      ((memLp_finsetSum (Finset.range M) fun (j : ℕ) _ => (pde_hx_memLp_R (σ := (j : ℝ) + 1) (by positivity)
        hf').const_mul (c j)).indicator hPm.compl.nullMeasurableSet)).ae_eq
      (Eventually.of_forall fun y => ?_)
    by_cases h : 0 < y 1 <;> simp [h]
  refine (hE.restrict W).ae_eq ?_
  refine (ae_restrict_iff' hWm).2 ((measure_eq_zero_iff_ae_notMem.1 pde_hx_line_null).mono
    fun y h1 hyW => ?_)
  exact pde_hx_ext_ind hV M (fun j t => c j * t) f (by rw [← hW]; exact hyW) h1

/-- W-PDE1 P5 helper (Hestenes induction): if the moments `∑_{j<M} c j (-1/(j+1))^m` equal `1`
for `m < N`, the extension `E_c` maps `W^{N,2}` of the half-disc into `W^{N,2}` of the disc. -/
theorem pde_hx_ind {r : ℝ} (hr : 0 < r) {V W : Opens X}
    (hV : (V : Set X) = ball 0 r ∩ {y | 0 < y 1}) (hW : (W : Set X) = ball 0 r) (M : ℕ) :
    ∀ (N : ℕ) (c : ℕ → ℝ),
      (∀ m < N, ∑ j ∈ Finset.range M, c j * (-(1 / ((j : ℝ) + 1))) ^ m = 1) →
      ∀ u : TauCeti.Wkp (volume : Measure X) V 2 N, ∃ w : TauCeti.Wkp (volume : Measure X) W 2 N,
        (TauCeti.Wkp.value N w : X → ℝ) =ᵐ[(volume : Measure X).restrict W]
          fun y => if 0 < y 1 then (TauCeti.Wkp.value N u : X → ℝ) y else
            ∑ j ∈ Finset.range M,
              c j * (TauCeti.Wkp.value N u : X → ℝ) (WithLp.toLp 2 ![y 0, -(y 1 / (j + 1))]) := by
  intro N
  induction N with
  | zero =>
    intro c _ u
    have hm := pde_hx_memLp_ext hV hW M c (Lp.memLp (TauCeti.Wkp.value 0 u))
    exact ⟨hm.toLp _, hm.coeFn_toLp⟩
  | succ N ih =>
    intro c hc u
    obtain ⟨d₀, hd₀⟩ := TauCeti.Wkp.exists_hasWeakLineDerivOn_value N u
      (EuclideanSpace.basisFun (Fin 2) ℝ 0)
    obtain ⟨d₁, hd₁⟩ := TauCeti.Wkp.exists_hasWeakLineDerivOn_value N u
      (EuclideanSpace.basisFun (Fin 2) ℝ 1)
    have hc0 : ∑ j ∈ Finset.range M, c j = 1 := by
      simpa only [pow_zero, mul_one] using hc 0 (Nat.succ_pos N)
    have hc' : ∀ m < N, ∑ j ∈ Finset.range M,
        -(c j / ((j : ℝ) + 1)) * (-(1 / ((j : ℝ) + 1))) ^ m = 1 := by
      intro m hm
      refine Eq.trans ?_ (hc (m + 1) (by omega))
      exact Finset.sum_congr rfl fun j _ => by ring
    obtain ⟨w₀, hw₀⟩ := ih c (fun m hm => hc m (by omega)) d₀
    obtain ⟨w₁, hw₁⟩ := ih (fun j => -(c j / ((j : ℝ) + 1))) hc' d₁
    obtain ⟨h₀, h₁⟩ := pde_hx_glue hr hV hW M c hc0 (Lp.memLp (TauCeti.Wkp.value (N + 1) u))
      (Lp.memLp (TauCeti.Wkp.value N d₀)) (Lp.memLp (TauCeti.Wkp.value N d₁)) hd₀ hd₁
    have hm := pde_hx_memLp_ext hV hW M c (Lp.memLp (TauCeti.Wkp.value (N + 1) u))
    obtain ⟨w, hw⟩ := TauCeti.Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn
      (EuclideanSpace.basisFun (Fin 2) ℝ) (hm.toLp _) N (Fin.forall_fin_two.2
        ⟨⟨w₀, (h₀.congr_ae_deriv hw₀.symm).congr_ae hm.coeFn_toLp.symm⟩,
          ⟨w₁, (h₁.congr_ae_deriv hw₁.symm).congr_ae hm.coeFn_toLp.symm⟩⟩)
    exact ⟨w, by rw [hw]; exact hm.coeFn_toLp⟩

/-- W-PDE1 P5 helper (Hestenes coefficients): there are `c₀, …, c_{N-1}` with
`∑_{j<N} c j (-1/(j+1))^m = 1` for every `m < N` (a Vandermonde system with distinct nodes). -/
theorem pde_hx_coeff (N : ℕ) :
    ∃ c : ℕ → ℝ, ∀ m < N, ∑ j ∈ Finset.range N, c j * (-(1 / ((j : ℝ) + 1))) ^ m = 1 := by
  set x : Fin N → ℝ := fun j => -(1 / ((j : ℝ) + 1)) with hx
  have hinj : Function.Injective x := by
    intro i j hij
    simp only [hx, neg_inj, one_div, _root_.inv_inj, add_left_inj, Nat.cast_inj] at hij
    exact Fin.ext hij
  have hdet : IsUnit (Matrix.vandermonde x).transpose := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact (Matrix.det_vandermonde_ne_zero_iff.2 hinj).isUnit
  obtain ⟨c0, hc0⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hdet (fun _ => 1)
  refine ⟨fun j => if h : j < N then c0 ⟨j, h⟩ else 0, fun m hm => ?_⟩
  have h : ∑ j : Fin N, x j ^ m * c0 j = 1 := congrFun hc0 ⟨m, hm⟩
  rw [Finset.sum_range]
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [j.is_lt, ↓reduceDIte, Fin.eta, hx]
  ring

/-- W-PDE1 P5 (Hestenes extension across the flat boundary; frozen statement). Every element of
`W^{N,2}` of the half-disc `V` agrees a.e. on `V` with (the value of) an element of `W^{N,2}` of
the disc `W`: the extension `E_c u` with Hestenes coefficients `c` (`pde_hx_coeff`). -/
theorem pde_hestenes_ext (N : ℕ) {r : ℝ} (hr : 0 < r) {V W : Opens X}
    (hV : (V : Set X) = ball 0 r ∩ {y | 0 < y 1}) (hW : (W : Set X) = ball 0 r)
    (u : TauCeti.Wkp (volume : Measure X) V 2 N) :
    ∃ w : TauCeti.Wkp (volume : Measure X) W 2 N,
      (TauCeti.Wkp.value N w : X → ℝ) =ᵐ[(volume : Measure X).restrict V]
        (TauCeti.Wkp.value N u : X → ℝ) := by
  obtain ⟨c, hc⟩ := pde_hx_coeff N
  obtain ⟨w, hw⟩ := pde_hx_ind hr hV hW N N c hc u
  refine ⟨w, ?_⟩
  have hVW : (V : Set X) ⊆ W := by rw [hV, hW]; exact inter_subset_left
  refine Filter.EventuallyEq.trans (ae_restrict_of_ae_restrict_of_subset hVW hw)
    ((ae_restrict_iff' V.isOpen.measurableSet).2 (Eventually.of_forall fun y hy => ?_))
  have hy1 : 0 < y 1 := by rw [hV] at hy; exact hy.2
  simp only [hy1, ↓reduceIte]


/-- W-PDE1 P5 (A): a function in `H^k` of the half disc for every `k` has a representative
smooth on the closed half disc `B(0, r) ∩ {0 ≤ y₁}`. -/
theorem pde_bd_closure_loc {r : ℝ} (hr : 0 < r) {V : Opens X}
    (hV : (V : Set X) = ball 0 r ∩ {y | 0 < y 1}) {f : X → ℝ}
    (hk : ∀ k : ℕ, ∃ w : TauCeti.Wkp (volume : Measure X) V 2 k,
      (TauCeti.Wkp.value k w : X → ℝ) =ᵐ[(volume : Measure X).restrict V] f) :
    ∃ h : X → ℝ, ContDiffOn ℝ ∞ h (ball 0 r ∩ {y | 0 ≤ y 1}) ∧
      f =ᵐ[(volume : Measure X).restrict V] h := by
  let W : Opens X := ⟨ball 0 r, isOpen_ball⟩
  have hfin : Module.finrank ℝ X < 2 * 2 := by simp
  have hrep : ∀ j : ℕ, ∃ g : X → ℝ, ContDiffOn ℝ j g (ball 0 r) ∧
      f =ᵐ[(volume : Measure X).restrict V] g := by
    intro j
    obtain ⟨w, hw⟩ := hk (2 + j)
    obtain ⟨w', hw'⟩ := pde_hestenes_ext (2 + j) hr hV (W := W) rfl w
    obtain ⟨g, hg, hwg⟩ := TauCeti.Wkp.exists_contDiffOn_ae_eq hfin j w'
    have hVW : (V : Set X) ⊆ W := by rw [hV]; exact inter_subset_left
    exact ⟨g, hg, hw.symm.trans (hw'.symm.trans (ae_restrict_of_ae_restrict_of_subset hVW hwg))⟩
  have hcl : ball (0 : X) r ∩ {y | 0 ≤ y 1} ⊆ closure (V : Set X) := by
    have h1 : {y : X | 0 ≤ y 1} = closure {y : X | 0 < y 1} := by
      have := (PiLp.isOpenMap_apply 2 (fun _ : Fin 2 => ℝ) 1).preimage_closure_eq_closure_preimage
        (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1) (Ioi 0)
      rw [closure_Ioi] at this
      exact this
    rw [h1, hV]
    exact isOpen_ball.inter_closure
  obtain ⟨g, hg, hfg⟩ := hrep 0
  have hgc : ContinuousOn g (ball 0 r) := by simpa using hg
  refine ⟨g, contDiffOn_infty.2 fun j => ?_, hfg⟩
  obtain ⟨gj, hgj, hfgj⟩ := hrep j
  have hVb : (V : Set X) ⊆ ball 0 r ∩ {y | 0 ≤ y 1} := by
    rw [hV]; exact fun y hy => ⟨hy.1, show 0 ≤ y 1 from le_of_lt hy.2⟩
  have hsub : ball (0 : X) r ∩ {y | 0 ≤ y 1} ⊆ ball 0 r := inter_subset_left
  have heq : EqOn gj g (ball 0 r ∩ {y | 0 ≤ y 1}) :=
    (Measure.eqOn_open_of_ae_eq (hfgj.symm.trans hfg) V.isOpen
      (hgj.continuousOn.mono (hVb.trans hsub)) (hgc.mono (hVb.trans hsub))).of_subset_closure
      (hgj.continuousOn.mono hsub) (hgc.mono hsub) hVb hcl
  exact (hgj.mono hsub).congr fun y hy => (heq hy).symm

/-- Helper (P5-B): a linear isometry `ℝ × ℝ ≃ X` sending the normal coordinate to `y₁`. -/
theorem pde_bd_swap : ∃ Φ : WithLp 2 (ℝ × ℝ) ≃ₗᵢ[ℝ] X,
    ∀ q : WithLp 2 (ℝ × ℝ), Φ q 0 = (WithLp.ofLp q).2 ∧ Φ q 1 = (WithLp.ofLp q).1 := by
  let L : WithLp 2 (ℝ × ℝ) ≃ₗ[ℝ] X :=
    { toFun := fun q => !₂[(WithLp.ofLp q).2, (WithLp.ofLp q).1]
      invFun := fun y => WithLp.toLp 2 (y 1, y 0)
      map_add' := fun q q' => by ext i; fin_cases i <;> simp
      map_smul' := fun c q => by ext i; fin_cases i <;> simp
      left_inv := fun q => rfl
      right_inv := fun y => by ext i; fin_cases i <;> simp }
  refine ⟨L.isometryOfInner fun q q' => ?_, fun q => ⟨rfl, rfl⟩⟩
  simp [L, WithLp.prod_inner_apply, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- Helper (P5-B): a smooth bump, `1` on `B̄(y₀, δ)`, supported in `B̄(y₀, 2δ)`, with a uniform
bound on its value and gradient. -/
theorem pde_bd_bump (y₀ : X) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ζ : X → ℝ, ContDiff ℝ ∞ ζ ∧ (∀ y ∈ closedBall y₀ δ, ζ y = 1) ∧
      tsupport ζ ⊆ closedBall y₀ (2 * δ) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |ζ x| ≤ M ∧ ‖gradient ζ x‖ ≤ M := by
  let b : ContDiffBump y₀ := ⟨δ, 2 * δ, hδ, by linarith⟩
  have hb : ContDiff ℝ ∞ (b : X → ℝ) := b.contDiff
  obtain ⟨M1, hM1⟩ := hb.continuous.bounded_above_of_compact_support b.hasCompactSupport
  obtain ⟨M2, hM2⟩ := (hb.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (b.hasCompactSupport.fderiv (𝕜 := ℝ))
  refine ⟨b, hb, fun y hy => b.one_of_mem_closedBall hy, b.tsupport_eq.le, max 0 (max M1 M2),
    le_max_left _ _, fun x => ⟨?_, ?_⟩⟩
  · have := hM1 x
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left _ _).trans (le_max_right _ _))
  · have : ‖gradient (b : X → ℝ) x‖ = ‖fderiv ℝ (b : X → ℝ) x‖ := by
      show ‖(InnerProductSpace.toDual ℝ X).symm (fderiv ℝ (b : X → ℝ) x)‖ = _
      exact LinearIsometryEquiv.norm_map _ _
    rw [this]
    exact (hM2 x).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- Helper (P5-B): the cutoff `ζ v` equals `ζ h` a.e. on `H`. -/
theorem pde_bd_tr_value {H Ω₂ : Opens X} (hH : (H : Set X) = {y | 0 < y 1}) (hΩ₂H : Ω₂ ≤ H)
    {ρ : ℝ} (hΩ₂ : (Ω₂ : Set X) = ball 0 ρ ∩ {y | 0 < y 1})
    {v : TauCeti.W1p (volume : Measure X) Ω₂ 2} {ζ : X → ℝ} (hζ : ContDiff ℝ ∞ ζ) {M : ℝ}
    (hM : 0 ≤ M) (hζM : ∀ x ∈ Ω₂, |ζ x| ≤ M) (hgM : ∀ x ∈ Ω₂, ‖gradient ζ x‖ ≤ M)
    (hs : (H : Set X) ∩ tsupport ζ ⊆ Ω₂) (hζ0 : ∀ x, x ∉ ball (0 : X) ρ → ζ x = 0)
    {h : X → ℝ} (hvh : TauCeti.W1p.value v =ᵐ[(volume : Measure X).restrict Ω₂] h) :
    ∀ᵐ x ∂(volume : Measure X), x ∈ (H : Set X) →
      TauCeti.W1p.value (TauCeti.W1p.localizeL hΩ₂H ζ hζ hM hζM hgM hs v) x = ζ x * h x := by
  have h1 := (ae_restrict_iff' H.isOpen.measurableSet).1
    (TauCeti.W1p.value_localizeL_ae hΩ₂H hζ hM hζM hgM hs v)
  have h2 := (ae_restrict_iff' Ω₂.isOpen.measurableSet).1 hvh
  filter_upwards [h1, h2] with x hx1 hx2 hxH
  rw [hx1 hxH]
  by_cases hxΩ : x ∈ (Ω₂ : Set X)
  · rw [indicator_of_mem hxΩ, hx2 hxΩ, smul_eq_mul]
  · rw [indicator_of_notMem hxΩ]
    have hxb : x ∉ ball (0 : X) ρ := fun hxb => hxΩ (by
      have h3 := hxH
      rw [hH] at h3
      rw [hΩ₂]
      exact ⟨hxb, h3⟩)
    rw [hζ0 x hxb, zero_mul]

/-- Helper (P5-B): transported to the half-space `{0 < fst}` of `ℝ × ℝ`, the cutoff has zero
trace, so `ζ h` vanishes a.e. on the boundary line. -/
theorem pde_bd_tr_line {H : Opens X} {Φ : WithLp 2 (ℝ × ℝ) ≃ₗᵢ[ℝ] X}
    (hΦ : ∀ q : WithLp 2 (ℝ × ℝ), Φ q 0 = (WithLp.ofLp q).2 ∧ Φ q 1 = (WithLp.ofLp q).1)
    (hH : (H : Set X) = {y | 0 < y 1}) {ρ : ℝ} {h : X → ℝ}
    (hc : ContinuousOn h (ball 0 ρ ∩ {y | 0 ≤ y 1})) {ζ : X → ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (hζρ : tsupport ζ ⊆ ball 0 ρ) {w : TauCeti.W1p (volume : Measure X) H 2}
    (hw0 : w ∈ TauCeti.w1p0Submodule (volume : Measure X) H 2)
    (hwv : ∀ᵐ x ∂(volume : Measure X), x ∈ (H : Set X) → TauCeti.W1p.value w x = ζ x * h x) :
    ∀ᵐ t ∂(volume : Measure ℝ), ζ (Φ (WithLp.toLp 2 (0, t))) * h (Φ (WithLp.toLp 2 (0, t))) = 0 := by
  let U' : Opens (WithLp 2 (ℝ × ℝ)) := TauCeti.normalHalfSpace 0
  have hUV : (U' : Set (WithLp 2 (ℝ × ℝ))) = Φ ⁻¹' (H : Set X) := by
    ext q
    simp only [mem_preimage, hH, mem_ofPred_eq, (hΦ q).2]
    rfl
  have hΦmp : MeasurePreserving Φ := Φ.measurePreserving
  have hΦl : LocallyLipschitzOn (U' : Set (WithLp 2 (ℝ × ℝ))) Φ :=
    Φ.lipschitzWith.locallyLipschitz.locallyLipschitzOn
  have hΦd : ∀ q ∈ (U' : Set (WithLp 2 (ℝ × ℝ))), ‖fderiv ℝ Φ q‖ ≤ 1 := fun q _ => by
    rw [show fderiv ℝ Φ q = (Φ.toContinuousLinearEquiv : WithLp 2 (ℝ × ℝ) →L[ℝ] X) from
      Φ.toContinuousLinearEquiv.fderiv]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp
  have hu'0 := TauCeti.W1p.compMeasurePreservingL_mem_w1p0Submodule (by norm_num)
    Φ.toHomeomorph.isProperMap hΦmp hUV hΦl hΦd hw0
  have htr0 : TauCeti.W1p.halfSpaceTrace (p := 2) (by norm_num) 0
      (TauCeti.W1p.compMeasurePreservingL hΦmp hUV hΦl hΦd w) = 0 :=
    TauCeti.W1p.halfSpaceTrace_eq_zero_of_w1p0 (p := 2) (by norm_num) 0 ⟨_, hu'0⟩
  let f : WithLp 2 (ℝ × ℝ) → ℝ := fun q => ζ (Φ q) * h (Φ q)
  have hf : ContinuousOn f {q | 0 ≤ q.fst} := by
    intro q hq
    by_cases hqb : Φ q ∈ ball (0 : X) ρ
    · have hq1 : 0 ≤ Φ q 1 := by rw [(hΦ q).2]; exact hq
      have hcw : ContinuousWithinAt (fun q => h (Φ q))
          (Φ ⁻¹' (ball 0 ρ ∩ {y | 0 ≤ y 1})) q :=
        (hc _ ⟨hqb, hq1⟩).comp Φ.continuous.continuousWithinAt fun _ hx => hx
      refine ((hζ.continuous.comp Φ.continuous).continuousWithinAt.mul
        (hcw.mono_of_mem_nhdsWithin ?_))
      refine mem_nhdsWithin.2 ⟨Φ ⁻¹' ball 0 ρ, isOpen_ball.preimage Φ.continuous, hqb,
        fun q' hq' => ⟨hq'.1, ?_⟩⟩
      show 0 ≤ Φ q' 1
      rw [(hΦ q').2]
      exact hq'.2
    · have hnt : Φ q ∉ tsupport ζ := fun h' => hqb (hζρ h')
      have hev : ∀ᶠ q' in 𝓝 q, (0 : ℝ) = f q' := by
        filter_upwards [(Φ.continuous.tendsto q).eventually
          ((isClosed_tsupport ζ).isOpen_compl.mem_nhds hnt)] with q' hq'
        simp [f, image_eq_zero_of_notMem_tsupport hq']
      exact (continuousAt_const.congr hev).continuousWithinAt
  have hu' : TauCeti.W1p.value (TauCeti.W1p.compMeasurePreservingL hΦmp hUV hΦl hΦd w)
      =ᵐ[(volume : Measure (WithLp 2 (ℝ × ℝ))).restrict U'] f := by
    refine (TauCeti.W1p.value_compMeasurePreservingL_ae hΦmp hUV hΦl hΦd w).trans ?_
    have h1 := hΦmp.quasiMeasurePreserving.ae hwv
    refine (ae_restrict_iff' U'.isOpen.measurableSet).2 ?_
    filter_upwards [h1] with q hq hqU
    rw [hUV] at hqU
    exact hq hqU
  have htr := TauCeti.W1p.halfSpaceTrace_apply_ae_of_continuousOn (p := 2) (by norm_num) 0 hf hu'
  filter_upwards [htr, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := (volume : Measure ℝ))] with t ht ht0
  rw [htr0] at ht
  rw [ht0] at ht
  exact ht.symm

/-- Helper (P5-B): a continuous `h` with `ζ h = 0` a.e. on the boundary line, `ζ = 1` near `y₀`,
vanishes at `y₀`. -/
theorem pde_bd_tr_point {Φ : WithLp 2 (ℝ × ℝ) ≃ₗᵢ[ℝ] X}
    (hΦ : ∀ q : WithLp 2 (ℝ × ℝ), Φ q 0 = (WithLp.ofLp q).2 ∧ Φ q 1 = (WithLp.ofLp q).1)
    {ρ : ℝ} {h : X → ℝ} (hc : ContinuousOn h (ball 0 ρ ∩ {y | 0 ≤ y 1})) {y₀ : X}
    (hy₀1 : y₀ 1 = 0) {δ : ℝ} (hδ : 0 < δ) (hδρ : closedBall y₀ (2 * δ) ⊆ ball (0 : X) ρ)
    {ζ : X → ℝ} (hζ1 : ∀ y ∈ closedBall y₀ δ, ζ y = 1)
    (hline : ∀ᵐ t ∂(volume : Measure ℝ),
      ζ (Φ (WithLp.toLp 2 (0, t))) * h (Φ (WithLp.toLp 2 (0, t))) = 0) :
    h y₀ = 0 := by
  have hc0 : ∀ t : ℝ, Φ (WithLp.toLp 2 (0, t)) 0 = t := fun t => by simp [(hΦ _).1]
  have hc1 : ∀ t : ℝ, Φ (WithLp.toLp 2 (0, t)) 1 = 0 := fun t => by simp [(hΦ _).2]
  have hcy : Φ (WithLp.toLp 2 (0, y₀ 0)) = y₀ := by
    ext i
    fin_cases i
    · simp [hc0]
    · simp [hc1, hy₀1]
  have hdist : ∀ t : ℝ, dist (Φ (WithLp.toLp 2 (0, t))) y₀ = |t - y₀ 0| := by
    intro t
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, hc0, hc1, hy₀1, Real.dist_eq, Real.dist_eq]
    simp [Real.sqrt_sq_eq_abs]
  have hI : ∀ t ∈ Ioo (y₀ 0 - δ) (y₀ 0 + δ), Φ (WithLp.toLp 2 (0, t)) ∈ closedBall y₀ δ :=
    fun t ht => by
      rw [mem_closedBall, hdist, abs_le]
      constructor <;> linarith [ht.1, ht.2]
  have hcb : MapsTo (fun t : ℝ => Φ (WithLp.toLp 2 (0, t))) (Ioo (y₀ 0 - δ) (y₀ 0 + δ))
      (ball 0 ρ ∩ {y | 0 ≤ y 1}) := fun t ht =>
    ⟨hδρ (closedBall_subset_closedBall (by linarith) (hI t ht)),
      show 0 ≤ Φ (WithLp.toLp 2 (0, t)) 1 by rw [hc1]⟩
  have hcc : Continuous fun t : ℝ => Φ (WithLp.toLp 2 (0, t)) :=
    Φ.continuous.comp ((WithLp.prod_continuous_toLp 2 ℝ ℝ).comp
      (continuous_const.prodMk continuous_id))
  have hae : (fun t => h (Φ (WithLp.toLp 2 (0, t))))
      =ᵐ[(volume : Measure ℝ).restrict (Ioo (y₀ 0 - δ) (y₀ 0 + δ))] fun _ => (0 : ℝ) := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    filter_upwards [hline] with t ht htI
    rw [hζ1 _ (hI t htI), one_mul] at ht
    exact ht
  have heq := Measure.eqOn_open_of_ae_eq hae isOpen_Ioo (hc.comp hcc.continuousOn hcb)
    continuousOn_const
  have h0 := heq (show y₀ 0 ∈ Ioo (y₀ 0 - δ) (y₀ 0 + δ) from ⟨by linarith, by linarith⟩)
  simp only at h0
  rw [hcy] at h0
  exact h0

/-- W-PDE1 P5 (B): let `v ∈ H¹(Ω₂)`, `Ω₂ = B(0, ρ) ∩ H`, have all its cutoffs supported in
`B(0, ρ)` in `H¹₀(H)`, and a representative `h` continuous on `B(0, ρ) ∩ {0 ≤ y₁}`.  Then `h`
vanishes on the flat boundary `B(0, ρ) ∩ {y₁ = 0}`. -/
theorem pde_bd_trace0 {H Ω₂ : Opens X} (hH : (H : Set X) = {y | 0 < y 1}) (hΩ₂H : Ω₂ ≤ H)
    {ρ : ℝ} (hΩ₂ : (Ω₂ : Set X) = ball 0 ρ ∩ {y | 0 < y 1})
    {v : TauCeti.W1p (volume : Measure X) Ω₂ 2}
    (hv0 : ∀ (ζ : X → ℝ) (hζ : ContDiff ℝ ∞ ζ) (M : ℝ) (hM : 0 ≤ M)
      (hζM : ∀ x ∈ Ω₂, |ζ x| ≤ M) (hgM : ∀ x ∈ Ω₂, ‖gradient ζ x‖ ≤ M)
      (hs : (H : Set X) ∩ tsupport ζ ⊆ Ω₂), tsupport ζ ⊆ ball 0 ρ →
        TauCeti.W1p.localizeL hΩ₂H ζ hζ hM hζM hgM hs v ∈
          TauCeti.w1p0Submodule (volume : Measure X) H 2)
    {h : X → ℝ} (hc : ContinuousOn h (ball 0 ρ ∩ {y | 0 ≤ y 1}))
    (hvh : TauCeti.W1p.value v =ᵐ[(volume : Measure X).restrict Ω₂] h) :
    ∀ y ∈ ball (0 : X) ρ, y 1 = 0 → h y = 0 := by
  intro y₀ hy₀ hy₀1
  obtain ⟨Φ, hΦ⟩ := pde_bd_swap
  obtain ⟨ε, hε, hεb⟩ := Metric.isOpen_iff.1 isOpen_ball y₀ hy₀
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ = ε / 4 := ⟨ε / 4, by positivity, rfl⟩
  have hδρ : closedBall y₀ (2 * δ) ⊆ ball (0 : X) ρ :=
    (closedBall_subset_ball (by linarith)).trans hεb
  obtain ⟨ζ, hζ, hζ1, hζt, M, hM, hζMg⟩ := pde_bd_bump y₀ hδ
  have hζρ : tsupport ζ ⊆ ball 0 ρ := hζt.trans hδρ
  have hζ0 : ∀ x, x ∉ ball (0 : X) ρ → ζ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h' => hx (hζρ h')
  have hs : (H : Set X) ∩ tsupport ζ ⊆ Ω₂ := fun x hx => by
    have h1 := hx.1
    rw [hH] at h1
    rw [hΩ₂]
    exact ⟨hζρ hx.2, h1⟩
  have hw0 := hv0 ζ hζ M hM (fun x _ => (hζMg x).1) (fun x _ => (hζMg x).2) hs hζρ
  have hwv := pde_bd_tr_value hH hΩ₂H hΩ₂ hζ hM (fun x _ => (hζMg x).1) (fun x _ => (hζMg x).2)
    hs hζ0 hvh
  have hline := pde_bd_tr_line hΦ hH hc hζ hζρ hw0 hwv
  exact pde_bd_tr_point hΦ hc hy₀1 hδ hδρ hζ1 hline

/-- Helper (P5-C): in a flattening chart, points of `Ω̄` lie in `{0 ≤ y₁}`. -/
theorem pde_bd_closure_nonneg {Ω : Opens X} {e : OpenPartialHomeomorph X X}
    (hΩe : ∀ x ∈ e.source, x ∈ (Ω : Set X) ↔ 0 < (e x) 1) {x : X}
    (hx : x ∈ closure (Ω : Set X)) (hxs : x ∈ e.source) : 0 ≤ e x 1 := by
  by_contra hneg
  push Not at hneg
  have ho : IsOpen (e.source ∩ e ⁻¹' {y : X | y 1 < 0}) :=
    e.isOpen_inter_preimage (isOpen_lt (by fun_prop) continuous_const)
  obtain ⟨z, hz, hzΩ⟩ := mem_closure_iff.1 hx _ ho ⟨hxs, hneg⟩
  exact (not_lt.2 ((hΩe z hz.1).1 hzΩ).le) hz.2

/-- Helper (P5-C): the local boundary picture.  At `x₀ ∈ ∂Ω` there is a flattening chart and a
function `hl` smooth on the closed half disc `B(0, r) ∩ {0 ≤ y₁}`, zero on `B(0, r/2) ∩ {y₁ = 0}`,
representing `u ∘ e⁻¹` on the open half disc. -/
theorem pde_bd_local {Ω U : Opens X} (hΩc : IsCompact (closure (Ω : Set X)))
    (hΩU : closure (Ω : Set X) ⊆ U) {ψ : X → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hΩψ : (Ω : Set X) = {x | ψ x < 0}) (hψ0 : ∀ x, ψ x = 0 → fderiv ℝ ψ x ≠ 0)
    {A : X → Matrix (Fin 2) (Fin 2) ℝ} {lam Lam : ℝ}
    (hell : TauCeti.PDE.UniformlyEllipticOn (U : Set X) A lam Lam)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U) {β : X → X} {γ F : X → ℝ}
    (hβ : ContDiffOn ℝ ∞ β U) (hγ : ContDiffOn ℝ ∞ γ U) (hF : ContDiffOn ℝ ∞ F U)
    (f : Lp ℝ 2 ((volume : Measure X).restrict Ω))
    (hfF : (f : X → ℝ) =ᵐ[(volume : Measure X).restrict Ω] F)
    {u : TauCeti.W1p0 (volume : Measure X) Ω 2}
    (hu : TauCeti.PDE.IsWeakSolutionDirichlet A β γ f u)
    {x₀ : X} (hx₀ : x₀ ∈ frontier (Ω : Set X)) :
    ∃ (e : OpenPartialHomeomorph X X) (r : ℝ), 0 < r ∧ x₀ ∈ e.source ∧ e x₀ = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧ ball 0 r ⊆ e.target ∧
      (∀ x ∈ e.source, x ∈ (Ω : Set X) ↔ 0 < (e x) 1) ∧
      ∃ hl : X → ℝ, ContDiffOn ℝ ∞ hl (ball 0 r ∩ {y | 0 ≤ y 1}) ∧
        (∀ y ∈ ball (0 : X) (r / 2), y 1 = 0 → hl y = 0) ∧
        (fun y => TauCeti.W1p.value (u : TauCeti.W1p (volume : Measure X) Ω 2) (e.symm y))
          =ᵐ[(volume : Measure X).restrict (ball 0 r ∩ {y | 0 < y 1})] hl := by
  obtain ⟨e, r, hr, hx₀e, he0, he, hes, hrt, hΩe, hk⟩ :=
    pde_boundary_Hk hΩc hΩU hψ hΩψ hψ0 hell hA hβ hγ hF f hfF hu hx₀
  let H : Opens X := ⟨{y | 0 < y 1}, isOpen_lt continuous_const (by fun_prop)⟩
  let V : Opens X := ⟨ball 0 r ∩ {y | 0 < y 1}, isOpen_ball.inter H.isOpen⟩
  obtain ⟨hl, hhl, hfhl⟩ := pde_bd_closure_loc hr (V := V) rfl (fun k => hk k V rfl)
  let Ω₂ : Opens X := ⟨ball 0 (r / 2) ∩ {y | 0 < y 1}, isOpen_ball.inter H.isOpen⟩
  have hmem : ∀ y ∈ (Ω₂ : Set X), y ∈ ball (0 : X) (r / 2) ∧ 0 < y 1 := fun y hy => hy
  have hΩ₂H : Ω₂ ≤ H := fun y hy => (hmem y hy).2
  have hρt' : closedBall (0 : X) (r / 2) ⊆ e.target :=
    (closedBall_subset_ball (by linarith)).trans hrt
  have hΩ₂t : (Ω₂ : Set X) ⊆ e.target := fun y hy => hρt' (ball_subset_closedBall (hmem y hy).1)
  have hΩ₂Ω : MapsTo e.symm Ω₂ Ω := fun y hy => (hΩe _ (e.map_target (hΩ₂t hy))).2
    (by rw [e.right_inv (hΩ₂t hy)]; exact (hmem y hy).2)
  obtain ⟨L, c, hc, hLc⟩ := pde_bd_jbounds he hes (isCompact_closedBall (0 : X) (r / 2)) hρt'
  have hd : DifferentiableOn ℝ e.symm Ω₂ := (hes.differentiableOn (by simp)).mono hΩ₂t
  have hinj : InjOn e.symm Ω₂ := e.symm.injOn.mono hΩ₂t
  have hL : ∀ y ∈ (Ω₂ : Set X), ‖fderiv ℝ e.symm y‖ ≤ L := fun y hy =>
    (hLc y (ball_subset_closedBall (hmem y hy).1)).1
  have hdet : ∀ y ∈ (Ω₂ : Set X), c ≤ |(fderiv ℝ e.symm y).det| := fun y hy =>
    (hLc y (ball_subset_closedBall (hmem y hy).1)).2
  have hΩ₂V : (Ω₂ : Set X) ⊆ V := fun y hy =>
    ⟨ball_subset_ball (by linarith) (hmem y hy).1, (hmem y hy).2⟩
  have h0 := pde_bd_trace0 (H := H) rfl hΩ₂H (ρ := r / 2) rfl
    (v := TauCeti.W1p.compL e.symm (p := 2) (by norm_num) hd hinj hΩ₂Ω hL hc hdet
      (u : TauCeti.W1p (volume : Measure X) Ω 2))
    (fun ζ hζ M hM hζM hgM hs hζρ => pde_bd_v0 rfl hΩ₂H hes hρt' hΩe hd hinj hΩ₂Ω hL hc hdet
      u.2 ζ hζ M hM hζM hgM hs hζρ)
    (hhl.continuousOn.mono (inter_subset_inter_left _ (ball_subset_ball (by linarith))))
    ((TauCeti.W1p.value_compL_ae e.symm (p := 2) (by norm_num) hd hinj hΩ₂Ω hL hc hdet _).trans
      (ae_restrict_of_ae_restrict_of_subset hΩ₂V hfhl))
  exact ⟨e, r, hr, hx₀e, he0, he, hes, hrt, hΩe, hl, hhl, h0, hfhl⟩

/-- Helper (P5-C): the interior representative and the chart representative agree on
`Ω ∩ e⁻¹(B(0, r))` (a.e. by the null-set invariance of `e⁻¹`, everywhere by continuity). -/
theorem pde_bd_glue_eq {Ω : Opens X} {e : OpenPartialHomeomorph X X}
    (he : ContDiffOn ℝ ∞ e e.source) (hes : ContDiffOn ℝ ∞ e.symm e.target) {r : ℝ}
    (hrt : ball 0 r ⊆ e.target) (hΩe : ∀ x ∈ e.source, x ∈ (Ω : Set X) ↔ 0 < (e x) 1)
    {u gi hl : X → ℝ} (hgi : ContinuousOn gi Ω)
    (hugi : u =ᵐ[(volume : Measure X).restrict Ω] gi)
    (hhl : ContinuousOn hl (ball 0 r ∩ {y | 0 ≤ y 1}))
    (huhl : (fun y => u (e.symm y))
      =ᵐ[(volume : Measure X).restrict (ball 0 r ∩ {y | 0 < y 1})] hl) :
    ∀ x ∈ (Ω : Set X), x ∈ e.source → e x ∈ ball (0 : X) r → gi x = hl (e x) := by
  have hSo : IsOpen ((Ω : Set X) ∩ (e.source ∩ e ⁻¹' ball 0 r)) :=
    Ω.isOpen.inter (e.isOpen_inter_preimage isOpen_ball)
  have hWm : MeasurableSet (ball (0 : X) r ∩ {y | 0 < y 1}) :=
    isOpen_ball.measurableSet.inter (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have hN0 := ae_iff.1 ((ae_restrict_iff' hWm).1 huhl)
  have hNsub : {y : X | ¬(y ∈ ball (0 : X) r ∩ {y | 0 < y 1} → u (e.symm y) = hl y)} ⊆
      e.target := fun y hy => hrt (not_imp.1 hy).1.1
  have hNi := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (μ := volume)
    ((hes.differentiableOn (by simp)).mono hNsub) hN0
  have hae : gi =ᵐ[(volume : Measure X).restrict
      ((Ω : Set X) ∩ (e.source ∩ e ⁻¹' ball 0 r))] fun x => hl (e x) := by
    have h1 : u =ᵐ[(volume : Measure X).restrict
        ((Ω : Set X) ∩ (e.source ∩ e ⁻¹' ball 0 r))] gi :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left hugi
    refine h1.symm.trans ((ae_restrict_iff' hSo.measurableSet).2 ?_)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hNi] with x hx hxS
    have hxs : x ∈ e.source := hxS.2.1
    have hyW : e x ∈ ball (0 : X) r ∩ {y | 0 < y 1} := ⟨hxS.2.2, (hΩe x hxs).1 hxS.1⟩
    have hP : e x ∈ ball (0 : X) r ∩ {y | 0 < y 1} → u (e.symm (e x)) = hl (e x) := by
      by_contra hc
      exact hx ⟨e x, hc, e.left_inv hxs⟩
    have := hP hyW
    rw [e.left_inv hxs] at this
    exact this
  have hcont2 : ContinuousOn (fun x => hl (e x)) ((Ω : Set X) ∩ (e.source ∩ e ⁻¹' ball 0 r)) :=
    hhl.comp (he.continuousOn.mono fun x hx => hx.2.1) fun x hx =>
      ⟨hx.2.2, le_of_lt ((hΩe x hx.2.1).1 hx.1)⟩
  intro x hx hxs hxr
  exact Measure.eqOn_open_of_ae_eq hae hSo (hgi.mono inter_subset_left) hcont2 ⟨hx, hxs, hxr⟩

/-- W-PDE1 P5 deliverable (smooth up to the boundary, zero on the boundary): with the hypotheses
of `pde_boundary_Hk`, the weak solution `u ∈ H¹₀(Ω)` has a representative `g` smooth on `Ω̄`
with `g = 0` on `∂Ω`. -/
theorem pde_closure_smooth {Ω U : Opens X} (hΩc : IsCompact (closure (Ω : Set X)))
    (hΩU : closure (Ω : Set X) ⊆ U) {ψ : X → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hΩψ : (Ω : Set X) = {x | ψ x < 0}) (hψ0 : ∀ x, ψ x = 0 → fderiv ℝ ψ x ≠ 0)
    {A : X → Matrix (Fin 2) (Fin 2) ℝ} {lam Lam : ℝ}
    (hell : TauCeti.PDE.UniformlyEllipticOn (U : Set X) A lam Lam)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U) {β : X → X} {γ F : X → ℝ}
    (hβ : ContDiffOn ℝ ∞ β U) (hγ : ContDiffOn ℝ ∞ γ U) (hF : ContDiffOn ℝ ∞ F U)
    (f : Lp ℝ 2 ((volume : Measure X).restrict Ω))
    (hfF : (f : X → ℝ) =ᵐ[(volume : Measure X).restrict Ω] F)
    {u : TauCeti.W1p0 (volume : Measure X) Ω 2}
    (hu : TauCeti.PDE.IsWeakSolutionDirichlet A β γ f u) :
    ∃ g : X → ℝ, ContDiffOn ℝ ∞ g (closure (Ω : Set X)) ∧
      TauCeti.W1p.value (u : TauCeti.W1p (volume : Measure X) Ω 2)
        =ᵐ[(volume : Measure X).restrict Ω] g ∧
      ∀ x ∈ frontier (Ω : Set X), g x = 0 := by
  have hsplit := pde_bd_split hΩc hΩU hA hβ hγ f hfF hu
  have hΩU' : (Ω : Set X) ⊆ U := subset_closure.trans hΩU
  obtain ⟨gi, hgi, hugi⟩ := pde_smooth_rep (Ω := Ω) fun k V hV hVΩ => by
    obtain ⟨W, hW⟩ := pde_Hk_loc (hell.mono_set hΩU') (fun i j => (hA i j).mono hΩU')
      (hβ.mono hΩU') (hγ.mono hΩU') (hF.mono hΩU') hsplit k hV hVΩ
    exact ⟨TauCeti.Wkp.lowerOrder k W, hW⟩
  refine ⟨(Ω : Set X).indicator gi, contDiffOn_of_locally_contDiffOn fun x hx => ?_,
    hugi.trans (indicator_ae_eq_restrict Ω.isOpen.measurableSet.nullMeasurableSet).symm,
    fun x hx => indicator_of_notMem (fun h => hx.2 (by rw [Ω.isOpen.interior_eq]; exact h)) _⟩
  by_cases hxΩ : x ∈ (Ω : Set X)
  · exact ⟨Ω, Ω.isOpen, hxΩ, (hgi.mono inter_subset_right).congr fun y hy =>
      indicator_of_mem hy.2 _⟩
  have hxf : x ∈ frontier (Ω : Set X) := ⟨hx, by rw [Ω.isOpen.interior_eq]; exact hxΩ⟩
  obtain ⟨e, r, hr, hxe, he0, he, hes, hrt, hΩe, hl, hhl, hl0, hfhl⟩ :=
    pde_bd_local hΩc hΩU hψ hΩψ hψ0 hell hA hβ hγ hF f hfF hu hxf
  have hglue := pde_bd_glue_eq he hes hrt hΩe hgi.continuousOn hugi hhl.continuousOn hfhl
  refine ⟨e.source ∩ e ⁻¹' ball 0 (r / 2), e.isOpen_inter_preimage isOpen_ball,
    ⟨hxe, by rw [mem_preimage, he0]; exact mem_ball_self (by linarith)⟩, ?_⟩
  refine (hhl.comp (he.mono (t := closure (Ω : Set X) ∩ (e.source ∩ e ⁻¹' ball 0 (r / 2)))
    fun y hy => hy.2.1) fun y (hy : y ∈ closure (Ω : Set X) ∩ (e.source ∩ e ⁻¹' ball 0 (r / 2))) =>
    ⟨ball_subset_ball (by linarith) hy.2.2, pde_bd_closure_nonneg hΩe hy.1 hy.2.1⟩).congr
    fun y hy => ?_
  by_cases hyΩ : y ∈ (Ω : Set X)
  · rw [indicator_of_mem hyΩ]
    exact hglue y hyΩ hy.2.1 (ball_subset_ball (by linarith) hy.2.2)
  · rw [indicator_of_notMem hyΩ]
    have h1 : e y 1 = 0 := le_antisymm (not_lt.1 fun h => hyΩ ((hΩe y hy.2.1).2 h))
      (pde_bd_closure_nonneg hΩe hy.1 hy.2.1)
    exact (hl0 (e y) hy.2.2 h1).symm

end EpsteinVMO
