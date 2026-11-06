/-
# The measurable Riemann mapping theorem on the disc, from `LiZhongQC`

The companion development `lizhong_quasiconformal_teichmuller` proves the measurable
Riemann mapping theorem for the whole plane (`LiZhongQC.thm13_7_normalized_existence`,
axiom-clean).  This file derives from it the version on the disc that
`DouadyEarleExt.Quasiconformal` needs: a quasiconformal self-map of the closed disc with
prescribed complex dilatation, fixing the boundary points `1, i, -1`.

The construction, in `LiZhongQC`'s vocabulary throughout:

1. extend `μ` by `0` off the disc and take the plane solution `χ` of Theorem 13.7;
2. `Ω = χ(Δ)` is a bounded Jordan domain; a Riemann map `φ : Ω → Δ` extends to the
   boundary by Carathéodory's theorem (`caratheodory_jordan_clean`), so `f₀ = φ ∘ χ` is a
   self-map of `Δ` extending to a homeomorphism of `Δ̄`, with the dilatation of `χ`;
3. a rotation fixes `1`; conjugating by the Cayley transform, the boundary map becomes an
   increasing self-map of `ℝ` (the orientation input is
   `cyclicOrder_preserved_of_isHomeoExtension_jacobian_pos`, fed by a single point of
   positive Jacobian); an affine automorphism of the upper half-plane then fixes `i, -1`.

No step of this file uses `sorry`.
-/
import Mathlib
import LiZhongQC.Ch02.S13_Representation
import LiZhongQC.Ch01.S05_ExtremalProblems
import LiZhongQC.Lemmas.UnitDiscJordan

open Complex Set Metric Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace AhlforsBers

open LiZhongQC

/-! ### Post-composition with a conformal map does not change the dilatation -/

theorem dz_dzbar_comp_of_hasDerivAt {φ g : ℂ → ℂ} {z c : ℂ} (hφ : HasDerivAt φ c (g z))
    (hg : DifferentiableAt ℝ g z) :
    dz (φ ∘ g) z = c * dz g z ∧ dzbar (φ ∘ g) z = c * dzbar g z := by
  have h := (hφ.hasFDerivAt.restrictScalars ℝ).comp z hg.hasFDerivAt
  rw [dz, dzbar, dz, dzbar, h.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]
  constructor <;> ring

theorem complexDilatation_eq_zero_of_not_differentiableAt {g : ℂ → ℂ} {z : ℂ}
    (hg : ¬ DifferentiableAt ℝ g z) : complexDilatation g z = 0 := by
  simp [complexDilatation, dz, dzbar, fderiv_zero_of_not_differentiableAt hg]

/-- Post-composition with a map that is holomorphic at `g z` and has a holomorphic left inverse
on a neighbourhood `Ω` of `g z` leaves the complex dilatation unchanged — at every point, not
just almost everywhere: where `g` is not differentiable neither is `φ ∘ g`, and both sides are
the junk value `0`. -/
theorem complexDilatation_comp_conformal {φ ψ g : ℂ → ℂ} {Ω : Set ℂ} {z : ℂ}
    (hΩ : IsOpen Ω) (hgz : g z ∈ Ω) (hgc : ContinuousAt g z)
    (hφ : DifferentiableAt ℂ φ (g z)) (hψ : DifferentiableAt ℂ ψ (φ (g z)))
    (hψφ : ∀ w ∈ Ω, ψ (φ w) = w) :
    complexDilatation (φ ∘ g) z = complexDilatation g z := by
  have hev : ∀ᶠ w in 𝓝 z, ψ (φ (g w)) = g w :=
    Filter.eventually_of_mem (hgc.preimage_mem_nhds (hΩ.mem_nhds hgz)) fun w hw => hψφ _ hw
  by_cases hg : DifferentiableAt ℝ g z
  · -- `ψ ∘ φ = id` near `g z`, so `φ'(g z) ≠ 0`
    have hc : deriv φ (g z) ≠ 0 := by
      intro h0
      have hid : (ψ ∘ φ) =ᶠ[𝓝 (g z)] id :=
        Filter.eventually_of_mem (hΩ.mem_nhds hgz) fun w hw => hψφ w hw
      have h1 : HasDerivAt (ψ ∘ φ) (deriv ψ (φ (g z)) * deriv φ (g z)) (g z) :=
        hψ.hasDerivAt.comp (g z) hφ.hasDerivAt
      have h2 : HasDerivAt (ψ ∘ φ) 1 (g z) := (hasDerivAt_id (g z)).congr_of_eventuallyEq hid
      have := h1.unique h2
      rw [h0, mul_zero] at this
      exact zero_ne_one this
    obtain ⟨h1, h2⟩ := dz_dzbar_comp_of_hasDerivAt hφ.hasDerivAt hg
    rw [complexDilatation, complexDilatation, h1, h2, mul_div_mul_left _ _ hc]
  · have hcomp : ¬ DifferentiableAt ℝ (φ ∘ g) z := by
      intro hd
      apply hg
      have hd' : DifferentiableAt ℝ (ψ ∘ (φ ∘ g)) z := (hψ.restrictScalars ℝ).comp z hd
      exact hd'.congr_of_eventuallyEq (hev.mono fun w hw => hw.symm)
    rw [complexDilatation_eq_zero_of_not_differentiableAt hg,
      complexDilatation_eq_zero_of_not_differentiableAt hcomp]

/-! ### Step 1: an unnormalized solution on the disc -/

theorem isBeltramiCoeff_indicator {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k)
    (hμ : IsBeltramiCoeff μ unitDisc k) : IsBeltramiCoeff (unitDisc.indicator μ) univ k := by
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  refine ⟨?_, ?_⟩
  · rw [Measure.restrict_univ]
    exact (aestronglyMeasurable_indicator_iff hDm).2 hμ.1
  · rw [Measure.restrict_univ]
    have h2 := (ae_restrict_iff' hDm).1 hμ.2
    filter_upwards [h2] with z hz
    by_cases hzD : z ∈ unitDisc
    · rw [indicator_of_mem hzD]; exact hz hzD
    · rw [indicator_of_notMem hzD, norm_zero]; exact hk₀

/-- A `K`-quasiconformal self-map of the disc with dilatation `μ` a.e., extending to a
homeomorphism of the closed disc: the plane solution of Theorem 13.7 followed by a Riemann map
of its image, extended to the boundary by Carathéodory's theorem. -/
theorem exists_disc_solution {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμ : IsBeltramiCoeff μ unitDisc k) :
    ∃ f : ℂ → ℂ, ∃ F : ExtPlane → ExtPlane,
      (∀ k', 0 ≤ k' → k' < 1 → IsBeltramiCoeff μ unitDisc k' →
        IsKQC f unitDisc ((1 + k') / (1 - k'))) ∧ f '' unitDisc = unitDisc ∧
      (∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation f z = μ z) ∧
      IsHomeoExtension f unitDisc unitDisc F := by
  -- the plane solution for `μ` extended by zero
  obtain ⟨χ, hχn, hχK, -⟩ :=
    thm13_7_normalized_existence hk₀ hk (isBeltramiCoeff_indicator hk₀ hμ)
  have hχs : χ '' univ = univ := hχn.2.1
  have hχd : ∀ᵐ z, complexDilatation χ z = unitDisc.indicator μ z := hχn.2.2.2.2
  -- `χ` is `(1+k')/(1-k')`-q.c. for every admissible `k'`: the solution of Theorem 13.7 does not
  -- depend on the bound used to produce it
  have hχK' : ∀ k', 0 ≤ k' → k' < 1 → IsBeltramiCoeff μ unitDisc k' →
      IsKQC χ univ ((1 + k') / (1 - k')) := by
    intro k' hk'₀ hk' hμ'
    obtain ⟨χ', -, hχ'K, huniq⟩ :=
      thm13_7_normalized_existence hk'₀ hk' (isBeltramiCoeff_indicator hk'₀ hμ')
    rw [huniq χ hχn]
    exact hχ'K
  obtain ⟨e, he⟩ := t1_homeomorph hχK hχs
  set Ω : Set ℂ := e '' unitDisc with hΩdef
  have hΩo : IsOpen Ω := t1_isOpen_image e
  have hΩc : IsConnected Ω := t1_isConnected_image e
  have hΩne : Ωᶜ.Nonempty := t1_compl_nonempty e
  have : SimplyConnectedSpace ↥Ω := t1_simplyConnected_image e
  have hΩb : Bornology.IsBounded Ω :=
    ((isCompact_closedBall (0 : ℂ) 1).image e.continuous).isBounded.subset
      (image_mono ball_subset_closedBall)
  have hχΩ : χ '' unitDisc = Ω := by rw [hΩdef, he]
  -- `Ω` is a Jordan domain: the image of `Δ` under the sphere homeomorphism extending `e`
  set E : ExtPlane ≃ₜ ExtPlane := e.onePointCongr with hEdef
  have hEcoe : ∀ z : ℂ, E (z : ExtPlane) = ((χ z : ℂ) : ExtPlane) := fun z => by
    rw [hEdef, Homeomorph.onePointCongr_apply, ← he]; rfl
  have hEimg : E '' toExt unitDisc = toExt Ω := by
    rw [toExt, toExt, image_image, ← hχΩ, image_image]
    exact image_congr fun z _ => hEcoe z
  have hΩJ : IsJordanDomain Ω := uq_isJordanDomain_image E isJordanDomain_unitDisc hEimg
  -- a Riemann map of `Ω`, its inverse, and the Carathéodory extension
  have h0Ω : χ 0 ∈ Ω := hχΩ ▸ mem_image_of_mem χ (by simp [unitDisc])
  obtain ⟨φ, hφ, -, -⟩ := t1_riemannMap hΩo hΩc hΩne h0Ω
  set ψ := Function.invFunOn φ Ω with hψdef
  have hψ : IsConformalOnto ψ unitDisc Ω := hφ.symm hΩo
  have hψφ : ∀ w ∈ Ω, ψ (φ w) = w := fun w hw => hφ.2.1.leftInvOn_invFunOn hw
  obtain ⟨Ψ, hΨ⟩ := caratheodory_jordan_clean hΩb hψ hΩJ.2.2
  have hinv : EqOn (Function.invFunOn ψ unitDisc) φ Ω := fun w hw => by
    have hφw : φ w ∈ unitDisc := hφ.2.2 ▸ mem_image_of_mem φ hw
    have h := hψ.2.1.leftInvOn_invFunOn hφw
    rwa [hψφ w hw] at h
  have hφext : IsHomeoExtension φ Ω unitDisc
      (Function.invFunOn Ψ (closure (toExt unitDisc))) := by
    obtain ⟨h1, h2, h3, h4⟩ := isHomeoExtension_invFunOn hψ hΨ
    exact ⟨fun z hz => by rw [h1 z hz, hinv hz], h2, h3, h4⟩
  have hχext : IsHomeoExtension χ unitDisc Ω E :=
    ⟨fun z _ => hEcoe z, E.continuous.continuousOn, E.injective.injOn,
      by rw [E.image_closure, hEimg]⟩
  have hχmaps : MapsTo χ unitDisc Ω := fun z hz => hχΩ ▸ mem_image_of_mem χ hz
  refine ⟨φ ∘ χ, _, ?_, ?_, ?_, hφext.comp hχext hχmaps⟩
  · intro k' hk'₀ hk' hμ'
    have h := thm7_1_comp (nx_isKQC_restrict (hχK' k' hk'₀ hk' hμ') isOpen_ball (subset_univ _))
      (isKQC_one_of_conformal hΩo hφ) (image_subset_iff.2 hχmaps)
    rwa [mul_one] at h
  · rw [image_comp, hχΩ, hφ.2.2]
  · filter_upwards [ae_restrict_of_ae hχd, self_mem_ae_restrict measurableSet_ball]
      with z hz hzD
    have hχz : χ z ∈ Ω := hχmaps hzD
    rw [complexDilatation_comp_conformal hΩo hχz
        (he ▸ e.continuous.continuousAt)
        (hφ.1.differentiableAt (hΩo.mem_nhds hχz))
        (hφ.differentiableAt_invFunOn hΩo hχz) hψφ,
      hz, indicator_of_mem hzD]

/-! ### Step 2: normalization by conformal automorphisms of the disc -/

/-- A homeomorphism of `ℂ̄` agreeing with `M` on `U` is a homeomorphic extension of `M`. -/
theorem isHomeoExtension_of_homeomorph {M : ℂ → ℂ} {U V : Set ℂ} (e : ExtPlane ≃ₜ ExtPlane)
    (he : ∀ w ∈ U, e (w : ExtPlane) = ((M w : ℂ) : ExtPlane)) (himg : M '' U = V) :
    IsHomeoExtension M U V e := by
  have hi : e '' toExt U = toExt V := by
    rw [toExt, toExt, image_image, ← himg, image_image]
    exact image_congr he
  exact ⟨he, e.continuous.continuousOn, e.injective.injOn, by rw [e.image_closure, hi]⟩

/-- Post-composing with a conformal self-map of the disc that extends to `Δ̄` keeps every
property of the solution. -/
theorem normalize_step {f N : ℂ → ℂ} {F N' : ExtPlane → ExtPlane} {K : ℝ} {μ : ℂ → ℂ}
    (hf : IsKQC f unitDisc K) (hfs : f '' unitDisc = unitDisc)
    (hfd : ∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation f z = μ z)
    (hF : IsHomeoExtension f unitDisc unitDisc F)
    (hN : IsConformalOnto N unitDisc unitDisc) (hNe : IsHomeoExtension N unitDisc unitDisc N') :
    IsKQC (N ∘ f) unitDisc K ∧ (N ∘ f) '' unitDisc = unitDisc ∧
      (∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation (N ∘ f) z = μ z) ∧
      IsHomeoExtension (N ∘ f) unitDisc unitDisc (N' ∘ F) := by
  have hmaps : MapsTo f unitDisc unitDisc := fun z hz => hfs ▸ mem_image_of_mem f hz
  refine ⟨?_, by rw [image_comp, hfs, hN.2.2], ?_, hNe.comp hF hmaps⟩
  · have h := thm7_1_comp hf (isKQC_one_of_conformal isOpen_ball hN) (image_subset_iff.2 hmaps)
    rwa [mul_one] at h
  · filter_upwards [hfd, self_mem_ae_restrict measurableSet_ball] with z hz hzD
    rw [complexDilatation_comp_conformal isOpen_ball (hmaps hzD)
      (hf.2.2.1.1.continuousAt (isOpen_ball.mem_nhds hzD))
      (hN.1.differentiableAt (isOpen_ball.mem_nhds (hmaps hzD)))
      (hN.differentiableAt_invFunOn isOpen_ball (hmaps hzD))
      (fun w hw => hN.2.1.leftInvOn_invFunOn hw), hz]

/-- The rotation `w ↦ conj a · w`, `|a| = 1`, is a conformal automorphism of the disc. -/
theorem isConformalOnto_rot {a : ℂ} (ha : ‖a‖ = 1) :
    IsConformalOnto (fun w => conj a * w) unitDisc unitDisc := by
  have hca : ‖conj a‖ = 1 := by rw [Complex.norm_conj, ha]
  have ha0 : conj a ≠ 0 := by intro h; rw [h, norm_zero] at hca; exact zero_ne_one hca
  refine ⟨(differentiable_id.const_mul _).differentiableOn, ?_, ?_⟩
  · intro x _ y _ hxy
    exact mul_left_cancel₀ ha0 hxy
  · ext w
    simp only [mem_image, unitDisc, mem_ball_zero_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [norm_mul, hca, one_mul]; exact hx
    · intro hw
      refine ⟨a * w, by rwa [norm_mul, ha, one_mul], ?_⟩
      rw [← mul_assoc, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ha]
      simp

theorem mobiusFn_cinv (w : ℂ) : mobiusFn I I (-1) 1 w = cayleyInv w := by
  rw [mobiusFn, cayleyInv]; congr 1 <;> ring

/-- The inverse Cayley transform `w ↦ i(1+w)/(1-w)` maps `Δ` conformally onto `ℍ`. -/
theorem isConformalOnto_cinv : IsConformalOnto (mobiusFn I I (-1) 1) unitDisc upperHalf := by
  have hden : ∀ w ∈ unitDisc, (-1 : ℂ) * w + 1 ≠ 0 := fun w hw h => by
    have h1 : w = 1 := by linear_combination -h
    rw [h1] at hw; simp [unitDisc] at hw
  refine ⟨fun w hw => ?_, ?_, ?_⟩
  · exact (((differentiableAt_id.const_mul I).add_const I).div
      ((differentiableAt_id.const_mul (-1)).add_const 1) (hden w hw)).differentiableWithinAt
  · intro x hx y hy hxy
    rw [mobiusFn_cinv, mobiusFn_cinv] at hxy
    rw [← cayley_cayleyInv (mem_ball_zero_iff.1 hx), ← cayley_cayleyInv (mem_ball_zero_iff.1 hy),
      hxy]
  · ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [mobiusFn_cinv]; exact cayleyInv_mem_upperHalf (mem_ball_zero_iff.1 hw)
    · intro hz
      exact ⟨cayley z, cayley_mem_unitDisc hz, by rw [mobiusFn_cinv, cayleyInv_cayley hz]⟩

theorem cyclicStrictMono_vec : CyclicStrictMono ![(-1 : ℝ), 0, 1, 2] := by
  refine ⟨0, Fin.strictMono_iff_lt_succ.2 fun i => ?_⟩
  fin_cases i <;> norm_num

theorem not_cyclicStrictMono_of_strictAnti {f : ℝ → ℝ} (hf : StrictAnti f) :
    ¬ CyclicStrictMono (fun i => f (![(-1 : ℝ), 0, 1, 2] i)) := by
  rintro ⟨k, hk⟩
  have a := hk (show (0 : Fin 4) < 1 by decide)
  have b := hk (show (1 : Fin 4) < 2 by decide)
  have c := hk (show (2 : Fin 4) < 3 by decide)
  have h1 : f 0 < f (-1) := hf (by norm_num)
  have h2 : f 1 < f 0 := hf (by norm_num)
  have h3 : f 2 < f 1 := hf (by norm_num)
  fin_cases k <;> simp_all <;> linarith

/-- A homeomorphic extension of a self-map of `ℍ` fixing `∞` restricts to a continuous injective
self-map of `ℝ`. -/
theorem exists_boundary_real {g : ℂ → ℂ} {G : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension g upperHalf upperHalf G) (hgs : g '' upperHalf = upperHalf)
    (hinf : G extInf = extInf) :
    ∃ h : ℝ → ℝ, Continuous h ∧ Function.Injective h ∧
      ∀ t : ℝ, G (((t : ℝ) : ℂ) : ExtPlane) = (((h t : ℝ) : ℂ) : ExtPlane) := by
  have hfr : G '' frontier (toExt upperHalf) = frontier (toExt upperHalf) :=
    hG.image_frontier isOpen_upperHalf isOpen_upperHalf hgs
  set ι : ℝ → ExtPlane := fun t => (((t : ℝ) : ℂ) : ExtPlane) with hιdef
  have hιeq : ι = realToExtPlane ∘ ((↑) : ℝ → OnePoint ℝ) :=
    funext fun t => (realToExtPlane_coe t).symm
  have hιfr : ∀ t, ι t ∈ frontier (toExt upperHalf) := fun t => by
    rw [hιeq, ← range_realToExtPlane]; exact mem_range_self _
  have hinfr : extInf ∈ frontier (toExt upperHalf) := by
    rw [← range_realToExtPlane, ← realToExtPlane_infty]; exact mem_range_self _
  have hcl : frontier (toExt upperHalf) ⊆ closure (toExt upperHalf) := frontier_subset_closure
  have hex : ∀ t : ℝ, ∃ s : ℝ, G (ι t) = ι s := by
    intro t
    have hmem : G (ι t) ∈ frontier (toExt upperHalf) := hfr ▸ mem_image_of_mem G (hιfr t)
    rw [← range_realToExtPlane] at hmem
    obtain ⟨w, hw⟩ := hmem
    by_cases hw' : w = OnePoint.infty
    · exfalso
      rw [hw', realToExtPlane_infty, ← hinf] at hw
      exact OnePoint.coe_ne_infty _ (hG.2.2.1 (hcl hinfr) (hcl (hιfr t)) hw).symm
    · obtain ⟨s, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hw'
      exact ⟨s, by rw [← hw, realToExtPlane_coe]⟩
  choose h hh using hex
  have hιemb : Topology.IsEmbedding ι := by
    rw [hιeq]
    exact isClosedEmbedding_realToExtPlane.isEmbedding.comp OnePoint.isOpenEmbedding_coe.isEmbedding
  refine ⟨h, ?_, ?_, hh⟩
  · rw [hιemb.continuous_iff]
    have hcomp : (ι ∘ h) = fun t => G (ι t) := funext fun t => (hh t).symm
    rw [hcomp]
    exact hG.2.1.comp_continuous hιemb.continuous (fun t => hcl (hιfr t))
  · intro t₁ t₂ ht
    have h1 : G (ι t₁) = G (ι t₂) := by rw [hh, hh, ht]
    exact hιemb.injective (hG.2.2.1 (hcl (hιfr t₁)) (hcl (hιfr t₂)) h1)

/-- **Orientation.**  A quasiconformal self-map of `ℍ` extending to `ℍ̄` and fixing `∞` is
increasing on `ℝ`.  The input is `cyclicOrder_preserved_of_isHomeoExtension_jacobian_pos`, which
needs one point of positive Jacobian; almost every point supplies one. -/
theorem boundary_strictMono {g : ℂ → ℂ} {G : ExtPlane → ExtPlane} {K : ℝ}
    (hgK : IsKQC g upperHalf K) (hG : IsHomeoExtension g upperHalf upperHalf G)
    (hgs : g '' upperHalf = upperHalf) (hinf : G extInf = extInf) :
    ∃ h : ℝ → ℝ, StrictMono h ∧
      ∀ t : ℝ, G (((t : ℝ) : ℂ) : ExtPlane) = (((h t : ℝ) : ℂ) : ExtPlane) := by
  obtain ⟨h, hc, hi, hh⟩ := exists_boundary_real hG hgs hinf
  refine ⟨h, ?_, hh⟩
  rcases hc.strictMono_of_inj hi with hmono | hanti
  · exact hmono
  · exfalso
    have hne : volume.restrict upperHalf ≠ 0 := by
      rw [Ne, Measure.restrict_eq_zero]
      exact isOpen_upperHalf.measure_ne_zero volume ⟨I, by simp [upperHalf]⟩
    have := ae_neBot.2 hne
    obtain ⟨z₀, hz₀, hd, hJ⟩ := ((ae_restrict_mem isOpen_upperHalf.measurableSet).and
      ((thm9_3_differentiable_ae hgK).and (thm9_6_cor2_jacobian_pos hgK))).exists
    exact not_cyclicStrictMono_of_strictAnti hanti
      (cyclicOrder_preserved_of_isHomeoExtension_jacobian_pos hG hgs hz₀ hd hJ _
        cyclicStrictMono_vec _ fun i => hh _)

theorem cinv_den_ne_zero {w : ℂ} (hw : w ∈ unitDisc) : (-1 : ℂ) * w + 1 ≠ 0 := fun h => by
  have h1 : w = 1 := by linear_combination -h
  rw [h1] at hw; simp [unitDisc] at hw

/-! ### Step 3: the normalized solution -/

/-- **The measurable Riemann mapping theorem on the disc**, normalized at `1, i, -1`: for `μ`
measurable on `Δ` with `‖μ‖_∞ ≤ k < 1` there is a `((1+k)/(1-k))`-quasiconformal self-map of the
disc with complex dilatation `μ` a.e., extending to a homeomorphism of `Δ̄` that fixes `1, i, -1`.
This is `LiZhongQC.IsDiscNormalizedSolution`, together with the sharp constant. -/
theorem exists_disc_normalized {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμ : IsBeltramiCoeff μ unitDisc k) :
    ∃ f : ℂ → ℂ, ∃ F : ExtPlane → ExtPlane,
      (∀ k', 0 ≤ k' → k' < 1 → IsBeltramiCoeff μ unitDisc k' →
        IsKQC f unitDisc ((1 + k') / (1 - k'))) ∧ f '' unitDisc = unitDisc ∧
      (∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation f z = μ z) ∧
      IsHomeoExtension f unitDisc unitDisc F ∧
      F ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧ F (I : ExtPlane) = (I : ExtPlane) ∧
      F ((-1 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane) := by
  obtain ⟨f₀, F₀, hKall, hs, hd, hF⟩ := exists_disc_solution hk₀ hk hμ
  have hK := hKall k hk₀ hk hμ
  /- (a) The boundary value `a = F₀(1)` and the rotation `R` taking it back to `1`. -/
  have hfr : F₀ '' frontier (toExt unitDisc) = frontier (toExt unitDisc) :=
    hF.image_frontier isOpen_ball isOpen_ball hs
  obtain ⟨a, ha, hFa⟩ : ∃ a : ℂ, ‖a‖ = 1 ∧ F₀ ((1 : ℂ) : ExtPlane) = (a : ExtPlane) := by
    have h1fr : ((1 : ℂ) : ExtPlane) ∈ frontier (toExt unitDisc) := by
      rw [frontier_toExt_unitDisc]; exact mem_image_of_mem _ (by simp)
    have hmem := hfr ▸ mem_image_of_mem F₀ h1fr
    rw [frontier_toExt_unitDisc] at hmem
    obtain ⟨w, hw, hw'⟩ := hmem
    exact ⟨w, by simpa using hw, hw'.symm⟩
  have ha0 : conj a ≠ 0 := by
    intro h; rw [map_eq_zero] at h; rw [h, norm_zero] at ha; exact zero_ne_one ha
  have hRdet : conj a * 1 - 0 * 0 ≠ 0 := by simpa using ha0
  set R : ℂ → ℂ := fun w => conj a * w with hRdef
  have hR : IsConformalOnto R unitDisc unitDisc := isConformalOnto_rot ha
  set Rh := mobiusHomeomorph (conj a) 0 0 1 hRdet with hRhdef
  have hRcoe : ∀ w : ℂ, Rh (w : ExtPlane) = ((R w : ℂ) : ExtPlane) := fun w => by
    rw [hRhdef, mobiusHomeomorph_apply, mobiusExt_coe (by simp)]
    simp [mobiusFn, hRdef]
  have hRe : IsHomeoExtension R unitDisc unitDisc Rh :=
    isHomeoExtension_of_homeomorph Rh (fun w _ => hRcoe w) hR.2.2
  have hRa : Rh (a : ExtPlane) = ((1 : ℂ) : ExtPlane) := by
    rw [hRcoe]
    congr 1
    show conj a * a = 1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ha]
    simp
  obtain ⟨hK₁, hs₁, -, hF₁⟩ := normalize_step hK hs hd hF hR hRe
  /- (b) Conjugate by the Cayley transform `ℍ → Δ`; the boundary map fixes `∞` and is
  increasing on `ℝ`. -/
  set Ch := mobiusHomeomorph 1 (-I) 1 I cayley_inv_det with hChdef
  have hCcoe : ∀ z : ℂ, z + I ≠ 0 → Ch (z : ExtPlane) = ((cayley z : ℂ) : ExtPlane) :=
    fun z hz => by
      rw [hChdef, mobiusHomeomorph_apply, mobiusExt_coe (by simpa using hz)]
      congr 1
      rw [mobiusFn, cayley]
      congr 1 <;> ring
  have hCe : IsHomeoExtension cayley upperHalf unitDisc Ch :=
    isHomeoExtension_of_homeomorph Ch (fun z hz => hCcoe z (cayley_den_ne_zero hz))
      isConformalOnto_cayley.2.2
  set Cih := mobiusHomeomorph I I (-1) 1 cayley_det with hCihdef
  have hCie : IsHomeoExtension (mobiusFn I I (-1) 1) unitDisc upperHalf Cih :=
    isHomeoExtension_of_homeomorph Cih
      (fun w hw => by rw [hCihdef, mobiusHomeomorph_apply, mobiusExt_coe (cinv_den_ne_zero hw)])
      isConformalOnto_cinv.2.2
  have hmC : MapsTo cayley upperHalf unitDisc := isConformalOnto_cayley.mapsTo
  have hmRf : MapsTo (R ∘ f₀) unitDisc unitDisc := fun z hz => hs₁ ▸ mem_image_of_mem _ hz
  set g : ℂ → ℂ := mobiusFn I I (-1) 1 ∘ ((R ∘ f₀) ∘ cayley) with hgdef
  set G : ExtPlane → ExtPlane := Cih ∘ ((Rh ∘ F₀) ∘ Ch) with hGdef
  have hG : IsHomeoExtension g upperHalf upperHalf G :=
    hCie.comp (hF₁.comp hCe hmC) (hmRf.comp hmC)
  have hgs : g '' upperHalf = upperHalf := by
    rw [hgdef, image_comp, image_comp, isConformalOnto_cayley.2.2, hs₁,
      isConformalOnto_cinv.2.2]
  have hgK : IsKQC g upperHalf (1 * ((1 + k) / (1 - k)) * 1) :=
    thm7_1_comp (thm7_1_comp (isKQC_one_of_conformal isOpen_upperHalf isConformalOnto_cayley)
      hK₁ (image_subset_iff.2 hmC)) (isKQC_one_of_conformal isOpen_ball isConformalOnto_cinv)
      (image_subset_iff.2 (hmRf.comp hmC))
  have hC_inf : Ch extInf = ((1 : ℂ) : ExtPlane) := by
    rw [hChdef, mobiusHomeomorph_apply, mobiusExt_infty_of_ne one_ne_zero, div_one]
  have hCi_one : Cih ((1 : ℂ) : ExtPlane) = extInf := by
    rw [hCihdef, mobiusHomeomorph_apply, mobiusExt_coe_of_eq_zero (by ring)]
  have hC_m1 : Ch (((-1 : ℝ) : ℂ) : ExtPlane) = (I : ExtPlane) := by
    have hden : ((-1 : ℝ) : ℂ) + I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
    rw [hCcoe _ hden]
    congr 1
    rw [cayley, div_eq_iff hden]
    push_cast
    linear_combination (-1 : ℂ) * I_sq
  have hC_0 : Ch (((0 : ℝ) : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane) := by
    rw [hCcoe _ (by simp)]
    congr 1
    simp [cayley, I_ne_zero]
  have hGinf : G extInf = extInf := by
    simp only [hGdef, Function.comp_apply]
    rw [hC_inf, hFa, hRa, hCi_one]
  obtain ⟨h, hmono, hh⟩ := boundary_strictMono hgK hG hgs hGinf
  /- (c) The affine automorphism `x ↦ αx + β` of `ℍ` taking `h(-1), h(0)` to `-1, 0`. -/
  have hpos : 0 < h 0 - h (-1) := sub_pos.2 (hmono (by norm_num))
  set α : ℝ := 1 / (h 0 - h (-1)) with hαdef
  have hα : 0 < α := one_div_pos.2 hpos
  set β : ℝ := -(α * h 0) with hβdef
  obtain ⟨hA, hAe⟩ := uq_k_mobius_auto (a := α) (b := β) (c := 0) (d := 1) (by simpa using hα)
  set A : ℂ → ℂ := mobiusFn (α : ℂ) (β : ℂ) ((0 : ℝ) : ℂ) ((1 : ℝ) : ℂ) with hAdef
  set Ah := mobiusExt (α : ℂ) (β : ℂ) ((0 : ℝ) : ℂ) ((1 : ℝ) : ℂ) with hAhdef
  have hA_inf : Ah extInf = extInf := mobiusExt_infty_of_eq (by simp)
  have hA_real : ∀ t : ℝ,
      Ah (((t : ℝ) : ℂ) : ExtPlane) = ((((α * t + β : ℝ)) : ℂ) : ExtPlane) := fun t => by
    rw [hAhdef, mobiusExt_ofReal_coe (by simp)]
    simp
  have hm1 : α * h (-1) + β = -1 := by
    rw [hβdef, hαdef]
    field_simp
    ring
  have hm0 : α * h 0 + β = 0 := by rw [hβdef]; ring
  /- The normalizing automorphism `N = C ∘ A ∘ C⁻¹ ∘ R` of the disc. -/
  have hmR : MapsTo R unitDisc unitDisc := hR.mapsTo
  have hmCi : MapsTo (mobiusFn I I (-1) 1) unitDisc upperHalf := isConformalOnto_cinv.mapsTo
  have hmA : MapsTo A upperHalf upperHalf := hA.mapsTo
  have hN : IsConformalOnto (cayley ∘ (A ∘ (mobiusFn I I (-1) 1 ∘ R))) unitDisc unitDisc :=
    isConformalOnto_cayley.comp (hA.comp (isConformalOnto_cinv.comp hR))
  have hNe : IsHomeoExtension (cayley ∘ (A ∘ (mobiusFn I I (-1) 1 ∘ R))) unitDisc unitDisc
      (Ch ∘ (Ah ∘ (Cih ∘ Rh))) :=
    hCe.comp (hAe.comp (hCie.comp hRe hmR) (hmCi.comp hmR)) (hmA.comp (hmCi.comp hmR))
  obtain ⟨-, hsf, hdf, hFf⟩ := normalize_step hK hs hd hF hN hNe
  refine ⟨_, _, fun k' hk'₀ hk' hμ' => (normalize_step (hKall k' hk'₀ hk' hμ') hs hd hF hN hNe).1,
    hsf, hdf, hFf, ?_, ?_, ?_⟩
  · -- `1 ↦ a ↦ 1 ↦ ∞ ↦ ∞ ↦ 1`
    simp only [Function.comp_apply]
    rw [hFa, hRa, hCi_one, hA_inf, hC_inf]
  · -- `i = C(-1)`, and the boundary map sends `-1` to `h(-1)`, which `A` sends to `-1`
    have hkey := hh (-1)
    simp only [hGdef, Function.comp_apply, hC_m1] at hkey
    simp only [Function.comp_apply]
    rw [hkey, hA_real, hm1, hC_m1]
  · -- `-1 = C(0)`, and `h(0) ↦ 0`
    have hkey := hh 0
    simp only [hGdef, Function.comp_apply, hC_0] at hkey
    simp only [Function.comp_apply]
    rw [hkey, hA_real, hm0, hC_0]

/-! ### Step 4: uniqueness against generalized solutions -/

theorem mem_frontier_toExt_unitDisc {z : ℂ} (hz : ‖z‖ = 1) :
    (z : ExtPlane) ∈ frontier (toExt unitDisc) := by
  rw [frontier_toExt_unitDisc]; exact mem_image_of_mem _ (by simpa using hz)

/-- **Uniqueness.**  A generalized `L²` solution `g` of the same Beltrami equation, mapping `Δ`
onto itself, extending to `Δ̄` and agreeing with `f` at `1, i, -1`, coincides with `f` on `Δ`.
This is `thm13_4_uniqueness` for the disc, except that the competitor need only be a
generalized solution: `g ∘ f⁻¹` is holomorphic by the similarity principle
(`similarity_comp_inv_holomorphic`), hence a conformal automorphism of `Δ` fixing three boundary
points (`uq_auto_eq_id`). -/
theorem disc_unique {μ f g : ℂ → ℂ} {k K : ℝ} (hk : k < 1) (hμ : IsBeltramiCoeff μ unitDisc k)
    (hfK : IsKQC f unitDisc K) (hfs : f '' unitDisc = unitDisc)
    (hfd : ∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation f z = μ z)
    {F G : ExtPlane → ExtPlane} (hF : IsHomeoExtension f unitDisc unitDisc F)
    (hg : IsGenSolution g μ unitDisc 2) (hgs : g '' unitDisc = unitDisc)
    (hgi : InjOn g unitDisc) (hG : IsHomeoExtension g unitDisc unitDisc G)
    (h1 : F ((1 : ℂ) : ExtPlane) = G ((1 : ℂ) : ExtPlane))
    (hI : F (I : ExtPlane) = G (I : ExtPlane))
    (hm1 : F ((-1 : ℂ) : ExtPlane) = G ((-1 : ℂ) : ExtPlane)) :
    EqOn g f unitDisc := by
  have hD : IsOpen unitDisc := isOpen_ball
  obtain ⟨-, hh, g', h', hp, heq⟩ := thm10_2_genHomeoSolution_of_isKQC hfK
  have hfgen : IsGenHomeoSolution f μ unitDisc 2 :=
    ⟨hh, g', h', hp, by
      filter_upwards [heq, hfd] with z ha hb
      rw [hb] at ha
      exact ha⟩
  have hfh : IsHomeomorphOnto f unitDisc unitDisc := by
    have h := hh
    rwa [hfs] at h
  set finv := Function.invFunOn f unitDisc with hfinvdef
  have hfinvh : IsHomeomorphOnto finv unitDisc unitDisc := isHomeomorphOnto_invFunOn hfh
  have hmaps : MapsTo finv unitDisc unitDisc :=
    fun w hw => hfinvh.2.2.1 ▸ mem_image_of_mem _ hw
  have hhol : DifferentiableOn ℂ (g ∘ finv) (f '' unitDisc) :=
    similarity_comp_inv_holomorphic hD hk hμ hfgen hg
  rw [hfs] at hhol
  have hφ : IsConformalOnto (g ∘ finv) unitDisc unitDisc :=
    ⟨hhol, hgi.comp hfinvh.2.1 hmaps, by rw [image_comp, hfinvh.2.2.1, hgs]⟩
  have hφext : IsHomeoExtension (g ∘ finv) unitDisc unitDisc
      (G ∘ Function.invFunOn F (closure (toExt unitDisc))) :=
    hG.comp (uq_isHomeoExtension_invFunOn hD hD hfh hF) hmaps
  -- the three boundary points and their images under `F`
  set p : Fin 3 → ExtPlane := ![((1 : ℂ) : ExtPlane), (I : ExtPlane), ((-1 : ℂ) : ExtPlane)]
    with hpdef
  have hpfr : ∀ i, p i ∈ frontier (toExt unitDisc) := by
    intro i
    fin_cases i
    · exact mem_frontier_toExt_unitDisc (by simp)
    · exact mem_frontier_toExt_unitDisc (by simp)
    · exact mem_frontier_toExt_unitDisc (by simp)
  have hpcl : ∀ i, p i ∈ closure (toExt unitDisc) := fun i => frontier_subset_closure (hpfr i)
  have hpinj : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (exfalso; revert hij; norm_num [hpdef, Complex.ext_iff])
  have hFG : ∀ i, F (p i) = G (p i) := by
    intro i
    fin_cases i
    · exact h1
    · exact hI
    · exact hm1
  have hfr : F '' frontier (toExt unitDisc) = frontier (toExt unitDisc) :=
    hF.image_frontier hD hD hfs
  have hqinj : Function.Injective (fun i => F (p i)) :=
    fun i j hij => hpinj (hF.2.2.1 (hpcl i) (hpcl j) hij)
  have hqfr : ∀ i, (fun i => F (p i)) i ∈ frontier (toExt unitDisc) :=
    fun i => hfr ▸ mem_image_of_mem F (hpfr i)
  have hfix : ∀ i, (G ∘ Function.invFunOn F (closure (toExt unitDisc))) ((fun i => F (p i)) i) =
      (fun i => F (p i)) i := by
    intro i
    simp only [Function.comp_apply]
    rw [hF.2.2.1.leftInvOn_invFunOn (hpcl i), hFG i]
  have hid := uq_auto_eq_id isJordanDomain_unitDisc hφ hφext hqinj hqfr hfix
  intro z hz
  have hfz : f z ∈ unitDisc := hfs ▸ mem_image_of_mem f hz
  have hz' := hid hfz
  simp only [Function.comp_apply, id] at hz'
  rwa [hfinvdef, hfh.2.1.leftInvOn_invFunOn hz] at hz'

/-- **Regularity of differentiable solutions.**  A homeomorphism of `Δ` that is differentiable at
every point and solves the Beltrami equation at every point, with `‖μ‖ ≤ k < 1`, is an `L²`
generalized solution.  The area formula bounds `∫ ‖∂g‖²` by `(1+k)/(1-k)` times the area of
`g(Δ)`; by Tonelli the derivative is integrable on almost every line of every rectangle, so the
fundamental theorem of calculus makes `g` absolutely continuous there; and
`lemma9_2_genPartials_of_isACL` turns `ACL` plus locally `L²` partials into generalized
partials. -/
theorem isGenSolution_of_differentiable {μ g : ℂ → ℂ} {k : ℝ} (hk : k < 1)
    (hμ : ∀ z ∈ unitDisc, ‖μ z‖ ≤ k) (hgc : ContinuousOn g unitDisc) (hgi : InjOn g unitDisc)
    (hgb : Bornology.IsBounded (g '' unitDisc)) (hgd : ∀ z ∈ unitDisc, DifferentiableAt ℝ g z)
    (hgeq : ∀ z ∈ unitDisc, dzbar g z = μ z * dz g z) : IsGenSolution g μ unitDisc 2 := by
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have h0D : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hk₀ : 0 ≤ k := (norm_nonneg _).trans (hμ 0 h0D)
  have h1k : 0 < 1 - k := by linarith
  -- pointwise: `‖∂_v g‖² ≤ C · J_g` for `v = 1, i`
  set C : ℝ := (1 + k) / (1 - k) with hCdef
  have hC : 0 ≤ C := div_nonneg (by linarith) h1k.le
  have hdzb : ∀ z ∈ unitDisc, ‖dzbar g z‖ ≤ k * ‖dz g z‖ := fun z hz => by
    rw [hgeq z hz, norm_mul]; exact mul_le_mul_of_nonneg_right (hμ z hz) (norm_nonneg _)
  have hJlow : ∀ z ∈ unitDisc, (1 - k ^ 2) * ‖dz g z‖ ^ 2 ≤ jacobian g z := fun z hz => by
    have := hdzb z hz
    rw [jacobian]
    nlinarith [norm_nonneg (dzbar g z), norm_nonneg (dz g z)]
  have hJ0 : ∀ z ∈ unitDisc, 0 ≤ jacobian g z := fun z hz =>
    (mul_nonneg (by nlinarith) (sq_nonneg _)).trans (hJlow z hz)
  have hv1 : ∀ z, fderiv ℝ g z 1 = dz g z + dzbar g z := fun z => by rw [dz, dzbar]; ring
  have hvI : ∀ z, fderiv ℝ g z I = I * (dz g z - dzbar g z) := fun z => by
    rw [dz, dzbar]; linear_combination (fderiv ℝ g z I) * I_sq
  have hvle : ∀ v : ℂ, (v = 1 ∨ v = I) → ∀ z, ‖fderiv ℝ g z v‖ ≤ ‖dz g z‖ + ‖dzbar g z‖ := by
    rintro v (rfl | rfl) z
    · rw [hv1]; exact norm_add_le _ _
    · rw [hvI, norm_mul, norm_I, one_mul]; exact norm_sub_le _ _
  have hsq : ∀ v : ℂ, (v = 1 ∨ v = I) → ∀ z ∈ unitDisc,
      ‖fderiv ℝ g z v‖ ^ 2 ≤ C * jacobian g z := by
    intro v hv z hz
    have h1 : ‖fderiv ℝ g z v‖ ≤ (1 + k) * ‖dz g z‖ := by linarith [hvle v hv z, hdzb z hz]
    have hsq' : ‖fderiv ℝ g z v‖ ^ 2 ≤ ((1 + k) * ‖dz g z‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [hCdef, div_mul_eq_mul_div, le_div_iff₀ h1k]
    nlinarith [mul_le_mul_of_nonneg_left hsq' h1k.le,
      mul_le_mul_of_nonneg_left (hJlow z hz) (by linarith : (0 : ℝ) ≤ 1 + k)]
  -- the area formula: `∫_Δ J_g = |g(Δ)| < ∞`
  have hJint : ∫⁻ z in unitDisc, ENNReal.ofReal (jacobian g z) < ⊤ := by
    have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hD
      (fun z hz => (hgd z hz).hasFDerivAt.hasFDerivWithinAt) hgi (fun _ => (1 : ENNReal))
    simp only [mul_one, setLIntegral_const, one_mul] at hcv
    have heq : ∫⁻ z in unitDisc, ENNReal.ofReal |(fderiv ℝ g z).det| =
        ∫⁻ z in unitDisc, ENNReal.ofReal (jacobian g z) :=
      setLIntegral_congr_fun hD fun z hz => by
        have e : (fderiv ℝ g z).det = jacobian g z := det_fderiv_eq_jacobian (hgd z hz)
        rw [e, abs_of_nonneg (hJ0 z hz)]
    rw [← heq, ← hcv]
    exact hgb.measure_lt_top
  have hmeasv : ∀ v : ℂ, Measurable fun z => fderiv ℝ g z v :=
    fun v => measurable_fderiv_apply_const ℝ g v
  have hL2 : ∀ v : ℂ, (v = 1 ∨ v = I) →
      ∫⁻ z in unitDisc, ‖fderiv ℝ g z v‖ₑ ^ 2 < ⊤ := by
    intro v hv
    calc ∫⁻ z in unitDisc, ‖fderiv ℝ g z v‖ₑ ^ 2
        ≤ ∫⁻ z in unitDisc, ENNReal.ofReal C * ENNReal.ofReal (jacobian g z) := by
          refine setLIntegral_mono' hD fun z hz => ?_
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
            ← ENNReal.ofReal_mul hC]
          exact ENNReal.ofReal_le_ofReal (hsq v hv z hz)
      _ = ENNReal.ofReal C * ∫⁻ z in unitDisc, ENNReal.ofReal (jacobian g z) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJint
  -- `L¹` on every rectangle of `Δ`: `t ≤ 1 + t²`
  have hL1 : ∀ v : ℂ, (v = 1 ∨ v = I) → ∀ {a b c d : ℝ}, openRect a b c d ⊆ unitDisc →
      ∫⁻ z in openRect a b c d, ‖fderiv ℝ g z v‖ₑ < ⊤ := by
    intro v hv a b c d hR
    have hRm : MeasurableSet (openRect a b c d) := measurableSet_openRect a b c d
    calc ∫⁻ z in openRect a b c d, ‖fderiv ℝ g z v‖ₑ
        ≤ ∫⁻ z in openRect a b c d, (1 + ‖fderiv ℝ g z v‖ₑ ^ 2) := by
          refine lintegral_mono fun z => ?_
          rcases le_total ‖fderiv ℝ g z v‖ₑ 1 with h | h
          · exact h.trans le_self_add
          · calc ‖fderiv ℝ g z v‖ₑ = ‖fderiv ℝ g z v‖ₑ * 1 := (mul_one _).symm
              _ ≤ ‖fderiv ℝ g z v‖ₑ * ‖fderiv ℝ g z v‖ₑ := by gcongr
              _ = ‖fderiv ℝ g z v‖ₑ ^ 2 := (sq _).symm
              _ ≤ 1 + ‖fderiv ℝ g z v‖ₑ ^ 2 := le_add_self
      _ = volume (openRect a b c d) + ∫⁻ z in openRect a b c d, ‖fderiv ℝ g z v‖ₑ ^ 2 := by
          rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul]
      _ < ⊤ := by
          refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
          · exact (isBounded_ball.subset hR).measure_lt_top
          · exact (lintegral_mono_set hR).trans_lt (hL2 v hv)
  -- a line segment inside `Δ` on which the derivative is integrable is absolutely continuous
  have hAC : ∀ (p q : ℂ) (c d : ℝ), c < d →
      (∀ t ∈ Icc c d, p + (t : ℂ) * q ∈ unitDisc) →
      ∫⁻ t in Ioo c d, ‖fderiv ℝ g (p + (t : ℂ) * q) q‖ₑ < ⊤ →
      AbsolutelyContinuousOnInterval (fun t : ℝ => g (p + (t : ℂ) * q)) c d := by
    intro p q c d hcd hseg hfin
    set φ' : ℝ → ℂ := fun t => fderiv ℝ g (p + (t : ℂ) * q) q with hφ'def
    have hline : Continuous fun t : ℝ => p + (t : ℂ) * q := by fun_prop
    have hφ'm : Measurable φ' := (hmeasv q).comp hline.measurable
    have hint : IntervalIntegrable φ' volume c d := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hcd.le]
      exact ⟨hφ'm.aestronglyMeasurable, hfin⟩
    have huIcc : uIcc c d = Icc c d := uIcc_of_le hcd.le
    have hderiv : ∀ t ∈ uIcc c d, HasDerivAt (fun t : ℝ => g (p + (t : ℂ) * q)) (φ' t) t := by
      intro t ht
      rw [huIcc] at ht
      have hl : HasDerivAt (fun t : ℝ => p + (t : ℂ) * q) q t := by
        simpa using ((hasDerivAt_id t).ofReal_comp.mul_const q).const_add p
      exact (hgd _ (hseg t ht)).hasFDerivAt.comp_hasDerivAt t hl
    have hFTC : EqOn (fun t => g (p + (c : ℂ) * q) + ∫ s in c..t, φ' s)
        (fun t : ℝ => g (p + (t : ℂ) * q)) (uIcc c d) := by
      intro t ht
      have hsub : uIcc c t ⊆ uIcc c d := uIcc_subset_uIcc_left ht
      dsimp only
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hderiv s (hsub hs))
        (hint.mono_set hsub)]
      ring
    refine absolutelyContinuousOnInterval_congr hFTC ?_
    have h := (absolutelyContinuousOnInterval_const (g (p + (c : ℂ) * q)) c d).add
      (absolutelyContinuousOnInterval_intervalIntegral_complex hint left_mem_uIcc)
    exact absolutelyContinuousOnInterval_congr (fun t _ => rfl) h
  -- `g` is ACL on `Δ`
  have hACL : IsACL g unitDisc := by
    refine ⟨hgc, fun a b c d hab hcd hR => ⟨?_, ?_⟩⟩
    · -- vertical lines: `y ↦ g(x + iy)`
      have hRo : openRect a b c d ⊆ unitDisc := (openRect_subset_closedRect a b c d).trans hR
      have hF : Measurable fun z => ‖fderiv ℝ g z I‖ₑ := (hmeasv I).enorm
      have htot := hL1 I (Or.inr rfl) hRo
      rw [lintegral_openRect hF] at htot
      have hmeas : Measurable fun x : ℝ => ∫⁻ y in Ioo c d, ‖fderiv ℝ g ((x : ℂ) + (y : ℂ) * I) I‖ₑ :=
        (hF.comp continuous_rectCoords.measurable).lintegral_prod_right'
      filter_upwards [ae_lt_top' hmeas.aemeasurable htot.ne, ae_restrict_mem measurableSet_Ioo]
        with x hx hxab
      exact hAC (x : ℂ) I c d hcd (fun t ht => hR ⟨by simpa using hxab.1.le,
        by simpa using hxab.2.le, by simpa using ht.1, by simpa using ht.2⟩) hx
    · -- horizontal lines: `x ↦ g(x + iy)`
      have hRo : openRect a b c d ⊆ unitDisc := (openRect_subset_closedRect a b c d).trans hR
      have hF : Measurable fun z => ‖fderiv ℝ g z 1‖ₑ := (hmeasv 1).enorm
      have htot := hL1 1 (Or.inl rfl) hRo
      rw [lintegral_openRect_symm hF] at htot
      have hmeas : Measurable fun y : ℝ => ∫⁻ x in Ioo a b, ‖fderiv ℝ g ((x : ℂ) + (y : ℂ) * I) 1‖ₑ :=
        (hF.comp (continuous_rectCoords.comp continuous_swap).measurable).lintegral_prod_right'
      filter_upwards [ae_lt_top' hmeas.aemeasurable htot.ne, ae_restrict_mem measurableSet_Ioo]
        with y hy hycd
      have hAC' := hAC ((y : ℂ) * I) 1 a b hab (fun t ht => hR ⟨by simpa using ht.1,
        by simpa using ht.2, by simpa using hycd.1.le, by simpa using hycd.2.le⟩)
        (by simpa [add_comm] using hy)
      exact absolutelyContinuousOnInterval_congr (fun t _ => by simp [add_comm]) hAC'
  -- locally `L²` partials
  have hloc : ∀ K ⊆ unitDisc, IsCompact K →
      MemLp (partialX g) 2 (volume.restrict K) ∧ MemLp (partialY g) 2 (volume.restrict K) := by
    intro K hKD hKc
    have hKm : ∀ v : ℂ, (v = 1 ∨ v = I) → ∀ P : ℂ → ℂ, (∀ z ∈ unitDisc, P z = fderiv ℝ g z v) →
        MemLp P 2 (volume.restrict K) := by
      intro v hv P hP
      have hae : P =ᵐ[volume.restrict K] fun z => fderiv ℝ g z v := by
        filter_upwards [ae_restrict_mem hKc.measurableSet] with z hz
        exact hP z (hKD hz)
      refine (memLp_congr_ae hae).2 ?_
      rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero
        ENNReal.ofNat_ne_top (hmeasv v).aestronglyMeasurable]
      simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
      exact (lintegral_mono_set hKD).trans_lt (hL2 v hv)
    exact ⟨hKm 1 (Or.inl rfl) _ fun z hz => partialX_eq_of_differentiableAt (hgd z hz),
      hKm I (Or.inr rfl) _ fun z hz => partialY_eq_of_differentiableAt (hgd z hz)⟩
  refine ⟨partialX g, partialY g,
    lemma9_2_genPartials_of_isACL isOpen_ball (by norm_num) (by norm_num) hACL hloc, ?_⟩
  filter_upwards [ae_restrict_mem hD] with z hz
  rw [genDzbar, genDz, partialX_eq_of_differentiableAt (hgd z hz),
    partialY_eq_of_differentiableAt (hgd z hz)]
  exact hgeq z hz

/-! ### Step 5: the theorem on the closed disc, in plain terms -/

theorem closure_toExt_unitDisc : closure (toExt unitDisc) = toExt (closedBall (0 : ℂ) 1) := by
  rw [show unitDisc = ball (0 : ℂ) 1 from rfl, closure_toExt_of_isBounded isBounded_ball,
    closure_ball _ one_ne_zero]

theorem norm_div_le_of_dilatation {a b : ℂ} {q : ℝ} (hq₀ : 0 ≤ q) (hq : q < 1)
    (h : ‖a‖ + ‖b‖ ≤ (1 + q) / (1 - q) * (‖a‖ - ‖b‖)) : ‖b / a‖ ≤ q := by
  have h1q : 0 < 1 - q := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h1q] at h
  have hb : ‖b‖ ≤ q * ‖a‖ := by nlinarith
  rcases eq_or_ne a 0 with rfl | ha
  · simpa using hq₀
  · rw [norm_div, div_le_iff₀ (norm_pos_iff.2 ha)]; linarith

/-- **The measurable Riemann mapping theorem on the closed disc.**  Everything
`DouadyEarleExt.Quasiconformal` asks of `f^μ`.  The one `LiZhongQC` notion in the
statement is quasiconformality (`IsKQC`), which is what pins the choice of `f^μ`
down enough for Lemma 4 to be provable. -/
theorem exists_closedDisc_solution {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμm : Measurable μ) (hμb : ∀ z : ℂ, ‖z‖ < 1 → ‖μ z‖ ≤ k) :
    ∃ f : ℂ → ℂ,
      ContinuousOn f (closedBall 0 1) ∧ BijOn f (closedBall 0 1) (closedBall 0 1) ∧
      f 1 = 1 ∧ f I = I ∧ f (-1) = -1 ∧ (∀ z : ℂ, ‖z‖ = 1 → ‖f z‖ = 1) ∧
      (∀ z : ℂ, ‖z‖ < 1 → ‖f z‖ < 1) ∧
      (∀ᵐ z : ℂ, ‖z‖ < 1 → dzbar f z = μ z * dz f z ∧ dz f z ≠ 0) ∧
      (∀ k' : ℝ, (∀ z : ℂ, ‖z‖ < 1 → ‖μ z‖ ≤ k') →
        ∀ z : ℂ, ‖z‖ < 1 → ‖complexDilatation f z‖ ≤ k') ∧
      (∃ K : ℝ, IsKQC f unitDisc K) ∧
      ∀ g : ℂ → ℂ, ContinuousOn g (closedBall 0 1) → BijOn g (closedBall 0 1) (closedBall 0 1) →
        g 1 = 1 → g I = I → g (-1) = -1 → (∀ z : ℂ, ‖z‖ = 1 → ‖g z‖ = 1) →
        (∀ z : ℂ, ‖z‖ < 1 → DifferentiableAt ℝ g z) →
        (∀ z : ℂ, ‖z‖ < 1 → dzbar g z = μ z * dz g z) →
        EqOn g f (closedBall 0 1) := by
  have hLZ : ∀ k', (∀ z : ℂ, ‖z‖ < 1 → ‖μ z‖ ≤ k') → IsBeltramiCoeff μ unitDisc k' := by
    intro k' hb
    refine ⟨hμm.aestronglyMeasurable, ?_⟩
    rw [ae_restrict_iff' (show MeasurableSet unitDisc from measurableSet_ball)]
    exact Filter.Eventually.of_forall fun z hz => hb z (mem_ball_zero_iff.1 hz)
  obtain ⟨f, F, hKall, hs, hd, hF, hF1, hFI, hFm1⟩ := exists_disc_normalized hk₀ hk (hLZ k hμb)
  have hK := hKall k hk₀ hk (hLZ k hμb)
  have hcl : closure (toExt unitDisc) = toExt (closedBall (0 : ℂ) 1) := closure_toExt_unitDisc
  have hmemcl : ∀ z ∈ closedBall (0 : ℂ) 1, (z : ExtPlane) ∈ closure (toExt unitDisc) :=
    fun z hz => by rw [hcl]; exact mem_image_of_mem _ hz
  have hDsub : unitDisc ⊆ closedBall (0 : ℂ) 1 := ball_subset_closedBall
  -- the representative on the closed disc: the boundary values are read off `F`
  set f' : ℂ → ℂ := fun z => (F (z : ExtPlane)).elim 0 id with hf'def
  have hFcoe : ∀ z ∈ closedBall (0 : ℂ) 1,
      F (z : ExtPlane) = ((f' z : ℂ) : ExtPlane) ∧ f' z ∈ closedBall (0 : ℂ) 1 := by
    intro z hz
    have hmem : F (z : ExtPlane) ∈ closure (toExt unitDisc) := by
      rw [← hF.2.2.2]; exact mem_image_of_mem F (hmemcl z hz)
    rw [hcl] at hmem
    obtain ⟨w, hw, hw'⟩ := hmem
    have hfz : f' z = w := by
      rw [hf'def]
      simp only
      rw [← hw']
      rfl
    exact ⟨by rw [hfz, hw'], hfz ▸ hw⟩
  have hfD : ∀ z ∈ unitDisc, f' z = f z := by
    intro z hz
    rw [hf'def]
    simp only
    rw [hF.1 z hz]
    rfl
  have hloc : ∀ z ∈ unitDisc, f' =ᶠ[𝓝 z] f := fun z hz =>
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) fun w hw => hfD w hw
  have hdz : ∀ z ∈ unitDisc, dz f' z = dz f z := fun z hz => by
    rw [dz, dz, (hloc z hz).fderiv_eq]
  have hdzbar : ∀ z ∈ unitDisc, dzbar f' z = dzbar f z := fun z hz => by
    rw [dzbar, dzbar, (hloc z hz).fderiv_eq]
  have hcd : ∀ z ∈ unitDisc, complexDilatation f' z = complexDilatation f z := fun z hz => by
    rw [complexDilatation, complexDilatation, hdz z hz, hdzbar z hz]
  have hfms : ∀ z ∈ unitDisc, f z ∈ unitDisc := fun z hz => hs ▸ mem_image_of_mem f hz
  have hcont : ContinuousOn f' (closedBall 0 1) := by
    rw [OnePoint.isOpenEmbedding_coe.isEmbedding.continuousOn_iff]
    have h1 : ContinuousOn (F ∘ ((↑) : ℂ → ExtPlane)) (closedBall 0 1) :=
      hF.2.1.comp OnePoint.continuous_coe.continuousOn hmemcl
    exact h1.congr fun z hz => (hFcoe z hz).1.symm
  have hbij : BijOn f' (closedBall 0 1) (closedBall 0 1) := by
    refine ⟨fun z hz => (hFcoe z hz).2, fun x hx y hy hxy => ?_, fun w hw => ?_⟩
    · have := hF.2.2.1 (hmemcl x hx) (hmemcl y hy)
        (by rw [(hFcoe x hx).1, (hFcoe y hy).1, hxy])
      exact OnePoint.coe_injective this
    · have hw' : (w : ExtPlane) ∈ F '' closure (toExt unitDisc) := by
        rw [hF.2.2.2, hcl]; exact mem_image_of_mem _ hw
      obtain ⟨v, hv, hvw⟩ := hw'
      rw [hcl] at hv
      obtain ⟨z, hz, rfl⟩ := hv
      exact ⟨z, hz, OnePoint.coe_injective (by rw [← (hFcoe z hz).1, hvw])⟩
  have hvalue : ∀ z : ℂ, F (z : ExtPlane) = (z : ExtPlane) → f' z = z := fun z hz => by
    rw [hf'def]
    simp only
    rw [hz]
    rfl
  refine ⟨f', hcont, hbij, hvalue 1 hF1, hvalue I hFI, hvalue (-1) hFm1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the circle goes to the circle
    intro z hz
    have hfr : F '' frontier (toExt unitDisc) = frontier (toExt unitDisc) :=
      hF.image_frontier isOpen_ball isOpen_ball hs
    have hmem := hfr ▸ mem_image_of_mem F (mem_frontier_toExt_unitDisc hz)
    rw [frontier_toExt_unitDisc, (hFcoe z (mem_closedBall_zero_iff.2 hz.le)).1] at hmem
    obtain ⟨w, hw, hw'⟩ := hmem
    rw [← OnePoint.coe_injective hw']
    exact mem_sphere_zero_iff_norm.1 hw
  · -- the disc goes into the disc
    intro z hz
    have hzD : z ∈ unitDisc := mem_ball_zero_iff.2 hz
    rw [hfD z hzD]
    exact mem_ball_zero_iff.1 (hfms z hzD)
  · -- the Beltrami equation and nondegeneracy, almost everywhere
    have h2 := (ae_restrict_iff' measurableSet_ball).1 (hd.and (thm9_6_cor2_jacobian_pos hK))
    filter_upwards [h2] with z hz
    intro hz1
    have hzD : z ∈ unitDisc := mem_ball_zero_iff.2 hz1
    obtain ⟨hcdz, hJz⟩ := hz hzD
    have hne : dz f z ≠ 0 := by
      intro h0
      rw [jacobian, h0, norm_zero] at hJz
      nlinarith [norm_nonneg (dzbar f z)]
    rw [hdz z hzD, hdzbar z hzD]
    refine ⟨?_, hne⟩
    rw [complexDilatation, div_eq_iff hne] at hcdz
    exact hcdz
  · -- the dilatation bound at every point of the disc
    intro k' hk' z hz
    have hzD : z ∈ unitDisc := mem_ball_zero_iff.2 hz
    rw [hcd z hzD]
    have key : ∀ q, 0 ≤ q → q < 1 → (∀ w : ℂ, ‖w‖ < 1 → ‖μ w‖ ≤ q) →
        ‖complexDilatation f z‖ ≤ q := by
      intro q hq₀ hq hqb
      have hKq := hKall q hq₀ hq (hLZ q hqb)
      by_cases hdiff : DifferentiableAt ℝ f z
      · exact norm_div_le_of_dilatation hq₀ hq (ac_t_dilatation_of_differentiableAt hKq hzD hdiff)
      · rw [complexDilatation_eq_zero_of_not_differentiableAt hdiff, norm_zero]
        exact hq₀
    have hk'₀ : 0 ≤ k' := (norm_nonneg _).trans (hk' 0 (by simp))
    by_cases hk'1 : k' < 1
    · exact key k' hk'₀ hk'1 hk'
    · exact (key k hk₀ hk hμb).trans (by linarith)
  · exact ⟨_, ad_isKQC_congr hK fun z hz => hfD z hz⟩
  · -- uniqueness
    intro g hgc hgb hg1 hgI hgm1 hgS hgd hgeq
    have hgi : InjOn g (closedBall 0 1) := hgb.injOn
    have hgDo : IsOpen (g '' unitDisc) :=
      isOpen_image_of_continuousOn_injOn isOpen_ball (hgc.mono hDsub) (hgi.mono hDsub)
    have hgs : g '' unitDisc = unitDisc := by
      apply Subset.antisymm
      · have hsub : g '' unitDisc ⊆ closedBall 0 1 := (image_mono hDsub).trans hgb.mapsTo.image_subset
        have := hgDo.subset_interior_iff.2 hsub
        rwa [interior_closedBall _ one_ne_zero] at this
      · intro w hw
        obtain ⟨z, hz, rfl⟩ := hgb.surjOn (hDsub hw)
        refine ⟨z, ?_, rfl⟩
        rcases (mem_closedBall_zero_iff.1 hz).lt_or_eq with h | h
        · exact mem_ball_zero_iff.2 h
        · exfalso
          have h1 := hgS z h
          have h2 := mem_ball_zero_iff.1 hw
          linarith
    have hgen : IsGenSolution g μ unitDisc 2 :=
      isGenSolution_of_differentiable hk (fun z hz => hμb z (mem_ball_zero_iff.1 hz))
        (hgc.mono hDsub) (hgi.mono hDsub) (by rw [hgs]; exact isBounded_ball)
        (fun z hz => hgd z (mem_ball_zero_iff.1 hz)) (fun z hz => hgeq z (mem_ball_zero_iff.1 hz))
    have hGe : IsHomeoExtension g unitDisc unitDisc (OnePoint.map g) := by
      refine ⟨fun z _ => rfl, ?_, ?_, ?_⟩
      · rw [hcl, toExt, OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_image_iff]
        exact OnePoint.continuous_coe.comp_continuousOn hgc
      · rw [hcl]
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
        exact congrArg _ (hgi hx hy (OnePoint.coe_injective hxy))
      · rw [hcl, toExt, image_image]
        simp only [OnePoint.map_some]
        rw [← image_image, hgb.image_eq]
    have hEq := disc_unique hk (hLZ k hμb) hK hs hd hF hgen hgs (hgi.mono hDsub) hGe
      (by rw [hF1, OnePoint.map_some, hg1]) (by rw [hFI, OnePoint.map_some, hgI])
      (by rw [hFm1, OnePoint.map_some, hgm1])
    have hEqD : EqOn g f' unitDisc := fun z hz => by rw [hfD z hz]; exact hEq hz
    exact hEqD.of_subset_closure hgc hcont hDsub (closure_ball (0 : ℂ) one_ne_zero).symm.subset

end AhlforsBers
