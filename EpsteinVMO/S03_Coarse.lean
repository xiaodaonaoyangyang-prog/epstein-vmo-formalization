import EpsteinVMO.S02_Prelim

/-!
# §3 Coarse geometry of the labels (statements)

Source: `sec03-coarse.tex`.  Standing hypotheses of the section (`sec03-coarse.tex:5`): `Γ` is a
`K`-quasicircle through `∞` that is not a circle, i.e. `IsKQuasiPair Ω Ωs K ∧ ¬ IsLinePair Ω Ωs`;
constants "depending only on `K`" are chosen before the curve.  `d(w) = dist(w, Γ ∩ ℂ)` is
`infDist w (curveOf Ω Ωs)`.  Lemma 3.4 (`lem:borel-label`) is stated in `S02_Prelim`
(`lem_borel_label`), since §2 already uses it.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace EpsteinVMO

open LiZhongQC

/-! ## Section-local definitions -/

/-- `γ : ℝ → Ω` is a complete geodesic of `(Ω, ρ)` parametrized proportionally to arclength:
`d_ρ(γ t, γ t') = c |t - t'|` for some speed `c > 0`. -/
def IsRhoGeodesic (Ω : Set ℂ) (γ : ℝ → ℂ) : Prop :=
  (∀ t, γ t ∈ Ω) ∧ ∃ c : ℝ, 0 < c ∧ ∀ t t', poincareDist Ω (γ t) (γ t') = c * |t - t'|

/-- `(q, ℓ)` is a labelled point (Proposition 3.6, `sec03-coarse.tex:205`): `q = X(ℓ)` with
`ℓ ∈ Ω`; or `q = X*(z*)` with label `ℓ = R(z*) = lab q`; or `q ∈ 𝒩` with label `ℓ = lab q`. -/
def IsLabelledPt (Ω Ωs : Set ℂ) (lab : ℂ × ℝ → ℂ) (q : ℂ × ℝ) (ℓ : ℂ) : Prop :=
  (ℓ ∈ Ω ∧ q = epstein Ω ℓ) ∨ (∃ z ∈ Ωs, q = epstein Ωs z ∧ ℓ = lab q) ∨
    (q ∈ gap Ω Ωs ∧ ℓ = lab q)

/-! ## §3.1 Quasiconformal input -/

/-- Swapping the two sides of a `K`-quasi pair: `F ∘ (z ↦ -z)` exchanges `ℍ` and `𝕃`. -/
theorem s03_qce_swap {Ω Ωs : Set ℂ} {K : ℝ} (h : IsKQuasiPair Ω Ωs K) : IsKQuasiPair Ωs Ω K := by
  obtain ⟨F, hK, hs, hU, hL⟩ := h
  have hnegs : (fun z : ℂ => -z) '' univ = univ := image_univ_of_surjective neg_surjective
  have hneg : IsKQC (fun z : ℂ => -z) univ 1 :=
    isKQC_one_of_conformal isOpen_univ ⟨differentiable_neg.differentiableOn, neg_injective.injOn, hnegs⟩
  have hFn : IsKQC (F ∘ fun z : ℂ => -z) univ (1 * K) := thm7_1_comp hneg hK (subset_univ _)
  rw [one_mul] at hFn
  have hnu : (fun z : ℂ => -z) '' upperHalf = lowerHalf := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : 0 < z.im := hz
      show (-z).im < 0
      rw [neg_im]
      exact neg_neg_of_pos hz'
    · intro hw
      have hw' : w.im < 0 := hw
      refine ⟨-w, ?_, neg_neg w⟩
      show 0 < (-w).im
      rw [neg_im]
      exact neg_pos.mpr hw'
  have hnl : (fun z : ℂ => -z) '' lowerHalf = upperHalf := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : z.im < 0 := hz
      show 0 < (-z).im
      rw [neg_im]
      exact neg_pos.mpr hz'
    · intro hw
      have hw' : 0 < w.im := hw
      refine ⟨-w, ?_, neg_neg w⟩
      show (-w).im < 0
      rw [neg_im]
      exact neg_neg_of_pos hw'
  refine ⟨F ∘ fun z : ℂ => -z, hFn, ?_, ?_, ?_⟩
  · rw [image_comp, hnegs, hs]
  · rw [image_comp, hnu, hL]
  · rw [image_comp, hnl, hU]

/-- The upper side `Ω = F(ℍ)` of a `K`-quasi pair is a Jordan domain with `∞` on its boundary. -/
theorem s03_qce_jordan {Ω Ωs : Set ℂ} {K : ℝ} (h : IsKQuasiPair Ω Ωs K) :
    IsJordanDomain Ω ∧ extInf ∈ frontier (toExt Ω) := by
  obtain ⟨F, hK, hs, hU, -⟩ := h
  obtain ⟨e, rfl⟩ := t1_homeomorph hK hs
  have himg : e.onePointCongr '' toExt upperHalf = toExt Ω := by
    rw [s13x_de_image_toExt, hU]
  refine ⟨uq_isJordanDomain_image e.onePointCongr isJordanDomain_upperHalf himg, ?_⟩
  rw [← himg, ← e.onePointCongr.image_frontier]
  have hHo : IsOpen (toExt upperHalf) := OnePoint.isOpen_image_coe.2 isOpen_upperHalf
  refine ⟨extInf, ⟨s13x_rf_infty_mem_closure, ?_⟩, rfl⟩
  rw [hHo.interior_eq]
  rintro ⟨z, -, hz⟩
  exact OnePoint.coe_ne_infty z hz

/-- A homeomorphism of `ℂ̄` agreeing on `U` with a map `g` carries `toExt U` onto `toExt (g '' U)`. -/
theorem s03_qce_image_toExt (e : ExtPlane ≃ₜ ExtPlane) {g : ℂ → ℂ} {U W : Set ℂ}
    (he : ∀ w ∈ U, e (w : ExtPlane) = ((g w : ℂ) : ExtPlane)) (hg : g '' U = W) :
    e '' toExt U = toExt W := by
  rw [← hg]
  ext x
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨g w, ⟨w, hw, rfl⟩, (he w hw).symm⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, ⟨w, hw, rfl⟩, he w hw⟩

/-- The Möbius homeomorphism `w ↦ (iw + i)/(-w + 1)` agrees with `cayleyInv` on `Δ`. -/
theorem s03_qce_cayleyExt_coe {w : ℂ} (hw : w ∈ unitDisc) :
    mobiusHomeomorph I I (-1) 1 cayley_det (w : ExtPlane) = ((cayleyInv w : ℂ) : ExtPlane) := by
  have hw' : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hden : (-1 : ℂ) * w + 1 ≠ 0 := by
    intro h
    apply cayleyInv_den_ne_zero hw'
    linear_combination h
  rw [mobiusHomeomorph_apply, mobiusExt_coe hden]
  show (((I * w + I) / (-1 * w + 1) : ℂ) : ExtPlane) = ((I * (1 + w) / (1 - w) : ℂ) : ExtPlane)
  congr 1
  ring

/-- The unit disc is a Jordan domain (the Cayley image of `ℍ`). -/
theorem s03_qce_jordan_disc : IsJordanDomain unitDisc :=
  uq_isJordanDomain_image (mobiusHomeomorph 1 (-I) 1 I cayley_inv_det) isJordanDomain_upperHalf
    s13x_th_cayleyExt_image

/-- Core of Lemma 3.1: if `φ : Ω → ℍ` is conformal with a boundary homeomorphism fixing `∞`, then
`φ⁻¹ : ℍ → Ω` is the restriction of a `K²`-q.c. homeomorphism of the plane.  `T = φ ∘ F` is a `K`-q.c.
self-map of `ℍ` fixing `∞`; reflect it (`qc_reflection_extension`) to `g`, and take `E = F ∘ g⁻¹`. -/
theorem s03_qce_core {Ω Ωs : Set ℂ} {K : ℝ} (h : IsKQuasiPair Ω Ωs K) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ Ω upperHalf) {Φ : ExtPlane → ExtPlane}
    (hΦ : IsHomeoExtension φ Ω upperHalf Φ) (hΦi : Φ extInf = extInf) :
    ∃ E : ℂ → ℂ, IsKQC E univ (K * K) ∧ E '' univ = univ ∧
      EqOn E (Function.invFunOn φ Ω) upperHalf := by
  obtain ⟨F, hK, hs, hU, -⟩ := h
  obtain ⟨e, rfl⟩ := t1_homeomorph hK hs
  have hΩo : IsOpen Ω := hU ▸ e.isOpenMap _ isOpen_upperHalf
  have hT : IsKQC (φ ∘ e) upperHalf (K * 1) :=
    thm7_1_comp (ac_t_isKQC_restrict hK isOpen_upperHalf (subset_univ _))
      (isKQC_one_of_conformal hΩo hφ) hU.le
  have hTimg : (φ ∘ e) '' upperHalf = upperHalf := by rw [image_comp, hU, hφ.2.2]
  have hext : IsHomeoExtension (φ ∘ e) upperHalf upperHalf (Φ ∘ e.onePointCongr) := by
    have h1 := s13x_de_isHomeoExtension_homeomorph e upperHalf
    rw [hU] at h1
    exact hΦ.comp h1 (fun z hz => hU ▸ mem_image_of_mem e hz)
  have hei : (Φ ∘ e.onePointCongr) extInf = extInf := hΦi
  have hinf : Tendsto (φ ∘ e) (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ) := by
    have h1 := uq_tendsto_norm_atTop_of_continuousWithinAt_extInf hext.1
      (hext.2.1 extInf s13x_rf_infty_mem_closure) hei
    have h2 := tendsto_norm_atTop_iff_cobounded.mp h1
    rw [Metric.cobounded_eq_cocompact] at h2
    exact h2.mono_left (inf_le_inf_right _
      ((Metric.cobounded_eq_cocompact (α := ℂ)).symm.le.trans (comap_norm_atTop (E := ℂ)).symm.le))
  obtain ⟨g, hg, hgs, hgT, -⟩ := qc_reflection_extension hT hTimg hinf
  have hgi : Function.Injective g := fun a b hab => hg.2.2.1.2.1 (mem_univ a) (mem_univ b) hab
  have hgl : ∀ z, Function.invFunOn g univ (g z) = z := fun z =>
    hgi.injOn.leftInvOn_invFunOn (mem_univ z)
  have hginv : IsKQC (Function.invFunOn g univ) univ (K * 1) := by
    have h1 := thm7_2_inv hg
    rwa [hgs] at h1
  have hE : IsKQC (e ∘ Function.invFunOn g univ) univ (K * 1 * K) :=
    thm7_1_comp hginv hK (subset_univ _)
  rw [mul_one] at hE
  refine ⟨e ∘ Function.invFunOn g univ, hE, ?_, ?_⟩
  · rw [image_comp, image_univ_of_surjective (fun z => ⟨g z, hgl z⟩), hs]
  · intro w hw
    have hw' : w ∈ (φ ∘ e) '' upperHalf := by rw [hTimg]; exact hw
    obtain ⟨z, hz, rfl⟩ := hw'
    have h1 : Function.invFunOn g univ ((φ ∘ e) z) = z := by
      rw [← hgT hz]
      exact hgl z
    have hez : e z ∈ Ω := hU ▸ mem_image_of_mem e hz
    show e (Function.invFunOn g univ ((φ ∘ e) z)) = Function.invFunOn φ Ω ((φ ∘ e) z)
    rw [h1]
    exact (hφ.2.1.leftInvOn_invFunOn hez).symm

/-- Lemma 3.1, half-plane part, with `Q = K²`. -/
theorem s03_qce_partC {Ω Ωs : Set ℂ} {K : ℝ} (h : IsKQuasiPair Ω Ωs K) :
    ∃ f : ℂ → ℂ, IsConformalOnto f upperHalf Ω ∧
      ∃ F : ℂ → ℂ, IsKQC F univ (K * K) ∧ F '' univ = univ ∧ EqOn F f upperHalf := by
  obtain ⟨hJ, hinf⟩ := s03_qce_jordan h
  obtain ⟨φ, hφ, Φ, hΦ, hΦi⟩ := s16p_uniformizer_inf hJ hinf
  obtain ⟨E, hE, hEs, hEq⟩ := s03_qce_core h hφ hΦ hΦi
  exact ⟨Function.invFunOn φ Ω, hφ.symm hJ.1, E, hE, hEs, hEq⟩

/-- Lemma 3.1, disc part, with `Q = K²`.  For `f : Δ → Ω` let `p ∈ ∂Δ` be the boundary point sent to `∞`;
`φ = cayleyInv ∘ (p⁻¹ ·) ∘ f⁻¹ : Ω → ℍ` fixes `∞`, so `φ⁻¹ = E|ℍ` (`s03_qce_core`), and
`F(ζ) = 1/(E(cayleyInv(ζ/p)) - E(-i))` (a removable point at `p`), `M(w) = E(-i) + 1/w`. -/
theorem s03_qce_partA {Ω Ωs : Set ℂ} {K : ℝ} (h : IsKQuasiPair Ω Ωs K) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) :
    ∃ (F : ℂ → ℂ) (M : ExtPlane → ExtPlane), IsKQC F univ (K * K) ∧ F '' univ = univ ∧
      IsMobius M ∧ ∀ z ∈ unitDisc, M (F z) = (f z : ExtPlane) := by
  obtain ⟨hJ, hinf⟩ := s03_qce_jordan h
  have hDo : IsOpen unitDisc := isOpen_ball
  obtain ⟨Fx, hFx⟩ := thm13_3_boundary_correspondence s03_qce_jordan_disc hJ
    ⟨1, isKQC_one_of_conformal hDo hf⟩ hf.2.2
  set ψ := Function.invFunOn f unitDisc with hψdef
  have hψ : IsConformalOnto ψ Ω unitDisc := hf.symm hDo
  have hΨ := isHomeoExtension_invFunOn hf hFx
  set Ψ := Function.invFunOn Fx (closure (toExt unitDisc)) with hΨdef
  have hψf : ∀ z ∈ unitDisc, ψ (f z) = z := fun z hz => hf.2.1.leftInvOn_invFunOn hz
  -- the boundary point `p = Ψ(∞)`
  have hmem : Ψ extInf ∈ closure (toExt unitDisc) :=
    hΨ.2.2.2 ▸ mem_image_of_mem Ψ (frontier_subset_closure hinf)
  have hcl : closure (toExt unitDisc) ⊆ toExt (closedBall (0 : ℂ) 1) :=
    closure_minimal (image_mono ball_subset_closedBall)
      ((isCompact_closedBall (0 : ℂ) 1).image OnePoint.continuous_coe).isClosed
  obtain ⟨p, hp1, hpΨ⟩ := hcl hmem
  have hpn : ‖p‖ = 1 := by
    refine le_antisymm (mem_closedBall_zero_iff.mp hp1) (not_lt.mp fun hlt => ?_)
    have hpD : p ∈ unitDisc := mem_ball_zero_iff.mpr hlt
    have hfp : f p ∈ Ω := hf.2.2 ▸ mem_image_of_mem f hpD
    have h1 : Ψ ((f p : ℂ) : ExtPlane) = Ψ extInf := by
      rw [hΨ.1 (f p) hfp, hf.2.1.leftInvOn_invFunOn hpD, hpΨ]
    have h2 := hΨ.2.2.1 (subset_closure ⟨f p, hfp, rfl⟩) (frontier_subset_closure hinf) h1
    exact OnePoint.coe_ne_infty _ h2
  have hp0 : p ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hpn
    exact zero_ne_one hpn
  -- the rotation `ρ ζ = p⁻¹ ζ`
  set ρ : ℂ → ℂ := fun ζ => p⁻¹ * ζ with hρdef
  have hpi : ‖p⁻¹‖ = 1 := by rw [norm_inv, hpn, inv_one]
  have hρs : ρ '' univ = univ :=
    image_univ_of_surjective fun w => ⟨p * w, by simp only [hρdef]; field_simp⟩
  have hρD : ρ '' unitDisc = unitDisc := by
    ext w
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      refine mem_ball_zero_iff.mpr ?_
      rw [hρdef, norm_mul, hpi, one_mul]
      exact mem_ball_zero_iff.mp hζ
    · intro hw
      refine ⟨p * w, mem_ball_zero_iff.mpr ?_, by simp only [hρdef]; field_simp⟩
      rw [norm_mul, hpn, one_mul]
      exact mem_ball_zero_iff.mp hw
  have hρd : Differentiable ℂ ρ := (differentiable_const _).mul differentiable_id
  have hρi : Function.Injective ρ := fun a b hab => mul_left_cancel₀ (inv_ne_zero hp0) hab
  have hρc : IsConformalOnto ρ unitDisc unitDisc := ⟨hρd.differentiableOn, hρi.injOn, hρD⟩
  have hdet : p⁻¹ * 1 - 0 * 0 ≠ 0 := by simpa using hp0
  set er := mobiusHomeomorph p⁻¹ 0 0 1 hdet with herdef
  have her : ∀ w : ℂ, er (w : ExtPlane) = ((ρ w : ℂ) : ExtPlane) := by
    intro w
    rw [herdef, mobiusHomeomorph_apply, mobiusExt_coe (by simp : (0 : ℂ) * w + 1 ≠ 0)]
    show (((p⁻¹ * w + 0) / (0 * w + 1) : ℂ) : ExtPlane) = ((p⁻¹ * w : ℂ) : ExtPlane)
    congr 1
    simp
  set ec := mobiusHomeomorph I I (-1) 1 cayley_det with hecdef
  -- `φ = cayleyInv ∘ ρ ∘ ψ : Ω → ℍ`, with boundary map fixing `∞`
  have hφ : IsConformalOnto (cayleyInv ∘ (ρ ∘ ψ)) Ω upperHalf :=
    s02_cayleyInv_conformal.comp (hρc.comp hψ)
  have hext1 : IsHomeoExtension (ρ ∘ ψ) Ω unitDisc (er ∘ Ψ) :=
    hΨ.comp_homeomorph hψ.mapsTo er (fun w _ => her w) (s03_qce_image_toExt er (fun w _ => her w) hρD)
  have hext2 : IsHomeoExtension (cayleyInv ∘ (ρ ∘ ψ)) Ω upperHalf (ec ∘ (er ∘ Ψ)) :=
    hext1.comp_homeomorph (hρc.comp hψ).mapsTo ec (fun w hw => s03_qce_cayleyExt_coe hw)
      (s03_qce_image_toExt ec (fun w hw => s03_qce_cayleyExt_coe hw) s02_cayleyInv_conformal.2.2)
  have hρp : ρ p = 1 := by simp only [hρdef]; field_simp
  have hval : (ec ∘ (er ∘ Ψ)) extInf = extInf := by
    show ec (er (Ψ extInf)) = extInf
    rw [← hpΨ, her, hρp, hecdef, mobiusHomeomorph_apply]
    exact mobiusExt_coe_of_eq_zero (by ring)
  obtain ⟨E, hE, hEs, hEq⟩ := s03_qce_core h hφ hext2 hval
  have hEi : Function.Injective E := fun a b hab => hE.2.2.1.2.1 (mem_univ a) (mem_univ b) hab
  -- the conjugate `G` and the final map `F = G ∘ ρ`
  set G : ℂ → ℂ := fun ξ => (E (-I + 2 * I * (1 - ξ)⁻¹) - E (-I))⁻¹ with hGdef
  have hGh : IsHomeomorphOnto G univ univ := b4_qc_conj_isHomeomorphOnto hE hEs
  have hG : IsKQC G univ (K * K) := b4_isKQC_univ_of_punctured hGh (b4_qc_conj_isKQC hE)
  have hρK : IsKQC ρ univ 1 := isKQC_one_of_conformal isOpen_univ ⟨hρd.differentiableOn, hρi.injOn, hρs⟩
  have hF : IsKQC (G ∘ ρ) univ (1 * (K * K)) := thm7_1_comp hρK hG (subset_univ _)
  rw [one_mul] at hF
  refine ⟨G ∘ ρ, mobiusExt (E (-I)) 1 1 0, hF, ?_, ⟨E (-I), 1, 1, 0, by simp, rfl⟩, ?_⟩
  · rw [image_comp, hρs, hGh.2.2.1]
  · intro z hz
    have hξ : ρ z ∈ unitDisc := hρD ▸ mem_image_of_mem ρ hz
    have hξ' : ‖ρ z‖ < 1 := mem_ball_zero_iff.mp hξ
    have h1 : (1 : ℂ) - ρ z ≠ 0 := cayleyInv_den_ne_zero hξ'
    have hC : -I + 2 * I * (1 - ρ z)⁻¹ = cayleyInv (ρ z) := by
      show -I + 2 * I * (1 - ρ z)⁻¹ = I * (1 + ρ z) / (1 - ρ z)
      field_simp
      ring
    have hfz : f z ∈ Ω := hf.2.2 ▸ mem_image_of_mem f hz
    have hφfz : (cayleyInv ∘ (ρ ∘ ψ)) (f z) = cayleyInv (ρ z) := by
      show cayleyInv (ρ (ψ (f z))) = cayleyInv (ρ z)
      rw [hψf z hz]
    have hEz : E (cayleyInv (ρ z)) = f z := by
      rw [hEq (cayleyInv_mem_upperHalf hξ'), ← hφfz]
      exact hφ.2.1.leftInvOn_invFunOn hfz
    have hne : f z - E (-I) ≠ 0 := by
      intro h0
      rw [← hEz] at h0
      have h2 := hEi (sub_eq_zero.mp h0)
      have h3 : 0 < (cayleyInv (ρ z)).im := cayleyInv_mem_upperHalf hξ'
      rw [h2, neg_im, I_im] at h3
      norm_num at h3
    have hGz : (G ∘ ρ) z = (f z - E (-I))⁻¹ := by
      show (E (-I + 2 * I * (1 - ρ z)⁻¹) - E (-I))⁻¹ = (f z - E (-I))⁻¹
      rw [hC, hEz]
    rw [hGz, mobiusExt_coe (by simpa using inv_ne_zero hne)]
    show (((E (-I) * (f z - E (-I))⁻¹ + 1) / (1 * (f z - E (-I))⁻¹ + 0) : ℂ) : ExtPlane) =
      ((f z : ℂ) : ExtPlane)
    congr 1
    field_simp
    ring

/-- Lemma 3.1 `lem:qc-extension`, `sec03-coarse.tex:16`: there is `Q = Q(K)` such that every
conformal `f : 𝔻 → Ω` and `g : 𝔻 → Ω*` extends to a `Q`-q.c. homeomorphism of `ℂ̂` (a `Q`-q.c.
homeomorphism of `ℂ` followed by a Möbius map), and (as `∞ ∈ Γ`) there is a conformal
`f : ℍ → Ω` with `f(∞) = ∞` extending to a `Q`-q.c. homeomorphism of `ℂ`. -/
theorem lem_qc_extension (K : ℝ) :
    ∃ Q : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      (∀ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω →
        ∃ (F : ℂ → ℂ) (M : ExtPlane → ExtPlane), IsKQC F univ Q ∧ F '' univ = univ ∧
          IsMobius M ∧ ∀ z ∈ unitDisc, M (F z) = (f z : ExtPlane)) ∧
      (∀ g : ℂ → ℂ, IsConformalOnto g unitDisc Ωs →
        ∃ (G : ℂ → ℂ) (M : ExtPlane → ExtPlane), IsKQC G univ Q ∧ G '' univ = univ ∧
          IsMobius M ∧ ∀ z ∈ unitDisc, M (G z) = (g z : ExtPlane)) ∧
      ∃ f : ℂ → ℂ, IsConformalOnto f upperHalf Ω ∧
        ∃ F : ℂ → ℂ, IsKQC F univ Q ∧ F '' univ = univ ∧ EqOn F f upperHalf := by
  -- `Q = K²`.  The hypothesis `¬ IsLinePair Ω Ωs` is not needed: the statement stays true without it
  -- (for a half-plane pair every part holds as well).  Part (B) is part (A) for the swapped pair.
  refine ⟨K * K, fun Ω Ωs h hnl => ?_⟩
  have _hnl := hnl
  exact ⟨fun f hf => s03_qce_partA h hf, fun g hg => s03_qce_partA (s03_qce_swap h) hg,
    s03_qce_partC h⟩

/-- Ring estimate behind Lemma 3.2: for a `Q`-q.c. map `F` of the plane onto itself, `a ≠ c` and `t > 0`,
`t ≤ 16^Q (1 + |F(a + t(a - c)) - F(a)| / |F(c) - F(a)|)^Q`.  With `G(z) = F(a + z(a - c)) - F(a)` the Teichmüller
ring `T_t` (exhausted by `b4_teich_exhaust`) separates `{-1, 0}` from `{t, ∞}`, its image separates
`{0, G(-1)}` from `{G(t), ∞}`; Theorem 7.4 and Teichmüller's modulus theorem (`thm5_3_teichmuller_modulus_theorem`)
give `μ(√(1/(1+t))) ≤ Q μ(√(1/(1+s)))`, and `log(4√t) ≤ μ(√(1/(1+t)))`, `μ(r) ≤ log(4/r)`. -/
theorem s03_tp_ring {F : ℂ → ℂ} {Q : ℝ} (hF : IsKQC F univ Q) (hs : F '' univ = univ)
    {a c : ℂ} (hac : a ≠ c) {t : ℝ} (ht : 0 < t) :
    t ≤ 16 ^ Q * (1 + ‖F (a + t * (a - c)) - F a‖ / ‖F c - F a‖) ^ Q := by
  have hQ1 : 1 ≤ Q := hF.2.1
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ1
  have hFi : Function.Injective F := fun x y hxy => hF.2.2.1.2.1 (mem_univ x) (mem_univ y) hxy
  have hac' : a - c ≠ 0 := sub_ne_zero.mpr hac
  -- the normalized map `G`
  set A : ℂ → ℂ := fun z => a + z * (a - c) with hAdef
  set T : ℂ → ℂ := fun w => w - F a with hTdef
  have hAs : A '' univ = univ := image_univ_of_surjective fun w =>
    ⟨(w - a) / (a - c), by simp only [hAdef]; field_simp; ring⟩
  have hTs : T '' univ = univ := image_univ_of_surjective fun w => ⟨w + F a, by simp [hTdef]⟩
  have hAK : IsKQC A univ 1 := isKQC_one_of_conformal isOpen_univ
    ⟨((differentiable_const a).add (differentiable_id.mul (differentiable_const _))).differentiableOn,
      fun x _ y _ hxy => mul_right_cancel₀ hac' (add_left_cancel hxy), hAs⟩
  have hTK : IsKQC T univ 1 := isKQC_one_of_conformal isOpen_univ
    ⟨(differentiable_id.sub (differentiable_const _)).differentiableOn,
      fun x _ y _ hxy => sub_left_injective hxy, hTs⟩
  set G : ℂ → ℂ := T ∘ (F ∘ A) with hGdef
  have hGK : IsKQC G univ (1 * Q * 1) :=
    thm7_1_comp (thm7_1_comp hAK hF (subset_univ _)) hTK (subset_univ _)
  rw [one_mul, mul_one] at hGK
  have hGs : G '' univ = univ := by rw [hGdef, image_comp, image_comp, hAs, hs, hTs]
  have hhom : IsHomeomorphOnto G univ univ := by
    have h := hGK.2.2.1
    rwa [hGs] at h
  have hG0 : G 0 = 0 := by
    show F (a + 0 * (a - c)) - F a = 0
    rw [zero_mul, add_zero, sub_self]
  set z₁ := G (-1) with hz₁def
  set z₂ := G (t : ℂ) with hz₂def
  have hz₁ : z₁ = F c - F a := by
    show F (a + -1 * (a - c)) - F a = F c - F a
    congr 2
    ring
  have hz₂ : z₂ = F (a + t * (a - c)) - F a := by
    show F (a + (t : ℂ) * (a - c)) - F a = F (a + t * (a - c)) - F a
    rfl
  have hz₁0 : z₁ ≠ 0 := by
    rw [hz₁]
    exact sub_ne_zero.mpr fun h => hac (hFi h).symm
  have hz₂0 : z₂ ≠ 0 := by
    rw [hz₂]
    refine sub_ne_zero.mpr fun h => ?_
    have h1 := hFi h
    have h2 : (t : ℂ) * (a - c) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact ht.ne' (Complex.ofReal_eq_zero.mp h3)
    · exact hac' h3
  have hn₁ : 0 < ‖z₁‖ := norm_pos_iff.mpr hz₁0
  have hn₂ : 0 < ‖z₂‖ := norm_pos_iff.mpr hz₂0
  -- the modulus inequality `π Λ(t) ≤ Q · 2μ(v)`
  set v : ℝ := Real.sqrt (‖z₁‖ / (‖z₁‖ + ‖z₂‖)) with hvdef
  have hμv : 0 ≤ grotzschMu v := ENNReal.toReal_nonneg
  have hmod : π * quadLambda t ≤ Q * (2 * grotzschMu v) := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨B, hB, hBcl, hBmod, P, P', hc, hPc, hQc, hPQ, hP, hQ, hQi⟩ := b4_teich_exhaust ht hε
    obtain ⟨hB', hle, -⟩ := thm7_4_dcModulus_quasi_invariance hGK hB hBcl
    have hsep := b4_image_separates hhom hc hPc hQc hPQ hP hQ hQi
    rw [hG0, Set.pair_comm] at hsep
    have h53 := thm5_3_teichmuller_modulus_theorem hz₁0 hz₂0 hB' hsep
    have hchain : ENNReal.ofReal (π * quadLambda t - ε) ≤ ENNReal.ofReal (Q * (2 * grotzschMu v)) :=
      calc ENNReal.ofReal (π * quadLambda t - ε) ≤ dcModulus B := hBmod
        _ ≤ ENNReal.ofReal Q * dcModulus (G '' B) := hle
        _ ≤ ENNReal.ofReal Q * ENNReal.ofReal (2 * grotzschMu v) := by gcongr
        _ = ENNReal.ofReal (Q * (2 * grotzschMu v)) := (ENNReal.ofReal_mul hQ0).symm
    have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hchain
    linarith
  -- `π Λ(t) = 2 μ(u)`
  set u : ℝ := Real.sqrt (1 / (1 + t)) with hudef
  have hΛ : π * quadLambda t = 2 * grotzschMu u := by
    rw [eq5_17 ht, eq5_7 ht, mul_div_cancel₀ _ Real.pi_ne_zero]
  have hμ : grotzschMu u ≤ Q * grotzschMu v := by nlinarith
  -- bounds on `u`, `v`
  have hu2 : u ^ 2 = 1 / (1 + t) := Real.sq_sqrt (by positivity)
  have hu0 : 0 < u := Real.sqrt_pos.mpr (by positivity)
  have hu1 : u < 1 := by
    rw [hudef, Real.sqrt_lt' one_pos, one_pow, div_lt_one (by linarith)]
    linarith
  have hv2 : v ^ 2 = ‖z₁‖ / (‖z₁‖ + ‖z₂‖) := Real.sq_sqrt (by positivity)
  have hv0 : 0 < v := Real.sqrt_pos.mpr (by positivity)
  have hv1 : v < 1 := by
    rw [hvdef, Real.sqrt_lt' one_pos, one_pow, div_lt_one (by linarith)]
    linarith
  have hlow := em_lower hu0 hu1
  have hup := em_upper hv0 hv1
  -- `X = 4√(1-u²)/u`, `Y = 4/v`: `log X ≤ Q log Y`
  set X : ℝ := 4 * Real.sqrt (1 - u ^ 2) / u with hXdef
  set Y : ℝ := 4 / v with hYdef
  have h1u : 0 < 1 - u ^ 2 := by nlinarith
  have hX0 : 0 < X := div_pos (mul_pos four_pos (Real.sqrt_pos.mpr h1u)) hu0
  have hY0 : 0 < Y := div_pos four_pos hv0
  have hlog : Real.log X ≤ Real.log (Y ^ Q) := by
    rw [Real.log_rpow hY0]
    have hQμ : Q * grotzschMu v ≤ Q * Real.log Y := mul_le_mul_of_nonneg_left hup hQ0
    linarith
  have hXY : X ≤ Y ^ Q := (Real.log_le_log_iff hX0 (Real.rpow_pos_of_pos hY0 Q)).mp hlog
  have hX2 : X ^ 2 = 16 * t := by
    rw [hXdef, div_pow, mul_pow, Real.sq_sqrt h1u.le, hu2]
    field_simp
    ring
  have hY2 : Y ^ 2 = 16 * (1 + ‖z₂‖ / ‖z₁‖) := by
    rw [hYdef, div_pow, hv2]
    field_simp
    ring
  have hYe : (Y ^ 2) ^ Q = (Y ^ Q) ^ 2 := by
    rw [← Real.rpow_natCast Y 2, ← Real.rpow_mul hY0.le, ← Real.rpow_natCast (Y ^ Q) 2,
      ← Real.rpow_mul hY0.le, mul_comm]
  have hXY2 : X ^ 2 ≤ (Y ^ 2) ^ Q := (pow_le_pow_left₀ hX0.le hXY 2).trans_eq hYe.symm
  rw [hX2, hY2, Real.mul_rpow (by norm_num) (by positivity), hz₁, hz₂] at hXY2
  linarith

/-- Circle distortion (Theorem 15.4) in two-point form: `|x - a| = |y - a| > 0` implies
`|F x - F a| ≤ λ(Q) |F y - F a|`. -/
theorem s03_tp_circle {F : ℂ → ℂ} {Q : ℝ} (hF : IsKQC F univ Q) (hs : F '' univ = univ)
    {a x y : ℂ} (hxy : ‖x - a‖ = ‖y - a‖) (hx : x ≠ a) :
    ‖F x - F a‖ ≤ lambdaInv Q * ‖F y - F a‖ := by
  set r := ‖x - a‖ with hrdef
  have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hc := thm15_4_circle_distortion hF hs a hr
  set φ : ℝ → ℝ := fun θ => ‖F (a + r * exp (θ * I)) - F a‖ with hφdef
  have hFc : Continuous F := continuousOn_univ.mp hF.2.2.1.1
  have hpt : ∀ z : ℂ, ‖z - a‖ = r → φ (arg (z - a)) = ‖F z - F a‖ := by
    intro z hz
    show ‖F (a + r * exp (arg (z - a) * I)) - F a‖ = ‖F z - F a‖
    rw [← hz, norm_mul_exp_arg_mul_I, add_sub_cancel]
  have hbdd : BddAbove (range φ) := by
    have hK : IsCompact ((fun z => ‖F z - F a‖) '' sphere a r) :=
      (isCompact_sphere a r).image (continuous_norm.comp (hFc.sub continuous_const))
    refine hK.bddAbove.mono ?_
    rintro _ ⟨θ, rfl⟩
    refine ⟨a + r * exp (θ * I), ?_, rfl⟩
    rw [mem_sphere_iff_norm, add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hbdd' : BddBelow (range φ) := ⟨0, by rintro _ ⟨θ, rfl⟩; exact norm_nonneg _⟩
  have h1 : ‖F x - F a‖ ≤ sSup (range φ) := (hpt x rfl) ▸ le_csSup hbdd ⟨_, rfl⟩
  have h2 : sInf (range φ) ≤ ‖F y - F a‖ := (hpt y hxy.symm) ▸ csInf_le hbdd' ⟨_, rfl⟩
  have hlam : 0 ≤ lambdaInv Q := zero_le_one.trans (td_one_le_lambdaInv hF.2.1)
  calc ‖F x - F a‖ ≤ sSup (range φ) := h1
    _ ≤ lambdaInv Q * sInf (range φ) := hc
    _ ≤ lambdaInv Q * ‖F y - F a‖ := mul_le_mul_of_nonneg_left h2 hlam

/-- One-sided three-point estimate: for `a ≠ c`, `b ≠ a`, with `t = |a - b|/|a - c|` and
`s = |F a - F b|/|F a - F c|`, `t ≤ 16^Q (1 + λ(Q) s)^Q`. -/
theorem s03_tp_one {F : ℂ → ℂ} {Q : ℝ} (hF : IsKQC F univ Q) (hs : F '' univ = univ)
    {a b c : ℂ} (hac : a ≠ c) (hab : a ≠ b) :
    ‖a - b‖ / ‖a - c‖ ≤ 16 ^ Q * (1 + lambdaInv Q * (‖F a - F b‖ / ‖F a - F c‖)) ^ Q := by
  have hQ0 : 0 ≤ Q := zero_le_one.trans hF.2.1
  have hFi : Function.Injective F := fun x y hxy => hF.2.2.1.2.1 (mem_univ x) (mem_univ y) hxy
  have hn : 0 < ‖a - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hac)
  have hFn : 0 < ‖F a - F c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hac (hFi h))
  set t := ‖a - b‖ / ‖a - c‖ with htdef
  have ht : 0 < t := div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hab)) hn
  have hring := s03_tp_ring hF hs hac ht
  set b' := a + t * (a - c) with hb'def
  have hb'n : ‖b' - a‖ = ‖b - a‖ := by
    rw [hb'def, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le, htdef,
      div_mul_cancel₀ _ hn.ne', norm_sub_rev]
  have hb'a : b' ≠ a := by
    intro h
    rw [h, sub_self, norm_zero, norm_sub_rev] at hb'n
    exact hab (sub_eq_zero.mp (norm_eq_zero.mp hb'n.symm))
  have hcirc := s03_tp_circle hF hs hb'n hb'a
  have hlam : 0 ≤ lambdaInv Q := zero_le_one.trans (td_one_le_lambdaInv hF.2.1)
  have hle : ‖F b' - F a‖ / ‖F c - F a‖ ≤ lambdaInv Q * (‖F a - F b‖ / ‖F a - F c‖) := by
    rw [norm_sub_rev (F c), norm_sub_rev (F b) (F a), mul_div_assoc'] at *
    exact div_le_div_of_nonneg_right hcirc hFn.le
  refine hring.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact Real.rpow_le_rpow (by positivity) (by linarith) hQ0

/-- Lemma 3.2, one direction: `t ≤ C max(s^{1/Q}, s^Q)` with `C = A²`, `A = 16^Q (1 + λ(Q))^Q`. -/
theorem s03_tp_qs (Q : ℝ) (hQ : 1 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : ℂ → ℂ, IsKQC F univ Q → F '' univ = univ →
      ∀ a b c : ℂ, a ≠ c →
        ‖a - b‖ / ‖a - c‖ ≤
          C * max ((‖F a - F b‖ / ‖F a - F c‖) ^ (1 / Q)) ((‖F a - F b‖ / ‖F a - F c‖) ^ Q) := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hlam1 : 1 ≤ lambdaInv Q := td_one_le_lambdaInv hQ
  set A : ℝ := 16 ^ Q * (1 + lambdaInv Q) ^ Q with hAdef
  have hA1 : 1 ≤ A := by
    rw [hAdef]
    have h1 : 1 ≤ (16 : ℝ) ^ Q := Real.one_le_rpow (by norm_num) hQ0.le
    have h2 : 1 ≤ (1 + lambdaInv Q) ^ Q := Real.one_le_rpow (by linarith) hQ0.le
    nlinarith
  have hA0 : 0 < A := zero_lt_one.trans_le hA1
  refine ⟨A ^ 2, by positivity, fun F hF hs a b c hac => ?_⟩
  have hFi : Function.Injective F := fun x y hxy => hF.2.2.1.2.1 (mem_univ x) (mem_univ y) hxy
  set s := ‖F a - F b‖ / ‖F a - F c‖ with hsdef
  set t := ‖a - b‖ / ‖a - c‖ with htdef
  have hmax0 : 0 ≤ max (s ^ (1 / Q)) (s ^ Q) :=
    le_max_of_le_left (Real.rpow_nonneg (by positivity) _)
  by_cases hab : a = b
  · have ht0 : t = 0 := by rw [htdef, hab, sub_self, norm_zero, zero_div]
    rw [ht0]
    positivity
  have hn : 0 < ‖a - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hac)
  have ht : 0 < t := div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hab)) hn
  have hFb : 0 < ‖F a - F b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hab (hFi h))
  have hFc : 0 < ‖F a - F c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hac (hFi h))
  have hs0 : 0 < s := div_pos hFb hFc
  -- (I) for `F`
  have hI := s03_tp_one hF hs hac hab
  -- (II) for `F⁻¹` with the points `F a, F c, F b`
  set Fi := Function.invFunOn F univ with hFidef
  have hFiF : ∀ z, Fi (F z) = z := fun z => hFi.injOn.leftInvOn_invFunOn (mem_univ z)
  have hFiK : IsKQC Fi univ Q := by
    have h := thm7_2_inv hF
    rwa [hs] at h
  have hFis : Fi '' univ = univ := image_univ_of_surjective fun z => ⟨F z, hFiF z⟩
  have hII := s03_tp_one hFiK hFis (a := F a) (b := F c) (c := F b) (fun h => hab (hFi h))
    (fun h => hac (hFi h))
  rw [hFiF, hFiF, hFiF] at hII
  have hinvs : ‖F a - F c‖ / ‖F a - F b‖ = 1 / s := by rw [hsdef, one_div_div]
  have hinvt : ‖a - c‖ / ‖a - b‖ = 1 / t := by rw [htdef, one_div_div]
  rw [hinvs, hinvt] at hII
  have hQs : 0 ≤ s ^ Q := Real.rpow_nonneg hs0.le Q
  have hQs' : 0 ≤ s ^ (1 / Q) := Real.rpow_nonneg hs0.le _
  have hAA : A ≤ A ^ 2 := by nlinarith
  rcases le_or_gt 1 s with hs1 | hs1
  · -- `s ≥ 1`: `t ≤ A s^Q`
    have h1 : 1 + lambdaInv Q * s ≤ (1 + lambdaInv Q) * s := by nlinarith
    have h2 : (1 + lambdaInv Q * s) ^ Q ≤ ((1 + lambdaInv Q) * s) ^ Q :=
      Real.rpow_le_rpow (by positivity) h1 hQ0.le
    rw [Real.mul_rpow (by linarith) hs0.le] at h2
    have h3 : t ≤ A * s ^ Q := by
      rw [hAdef, mul_assoc]
      exact hI.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    calc t ≤ A * s ^ Q := h3
      _ ≤ A ^ 2 * s ^ Q := mul_le_mul_of_nonneg_right hAA hQs
      _ ≤ A ^ 2 * max (s ^ (1 / Q)) (s ^ Q) := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  rcases le_or_gt t 1 with ht1 | ht1
  · -- `s < 1`, `t ≤ 1`: `t^Q ≤ A s`
    have h1 : 1 + lambdaInv Q * (1 / t) ≤ (1 + lambdaInv Q) * (1 / t) := by
      rw [mul_one_div, mul_one_div, add_div]
      have : 1 ≤ 1 / t := by rw [le_div_iff₀ ht]; linarith
      linarith [one_le_div_iff.mpr (Or.inl ⟨ht, ht1⟩)]
    have h2 : (1 + lambdaInv Q * (1 / t)) ^ Q ≤ ((1 + lambdaInv Q) * (1 / t)) ^ Q :=
      Real.rpow_le_rpow (by positivity) h1 hQ0.le
    rw [Real.mul_rpow (by linarith) (by positivity), Real.div_rpow zero_le_one ht.le,
      Real.one_rpow] at h2
    have h3 : 1 / s ≤ A / t ^ Q := by
      calc 1 / s ≤ 16 ^ Q * (1 + lambdaInv Q * (1 / t)) ^ Q := hII
        _ ≤ 16 ^ Q * ((1 + lambdaInv Q) ^ Q * (1 / t ^ Q)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = A / t ^ Q := by rw [hAdef]; ring
    have htQ : 0 < t ^ Q := Real.rpow_pos_of_pos ht Q
    have h4 : t ^ Q ≤ A * s := by
      rw [div_le_div_iff₀ hs0 htQ, one_mul] at h3
      linarith
    have h5 : t ≤ (A * s) ^ (1 / Q) := by
      have h6 := Real.rpow_le_rpow htQ.le h4 (by positivity : (0 : ℝ) ≤ 1 / Q)
      rwa [← Real.rpow_mul ht.le, mul_one_div_cancel hQ0.ne', Real.rpow_one] at h6
    rw [Real.mul_rpow hA0.le hs0.le] at h5
    have h7 : A ^ (1 / Q) ≤ A := by
      calc A ^ (1 / Q) ≤ A ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hA1 (by rw [div_le_one hQ0]; exact hQ)
        _ = A := Real.rpow_one A
    calc t ≤ A ^ (1 / Q) * s ^ (1 / Q) := h5
      _ ≤ A ^ 2 * s ^ (1 / Q) := mul_le_mul_of_nonneg_right (h7.trans hAA) hQs'
      _ ≤ A ^ 2 * max (s ^ (1 / Q)) (s ^ Q) := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  · -- `s < 1`, `t > 1`: `t ≤ A` and `s ≥ 1/A`
    have h1 : (1 + lambdaInv Q * (1 / t)) ^ Q ≤ (1 + lambdaInv Q) ^ Q := by
      refine Real.rpow_le_rpow (by positivity) ?_ hQ0.le
      have : 1 / t ≤ 1 := by rw [div_le_one ht]; exact ht1.le
      nlinarith
    have h2 : 1 / s ≤ A := hII.trans (by rw [hAdef]; exact mul_le_mul_of_nonneg_left h1 (by positivity))
    have h3 : (1 + lambdaInv Q * s) ^ Q ≤ (1 + lambdaInv Q) ^ Q := by
      refine Real.rpow_le_rpow (by positivity) ?_ hQ0.le
      nlinarith
    have htA : t ≤ A := hI.trans (by rw [hAdef]; exact mul_le_mul_of_nonneg_left h3 (by positivity))
    have hsA : 1 / A ≤ s := by
      rw [div_le_iff₀ hA0]
      rw [div_le_iff₀ hs0] at h2
      linarith
    have hsQ : s ≤ s ^ (1 / Q) := by
      calc s = s ^ (1 : ℝ) := (Real.rpow_one s).symm
        _ ≤ s ^ (1 / Q) :=
          Real.rpow_le_rpow_of_exponent_ge hs0 hs1.le (by rw [div_le_one hQ0]; exact hQ)
    have h4 : 1 ≤ A * s ^ (1 / Q) := by
      have : 1 ≤ A * s := by rw [div_le_iff₀ hA0] at hsA; linarith
      nlinarith
    calc t ≤ A := htA
      _ ≤ A * (A * s ^ (1 / Q)) := by nlinarith
      _ = A ^ 2 * s ^ (1 / Q) := by ring
      _ ≤ A ^ 2 * max (s ^ (1 / Q)) (s ^ Q) := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

/-- Lemma 3.2 `lem:three-point`, (3.1) `eq:three-point`, `sec03-coarse.tex:38`: with
`η_Q(t) = C' max(t^{1/Q}, t^Q)`, every `Q`-q.c. homeomorphism `F` of `ℂ` satisfies
`|F a - F b|/|F a - F c| ≤ η_Q(|a - b|/|a - c|)`, and so does `F⁻¹` (written at the points
`F a, F b, F c`). -/
theorem lem_three_point (Q : ℝ) (hQ : 1 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : ℂ → ℂ, IsKQC F univ Q → F '' univ = univ →
      ∀ a b c : ℂ, a ≠ c →
        ‖F a - F b‖ / ‖F a - F c‖ ≤
            C * max ((‖a - b‖ / ‖a - c‖) ^ (1 / Q)) ((‖a - b‖ / ‖a - c‖) ^ Q) ∧
          ‖a - b‖ / ‖a - c‖ ≤
            C * max ((‖F a - F b‖ / ‖F a - F c‖) ^ (1 / Q))
              ((‖F a - F b‖ / ‖F a - F c‖) ^ Q) := by
  obtain ⟨C, hC, hqs⟩ := s03_tp_qs Q hQ
  refine ⟨C, hC, fun F hF hs a b c hac => ⟨?_, hqs F hF hs a b c hac⟩⟩
  have hFi : Function.Injective F := fun x y hxy => hF.2.2.1.2.1 (mem_univ x) (mem_univ y) hxy
  set Fi := Function.invFunOn F univ with hFidef
  have hFiF : ∀ z, Fi (F z) = z := fun z => hFi.injOn.leftInvOn_invFunOn (mem_univ z)
  have hFiK : IsKQC Fi univ Q := by
    have h := thm7_2_inv hF
    rwa [hs] at h
  have hFis : Fi '' univ = univ := image_univ_of_surjective fun z => ⟨F z, hFiF z⟩
  have h := hqs Fi hFiK hFis (F a) (F b) (F c) (fun h => hac (hFi h))
  rwa [hFiF, hFiF, hFiF] at h

/-! ## §3.2 Distances in the domain -/

/-- B0: a `K`-quasi pair is a Jordan pair. -/
theorem s03_b0_jordanPair {Ω Ωs : Set ℂ} {K : ℝ} (h : IsKQuasiPair Ω Ωs K) : IsJordanPair Ω Ωs := by
  obtain ⟨F, hK, hs, hU, hL⟩ := h
  obtain ⟨e, rfl⟩ := t1_homeomorph hK hs
  exact ⟨e, hU, hL⟩

/-- B0: the two sides of a `K`-quasi pair are open and disjoint, and `Ω` has a Riemann map. -/
theorem s03_b0_basic {Ω Ωs : Set ℂ} {K : ℝ} (h : IsKQuasiPair Ω Ωs K) :
    IsOpen Ω ∧ IsOpen Ωs ∧ Disjoint Ω Ωs ∧ ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω := by
  have hR := s02_jordanPair_riemannMap (s03_b0_jordanPair h)
  obtain ⟨F, hK, hs, hU, hL⟩ := h
  obtain ⟨e, rfl⟩ := t1_homeomorph hK hs
  refine ⟨hU ▸ e.isOpenMap _ (isOpen_lt continuous_const continuous_im),
    hL ▸ e.isOpenMap _ (isOpen_lt continuous_im continuous_const), ?_, hR⟩
  rw [← hU, ← hL]
  refine (disjoint_image_iff e.injective).2 (disjoint_left.2 fun z h1 h2 => ?_)
  exact lt_asymm (show 0 < z.im from h1) (show z.im < 0 from h2)

/-- B0: for every `Q`-q.c. homeomorphism `F` of the plane with `F(ℍ) = Ω`, `F(ℝ) = Γ ∩ ℂ = curveOf Ω Ωs` and
`F(𝕃) = Ωs`.  (Applies both to the map of `IsKQuasiPair` and to the extension of Lemma 3.1.) -/
theorem s03_b0_image {Ω Ωs : Set ℂ} {K Q : ℝ} (h : IsKQuasiPair Ω Ωs K) {F : ℂ → ℂ}
    (hF : IsKQC F univ Q) (hFs : F '' univ = univ) (hFU : F '' upperHalf = Ω) :
    F '' {z : ℂ | z.im = 0} = curveOf Ω Ωs ∧ F '' lowerHalf = Ωs := by
  obtain ⟨-, -, hdisj, -⟩ := s03_b0_basic h
  obtain ⟨G, hGK, hGs, hGU, hGL⟩ := h
  obtain ⟨g, rfl⟩ := t1_homeomorph hGK hGs
  obtain ⟨e, rfl⟩ := t1_homeomorph hF hFs
  -- membership in `Ω`, `Ωs`, `curveOf` read through `g⁻¹`
  have hΩ : ∀ z, z ∈ Ω ↔ 0 < (g.symm z).im := fun z => by
    rw [← hGU, ← g.preimage_symm]
    rfl
  have hΩs : ∀ z, z ∈ Ωs ↔ (g.symm z).im < 0 := fun z => by
    rw [← hGL, ← g.preimage_symm]
    rfl
  have hC : ∀ z, z ∈ curveOf Ω Ωs ↔ (g.symm z).im = 0 := fun z => by
    show z ∉ Ω ∪ Ωs ↔ _
    rw [mem_union, hΩ, hΩs]
    constructor
    · intro hn
      rcases lt_trichotomy (g.symm z).im 0 with h1 | h1 | h1
      · exact absurd (Or.inr h1) hn
      · exact h1
      · exact absurd (Or.inl h1) hn
    · intro h0 hn
      rcases hn with h1 | h1 <;> linarith
  -- `curveOf = frontier Ω`
  have hfr : ∀ e' : ℂ ≃ₜ ℂ, e' '' {z : ℂ | z.im = 0} = frontier (e' '' upperHalf) := fun e' => by
    rw [← e'.image_frontier]
    congr 1
    exact (frontier_setOfPred_lt_im 0).symm
  have hCfr : curveOf Ω Ωs = frontier Ω := by
    have h2 := hfr g
    rw [hGU, ← g.preimage_symm] at h2
    rw [← h2]
    ext z
    exact hC z
  have h1 : e '' {z : ℂ | z.im = 0} = curveOf Ω Ωs := by rw [hfr e, hFU, hCfr]
  refine ⟨h1, ?_⟩
  -- `e(𝕃)` is the complement of `e(ℍ) ∪ e(ℝ) = Ω ∪ Γ`
  ext z
  rw [← e.preimage_symm]
  have hU' : z ∈ Ω ↔ 0 < (e.symm z).im := by
    rw [← hFU, ← e.preimage_symm]
    rfl
  have hC' : z ∈ curveOf Ω Ωs ↔ (e.symm z).im = 0 := by
    rw [← h1, ← e.preimage_symm]
    rfl
  show (e.symm z).im < 0 ↔ z ∈ Ωs
  constructor
  · intro hz
    by_contra hzs
    have hzΩ : z ∉ Ω := fun hz' => by linarith [hU'.1 hz']
    have hzC : z ∈ curveOf Ω Ωs := fun hu => (mem_union _ _ _).1 hu |>.elim hzΩ hzs
    linarith [hC'.1 hzC]
  · intro hz
    rcases lt_trichotomy (e.symm z).im 0 with h2 | h2 | h2
    · exact h2
    · exact absurd (hC'.2 h2) fun hc => hc (Or.inr hz)
    · exact absurd (hU'.2 h2) fun hc => disjoint_left.1 hdisj hc hz

/-- B0: `Γ ∩ ℂ = curveOf Ω Ωs` is nonempty and disjoint from both sides. -/
theorem s03_b0_curve {Ω Ωs : Set ℂ} {K : ℝ} (h : IsKQuasiPair Ω Ωs K) :
    (curveOf Ω Ωs).Nonempty ∧ curveOf Ω Ωs ⊆ Ωᶜ ∧ curveOf Ω Ωs ⊆ Ωsᶜ := by
  obtain ⟨F, hK, hs, hU, hL⟩ := h
  have hI := (s03_b0_image ⟨F, hK, hs, hU, hL⟩ hK hs hU).1
  refine ⟨hI ▸ ⟨F 0, 0, by simp, rfl⟩, fun z hz hzΩ => hz (Or.inl hzΩ), fun z hz hzΩ => hz (Or.inr hzΩ)⟩

/-- B0: for `w ∈ Ω`, `dist(w, Ωᶜ) = d(w) = dist(w, Γ ∩ ℂ)` (a segment from `w` to a point of `Ωᶜ` meets `Γ`). -/
theorem s03_b0_infDist {Ω Ωs : Set ℂ} {K : ℝ} (h : IsKQuasiPair Ω Ωs K) {w : ℂ} (hw : w ∈ Ω) :
    infDist w Ωᶜ = infDist w (curveOf Ω Ωs) := by
  obtain ⟨hΩo, hΩso, hdisj, -⟩ := s03_b0_basic h
  obtain ⟨hne, hsub, -⟩ := s03_b0_curve h
  refine le_antisymm (infDist_le_infDist_of_subset hsub hne)
    ((le_infDist (hne.mono hsub)).2 fun y hy => ?_)
  -- a point `γ ∈ Γ` on the segment `[w, y]`
  have hγ : ∃ γ ∈ segment ℝ w y, γ ∈ curveOf Ω Ωs := by
    by_contra hno
    have hcov : segment ℝ w y ⊆ Ω ∪ Ωs := fun z hz => by
      by_contra hz'
      exact hno ⟨z, hz, hz'⟩
    have hyΩs : y ∈ Ωs := ((mem_union _ _ _).1 (hcov (right_mem_segment ℝ w y))).resolve_left hy
    obtain ⟨z, -, hz1, hz2⟩ := (convex_segment w y).isPreconnected Ω Ωs hΩo hΩso hcov
      ⟨w, left_mem_segment ℝ w y, hw⟩ ⟨y, right_mem_segment ℝ w y, hyΩs⟩
    exact disjoint_left.1 hdisj hz1 hz2
  obtain ⟨γ, hγs, hγC⟩ := hγ
  have hd := dist_add_dist_of_mem_segment hγs
  calc infDist w (curveOf Ω Ωs) ≤ dist w γ := infDist_le_dist_of_mem hγC
    _ ≤ dist w y := by linarith [dist_nonneg (x := γ) (y := y)]

/-- B0: the same for `w ∈ Ωs`: `dist(w, Ωsᶜ) = dist(w, Γ ∩ ℂ)`. -/
theorem s03_b0_infDist_s {Ω Ωs : Set ℂ} {K : ℝ} (h : IsKQuasiPair Ω Ωs K) {w : ℂ} (hw : w ∈ Ωs) :
    infDist w Ωsᶜ = infDist w (curveOf Ω Ωs) := by
  have h' := s03_b0_infDist (s03_qce_swap h) hw
  rwa [show curveOf Ωs Ω = curveOf Ω Ωs from by
    show (Ωs ∪ Ω)ᶜ = (Ω ∪ Ωs)ᶜ
    rw [union_comm]] at h'

/-- Domain-distance helper: for a conformal `f : ℍ → Ω`,
`d_ρ(f ζ, f ζ') ≤ d_ℍ(ζ, ζ') = 2 arsinh(|ζ - ζ'|/(2√(Im ζ Im ζ')))`. -/
theorem s03_dd_upper {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f upperHalf Ω) {ζ ζ' : ℂ}
    (hζ : ζ ∈ upperHalf) (hζ' : ζ' ∈ upperHalf) :
    poincareDist Ω (f ζ) (f ζ') ≤ 2 * Real.arsinh (‖ζ - ζ'‖ / (2 * √(ζ.im * ζ'.im))) := by
  have hc := s02_cayleyInv_conformal
  obtain ⟨a, ha, rfl⟩ : ζ ∈ cayleyInv '' unitDisc := by rw [hc.2.2]; exact hζ
  obtain ⟨z, hz, rfl⟩ : ζ' ∈ cayleyInv '' unitDisc := by rw [hc.2.2]; exact hζ'
  have hcm : MapsTo cayleyInv unitDisc upperHalf := fun x hx => by
    rw [← hc.2.2]; exact mem_image_of_mem _ hx
  have hg : IsConformalOnto (f ∘ cayleyInv) unitDisc Ω :=
    ⟨hf.1.comp hc.1 hcm, hf.2.1.comp hc.2.1 hcm, by rw [Set.image_comp, hc.2.2, hf.2.2]⟩
  have hle : poincareDist Ω (f (cayleyInv a)) (f (cayleyInv z)) ≤ diskDist a z := by
    unfold poincareDist
    refine csInf_le ⟨0, ?_⟩ ⟨f ∘ cayleyInv, a, z, hg, ha, hz, rfl, rfl, rfl⟩
    rintro _ ⟨g, b, y, -, hb, hy, -, -, rfl⟩
    exact s02_diskDist_nonneg hb hy
  refine hle.trans_eq ?_
  rw [s02_diskDist_cayley ha hz, UpperHalfPlane.dist_eq, Complex.dist_eq]
  rfl

/-- Domain-distance helper: `arcosh(1 + 2t²/(1 - t²)) ≤ 3s` for `0 ≤ t ≤ s ≤ 1/2`. -/
theorem s03_dd_arcosh {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) (hs : s ≤ 1 / 2) :
    Real.arcosh (1 + 2 * t ^ 2 / (1 - t ^ 2)) ≤ 3 * s := by
  have hs0 : 0 ≤ s := ht.trans hts
  have h1t : 3 / 4 ≤ 1 - t ^ 2 := by nlinarith
  have hX : 1 + 2 * t ^ 2 / (1 - t ^ 2) ≤ Real.cosh (3 * s) := by
    have hsh : 3 * s / 2 ≤ Real.sinh (3 * s / 2) := Real.self_le_sinh_iff.2 (by linarith)
    have hc : Real.cosh (3 * s) = 1 + 2 * Real.sinh (3 * s / 2) ^ 2 := by
      rw [show 3 * s = 2 * (3 * s / 2) by ring, Real.cosh_two_mul, Real.cosh_sq]
      ring_nf
    have hq : 2 * t ^ 2 / (1 - t ^ 2) ≤ 8 / 3 * t ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg t]
    have hsq : (3 * s / 2) ^ 2 ≤ Real.sinh (3 * s / 2) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hsh 2
    rw [hc]
    nlinarith [sq_nonneg t, sq_nonneg s]
  have hX1 : 0 < 1 + 2 * t ^ 2 / (1 - t ^ 2) :=
    add_pos_of_pos_of_nonneg one_pos (div_nonneg (by positivity) (by linarith))
  calc Real.arcosh (1 + 2 * t ^ 2 / (1 - t ^ 2)) ≤ Real.arcosh (Real.cosh (3 * s)) :=
        (Real.arcosh_le_arcosh hX1 (Real.cosh_pos _)).2 hX
    _ = 3 * s := Real.arcosh_cosh (by linarith)

/-- Domain-distance helper (Schwarz lemma on a disc `B(w, r) ⊆ Ω`):
`d_ρ(w, w') ≤ 3|w' - w|/r` for `|w' - w| ≤ r/2`. -/
theorem s03_dd_small {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w w' : ℂ}
    {r : ℝ} (hr : 0 < r) (hB : ball w r ⊆ Ω) (hww : ‖w' - w‖ ≤ r / 2) :
    poincareDist Ω w w' ≤ 3 * (‖w' - w‖ / r) := by
  obtain ⟨g, hg⟩ := hΩ
  have hψ : IsConformalOnto (Function.invFunOn g unitDisc) Ω unitDisc := hg.symm isOpen_ball
  have hgψ : ∀ v ∈ Ω, g (Function.invFunOn g unitDisc v) = v := fun v hv =>
    Function.invFunOn_eq (show v ∈ g '' unitDisc by rw [hg.2.2]; exact hv)
  have hψm : MapsTo (Function.invFunOn g unitDisc) Ω unitDisc := fun v hv => by
    have := mem_image_of_mem (Function.invFunOn g unitDisc) hv
    rwa [hψ.2.2] at this
  have hψd := hψ.1
  generalize Function.invFunOn g unitDisc = ψ at hgψ hψm hψd
  have hw : w ∈ Ω := hB (mem_ball_self hr)
  have hw'b : w' ∈ ball w r := by
    rw [mem_ball, dist_eq_norm]; linarith
  have hw' : w' ∈ Ω := hB hw'b
  set a := ψ w with hadef
  set z := ψ w' with hzdef
  have ha : a ∈ unitDisc := hψm hw
  have hz : z ∈ unitDisc := hψm hw'
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  -- `d_ρ(w, w') ≤ d_𝔻(a, z)`
  have hle : poincareDist Ω w w' ≤ diskDist a z := by
    unfold poincareDist
    refine csInf_le ⟨0, ?_⟩ ⟨g, a, z, hg, ha, hz, hgψ w hw, hgψ w' hw', rfl⟩
    rintro _ ⟨g', b, y, -, hb, hy, -, -, rfl⟩
    exact s02_diskDist_nonneg hb hy
  -- Schwarz lemma for `h = M_a ∘ ψ` on `B(w, r)`
  have haa : blaschke a a = 0 := by
    show (a - a) / (1 - conj a * a) = 0
    rw [sub_self, zero_div]
  have hhd : DifferentiableOn ℂ (fun u => blaschke a (ψ u)) (ball w r) :=
    (differentiableOn_blaschke ha1).comp (hψd.mono hB) (fun u hu => hψm (hB hu))
  have hhm : MapsTo (fun u => blaschke a (ψ u)) (ball w r)
      (closedBall ((fun u => blaschke a (ψ u)) w) 1) := by
    intro u hu
    show blaschke a (ψ u) ∈ closedBall (blaschke a a) 1
    rw [haa, mem_closedBall, dist_zero_right]
    exact (blaschke_mem_unitDisc ha1 (mem_ball_zero_iff.mp (hψm (hB hu)))).le
  have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hhd hhm hw'b
  rw [← hadef, ← hzdef, haa, dist_zero_right, dist_eq_norm] at hsch
  have hβ : ‖blaschke a z‖ ≤ ‖w' - w‖ / r := by
    rw [div_mul_eq_mul_div, one_mul] at hsch; exact hsch
  have hβ1 : ‖blaschke a z‖ < 1 := blaschke_mem_unitDisc ha1 hz1
  -- `d_𝔻(a, z) = d_𝔻(0, M_a z)`
  have hdd : diskDist a z = Real.arcosh (1 + 2 * ‖blaschke a z‖ ^ 2 / (1 - ‖blaschke a z‖ ^ 2)) := by
    unfold diskDist
    rw [← s02_diskCoshDist_blaschke ha1 ha1 hz1, haa]
    unfold diskCoshDist
    rw [zero_sub, norm_neg, norm_zero]
    congr 2
    ring
  rw [hdd] at hle
  exact hle.trans (s03_dd_arcosh (norm_nonneg _) hβ (by rw [div_le_iff₀ hr]; linarith))

/-- Domain-distance helper (three-point step): if `F(ℝ) ⊆ Γ` and `m ≤ dist(F ζ, Γ)` then
`|ζ - ζ'| ≤ C₀ max(R^{1/Q}, R^Q) Im ζ` with `R = |F ζ - F ζ'|/m`. -/
theorem s03_dd_tp {Q C₀ : ℝ} (hQ : 1 ≤ Q) {F : ℂ → ℂ}
    (hqs : ∀ a b c : ℂ, a ≠ c → ‖a - b‖ / ‖a - c‖ ≤
      C₀ * max ((‖F a - F b‖ / ‖F a - F c‖) ^ (1 / Q)) ((‖F a - F b‖ / ‖F a - F c‖) ^ Q))
    (hC₀ : 0 < C₀) {Γ : Set ℂ} (hΓ : F '' {z : ℂ | z.im = 0} ⊆ Γ) {ζ ζ' : ℂ} (hζ : 0 < ζ.im)
    {m : ℝ} (hm : 0 < m) (hmd : m ≤ infDist (F ζ) Γ) :
    ‖ζ - ζ'‖ ≤ C₀ * max ((‖F ζ - F ζ'‖ / m) ^ (1 / Q)) ((‖F ζ - F ζ'‖ / m) ^ Q) * ζ.im := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  set x : ℂ := (ζ.re : ℂ) with hxdef
  have hzx : ‖ζ - x‖ = ζ.im := by
    have : ζ - x = (ζ.im : ℂ) * I := by
      apply Complex.ext <;> simp [hxdef]
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hζ]
  have hne : ζ ≠ x := fun h => by
    have := congrArg Complex.im h
    simp [hxdef] at this
    linarith
  have hFx : F x ∈ Γ := hΓ ⟨x, by simp [hxdef], rfl⟩
  have hd : m ≤ ‖F ζ - F x‖ := hmd.trans ((infDist_le_dist_of_mem hFx).trans_eq (dist_eq_norm _ _))
  have hd0 : 0 < ‖F ζ - F x‖ := hm.trans_le hd
  have hsR : ‖F ζ - F ζ'‖ / ‖F ζ - F x‖ ≤ ‖F ζ - F ζ'‖ / m :=
    div_le_div_of_nonneg_left (norm_nonneg _) hm hd
  have hs0 : 0 ≤ ‖F ζ - F ζ'‖ / ‖F ζ - F x‖ := by positivity
  have hmax : max ((‖F ζ - F ζ'‖ / ‖F ζ - F x‖) ^ (1 / Q)) ((‖F ζ - F ζ'‖ / ‖F ζ - F x‖) ^ Q) ≤
      max ((‖F ζ - F ζ'‖ / m) ^ (1 / Q)) ((‖F ζ - F ζ'‖ / m) ^ Q) :=
    max_le_max (Real.rpow_le_rpow hs0 hsR (by positivity)) (Real.rpow_le_rpow hs0 hsR hQ0.le)
  have h1 := (hqs ζ ζ' x hne).trans (mul_le_mul_of_nonneg_left hmax hC₀.le)
  rw [hzx, div_le_iff₀ hζ] at h1
  exact h1

/-- Domain-distance helper (large `R_e`): `2 arsinh(η/2) ≤ 2(3 log(1 + C₀) + Q) log(1 + R)` for
`η = C₀ max(R^{1/Q}, R^Q)` and `R ≥ 1/2`. -/
theorem s03_dd_large {Q C₀ R : ℝ} (hQ : 1 ≤ Q) (hC₀ : 0 < C₀) (hR : 1 / 2 ≤ R) :
    2 * Real.arsinh (C₀ * max (R ^ (1 / Q)) (R ^ Q) / 2) ≤
      2 * (3 * Real.log (1 + C₀) + Q) * Real.log (1 + R) := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hR0 : 0 ≤ R := by linarith
  have h1R : 1 ≤ 1 + R := by linarith
  set η := C₀ * max (R ^ (1 / Q)) (R ^ Q) with hηdef
  have hη0 : 0 ≤ η := mul_nonneg hC₀.le (le_max_of_le_right (Real.rpow_nonneg hR0 _))
  -- `arsinh(η/2) ≤ log(1 + η)`
  have ha : Real.arsinh (η / 2) ≤ Real.log (1 + η) := by
    rw [Real.le_log_iff_exp_le (by linarith), Real.exp_arsinh]
    have : √(1 + (η / 2) ^ 2) ≤ 1 + η / 2 := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    linarith
  -- `η ≤ C₀ (1 + R)^Q`
  have hP1 : 1 ≤ (1 + R) ^ Q := Real.one_le_rpow h1R hQ0.le
  have hηle : η ≤ C₀ * (1 + R) ^ Q := by
    refine mul_le_mul_of_nonneg_left (max_le ?_ ?_) hC₀.le
    · refine (Real.rpow_le_rpow hR0 (show R ≤ 1 + R by linarith) (by positivity)).trans ?_
      refine Real.rpow_le_rpow_of_exponent_le h1R ?_
      rw [div_le_iff₀ hQ0]; nlinarith
    · exact Real.rpow_le_rpow hR0 (by linarith) hQ0.le
  have hlog : Real.log (1 + η) ≤ Real.log (1 + C₀) + Q * Real.log (1 + R) := by
    rw [← Real.log_rpow (by linarith), ← Real.log_mul (by linarith) (by positivity)]
    refine Real.log_le_log (by linarith) ?_
    nlinarith
  -- `log(1 + R) ≥ 1/3`
  have hL : 1 / 3 ≤ Real.log (1 + R) := by
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + R by linarith)
    have : (1 + R)⁻¹ ≤ 2 / 3 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    linarith
  have hlc : 0 ≤ Real.log (1 + C₀) := Real.log_nonneg (by linarith)
  nlinarith

/-- Domain-distance helper: `3R ≤ 5 log(1 + R)` for `0 ≤ R ≤ 1/2`. -/
theorem s03_dd_lin {R : ℝ} (hR0 : 0 ≤ R) (hR : R ≤ 1 / 2) : 3 * R ≤ 5 * Real.log (1 + R) := by
  have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + R by linarith)
  have : 1 - (1 + R)⁻¹ = R / (1 + R) := by field_simp; ring
  rw [this, div_le_iff₀ (by linarith)] at h
  nlinarith [Real.log_nonneg (show 1 ≤ 1 + R by linarith)]

/-- Domain-distance helper: (3.2) on the side `Ω` of a `K`-quasi pair. -/
theorem s03_dd_side (K : ℝ) :
    ∃ C : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
      ∀ w ∈ Ω, ∀ w' ∈ Ω, poincareDist Ω w w' ≤ C * Real.log (1 + ‖w - w'‖ /
        min (infDist w (curveOf Ω Ωs)) (infDist w' (curveOf Ω Ωs))) := by
  by_cases hK : 1 ≤ K
  swap
  · refine ⟨0, fun Ω Ωs h => ?_⟩
    obtain ⟨F, hF, -⟩ := h
    exact absurd hF.2.1 hK
  have hQ : 1 ≤ K * K := by nlinarith
  obtain ⟨C₀, hC₀, hqs⟩ := s03_tp_qs (K * K) hQ
  refine ⟨5 + 2 * (3 * Real.log (1 + C₀) + K * K), fun Ω Ωs h w hw w' hw' => ?_⟩
  obtain ⟨-, -, -, hR⟩ := s03_b0_basic h
  obtain ⟨g, hg⟩ := hR
  set Γ := curveOf Ω Ωs with hΓdef
  have hd : 0 < infDist w Γ := by rw [← s03_b0_infDist h hw]; exact s02_infDist_pos hg hw
  have hd' : 0 < infDist w' Γ := by rw [← s03_b0_infDist h hw']; exact s02_infDist_pos hg hw'
  set m := min (infDist w Γ) (infDist w' Γ) with hmdef
  have hm : 0 < m := lt_min hd hd'
  set R := ‖w - w'‖ / m with hRdef
  have hR0 : 0 ≤ R := by positivity
  have hL0 : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
  have hcoef : 0 ≤ 2 * (3 * Real.log (1 + C₀) + K * K) := by
    have := Real.log_nonneg (show 1 ≤ 1 + C₀ by linarith); positivity
  rcases le_or_gt R (1 / 2) with hRs | hRl
  · -- small `R_e`: Schwarz lemma on the disc `B(w, d(w))` (or `B(w', d(w'))`)
    have h3 : poincareDist Ω w w' ≤ 3 * R := by
      rcases le_total (infDist w Γ) (infDist w' Γ) with hle | hle
      · have hmw : m = infDist w Γ := min_eq_left hle
        have hB : ball w (infDist w Γ) ⊆ Ω := by
          rw [← s03_b0_infDist h hw]; exact ball_infDist_compl_subset
        have hs := s03_dd_small (w' := w') ⟨g, hg⟩ hd hB (by
          rw [norm_sub_rev]
          rw [hRdef, hmw, div_le_iff₀ hd] at hRs; linarith)
        rw [norm_sub_rev, ← hmw] at hs
        exact hs
      · have hmw : m = infDist w' Γ := min_eq_right hle
        have hB : ball w' (infDist w' Γ) ⊆ Ω := by
          rw [← s03_b0_infDist h hw']; exact ball_infDist_compl_subset
        have hs := s03_dd_small (w' := w) ⟨g, hg⟩ hd' hB (by
          rw [hRdef, hmw, div_le_iff₀ hd'] at hRs; linarith)
        rw [← hmw, s02_poincareDist_comm ⟨g, hg⟩ hw' hw] at hs
        exact hs
    calc poincareDist Ω w w' ≤ 3 * R := h3
      _ ≤ 5 * Real.log (1 + R) := s03_dd_lin hR0 hRs
      _ ≤ (5 + 2 * (3 * Real.log (1 + C₀) + K * K)) * Real.log (1 + R) := by nlinarith
  · -- large `R_e`: the quasiconformal parametrisation by `ℍ` and the three-point estimate
    obtain ⟨f, hf, F, hF, hFs, hFf⟩ := s03_qce_partC h
    have hFU : F '' upperHalf = Ω := hFf.image_eq.trans hf.2.2
    have hΓF : F '' {z : ℂ | z.im = 0} ⊆ Γ := (s03_b0_image h hF hFs hFU).1.le
    obtain ⟨ζ, hζ, rfl⟩ : w ∈ f '' upperHalf := by rw [hf.2.2]; exact hw
    obtain ⟨ζ', hζ', rfl⟩ : w' ∈ f '' upperHalf := by rw [hf.2.2]; exact hw'
    have hy : 0 < ζ.im := hζ
    have hy' : 0 < ζ'.im := hζ'
    have hqF := hqs F hF hFs
    set η := C₀ * max (R ^ (1 / (K * K))) (R ^ (K * K)) with hηdef
    have hη0 : 0 ≤ η := mul_nonneg hC₀.le (le_max_of_le_right (Real.rpow_nonneg hR0 _))
    have e1 := s03_dd_tp (ζ' := ζ') hQ hqF hC₀ hΓF hy hm (by rw [hFf hζ]; exact min_le_left _ _)
    have e2 := s03_dd_tp (ζ' := ζ) hQ hqF hC₀ hΓF hy' hm (by rw [hFf hζ']; exact min_le_right _ _)
    rw [hFf hζ, hFf hζ'] at e1 e2
    rw [norm_sub_rev (f ζ'), ← hRdef, ← hηdef] at e2
    rw [← hRdef, ← hηdef] at e1
    rw [norm_sub_rev ζ'] at e2
    have hsq : ‖ζ - ζ'‖ ≤ η * √(ζ.im * ζ'.im) := by
      have hpos : 0 < ζ.im * ζ'.im := mul_pos hy hy'
      have h2 : ‖ζ - ζ'‖ ^ 2 ≤ (η * ζ.im) * (η * ζ'.im) := by
        rw [sq]; exact mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
      calc ‖ζ - ζ'‖ = √(‖ζ - ζ'‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ √((η * ζ.im) * (η * ζ'.im)) := Real.sqrt_le_sqrt h2
        _ = η * √(ζ.im * ζ'.im) := by
          rw [show (η * ζ.im) * (η * ζ'.im) = η ^ 2 * (ζ.im * ζ'.im) by ring,
            Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hη0]
    have hsqrt : 0 < √(ζ.im * ζ'.im) := Real.sqrt_pos.2 (mul_pos hy hy')
    have hup := s03_dd_upper hf hζ hζ'
    have harg : ‖ζ - ζ'‖ / (2 * √(ζ.im * ζ'.im)) ≤ η / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    calc poincareDist Ω (f ζ) (f ζ') ≤ 2 * Real.arsinh (η / 2) :=
          hup.trans (by nlinarith [Real.arsinh_le_arsinh.2 harg])
      _ ≤ 2 * (3 * Real.log (1 + C₀) + K * K) * Real.log (1 + R) :=
          s03_dd_large hQ hC₀ hRl.le
      _ ≤ (5 + 2 * (3 * Real.log (1 + C₀) + K * K)) * Real.log (1 + R) := by nlinarith

/-- Lemma 3.3 `lem:domain-distance`, (3.2) `eq:domain-distance`, `sec03-coarse.tex:75`:
`d_ρ(w, w') ≤ C(K) log(1 + R_e)`, `R_e = |w - w'|/min{d(w), d(w')}`; the same in `Ω*`. -/
theorem lem_domain_distance (K : ℝ) :
    ∃ C : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      (∀ w ∈ Ω, ∀ w' ∈ Ω, poincareDist Ω w w' ≤ C * Real.log (1 + ‖w - w'‖ /
        min (infDist w (curveOf Ω Ωs)) (infDist w' (curveOf Ω Ωs)))) ∧
      ∀ w ∈ Ωs, ∀ w' ∈ Ωs, poincareDist Ωs w w' ≤ C * Real.log (1 + ‖w - w'‖ /
        min (infDist w (curveOf Ω Ωs)) (infDist w' (curveOf Ω Ωs))) := by
  -- The hypothesis `¬ IsLinePair Ω Ωs` is not needed: the statement stays true without it.
  -- The side `Ω*` is the side `Ω` of the swapped pair, with the same curve.
  obtain ⟨C, hC⟩ := s03_dd_side K
  refine ⟨C, fun Ω Ωs h hnl => ⟨hC Ω Ωs h, ?_⟩⟩
  have _hnl := hnl
  have hcs : curveOf Ωs Ω = curveOf Ω Ωs := by rw [curveOf, curveOf, union_comm]
  have h' := hC Ωs Ω (s03_qce_swap h)
  rwa [hcs] at h'

/-! ## §3.3 Interior points on both sides and the width of the gap -/

/-- Corkscrew helper: a finite point of the curve of `F(ℍ), F(𝕃)` (`F` onto `ℂ`) is `F(a)` for
some real `a`. -/
theorem s03_ck_real {Ω Ωs : Set ℂ} {F : ℂ → ℂ} (hs : F '' univ = univ)
    (hU : F '' upperHalf = Ω) (hL : F '' lowerHalf = Ωs) {x : ℂ} (hx : x ∈ curveOf Ω Ωs) :
    ∃ a : ℝ, F a = x := by
  obtain ⟨z, -, rfl⟩ : x ∈ F '' univ := by rw [hs]; exact mem_univ x
  refine ⟨z.re, ?_⟩
  have hz : z.im = 0 := by
    rcases lt_trichotomy z.im 0 with h | h | h
    · exact absurd (Or.inr (by rw [← hL]; exact mem_image_of_mem F h)) hx
    · exact h
    · exact absurd (Or.inl (by rw [← hU]; exact mem_image_of_mem F h)) hx
  congr 1
  exact Complex.ext (by simp) (by simp [hz])

/-- Corkscrew helper: `|(a + t i) - a| = |t|`. -/
theorem s03_ck_norm (a t : ℝ) : ‖((a : ℂ) + t * I) - a‖ = |t| := by
  simp

/-- Corkscrew helper: from `1 ≤ C max(R^{1/K}, R^K)` with `C, K ≥ 1`, `R ≥ 0` follows
`(1/C)^K ≤ R`. -/
theorem s03_ck_rpow {R C K : ℝ} (hR : 0 ≤ R) (hC : 1 ≤ C) (hK : 1 ≤ K)
    (h : 1 ≤ C * max (R ^ (1 / K)) (R ^ K)) : (1 / C) ^ K ≤ R := by
  have hC0 : 0 < C := by linarith
  have hK0 : 0 < K := by linarith
  have hc1 : 1 / C ≤ 1 := by rw [div_le_one hC0]; exact hC
  have hc0 : 0 ≤ 1 / C := by positivity
  have hm : 1 / C ≤ max (R ^ (1 / K)) (R ^ K) := by
    rw [div_le_iff₀ hC0, mul_comm]; exact h
  rcases le_max_iff.1 hm with h1 | h1
  · calc (1 / C) ^ K ≤ (R ^ (1 / K)) ^ K := Real.rpow_le_rpow hc0 h1 hK0.le
      _ = R := by rw [one_div, Real.rpow_inv_rpow hR hK0.ne']
  · by_cases hR1 : 1 ≤ R
    · exact (Real.rpow_le_one hc0 hc1 hK0.le).trans hR1
    · push Not at hR1
      calc (1 / C) ^ K ≤ 1 / C := by
            simpa using Real.rpow_le_rpow_of_exponent_ge' hc0 hc1 zero_le_one hK
        _ ≤ R ^ K := h1
        _ ≤ R := by simpa using Real.rpow_le_rpow_of_exponent_ge' hR hR1.le zero_le_one hK

/-- Corkscrew helper: for a map `F` with the inverse three-point bound (constant `C`), real `a, s`
and `t ≠ 0`, `(1/C)^K |F(a + t i) - F(a)| ≤ |F(a + t i) - F(s)|`. -/
theorem s03_ck_far {F : ℂ → ℂ} {C K : ℝ} (hC : 1 ≤ C) (hK : 1 ≤ K)
    (h3 : ∀ a b c : ℂ, a ≠ c → ‖a - b‖ / ‖a - c‖ ≤
      C * max ((‖F a - F b‖ / ‖F a - F c‖) ^ (1 / K)) ((‖F a - F b‖ / ‖F a - F c‖) ^ K))
    (hFi : Function.Injective F) (a t s : ℝ) (ht : t ≠ 0) :
    (1 / C) ^ K * ‖F (a + t * I) - F a‖ ≤ ‖F (a + t * I) - F s‖ := by
  have hne : (a : ℂ) + t * I ≠ a := by
    intro h
    apply ht
    simpa using congrArg Complex.im h
  have hpos : 0 < ‖F (a + t * I) - F a‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 fun h => hne (hFi h))
  have h1 : 1 ≤ ‖((a : ℂ) + t * I) - s‖ / ‖((a : ℂ) + t * I) - a‖ := by
    rw [one_le_div (norm_pos_iff.2 (sub_ne_zero.2 hne)), s03_ck_norm]
    have := Complex.abs_im_le_norm (((a : ℂ) + t * I) - s)
    simpa using this
  have := s03_ck_rpow (div_nonneg (norm_nonneg _) hpos.le) hC hK (h1.trans (h3 _ _ _ hne))
  rwa [le_div_iff₀ hpos] at this

/-- Lemma 3.4 `lem:corkscrew`, `sec03-coarse.tex:102`: there is `c₁ = c₁(K) ∈ (0, 1]` such that
for `x ∈ Γ ∩ ℂ` and `r > 0` there are `y₊ ∈ Ω`, `y₋ ∈ Ω*` with `|y± - x| ≤ r/c₁` and
`dist(y±, Γ) ≥ c₁ r`. -/
theorem lem_corkscrew (K : ℝ) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 ∧ ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ x ∈ curveOf Ω Ωs, ∀ r : ℝ, 0 < r →
        ∃ yp ∈ Ω, ∃ ym ∈ Ωs, ‖yp - x‖ ≤ r / c₁ ∧ ‖ym - x‖ ≤ r / c₁ ∧
          c₁ * r ≤ infDist yp (curveOf Ω Ωs) ∧ c₁ * r ≤ infDist ym (curveOf Ω Ωs) := by
  -- `c₁ = (1/C)^K / C` with `C ≥ 1` the constant of Lemma 3.2 for `Q = K`; `y± = F(a ± t i)` with
  -- `x = F(a)` and `t` chosen (intermediate value theorem) so that `|F(a + t i) - x| = r`.  The
  -- hypothesis `¬ IsLinePair Ω Ωs` is not needed: the statement stays true without it.
  by_cases hK : 1 ≤ K
  swap
  · refine ⟨1, one_pos, le_rfl, fun Ω Ωs h => ?_⟩
    obtain ⟨F, hF, -⟩ := h
    exact absurd hF.2.1 hK
  obtain ⟨C₀, -, h3₀⟩ := lem_three_point K hK
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max C₀ 1 := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := hC ▸ le_max_right _ _
  have hC0 : 0 < C := by linarith
  have hK0 : 0 < K := by linarith
  have hcK : 0 < (1 / C) ^ K := by positivity
  have hcK1 : (1 / C) ^ K ≤ 1 :=
    Real.rpow_le_one (by positivity) (by rw [div_le_one hC0]; exact hC1) hK0.le
  refine ⟨(1 / C) ^ K / C, by positivity,
    (div_le_one hC0).2 (hcK1.trans hC1), fun Ω Ωs h hnl x hx r hr => ?_⟩
  have _hnl := hnl
  obtain ⟨F, hF, hs, hU, hL⟩ := h
  have hFc : Continuous F := continuousOn_univ.mp hF.2.2.1.1
  have hFi : Function.Injective F := injOn_univ.mp hF.2.2.1.2.1
  -- Lemma 3.2 with the constant `C ≥ C₀`
  have hmx : ∀ u : ℝ, 0 ≤ u → 0 ≤ max (u ^ (1 / K)) (u ^ K) := fun u hu =>
    le_max_of_le_left (Real.rpow_nonneg hu _)
  have h3 : ∀ a b c : ℂ, a ≠ c →
      ‖F a - F b‖ / ‖F a - F c‖ ≤
          C * max ((‖a - b‖ / ‖a - c‖) ^ (1 / K)) ((‖a - b‖ / ‖a - c‖) ^ K) ∧
        ‖a - b‖ / ‖a - c‖ ≤
          C * max ((‖F a - F b‖ / ‖F a - F c‖) ^ (1 / K))
            ((‖F a - F b‖ / ‖F a - F c‖) ^ K) := by
    intro a b c hac
    obtain ⟨h1, h2⟩ := h3₀ F hF hs a b c hac
    have hCC : C₀ ≤ C := hC ▸ le_max_left _ _
    exact ⟨h1.trans (mul_le_mul_of_nonneg_right hCC
        (hmx _ (div_nonneg (norm_nonneg _) (norm_nonneg _)))),
      h2.trans (mul_le_mul_of_nonneg_right hCC
        (hmx _ (div_nonneg (norm_nonneg _) (norm_nonneg _))))⟩
  obtain ⟨a, rfl⟩ := s03_ck_real hs hU hL hx
  have hne : ∀ t : ℝ, t ≠ 0 → (a : ℂ) + t * I ≠ a := fun t ht h => ht (by
    simpa using congrArg Complex.im h)
  have hgp : ∀ t : ℝ, t ≠ 0 → 0 < ‖F (a + t * I) - F a‖ := fun t ht =>
    norm_pos_iff.2 (sub_ne_zero.2 fun h => hne t ht (hFi h))
  have hgc : Continuous fun t : ℝ => ‖F (a + t * I) - F a‖ := by fun_prop
  -- some `T ≥ 0` has `|F(a + T i) - F(a)| ≥ r`
  obtain ⟨T, hT0, hTr⟩ : ∃ T : ℝ, 0 ≤ T ∧ r ≤ ‖F (a + T * I) - F a‖ := by
    by_contra hno
    push Not at hno
    have hg1 := hgp 1 one_ne_zero
    obtain ⟨S, hS⟩ : ∃ S : ℝ, S = r / ‖F (a + (1 : ℝ) * I) - F a‖ := ⟨_, rfl⟩
    have hS0 : 0 ≤ S := hS ▸ div_nonneg hr.le hg1.le
    obtain ⟨T, hT⟩ : ∃ T : ℝ, T = C * max (S ^ (1 / K)) (S ^ K) + 1 := ⟨_, rfl⟩
    have hT0 : 0 ≤ T := by rw [hT]; have := hmx S hS0; positivity
    have h := (h3 a (a + T * I) (a + (1 : ℝ) * I) (hne 1 one_ne_zero).symm).2
    rw [norm_sub_rev (a : ℂ), norm_sub_rev (a : ℂ), s03_ck_norm, s03_ck_norm, abs_one,
      abs_of_nonneg hT0, div_one, norm_sub_rev (F a), norm_sub_rev (F a)] at h
    have hle : ‖F (a + T * I) - F a‖ / ‖F (a + (1 : ℝ) * I) - F a‖ ≤ S := by
      rw [hS]
      exact div_le_div_of_nonneg_right (hno T hT0).le hg1.le
    have hq0 : 0 ≤ ‖F (a + T * I) - F a‖ / ‖F (a + (1 : ℝ) * I) - F a‖ := by positivity
    have hmono : max ((‖F (a + T * I) - F a‖ / ‖F (a + (1 : ℝ) * I) - F a‖) ^ (1 / K))
        ((‖F (a + T * I) - F a‖ / ‖F (a + (1 : ℝ) * I) - F a‖) ^ K) ≤
        max (S ^ (1 / K)) (S ^ K) :=
      max_le_max (Real.rpow_le_rpow hq0 hle (by positivity))
        (Real.rpow_le_rpow hq0 hle hK0.le)
    have := mul_le_mul_of_nonneg_left hmono hC0.le
    linarith
  -- the intermediate value theorem gives `t ∈ (0, T]` with `|F(a + t i) - F(a)| = r`
  obtain ⟨t, ⟨ht0, -⟩, htr⟩ := intermediate_value_Icc hT0 hgc.continuousOn
    (show r ∈ Icc (‖F (a + (0 : ℝ) * I) - F a‖) (‖F (a + T * I) - F a‖) by
      simp only [ofReal_zero, zero_mul, add_zero, sub_self, norm_zero]
      exact ⟨hr.le, hTr⟩)
  have ht : 0 < t := by
    rcases ht0.lt_or_eq with h | h
    · exact h
    · subst h
      simp at htr
      linarith
  simp only at htr
  -- `m = |F(a - t i) - F(a)|` is comparable to `r`
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ‖F (a + (-t : ℝ) * I) - F a‖ := ⟨_, rfl⟩
  have hm0 : 0 < m := hm ▸ hgp (-t) (neg_ne_zero.2 ht.ne')
  have hr1 : ‖(a : ℂ) - (a + (-t : ℝ) * I)‖ / ‖(a : ℂ) - (a + t * I)‖ = 1 := by
    rw [norm_sub_rev (a : ℂ), norm_sub_rev (a : ℂ), s03_ck_norm, s03_ck_norm, abs_neg,
      div_self (abs_pos.2 ht.ne').ne']
  have hr1' : ‖(a : ℂ) - (a + t * I)‖ / ‖(a : ℂ) - (a + (-t : ℝ) * I)‖ = 1 := by
    rw [norm_sub_rev (a : ℂ), norm_sub_rev (a : ℂ), s03_ck_norm, s03_ck_norm, abs_neg,
      div_self (abs_pos.2 ht.ne').ne']
  have hmr : m ≤ C * r := by
    have h := (h3 a (a + (-t : ℝ) * I) (a + t * I) (hne t ht.ne').symm).1
    rw [hr1, Real.one_rpow, Real.one_rpow, max_self, mul_one, norm_sub_rev (F a),
      norm_sub_rev (F a), htr, ← hm, div_le_iff₀ hr] at h
    linarith
  have hrm : r ≤ C * m := by
    have h := (h3 a (a + t * I) (a + (-t : ℝ) * I) (hne (-t) (neg_ne_zero.2 ht.ne')).symm).1
    rw [hr1', Real.one_rpow, Real.one_rpow, max_self, mul_one, norm_sub_rev (F a),
      norm_sub_rev (F a), htr, ← hm, div_le_iff₀ hm0] at h
    linarith
  have hnon : (curveOf Ω Ωs).Nonempty := ⟨_, hx⟩
  have hfar : ∀ t' : ℝ, t' ≠ 0 → ∀ y ∈ curveOf Ω Ωs,
      (1 / C) ^ K * ‖F (a + t' * I) - F a‖ ≤ dist (F (a + t' * I)) y := by
    intro t' ht' y hy
    obtain ⟨s, rfl⟩ := s03_ck_real hs hU hL hy
    rw [dist_eq_norm]
    exact s03_ck_far hC1 hK (fun a b c hac => (h3 a b c hac).2) hFi a t' s ht'
  have hc1 : (1 / C) ^ K / C * C = (1 / C) ^ K := div_mul_cancel₀ _ hC0.ne'
  refine ⟨F (a + t * I), ?_, F (a + (-t : ℝ) * I), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hU]
    exact mem_image_of_mem F (show (0 : ℝ) < ((a : ℂ) + t * I).im by simpa using ht)
  · rw [← hL]
    exact mem_image_of_mem F (show ((a : ℂ) + (-t : ℝ) * I).im < 0 by simpa using ht)
  · rw [htr, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left (hcK1.trans hC1) hr.le,
      div_le_self hcK.le hC1]
  · rw [← hm, le_div_iff₀ (by positivity)]
    have : m * ((1 / C) ^ K / C) ≤ C * r * ((1 / C) ^ K / C) :=
      mul_le_mul_of_nonneg_right hmr (by positivity)
    nlinarith
  · refine (le_infDist hnon).2 fun y hy => le_trans ?_ (hfar t ht.ne' y hy)
    rw [htr]
    have := div_le_self hcK.le hC1
    nlinarith
  · refine (le_infDist hnon).2 fun y hy => le_trans ?_ (hfar (-t) (neg_ne_zero.2 ht.ne') y hy)
    rw [← hm]
    have : (1 / C) ^ K / C * r ≤ (1 / C) ^ K / C * (C * m) :=
      mul_le_mul_of_nonneg_left hrm (by positivity)
    nlinarith

/-- Width helper: `d(q, S) ≤ 0` for `q ∈ S ⊆ ℍ³`. -/
theorem s03_wd_self {q : ℂ × ℝ} {S : Set (ℂ × ℝ)} (hq : q ∈ S) (hS : S ⊆ UHS) :
    hdistSet q S ≤ 0 := by
  have hq2 : 0 < q.2 := hS hq
  refine (csInf_le ⟨0, ?_⟩ (mem_image_of_mem _ hq)).trans_eq ?_
  · rintro _ ⟨p, hp, rfl⟩
    have hp2 : 0 < p.2 := hS hp
    exact Real.arcosh_nonneg (le_add_of_nonneg_right (div_nonneg
      (add_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_pos (mul_pos two_pos hq2) hp2).le))
  · simp [hdist, coshDist, Real.arcosh_zero]

/-- Width helper: the union of horoballs lies in `ℍ³`. -/
theorem s03_wd_horoUnion_sub (Ω : Set ℂ) : horoUnion Ω ⊆ UHS := by
  intro p hp
  simp only [horoUnion, mem_iUnion] at hp
  obtain ⟨w, -, hp⟩ := hp
  exact hp.1

/-- Width helper: a point `y ∈ Ω'` with `d(y) ≥ c ξ` and `|W - y| ≤ B ξ` gives
`d(q, U') ≤ log((B² + 1)/c)` for `q = (W, ξ)` (Koebe and (2.16)). -/
theorem s03_wd_est {Ω' Ωo : Set ℂ} (hJ : IsJordanPair Ω' Ωo) {q : ℂ × ℝ} (hq : q ∈ UHS)
    {y : ℂ} (hy : y ∈ Ω') {c B : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hd : c * q.2 ≤ infDist y Ω'ᶜ)
    (hW : ‖q.1 - y‖ ≤ B * q.2) :
    hdistSet q (horoUnion Ω') ≤ Real.log ((B ^ 2 + 1) / c) := by
  have hξ : 0 < q.2 := hq
  have hM : 1 ≤ (B ^ 2 + 1) / c := by rw [le_div_iff₀ hc]; nlinarith [sq_nonneg B]
  by_cases hqU : q ∈ horoUnion Ω'
  · exact (s03_wd_self hqU (s03_wd_horoUnion_sub Ω')).trans (Real.log_nonneg hM)
  obtain ⟨w, hw, hmin, hdU⟩ := eq_dist_U hJ hq hqU
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  have hN : ∀ v : ℂ, 0 < ‖q.1 - v‖ ^ 2 + q.2 ^ 2 := fun v =>
    add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hξ 2)
  have hΦw : 0 < horoPhi Ω' q w :=
    div_pos (mul_pos (s02_poincareDensity_pos ⟨f, hf⟩ hw) (hN w)) (mul_pos two_pos hξ)
  have hyf : y ∈ f '' unitDisc := by rw [hf.2.2]; exact hy
  obtain ⟨z, hz, hfz⟩ := hyf
  have hk := (lem_koebe_a hf hz).2.2.2
  rw [hfz] at hk
  have hcξ : 0 < c * q.2 := mul_pos hc hξ
  have hlam : poincareDensity Ω' y ≤ 2 / (c * q.2) :=
    hk.trans (div_le_div_of_nonneg_left (by norm_num) hcξ hd)
  have hl0 := s02_poincareDensity_pos ⟨f, hf⟩ hy
  have hN' : ‖q.1 - y‖ ^ 2 + q.2 ^ 2 ≤ (B ^ 2 + 1) * q.2 ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hW 2
    nlinarith
  have hΦy : horoPhi Ω' q y ≤ (B ^ 2 + 1) / c := by
    unfold horoPhi
    rw [div_le_div_iff₀ (mul_pos two_pos hξ) hc]
    calc poincareDensity Ω' y * (‖q.1 - y‖ ^ 2 + q.2 ^ 2) * c ≤
        2 / (c * q.2) * ((B ^ 2 + 1) * q.2 ^ 2) * c :=
          mul_le_mul_of_nonneg_right (mul_le_mul hlam hN' (hN y).le (div_pos two_pos hcξ).le)
            hc.le
      _ = (B ^ 2 + 1) * (2 * q.2) := by
          field_simp
  rw [hdU]
  exact Real.log_le_log hΦw ((hmin y hy).trans hΦy)

/-- Width helper: if `q = (W, ξ) ∈ 𝒩` then `dist(W, Γ) < ξ` (Koebe: otherwise `Φ_q(W) ≤ 1`). -/
theorem s03_wd_near {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) (hJs : IsJordanPair Ωs Ω)
    (hdE : ∀ w ∈ Ω, infDist w Ωᶜ = infDist w (curveOf Ω Ωs))
    (hdEs : ∀ w ∈ Ωs, infDist w Ωsᶜ = infDist w (curveOf Ω Ωs))
    {q : ℂ × ℝ} (hq : q ∈ gap Ω Ωs) : infDist q.1 (curveOf Ω Ωs) < q.2 := by
  obtain ⟨hqU, hqn⟩ := hq
  have hξ : 0 < q.2 := hqU
  by_contra hle
  push Not at hle
  have key : ∀ {Ω' Ωo : Set ℂ}, IsJordanPair Ω' Ωo → q.1 ∈ Ω' → q.2 ≤ infDist q.1 Ω'ᶜ →
      q ∈ horoUnion Ω' := by
    intro Ω' Ωo hJ' hW' hd
    obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ'
    have hy : q.1 ∈ f '' unitDisc := by rw [hf.2.2]; exact hW'
    obtain ⟨z, hz, hfz⟩ := hy
    have hk := (lem_koebe_a hf hz).2.2.2
    rw [hfz] at hk
    have hlam : poincareDensity Ω' q.1 ≤ 2 / q.2 :=
      hk.trans (div_le_div_of_nonneg_left (by norm_num) hξ hd)
    simp only [horoUnion, mem_iUnion]
    refine ⟨q.1, hW', ?_⟩
    show q ∈ UHS ∧ horoPhi Ω' q q.1 ≤ 1
    refine ⟨hqU, ?_⟩
    unfold horoPhi
    rw [sub_self, norm_zero, div_le_one (mul_pos two_pos hξ)]
    calc poincareDensity Ω' q.1 * (0 ^ 2 + q.2 ^ 2) ≤ 2 / q.2 * (0 ^ 2 + q.2 ^ 2) :=
          mul_le_mul_of_nonneg_right hlam (by positivity)
      _ = 2 * q.2 := by
          field_simp
          ring
  have hW : q.1 ∈ Ω ∪ Ωs := by
    by_contra hW
    have : infDist q.1 (curveOf Ω Ωs) = 0 := infDist_zero_of_mem hW
    linarith
  rcases hW with hW | hW
  · exact hqn (Or.inl (key hJ hW (by rw [hdE _ hW]; exact hle)))
  · exact hqn (Or.inr (key hJs hW (by rw [hdEs _ hW]; exact hle)))

/-- Width helper: for `q = (W, ξ)` with `|W - x| ≤ A ξ` for some `x ∈ Γ`, the corkscrew points of
Lemma 3.4 at `x` with `r = ξ` give `d(q, U), d(q, U*) ≤ log(((A + 1/c₁)² + 1)/c₁)`. -/
theorem s03_wd_side {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) (hJs : IsJordanPair Ωs Ω)
    (hdE : ∀ w ∈ Ω, infDist w Ωᶜ = infDist w (curveOf Ω Ωs))
    (hdEs : ∀ w ∈ Ωs, infDist w Ωsᶜ = infDist w (curveOf Ω Ωs)) {c₁ : ℝ} (hc : 0 < c₁)
    (hc1 : c₁ ≤ 1)
    (hck : ∀ x ∈ curveOf Ω Ωs, ∀ r : ℝ, 0 < r →
      ∃ yp ∈ Ω, ∃ ym ∈ Ωs, ‖yp - x‖ ≤ r / c₁ ∧ ‖ym - x‖ ≤ r / c₁ ∧
        c₁ * r ≤ infDist yp (curveOf Ω Ωs) ∧ c₁ * r ≤ infDist ym (curveOf Ω Ωs))
    {q : ℂ × ℝ} (hq : q ∈ UHS) {x : ℂ} (hx : x ∈ curveOf Ω Ωs) {A : ℝ}
    (hW : ‖q.1 - x‖ ≤ A * q.2) :
    hdistSet q (horoUnion Ω) ≤ Real.log (((A + 1 / c₁) ^ 2 + 1) / c₁) ∧
      hdistSet q (horoUnion Ωs) ≤ Real.log (((A + 1 / c₁) ^ 2 + 1) / c₁) := by
  have hξ : 0 < q.2 := hq
  obtain ⟨yp, hyp, ym, hym, h1, h2, h3, h4⟩ := hck x hx q.2 hξ
  have hB : ∀ y, ‖y - x‖ ≤ q.2 / c₁ → ‖q.1 - y‖ ≤ (A + 1 / c₁) * q.2 := fun y hy =>
    calc ‖q.1 - y‖ ≤ ‖q.1 - x‖ + ‖x - y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ A * q.2 + q.2 / c₁ := by rw [norm_sub_rev x]; exact add_le_add hW hy
      _ = (A + 1 / c₁) * q.2 := by ring
  exact ⟨s03_wd_est hJ hq hyp hc hc1 (by rw [hdE yp hyp]; exact h3) (hB yp h1),
    s03_wd_est hJs hq hym hc hc1 (by rw [hdEs ym hym]; exact h4) (hB ym h2)⟩

/-- Width helper: `d(X(w), U*) ≤ log(((16 + 1/c₁)² + 1)/c₁)` from `dist(W_X, Γ) ≤ 15 ξ_X`
(Lemma 2.3). -/
theorem s03_wd_ep {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) (hJs : IsJordanPair Ωs Ω)
    (hdE : ∀ w ∈ Ω, infDist w Ωᶜ = infDist w (curveOf Ω Ωs))
    (hdEs : ∀ w ∈ Ωs, infDist w Ωsᶜ = infDist w (curveOf Ω Ωs)) {c₁ : ℝ} (hc : 0 < c₁)
    (hc1 : c₁ ≤ 1)
    (hck : ∀ x ∈ curveOf Ω Ωs, ∀ r : ℝ, 0 < r →
      ∃ yp ∈ Ω, ∃ ym ∈ Ωs, ‖yp - x‖ ≤ r / c₁ ∧ ‖ym - x‖ ≤ r / c₁ ∧
        c₁ * r ≤ infDist yp (curveOf Ω Ωs) ∧ c₁ * r ≤ infDist ym (curveOf Ω Ωs))
    (hne : (curveOf Ω Ωs).Nonempty) {w : ℂ} (hw : w ∈ Ω) :
    hdistSet (epstein Ω w) (horoUnion Ωs) ≤ Real.log (((16 + 1 / c₁) ^ 2 + 1) / c₁) := by
  have hR := s02_jordanPair_riemannMap hJ
  obtain ⟨e1, -, e3, e4, -, e6⟩ := lem_ep_position hR hw
  have hl := s02_poincareDensity_pos hR hw
  have hξ : 0 < (epstein Ω w).2 := lt_of_lt_of_le (by positivity) e1
  rw [hdE w hw] at e4 e6
  obtain ⟨x, hx, hxd⟩ := (infDist_lt_iff hne).1
    (show infDist w (curveOf Ω Ωs) < infDist w (curveOf Ω Ωs) + (epstein Ω w).2 by linarith)
  rw [dist_eq_norm] at hxd
  have hW : ‖(epstein Ω w).1 - x‖ ≤ 16 * (epstein Ω w).2 :=
    calc ‖(epstein Ω w).1 - x‖ ≤ ‖(epstein Ω w).1 - w‖ + ‖w - x‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 16 * (epstein Ω w).2 := by linarith
  exact (s03_wd_side hJ hJs hdE hdEs hc hc1 hck hξ hx hW).2

/-- Lemma 3.5 `lem:width`, (3.3) `eq:width`, `sec03-coarse.tex:123`: there is `D_K < ∞` with
`d(q, U), d(q, U*) ≤ D_K` for `q ∈ 𝒩`, `d(X(w), U*) ≤ D_K` and `d(X*(w*), U) ≤ D_K`. -/
theorem lem_width (K : ℝ) :
    ∃ D : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      (∀ q ∈ gap Ω Ωs, hdistSet q (horoUnion Ω) ≤ D ∧ hdistSet q (horoUnion Ωs) ≤ D) ∧
      (∀ w ∈ Ω, hdistSet (epstein Ω w) (horoUnion Ωs) ≤ D) ∧
      ∀ ws ∈ Ωs, hdistSet (epstein Ωs ws) (horoUnion Ω) ≤ D := by
  -- `D_K = log(((16 + 1/c₁)² + 1)/c₁)` with `c₁` from Lemma 3.4.
  obtain ⟨c₁, hc, hc1, hck⟩ := lem_corkscrew K
  refine ⟨Real.log (((16 + 1 / c₁) ^ 2 + 1) / c₁), fun Ω Ωs h hnl => ?_⟩
  have hJ : IsJordanPair Ω Ωs := s03_b0_jordanPair h
  have hJs : IsJordanPair Ωs Ω := s03_b0_jordanPair (s03_qce_swap h)
  have hdE : ∀ w ∈ Ω, infDist w Ωᶜ = infDist w (curveOf Ω Ωs) := fun w hw =>
    s03_b0_infDist h hw
  have hdEs : ∀ w ∈ Ωs, infDist w Ωsᶜ = infDist w (curveOf Ω Ωs) := fun w hw =>
    s03_b0_infDist_s h hw
  have hckΩ := hck Ω Ωs h hnl
  have hne := (s03_b0_curve h).1
  have hc0 : 0 ≤ 1 / c₁ := one_div_nonneg.2 hc.le
  refine ⟨fun q hq => ?_, fun w hw => s03_wd_ep hJ hJs hdE hdEs hc hc1 hckΩ hne hw,
    fun ws hws => ?_⟩
  · obtain ⟨x, hx, hxd⟩ := (infDist_lt_iff hne).1 (s03_wd_near hJ hJs hdE hdEs hq)
    rw [dist_eq_norm] at hxd
    have hs := s03_wd_side hJ hJs hdE hdEs hc hc1 hckΩ hq.1 hx (A := 1) (by linarith)
    have hmono : Real.log (((1 + 1 / c₁) ^ 2 + 1) / c₁) ≤
        Real.log (((16 + 1 / c₁) ^ 2 + 1) / c₁) := by
      refine Real.log_le_log (by positivity) (div_le_div_of_nonneg_right ?_ hc.le)
      nlinarith
    exact ⟨hs.1.trans hmono, hs.2.trans hmono⟩
  · -- the symmetric case: `X*(w*)` for the swapped pair
    have hcs : curveOf Ωs Ω = curveOf Ω Ωs := by rw [curveOf, curveOf, union_comm]
    have hckΩs : ∀ x ∈ curveOf Ωs Ω, ∀ r : ℝ, 0 < r →
        ∃ yp ∈ Ωs, ∃ ym ∈ Ω, ‖yp - x‖ ≤ r / c₁ ∧ ‖ym - x‖ ≤ r / c₁ ∧
          c₁ * r ≤ infDist yp (curveOf Ωs Ω) ∧ c₁ * r ≤ infDist ym (curveOf Ωs Ω) := by
      intro x hx r hr
      rw [hcs] at hx ⊢
      obtain ⟨yp, hyp, ym, hym, h1, h2, h3, h4⟩ := hckΩ x hx r hr
      exact ⟨ym, hym, yp, hyp, h2, h1, h4, h3⟩
    exact s03_wd_ep hJs hJ (hcs ▸ hdEs) (hcs ▸ hdE) hc hc1 hckΩs (hcs ▸ hne) hws

/-! ## §3.5 Quasi-isometric properties -/

/-- Quasi-isometry helper: with `X(w) = (W, ξ)`, `X(w') = (W', ξ')` placed as in Lemma 2.3
(`d/5 ≤ ξ ≤ 4d`, `|W - w| ≤ 2d`), `R_e = |w - w'|/min{d, d'} ≤ 256 cosh² d(X w, X w')`. -/
theorem s03_qi_Re {W W' w w' : ℂ} {ξ ξ' d d' : ℝ} (hξ : 0 < ξ) (hξ' : 0 < ξ')
    (h1 : d / 5 ≤ ξ) (h2 : ξ ≤ 4 * d) (h3 : ‖W - w‖ ≤ 2 * d)
    (h1' : d' / 5 ≤ ξ') (h2' : ξ' ≤ 4 * d') (h3' : ‖W' - w'‖ ≤ 2 * d') :
    ‖w - w'‖ / min d d' ≤ 256 * coshDist (W, ξ) (W', ξ') ^ 2 := by
  set c := coshDist (W, ξ) (W', ξ') with hcdef
  have hpos : 0 < 2 * ξ * ξ' := by positivity
  have hkey : ‖W - W'‖ ^ 2 + (ξ - ξ') ^ 2 = 2 * ξ * ξ' * (c - 1) := by
    rw [hcdef]
    unfold coshDist
    field_simp
    ring
  have hc1 : 1 ≤ c := by
    have : 0 ≤ 2 * ξ * ξ' * (c - 1) := by rw [← hkey]; positivity
    by_contra hlt
    push Not at hlt
    nlinarith
  have hc0 : 0 < c := by linarith
  have hξ'le : ξ' ≤ 2 * c * ξ :=
    le_of_mul_le_mul_right (by nlinarith [sq_nonneg ‖W - W'‖, sq_nonneg ξ]) hξ'
  have hξle : ξ ≤ 2 * c * ξ' :=
    le_of_mul_le_mul_right (by nlinarith [sq_nonneg ‖W - W'‖, sq_nonneg ξ']) hξ
  have hWW : ‖W - W'‖ ≤ 2 * c * ξ := by
    have h : ‖W - W'‖ ^ 2 ≤ (2 * c * ξ) ^ 2 := by
      nlinarith [sq_nonneg (ξ - ξ')]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h
  have hww : ‖w - w'‖ ≤ 32 * c * ξ := by
    have t1 : ‖w - w'‖ ≤ ‖w - W‖ + ‖W - W'‖ + ‖W' - w'‖ :=
      (norm_sub_le_norm_sub_add_norm_sub w W' w').trans
        (add_le_add_left (norm_sub_le_norm_sub_add_norm_sub w W W') _)
    rw [norm_sub_rev w W] at t1
    nlinarith
  have hd : 0 < d := by linarith
  have hd' : 0 < d' := by linarith
  have hm : ξ / (8 * c) ≤ min d d' := by
    refine le_min ?_ ?_
    · rw [div_le_iff₀ (by positivity)]; nlinarith
    · rw [div_le_iff₀ (by positivity)]; nlinarith
  rw [div_le_iff₀ (lt_min hd hd')]
  calc ‖w - w'‖ ≤ 32 * c * ξ := hww
    _ = 256 * c ^ 2 * (ξ / (8 * c)) := by field_simp; ring
    _ ≤ 256 * c ^ 2 * min d d' := mul_le_mul_of_nonneg_left hm (by positivity)

/-- Quasi-isometry helper: `log(1 + 256 cosh²r) ≤ log 257 + 2 r` for `r = arcosh c`, `c ≥ 1`. -/
theorem s03_qi_log {c : ℝ} (hc : 1 ≤ c) :
    Real.log (1 + 256 * c ^ 2) ≤ Real.log 257 + 2 * Real.arcosh c := by
  have hc0 : 0 < c := by linarith
  have hle : c ≤ Real.exp (Real.arcosh c) := by
    rw [Real.exp_arcosh hc]; linarith [Real.sqrt_nonneg (c ^ 2 - 1)]
  have hlc : Real.log c ≤ Real.arcosh c := by
    rw [Real.log_le_iff_le_exp hc0]; exact hle
  have h1 : 1 + 256 * c ^ 2 ≤ 257 * c ^ 2 := by nlinarith
  calc Real.log (1 + 256 * c ^ 2) ≤ Real.log (257 * c ^ 2) := Real.log_le_log (by positivity) h1
    _ = Real.log 257 + 2 * Real.log c := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    _ ≤ Real.log 257 + 2 * Real.arcosh c := by linarith

/-- Proposition 3.6 helper (the lower bound of (3.4)): `d_ρ(w, w') ≤ A_K d(X w, X w') + B_K` on the
side `Ω` of a `K`-quasi pair (Lemmas 2.3 and 3.3). -/
theorem s03_qi_lower (K : ℝ) :
    ∃ A B : ℝ, 0 ≤ A ∧ ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ∀ w ∈ Ω, ∀ w' ∈ Ω,
      poincareDist Ω w w' ≤ A * hdist (epstein Ω w) (epstein Ω w') + B := by
  obtain ⟨C, hC⟩ := s03_dd_side K
  set C' := max C 0 with hC'def
  refine ⟨2 * C', C' * Real.log 257, by have := le_max_right C 0; linarith,
    fun Ω Ωs h w hw w' hw' => ?_⟩
  obtain ⟨-, -, -, hR⟩ := s03_b0_basic h
  have hdd := hC Ω Ωs h w hw w' hw'
  obtain ⟨e1, -, -, e4, e5, e6⟩ := lem_ep_position hR hw
  obtain ⟨f1, -, -, f4, f5, f6⟩ := lem_ep_position hR hw'
  rw [s03_b0_infDist h hw] at e4 e5 e6
  rw [s03_b0_infDist h hw'] at f4 f5 f6
  have hl := s02_poincareDensity_pos hR hw
  have hl' := s02_poincareDensity_pos hR hw'
  have hξ : 0 < (epstein Ω w).2 := lt_of_lt_of_le (by positivity) e1
  have hξ' : 0 < (epstein Ω w').2 := lt_of_lt_of_le (by positivity) f1
  have hRe := s03_qi_Re hξ hξ' e4 e5 e6 f4 f5 f6
  set c := coshDist ((epstein Ω w).1, (epstein Ω w).2) ((epstein Ω w').1, (epstein Ω w').2)
    with hcdef
  have hc1 : 1 ≤ c := by
    rw [hcdef]
    unfold coshDist
    exact le_add_of_nonneg_right (div_nonneg (by positivity) (by positivity))
  have hhd : hdist (epstein Ω w) (epstein Ω w') = Real.arcosh c := rfl
  set R := ‖w - w'‖ / min (infDist w (curveOf Ω Ωs)) (infDist w' (curveOf Ω Ωs)) with hRdef
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    exact div_nonneg (norm_nonneg _) (le_min infDist_nonneg infDist_nonneg)
  have hlog : Real.log (1 + R) ≤ Real.log 257 + 2 * Real.arcosh c :=
    (Real.log_le_log (by linarith) (by linarith)).trans (s03_qi_log hc1)
  have hL0 : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
  have hC'0 : 0 ≤ C' := le_max_right _ _
  calc poincareDist Ω w w' ≤ C * Real.log (1 + R) := hdd
    _ ≤ C' * Real.log (1 + R) := mul_le_mul_of_nonneg_right (le_max_left _ _) hL0
    _ ≤ C' * (Real.log 257 + 2 * Real.arcosh c) := mul_le_mul_of_nonneg_left hlog hC'0
    _ = 2 * C' * hdist (epstein Ω w) (epstein Ω w') + C' * Real.log 257 := by rw [hhd]; ring

/-- `arcosh (1 + x) ≤ √(2x)` for `x ≥ 0` (from `cosh s ≥ 1 + s²/2`). -/
theorem s03_arcosh_one_add_le {x : ℝ} (hx : 0 ≤ x) : Real.arcosh (1 + x) ≤ √(2 * x) := by
  set s := √(2 * x) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = 2 * x := Real.sq_sqrt (by positivity)
  have hsh : s / 2 ≤ Real.sinh (s / 2) := Real.self_le_sinh_iff.mpr (by positivity)
  have hc : 1 + x ≤ Real.cosh s := by
    have h2 : Real.cosh s = 1 + 2 * Real.sinh (s / 2) ^ 2 := by
      have := Real.cosh_two_mul (s / 2)
      rw [show 2 * (s / 2) = s by ring] at this
      rw [this, Real.cosh_sq]
      ring
    rw [h2]
    have := mul_le_mul hsh hsh (by positivity) (le_trans (by positivity) hsh)
    nlinarith
  calc Real.arcosh (1 + x) ≤ Real.arcosh (Real.cosh s) :=
        (Real.arcosh_le_arcosh (by positivity) (Real.cosh_pos s)).mpr hc
    _ = s := Real.arcosh_cosh hs0

/-- `d(p, q) ≤ √((|p₁ - q₁|² + (p₂ - q₂)²) / (p₂ q₂))` on `ℍ³`. -/
theorem s03_hdist_le_sqrt {p q : ℂ × ℝ} (hp : 0 < p.2) (hq : 0 < q.2) :
    hdist p q ≤ √((‖p.1 - q.1‖ ^ 2 + (p.2 - q.2) ^ 2) / (p.2 * q.2)) := by
  have h := s03_arcosh_one_add_le
    (x := (‖p.1 - q.1‖ ^ 2 + (p.2 - q.2) ^ 2) / (2 * p.2 * q.2)) (by positivity)
  have e : 2 * ((‖p.1 - q.1‖ ^ 2 + (p.2 - q.2) ^ 2) / (2 * p.2 * q.2)) =
      (‖p.1 - q.1‖ ^ 2 + (p.2 - q.2) ^ 2) / (p.2 * q.2) := by
    rw [← mul_div_assoc, mul_assoc 2, mul_div_mul_left _ _ two_ne_zero]
  rw [e] at h
  exact h

/-- Path-length bound in `ℍ³`, strong form: if `γ` is differentiable on `[0, T]` with values in
`ℍ³` and hyperbolic speed `√⟨γ', γ'⟩_{γ} ≤ M`, then `d(γ(0), γ(t)) ≤ M t` for `t ∈ [0, T]`. -/
theorem s03_hdist_le_of_speed' {γ γ' : ℝ → ℂ × ℝ} {T M : ℝ}
    (hγ : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (γ' t) (Icc 0 T) t)
    (hU : ∀ t ∈ Icc 0 T, γ t ∈ UHS)
    (hM : ∀ t ∈ Icc 0 T, √(hypInner (γ t) (γ' t) (γ' t)) ≤ M) :
    ∀ t ∈ Icc 0 T, hdist (γ 0) (γ t) ≤ M * t := by
  rcases lt_or_ge T 0 with hT | hT
  · intro t ht
    exact absurd (ht.1.trans ht.2) (by linarith)
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hγc : ContinuousOn γ (Icc 0 T) := fun t ht => (hγ t ht).continuousWithinAt
  have hp0 : 0 < (γ 0).2 := hU 0 h0
  have hcd : ContinuousOn (fun t => coshDist (γ 0) (γ t)) (Icc 0 T) := by
    have h1 : ContinuousOn (fun t => (γ t).1) (Icc 0 T) := continuous_fst.comp_continuousOn hγc
    have h2 : ContinuousOn (fun t => (γ t).2) (Icc 0 T) := continuous_snd.comp_continuousOn hγc
    unfold coshDist
    refine continuousOn_const.add (ContinuousOn.div ?_ ?_ ?_)
    · exact ((continuousOn_const.sub h1).norm.pow 2).add ((continuousOn_const.sub h2).pow 2)
    · exact continuousOn_const.mul h2
    · intro t ht
      have : 0 < (γ t).2 := hU t ht
      positivity
  have hge : ∀ t ∈ Icc 0 T, 1 ≤ coshDist (γ 0) (γ t) := by
    intro t ht
    have : 0 < (γ t).2 := hU t ht
    unfold coshDist
    have : 0 ≤ (‖(γ 0).1 - (γ t).1‖ ^ 2 + ((γ 0).2 - (γ t).2) ^ 2) / (2 * (γ 0).2 * (γ t).2) := by
      positivity
    linarith
  have hfc : ContinuousOn (fun t => hdist (γ 0) (γ t)) (Icc 0 T) :=
    Real.continuousOn_arcosh.comp hcd (fun t ht => mem_Ici.mpr (hge t ht))
  refine image_le_of_liminf_slope_right_le_deriv_boundary hfc (B := fun t => M * t)
    (B' := fun _ => M) ?_ (continuousOn_const.mul continuousOn_id) ?_ ?_
  · show hdist (γ 0) (γ 0) ≤ M * 0
    have : coshDist (γ 0) (γ 0) = 1 := by
      unfold coshDist
      simp
    rw [mul_zero]
    unfold hdist
    rw [this, Real.arcosh_zero]
  · intro x _
    simpa using ((hasDerivAt_id x).const_mul M).hasDerivWithinAt
  · intro x hx r hr
    have hxI : x ∈ Icc 0 T := Ico_subset_Icc_self hx
    have hpx : 0 < (γ x).2 := hU x hxI
    have hd : HasDerivWithinAt γ (γ' x) (Ioi x) x :=
      (hγ x hxI).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT_of_mem hx)
    have hsl : Tendsto (slope γ x) (𝓝[>] x) (𝓝 (γ' x)) :=
      (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x)).mp hd
    have hc2 : Tendsto (fun z => (γ z).2) (𝓝[>] x) (𝓝 (γ x).2) :=
      (continuous_snd.tendsto _).comp hd.continuousWithinAt.tendsto
    set A : ℂ × ℝ → ℝ := fun v => ‖v.1‖ ^ 2 + v.2 ^ 2 with hAdef
    have hA : Continuous A := (continuous_fst.norm.pow 2).add (continuous_snd.pow 2)
    have hlim : Tendsto (fun z => √(A (slope γ x z) / ((γ x).2 * (γ z).2))) (𝓝[>] x)
        (𝓝 (√(A (γ' x) / ((γ x).2 * (γ x).2)))) :=
      (((hA.tendsto _).comp hsl).div (tendsto_const_nhds.mul hc2) (by positivity)).sqrt
    have hL : √(A (γ' x) / ((γ x).2 * (γ x).2)) = √(hypInner (γ x) (γ' x) (γ' x)) := by
      congr 1
      simp only [hAdef, hypInner]
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      ring
    have hlt : √(A (γ' x) / ((γ x).2 * (γ x).2)) < r :=
      lt_of_le_of_lt ((le_of_eq hL).trans (hM x hxI)) hr
    refine Filter.Eventually.frequently ?_
    filter_upwards [hlim.eventually (gt_mem_nhds hlt), Ioo_mem_nhdsGT hx.2] with z hz hzI
    have hzI' : z ∈ Icc 0 T := ⟨hx.1.trans hzI.1.le, hzI.2.le⟩
    have hpz : 0 < (γ z).2 := hU z hzI'
    have hc : 0 < z - x := sub_pos.mpr hzI.1
    have htri := s02_hdist_triangle (hU 0 h0) (hU x hxI) (hU z hzI')
    have hsq := s03_hdist_le_sqrt hpx hpz
    have hs1 : ‖(slope γ x z).1‖ = ‖(γ x).1 - (γ z).1‖ / (z - x) := by
      rw [slope_def_module, Prod.smul_fst, Prod.fst_sub, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hc, norm_sub_rev]
      ring
    have hs2 : (slope γ x z).2 = -((γ x).2 - (γ z).2) / (z - x) := by
      rw [slope_def_module, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
      ring
    have k : √((‖(γ x).1 - (γ z).1‖ ^ 2 + ((γ x).2 - (γ z).2) ^ 2) / ((γ x).2 * (γ z).2)) /
        (z - x) = √(A (slope γ x z) / ((γ x).2 * (γ z).2)) := by
      rw [← Real.sqrt_sq hc.le, ← Real.sqrt_div' _ (sq_nonneg _)]
      congr 1
      simp only [hAdef]
      rw [hs1, hs2]
      field_simp
    rw [slope_def_field]
    calc (hdist (γ 0) (γ z) - hdist (γ 0) (γ x)) / (z - x) ≤ hdist (γ x) (γ z) / (z - x) :=
          div_le_div_of_nonneg_right (by linarith) hc.le
      _ ≤ √((‖(γ x).1 - (γ z).1‖ ^ 2 + ((γ x).2 - (γ z).2) ^ 2) / ((γ x).2 * (γ z).2)) /
            (z - x) := div_le_div_of_nonneg_right hsq hc.le
      _ = √(A (slope γ x z) / ((γ x).2 * (γ z).2)) := k
      _ < r := hz

/-- Path-length bound in `ℍ³`: if `γ` is differentiable on `[0, T]` with values in `ℍ³` and
hyperbolic speed `√⟨γ', γ'⟩_{γ} ≤ M`, then `d(γ(0), γ(T)) ≤ M T`. -/
theorem s03_hdist_le_of_speed {γ γ' : ℝ → ℂ × ℝ} {T M : ℝ} (hT : 0 ≤ T)
    (hγ : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (γ' t) (Icc 0 T) t)
    (hU : ∀ t ∈ Icc 0 T, γ t ∈ UHS)
    (hM : ∀ t ∈ Icc 0 T, √(hypInner (γ t) (γ' t) (γ' t)) ≤ M) :
    hdist (γ 0) (γ T) ≤ M * T :=
  s03_hdist_le_of_speed' hγ hU hM T ⟨hT, le_rfl⟩

/-- Half-angle formulas: `cosh x = (1 + τ²)/(1 - τ²)` and `sinh x = 2τ/(1 - τ²)`, `τ = tanh(x/2)`. -/
theorem s03_geo_cosh_tanh (x : ℝ) :
    Real.cosh x = (1 + Real.tanh (x / 2) ^ 2) / (1 - Real.tanh (x / 2) ^ 2) ∧
      Real.sinh x = 2 * Real.tanh (x / 2) / (1 - Real.tanh (x / 2) ^ 2) := by
  have hc := Real.cosh_pos (x / 2)
  have hsq := Real.cosh_sq (x / 2)
  have hx : x = 2 * (x / 2) := by ring
  have h1 : 1 - Real.tanh (x / 2) ^ 2 = 1 / Real.cosh (x / 2) ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    linarith
  constructor
  · rw [h1, hx, Real.cosh_two_mul, ← hx, Real.tanh_eq_sinh_div_cosh]
    field_simp
  · rw [h1, hx, Real.sinh_two_mul, ← hx, Real.tanh_eq_sinh_div_cosh]
    field_simp

/-- A disc distance `|s|` gives `cosh_𝔻 = cosh s`. -/
theorem s03_geo_coshDist {u v : ℂ} (hu : u ∈ unitDisc) (hv : v ∈ unitDisc) {s : ℝ}
    (h : diskDist u v = |s|) : diskCoshDist u v = Real.cosh s := by
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  have hv1 : ‖v‖ < 1 := mem_ball_zero_iff.mp hv
  have h1 : 0 < 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
  have h2 : 0 < 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
  have hge : 1 ≤ diskCoshDist u v := by
    unfold diskCoshDist
    have : 0 ≤ 2 * ‖u - v‖ ^ 2 / ((1 - ‖u‖ ^ 2) * (1 - ‖v‖ ^ 2)) := by positivity
    linarith
  rw [← Real.cosh_arcosh hge, ← Real.cosh_abs s, ← h]
  rfl

/-- Geodesics of `𝔻` through `0`: if `d_𝔻(w t, w t') = c|t - t'|` and `w 0 = 0`, then
`w t = e · tanh(c t / 2)` with `|e| = 1`. -/
theorem s03_geo_disk {w : ℝ → ℂ} (hw : ∀ t, w t ∈ unitDisc) (hw0 : w 0 = 0) {c : ℝ}
    (hc : 0 < c) (hd : ∀ t t', diskDist (w t) (w t') = c * |t - t'|) :
    ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ t, w t = e * (Real.tanh (c * t / 2) : ℂ) := by
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  -- `|w t| = |tanh(ct/2)|`
  have hnorm : ∀ t, ‖w t‖ ^ 2 = Real.tanh (c * t / 2) ^ 2 := by
    intro t
    have h := s03_geo_coshDist h0 (hw t) (s := c * t)
      (by rw [← hw0, hd, abs_mul, abs_of_pos hc, zero_sub, abs_neg])
    obtain ⟨hch, -⟩ := s03_geo_cosh_tanh (c * t)
    rw [hch] at h
    unfold diskCoshDist at h
    simp only [zero_sub, norm_neg, norm_zero] at h
    have hτ : 0 < 1 - Real.tanh (c * t / 2) ^ 2 := by
      have := Real.abs_tanh_lt_one (c * t / 2)
      nlinarith [abs_nonneg (Real.tanh (c * t / 2)), sq_abs (Real.tanh (c * t / 2))]
    have hw1 : ‖w t‖ < 1 := mem_ball_zero_iff.mp (hw t)
    have hr : 0 < 1 - ‖w t‖ ^ 2 := by nlinarith [norm_nonneg (w t)]
    have hτ' := hτ.ne'
    have hr' := hr.ne'
    field_simp at h
    nlinarith
  -- `|w t - w 1| = |tanh(ct/2) - tanh(c/2)|`
  have hdiff : ∀ t, ‖w t - w 1‖ ^ 2 = (Real.tanh (c * t / 2) - Real.tanh (c * 1 / 2)) ^ 2 := by
    intro t
    have h := s03_geo_coshDist (hw t) (hw 1) (s := c * t - c * 1)
      (by rw [hd, ← mul_sub, abs_mul, abs_of_pos hc])
    obtain ⟨hct, hst⟩ := s03_geo_cosh_tanh (c * t)
    obtain ⟨hc1, hs1⟩ := s03_geo_cosh_tanh (c * 1)
    rw [Real.cosh_sub, hct, hst, hc1, hs1] at h
    unfold diskCoshDist at h
    rw [hnorm t, hnorm 1] at h
    set a := Real.tanh (c * t / 2)
    set b := Real.tanh (c * 1 / 2)
    have ha1 : |a| < 1 := Real.abs_tanh_lt_one _
    have hb1 : |b| < 1 := Real.abs_tanh_lt_one _
    have hA : 0 < 1 - a ^ 2 := by nlinarith [abs_nonneg a, sq_abs a]
    have hB : 0 < 1 - b ^ 2 := by nlinarith [abs_nonneg b, sq_abs b]
    field_simp at h
    nlinarith [mul_pos hA hB]
  set τ₁ := Real.tanh (c * 1 / 2) with hτ₁
  have hτ₁0 : 0 < τ₁ := by
    rw [hτ₁, Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by positivity)) (Real.cosh_pos _)
  have hw1n : ‖w 1‖ = τ₁ := by
    have := hnorm 1
    rw [← hτ₁] at this
    rw [← Real.sqrt_sq (norm_nonneg _), this, Real.sqrt_sq hτ₁0.le]
  refine ⟨w 1 / (τ₁ : ℂ), ?_, fun t => ?_⟩
  · rw [norm_div, hw1n, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ₁0, div_self hτ₁0.ne']
  · set τ := Real.tanh (c * t / 2) with hτ
    set e := w 1 / (τ₁ : ℂ) with he
    have hB : w 1 = e * (τ₁ : ℂ) := by
      rw [he, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hτ₁0.ne')]
    have hen : e.re ^ 2 + e.im ^ 2 = 1 := by
      have : ‖e‖ = 1 := by
        rw [he, norm_div, hw1n, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ₁0,
          div_self hτ₁0.ne']
      have h2 := Complex.sq_norm e
      rw [this, Complex.normSq_apply] at h2
      nlinarith
    have h1 := hnorm t
    have h2 := hdiff t
    rw [hB] at h2
    rw [Complex.sq_norm, Complex.normSq_apply] at h1 h2
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero] at h2
    set a1 := (w t).re
    set a2 := (w t).im
    have hae : τ₁ * (a1 * e.re + a2 * e.im) = τ₁ * τ := by
      linear_combination (h1 - h2 + τ₁ ^ 2 * hen) / 2
    have hae' : a1 * e.re + a2 * e.im = τ := mul_left_cancel₀ hτ₁0.ne' hae
    have hz : (a1 - τ * e.re) ^ 2 + (a2 - τ * e.im) ^ 2 = 0 := by
      linear_combination h1 - 2 * τ * hae' + τ ^ 2 * hen
    have hz1 : a1 - τ * e.re = 0 := by nlinarith [sq_nonneg (a1 - τ * e.re), sq_nonneg (a2 - τ * e.im)]
    have hz2 : a2 - τ * e.im = 0 := by nlinarith [sq_nonneg (a1 - τ * e.re), sq_nonneg (a2 - τ * e.im)]
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      linarith
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero]
      linarith

/-- ρ-geodesics through a Riemann map `f`: `γ(t) = f(B_{-p}(e · tanh(c t / 2)))` with
`p = f⁻¹(γ 0)`, `|e| = 1` and `c` the speed of `γ`. -/
theorem s03_geo_eq_f {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {γ : ℝ → ℂ}
    (hγ : IsRhoGeodesic Ω γ) :
    ∃ c : ℝ, 0 < c ∧ (∀ t t', poincareDist Ω (γ t) (γ t') = c * |t - t'|) ∧
      ∃ p ∈ unitDisc, ∃ e : ℂ, ‖e‖ = 1 ∧
        ∀ t, γ t = f (blaschke (-p) (e * (Real.tanh (c * t / 2) : ℂ))) := by
  obtain ⟨hmem, c, hc, hd⟩ := hγ
  have hex : ∀ t, ∃ a ∈ unitDisc, f a = γ t := fun t => by
    have := hmem t
    rw [← hf.2.2] at this
    exact this
  set p := Function.invFunOn f unitDisc (γ 0) with hpdef
  have hp : p ∈ unitDisc := Function.invFunOn_mem (hex 0)
  have hfp : f p = γ 0 := Function.invFunOn_eq (hex 0)
  obtain ⟨hg, hg0, -⟩ := s02_disc_recenter hf hp
  set g := f ∘ blaschke (-p) with hgdef
  have hexg : ∀ t, ∃ a ∈ unitDisc, g a = γ t := fun t => by
    have := hmem t
    rw [← hg.2.2] at this
    exact this
  set w : ℝ → ℂ := fun t => Function.invFunOn g unitDisc (γ t) with hwdef
  have hw : ∀ t, w t ∈ unitDisc := fun t => Function.invFunOn_mem (hexg t)
  have hgw : ∀ t, g (w t) = γ t := fun t => Function.invFunOn_eq (hexg t)
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hw0 : w 0 = 0 := hg.2.1 (hw 0) h0 (by rw [hgw 0, hg0, hfp])
  have hdd : ∀ t t', diskDist (w t) (w t') = c * |t - t'| := fun t t' => by
    rw [← subsec_poincare_dist hg (hw t) (hw t'), hgw, hgw, hd]
  obtain ⟨e, he, hwe⟩ := s03_geo_disk hw hw0 hc hdd
  refine ⟨c, hc, hd, p, hp, e, he, fun t => ?_⟩
  rw [← hgw t, hwe t]
  rfl

/-- ρ-geodesics are reparametrized diameters: `γ(t) = g(tanh(c t / 2))` for a Riemann map
`g : 𝔻 → Ω` with `g 0 = γ 0`. -/
theorem s03_geo_eq {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {γ : ℝ → ℂ}
    (hγ : IsRhoGeodesic Ω γ) :
    ∃ g : ℂ → ℂ, ∃ c : ℝ, IsConformalOnto g unitDisc Ω ∧ g 0 = γ 0 ∧ 0 < c ∧
      ∀ t, γ t = g (Real.tanh (c * t / 2)) := by
  obtain ⟨f, hf⟩ := hΩ
  obtain ⟨c, hc, -, p, hp, e, he, hγe⟩ := s03_geo_eq_f hf hγ
  obtain ⟨hG, hG0, -⟩ := s02_disc_recenter hf hp
  have hR : IsConformalOnto (fun z => e * z) unitDisc unitDisc := isConformalOnto_rot he
  have hRm : MapsTo (fun z => e * z) unitDisc unitDisc := fun z hz =>
    hR.2.2 ▸ mem_image_of_mem _ hz
  refine ⟨(f ∘ blaschke (-p)) ∘ (fun z => e * z), c,
    ⟨hG.1.comp hR.1 hRm, hG.2.1.comp hR.2.1 hRm, by rw [image_comp, hR.2.2, hG.2.2]⟩, ?_, hc,
    fun t => hγe t⟩
  have h0 := hγe 0
  rw [mul_zero, zero_div, Real.tanh_zero, Complex.ofReal_zero, mul_zero] at h0
  rw [h0]
  show (f ∘ blaschke (-p)) (e * 0) = f (blaschke (-p) 0)
  rw [mul_zero]
  rfl

/-- ρ-geodesics are smooth. -/
theorem s03_geo_contDiff {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    {γ : ℝ → ℂ} (hγ : IsRhoGeodesic Ω γ) {n : WithTop ℕ∞} : ContDiff ℝ n γ := by
  obtain ⟨g, c, hg, -, -, hγg⟩ := s03_geo_eq hΩ hγ
  have hfun : γ = fun t => g (Real.tanh (c * t / 2)) := funext hγg
  rw [hfun, contDiff_iff_contDiffAt]
  intro t
  have hτ : ContDiff ℝ n fun t : ℝ => ((Real.tanh (c * t / 2) : ℝ) : ℂ) := by
    have h1 : ContDiff ℝ n fun t : ℝ => Real.tanh (c * t / 2) := by
      have : (fun t : ℝ => Real.tanh (c * t / 2)) =
          fun t => Real.sinh (c * t / 2) / Real.cosh (c * t / 2) := by
        funext t
        exact Real.tanh_eq_sinh_div_cosh _
      rw [this]
      exact (Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id |>.div_const 2)).div
        (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id |>.div_const 2))
        (fun x => (Real.cosh_pos _).ne')
    exact Complex.ofRealCLM.contDiff.comp h1
  have hmem : ((Real.tanh (c * t / 2) : ℝ) : ℂ) ∈ unitDisc := by
    refine mem_ball_zero_iff.mpr ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_tanh_lt_one _
  have hgc : ContDiffAt ℝ n g ((Real.tanh (c * t / 2) : ℝ) : ℂ) :=
    ((hg.1.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds hmem)).restrict_scalars ℝ
  exact hgc.comp t hτ.contDiffAt

/-- `tanh' = 1 - tanh²`. -/
theorem s03_geo_hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hc := (Real.cosh_pos x).ne'
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have e : Real.sinh / Real.cosh = Real.tanh := by
    funext y
    rw [Pi.div_apply]
    exact (Real.tanh_eq_sinh_div_cosh y).symm
  rw [e] at h
  refine h.congr_deriv ?_
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, eq_sub_iff_add_eq, ← add_div,
    div_eq_one_iff_eq (pow_ne_zero 2 hc)]
  ring

/-- Explicit first derivative of `t ↦ g(tanh(c t / 2))` for a Riemann map `g`. -/
theorem s03_geo_hasDerivAt {Ω : Set ℂ} {g : ℂ → ℂ} (hg : IsConformalOnto g unitDisc Ω) (c t : ℝ) :
    HasDerivAt (fun t : ℝ => g (Real.tanh (c * t / 2)))
      (deriv g (Real.tanh (c * t / 2)) *
        ((c / 2 * (1 - Real.tanh (c * t / 2) ^ 2) : ℝ) : ℂ)) t := by
  have hmem : ((Real.tanh (c * t / 2) : ℝ) : ℂ) ∈ unitDisc := by
    refine mem_ball_zero_iff.mpr ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_tanh_lt_one _
  have hgd : HasDerivAt g (deriv g (Real.tanh (c * t / 2))) ((Real.tanh (c * t / 2) : ℝ) : ℂ) :=
    (hg.1.differentiableAt (isOpen_ball.mem_nhds hmem)).hasDerivAt
  have hlin : HasDerivAt (fun t : ℝ => c * t / 2) (c * 1 / 2) t :=
    ((hasDerivAt_id t).const_mul c).div_const 2
  have hτ := (s03_geo_hasDerivAt_tanh (c * t / 2)).comp t hlin
  have h := hgd.comp_ofReal.scomp t hτ
  refine h.congr_deriv ?_
  rw [Complex.real_smul]
  push_cast
  ring

/-- Quasi-isometry helper: `tanh(d_𝔻(0, r)/2) = r` for `0 ≤ r < 1`. -/
theorem s03_qiu_tanh {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.tanh (1 * diskDist 0 (r : ℂ) / 2) = r := by
  have hr2 : 0 < 1 - r ^ 2 := by nlinarith
  have hc : diskCoshDist 0 (r : ℂ) = (1 + r ^ 2) / (1 - r ^ 2) := by
    unfold diskCoshDist
    rw [zero_sub, norm_neg, norm_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    field_simp
    ring
  have hge : 1 ≤ diskCoshDist 0 (r : ℂ) := by
    rw [hc, le_div_iff₀ hr2]; nlinarith
  set T := diskDist 0 (r : ℂ) with hTdef
  have hT0 : 0 ≤ T := Real.arcosh_nonneg hge
  have hcosh : Real.cosh T = (1 + r ^ 2) / (1 - r ^ 2) := by
    rw [hTdef]
    unfold diskDist
    rw [Real.cosh_arcosh hge, hc]
  obtain ⟨hct, -⟩ := s03_geo_cosh_tanh T
  rw [one_mul]
  set τ := Real.tanh (T / 2) with hτ
  have hτ1 : |τ| < 1 := Real.abs_tanh_lt_one _
  have hτ2 : 0 < 1 - τ ^ 2 := by nlinarith [abs_nonneg τ, sq_abs τ]
  have hτ0 : 0 ≤ τ := by
    rw [hτ, Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr (by linarith)) (Real.cosh_pos _).le
  have he : (1 + τ ^ 2) / (1 - τ ^ 2) = (1 + r ^ 2) / (1 - r ^ 2) := by rw [← hct, hcosh]
  rw [div_eq_div_iff hτ2.ne' hr2.ne'] at he
  have hsq : τ ^ 2 = r ^ 2 := by nlinarith
  exact (pow_left_inj₀ hτ0 hr0 two_ne_zero).1 hsq

/-- Proposition 3.6 helper (upper bound of (3.4) on one side): `d(X w, X w') ≤ (5/2) d_ρ(w, w')`
for a simply connected `Ω` with a Riemann map, by integrating `eq_dX_norm_always` along the
unit-speed `ρ`-geodesic `t ↦ g(tanh(t/2))`, `g(0) = w`, `g(r) = w'`. -/
theorem s03_qiu_side {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w w' : ℂ}
    (hw : w ∈ Ω) (hw' : w' ∈ Ω) :
    hdist (epstein Ω w) (epstein Ω w') ≤ 5 / 2 * poincareDist Ω w w' := by
  obtain ⟨f, hf⟩ := hΩ
  have hex : ∀ x ∈ Ω, ∃ a ∈ unitDisc, f a = x := fun x hx => by
    rw [← hf.2.2] at hx
    exact hx
  set p := Function.invFunOn f unitDisc w with hpdef
  set q := Function.invFunOn f unitDisc w' with hqdef
  have hp : p ∈ unitDisc := Function.invFunOn_mem (hex w hw)
  have hq : q ∈ unitDisc := Function.invFunOn_mem (hex w' hw')
  have hfp : f p = w := Function.invFunOn_eq (hex w hw)
  have hfq : f q = w' := Function.invFunOn_eq (hex w' hw')
  have hp1 : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
  have hq1 : ‖q‖ < 1 := mem_ball_zero_iff.mp hq
  obtain ⟨hg, hg0, -⟩ := s02_disc_recenter hf hp
  set b := blaschke p q with hbdef
  have hb1 : ‖b‖ < 1 := blaschke_mem_unitDisc hp1 hq1
  have hgb : (f ∘ blaschke (-p)) b = w' := by
    show f (blaschke (-p) (blaschke p q)) = w'
    rw [blaschke_neg_blaschke hp1 hq1, hfq]
  -- a unit `e` with `e ‖b‖ = b`
  obtain ⟨e, he1, heb⟩ : ∃ e : ℂ, ‖e‖ = 1 ∧ e * ((‖b‖ : ℝ) : ℂ) = b := by
    by_cases hb0 : b = 0
    · exact ⟨1, norm_one, by rw [hb0, norm_zero, Complex.ofReal_zero, mul_zero]⟩
    · have hn : ((‖b‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hb0)
      refine ⟨b / ((‖b‖ : ℝ) : ℂ), ?_, div_mul_cancel₀ _ hn⟩
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        div_self (norm_ne_zero_iff.mpr hb0)]
  have hR : IsConformalOnto (fun z => e * z) unitDisc unitDisc := isConformalOnto_rot he1
  have hRm : MapsTo (fun z => e * z) unitDisc unitDisc := fun z hz =>
    hR.2.2 ▸ mem_image_of_mem _ hz
  set g := (f ∘ blaschke (-p)) ∘ (fun z => e * z) with hgdef
  have hg1 : IsConformalOnto g unitDisc Ω :=
    ⟨hg.1.comp hR.1 hRm, hg.2.1.comp hR.2.1 hRm, by rw [image_comp, hR.2.2, hg.2.2]⟩
  have hg10 : g 0 = w := by
    show (f ∘ blaschke (-p)) (e * 0) = w
    rw [mul_zero, hg0, hfp]
  set r := ‖b‖ with hrdef
  have hgr : g (r : ℂ) = w' := by
    show (f ∘ blaschke (-p)) (e * (r : ℂ)) = w'
    rw [heb, hgb]
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hrD : (r : ℂ) ∈ unitDisc := by
    refine mem_ball_zero_iff.mpr ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]
    exact hb1
  set T := diskDist 0 (r : ℂ) with hTdef
  have hdρ : poincareDist Ω w w' = T := by
    rw [← hg10, ← hgr]
    exact subsec_poincare_dist hg1 h0 hrD
  have hT0 : 0 ≤ T := s02_diskDist_nonneg h0 hrD
  have hτT : Real.tanh (1 * T / 2) = r := s03_qiu_tanh (norm_nonneg b) hb1
  -- the path and its velocity
  have hτD : ∀ t : ℝ, ((Real.tanh (1 * t / 2) : ℝ) : ℂ) ∈ unitDisc := fun t => by
    refine mem_ball_zero_iff.mpr ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_tanh_lt_one _
  have hPΩ : ∀ t : ℝ, g (Real.tanh (1 * t / 2)) ∈ Ω := fun t => by
    rw [← hg1.2.2]; exact mem_image_of_mem g (hτD t)
  have hP := s03_geo_hasDerivAt hg1 1
  have hγ : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t => epstein Ω (g (Real.tanh (1 * t / 2))))
      (fderiv ℝ (epstein Ω) (g (Real.tanh (1 * t / 2)))
        (deriv g (Real.tanh (1 * t / 2)) *
          ((1 / 2 * (1 - Real.tanh (1 * t / 2) ^ 2) : ℝ) : ℂ))) (Icc 0 T) t := fun t _ => by
    have hX := (s02_epstein_differentiableAt ⟨f, hf⟩ (hPΩ t)).hasFDerivAt
    have hd := hX.comp_hasDerivAt t (hP t)
    exact hd.hasDerivWithinAt
  have hU : ∀ t ∈ Icc 0 T, epstein Ω (g (Real.tanh (1 * t / 2))) ∈ UHS := fun t _ => by
    have hl := s02_poincareDensity_pos ⟨f, hf⟩ (hPΩ t)
    have h1 := (lem_ep_position ⟨f, hf⟩ (hPΩ t)).1
    show 0 < (epstein Ω (g (Real.tanh (1 * t / 2)))).2
    exact lt_of_lt_of_le (by positivity) h1
  have hM : ∀ t ∈ Icc 0 T, √(hypInner (epstein Ω (g (Real.tanh (1 * t / 2))))
      (fderiv ℝ (epstein Ω) (g (Real.tanh (1 * t / 2)))
        (deriv g (Real.tanh (1 * t / 2)) * ((1 / 2 * (1 - Real.tanh (1 * t / 2) ^ 2) : ℝ) : ℂ)))
      (fderiv ℝ (epstein Ω) (g (Real.tanh (1 * t / 2)))
        (deriv g (Real.tanh (1 * t / 2)) *
          ((1 / 2 * (1 - Real.tanh (1 * t / 2) ^ 2) : ℝ) : ℂ)))) ≤ 5 / 2 := fun t _ => by
    refine (eq_dX_norm_always ⟨f, hf⟩ (hPΩ t) _).trans (le_of_eq ?_)
    set τ := Real.tanh (1 * t / 2) with hτ
    have hτ2 : 0 < 1 - τ ^ 2 := by
      have := Real.abs_tanh_lt_one (1 * t / 2)
      nlinarith [abs_nonneg τ, sq_abs τ]
    have hlam := eq_lambda_f hg1 (hτD t)
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hlam
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
      ← mul_assoc (poincareDensity Ω _), hlam]
    rw [show (2 : ℝ) / (1 - τ ^ 2) * (1 / 2 * (1 - τ ^ 2)) = 1 by field_simp, mul_one]
  have key := s03_hdist_le_of_speed hT0 hγ hU hM
  simp only [mul_zero, zero_div, Real.tanh_zero, Complex.ofReal_zero, hg10, hτT, hgr] at key
  rw [hdρ]
  exact key

/-- Proposition 3.6 helper (the upper bound of (3.4), split off with the leader's approval):
`d(X w, X w') ≤ (5/2) d_ρ(w, w')`, and the same for `X*`.  Open: it is (2.7) `eq:dX-norm`
integrated along a `ρ`-geodesic, which needs `eq_dX_norm_always` and a path-length description
of `d_ρ`. -/
theorem s03_qi_upper (K : ℝ) :
    ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      (∀ w ∈ Ω, ∀ w' ∈ Ω, hdist (epstein Ω w) (epstein Ω w') ≤ 5 / 2 * poincareDist Ω w w') ∧
      ∀ w ∈ Ωs, ∀ w' ∈ Ωs,
        hdist (epstein Ωs w) (epstein Ωs w') ≤ 5 / 2 * poincareDist Ωs w w' := by
  -- `s03_qiu_side` on `Ω` and on `Ω*` (the swapped pair).  The hypothesis `¬ IsLinePair Ω Ωs` is
  -- not needed: the bound holds for every simply connected side with a Riemann map.
  intro Ω Ωs h hnl
  have _hnl := hnl
  exact ⟨fun w hw w' hw' => s03_qiu_side (s03_b0_basic h).2.2.2 hw hw',
    fun w hw w' hw' => s03_qiu_side (s03_b0_basic (s03_qce_swap h)).2.2.2 hw hw'⟩

/-- Quasi-isometry helper: `X(w) ∈ B_w ⊆ U`. -/
theorem s03_qik_mem {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) : epstein Ω w ∈ horoUnion Ω := by
  have hl := s02_poincareDensity_pos hΩ hw
  refine mem_iUnion₂.mpr ⟨w, hw, ?_, ?_⟩
  · rw [← s02_normalGeod_zero Ω w hl]
    exact s02_normalGeod_pos Ω w hl 0
  · rw [← s02_normalGeod_zero Ω w hl, s02_horoPhi_normalGeod Ω w hl 0, Real.exp_zero]

/-- Quasi-isometry helper: a labelled point `q` with label `ℓ` has `ℓ ∈ Ω`, `q ∈ ℍ³` and
`d(q, X(ℓ)) ≤ D` (trivial on `Σ`; on `𝒩 ∪ Σ*`, `X(ℓ)` is a nearest point of `U`, Lemma 2.10, and
`d(q, U) ≤ D`).  Here `U ∩ U* = ∅` (Proposition 2.8(b)) is a hypothesis. -/
theorem s03_qik_pt {Ω Ωs : Set ℂ} {K : ℝ} (h : IsKQuasiPair Ω Ωs K) (hnl : ¬ IsLinePair Ω Ωs)
    (hsep : horoUnion Ω ∩ horoUnion Ωs = ∅) {lab : ℂ × ℝ → ℂ} (hlab : IsLabel Ω lab) {D : ℝ}
    (hD0 : 0 ≤ D) (hDg : ∀ q ∈ gap Ω Ωs, hdistSet q (horoUnion Ω) ≤ D)
    (hDs : ∀ ws ∈ Ωs, hdistSet (epstein Ωs ws) (horoUnion Ω) ≤ D) {q : ℂ × ℝ} {ℓ : ℂ}
    (hq : IsLabelledPt Ω Ωs lab q ℓ) : ℓ ∈ Ω ∧ q ∈ UHS ∧ hdist q (epstein Ω ℓ) ≤ D := by
  have hJ := s03_b0_jordanPair h
  have hJs := s03_b0_jordanPair (s03_qce_swap h)
  have hR := s02_jordanPair_riemannMap hJ
  have hRs := s02_jordanPair_riemannMap hJs
  -- the nearest-point step on `ℍ³ ∖ U`
  have hnear : ∀ q : ℂ × ℝ, q ∈ UHS → q ∉ horoUnion Ω → hdistSet q (horoUnion Ω) ≤ D →
      lab q ∈ Ω ∧ hdist q (epstein Ω (lab q)) ≤ D := by
    intro q hqH hqU hd
    obtain ⟨hℓ, hmin⟩ := hlab.2 q ⟨hqH, hqU⟩
    refine ⟨hℓ, ?_⟩
    rw [(lem_nearest hJ hnl hqH hqU hℓ hmin).2.2.2]
    exact hd
  rcases hq with ⟨hℓ, rfl⟩ | ⟨z, hz, rfl, rfl⟩ | ⟨hqg, rfl⟩
  · refine ⟨hℓ, s03_wd_horoUnion_sub Ω (s03_qik_mem hR hℓ), ?_⟩
    simp [hdist, coshDist, Real.arcosh_zero, hD0]
  · have hmem := s03_qik_mem hRs hz
    have hqH : epstein Ωs z ∈ UHS := s03_wd_horoUnion_sub Ωs hmem
    have hqU : epstein Ωs z ∉ horoUnion Ω := fun hU => by
      have : epstein Ωs z ∈ horoUnion Ω ∩ horoUnion Ωs := ⟨hU, hmem⟩
      rw [hsep] at this
      exact this
    obtain ⟨hℓ, hd⟩ := hnear _ hqH hqU (hDs z hz)
    exact ⟨hℓ, hqH, hd⟩
  · have hqH : q ∈ UHS := hqg.1
    have hqU : q ∉ horoUnion Ω := fun hU => hqg.2 (Or.inl hU)
    obtain ⟨hℓ, hd⟩ := hnear q hqH hqU (hDg q hqg)
    exact ⟨hℓ, hqH, hd⟩

/-- Quasi-isometry helper ((3.5) `eq:QK` given `U ∩ U* = ∅`): two labelled points at distance `≤ r`
have labels at `ρ`-distance `≤ A (r + 2D) + B`. -/
theorem s03_qik_pair {Ω Ωs : Set ℂ} {K : ℝ} (h : IsKQuasiPair Ω Ωs K) (hnl : ¬ IsLinePair Ω Ωs)
    (hsep : horoUnion Ω ∩ horoUnion Ωs = ∅) {A B D : ℝ} (hA : 0 ≤ A)
    (hl : ∀ w ∈ Ω, ∀ w' ∈ Ω, poincareDist Ω w w' ≤ A * hdist (epstein Ω w) (epstein Ω w') + B)
    (hD0 : 0 ≤ D) (hDg : ∀ q ∈ gap Ω Ωs, hdistSet q (horoUnion Ω) ≤ D)
    (hDs : ∀ ws ∈ Ωs, hdistSet (epstein Ωs ws) (horoUnion Ω) ≤ D) {lab : ℂ × ℝ → ℂ}
    (hlab : IsLabel Ω lab) {q q' : ℂ × ℝ} {ℓ ℓ' : ℂ} {r : ℝ} (hq : IsLabelledPt Ω Ωs lab q ℓ)
    (hq' : IsLabelledPt Ω Ωs lab q' ℓ') (hr : hdist q q' ≤ r) :
    poincareDist Ω ℓ ℓ' ≤ A * (r + 2 * D) + B := by
  have hR := s02_jordanPair_riemannMap (s03_b0_jordanPair h)
  obtain ⟨hℓ, hqH, hd⟩ := s03_qik_pt h hnl hsep hlab hD0 hDg hDs hq
  obtain ⟨hℓ', hqH', hd'⟩ := s03_qik_pt h hnl hsep hlab hD0 hDg hDs hq'
  have hX := s03_wd_horoUnion_sub Ω (s03_qik_mem hR hℓ)
  have hX' := s03_wd_horoUnion_sub Ω (s03_qik_mem hR hℓ')
  have htri : hdist (epstein Ω ℓ) (epstein Ω ℓ') ≤ r + 2 * D := by
    have t1 := s02_hdist_triangle hX hqH hX'
    have t2 := s02_hdist_triangle hqH hqH' hX'
    rw [s02_hdist_comm (epstein Ω ℓ) q] at t1
    linarith
  calc poincareDist Ω ℓ ℓ' ≤ A * hdist (epstein Ω ℓ) (epstein Ω ℓ') + B := hl ℓ hℓ ℓ' hℓ'
    _ ≤ A * (r + 2 * D) + B := by nlinarith

/-- Proposition 3.6 `prop:qi`, (3.4) `eq:qi`, `sec03-coarse.tex:197`:
`d_ρ(w, w') ≤ A_K d(X w, X w') + B_K` and `d(X w, X w') ≤ (5/2) d_ρ(w, w')`; the same for `X*`. -/
theorem prop_qi (K : ℝ) :
    ∃ A B : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      (∀ w ∈ Ω, ∀ w' ∈ Ω,
        poincareDist Ω w w' ≤ A * hdist (epstein Ω w) (epstein Ω w') + B ∧
          hdist (epstein Ω w) (epstein Ω w') ≤ 5 / 2 * poincareDist Ω w w') ∧
      ∀ w ∈ Ωs, ∀ w' ∈ Ωs,
        poincareDist Ωs w w' ≤ A * hdist (epstein Ωs w) (epstein Ωs w') + B ∧
          hdist (epstein Ωs w) (epstein Ωs w') ≤ 5 / 2 * poincareDist Ωs w w' := by
  -- The lower bound is `s03_qi_lower` (for `X*`: the swapped pair); the upper bound is the open
  -- helper `s03_qi_upper`.
  obtain ⟨A, B, -, hl⟩ := s03_qi_lower K
  refine ⟨A, B, fun Ω Ωs h hnl => ?_⟩
  obtain ⟨hu, hus⟩ := s03_qi_upper K Ω Ωs h hnl
  exact ⟨fun w hw w' hw' => ⟨hl Ω Ωs h w hw w' hw', hu w hw w' hw'⟩,
    fun w hw w' hw' => ⟨hl Ωs Ω (s03_qce_swap h) w hw w' hw', hus w hw w' hw'⟩⟩

/-- Proposition 3.6 `prop:qi`, (3.5) `eq:QK`, `sec03-coarse.tex:205`: with the constants `A_K, B_K`
of (3.4) and `D_K` of Lemma 3.5, two labelled points at distance `≤ r` have labels at
`ρ`-distance `≤ Q_K(r) = A_K (r + 2 D_K) + B_K`. -/
theorem prop_qi_QK (K : ℝ) :
    ∃ A B D : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      (∀ w ∈ Ω, ∀ w' ∈ Ω,
        poincareDist Ω w w' ≤ A * hdist (epstein Ω w) (epstein Ω w') + B) ∧
      (∀ q ∈ gap Ω Ωs, hdistSet q (horoUnion Ω) ≤ D) ∧
      (∀ ws ∈ Ωs, hdistSet (epstein Ωs ws) (horoUnion Ω) ≤ D) ∧
      ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab → ∀ (q q' : ℂ × ℝ) (ℓ ℓ' : ℂ) (r : ℝ),
        IsLabelledPt Ω Ωs lab q ℓ → IsLabelledPt Ω Ωs lab q' ℓ' → hdist q q' ≤ r →
          poincareDist Ω ℓ ℓ' ≤ A * (r + 2 * D) + B := by
  -- `A, B` from `s03_qi_lower`, `D = max(D_K, 0)` from Lemma 3.5; `U ∩ U* = ∅` is
  -- Proposition 2.8(b).
  obtain ⟨A, B, hA, hl⟩ := s03_qi_lower K
  obtain ⟨D, hD⟩ := lem_width K
  refine ⟨A, B, max D 0, fun Ω Ωs h hnl => ?_⟩
  obtain ⟨hw1, -, hw3⟩ := hD Ω Ωs h hnl
  have hDg : ∀ q ∈ gap Ω Ωs, hdistSet q (horoUnion Ω) ≤ max D 0 := fun q hq =>
    (hw1 q hq).1.trans (le_max_left _ _)
  have hDs : ∀ ws ∈ Ωs, hdistSet (epstein Ωs ws) (horoUnion Ω) ≤ max D 0 := fun ws hws =>
    (hw3 ws hws).trans (le_max_left _ _)
  have hsep := (prop_separation_b (s03_b0_jordanPair h) hnl).2
  exact ⟨hl Ω Ωs h, hDg, hDs, fun lab hlab q q' ℓ ℓ' r hq hq' hr =>
    s03_qik_pair h hnl hsep hA (hl Ω Ωs h) (le_max_right _ _) hDg hDs hlab hq hq' hr⟩

/-- `R`-quasi-isometry helper: a line pair stays a line pair after swapping the sides. -/
theorem s03_cr_line {Ω Ωs : Set ℂ} (hnl : ¬ IsLinePair Ω Ωs) : ¬ IsLinePair Ωs Ω := by
  rintro ⟨a, b, ha, h1, h2⟩
  refine hnl ⟨-a, -b, neg_ne_zero.2 ha, ?_, ?_⟩
  · rw [h2]
    ext z
    simp only [mem_ofPred_eq, neg_mul, ← neg_add, Complex.neg_im]
    constructor <;> intro h <;> linarith
  · rw [h1]
    ext z
    simp only [mem_ofPred_eq, neg_mul, ← neg_add, Complex.neg_im]
    constructor <;> intro h <;> linarith

/-- `R`-quasi-isometry helper: `d(P, Q) ≤ D` in `ℍ³` gives `Q₂ ≤ 2 cosh D · P₂` and
`|P₁ - Q₁| ≤ 2 cosh D · P₂`. -/
theorem s03_cr_close {P Q : ℂ × ℝ} (hP : 0 < P.2) (hQ : 0 < Q.2) {D : ℝ} (hD : hdist P Q ≤ D) :
    Q.2 ≤ 2 * Real.cosh D * P.2 ∧ ‖P.1 - Q.1‖ ≤ 2 * Real.cosh D * P.2 := by
  set c := coshDist P Q with hcdef
  have hpos : 0 < 2 * P.2 * Q.2 := by positivity
  have hkey : ‖P.1 - Q.1‖ ^ 2 + (P.2 - Q.2) ^ 2 = 2 * P.2 * Q.2 * (c - 1) := by
    rw [hcdef]
    unfold coshDist
    field_simp
    ring
  have hc1 : 1 ≤ c := by
    rw [hcdef]
    unfold coshDist
    exact le_add_of_nonneg_right (div_nonneg (by positivity) hpos.le)
  have hcD : c ≤ Real.cosh D := by
    have hD0 : 0 ≤ D := (Real.arcosh_nonneg hc1).trans hD
    rw [← Real.cosh_arcosh hc1]
    refine Real.cosh_le_cosh.2 ?_
    rw [abs_of_nonneg (Real.arcosh_nonneg hc1), abs_of_nonneg hD0]
    exact hD
  have hQle : Q.2 ≤ 2 * c * P.2 :=
    le_of_mul_le_mul_right (by nlinarith [sq_nonneg ‖P.1 - Q.1‖, sq_nonneg P.2]) hQ
  have hPQ : ‖P.1 - Q.1‖ ≤ 2 * c * P.2 := by
    have h : ‖P.1 - Q.1‖ ^ 2 ≤ (2 * c * P.2) ^ 2 := by nlinarith [sq_nonneg (P.2 - Q.2)]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h
  exact ⟨hQle.trans (by nlinarith), hPQ.trans (by nlinarith)⟩

/-- `R`-quasi-isometry helper (continuity at `Γ`): for `x ∈ Γ ∩ ℂ` and `z ∈ Ω*`, if
`d(X*(z), X(w)) ≤ D` then `|w - x| ≤ (96 cosh D + 3)|z - x|` (Lemma 2.3 on both sides). -/
theorem s03_cr_lip {Ω Ωs : Set ℂ} {K : ℝ} (h : IsKQuasiPair Ω Ωs K) {x : ℂ}
    (hx : x ∈ curveOf Ω Ωs) {z w : ℂ} (hz : z ∈ Ωs) (hw : w ∈ Ω) {D : ℝ}
    (hD : hdist (epstein Ωs z) (epstein Ω w) ≤ D) :
    ‖w - x‖ ≤ (96 * Real.cosh D + 3) * ‖z - x‖ := by
  have hR := s02_jordanPair_riemannMap (s03_b0_jordanPair h)
  have hRs := s02_jordanPair_riemannMap (s03_b0_jordanPair (s03_qce_swap h))
  obtain ⟨e1, -, -, -, e5, e6⟩ := lem_ep_position hRs hz
  obtain ⟨f1, -, -, f4, -, f6⟩ := lem_ep_position hR hw
  rw [s03_b0_infDist_s h hz] at e5 e6
  rw [s03_b0_infDist h hw] at f4 f6
  have hξs : 0 < (epstein Ωs z).2 :=
    lt_of_lt_of_le (by have := s02_poincareDensity_pos hRs hz; positivity) e1
  have hξ : 0 < (epstein Ω w).2 :=
    lt_of_lt_of_le (by have := s02_poincareDensity_pos hR hw; positivity) f1
  obtain ⟨c1, c2⟩ := s03_cr_close hξs hξ hD
  have hdz : infDist z (curveOf Ω Ωs) ≤ ‖z - x‖ :=
    (infDist_le_dist_of_mem hx).trans_eq (dist_eq_norm _ _)
  have hch : 1 ≤ Real.cosh D := Real.one_le_cosh D
  have t1 : ‖w - x‖ ≤ ‖w - (epstein Ω w).1‖ + ‖(epstein Ω w).1 - (epstein Ωs z).1‖ +
      ‖(epstein Ωs z).1 - z‖ + ‖z - x‖ := by
    have a1 := norm_sub_le_norm_sub_add_norm_sub w (epstein Ω w).1 x
    have a2 := norm_sub_le_norm_sub_add_norm_sub (epstein Ω w).1 (epstein Ωs z).1 x
    have a3 := norm_sub_le_norm_sub_add_norm_sub (epstein Ωs z).1 z x
    linarith
  rw [norm_sub_rev w (epstein Ω w).1, norm_sub_rev (epstein Ω w).1 (epstein Ωs z).1] at t1
  have hc0 : 0 ≤ Real.cosh D := by linarith
  have s4 : Real.cosh D * (epstein Ωs z).2 ≤ Real.cosh D * (4 * infDist z (curveOf Ω Ωs)) :=
    mul_le_mul_of_nonneg_left e5 hc0
  have s5 : Real.cosh D * infDist z (curveOf Ω Ωs) ≤ Real.cosh D * ‖z - x‖ :=
    mul_le_mul_of_nonneg_left hdz hc0
  have s6 : 0 ≤ Real.cosh D * ‖z - x‖ := mul_nonneg hc0 (norm_nonneg _)
  have s7 : infDist w (curveOf Ω Ωs) ≤ 5 * (epstein Ω w).2 := by linarith
  linarith

/-- Corollary 3.7 `cor:R-qi`, `sec03-coarse.tex:236`: `R = w ∘ X* : (Ω*, ρ*) → (Ω, ρ)` is a
quasi-isometry with constants depending only on `K`, its image is `Q_K(D_K)`-dense, and `R`
extends continuously to `Γ ∩ ℂ` by the identity. -/
theorem cor_R_qi (K : ℝ) :
    ∃ A B E : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab →
        (∀ z ∈ Ωs, lab (epstein Ωs z) ∈ Ω) ∧
        (∀ z ∈ Ωs, ∀ z' ∈ Ωs,
          poincareDist Ω (lab (epstein Ωs z)) (lab (epstein Ωs z')) ≤
              A * poincareDist Ωs z z' + B ∧
            poincareDist Ωs z z' ≤
              A * poincareDist Ω (lab (epstein Ωs z)) (lab (epstein Ωs z')) + B) ∧
        (∀ w ∈ Ω, ∃ z ∈ Ωs, poincareDist Ω (lab (epstein Ωs z)) w ≤ E) ∧
        ∀ x ∈ curveOf Ω Ωs, Tendsto (fun z => lab (epstein Ωs z)) (𝓝[Ωs] x) (𝓝 x) := by
  -- `A, B` from `s03_qi_lower` (uniform over `K`-quasi pairs, so also for the swapped pair),
  -- `D = max(D_K, 0)` from Lemma 3.5.  The quasi-isometry bounds use the open `5/2` helper
  -- `s03_qi_upper`; `U ∩ U* = ∅` is Proposition 2.8(b).
  obtain ⟨A, B, hA, hl⟩ := s03_qi_lower K
  obtain ⟨D, hD⟩ := lem_width K
  set D' := max D 0 with hD'def
  have hD'0 : 0 ≤ D' := le_max_right _ _
  refine ⟨5 / 2 * A, 2 * A * D' + B, A * (D' + 2 * D') + B,
    fun Ω Ωs h hnl lab hlab => ?_⟩
  obtain ⟨hw1, hw2, hw3⟩ := hD Ω Ωs h hnl
  have hDg : ∀ q ∈ gap Ω Ωs, hdistSet q (horoUnion Ω) ≤ D' := fun q hq =>
    (hw1 q hq).1.trans (le_max_left _ _)
  have hDs : ∀ ws ∈ Ωs, hdistSet (epstein Ωs ws) (horoUnion Ω) ≤ D' := fun ws hws =>
    (hw3 ws hws).trans (le_max_left _ _)
  have hJ := s03_b0_jordanPair h
  have hJs := s03_b0_jordanPair (s03_qce_swap h)
  have hR := s02_jordanPair_riemannMap hJ
  have hRs := s02_jordanPair_riemannMap hJs
  have hsep := (prop_separation_b hJ hnl).2
  obtain ⟨hu, hus⟩ := s03_qi_upper K Ω Ωs h hnl
  have hlΩ := hl Ω Ωs h
  have hlΩs := hl Ωs Ω (s03_qce_swap h)
  -- the labelled points `X*(z)`, label `R(z)`
  have hpt : ∀ z ∈ Ωs, lab (epstein Ωs z) ∈ Ω ∧ epstein Ωs z ∈ UHS ∧
      hdist (epstein Ωs z) (epstein Ω (lab (epstein Ωs z))) ≤ D' := fun z hz =>
    s03_qik_pt h hnl hsep hlab hD'0 hDg hDs (Or.inr (Or.inl ⟨z, hz, rfl, rfl⟩))
  have hXU : ∀ w ∈ Ω, epstein Ω w ∈ UHS := fun w hw =>
    s03_wd_horoUnion_sub Ω (s03_qik_mem hR hw)
  refine ⟨fun z hz => (hpt z hz).1, fun z hz z' hz' => ⟨?_, ?_⟩, fun w hw => ?_, fun x hx => ?_⟩
  · -- upper bound: (3.5) and the `5/2` bound for `X*`
    have hq := s03_qik_pair h hnl hsep hA hlΩ hD'0 hDg hDs hlab
      (Or.inr (Or.inl ⟨z, hz, rfl, rfl⟩)) (Or.inr (Or.inl ⟨z', hz', rfl, rfl⟩)) (hus z hz z' hz')
    linarith
  · -- lower bound: (3.4) for `X*` and the comparison `X*(z) ~ X(R z)`
    obtain ⟨h1, hq1, hd1⟩ := hpt z hz
    obtain ⟨h2, hq2, hd2⟩ := hpt z' hz'
    have hX1 := hXU _ h1
    have hX2 := hXU _ h2
    have t1 := s02_hdist_triangle hq1 hX1 hq2
    have t2 := s02_hdist_triangle hX1 hX2 hq2
    rw [s02_hdist_comm (epstein Ω (lab (epstein Ωs z'))) (epstein Ωs z')] at t2
    have hup := hu _ h1 _ h2
    have hlow := hlΩs z hz z' hz'
    have hh : hdist (epstein Ωs z) (epstein Ωs z') ≤
        2 * D' + 5 / 2 * poincareDist Ω (lab (epstein Ωs z)) (lab (epstein Ωs z')) := by
      linarith
    nlinarith
  · -- density: a nearest point of `U*` to `X(w)` is some `X*(z)`, within `D` of `X(w)`
    have hqH := hXU w hw
    have hqU : epstein Ω w ∉ horoUnion Ωs := fun hU => by
      have : epstein Ω w ∈ horoUnion Ω ∩ horoUnion Ωs := ⟨s03_qik_mem hR hw, hU⟩
      rw [hsep] at this
      exact this
    obtain ⟨z, hz, hmin⟩ := lem_proper_min hJs hqH
    have hnear := (lem_nearest hJs (s03_cr_line hnl) hqH hqU hz hmin).2.2.2
    have hdz : hdist (epstein Ωs z) (epstein Ω w) ≤ D' := by
      rw [s02_hdist_comm, hnear]
      exact (hw2 w hw).trans (le_max_left _ _)
    exact ⟨z, hz, s03_qik_pair h hnl hsep hA hlΩ hD'0 hDg hDs hlab
      (Or.inr (Or.inl ⟨z, hz, rfl, rfl⟩)) (Or.inl ⟨hw, rfl⟩) hdz⟩
  · -- continuity at `Γ`: `|R(z) - x| ≤ L |z - x|`
    set L := 96 * Real.cosh D' + 3 with hLdef
    have hL : 0 < L := by have := Real.one_le_cosh D'; linarith
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    refine ⟨ε / L, div_pos hε hL, fun z hz hzx => ?_⟩
    obtain ⟨h1, -, hd1⟩ := hpt z hz
    have hlip := s03_cr_lip h hx hz h1 hd1
    rw [dist_eq_norm] at hzx ⊢
    calc ‖lab (epstein Ωs z) - x‖ ≤ L * ‖z - x‖ := hlip
      _ < L * (ε / L) := mul_lt_mul_of_pos_left hzx hL
      _ = ε := by field_simp

/-- Selection-change helper: `w ↦ k_p(w)` is Borel on `ℂ` (explicit on `Ω` through a Riemann map,
and `1` off `Ω`, where `d_ρ(p, ·)` is `sInf ∅ = 0`). -/
theorem s03_sc_meas {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {p : ℂ}
    (hp : p ∈ Ω) : Measurable (intrKernel Ω p) := by
  classical
  obtain ⟨f, hf⟩ := hΩ
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hψ : IsConformalOnto (Function.invFunOn f unitDisc) Ω unitDisc := hf.symm isOpen_ball
  have hfψ : ∀ v ∈ Ω, f (Function.invFunOn f unitDisc v) = v := fun v hv =>
    Function.invFunOn_eq (show v ∈ f '' unitDisc by rw [hf.2.2]; exact hv)
  have hψm : MapsTo (Function.invFunOn f unitDisc) Ω unitDisc := fun v hv => by
    have := mem_image_of_mem (Function.invFunOn f unitDisc) hv
    rwa [hψ.2.2] at this
  have hψc : ContinuousOn (Function.invFunOn f unitDisc) Ω := hψ.1.continuousOn
  generalize Function.invFunOn f unitDisc = ψ at hfψ hψm hψc
  set a := ψ p with hadef
  have ha : a ∈ unitDisc := hψm hp
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  set G : ℂ → ℝ := fun z => (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖1 - conj a * z‖ ^ 2 with hGdef
  have hGc : ContinuousOn G unitDisc := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => ?_
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 (blaschke_den_ne_zero ha1 (mem_ball_zero_iff.mp hz)))
  have heq : intrKernel Ω p = Ω.piecewise (fun w => G (ψ w)) (fun _ => 1) := by
    funext w
    by_cases hw : w ∈ Ω
    · rw [Set.piecewise_eq_of_mem _ _ _ hw]
      have h := s02_intrKernel_eq hf ha (hψm hw)
      rw [hfψ p hp, hfψ w hw] at h
      exact h
    · rw [Set.piecewise_eq_of_notMem _ _ _ hw]
      have hempty : {d : ℝ | ∃ (g : ℂ → ℂ) (a z : ℂ), IsConformalOnto g unitDisc Ω ∧
          a ∈ unitDisc ∧ z ∈ unitDisc ∧ g a = p ∧ g z = w ∧ d = diskDist a z} = ∅ := by
        ext d
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨g, b, z, hg, -, hz, -, hgz, -⟩
        exact hw (by rw [← hgz, ← hg.2.2]; exact mem_image_of_mem g hz)
      unfold intrKernel poincareDist
      rw [hempty, Real.sInf_empty, zero_div, Real.cosh_zero, inv_one, one_pow]
  rw [heq]
  exact ContinuousOn.measurable_piecewise (hGc.comp hψc hψm) continuousOn_const
    hΩo.measurableSet

/-- Selection-change helper: for `q ∈ 𝒩 ∪ Σ*` and two labels, `w₁(q), w₂(q) ∈ Ω` and
`d_ρ(w₁(q), w₂(q)) ≤ 2AD + B` (both `X(wᵢ(q))` are within `D` of `q`).  Here `U ∩ U* = ∅`
(Proposition 2.8(b)) is a hypothesis. -/
theorem s03_sc_pt {Ω Ωs : Set ℂ} {K : ℝ} (h : IsKQuasiPair Ω Ωs K) (hnl : ¬ IsLinePair Ω Ωs)
    (hsep : horoUnion Ω ∩ horoUnion Ωs = ∅) {A B D : ℝ} (hA : 0 ≤ A)
    (hl : ∀ w ∈ Ω, ∀ w' ∈ Ω, poincareDist Ω w w' ≤ A * hdist (epstein Ω w) (epstein Ω w') + B)
    (hD0 : 0 ≤ D) (hDg : ∀ q ∈ gap Ω Ωs, hdistSet q (horoUnion Ω) ≤ D)
    (hDs : ∀ ws ∈ Ωs, hdistSet (epstein Ωs ws) (horoUnion Ω) ≤ D) {lab₁ lab₂ : ℂ × ℝ → ℂ}
    (hlab₁ : IsLabel Ω lab₁) (hlab₂ : IsLabel Ω lab₂) {q : ℂ × ℝ}
    (hq : q ∈ gap Ω Ωs ∪ epstein Ωs '' Ωs) :
    lab₁ q ∈ Ω ∧ lab₂ q ∈ Ω ∧ poincareDist Ω (lab₁ q) (lab₂ q) ≤ A * (2 * D) + B := by
  have hR := s02_jordanPair_riemannMap (s03_b0_jordanPair h)
  have hpt : ∀ lab : ℂ × ℝ → ℂ, IsLabelledPt Ω Ωs lab q (lab q) := by
    intro lab
    rcases hq with hqg | ⟨z, hz, rfl⟩
    · exact Or.inr (Or.inr ⟨hqg, rfl⟩)
    · exact Or.inr (Or.inl ⟨z, hz, rfl, rfl⟩)
  obtain ⟨h1, hqH, hd1⟩ := s03_qik_pt h hnl hsep hlab₁ hD0 hDg hDs (hpt lab₁)
  obtain ⟨h2, -, hd2⟩ := s03_qik_pt h hnl hsep hlab₂ hD0 hDg hDs (hpt lab₂)
  have hX1 := s03_wd_horoUnion_sub Ω (s03_qik_mem hR h1)
  have hX2 := s03_wd_horoUnion_sub Ω (s03_qik_mem hR h2)
  have htri : hdist (epstein Ω (lab₁ q)) (epstein Ω (lab₂ q)) ≤ 2 * D := by
    have t := s02_hdist_triangle hX1 hqH hX2
    rw [s02_hdist_comm (epstein Ω (lab₁ q)) q] at t
    linarith
  refine ⟨h1, h2, (hl _ h1 _ h2).trans ?_⟩
  nlinarith

/-- Selection-change helper ((2.17) `eq:kernel-lip`): `d_ρ(w₁, w₂) ≤ C` gives
`k_p(w₁) ≤ e^C k_p(w₂)` in `ℝ≥0∞`. -/
theorem s03_sc_kernel {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {p w₁ w₂ : ℂ}
    {C : ℝ} (hp : p ∈ Ω) (h1 : w₁ ∈ Ω) (h2 : w₂ ∈ Ω) (hC : poincareDist Ω w₁ w₂ ≤ C) :
    ENNReal.ofReal (intrKernel Ω p w₁) ≤
      ENNReal.ofReal (Real.exp C) * ENNReal.ofReal (intrKernel Ω p w₂) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos C).le]
  refine ENNReal.ofReal_le_ofReal ((eq_kernel_lip_b hΩ hp h1 h2).trans ?_)
  have hk : 0 ≤ intrKernel Ω p w₂ := by unfold intrKernel; positivity
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hC) hk

/-- Lemma 3.8 `lem:selection-change`, `sec03-coarse.tex:257`: two labels differ by at most
`Q_K(0)` in `d_ρ` on `𝒩 ∪ Σ*`; hence `K_*` and `K_V` computed with them differ at most by the
factor `e^{Q_K(0)}`. -/
theorem lem_selection_change (K : ℝ) :
    ∃ C : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ lab₁ lab₂ : ℂ × ℝ → ℂ, IsLabel Ω lab₁ → IsLabel Ω lab₂ →
        (∀ q ∈ gap Ω Ωs ∪ epstein Ωs '' Ωs, poincareDist Ω (lab₁ q) (lab₂ q) ≤ C) ∧
        ∀ p ∈ Ω, Kst Ω Ωs lab₁ p ≤ ENNReal.ofReal (Real.exp C) * Kst Ω Ωs lab₂ p ∧
          KV Ω Ωs lab₁ p ≤ ENNReal.ofReal (Real.exp C) * KV Ω Ωs lab₂ p := by
  -- `C = Q_K(0) = 2 A D + B` with `A, B` from `s03_qi_lower` and `D = max(D_K, 0)` from Lemma 3.5;
  -- `U ∩ U* = ∅` is Proposition 2.8(b).
  obtain ⟨A, B, hA, hl⟩ := s03_qi_lower K
  obtain ⟨D, hD⟩ := lem_width K
  refine ⟨A * (2 * max D 0) + B, fun Ω Ωs h hnl lab₁ lab₂ hlab₁ hlab₂ => ?_⟩
  obtain ⟨hw1, -, hw3⟩ := hD Ω Ωs h hnl
  have hDg : ∀ q ∈ gap Ω Ωs, hdistSet q (horoUnion Ω) ≤ max D 0 := fun q hq =>
    (hw1 q hq).1.trans (le_max_left _ _)
  have hDs : ∀ ws ∈ Ωs, hdistSet (epstein Ωs ws) (horoUnion Ω) ≤ max D 0 := fun ws hws =>
    (hw3 ws hws).trans (le_max_left _ _)
  have hsep := (prop_separation_b (s03_b0_jordanPair h) hnl).2
  have hpt := fun q (hq : q ∈ gap Ω Ωs ∪ epstein Ωs '' Ωs) =>
    s03_sc_pt h hnl hsep hA (hl Ω Ωs h) (le_max_right _ _) hDg hDs hlab₁ hlab₂ hq
  have hR := s02_jordanPair_riemannMap (s03_b0_jordanPair h)
  refine ⟨fun q hq => (hpt q hq).2.2, fun p hp => ⟨?_, ?_⟩⟩
  · -- `K_*`: pointwise on `Ω*`, which carries `curvMass Ω*`
    have hΩso : IsOpen Ωs := (s03_b0_basic h).2.1
    have hae : ∀ᵐ z ∂curvMass Ωs, z ∈ Ωs :=
      (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩso.measurableSet)
    unfold Kst
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae (hae.mono fun z hz => ?_)
    obtain ⟨h1, h2, hd⟩ := hpt _ (Or.inr ⟨z, hz, rfl⟩)
    exact s03_sc_kernel hR hp h1 h2 hd
  · -- `K_V`: pointwise on `𝒩`
    unfold KV
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono (measurable_const.mul
      (ENNReal.measurable_ofReal.comp ((s03_sc_meas hR hp).comp hlab₂.1))) fun q hq => ?_
    obtain ⟨h1, h2, hd⟩ := hpt q (Or.inl hq)
    exact s03_sc_kernel hR hp h1 h2 hd

/-! ## §3.6 Competing parameters and unique labels -/

/-- Competing-parameters helper: with `X(w) = (W, ξ)` placed as in Lemma 2.3, `d' ≤ d + |w - w'|`
and `|W - w'|² + ξ² ≤ 4 T ξ d'` (from `Φ_{X(w)}(w') ≤ T` and Koebe), `R_e ≤ 440 T²`. -/
theorem s03_cp_Re {W w w' : ℂ} {ξ d d' T : ℝ} (hξ : 0 < ξ) (hd' : 0 < d') (hT : 1 ≤ T)
    (h1 : d / 5 ≤ ξ) (h2 : ξ ≤ 4 * d) (h3 : ‖W - w‖ ≤ 2 * d) (hdd : d' ≤ d + ‖w - w'‖)
    (hΦ : ‖W - w'‖ ^ 2 + ξ ^ 2 ≤ 4 * T * ξ * d') :
    ‖w - w'‖ / min d d' ≤ 440 * T ^ 2 := by
  have hd : 0 < d := by linarith
  have hT0 : 0 < T := by linarith
  set a := ‖W - w'‖ with hadef
  have ha0 : 0 ≤ a := norm_nonneg _
  have hww : ‖w - w'‖ ≤ 2 * d + a := by
    have := norm_sub_le_norm_sub_add_norm_sub w W w'
    rw [norm_sub_rev w W] at this
    linarith
  -- `ξ ≤ 4 T d'`, so `d' ≥ d/(20T)`
  have hξd' : ξ ≤ 4 * T * d' := le_of_mul_le_mul_right (by nlinarith [sq_nonneg a]) hξ
  -- `a² ≤ 16 T d d'`
  have ha2 : a ^ 2 ≤ 16 * T * d * d' := by nlinarith [sq_nonneg ξ]
  -- `d' ≤ 25 T d`
  have hd'le : d' ≤ 25 * T * d := by
    by_contra hlt
    push Not at hlt
    have hx : 3 * d < d' := by nlinarith
    have hsq : (d' - 3 * d) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    nlinarith [mul_pos hd hT0, mul_pos (mul_pos hd hT0) hT0]
  have ha : a ≤ 20 * T * d := by
    have h : a ^ 2 ≤ (20 * T * d) ^ 2 := by nlinarith [mul_pos hd hT0]
    exact (pow_le_pow_iff_left₀ ha0 (by positivity) two_ne_zero).1 h
  have hm : d / (20 * T) ≤ min d d' := by
    refine le_min ?_ ?_
    · rw [div_le_iff₀ (by positivity)]; nlinarith
    · rw [div_le_iff₀ (by positivity)]; nlinarith
  rw [div_le_iff₀ (lt_min hd hd')]
  calc ‖w - w'‖ ≤ 22 * T * d := by nlinarith
    _ = 440 * T ^ 2 * (d / (20 * T)) := by field_simp; ring
    _ ≤ 440 * T ^ 2 * min d d' := mul_le_mul_of_nonneg_left hm (by positivity)

/-- Lemma 3.9 `lem:competing`, (3.6) `eq:competing`, `sec03-coarse.tex:272`:
`Φ_{X(w)}(w') ≤ T ⇒ d_ρ(w, w') ≤ C_K (1 + log T)` for `T ≥ 1`. -/
theorem lem_competing (K : ℝ) :
    ∃ C : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ w ∈ Ω, ∀ w' ∈ Ω, ∀ T : ℝ, 1 ≤ T → horoPhi Ω (epstein Ω w) w' ≤ T →
        poincareDist Ω w w' ≤ C * (1 + Real.log T) := by
  -- `R_e ≤ 440 T²` (`s03_cp_Re`) and Lemma 3.3.  The hypothesis `¬ IsLinePair Ω Ωs` is not needed:
  -- the statement stays true without it.
  obtain ⟨C, hC⟩ := s03_dd_side K
  set C' := max C 0 with hC'def
  have hC'0 : 0 ≤ C' := le_max_right _ _
  refine ⟨C' * (Real.log 441 + 2), fun Ω Ωs h hnl w hw w' hw' T hT hΦ => ?_⟩
  have _hnl := hnl
  obtain ⟨-, -, -, hR⟩ := s03_b0_basic h
  obtain ⟨f, hf⟩ := hR
  have hdd := hC Ω Ωs h w hw w' hw'
  obtain ⟨e1, -, -, e4, e5, e6⟩ := lem_ep_position ⟨f, hf⟩ hw
  rw [s03_b0_infDist h hw] at e4 e5 e6
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hw
  have hξ : 0 < (epstein Ω w).2 := lt_of_lt_of_le (by positivity) e1
  -- Koebe at `w'`: `λ(w') ≥ 1/(2 d')`
  obtain ⟨z, hz, rfl⟩ : w' ∈ f '' unitDisc := by rw [hf.2.2]; exact hw'
  have hk := (lem_koebe_a hf hz).2.2.1
  rw [s03_b0_infDist h hw'] at hk
  have hd' : 0 < infDist (f z) (curveOf Ω Ωs) := by
    rw [← s03_b0_infDist h hw']; exact s02_infDist_pos hf hw'
  have hΦ' : ‖(epstein Ω w).1 - f z‖ ^ 2 + (epstein Ω w).2 ^ 2 ≤
      4 * T * (epstein Ω w).2 * infDist (f z) (curveOf Ω Ωs) := by
    have hΦd : poincareDensity Ω (f z) * (‖(epstein Ω w).1 - f z‖ ^ 2 + (epstein Ω w).2 ^ 2) ≤
        T * (2 * (epstein Ω w).2) := by
      have : horoPhi Ω (epstein Ω w) (f z) = poincareDensity Ω (f z) *
          (‖(epstein Ω w).1 - f z‖ ^ 2 + (epstein Ω w).2 ^ 2) / (2 * (epstein Ω w).2) := rfl
      rw [this, div_le_iff₀ (by positivity)] at hΦ
      exact hΦ
    have hN : 0 ≤ ‖(epstein Ω w).1 - f z‖ ^ 2 + (epstein Ω w).2 ^ 2 := by positivity
    have hk' : 1 ≤ 2 * infDist (f z) (curveOf Ω Ωs) * poincareDensity Ω (f z) := by
      rw [div_le_iff₀ (by positivity)] at hk; linarith
    nlinarith
  have hdist' : infDist (f z) (curveOf Ω Ωs) ≤ infDist w (curveOf Ω Ωs) + ‖w - f z‖ := by
    have := infDist_le_infDist_add_dist (x := f z) (y := w) (s := curveOf Ω Ωs)
    rwa [dist_eq_norm, norm_sub_rev] at this
  have hRe := s03_cp_Re hξ hd' hT e4 e5 e6 hdist' hΦ'
  set R := ‖w - f z‖ / min (infDist w (curveOf Ω Ωs)) (infDist (f z) (curveOf Ω Ωs)) with hRdef
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    exact div_nonneg (norm_nonneg _) (le_min infDist_nonneg infDist_nonneg)
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlog : Real.log (1 + R) ≤ Real.log 441 + 2 * Real.log T := by
    calc Real.log (1 + R) ≤ Real.log (441 * T ^ 2) :=
          Real.log_le_log (by linarith) (by nlinarith)
      _ = Real.log 441 + 2 * Real.log T := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  have hL0 : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
  have h441 : 0 ≤ Real.log 441 := Real.log_nonneg (by norm_num)
  calc poincareDist Ω w (f z) ≤ C * Real.log (1 + R) := hdd
    _ ≤ C' * Real.log (1 + R) := mul_le_mul_of_nonneg_right (le_max_left _ _) hL0
    _ ≤ C' * (Real.log 441 + 2 * Real.log T) := mul_le_mul_of_nonneg_left hlog hC'0
    _ ≤ C' * (Real.log 441 + 2) * (1 + Real.log T) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (by nlinarith) hC'0

/-- Algebra of (3.7): the second derivative of `Φ_q` along a diameter of a Riemann map `G`, with
`G'(0) = α₁`, `G''(0) = α₂`, `G'''(0) = α₃`, `a = q₁ - G(0)`, `b = q₂`, `ρ = |α₁|`. -/
theorem s03_hess_alg (α₁ α₂ α₃ a : ℂ) {b ρ : ℝ} (hb : b ≠ 0) (hρ : ρ ≠ 0) (hα : α₁ ≠ 0) :
    let m0 := α₁.re ^ 2 + α₁.im ^ 2
    let m1 := 2 * (α₁.re * α₂.re + α₁.im * α₂.im)
    let m2 := 2 * (α₂.re ^ 2 + α₂.im ^ 2) + 2 * (α₁.re * α₃.re + α₁.im * α₃.im)
    let n0 := a.re ^ 2 + a.im ^ 2 + b ^ 2
    let n1 := 2 * (a.re * (-α₁).re + a.im * (-α₁).im)
    let n2 := 2 * ((-α₁).re ^ 2 + (-α₁).im ^ 2) + 2 * (a.re * (-α₂).re + a.im * (-α₂).im)
    let k0 := 1 / ρ
    let k1 := -m1 / (2 * m0 * ρ)
    let k2 := -m2 / (2 * m0 * ρ) + 3 * m1 ^ 2 / (4 * m0 ^ 2 * ρ)
    let Φ := n0 / (b * ρ)
    let ψ := -α₂ / (2 * α₁ ^ 2)
    (n2 * k0 + 2 * n0 * k0 + n0 * k2 + 2 * n1 * k1) / b =
      ((Φ : ℂ) * (-((α₃ * α₁ - α₂ * α₂) / α₁ ^ 2 - 1 / 2 * (α₂ / α₁) ^ 2))).re +
        2 * (Φ * (4 / m0) / 4 + 2 / ρ / (2 * b) *
          (n0 * (ψ.re ^ 2 + ψ.im ^ 2) - 2 * (ψ * a).re + 1)) * m0 := by
  intro m0 m1 m2 n0 n1 n2 k0 k1 k2 Φ ψ
  have hm : m0 ≠ 0 := by
    have : 0 < m0 := by
      have h := Complex.normSq_pos.mpr hα
      rw [Complex.normSq_apply] at h
      show 0 < α₁.re ^ 2 + α₁.im ^ 2
      nlinarith
    exact this.ne'
  have hinv : (α₁ ^ 2)⁻¹ = conj α₁ ^ 2 * ((1 / m0 ^ 2 : ℝ) : ℂ) := by
    have hc : α₁ * conj α₁ = ((m0 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_apply]
      simp only [m0]
      push_cast
      ring
    have hm' : ((m0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm
    rw [eq_comm, ← mul_inv_eq_one₀ (inv_ne_zero (pow_ne_zero 2 hα)), inv_inv]
    calc conj α₁ ^ 2 * ((1 / m0 ^ 2 : ℝ) : ℂ) * α₁ ^ 2 =
          (α₁ * conj α₁) ^ 2 * ((1 / m0 ^ 2 : ℝ) : ℂ) := by ring
      _ = 1 := by rw [hc]; push_cast; field_simp
  have hS : -((α₃ * α₁ - α₂ * α₂) / α₁ ^ 2 - 1 / 2 * (α₂ / α₁) ^ 2) =
      (-(α₃ * α₁) + 3 / 2 * α₂ ^ 2) * (α₁ ^ 2)⁻¹ := by
    field_simp
    ring
  have hψ : ψ = -α₂ / 2 * (α₁ ^ 2)⁻¹ := by
    show -α₂ / (2 * α₁ ^ 2) = _
    field_simp
  rw [hS, hψ, hinv]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, Complex.div_ofNat_re, Complex.div_ofNat_im, pow_two,
    Complex.re_ofNat, Complex.im_ofNat]
  simp only [m0, m1, m2, n0, n1, n2, k0, k1, k2, Φ, Complex.neg_re, Complex.neg_im] at *
  field_simp
  ring


/-- Second-order jets: products. -/
theorem s03_hess_jet_mul {f g : ℝ → ℝ} {s0 b1 c1 b2 c2 : ℝ}
    (hf : ∃ f' : ℝ → ℝ, (∀ᶠ s in 𝓝 s0, HasDerivAt f (f' s) s) ∧ f' s0 = b1 ∧ HasDerivAt f' c1 s0)
    (hg : ∃ g' : ℝ → ℝ, (∀ᶠ s in 𝓝 s0, HasDerivAt g (g' s) s) ∧ g' s0 = b2 ∧ HasDerivAt g' c2 s0) :
    ∃ h' : ℝ → ℝ, (∀ᶠ s in 𝓝 s0, HasDerivAt (fun s => f s * g s) (h' s) s) ∧
      h' s0 = b1 * g s0 + f s0 * b2 ∧ HasDerivAt h' (c1 * g s0 + 2 * b1 * b2 + f s0 * c2) s0 := by
  obtain ⟨f', hf1, hf2, hf3⟩ := hf
  obtain ⟨g', hg1, hg2, hg3⟩ := hg
  refine ⟨fun s => f' s * g s + f s * g' s, ?_, ?_, ?_⟩
  · filter_upwards [hf1, hg1] with s h1 h2
    exact h1.mul h2
  · show f' s0 * g s0 + f s0 * g' s0 = _
    rw [hf2, hg2]
  · have h1 := hf1.self_of_nhds
    have h2 := hg1.self_of_nhds
    refine ((hf3.mul h2).add (h1.mul hg3)).congr_deriv ?_
    rw [hf2, hg2]
    ring

/-- Second-order jets: constants. -/
theorem s03_hess_jet_const (k s0 : ℝ) :
    ∃ h' : ℝ → ℝ, (∀ᶠ s in 𝓝 s0, HasDerivAt (fun _ : ℝ => k) (h' s) s) ∧ h' s0 = 0 ∧
      HasDerivAt h' 0 s0 :=
  ⟨fun _ => 0, Eventually.of_forall fun s => hasDerivAt_const s k, rfl, hasDerivAt_const s0 0⟩

/-- Second-order jets: adding a constant. -/
theorem s03_hess_jet_add_const {f : ℝ → ℝ} {s0 b c : ℝ} (k : ℝ)
    (hf : ∃ f' : ℝ → ℝ, (∀ᶠ s in 𝓝 s0, HasDerivAt f (f' s) s) ∧ f' s0 = b ∧ HasDerivAt f' c s0) :
    ∃ h' : ℝ → ℝ, (∀ᶠ s in 𝓝 s0, HasDerivAt (fun s => f s + k) (h' s) s) ∧ h' s0 = b ∧
      HasDerivAt h' c s0 := by
  obtain ⟨f', hf1, hf2, hf3⟩ := hf
  exact ⟨f', hf1.mono fun s h => h.add_const k, hf2, hf3⟩

/-- Second-order jets: eventually equal functions. -/
theorem s03_hess_jet_congr {f g : ℝ → ℝ} {s0 b c : ℝ} (h : f =ᶠ[𝓝 s0] g)
    (hf : ∃ f' : ℝ → ℝ, (∀ᶠ s in 𝓝 s0, HasDerivAt f (f' s) s) ∧ f' s0 = b ∧ HasDerivAt f' c s0) :
    ∃ g' : ℝ → ℝ, (∀ᶠ s in 𝓝 s0, HasDerivAt g (g' s) s) ∧ g' s0 = b ∧ HasDerivAt g' c s0 := by
  obtain ⟨f', hf1, hf2, hf3⟩ := hf
  refine ⟨f', ?_, hf2, hf3⟩
  filter_upwards [hf1, h.eventuallyEq_nhds] with s h1 h2
  exact h1.congr_of_eventuallyEq h2.symm

/-- Second-order jets: `(√f)⁻¹` for `f > 0`. -/
theorem s03_hess_jet_invsqrt {f : ℝ → ℝ} {s0 b c : ℝ} (hpos : 0 < f s0)
    (hf : ∃ f' : ℝ → ℝ, (∀ᶠ s in 𝓝 s0, HasDerivAt f (f' s) s) ∧ f' s0 = b ∧ HasDerivAt f' c s0) :
    ∃ h' : ℝ → ℝ, (∀ᶠ s in 𝓝 s0, HasDerivAt (fun s => (√(f s))⁻¹) (h' s) s) ∧
      h' s0 = -b / (2 * f s0 * √(f s0)) ∧
      HasDerivAt h' (-c / (2 * f s0 * √(f s0)) + 3 * b ^ 2 / (4 * f s0 ^ 2 * √(f s0))) s0 := by
  obtain ⟨f', hf1, hf2, hf3⟩ := hf
  have hfd := hf1.self_of_nhds
  have hev : ∀ᶠ s in 𝓝 s0, 0 < f s := hfd.continuousAt.eventually (lt_mem_nhds hpos)
  refine ⟨fun s => -f' s / (2 * f s * √(f s)), ?_, by show -f' s0 / _ = _; rw [hf2], ?_⟩
  · filter_upwards [hf1, hev] with s h1 h2
    have hs := Real.sqrt_pos.mpr h2
    refine ((h1.sqrt h2.ne').inv hs.ne').congr_deriv ?_
    have := Real.sq_sqrt h2.le
    field_simp
    rw [this]
  · have hs := Real.sqrt_pos.mpr hpos
    have hsq : HasDerivAt (fun s => √(f s)) (b / (2 * √(f s0))) s0 := by
      have := hfd.sqrt hpos.ne'
      rwa [hf2] at this
    have hD : HasDerivAt (fun s => 2 * f s * √(f s)) (2 * b * √(f s0) + 2 * f s0 * (b / (2 * √(f s0)))) s0 := by
      have := ((hfd.const_mul 2).mul hsq)
      rw [hf2] at this
      exact this
    refine (hf3.neg.div hD (by positivity)).congr_deriv ?_
    simp only [Pi.neg_apply, hf2]
    have h2 := Real.sq_sqrt hpos.le
    set r := √(f s0)
    rw [← h2]
    field_simp
    ring

/-- Second-order jets: `‖u‖²` for a curve `u : ℝ → ℂ`. -/
theorem s03_hess_jet_normSq {u u' : ℝ → ℂ} {s0 : ℝ} {u2 : ℂ}
    (hu1 : ∀ᶠ s in 𝓝 s0, HasDerivAt u (u' s) s) (hu2 : HasDerivAt u' u2 s0) :
    ∃ h' : ℝ → ℝ, (∀ᶠ s in 𝓝 s0, HasDerivAt (fun s => ‖u s‖ ^ 2) (h' s) s) ∧
      h' s0 = 2 * ((u s0).re * (u' s0).re + (u s0).im * (u' s0).im) ∧
      HasDerivAt h' (2 * ((u' s0).re ^ 2 + (u' s0).im ^ 2) +
        2 * ((u s0).re * u2.re + (u s0).im * u2.im)) s0 := by
  have hre : ∀ {v : ℝ → ℂ} {d : ℂ} {s : ℝ}, HasDerivAt v d s →
      HasDerivAt (fun s => (v s).re) d.re s := fun h =>
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt _ h
  have him : ∀ {v : ℝ → ℂ} {d : ℂ} {s : ℝ}, HasDerivAt v d s →
      HasDerivAt (fun s => (v s).im) d.im s := fun h =>
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt _ h
  have he : (fun s => ‖u s‖ ^ 2) = fun s => (u s).re * (u s).re + (u s).im * (u s).im := by
    funext s
    rw [Complex.sq_norm, Complex.normSq_apply]
  rw [he]
  refine ⟨fun s => 2 * ((u s).re * (u' s).re + (u s).im * (u' s).im), ?_, rfl, ?_⟩
  · filter_upwards [hu1] with s h
    refine (((hre h).mul (hre h)).add ((him h).mul (him h))).congr_deriv ?_
    ring
  · have h := hu1.self_of_nhds
    refine ((((hre h).mul (hre hu2)).add ((him h).mul (him hu2))).const_mul 2).congr_deriv ?_
    ring

/-- Second-order jets along `ℝ` of a holomorphic map of `𝔻` at `0`. -/
theorem s03_hess_hjet {H : ℂ → ℂ} (hH : DifferentiableOn ℂ H unitDisc) :
    (∀ᶠ s : ℝ in 𝓝 (0 : ℝ), HasDerivAt (fun s : ℝ => H (s : ℂ)) (deriv H (s : ℂ)) s) ∧
      HasDerivAt (fun s : ℝ => deriv H (s : ℂ)) (deriv (deriv H) 0) (0 : ℝ) := by
  have hH' : DifferentiableOn ℂ (deriv H) unitDisc := hH.deriv isOpen_ball
  have hmem : ∀ s : ℝ, s ∈ Ioo (-1 : ℝ) 1 → ((s : ℂ)) ∈ unitDisc := fun s hs => by
    refine mem_ball_zero_iff.mpr ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]
    exact hs
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨?_, ?_⟩
  · filter_upwards [Ioo_mem_nhds h0.1 h0.2] with s hs
    exact (hH.differentiableAt (isOpen_ball.mem_nhds (hmem s hs))).hasDerivAt.comp_ofReal
  · have h := (hH'.differentiableAt (isOpen_ball.mem_nhds (hmem 0 h0))).hasDerivAt.comp_ofReal
    rw [Complex.ofReal_zero] at h
    exact h

/-- Second derivative of a composite `Ψ ∘ x` from jets. -/
theorem s03_hess_jet_comp {Ψ x x' : ℝ → ℝ} {t0 s0 b c x2 : ℝ} (hxt : x t0 = s0)
    (hΨ : ∃ Ψ' : ℝ → ℝ, (∀ᶠ s in 𝓝 s0, HasDerivAt Ψ (Ψ' s) s) ∧ Ψ' s0 = b ∧ HasDerivAt Ψ' c s0)
    (hx : ∀ t, HasDerivAt x (x' t) t) (hx2 : HasDerivAt x' x2 t0) :
    deriv (deriv (Ψ ∘ x)) t0 = c * x' t0 ^ 2 + b * x2 := by
  subst hxt
  obtain ⟨Ψ', h1, h2, h3⟩ := hΨ
  have hev : ∀ᶠ t in 𝓝 t0, HasDerivAt Ψ (Ψ' (x t)) (x t) :=
    (hx t0).continuousAt.eventually h1
  have hd : deriv (Ψ ∘ x) =ᶠ[𝓝 t0] fun t => Ψ' (x t) * x' t := by
    filter_upwards [hev] with t ht
    exact (ht.comp t (hx t)).deriv
  rw [hd.deriv_eq]
  refine ((h3.comp t0 (hx t0)).mul hx2).deriv.trans ?_
  rw [Function.comp_apply, h2]
  ring

/-- The velocity of a `ρ`-geodesic never vanishes. -/
theorem s03_hess_deriv_ne {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    {γ : ℝ → ℂ} (hγ : IsRhoGeodesic Ω γ) (t : ℝ) : deriv γ t ≠ 0 := by
  obtain ⟨g, c, hg, -, hc, hγg⟩ := s03_geo_eq hΩ hγ
  have hfun : γ = fun t => g (Real.tanh (c * t / 2)) := funext hγg
  rw [hfun, (s03_geo_hasDerivAt hg c t).deriv]
  have hmem : ((Real.tanh (c * t / 2) : ℝ) : ℂ) ∈ unitDisc := by
    refine mem_ball_zero_iff.mpr ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_tanh_lt_one _
  refine mul_ne_zero (deriv_ne_zero_of_injOn isOpen_ball hg.1 hg.2.1 hmem) ?_
  rw [Complex.ofReal_ne_zero]
  have h1 := Real.abs_tanh_lt_one (c * t / 2)
  have h2 : 0 < 1 - Real.tanh (c * t / 2) ^ 2 := by
    nlinarith [abs_nonneg (Real.tanh (c * t / 2)), sq_abs (Real.tanh (c * t / 2))]
  positivity

/-- `t ↦ Φ_q(γ(t))` is smooth along a `ρ`-geodesic. -/
theorem s03_hess_phi_contDiff {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    {γ : ℝ → ℂ} (hγ : IsRhoGeodesic Ω γ) (q : ℂ × ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun t => horoPhi Ω q (γ t)) := by
  obtain ⟨g, c, hg, -, -, hγg⟩ := s03_geo_eq hΩ hγ
  have hg' : DifferentiableOn ℂ (deriv g) unitDisc := hg.1.deriv isOpen_ball
  set x : ℝ → ℝ := fun t => Real.tanh (c * t / 2) with hxdef
  have hxm : ∀ t, ((x t : ℝ) : ℂ) ∈ unitDisc := fun t => by
    refine mem_ball_zero_iff.mpr ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_tanh_lt_one _
  have hx1 : ∀ t, 0 < 1 - x t ^ 2 := fun t => by
    have h1 := Real.abs_tanh_lt_one (c * t / 2)
    nlinarith [abs_nonneg (Real.tanh (c * t / 2)), sq_abs (Real.tanh (c * t / 2))]
  have hxc : ContDiff ℝ n x := by
    have : x = fun t : ℝ => Real.sinh (c * t / 2) / Real.cosh (c * t / 2) := by
      funext t
      exact Real.tanh_eq_sinh_div_cosh _
    rw [this]
    exact (Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id |>.div_const 2)).div
      (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id |>.div_const 2))
      (fun x => (Real.cosh_pos _).ne')
  have hxC : ContDiff ℝ n fun t => ((x t : ℝ) : ℂ) := Complex.ofRealCLM.contDiff.comp hxc
  have hcomp : ∀ {h : ℂ → ℂ}, DifferentiableOn ℂ h unitDisc → ∀ t,
      ContDiffAt ℝ n (fun t => h (x t)) t := fun hh t =>
    (((hh.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds (hxm t))).restrict_scalars
      ℝ).comp t hxC.contDiffAt
  have hP : ∀ t, deriv g (x t) ≠ 0 := fun t =>
    deriv_ne_zero_of_injOn isOpen_ball hg.1 hg.2.1 (hxm t)
  have hF : (fun t => horoPhi Ω q (γ t)) = fun t =>
      2 / ((1 - x t ^ 2) * ‖deriv g (x t)‖) * (‖q.1 - g (x t)‖ ^ 2 + q.2 ^ 2) / (2 * q.2) := by
    funext t
    rw [hγg t]
    have hl := eq_lambda_f hg (hxm t)
    have hPn : 0 < ‖deriv g (x t)‖ := norm_pos_iff.mpr (hP t)
    have hs2 : ‖((x t : ℝ) : ℂ)‖ ^ 2 = x t ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hs2] at hl
    have h1 := hx1 t
    have hlam : poincareDensity Ω (g (x t)) = 2 / ((1 - x t ^ 2) * ‖deriv g (x t)‖) := by
      rw [← div_div, ← hl, mul_div_cancel_right₀ _ hPn.ne']
    unfold horoPhi
    rw [hlam]
  rw [hF, contDiff_iff_contDiffAt]
  intro t
  have hden : (1 - x t ^ 2) * ‖deriv g (x t)‖ ≠ 0 :=
    mul_ne_zero (hx1 t).ne' (norm_ne_zero_iff.mpr (hP t))
  refine ContDiffAt.div_const (ContDiffAt.mul (contDiffAt_const.div
    ((contDiffAt_const.sub (hxc.contDiffAt.pow 2)).mul ((hcomp hg' t).norm ℝ (hP t))) hden)
    (((contDiffAt_const.sub (hcomp hg.1 t)).norm_sq ℝ).add contDiffAt_const)) _

/-- Lemma 3.10 `lem:convexity`, (3.7) `eq:hessian`, `sec03-coarse.tex:294`: with
`ρ = e^{2u}|dw|²`, `(∇²_ρ Φ_q)_{ww} = ½ Φ_q S(f⁻¹)` and `(∇²_ρ Φ_q)_{w w̄} = B ≥ ¼ Φ_q e^{2u}`.
The Hessian is read along `ρ`-geodesics: `(Φ_q ∘ γ)''(0) = 2 Re((∇²Φ)_{ww} v²) + 2 (∇²Φ)_{w w̄} |v|²`
for `γ(0) = w`, `γ'(0) = v`. -/
theorem lem_convexity_hessian {Ω Ωs : Set ℂ} {K : ℝ} (hK : IsKQuasiPair Ω Ωs K)
    (hnc : ¬ IsLinePair Ω Ωs) {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {q : ℂ × ℝ}
    (hq : q ∈ UHS) {w : ℂ} (hw : w ∈ Ω) :
    ∃ B : ℝ, horoPhi Ω q w * poincareDensity Ω w ^ 2 / 4 ≤ B ∧
      ∀ γ : ℝ → ℂ, IsRhoGeodesic Ω γ → γ 0 = w →
        deriv (deriv (fun t => horoPhi Ω q (γ t))) 0 =
          ((horoPhi Ω q w : ℂ) * schwarzian (Function.invFunOn f unitDisc) w *
              deriv γ 0 ^ 2).re + 2 * B * ‖deriv γ 0‖ ^ 2 := by
  -- the quasi-pair hypotheses are not needed: the identity holds for every Riemann map
  have _hK := hK
  have _hnc := hnc
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hb : 0 < q.2 := hq
  have hex : ∃ a ∈ unitDisc, f a = w := by
    have := hw
    rw [← hf.2.2] at this
    exact this
  set p := Function.invFunOn f unitDisc w with hpdef
  have hp : p ∈ unitDisc := Function.invFunOn_mem hex
  have hfp : f p = w := Function.invFunOn_eq hex
  obtain ⟨hg, hg0, -⟩ := s02_disc_recenter hf hp
  set g₀ := f ∘ blaschke (-p) with hg₀def
  have hg₀' : DifferentiableOn ℂ (deriv g₀) unitDisc := hg.1.deriv isOpen_ball
  set a₁ := deriv g₀ 0 with ha₁def
  set a₂ := deriv (deriv g₀) 0 with ha₂def
  have ha₁ : a₁ ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hg.1 hg.2.1 h0
  set ψ : ℂ := -a₂ / (2 * a₁ ^ 2) with hψdef
  set A : ℂ := q.1 - w with hAdef
  set lam := poincareDensity Ω w with hlamdef
  have hlam0 : 0 ≤ lam := (s02_poincareDensity_pos ⟨f, hf⟩ hw).le
  refine ⟨horoPhi Ω q w * lam ^ 2 / 4 +
    lam / (2 * q.2) * ((‖A‖ ^ 2 + q.2 ^ 2) * ‖ψ‖ ^ 2 - 2 * (ψ * A).re + 1), ?_, ?_⟩
  · -- `(|A|² + b²)|ψ|² - 2 Re(ψ A) + 1 ≥ (|A||ψ| - 1)² ≥ 0`
    refine le_add_of_nonneg_right (mul_nonneg (by positivity) ?_)
    have h1 : (ψ * A).re ≤ ‖ψ‖ * ‖A‖ := (Complex.re_le_norm _).trans (norm_mul ψ A).le
    nlinarith [sq_nonneg (‖A‖ * ‖ψ‖ - 1), sq_nonneg (q.2 * ‖ψ‖)]
  intro γ hγ hγ0
  obtain ⟨c, hc, -, p', hp', e, he, hγe⟩ := s03_geo_eq_f hf hγ
  have he0 : e ≠ 0 := by
    intro h
    rw [h, norm_zero] at he
    exact zero_ne_one he
  -- the base point is `p`
  have hpp : p' = p := by
    have h1 := hγe 0
    rw [hγ0, mul_zero, zero_div, Real.tanh_zero, Complex.ofReal_zero, mul_zero] at h1
    have h2 : blaschke (-p') 0 = p' := by
      show (0 - -p') / (1 - conj (-p') * 0) = p'
      simp
    rw [h2] at h1
    exact hf.2.1 hp' hp (h1.symm.trans hfp.symm)
  subst hpp
  -- the rotated Riemann map `G(z) = g₀(e z)`
  have hR : IsConformalOnto (fun z => e * z) unitDisc unitDisc := isConformalOnto_rot he
  have hRm : MapsTo (fun z => e * z) unitDisc unitDisc := fun z hz =>
    hR.2.2 ▸ mem_image_of_mem _ hz
  set G : ℂ → ℂ := g₀ ∘ fun z => e * z with hGdef
  have hG : IsConformalOnto G unitDisc Ω :=
    ⟨hg.1.comp hR.1 hRm, hg.2.1.comp hR.2.1 hRm, by rw [image_comp, hR.2.2, hg.2.2]⟩
  have hG0 : G 0 = w := by
    show g₀ (e * 0) = w
    rw [mul_zero, hg0, hfp]
  have hG' : DifferentiableOn ℂ (deriv G) unitDisc := hG.1.deriv isOpen_ball
  have hG'' : DifferentiableOn ℂ (deriv (deriv G)) unitDisc := hG'.deriv isOpen_ball
  set α₁ := deriv G 0 with hα₁def
  set α₂ := deriv (deriv G) 0 with hα₂def
  set α₃ := deriv (deriv (deriv G)) 0 with hα₃def
  have hα₁ : α₁ ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hG.1 hG.2.1 h0
  -- `ψ` computed from `G`
  have hdG : ∀ z ∈ unitDisc, HasDerivAt G (deriv g₀ (e * z) * (e * 1)) z := fun z hz =>
    (hg.1.differentiableAt (isOpen_ball.mem_nhds (hRm hz))).hasDerivAt.comp z
      ((hasDerivAt_id z).const_mul e)
  have hα₁e : α₁ = a₁ * e := by
    rw [hα₁def, (hdG 0 h0).deriv, mul_zero, mul_one]
  have hα₂e : α₂ = a₂ * e * e := by
    have hev : deriv G =ᶠ[𝓝 0] fun z => deriv g₀ (e * z) * (e * 1) := by
      filter_upwards [isOpen_ball.mem_nhds h0] with z hz
      exact (hdG z hz).deriv
    rw [hα₂def, hev.deriv_eq]
    have := ((hg₀'.differentiableAt (isOpen_ball.mem_nhds (hRm h0))).hasDerivAt.comp (0 : ℂ)
      ((hasDerivAt_id (0 : ℂ)).const_mul e)).mul_const (e * 1)
    refine this.deriv.trans ?_
    show deriv (deriv g₀) (e * 0) * (e * 1) * (e * 1) = _
    rw [mul_zero, mul_one]
  have hψG : -α₂ / (2 * α₁ ^ 2) = ψ := by
    rw [hα₁e, hα₂e, hψdef]
    field_simp
  -- `S(f⁻¹)(w) α₁² = -S G(0)`
  have hψf : IsConformalOnto (Function.invFunOn f unitDisc) Ω unitDisc := hf.symm isOpen_ball
  have hGA : AnalyticAt ℂ G 0 := hG.1.analyticAt (isOpen_ball.mem_nhds h0)
  have hSinv : schwarzian (Function.invFunOn f unitDisc) w * α₁ ^ 2 =
      -((α₃ * α₁ - α₂ * α₂) / α₁ ^ 2 - 1 / 2 * (α₂ / α₁) ^ 2) := by
    have hw' : G 0 ∈ Ω := hG0 ▸ hw
    have hψA : AnalyticAt ℂ (Function.invFunOn f unitDisc) (G 0) :=
      hψf.1.analyticAt (hΩo.mem_nhds hw')
    have hψ' : deriv (Function.invFunOn f unitDisc) (G 0) ≠ 0 :=
      deriv_ne_zero_of_injOn hΩo hψf.1 hψf.2.1 hw'
    have hp1 : ‖-p‖ < 1 := by rw [norm_neg]; exact mem_ball_zero_iff.mp hp
    have hloc : Function.invFunOn f unitDisc ∘ G =ᶠ[𝓝 0]
        fun v => (e * v + p) / (conj p * e * v + 1) := by
      filter_upwards [isOpen_ball.mem_nhds h0] with v hv
      have hb' : blaschke (-p) (e * v) ∈ unitDisc :=
        mem_ball_zero_iff.mpr (blaschke_mem_unitDisc hp1 (mem_ball_zero_iff.mp (hRm hv)))
      show Function.invFunOn f unitDisc (f (blaschke (-p) (e * v))) = _
      rw [hf.2.1.leftInvOn_invFunOn hb']
      show (e * v - -p) / (1 - conj (-p) * (e * v)) = _
      rw [map_neg]
      congr 1 <;> ring
    have hdet : e * 1 - p * (conj p * e) ≠ 0 := by
      have hn : p * conj p = ((Complex.normSq p : ℝ) : ℂ) := Complex.mul_conj p
      have hlt : Complex.normSq p < 1 := by
        rw [Complex.normSq_eq_norm_sq]
        have h1 := mem_ball_zero_iff.mp hp
        nlinarith [norm_nonneg p]
      have : e * 1 - p * (conj p * e) = e * (1 - ((Complex.normSq p : ℝ) : ℂ)) := by
        rw [← hn]; ring
      rw [this]
      refine mul_ne_zero he0 ?_
      rw [sub_ne_zero, ne_comm, ← Complex.ofReal_one, Ne, Complex.ofReal_inj]
      exact hlt.ne
    have hchain := eq19_1_chain_rule hGA hα₁ hψA hψ'
    rw [schwarzian_congr (hloc.filter_mono nhdsWithin_le_nhds), schwarzian_mobius hdet,
      hG0, schwarzian_of_analyticAt hGA] at hchain
    have hH : schwarzianHol G 0 = deriv (fun z => deriv (deriv G) z / deriv G z) 0 -
        1 / 2 * (deriv (deriv G) 0 / deriv G 0) ^ 2 := rfl
    have hq' : HasDerivAt (fun z => deriv (deriv G) z / deriv G z)
        ((α₃ * α₁ - α₂ * α₂) / α₁ ^ 2) 0 :=
      (hG''.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt.div
        (hG'.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt hα₁
    rw [hH, hq'.deriv] at hchain
    linear_combination -hchain
  -- jets along the real diameter of `G`
  have hmem : ∀ s : ℝ, s ∈ Ioo (-1 : ℝ) 1 → (s : ℂ) ∈ unitDisc := fun s hs => by
    refine mem_ball_zero_iff.mpr ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]
    exact hs
  have hI : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  obtain ⟨JG1, JG2⟩ := s03_hess_hjet hG.1
  obtain ⟨JP1, JP2⟩ := s03_hess_hjet hG'
  have JN := s03_hess_jet_add_const (q.2 ^ 2) (s03_hess_jet_normSq
    (u := fun s : ℝ => q.1 - G (s : ℂ)) (u' := fun s : ℝ => -deriv G (s : ℂ))
    (JG1.mono fun s h => h.const_sub q.1) JG2.neg)
  have hP0 : 0 < ‖deriv G ((0 : ℝ) : ℂ)‖ ^ 2 := by
    rw [Complex.ofReal_zero]
    exact pow_pos (norm_pos_iff.mpr hα₁) 2
  have JK := s03_hess_jet_invsqrt (f := fun s : ℝ => ‖deriv G (s : ℂ)‖ ^ 2) (s0 := 0) hP0
    (s03_hess_jet_normSq JP1 JP2)
  have JQ : ∃ h' : ℝ → ℝ, (∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun s : ℝ => (1 - s ^ 2)⁻¹) (h' s) s) ∧
      h' 0 = 0 ∧ HasDerivAt h' 2 0 := by
    refine ⟨fun s => 2 * s / (1 - s ^ 2) ^ 2, ?_, by simp, ?_⟩
    · filter_upwards [hI] with s hs
      have h1 : 1 - s ^ 2 ≠ 0 := by
        have : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
        exact this.ne'
      refine (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_pow 2 s)).inv h1).congr_deriv ?_
      norm_num
    · have := ((hasDerivAt_id (0 : ℝ)).const_mul 2).div
        (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_pow 2 (0 : ℝ))).pow 2) (by norm_num)
      refine this.congr_deriv ?_
      norm_num
  have J := s03_hess_jet_mul (s03_hess_jet_mul (s03_hess_jet_mul
    (s03_hess_jet_const (1 / q.2) 0) JN) JQ) JK
  -- the product is `Φ_q ∘ G` near `0`
  have hΨeq : (fun s : ℝ => 1 / q.2 * (‖q.1 - G (s : ℂ)‖ ^ 2 + q.2 ^ 2) * (1 - s ^ 2)⁻¹ *
      (√(‖deriv G (s : ℂ)‖ ^ 2))⁻¹) =ᶠ[𝓝 0] fun s : ℝ => horoPhi Ω q (G (s : ℂ)) := by
    filter_upwards [hI] with s hs
    have hl := eq_lambda_f hG (hmem s hs)
    have hPn : 0 < ‖deriv G (s : ℂ)‖ :=
      norm_pos_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hG.1 hG.2.1 (hmem s hs))
    have hs2 : ‖(s : ℂ)‖ ^ 2 = s ^ 2 := by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have h1 : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
    rw [hs2] at hl
    rw [Real.sqrt_sq (norm_nonneg _)]
    have hlam : poincareDensity Ω (G s) = 2 / (1 - s ^ 2) / ‖deriv G s‖ := by
      rw [← hl]
      field_simp
    unfold horoPhi
    rw [hlam]
    field_simp
  have JΨ := s03_hess_jet_congr hΨeq J
  -- the parameter `x(t) = tanh(c t / 2)`
  set x : ℝ → ℝ := fun t => Real.tanh (c * t / 2) with hxdef
  set x' : ℝ → ℝ := fun t => c / 2 * (1 - Real.tanh (c * t / 2) ^ 2) with hx'def
  have hx : ∀ t, HasDerivAt x (x' t) t := fun t => by
    have hlin : HasDerivAt (fun t : ℝ => c * t / 2) (c * 1 / 2) t :=
      ((hasDerivAt_id t).const_mul c).div_const 2
    refine ((s03_geo_hasDerivAt_tanh (c * t / 2)).comp t hlin).congr_deriv ?_
    ring
  have hx0 : x 0 = 0 := by simp [hxdef, Real.tanh_zero]
  have hx'0 : x' 0 = c / 2 := by simp [hx'def, Real.tanh_zero]
  have hx2 : HasDerivAt x' 0 0 := by
    have := (((hx 0).pow 2).const_sub 1).const_mul (c / 2)
    refine this.congr_deriv ?_
    rw [hx0]
    ring
  have hγf : γ = (fun s : ℝ => G (s : ℂ)) ∘ x := by
    funext t
    rw [hγe t]
    rfl
  have hγd : deriv γ 0 = ((c / 2 : ℝ) : ℂ) * α₁ := by
    have h1 : HasDerivAt (fun s : ℝ => G (s : ℂ)) (deriv G ((x 0 : ℝ) : ℂ)) (x 0) := by
      rw [hx0]
      exact JG1.self_of_nhds
    rw [hγf, (h1.scomp 0 (hx 0)).deriv, hx0, Complex.ofReal_zero, Complex.real_smul, hx'0]
  have hF : (fun t => horoPhi Ω q (γ t)) = (fun s : ℝ => horoPhi Ω q (G (s : ℂ))) ∘ x := by
    rw [hγf]
    rfl
  have hcomp := s03_hess_jet_comp hx0 JΨ hx hx2
  -- the values at `0`
  have hρ : ‖α₁‖ ≠ 0 := norm_ne_zero_iff.mpr hα₁
  have hΦ : horoPhi Ω q w = (A.re ^ 2 + A.im ^ 2 + q.2 ^ 2) / (q.2 * ‖α₁‖) := by
    have h := hΨeq.self_of_nhds
    simp only [Complex.ofReal_zero, hG0, ← hα₁def] at h
    rw [← h, ← hAdef, Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, Complex.normSq_apply]
    field_simp
    ring
  have hlamw : lam = 2 / ‖α₁‖ := by
    have h := eq_lambda_f hG h0
    rw [hG0, norm_zero] at h
    rw [hlamdef, eq_div_iff hρ, h]
    norm_num
  have key := s03_hess_alg α₁ α₂ α₃ A hb.ne' hρ hα₁
  have hm : ‖α₁‖ ^ 2 = α₁.re ^ 2 + α₁.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hSre : ((horoPhi Ω q w : ℂ) * schwarzian (Function.invFunOn f unitDisc) w *
      (((c / 2 : ℝ) : ℂ) * α₁) ^ 2).re = (c / 2) ^ 2 * ((horoPhi Ω q w : ℂ) *
        -((α₃ * α₁ - α₂ * α₂) / α₁ ^ 2 - 1 / 2 * (α₂ / α₁) ^ 2)).re := by
    rw [← hSinv, ← Complex.re_ofReal_mul]
    congr 1
    push_cast
    ring
  have hvn : ‖((c / 2 : ℝ) : ℂ) * α₁‖ ^ 2 = (c / 2) ^ 2 * ‖α₁‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hF, hcomp, hγd, hSre, hvn, hΦ, hlamw, ← hψG, div_pow (2 : ℝ) ‖α₁‖ 2]
  simp only [Complex.ofReal_zero, hG0, ← hAdef, ← hα₃def, ← hα₂def, ← hα₁def]
  simp only [Real.sqrt_sq (norm_nonneg α₁)]
  rw [hm]
  simp only [Complex.sq_norm, Complex.normSq_apply, hx'0]
  simp only at key
  linear_combination (c / 2) ^ 2 * key


/-- Lemma 3.10 `lem:convexity`, `sec03-coarse.tex:301`:
`∇²_ρ Φ_q(v, v) ≥ Φ_q (½ - s) |v|²_ρ`. -/
theorem lem_convexity_lower {Ω Ωs : Set ℂ} {K : ℝ} (hK : IsKQuasiPair Ω Ωs K)
    (hnc : ¬ IsLinePair Ω Ωs) {q : ℂ × ℝ} (hq : q ∈ UHS) {w : ℂ} (hw : w ∈ Ω)
    {γ : ℝ → ℂ} (hγ : IsRhoGeodesic Ω γ) (hγ0 : γ 0 = w) :
    horoPhi Ω q w * (1 / 2 - schwarzNorm Ω w) * (poincareDensity Ω w ^ 2 * ‖deriv γ 0‖ ^ 2) ≤
      deriv (deriv (fun t => horoPhi Ω q (γ t))) 0 := by
  obtain ⟨-, -, -, hR⟩ := s03_b0_basic hK
  obtain ⟨f, hf⟩ := hR
  obtain ⟨B, hB, hH⟩ := lem_convexity_hessian hK hnc hf hq hw
  rw [hH γ hγ hγ0]
  have hb : 0 < q.2 := hq
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hw
  have hΦ : 0 ≤ horoPhi Ω q w := by
    unfold horoPhi
    positivity
  have hSn : ‖schwarzian (Function.invFunOn f unitDisc) w‖ =
      schwarzNorm Ω w * poincareDensity Ω w ^ 2 := by
    rw [eq_def_s hf hw]
    field_simp
  have hre : -(horoPhi Ω q w * ‖schwarzian (Function.invFunOn f unitDisc) w‖ * ‖deriv γ 0‖ ^ 2) ≤
      ((horoPhi Ω q w : ℂ) * schwarzian (Function.invFunOn f unitDisc) w * deriv γ 0 ^ 2).re := by
    have h1 := Complex.abs_re_le_norm
      ((horoPhi Ω q w : ℂ) * schwarzian (Function.invFunOn f unitDisc) w * deriv γ 0 ^ 2)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΦ,
      norm_pow] at h1
    linarith [neg_abs_le ((horoPhi Ω q w : ℂ) * schwarzian (Function.invFunOn f unitDisc) w *
      deriv γ 0 ^ 2).re]
  rw [hSn] at hre
  have hB' := mul_le_mul_of_nonneg_right hB (sq_nonneg ‖deriv γ 0‖)
  nlinarith

/-- Lemma 3.10 `lem:convexity`, `sec03-coarse.tex:302`: `Φ_q` is strictly convex (along
`ρ`-geodesics) on every geodesically convex set on which `s < 1/2`. -/
theorem lem_convexity_strict {Ω Ωs : Set ℂ} {K : ℝ} (hK : IsKQuasiPair Ω Ωs K)
    (hnc : ¬ IsLinePair Ω Ωs) {q : ℂ × ℝ} (hq : q ∈ UHS) {S : Set ℂ} (hSΩ : S ⊆ Ω)
    (hconv : ∀ γ : ℝ → ℂ, IsRhoGeodesic Ω γ → ∀ a b : ℝ, a ≤ b → γ a ∈ S → γ b ∈ S →
      γ '' Icc a b ⊆ S)
    (hs : ∀ w ∈ S, schwarzNorm Ω w < 1 / 2) {γ : ℝ → ℂ} (hγ : IsRhoGeodesic Ω γ) {a b : ℝ}
    (hγS : γ '' Icc a b ⊆ S) :
    StrictConvexOn ℝ (Icc a b) (fun t => horoPhi Ω q (γ t)) := by
  -- geodesic convexity of `S` is not needed: `γ([a, b]) ⊆ S` is assumed directly
  have _hconv := hconv
  obtain ⟨-, -, -, hΩ⟩ := s03_b0_basic hK
  have hb : 0 < q.2 := hq
  refine strictConvexOn_of_deriv2_pos (convex_Icc a b)
    (s03_hess_phi_contDiff (n := 2) hΩ hγ q).continuous.continuousOn ?_
  intro t0 ht0
  have hwS : γ t0 ∈ S := hγS (mem_image_of_mem γ (interior_subset ht0))
  have hwΩ := hSΩ hwS
  set γ' : ℝ → ℂ := fun t => γ (t + t0) with hγ'def
  have hγ' : IsRhoGeodesic Ω γ' := by
    obtain ⟨hm, c, hc, hd⟩ := hγ
    refine ⟨fun t => hm _, c, hc, fun t t' => ?_⟩
    show poincareDist Ω (γ (t + t0)) (γ (t' + t0)) = c * |t - t'|
    rw [hd]
    congr 2
    ring
  have hγ'0 : γ' 0 = γ t0 := by
    show γ (0 + t0) = γ t0
    rw [zero_add]
  have hL := lem_convexity_lower hK hnc hq hwΩ hγ' hγ'0
  set F : ℝ → ℝ := fun t => horoPhi Ω q (γ t) with hFdef
  have h1 : deriv (fun t => horoPhi Ω q (γ' t)) = fun t => deriv F (t + t0) := by
    funext t
    exact deriv_comp_add_const F t0 t
  have e1 : deriv (deriv (fun t => horoPhi Ω q (γ' t))) 0 = deriv (deriv F) t0 := by
    rw [h1]
    rw [deriv_comp_add_const (deriv F) t0 0, zero_add]
  show 0 < deriv (deriv F) t0
  rw [← e1]
  refine lt_of_lt_of_le ?_ hL
  have hl := s02_poincareDensity_pos hΩ hwΩ
  have hΦ : 0 < horoPhi Ω q (γ t0) := by
    unfold horoPhi
    have : 0 < ‖q.1 - γ t0‖ ^ 2 + q.2 ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hb 2)
    positivity
  have hs' : 0 < 1 / 2 - schwarzNorm Ω (γ t0) := by linarith [hs _ hwS]
  have hvn : 0 < ‖deriv γ' 0‖ := norm_pos_iff.mpr (s03_hess_deriv_ne hΩ hγ' 0)
  exact mul_pos (mul_pos hΦ hs') (mul_pos (pow_pos hl 2) (pow_pos hvn 2))

/-- Busemann step of Proposition 3.11: `Φ_{X(w)}(w') ≤ e^{|τ|} Φ_{E(w,τ)}(w')`. -/
theorem s03_ul_busemann {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w w' : ℂ}
    (hw : w ∈ Ω) (hw' : w' ∈ Ω) (τ : ℝ) :
    horoPhi Ω (epstein Ω w) w' ≤ Real.exp |τ| * horoPhi Ω (normalGeod Ω w τ) w' := by
  obtain ⟨hU, hd, h0⟩ := lem_normal_b hΩ hw
  have hl := s02_poincareDensity_pos hΩ hw'
  have hpos : ∀ q ∈ UHS, 0 < horoPhi Ω q w' := fun q hq => by
    have hq2 : 0 < q.2 := hq
    unfold horoPhi
    positivity
  have hb := lem_busemann hΩ hw' (hU 0) (hU τ)
  rw [hd, h0, zero_sub, abs_neg] at hb
  have h1 := (abs_le.mp hb).2
  have hA := hpos _ (h0 ▸ hU 0)
  have hB := hpos _ (hU τ)
  calc horoPhi Ω (epstein Ω w) w' = Real.exp (Real.log (horoPhi Ω (epstein Ω w) w')) :=
        (Real.exp_log hA).symm
    _ ≤ Real.exp (|τ| + Real.log (horoPhi Ω (normalGeod Ω w τ) w')) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_add, Real.exp_log hB]

/-- `d_𝔻(tanh(a/2), tanh(b/2)) = |a - b|`: the real diameter is a unit-speed geodesic. -/
theorem s03_ul_diskDist_tanh (a b : ℝ) :
    diskDist (Real.tanh (a / 2) : ℂ) (Real.tanh (b / 2) : ℂ) = |a - b| := by
  have hu1 := (sq_lt_one_iff_abs_lt_one _).mpr (Real.abs_tanh_lt_one (a / 2))
  have hv1 := (sq_lt_one_iff_abs_lt_one _).mpr (Real.abs_tanh_lt_one (b / 2))
  obtain ⟨ca, sa⟩ := s03_geo_cosh_tanh a
  obtain ⟨cb, sb⟩ := s03_geo_cosh_tanh b
  set u := Real.tanh (a / 2)
  set v := Real.tanh (b / 2)
  have hu2 : 1 - u ^ 2 ≠ 0 := by linarith
  have hv2 : 1 - v ^ 2 ≠ 0 := by linarith
  have hc : diskCoshDist (u : ℂ) (v : ℂ) = Real.cosh (a - b) := by
    rw [Real.cosh_sub, ca, sa, cb, sb]
    unfold diskCoshDist
    rw [← ofReal_sub, Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, sq_abs]
    field_simp
    ring
  unfold diskDist
  rw [hc, ← Real.cosh_abs, Real.arcosh_cosh (abs_nonneg _)]

/-- A unit-speed `ρ`-geodesic from `w` through `w'`: `γ(t) = g(tanh(t/2))` for a Riemann map `g`
with `g 0 = w`; it reaches `w'` at time `d_ρ(w, w')`, and `γ' ≠ 0`. -/
theorem s03_ul_geo {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) {w w' : ℂ} (hw : w ∈ Ω)
    (hw' : w' ∈ Ω) :
    ∃ γ : ℝ → ℂ, IsRhoGeodesic Ω γ ∧ γ 0 = w ∧ γ (poincareDist Ω w w') = w' ∧
      (∀ t, poincareDist Ω w (γ t) = |t|) ∧ ∀ t, deriv γ t ≠ 0 := by
  obtain ⟨f, hf, hf0⟩ := s02_riemannMap_at hΓ hw
  obtain ⟨z, hz, rfl⟩ : w' ∈ f '' unitDisc := by rw [hf.2.2]; exact hw'
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  obtain ⟨e, he, hez⟩ : ∃ e : ℂ, ‖e‖ = 1 ∧ z = e * (‖z‖ : ℂ) := by
    by_cases h0 : z = 0
    · exact ⟨1, norm_one, by rw [h0, norm_zero, ofReal_zero, mul_zero]⟩
    · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr h0
      refine ⟨z / (‖z‖ : ℂ), ?_, ?_⟩
      · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hn]
      · rw [div_mul_cancel₀ _ (ofReal_ne_zero.mpr hn)]
  have hR : IsConformalOnto (fun x => e * x) unitDisc unitDisc := isConformalOnto_rot he
  have hRm : MapsTo (fun x => e * x) unitDisc unitDisc := fun x hx =>
    hR.2.2 ▸ mem_image_of_mem _ hx
  set g : ℂ → ℂ := f ∘ (fun x => e * x) with hgdef
  have hg : IsConformalOnto g unitDisc Ω :=
    ⟨hf.1.comp hR.1 hRm, hf.2.1.comp hR.2.1 hRm, by rw [hgdef, image_comp, hR.2.2, hf.2.2]⟩
  have ht : ∀ s : ℝ, ((Real.tanh s : ℝ) : ℂ) ∈ unitDisc := fun s => by
    refine mem_ball_zero_iff.mpr ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_tanh_lt_one _
  set γ : ℝ → ℂ := fun t => g (Real.tanh (1 * t / 2)) with hγdef
  have hgeo : ∀ t t', poincareDist Ω (γ t) (γ t') = 1 * |t - t'| := fun t t' => by
    rw [hγdef]
    dsimp only
    rw [subsec_poincare_dist hg (ht _) (ht _), one_mul, one_mul, one_mul]
    exact s03_ul_diskDist_tanh t t'
  have hγ0 : γ 0 = w := by
    rw [hγdef]
    dsimp only
    rw [mul_zero, zero_div, Real.tanh_zero, ofReal_zero]
    show f (e * 0) = w
    rw [mul_zero, hf0]
  have hd : ∀ t, poincareDist Ω w (γ t) = |t| := fun t => by
    rw [← hγ0, hgeo, one_mul, zero_sub, abs_neg]
  set s := 2 * Real.artanh ‖z‖ with hs
  have hs0 : 0 ≤ s := by have := Real.artanh_nonneg (norm_nonneg z); linarith
  have hγs : γ s = f z := by
    rw [hγdef]
    dsimp only
    rw [show 1 * s / 2 = Real.artanh ‖z‖ by rw [hs]; ring,
      Real.tanh_artanh ⟨by linarith [norm_nonneg z], hz1⟩]
    show f (e * (‖z‖ : ℂ)) = f z
    rw [← hez]
  have hds : poincareDist Ω w (f z) = s := by rw [← hγs, hd, abs_of_nonneg hs0]
  refine ⟨γ, ⟨fun t => hg.2.2 ▸ mem_image_of_mem g (ht _), 1, one_pos, hgeo⟩, hγ0,
    by rw [hds, hγs], hd, fun t => ?_⟩
  rw [(s03_geo_hasDerivAt hg 1 t).deriv]
  refine mul_ne_zero (deriv_ne_zero_of_injOn isOpen_ball hg.1 hg.2.1 (ht _)) ?_
  rw [ofReal_ne_zero]
  have := (sq_lt_one_iff_abs_lt_one _).mpr (Real.abs_tanh_lt_one (1 * t / 2))
  have h2 : (0 : ℝ) < 1 / 2 * (1 - Real.tanh (1 * t / 2) ^ 2) := by nlinarith
  exact h2.ne'

/-- If `h ∈ C²`, `h'(0) = 0` and `h'' > 0` on `(0, T)`, then `h(0) < h(T)`. -/
theorem s03_ul_strict {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h) (h0 : deriv h 0 = 0) {T : ℝ}
    (hT : 0 < T) (h2 : ∀ t ∈ Ioo 0 T, 0 < deriv (deriv h) t) : h 0 < h T := by
  have hc1 : Continuous (deriv h) := hh.continuous_deriv (by norm_num)
  have hm1 : StrictMonoOn (deriv h) (Icc 0 T) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 T) hc1.continuousOn (by rw [interior_Icc]; exact h2)
  have hpos : ∀ t ∈ interior (Icc 0 T), 0 < deriv h t := by
    rw [interior_Icc]
    intro t ht
    rw [← h0]
    exact hm1 (left_mem_Icc.mpr hT.le) (Ioo_subset_Icc_self ht) ht.1
  exact strictMonoOn_of_deriv_pos (convex_Icc 0 T) hh.continuous.continuousOn hpos
    (left_mem_Icc.mpr hT.le) (right_mem_Icc.mpr hT.le) hT

/-- Near half of Proposition 3.11: if `s < 1/2` on `B_ρ(w, R)`, then for `q = E(w, τ)` every
`w' ≠ w` with `d_ρ(w, w') ≤ R` has `Φ_q(w) < Φ_q(w')` (`w` is critical by Lemma 2.4 and `Φ_q` is
strictly convex along the geodesic from `w` to `w'` by Lemma 3.10). -/
theorem s03_ul_near {Ω Ωs : Set ℂ} {K : ℝ} (hK : IsKQuasiPair Ω Ωs K) (hnc : ¬ IsLinePair Ω Ωs)
    {w : ℂ} (hw : w ∈ Ω) {R : ℝ}
    (hs : ∀ w' ∈ Ω, poincareDist Ω w w' ≤ R → schwarzNorm Ω w' < 1 / 2) (τ : ℝ) {w' : ℂ}
    (hw' : w' ∈ Ω) (hne : w' ≠ w) (hR : poincareDist Ω w w' ≤ R) :
    horoPhi Ω (normalGeod Ω w τ) w < horoPhi Ω (normalGeod Ω w τ) w' := by
  have hΓ := s03_b0_jordanPair hK
  have hΩ := s02_jordanPair_riemannMap hΓ
  obtain ⟨γ, hγ, hγ0, hγT, hγd, hγ'⟩ := s03_ul_geo hΓ hw hw'
  set q := normalGeod Ω w τ with hqdef
  have hq : q ∈ UHS := (lem_normal_b hΩ hw).1 τ
  set T := poincareDist Ω w w' with hTdef
  have hT0 : 0 ≤ T := by
    have := hγd T
    rw [hγT] at this
    linarith [abs_nonneg T]
  have hT : 0 < T := lt_of_le_of_ne hT0 fun h => hne (by rw [← hγT, ← h, hγ0])
  -- `w` is a critical point of `Φ_q` (Lemma 2.4)
  have hcrit : HasFDerivAt (fun x => horoPhi Ω q x) (0 : ℂ →L[ℝ] ℝ) w := by
    have hmem : q ∈ range (normalGeod Ω w) := ⟨τ, rfl⟩
    rw [← lem_normal_a hΩ hw] at hmem
    exact hmem.2
  have hγd0 : HasDerivAt γ (deriv γ 0) 0 :=
    ((s03_geo_contDiff hΩ hγ (n := 1)).differentiable one_ne_zero 0).hasDerivAt
  rw [← hγ0] at hcrit
  have h0 : deriv (fun t => horoPhi Ω q (γ t)) 0 = 0 := by
    have := (hcrit.comp_hasDerivAt 0 hγd0).deriv
    simpa [Function.comp_def] using this
  -- `(Φ_q ∘ γ)'' > 0` on `(0, T)` (Lemma 3.10 at the shifted geodesic `s ↦ γ(s + t)`)
  have h2 : ∀ t ∈ Ioo 0 T, 0 < deriv (deriv (fun t => horoPhi Ω q (γ t))) t := by
    intro t ht
    obtain ⟨hmem, c, hc, hdc⟩ := hγ
    have hγt : IsRhoGeodesic Ω (fun s => γ (s + t)) :=
      ⟨fun s => hmem _, c, hc, fun s s' => by rw [hdc, add_sub_add_right_eq_sub]⟩
    have hL := lem_convexity_lower hK hnc hq (hmem t) hγt (by simp only [zero_add])
    beta_reduce at hL
    have e1 : deriv (fun s => horoPhi Ω q (γ (s + t))) =
        fun s => deriv (fun t => horoPhi Ω q (γ t)) (s + t) :=
      funext fun s => deriv_comp_add_const (f := fun t => horoPhi Ω q (γ t)) ..
    rw [e1, deriv_comp_add_const (f := deriv (fun t => horoPhi Ω q (γ t))),
      deriv_comp_add_const (f := γ), zero_add] at hL
    have hl := s02_poincareDensity_pos hΩ (hmem t)
    have hq2 : 0 < q.2 := hq
    have hΦ : 0 < horoPhi Ω q (γ t) := by unfold horoPhi; positivity
    have hst : 0 < 1 / 2 - schwarzNorm Ω (γ t) := by
      have := hs (γ t) (hmem t) (by rw [hγd t, abs_of_pos ht.1]; exact ht.2.le.trans hR)
      linarith
    have hv : 0 < ‖deriv γ t‖ := norm_pos_iff.mpr (hγ' t)
    exact lt_of_lt_of_le (by positivity) hL
  have hmain := s03_ul_strict (s03_hess_phi_contDiff hΩ hγ q (n := 2)) h0 hT h2
  simp only [hγ0, hγT] at hmain
  exact hmain

/-- Proposition 3.11, (3.8) first clause: `w` is the unique global minimizer of `Φ_{E(w,τ)}`,
`0 ≤ τ ≤ 1`, when `s < 1/2` on `B_ρ(w, 3C + 2)` (`C` from Lemma 3.9). -/
theorem s03_ul_min {Ω Ωs : Set ℂ} {K C : ℝ} (hK : IsKQuasiPair Ω Ωs K) (hnc : ¬ IsLinePair Ω Ωs)
    (hC : ∀ w ∈ Ω, ∀ w' ∈ Ω, ∀ T : ℝ, 1 ≤ T → horoPhi Ω (epstein Ω w) w' ≤ T →
      poincareDist Ω w w' ≤ C * (1 + Real.log T))
    {w : ℂ} (hw : w ∈ Ω)
    (hs : ∀ w' ∈ Ω, poincareDist Ω w w' ≤ 3 * C + 2 → schwarzNorm Ω w' < 1 / 2)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) {w' : ℂ} (hw' : w' ∈ Ω) (hne : w' ≠ w) :
    horoPhi Ω (normalGeod Ω w τ) w < horoPhi Ω (normalGeod Ω w τ) w' := by
  by_cases hd : poincareDist Ω w w' ≤ 3 * C + 2
  · exact s03_ul_near hK hnc hw hs τ hw' hne hd
  · by_contra hle
    rw [not_lt] at hle
    have hΩ := s02_jordanPair_riemannMap (s03_b0_jordanPair hK)
    rw [s02_horoPhi_normalGeod Ω w (s02_poincareDensity_pos hΩ hw)] at hle
    have hX := s03_ul_busemann hΩ hw hw' τ
    rw [abs_of_nonneg hτ.1] at hX
    have hX2 : horoPhi Ω (epstein Ω w) w' ≤ Real.exp 2 :=
      calc horoPhi Ω (epstein Ω w) w' ≤ Real.exp τ * Real.exp τ :=
            hX.trans (mul_le_mul_of_nonneg_left hle (Real.exp_pos τ).le)
        _ = Real.exp (τ + τ) := (Real.exp_add τ τ).symm
        _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith [hτ.2])
    have := hC w hw w' hw' (Real.exp 2) (Real.one_le_exp (by norm_num)) hX2
    rw [Real.log_exp] at this
    exact hd (by linarith)

/-- `τ ↦ E(w, τ)` is continuous. -/
theorem s03_ul_normalGeod_cont {Ω : Set ℂ} {w : ℂ} (hl : 0 < poincareDensity Ω w) :
    Continuous (normalGeod Ω w) := by
  have hD : ∀ τ : ℝ,
      0 < ‖logDensityDz Ω w‖ ^ 2 + (poincareDensity Ω w * Real.exp (-τ) / 2) ^ 2 :=
    fun τ => by positivity
  unfold normalGeod
  refine Continuous.prodMk ?_ ?_
  · exact continuous_const.add (continuous_const.div (by fun_prop)
      fun τ => ofReal_ne_zero.mpr (hD τ).ne')
  · exact Continuous.div (by fun_prop) (by fun_prop) fun τ => (hD τ).ne'

/-- Proposition 3.11 `prop:unique-label`, (3.8) `eq:unique-label`, `sec03-coarse.tex:326`: there is
`R₀ = R₀(K)` such that if `s < 1/2` on `B_ρ(w, R₀ + 2)`, then for `0 ≤ τ ≤ 1` the point `w` is the
unique global minimizer of `Φ_{E(w,τ)}`; every label satisfies `w(E(w,τ)) = w` and
`d(E(w,τ), U) = τ` for `0 < τ ≤ 1`; `X(w) ∈ ∂U`; and the normal segments
`{E(w,τ) : 0 < τ ≤ 1}` issued from such points are pairwise disjoint. -/
theorem prop_unique_label (K : ℝ) :
    ∃ R₀ : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      (∀ w ∈ Ω, (∀ w' ∈ Ω, poincareDist Ω w w' ≤ R₀ + 2 → schwarzNorm Ω w' < 1 / 2) →
        (∀ τ ∈ Icc (0 : ℝ) 1, ∀ w' ∈ Ω, w' ≠ w →
          horoPhi Ω (normalGeod Ω w τ) w < horoPhi Ω (normalGeod Ω w τ) w') ∧
        (∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab → ∀ τ ∈ Ioc (0 : ℝ) 1,
          lab (normalGeod Ω w τ) = w ∧ hdistSet (normalGeod Ω w τ) (horoUnion Ω) = τ) ∧
        epstein Ω w ∈ frontier (horoUnion Ω)) ∧
      ∀ w₁ ∈ Ω, ∀ w₂ ∈ Ω,
        (∀ w' ∈ Ω, poincareDist Ω w₁ w' ≤ R₀ + 2 → schwarzNorm Ω w' < 1 / 2) →
        (∀ w' ∈ Ω, poincareDist Ω w₂ w' ≤ R₀ + 2 → schwarzNorm Ω w' < 1 / 2) → w₁ ≠ w₂ →
        ∀ τ₁ ∈ Ioc (0 : ℝ) 1, ∀ τ₂ ∈ Ioc (0 : ℝ) 1,
          normalGeod Ω w₁ τ₁ ≠ normalGeod Ω w₂ τ₂ := by
  obtain ⟨C, hC⟩ := lem_competing K
  refine ⟨3 * C, fun Ω Ωs hK hnc => ?_⟩
  have hΓ := s03_b0_jordanPair hK
  have hΩ := s02_jordanPair_riemannMap hΓ
  have hmin := fun {w : ℂ} (hw : w ∈ Ω) hs {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) {w' : ℂ}
    (hw' : w' ∈ Ω) (hne : w' ≠ w) => s03_ul_min hK hnc (hC Ω Ωs hK hnc) hw hs hτ hw' hne
  -- for `0 < τ ≤ 1`, `E(w, τ) ∉ U` and `w` is the only minimizer of `Φ_{E(w,τ)}`
  have hout : ∀ w ∈ Ω, (∀ w' ∈ Ω, poincareDist Ω w w' ≤ 3 * C + 2 → schwarzNorm Ω w' < 1 / 2) →
      ∀ τ ∈ Ioc (0 : ℝ) 1, normalGeod Ω w τ ∉ horoUnion Ω ∧
        ∀ w₀ ∈ Ω, (∀ w' ∈ Ω, horoPhi Ω (normalGeod Ω w τ) w₀ ≤ horoPhi Ω (normalGeod Ω w τ) w') →
          w₀ = w := by
    intro w hw hs τ hτ
    have hτ' : τ ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hτ
    have hl := s02_poincareDensity_pos hΩ hw
    have huniq : ∀ w₀ ∈ Ω, (∀ w' ∈ Ω, horoPhi Ω (normalGeod Ω w τ) w₀ ≤
        horoPhi Ω (normalGeod Ω w τ) w') → w₀ = w := fun w₀ hw₀ h0 => by
      by_contra hne
      exact absurd (h0 w hw) (not_le.mpr (hmin hw hs hτ' hw₀ hne))
    refine ⟨fun hU => ?_, huniq⟩
    rw [horoUnion, mem_iUnion₂] at hU
    obtain ⟨w'', hw'', hB⟩ := hU
    have h1 : horoPhi Ω (normalGeod Ω w τ) w ≤ horoPhi Ω (normalGeod Ω w τ) w'' := by
      by_cases he : w'' = w
      · rw [he]
      · exact (hmin hw hs hτ' hw'' he).le
    rw [s02_horoPhi_normalGeod Ω w hl] at h1
    linarith [hB.2, Real.one_lt_exp_iff.mpr hτ.1]
  refine ⟨fun w hw hs => ⟨fun τ hτ w' hw' hne => hmin hw hs hτ hw' hne,
    fun lab hlab τ hτ => ?_, ?_⟩, ?_⟩
  · obtain ⟨hqU, huniq⟩ := hout w hw hs τ hτ
    have hq : normalGeod Ω w τ ∈ UHS := (lem_normal_b hΩ hw).1 τ
    obtain ⟨hlabΩ, hlabm⟩ := hlab.2 _ ⟨hq, hqU⟩
    obtain ⟨w₀, hw₀, hmin₀, heq⟩ := eq_dist_U hΓ hq hqU
    refine ⟨huniq _ hlabΩ hlabm, ?_⟩
    rw [heq, huniq _ hw₀ hmin₀, eq_normal_flow hΩ hw]
  · -- `X(w) ∈ B_w ⊆ U`, and `E(w, τ) ∉ U` for small `τ > 0` with `E(w, τ) → X(w)`
    have hl := s02_poincareDensity_pos hΩ hw
    have h0 := s02_normalGeod_zero Ω w hl
    refine ⟨subset_closure ?_, fun hint => ?_⟩
    · rw [horoUnion, mem_iUnion₂]
      refine ⟨w, hw, h0 ▸ (lem_normal_b hΩ hw).1 0, ?_⟩
      rw [← h0, s02_horoPhi_normalGeod Ω w hl, Real.exp_zero]
    · have hmem : interior (horoUnion Ω) ∈ 𝓝 (normalGeod Ω w 0) := by
        rw [h0]
        exact isOpen_interior.mem_nhds hint
      have hev := ((s03_ul_normalGeod_cont hl).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).eventually hmem
      obtain ⟨τ, hτU, hτ⟩ := (hev.and (Ioc_mem_nhdsGT one_pos)).exists
      exact (hout w hw hs τ hτ).1 (interior_subset hτU)
  · intro w₁ hw₁ w₂ hw₂ hs₁ hs₂ hne τ₁ hτ₁ τ₂ hτ₂ heq
    have a := hmin hw₁ hs₁ (Ioc_subset_Icc_self hτ₁) hw₂ (Ne.symm hne)
    have b := hmin hw₂ hs₂ (Ioc_subset_Icc_self hτ₂) hw₁ hne
    rw [heq] at a
    linarith

/-! ## §3.7 A scale-invariant version for bounded curves -/

/-- Bounded-corkscrew helper: for a bounded quasicircle `F(∂𝔻)`, `Γ ∩ ℂ = curveOf Ω Ωs = F(∂𝔻)`. -/
theorem s03_cb_curve {Ω Ωs : Set ℂ} {F : ℂ → ℂ} (hi : Function.Injective F)
    (hs : F '' univ = univ) (hD : F '' unitDisc = Ω) (hE : F '' unitDiscExterior = Ωs) :
    curveOf Ω Ωs = F '' {z : ℂ | ‖z‖ = 1} := by
  ext x
  obtain ⟨z, -, rfl⟩ : x ∈ F '' univ := by rw [hs]; exact mem_univ x
  have hΩ : F z ∈ Ω ↔ ‖z‖ < 1 := by
    rw [← hD, hi.mem_set_image]; exact mem_ball_zero_iff
  have hΩs : F z ∈ Ωs ↔ 1 < ‖z‖ := by
    rw [← hE, hi.mem_set_image]; rfl
  rw [hi.mem_set_image]
  show F z ∉ Ω ∪ Ωs ↔ ‖z‖ = 1
  rw [mem_union, hΩ, hΩs]
  constructor
  · intro h
    rcases lt_trichotomy ‖z‖ 1 with h1 | h1 | h1
    · exact absurd (Or.inl h1) h
    · exact h1
    · exact absurd (Or.inr h1) h
  · intro h1 h
    rcases h with h | h <;> linarith

/-- Bounded-corkscrew helper: for `a ∈ ∂𝔻` and `0 < r ≤ diam(F(∂𝔻))/2` there is `b ∈ ∂𝔻` with
`|F(b) - F(a)| = r` (intermediate values along the circle). -/
theorem s03_cb_far {F : ℂ → ℂ} (hc : Continuous F) {a : ℂ} (ha : ‖a‖ = 1) {r : ℝ} (hr : 0 < r)
    (hrd : r ≤ diam (F '' {z : ℂ | ‖z‖ = 1}) / 2) :
    ∃ b : ℂ, ‖b‖ = 1 ∧ ‖F b - F a‖ = r := by
  set S : Set ℂ := {z : ℂ | ‖z‖ = 1} with hSdef
  have hS : S = sphere (0 : ℂ) 1 := by ext z; simp [hSdef]
  have hSc : IsCompact S := by rw [hS]; exact isCompact_sphere 0 1
  have haS : a ∈ S := ha
  set φ : ℂ → ℝ := fun z => ‖F z - F a‖ with hφdef
  have hφc : Continuous φ := (hc.sub continuous_const).norm
  obtain ⟨z₀, hz₀, hmax⟩ := hSc.exists_isMaxOn ⟨a, haS⟩ hφc.continuousOn
  -- `diam(F(S)) ≤ 2 φ(z₀)`
  have hdiam : diam (F '' S) ≤ 2 * φ z₀ := by
    have h0 : 0 ≤ φ z₀ := norm_nonneg _
    refine diam_le_of_forall_dist_le (by linarith) ?_
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    have h1 : φ y ≤ φ z₀ := hmax hy
    have h2 : φ y' ≤ φ z₀ := hmax hy'
    rw [dist_eq_norm]
    calc ‖F y - F y'‖ ≤ ‖F y - F a‖ + ‖F a - F y'‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * φ z₀ := by rw [norm_sub_rev (F a)]; simp only [hφdef] at h1 h2; linarith
  have hrM : r ≤ φ z₀ := by linarith
  -- intermediate values along `t ↦ exp(t i)`
  set e : ℝ → ℂ := fun t => Complex.exp (t * I) with hedef
  have he : ∀ z : ℂ, ‖z‖ = 1 → e (Complex.arg z) = z := fun z hz => by
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hz, Complex.ofReal_one, one_mul] at this
    exact this
  have hecont : Continuous (fun t => φ (e t)) := hφc.comp (by fun_prop)
  have hmem : r ∈ uIcc (φ (e (Complex.arg a))) (φ (e (Complex.arg z₀))) := by
    rw [he a ha, he z₀ hz₀]
    have : φ a = 0 := by simp [hφdef]
    rw [this]
    exact mem_uIcc.2 (Or.inl ⟨hr.le, hrM⟩)
  obtain ⟨t, -, ht⟩ := intermediate_value_uIcc hecont.continuousOn hmem
  refine ⟨e t, ?_, ht⟩
  simp only [hedef]
  exact Complex.norm_exp_ofReal_mul_I t

/-- Bounded-corkscrew helper (three-point step): with `C ≥ 1` the three-point constant, `a, b ∈ ∂𝔻`,
`t = |b - a|`, and `a'` with `|a' - a| = t/2 ≤ |a' - ζ|` for all `ζ ∈ ∂𝔻`, the point `y = F(a')`
satisfies `r/(C 2^K) ≤ |y - F a| ≤ C r` and `dist(y, F(∂𝔻)) ≥ r/(C² 2^K)`, `r = |F b - F a|`. -/
theorem s03_cb_pt {K C : ℝ} (hK : 1 ≤ K) (hC : 1 ≤ C) {F : ℂ → ℂ}
    (htp : ∀ a b c : ℂ, a ≠ c →
      ‖F a - F b‖ / ‖F a - F c‖ ≤ C * max ((‖a - b‖ / ‖a - c‖) ^ (1 / K)) ((‖a - b‖ / ‖a - c‖) ^ K))
    (hi : Function.Injective F) {a b a' : ℂ} (hab : a ≠ b)
    (ha' : ‖a' - a‖ = ‖b - a‖ / 2) (hζ : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖b - a‖ / 2 ≤ ‖a' - ζ‖) :
    ‖F b - F a‖ / (C * (2 : ℝ) ^ K) ≤ ‖F a' - F a‖ ∧ ‖F a' - F a‖ ≤ C * ‖F b - F a‖ ∧
      ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖F b - F a‖ / (C ^ 2 * (2 : ℝ) ^ K) ≤ ‖F a' - F ζ‖ := by
  have hK0 : 0 < K := by linarith
  have hC0 : 0 < C := by linarith
  set t := ‖b - a‖ with htdef
  have ht : 0 < t := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hab))
  have ha'a : a' ≠ a := fun h => by rw [h, sub_self, norm_zero] at ha'; linarith
  have hFb : 0 < ‖F b - F a‖ := norm_pos_iff.2 (sub_ne_zero.2 (fun h => hab (hi h).symm))
  have hFa' : 0 < ‖F a' - F a‖ := norm_pos_iff.2 (sub_ne_zero.2 (fun h => ha'a (hi h)))
  have h2K : 1 ≤ (2 : ℝ) ^ K := Real.one_le_rpow (by norm_num) hK0.le
  -- `max(s^{1/K}, s^K) ≤ 1` for `0 ≤ s ≤ 1` and `≤ 2^K` for `s = 2`
  have hsmall : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → max (s ^ (1 / K)) (s ^ K) ≤ 1 := fun s h0 h1 =>
    max_le (Real.rpow_le_one h0 h1 (by positivity)) (Real.rpow_le_one h0 h1 hK0.le)
  have htwo : max ((2 : ℝ) ^ (1 / K)) ((2 : ℝ) ^ K) ≤ (2 : ℝ) ^ K := by
    refine max_le (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) le_rfl
    rw [div_le_iff₀ hK0]; nlinarith
  -- upper: base `a`, points `a'`, `b`
  have hup : ‖F a' - F a‖ ≤ C * ‖F b - F a‖ := by
    have h := htp a a' b hab
    rw [norm_sub_rev a a', ha', norm_sub_rev a b, ← htdef,
      show t / 2 / t = 1 / 2 by field_simp] at h
    have h' := h.trans (mul_le_mul_of_nonneg_left (hsmall (1 / 2) (by norm_num) (by norm_num))
      hC0.le)
    rw [mul_one, norm_sub_rev (F a) (F a'), norm_sub_rev (F a) (F b), div_le_iff₀ hFb] at h'
    exact h'
  -- lower: base `a`, points `b`, `a'`
  have hlow : ‖F b - F a‖ / (C * (2 : ℝ) ^ K) ≤ ‖F a' - F a‖ := by
    have h := htp a b a' (Ne.symm ha'a)
    rw [norm_sub_rev a b, ← htdef, norm_sub_rev a a', ha', show t / (t / 2) = 2 by field_simp] at h
    have h' := h.trans (mul_le_mul_of_nonneg_left htwo hC0.le)
    rw [norm_sub_rev (F a) (F b), norm_sub_rev (F a) (F a'), div_le_iff₀ hFa'] at h'
    rw [div_le_iff₀ (by positivity)]
    linarith
  refine ⟨hlow, hup, fun ζ hζ1 => ?_⟩
  -- distance to the curve: base `a'`, points `a`, `ζ`
  have hd : t / 2 ≤ ‖a' - ζ‖ := hζ ζ hζ1
  have ha'ζ : a' ≠ ζ := fun h => by rw [h, sub_self, norm_zero] at hd; linarith
  have hFζ : 0 < ‖F a' - F ζ‖ := norm_pos_iff.2 (sub_ne_zero.2 (fun h => ha'ζ (hi h)))
  have h := htp a' a ζ ha'ζ
  rw [ha'] at h
  have hs1 : t / 2 / ‖a' - ζ‖ ≤ 1 := by rw [div_le_one (by linarith)]; exact hd
  have h' := h.trans (mul_le_mul_of_nonneg_left
    (hsmall _ (by positivity) hs1) hC0.le)
  rw [mul_one, div_le_iff₀ hFζ] at h'
  rw [div_le_iff₀ (by positivity)]
  have hC2 : C ≤ C ^ 2 := by nlinarith
  calc ‖F b - F a‖ ≤ C * (2 : ℝ) ^ K * ‖F a' - F a‖ := by
        rw [div_le_iff₀ (by positivity)] at hlow; linarith
    _ ≤ C * (2 : ℝ) ^ K * (C * ‖F a' - F ζ‖) := by
        exact mul_le_mul_of_nonneg_left h' (by positivity)
    _ = ‖F a' - F ζ‖ * (C ^ 2 * (2 : ℝ) ^ K) := by ring

/-- Lemma 3.12 `lem:corkscrew-bounded`, `sec03-coarse.tex:359`: for a bounded `K`-quasicircle there
is `c₂ = c₂(K) > 0` such that for `x ∈ Γ` and `0 < r ≤ diam(Γ)/2` there are `y₊ ∈ Ω`, `y₋ ∈ Ω*`
with `c₂ r ≤ |y± - x| ≤ r/c₂` and `dist(y±, Γ) ≥ c₂ r`. -/
theorem lem_corkscrew_bounded (K : ℝ) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ Ω Ωs : Set ℂ, IsBoundedKQuasicircle Ω Ωs K →
      ∀ x ∈ curveOf Ω Ωs, ∀ r : ℝ, 0 < r → r ≤ diam (curveOf Ω Ωs) / 2 →
        ∃ yp ∈ Ω, ∃ ym ∈ Ωs,
          c₂ * r ≤ ‖yp - x‖ ∧ ‖yp - x‖ ≤ r / c₂ ∧ c₂ * r ≤ ‖ym - x‖ ∧ ‖ym - x‖ ≤ r / c₂ ∧
          c₂ * r ≤ infDist yp (curveOf Ω Ωs) ∧ c₂ * r ≤ infDist ym (curveOf Ω Ωs) := by
  -- `F` is a homeomorphism of `ℂ`, so `F(∞) = ∞` and no Möbius normalisation is needed.
  -- `c₂ = 1/(C² 2^K)` with `C ≥ 1` the three-point constant; `y₊ = F(a(1 - t/2))`,
  -- `y₋ = F(a(1 + t/2))`, `t = |b - a|`, `|F b - F a| = r`.
  by_cases hK : 1 ≤ K
  swap
  · refine ⟨1, one_pos, fun Ω Ωs hq => ?_⟩
    obtain ⟨F, hF, -⟩ := hq
    exact absurd hF.2.1 hK
  obtain ⟨C₀, -, htp⟩ := lem_three_point K hK
  set C := max C₀ 1 with hCdef
  have hC : 1 ≤ C := le_max_right _ _
  have hC0 : 0 < C := by linarith
  have h2K : 1 ≤ (2 : ℝ) ^ K := Real.one_le_rpow (by norm_num) (by linarith)
  refine ⟨1 / (C ^ 2 * (2 : ℝ) ^ K), by positivity, fun Ω Ωs hq x hx r hr hrd => ?_⟩
  obtain ⟨F, hF, hs, hD, hE⟩ := hq
  have hc : Continuous F := continuousOn_univ.mp hF.2.2.1.1
  have hi : Function.Injective F := injOn_univ.mp hF.2.2.1.2.1
  have hcurve := s03_cb_curve hi hs hD hE
  have htpC : ∀ a b c : ℂ, a ≠ c → ‖F a - F b‖ / ‖F a - F c‖ ≤
      C * max ((‖a - b‖ / ‖a - c‖) ^ (1 / K)) ((‖a - b‖ / ‖a - c‖) ^ K) := fun a b c hac =>
    ((htp F hF hs a b c hac).1).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_max_of_le_right
        (Real.rpow_nonneg (by positivity) _)))
  rw [hcurve] at hx hrd ⊢
  obtain ⟨a, ha, rfl⟩ := hx
  have ha1 : ‖a‖ = 1 := ha
  obtain ⟨b, hb, hbr⟩ := s03_cb_far hc ha1 hr hrd
  have hab : a ≠ b := fun h => by rw [h, sub_self, norm_zero] at hbr; linarith
  set t := ‖b - a‖ with htdef
  have ht : 0 < t := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hab))
  have ht2 : t ≤ 2 := by
    calc t ≤ ‖b‖ + ‖a‖ := norm_sub_le _ _
      _ = 2 := by rw [hb, ha1]; norm_num
  -- the two points `a(1 ∓ t/2)`
  have hpt : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      ‖a * ((1 + σ * t / 2 : ℝ) : ℂ)‖ = 1 + σ * t / 2 ∧
      ‖a * ((1 + σ * t / 2 : ℝ) : ℂ) - a‖ = t / 2 ∧
      ∀ ζ : ℂ, ‖ζ‖ = 1 → t / 2 ≤ ‖a * ((1 + σ * t / 2 : ℝ) : ℂ) - ζ‖ := by
    intro σ hσ
    have hσ1 : |σ| = 1 := by rcases hσ with h | h <;> simp [h]
    have hpos : 0 ≤ 1 + σ * t / 2 := by rcases hσ with h | h <;> rw [h] <;> linarith
    have hn : ‖a * ((1 + σ * t / 2 : ℝ) : ℂ)‖ = 1 + σ * t / 2 := by
      rw [norm_mul, ha1, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
    refine ⟨hn, ?_, fun ζ hζ => ?_⟩
    · rw [show a * ((1 + σ * t / 2 : ℝ) : ℂ) - a = a * ((σ * t / 2 : ℝ) : ℂ) by push_cast; ring,
        norm_mul, ha1, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, hσ1,
        abs_of_pos ht]
      norm_num
    · have h := abs_norm_sub_norm_le (a * ((1 + σ * t / 2 : ℝ) : ℂ)) ζ
      rw [hn, hζ] at h
      rcases hσ with h' | h' <;> rw [h'] at h ⊢
      · rw [show 1 + 1 * t / 2 - 1 = t / 2 by ring, abs_of_pos (by linarith)] at h; exact h
      · rw [show 1 + -1 * t / 2 - 1 = -(t / 2) by ring, abs_neg, abs_of_pos (by linarith)] at h
        exact h
  obtain ⟨nm, dm, zm⟩ := hpt (-1) (Or.inr rfl)
  obtain ⟨np, dp, zp⟩ := hpt 1 (Or.inl rfl)
  set am := a * ((1 + -1 * t / 2 : ℝ) : ℂ) with hamdef
  set ap := a * ((1 + 1 * t / 2 : ℝ) : ℂ) with hapdef
  have hamD : am ∈ unitDisc := mem_ball_zero_iff.2 (by rw [nm]; linarith)
  have hapE : ap ∈ unitDiscExterior := show 1 < ‖ap‖ by rw [np]; linarith
  obtain ⟨lm, um, cm⟩ := s03_cb_pt hK hC htpC hi hab dm zm
  obtain ⟨lp, up, cp⟩ := s03_cb_pt hK hC htpC hi hab dp zp
  rw [hbr] at lm um cm lp up cp
  have hc₂ : 0 < C ^ 2 * (2 : ℝ) ^ K := by positivity
  have hle1 : 1 / (C ^ 2 * (2 : ℝ) ^ K) * r ≤ r / (C * (2 : ℝ) ^ K) := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_left hr.le (by positivity) (by nlinarith)
  have hle2 : C * r ≤ r / (1 / (C ^ 2 * (2 : ℝ) ^ K)) := by
    rw [div_div_eq_mul_div, div_one]
    have hX : C ≤ C ^ 2 * (2 : ℝ) ^ K := by
      nlinarith [mul_le_mul_of_nonneg_left h2K (sq_nonneg C)]
    nlinarith [mul_le_mul_of_nonneg_left hX hr.le]
  have hne : (F '' {z : ℂ | ‖z‖ = 1}).Nonempty := ⟨F a, a, ha, rfl⟩
  have hinf : ∀ y : ℂ, (∀ ζ : ℂ, ‖ζ‖ = 1 → r / (C ^ 2 * (2 : ℝ) ^ K) ≤ ‖y - F ζ‖) →
      1 / (C ^ 2 * (2 : ℝ) ^ K) * r ≤ infDist y (F '' {z : ℂ | ‖z‖ = 1}) := by
    intro y hy
    refine (le_infDist hne).2 ?_
    rintro _ ⟨ζ, hζ, rfl⟩
    rw [dist_eq_norm, one_div_mul_eq_div]
    exact hy ζ hζ
  refine ⟨F am, by rw [← hD]; exact mem_image_of_mem F hamD, F ap,
    by rw [← hE]; exact mem_image_of_mem F hapE, hle1.trans lm, um.trans hle2, hle1.trans lp, up.trans hle2,
    hinf _ cm, hinf _ cp⟩

/-- Proof of `lem_corkscrew_bounded_sharp`: `Ω = F(𝔻)` is bounded and `F(1) ∈ Γ`, so
`dist(·, Γ)` is bounded on `Ω`. -/
theorem s03_lem_corkscrew_bounded_sharp (K : ℝ) {c₂ : ℝ} (hc₂ : 0 < c₂) {Ω Ωs : Set ℂ}
    (hq : IsBoundedKQuasicircle Ω Ωs K) :
    ∃ r : ℝ, 0 < r ∧ ∀ yp ∈ Ω, infDist yp (curveOf Ω Ωs) < c₂ * r := by
  obtain ⟨F, hK, -, hD, hE⟩ := hq
  have hc : Continuous F := continuousOn_univ.mp hK.2.2.1.1
  have hi : Function.Injective F := injOn_univ.mp hK.2.2.1.2.1
  have h1 : F 1 ∈ curveOf Ω Ωs := by
    show F 1 ∈ (Ω ∪ Ωs)ᶜ
    rintro (h | h)
    · rw [← hD] at h
      obtain ⟨z, hz, hzF⟩ := h
      rw [hi hzF] at hz
      have := mem_ball_zero_iff.mp hz
      norm_num at this
    · rw [← hE] at h
      obtain ⟨z, hz, hzF⟩ := h
      rw [hi hzF] at hz
      have : (1 : ℝ) < ‖(1 : ℂ)‖ := hz
      norm_num at this
  obtain ⟨R, hR⟩ := ((isCompact_closedBall (0 : ℂ) 1).image hc).isBounded.subset_closedBall 0
  refine ⟨(max R 0 + ‖F 1‖ + 1) / c₂, by positivity, fun yp hyp => ?_⟩
  have hy : ‖yp‖ ≤ R := by
    rw [← hD] at hyp
    obtain ⟨z, hz, rfl⟩ := hyp
    exact mem_closedBall_zero_iff.mp (hR (mem_image_of_mem F (ball_subset_closedBall hz)))
  calc infDist yp (curveOf Ω Ωs) ≤ dist yp (F 1) := infDist_le_dist_of_mem h1
    _ ≤ ‖yp‖ + ‖F 1‖ := by rw [dist_eq_norm]; exact norm_sub_le _ _
    _ < c₂ * ((max R 0 + ‖F 1‖ + 1) / c₂) := by
      rw [mul_div_cancel₀ _ hc₂.ne']
      linarith [le_max_left R 0]

/-- §3.7, `sec03-coarse.tex:382`: the restriction `r ≤ diam(Γ)/2` cannot be removed: at large
scales the bounded side contains no point at distance `≥ c₂ r` from `Γ`. -/
theorem lem_corkscrew_bounded_sharp (K : ℝ) {c₂ : ℝ} (hc₂ : 0 < c₂) {Ω Ωs : Set ℂ}
    (hq : IsBoundedKQuasicircle Ω Ωs K) :
    ∃ r : ℝ, 0 < r ∧ ∀ yp ∈ Ω, infDist yp (curveOf Ω Ωs) < c₂ * r := by
  exact s03_lem_corkscrew_bounded_sharp K hc₂ hq

/-- For `T z = ζ₀ - 2iζ₀/(z + i)` (`|ζ₀| = 1`, `z ≠ -i`): `(1 - |T z|²) |z + i|² = 4 Im z`. -/
theorem s03_T_norm_identity {ζ₀ : ℂ} (hζ₀ : ‖ζ₀‖ = 1) {z : ℂ} (hz : z ≠ -I) :
    (1 - ‖ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹‖ ^ 2) * ‖z + I‖ ^ 2 = 4 * z.im := by
  have hzI : z + I ≠ 0 := fun h => hz (eq_neg_of_add_eq_zero_left h)
  have hn : ‖z + I‖ ≠ 0 := norm_ne_zero_iff.mpr hzI
  have hT : ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹ = ζ₀ * (z - I) / (z + I) := by
    field_simp
    ring
  have h1 : ‖ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹‖ ^ 2 * ‖z + I‖ ^ 2 = ‖z - I‖ ^ 2 := by
    rw [hT, norm_div, norm_mul, hζ₀, one_mul, div_pow]
    field_simp
  have h2 : ‖z + I‖ ^ 2 - ‖z - I‖ ^ 2 = 4 * z.im := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [add_re, add_im, sub_re, sub_im, I_re, I_im]
    ring
  linear_combination h2 - h1

/-- `|T z| < 1` exactly on the upper half-plane (`z ≠ -i`). -/
theorem s03_T_norm_lt_one_iff {ζ₀ : ℂ} (hζ₀ : ‖ζ₀‖ = 1) {z : ℂ} (hz : z ≠ -I) :
    ‖ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹‖ < 1 ↔ 0 < z.im := by
  have E := s03_T_norm_identity hζ₀ hz
  have hP : 0 < ‖z + I‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr fun h => hz (eq_neg_of_add_eq_zero_left h)) 2
  have hn := norm_nonneg (ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹)
  constructor
  · intro h
    have h2 : ‖ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹‖ ^ 2 < 1 := by nlinarith
    have := mul_pos (by linarith : (0 : ℝ) < 1 - ‖ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹‖ ^ 2) hP
    linarith
  · intro h
    by_contra hc
    push_neg at hc
    have h2 : 1 ≤ ‖ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹‖ ^ 2 := by nlinarith
    have := mul_nonpos_of_nonpos_of_nonneg
      (by linarith : 1 - ‖ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹‖ ^ 2 ≤ 0) hP.le
    linarith

/-- `|T z| > 1` exactly on the lower half-plane (`z ≠ -i`). -/
theorem s03_T_one_lt_norm_iff {ζ₀ : ℂ} (hζ₀ : ‖ζ₀‖ = 1) {z : ℂ} (hz : z ≠ -I) :
    1 < ‖ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹‖ ↔ z.im < 0 := by
  have E := s03_T_norm_identity hζ₀ hz
  have hP : 0 < ‖z + I‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr fun h => hz (eq_neg_of_add_eq_zero_left h)) 2
  have hn := norm_nonneg (ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹)
  constructor
  · intro h
    have h2 : 1 < ‖ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹‖ ^ 2 := by nlinarith
    have := mul_neg_of_neg_of_pos (by linarith : 1 - ‖ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹‖ ^ 2 < 0) hP
    linarith
  · intro h
    by_contra hc
    push_neg at hc
    have h2 : ‖ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹‖ ^ 2 ≤ 1 := by nlinarith
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ‖ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹‖ ^ 2) hP.le
    linarith

/-- Every `w` off the unit circle is `T z` for some `z ≠ -i` (`z` the Cayley image of `w/ζ₀`,
LZ `tp_b1_T_cayley`). -/
theorem s03_T_surj {ζ₀ : ℂ} (hζ₀ : ‖ζ₀‖ = 1) {w : ℂ} (hw : ‖w‖ ≠ 1) :
    ∃ z : ℂ, z ≠ -I ∧ ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹ = w := by
  have hζ0 : ζ₀ ≠ 0 := ne_zero_of_norm_ne_zero (by rw [hζ₀]; exact one_ne_zero)
  have hu : w / ζ₀ ≠ 1 := by
    intro h
    apply hw
    rw [div_eq_one_iff_eq hζ0] at h
    rw [h, hζ₀]
  have hT := tp_b1_T_cayley ζ₀ hu
  refine ⟨I * (1 + w / ζ₀) / (1 - w / ζ₀), fun h => hu ?_, ?_⟩
  · rw [h, neg_add_cancel, inv_zero, mul_zero, sub_zero] at hT
    exact mul_left_cancel₀ hζ0 (hT.symm.trans (mul_one ζ₀).symm)
  · rw [hT]
    field_simp

/-- The Möbius map `T z = ζ₀ (z - i)/(z + i)` (written `ζ₀ - 2iζ₀/(z + i)`, `|ζ₀| = 1`) maps the
upper half-plane onto `𝔻`. -/
theorem s03_T_image_upper {ζ₀ : ℂ} (hζ₀ : ‖ζ₀‖ = 1) :
    (fun z : ℂ => ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹) '' upperHalf = unitDisc := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzI : z ≠ -I := by
      rintro rfl
      have h : (0 : ℝ) < (-I).im := hz
      norm_num at h
    exact mem_ball_zero_iff.mpr ((s03_T_norm_lt_one_iff hζ₀ hzI).2 hz)
  · intro hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    obtain ⟨z, hzI, rfl⟩ := s03_T_surj hζ₀ hw1.ne
    exact ⟨z, (s03_T_norm_lt_one_iff hζ₀ hzI).1 hw1, rfl⟩

/-- `T` maps the lower half-plane minus its pole `-i` onto `{|z| > 1}`. -/
theorem s03_T_image_lower {ζ₀ : ℂ} (hζ₀ : ‖ζ₀‖ = 1) :
    (fun z : ℂ => ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹) '' (lowerHalf \ {-I}) = unitDiscExterior := by
  ext w
  constructor
  · rintro ⟨z, ⟨hz, hzI⟩, rfl⟩
    exact (s03_T_one_lt_norm_iff hζ₀ fun h => hzI (mem_singleton_iff.mpr h)).2 hz
  · intro hw
    have hw1 : 1 < ‖w‖ := hw
    obtain ⟨z, hzI, rfl⟩ := s03_T_surj hζ₀ hw1.ne'
    exact ⟨z, ⟨(s03_T_one_lt_norm_iff hζ₀ hzI).1 hw1, hzI⟩, rfl⟩

/-- **Quasi-pair transport.** For a bounded `K`-quasicircle `(Ω, Ωs)` and `x₀ ∈ Γ`, the pair
transported by `invAt x₀` is a `K`-quasi-pair through `∞`: `G = invAt x₀ ∘ F ∘ T` with `F` the
global `K`-q.c. map and `T` as above (`F(T z) ≠ x₀` for `z ≠ -i`), `G(-i) = 0`; `G` is `K`-q.c. off
`-i` (LZ `tp_b1_conj_isKQC`), a homeomorphism of the plane (`tp_b1_conj_isHomeomorphOnto`), and the
point is removable (`b4_isKQC_univ_of_punctured`). -/
theorem s03_invPair_isKQuasiPair {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    {x₀ : ℂ} (hx₀ : x₀ ∈ curveOf Ω Ωs) :
    IsKQuasiPair (invPairΩ Ω x₀) (invPairΩs Ωs x₀) K := by
  obtain ⟨F, hF, hFs, hF1, hF2⟩ := hΓ
  obtain ⟨ζ₀, -, rfl⟩ : x₀ ∈ F '' univ := by rw [hFs]; exact mem_univ _
  simp only [curveOf, mem_compl_iff, mem_union, not_or] at hx₀
  have hζ₀ : ‖ζ₀‖ = 1 := by
    rcases lt_trichotomy ‖ζ₀‖ 1 with h | h | h
    · exact absurd (by rw [← hF1]; exact mem_image_of_mem F (mem_ball_zero_iff.mpr h)) hx₀.1
    · exact h
    · exact absurd (by rw [← hF2]; exact mem_image_of_mem F (show ζ₀ ∈ unitDiscExterior from h))
        hx₀.2
  have hζ0 : ζ₀ ≠ 0 := ne_zero_of_norm_ne_zero (by rw [hζ₀]; exact one_ne_zero)
  have hK := tp_b1_conj_isKQC hF 0 hζ0 one_ne_zero
  have hH := tp_b1_conj_isHomeomorphOnto hF hFs 0 hζ0 one_ne_zero
  obtain ⟨G, hGdef⟩ : ∃ G : ℂ → ℂ,
      G = fun z : ℂ => 0 + 1 * (F (ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹) - F ζ₀)⁻¹ := ⟨_, rfl⟩
  rw [← hGdef] at hK hH
  have hGz : ∀ z, G z = (F (ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹) - F ζ₀)⁻¹ := fun z => by
    simp only [hGdef, zero_add, one_mul]
  have hG0 : G (-I) = 0 := by
    rw [hGz]
    simp
  refine ⟨G, b4_isKQC_univ_of_punctured hH hK, hH.2.2.1, ?_, ?_⟩
  · rw [show invPairΩ Ω (F ζ₀) = invAt (F ζ₀) ''
        (F '' ((fun z : ℂ => ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹) '' upperHalf)) by
          unfold invPairΩ
          rw [s03_T_image_upper hζ₀, hF1],
      image_image, image_image]
    exact image_congr fun z _ => hGz z
  · have hmem : -I ∈ lowerHalf := by
      show (-I).im < 0
      simp
    rw [← insert_sdiff_self_of_mem hmem, image_insert_eq, hG0,
      show invPairΩs Ωs (F ζ₀) = insert 0 (invAt (F ζ₀) ''
        (F '' ((fun z : ℂ => ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹) '' (lowerHalf \ {-I})))) by
          unfold invPairΩs
          rw [s03_T_image_lower hζ₀, hF2, union_singleton],
      image_image, image_image]
    exact congrArg (insert 0) (image_congr fun z _ => hGz z)

/-! ## W-COMP: compactness of normalized quasi pairs (stages K1–K4)

Shared by `prop_mass_volume_claim` (S06) and `lem_tube` (S04).  Bypasses: affine normalization
(no `ℂ̂`), and on the `Ω*` side the `Q`-q.c. extensions of `lem_qc_extension` instead of the
Carathéodory kernel theorem.  All statements are general (no `K`-quasi pair is fixed). -/

/-- W-COMP K1 helper: `max(t^{1/Q}, t^Q) ≤ s^Q` for `0 ≤ t ≤ s`, `1 ≤ s`, `1 ≤ Q`. -/
theorem s03_wc_eta_le {Q t s : ℝ} (hQ : 1 ≤ Q) (ht : 0 ≤ t) (hts : t ≤ s) (hs : 1 ≤ s) :
    max (t ^ (1 / Q)) (t ^ Q) ≤ s ^ Q := by
  have hQ0 : 0 < Q := by linarith
  refine max_le ?_ (Real.rpow_le_rpow ht hts hQ0.le)
  refine le_trans (Real.rpow_le_rpow ht hts (by positivity)) ?_
  refine Real.rpow_le_rpow_of_exponent_le hs ?_
  rw [div_le_iff₀ hQ0]
  nlinarith

/-- W-COMP K1 (plane distortion): a `Q`-q.c. homeomorphism `F` of `ℂ` onto `ℂ` with `F 0 = 0`,
`F 1 = 1` satisfies `|F a| ≤ C η(|a|)`, `|a| ≤ C η(|F a|)` and the local Hölder bound
`|F a - F b| ≤ C (|a| + 1)^Q η(|a - b|)`, `η(t) = max(t^{1/Q}, t^Q)`, with `C` depending only on
`Q` (from `lem_three_point` at `(0, a, 1)` and `(a, b, a + 1)`). -/
theorem s03_wc_dist (Q : ℝ) (hQ : 1 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : ℂ → ℂ, IsKQC F univ Q → F '' univ = univ → F 0 = 0 → F 1 = 1 →
      ∀ a b : ℂ, ‖F a‖ ≤ C * max (‖a‖ ^ (1 / Q)) (‖a‖ ^ Q) ∧
        ‖a‖ ≤ C * max (‖F a‖ ^ (1 / Q)) (‖F a‖ ^ Q) ∧
        ‖F a - F b‖ ≤ C * (‖a‖ + 1) ^ Q * max (‖a - b‖ ^ (1 / Q)) (‖a - b‖ ^ Q) := by
  obtain ⟨C, hC, htp⟩ := lem_three_point Q hQ
  refine ⟨C + 2 * C * C, by positivity, fun F hF hs h0 h1 a b => ?_⟩
  have hD : C ≤ C + 2 * C * C := by nlinarith
  have h01 : (0 : ℂ) ≠ 1 := zero_ne_one
  have hA := htp F hF hs 0 a 1 h01
  simp only [h0, h1, zero_sub, norm_neg, norm_one, div_one] at hA
  have hFa : ‖F a‖ ≤ C * max (‖a‖ ^ (1 / Q)) (‖a‖ ^ Q) := hA.1
  refine ⟨le_trans hFa (mul_le_mul_of_nonneg_right hD
      (le_max_of_le_right (by positivity))), le_trans hA.2 (mul_le_mul_of_nonneg_right hD
      (le_max_of_le_right (by positivity))), ?_⟩
  have hinj : Function.Injective F := fun x y hxy =>
    hF.2.2.1.2.1 (mem_univ x) (mem_univ y) hxy
  have hac : a ≠ a + 1 := by
    intro h
    have : (1 : ℂ) = 0 := by linear_combination -h
    exact one_ne_zero this
  have hB := (htp F hF hs a b (a + 1) hac).1
  have hn1 : ‖a - (a + 1)‖ = 1 := by
    rw [show a - (a + 1) = -1 by ring, norm_neg, norm_one]
  rw [hn1, div_one] at hB
  have hpos : 0 < ‖F a - F (a + 1)‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hac (hinj h))
  rw [div_le_iff₀ hpos] at hB
  set M := max (‖a - b‖ ^ (1 / Q)) (‖a - b‖ ^ Q) with hMdef
  have hM0 : 0 ≤ M := le_max_of_le_right (by positivity)
  have hs1 : 1 ≤ ‖a‖ + 1 := by linarith [norm_nonneg a]
  have hA1 := (htp F hF hs 0 (a + 1) 1 h01).1
  simp only [h0, h1, zero_sub, norm_neg, norm_one, div_one] at hA1
  have hE1 : ‖F a‖ ≤ C * (‖a‖ + 1) ^ Q :=
    le_trans hFa (mul_le_mul_of_nonneg_left
      (s03_wc_eta_le hQ (norm_nonneg a) (by linarith) hs1) hC.le)
  have hE2 : ‖F (a + 1)‖ ≤ C * (‖a‖ + 1) ^ Q :=
    le_trans hA1 (mul_le_mul_of_nonneg_left
      (s03_wc_eta_le hQ (norm_nonneg _) (by simpa using norm_add_le a 1) hs1) hC.le)
  have hdiff : ‖F a - F (a + 1)‖ ≤ 2 * C * (‖a‖ + 1) ^ Q := by
    linarith [norm_sub_le (F a) (F (a + 1))]
  have hP0 : 0 ≤ (‖a‖ + 1) ^ Q := by positivity
  calc ‖F a - F b‖ ≤ C * M * ‖F a - F (a + 1)‖ := hB
    _ ≤ C * M * (2 * C * (‖a‖ + 1) ^ Q) :=
        mul_le_mul_of_nonneg_left hdiff (mul_nonneg hC.le hM0)
    _ = 2 * C * C * (‖a‖ + 1) ^ Q * M := by ring
    _ ≤ (C + 2 * C * C) * (‖a‖ + 1) ^ Q * M := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hP0) hM0
        linarith

/-- W-COMP K2 helper (Arzelà–Ascoli on `ℂ`): a sequence of maps `ℂ → ℂ`, bounded and
equicontinuous on every closed ball, has a locally uniformly convergent subsequence with a
continuous limit. -/
theorem s03_wc_ascoli (u : ℕ → ℂ → ℂ)
    (hb : ∀ R : ℝ, ∃ B : ℝ, ∀ (n : ℕ) (z : ℂ), ‖z‖ ≤ R → ‖u n z‖ ≤ B)
    (heq : ∀ R ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (a b : ℂ), ‖a‖ ≤ R → ‖a - b‖ < δ →
      ‖u n a - u n b‖ < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → ℂ, Continuous v ∧
      TendstoLocallyUniformly (fun n => u (φ n)) v atTop := by
  choose B hB using hb
  choose! δ hδ0 hδ using heq
  set T : Set (ℂ → ℂ) := {g | (∀ z, ‖g z‖ ≤ B ‖z‖) ∧ ∀ R ε : ℝ, 0 < ε → ∀ a b : ℂ, ‖a‖ ≤ R →
    ‖a - b‖ < δ R ε → ‖g a - g b‖ ≤ ε} with hT
  have hTc : ∀ g ∈ T, Continuous g := by
    intro g hg
    rw [Metric.continuous_iff]
    intro a ε hε
    refine ⟨δ ‖a‖ (ε / 2), hδ0 _ _ (half_pos hε), fun b hb => ?_⟩
    rw [dist_eq_norm, ← norm_neg, neg_sub]
    rw [dist_eq_norm, ← norm_neg, neg_sub] at hb
    have := hg.2 ‖a‖ (ε / 2) (half_pos hε) a b le_rfl hb
    linarith
  have h1 : IsClosed {g : ℂ → ℂ | ∀ z, ‖g z‖ ≤ B ‖z‖} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun z =>
      isClosed_le (continuous_norm.comp (continuous_apply z)) continuous_const
  have h2 : IsClosed {g : ℂ → ℂ | ∀ R ε : ℝ, 0 < ε → ∀ a b : ℂ, ‖a‖ ≤ R →
      ‖a - b‖ < δ R ε → ‖g a - g b‖ ≤ ε} := by
    simp only [ofPred_forall]
    refine isClosed_iInter fun R => isClosed_iInter fun ε => isClosed_iInter fun _ =>
      isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => ?_
    exact isClosed_le (continuous_norm.comp ((continuous_apply a).sub (continuous_apply b)))
      continuous_const
  have hTcl : IsClosed T := h1.inter h2
  have hTk : IsCompact T :=
    (isCompact_univ_pi fun z => isCompact_closedBall (0 : ℂ) (B ‖z‖)).of_isClosed_subset hTcl
      fun g hg z _ => by simpa [mem_closedBall, dist_zero_right] using hg.1 z
  set S : Set C(ℂ, ℂ) := {f | ⇑f ∈ T} with hS
  have hST : ContinuousMap.toFun '' S = T := by
    ext g
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact hf
    · intro hg
      exact ⟨⟨g, hTc g hg⟩, hg, rfl⟩
  have heqc : Equicontinuous ((↑) : S → ℂ → ℂ) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    refine ⟨δ ‖x₀‖ (ε / 2), hδ0 _ _ (half_pos hε), fun x hx f => ?_⟩
    rw [dist_eq_norm, ← norm_neg, neg_sub] at hx
    have := f.2.2 ‖x₀‖ (ε / 2) (half_pos hε) x₀ x le_rfl hx
    rw [dist_eq_norm]
    exact lt_of_le_of_lt this (half_lt_self hε)
  have hSk : IsCompact S := ArzelaAscoli.isCompact_of_equicontinuous S (hST ▸ hTk) heqc
  have hmem : ∀ n, u n ∈ T := fun n =>
    ⟨fun z => hB ‖z‖ n z le_rfl, fun R ε hε a b ha hab => (hδ R ε hε n a b ha hab).le⟩
  obtain ⟨f, -, φ, hφ, hlim⟩ :=
    hSk.tendsto_subseq (x := fun n => (⟨u n, hTc _ (hmem n)⟩ : C(ℂ, ℂ))) fun n => hmem n
  exact ⟨φ, hφ, ⇑f, f.continuous, ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlim⟩

/-- W-COMP K2 helper: `η(t) = max(t^{1/Q}, t^Q)` is small for small `t ≥ 0`. -/
theorem s03_wc_eta_small {Q : ℝ} (hQ : 1 ≤ Q) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 ≤ t → t < δ → max (t ^ (1 / Q)) (t ^ Q) < η := by
  have hQ0 : 0 < Q := by linarith
  have hc : ContinuousAt (fun t : ℝ => max (t ^ (1 / Q)) (t ^ Q)) 0 :=
    (Real.continuousAt_rpow_const 0 (1 / Q) (Or.inr (by positivity))).max
      (Real.continuousAt_rpow_const 0 Q (Or.inr hQ0.le))
  have h0 : max ((0 : ℝ) ^ (1 / Q)) ((0 : ℝ) ^ Q) = 0 := by
    rw [Real.zero_rpow (by positivity), Real.zero_rpow hQ0.ne', max_self]
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp hc η hη
  refine ⟨δ, hδ, fun t ht htδ => ?_⟩
  have := h (x := t) (by rwa [Real.dist_eq, sub_zero, abs_of_nonneg ht])
  rw [h0, Real.dist_eq, sub_zero] at this
  exact lt_of_le_of_lt (le_abs_self _) this

/-- W-COMP K2 helper: locally uniform convergence passes to subsequences. -/
theorem s03_wc_tlu_subseq {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (h : TendstoLocallyUniformly F f atTop)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) : TendstoLocallyUniformly (fun n => F (φ n)) f atTop := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto] at h ⊢
  intro x
  exact (h x).comp (hφ.tendsto_atTop.prodMap tendsto_id)

/-- W-COMP K2 helper: the bounds of `s03_wc_dist` feed `s03_wc_ascoli` for any sequence of
normalized `Q`-q.c. homeomorphisms of `ℂ` onto `ℂ`. -/
theorem s03_wc_ascoli_qc {Q : ℝ} (hQ : 1 ≤ Q) (u : ℕ → ℂ → ℂ) (hu : ∀ n, IsKQC (u n) univ Q)
    (hs : ∀ n, u n '' univ = univ) (h0 : ∀ n, u n 0 = 0) (h1 : ∀ n, u n 1 = 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → ℂ, Continuous v ∧
      TendstoLocallyUniformly (fun n => u (φ n)) v atTop := by
  obtain ⟨C, hC, hd⟩ := s03_wc_dist Q hQ
  refine s03_wc_ascoli u (fun R => ⟨C * (|R| + 1) ^ Q, fun n z hz => ?_⟩)
    (fun R ε hε => ?_)
  · refine le_trans (hd (u n) (hu n) (hs n) (h0 n) (h1 n) z z).1
      (mul_le_mul_of_nonneg_left (s03_wc_eta_le hQ (norm_nonneg z)
        (by linarith [le_abs_self R]) (by linarith [abs_nonneg R])) hC.le)
  · have hP : 0 < C * (|R| + 1) ^ Q + 1 := by positivity
    obtain ⟨δ, hδ, h⟩ := s03_wc_eta_small hQ (div_pos hε hP)
    refine ⟨δ, hδ, fun n a b ha hab => ?_⟩
    have h3 := (hd (u n) (hu n) (hs n) (h0 n) (h1 n) a b).2.2
    have hm := h ‖a - b‖ (norm_nonneg _) hab
    have hA : (‖a‖ + 1) ^ Q ≤ (|R| + 1) ^ Q :=
      Real.rpow_le_rpow (by positivity) (by linarith [le_abs_self R]) (by linarith)
    have hM0 : 0 ≤ max (‖a - b‖ ^ (1 / Q)) (‖a - b‖ ^ Q) := le_max_of_le_right (by positivity)
    calc ‖u n a - u n b‖ ≤ C * (‖a‖ + 1) ^ Q * max (‖a - b‖ ^ (1 / Q)) (‖a - b‖ ^ Q) := h3
      _ ≤ (C * (|R| + 1) ^ Q + 1) * max (‖a - b‖ ^ (1 / Q)) (‖a - b‖ ^ Q) := by
          refine mul_le_mul_of_nonneg_right ?_ hM0
          nlinarith
      _ < (C * (|R| + 1) ^ Q + 1) * (ε / (C * (|R| + 1) ^ Q + 1)) :=
          mul_lt_mul_of_pos_left hm hP
      _ = ε := by field_simp

/-- W-COMP K2 helper (the limit is `Q`-q.c.): a locally uniform limit of `Q`-q.c. maps of `ℂ`
that is not constant is `Q`-q.c. on `ℂ` (LZ `thm8_2_limit` on balls; a quadrilateral with closure
in `ℂ` lies in a ball). -/
theorem s03_wc_limit_qc {Q : ℝ} {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ} (hF : ∀ n, IsKQC (F n) univ Q)
    (hconv : TendstoLocallyUniformly F G atTop) {a b : ℂ} (hab : G a ≠ G b) :
    IsKQC G univ Q := by
  have hU := tendstoLocallyUniformlyOn_univ.mpr hconv
  refine t203_lim_limit_isKQC isOpen_univ hF hU ?_
  intro x _ y _ hxy
  have hk : 0 < ‖x‖ + ‖y‖ + ‖a‖ + ‖b‖ + 1 := by positivity
  have hmem : ∀ z : ℂ, ‖z‖ < ‖x‖ + ‖y‖ + ‖a‖ + ‖b‖ + 1 →
      z ∈ ball (0 : ℂ) (‖x‖ + ‖y‖ + ‖a‖ + ‖b‖ + 1) := fun z hz => by simpa using hz
  have nx := norm_nonneg x
  have ny := norm_nonneg y
  have na := norm_nonneg a
  have nb := norm_nonneg b
  rcases thm8_2_limit isBounded_ball (isConnected_ball hk)
      (fun n => ac_t_isKQC_restrict (hF n) isOpen_ball (subset_univ _))
      (hU.mono (subset_univ _)) with ⟨c, hc⟩ | h
  · exact absurd ((hc a (hmem a (by linarith))).trans (hc b (hmem b (by linarith))).symm) hab
  · exact h.2.2.1.2.1 (hmem x (by linarith)) (hmem y (by linarith)) hxy

/-- W-COMP K2 (plane compactness with inverses): normalized (`0 ↦ 0`, `1 ↦ 1`) `Q`-q.c.
homeomorphisms of `ℂ` onto `ℂ` have a subsequence converging locally uniformly to a normalized
`Q`-q.c. homeomorphism `G` of `ℂ` onto `ℂ`, with the inverses converging locally uniformly to
`G⁻¹`. -/
theorem s03_wc_compact {Q : ℝ} (hQ : 1 ≤ Q) (F : ℕ → ℂ → ℂ) (hF : ∀ n, IsKQC (F n) univ Q)
    (hs : ∀ n, F n '' univ = univ) (h0 : ∀ n, F n 0 = 0) (h1 : ∀ n, F n 1 = 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G H : ℂ → ℂ, IsKQC G univ Q ∧ G '' univ = univ ∧ G 0 = 0 ∧
      G 1 = 1 ∧ (∀ z, H (G z) = z) ∧ (∀ z, G (H z) = z) ∧
      TendstoLocallyUniformly (fun n => F (φ n)) G atTop ∧
      TendstoLocallyUniformly (fun n => Function.invFunOn (F (φ n)) univ) H atTop := by
  have hinj : ∀ n, Function.Injective (F n) := fun n x y hxy =>
    (hF n).2.2.1.2.1 (mem_univ x) (mem_univ y) hxy
  have hFiF : ∀ n z, Function.invFunOn (F n) univ (F n z) = z := fun n z =>
    (hinj n).injOn.leftInvOn_invFunOn (mem_univ z)
  have hFFi : ∀ n z, F n (Function.invFunOn (F n) univ z) = z := fun n z => by
    have hz : z ∈ F n '' univ := by rw [hs n]; exact mem_univ z
    exact Function.invFunOn_eq hz
  have hFiK : ∀ n, IsKQC (Function.invFunOn (F n) univ) univ Q := fun n => by
    have h := thm7_2_inv (hF n)
    rwa [hs n] at h
  have hFis : ∀ n, Function.invFunOn (F n) univ '' univ = univ := fun n =>
    image_univ_of_surjective fun z => ⟨F n z, hFiF n z⟩
  have hFi0 : ∀ n, Function.invFunOn (F n) univ 0 = 0 := fun n => by
    simpa [h0 n] using hFiF n 0
  have hFi1 : ∀ n, Function.invFunOn (F n) univ 1 = 1 := fun n => by
    simpa [h1 n] using hFiF n 1
  obtain ⟨φ₁, hφ₁, G, hGc, hG⟩ := s03_wc_ascoli_qc hQ F hF hs h0 h1
  obtain ⟨φ₂, hφ₂, H, hHc, hH⟩ := s03_wc_ascoli_qc hQ (fun n => Function.invFunOn (F (φ₁ n)) univ)
    (fun n => hFiK _) (fun n => hFis _) (fun n => hFi0 _) (fun n => hFi1 _)
  have hG' := s03_wc_tlu_subseq hG hφ₂
  have hpt : ∀ z, Tendsto (fun n => F (φ₁ (φ₂ n)) z) atTop (𝓝 (G z)) := fun z =>
    hG'.tendsto_comp hGc.continuousAt tendsto_const_nhds
  have hG0 : G 0 = 0 := tendsto_nhds_unique (hpt 0) (by simp only [h0]; exact tendsto_const_nhds)
  have hG1 : G 1 = 1 := tendsto_nhds_unique (hpt 1) (by simp only [h1]; exact tendsto_const_nhds)
  have hHG : ∀ z, H (G z) = z := fun z => by
    have := hH.tendsto_comp hHc.continuousAt (hpt z)
    simp only [hFiF] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hGH : ∀ z, G (H z) = z := fun z => by
    have hq : Tendsto (fun n => Function.invFunOn (F (φ₁ (φ₂ n))) univ z) atTop (𝓝 (H z)) :=
      hH.tendsto_comp hHc.continuousAt tendsto_const_nhds
    have := hG'.tendsto_comp hGc.continuousAt hq
    simp only [hFFi] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hGK : IsKQC G univ Q := s03_wc_limit_qc (fun n => hF _) hG' (a := 0) (b := 1)
    (by rw [hG0, hG1]; exact zero_ne_one)
  exact ⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, G, H, hGK,
    image_univ_of_surjective fun z => ⟨H z, hGH z⟩, hG0, hG1, hHG, hGH, hG', hH⟩

/-- W-COMP K3 helper (Weierstrass): a locally uniform limit on an open set of holomorphic maps,
if injective, is holomorphic with nonvanishing derivative, and all derivatives converge locally
uniformly. -/
theorem s03_wc_weierstrass {U : Set ℂ} (hU : IsOpen U) {g : ℕ → ℂ → ℂ} {gL : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn g gL atTop U) (hd : ∀ n, DifferentiableOn ℂ (g n) U)
    (hinj : InjOn gL U) :
    DifferentiableOn ℂ gL U ∧ (∀ z ∈ U, deriv gL z ≠ 0) ∧
      ∀ k : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedDeriv k (g n)) (iteratedDeriv k gL)
        atTop U := by
  have hdL : DifferentiableOn ℂ gL U := hconv.differentiableOn (Eventually.of_forall hd) hU
  refine ⟨hdL, fun z hz => deriv_ne_zero_of_injOn hU hdL hinj hz, fun k => ?_⟩
  have key : ∀ k : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedDeriv k (g n))
      (iteratedDeriv k gL) atTop U ∧ ∀ n, DifferentiableOn ℂ (iteratedDeriv k (g n)) U := by
    intro k
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using ⟨hconv, hd⟩
    | succ k ih =>
      simp only [iteratedDeriv_succ]
      exact ⟨ih.1.deriv (Eventually.of_forall ih.2) hU, fun n => (ih.2 n).deriv hU⟩
  exact (key k).1

/-- W-COMP K3 helper: along a strictly increasing `ψ`, a sequence `y k → x` can be spread to a
full sequence `ζ n → x` with `ζ (ψ k) = y k` (`ζ n = y k` for the largest `k` with `ψ k ≤ n`). -/
theorem s03_wc_spread {α : Type*} [TopologicalSpace α] {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    {y : ℕ → α} {x : α} (hy : Tendsto y atTop (𝓝 x)) :
    ∃ ζ : ℕ → α, Tendsto ζ atTop (𝓝 x) ∧ (∀ k, ζ (ψ k) = y k) ∧ ∀ n, ∃ k, ζ n = y k := by
  refine ⟨fun n => y (Nat.findGreatest (fun k => ψ k ≤ n) n), ?_, fun k => ?_,
    fun n => ⟨_, rfl⟩⟩
  · refine hy.comp (tendsto_atTop_atTop.mpr fun m => ⟨ψ m, fun n hn => ?_⟩)
    exact Nat.le_findGreatest (le_trans (hψ.id_le m) hn) hn
  · show y (Nat.findGreatest (fun j => ψ j ≤ ψ k) (ψ k)) = y k
    congr 1
    rw [Nat.findGreatest_eq_iff]
    refine ⟨hψ.id_le k, fun _ => le_rfl, fun j hkj _ hj => ?_⟩
    exact absurd hj (not_le.mpr (hψ hkj))

/-- W-COMP K3 helper (sequential convergence on a compact set is uniform): if
`u n (ζ n) → v x` whenever `ζ n → x` inside the compact set `S` (`x ∈ S`), then `u n → v`
uniformly on `S`. -/
theorem s03_wc_unif_of_seq {α : Type*} [MetricSpace α] {S : Set α} (hS : IsCompact S)
    {u : ℕ → α → ℝ} {v : α → ℝ}
    (h : ∀ x ∈ S, ∀ ζ : ℕ → α, (∀ n, ζ n ∈ S) → Tendsto ζ atTop (𝓝 x) →
      Tendsto (fun n => u n (ζ n)) atTop (𝓝 (v x))) :
    TendstoUniformlyOn u v atTop S := by
  -- subsequence version of `h`
  have hsub : ∀ x ∈ S, ∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ y : ℕ → α, (∀ k, y k ∈ S) →
      Tendsto y atTop (𝓝 x) → Tendsto (fun k => u (ψ k) (y k)) atTop (𝓝 (v x)) := by
    intro x hx ψ hψ y hyS hy
    obtain ⟨ζ, hζ, hζψ, hζy⟩ := s03_wc_spread hψ hy
    have hζS : ∀ n, ζ n ∈ S := fun n => by
      obtain ⟨k, hk⟩ := hζy n
      rw [hk]
      exact hyS k
    have := (h x hx ζ hζS hζ).comp hψ.tendsto_atTop
    simpa only [Function.comp_def, hζψ] using this
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hne
  rw [not_eventually] at hne
  obtain ⟨ψ, hψ, hψP⟩ := extraction_of_frequently_atTop hne
  simp only [not_forall, not_lt] at hψP
  choose y hyS hyε using hψP
  obtain ⟨x, hxS, θ, hθ, hyx⟩ := hS.tendsto_subseq hyS
  -- `v` is sequentially continuous along `y ∘ θ`
  have hpt : ∀ k, Tendsto (fun n => u n (y (θ k))) atTop (𝓝 (v (y (θ k)))) := fun k =>
    h _ (hyS _) (fun _ => y (θ k)) (fun _ => hyS _) tendsto_const_nhds
  have hN : ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, dist (u n (y (θ k))) (v (y (θ k))) < 1 / ((k : ℝ) + 1) :=
    fun k => Metric.tendsto_atTop.mp (hpt k) _ (by positivity)
  choose N hN using hN
  have hm : StrictMono fun k => (∑ j ∈ Finset.range (k + 1), N j) + k := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    simp only [Finset.sum_range_succ (n := k + 1)]
    omega
  have hmN : ∀ k, N k ≤ (∑ j ∈ Finset.range (k + 1), N j) + k := fun k => by
    have := Finset.single_le_sum (f := N) (fun j _ => Nat.zero_le (N j))
      (Finset.self_mem_range_succ k)
    omega
  have h1 := hsub x hxS _ hm (fun k => y (θ k)) (fun k => hyS _) hyx
  have hv : Tendsto (fun k => v (y (θ k))) atTop (𝓝 (v x)) := by
    refine tendsto_iff_dist_tendsto_zero.mpr ?_
    have hd0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1' := tendsto_iff_dist_tendsto_zero.mp h1
    refine squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) (by simpa using h1'.add hd0)
    have := hN k _ (hmN k)
    rw [dist_comm, one_div] at this
    linarith [dist_triangle (v (y (θ k))) (u ((∑ j ∈ Finset.range (k + 1), N j) + k) (y (θ k)))
      (v x)]
  have h2 := hsub x hxS (ψ ∘ θ) (hψ.comp hθ) (fun k => y (θ k)) (fun k => hyS _) hyx
  have h3 : Tendsto (fun k => dist (v (y (θ k))) (u ((ψ ∘ θ) k) (y (θ k)))) atTop
      (𝓝 (dist (v x) (v x))) := hv.dist h2
  rw [dist_self] at h3
  obtain ⟨k, hk⟩ := (h3.eventually (gt_mem_nhds hε)).exists
  exact absurd (hyε (θ k)) (not_le.mpr hk)

/-- W-COMP K3 helper: the Schwarzian of a holomorphic map with `f' ≠ 0`, written through
`f', f'', f'''`. -/
theorem s03_wc_schwarzian_eq {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {w : ℂ} (hw : w ∈ U) (hd : deriv f w ≠ 0) :
    schwarzian f w = (deriv (deriv (deriv f)) w * deriv f w -
        deriv (deriv f) w * deriv (deriv f) w) / deriv f w ^ 2 -
      1 / 2 * (deriv (deriv f) w / deriv f w) ^ 2 := by
  have hn := hU.mem_nhds hw
  have h1 := hf.deriv hU
  have h2 := h1.deriv hU
  rw [schwarzian_of_analyticAt (hf.analyticAt hn)]
  show deriv (fun u => deriv (deriv f) u / deriv f u) w -
      (1 / 2) * (deriv (deriv f) w / deriv f w) ^ 2 = _
  rw [deriv_fun_div (h2.differentiableAt hn) (h1.differentiableAt hn) hd]

/-- W-COMP K3 (2-jet continuity): if conformal maps `h n : 𝔻 → Ω n` converge locally uniformly
on `𝔻` to a conformal `hL : 𝔻 → ΩL`, then along every `ζ n → z ∈ 𝔻` the point `h n (ζ n)`, the
density `λ`, `A = ∂ log λ`, the Schwarzian norm `s`, the Epstein point `X` and `Φ_{q n}` (for
`q n → q ∈ ℍ³`) converge (by `eq_lambda_f`, `s02_logDensityDz_mul_deriv`, `eq_s_disk`, the
formula of `epstein` and `s03_wc_weierstrass`). -/
theorem s03_wc_jets {Ω : ℕ → Set ℂ} {ΩL : Set ℂ} {h : ℕ → ℂ → ℂ} {hL : ℂ → ℂ}
    (hc : ∀ n, IsConformalOnto (h n) unitDisc (Ω n)) (hcL : IsConformalOnto hL unitDisc ΩL)
    (hconv : TendstoLocallyUniformlyOn h hL atTop unitDisc) {z : ℂ} (hz : z ∈ unitDisc)
    {ζ : ℕ → ℂ} (hζD : ∀ n, ζ n ∈ unitDisc) (hζ : Tendsto ζ atTop (𝓝 z)) :
    Tendsto (fun n => h n (ζ n)) atTop (𝓝 (hL z)) ∧
      Tendsto (fun n => poincareDensity (Ω n) (h n (ζ n))) atTop
        (𝓝 (poincareDensity ΩL (hL z))) ∧
      Tendsto (fun n => logDensityDz (Ω n) (h n (ζ n))) atTop
        (𝓝 (logDensityDz ΩL (hL z))) ∧
      Tendsto (fun n => schwarzNorm (Ω n) (h n (ζ n))) atTop (𝓝 (schwarzNorm ΩL (hL z))) ∧
      Tendsto (fun n => epstein (Ω n) (h n (ζ n))) atTop (𝓝 (epstein ΩL (hL z))) ∧
      ∀ (q : ℕ → ℂ × ℝ) (q₀ : ℂ × ℝ), 0 < q₀.2 → Tendsto q atTop (𝓝 q₀) →
        Tendsto (fun n => horoPhi (Ω n) (q n) (h n (ζ n))) atTop (𝓝 (horoPhi ΩL q₀ (hL z))) := by
  have hU : IsOpen unitDisc := show IsOpen (ball (0 : ℂ) 1) from isOpen_ball
  obtain ⟨hdL, hdL0, hiter⟩ := s03_wc_weierstrass hU hconv (fun n => (hc n).1) hcL.2.1
  have hzw : Tendsto ζ atTop (𝓝[unitDisc] z) :=
    tendsto_nhdsWithin_iff.mpr ⟨hζ, Eventually.of_forall hζD⟩
  have hdk : ∀ k, DifferentiableOn ℂ (iteratedDeriv k hL) unitDisc := by
    intro k
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hdL
    | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv hU
  have hJ : ∀ k, Tendsto (fun n => iteratedDeriv k (h n) (ζ n)) atTop
      (𝓝 (iteratedDeriv k hL z)) := fun k =>
    (hiter k).tendsto_comp ((hdk k).continuousOn.continuousWithinAt hz) hz hzw
  have e2 : ∀ f : ℂ → ℂ, iteratedDeriv 2 f = deriv (deriv f) := fun f => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have e3 : ∀ f : ℂ → ℂ, iteratedDeriv 3 f = deriv (deriv (deriv f)) := fun f => by
    rw [iteratedDeriv_succ, e2]
  have hJ0 : Tendsto (fun n => h n (ζ n)) atTop (𝓝 (hL z)) := by
    simpa only [iteratedDeriv_zero] using hJ 0
  have hJ1 : Tendsto (fun n => deriv (h n) (ζ n)) atTop (𝓝 (deriv hL z)) := by
    simpa only [iteratedDeriv_one] using hJ 1
  have hJ2 : Tendsto (fun n => deriv (deriv (h n)) (ζ n)) atTop (𝓝 (deriv (deriv hL) z)) := by
    simpa only [e2] using hJ 2
  have hJ3 : Tendsto (fun n => deriv (deriv (deriv (h n))) (ζ n)) atTop
      (𝓝 (deriv (deriv (deriv hL)) z)) := by
    simpa only [e3] using hJ 3
  have hd_ne : ∀ n, deriv (h n) (ζ n) ≠ 0 := fun n =>
    deriv_ne_zero_of_injOn hU (hc n).1 (hc n).2.1 (hζD n)
  have hdL_ne : deriv hL z ≠ 0 := hdL0 z hz
  have hz1 : ‖z‖ < 1 := by simpa using (show z ∈ ball (0 : ℂ) 1 from hz)
  have h1z : (1 : ℝ) - ‖z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z]
  have h1zp : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hT1 : Tendsto (fun n => (1 : ℝ) - ‖ζ n‖ ^ 2) atTop (𝓝 (1 - ‖z‖ ^ 2)) :=
    tendsto_const_nhds.sub (hζ.norm.pow 2)
  -- the density
  have hlam : ∀ n, poincareDensity (Ω n) (h n (ζ n)) =
      2 / (1 - ‖ζ n‖ ^ 2) / ‖deriv (h n) (ζ n)‖ := fun n => by
    rw [eq_div_iff (norm_ne_zero_iff.mpr (hd_ne n))]
    exact eq_lambda_f (hc n) (hζD n)
  have hlamL : poincareDensity ΩL (hL z) = 2 / (1 - ‖z‖ ^ 2) / ‖deriv hL z‖ := by
    rw [eq_div_iff (norm_ne_zero_iff.mpr hdL_ne)]
    exact eq_lambda_f hcL hz
  have hlT : Tendsto (fun n => poincareDensity (Ω n) (h n (ζ n))) atTop
      (𝓝 (poincareDensity ΩL (hL z))) := by
    rw [show (fun n => poincareDensity (Ω n) (h n (ζ n))) =
      fun n => 2 / (1 - ‖ζ n‖ ^ 2) / ‖deriv (h n) (ζ n)‖ from funext hlam, hlamL]
    exact (tendsto_const_nhds.div hT1 h1z).div hJ1.norm (norm_ne_zero_iff.mpr hdL_ne)
  have hlpos : 0 < poincareDensity ΩL (hL z) := by
    rw [hlamL]
    have := norm_pos_iff.mpr hdL_ne
    positivity
  -- `A = ∂ log λ`
  have hA : ∀ n, logDensityDz (Ω n) (h n (ζ n)) =
      (conj (ζ n) / ((1 - ‖ζ n‖ ^ 2 : ℝ) : ℂ) -
        deriv (deriv (h n)) (ζ n) / (2 * deriv (h n) (ζ n))) / deriv (h n) (ζ n) := fun n => by
    rw [eq_div_iff (hd_ne n)]
    exact s02_logDensityDz_mul_deriv (hc n) (hζD n)
  have hAL : logDensityDz ΩL (hL z) =
      (conj z / ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) - deriv (deriv hL) z / (2 * deriv hL z)) /
        deriv hL z := by
    rw [eq_div_iff hdL_ne]
    exact s02_logDensityDz_mul_deriv hcL hz
  have hAT : Tendsto (fun n => logDensityDz (Ω n) (h n (ζ n))) atTop
      (𝓝 (logDensityDz ΩL (hL z))) := by
    rw [show (fun n => logDensityDz (Ω n) (h n (ζ n))) = fun n =>
      (conj (ζ n) / ((1 - ‖ζ n‖ ^ 2 : ℝ) : ℂ) -
        deriv (deriv (h n)) (ζ n) / (2 * deriv (h n) (ζ n))) / deriv (h n) (ζ n) from funext hA,
      hAL]
    refine Tendsto.div (Tendsto.sub (Tendsto.div ((Complex.continuous_conj.tendsto z).comp hζ)
      ((Complex.continuous_ofReal.tendsto _).comp hT1) (Complex.ofReal_ne_zero.mpr h1z))
      (hJ2.div (tendsto_const_nhds.mul hJ1) (mul_ne_zero two_ne_zero hdL_ne))) hJ1 hdL_ne
  -- the Schwarzian norm
  have hsT : Tendsto (fun n => schwarzNorm (Ω n) (h n (ζ n))) atTop
      (𝓝 (schwarzNorm ΩL (hL z))) := by
    rw [show (fun n => schwarzNorm (Ω n) (h n (ζ n))) = fun n =>
      ‖(deriv (deriv (deriv (h n))) (ζ n) * deriv (h n) (ζ n) -
        deriv (deriv (h n)) (ζ n) * deriv (deriv (h n)) (ζ n)) / deriv (h n) (ζ n) ^ 2 -
          1 / 2 * (deriv (deriv (h n)) (ζ n) / deriv (h n) (ζ n)) ^ 2‖ *
        (1 - ‖ζ n‖ ^ 2) ^ 2 / 4 from funext fun n => by
      rw [eq_s_disk (hc n) (hζD n), s03_wc_schwarzian_eq hU (hc n).1 (hζD n) (hd_ne n)],
      eq_s_disk hcL hz, s03_wc_schwarzian_eq hU hdL hz hdL_ne]
    refine Tendsto.div_const (Tendsto.mul (Tendsto.norm (Tendsto.sub (Tendsto.div
      ((hJ3.mul hJ1).sub (hJ2.mul hJ2)) (hJ1.pow 2) (pow_ne_zero 2 hdL_ne))
      (tendsto_const_nhds.mul ((hJ2.div hJ1 hdL_ne).pow 2)))) (hT1.pow 2)) 4
  -- the Epstein point
  have hden : 0 < poincareDensity ΩL (hL z) ^ 2 + 4 * ‖logDensityDz ΩL (hL z)‖ ^ 2 := by
    positivity
  have hDT : Tendsto (fun n => poincareDensity (Ω n) (h n (ζ n)) ^ 2 +
      4 * ‖logDensityDz (Ω n) (h n (ζ n))‖ ^ 2) atTop
      (𝓝 (poincareDensity ΩL (hL z) ^ 2 + 4 * ‖logDensityDz ΩL (hL z)‖ ^ 2)) :=
    (hlT.pow 2).add (tendsto_const_nhds.mul (hAT.norm.pow 2))
  have hXT : Tendsto (fun n => epstein (Ω n) (h n (ζ n))) atTop (𝓝 (epstein ΩL (hL z))) := by
    refine Tendsto.prodMk_nhds ?_ ?_
    · refine hJ0.add (Tendsto.div (tendsto_const_nhds.mul
        ((Complex.continuous_conj.tendsto _).comp hAT))
        ((Complex.continuous_ofReal.tendsto _).comp hDT)
        (Complex.ofReal_ne_zero.mpr hden.ne'))
    · exact (tendsto_const_nhds.mul hlT).div hDT hden.ne'
  refine ⟨hJ0, hlT, hAT, hsT, hXT, fun q q₀ hq₀ hq => ?_⟩
  have hq1 : Tendsto (fun n => (q n).1) atTop (𝓝 q₀.1) := (continuous_fst.tendsto _).comp hq
  have hq2 : Tendsto (fun n => (q n).2) atTop (𝓝 q₀.2) := (continuous_snd.tendsto _).comp hq
  exact (hlT.mul (((hq1.sub hJ0).norm.pow 2).add (hq2.pow 2))).div
    (tendsto_const_nhds.mul hq2) (by positivity)

/-- W-COMP K4 helper: pre-composing a `K`-q.c. homeomorphism of `ℂ` with an affine map. -/
theorem s03_wc_affine_pre {F : ℂ → ℂ} {K : ℝ} (hF : IsKQC F univ K) (hs : F '' univ = univ)
    {α : ℂ} (β : ℂ) (hα : α ≠ 0) :
    IsKQC (fun v => F (α * v + β)) univ K ∧ (fun v => F (α * v + β)) '' univ = univ := by
  have h := td_affine_comp hF hs β 0 hα one_ne_zero
  simp only [one_mul, add_zero] at h
  exact h

/-- W-COMP K4 helper: a real affine map `v ↦ α v + β` (`α > 0`) is a conformal self-map of the
upper and of the lower half-plane. -/
theorem s03_wc_real_affine {α β : ℝ} (hα : 0 < α) :
    IsConformalOnto (fun v : ℂ => (α : ℂ) * v + β) upperHalf upperHalf ∧
      (fun v : ℂ => (α : ℂ) * v + β) '' lowerHalf = lowerHalf := by
  have him : ∀ v : ℂ, ((α : ℂ) * v + β).im = α * v.im := fun v => by simp
  have hα' : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
  have hinv : ∀ z : ℂ, (α : ℂ) * ((z - β) / α) + β = z := fun z => by
    field_simp
    ring
  have himi : ∀ z : ℂ, ((z - β) / (α : ℂ)).im = z.im / α := fun z => by
    rw [Complex.div_ofReal_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
  refine ⟨⟨by fun_prop, fun a _ b _ hab => ?_, ?_⟩, ?_⟩
  · have : (α : ℂ) * a = α * b := by simpa using hab
    exact mul_left_cancel₀ hα' this
  · ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      show 0 < ((α : ℂ) * v + β).im
      rw [him]
      exact mul_pos hα hv
    · intro hz
      refine ⟨(z - β) / α, ?_, hinv z⟩
      show 0 < ((z - β) / (α : ℂ)).im
      rw [himi]
      exact div_pos hz hα
  · ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      show ((α : ℂ) * v + β).im < 0
      rw [him]
      exact mul_neg_of_pos_of_neg hα hv
    · intro hz
      refine ⟨(z - β) / α, ?_, hinv z⟩
      show ((z - β) / (α : ℂ)).im < 0
      rw [himi]
      exact div_neg_of_neg_of_pos hz hα

/-- W-COMP K4 helper (affine normalization of one pair): for a `K`-quasi pair and `w ∈ Ω` there
is an affine `A z = a z + b` with `A w = 0` and a normalized (`0 ↦ 0`, `1 ↦ 1`) `K`-q.c.
homeomorphism `G` of `ℂ` with `v ↦ G (v - i)` mapping `ℍ` onto `A Ω` and the lower half-plane
onto `A Ω*`. -/
theorem s03_wc_normalize {Ω Ωs : Set ℂ} {K : ℝ} (h : IsKQuasiPair Ω Ωs K) {w : ℂ}
    (hw : w ∈ Ω) :
    ∃ (a b : ℂ) (G : ℂ → ℂ), a ≠ 0 ∧ a * w + b = 0 ∧ IsKQC G univ K ∧ G '' univ = univ ∧
      G 0 = 0 ∧ G 1 = 1 ∧ (fun v => G (v - I)) '' upperHalf = (fun z => a * z + b) '' Ω ∧
      (fun v => G (v - I)) '' lowerHalf = (fun z => a * z + b) '' Ωs := by
  obtain ⟨F, hF, hs, hU, hL⟩ := h
  rw [← hU] at hw
  obtain ⟨ζ, hζ, rfl⟩ := hw
  have hζi : 0 < ζ.im := hζ
  have hα : (ζ.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hζi.ne'
  have hζeq : (ζ.im : ℂ) * I + ζ.re = ζ := by
    rw [add_comm]
    exact Complex.re_add_im ζ
  have hinj : Function.Injective F := fun x y hxy =>
    hF.2.2.1.2.1 (mem_univ x) (mem_univ y) hxy
  set c : ℂ := F ((ζ.im : ℂ) * 1 + ((ζ.im : ℂ) * I + ζ.re)) - F ζ with hcdef
  have hc : c ≠ 0 := by
    refine sub_ne_zero.mpr fun h => ?_
    have h' := hinj h
    rw [hζeq, mul_one] at h'
    exact hα (by linear_combination h')
  obtain ⟨hK1, hs1⟩ := s03_wc_affine_pre hF hs ((ζ.im : ℂ) * I + ζ.re) hα
  obtain ⟨hK2, hs2⟩ := bB_l_affine_isKQC hK1 hs1 (F ζ) hc
  have hGv : ∀ v : ℂ, (F ((ζ.im : ℂ) * (v - I) + ((ζ.im : ℂ) * I + ζ.re)) - F ζ) / c =
      c⁻¹ * F ((ζ.im : ℂ) * v + ζ.re) + -F ζ / c := fun v => by
    rw [show (ζ.im : ℂ) * (v - I) + ((ζ.im : ℂ) * I + ζ.re) = (ζ.im : ℂ) * v + ζ.re by ring]
    ring
  have hcomp : (fun v => (F ((ζ.im : ℂ) * (v - I) + ((ζ.im : ℂ) * I + ζ.re)) - F ζ) / c) =
      (fun z => c⁻¹ * z + -F ζ / c) ∘ F ∘ fun v : ℂ => (ζ.im : ℂ) * v + ζ.re :=
    funext hGv
  obtain ⟨hT, hTl⟩ := s03_wc_real_affine (β := ζ.re) hζi
  refine ⟨c⁻¹, -F ζ / c, fun u => (F ((ζ.im : ℂ) * u + ((ζ.im : ℂ) * I + ζ.re)) - F ζ) / c,
    inv_ne_zero hc, by field_simp; ring, hK2, hs2, ?_, ?_, ?_, ?_⟩
  · show (F ((ζ.im : ℂ) * 0 + ((ζ.im : ℂ) * I + ζ.re)) - F ζ) / c = 0
    rw [mul_zero, zero_add, hζeq, sub_self, zero_div]
  · exact div_self hc
  · rw [hcomp, image_comp, image_comp, hT.2.2, ← hU]
  · rw [hcomp, image_comp, image_comp, hTl, ← hL]

/-- W-COMP K4 helper (normalized pair sequences): for `K`-quasi pairs `(Ω n, Ω* n)` with
`w n ∈ Ω n`, after affine changes `A n` with `A n (w n) = 0` and a subsequence, the pairs are
`P n (ℍ), P n (ℍ⁻)` for `K`-q.c. homeomorphisms `P n` of `ℂ` with `P n i = 0`, converging with their
inverses locally uniformly to a `K`-q.c. homeomorphism `PL` of `ℂ` (with inverse `HL`), `PL i = 0`. -/
theorem s03_wc_pairs {K : ℝ} (hK : 1 ≤ K) (Ω Ωs : ℕ → Set ℂ)
    (hpair : ∀ n, IsKQuasiPair (Ω n) (Ωs n) K) (w : ℕ → ℂ) (hw : ∀ n, w n ∈ Ω n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (a b : ℕ → ℂ) (P : ℕ → ℂ → ℂ) (PL HL : ℂ → ℂ),
      (∀ n, a n ≠ 0 ∧ a n * w (φ n) + b n = 0) ∧
      (∀ n, IsKQC (P n) univ K ∧ P n '' univ = univ ∧ P n I = 0 ∧
        P n '' upperHalf = (fun z => a n * z + b n) '' Ω (φ n) ∧
        P n '' lowerHalf = (fun z => a n * z + b n) '' Ωs (φ n)) ∧
      IsKQC PL univ K ∧ PL '' univ = univ ∧ PL I = 0 ∧ (∀ z, HL (PL z) = z ∧ PL (HL z) = z) ∧
      TendstoLocallyUniformly P PL atTop ∧
      TendstoLocallyUniformly (fun n => Function.invFunOn (P n) univ) HL atTop := by
  choose a b G ha hab hGK hGs hG0 hG1 hGU hGL using fun n => s03_wc_normalize (hpair n) (hw n)
  obtain ⟨φ, hφ, Gl, HG, hGLK, hGLs, hGL0, -, hHG, hGH, hconv, hinv⟩ :=
    s03_wc_compact hK G hGK hGs hG0 hG1
  have hshift : ∀ {F : ℂ → ℂ}, IsKQC F univ K → F '' univ = univ →
      IsKQC (fun v => F (v - I)) univ K ∧ (fun v => F (v - I)) '' univ = univ := by
    intro F hF hFs
    have h := s03_wc_affine_pre hF hFs (-I) one_ne_zero
    simp only [one_mul, ← sub_eq_add_neg] at h
    exact h
  have hPi : ∀ n z, Function.invFunOn (fun v => G (φ n) (v - I)) univ z =
      Function.invFunOn (G (φ n)) univ z + I := fun n z => by
    obtain ⟨hK', hs'⟩ := hshift (hGK (φ n)) (hGs (φ n))
    have hinj : Function.Injective (fun v => G (φ n) (v - I)) := fun x y hxy =>
      hK'.2.2.1.2.1 (mem_univ x) (mem_univ y) hxy
    have hz : z ∈ (fun v => G (φ n) (v - I)) '' univ := by rw [hs']; exact mem_univ z
    have hz' : z ∈ G (φ n) '' univ := by rw [hGs]; exact mem_univ z
    refine hinj ((Function.invFunOn_eq hz).trans ?_)
    show z = G (φ n) (Function.invFunOn (G (φ n)) univ z + I - I)
    rw [add_sub_cancel_right, Function.invFunOn_eq hz']
  refine ⟨φ, hφ, fun n => a (φ n), fun n => b (φ n), fun n v => G (φ n) (v - I),
    fun v => Gl (v - I), fun z => HG z + I, fun n => ⟨ha _, hab _⟩, fun n => ?_,
    (hshift hGLK hGLs).1, (hshift hGLK hGLs).2, by simp [hGL0], fun z => ⟨?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨hK', hs'⟩ := hshift (hGK (φ n)) (hGs (φ n))
    exact ⟨hK', hs', by simp [hG0], hGU _, hGL _⟩
  · show HG (Gl (z - I)) + I = z
    rw [hHG, sub_add_cancel]
  · show Gl (HG z + I - I) = z
    rw [add_sub_cancel_right, hGH]
  · exact hconv.comp (fun v => v - I) (continuous_sub_right I)
  · rw [show (fun n => Function.invFunOn (fun v => G (φ n) (v - I)) univ) =
      fun n z => Function.invFunOn (G (φ n)) univ z + I from funext fun n => funext (hPi n)]
    exact (uniformContinuous_id.add uniformContinuous_const).comp_tendstoLocallyUniformly hinv

/-- W-COMP K4 helper: kernel convergence for an arbitrary open set `W` (see `s03_wc_kernel`). -/
theorem s03_wc_kernel_open {Q : ℝ} {P : ℕ → ℂ → ℂ} {PL HL : ℂ → ℂ}
    (hP : ∀ n, IsKQC (P n) univ Q) (hs : ∀ n, P n '' univ = univ) (hPL : IsKQC PL univ Q)
    (hHL : ∀ z, HL (PL z) = z ∧ PL (HL z) = z)
    (hinv : TendstoLocallyUniformly (fun n => Function.invFunOn (P n) univ) HL atTop)
    {W : Set ℂ} (hW : IsOpen W) :
    (∀ C : Set ℂ, IsCompact C → C ⊆ PL '' W → ∀ᶠ n in atTop, C ⊆ P n '' W) ∧
      (∀ (z : ℕ → ℂ) (x : ℂ), Tendsto z atTop (𝓝 x) → (∀ n, z n ∉ P n '' W) →
        x ∉ PL '' W) := by
  have hPi : ∀ n z, P n (Function.invFunOn (P n) univ z) = z := fun n z => by
    have hz : z ∈ P n '' univ := by rw [hs n]; exact mem_univ z
    exact Function.invFunOn_eq hz
  have hcont : ∀ n, Continuous (Function.invFunOn (P n) univ) := fun n => by
    have h := (thm7_2_inv (hP n)).2.2.1.1
    rw [hs n] at h
    exact continuousOn_univ.mp h
  have hHLc : Continuous HL := hinv.continuous (Frequently.of_forall hcont)
  have h1 : ∀ C : Set ℂ, IsCompact C → C ⊆ PL '' W → ∀ᶠ n in atTop, C ⊆ P n '' W := by
    intro C hC hCW
    have hHC : HL '' C ⊆ W := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨v, hv, rfl⟩ := hCW hx
      rw [(hHL v).1]
      exact hv
    obtain ⟨δ, hδ, hth⟩ := (hC.image hHLc).exists_thickening_subset_open hW hHC
    have hu := (tendstoLocallyUniformly_iff_forall_isCompact.mp hinv) C hC
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu δ hδ] with n hn x hx
    refine ⟨Function.invFunOn (P n) univ x, hth ?_, hPi n x⟩
    exact mem_thickening_iff.mpr ⟨HL x, mem_image_of_mem HL hx, by
      rw [dist_comm]
      exact hn x hx⟩
  refine ⟨h1, fun z x hz hzn hx => ?_⟩
  have hO : IsOpen (PL '' W) :=
    isOpen_image_of_isKQC (ac_t_isKQC_restrict hPL hW (subset_univ _))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO x hx
  have hcb : closedBall x (r / 2) ⊆ PL '' W :=
    (closedBall_subset_ball (half_lt_self hr)).trans hball
  obtain ⟨n, hn1, hn2⟩ := ((h1 _ (isCompact_closedBall x (r / 2)) hcb).and
    (hz.eventually (closedBall_mem_nhds x (half_pos hr)))).exists
  exact hzn n (hn1 hn2)

/-- W-COMP K4 helper (kernel convergence without the kernel theorem): if `P n⁻¹ → PL⁻¹` locally
uniformly, every compact subset of `PL(ℍ)` (of `PL(ℍ⁻)`) lies in `P n (ℍ)` (in `P n (ℍ⁻)`) for
large `n`, and a limit of points outside `P n (ℍ)` (outside `P n (ℍ⁻)`) is outside `PL(ℍ)`
(outside `PL(ℍ⁻)`). -/
theorem s03_wc_kernel {Q : ℝ} {P : ℕ → ℂ → ℂ} {PL HL : ℂ → ℂ} (hP : ∀ n, IsKQC (P n) univ Q)
    (hs : ∀ n, P n '' univ = univ) (hPL : IsKQC PL univ Q) (hPLs : PL '' univ = univ)
    (hHL : ∀ z, HL (PL z) = z ∧ PL (HL z) = z)
    (hinv : TendstoLocallyUniformly (fun n => Function.invFunOn (P n) univ) HL atTop) :
    (∀ C : Set ℂ, IsCompact C → C ⊆ PL '' upperHalf → ∀ᶠ n in atTop, C ⊆ P n '' upperHalf) ∧
      (∀ C : Set ℂ, IsCompact C → C ⊆ PL '' lowerHalf → ∀ᶠ n in atTop, C ⊆ P n '' lowerHalf) ∧
      (∀ (z : ℕ → ℂ) (x : ℂ), Tendsto z atTop (𝓝 x) → (∀ n, z n ∉ P n '' upperHalf) →
        x ∉ PL '' upperHalf) ∧
      (∀ (z : ℕ → ℂ) (x : ℂ), Tendsto z atTop (𝓝 x) → (∀ n, z n ∉ P n '' lowerHalf) →
        x ∉ PL '' lowerHalf) := by
  have _h := hPLs
  obtain ⟨u1, u2⟩ := s03_wc_kernel_open hP hs hPL hHL hinv isOpen_upperHalf
  obtain ⟨l1, l2⟩ := s03_wc_kernel_open hP hs hPL hHL hinv isOpen_lowerHalf
  exact ⟨u1, l1, u2, l2⟩

/-- W-COMP K4 helper (core of `s03_wc_riemann`): as `s03_wc_riemann`, assuming a closed ball
about `y₀` inside every `P n (ℍ)` and a common point `x` of every `P n (ℍ⁻)`.  The Riemann maps
come from `s03_qce_partC` (with `Q²`-q.c. extensions `F n`), reparametrized so that `F n i = y₀`;
`G n u = (F n (u + i) - y₀)/d n` with `d n = F n (1 + i) - y₀` is normalized, `|d n|` is bounded
above (through `x`) and below (through the ball), and the limit domain is identified by the
exclusions of `s03_wc_kernel`. -/
theorem s03_wc_riemann_core {Q : ℝ} (hQ : 1 ≤ Q) {P : ℕ → ℂ → ℂ} {PL HL : ℂ → ℂ}
    (hP : ∀ n, IsKQC (P n) univ Q) (hs : ∀ n, P n '' univ = univ) (hPL : IsKQC PL univ Q)
    (hPLs : PL '' univ = univ) (hHL : ∀ z, HL (PL z) = z ∧ PL (HL z) = z)
    (hinv : TendstoLocallyUniformly (fun n => Function.invFunOn (P n) univ) HL atTop)
    {y₀ x : ℂ} {r : ℝ} (hr : 0 < r) (hball : ∀ n, closedBall y₀ r ⊆ P n '' upperHalf)
    (hx : ∀ n, x ∈ P n '' lowerHalf) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (g : ℕ → ℂ → ℂ) (gL : ℂ → ℂ),
      (∀ n, IsConformalOnto (g n) unitDisc (P (φ n) '' upperHalf) ∧ g n 0 = y₀) ∧
      IsConformalOnto gL unitDisc (PL '' upperHalf) ∧ gL 0 = y₀ ∧
      TendstoLocallyUniformlyOn g gL atTop unitDisc := by
  have hQQ : 1 ≤ Q * Q := by nlinarith
  have hpairs : ∀ n, IsKQuasiPair (P n '' upperHalf) (P n '' lowerHalf) Q := fun n =>
    ⟨P n, hP n, hs n, rfl, rfl⟩
  have hdisj : ∀ n z, z ∈ P n '' upperHalf → z ∉ P n '' lowerHalf := by
    rintro n _ ⟨u, hu, rfl⟩ ⟨v, hv, hvu⟩
    have e := (hP n).2.2.1.2.1 (mem_univ v) (mem_univ u) hvu
    have h1 : (0 : ℝ) < u.im := hu
    have h2 : v.im < 0 := hv
    rw [e] at h2
    linarith
  choose f hf F hF hFs hFf using fun n => s03_qce_partC (hpairs n)
  have hy : ∀ n, y₀ ∈ f n '' upperHalf := fun n => by
    rw [(hf n).2.2]
    exact hball n (mem_closedBall_self hr.le)
  choose ζ hζ hfζ using hy
  have hζi : ∀ n, 0 < (ζ n).im := fun n => hζ n
  set F' : ℕ → ℂ → ℂ := fun n v => F n (((ζ n).im : ℂ) * v + (ζ n).re) with hF'def
  set f' : ℕ → ℂ → ℂ := fun n v => f n (((ζ n).im : ℂ) * v + (ζ n).re) with hf'def
  have hT := fun n => s03_wc_real_affine (β := (ζ n).re) (hζi n)
  have hF'K : ∀ n, IsKQC (F' n) univ (Q * Q) ∧ F' n '' univ = univ := fun n =>
    s03_wc_affine_pre (hF n) (hFs n) _ (Complex.ofReal_ne_zero.mpr (hζi n).ne')
  have hf' : ∀ n, IsConformalOnto (f' n) upperHalf (P n '' upperHalf) := fun n =>
    (hf n).comp (hT n).1
  have hFf' : ∀ n, EqOn (F' n) (f' n) upperHalf := fun n v hv =>
    hFf n ((hT n).1.mapsTo hv)
  have hF'I : ∀ n, F' n I = y₀ := fun n => by
    show F n (((ζ n).im : ℂ) * I + (ζ n).re) = y₀
    rw [add_comm, Complex.re_add_im, hFf n (hζ n), hfζ n]
  have hF'U : ∀ n, F' n '' upperHalf = P n '' upperHalf := fun n => by
    rw [(hFf' n).image_eq, (hf' n).2.2]
  have hF'L : ∀ n, F' n '' lowerHalf = P n '' lowerHalf := fun n =>
    (s03_b0_image (hpairs n) (hF'K n).1 (hF'K n).2 (hF'U n)).2
  have hF'inj : ∀ n, Function.Injective (F' n) := fun n a b h =>
    (hF'K n).1.2.2.1.2.1 (mem_univ a) (mem_univ b) h
  -- the normalized maps
  set d : ℕ → ℂ := fun n => F' n (1 + I) - y₀ with hddef
  have hd : ∀ n, d n ≠ 0 := fun n h => by
    have h1 : F' n (1 + I) = F' n I := by rw [hF'I]; exact sub_eq_zero.mp h
    have h2 := hF'inj n h1
    have h3 : (1 : ℂ) = 0 := by linear_combination h2
    exact one_ne_zero h3
  set Gh : ℕ → ℂ → ℂ := fun n u => (F' n (1 * u + I) - y₀) / d n with hGhdef
  have hGhK : ∀ n, IsKQC (Gh n) univ (Q * Q) ∧ Gh n '' univ = univ := fun n => by
    obtain ⟨h1, h2⟩ := s03_wc_affine_pre (hF'K n).1 (hF'K n).2 I one_ne_zero
    exact bB_l_affine_isKQC h1 h2 y₀ (hd n)
  have hGh0 : ∀ n, Gh n 0 = 0 := fun n => by
    show (F' n (1 * 0 + I) - y₀) / d n = 0
    rw [mul_zero, zero_add, hF'I, sub_self, zero_div]
  have hGh1 : ∀ n, Gh n 1 = 1 := fun n => by
    show (F' n (1 * 1 + I) - y₀) / d n = 1
    rw [one_mul]
    exact div_self (hd n)
  have hrep : ∀ n v, F' n v = y₀ + d n * Gh n (v - I) := fun n v => by
    show F' n v = y₀ + d n * ((F' n (1 * (v - I) + I) - y₀) / d n)
    rw [show 1 * (v - I) + I = v by ring]
    field_simp [hd n]
    ring
  -- bounds on `d n`
  obtain ⟨C, hC, hdist⟩ := s03_wc_dist (Q * Q) hQQ
  obtain ⟨δ, hδ, hηs⟩ := s03_wc_eta_small hQQ (inv_pos.mpr hC)
  have hup : ∀ n, ‖d n‖ ≤ ‖x - y₀‖ / δ := by
    intro n
    have hxn : x ∈ F' n '' lowerHalf := by rw [hF'L]; exact hx n
    obtain ⟨u, hu, hux⟩ := hxn
    have hG : Gh n (u - I) = (x - y₀) / d n := by
      have h := hrep n u
      rw [hux] at h
      rw [eq_div_iff (hd n)]
      linear_combination (-1 : ℂ) * h
    have h2 := (hdist (Gh n) (hGhK n).1 (hGhK n).2 (hGh0 n) (hGh1 n) (u - I) 0).2.1
    have h1 : 1 ≤ ‖u - I‖ := by
      have h := Complex.abs_im_le_norm (u - I)
      have hui : (u - I).im = u.im - 1 := by simp
      have hu' : u.im < 0 := hu
      rw [hui, abs_of_neg (by linarith)] at h
      linarith
    by_contra hcon
    push Not at hcon
    have ht : ‖(x - y₀) / d n‖ < δ := by
      rw [norm_div, div_lt_iff₀ (norm_pos_iff.mpr (hd n))]
      rw [div_lt_iff₀ hδ] at hcon
      linarith
    have h3 := hηs _ (norm_nonneg _) ht
    rw [← hG] at h3
    have h4 : C * max (‖Gh n (u - I)‖ ^ (1 / (Q * Q))) (‖Gh n (u - I)‖ ^ (Q * Q)) < 1 :=
      calc _ < C * C⁻¹ := mul_lt_mul_of_pos_left h3 hC
        _ = 1 := mul_inv_cancel₀ hC.ne'
    linarith
  set M : ℝ := C * max (‖(-2 * I : ℂ)‖ ^ (1 / (Q * Q))) (‖(-2 * I : ℂ)‖ ^ (Q * Q)) with hMdef
  have hlow : ∀ n, r < ‖d n‖ * M := by
    intro n
    have hm : F' n (-I) ∈ P n '' lowerHalf := by
      rw [← hF'L]
      exact mem_image_of_mem _ (show (-I).im < 0 by simp)
    have hnot : F' n (-I) ∉ closedBall y₀ r := fun h => hdisj n _ (hball n h) hm
    rw [mem_closedBall, not_le, dist_eq_norm, hrep n (-I), add_sub_cancel_left, norm_mul] at hnot
    have hb := (hdist (Gh n) (hGhK n).1 (hGhK n).2 (hGh0 n) (hGh1 n) (-I - I) 0).1
    rw [show -I - I = -2 * I by ring] at hb hnot
    exact lt_of_lt_of_le hnot (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  -- compactness
  obtain ⟨φ₁, hφ₁, Gl, Hl, hGlK, hGls, hGl0, -, -, -, hconvG, -⟩ :=
    s03_wc_compact hQQ Gh (fun n => (hGhK n).1) (fun n => (hGhK n).2) hGh0 hGh1
  obtain ⟨dL, -, φ₂, hφ₂, hdlim⟩ := (isCompact_closedBall (0 : ℂ) (‖x - y₀‖ / δ)).tendsto_subseq
    (x := fun n => d (φ₁ n)) fun n => by simpa using hup (φ₁ n)
  have hdlim' : Tendsto (fun n => d (φ₁ (φ₂ n))) atTop (𝓝 dL) := hdlim
  have hdL : dL ≠ 0 := by
    intro h0
    have hT' : Tendsto (fun n => ‖d (φ₁ (φ₂ n))‖ * M) atTop (𝓝 (‖dL‖ * M)) :=
      hdlim'.norm.mul_const M
    rw [h0, norm_zero, zero_mul] at hT'
    have := ge_of_tendsto hT' (Eventually.of_forall fun n => (hlow (φ₁ (φ₂ n))).le)
    linarith
  -- the limit map
  set FL : ℂ → ℂ := fun v => y₀ + dL * Gl (v - I) with hFLdef
  have hFLK : IsKQC FL univ (Q * Q) ∧ FL '' univ = univ := by
    have h := td_affine_comp hGlK hGls (-I) y₀ one_ne_zero hdL
    have e : FL = fun z => dL * Gl (1 * z + -I) + y₀ := funext fun v => by
      show y₀ + dL * Gl (v - I) = dL * Gl (1 * v + -I) + y₀
      rw [one_mul, ← sub_eq_add_neg, add_comm]
    rw [e]
    exact h
  have hGlc : Continuous Gl := continuousOn_univ.mp hGlK.2.2.1.1
  have hconvF : TendstoLocallyUniformly (fun n => F' (φ₁ (φ₂ n))) FL atTop := by
    have e : (fun n => F' (φ₁ (φ₂ n))) =
        fun n v => y₀ + d (φ₁ (φ₂ n)) * Gh (φ₁ (φ₂ n)) (v - I) :=
      funext fun n => funext fun v => hrep _ v
    rw [e]
    have hc1 : TendstoLocallyUniformly (fun (_ : ℕ) (_ : ℂ) => y₀) (fun _ => y₀) atTop :=
      (tendsto_const_nhds.tendstoUniformly_const).tendstoLocallyUniformly
    have hc2 : TendstoLocallyUniformly (fun n (_ : ℂ) => d (φ₁ (φ₂ n))) (fun _ => dL) atTop :=
      hdlim'.tendstoUniformly_const.tendstoLocallyUniformly
    have hc3 : TendstoLocallyUniformly (fun n v => Gh (φ₁ (φ₂ n)) (v - I))
        (fun v => Gl (v - I)) atTop :=
      (s03_wc_tlu_subseq hconvG hφ₂).comp (fun v => v - I) (continuous_sub_right I)
    exact hc1.add (hc2.mul₀ hc3 continuous_const (hGlc.comp (continuous_sub_right I)))
  have hFLc : Continuous FL := continuousOn_univ.mp hFLK.1.2.2.1.1
  have hpt : ∀ v, Tendsto (fun n => F' (φ₁ (φ₂ n)) v) atTop (𝓝 (FL v)) := fun v =>
    hconvF.tendsto_comp hFLc.continuousAt tendsto_const_nhds
  have hFLinj : Function.Injective FL := fun a b h =>
    hFLK.1.2.2.1.2.1 (mem_univ a) (mem_univ b) h
  obtain ⟨-, -, kU, kL⟩ := s03_wc_kernel (fun n => hP (φ₁ (φ₂ n))) (fun n => hs (φ₁ (φ₂ n)))
    hPL hPLs hHL (s03_wc_tlu_subseq hinv (hφ₁.comp hφ₂))
  have hi : ∀ v ∈ upperHalf, FL v ∉ PL '' lowerHalf := fun v hv =>
    kL _ _ (hpt v) fun n hn =>
      hdisj (φ₁ (φ₂ n)) _ (by rw [← hF'U]; exact mem_image_of_mem _ hv) hn
  have hii : ∀ v ∉ upperHalf, FL v ∉ PL '' upperHalf := fun v hv =>
    kU _ _ (hpt v) fun n hn => by
      rw [← hF'U] at hn
      obtain ⟨u, hu, hvu⟩ := hn
      exact hv ((hF'inj _ hvu) ▸ hu)
  have hFLU : FL '' upperHalf = PL '' upperHalf := by
    apply Subset.antisymm
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨u, -, hu⟩ : FL v ∈ PL '' univ := by rw [hPLs]; exact mem_univ _
      refine ⟨u, ?_, hu⟩
      by_contra hu0
      have hu0' : u.im ≤ 0 := not_lt.mp hu0
      rcases hu0'.lt_or_eq with hneg | hzero
      · exact hi v hv ⟨u, hneg, hu⟩
      · have hO : IsOpen (PL ⁻¹' (FL '' upperHalf)) :=
          (isOpen_image_of_isKQC (ac_t_isKQC_restrict hFLK.1 isOpen_upperHalf
            (subset_univ _))).preimage (continuousOn_univ.mp hPL.2.2.1.1)
        have huO : u ∈ PL ⁻¹' (FL '' upperHalf) := by
          show PL u ∈ FL '' upperHalf
          rw [hu]
          exact mem_image_of_mem _ hv
        obtain ⟨ε, hε, hεb⟩ := Metric.isOpen_iff.mp hO u huO
        have hu' : u - ((ε / 2 : ℝ) : ℂ) * I ∈ ball u ε := by
          rw [mem_ball, dist_eq_norm, show u - ((ε / 2 : ℝ) : ℂ) * I - u =
            -(((ε / 2 : ℝ) : ℂ) * I) by ring, norm_neg, norm_mul, Complex.norm_I, mul_one,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
          exact half_lt_self hε
        obtain ⟨v', hv', hv'e⟩ := hεb hu'
        refine hi v' hv' ⟨u - ((ε / 2 : ℝ) : ℂ) * I, ?_, hv'e.symm⟩
        show (u - ((ε / 2 : ℝ) : ℂ) * I).im < 0
        simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero]
        linarith
    · rintro _ ⟨u, hu, rfl⟩
      obtain ⟨v, -, hv⟩ : PL u ∈ FL '' univ := by rw [hFLK.2]; exact mem_univ _
      refine ⟨v, ?_, hv⟩
      by_contra hvU
      exact hii v hvU ⟨u, hu, hv.symm⟩
  have hU1 : TendstoLocallyUniformlyOn (fun n => F' (φ₁ (φ₂ n))) FL atTop upperHalf :=
    (tendstoLocallyUniformlyOn_univ.mpr hconvF).mono (subset_univ _)
  have hFLd : DifferentiableOn ℂ FL upperHalf :=
    hU1.differentiableOn (Eventually.of_forall fun n =>
      (hf' (φ₁ (φ₂ n))).1.congr (hFf' (φ₁ (φ₂ n)))) isOpen_upperHalf
  have hFLconf : IsConformalOnto FL upperHalf (PL '' upperHalf) :=
    ⟨hFLd, hFLinj.injOn, hFLU⟩
  have hcay := s02_cayleyInv_conformal
  have hcay0 : cayleyInv 0 = I := by
    show I * (1 + 0) / (1 - 0) = I
    simp
  have hIU : I ∈ upperHalf := show (0 : ℝ) < I.im by simp
  refine ⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, fun n => f' (φ₁ (φ₂ n)) ∘ cayleyInv, FL ∘ cayleyInv,
    fun n => ⟨(hf' (φ₁ (φ₂ n))).comp hcay, ?_⟩, hFLconf.comp hcay, ?_, ?_⟩
  · show f' (φ₁ (φ₂ n)) (cayleyInv 0) = y₀
    rw [hcay0, ← hFf' _ hIU]
    exact hF'I _
  · show FL (cayleyInv 0) = y₀
    rw [hcay0]
    show y₀ + dL * Gl (I - I) = y₀
    rw [sub_self, hGl0, mul_zero, add_zero]
  · refine (hU1.comp cayleyInv hcay.mapsTo hcay.1.continuousOn).congr fun n z hz => ?_
    show F' (φ₁ (φ₂ n)) (cayleyInv z) = f' (φ₁ (φ₂ n)) (cayleyInv z)
    exact hFf' _ (hcay.mapsTo hz)

/-- W-COMP K4 (Riemann maps of the converging domains, upper side): under the convergence of
`s03_wc_pairs`, for an anchor `y₀ ∈ PL(ℍ)` a subsequence of the domains `P n (ℍ)` has conformal
maps `g n : 𝔻 → P (φ n) (ℍ)`, `g n 0 = y₀`, converging locally uniformly on `𝔻` to a conformal
`gL : 𝔻 → PL(ℍ)` (via `s03_qce_partC`, `s03_wc_compact` with `Q²`, and `s03_wc_kernel`). -/
theorem s03_wc_riemann {Q : ℝ} (hQ : 1 ≤ Q) {P : ℕ → ℂ → ℂ} {PL HL : ℂ → ℂ}
    (hP : ∀ n, IsKQC (P n) univ Q) (hs : ∀ n, P n '' univ = univ) (hPL : IsKQC PL univ Q)
    (hPLs : PL '' univ = univ) (hHL : ∀ z, HL (PL z) = z ∧ PL (HL z) = z)
    (hinv : TendstoLocallyUniformly (fun n => Function.invFunOn (P n) univ) HL atTop)
    {y₀ : ℂ} (hy : y₀ ∈ PL '' upperHalf) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (g : ℕ → ℂ → ℂ) (gL : ℂ → ℂ),
      (∀ n, IsConformalOnto (g n) unitDisc (P (φ n) '' upperHalf) ∧ g n 0 = y₀) ∧
      IsConformalOnto gL unitDisc (PL '' upperHalf) ∧ gL 0 = y₀ ∧
      TendstoLocallyUniformlyOn g gL atTop unitDisc := by
  obtain ⟨kU, kL, -, -⟩ := s03_wc_kernel hP hs hPL hPLs hHL hinv
  have hO : IsOpen (PL '' upperHalf) :=
    isOpen_image_of_isKQC (ac_t_isKQC_restrict hPL isOpen_upperHalf (subset_univ _))
  obtain ⟨r, hr, hrb⟩ := Metric.isOpen_iff.mp hO y₀ hy
  have hcb : closedBall y₀ (r / 2) ⊆ PL '' upperHalf :=
    (closedBall_subset_ball (half_lt_self hr)).trans hrb
  have hxL : ({PL (-I)} : Set ℂ) ⊆ PL '' lowerHalf :=
    singleton_subset_iff.mpr (mem_image_of_mem _ (show (-I).im < 0 by simp))
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((kU _ (isCompact_closedBall y₀ (r / 2)) hcb).and
    (kL _ isCompact_singleton hxL))
  have hsh : StrictMono fun n => n + N := fun a b h => Nat.add_lt_add_right h N
  obtain ⟨φ, hφ, g, gL, hg, hgL, hgL0, hconv⟩ := s03_wc_riemann_core hQ
    (P := fun n => P (n + N)) (fun n => hP _) (fun n => hs _) hPL hPLs hHL
    (s03_wc_tlu_subseq hinv hsh) (half_pos hr) (fun n => (hN (n + N) (Nat.le_add_left N n)).1)
    (fun n => (hN (n + N) (Nat.le_add_left N n)).2 rfl)
  exact ⟨fun n => φ n + N, hsh.comp hφ, g, gL, hg, hgL, hgL0, hconv⟩

/-- W-COMP K4 (lower side): `s03_wc_riemann` for the domains `P n (ℍ⁻)`, an anchor
`y₁ ∈ PL(ℍ⁻)` (apply it to `v ↦ P n (-v)`). -/
theorem s03_wc_riemann_lower {Q : ℝ} (hQ : 1 ≤ Q) {P : ℕ → ℂ → ℂ} {PL HL : ℂ → ℂ}
    (hP : ∀ n, IsKQC (P n) univ Q) (hs : ∀ n, P n '' univ = univ) (hPL : IsKQC PL univ Q)
    (hPLs : PL '' univ = univ) (hHL : ∀ z, HL (PL z) = z ∧ PL (HL z) = z)
    (hinv : TendstoLocallyUniformly (fun n => Function.invFunOn (P n) univ) HL atTop)
    {y₁ : ℂ} (hy : y₁ ∈ PL '' lowerHalf) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (g : ℕ → ℂ → ℂ) (gL : ℂ → ℂ),
      (∀ n, IsConformalOnto (g n) unitDisc (P (φ n) '' lowerHalf) ∧ g n 0 = y₁) ∧
      IsConformalOnto gL unitDisc (PL '' lowerHalf) ∧ gL 0 = y₁ ∧
      TendstoLocallyUniformlyOn g gL atTop unitDisc := by
  have hneg : (fun v : ℂ => -v) '' upperHalf = lowerHalf := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      show (-v).im < 0
      have : (0 : ℝ) < v.im := hv
      simp only [Complex.neg_im]
      linarith
    · intro hz
      refine ⟨-z, ?_, neg_neg z⟩
      show (0 : ℝ) < (-z).im
      have : z.im < 0 := hz
      simp only [Complex.neg_im]
      linarith
  have hflip : ∀ {F : ℂ → ℂ}, IsKQC F univ Q → F '' univ = univ →
      IsKQC (fun v => F (-v)) univ Q ∧ (fun v => F (-v)) '' univ = univ := by
    intro F hF hFs
    have h := s03_wc_affine_pre hF hFs 0 (neg_ne_zero.mpr one_ne_zero)
    simp only [neg_one_mul, add_zero] at h
    exact h
  have himg : ∀ F : ℂ → ℂ, (fun v => F (-v)) '' upperHalf = F '' lowerHalf := fun F => by
    rw [← hneg, image_image]
  have hPi : ∀ n z, Function.invFunOn (fun v => P n (-v)) univ z =
      -Function.invFunOn (P n) univ z := fun n z => by
    obtain ⟨hK', hs'⟩ := hflip (hP n) (hs n)
    have hinj : Function.Injective (fun v => P n (-v)) := fun a b hab =>
      hK'.2.2.1.2.1 (mem_univ a) (mem_univ b) hab
    have hz : z ∈ (fun v => P n (-v)) '' univ := by rw [hs']; exact mem_univ z
    have hz' : z ∈ P n '' univ := by rw [hs n]; exact mem_univ z
    refine hinj ((Function.invFunOn_eq hz).trans ?_)
    show z = P n (- -Function.invFunOn (P n) univ z)
    rw [neg_neg, Function.invFunOn_eq hz']
  have hinv' : TendstoLocallyUniformly (fun n => Function.invFunOn (fun v => P n (-v)) univ)
      (fun z => -HL z) atTop := by
    rw [show (fun n => Function.invFunOn (fun v => P n (-v)) univ) =
      fun n z => -Function.invFunOn (P n) univ z from funext fun n => funext (hPi n)]
    exact uniformContinuous_neg.comp_tendstoLocallyUniformly hinv
  have hy' : y₁ ∈ (fun v => PL (-v)) '' upperHalf := by rw [himg]; exact hy
  obtain ⟨φ, hφ, g, gL, hg, hgL, hgL0, hconv⟩ := s03_wc_riemann hQ
    (P := fun n v => P n (-v)) (PL := fun v => PL (-v)) (HL := fun z => -HL z)
    (fun n => (hflip (hP n) (hs n)).1) (fun n => (hflip (hP n) (hs n)).2)
    (hflip hPL hPLs).1 (hflip hPL hPLs).2
    (fun z => ⟨by simp [(hHL _).1], by simp [(hHL _).2]⟩) hinv' hy'
  refine ⟨φ, hφ, g, gL, fun n => ?_, ?_, hgL0, hconv⟩
  · rw [← himg]
    exact hg n
  · rw [← himg]
    exact hgL

end EpsteinVMO
