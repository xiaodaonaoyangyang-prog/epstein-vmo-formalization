import EpsteinVMO.S07_Transfer
import EpsteinVMO.S03_Coarse
import EpsteinVMO.S09_Ambient
import EpsteinVMO.S07b_ShenWei
import EpsteinVMO.S07d_BMO

/-!
# §8 Proof of Theorem B

Source: `sec08-thmB.tex` (Theorem B is stated in `sec01-intro.tex:205`).

A bounded `K`-quasicircle is `IsBoundedKQuasicircle Ω Ωs K` (`Ω` the bounded component). Its
horoball quantities are read through the inversion `invAt x₀` at a point `x₀ ∈ Γ`
(`Defs.lean`, modelling conventions): the transported pair is `(invPairΩ Ω x₀, invPairΩs Ωs x₀)`
and a point `p` is read as `invAt x₀ p`. All statements quantify over `x₀ ∈ Γ` and over labels
of the transported domain. "Gap volume measured from the unbounded side" (Corollary 8.4) uses the
transported pair with the roles exchanged, `KV (invPairΩs Ωs x₀) (invPairΩ Ω x₀)`, with labels in
`invPairΩs Ωs x₀`; it is evaluated on all of `invPairΩs Ωs x₀`, which contains the image `0` of
`∞ ∈ Ω*`.

Not formalized: Remark 8.3 (choice of labels) is Lemma `lem:selection-change` of §3; Remark 8.5
`rem:MT` is a heuristic.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace EpsteinVMO

open LiZhongQC

/-- The Carleson norm is homogeneous: `‖c • μ‖_CM = c ‖μ‖_CM`. -/
theorem s08_carlesonNorm_smul (c : ℝ≥0∞) (μ : Measure ℂ) :
    carlesonNorm (c • μ) = c * carlesonNorm μ := by
  unfold carlesonNorm
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.mul_iSup, mul_div_assoc]

/-- `|Sf|²(1-|z|²)³ dA = 4 ϖ m_f` (Lemma 7.9 written for the Carleson measure). -/
theorem s08_schwarzCarleson_eq (f : ℂ → ℂ) :
    schwarzCarlesonMeasure f = (4 : ℝ≥0∞) • varpiMeasure (pullbackMass f) := by
  rw [lem_one_sided_varpi, smul_smul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
    one_smul]

/-- `sup_{p ∈ Ω} K_H(p) = sup_{a ∈ 𝔻} 𝒫_{m_f}(a)` (Lemma 7.9 and `f(𝔻) = Ω`). -/
theorem s08_sup_KH_eq (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    (f : ℂ → ℂ) (hf : IsConformalOnto f unitDisc Ω) (x₀ : ℂ) (hx₀ : x₀ ∈ curveOf Ω Ωs) :
    ⨆ p ∈ Ω, KH (invPairΩ Ω x₀) (invAt x₀ p) = ⨆ a ∈ unitDisc, poissonP (pullbackMass f) a := by
  refine le_antisymm (iSup₂_le fun p hp => ?_) (iSup₂_le fun a ha => ?_)
  · obtain ⟨a, ha, rfl⟩ : p ∈ f '' unitDisc := by rw [hf.2.2]; exact hp
    rw [lem_one_sided K Ω Ωs hΓ f hf x₀ hx₀ a ha]
    exact le_iSup₂ (f := fun a (_ : a ∈ unitDisc) => poissonP (pullbackMass f) a) a ha
  · rw [← lem_one_sided K Ω Ωs hΓ f hf x₀ hx₀ a ha]
    have hfa : f a ∈ Ω := by rw [← hf.2.2]; exact mem_image_of_mem f ha
    exact le_iSup₂ (f := fun p (_ : p ∈ Ω) => KH (invPairΩ Ω x₀) (invAt x₀ p)) (f a) hfa

/-- `e^{d_𝔻(a, z)} ≤ 2 cosh d_𝔻(a, z)`, written with the explicit `cosh` formula. -/
theorem s08_exp_diskDist_le {a z : ℂ} (ha : a ∈ unitDisc) (hz : z ∈ unitDisc) :
    Real.exp (diskDist a z) ≤ 2 * diskCoshDist a z := by
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hx1 : 1 ≤ diskCoshDist a z := by
    unfold diskCoshDist
    have h0 : 0 ≤ 2 * ‖a - z‖ ^ 2 / ((1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2)) :=
      div_nonneg (by positivity)
        (mul_nonneg (by nlinarith [norm_nonneg a]) (by nlinarith [norm_nonneg z]))
    linarith
  have hc := Real.cosh_arcosh hx1
  unfold diskDist
  rw [Real.cosh_eq] at hc
  nlinarith [Real.exp_pos (-Real.arcosh (diskCoshDist a z))]

/-- Remark 8.1, `rem:vanishing-bounded` (`sec08-thmB.tex:45`): the hypothesis of the forward
direction of B(ii) implies the hypothesis of B(i). -/
theorem rem_vanishing_bounded (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    (f : ℂ → ℂ) (hf : IsConformalOnto f unitDisc Ω) (x₀ : ℂ) (hx₀ : x₀ ∈ curveOf Ω Ωs)
    (lab : ℂ × ℝ → ℂ) (hlab : IsLabel (invPairΩ Ω x₀) lab)
    (hV : DiskBoundaryVanishing
      (fun a => KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ (f a)))) :
    (⨆ p ∈ Ω, KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ p)) < ⊤ := by
  -- Remark 8.1: `K_V(f a) ≤ 1` for `|a| > r`; for `|a| ≤ r` compare with `a₀ = (max r 0 + 1)/2`
  -- through (2.17), `K_V(p) ≤ e^{d_ρ(p, p')} K_V(p')`.
  -- `hΓ` is not needed: only the Riemann map `f` and `x₀ ∉ Ω` are used (the statement stays true
  -- without it).
  have _hΓ := hΓ
  obtain ⟨r, hr1, hr⟩ := hV 1 zero_lt_one
  set r' : ℝ := max r 0 with hr'def
  have hr'1 : r' < 1 := max_lt hr1 one_pos
  have hr'0 : 0 ≤ r' := le_max_right r 0
  set ρ : ℝ := (r' + 1) / 2 with hρdef
  have hρ0 : 0 ≤ ρ := by linarith
  have hρ1 : ρ < 1 := by linarith
  have hrρ : r < ρ := by linarith [le_max_left r 0]
  set a₀ : ℂ := (ρ : ℂ) with ha₀def
  have ha₀n : ‖a₀‖ = ρ := by rw [ha₀def, Complex.norm_real, Real.norm_of_nonneg hρ0]
  have ha₀ : a₀ ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [ha₀n]; exact hρ1)
  have hx₀Ω : x₀ ∉ Ω := fun h => hx₀ (Or.inl h)
  have hF := s07_invAt_conformal hf hx₀Ω
  have hR : ∃ g : ℂ → ℂ, IsConformalOnto g unitDisc (invPairΩ Ω x₀) := ⟨_, hF⟩
  have hFm : ∀ z ∈ unitDisc, invAt x₀ (f z) ∈ invPairΩ Ω x₀ := fun z hz => by
    rw [← hF.2.2]; exact mem_image_of_mem (fun z => invAt x₀ (f z)) hz
  set M : ℝ := 1 + 8 / ((1 - r' ^ 2) * (1 - ρ ^ 2)) with hMdef
  have hD0 : 0 < (1 - r' ^ 2) * (1 - ρ ^ 2) := mul_pos (by nlinarith) (by nlinarith)
  have hM1 : 1 ≤ M := by have := div_pos (by norm_num : (0 : ℝ) < 8) hD0; linarith
  have hKV0 : KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ (f a₀)) ≤ 1 :=
    hr a₀ (by rw [ha₀n]; exact hrρ) (by rw [ha₀n]; exact hρ1)
  have key : ∀ a ∈ unitDisc,
      KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ (f a)) ≤ ENNReal.ofReal (2 * M) := by
    intro a ha
    have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
    by_cases har : r < ‖a‖
    · exact (hr a har ha1).trans (ENNReal.one_le_ofReal.mpr (by linarith))
    have har' : ‖a‖ ≤ r' := (not_lt.mp har).trans (le_max_left r 0)
    have hd : Real.exp (poincareDist (invPairΩ Ω x₀) (invAt x₀ (f a)) (invAt x₀ (f a₀))) ≤
        2 * M := by
      rw [subsec_poincare_dist hF ha ha₀]
      refine (s08_exp_diskDist_le ha ha₀).trans ?_
      have hn : ‖a - a₀‖ ≤ 2 := by
        have := norm_sub_le a a₀
        rw [ha₀n] at this
        linarith
      have hn2 : ‖a - a₀‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (a - a₀)]
      have hsq : ‖a‖ ^ 2 ≤ r' ^ 2 := pow_le_pow_left₀ (norm_nonneg a) har' 2
      have hDD : (1 - r' ^ 2) * (1 - ρ ^ 2) ≤ (1 - ‖a‖ ^ 2) * (1 - ‖a₀‖ ^ 2) := by
        rw [ha₀n]
        exact mul_le_mul_of_nonneg_right (by linarith) (by nlinarith)
      have hfrac : 2 * ‖a - a₀‖ ^ 2 / ((1 - ‖a‖ ^ 2) * (1 - ‖a₀‖ ^ 2)) ≤
          8 / ((1 - r' ^ 2) * (1 - ρ ^ 2)) := by
        rw [div_le_div_iff₀ (hD0.trans_le hDD) hD0]
        nlinarith [mul_le_mul_of_nonneg_right hn2 hD0.le]
      unfold diskCoshDist
      linarith
    have h1 : KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ (f a)) ≤
        ENNReal.ofReal (Real.exp
            (poincareDist (invPairΩ Ω x₀) (invAt x₀ (f a)) (invAt x₀ (f a₀)))) *
          KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ (f a₀)) := by
      unfold KV
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono (measurable_const.mul (ENNReal.measurable_ofReal.comp
        ((s03_sc_meas hR (hFm a₀ ha₀)).comp hlab.1))) fun q hq => ?_
      have hq' : q ∈ UHS \ horoUnion (invPairΩ Ω x₀) := ⟨hq.1, fun h => hq.2 (Or.inl h)⟩
      have hw := (hlab.2 q hq').1
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact ENNReal.ofReal_le_ofReal (eq_kernel_lip_c hR (hFm a ha) (hFm a₀ ha₀) hw)
    calc KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ (f a))
        ≤ ENNReal.ofReal (Real.exp
            (poincareDist (invPairΩ Ω x₀) (invAt x₀ (f a)) (invAt x₀ (f a₀)))) *
          KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ (f a₀)) := h1
      _ ≤ ENNReal.ofReal (2 * M) * 1 := mul_le_mul' (ENNReal.ofReal_le_ofReal hd) hKV0
      _ = ENNReal.ofReal (2 * M) := mul_one _
  refine lt_of_le_of_lt (iSup₂_le fun p hp => ?_) (ENNReal.ofReal_lt_top (r := 2 * M))
  obtain ⟨a, ha, rfl⟩ : p ∈ f '' unitDisc := by rw [hf.2.2]; exact hp
  exact key a ha

/-- Remark 8.2, `rem:B-constants` (`sec08-thmB.tex:60`), first inequality:
`‖|Sf|²(1-|z|²)³ dA‖_CM ≤ 16 sup_Ω K_H`. -/
theorem rem_B_constants_a (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    (f : ℂ → ℂ) (hf : IsConformalOnto f unitDisc Ω) (x₀ : ℂ) (hx₀ : x₀ ∈ curveOf Ω Ωs) :
    carlesonNorm (schwarzCarlesonMeasure f) ≤ 16 * ⨆ p ∈ Ω, KH (invPairΩ Ω x₀) (invAt x₀ p) := by
  rw [s08_schwarzCarleson_eq, s08_carlesonNorm_smul, s08_sup_KH_eq K Ω Ωs hΓ f hf x₀ hx₀,
    show (16 : ℝ≥0∞) = 4 * 4 by norm_num, mul_assoc]
  gcongr
  exact (lem_kernel_test_b (pullbackMass f)).1

/-- Remark 8.2, `rem:B-constants` (`sec08-thmB.tex:62`): the forward direction of B(i) is
quantitative, `‖|Sf|²(1-|z|²)³ dA‖_CM ≤ 16 C(K) sup_Ω K_V` with `C(K)` depending only on `K`. -/
theorem rem_B_constants_b (K : ℝ) (hK : 1 ≤ K) : ∃ C : ℝ≥0,
    ∀ Ω Ωs : Set ℂ, IsBoundedKQuasicircle Ω Ωs K → ∀ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω →
      ∀ x₀ ∈ curveOf Ω Ωs, ∀ lab : ℂ × ℝ → ℂ, IsLabel (invPairΩ Ω x₀) lab →
        carlesonNorm (schwarzCarlesonMeasure f) ≤
          16 * (C : ℝ≥0∞) * ⨆ p ∈ Ω, KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ p) := by
  -- Theorem A's lower bound `K_H ≤ K_H + K_* ≤ C(K) K_V` on the transported quasi-pair, then the
  -- first inequality `rem_B_constants_a`
  obtain ⟨C, hC⟩ := thm_lower K hK
  refine ⟨C, fun Ω Ωs hΓ f hf x₀ hx₀ lab hlab => ?_⟩
  have hpair := s03_invPair_isKQuasiPair hΓ hx₀
  calc carlesonNorm (schwarzCarlesonMeasure f)
      ≤ 16 * ⨆ p ∈ Ω, KH (invPairΩ Ω x₀) (invAt x₀ p) :=
        rem_B_constants_a K Ω Ωs hΓ f hf x₀ hx₀
    _ ≤ 16 * ((C : ℝ≥0∞) *
          ⨆ p ∈ Ω, KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ p)) := by
        gcongr
        refine iSup₂_le fun p hp => ?_
        calc KH (invPairΩ Ω x₀) (invAt x₀ p)
            ≤ KH2 (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ p) := by
              show _ ≤ KH _ _ + Kst _ _ _ _
              exact le_self_add
          _ ≤ (C : ℝ≥0∞) * KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ p) :=
              hC _ _ hpair lab hlab _ (mem_image_of_mem _ hp)
          _ ≤ (C : ℝ≥0∞) *
                ⨆ p ∈ Ω, KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ p) := by
              gcongr
              exact le_iSup₂ (f := fun p (_ : p ∈ Ω) =>
                KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ p)) p hp
    _ = 16 * (C : ℝ≥0∞) *
          ⨆ p ∈ Ω, KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ p) :=
        (mul_assoc _ _ _).symm

/-- Remark 8.2, `rem:B-constants` (`sec08-thmB.tex:64`):
`sup_Ω K_H ≤ 20 ‖|Sf|²(1-|z|²)³ dA‖_CM`. -/
theorem rem_B_constants_c (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    (f : ℂ → ℂ) (hf : IsConformalOnto f unitDisc Ω) (x₀ : ℂ) (hx₀ : x₀ ∈ curveOf Ω Ωs) :
    ⨆ p ∈ Ω, KH (invPairΩ Ω x₀) (invAt x₀ p) ≤ 20 * carlesonNorm (schwarzCarlesonMeasure f) := by
  rw [s08_schwarzCarleson_eq, s08_carlesonNorm_smul, s08_sup_KH_eq K Ω Ωs hΓ f hf x₀ hx₀,
    ← mul_assoc, show (20 : ℝ≥0∞) * 4 = 80 by norm_num]
  exact (lem_kernel_test_b (pullbackMass f)).2

/-- Helper for `cor:B-outer`: the hyperbolic distance `d_ρ` is natural under a similarity
`A z = a z + b` (`f ↦ A ∘ f` is a bijection of the conformal maps `𝔻 → Ω` and `𝔻 → A(Ω)`). -/
theorem s08_mb_pdist_aff (Ω : Set ℂ) {a b : ℂ} (ha : a ≠ 0) (p w : ℂ) :
    poincareDist ((fun z => a * z + b) '' Ω) (a * p + b) (a * w + b) = poincareDist Ω p w := by
  have hconf : ∀ α β : ℂ, α ≠ 0 → ∀ (S : Set ℂ) (f : ℂ → ℂ), IsConformalOnto f unitDisc S →
      IsConformalOnto (fun ζ => α * f ζ + β) unitDisc ((fun z => α * z + β) '' S) := by
    intro α β hα S f hf
    refine ⟨(hf.1.const_mul α).add_const β, fun x hx y hy h => hf.2.1 hx hy ?_, ?_⟩
    · have h' : α * f x + β = α * f y + β := h
      exact mul_left_cancel₀ hα (add_right_cancel h')
    · rw [← hf.2.2, image_image]
  have hai : a⁻¹ ≠ 0 := inv_ne_zero ha
  have hback : (fun z => a⁻¹ * z + -(a⁻¹ * b)) '' ((fun z => a * z + b) '' Ω) = Ω := by
    have e : (fun x => a⁻¹ * (a * x + b) + -(a⁻¹ * b)) = id := by
      funext x
      show a⁻¹ * (a * x + b) + -(a⁻¹ * b) = x
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
      ring
    rw [image_image, e, image_id]
  unfold poincareDist
  congr 1
  ext d
  constructor
  · rintro ⟨f, a', z, hf, ha', hz, hfa, hfz, rfl⟩
    refine ⟨fun ζ => a⁻¹ * f ζ + -(a⁻¹ * b), a', z, ?_, ha', hz, ?_, ?_, rfl⟩
    · have h := hconf a⁻¹ (-(a⁻¹ * b)) hai _ f hf
      rwa [hback] at h
    · show a⁻¹ * f a' + -(a⁻¹ * b) = p
      rw [hfa]
      field_simp
      ring
    · show a⁻¹ * f z + -(a⁻¹ * b) = w
      rw [hfz]
      field_simp
      ring
  · rintro ⟨f, a', z, hf, ha', hz, hfa, hfz, rfl⟩
    refine ⟨fun ζ => a * f ζ + b, a', z, hconf a b ha Ω f hf, ha', hz, ?_, ?_, rfl⟩
    · show a * f a' + b = a * p + b
      rw [hfa]
    · show a * f z + b = a * w + b
      rw [hfz]

/-- Helper for `cor:B-outer`: `Φ_q(w)` is natural under a similarity `A z = a z + b`, whose
Poincaré extension is `(W, ξ) ↦ (a W + b, |a| ξ)`. -/
theorem s08_mb_horoPhi_aff {Ω : Set ℂ} (hΩ : ∃ f, IsConformalOnto f unitDisc Ω) {a b : ℂ}
    (ha : a ≠ 0) (q : ℂ × ℝ) (hq : 0 < q.2) {w : ℂ} (hw : w ∈ Ω) :
    horoPhi ((fun z => a * z + b) '' Ω) (a * q.1 + b, ‖a‖ * q.2) (a * w + b) = horoPhi Ω q w := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hq0 : q.2 ≠ 0 := hq.ne'
  have hl := (subsec_poincare_natural_affine hΩ (b := b) ha hw).1
  unfold horoPhi
  dsimp only
  rw [show a * q.1 + b - (a * w + b) = a * (q.1 - w) by ring, norm_mul, ← hl]
  field_simp

/-- Helper for `cor:B-outer`: under a similarity `A z = a z + b` the transported label
`A ∘ lab ∘ T⁻¹` (`T` the Poincaré extension of `A`) is a label of `A(Ω)`, and
`K_V` is natural: `K_V^{A(Ω), A(Ω*)}(A p) = K_V^{Ω, Ω*}(p)`. -/
theorem s08_mb_KV_aff {Ω Ωs : Set ℂ} (hΩ : ∃ f, IsConformalOnto f unitDisc Ω)
    (hΩs : ∃ f, IsConformalOnto f unitDisc Ωs) {a b : ℂ} (ha : a ≠ 0) {lab : ℂ × ℝ → ℂ}
    (hlab : IsLabel Ω lab) :
    IsLabel ((fun z => a * z + b) '' Ω) (fun q => a * lab ((q.1 - b) / a, q.2 / ‖a‖) + b) ∧
      ∀ p : ℂ, KV ((fun z => a * z + b) '' Ω) ((fun z => a * z + b) '' Ωs)
          (fun q => a * lab ((q.1 - b) / a, q.2 / ‖a‖) + b) (a * p + b) = KV Ω Ωs lab p := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hna' : ‖a‖ ≠ 0 := hna.ne'
  have hT := s09_affExt_meas a b ha
  have hTi : ∀ q : ℂ × ℝ, ((a * q.1 + b - b) / a, ‖a‖ * q.2 / ‖a‖) = q := fun q => by
    ext
    · show (a * q.1 + b - b) / a = q.1
      field_simp
      ring
    · show ‖a‖ * q.2 / ‖a‖ = q.2
      field_simp
  refine ⟨⟨?_, fun q hq => ?_⟩, fun p => ?_⟩
  · have h1 : Measurable fun q : ℂ × ℝ => ((q.1 - b) / a, q.2 / ‖a‖) := by fun_prop
    exact (measurable_const.mul (hlab.1.comp h1)).add_const b
  · obtain ⟨q₀, hq₀⟩ : ∃ q₀ : ℂ × ℝ, q₀ = ((q.1 - b) / a, q.2 / ‖a‖) := ⟨_, rfl⟩
    have hqT : q = (a * q₀.1 + b, ‖a‖ * q₀.2) := by
      rw [hq₀]
      ext
      · show q.1 = a * ((q.1 - b) / a) + b
        field_simp
        ring
      · show q.2 = ‖a‖ * (q.2 / ‖a‖)
        field_simp
    show a * lab ((q.1 - b) / a, q.2 / ‖a‖) + b ∈ _ ∧ ∀ w ∈ _,
      horoPhi _ q (a * lab ((q.1 - b) / a, q.2 / ‖a‖) + b) ≤ horoPhi _ q w
    rw [← hq₀]
    obtain ⟨hqU, hqH⟩ := hq
    subst hqT
    have hq0U : q₀ ∈ UHS := by
      have h : 0 < ‖a‖ * q₀.2 := hqU
      exact pos_of_mul_pos_right h hna.le
    have hq0H : q₀ ∉ horoUnion Ω := by
      rw [← s09_horoUnion_aff Ω hΩ a b ha]
      exact hqH
    obtain ⟨hmem, hmin⟩ := hlab.2 q₀ ⟨hq0U, hq0H⟩
    refine ⟨mem_image_of_mem _ hmem, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    rw [s08_mb_horoPhi_aff hΩ ha q₀ hq0U hmem, s08_mb_horoPhi_aff hΩ ha q₀ hq0U hw]
    exact hmin w hw
  · have hgap : (fun q : ℂ × ℝ => (a * q.1 + b, ‖a‖ * q.2)) ⁻¹'
        gap ((fun z => a * z + b) '' Ω) ((fun z => a * z + b) '' Ωs) = gap Ω Ωs := by
      unfold gap
      rw [preimage_sdiff, preimage_union, s09_affExt_UHS a b ha, s09_horoUnion_aff Ω hΩ a b ha,
        s09_horoUnion_aff Ωs hΩs a b ha]
    unfold KV
    conv_lhs => rw [← s09_hvol_map_aff a b ha, hT.restrict_map, hT.lintegral_map, hgap]
    refine lintegral_congr fun q => ?_
    show ENNReal.ofReal (intrKernel _ (a * p + b)
        (a * lab ((a * q.1 + b - b) / a, ‖a‖ * q.2 / ‖a‖) + b)) = _
    rw [hTi q]
    unfold intrKernel
    rw [s08_mb_pdist_aff Ω ha p (lab q)]

/-- Helper for `cor:B-outer`: with `d = x₀ - c`, `invAt (invAt c x₀) ∘ invAt c ∘ (invAt x₀)⁻¹` is
`u ↦ -d² u - d`, including the points `u = 0` (`∞ ↦ 0` under `invAt x₀`, `invAt c`) and
`u = invAt x₀ c` (`c ↦ ∞`). -/
theorem s08_mb_compose {x₀ c : ℂ} (hd : x₀ ≠ c) :
    (∀ w : ℂ, w ≠ x₀ → w ≠ c →
        -(x₀ - c) ^ 2 * invAt x₀ w + -(x₀ - c) = invAt (invAt c x₀) (invAt c w)) ∧
      -(x₀ - c) ^ 2 * 0 + -(x₀ - c) = invAt (invAt c x₀) 0 ∧
      -(x₀ - c) ^ 2 * invAt x₀ c + -(x₀ - c) = 0 := by
  have hd' : x₀ - c ≠ 0 := sub_ne_zero.mpr hd
  refine ⟨fun w hw0 hwc => ?_, ?_, ?_⟩
  · have h1 : w - x₀ ≠ 0 := sub_ne_zero.mpr hw0
    have h2 : w - c ≠ 0 := sub_ne_zero.mpr hwc
    have h3 : x₀ - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw0)
    unfold invAt
    rw [show (w - c)⁻¹ - (x₀ - c)⁻¹ = (x₀ - w) / ((w - c) * (x₀ - c)) by field_simp; ring,
      inv_div]
    field_simp
    ring
  · unfold invAt
    rw [zero_sub, inv_neg, inv_inv, mul_zero, zero_add]
  · have h1 : c - x₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hd)
    unfold invAt
    rw [show c - x₀ = -(x₀ - c) by ring]
    field_simp
    ring

/-- Helper for `cor:B-outer`: the similarity `A u = -d² u - d` maps the transported pair of `Γ`
(sides exchanged) onto the transported pair of `τ(Γ)`, and `x₁ = invAt c x₀` lies on `τ(Γ)`. -/
theorem s08_mb_sets {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K) {x₀ : ℂ}
    (hx₀ : x₀ ∈ curveOf Ω Ωs) {c : ℂ} (hc : c ∈ Ω) :
    (fun z => -(x₀ - c) ^ 2 * z + -(x₀ - c)) '' invPairΩs Ωs x₀ =
        invPairΩ (invPairΩs Ωs c) (invAt c x₀) ∧
      (fun z => -(x₀ - c) ^ 2 * z + -(x₀ - c)) '' invPairΩ Ω x₀ =
        invPairΩs (invAt c '' (Ω \ {c})) (invAt c x₀) ∧
      invAt c x₀ ∈ curveOf (invPairΩs Ωs c) (invAt c '' (Ω \ {c})) := by
  have hdisj : ∀ w ∈ Ω, w ∉ Ωs := by
    obtain ⟨F, hF, -, h1, h2⟩ := hΓ
    intro w hw hws
    rw [← h1] at hw
    rw [← h2] at hws
    obtain ⟨u, hu, rfl⟩ := hw
    obtain ⟨v, hv, hvu⟩ := hws
    have he : v = u := hF.2.2.1.2.1 (mem_univ _) (mem_univ _) hvu
    have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
    have hv1 : 1 < ‖v‖ := hv
    rw [he] at hv1
    linarith
  simp only [curveOf, mem_compl_iff, mem_union, not_or] at hx₀
  have hxc : x₀ ≠ c := fun h => hx₀.1 (h ▸ hc)
  obtain ⟨hA, hA0, hAc⟩ := s08_mb_compose hxc
  have e1 : ∀ w ∈ Ωs, -(x₀ - c) ^ 2 * invAt x₀ w + -(x₀ - c) = invAt (invAt c x₀) (invAt c w) :=
    fun w hw => hA w (fun h => hx₀.2 (h ▸ hw)) (fun h => hdisj c hc (h ▸ hw))
  have e2 : ∀ w ∈ Ω, w ≠ c →
      -(x₀ - c) ^ 2 * invAt x₀ w + -(x₀ - c) = invAt (invAt c x₀) (invAt c w) :=
    fun w hw hwc => hA w (fun h => hx₀.1 (h ▸ hw)) hwc
  have hinj : ∀ w : ℂ, invAt c w = invAt c x₀ → w = x₀ := fun w h => by
    unfold invAt at h
    have := inv_injective h
    linear_combination this
  have hx1 : invAt c x₀ ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hxc)
  refine ⟨?_, ?_, ?_⟩
  · unfold invPairΩs invPairΩ
    ext u
    simp only [mem_image, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨v, ⟨w, hw, rfl⟩ | rfl, rfl⟩
      · exact ⟨invAt c w, Or.inl ⟨w, hw, rfl⟩, (e1 w hw).symm⟩
      · exact ⟨0, Or.inr rfl, hA0.symm⟩
    · rintro ⟨y, ⟨w, hw, rfl⟩ | rfl, rfl⟩
      · exact ⟨invAt x₀ w, Or.inl ⟨w, hw, rfl⟩, e1 w hw⟩
      · exact ⟨0, Or.inr rfl, hA0⟩
  · unfold invPairΩs invPairΩ
    ext u
    simp only [mem_image, mem_union, mem_singleton_iff, Set.mem_sdiff]
    constructor
    · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
      by_cases hwc : w = c
      · subst hwc
        exact Or.inr hAc
      · exact Or.inl ⟨invAt c w, ⟨w, ⟨hw, hwc⟩, rfl⟩, (e2 w hw hwc).symm⟩
    · rintro (⟨y, ⟨w, ⟨hw, hwc⟩, rfl⟩, rfl⟩ | rfl)
      · exact ⟨invAt x₀ w, ⟨w, hw, rfl⟩, e2 w hw hwc⟩
      · exact ⟨invAt x₀ c, ⟨c, hc, rfl⟩, hAc⟩
  · unfold curveOf invPairΩs
    rw [mem_compl_iff, mem_union, mem_union, not_or, not_or]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro ⟨w, hw, h⟩
      exact hx₀.2 (hinj w h ▸ hw)
    · intro h
      exact hx1 (mem_singleton_iff.mp h)
    · rintro ⟨w, ⟨hw, -⟩, h⟩
      exact hx₀.1 (hinj w h ▸ hw)

/-- Helper for `cor:B-outer`: for `a ∈ 𝔻` there is a Möbius involution `σ z = a + k (z - a)⁻¹`
(`σ(∞) = a`) exchanging `𝔻 ∖ {a}` and `𝔻*` (`k = a(|a|² - 1)/ā`, and `k = 1` for `a = 0`). -/
theorem s08_mb_sigma {a : ℂ} (ha : a ∈ unitDisc) :
    ∃ k : ℂ, k ≠ 0 ∧ ∀ z : ℂ, z ≠ a →
      (‖a + k * (z - a)⁻¹‖ < 1 ↔ 1 < ‖z‖) ∧ (1 < ‖a + k * (z - a)⁻¹‖ ↔ ‖z‖ < 1) := by
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  rcases eq_or_ne a 0 with rfl | ha0
  · refine ⟨1, one_ne_zero, fun z hz => ?_⟩
    have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    simp only [zero_add, sub_zero, one_mul, norm_inv]
    exact ⟨inv_lt_one₀ hz0, one_lt_inv₀ hz0⟩
  · refine ⟨a * ((‖a‖ ^ 2 - 1 : ℝ) : ℂ) / conj a, ?_, fun z hz => ?_⟩
    · refine div_ne_zero (mul_ne_zero ha0 ?_) ((map_ne_zero _).mpr ha0)
      have hn := norm_nonneg a
      exact_mod_cast (show ‖a‖ ^ 2 - 1 ≠ 0 by nlinarith)
    have hid := s09_cq_sigma_norm ha0 hz
    set s := a + a * ((‖a‖ ^ 2 - 1 : ℝ) : ℂ) / conj a * (z - a)⁻¹ with hs
    have hpos : 0 < ‖z - a‖ ^ 2 := by
      have := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
      positivity
    have hn := norm_nonneg a
    have hA : ‖a‖ ^ 2 - 1 < 0 := by nlinarith
    have hs0 := norm_nonneg s
    have hz0 := norm_nonneg z
    constructor
    · constructor
      · intro h
        by_contra h'
        have hn2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [not_lt.mp h']
        have hs2 : ‖s‖ ^ 2 < 1 := by nlinarith
        have p1 := mul_pos (sub_pos.mpr hs2) hpos
        have p2 := mul_nonneg_of_nonpos_of_nonpos hA.le (sub_nonpos.mpr hn2)
        nlinarith
      · intro h
        by_contra h'
        have hs2 : 1 ≤ ‖s‖ ^ 2 := by nlinarith [not_lt.mp h']
        have hn2 : 1 < ‖z‖ ^ 2 := by nlinarith
        have p1 := mul_nonneg (sub_nonneg.mpr hs2) hpos.le
        have p2 := mul_neg_of_neg_of_pos hA (sub_pos.mpr hn2)
        nlinarith
    · constructor
      · intro h
        by_contra h'
        have hn2 : 1 ≤ ‖z‖ ^ 2 := by nlinarith [not_lt.mp h']
        have hs2 : 1 < ‖s‖ ^ 2 := by nlinarith
        have p1 := mul_pos (sub_pos.mpr hs2) hpos
        have p2 := mul_nonpos_of_nonpos_of_nonneg hA.le (sub_nonneg.mpr hn2)
        nlinarith
      · intro h
        by_contra h'
        have hs2 : ‖s‖ ^ 2 ≤ 1 := by nlinarith [not_lt.mp h']
        have hn2 : ‖z‖ ^ 2 < 1 := by nlinarith
        have p1 := mul_nonneg (sub_nonneg.mpr hs2) hpos.le
        have p2 := mul_pos_of_neg_of_neg hA (sub_neg.mpr hn2)
        nlinarith

/-- Helper for `cor:B-outer`: inverting a bounded `K`-quasicircle at a point `c` of the bounded
component gives a bounded `K`-quasicircle with bounded component `τ(Ω*) ∪ {τ ∞}` and unbounded
component `τ(Ω ∖ {c})`, `τ = invAt c` (the conjugation of `s09_cq_inv_qc`, with `σ` from
`s08_mb_sigma` exchanging `F⁻¹ c` and `∞`). -/
theorem s08_mb_inner_qc {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K) {c : ℂ}
    (hc : c ∈ Ω) : IsBoundedKQuasicircle (invPairΩs Ωs c) (invAt c '' (Ω \ {c})) K := by
  obtain ⟨F, hF, hFs, h1, h2⟩ := hΓ
  obtain ⟨a, ha1, rfl⟩ : c ∈ F '' unitDisc := by
    rw [h1]
    exact hc
  have hFi : Function.Injective F := injOn_univ.mp hF.2.2.1.2.1
  obtain ⟨k, hk, hkn⟩ := s08_mb_sigma ha1
  have ha1' : ‖a‖ < 1 := mem_ball_zero_iff.mp ha1
  obtain ⟨σ, hσ⟩ : ∃ σ : ℂ → ℂ, σ = fun z => a + k * (z - a)⁻¹ := ⟨_, rfl⟩
  have hσa : σ a = a := by
    rw [hσ]
    simp
  have hσne : ∀ z, z ≠ a → σ z ≠ a := fun z hz h => by
    rw [hσ] at h
    simp only [add_eq_left, mul_eq_zero, inv_eq_zero, sub_eq_zero] at h
    exact h.elim hk hz
  have hσσ : ∀ z, σ (σ z) = z := fun z => by
    rcases eq_or_ne z a with rfl | hz
    · rw [hσa, hσa]
    · have hza : z - a ≠ 0 := sub_ne_zero.mpr hz
      rw [hσ]
      simp only [add_sub_cancel_left, mul_inv, inv_inv]
      field_simp
      ring
  have hσn : ∀ z, z ≠ a → (‖σ z‖ < 1 ↔ 1 < ‖z‖) ∧ (1 < ‖σ z‖ ↔ ‖z‖ < 1) := fun z hz => by
    rw [hσ]
    exact hkn z hz
  have himD : σ '' unitDisc = unitDiscExterior ∪ {a} := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rcases eq_or_ne z a with rfl | hza
      · rw [hσa]
        exact Or.inr rfl
      · exact Or.inl ((hσn z hza).2.2 (mem_ball_zero_iff.mp hz))
    · rintro w (hw | hw)
      · have hw1 : 1 < ‖w‖ := hw
        have hwa : w ≠ a := fun h => by rw [h] at hw1; linarith
        exact ⟨σ w, mem_ball_zero_iff.mpr ((hσn w hwa).1.2 hw1), hσσ w⟩
      · rw [mem_singleton_iff.mp hw]
        exact ⟨a, ha1, hσa⟩
  have himE : σ '' unitDiscExterior = unitDisc \ {a} := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have hz1 : 1 < ‖z‖ := hz
      have hza : z ≠ a := fun h => by rw [h] at hz1; linarith
      exact ⟨mem_ball_zero_iff.mpr ((hσn z hza).1.2 hz1), hσne z hza⟩
    · rintro w ⟨hw, hwa⟩
      have hwa' : w ≠ a := hwa
      exact ⟨σ w, (hσn w hwa').2.2 (mem_ball_zero_iff.mp hw), hσσ w⟩
  -- quasiconformality off `a`
  have hq1 := thm7_1_comp (tp_b1_M_isKQC a a hk) hF (subset_univ _)
  have hsub : (F ∘ fun z : ℂ => a + k * (z - a)⁻¹) '' {a}ᶜ ⊆ {F a}ᶜ := by
    rintro _ ⟨z, hz, rfl⟩ h
    have heq := hF.2.2.1.2.1 (mem_univ _) (mem_univ _) (mem_singleton_iff.mp h)
    have hz' : z ≠ a := hz
    exact hσne z hz' (by rw [hσ]; exact heq)
  have hq2 := thm7_1_comp hq1 (tp_b1_M_isKQC (F a) 0 one_ne_zero) hsub
  rw [one_mul, mul_one] at hq2
  -- homeomorphism of the plane (the `nxInvConj` trick of `tp_b1_conj_isHomeomorphOnto`)
  obtain ⟨e, he⟩ := t1_homeomorph hF hFs
  set e₁ : ℂ ≃ₜ ℂ := ((Homeomorph.mulLeft₀ k hk).trans (Homeomorph.addLeft a)).trans
    (e.trans (Homeomorph.subRight (e a))) with he₁
  have h0 : e₁ 0 = 0 := by simp [he₁]
  obtain ⟨E, hE⟩ := nxI1_exists_homeo e₁ h0
  obtain ⟨G, hG⟩ : ∃ G : ℂ ≃ₜ ℂ, G = (Homeomorph.subRight a).trans E := ⟨_, rfl⟩
  have hGz : ∀ z, G z = invAt (F a) (F (σ z)) := fun z => by
    rw [hG, hσ, ← he]
    simp [hE, nxInvConj, he₁, invAt]
  have hGf : (⇑G : ℂ → ℂ) = fun z : ℂ => 0 + 1 * ((F ∘ fun z : ℂ => a + k * (z - a)⁻¹) z - F a)⁻¹ := by
    funext z
    rw [hGz, hσ]
    simp [invAt]
  have hHom := nxI1_isHomeomorphOnto_of_homeomorph G
  refine ⟨G, b4_isKQC_univ_of_punctured hHom (by rw [hGf]; exact hq2), hHom.2.2.1, ?_, ?_⟩
  · rw [show (⇑G) '' unitDisc = invAt (F a) '' (F '' (σ '' unitDisc)) by
      rw [image_image, image_image]
      exact image_congr fun z _ => hGz z, himD, image_union, image_union, h2, image_singleton,
      image_singleton]
    unfold invPairΩs
    congr 2
    simp [invAt]
  · rw [show (⇑G) '' unitDiscExterior = invAt (F a) '' (F '' (σ '' unitDiscExterior)) by
      rw [image_image, image_image]
      exact image_congr fun z _ => hGz z, himE, image_sdiff hFi, h1, image_singleton]

/-- Helper for `cor:B-outer`: `ĝ = τ ∘ g ∘ I` (`I z = z⁻¹`, `ĝ 0 = 0`; removable since
`g(∞) = ∞`) is a conformal map of `𝔻` onto the bounded component `τ(Ω*) ∪ {τ ∞}` of `τ(Γ)`. -/
theorem s08_mb_ghat {Ωs : Set ℂ} {g : ℂ → ℂ} (hg : IsConformalOnto g unitDiscExterior Ωs)
    (hgInf : Tendsto g (cocompact ℂ) (cocompact ℂ)) {c : ℂ} (hc : c ∉ Ωs) :
    IsConformalOnto (Function.update (fun z => invAt c (g z⁻¹)) 0 0) unitDisc
      (invPairΩs Ωs c) := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hgE : ∀ b ∈ unitDiscExterior, g b ∈ Ωs := fun b hb => by
    rw [← hg.2.2]
    exact mem_image_of_mem g hb
  have hinvE : ∀ z ∈ unitDisc, z ≠ 0 → z⁻¹ ∈ unitDiscExterior := fun z hz hz0 => by
    show 1 < ‖z⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr hz0)).mpr (mem_ball_zero_iff.mp hz)
  have hne : ∀ b ∈ unitDiscExterior, g b - c ≠ 0 := fun b hb h =>
    hc (sub_eq_zero.mp h ▸ hgE b hb)
  have hupd : ∀ z, z ≠ 0 →
      Function.update (fun z => invAt c (g z⁻¹)) 0 0 z = invAt c (g z⁻¹) := fun z hz =>
    Function.update_of_ne hz _ _
  refine ⟨?_, ?_, ?_⟩
  · refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (isOpen_ball.mem_nhds (mem_ball_self one_pos))).mp ⟨?_, ?_⟩
    · have hd : DifferentiableOn ℂ (fun z => invAt c (g z⁻¹)) (unitDisc \ {0}) := by
        intro z hz
        have hz0 : z ≠ 0 := hz.2
        have hzE := hinvE z hz.1 hz0
        have hgz : DifferentiableAt ℂ g z⁻¹ := (hg.1 z⁻¹ hzE).differentiableAt (hEo.mem_nhds hzE)
        have h1 : DifferentiableAt ℂ (fun y : ℂ => (g y⁻¹ - c)⁻¹) z :=
          ((hgz.comp z (hasDerivAt_inv hz0).differentiableAt).sub_const c).inv (hne _ hzE)
        exact h1.differentiableWithinAt
      exact hd.congr fun z hz => hupd z hz.2
    · rw [continuousAt_update_same]
      have h1 : Tendsto (fun z : ℂ => g z⁻¹) (𝓝[≠] 0) (Bornology.cobounded ℂ) := by
        rw [Metric.cobounded_eq_cocompact]
        exact hgInf.comp (Metric.cobounded_eq_cocompact (α := ℂ) ▸ tendsto_inv₀_nhdsNE_zero)
      exact tendsto_inv₀_cobounded.comp ((tendsto_sub_const_cobounded c).comp h1)
  · intro x hx y hy h
    rcases eq_or_ne x 0 with rfl | hx0 <;> rcases eq_or_ne y 0 with rfl | hy0
    · rfl
    · rw [Function.update_self, hupd y hy0] at h
      exact absurd (inv_eq_zero.mp h.symm) (hne _ (hinvE y hy hy0))
    · rw [Function.update_self, hupd x hx0] at h
      exact absurd (inv_eq_zero.mp h) (hne _ (hinvE x hx hx0))
    · rw [hupd x hx0, hupd y hy0] at h
      have h' : g x⁻¹ = g y⁻¹ := by
        have := inv_injective h
        linear_combination this
      exact inv_injective (hg.2.1 (hinvE x hx hx0) (hinvE y hy hy0) h')
  · ext u
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases eq_or_ne z 0 with rfl | hz0
      · rw [Function.update_self]
        exact Or.inr rfl
      · rw [hupd z hz0]
        exact Or.inl ⟨g z⁻¹, hgE _ (hinvE z hz hz0), rfl⟩
    · rintro (⟨w, hw, rfl⟩ | hu)
      · rw [← hg.2.2] at hw
        obtain ⟨b, hb, rfl⟩ := hw
        have hb1 : 1 < ‖b‖ := hb
        have hb0 : b ≠ 0 := ne_zero_of_norm_ne_zero (by linarith)
        refine ⟨b⁻¹, ?_, ?_⟩
        · refine mem_ball_zero_iff.mpr ?_
          rw [norm_inv]
          exact inv_lt_one_of_one_lt₀ hb1
        · rw [hupd _ (inv_ne_zero hb0), inv_inv]
      · rw [mem_singleton_iff.mp hu]
        exact ⟨0, mem_ball_self one_pos, Function.update_self _ _ _⟩

/-- Helper for `cor:B-outer` (i): `sup_{Ω*} K_V^*` of `Γ` is `sup_{τ(Ω*)} K_V` of `τ(Γ)` (base point
`x₁ = invAt c x₀`), for a transported label. -/
theorem s08_outer_sup {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K) {x₀ : ℂ}
    (hx₀ : x₀ ∈ curveOf Ω Ωs) {c : ℂ} (hc : c ∈ Ω) {lab : ℂ × ℝ → ℂ}
    (hlab : IsLabel (invPairΩs Ωs x₀) lab) :
    ∃ lab' : ℂ × ℝ → ℂ, IsLabel (invPairΩ (invPairΩs Ωs c) (invAt c x₀)) lab' ∧
      (⨆ p ∈ invPairΩs Ωs x₀, KV (invPairΩs Ωs x₀) (invPairΩ Ω x₀) lab p) =
        (⨆ p ∈ invPairΩs Ωs c, KV (invPairΩ (invPairΩs Ωs c) (invAt c x₀))
          (invPairΩs (invAt c '' (Ω \ {c})) (invAt c x₀)) lab' (invAt (invAt c x₀) p)) := by
  have hxc : x₀ ≠ c := fun h => (Set.notMem_of_mem_compl hx₀) (Or.inl (h ▸ hc))
  have ha : -(x₀ - c) ^ 2 ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 (sub_ne_zero.mpr hxc))
  obtain ⟨hc1, hc2⟩ := s09_jordan_conformal _ _
    (s03_b0_jordanPair (s03_invPair_isKQuasiPair hΓ hx₀))
  obtain ⟨hL, hKV⟩ := s08_mb_KV_aff (b := -(x₀ - c)) hc2 hc1 ha hlab
  obtain ⟨hS1, hS2, -⟩ := s08_mb_sets hΓ hx₀ hc
  rw [hS1, hS2] at hKV
  rw [hS1] at hL
  refine ⟨_, hL, ?_⟩
  calc (⨆ p ∈ invPairΩs Ωs x₀, KV (invPairΩs Ωs x₀) (invPairΩ Ω x₀) lab p)
      = ⨆ p ∈ invPairΩs Ωs x₀, KV (invPairΩ (invPairΩs Ωs c) (invAt c x₀))
          (invPairΩs (invAt c '' (Ω \ {c})) (invAt c x₀))
          (fun q => -(x₀ - c) ^ 2 * lab ((q.1 - -(x₀ - c)) / -(x₀ - c) ^ 2,
            q.2 / ‖-(x₀ - c) ^ 2‖) + -(x₀ - c)) (-(x₀ - c) ^ 2 * p + -(x₀ - c)) :=
        iSup_congr fun p => iSup_congr fun _ => (hKV p).symm
    _ = ⨆ q ∈ (fun z => -(x₀ - c) ^ 2 * z + -(x₀ - c)) '' invPairΩs Ωs x₀,
          KV (invPairΩ (invPairΩs Ωs c) (invAt c x₀))
          (invPairΩs (invAt c '' (Ω \ {c})) (invAt c x₀))
          (fun q => -(x₀ - c) ^ 2 * lab ((q.1 - -(x₀ - c)) / -(x₀ - c) ^ 2,
            q.2 / ‖-(x₀ - c) ^ 2‖) + -(x₀ - c)) q :=
        iSup_image.symm
    _ = _ := by
        rw [hS1]
        exact iSup_image

/-- Helper for `cor:B-outer` (ii): the outer vanishing condition along `g` for `Γ` is the inner
vanishing condition `DiskBoundaryVanishing` along `ĝ` for `τ(Γ)`, for a transported label
(`ĝ(z) = τ(g(b))`, `b = z⁻¹`). -/
theorem s08_outer_vanish {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K) {g : ℂ → ℂ}
    (hg : IsConformalOnto g unitDiscExterior Ωs) {x₀ : ℂ} (hx₀ : x₀ ∈ curveOf Ω Ωs) {c : ℂ}
    (hc : c ∈ Ω) {lab : ℂ × ℝ → ℂ} (hlab : IsLabel (invPairΩs Ωs x₀) lab) :
    ∃ lab' : ℂ × ℝ → ℂ, IsLabel (invPairΩ (invPairΩs Ωs c) (invAt c x₀)) lab' ∧
      ((∀ ε : ℝ≥0∞, 0 < ε → ∃ r : ℝ, 1 < r ∧ ∀ b : ℂ, 1 < ‖b‖ → ‖b‖ < r →
          KV (invPairΩs Ωs x₀) (invPairΩ Ω x₀) lab (invAt x₀ (g b)) ≤ ε) ↔
        DiskBoundaryVanishing (fun z => KV (invPairΩ (invPairΩs Ωs c) (invAt c x₀))
          (invPairΩs (invAt c '' (Ω \ {c})) (invAt c x₀)) lab'
          (invAt (invAt c x₀) (Function.update (fun z => invAt c (g z⁻¹)) 0 0 z)))) := by
  have hx₀' := hx₀
  simp only [curveOf, mem_compl_iff, mem_union, not_or] at hx₀'
  have hxc : x₀ ≠ c := fun h => hx₀'.1 (h ▸ hc)
  have ha : -(x₀ - c) ^ 2 ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 (sub_ne_zero.mpr hxc))
  have hdisj : c ∉ Ωs := by
    obtain ⟨F, hF, -, h1, h2⟩ := hΓ
    intro hcs
    rw [← h1] at hc
    rw [← h2] at hcs
    obtain ⟨u, hu, rfl⟩ := hc
    obtain ⟨v, hv, hvu⟩ := hcs
    have he : v = u := hF.2.2.1.2.1 (mem_univ _) (mem_univ _) hvu
    have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
    have hv1 : 1 < ‖v‖ := hv
    rw [he] at hv1
    linarith
  have hgE : ∀ b ∈ unitDiscExterior, g b ∈ Ωs := fun b hb => by
    rw [← hg.2.2]
    exact mem_image_of_mem g hb
  obtain ⟨hc1, hc2⟩ := s09_jordan_conformal _ _
    (s03_b0_jordanPair (s03_invPair_isKQuasiPair hΓ hx₀))
  obtain ⟨hL, hKV⟩ := s08_mb_KV_aff (b := -(x₀ - c)) hc2 hc1 ha hlab
  obtain ⟨hS1, hS2, -⟩ := s08_mb_sets hΓ hx₀ hc
  obtain ⟨hA, -, -⟩ := s08_mb_compose hxc
  rw [hS1, hS2] at hKV
  rw [hS1] at hL
  refine ⟨_, hL, ?_⟩
  set G := Function.update (fun z => invAt c (g z⁻¹)) 0 0 with hG
  set V := fun z => KV (invPairΩ (invPairΩs Ωs c) (invAt c x₀))
    (invPairΩs (invAt c '' (Ω \ {c})) (invAt c x₀))
    (fun q => -(x₀ - c) ^ 2 * lab ((q.1 - -(x₀ - c)) / -(x₀ - c) ^ 2,
      q.2 / ‖-(x₀ - c) ^ 2‖) + -(x₀ - c)) (invAt (invAt c x₀) (G z)) with hV
  -- `ĝ(b⁻¹) = τ(g b)` and `invAt x₁ (τ w) = A (invAt x₀ w)`
  have hpt : ∀ b : ℂ, 1 < ‖b‖ →
      V b⁻¹ = KV (invPairΩs Ωs x₀) (invPairΩ Ω x₀) lab (invAt x₀ (g b)) := fun b hb => by
    have hb0 : b ≠ 0 := ne_zero_of_norm_ne_zero (by linarith)
    have hgb := hgE b hb
    have e1 : G b⁻¹ = invAt c (g b) := by
      rw [hG, Function.update_of_ne (inv_ne_zero hb0), inv_inv]
    rw [hV]
    dsimp only
    rw [e1, ← hA (g b) (fun h => hx₀'.2 (h ▸ hgb)) (fun h => hdisj (h ▸ hgb))]
    exact hKV _
  show (∀ ε : ℝ≥0∞, 0 < ε → ∃ r : ℝ, 1 < r ∧ ∀ b : ℂ, 1 < ‖b‖ → ‖b‖ < r →
      KV (invPairΩs Ωs x₀) (invPairΩ Ω x₀) lab (invAt x₀ (g b)) ≤ ε) ↔ DiskBoundaryVanishing V
  constructor
  · intro h ε hε
    obtain ⟨r, hr, hb⟩ := h ε hε
    have hr0 : 0 < r := by linarith
    refine ⟨r⁻¹, inv_lt_one_of_one_lt₀ hr, fun z hz1 hz2 => ?_⟩
    have hz0' : 0 < ‖z‖ := lt_trans (inv_pos.mpr hr0) hz1
    have hz0 : z ≠ 0 := norm_pos_iff.mp hz0'
    have hb1 : 1 < ‖z⁻¹‖ := by
      rw [norm_inv]
      exact (one_lt_inv₀ hz0').mpr hz2
    have hb2 : ‖z⁻¹‖ < r := by
      rw [norm_inv]
      exact (inv_lt_comm₀ hr0 hz0').mp hz1
    rw [← inv_inv z, hpt z⁻¹ hb1]
    exact hb z⁻¹ hb1 hb2
  · intro h ε hε
    obtain ⟨r', hr', hz⟩ := h ε hε
    set s := max r' (1 / 2) with hs
    have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hs1 : s < 1 := max_lt hr' (by norm_num)
    refine ⟨s⁻¹, (one_lt_inv₀ hs0).mpr hs1, fun b hb1 hb2 => ?_⟩
    have hb0' : 0 < ‖b‖ := by linarith
    rw [← hpt b hb1]
    refine hz b⁻¹ ?_ ?_
    · rw [norm_inv]
      exact lt_of_le_of_lt (le_max_left _ _) ((lt_inv_comm₀ hb0' hs0).mp hb2)
    · rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ hb1

/-- Theorem B (i), forward direction: `sup_{p ∈ Ω} K_V(p) < ∞` implies that `Γ` is a BMO
quasicircle (`sec08-thmB.tex:15–17`). -/
theorem s08_B_i_fwd (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K) (x₀ : ℂ)
    (hx₀ : x₀ ∈ curveOf Ω Ωs) (lab : ℂ × ℝ → ℂ) (hlab : IsLabel (invPairΩ Ω x₀) lab) :
    (⨆ p ∈ Ω, KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ p)) < ⊤ →
      IsBMOQuasicircle Ω Ωs := by
  -- `K_H ≤ K_H + K_* ≤ C(K) K_V` (Theorem A, lower bound), then Lemma 7.9 (i)
  intro h
  have hK : 1 ≤ K := by
    obtain ⟨F, hF, -⟩ := hΓ
    exact hF.2.1
  obtain ⟨C, hC⟩ := thm_lower K hK
  have hpair := s03_invPair_isKQuasiPair hΓ hx₀
  refine (lem_one_sided_i K Ω Ωs hΓ x₀ hx₀).mp ?_
  refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.coe_lt_top (r := C)) h)
  refine iSup₂_le fun p hp => ?_
  calc KH (invPairΩ Ω x₀) (invAt x₀ p)
      ≤ KH2 (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ p) := by
        show _ ≤ KH _ _ + Kst _ _ _ _
        exact le_self_add
    _ ≤ (C : ℝ≥0∞) * KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ p) :=
        hC _ _ hpair lab hlab _ (mem_image_of_mem _ hp)
    _ ≤ (C : ℝ≥0∞) * ⨆ p ∈ Ω, KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ p) := by
        gcongr
        exact le_iSup₂ (f := fun p (_ : p ∈ Ω) =>
          KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ p)) p hp

/-- Theorem B (ii), forward direction: `lim_{r↑1} sup_{r<|a|<1} K_V(f(a)) = 0` implies that `Γ` is
a VMO quasicircle (`sec08-thmB.tex:27–30`). -/
theorem s08_B_ii_fwd (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K) (f : ℂ → ℂ)
    (hf : IsConformalOnto f unitDisc Ω) (x₀ : ℂ) (hx₀ : x₀ ∈ curveOf Ω Ωs) (lab : ℂ × ℝ → ℂ)
    (hlab : IsLabel (invPairΩ Ω x₀) lab) :
    DiskBoundaryVanishing (fun a => KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ (f a))) →
      IsVMOQuasicircle Ω Ωs := by
  -- `K_H(f a) ≤ C(K) K_V(f a)` pointwise (Theorem A, lower bound), then Lemma 7.9 (ii)
  intro hV
  have hK : 1 ≤ K := by
    obtain ⟨F, hF, -⟩ := hΓ
    exact hF.2.1
  obtain ⟨C, hC⟩ := thm_lower K hK
  have hpair := s03_invPair_isKQuasiPair hΓ hx₀
  refine (lem_one_sided_ii K Ω Ωs hΓ f hf x₀ hx₀).mp ?_
  intro ε hε
  have hC1 : ((C : ℝ≥0∞) + 1) ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ENNReal.one_ne_top⟩
  obtain ⟨r, hr, hra⟩ := hV (ε / ((C : ℝ≥0∞) + 1)) (ENNReal.div_pos hε.ne' hC1)
  refine ⟨r, hr, fun a h1 h2 => ?_⟩
  have ha : a ∈ unitDisc := mem_ball_zero_iff.mpr h2
  have hfa : invAt x₀ (f a) ∈ invPairΩ Ω x₀ := by
    show invAt x₀ (f a) ∈ invAt x₀ '' Ω
    refine mem_image_of_mem _ ?_
    rw [← hf.2.2]
    exact mem_image_of_mem f ha
  calc KH (invPairΩ Ω x₀) (invAt x₀ (f a))
      ≤ KH2 (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ (f a)) := by
        show _ ≤ KH _ _ + Kst _ _ _ _
        exact le_self_add
    _ ≤ (C : ℝ≥0∞) * KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ (f a)) :=
        hC _ _ hpair lab hlab _ hfa
    _ ≤ ((C : ℝ≥0∞) + 1) * (ε / ((C : ℝ≥0∞) + 1)) :=
        mul_le_mul' le_self_add (hra a h1 h2)
    _ ≤ ε := ENNReal.mul_div_le

/-- Helper for `s07_opp_two_sided_vmo`: the two components of a bounded quasicircle are
disjoint. -/
theorem s08_ts_disj {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K) : Disjoint Ω Ωs := by
  obtain ⟨F, hF, -, h1, h2⟩ := hΓ
  rw [Set.disjoint_left]
  intro p hp hps
  rw [← h1] at hp
  rw [← h2] at hps
  obtain ⟨u, hu, rfl⟩ := hp
  obtain ⟨v, hv, hvu⟩ := hps
  have he : v = u := hF.2.2.1.2.1 (mem_univ _) (mem_univ _) hvu
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  have hv1 : 1 < ‖v‖ := hv
  rw [he] at hv1
  linarith

/-- Helper for `s07_opp_two_sided_vmo`: points of `∂𝔻` are limit points of `𝔻*`. -/
theorem s08_ts_neBot {ξ : ℂ} (hξ : ξ ∈ sphere (0 : ℂ) 1) : (𝓝[unitDiscExterior] ξ).NeBot := by
  have hE : unitDiscExterior = (closedBall (0 : ℂ) 1)ᶜ := by
    ext z
    show 1 < ‖z‖ ↔ z ∈ (closedBall (0 : ℂ) 1)ᶜ
    simp only [mem_compl_iff, mem_closedBall_zero_iff, not_le]
  refine mem_closure_iff_nhdsWithin_neBot.mp ?_
  rw [hE, closure_compl, interior_closedBall' (0 : ℂ) 1]
  simp only [mem_compl_iff, mem_ball_zero_iff, not_lt]
  exact (mem_sphere_zero_iff_norm.mp hξ).ge

/-- Helper for `s07_opp_two_sided_vmo`: on `∂𝔻`, `(ζ̄)⁻¹ = ζ`. -/
theorem s08_ts_conj_inv {ζ : ℂ} (hζ : ‖ζ‖ = 1) : (conj ζ)⁻¹ = ζ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [Complex.conj_mul', hζ]
  norm_num

/-- Helper for `s07_opp_two_sided_vmo`: `w ↦ 1/w` sends `𝔻` near `ζ ∈ ∂𝔻` into `𝔻*` near `1/ζ`. -/
theorem s08_ts_inv_in {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    Tendsto (fun w : ℂ => w⁻¹) (𝓝[unitDisc] ζ) (𝓝[unitDiscExterior] ζ⁻¹) := by
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hζ
    exact zero_ne_one hζ
  refine tendsto_nhdsWithin_iff.mpr ⟨((continuousAt_inv₀ hζ0).tendsto).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_ne.mem_nhds hζ0)] with w hw hw0
  show 1 < ‖w⁻¹‖
  rw [norm_inv]
  exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hw0, mem_ball_zero_iff.mp hw⟩

/-- Helper for `s07_opp_two_sided_vmo`: `w ↦ 1/w` sends `𝔻*` near `ζ ∈ ∂𝔻` into `𝔻` near `1/ζ`. -/
theorem s08_ts_inv_out {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    Tendsto (fun w : ℂ => w⁻¹) (𝓝[unitDiscExterior] ζ) (𝓝[unitDisc] ζ⁻¹) := by
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hζ
    exact zero_ne_one hζ
  refine tendsto_nhdsWithin_iff.mpr ⟨((continuousAt_inv₀ hζ0).tendsto).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw1 : 1 < ‖w‖ := hw
  show w⁻¹ ∈ ball (0 : ℂ) 1
  rw [mem_ball_zero_iff, norm_inv]
  exact inv_lt_one_of_one_lt₀ hw1

/-- Helper for `s07_opp_two_sided_vmo`: `M_{-b} ∘ M_b = id` on `𝔻` (`M_a = diskMobius 0 a`). -/
theorem s08_ts_mob_comp {b : ℂ} (hb : ‖b‖ < 1) {w : ℂ} (hw : ‖w‖ < 1) :
    diskMobius 0 (-b) (diskMobius 0 b w) = w := by
  have hlt : ‖conj b * w‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg b, norm_nonneg w]
  have hd : 1 - conj b * w ≠ 0 := by
    intro h
    have h' : conj b * w = 1 := (sub_eq_zero.mp h).symm
    rw [h', norm_one] at hlt
    exact lt_irrefl _ hlt
  have hbb : (1 : ℂ) - conj b * b ≠ 0 := by
    rw [Complex.conj_mul']
    intro h
    have h' : ((‖b‖ ^ 2 : ℝ) : ℂ) = 1 := by push_cast; linear_combination -h
    have h'' : ‖b‖ ^ 2 = 1 := by exact_mod_cast h'
    nlinarith [norm_nonneg b]
  have hX : (w - b) / (1 - conj b * w) + b = w * (1 - conj b * b) / (1 - conj b * w) := by
    rw [div_add' _ _ _ hd]
    congr 1
    ring
  have hY : 1 + conj b * ((w - b) / (1 - conj b * w)) = (1 - conj b * b) / (1 - conj b * w) := by
    rw [mul_div_assoc', add_div' _ _ _ hd]
    congr 1
    ring
  show exp (((0 : ℝ) : ℂ) * I) * ((exp (((0 : ℝ) : ℂ) * I) * ((w - b) / (1 - conj b * w)) - -b) /
    (1 - conj (-b) * (exp (((0 : ℝ) : ℂ) * I) * ((w - b) / (1 - conj b * w))))) = w
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, map_neg, neg_mul,
    sub_neg_eq_add]
  rw [hX, hY, div_div_div_cancel_right₀ hd, mul_div_assoc, div_self hbb, mul_one]

/-- Helper for `s07_opp_two_sided_vmo`: for a VMO quasicircle and `c ∈ Ω`, there is a Riemann map
`f₁ : 𝔻 → Ω` with `f₁ 0 = c` and `log f₁' ∈ VMOA`. -/
theorem s08_ts_norm {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K) {c : ℂ} (hc : c ∈ Ω)
    (hV : IsVMOQuasicircle Ω Ωs) :
    ∃ f₁ : ℂ → ℂ, IsConformalOnto f₁ unitDisc Ω ∧ f₁ 0 = c ∧ LogDerivVMOA f₁ := by
  obtain ⟨-, f, hf, hfV⟩ := hV
  rw [← hf.2.2] at hc
  obtain ⟨b, hbD, hbc⟩ := hc
  have hb : ‖b‖ < 1 := mem_ball_zero_iff.mp hbD
  have hb' : ‖-b‖ < 1 := by rwa [norm_neg]
  have hf₁ := s07b_comp_mob_conformal hf 0 hb'
  refine ⟨fun z => f (diskMobius 0 (-b) z), hf₁, ?_, ?_⟩
  · show f (exp (((0 : ℝ) : ℂ) * I) * ((0 - -b) / (1 - conj (-b) * 0))) = c
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, zero_sub, neg_neg,
      mul_zero, sub_zero, div_one]
    exact hbc
  · refine s07b_vmoa_of_mobius hΓ hf₁ 0 hb ?_
    have hCf := s02_sw_V_fwd hf hfV
    have heq : schwarzCarlesonMeasure (fun z => (fun z => f (diskMobius 0 (-b) z)) (diskMobius 0 b z)) =
        schwarzCarlesonMeasure f := by
      unfold schwarzCarlesonMeasure
      refine withDensity_congr_ae ?_
      filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet (ball (0 : ℂ) 1))] with z hz
      have hev : (fun z => (fun z => f (diskMobius 0 (-b) z)) (diskMobius 0 b z)) =ᶠ[𝓝[≠] z] f := by
        filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz)] with w hw
        show f (diskMobius 0 (-b) (diskMobius 0 b w)) = f w
        rw [s08_ts_mob_comp hb (mem_ball_zero_iff.mp hw)]
      rw [schwarzian_congr hev]
    rw [heq]
    exact hCf

/-- Helper for `s07_opp_two_sided_vmo`: if `f₁ : 𝔻 → Ω` is conformal with `f₁ 0 = c`, then
`w ↦ τ(f₁(1/w))`, `τ = invAt c`, maps `𝔻*` conformally onto `τ(Ω ∖ {c})`. -/
theorem s08_ts_gp_conf {Ω : Set ℂ} {f₁ : ℂ → ℂ} (hf₁ : IsConformalOnto f₁ unitDisc Ω) {c : ℂ}
    (hf₁0 : f₁ 0 = c) :
    IsConformalOnto (fun w => invAt c (f₁ w⁻¹)) unitDiscExterior (invAt c '' (Ω \ {c})) := by
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hinD : ∀ w ∈ unitDiscExterior, w⁻¹ ∈ unitDisc := fun w hw => by
    have hw1 : 1 < ‖w‖ := hw
    show w⁻¹ ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, norm_inv]
    exact inv_lt_one_of_one_lt₀ hw1
  have hne0 : ∀ w ∈ unitDiscExterior, w ≠ 0 := fun w hw h => by
    have hw1 : 1 < ‖w‖ := hw
    rw [h, norm_zero] at hw1
    linarith
  have hnec : ∀ w ∈ unitDiscExterior, f₁ w⁻¹ ≠ c := fun w hw h => by
    rw [← hf₁0] at h
    exact inv_ne_zero (hne0 w hw) (hf₁.2.1 (hinD w hw) h0D h)
  refine ⟨fun w hw => ?_, fun w hw w' hw' h => ?_, ?_⟩
  · have hd : DifferentiableAt ℂ f₁ w⁻¹ :=
      (hf₁.1 _ (hinD w hw)).differentiableAt (isOpen_ball.mem_nhds (hinD w hw))
    have h2 : DifferentiableAt ℂ (fun w => (f₁ w⁻¹ - c)⁻¹) w :=
      ((hd.comp w (differentiableAt_inv (hne0 w hw))).sub_const c).inv
        (sub_ne_zero.mpr (hnec w hw))
    exact h2.differentiableWithinAt
  · have h' : (f₁ w⁻¹ - c)⁻¹ = (f₁ w'⁻¹ - c)⁻¹ := h
    have h2 : f₁ w⁻¹ = f₁ w'⁻¹ := by
      have := inv_inj.mp h'
      linear_combination this
    exact inv_inj.mp (hf₁.2.1 (hinD w hw) (hinD w' hw') h2)
  · ext p
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨f₁ w⁻¹, ⟨?_, hnec w hw⟩, rfl⟩
      rw [← hf₁.2.2]
      exact mem_image_of_mem f₁ (hinD w hw)
    · rintro ⟨q, ⟨hqΩ, hqc⟩, rfl⟩
      rw [← hf₁.2.2] at hqΩ
      obtain ⟨u, hu, rfl⟩ := hqΩ
      have hu0 : u ≠ 0 := fun h => hqc (by rw [h, hf₁0]; rfl)
      refine ⟨u⁻¹, ?_, ?_⟩
      · show 1 < ‖u⁻¹‖
        rw [norm_inv]
        exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hu0, mem_ball_zero_iff.mp hu⟩
      · show invAt c (f₁ u⁻¹⁻¹) = invAt c (f₁ u)
        rw [inv_inv]

/-- Helper for `s07_opp_two_sided_vmo`: `w ↦ τ(f₁(1/w))` sends `∞` to `∞`. -/
theorem s08_ts_gp_inf {Ω : Set ℂ} {f₁ : ℂ → ℂ} (hf₁ : IsConformalOnto f₁ unitDisc Ω) {c : ℂ}
    (hf₁0 : f₁ 0 = c) :
    Tendsto (fun w => invAt c (f₁ w⁻¹)) (cocompact ℂ) (cocompact ℂ) := by
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have h1 : Tendsto (fun w : ℂ => w⁻¹) (cocompact ℂ) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_cobounded
    · filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with w hw
      exact inv_ne_zero hw
  have hc0 : ContinuousAt f₁ 0 :=
    ((hf₁.1 0 h0D).differentiableAt (isOpen_ball.mem_nhds h0D)).continuousAt
  have h2 : Tendsto (fun u : ℂ => f₁ u - c) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun u => f₁ u - c) (𝓝 0) (𝓝 (f₁ 0 - c)) := hc0.tendsto.sub_const c
      rw [hf₁0, sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_ball.mem_nhds h0D)] with u hu hD
      intro h
      have h' : f₁ u = f₁ 0 := by rw [hf₁0]; exact sub_eq_zero.mp h
      exact hu (hf₁.2.1 hD h0D h')
  have h3 : Tendsto (fun v : ℂ => v⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_nhdsNE_zero
  exact h3.comp (h2.comp h1)

/-- Helper for `s07_opp_two_sided_vmo` (`sec07-transfer.tex:486–497`): the welding of the inverted
curve `τ(Γ)`, `τ = invAt c`, for the pair `(ĝ, ĝ*)`, `ĝ(w) = outerPt g c (w̄) = τ(g(1/w))`,
`ĝ*(w) = τ(f₁(1/w))` (`f₁ 0 = c`), is `ĥ = c₀ ∘ h₁⁻¹ ∘ c₀`, `h₁` the welding of `(f₁, g)`. -/
theorem s08_ts_weld {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K) {c : ℂ} (hc : c ∈ Ω)
    {g : ℂ → ℂ} (hg : IsConformalOnto g unitDiscExterior Ωs)
    (hgInf : Tendsto g (cocompact ℂ) (cocompact ℂ)) {f₁ : ℂ → ℂ}
    (hf₁ : IsConformalOnto f₁ unitDisc Ω) (hf₁0 : f₁ 0 = c) {h₁ hinv : ℂ → ℂ}
    (hw₁ : IsDiskWelding Ω Ωs f₁ g h₁)
    (hinvP : ∀ ζ ∈ sphere (0 : ℂ) 1, hinv ζ ∈ sphere (0 : ℂ) 1 ∧ h₁ (hinv ζ) = ζ ∧ hinv (h₁ ζ) = ζ) :
    IsDiskWelding (invPairΩs Ωs c) (invAt c '' (Ω \ {c})) (fun w => outerPt g c (conj w))
      (fun w => invAt c (f₁ w⁻¹)) (fun z => conj (hinv (conj z))) := by
  have hdisj := s08_ts_disj hΓ
  have hcs : c ∉ Ωs := Set.disjoint_left.mp hdisj hc
  have hΩo : IsOpen Ω := hf₁.isOpen isOpen_ball
  have hcl : c ∉ closure Ωs := Set.disjoint_left.mp (hdisj.closure_right hΩo) hc
  have hsc : ∀ ζ ∈ sphere (0 : ℂ) 1, conj ζ ∈ sphere (0 : ℂ) 1 := fun ζ hζ => by
    rw [mem_sphere_zero_iff_norm, Complex.norm_conj]
    exact mem_sphere_zero_iff_norm.mp hζ
  refine ⟨s07_outer_conformal hg hgInf hcs, s08_ts_gp_conf hf₁ hf₁0, s08_ts_gp_inf hf₁ hf₁0,
    fun ζ hζ => hsc _ (hinvP _ (hsc ζ hζ)).1, fun ζ hζ => ?_⟩
  have hξ := (hinvP _ (hsc ζ hζ)).1
  have hhξ := (hinvP _ (hsc ζ hζ)).2.1
  have hξ1 : ‖hinv (conj ζ)‖ = 1 := mem_sphere_zero_iff_norm.mp hξ
  have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
  obtain ⟨y, hfy, hgy⟩ := hw₁.2.2.2.2 _ hξ
  have := s08_ts_neBot hξ
  have hy : y ∈ closure Ωs := by
    refine mem_closure_of_tendsto hgy ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [← hg.2.2]
    exact mem_image_of_mem g hw
  have hyc : y ≠ c := fun h => hcl (h ▸ hy)
  have hτ : ContinuousAt (invAt c) y := by
    show ContinuousAt (fun z => (z - c)⁻¹) y
    exact (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hyc)
  refine ⟨invAt c y, ?_, ?_⟩
  · have hc1 : ‖conj (hinv (conj ζ))‖ = 1 := by rw [Complex.norm_conj, hξ1]
    have hin := s08_ts_inv_in hc1
    rw [s08_ts_conj_inv hξ1] at hin
    have hne : conj (hinv (conj ζ)) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hc1
      exact zero_ne_one hc1
    refine (hτ.tendsto.comp (hgy.comp hin)).congr' ?_
    filter_upwards [nhdsWithin_le_nhds (isOpen_ne.mem_nhds hne)] with w hw0
    exact (s07_outerPt_conj hw0).symm
  · have hout := s08_ts_inv_out hζ1
    have hζi : ζ⁻¹ = h₁ (hinv (conj ζ)) := by
      rw [hhξ]
      exact inv_eq_of_mul_eq_one_right (by rw [Complex.mul_conj', hζ1]; norm_num)
    rw [hζi] at hout
    exact hτ.tendsto.comp (hfy.comp hout)

/-- Residual wall **W-FKPH**, VMO part: for a VMO quasicircle `Γ` and `c ∈ Ω`,
`log ĝ' ∈ VMOA`. -/
theorem s07_opp_two_sided_vmo (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    {g : ℂ → ℂ} (hg : IsConformalOnto g unitDiscExterior Ωs)
    (hgInf : Tendsto g (cocompact ℂ) (cocompact ℂ)) {c : ℂ} (hc : c ∈ Ω)
    (hV : IsVMOQuasicircle Ω Ωs) :
    LogDerivVMOA (fun w => outerPt g c (conj w)) := by
  -- (V2) ⇒ (V5) for `Γ` (Riemann map normalized by `f₁ 0 = c`), the group and conjugation
  -- properties for `ĥ = c₀ ∘ h₁⁻¹ ∘ c₀`, then (V5) ⇒ (V2) for `τ(Γ)` and the pair `(ĝ, ĝ*)`
  obtain ⟨f₁, hf₁, hf₁0, hf₁V⟩ := s08_ts_norm hΓ hc hV
  obtain ⟨h₁, hw₁, hh₁⟩ := sec07_welding_exists K Ω Ωs hΓ f₁ g hf₁ hg hgInf
  have hS₁ := s07b_fkph_V5_fwd hΓ hw₁ hf₁V
  obtain ⟨hinv, hinvP⟩ := s07b_circle_inv hh₁
  have hSi := ss_circle_inv h₁ hinv hS₁ fun ζ hζ => ⟨(hinvP ζ hζ).1, (hinvP ζ hζ).2.1⟩
  exact s07b_V5_bwd (s08_mb_inner_qc hΓ hc) (s08_ts_weld hΓ hc hg hgInf hf₁ hf₁0 hw₁ hinvP)
    (ss_circle_conj hinv hSi)

/-- Proposition 7.10 (c), `prop:opposite` (`sec07-transfer.tex:458`), VMO part:
`ϖ m^* ∈ CM₀`. -/
theorem prop_opposite_c_vmo (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    (hnc : ¬ IsRoundCircle Ω Ωs) (g : ℂ → ℂ) (hg : IsConformalOnto g unitDiscExterior Ωs)
    (hgInf : Tendsto g (cocompact ℂ) (cocompact ℂ)) (hV : IsVMOQuasicircle Ω Ωs) :
    IsVanishingCarlesonDisk (varpiMeasure (farMass g)) := by
  have _hnc := hnc
  obtain ⟨c, hc, hcs⟩ : ∃ c, c ∈ Ω ∧ c ∉ Ωs := by
    obtain ⟨F, hF, -, h1, h2⟩ := hΓ
    refine ⟨F 0, ?_, ?_⟩
    · rw [← h1]
      exact mem_image_of_mem F (mem_ball_self one_pos)
    · intro hcs
      rw [← h2] at hcs
      obtain ⟨v, hv, hv0⟩ := hcs
      have he : v = 0 := hF.2.2.1.2.1 (mem_univ _) (mem_univ _) hv0
      have hv1 : 1 < ‖v‖ := hv
      rw [he, norm_zero] at hv1
      linarith
  exact s07_opp_mstar_vmo hg hgInf hcs (s07_opp_two_sided_vmo K Ω Ωs hΓ hg hgInf hc hV)

/-- Helper for `prop_opposite_d_vmo` (`SS ⊆ SQS`, `sec02-prelim.tex:589`): a strongly symmetric
circle map is strongly quasisymmetric, with modulus `δf ε = (ε/C)^{1/δ}` read off the power form of
`s07b_ssa_pow` on the lift (`s07_circleLen_exp_image` on both sides). -/
theorem s08_dv_ss_sqs {h : ℂ → ℂ} (hS : IsStronglySymmetric h) : IsStronglyQS h := by
  obtain ⟨H, u, hH, hHc, hper, hl, -⟩ := id hS
  obtain ⟨-, ⟨C, δ, hC, hδ, hP⟩, -, -⟩ := s07b_ssa_pow hS hHc hl
  have hexp : Continuous fun θ : ℝ => exp (θ * I) := by fun_prop
  have hHm : ∀ T : Set ℝ, MeasurableSet T → MeasurableSet (H '' T) := fun T hT =>
    hT.image_of_continuousOn_injOn hHc.continuousOn hH.injective.injOn
  refine ⟨fun ε => (ε / C) ^ δ⁻¹, ⟨H, hH, hHc, hper, hl⟩, fun ε hε =>
    ⟨Real.rpow_pos_of_pos (div_pos hε hC) _, fun a b hab hab2 E hEI hE hlen => ?_⟩⟩
  have hba : 0 < b - a := by linarith
  obtain ⟨S, hSdef⟩ : ∃ S, S = Icc a b ∩ (fun θ : ℝ => exp (θ * I)) ⁻¹' E := ⟨_, rfl⟩
  have hSm : MeasurableSet S := hSdef ▸ measurableSet_Icc.inter (hE.preimage hexp.measurable)
  have hSI : S ⊆ Icc a b := hSdef ▸ inter_subset_left
  have hES : E = (fun θ : ℝ => exp (θ * I)) '' S := by
    rw [hSdef]
    ext z
    constructor
    · intro hz
      obtain ⟨θ, hθ, rfl⟩ := hEI hz
      exact ⟨θ, ⟨hθ, hz⟩, rfl⟩
    · rintro ⟨θ, hθ, rfl⟩
      exact hθ.2
  have hIsub : Icc a b ⊆ Icc a (a + 2 * π) := fun θ hθ => ⟨hθ.1, by linarith [hθ.2]⟩
  have hHab2 : H b ≤ H a + 2 * π := by
    rw [← hper]
    exact hH.monotone (by linarith)
  have hHsub : ∀ T ⊆ Icc a b, H '' T ⊆ Icc (H a) (H a + 2 * π) := by
    rintro T hT _ ⟨θ, hθ, rfl⟩
    exact ⟨hH.monotone (hT hθ).1, (hH.monotone (hT hθ).2).trans hHab2⟩
  have himg : ∀ T : Set ℝ, h '' ((fun θ : ℝ => exp (θ * I)) '' T) =
      (fun θ : ℝ => exp (θ * I)) '' (H '' T) := by
    intro T
    rw [image_image, image_image]
    exact image_congr fun θ _ => hl θ
  have hI : circleLen (circleArc a b) = ENNReal.ofReal (b - a) := by
    rw [show circleArc a b = (fun θ : ℝ => exp (θ * I)) '' Icc a b from rfl,
      s07_circleLen_exp_image a _ measurableSet_Icc hIsub, Real.volume_Icc]
  have hEl : circleLen E = volume S := by
    rw [hES, s07_circleLen_exp_image a S hSm (hSI.trans hIsub)]
  have key : circleLen (h '' E) ≤ ENNReal.ofReal (C * ((circleLen E).toReal / (b - a)) ^ δ) *
      circleLen (h '' circleArc a b) := by
    rw [hEl, hES, show circleArc a b = (fun θ : ℝ => exp (θ * I)) '' Icc a b from rfl, himg, himg,
      s07_circleLen_exp_image (H a) _ (hHm S hSm) (hHsub S hSI),
      s07_circleLen_exp_image (H a) _ (hHm _ measurableSet_Icc) (hHsub _ subset_rfl)]
    exact hP a b hab hab2 S hSI hSm
  refine key.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  rw [hI] at hlen
  have hq : 0 ≤ (ε / C) ^ δ⁻¹ := Real.rpow_nonneg (div_pos hε hC).le _
  have ht : (circleLen E).toReal / (b - a) ≤ (ε / C) ^ δ⁻¹ := by
    rw [div_le_iff₀ hba]
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      hlen
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq, ENNReal.toReal_ofReal hba.le] at h1
  have h0 : 0 ≤ (circleLen E).toReal / (b - a) := div_nonneg ENNReal.toReal_nonneg hba.le
  calc C * ((circleLen E).toReal / (b - a)) ^ δ ≤ C * ((ε / C) ^ δ⁻¹) ^ δ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0 ht hδ.le) hC.le
    _ = ε := by
        rw [← Real.rpow_mul (div_pos hε hC).le, inv_mul_cancel₀ hδ.ne', Real.rpow_one]
        field_simp

/-- Helper for `prop_opposite_d_vmo`: boundary vanishing along one conformal map `f' : 𝔻 → Ω`
transfers to any other `f : 𝔻 → Ω` (`f'⁻¹ ∘ f` is proper: `f⁻¹ ∘ f'` maps the compact disc
`|z| ≤ ρ` into a compact subset of `𝔻`). -/
theorem s08_dv_reparam {Ω : Set ℂ} {f f' : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (hf' : IsConformalOnto f' unitDisc Ω) {F : ℂ → ℝ≥0∞}
    (hD : DiskBoundaryVanishing fun a => F (f' a)) : DiskBoundaryVanishing fun a => F (f a) := by
  intro ε hε
  obtain ⟨r', hr'1, hr'⟩ := hD ε hε
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = max r' 0 := ⟨_, rfl⟩
  have hρ1 : ρ < 1 := hρ ▸ max_lt hr'1 one_pos
  have hBD : closedBall (0 : ℂ) ρ ⊆ unitDisc := closedBall_subset_ball hρ1
  have hfs := hf.symm isOpen_ball
  have hK1 : IsCompact (f' '' closedBall (0 : ℂ) ρ) :=
    (isCompact_closedBall 0 ρ).image_of_continuousOn (hf'.1.continuousOn.mono hBD)
  have hK1Ω : f' '' closedBall (0 : ℂ) ρ ⊆ Ω := (image_mono hBD).trans hf'.2.2.subset
  have hK2 : IsCompact (Function.invFunOn f unitDisc '' (f' '' closedBall (0 : ℂ) ρ)) :=
    hK1.image_of_continuousOn (hfs.1.continuousOn.mono hK1Ω)
  have hK2D : Function.invFunOn f unitDisc '' (f' '' closedBall (0 : ℂ) ρ) ⊆ ball (0 : ℂ) 1 :=
    (image_mono hK1Ω).trans hfs.2.2.subset
  obtain ⟨r, hr1, hrsub⟩ := exists_lt_subset_ball hK2.isClosed hK2D
  refine ⟨r, hr1, fun a har ha1 => ?_⟩
  have haD : a ∈ unitDisc := mem_ball_zero_iff.mpr ha1
  obtain ⟨b, hbD, hb⟩ := hf'.2.2.symm.subset (hf.2.2.subset (mem_image_of_mem f haD))
  have hb1 : ‖b‖ < 1 := mem_ball_zero_iff.mp hbD
  have hρb : ρ < ‖b‖ := by
    by_contra hcon'
    have hcon : ‖b‖ ≤ ρ := not_lt.mp hcon'
    have hmem : a ∈ Function.invFunOn f unitDisc '' (f' '' closedBall (0 : ℂ) ρ) := by
      refine ⟨f' b, mem_image_of_mem f' (mem_closedBall_zero_iff.mpr hcon), ?_⟩
      rw [hb]
      exact hf.2.1.leftInvOn_invFunOn haD
    have := hrsub hmem
    rw [mem_ball_zero_iff] at this
    linarith
  show F (f a) ≤ ε
  rw [← hb]
  exact hr' b (lt_of_le_of_lt (hρ ▸ le_max_left _ _) hρb) hb1

/-- Helper for `prop_opposite_d_vmo`: a bounded `K`-quasicircle has an exterior Riemann map
`g : 𝔻* → Ω*` with `g(∞) = ∞`: `g(w) = c + 1/φ₁(1/w)`, `φ₁ : 𝔻 → τ(Ω*)` conformal with
`φ₁(0) = 0` (`τ = invAt c`, `c ∈ Ω`; `s08_mb_inner_qc`, `s07_exists_riemannMap`). -/
theorem s08_dv_ext {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K) {c : ℂ}
    (hc : c ∈ Ω) :
    ∃ g : ℂ → ℂ, IsConformalOnto g unitDiscExterior Ωs ∧ Tendsto g (cocompact ℂ) (cocompact ℂ) := by
  have hcs : c ∉ Ωs := fun h => Set.disjoint_left.mp (s08_ts_disj hΓ) hc h
  obtain ⟨φ, hφ⟩ := s07_exists_riemannMap (s08_mb_inner_qc hΓ hc)
  have h0 : (0 : ℂ) ∈ invPairΩs Ωs c := Or.inr rfl
  obtain ⟨b, hbD, hb0⟩ := hφ.2.2.symm.subset h0
  have hb : ‖b‖ < 1 := mem_ball_zero_iff.mp hbD
  have hb' : ‖-b‖ < 1 := by rwa [norm_neg]
  have hφ₁ := s07b_comp_mob_conformal hφ 0 hb'
  have hφ₁0 : (fun z => φ (diskMobius 0 (-b) z)) 0 = 0 := by
    show φ (exp (((0 : ℝ) : ℂ) * I) * ((0 - -b) / (1 - conj (-b) * 0))) = 0
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, zero_sub, neg_neg,
      mul_zero, sub_zero, div_one]
    exact hb0
  obtain ⟨G, hG, hGi⟩ : ∃ G : ℂ → ℂ,
      IsConformalOnto G unitDiscExterior (invAt 0 '' (invPairΩs Ωs c \ {0})) ∧
        Tendsto G (cocompact ℂ) (cocompact ℂ) :=
    ⟨_, s08_ts_gp_conf hφ₁ hφ₁0, s08_ts_gp_inf hφ₁ hφ₁0⟩
  have hinv2 : ∀ y : ℂ, c + invAt 0 (invAt c y) = y := by
    intro y
    show c + ((y - c)⁻¹ - 0)⁻¹ = y
    rw [sub_zero, inv_inv]
    ring
  have hset : (fun z => c + z) '' (invAt 0 '' (invPairΩs Ωs c \ {0})) = Ωs := by
    ext y
    constructor
    · rintro ⟨_, ⟨q, ⟨hq, hq0⟩, rfl⟩, rfl⟩
      have hq' : q ∈ invAt c '' Ωs ∪ {0} := hq
      rcases hq' with ⟨y', hy', rfl⟩ | hq'
      · show c + invAt 0 (invAt c y') ∈ Ωs
        rw [hinv2]
        exact hy'
      · exact absurd hq' hq0
    · intro hy
      have hyc : y ≠ c := fun h => hcs (h ▸ hy)
      refine ⟨invAt 0 (invAt c y), ⟨invAt c y, ⟨Or.inl ⟨y, hy, rfl⟩, ?_⟩, rfl⟩, hinv2 y⟩
      exact inv_ne_zero (sub_ne_zero.mpr hyc)
  refine ⟨fun w => c + G w, ⟨fun w hw => (hG.1 w hw).const_add c,
    fun w hw w' hw' h => hG.2.1 hw hw' (add_left_cancel h), ?_⟩, ?_⟩
  · rw [← hG.2.2, image_image] at hset
    exact hset
  · have hT : Tendsto (Homeomorph.addLeft c) (cocompact ℂ) (cocompact ℂ) :=
      (Homeomorph.addLeft c).map_cocompact.le
    exact hT.comp hGi

/-- Helper for `prop_opposite_d_vmo`: a function measurable on `𝔻` agrees there with a globally
measurable one (`0` off `𝔻`). -/
theorem s08_dv_meas {A : ℂ → ℂ} (hA : Measurable (unitDisc.restrict A)) :
    ∃ A' : ℂ → ℂ, Measurable A' ∧ ∀ z ∈ unitDisc, A' z = A z := by
  classical
  have hD : MeasurableSet unitDisc := measurableSet_ball
  refine ⟨fun z => if z ∈ unitDisc then A z else 0, ?_, fun z hz => if_pos hz⟩
  refine measurable_of_restrict_of_restrict_compl hD ?_ ?_
  · have hA' : Measurable (unitDisc.domRestrict A) := hA
    have h1 : (unitDisc.domRestrict fun z => if z ∈ unitDisc then A z else 0) =
        unitDisc.domRestrict A :=
      funext fun z => if_pos z.2
    rw [h1]
    exact hA'
  · have h2 : (unitDiscᶜ.domRestrict fun z => if z ∈ unitDisc then A z else 0) = fun _ => 0 :=
      funext fun z => if_neg z.2
    rw [h2]
    exact measurable_const

/-- Helper for `prop_opposite_d_vmo`: `m^*` has a measurable density on `𝔻` (the Schwarzian of the
analytic germ `u ↦ g(1/u)` at `z̄ ≠ 0` is `schwarzianHol`). -/
theorem s08_dv_farMass {Ωs : Set ℂ} {g : ℂ → ℂ} (hg : IsConformalOnto g unitDiscExterior Ωs) :
    ∃ b : ℂ → ℝ≥0∞, Measurable b ∧ farMass g = (volume.restrict unitDisc).withDensity b := by
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  refine ⟨fun z => ENNReal.ofReal (‖schwarzianHol (fun u => g u⁻¹) (conj z)‖ ^ 2 * varpi z ^ 2 / 4),
    ?_, ?_⟩
  · have hS := s02_pullback_measurable_schwarzianHol (fun u => g u⁻¹)
    have hc : Measurable fun z : ℂ => conj z := Complex.continuous_conj.measurable
    have hSc : Measurable fun z : ℂ => schwarzianHol (fun u => g u⁻¹) (conj z) := hS.comp hc
    unfold varpi
    fun_prop
  · unfold farMass
    refine withDensity_congr_ae ?_
    have h0 : ∀ᵐ w ∂(volume.restrict unitDisc), w ≠ 0 := by
      refine ae_restrict_of_ae ?_
      rw [ae_iff]
      simp
    filter_upwards [ae_restrict_mem hD, h0] with z hz hz0
    have hcz0 : conj z ≠ 0 := by simpa using hz0
    have hmem : (conj z)⁻¹ ∈ unitDiscExterior := by
      show 1 < ‖(conj z)⁻¹‖
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      rw [norm_inv, Complex.norm_conj]
      exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hz0, hz1⟩
    have hga : AnalyticAt ℂ g (conj z)⁻¹ := hg.1.analyticAt (hEo.mem_nhds hmem)
    have han : AnalyticAt ℂ (fun u => g u⁻¹) (conj z) := hga.comp (analyticAt_inv hcz0)
    show ENNReal.ofReal (‖schwarzian (fun u => g u⁻¹) (conj z)‖ ^ 2 * varpi z ^ 2 / 4) =
      ENNReal.ofReal (‖schwarzianHol (fun u => g u⁻¹) (conj z)‖ ^ 2 * varpi z ^ 2 / 4)
    rw [schwarzian_of_analyticAt han]

/-- Helper for `prop_opposite_d_vmo`: for measurable `A : 𝔻 → 𝔻`,
`𝒫_{A_* m^*}(a) = ∫ k_a(A z) dm^*(z)` (`m^*` lives on `𝔻`). -/
theorem s08_dv_poisson {g A : ℂ → ℂ} (hA : Measurable A) (hAD : MapsTo A unitDisc unitDisc)
    (a : ℂ) :
    poissonP ((farMass g).map A) a = ∫⁻ z, ENNReal.ofReal (diskKernel a (A z)) ∂farMass g := by
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hk : Measurable fun z => ENNReal.ofReal (diskKernel a z) := by
    unfold diskKernel varpi
    fun_prop
  have hac : farMass g ≪ volume.restrict unitDisc := withDensity_absolutelyContinuous _ _
  have hae : ∀ᵐ z ∂farMass g, z ∈ A ⁻¹' unitDisc :=
    hac.ae_le ((ae_restrict_mem hD).mono fun z hz => hAD hz)
  unfold poissonP
  rw [setLIntegral_map hD hk hA, Measure.restrict_eq_self_of_ae_mem hae]

/-- Proposition 7.10 (d), `prop:opposite` (`sec07-transfer.tex:460`), VMO part:
`lim_{r↑1} sup_{r<|a|<1} K_*(f(a)) = 0`. -/
theorem prop_opposite_d_vmo (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    (hnc : ¬ IsRoundCircle Ω Ωs) (f : ℂ → ℂ) (hf : IsConformalOnto f unitDisc Ω) (x₀ : ℂ)
    (hx₀ : x₀ ∈ curveOf Ω Ωs) (lab : ℂ × ℝ → ℂ) (hlab : IsLabel (invPairΩ Ω x₀) lab)
    (hV : IsVMOQuasicircle Ω Ωs) :
    DiskBoundaryVanishing
      (fun a => Kst (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ (f a))) := by
  -- (c) for the far side + qi-transfer (Prop. 7.8) along the far-side map `A` of Prop. 7.10 (a),
  -- for a VMOA Riemann map `f'` (the welding is SS by (V2) ⇒ (V5), hence SQS), then `f' ↝ f`
  obtain ⟨F, hF, -, h1, -⟩ := id hΓ
  have hK : 1 ≤ K := hF.2.1
  have hc : F 0 ∈ Ω := by
    rw [← h1]
    exact mem_image_of_mem F (mem_ball_self one_pos)
  obtain ⟨g, hg, hgInf⟩ := s08_dv_ext hΓ hc
  obtain ⟨-, f', hf', hf'V⟩ := id hV
  refine s08_dv_reparam
    (F := fun p => Kst (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ p)) hf hf' ?_
  obtain ⟨h, hw, -⟩ := sec07_welding_exists K Ω Ωs hΓ f' g hf' hg hgInf
  have hSQS := s08_dv_ss_sqs (s07b_fkph_V5_fwd hΓ hw hf'V)
  have hext := s07_weld_admitsExt hΓ hw
  obtain ⟨L, c', hLc⟩ := prop_opposite_a K hK
  obtain ⟨⟨A, hA⟩, hAall⟩ := hLc Ω Ωs hΓ hnc f' g h hw x₀ hx₀ lab hlab
  obtain ⟨A', hA'm, hA'eq⟩ := s08_dv_meas (hAall A hA).2.1
  have hA' : IsFarSideMap Ω Ωs f' g x₀ lab A' := by
    intro z hz
    rw [hA'eq z hz]
    exact hA z hz
  obtain ⟨hQI, -, hbd⟩ := hAall A' hA'
  obtain ⟨b, hb, hfm⟩ := s08_dv_farMass hg
  have hcv := prop_opposite_c_vmo K Ω Ωs hΓ hnc g hg hgInf hV
  rw [hfm] at hcv
  have hcm := (prop_qi_transfer_cm0 h (K * K) L c' hSQS hext A' hA'm hQI hbd b hb).mp hcv
  rw [← hfm] at hcm
  have hP := (lem_kernel_test_c _).mp hcm
  intro ε hε
  obtain ⟨r, hr1, hr⟩ := hP ε hε
  refine ⟨r, hr1, fun a har ha1 => ?_⟩
  have haD : a ∈ unitDisc := mem_ball_zero_iff.mpr ha1
  show Kst (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ (f' a)) ≤ ε
  rw [prop_opposite_b K Ω Ωs hΓ hnc f' g hf' hg hgInf x₀ hx₀ lab hlab A' hA' a haD,
    ← s08_dv_poisson hA'm hQI.1]
  exact hr a har ha1

/-- Helper for `s07_opp_two_sided_bmo` (BMO analogue of `s08_ts_norm`): for a BMO quasicircle and
`c ∈ Ω`, there is a Riemann map `f₁ : 𝔻 → Ω` with `f₁ 0 = c` and `log f₁' ∈ BMOA`. -/
theorem s08_tsb_norm {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K) {c : ℂ} (hc : c ∈ Ω)
    (hB : IsBMOQuasicircle Ω Ωs) :
    ∃ f₁ : ℂ → ℂ, IsConformalOnto f₁ unitDisc Ω ∧ f₁ 0 = c ∧ LogDerivBMOA f₁ := by
  obtain ⟨-, f, hf, hfB⟩ := hB
  rw [← hf.2.2] at hc
  obtain ⟨b, hbD, hbc⟩ := hc
  have hb : ‖b‖ < 1 := mem_ball_zero_iff.mp hbD
  have hb' : ‖-b‖ < 1 := by rwa [norm_neg]
  have hf₁ := s07b_comp_mob_conformal hf 0 hb'
  refine ⟨fun z => f (diskMobius 0 (-b) z), hf₁, ?_, ?_⟩
  · show f (exp (((0 : ℝ) : ℂ) * I) * ((0 - -b) / (1 - conj (-b) * 0))) = c
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, zero_sub, neg_neg,
      mul_zero, sub_zero, div_one]
    exact hbc
  · refine s07b_bmoa_of_mobius hΓ hf₁ 0 hb ?_
    have hCf := s02_sw_B_fwd hf hfB
    have heq : schwarzCarlesonMeasure (fun z => (fun z => f (diskMobius 0 (-b) z)) (diskMobius 0 b z)) =
        schwarzCarlesonMeasure f := by
      unfold schwarzCarlesonMeasure
      refine withDensity_congr_ae ?_
      filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet (ball (0 : ℂ) 1))] with z hz
      have hev : (fun z => (fun z => f (diskMobius 0 (-b) z)) (diskMobius 0 b z)) =ᶠ[𝓝[≠] z] f := by
        filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz)] with w hw
        show f (diskMobius 0 (-b) (diskMobius 0 b w)) = f w
        rw [s08_ts_mob_comp hb (mem_ball_zero_iff.mp hw)]
      rw [schwarzian_congr hev]
    rw [heq]
    exact hCf

/-- Residual wall **W-FKPH** (Proposition 7.10 (c), `sec07-transfer.tex:486–508`), BMO part: for a
BMO quasicircle `Γ` and `c ∈ Ω`, the bounded far-side chart `ĝ(w) = outerPt g c (w̄) = τ(g(1/w))`,
`τ = invAt c`, a conformal map of `𝔻` onto the bounded component of `τ(Γ)`, has `log ĝ' ∈ BMOA`
(paper: (B2) ⇒ (B5) for `Γ`, group and conjugation properties, (B5) ⇒ (B2) for `τ(Γ)`). -/
theorem s07_opp_two_sided_bmo (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    {g : ℂ → ℂ} (hg : IsConformalOnto g unitDiscExterior Ωs)
    (hgInf : Tendsto g (cocompact ℂ) (cocompact ℂ)) {c : ℂ} (hc : c ∈ Ω)
    (hB : IsBMOQuasicircle Ω Ωs) :
    LogDerivBMOA (fun w => outerPt g c (conj w)) := by
  -- (B2) ⇒ (B5) for `Γ` (Riemann map normalized by `f₁ 0 = c`), the group and conjugation
  -- properties for `ĥ = c₀ ∘ h₁⁻¹ ∘ c₀`, then (B5) ⇒ (B2) for `τ(Γ)` and the pair `(ĝ, ĝ*)`
  obtain ⟨f₁, hf₁, hf₁0, hf₁B⟩ := s08_tsb_norm hΓ hc hB
  obtain ⟨h₁, hw₁, hh₁⟩ := sec07_welding_exists K Ω Ωs hΓ f₁ g hf₁ hg hgInf
  have hS₁ := s07d_b2_b5 hΓ hw₁ hf₁B
  obtain ⟨hinv, hinvP⟩ := s07b_circle_inv hh₁
  have hSi := sqs_circle_inv h₁ hinv hS₁ fun ζ hζ => ⟨(hinvP ζ hζ).1, (hinvP ζ hζ).2.1⟩
  exact s07b_B5_bwd (s08_mb_inner_qc hΓ hc) (s08_ts_weld hΓ hc hg hgInf hf₁ hf₁0 hw₁ hinvP)
    (sqs_circle_conj hinv hSi)

/-- Proposition 7.10 (c), `prop:opposite` (`sec07-transfer.tex:457`), BMO part:
`ϖ m^* ∈ CM`. -/
theorem prop_opposite_c_bmo (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    (hnc : ¬ IsRoundCircle Ω Ωs) (g : ℂ → ℂ) (hg : IsConformalOnto g unitDiscExterior Ωs)
    (hgInf : Tendsto g (cocompact ℂ) (cocompact ℂ)) (hB : IsBMOQuasicircle Ω Ωs) :
    IsCarlesonDisk (varpiMeasure (farMass g)) := by
  have _hnc := hnc
  obtain ⟨c, hc, hcs⟩ : ∃ c, c ∈ Ω ∧ c ∉ Ωs := by
    obtain ⟨F, hF, -, h1, h2⟩ := hΓ
    refine ⟨F 0, ?_, ?_⟩
    · rw [← h1]
      exact mem_image_of_mem F (mem_ball_self one_pos)
    · intro hcs
      rw [← h2] at hcs
      obtain ⟨v, hv, hv0⟩ := hcs
      have he : v = 0 := hF.2.2.1.2.1 (mem_univ _) (mem_univ _) hv0
      have hv1 : 1 < ‖v‖ := hv
      rw [he, norm_zero] at hv1
      linarith
  exact s07_opp_mstar_bmo hg hgInf hcs (s07_opp_two_sided_bmo K Ω Ωs hΓ hg hgInf hc hB)

/-- Proposition 7.10 (d), `prop:opposite` (`sec07-transfer.tex:459`), BMO part:
`sup_Ω K_* < ∞`. -/
theorem prop_opposite_d_bmo (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    (hnc : ¬ IsRoundCircle Ω Ωs) (x₀ : ℂ) (hx₀ : x₀ ∈ curveOf Ω Ωs) (lab : ℂ × ℝ → ℂ)
    (hlab : IsLabel (invPairΩ Ω x₀) lab) (hB : IsBMOQuasicircle Ω Ωs) :
    (⨆ p ∈ Ω, Kst (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ p)) < ⊤ := by
  -- (c) for the far side + qi-transfer (Prop. 7.8) along the far-side map `A` of Prop. 7.10 (a),
  -- for a BMOA Riemann map `f'` (the welding is SQS by (B2) ⇒ (B5)), then Lemma 7.6 (b):
  -- `sup_𝔻 P[m] ≤ 80 ‖ϖ m‖_CM`, and `K_*(f'(a)) = P[A_* m^*](a)` (Prop. 7.10 (b))
  obtain ⟨F, hF, -, h1, -⟩ := id hΓ
  have hK : 1 ≤ K := hF.2.1
  have hc : F 0 ∈ Ω := by
    rw [← h1]
    exact mem_image_of_mem F (mem_ball_self one_pos)
  obtain ⟨g, hg, hgInf⟩ := s08_dv_ext hΓ hc
  obtain ⟨-, f', hf', hf'B⟩ := id hB
  obtain ⟨h, hw, -⟩ := sec07_welding_exists K Ω Ωs hΓ f' g hf' hg hgInf
  have hSQS := s07d_b2_b5 hΓ hw hf'B
  have hext := s07_weld_admitsExt hΓ hw
  obtain ⟨L, c', hLc⟩ := prop_opposite_a K hK
  obtain ⟨⟨A, hA⟩, hAall⟩ := hLc Ω Ωs hΓ hnc f' g h hw x₀ hx₀ lab hlab
  obtain ⟨A', hA'm, hA'eq⟩ := s08_dv_meas (hAall A hA).2.1
  have hA' : IsFarSideMap Ω Ωs f' g x₀ lab A' := by
    intro z hz
    rw [hA'eq z hz]
    exact hA z hz
  obtain ⟨hQI, -, hbd⟩ := hAall A' hA'
  obtain ⟨b, hb, hfm⟩ := s08_dv_farMass hg
  have hcb := prop_opposite_c_bmo K Ω Ωs hΓ hnc g hg hgInf hB
  rw [hfm] at hcb
  have hcm := (prop_qi_transfer_cm h (K * K) L c' hSQS hext A' hA'm hQI hbd b hb).mp hcb
  rw [← hfm] at hcm
  have hN := (s07_carlesonNorm_lt_top _).2 hcm
  have hPt : (⨆ a ∈ unitDisc, poissonP ((farMass g).map A') a) < ⊤ :=
    lt_of_le_of_lt (lem_kernel_test_b ((farMass g).map A')).2 (ENNReal.mul_lt_top (by simp) hN)
  refine lt_of_le_of_lt (iSup₂_le fun p hp => ?_) hPt
  rw [← hf'.2.2] at hp
  obtain ⟨a, haD, rfl⟩ := hp
  rw [prop_opposite_b K Ω Ωs hΓ hnc f' g hf' hg hgInf x₀ hx₀ lab hlab A' hA' a haD,
    ← s08_dv_poisson hA'm hQI.1]
  exact le_iSup₂ (f := fun a (_ : a ∈ unitDisc) => poissonP ((farMass g).map A') a) a haD

/-- Helper for `thm_B_ii`: boundary vanishing passes to `G ≤ C (F₁ + F₂)` on `𝔻`. -/
theorem s08_bii_comb {F₁ F₂ G : ℂ → ℝ≥0∞} (C : ℝ≥0) (h1 : DiskBoundaryVanishing F₁)
    (h2 : DiskBoundaryVanishing F₂) (hG : ∀ a : ℂ, ‖a‖ < 1 → G a ≤ C * (F₁ a + F₂ a)) :
    DiskBoundaryVanishing G := by
  intro ε hε
  have hC1 : (C : ℝ≥0∞) + 1 ≠ 0 := by simp
  have hC2 : 2 * ((C : ℝ≥0∞) + 1) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (by simp) ?_
    simp
  have hη : 0 < ε / (2 * ((C : ℝ≥0∞) + 1)) :=
    ENNReal.div_pos_iff.mpr ⟨hε.ne', hC2⟩
  obtain ⟨r₁, hr₁, h1'⟩ := h1 _ hη
  obtain ⟨r₂, hr₂, h2'⟩ := h2 _ hη
  refine ⟨max r₁ r₂, max_lt hr₁ hr₂, fun a har ha1 => ?_⟩
  have ha₁ : r₁ < ‖a‖ := lt_of_le_of_lt (le_max_left _ _) har
  have ha₂ : r₂ < ‖a‖ := lt_of_le_of_lt (le_max_right _ _) har
  calc G a ≤ C * (F₁ a + F₂ a) := hG a ha1
    _ ≤ C * (ε / (2 * ((C : ℝ≥0∞) + 1)) + ε / (2 * ((C : ℝ≥0∞) + 1))) := by
        gcongr
        · exact h1' a ha₁ ha1
        · exact h2' a ha₂ ha1
    _ ≤ (2 * ((C : ℝ≥0∞) + 1)) * (ε / (2 * ((C : ℝ≥0∞) + 1))) := by
        rw [← two_mul, ← mul_assoc, mul_comm (C : ℝ≥0∞) 2, mul_assoc, mul_assoc]
        gcongr
        exact le_self_add
    _ ≤ ε := ENNReal.mul_div_le

/-- Theorem B (i), `thm_B_i` (`sec01-intro.tex:209`, proof `sec08-thmB.tex:14`): for a bounded
`K`-quasicircle, every `x₀ ∈ Γ` and every label, `sup_{p ∈ Ω} K_V(p) < ∞` iff `Γ` is a BMO
quasicircle. -/
theorem thm_B_i (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K) (x₀ : ℂ)
    (hx₀ : x₀ ∈ curveOf Ω Ωs) (lab : ℂ × ℝ → ℂ) (hlab : IsLabel (invPairΩ Ω x₀) lab) :
    (⨆ p ∈ Ω, KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ p)) < ⊤ ↔
      IsBMOQuasicircle Ω Ωs := by
  -- (⇒) Theorem A lower bound + Lemma 7.9 (i) (`s08_B_i_fwd`); (⇐) `K_V ≤ C K_{H,2}`
  -- (Theorem A, upper bound) with `sup K_H < ∞` (Lemma 7.9 (i)) and `sup K_* < ∞` (Prop. 7.10 (d));
  -- for a round circle the transported pair is a line pair and `K_{H,2} = 0`
  have hK : 1 ≤ K := by
    obtain ⟨F, hF, -⟩ := hΓ
    exact hF.2.1
  refine ⟨s08_B_i_fwd K Ω Ωs hΓ x₀ hx₀ lab hlab, fun hB => ?_⟩
  obtain ⟨C, hC⟩ := thm_upper K hK
  have hQP := s03_invPair_isKQuasiPair hΓ hx₀
  have hp : ∀ p ∈ Ω, invAt x₀ p ∈ invPairΩ Ω x₀ := fun p hp => mem_image_of_mem _ hp
  have hKH := (lem_one_sided_i K Ω Ωs hΓ x₀ hx₀).mpr hB
  by_cases hnc : IsRoundCircle Ω Ωs
  · obtain ⟨h1, h2⟩ := s06_tl_line (s07_round_linePair hΓ hnc hx₀)
    refine lt_of_le_of_lt (iSup₂_le fun p hp' => ?_) ENNReal.zero_lt_top
    refine (hC _ _ hQP lab hlab _ (hp p hp')).trans ?_
    have h0 : KH2 (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ p) = 0 := by
      unfold KH2 KH Kst
      rw [h1, h2]
      simp
    rw [h0, mul_zero]
  · have hD := prop_opposite_d_bmo K Ω Ωs hΓ hnc x₀ hx₀ lab hlab hB
    refine lt_of_le_of_lt (iSup₂_le fun p hp' => ?_)
      (ENNReal.mul_lt_top (ENNReal.coe_lt_top (r := C)) (ENNReal.add_lt_top.2 ⟨hKH, hD⟩))
    refine (hC _ _ hQP lab hlab _ (hp p hp')).trans ?_
    gcongr
    show KH _ _ + Kst _ _ _ _ ≤ _
    gcongr
    · exact le_iSup₂ (f := fun p (_ : p ∈ Ω) => KH (invPairΩ Ω x₀) (invAt x₀ p)) p hp'
    · exact le_iSup₂ (f := fun p (_ : p ∈ Ω) =>
        Kst (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ p)) p hp'

/-- Theorem B (ii), `thm_B_ii` (`sec01-intro.tex:210`, proof `sec08-thmB.tex:25`): for every
conformal `f : 𝔻 → Ω`, `lim_{r↑1} sup_{r<|a|<1} K_V(f(a)) = 0` iff `Γ` is a VMO quasicircle. -/
theorem thm_B_ii (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K) (f : ℂ → ℂ)
    (hf : IsConformalOnto f unitDisc Ω) (x₀ : ℂ) (hx₀ : x₀ ∈ curveOf Ω Ωs) (lab : ℂ × ℝ → ℂ)
    (hlab : IsLabel (invPairΩ Ω x₀) lab) :
    DiskBoundaryVanishing (fun a => KV (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ (f a))) ↔
      IsVMOQuasicircle Ω Ωs := by
  -- (⇒) Theorem A lower bound + Lemma 7.9 (ii) (`s08_B_ii_fwd`); (⇐) `K_V ≤ C K_{H,2}`
  -- (Theorem A, upper bound) with `K_H ∘ f → 0` (Lemma 7.9 (ii)) and `K_* ∘ f → 0` (Prop. 7.10 (d));
  -- for a round circle the transported pair is a line pair and `K_{H,2} = 0`
  have hK : 1 ≤ K := by
    obtain ⟨F, hF, -⟩ := hΓ
    exact hF.2.1
  refine ⟨s08_B_ii_fwd K Ω Ωs hΓ f hf x₀ hx₀ lab hlab, fun hV => ?_⟩
  obtain ⟨C, hC⟩ := thm_upper K hK
  have hQP := s03_invPair_isKQuasiPair hΓ hx₀
  have hp : ∀ a : ℂ, ‖a‖ < 1 → invAt x₀ (f a) ∈ invPairΩ Ω x₀ := fun a ha =>
    mem_image_of_mem _ (hf.2.2.subset (mem_image_of_mem f (mem_ball_zero_iff.mpr ha)))
  have hKH := (lem_one_sided_ii K Ω Ωs hΓ f hf x₀ hx₀).mpr hV
  by_cases hnc : IsRoundCircle Ω Ωs
  · obtain ⟨h1, h2⟩ := s06_tl_line (s07_round_linePair hΓ hnc hx₀)
    intro ε _
    refine ⟨0, zero_lt_one, fun a _ ha1 => ?_⟩
    refine (hC _ _ hQP lab hlab _ (hp a ha1)).trans ?_
    have h0 : KH2 (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ (f a)) = 0 := by
      unfold KH2 KH Kst
      rw [h1, h2]
      simp
    rw [h0, mul_zero]
    exact zero_le
  · exact s08_bii_comb C hKH (prop_opposite_d_vmo K Ω Ωs hΓ hnc f hf x₀ hx₀ lab hlab hV)
      fun a ha => hC _ _ hQP lab hlab _ (hp a ha)

/-- Helper for `cor_B_outer_ii` (`sec08-thmB.tex:82–90`): for a Riemann map `f₀ : 𝔻 → Ω` and
`c = f₀(0)`, `τ(Γ)` (`τ = invAt c`) is a VMO quasicircle iff `Γ` is. (⇐) is `s07_opp_two_sided_vmo`
for `Γ`; (⇒) is `s07_opp_two_sided_vmo` for `τ(Γ)` at `0 ∈ τ(Ω*)` with the exterior map
`w ↦ τ(f₀(1/w))`, whose far-side chart is `f₀ - c`. -/
theorem s08_cbo_vmo_iff {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K) {g : ℂ → ℂ}
    (hg : IsConformalOnto g unitDiscExterior Ωs) (hgInf : Tendsto g (cocompact ℂ) (cocompact ℂ))
    {f₀ : ℂ → ℂ} (hf₀ : IsConformalOnto f₀ unitDisc Ω) :
    IsVMOQuasicircle (invPairΩs Ωs (f₀ 0)) (invAt (f₀ 0) '' (Ω \ {f₀ 0})) ↔
      IsVMOQuasicircle Ω Ωs := by
  have hc : f₀ 0 ∈ Ω := hf₀.2.2.subset (mem_image_of_mem f₀ (mem_ball_self one_pos))
  have hcs : f₀ 0 ∉ Ωs := fun h => Set.disjoint_left.mp (s08_ts_disj hΓ) hc h
  have hΓ' := s08_mb_inner_qc hΓ hc
  constructor
  · intro hVτ
    have hL := s07_opp_two_sided_vmo K _ _ hΓ' (s08_ts_gp_conf hf₀ rfl) (s08_ts_gp_inf hf₀ rfl)
      (show (0 : ℂ) ∈ invPairΩs Ωs (f₀ 0) from Or.inr rfl) hVτ
    have heq : (fun w => outerPt (fun w => invAt (f₀ 0) (f₀ w⁻¹)) 0 (conj w)) =
        fun w => f₀ w - f₀ 0 := by
      funext w
      rcases eq_or_ne w 0 with rfl | hw
      · simp [outerPt]
      · rw [s07_outerPt_conj hw]
        show ((f₀ w⁻¹⁻¹ - f₀ 0)⁻¹ - 0)⁻¹ = f₀ w - f₀ 0
        rw [inv_inv, sub_zero, inv_inv]
    have hd : deriv (fun w => f₀ w - f₀ 0) = deriv f₀ := by
      funext z
      simp
    rw [heq] at hL
    unfold LogDerivVMOA at hL
    rw [hd] at hL
    exact ⟨⟨K, hΓ⟩, f₀, hf₀, hL⟩
  · intro hV
    exact ⟨⟨K, hΓ'⟩, _, s07_outer_conformal hg hgInf hcs,
      s07_opp_two_sided_vmo K Ω Ωs hΓ hg hgInf hc hV⟩

/-- Helper for `cor_B_outer_i` (`sec08-thmB.tex:77–81`; BMO analogue of `s08_cbo_vmo_iff`): for a
Riemann map `f₀ : 𝔻 → Ω` and `c = f₀(0)`, `τ(Γ)` (`τ = invAt c`) is a BMO quasicircle iff `Γ` is.
(⇐) is `s07_opp_two_sided_bmo` for `Γ`; (⇒) is `s07_opp_two_sided_bmo` for `τ(Γ)` at
`0 ∈ τ(Ω*)` with the exterior map `w ↦ τ(f₀(1/w))`, whose far-side chart is `f₀ - c`. -/
theorem s08_cbo_bmo_iff {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K) {g : ℂ → ℂ}
    (hg : IsConformalOnto g unitDiscExterior Ωs) (hgInf : Tendsto g (cocompact ℂ) (cocompact ℂ))
    {f₀ : ℂ → ℂ} (hf₀ : IsConformalOnto f₀ unitDisc Ω) :
    IsBMOQuasicircle (invPairΩs Ωs (f₀ 0)) (invAt (f₀ 0) '' (Ω \ {f₀ 0})) ↔
      IsBMOQuasicircle Ω Ωs := by
  have hc : f₀ 0 ∈ Ω := hf₀.2.2.subset (mem_image_of_mem f₀ (mem_ball_self one_pos))
  have hcs : f₀ 0 ∉ Ωs := fun h => Set.disjoint_left.mp (s08_ts_disj hΓ) hc h
  have hΓ' := s08_mb_inner_qc hΓ hc
  constructor
  · intro hBτ
    have hL := s07_opp_two_sided_bmo K _ _ hΓ' (s08_ts_gp_conf hf₀ rfl) (s08_ts_gp_inf hf₀ rfl)
      (show (0 : ℂ) ∈ invPairΩs Ωs (f₀ 0) from Or.inr rfl) hBτ
    have heq : (fun w => outerPt (fun w => invAt (f₀ 0) (f₀ w⁻¹)) 0 (conj w)) =
        fun w => f₀ w - f₀ 0 := by
      funext w
      rcases eq_or_ne w 0 with rfl | hw
      · simp [outerPt]
      · rw [s07_outerPt_conj hw]
        show ((f₀ w⁻¹⁻¹ - f₀ 0)⁻¹ - 0)⁻¹ = f₀ w - f₀ 0
        rw [inv_inv, sub_zero, inv_inv]
    have hd : deriv (fun w => f₀ w - f₀ 0) = deriv f₀ := by
      funext z
      simp
    rw [heq] at hL
    unfold LogDerivBMOA at hL
    rw [hd] at hL
    exact ⟨⟨K, hΓ⟩, f₀, hf₀, hL⟩
  · intro hB
    exact ⟨⟨K, hΓ'⟩, _, s07_outer_conformal hg hgInf hcs,
      s07_opp_two_sided_bmo K Ω Ωs hΓ hg hgInf hc hB⟩

/-- Corollary 8.4 (i), `cor:B-outer` (`sec08-thmB.tex:77`): the gap volume based at points of
`Ω*` (labels in `Ω*`) is bounded iff `Γ` is a BMO quasicircle. -/
theorem cor_B_outer_i (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K) (x₀ : ℂ)
    (hx₀ : x₀ ∈ curveOf Ω Ωs) (lab : ℂ × ℝ → ℂ) (hlab : IsLabel (invPairΩs Ωs x₀) lab) :
    (⨆ p ∈ invPairΩs Ωs x₀, KV (invPairΩs Ωs x₀) (invPairΩ Ω x₀) lab p) < ⊤ ↔
      IsBMOQuasicircle Ω Ωs := by
  -- the outer statement is Theorem B (i) for `τ(Γ)`, `τ = invAt c`, `c = f₀(0) ∈ Ω`
  -- (`s08_outer_sup`), and BMO(`τ(Γ)`) ⟺ BMO(`Γ`) (`s08_cbo_bmo_iff`)
  obtain ⟨f₀, hf₀⟩ := s07_exists_riemannMap hΓ
  have hc : f₀ 0 ∈ Ω := hf₀.2.2.subset (mem_image_of_mem f₀ (mem_ball_self one_pos))
  obtain ⟨g, hg, hgInf⟩ := s08_dv_ext hΓ hc
  obtain ⟨lab', hlab', heq⟩ := s08_outer_sup hΓ hx₀ hc hlab
  rw [heq]
  exact (thm_B_i K _ _ (s08_mb_inner_qc hΓ hc) _ (s08_mb_sets hΓ hx₀ hc).2.2 lab' hlab').trans
    (s08_cbo_bmo_iff hΓ hg hgInf hf₀)

/-- Corollary 8.4 (ii), `cor:B-outer` (`sec08-thmB.tex:82`): for `g : 𝔻* → Ω*` conformal with
`g(∞) = ∞`, `lim_{r↓1} sup_{1<|b|<r} K_V^*(g(b)) = 0` iff `Γ` is a VMO quasicircle. -/
theorem cor_B_outer_ii (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K) (g : ℂ → ℂ)
    (hg : IsConformalOnto g unitDiscExterior Ωs) (hgInf : Tendsto g (cocompact ℂ) (cocompact ℂ))
    (x₀ : ℂ) (hx₀ : x₀ ∈ curveOf Ω Ωs) (lab : ℂ × ℝ → ℂ) (hlab : IsLabel (invPairΩs Ωs x₀) lab) :
    (∀ ε : ℝ≥0∞, 0 < ε → ∃ r : ℝ, 1 < r ∧ ∀ b : ℂ, 1 < ‖b‖ → ‖b‖ < r →
        KV (invPairΩs Ωs x₀) (invPairΩ Ω x₀) lab (invAt x₀ (g b)) ≤ ε) ↔
      IsVMOQuasicircle Ω Ωs := by
  -- the outer statement is Theorem B (ii) for `τ(Γ)`, `τ = invAt c`, `c = f₀(0) ∈ Ω`, along the
  -- conformal map `ĝ(z) = τ(g(1/z))` (`s08_outer_vanish`, `s08_mb_ghat`), and
  -- VMO(`τ(Γ)`) ⟺ VMO(`Γ`) (`s08_cbo_vmo_iff`)
  obtain ⟨f₀, hf₀⟩ := s07_exists_riemannMap hΓ
  have hc : f₀ 0 ∈ Ω := hf₀.2.2.subset (mem_image_of_mem f₀ (mem_ball_self one_pos))
  have hcs : f₀ 0 ∉ Ωs := fun h => Set.disjoint_left.mp (s08_ts_disj hΓ) hc h
  obtain ⟨lab', hlab', hiff⟩ := s08_outer_vanish hΓ hg hx₀ hc hlab
  exact hiff.trans ((thm_B_ii K _ _ (s08_mb_inner_qc hΓ hc) _ (s08_mb_ghat hg hgInf hcs) _
    (s08_mb_sets hΓ hx₀ hc).2.2 lab' hlab').trans (s08_cbo_vmo_iff hΓ hg hgInf hf₀))

end EpsteinVMO
