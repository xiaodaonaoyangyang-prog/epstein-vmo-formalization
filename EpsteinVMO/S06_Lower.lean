import EpsteinVMO.S05_Upper
import EpsteinVMO.S03_Coarse
import LiZhongQC.Ch03.S15_Distortion

/-!
# §6 The lower bound and the proof of Theorem A (`sec06-lower.tex`)

Statements of §6: Theorem 6.1 (`thm:lower`), Lemma 6.2 (`lem:grunsky`), Lemma 6.3
(`lem:strips`), Lemma 6.4 (`lem:local-mass`), Proposition 6.5 (`prop:mass-volume`) with its
Claim 6.6, Theorem A (`thm_A`) and Remark 6.7 (`rem:symmetric`).

## Conventions

* The curvature measure `μ_H = X_*(s² dâ) + X*_*(s*² dâ*)` is not given a name: as in the paper,
  `μ_H(E) = m_Ω(X⁻¹E) + m_{Ω*}((X*)⁻¹E)` with `m = curvMass`, which counts multiplicity.
* `B(P, r)` is the closed ball `hball P r`; `B_ρ(w, r)` in the hypothesis of Lemma 6.3 is taken
  closed, as in `prop_unique_label` (S03).
* `d(B_w, U*)` is `hdistSets (horoball Ω w) (horoUnion Ωs)` (S02).
* The displayed identity (6.4) (`eq:Phi-osc`, Möbius naturality of `Φ` under the osculating Möbius
  map, quoted from [BBVW, Lemma 3.1]) is used only inside the proof of Claim 6.6 and is not stated.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace EpsteinVMO

open LiZhongQC

/-- Taylor data at `0` of a function given on `𝔻` by a power series without constant term. -/
theorem s06_gr_phi {φ : ℂ → ℂ} {c : ℕ → ℂ}
    (h : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => (if n = 0 then 0 else c n) * z ^ n) (φ z)) :
    AnalyticAt ℂ φ 0 ∧ φ 0 = 0 ∧ deriv φ 0 = c 1 ∧ deriv (deriv φ) 0 = 2 * c 2 := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℂ, d = fun n => if n = 0 then 0 else c n := ⟨_, rfl⟩
  have h' : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => d n * z ^ n) (φ z) := by
    intro z hz; rw [hd]; exact h z hz
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ d with hp
  have hhalf : ((1 / 2 : ℝ) : ℂ) ∈ unitDisc := by
    rw [unitDisc, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; norm_num
  have hrad : ((1 / 2 : ℝ≥0) : ℝ≥0∞) ≤ p.radius := by
    refine p.le_radius_of_tendsto (l := 0) ?_
    have ht := ((h' _ hhalf).summable.tendsto_atTop_zero).norm
    rw [norm_zero] at ht
    refine ht.congr fun n => ?_
    rw [hp, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs]
    norm_num
  have hps : HasFPowerSeriesOnBall φ p 0 ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
    refine ⟨hrad, by norm_num, fun {y} hy => ?_⟩
    have hy' : y ∈ unitDisc := by
      rw [Metric.mem_eball, edist_zero_right] at hy
      have : ‖y‖₊ < (1 / 2 : ℝ≥0) := by exact_mod_cast hy
      rw [unitDisc, mem_ball_zero_iff]
      have : ‖y‖ < 1 / 2 := by exact_mod_cast this
      linarith
    rw [zero_add]
    refine (h' y hy').congr_fun ?_
    intro n
    rw [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  have hpa := hps.hasFPowerSeriesAt
  refine ⟨hpa.analyticAt, ?_, ?_, ?_⟩
  · have := hps.coeff_zero (fun _ => 1)
    rw [← this, hp, FormalMultilinearSeries.ofScalars_apply_eq, hd]
    simp
  · rw [hpa.deriv, hp, FormalMultilinearSeries.ofScalars_apply_eq, hd]
    simp
  · have h2 := hps.factorial_smul 1 2
    rw [← iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_succ, iteratedDeriv_one, hp,
      FormalMultilinearSeries.ofScalars_apply_eq, hd] at h2
    rw [← h2]
    simp

/-- Second derivative and Schwarzian at `0` of `z ↦ z e^{φ(z)}` with `φ(0) = 0`:
`F''(0) = 2φ'(0)` and `S_F(0) = 3φ''(0) - 3φ'(0)²`. -/
theorem s06_gr_schw {φ : ℂ → ℂ} (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0) :
    deriv (deriv (fun z => z * exp (φ z))) 0 = 2 * deriv φ 0 ∧
      schwarzianHol (fun z => z * exp (φ z)) 0 = 3 * deriv (deriv φ) 0 - 3 * deriv φ 0 ^ 2 := by
  obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ, F = fun z => z * exp (φ z) := ⟨_, rfl⟩
  obtain ⟨d1, hd1⟩ : ∃ d1 : ℂ → ℂ, d1 = deriv φ := ⟨_, rfl⟩
  obtain ⟨d2, hd2⟩ : ∃ d2 : ℂ → ℂ, d2 = deriv d1 := ⟨_, rfl⟩
  obtain ⟨G1, hG1⟩ : ∃ G1 : ℂ → ℂ, G1 = fun z => exp (φ z) * (1 + z * d1 z) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℂ → ℂ, N = fun z => d1 z * (1 + z * d1 z) + (d1 z + z * d2 z) :=
    ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℂ → ℂ, D = fun z => 1 + z * d1 z := ⟨_, rfl⟩
  have hev : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℂ φ z := hφ.eventually_analyticAt
  have hd1a : ∀ z, AnalyticAt ℂ φ z → AnalyticAt ℂ d1 z := fun z hz => hd1 ▸ hz.deriv
  have hd2a : ∀ z, AnalyticAt ℂ φ z → AnalyticAt ℂ d2 z := fun z hz => hd2 ▸ (hd1a z hz).deriv
  have hF1 : ∀ z, AnalyticAt ℂ φ z → HasDerivAt F (G1 z) z := by
    intro z hz
    have h1 := (hasDerivAt_id z).mul (hz.differentiableAt.hasDerivAt.cexp)
    rw [hF, hG1]
    refine h1.congr_deriv ?_
    rw [hd1]; simp only [id]; ring
  have hG1d : ∀ z, AnalyticAt ℂ φ z → HasDerivAt G1 (exp (φ z) * N z) z := by
    intro z hz
    have he := hz.differentiableAt.hasDerivAt.cexp
    have hl := ((hasDerivAt_id z).mul (hd1a z hz).differentiableAt.hasDerivAt).const_add 1
    have h1 := he.mul hl
    rw [hG1]
    refine h1.congr_deriv ?_
    rw [hN, hd2, hd1]; simp only [Pi.mul_apply, id]; ring
  have hdF : deriv F =ᶠ[𝓝 0] G1 := hev.mono fun z hz => (hF1 z hz).deriv
  have hddF : deriv (deriv F) =ᶠ[𝓝 0] fun z => exp (φ z) * N z := by
    have h1 : ∀ᶠ z in 𝓝 (0 : ℂ), deriv F =ᶠ[𝓝 z] G1 := by
      filter_upwards [hev.eventually_nhds] with z hz
      exact hz.mono fun y hy => (hF1 y hy).deriv
    filter_upwards [h1, hev] with z hz hza
    rw [hz.deriv_eq]; exact (hG1d z hza).deriv
  have hratio : (fun w => deriv (deriv F) w / deriv F w) =ᶠ[𝓝 0] N / D := by
    filter_upwards [hddF, hdF] with z h1 h2
    rw [Pi.div_apply, h1, h2, hG1, hD]
    simp only
    rw [mul_div_mul_left _ _ (exp_ne_zero _)]
  have hN0 : N 0 = 2 * d1 0 := by rw [hN]; ring
  have hD0 : D 0 = 1 := by rw [hD]; ring
  have hNd : HasDerivAt N (3 * d2 0 + d1 0 ^ 2) 0 := by
    have ha1 := (hd1a 0 hφ).differentiableAt.hasDerivAt
    have ha2 := (hd2a 0 hφ).differentiableAt.hasDerivAt
    have hl := ((hasDerivAt_id (0 : ℂ)).mul ha1).const_add 1
    have hm := (hasDerivAt_id (0 : ℂ)).mul ha2
    have h := (ha1.mul hl).add (ha1.add hm)
    rw [hN]
    refine h.congr_deriv ?_
    rw [← hd2]; simp only [Pi.mul_apply, id]; ring
  have hDd : HasDerivAt D (d1 0) 0 := by
    have ha1 := (hd1a 0 hφ).differentiableAt.hasDerivAt
    have hl := ((hasDerivAt_id (0 : ℂ)).mul ha1).const_add 1
    rw [hD]
    refine hl.congr_deriv ?_
    simp only [id]; ring
  have hQ := hNd.div hDd (by rw [hD0]; exact one_ne_zero)
  have hdF0 : deriv F 0 = 1 := by
    rw [hdF.eq_of_nhds, hG1]; simp [h0]
  have hddF0 : deriv (deriv F) 0 = 2 * d1 0 := by
    rw [hddF.eq_of_nhds, h0, exp_zero, one_mul, hN0]
  refine ⟨?_, ?_⟩
  · rw [← hF, hddF0, hd1]
  · rw [← hF]
    show deriv (fun w => deriv (deriv F) w / deriv F w) 0 -
        (1 / 2) * (deriv (deriv F) 0 / deriv F 0) ^ 2 = _
    rw [hratio.deriv_eq, hQ.deriv, hddF0, hdF0, hN0, hD0, ← hd1, ← hd2]
    ring

/-- The Grunsky estimate for a normalized disjoint pair: `(|S_f(0)|/4)² ≤ 9 log|g'(∞)|`
(the computation in the proof of Lemma 6.2, with `N = 2` in the Grunsky inequality). -/
theorem s06_gr_core {f g : ℂ → ℂ} (h : TakhtajanTeo.Ch2.IsNormalizedDisjointPair f g) :
    (‖schwarzian f 0‖ / 4) ^ 2 ≤ 9 * Real.log ‖TakhtajanTeo.derivAtInfty g‖ := by
  obtain ⟨φ, hφs, hfφ⟩ := TakhtajanTeo.Ch2.r22_f_series h
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, c = fun n : ℕ => -TakhtajanTeo.Ch2.grunsky f g (-(n : ℤ)) 0 :=
    ⟨_, rfl⟩
  have hφs' : ∀ z ∈ unitDisc, HasSum (fun n : ℕ => (if n = 0 then 0 else c n) * z ^ n) (φ z) := by
    rw [hc]; exact hφs
  obtain ⟨hφa, hφ0, hφ1, hφ2⟩ := s06_gr_phi hφs'
  obtain ⟨hdd, hS⟩ := s06_gr_schw hφa hφ0
  have hball : unitDisc ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds (mem_ball_self one_pos)
  have heq : f =ᶠ[𝓝 0] fun z => z * exp (φ z) := Filter.eventually_of_mem hball hfφ
  have hfa : AnalyticAt ℂ f 0 :=
    h.1.analyticAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))
  have hSf : schwarzian f 0 = 3 * (2 * c 2) - 3 * c 1 ^ 2 := by
    rw [schwarzian_of_analyticAt hfa, schwarzianHol_congr heq, hS, hφ1, hφ2]
  have hB := koebe_bieberbach h.1 h.2.1 h.2.2.1 h.2.2.2.1
  rw [heq.deriv.deriv_eq, hdd, hφ1, norm_mul] at hB
  have hc1 : ‖c 1‖ ≤ 2 := by norm_num at hB; linarith
  have hP := s02_r22_partial_le h 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hP
  have e1 : ‖c 1‖ = ‖TakhtajanTeo.Ch2.grunsky f g (-((((0 : ℕ) : ℤ)) + 1)) 0‖ := by
    rw [hc]; simp
  have e2 : ‖c 2‖ = ‖TakhtajanTeo.Ch2.grunsky f g (-((((1 : ℕ) : ℤ)) + 1)) 0‖ := by
    rw [hc]; simp
  rw [← e1, ← e2, Real.log_pow] at hP
  have hx := norm_nonneg (c 1)
  have hy := norm_nonneg (c 2)
  have hq1 := sq_nonneg ‖TakhtajanTeo.Ch2.grunsky f g (((0 : ℕ) : ℤ) + 1) 0‖
  have hq2 := sq_nonneg ‖TakhtajanTeo.Ch2.grunsky f g (((1 : ℕ) : ℤ) + 1) 0‖
  have hT : ‖schwarzian f 0‖ ≤ 6 * ‖c 2‖ + 3 * ‖c 1‖ ^ 2 := by
    rw [hSf]
    calc ‖3 * (2 * c 2) - 3 * c 1 ^ 2‖ ≤ ‖3 * (2 * c 2)‖ + ‖3 * c 1 ^ 2‖ := norm_sub_le _ _
      _ = 6 * ‖c 2‖ + 3 * ‖c 1‖ ^ 2 := by
        rw [norm_mul, norm_mul, norm_mul, norm_pow]; norm_num; ring
  have hTn := norm_nonneg (schwarzian f 0)
  have hsq : ‖schwarzian f 0‖ ^ 2 ≤ (6 * ‖c 2‖ + 3 * ‖c 1‖ ^ 2) ^ 2 := by gcongr
  push_cast at hP
  nlinarith [sq_nonneg (6 * ‖c 2‖ - 3 * ‖c 1‖ ^ 2), mul_nonneg hx hx,
    mul_le_mul_of_nonneg_left hc1 hx]

/-- Elementary inequality: a point `(W, ξ)` of the closed ball of Euclidean diameter `h` tangent to
`ℂ` at `b` satisfies `‖W - a‖² + ξ² ≥ ξ ‖a - b‖²/h`. -/
theorem s06_gr_ball_ineq {a b W : ℂ} {ξ h : ℝ} (hξ : 0 < ξ)
    (hB : ‖W - b‖ ^ 2 + ξ ^ 2 ≤ h * ξ) :
    ξ * ‖a - b‖ ^ 2 ≤ h * (‖W - a‖ ^ 2 + ξ ^ 2) := by
  have htri : ‖a - b‖ ≤ ‖W - a‖ + ‖W - b‖ := by
    calc ‖a - b‖ = ‖(W - b) - (W - a)‖ := by ring_nf
      _ ≤ ‖W - b‖ + ‖W - a‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  have hA := norm_nonneg (W - a)
  have hBn := norm_nonneg (W - b)
  have hv := norm_nonneg (a - b)
  have hsq : ‖a - b‖ ^ 2 ≤ (‖W - a‖ + ‖W - b‖) ^ 2 := by gcongr
  set A := ‖W - a‖
  set B := ‖W - b‖
  -- `ξ (A+B)² ≤ h (A² + ξ²)`: use `h ξ ≥ ξ² + B²` and `(AB - ξ²)² ≥ 0`.
  have key : ξ * (A + B) ^ 2 ≤ h * (A ^ 2 + ξ ^ 2) := by
    have h1 : ξ * (ξ * (A + B) ^ 2) ≤ ξ * (h * (A ^ 2 + ξ ^ 2)) := by
      nlinarith [sq_nonneg (A * B - ξ ^ 2), mul_le_mul_of_nonneg_left hB (sq_nonneg A),
        mul_le_mul_of_nonneg_left hB (le_of_lt (pow_pos hξ 2))]
    exact le_of_mul_le_mul_left h1 hξ
  calc ξ * ‖a - b‖ ^ 2 ≤ ξ * (A + B) ^ 2 := mul_le_mul_of_nonneg_left hsq hξ.le
    _ ≤ _ := key

/-- Hyperbolic distance between the horoballs `B_w ⊆ ℍ³` of `Ω` and `B*_{w*}` of `Ω*`:
`d(q, q') ≥ log(λ(w) λ*(w*) ‖w - w*‖²/4)`. -/
theorem s06_gr_horo_dist {Ω Ωs : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    (hΩs : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ωs) {w ws : ℂ} (hw : w ∈ Ω) (hws : ws ∈ Ωs) (hww : w ≠ ws)
    {q q' : ℂ × ℝ} (hq : q ∈ horoball Ω w) (hq' : q' ∈ horoball Ωs ws) :
    Real.log (poincareDensity Ω w * poincareDensity Ωs ws * ‖w - ws‖ ^ 2 / 4) ≤ hdist q q' := by
  have hl := s02_poincareDensity_pos hΩ hw
  have hls := s02_poincareDensity_pos hΩs hws
  have hξ : 0 < q.2 := hq.1
  have hξ' : 0 < q'.2 := hq'.1
  have hbus := lem_busemann hΩ hw hq.1 hq'.1
  have hP : horoPhi Ω q w ≤ 1 := hq.2
  have hPpos : 0 < horoPhi Ω q w := by
    unfold horoPhi; positivity
  have hlog1 : Real.log (horoPhi Ω q w) ≤ 0 := Real.log_nonpos hPpos.le hP
  have hP' : horoPhi Ωs q' ws ≤ 1 := hq'.2
  unfold horoPhi at hP'
  rw [div_le_one (by positivity)] at hP'
  -- `q'` lies in the ball of diameter `h₂ = 2/λ*(w*)` tangent at `w*`.
  have hB : ‖q'.1 - ws‖ ^ 2 + q'.2 ^ 2 ≤ (2 / poincareDensity Ωs ws) * q'.2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hls]; nlinarith
  have hineq := s06_gr_ball_ineq (a := w) hξ' hB
  have hpos : 0 < poincareDensity Ω w * poincareDensity Ωs ws * ‖w - ws‖ ^ 2 / 4 := by
    have : 0 < ‖w - ws‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hww)
    positivity
  have hle : poincareDensity Ω w * poincareDensity Ωs ws * ‖w - ws‖ ^ 2 / 4 ≤
      horoPhi Ω q' w := by
    unfold horoPhi
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    rw [div_mul_eq_mul_div, le_div_iff₀ hls] at hineq
    nlinarith [mul_le_mul_of_nonneg_left hineq hl.le]
  have hlog2 := Real.log_le_log hpos hle
  have := (abs_le.mp hbus).1
  linarith

/-- Möbius invariance of the Schwarzian for the normalization `B((f - u)⁻¹ - Δ⁻¹)` used in
`s02_normalize_pair`, when `u ∉ Ω = f(𝔻)`. -/
theorem s06_gr_mobius {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {u Δ B : ℂ}
    (hu : u ∉ Ω) (hΔ : Δ ≠ 0) (hB : B ≠ 0) :
    schwarzian (fun z => B * ((f z - u)⁻¹ - Δ⁻¹)) 0 = schwarzian f 0 := by
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hball : unitDisc ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds h0
  have hfu : ∀ z ∈ unitDisc, f z - u ≠ 0 := by
    intro z hz h
    rw [sub_eq_zero] at h
    exact hu (h ▸ hf.2.2 ▸ mem_image_of_mem f hz)
  have heq : (fun z => B * ((f z - u)⁻¹ - Δ⁻¹)) =ᶠ[𝓝 0]
      fun z => (-B * Δ⁻¹ * f z + (B + B * Δ⁻¹ * u)) / (1 * f z + -u) := by
    filter_upwards [hball] with z hz
    have h1 := hfu z hz
    rw [one_mul, ← sub_eq_add_neg]
    field_simp
    ring
  rw [schwarzian_congr (heq.filter_mono nhdsWithin_le_nhds)]
  have hfa : AnalyticAt ℂ f 0 := hf.1.analyticAt hball
  have hf' : deriv f 0 ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 h0
  refine schwarzian_mobius_comp_of_ne hfa hf' ?_ ?_
  · intro h
    apply hB
    linear_combination -h
  · rw [one_mul, ← sub_eq_add_neg]; exact hfu 0 h0

/-- The centre point `(w, 1/λ(w))` lies in `B_w`. -/
theorem s06_gr_center {Ω : Set ℂ} {w : ℂ} (hl : 0 < poincareDensity Ω w) :
    (w, 1 / poincareDensity Ω w) ∈ horoball Ω w := by
  refine ⟨by show 0 < 1 / poincareDensity Ω w; positivity, ?_⟩
  show horoPhi Ω (w, 1 / poincareDensity Ω w) w ≤ 1
  have : horoPhi Ω (w, 1 / poincareDensity Ω w) w = 1 / 2 := by
    unfold horoPhi
    simp only [sub_self, norm_zero]
    field_simp
    ring
  rw [this]; norm_num

/-- One side of Lemma 6.2: `d(B_w, U*) ≥ s(w)²/9` for `w ∈ Ω`. -/
theorem s06_gr_one {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) {w : ℂ} (hw : w ∈ Ω) :
    schwarzNorm Ω w ^ 2 / 9 ≤ hdistSets (horoball Ω w) (horoUnion Ωs) := by
  have hΓs := s02_jordanPair_symm hΓ
  have hd := s02_jordanPair_disjoint hΓ
  have hΩ := s02_jordanPair_riemannMap hΓ
  have hΩs := s02_jordanPair_riemannMap hΓs
  obtain ⟨f, hf, hf0⟩ := s02_riemannMap_at hΓ hw
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hs : schwarzNorm Ω w = ‖schwarzian f 0‖ / 4 := by
    have := eq_s_disk hf h0
    rw [hf0] at this
    rw [this]; simp
  have hl := s02_poincareDensity_pos hΩ hw
  have hfd : deriv f 0 ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 h0
  have hfn : ‖deriv f 0‖ ≠ 0 := norm_ne_zero_iff.mpr hfd
  have e1 : poincareDensity Ω w = 2 / ‖deriv f 0‖ := by
    have hlf := eq_lambda_f hf h0
    rw [hf0] at hlf
    rw [eq_div_iff hfn, hlf]; simp
  have key : ∀ ws ∈ Ωs, schwarzNorm Ω w ^ 2 / 9 ≤
      Real.log (poincareDensity Ω w * poincareDensity Ωs ws * ‖w - ws‖ ^ 2 / 4) := by
    intro ws hws
    obtain ⟨g, hg, hg0⟩ := s02_riemannMap_at hΓs hws
    obtain ⟨hN, -, hder⟩ := s02_normalize_pair hd hf hg
    have hc := s06_gr_core hN
    have hgd : deriv g 0 ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hg.1 hg.2.1 h0
    have hgn : ‖deriv g 0‖ ≠ 0 := norm_ne_zero_iff.mpr hgd
    have hww : w ≠ ws := hd.ne_of_mem hw hws
    have hΔ : f 0 - g 0 ≠ 0 := by rw [hf0, hg0]; exact sub_ne_zero.mpr hww
    have hu : g 0 ∉ Ω := fun h => hd.ne_of_mem h (hg0 ▸ hws) rfl
    have hB : -(f 0 - g 0) ^ 2 / deriv f 0 ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hΔ)) hfd
    rw [s06_gr_mobius hf hu hΔ hB, hder] at hc
    have e2 : poincareDensity Ωs ws = 2 / ‖deriv g 0‖ := by
      have hlg := eq_lambda_f hg h0
      rw [hg0] at hlg
      rw [eq_div_iff hgn, hlg]; simp
    have hn : ‖-(f 0 - g 0) ^ 2 / (deriv f 0 * deriv g 0)‖ =
        poincareDensity Ω w * poincareDensity Ωs ws * ‖w - ws‖ ^ 2 / 4 := by
      rw [norm_div, norm_neg, norm_pow, norm_mul, hf0, hg0, e1, e2]
      field_simp
      ring
    rw [hs, ← hn]
    linarith
  unfold hdistSets
  obtain ⟨F, -, hF2⟩ := hΓ
  have hws0 : F (-I) ∈ Ωs := hF2 ▸ mem_image_of_mem F (show (-I).im < 0 by simp)
  have hls0 := s02_poincareDensity_pos hΩs hws0
  have hU0 : (F (-I), 1 / poincareDensity Ωs (F (-I))) ∈ horoUnion Ωs := by
    unfold horoUnion
    exact mem_iUnion₂.mpr ⟨_, hws0, s06_gr_center hls0⟩
  refine le_csInf ⟨_, mem_image2_of_mem (s06_gr_center hl) hU0⟩ ?_
  rintro x ⟨q, hq, q', hq', rfl⟩
  unfold horoUnion at hq'
  obtain ⟨ws, hws, hq'ws⟩ := mem_iUnion₂.mp hq'
  exact (key ws hws).trans (s06_gr_horo_dist hΩ hΩs hw hws (hd.ne_of_mem hw hws) hq hq'ws)

/-- **Lemma 6.2** (`lem:grunsky`, sec06-lower.tex:22).  For a Jordan curve and `w ∈ Ω`,
`d(B_w, U*) ≥ s(w)²/9` (6.2) (`eq:grunsky`), and symmetrically `d(B*_{z*}, U) ≥ s*(z*)²/9` for
`z* ∈ Ω*`. -/
theorem lem_grunsky : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs →
    (∀ w ∈ Ω, schwarzNorm Ω w ^ 2 / 9 ≤ hdistSets (horoball Ω w) (horoUnion Ωs)) ∧
    ∀ z ∈ Ωs, schwarzNorm Ωs z ^ 2 / 9 ≤ hdistSets (horoball Ωs z) (horoUnion Ω) := by
  intro Ω Ωs hΓ
  exact ⟨fun w hw => s06_gr_one hΓ hw, fun z hz => s06_gr_one (s02_jordanPair_symm hΓ) hz⟩

/-- `d(q, q') ≥ 0` on `ℍ³`. -/
theorem s06_st_hdist_nonneg {q q' : ℂ × ℝ} (hq : q ∈ UHS) (hq' : q' ∈ UHS) :
    0 ≤ hdist q q' := by
  have h2 : 0 < q.2 := hq
  have h2' : 0 < q'.2 := hq'
  unfold hdist coshDist
  refine Real.arcosh_nonneg ?_
  have : 0 ≤ (‖q.1 - q'.1‖ ^ 2 + (q.2 - q'.2) ^ 2) / (2 * q.2 * q'.2) := by positivity
  linarith

/-- **Lemma 6.3** (Short strips, `lem:strips`, sec06-lower.tex:70).  With `R₀ = R₀(K)` (as in
Proposition 3.11): if `w ∈ Ω` and `s < 1/2` on `B_ρ(w, R₀ + 2)`, then
`{E(w, τ) : 0 < τ < s(w)²/18} ⊆ 𝒩` (6.3) (`eq:strip`); strips issued from different such points
of `Ω` are disjoint. -/
theorem lem_strips : ∀ K : ℝ, 1 ≤ K → ∃ R₀ : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
    ¬ IsLinePair Ω Ωs →
      (∀ w ∈ Ω, (∀ w' ∈ Ω, poincareDist Ω w w' ≤ R₀ + 2 → schwarzNorm Ω w' < 1 / 2) →
        ∀ τ : ℝ, 0 < τ → τ < schwarzNorm Ω w ^ 2 / 18 → normalGeod Ω w τ ∈ gap Ω Ωs) ∧
      ∀ w₁ ∈ Ω, ∀ w₂ ∈ Ω,
        (∀ w' ∈ Ω, poincareDist Ω w₁ w' ≤ R₀ + 2 → schwarzNorm Ω w' < 1 / 2) →
        (∀ w' ∈ Ω, poincareDist Ω w₂ w' ≤ R₀ + 2 → schwarzNorm Ω w' < 1 / 2) → w₁ ≠ w₂ →
        ∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ < schwarzNorm Ω w₁ ^ 2 / 18 →
          0 < τ₂ → τ₂ < schwarzNorm Ω w₂ ^ 2 / 18 →
            normalGeod Ω w₁ τ₁ ≠ normalGeod Ω w₂ τ₂ := by
  intro K _
  obtain ⟨R₀, hR⟩ := prop_unique_label K
  refine ⟨R₀, fun Ω Ωs hK hnc => ?_⟩
  have hΓ := s03_b0_jordanPair hK
  have hΩ := s02_jordanPair_riemannMap hΓ
  -- `τ < s(w)²/18 ≤ 1/8` by Nehari
  have hτ1 : ∀ w ∈ Ω, ∀ τ : ℝ, τ < schwarzNorm Ω w ^ 2 / 18 → τ ≤ 1 := fun w hw τ hτ => by
    have hN := eq_nehari hΩ hw
    nlinarith [hN.1, hN.2]
  refine ⟨fun w hw hs τ hτ0 hτs => ?_, fun w₁ hw₁ w₂ hw₂ hs₁ hs₂ hne τ₁ τ₂ h1 h1' h2 h2' =>
    (hR Ω Ωs hK hnc).2 w₁ hw₁ w₂ hw₂ hs₁ hs₂ hne τ₁ ⟨h1, hτ1 w₁ hw₁ τ₁ h1'⟩ τ₂
      ⟨h2, hτ1 w₂ hw₂ τ₂ h2'⟩⟩
  have hmin := ((hR Ω Ωs hK hnc).1 w hw hs).1 τ ⟨hτ0.le, hτ1 w hw τ hτs⟩
  have hl := s02_poincareDensity_pos hΩ hw
  obtain ⟨hU, hd, h0⟩ := lem_normal_b hΩ hw
  refine ⟨hU τ, ?_⟩
  rintro (hq | hq)
  · -- `Φ_{E(w,τ)} ≥ Φ_{E(w,τ)}(w) = e^τ > 1` on `Ω` (Proposition 3.11), so `E(w,τ) ∉ U`
    rw [horoUnion, mem_iUnion₂] at hq
    obtain ⟨w'', hw'', hB⟩ := hq
    have h1 : horoPhi Ω (normalGeod Ω w τ) w ≤ horoPhi Ω (normalGeod Ω w τ) w'' := by
      by_cases he : w'' = w
      · rw [he]
      · exact (hmin w'' hw'' he).le
    rw [s02_horoPhi_normalGeod Ω w hl] at h1
    linarith [hB.2, Real.one_lt_exp_iff.mpr hτ0]
  · -- `d(B_w, U*) ≤ d(X(w), E(w,τ)) = τ < s(w)²/18`, against Lemma 6.2
    have hX : epstein Ω w ∈ horoball Ω w :=
      ⟨h0 ▸ hU 0, by rw [← h0, s02_horoPhi_normalGeod Ω w hl, Real.exp_zero]⟩
    have hg := s06_gr_one hΓ hw
    have hle : hdistSets (horoball Ω w) (horoUnion Ωs) ≤ τ := by
      unfold hdistSets
      refine csInf_le ⟨0, ?_⟩ ⟨_, hX, _, hq, ?_⟩
      · rintro x ⟨a, ha, b, hb, rfl⟩
        rw [horoUnion, mem_iUnion₂] at hb
        obtain ⟨ws, hws, hbw⟩ := hb
        exact s06_st_hdist_nonneg ha.1 hbw.1
      · rw [← h0, hd, zero_sub, abs_neg, abs_of_pos hτ0]
    linarith

/-- `d_𝔻(0, z) ≤ R` forces `|z| ≤ (e^R - 1)/(e^R + 1)`. -/
theorem s06_lm_radius {z : ℂ} (hz : ‖z‖ < 1) {R : ℝ} (h : logRatio ‖z‖ ≤ R) :
    ‖z‖ ≤ (Real.exp R - 1) / (Real.exp R + 1) := by
  change Real.log (1 + ‖z‖) - Real.log (1 - ‖z‖) ≤ R at h
  have h1 : 0 < 1 - ‖z‖ := by linarith
  have h2 : 0 < 1 + ‖z‖ := by linarith [norm_nonneg z]
  have h3 : Real.log (1 + ‖z‖) ≤ R + Real.log (1 - ‖z‖) := by linarith
  rw [Real.log_le_iff_le_exp h2, Real.exp_add, Real.exp_log h1] at h3
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- `m_Ω(Ω^c) = 0`. -/
theorem s06_lm_compl {Ω : Set ℂ} (hΩ : IsOpen Ω) : curvMass Ω Ωᶜ = 0 := by
  unfold curvMass
  rw [withDensity_apply _ hΩ.measurableSet.compl,
    Measure.restrict_restrict hΩ.measurableSet.compl, compl_inter_self, Measure.restrict_empty,
    lintegral_zero_measure]

/-- The curvature mass of the image of a closed disc `|z| ≤ t < 1` under a Riemann map:
`m_Ω(f(\bar D_t)) ≤ 9/(1-t²)² · area(\bar D_t)` (by (2.6) and Nehari `s ≤ 3/2`). -/
theorem s06_lm_disc {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {t : ℝ}
    (ht1 : t < 1) :
    curvMass Ω (f '' closedBall 0 t) ≤
      ENNReal.ofReal (9 / (1 - t ^ 2) ^ 2) * volume (closedBall (0 : ℂ) t) := by
  have hsub : closedBall (0 : ℂ) t ⊆ unitDisc := closedBall_subset_ball ht1
  have hT : MeasurableSet (f '' closedBall 0 t) :=
    ((isCompact_closedBall 0 t).image_of_continuousOn
      (hf.1.continuousOn.mono hsub)).isClosed.measurableSet
  rw [← lintegral_indicator_one hT,
    eq_pullback_mass_a (φ := (f '' closedBall (0 : ℂ) t).indicator 1) hf
      (measurable_one.indicator hT)]
  calc ∫⁻ z in unitDisc, (f '' closedBall 0 t).indicator 1 (f z) *
        ENNReal.ofReal (‖schwarzian f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 / 4)
      ≤ ∫⁻ z in unitDisc, (closedBall (0 : ℂ) t).indicator
          (fun _ => ENNReal.ofReal (9 / (1 - t ^ 2) ^ 2)) z := by
        refine setLIntegral_mono (measurable_const.indicator measurableSet_closedBall) ?_
        intro z hz
        by_cases hfz : f z ∈ f '' closedBall 0 t
        · have hfz' := hfz
          obtain ⟨z', hz', hzz⟩ := hfz'
          have hzc : z ∈ closedBall (0 : ℂ) t := hf.2.1 (hsub hz') hz hzz ▸ hz'
          rw [indicator_of_mem hfz, indicator_of_mem hzc, Pi.one_apply, one_mul]
          refine ENNReal.ofReal_le_ofReal ?_
          have hzt : ‖z‖ ≤ t := mem_closedBall_zero_iff.mp hzc
          have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
          have hfzΩ : f z ∈ Ω := hf.2.2 ▸ mem_image_of_mem f hz
          have hN := (eq_nehari ⟨f, hf⟩ hfzΩ).2
          rw [eq_s_disk hf hz] at hN
          set u := 1 - ‖z‖ ^ 2 with hu
          set S := ‖schwarzian f z‖
          have hS0 : 0 ≤ S := norm_nonneg _
          have hu0 : 0 < 1 - t ^ 2 := by nlinarith [norm_nonneg z]
          have hut : 1 - t ^ 2 ≤ u := by nlinarith [norm_nonneg z]
          have hupos : 0 < u := lt_of_lt_of_le hu0 hut
          have h6 : S * u ^ 2 ≤ 6 := by linarith
          have hb : S ^ 2 * u ^ 2 / 4 ≤ 9 / u ^ 2 := by
            rw [le_div_iff₀ (by positivity)]
            nlinarith [mul_nonneg hS0 (sq_nonneg u)]
          calc S ^ 2 * u ^ 2 / 4 ≤ 9 / u ^ 2 := hb
            _ ≤ 9 / (1 - t ^ 2) ^ 2 := by gcongr
        · rw [indicator_of_notMem hfz, zero_mul]
          exact bot_le
    _ = ENNReal.ofReal (9 / (1 - t ^ 2) ^ 2) * (volume.restrict unitDisc) (closedBall 0 t) :=
        lintegral_indicator_const measurableSet_closedBall _
    _ ≤ _ := by gcongr; exact Measure.restrict_le_self

/-- One side of Lemma 6.4: `m_Ω(X⁻¹ B(P, 1)) ≤ M(K)`. -/
theorem s06_lm_side (K : ℝ) : ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
    ∀ P ∈ UHS, curvMass Ω (epstein Ω ⁻¹' hball P 1) ≤ M := by
  obtain ⟨A, B, hA, hl⟩ := s03_qi_lower K
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = max (2 * A + B) 0 := ⟨_, rfl⟩
  obtain ⟨t, htd⟩ : ∃ t : ℝ, t = (Real.exp R - 1) / (Real.exp R + 1) := ⟨_, rfl⟩
  have he : 0 < Real.exp R := Real.exp_pos R
  have ht1 : t < 1 := by rw [htd, div_lt_one (by linarith)]; linarith
  refine ⟨ENNReal.ofReal (9 / (1 - t ^ 2) ^ 2) * volume (closedBall (0 : ℂ) t),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (isCompact_closedBall _ _).measure_lt_top.ne, ?_⟩
  intro Ω Ωs h P hP
  obtain ⟨hΩo, -, -, -⟩ := s03_b0_basic h
  have hc := s06_lm_compl hΩo
  by_cases hE : (epstein Ω ⁻¹' hball P 1 ∩ Ω).Nonempty
  · obtain ⟨w0, hw0E, hw0⟩ := hE
    obtain ⟨f, hf, hf0⟩ := s02_riemannMap_at (s03_b0_jordanPair h) hw0
    have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
    have hsub : epstein Ω ⁻¹' hball P 1 ⊆ f '' closedBall 0 t ∪ Ωᶜ := by
      intro w hwE
      by_cases hw : w ∈ Ω
      · left
        obtain ⟨z, hz, rfl⟩ : w ∈ f '' unitDisc := by rw [hf.2.2]; exact hw
        refine ⟨z, ?_, rfl⟩
        have hd : hdist (epstein Ω w0) (epstein Ω (f z)) ≤ 2 := by
          have tr := s02_hdist_triangle hw0E.1 hP hwE.1
          rw [s02_hdist_comm (epstein Ω w0) P] at tr
          linarith [hw0E.2, hwE.2]
        have hq := hl Ω Ωs h w0 hw0 (f z) hw
        rw [← hf0, subsec_poincare_dist hf h0 hz,
          s05_diskDist_zero (mem_ball_zero_iff.mp hz)] at hq
        have hqR : logRatio ‖z‖ ≤ R := by
          rw [hR]
          refine le_trans hq (le_trans ?_ (le_max_left _ _))
          rw [← hf0] at hd
          nlinarith [mul_le_mul_of_nonneg_left hd hA]
        rw [mem_closedBall_zero_iff, htd]
        exact s06_lm_radius (mem_ball_zero_iff.mp hz) hqR
      · right; exact hw
    calc curvMass Ω (epstein Ω ⁻¹' hball P 1) ≤ curvMass Ω (f '' closedBall 0 t ∪ Ωᶜ) :=
          measure_mono hsub
      _ ≤ curvMass Ω (f '' closedBall 0 t) + curvMass Ω Ωᶜ := measure_union_le _ _
      _ ≤ _ := by rw [hc, add_zero]; exact s06_lm_disc hf ht1
  · have hsub : epstein Ω ⁻¹' hball P 1 ⊆ Ωᶜ := fun w hw hwΩ => hE ⟨w, hw, hwΩ⟩
    calc curvMass Ω (epstein Ω ⁻¹' hball P 1) ≤ curvMass Ω Ωᶜ := measure_mono hsub
      _ = 0 := hc
      _ ≤ _ := bot_le

/-- **Lemma 6.4** (`lem:local-mass`, sec06-lower.tex:91).  There is `C₁(K)` with
`μ_H(B(P, 1)) ≤ C₁(K)` for every `P ∈ ℍ³`. -/
theorem lem_local_mass : ∀ K : ℝ, 1 ≤ K → ∃ C₁ : ℝ≥0, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
    ∀ P ∈ UHS,
      curvMass Ω (epstein Ω ⁻¹' hball P 1) + curvMass Ωs (epstein Ωs ⁻¹' hball P 1) ≤
        (C₁ : ℝ≥0∞) := by
  intro K _
  obtain ⟨M, hM, hside⟩ := s06_lm_side K
  refine ⟨2 * M.toNNReal, fun Ω Ωs h P hP => ?_⟩
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hM, ENNReal.coe_ofNat, two_mul]
  exact add_le_add (hside Ω Ωs h P hP) (hside Ωs Ω (s03_qce_swap h) P hP)

/-- Mass–volume helper (MV3): for `0 ≤ s < 1/2` and `0 ≤ τ ≤ 1/72`,
`cosh²τ - s² e^{2τ} ≥ 7/10`. -/
theorem s06_mv_factor_ge {s τ : ℝ} (hs0 : 0 ≤ s) (hs : s < 1 / 2) (hτ0 : 0 ≤ τ)
    (hτ : τ ≤ 1 / 72) : 7 / 10 ≤ Real.cosh τ ^ 2 - s ^ 2 * Real.exp τ ^ 2 := by
  have hc : 1 ≤ Real.cosh τ := Real.one_le_cosh τ
  have he0 : 0 < Real.exp τ := Real.exp_pos τ
  have he : Real.exp τ ≤ 72 / 71 := by
    refine (Real.exp_bound_div_one_sub_of_interval hτ0 (by linarith)).trans ?_
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hs2 : s ^ 2 ≤ 1 / 4 := by nlinarith
  have hp : s ^ 2 * Real.exp τ ^ 2 ≤ 1 / 4 * (72 / 71) ^ 2 :=
    mul_le_mul hs2 (pow_le_pow_left₀ he0.le he 2) (by positivity) (by norm_num)
  have hc2 : 1 ≤ Real.cosh τ ^ 2 := by nlinarith
  norm_num at hp
  linarith

/-- Mass–volume helper (MV4): the strip set
`S = {(w, τ) : w ∈ Π, 0 < τ < s(w)²/18}` over `Π = X⁻¹(B(P, 1))` is measurable. -/
theorem s06_mv_strip_measurable {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {P : ℂ × ℝ}
    (hP : P ∈ UHS) :
    MeasurableSet {p : ℂ × ℝ | p.1 ∈ Ω ∧ epstein Ω p.1 ∈ hball P 1 ∧ 0 < p.2 ∧
      p.2 < schwarzNorm Ω p.1 ^ 2 / 18} := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  have hΩo : IsOpen Ω := s05_jordan_isOpen hJ
  have hP2 : (0 : ℝ) < P.2 := hP
  have hXU : ∀ w ∈ Ω, 0 < (epstein Ω w).2 := fun w hw => by
    have h := lem_normal_b ⟨f, hf⟩ hw
    rw [← h.2.2]
    exact h.1 0
  have hXC : ContinuousOn (epstein Ω) Ω := (lem_fff_smooth ⟨f, hf⟩).continuousOn
  have hsC : ContinuousOn (schwarzNorm Ω) Ω :=
    ((s02_contDiffOn_invFun hf).2.2.2.continuousOn.norm.div
      ((s02_contDiffOn_poincareDensity hf).continuousOn.pow 2)
      (fun x hx => pow_ne_zero 2 (s02_poincareDensity_pos ⟨f, hf⟩ hx).ne')).congr
      (fun x hx => eq_def_s hf hx)
  have hg : ContinuousOn (fun w => coshDist P (epstein Ω w)) Ω := by
    unfold coshDist
    have h1 : ContinuousOn (fun w => (epstein Ω w).1) Ω := continuous_fst.comp_continuousOn hXC
    have h2 : ContinuousOn (fun w => (epstein Ω w).2) Ω := continuous_snd.comp_continuousOn hXC
    exact continuousOn_const.add ((((continuousOn_const.sub h1).norm.pow 2).add
      ((continuousOn_const.sub h2).pow 2)).div (continuousOn_const.mul h2)
      fun w hw => (mul_pos (mul_pos two_pos hP2) (hXU w hw)).ne')
  -- `X(w) ∈ B(P, 1) ↔ cosh d(P, X(w)) ≤ cosh 1`
  have hiff : ∀ w ∈ Ω, epstein Ω w ∈ hball P 1 ↔ coshDist P (epstein Ω w) ≤ Real.cosh 1 := by
    intro w hw
    have hc1 : 0 < coshDist P (epstein Ω w) := by
      have h0 := hXU w hw
      unfold coshDist
      have : 0 ≤ (‖P.1 - (epstein Ω w).1‖ ^ 2 + (P.2 - (epstein Ω w).2) ^ 2) /
          (2 * P.2 * (epstein Ω w).2) :=
        div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_pos (mul_pos two_pos hP2) h0).le
      linarith
    have hch : 0 < Real.cosh 1 := Real.cosh_pos 1
    constructor
    · rintro ⟨-, hd⟩
      exact (Real.arcosh_le_arcosh hc1 hch).1 (hd.trans (Real.arcosh_cosh zero_le_one).symm.le)
    · intro h
      exact ⟨hXU w hw, ((Real.arcosh_le_arcosh hc1 hch).2 h).trans (Real.arcosh_cosh zero_le_one).le⟩
  have hA : MeasurableSet {w | w ∈ Ω ∧ epstein Ω w ∈ hball P 1} := by
    have h1 : {w | w ∈ Ω ∧ epstein Ω w ∈ hball P 1} =
        Ω \ (Ω ∩ (fun w => coshDist P (epstein Ω w)) ⁻¹' Ioi (Real.cosh 1)) := by
      ext w
      constructor
      · rintro ⟨hw, hb⟩
        refine ⟨hw, fun h => ?_⟩
        exact absurd ((hiff w hw).1 hb)
          (not_le.2 (show Real.cosh 1 < coshDist P (epstein Ω w) from h.2))
      · rintro ⟨hw, hb⟩
        exact ⟨hw, (hiff w hw).2 (not_lt.1 fun h => hb ⟨hw, h⟩)⟩
    rw [h1]
    exact hΩo.measurableSet.diff (hg.isOpen_inter_preimage hΩo isOpen_Ioi).measurableSet
  have hU : IsOpen {p : ℂ × ℝ | p.1 ∈ Ω ∧ 0 < p.2 ∧ p.2 < schwarzNorm Ω p.1 ^ 2 / 18} := by
    have hc : ContinuousOn (fun p : ℂ × ℝ => (p.2, schwarzNorm Ω p.1 ^ 2 / 18 - p.2))
        (Ω ×ˢ univ) :=
      continuous_snd.continuousOn.prodMk ((((hsC.comp continuous_fst.continuousOn
        (fun p (hp : p ∈ Ω ×ˢ (univ : Set ℝ)) => hp.1)).pow 2).div_const 18).sub continuous_snd.continuousOn)
    have h := hc.isOpen_inter_preimage (hΩo.prod isOpen_univ) ((isOpen_Ioi (a := (0 : ℝ))).prod (isOpen_Ioi (a := (0 : ℝ))))
    convert h using 1
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ, and_true, mem_preimage, mem_Ioi,
      sub_pos]
  have he : {p : ℂ × ℝ | p.1 ∈ Ω ∧ epstein Ω p.1 ∈ hball P 1 ∧ 0 < p.2 ∧
      p.2 < schwarzNorm Ω p.1 ^ 2 / 18} = ({w | w ∈ Ω ∧ epstein Ω w ∈ hball P 1} ×ˢ univ) ∩
      {p : ℂ × ℝ | p.1 ∈ Ω ∧ 0 < p.2 ∧ p.2 < schwarzNorm Ω p.1 ^ 2 / 18} := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ, and_true]
    tauto
  rw [he]
  exact (hA.prod MeasurableSet.univ).inter hU.measurableSet

/-- Mass–volume helper (MV5): under the Case 1 hypothesis on the side of `Ω`, `E` is injective on
the strip set and maps it into `𝒩 ∩ B(P, 2)` (Lemma 6.3 and `d(E(w,τ), X(w)) = τ`). -/
theorem s06_mv_strip_image : ∀ K : ℝ, 1 ≤ K → ∃ R₀ : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
    ¬ IsLinePair Ω Ωs → ∀ P ∈ UHS,
      (∀ w₀ ∈ Ω, epstein Ω w₀ ∈ hball P 1 → ∀ w' ∈ Ω, poincareDist Ω w₀ w' ≤ R₀ + 2 →
        schwarzNorm Ω w' < 1 / 2) →
      InjOn (fun p : ℂ × ℝ => normalGeod Ω p.1 p.2) {p : ℂ × ℝ | p.1 ∈ Ω ∧
          epstein Ω p.1 ∈ hball P 1 ∧ 0 < p.2 ∧ p.2 < schwarzNorm Ω p.1 ^ 2 / 18} ∧
        (fun p : ℂ × ℝ => normalGeod Ω p.1 p.2) '' {p : ℂ × ℝ | p.1 ∈ Ω ∧
          epstein Ω p.1 ∈ hball P 1 ∧ 0 < p.2 ∧ p.2 < schwarzNorm Ω p.1 ^ 2 / 18} ⊆
          gap Ω Ωs ∩ hball P 2 := by
  intro K hK
  obtain ⟨R₀, hR⟩ := lem_strips K hK
  refine ⟨R₀, fun Ω Ωs hQ hnl P hP hside => ?_⟩
  obtain ⟨hstrip, hdisj⟩ := hR Ω Ωs hQ hnl
  have hJ := s03_b0_jordanPair hQ
  have hΩ := s02_jordanPair_riemannMap hJ
  refine ⟨?_, ?_⟩
  · rintro ⟨w₁, τ₁⟩ ⟨hw₁, hb₁, h₁0, h₁1⟩ ⟨w₂, τ₂⟩ ⟨hw₂, hb₂, h₂0, h₂1⟩ heq
    change normalGeod Ω w₁ τ₁ = normalGeod Ω w₂ τ₂ at heq
    by_cases hw : w₁ = w₂
    · subst hw
      have hd := (lem_normal_b hΩ hw₁).2.1 τ₁ τ₂
      rw [heq] at hd
      have hc : coshDist (normalGeod Ω w₁ τ₂) (normalGeod Ω w₁ τ₂) = 1 := by simp [coshDist]
      have h0 : hdist (normalGeod Ω w₁ τ₂) (normalGeod Ω w₁ τ₂) = 0 := by
        simp only [hdist, hc, Real.arcosh_zero]
      rw [h0] at hd
      have : τ₁ = τ₂ := by
        have := abs_eq_zero.1 hd.symm
        linarith
      rw [this]
    · exact absurd heq (hdisj w₁ hw₁ w₂ hw₂ (hside w₁ hw₁ hb₁) (hside w₂ hw₂ hb₂) hw τ₁ τ₂ h₁0 h₁1
        h₂0 h₂1)
  · rintro _ ⟨⟨w, τ⟩, ⟨hw, hb, h0, h1⟩, rfl⟩
    change normalGeod Ω w τ ∈ gap Ω Ωs ∩ hball P 2
    have hn := lem_normal_b hΩ hw
    have hU : normalGeod Ω w τ ∈ UHS := hn.1 τ
    have htri := s02_hdist_triangle hP hb.1 hU
    have hd2 : hdist (epstein Ω w) (normalGeod Ω w τ) = |0 - τ| := by
      rw [← hn.2.2]
      exact hn.2.1 0 τ
    have hN := eq_nehari hΩ hw
    have hτ : τ ≤ 1 := by nlinarith [hN.1, hN.2]
    have hb2 : hdist P (epstein Ω w) ≤ 1 := hb.2
    rw [hd2, zero_sub, abs_neg, abs_of_pos h0] at htri
    refine ⟨hstrip w hw (hside w hw hb) τ h0 h1, hU, ?_⟩
    show hdist P (normalGeod Ω w τ) ≤ 2
    linarith

/-- Mass–volume helper (MV6), one side of Case 1 of Proposition 6.5: change of variables along
`E` on the strip set (MV1, MV2, MV4, MV5), the factor bound MV3 and Tonelli in `τ` give
`μ_H^Ω(B(P, 1)) ≤ 26 vol(𝒩 ∩ B(P, 2))` (the paper's `48`, with `(7/10)/18 ≥ 1/26`). -/
theorem s06_mv_side : ∀ K : ℝ, 1 ≤ K → ∃ R₀ : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
    ¬ IsLinePair Ω Ωs → ∀ P ∈ UHS,
      (∀ w₀ ∈ Ω, epstein Ω w₀ ∈ hball P 1 → ∀ w' ∈ Ω, poincareDist Ω w₀ w' ≤ R₀ + 2 →
        schwarzNorm Ω w' < 1 / 2) →
      curvMass Ω (epstein Ω ⁻¹' hball P 1) ≤ 26 * hvol (gap Ω Ωs ∩ hball P 2) := by
  intro K hK
  obtain ⟨R₁, hR⟩ := s06_mv_strip_image K hK
  refine ⟨max R₁ 0, fun Ω Ωs hQ hnl P hP hside => ?_⟩
  have hside' : ∀ w₀ ∈ Ω, epstein Ω w₀ ∈ hball P 1 → ∀ w' ∈ Ω, poincareDist Ω w₀ w' ≤ R₁ + 2 →
      schwarzNorm Ω w' < 1 / 2 := fun w₀ hw₀ hb w' hw' hd =>
    hside w₀ hw₀ hb w' hw' (hd.trans (by linarith [le_max_left R₁ 0]))
  obtain ⟨hinj, himg⟩ := hR Ω Ωs hQ hnl P hP hside'
  have hJ := s03_b0_jordanPair hQ
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  have hΩo : IsOpen Ω := s05_jordan_isOpen hJ
  have hP2 : (0 : ℝ) < P.2 := hP
  -- `s < 1/2` on `Π` (the ball of radius `0`)
  have hsmall : ∀ w ∈ Ω, epstein Ω w ∈ hball P 1 → schwarzNorm Ω w < 1 / 2 := by
    intro w hw hb
    obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.1 hΩo w hw
    have h0 := s03_dd_small ⟨f, hf⟩ hr hB (w' := w) (by rw [sub_self, norm_zero]; positivity)
    rw [sub_self, norm_zero, zero_div, mul_zero] at h0
    exact hside w hw hb w hw (h0.trans (by linarith [le_max_right R₁ 0]))
  -- measurability of `Π = Ω ∩ X⁻¹(B(P, 1))`, as in MV4
  have hXU : ∀ w ∈ Ω, 0 < (epstein Ω w).2 := fun w hw => by
    have h := lem_normal_b ⟨f, hf⟩ hw
    rw [← h.2.2]
    exact h.1 0
  have hXC : ContinuousOn (epstein Ω) Ω := (lem_fff_smooth ⟨f, hf⟩).continuousOn
  have hlC : ContinuousOn (poincareDensity Ω) Ω :=
    (s02_contDiffOn_poincareDensity hf).continuousOn
  have hsC : ContinuousOn (schwarzNorm Ω) Ω :=
    ((s02_contDiffOn_invFun hf).2.2.2.continuousOn.norm.div (hlC.pow 2)
      (fun x hx => pow_ne_zero 2 (s02_poincareDensity_pos ⟨f, hf⟩ hx).ne')).congr
      (fun x hx => eq_def_s hf hx)
  have hg : ContinuousOn (fun w => coshDist P (epstein Ω w)) Ω := by
    unfold coshDist
    have h1 : ContinuousOn (fun w => (epstein Ω w).1) Ω := continuous_fst.comp_continuousOn hXC
    have h2 : ContinuousOn (fun w => (epstein Ω w).2) Ω := continuous_snd.comp_continuousOn hXC
    exact continuousOn_const.add ((((continuousOn_const.sub h1).norm.pow 2).add
      ((continuousOn_const.sub h2).pow 2)).div (continuousOn_const.mul h2)
      fun w hw => (mul_pos (mul_pos two_pos hP2) (hXU w hw)).ne')
  have hiff : ∀ w ∈ Ω, epstein Ω w ∈ hball P 1 ↔ coshDist P (epstein Ω w) ≤ Real.cosh 1 := by
    intro w hw
    have hc1 : 0 < coshDist P (epstein Ω w) := by
      have h0 := hXU w hw
      unfold coshDist
      have : 0 ≤ (‖P.1 - (epstein Ω w).1‖ ^ 2 + (P.2 - (epstein Ω w).2) ^ 2) /
          (2 * P.2 * (epstein Ω w).2) :=
        div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_pos (mul_pos two_pos hP2) h0).le
      linarith
    have hch : 0 < Real.cosh 1 := Real.cosh_pos 1
    constructor
    · rintro ⟨-, hd⟩
      exact (Real.arcosh_le_arcosh hc1 hch).1 (hd.trans (Real.arcosh_cosh zero_le_one).symm.le)
    · intro h
      exact ⟨hXU w hw, ((Real.arcosh_le_arcosh hc1 hch).2 h).trans (Real.arcosh_cosh zero_le_one).le⟩
  have hA : MeasurableSet {w | w ∈ Ω ∧ epstein Ω w ∈ hball P 1} := by
    have h1 : {w | w ∈ Ω ∧ epstein Ω w ∈ hball P 1} =
        Ω \ (Ω ∩ (fun w => coshDist P (epstein Ω w)) ⁻¹' Ioi (Real.cosh 1)) := by
      ext w
      constructor
      · rintro ⟨hw, hb⟩
        refine ⟨hw, fun h => ?_⟩
        exact absurd ((hiff w hw).1 hb)
          (not_le.2 (show Real.cosh 1 < coshDist P (epstein Ω w) from h.2))
      · rintro ⟨hw, hb⟩
        exact ⟨hw, (hiff w hw).2 (not_lt.1 fun h => hb ⟨hw, h⟩)⟩
    rw [h1]
    exact hΩo.measurableSet.diff (hg.isOpen_inter_preimage hΩo isOpen_Ioi).measurableSet
  -- measurable extensions of `λ` and `s` by `0` off `Ω`
  classical
  have hlm : Measurable (Ω.piecewise (poincareDensity Ω) (fun _ => (0 : ℝ))) :=
    hlC.measurable_piecewise continuousOn_const hΩo.measurableSet
  set lt := Ω.piecewise (poincareDensity Ω) (fun _ => (0 : ℝ)) with hlt
  set st := Ω.piecewise (schwarzNorm Ω) (fun _ => (0 : ℝ)) with hst
  have hltw : ∀ w ∈ Ω, lt w = poincareDensity Ω w := fun w hw => Set.piecewise_eq_of_mem _ _ _ hw
  have hstw : ∀ w ∈ Ω, st w = schwarzNorm Ω w := fun w hw => Set.piecewise_eq_of_mem _ _ _ hw
  -- the strip set
  obtain ⟨S, hS⟩ : ∃ S : Set (ℂ × ℝ), S = {p : ℂ × ℝ | p.1 ∈ Ω ∧ epstein Ω p.1 ∈ hball P 1 ∧
      0 < p.2 ∧ p.2 < schwarzNorm Ω p.1 ^ 2 / 18} := ⟨_, rfl⟩
  have hSm : MeasurableSet S := hS ▸ s06_mv_strip_measurable hJ hP
  rw [← hS] at hinj himg
  -- (1) the curvature mass as an integral over `Π`
  have h1 : curvMass Ω (epstein Ω ⁻¹' hball P 1) =
      ∫⁻ w in {w | w ∈ Ω ∧ epstein Ω w ∈ hball P 1},
        ENNReal.ofReal (schwarzNorm Ω w ^ 2 * poincareDensity Ω w ^ 2) := by
    unfold curvMass
    rw [withDensity_apply', Measure.restrict_restrict' hΩo.measurableSet,
      show epstein Ω ⁻¹' hball P 1 ∩ Ω = {w | w ∈ Ω ∧ epstein Ω w ∈ hball P 1} from
        Set.ext fun w => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩]
  -- (2) `s²λ² ≤ 26 · (7/10)λ² · s²/18`
  have h2 : ∫⁻ w in {w | w ∈ Ω ∧ epstein Ω w ∈ hball P 1},
        ENNReal.ofReal (schwarzNorm Ω w ^ 2 * poincareDensity Ω w ^ 2) ≤
      26 * ∫⁻ w in {w | w ∈ Ω ∧ epstein Ω w ∈ hball P 1},
        ENNReal.ofReal (7 / 10 * lt w ^ 2) * ENNReal.ofReal (st w ^ 2 / 18) := by
    rw [← lintegral_const_mul' _ _ (by norm_num : (26 : ℝ≥0∞) ≠ ∞)]
    refine setLIntegral_mono' hA fun w hw => ?_
    rw [hltw w hw.1, hstw w hw.1, ← ENNReal.ofReal_mul
      (show (0 : ℝ) ≤ 7 / 10 * poincareDensity Ω w ^ 2 by positivity),
      show (26 : ℝ≥0∞) = ENNReal.ofReal 26 by norm_num,
      ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 26 by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [mul_nonneg (sq_nonneg (schwarzNorm Ω w)) (sq_nonneg (poincareDensity Ω w))]
  -- (3) Tonelli in `τ`: the fibre of `S` over `w ∈ Π` is `(0, s²/18)`
  have hFib : ∀ x : ℂ, ∫⁻ y : ℝ,
      S.indicator (fun p : ℂ × ℝ => ENNReal.ofReal (7 / 10 * lt p.1 ^ 2)) (x, y) =
      {w | w ∈ Ω ∧ epstein Ω w ∈ hball P 1}.indicator
        (fun w => ENNReal.ofReal (7 / 10 * lt w ^ 2) * ENNReal.ofReal (st w ^ 2 / 18)) x := by
    intro x
    by_cases hx : x ∈ Ω ∧ epstein Ω x ∈ hball P 1
    · rw [Set.indicator_of_mem (show x ∈ {w | w ∈ Ω ∧ epstein Ω w ∈ hball P 1} from hx)]
      have he : (fun y : ℝ =>
          S.indicator (fun p : ℂ × ℝ => ENNReal.ofReal (7 / 10 * lt p.1 ^ 2)) (x, y)) =
          (Ioo 0 (schwarzNorm Ω x ^ 2 / 18)).indicator
            (fun _ => ENNReal.ofReal (7 / 10 * lt x ^ 2)) := by
        ext y
        by_cases hy : y ∈ Ioo 0 (schwarzNorm Ω x ^ 2 / 18)
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem
            (show (x, y) ∈ S by rw [hS]; exact ⟨hx.1, hx.2, hy.1, hy.2⟩)]
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem
            (show (x, y) ∉ S by rw [hS]; exact fun h => hy ⟨h.2.2.1, h.2.2.2⟩)]
      rw [he, lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo, sub_zero,
        hstw x hx.1]
    · rw [Set.indicator_of_notMem (show x ∉ {w | w ∈ Ω ∧ epstein Ω w ∈ hball P 1} from hx)]
      have he : (fun y : ℝ =>
          S.indicator (fun p : ℂ × ℝ => ENNReal.ofReal (7 / 10 * lt p.1 ^ 2)) (x, y)) =
          fun _ => 0 := by
        ext y
        exact Set.indicator_of_notMem
          (show (x, y) ∉ S by rw [hS]; exact fun h => hx ⟨h.1, h.2.1⟩) _
      rw [he, lintegral_zero]
  have hGm : Measurable (fun p : ℂ × ℝ => ENNReal.ofReal (7 / 10 * lt p.1 ^ 2)) :=
    ENNReal.measurable_ofReal.comp (((hlm.comp measurable_fst).pow_const 2).const_mul _)
  have h3 : ∫⁻ w in {w | w ∈ Ω ∧ epstein Ω w ∈ hball P 1},
        ENNReal.ofReal (7 / 10 * lt w ^ 2) * ENNReal.ofReal (st w ^ 2 / 18) =
      ∫⁻ p in S, ENNReal.ofReal (7 / 10 * lt p.1 ^ 2) := by
    rw [← lintegral_indicator hA, ← lintegral_indicator hSm, Measure.volume_eq_prod,
      lintegral_prod _ (hGm.indicator hSm).aemeasurable]
    exact (lintegral_congr fun x => hFib x).symm
  -- (4) change of variables along `E`, with `|det DE| ξ⁻³ = λ² (cosh²τ - s²e^{2τ}) ≥ (7/10)λ²`
  have hsubU : (fun p : ℂ × ℝ => normalGeod Ω p.1 p.2) '' S ⊆ UHS := fun x hx => (himg hx).1.1
  have h4 : ∫⁻ p in S, ENNReal.ofReal (7 / 10 * lt p.1 ^ 2) ≤
      hvol ((fun p : ℂ × ℝ => normalGeod Ω p.1 p.2) '' S) := by
    have : (volume : Measure (ℂ × ℝ)).IsAddHaarMeasure := by
      rw [Measure.volume_eq_prod]
      infer_instance
    unfold hvol
    rw [withDensity_apply', Measure.restrict_restrict_of_subset hsubU,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm
        (fun p hp => (s06_mv_hasFDerivAt hJ (by rw [hS] at hp; exact hp.1) p.2).hasFDerivWithinAt)
        hinj]
    refine setLIntegral_mono' hSm fun p hp => ?_
    rw [hS] at hp
    obtain ⟨hw, hb, h0, h1⟩ := hp
    have hs0 := (eq_nehari ⟨f, hf⟩ hw).1
    have hs2 := hsmall p.1 hw hb
    have hss : schwarzNorm Ω p.1 ^ 2 < 1 / 4 := by nlinarith
    have hl0 := s02_poincareDensity_pos ⟨f, hf⟩ hw
    have hq3 : (normalGeod Ω p.1 p.2).2 ^ 3 ≠ 0 := (pow_pos (s02_normalGeod_pos Ω p.1 hl0 p.2) 3).ne'
    have hfac := s06_mv_factor_ge hs0 hs2 h0.le (by linarith)
    rw [← ENNReal.ofReal_mul (abs_nonneg _), s06_mv_det hJ hw (by linarith) p.2, hltw p.1 hw]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [abs_of_pos (by linarith :
      (0 : ℝ) < Real.cosh p.2 ^ 2 - schwarzNorm Ω p.1 ^ 2 * Real.exp p.2 ^ 2),
      mul_right_comm, mul_inv_cancel₀ hq3, one_mul]
    nlinarith [sq_nonneg (poincareDensity Ω p.1)]
  calc curvMass Ω (epstein Ω ⁻¹' hball P 1) = _ := h1
    _ ≤ _ := h2
    _ = 26 * ∫⁻ p in S, ENNReal.ofReal (7 / 10 * lt p.1 ^ 2) := by rw [h3]
    _ ≤ 26 * hvol ((fun p : ℂ × ℝ => normalGeod Ω p.1 p.2) '' S) := by gcongr
    _ ≤ 26 * hvol (gap Ω Ωs ∩ hball P 2) := by gcongr

/-- Mass–volume helper (MV7), **Case 1 of Proposition 6.5** (sec06-lower.tex:115): if `s < 1/2` on
the `ρ`-neighbourhood of radius `R₀ + 2` of `Π = X⁻¹(B(P,1))`, and `s* < 1/2` likewise on the side
of `Ω*`, then `μ_H(B(P, 1)) ≤ 52 vol(𝒩 ∩ B(P, 2))`.  Relation to the paper: its Case 1 assumes
`s < 1/2` on `N_{L₀}(Π)` with `L₀ = R₀ + 3`, which contains every `B̄_ρ(w₀, R₀ + 2)` with `w₀ ∈ Π`; so
the hypothesis here is weaker.  The paper's constant `96` (one side, `1/48`, larger side kept)
improves to `52` here: each side gives `26` (the factor bound `7/10` and `1/18`) and the two sides
are summed. -/
theorem s06_mv_case1 : ∀ K : ℝ, 1 ≤ K → ∃ R₀ : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
    ¬ IsLinePair Ω Ωs → ∀ P ∈ UHS,
      (∀ w₀ ∈ Ω, epstein Ω w₀ ∈ hball P 1 → ∀ w' ∈ Ω, poincareDist Ω w₀ w' ≤ R₀ + 2 →
        schwarzNorm Ω w' < 1 / 2) →
      (∀ z₀ ∈ Ωs, epstein Ωs z₀ ∈ hball P 1 → ∀ z' ∈ Ωs, poincareDist Ωs z₀ z' ≤ R₀ + 2 →
        schwarzNorm Ωs z' < 1 / 2) →
      curvMass Ω (epstein Ω ⁻¹' hball P 1) + curvMass Ωs (epstein Ωs ⁻¹' hball P 1) ≤
        52 * hvol (gap Ω Ωs ∩ hball P 2) := by
  intro K hK
  obtain ⟨R₀, hR⟩ := s06_mv_side K hK
  refine ⟨R₀, fun Ω Ωs hQ hnl P hP h1 h2 => ?_⟩
  have e1 := hR Ω Ωs hQ hnl P hP h1
  have e2 := hR Ωs Ω (s03_qce_swap hQ) (s03_cr_line hnl) P hP h2
  have hg : gap Ωs Ω = gap Ω Ωs := by
    unfold gap
    rw [union_comm]
  rw [hg] at e2
  calc curvMass Ω (epstein Ω ⁻¹' hball P 1) + curvMass Ωs (epstein Ωs ⁻¹' hball P 1)
      ≤ 26 * hvol (gap Ω Ωs ∩ hball P 2) + 26 * hvol (gap Ω Ωs ∩ hball P 2) := add_le_add e1 e2
    _ = 52 * hvol (gap Ω Ωs ∩ hball P 2) := by
      rw [← add_mul]
      norm_num

-- Moved byte-identically from `S09_Ambient.lean` (2026-11-04, leader-approved) so that Claim 6.6 can use them;
-- S09 imports S06 and keeps using them.

/-- The real determinant of multiplication by `c` on `ℂ` is `|c|²`. -/
theorem s09_det_cmul (c : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq,
    Complex.normSq_eq_norm_sq]

theorem s09_affExt_meas (a b : ℂ) (ha : a ≠ 0) :
    MeasurableEmbedding (fun q : ℂ × ℝ => (a * q.1 + b, ‖a‖ * q.2)) := by
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  let e : (ℂ × ℝ) ≃ᵐ (ℂ × ℝ) :=
    { toFun := fun q => (a * q.1 + b, ‖a‖ * q.2)
      invFun := fun q => ((q.1 - b) / a, q.2 / ‖a‖)
      left_inv := fun q => by
        ext
        · simp only
          field_simp
          ring
        · simp only
          field_simp
      right_inv := fun q => by
        ext
        · simp only
          field_simp
          ring
        · simp only
          field_simp
      measurable_toFun := by
        show Measurable fun q : ℂ × ℝ => (a * q.1 + b, ‖a‖ * q.2)
        fun_prop
      measurable_invFun := by
        show Measurable fun q : ℂ × ℝ => ((q.1 - b) / a, q.2 / ‖a‖)
        fun_prop }
  exact e.measurableEmbedding

theorem s09_affExt_surj (a b : ℂ) (ha : a ≠ 0) :
    Function.Surjective (fun q : ℂ × ℝ => (a * q.1 + b, ‖a‖ * q.2)) := by
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  intro q
  refine ⟨((q.1 - b) / a, q.2 / ‖a‖), ?_⟩
  ext
  · simp only
    field_simp
    ring
  · simp only
    field_simp

theorem s09_affExt_UHS (a b : ℂ) (ha : a ≠ 0) :
    (fun q : ℂ × ℝ => (a * q.1 + b, ‖a‖ * q.2)) ⁻¹' UHS = UHS := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  ext q
  show 0 < ‖a‖ * q.2 ↔ 0 < q.2
  constructor
  · intro h
    exact pos_of_mul_pos_right h hna.le
  · intro h
    exact mul_pos hna h

/-- `hvol` is invariant under the Poincaré extension of `z ↦ a z + b`. -/
theorem s09_hvol_map_aff (a b : ℂ) (ha : a ≠ 0) :
    Measure.map (fun q : ℂ × ℝ => (a * q.1 + b, ‖a‖ * q.2)) hvol = hvol := by
  set T : ℂ × ℝ → ℂ × ℝ := fun q => (a * q.1 + b, ‖a‖ * q.2) with hTdef
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hT := s09_affExt_meas a b ha
  have hU : MeasurableSet UHS := measurableSet_lt measurable_const measurable_snd
  have hL : ∀ q : ℂ × ℝ, HasFDerivAt T
      (((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ).prodMap
        (ContinuousLinearMap.toSpanSingleton ℝ ‖a‖)) q := by
    intro q
    have h1 : HasDerivAt (fun z : ℂ => a * z + b) a q.1 :=
      ((hasDerivAt_id q.1).const_mul a).add_const b |>.congr_deriv (mul_one a)
    have h2 : HasDerivAt (fun t : ℝ => ‖a‖ * t) ‖a‖ q.2 :=
      (hasDerivAt_id q.2).const_mul ‖a‖ |>.congr_deriv (mul_one _)
    exact (h1.hasFDerivAt.restrictScalars ℝ).prodMap q h2.hasFDerivAt
  have hdet : (((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ).prodMap
      (ContinuousLinearMap.toSpanSingleton ℝ ‖a‖)).det = ‖a‖ ^ 3 := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap]
    have := s09_det_cmul a
    rw [ContinuousLinearMap.det] at this
    rw [this]
    simp
    ring
  have : (volume : Measure (ℂ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  ext S hS
  have hpre : MeasurableSet (T ⁻¹' S ∩ UHS) := (hT.measurable hS).inter hU
  rw [Measure.map_apply hT.measurable hS]
  unfold hvol
  rw [withDensity_apply _ hS, withDensity_apply _ (hT.measurable hS),
    Measure.restrict_restrict hS, Measure.restrict_restrict (hT.measurable hS)]
  have hset : S ∩ UHS = T '' (T ⁻¹' S ∩ UHS) := by
    conv_rhs => rw [← s09_affExt_UHS a b ha]
    rw [← preimage_inter, image_preimage_eq _ (s09_affExt_surj a b ha)]
  rw [hset, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hpre
    (fun q _ => (hL q).hasFDerivWithinAt) hT.injective.injOn]
  refine (setLIntegral_congr_fun hpre (fun q hq => ?_)).symm
  have hq : 0 < q.2 := hq.2
  rw [hdet, abs_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [hTdef]
  dsimp only
  field_simp

/-- Horoballs are natural under the affine extension. -/
theorem s09_horoUnion_aff (Ω : Set ℂ) (hΩ : ∃ f, IsConformalOnto f unitDisc Ω) (a b : ℂ)
    (ha : a ≠ 0) :
    (fun q : ℂ × ℝ => (a * q.1 + b, ‖a‖ * q.2)) ⁻¹' horoUnion ((fun z => a * z + b) '' Ω) =
      horoUnion Ω := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have key : ∀ q : ℂ × ℝ, 0 < q.2 → ∀ w ∈ Ω,
      horoPhi ((fun z => a * z + b) '' Ω) (a * q.1 + b, ‖a‖ * q.2) (a * w + b) =
        horoPhi Ω q w := by
    intro q hq w hw
    have hl := (subsec_poincare_natural_affine hΩ (b := b) ha hw).1
    unfold horoPhi
    dsimp only
    rw [show a * q.1 + b - (a * w + b) = a * (q.1 - w) by ring, norm_mul, ← hl]
    field_simp
  ext q
  simp only [mem_preimage, horoUnion, mem_iUnion₂, horoball, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, hq1, hq2⟩
    have hq : 0 < q.2 := pos_of_mul_pos_right (show 0 < ‖a‖ * q.2 from hq1) hna.le
    exact ⟨w, hw, hq, by rwa [key q hq w hw] at hq2⟩
  · rintro ⟨w, hw, hq, hq2⟩
    refine ⟨a * w + b, ⟨w, hw, rfl⟩, ?_, ?_⟩
    · show 0 < ‖a‖ * q.2
      exact mul_pos hna hq
    · rwa [key q hq w hw]

/-- Claim-6.6 helper (CL1): a subsequence of a locally uniformly convergent sequence converges
locally uniformly. -/
theorem s06_cl_tlu_subseq {g : ℕ → ℂ → ℂ} {gL : ℂ → ℂ} {s : Set ℂ}
    (h : TendstoLocallyUniformlyOn g gL atTop s) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    TendstoLocallyUniformlyOn (fun n => g (ψ n)) gL atTop s := by
  intro u hu x hx
  obtain ⟨t, ht, hev⟩ := h u hu x hx
  exact ⟨t, ht, hψ.tendsto_atTop.eventually hev⟩

/-- Claim-6.6 helper (CL2): the Schwarzian norm of a half-plane vanishes (`s02_halfplane`). -/
theorem s06_cl_line_s {Ω Ωs : Set ℂ} (hl : IsLinePair Ω Ωs) {w : ℂ} (hw : w ∈ Ω) :
    schwarzNorm Ω w = 0 := by
  obtain ⟨a, b, ha, rfl, rfl⟩ := hl
  exact (s02_halfplane a b ha 1 (Or.inl rfl) {z | 0 < (a * z + b).im} (fun z => by simp)).1 w hw

/-- Claim-6.6 helper (CL3): a closed `d_𝔻`-ball about `0` lies in a closed Euclidean disk of
radius `< 1`. -/
theorem s06_cl_disk_confine (R : ℝ) : ∃ r : ℝ, r < 1 ∧ ∀ ζ : ℂ, ζ ∈ unitDisc →
    diskDist 0 ζ ≤ R → ‖ζ‖ ≤ r := by
  have hc := Real.cosh_pos R
  have hc1 := Real.one_le_cosh R
  refine ⟨Real.sqrt ((Real.cosh R - 1) / (Real.cosh R + 1)), ?_, fun ζ hζ hd => ?_⟩
  · rw [Real.sqrt_lt' one_pos, one_pow, div_lt_one (by linarith)]
    linarith
  · have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
    have h1t : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
    have hval : diskCoshDist 0 ζ = 1 + 2 * ‖ζ‖ ^ 2 / (1 - ‖ζ‖ ^ 2) := by
      unfold diskCoshDist
      rw [zero_sub, norm_neg, norm_zero]
      ring_nf
    have hX : 1 ≤ diskCoshDist 0 ζ := by
      rw [hval]
      have : 0 ≤ 2 * ‖ζ‖ ^ 2 / (1 - ‖ζ‖ ^ 2) := by positivity
      linarith
    have hle : diskCoshDist 0 ζ ≤ Real.cosh R := by
      rw [← Real.cosh_arcosh hX]
      refine Real.cosh_le_cosh.2 ?_
      rw [abs_of_nonneg (Real.arcosh_nonneg hX)]
      exact hd.trans (le_abs_self R)
    rw [hval] at hle
    have h2 : 2 * ‖ζ‖ ^ 2 ≤ (Real.cosh R - 1) * (1 - ‖ζ‖ ^ 2) := by
      rw [← div_le_iff₀ h1t]
      linarith
    rw [Real.le_sqrt (norm_nonneg _), le_div_iff₀ (by linarith)]
    · nlinarith
    · exact div_nonneg (by linarith) (by linarith)

/-- Claim-6.6 helper (CL4): on `ℍ³`, Euclidean convergence is convergence in `hdist`. -/
theorem s06_cl_hdist_tendsto {q : ℕ → ℂ × ℝ} {a : ℂ × ℝ} (ha : a ∈ UHS)
    (hq : ∀ n, q n ∈ UHS) :
    Tendsto q atTop (𝓝 a) ↔ Tendsto (fun n => hdist (q n) a) atTop (𝓝 0) := by
  have ha2 : 0 < a.2 := ha
  have hge : ∀ n, 1 ≤ coshDist (q n) a := fun n => by
    have hq2 : 0 < (q n).2 := hq n
    unfold coshDist
    have : 0 ≤ (‖(q n).1 - a.1‖ ^ 2 + ((q n).2 - a.2) ^ 2) / (2 * (q n).2 * a.2) := by positivity
    linarith
  constructor
  · intro h
    have hcA : ContinuousAt (fun p : ℂ × ℝ => coshDist p a) a := by
      unfold coshDist
      exact continuousAt_const.add ((((continuous_fst.sub continuous_const).norm.pow 2).add
        ((continuous_snd.sub continuous_const).pow 2)).continuousAt.div
        ((continuous_const.mul continuous_snd).mul continuous_const).continuousAt
        (by positivity))
    have h1 : Tendsto (fun n => coshDist (q n) a) atTop (𝓝 1) := by
      have := hcA.tendsto.comp h
      have e : coshDist a a = 1 := by simp [coshDist]
      rw [e] at this
      exact this
    have h2 := ((Real.continuousOn_arcosh 1 (Set.mem_Ici.2 le_rfl)).tendsto).comp
      (tendsto_nhdsWithin_iff.2 ⟨h1, Eventually.of_forall hge⟩)
    rw [Real.arcosh_zero] at h2
    exact h2
  · intro h
    have hc : Tendsto (fun n => coshDist (q n) a) atTop (𝓝 1) := by
      have := (Real.continuous_cosh.tendsto 0).comp h
      rw [Real.cosh_zero] at this
      refine this.congr fun n => ?_
      show Real.cosh (Real.arcosh _) = _
      exact Real.cosh_arcosh (hge n)
    -- `S n = |Δ₁|² + Δ₂² = (cosh d - 1) · 2 ξₙ ξ`, with `ξₙ ≤ 4ξ` eventually
    have hS : Tendsto (fun n => ‖(q n).1 - a.1‖ ^ 2 + ((q n).2 - a.2) ^ 2) atTop (𝓝 0) := by
      have hlim : Tendsto (fun n => (coshDist (q n) a - 1) * (8 * a.2 ^ 2)) atTop (𝓝 0) := by
        have := (hc.sub_const 1).mul_const (8 * a.2 ^ 2)
        rwa [sub_self, zero_mul] at this
      refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hlim
      filter_upwards [(tendsto_order.1 hc).2 2 (by norm_num)] with n hn
      have hq2 : 0 < (q n).2 := hq n
      have he : ‖(q n).1 - a.1‖ ^ 2 + ((q n).2 - a.2) ^ 2 =
          (coshDist (q n) a - 1) * (2 * (q n).2 * a.2) := by
        unfold coshDist
        field_simp
        ring
      have hden : 0 < 2 * (q n).2 * a.2 := by positivity
      have hnum : ((q n).2 - a.2) ^ 2 ≤ 2 * (q n).2 * a.2 := by
        have h0 : 0 ≤ ‖(q n).1 - a.1‖ ^ 2 := sq_nonneg _
        have : (coshDist (q n) a - 1) * (2 * (q n).2 * a.2) ≤ 1 * (2 * (q n).2 * a.2) :=
          mul_le_mul_of_nonneg_right (by linarith) hden.le
        linarith
      have hq4 : (q n).2 ≤ 4 * a.2 := by nlinarith
      rw [he]
      have h1 := hge n
      have : 2 * (q n).2 * a.2 ≤ 8 * a.2 ^ 2 := by nlinarith
      nlinarith
    have hsq : Tendsto (fun n => Real.sqrt (‖(q n).1 - a.1‖ ^ 2 + ((q n).2 - a.2) ^ 2)) atTop
        (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hS
      rwa [Real.sqrt_zero] at this
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      hsq)
    rw [Real.le_sqrt (norm_nonneg _), Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
    rcases le_total ‖(q n).1 - a.1‖ |(q n).2 - a.2| with h' | h'
    · rw [max_eq_right h', sq_abs]
      nlinarith [sq_nonneg ‖(q n).1 - a.1‖]
    · rw [max_eq_left h']
      nlinarith [sq_nonneg ((q n).2 - a.2)]
    · positivity

/-- Claim-6.6 helper (CL5): closed hyperbolic balls are sequentially compact. -/
theorem s06_cl_hball_seq {P : ℂ × ℝ} (hP : P ∈ UHS) {r : ℝ} {q : ℕ → ℂ × ℝ}
    (hq : ∀ n, q n ∈ hball P r) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ q₀ ∈ hball P r, Tendsto (fun n => q (ψ n)) atTop (𝓝 q₀) := by
  have hP2 : 0 < P.2 := hP
  have hch := Real.cosh_pos r
  obtain ⟨q₀, hq₀B, φ, hφ, hlim⟩ :=
    ((isCompact_closedBall P.1 (Real.sqrt (4 * Real.cosh r * (Real.cosh r - 1) * P.2 ^ 2))).prod
      (isCompact_Icc (a := P.2 / (2 * Real.cosh r)) (b := 2 * Real.cosh r * P.2))).tendsto_subseq
      (fun n => s05_dd_hball_box hP (hq n))
  have hq₀U : q₀ ∈ UHS := by
    have h := (mem_prod.1 hq₀B).2.1
    show 0 < q₀.2
    exact lt_of_lt_of_le (by positivity) h
  refine ⟨φ, hφ, q₀, ⟨hq₀U, ?_⟩, hlim⟩
  have hd := (s06_cl_hdist_tendsto hq₀U (fun n => (hq (φ n)).1)).1 hlim
  have h2 := hd.const_add r
  rw [add_zero] at h2
  exact ge_of_tendsto' h2 fun n =>
    (s02_hdist_triangle hP (hq (φ n)).1 hq₀U).trans (by linarith [(hq (φ n)).2])

/-- Claim-6.6 helper (CL6): closed hyperbolic balls are Euclidean convex
(`d(P, Q) ≤ r ⟺ |P₁ - Q₁|² + (P₂ - Q₂)² ≤ 2(cosh r - 1) P₂ Q₂`). -/
theorem s06_cl_hball_convex {P : ℂ × ℝ} (hP : P ∈ UHS) (r : ℝ) : Convex ℝ (hball P r) := by
  have hP2 : 0 < P.2 := hP
  have hge : ∀ Q : ℂ × ℝ, 0 < Q.2 → 1 ≤ coshDist P Q := fun Q hQ2 => by
    unfold coshDist
    have : 0 ≤ (‖P.1 - Q.1‖ ^ 2 + (P.2 - Q.2) ^ 2) / (2 * P.2 * Q.2) := by positivity
    linarith
  by_cases hr : 0 ≤ r
  swap
  · have he : hball P r = ∅ := by
      ext Q
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨hQ, hd⟩
      have := Real.arcosh_nonneg (hge Q hQ)
      unfold hdist at hd
      linarith
    rw [he]
    exact convex_empty
  have hc := Real.cosh_pos r
  have heq : hball P r = {Q : ℂ × ℝ | 0 < Q.2 ∧
      ‖P.1 - Q.1‖ ^ 2 + (P.2 - Q.2) ^ 2 ≤ 2 * (Real.cosh r - 1) * P.2 * Q.2} := by
    ext Q
    constructor
    · rintro ⟨hQ, hd⟩
      have hQ2 : 0 < Q.2 := hQ
      have hcd : coshDist P Q ≤ Real.cosh r :=
        (Real.arcosh_le_arcosh (by linarith [hge Q hQ2]) hc).1
          (hd.trans (Real.arcosh_cosh hr).symm.le)
      unfold coshDist at hcd
      have hden : 0 < 2 * P.2 * Q.2 := by positivity
      have h := (div_le_iff₀ hden).1 (by linarith :
        (‖P.1 - Q.1‖ ^ 2 + (P.2 - Q.2) ^ 2) / (2 * P.2 * Q.2) ≤ Real.cosh r - 1)
      exact ⟨hQ2, by linarith⟩
    · rintro ⟨hQ2, hN⟩
      refine ⟨hQ2, ?_⟩
      have hcd : coshDist P Q ≤ Real.cosh r := by
        unfold coshDist
        have hden : 0 < 2 * P.2 * Q.2 := by positivity
        have : (‖P.1 - Q.1‖ ^ 2 + (P.2 - Q.2) ^ 2) / (2 * P.2 * Q.2) ≤ Real.cosh r - 1 := by
          rw [div_le_iff₀ hden]
          linarith
        linarith
      show Real.arcosh (coshDist P Q) ≤ r
      exact ((Real.arcosh_le_arcosh (by linarith [hge Q hQ2]) hc).2 hcd).trans
        (Real.arcosh_cosh hr).le
  rw [heq]
  intro x hx y hy s t hs ht hst
  obtain rfl : t = 1 - s := by linarith
  obtain ⟨hx2, hxN⟩ := hx
  obtain ⟨hy2, hyN⟩ := hy
  have e1 : P.1 - (s • x.1 + (1 - s) • y.1) = s • (P.1 - x.1) + (1 - s) • (P.1 - y.1) := by
    have h : P.1 = s • P.1 + (1 - s) • P.1 := by rw [← add_smul, add_sub_cancel, one_smul]
    conv_lhs => rw [h]
    rw [smul_sub, smul_sub]
    abel
  have hn : ‖P.1 - (s • x.1 + (1 - s) • y.1)‖ ≤ s * ‖P.1 - x.1‖ + (1 - s) * ‖P.1 - y.1‖ := by
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
  have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  refine ⟨?_, ?_⟩
  · show 0 < s * x.2 + (1 - s) * y.2
    have hm := lt_min hx2 hy2
    have h1 := mul_le_mul_of_nonneg_left (min_le_left x.2 y.2) hs
    have h2 := mul_le_mul_of_nonneg_left (min_le_right x.2 y.2) ht
    nlinarith
  · show ‖P.1 - (s • x.1 + (1 - s) • y.1)‖ ^ 2 + (P.2 - (s * x.2 + (1 - s) * y.2)) ^ 2 ≤
      2 * (Real.cosh r - 1) * P.2 * (s * x.2 + (1 - s) * y.2)
    set u := ‖P.1 - x.1‖
    set v := ‖P.1 - y.1‖
    have c1 : (s * u + (1 - s) * v) ^ 2 ≤ s * u ^ 2 + (1 - s) * v ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg (u - v))]
    have c2 : (P.2 - (s * x.2 + (1 - s) * y.2)) ^ 2 ≤
        s * (P.2 - x.2) ^ 2 + (1 - s) * (P.2 - y.2) ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg ((P.2 - x.2) - (P.2 - y.2)))]
    have h1 := mul_le_mul_of_nonneg_left hxN hs
    have h2 := mul_le_mul_of_nonneg_left hyN ht
    nlinarith

/-- Claim-6.6 helper (CL7), the limit step of the paper's uniform-convergence argument: if conformal
maps `h n : 𝔻 → Ω n` (sides of non-circular `K`-quasi pairs) converge locally uniformly on `𝔻` to a
conformal `hL : 𝔻 → ΩL`, `q n → q₀ ∈ ℍ³` and `q n ∈ B_{w n}` with `w n ∈ Ω n`, then `q₀ ∈ U_L`.
The points `w n = h n (ζ n)` are confined to `|ζ| ≤ r < 1` by `lem_busemann` and `lem_competing`
(anchor `X_n(h n 0) → X_L(hL 0)`, CL3, CL4), and `s03_wc_jets` passes `Φ ≤ 1` to the limit along a
subsequence. -/
theorem s06_cl_limit_horo {K : ℝ} {Ω Ωs : ℕ → Set ℂ} {ΩL : Set ℂ} {h : ℕ → ℂ → ℂ}
    {hL : ℂ → ℂ} (hpair : ∀ n, IsKQuasiPair (Ω n) (Ωs n) K)
    (hnl : ∀ n, ¬ IsLinePair (Ω n) (Ωs n))
    (hc : ∀ n, IsConformalOnto (h n) unitDisc (Ω n)) (hcL : IsConformalOnto hL unitDisc ΩL)
    (hconv : TendstoLocallyUniformlyOn h hL atTop unitDisc)
    {q : ℕ → ℂ × ℝ} {q₀ : ℂ × ℝ} (hqU : ∀ n, q n ∈ UHS) (hq₀ : q₀ ∈ UHS)
    (hq : Tendsto q atTop (𝓝 q₀)) {w : ℕ → ℂ} (hw : ∀ n, w n ∈ Ω n)
    (hΦ : ∀ n, horoPhi (Ω n) (q n) (w n) ≤ 1) :
    q₀ ∈ horoUnion ΩL := by
  obtain ⟨C, hC⟩ := lem_competing K
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hXU : ∀ {Ω' : Set ℂ} {f : ℂ → ℂ}, IsConformalOnto f unitDisc Ω' → ∀ x ∈ Ω',
      epstein Ω' x ∈ UHS := fun hf x hx => by
    have h := lem_normal_b ⟨_, hf⟩ hx
    rw [← h.2.2]
    exact h.1 0
  have hdnn : ∀ p p' : ℂ × ℝ, p ∈ UHS → p' ∈ UHS → 0 ≤ hdist p p' := fun p p' hp hp' => by
    have h2 : 0 < p.2 := hp
    have h2' : 0 < p'.2 := hp'
    show 0 ≤ Real.arcosh (coshDist p p')
    apply Real.arcosh_nonneg
    unfold coshDist
    have : 0 ≤ (‖p.1 - p'.1‖ ^ 2 + (p.2 - p'.2) ^ 2) / (2 * p.2 * p'.2) := by positivity
    linarith
  have hmem : ∀ n, h n 0 ∈ Ω n := fun n => by
    rw [← (hc n).2.2]
    exact mem_image_of_mem _ h0D
  have hmemL : hL 0 ∈ ΩL := by
    rw [← hcL.2.2]
    exact mem_image_of_mem _ h0D
  -- anchors `X_n = X(h n 0) → X_L = X(hL 0)`
  obtain ⟨-, -, -, -, hX, -⟩ := s03_wc_jets hc hcL hconv h0D (fun _ => h0D) tendsto_const_nhds
  have hXLU := hXU hcL _ hmemL
  have hdX := (s06_cl_hdist_tendsto hXLU (fun n => hXU (hc n) _ (hmem n))).1 hX
  have hdq := (s06_cl_hdist_tendsto hq₀ hqU).1 hq
  obtain ⟨B, hB⟩ : ∃ B, B = hdist (epstein ΩL (hL 0)) q₀ + 2 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hB]
    linarith [hdnn _ _ hXLU hq₀]
  have hev : ∀ᶠ n in atTop, hdist (epstein (Ω n) (h n 0)) (q n) ≤ B := by
    filter_upwards [(tendsto_order.1 hdX).2 1 one_pos, (tendsto_order.1 hdq).2 1 one_pos]
      with n h1 h2
    have t1 := s02_hdist_triangle (hXU (hc n) _ (hmem n)) hXLU (hqU n)
    have t2 := s02_hdist_triangle hXLU hq₀ (hqU n)
    rw [s02_hdist_comm (q n) q₀] at h2
    linarith
  -- the horoball points are confined to `|ζ| ≤ r < 1`
  obtain ⟨r, hr1, hr⟩ := s06_cl_disk_confine (C * (1 + B))
  have hζ : ∀ᶠ n in atTop, ∃ ζ ∈ unitDisc, ‖ζ‖ ≤ r ∧ h n ζ = w n := by
    filter_upwards [hev] with n hn
    obtain ⟨ζ, hζD, hζw⟩ : w n ∈ h n '' unitDisc := by
      rw [(hc n).2.2]
      exact hw n
    refine ⟨ζ, hζD, hr ζ hζD ?_, hζw⟩
    have hl := s02_poincareDensity_pos ⟨h n, hc n⟩ (hw n)
    have hbus := lem_busemann ⟨h n, hc n⟩ (hw n) (hXU (hc n) _ (hmem n)) (hqU n)
    have hq2 : 0 < (q n).2 := hqU n
    have hX2 : 0 < (epstein (Ω n) (h n 0)).2 := hXU (hc n) _ (hmem n)
    have hΦq : 0 < horoPhi (Ω n) (q n) (w n) := by
      unfold horoPhi
      positivity
    have hΦX : 0 < horoPhi (Ω n) (epstein (Ω n) (h n 0)) (w n) := by
      unfold horoPhi
      positivity
    have hlog : Real.log (horoPhi (Ω n) (epstein (Ω n) (h n 0)) (w n)) ≤ B := by
      have h1 := (abs_le.1 hbus).2
      have h2 : Real.log (horoPhi (Ω n) (q n) (w n)) ≤ 0 := Real.log_nonpos hΦq.le (hΦ n)
      linarith
    have hT : horoPhi (Ω n) (epstein (Ω n) (h n 0)) (w n) ≤ Real.exp B := by
      rw [← Real.exp_log hΦX]
      exact Real.exp_le_exp.2 hlog
    have hcomp := hC (Ω n) (Ωs n) (hpair n) (hnl n) (h n 0) (hmem n) (w n) (hw n) (Real.exp B)
      (Real.one_le_exp hB0) hT
    rw [Real.log_exp, ← hζw, subsec_poincare_dist (hc n) h0D hζD] at hcomp
    exact hcomp
  -- a convergent subsequence of the parameters, and the limit of `Φ`
  obtain ⟨N, hN⟩ := eventually_atTop.1 hζ
  choose ζ hζD hζr hζw using fun k => hN (k + N) (Nat.le_add_left N k)
  obtain ⟨ζ₀, hζ₀, ψ, hψ, hlim⟩ := (isCompact_closedBall (0 : ℂ) r).tendsto_subseq
    (fun k => mem_closedBall_zero_iff.2 (hζr k))
  have hζ₀D : ζ₀ ∈ unitDisc := mem_ball_zero_iff.2 ((mem_closedBall_zero_iff.1 hζ₀).trans_lt hr1)
  have hσ : StrictMono (fun k => ψ k + N) := fun i j hij => Nat.add_lt_add_right (hψ hij) N
  obtain ⟨-, -, -, -, -, hΦL⟩ := s03_wc_jets (fun k => hc (ψ k + N)) hcL
    (s06_cl_tlu_subseq hconv hσ) hζ₀D (fun k => hζD (ψ k)) hlim
  have hlimΦ := hΦL (fun k => q (ψ k + N)) q₀ hq₀ (hq.comp hσ.tendsto_atTop)
  have hle : horoPhi ΩL q₀ (hL ζ₀) ≤ 1 := le_of_tendsto' hlimΦ fun k => by
    show horoPhi (Ω (ψ k + N)) (q (ψ k + N)) (h (ψ k + N) (ζ (ψ k))) ≤ 1
    rw [hζw (ψ k)]
    exact hΦ _
  have hζ₀L : hL ζ₀ ∈ ΩL := by
    rw [← hcL.2.2]
    exact mem_image_of_mem _ hζ₀D
  exact mem_biUnion hζ₀L ⟨hq₀, hle⟩

/-- Claim-6.6 helper (CL8): `U = horoUnion Ω` is relatively closed in `ℍ³` (CL7 with constant
sequences). -/
theorem s06_cl_horo_closed {K : ℝ} {Ω Ωs : Set ℂ} (hpair : IsKQuasiPair Ω Ωs K)
    (hnl : ¬ IsLinePair Ω Ωs) {q : ℂ × ℝ} (hq : q ∈ closure (horoUnion Ω)) (hqU : q ∈ UHS) :
    q ∈ horoUnion Ω := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap (s03_b0_jordanPair hpair)
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hq
  have hu' : ∀ n, ∃ w ∈ Ω, u n ∈ horoball Ω w := fun n => by
    obtain ⟨w, hw, hb⟩ := mem_iUnion₂.1 (hu n)
    exact ⟨w, hw, hb⟩
  choose w hw hwb using hu'
  have hconst : TendstoLocallyUniformlyOn (fun _ : ℕ => f) f atTop unitDisc :=
    fun _ hu _ _ => ⟨univ, univ_mem, Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu⟩
  exact s06_cl_limit_horo (Ω := fun _ => Ω) (Ωs := fun _ => Ωs) (fun _ => hpair) (fun _ => hnl)
    (fun _ => hf) hf hconst (fun n => (hwb n).1) hqU hlim hw (fun n => (hwb n).2)

/-- Claim-6.6 helper (CL9), "a ball in the gap": with `D` from `lem_width`, for a non-circular
`K`-quasi pair and `w ∈ Ω` there is `B(q₀, δ) ⊆ 𝒩` with `0 < δ ≤ 1` and `d(X(w), q₀) ≤ D + 1`.  The
segment from `X(w) ∈ U` to a point of `U*` within `D + 1` is connected, lies in `B(X(w), D + 1)`
(CL6) and so meets `𝒩`, since `U`, `U*` are relatively closed (CL8) and disjoint
(`prop_separation_b`); CL8 again gives the ball. -/
theorem s06_cl_gap_ball (K : ℝ) : ∃ D : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
    ¬ IsLinePair Ω Ωs → ∀ w ∈ Ω, ∃ q₀ : ℂ × ℝ, ∃ δ : ℝ, q₀ ∈ UHS ∧ 0 < δ ∧ δ ≤ 1 ∧
      hball q₀ δ ⊆ gap Ω Ωs ∧ hdist (epstein Ω w) q₀ ≤ D + 1 := by
  obtain ⟨D, hD⟩ := lem_width K
  refine ⟨D, fun Ω Ωs hpair hnl w hw => ?_⟩
  have hJ := s03_b0_jordanPair hpair
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  obtain ⟨g, hg⟩ := s02_jordanPair_riemannMap (s02_jordanPair_symm hJ)
  have hpairs := s03_qce_swap hpair
  have hnls := s03_cr_line hnl
  obtain ⟨-, hwd, -⟩ := hD Ω Ωs hpair hnl
  have hdnn : ∀ p p' : ℂ × ℝ, p ∈ UHS → p' ∈ UHS → 0 ≤ hdist p p' := fun p p' hp hp' => by
    have h2 : 0 < p.2 := hp
    have h2' : 0 < p'.2 := hp'
    show 0 ≤ Real.arcosh (coshDist p p')
    apply Real.arcosh_nonneg
    unfold coshDist
    have : 0 ≤ (‖p.1 - p'.1‖ ^ 2 + (p.2 - p'.2) ^ 2) / (2 * p.2 * p'.2) := by positivity
    linarith
  -- `X(x) ∈ U` for `x ∈ Ω`, and likewise on the side of `Ω*`
  have hXin : ∀ {Ω' : Set ℂ} {f' : ℂ → ℂ}, IsConformalOnto f' unitDisc Ω' → ∀ x ∈ Ω',
      epstein Ω' x ∈ horoUnion Ω' := fun hf' x hx => by
    have hn := lem_normal_b ⟨_, hf'⟩ hx
    refine mem_biUnion hx ⟨?_, ?_⟩
    · rw [← hn.2.2]
      exact hn.1 0
    · rw [← hn.2.2, s02_horoPhi_normalGeod _ x (s02_poincareDensity_pos ⟨_, hf'⟩ hx) 0,
        Real.exp_zero]
  have hXB := hXin hf w hw
  have hXU : epstein Ω w ∈ UHS := (mem_iUnion₂.1 hXB).choose_spec.choose_spec.1
  -- a point `y ∈ U*` within `D + 1` (`lem_width`)
  have hg0 : g 0 ∈ Ωs := by
    rw [← hg.2.2]
    exact mem_image_of_mem _ (mem_ball_self one_pos)
  have hne : (hdist (epstein Ω w) '' horoUnion Ωs).Nonempty :=
    ⟨_, mem_image_of_mem _ (hXin hg _ hg0)⟩
  obtain ⟨_, ⟨y, hyU, rfl⟩, hy⟩ := exists_lt_of_csInf_lt hne
    (lt_of_le_of_lt (hwd w hw) (lt_add_one D))
  obtain ⟨wy, -, hwy⟩ := mem_iUnion₂.1 hyU
  have hyH : y ∈ UHS := hwy.1
  -- the segment `[X, y]` lies in `B(X, D + 1)`
  have hXX : hdist (epstein Ω w) (epstein Ω w) = 0 := by
    have hc : coshDist (epstein Ω w) (epstein Ω w) = 1 := by simp [coshDist]
    simp only [hdist, hc, Real.arcosh_zero]
  have hSsub : segment ℝ (epstein Ω w) y ⊆ hball (epstein Ω w) (D + 1) :=
    (s06_cl_hball_convex hXU (D + 1)).segment_subset
      ⟨hXU, by rw [hXX]; linarith [hdnn _ _ hXU hyH]⟩ ⟨hyH, hy.le⟩
  -- the segment meets `𝒩`, since `U`, `U*` are relatively closed and disjoint
  have hsep := (prop_separation_b hJ hnl).2
  obtain ⟨q₀, hq₀S, hq₀n⟩ : ∃ q₀ ∈ segment ℝ (epstein Ω w) y,
      q₀ ∉ horoUnion Ω ∪ horoUnion Ωs := by
    by_contra hcon
    have hcon' : ∀ q ∈ segment ℝ (epstein Ω w) y, q ∈ horoUnion Ω ∪ horoUnion Ωs :=
      fun q hq => by
        by_contra h
        exact hcon ⟨q, hq, h⟩
    have hcov : segment ℝ (epstein Ω w) y ⊆ closure (horoUnion Ω) ∪ closure (horoUnion Ωs) :=
      fun q hq => (hcon' q hq).elim (fun h => Or.inl (subset_closure h))
        (fun h => Or.inr (subset_closure h))
    obtain ⟨q, hqS, hq1, hq2⟩ := isPreconnected_closed_iff.1
      (convex_segment (epstein Ω w) y).isPreconnected _ _ isClosed_closure isClosed_closure hcov
      ⟨_, left_mem_segment ℝ _ y, subset_closure hXB⟩ ⟨y, right_mem_segment ℝ _ y, subset_closure hyU⟩
    have hqU := (hSsub hqS).1
    have hboth : q ∈ horoUnion Ω ∩ horoUnion Ωs :=
      ⟨s06_cl_horo_closed hpair hnl hq1 hqU, s06_cl_horo_closed hpairs hnls hq2 hqU⟩
    rw [hsep] at hboth
    exact hboth
  have hq₀U : q₀ ∈ UHS := (hSsub hq₀S).1
  have hq₀d : hdist (epstein Ω w) q₀ ≤ D + 1 := (hSsub hq₀S).2
  -- a closed ball about `q₀` in `𝒩` (relative closedness again)
  have hball' : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ hball q₀ δ ⊆ gap Ω Ωs := by
    by_contra hcon
    have hk : ∀ k : ℕ, ∃ p ∈ hball q₀ (1 / ((k : ℝ) + 1)), p ∉ gap Ω Ωs := fun k => by
      by_contra hk
      have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [k.cast_nonneg (α := ℝ)]
      exact hcon ⟨1 / ((k : ℝ) + 1), by positivity, by rw [div_le_one (by positivity)]; exact hk1,
        fun p hp => by
          by_contra hp'
          exact hk ⟨p, hp, hp'⟩⟩
    choose p hp hpn using hk
    have hpU : ∀ k, p k ∈ UHS := fun k => (hp k).1
    have hconv : Tendsto p atTop (𝓝 q₀) := by
      refine (s06_cl_hdist_tendsto hq₀U hpU).2 ?_
      refine squeeze_zero (fun k => hdnn _ _ (hpU k) hq₀U) (fun k => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      rw [s02_hdist_comm]
      exact (hp k).2
    have hpin : ∀ k, p k ∈ horoUnion Ω ∪ horoUnion Ωs := fun k => by
      by_contra h
      exact hpn k ⟨hpU k, h⟩
    have hcl : q₀ ∈ closure (horoUnion Ω ∪ horoUnion Ωs) :=
      mem_closure_of_tendsto hconv (Eventually.of_forall hpin)
    rw [closure_union] at hcl
    rcases hcl with h | h
    · exact hq₀n (Or.inl (s06_cl_horo_closed hpair hnl h hq₀U))
    · exact hq₀n (Or.inr (s06_cl_horo_closed hpairs hnls h hq₀U))
  obtain ⟨δ, hδ0, hδ1, hδ⟩ := hball'
  exact ⟨q₀, δ, hq₀U, hδ0, hδ1, hδ, hq₀d⟩

/-- Claim-6.6 helper (CL10): the gap volume near `X(w)` is invariant under `z ↦ a z + b`
(`subsec_epstein_natural_affine`, `s09_horoUnion_aff`, `s09_hvol_map_aff`). -/
theorem s06_cl_aff {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {a b : ℂ} (ha : a ≠ 0) {w : ℂ}
    (hw : w ∈ Ω) (M : ℝ) :
    hvol (gap ((fun z => a * z + b) '' Ω) ((fun z => a * z + b) '' Ωs) ∩
        hball (epstein ((fun z => a * z + b) '' Ω) (a * w + b)) M) =
      hvol (gap Ω Ωs ∩ hball (epstein Ω w) M) := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  obtain ⟨g, hg⟩ := s02_jordanPair_riemannMap (s02_jordanPair_symm hJ)
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hXw : epstein Ω w ∈ UHS := by
    have h := lem_normal_b ⟨f, hf⟩ hw
    rw [← h.2.2]
    exact h.1 0
  have hcd : ∀ p q : ℂ × ℝ, 0 < p.2 → 0 < q.2 →
      hdist (a * p.1 + b, ‖a‖ * p.2) (a * q.1 + b, ‖a‖ * q.2) = hdist p q := by
    intro p q hp hq
    have hc : coshDist (a * p.1 + b, ‖a‖ * p.2) (a * q.1 + b, ‖a‖ * q.2) = coshDist p q := by
      unfold coshDist
      dsimp only
      rw [show a * p.1 + b - (a * q.1 + b) = a * (p.1 - q.1) by ring, norm_mul]
      field_simp
    unfold hdist
    rw [hc]
  have hpre : (fun q : ℂ × ℝ => (a * q.1 + b, ‖a‖ * q.2)) ⁻¹'
      (gap ((fun z => a * z + b) '' Ω) ((fun z => a * z + b) '' Ωs) ∩
        hball (epstein ((fun z => a * z + b) '' Ω) (a * w + b)) M) =
      gap Ω Ωs ∩ hball (epstein Ω w) M := by
    rw [subsec_epstein_natural_affine ⟨f, hf⟩ ha hw, preimage_inter]
    congr 1
    · unfold gap
      rw [preimage_sdiff, preimage_union, s09_affExt_UHS a b ha, s09_horoUnion_aff Ω ⟨f, hf⟩ a b ha,
        s09_horoUnion_aff Ωs ⟨g, hg⟩ a b ha]
    · ext q
      constructor
      · rintro ⟨hqU, hd⟩
        have hq2 : 0 < q.2 := pos_of_mul_pos_right (show 0 < ‖a‖ * q.2 from hqU) hna.le
        exact ⟨hq2, by rwa [hcd _ _ hXw hq2] at hd⟩
      · rintro ⟨hqU, hd⟩
        have hq2 : 0 < q.2 := hqU
        refine ⟨show 0 < ‖a‖ * q.2 from mul_pos hna hq2, ?_⟩
        show hdist (a * (epstein Ω w).1 + b, ‖a‖ * (epstein Ω w).2) (a * q.1 + b, ‖a‖ * q.2) ≤ M
        rw [hcd _ _ hXw hq2]
        exact hd
  conv_lhs => rw [← s09_hvol_map_aff a b ha]
  rw [(s09_affExt_meas a b ha).map_apply, hpre]

/-- Claim-6.6 helper (CL11), the uniform convergence on both sides in sequential form: if the
Riemann maps of both sides of non-circular `K`-quasi pairs converge locally uniformly on `𝔻` to
conformal maps onto `ΩL`, `ΩsL`, then every closed ball `B(q₀, δ) ⊆ 𝒩_L` lies in `𝒩_n` for large
`n` (CL5, and CL7 on each side). -/
theorem s06_cl_eventually_gap {K : ℝ} {Ω Ωs : ℕ → Set ℂ} {ΩL ΩsL : Set ℂ}
    (hpair : ∀ n, IsKQuasiPair (Ω n) (Ωs n) K) (hnl : ∀ n, ¬ IsLinePair (Ω n) (Ωs n))
    {g gs : ℕ → ℂ → ℂ} {gL gsL : ℂ → ℂ}
    (hg : ∀ n, IsConformalOnto (g n) unitDisc (Ω n)) (hgL : IsConformalOnto gL unitDisc ΩL)
    (hgc : TendstoLocallyUniformlyOn g gL atTop unitDisc)
    (hgs : ∀ n, IsConformalOnto (gs n) unitDisc (Ωs n))
    (hgsL : IsConformalOnto gsL unitDisc ΩsL)
    (hgsc : TendstoLocallyUniformlyOn gs gsL atTop unitDisc)
    {q₀ : ℂ × ℝ} (hq₀ : q₀ ∈ UHS) {δ : ℝ} (hgap : hball q₀ δ ⊆ gap ΩL ΩsL) :
    ∀ᶠ n in atTop, hball q₀ δ ⊆ gap (Ω n) (Ωs n) := by
  by_contra hcon
  obtain ⟨ψ, hψ, hψp⟩ := extraction_of_frequently_atTop (Filter.not_eventually.1 hcon)
  have hk : ∀ k, ∃ p ∈ hball q₀ δ, p ∉ gap (Ω (ψ k)) (Ωs (ψ k)) := fun k => by
    have h := hψp k
    rw [not_subset] at h
    exact h
  choose p hp hpn using hk
  obtain ⟨ψ₂, hψ₂, q, hq, hlim⟩ := s06_cl_hball_seq hq₀ hp
  have hpin : ∀ k, p k ∈ horoUnion (Ω (ψ k)) ∪ horoUnion (Ωs (ψ k)) := fun k => by
    by_contra h
    exact hpn k ⟨(hp k).1, h⟩
  have hqg := hgap hq
  have hor : (∃ᶠ k in atTop, p (ψ₂ k) ∈ horoUnion (Ω (ψ (ψ₂ k)))) ∨
      ∃ᶠ k in atTop, p (ψ₂ k) ∈ horoUnion (Ωs (ψ (ψ₂ k))) := by
    rw [← frequently_or_distrib]
    exact Frequently.of_forall fun k => hpin (ψ₂ k)
  rcases hor with h1 | h1
  · obtain ⟨ψ₃, hψ₃, hψ₃p⟩ := extraction_of_frequently_atTop h1
    choose w hw hwb using fun k => mem_iUnion₂.1 (hψ₃p k)
    have h := s06_cl_limit_horo (Ω := fun k => Ω (ψ (ψ₂ (ψ₃ k))))
      (Ωs := fun k => Ωs (ψ (ψ₂ (ψ₃ k)))) (h := fun k => g (ψ (ψ₂ (ψ₃ k))))
      (fun k => hpair _) (fun k => hnl _) (fun k => hg _) hgL
      (s06_cl_tlu_subseq hgc (hψ.comp (hψ₂.comp hψ₃))) (fun k => (hwb k).1) hqg.1
      (hlim.comp hψ₃.tendsto_atTop) hw (fun k => (hwb k).2)
    exact hqg.2 (Or.inl h)
  · obtain ⟨ψ₃, hψ₃, hψ₃p⟩ := extraction_of_frequently_atTop h1
    choose w hw hwb using fun k => mem_iUnion₂.1 (hψ₃p k)
    have h := s06_cl_limit_horo (Ω := fun k => Ωs (ψ (ψ₂ (ψ₃ k))))
      (Ωs := fun k => Ω (ψ (ψ₂ (ψ₃ k)))) (h := fun k => gs (ψ (ψ₂ (ψ₃ k))))
      (fun k => s03_qce_swap (hpair _)) (fun k => s03_cr_line (hnl _)) (fun k => hgs _) hgsL
      (s06_cl_tlu_subseq hgsc (hψ.comp (hψ₂.comp hψ₃))) (fun k => (hwb k).1) hqg.1
      (hlim.comp hψ₃.tendsto_atTop) hw (fun k => (hwb k).2)
    exact hqg.2 (Or.inr h)

/-- **Claim 6.6** (in the proof of Proposition 6.5, sec06-lower.tex:140).  With `M = D_Q + 2`
depending only on `K`, there is `v_K > 0`, depending only on `K`, such that
`vol(𝒩 ∩ B(X(w), M)) ≥ v_K` for every non-circular `K`-quasicircle and every `w ∈ Ω` with
`s(w) ≥ 1/2`. -/
theorem prop_mass_volume_claim : ∀ K : ℝ, 1 ≤ K → ∃ M vK : ℝ, 0 < vK ∧ ∀ Ω Ωs : Set ℂ,
    IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs → ∀ w ∈ Ω, 1 / 2 ≤ schwarzNorm Ω w →
      ENNReal.ofReal vK ≤ hvol (gap Ω Ωs ∩ hball (epstein Ω w) M) := by
  intro K hK
  obtain ⟨D, hD⟩ := s06_cl_gap_ball K
  refine ⟨D + 3, ?_⟩
  by_contra hcon
  -- a sequence of counterexamples with gap volume `< 1/(n+1)`
  have hseq : ∀ n : ℕ, ∃ (Ω Ωs : Set ℂ) (w : ℂ), IsKQuasiPair Ω Ωs K ∧ ¬ IsLinePair Ω Ωs ∧
      w ∈ Ω ∧ 1 / 2 ≤ schwarzNorm Ω w ∧
      hvol (gap Ω Ωs ∩ hball (epstein Ω w) (D + 3)) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    by_contra hn
    exact hcon ⟨1 / ((n : ℝ) + 1), by positivity, fun Ω Ωs hp hnl w hw hs =>
      le_of_not_gt fun hlt => hn ⟨Ω, Ωs, w, hp, hnl, hw, hs, hlt⟩⟩
  choose Ω Ωs w hpair hnl hw hs hvl using hseq
  -- normalize (`w ↦ 0`) and pass to a convergent subsequence
  obtain ⟨φ, hφ, a, b, P, PL, HL, hab, hPn, hPLK, hPLs, hPLI, hHL, -, hinv⟩ :=
    s03_wc_pairs hK Ω Ωs hpair w hw
  have hJ : ∀ n, IsJordanPair (Ω n) (Ωs n) := fun n => s03_b0_jordanPair (hpair n)
  have hP : ∀ n, IsKQC (P n) univ K := fun n => (hPn n).1
  have hPs : ∀ n, P n '' univ = univ := fun n => (hPn n).2.1
  have hI : (I : ℂ) ∈ upperHalf := show (0 : ℝ) < I.im by simp
  have hmI : (-I : ℂ) ∈ lowerHalf := show (-I).im < (0 : ℝ) by simp
  have hs0 : ∀ n, 1 / 2 ≤ schwarzNorm (P n '' upperHalf) 0 := fun n => by
    have e := (subsec_poincare_natural_affine (s02_jordanPair_riemannMap (hJ (φ n)))
      (a := a n) (b := b n) (hab n).1 (hw (φ n))).2
    rw [(hab n).2] at e
    rw [(hPn n).2.2.2.1, e]
    exact hs (φ n)
  have hv0 : ∀ n, hvol (gap (P n '' upperHalf) (P n '' lowerHalf) ∩
      hball (epstein (P n '' upperHalf) 0) (D + 3)) <
        ENNReal.ofReal (1 / ((φ n : ℝ) + 1)) := fun n => by
    have e := s06_cl_aff (hJ (φ n)) (a := a n) (b := b n) (hab n).1 (hw (φ n)) (D + 3)
    rw [(hab n).2] at e
    rw [(hPn n).2.2.2.1, (hPn n).2.2.2.2, e]
    exact hvl (φ n)
  -- Riemann maps of both sides converge (W-COMP K4)
  obtain ⟨φ₂, hφ₂, g, gL, hg, hgL, hgL0, hgc⟩ :=
    s03_wc_riemann hK hP hPs hPLK hPLs hHL hinv (y₀ := 0) ⟨I, hI, hPLI⟩
  obtain ⟨φ₃, hφ₃, gs, gsL, hgs, hgsL, -, hgsc⟩ :=
    s03_wc_riemann_lower hK (P := fun n => P (φ₂ n)) (fun n => hP (φ₂ n))
      (fun n => hPs (φ₂ n)) hPLK hPLs hHL (s03_wc_tlu_subseq hinv hφ₂) (y₁ := PL (-I))
      ⟨-I, hmI, rfl⟩
  have hgc' := s06_cl_tlu_subseq hgc hφ₃
  have hpair' : ∀ m, IsKQuasiPair (P (φ₂ (φ₃ m)) '' upperHalf) (P (φ₂ (φ₃ m)) '' lowerHalf) K :=
    fun m => ⟨P (φ₂ (φ₃ m)), hP _, hPs _, rfl, rfl⟩
  have h0P : ∀ n, (0 : ℂ) ∈ P n '' upperHalf := fun n => ⟨I, hI, (hPn n).2.2.1⟩
  have hnl' : ∀ m, ¬ IsLinePair (P (φ₂ (φ₃ m)) '' upperHalf) (P (φ₂ (φ₃ m)) '' lowerHalf) :=
    fun m hl => by
      have h1 := s06_cl_line_s hl (h0P _)
      have h2 := hs0 (φ₂ (φ₃ m))
      linarith
  -- the limit: `s_L(0) ≥ 1/2`, so the limit curve is not a line
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  obtain ⟨-, -, -, hsL, hXL, -⟩ := s03_wc_jets (fun m => (hg (φ₃ m)).1) hgL hgc' h0D
    (fun _ => h0D) tendsto_const_nhds
  rw [hgL0] at hsL hXL
  have hsL' : Tendsto (fun m => schwarzNorm (P (φ₂ (φ₃ m)) '' upperHalf) 0) atTop
      (𝓝 (schwarzNorm (PL '' upperHalf) 0)) :=
    hsL.congr fun m => by rw [(hg (φ₃ m)).2]
  have hXL' : Tendsto (fun m => epstein (P (φ₂ (φ₃ m)) '' upperHalf) 0) atTop
      (𝓝 (epstein (PL '' upperHalf) 0)) :=
    hXL.congr fun m => by rw [(hg (φ₃ m)).2]
  have hsL0 : 1 / 2 ≤ schwarzNorm (PL '' upperHalf) 0 :=
    ge_of_tendsto hsL' (Eventually.of_forall fun m => hs0 _)
  have hpairL : IsKQuasiPair (PL '' upperHalf) (PL '' lowerHalf) K := ⟨PL, hPLK, hPLs, rfl, rfl⟩
  have h0L : (0 : ℂ) ∈ PL '' upperHalf := ⟨I, hI, hPLI⟩
  have hnlL : ¬ IsLinePair (PL '' upperHalf) (PL '' lowerHalf) := fun hl => by
    have h1 := s06_cl_line_s hl h0L
    linarith
  -- a ball in the limit gap, and in the gaps of the sequence (CL9, CL11)
  obtain ⟨q₀, δ, hq₀, hδ0, hδ1, hbg, hdq⟩ := hD _ _ hpairL hnlL 0 h0L
  have hev := s06_cl_eventually_gap hpair' hnl' (fun m => (hg (φ₃ m)).1) hgL hgc'
    (fun m => (hgs m).1) hgsL hgsc hq₀ hbg
  -- `X_m(0) → X_L(0)`
  have hXU : ∀ {Ω' : Set ℂ} {f : ℂ → ℂ}, IsConformalOnto f unitDisc Ω' → ∀ x ∈ Ω',
      epstein Ω' x ∈ UHS := fun hf x hx => by
    have h := lem_normal_b ⟨_, hf⟩ hx
    rw [← h.2.2]
    exact h.1 0
  have hXd := (s06_cl_hdist_tendsto (hXU hgL 0 h0L)
    (fun m => hXU (hg (φ₃ m)).1 0 (h0P _))).1 hXL'
  have hc : 0 < 2 * π * δ ^ 3 / 27 := by positivity
  obtain ⟨m, hm1, hm2, hm3⟩ := (hev.and ((tendsto_order.1 hXd).2 1 one_pos |>.and
    ((tendsto_order.1 tendsto_one_div_add_atTop_nhds_zero_nat).2 _ hc))).exists
  -- the contradiction
  have hsub : hball q₀ δ ⊆ gap (P (φ₂ (φ₃ m)) '' upperHalf) (P (φ₂ (φ₃ m)) '' lowerHalf) ∩
      hball (epstein (P (φ₂ (φ₃ m)) '' upperHalf) 0) (D + 3) := fun q hq => by
    refine ⟨hm1 hq, hq.1, ?_⟩
    have hXm := hXU (hg (φ₃ m)).1 0 (h0P _)
    have t1 := s02_hdist_triangle hXm (hXU hgL 0 h0L) hq.1
    have t2 := s02_hdist_triangle (hXU hgL 0 h0L) hq₀ hq.1
    have := hq.2
    linarith
  have hidx : (m : ℝ) ≤ φ (φ₂ (φ₃ m)) := by
    exact_mod_cast ((hφ.comp (hφ₂.comp hφ₃)).id_le m)
  have hlt : ENNReal.ofReal (1 / ((φ (φ₂ (φ₃ m)) : ℝ) + 1)) < ENNReal.ofReal (2 * π * δ ^ 3 / 27) := by
    rw [ENNReal.ofReal_lt_ofReal_iff hc]
    calc 1 / ((φ (φ₂ (φ₃ m)) : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
      _ < _ := hm3
  have := (s05_pk_hvol_ge hq₀ hδ0 hδ1).trans ((measure_mono hsub).trans (hv0 _).le)
  exact absurd (this.trans_lt hlt) (lt_irrefl _)

/-- **Proposition 6.5** (`prop:mass-volume`, sec06-lower.tex:103).  There are `R_K ≥ 2` and
`C(K)` such that for every `K`-quasicircle that is not a circle and every `P ∈ ℍ³`,
`μ_H(B(P, 1)) ≤ C(K) vol(𝒩 ∩ B(P, R_K))` (6.5) (`eq:mass-volume`).  (Statement as agreed with
§9, which uses it.) -/
theorem prop_mass_volume :
    ∀ K : ℝ, 1 ≤ K → ∃ R C : ℝ≥0, 2 ≤ R ∧ ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
      ¬ IsLinePair Ω Ωs → ∀ P ∈ UHS,
        curvMass Ω (epstein Ω ⁻¹' hball P 1) + curvMass Ωs (epstein Ωs ⁻¹' hball P 1) ≤
          (C : ℝ≥0∞) * hvol (gap Ω Ωs ∩ hball P R) := by
  intro K hK
  obtain ⟨R₀, hc1⟩ := s06_mv_case1 K hK
  obtain ⟨M, vK, hv, hcl⟩ := prop_mass_volume_claim K hK
  obtain ⟨C₁, hC₁⟩ := lem_local_mass K hK
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = max 2 (1 + 5 / 2 * (R₀ + 2) + M) := ⟨_, rfl⟩
  have hR2 : (2 : ℝ) ≤ R := hR ▸ le_max_left _ _
  have hRM : 1 + 5 / 2 * (R₀ + 2) + M ≤ R := hR ▸ le_max_right _ _
  have hRc : ((R.toNNReal : ℝ≥0) : ℝ) = R := Real.coe_toNNReal _ (by linarith)
  -- `vK > 0`, so `vK.toNNReal ≠ 0` and `C₁ / vK` is a genuine (finite) ratio
  have hne : vK.toNNReal ≠ 0 := (Real.toNNReal_pos.2 hv).ne'
  have hmono : ∀ {P : ℂ × ℝ} {a b : ℝ}, a ≤ b → hball P a ⊆ hball P b :=
    fun hab _ hQ => ⟨hQ.1, hQ.2.trans hab⟩
  refine ⟨R.toNNReal, max 52 (C₁ / vK.toNNReal), ?_, fun Ω Ωs hpair hnl P hP => ?_⟩
  · rw [← NNReal.coe_le_coe, hRc]
    simpa using hR2
  rw [hRc]
  -- Case 2 (on either side): a point with `s ≥ 1/2` near `Π`; the gap volume near it is `≥ vK`
  have key : ∀ Ω' Ωs' : Set ℂ, IsKQuasiPair Ω' Ωs' K → ¬ IsLinePair Ω' Ωs' →
      gap Ω' Ωs' = gap Ω Ωs → ∀ w₀ ∈ Ω', epstein Ω' w₀ ∈ hball P 1 → ∀ w' ∈ Ω',
      poincareDist Ω' w₀ w' ≤ R₀ + 2 → 1 / 2 ≤ schwarzNorm Ω' w' →
      curvMass Ω (epstein Ω ⁻¹' hball P 1) + curvMass Ωs (epstein Ωs ⁻¹' hball P 1) ≤
        ((max 52 (C₁ / vK.toNNReal) : ℝ≥0) : ℝ≥0∞) * hvol (gap Ω Ωs ∩ hball P R) := by
    intro Ω' Ωs' hp' hnl' hg w₀ hw₀ hX₀ w' hw' hd hs
    obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap (s03_b0_jordanPair hp')
    have hn := lem_normal_b ⟨f, hf⟩ hw'
    have hX'U : epstein Ω' w' ∈ UHS := by
      rw [← hn.2.2]
      exact hn.1 0
    have hq := (s03_qi_upper K Ω' Ωs' hp' hnl').1 w₀ hw₀ w' hw'
    have hsub : hball (epstein Ω' w') M ⊆ hball P R := fun Q hQ => by
      refine ⟨hQ.1, ?_⟩
      have t1 := s02_hdist_triangle hP hX₀.1 hQ.1
      have t2 := s02_hdist_triangle hX₀.1 hX'U hQ.1
      have h1 := hX₀.2
      have h2 := hQ.2
      linarith
    have hvK := hcl Ω' Ωs' hp' hnl' w' hw' hs
    rw [hg] at hvK
    calc curvMass Ω (epstein Ω ⁻¹' hball P 1) + curvMass Ωs (epstein Ωs ⁻¹' hball P 1)
        ≤ (C₁ : ℝ≥0∞) := hC₁ Ω Ωs hpair P hP
      _ = ((C₁ / vK.toNNReal : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal vK := by
        show _ = _ * ((vK.toNNReal : ℝ≥0) : ℝ≥0∞)
        rw [← ENNReal.coe_mul, div_mul_cancel₀ _ hne]
      _ ≤ ((max 52 (C₁ / vK.toNNReal) : ℝ≥0) : ℝ≥0∞) * hvol (gap Ω Ωs ∩ hball P R) :=
        mul_le_mul' (ENNReal.coe_le_coe.2 (le_max_right _ _))
          (hvK.trans (measure_mono (inter_subset_inter_right _ hsub)))
  have hg : gap Ωs Ω = gap Ω Ωs := by
    unfold gap
    rw [union_comm]
  by_cases h1 : ∀ w₀ ∈ Ω, epstein Ω w₀ ∈ hball P 1 → ∀ w' ∈ Ω, poincareDist Ω w₀ w' ≤ R₀ + 2 →
      schwarzNorm Ω w' < 1 / 2
  · by_cases h2 : ∀ z₀ ∈ Ωs, epstein Ωs z₀ ∈ hball P 1 → ∀ z' ∈ Ωs,
        poincareDist Ωs z₀ z' ≤ R₀ + 2 → schwarzNorm Ωs z' < 1 / 2
    · -- Case 1
      calc curvMass Ω (epstein Ω ⁻¹' hball P 1) + curvMass Ωs (epstein Ωs ⁻¹' hball P 1)
          ≤ 52 * hvol (gap Ω Ωs ∩ hball P 2) := hc1 Ω Ωs hpair hnl P hP h1 h2
        _ ≤ ((max 52 (C₁ / vK.toNNReal) : ℝ≥0) : ℝ≥0∞) * hvol (gap Ω Ωs ∩ hball P R) :=
          mul_le_mul' (by exact_mod_cast le_max_left (52 : ℝ≥0) (C₁ / vK.toNNReal))
            (measure_mono (inter_subset_inter_right _ (hmono hR2)))
    · push Not at h2
      obtain ⟨z₀, hz₀, hX, z', hz', hd, hs⟩ := h2
      exact key Ωs Ω (s03_qce_swap hpair) (s03_cr_line hnl) hg z₀ hz₀ hX z' hz' hd hs
  · push Not at h1
    obtain ⟨w₀, hw₀, hX, w', hw', hd, hs⟩ := h1
    exact key Ω Ωs hpair hnl rfl w₀ hw₀ hX w' hw' hd hs

/-- Theorem-6.1 helper (TL1): a maximal `1`-separated subset of `ℍ³` (Zorn); the closed balls
`B(b, 1)`, `b ∈ S`, cover `ℍ³`. -/
theorem s06_tl_net : ∃ S : Set (ℂ × ℝ), S ⊆ UHS ∧
    (∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → 1 ≤ hdist b b') ∧ ∀ q ∈ UHS, ∃ b ∈ S, hdist b q ≤ 1 := by
  obtain ⟨m, hm⟩ := zorn_subset {S : Set (ℂ × ℝ) | S ⊆ UHS ∧
      ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → 1 ≤ hdist b b'} fun c hc hch => by
    refine ⟨⋃₀ c, ⟨sUnion_subset fun s hs => (hc hs).1, ?_⟩, fun s hs => subset_sUnion_of_mem hs⟩
    intro b hb b' hb' hne
    obtain ⟨s, hs, hbs⟩ := hb
    obtain ⟨s', hs', hbs'⟩ := hb'
    rcases hch.total hs hs' with h | h
    · exact (hc hs').2 b (h hbs) b' hbs' hne
    · exact (hc hs).2 b hbs b' (h hbs') hne
  refine ⟨m, hm.1.1, hm.1.2, fun q hq => ?_⟩
  by_contra hcon
  push Not at hcon
  -- maximality: otherwise `q` could be added to the net
  have hins : insert q m ∈ {S : Set (ℂ × ℝ) | S ⊆ UHS ∧
      ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → 1 ≤ hdist b b'} := by
    refine ⟨insert_subset hq hm.1.1, ?_⟩
    intro b hb b' hb' hne
    rcases hb with hb | hb <;> rcases hb' with hb' | hb'
    · exact absurd (hb.trans hb'.symm) hne
    · rw [hb, s02_hdist_comm]
      exact (hcon b' hb').le
    · rw [hb']
      exact (hcon b hb).le
    · exact hm.1.2 b hb b' hb' hne
  have hqm : q ∈ m := hm.2 hins (subset_insert q m) (mem_insert q m)
  have hlt := hcon q hqm
  have hc : coshDist q q = 1 := by simp [coshDist]
  have h0 : hdist q q = 0 := by simp only [hdist, hc, Real.arcosh_zero]
  linarith

/-- Theorem-6.1 helper (TL3): for a line pair both curvature measures vanish (`s = s* = 0`). -/
theorem s06_tl_line {Ω Ωs : Set ℂ} (hl : IsLinePair Ω Ωs) : curvMass Ω = 0 ∧ curvMass Ωs = 0 := by
  have hzero : ∀ {Ω' : Set ℂ}, IsOpen Ω' → (∀ w ∈ Ω', schwarzNorm Ω' w = 0) → curvMass Ω' = 0 := by
    intro Ω' ho hs
    have hae : (fun w => ENNReal.ofReal (schwarzNorm Ω' w ^ 2 * poincareDensity Ω' w ^ 2)) =ᵐ[volume.restrict Ω'] 0 :=
      (ae_restrict_iff' ho.measurableSet).2 (Eventually.of_forall fun w hw => by simp [hs w hw])
    show (volume.restrict Ω').withDensity _ = 0
    rw [withDensity_congr_ae hae, withDensity_zero]
  obtain ⟨a, b, ha, hΩ, hΩs⟩ := hl
  have hc : Continuous fun z : ℂ => (a * z + b).im :=
    Complex.continuous_im.comp ((continuous_const.mul continuous_id).add continuous_const)
  have e : ∀ z : ℂ, (-a * z + -b).im = -(a * z + b).im := fun z => by
    rw [show -a * z + -b = -(a * z + b) by ring, Complex.neg_im]
  have hl1 : IsLinePair Ω Ωs := ⟨a, b, ha, hΩ, hΩs⟩
  have hl2 : IsLinePair Ωs Ω := ⟨-a, -b, neg_ne_zero.2 ha,
    by rw [hΩs]; ext z; simp only [mem_ofPred_eq, e, neg_pos],
    by rw [hΩ]; ext z; simp only [mem_ofPred_eq, e, neg_lt_zero]⟩
  have ho1 : IsOpen Ω := by
    rw [hΩ]
    exact isOpen_lt continuous_const hc
  have ho2 : IsOpen Ωs := by
    rw [hΩs]
    exact isOpen_lt hc continuous_const
  exact ⟨hzero ho1 fun w hw => s06_cl_line_s hl1 hw, hzero ho2 fun w hw => s06_cl_line_s hl2 hw⟩

/-- Theorem-6.1 helper (TL4): `Ω ∩ X⁻¹(B(P, 1))` is measurable. -/
theorem s06_tl_meas {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {P : ℂ × ℝ} (hP : P ∈ UHS) :
    MeasurableSet (Ω ∩ epstein Ω ⁻¹' hball P 1) := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  have hΩo : IsOpen Ω := s05_jordan_isOpen hJ
  have hP2 : (0 : ℝ) < P.2 := hP
  have hXU : ∀ w ∈ Ω, 0 < (epstein Ω w).2 := fun w hw => by
    have h := lem_normal_b ⟨f, hf⟩ hw
    rw [← h.2.2]
    exact h.1 0
  have hXC : ContinuousOn (epstein Ω) Ω := (lem_fff_smooth ⟨f, hf⟩).continuousOn
  have hg : ContinuousOn (fun w => coshDist P (epstein Ω w)) Ω := by
    unfold coshDist
    have h1 : ContinuousOn (fun w => (epstein Ω w).1) Ω := continuous_fst.comp_continuousOn hXC
    have h2 : ContinuousOn (fun w => (epstein Ω w).2) Ω := continuous_snd.comp_continuousOn hXC
    exact continuousOn_const.add ((((continuousOn_const.sub h1).norm.pow 2).add
      ((continuousOn_const.sub h2).pow 2)).div (continuousOn_const.mul h2)
      fun w hw => (mul_pos (mul_pos two_pos hP2) (hXU w hw)).ne')
  -- `X(w) ∈ B(P, 1) ↔ cosh d(P, X(w)) ≤ cosh 1`
  have hiff : ∀ w ∈ Ω, epstein Ω w ∈ hball P 1 ↔ coshDist P (epstein Ω w) ≤ Real.cosh 1 := by
    intro w hw
    have hc1 : 0 < coshDist P (epstein Ω w) := by
      have h0 := hXU w hw
      unfold coshDist
      have : 0 ≤ (‖P.1 - (epstein Ω w).1‖ ^ 2 + (P.2 - (epstein Ω w).2) ^ 2) /
          (2 * P.2 * (epstein Ω w).2) :=
        div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_pos (mul_pos two_pos hP2) h0).le
      linarith
    have hch : 0 < Real.cosh 1 := Real.cosh_pos 1
    constructor
    · rintro ⟨-, hd⟩
      exact (Real.arcosh_le_arcosh hc1 hch).1 (hd.trans (Real.arcosh_cosh zero_le_one).symm.le)
    · intro h
      exact ⟨hXU w hw, ((Real.arcosh_le_arcosh hc1 hch).2 h).trans (Real.arcosh_cosh zero_le_one).le⟩
  have h1 : Ω ∩ epstein Ω ⁻¹' hball P 1 =
      Ω \ (Ω ∩ (fun w => coshDist P (epstein Ω w)) ⁻¹' Ioi (Real.cosh 1)) := by
    ext w
    constructor
    · rintro ⟨hw, hb⟩
      refine ⟨hw, fun h => ?_⟩
      exact absurd ((hiff w hw).1 hb)
        (not_le.2 (show Real.cosh 1 < coshDist P (epstein Ω w) from h.2))
    · rintro ⟨hw, hb⟩
      exact ⟨hw, (hiff w hw).2 (not_lt.1 fun h => hb ⟨hw, h⟩)⟩
  rw [h1]
  exact hΩo.measurableSet.diff (hg.isOpen_inter_preimage hΩo isOpen_Ioi).measurableSet

/-- Theorem-6.1 helper (TL5): for a non-circular `K`-quasicircle the gap `𝒩` is measurable
(`U`, `U*` are relatively closed in `ℍ³`, `s06_cl_horo_closed`). -/
theorem s06_tl_gap_meas {K : ℝ} {Ω Ωs : Set ℂ} (hpair : IsKQuasiPair Ω Ωs K)
    (hnl : ¬ IsLinePair Ω Ωs) : MeasurableSet (gap Ω Ωs) := by
  have hUo : IsOpen UHS := isOpen_lt continuous_const continuous_snd
  have hcl : ∀ {Ω' Ωs' : Set ℂ}, IsKQuasiPair Ω' Ωs' K → ¬ IsLinePair Ω' Ωs' →
      MeasurableSet (horoUnion Ω') := by
    intro Ω' Ωs' hp hn
    have e : horoUnion Ω' = closure (horoUnion Ω') ∩ UHS := by
      apply Subset.antisymm
      · intro q hq
        exact ⟨subset_closure hq, (mem_iUnion₂.1 hq).choose_spec.choose_spec.1⟩
      · rintro q ⟨h1, h2⟩
        exact s06_cl_horo_closed hp hn h1 h2
    rw [e]
    exact isClosed_closure.measurableSet.inter hUo.measurableSet
  exact hUo.measurableSet.diff ((hcl hpair hnl).union (hcl (s03_qce_swap hpair) (s03_cr_line hnl)))

/-- Theorem-6.1 helper (TL6): if the balls `B(b, 1)`, `b ∈ S` (countable), cover `ℍ³`, then
`∫ f dm_Ω ≤ ∑_b ∫_{Ω ∩ X⁻¹B(b,1)} f dm_Ω`. -/
theorem s06_tl_cover {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {S : Set (ℂ × ℝ)} (hSc : S.Countable)
    (hcov : ∀ q ∈ UHS, ∃ b ∈ S, hdist b q ≤ 1) (f : ℂ → ℝ≥0∞) :
    ∫⁻ w, f w ∂curvMass Ω ≤ ∑' b : S, ∫⁻ w in Ω ∩ epstein Ω ⁻¹' hball b 1, f w ∂curvMass Ω := by
  have : Countable S := hSc.to_subtype
  obtain ⟨f', hf'⟩ := s02_jordanPair_riemannMap hJ
  have hΩo := s05_jordan_isOpen hJ
  -- `m_Ω`-a.e. point lies in some cell (the complement of `Ω` is null)
  have hae : ∀ᵐ w ∂curvMass Ω, w ∈ ⋃ b : S, Ω ∩ epstein Ω ⁻¹' hball b 1 := by
    refine ae_iff.2 (measure_mono_null (fun w hw => ?_) (s06_lm_compl hΩo))
    intro hwΩ
    apply hw
    have hn := lem_normal_b ⟨f', hf'⟩ hwΩ
    have hXU : epstein Ω w ∈ UHS := by
      rw [← hn.2.2]
      exact hn.1 0
    obtain ⟨b, hbS, hbq⟩ := hcov _ hXU
    exact mem_iUnion.2 ⟨⟨b, hbS⟩, hwΩ, hXU, hbq⟩
  calc ∫⁻ w, f w ∂curvMass Ω
      = ∫⁻ w in ⋃ b : S, Ω ∩ epstein Ω ⁻¹' hball b 1, f w ∂curvMass Ω := by
        rw [Measure.restrict_eq_self_of_ae_mem hae]
    _ ≤ _ := lintegral_iUnion_le _ _

/-- Theorem-6.1 helper (TL7), one cell of the weighted summation (sec06-lower.tex:239–256): with
`R = R_K`, `C(K)` from Proposition 6.5 and `Q = Q_K(2R_K)` from (3.4), for every `b ∈ ℍ³`,
`∫_{X⁻¹B(b,1)} k_p s² dâ + ∫_{X*⁻¹B(b,1)} k_p(R z*) s*² dâ* ≤ C e^{2Q} ∫_{𝒩 ∩ B(b,R)} k_p(w(q)) dvol`.
-/
theorem s06_tl_cell : ∀ K : ℝ, 1 ≤ K → ∃ R C : ℝ, 0 ≤ C ∧ ∀ Ω Ωs : Set ℂ,
    IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs → ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab → ∀ p ∈ Ω,
      ∀ b ∈ UHS,
        (∫⁻ w in Ω ∩ epstein Ω ⁻¹' hball b 1, ENNReal.ofReal (intrKernel Ω p w) ∂curvMass Ω) +
          (∫⁻ z in Ωs ∩ epstein Ωs ⁻¹' hball b 1,
            ENNReal.ofReal (intrKernel Ω p (lab (epstein Ωs z))) ∂curvMass Ωs) ≤
          ENNReal.ofReal C *
            ∫⁻ q in gap Ω Ωs ∩ hball b R, ENNReal.ofReal (intrKernel Ω p (lab q)) ∂hvol := by
  intro K hK
  obtain ⟨R', C', hR2, hPMV⟩ := prop_mass_volume K hK
  obtain ⟨A, B, D, hQK⟩ := prop_qi_QK K
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = A * (((R' : ℝ) + 2) + 2 * D) + B := ⟨_, rfl⟩
  refine ⟨R', C' * Real.exp (2 * Q), by positivity,
    fun Ω Ωs hpair hnl lab hlab p hp b hb => ?_⟩
  have hJ := s03_b0_jordanPair hpair
  have hΩ := s02_jordanPair_riemannMap hJ
  obtain ⟨-, hDg, hDs, hlabd⟩ := hQK Ω Ωs hpair hnl
  have hsep := (prop_separation_b hJ hnl).2
  have hDg' : ∀ q ∈ gap Ω Ωs, hdistSet q (horoUnion Ω) ≤ max D 0 := fun q hq =>
    (hDg q hq).trans (le_max_left _ _)
  have hDs' : ∀ ws ∈ Ωs, hdistSet (epstein Ωs ws) (horoUnion Ω) ≤ max D 0 := fun ws hws =>
    (hDs ws hws).trans (le_max_left _ _)
  have hpt : ∀ {q : ℂ × ℝ} {ℓ' : ℂ}, IsLabelledPt Ω Ωs lab q ℓ' →
      ℓ' ∈ Ω ∧ q ∈ UHS ∧ hdist q (epstein Ω ℓ') ≤ max D 0 := fun hq =>
    s03_qik_pt hpair hnl hsep hlab (le_max_right D 0) hDg' hDs' hq
  have hR2' : (2 : ℝ) ≤ R' := by exact_mod_cast hR2
  -- labelled points in `B(b, 1)` and `B(b, R)`: kernel ratio at most `e^Q` (2.17), (3.4)
  have hcmp : ∀ {q q' : ℂ × ℝ} {ℓ ℓ' : ℂ}, IsLabelledPt Ω Ωs lab q ℓ →
      IsLabelledPt Ω Ωs lab q' ℓ' → q ∈ hball b 1 → q' ∈ hball b R' →
      ENNReal.ofReal (intrKernel Ω p ℓ) ≤
        ENNReal.ofReal (Real.exp Q) * ENNReal.ofReal (intrKernel Ω p ℓ') := by
    intro q q' ℓ ℓ' hq hq' hqb hq'b
    refine s03_sc_kernel hΩ hp (hpt hq).1 (hpt hq').1 ?_
    rw [hQ]
    refine hlabd lab hlab q q' ℓ ℓ' _ hq hq' ?_
    have t := s02_hdist_triangle hqb.1 hb hq'b.1
    rw [s02_hdist_comm q b] at t
    have h1 := hqb.2
    have h2 := hq'b.2
    linarith
  have hsub : hball b 1 ⊆ hball b R' := fun _ hx => ⟨hx.1, hx.2.trans (by linarith)⟩
  have hT := s06_tl_meas hJ hb
  have hTs := s06_tl_meas (s03_b0_jordanPair (s03_qce_swap hpair)) hb
  -- an empty cell contributes nothing
  by_cases h0 : curvMass Ω (Ω ∩ epstein Ω ⁻¹' hball b 1) = 0 ∧
      curvMass Ωs (Ωs ∩ epstein Ωs ⁻¹' hball b 1) = 0
  · rw [setLIntegral_measure_zero _ _ h0.1, setLIntegral_measure_zero _ _ h0.2, add_zero]
    exact bot_le
  -- a reference labelled point `(q₀, ℓ₀)` with `q₀ ∈ B(b, 1)`
  obtain ⟨q₀, ℓ₀, hlab₀, hq₀⟩ : ∃ q₀ ℓ₀, IsLabelledPt Ω Ωs lab q₀ ℓ₀ ∧ q₀ ∈ hball b 1 := by
    rcases not_and_or.1 h0 with h | h
    · obtain ⟨w, hw, hwb⟩ := nonempty_of_measure_ne_zero h
      exact ⟨_, w, Or.inl ⟨hw, rfl⟩, hwb⟩
    · obtain ⟨z, hz, hzb⟩ := nonempty_of_measure_ne_zero h
      exact ⟨_, _, Or.inr (Or.inl ⟨z, hz, rfl, rfl⟩), hzb⟩
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = ENNReal.ofReal (intrKernel Ω p ℓ₀) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = ENNReal.ofReal (Real.exp Q) := ⟨_, rfl⟩
  have hF1 : ∫⁻ w in Ω ∩ epstein Ω ⁻¹' hball b 1, ENNReal.ofReal (intrKernel Ω p w) ∂curvMass Ω ≤
      e * κ * curvMass Ω (epstein Ω ⁻¹' hball b 1) := by
    calc _ ≤ ∫⁻ _ in Ω ∩ epstein Ω ⁻¹' hball b 1, e * κ ∂curvMass Ω :=
          setLIntegral_mono' hT fun w hw => by
            rw [he, hκ, mul_comm]
            exact (hcmp (Or.inl ⟨hw.1, rfl⟩) hlab₀ hw.2 (hsub hq₀)).trans_eq (mul_comm _ _)
      _ ≤ e * κ * curvMass Ω (epstein Ω ⁻¹' hball b 1) := by
          rw [setLIntegral_const]
          exact mul_le_mul' le_rfl (measure_mono inter_subset_right)
  have hF2 : ∫⁻ z in Ωs ∩ epstein Ωs ⁻¹' hball b 1,
        ENNReal.ofReal (intrKernel Ω p (lab (epstein Ωs z))) ∂curvMass Ωs ≤
      e * κ * curvMass Ωs (epstein Ωs ⁻¹' hball b 1) := by
    calc _ ≤ ∫⁻ _ in Ωs ∩ epstein Ωs ⁻¹' hball b 1, e * κ ∂curvMass Ωs :=
          setLIntegral_mono' hTs fun z hz => by
            rw [he, hκ, mul_comm]
            exact (hcmp (Or.inr (Or.inl ⟨z, hz.1, rfl, rfl⟩)) hlab₀ hz.2 (hsub hq₀)).trans_eq
              (mul_comm _ _)
      _ ≤ e * κ * curvMass Ωs (epstein Ωs ⁻¹' hball b 1) := by
          rw [setLIntegral_const]
          exact mul_le_mul' le_rfl (measure_mono inter_subset_right)
  -- the gap side: `κ vol(𝒩 ∩ B(b, R)) ≤ e^Q ∫_{𝒩 ∩ B(b,R)} k_p(w(q))`
  have hGm : MeasurableSet (gap Ω Ωs ∩ hball b R') :=
    (s06_tl_gap_meas hpair hnl).inter (s05_pk_hball_meas _ _)
  have hG : κ * hvol (gap Ω Ωs ∩ hball b R') ≤
      e * ∫⁻ q in gap Ω Ωs ∩ hball b R', ENNReal.ofReal (intrKernel Ω p (lab q)) ∂hvol := by
    rw [← setLIntegral_const, ← lintegral_const_mul' _ _ (by rw [he]; exact ENNReal.ofReal_ne_top)]
    refine setLIntegral_mono' hGm fun q hq => ?_
    rw [he, hκ]
    exact hcmp hlab₀ (Or.inr (Or.inr ⟨hq.1, rfl⟩)) hq₀ hq.2
  have hP := hPMV Ω Ωs hpair hnl b hb
  calc _ ≤ e * κ * curvMass Ω (epstein Ω ⁻¹' hball b 1) +
        e * κ * curvMass Ωs (epstein Ωs ⁻¹' hball b 1) := add_le_add hF1 hF2
    _ = e * κ * (curvMass Ω (epstein Ω ⁻¹' hball b 1) +
        curvMass Ωs (epstein Ωs ⁻¹' hball b 1)) := by ring
    _ ≤ e * κ * ((C' : ℝ≥0∞) * hvol (gap Ω Ωs ∩ hball b R')) := mul_le_mul' le_rfl hP
    _ = e * C' * (κ * hvol (gap Ω Ωs ∩ hball b R')) := by ring
    _ ≤ e * C' * (e * ∫⁻ q in gap Ω Ωs ∩ hball b R',
        ENNReal.ofReal (intrKernel Ω p (lab q)) ∂hvol) := mul_le_mul' le_rfl hG
    _ = ENNReal.ofReal (C' * Real.exp (2 * Q)) * ∫⁻ q in gap Ω Ωs ∩ hball b R',
        ENNReal.ofReal (intrKernel Ω p (lab q)) ∂hvol := by
        rw [he, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal,
          show 2 * Q = Q + Q by ring, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
        ring

/-- **Theorem 6.1** (`thm:lower`, sec06-lower.tex:5).  For every `K ≥ 1` there is `C(K) < ∞` such
that for every `K`-quasicircle, every label and every `p ∈ Ω`, `K_{H,2}(p) ≤ C(K) K_V(p)` (6.1)
(`eq:lower`). -/
theorem thm_lower : ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ≥0, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
    ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab → ∀ p ∈ Ω,
      KH2 Ω Ωs lab p ≤ (C : ℝ≥0∞) * KV Ω Ωs lab p := by
  intro K hK
  obtain ⟨R, C, hC0, hcell⟩ := s06_tl_cell K hK
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = 23328 * Real.cosh (R + 1 / 3) ^ 6 := ⟨_, rfl⟩
  refine ⟨(C * N).toNNReal, fun Ω Ωs hpair lab hlab p hp => ?_⟩
  by_cases hl : IsLinePair Ω Ωs
  · -- circles: `K_{H,2} = 0`
    obtain ⟨h1, h2⟩ := s06_tl_line hl
    have e : KH2 Ω Ωs lab p = 0 := by
      show (∫⁻ w, _ ∂curvMass Ω) + ∫⁻ z, _ ∂curvMass Ωs = 0
      rw [h1, h2, lintegral_zero_measure, lintegral_zero_measure, add_zero]
    rw [e]
    exact bot_le
  obtain ⟨S, hSU, hS, hcov⟩ := s06_tl_net
  have hSc := s06_tl_countable hSU hS
  have hJ := s03_b0_jordanPair hpair
  have hJs := s03_b0_jordanPair (s03_qce_swap hpair)
  have hKH := s06_tl_cover hJ hSc hcov (fun w => ENNReal.ofReal (intrKernel Ω p w))
  have hKs := s06_tl_cover hJs hSc hcov
    (fun z => ENNReal.ofReal (intrKernel Ω p (lab (epstein Ωs z))))
  obtain ⟨g, hg⟩ : ∃ g : ℂ × ℝ → ℝ≥0∞, g = fun q => ENNReal.ofReal (intrKernel Ω p (lab q)) :=
    ⟨_, rfl⟩
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
  calc KH2 Ω Ωs lab p
      ≤ ∑' b : S, ((∫⁻ w in Ω ∩ epstein Ω ⁻¹' hball b 1, ENNReal.ofReal (intrKernel Ω p w)
            ∂curvMass Ω) +
          ∫⁻ z in Ωs ∩ epstein Ωs ⁻¹' hball b 1,
            ENNReal.ofReal (intrKernel Ω p (lab (epstein Ωs z))) ∂curvMass Ωs) := by
        rw [tsum_add]
        exact add_le_add hKH hKs
    _ ≤ ∑' b : S, ENNReal.ofReal C * ∫⁻ q in gap Ω Ωs ∩ hball b R, g q ∂hvol := by
        rw [hg]
        exact tsum_le_tsum fun b => hcell Ω Ωs hpair hl lab hlab p hp b (hSU b.2)
    _ = ENNReal.ofReal C *
          ∑' b : S, ∫⁻ q, (hball (b : ℂ × ℝ) R).indicator g q ∂(hvol.restrict (gap Ω Ωs)) := by
        rw [ENNReal.tsum_mul_left]
        congr 1
        refine tsum_congr fun b => ?_
        rw [lintegral_indicator (s05_pk_hball_meas _ _),
          Measure.restrict_restrict (s05_pk_hball_meas _ _), inter_comm]
    _ ≤ ENNReal.ofReal C *
          ∫⁻ q, ∑' b : S, (hball (b : ℂ × ℝ) R).indicator g q ∂(hvol.restrict (gap Ω Ωs)) := by
        gcongr
        exact s05_ct_tsum_lintegral_le _ _
    _ ≤ ENNReal.ofReal C * ∫⁻ q, ENNReal.ofReal N * g q ∂(hvol.restrict (gap Ω Ωs)) := by
        gcongr with q
        exact hmult q
    _ = ((C * N).toNNReal : ℝ≥0∞) * KV Ω Ωs lab p := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
          ← ENNReal.ofReal_mul hC0, hg]
        rfl

/-- **Theorem A** (`thm_A`, sec01-intro.tex:190; proof sec06-lower.tex:263).  For every `K ≥ 1`
there are `c(K) > 0` and `C(K) < ∞` such that for every `K`-quasicircle, every label and every
`p ∈ Ω`, `c(K)(K_H(p) + K_*(p)) ≤ K_V(p) ≤ C(K)(K_H(p) + K_*(p))`, as extended nonnegative
integrals. -/
theorem thm_A : ∀ K : ℝ, 1 ≤ K → ∃ c C : ℝ≥0, 0 < c ∧ ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
    ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab → ∀ p ∈ Ω,
      (c : ℝ≥0∞) * KH2 Ω Ωs lab p ≤ KV Ω Ωs lab p ∧
        KV Ω Ωs lab p ≤ (C : ℝ≥0∞) * KH2 Ω Ωs lab p := by
  intro K hK
  obtain ⟨Cu, hu⟩ := thm_upper K hK
  obtain ⟨Cl, hl⟩ := thm_lower K hK
  have hm : (0 : ℝ≥0) < max Cl 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(max Cl 1)⁻¹, Cu, inv_pos.mpr hm, fun Ω Ωs hΩ lab hlab p hp => ?_⟩
  refine ⟨?_, hu Ω Ωs hΩ lab hlab p hp⟩
  calc (((max Cl 1)⁻¹ : ℝ≥0) : ℝ≥0∞) * KH2 Ω Ωs lab p
      ≤ (((max Cl 1)⁻¹ : ℝ≥0) : ℝ≥0∞) * (((max Cl 1 : ℝ≥0) : ℝ≥0∞) * KV Ω Ωs lab p) := by
        gcongr
        calc KH2 Ω Ωs lab p ≤ (Cl : ℝ≥0∞) * KV Ω Ωs lab p := hl Ω Ωs hΩ lab hlab p hp
          _ ≤ _ := by
            gcongr
            exact_mod_cast le_max_left _ _
    _ = KV Ω Ωs lab p := by
        rw [← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hm.ne', ENNReal.coe_one, one_mul]

/-- **Remark 6.7** (`rem:symmetric`, sec06-lower.tex:275).  Exchanging `Ω` and `Ω*` gives the
symmetric version of Theorem A for the quantities based at `p* ∈ Ω*`, with labels in `Ω*`; both
versions involve the same gap `𝒩`. -/
theorem rem_symmetric : ∀ K : ℝ, 1 ≤ K → ∃ c C : ℝ≥0, 0 < c ∧ ∀ Ω Ωs : Set ℂ,
    IsKQuasiPair Ω Ωs K →
      gap Ωs Ω = gap Ω Ωs ∧
      ∀ lab : ℂ × ℝ → ℂ, IsLabel Ωs lab → ∀ p ∈ Ωs,
        (c : ℝ≥0∞) * KH2 Ωs Ω lab p ≤ KV Ωs Ω lab p ∧
          KV Ωs Ω lab p ≤ (C : ℝ≥0∞) * KH2 Ωs Ω lab p := by
  intro K hK
  obtain ⟨c, C, hc, hA⟩ := thm_A K hK
  refine ⟨c, C, hc, fun Ω Ωs hΩ => ⟨?_, hA Ωs Ω (s03_qce_swap hΩ)⟩⟩
  simp only [gap, union_comm]

end EpsteinVMO
