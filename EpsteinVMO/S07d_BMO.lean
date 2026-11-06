import EpsteinVMO.S07b_ShenWei

/-!
# Shen–Wei (B2) ⇒ (B5): host module (Round BMO)

Created by the leader on 2026-11-06 (Round BMO, `collaboration/ROUND_BMO.md`). Route R1 (Bishop–Jones Thm 4 +
Astala–Zinsmeister Thm 4): BMOA sawtooth stopping time (P1), sawtooth geometry and chord-arc images (P2),
Ahlfors bi-Lipschitz reflection (P3), weak A∞ of harmonic measure on qc-image domains with Ahlfors-regular
boundary (P4), harmonic-measure transfer (P5), per-arc assembly (P6), self-improvement to `IsStronglyQSWith` (P7).
The BMO targets (`thm_shen_wei_B5` (→), `s07_opp_two_sided_bmo`, `prop_opposite_d_bmo`, `thm_B_i`,
`cor_B_outer_i`) are assembled downstream (P8).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace EpsteinVMO

open LiZhongQC

/-- P4.5 helper (w4): the Poisson denominator dominates `(1 - r)²`. -/
theorem s07d_p4_core_den {r : ℝ} (hr0 : 0 ≤ r) (s : ℝ) :
    (1 - r) ^ 2 ≤ 1 - 2 * r * Real.cos s + r ^ 2 := by
  nlinarith [Real.cos_le_one s]

/-- P4.5 helper (w4): the Poisson denominator is positive for `0 ≤ r < 1`. -/
theorem s07d_p4_core_den_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (s : ℝ) :
    0 < 1 - 2 * r * Real.cos s + r ^ 2 := by
  have h := s07d_p4_core_den hr0 s
  have h1 : 0 < 1 - r := by linarith
  have : 0 < (1 - r) ^ 2 := by positivity
  linarith

/-- P4.5 helper (w4): the Poisson kernel is nonnegative. -/
theorem s07d_p4_core_k_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (s : ℝ) :
    0 ≤ (1 - r ^ 2) / (1 - 2 * r * Real.cos s + r ^ 2) :=
  div_nonneg (by nlinarith) (s07d_p4_core_den_pos hr0 hr1 s).le

/-- P4.5 helper (w4): `P_r ≤ 2/(1 - r)`. -/
theorem s07d_p4_core_k_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (s : ℝ) :
    (1 - r ^ 2) / (1 - 2 * r * Real.cos s + r ^ 2) ≤ 2 / (1 - r) := by
  have hd := s07d_p4_core_den hr0 s
  have hdp := s07d_p4_core_den_pos hr0 hr1 s
  have h1r : 0 < 1 - r := by linarith
  rw [div_le_div_iff₀ hdp h1r]
  have h2 : 0 ≤ (1 - r) ^ 2 * (1 - r) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ) ≤ 2)]

/-- P4.5 helper (w4): `1 - cos s ≥ 2 s²/π²` for `|s| ≤ π`. -/
theorem s07d_p4_core_one_sub_cos {s : ℝ} (hs : |s| ≤ π) :
    2 * s ^ 2 / π ^ 2 ≤ 1 - Real.cos s := by
  have hpi := Real.pi_pos
  have hhalf : |s / 2| ≤ π / 2 := by rw [abs_div, abs_two]; linarith
  have hj := Real.mul_abs_le_abs_sin hhalf
  have hc : Real.cos s = 1 - 2 * Real.sin (s / 2) ^ 2 := by
    have e : s = 2 * (s / 2) := by ring
    conv_lhs => rw [e]
    rw [Real.cos_two_mul, Real.cos_sq']
    ring
  rw [hc]
  have h1 : 2 / π * |s / 2| = |s| / π := by
    rw [abs_div, abs_two]
    field_simp
  rw [h1] at hj
  have h2 : (|s| / π) ^ 2 ≤ Real.sin (s / 2) ^ 2 := by
    rw [← sq_abs (Real.sin (s / 2))]
    exact pow_le_pow_left₀ (by positivity) hj 2
  have h3 : (|s| / π) ^ 2 = s ^ 2 / π ^ 2 := by rw [div_pow, sq_abs]
  rw [h3] at h2
  have h4 : 2 * s ^ 2 / π ^ 2 = 2 * (s ^ 2 / π ^ 2) := by ring
  linarith

/-- P4.5 helper (w4): tail bound `P_r(s) s² ≤ 8π² (1 - r)` for `|s| ≤ π`. -/
theorem s07d_p4_core_k_tail {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {s : ℝ} (hs : |s| ≤ π) :
    (1 - r ^ 2) / (1 - 2 * r * Real.cos s + r ^ 2) * s ^ 2 ≤ 8 * π ^ 2 * (1 - r) := by
  have hc := s07d_p4_core_one_sub_cos hs
  have hdp := s07d_p4_core_den_pos hr0 hr1 s
  have hpi := Real.pi_pos
  have hs2 : s ^ 2 ≤ π ^ 2 := by
    rw [← sq_abs s]
    exact pow_le_pow_left₀ (abs_nonneg s) hs 2
  set q : ℝ := s ^ 2 / (4 * π ^ 2) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq4 : q ≤ 1 / 4 := by
    rw [hq, div_le_iff₀ (by positivity)]
    nlinarith
  have hq8 : 2 * s ^ 2 / π ^ 2 = 8 * q := by
    rw [hq]
    field_simp
    ring
  rw [hq8] at hc
  have hd : q ≤ 1 - 2 * r * Real.cos s + r ^ 2 := by
    have e : 1 - 2 * r * Real.cos s + r ^ 2 = (1 - r) ^ 2 + 2 * r * (1 - Real.cos s) := by ring
    rw [e]
    have hm : 2 * r * (8 * q) ≤ 2 * r * (1 - Real.cos s) :=
      mul_le_mul_of_nonneg_left hc (by linarith)
    rcases le_total r (1 / 2) with h | h
    · nlinarith
    · nlinarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hdp]
  have h1r : 0 < 1 - r := by linarith
  have hsq : s ^ 2 = 4 * π ^ 2 * q := by
    rw [hq]
    field_simp
  calc (1 - r ^ 2) * s ^ 2 ≤ 2 * (1 - r) * s ^ 2 :=
        mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg s)
    _ = 8 * π ^ 2 * (1 - r) * q := by rw [hsq]; ring
    _ ≤ 8 * π ^ 2 * (1 - r) * (1 - 2 * r * Real.cos s + r ^ 2) :=
        mul_le_mul_of_nonneg_left hd (by positivity)

/-- P4.5 helper (w4): lower bound `P_r(s) ≥ 1/((1 + π²)(1 - r))` for `|s| ≤ π (1 - r)`. -/
theorem s07d_p4_core_k_low {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {s : ℝ} (hs : |s| ≤ π * (1 - r)) :
    1 / ((1 + π ^ 2) * (1 - r)) ≤ (1 - r ^ 2) / (1 - 2 * r * Real.cos s + r ^ 2) := by
  have hdp := s07d_p4_core_den_pos hr0 hr1 s
  have h1r : 0 < 1 - r := by linarith
  have hc : 1 - s ^ 2 / 2 ≤ Real.cos s := Real.one_sub_sq_div_two_le_cos
  have hs2 : s ^ 2 ≤ (π * (1 - r)) ^ 2 := by
    rw [← sq_abs s]
    exact pow_le_pow_left₀ (abs_nonneg s) hs 2
  have hm : 2 * r * (1 - s ^ 2 / 2) ≤ 2 * r * Real.cos s :=
    mul_le_mul_of_nonneg_left hc (by linarith)
  have hrs : r * s ^ 2 ≤ s ^ 2 := by nlinarith [sq_nonneg s]
  have hd : 1 - 2 * r * Real.cos s + r ^ 2 ≤ (1 + π ^ 2) * (1 - r) ^ 2 := by
    nlinarith
  rw [div_le_div_iff₀ (by positivity) hdp]
  have h5 : 0 ≤ r * (1 - r) ^ 2 * (1 + π ^ 2) := by positivity
  nlinarith

/-- P4.5 helper (w4): `|e^{it} - r e^{iφ}|² = 1 - 2 r cos(t - φ) + r²`. -/
theorem s07d_p4_core_norm (r φ t : ℝ) :
    ‖Complex.exp (t * Complex.I) - (r : ℂ) * Complex.exp (φ * Complex.I)‖ ^ 2 =
      1 - 2 * r * Real.cos (t - φ) + r ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [Real.cos_sub]
  have h1 := Real.sin_sq_add_cos_sq t
  have h2 := Real.sin_sq_add_cos_sq φ
  linear_combination h1 + r ^ 2 * h2

/-- P4.5 helper (w4): the Poisson kernel has mass one over a period centred at `φ`. -/
theorem s07d_p4_core_mass {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (φ : ℝ) :
    (1 / (2 * π)) * ∫ t in (φ - π)..(φ + π),
      (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) = 1 := by
  set z : ℂ := (r : ℂ) * Complex.exp (φ * Complex.I) with hz
  have hzn : ‖z‖ = r := by
    rw [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr0]
  have hzD : z ∈ unitDisc := by
    show z ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, hzn]
    exact hr1
  have hm := s07c_fkps_m2_kernel_mass z hzD
  have hcongr : ∀ t : ℝ, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 =
      (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) := fun t => by
    rw [hzn, hz, s07d_p4_core_norm]
  simp only [hcongr] at hm
  rw [s07c_fkps_m2_shift _ (fun t => by
    rw [show t + 2 * π - φ = (t - φ) + 2 * π by ring, Real.cos_add_two_pi]) φ] at hm
  rw [one_div]
  exact hm

/-- P4.5 helper (w4): the tangent-line bound `log y ≤ log T + y/T - 1`. -/
theorem s07d_p4_core_tangent {y T : ℝ} (hy : 0 < y) (hT : 0 < T) :
    Real.log y ≤ Real.log T + y / T - 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hT)
  rw [Real.log_div hy.ne' hT.ne'] at h
  linarith

/-- P4.5 helper (w4): dyadic shell: if `x > ℓ/2` there is `n ≥ 1` with
`2ⁿ ℓ/4 < x ≤ 2ⁿ ℓ/2`. -/
theorem s07d_p4_core_shell {ℓ x : ℝ} (hℓ : 0 < ℓ) (hx : ℓ / 2 < x) :
    ∃ n : ℕ, 1 ≤ n ∧ 2 ^ n * ℓ / 4 < x ∧ x ≤ 2 ^ n * ℓ / 2 := by
  classical
  have hex : ∃ n : ℕ, x ≤ 2 ^ n * ℓ / 2 := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * x / ℓ) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ hℓ] at hn
    linarith
  have hpos : 0 < Nat.find hex := by
    by_contra h0
    have h00 : Nat.find hex = 0 := by omega
    have hs := Nat.find_spec hex
    rw [h00, pow_zero, one_mul] at hs
    linarith
  refine ⟨Nat.find hex, hpos, ?_, Nat.find_spec hex⟩
  have hlt := Nat.find_min hex (Nat.sub_lt hpos one_pos)
  rw [not_le] at hlt
  have he : (2 : ℝ) ^ Nat.find hex = 2 * 2 ^ (Nat.find hex - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [he]
  linarith

/-- P4.5 helper (w4): for `0 < ℓ ≤ 2π` there is `N` with `2π ≤ 2ᴺ ℓ ≤ 4π`. -/
theorem s07d_p4_core_N {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ2 : ℓ ≤ 2 * π) :
    ∃ N : ℕ, 2 * π ≤ 2 ^ N * ℓ ∧ 2 ^ N * ℓ ≤ 4 * π := by
  classical
  have hpi := Real.pi_pos
  have hex : ∃ n : ℕ, 2 * π ≤ 2 ^ n * ℓ := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * π / ℓ) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ hℓ] at hn
    linarith
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, pow_zero, one_mul]
    linarith
  · have hlt := Nat.find_min hex (Nat.sub_lt hpos one_pos)
    rw [not_le] at hlt
    have he : (2 : ℝ) ^ Nat.find hex = 2 * 2 ^ (Nat.find hex - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [he]
    nlinarith

/-- P4.5 helper (w4): iterated doubling `ν(2ʲ J) ≤ Dʲ ν(J)` for `2ʲ |J| ≤ 4π`. -/
theorem s07d_p4_core_dbl_iter {ν : Measure ℝ} {D : ℝ} (hD : 1 ≤ D)
    (hdbl : ∀ a b : ℝ, a < b → b - a ≤ 2 * π →
        ν (Icc (a - (b - a) / 2) (b + (b - a) / 2)) ≤ ENNReal.ofReal D * ν (Icc a b))
    (φ : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) : ∀ j : ℕ, 2 ^ j * ℓ ≤ 4 * π →
      ν (Icc (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2)) ≤
        ENNReal.ofReal (D ^ j) * ν (Icc (φ - ℓ / 2) (φ + ℓ / 2)) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp
  | succ k ih =>
    intro hk
    have hp : (0 : ℝ) < 2 ^ k * ℓ := by positivity
    have hk2 : (2 : ℝ) ^ (k + 1) * ℓ = 2 * (2 ^ k * ℓ) := by ring
    rw [hk2] at hk
    have hk' : 2 ^ k * ℓ ≤ 4 * π := by linarith
    have h := hdbl (φ - 2 ^ k * ℓ / 2) (φ + 2 ^ k * ℓ / 2) (by linarith) (by linarith)
    have e1 : φ - 2 ^ k * ℓ / 2 - (φ + 2 ^ k * ℓ / 2 - (φ - 2 ^ k * ℓ / 2)) / 2 =
        φ - 2 ^ (k + 1) * ℓ / 2 := by ring
    have e2 : φ + 2 ^ k * ℓ / 2 + (φ + 2 ^ k * ℓ / 2 - (φ - 2 ^ k * ℓ / 2)) / 2 =
        φ + 2 ^ (k + 1) * ℓ / 2 := by ring
    rw [e1, e2] at h
    have hD0 : (0 : ℝ) ≤ D := by linarith
    calc ν (Icc (φ - 2 ^ (k + 1) * ℓ / 2) (φ + 2 ^ (k + 1) * ℓ / 2))
        ≤ ENNReal.ofReal D * ν (Icc (φ - 2 ^ k * ℓ / 2) (φ + 2 ^ k * ℓ / 2)) := h
      _ ≤ ENNReal.ofReal D * (ENNReal.ofReal (D ^ k) * ν (Icc (φ - ℓ / 2) (φ + ℓ / 2))) := by
          gcongr
          exact ih hk'
      _ = ENNReal.ofReal (D ^ (k + 1)) * ν (Icc (φ - ℓ / 2) (φ + ℓ / 2)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hD0, pow_succ, mul_comm D]

/-- P4.5 helper (w4): `∑_{j<n} j/2ʲ + 2(n+1)/2ⁿ = 2`. -/
theorem s07d_p4_core_sum_j (n : ℕ) :
    ∑ j ∈ Finset.range n, (j : ℝ) / 2 ^ j + 2 * ((n : ℝ) + 1) / 2 ^ n = 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    have e : 2 * (((k + 1 : ℕ) : ℝ) + 1) / 2 ^ (k + 1) = ((k : ℝ) + 2) / 2 ^ k := by
      rw [pow_succ]
      push_cast
      field_simp
      ring
    rw [e]
    have e2 : (k : ℝ) / 2 ^ k + ((k : ℝ) + 2) / 2 ^ k = 2 * ((k : ℝ) + 1) / 2 ^ k := by
      field_simp
      ring
    linarith

/-- P4.5 helper (w4): `∑_{j<n} j/2ʲ ≤ 2`. -/
theorem s07d_p4_core_sum_j_le (n : ℕ) : ∑ j ∈ Finset.range n, (j : ℝ) / 2 ^ j ≤ 2 := by
  have h := s07d_p4_core_sum_j n
  have : 0 ≤ 2 * ((n : ℝ) + 1) / 2 ^ n := by positivity
  linarith

/-- P4.5 helper (w4): `∑_{j<n} (1/2)ʲ ≤ 2` and `∑_{j<n} (1/4)ʲ ≤ 4/3`. -/
theorem s07d_p4_core_geom (n : ℕ) :
    ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j ≤ 2 ∧ ∑ j ∈ Finset.range n, (1 / 4 : ℝ) ^ j ≤ 4 / 3 := by
  constructor
  · rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
    have : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
    rw [div_le_iff_of_neg (by norm_num)]
    linarith
  · rw [geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1)]
    have : 0 ≤ (1 / 4 : ℝ) ^ n := by positivity
    rw [div_le_iff_of_neg (by norm_num)]
    linarith

/-- P4.5 helper (w4): a nonnegative measurable `w` with `∫⁻_S w ≤ ν(S) < ∞` is integrable on `S`
and `∫_S w ≤ ν(S)`. -/
theorem s07d_p4_core_wint {ν : Measure ℝ} {w : ℝ → ℝ} (hwm : Measurable w) (hw0 : ∀ t, 0 ≤ w t)
    {S : Set ℝ} (hle : ∫⁻ t in S, ENNReal.ofReal (w t) ≤ ν S) (hfin : ν S ≠ ⊤) :
    IntegrableOn w S volume ∧ ∫ t in S, w t ≤ (ν S).toReal := by
  have hne : ∫⁻ t in S, ENNReal.ofReal (w t) ≠ ⊤ := ne_top_of_le_ne_top hfin hle
  have hm : AEMeasurable (fun t => ENNReal.ofReal (w t)) (volume.restrict S) :=
    (ENNReal.measurable_ofReal.comp hwm).aemeasurable
  have hint := integrable_toReal_of_lintegral_ne_top hm hne
  have he : (fun t => (ENNReal.ofReal (w t)).toReal) = w := by
    funext t
    exact ENNReal.toReal_ofReal (hw0 t)
  rw [he] at hint
  refine ⟨hint, ?_⟩
  have hi : ∫ t in S, w t = (∫⁻ t in S, ENNReal.ofReal (w t)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hw0) hwm.aestronglyMeasurable
  rw [hi]
  exact ENNReal.toReal_mono hfin hle

/-- P4.5 helper (w4): on the dyadic shell `|s| > 2ⁿ ℓ/4`, `P_r(s) ≤ 64π/(4ⁿ ℓ)` (`1 - r = ℓ/2π`). -/
theorem s07d_p4_core_k_shell {r ℓ s : ℝ} {n : ℕ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hℓ : 0 < ℓ)
    (hrℓ : 1 - r = ℓ / (2 * π)) (hs : |s| ≤ π) (hn : 2 ^ n * ℓ / 4 < |s|) :
    (1 - r ^ 2) / (1 - 2 * r * Real.cos s + r ^ 2) ≤ 64 * π / (4 ^ n * ℓ) := by
  have hpi := Real.pi_pos
  set K := (1 - r ^ 2) / (1 - 2 * r * Real.cos s + r ^ 2) with hK
  have hK0 : 0 ≤ K := s07d_p4_core_k_nonneg hr0 hr1 s
  have ht := s07d_p4_core_k_tail hr0 hr1 hs
  rw [← hK, hrℓ] at ht
  have ht' : K * s ^ 2 ≤ 4 * π * ℓ := by
    have e : 8 * π ^ 2 * (ℓ / (2 * π)) = 4 * π * ℓ := by field_simp; ring
    linarith
  have hp : 0 ≤ 2 ^ n * ℓ / 4 := by positivity
  have hs2 : (2 ^ n * ℓ / 4) ^ 2 ≤ s ^ 2 := by
    rw [← sq_abs s]
    exact pow_le_pow_left₀ hp hn.le 2
  have key : K * (2 ^ n * ℓ / 4) ^ 2 ≤ 4 * π * ℓ :=
    le_trans (mul_le_mul_of_nonneg_left hs2 hK0) ht'
  have h4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by
    rw [← mul_pow]
    norm_num
  rw [le_div_iff₀ (by positivity)]
  have e : K * (4 ^ n * ℓ) = K * (2 ^ n * ℓ / 4) ^ 2 * (16 / ℓ) := by
    rw [h4]
    field_simp
    ring
  rw [e]
  calc K * (2 ^ n * ℓ / 4) ^ 2 * (16 / ℓ) ≤ 4 * π * ℓ * (16 / ℓ) :=
        mul_le_mul_of_nonneg_right key (by positivity)
    _ = 64 * π := by field_simp; ring

/-- P4.5 helper (w4): pointwise dyadic bound for `P_r · log max(1, 2|t - φ|/ℓ)`. -/
theorem s07d_p4_core_ptw3 {r φ ℓ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hℓ : 0 < ℓ)
    (hrℓ : 1 - r = ℓ / (2 * π)) {N : ℕ} (hN : 2 * π ≤ 2 ^ N * ℓ) {t : ℝ} (ht : |t - φ| ≤ π) :
    (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) * Real.log (max 1 (2 * |t - φ| / ℓ)) ≤
      ∑ j ∈ Finset.range (N + 1), 64 * π * j * Real.log 2 / (4 ^ j * ℓ) *
        (Icc (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2)).indicator 1 t := by
  have hpi := Real.pi_pos
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hK0 := s07d_p4_core_k_nonneg hr0 hr1 (t - φ)
  have hterm : ∀ j ∈ Finset.range (N + 1), 0 ≤ 64 * π * j * Real.log 2 / (4 ^ j * ℓ) *
      (Icc (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2)).indicator 1 t := fun j _ => by
    apply mul_nonneg
    · positivity
    · exact Set.indicator_nonneg (fun _ _ => zero_le_one) t
  rcases le_or_gt (|t - φ|) (ℓ / 2) with hs | hs
  · have hm : max 1 (2 * |t - φ| / ℓ) = 1 := by
      apply max_eq_left
      rw [div_le_iff₀ hℓ]
      linarith
    rw [hm, Real.log_one, mul_zero]
    exact Finset.sum_nonneg hterm
  · obtain ⟨n, hn1, hnl, hnu⟩ := s07d_p4_core_shell hℓ hs
    have hnN : n ∈ Finset.range (N + 1) := by
      rw [Finset.mem_range]
      have h1 : 2 ^ n * ℓ < 2 ^ (N + 1) * ℓ := by
        rw [pow_succ]
        linarith
      have h2 : (2 : ℝ) ^ n < 2 ^ (N + 1) := lt_of_mul_lt_mul_right h1 hℓ.le
      exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h2
    have hmax : max 1 (2 * |t - φ| / ℓ) = 2 * |t - φ| / ℓ := by
      apply max_eq_right
      rw [le_div_iff₀ hℓ]
      linarith
    have hL : Real.log (2 * |t - φ| / ℓ) ≤ n * Real.log 2 := by
      rw [← Real.log_pow]
      apply Real.log_le_log (div_pos (by linarith) hℓ)
      rw [div_le_iff₀ hℓ]
      linarith
    have hL0 : 0 ≤ Real.log (2 * |t - φ| / ℓ) :=
      Real.log_nonneg (by rw [le_div_iff₀ hℓ]; linarith)
    have hK := s07d_p4_core_k_shell hr0 hr1 hℓ hrℓ ht hnl
    have hmem : t ∈ Icc (φ - 2 ^ n * ℓ / 2) (φ + 2 ^ n * ℓ / 2) := by
      obtain ⟨h1, h2⟩ := abs_le.1 hnu
      constructor <;> linarith
    have hind : (Icc (φ - 2 ^ n * ℓ / 2) (φ + 2 ^ n * ℓ / 2)).indicator (1 : ℝ → ℝ) t = 1 := by
      rw [Set.indicator_of_mem hmem, Pi.one_apply]
    calc (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) * Real.log (max 1 (2 * |t - φ| / ℓ))
        = (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) * Real.log (2 * |t - φ| / ℓ) := by
          rw [hmax]
      _ ≤ 64 * π / (4 ^ n * ℓ) * (n * Real.log 2) := mul_le_mul hK hL hL0 (by positivity)
      _ = 64 * π * n * Real.log 2 / (4 ^ n * ℓ) *
            (Icc (φ - 2 ^ n * ℓ / 2) (φ + 2 ^ n * ℓ / 2)).indicator 1 t := by
          rw [hind]
          ring
      _ ≤ _ := Finset.single_le_sum hterm hnN

/-- P4.5 helper (w4): pointwise dyadic bound for `P_r / κ`, `κ = exp(log_2 D · log max(1, 2|t-φ|/ℓ))`. -/
theorem s07d_p4_core_ptw5 {r φ ℓ D : ℝ} (hD : 1 ≤ D) (hr0 : 0 ≤ r) (hr1 : r < 1) (hℓ : 0 < ℓ)
    (hrℓ : 1 - r = ℓ / (2 * π)) {N : ℕ} (hN : 2 * π ≤ 2 ^ N * ℓ) {t : ℝ} (ht : |t - φ| ≤ π) :
    (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) /
        Real.exp (Real.log D / Real.log 2 * Real.log (max 1 (2 * |t - φ| / ℓ))) ≤
      ∑ j ∈ Finset.range (N + 1), 64 * π * D / (4 ^ j * ℓ * D ^ j) *
        (Icc (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2)).indicator 1 t := by
  have hpi := Real.pi_pos
  have hD0 : 0 < D := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hK0 := s07d_p4_core_k_nonneg hr0 hr1 (t - φ)
  have hterm : ∀ j ∈ Finset.range (N + 1), 0 ≤ 64 * π * D / (4 ^ j * ℓ * D ^ j) *
      (Icc (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2)).indicator 1 t := fun j _ => by
    apply mul_nonneg
    · positivity
    · exact Set.indicator_nonneg (fun _ _ => zero_le_one) t
  rcases le_or_gt (|t - φ|) (ℓ / 2) with hs | hs
  · have hm : max 1 (2 * |t - φ| / ℓ) = 1 := by
      apply max_eq_left
      rw [div_le_iff₀ hℓ]
      linarith
    rw [hm, Real.log_one, mul_zero, Real.exp_zero, div_one]
    have hK := s07d_p4_core_k_le hr0 hr1 (t - φ)
    rw [hrℓ] at hK
    have hmem : t ∈ Icc (φ - 2 ^ 0 * ℓ / 2) (φ + 2 ^ 0 * ℓ / 2) := by
      obtain ⟨h1, h2⟩ := abs_le.1 hs
      rw [pow_zero, one_mul]
      constructor <;> linarith
    have hind : (Icc (φ - 2 ^ 0 * ℓ / 2) (φ + 2 ^ 0 * ℓ / 2)).indicator (1 : ℝ → ℝ) t = 1 := by
      rw [Set.indicator_of_mem hmem, Pi.one_apply]
    have h0 : (0 : ℕ) ∈ Finset.range (N + 1) := by
      rw [Finset.mem_range]
      omega
    calc (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) ≤ 2 / (ℓ / (2 * π)) := hK
      _ ≤ 64 * π * D / (4 ^ 0 * ℓ * D ^ 0) *
            (Icc (φ - 2 ^ 0 * ℓ / 2) (φ + 2 ^ 0 * ℓ / 2)).indicator 1 t := by
          rw [hind, pow_zero, pow_zero, one_mul, mul_one, mul_one]
          have e : 2 / (ℓ / (2 * π)) = 4 * π / ℓ := by field_simp; ring
          rw [e]
          apply div_le_div_of_nonneg_right _ hℓ.le
          nlinarith
      _ ≤ _ := Finset.single_le_sum hterm h0
  · obtain ⟨n, hn1, hnl, hnu⟩ := s07d_p4_core_shell hℓ hs
    have hnN : n ∈ Finset.range (N + 1) := by
      rw [Finset.mem_range]
      have h1 : 2 ^ n * ℓ < 2 ^ (N + 1) * ℓ := by
        rw [pow_succ]
        linarith
      have h2 : (2 : ℝ) ^ n < 2 ^ (N + 1) := lt_of_mul_lt_mul_right h1 hℓ.le
      exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h2
    have hmax : max 1 (2 * |t - φ| / ℓ) = 2 * |t - φ| / ℓ := by
      apply max_eq_right
      rw [le_div_iff₀ hℓ]
      linarith
    have hL : (n : ℝ) * Real.log 2 - Real.log 2 ≤ Real.log (2 * |t - φ| / ℓ) := by
      have e : (n : ℝ) * Real.log 2 - Real.log 2 = Real.log (2 ^ n / 2) := by
        rw [Real.log_div (by positivity) (by norm_num), Real.log_pow]
      rw [e]
      apply Real.log_le_log (by positivity)
      rw [le_div_iff₀ hℓ]
      linarith
    have hκ : D ^ n / D ≤
        Real.exp (Real.log D / Real.log 2 * Real.log (max 1 (2 * |t - φ| / ℓ))) := by
      rw [hmax]
      have e : D ^ n / D = Real.exp (n * Real.log D - Real.log D) := by
        rw [Real.exp_sub, Real.exp_log hD0, Real.exp_nat_mul, Real.exp_log hD0]
      rw [e]
      apply Real.exp_le_exp.2
      have hγ : 0 ≤ Real.log D / Real.log 2 := div_nonneg hlD hl2.le
      have := mul_le_mul_of_nonneg_left hL hγ
      have e2 : Real.log D / Real.log 2 * ((n : ℝ) * Real.log 2 - Real.log 2) =
          n * Real.log D - Real.log D := by
        field_simp
      linarith
    have hK := s07d_p4_core_k_shell hr0 hr1 hℓ hrℓ ht hnl
    have hmem : t ∈ Icc (φ - 2 ^ n * ℓ / 2) (φ + 2 ^ n * ℓ / 2) := by
      obtain ⟨h1, h2⟩ := abs_le.1 hnu
      constructor <;> linarith
    have hind : (Icc (φ - 2 ^ n * ℓ / 2) (φ + 2 ^ n * ℓ / 2)).indicator (1 : ℝ → ℝ) t = 1 := by
      rw [Set.indicator_of_mem hmem, Pi.one_apply]
    have hDn : 0 < D ^ n / D := by positivity
    calc (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) /
          Real.exp (Real.log D / Real.log 2 * Real.log (max 1 (2 * |t - φ| / ℓ)))
        ≤ (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) / (D ^ n / D) :=
          div_le_div_of_nonneg_left hK0 hDn hκ
      _ ≤ 64 * π / (4 ^ n * ℓ) / (D ^ n / D) := div_le_div_of_nonneg_right hK hDn.le
      _ = 64 * π * D / (4 ^ n * ℓ * D ^ n) *
            (Icc (φ - 2 ^ n * ℓ / 2) (φ + 2 ^ n * ℓ / 2)).indicator 1 t := by
          rw [hind]
          field_simp
      _ ≤ _ := Finset.single_le_sum hterm hnN

/-- P4.5 helper (w4): `∫_W S.indicator f ≤ ∫_S f` for `f ≥ 0` on `S`. -/
theorem s07d_p4_core_setind {f : ℝ → ℝ} {S W : Set ℝ} (hS : MeasurableSet S)
    (hf : IntegrableOn f S volume) (hf0 : ∀ t ∈ S, 0 ≤ f t) :
    ∫ t in W, S.indicator f t ≤ ∫ t in S, f t := by
  rw [setIntegral_indicator hS]
  exact setIntegral_mono_set hf ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall hf0))
    inter_subset_right.eventuallyLE

/-- P4.5 helper (w4): `∫_{[x, y]} 1 = y - x`. -/
theorem s07d_p4_core_int_one {x y : ℝ} (hxy : x ≤ y) : ∫ t in Icc x y, (1 : ℝ) = y - x := by
  rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]

/-- P4.5 helper (w4): the log-weight integral `∫_W P_r · log max(1, 2|t-φ|/ℓ) ≤ 128 π log 2`. -/
theorem s07d_p4_core_T3 {r φ ℓ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hℓ : 0 < ℓ)
    (hrℓ : 1 - r = ℓ / (2 * π)) {N : ℕ} (hN : 2 * π ≤ 2 ^ N * ℓ) :
    ∫ t in Icc (φ - π) (φ + π), (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) *
      Real.log (max 1 (2 * |t - φ| / ℓ)) ≤ 128 * π * Real.log 2 := by
  have hpi := Real.pi_pos
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcont : Continuous fun t : ℝ => (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) *
      Real.log (max 1 (2 * |t - φ| / ℓ)) := by
    refine Continuous.mul ?_ ?_
    · exact continuous_const.div (by fun_prop) fun t => (s07d_p4_core_den_pos hr0 hr1 _).ne'
    · refine Continuous.log ?_ fun t => (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
      exact continuous_const.max
        ((continuous_const.mul (continuous_abs.comp (continuous_id.sub continuous_const))).div_const ℓ)
  have hint : ∀ j ∈ Finset.range (N + 1), Integrable (fun t => 64 * π * j * Real.log 2 /
      (4 ^ j * ℓ) * (Icc (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2)).indicator 1 t)
      (volume.restrict (Icc (φ - π) (φ + π))) := fun j _ =>
    ((integrable_const (1 : ℝ)).indicator measurableSet_Icc).const_mul _
  calc ∫ t in Icc (φ - π) (φ + π), (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) *
        Real.log (max 1 (2 * |t - φ| / ℓ))
      ≤ ∫ t in Icc (φ - π) (φ + π), ∑ j ∈ Finset.range (N + 1), 64 * π * j * Real.log 2 /
          (4 ^ j * ℓ) * (Icc (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2)).indicator 1 t := by
        refine setIntegral_mono_on hcont.integrableOn_Icc (integrable_finsetSum _ hint)
          measurableSet_Icc fun t ht => ?_
        have hts : |t - φ| ≤ π := by
          rw [abs_le]
          constructor <;> linarith [ht.1, ht.2]
        exact s07d_p4_core_ptw3 hr0 hr1 hℓ hrℓ hN hts
    _ = ∑ j ∈ Finset.range (N + 1), 64 * π * j * Real.log 2 / (4 ^ j * ℓ) *
          ∫ t in Icc (φ - π) (φ + π), (Icc (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2)).indicator 1 t := by
        rw [integral_finsetSum _ hint]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact integral_const_mul _ _
    _ ≤ ∑ j ∈ Finset.range (N + 1), 64 * π * j * Real.log 2 / (4 ^ j * ℓ) * (2 ^ j * ℓ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hle : (φ - 2 ^ j * ℓ / 2) ≤ (φ + 2 ^ j * ℓ / 2) := by
          have : 0 ≤ 2 ^ j * ℓ / 2 := by positivity
          linarith
        calc ∫ t in Icc (φ - π) (φ + π), (Icc (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2)).indicator 1 t
            ≤ ∫ t in Icc (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2), (1 : ℝ → ℝ) t :=
              s07d_p4_core_setind measurableSet_Icc (integrableOn_const (by
                rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
                (fun _ _ => zero_le_one)
          _ = 2 ^ j * ℓ := by
              simp only [Pi.one_apply]
              rw [s07d_p4_core_int_one hle]
              ring
    _ = 64 * π * Real.log 2 * ∑ j ∈ Finset.range (N + 1), (j : ℝ) / 2 ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have h4 : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by
          rw [← mul_pow]
          norm_num
        rw [h4]
        field_simp
    _ ≤ 64 * π * Real.log 2 * 2 :=
        mul_le_mul_of_nonneg_left (s07d_p4_core_sum_j_le _) (by positivity)
    _ = 128 * π * Real.log 2 := by ring

/-- P4.5 helper (w4): the `ν`-weighted dyadic integral
`∫_W (w + τ) P_r / κ ≤ 128 π D Λ`, `Λ = ν(J)/|J|`, `τ ≤ Λ/4`. -/
theorem s07d_p4_core_T5 {ν : Measure ℝ} {w : ℝ → ℝ} {D r φ ℓ τ : ℝ} (hD : 1 ≤ D)
    (hfin : ∀ a b : ℝ, ν (Icc a b) ≠ ⊤)
    (hdbl : ∀ a b : ℝ, a < b → b - a ≤ 2 * π →
      ν (Icc (a - (b - a) / 2) (b + (b - a) / 2)) ≤ ENNReal.ofReal D * ν (Icc a b))
    (hwm : Measurable w) (hw0 : ∀ t, 0 ≤ w t)
    (hwν : ∀ E : Set ℝ, MeasurableSet E → ∫⁻ t in E, ENNReal.ofReal (w t) ≤ ν E)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hℓ : 0 < ℓ) (hrℓ : 1 - r = ℓ / (2 * π)) {N : ℕ}
    (hN1 : 2 * π ≤ 2 ^ N * ℓ) (hN2 : 2 ^ N * ℓ ≤ 4 * π) (hτ0 : 0 ≤ τ)
    (hτ : τ ≤ (ν (Icc (φ - ℓ / 2) (φ + ℓ / 2))).toReal / ℓ / 4) :
    ∫ t in Icc (φ - π) (φ + π), (w t + τ) *
      ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) /
        Real.exp (Real.log D / Real.log 2 * Real.log (max 1 (2 * |t - φ| / ℓ)))) ≤
      128 * π * D * ((ν (Icc (φ - ℓ / 2) (φ + ℓ / 2))).toReal / ℓ) := by
  have hpi := Real.pi_pos
  have hD0 : 0 < D := by linarith
  set V := (ν (Icc (φ - ℓ / 2) (φ + ℓ / 2))).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set Λ := V / ℓ with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hwW := s07d_p4_core_wint hwm hw0 (hwν _ measurableSet_Icc) (hfin (φ - π) (φ + π))
  have hwτW : IntegrableOn (fun t => w t + τ) (Icc (φ - π) (φ + π)) volume :=
    hwW.1.add (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hκc : Continuous fun t : ℝ =>
      Real.exp (Real.log D / Real.log 2 * Real.log (max 1 (2 * |t - φ| / ℓ))) := by
    refine Real.continuous_exp.comp (continuous_const.mul ?_)
    refine Continuous.log ?_ fun t => (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
    exact continuous_const.max
      ((continuous_const.mul (continuous_abs.comp (continuous_id.sub continuous_const))).div_const ℓ)
  have hqc : Continuous fun t : ℝ => (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) /
      Real.exp (Real.log D / Real.log 2 * Real.log (max 1 (2 * |t - φ| / ℓ))) := by
    refine Continuous.div ?_ hκc fun t => (Real.exp_pos _).ne'
    exact continuous_const.div (by fun_prop) fun t => (s07d_p4_core_den_pos hr0 hr1 _).ne'
  have hLHS : IntegrableOn (fun t => (w t + τ) *
      ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) /
        Real.exp (Real.log D / Real.log 2 * Real.log (max 1 (2 * |t - φ| / ℓ)))))
      (Icc (φ - π) (φ + π)) volume :=
    hwτW.mul_continuousOn hqc.continuousOn isCompact_Icc
  have hint : ∀ j ∈ Finset.range (N + 1), Integrable (fun t => 64 * π * D / (4 ^ j * ℓ * D ^ j) *
      (Icc (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2)).indicator (fun t => w t + τ) t)
      (volume.restrict (Icc (φ - π) (φ + π))) := fun j _ =>
    (hwτW.indicator measurableSet_Icc).const_mul _
  calc ∫ t in Icc (φ - π) (φ + π), (w t + τ) *
        ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) /
          Real.exp (Real.log D / Real.log 2 * Real.log (max 1 (2 * |t - φ| / ℓ))))
      ≤ ∫ t in Icc (φ - π) (φ + π), ∑ j ∈ Finset.range (N + 1), 64 * π * D / (4 ^ j * ℓ * D ^ j) *
          (Icc (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2)).indicator (fun t => w t + τ) t := by
        refine setIntegral_mono_on hLHS (integrable_finsetSum _ hint) measurableSet_Icc
          fun t ht => ?_
        have hts : |t - φ| ≤ π := by
          rw [abs_le]
          constructor <;> linarith [ht.1, ht.2]
        have h := s07d_p4_core_ptw5 hD hr0 hr1 hℓ hrℓ hN1 hts
        have hy : 0 ≤ w t + τ := by linarith [hw0 t]
        calc (w t + τ) * ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) /
              Real.exp (Real.log D / Real.log 2 * Real.log (max 1 (2 * |t - φ| / ℓ))))
            ≤ (w t + τ) * ∑ j ∈ Finset.range (N + 1), 64 * π * D / (4 ^ j * ℓ * D ^ j) *
                (Icc (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2)).indicator 1 t :=
              mul_le_mul_of_nonneg_left h hy
          _ = _ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              by_cases hm : t ∈ Icc (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2)
              · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, Pi.one_apply]
                ring
              · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]
                ring
    _ = ∑ j ∈ Finset.range (N + 1), 64 * π * D / (4 ^ j * ℓ * D ^ j) *
          ∫ t in Icc (φ - π) (φ + π),
            (Icc (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2)).indicator (fun t => w t + τ) t := by
        rw [integral_finsetSum _ hint]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact integral_const_mul _ _
    _ ≤ ∑ j ∈ Finset.range (N + 1), 64 * π * D / (4 ^ j * ℓ * D ^ j) *
          (D ^ j * V + τ * (2 ^ j * ℓ)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hjN : j ≤ N := by
          rw [Finset.mem_range] at hj
          omega
        have hp : 0 ≤ 2 ^ j * ℓ / 2 := by positivity
        have hle : (φ - 2 ^ j * ℓ / 2) ≤ (φ + 2 ^ j * ℓ / 2) := by linarith
        have hj4 : 2 ^ j * ℓ ≤ 4 * π := by
          have : (2 : ℝ) ^ j ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hjN
          nlinarith
        have hwj := s07d_p4_core_wint hwm hw0 (hwν _ measurableSet_Icc)
          (hfin (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2))
        have hcj : IntegrableOn (fun _ : ℝ => τ) (Icc (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2))
            volume := integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        have hdj := s07d_p4_core_dbl_iter hD hdbl φ hℓ j hj4
        have hνj : (ν (Icc (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2))).toReal ≤ D ^ j * V := by
          have h1 := ENNReal.toReal_mono
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin _ _)) hdj
          rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h1
        calc ∫ t in Icc (φ - π) (φ + π),
              (Icc (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2)).indicator (fun t => w t + τ) t
            ≤ ∫ t in Icc (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2), (w t + τ) :=
              s07d_p4_core_setind measurableSet_Icc (hwj.1.add hcj)
                (fun t _ => by linarith [hw0 t])
          _ = (∫ t in Icc (φ - 2 ^ j * ℓ / 2) (φ + 2 ^ j * ℓ / 2), w t) + τ * (2 ^ j * ℓ) := by
              rw [integral_add hwj.1 hcj, setIntegral_const, smul_eq_mul, measureReal_def,
                Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
              ring
          _ ≤ D ^ j * V + τ * (2 ^ j * ℓ) := by linarith [hwj.2]
    _ ≤ ∑ j ∈ Finset.range (N + 1), (64 * π * D * Λ * (1 / 4 : ℝ) ^ j +
          64 * π * D * τ * (1 / 2 : ℝ) ^ j) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h4 : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by
          rw [← mul_pow]
          norm_num
        have hDj : 1 ≤ D ^ j := one_le_pow₀ hD
        have hDj0 : 0 < D ^ j := by positivity
        have e1 : 64 * π * D / (4 ^ j * ℓ * D ^ j) * (D ^ j * V) = 64 * π * D * Λ * (1 / 4 : ℝ) ^ j := by
          rw [hΛ, one_div_pow]
          field_simp
        have e2 : 64 * π * D / (4 ^ j * ℓ * D ^ j) * (τ * (2 ^ j * ℓ)) =
            64 * π * D * τ * (1 / 2 : ℝ) ^ j / D ^ j := by
          rw [h4, one_div_pow]
          field_simp
        have e3 : 64 * π * D * τ * (1 / 2 : ℝ) ^ j / D ^ j ≤ 64 * π * D * τ * (1 / 2 : ℝ) ^ j :=
          div_le_self (by positivity) hDj
        rw [mul_add, e1, e2]
        linarith
    _ = 64 * π * D * Λ * ∑ j ∈ Finset.range (N + 1), (1 / 4 : ℝ) ^ j +
          64 * π * D * τ * ∑ j ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ j := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 64 * π * D * Λ * (4 / 3) + 64 * π * D * τ * 2 := by
        obtain ⟨g2, g4⟩ := s07d_p4_core_geom (N + 1)
        have h1 : 0 ≤ 64 * π * D * Λ := by positivity
        have h2 : 0 ≤ 64 * π * D * τ := by positivity
        exact add_le_add (mul_le_mul_of_nonneg_left g4 h1) (mul_le_mul_of_nonneg_left g2 h2)
    _ ≤ 128 * π * D * Λ := by
        have hτ' : τ ≤ Λ / 4 := by rw [hΛ]; exact hτ
        have h3 : 0 ≤ π * D := by positivity
        nlinarith

/-- P4.5 helper (w4): `|log y| ≤ |log τ| + y` for `y ≥ τ > 0`. -/
theorem s07d_p4_core_abs_log {y τ : ℝ} (hτ : 0 < τ) (hy : τ ≤ y) :
    |Real.log y| ≤ |Real.log τ| + y := by
  have hy0 : 0 < y := lt_of_lt_of_le hτ hy
  have h1 : Real.log τ ≤ Real.log y := Real.log_le_log hτ hy
  have h2 : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy0
  rw [abs_le]
  constructor
  · have := neg_abs_le (Real.log τ)
    linarith
  · have := abs_nonneg (Real.log τ)
    linarith

/-- P4.5 helper (w4): the pointwise tangent bound of the splitting argument, with weight
`T = Λ (4η)^{[t ∈ B]} e^{γ L}`; `iK`, `iW` are the values of the `B`-indicators of `K`, `yK`. -/
theorem s07d_p4_core_ptwab {K L γ Λ η y iK iW : ℝ} (hK0 : 0 ≤ K) (hL0 : 0 ≤ L) (hγ0 : 0 ≤ γ)
    (hΛ0 : 0 < Λ) (hη0 : 0 < η) (hy : 0 < y)
    (hcase : (iK = K ∧ iW = y * K) ∨ (iK = 0 ∧ iW = 0)) :
    Real.log y * K ≤ Real.log Λ * K + Real.log (4 * η) * iK + γ * (K * L) +
      1 / (4 * η * Λ) * iW + 1 / Λ * (y * (K / Real.exp (γ * L))) - K := by
  have hκ1 : 1 ≤ Real.exp (γ * L) := Real.one_le_exp (mul_nonneg hγ0 hL0)
  have hκ0 : 0 < Real.exp (γ * L) := Real.exp_pos _
  have hextra : 0 ≤ 1 / Λ * (y * (K / Real.exp (γ * L))) := by positivity
  have hc : Real.log y * K = K * Real.log y := mul_comm _ _
  rcases hcase with h | h
  · obtain ⟨h1, h2⟩ := h
    rw [h1, h2]
    have hT : 0 < Λ * (4 * η) * Real.exp (γ * L) := by positivity
    have htan := s07d_p4_core_tangent hy hT
    have hlogT : Real.log (Λ * (4 * η) * Real.exp (γ * L)) =
        Real.log Λ + Real.log (4 * η) + γ * L := by
      rw [Real.log_mul (by positivity) hκ0.ne', Real.log_mul hΛ0.ne' (by positivity),
        Real.log_exp]
    rw [hlogT] at htan
    have hdiv : y / (Λ * (4 * η) * Real.exp (γ * L)) ≤ y / (4 * η * Λ) := by
      apply div_le_div_of_nonneg_left hy.le (by positivity)
      nlinarith [mul_pos hΛ0 hη0]
    have hm1 := mul_le_mul_of_nonneg_left htan hK0
    have hm2 := mul_le_mul_of_nonneg_left hdiv hK0
    have e : K * (y / (4 * η * Λ)) = 1 / (4 * η * Λ) * (y * K) := by ring
    have hexp : K * (Real.log Λ + Real.log (4 * η) + γ * L +
        y / (Λ * (4 * η) * Real.exp (γ * L)) - 1) =
        Real.log Λ * K + Real.log (4 * η) * K + γ * (K * L) +
          K * (y / (Λ * (4 * η) * Real.exp (γ * L))) - K := by ring
    linarith
  · obtain ⟨h1, h2⟩ := h
    rw [h1, h2, mul_zero, mul_zero]
    have hT : 0 < Λ * Real.exp (γ * L) := by positivity
    have htan := s07d_p4_core_tangent hy hT
    have hlogT : Real.log (Λ * Real.exp (γ * L)) = Real.log Λ + γ * L := by
      rw [Real.log_mul hΛ0.ne' hκ0.ne', Real.log_exp]
    rw [hlogT] at htan
    have hm1 := mul_le_mul_of_nonneg_left htan hK0
    have e : K * (y / (Λ * Real.exp (γ * L))) = 1 / Λ * (y * (K / Real.exp (γ * L))) := by
      field_simp
    have hexp : K * (Real.log Λ + γ * L + y / (Λ * Real.exp (γ * L)) - 1) =
        Real.log Λ * K + γ * (K * L) + K * (y / (Λ * Real.exp (γ * L))) - K := by ring
    linarith

/-- P4.5 helper (w4): `2π`-normalised Poisson mass of `B ⊆ J` is `≥ 1/(2(1 + π²))` when
`|B| ≥ |J|/2`. -/
theorem s07d_p4_core_X2 {r φ ℓ : ℝ} {B : Set ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hℓ : 0 < ℓ)
    (hrℓ : 1 - r = ℓ / (2 * π)) (hBm : MeasurableSet B)
    (hBJ : B ⊆ Icc (φ - ℓ / 2) (φ + ℓ / 2)) (hBW : B ⊆ Icc (φ - π) (φ + π))
    (hvolBge : ℓ / 2 ≤ (volume B).toReal) :
    π / (1 + π ^ 2) ≤ ∫ t in Icc (φ - π) (φ + π),
      B.indicator (fun t => (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2)) t := by
  have hpi := Real.pi_pos
  have hvolB : volume B ≠ ⊤ := by
    intro h
    rw [h, ENNReal.toReal_top] at hvolBge
    linarith
  have hKc : Continuous fun t : ℝ => (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) :=
    continuous_const.div (by fun_prop) fun t => (s07d_p4_core_den_pos hr0 hr1 _).ne'
  rw [setIntegral_indicator hBm, inter_eq_right.2 hBW]
  have hc : IntegrableOn (fun _ : ℝ => 2 * π / ((1 + π ^ 2) * ℓ)) B volume :=
    integrableOn_const hvolB
  have hlow : ∀ t ∈ B, 2 * π / ((1 + π ^ 2) * ℓ) ≤
      (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) := fun t ht => by
    have htJ := hBJ ht
    have hts : |t - φ| ≤ π * (1 - r) := by
      rw [hrℓ, abs_le]
      have e : π * (ℓ / (2 * π)) = ℓ / 2 := by field_simp
      rw [e]
      constructor <;> linarith [htJ.1, htJ.2]
    have h := s07d_p4_core_k_low hr0 hr1 hts
    have e : 1 / ((1 + π ^ 2) * (1 - r)) = 2 * π / ((1 + π ^ 2) * ℓ) := by
      rw [hrℓ]
      field_simp
    linarith
  have h := setIntegral_mono_on hc (hKc.integrableOn_Icc.mono_set hBW) hBm hlow
  rw [setIntegral_const, smul_eq_mul, measureReal_def] at h
  have e : ℓ / 2 * (2 * π / ((1 + π ^ 2) * ℓ)) = π / (1 + π ^ 2) := by field_simp
  have h2 : ℓ / 2 * (2 * π / ((1 + π ^ 2) * ℓ)) ≤ (volume B).toReal * (2 * π / ((1 + π ^ 2) * ℓ)) :=
    mul_le_mul_of_nonneg_right hvolBge (by positivity)
  linarith

/-- P4.5 helper (w4): `∫_W 1_B (w + τ) P_r ≤ 8 π η Λ` when `ν(B) ≤ η Λ ℓ`, `|B| ≤ ℓ`, `τ = ηΛ`. -/
theorem s07d_p4_core_X4 {ν : Measure ℝ} {w : ℝ → ℝ} {r φ ℓ τ η Λ : ℝ} {B : Set ℝ}
    (hwm : Measurable w) (hw0 : ∀ t, 0 ≤ w t)
    (hwν : ∀ E : Set ℝ, MeasurableSet E → ∫⁻ t in E, ENNReal.ofReal (w t) ≤ ν E)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hℓ : 0 < ℓ) (hrℓ : 1 - r = ℓ / (2 * π))
    (hWfin : ν (Icc (φ - π) (φ + π)) ≠ ⊤)
    (hBm : MeasurableSet B) (hBW : B ⊆ Icc (φ - π) (φ + π)) (hνBfin : ν B ≠ ⊤)
    (hvolB : volume B ≠ ⊤) (hvolBle : (volume B).toReal ≤ ℓ) (hτ0 : 0 ≤ τ)
    (hτ : τ = η * Λ) (hνB : (ν B).toReal ≤ η * Λ * ℓ) :
    ∫ t in Icc (φ - π) (φ + π),
      B.indicator (fun t => (w t + τ) * ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2))) t ≤
      8 * π * η * Λ := by
  have hpi := Real.pi_pos
  have hKc : Continuous fun t : ℝ => (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) :=
    continuous_const.div (by fun_prop) fun t => (s07d_p4_core_den_pos hr0 hr1 _).ne'
  have hwW := s07d_p4_core_wint hwm hw0 (hwν _ measurableSet_Icc) hWfin
  have hwτW : IntegrableOn (fun t => w t + τ) (Icc (φ - π) (φ + π)) volume :=
    hwW.1.add (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have iwK : IntegrableOn (fun t => (w t + τ) *
      ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2))) (Icc (φ - π) (φ + π)) volume :=
    hwτW.mul_continuousOn hKc.continuousOn isCompact_Icc
  have hwB := s07d_p4_core_wint hwm hw0 (hwν _ hBm) hνBfin
  have hcB : IntegrableOn (fun _ : ℝ => τ) B volume := integrableOn_const hvolB
  have h4 : ∫ t in B, (w t + τ) * (4 * π / ℓ) =
      ((∫ t in B, w t) + τ * (volume B).toReal) * (4 * π / ℓ) := by
    rw [integral_mul_const, integral_add hwB.1 hcB, setIntegral_const, smul_eq_mul,
      measureReal_def]
    ring
  have h5 : ((∫ t in B, w t) + τ * (volume B).toReal) ≤ η * Λ * ℓ + η * Λ * ℓ := by
    have h1 : (∫ t in B, w t) ≤ η * Λ * ℓ := le_trans hwB.2 hνB
    have h2 : τ * (volume B).toReal ≤ τ * ℓ := mul_le_mul_of_nonneg_left hvolBle hτ0
    have h3 : τ * ℓ = η * Λ * ℓ := by rw [hτ]
    linarith
  calc ∫ t in Icc (φ - π) (φ + π),
        B.indicator (fun t => (w t + τ) * ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2))) t
      ≤ ∫ t in B, (w t + τ) * ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2)) :=
        s07d_p4_core_setind hBm (iwK.mono_set hBW) (fun t _ =>
          mul_nonneg (by linarith [hw0 t]) (s07d_p4_core_k_nonneg hr0 hr1 _))
    _ ≤ ∫ t in B, (w t + τ) * (4 * π / ℓ) := by
        refine setIntegral_mono_on (iwK.mono_set hBW) ((hwB.1.add hcB).mul_const _) hBm
          fun t _ => ?_
        have hKle := s07d_p4_core_k_le hr0 hr1 (t - φ)
        rw [hrℓ] at hKle
        have e : 2 / (ℓ / (2 * π)) = 4 * π / ℓ := by field_simp; ring
        rw [e] at hKle
        exact mul_le_mul_of_nonneg_left hKle (by linarith [hw0 t])
    _ ≤ (η * Λ * ℓ + η * Λ * ℓ) * (4 * π / ℓ) := by
        rw [h4]
        exact mul_le_mul_of_nonneg_right h5 (div_nonneg (by positivity) hℓ.le)
    _ = 8 * π * η * Λ := by
        field_simp
        ring

/-- P4.5 helper (w4): `log(w + τ) P_r` is integrable on `W` (`τ > 0`, `w ≥ 0` integrable). -/
theorem s07d_p4_core_iL {w : ℝ → ℝ} {r φ τ : ℝ} (hwm : Measurable w) (hw0 : ∀ t, 0 ≤ w t)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hτ0 : 0 < τ) {W : Set ℝ} (hW : volume W ≠ ⊤)
    (hwW : IntegrableOn w W volume) :
    IntegrableOn (fun t => Real.log (w t + τ) *
      ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2))) W volume := by
  have hKc : Continuous fun t : ℝ => (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) :=
    continuous_const.div (by fun_prop) fun t => (s07d_p4_core_den_pos hr0 hr1 _).ne'
  have hbd : IntegrableOn (fun t => (|Real.log τ| + (w t + τ)) * (2 / (1 - r))) W volume :=
    ((integrableOn_const hW).add (hwW.add (integrableOn_const hW))).mul_const _
  refine hbd.mono' ?_ ?_
  · exact ((Real.measurable_log.comp (hwm.add_const τ)).mul hKc.measurable).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t => ?_
    have hK0 := s07d_p4_core_k_nonneg hr0 hr1 (t - φ)
    have hKle := s07d_p4_core_k_le hr0 hr1 (t - φ)
    have hlog := s07d_p4_core_abs_log hτ0 (by linarith [hw0 t] : τ ≤ w t + τ)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hK0]
    exact mul_le_mul hlog hKle hK0 (by linarith [abs_nonneg (Real.log τ), hw0 t])

/-- P4.5 helper (w4): integrate a pointwise bound `g ≤ Σ cᵢ kᵢ - k₁` over `W`. -/
theorem s07d_p4_core_sum5 {W : Set ℝ} {g k1 k2 k3 k4 k5 : ℝ → ℝ} {c1 c2 c3 c4 c5 : ℝ}
    (hg : IntegrableOn g W volume) (j1 : IntegrableOn k1 W volume)
    (j2 : IntegrableOn k2 W volume) (j3 : IntegrableOn k3 W volume)
    (j4 : IntegrableOn k4 W volume) (j5 : IntegrableOn k5 W volume)
    (h : ∀ t ∈ W, g t ≤ c1 * k1 t + c2 * k2 t + c3 * k3 t + c4 * k4 t + c5 * k5 t - k1 t)
    (hW : MeasurableSet W) :
    ∫ t in W, g t ≤ c1 * (∫ t in W, k1 t) + c2 * (∫ t in W, k2 t) + c3 * (∫ t in W, k3 t) +
      c4 * (∫ t in W, k4 t) + c5 * (∫ t in W, k5 t) - ∫ t in W, k1 t := by
  have a1 : IntegrableOn (fun t => c1 * k1 t) W volume := j1.const_mul c1
  have b2 : IntegrableOn (fun t => c2 * k2 t) W volume := j2.const_mul c2
  have b3 : IntegrableOn (fun t => c3 * k3 t) W volume := j3.const_mul c3
  have b4 : IntegrableOn (fun t => c4 * k4 t) W volume := j4.const_mul c4
  have b5 : IntegrableOn (fun t => c5 * k5 t) W volume := j5.const_mul c5
  have a2 : IntegrableOn (fun t => c1 * k1 t + c2 * k2 t) W volume := a1.add b2
  have a3 : IntegrableOn (fun t => c1 * k1 t + c2 * k2 t + c3 * k3 t) W volume := a2.add b3
  have a4 : IntegrableOn (fun t => c1 * k1 t + c2 * k2 t + c3 * k3 t + c4 * k4 t) W volume :=
    a3.add b4
  have a5 : IntegrableOn (fun t => c1 * k1 t + c2 * k2 t + c3 * k3 t + c4 * k4 t + c5 * k5 t)
      W volume := a4.add b5
  have a6 : IntegrableOn (fun t => c1 * k1 t + c2 * k2 t + c3 * k3 t + c4 * k4 t + c5 * k5 t -
      k1 t) W volume := a5.sub j1
  have hm := setIntegral_mono_on hg a6 hW h
  rw [integral_sub a5 j1, integral_add a4 b5, integral_add a3 b4, integral_add a2 b3,
    integral_add a1 b2, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul] at hm
  exact hm

/-- P4.5 helper (w4): the arithmetic assembly of the five Poisson-integral pieces. -/
theorem s07d_p4_core_asm {I X1 X2 X3 X4 X5 Λ η D : ℝ} (hΛ0 : 0 < Λ) (hη0 : 0 < η)
    (hη : η ≤ 1 / 4) (hD : 1 ≤ D)
    (hmono : I ≤ Real.log Λ * X1 + Real.log (4 * η) * X2 + Real.log D / Real.log 2 * X3 +
      1 / (4 * η * Λ) * X4 + 1 / Λ * X5 - X1)
    (hX1 : X1 = 2 * π) (hX2 : π / (1 + π ^ 2) ≤ X2) (hX3 : X3 ≤ 128 * π * Real.log 2)
    (hX4 : X4 ≤ 8 * π * η * Λ) (hX5 : X5 ≤ 128 * π * D * Λ) :
    (1 / (2 * π)) * I ≤
      Real.log Λ + Real.log (4 * η) / (2 * (1 + π ^ 2)) + 64 * Real.log D + 64 * D := by
  have hpi := Real.pi_pos
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hγ0 : 0 ≤ Real.log D / Real.log 2 := div_nonneg hlD hl2.le
  have hl4 : Real.log (4 * η) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  have t2 : Real.log (4 * η) * X2 ≤ Real.log (4 * η) * (π / (1 + π ^ 2)) :=
    mul_le_mul_of_nonpos_left hX2 hl4
  have t3 : Real.log D / Real.log 2 * X3 ≤ Real.log D / Real.log 2 * (128 * π * Real.log 2) :=
    mul_le_mul_of_nonneg_left hX3 hγ0
  have t4 : 1 / (4 * η * Λ) * X4 ≤ 2 * π := by
    calc _ ≤ 1 / (4 * η * Λ) * (8 * π * η * Λ) :=
          mul_le_mul_of_nonneg_left hX4 (by positivity)
      _ = 2 * π := by field_simp; ring
  have t5 : 1 / Λ * X5 ≤ 128 * π * D := by
    calc _ ≤ 1 / Λ * (128 * π * D * Λ) := mul_le_mul_of_nonneg_left hX5 (by positivity)
      _ = 128 * π * D := by field_simp
  have t3' : Real.log D / Real.log 2 * (128 * π * Real.log 2) = 128 * π * Real.log D := by
    field_simp
  rw [hX1] at hmono
  have hS : I ≤ Real.log Λ * (2 * π) + Real.log (4 * η) * (π / (1 + π ^ 2)) +
      128 * π * Real.log D + 2 * π + 128 * π * D - 2 * π := by linarith
  have hfin2 : (1 / (2 * π)) * (Real.log Λ * (2 * π) + Real.log (4 * η) * (π / (1 + π ^ 2)) +
      128 * π * Real.log D + 2 * π + 128 * π * D - 2 * π) =
      Real.log Λ + Real.log (4 * η) / (2 * (1 + π ^ 2)) + 64 * Real.log D + 64 * D := by
    field_simp
    ring
  rw [← hfin2]
  exact mul_le_mul_of_nonneg_left hS (by positivity)

/-- P4.5 helper (w4): the Poisson average of `log(w + ηΛ)` at the top point of `J` is
`≤ log Λ + log(4η)/(2(1+π²)) + 64 log D + 64 D` when `ν(B) ≤ η ν(J)` on a half of `J`. -/
theorem s07d_p4_core_int {ν : Measure ℝ} {w : ℝ → ℝ} {D η r φ ℓ Λ τ : ℝ} {B : Set ℝ}
    (hD : 1 ≤ D) (hη0 : 0 < η) (hη : η ≤ 1 / 4)
    (hfin : ∀ a b : ℝ, ν (Icc a b) ≠ ⊤)
    (hdbl : ∀ a b : ℝ, a < b → b - a ≤ 2 * π →
      ν (Icc (a - (b - a) / 2) (b + (b - a) / 2)) ≤ ENNReal.ofReal D * ν (Icc a b))
    (hwm : Measurable w) (hw0 : ∀ t, 0 ≤ w t)
    (hwν : ∀ E : Set ℝ, MeasurableSet E → ∫⁻ t in E, ENNReal.ofReal (w t) ≤ ν E)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hℓ : 0 < ℓ) (hlen : ℓ ≤ 2 * π) (hrℓ : 1 - r = ℓ / (2 * π))
    (hΛ : Λ = (ν (Icc (φ - ℓ / 2) (φ + ℓ / 2))).toReal / ℓ) (hΛ0 : 0 < Λ) (hτ : τ = η * Λ)
    (hBm : MeasurableSet B) (hBJ : B ⊆ Icc (φ - ℓ / 2) (φ + ℓ / 2))
    (hvolBge : ℓ / 2 ≤ (volume B).toReal) (hνB : (ν B).toReal ≤ η * Λ * ℓ) :
    (1 / (2 * π)) * ∫ t in (φ - π)..(φ + π),
      Real.log (w t + τ) * ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2)) ≤
      Real.log Λ + Real.log (4 * η) / (2 * (1 + π ^ 2)) + 64 * Real.log D + 64 * D := by
  have hpi := Real.pi_pos
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hγ0 : 0 ≤ Real.log D / Real.log 2 := div_nonneg hlD hl2.le
  have hτ0 : 0 < τ := by rw [hτ]; exact mul_pos hη0 hΛ0
  have hτΛ : τ ≤ (ν (Icc (φ - ℓ / 2) (φ + ℓ / 2))).toReal / ℓ / 4 := by
    rw [← hΛ, hτ]
    nlinarith
  obtain ⟨N, hN1, hN2⟩ := s07d_p4_core_N hℓ hlen
  have hJW : Icc (φ - ℓ / 2) (φ + ℓ / 2) ⊆ Icc (φ - π) (φ + π) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hBW : B ⊆ Icc (φ - π) (φ + π) := hBJ.trans hJW
  have hvolJ : volume (Icc (φ - ℓ / 2) (φ + ℓ / 2)) = ENNReal.ofReal ℓ := by
    rw [Real.volume_Icc]
    congr 1
    ring
  have hvolB : volume B ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hvolJ]; exact ENNReal.ofReal_ne_top) (measure_mono hBJ)
  have hvolBle : (volume B).toReal ≤ ℓ := by
    have h := ENNReal.toReal_mono (by rw [hvolJ]; exact ENNReal.ofReal_ne_top) (measure_mono hBJ)
    rwa [hvolJ, ENNReal.toReal_ofReal hℓ.le] at h
  have hνBfin : ν B ≠ ⊤ := ne_top_of_le_ne_top (hfin _ _) (measure_mono hBJ)
  have hWfin := hfin (φ - π) (φ + π)
  have hWvol : volume (Icc (φ - π) (φ + π)) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hKc : Continuous fun t : ℝ => (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) :=
    continuous_const.div (by fun_prop) fun t => (s07d_p4_core_den_pos hr0 hr1 _).ne'
  have hLc : Continuous fun t : ℝ => Real.log (max 1 (2 * |t - φ| / ℓ)) := by
    refine Continuous.log ?_ fun t => (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
    exact continuous_const.max
      ((continuous_const.mul (continuous_abs.comp (continuous_id.sub continuous_const))).div_const ℓ)
  have hκc : Continuous fun t : ℝ =>
      Real.exp (Real.log D / Real.log 2 * Real.log (max 1 (2 * |t - φ| / ℓ))) :=
    Real.continuous_exp.comp (continuous_const.mul hLc)
  have hqc : Continuous fun t : ℝ => (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) /
      Real.exp (Real.log D / Real.log 2 * Real.log (max 1 (2 * |t - φ| / ℓ))) :=
    hKc.div hκc fun t => (Real.exp_pos _).ne'
  have hwW := s07d_p4_core_wint hwm hw0 (hwν _ measurableSet_Icc) hWfin
  have hwτW : IntegrableOn (fun t => w t + τ) (Icc (φ - π) (φ + π)) volume :=
    hwW.1.add (integrableOn_const hWvol)
  have iK : IntegrableOn (fun t : ℝ => (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2))
      (Icc (φ - π) (φ + π)) volume := hKc.integrableOn_Icc
  have iwK : IntegrableOn (fun t => (w t + τ) *
      ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2))) (Icc (φ - π) (φ + π)) volume :=
    hwτW.mul_continuousOn hKc.continuousOn isCompact_Icc
  have iwq : IntegrableOn (fun t => (w t + τ) *
      ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) /
        Real.exp (Real.log D / Real.log 2 * Real.log (max 1 (2 * |t - φ| / ℓ)))))
      (Icc (φ - π) (φ + π)) volume :=
    hwτW.mul_continuousOn hqc.continuousOn isCompact_Icc
  have i3 : IntegrableOn (fun t => (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) *
      Real.log (max 1 (2 * |t - φ| / ℓ))) (Icc (φ - π) (φ + π)) volume :=
    (hKc.mul hLc).integrableOn_Icc
  have iL := s07d_p4_core_iL (φ := φ) hwm hw0 hr0 hr1 hτ0 hWvol hwW.1
  have hcase : ∀ t, (B.indicator (fun t => (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2)) t =
        (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) ∧
      B.indicator (fun t => (w t + τ) * ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2))) t =
        (w t + τ) * ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2))) ∨
      (B.indicator (fun t => (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2)) t = 0 ∧
      B.indicator (fun t => (w t + τ) * ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2))) t =
        0) := by
    intro t
    by_cases htB : t ∈ B
    · left
      exact ⟨Set.indicator_of_mem htB _, Set.indicator_of_mem htB _⟩
    · right
      exact ⟨Set.indicator_of_notMem htB _, Set.indicator_of_notMem htB _⟩
  have hmono := s07d_p4_core_sum5 (W := Icc (φ - π) (φ + π))
    (g := fun t => Real.log (w t + τ) * ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2)))
    (k1 := fun t => (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2))
    (k2 := B.indicator (fun t => (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2)))
    (k3 := fun t => (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) *
      Real.log (max 1 (2 * |t - φ| / ℓ)))
    (k4 := B.indicator (fun t => (w t + τ) *
      ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2))))
    (k5 := fun t => (w t + τ) * ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) /
      Real.exp (Real.log D / Real.log 2 * Real.log (max 1 (2 * |t - φ| / ℓ)))))
    (c1 := Real.log Λ) (c2 := Real.log (4 * η)) (c3 := Real.log D / Real.log 2)
    (c4 := 1 / (4 * η * Λ)) (c5 := 1 / Λ)
    iL iK (iK.indicator hBm) i3 (iwK.indicator hBm) iwq
    (fun t _ => s07d_p4_core_ptwab (s07d_p4_core_k_nonneg hr0 hr1 (t - φ))
      (Real.log_nonneg (le_max_left _ _)) hγ0 hΛ0 hη0 (by linarith [hw0 t]) (hcase t))
    measurableSet_Icc
  beta_reduce at hmono
  have hconv : ∀ f : ℝ → ℝ, ∫ t in (φ - π)..(φ + π), f t = ∫ t in Icc (φ - π) (φ + π), f t :=
    fun f => by rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
  have hX1 : ∫ t in Icc (φ - π) (φ + π), (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) =
      2 * π := by
    have h := s07d_p4_core_mass hr0 hr1 φ
    rw [hconv] at h
    field_simp at h
    linarith
  have hX2 := s07d_p4_core_X2 hr0 hr1 hℓ hrℓ hBm hBJ hBW hvolBge
  have hX3 := s07d_p4_core_T3 (φ := φ) hr0 hr1 hℓ hrℓ hN1
  have hX4 := s07d_p4_core_X4 hwm hw0 hwν hr0 hr1 hℓ hrℓ hWfin hBm hBW hνBfin hvolB hvolBle
    hτ0.le hτ hνB
  have hX5 := s07d_p4_core_T5 (ν := ν) (w := w) (D := D) (r := r) (φ := φ) (ℓ := ℓ) (τ := τ)
    hD hfin hdbl hwm hw0 hwν hr0 hr1 hℓ hrℓ hN1 hN2 hτ0.le hτΛ
  rw [← hΛ] at hX5
  rw [hconv]
  exact s07d_p4_core_asm hΛ0 hη0 hη hD hmono hX1 hX2 hX3 hX4 hX5

/-- **P4.5** (`core`, the real-variable heart): let `ν` be a locally finite doubling measure on
`ℝ` with density part `w` (`∫_E w ≤ ν(E)`), and `u(r, φ)` a function satisfying the Jensen bound
`u ≤ C₀ + P_r[log(w + τ)]` (all `τ > 0`) and the upper comparison
`ν(J) ≤ C₁ |J| e^{u(z_J)}` on arcs.  Then `ν` is weakly `A∞` on intervals of length `≤ 2π`,
with `δ₀, η₀` depending only on `C₀, C₁, D`. -/
theorem s07d_p4_core {C₀ C₁ D : ℝ} (hC₁ : 0 < C₁) (hD : 1 ≤ D) :
    ∃ δ₀ η₀ : ℝ, 0 < δ₀ ∧ 0 < η₀ ∧ η₀ < 1 ∧
    ∀ (ν : Measure ℝ) (w : ℝ → ℝ) (u : ℝ → ℝ → ℝ),
      (∀ a b : ℝ, ν (Icc a b) ≠ ⊤) →
      (∀ a b : ℝ, a < b → b - a ≤ 2 * π →
        ν (Icc (a - (b - a) / 2) (b + (b - a) / 2)) ≤ ENNReal.ofReal D * ν (Icc a b)) →
      Measurable w → (∀ t, 0 ≤ w t) →
      (∀ E : Set ℝ, MeasurableSet E → ∫⁻ t in E, ENNReal.ofReal (w t) ≤ ν E) →
      (∀ r φ τ : ℝ, 0 ≤ r → r < 1 → 0 < τ →
        u r φ ≤ C₀ + (1 / (2 * π)) * ∫ t in (φ - π)..(φ + π),
          Real.log (w t + τ) * ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2))) →
      (∀ a b : ℝ, a < b → b - a ≤ 2 * π →
        ν (Icc a b) ≤
          ENNReal.ofReal (C₁ * (b - a) * Real.exp (u (1 - (b - a) / (2 * π)) ((a + b) / 2)))) →
      ∀ a b : ℝ, a < b → b - a ≤ 2 * π → ∀ E ⊆ Icc a b, MeasurableSet E →
        volume E ≤ ENNReal.ofReal (δ₀ * (b - a)) →
        ν E ≤ ENNReal.ofReal (1 - η₀) * ν (Icc a b) := by
  have hpi := Real.pi_pos
  set m : ℝ := 2 * (1 + π ^ 2) with hm
  have hm0 : 0 < m := by positivity
  set A : ℝ := C₀ + Real.log C₁ + 64 * Real.log D + 64 * D with hA
  set η : ℝ := Real.exp (-(m * (|A| + 1))) / 4 with hη
  have hη0 : 0 < η := by positivity
  have hη4 : η ≤ 1 / 4 := by
    have : Real.exp (-(m * (|A| + 1))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by have := abs_nonneg A; nlinarith)
    rw [hη]
    linarith
  have hl4 : Real.log (4 * η) = -(m * (|A| + 1)) := by
    rw [hη, show 4 * (Real.exp (-(m * (|A| + 1))) / 4) = Real.exp (-(m * (|A| + 1))) by ring,
      Real.log_exp]
  refine ⟨1 / 2, η, by norm_num, hη0, by linarith, ?_⟩
  intro ν w u hfin hdbl hwm hw0 hwν hH1 hH2 a b hab hlen E hEJ hEm hEvol
  by_contra hcon
  have hEJν : ν E ≤ ν (Icc a b) := measure_mono hEJ
  set V := (ν (Icc a b)).toReal with hV
  have hV0 : 0 < V := by
    rcases (ENNReal.toReal_nonneg : 0 ≤ V).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : ν (Icc a b) = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).1 h.symm with h1 | h1
        · exact h1
        · exact absurd h1 (hfin a b)
      apply hcon
      rw [h0, mul_zero]
      exact le_of_le_of_eq hEJν h0
  set B := Icc a b \ E with hBdef
  have hBm : MeasurableSet B := measurableSet_Icc.diff hEm
  have hBJ : B ⊆ Icc a b := sdiff_subset
  have hsplit : ν E + ν B = ν (Icc a b) := by
    rw [hBdef, measure_add_sdiff hEm.nullMeasurableSet, union_eq_right.2 hEJ]
  have hEfin : ν E ≠ ⊤ := ne_top_of_le_ne_top (hfin a b) hEJν
  have hBfin : ν B ≠ ⊤ := ne_top_of_le_ne_top (hfin a b) (measure_mono hBJ)
  have hsplitR : (ν E).toReal + (ν B).toReal = V := by
    rw [hV, ← hsplit, ENNReal.toReal_add hEfin hBfin]
  have hcon' : (1 - η) * V < (ν E).toReal := by
    have h := lt_of_not_ge hcon
    have h2 := (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin a b))
      hEfin).2 h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at h2
  have hνB : (ν B).toReal ≤ η * V := by linarith
  have hBvol : ENNReal.ofReal ((b - a) / 2) ≤ volume B := by
    have hs : volume E + volume B = volume (Icc a b) := by
      rw [hBdef, measure_add_sdiff hEm.nullMeasurableSet, union_eq_right.2 hEJ]
    rw [Real.volume_Icc] at hs
    have hEf : volume E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hEvol
    have hBf : volume B ≠ ⊤ := by
      intro h
      rw [h, add_top] at hs
      exact ENNReal.ofReal_ne_top hs.symm
    have hsR := congrArg ENNReal.toReal hs
    rw [ENNReal.toReal_add hEf hBf, ENNReal.toReal_ofReal (by linarith)] at hsR
    have hER := ENNReal.toReal_mono ENNReal.ofReal_ne_top hEvol
    rw [ENNReal.toReal_ofReal (by linarith)] at hER
    rw [ENNReal.ofReal_le_iff_le_toReal hBf]
    linarith
  have hℓ : 0 < b - a := by linarith
  have hr0 : 0 ≤ 1 - (b - a) / (2 * π) := by
    have : (b - a) / (2 * π) ≤ 1 := by rw [div_le_one (by positivity)]; exact hlen
    linarith
  have hr1 : 1 - (b - a) / (2 * π) < 1 := by
    have : 0 < (b - a) / (2 * π) := by positivity
    linarith
  have hJeq : Icc ((a + b) / 2 - (b - a) / 2) ((a + b) / 2 + (b - a) / 2) = Icc a b := by
    congr 1 <;> ring
  have hΛeq : V / (b - a) =
      (ν (Icc ((a + b) / 2 - (b - a) / 2) ((a + b) / 2 + (b - a) / 2))).toReal / (b - a) := by
    rw [hJeq]
  have hBJ' : B ⊆ Icc ((a + b) / 2 - (b - a) / 2) ((a + b) / 2 + (b - a) / 2) := by
    rw [hJeq]
    exact hBJ
  have hvolBge : (b - a) / 2 ≤ (volume B).toReal := by
    have hBf : volume B ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (measure_mono hBJ)
    have h := ENNReal.toReal_mono hBf hBvol
    rwa [ENNReal.toReal_ofReal (by linarith)] at h
  have hνB' : (ν B).toReal ≤ η * (V / (b - a)) * (b - a) := by
    rw [mul_assoc, div_mul_cancel₀ _ hℓ.ne']
    exact hνB
  have hint := s07d_p4_core_int (r := 1 - (b - a) / (2 * π)) (φ := (a + b) / 2) (ℓ := b - a)
    (Λ := V / (b - a)) (τ := η * (V / (b - a))) hD hη0 hη4 hfin hdbl hwm hw0 hwν hr0 hr1 hℓ hlen
    (by ring) hΛeq (div_pos hV0 hℓ) rfl hBm hBJ' hvolBge hνB'
  have hτ : 0 < η * (V / (b - a)) := by positivity
  have h1 := hH1 (1 - (b - a) / (2 * π)) ((a + b) / 2) (η * (V / (b - a))) hr0 hr1 hτ
  have h2 := hH2 a b hab hlen
  set U := u (1 - (b - a) / (2 * π)) ((a + b) / 2) with hU
  have h2R : V ≤ C₁ * (b - a) * Real.exp U := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    rwa [ENNReal.toReal_ofReal (by positivity)] at h
  have h3 : Real.log V ≤ Real.log C₁ + Real.log (b - a) + U := by
    have h := Real.log_le_log hV0 h2R
    rwa [Real.log_mul (by positivity) (Real.exp_pos U).ne', Real.log_mul hC₁.ne' hℓ.ne',
      Real.log_exp] at h
  have h4 : Real.log (V / (b - a)) = Real.log V - Real.log (b - a) :=
    Real.log_div hV0.ne' hℓ.ne'
  rw [h4, hl4] at hint
  have h5 : -(m * (|A| + 1)) / (2 * (1 + π ^ 2)) = -(|A| + 1) := by
    rw [hm]
    field_simp
  rw [h5] at hint
  have h6 := le_abs_self A
  rw [hA] at h6
  linarith

/-! ### P4.4 probe (w4): the `h → 0` limit / uniform-integrability step of `jensen` -/

/-- P4.4 probe helper (w4): finite on compact intervals ⇒ locally finite. -/
theorem s07d_p4_jl_lfin {ν : Measure ℝ} (hfin : ∀ a b : ℝ, ν (Icc a b) ≠ ⊤) :
    IsLocallyFiniteMeasure ν :=
  ⟨fun x => ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith),
    lt_top_iff_ne_top.2 (hfin _ _)⟩⟩

/-- P4.4 probe helper (w4): the density `w = (dν/dθ).toReal` satisfies `∫_E w ≤ ν(E)`. -/
theorem s07d_p4_jl_wle {ν : Measure ℝ} (E : Set ℝ) (hE : MeasurableSet E) :
    ∫⁻ t in E, ENNReal.ofReal (ν.rnDeriv volume t).toReal ≤ ν E := by
  have h := Measure.withDensity_rnDeriv_le ν volume
  have h2 := h E
  rw [withDensity_apply _ hE] at h2
  refine le_trans (lintegral_mono fun t => ?_) h2
  exact ENNReal.ofReal_toReal_le

/-- P4.4 probe helper (w4): `log (1 + y)² ≤ 4 y` for `y ≥ 0`. -/
theorem s07d_p4_jl_logsq {y : ℝ} (hy : 0 ≤ y) : Real.log (1 + y) ^ 2 ≤ 4 * y := by
  have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hs : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  have hq := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ 2 * Real.sqrt y)
  have h1 : Real.log (1 + y) ≤ 2 * Real.sqrt y := by
    rw [Real.log_le_iff_le_exp (by linarith)]
    nlinarith
  have h0 : 0 ≤ Real.log (1 + y) := Real.log_nonneg (by linarith)
  have h2 := pow_le_pow_left₀ h0 h1 2
  nlinarith

/-- P4.4 probe helper (w4): `t ↦ ν[t - h, t + h]` is a.e.-strongly measurable on `[a, b]`
(difference of two monotone functions there). -/
theorem s07d_p4_jl_meas {ν : Measure ℝ} (hfin : ∀ a b : ℝ, ν (Icc a b) ≠ ⊤) (a b h : ℝ)
    (hh : 0 ≤ h) :
    AEStronglyMeasurable (fun t => (ν (Icc (t - h) (t + h))).toReal)
      (volume.restrict (Icc a b)) := by
  have hu : Monotone fun t => (ν (Icc (a - h) (t + h))).toReal := fun x y hxy =>
    ENNReal.toReal_mono (hfin _ _) (measure_mono (Icc_subset_Icc le_rfl (by linarith)))
  have hv : Monotone fun t => (ν (Ico (a - h) (t - h))).toReal := fun x y hxy =>
    ENNReal.toReal_mono (ne_top_of_le_ne_top (hfin (a - h) (y - h))
      (measure_mono Ico_subset_Icc_self)) (measure_mono (Ico_subset_Ico le_rfl (by linarith)))
  refine ((hu.measurable.sub hv.measurable).aestronglyMeasurable).congr ?_
  refine (ae_restrict_mem measurableSet_Icc).mono fun t ht => ?_
  have hU : Ico (a - h) (t - h) ∪ Icc (t - h) (t + h) = Icc (a - h) (t + h) :=
    Ico_union_Icc_eq_Icc (by linarith [ht.1]) (by linarith)
  have hD : Disjoint (Ico (a - h) (t - h)) (Icc (t - h) (t + h)) :=
    Set.disjoint_left.2 fun s hs1 hs2 => (not_le.2 hs1.2) hs2.1
  have hm := measure_union (μ := ν) hD measurableSet_Icc
  rw [hU] at hm
  have hfA : ν (Ico (a - h) (t - h)) ≠ ⊤ :=
    ne_top_of_le_ne_top (hfin (a - h) (t - h)) (measure_mono Ico_subset_Icc_self)
  show (ν (Icc (a - h) (t + h))).toReal - (ν (Ico (a - h) (t - h))).toReal =
    (ν (Icc (t - h) (t + h))).toReal
  rw [hm, ENNReal.toReal_add hfA (hfin _ _)]
  ring

/-- P4.4 probe helper (w4): Lebesgue differentiation, `ν[t-h, t+h]/(2h) → (dν/dθ)(t)` a.e. -/
theorem s07d_p4_jl_lim {ν : Measure ℝ} (hfin : ∀ a b : ℝ, ν (Icc a b) ≠ ⊤) :
    ∀ᵐ t ∂volume, Tendsto (fun h => (ν (Icc (t - h) (t + h))).toReal / (2 * h)) (𝓝[>] 0)
      (𝓝 (ν.rnDeriv volume t).toReal) := by
  haveI := s07d_p4_jl_lfin hfin
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv ν volume, Measure.rnDeriv_lt_top ν volume]
    with t ht hlt
  refine ((ENNReal.tendsto_toReal hlt.ne).comp ht).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : 0 < h := hh
  show (ν (closedBall t h) / volume (closedBall t h)).toReal =
    (ν (Icc (t - h) (t + h))).toReal / (2 * h)
  rw [Real.closedBall_eq_Icc, Real.volume_Icc, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (by linarith)]
  congr 1
  ring

/-- P4.4 probe helper (w4): Tonelli, `∫_a^b ν[t-h, t+h] dt ≤ 2h ν[a-h, b+h]`. -/
theorem s07d_p4_jl_fub {ν : Measure ℝ} (hfin : ∀ a b : ℝ, ν (Icc a b) ≠ ⊤) {a b h : ℝ}
    (hh : 0 ≤ h) :
    ∫⁻ t in Icc a b, ν (Icc (t - h) (t + h)) ≤
      ENNReal.ofReal (2 * h) * ν (Icc (a - h) (b + h)) := by
  haveI := s07d_p4_jl_lfin hfin
  set S : Set (ℝ × ℝ) := {p | |p.2 - p.1| ≤ h} with hS
  have hSm : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have h1 : ∀ t, ν (Icc (t - h) (t + h)) = ∫⁻ s, S.indicator 1 (t, s) ∂ν := by
    intro t
    rw [← lintegral_indicator_one measurableSet_Icc]
    refine lintegral_congr fun s => ?_
    have e : s ∈ Icc (t - h) (t + h) ↔ (t, s) ∈ S := by
      rw [Set.mem_Icc, hS, Set.mem_setOf_eq, abs_le]
      constructor
      · intro h'
        constructor <;> linarith [h'.1, h'.2]
      · intro h'
        constructor <;> linarith [h'.1, h'.2]
    by_cases hs : s ∈ Icc (t - h) (t + h)
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (e.1 hs)]
      rfl
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (fun h' => hs (e.2 h'))]
  rw [lintegral_congr h1, lintegral_lintegral_swap
    (f := fun t s => S.indicator (1 : ℝ × ℝ → ℝ≥0∞) (t, s))
    (measurable_one.indicator hSm).aemeasurable]
  calc _ ≤ ∫⁻ s, ENNReal.ofReal (2 * h) * (Icc (a - h) (b + h)).indicator 1 s ∂ν := by
        refine lintegral_mono fun s => ?_
        by_cases hs : s ∈ Icc (a - h) (b + h)
        · rw [Set.indicator_of_mem hs, Pi.one_apply, mul_one]
          calc _ ≤ ∫⁻ t, S.indicator 1 (t, s) := setLIntegral_le_lintegral _ _
            _ = volume (Icc (s - h) (s + h)) := by
                rw [← lintegral_indicator_one measurableSet_Icc]
                refine lintegral_congr fun t => ?_
                have e : t ∈ Icc (s - h) (s + h) ↔ (t, s) ∈ S := by
                  rw [Set.mem_Icc, hS, Set.mem_setOf_eq, abs_le]
                  constructor
                  · intro h'
                    constructor <;> linarith [h'.1, h'.2]
                  · intro h'
                    constructor <;> linarith [h'.1, h'.2]
                by_cases ht : t ∈ Icc (s - h) (s + h)
                · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (e.1 ht)]
                  rfl
                · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (fun h' => ht (e.2 h'))]
            _ = ENNReal.ofReal (2 * h) := by
                rw [Real.volume_Icc]
                congr 1
                ring
        · rw [Set.indicator_of_notMem hs, mul_zero]
          calc _ ≤ ∫⁻ t in Icc a b, (0 : ℝ≥0∞) := by
                refine setLIntegral_mono' measurableSet_Icc fun t ht => le_of_eq ?_
                refine Set.indicator_of_notMem (fun h' => hs ?_) _
                rw [hS, Set.mem_setOf_eq, abs_le] at h'
                exact ⟨by linarith [ht.1, h'.1], by linarith [ht.2, h'.2]⟩
            _ = 0 := lintegral_zero
    _ = ENNReal.ofReal (2 * h) * ν (Icc (a - h) (b + h)) := by
        rw [lintegral_const_mul _ (measurable_one.indicator measurableSet_Icc),
          lintegral_indicator_one measurableSet_Icc]

/-- P4.4 probe helper (w4): truncation of `log(A + τ)` at height `M` above `log τ`, with the
`L²`-type remainder `4A/(τM)`. -/
theorem s07d_p4_jl_trunc {A P τ M : ℝ} (hA : 0 ≤ A) (hP : 0 ≤ P) (hτ : 0 < τ) (hM : 0 < M) :
    Real.log (A + τ) * P ≤ (Real.log τ + min (Real.log (1 + A / τ)) M) * P +
      4 / (τ * M) * (A * P) := by
  have hy : 0 ≤ A / τ := div_nonneg hA hτ.le
  have hF0 : 0 ≤ Real.log (1 + A / τ) := Real.log_nonneg (by linarith)
  have hsplit : Real.log (A + τ) = Real.log τ + Real.log (1 + A / τ) := by
    rw [← Real.log_mul hτ.ne' (by positivity)]
    congr 1
    field_simp
    ring
  have hsq := s07d_p4_jl_logsq hy
  have hF : Real.log (1 + A / τ) ≤ min (Real.log (1 + A / τ)) M + 4 / (τ * M) * A := by
    have hc : 0 ≤ 4 / (τ * M) * A := by positivity
    rcases le_total (Real.log (1 + A / τ)) M with h | h
    · rw [min_eq_left h]
      linarith
    · rw [min_eq_right h]
      have h1 : Real.log (1 + A / τ) * M ≤ Real.log (1 + A / τ) ^ 2 := by nlinarith
      have h2 : Real.log (1 + A / τ) ^ 2 / M ≤ 4 / (τ * M) * A := by
        rw [div_le_iff₀ hM]
        have e : 4 / (τ * M) * A * M = 4 * (A / τ) := by field_simp
        rw [e]
        exact hsq
      have h3 : Real.log (1 + A / τ) ≤ Real.log (1 + A / τ) ^ 2 / M := by
        rw [le_div_iff₀ hM]
        exact h1
      linarith
  rw [hsplit]
  have := mul_le_mul_of_nonneg_right hF hP
  nlinarith

/-- P4.4 probe helper (w4): real form of the Tonelli bound, `∫_a^b ν[t-h,t+h] dt ≤ 2h ν[a-1,b+1]`
for `0 < h ≤ 1`, together with integrability. -/
theorem s07d_p4_jl_fubR {ν : Measure ℝ} (hfin : ∀ a b : ℝ, ν (Icc a b) ≠ ⊤) {a b h : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) :
    IntegrableOn (fun t => (ν (Icc (t - h) (t + h))).toReal) (Icc a b) volume ∧
    ∫ t in Icc a b, (ν (Icc (t - h) (t + h))).toReal ≤
      2 * h * (ν (Icc (a - 1) (b + 1))).toReal := by
  have hmeas := s07d_p4_jl_meas hfin a b h hh.le
  have hbd : ∀ t ∈ Icc a b, ‖(ν (Icc (t - h) (t + h))).toReal‖ ≤
      (ν (Icc (a - 1) (b + 1))).toReal := fun t ht => by
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono (hfin _ _)
      (measure_mono (Icc_subset_Icc (by linarith [ht.1]) (by linarith [ht.2])))
  have hint : IntegrableOn (fun t => (ν (Icc (t - h) (t + h))).toReal) (Icc a b) volume := by
    refine Integrable.mono' (g := fun _ => (ν (Icc (a - 1) (b + 1))).toReal)
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) hmeas ?_
    exact (ae_restrict_mem measurableSet_Icc).mono hbd
  refine ⟨hint, ?_⟩
  have hfub := s07d_p4_jl_fub hfin (a := a) (b := b) hh.le
  have h1 : ENNReal.ofReal (∫ t in Icc a b, (ν (Icc (t - h) (t + h))).toReal) =
      ∫⁻ t in Icc a b, ν (Icc (t - h) (t + h)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun t => ENNReal.toReal_nonneg)]
    exact lintegral_congr fun t => ENNReal.ofReal_toReal (hfin _ _)
  have h2 : ENNReal.ofReal (∫ t in Icc a b, (ν (Icc (t - h) (t + h))).toReal) ≤
      ENNReal.ofReal (2 * h) * ν (Icc (a - 1) (b + 1)) := by
    rw [h1]
    exact hfub.trans (mul_le_mul_of_nonneg_left (measure_mono
      (Icc_subset_Icc (by linarith) (by linarith))) zero_le)
  have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin _ _)) h2
  rw [ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc
      fun t _ => ENNReal.toReal_nonneg), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith)] at h3
  exact h3

/-- P4.4 probe helper (w4): the truncated integrands converge (dominated convergence). -/
theorem s07d_p4_jl_dct {ν : Measure ℝ} (hfin : ∀ a b : ℝ, ν (Icc a b) ≠ ⊤) {P : ℝ → ℝ}
    (hPc : Continuous P) {τ M a b Pm : ℝ} (hτ : 0 < τ)
    (hPm : ∀ t ∈ Icc a b, |P t| ≤ Pm) :
    Tendsto (fun h => ∫ t in Icc a b, (Real.log τ +
        min (Real.log (1 + (ν (Icc (t - h) (t + h))).toReal / (2 * h) / τ)) M) * P t)
      (𝓝[>] 0)
      (𝓝 (∫ t in Icc a b, (Real.log τ +
        min (Real.log (1 + (ν.rnDeriv volume t).toReal / τ)) M) * P t)) := by
  have hφm : Measurable fun y : ℝ => Real.log τ + min (Real.log (1 + y / τ)) M := by fun_prop
  refine tendsto_integral_filter_of_dominated_convergence
    (fun _ => (|Real.log τ| + |M|) * Pm) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : 0 < h := hh
    have hA := (s07d_p4_jl_meas hfin a b h hh0.le).aemeasurable.div_const (2 * h)
    exact ((hφm.comp_aemeasurable hA).mul hPc.measurable.aemeasurable).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : 0 < h := hh
    refine (ae_restrict_mem measurableSet_Icc).mono fun t ht => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |Real.log τ + min (Real.log (1 + (ν (Icc (t - h) (t + h))).toReal / (2 * h) / τ)) M|
        ≤ |Real.log τ| + |M| := by
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_le]
      constructor
      · have hA0 : 0 ≤ (ν (Icc (t - h) (t + h))).toReal / (2 * h) / τ :=
          div_nonneg (div_nonneg ENNReal.toReal_nonneg (by linarith)) hτ.le
        have hl0 := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 +
          (ν (Icc (t - h) (t + h))).toReal / (2 * h) / τ)
        exact le_min (by linarith [abs_nonneg M]) (neg_abs_le M)
      · exact (min_le_right _ _).trans (le_abs_self M)
    exact mul_le_mul h1 (hPm t ht) (abs_nonneg _) (by positivity)
  · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  · refine ae_restrict_of_ae ?_
    filter_upwards [s07d_p4_jl_lim hfin] with t ht
    have hne : 1 + (ν.rnDeriv volume t).toReal / τ ≠ 0 := by
      have : 0 ≤ (ν.rnDeriv volume t).toReal / τ := div_nonneg ENNReal.toReal_nonneg hτ.le
      linarith
    have hc : ContinuousAt (fun y : ℝ => Real.log τ + min (Real.log (1 + y / τ)) M)
        (ν.rnDeriv volume t).toReal :=
      continuousAt_const.add (ContinuousAt.comp (g := fun z : ℝ => min z M)
        (f := fun y : ℝ => Real.log (1 + y / τ)) (continuous_id.min continuous_const).continuousAt
        (ContinuousAt.comp (f := fun y : ℝ => 1 + y / τ) (Real.continuousAt_log hne)
          (by fun_prop)))
    exact (hc.tendsto.comp ht).mul_const (P t)

/-- P4.4 probe helper (w4): the truncated integrand is integrable on `[a, b]`. -/
theorem s07d_p4_jl_Gint {A P : ℝ → ℝ} {τ M a b Pm : ℝ}
    (hAm : AEStronglyMeasurable A (volume.restrict (Icc a b))) (hA0 : ∀ t, 0 ≤ A t)
    (hPc : Continuous P) (hτ : 0 < τ) (hPm : ∀ t ∈ Icc a b, |P t| ≤ Pm) :
    IntegrableOn (fun t => (Real.log τ + min (Real.log (1 + A t / τ)) M) * P t) (Icc a b)
      volume := by
  have hφm : Measurable fun y : ℝ => Real.log τ + min (Real.log (1 + y / τ)) M := by fun_prop
  refine Integrable.mono' (g := fun _ => (|Real.log τ| + |M|) * Pm)
    (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    ((hφm.comp_aemeasurable hAm.aemeasurable).mul hPc.measurable.aemeasurable).aestronglyMeasurable
    ?_
  refine (ae_restrict_mem measurableSet_Icc).mono fun t ht => ?_
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 : |Real.log τ + min (Real.log (1 + A t / τ)) M| ≤ |Real.log τ| + |M| := by
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_le]
    constructor
    · have hl0 := Real.log_nonneg (by have := div_nonneg (hA0 t) hτ.le; linarith :
        (1 : ℝ) ≤ 1 + A t / τ)
      exact le_min (by linarith [abs_nonneg M]) (neg_abs_le M)
    · exact (min_le_right _ _).trans (le_abs_self M)
  exact mul_le_mul h1 (hPm t ht) (abs_nonneg _) (by positivity)

/-- P4.4 probe helper (w4): `log(A + τ) P` is integrable on `[a, b]` when `A ≥ 0` is. -/
theorem s07d_p4_jl_Lint {A P : ℝ → ℝ} {τ a b Pm : ℝ}
    (hAm : AEStronglyMeasurable A (volume.restrict (Icc a b))) (hA0 : ∀ t, 0 ≤ A t)
    (hAi : IntegrableOn A (Icc a b) volume)
    (hPc : Continuous P) (hτ : 0 < τ) (hPm : ∀ t ∈ Icc a b, |P t| ≤ Pm) :
    IntegrableOn (fun t => Real.log (A t + τ) * P t) (Icc a b) volume := by
  have hW : volume (Icc a b) ≠ ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hφm : Measurable fun y : ℝ => Real.log (y + τ) := by fun_prop
  refine Integrable.mono' (g := fun t => (|Real.log τ| + (A t + τ)) * Pm)
    (((integrableOn_const hW).add (hAi.add (integrableOn_const hW))).mul_const Pm)
    ((hφm.comp_aemeasurable hAm.aemeasurable).mul hPc.measurable.aemeasurable).aestronglyMeasurable
    ?_
  refine (ae_restrict_mem measurableSet_Icc).mono fun t ht => ?_
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 := s07d_p4_core_abs_log hτ (by linarith [hA0 t] : τ ≤ A t + τ)
  exact mul_le_mul h1 (hPm t ht) (abs_nonneg _) (by linarith [abs_nonneg (Real.log τ), hA0 t])

/-- P4.4 probe helper (w4): truncation only lowers the integrand. -/
theorem s07d_p4_jl_Gle {A P τ M : ℝ} (hA : 0 ≤ A) (hP : 0 ≤ P) (hτ : 0 < τ) :
    (Real.log τ + min (Real.log (1 + A / τ)) M) * P ≤ Real.log (A + τ) * P := by
  have hsplit : Real.log (A + τ) = Real.log τ + Real.log (1 + A / τ) := by
    rw [← Real.log_mul hτ.ne' (by positivity)]
    congr 1
    field_simp
    ring
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right (add_le_add le_rfl (min_le_left _ _)) hP

/-- **P4.4 probe** (w4): the `h → 0` limit step of `jensen`.  For a measure `ν` finite on
compact intervals, a continuous weight `P ≥ 0` and `τ > 0`, the integrals of
`log(ν[t-h, t+h]/(2h) + τ) P(t)` over `[a, b]` are eventually `≤ ∫ log(dν/dθ + τ) P + ε`. -/
theorem s07d_p4_jl_main {ν : Measure ℝ} (hfin : ∀ a b : ℝ, ν (Icc a b) ≠ ⊤) {P : ℝ → ℝ}
    (hPc : Continuous P) (hP0 : ∀ t, 0 ≤ P t) {τ a b ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), ∫ t in Icc a b,
        Real.log ((ν (Icc (t - h) (t + h))).toReal / (2 * h) + τ) * P t ≤
      (∫ t in Icc a b, Real.log ((ν.rnDeriv volume t).toReal + τ) * P t) + ε := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a b) hPc.continuousOn
  have hPm : ∀ t ∈ Icc a b, |P t| ≤ max C 0 := fun t ht => by
    have h := hC t ht
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  have hPm0 : 0 ≤ max C 0 := le_max_right _ _
  set Pm := max C 0 with hPmdef
  set V := (ν (Icc (a - 1) (b + 1))).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set M := 8 * Pm * V / (τ * ε) + 1 with hMdef
  have hM0 : 0 < M := by rw [hMdef]; positivity
  have hMε : 4 / (τ * M) * (Pm * V) ≤ ε / 2 := by
    have e2 : ε / 2 * (τ * M) = 4 * (Pm * V) + ε * τ / 2 := by
      rw [hMdef]
      field_simp
      ring
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < τ * M), e2]
    nlinarith [mul_pos hε hτ]
  -- the `L¹` density
  have hwm : Measurable fun t => (ν.rnDeriv volume t).toReal :=
    (Measure.measurable_rnDeriv ν volume).ennreal_toReal
  have hw := s07d_p4_core_wint hwm (fun t => ENNReal.toReal_nonneg)
    (s07d_p4_jl_wle (ν := ν) (Icc a b) measurableSet_Icc) (hfin a b)
  have hwA : AEStronglyMeasurable (fun t => (ν.rnDeriv volume t).toReal)
      (volume.restrict (Icc a b)) := hwm.aestronglyMeasurable
  have iL := s07d_p4_jl_Lint hwA (fun t => ENNReal.toReal_nonneg) hw.1 hPc hτ hPm
  have iG := s07d_p4_jl_Gint (M := M) hwA (fun t => ENNReal.toReal_nonneg) hPc hτ hPm
  have hGle : (∫ t in Icc a b, (Real.log τ +
      min (Real.log (1 + (ν.rnDeriv volume t).toReal / τ)) M) * P t) ≤
      ∫ t in Icc a b, Real.log ((ν.rnDeriv volume t).toReal + τ) * P t :=
    setIntegral_mono_on iG iL measurableSet_Icc fun t _ =>
      s07d_p4_jl_Gle ENNReal.toReal_nonneg (hP0 t) hτ
  have hdct := s07d_p4_jl_dct hfin hPc (M := M) hτ hPm
  filter_upwards [(tendsto_order.1 hdct).2 _ (lt_add_of_pos_right _ (half_pos hε)),
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with h hG hh
  have hh0 : 0 < h := hh.1
  obtain ⟨hνi, hνb⟩ := s07d_p4_jl_fubR hfin (a := a) (b := b) hh0 hh.2.le
  have hAm : AEStronglyMeasurable (fun t => (ν (Icc (t - h) (t + h))).toReal / (2 * h))
      (volume.restrict (Icc a b)) :=
    ((s07d_p4_jl_meas hfin a b h hh0.le).aemeasurable.div_const _).aestronglyMeasurable
  have hA0 : ∀ t, 0 ≤ (ν (Icc (t - h) (t + h))).toReal / (2 * h) := fun t =>
    div_nonneg ENNReal.toReal_nonneg (by linarith)
  have hAi : IntegrableOn (fun t => (ν (Icc (t - h) (t + h))).toReal / (2 * h)) (Icc a b)
      volume := hνi.div_const _
  have iLh := s07d_p4_jl_Lint hAm hA0 hAi hPc hτ hPm
  have iGh := s07d_p4_jl_Gint (M := M) hAm hA0 hPc hτ hPm
  have iAP : IntegrableOn (fun t => (ν (Icc (t - h) (t + h))).toReal / (2 * h) * P t) (Icc a b)
      volume := hAi.mul_continuousOn hPc.continuousOn isCompact_Icc
  have iR : IntegrableOn (fun t => (Real.log τ +
      min (Real.log (1 + (ν (Icc (t - h) (t + h))).toReal / (2 * h) / τ)) M) * P t +
      4 / (τ * M) * ((ν (Icc (t - h) (t + h))).toReal / (2 * h) * P t)) (Icc a b) volume :=
    iGh.add (iAP.const_mul _)
  have h1 := setIntegral_mono_on iLh iR measurableSet_Icc fun t _ =>
    s07d_p4_jl_trunc (hA0 t) (hP0 t) hτ hM0
  rw [integral_add iGh (iAP.const_mul _), integral_const_mul] at h1
  have h2 : ∫ t in Icc a b, (ν (Icc (t - h) (t + h))).toReal / (2 * h) * P t ≤ Pm * V := by
    have iPA : IntegrableOn (fun t => Pm * ((ν (Icc (t - h) (t + h))).toReal / (2 * h)))
        (Icc a b) volume := hAi.const_mul _
    calc _ ≤ ∫ t in Icc a b, Pm * ((ν (Icc (t - h) (t + h))).toReal / (2 * h)) :=
          setIntegral_mono_on iAP iPA measurableSet_Icc fun t ht => by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hPm t ht)) (hA0 t)
      _ = Pm * ((∫ t in Icc a b, (ν (Icc (t - h) (t + h))).toReal) / (2 * h)) := by
          rw [integral_const_mul, integral_div]
      _ ≤ Pm * (2 * h * V / (2 * h)) := by
          refine mul_le_mul_of_nonneg_left ?_ hPm0
          exact div_le_div_of_nonneg_right hνb (by linarith)
      _ = Pm * V := by
          field_simp
  have h3 : 4 / (τ * M) * ∫ t in Icc a b,
      (ν (Icc (t - h) (t + h))).toReal / (2 * h) * P t ≤ ε / 2 :=
    (mul_le_mul_of_nonneg_left h2 (by positivity)).trans hMε
  linarith

/-! ### P4.4 (w4): `jensen` -/

/-- P4.4 helper (w4): the Poisson representation of `log ‖g‖` on the circle `|z| = s`, in the
window `[φ - π, φ + π]` with kernel `P_{r/s}(t - φ)`. -/
theorem s07d_p4_jn_poisson {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc)
    (hg0 : ∀ z ∈ unitDisc, g z ≠ 0) {r s φ : ℝ} (hr0 : 0 ≤ r) (hrs : r < s) (hs1 : s < 1) :
    Real.log ‖g ((r : ℂ) * Complex.exp (φ * Complex.I))‖ =
      (1 / (2 * π)) * ∫ t in (φ - π)..(φ + π),
        Real.log ‖g ((s : ℂ) * Complex.exp (t * Complex.I))‖ *
          ((1 - (r / s) ^ 2) / (1 - 2 * (r / s) * Real.cos (t - φ) + (r / s) ^ 2)) := by
  have hpi := Real.pi_pos
  have hs0 : 0 < s := lt_of_le_of_lt hr0 hrs
  have hharm : InnerProductSpace.HarmonicOnNhd (fun z => Real.log ‖g z‖) (closedBall (0 : ℂ) s) := by
    intro x hx
    have hxD : x ∈ unitDisc := by
      show x ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff]
      rw [mem_closedBall_zero_iff] at hx
      linarith
    have han : AnalyticAt ℂ g x :=
      hg.analyticAt ((isOpen_ball : IsOpen (ball (0 : ℂ) 1)).mem_nhds hxD)
    exact han.harmonicAt_log_norm (hg0 x hxD)
  have hw : (r : ℂ) * Complex.exp (φ * Complex.I) ∈ ball (0 : ℂ) s := by
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_of_nonneg hr0]
    exact hrs
  have h := hharm.circleAverage_poissonKernel_smul hw
  rw [Real.circleAverage_eq_integral_add (φ - π), smul_eq_mul,
    intervalIntegral.integral_comp_add_right
      (fun θ => (poissonKernel 0 ((r : ℂ) * Complex.exp (φ * Complex.I)) •
        fun z => Real.log ‖g z‖) (circleMap 0 s θ)) (φ - π)] at h
  have e1 : (0 : ℝ) + (φ - π) = φ - π := by ring
  have e2 : 2 * π + (φ - π) = φ + π := by ring
  rw [e1, e2] at h
  rw [← h]
  have hρ0 : 0 ≤ r / s := div_nonneg hr0 hs0.le
  have hρ1 : r / s < 1 := (div_lt_one hs0).2 hrs
  have hint : ∀ t : ℝ, (poissonKernel 0 ((r : ℂ) * Complex.exp (φ * Complex.I)) •
      fun z => Real.log ‖g z‖) (circleMap 0 s t) =
      Real.log ‖g ((s : ℂ) * Complex.exp (t * Complex.I))‖ *
        ((1 - (r / s) ^ 2) / (1 - 2 * (r / s) * Real.cos (t - φ) + (r / s) ^ 2)) := by
    intro t
    rw [Pi.smul_apply', smul_eq_mul, circleMap_zero, poissonKernel_def]
    simp only [sub_zero]
    have hn1 : ‖(s : ℂ) * Complex.exp (t * Complex.I)‖ = s := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_of_nonneg hs0.le]
    have hn2 : ‖(r : ℂ) * Complex.exp (φ * Complex.I)‖ = r := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_of_nonneg hr0]
    have hfac : (s : ℂ) * Complex.exp (t * Complex.I) - (r : ℂ) * Complex.exp (φ * Complex.I) =
        (s : ℂ) * (Complex.exp (t * Complex.I) - ((r / s : ℝ) : ℂ) * Complex.exp (φ * Complex.I)) := by
      have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
      push_cast
      rw [mul_sub]
      congr 1
      field_simp
    have hn3 : ‖(s : ℂ) * Complex.exp (t * Complex.I) - (r : ℂ) * Complex.exp (φ * Complex.I)‖ ^ 2 =
        s ^ 2 * (1 - 2 * (r / s) * Real.cos (t - φ) + (r / s) ^ 2) := by
      rw [hfac, norm_mul, mul_pow, s07d_p4_core_norm, Complex.norm_of_nonneg hs0.le]
    rw [hn1, hn2, hn3]
    have hd := s07d_p4_core_den_pos hρ0 hρ1 (t - φ)
    have e : (s ^ 2 - r ^ 2) / (s ^ 2 * (1 - 2 * (r / s) * Real.cos (t - φ) + (r / s) ^ 2)) =
        (1 - (r / s) ^ 2) / (1 - 2 * (r / s) * Real.cos (t - φ) + (r / s) ^ 2) := by
      field_simp
    rw [e]
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hint t)]
  ring

/-- P4.4 helper (w4): translation invariance of the window integral of a `2π`-periodic
continuous function. -/
theorem s07d_p4_jn_per {G : ℝ → ℝ} (hG : Continuous G) (hGp : Function.Periodic G (2 * π))
    (x φ : ℝ) :
    ∫ t in Icc (φ - π) (φ + π), G (t + x) = ∫ t in Icc (φ - π) (φ + π), G t := by
  have hpi := Real.pi_pos
  have hconv : ∀ F : ℝ → ℝ, ∫ t in Icc (φ - π) (φ + π), F t = ∫ t in (φ - π)..(φ + π), F t :=
    fun F => by rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
  rw [hconv, hconv, intervalIntegral.integral_comp_add_right (fun t => G t) x]
  have e1 : φ + π + x = (φ - π + x) + 2 * π := by ring
  have e2 : φ + π = (φ - π) + 2 * π := by ring
  rw [e1, e2]
  exact hGp.intervalIntegral_add_eq _ _

/-- P4.4 helper (w4): replacing `f` by its moving average `M_h f` in a window integral against a
periodic weight `P` costs at most `δ ∫ |f|`, where `δ` bounds the oscillation of `P` at scale `h`
(Fubini + periodicity). -/
theorem s07d_p4_jn_swap {P f : ℝ → ℝ} (hP : Continuous P) (hf : Continuous f)
    (hPp : Function.Periodic P (2 * π)) (hfp : Function.Periodic f (2 * π)) {h φ δ : ℝ}
    (hh : 0 < h) (hδ : ∀ t x, x ∈ Icc (-h) h → |P t - P (t - x)| ≤ δ) :
    ∫ t in Icc (φ - π) (φ + π), f t * P t ≤
      (∫ t in Icc (φ - π) (φ + π), (1 / (2 * h) * ∫ x in Icc (-h) h, f (t + x)) * P t) +
        δ * ∫ t in Icc (φ - π) (φ + π), |f t| := by
  have hXv : volume.real (Icc (-h) h) = 2 * h := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hFc : Continuous (Function.uncurry fun (t x : ℝ) => f (t + x) * P t) :=
    (hf.comp (continuous_fst.add continuous_snd)).mul (hP.comp continuous_fst)
  have hFi : Integrable (Function.uncurry fun (t x : ℝ) => f (t + x) * P t)
      ((volume.restrict (Icc (φ - π) (φ + π))).prod (volume.restrict (Icc (-h) h))) := by
    rw [Measure.prod_restrict]
    exact hFc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have S1 : (∫ t in Icc (φ - π) (φ + π), (1 / (2 * h) * ∫ x in Icc (-h) h, f (t + x)) * P t) =
      1 / (2 * h) * ∫ x in Icc (-h) h, ∫ t in Icc (φ - π) (φ + π), f (t + x) * P t := by
    have e : ∀ t, (1 / (2 * h) * ∫ x in Icc (-h) h, f (t + x)) * P t =
        1 / (2 * h) * ∫ x in Icc (-h) h, f (t + x) * P t := fun t => by
      rw [integral_mul_const]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_const_mul,
      integral_integral_swap hFi]
  have S2 : ∀ x, ∫ t in Icc (φ - π) (φ + π), f (t + x) * P t =
      ∫ t in Icc (φ - π) (φ + π), f t * P (t - x) := fun x => by
    have hGc : Continuous fun t => f t * P (t - x) := hf.mul (hP.comp (continuous_id.sub continuous_const))
    have hGp : Function.Periodic (fun t => f t * P (t - x)) (2 * π) := fun t => by
      show f (t + 2 * π) * P (t + 2 * π - x) = f t * P (t - x)
      rw [hfp t, show t + 2 * π - x = (t - x) + 2 * π by ring, hPp]
    have := s07d_p4_jn_per hGc hGp x φ
    simp only [add_sub_cancel_right] at this
    exact this
  have hI1 : IntegrableOn (fun _ : ℝ => ∫ t in Icc (φ - π) (φ + π), f t * P t) (Icc (-h) h)
      volume := integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hI2c : Continuous fun x : ℝ => ∫ t in Icc (φ - π) (φ + π), f t * P (t - x) :=
    continuous_parametric_integral_of_continuous (f := fun (x t : ℝ) => f t * P (t - x))
      ((hf.comp continuous_snd).mul (hP.comp (continuous_snd.sub continuous_fst))) isCompact_Icc
  have hI2 : IntegrableOn (fun x : ℝ => ∫ t in Icc (φ - π) (φ + π), f t * P (t - x))
      (Icc (-h) h) volume := hI2c.integrableOn_Icc
  have hfW : IntegrableOn f (Icc (φ - π) (φ + π)) volume := hf.integrableOn_Icc
  have hD : ∀ x ∈ Icc (-h) h, (∫ t in Icc (φ - π) (φ + π), f t * P t) -
      (∫ t in Icc (φ - π) (φ + π), f t * P (t - x)) ≤ δ * ∫ t in Icc (φ - π) (φ + π), |f t| := by
    intro x hx
    have i1 : IntegrableOn (fun t => f t * P t) (Icc (φ - π) (φ + π)) volume :=
      (hf.mul hP).integrableOn_Icc
    have i2 : IntegrableOn (fun t => f t * P (t - x)) (Icc (φ - π) (φ + π)) volume :=
      (hf.mul (hP.comp (continuous_id.sub continuous_const))).integrableOn_Icc
    rw [← integral_sub i1 i2, ← integral_const_mul]
    refine setIntegral_mono_on (i1.sub i2) (hfW.abs.const_mul δ) measurableSet_Icc
      fun t _ => ?_
    have h1 : f t * P t - f t * P (t - x) = f t * (P t - P (t - x)) := by ring
    show f t * P t - f t * P (t - x) ≤ δ * |f t|
    rw [h1]
    calc f t * (P t - P (t - x)) ≤ |f t * (P t - P (t - x))| := le_abs_self _
      _ = |f t| * |P t - P (t - x)| := abs_mul _ _
      _ ≤ |f t| * δ := mul_le_mul_of_nonneg_left (hδ t x hx) (abs_nonneg _)
      _ = δ * |f t| := mul_comm _ _
  have hI12 : IntegrableOn (fun x : ℝ => (∫ t in Icc (φ - π) (φ + π), f t * P t) -
      ∫ t in Icc (φ - π) (φ + π), f t * P (t - x)) (Icc (-h) h) volume := hI1.sub hI2
  have hDi := setIntegral_mono_on hI12
    (integrableOn_const (C := δ * ∫ t in Icc (φ - π) (φ + π), |f t|)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) measurableSet_Icc hD
  rw [integral_sub hI1 hI2, setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul,
    hXv] at hDi
  rw [S1, integral_congr_ae (Filter.Eventually.of_forall S2)]
  have e : 1 / (2 * h) * (2 * h * (∫ t in Icc (φ - π) (φ + π), f t * P t)) =
      ∫ t in Icc (φ - π) (φ + π), f t * P t := by
    field_simp
  have e2 : 1 / (2 * h) * (2 * h * (δ * ∫ t in Icc (φ - π) (φ + π), |f t|)) =
      δ * ∫ t in Icc (φ - π) (φ + π), |f t| := by
    field_simp
  have hpos : 0 < 1 / (2 * h) := by positivity
  have := mul_le_mul_of_nonneg_left hDi hpos.le
  rw [mul_sub, e, e2] at this
  linarith

/-- P4.4 helper (w4): Lipschitz bound of the Poisson kernel in the angle. -/
theorem s07d_p4_jn_lipt {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (u v : ℝ) :
    |(1 - ρ ^ 2) / (1 - 2 * ρ * Real.cos u + ρ ^ 2) -
      (1 - ρ ^ 2) / (1 - 2 * ρ * Real.cos v + ρ ^ 2)| ≤ 4 * |u - v| / (1 - ρ) ^ 3 := by
  have hd1 := s07d_p4_core_den hρ0 u
  have hd2 := s07d_p4_core_den hρ0 v
  have hp1 := s07d_p4_core_den_pos hρ0 hρ1 u
  have hp2 := s07d_p4_core_den_pos hρ0 hρ1 v
  have h1r : 0 < 1 - ρ := by linarith
  have e : (1 - ρ ^ 2) / (1 - 2 * ρ * Real.cos u + ρ ^ 2) -
      (1 - ρ ^ 2) / (1 - 2 * ρ * Real.cos v + ρ ^ 2) =
      (1 - ρ ^ 2) * (2 * ρ) * (Real.cos u - Real.cos v) /
        ((1 - 2 * ρ * Real.cos u + ρ ^ 2) * (1 - 2 * ρ * Real.cos v + ρ ^ 2)) := by
    have hq1 := hp1.ne'
    have hq2 := hp2.ne'
    rw [div_sub_div _ _ hq1 hq2]
    congr 1
    ring
  rw [e, abs_div, abs_mul, abs_mul, abs_of_nonneg (by nlinarith : 0 ≤ 1 - ρ ^ 2),
    abs_of_nonneg (by linarith : 0 ≤ 2 * ρ), abs_of_pos (mul_pos hp1 hp2)]
  have hc := Real.abs_cos_sub_cos_le u v
  have hden : (1 - ρ) ^ 2 * (1 - ρ) ^ 2 ≤
      (1 - 2 * ρ * Real.cos u + ρ ^ 2) * (1 - 2 * ρ * Real.cos v + ρ ^ 2) :=
    mul_le_mul hd1 hd2 (by positivity) hp1.le
  rw [div_le_div_iff₀ (mul_pos hp1 hp2) (by positivity)]
  have hnum : (1 - ρ ^ 2) * (2 * ρ) * |Real.cos u - Real.cos v| ≤ 4 * (1 - ρ) * |u - v| := by
    have h2 : (1 - ρ ^ 2) * (2 * ρ) ≤ 4 * (1 - ρ) := by nlinarith
    calc (1 - ρ ^ 2) * (2 * ρ) * |Real.cos u - Real.cos v|
        ≤ (1 - ρ ^ 2) * (2 * ρ) * |u - v| :=
          mul_le_mul_of_nonneg_left hc (by nlinarith)
      _ ≤ 4 * (1 - ρ) * |u - v| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  have hab := abs_nonneg (u - v)
  calc (1 - ρ ^ 2) * (2 * ρ) * |Real.cos u - Real.cos v| * (1 - ρ) ^ 3
      ≤ 4 * (1 - ρ) * |u - v| * (1 - ρ) ^ 3 :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = 4 * |u - v| * ((1 - ρ) ^ 2 * (1 - ρ) ^ 2) := by ring
    _ ≤ 4 * |u - v| * ((1 - 2 * ρ * Real.cos u + ρ ^ 2) * (1 - 2 * ρ * Real.cos v + ρ ^ 2)) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

/-- P4.4 helper (w4): Lipschitz bound of the Poisson kernel in the radius. -/
theorem s07d_p4_jn_lipr {ρ₁ ρ₂ m : ℝ} (h10 : 0 ≤ ρ₁) (h20 : 0 ≤ ρ₂) (h1m : ρ₁ ≤ m) (h2m : ρ₂ ≤ m)
    (hm : m < 1) (u : ℝ) :
    |(1 - ρ₁ ^ 2) / (1 - 2 * ρ₁ * Real.cos u + ρ₁ ^ 2) -
      (1 - ρ₂ ^ 2) / (1 - 2 * ρ₂ * Real.cos u + ρ₂ ^ 2)| ≤ 8 * |ρ₁ - ρ₂| / (1 - m) ^ 4 := by
  have hd1 := s07d_p4_core_den h10 u
  have hd2 := s07d_p4_core_den h20 u
  have hp1 := s07d_p4_core_den_pos h10 (lt_of_le_of_lt h1m hm) u
  have hp2 := s07d_p4_core_den_pos h20 (lt_of_le_of_lt h2m hm) u
  have h1m' : 0 < 1 - m := by linarith
  have e : (1 - ρ₁ ^ 2) / (1 - 2 * ρ₁ * Real.cos u + ρ₁ ^ 2) -
      (1 - ρ₂ ^ 2) / (1 - 2 * ρ₂ * Real.cos u + ρ₂ ^ 2) =
      2 * (ρ₁ - ρ₂) * (Real.cos u * (1 + ρ₁ * ρ₂) - (ρ₁ + ρ₂)) /
        ((1 - 2 * ρ₁ * Real.cos u + ρ₁ ^ 2) * (1 - 2 * ρ₂ * Real.cos u + ρ₂ ^ 2)) := by
    have hq1 := hp1.ne'
    have hq2 := hp2.ne'
    rw [div_sub_div _ _ hq1 hq2]
    congr 1
    ring
  have hc1 := Real.cos_le_one u
  have hc2 := Real.neg_one_le_cos u
  have hq : |Real.cos u * (1 + ρ₁ * ρ₂) - (ρ₁ + ρ₂)| ≤ 4 := by
    rw [abs_le]
    have hm1 : ρ₁ * ρ₂ ≤ 1 := by nlinarith
    constructor <;> nlinarith [mul_nonneg h10 h20]
  have hA : (1 - m) ^ 2 ≤ 1 - 2 * ρ₁ * Real.cos u + ρ₁ ^ 2 :=
    le_trans (pow_le_pow_left₀ h1m'.le (by linarith) 2) hd1
  have hB : (1 - m) ^ 2 ≤ 1 - 2 * ρ₂ * Real.cos u + ρ₂ ^ 2 :=
    le_trans (pow_le_pow_left₀ h1m'.le (by linarith) 2) hd2
  have hden : (1 - m) ^ 4 ≤
      (1 - 2 * ρ₁ * Real.cos u + ρ₁ ^ 2) * (1 - 2 * ρ₂ * Real.cos u + ρ₂ ^ 2) := by
    have := mul_le_mul hA hB (by positivity) hp1.le
    nlinarith
  rw [e, abs_div, abs_of_pos (mul_pos hp1 hp2), abs_mul, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [div_le_div_iff₀ (mul_pos hp1 hp2) (by positivity)]
  have hab := abs_nonneg (ρ₁ - ρ₂)
  calc 2 * |ρ₁ - ρ₂| * |Real.cos u * (1 + ρ₁ * ρ₂) - (ρ₁ + ρ₂)| * (1 - m) ^ 4
      ≤ 2 * |ρ₁ - ρ₂| * 4 * (1 - m) ^ 4 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by positivity)) (by positivity)
    _ = 8 * |ρ₁ - ρ₂| * (1 - m) ^ 4 := by ring
    _ ≤ 8 * |ρ₁ - ρ₂| * ((1 - 2 * ρ₁ * Real.cos u + ρ₁ ^ 2) *
          (1 - 2 * ρ₂ * Real.cos u + ρ₂ ^ 2)) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

/-- P4.4 helper (w4): `log (c A + τ) ≤ log (max c 1) + log (A + τ)`. -/
theorem s07d_p4_jn_logc {c A τ : ℝ} (hc : 0 ≤ c) (hA : 0 ≤ A) (hτ : 0 < τ) :
    Real.log (c * A + τ) ≤ Real.log (max c 1) + Real.log (A + τ) := by
  have hm : 0 < max c 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  rw [← Real.log_mul hm.ne' (by linarith)]
  apply Real.log_le_log (by positivity)
  have h1 : c * A ≤ max c 1 * A := mul_le_mul_of_nonneg_right (le_max_left _ _) hA
  have h2 : τ ≤ max c 1 * τ := le_mul_of_one_le_left hτ.le (le_max_right _ _)
  nlinarith

/-- P4.4 helper (w4): window integrals as interval integrals. -/
theorem s07d_p4_jn_conv (F : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Icc a b, F t = ∫ t in a..b, F t := by
  rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

/-- P4.4 helper (w4): concavity of `log` on an arc of length `2h` (tangent-line form) plus the
Whitney bound: the arc average of `log (F + τ)` is `≤ log max(3C, 1) + log (ν(3I)/|3I| + τ)`. -/
theorem s07d_p4_jn_avg {F : ℝ → ℝ} {ν : Measure ℝ} {C h θ τ : ℝ} (hFc : Continuous F)
    (hF0 : ∀ t, 0 ≤ F t) (hC : 0 < C) (hfin : ∀ a b : ℝ, ν (Icc a b) ≠ ⊤)
    (hWh : ENNReal.ofReal (∫ t in (θ - h)..(θ + h), F t) ≤
      ENNReal.ofReal C * ν (Icc ((θ - h) - ((θ + h) - (θ - h))) ((θ + h) + ((θ + h) - (θ - h)))))
    (hh : 0 < h) (hτ : 0 < τ) :
    1 / (2 * h) * ∫ x in Icc (-h) h, Real.log (F (θ + x) + τ) ≤
      Real.log (max (3 * C) 1) +
        Real.log ((ν (Icc (θ - 3 * h) (θ + 3 * h))).toReal / (2 * (3 * h)) + τ) := by
  set V := (ν (Icc (θ - 3 * h) (θ + 3 * h))).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have e1 : (θ - h) - ((θ + h) - (θ - h)) = θ - 3 * h := by ring
  have e2 : (θ + h) + ((θ + h) - (θ - h)) = θ + 3 * h := by ring
  rw [e1, e2, ← s07d_p4_jn_conv F (by linarith)] at hWh
  set I := ∫ t in Icc (θ - h) (θ + h), F t with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Icc fun t _ => hF0 t
  have hIV : I ≤ C * V := by
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin _ _)) hWh
    rwa [ENNReal.toReal_ofReal hI0, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le] at h1
  -- change of variables
  have hcv : ∫ x in Icc (-h) h, Real.log (F (θ + x) + τ) =
      ∫ t in Icc (θ - h) (θ + h), Real.log (F t + τ) := by
    rw [s07d_p4_jn_conv _ (by linarith), s07d_p4_jn_conv _ (by linarith),
      intervalIntegral.integral_comp_add_left (fun t => Real.log (F t + τ)) θ]
    congr 1 <;> ring
  rw [hcv]
  set m := I / (2 * h) + τ with hm
  have hm0 : 0 < m := by positivity
  have hFi : IntegrableOn F (Icc (θ - h) (θ + h)) volume := hFc.integrableOn_Icc
  have hvol : volume (Icc (θ - h) (θ + h)) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hvr : volume.real (Icc (θ - h) (θ + h)) = 2 * h := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hcst : IntegrableOn (fun _ : ℝ => Real.log m - 1 + τ / m) (Icc (θ - h) (θ + h)) volume :=
    integrableOn_const hvol
  have hR : IntegrableOn (fun t => Real.log m - 1 + τ / m + F t / m) (Icc (θ - h) (θ + h))
      volume := hcst.add (hFi.div_const m)
  have hL : IntegrableOn (fun t => Real.log (F t + τ)) (Icc (θ - h) (θ + h)) volume :=
    ((hFc.add continuous_const).log fun t => (show (0 : ℝ) < F t + τ by linarith [hF0 t]).ne').integrableOn_Icc
  have hptw : ∀ t ∈ Icc (θ - h) (θ + h),
      Real.log (F t + τ) ≤ Real.log m - 1 + τ / m + F t / m := fun t _ => by
    have h1 := s07d_p4_core_tangent (by linarith [hF0 t] : 0 < F t + τ) hm0
    have e : (F t + τ) / m = F t / m + τ / m := add_div _ _ _
    linarith
  have h1 := setIntegral_mono_on hL hR measurableSet_Icc hptw
  rw [integral_add hcst (hFi.div_const m), setIntegral_const, smul_eq_mul, hvr,
    integral_div] at h1
  have hmI : I = 2 * h * (m - τ) := by
    rw [hm]
    field_simp
    ring
  have key : 2 * h * (Real.log m - 1 + τ / m) + I / m = 2 * h * Real.log m := by
    rw [hmI]
    field_simp
    ring
  rw [key] at h1
  have h2 : 1 / (2 * h) * ∫ t in Icc (θ - h) (θ + h), Real.log (F t + τ) ≤ Real.log m := by
    have hp : 0 < 1 / (2 * h) := by positivity
    have := mul_le_mul_of_nonneg_left h1 hp.le
    have e : 1 / (2 * h) * (2 * h * Real.log m) = Real.log m := by field_simp
    linarith
  have h3 : Real.log m ≤ Real.log (C * V / (2 * h) + τ) := by
    apply Real.log_le_log hm0
    have : I / (2 * h) ≤ C * V / (2 * h) := div_le_div_of_nonneg_right hIV (by linarith)
    linarith
  have e3 : C * V / (2 * h) = 3 * C * (V / (2 * (3 * h))) := by
    field_simp
  rw [e3] at h3
  have h4 := s07d_p4_jn_logc (c := 3 * C) (A := V / (2 * (3 * h))) (by linarith)
    (by positivity) hτ
  linarith

/-- P4.4 helper (w4): `L¹` bound for `log (F + τ)` on the window from the Whitney bound of the
whole window. -/
theorem s07d_p4_jn_L1f {F : ℝ → ℝ} {ν : Measure ℝ} {C φ τ : ℝ} (hFc : Continuous F)
    (hF0 : ∀ t, 0 ≤ F t) (hC : 0 < C) (hfin : ∀ a b : ℝ, ν (Icc a b) ≠ ⊤)
    (hWh : ENNReal.ofReal (∫ t in (φ - π)..(φ + π), F t) ≤
      ENNReal.ofReal C * ν (Icc ((φ - π) - ((φ + π) - (φ - π))) ((φ + π) + ((φ + π) - (φ - π)))))
    (hτ : 0 < τ) :
    ∫ t in Icc (φ - π) (φ + π), |Real.log (F t + τ)| ≤
      2 * π * (|Real.log τ| + τ) + C * (ν (Icc (φ - 3 * π) (φ + 3 * π))).toReal := by
  have hpi := Real.pi_pos
  have e1 : (φ - π) - ((φ + π) - (φ - π)) = φ - 3 * π := by ring
  have e2 : (φ + π) + ((φ + π) - (φ - π)) = φ + 3 * π := by ring
  rw [e1, e2, ← s07d_p4_jn_conv F (by linarith)] at hWh
  have hI0 : 0 ≤ ∫ t in Icc (φ - π) (φ + π), F t :=
    setIntegral_nonneg measurableSet_Icc fun t _ => hF0 t
  have hIV : (∫ t in Icc (φ - π) (φ + π), F t) ≤
      C * (ν (Icc (φ - 3 * π) (φ + 3 * π))).toReal := by
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin _ _)) hWh
    rwa [ENNReal.toReal_ofReal hI0, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le] at h1
  have hvol : volume (Icc (φ - π) (φ + π)) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hvr : volume.real (Icc (φ - π) (φ + π)) = 2 * π := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hFi : IntegrableOn F (Icc (φ - π) (φ + π)) volume := hFc.integrableOn_Icc
  have hcst : IntegrableOn (fun _ : ℝ => |Real.log τ| + τ) (Icc (φ - π) (φ + π)) volume :=
    integrableOn_const hvol
  have hL : IntegrableOn (fun t => |Real.log (F t + τ)|) (Icc (φ - π) (φ + π)) volume :=
    ((hFc.add continuous_const).log fun t => (show (0 : ℝ) < F t + τ by linarith [hF0 t]).ne').abs.integrableOn_Icc
  have hR : IntegrableOn (fun t => |Real.log τ| + τ + F t) (Icc (φ - π) (φ + π)) volume :=
    hcst.add hFi
  have h1 := setIntegral_mono_on hL hR measurableSet_Icc fun t _ => by
    have := s07d_p4_core_abs_log hτ (by linarith [hF0 t] : τ ≤ F t + τ)
    show |Real.log (F t + τ)| ≤ |Real.log τ| + τ + F t
    linarith
  rw [integral_add hcst hFi, setIntegral_const, smul_eq_mul, hvr] at h1
  linarith

/-- P4.4 helper (w4): `L¹` bound for `log (A_{h'} + τ)` on the window, `0 < h' ≤ 1`. -/
theorem s07d_p4_jn_L1A {ν : Measure ℝ} (hfin : ∀ a b : ℝ, ν (Icc a b) ≠ ⊤) {h' φ τ : ℝ}
    (hh : 0 < h') (hh1 : h' ≤ 1) (hτ : 0 < τ) :
    IntegrableOn (fun t => |Real.log ((ν (Icc (t - h') (t + h'))).toReal / (2 * h') + τ)|)
      (Icc (φ - π) (φ + π)) volume ∧
    ∫ t in Icc (φ - π) (φ + π), |Real.log ((ν (Icc (t - h') (t + h'))).toReal / (2 * h') + τ)| ≤
      2 * π * (|Real.log τ| + τ) + (ν (Icc (φ - π - 1) (φ + π + 1))).toReal := by
  have hpi := Real.pi_pos
  obtain ⟨hνi, hνb⟩ := s07d_p4_jl_fubR hfin (a := φ - π) (b := φ + π) hh hh1
  have hvol : volume (Icc (φ - π) (φ + π)) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hvr : volume.real (Icc (φ - π) (φ + π)) = 2 * π := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hA0 : ∀ t, 0 ≤ (ν (Icc (t - h') (t + h'))).toReal / (2 * h') := fun t =>
    div_nonneg ENNReal.toReal_nonneg (by linarith)
  have hAi : IntegrableOn (fun t => (ν (Icc (t - h') (t + h'))).toReal / (2 * h'))
      (Icc (φ - π) (φ + π)) volume := hνi.div_const _
  have hAm : AEStronglyMeasurable (fun t => (ν (Icc (t - h') (t + h'))).toReal / (2 * h'))
      (volume.restrict (Icc (φ - π) (φ + π))) :=
    ((s07d_p4_jl_meas hfin (φ - π) (φ + π) h' hh.le).aemeasurable.div_const
      _).aestronglyMeasurable
  have hcst : IntegrableOn (fun _ : ℝ => |Real.log τ| + τ) (Icc (φ - π) (φ + π)) volume :=
    integrableOn_const hvol
  have hR : IntegrableOn (fun t => |Real.log τ| + τ +
      (ν (Icc (t - h') (t + h'))).toReal / (2 * h')) (Icc (φ - π) (φ + π)) volume :=
    hcst.add hAi
  have hφm : Measurable fun y : ℝ => |Real.log (y + τ)| := by fun_prop
  have hpt : ∀ t, |Real.log ((ν (Icc (t - h') (t + h'))).toReal / (2 * h') + τ)| ≤
      |Real.log τ| + τ + (ν (Icc (t - h') (t + h'))).toReal / (2 * h') := fun t => by
    have := s07d_p4_core_abs_log hτ (by linarith [hA0 t] :
      τ ≤ (ν (Icc (t - h') (t + h'))).toReal / (2 * h') + τ)
    linarith
  have hLi : IntegrableOn
      (fun t => |Real.log ((ν (Icc (t - h') (t + h'))).toReal / (2 * h') + τ)|)
      (Icc (φ - π) (φ + π)) volume := by
    refine Integrable.mono' hR
      (hφm.comp_aemeasurable hAm.aemeasurable).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, abs_abs]
    exact hpt t
  refine ⟨hLi, ?_⟩
  have h1 := setIntegral_mono_on hLi hR measurableSet_Icc fun t _ => hpt t
  rw [integral_add hcst hAi, setIntegral_const, smul_eq_mul, hvr, integral_div] at h1
  have h2 : (∫ t in Icc (φ - π) (φ + π), (ν (Icc (t - h') (t + h'))).toReal) / (2 * h') ≤
      (ν (Icc (φ - π - 1) (φ + π + 1))).toReal := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  linarith

/-- P4.4 helper (w4): steps 2–3 — `log F ≤ log (F + τ)`, then the moving-average swap. -/
theorem s07d_p4_jn_A {F K : ℝ → ℝ} {h φ τ δ : ℝ} (hFc : Continuous F) (hFpos : ∀ t, 0 < F t)
    (hFp : Function.Periodic F (2 * π)) (hKc : Continuous K) (hK0 : ∀ t, 0 ≤ K t)
    (hKp : Function.Periodic K (2 * π)) (hh : 0 < h) (hτ : 0 < τ)
    (hδ : ∀ t x, x ∈ Icc (-h) h → |K t - K (t - x)| ≤ δ) :
    ∫ t in Icc (φ - π) (φ + π), Real.log (F t) * K t ≤
      (∫ t in Icc (φ - π) (φ + π),
        (1 / (2 * h) * ∫ x in Icc (-h) h, Real.log (F (t + x) + τ)) * K t) +
        δ * ∫ t in Icc (φ - π) (φ + π), |Real.log (F t + τ)| := by
  have hfc : Continuous fun t => Real.log (F t + τ) :=
    (hFc.add continuous_const).log fun t =>
      (show (0 : ℝ) < F t + τ by linarith [hFpos t]).ne'
  have hfp : Function.Periodic (fun t => Real.log (F t + τ)) (2 * π) := fun t => by
    show Real.log (F (t + 2 * π) + τ) = Real.log (F t + τ)
    rw [hFp t]
  have hsw := s07d_p4_jn_swap (φ := φ) hKc hfc hKp hfp hh hδ
  have hle : ∫ t in Icc (φ - π) (φ + π), Real.log (F t) * K t ≤
      ∫ t in Icc (φ - π) (φ + π), Real.log (F t + τ) * K t := by
    refine setIntegral_mono_on ((hFc.log fun t => (hFpos t).ne').mul hKc).integrableOn_Icc
      (hfc.mul hKc).integrableOn_Icc measurableSet_Icc fun t _ => ?_
    exact mul_le_mul_of_nonneg_right
      (Real.log_le_log (hFpos t) (by linarith)) (hK0 t)
  linarith

/-- P4.4 helper (w4): steps 4–5 — arc-average bound and switch of the kernel `K → Kr`. -/
theorem s07d_p4_jn_B {F K Kr : ℝ → ℝ} {ν : Measure ℝ} {C h φ τ δ₂ Pm : ℝ}
    (hFc : Continuous F) (hF0 : ∀ t, 0 ≤ F t) (hfin : ∀ a b : ℝ, ν (Icc a b) ≠ ⊤)
    (hWh : ∀ θ : ℝ, ENNReal.ofReal (∫ t in (θ - h)..(θ + h), F t) ≤
      ENNReal.ofReal C * ν (Icc ((θ - h) - ((θ + h) - (θ - h))) ((θ + h) + ((θ + h) - (θ - h)))))
    (hh : 0 < h) (hh1 : 3 * h ≤ 1) (hτ : 0 < τ) (hC : 0 < C)
    (hKc : Continuous K) (hK0 : ∀ t, 0 ≤ K t) (hKm : ∫ t in Icc (φ - π) (φ + π), K t = 2 * π)
    (hKrc : Continuous Kr) (hPm : ∀ t ∈ Icc (φ - π) (φ + π), |K t| ≤ Pm ∧ |Kr t| ≤ Pm)
    (hδ : ∀ t, |K t - Kr t| ≤ δ₂) :
    (∫ t in Icc (φ - π) (φ + π),
        (1 / (2 * h) * ∫ x in Icc (-h) h, Real.log (F (t + x) + τ)) * K t) ≤
      2 * π * Real.log (max (3 * C) 1) +
        (∫ t in Icc (φ - π) (φ + π),
          Real.log ((ν (Icc (t - 3 * h) (t + 3 * h))).toReal / (2 * (3 * h)) + τ) * Kr t) +
        δ₂ * ∫ t in Icc (φ - π) (φ + π),
          |Real.log ((ν (Icc (t - 3 * h) (t + 3 * h))).toReal / (2 * (3 * h)) + τ)| := by
  have h3 : 0 < 3 * h := by linarith
  have hMc : Continuous fun t => 1 / (2 * h) * ∫ x in Icc (-h) h, Real.log (F (t + x) + τ) :=
    continuous_const.mul (continuous_parametric_integral_of_continuous
      (f := fun (t x : ℝ) => Real.log (F (t + x) + τ))
      (((hFc.comp (continuous_fst.add continuous_snd)).add continuous_const).log
        fun p => (show (0 : ℝ) < F (p.1 + p.2) + τ by linarith [hF0 (p.1 + p.2)]).ne')
      isCompact_Icc)
  have hAm : AEStronglyMeasurable
      (fun t => (ν (Icc (t - 3 * h) (t + 3 * h))).toReal / (2 * (3 * h)))
      (volume.restrict (Icc (φ - π) (φ + π))) :=
    ((s07d_p4_jl_meas hfin (φ - π) (φ + π) (3 * h) h3.le).aemeasurable.div_const
      _).aestronglyMeasurable
  have hA0 : ∀ t, 0 ≤ (ν (Icc (t - 3 * h) (t + 3 * h))).toReal / (2 * (3 * h)) := fun t =>
    div_nonneg ENNReal.toReal_nonneg (by linarith)
  have hAi : IntegrableOn (fun t => (ν (Icc (t - 3 * h) (t + 3 * h))).toReal / (2 * (3 * h)))
      (Icc (φ - π) (φ + π)) volume :=
    (s07d_p4_jl_fubR hfin (a := φ - π) (b := φ + π) h3 hh1).1.div_const _
  have iLK := s07d_p4_jl_Lint hAm hA0 hAi hKc hτ fun t ht => (hPm t ht).1
  have iLKr := s07d_p4_jl_Lint hAm hA0 hAi hKrc hτ fun t ht => (hPm t ht).2
  have iLa := (s07d_p4_jn_L1A hfin (φ := φ) h3 hh1 hτ).1
  have iK : IntegrableOn K (Icc (φ - π) (φ + π)) volume := hKc.integrableOn_Icc
  have iC : IntegrableOn (fun t => Real.log (max (3 * C) 1) * K t) (Icc (φ - π) (φ + π))
      volume := iK.const_mul _
  have iS : IntegrableOn (fun t => Real.log (max (3 * C) 1) * K t +
      Real.log ((ν (Icc (t - 3 * h) (t + 3 * h))).toReal / (2 * (3 * h)) + τ) * K t)
      (Icc (φ - π) (φ + π)) volume := iC.add iLK
  have iMK : IntegrableOn (fun t =>
      (1 / (2 * h) * ∫ x in Icc (-h) h, Real.log (F (t + x) + τ)) * K t)
      (Icc (φ - π) (φ + π)) volume := (hMc.mul hKc).integrableOn_Icc
  have s4 := setIntegral_mono_on iMK iS measurableSet_Icc
    fun t _ => by
      have := s07d_p4_jn_avg (θ := t) hFc hF0 hC hfin (hWh t) hh hτ
      show (1 / (2 * h) * ∫ x in Icc (-h) h, Real.log (F (t + x) + τ)) * K t ≤
        Real.log (max (3 * C) 1) * K t +
          Real.log ((ν (Icc (t - 3 * h) (t + 3 * h))).toReal / (2 * (3 * h)) + τ) * K t
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right this (hK0 t)
  rw [integral_add iC iLK, integral_const_mul, hKm] at s4
  have iT : IntegrableOn (fun t =>
      Real.log ((ν (Icc (t - 3 * h) (t + 3 * h))).toReal / (2 * (3 * h)) + τ) * Kr t +
      δ₂ * |Real.log ((ν (Icc (t - 3 * h) (t + 3 * h))).toReal / (2 * (3 * h)) + τ)|)
      (Icc (φ - π) (φ + π)) volume := iLKr.add (iLa.const_mul _)
  have s5 := setIntegral_mono_on iLK iT measurableSet_Icc fun t _ => by
    show Real.log ((ν (Icc (t - 3 * h) (t + 3 * h))).toReal / (2 * (3 * h)) + τ) * K t ≤
      Real.log ((ν (Icc (t - 3 * h) (t + 3 * h))).toReal / (2 * (3 * h)) + τ) * Kr t +
        δ₂ * |Real.log ((ν (Icc (t - 3 * h) (t + 3 * h))).toReal / (2 * (3 * h)) + τ)|
    have h1 := abs_mul (Real.log ((ν (Icc (t - 3 * h) (t + 3 * h))).toReal / (2 * (3 * h)) + τ))
      (K t - Kr t)
    have h2 := le_abs_self (Real.log ((ν (Icc (t - 3 * h) (t + 3 * h))).toReal /
      (2 * (3 * h)) + τ) * (K t - Kr t))
    have h3 := mul_le_mul_of_nonneg_left (hδ t)
      (abs_nonneg (Real.log ((ν (Icc (t - 3 * h) (t + 3 * h))).toReal / (2 * (3 * h)) + τ)))
    have e : Real.log ((ν (Icc (t - 3 * h) (t + 3 * h))).toReal / (2 * (3 * h)) + τ) * K t =
        Real.log ((ν (Icc (t - 3 * h) (t + 3 * h))).toReal / (2 * (3 * h)) + τ) * Kr t +
        Real.log ((ν (Icc (t - 3 * h) (t + 3 * h))).toReal / (2 * (3 * h)) + τ) *
          (K t - Kr t) := by ring
    linarith
  rw [integral_add iLKr (iLa.const_mul _), integral_const_mul] at s5
  linarith

/-- P4.4 helper (w4): facts about the radius `ρ = r/(1-h)` for `0 < h < (1-r)/4`. -/
theorem s07d_p4_jn_rho {r h : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hh0 : 0 < h)
    (hh : h < (1 - r) / 4) :
    r < 1 - h ∧ 0 ≤ r / (1 - h) ∧ r / (1 - h) ≤ (1 + r) / 2 ∧ |r / (1 - h) - r| ≤ 2 * h := by
  have hs : 3 / 4 < 1 - h := by linarith
  have hs0 : 0 < 1 - h := by linarith
  refine ⟨by linarith, div_nonneg hr0 hs0.le, ?_, ?_⟩
  · rw [div_le_iff₀ hs0]
    nlinarith
  · have e : r / (1 - h) - r = r * h / (1 - h) := by
      field_simp
      ring
    rw [e, abs_of_nonneg (by positivity), div_le_iff₀ hs0]
    nlinarith

/-- P4.4 helper (w4): the final arithmetic of the `ε`-argument. -/
theorem s07d_p4_jn_arith {X0 X5 C₀ ε h r B1 B2 δ₁ δ₂ I1 I2 : ℝ} (hε : 0 < ε) (hh : 0 < h)
    (hr1 : r < 1) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hX : X0 ≤ 2 * π * C₀ + (X5 + π * ε) + δ₂ * I2 + δ₁ * I1)
    (hI1 : I1 ≤ B1) (hI2 : I2 ≤ B2) (hδ₁0 : 0 ≤ δ₁) (hδ₂0 : 0 ≤ δ₂)
    (hδ₁ : δ₁ ≤ 32 * h / (1 - r) ^ 3) (hδ₂ : δ₂ ≤ 256 * h / (1 - r) ^ 4)
    (hhQ : h < π * ε / (32 * B1 / (1 - r) ^ 3 + 256 * B2 / (1 - r) ^ 4 + 1)) :
    (1 / (2 * π)) * X0 ≤ C₀ + (1 / (2 * π)) * X5 + ε := by
  have hpi := Real.pi_pos
  have h1r : 0 < 1 - r := by linarith
  set Q := 32 * B1 / (1 - r) ^ 3 + 256 * B2 / (1 - r) ^ 4 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have t1 : δ₁ * I1 ≤ 32 * h / (1 - r) ^ 3 * B1 :=
    (mul_le_mul_of_nonneg_left hI1 hδ₁0).trans (mul_le_mul_of_nonneg_right hδ₁ hB1)
  have t2 : δ₂ * I2 ≤ 256 * h / (1 - r) ^ 4 * B2 :=
    (mul_le_mul_of_nonneg_left hI2 hδ₂0).trans (mul_le_mul_of_nonneg_right hδ₂ hB2)
  have e : 32 * h / (1 - r) ^ 3 * B1 + 256 * h / (1 - r) ^ 4 * B2 = h * Q := by
    rw [hQ]
    ring
  have t3 : h * Q ≤ π * ε := by
    have h2 : h * (Q + 1) < π * ε := (lt_div_iff₀ (by positivity)).1 hhQ
    nlinarith
  have hS : X0 ≤ 2 * π * C₀ + X5 + 2 * π * ε := by linarith
  have h4 := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ 1 / (2 * π))
  have e2 : 1 / (2 * π) * (2 * π * C₀ + X5 + 2 * π * ε) = C₀ + 1 / (2 * π) * X5 + ε := by
    field_simp
  linarith

/-- P4.4 helper (w4): the `ε`-form of `jensen` at a fixed point `r e^{iφ}`. -/
theorem s07d_p4_jn_eps {g : ℂ → ℂ} {ν : Measure ℝ} {C r φ τ ε : ℝ} (hC : 0 < C)
    (hg : DifferentiableOn ℂ g unitDisc) (hg0 : ∀ z ∈ unitDisc, g z ≠ 0)
    (hfin : ∀ a b : ℝ, ν (Icc a b) ≠ ⊤)
    (hWh : ∀ a b r : ℝ, a < b → b - a ≤ 2 * π → 0 ≤ r → 1 - (b - a) ≤ r → r < 1 →
      ENNReal.ofReal (∫ t in a..b, ‖g ((r : ℂ) * Complex.exp (t * Complex.I))‖) ≤
        ENNReal.ofReal C * ν (Icc (a - (b - a)) (b + (b - a))))
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hτ : 0 < τ) (hε : 0 < ε) :
    Real.log ‖g ((r : ℂ) * Complex.exp (φ * Complex.I))‖ ≤
      Real.log (max (3 * C) 1) + (1 / (2 * π)) * (∫ t in Icc (φ - π) (φ + π),
        Real.log ((ν.rnDeriv volume t).toReal + τ) *
          ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2))) + ε := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have h1r : 0 < 1 - r := by linarith
  -- the kernel at `r`
  obtain ⟨Kr, hKr⟩ : ∃ K : ℝ → ℝ,
      K = fun t => (1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2) := ⟨_, rfl⟩
  have hKrc : Continuous Kr := by
    rw [hKr]
    exact continuous_const.div (by fun_prop) fun t => (s07d_p4_core_den_pos hr0 hr1 _).ne'
  have hKr0 : ∀ t, 0 ≤ Kr t := fun t => by
    rw [hKr]
    exact s07d_p4_core_k_nonneg hr0 hr1 _
  -- constants
  set B1 := 2 * π * (|Real.log τ| + τ) + C * (ν (Icc (φ - 3 * π) (φ + 3 * π))).toReal with hB1
  set B2 := 2 * π * (|Real.log τ| + τ) + (ν (Icc (φ - π - 1) (φ + π + 1))).toReal with hB2
  have hB10 : 0 ≤ B1 := by positivity
  have hB20 : 0 ≤ B2 := by positivity
  set h0 := min (min ((1 - r) / 4) (1 / 3))
    (π * ε / (32 * B1 / (1 - r) ^ 3 + 256 * B2 / (1 - r) ^ 4 + 1)) with hh0def
  have hh0 : 0 < h0 := by
    rw [hh0def]
    refine lt_min (lt_min (by linarith) (by norm_num)) ?_
    positivity
  -- the limit step, at scale `3h`
  have hpr := s07d_p4_jl_main hfin (P := Kr) hKrc hKr0 (a := φ - π) (b := φ + π) hτ
    (by positivity : 0 < π * ε)
  have ht3 : Tendsto (fun h : ℝ => 3 * h) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun h : ℝ => 3 * h) (𝓝 0) (𝓝 (3 * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      have hh' : 0 < h := hh
      show 0 < 3 * h
      linarith
  obtain ⟨h, hp3, hhI⟩ := ((ht3.eventually hpr).and (Ioo_mem_nhdsGT hh0)).exists
  have hhpos : 0 < h := hhI.1
  have hhr : h < (1 - r) / 4 := lt_of_lt_of_le hhI.2 ((min_le_left _ _).trans (min_le_left _ _))
  have hh3 : h < 1 / 3 := lt_of_lt_of_le hhI.2 ((min_le_left _ _).trans (min_le_right _ _))
  have hhQ : h < π * ε / (32 * B1 / (1 - r) ^ 3 + 256 * B2 / (1 - r) ^ 4 + 1) :=
    lt_of_lt_of_le hhI.2 (min_le_right _ _)
  obtain ⟨hrs, hρ0, hρm, hρr⟩ := s07d_p4_jn_rho hr0 hr1 hhpos hhr
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 1 - h := ⟨_, rfl⟩
  rw [← hs] at hrs hρ0 hρm hρr
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hs1 : s < 1 := by rw [hs]; linarith
  set ρ := r / s with hρ
  have hρ1 : ρ < 1 := by linarith
  -- the boundary function at radius `s`
  have hmem : ∀ t : ℝ, (s : ℂ) * Complex.exp (t * Complex.I) ∈ unitDisc := fun t => by
    show (s : ℂ) * Complex.exp (t * Complex.I) ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_of_nonneg hs0]
    exact hs1
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ,
      F = fun t : ℝ => ‖g ((s : ℂ) * Complex.exp ((t : ℂ) * Complex.I))‖ :=
    ⟨_, rfl⟩
  have hFc : Continuous F := by
    rw [hF]
    exact (hg.continuousOn.comp_continuous (by fun_prop) hmem).norm
  have hFpos : ∀ t, 0 < F t := fun t => by
    rw [hF]
    exact norm_pos_iff.2 (hg0 _ (hmem t))
  have hFp : Function.Periodic F (2 * π) := fun t => by
    rw [hF]
    show ‖g ((s : ℂ) * Complex.exp (((t + 2 * π : ℝ) : ℂ) * Complex.I))‖ =
      ‖g ((s : ℂ) * Complex.exp (t * Complex.I))‖
    have e : (((t + 2 * π : ℝ) : ℂ) * Complex.I) = (t : ℂ) * Complex.I + 2 * π * Complex.I := by
      push_cast
      ring
    rw [e, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  -- the kernel at `ρ`
  obtain ⟨K, hK⟩ : ∃ K : ℝ → ℝ,
      K = fun t => (1 - ρ ^ 2) / (1 - 2 * ρ * Real.cos (t - φ) + ρ ^ 2) := ⟨_, rfl⟩
  have hKc : Continuous K := by
    rw [hK]
    exact continuous_const.div (by fun_prop) fun t => (s07d_p4_core_den_pos hρ0 hρ1 _).ne'
  have hK0 : ∀ t, 0 ≤ K t := fun t => by
    rw [hK]
    exact s07d_p4_core_k_nonneg hρ0 hρ1 _
  have hKp : Function.Periodic K (2 * π) := fun t => by
    rw [hK]
    show (1 - ρ ^ 2) / (1 - 2 * ρ * Real.cos (t + 2 * π - φ) + ρ ^ 2) =
      (1 - ρ ^ 2) / (1 - 2 * ρ * Real.cos (t - φ) + ρ ^ 2)
    rw [show t + 2 * π - φ = (t - φ) + 2 * π by ring, Real.cos_add_two_pi]
  have hKm : ∫ t in Icc (φ - π) (φ + π), K t = 2 * π := by
    have h := s07d_p4_core_mass hρ0 hρ1 φ
    rw [← s07d_p4_jn_conv _ (by linarith)] at h
    rw [hK]
    field_simp at h
    linarith
  have hδ₁ : ∀ t x, x ∈ Icc (-h) h → |K t - K (t - x)| ≤ 4 * h / (1 - ρ) ^ 3 := by
    intro t x hx
    rw [hK]
    have h1 := s07d_p4_jn_lipt hρ0 hρ1 (t - φ) (t - x - φ)
    have e : (t - φ) - (t - x - φ) = x := by ring
    rw [e] at h1
    have hx' : |x| ≤ h := abs_le.2 ⟨by linarith [hx.1], hx.2⟩
    have h2 : 4 * |x| / (1 - ρ) ^ 3 ≤ 4 * h / (1 - ρ) ^ 3 :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    exact h1.trans h2
  have hPm : ∀ t ∈ Icc (φ - π) (φ + π), |K t| ≤ 2 / (1 - ρ) + 2 / (1 - r) ∧
      |Kr t| ≤ 2 / (1 - ρ) + 2 / (1 - r) := fun t _ => by
    have a1 := s07d_p4_core_k_le hρ0 hρ1 (t - φ)
    have a2 := s07d_p4_core_k_le hr0 hr1 (t - φ)
    have b1 : 0 ≤ 2 / (1 - ρ) := by have : 0 < 1 - ρ := by linarith
                                    positivity
    have b2 : 0 ≤ 2 / (1 - r) := by positivity
    rw [abs_of_nonneg (hK0 t), abs_of_nonneg (hKr0 t), hK, hKr]
    exact ⟨by linarith, by linarith⟩
  have hδ₂ : ∀ t, |K t - Kr t| ≤ 8 * |ρ - r| / (1 - (1 + r) / 2) ^ 4 := fun t => by
    rw [hK, hKr]
    exact s07d_p4_jn_lipr hρ0 hr0 hρm (by linarith) (by linarith) (t - φ)
  -- Whitney bounds for `F`
  have hWhF : ∀ θ : ℝ, ENNReal.ofReal (∫ t in (θ - h)..(θ + h), F t) ≤
      ENNReal.ofReal C * ν (Icc ((θ - h) - ((θ + h) - (θ - h))) ((θ + h) + ((θ + h) - (θ - h)))) :=
    fun θ => by
      have := hWh (θ - h) (θ + h) s (by linarith) (by linarith) hs0 (by rw [hs]; linarith) hs1
      rw [hF]
      exact this
  have hWhW : ENNReal.ofReal (∫ t in (φ - π)..(φ + π), F t) ≤
      ENNReal.ofReal C *
        ν (Icc ((φ - π) - ((φ + π) - (φ - π))) ((φ + π) + ((φ + π) - (φ - π)))) := by
    have := hWh (φ - π) (φ + π) s (by linarith) (by linarith) hs0 (by linarith) hs1
    rw [hF]
    exact this
  -- the chain
  have hP := s07d_p4_jn_poisson (φ := φ) hg hg0 hr0 hrs hs1
  have hX0 : Real.log ‖g ((r : ℂ) * Complex.exp (φ * Complex.I))‖ =
      (1 / (2 * π)) * ∫ t in Icc (φ - π) (φ + π), Real.log (F t) * K t := by
    rw [hP, s07d_p4_jn_conv _ (by linarith), hF, hK]
  have hA := s07d_p4_jn_A (φ := φ) hFc hFpos hFp hKc hK0 hKp hhpos hτ hδ₁
  have hB := s07d_p4_jn_B (φ := φ) hFc (fun t => (hFpos t).le) hfin hWhF hhpos (by linarith)
    hτ hC hKc hK0 hKm hKrc hPm hδ₂
  have hL1f := s07d_p4_jn_L1f hFc (fun t => (hFpos t).le) hC hfin hWhW hτ
  have hL1A := (s07d_p4_jn_L1A hfin (φ := φ) (by linarith : 0 < 3 * h) (by linarith) hτ).2
  have hδ₁b : 4 * h / (1 - ρ) ^ 3 ≤ 32 * h / (1 - r) ^ 3 := by
    have hq : (1 - r) / 2 ≤ 1 - ρ := by linarith
    have hq0 : 0 < (1 - r) / 2 := by linarith
    calc 4 * h / (1 - ρ) ^ 3 ≤ 4 * h / ((1 - r) / 2) ^ 3 :=
          div_le_div_of_nonneg_left (by linarith) (by positivity) (pow_le_pow_left₀ hq0.le hq 3)
      _ = 32 * h / (1 - r) ^ 3 := by field_simp; ring
  have hδ₂b : 8 * |ρ - r| / (1 - (1 + r) / 2) ^ 4 ≤ 256 * h / (1 - r) ^ 4 := by
    have e : (1 - (1 + r) / 2) = (1 - r) / 2 := by ring
    rw [e]
    calc 8 * |ρ - r| / ((1 - r) / 2) ^ 4 ≤ 8 * (2 * h) / ((1 - r) / 2) ^ 4 :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = 256 * h / (1 - r) ^ 4 := by field_simp; ring
  have hKrX : (∫ t in Icc (φ - π) (φ + π), Real.log ((ν.rnDeriv volume t).toReal + τ) * Kr t) =
      ∫ t in Icc (φ - π) (φ + π), Real.log ((ν.rnDeriv volume t).toReal + τ) *
        ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2)) := by
    rw [hKr]
  rw [hX0, ← hKrX]
  have hρ1' : 0 < 1 - ρ := by linarith
  exact s07d_p4_jn_arith hε hhpos hr1 hB10 hB20 (by linarith) hL1f hL1A (by positivity)
    (by positivity) hδ₁b hδ₂b hhQ

/-- **P4.4** (`jensen`): boundary Jensen inequality with an additive constant.  If `g` is
holomorphic and zero-free on `𝔻` and its Whitney integrals are dominated by a locally finite
measure `ν` on `ℝ`, then `log |g(r e^{iφ})| ≤ C₀ + P_r[log(w + τ)](φ)` for every `τ > 0`, where
`w = dν/dθ` (Radon–Nikodym derivative against Lebesgue measure). -/
theorem s07d_p4_jensen {C : ℝ} (hC : 0 < C) :
    ∃ C₀ : ℝ, ∀ (g : ℂ → ℂ) (ν : Measure ℝ), DifferentiableOn ℂ g unitDisc →
      (∀ z ∈ unitDisc, g z ≠ 0) → (∀ a b : ℝ, ν (Icc a b) ≠ ⊤) →
      (∀ a b r : ℝ, a < b → b - a ≤ 2 * π → 0 ≤ r → 1 - (b - a) ≤ r → r < 1 →
        ENNReal.ofReal (∫ t in a..b, ‖g ((r : ℂ) * Complex.exp (t * Complex.I))‖) ≤
          ENNReal.ofReal C * ν (Icc (a - (b - a)) (b + (b - a)))) →
      ∀ r φ τ : ℝ, 0 ≤ r → r < 1 → 0 < τ →
        Real.log ‖g ((r : ℂ) * Complex.exp (φ * Complex.I))‖ ≤
          C₀ + (1 / (2 * π)) * ∫ t in (φ - π)..(φ + π),
            Real.log ((ν.rnDeriv volume t).toReal + τ) *
              ((1 - r ^ 2) / (1 - 2 * r * Real.cos (t - φ) + r ^ 2)) := by
  refine ⟨Real.log (max (3 * C) 1), fun g ν hg hg0 hfin hWh r φ τ hr0 hr1 hτ => ?_⟩
  have hpi := Real.pi_pos
  rw [← s07d_p4_jn_conv _ (by linarith)]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  exact s07d_p4_jn_eps hC hg hg0 hfin hWh hr0 hr1 hτ hε

/-! ## P2, block A (w3): bi-Lipschitz ⇒ q.c. (`s07d_p2_bilip_qc`) and the radial stretch onto a
ball-star-shaped domain (`s07d_p2_kappa`). Frozen interface `P2_STUBS` 4a4493d3. -/

/-- P2.1 helper: at a point of differentiability, a lower Lipschitz bound
`‖w - z‖ ≤ L ‖κ w - κ z‖` passes to the derivative. -/
theorem s07d_p2_bq_lower {κ : ℂ → ℂ} {L : ℝ} {z : ℂ} (hL : 0 < L)
    (hlow : ∀ w : ℂ, ‖w - z‖ ≤ L * ‖κ w - κ z‖) (hd : DifferentiableAt ℝ κ z) (h : ℂ) :
    ‖h‖ ≤ L * ‖fderiv ℝ κ z h‖ := by
  set g : ℝ → ℂ := fun t => κ (z + t • h) with hg
  have hlin : HasDerivAt (fun t : ℝ => z + t • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add z
  have hgd : HasDerivAt g (fderiv ℝ κ z h) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hlin (by simp)
  have hT := (hasDerivAt_iff_tendsto_slope.1 hgd).norm
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖h‖ / L ≤ ‖slope g 0 t‖ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht
    have hb := hlow (z + t • h)
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at hb
    have hta : 0 < |t| := abs_pos.2 ht0
    rw [slope_def_module, norm_smul, sub_zero, norm_inv, Real.norm_eq_abs]
    have e0 : g 0 = κ z := by simp [hg]
    rw [e0, div_le_iff₀ hL]
    rw [inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ hta]
    simp only [hg]
    nlinarith [norm_nonneg h]
  have := ge_of_tendsto hT hev
  rwa [div_le_iff₀ hL, mul_comm] at this

/-- P2.1 helper (algebra of `ℝ`-linear maps of `ℂ`): if `h ↦ a h + b h̄` has norm `≤ L` and minimal
stretch `≥ 1/L`, and `|b| < |a|`, then `|a| + |b| ≤ L² (|a| - |b|)`. -/
theorem s07d_p2_bq_alg (a b : ℂ) (L : ℝ) (hL : 1 ≤ L)
    (hup : ∀ h : ℂ, ‖a * h + b * conj h‖ ≤ L * ‖h‖)
    (hlo : ∀ h : ℂ, ‖h‖ ≤ L * ‖a * h + b * conj h‖) (hab : ‖b‖ < ‖a‖) :
    ‖a‖ + ‖b‖ ≤ L ^ 2 * (‖a‖ - ‖b‖) := by
  by_cases hb : b = 0
  · subst hb
    simp only [norm_zero, sub_zero, add_zero]
    have hL2 : 1 ≤ L ^ 2 := by nlinarith
    nlinarith [norm_nonneg a]
  have ha : a ≠ 0 := norm_pos_iff.1 ((norm_nonneg b).trans_lt hab)
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hnb : 0 < ‖b‖ := norm_pos_iff.2 hb
  set v : ℂ := conj a * b with hv
  have hnv : ‖v‖ = ‖a‖ * ‖b‖ := by rw [hv, norm_mul, Complex.norm_conj]
  set h : ℂ := Complex.exp (((arg v / 2 : ℝ) : ℂ) * I) with hh
  have hh2 : h ^ 2 = Complex.exp ((arg v : ℂ) * I) := by
    rw [hh, sq, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hkey : (‖v‖ : ℂ) * h ^ 2 = v := by rw [hh2]; exact norm_mul_exp_arg_mul_I v
  have hn1 : ‖h‖ = 1 := by rw [hh]; exact Complex.norm_exp_ofReal_mul_I _
  have hc : conj h * h = 1 := by
    rw [Complex.conj_mul', hn1]
    simp
  have hmc : a * conj a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']
    push_cast
    ring
  have hkey' : (‖a‖ : ℂ) * (‖b‖ : ℂ) * h ^ 2 = v := by
    rw [← hkey, hnv]
    push_cast
    ring
  have hmc' : a * conj a = (‖a‖ : ℂ) ^ 2 := by rw [hmc]; push_cast; ring
  -- `h` aligns `a h` and `b h̄`; `h I` opposes them
  have e1 : (‖a‖ : ℂ) * (‖b‖ : ℂ) * (a * h + b * conj h) =
      conj h * (b * ((‖a‖ : ℂ) * ((‖a‖ : ℂ) + (‖b‖ : ℂ)))) := by
    linear_combination (-((‖a‖ : ℂ) * (‖b‖ : ℂ)) * a * h) * hc + (conj h * a) * hkey' +
      (conj h * b) * hmc' + (conj h * a) * hv
  have e2 : (‖a‖ : ℂ) * (‖b‖ : ℂ) * (a * (h * I) + b * conj (h * I)) =
      conj (h * I) * (b * ((‖a‖ : ℂ) * ((‖b‖ : ℂ) - (‖a‖ : ℂ)))) := by
    rw [map_mul, Complex.conj_I]
    linear_combination I * ((-((‖a‖ : ℂ) * (‖b‖ : ℂ)) * a * h) * hc + (conj h * a) * hkey' +
      (conj h * b) * hmc' + (conj h * a) * hv)
  have hab0 : 0 < ‖a‖ * ‖b‖ := mul_pos hna hnb
  have nadd : ‖(‖a‖ : ℂ) + (‖b‖ : ℂ)‖ = ‖a‖ + ‖b‖ := by
    rw [← ofReal_add, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have nsub : ‖(‖b‖ : ℂ) - (‖a‖ : ℂ)‖ = ‖a‖ - ‖b‖ := by
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hnI : ‖h * I‖ = 1 := by rw [norm_mul, hn1, Complex.norm_I, one_mul]
  have n1 := congrArg norm e1
  have n2 := congrArg norm e2
  simp only [norm_mul, Complex.norm_conj, hn1, hnI, Complex.norm_real, norm_norm, nadd, nsub,
    one_mul] at n1 n2
  have hX : ‖a * h + b * conj h‖ = ‖a‖ + ‖b‖ := by
    have : ‖a‖ * ‖b‖ * ‖a * h + b * conj h‖ = ‖a‖ * ‖b‖ * (‖a‖ + ‖b‖) := by rw [n1]; ring
    exact mul_left_cancel₀ hab0.ne' this
  have hY : ‖a * (h * I) + b * conj (h * I)‖ = ‖a‖ - ‖b‖ := by
    have : ‖a‖ * ‖b‖ * ‖a * (h * I) + b * conj (h * I)‖ = ‖a‖ * ‖b‖ * (‖a‖ - ‖b‖) := by
      rw [n2]; ring
    exact mul_left_cancel₀ hab0.ne' this
  have h1 := hup h
  have h2 := hlo (h * I)
  rw [hX, hn1] at h1
  rw [hY, hnI] at h2
  nlinarith

/-- P2.1 (bi-Lipschitz ⇒ q.c.): an `L`-bi-Lipschitz map of `ℂ` onto `ℂ` with `|∂_{z̄} κ| < |∂_z κ|`
at almost every point of differentiability is `L²`-quasiconformal. -/
theorem s07d_p2_bilip_qc (L : ℝ) (hL : 1 ≤ L) (κ : ℂ → ℂ)
    (hκ : ∀ z w : ℂ, ‖z - w‖ ≤ L * ‖κ z - κ w‖ ∧ ‖κ z - κ w‖ ≤ L * ‖z - w‖)
    (hsurj : κ '' univ = univ)
    (hor : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ κ z → ‖dzbar κ z‖ < ‖dz κ z‖) :
    IsKQC κ univ (L ^ 2) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hLip : LipschitzWith (Real.toNNReal L) κ := LipschitzWith.of_dist_le_mul fun z w => by
    rw [Real.coe_toNNReal _ hL0.le, dist_eq_norm, dist_eq_norm]
    exact (hκ z w).2
  have hinj : Function.Injective κ := fun z w he => by
    have h := (hκ z w).1
    rw [he, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h)
  have hg : ∀ y : ℂ, κ (Function.invFunOn κ univ y) = y := fun y => by
    have hy : y ∈ κ '' univ := by rw [hsurj]; exact mem_univ y
    exact Function.invFunOn_eq hy
  have hgLip : LipschitzWith (Real.toNNReal L) (Function.invFunOn κ univ) :=
    LipschitzWith.of_dist_le_mul fun y y' => by
      rw [Real.coe_toNNReal _ hL0.le, dist_eq_norm, dist_eq_norm]
      have h := (hκ (Function.invFunOn κ univ y) (Function.invFunOn κ univ y')).1
      rwa [hg, hg] at h
  have hhom : IsHomeomorphOnto κ univ univ :=
    ⟨hLip.continuous.continuousOn, hinj.injOn, hsurj, hgLip.continuous.continuousOn⟩
  have hK : (1 : ℝ) ≤ L ^ 2 := by nlinarith
  refine (thm10_1_isKQC_iff isOpen_univ hK hhom).2
    ⟨⟨hLip.continuous.continuousOn, fun a b c d _ _ _ =>
      ⟨ae_of_all _ fun x => ?_, ae_of_all _ fun y => ?_⟩⟩, ?_⟩
  · refine LipschitzOnWith.absolutelyContinuousOnInterval (K := Real.toNNReal L)
      (LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun y y' => ?_))
    rw [Real.coe_toNNReal _ hL0.le, dist_eq_norm, Real.dist_eq]
    calc _ ≤ L * ‖((x : ℂ) + (y : ℂ) * I) - ((x : ℂ) + (y' : ℂ) * I)‖ := (hκ _ _).2
      _ = L * |y - y'| := by
        rw [show ((x : ℂ) + (y : ℂ) * I) - ((x : ℂ) + (y' : ℂ) * I) = ((y - y' : ℝ) : ℂ) * I by
          push_cast; ring, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  · refine LipschitzOnWith.absolutelyContinuousOnInterval (K := Real.toNNReal L)
      (LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun x x' => ?_))
    rw [Real.coe_toNNReal _ hL0.le, dist_eq_norm, Real.dist_eq]
    calc _ ≤ L * ‖((x : ℂ) + (y : ℂ) * I) - ((x' : ℂ) + (y : ℂ) * I)‖ := (hκ _ _).2
      _ = L * |x - x'| := by
        rw [show ((x : ℂ) + (y : ℂ) * I) - ((x' : ℂ) + (y : ℂ) * I) = ((x - x' : ℝ) : ℂ) by
          push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
  · filter_upwards [ae_restrict_of_ae (hLip.ae_differentiableAt (μ := volume)),
      ae_restrict_of_ae hor] with z hd ho
    refine s07d_p2_bq_alg (dz κ z) (dzbar κ z) L hL (fun h => ?_) (fun h => ?_) (ho hd)
    · rw [← fderiv_eq_dz_dzbar hd]
      have hn : ‖fderiv ℝ κ z‖ ≤ L := by
        have h := hd.hasFDerivAt.le_of_lipschitz hLip
        rwa [Real.coe_toNNReal _ hL0.le] at h
      calc ‖fderiv ℝ κ z h‖ ≤ ‖fderiv ℝ κ z‖ * ‖h‖ := (fderiv ℝ κ z).le_opNorm h
        _ ≤ L * ‖h‖ := by gcongr
    · rw [← fderiv_eq_dz_dzbar hd]
      exact s07d_p2_bq_lower hL0 (fun w => (hκ w z).1) hd h

/-- P2.2 helper: `|w'| · |w/|w| - w'/|w'|| ≤ 2 |w - w'|`. -/
theorem s07d_p2_rs_unit {w w' : ℂ} (hw : w ≠ 0) (hw' : w' ≠ 0) :
    ‖w'‖ * ‖w / (‖w‖ : ℂ) - w' / (‖w'‖ : ℂ)‖ ≤ 2 * ‖w - w'‖ := by
  have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hw).ne'
  have hn' : (‖w'‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hw').ne'
  have e : (‖w'‖ : ℂ) * (w / (‖w‖ : ℂ) - w' / (‖w'‖ : ℂ)) =
      ((‖w'‖ - ‖w‖ : ℝ) : ℂ) * (w / (‖w‖ : ℂ)) + (w - w') := by
    rw [ofReal_sub]
    field_simp
    ring
  have h1 : ‖w / (‖w‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_pos_iff.2 hw).ne']
  have h2 := abs_norm_sub_norm_le w' w
  rw [norm_sub_rev w' w] at h2
  calc ‖w'‖ * ‖w / (‖w‖ : ℂ) - w' / (‖w'‖ : ℂ)‖
        = ‖(‖w'‖ : ℂ) * (w / (‖w‖ : ℂ) - w' / (‖w'‖ : ℂ))‖ := by
          rw [norm_mul, Complex.norm_real, norm_norm]
    _ = ‖((‖w'‖ - ‖w‖ : ℝ) : ℂ) * (w / (‖w‖ : ℂ)) + (w - w')‖ := by rw [e]
    _ ≤ ‖((‖w'‖ - ‖w‖ : ℝ) : ℂ) * (w / (‖w‖ : ℂ))‖ + ‖w - w'‖ := norm_add_le _ _
    _ = |‖w'‖ - ‖w‖| + ‖w - w'‖ := by
          rw [norm_mul, h1, mul_one, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 2 * ‖w - w'‖ := by linarith

/-- P2.2 helper: a `0`-homogeneous profile takes the same value at `w` and at `w/|w|`. -/
theorem s07d_p2_rs_hn {P : ℂ → ℝ} (hhom : ∀ (w : ℂ) (r : ℝ), 0 < r → P ((r : ℂ) * w) = P w)
    {w : ℂ} (hw : w ≠ 0) : P (w / (‖w‖ : ℂ)) = P w := by
  have e : w / (‖w‖ : ℂ) = ((‖w‖⁻¹ : ℝ) : ℂ) * w := by push_cast; ring
  rw [e, hhom w _ (inv_pos.2 (norm_pos_iff.2 hw))]

/-- P2.2 helper: the radial stretch `w ↦ P(w) w` with a `0`-homogeneous profile `0 ≤ P ≤ M`,
`Λ`-Lipschitz on the circle, is `(M + 2Λ)`-Lipschitz. -/
theorem s07d_p2_rs_lip {P : ℂ → ℝ} {M Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hhom : ∀ (w : ℂ) (r : ℝ), 0 < r → P ((r : ℂ) * w) = P w)
    (hb : ∀ w : ℂ, w ≠ 0 → 0 ≤ P w ∧ P w ≤ M)
    (hlip : ∀ u v : ℂ, ‖u‖ = 1 → ‖v‖ = 1 → |P u - P v| ≤ Λ * ‖u - v‖) (w w' : ℂ) :
    ‖(P w : ℂ) * w - (P w' : ℂ) * w'‖ ≤ (M + 2 * Λ) * ‖w - w'‖ := by
  have hM : 0 ≤ M := (hb 1 one_ne_zero).1.trans (hb 1 one_ne_zero).2
  have hone : ∀ x : ℂ, ‖(P x : ℂ) * x‖ ≤ M * ‖x‖ := fun x => by
    by_cases hx : x = 0
    · subst hx; simp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb x hx).1]
    exact mul_le_mul_of_nonneg_right (hb x hx).2 (norm_nonneg x)
  by_cases hw : w = 0
  · subst hw
    have := hone w'
    rw [mul_zero, zero_sub, norm_neg, zero_sub, norm_neg]
    nlinarith [norm_nonneg w']
  by_cases hw' : w' = 0
  · subst hw'
    have := hone w
    rw [mul_zero, sub_zero, sub_zero]
    nlinarith [norm_nonneg w]
  have hu : ‖w / (‖w‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_pos_iff.2 hw).ne']
  have hu' : ‖w' / (‖w'‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_pos_iff.2 hw').ne']
  have hP := hlip _ _ hu hu'
  rw [s07d_p2_rs_hn hhom hw, s07d_p2_rs_hn hhom hw'] at hP
  have hU := s07d_p2_rs_unit hw hw'
  have e : (P w : ℂ) * w - (P w' : ℂ) * w' = (P w : ℂ) * (w - w') + ((P w - P w' : ℝ) : ℂ) * w' := by
    push_cast; ring
  rw [e]
  calc ‖(P w : ℂ) * (w - w') + ((P w - P w' : ℝ) : ℂ) * w'‖
        ≤ ‖(P w : ℂ) * (w - w')‖ + ‖((P w - P w' : ℝ) : ℂ) * w'‖ := norm_add_le _ _
    _ = |P w| * ‖w - w'‖ + |P w - P w'| * ‖w'‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
    _ ≤ M * ‖w - w'‖ + Λ * (‖w'‖ * ‖w / (‖w‖ : ℂ) - w' / (‖w'‖ : ℂ)‖) := by
          rw [abs_of_nonneg (hb w hw).1]
          have h1 : P w * ‖w - w'‖ ≤ M * ‖w - w'‖ :=
            mul_le_mul_of_nonneg_right (hb w hw).2 (norm_nonneg _)
          have h2 : |P w - P w'| * ‖w'‖ ≤ Λ * ‖w / (‖w‖ : ℂ) - w' / (‖w'‖ : ℂ)‖ * ‖w'‖ :=
            mul_le_mul_of_nonneg_right hP (norm_nonneg _)
          linarith
    _ ≤ M * ‖w - w'‖ + Λ * (2 * ‖w - w'‖) := by gcongr
    _ = (M + 2 * Λ) * ‖w - w'‖ := by ring

/-- P2.2 helper: the profile is continuous off `0`. -/
theorem s07d_p2_rs_cont {P : ℂ → ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hhom : ∀ (w : ℂ) (r : ℝ), 0 < r → P ((r : ℂ) * w) = P w)
    (hlip : ∀ u v : ℂ, ‖u‖ = 1 → ‖v‖ = 1 → |P u - P v| ≤ Λ * ‖u - v‖) {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt P z := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min ‖z‖ (ε * ‖z‖ / (2 * Λ + 1)), lt_min hzn (by positivity), fun y hy => ?_⟩
  rw [dist_eq_norm] at hy
  have hy1 : ‖y - z‖ < ‖z‖ := hy.trans_le (min_le_left _ _)
  have hy2 : ‖y - z‖ < ε * ‖z‖ / (2 * Λ + 1) := hy.trans_le (min_le_right _ _)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_sub, norm_neg] at hy1
    exact lt_irrefl _ hy1
  have hu : ‖y / (‖y‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_pos_iff.2 hy0).ne']
  have hu' : ‖z / (‖z‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm, div_self hzn.ne']
  have hP := hlip _ _ hu hu'
  rw [s07d_p2_rs_hn hhom hy0, s07d_p2_rs_hn hhom hz] at hP
  have hU := s07d_p2_rs_unit hy0 hz
  rw [Real.dist_eq]
  have h3 : ‖z‖ * |P y - P z| ≤ 2 * Λ * ‖y - z‖ := by
    calc ‖z‖ * |P y - P z| ≤ ‖z‖ * (Λ * ‖y / (‖y‖ : ℂ) - z / (‖z‖ : ℂ)‖) :=
          mul_le_mul_of_nonneg_left hP hzn.le
      _ = Λ * (‖z‖ * ‖y / (‖y‖ : ℂ) - z / (‖z‖ : ℂ)‖) := by ring
      _ ≤ Λ * (2 * ‖y - z‖) := mul_le_mul_of_nonneg_left hU hΛ
      _ = 2 * Λ * ‖y - z‖ := by ring
  have h4 : (2 * Λ + 1) * ‖y - z‖ < ε * ‖z‖ := by
    rw [lt_div_iff₀ (by positivity)] at hy2
    linarith
  by_contra hc
  push Not at hc
  nlinarith [norm_nonneg (y - z)]

/-- P2.2 helper (orientation of the radial stretch): at a point `w ≠ 0` of differentiability,
`D(P(·)·)(w) w = P(w) w` and `Im(D(P(·)·)(w)(i w)/w) = P(w)`, so the Jacobian is `P(w)² > 0`. -/
theorem s07d_p2_rs_or {P : ℂ → ℝ} (hhom : ∀ (w : ℂ) (r : ℝ), 0 < r → P ((r : ℂ) * w) = P w)
    {w : ℂ} (hw : w ≠ 0) (hPw : 0 < P w) (hPc : ContinuousAt P w)
    (hd : DifferentiableAt ℝ (fun z => (P z : ℂ) * z) w) :
    ‖dzbar (fun z => (P z : ℂ) * z) w‖ < ‖dz (fun z => (P z : ℂ) * z) w‖ := by
  set F : ℂ → ℂ := fun z => (P z : ℂ) * z with hF
  -- radial direction
  have hA1 : fderiv ℝ F w w = (P w : ℂ) * w := by
    have hlin : HasDerivAt (fun t : ℝ => w + (t : ℂ) * w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const w).const_add w
    have h1 : HasDerivAt (fun t : ℝ => F (w + (t : ℂ) * w)) (fderiv ℝ F w w) 0 :=
      hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hlin (by simp)
    have h3 : HasDerivAt (fun t : ℝ => (1 + (t : ℂ)) * ((P w : ℂ) * w)) ((P w : ℂ) * w) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_add (1 : ℂ)).mul_const ((P w : ℂ) * w)
    have h2 : HasDerivAt (fun t : ℝ => F (w + (t : ℂ) * w)) ((P w : ℂ) * w) 0 := by
      refine h3.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with t ht
      have ht' : (0 : ℝ) < 1 + t := by linarith [Set.mem_Ioi.1 ht]
      have e : w + (t : ℂ) * w = ((1 + t : ℝ) : ℂ) * w := by push_cast; ring
      show (P (w + (t : ℂ) * w) : ℂ) * (w + (t : ℂ) * w) = (1 + (t : ℂ)) * ((P w : ℂ) * w)
      rw [e, hhom w (1 + t) ht']
      push_cast
      ring
    exact h1.unique h2
  -- angular direction
  have hA2 : (fderiv ℝ F w (w * I) / w).im = P w := by
    set γ : ℝ → ℂ := fun t => w * Complex.exp ((t : ℂ) * I) with hγdef
    have hγ : HasDerivAt γ (w * I) 0 := by
      have he := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const I).cexp
      simpa [hγdef] using he.const_mul w
    have hγ0 : γ 0 = w := by simp [hγdef]
    have hg : HasDerivAt (fun t => F (γ t) / w) (fderiv ℝ F w (w * I) / w) 0 :=
      (hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm).div_const w
    have him : HasDerivAt (fun t => (F (γ t) / w).im) (fderiv ℝ F w (w * I) / w).im 0 :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hg
    have hform : ∀ t : ℝ, (F (γ t) / w).im = P (γ t) * Real.sin t := by
      intro t
      have e : (P (γ t) : ℂ) * (w * Complex.exp ((t : ℂ) * I)) / w =
          (P (γ t) : ℂ) * Complex.exp ((t : ℂ) * I) := by
        field_simp
      show ((P (γ t) : ℂ) * γ t / w).im = P (γ t) * Real.sin t
      rw [hγdef]
      simp only
      rw [e, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
    have hk : ContinuousAt (fun t => P (γ t)) 0 := ContinuousAt.comp_of_eq hPc hγ.continuousAt hγ0
    have hks : HasDerivAt (fun t => P (γ t) * Real.sin t) (P w) 0 := by
      rw [hasDerivAt_iff_tendsto_slope]
      have hs := hasDerivAt_iff_tendsto_slope.1 (Real.hasDerivAt_sin 0)
      rw [Real.cos_zero] at hs
      have hkt : Tendsto (fun t => P (γ t)) (𝓝[≠] (0 : ℝ)) (𝓝 (P w)) := by
        have := hk.tendsto
        rw [hγ0] at this
        exact this.mono_left nhdsWithin_le_nhds
      have := hkt.mul hs
      rw [mul_one] at this
      refine this.congr' (Eventually.of_forall fun t => ?_)
      simp only [slope_def_field, Real.sin_zero, mul_zero, sub_zero]
      ring
    have hks' : HasDerivAt (fun t => (F (γ t) / w).im) (P w) 0 := by
      simpa only [hform] using hks
    exact him.unique hks'
  -- algebra: `Im(conj(A w) A(i w)) = (|a|² - |b|²)|w|² = P(w)² |w|²`
  have hz := fderiv_eq_dz_dzbar hd
  set a := dz F w with ha
  set b := dzbar F w with hb
  have hid : (conj (fderiv ℝ F w w) * fderiv ℝ F w (w * I)).im = (‖a‖ ^ 2 - ‖b‖ ^ 2) * ‖w‖ ^ 2 := by
    rw [hz w, hz (w * I)]
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, map_add, map_mul,
      Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im, Complex.conj_conj]
    ring
  have hw2 : conj (fderiv ℝ F w w) * fderiv ℝ F w (w * I) =
      ((P w * ‖w‖ ^ 2 : ℝ) : ℂ) * (fderiv ℝ F w (w * I) / w) := by
    calc conj (fderiv ℝ F w w) * fderiv ℝ F w (w * I)
          = (P w : ℂ) * (conj w * w) * (fderiv ℝ F w (w * I) / w) := by
            rw [hA1, map_mul, Complex.conj_ofReal]
            field_simp
      _ = ((P w * ‖w‖ ^ 2 : ℝ) : ℂ) * (fderiv ℝ F w (w * I) / w) := by
            rw [Complex.conj_mul']
            push_cast
            ring
  have hkey : (‖a‖ ^ 2 - ‖b‖ ^ 2) * ‖w‖ ^ 2 = P w ^ 2 * ‖w‖ ^ 2 := by
    rw [← hid, hw2, Complex.im_ofReal_mul, hA2]
    ring
  have hwn : 0 < ‖w‖ ^ 2 := by positivity
  have hsq : ‖b‖ ^ 2 < ‖a‖ ^ 2 := by
    have := mul_right_cancel₀ hwn.ne' hkey
    nlinarith
  by_contra hc
  push Not at hc
  nlinarith [norm_nonneg a, norm_nonneg b]

/-- P2.2 helper: the radial stretch `F w = P(w) w` with a `0`-homogeneous profile `1 ≤ P ≤ A`,
`Λ`-Lipschitz on the circle, is an `(A + 2Λ)`-bi-Lipschitz `(A + 2Λ)²`-q.c. map of `ℂ` onto `ℂ`. -/
theorem s07d_p2_rs_qc {P : ℂ → ℝ} {A Λ : ℝ} (hA : 1 ≤ A) (hΛ : 0 ≤ Λ)
    (hhom : ∀ (w : ℂ) (r : ℝ), 0 < r → P ((r : ℂ) * w) = P w)
    (hb : ∀ w : ℂ, w ≠ 0 → 1 ≤ P w ∧ P w ≤ A)
    (hlip : ∀ u v : ℂ, ‖u‖ = 1 → ‖v‖ = 1 → |P u - P v| ≤ Λ * ‖u - v‖) :
    IsKQC (fun w => (P w : ℂ) * w) univ ((A + 2 * Λ) ^ 2) ∧
      (fun w => (P w : ℂ) * w) '' univ = univ ∧
      ∀ z w : ℂ, ‖z - w‖ ≤ (A + 2 * Λ) * ‖(P z : ℂ) * z - (P w : ℂ) * w‖ ∧
        ‖(P z : ℂ) * z - (P w : ℂ) * w‖ ≤ (A + 2 * Λ) * ‖z - w‖ := by
  have hup := s07d_p2_rs_lip hΛ hhom (fun w hw => ⟨zero_le_one.trans (hb w hw).1, (hb w hw).2⟩) hlip
  have hPpos : ∀ w : ℂ, w ≠ 0 → 0 < P w := fun w hw => zero_lt_one.trans_le (hb w hw).1
  -- the inverse stretch `v ↦ P(v)⁻¹ v`
  have hhomi : ∀ (w : ℂ) (r : ℝ), 0 < r → (P ((r : ℂ) * w))⁻¹ = (P w)⁻¹ := fun w r hr => by
    rw [hhom w r hr]
  have hbi : ∀ w : ℂ, w ≠ 0 → 0 ≤ (P w)⁻¹ ∧ (P w)⁻¹ ≤ 1 := fun w hw =>
    ⟨inv_nonneg.2 (hPpos w hw).le, inv_le_one_of_one_le₀ (hb w hw).1⟩
  have hlipi : ∀ u v : ℂ, ‖u‖ = 1 → ‖v‖ = 1 → |(P u)⁻¹ - (P v)⁻¹| ≤ Λ * ‖u - v‖ := by
    intro u v hu hv
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    have hv0 : v ≠ 0 := by rintro rfl; simp at hv
    have h1 := hb u hu0
    have h2 := hb v hv0
    rw [inv_sub_inv (hPpos u hu0).ne' (hPpos v hv0).ne', abs_div, abs_sub_comm,
      abs_of_pos (mul_pos (hPpos u hu0) (hPpos v hv0))]
    calc |P u - P v| / (P u * P v) ≤ |P u - P v| :=
          div_le_self (abs_nonneg _) (by nlinarith)
      _ ≤ Λ * ‖u - v‖ := hlip u v hu hv
  have hlo := s07d_p2_rs_lip hΛ hhomi hbi hlipi
  have hGF : ∀ w : ℂ, ((P ((P w : ℂ) * w))⁻¹ : ℂ) * ((P w : ℂ) * w) = w := by
    intro w
    by_cases hw : w = 0
    · subst hw; simp
    rw [hhom w (P w) (hPpos w hw)]
    have : (P w : ℂ) ≠ 0 := by exact_mod_cast (hPpos w hw).ne'
    field_simp
  have hFG : ∀ v : ℂ, (P (((P v)⁻¹ : ℝ) * v) : ℂ) * ((((P v)⁻¹ : ℝ) : ℂ) * v) = v := by
    intro v
    by_cases hv : v = 0
    · subst hv; simp
    rw [hhom v _ (inv_pos.2 (hPpos v hv))]
    have : (P v : ℂ) ≠ 0 := by exact_mod_cast (hPpos v hv).ne'
    push_cast
    field_simp
  have hbl : ∀ z w : ℂ, ‖z - w‖ ≤ (A + 2 * Λ) * ‖(P z : ℂ) * z - (P w : ℂ) * w‖ ∧
      ‖(P z : ℂ) * z - (P w : ℂ) * w‖ ≤ (A + 2 * Λ) * ‖z - w‖ := by
    intro z w
    refine ⟨?_, hup z w⟩
    have h := hlo ((P z : ℂ) * z) ((P w : ℂ) * w)
    push_cast at h
    rw [hGF z, hGF w] at h
    calc ‖z - w‖ ≤ (1 + 2 * Λ) * ‖(P z : ℂ) * z - (P w : ℂ) * w‖ := h
      _ ≤ (A + 2 * Λ) * ‖(P z : ℂ) * z - (P w : ℂ) * w‖ := by gcongr
  have hsurj : (fun w => (P w : ℂ) * w) '' univ = univ :=
    eq_univ_of_forall fun v => ⟨(((P v)⁻¹ : ℝ) : ℂ) * v, mem_univ _, hFG v⟩
  refine ⟨s07d_p2_bilip_qc (A + 2 * Λ) (by linarith) _ hbl hsurj ?_, hsurj, hbl⟩
  have h0 : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := by
    have := (measure_singleton (0 : ℂ) : volume ({0} : Set ℂ) = 0)
    filter_upwards [compl_mem_ae_iff.2 this] with z hz
    exact hz
  filter_upwards [h0] with z hz hd
  exact s07d_p2_rs_or hhom hz (hPpos z hz) (s07d_p2_rs_cont hΛ hhom hlip hz) hd

/-- P2.2 helper (the profile along a ray): for a unit vector `u`,
`T = sup {s ≥ 0 : c + s u ∈ 𝒟}` lies in `[ρ₀, A ρ₀]` and `c + s u ∈ 𝒟 ↔ s < T` for `s ≥ 0`. -/
theorem s07d_p2_rs_ray {𝒟 : Set ℂ} {c : ℂ} {ρ₀ A : ℝ} (hρ₀ : 0 < ρ₀) (hD : IsOpen 𝒟)
    (hin : ball c ρ₀ ⊆ 𝒟) (hout : 𝒟 ⊆ ball c (A * ρ₀))
    (hst : ∀ p ∈ 𝒟, ∀ b ∈ ball c ρ₀, ∀ t ∈ Icc (0 : ℝ) 1, p + t • (b - p) ∈ 𝒟) {u : ℂ}
    (hu : ‖u‖ = 1) :
    (ρ₀ ≤ sSup {s : ℝ | 0 ≤ s ∧ c + (s : ℂ) * u ∈ 𝒟} ∧
      sSup {s : ℝ | 0 ≤ s ∧ c + (s : ℂ) * u ∈ 𝒟} ≤ A * ρ₀) ∧
      ∀ s : ℝ, 0 ≤ s → (c + (s : ℂ) * u ∈ 𝒟 ↔ s < sSup {s : ℝ | 0 ≤ s ∧ c + (s : ℂ) * u ∈ 𝒟}) := by
  set S := {s : ℝ | 0 ≤ s ∧ c + (s : ℂ) * u ∈ 𝒟} with hS
  have hnorm : ∀ s : ℝ, 0 ≤ s → ‖(s : ℂ) * u‖ = s := fun s hs => by
    rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  have hbdd : BddAbove S := ⟨A * ρ₀, fun s hs => by
    have h := hout hs.2
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hnorm s hs.1] at h
    exact h.le⟩
  have hne : S.Nonempty := ⟨0, le_rfl, by simpa using hin (mem_ball_self hρ₀)⟩
  have hsmall : ∀ s : ℝ, 0 ≤ s → s < ρ₀ → s ∈ S := fun s hs hs' => ⟨hs, hin (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hnorm s hs]
    exact hs')⟩
  have hlow : ρ₀ ≤ sSup S := by
    refine le_of_forall_lt fun s hs => ?_
    by_cases h0 : s < 0
    · exact h0.trans_le (le_csSup hbdd ⟨le_rfl, by simpa using hin (mem_ball_self hρ₀)⟩)
    push Not at h0
    obtain ⟨s', hs'1, hs'2⟩ := exists_between hs
    exact hs'1.trans_le (le_csSup hbdd (hsmall s' (h0.trans hs'1.le) hs'2))
  refine ⟨⟨hlow, csSup_le hne fun s hs => by
    have h := hout hs.2
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hnorm s hs.1] at h
    exact h.le⟩, fun s hs => ⟨fun hm => ?_, fun hlt => ?_⟩⟩
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hD _ hm
    have hm' : s + ε / 2 ∈ S := by
      refine ⟨by linarith, hball ?_⟩
      rw [mem_ball, dist_eq_norm, show c + ((s + ε / 2 : ℝ) : ℂ) * u - (c + (s : ℂ) * u) =
        ((ε / 2 : ℝ) : ℂ) * u by push_cast; ring, hnorm _ (by linarith)]
      linarith
    linarith [le_csSup hbdd hm']
  · obtain ⟨s', hs', hss'⟩ := exists_lt_of_lt_csSup hne hlt
    have hs'0 : 0 < s' := hs.trans_lt hss'
    have h := hst _ hs'.2 c (mem_ball_self hρ₀) (1 - s / s')
      ⟨by rw [sub_nonneg]; exact (div_le_one hs'0).2 hss'.le, by
        have : 0 ≤ s / s' := div_nonneg hs hs'0.le
        linarith⟩
    convert h using 1
    rw [Complex.real_smul]
    have : (s' : ℂ) ≠ 0 := by exact_mod_cast hs'0.ne'
    push_cast
    field_simp
    ring

/-- P2.2 helper (the ray profile is Lipschitz on the circle): for unit `u, v`,
`T(u) - 2A²ρ₀ |u - v| ≤ T(v)`. -/
theorem s07d_p2_rs_raylip {𝒟 : Set ℂ} {c : ℂ} {ρ₀ A : ℝ} (hρ₀ : 0 < ρ₀) (hD : IsOpen 𝒟)
    (hin : ball c ρ₀ ⊆ 𝒟) (hout : 𝒟 ⊆ ball c (A * ρ₀))
    (hst : ∀ p ∈ 𝒟, ∀ b ∈ ball c ρ₀, ∀ t ∈ Icc (0 : ℝ) 1, p + t • (b - p) ∈ 𝒟) {u v : ℂ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    sSup {s : ℝ | 0 ≤ s ∧ c + (s : ℂ) * u ∈ 𝒟} - 2 * A ^ 2 * ρ₀ * ‖u - v‖ ≤
      sSup {s : ℝ | 0 ≤ s ∧ c + (s : ℂ) * v ∈ 𝒟} := by
  obtain ⟨⟨hTu1, hTu2⟩, hmu⟩ := s07d_p2_rs_ray hρ₀ hD hin hout hst hu
  obtain ⟨⟨hTv1, -⟩, hmv⟩ := s07d_p2_rs_ray hρ₀ hD hin hout hst hv
  set Tu := sSup {s : ℝ | 0 ≤ s ∧ c + (s : ℂ) * u ∈ 𝒟}
  set Tv := sSup {s : ℝ | 0 ≤ s ∧ c + (s : ℂ) * v ∈ 𝒟}
  set δ := ‖u - v‖ with hδ
  have hδ0 : 0 ≤ δ := norm_nonneg _
  -- every `s ∈ [0, Tu)` gives `s - 2 s² δ / ρ₀ ≤ Tv`
  have key : ∀ s : ℝ, 0 ≤ s → s < Tu → s - 2 * A ^ 2 * ρ₀ * δ ≤ Tv := by
    intro s hs hsT
    have hsA : s ^ 2 ≤ A ^ 2 * ρ₀ ^ 2 := by
      have : s < A * ρ₀ := hsT.trans_le hTu2
      nlinarith
    have hred : s - 2 * A ^ 2 * ρ₀ * δ ≤ s - 2 * s ^ 2 * δ / ρ₀ := by
      have : 2 * s ^ 2 * δ / ρ₀ ≤ 2 * A ^ 2 * ρ₀ * δ := by
        rw [div_le_iff₀ hρ₀]
        nlinarith
      linarith
    refine hred.trans ?_
    set lam := 2 * s * δ / ρ₀ with hlam
    have hlam0 : 0 ≤ lam := by positivity
    have hform : s - 2 * s ^ 2 * δ / ρ₀ = (1 - lam) * s := by rw [hlam]; ring
    rw [hform]
    by_cases h1 : 1 ≤ lam
    · nlinarith
    push Not at h1
    have hp : c + (s : ℂ) * u ∈ 𝒟 := (hmu s hs).2 hsT
    by_cases hz : lam = 0
    · have hsd : s * δ = 0 := by
        have : 2 * s * δ / ρ₀ = 0 := hz
        rw [div_eq_zero_iff] at this
        rcases this with h | h
        · linarith
        · linarith
      rw [hz, sub_zero, one_mul]
      rcases mul_eq_zero.1 hsd with h | h
      · rw [h]; exact hTv1.trans' hρ₀.le
      · have huv : u = v := sub_eq_zero.1 (norm_eq_zero.1 h)
        rw [huv] at hp
        exact ((hmv s hs).1 hp).le
    have hlampos : 0 < lam := lt_of_le_of_ne hlam0 (Ne.symm hz)
    have hlc : (lam : ℂ) ≠ 0 := by exact_mod_cast hlampos.ne'
    set b : ℂ := c + (((1 - lam) * s / lam : ℝ) : ℂ) * (v - u) with hbdef
    have hb : b ∈ ball c ρ₀ := by
      rw [mem_ball, dist_eq_norm, hbdef, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_sub_rev, ← hδ]
      have e : (1 - lam) * s / lam * δ = (1 - lam) * (ρ₀ / 2) := by
        rw [hlam]
        have hsδ : s * δ ≠ 0 := by
          intro h0
          apply hz
          rw [hlam, mul_assoc, h0, mul_zero, zero_div]
        have hs0 : s ≠ 0 := left_ne_zero_of_mul hsδ
        have hδ1 : δ ≠ 0 := right_ne_zero_of_mul hsδ
        field_simp
      rw [e]
      nlinarith
    have hm := hst _ hp b hb lam ⟨hlam0, h1.le⟩
    have e : c + (s : ℂ) * u + lam • (b - (c + (s : ℂ) * u)) = c + (((1 - lam) * s : ℝ) : ℂ) * v := by
      rw [Complex.real_smul, hbdef]
      push_cast
      field_simp
      ring
    rw [e] at hm
    exact ((hmv _ (mul_nonneg (by linarith) hs)).1 hm).le
  by_contra hc
  push Not at hc
  obtain ⟨s, hs1, hs2⟩ := exists_between (show max 0 (Tv + 2 * A ^ 2 * ρ₀ * δ) < Tu from
    max_lt (hρ₀.trans_le hTu1) (by linarith))
  have := key s ((le_max_left _ _).trans hs1.le) hs2
  linarith [le_max_right 0 (Tv + 2 * A ^ 2 * ρ₀ * δ)]

/-- P2.2 (radial stretch): a ball-star-shaped domain `B(c, ρ₀) ⊆ 𝒟 ⊆ B(c, A ρ₀)` is the image of
`𝔻` under a global `Q`-q.c. map `κ` which is bi-Lipschitz at scale `ρ₀` (`Q` depends only on `A`),
with `κ(𝔻̄) = closure 𝒟` and `κ(∂𝔻) = ∂𝒟`. -/
theorem s07d_p2_kappa (A : ℝ) (hA : 1 ≤ A) : ∃ Q : ℝ, 1 ≤ Q ∧
    ∀ (𝒟 : Set ℂ) (c : ℂ) (ρ₀ : ℝ), 0 < ρ₀ → IsOpen 𝒟 → ball c ρ₀ ⊆ 𝒟 → 𝒟 ⊆ ball c (A * ρ₀) →
      (∀ p ∈ 𝒟, ∀ b ∈ ball c ρ₀, ∀ t ∈ Icc (0 : ℝ) 1, p + t • (b - p) ∈ 𝒟) →
      ∃ κ : ℂ → ℂ, IsKQC κ univ Q ∧ κ '' univ = univ ∧ κ '' unitDisc = 𝒟 ∧
        κ '' closedBall (0 : ℂ) 1 = closure 𝒟 ∧ κ '' sphere (0 : ℂ) 1 = frontier 𝒟 ∧
        ∀ z w : ℂ, ρ₀ * ‖z - w‖ ≤ Q * ‖κ z - κ w‖ ∧ ‖κ z - κ w‖ ≤ Q * ρ₀ * ‖z - w‖ := by
  refine ⟨(A + 2 * (2 * A ^ 2)) ^ 2, by nlinarith, ?_⟩
  intro 𝒟 c ρ₀ hρ₀ hD hin hout hst
  set L : ℝ := A + 2 * (2 * A ^ 2) with hLdef
  have hL1 : 1 ≤ L := by nlinarith
  have hLQ : L ≤ L ^ 2 := by nlinarith
  set P : ℂ → ℝ := fun w => sSup {s : ℝ | 0 ≤ s ∧ c + (s : ℂ) * (w / (‖w‖ : ℂ)) ∈ 𝒟} / ρ₀
    with hPdef
  have hunit : ∀ w : ℂ, w ≠ 0 → ‖w / (‖w‖ : ℂ)‖ = 1 := fun w hw => by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_pos_iff.2 hw).ne']
  have hPu : ∀ u : ℂ, ‖u‖ = 1 → P u = sSup {s : ℝ | 0 ≤ s ∧ c + (s : ℂ) * u ∈ 𝒟} / ρ₀ := by
    intro u hu
    simp only [hPdef, hu, ofReal_one, div_one]
  have hhom : ∀ (w : ℂ) (r : ℝ), 0 < r → P ((r : ℂ) * w) = P w := by
    intro w r hr
    have e : (r : ℂ) * w / (‖(r : ℂ) * w‖ : ℂ) = w / (‖w‖ : ℂ) := by
      by_cases hw : w = 0
      · subst hw; simp
      have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hw).ne'
      have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      push_cast
      field_simp
    simp only [hPdef, e]
  have hb : ∀ w : ℂ, w ≠ 0 → 1 ≤ P w ∧ P w ≤ A := by
    intro w hw
    rw [← s07d_p2_rs_hn hhom hw, hPu _ (hunit w hw)]
    obtain ⟨⟨h1, h2⟩, -⟩ := s07d_p2_rs_ray hρ₀ hD hin hout hst (hunit w hw)
    exact ⟨(le_div_iff₀ hρ₀).2 (by linarith), (div_le_iff₀ hρ₀).2 h2⟩
  have hlip : ∀ u v : ℂ, ‖u‖ = 1 → ‖v‖ = 1 → |P u - P v| ≤ 2 * A ^ 2 * ‖u - v‖ := by
    intro u v hu hv
    rw [hPu u hu, hPu v hv]
    have h1 := s07d_p2_rs_raylip hρ₀ hD hin hout hst hu hv
    have h2 := s07d_p2_rs_raylip hρ₀ hD hin hout hst hv hu
    rw [norm_sub_rev v u] at h2
    rw [← sub_div, abs_div, abs_of_pos hρ₀, div_le_iff₀ hρ₀, abs_le]
    constructor <;> nlinarith
  have hmem : ∀ v : ℂ, v ≠ 0 → (c + v ∈ 𝒟 ↔ ‖v‖ < ρ₀ * P v) := by
    intro v hv
    have h := (s07d_p2_rs_ray hρ₀ hD hin hout hst (hunit v hv)).2 ‖v‖ (norm_nonneg v)
    have e : ((‖v‖ : ℝ) : ℂ) * (v / (‖v‖ : ℂ)) = v := by
      have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hv).ne'
      field_simp
    rw [e] at h
    rw [h, hPdef]
    simp only
    rw [mul_div_cancel₀ _ hρ₀.ne']
  obtain ⟨hFqc, -, hFbl⟩ := s07d_p2_rs_qc hA (by positivity) hhom hb hlip
  have hρc : (ρ₀ : ℂ) ≠ 0 := by exact_mod_cast hρ₀.ne'
  have haff : IsConformalOnto (fun z : ℂ => c + (ρ₀ : ℂ) * z) univ univ := by
    refine ⟨by fun_prop, fun x _ y _ hxy => ?_, eq_univ_of_forall fun y => ⟨(y - c) / ρ₀, mem_univ _, ?_⟩⟩
    · exact mul_left_cancel₀ hρc (add_left_cancel hxy)
    · show c + (ρ₀ : ℂ) * ((y - c) / ρ₀) = y
      field_simp
      ring
  have hK := thm7_1_comp hFqc (isKQC_one_of_conformal isOpen_univ haff) (subset_univ _)
  rw [mul_one] at hK
  have hdiff : ∀ z w : ℂ, ‖(c + (ρ₀ : ℂ) * ((P z : ℂ) * z)) - (c + (ρ₀ : ℂ) * ((P w : ℂ) * w))‖ =
      ρ₀ * ‖(P z : ℂ) * z - (P w : ℂ) * w‖ := fun z w => by
    rw [show (c + (ρ₀ : ℂ) * ((P z : ℂ) * z)) - (c + (ρ₀ : ℂ) * ((P w : ℂ) * w)) =
      (ρ₀ : ℂ) * ((P z : ℂ) * z - (P w : ℂ) * w) by ring, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hρ₀]
  have hinj : Function.Injective fun z : ℂ => c + (ρ₀ : ℂ) * ((P z : ℂ) * z) := by
    intro z w h
    have h1 := (hFbl z w).1
    have h2 := hdiff z w
    simp only at h
    rw [h, sub_self, norm_zero] at h2
    have : ‖(P z : ℂ) * z - (P w : ℂ) * w‖ = 0 := by
      rcases mul_eq_zero.1 h2.symm with h3 | h3
      · exact absurd h3 hρ₀.ne'
      · exact h3
    rw [this, mul_zero] at h1
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h1)
  have hcont : Continuous fun z : ℂ => c + (ρ₀ : ℂ) * ((P z : ℂ) * z) := by
    have hFc : Continuous fun z : ℂ => (P z : ℂ) * z := by
      refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal L) fun z w => ?_).continuous
      rw [Real.coe_toNNReal _ (by linarith), dist_eq_norm, dist_eq_norm]
      exact (hFbl z w).2
    exact continuous_const.add (continuous_const.mul hFc)
  have hdisc : (fun z : ℂ => c + (ρ₀ : ℂ) * ((P z : ℂ) * z)) '' unitDisc = 𝒟 := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
      by_cases hw0 : w = 0
      · subst hw0
        simpa using hin (mem_ball_self hρ₀)
      have hPw := hb w hw0
      have hv0 : (ρ₀ : ℂ) * ((P w : ℂ) * w) ≠ 0 :=
        mul_ne_zero hρc (mul_ne_zero (by exact_mod_cast (by linarith : (0 : ℝ) < P w).ne') hw0)
      refine (hmem _ hv0).2 ?_
      have e : (ρ₀ : ℂ) * ((P w : ℂ) * w) = ((ρ₀ * P w : ℝ) : ℂ) * w := by push_cast; ring
      have hpp : 0 < ρ₀ * P w := mul_pos hρ₀ (by linarith)
      rw [e, hhom w _ hpp, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpp]
      nlinarith
    · intro hz
      by_cases hv : z - c = 0
      · refine ⟨0, mem_ball_self one_pos, ?_⟩
        simp only [mul_zero, add_zero]
        exact (sub_eq_zero.1 hv).symm
      have hm := (hmem (z - c) hv).1 (by rwa [add_sub_cancel])
      have hPv := hb (z - c) hv
      have hpos : 0 < ρ₀ * P (z - c) := by nlinarith
      refine ⟨(((ρ₀ * P (z - c))⁻¹ : ℝ) : ℂ) * (z - c), ?_, ?_⟩
      · rw [unitDisc, mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (inv_pos.2 hpos), inv_mul_lt_iff₀ hpos, mul_one]
        exact hm
      · show c + (ρ₀ : ℂ) * ((P ((((ρ₀ * P (z - c))⁻¹ : ℝ) : ℂ) * (z - c)) : ℂ) *
          ((((ρ₀ * P (z - c))⁻¹ : ℝ) : ℂ) * (z - c))) = z
        rw [hhom _ _ (inv_pos.2 hpos)]
        have hPc : (P (z - c) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0 : ℝ) < P (z - c)).ne'
        push_cast
        field_simp
        ring
  have hball : unitDisc = ball (0 : ℂ) 1 := rfl
  have hclosed : (fun z : ℂ => c + (ρ₀ : ℂ) * ((P z : ℂ) * z)) '' closedBall (0 : ℂ) 1 =
      closure 𝒟 := by
    apply Subset.antisymm
    · rw [← closure_ball (0 : ℂ) one_ne_zero, ← hdisc, hball]
      exact image_closure_subset_closure_image hcont
    · refine closure_minimal ?_ ((isCompact_closedBall (0 : ℂ) 1).image hcont).isClosed
      rw [← hdisc, hball]
      exact image_mono ball_subset_closedBall
  refine ⟨fun z => c + (ρ₀ : ℂ) * ((P z : ℂ) * z), hK, ?_, hdisc, hclosed, ?_, fun z w => ?_⟩
  · refine eq_univ_of_forall fun y => ?_
    have hy : (y - c) / ρ₀ ∈ (fun w => (P w : ℂ) * w) '' univ := by
      rw [(s07d_p2_rs_qc hA (by positivity) hhom hb hlip).2.1]
      exact mem_univ _
    obtain ⟨w, -, hw⟩ := hy
    refine ⟨w, mem_univ _, ?_⟩
    show c + (ρ₀ : ℂ) * ((P w : ℂ) * w) = y
    simp only at hw
    rw [hw]
    field_simp
    ring
  · rw [frontier, hD.interior_eq, ← hclosed, ← hdisc, hball, ← closedBall_sdiff_ball,
      image_sdiff hinj]
  · rw [hdiff z w]
    have h1 := hFbl z w
    rw [← hLdef] at h1
    have hX := norm_nonneg ((P z : ℂ) * z - (P w : ℂ) * w)
    have hY := norm_nonneg (z - w)
    have h2 := mul_le_mul_of_nonneg_left h1.1 hρ₀.le
    have h3 := mul_le_mul_of_nonneg_left h1.2 hρ₀.le
    have h4 := mul_le_mul_of_nonneg_right hLQ (mul_nonneg hρ₀.le hX)
    have h5 := mul_le_mul_of_nonneg_right hLQ (mul_nonneg hρ₀.le hY)
    constructor <;> nlinarith

/-! ### P4.1 (w4): `ext` -/

/-- **P4.1** (`ext`): the Riemann map `ψ : 𝔻 → V` of a quasidisk `V = G(𝔻)` (`G` a global
`K`-q.c. map) has a global `K²`-q.c. extension `F`, with `F(∂𝔻) = G(∂𝔻) = ∂V`. -/
theorem s07d_p4_ext {K : ℝ} {V : Set ℂ} {ψ G : ℂ → ℂ} (hψ : IsConformalOnto ψ unitDisc V)
    (hG : IsKQC G univ K) (hGs : G '' univ = univ) (hGV : G '' unitDisc = V) (hψ0 : ψ 0 = G 0) :
    ∃ F : ℂ → ℂ, IsKQC F univ (K * K) ∧ F '' univ = univ ∧ EqOn F ψ unitDisc ∧
      F '' sphere 0 1 = G '' sphere 0 1 := by
  have hDo : IsOpen unitDisc := (isOpen_ball : IsOpen (ball (0 : ℂ) 1))
  have hψ1 : IsKQC ψ unitDisc 1 := isKQC_one_of_conformal hDo hψ
  have hGi := thm7_2_inv hG
  rw [hGs] at hGi
  have hGinj : InjOn G univ := hG.2.2.1.2.1
  have hleft : ∀ z, Function.invFunOn G univ (G z) = z := fun z =>
    hGinj.leftInvOn_invFunOn (mem_univ z)
  have hright : ∀ w, G (Function.invFunOn G univ w) = w := fun w => by
    have hw : w ∈ G '' univ := by
      rw [hGs]
      exact mem_univ w
    exact Function.invFunOn_eq hw
  have hH1 : IsKQC (Function.invFunOn G univ ∘ ψ) unitDisc (1 * K) :=
    thm7_1_comp hψ1 hGi (subset_univ _)
  have hH : IsKQC (Function.invFunOn G univ ∘ ψ) unitDisc K := by
    rw [one_mul] at hH1
    exact hH1
  have hHs : (Function.invFunOn G univ ∘ ψ) '' unitDisc = unitDisc := by
    rw [image_comp, hψ.2.2, ← hGV, image_image]
    simp only [hleft, image_id']
  have hH0 : (Function.invFunOn G univ ∘ ψ) 0 = 0 := by
    show Function.invFunOn G univ (ψ 0) = 0
    rw [hψ0, hleft]
  obtain ⟨Fx, hFx⟩ :=
    thm13_3_boundary_correspondence isJordanDomain_unitDisc isJordanDomain_unitDisc ⟨K, hH⟩ hHs
  obtain ⟨g, hg, hgs, hgH, -, hsym, -⟩ := ab_reflect hH hHs hH0 hFx
  have hg0 : g 0 = 0 := by
    rw [hgH (mem_ball_self one_pos), hH0]
  obtain ⟨φc, hbij, -, -, hφc⟩ := s07_de_limit_circle hg hgs hg0 hsym
  have hcirc : ∀ z ∈ sphere (0 : ℂ) 1, ((Circle.exp (Complex.arg z) : Circle) : ℂ) = z :=
    fun z hz => by
      rw [Circle.coe_exp]
      have h := Complex.norm_mul_exp_arg_mul_I z
      rw [mem_sphere_zero_iff_norm.1 hz, Complex.ofReal_one, one_mul] at h
      exact h
  have hgS : g '' sphere 0 1 = sphere 0 1 := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← hcirc z hz, ← hφc]
      exact mem_sphere_zero_iff_norm.2 (Circle.norm_coe _)
    · intro hw
      obtain ⟨ζ, hζ⟩ := hbij.2 (Circle.exp (Complex.arg w))
      refine ⟨ζ, mem_sphere_zero_iff_norm.2 (Circle.norm_coe ζ), ?_⟩
      rw [← hφc ζ, hζ, hcirc w hw]
  refine ⟨G ∘ g, thm7_1_comp hg hG (subset_univ _), ?_, ?_, ?_⟩
  · rw [image_comp, hgs, hGs]
  · intro z hz
    show G (g z) = ψ z
    rw [hgH hz]
    exact hright (ψ z)
  · rw [image_comp, hgS]

/-! ### P4.2 (w4): `nu` -/

/-- P4.2 helper (w4): `t ↦ F(e^{it})` is injective on every half-open window of length `2π`. -/
theorem s07d_p4_nu_inj {F : ℂ → ℂ} (hinj : InjOn F (sphere 0 1)) (c : ℝ) :
    InjOn (fun t : ℝ => F (Complex.exp (t * Complex.I))) (Ico c (c + 2 * π)) := by
  intro x hx y hy hxy
  have hs : ∀ t : ℝ, Complex.exp (t * Complex.I) ∈ sphere (0 : ℂ) 1 := fun t => by
    rw [mem_sphere_zero_iff_norm, Complex.norm_exp_ofReal_mul_I]
  have h1 : Complex.exp (x * Complex.I) = Complex.exp (y * Complex.I) := hinj (hs x) (hs y) hxy
  have h2 : ∀ t : ℝ, circleMap 0 1 t = Complex.exp (t * Complex.I) := fun t => by
    rw [circleMap_zero, Complex.ofReal_one, one_mul]
  refine injOn_circleMap_of_abs_sub_le' (c := 0) one_ne_zero (by linarith) hx hy ?_
  rw [h2, h2]
  exact h1

/-- P4.2 helper (w4): images of Borel subsets of a window under `t ↦ F(e^{it})` are Borel
(Lusin–Souslin). -/
theorem s07d_p4_nu_mimg {F : ℂ → ℂ} (hF : Continuous F) (hinj : InjOn F (sphere 0 1)) {c : ℝ}
    {S : Set ℝ} (hS : MeasurableSet S) (hSc : S ⊆ Ico c (c + 2 * π)) :
    MeasurableSet ((fun t : ℝ => F (Complex.exp (t * Complex.I))) '' S) := by
  have hc : Continuous fun t : ℝ => F (Complex.exp (t * Complex.I)) := hF.comp (by fun_prop)
  exact hS.image_of_continuousOn_injOn hc.continuousOn ((s07d_p4_nu_inj hinj c).mono hSc)

/-- P4.2 helper (w4): the windows `[2πn, 2πn + 2π)` cover `ℝ`. -/
theorem s07d_p4_nu_win (t : ℝ) : ∃ n : ℤ, t ∈ Ico (2 * π * n) (2 * π * n + 2 * π) := by
  have hpi := Real.pi_pos
  have hp : (0 : ℝ) < 2 * π := by linarith
  refine ⟨⌊t / (2 * π)⌋, ?_, ?_⟩
  · have h := Int.floor_le (t / (2 * π))
    rw [le_div_iff₀ hp] at h
    have e : (⌊t / (2 * π)⌋ : ℝ) * (2 * π) = 2 * π * ⌊t / (2 * π)⌋ := by ring
    linarith
  · have h := Int.lt_floor_add_one (t / (2 * π))
    rw [div_lt_iff₀ hp] at h
    have e : ((⌊t / (2 * π)⌋ : ℝ) + 1) * (2 * π) = 2 * π * ⌊t / (2 * π)⌋ + 2 * π := by ring
    linarith

/-- P4.2 helper (w4): the windows `[2πn, 2πn + 2π)` are pairwise disjoint. -/
theorem s07d_p4_nu_winu {t : ℝ} {n m : ℤ} (hn : t ∈ Ico (2 * π * n) (2 * π * n + 2 * π))
    (hm : t ∈ Ico (2 * π * m) (2 * π * m + 2 * π)) : n = m := by
  have hpi := Real.pi_pos
  have hp : (0 : ℝ) < 2 * π := by linarith
  have key : ∀ k : ℤ, t ∈ Ico (2 * π * k) (2 * π * k + 2 * π) → ⌊t / (2 * π)⌋ = k := by
    intro k hk
    rw [Int.floor_eq_iff, le_div_iff₀ hp, div_lt_iff₀ hp]
    have e1 : (k : ℝ) * (2 * π) = 2 * π * k := by ring
    have e2 : ((k : ℝ) + 1) * (2 * π) = 2 * π * k + 2 * π := by ring
    exact ⟨by linarith [hk.1], by linarith [hk.2]⟩
  rw [← key n hn, ← key m hm]

/-- **P4.2** (`nu`): the pullback of `μH[1]` along `θ ↦ F(e^{iθ})` (one period at a time) is a
measure on `ℝ`. -/
theorem s07d_p4_nu {F : ℂ → ℂ} (hF : Continuous F) (hinj : InjOn F (sphere 0 1)) :
    ∃ ν : Measure ℝ, ∀ a : ℝ, ∀ E ⊆ Ico a (a + 2 * π), MeasurableSet E →
      ν E = μH[1] (F '' ((fun t : ℝ => Complex.exp (t * Complex.I)) '' E)) := by
  have hpi := Real.pi_pos
  obtain ⟨e, he⟩ : ∃ e : ℝ → ℂ, e = fun t : ℝ => F (Complex.exp (t * Complex.I)) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℤ → Set ℝ, W = fun n : ℤ => Ico (2 * π * n) (2 * π * n + 2 * π) :=
    ⟨_, rfl⟩
  have hinj' : ∀ c : ℝ, InjOn e (Ico c (c + 2 * π)) := fun c => by
    rw [he]
    exact s07d_p4_nu_inj hinj c
  have hmimg : ∀ (c : ℝ) (S : Set ℝ), MeasurableSet S → S ⊆ Ico c (c + 2 * π) →
      MeasurableSet (e '' S) := fun c S hS hSc => by
    rw [he]
    exact s07d_p4_nu_mimg hF hinj hS hSc
  have hWm : ∀ n : ℤ, MeasurableSet (W n) := fun n => by
    rw [hW]
    exact measurableSet_Ico
  have hWin : ∀ t : ℝ, ∃ n : ℤ, t ∈ W n := fun t => by
    rw [hW]
    exact s07d_p4_nu_win t
  have hWu : ∀ (t : ℝ) (n m : ℤ), t ∈ W n → t ∈ W m → n = m := fun t n m hn hm => by
    rw [hW] at hn hm
    exact s07d_p4_nu_winu hn hm
  have hWinj : ∀ n : ℤ, InjOn e (W n) := fun n => by
    rw [hW]
    exact hinj' (2 * π * n)
  have hWimg : ∀ (n : ℤ) (S : Set ℝ), MeasurableSet S → S ⊆ W n → MeasurableSet (e '' S) :=
    fun n S hS hSc => by
      rw [hW] at hSc
      exact hmimg (2 * π * n) S hS hSc
  refine ⟨Measure.ofMeasurable (fun S _ => ∑' n : ℤ, μH[1] (e '' (S ∩ W n))) ?_ ?_, ?_⟩
  · show ∑' n : ℤ, μH[1] (e '' (∅ ∩ W n)) = 0
    simp
  · intro f hf hd
    show ∑' n : ℤ, μH[1] (e '' ((⋃ i, f i) ∩ W n)) = ∑' i, ∑' n : ℤ, μH[1] (e '' (f i ∩ W n))
    have h1 : ∀ n : ℤ, μH[1] (e '' ((⋃ i, f i) ∩ W n)) = ∑' i, μH[1] (e '' (f i ∩ W n)) := by
      intro n
      rw [iUnion_inter, image_iUnion]
      refine measure_iUnion ?_ ?_
      · intro i j hij
        show Disjoint (e '' (f i ∩ W n)) (e '' (f j ∩ W n))
        rw [Set.disjoint_left]
        rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
        have hxy : y = x := hWinj n hy.2 hx.2 hyx
        have hdij : Disjoint (f i) (f j) := hd hij
        exact Set.disjoint_left.1 hdij hx.1 (hxy ▸ hy.1)
      · intro i
        exact hWimg n _ ((hf i).inter (hWm n)) inter_subset_right
    rw [tsum_congr h1, ENNReal.tsum_comm]
  · intro a E hE hEm
    rw [Measure.ofMeasurable_apply E hEm]
    show ∑' n : ℤ, μH[1] (e '' (E ∩ W n)) =
      μH[1] (F '' ((fun t : ℝ => Complex.exp (t * Complex.I)) '' E))
    have hEe : F '' ((fun t : ℝ => Complex.exp (t * Complex.I)) '' E) = e '' E := by
      rw [image_image, he]
    have hcov : (⋃ n : ℤ, W n) = univ := eq_univ_of_forall fun t => mem_iUnion.2 (hWin t)
    have hU : e '' E = ⋃ n : ℤ, e '' (E ∩ W n) := by
      rw [← image_iUnion, ← inter_iUnion, hcov, inter_univ]
    rw [hEe, hU, measure_iUnion]
    · intro n m hnm
      show Disjoint (e '' (E ∩ W n)) (e '' (E ∩ W m))
      rw [Set.disjoint_left]
      rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
      have hxy : y = x := hinj' a (hE hy.1) (hE hx.1) hyx
      exact hnm (hWu x n m hx.2 (hxy ▸ hy.2))
    · intro n
      exact hmimg a _ (hEm.inter (hWm n)) (inter_subset_left.trans hE)


/-! ## P5: harmonic-measure transfer (w6, Round BMO) -/

/-- P5 helper: `t ↦ 1_S(e^{it})` is measurable. -/
theorem s07d_p5_ind_meas (S : Set ℂ) (hS : MeasurableSet S) :
    Measurable fun t : ℝ => S.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) :=
  (measurable_const.indicator hS).comp
    (by fun_prop : Continuous fun t : ℝ => Complex.exp (t * I)).measurable

/-- P5 helper: an indicator is bounded by `1`. -/
theorem s07d_p5_ind_abs (S : Set ℂ) (x : ℂ) : |S.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
  unfold Set.indicator; split_ifs <;> norm_num

/-- P5 helper: Poisson integrands with bounded measurable data are interval integrable. -/
theorem s07d_p5_pint_integrable (z : ℂ) (hz : z ∈ unitDisc) (f : ℝ → ℝ) (hf : Measurable f)
    (hf1 : ∀ t, |f t| ≤ 1) :
    IntervalIntegrable (fun t : ℝ => (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 * f t)
      volume 0 (2 * π) := by
  refine ((s07c_fkps_m2_kernel_cont z hz).intervalIntegrable 0 (2 * π)).mono_fun
    (((s07c_fkps_m2_kernel_cont z hz).measurable.mul hf).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun t => ?_
  dsimp only
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hf1 t)

/-- P5 helper: monotonicity of the Poisson integral. -/
theorem s07d_p5_pint_mono (z : ℂ) (hz : z ∈ unitDisc) (f g : ℝ → ℝ) (hf : Measurable f)
    (hg : Measurable g) (hf1 : ∀ t, |f t| ≤ 1) (hg1 : ∀ t, |g t| ≤ 1) (hfg : ∀ t, f t ≤ g t) :
    (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 * f t ≤
      (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 * g t := by
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact intervalIntegral.integral_mono_on (by positivity) (s07d_p5_pint_integrable z hz f hf hf1)
    (s07d_p5_pint_integrable z hz g hg hg1) fun t _ =>
      mul_le_mul_of_nonneg_left (hfg t) (s07c_fkps_m2_kernel_nonneg z hz t)

/-- P5 helper: the Poisson integral of a set is nonnegative. -/
theorem s07d_p5_pint_nonneg (z : ℂ) (hz : z ∈ unitDisc) (S : Set ℂ) :
    0 ≤ (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 *
      S.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) := by
  refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg (by positivity) fun t _ => ?_)
  exact mul_nonneg (s07c_fkps_m2_kernel_nonneg z hz t) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

/-- P5 helper: the Poisson integral of a set is at most `1`. -/
theorem s07d_p5_pint_le_one (z : ℂ) (hz : z ∈ unitDisc) (S : Set ℂ) (hS : MeasurableSet S) :
    (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 *
      S.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) ≤ 1 := by
  refine (s07d_p5_pint_mono z hz (fun t : ℝ => S.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)))
    (fun _ => (1 : ℝ)) (s07d_p5_ind_meas S hS) measurable_const (fun t => s07d_p5_ind_abs S _)
    (fun _ => by norm_num) (fun t => ?_)).trans (le_of_eq ?_)
  · have := s07d_p5_ind_abs S (Complex.exp (t * I))
    exact (le_abs_self _).trans this
  · simp only [mul_one]
    exact s07c_fkps_m2_kernel_mass z hz

/-- P5 helper: the Poisson integral only sees the values on the circle. -/
theorem s07d_p5_pint_congr (z : ℂ) (S T : Set ℂ)
    (h : ∀ t : ℝ, Complex.exp (t * I) ∈ S ↔ Complex.exp (t * I) ∈ T) :
    (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 *
      S.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) =
    (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 *
      T.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) := by
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  by_cases hs : Complex.exp (t * I) ∈ S
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem ((h t).mp hs)]
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (fun h' => hs ((h t).mpr h'))]

/-- **P5.1** (`herglotz`): the Poisson integral of the indicator of a measurable set is the real part
of a holomorphic function on `𝔻` (Herglotz), with values in `[0, 1]`. -/
theorem s07d_p5_herglotz (S : Set ℂ) (hS : MeasurableSet S) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F unitDisc ∧ ∀ z ∈ unitDisc,
      (F z).re = (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
        (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 *
          S.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) ∧
      0 ≤ (F z).re ∧ (F z).re ≤ 1 := by
  obtain ⟨f, hfdef⟩ : ∃ f : ℂ → ℂ, f = fun ζ => ((S.indicator (fun _ => (1 : ℝ)) ζ : ℝ) : ℂ) :=
    ⟨_, rfl⟩
  have hfm := s07d_p5_ind_meas S hS
  have hfc : ∀ t : ℝ, f (circleMap 0 1 t) =
      ((S.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) : ℝ) : ℂ) := by
    intro t; simp [hfdef, circleMap]
  have hci : CircleIntegrable f 0 1 := by
    unfold CircleIntegrable
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun ?_ ?_
    · simp only [hfc]
      exact (Complex.measurable_ofReal.comp hfm).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t => ?_
      simp only [hfc, Complex.norm_real, Real.norm_eq_abs, abs_one]
      exact s07d_p5_ind_abs S _
  refine ⟨fun w => Real.circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • f ζ) 0 1, ?_, ?_⟩
  · intro w hw
    have hws : w ∈ (sphere (0 : ℂ) |(1 : ℝ)|)ᶜ := by
      rw [abs_one, mem_compl_iff, mem_sphere_zero_iff_norm]
      exact ne_of_lt (by simpa [unitDisc, mem_ball_zero_iff] using hw)
    exact ((analyticOnNhd_circleAverage_herglotzRieszKernel_smul hci) w hws).differentiableAt
      |>.differentiableWithinAt
  · intro w hw
    have hne : ∀ t : ℝ, circleMap 0 1 t - 0 - (w - 0) ≠ 0 := by
      intro t h
      apply s07c_fkps_m2_exp_ne w hw t
      simpa [circleMap] using h
    have hkc : Continuous fun t : ℝ => herglotzRieszKernel 0 w (circleMap 0 1 t) := by
      simp only [herglotzRieszKernel_def]
      exact (((continuous_circleMap 0 1).sub continuous_const).add continuous_const).div
        (((continuous_circleMap 0 1).sub continuous_const).sub continuous_const) hne
    have hint : IntervalIntegrable
        (fun t : ℝ => herglotzRieszKernel 0 w (circleMap 0 1 t) • f (circleMap 0 1 t))
        volume 0 (2 * π) := by
      refine (hkc.norm.intervalIntegrable 0 (2 * π)).mono_fun ?_ ?_
      · simp only [hfc]
        exact (hkc.measurable.smul (Complex.measurable_ofReal.comp hfm)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun t => ?_
        dsimp only
        rw [hfc, norm_smul, norm_norm, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (norm_nonneg _) (s07d_p5_ind_abs S _)
    have hre := intervalIntegral.intervalIntegral_re (μ := volume) hint
    simp only [RCLike.re_to_complex] at hre
    have hP : (Real.circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • f ζ) 0 1).re =
        (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 *
          S.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) := by
      rw [Real.circleAverage_def, smul_re, smul_eq_mul, ← hre]
      congr 1
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [hfc]
      exact s07c_fkps_m2_re_herglotz w t _
    refine ⟨hP, ?_, ?_⟩
    · rw [hP]; exact s07d_p5_pint_nonneg w hw S
    · rw [hP]; exact s07d_p5_pint_le_one w hw S hS

/-- P5 helper: a continuous `2π`-periodic bump, positive only where `e^{it} ∈ B(ζ, r)`. -/
theorem s07d_p5_bump (ζ : ℂ) (r : ℝ) (hr : 0 < r) :
    Continuous (fun t : ℝ => max 0 (1 - ‖Complex.exp (t * I) - ζ‖ / r)) ∧
    (∀ t : ℝ, max 0 (1 - ‖Complex.exp (((t + 2 * π : ℝ) : ℂ) * I) - ζ‖ / r) =
      max 0 (1 - ‖Complex.exp (t * I) - ζ‖ / r)) ∧
    (∀ t : ℝ, |max 0 (1 - ‖Complex.exp (t * I) - ζ‖ / r)| ≤ 1) ∧
    (∀ t : ℝ, 0 < max 0 (1 - ‖Complex.exp (t * I) - ζ‖ / r) →
      Complex.exp (t * I) ∈ ball ζ r) := by
  refine ⟨continuous_const.max (continuous_const.sub
      ((by fun_prop : Continuous fun t : ℝ => ‖Complex.exp (t * I) - ζ‖).div_const r)),
    fun t => by rw [s07c_fkps_m2_exp_periodic], fun t => ?_, fun t ht => ?_⟩
  · rw [abs_of_nonneg (le_max_left _ _)]
    refine max_le zero_le_one ?_
    have : 0 ≤ ‖Complex.exp (t * I) - ζ‖ / r := div_nonneg (norm_nonneg _) hr.le
    linarith
  · rw [mem_ball, dist_eq_norm]
    rcases lt_max_iff.mp ht with h | h
    · exact absurd h (lt_irrefl 0)
    · have : ‖Complex.exp (t * I) - ζ‖ / r < 1 := by linarith
      rwa [div_lt_one hr] at this

/-- P5 helper: a unit vector is `e^{i arg ζ}`. -/
theorem s07d_p5_exp_arg (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) 1) :
    Complex.exp ((Complex.arg ζ : ℝ) * I) = ζ := by
  have hζ1 : ‖ζ‖ = 1 := by simpa using hζ
  have := Complex.norm_mul_exp_arg_mul_I ζ
  rwa [hζ1, Complex.ofReal_one, one_mul] at this

/-- **P5.2** (`open`): at a point `ζ` of an open set `U`, the harmonic measure of `U` tends to `1`
from below (lower semicontinuity at the boundary). -/
theorem s07d_p5_open (U : Set ℂ) (hU : IsOpen U) :
    ∀ ζ ∈ U ∩ sphere (0 : ℂ) 1, ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝[unitDisc] ζ,
      1 - ε < (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
        (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 *
          U.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) := by
  rintro ζ ⟨hζU, hζs⟩ ε hε
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU ζ hζU
  obtain ⟨hc, hp, h1, hsupp⟩ := s07d_p5_bump ζ r hr
  have hθ := s07d_p5_exp_arg ζ hζs
  have ht := s07c_fkps_m2_poisson_tendsto _ hc hp (Complex.arg ζ)
  have hval : max 0 (1 - ‖Complex.exp ((Complex.arg ζ : ℝ) * I) - ζ‖ / r) = 1 := by
    rw [hθ, sub_self, norm_zero, zero_div, sub_zero]; exact max_eq_right zero_le_one
  rw [hval, hθ] at ht
  have hev := ht.eventually (lt_mem_nhds (show 1 - ε < 1 by linarith))
  filter_upwards [hev, self_mem_nhdsWithin] with z hz hzD
  refine lt_of_lt_of_le hz (s07d_p5_pint_mono z hzD _ _ hc.measurable
    (s07d_p5_ind_meas U hU.measurableSet) h1 (fun t => s07d_p5_ind_abs U _) fun t => ?_)
  by_cases hpos : 0 < max 0 (1 - ‖Complex.exp (t * I) - ζ‖ / r)
  · rw [Set.indicator_of_mem (hrU (hsupp t hpos))]
    exact (le_abs_self _).trans (h1 t)
  · push_neg at hpos
    exact hpos.trans (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

/-- **P5.3** (`closed`): at a boundary point `ζ` off a closed set `K`, the harmonic measure of `K`
tends to `0`. -/
theorem s07d_p5_closed (K : Set ℂ) (hK : IsClosed K) :
    ∀ ζ ∈ sphere (0 : ℂ) 1 \ K, ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝[unitDisc] ζ,
      (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
        (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 *
          K.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) < ε := by
  rintro ζ ⟨hζs, hζK⟩ ε hε
  obtain ⟨r, hr, hrK⟩ := Metric.isOpen_iff.mp hK.isOpen_compl ζ hζK
  obtain ⟨hc, hp, h1, hsupp⟩ := s07d_p5_bump ζ r hr
  have hθ := s07d_p5_exp_arg ζ hζs
  have hc' : Continuous fun t : ℝ => 1 - max 0 (1 - ‖Complex.exp (t * I) - ζ‖ / r) :=
    continuous_const.sub hc
  have hp' : ∀ t : ℝ, 1 - max 0 (1 - ‖Complex.exp (((t + 2 * π : ℝ) : ℂ) * I) - ζ‖ / r) =
      1 - max 0 (1 - ‖Complex.exp (t * I) - ζ‖ / r) := fun t => by rw [hp t]
  have h1' : ∀ t : ℝ, |1 - max 0 (1 - ‖Complex.exp (t * I) - ζ‖ / r)| ≤ 1 := by
    intro t
    have h0 := le_max_left (0 : ℝ) (1 - ‖Complex.exp (t * I) - ζ‖ / r)
    have h2 := (le_abs_self _).trans (h1 t)
    rw [abs_le]; constructor <;> linarith
  have ht := s07c_fkps_m2_poisson_tendsto _ hc' hp' (Complex.arg ζ)
  have hval : 1 - max 0 (1 - ‖Complex.exp ((Complex.arg ζ : ℝ) * I) - ζ‖ / r) = 0 := by
    rw [hθ, sub_self, norm_zero, zero_div, sub_zero, max_eq_right zero_le_one, sub_self]
  rw [hval, hθ] at ht
  have hev := ht.eventually (gt_mem_nhds hε)
  filter_upwards [hev, self_mem_nhdsWithin] with z hz hzD
  refine lt_of_le_of_lt (s07d_p5_pint_mono z hzD _ _ (s07d_p5_ind_meas K hK.measurableSet)
    hc'.measurable (fun t => s07d_p5_ind_abs K _) h1' fun t => ?_) hz
  by_cases hm : Complex.exp (t * I) ∈ K
  · rw [Set.indicator_of_mem hm]
    have hnpos : ¬ 0 < max 0 (1 - ‖Complex.exp (t * I) - ζ‖ / r) := fun h => hrK (hsupp t h) hm
    push_neg at hnpos
    linarith
  · rw [Set.indicator_of_notMem hm]
    have := (le_abs_self _).trans (h1 t)
    linarith

/-- **P5.4** (`minprin`): minimum principle with boundary `liminf ≥ 0` at every point of `∂𝔻`
(no boundedness assumed): `Re F ≥ 0` on `𝔻`. -/
theorem s07d_p5_minprin (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F unitDisc)
    (hb : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝[unitDisc] ζ, -ε < (F z).re) :
    ∀ z ∈ unitDisc, 0 ≤ (F z).re := by
  intro z hz
  have hz1 : ‖z‖ < 1 := by simpa [unitDisc, mem_ball_zero_iff] using hz
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨A, hAdef⟩ : ∃ A : Set ℂ, A = {w | w ∈ unitDisc → -ε < (F w).re} := ⟨_, rfl⟩
  have hAn : ∀ ζ ∈ sphere (0 : ℂ) 1, A ∈ 𝓝 ζ := fun ζ hζ => by
    have h2 := mem_nhdsWithin_iff_eventually.mp (hb ζ hζ ε hε)
    rw [hAdef]; exact h2
  have hsub : sphere (0 : ℂ) 1 ⊆ interior A := fun ζ hζ =>
    mem_interior_iff_mem_nhds.mpr (hAn ζ hζ)
  obtain ⟨δ, hδ, hth⟩ := (isCompact_sphere (0 : ℂ) 1).exists_thickening_subset_open
    isOpen_interior hsub
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = max ((‖z‖ + 1) / 2) (1 - δ / 2) := ⟨_, rfl⟩
  have hr1 : r < 1 := by rw [hrdef]; exact max_lt (by linarith) (by linarith)
  have hrz : ‖z‖ < r := by rw [hrdef]; exact lt_max_of_lt_left (by linarith)
  have hrδ : 1 - δ < r := by rw [hrdef]; exact lt_max_of_lt_right (by linarith)
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg z) hrz
  have hsph : ∀ w : ℂ, ‖w‖ = r → -ε < (F w).re := by
    intro w hw
    have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; linarith
    have hwn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw0
    have hζn : ‖w / (‖w‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        div_self (norm_ne_zero_iff.mpr hw0)]
    have heq : w - w / (‖w‖ : ℂ) = ((‖w‖ - 1 : ℝ) : ℂ) * (w / (‖w‖ : ℂ)) := by
      push_cast; field_simp
    have hmem : w ∈ thickening δ (sphere (0 : ℂ) 1) := by
      rw [Metric.mem_thickening_iff]
      refine ⟨w / (‖w‖ : ℂ), by simpa using hζn, ?_⟩
      rw [dist_eq_norm, heq, norm_mul, hζn, mul_one, Complex.norm_real, Real.norm_eq_abs, hw,
        abs_of_nonpos (by linarith)]
      linarith
    have hA := interior_subset (hth hmem)
    rw [hAdef] at hA
    exact hA (by simp [unitDisc]; linarith)
  have hcb : closedBall (0 : ℂ) r ⊆ unitDisc := closedBall_subset_ball hr1
  have hd : DifferentiableOn ℂ (fun w => Complex.exp (-F w)) (closedBall (0 : ℂ) r) :=
    ((hF.mono hcb).neg).cexp
  have hdc : DiffContOnCl ℂ (fun w => Complex.exp (-F w)) (ball (0 : ℂ) r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rwa [closure_ball 0 hr0.ne']
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball) hdc
    (C := Real.exp ε) (fun w hw => ?_) (subset_closure (mem_ball_zero_iff.mpr hrz))
  · rw [Complex.norm_exp, neg_re, Real.exp_le_exp] at hmax
    linarith
  · rw [frontier_ball 0 hr0.ne', mem_sphere_zero_iff_norm] at hw
    rw [Complex.norm_exp, neg_re, Real.exp_le_exp]
    linarith [hsph w hw]

/-- P5 helper: `(2π)⁻¹ ∫₀^{2π} (P f + c) = (2π)⁻¹ ∫₀^{2π} P f + c`. -/
theorem s07d_p5_add_const (z : ℂ) (hz : z ∈ unitDisc) (f : ℝ → ℝ) (hf : Measurable f)
    (hf1 : ∀ t, |f t| ≤ 1) (c : ℝ) :
    (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 * f t + c =
      (2 * π)⁻¹ * (∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 * f t) +
        c := by
  rw [intervalIntegral.integral_add (s07d_p5_pint_integrable z hz f hf hf1) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_add]
  have : (2 * π)⁻¹ * (2 * π * c) = c := by field_simp
  rw [this]

/-- P5 helper: `t ↦ 1_S(e^{it})` is interval integrable on `[0, 2π]`. -/
theorem s07d_p5_ind_int (S : Set ℂ) (hS : MeasurableSet S) :
    IntervalIntegrable (fun t : ℝ => S.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)))
      volume 0 (2 * π) := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun
    (s07d_p5_ind_meas S hS).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [Real.norm_eq_abs, norm_one]
  exact s07d_p5_ind_abs S _

/-- P5 helper: the Poisson kernel at `z ∈ 𝔻` is at most `2/(1 - |z|)`. -/
theorem s07d_p5_kernel_le (z : ℂ) (hz : z ∈ unitDisc) (t : ℝ) :
    (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 ≤ 2 / (1 - ‖z‖) := by
  have hz1 : ‖z‖ < 1 := by simpa [unitDisc, mem_ball_zero_iff] using hz
  have h0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hd : 1 - ‖z‖ ≤ ‖Complex.exp (t * I) - z‖ := by
    have := norm_sub_norm_le (Complex.exp (t * I)) z
    rw [Complex.norm_exp_ofReal_mul_I] at this
    linarith
  have h1 : (1 - ‖z‖) ^ 2 ≤ ‖Complex.exp (t * I) - z‖ ^ 2 :=
    pow_le_pow_left₀ (by linarith) hd 2
  calc (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2
      ≤ (1 - ‖z‖ ^ 2) / (1 - ‖z‖) ^ 2 :=
        div_le_div_of_nonneg_left (by nlinarith) (by nlinarith) h1
    _ ≤ 2 / (1 - ‖z‖) := by
        rw [div_le_div_iff₀ (by nlinarith) (by linarith)]
        nlinarith [mul_pos (sub_pos.mpr hz1) (sub_pos.mpr hz1)]

/-- P5 helper: `P[E] ≤ P[F] + (2π)⁻¹ (2/(1-|z|)) |{t ∈ (0, 2π] : e^{it} ∈ E \ F}|`. -/
theorem s07d_p5_excess (z : ℂ) (hz : z ∈ unitDisc) (E F : Set ℂ) (hE : MeasurableSet E)
    (hF : MeasurableSet F) :
    (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 *
        E.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) ≤
      ((2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 *
        F.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I))) +
      (2 * π)⁻¹ * (2 / (1 - ‖z‖)) *
        (volume ((fun t : ℝ => Complex.exp (t * I)) ⁻¹' (E \ F) ∩ Ioc 0 (2 * π))).toReal := by
  have hEF : MeasurableSet (E \ F) := hE.diff hF
  have hexp : Continuous fun t : ℝ => Complex.exp (t * I) := by fun_prop
  have hpre : MeasurableSet ((fun t : ℝ => Complex.exp (t * I)) ⁻¹' (E \ F)) :=
    hEF.preimage hexp.measurable
  have hind : ∫ t in (0 : ℝ)..2 * π, (E \ F).indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) =
      (volume ((fun t : ℝ => Complex.exp (t * I)) ⁻¹' (E \ F) ∩ Ioc 0 (2 * π))).toReal := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    have : (fun t : ℝ => (E \ F).indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I))) =
        ((fun t : ℝ => Complex.exp (t * I)) ⁻¹' (E \ F)).indicator 1 := by
      funext t; rfl
    rw [this, integral_indicator_one hpre, measureReal_def, Measure.restrict_apply hpre]
  have hi1 := s07d_p5_pint_integrable z hz _ (s07d_p5_ind_meas F hF) (fun t => s07d_p5_ind_abs F _)
  have hi2 := (s07d_p5_ind_int (E \ F) hEF).const_mul (2 / (1 - ‖z‖))
  have hM : 0 ≤ 2 / (1 - ‖z‖) := by
    have hz1 : ‖z‖ < 1 := by simpa [unitDisc, mem_ball_zero_iff] using hz
    exact div_nonneg zero_le_two (by linarith)
  calc (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 *
        E.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I))
      ≤ (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, ((1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 *
          F.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) + 2 / (1 - ‖z‖) *
          (E \ F).indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine intervalIntegral.integral_mono_on (by positivity)
          (s07d_p5_pint_integrable z hz _ (s07d_p5_ind_meas E hE) (fun t => s07d_p5_ind_abs E _))
          (hi1.add hi2) fun t _ => ?_
        have hk := s07d_p5_kernel_le z hz t
        have hk0 := s07c_fkps_m2_kernel_nonneg z hz t
        by_cases hEm : Complex.exp (t * I) ∈ E
        · by_cases hFm : Complex.exp (t * I) ∈ F
          · rw [Set.indicator_of_mem hEm, Set.indicator_of_mem hFm,
              Set.indicator_of_notMem (fun h : Complex.exp (t * I) ∈ E \ F => h.2 hFm)]
            linarith
          · rw [Set.indicator_of_mem hEm, Set.indicator_of_notMem hFm,
              Set.indicator_of_mem (show Complex.exp (t * I) ∈ E \ F from ⟨hEm, hFm⟩)]
            linarith
        · rw [Set.indicator_of_notMem hEm, Set.indicator_of_notMem (fun h : Complex.exp (t * I) ∈ E \ F => hEm h.1)]
          have := mul_nonneg hk0 (Set.indicator_nonneg (fun _ _ => zero_le_one)
            (Complex.exp (t * I)) (s := F) (f := fun _ => (1 : ℝ)))
          linarith
    _ = _ := by
        rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul, hind]
        ring

/-- **P5.5** (`approx`): inner regularity (compact `K ⊆ C`) and outer regularity (open `U ⊇ D`) for
the Poisson-weighted arc length at a fixed `z ∈ 𝔻`. -/
theorem s07d_p5_approx (z : ℂ) (hz : z ∈ unitDisc) (η : ℝ) (hη : 0 < η) :
    (∀ C : Set ℂ, MeasurableSet C → ∃ K ⊆ C, IsCompact K ∧
      (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 *
          C.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) ≤
        (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 *
          K.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) + η) ∧
    (∀ D : Set ℂ, MeasurableSet D → ∃ U, D ⊆ U ∧ IsOpen U ∧
      (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 *
          U.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) ≤
        (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 *
          D.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) + η) := by
  have hz1 : ‖z‖ < 1 := by simpa [unitDisc, mem_ball_zero_iff] using hz
  have hexp : Continuous fun t : ℝ => Complex.exp (t * I) := by fun_prop
  obtain ⟨m, hmdef⟩ : ∃ m : Measure ℂ,
      m = Measure.map (fun t : ℝ => Complex.exp (t * I)) (volume.restrict (Ioc 0 (2 * π))) :=
    ⟨_, rfl⟩
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have : IsFiniteMeasure m := by rw [hmdef]; infer_instance
  have hm : ∀ B : Set ℂ, MeasurableSet B →
      m B = volume ((fun t : ℝ => Complex.exp (t * I)) ⁻¹' B ∩ Ioc 0 (2 * π)) := by
    intro B hB
    rw [hmdef, Measure.map_apply hexp.measurable hB,
      Measure.restrict_apply (hB.preimage hexp.measurable)]
  have hM : 0 < 2 / (1 - ‖z‖) := div_pos two_pos (by linarith)
  obtain ⟨η', hη'def⟩ : ∃ η' : ℝ, η' = η * (2 * π) / (2 / (1 - ‖z‖)) := ⟨_, rfl⟩
  have hη' : 0 < η' := by rw [hη'def]; positivity
  have hfin : ∀ x : ℝ≥0∞, x < ENNReal.ofReal η' →
      (2 * π)⁻¹ * (2 / (1 - ‖z‖)) * x.toReal ≤ η := by
    intro x hx
    have hxr : x.toReal ≤ η' := (ENNReal.toReal_lt_of_lt_ofReal hx).le
    calc (2 * π)⁻¹ * (2 / (1 - ‖z‖)) * x.toReal ≤ (2 * π)⁻¹ * (2 / (1 - ‖z‖)) * η' :=
          mul_le_mul_of_nonneg_left hxr (by positivity)
      _ = η := by rw [hη'def]; field_simp
  refine ⟨fun C hC => ?_, fun D hD => ?_⟩
  · obtain ⟨F, hFC, hFc, hFlt⟩ := hC.exists_isClosed_diff_lt (measure_ne_top m C)
      (ENNReal.ofReal_pos.mpr hη').ne'
    refine ⟨F ∩ sphere (0 : ℂ) 1, inter_subset_left.trans hFC,
      (isCompact_sphere 0 1).inter_left hFc, ?_⟩
    have hK : MeasurableSet (F ∩ sphere (0 : ℂ) 1) :=
      hFc.measurableSet.inter isClosed_sphere.measurableSet
    rw [s07d_p5_add_const z hz _ (s07d_p5_ind_meas _ hK) (fun t => s07d_p5_ind_abs _ _)]
    refine (s07d_p5_excess z hz C _ hC hK).trans (add_le_add le_rfl ?_)
    have hset : (fun t : ℝ => Complex.exp (t * I)) ⁻¹' (C \ (F ∩ sphere (0 : ℂ) 1)) =
        (fun t : ℝ => Complex.exp (t * I)) ⁻¹' (C \ F) := by
      ext t
      simp [Complex.norm_exp_ofReal_mul_I]
    rw [hset, ← hm _ (hC.diff hFc.measurableSet)]
    exact hfin _ hFlt
  · have hlt : m D < m D + ENNReal.ofReal η' :=
      ENNReal.lt_add_right (measure_ne_top m D) (ENNReal.ofReal_pos.mpr hη').ne'
    obtain ⟨U, hDU, hUo, hUlt⟩ := Set.exists_isOpen_lt_of_lt D _ hlt
    refine ⟨U, hDU, hUo, ?_⟩
    rw [s07d_p5_add_const z hz _ (s07d_p5_ind_meas _ hD) (fun t => s07d_p5_ind_abs _ _)]
    refine (s07d_p5_excess z hz U D hUo.measurableSet hD).trans (add_le_add le_rfl ?_)
    rw [← hm _ (hUo.measurableSet.diff hD), measure_diff hDU hD.nullMeasurableSet
      (measure_ne_top m D)]
    refine hfin _ (ENNReal.sub_lt_of_lt_add (measure_mono hDU) ?_)
    rwa [add_comm]

/-- **P5.6** (`lowner`, continuous Löwner lemma): let `φ` be continuous on `𝔻̄`, holomorphic on `𝔻`,
with `φ(𝔻) ⊆ 𝔻`, and let `C, D` be measurable with `φ(C ∩ ∂𝔻) ⊆ D ∩ ∂𝔻`. Then
`ω(z, C) ≤ ω(φ z, D)` for every `z ∈ 𝔻`. -/
theorem s07d_p5_lowner (φ : ℂ → ℂ) (hφc : ContinuousOn φ (closedBall (0 : ℂ) 1))
    (hφd : DifferentiableOn ℂ φ unitDisc) (hφm : MapsTo φ unitDisc unitDisc)
    (C D : Set ℂ) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hCD : MapsTo φ (C ∩ sphere (0 : ℂ) 1) (D ∩ sphere (0 : ℂ) 1)) (z : ℂ) (hz : z ∈ unitDisc) :
    (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 *
        C.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) ≤
      (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖φ z‖ ^ 2) / ‖Complex.exp (t * I) - φ z‖ ^ 2 *
        D.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨K₀, hK₀C, hK₀c, hK₀⟩ := (s07d_p5_approx z hz (ε / 2) (by linarith)).1 C hC
  obtain ⟨U, hDU, hUo, hU⟩ := (s07d_p5_approx (φ z) (hφm hz) (ε / 2) (by linarith)).2 D hD
  rw [s07d_p5_add_const z hz _ (s07d_p5_ind_meas _ hK₀c.isClosed.measurableSet)
    (fun t => s07d_p5_ind_abs _ _)] at hK₀
  rw [s07d_p5_add_const (φ z) (hφm hz) _ (s07d_p5_ind_meas _ hD)
    (fun t => s07d_p5_ind_abs _ _)] at hU
  -- `K = K₀ ∩ ∂𝔻`: compact, inside `C ∩ ∂𝔻`, same Poisson integral
  obtain ⟨K, hKdef⟩ : ∃ K : Set ℂ, K = K₀ ∩ sphere (0 : ℂ) 1 := ⟨_, rfl⟩
  have hKc : IsClosed K := by
    rw [hKdef]; exact (hK₀c.inter_right isClosed_sphere).isClosed
  have hKK₀ := s07d_p5_pint_congr z K K₀ fun t => by
    rw [hKdef]; simp [Complex.norm_exp_ofReal_mul_I]
  obtain ⟨FU, hFUd, hFU⟩ := s07d_p5_herglotz U hUo.measurableSet
  obtain ⟨FK, hFKd, hFK⟩ := s07d_p5_herglotz K hKc.measurableSet
  have hmin := s07d_p5_minprin (fun w => FU (φ w) - FK w)
    ((hFUd.comp hφd hφm).sub hFKd) (fun ζ hζ δ hδ => ?_) z hz
  · simp only [sub_re] at hmin
    rw [(hFU (φ z) (hφm hz)).1, (hFK z hz).1, hKK₀] at hmin
    linarith
  · by_cases hζK : ζ ∈ K
    · have hζC : ζ ∈ C ∩ sphere (0 : ℂ) 1 := by
        rw [hKdef] at hζK; exact ⟨hK₀C hζK.1, hζK.2⟩
      have hφζ := hCD hζC
      have hlim : Tendsto φ (𝓝[unitDisc] ζ) (𝓝[unitDisc] (φ ζ)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨((hφc ζ (sphere_subset_closedBall hζ)).mono ball_subset_closedBall).tendsto, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with w hw using hφm hw
      have hev := hlim.eventually (s07d_p5_open U hUo (φ ζ) ⟨hDU hφζ.1, hφζ.2⟩ δ hδ)
      filter_upwards [hev, self_mem_nhdsWithin] with w hw hwD
      simp only [sub_re]
      rw [(hFU (φ w) (hφm hwD)).1, (hFK w hwD).1]
      have := (hFK w hwD).2.2
      rw [(hFK w hwD).1] at this
      linarith
    · have hev := s07d_p5_closed K hKc ζ ⟨hζ, hζK⟩ δ hδ
      filter_upwards [hev, self_mem_nhdsWithin] with w hw hwD
      simp only [sub_re]
      rw [(hFK w hwD).1]
      have := (hFU (φ w) (hφm hwD)).2.1
      linarith

/-- P5 helper: the map `φ = Gg⁻¹ ∘ Ψ` of the transfer, for a conformal `g : U → W` (`U` open)
extended by a homeomorphism `Gg` of `ℂ`: continuous, holomorphic on `𝔻` with `φ(𝔻) ⊆ U`,
`φ z = w` when `g w = ψ z`, and `φ(Ψ⁻¹X ∩ ∂𝔻) ⊆ Gg⁻¹X ∩ ∂𝔻` for `X ⊆ Gg(∂𝔻)`. -/
theorem s07d_p5_phi {U V W : Set ℂ} (hU : IsOpen U) {ψ g Ψ Gg : ℂ → ℂ}
    (hψ : IsConformalOnto ψ unitDisc V) (hg : IsConformalOnto g U W) (hVW : V ⊆ W)
    (hΨ : IsHomeomorphOnto Ψ univ univ) (hΨψ : EqOn Ψ ψ unitDisc)
    (hG : IsHomeomorphOnto Gg univ univ) (hGg : EqOn Gg g U)
    (X : Set ℂ) (hXΓ : X ⊆ Gg '' sphere (0 : ℂ) 1) :
    Continuous (fun x => Function.invFunOn Gg univ (Ψ x)) ∧
    DifferentiableOn ℂ (fun x => Function.invFunOn Gg univ (Ψ x)) unitDisc ∧
    MapsTo (fun x => Function.invFunOn Gg univ (Ψ x)) unitDisc U ∧
    (∀ z w : ℂ, w ∈ U → g w = ψ z → z ∈ unitDisc → Function.invFunOn Gg univ (Ψ z) = w) ∧
    MapsTo (fun x => Function.invFunOn Gg univ (Ψ x)) (Ψ ⁻¹' X ∩ sphere (0 : ℂ) 1)
      (Gg ⁻¹' X ∩ sphere (0 : ℂ) 1) := by
  obtain ⟨hΨc, -, -, -⟩ := hΨ
  obtain ⟨-, hGi, hGs, hGic⟩ := hG
  have hGic' : Continuous (Function.invFunOn Gg univ) := continuousOn_univ.mp hGic
  have hleft : ∀ x, Function.invFunOn Gg univ (Gg x) = x := fun x =>
    hGi.leftInvOn_invFunOn (mem_univ x)
  have hΨcont : Continuous Ψ := continuousOn_univ.mp hΨc
  have hpre : ∀ x ∈ unitDisc, ∃ y ∈ U, g y = ψ x := fun x hx => by
    have : ψ x ∈ W := hVW (hψ.2.2 ▸ mem_image_of_mem ψ hx)
    rw [← hg.2.2] at this
    exact this
  have hφx : ∀ x ∈ unitDisc, ∀ y ∈ U, g y = ψ x → Function.invFunOn Gg univ (Ψ x) = y := by
    intro x hx y hy hxy
    rw [hΨψ hx, ← hxy, ← hGg hy, hleft]
  refine ⟨hGic'.comp hΨcont, ?_, fun x hx => ?_, fun z w hw hzw hz => hφx z hz w hw hzw, ?_⟩
  · have hinv := (RMT.differentiableOn_invFunOn_of_injOn hU hg.1 hg.2.1).2
    have hmaps : MapsTo ψ unitDisc (g '' U) := fun x hx => by
      obtain ⟨y, hy, hxy⟩ := hpre x hx
      exact ⟨y, hy, hxy⟩
    refine (hinv.comp hψ.1 hmaps).congr fun x hx => ?_
    obtain ⟨y, hy, hxy⟩ := hpre x hx
    rw [hφx x hx y hy hxy]
    show y = Function.invFunOn g U (ψ x)
    rw [← hxy, hg.2.1.leftInvOn_invFunOn hy]
  · obtain ⟨y, hy, hxy⟩ := hpre x hx
    show Function.invFunOn Gg univ (Ψ x) ∈ U
    rw [hφx x hx y hy hxy]; exact hy
  · rintro ζ ⟨hζX, hζs⟩
    obtain ⟨η, hη, hηeq⟩ := hXΓ hζX
    have : Function.invFunOn Gg univ (Ψ ζ) = η := by rw [← hηeq, hleft]
    refine ⟨?_, ?_⟩
    · show Gg (Function.invFunOn Gg univ (Ψ ζ)) ∈ X
      rw [this, hηeq]; exact hζX
    · show Function.invFunOn Gg univ (Ψ ζ) ∈ sphere (0 : ℂ) 1
      rw [this]; exact hη

/-- **P5** (`transfer`, interior form): harmonic measure increases with the domain on common
boundary. Let `V = ψ(𝔻) ⊆ W = g(𝔻)`, with `ψ, g` conformal and extending to homeomorphisms
`Ψ, Gg` of `ℂ`, and `X ⊆ ∂W = Gg(∂𝔻)` measurable. Then for `ψ z = g w`:
`ω_V(ψ z, X) ≤ ω_W(g w, X)`, i.e. `P_z[1_{Ψ⁻¹X}] ≤ P_w[1_{Gg⁻¹X}]`. -/
theorem s07d_p5_transfer {V W : Set ℂ} {ψ g Ψ Gg : ℂ → ℂ}
    (hψ : IsConformalOnto ψ unitDisc V) (hg : IsConformalOnto g unitDisc W) (hVW : V ⊆ W)
    (hΨ : IsHomeomorphOnto Ψ univ univ) (hΨψ : EqOn Ψ ψ unitDisc)
    (hG : IsHomeomorphOnto Gg univ univ) (hGg : EqOn Gg g unitDisc)
    (X : Set ℂ) (hX : MeasurableSet X) (hXΓ : X ⊆ Gg '' sphere (0 : ℂ) 1)
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hzw : g w = ψ z) :
    (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 *
        (Ψ ⁻¹' X).indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) ≤
      (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 *
        (Gg ⁻¹' X).indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) := by
  have hΨc : Continuous Ψ := continuousOn_univ.mp hΨ.1
  have hGc : Continuous Gg := continuousOn_univ.mp hG.1
  obtain ⟨hφc, hφd, hφm, hφz, hφb⟩ := s07d_p5_phi (isOpen_ball : IsOpen unitDisc) hψ hg hVW hΨ
    hΨψ hG hGg X hXΓ
  have h := s07d_p5_lowner _ hφc.continuousOn hφd hφm (Ψ ⁻¹' X) (Gg ⁻¹' X)
    (hX.preimage hΨc.measurable) (hX.preimage hGc.measurable) hφb z hz
  rwa [hφz z w hw hzw hz] at h

/-- P5 helper: on the unit circle, `y⁻¹ = ȳ`. -/
theorem s07d_p5_unit_inv (y : ℂ) (hy : ‖y‖ = 1) : y⁻¹ = conj y := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hy]
  simp

/-- P5 helper: the exterior Poisson integral at `w ∈ 𝔻*` is the interior one at `1/w` of the
conjugate set: `P_ext(w, ζ) = P(1/w, ζ̄)`. -/
theorem s07d_p5_ext_eq (w : ℂ) (hw : 1 < ‖w‖) (D : Set ℂ) :
    (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖w⁻¹‖ ^ 2) / ‖Complex.exp (t * I) - w⁻¹‖ ^ 2 *
        ((fun y => conj y) ⁻¹' D).indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) =
      (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (‖w‖ ^ 2 - 1) / ‖Complex.exp (t * I) - w‖ ^ 2 *
        D.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) := by
  have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; linarith
  congr 1
  have hsub := intervalIntegral.integral_comp_sub_left (a := 0) (b := 2 * π)
    (fun s : ℝ => (‖w‖ ^ 2 - 1) / ‖Complex.exp (s * I) - w‖ ^ 2 *
      D.indicator (fun _ => (1 : ℝ)) (Complex.exp (s * I))) (2 * π)
  rw [sub_self, sub_zero] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have he1 : ‖Complex.exp (t * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I t
  have he0 : Complex.exp (t * I) ≠ 0 := Complex.exp_ne_zero _
  have he' : Complex.exp (((2 * π - t : ℝ) : ℂ) * I) = (Complex.exp (t * I))⁻¹ := by
    rw [show ((2 * π - t : ℝ) : ℂ) * I = 2 * π * I + -(t * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul, Complex.exp_neg]
  rw [he', s07d_p5_unit_inv _ he1]
  rw [show ((fun y => conj y) ⁻¹' D).indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) =
    D.indicator (fun _ => (1 : ℝ)) (conj (Complex.exp (t * I))) from rfl]
  congr 1
  rw [← s07d_p5_unit_inv _ he1]
  obtain ⟨e, hedef⟩ : ∃ e : ℂ, e = Complex.exp (t * I) := ⟨_, rfl⟩
  rw [← hedef] at he1 he0 ⊢
  have hN : ‖w * e - 1‖ ≠ 0 := by
    intro h
    have h1 : w * e = 1 := sub_eq_zero.mp (norm_eq_zero.mp h)
    have : ‖w * e‖ = ‖w‖ := by rw [norm_mul, he1, mul_one]
    rw [h1, norm_one] at this
    linarith
  have h1 : e - w⁻¹ = w⁻¹ * (w * e - 1) := by
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hw0, one_mul, mul_one]
  have h2 : e⁻¹ - w = -(e⁻¹ * (w * e - 1)) := by
    rw [mul_sub, mul_one, mul_comm w e, ← mul_assoc, inv_mul_cancel₀ he0, one_mul, neg_sub]
  have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  rw [h1, h2, norm_neg, norm_mul, norm_mul, norm_inv, norm_inv, he1, inv_one, one_mul]
  field_simp

/-- **P5** (`transfer_ext`, exterior form, for the welding side `Ωs = g(𝔻*)`): as `transfer`, with
`W = g(𝔻*)` and the exterior Poisson kernel `(|w|² - 1)/|e^{it} - w|²` at `w ∈ 𝔻*`. -/
theorem s07d_p5_transfer_ext {V W : Set ℂ} {ψ g Ψ Gg : ℂ → ℂ}
    (hψ : IsConformalOnto ψ unitDisc V) (hg : IsConformalOnto g unitDiscExterior W) (hVW : V ⊆ W)
    (hΨ : IsHomeomorphOnto Ψ univ univ) (hΨψ : EqOn Ψ ψ unitDisc)
    (hG : IsHomeomorphOnto Gg univ univ) (hGg : EqOn Gg g unitDiscExterior)
    (X : Set ℂ) (hX : MeasurableSet X) (hXΓ : X ⊆ Gg '' sphere (0 : ℂ) 1)
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDiscExterior) (hzw : g w = ψ z) :
    (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 *
        (Ψ ⁻¹' X).indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) ≤
      (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (‖w‖ ^ 2 - 1) / ‖Complex.exp (t * I) - w‖ ^ 2 *
        (Gg ⁻¹' X).indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) := by
  have hΨc : Continuous Ψ := continuousOn_univ.mp hΨ.1
  have hGc : Continuous Gg := continuousOn_univ.mp hG.1
  have hUo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  obtain ⟨hφc, hφd, hφm, hφz, hφb⟩ := s07d_p5_phi hUo hψ hg hVW hΨ hΨψ hG hGg X hXΓ
  obtain ⟨φ, hφdef⟩ : ∃ φ : ℂ → ℂ, φ = fun x => Function.invFunOn Gg univ (Ψ x) := ⟨_, rfl⟩
  rw [← hφdef] at hφc hφd hφm hφb
  have hφz' : φ z = w := by rw [hφdef]; exact hφz z w hw hzw hz
  have hge : ∀ x ∈ closedBall (0 : ℂ) 1, 1 ≤ ‖φ x‖ := by
    have hcl : IsClosed {x : ℂ | 1 ≤ ‖φ x‖} := isClosed_le continuous_const (continuous_norm.comp hφc)
    have hsub : unitDisc ⊆ {x : ℂ | 1 ≤ ‖φ x‖} := fun x hx => show 1 ≤ ‖φ x‖ from le_of_lt (hφm hx)
    intro x hx
    rw [← closure_ball (0 : ℂ) one_ne_zero] at hx
    exact closure_minimal hsub hcl hx
  have hne : ∀ x ∈ closedBall (0 : ℂ) 1, φ x ≠ 0 := fun x hx h => by
    have := hge x hx; rw [h, norm_zero] at this; linarith
  have hDm : MeasurableSet ((fun y => conj y) ⁻¹' (Gg ⁻¹' X)) :=
    (hX.preimage hGc.measurable).preimage Complex.continuous_conj.measurable
  have hl := s07d_p5_lowner (fun x => (φ x)⁻¹) (hφc.continuousOn.inv₀ hne)
    (hφd.inv fun x hx => hne x (ball_subset_closedBall hx))
    (fun x hx => by
      have h1 : 1 < ‖φ x‖ := hφm hx
      show (φ x)⁻¹ ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff, norm_inv]
      exact inv_lt_one_of_one_lt₀ h1)
    (Ψ ⁻¹' X) _ (hX.preimage hΨc.measurable) hDm
    (fun ζ hζ => by
      obtain ⟨hζX, hζs⟩ := hφb hζ
      have hn : ‖φ ζ‖ = 1 := by simpa using hζs
      refine ⟨?_, ?_⟩
      · show Gg (conj (φ ζ)⁻¹) ∈ X
        rw [s07d_p5_unit_inv _ hn, Complex.conj_conj]; exact hζX
      · show (φ ζ)⁻¹ ∈ sphere (0 : ℂ) 1
        rw [mem_sphere_zero_iff_norm, norm_inv, hn, inv_one]) z hz
  rw [hφz'] at hl
  rw [← s07d_p5_ext_eq w hw]
  exact hl

/-! ### P4.3 (w4): `geom` -/

/-- P4.3 helper (w4): the three-point bound in the form `‖a - b‖ ≤ L ‖a - c‖ ⇒
‖F a - F b‖ ≤ C L^K ‖F a - F c‖` (`L ≥ 1`). -/
theorem s07d_p4_g_qs {K C : ℝ} {F : ℂ → ℂ} (hK : 1 ≤ K) (hC : 0 < C)
    (hqs : ∀ a b c : ℂ, a ≠ c → ‖F a - F b‖ / ‖F a - F c‖ ≤
      C * max ((‖a - b‖ / ‖a - c‖) ^ (1 / K)) ((‖a - b‖ / ‖a - c‖) ^ K))
    (hFi : Function.Injective F) {a b c : ℂ} {L : ℝ} (hL : 1 ≤ L) (hac : a ≠ c)
    (hab : ‖a - b‖ ≤ L * ‖a - c‖) :
    ‖F a - F b‖ ≤ C * L ^ K * ‖F a - F c‖ := by
  have hac' : 0 < ‖a - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hac)
  have hFac : 0 < ‖F a - F c‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hac (hFi h))
  have hρ0 : 0 ≤ ‖a - b‖ / ‖a - c‖ := div_nonneg (norm_nonneg _) hac'.le
  have hρL : ‖a - b‖ / ‖a - c‖ ≤ L := (div_le_iff₀ hac').2 hab
  have hK0 : 0 < K := by linarith
  have hKi : 1 / K ≤ K := by
    rw [div_le_iff₀ hK0]
    nlinarith
  have h1 : (‖a - b‖ / ‖a - c‖) ^ (1 / K) ≤ L ^ K :=
    (Real.rpow_le_rpow hρ0 hρL (by positivity)).trans (Real.rpow_le_rpow_of_exponent_le hL hKi)
  have h2 : (‖a - b‖ / ‖a - c‖) ^ K ≤ L ^ K := Real.rpow_le_rpow hρ0 hρL hK0.le
  have h3 := hqs a b c hac
  rw [div_le_iff₀ hFac] at h3
  have h4 : C * max ((‖a - b‖ / ‖a - c‖) ^ (1 / K)) ((‖a - b‖ / ‖a - c‖) ^ K) ≤ C * L ^ K :=
    mul_le_mul_of_nonneg_left (max_le h1 h2) hC.le
  nlinarith

/-- P4.3 helper (w4): points of the unit circle. -/
theorem s07d_p4_g_sph (t : ℝ) : Complex.exp (t * Complex.I) ∈ sphere (0 : ℂ) 1 := by
  rw [mem_sphere_zero_iff_norm, Complex.norm_exp_ofReal_mul_I]

/-- P4.3 helper (w4): the distance of two image points is bounded by the length of the image
arc. -/
theorem s07d_p4_g_low {F : ℂ → ℂ} (hF : Continuous F) {s t u v : ℝ} (hst : s ≤ t)
    (hu : u ∈ Icc s t) (hv : v ∈ Icc s t) :
    ENNReal.ofReal ‖F (Complex.exp (u * Complex.I)) - F (Complex.exp (v * Complex.I))‖ ≤
      μH[1] (F '' ((fun t : ℝ => Complex.exp (t * Complex.I)) '' Icc s t)) := by
  have _h := hst
  have hc : Continuous fun t : ℝ => Complex.exp (t * Complex.I) := by fun_prop
  have hpc : IsPreconnected (F '' ((fun t : ℝ => Complex.exp (t * Complex.I)) '' Icc s t)) :=
    (isPreconnected_Icc.image _ hc.continuousOn).image F hF.continuousOn
  have h := hpc.edist_le_hausdorffMeasure
    (mem_image_of_mem F (mem_image_of_mem (fun t : ℝ => Complex.exp (t * Complex.I)) hu))
    (mem_image_of_mem F (mem_image_of_mem (fun t : ℝ => Complex.exp (t * Complex.I)) hv))
  rw [edist_dist, dist_eq_norm] at h
  exact h

/-- P4.3 helper (w4): the upper Ahlfors bound for subsets of the curve inside a closed disc. -/
theorem s07d_p4_g_ball {F : ℂ → ℂ} {M : ℝ}
    (hAR : ∀ z : ℂ, ∀ r : ℝ, 0 < r → μH[1] (F '' sphere 0 1 ∩ ball z r) ≤ ENNReal.ofReal (M * r))
    {S : Set ℂ} {p : ℂ} {R : ℝ} (hR : 0 < R) (hS : S ⊆ F '' sphere 0 1)
    (hSp : S ⊆ closedBall p R) : μH[1] S ≤ ENNReal.ofReal (M * (2 * R)) :=
  (measure_mono (subset_inter hS (hSp.trans (closedBall_subset_ball (by linarith))))).trans
    (hAR p (2 * R) (by linarith))

/-- P4.3 helper (w4): arc images lie on the curve. -/
theorem s07d_p4_g_onC {F : ℂ → ℂ} (X : Set ℝ) :
    F '' ((fun t : ℝ => Complex.exp (t * Complex.I)) '' X) ⊆ F '' sphere 0 1 := by
  rintro w ⟨z, ⟨t, -, rfl⟩, rfl⟩
  exact mem_image_of_mem F (s07d_p4_g_sph t)

/-- P4.3 helper (w4): `ν` of a closed interval of length `≤ 2π` is at most the length of its image
arc (the endpoint is a `ν`-null singleton). -/
theorem s07d_p4_g_nuIcc {F : ℂ → ℂ} {ν : Measure ℝ}
    (hν : ∀ a : ℝ, ∀ E ⊆ Ico a (a + 2 * π), MeasurableSet E →
      ν E = μH[1] (F '' ((fun t : ℝ => Complex.exp (t * Complex.I)) '' E)))
    {a b : ℝ} (hab : b - a ≤ 2 * π) :
    ν (Icc a b) ≤ μH[1] (F '' ((fun t : ℝ => Complex.exp (t * Complex.I)) '' Icc a b)) := by
  have hpi := Real.pi_pos
  have hsub : Icc a b ⊆ Ico a b ∪ {b} := fun t ht => by
    rcases eq_or_lt_of_le ht.2 with h | h
    · exact Or.inr h
    · exact Or.inl ⟨ht.1, h⟩
  have h1 : ν (Ico a b) ≤ μH[1] (F '' ((fun t : ℝ => Complex.exp (t * Complex.I)) '' Icc a b)) := by
    rw [hν a (Ico a b) (fun t ht => ⟨ht.1, by linarith [ht.2]⟩) measurableSet_Ico]
    exact measure_mono (image_mono (image_mono Ico_subset_Icc_self))
  have h2 : ν {b} = 0 := by
    rw [hν b {b} (fun t ht => by
      rw [mem_singleton_iff.1 ht]
      exact ⟨le_rfl, by linarith⟩) (measurableSet_singleton b), image_singleton, image_singleton]
    haveI := Measure.nullSingletonClass_hausdorff (X := ℂ) one_pos
    exact measure_singleton _
  calc ν (Icc a b) ≤ ν (Ico a b ∪ {b}) := measure_mono hsub
    _ ≤ ν (Ico a b) + ν {b} := measure_union_le _ _
    _ ≤ _ := by rw [h2, add_zero]; exact h1

/-- P4.3 helper (w4): `ν` is locally finite. -/
theorem s07d_p4_g_fin {F : ℂ → ℂ} {ν : Measure ℝ} {M : ℝ} (hF : Continuous F)
    (hAR : ∀ z : ℂ, ∀ r : ℝ, 0 < r → μH[1] (F '' sphere 0 1 ∩ ball z r) ≤ ENNReal.ofReal (M * r))
    (hν : ∀ a : ℝ, ∀ E ⊆ Ico a (a + 2 * π), MeasurableSet E →
      ν E = μH[1] (F '' ((fun t : ℝ => Complex.exp (t * Complex.I)) '' E)))
    (a b : ℝ) : ν (Icc a b) ≠ ⊤ := by
  have hpi := Real.pi_pos
  obtain ⟨R, hR, hRb⟩ := ((isCompact_sphere (0 : ℂ) 1).image hF).isBounded.subset_ball_lt 0 0
  have hW : ∀ k : ℕ, ν (Ico (a + 2 * π * k) (a + 2 * π * k + 2 * π)) ≤
      ENNReal.ofReal (M * R) := fun k => by
    rw [hν _ _ subset_rfl measurableSet_Ico]
    exact (measure_mono (subset_inter (s07d_p4_g_onC _) ((s07d_p4_g_onC _).trans hRb))).trans
      (hAR 0 R hR)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (b - a) / (2 * π) < N := exists_nat_gt _
  have hcov : Icc a b ⊆ ⋃ k ∈ Finset.range N, Ico (a + 2 * π * k) (a + 2 * π * k + 2 * π) := by
    intro t ht
    have hp : (0 : ℝ) < 2 * π := by linarith
    have h0 : 0 ≤ (t - a) / (2 * π) := div_nonneg (by linarith [ht.1]) hp.le
    have hf1 := Nat.floor_le h0
    have hf2 := Nat.lt_floor_add_one ((t - a) / (2 * π))
    rw [le_div_iff₀ hp] at hf1
    rw [div_lt_iff₀ hp] at hf2
    refine mem_iUnion₂.2 ⟨⌊(t - a) / (2 * π)⌋₊, Finset.mem_range.2 ?_, ?_, ?_⟩
    · have h3 : (t - a) / (2 * π) ≤ (b - a) / (2 * π) :=
        div_le_div_of_nonneg_right (by linarith [ht.2]) hp.le
      have h4 : (⌊(t - a) / (2 * π)⌋₊ : ℝ) < N := lt_of_le_of_lt (Nat.floor_le h0) (by linarith)
      exact_mod_cast h4
    · have e : (⌊(t - a) / (2 * π)⌋₊ : ℝ) * (2 * π) = 2 * π * ⌊(t - a) / (2 * π)⌋₊ := by ring
      linarith
    · have e : ((⌊(t - a) / (2 * π)⌋₊ : ℝ) + 1) * (2 * π) =
          2 * π * ⌊(t - a) / (2 * π)⌋₊ + 2 * π := by ring
      linarith
  refine ne_top_of_le_ne_top ?_ ((measure_mono hcov).trans (measure_biUnion_finset_le _ _))
  refine ne_top_of_le_ne_top ?_ (Finset.sum_le_sum fun k _ => hW k)
  rw [Finset.sum_const, nsmul_eq_mul]
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top

/-- P4.3 helper (w4): the chord between two points of the unit circle. -/
theorem s07d_p4_g_chordE (u v : ℝ) :
    ‖Complex.exp (u * Complex.I) - Complex.exp (v * Complex.I)‖ =
      ‖Complex.exp (Complex.I * ((v - u : ℝ) : ℂ)) - 1‖ := by
  have e1 : Complex.exp (v * Complex.I) =
      Complex.exp (u * Complex.I) * Complex.exp (Complex.I * ((v - u : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e1, show Complex.exp (u * Complex.I) -
      Complex.exp (u * Complex.I) * Complex.exp (Complex.I * ((v - u : ℝ) : ℂ)) =
      -(Complex.exp (u * Complex.I) * (Complex.exp (Complex.I * ((v - u : ℝ) : ℂ)) - 1)) by ring,
    norm_neg, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- P4.3 helper (w4): lower chord bound `‖e^{iu} - e^{iv}‖ ≥ (2/π)(v - u)` for `0 ≤ v - u ≤ π`. -/
theorem s07d_p4_g_chordL {u v : ℝ} (h0 : 0 ≤ v - u) (h1 : v - u ≤ π) :
    2 / π * (v - u) ≤ ‖Complex.exp (u * Complex.I) - Complex.exp (v * Complex.I)‖ := by
  have hpi := Real.pi_pos
  rw [s07d_p4_g_chordE, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hs := Real.mul_le_sin (x := (v - u) / 2) (by linarith) (by linarith)
  have hs0 : 0 ≤ Real.sin ((v - u) / 2) := le_trans (by positivity) hs
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hs0, abs_two]
  have e : 2 / π * (v - u) = 2 * (2 / π * ((v - u) / 2)) := by ring
  rw [e]
  linarith

/-- P4.3 helper (w4): upper chord bound `‖e^{iu} - e^{iv}‖ ≤ |v - u|`. -/
theorem s07d_p4_g_chordU (u v : ℝ) :
    ‖Complex.exp (u * Complex.I) - Complex.exp (v * Complex.I)‖ ≤ |v - u| := by
  rw [s07d_p4_g_chordE]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := v - u)
  rw [Real.norm_eq_abs] at h
  exact h

/-- P4.3 helper (w4): image arcs inside an `L ≤ 2π`-interval sit in a closed disc of radius
`C π^K ‖F(e^{im}) - F(e^{ia})‖` about the image of the midpoint, on the doubled interval. -/
theorem s07d_p4_g_dball {K C : ℝ} {F : ℂ → ℂ} (hK : 1 ≤ K) (hC : 0 < C)
    (hqs : ∀ a b c : ℂ, a ≠ c → ‖F a - F b‖ / ‖F a - F c‖ ≤
      C * max ((‖a - b‖ / ‖a - c‖) ^ (1 / K)) ((‖a - b‖ / ‖a - c‖) ^ K))
    (hFi : Function.Injective F) {a b : ℝ} (hab : a < b) (hL : b - a ≤ 2 * π) :
    F '' ((fun t : ℝ => Complex.exp (t * Complex.I)) ''
        Icc (a - (b - a) / 2) (b + (b - a) / 2)) ⊆
      closedBall (F (Complex.exp (((a + b) / 2 : ℝ) * Complex.I)))
        (C * π ^ K * ‖F (Complex.exp (((a + b) / 2 : ℝ) * Complex.I)) -
          F (Complex.exp (a * Complex.I))‖) := by
  have hpi := Real.pi_pos
  rintro w ⟨z, ⟨s, hs, rfl⟩, rfl⟩
  rw [mem_closedBall, dist_comm, dist_eq_norm]
  have hc1 := s07d_p4_g_chordL (u := a) (v := (a + b) / 2) (by linarith) (by linarith)
  have hne : Complex.exp (((a + b) / 2 : ℝ) * Complex.I) ≠ Complex.exp (a * Complex.I) := by
    intro h
    rw [h, sub_self, norm_zero] at hc1
    have : 0 < 2 / π * ((a + b) / 2 - a) := by
      have : 0 < (a + b) / 2 - a := by linarith
      positivity
    linarith
  have hc2 := s07d_p4_g_chordU ((a + b) / 2) s
  have habs : |s - (a + b) / 2| ≤ b - a := abs_le.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hr : ‖Complex.exp (((a + b) / 2 : ℝ) * Complex.I) - Complex.exp (s * Complex.I)‖ ≤
      π * ‖Complex.exp (((a + b) / 2 : ℝ) * Complex.I) - Complex.exp (a * Complex.I)‖ := by
    have h3 : ‖Complex.exp (a * Complex.I) - Complex.exp (((a + b) / 2 : ℝ) * Complex.I)‖ =
        ‖Complex.exp (((a + b) / 2 : ℝ) * Complex.I) - Complex.exp (a * Complex.I)‖ := norm_sub_rev _ _
    rw [h3] at hc1
    have h4 : π * (2 / π * ((a + b) / 2 - a)) = b - a := by
      field_simp
      ring
    nlinarith
  exact s07d_p4_g_qs hK hC hqs hFi (by linarith [Real.pi_gt_three]) hne hr

/-- P4.3 helper (w4): the doubling bound. -/
theorem s07d_p4_g_doub {K C M : ℝ} {F : ℂ → ℂ} {ν : Measure ℝ} (hK : 1 ≤ K) (hC : 0 < C)
    (hM : 0 < M)
    (hqs : ∀ a b c : ℂ, a ≠ c → ‖F a - F b‖ / ‖F a - F c‖ ≤
      C * max ((‖a - b‖ / ‖a - c‖) ^ (1 / K)) ((‖a - b‖ / ‖a - c‖) ^ K))
    (hFi : Function.Injective F) (hFc : Continuous F)
    (hAR : ∀ z : ℂ, ∀ r : ℝ, 0 < r → μH[1] (F '' sphere 0 1 ∩ ball z r) ≤ ENNReal.ofReal (M * r))
    (hν : ∀ a : ℝ, ∀ E ⊆ Ico a (a + 2 * π), MeasurableSet E →
      ν E = μH[1] (F '' ((fun t : ℝ => Complex.exp (t * Complex.I)) '' E)))
    {a b : ℝ} (hab : a < b) (hL : b - a ≤ 2 * π) :
    ν (Icc (a - (b - a) / 2) (b + (b - a) / 2)) ≤
      ENNReal.ofReal (4 * M * (C * π ^ K)) * ν (Icc a b) := by
  have hpi := Real.pi_pos
  set m : ℝ := (a + b) / 2 with hm
  set d : ℝ := ‖F (Complex.exp ((m : ℝ) * Complex.I)) - F (Complex.exp (a * Complex.I))‖ with hd
  have hc1 := s07d_p4_g_chordL (u := a) (v := m) (by linarith) (by linarith)
  have hd0 : 0 < d := by
    rw [hd]
    refine norm_pos_iff.2 (sub_ne_zero.2 fun h => ?_)
    have h' := hFi h
    rw [h', sub_self, norm_zero] at hc1
    have : 0 < 2 / π * (m - a) := by
      have : 0 < m - a := by linarith
      positivity
    linarith
  have hball := s07d_p4_g_dball hK hC hqs hFi hab hL
  set R : ℝ := C * π ^ K * d with hR
  have hR0 : 0 < R := by positivity
  set p : ℝ := a - (b - a) / 2 with hp
  set q : ℝ := b + (b - a) / 2 with hq
  set q1 : ℝ := min (p + 2 * π) q with hq1
  have hsplit : Icc p q ⊆ Icc p q1 ∪ Icc q1 q := fun t ht => by
    rcases le_total t q1 with h | h
    · exact Or.inl ⟨ht.1, h⟩
    · exact Or.inr ⟨h, ht.2⟩
  have hq1p : q1 - p ≤ 2 * π := by
    have := min_le_left (p + 2 * π) q
    linarith
  have hqq1 : q - q1 ≤ 2 * π := by
    rcases le_total (p + 2 * π) q with h | h
    · rw [hq1, min_eq_left h]
      linarith
    · rw [hq1, min_eq_right h]
      linarith
  have hq1q : q1 ≤ q := min_le_right _ _
  have hpq1 : p ≤ q1 := le_min (by linarith) (by linarith)
  have hpiece : ∀ u v : ℝ, p ≤ u → v ≤ q → v - u ≤ 2 * π →
      ν (Icc u v) ≤ ENNReal.ofReal (M * (2 * R)) := fun u v hu hv huv => by
    refine (s07d_p4_g_nuIcc hν huv).trans (s07d_p4_g_ball hAR
      (p := F (Complex.exp (((a + b) / 2 : ℝ) * Complex.I))) hR0 (s07d_p4_g_onC _) ?_)
    refine (image_mono (image_mono (Icc_subset_Icc hu hv))).trans ?_
    exact hball
  have hJ : ENNReal.ofReal d ≤ ν (Icc a b) := by
    have h1 := s07d_p4_g_low hFc (s := a) (t := m) (by linarith) (right_mem_Icc.2 (by linarith))
      (left_mem_Icc.2 (by linarith))
    rw [← hν a (Icc a m) (fun t ht => ⟨ht.1, by linarith [ht.2]⟩) measurableSet_Icc] at h1
    exact h1.trans (measure_mono (Icc_subset_Icc le_rfl (by linarith)))
  calc ν (Icc p q) ≤ ν (Icc p q1 ∪ Icc q1 q) := measure_mono hsplit
    _ ≤ ν (Icc p q1) + ν (Icc q1 q) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (M * (2 * R)) + ENNReal.ofReal (M * (2 * R)) :=
        add_le_add (hpiece p q1 le_rfl hq1q hq1p) (hpiece q1 q hpq1 le_rfl hqq1)
    _ = ENNReal.ofReal (4 * M * (C * π ^ K)) * ENNReal.ofReal d := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul
          (by positivity), hR]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (4 * M * (C * π ^ K)) * ν (Icc a b) := by gcongr

/-- P4.3 helper (w4): for `F` extending `ψ`, `F y ∈ V` only for `y ∈ 𝔻`. -/
theorem s07d_p4_g_inV {V : Set ℂ} {ψ F : ℂ → ℂ} (hψ : IsConformalOnto ψ unitDisc V)
    (hFi : Function.Injective F) (hFψ : EqOn F ψ unitDisc) {y : ℂ} (hy : F y ∈ V) :
    y ∈ unitDisc := by
  rw [← hψ.2.2] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  have h : F x = F y := by rw [hFψ hx, hxy]
  rw [← hFi h]
  exact hx

/-- P4.3 helper (w4): the upper bound `ν(J) ≤ c |J| |ψ'(z_J)|`. -/
theorem s07d_p4_g_upper {K C M : ℝ} {V : Set ℂ} {ψ F : ℂ → ℂ} {ν : Measure ℝ} (hK : 1 ≤ K)
    (hC : 0 < C) (hM : 0 < M)
    (hqs : ∀ a b c : ℂ, a ≠ c → ‖F a - F b‖ / ‖F a - F c‖ ≤
      C * max ((‖a - b‖ / ‖a - c‖) ^ (1 / K)) ((‖a - b‖ / ‖a - c‖) ^ K))
    (hFi : Function.Injective F)
    (hAR : ∀ z : ℂ, ∀ r : ℝ, 0 < r → μH[1] (F '' sphere 0 1 ∩ ball z r) ≤ ENNReal.ofReal (M * r))
    (hν : ∀ a : ℝ, ∀ E ⊆ Ico a (a + 2 * π), MeasurableSet E →
      ν E = μH[1] (F '' ((fun t : ℝ => Complex.exp (t * Complex.I)) '' E)))
    (hψ : IsConformalOnto ψ unitDisc V) (hFψ : EqOn F ψ unitDisc) (hFs : F '' univ = univ)
    {a b : ℝ} (hab : a < b) (hL : b - a ≤ 2 * π) :
    ν (Icc a b) ≤ ENNReal.ofReal (2 * M * (C * (1 + π) ^ K) / π * (b - a) *
      ‖deriv ψ (((1 - (b - a) / (2 * π) : ℝ) : ℂ) *
        Complex.exp (((a + b) / 2 : ℝ) * Complex.I))‖) := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  set ρ : ℝ := 1 - (b - a) / (2 * π) with hρ
  set m : ℝ := (a + b) / 2 with hm
  have hρ0 : 0 ≤ ρ := by
    rw [hρ, sub_nonneg, div_le_one (by linarith)]
    exact hL
  have hLρ : 1 - ρ = (b - a) / (2 * π) := by rw [hρ]; ring
  have hρ1 : ρ < 1 := by
    have : 0 < (b - a) / (2 * π) := div_pos (by linarith) (by linarith)
    linarith
  set z : ℂ := (ρ : ℂ) * Complex.exp (m * Complex.I) with hz
  have hzn : ‖z‖ = ρ := by
    rw [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_of_nonneg hρ0]
  have hzD : z ∈ unitDisc := by
    show z ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, hzn]
    exact hρ1
  have hVc : ∀ w ∈ Vᶜ, ∃ y : ℂ, 1 ≤ ‖y‖ ∧ F y = w := by
    intro w hw
    have hw' : w ∈ F '' univ := by rw [hFs]; exact mem_univ w
    obtain ⟨y, -, rfl⟩ := hw'
    refine ⟨y, ?_, rfl⟩
    by_contra h
    push_neg at h
    have hyD : y ∈ unitDisc := by
      show y ∈ ball (0 : ℂ) 1
      exact mem_ball_zero_iff.2 h
    exact hw (by rw [← hψ.2.2, hFψ hyD]; exact mem_image_of_mem ψ hyD)
  have hne : (Vᶜ).Nonempty := by
    refine ⟨F 1, fun h => ?_⟩
    have := s07d_p4_g_inV hψ hFi hFψ h
    have h1 : ‖(1 : ℂ)‖ < 1 := mem_ball_zero_iff.1 this
    rw [norm_one] at h1
    exact lt_irrefl _ h1
  set A : ℝ := C * (1 + π) ^ K with hA
  have hA0 : 0 < A := by positivity
  have hkey : ∀ s ∈ Icc a b, ‖F z - F (Complex.exp (s * Complex.I))‖ ≤
      A * infDist (ψ z) Vᶜ := by
    intro s hs
    have h1 : ‖F z - F (Complex.exp (s * Complex.I))‖ / A ≤ infDist (ψ z) Vᶜ := by
      refine (le_infDist hne).2 fun w hw => ?_
      obtain ⟨y, hy1, rfl⟩ := hVc w hw
      have hzy0 : (b - a) / (2 * π) ≤ ‖z - y‖ := by
        have := norm_sub_norm_le y z
        rw [norm_sub_rev y z, hzn] at this
        linarith
      have hzy : z ≠ y := by
        intro h
        rw [h, sub_self, norm_zero] at hzy0
        have : 0 < (b - a) / (2 * π) := div_pos (by linarith) (by linarith)
        linarith
      have hze : ‖z - Complex.exp (m * Complex.I)‖ = (b - a) / (2 * π) := by
        rw [hz, show (ρ : ℂ) * Complex.exp (m * Complex.I) - Complex.exp (m * Complex.I) =
          ((ρ - 1 : ℝ) : ℂ) * Complex.exp (m * Complex.I) by push_cast; ring, norm_mul,
          Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonpos (by linarith)]
        linarith
      have hes := s07d_p4_g_chordU m s
      have habs : |s - m| ≤ (b - a) / 2 := abs_le.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have htri : ‖z - Complex.exp (s * Complex.I)‖ ≤ (1 + π) * ‖z - y‖ := by
        have h2 := norm_sub_le_norm_sub_add_norm_sub z (Complex.exp (m * Complex.I))
          (Complex.exp (s * Complex.I))
        have h3 : (b - a) / 2 = π * ((b - a) / (2 * π)) := by field_simp
        nlinarith
      have hq := s07d_p4_g_qs hK hC hqs hFi (by linarith) hzy htri
      rw [div_le_iff₀ hA0, dist_eq_norm, ← hFψ hzD]
      rw [hA]
      linarith
    rw [div_le_iff₀ hA0] at h1
    linarith
  have hkoebe := (lem_koebe_a hψ hzD).1
  have h1z : 1 - ‖z‖ ^ 2 ≤ (b - a) / π := by
    rw [hzn]
    have : (b - a) / π = 2 * (1 - ρ) := by rw [hLρ]; field_simp
    nlinarith
  set R : ℝ := A * ((b - a) / π) * ‖deriv ψ z‖ with hR
  have hbound : ∀ s ∈ Icc a b, ‖F z - F (Complex.exp (s * Complex.I))‖ ≤ R := by
    intro s hs
    have h2 := hkey s hs
    have h3 : infDist (ψ z) Vᶜ ≤ (b - a) / π * ‖deriv ψ z‖ :=
      hkoebe.trans (mul_le_mul_of_nonneg_right h1z (norm_nonneg _))
    rw [hR]
    nlinarith
  have hR0 : 0 < R := by
    have h2 := hbound a (left_mem_Icc.2 hab.le)
    have hza : z ≠ Complex.exp (a * Complex.I) := by
      intro h
      have := congrArg norm h
      rw [hzn, Complex.norm_exp_ofReal_mul_I] at this
      linarith
    have h3 : 0 < ‖F z - F (Complex.exp (a * Complex.I))‖ :=
      norm_pos_iff.2 (sub_ne_zero.2 fun h => hza (hFi h))
    linarith
  have hball : F '' ((fun t : ℝ => Complex.exp (t * Complex.I)) '' Icc a b) ⊆
      closedBall (F z) R := by
    rintro w ⟨y, ⟨s, hs, rfl⟩, rfl⟩
    rw [mem_closedBall, dist_comm, dist_eq_norm]
    exact hbound s hs
  refine (s07d_p4_g_nuIcc hν (by linarith)).trans
    ((s07d_p4_g_ball hAR hR0 (s07d_p4_g_onC _) hball).trans (le_of_eq ?_))
  congr 1
  rw [hR, hA]
  ring

/-- P4.3 helper (w4): the Whitney bound `∫_I |ψ'(r e^{it})| dt ≤ C_W ν(3I)`. -/
theorem s07d_p4_g_whit {K C : ℝ} {V : Set ℂ} {ψ F : ℂ → ℂ} {ν : Measure ℝ} (hK : 1 ≤ K)
    (hC : 0 < C)
    (hqs : ∀ a b c : ℂ, a ≠ c → ‖F a - F b‖ / ‖F a - F c‖ ≤
      C * max ((‖a - b‖ / ‖a - c‖) ^ (1 / K)) ((‖a - b‖ / ‖a - c‖) ^ K))
    (hFi : Function.Injective F) (hFc : Continuous F)
    (hν : ∀ a : ℝ, ∀ E ⊆ Ico a (a + 2 * π), MeasurableSet E →
      ν E = μH[1] (F '' ((fun t : ℝ => Complex.exp (t * Complex.I)) '' E)))
    (hfin : ∀ a b : ℝ, ν (Icc a b) ≠ ⊤)
    (hψ : IsConformalOnto ψ unitDisc V) (hFψ : EqOn F ψ unitDisc)
    {a b r : ℝ} (hab : a < b) (hr0 : 0 ≤ r) (hr : 1 - (b - a) ≤ r) (hr1 : r < 1) :
    ENNReal.ofReal (∫ t in a..b, ‖deriv ψ ((r : ℂ) * Complex.exp (t * Complex.I))‖) ≤
      ENNReal.ofReal (8 * (C * π ^ K)) * ν (Icc (a - (b - a)) (b + (b - a))) := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  set h : ℝ := 1 - r with hh
  have hh0 : 0 < h := by linarith
  have hh1 : h ≤ 1 := by linarith
  have hhL : h ≤ b - a := by linarith
  have hDo : IsOpen unitDisc := (isOpen_ball : IsOpen (ball (0 : ℂ) 1))
  have hmemr : ∀ t : ℝ, (r : ℂ) * Complex.exp (t * Complex.I) ∈ unitDisc := fun t => by
    show (r : ℂ) * Complex.exp (t * Complex.I) ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_of_nonneg hr0]
    exact hr1
  set c : ℝ := 4 * (C * π ^ K) with hc
  have hc0 : 0 < c := by positivity
  have hpt : ∀ t : ℝ, ENNReal.ofReal ‖deriv ψ ((r : ℂ) * Complex.exp (t * Complex.I))‖ ≤
      ENNReal.ofReal (c / h) * ν (Icc (t - h) (t + h)) := by
    intro t
    set z : ℂ := (r : ℂ) * Complex.exp (t * Complex.I) with hz
    have hzD := hmemr t
    have hzn : ‖z‖ = r := by
      rw [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_of_nonneg hr0]
    have het : F (Complex.exp (t * Complex.I)) ∈ Vᶜ := by
      intro hin
      have h1 := mem_ball_zero_iff.1 (s07d_p4_g_inV hψ hFi hFψ hin)
      rw [Complex.norm_exp_ofReal_mul_I] at h1
      exact lt_irrefl _ h1
    have hk := (lem_koebe_a hψ hzD).2.1
    have hd : infDist (ψ z) Vᶜ ≤ ‖F (Complex.exp (t * Complex.I)) - F z‖ :=
      calc infDist (ψ z) Vᶜ ≤ dist (ψ z) (F (Complex.exp (t * Complex.I))) :=
            infDist_le_dist_of_mem het
        _ = ‖F (Complex.exp (t * Complex.I)) - F z‖ := by
            rw [dist_eq_norm, norm_sub_rev, hFψ hzD]
    have hcl := s07d_p4_g_chordL (u := t) (v := t + h) (by linarith) (by linarith)
    have hez : ‖Complex.exp (t * Complex.I) - z‖ = h := by
      rw [hz, show Complex.exp (t * Complex.I) - (r : ℂ) * Complex.exp (t * Complex.I) =
        ((1 - r : ℝ) : ℂ) * Complex.exp (t * Complex.I) by push_cast; ring, norm_mul,
        Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
    have hne : Complex.exp (t * Complex.I) ≠ Complex.exp (((t + h : ℝ) : ℂ) * Complex.I) := by
      intro he
      rw [he, sub_self, norm_zero] at hcl
      have : 0 < 2 / π * (t + h - t) := by
        have : 0 < t + h - t := by linarith
        positivity
      linarith
    have hratio : ‖Complex.exp (t * Complex.I) - z‖ ≤
        π * ‖Complex.exp (t * Complex.I) - Complex.exp (((t + h : ℝ) : ℂ) * Complex.I)‖ := by
      rw [hez]
      have e : π * (2 / π * (t + h - t)) = 2 * h := by field_simp; ring
      nlinarith
    have hq := s07d_p4_g_qs hK hC hqs hFi (by linarith) hne hratio
    have hX := s07d_p4_g_low hFc (s := t) (t := t + h) (u := t) (v := t + h) (by linarith)
      (left_mem_Icc.2 (by linarith)) (right_mem_Icc.2 (by linarith))
    rw [← hν t (Icc t (t + h)) (fun x hx => ⟨hx.1, by linarith [hx.2]⟩) measurableSet_Icc] at hX
    have hX2 : ν (Icc t (t + h)) ≤ ν (Icc (t - h) (t + h)) :=
      measure_mono (Icc_subset_Icc (by linarith) le_rfl)
    set X : ℝ := ‖F (Complex.exp (t * Complex.I)) -
      F (Complex.exp (((t + h : ℝ) : ℂ) * Complex.I))‖ with hXdef
    have h1r : h ≤ 1 - ‖z‖ ^ 2 := by
      rw [hzn, hh]
      nlinarith
    have hmain : ‖deriv ψ z‖ ≤ c / h * X := by
      have h2 : h * ‖deriv ψ z‖ ≤ (1 - ‖z‖ ^ 2) * ‖deriv ψ z‖ :=
        mul_le_mul_of_nonneg_right h1r (norm_nonneg _)
      have h3 : h * ‖deriv ψ z‖ ≤ c * X := by
        rw [hc]
        linarith
      rw [div_mul_eq_mul_div, le_div_iff₀ hh0]
      linarith
    calc ENNReal.ofReal ‖deriv ψ z‖ ≤ ENNReal.ofReal (c / h * X) := ENNReal.ofReal_le_ofReal hmain
      _ = ENNReal.ofReal (c / h) * ENNReal.ofReal X := ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal (c / h) * ν (Icc (t - h) (t + h)) := by
          gcongr
          exact hX.trans hX2
  have hfc : Continuous fun t : ℝ => ‖deriv ψ ((r : ℂ) * Complex.exp (t * Complex.I))‖ :=
    ((hψ.1.deriv hDo).continuousOn.comp_continuous (by fun_prop) hmemr).norm
  have hint : IntegrableOn (fun t : ℝ => ‖deriv ψ ((r : ℂ) * Complex.exp (t * Complex.I))‖)
      (Ioc a b) volume := hfc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [intervalIntegral.integral_of_le hab.le,
    ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun t => norm_nonneg _)]
  calc (∫⁻ t in Ioc a b, ENNReal.ofReal ‖deriv ψ ((r : ℂ) * Complex.exp (t * Complex.I))‖)
      ≤ ∫⁻ t in Icc a b, ENNReal.ofReal ‖deriv ψ ((r : ℂ) * Complex.exp (t * Complex.I))‖ :=
        lintegral_mono_set Ioc_subset_Icc_self
    _ ≤ ∫⁻ t in Icc a b, ENNReal.ofReal (c / h) * ν (Icc (t - h) (t + h)) :=
        lintegral_mono fun t => hpt t
    _ = ENNReal.ofReal (c / h) * ∫⁻ t in Icc a b, ν (Icc (t - h) (t + h)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (c / h) * (ENNReal.ofReal (2 * h) * ν (Icc (a - h) (b + h))) := by
        gcongr
        exact s07d_p4_jl_fub hfin hh0.le
    _ = ENNReal.ofReal (8 * (C * π ^ K)) * ν (Icc (a - h) (b + h)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [hc]
        field_simp
        norm_num
    _ ≤ ENNReal.ofReal (8 * (C * π ^ K)) * ν (Icc (a - (b - a)) (b + (b - a))) := by
        gcongr

/-- **P4.3** (`geom`): for the Riemann map `ψ` of a quasidisk with global `K`-q.c. extension `F`
and `M`-upper-Ahlfors-regular boundary `F(∂𝔻)`, the pullback `ν` of arclength is locally finite,
doubling, bounded above by `c |J| |ψ'(z_J)|` on arcs, and dominates the Whitney integrals
`∫_I |ψ'(r e^{it})| dt` (`1 - |I| ≤ r < 1`) of the tripled arc. -/
theorem s07d_p4_geom {K M : ℝ} (hK : 1 ≤ K) (hM : 0 < M) :
    ∃ C c D : ℝ, 0 < C ∧ 0 < c ∧ 1 ≤ D ∧
    ∀ (V : Set ℂ) (ψ F : ℂ → ℂ) (ν : Measure ℝ), IsConformalOnto ψ unitDisc V →
      IsKQC F univ K → F '' univ = univ → EqOn F ψ unitDisc →
      (∀ z : ℂ, ∀ r : ℝ, 0 < r → μH[1] (F '' sphere 0 1 ∩ ball z r) ≤ ENNReal.ofReal (M * r)) →
      (∀ a : ℝ, ∀ E ⊆ Ico a (a + 2 * π), MeasurableSet E →
        ν E = μH[1] (F '' ((fun t : ℝ => Complex.exp (t * Complex.I)) '' E))) →
      (∀ a b : ℝ, ν (Icc a b) ≠ ⊤) ∧
      (∀ a b : ℝ, a < b → b - a ≤ 2 * π →
        ν (Icc (a - (b - a) / 2) (b + (b - a) / 2)) ≤ ENNReal.ofReal D * ν (Icc a b)) ∧
      (∀ a b : ℝ, a < b → b - a ≤ 2 * π →
        ν (Icc a b) ≤ ENNReal.ofReal (c * (b - a) *
          ‖deriv ψ (((1 - (b - a) / (2 * π) : ℝ) : ℂ) *
            Complex.exp (((a + b) / 2 : ℝ) * Complex.I))‖)) ∧
      (∀ a b r : ℝ, a < b → b - a ≤ 2 * π → 0 ≤ r → 1 - (b - a) ≤ r → r < 1 →
        ENNReal.ofReal (∫ t in a..b, ‖deriv ψ ((r : ℂ) * Complex.exp (t * Complex.I))‖) ≤
          ENNReal.ofReal C * ν (Icc (a - (b - a)) (b + (b - a)))) := by
  obtain ⟨C₃, hC₃, hqs3⟩ := lem_three_point K hK
  refine ⟨8 * (C₃ * π ^ K), 2 * M * (C₃ * (1 + π) ^ K) / π, max 1 (4 * M * (C₃ * π ^ K)),
    by positivity, by positivity, le_max_left _ _, ?_⟩
  intro V ψ F ν hψ hF hFs hFψ hAR hν
  have hqs : ∀ a b c : ℂ, a ≠ c → ‖F a - F b‖ / ‖F a - F c‖ ≤
      C₃ * max ((‖a - b‖ / ‖a - c‖) ^ (1 / K)) ((‖a - b‖ / ‖a - c‖) ^ K) :=
    fun a b c h => (hqs3 F hF hFs a b c h).1
  have hFi : Function.Injective F := fun x y h => hF.2.2.1.2.1 (mem_univ x) (mem_univ y) h
  have hFc : Continuous F := continuousOn_univ.mp hF.2.2.1.1
  have hfin := s07d_p4_g_fin hFc hAR hν
  refine ⟨hfin, fun a b hab hL => ?_,
    fun a b hab hL => s07d_p4_g_upper hK hC₃ hM hqs hFi hAR hν hψ hFψ hFs hab hL,
    fun a b r hab _ hr0 hr hr1 => s07d_p4_g_whit hK hC₃ hqs hFi hFc hν hfin hψ hFψ hab hr0 hr hr1⟩
  refine (s07d_p4_g_doub hK hC₃ hM hqs hFi hFc hAR hν hab hL).trans ?_
  gcongr
  exact le_max_right _ _

/-! ### P4.6 (w4): assembly -/

/-- P4.6 helper (w4): the derivative of a conformal map of `𝔻` does not vanish (Koebe). -/
theorem s07d_p4_as_dne {V : Set ℂ} {ψ : ℂ → ℂ} (hψ : IsConformalOnto ψ unitDisc V) {z : ℂ}
    (hz : z ∈ unitDisc) : deriv ψ z ≠ 0 := by
  have h1 := (lem_koebe_a hψ hz).1
  have h2 := s02_infDist_pos hψ (show ψ z ∈ V by rw [← hψ.2.2]; exact mem_image_of_mem ψ hz)
  intro h
  rw [h, norm_zero, mul_zero] at h1
  linarith

/-- **P4 add-on** (`lavrentiev_nu`, leader-approved 2026-11-06). `s07d_p4_lavrentiev` in the measure form
of `s07d_p4_nu`/`s07d_p4_core`: the arclength pullback `ν` itself, locally finite and weakly `A∞`
on intervals of length `≤ 2π`. This is P4.1 + P4.2 + P4.3 + P4.4 + P4.5 assembled. The consumer is P6
via P7 `s07d_p7_meas`. -/
theorem s07d_p4_lavrentiev_nu (K M : ℝ) (hK : 1 ≤ K) (hM : 0 < M) :
    ∃ δ₀ η₀ : ℝ, 0 < δ₀ ∧ 0 < η₀ ∧ η₀ < 1 ∧
    ∀ (V : Set ℂ) (ψ G : ℂ → ℂ), IsConformalOnto ψ unitDisc V → IsKQC G univ K →
      G '' univ = univ → G '' unitDisc = V → ψ 0 = G 0 →
      (∀ z : ℂ, ∀ r : ℝ, 0 < r → μH[1] (G '' sphere 0 1 ∩ ball z r) ≤ ENNReal.ofReal (M * r)) →
      ∃ (F : ℂ → ℂ) (ν : Measure ℝ), IsKQC F univ (K * K) ∧ F '' univ = univ ∧ EqOn F ψ unitDisc ∧
        (∀ a : ℝ, ∀ E ⊆ Ico a (a + 2 * π), MeasurableSet E →
          ν E = μH[1] (F '' ((fun t : ℝ => Complex.exp (t * Complex.I)) '' E))) ∧
        (∀ a b : ℝ, ν (Icc a b) ≠ ⊤) ∧
        ∀ a b : ℝ, a < b → b - a ≤ 2 * π → ∀ E ⊆ Icc a b, MeasurableSet E →
          volume E ≤ ENNReal.ofReal (δ₀ * (b - a)) →
          ν E ≤ ENNReal.ofReal (1 - η₀) * ν (Icc a b) := by
  have hKK : 1 ≤ K * K := by nlinarith
  obtain ⟨C, c, D, hC, hc, hD, hgeom⟩ := s07d_p4_geom hKK hM
  obtain ⟨C₀, hjen⟩ := s07d_p4_jensen hC
  obtain ⟨δ₀, η₀, hδ, hη, hη1, hcore⟩ := s07d_p4_core (C₀ := C₀) hc hD
  refine ⟨δ₀, η₀, hδ, hη, hη1, fun V ψ G hψ hG hGs hGV hψ0 hAR => ?_⟩
  have hpi := Real.pi_pos
  obtain ⟨F, hF, hFs, hFψ, hFS⟩ := s07d_p4_ext hψ hG hGs hGV hψ0
  have hARF : ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      μH[1] (F '' sphere 0 1 ∩ ball z r) ≤ ENNReal.ofReal (M * r) := by
    rw [hFS]
    exact hAR
  have hFc : Continuous F := continuousOn_univ.mp hF.2.2.1.1
  have hFinj : InjOn F (sphere 0 1) := fun x _ y _ h =>
    hF.2.2.1.2.1 (mem_univ x) (mem_univ y) h
  obtain ⟨ν, hν⟩ := s07d_p4_nu hFc hFinj
  obtain ⟨hfin, hdoub, hup, hwh⟩ := hgeom V ψ F ν hψ hF hFs hFψ hARF hν
  have hDo : IsOpen unitDisc := (isOpen_ball : IsOpen (ball (0 : ℂ) 1))
  have hdne : ∀ z ∈ unitDisc, deriv ψ z ≠ 0 := fun z hz => s07d_p4_as_dne hψ hz
  have hjen' := hjen (deriv ψ) ν (hψ.1.deriv hDo) hdne hfin hwh
  have hup' : ∀ a b : ℝ, a < b → b - a ≤ 2 * π →
      ν (Icc a b) ≤ ENNReal.ofReal (c * (b - a) * Real.exp
        (Real.log ‖deriv ψ (((1 - (b - a) / (2 * π) : ℝ) : ℂ) *
          Complex.exp (((a + b) / 2 : ℝ) * Complex.I))‖)) := by
    intro a b hab hL
    have hρ0 : 0 ≤ 1 - (b - a) / (2 * π) := by
      rw [sub_nonneg, div_le_one (by linarith)]
      exact hL
    have hρ1 : 1 - (b - a) / (2 * π) < 1 := by
      have : 0 < (b - a) / (2 * π) := div_pos (by linarith) (by linarith)
      linarith
    have hz : (((1 - (b - a) / (2 * π) : ℝ) : ℂ) *
        Complex.exp (((a + b) / 2 : ℝ) * Complex.I)) ∈ unitDisc := by
      show (((1 - (b - a) / (2 * π) : ℝ) : ℂ) *
        Complex.exp (((a + b) / 2 : ℝ) * Complex.I)) ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_of_nonneg hρ0]
      exact hρ1
    rw [Real.exp_log (norm_pos_iff.2 (hdne _ hz))]
    exact hup a b hab hL
  refine ⟨F, ν, hF, hFs, hFψ, hν, hfin, ?_⟩
  exact hcore ν (fun t => (ν.rnDeriv volume t).toReal)
    (fun r φ => Real.log ‖deriv ψ ((r : ℂ) * Complex.exp (φ * Complex.I))‖) hfin hdoub
    (Measure.measurable_rnDeriv ν volume).ennreal_toReal (fun t => ENNReal.toReal_nonneg)
    (fun E hE => s07d_p4_jl_wle E hE) hjen' hup'

/-- **P4** (`lavrentiev`, consumer-facing): for a quasidisk `V = G(𝔻)` (`G` a global `K`-q.c.
map) with `M`-upper-Ahlfors-regular boundary, the Riemann map `ψ` has a global `K²`-q.c.
extension `F` for which arclength on `∂V` is weakly `A∞` against harmonic measure at `ψ(0)`:
`|E| ≤ δ₀ |J| ⇒ μH[1](F(E)) ≤ (1 - η₀) μH[1](F(J))` for arcs `J` and measurable `E ⊆ J`, with
`δ₀, η₀` depending only on `(K, M)`. -/
theorem s07d_p4_lavrentiev (K M : ℝ) (hK : 1 ≤ K) (hM : 0 < M) :
    ∃ δ₀ η₀ : ℝ, 0 < δ₀ ∧ 0 < η₀ ∧ η₀ < 1 ∧
    ∀ (V : Set ℂ) (ψ G : ℂ → ℂ), IsConformalOnto ψ unitDisc V → IsKQC G univ K →
      G '' univ = univ → G '' unitDisc = V → ψ 0 = G 0 →
      (∀ z : ℂ, ∀ r : ℝ, 0 < r → μH[1] (G '' sphere 0 1 ∩ ball z r) ≤ ENNReal.ofReal (M * r)) →
      ∃ F : ℂ → ℂ, IsKQC F univ (K * K) ∧ F '' univ = univ ∧ EqOn F ψ unitDisc ∧
        ∀ a b : ℝ, a < b → b - a ≤ 2 * π → ∀ E ⊆ circleArc a b, MeasurableSet E →
          circleLen E ≤ ENNReal.ofReal δ₀ * circleLen (circleArc a b) →
          μH[1] (F '' E) ≤ ENNReal.ofReal (1 - η₀) * μH[1] (F '' circleArc a b) := by
  obtain ⟨δ₀, η₀, hδ, hη, hη1, h⟩ := s07d_p4_lavrentiev_nu K M hK hM
  refine ⟨δ₀, η₀, hδ, hη, hη1, fun V ψ G hψ hG hGs hGV hψ0 hAR => ?_⟩
  obtain ⟨F, ν, hF, hFs, hFψ, hν, hfin, hA⟩ := h V ψ G hψ hG hGs hGV hψ0 hAR
  refine ⟨F, hF, hFs, hFψ, fun a b hab hL E hE hEm hlen => ?_⟩
  have hpi := Real.pi_pos
  have hec : Continuous fun θ : ℝ => Complex.exp (θ * Complex.I) := by fun_prop
  obtain ⟨E₁, hE₁⟩ : ∃ E₁ : Set ℝ, E₁ = Ico a (a + 2 * π) ∩ Icc a b ∩
      (fun θ : ℝ => Complex.exp (θ * Complex.I)) ⁻¹' E := ⟨_, rfl⟩
  have hE₁m : MeasurableSet E₁ := by
    rw [hE₁]
    exact (measurableSet_Ico.inter measurableSet_Icc).inter (hEm.preimage hec.measurable)
  have hE₁W : E₁ ⊆ Ico a (a + 2 * π) := fun t ht => by
    rw [hE₁] at ht
    exact ht.1.1
  have hE₁J : E₁ ⊆ Icc a b := fun t ht => by
    rw [hE₁] at ht
    exact ht.1.2
  have hE₁img : (fun θ : ℝ => Complex.exp (θ * Complex.I)) '' E₁ = E := by
    ext x
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      rw [hE₁] at hθ
      exact hθ.2
    · intro hx
      have hx' : x ∈ (fun θ : ℝ => Complex.exp (θ * Complex.I)) '' Icc a b := hE hx
      obtain ⟨θ, hθ, rfl⟩ := hx'
      by_cases hθ2 : θ < a + 2 * π
      · refine ⟨θ, ?_, rfl⟩
        rw [hE₁]
        exact ⟨⟨⟨hθ.1, hθ2⟩, hθ⟩, hx⟩
      · have hθe : θ = a + 2 * π := le_antisymm (by linarith [hθ.2]) (not_lt.1 hθ2)
        have hper : Complex.exp (θ * Complex.I) = Complex.exp (a * Complex.I) := by
          rw [hθe, show (((a + 2 * π : ℝ) : ℂ) * Complex.I) =
            (a : ℂ) * Complex.I + 2 * π * Complex.I by push_cast; ring, Complex.exp_add,
            Complex.exp_two_pi_mul_I, mul_one]
        refine ⟨a, ?_, hper.symm⟩
        rw [hE₁]
        refine ⟨⟨⟨le_rfl, by linarith⟩, ⟨le_rfl, hab.le⟩⟩, ?_⟩
        show Complex.exp (a * Complex.I) ∈ E
        rw [← hper]
        exact hx
  have hvol : volume E₁ = circleLen E := by
    rw [← hE₁img]
    exact (s07_circleLen_exp_image a E₁ hE₁m fun t ht => ⟨(hE₁W ht).1, (hE₁W ht).2.le⟩).symm
  have hlenarc : circleLen (circleArc a b) = ENNReal.ofReal (b - a) := by
    show circleLen ((fun θ : ℝ => Complex.exp (θ * Complex.I)) '' Icc a b) = _
    rw [s07_circleLen_exp_image a (Icc a b) measurableSet_Icc (Icc_subset_Icc le_rfl (by linarith)),
      Real.volume_Icc]
  have hE₁vol : volume E₁ ≤ ENNReal.ofReal (δ₀ * (b - a)) := by
    rw [hvol, ENNReal.ofReal_mul hδ.le, ← hlenarc]
    exact hlen
  have h1 := hA a b hab hL E₁ hE₁J hE₁m hE₁vol
  have hνE₁ : ν E₁ = μH[1] (F '' E) := by
    rw [hν a E₁ hE₁W hE₁m, hE₁img]
  have hνJ : ν (Icc a b) ≤ μH[1] (F '' circleArc a b) := s07d_p4_g_nuIcc hν hL
  rw [← hνE₁]
  exact h1.trans (mul_le_mul_of_nonneg_left hνJ zero_le)


/-- P1 helper (Poisson representation, S07c kernel form; Mathlib `DiffContOnCl.circleAverage_poissonKernel_smul`). -/
theorem s07d_p1_poisson {u : ℂ → ℂ} (hu : DiffContOnCl ℂ u (ball (0 : ℂ) 1)) {z : ℂ} (hz : z ∈ unitDisc) :
    u z = ((2 * π)⁻¹ : ℝ) • ∫ t in (0 : ℝ)..2 * π,
      ((1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 : ℝ) • u (Complex.exp (t * I)) := by
  have h := hu.circleAverage_poissonKernel_smul (c := 0) hz
  rw [Real.circleAverage_def] at h
  rw [← h]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hc : circleMap 0 1 t = Complex.exp (t * I) := by simp [circleMap]
  rw [hc, Pi.smul_apply', poissonKernel_def, sub_zero, sub_zero, Complex.norm_exp_ofReal_mul_I, one_pow]

/-- P1 helper (LP lower bound for polynomials): `∫₀^{2π} |Σ_{m<N} a_{m+1} e^{i(m+1)t}|² ≤
4 ∫_𝔻 (1 - |z|²) |Σ_{m<N} (m+1) a_{m+1} z^m|²` (coefficientwise `(m+1)/(2(m+2)) ≥ 1/4`). -/
theorem s07d_p1_lp_poly (a : ℕ → ℂ) (N : ℕ) :
    ∫ t in (0 : ℝ)..2 * π, ‖∑ m ∈ Finset.range N, a (m + 1) * Complex.exp (t * I) ^ (m + 1)‖ ^ 2 ≤
      4 * ∫ z in unitDisc, (1 - ‖z‖ ^ 2) *
        ‖∑ m ∈ Finset.range N, ((m + 1 : ℕ) : ℂ) * a (m + 1) * z ^ m‖ ^ 2 := by
  have h1 := s12_circle_parseval (Finset.range N) (fun m => m + 1)
    (fun _ _ _ _ h => Nat.succ_injective h) (fun m => a (m + 1)) zero_le_one
  have h2 := s02_vd_disc_parseval (fun t => 1 - t ^ 2) (by fun_prop)
    (fun m => ((m + 1 : ℕ) : ℂ) * a (m + 1)) N
  simp only [s02_vd_radial1] at h2
  rw [Real.circleAverage_def] at h1
  have hc : ∀ θ : ℝ, circleMap 0 1 θ = Complex.exp (θ * I) := fun θ => by simp [circleMap]
  simp only [hc, one_pow, mul_one, smul_eq_mul] at h1
  have hpi := Real.pi_pos
  have hL : ∫ t in (0 : ℝ)..2 * π, ‖∑ m ∈ Finset.range N, a (m + 1) * Complex.exp (t * I) ^ (m + 1)‖ ^ 2 =
      2 * π * ∑ m ∈ Finset.range N, ‖a (m + 1)‖ ^ 2 := by
    rw [← h1, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  rw [hL, h2, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [norm_mul, Complex.norm_natCast, mul_pow]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hA := sq_nonneg ‖a (m + 1)‖
  push_cast
  rw [show 4 * (2 * π * (((m : ℝ) + 1) ^ 2 * ‖a (m + 1)‖ ^ 2 *
      (1 / (2 * ((m : ℝ) + 1) * ((m : ℝ) + 2))))) =
      2 * π * ‖a (m + 1)‖ ^ 2 * (2 * ((m : ℝ) + 1) / ((m : ℝ) + 2)) by field_simp; ring]
  exact le_mul_of_one_le_right (by positivity) ((one_le_div (by positivity)).mpr (by linarith))

/-- P1 helper: a uniform limit on `D̄` of continuous functions passes to `∫₀^{2π} |P_N(e^{it}) - c|²`. -/
theorem s07d_p1_circle_lim {P : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hP : ∀ N, Continuous (P N)) (hf : ContinuousOn f (closedBall 0 1))
    (hU : TendstoUniformlyOn P f atTop (closedBall 0 1)) (c : ℂ) :
    Tendsto (fun N => ∫ t in (0 : ℝ)..2 * π, ‖P N (Complex.exp (t * I)) - c‖ ^ 2) atTop
      (𝓝 (∫ t in (0 : ℝ)..2 * π, ‖f (Complex.exp (t * I)) - c‖ ^ 2)) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hf
  have hmem : ∀ t : ℝ, Complex.exp (t * I) ∈ closedBall (0 : ℂ) 1 := fun t => by
    rw [mem_closedBall_zero_iff, Complex.norm_exp_ofReal_mul_I]
  have hEc : Continuous fun t : ℝ => Complex.exp (t * I) := by fun_prop
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => (M + 1 + ‖c‖) ^ 2) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun N =>
      ((((hP N).comp hEc).sub continuous_const).norm.pow 2).aestronglyMeasurable
  · filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hU) 1 one_pos] with N hN
    refine Eventually.of_forall fun t _ => ?_
    have h1 : ‖P N (Complex.exp (t * I))‖ ≤ M + 1 := by
      have := hN _ (hmem t)
      rw [dist_eq_norm] at this
      linarith [norm_sub_norm_le (P N (Complex.exp (t * I))) (f (Complex.exp (t * I))),
        hM _ (hmem t), norm_sub_rev (f (Complex.exp (t * I))) (P N (Complex.exp (t * I)))]
    rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((norm_sub_le _ _).trans (by linarith)) 2
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t _ =>
      (((hU.tendsto_at (hmem t)).sub tendsto_const_nhds).norm.pow 2)

/-- P1 helper (LP lower bound, `[Garsia]` step): for `F` holomorphic on `𝔻` and `0 < r < 1`,
`∫₀^{2π} |F(r e^{it}) - F(0)|² ≤ 4 ∫_𝔻 (1 - |z|²) |r F'(rz)|²` (dilated Taylor polynomials as in S02
`s02_vd_dilate`). -/
theorem s07d_p1_lp {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F unitDisc) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) :
    ∫ t in (0 : ℝ)..2 * π, ‖F ((r : ℂ) * Complex.exp (t * I)) - F 0‖ ^ 2 ≤
      4 * ∫ z in unitDisc, (1 - ‖z‖ ^ 2) * ‖(r : ℂ) * deriv F ((r : ℂ) * z)‖ ^ 2 := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, c = fun n => ((n.factorial : ℂ))⁻¹ * iteratedDeriv n F 0 :=
    ⟨_, rfl⟩
  have hs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (F z) := by
    intro z hz
    have h := hasSum_taylorSeries_on_ball hF hz
    simp only [sub_zero, smul_eq_mul] at h
    convert h using 2 with n
    simp only [hc]
    ring
  have hc0 : c 0 = F 0 := by simp [hc]
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
  have hL1 := (s07d_p1_circle_lim (fun N => continuous_finsetSum _ fun n _ => by fun_prop) hc1 hU1
    (F 0)).comp (tendsto_add_atTop_nat 1)
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
  have hpN : ∀ N : ℕ, ∫ t in (0 : ℝ)..2 * π,
      ‖∑ n ∈ Finset.range (N + 1), c n * (r : ℂ) ^ n * Complex.exp (t * I) ^ n - F 0‖ ^ 2 ≤
      4 * (r ^ 2 * ∫ z in unitDisc, (1 - ‖z‖ ^ 2) *
        ‖∑ m ∈ Finset.range N, c (m + 1) * ((m + 1 : ℕ) : ℂ) * (r : ℂ) ^ m * z ^ m‖ ^ 2) := by
    intro N
    have h := s07d_p1_lp_poly (fun n => c n * (r : ℂ) ^ n) N
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
    refine le_of_eq_of_le (intervalIntegral.integral_congr fun t _ => ?_) h
    rw [Finset.sum_range_succ', pow_zero, pow_zero, mul_one, mul_one, hc0, add_sub_cancel_right]
  have hR : ∫ z in unitDisc, (1 - ‖z‖ ^ 2) * ‖(r : ℂ) * deriv F ((r : ℂ) * z)‖ ^ 2 =
      r ^ 2 * ∫ z in unitDisc, (1 - ‖z‖ ^ 2) * ‖deriv F ((r : ℂ) * z)‖ ^ 2 := by
    rw [← integral_const_mul]
    congr 1
    funext z
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    ring
  rw [hR]
  exact le_of_tendsto_of_tendsto' hL1 ((hL2.const_mul (r ^ 2)).const_mul 4) hpN
/-- P1 helper: `1 - w̄ ζ ≠ 0` and `1 + w̄ ζ ≠ 0` for `|w| < 1`, `|ζ| ≤ 1`. -/
theorem s07d_p1_den {w ζ : ℂ} (hw : ‖w‖ < 1) (hζ : ‖ζ‖ ≤ 1) :
    (1 : ℂ) - conj w * ζ ≠ 0 ∧ (1 : ℂ) + conj w * ζ ≠ 0 := by
  have h : ‖conj w * ζ‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg w, norm_nonneg ζ]
  constructor
  · intro h0
    rw [show conj w * ζ = 1 by linear_combination -h0, norm_one] at h
    exact lt_irrefl _ h
  · intro h0
    rw [show conj w * ζ = -1 by linear_combination h0, norm_neg, norm_one] at h
    exact lt_irrefl _ h

/-- P1 helper: `τ_w` maps `∂𝔻` to `∂𝔻`. -/
theorem s07d_p1_mob_norm {w ζ : ℂ} (hw : ‖w‖ < 1) (hζ : ‖ζ‖ = 1) :
    ‖(ζ + w) / (1 + conj w * ζ)‖ = 1 := by
  have e : (1 : ℂ) + conj w * ζ = ζ * conj (ζ + w) := by
    rw [map_add, mul_add, Complex.mul_conj', hζ]
    push_cast
    ring
  have h0 : ζ + w ≠ 0 := by
    intro h
    have : ‖ζ‖ = ‖w‖ := by rw [eq_neg_of_add_eq_zero_left h, norm_neg]
    linarith
  rw [e, norm_div, norm_mul, Complex.norm_conj, hζ, one_mul, div_self (norm_ne_zero_iff.mpr h0)]

/-- P1 helper (Möbius change of variables on `∂𝔻`): for `w ∈ 𝔻` and `τ_w(y) = (y + w)/(1 + w̄ y)`,
`∫₀^{2π} P_w(t) G(e^{it}) dt = ∫₀^{2π} G(τ_w(e^{is})) ds` (S07c `s07c_fkps_m6_mob` with `c = -w`, `s07c_fkps_m6_cov`). -/
theorem s07d_p1_mob_circle {w : ℂ} (hw : w ∈ unitDisc) (G : ℂ → ℝ)
    (hf : Continuous fun s : ℝ => G ((Complex.exp (s * I) + w) / (1 + conj w * Complex.exp (s * I)))) :
    ∫ t in (0 : ℝ)..2 * π, (1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 * G (Complex.exp (t * I)) =
      ∫ s in (0 : ℝ)..2 * π, G ((Complex.exp (s * I) + w) / (1 + conj w * Complex.exp (s * I))) := by
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hpi := Real.pi_pos
  obtain ⟨h1, h2, h3, h4, h5⟩ := s07c_fkps_m6_mob (c := -w) (by rwa [norm_neg])
  set Φ : ℝ → ℝ := fun t => t + 2 * arg (1 + -w * Complex.exp (-(t * I))) with hΦ
  set f : ℝ → ℝ := fun s => G ((Complex.exp (s * I) + w) / (1 + conj w * Complex.exp (s * I))) with hfdef
  have hn : (1 : ℂ) - conj w * w ≠ 0 := s07c_fkps_m6_rn_w4_num hw1
  have hinv : ∀ ζ : ℂ, ‖ζ‖ = 1 →
      ((ζ - w) / (1 - conj w * ζ) + w) / (1 + conj w * ((ζ - w) / (1 - conj w * ζ))) = ζ := by
    intro ζ hζ
    have hd := (s07d_p1_den hw1 hζ.le).1
    have e1 : (ζ - w) / (1 - conj w * ζ) + w = ζ * (1 - conj w * w) / (1 - conj w * ζ) := by
      rw [eq_div_iff hd, add_mul, div_mul_cancel₀ _ hd]
      ring
    have e2 : 1 + conj w * ((ζ - w) / (1 - conj w * ζ)) = (1 - conj w * w) / (1 - conj w * ζ) := by
      rw [eq_div_iff hd, add_mul, mul_assoc, div_mul_cancel₀ _ hd]
      ring
    rw [e1, e2, div_div_div_cancel_right₀ hd, mul_div_cancel_right₀ _ hn]
  have hkey : ∀ t : ℝ, f (Φ t) = G (Complex.exp (t * I)) := by
    intro t
    have e : (Complex.exp (t * I) - w) / (1 - conj w * Complex.exp (t * I)) =
        Complex.exp (((t + 2 * arg (1 + -w * Complex.exp (-(t * I))) : ℝ) : ℂ) * I) := by
      rw [← h1 t, map_neg]
      congr 1; ring
    show G ((Complex.exp (((t + 2 * arg (1 + -w * Complex.exp (-(t * I))) : ℝ) : ℂ) * I) + w) /
      (1 + conj w * Complex.exp (((t + 2 * arg (1 + -w * Complex.exp (-(t * I))) : ℝ) : ℂ) * I))) = _
    rw [← e, hinv _ (Complex.norm_exp_ofReal_mul_I t)]
  have hper : Function.Periodic f (2 * π) := by
    intro s
    show G _ = G _
    rw [show (((s + 2 * π : ℝ) : ℂ) * I) = (s : ℂ) * I + 2 * π * I by push_cast; ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hcov := s07c_fkps_m6_cov (f := f) (t₁ := 0) (t₂ := 2 * π) (by positivity) h4 h2 h3
    (hf.integrableOn_Icc)
  have hΦ2 : Φ (2 * π) = Φ 0 + 2 * π := by
    have := h5 0
    simp only [zero_add] at this
    show 2 * π + 2 * arg (1 + -w * Complex.exp (-(((2 * π : ℝ) : ℂ) * I))) =
      0 + 2 * arg (1 + -w * Complex.exp (-(((0 : ℝ) : ℂ) * I))) + 2 * π
    linarith
  rw [hΦ2, hper.intervalIntegral_add_eq (Φ 0) 0, zero_add] at hcov
  rw [hcov]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [hkey, norm_neg, ← sub_eq_add_neg, mul_comm]

/-- P1 helper (Möbius change of variables in `𝔻`): for `w ∈ 𝔻`, `τ_w(y) = (y + w)/(1 + w̄ y)` and `g`
holomorphic on `𝔻`, `∫_𝔻 (1-|y|²)|(g∘τ_w)'|² = ∫_𝔻 (1-|x|²)|g'(x)|² (1-|w|²)/|1-w̄x|²` (S07c `s07c_fkps_m6_rn_cov`). -/
theorem s07d_p1_mob_area {w : ℂ} (hw : w ∈ unitDisc) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) :
    ∫⁻ y in unitDisc, ENNReal.ofReal ((1 - ‖y‖ ^ 2) *
        ‖deriv (fun v => g ((v + w) / (1 + conj w * v))) y‖ ^ 2) =
      ∫⁻ x in unitDisc, ENNReal.ofReal ((1 - ‖x‖ ^ 2) * ‖deriv g x‖ ^ 2 *
        ((1 - ‖w‖ ^ 2) / ‖1 - conj w * x‖ ^ 2)) := by
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  conv_rhs => rw [s07c_fkps_m6_rn_cov (z := w) (φ := fun v => (v + w) / (1 + conj w * v)) (fun _ => rfl) hw]
  refine setLIntegral_congr_fun measurableSet_ball fun y hy => ?_
  have hy1 : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
  have hden := (s07c_fkps_m6_rn_w4_den hw1 hy1).1
  have hτ := s07c_fkps_m6_rn_w4_hd_add hden
  have hτm : (y + w) / (1 + conj w * y) ∈ unitDisc := mem_ball_zero_iff.mpr (s07c_fkps_m6_rn_w4_mem_add hw1 hy1)
  have hgd : HasDerivAt g (deriv g ((y + w) / (1 + conj w * y))) ((y + w) / (1 + conj w * y)) :=
    (hg.differentiableAt (isOpen_ball.mem_nhds hτm)).hasDerivAt
  have hdc : deriv (fun v => g ((v + w) / (1 + conj w * v))) y = deriv g ((y + w) / (1 + conj w * y)) *
      ((1 - conj w * w) / (1 + conj w * y) ^ 2) := (hgd.comp y hτ).deriv
  rw [hdc]
  have hpp := (s07c_fkps_m6_rn_w4_pullpt (z := w) (φ := fun v => (v + w) / (1 + conj w * v)) (fun _ => rfl)
    hw (a := 0) (by simp [unitDisc]) hy).1
  have hq : (1 : ℂ) - conj w * w = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']
    push_cast
    ring
  have hq0 : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hs0 : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
  have hD : 0 < ‖1 + conj w * y‖ := norm_pos_iff.mpr hden
  have hτ1 : 1 - conj w * ((y + w) / (1 + conj w * y)) = (1 - conj w * w) / (1 + conj w * y) := by
    rw [eq_div_iff hden, sub_mul, mul_assoc, div_mul_cancel₀ _ hden]
    ring
  have hτn : ‖1 - conj w * ((y + w) / (1 + conj w * y))‖ = (1 - ‖w‖ ^ 2) / ‖1 + conj w * y‖ := by
    rw [hτ1, norm_div, hq, Complex.norm_real, Real.norm_of_nonneg hq0.le]
  have hpp' : 1 - ‖(y + w) / (1 + conj w * y)‖ ^ 2 = (1 - ‖y‖ ^ 2) * ((1 - ‖w‖ ^ 2) / ‖1 + conj w * y‖ ^ 2) := by
    rw [← hpp]
    field_simp
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [hτn, hpp', norm_mul, norm_div, norm_pow, hq, Complex.norm_real, Real.norm_of_nonneg hq0.le]
  field_simp

/-- P1 helper (dilation): for `Ψ ≥ 0` measurable and `0 < r ≤ 1`,
`∫_𝔻 (1-|z|²) r² Ψ(rz) dA ≤ ∫_{B(0,r)} (1-|u|²) Ψ(u) dA` (`u = rz`, `1 - |u|²/r² ≤ 1 - |u|²`; cf. S02 `s02_vd_scale`). -/
theorem s07d_p1_scale (Ψ : ℂ → ℝ) (hΨ : Measurable Ψ) (hΨ0 : ∀ u, 0 ≤ Ψ u) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r ≤ 1) :
    ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) * (r ^ 2 * Ψ ((r : ℂ) * z))) ≤
      ∫⁻ u in ball (0 : ℂ) r, ENNReal.ofReal ((1 - ‖u‖ ^ 2) * Ψ u) := by
  have hr' : r ≠ 0 := hr0.ne'
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ → ℝ≥0∞, ψ = (ball (0 : ℂ) r).indicator fun u =>
      ENNReal.ofReal (r ^ 2 * ((1 - ‖u‖ ^ 2 / r ^ 2) * Ψ u)) := ⟨_, rfl⟩
  have hψm : Measurable ψ := by
    rw [hψ]
    exact (ENNReal.measurable_ofReal.comp (by fun_prop)).indicator measurableSet_ball
  have hpt : ∀ z : ℂ, unitDisc.indicator (fun z => ENNReal.ofReal ((1 - ‖z‖ ^ 2) *
      (r ^ 2 * Ψ ((r : ℂ) * z)))) z = ψ (r • z) := by
    intro z
    have hn : ‖r • z‖ = r * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg hr0.le]
    rw [hψ]
    by_cases hz : z ∈ unitDisc
    · have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      rw [Set.indicator_of_mem hz,
        Set.indicator_of_mem (mem_ball_zero_iff.mpr (by rw [hn]; nlinarith))]
      congr 1
      rw [hn, Complex.real_smul]
      field_simp
    · have hz1 : ¬ ‖z‖ < 1 := fun h => hz (mem_ball_zero_iff.mpr h)
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h => hz1 (by
        have := mem_ball_zero_iff.mp h
        rw [hn] at this
        nlinarith))]
  have hmap := Measure.map_addHaar_smul (volume : Measure ℂ) hr'
  rw [Complex.finrank_real_complex] at hmap
  calc ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) * (r ^ 2 * Ψ ((r : ℂ) * z)))
      = ∫⁻ z, ψ (r • z) := by
        rw [← lintegral_indicator (s := unitDisc) measurableSet_ball]
        exact lintegral_congr hpt
    _ = ∫⁻ u, ψ u ∂(Measure.map (fun z : ℂ => r • z) volume) :=
        (lintegral_map hψm (measurable_const_smul r)).symm
    _ = ENNReal.ofReal |(r ^ 2)⁻¹| * ∫⁻ u, ψ u := by rw [hmap, lintegral_smul_measure, smul_eq_mul]
    _ = ∫⁻ u in ball (0 : ℂ) r, ENNReal.ofReal ((1 - ‖u‖ ^ 2 / r ^ 2) * Ψ u) := by
        rw [hψ, lintegral_indicator measurableSet_ball,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun u => ?_
        rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (inv_pos.mpr (pow_pos hr0 2))]
        congr 1
        field_simp
    _ ≤ ∫⁻ u in ball (0 : ℂ) r, ENNReal.ofReal ((1 - ‖u‖ ^ 2) * Ψ u) := by
        refine setLIntegral_mono' measurableSet_ball fun u hu => ?_
        apply ENNReal.ofReal_le_ofReal
        have hu1 : ‖u‖ < r := mem_ball_zero_iff.mp hu
        have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hr0.le hr1
        have hrp : 0 < r ^ 2 := pow_pos hr0 2
        have h2 : 1 - ‖u‖ ^ 2 / r ^ 2 ≤ 1 - ‖u‖ ^ 2 := by
          have : ‖u‖ ^ 2 ≤ ‖u‖ ^ 2 / r ^ 2 := by
            rw [le_div_iff₀ hrp]
            nlinarith [mul_le_mul_of_nonneg_left hr2 (sq_nonneg ‖u‖)]
          linarith
        exact mul_le_mul_of_nonneg_right h2 (hΨ0 u)

/-- P1 helper (kernel test, S07 `lem_kernel_test_b`): if `|φ'|²(1-|z|²) dA` has Carleson constant `A`, then
`∫_𝔻 (1-|u|²)|φ'(u)|² (1-|w|²)/|1-w̄u|² ≤ 80 A` for `w ∈ 𝔻`. -/
theorem s07d_p1_kernel {φ : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hC : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
        derivCarlesonMeasure (deriv φ) (unitDisc ∩ ball ζ r) ≤ ENNReal.ofReal (A * r))
    {w : ℂ} (hw : w ∈ unitDisc) :
    ∫⁻ u in unitDisc, ENNReal.ofReal ((1 - ‖u‖ ^ 2) * ‖deriv φ u‖ ^ 2 *
      ((1 - ‖w‖ ^ 2) / ‖1 - conj w * u‖ ^ 2)) ≤ ENNReal.ofReal (80 * A) := by
  set f : ℂ → ℝ≥0∞ := fun u => ENNReal.ofReal (‖deriv φ u‖ ^ 2) with hf
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp ((measurable_deriv φ).norm.pow_const 2)
  set m : Measure ℂ := volume.withDensity f with hm
  have hD : MeasurableSet (unitDisc : Set ℂ) := measurableSet_ball
  have hv : Measurable fun z : ℂ => ENNReal.ofReal (varpi z) :=
    ENNReal.measurable_ofReal.comp ((show (varpi : ℂ → ℝ) = fun z => 1 - ‖z‖ ^ 2 from rfl) ▸
      (by fun_prop))
  have hk : Measurable fun z : ℂ => ENNReal.ofReal (diskKernel w z) :=
    ENNReal.measurable_ofReal.comp ((show (diskKernel w : ℂ → ℝ) =
      fun z => (1 - ‖w‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖1 - conj w * z‖ ^ 2 from rfl) ▸ (by fun_prop))
  have hvm : varpiMeasure m = derivCarlesonMeasure (deriv φ) := by
    rw [varpiMeasure, hm, restrict_withDensity hD, ← withDensity_mul _ hfm hv, derivCarlesonMeasure]
    congr 1
    funext z
    simp only [Pi.mul_apply, hf, varpi]
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  have hcn : carlesonNorm (varpiMeasure m) ≤ ENNReal.ofReal A := by
    rw [hvm, carlesonNorm]
    refine iSup₂_le fun ζ hζ => iSup₂_le fun r hr => ?_
    refine ENNReal.div_le_of_le_mul ?_
    rw [← ENNReal.ofReal_mul hA]
    exact hC ζ hζ r hr.1 hr.2
  have hP : poissonP m w ≤ ENNReal.ofReal (80 * A) := by
    calc poissonP m w ≤ ⨆ a ∈ unitDisc, poissonP m a := le_iSup₂ (f := fun a _ => poissonP m a) w hw
      _ ≤ 80 * carlesonNorm (varpiMeasure m) := (lem_kernel_test_b m).2
      _ ≤ 80 * ENNReal.ofReal A := by gcongr
      _ = ENNReal.ofReal (80 * A) := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
  refine le_trans (le_of_eq ?_) hP
  rw [poissonP, hm, setLIntegral_withDensity_eq_setLIntegral_mul _ hfm hk hD]
  refine setLIntegral_congr_fun hD fun u _ => ?_
  simp only [Pi.mul_apply, hf, diskKernel, varpi]
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  ring

/-- P1 helper: the Poisson-kernel comparison under dilation, `(1-|w|²)/|1-w̄u/r|² ≤ 4 (1-|w|²)/|1-w̄u|²`
for `|u| < r` and `1 - r ≤ (1-|w|)/4`. -/
theorem s07d_p1_kdil {w u : ℂ} (hw : ‖w‖ < 1) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hrw : 1 - r ≤ (1 - ‖w‖) / 4) (hu : ‖u‖ < r) :
    (1 - ‖w‖ ^ 2) / ‖1 - conj w * (u / r)‖ ^ 2 ≤ 4 * ((1 - ‖w‖ ^ 2) / ‖1 - conj w * u‖ ^ 2) := by
  have hq : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hur : ‖u / (r : ℂ)‖ = ‖u‖ / r := by rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have hur1 : ‖u‖ / r ≤ 1 := (div_le_one hr0).mpr hu.le
  have hd : 1 - ‖w‖ ≤ ‖1 - conj w * (u / r)‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) (conj w * (u / r))
    rw [norm_one, norm_mul, Complex.norm_conj, hur] at h1
    nlinarith [norm_nonneg w, div_nonneg (norm_nonneg u) hr0.le]
  have hed : ‖(1 - conj w * u) - (1 - conj w * (u / r))‖ ≤ 1 - r := by
    have hc : 0 ≤ 1 / r - 1 := by rw [sub_nonneg, le_div_iff₀ hr0]; linarith
    have e : (1 - conj w * u) - (1 - conj w * (u / r)) = conj w * (u * (((1 / r - 1 : ℝ)) : ℂ)) := by
      push_cast
      field_simp
      ring
    rw [e, norm_mul, Complex.norm_conj, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
    have h2 : ‖u‖ * (1 / r - 1) ≤ r * (1 / r - 1) := mul_le_mul_of_nonneg_right hu.le hc
    have h3 : r * (1 / r - 1) = 1 - r := by field_simp
    nlinarith [norm_nonneg w, mul_nonneg (norm_nonneg u) hc]
  have hdpos : 0 < ‖1 - conj w * (u / r)‖ := by linarith
  have he : ‖1 - conj w * u‖ ≤ 2 * ‖1 - conj w * (u / r)‖ := by
    have := norm_add_le (1 - conj w * (u / r)) ((1 - conj w * u) - (1 - conj w * (u / r)))
    rw [add_sub_cancel] at this
    linarith
  have hepos : 0 < ‖1 - conj w * u‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) (conj w * u)
    rw [norm_one, norm_mul, Complex.norm_conj] at h1
    have h2 : ‖w‖ * ‖u‖ < 1 := by nlinarith [norm_nonneg w, norm_nonneg u]
    linarith
  have h4 : ‖1 - conj w * u‖ ^ 2 / 4 ≤ ‖1 - conj w * (u / r)‖ ^ 2 := by nlinarith
  calc (1 - ‖w‖ ^ 2) / ‖1 - conj w * (u / r)‖ ^ 2 ≤ (1 - ‖w‖ ^ 2) / (‖1 - conj w * u‖ ^ 2 / 4) :=
        div_le_div_of_nonneg_left hq (by positivity) h4
    _ = 4 * ((1 - ‖w‖ ^ 2) / ‖1 - conj w * u‖ ^ 2) := by field_simp

/-- P1 helper (Garsia, dilation + kernel step): under the Carleson hypothesis with constant `A`, for `w ∈ 𝔻` and
`1 - r ≤ (1-|w|)/4`, `∫_𝔻 (1-|x|²) |(φ(r·))'(x)|² (1-|w|²)/|1-w̄x|² ≤ 320 A`. -/
theorem s07d_p1_garsia_dk {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {A : ℝ} (hA : 0 ≤ A)
    (hC : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
        derivCarlesonMeasure (deriv φ) (unitDisc ∩ ball ζ r) ≤ ENNReal.ofReal (A * r))
    {w : ℂ} (hw : w ∈ unitDisc) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hrw : 1 - r ≤ (1 - ‖w‖) / 4) :
    ∫⁻ x in unitDisc, ENNReal.ofReal ((1 - ‖x‖ ^ 2) * ‖deriv (fun x : ℂ => φ ((r : ℂ) * x)) x‖ ^ 2 *
      ((1 - ‖w‖ ^ 2) / ‖1 - conj w * x‖ ^ 2)) ≤ ENNReal.ofReal (320 * A) := by
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hK0 : ∀ x : ℂ, 0 ≤ (1 - ‖w‖ ^ 2) / ‖1 - conj w * x‖ ^ 2 := fun x => by
    have : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    positivity
  have hrm : ∀ x : ℂ, ‖x‖ ≤ 1 → (r : ℂ) * x ∈ unitDisc := fun x hx => by
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    exact (mul_le_of_le_one_right hr0.le hx).trans_lt hr1
  calc ∫⁻ x in unitDisc, ENNReal.ofReal ((1 - ‖x‖ ^ 2) * ‖deriv (fun x : ℂ => φ ((r : ℂ) * x)) x‖ ^ 2 *
        ((1 - ‖w‖ ^ 2) / ‖1 - conj w * x‖ ^ 2))
      = ∫⁻ x in unitDisc, ENNReal.ofReal ((1 - ‖x‖ ^ 2) * (r ^ 2 * (‖deriv φ ((r : ℂ) * x)‖ ^ 2 *
          ((1 - ‖w‖ ^ 2) / ‖1 - conj w * ((r : ℂ) * x / r)‖ ^ 2)))) := by
        refine setLIntegral_congr_fun measurableSet_ball fun x hx => ?_
        have h1 : HasDerivAt (fun x : ℂ => (r : ℂ) * x) (r : ℂ) x := by
          simpa using (hasDerivAt_id x).const_mul (r : ℂ)
        have hd : HasDerivAt (fun x : ℂ => φ ((r : ℂ) * x)) (deriv φ ((r : ℂ) * x) * r) x :=
          ((hφ.differentiableAt (isOpen_ball.mem_nhds
            (hrm x (mem_ball_zero_iff.mp hx).le))).hasDerivAt).comp x h1
        rw [hd.deriv, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hr0.ne'), norm_mul,
          Complex.norm_real, Real.norm_of_nonneg hr0.le]
        ring_nf
    _ ≤ ∫⁻ u in ball (0 : ℂ) r, ENNReal.ofReal ((1 - ‖u‖ ^ 2) * (‖deriv φ u‖ ^ 2 *
          ((1 - ‖w‖ ^ 2) / ‖1 - conj w * (u / r)‖ ^ 2))) :=
        s07d_p1_scale (fun u => ‖deriv φ u‖ ^ 2 * ((1 - ‖w‖ ^ 2) / ‖1 - conj w * (u / r)‖ ^ 2))
          (((measurable_deriv φ).norm.pow_const 2).mul (by fun_prop))
          (fun u => mul_nonneg (sq_nonneg _) (hK0 _)) hr0 hr1.le
    _ ≤ ∫⁻ u in ball (0 : ℂ) r, ENNReal.ofReal (4 * ((1 - ‖u‖ ^ 2) * ‖deriv φ u‖ ^ 2 *
          ((1 - ‖w‖ ^ 2) / ‖1 - conj w * u‖ ^ 2))) := by
        refine setLIntegral_mono' measurableSet_ball fun u hu => ENNReal.ofReal_le_ofReal ?_
        have hu1 : ‖u‖ < r := mem_ball_zero_iff.mp hu
        have hs : 0 ≤ 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
        have hk := s07d_p1_kdil hw1 hr0 hr1.le hrw hu1
        calc (1 - ‖u‖ ^ 2) * (‖deriv φ u‖ ^ 2 * ((1 - ‖w‖ ^ 2) / ‖1 - conj w * (u / r)‖ ^ 2))
            ≤ (1 - ‖u‖ ^ 2) * (‖deriv φ u‖ ^ 2 * (4 * ((1 - ‖w‖ ^ 2) / ‖1 - conj w * u‖ ^ 2))) := by
              gcongr
          _ = _ := by ring
    _ ≤ ∫⁻ u in unitDisc, ENNReal.ofReal (4 * ((1 - ‖u‖ ^ 2) * ‖deriv φ u‖ ^ 2 *
          ((1 - ‖w‖ ^ 2) / ‖1 - conj w * u‖ ^ 2))) := lintegral_mono_set (ball_subset_ball hr1.le)
    _ = 4 * ∫⁻ u in unitDisc, ENNReal.ofReal ((1 - ‖u‖ ^ 2) * ‖deriv φ u‖ ^ 2 *
          ((1 - ‖w‖ ^ 2) / ‖1 - conj w * u‖ ^ 2)) := by
        rw [← lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
        refine lintegral_congr fun u => ?_
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
    _ ≤ 4 * ENNReal.ofReal (80 * A) := by gcongr; exact s07d_p1_kernel hA hC hw
    _ = ENNReal.ofReal (320 * A) := by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
        ring_nf

/-- P1 helper (Garsia at radius `ρ`): with `h = φ(r τ_w(·))`, `∫₀^{2π} |h(ρe^{is}) - h(0)|² ≤ 1280 A` for `0 < ρ < 1`. -/
theorem s07d_p1_garsia_rho {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {A : ℝ} (hA : 0 ≤ A)
    (hC : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
        derivCarlesonMeasure (deriv φ) (unitDisc ∩ ball ζ r) ≤ ENNReal.ofReal (A * r))
    {w : ℂ} (hw : w ∈ unitDisc) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hrw : 1 - r ≤ (1 - ‖w‖) / 4)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∫ s in (0 : ℝ)..2 * π, ‖φ ((r : ℂ) * (((ρ : ℂ) * Complex.exp (s * I) + w) /
      (1 + conj w * ((ρ : ℂ) * Complex.exp (s * I))))) - φ ((r : ℂ) * ((0 + w) / (1 + conj w * 0)))‖ ^ 2 ≤
      1280 * A := by
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hrm : ∀ x : ℂ, ‖x‖ ≤ 1 → (r : ℂ) * x ∈ unitDisc := fun x hx => by
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    exact (mul_le_of_le_one_right hr0.le hx).trans_lt hr1
  have hgd : DifferentiableOn ℂ (fun x : ℂ => φ ((r : ℂ) * x)) unitDisc :=
    hφ.comp ((differentiableOn_const _).mul differentiableOn_id) fun x hx =>
      hrm x (mem_ball_zero_iff.mp hx).le
  have hhd : DifferentiableOn ℂ (fun v : ℂ => φ ((r : ℂ) * ((v + w) / (1 + conj w * v)))) unitDisc := by
    refine hgd.comp (fun v hv => ?_) fun v hv =>
      mem_ball_zero_iff.mpr (s07c_fkps_m6_rn_w4_mem_add hw1 (mem_ball_zero_iff.mp hv))
    exact (s07c_fkps_m6_rn_w4_hd_add (s07d_p1_den hw1 (mem_ball_zero_iff.mp hv).le).2).differentiableAt
      |>.differentiableWithinAt
  have hLP := s07d_p1_lp hhd hρ0 hρ1
  have hma := s07d_p1_mob_area hw hgd
  have hdk := s07d_p1_garsia_dk hφ hA hC hw hr0 hr1 hrw
  set h : ℂ → ℂ := fun v => φ ((r : ℂ) * ((v + w) / (1 + conj w * v))) with hhdef
  have hL : ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) * ‖(ρ : ℂ) * deriv h ((ρ : ℂ) * z)‖ ^ 2) ≤
      ENNReal.ofReal (320 * A) := by
    calc ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) * ‖(ρ : ℂ) * deriv h ((ρ : ℂ) * z)‖ ^ 2)
        = ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) * (ρ ^ 2 * ‖deriv h ((ρ : ℂ) * z)‖ ^ 2)) := by
          refine lintegral_congr fun z => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0.le, mul_pow]
      _ ≤ ∫⁻ u in ball (0 : ℂ) ρ, ENNReal.ofReal ((1 - ‖u‖ ^ 2) * ‖deriv h u‖ ^ 2) :=
          s07d_p1_scale (fun u => ‖deriv h u‖ ^ 2) ((measurable_deriv h).norm.pow_const 2)
            (fun u => sq_nonneg _) hρ0 hρ1.le
      _ ≤ ∫⁻ u in unitDisc, ENNReal.ofReal ((1 - ‖u‖ ^ 2) * ‖deriv h u‖ ^ 2) :=
          lintegral_mono_set (ball_subset_ball hρ1.le)
      _ ≤ ENNReal.ofReal (320 * A) := by rw [hma]; exact hdk
  have hI : ∫ z in unitDisc, (1 - ‖z‖ ^ 2) * ‖(ρ : ℂ) * deriv h ((ρ : ℂ) * z)‖ ^ 2 ≤ 320 * A := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    · exact ENNReal.toReal_le_of_le_ofReal (by positivity) hL
    · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      have : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z, mem_ball_zero_iff.mp hz]
      positivity
    · exact ((by fun_prop : Measurable fun z : ℂ => 1 - ‖z‖ ^ 2).mul
        ((((measurable_deriv h).comp (measurable_const_mul (ρ : ℂ))).const_mul
          (ρ : ℂ)).norm.pow_const 2)).aestronglyMeasurable
  linarith

/-- P1 helper (Garsia bound): if `|φ'|²(1-|z|²) dA` has Carleson constant `A`, then for `w ∈ 𝔻` and
`1 - r ≤ (1-|w|)/4`, `∫₀^{2π} P_w(t) |φ(r e^{it}) - φ(rw)|² dt ≤ 1280 A` (circle Möbius change, LP lower bound,
area Möbius change, dilation and the kernel test; `ρ → 1` by dominated convergence). -/
theorem s07d_p1_garsia {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {A : ℝ} (hA : 0 ≤ A)
    (hC : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
        derivCarlesonMeasure (deriv φ) (unitDisc ∩ ball ζ r) ≤ ENNReal.ofReal (A * r))
    {w : ℂ} (hw : w ∈ unitDisc) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hrw : 1 - r ≤ (1 - ‖w‖) / 4) :
    ∫ t in (0 : ℝ)..2 * π, (1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 *
      ‖φ ((r : ℂ) * Complex.exp (t * I)) - φ ((r : ℂ) * w)‖ ^ 2 ≤ 1280 * A := by
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hrm : ∀ x : ℂ, ‖x‖ ≤ 1 → (r : ℂ) * x ∈ unitDisc := fun x hx => by
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    exact (mul_le_of_le_one_right hr0.le hx).trans_lt hr1
  have hτm : ∀ v : ℂ, ‖v‖ < 1 → ‖(v + w) / (1 + conj w * v)‖ < 1 := fun v hv =>
    s07c_fkps_m6_rn_w4_mem_add hw1 hv
  have hτc : ∀ v : ℂ, ‖v‖ ≤ 1 → ContinuousAt (fun v : ℂ => (v + w) / (1 + conj w * v)) v := fun v hv =>
    (s07c_fkps_m6_rn_w4_hd_add (s07d_p1_den hw1 hv).2).continuousAt
  have hEc : Continuous fun s : ℝ => Complex.exp (s * I) := by fun_prop
  have hE1 : ∀ s : ℝ, ‖Complex.exp (s * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I
  have hτE : Continuous fun s : ℝ => (Complex.exp (s * I) + w) / (1 + conj w * Complex.exp (s * I)) :=
    continuous_iff_continuousAt.mpr fun s =>
      ContinuousAt.comp (f := fun s : ℝ => Complex.exp (s * I)) (hτc _ (hE1 s).le) hEc.continuousAt
  have hcont : Continuous fun s : ℝ =>
      ‖φ ((r : ℂ) * ((Complex.exp (s * I) + w) / (1 + conj w * Complex.exp (s * I)))) - φ ((r : ℂ) * w)‖ ^ 2 :=
    (((hφ.continuousOn.comp_continuous (continuous_const.mul hτE) fun s =>
      hrm _ (s07d_p1_mob_norm hw1 (hE1 s)).le).sub continuous_const).norm.pow 2)
  rw [s07d_p1_mob_circle hw (fun x => ‖φ ((r : ℂ) * x) - φ ((r : ℂ) * w)‖ ^ 2) hcont]
  have hw0 : (0 + w) / (1 + conj w * 0) = w := by simp
  -- `ρ_k → 1`
  set ρ : ℕ → ℝ := fun k => 1 - 1 / ((k : ℝ) + 2) with hρ
  have hρ0 : ∀ k, 0 < ρ k := fun k => by
    have : 1 / ((k : ℝ) + 2) ≤ 1 / 2 := by gcongr; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    simp only [hρ]
    linarith
  have hρ1 : ∀ k, ρ k < 1 := fun k => by
    have : 0 < 1 / ((k : ℝ) + 2) := by positivity
    simp only [hρ]
    linarith
  have hρt : Tendsto ρ atTop (𝓝 1) := by
    have : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    simpa [hρ] using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    (hφ.continuousOn.mono fun x hx => mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx).trans_lt hr1))
  have hhb : ∀ v : ℂ, ‖v‖ < 1 → ‖φ ((r : ℂ) * ((v + w) / (1 + conj w * v)))‖ ≤ M := fun v hv => by
    refine hM _ (mem_closedBall_zero_iff.mpr ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    exact mul_le_of_le_one_right hr0.le (hτm v hv).le
  have hh0M : ‖φ ((r : ℂ) * w)‖ ≤ M := by
    have := hhb 0 (by simp)
    rwa [hw0] at this
  have hvk : ∀ (k : ℕ) (s : ℝ), ‖(ρ k : ℂ) * Complex.exp (s * I)‖ < 1 := fun k s => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρ0 k).le, hE1, mul_one]
    exact hρ1 k
  have hcv : ∀ v : ℂ, ‖v‖ < 1 → ContinuousAt (fun v : ℂ => φ ((r : ℂ) * ((v + w) / (1 + conj w * v)))) v :=
    fun v hv => ContinuousAt.comp (f := fun v : ℂ => (r : ℂ) * ((v + w) / (1 + conj w * v)))
      ((hφ.differentiableAt (isOpen_ball.mem_nhds (hrm _ (hτm v hv).le))).continuousAt)
      (continuousAt_const.mul (hτc _ hv.le))
  have hlim : Tendsto (fun k => ∫ s in (0 : ℝ)..2 * π, ‖φ ((r : ℂ) * (((ρ k : ℂ) * Complex.exp (s * I) + w) /
      (1 + conj w * ((ρ k : ℂ) * Complex.exp (s * I))))) - φ ((r : ℂ) * w)‖ ^ 2) atTop
      (𝓝 (∫ s in (0 : ℝ)..2 * π, ‖φ ((r : ℂ) * ((Complex.exp (s * I) + w) /
        (1 + conj w * Complex.exp (s * I)))) - φ ((r : ℂ) * w)‖ ^ 2)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (2 * M) ^ 2) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun k => ?_
      have hc : Continuous fun s : ℝ => φ ((r : ℂ) * (((ρ k : ℂ) * Complex.exp (s * I) + w) /
          (1 + conj w * ((ρ k : ℂ) * Complex.exp (s * I))))) :=
        continuous_iff_continuousAt.mpr fun s =>
          ContinuousAt.comp (f := fun s : ℝ => (ρ k : ℂ) * Complex.exp (s * I)) (hcv _ (hvk k s))
            (continuous_const.mul hEc).continuousAt
      exact ((hc.sub continuous_const).norm.pow 2).aestronglyMeasurable
    · refine Eventually.of_forall fun k => Eventually.of_forall fun s _ => ?_
      rw [norm_pow, norm_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by linarith [hhb _ (hvk k s)])) 2
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun s _ => ?_
      have hca : ContinuousAt (fun v : ℂ => φ ((r : ℂ) * ((v + w) / (1 + conj w * v)))) (Complex.exp (s * I)) :=
        ContinuousAt.comp (f := fun v : ℂ => (r : ℂ) * ((v + w) / (1 + conj w * v)))
          ((hφ.differentiableAt (isOpen_ball.mem_nhds (hrm _ (s07d_p1_mob_norm hw1 (hE1 s)).le))).continuousAt)
          (continuousAt_const.mul (hτc _ (hE1 s).le))
      have ht : Tendsto (fun k => (ρ k : ℂ) * Complex.exp (s * I)) atTop (𝓝 (Complex.exp (s * I))) := by
        simpa using ((Complex.continuous_ofReal.tendsto 1).comp hρt).mul_const (Complex.exp (s * I))
      exact ((hca.tendsto.comp ht).sub tendsto_const_nhds).norm.pow 2
  refine le_of_tendsto' hlim fun k => ?_
  have := s07d_p1_garsia_rho hφ hA hC hw hr0 hr1 hrw (hρ0 k) (hρ1 k)
  rwa [hw0] at this

/-- P1 helper: for continuous nonnegative `g`, `∫⁻_{[0,2π]} ofReal g = ofReal ∫₀^{2π} g`. -/
theorem s07d_p1_oreal_int {g : ℝ → ℝ} (hg : Continuous g) (h0 : ∀ t, 0 ≤ g t) :
    ∫⁻ t in Icc 0 (2 * π), ENNReal.ofReal (g t) =
      ENNReal.ofReal (∫ t in (0 : ℝ)..2 * π, g t) := by
  rw [intervalIntegral.integral_of_le (by positivity), ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal (hg.integrableOn_Icc) (ae_of_all _ h0)]

/-- P1 helper (far-kernel comparison): if `1 - |v| ≤ 2(1 - |w|)`, `|v - w| ≤ D(1 - |w|)` and
`|e^{it} - w| ≥ 2D(1 - |w|)`, then `P_v(t) ≤ 16 P_w(t)`. -/
theorem s07d_p1_far {v w : ℂ} (hv : v ∈ unitDisc) (hw : w ∈ unitDisc) {D : ℝ}
    (h1 : 1 - ‖v‖ ≤ 2 * (1 - ‖w‖)) (hD : ‖v - w‖ ≤ D * (1 - ‖w‖)) (t : ℝ)
    (ht : 2 * D * (1 - ‖w‖) ≤ ‖Complex.exp (t * I) - w‖) :
    (1 - ‖v‖ ^ 2) / ‖Complex.exp (t * I) - v‖ ^ 2 ≤
      16 * ((1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2) := by
  have hv1 : ‖v‖ < 1 := mem_ball_zero_iff.mp hv
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hX : 0 < ‖Complex.exp (t * I) - w‖ := norm_pos_iff.mpr (s07c_fkps_m2_exp_ne w hw t)
  have hY : 0 < ‖Complex.exp (t * I) - v‖ := norm_pos_iff.mpr (s07c_fkps_m2_exp_ne v hv t)
  have htri := norm_sub_le_norm_sub_add_norm_sub (Complex.exp (t * I)) v w
  have hXY : ‖Complex.exp (t * I) - w‖ ≤ 2 * ‖Complex.exp (t * I) - v‖ := by linarith
  have hnv : 0 ≤ ‖v‖ := norm_nonneg _
  have hnw : 0 ≤ ‖w‖ := norm_nonneg _
  have hk : 1 - ‖v‖ ^ 2 ≤ 4 * (1 - ‖w‖ ^ 2) := by
    nlinarith [sq_nonneg (1 - ‖v‖), mul_nonneg hnw (sub_nonneg.mpr hw1.le)]
  have hk0 : 0 ≤ 1 - ‖v‖ ^ 2 := by nlinarith
  have hsq : ‖Complex.exp (t * I) - w‖ ^ 2 ≤ 4 * ‖Complex.exp (t * I) - v‖ ^ 2 := by
    nlinarith [pow_le_pow_left₀ hX.le hXY 2]
  have key : (1 - ‖v‖ ^ 2) / ‖Complex.exp (t * I) - v‖ ^ 2 ≤
      16 * (1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc (1 - ‖v‖ ^ 2) * ‖Complex.exp (t * I) - w‖ ^ 2
        ≤ (4 * (1 - ‖w‖ ^ 2)) * (4 * ‖Complex.exp (t * I) - v‖ ^ 2) :=
          mul_le_mul hk hsq (by positivity) (by nlinarith)
      _ = 16 * (1 - ‖w‖ ^ 2) * ‖Complex.exp (t * I) - v‖ ^ 2 := by ring
  rwa [mul_div_assoc] at key

/-- P1 helper: continuity, measurability and periodicity of the truncated boundary function
`1_J · |φ(r e^{it}) - φ(r w)|`, `J = {t : |e^{it} - w| < 2D(1 - |w|)}`. -/
theorem s07d_p1_hprop {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) (w : ℂ) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (D : ℝ) :
    Continuous (fun t : ℝ => ‖φ ((r : ℂ) * Complex.exp (t * I)) - φ ((r : ℂ) * w)‖) ∧
    Measurable (indicator {t : ℝ | ‖Complex.exp (t * I) - w‖ < 2 * D * (1 - ‖w‖)}
          fun t => ‖φ ((r : ℂ) * Complex.exp (t * I)) - φ ((r : ℂ) * w)‖) ∧
    ∀ t, indicator {t : ℝ | ‖Complex.exp (t * I) - w‖ < 2 * D * (1 - ‖w‖)}
          (fun t => ‖φ ((r : ℂ) * Complex.exp (t * I)) - φ ((r : ℂ) * w)‖) (t + 2 * π) =
        indicator {t : ℝ | ‖Complex.exp (t * I) - w‖ < 2 * D * (1 - ‖w‖)}
          (fun t => ‖φ ((r : ℂ) * Complex.exp (t * I)) - φ ((r : ℂ) * w)‖) t := by
  have hrm : ∀ x : ℂ, ‖x‖ ≤ 1 → (r : ℂ) * x ∈ unitDisc := fun x hx => by
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    exact (mul_le_of_le_one_right hr0.le hx).trans_lt hr1
  have hc : Continuous (fun t : ℝ => ‖φ ((r : ℂ) * Complex.exp (t * I)) - φ ((r : ℂ) * w)‖) := by
    have h1 : Continuous fun t : ℝ => φ ((r : ℂ) * Complex.exp (t * I)) :=
      hφ.continuousOn.comp_continuous (by fun_prop)
        fun t => hrm _ (Complex.norm_exp_ofReal_mul_I t).le
    exact (h1.sub continuous_const).norm
  refine ⟨hc, hc.measurable.indicator
    (isOpen_lt (by fun_prop) continuous_const).measurableSet, fun t => ?_⟩
  have e := s07c_fkps_m2_exp_periodic t
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, e]

/-- P1 helper (step 6, nontangential split): for `v` in the `γ`-cone at `e^{iθ}` with
`1 - |v| ≤ 2(1 - |w|)` and `|v - w| ≤ D(1 - |w|)`,
`|φ(rv) - φ(rw)| ≤ C · M(1_J F)(θ) + (2π)⁻¹ · 16(2π + 1280A)` (near part by S07c `m2_nt_lint`,
far part by `s07d_p1_far` and Garsia `s07d_p1_garsia`). -/
theorem s07d_p1_nt (γ : ℝ) (hγ : 0 < γ) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ φ : ℂ → ℂ,
    DifferentiableOn ℂ φ unitDisc → ∀ A : ℝ, 0 ≤ A →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
        derivCarlesonMeasure (deriv φ) (unitDisc ∩ ball ζ r) ≤ ENNReal.ofReal (A * r)) →
    ∀ w : ℂ, w ∈ unitDisc → ∀ r : ℝ, 0 < r → r < 1 → 1 - r ≤ (1 - ‖w‖) / 4 →
    ∀ (D θ : ℝ) (v : ℂ), v ∈ unitDisc → ‖v - Complex.exp (θ * I)‖ < γ * (1 - ‖v‖) →
    1 - ‖v‖ ≤ 2 * (1 - ‖w‖) → ‖v - w‖ ≤ D * (1 - ‖w‖) →
    ENNReal.ofReal ‖φ ((r : ℂ) * v) - φ ((r : ℂ) * w)‖ ≤
      C * TauCeti.maximalFunction volume
        (indicator {t : ℝ | ‖Complex.exp (t * I) - w‖ < 2 * D * (1 - ‖w‖)}
          fun t => ‖φ ((r : ℂ) * Complex.exp (t * I)) - φ ((r : ℂ) * w)‖) θ +
      ENNReal.ofReal ((2 * π)⁻¹ * (16 * (2 * π + 1280 * A))) := by
  obtain ⟨C, hC, hNT⟩ := s07c_fkps_m2_nt_lint γ hγ
  refine ⟨C, hC, ?_⟩
  intro φ hφ A hA hCar w hw r hr0 hr1 hrw D θ v hv hc h1 hD
  have hpi : 0 < π := Real.pi_pos
  have hrm : ∀ x : ℂ, ‖x‖ ≤ 1 → (r : ℂ) * x ∈ unitDisc := fun x hx => by
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    exact (mul_le_of_le_one_right hr0.le hx).trans_lt hr1
  obtain ⟨hFc, hhm, hper⟩ := s07d_p1_hprop hφ w hr0 hr1 D
  set F : ℝ → ℝ := fun t => ‖φ ((r : ℂ) * Complex.exp (t * I)) - φ ((r : ℂ) * w)‖ with hFdef
  set J : Set ℝ := {t : ℝ | ‖Complex.exp (t * I) - w‖ < 2 * D * (1 - ‖w‖)} with hJdef
  set h : ℝ → ℝ := indicator J F with hhdef
  have hF0 : ∀ t, 0 ≤ F t := fun t => norm_nonneg _
  set u : ℂ → ℂ := fun x => φ ((r : ℂ) * x) - φ ((r : ℂ) * w) with hudef
  have hu : DiffContOnCl ℂ u (ball (0 : ℂ) 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) one_ne_zero]
    intro x hx
    have hx' : (r : ℂ) * x ∈ unitDisc := hrm x (mem_closedBall_zero_iff.mp hx)
    have hd : DifferentiableAt ℂ φ ((r : ℂ) * x) := hφ.differentiableAt (isOpen_ball.mem_nhds hx')
    exact ((hd.comp x (differentiableAt_id.const_mul (r : ℂ))).sub
      (differentiableAt_const _)).differentiableWithinAt
  have hrep := s07d_p1_poisson hu hv
  have hK0 := s07c_fkps_m2_kernel_nonneg v hv
  have hKc := s07c_fkps_m2_kernel_cont v hv
  have hKwc := s07c_fkps_m2_kernel_cont w hw
  have hKw0 := s07c_fkps_m2_kernel_nonneg w hw
  have hbound : ‖u v‖ ≤ (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
      (1 - ‖v‖ ^ 2) / ‖Complex.exp (t * I) - v‖ ^ 2 * F t := by
    rw [hrep, norm_smul, Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [norm_smul, Real.norm_of_nonneg (hK0 t)]
  have hpt : ∀ t : ℝ, ENNReal.ofReal ((1 - ‖v‖ ^ 2) / ‖Complex.exp (t * I) - v‖ ^ 2 * F t) ≤
      ENNReal.ofReal ((1 - ‖v‖ ^ 2) / ‖Complex.exp (t * I) - v‖ ^ 2) * ‖h t‖ₑ +
      ENNReal.ofReal (16 * ((1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 * (1 + F t ^ 2))) := by
    intro t
    by_cases ht : t ∈ J
    · rw [hhdef, indicator_of_mem ht, Real.enorm_eq_ofReal (hF0 t),
        ← ENNReal.ofReal_mul (hK0 t)]
      exact le_self_add
    · rw [hhdef, indicator_of_notMem ht, enorm_zero, mul_zero, zero_add]
      apply ENNReal.ofReal_le_ofReal
      have hfar := s07d_p1_far hv hw h1 hD t (not_lt.mp ht)
      have hF1 : F t ≤ 1 + F t ^ 2 := by nlinarith [sq_nonneg (F t - 1), hF0 t]
      calc _ ≤ 16 * ((1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2) * F t :=
            mul_le_mul_of_nonneg_right hfar (hF0 t)
        _ ≤ 16 * ((1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2) * (1 + F t ^ 2) :=
            mul_le_mul_of_nonneg_left hF1 (mul_nonneg (by norm_num) (hKw0 t))
        _ = _ := by ring
  have hlint : ENNReal.ofReal (∫ t in (0 : ℝ)..2 * π,
      (1 - ‖v‖ ^ 2) / ‖Complex.exp (t * I) - v‖ ^ 2 * F t) =
      ∫⁻ t in Icc 0 (2 * π), ENNReal.ofReal ((1 - ‖v‖ ^ 2) / ‖Complex.exp (t * I) - v‖ ^ 2 * F t) :=
    (s07d_p1_oreal_int (hKc.mul hFc) fun t => mul_nonneg (hK0 t) (hF0 t)).symm
  have hfc : Continuous fun t : ℝ =>
      16 * ((1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 * (1 + F t ^ 2)) :=
    continuous_const.mul (hKwc.mul (continuous_const.add (hFc.pow 2)))
  have hfarm : Measurable fun t : ℝ =>
      ENNReal.ofReal (16 * ((1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 * (1 + F t ^ 2))) :=
    ENNReal.measurable_ofReal.comp hfc.measurable
  have hfarint : ∫⁻ t in Icc 0 (2 * π),
      ENNReal.ofReal (16 * ((1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 * (1 + F t ^ 2))) ≤
      ENNReal.ofReal (16 * (2 * π + 1280 * A)) := by
    rw [s07d_p1_oreal_int hfc
      (fun t => mul_nonneg (by norm_num) (mul_nonneg (hKw0 t) (by positivity)))]
    apply ENNReal.ofReal_le_ofReal
    rw [intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have hmass := s07c_fkps_m2_kernel_mass w hw
    have hg : ∫ t in (0 : ℝ)..2 * π, (1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 * F t ^ 2 ≤
        1280 * A := s07d_p1_garsia hφ hA hCar hw hr0 hr1 hrw
    have e : ∀ t : ℝ, (1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 * (1 + F t ^ 2) =
        (1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 +
          (1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 * F t ^ 2 := fun t => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_add (by exact hKwc.intervalIntegrable _ _)
      (by exact (hKwc.mul (hFc.pow 2)).intervalIntegrable _ _)]
    have h2pi : ∫ t in (0 : ℝ)..2 * π, (1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 =
        2 * π := by
      rw [inv_mul_eq_iff_eq_mul₀ (by positivity), mul_one] at hmass
      exact hmass
    linarith
  have hnt := hNT h hhm hper θ v hv hc
  calc ENNReal.ofReal ‖φ ((r : ℂ) * v) - φ ((r : ℂ) * w)‖ = ENNReal.ofReal ‖u v‖ := rfl
    _ ≤ ENNReal.ofReal ((2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
        (1 - ‖v‖ ^ 2) / ‖Complex.exp (t * I) - v‖ ^ 2 * F t) := ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (2 * π)⁻¹ * ∫⁻ t in Icc 0 (2 * π),
        ENNReal.ofReal ((1 - ‖v‖ ^ 2) / ‖Complex.exp (t * I) - v‖ ^ 2 * F t) := by
      rw [ENNReal.ofReal_mul (by positivity), hlint]
    _ ≤ ENNReal.ofReal (2 * π)⁻¹ * ((∫⁻ t in Icc 0 (2 * π),
          ENNReal.ofReal ((1 - ‖v‖ ^ 2) / ‖Complex.exp (t * I) - v‖ ^ 2) * ‖h t‖ₑ) +
        ∫⁻ t in Icc 0 (2 * π),
          ENNReal.ofReal (16 * ((1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 *
            (1 + F t ^ 2)))) := by
      gcongr
      exact (lintegral_mono fun t => hpt t).trans (lintegral_add_right _ hfarm).le
    _ = ENNReal.ofReal (2 * π)⁻¹ * (∫⁻ t in Icc 0 (2 * π),
          ENNReal.ofReal ((1 - ‖v‖ ^ 2) / ‖Complex.exp (t * I) - v‖ ^ 2) * ‖h t‖ₑ) +
        ENNReal.ofReal (2 * π)⁻¹ * ∫⁻ t in Icc 0 (2 * π),
          ENNReal.ofReal (16 * ((1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 *
            (1 + F t ^ 2))) := mul_add _ _ _
    _ ≤ C * TauCeti.maximalFunction volume h θ +
        ENNReal.ofReal (2 * π)⁻¹ * ENNReal.ofReal (16 * (2 * π + 1280 * A)) := by
      gcongr
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

/-- P1 helper (step 7, bad set): Chebyshev + Hardy–Littlewood (S07c `m2_maxL2`) + the kernel lower
bound on `J`: `T² · |{θ ∈ [a,b] : T < C · M(1_J F)(θ)}| ≤ C² C_HL (2D)² · 1280A · (1 - |w|)`. -/
theorem s07d_p1_bad : ∃ CH : ℝ≥0∞, CH ≠ ⊤ ∧ ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ unitDisc →
    ∀ A : ℝ, 0 ≤ A →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
        derivCarlesonMeasure (deriv φ) (unitDisc ∩ ball ζ r) ≤ ENNReal.ofReal (A * r)) →
    ∀ w : ℂ, w ∈ unitDisc → ∀ r : ℝ, 0 < r → r < 1 → 1 - r ≤ (1 - ‖w‖) / 4 →
    ∀ (D : ℝ) (C T : ℝ≥0∞) (a b : ℝ), a ≤ b → b - a ≤ 1 →
    T ^ 2 * volume {θ : ℝ | θ ∈ Icc a b ∧ T < C * TauCeti.maximalFunction volume
        (indicator {t : ℝ | ‖Complex.exp (t * I) - w‖ < 2 * D * (1 - ‖w‖)}
          fun t => ‖φ ((r : ℂ) * Complex.exp (t * I)) - φ ((r : ℂ) * w)‖) θ} ≤
      C ^ 2 * CH * ENNReal.ofReal ((2 * D) ^ 2 * (1280 * A) * (1 - ‖w‖)) := by
  obtain ⟨CH, hCH, hML⟩ := s07c_fkps_m2_maxL2
  refine ⟨CH, hCH, ?_⟩
  intro φ hφ A hA hCar w hw r hr0 hr1 hrw D C T a b hab hba
  have hpi : 0 < π := Real.pi_pos
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  obtain ⟨hFc, hhm, hper⟩ := s07d_p1_hprop hφ w hr0 hr1 D
  set F : ℝ → ℝ := fun t => ‖φ ((r : ℂ) * Complex.exp (t * I)) - φ ((r : ℂ) * w)‖ with hFdef
  set J : Set ℝ := {t : ℝ | ‖Complex.exp (t * I) - w‖ < 2 * D * (1 - ‖w‖)} with hJdef
  set h : ℝ → ℝ := indicator J F with hhdef
  have hF0 : ∀ t, 0 ≤ F t := fun t => norm_nonneg _
  have hKwc := s07c_fkps_m2_kernel_cont w hw
  have hKw0 := s07c_fkps_m2_kernel_nonneg w hw
  set M : ℝ → ℝ≥0∞ := TauCeti.maximalFunction volume h with hMdef
  have hMm : Measurable M := TauCeti.measurable_maximalFunction volume h
  have hMper : ∀ θ, M (θ + 2 * π) = M θ := s07c_fkps_m2_max_periodic h hper
  have hpt : ∀ θ : ℝ, ‖h θ‖ₑ ^ 2 ≤ ENNReal.ofReal ((2 * D) ^ 2 * (1 - ‖w‖) *
      ((1 - ‖w‖ ^ 2) / ‖Complex.exp (θ * I) - w‖ ^ 2 * F θ ^ 2)) := by
    intro θ
    by_cases hθ : θ ∈ J
    · rw [hhdef, indicator_of_mem hθ, Real.enorm_eq_ofReal (hF0 θ),
        ← ENNReal.ofReal_pow (hF0 θ)]
      apply ENNReal.ofReal_le_ofReal
      have hX : 0 < ‖Complex.exp (θ * I) - w‖ := norm_pos_iff.mpr (s07c_fkps_m2_exp_ne w hw θ)
      have hlt : ‖Complex.exp (θ * I) - w‖ < 2 * D * (1 - ‖w‖) := hθ
      have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
      have hsq : ‖Complex.exp (θ * I) - w‖ ^ 2 ≤ (2 * D) ^ 2 * (1 - ‖w‖) * (1 - ‖w‖ ^ 2) := by
        nlinarith [pow_le_pow_left₀ hX.le hlt.le 2,
          mul_nonneg (sq_nonneg (2 * D * (1 - ‖w‖))) hw0]
      have hk : 1 ≤ (2 * D) ^ 2 * (1 - ‖w‖) * ((1 - ‖w‖ ^ 2) / ‖Complex.exp (θ * I) - w‖ ^ 2) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity), one_mul]
        exact hsq
      nlinarith [sq_nonneg (F θ)]
    · rw [hhdef, indicator_of_notMem hθ, enorm_zero]
      simp
  have hsub : {θ : ℝ | θ ∈ Icc a b ∧ T < C * M θ} ⊆ {θ | T ^ 2 ≤ (C * M θ) ^ 2} ∩ Icc a b :=
    fun θ hθ => ⟨pow_le_pow_left₀ (by simp) hθ.2.le 2, hθ.1⟩
  have hIcc : Icc a b ⊆ Ioc (a - 1) (a - 1 + 2 * π) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_gt_three]⟩
  have hg : ∫ t in (0 : ℝ)..2 * π, (1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 * F t ^ 2 ≤
      1280 * A := s07d_p1_garsia hφ hA hCar hw hr0 hr1 hrw
  have hX0 : 0 ≤ (2 * D) ^ 2 * (1 - ‖w‖) := mul_nonneg (sq_nonneg _) (by linarith)
  calc T ^ 2 * volume {θ : ℝ | θ ∈ Icc a b ∧ T < C * M θ}
      ≤ T ^ 2 * volume.restrict (Icc a b) {θ | T ^ 2 ≤ (C * M θ) ^ 2} := by
        gcongr T ^ 2 * ?_
        rw [Measure.restrict_apply' measurableSet_Icc]
        exact measure_mono hsub
    _ ≤ ∫⁻ θ in Icc a b, (C * M θ) ^ 2 :=
        mul_meas_ge_le_lintegral₀ ((measurable_const.mul hMm).pow_const 2).aemeasurable _
    _ ≤ ∫⁻ θ in Ioc (a - 1) (a - 1 + 2 * π), (C * M θ) ^ 2 := lintegral_mono_set hIcc
    _ = ∫⁻ θ in Ioc 0 (2 * π), (C * M θ) ^ 2 :=
        s07c_fkps_m2_lint_period _ (fun θ => by simp only [hMper]) _
    _ = C ^ 2 * ∫⁻ θ in Icc 0 (2 * π), M θ ^ 2 := by
        rw [setLIntegral_congr Ioc_ae_eq_Icc]
        simp_rw [mul_pow]
        exact lintegral_const_mul _ (hMm.pow_const 2)
    _ ≤ C ^ 2 * (CH * ∫⁻ θ in Icc 0 (2 * π), ‖h θ‖ₑ ^ 2) := by
        gcongr
        exact hML h hhm hper
    _ ≤ C ^ 2 * (CH * ∫⁻ θ in Icc 0 (2 * π), ENNReal.ofReal ((2 * D) ^ 2 * (1 - ‖w‖) *
          ((1 - ‖w‖ ^ 2) / ‖Complex.exp (θ * I) - w‖ ^ 2 * F θ ^ 2))) := by
        gcongr with θ
        exact hpt θ
    _ = C ^ 2 * (CH * ENNReal.ofReal ((2 * D) ^ 2 * (1 - ‖w‖) *
          ∫ t in (0 : ℝ)..2 * π, (1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 * F t ^ 2)) := by
        rw [s07d_p1_oreal_int (g := fun t => (2 * D) ^ 2 * (1 - ‖w‖) *
            ((1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 * F t ^ 2))
          (continuous_const.mul (hKwc.mul (hFc.pow 2)))
          (fun t => mul_nonneg hX0 (mul_nonneg (hKw0 t) (sq_nonneg _))),
          intervalIntegral.integral_const_mul]
    _ ≤ C ^ 2 * CH * ENNReal.ofReal ((2 * D) ^ 2 * (1280 * A) * (1 - ‖w‖)) := by
        rw [← mul_assoc]
        gcongr C ^ 2 * CH * ENNReal.ofReal ?_
        calc _ ≤ (2 * D) ^ 2 * (1 - ‖w‖) * (1280 * A) := mul_le_mul_of_nonneg_left hg hX0
          _ = _ := by ring

/-- P1 helper (step 8 geometry): a point `ρ e^{is}` of the open `α/2`-cone at `t ∈ [a, b]` with
`1 - ρ < 2(b - a)`, rescaled by `r' ≥ (1 + ρ)/2`, lies in the `(1 + 4/α)`-cone at `t`, at height
`≤ 2(b - a)` and within `(2(1 + 4/α) + 2)(b - a)` of `w₀ = (1 - (b - a)) e^{i(a+b)/2}`. -/
theorem s07d_p1_geom {α : ℝ} (hα : 0 < α) {a b t ρ s r' : ℝ} (hab : a < b)
    (ht : t ∈ Icc a b) (hρ0 : 0 < ρ) (hr'0 : 0 < r') (hr'1 : r' < 1) (hρr : ρ < r')
    (hr'ρ : (1 + ρ) / 2 ≤ r') (h2 : 1 - ρ < 2 * (b - a)) (h3 : α / 2 * |s - t| < 1 - ρ) :
    ∃ v : ℂ, v ∈ unitDisc ∧ ‖v - Complex.exp (t * I)‖ < (1 + 4 / α) * (1 - ‖v‖) ∧
      1 - ‖v‖ ≤ 2 * (b - a) ∧
      ‖v - ((1 - (b - a) : ℝ) : ℂ) * Complex.exp (((a + b) / 2 : ℝ) * I)‖ ≤
        (2 * (1 + 4 / α) + 2) * (b - a) ∧
      (r' : ℂ) * v = (ρ : ℂ) * Complex.exp (s * I) := by
  have hℓ : 0 < b - a := sub_pos.mpr hab
  set q : ℝ := ρ / r' with hqdef
  have hq0 : 0 < q := div_pos hρ0 hr'0
  have hq1 : q < 1 := (div_lt_one hr'0).mpr hρr
  have hqr : q * r' = ρ := div_mul_cancel₀ ρ hr'0.ne'
  have hqρ : ρ ≤ q := by
    rw [hqdef, le_div_iff₀ hr'0]
    exact mul_le_of_le_one_right hρ0.le hr'1.le
  have h2ρ : 2 * ρ ≤ r' * (1 + ρ) := by nlinarith [sq_nonneg (1 - ρ)]
  have hkey : 1 - ρ ≤ 2 * (1 - q) := by nlinarith
  have hnv : ‖(q : ℂ) * Complex.exp (s * I)‖ = q := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hq0.le,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hst : |s - t| < 2 / α * (1 - ρ) := by
    calc |s - t| = 2 / α * (α / 2 * |s - t|) := by field_simp
      _ < 2 / α * (1 - ρ) := mul_lt_mul_of_pos_left h3 (by positivity)
  have hvs : ‖(q : ℂ) * Complex.exp (s * I) - Complex.exp (s * I)‖ = 1 - q := by
    rw [show (q : ℂ) * Complex.exp (s * I) - Complex.exp (s * I) =
        ((q - 1 : ℝ) : ℂ) * Complex.exp (s * I) by push_cast; ring, norm_mul,
      Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs,
      abs_of_neg (by linarith)]
    ring
  have hcone_le : ‖(q : ℂ) * Complex.exp (s * I) - Complex.exp (t * I)‖ ≤ (1 - q) + |s - t| := by
    have e1 := norm_sub_le_norm_sub_add_norm_sub ((q : ℂ) * Complex.exp (s * I))
      (Complex.exp (s * I)) (Complex.exp (t * I))
    have e2 := s07c_fkps_m2_chord_le s t
    linarith
  have h4a : 2 / α * (1 - ρ) ≤ 4 / α * (1 - q) := by
    rw [show 4 / α * (1 - q) = 2 / α * (2 * (1 - q)) by ring]
    exact mul_le_mul_of_nonneg_left hkey (by positivity)
  have hcone : ‖(q : ℂ) * Complex.exp (s * I) - Complex.exp (t * I)‖ < (1 + 4 / α) * (1 - q) := by
    have e : (1 + 4 / α) * (1 - q) = (1 - q) + 4 / α * (1 - q) := by ring
    rw [e]
    linarith
  refine ⟨(q : ℂ) * Complex.exp (s * I), mem_ball_zero_iff.mpr (by rw [hnv]; exact hq1), ?_, ?_,
    ?_, ?_⟩
  · rw [hnv]
    exact hcone
  · rw [hnv]
    linarith
  · have hct : ‖Complex.exp (t * I) - Complex.exp (((a + b) / 2 : ℝ) * I)‖ ≤ (b - a) / 2 := by
      refine (s07c_fkps_m2_chord_le _ _).trans ?_
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hcw : ‖Complex.exp (((a + b) / 2 : ℝ) * I) -
        ((1 - (b - a) : ℝ) : ℂ) * Complex.exp (((a + b) / 2 : ℝ) * I)‖ = b - a := by
      rw [show Complex.exp (((a + b) / 2 : ℝ) * I) -
          ((1 - (b - a) : ℝ) : ℂ) * Complex.exp (((a + b) / 2 : ℝ) * I) =
          ((b - a : ℝ) : ℂ) * Complex.exp (((a + b) / 2 : ℝ) * I) by push_cast; ring,
        norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
        Real.norm_of_nonneg hℓ.le]
    have e1 := norm_sub_le_norm_sub_add_norm_sub ((q : ℂ) * Complex.exp (s * I))
      (Complex.exp (t * I)) (((1 - (b - a) : ℝ) : ℂ) * Complex.exp (((a + b) / 2 : ℝ) * I))
    have e2 := norm_sub_le_norm_sub_add_norm_sub (Complex.exp (t * I))
      (Complex.exp (((a + b) / 2 : ℝ) * I))
      (((1 - (b - a) : ℝ) : ℂ) * Complex.exp (((a + b) / 2 : ℝ) * I))
    have hγq : (1 + 4 / α) * (1 - q) ≤ (1 + 4 / α) * (2 * (b - a)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e3 : (2 * (1 + 4 / α) + 2) * (b - a) = (1 + 4 / α) * (2 * (b - a)) + 2 * (b - a) := by
      ring
    rw [e3]
    linarith
  · rw [← mul_assoc, ← Complex.ofReal_mul, mul_comm r' q, hqr]

/-- P1 helper (step 8 constant): `k₀ ℓ ≤ λ² · ηℓ` in `ℝ≥0∞` when `k₀.toReal ≤ λ² η`. -/
theorem s07d_p1_kcalc {k0 : ℝ≥0∞} (hk0 : k0 ≠ ⊤) {lam η ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hlam : 0 ≤ lam) (hk0r : k0.toReal ≤ lam ^ 2 * η) :
    k0 * ENNReal.ofReal ℓ ≤ ENNReal.ofReal lam ^ 2 * ENNReal.ofReal (η * ℓ) := by
  calc k0 * ENNReal.ofReal ℓ = ENNReal.ofReal (k0.toReal * ℓ) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hk0]
    _ ≤ ENNReal.ofReal (lam ^ 2 * (η * ℓ)) := by
        apply ENNReal.ofReal_le_ofReal
        calc k0.toReal * ℓ ≤ lam ^ 2 * η * ℓ := mul_le_mul_of_nonneg_right hk0r hℓ
          _ = _ := by ring
    _ = ENNReal.ofReal lam ^ 2 * ENNReal.ofReal (η * ℓ) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hlam]

/-- P1 input adapter: for `f` holomorphic on `𝔻` with `f' ≠ 0`, a holomorphic `φ = log f'` on `𝔻`
(`φ' = f''/f'`, `exp φ = f'`); under `LogDerivBMOA f` its derivative Carleson measure has a finite
real constant `A` (LZ `kb_d2_log_deriv`). -/
theorem s07d_p1_logderiv (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f unitDisc)
    (hf' : ∀ z ∈ unitDisc, deriv f z ≠ 0) (hB : LogDerivBMOA f) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ unitDisc ∧
      (∀ z ∈ unitDisc, deriv φ z = deriv (deriv f) z / deriv f z) ∧
      (∀ z ∈ unitDisc, Complex.exp (φ z) = deriv f z) ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
        derivCarlesonMeasure (deriv φ) (unitDisc ∩ ball ζ r) ≤ ENNReal.ofReal (A * r) := by
  obtain ⟨G, hGd, hGe⟩ := kb_d2_log_deriv (f := f) hf hf'
  obtain ⟨C, hCt, hCar⟩ := hB
  refine ⟨G, fun z hz => (hGd z hz).differentiableAt.differentiableWithinAt,
    fun z hz => (hGd z hz).deriv, hGe, C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro ζ hζ r hr0 hr2
  have heq : derivCarlesonMeasure (deriv G) =
      derivCarlesonMeasure fun z => deriv (deriv f) z / deriv f z := by
    show (volume.restrict unitDisc).withDensity
        (fun z => ENNReal.ofReal (‖deriv G z‖ ^ 2 * (1 - ‖z‖ ^ 2))) =
      (volume.restrict unitDisc).withDensity
        (fun z => ENNReal.ofReal (‖deriv (deriv f) z / deriv f z‖ ^ 2 * (1 - ‖z‖ ^ 2)))
    refine withDensity_congr_ae ?_
    refine (ae_restrict_iff' isOpen_ball.measurableSet).mpr (ae_of_all _ fun z hz => ?_)
    simp only [(hGd z hz).deriv]
  rw [heq, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCt]
  exact hCar ζ hζ r hr0 hr2

/-- P1 (BMOA sawtooth stopping time; Bishop–Jones Thm 4 (1)⇒(2), BJ l.889–905). Let `φ` be holomorphic on
`𝔻` with `|φ'|²(1-|z|²) dA` Carleson with constant `A`. For the arc `I = {e^{it} : a ≤ t ≤ b}`,
`|I| = b - a ≤ 1/2`, and `w₀ = (1 - |I|) e^{i(a+b)/2}`, there is a closed `E ⊆ [a, b]` with
`|E| ≥ (1 - η)|I|` such that `|φ - φ(w₀)| ≤ C₁` on the sawtooth region
`𝒟 = {ρ e^{is} : ∃ t ∈ E, α |s - t| ≤ 1 - ρ ≤ |I|, ρ < 1}` (closed cones of aperture `α` with vertices in `E`,
truncated at height `|I|`). `C₁` depends only on `A, α, η`. -/
theorem s07d_p1_sawtooth (A α η : ℝ) (hA : 0 ≤ A) (hα : 0 < α) (hη : 0 < η) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ unitDisc →
      (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
        derivCarlesonMeasure (deriv φ) (unitDisc ∩ ball ζ r) ≤ ENNReal.ofReal (A * r)) →
      ∀ a b : ℝ, a < b → b - a ≤ 1 / 2 →
        ∃ E ⊆ Icc a b, IsClosed E ∧ ENNReal.ofReal ((1 - η) * (b - a)) ≤ volume E ∧
          ∀ t ∈ E, ∀ ρ s : ℝ, ρ < 1 → 1 - ρ ≤ b - a → α * |s - t| ≤ 1 - ρ →
            ‖φ ((ρ : ℂ) * Complex.exp (s * I)) -
              φ (((1 - (b - a) : ℝ) : ℂ) * Complex.exp (((a + b) / 2 : ℝ) * I))‖ ≤ C₁ := by
  set γ : ℝ := 1 + 4 / α with hγdef
  have hγ : 0 < γ := by positivity
  set D : ℝ := 2 * γ + 2 with hDdef
  obtain ⟨C, hCtop, hNT⟩ := s07d_p1_nt γ hγ
  obtain ⟨CH, hCHtop, hBad⟩ := s07d_p1_bad
  set k0 : ℝ≥0∞ := C ^ 2 * CH * ENNReal.ofReal ((2 * D) ^ 2 * (1280 * A)) with hk0def
  have hk0 : k0 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top hCtop) hCHtop) ENNReal.ofReal_ne_top
  set lam : ℝ := k0.toReal / η + 1 with hlamdef
  have hk0r0 : 0 ≤ k0.toReal := ENNReal.toReal_nonneg
  have hlam1 : 1 ≤ lam := by
    have : 0 ≤ k0.toReal / η := div_nonneg hk0r0 hη.le
    linarith
  have hk0r : k0.toReal ≤ lam ^ 2 * η := by
    have e2 : lam * η = k0.toReal + η := by
      rw [hlamdef, add_mul, div_mul_cancel₀ _ hη.ne', one_mul]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hlam1) (by linarith : (0 : ℝ) ≤ lam)) hη.le]
  set Far : ℝ := (2 * π)⁻¹ * (16 * (2 * π + 1280 * A)) with hFardef
  have hFar : 0 ≤ Far := by
    have := Real.pi_pos
    rw [hFardef]
    positivity
  refine ⟨lam + Far + 1, by linarith, ?_⟩
  intro φ hφ hCar a b hab hba
  have hℓ : 0 < b - a := sub_pos.mpr hab
  set w₀ : ℂ := ((1 - (b - a) : ℝ) : ℂ) * Complex.exp (((a + b) / 2 : ℝ) * I) with hw0def
  have hnw0 : ‖w₀‖ = 1 - (b - a) := by
    rw [hw0def, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
      Real.norm_of_nonneg (by linarith)]
  have hnw' : 1 - ‖w₀‖ = b - a := by rw [hnw0]; ring
  have hw₀ : w₀ ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hnw0]; linarith)
  set Bn : ℕ → Set ℝ := fun n => {t : ℝ | ∃ ρ s : ℝ, ρ < 1 - 1 / ((n : ℝ) + 2) ∧
      1 - ρ < 2 * (b - a) ∧ α / 2 * |s - t| < 1 - ρ ∧
      lam + Far + 1 < ‖φ ((ρ : ℂ) * Complex.exp (s * I)) - φ w₀‖} with hBndef
  have hBopen : ∀ n, IsOpen (Bn n) := by
    intro n
    rw [isOpen_iff_forall_mem_open]
    intro t ht
    obtain ⟨ρ, s, h1, h2, h3, h4⟩ := ht
    exact ⟨{t' : ℝ | α / 2 * |s - t'| < 1 - ρ}, fun t' ht' => ⟨ρ, s, h1, h2, ht', h4⟩,
      isOpen_lt (by fun_prop) continuous_const, h3⟩
  have hBmono : Monotone Bn := by
    intro n m hnm t ht
    obtain ⟨ρ, s, h1, h2, h3, h4⟩ := ht
    refine ⟨ρ, s, h1.trans_le ?_, h2, h3, h4⟩
    have : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
    gcongr
  refine ⟨Icc a b \ ⋃ n, Bn n, sdiff_subset, isClosed_Icc.sdiff (isOpen_iUnion hBopen), ?_, ?_⟩
  · have hBn : ∀ n : ℕ, volume (Icc a b ∩ Bn n) ≤ ENNReal.ofReal (η * (b - a)) := by
      intro n
      have hpos : 0 < 1 / ((n : ℝ) + 2) := by positivity
      have hev : ∀ᶠ r' in 𝓝[<] (1 : ℝ), (1 + (1 - 1 / ((n : ℝ) + 2))) / 2 < r' ∧
          1 - (b - a) / 4 < r' ∧ φ ((r' : ℂ) * w₀) ∈ closedBall (φ w₀) 1 := by
        have hc : ContinuousAt (fun r' : ℝ => φ ((r' : ℂ) * w₀)) 1 := by
          have hφc : ContinuousAt φ (((1 : ℝ) : ℂ) * w₀) := by
            rw [Complex.ofReal_one, one_mul]
            exact (hφ.differentiableAt (isOpen_ball.mem_nhds hw₀)).continuousAt
          exact hφc.comp (f := fun r' : ℝ => (r' : ℂ) * w₀) (by fun_prop)
        have hlim : Tendsto (fun r' : ℝ => φ ((r' : ℂ) * w₀)) (𝓝[<] 1) (𝓝 (φ w₀)) := by
          have : Tendsto (fun r' : ℝ => φ ((r' : ℂ) * w₀)) (𝓝[<] (1 : ℝ))
              (𝓝 (φ (((1 : ℝ) : ℂ) * w₀))) := hc.tendsto.mono_left nhdsWithin_le_nhds
          rwa [Complex.ofReal_one, one_mul] at this
        have h1 : ∀ᶠ r' in 𝓝[<] (1 : ℝ), (1 + (1 - 1 / ((n : ℝ) + 2))) / 2 < r' :=
          Filter.mem_of_superset (Ioo_mem_nhdsLT (show (1 + (1 - 1 / ((n : ℝ) + 2))) / 2 < 1 by
            linarith)) fun x hx => hx.1
        have h2 : ∀ᶠ r' in 𝓝[<] (1 : ℝ), 1 - (b - a) / 4 < r' :=
          Filter.mem_of_superset (Ioo_mem_nhdsLT (show 1 - (b - a) / 4 < 1 by linarith))
            fun x hx => hx.1
        exact h1.and (h2.and (hlim.eventually (closedBall_mem_nhds (φ w₀) one_pos)))
      obtain ⟨r', ⟨hr'a, hr'b, hr'c⟩, hr'1⟩ := (hev.and self_mem_nhdsWithin).exists
      have hr'1' : r' < 1 := hr'1
      have hr'c' : ‖φ ((r' : ℂ) * w₀) - φ w₀‖ ≤ 1 := by
        rwa [mem_closedBall, dist_eq_norm] at hr'c
      have hr'0 : 0 < r' := by linarith
      have hrw' : 1 - r' ≤ (1 - ‖w₀‖) / 4 := by rw [hnw']; linarith
      have hsub : Icc a b ∩ Bn n ⊆ {θ : ℝ | θ ∈ Icc a b ∧ ENNReal.ofReal lam <
          C * TauCeti.maximalFunction volume
            (indicator {t : ℝ | ‖Complex.exp (t * I) - w₀‖ < 2 * D * (1 - ‖w₀‖)}
              fun t => ‖φ ((r' : ℂ) * Complex.exp (t * I)) - φ ((r' : ℂ) * w₀)‖) θ} := by
        rintro t ⟨htI, ρ, s, h1, h2, h3, h4⟩
        refine ⟨htI, ?_⟩
        by_contra hle
        push Not at hle
        have hρ0 : 0 < ρ := by linarith
        have hρr : ρ < r' := by linarith
        have hr'ρ : (1 + ρ) / 2 ≤ r' := by linarith
        obtain ⟨v, hv, hcone, h1v, hDv, hrv⟩ :=
          s07d_p1_geom hα hab htI hρ0 hr'0 hr'1' hρr hr'ρ h2 h3
        have h1v' : 1 - ‖v‖ ≤ 2 * (1 - ‖w₀‖) := by rw [hnw']; exact h1v
        have hDv' : ‖v - w₀‖ ≤ D * (1 - ‖w₀‖) := by rw [hnw']; exact hDv
        have hmain := hNT φ hφ A hA hCar w₀ hw₀ r' hr'0 hr'1' hrw' D t v hv hcone h1v' hDv'
        rw [hrv] at hmain
        have hfin : ENNReal.ofReal ‖φ ((ρ : ℂ) * Complex.exp (s * I)) - φ ((r' : ℂ) * w₀)‖ ≤
            ENNReal.ofReal (lam + Far) := by
          calc _ ≤ _ := hmain
            _ ≤ ENNReal.ofReal lam + ENNReal.ofReal Far := by gcongr
            _ = _ := (ENNReal.ofReal_add (by linarith) hFar).symm
        have hfin' := (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp hfin
        have htri2 := norm_sub_le_norm_sub_add_norm_sub (φ ((ρ : ℂ) * Complex.exp (s * I)))
          (φ ((r' : ℂ) * w₀)) (φ w₀)
        linarith
      have hb := hBad φ hφ A hA hCar w₀ hw₀ r' hr'0 hr'1' hrw' D C (ENNReal.ofReal lam) a b
        hab.le (by linarith)
      have hK : C ^ 2 * CH * ENNReal.ofReal ((2 * D) ^ 2 * (1280 * A) * (1 - ‖w₀‖)) ≤
          ENNReal.ofReal lam ^ 2 * ENNReal.ofReal (η * (b - a)) := by
        have e1 : C ^ 2 * CH * ENNReal.ofReal ((2 * D) ^ 2 * (1280 * A) * (1 - ‖w₀‖)) =
            k0 * ENNReal.ofReal (b - a) := by
          rw [hnw', ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (by linarith)), hk0def]
          ring
        rw [e1]
        exact s07d_p1_kcalc hk0 hℓ.le (by linarith) hk0r
      have hT0 : ENNReal.ofReal lam ^ 2 ≠ 0 :=
        pow_ne_zero _ (ENNReal.ofReal_pos.mpr (by linarith)).ne'
      have hTt : ENNReal.ofReal lam ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
      calc volume (Icc a b ∩ Bn n) ≤ _ := measure_mono hsub
        _ ≤ _ := by
          rw [← ENNReal.mul_le_mul_iff_right hT0 hTt]
          exact hb.trans hK
    have hmono : Monotone fun n => Icc a b ∩ Bn n :=
      fun n m hnm => inter_subset_inter_right _ (hBmono hnm)
    have hU : volume (Icc a b ∩ ⋃ n, Bn n) ≤ ENNReal.ofReal (η * (b - a)) := by
      rw [inter_iUnion, hmono.measure_iUnion]
      exact iSup_le hBn
    have hsplit := measure_le_inter_add_sdiff volume (Icc a b) (⋃ n, Bn n)
    rw [Real.volume_Icc] at hsplit
    rw [show (1 - η) * (b - a) = (b - a) - η * (b - a) by ring,
      ENNReal.ofReal_sub _ (mul_nonneg hη.le hℓ.le), tsub_le_iff_left]
    exact hsplit.trans (add_le_add hU le_rfl)
  · intro t ht ρ s hρ1 hρℓ hαs
    by_contra hcon
    push Not at hcon
    apply ht.2
    have h1ρ : 0 < 1 - ρ := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - ρ))
    refine mem_iUnion.mpr ⟨n, ρ, s, ?_, by linarith, by nlinarith [abs_nonneg (s - t)], hcon⟩
    have : 1 / ((n : ℝ) + 2) < 1 - ρ := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ h1ρ] at hn
      nlinarith
    linarith

/-! ## P2, block B (w3): sawtooth (P2.3), bi-Lipschitz (P2.4), chord-arc output (P2.5) -/

/-- P2.3 helper: `|(1 - t) ζ + t b| ≤ (1 - t) + t |b|` for `|ζ| = 1`, `t ∈ [0, 1]`. -/
theorem s07d_p2_saw_norm {ζ b : ℂ} {t : ℝ} (hζ : ‖ζ‖ = 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖ζ + t • (b - ζ)‖ ≤ (1 - t) + t * ‖b‖ := by
  have he : ζ + t • (b - ζ) = (1 - t) • ζ + t • b := by module
  rw [he]
  calc ‖(1 - t) • ζ + t • b‖ ≤ ‖(1 - t) • ζ‖ + ‖t • b‖ := norm_add_le _ _
    _ = (1 - t) + t * ‖b‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg ht0, hζ,
        mul_one]

/-- P2.3 helper: the sawtooth is open. -/
theorem s07d_p2_saw_open (E : Set ℂ) (c : ℂ) (ρ₀ : ℝ) :
    IsOpen {z : ℂ | ∃ ζ ∈ E, ∃ b ∈ ball c ρ₀, ∃ t ∈ Ioc (0 : ℝ) 1, z = ζ + t • (b - ζ)} := by
  rw [Metric.isOpen_iff]
  rintro z ⟨ζ, hζ, b, hb, t, ht, rfl⟩
  have hb' : ‖b - c‖ < ρ₀ := by rwa [mem_ball, dist_eq_norm] at hb
  refine ⟨t * (ρ₀ - ‖b - c‖), mul_pos ht.1 (by linarith), ?_⟩
  intro z' hz'
  rw [mem_ball, dist_eq_norm] at hz'
  have ht0 : t ≠ 0 := ht.1.ne'
  refine ⟨ζ, hζ, b + t⁻¹ • (z' - (ζ + t • (b - ζ))), ?_, t, ht, ?_⟩
  · rw [mem_ball, dist_eq_norm]
    have h1 : ‖t⁻¹ • (z' - (ζ + t • (b - ζ)))‖ < ρ₀ - ‖b - c‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.1.le), inv_mul_lt_iff₀ ht.1]
      exact hz'
    calc ‖b + t⁻¹ • (z' - (ζ + t • (b - ζ))) - c‖
        = ‖(b - c) + t⁻¹ • (z' - (ζ + t • (b - ζ)))‖ := by congr 1; abel
      _ ≤ ‖b - c‖ + ‖t⁻¹ • (z' - (ζ + t • (b - ζ)))‖ := norm_add_le _ _
      _ < ρ₀ := by linarith
  · have hW : ∀ W : ℂ, t • (t⁻¹ • W) = W := fun W => by
      rw [smul_smul, mul_inv_cancel₀ ht0, one_smul]
    calc z' = ζ + (t • (b - ζ) + t • (t⁻¹ • (z' - (ζ + t • (b - ζ))))) := by rw [hW]; abel
      _ = ζ + t • (b + t⁻¹ • (z' - (ζ + t • (b - ζ))) - ζ) := by
        rw [← smul_add]; congr 2; abel

/-- P2.3 (the sawtooth over `E ⊆ ∂𝔻`): `𝒟 = {(1 - t) ζ + t b : ζ ∈ E, b ∈ B(c, ρ₀), t ∈ (0, 1]}`.
If `B̄(c, ρ₀) ⊆ 𝔻` and `|ζ - c| ≤ D` on `E ≠ ∅`, then `𝒟` is open, ball-star-shaped,
`B(c, ρ₀) ⊆ 𝒟 ⊆ 𝔻 ∩ B(c, D + ρ₀)`, every point of `𝒟` lies in the truncated cone
`{|z - ζ| ≤ α (1 - |z|), |z - ζ| ≤ D + ρ₀}` over some `ζ ∈ E` with
`α = (D + ρ₀)/(1 - |c| - ρ₀)`, and, for closed `E`, `closure 𝒟 ∩ ∂𝔻 = E`. -/
theorem s07d_p2_saw (E : Set ℂ) (c : ℂ) (ρ₀ D : ℝ) (hE : E ⊆ sphere (0 : ℂ) 1) (hEn : E.Nonempty)
    (hρ₀ : 0 < ρ₀) (hc : ‖c‖ + ρ₀ < 1) (hD : ∀ ζ ∈ E, ‖ζ - c‖ ≤ D) :
    IsOpen {z : ℂ | ∃ ζ ∈ E, ∃ b ∈ ball c ρ₀, ∃ t ∈ Ioc (0 : ℝ) 1, z = ζ + t • (b - ζ)} ∧
      ball c ρ₀ ⊆ {z : ℂ | ∃ ζ ∈ E, ∃ b ∈ ball c ρ₀, ∃ t ∈ Ioc (0 : ℝ) 1, z = ζ + t • (b - ζ)} ∧
      {z : ℂ | ∃ ζ ∈ E, ∃ b ∈ ball c ρ₀, ∃ t ∈ Ioc (0 : ℝ) 1, z = ζ + t • (b - ζ)} ⊆
        unitDisc ∩ ball c (D + ρ₀) ∧
      (∀ p ∈ {z : ℂ | ∃ ζ ∈ E, ∃ b ∈ ball c ρ₀, ∃ t ∈ Ioc (0 : ℝ) 1, z = ζ + t • (b - ζ)},
        ∀ b ∈ ball c ρ₀, ∀ t ∈ Icc (0 : ℝ) 1,
          p + t • (b - p) ∈
            {z : ℂ | ∃ ζ ∈ E, ∃ b ∈ ball c ρ₀, ∃ t ∈ Ioc (0 : ℝ) 1, z = ζ + t • (b - ζ)}) ∧
      (∀ z ∈ {z : ℂ | ∃ ζ ∈ E, ∃ b ∈ ball c ρ₀, ∃ t ∈ Ioc (0 : ℝ) 1, z = ζ + t • (b - ζ)},
        ∃ ζ ∈ E, ‖z - ζ‖ * (1 - ‖c‖ - ρ₀) ≤ (D + ρ₀) * (1 - ‖z‖) ∧ ‖z - ζ‖ ≤ D + ρ₀) ∧
      (IsClosed E →
        closure {z : ℂ | ∃ ζ ∈ E, ∃ b ∈ ball c ρ₀, ∃ t ∈ Ioc (0 : ℝ) 1, z = ζ + t • (b - ζ)} ∩
          sphere (0 : ℂ) 1 = E) := by
  obtain ⟨ζ₀, hζ₀⟩ := hEn
  have hD0 : 0 ≤ D := le_trans (norm_nonneg _) (hD ζ₀ hζ₀)
  have hnE : ∀ ζ ∈ E, ‖ζ‖ = 1 := fun ζ h => by
    have := hE h
    rwa [mem_sphere_zero_iff_norm] at this
  have hbc : ∀ b ∈ closedBall c ρ₀, ‖b‖ ≤ ‖c‖ + ρ₀ := by
    intro b hb
    rw [mem_closedBall, dist_eq_norm] at hb
    calc ‖b‖ = ‖c + (b - c)‖ := by congr 1; abel
      _ ≤ ‖c‖ + ‖b - c‖ := norm_add_le _ _
      _ ≤ ‖c‖ + ρ₀ := by linarith
  have hbn : ∀ b ∈ closedBall c ρ₀, ‖b‖ < 1 := fun b hb => lt_of_le_of_lt (hbc b hb) hc
  refine ⟨s07d_p2_saw_open E c ρ₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    exact ⟨ζ₀, hζ₀, b, hb, 1, ⟨one_pos, le_rfl⟩, by rw [one_smul, add_sub_cancel]⟩
  · rintro z ⟨ζ, hζ, b, hb, t, ht, rfl⟩
    have hb1 := hbn b (ball_subset_closedBall hb)
    have hbc' : ‖b - c‖ < ρ₀ := by rwa [mem_ball, dist_eq_norm] at hb
    refine ⟨?_, ?_⟩
    · show _ ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff]
      have h1 := s07d_p2_saw_norm (b := b) (hnE ζ hζ) ht.1.le ht.2
      have h2 : t * ‖b‖ < t := mul_lt_of_lt_one_right ht.1 hb1
      linarith
    · rw [mem_ball, dist_eq_norm]
      have he : ζ + t • (b - ζ) - c = (1 - t) • (ζ - c) + t • (b - c) := by module
      rw [he]
      have h1 : (1 - t) * ‖ζ - c‖ ≤ (1 - t) * D :=
        mul_le_mul_of_nonneg_left (hD ζ hζ) (by linarith [ht.2])
      have h2 : t * ‖b - c‖ < t * ρ₀ := mul_lt_mul_of_pos_left hbc' ht.1
      have h3 : 0 ≤ t * D := mul_nonneg ht.1.le hD0
      have h4 : t * ρ₀ ≤ ρ₀ := mul_le_of_le_one_left hρ₀.le ht.2
      calc ‖(1 - t) • (ζ - c) + t • (b - c)‖ ≤ ‖(1 - t) • (ζ - c)‖ + ‖t • (b - c)‖ :=
            norm_add_le _ _
        _ = (1 - t) * ‖ζ - c‖ + t * ‖b - c‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [ht.2]),
            Real.norm_of_nonneg ht.1.le]
        _ < D + ρ₀ := by nlinarith
  · rintro p ⟨ζ, hζ, b, hb, t, ht, rfl⟩ b' hb' s hs
    obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = t + s * (1 - t) := ⟨_, rfl⟩
    have hs1 : s * (1 - t) ≤ 1 - t := mul_le_of_le_one_left (by linarith [ht.2]) hs.2
    have hs0 : 0 ≤ s * (1 - t) := mul_nonneg hs.1 (by linarith [ht.2])
    have hT : 0 < T := by rw [hTdef]; linarith [ht.1]
    have hT1 : T ≤ 1 := by rw [hTdef]; linarith
    have hTi : T * T⁻¹ = 1 := mul_inv_cancel₀ hT.ne'
    refine ⟨ζ, hζ, (T⁻¹ * ((1 - s) * t)) • b + (T⁻¹ * s) • b', ?_, T, ⟨hT, hT1⟩, ?_⟩
    · refine convex_ball c ρ₀ hb hb'
        (mul_nonneg (inv_nonneg.2 hT.le) (mul_nonneg (by linarith [hs.2]) ht.1.le))
        (mul_nonneg (inv_nonneg.2 hT.le) hs.1) ?_
      rw [← mul_add, show (1 - s) * t + s = T by rw [hTdef]; ring, inv_mul_cancel₀ hT.ne']
    · have hR : T • ((T⁻¹ * ((1 - s) * t)) • b + (T⁻¹ * s) • b' - ζ) =
          ((1 - s) * t) • b + s • b' - T • ζ := by
        simp only [smul_sub, smul_add, smul_smul, ← mul_assoc, hTi, one_mul]
      rw [hR, hTdef]
      module
  · rintro z ⟨ζ, hζ, b, hb, t, ht, rfl⟩
    refine ⟨ζ, hζ, ?_, ?_⟩
    · have hzz : ‖ζ + t • (b - ζ) - ζ‖ = t * ‖b - ζ‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le]
      have hbc' : ‖b - c‖ < ρ₀ := by rwa [mem_ball, dist_eq_norm] at hb
      have hbz : ‖b - ζ‖ ≤ D + ρ₀ := by
        calc ‖b - ζ‖ = ‖(b - c) - (ζ - c)‖ := by congr 1; abel
          _ ≤ ‖b - c‖ + ‖ζ - c‖ := norm_sub_le _ _
          _ ≤ D + ρ₀ := by linarith [hD ζ hζ]
      have hk : 0 < 1 - ‖c‖ - ρ₀ := by linarith
      have hn := s07d_p2_saw_norm (b := b) (hnE ζ hζ) ht.1.le ht.2
      have hb2 : t * ‖b‖ ≤ t * (‖c‖ + ρ₀) :=
        mul_le_mul_of_nonneg_left (hbc b (ball_subset_closedBall hb)) ht.1.le
      have h2 : t * (1 - ‖c‖ - ρ₀) ≤ 1 - ‖ζ + t • (b - ζ)‖ := by nlinarith
      have h1 : t * ‖b - ζ‖ * (1 - ‖c‖ - ρ₀) ≤ t * (D + ρ₀) * (1 - ‖c‖ - ρ₀) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbz ht.1.le) hk.le
      have h3 : (D + ρ₀) * (t * (1 - ‖c‖ - ρ₀)) ≤ (D + ρ₀) * (1 - ‖ζ + t • (b - ζ)‖) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      rw [hzz]
      calc t * ‖b - ζ‖ * (1 - ‖c‖ - ρ₀) ≤ t * (D + ρ₀) * (1 - ‖c‖ - ρ₀) := h1
        _ = (D + ρ₀) * (t * (1 - ‖c‖ - ρ₀)) := by ring
        _ ≤ (D + ρ₀) * (1 - ‖ζ + t • (b - ζ)‖) := h3
    · rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le]
      have hbz : ‖b - ζ‖ ≤ D + ρ₀ := by
        have hbc' : ‖b - c‖ < ρ₀ := by rwa [mem_ball, dist_eq_norm] at hb
        calc ‖b - ζ‖ = ‖(b - c) - (ζ - c)‖ := by congr 1; abel
          _ ≤ ‖b - c‖ + ‖ζ - c‖ := norm_sub_le _ _
          _ ≤ D + ρ₀ := by linarith [hD ζ hζ]
      calc t * ‖b - ζ‖ ≤ 1 * (D + ρ₀) := mul_le_mul ht.2 hbz (norm_nonneg _) zero_le_one
        _ = D + ρ₀ := one_mul _
  · intro hEc
    have hEk : IsCompact E := (isCompact_sphere (0 : ℂ) 1).of_isClosed_subset hEc hE
    apply Subset.antisymm
    · rintro z ⟨hzc, hzs⟩
      have hK : IsCompact ((fun q : ℂ × ℂ × ℝ => q.1 + q.2.2 • (q.2.1 - q.1)) ''
          (E ×ˢ (closedBall c ρ₀ ×ˢ Icc (0 : ℝ) 1))) :=
        (hEk.prod ((isCompact_closedBall c ρ₀).prod isCompact_Icc)).image (by fun_prop)
      have hSK : {z : ℂ | ∃ ζ ∈ E, ∃ b ∈ ball c ρ₀, ∃ t ∈ Ioc (0 : ℝ) 1, z = ζ + t • (b - ζ)} ⊆
          (fun q : ℂ × ℂ × ℝ => q.1 + q.2.2 • (q.2.1 - q.1)) ''
            (E ×ˢ (closedBall c ρ₀ ×ˢ Icc (0 : ℝ) 1)) := by
        rintro w ⟨ζ, hζ, b, hb, t, ht, rfl⟩
        exact ⟨(ζ, b, t), ⟨hζ, ball_subset_closedBall hb, ht.1.le, ht.2⟩, rfl⟩
      obtain ⟨⟨ζ, b, t⟩, ⟨hζ, hb, ht0, ht1⟩, rfl⟩ := closure_minimal hSK hK.isClosed hzc
      rcases eq_or_lt_of_le ht0 with h0 | h0
      · subst h0
        simpa using hζ
      · exfalso
        have h1 := s07d_p2_saw_norm (b := b) (hnE ζ hζ) ht0 ht1
        have hb1 := hbn b hb
        have h2 : t * ‖b‖ < t := mul_lt_of_lt_one_right h0 hb1
        rw [mem_sphere_zero_iff_norm] at hzs
        simp only at hzs
        linarith
    · intro ζ hζ
      refine ⟨Metric.mem_closure_iff.2 ?_, hE hζ⟩
      intro ε hε
      have ht0 : 0 < min 1 (ε / (D + 1)) := lt_min one_pos (div_pos hε (by linarith))
      refine ⟨ζ + (min 1 (ε / (D + 1))) • (c - ζ),
        ⟨ζ, hζ, c, mem_ball_self hρ₀, min 1 (ε / (D + 1)), ⟨ht0, min_le_left _ _⟩, rfl⟩, ?_⟩
      have he : ζ - (ζ + (min 1 (ε / (D + 1))) • (c - ζ)) =
          -((min 1 (ε / (D + 1))) • (c - ζ)) := by abel
      rw [dist_eq_norm, he, norm_neg, norm_smul, Real.norm_of_nonneg ht0.le, norm_sub_rev]
      have h1 : min 1 (ε / (D + 1)) ≤ ε / (D + 1) := min_le_right _ _
      calc min 1 (ε / (D + 1)) * ‖ζ - c‖ ≤ (ε / (D + 1)) * D :=
            mul_le_mul h1 (hD ζ hζ) (norm_nonneg _) (by positivity)
        _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
          nlinarith

/-- P2.4 helper: from a point `z` of `closure 𝒟`, every point of the open segment toward any
`b ∈ B(c, ρ₀)` lies in the ball-star-shaped domain `𝒟`. -/
theorem s07d_p2_bl_cl {𝒟 : Set ℂ} {c z b : ℂ} {ρ₀ lam : ℝ}
    (hst : ∀ p ∈ 𝒟, ∀ b ∈ ball c ρ₀, ∀ t ∈ Icc (0 : ℝ) 1, p + t • (b - p) ∈ 𝒟)
    (hz : z ∈ closure 𝒟) (hb : b ∈ ball c ρ₀) (hl0 : 0 < lam) (hl1 : lam ≤ 1) :
    z + lam • (b - z) ∈ 𝒟 := by
  have hbc : ‖b - c‖ < ρ₀ := by rwa [mem_ball, dist_eq_norm] at hb
  obtain ⟨q, hq, hzq⟩ :=
    Metric.mem_closure_iff.1 hz (lam * (ρ₀ - ‖b - c‖)) (mul_pos hl0 (by linarith))
  rw [dist_eq_norm] at hzq
  have hk : lam * ((1 - lam) / lam) = 1 - lam := mul_div_cancel₀ _ hl0.ne'
  have hk0 : 0 ≤ (1 - lam) / lam := div_nonneg (by linarith) hl0.le
  have hb' : b + ((1 - lam) / lam) • (z - q) ∈ ball c ρ₀ := by
    rw [mem_ball, dist_eq_norm]
    have h1 : ‖((1 - lam) / lam) • (z - q)‖ ≤ (1 - lam) * (ρ₀ - ‖b - c‖) := by
      rw [norm_smul, Real.norm_of_nonneg hk0]
      calc (1 - lam) / lam * ‖z - q‖ ≤ (1 - lam) / lam * (lam * (ρ₀ - ‖b - c‖)) :=
            mul_le_mul_of_nonneg_left hzq.le hk0
        _ = (1 - lam) * (ρ₀ - ‖b - c‖) := by rw [← mul_assoc, div_mul_cancel₀ _ hl0.ne']
    calc ‖b + ((1 - lam) / lam) • (z - q) - c‖ = ‖(b - c) + ((1 - lam) / lam) • (z - q)‖ := by
          congr 1; abel
      _ ≤ ‖b - c‖ + ‖((1 - lam) / lam) • (z - q)‖ := norm_add_le _ _
      _ < ρ₀ := by nlinarith [mul_pos hl0 (sub_pos.2 hbc)]
  have h := hst q hq _ hb' lam ⟨hl0.le, hl1⟩
  have hsm : lam • (((1 - lam) / lam) • (z - q)) = (1 - lam) • (z - q) := by rw [smul_smul, hk]
  have he : q + lam • (b + ((1 - lam) / lam) • (z - q) - q) = z + lam • (b - z) := by
    calc q + lam • (b + ((1 - lam) / lam) • (z - q) - q)
        = q + lam • (b - q) + lam • (((1 - lam) / lam) • (z - q)) := by module
      _ = q + lam • (b - q) + (1 - lam) • (z - q) := by rw [hsm]
      _ = z + lam • (b - z) := by module
  rwa [he] at h

/-- P2.4 helper: for `z ∈ closure 𝒟` and `0 < τ ≤ ρ₀/4` there is `p` at distance `τ` from `z`
with `B(p, τ/A) ⊆ 𝒟` and the half-open segment `(z, p]` inside `𝒟`. -/
theorem s07d_p2_bl_pick {𝒟 : Set ℂ} {c z : ℂ} {A ρ₀ τ : ℝ} (hA : 1 ≤ A) (hρ₀ : 0 < ρ₀)
    (hball : ball c ρ₀ ⊆ 𝒟) (hsub : 𝒟 ⊆ ball c (A * ρ₀))
    (hst : ∀ p ∈ 𝒟, ∀ b ∈ ball c ρ₀, ∀ t ∈ Icc (0 : ℝ) 1, p + t • (b - p) ∈ 𝒟)
    (hz : z ∈ closure 𝒟) (hτ : 0 < τ) (hτρ : τ ≤ ρ₀ / 4) :
    ∃ p : ℂ, ‖z - p‖ = τ ∧ ball p (τ / A) ⊆ 𝒟 ∧ ∀ μ ∈ Ioc (0 : ℝ) 1, z + μ • (p - z) ∈ 𝒟 := by
  have hA0 : 0 < A := by linarith
  have hzc : ‖c - z‖ ≤ A * ρ₀ := by
    have hcl : closure 𝒟 ⊆ closedBall c (A * ρ₀) :=
      closure_minimal (fun x hx => ball_subset_closedBall (hsub hx)) isClosed_closedBall
    have h := hcl hz
    rw [mem_closedBall, dist_eq_norm] at h
    rwa [norm_sub_rev]
  rcases le_or_gt τ ‖c - z‖ with h1 | h1
  · have hcz : 0 < ‖c - z‖ := lt_of_lt_of_le hτ h1
    obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = τ / ‖c - z‖ := ⟨_, rfl⟩
    have hl0 : 0 < lam := by rw [hlam]; exact div_pos hτ hcz
    have hl1 : lam ≤ 1 := by rw [hlam]; exact (div_le_one hcz).2 h1
    have hlz : lam * ‖c - z‖ = τ := by rw [hlam]; exact div_mul_cancel₀ _ hcz.ne'
    refine ⟨z + lam • (c - z), ?_, ?_, ?_⟩
    · rw [show z - (z + lam • (c - z)) = -(lam • (c - z)) by abel, norm_neg, norm_smul,
        Real.norm_of_nonneg hl0.le, hlz]
    · intro y hy
      rw [mem_ball, dist_eq_norm] at hy
      have hb : c + lam⁻¹ • (y - (z + lam • (c - z))) ∈ ball c ρ₀ := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.2 hl0.le)]
        have hli : lam⁻¹ = ‖c - z‖ / τ := by rw [hlam, inv_div]
        rw [hli]
        calc ‖c - z‖ / τ * ‖y - (z + lam • (c - z))‖
            ≤ (A * ρ₀) / τ * ‖y - (z + lam • (c - z))‖ :=
              mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hzc hτ.le) (norm_nonneg _)
          _ < (A * ρ₀) / τ * (τ / A) := mul_lt_mul_of_pos_left hy (by positivity)
          _ = ρ₀ := by field_simp
      have h2 := s07d_p2_bl_cl hst hz hb hl0 hl1
      have hsm : lam • (lam⁻¹ • (y - (z + lam • (c - z)))) = y - (z + lam • (c - z)) := by
        rw [smul_smul, mul_inv_cancel₀ hl0.ne', one_smul]
      have he : z + lam • (c + lam⁻¹ • (y - (z + lam • (c - z))) - z) = y := by
        calc z + lam • (c + lam⁻¹ • (y - (z + lam • (c - z))) - z)
            = z + lam • (c - z) + lam • (lam⁻¹ • (y - (z + lam • (c - z)))) := by module
          _ = y := by rw [hsm]; abel
      rwa [he] at h2
    · intro μ hμ
      have h2 := s07d_p2_bl_cl hst hz (mem_ball_self hρ₀) (mul_pos hμ.1 hl0)
        ((mul_le_of_le_one_left hl0.le hμ.2).trans hl1)
      have he : z + (μ * lam) • (c - z) = z + μ • (z + lam • (c - z) - z) := by module
      rwa [he] at h2
  · refine ⟨z + (τ : ℂ), ?_, ?_, ?_⟩
    · rw [show z - (z + (τ : ℂ)) = -(τ : ℂ) by abel, norm_neg, Complex.norm_of_nonneg hτ.le]
    · intro y hy
      apply hball
      rw [mem_ball, dist_eq_norm] at hy ⊢
      have hτA : τ / A ≤ τ := div_le_self hτ.le hA
      calc ‖y - c‖ = ‖(y - (z + (τ : ℂ))) + (τ : ℂ) + (z - c)‖ := by congr 1; abel
        _ ≤ ‖y - (z + (τ : ℂ))‖ + ‖(τ : ℂ)‖ + ‖z - c‖ := norm_add₃_le
        _ < ρ₀ := by rw [Complex.norm_of_nonneg hτ.le, norm_sub_rev z c]; linarith
    · intro μ hμ
      apply hball
      have he : z + μ • (z + (τ : ℂ) - z) - c = (z - c) + μ • (τ : ℂ) := by module
      rw [mem_ball, dist_eq_norm, he]
      have hμτ : μ * τ ≤ τ := mul_le_of_le_one_left hτ.le hμ.2
      calc ‖(z - c) + μ • (τ : ℂ)‖ ≤ ‖z - c‖ + ‖μ • (τ : ℂ)‖ := norm_add_le _ _
        _ < ρ₀ := by
          rw [norm_smul, Real.norm_of_nonneg hμ.1.le, Complex.norm_of_nonneg hτ.le,
            norm_sub_rev]
          linarith

/-- P2.4 helper (upper bound): if the half-open segment `(z, p]` lies in `𝒟`, where `Φ` is
complex-differentiable with `|Φ'| ≤ K`, and `Φ` is continuous at `z`, then
`|Φ p - Φ z| ≤ K |p - z|`. -/
theorem s07d_p2_bl_upper {Φ : ℂ → ℂ} {𝒟 : Set ℂ} {z p : ℂ} {K : ℝ}
    (hd : ∀ x ∈ 𝒟, DifferentiableAt ℂ Φ x) (hb : ∀ x ∈ 𝒟, ‖deriv Φ x‖ ≤ K) (hK : 0 ≤ K)
    (hc : ContinuousAt Φ z) (hseg : ∀ μ ∈ Ioc (0 : ℝ) 1, z + μ • (p - z) ∈ 𝒟) :
    ‖Φ p - Φ z‖ ≤ K * ‖p - z‖ := by
  have hev : ∀ᶠ μ in 𝓝[>] (0 : ℝ), ‖Φ p - Φ (z + μ • (p - z))‖ ≤ K * ‖p - z‖ := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with μ hμ
    have h1m : 0 ≤ 1 - μ := by linarith [hμ.2]
    have hseg' : segment ℝ (z + μ • (p - z)) p ⊆ 𝒟 := by
      rw [segment_eq_image']
      rintro x ⟨θ, hθ, rfl⟩
      have h1 : 0 < μ + θ * (1 - μ) := by nlinarith [mul_nonneg hθ.1 h1m, hμ.1]
      have h2 : μ + θ * (1 - μ) ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right hθ.2 h1m]
      have h3 := hseg (μ + θ * (1 - μ)) ⟨h1, h2⟩
      have he : z + μ • (p - z) + θ • (p - (z + μ • (p - z))) =
          z + (μ + θ * (1 - μ)) • (p - z) := by module
      show z + μ • (p - z) + θ • (p - (z + μ • (p - z))) ∈ 𝒟
      rwa [he]
    have hm := (convex_segment (z + μ • (p - z)) p).norm_image_sub_le_of_norm_deriv_le
      (fun x hx => hd x (hseg' hx)) (fun x hx => hb x (hseg' hx))
      (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
    have he : p - (z + μ • (p - z)) = (1 - μ) • (p - z) := by module
    rw [he, norm_smul, Real.norm_of_nonneg h1m] at hm
    calc ‖Φ p - Φ (z + μ • (p - z))‖ ≤ K * ((1 - μ) * ‖p - z‖) := hm
      _ ≤ K * ‖p - z‖ :=
        mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hμ.1.le (norm_nonneg (p - z))]) hK
  have h1 : Tendsto (fun μ : ℝ => z + μ • (p - z)) (𝓝 0) (𝓝 z) := by
    have hcont : Continuous (fun μ : ℝ => z + μ • (p - z)) := by fun_prop
    simpa using hcont.tendsto 0
  have hT : Tendsto (fun μ : ℝ => ‖Φ p - Φ (z + μ • (p - z))‖) (𝓝[>] (0 : ℝ))
      (𝓝 ‖Φ p - Φ z‖) :=
    ((tendsto_const_nhds.sub (hc.tendsto.comp h1)).norm).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hT hev

/-- P2.4 helper (Koebe ¼ on a disc): if `Φ` is injective, holomorphic on `𝔻 ⊇ B(p, r)` and
`y ∉ B(p, r)`, then `r |Φ'(p)| ≤ 4 |Φ y - Φ p|`. -/
theorem s07d_p2_bl_koebe {Φ : ℂ → ℂ} {p y : ℂ} {r : ℝ} (hr : 0 < r) (hball : ball p r ⊆ unitDisc)
    (hdiff : DifferentiableOn ℂ Φ unitDisc) (hinj : InjOn Φ univ) (hy : y ∉ ball p r) :
    r * ‖deriv Φ p‖ ≤ 4 * ‖Φ y - Φ p‖ := by
  have hmaps : ∀ ζ ∈ ball (0 : ℂ) 1, p + (r : ℂ) * ζ ∈ ball p r := by
    intro ζ hζ
    rw [mem_ball_zero_iff] at hζ
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_of_nonneg hr.le]
    exact mul_lt_of_lt_one_right hr hζ
  have hψd : DifferentiableOn ℂ (fun ζ : ℂ => Φ (p + (r : ℂ) * ζ) - Φ p) (ball (0 : ℂ) 1) := by
    refine DifferentiableOn.sub_const ?_ _
    exact hdiff.comp (by fun_prop) (fun ζ hζ => hball (hmaps ζ hζ))
  have hψinj : InjOn (fun ζ : ℂ => Φ (p + (r : ℂ) * ζ) - Φ p) (ball (0 : ℂ) 1) := by
    intro a _ b _ hab
    have h1 : Φ (p + (r : ℂ) * a) = Φ (p + (r : ℂ) * b) := by simpa using hab
    have h2 := hinj (mem_univ _) (mem_univ _) h1
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
    exact mul_left_cancel₀ hr0 (add_left_cancel h2)
  have hw : Φ y - Φ p ∉ (fun ζ : ℂ => Φ (p + (r : ℂ) * ζ) - Φ p) '' ball (0 : ℂ) 1 := by
    rintro ⟨ζ, hζ, hζe⟩
    have h1 : Φ (p + (r : ℂ) * ζ) = Φ y := by simpa using hζe
    have h2 := hinj (mem_univ _) (mem_univ _) h1
    apply hy
    rw [← h2]
    exact hmaps ζ hζ
  have hK := koebe_quarter_of_not_mem hψd hψinj (by simp) hw
  have hpd : DifferentiableAt ℂ Φ p :=
    hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (hball (mem_ball_self hr)))
  have hlin : HasDerivAt (fun ζ : ℂ => p + (r : ℂ) * ζ) (r : ℂ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (r : ℂ)).const_add p
  have hd : HasDerivAt (fun ζ : ℂ => Φ (p + (r : ℂ) * ζ) - Φ p) (deriv Φ p * r) 0 :=
    (hpd.hasDerivAt.comp_of_eq (0 : ℂ) hlin (by simp)).sub_const (Φ p)
  rw [hd.deriv, norm_mul, Complex.norm_of_nonneg hr.le] at hK
  linarith [mul_comm r ‖deriv Φ p‖]

/-- P2.4 (BJ (2) ⇒ (3), quasidisk case): let `Φ` be a global `Q`-q.c. map, holomorphic on `𝔻`, and
`𝒟 ⊆ 𝔻` ball-star-shaped about `B(c, ρ₀)` with `𝒟 ⊆ B(c, A ρ₀)`. If `e^{-C} s ≤ |Φ'| ≤ e^C s` on
`𝒟`, then `Φ` is `L`-bi-Lipschitz at scale `s` on `closure 𝒟`, with `L` depending only on
`A, C, Q`. -/
theorem s07d_p2_bilip (A C Q : ℝ) (hA : 1 ≤ A) (hC : 0 ≤ C) (hQ : 1 ≤ Q) : ∃ L : ℝ, 1 ≤ L ∧
    ∀ (𝒟 : Set ℂ) (c : ℂ) (ρ₀ s : ℝ) (Φ : ℂ → ℂ), 0 < ρ₀ → 0 < s → IsOpen 𝒟 →
      ball c ρ₀ ⊆ 𝒟 → 𝒟 ⊆ unitDisc ∩ ball c (A * ρ₀) →
      (∀ p ∈ 𝒟, ∀ b ∈ ball c ρ₀, ∀ t ∈ Icc (0 : ℝ) 1, p + t • (b - p) ∈ 𝒟) →
      IsKQC Φ univ Q → Φ '' univ = univ → DifferentiableOn ℂ Φ unitDisc →
      (∀ z ∈ 𝒟, Real.exp (-C) * s ≤ ‖deriv Φ z‖ ∧ ‖deriv Φ z‖ ≤ Real.exp C * s) →
      ∀ z ∈ closure 𝒟, ∀ w ∈ closure 𝒟,
        s * ‖z - w‖ ≤ L * ‖Φ z - Φ w‖ ∧ ‖Φ z - Φ w‖ ≤ L * s * ‖z - w‖ := by
  -- The frozen hypothesis `0 ≤ C` is not needed by this proof (the statement stays true
  -- without it: only `e^{±C}` enter, and they are positive for every real `C`).
  have _hC := hC
  obtain ⟨C₀, hC₀, h3⟩ := lem_three_point Q hQ
  have hA0 : 0 < A := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ,
      L = max (32 * A ^ 2 * Real.exp C * C₀) (C₀ * (8 * A) ^ Q * Real.exp C) + 1 := ⟨_, rfl⟩
  have hL1 : 32 * A ^ 2 * Real.exp C * C₀ ≤ L := by
    rw [hLdef]; linarith [le_max_left (32 * A ^ 2 * Real.exp C * C₀) (C₀ * (8 * A) ^ Q * Real.exp C)]
  have hL2 : C₀ * (8 * A) ^ Q * Real.exp C ≤ L := by
    rw [hLdef]; linarith [le_max_right (32 * A ^ 2 * Real.exp C * C₀) (C₀ * (8 * A) ^ Q * Real.exp C)]
  have hL0 : 0 ≤ C₀ * (8 * A) ^ Q * Real.exp C := by positivity
  refine ⟨L, by
    rw [hLdef]; linarith [le_max_right (32 * A ^ 2 * Real.exp C * C₀) (C₀ * (8 * A) ^ Q * Real.exp C)],
    ?_⟩
  intro 𝒟 c ρ₀ s Φ hρ₀ hs h𝒟o hball hsub hst hΦ hsurj hdiff hder z hz w hw
  have hinj : InjOn Φ univ := hΦ.2.2.1.2.1
  have hcont : ContinuousOn Φ univ := hΦ.2.2.1.1
  rcases eq_or_ne z w with rfl | hzw
  · simp
  have ht : 0 < ‖z - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hzw)
  have hcl : closure 𝒟 ⊆ closedBall c (A * ρ₀) :=
    closure_minimal (fun x hx => ball_subset_closedBall (hsub hx).2) isClosed_closedBall
  have htb : ‖z - w‖ ≤ 2 * A * ρ₀ := by
    have h1 := hcl hz
    have h2 := hcl hw
    rw [mem_closedBall, dist_eq_norm] at h1 h2
    calc ‖z - w‖ = ‖(z - c) - (w - c)‖ := by congr 1; abel
      _ ≤ ‖z - c‖ + ‖w - c‖ := norm_sub_le _ _
      _ ≤ 2 * A * ρ₀ := by linarith
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = ‖z - w‖ / (8 * A) := ⟨_, rfl⟩
  have hτ : 0 < τ := by rw [hτdef]; positivity
  have hτρ : τ ≤ ρ₀ / 4 := by
    rw [hτdef, div_le_iff₀ (by positivity)]
    nlinarith
  have hτt : τ ≤ ‖z - w‖ := by
    rw [hτdef, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨p, hzp, hpb, hseg⟩ :=
    s07d_p2_bl_pick hA hρ₀ hball (fun x hx => (hsub hx).2) hst hz hτ hτρ
  have hτA : 0 < τ / A := div_pos hτ hA0
  have hp : p ∈ 𝒟 := hpb (mem_ball_self hτA)
  have hdx : ∀ x ∈ 𝒟, DifferentiableAt ℂ Φ x := fun x hx =>
    hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (hsub hx).1)
  -- upper bound on `|Φ p - Φ z|`
  have hU : ‖Φ p - Φ z‖ ≤ Real.exp C * s * ‖p - z‖ :=
    s07d_p2_bl_upper hdx (fun x hx => (hder x hx).2) (by positivity)
      (hcont.continuousAt univ_mem) hseg
  -- lower bound on `|Φ z - Φ p|` (Koebe ¼)
  have hKb : τ / A * ‖deriv Φ p‖ ≤ 4 * ‖Φ z - Φ p‖ := by
    refine s07d_p2_bl_koebe hτA (fun x hx => (hsub (hpb hx)).1) hdiff hinj ?_
    rw [mem_ball, dist_eq_norm, hzp, not_lt]
    exact div_le_self hτ.le hA
  have hzp' : z ≠ p := by
    intro h
    rw [h, sub_self, norm_zero] at hzp
    exact hτ.ne' hzp.symm
  have hΦzp : 0 < ‖Φ z - Φ p‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 (fun h => hzp' (hinj (mem_univ _) (mem_univ _) h)))
  have hΦzw : 0 < ‖Φ z - Φ w‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 (fun h => hzw (hinj (mem_univ _) (mem_univ _) h)))
  -- three-point estimate, ratio `8A`
  have hT1 : ‖Φ z - Φ w‖ ≤ C₀ * (8 * A) ^ Q * ‖Φ z - Φ p‖ := by
    have h := (h3 Φ hΦ hsurj z w p hzp').1
    have hr : ‖z - w‖ / ‖z - p‖ = 8 * A := by
      rw [hzp, hτdef]; field_simp
    rw [hr] at h
    have h8 : (1 : ℝ) ≤ 8 * A := by linarith
    have hQi : 1 / Q ≤ Q := le_trans ((div_le_one (by linarith)).2 hQ) hQ
    have hmax : max ((8 * A) ^ (1 / Q)) ((8 * A) ^ Q) ≤ (8 * A) ^ Q :=
      max_le (Real.rpow_le_rpow_of_exponent_le h8 hQi) le_rfl
    rw [div_le_iff₀ hΦzp] at h
    calc ‖Φ z - Φ w‖ ≤ C₀ * max ((8 * A) ^ (1 / Q)) ((8 * A) ^ Q) * ‖Φ z - Φ p‖ := h
      _ ≤ C₀ * (8 * A) ^ Q * ‖Φ z - Φ p‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax hC₀.le) hΦzp.le
  -- three-point estimate, ratio `1/(8A)`
  have hT2 : ‖Φ z - Φ p‖ ≤ C₀ * ‖Φ z - Φ w‖ := by
    have h := (h3 Φ hΦ hsurj z p w hzw).1
    have hx0 : 0 ≤ ‖z - p‖ / ‖z - w‖ := by positivity
    have hx1 : ‖z - p‖ / ‖z - w‖ ≤ 1 := by rw [hzp, div_le_one ht]; exact hτt
    have hQ0 : 0 ≤ 1 / Q := by positivity
    have hmax : max ((‖z - p‖ / ‖z - w‖) ^ (1 / Q)) ((‖z - p‖ / ‖z - w‖) ^ Q) ≤ 1 :=
      max_le (Real.rpow_le_one hx0 hx1 hQ0) (Real.rpow_le_one hx0 hx1 (by linarith))
    rw [div_le_iff₀ hΦzw] at h
    calc ‖Φ z - Φ p‖ ≤ C₀ * max ((‖z - p‖ / ‖z - w‖) ^ (1 / Q)) ((‖z - p‖ / ‖z - w‖) ^ Q) *
          ‖Φ z - Φ w‖ := h
      _ ≤ C₀ * 1 * ‖Φ z - Φ w‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax hC₀.le) hΦzw.le
      _ = C₀ * ‖Φ z - Φ w‖ := by rw [mul_one]
  constructor
  · have ha : τ / A * (Real.exp (-C) * s) ≤ 4 * (C₀ * ‖Φ z - Φ w‖) :=
      calc τ / A * (Real.exp (-C) * s) ≤ τ / A * ‖deriv Φ p‖ :=
            mul_le_mul_of_nonneg_left (hder p hp).1 hτA.le
        _ ≤ 4 * ‖Φ z - Φ p‖ := hKb
        _ ≤ 4 * (C₀ * ‖Φ z - Φ w‖) := by linarith
    have hst' : s * ‖z - w‖ = τ / A * (Real.exp (-C) * s) * (8 * A ^ 2 * Real.exp C) := by
      rw [hτdef, Real.exp_neg]
      field_simp
    calc s * ‖z - w‖ = τ / A * (Real.exp (-C) * s) * (8 * A ^ 2 * Real.exp C) := hst'
      _ ≤ 4 * (C₀ * ‖Φ z - Φ w‖) * (8 * A ^ 2 * Real.exp C) :=
        mul_le_mul_of_nonneg_right ha (by positivity)
      _ = 32 * A ^ 2 * Real.exp C * C₀ * ‖Φ z - Φ w‖ := by ring
      _ ≤ L * ‖Φ z - Φ w‖ := mul_le_mul_of_nonneg_right hL1 (norm_nonneg _)
  · have hpz : ‖p - z‖ = τ := by rw [norm_sub_rev]; exact hzp
    calc ‖Φ z - Φ w‖ ≤ C₀ * (8 * A) ^ Q * ‖Φ z - Φ p‖ := hT1
      _ ≤ C₀ * (8 * A) ^ Q * (Real.exp C * s * ‖p - z‖) := by
          rw [norm_sub_rev (Φ z)]
          exact mul_le_mul_of_nonneg_left hU (by positivity)
      _ ≤ C₀ * (8 * A) ^ Q * (Real.exp C * s * ‖z - w‖) := by
          rw [hpz]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hτt (by positivity)) (by positivity)
      _ = C₀ * (8 * A) ^ Q * Real.exp C * s * ‖z - w‖ := by ring
      _ ≤ L * s * ‖z - w‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL2 hs.le) ht.le

/-- P2.5 helper: a `K`-Lipschitz map on `S` (into `ℂ`) multiplies `μH[1]` by at most `K`. -/
theorem s07d_p2_ah_lip {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {f : X → ℂ} {S : Set X} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) ≤ K * dist x y) :
    μH[1] (f '' S) ≤ ENNReal.ofReal K * μH[1] S := by
  have hL : LipschitzOnWith (Real.toNNReal K) f S :=
    LipschitzOnWith.of_dist_le_mul (fun x hx y hy => by
      rw [Real.coe_toNNReal _ hK]; exact h x hx y hy)
  have h1 := hL.hausdorffMeasure_image_le (d := 1) zero_le_one
  rw [ENNReal.rpow_one] at h1
  exact h1

/-- P2.5 helper (chord vs. arc): `2 |θ| ≤ π |e^{iθ} - 1|` for `|θ| ≤ π`. -/
theorem s07d_p2_ah_chord (θ : ℝ) (hθ : |θ| ≤ π) : 2 * |θ| ≤ π * ‖exp (I * θ) - 1‖ := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  have hs := Real.sin_sq_eq_half_sub (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at hs
  have hc := Real.cos_le_one_sub_mul_cos_sq hθ
  have hπ := Real.pi_pos
  have hN : (2 * |θ|) ^ 2 ≤ (π * |2 * Real.sin (θ / 2)|) ^ 2 := by
    simp only [mul_pow, sq_abs]
    rw [hs]
    have h1 : 2 / π ^ 2 * θ ^ 2 * π ^ 2 = 2 * θ ^ 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg π)]
  exact (sq_le_sq₀ (by positivity) (by positivity)).1 hN

/-- P2.5 helper (arc length): `μH[1](∂𝔻 ∩ B(u₀, R)) ≤ π R` for `|u₀| = 1`. -/
theorem s07d_p2_ah_arc (u₀ : ℂ) (hu₀ : ‖u₀‖ = 1) (R : ℝ) :
    μH[1] (sphere (0 : ℂ) 1 ∩ ball u₀ R) ≤ ENNReal.ofReal (π * R) := by
  have hu0 : u₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu₀
    exact zero_ne_one hu₀
  have hsub : sphere (0 : ℂ) 1 ∩ ball u₀ R ⊆
      (fun θ : ℝ => u₀ * exp (I * θ)) '' Icc (-(π / 2 * R)) (π / 2 * R) := by
    rintro u ⟨hu, hub⟩
    rw [mem_sphere_zero_iff_norm] at hu
    rw [mem_ball, dist_eq_norm] at hub
    have hq : ‖u / u₀‖ = 1 := by rw [norm_div, hu, hu₀, div_one]
    have he : exp (I * (arg (u / u₀) : ℂ)) = u / u₀ := by
      have h := Complex.norm_mul_exp_arg_mul_I (u / u₀)
      rw [hq, Complex.ofReal_one, one_mul, mul_comm] at h
      exact h
    have hfu : u₀ * exp (I * (arg (u / u₀) : ℂ)) = u := by rw [he]; exact mul_div_cancel₀ u hu0
    have hd : ‖u - u₀‖ = ‖exp (I * (arg (u / u₀) : ℂ)) - 1‖ := by
      rw [he]
      calc ‖u - u₀‖ = ‖u₀ * (u / u₀ - 1)‖ := by rw [mul_sub, mul_div_cancel₀ u hu0, mul_one]
        _ = ‖u / u₀ - 1‖ := by rw [norm_mul, hu₀, one_mul]
    have hc := s07d_p2_ah_chord (arg (u / u₀)) (Complex.abs_arg_le_pi _)
    rw [← hd] at hc
    refine ⟨arg (u / u₀), ?_, hfu⟩
    rw [mem_Icc, ← abs_le]
    nlinarith [mul_le_mul_of_nonneg_left hub.le Real.pi_pos.le]
  have hlip : ∀ a ∈ Icc (-(π / 2 * R)) (π / 2 * R), ∀ b ∈ Icc (-(π / 2 * R)) (π / 2 * R),
      dist ((fun θ : ℝ => u₀ * exp (I * θ)) a) ((fun θ : ℝ => u₀ * exp (I * θ)) b) ≤
        1 * dist a b := by
    intro a _ b _
    rw [dist_eq_norm, dist_eq_norm, one_mul]
    have hea : exp (I * (a : ℂ)) = exp (I * (b : ℂ)) * exp (I * ((a - b : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    calc ‖u₀ * exp (I * (a : ℂ)) - u₀ * exp (I * (b : ℂ))‖
        = ‖u₀ * exp (I * (b : ℂ)) * (exp (I * ((a - b : ℝ) : ℂ)) - 1)‖ := by
          rw [hea]; congr 1; ring
      _ = ‖exp (I * ((a - b : ℝ) : ℂ)) - 1‖ := by
          rw [norm_mul, norm_mul, hu₀, Complex.norm_exp_I_mul_ofReal, one_mul, one_mul]
      _ ≤ ‖a - b‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
  calc μH[1] (sphere (0 : ℂ) 1 ∩ ball u₀ R)
      ≤ μH[1] ((fun θ : ℝ => u₀ * exp (I * θ)) '' Icc (-(π / 2 * R)) (π / 2 * R)) :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal 1 * μH[1] (Icc (-(π / 2 * R)) (π / 2 * R)) := s07d_p2_ah_lip zero_le_one hlip
    _ = ENNReal.ofReal (π * R) := by
        rw [ENNReal.ofReal_one, one_mul, hausdorffMeasure_real, Real.volume_Icc]
        congr 1; ring

/-- P2.5 (chord-arc output): under the hypotheses of P2.4, `Φ(∂𝒟)` is upper Ahlfors-regular with a
constant `M(A, C, Q)` (the form of S09 `IsAhlforsRegular`), its length is `≤ M s ρ₀`, and `Φ`
changes the length of subsets of `closure 𝒟` by a factor in `[s/M, M s]`. -/
theorem s07d_p2_ahlfors (A C Q : ℝ) (hA : 1 ≤ A) (hC : 0 ≤ C) (hQ : 1 ≤ Q) : ∃ M : ℝ, 1 ≤ M ∧
    ∀ (𝒟 : Set ℂ) (c : ℂ) (ρ₀ s : ℝ) (Φ : ℂ → ℂ), 0 < ρ₀ → 0 < s → IsOpen 𝒟 →
      ball c ρ₀ ⊆ 𝒟 → 𝒟 ⊆ unitDisc ∩ ball c (A * ρ₀) →
      (∀ p ∈ 𝒟, ∀ b ∈ ball c ρ₀, ∀ t ∈ Icc (0 : ℝ) 1, p + t • (b - p) ∈ 𝒟) →
      IsKQC Φ univ Q → Φ '' univ = univ → DifferentiableOn ℂ Φ unitDisc →
      (∀ z ∈ 𝒟, Real.exp (-C) * s ≤ ‖deriv Φ z‖ ∧ ‖deriv Φ z‖ ≤ Real.exp C * s) →
      (∀ x : ℂ, ∀ r : ℝ, 0 < r →
        μH[1] (Φ '' frontier 𝒟 ∩ ball x r) ≤ ENNReal.ofReal (M * r)) ∧
      μH[1] (Φ '' frontier 𝒟) ≤ ENNReal.ofReal (M * s * ρ₀) ∧
      ∀ B ⊆ closure 𝒟, ENNReal.ofReal (s / M) * μH[1] B ≤ μH[1] (Φ '' B) ∧
        μH[1] (Φ '' B) ≤ ENNReal.ofReal (M * s) * μH[1] B := by
  obtain ⟨L, hL1, hbl⟩ := s07d_p2_bilip A C Q hA hC hQ
  obtain ⟨Qk, hQk, hkap⟩ := s07d_p2_kappa A hA
  have hlam : 1 ≤ L * Qk := by nlinarith
  have hlam2 : L * Qk ≤ (L * Qk) ^ 2 := by nlinarith
  have hLl : L ≤ L * Qk := by nlinarith
  refine ⟨12 * (L * Qk) ^ 2, by nlinarith, ?_⟩
  intro 𝒟 c ρ₀ s Φ hρ₀ hs h𝒟o hball hsub hst hΦ hsurj hdiff hder
  have hB := hbl 𝒟 c ρ₀ s Φ hρ₀ hs h𝒟o hball hsub hst hΦ hsurj hdiff hder
  obtain ⟨κ, -, -, -, -, hκS, hκL⟩ := hkap 𝒟 c ρ₀ hρ₀ h𝒟o hball (fun x hx => (hsub hx).2) hst
  have hinj : InjOn Φ univ := hΦ.2.2.1.2.1
  have hσ : 0 < s * ρ₀ := mul_pos hs hρ₀
  have hfr : ∀ u ∈ sphere (0 : ℂ) 1, κ u ∈ closure 𝒟 := fun u hu =>
    frontier_subset_closure (by rw [← hκS]; exact mem_image_of_mem κ hu)
  have hgU : ∀ u ∈ sphere (0 : ℂ) 1, ∀ v ∈ sphere (0 : ℂ) 1,
      ‖Φ (κ u) - Φ (κ v)‖ ≤ L * Qk * (s * ρ₀) * ‖u - v‖ := by
    intro u hu v hv
    calc ‖Φ (κ u) - Φ (κ v)‖ ≤ L * s * ‖κ u - κ v‖ := (hB _ (hfr u hu) _ (hfr v hv)).2
      _ ≤ L * s * (Qk * ρ₀ * ‖u - v‖) :=
          mul_le_mul_of_nonneg_left (hκL u v).2 (by positivity)
      _ = L * Qk * (s * ρ₀) * ‖u - v‖ := by ring
  have hgL : ∀ u ∈ sphere (0 : ℂ) 1, ∀ v ∈ sphere (0 : ℂ) 1,
      s * ρ₀ * ‖u - v‖ ≤ L * Qk * ‖Φ (κ u) - Φ (κ v)‖ := by
    intro u hu v hv
    calc s * ρ₀ * ‖u - v‖ = s * (ρ₀ * ‖u - v‖) := by ring
      _ ≤ s * (Qk * ‖κ u - κ v‖) := mul_le_mul_of_nonneg_left (hκL u v).1 hs.le
      _ = Qk * (s * ‖κ u - κ v‖) := by ring
      _ ≤ Qk * (L * ‖Φ (κ u) - Φ (κ v)‖) :=
          mul_le_mul_of_nonneg_left (hB _ (hfr u hu) _ (hfr v hv)).1 (by linarith)
      _ = L * Qk * ‖Φ (κ u) - Φ (κ v)‖ := by ring
  have himg : Φ '' frontier 𝒟 = (fun u => Φ (κ u)) '' sphere (0 : ℂ) 1 := by
    rw [← hκS, image_image]
  have hglip : ∀ T ⊆ sphere (0 : ℂ) 1,
      μH[1] ((fun u => Φ (κ u)) '' T) ≤ ENNReal.ofReal (L * Qk * (s * ρ₀)) * μH[1] T := by
    intro T hT
    refine s07d_p2_ah_lip (by positivity) (fun u hu v hv => ?_)
    rw [dist_eq_norm, dist_eq_norm]
    exact hgU u (hT hu) v (hT hv)
  refine ⟨?_, ?_, ?_⟩
  · intro x r hr
    rw [himg, ← image_inter_preimage]
    rcases (sphere (0 : ℂ) 1 ∩ (fun u => Φ (κ u)) ⁻¹' ball x r).eq_empty_or_nonempty with hT | hT
    · rw [hT, image_empty, measure_empty]
      exact zero_le
    obtain ⟨u₀, hu₀s, hu₀b⟩ := hT
    have hTs : sphere (0 : ℂ) 1 ∩ (fun u => Φ (κ u)) ⁻¹' ball x r ⊆
        sphere (0 : ℂ) 1 ∩ ball u₀ (2 * (L * Qk) * r / (s * ρ₀)) := by
      rintro u ⟨hus, hub⟩
      refine ⟨hus, ?_⟩
      rw [mem_ball, dist_eq_norm, lt_div_iff₀ hσ]
      rw [mem_preimage, mem_ball, dist_eq_norm] at hub hu₀b
      have h1 := hgL u hus u₀ hu₀s
      have h2 : ‖Φ (κ u) - Φ (κ u₀)‖ < 2 * r := by
        calc ‖Φ (κ u) - Φ (κ u₀)‖ = ‖(Φ (κ u) - x) - (Φ (κ u₀) - x)‖ := by congr 1; abel
          _ ≤ ‖Φ (κ u) - x‖ + ‖Φ (κ u₀) - x‖ := norm_sub_le _ _
          _ < 2 * r := by linarith
      have h3 : L * Qk * ‖Φ (κ u) - Φ (κ u₀)‖ < L * Qk * (2 * r) :=
        mul_lt_mul_of_pos_left h2 (by linarith)
      linarith
    have hu₀1 : ‖u₀‖ = 1 := by rwa [mem_sphere_zero_iff_norm] at hu₀s
    have hreal : L * Qk * (s * ρ₀) * (π * (2 * (L * Qk) * r / (s * ρ₀))) ≤
        12 * (L * Qk) ^ 2 * r := by
      have he : L * Qk * (s * ρ₀) * (π * (2 * (L * Qk) * r / (s * ρ₀))) =
          2 * π * ((L * Qk) ^ 2 * r) := by
        field_simp
      rw [he]
      have h4 := Real.pi_le_four
      have h0 : 0 ≤ (L * Qk) ^ 2 * r := by positivity
      nlinarith
    calc μH[1] ((fun u => Φ (κ u)) '' (sphere (0 : ℂ) 1 ∩ (fun u => Φ (κ u)) ⁻¹' ball x r))
        ≤ ENNReal.ofReal (L * Qk * (s * ρ₀)) *
            μH[1] (sphere (0 : ℂ) 1 ∩ (fun u => Φ (κ u)) ⁻¹' ball x r) :=
          hglip _ inter_subset_left
      _ ≤ ENNReal.ofReal (L * Qk * (s * ρ₀)) *
            μH[1] (sphere (0 : ℂ) 1 ∩ ball u₀ (2 * (L * Qk) * r / (s * ρ₀))) := by
          gcongr
      _ ≤ ENNReal.ofReal (L * Qk * (s * ρ₀)) *
            ENNReal.ofReal (π * (2 * (L * Qk) * r / (s * ρ₀))) := by
          gcongr
          exact s07d_p2_ah_arc u₀ hu₀1 _
      _ = ENNReal.ofReal (L * Qk * (s * ρ₀) * (π * (2 * (L * Qk) * r / (s * ρ₀)))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (12 * (L * Qk) ^ 2 * r) := ENNReal.ofReal_le_ofReal hreal
  · rw [himg]
    have hsb : sphere (0 : ℂ) 1 ⊆ sphere (0 : ℂ) 1 ∩ ball 1 3 := by
      intro u hu
      refine ⟨hu, ?_⟩
      rw [mem_sphere_zero_iff_norm] at hu
      rw [mem_ball, dist_eq_norm]
      have := norm_sub_le u 1
      rw [hu, norm_one] at this
      linarith
    have hreal : L * Qk * (s * ρ₀) * (π * 3) ≤ 12 * (L * Qk) ^ 2 * s * ρ₀ := by
      have h4 := Real.pi_le_four
      have h5 : L * Qk * (s * ρ₀) * (π * 3) ≤ L * Qk * (s * ρ₀) * 12 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h6 : L * Qk * (s * ρ₀) * 12 ≤ (L * Qk) ^ 2 * (s * ρ₀) * 12 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlam2 hσ.le) (by norm_num)
      nlinarith
    calc μH[1] ((fun u => Φ (κ u)) '' sphere (0 : ℂ) 1)
        ≤ ENNReal.ofReal (L * Qk * (s * ρ₀)) * μH[1] (sphere (0 : ℂ) 1) := hglip _ subset_rfl
      _ ≤ ENNReal.ofReal (L * Qk * (s * ρ₀)) * μH[1] (sphere (0 : ℂ) 1 ∩ ball 1 3) := by
          gcongr
      _ ≤ ENNReal.ofReal (L * Qk * (s * ρ₀)) * ENNReal.ofReal (π * 3) := by
          gcongr
          exact s07d_p2_ah_arc 1 norm_one 3
      _ = ENNReal.ofReal (L * Qk * (s * ρ₀) * (π * 3)) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (12 * (L * Qk) ^ 2 * s * ρ₀) := ENNReal.ofReal_le_ofReal hreal
  · intro B hBc
    have hM : L ≤ 12 * (L * Qk) ^ 2 := by nlinarith
    have hMpos : 0 < 12 * (L * Qk) ^ 2 := by positivity
    constructor
    · have hm : μH[1] B ≤ ENNReal.ofReal (L / s) * μH[1] (Φ '' B) := by
        have hcov : B ⊆ Function.invFunOn Φ B '' (Φ '' B) := by
          intro z hz
          refine ⟨Φ z, mem_image_of_mem Φ hz, ?_⟩
          have he : Φ (Function.invFunOn Φ B (Φ z)) = Φ z :=
            Function.invFunOn_eq ⟨z, hz, rfl⟩
          exact hinj (mem_univ _) (mem_univ _) he
        refine (measure_mono hcov).trans (s07d_p2_ah_lip (by positivity) ?_)
        intro u hu v hv
        obtain ⟨z, hz, rfl⟩ := hu
        obtain ⟨w, hw, rfl⟩ := hv
        have hz1 : Function.invFunOn Φ B (Φ z) ∈ B := Function.invFunOn_mem ⟨z, hz, rfl⟩
        have hw1 : Function.invFunOn Φ B (Φ w) ∈ B := Function.invFunOn_mem ⟨w, hw, rfl⟩
        have hz2 : Φ (Function.invFunOn Φ B (Φ z)) = Φ z := Function.invFunOn_eq ⟨z, hz, rfl⟩
        have hw2 : Φ (Function.invFunOn Φ B (Φ w)) = Φ w := Function.invFunOn_eq ⟨w, hw, rfl⟩
        have h1 := (hB _ (hBc hz1) _ (hBc hw1)).1
        rw [hz2, hw2] at h1
        rw [dist_eq_norm, dist_eq_norm, div_mul_eq_mul_div, le_div_iff₀ hs]
        linarith [mul_comm s ‖Function.invFunOn Φ B (Φ z) - Function.invFunOn Φ B (Φ w)‖]
      calc ENNReal.ofReal (s / (12 * (L * Qk) ^ 2)) * μH[1] B
          ≤ ENNReal.ofReal (s / (12 * (L * Qk) ^ 2)) * (ENNReal.ofReal (L / s) * μH[1] (Φ '' B)) := by
            gcongr
        _ = ENNReal.ofReal (s / (12 * (L * Qk) ^ 2) * (L / s)) * μH[1] (Φ '' B) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ 1 * μH[1] (Φ '' B) := by
            gcongr
            rw [ENNReal.ofReal_le_one, div_mul_div_comm, div_le_one (by positivity)]
            nlinarith
        _ = μH[1] (Φ '' B) := one_mul _
    · calc μH[1] (Φ '' B) ≤ ENNReal.ofReal (L * s) * μH[1] B := by
            refine s07d_p2_ah_lip (by positivity) (fun z hz w hw => ?_)
            rw [dist_eq_norm, dist_eq_norm]
            exact (hB z (hBc hz) w (hBc hw)).2
        _ ≤ ENNReal.ofReal (12 * (L * Qk) ^ 2 * s) * μH[1] B := by
            gcongr

/-! ## P7: self-improvement (one weak-`A∞` pair ⇒ strong quasisymmetry) -/

/-- P7 helper: membership in the dyadic interval `I_{n,j}` of `[a, b)` via the dyadic index. -/
theorem s07d_p7_mem_iff {a b : ℝ} (hab : a < b) (n j : ℕ) (x : ℝ) :
    x ∈ Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n)) ↔
      a ≤ x ∧ ⌊(x - a) / ((b - a) / 2 ^ n)⌋₊ = j := by
  have hℓ : 0 < (b - a) / 2 ^ n := div_pos (sub_pos.2 hab) (pow_pos two_pos n)
  constructor
  · rintro ⟨h1, h2⟩
    have ha : a ≤ x := le_trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) hℓ.le)) h1
    refine ⟨ha, ?_⟩
    rw [Nat.floor_eq_iff (div_nonneg (sub_nonneg.2 ha) hℓ.le), le_div_iff₀ hℓ, div_lt_iff₀ hℓ]
    constructor <;> linarith
  · rintro ⟨ha, hj⟩
    have h := (Nat.floor_eq_iff (div_nonneg (sub_nonneg.2 ha) hℓ.le)).1 hj
    rw [le_div_iff₀ hℓ, div_lt_iff₀ hℓ] at h
    constructor <;> linarith [h.1, h.2]

/-- P7 helper: dyadic indices are nested. -/
theorem s07d_p7_floor_nest {a b : ℝ} (hab : a < b) {n m : ℕ} (hnm : n ≤ m) {x : ℝ} :
    ⌊(x - a) / ((b - a) / 2 ^ n)⌋₊ = ⌊(x - a) / ((b - a) / 2 ^ m)⌋₊ / 2 ^ (m - n) := by
  have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
  have h2 : (2 : ℝ) ^ m = 2 ^ n * 2 ^ (m - n) := by rw [← pow_add, Nat.add_sub_cancel' hnm]
  have : (x - a) / ((b - a) / 2 ^ n) =
      (x - a) / ((b - a) / 2 ^ m) / ((2 ^ (m - n) : ℕ) : ℝ) := by
    push_cast
    rw [h2]
    field_simp
  rw [this, Nat.floor_div_natCast]

/-- P7 helper: a dyadic interval lies in its ancestors. -/
theorem s07d_p7_mem_anc {a b : ℝ} (hab : a < b) {n m k : ℕ} (hnm : n ≤ m) {x : ℝ}
    (hx : x ∈ Ico (a + k * ((b - a) / 2 ^ m)) (a + (k + 1) * ((b - a) / 2 ^ m))) :
    x ∈ Ico (a + ((k / 2 ^ (m - n) : ℕ) : ℝ) * ((b - a) / 2 ^ n))
      (a + (((k / 2 ^ (m - n) : ℕ) : ℝ) + 1) * ((b - a) / 2 ^ n)) := by
  rw [s07d_p7_mem_iff hab] at hx ⊢
  exact ⟨hx.1, by rw [s07d_p7_floor_nest hab hnm, hx.2]⟩

/-- P7 helper: dyadic intervals of the same level are disjoint. -/
theorem s07d_p7_uniq {a b : ℝ} (hab : a < b) {n j j' : ℕ} {x : ℝ}
    (hx : x ∈ Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n)))
    (hx' : x ∈ Ico (a + j' * ((b - a) / 2 ^ n)) (a + (j' + 1) * ((b - a) / 2 ^ n))) : j = j' := by
  rw [s07d_p7_mem_iff hab] at hx hx'
  rw [← hx.2, hx'.2]

/-- P7 helper (stopping time): summing over the maximal intervals of a dyadic family. -/
theorem s07d_p7_sum {a b : ℝ} (hab : a < b) (P : ℕ → ℕ → Prop) (μ₁ μ₂ : Measure ℝ) (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (c : ℝ≥0∞)
    (h : ∀ m k : ℕ, k < 2 ^ m → P m k → (∀ n < m, ¬ P n (k / 2 ^ (m - n))) →
      μ₁ (A ∩ Ico (a + k * ((b - a) / 2 ^ m)) (a + (k + 1) * ((b - a) / 2 ^ m))) ≤
        c * μ₂ (B ∩ Ico (a + k * ((b - a) / 2 ^ m)) (a + (k + 1) * ((b - a) / 2 ^ m)))) :
    μ₁ (A ∩ ⋃ (n : ℕ) (j : ℕ) (_ : j < 2 ^ n ∧ P n j),
        Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))) ≤
      c * μ₂ (B ∩ ⋃ (n : ℕ) (j : ℕ) (_ : j < 2 ^ n ∧ P n j),
        Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))) := by
  classical
  have hU : (⋃ (n : ℕ) (j : ℕ) (_ : j < 2 ^ n ∧ P n j),
      Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))) =
      ⋃ p : ℕ × ℕ, ⋃ (_ : p.2 < 2 ^ p.1 ∧ P p.1 p.2 ∧ ∀ n < p.1, ¬ P n (p.2 / 2 ^ (p.1 - n))),
        Ico (a + p.2 * ((b - a) / 2 ^ p.1)) (a + (p.2 + 1) * ((b - a) / 2 ^ p.1)) := by
    ext x
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨n, j, ⟨hj, hP⟩, hx⟩
      have hax : a ≤ x := ((s07d_p7_mem_iff hab n j x).1 hx).1
      have hidx : ⌊(x - a) / ((b - a) / 2 ^ n)⌋₊ = j := ((s07d_p7_mem_iff hab n j x).1 hx).2
      have hPn : P n ⌊(x - a) / ((b - a) / 2 ^ n)⌋₊ := by rw [hidx]; exact hP
      have hex : ∃ m, P m ⌊(x - a) / ((b - a) / 2 ^ m)⌋₊ := ⟨n, hPn⟩
      have hmn : Nat.find hex ≤ n := Nat.find_min' hex hPn
      refine ⟨(Nat.find hex, ⌊(x - a) / ((b - a) / 2 ^ Nat.find hex)⌋₊),
        ⟨?_, Nat.find_spec hex, ?_⟩, (s07d_p7_mem_iff hab _ _ x).2 ⟨hax, rfl⟩⟩
      · show ⌊(x - a) / ((b - a) / 2 ^ Nat.find hex)⌋₊ < 2 ^ Nat.find hex
        rw [s07d_p7_floor_nest hab hmn, hidx]
        exact (Nat.div_lt_iff_lt_mul (by positivity)).2
          (by rw [← pow_add, Nat.add_sub_cancel' hmn]; exact hj)
      · intro n' hn' hP'
        rw [← s07d_p7_floor_nest hab hn'.le] at hP'
        exact Nat.find_min hex hn' hP'
    · rintro ⟨⟨m, k⟩, ⟨hk, hP, -⟩, hx⟩
      exact ⟨m, k, ⟨hk, hP⟩, hx⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun p : ℕ × ℕ =>
      ⋃ (_ : p.2 < 2 ^ p.1 ∧ P p.1 p.2 ∧ ∀ n < p.1, ¬ P n (p.2 / 2 ^ (p.1 - n))),
        Ico (a + p.2 * ((b - a) / 2 ^ p.1)) (a + (p.2 + 1) * ((b - a) / 2 ^ p.1))) := by
    intro p q hpq
    rw [Function.onFun, Set.disjoint_left]
    intro x hxp hxq
    simp only [mem_iUnion, exists_prop] at hxp hxq
    obtain ⟨⟨-, hp2, hp3⟩, hxp⟩ := hxp
    obtain ⟨⟨-, hq2, hq3⟩, hxq⟩ := hxq
    rcases lt_trichotomy p.1 q.1 with hl | hl | hl
    · apply hq3 p.1 hl
      rw [← s07d_p7_uniq hab hxp (s07d_p7_mem_anc hab hl.le hxq)]
      exact hp2
    · apply hpq
      rw [← hl] at hxq
      exact Prod.ext hl (s07d_p7_uniq hab hxp hxq)
    · apply hp3 q.1 hl
      rw [← s07d_p7_uniq hab hxq (s07d_p7_mem_anc hab hl.le hxp)]
      exact hq2
  have hmeas : ∀ (C : Set ℝ), MeasurableSet C → ∀ p : ℕ × ℕ, MeasurableSet (C ∩
      ⋃ (_ : p.2 < 2 ^ p.1 ∧ P p.1 p.2 ∧ ∀ n < p.1, ¬ P n (p.2 / 2 ^ (p.1 - n))),
        Ico (a + p.2 * ((b - a) / 2 ^ p.1)) (a + (p.2 + 1) * ((b - a) / 2 ^ p.1))) :=
    fun C hC p => hC.inter (MeasurableSet.iUnion fun _ => measurableSet_Ico)
  rw [hU, inter_iUnion, inter_iUnion,
    measure_iUnion (fun p q hpq => (hdisj hpq).mono inter_subset_right inter_subset_right)
      (hmeas A hA),
    measure_iUnion (fun p q hpq => (hdisj hpq).mono inter_subset_right inter_subset_right)
      (hmeas B hB), ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun p => ?_
  by_cases hp : p.2 < 2 ^ p.1 ∧ P p.1 p.2 ∧ ∀ n < p.1, ¬ P n (p.2 / 2 ^ (p.1 - n))
  · have e : ∀ (q : Prop) (S : Set ℝ), q → (⋃ (_ : q), S) = S := fun q S hq => by
      ext x; simp only [mem_iUnion, exists_prop, and_iff_right hq]
    rw [e _ _ hp]
    exact h p.1 p.2 hp.1 hp.2.1 hp.2.2
  · rw [iUnion_eq_empty.2 fun h' => absurd h' hp, inter_empty, measure_empty]
    exact bot_le

/-- P7 helper (density on stopping intervals): if no strict ancestor of `I_{m₀,k₀}` is `Q`-good
and each `Q`-good interval satisfies `|I| ≤ c |G ∩ I|`, then `|Ω_Q ∩ I_{m₀,k₀}| ≤ c |G ∩ I_{m₀,k₀}|`. -/
theorem s07d_p7_vol {a b : ℝ} (hab : a < b) (G : Set ℝ) (hG : MeasurableSet G)
    (Q : ℕ → ℕ → Prop) (c : ℝ≥0∞)
    (hQ : ∀ n j : ℕ, Q n j → volume (Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n)))
      ≤ c * volume (G ∩ Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))))
    (m₀ k₀ : ℕ) (hanc : ∀ n < m₀, ¬ Q n (k₀ / 2 ^ (m₀ - n))) :
    volume ((⋃ (n : ℕ) (j : ℕ) (_ : j < 2 ^ n ∧ Q n j),
        Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))) ∩
        Ico (a + k₀ * ((b - a) / 2 ^ m₀)) (a + (k₀ + 1) * ((b - a) / 2 ^ m₀))) ≤
      c * volume (G ∩ Ico (a + k₀ * ((b - a) / 2 ^ m₀)) (a + (k₀ + 1) * ((b - a) / 2 ^ m₀))) := by
  have hsub1 : (⋃ (n : ℕ) (j : ℕ) (_ : j < 2 ^ n ∧ Q n j),
        Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))) ∩
        Ico (a + k₀ * ((b - a) / 2 ^ m₀)) (a + (k₀ + 1) * ((b - a) / 2 ^ m₀)) ⊆
      ⋃ (n : ℕ) (j : ℕ) (_ : j < 2 ^ n ∧ (Q n j ∧ m₀ ≤ n ∧ j / 2 ^ (n - m₀) = k₀)),
        Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n)) := by
    rintro x ⟨hx, hx0⟩
    simp only [mem_iUnion, exists_prop] at hx ⊢
    obtain ⟨n, j, ⟨hj, hQnj⟩, hxn⟩ := hx
    rcases le_or_gt m₀ n with hl | hl
    · exact ⟨n, j, ⟨hj, hQnj, hl, s07d_p7_uniq hab (s07d_p7_mem_anc hab hl hxn) hx0⟩, hxn⟩
    · exfalso
      apply hanc n hl
      rw [s07d_p7_uniq hab (s07d_p7_mem_anc hab hl.le hx0) hxn]
      exact hQnj
  have hsub2 : (⋃ (n : ℕ) (j : ℕ) (_ : j < 2 ^ n ∧ (Q n j ∧ m₀ ≤ n ∧ j / 2 ^ (n - m₀) = k₀)),
        Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))) ⊆
      Ico (a + k₀ * ((b - a) / 2 ^ m₀)) (a + (k₀ + 1) * ((b - a) / 2 ^ m₀)) := by
    intro x hx
    simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨n, j, ⟨-, -, hl, hjk⟩, hxn⟩ := hx
    have := s07d_p7_mem_anc hab hl hxn
    rwa [hjk] at this
  have key := s07d_p7_sum hab (fun n j => Q n j ∧ m₀ ≤ n ∧ j / 2 ^ (n - m₀) = k₀) volume volume
    univ G MeasurableSet.univ hG c (fun m k _ hP _ => by rw [univ_inter]; exact hQ m k hP.1)
  rw [univ_inter] at key
  calc _ ≤ _ := measure_mono hsub1
    _ ≤ _ := key
    _ ≤ _ := by gcongr

/-- P7 helper: the weak `A∞` hypothesis forces `ν` to have no atoms in `(a, b]`. -/
theorem s07d_p7_atom {α β : ℝ} (hβ : β < 1) (ν : Measure ℝ) {a b : ℝ}
    (hν : ν (Icc a b) ≠ ⊤)
    (hw : ∀ c d : ℝ, a ≤ c → c < d → d ≤ b → ∀ S ⊆ Icc c d, MeasurableSet S →
      volume S ≤ ENNReal.ofReal (α * (d - c)) → ν S ≤ ENNReal.ofReal β * ν (Icc c d))
    {d : ℝ} (had : a < d) (hdb : d ≤ b) : ν {d} = 0 := by
  have hda : 0 < d - a := sub_pos.2 had
  have hc_a : ∀ n : ℕ, a ≤ d - (d - a) / (n + 1) := fun n => by
    have : (d - a) / (n + 1) ≤ d - a :=
      div_le_self hda.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    linarith
  have hc_d : ∀ n : ℕ, d - (d - a) / (n + 1) < d := fun n => by
    have : 0 < (d - a) / (n + 1) := by positivity
    linarith
  have hbound : ∀ n : ℕ, ν {d} ≤ ENNReal.ofReal β * ν (Icc (d - (d - a) / (n + 1)) d) := fun n =>
    hw _ d (hc_a n) (hc_d n) hdb {d} (singleton_subset_iff.2 ⟨(hc_d n).le, le_rfl⟩)
      (measurableSet_singleton d) (by rw [Real.volume_singleton]; exact bot_le)
  have hanti : Antitone fun n : ℕ => Icc (d - (d - a) / (n + 1)) d := by
    intro n m hnm
    refine Icc_subset_Icc_left ?_
    have : (d - a) / (m + 1) ≤ (d - a) / (n + 1) :=
      div_le_div_of_nonneg_left hda.le (by positivity) (by exact_mod_cast Nat.succ_le_succ hnm)
    linarith
  have hinter : (⋂ n : ℕ, Icc (d - (d - a) / (n + 1)) d) = {d} := by
    ext x
    simp only [mem_iInter, mem_Icc, mem_singleton_iff]
    constructor
    · intro hx
      refine le_antisymm (hx 0).2 ?_
      by_contra hlt
      push Not at hlt
      obtain ⟨n, hn⟩ := exists_nat_gt ((d - a) / (d - x))
      rw [div_lt_iff₀ (sub_pos.2 hlt)] at hn
      have h1 := (hx n).1
      have : (d - a) / (n + 1) < d - x := by
        rw [div_lt_iff₀ (by positivity)]
        linarith
      linarith
    · rintro rfl
      exact fun n => ⟨(hc_d n).le, le_rfl⟩
  have htend := tendsto_measure_iInter_atTop (μ := ν)
    (s := fun n : ℕ => Icc (d - (d - a) / ((n : ℝ) + 1)) d)
    (fun n => measurableSet_Icc.nullMeasurableSet)
    hanti ⟨0, ne_top_of_le_ne_top hν (measure_mono (Icc_subset_Icc (hc_a 0) hdb))⟩
  rw [hinter] at htend
  have hle : ν {d} ≤ ENNReal.ofReal β * ν {d} :=
    ge_of_tendsto' (ENNReal.Tendsto.const_mul htend (Or.inr ENNReal.ofReal_ne_top)) hbound
  have hfin : ν {d} ≠ ⊤ :=
    ne_top_of_le_ne_top hν (measure_mono (singleton_subset_iff.2 ⟨had.le, hdb⟩))
  by_contra h0
  have := ENNReal.mul_lt_mul_right h0 hfin (ENNReal.ofReal_lt_one.2 hβ)
  rw [mul_one, mul_comm] at this
  exact absurd hle (not_le.2 this)

/-- **P7.1** (`level`, one Calderón–Zygmund step): for an open `G`, thresholds `0 < t < s < 1` with
`2t ≤ α s` and `|G ∩ [a, b]| ≤ t (b - a)`, let `Ω_r` be the union of the dyadic intervals
`[a + j ℓ_n, a + (j+1) ℓ_n)` (`ℓ_n = (b - a)/2^n`, `j < 2^n`) on which `G` has density `> r`.
Then `ν(Ω_s) ≤ β ν(Ω_t)`. -/
theorem s07d_p7_level {α β : ℝ} (hα : 0 < α) (hβ : β < 1) (ν : Measure ℝ) {a b : ℝ} (hab : a < b)
    (hν : ν (Icc a b) ≠ ⊤)
    (hw : ∀ c d : ℝ, a ≤ c → c < d → d ≤ b → ∀ S ⊆ Icc c d, MeasurableSet S →
      volume S ≤ ENNReal.ofReal (α * (d - c)) → ν S ≤ ENNReal.ofReal β * ν (Icc c d))
    (G : Set ℝ) (hG : IsOpen G) {t s : ℝ} (ht : 0 < t) (hts : t < s) (hs : s < 1) (htα : 2 * t ≤ α * s)
    (hGt : volume (G ∩ Icc a b) ≤ ENNReal.ofReal (t * (b - a))) :
    ν (⋃ (n : ℕ) (j : ℕ) (_ : j < 2 ^ n ∧ ENNReal.ofReal (s * ((b - a) / 2 ^ n)) <
        volume (G ∩ Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n)))),
        Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))) ≤
      ENNReal.ofReal β * ν (⋃ (n : ℕ) (j : ℕ) (_ : j < 2 ^ n ∧
        ENNReal.ofReal (t * ((b - a) / 2 ^ n)) <
          volume (G ∩ Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n)))),
        Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))) := by
  have hℓ : ∀ n : ℕ, 0 < (b - a) / 2 ^ n := fun n => div_pos (sub_pos.2 hab) (pow_pos two_pos n)
  have hs0 : 0 < s := ht.trans hts
  have hs' : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.2 hs0).ne'
  have hGm : MeasurableSet G := hG.measurableSet
  have hQP : ∀ n j : ℕ, ENNReal.ofReal (s * ((b - a) / 2 ^ n)) <
      volume (G ∩ Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))) →
      ENNReal.ofReal (t * ((b - a) / 2 ^ n)) <
      volume (G ∩ Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))) :=
    fun n j h => lt_of_le_of_lt
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hts.le (hℓ n).le)) h
  set Ωs := ⋃ (n : ℕ) (j : ℕ) (_ : j < 2 ^ n ∧ ENNReal.ofReal (s * ((b - a) / 2 ^ n)) <
        volume (G ∩ Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n)))),
        Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n)) with hΩs
  set Ωt := ⋃ (n : ℕ) (j : ℕ) (_ : j < 2 ^ n ∧
        ENNReal.ofReal (t * ((b - a) / 2 ^ n)) <
          volume (G ∩ Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n)))),
        Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n)) with hΩt
  have hsub : Ωs ⊆ Ωt := by
    intro x hx
    simp only [hΩs, hΩt, mem_iUnion, exists_prop] at hx ⊢
    obtain ⟨n, j, ⟨hj, hg⟩, hx⟩ := hx
    exact ⟨n, j, ⟨hj, hQP n j hg⟩, hx⟩
  have hmeasQ : MeasurableSet Ωs :=
    MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun j =>
      MeasurableSet.iUnion fun _ => measurableSet_Ico
  have hQ : ∀ n j : ℕ, ENNReal.ofReal (s * ((b - a) / 2 ^ n)) <
      volume (G ∩ Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))) →
      volume (Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))) ≤
        (ENNReal.ofReal s)⁻¹ *
          volume (G ∩ Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))) := by
    intro n j hq
    have h1 : ENNReal.ofReal s *
        volume (Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))) ≤
        volume (G ∩ Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))) := by
      rw [Real.volume_Ico, ← ENNReal.ofReal_mul hs0.le,
        show a + ((j : ℝ) + 1) * ((b - a) / 2 ^ n) - (a + j * ((b - a) / 2 ^ n)) =
          (b - a) / 2 ^ n by ring]
      exact hq.le
    exact (ENNReal.inv_mul_cancel_left hs' ENNReal.ofReal_ne_top).symm.le.trans
      (mul_le_mul_of_nonneg_left h1 (by positivity))
  have key : ν (Ωs ∩ Ωt) ≤ ENNReal.ofReal β * ν (univ ∩ Ωt) := by
    refine s07d_p7_sum hab (fun n j => ENNReal.ofReal (t * ((b - a) / 2 ^ n)) <
      volume (G ∩ Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n)))) ν ν Ωs univ
      hmeasQ MeasurableSet.univ _ ?_
    intro m k hk hP hanc
    beta_reduce at hP hanc
    rw [univ_inter]
    have hm : m ≠ 0 := by
      rintro rfl
      have hk0 : k = 0 := by simpa using hk
      subst hk0
      apply absurd hP
      rw [not_lt]
      simp only [pow_zero, div_one, Nat.cast_zero, zero_mul, add_zero, zero_add, one_mul]
      rw [show a + (b - a) = b by ring]
      exact (measure_mono (inter_subset_inter_right _ Ico_subset_Icc_self)).trans hGt
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hpar := hanc m' (Nat.lt_succ_self m')
    rw [not_lt, show m' + 1 - m' = 1 by omega, pow_one] at hpar
    have hDsub : Ico (a + k * ((b - a) / 2 ^ (m' + 1))) (a + (k + 1) * ((b - a) / 2 ^ (m' + 1))) ⊆
        Ico (a + ((k / 2 : ℕ) : ℝ) * ((b - a) / 2 ^ m'))
          (a + (((k / 2 : ℕ) : ℝ) + 1) * ((b - a) / 2 ^ m')) := fun x hx => by
      have := s07d_p7_mem_anc hab (Nat.le_succ m') hx
      rwa [show m' + 1 - m' = 1 by omega, pow_one] at this
    have e2 : (b - a) / 2 ^ m' = 2 * ((b - a) / 2 ^ (m' + 1)) := by
      rw [pow_succ]; field_simp
    have hvolG : volume (G ∩ Ico (a + k * ((b - a) / 2 ^ (m' + 1)))
        (a + (k + 1) * ((b - a) / 2 ^ (m' + 1)))) ≤
        ENNReal.ofReal s * ENNReal.ofReal (α * ((b - a) / 2 ^ (m' + 1))) := by
      refine (measure_mono (inter_subset_inter_right G hDsub)).trans (hpar.trans ?_)
      rw [← ENNReal.ofReal_mul hs0.le]
      apply ENNReal.ofReal_le_ofReal
      rw [e2]
      have := mul_le_mul_of_nonneg_right htα (hℓ (m' + 1)).le
      linarith
    have hV := s07d_p7_vol hab G hGm (fun n j => ENNReal.ofReal (s * ((b - a) / 2 ^ n)) <
      volume (G ∩ Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))))
      (ENNReal.ofReal s)⁻¹ hQ (m' + 1) k (fun n hn hq => hanc n hn (hQP n _ hq))
    have hvolS : volume (Ωs ∩ Ico (a + k * ((b - a) / 2 ^ (m' + 1)))
        (a + (k + 1) * ((b - a) / 2 ^ (m' + 1)))) ≤
        ENNReal.ofReal (α * ((b - a) / 2 ^ (m' + 1))) := by
      refine hV.trans ?_
      refine (mul_le_mul_of_nonneg_left hvolG (by positivity)).trans (le_of_eq ?_)
      exact ENNReal.inv_mul_cancel_left hs' ENNReal.ofReal_ne_top
    have hk1 : (k : ℝ) + 1 ≤ 2 ^ (m' + 1) := by exact_mod_cast Nat.succ_le_of_lt hk
    have hac : a ≤ a + k * ((b - a) / 2 ^ (m' + 1)) :=
      le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg k) (hℓ _).le)
    have hcd : a + k * ((b - a) / 2 ^ (m' + 1)) < a + (k + 1) * ((b - a) / 2 ^ (m' + 1)) := by
      linarith [hℓ (m' + 1)]
    have hdb : a + (k + 1) * ((b - a) / 2 ^ (m' + 1)) ≤ b := by
      have h3 := mul_le_mul_of_nonneg_right hk1 (hℓ (m' + 1)).le
      have e3 : (2 : ℝ) ^ (m' + 1) * ((b - a) / 2 ^ (m' + 1)) = b - a := by field_simp
      linarith
    have hdc : a + ((k : ℝ) + 1) * ((b - a) / 2 ^ (m' + 1)) - (a + k * ((b - a) / 2 ^ (m' + 1))) =
        (b - a) / 2 ^ (m' + 1) := by ring
    have hS := hw _ _ hac hcd hdb _ (inter_subset_right.trans Ico_subset_Icc_self)
      (hmeasQ.inter measurableSet_Ico) (by rw [hdc]; exact hvolS)
    have hatom := s07d_p7_atom hβ ν hν hw (hac.trans_lt hcd) hdb
    refine hS.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [← Ico_union_right hcd.le]
    exact (measure_union_le _ _).trans (by rw [hatom, add_zero])
  rwa [inter_eq_left.2 hsub, univ_inter] at key

/-- P7 helper: a union of dyadic subintervals of `[a, b)` lies in `[a, b)`. -/
theorem s07d_p7_union_sub {a b : ℝ} (hab : a < b) (P : ℕ → ℕ → Prop) :
    (⋃ (n : ℕ) (j : ℕ) (_ : j < 2 ^ n ∧ P n j),
      Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))) ⊆ Ico a b := by
  intro x hx
  simp only [mem_iUnion, exists_prop] at hx
  obtain ⟨n, j, ⟨hj, -⟩, hx⟩ := hx
  have hℓ : 0 < (b - a) / 2 ^ n := div_pos (sub_pos.2 hab) (pow_pos two_pos n)
  have hj1 : (j : ℝ) + 1 ≤ 2 ^ n := by exact_mod_cast Nat.succ_le_of_lt hj
  have e3 : (2 : ℝ) ^ n * ((b - a) / 2 ^ n) = b - a := by field_simp
  have h3 := mul_le_mul_of_nonneg_right hj1 hℓ.le
  exact ⟨((s07d_p7_mem_iff hab n j x).1 hx).1, by linarith [hx.2]⟩

/-- **P7m** (w6; requested: `s07d_p7_real` in measure form). A single weak-`A∞` pair `(α, β)` for
a measure `ν`, finite on `[a, b]`, on all subintervals of `[a, b]` gives the full modulus on
`[a, b]`, with `δf` depending only on `(α, β)`. P6 applies it to the arclength pullback of
`s07d_p4_lavrentiev_nu`. -/
theorem s07d_p7_meas (α β : ℝ) (hα : 0 < α) (hβ : β < 1) :
    ∃ δf : ℝ → ℝ, ∀ ε : ℝ, 0 < ε → 0 < δf ε ∧
      ∀ ν : Measure ℝ, ∀ a b : ℝ, a < b → ν (Icc a b) ≠ ⊤ →
      (∀ c d : ℝ, a ≤ c → c < d → d ≤ b → ∀ S ⊆ Icc c d, MeasurableSet S →
        volume S ≤ ENNReal.ofReal (α * (d - c)) → ν S ≤ ENNReal.ofReal β * ν (Icc c d)) →
      ∀ S ⊆ Icc a b, MeasurableSet S → volume S ≤ ENNReal.ofReal (δf ε * (b - a)) →
        ν S ≤ ENNReal.ofReal ε * ν (Icc a b) := by
  obtain ⟨α', hα', hα'α, hα'1⟩ : ∃ α' : ℝ, 0 < α' ∧ α' ≤ α ∧ α' ≤ 1 :=
    ⟨min α 1, lt_min hα one_pos, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨r, hrpos, hr1, hαr⟩ : ∃ r : ℝ, 0 < r ∧ 1 < r ∧ α' * r = 2 := by
    refine ⟨2 / α', div_pos two_pos hα', ?_, by field_simp⟩
    rw [lt_div_iff₀ hα']
    linarith
  have hq1 : max β 0 < 1 := max_lt hβ one_pos
  have hKex : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, max β 0 ^ K < ε := fun ε hε =>
    exists_pow_lt_of_lt_one hε hq1
  choose! K hK using hKex
  refine ⟨fun ε => 1 / (4 * r ^ K ε), fun ε hε =>
    ⟨div_pos one_pos (mul_pos (by norm_num) (pow_pos hrpos _)), ?_⟩⟩
  intro ν a b hab hν hw S hSab hSm hSvol
  have hKε := hK ε hε
  obtain ⟨N, hN⟩ : ∃ N, N = K ε := ⟨_, rfl⟩
  beta_reduce at hSvol
  rw [← hN] at hSvol hKε
  have hℓ : ∀ n : ℕ, 0 < (b - a) / 2 ^ n := fun n => div_pos (sub_pos.2 hab) (pow_pos two_pos n)
  have hRN : 0 < r ^ N := pow_pos hrpos N
  set τ : ℕ → ℝ := fun i => r ^ i / (2 * r ^ N) with hτ
  have hτpos : ∀ i, 0 < τ i := fun i => div_pos (pow_pos hrpos i) (mul_pos two_pos hRN)
  have hτmono : ∀ i j : ℕ, i ≤ j → τ i ≤ τ j := fun i j hij =>
    div_le_div_of_nonneg_right (pow_le_pow_right₀ hr1.le hij) (mul_pos two_pos hRN).le
  have hτN : τ N = 1 / 2 := by
    simp only [hτ]
    field_simp
  -- an open set `G ⊇ S` of small measure
  have hδlt : volume S < ENNReal.ofReal (τ 0 * (b - a)) := by
    refine hSvol.trans_lt ((ENNReal.ofReal_lt_ofReal_iff
      (mul_pos (hτpos 0) (sub_pos.2 hab))).2 ?_)
    have : 1 / (4 * r ^ N) < τ 0 := by
      simp only [hτ, pow_zero]
      exact one_div_lt_one_div_of_lt (mul_pos two_pos hRN) (by linarith)
    exact mul_lt_mul_of_pos_right this (sub_pos.2 hab)
  obtain ⟨G, hSG, hGo, hGvol⟩ := Set.exists_isOpen_lt_of_lt S _ hδlt
  have hw' : ∀ c d : ℝ, a ≤ c → c < d → d ≤ b → ∀ S ⊆ Icc c d, MeasurableSet S →
      volume S ≤ ENNReal.ofReal (α' * (d - c)) → ν S ≤ ENNReal.ofReal β * ν (Icc c d) :=
    fun c d hc hcd hd S' hS' hS'm hv => hw c d hc hcd hd S' hS' hS'm (hv.trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hα'α (sub_nonneg.2 hcd.le))))
  -- iterate the level estimate
  have hiter : ∀ i : ℕ, i ≤ N → ν (⋃ (n : ℕ) (j : ℕ) (_ : j < 2 ^ n ∧
      ENNReal.ofReal (τ i * ((b - a) / 2 ^ n)) <
        volume (G ∩ Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n)))),
      Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))) ≤
      ENNReal.ofReal β ^ i * ν (Icc a b) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [pow_zero, one_mul]
      exact measure_mono ((s07d_p7_union_sub hab _).trans Ico_subset_Icc_self)
    | succ i ih =>
      intro hi
      have hlev := s07d_p7_level (t := τ i) (s := τ (i + 1)) hα' hβ ν hab hν hw' G hGo
        (hτpos i)
        (div_lt_div_of_pos_right (pow_lt_pow_right₀ hr1 (Nat.lt_succ_self i))
          (mul_pos two_pos hRN))
        (lt_of_le_of_lt (hτmono _ _ hi) (by rw [hτN]; norm_num))
        (by
          apply le_of_eq
          simp only [hτ, pow_succ]
          rw [show α' * (r ^ i * r / (2 * r ^ N)) = (α' * r) * (r ^ i / (2 * r ^ N)) by ring,
            hαr])
        ((measure_mono inter_subset_left).trans (hGvol.le.trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (hτmono 0 i (Nat.zero_le i)) (sub_pos.2 hab).le))))
      refine hlev.trans ?_
      rw [pow_succ, mul_comm (ENNReal.ofReal β ^ i), mul_assoc]
      exact mul_le_mul_of_nonneg_left (ih (Nat.le_of_succ_le hi)) (by positivity)
  -- `S ⊆ Ω_{1/2} ∪ {b}`
  have hcov : S ⊆ (⋃ (n : ℕ) (j : ℕ) (_ : j < 2 ^ n ∧
      ENNReal.ofReal (τ N * ((b - a) / 2 ^ n)) <
        volume (G ∩ Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n)))),
      Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))) ∪ {b} := by
    intro x hx
    have hxab := hSab hx
    by_cases hxb : x = b
    · exact Or.inr hxb
    left
    have hxlt : x < b := lt_of_le_of_ne hxab.2 hxb
    obtain ⟨ε', hε', hball⟩ := Metric.isOpen_iff.1 hGo x (hSG hx)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (b - a) / 2 ^ n < ε' := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε' (sub_pos.2 hab))
        (by norm_num : (1 / 2 : ℝ) < 1)
      refine ⟨n, ?_⟩
      rw [lt_div_iff₀ (sub_pos.2 hab)] at hn
      rw [show (b - a) / 2 ^ n = (1 / 2) ^ n * (b - a) by rw [one_div_pow]; ring]
      exact hn
    have hxD : x ∈ Ico (a + (⌊(x - a) / ((b - a) / 2 ^ n)⌋₊ : ℕ) * ((b - a) / 2 ^ n))
        (a + ((⌊(x - a) / ((b - a) / 2 ^ n)⌋₊ : ℕ) + 1) * ((b - a) / 2 ^ n)) :=
      (s07d_p7_mem_iff hab n _ x).2 ⟨hxab.1, rfl⟩
    have hj : ⌊(x - a) / ((b - a) / 2 ^ n)⌋₊ < 2 ^ n := by
      rw [Nat.floor_lt (div_nonneg (sub_nonneg.2 hxab.1) (hℓ n).le)]
      push_cast
      rw [div_lt_iff₀ (hℓ n)]
      have e3 : (2 : ℝ) ^ n * ((b - a) / 2 ^ n) = b - a := by field_simp
      linarith
    have hDG : Ico (a + (⌊(x - a) / ((b - a) / 2 ^ n)⌋₊ : ℕ) * ((b - a) / 2 ^ n))
        (a + ((⌊(x - a) / ((b - a) / 2 ^ n)⌋₊ : ℕ) + 1) * ((b - a) / 2 ^ n)) ⊆ G := by
      intro y hy
      apply hball
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hy.1, hy.2, hxD.1, hxD.2]
    simp only [mem_iUnion, exists_prop]
    refine ⟨n, _, ⟨hj, ?_⟩, hxD⟩
    rw [inter_eq_right.2 hDG, Real.volume_Ico, ENNReal.ofReal_lt_ofReal_iff (by linarith [hℓ n]),
      hτN]
    linarith [hℓ n]
  have hb' : ENNReal.ofReal β = ENNReal.ofReal (max β 0) := by
    rcases le_total β 0 with h | h
    · rw [ENNReal.ofReal_of_nonpos h, max_eq_right h, ENNReal.ofReal_zero]
    · rw [max_eq_left h]
  calc ν S ≤ ν ((⋃ (n : ℕ) (j : ℕ) (_ : j < 2 ^ n ∧
        ENNReal.ofReal (τ N * ((b - a) / 2 ^ n)) <
          volume (G ∩ Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n)))),
        Ico (a + j * ((b - a) / 2 ^ n)) (a + (j + 1) * ((b - a) / 2 ^ n))) ∪ {b}) :=
        measure_mono hcov
    _ ≤ _ := measure_union_le _ _
    _ = _ := by rw [s07d_p7_atom hβ ν hν hw hab le_rfl, add_zero]
    _ ≤ ENNReal.ofReal β ^ N * ν (Icc a b) := hiter N le_rfl
    _ ≤ ENNReal.ofReal ε * ν (Icc a b) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [hb', ← ENNReal.ofReal_pow (le_max_right _ _)]
      exact ENNReal.ofReal_le_ofReal hKε.le

/-- P7 helper: on an interval of length `≤ 2π`, arc length of `h(e^{iT})` is the length of `H(T)`. -/
theorem s07d_p7_hlen {h : ℂ → ℂ} {H : ℝ → ℝ} (hH : StrictMono H) (hHc : Continuous H)
    (hper : ∀ θ, H (θ + 2 * π) = H θ + 2 * π)
    (hl : ∀ θ : ℝ, h (Complex.exp (θ * I)) = Complex.exp (H θ * I))
    {c d : ℝ} (hdc2 : d - c ≤ 2 * π) (T : Set ℝ) (hT : T ⊆ Icc c d) (hTm : MeasurableSet T) :
    circleLen (h '' ((fun θ : ℝ => Complex.exp (θ * I)) '' T)) = volume (H '' T) := by
  have hHd : H d ≤ H c + 2 * π := by
    rw [← hper]
    exact hH.monotone (by linarith)
  have himg : h '' ((fun θ : ℝ => Complex.exp (θ * I)) '' T) =
      (fun θ : ℝ => Complex.exp (θ * I)) '' (H '' T) := by
    rw [image_image, image_image]
    exact image_congr fun θ _ => hl θ
  rw [himg]
  refine s07_circleLen_exp_image (H c) _
    (hTm.image_of_continuousOn_injOn hHc.continuousOn hH.injective.injOn) ?_
  rintro _ ⟨θ, hθ, rfl⟩
  exact ⟨hH.monotone (hT hθ).1, (hH.monotone (hT hθ).2).trans hHd⟩

/-- P7 helper: the complement form of the weak pair, read on the lift `H`, gives the upper form
`|S| ≤ α |I| ⇒ |H(S)| ≤ (1 - β) |H(I)|` on intervals of length `≤ min ℓ₀ 2π`. -/
theorem s07d_p7_compl_weak {α β ℓ₀ : ℝ} (hα : 0 < α) (hβ : 0 < β) {h : ℂ → ℂ} {H : ℝ → ℝ}
    (hH : StrictMono H) (hHc : Continuous H) (hper : ∀ θ, H (θ + 2 * π) = H θ + 2 * π)
    (hl : ∀ θ : ℝ, h (Complex.exp (θ * I)) = Complex.exp (H θ * I))
    (hyp : ∀ a b : ℝ, a < b → b - a ≤ ℓ₀ → ∀ A ⊆ circleArc a b, MeasurableSet A →
      ENNReal.ofReal (1 - α) * circleLen (circleArc a b) ≤ circleLen A →
        ENNReal.ofReal β * circleLen (h '' circleArc a b) ≤ circleLen (h '' A))
    {c d : ℝ} (hcd : c < d) (hdc : d - c ≤ ℓ₀) (hdc2 : d - c ≤ 2 * π) (S : Set ℝ)
    (hS : S ⊆ Icc c d) (hSm : MeasurableSet S) (hv : volume S ≤ ENNReal.ofReal (α * (d - c))) :
    volume (H '' S) ≤ ENNReal.ofReal (1 - β) * volume (H '' Icc c d) := by
  have hIsub : Icc c d ⊆ Icc c (c + 2 * π) := fun θ hθ => ⟨hθ.1, by linarith [hθ.2]⟩
  have hHm : ∀ T : Set ℝ, MeasurableSet T → MeasurableSet (H '' T) := fun T hT =>
    hT.image_of_continuousOn_injOn hHc.continuousOn hH.injective.injOn
  have hTm : MeasurableSet (Icc c d \ S) := measurableSet_Icc.diff hSm
  have hTsub : Icc c d \ S ⊆ Icc c d := diff_subset
  have harc : circleArc c d = (fun θ : ℝ => Complex.exp (θ * I)) '' Icc c d := rfl
  have hvolT : volume S + volume (Icc c d \ S) = ENNReal.ofReal (d - c) := by
    rw [← Real.volume_Icc, ← measure_union disjoint_sdiff_right hTm, union_diff_cancel hS]
  have hlenA : ENNReal.ofReal (1 - α) * circleLen (circleArc c d) ≤
      circleLen ((fun θ : ℝ => Complex.exp (θ * I)) '' (Icc c d \ S)) := by
    rw [harc, s07_circleLen_exp_image c _ measurableSet_Icc hIsub,
      s07_circleLen_exp_image c _ hTm (hTsub.trans hIsub), Real.volume_Icc,
      ← ENNReal.ofReal_mul' (sub_nonneg.2 hcd.le)]
    have hSfin : volume S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hv
    have hT : volume (Icc c d \ S) = ENNReal.ofReal (d - c) - volume S := by
      rw [← hvolT, ENNReal.add_sub_cancel_left hSfin]
    rw [hT]
    calc ENNReal.ofReal ((1 - α) * (d - c)) = ENNReal.ofReal ((d - c) - α * (d - c)) := by
          congr 1; ring
      _ = ENNReal.ofReal (d - c) - ENNReal.ofReal (α * (d - c)) :=
          ENNReal.ofReal_sub _ (mul_nonneg hα.le (sub_nonneg.2 hcd.le))
      _ ≤ _ := tsub_le_tsub_left hv _
  have key := hyp c d hcd hdc _ (by rw [harc]; exact image_mono hTsub)
    (s07_inv_exp_meas c hTm (hTsub.trans hIsub)) hlenA
  rw [harc, s07d_p7_hlen hH hHc hper hl hdc2 _ subset_rfl measurableSet_Icc,
    s07d_p7_hlen hH hHc hper hl hdc2 _ hTsub hTm] at key
  have hHT : H '' (Icc c d \ S) = H '' Icc c d \ H '' S := image_diff hH.injective _ _
  have hsplit : volume (H '' S) + volume (H '' (Icc c d \ S)) = volume (H '' Icc c d) := by
    rw [hHT, ← measure_union disjoint_sdiff_right ((hHm _ measurableSet_Icc).diff (hHm S hSm)),
      union_diff_cancel (image_mono hS)]
  have hfin : volume (H '' Icc c d) ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_Icc_lt_top (a := H c) (b := H d)).ne
      (measure_mono (image_subset_iff.2 fun θ hθ => ⟨hH.monotone hθ.1, hH.monotone hθ.2⟩))
  rw [ENNReal.ofReal_sub 1 hβ.le, ENNReal.ofReal_one, ENNReal.sub_mul (fun _ _ => hfin), one_mul]
  refine ENNReal.le_sub_of_add_le_right (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) ?_
  exact (add_le_add le_rfl key).trans_eq hsplit

/-- P7 helper: `[a, b]` is covered by its `N` equal closed pieces. -/
theorem s07d_p7_cover {a b : ℝ} (hab : a < b) {N : ℕ} (hN : 0 < N) {θ : ℝ} (hθ : θ ∈ Icc a b) :
    ∃ i ∈ Finset.range N, θ ∈ Icc (a + i * ((b - a) / N)) (a + (i + 1) * ((b - a) / N)) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hL : 0 < (b - a) / N := div_pos (sub_pos.2 hab) hNr
  have e : (N : ℝ) * ((b - a) / N) = b - a := by field_simp
  rcases eq_or_lt_of_le hθ.2 with hθb | hθb
  · refine ⟨N - 1, Finset.mem_range.2 (by omega), ?_⟩
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one, hθb]
    constructor <;> linarith
  · refine ⟨⌊(θ - a) / ((b - a) / N)⌋₊, Finset.mem_range.2 ?_, ?_⟩
    · rw [Nat.floor_lt (div_nonneg (sub_nonneg.2 hθ.1) hL.le), div_lt_iff₀ hL]
      linarith
    · have h1 := Nat.floor_le (div_nonneg (sub_nonneg.2 hθ.1) hL.le)
      have h2 := Nat.lt_floor_add_one ((θ - a) / ((b - a) / N))
      rw [le_div_iff₀ hL] at h1
      rw [div_lt_iff₀ hL] at h2
      constructor <;> linarith

/-- **P7c** (w6; requested: `s07d_p7_sqs_compl` with a scale cutoff `ℓ₀`). The lower-bound weak pair
`|A| ≥ (1 - α) |I| ⇒ |h(A)| ≥ β |h(I)|` on arcs of length `≤ ℓ₀` gives strong quasisymmetry, with
`δf` depending only on `(α, β, ℓ₀)`. Longer arcs are split into `≤ ⌈4π/ℓ₀⌉` pieces; no doubling is
needed. -/
theorem s07d_p7_sqs_compl (α β ℓ₀ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hℓ₀ : 0 < ℓ₀) :
    ∃ δf : ℝ → ℝ, ∀ h : ℂ → ℂ, IsCircleHomeo h →
      (∀ a b : ℝ, a < b → b - a ≤ ℓ₀ → ∀ A ⊆ circleArc a b, MeasurableSet A →
        ENNReal.ofReal (1 - α) * circleLen (circleArc a b) ≤ circleLen A →
          ENNReal.ofReal β * circleLen (h '' circleArc a b) ≤ circleLen (h '' A)) →
      IsStronglyQSWith h δf := by
  obtain ⟨ℓ₁, hℓ₁, hℓ₁0, hℓ₁2⟩ : ∃ ℓ₁ : ℝ, 0 < ℓ₁ ∧ ℓ₁ ≤ ℓ₀ ∧ ℓ₁ ≤ 2 * π :=
    ⟨min ℓ₀ (2 * π), lt_min hℓ₀ (by positivity), min_le_left _ _, min_le_right _ _⟩
  obtain ⟨δ', hδ'⟩ := s07d_p7_meas α (1 - β) hα (by linarith)
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈2 * π / ℓ₁⌉₊ := ⟨_, rfl⟩
  have hN : 0 < N := by rw [hNdef]; exact Nat.ceil_pos.2 (div_pos (by positivity) hℓ₁)
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hNℓ : 2 * π ≤ N * ℓ₁ := by
    have := Nat.le_ceil (2 * π / ℓ₁)
    rw [← hNdef, div_le_iff₀ hℓ₁] at this
    exact this
  refine ⟨fun ε => δ' (ε / N) / N, fun h hh hyp => ⟨hh, fun ε hε => ?_⟩⟩
  obtain ⟨hδpos, hδ⟩ := hδ' (ε / N) (div_pos hε hNr)
  refine ⟨div_pos hδpos hNr, ?_⟩
  intro a b hab hab2 E hE hEm hElen
  obtain ⟨H, hH, hHc, hper, hl⟩ := hh
  have hHm : ∀ T : Set ℝ, MeasurableSet T → MeasurableSet (H '' T) := fun T hT =>
    hT.image_of_continuousOn_injOn hHc.continuousOn hH.injective.injOn
  have hνT : ∀ T : Set ℝ, MeasurableSet T → Measure.comap H volume T = volume (H '' T) :=
    fun T hT => Measure.comap_apply H hH.injective hHm volume hT
  have hIsub : Icc a b ⊆ Icc a (a + 2 * π) := fun θ hθ => ⟨hθ.1, by linarith [hθ.2]⟩
  have hSm : MeasurableSet (Icc a b ∩ (fun θ : ℝ => Complex.exp (θ * I)) ⁻¹' E) :=
    measurableSet_Icc.inter (hEm.preimage (by fun_prop))
  have hES : E = (fun θ : ℝ => Complex.exp (θ * I)) ''
      (Icc a b ∩ (fun θ : ℝ => Complex.exp (θ * I)) ⁻¹' E) := by
    ext z
    constructor
    · intro hz
      obtain ⟨θ, hθ, rfl⟩ := hE hz
      exact ⟨θ, ⟨hθ, hz⟩, rfl⟩
    · rintro ⟨θ, ⟨-, hθ⟩, rfl⟩
      exact hθ
  have harc : circleArc a b = (fun θ : ℝ => Complex.exp (θ * I)) '' Icc a b := rfl
  have hSvol : volume (Icc a b ∩ (fun θ : ℝ => Complex.exp (θ * I)) ⁻¹' E) ≤
      ENNReal.ofReal (δ' (ε / N) / N * (b - a)) := by
    beta_reduce at hElen
    rw [hES, harc, s07_circleLen_exp_image a _ hSm (inter_subset_left.trans hIsub),
      s07_circleLen_exp_image a _ measurableSet_Icc hIsub, Real.volume_Icc,
      ← ENNReal.ofReal_mul (div_pos hδpos hNr).le] at hElen
    exact hElen
  rw [hES, harc, s07d_p7_hlen hH hHc hper hl hab2 _ inter_subset_left hSm,
    s07d_p7_hlen hH hHc hper hl hab2 _ subset_rfl measurableSet_Icc, ← hνT _ hSm,
    ← hνT _ measurableSet_Icc]
  set S := Icc a b ∩ (fun θ : ℝ => Complex.exp (θ * I)) ⁻¹' E with hSdef
  have hwk : ∀ c d : ℝ, c < d → d - c ≤ ℓ₁ → ∀ T ⊆ Icc c d, MeasurableSet T →
      volume T ≤ ENNReal.ofReal (α * (d - c)) →
        Measure.comap H volume T ≤ ENNReal.ofReal (1 - β) * Measure.comap H volume (Icc c d) := by
    intro c d hcd hdc T hT hTm hv
    rw [hνT T hTm, hνT _ measurableSet_Icc]
    exact s07d_p7_compl_weak hα hβ hH hHc hper hl hyp hcd (hdc.trans hℓ₁0) (hdc.trans hℓ₁2)
      T hT hTm hv
  have hL : 0 < (b - a) / N := div_pos (sub_pos.2 hab) hNr
  have hLℓ : (b - a) / N ≤ ℓ₁ := by
    rw [div_le_iff₀ hNr]
    linarith
  have eNL : (N : ℝ) * ((b - a) / N) = b - a := by field_simp
  have hνfin : ∀ c d : ℝ, Measure.comap H volume (Icc c d) ≠ ⊤ := fun c d => by
    rw [hνT _ measurableSet_Icc]
    exact ne_top_of_le_ne_top (measure_Icc_lt_top (a := H c) (b := H d)).ne
      (measure_mono (image_subset_iff.2 fun θ hθ => ⟨hH.monotone hθ.1, hH.monotone hθ.2⟩))
  have hpiece : ∀ i ∈ Finset.range N, Measure.comap H volume
      (S ∩ Icc (a + i * ((b - a) / N)) (a + (i + 1) * ((b - a) / N))) ≤
        ENNReal.ofReal (ε / N) * Measure.comap H volume (Icc a b) := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.1 hi)
    have hp1 : a + i * ((b - a) / N) < a + (i + 1) * ((b - a) / N) := by linarith
    have hpa : a ≤ a + i * ((b - a) / N) :=
      le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hL.le)
    have hpb : a + (i + 1) * ((b - a) / N) ≤ b := by
      have := mul_le_mul_of_nonneg_right hi' hL.le
      linarith
    have hm := hδ (Measure.comap H volume) _ _ hp1 (hνfin _ _)
      (fun c d hc hcd hd T hT hTm hv => hwk c d hcd (by linarith) T hT hTm hv)
      (S ∩ Icc (a + i * ((b - a) / N)) (a + (i + 1) * ((b - a) / N))) inter_subset_right
      (hSm.inter measurableSet_Icc)
      ((measure_mono inter_subset_left).trans (hSvol.trans (le_of_eq (by congr 1; ring))))
    exact hm.trans (mul_le_mul_of_nonneg_left (measure_mono (Icc_subset_Icc hpa hpb))
      (by positivity))
  have hcovS : S ⊆ ⋃ i ∈ Finset.range N,
      S ∩ Icc (a + i * ((b - a) / N)) (a + (i + 1) * ((b - a) / N)) := by
    intro θ hθ
    obtain ⟨i, hi, hθi⟩ := s07d_p7_cover hab hN hθ.1
    exact mem_iUnion₂.2 ⟨i, hi, hθ, hθi⟩
  calc Measure.comap H volume S ≤ Measure.comap H volume (⋃ i ∈ Finset.range N,
        S ∩ Icc (a + i * ((b - a) / N)) (a + (i + 1) * ((b - a) / N))) := measure_mono hcovS
    _ ≤ ∑ i ∈ Finset.range N, Measure.comap H volume
        (S ∩ Icc (a + i * ((b - a) / N)) (a + (i + 1) * ((b - a) / N))) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ Finset.range N, ENNReal.ofReal (ε / N) * Measure.comap H volume (Icc a b) :=
        Finset.sum_le_sum hpiece
    _ = ENNReal.ofReal ε * Measure.comap H volume (Icc a b) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
        show (N : ℝ) * (ε / N) = ε by field_simp]


/-- P6c helper: every point of `∂𝔻` is `e^{it}` for some `t ∈ [0, 2π)`. -/
theorem s07d_p6c_sph_ico {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) :
    ∃ t ∈ Ico 0 (2 * π), Complex.exp (t * I) = z := by
  have hpi := Real.pi_pos
  have h1 := Complex.neg_pi_lt_arg z
  have h2 := Complex.arg_le_pi z
  have he := s07d_p5_exp_arg z hz
  by_cases h0 : 0 ≤ Complex.arg z
  · exact ⟨Complex.arg z, ⟨h0, by linarith⟩, he⟩
  · push Not at h0
    refine ⟨Complex.arg z + 2 * π, ⟨by linarith, by linarith⟩, ?_⟩
    exact (s07c_fkps_m2_exp_periodic (Complex.arg z)).trans he

/-- P6c helper: the harmonic measure at `0` of `Ψ⁻¹(X)`, as a Poisson integral, is
`|{t ∈ [0, 2π) : Ψ(e^{it}) ∈ X}| / 2π`. -/
theorem s07d_p6c_harm_int (Ψ : ℂ → ℂ) (X : Set ℂ)
    (hS : MeasurableSet ({t : ℝ | Complex.exp (t * I) ∈ Ψ ⁻¹' X})) :
    ∫ t in (0 : ℝ)..2 * π, (1 - ‖(0 : ℂ)‖ ^ 2) / ‖Complex.exp (t * I) - 0‖ ^ 2 *
        (Ψ ⁻¹' X).indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) =
      (volume ({t : ℝ | Complex.exp (t * I) ∈ Ψ ⁻¹' X} ∩ Ico 0 (2 * π))).toReal := by
  have hpi := Real.pi_pos
  have e : ∀ t : ℝ, (1 - ‖(0 : ℂ)‖ ^ 2) / ‖Complex.exp (t * I) - 0‖ ^ 2 *
      (Ψ ⁻¹' X).indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) =
      ({t : ℝ | Complex.exp (t * I) ∈ Ψ ⁻¹' X}).indicator (fun _ => (1 : ℝ)) t := by
    intro t
    rw [norm_zero, sub_zero, Complex.norm_exp_ofReal_mul_I]
    norm_num
    rfl
  simp_rw [e]
  rw [intervalIntegral.integral_of_le (by positivity), ← integral_Ico_eq_integral_Ioc,
    setIntegral_indicator hS, setIntegral_const, smul_eq_mul, mul_one, Measure.real, inter_comm]

/-- **P6c (harmonic measure of large subsets).** For a quasidisk `V = G(𝔻)` (`G` a global `K`-q.c.
map) with `M`-upper-Ahlfors-regular boundary and Riemann map `ψ` with `ψ 0 = G 0`, there is a
homeomorphic extension `Ψ` of `ψ` to `ℂ` such that every measurable `X ⊆ ∂V` with
`μH¹(X) ≥ θ μH¹(∂V)` and `μH¹(X) ≠ 0` has harmonic measure `≥ δ` at `ψ 0`, written as the Poisson
integral at `0` (the `z = 0` instance of the left side of `s07d_p5_transfer_ext`). `δ` depends only on
`(K, M, θ)`.
Suggested route: `s07d_p4_lavrentiev_nu` gives `F = Ψ` and `ν` (arclength pulled back to `[0, 2π)`);
`s07d_p7_meas` with `(α, β) = (δ₀, 1 - η₀)` and `ε = θ/2` on `[0, 2π]` gives `δf`; if
`|Ψ⁻¹(X)| ≤ δf(θ/2) · 2π` then `μH¹(X) = ν(…) ≤ (θ/2) μH¹(∂V) < θ μH¹(∂V)`, a contradiction
(`μH¹(∂V)` is finite by Ahlfors regularity and nonzero because `μH¹(X) ≠ 0`); so `δ = δf(θ/2)`. -/
theorem s07d_p6_harm (K M θ : ℝ) (hK : 1 ≤ K) (hM : 0 < M) (hθ : 0 < θ) : ∃ δ : ℝ, 0 < δ ∧
    ∀ (V : Set ℂ) (ψ G : ℂ → ℂ), IsConformalOnto ψ unitDisc V → IsKQC G univ K →
      G '' univ = univ → G '' unitDisc = V → ψ 0 = G 0 →
      (∀ z : ℂ, ∀ r : ℝ, 0 < r → μH[1] (G '' sphere 0 1 ∩ ball z r) ≤ ENNReal.ofReal (M * r)) →
      ∃ Ψ : ℂ → ℂ, IsHomeomorphOnto Ψ univ univ ∧ EqOn Ψ ψ unitDisc ∧
        Ψ '' sphere (0 : ℂ) 1 = G '' sphere (0 : ℂ) 1 ∧
        ∀ X : Set ℂ, MeasurableSet X → X ⊆ G '' sphere (0 : ℂ) 1 → μH[1] X ≠ 0 →
          ENNReal.ofReal θ * μH[1] (G '' sphere (0 : ℂ) 1) ≤ μH[1] X →
          δ ≤ (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖(0 : ℂ)‖ ^ 2) / ‖Complex.exp (t * I) - 0‖ ^ 2 *
            (Ψ ⁻¹' X).indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) := by
  obtain ⟨δ₀, η₀, hδ₀, hη₀, hη₀1, hLav⟩ := s07d_p4_lavrentiev_nu K M hK hM
  obtain ⟨δf, hδf⟩ := s07d_p7_meas δ₀ (1 - η₀) hδ₀ (by linarith)
  obtain ⟨hδpos, hδν⟩ := hδf (θ / 2) (by positivity)
  refine ⟨δf (θ / 2), hδpos, fun V ψ G hψ hG hGs hGV hψ0 hAR => ?_⟩
  have hpi := Real.pi_pos
  obtain ⟨F, ν, hF, hFs, hFψ, hνE, hνfin, hνd⟩ := hLav V ψ G hψ hG hGs hGV hψ0 hAR
  obtain ⟨F', hF', -, hF'ψ, hF'S⟩ := s07d_p4_ext hψ hG hGs hGV hψ0
  have hFh : IsHomeomorphOnto F univ univ := by
    have h := hF.2.2.1
    rwa [hFs] at h
  have hFc : Continuous F := continuousOn_univ.mp hF.2.2.1.1
  have hF'c : Continuous F' := continuousOn_univ.mp hF'.2.2.1.1
  have hEq : EqOn F F' (closedBall 0 1) := by
    refine EqOn.of_subset_closure (s := ball (0 : ℂ) 1)
      (fun z hz => (hFψ hz).trans (hF'ψ hz).symm) hFc.continuousOn hF'c.continuousOn
      ball_subset_closedBall ?_
    rw [closure_ball (0 : ℂ) one_ne_zero]
  have hFS : F '' sphere 0 1 = G '' sphere 0 1 := by
    rw [← hF'S]
    exact (hEq.mono sphere_subset_closedBall).image_eq
  refine ⟨F, hFh, hFψ, hFS, ?_⟩
  intro X hX hXs hX0 hθX
  have hTm : MeasurableSet ({t : ℝ | Complex.exp (t * I) ∈ F ⁻¹' X}) :=
    (hFc.comp (by fun_prop : Continuous fun t : ℝ => Complex.exp (t * I))).measurable hX
  set S : Set ℝ := {t : ℝ | Complex.exp (t * I) ∈ F ⁻¹' X} ∩ Ico 0 (2 * π) with hSdef
  have hSm : MeasurableSet S := hTm.inter measurableSet_Ico
  have hSIco : S ⊆ Ico 0 (0 + 2 * π) := by
    rw [zero_add]
    exact inter_subset_right
  have hSIcc : S ⊆ Icc 0 (2 * π) := fun t ht => Ico_subset_Icc_self ht.2
  rw [s07d_p6c_harm_int F X hTm]
  by_contra hlt
  push Not at hlt
  have hSfin : volume S ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
      (measure_mono inter_subset_right)
  have hvol : volume S ≤ ENNReal.ofReal (δf (θ / 2) * (2 * π - 0)) := by
    rw [ENNReal.le_ofReal_iff_toReal_le hSfin (mul_nonneg hδpos.le (by linarith))]
    rw [inv_mul_lt_iff₀ (by positivity)] at hlt
    linarith
  have hνS := hδν ν 0 (2 * π) (by positivity) (hνfin 0 (2 * π))
    (fun c d _ hcd hd S' hS' hS'm hv => hνd c d hcd (by linarith) S' hS' hS'm hv) S hSIcc hSm hvol
  -- `μH¹(X) ≤ ν S`
  have hXS : μH[1] X ≤ ν S := by
    rw [hνE 0 S hSIco hSm]
    refine measure_mono fun x hx => ?_
    have hx' : x ∈ F '' sphere 0 1 := hFS ▸ hXs hx
    obtain ⟨z, hz, rfl⟩ := hx'
    obtain ⟨t, ht, rfl⟩ := s07d_p6c_sph_ico hz
    exact ⟨Complex.exp (t * I), ⟨t, ⟨hx, ht⟩, rfl⟩, rfl⟩
  -- `ν [0, 2π] ≤ μH¹(∂V)`
  have hνI : ν (Icc 0 (2 * π)) ≤ μH[1] (G '' sphere (0 : ℂ) 1) := by
    have hpt : ν {2 * π} = 0 := by
      have hsub : ({2 * π} : Set ℝ) ⊆ Ico π (π + 2 * π) := by
        intro t ht
        rw [mem_singleton_iff] at ht
        rw [ht]
        constructor <;> linarith
      rw [hνE π {2 * π} hsub (measurableSet_singleton _), image_singleton, image_singleton]
      have := Measure.nullSingletonClass_hausdorff (X := ℂ) (d := 1) one_pos
      exact measure_singleton _
    have hIco : ν (Ico 0 (0 + 2 * π)) ≤ μH[1] (G '' sphere (0 : ℂ) 1) := by
      rw [hνE 0 (Ico 0 (0 + 2 * π)) subset_rfl measurableSet_Ico, ← hFS]
      exact measure_mono (image_mono fun z hz => by
        obtain ⟨t, -, rfl⟩ := hz
        exact s07d_p4_g_sph t)
    rw [zero_add] at hIco
    calc ν (Icc 0 (2 * π)) = ν (Ico 0 (2 * π) ∪ {2 * π}) := by
          rw [Ico_union_right (by positivity)]
      _ ≤ ν (Ico 0 (2 * π)) + ν {2 * π} := measure_union_le _ _
      _ ≤ _ := by rw [hpt, add_zero]; exact hIco
  -- contradiction: `θ m ≤ μH¹(X) ≤ (θ/2) m` with `0 < m < ∞`
  set m := μH[1] (G '' sphere (0 : ℂ) 1) with hmdef
  have hup : μH[1] X ≤ ENNReal.ofReal (θ / 2) * m :=
    hXS.trans (hνS.trans (by gcongr))
  have hθ0 : ENNReal.ofReal θ ≠ 0 := (ENNReal.ofReal_pos.mpr hθ).ne'
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, mul_zero] at hup
    exact hX0 (le_antisymm hup (by simp))
  have hmt : m ≠ ⊤ := by
    intro h
    have h1 : μH[1] X ≤ ENNReal.ofReal (θ / 2) * ν (Icc 0 (2 * π)) := hXS.trans hνS
    have h2 : ENNReal.ofReal (θ / 2) * ν (Icc 0 (2 * π)) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hνfin 0 (2 * π))
    rw [h, ENNReal.mul_top hθ0] at hθX
    exact h2 (top_le_iff.mp (hθX.trans h1))
  have hle : ENNReal.ofReal θ * m ≤ ENNReal.ofReal (θ / 2) * m := hθX.trans hup
  rw [ENNReal.mul_le_mul_iff_left hm0 hmt, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  linarith

/-! ## P6a (w3): scale lemma -/

/-- P6a helper: `|e^{iθ} - e^{iψ}| = |e^{i(θ-ψ)} - 1|`. -/
theorem s07d_p6_rot (θ ψ : ℝ) :
    ‖Complex.exp (θ * I) - Complex.exp (ψ * I)‖ = ‖Complex.exp (I * ((θ - ψ : ℝ) : ℂ)) - 1‖ := by
  have h : Complex.exp (θ * I) - Complex.exp (ψ * I) =
      Complex.exp (ψ * I) * (Complex.exp (I * ((θ - ψ : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- P6a helper (chord ≤ arc): `|e^{iθ} - e^{iψ}| ≤ |θ - ψ|`. -/
theorem s07d_p6_chord (θ ψ : ℝ) :
    ‖Complex.exp (θ * I) - Complex.exp (ψ * I)‖ ≤ |θ - ψ| := by
  rw [s07d_p6_rot, ← Real.norm_eq_abs]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- P6a helper: a subset of `∂𝔻 ∩ B̄(w, R)` (`|w| = 1`, `R ≥ 0`) has `circleLen ≤ 2π R`. -/
theorem s07d_p6_len {w : ℂ} (hw : ‖w‖ = 1) {R : ℝ} (hR : 0 ≤ R) {E : Set ℂ}
    (hE : E ⊆ closedBall w R) : circleLen E ≤ ENNReal.ofReal (2 * π * R) := by
  have hwφ : Complex.exp ((arg w : ℝ) * I) = w := by
    have h := Complex.norm_mul_exp_arg_mul_I w
    rw [hw, Complex.ofReal_one, one_mul] at h
    exact h
  have hkey : ∀ ψ : ℝ, Complex.exp (ψ * I) = w → ∀ θ : ℝ,
      Complex.exp (θ * I) ∈ E → |θ - ψ| ≤ π → |θ - ψ| ≤ π / 2 * R := by
    intro ψ hψ θ hθE hθψ
    have hd : ‖Complex.exp (θ * I) - w‖ ≤ R := by
      have := hE hθE
      rwa [mem_closedBall, dist_eq_norm] at this
    have hc := s07d_p2_ah_chord (θ - ψ) hθψ
    rw [← s07d_p6_rot, hψ] at hc
    nlinarith [mul_le_mul_of_nonneg_left hd Real.pi_pos.le]
  have h2π : Complex.exp (((arg w + 2 * π : ℝ) : ℂ) * I) = w := by
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    exact hwφ
  have hsub : {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ Complex.exp (θ * Complex.I) ∈ E} ⊆
      Icc (arg w - π / 2 * R) (arg w + π / 2 * R) ∪
        Icc (arg w + 2 * π - π / 2 * R) (arg w + 2 * π + π / 2 * R) := by
    rintro θ ⟨hθ, hθE⟩
    have ha1 := Complex.neg_pi_lt_arg w
    have ha2 := Complex.arg_le_pi w
    rcases le_or_gt (θ - arg w) π with h | h
    · left
      have h1 : |θ - arg w| ≤ π := abs_le.2 ⟨by linarith [hθ.1], h⟩
      have h2 := hkey (arg w) hwφ θ hθE h1
      rw [abs_le] at h2
      exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
    · right
      have h1 : |θ - (arg w + 2 * π)| ≤ π := abs_le.2 ⟨by linarith, by linarith [hθ.2]⟩
      have h2 := hkey (arg w + 2 * π) h2π θ hθE h1
      rw [abs_le] at h2
      exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
  show volume {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ Complex.exp (θ * Complex.I) ∈ E} ≤ _
  calc volume {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ Complex.exp (θ * Complex.I) ∈ E}
      ≤ volume (Icc (arg w - π / 2 * R) (arg w + π / 2 * R) ∪
          Icc (arg w + 2 * π - π / 2 * R) (arg w + 2 * π + π / 2 * R)) := measure_mono hsub
    _ ≤ volume (Icc (arg w - π / 2 * R) (arg w + π / 2 * R)) +
          volume (Icc (arg w + 2 * π - π / 2 * R) (arg w + 2 * π + π / 2 * R)) :=
        measure_union_le _ _
    _ = ENNReal.ofReal (π * R) + ENNReal.ofReal (π * R) := by
        rw [Real.volume_Icc, Real.volume_Icc]
        congr 2 <;> ring
    _ = ENNReal.ofReal (2 * π * R) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- P6a helper (hyperbolic comparison): if `cosh d_𝔻(p, q) ≤ B` then
`1 - |q| ≤ 2 B (1 - |p|)`. -/
theorem s07d_p6_hyp {p q : ℂ} {B : ℝ} (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) (hB1 : 1 ≤ B)
    (hB : diskCoshDist p q ≤ B) : 1 - ‖q‖ ≤ 2 * B * (1 - ‖p‖) := by
  have hA1 : 0 < 1 - ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
  have hA2 : 0 < 1 - ‖q‖ ^ 2 := by nlinarith [norm_nonneg q]
  have hx : 0 < 1 - ‖q‖ := by linarith
  have hy : 0 < 1 - ‖p‖ := by linarith
  rcases le_or_gt (1 - ‖q‖) (1 - ‖p‖) with h | h
  · nlinarith
  · have hpq : (1 - ‖q‖) - (1 - ‖p‖) ≤ ‖p - q‖ := by
      have := norm_sub_norm_le p q
      linarith
    have hsq : ((1 - ‖q‖) - (1 - ‖p‖)) ^ 2 ≤ ‖p - q‖ ^ 2 :=
      pow_le_pow_left₀ (by linarith) hpq 2
    have hd : 2 * ‖p - q‖ ^ 2 ≤ (B - 1) * ((1 - ‖p‖ ^ 2) * (1 - ‖q‖ ^ 2)) := by
      unfold diskCoshDist at hB
      have h1 : 2 * ‖p - q‖ ^ 2 / ((1 - ‖p‖ ^ 2) * (1 - ‖q‖ ^ 2)) ≤ B - 1 := by linarith
      rwa [div_le_iff₀ (mul_pos hA1 hA2)] at h1
    have hA1' : 1 - ‖p‖ ^ 2 ≤ 2 * (1 - ‖p‖) := by nlinarith [norm_nonneg p]
    have hA2' : 1 - ‖q‖ ^ 2 ≤ 2 * (1 - ‖q‖) := by nlinarith [norm_nonneg q]
    have hprod : (1 - ‖p‖ ^ 2) * (1 - ‖q‖ ^ 2) ≤ (2 * (1 - ‖p‖)) * (2 * (1 - ‖q‖)) :=
      mul_le_mul hA1' hA2' hA2.le (by linarith)
    have hB' : (B - 1) * ((1 - ‖p‖ ^ 2) * (1 - ‖q‖ ^ 2)) ≤
        (B - 1) * ((2 * (1 - ‖p‖)) * (2 * (1 - ‖q‖))) :=
      mul_le_mul_of_nonneg_left hprod (by linarith)
    nlinarith [mul_pos hx hy]

/-- P6a helper (three-point estimate with ratio `≤ 1`). -/
theorem s07d_p6_tp {C₀ Q : ℝ} (hQ : 1 ≤ Q) (hC₀ : 0 < C₀) {g : ℂ → ℂ} (hinj : InjOn g univ)
    {x y z : ℂ} (hxz : x ≠ z) (hr : ‖x - y‖ ≤ ‖x - z‖)
    (h : ‖g x - g y‖ / ‖g x - g z‖ ≤
      C₀ * max ((‖x - y‖ / ‖x - z‖) ^ (1 / Q)) ((‖x - y‖ / ‖x - z‖) ^ Q)) :
    ‖g x - g y‖ ≤ C₀ * ‖g x - g z‖ := by
  have hxz' : 0 < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hxz)
  have hg : 0 < ‖g x - g z‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 (fun e => hxz (hinj (mem_univ _) (mem_univ _) e)))
  have h0 : 0 ≤ ‖x - y‖ / ‖x - z‖ := by positivity
  have h1 : ‖x - y‖ / ‖x - z‖ ≤ 1 := (div_le_one hxz').2 hr
  have hmax : max ((‖x - y‖ / ‖x - z‖) ^ (1 / Q)) ((‖x - y‖ / ‖x - z‖) ^ Q) ≤ 1 :=
    max_le (Real.rpow_le_one h0 h1 (by positivity)) (Real.rpow_le_one h0 h1 (by linarith))
  rw [div_le_iff₀ hg] at h
  calc ‖g x - g y‖ ≤ C₀ * max ((‖x - y‖ / ‖x - z‖) ^ (1 / Q)) ((‖x - y‖ / ‖x - z‖) ^ Q) *
        ‖g x - g z‖ := h
    _ ≤ C₀ * 1 * ‖g x - g z‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax hC₀.le) hg.le
    _ = C₀ * ‖g x - g z‖ := by rw [mul_one]

/-- **P6a (scale lemma).** Let `F` be a closed-disk homeomorphism with `F 0 = 0` that is
`L`-bi-Lipschitz for `d_𝔻` and `L`-q.c. on `𝔻`, with inverse `Fi` on `𝔻̄`. For an arc
`I = circleArc a b` with `b - a ≤ 1`, top point `c_I = (1 - |I|) e^{i(a+b)/2}`, and `u ∈ 𝔻` with
`d_𝔻(u, c_I) ≤ D`:  `|Fi(I)| ≤ C (1 - |Fi u|)`, where `C` depends only on `(L, D)`.
Suggested route: `Fi` is `L`-q.c. on `𝔻` (`thm7_2_inv`); reflect it to a global q.c. map
(`ab_reflect`, as in `s07d_p3_glue`); then three-point distortion (`lem_three_point`) at
`c_I` and the endpoints of `I`; finally bounded `d_𝔻` gives `1 - |Fi u| ≍ 1 - |Fi c_I|`. -/
theorem s07d_p6_scale (L D : ℝ) (hL : 1 ≤ L) (hD : 0 ≤ D) : ∃ C : ℝ, 0 < C ∧
    ∀ F Fi : ℂ → ℂ, IsClosedDiskHomeo F → F 0 = 0 → IsDiskBiLip F L → IsKQC F unitDisc L →
      (∀ z ∈ closedBall (0 : ℂ) 1, Fi (F z) = z ∧ F (Fi z) = z) →
      ∀ a b : ℝ, a < b → b - a ≤ 1 → ∀ u ∈ unitDisc,
        diskDist u (((1 - (b - a) : ℝ) : ℂ) * Complex.exp (((a + b) / 2 : ℝ) * I)) ≤ D →
          circleLen (Fi '' circleArc a b) ≤ ENNReal.ofReal (C * (1 - ‖Fi u‖)) := by
  obtain ⟨C₀, hC₀, h3⟩ := lem_three_point L hL
  have hB1 : 1 ≤ Real.cosh (L * D) := Real.one_le_cosh _
  refine ⟨4 * π * C₀ ^ 2 * Real.cosh (L * D), by positivity, ?_⟩
  intro F Fi hF hF0 hFL hFq hFi a b hab hba u hu hud
  have hball : unitDisc = ball (0 : ℂ) 1 := rfl
  have hDcl : ∀ z ∈ unitDisc, z ∈ closedBall (0 : ℂ) 1 := fun z hz => ball_subset_closedBall hz
  obtain ⟨hmaps, -⟩ := s07_sb_maps hF hFL
  have hsurj := s07_sb_surj hF hFL
  have hsph := s07_sb_sphere hF hFL
  have hFinj : InjOn F unitDisc := hF.1.injOn.mono (fun z hz => hDcl z hz)
  -- `Fi` maps `𝔻̄`, `𝔻` and `∂𝔻` into themselves
  have hFi_cl : ∀ z ∈ closedBall (0 : ℂ) 1, Fi z ∈ closedBall (0 : ℂ) 1 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hF.1.surjOn hz
    rw [(hFi x hx).1]
    exact hx
  have hFi_D : ∀ w ∈ unitDisc, Fi w ∈ unitDisc := by
    intro w hw
    have h1 := hFi_cl w (hDcl w hw)
    rw [mem_closedBall_zero_iff] at h1
    rcases h1.lt_or_eq with h | h
    · rw [hball, mem_ball_zero_iff]
      exact h
    · exfalso
      have h2 := hsph (mem_sphere_zero_iff_norm.2 h)
      rw [(hFi w (hDcl w hw)).2, mem_sphere_zero_iff_norm] at h2
      have h3' : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
      linarith
  have hFi_S : ∀ ζ ∈ sphere (0 : ℂ) 1, Fi ζ ∈ sphere (0 : ℂ) 1 := by
    intro ζ hζ
    have hζc : ζ ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hζ
    have h1 := hFi_cl ζ hζc
    rw [mem_closedBall_zero_iff] at h1
    rcases h1.lt_or_eq with h | h
    · exfalso
      have h2 := hmaps (show Fi ζ ∈ unitDisc from mem_ball_zero_iff.2 h)
      rw [(hFi ζ hζc).2] at h2
      have h3' : ‖ζ‖ < 1 := mem_ball_zero_iff.1 h2
      rw [mem_sphere_zero_iff_norm] at hζ
      linarith
    · exact mem_sphere_zero_iff_norm.2 h
  -- the inverse `h = F⁻¹` on `𝔻` is `L`-q.c., normalized, and agrees with `Fi`
  have hFD : F '' unitDisc = unitDisc := Subset.antisymm (image_subset_iff.2 hmaps) hsurj
  have hFqi := thm7_2_inv hFq
  rw [hFD] at hFqi
  have hheq : ∀ w ∈ unitDisc, Function.invFunOn F unitDisc w = Fi w := by
    intro w hw
    have hw' : w ∈ F '' unitDisc := by rw [hFD]; exact hw
    refine hFinj (Function.invFunOn_mem hw') (hFi_D w hw) ?_
    rw [Function.invFunOn_eq hw', (hFi w (hDcl w hw)).2]
  have hhs : Function.invFunOn F unitDisc '' unitDisc = unitDisc := by
    apply Subset.antisymm
    · rintro _ ⟨w, hw, rfl⟩
      rw [hheq w hw]
      exact hFi_D w hw
    · intro z hz
      refine ⟨F z, hmaps hz, ?_⟩
      rw [hheq (F z) (hmaps hz), (hFi z (hDcl z hz)).1]
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hh0 : Function.invFunOn F unitDisc 0 = 0 := by
    rw [hheq 0 h0D]
    have h1 := (hFi 0 (hDcl 0 h0D)).1
    rwa [hF0] at h1
  obtain ⟨Hx, hHx⟩ :=
    thm13_3_boundary_correspondence isJordanDomain_unitDisc isJordanDomain_unitDisc ⟨L, hFqi⟩ hhs
  obtain ⟨g, hg, hgs, hgh, -, -, -⟩ := ab_reflect hFqi hhs hh0 hHx
  have hginj : InjOn g univ := hg.2.2.1.2.1
  have hgc : Continuous g := continuousOn_univ.1 hg.2.2.1.1
  -- `g = Fi` on `𝔻̄`
  have hgF : EqOn (g ∘ F) id (closedBall (0 : ℂ) 1) := by
    refine EqOn.of_subset_closure (s := unitDisc) ?_ (hgc.comp_continuousOn hF.2) continuousOn_id
      (fun z hz => hDcl z hz) ?_
    · intro z hz
      show g (F z) = z
      rw [hgh (hmaps hz), hheq (F z) (hmaps hz), (hFi z (hDcl z hz)).1]
    · rw [hball, closure_ball (0 : ℂ) one_ne_zero]
  have hgcl : ∀ z ∈ closedBall (0 : ℂ) 1, g z = Fi z := by
    intro z hz
    have h1 := hgF (hFi_cl z hz)
    simp only [Function.comp_apply, id] at h1
    rwa [(hFi z hz).2] at h1
  -- the arc, its midpoint `ζ₀` and its top point `c`
  obtain ⟨ζ₀, hζ₀def⟩ : ∃ ζ₀ : ℂ, ζ₀ = Complex.exp (((a + b) / 2 : ℝ) * I) := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = ((1 - (b - a) : ℝ) : ℂ) * ζ₀ := ⟨_, rfl⟩
  rw [← hζ₀def, ← hcdef] at hud
  have hℓ : 0 < b - a := by linarith
  have hζ₀1 : ‖ζ₀‖ = 1 := by rw [hζ₀def]; exact Complex.norm_exp_ofReal_mul_I _
  have hζ₀S : ζ₀ ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.2 hζ₀1
  have hc1 : ‖c‖ = 1 - (b - a) := by
    rw [hcdef, norm_mul, hζ₀1, mul_one, Complex.norm_of_nonneg (by linarith)]
  have hcD : c ∈ unitDisc := by
    rw [hball, mem_ball_zero_iff, hc1]
    linarith
  have hζc : ‖ζ₀ - c‖ = b - a := by
    have he : ζ₀ - c = ((b - a : ℝ) : ℂ) * ζ₀ := by rw [hcdef]; push_cast; ring
    rw [he, norm_mul, hζ₀1, mul_one, Complex.norm_of_nonneg hℓ.le]
  have hζcne : ζ₀ ≠ c := by
    intro e
    rw [e, sub_self, norm_zero] at hζc
    linarith
  have hI : ∀ z ∈ circleArc a b, z ∈ sphere (0 : ℂ) 1 ∧ ‖z - ζ₀‖ ≤ (b - a) / 2 := by
    intro z hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    refine ⟨mem_sphere_zero_iff_norm.2 (Complex.norm_exp_ofReal_mul_I θ), ?_⟩
    rw [hζ₀def]
    refine (s07d_p6_chord θ ((a + b) / 2)).trans ?_
    rw [abs_le]
    exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  -- (a) the image of the arc lies within `C₀ |g ζ₀ - g c|` of `g ζ₀`
  have hA : ∀ z ∈ circleArc a b, ‖g z - g ζ₀‖ ≤ C₀ * ‖g ζ₀ - g c‖ := by
    intro z hz
    have hr : ‖ζ₀ - z‖ ≤ ‖ζ₀ - c‖ := by
      rw [norm_sub_rev, hζc]
      linarith [(hI z hz).2]
    have h := s07d_p6_tp hL hC₀ hginj hζcne hr (h3 g hg hgs ζ₀ z c hζcne).1
    rwa [norm_sub_rev] at h
  -- (b) `|g c - g ζ₀| ≤ C₀ (1 - |g c|)`
  have hgcD : g c ∈ unitDisc := by rw [hgcl c (hDcl c hcD)]; exact hFi_D c hcD
  have hgc1 : ‖g c‖ < 1 := mem_ball_zero_iff.1 hgcD
  obtain ⟨η, hηS, hη⟩ : ∃ η ∈ sphere (0 : ℂ) 1, ‖g c - η‖ = 1 - ‖g c‖ := by
    by_cases hw0 : g c = 0
    · refine ⟨1, mem_sphere_zero_iff_norm.2 norm_one, ?_⟩
      rw [hw0, zero_sub, norm_neg, norm_one, norm_zero, sub_zero]
    · have hn : (‖g c‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hw0)
      have hu1 : ‖g c / (‖g c‖ : ℂ)‖ = 1 := by
        rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hw0)]
      refine ⟨g c / (‖g c‖ : ℂ), mem_sphere_zero_iff_norm.2 hu1, ?_⟩
      have he : g c - g c / (‖g c‖ : ℂ) = g c / (‖g c‖ : ℂ) * (((‖g c‖ - 1 : ℝ)) : ℂ) := by
        push_cast
        field_simp
      rw [he, norm_mul, hu1, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (by linarith)]
      ring
  have hη' : F η ∈ sphere (0 : ℂ) 1 ∧ g (F η) = η := by
    refine ⟨hsph hηS, ?_⟩
    rw [hgcl (F η) (sphere_subset_closedBall (hsph hηS)), (hFi η (sphere_subset_closedBall hηS)).1]
  have hB : ‖g c - g ζ₀‖ ≤ C₀ * (1 - ‖g c‖) := by
    have hcη : ‖c - ζ₀‖ ≤ ‖c - F η‖ := by
      rw [norm_sub_rev, hζc]
      have h1 := norm_sub_norm_le (F η) c
      rw [mem_sphere_zero_iff_norm.1 hη'.1, hc1] at h1
      rw [norm_sub_rev]
      linarith
    have hcne : c ≠ F η := by
      intro e
      have h1 := mem_sphere_zero_iff_norm.1 hη'.1
      rw [← e, hc1] at h1
      linarith
    have h := s07d_p6_tp hL hC₀ hginj hcne hcη (h3 g hg hgs c ζ₀ (F η) hcne).1
    rwa [hη'.2, hη] at h
  -- (c) the length bound
  have hR0 : 0 ≤ C₀ * (C₀ * (1 - ‖g c‖)) := by
    have : 0 ≤ 1 - ‖g c‖ := by linarith
    positivity
  have himg : Fi '' circleArc a b = g '' circleArc a b :=
    image_congr (fun z hz => (hgcl z (sphere_subset_closedBall (hI z hz).1)).symm)
  have hsubB : g '' circleArc a b ⊆ closedBall (g ζ₀) (C₀ * (C₀ * (1 - ‖g c‖))) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_closedBall, dist_eq_norm]
    calc ‖g z - g ζ₀‖ ≤ C₀ * ‖g ζ₀ - g c‖ := hA z hz
      _ ≤ C₀ * (C₀ * (1 - ‖g c‖)) := by
          rw [norm_sub_rev]
          exact mul_le_mul_of_nonneg_left hB hC₀.le
  have hgζ : ‖g ζ₀‖ = 1 := by
    rw [hgcl ζ₀ (sphere_subset_closedBall hζ₀S)]
    exact mem_sphere_zero_iff_norm.1 (hFi_S ζ₀ hζ₀S)
  have hlen := s07d_p6_len hgζ hR0 hsubB
  -- (d) `1 - |Fi c| ≤ 2 cosh(L D) (1 - |Fi u|)`
  have hFu : Fi u ∈ unitDisc := hFi_D u hu
  have hFc : Fi c ∈ unitDisc := hFi_D c hcD
  have hdist : diskDist (Fi u) (Fi c) ≤ L * D := by
    have h1 := (hFL (Fi u) hFu (Fi c) hFc).2
    rw [(hFi u (hDcl u hu)).2, (hFi c (hDcl c hcD)).2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hud (by linarith))
  have hcosh : diskCoshDist (Fi u) (Fi c) ≤ Real.cosh (L * D) := by
    rw [← s07_mo_cosh_dist hFu hFc]
    refine Real.cosh_le_cosh.2 ?_
    rw [abs_of_nonneg (s02_diskDist_nonneg hFu hFc), abs_of_nonneg (by positivity)]
    exact hdist
  have hcmp := s07d_p6_hyp (mem_ball_zero_iff.1 hFu) (mem_ball_zero_iff.1 hFc) hB1 hcosh
  rw [← hgcl c (hDcl c hcD)] at hcmp
  rw [himg]
  refine hlen.trans (ENNReal.ofReal_le_ofReal ?_)
  calc 2 * π * (C₀ * (C₀ * (1 - ‖g c‖))) = 2 * π * C₀ ^ 2 * (1 - ‖g c‖) := by ring
    _ ≤ 2 * π * C₀ ^ 2 * (2 * Real.cosh (L * D) * (1 - ‖Fi u‖)) :=
        mul_le_mul_of_nonneg_left hcmp (by positivity)
    _ = 4 * π * C₀ ^ 2 * Real.cosh (L * D) * (1 - ‖Fi u‖) := by ring

/-- P3 helper: `max(t^{1/K}, t^K) ≤ T^K` for `0 ≤ t ≤ T`, `1 ≤ T`, `1 ≤ K`. -/
theorem s07d_p3_eta_le {t T K : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (hT : 1 ≤ T) (hK : 1 ≤ K) :
    max (t ^ (1 / K)) (t ^ K) ≤ T ^ K := by
  have hK0 : 0 < K := by linarith
  have hKi : 1 / K ≤ K := by
    rw [div_le_iff₀ hK0]; nlinarith
  refine max_le ?_ (Real.rpow_le_rpow ht htT hK0.le)
  exact (Real.rpow_le_rpow ht htT (by positivity)).trans (Real.rpow_le_rpow_of_exponent_le hT hKi)

/-- P3 helper: the three-point bound in product form, `|a - b| ≤ T |a - c|` ⇒
`|E a - E b| ≤ C₀ T^K |E a - E c|`. -/
theorem s07d_p3_tp_apply {E : ℂ → ℂ} {K C₀ T : ℝ} (hK : 1 ≤ K) (hT : 1 ≤ T)
    (hi : Function.Injective E)
    (htp : ∀ a b c : ℂ, a ≠ c → ‖E a - E b‖ / ‖E a - E c‖ ≤
      C₀ * max ((‖a - b‖ / ‖a - c‖) ^ (1 / K)) ((‖a - b‖ / ‖a - c‖) ^ K))
    (hC₀ : 0 < C₀) {a b c : ℂ} (hac : a ≠ c) (hle : ‖a - b‖ ≤ T * ‖a - c‖) :
    ‖E a - E b‖ ≤ C₀ * T ^ K * ‖E a - E c‖ := by
  have hpos : 0 < ‖a - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hac)
  have hEpos : 0 < ‖E a - E c‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hac (hi h))
  have ht : ‖a - b‖ / ‖a - c‖ ≤ T := by rw [div_le_iff₀ hpos]; exact hle
  have h1 := htp a b c hac
  have h2 := s07d_p3_eta_le (div_nonneg (norm_nonneg _) hpos.le) ht hT hK
  have h3 : ‖E a - E b‖ / ‖E a - E c‖ ≤ C₀ * T ^ K :=
    h1.trans (mul_le_mul_of_nonneg_left h2 hC₀.le)
  rwa [div_le_iff₀ hEpos] at h3

/-- P3 helper: `jRefl u = u / |u|²`. -/
theorem s07d_p3_jRefl_eq (u : ℂ) : jRefl u = u * ((‖u‖ ^ 2)⁻¹ : ℝ) := by
  show (conj u)⁻¹ = _
  rw [Complex.inv_def, Complex.conj_conj, Complex.normSq_conj, Complex.normSq_eq_norm_sq]

/-- P3 helper: `|jRefl u| = |u|⁻¹`. -/
theorem s07d_p3_jRefl_norm (u : ℂ) : ‖jRefl u‖ = ‖u‖⁻¹ := by
  show ‖(conj u)⁻¹‖ = _
  rw [norm_inv, Complex.norm_conj]

/-- P3 helper: `|u - jRefl u| = (1 - |u|²)/|u|` for `0 < |u| ≤ 1`. -/
theorem s07d_p3_jRefl_sub {u : ℂ} (hu0 : u ≠ 0) (hu1 : ‖u‖ ≤ 1) :
    ‖u - jRefl u‖ = (1 - ‖u‖ ^ 2) / ‖u‖ := by
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu0
  rw [s07d_p3_jRefl_eq, show u - u * ((‖u‖ ^ 2)⁻¹ : ℝ) = u * ((1 - (‖u‖ ^ 2)⁻¹ : ℝ) : ℂ) by
    push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hle : 1 ≤ (‖u‖ ^ 2)⁻¹ := one_le_inv₀ (by positivity) |>.2 (by nlinarith)
  rw [abs_of_nonpos (by linarith)]
  field_simp
  ring

/-- P3 helper: the unit circle as the set `{z | |z| = 1}` is compact. -/
theorem s07d_p3_circle_compact : IsCompact {z : ℂ | ‖z‖ = 1} := by
  have : {z : ℂ | ‖z‖ = 1} = sphere (0 : ℂ) 1 := by
    ext z; simp
  rw [this]; exact isCompact_sphere 0 1

/-- P3 helper: `exp d_𝔻(0, ζ) = (1 + |ζ|)/(1 - |ζ|)`. -/
theorem s07d_p3_exp_dd0 {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    Real.exp (diskDist 0 ζ) = (1 + ‖ζ‖) / (1 - ‖ζ‖) := by
  set δ := ‖ζ‖ with hδ
  have hδ0 : 0 ≤ δ := norm_nonneg ζ
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < 1 - δ ^ 2 := by nlinarith
  have hx : diskCoshDist 0 ζ = 1 + 2 * δ ^ 2 / (1 - δ ^ 2) := by
    show 1 + 2 * ‖(0 : ℂ) - ζ‖ ^ 2 / ((1 - ‖(0 : ℂ)‖ ^ 2) * (1 - ‖ζ‖ ^ 2)) = _
    rw [zero_sub, norm_neg, norm_zero, ← hδ]
    ring
  have hx1 : 1 ≤ 1 + 2 * δ ^ 2 / (1 - δ ^ 2) := by
    have : 0 ≤ 2 * δ ^ 2 / (1 - δ ^ 2) := by positivity
    linarith
  show Real.exp (Real.arcosh (diskCoshDist 0 ζ)) = _
  rw [hx, Real.exp_arcosh hx1]
  have hsq : (1 + 2 * δ ^ 2 / (1 - δ ^ 2)) ^ 2 - 1 = (2 * δ / (1 - δ ^ 2)) ^ 2 := by
    field_simp
    ring
  rw [hsq, Real.sqrt_sq (by positivity)]
  field_simp
  ring

/-- P3 helper: `|ζ| ≤ d_𝔻(0, ζ)` and `1/(1 - |ζ|) ≤ exp d_𝔻(0, ζ)`. -/
theorem s07d_p3_dd0_bounds {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ‖ζ‖ ≤ diskDist 0 ζ ∧ 1 / (1 - ‖ζ‖) ≤ Real.exp (diskDist 0 ζ) := by
  have hδ0 : 0 ≤ ‖ζ‖ := norm_nonneg ζ
  have h1 : 0 < 1 - ‖ζ‖ := by linarith
  have hb : 1 / (1 - ‖ζ‖) ≤ Real.exp (diskDist 0 ζ) := by
    rw [s07d_p3_exp_dd0 hζ]
    exact div_le_div_of_nonneg_right (by linarith) h1.le
  refine ⟨?_, hb⟩
  rw [← Real.exp_le_exp]
  refine le_trans ?_ hb
  rw [le_div_iff₀ h1]
  have h := Real.add_one_le_exp (-‖ζ‖)
  have he : Real.exp ‖ζ‖ * Real.exp (-‖ζ‖) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  nlinarith [Real.exp_pos ‖ζ‖]

/-- P3 helper: `d_𝔻(u, v) = d_𝔻(0, M_u v)`. -/
theorem s07d_p3_dd_blaschke {u v : ℂ} (hu : u ∈ unitDisc) (hv : v ∈ unitDisc) :
    diskDist u v = diskDist 0 (blaschke u v) := by
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  have hv1 : ‖v‖ < 1 := mem_ball_zero_iff.mp hv
  show Real.arcosh (diskCoshDist u v) = Real.arcosh (diskCoshDist 0 (blaschke u v))
  rw [← s02_diskCoshDist_blaschke hu1 hu1 hv1, blaschke_self]

/-- P3 helper: Möbius invariance of `d_𝔻`. -/
theorem s07d_p3_dd_inv {b x y : ℂ} (hb : b ∈ unitDisc) (hx : x ∈ unitDisc) (hy : y ∈ unitDisc) :
    diskDist (blaschke b x) (blaschke b y) = diskDist x y := by
  show Real.arcosh (diskCoshDist (blaschke b x) (blaschke b y)) = Real.arcosh (diskCoshDist x y)
  rw [s02_diskCoshDist_blaschke (mem_ball_zero_iff.mp hb) (mem_ball_zero_iff.mp hx)
    (mem_ball_zero_iff.mp hy)]

/-- P3 helper: on a radius, `exp d_𝔻(ρ e, δ e) = ((1+δ)/(1-δ)) / ((1+ρ)/(1-ρ))` for
`0 ≤ ρ ≤ δ < 1`, `|e| = 1`. -/
theorem s07d_p3_exp_dd_radial {e : ℂ} (he : ‖e‖ = 1) {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hρδ : ρ ≤ δ)
    (hδ : δ < 1) :
    Real.exp (diskDist ((ρ : ℂ) * e) ((δ : ℂ) * e)) =
      ((1 + δ) / (1 - δ)) / ((1 + ρ) / (1 - ρ)) := by
  have hρ1 : ρ < 1 := lt_of_le_of_lt hρδ hδ
  have hmem : ∀ t : ℝ, 0 ≤ t → t < 1 → ((t : ℂ) * e) ∈ unitDisc := fun t ht0 ht1 => by
    refine mem_ball_zero_iff.2 ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0, he, mul_one]
    exact ht1
  have hden : (1 : ℝ) - ρ * δ ≠ 0 := by nlinarith
  have hbl : blaschke ((ρ : ℂ) * e) ((δ : ℂ) * e) = (((δ - ρ) / (1 - ρ * δ) : ℝ) : ℂ) * e := by
    have hce : conj e * e = 1 := by
      rw [Complex.conj_mul', he]; norm_num
    show ((δ : ℂ) * e - (ρ : ℂ) * e) / (1 - conj ((ρ : ℂ) * e) * ((δ : ℂ) * e)) = _
    rw [map_mul, Complex.conj_ofReal]
    have : (1 : ℂ) - (ρ : ℂ) * conj e * ((δ : ℂ) * e) = ((1 - ρ * δ : ℝ) : ℂ) := by
      rw [show (ρ : ℂ) * conj e * ((δ : ℂ) * e) = (ρ : ℂ) * δ * (conj e * e) by ring, hce]
      push_cast; ring
    have hden' : ((1 - ρ * δ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hden
    have hden'' : (1 : ℂ) - (ρ : ℂ) * (δ : ℂ) ≠ 0 := by push_cast at hden'; exact hden'
    have hden3 : (1 : ℂ) - (δ : ℂ) * (ρ : ℂ) ≠ 0 := by rw [mul_comm]; exact hden''
    rw [this, div_eq_iff hden']
    push_cast
    field_simp
  rw [s07d_p3_dd_blaschke (hmem ρ hρ hρ1) (hmem δ (hρ.trans hρδ) hδ), hbl]
  have hq0 : 0 ≤ (δ - ρ) / (1 - ρ * δ) := div_nonneg (by linarith) (by nlinarith)
  have hq1 : (δ - ρ) / (1 - ρ * δ) < 1 := by
    rw [div_lt_one (by nlinarith)]; nlinarith
  have hn : ‖(((δ - ρ) / (1 - ρ * δ) : ℝ) : ℂ) * e‖ = (δ - ρ) / (1 - ρ * δ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hq0, he, mul_one]
  rw [s07d_p3_exp_dd0 (by rw [hn]; exact hq1), hn]
  have h1 : (1 : ℝ) - δ ≠ 0 := by linarith
  have h2 : (1 : ℝ) - ρ ≠ 0 := by linarith
  have h3 : (1 : ℝ) + ρ ≠ 0 := by linarith
  have h4 : 1 - (δ - ρ) / (1 - ρ * δ) ≠ 0 := by
    have : (δ - ρ) / (1 - ρ * δ) < 1 := hq1
    linarith
  have hden2 : (1 : ℝ) - δ * ρ ≠ 0 := by rw [mul_comm]; exact hden
  rw [div_div_div_eq, div_eq_div_iff h4 (mul_ne_zero h1 h3)]
  field_simp
  ring

/-- P3 helper: `d_𝔻(z, w) = 0` forces `z = w`. -/
theorem s07d_p3_dd_eq_zero {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc)
    (h : diskDist z w ≤ 0) : z = w := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hζ : ‖blaschke z w‖ < 1 := blaschke_mem_unitDisc hz1 hw1
  have hb := (s07d_p3_dd0_bounds hζ).1
  rw [← s07d_p3_dd_blaschke hz hw] at hb
  have h0 : blaschke z w = 0 := norm_le_zero_iff.1 (hb.trans h)
  have := blaschke_neg_blaschke hz1 hw1
  rw [h0, blaschke_neg_zero] at this
  exact this

/-- P3 helper (splitting a hyperbolic segment): if `m < d_𝔻(z, w)`, there is `p ∈ 𝔻` with
`d_𝔻(z, p) ≤ m` and `d_𝔻(p, w) ≤ d_𝔻(z, w) - m` (the point at distance `m` on the geodesic). -/
theorem s07d_p3_split {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) {m : ℝ} (hm : 0 < m)
    (hlt : m < diskDist z w) :
    ∃ p ∈ unitDisc, diskDist z p ≤ m ∧ diskDist p w ≤ diskDist z w - m := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hnz : ‖-z‖ < 1 := by simpa using hz1
  set ζ := blaschke z w with hζdef
  have hζ : ‖ζ‖ < 1 := blaschke_mem_unitDisc hz1 hw1
  have hdζ : diskDist z w = diskDist 0 ζ := s07d_p3_dd_blaschke hz hw
  set δ := ‖ζ‖ with hδdef
  have hδ0 : 0 < δ := by
    rcases (norm_nonneg ζ).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : ζ = 0 := norm_eq_zero.1 h.symm
      rw [hdζ, h0, s07_mo_dist_self] at hlt
      linarith
  set e : ℂ := ζ / (δ : ℂ) with hedef
  have hδC : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hδ0.ne'
  have he : ‖e‖ = 1 := by
    rw [hedef, norm_div, Complex.norm_real, Real.norm_of_nonneg hδ0.le, ← hδdef, div_self hδ0.ne']
  have hζe : ζ = (δ : ℂ) * e := by rw [hedef]; field_simp
  set ρ : ℝ := (Real.exp m - 1) / (Real.exp m + 1) with hρdef
  have hem : 1 < Real.exp m := by have := Real.add_one_le_exp m; linarith
  have hρ0 : 0 ≤ ρ := div_nonneg (by linarith) (by linarith)
  have hρ1 : ρ < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hρe : (1 + ρ) / (1 - ρ) = Real.exp m := by
    rw [hρdef]
    have h1 : Real.exp m + 1 ≠ 0 := by linarith
    field_simp
    ring
  have hexpd : Real.exp (diskDist z w) = (1 + δ) / (1 - δ) := by rw [hdζ]; exact s07d_p3_exp_dd0 hζ
  have hρδ : ρ ≤ δ := by
    by_contra hc
    have hc := lt_of_not_ge hc
    have h1 : Real.exp m < Real.exp (diskDist z w) := Real.exp_lt_exp.2 hlt
    rw [← hρe, hexpd, div_lt_div_iff₀ (by linarith) (by linarith)] at h1
    nlinarith
  have hpe : ((ρ : ℂ) * e) ∈ unitDisc := by
    refine mem_ball_zero_iff.2 ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0, he, mul_one]
    exact hρ1
  set p := blaschke (-z) ((ρ : ℂ) * e) with hpdef
  have hp : p ∈ unitDisc :=
    mem_ball_zero_iff.2 (blaschke_mem_unitDisc hnz (mem_ball_zero_iff.1 hpe))
  have hzp : blaschke z p = (ρ : ℂ) * e := blaschke_blaschke_neg hz1 (mem_ball_zero_iff.1 hpe)
  refine ⟨p, hp, ?_, ?_⟩
  · have h1 : diskDist z p = diskDist 0 ((ρ : ℂ) * e) := by
      rw [s07d_p3_dd_blaschke hz hp, hzp]
    have h2 : Real.exp (diskDist 0 ((ρ : ℂ) * e)) = Real.exp m := by
      rw [s07d_p3_exp_dd0 (mem_ball_zero_iff.1 hpe), norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hρ0, he, mul_one, hρe]
    rw [h1, Real.exp_injective h2]
  · have h1 : diskDist p w = diskDist ((ρ : ℂ) * e) ((δ : ℂ) * e) := by
      rw [← s07d_p3_dd_inv hz hp hw, hzp, ← hζdef, hζe]
    have h2 := s07d_p3_exp_dd_radial he hρ0 hρδ hζ
    rw [← h1, ← hexpd, hρe, ← Real.exp_sub] at h2
    rw [Real.exp_injective h2]

/-- P3 helper (local bound from LZ `thm15_1`): a `K`-q.c. self-map of `𝔻` maps pairs at
`d_𝔻 ≤ (1/16)^K` to pairs at `d_𝔻 ≤ 2`. -/
theorem s07d_p3_qi_local {A : ℂ → ℂ} {K : ℝ} (hA : IsKQC A unitDisc K) (himg : A '' unitDisc = unitDisc)
    {z₁ z₂ : ℂ} (h₁ : z₁ ∈ unitDisc) (h₂ : z₂ ∈ unitDisc)
    (hd : diskDist z₂ z₁ ≤ (1 / 16 : ℝ) ^ K) : diskDist (A z₂) (A z₁) ≤ 2 := by
  have hK : 1 ≤ K := hA.2.1
  have hK0 : 0 < K := by linarith
  have hA₁ : A z₁ ∈ unitDisc := himg ▸ mem_image_of_mem A h₁
  have hA₂ : A z₂ ∈ unitDisc := himg ▸ mem_image_of_mem A h₂
  have hz₁ : ‖z₁‖ < 1 := mem_ball_zero_iff.mp h₁
  have hz₂ : ‖z₂‖ < 1 := mem_ball_zero_iff.mp h₂
  have h := thm15_1 hA himg h₁ h₂
  set δ := ‖(z₁ - z₂) / (1 - conj z₂ * z₁)‖ with hδdef
  set δ' := ‖(A z₁ - A z₂) / (1 - conj (A z₂) * A z₁)‖ with hδ'def
  have hbz : blaschke z₂ z₁ = (z₁ - z₂) / (1 - conj z₂ * z₁) := rfl
  have hbA : blaschke (A z₂) (A z₁) = (A z₁ - A z₂) / (1 - conj (A z₂) * A z₁) := rfl
  have hδb : ‖blaschke z₂ z₁‖ = δ := by rw [hbz]
  have hζ : ‖blaschke z₂ z₁‖ < 1 := blaschke_mem_unitDisc hz₂ hz₁
  have hδle : δ ≤ (1 / 16 : ℝ) ^ K := by
    have := (s07d_p3_dd0_bounds hζ).1
    rw [← s07d_p3_dd_blaschke h₂ h₁, hδb] at this
    exact this.trans hd
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hm1 : (1 / 16 : ℝ) ^ K ≤ 1 / 16 := by
    have := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num) hK
    simpa using this
  have hδ16 : δ ≤ 1 / 16 := hδle.trans hm1
  -- numerator: `4^{1-1/K} δ^{1/K} ≤ 4 · (1/16) = 1/4`
  have hn1 : (4 : ℝ) ^ (1 - 1 / K) ≤ 4 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (show 1 - 1 / K ≤ 1 by have h0 : 0 < 1 / K := (by positivity); linarith)
    simpa using this
  have hn2 : δ ^ (1 / K) ≤ 1 / 16 := by
    calc δ ^ (1 / K) ≤ ((1 / 16 : ℝ) ^ K) ^ (1 / K) :=
          Real.rpow_le_rpow hδ0 hδle (by positivity)
      _ = 1 / 16 := by
          rw [← Real.rpow_mul (by norm_num), mul_one_div_cancel hK0.ne', Real.rpow_one]
  have hnum : (4 : ℝ) ^ (1 - 1 / K) * δ ^ (1 / K) ≤ 1 / 4 := by
    have h0 : 0 ≤ δ ^ (1 / K) := Real.rpow_nonneg hδ0 _
    nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) (1 - 1 / K)]
  -- denominator: `(1 - δ²)^{1/(2K)} ≥ 1 - δ² ≥ 1/2`
  have hb0 : 0 < 1 - δ ^ 2 := by nlinarith
  have hb1 : 1 - δ ^ 2 ≤ 1 := by nlinarith
  have hden : 1 / 2 ≤ (1 - δ ^ 2) ^ (1 / (2 * K)) := by
    have hs : 1 / (2 * K) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have := Real.rpow_le_rpow_of_exponent_ge hb0 hb1 hs
    rw [Real.rpow_one] at this
    nlinarith
  have hδ' : δ' ≤ 1 / 2 := by
    refine h.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hζ' : ‖blaschke (A z₂) (A z₁)‖ < 1 :=
    blaschke_mem_unitDisc (mem_ball_zero_iff.mp hA₂) (mem_ball_zero_iff.mp hA₁)
  have hδ'b : ‖blaschke (A z₂) (A z₁)‖ = δ' := by rw [hbA]
  have hexp := s07d_p3_exp_dd0 hζ'
  rw [← s07d_p3_dd_blaschke hA₂ hA₁, hδ'b] at hexp
  have hδ'0 : 0 ≤ δ' := norm_nonneg _
  have h3 : Real.exp (diskDist (A z₂) (A z₁)) ≤ Real.exp 2 := by
    rw [hexp, div_le_iff₀ (by linarith)]
    have : (3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ); linarith
    nlinarith
  exact Real.exp_le_exp.1 h3

/-- P3 helper (chaining): a self-map of `𝔻` sending pairs at `d_𝔻 ≤ m` to pairs at `d_𝔻 ≤ M`
sends pairs at `d_𝔻 ≤ n m` to pairs at `d_𝔻 ≤ n M`. -/
theorem s07d_p3_chain {A : ℂ → ℂ} {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hmaps : MapsTo A unitDisc unitDisc)
    (hloc : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, diskDist z w ≤ m → diskDist (A z) (A w) ≤ M) :
    ∀ n : ℕ, ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, diskDist z w ≤ n * m →
      diskDist (A z) (A w) ≤ n * M := by
  intro n
  induction n with
  | zero =>
    intro z hz w hw h
    rw [Nat.cast_zero, zero_mul] at h
    rw [s07d_p3_dd_eq_zero hz hw h, s07_mo_dist_self, Nat.cast_zero, zero_mul]
  | succ n ih =>
    intro z hz w hw h
    by_cases hle : diskDist z w ≤ m
    · calc diskDist (A z) (A w) ≤ M := hloc z hz w hw hle
        _ ≤ ((n + 1 : ℕ) : ℝ) * M := by
          have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
          nlinarith
    · have hle := lt_of_not_ge hle
      obtain ⟨p, hp, hzp, hpw⟩ := s07d_p3_split hz hw hm hle
      have hpw' : diskDist p w ≤ n * m := by push_cast at h; linarith
      have h1 := hloc z hz p hp hzp
      have h2 := ih p hp w hw hpw'
      calc diskDist (A z) (A w) ≤ diskDist (A z) (A p) + diskDist (A p) (A w) :=
            s02_diskDist_triangle (hmaps hz) (hmaps hp) (hmaps hw)
        _ ≤ M + n * M := add_le_add h1 h2
        _ = ((n + 1 : ℕ) : ℝ) * M := by push_cast; ring

/-- P3 helper: the coarse upper bound `d_𝔻(A z, A w) ≤ (M/m) d_𝔻(z, w) + M`. -/
theorem s07d_p3_coarse_upper {A : ℂ → ℂ} {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hmaps : MapsTo A unitDisc unitDisc)
    (hloc : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, diskDist z w ≤ m → diskDist (A z) (A w) ≤ M)
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    diskDist (A z) (A w) ≤ M / m * diskDist z w + M := by
  have hd0 : 0 ≤ diskDist z w := s02_diskDist_nonneg hz hw
  obtain ⟨n, hn⟩ := exists_nat_ge (diskDist z w / m)
  set k := Nat.ceil (diskDist z w / m) with hk
  have hk1 : diskDist z w ≤ k * m := by
    have := Nat.le_ceil (diskDist z w / m)
    rw [div_le_iff₀ hm] at this
    exact this
  have hk2 : (k : ℝ) ≤ diskDist z w / m + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have h := s07d_p3_chain hm hM hmaps hloc k z hz w hw hk1
  calc diskDist (A z) (A w) ≤ k * M := h
    _ ≤ (diskDist z w / m + 1) * M := mul_le_mul_of_nonneg_right hk2 hM
    _ = M / m * diskDist z w + M := by ring

/-- P3 helper (Koebe growth at bounded hyperbolic distance): for a conformal `f : 𝔻 → Ω` and
`d_𝔻(u, v) ≤ D`, `|f u - f v| ≤ 4 e^{2D} d_𝔻(u, v) d(f u, ∂Ω)`. -/
theorem s07d_p3_koebe_lin {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {u v : ℂ}
    (hu : u ∈ unitDisc) (hv : v ∈ unitDisc) {D : ℝ} (hd : diskDist u v ≤ D) :
    ‖f u - f v‖ ≤ 4 * Real.exp (2 * D) * diskDist u v * infDist (f u) Ωᶜ := by
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  have hv1 : ‖v‖ < 1 := mem_ball_zero_iff.mp hv
  have hnz : ‖-u‖ < 1 := by simpa using hu1
  have hmaps : MapsTo (blaschke (-u)) unitDisc unitDisc := fun ζ hζ =>
    mem_ball_zero_iff.mpr (blaschke_mem_unitDisc hnz (mem_ball_zero_iff.mp hζ))
  have hinjB : InjOn (blaschke (-u)) unitDisc := (isConformalOnto_blaschke hnz).2.1
  have hDf : DifferentiableOn ℂ (fun ζ => (f ∘ blaschke (-u)) ζ - f u) (ball 0 1) :=
    (hf.1.comp (differentiableOn_blaschke hnz) hmaps).sub (differentiableOn_const _)
  have hinj : InjOn (fun ζ => (f ∘ blaschke (-u)) ζ - f u) (ball 0 1) := by
    intro ζ₁ h₁ ζ₂ h₂ he
    exact hinjB h₁ h₂ (hf.2.1 (hmaps h₁) (hmaps h₂) (sub_left_inj.mp he))
  have h0 : (fun ζ => (f ∘ blaschke (-u)) ζ - f u) 0 = 0 := by simp
  set ζ := blaschke u v with hζdef
  have hζ : ‖ζ‖ < 1 := blaschke_mem_unitDisc hu1 hv1
  have hg := koebe_growth_scaled hDf hinj h0 hζ
  have hdz : deriv (fun ζ => (f ∘ blaschke (-u)) ζ - f u) 0 = deriv (f ∘ blaschke (-u)) 0 :=
    deriv_sub_const _
  rw [hdz, s02_norm_deriv_comp_blaschke hf hu] at hg
  have hval : (f ∘ blaschke (-u)) ζ - f u = f v - f u := by
    simp only [Function.comp_apply, hζdef, blaschke_neg_blaschke hu1 hv1]
  rw [hval, norm_sub_rev] at hg
  have hm := (lem_koebe_a hf hu).2.1
  obtain ⟨hδd, hδe⟩ := s07d_p3_dd0_bounds hζ
  rw [← s07d_p3_dd_blaschke hu hv] at hδd hδe
  have h1 : 0 < 1 - ‖ζ‖ := by linarith [norm_nonneg ζ]
  have hD0 : 0 ≤ diskDist u v := (norm_nonneg ζ).trans hδd
  have he2 : (1 / (1 - ‖ζ‖)) ^ 2 ≤ Real.exp (2 * D) := by
    have : Real.exp (diskDist u v) ≤ Real.exp D := Real.exp_le_exp.2 hd
    calc (1 / (1 - ‖ζ‖)) ^ 2 ≤ Real.exp D ^ 2 :=
          pow_le_pow_left₀ (by positivity) (hδe.trans this) 2
      _ = Real.exp (2 * D) := by rw [← Real.exp_nat_mul]; norm_num
  have hd0 : 0 ≤ infDist (f u) Ωᶜ := infDist_nonneg
  calc ‖f u - f v‖ ≤ (1 - ‖u‖ ^ 2) * ‖deriv f u‖ * ‖ζ‖ / (1 - ‖ζ‖) ^ 2 := hg
    _ = ((1 - ‖u‖ ^ 2) * ‖deriv f u‖) * ‖ζ‖ * (1 / (1 - ‖ζ‖)) ^ 2 := by field_simp
    _ ≤ (4 * infDist (f u) Ωᶜ) * diskDist u v * Real.exp (2 * D) := by
        gcongr
    _ = 4 * Real.exp (2 * D) * diskDist u v * infDist (f u) Ωᶜ := by ring

/-- P3 helper (`s07_weld_admitsExt` with its witness made explicit): for the global `K`-q.c. map `F`
of a bounded quasicircle and `P` from `s07_weld_inner`, `A₀ = f⁻¹ ∘ F ∘ P` is a `K²`-q.c. self-map
of `𝔻` with boundary values `h`.  The proof is that of `s07_weld_admitsExt`. -/
theorem s07d_p3_A0 {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    {f g h : ℂ → ℂ} (hw : IsDiskWelding Ω Ωs f g h) {F P : ℂ → ℂ} (hFq : IsKQC F univ K)
    (hFs : F '' univ = univ) (hF1 : F '' unitDisc = Ω) (hPq : IsKQC P unitDisc K)
    (hPs : P '' unitDisc = unitDisc) (hP0 : P 0 = 0)
    (hPF : ∀ z ∈ unitDisc, z ≠ 0 → F (jRefl (P z)) = g (jRefl z)) :
    IsKQC (Function.invFunOn f unitDisc ∘ (F ∘ P)) unitDisc (K * K) ∧
      (Function.invFunOn f unitDisc ∘ (F ∘ P)) '' unitDisc = unitDisc ∧
      HasDiskBoundaryValues (Function.invFunOn f unitDisc ∘ (F ∘ P)) h := by
  obtain ⟨hf, -, -, hhS, hhb⟩ := hw
  obtain ⟨e, rfl⟩ := t1_homeomorph hFq hFs
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hfs := hf.symm isOpen_ball
  set fi := Function.invFunOn f unitDisc with hfi
  have c2 := thm7_1_comp (thm7_1_comp hPq (nx_isKQC_restrict hFq isOpen_ball (subset_univ _))
    hPs.le) (isKQC_one_of_conformal hΩo hfs) (by rw [image_comp, hPs]; exact hF1.le)
  rw [mul_one] at c2
  have hjfix : ∀ w : ℂ, ‖w‖ = 1 → jRefl w = w := fun w hw => by
    show (conj w)⁻¹ = w
    refine inv_eq_of_mul_eq_one_right ?_
    rw [Complex.conj_mul', hw]
    norm_num
  have hjj : ∀ z : ℂ, jRefl (jRefl z) = z := fun z => by
    show (conj (conj z)⁻¹)⁻¹ = z
    rw [map_inv₀, Complex.conj_conj, inv_inv]
  have hjc : ∀ w : ℂ, w ≠ 0 → ContinuousAt jRefl w := fun w hw =>
    Complex.continuous_conj.continuousAt.inv₀ ((map_ne_zero _).2 hw)
  have hPmem : ∀ z ∈ unitDisc, P z ∈ unitDisc := fun z hz => hPs ▸ mem_image_of_mem P hz
  have hPne : ∀ z ∈ unitDisc, z ≠ 0 → P z ≠ 0 := fun z hz hz0 h0 =>
    hz0 (hPq.2.2.1.2.1 hz (mem_ball_self one_pos) (h0.trans hP0.symm))
  refine ⟨c2, ?_, fun ζ hζ => ?_⟩
  · rw [image_comp, image_comp, hPs, hF1]
    exact hfs.2.2
  obtain ⟨x, hfx, hgx⟩ := hhb ζ hζ
  have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.1 hζ
  have hζ0 : ζ ≠ 0 := norm_ne_zero_iff.1 (by rw [hζ1]; exact one_ne_zero)
  have hcl : ∀ w : ℂ, ‖w‖ = 1 → w ∈ closure unitDisc := fun w hw => by
    show w ∈ closure (ball (0 : ℂ) 1)
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact mem_closedBall_zero_iff.2 hw.le
  have : (𝓝[unitDisc] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hcl ζ hζ1)
  have : (𝓝[unitDisc] (h ζ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (hcl _ (mem_sphere_zero_iff_norm.1 (hhS hζ)))
  set l := 𝓝[unitDisc] ζ with hl
  have hlD : ∀ᶠ z in l, z ∈ unitDisc ∧ z ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_ne_nhds hζ0)] with z h1 h2
    exact ⟨h1, h2⟩
  -- `j z → ζ` within `𝔻*`
  have hjT : Tendsto jRefl l (𝓝[unitDiscExterior] ζ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hlD.mono fun z hz => ?_⟩
    · have := (hjc ζ hζ0).tendsto.mono_left (nhdsWithin_le_nhds (s := unitDisc))
      rwa [hjfix ζ hζ1] at this
    · show 1 < ‖(conj z)⁻¹‖
      rw [norm_inv, Complex.norm_conj]
      exact (one_lt_inv₀ (norm_pos_iff.2 hz.2)).2 (mem_ball_zero_iff.1 hz.1)
  have heP : Tendsto (fun z => e (jRefl (P z))) l (𝓝 x) :=
    (hgx.comp hjT).congr' (hlD.mono fun z hz => (hPF z hz.1 hz.2).symm)
  have hjP : Tendsto (fun z => jRefl (P z)) l (𝓝 (e.symm x)) :=
    ((e.symm.continuous.tendsto x).comp heP).congr' (Eventually.of_forall fun z => by
      show e.symm (e (jRefl (P z))) = jRefl (P z)
      exact e.symm_apply_apply _)
  -- `‖F⁻¹ x‖ = 1`
  have hy1 : ‖e.symm x‖ = 1 := by
    apply le_antisymm
    · have hx : x ∈ closure Ω := mem_closure_of_tendsto hfx
        (eventually_nhdsWithin_of_forall fun z hz => hf.2.2 ▸ mem_image_of_mem f hz)
      rw [← hF1, ← e.image_closure] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [e.symm_apply_apply]
      have : y ∈ closure (ball (0 : ℂ) 1) := hy
      rw [closure_ball (0 : ℂ) one_ne_zero] at this
      exact mem_closedBall_zero_iff.1 this
    · refine ge_of_tendsto hjP.norm (hlD.mono fun z hz => ?_)
      have hPz := hPne z hz.1 hz.2
      show 1 ≤ ‖(conj (P z))⁻¹‖
      rw [norm_inv, Complex.norm_conj]
      exact (one_le_inv₀ (norm_pos_iff.2 hPz)).2 (mem_ball_zero_iff.1 (hPmem z hz.1)).le
  have hy0 : e.symm x ≠ 0 := norm_ne_zero_iff.1 (by rw [hy1]; exact one_ne_zero)
  have hPT : Tendsto P l (𝓝 (e.symm x)) := by
    have := ((hjc _ hy0).tendsto).comp hjP
    rw [hjfix _ hy1] at this
    exact this.congr' (Eventually.of_forall fun z => hjj (P z))
  have heT : Tendsto (fun z => e (P z)) l (𝓝 x) := by
    have := (e.continuous.tendsto _).comp hPT
    rwa [e.apply_symm_apply] at this
  refine s07_disk_preimage_tendsto hΓ hf (hhS hζ) hfx (hlD.mono fun z hz => ?_) ?_
  · have h1 : e (P z) ∈ Ω := hF1 ▸ mem_image_of_mem e (hPmem z hz.1)
    have h2 : fi (e (P z)) ∈ fi '' Ω := mem_image_of_mem fi h1
    have h3 : fi '' Ω = unitDisc := hfs.2.2
    rw [h3] at h2
    exact h2
  · refine heT.congr' (hlD.mono fun z hz => ?_)
    have hm : e (P z) ∈ f '' unitDisc := by
      rw [hf.2.2, ← hF1]
      exact mem_image_of_mem _ (hPmem z hz.1)
    exact (Function.invFunOn_eq hm).symm

/-- P3 helper (bounded pairs; as `s03_b0_infDist`): for disjoint open `Ω`, `Ωs` and `w ∈ Ω`,
`d(w, Ωᶜ) = d(w, Γ)`, `Γ = (Ω ∪ Ωs)ᶜ`. -/
theorem s07d_p3_infDist_compl {Ω Ωs : Set ℂ} (hΩo : IsOpen Ω) (hΩso : IsOpen Ωs)
    (hdisj : Disjoint Ω Ωs) (hne : (curveOf Ω Ωs).Nonempty) {w : ℂ} (hw : w ∈ Ω) :
    infDist w Ωᶜ = infDist w (curveOf Ω Ωs) := by
  have hsub : curveOf Ω Ωs ⊆ Ωᶜ := fun x hx hxΩ => hx (Or.inl hxΩ)
  refine le_antisymm (infDist_le_infDist_of_subset hsub hne)
    ((le_infDist (hne.mono hsub)).2 fun y hy => ?_)
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

/-- P3.1: a `K`-quasiconformal self-map of `𝔻` (onto) is an `(L, c)`-quasi-isometry of `d_𝔻`, with
`L`, `c` depending only on `K`. -/
theorem s07d_p3_qc_qi (K : ℝ) (hK : 1 ≤ K) : ∃ L c : ℝ, 1 ≤ L ∧ 0 ≤ c ∧
    ∀ A : ℂ → ℂ, IsKQC A unitDisc K → A '' unitDisc = unitDisc → IsDiskQI A L c := by
  have _hK := hK
  set m : ℝ := (1 / 16 : ℝ) ^ K with hmdef
  have hm : 0 < m := by positivity
  have hm1 : m ≤ 1 := by
    have := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num) hK
    rw [Real.rpow_one] at this
    rw [hmdef]; linarith
  refine ⟨2 / m, 2, by rw [le_div_iff₀ hm]; linarith, by norm_num, fun A hA himg => ?_⟩
  have hmaps : MapsTo A unitDisc unitDisc := fun z hz => himg ▸ mem_image_of_mem A hz
  have hloc : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, diskDist z w ≤ m → diskDist (A z) (A w) ≤ 2 :=
    fun z hz w hw h => s07d_p3_qi_local hA himg hw hz h
  -- the inverse
  set Ai := Function.invFunOn A unitDisc with hAidef
  have hAi : IsKQC Ai unitDisc K := by
    have := thm7_2_inv hA; rwa [himg] at this
  have hinj : InjOn A unitDisc := hA.2.2.1.2.1
  have hAiA : ∀ z ∈ unitDisc, Ai (A z) = z := fun z hz => hinj.leftInvOn_invFunOn hz
  have hAiimg : Ai '' unitDisc = unitDisc := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← himg] at hy
      exact Function.invFunOn_mem hy
    · intro hz
      exact ⟨A z, hmaps hz, hAiA z hz⟩
  have hmapsi : MapsTo Ai unitDisc unitDisc := fun z hz => hAiimg ▸ mem_image_of_mem Ai hz
  have hloci : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, diskDist z w ≤ m → diskDist (Ai z) (Ai w) ≤ 2 :=
    fun z hz w hw h => s07d_p3_qi_local hAi hAiimg hw hz h
  refine ⟨hmaps, fun x hx y hy => ⟨?_, s07d_p3_coarse_upper hm (by norm_num) hmaps hloc hx hy⟩⟩
  have h := s07d_p3_coarse_upper hm (by norm_num) hmapsi hloci (hmaps hx) (hmaps hy)
  rw [hAiA x hx, hAiA y hy] at h
  rw [inv_div]
  have h3 : m / 2 * diskDist x y ≤ m / 2 * (2 / m * diskDist (A x) (A y) + 2) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have e : m / 2 * (2 / m * diskDist (A x) (A y) + 2) = diskDist (A x) (A y) + m := by
    field_simp
  linarith

/-- P3.2 (Koebe, inside): for a conformal `f : 𝔻 → Ω` and `d_𝔻(u, v) ≤ D`,
`|f u - f v| ≤ C d_𝔻(u, v) d(f u, ∂Ω)` and `d(f u, ∂Ω) ≤ C d(f v, ∂Ω)`. Conversely, Euclidean-close
points are hyperbolically close: `|f u - f v| ≤ d(f u, ∂Ω)/2` gives
`d_𝔻(u, v) ≤ C |f u - f v| / d(f u, ∂Ω)`. -/
theorem s07d_p3_koebe_int (D : ℝ) (hD : 0 ≤ D) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsConformalOnto f unitDisc Ω →
      ∀ u ∈ unitDisc, ∀ v ∈ unitDisc,
        (diskDist u v ≤ D →
          ‖f u - f v‖ ≤ C * diskDist u v * infDist (f u) Ωᶜ ∧
            infDist (f u) Ωᶜ ≤ C * infDist (f v) Ωᶜ) ∧
        (‖f u - f v‖ ≤ infDist (f u) Ωᶜ / 2 →
          diskDist u v * infDist (f u) Ωᶜ ≤ C * ‖f u - f v‖) := by
  have hE1 : 1 ≤ Real.exp (2 * D) := Real.one_le_exp (by linarith)
  refine ⟨4 * Real.exp (2 * D) * (D + 1) + 3, by nlinarith, ?_⟩
  intro Ω f hf u hu v hv
  have hfu : f u ∈ Ω := by rw [← hf.2.2]; exact mem_image_of_mem f hu
  have hd0 : 0 < infDist (f u) Ωᶜ := s02_infDist_pos hf hfu
  have hdv0 : 0 ≤ infDist (f v) Ωᶜ := infDist_nonneg
  have hDD : 0 ≤ diskDist u v := s02_diskDist_nonneg hu hv
  refine ⟨fun hd => ⟨?_, ?_⟩, fun hc => ?_⟩
  · have h := s07d_p3_koebe_lin hf hu hv hd
    calc ‖f u - f v‖ ≤ 4 * Real.exp (2 * D) * diskDist u v * infDist (f u) Ωᶜ := h
      _ ≤ (4 * Real.exp (2 * D) * (D + 1) + 3) * diskDist u v * infDist (f u) Ωᶜ := by
        gcongr; nlinarith
  · have hd' : diskDist v u ≤ D := by rw [← s02_diskDist_comm hu hv]; exact hd
    have h := s07d_p3_koebe_lin hf hv hu hd'
    rw [← s02_diskDist_comm hu hv] at h
    have hlip : infDist (f u) Ωᶜ ≤ infDist (f v) Ωᶜ + dist (f u) (f v) :=
      infDist_le_infDist_add_dist
    rw [dist_eq_norm, norm_sub_rev] at hlip
    have h2 : 4 * Real.exp (2 * D) * diskDist u v * infDist (f v) Ωᶜ ≤
        4 * Real.exp (2 * D) * D * infDist (f v) Ωᶜ := by gcongr
    nlinarith
  · have hB : ball (f u) (infDist (f u) Ωᶜ) ⊆ Ω := by
      intro y hy
      by_contra hyc
      have := infDist_le_dist_of_mem (x := f u) (show y ∈ Ωᶜ from hyc)
      rw [mem_ball, dist_comm] at hy
      linarith
    have hsm := s03_dd_small ⟨f, hf⟩ hd0 hB (by rw [norm_sub_rev]; exact hc)
    rw [subsec_poincare_dist hf hu hv, norm_sub_rev] at hsm
    have hm := mul_le_mul_of_nonneg_right hsm hd0.le
    rw [mul_assoc, div_mul_cancel₀ _ hd0.ne'] at hm
    calc diskDist u v * infDist (f u) Ωᶜ ≤ 3 * ‖f u - f v‖ := hm
      _ ≤ (4 * Real.exp (2 * D) * (D + 1) + 3) * ‖f u - f v‖ := by
          gcongr; nlinarith


/-- P3 helper: `jRefl` is an involution of `ℂ` (with `jRefl 0 = 0`). -/
theorem s07d_p3_jRefl_jRefl (z : ℂ) : jRefl (jRefl z) = z := by
  show (conj (conj z)⁻¹)⁻¹ = z
  rw [map_inv₀, Complex.conj_conj, inv_inv]

/-- P3 helper: `jRefl` maps `𝔻*` into `𝔻 ∖ {0}`. -/
theorem s07d_p3_jRefl_ext {z : ℂ} (hz : z ∈ unitDiscExterior) : jRefl z ∈ unitDisc ∧ jRefl z ≠ 0 := by
  have hz1 : 1 < ‖z‖ := hz
  have hn := s07d_p3_jRefl_norm z
  have h0 : 0 < ‖z‖ := by linarith
  refine ⟨mem_ball_zero_iff.mpr (by rw [hn]; exact inv_lt_one_of_one_lt₀ hz1), fun h0' => ?_⟩
  rw [h0', norm_zero] at hn
  have : 0 < ‖z‖⁻¹ := inv_pos.2 h0
  linarith

/-- P3 helper: `jRefl` maps `𝔻 ∖ {0}` into `𝔻*`. -/
theorem s07d_p3_jRefl_int {u : ℂ} (hu : u ∈ unitDisc) (hu0 : u ≠ 0) : jRefl u ∈ unitDiscExterior := by
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  have h0 : 0 < ‖u‖ := norm_pos_iff.2 hu0
  show 1 < ‖jRefl u‖
  rw [s07d_p3_jRefl_norm]
  exact (one_lt_inv₀ h0).2 hu1


/-- P3 helper: `d_𝔻` is invariant under conjugation. -/
theorem s07d_p3_dd_conj (z z' : ℂ) : diskDist (conj z) (conj z') = diskDist z z' := by
  show Real.arcosh (1 + 2 * ‖conj z - conj z'‖ ^ 2 / ((1 - ‖conj z‖ ^ 2) * (1 - ‖conj z'‖ ^ 2))) =
    Real.arcosh (1 + 2 * ‖z - z'‖ ^ 2 / ((1 - ‖z‖ ^ 2) * (1 - ‖z'‖ ^ 2)))
  rw [← map_sub, Complex.norm_conj, Complex.norm_conj, Complex.norm_conj]

/-- P3 helper: `d_𝔻(0, ζ) = arcosh(1 + 2|ζ|²/(1 - |ζ|²))`. -/
theorem s07d_p3_dd0_eq (ζ : ℂ) : diskDist 0 ζ = Real.arcosh (1 + 2 * ‖ζ‖ ^ 2 / (1 - ‖ζ‖ ^ 2)) := by
  show Real.arcosh (1 + 2 * ‖0 - ζ‖ ^ 2 / ((1 - ‖(0 : ℂ)‖ ^ 2) * (1 - ‖ζ‖ ^ 2))) = _
  rw [zero_sub, norm_neg, norm_zero, show (1 - (0 : ℝ) ^ 2) * (1 - ‖ζ‖ ^ 2) = 1 - ‖ζ‖ ^ 2 by ring]

/-- P3 helper: `|1/(a - x₀) - 1/(b - x₀)| = |a - b|/(|a - x₀||b - x₀|)`. -/
theorem s07d_p3_invAt_sub {x₀ a b : ℂ} (ha : a ≠ x₀) (hb : b ≠ x₀) :
    ‖invAt x₀ a - invAt x₀ b‖ = ‖a - b‖ / (‖a - x₀‖ * ‖b - x₀‖) := by
  have h1 : a - x₀ ≠ 0 := sub_ne_zero.2 ha
  have h2 : b - x₀ ≠ 0 := sub_ne_zero.2 hb
  show ‖(a - x₀)⁻¹ - (b - x₀)⁻¹‖ = _
  rw [inv_sub_inv h1 h2, norm_div, norm_mul, show b - x₀ - (a - x₀) = b - a by ring,
    norm_sub_rev]

/-- P3 helper (the deep point; the third item of P3.4 at `u = 0`, restated so that P3.3, which sits
above P3.4, can use it): `diam Γ ≤ C d(E 0, Γ)`. -/
theorem s07d_p3_deep (K : ℝ) (hK : 1 ≤ K) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Ω Ωs : Set ℂ) (E : ℂ → ℂ), IsKQC E univ K → E '' univ = univ → E '' unitDisc = Ω →
      E '' unitDiscExterior = Ωs → diam (curveOf Ω Ωs) ≤ C * infDist (E 0) (curveOf Ω Ωs) := by
  obtain ⟨C₀, hC₀, htp₀⟩ := lem_three_point K hK
  have h3 : 0 < (3 : ℝ) ^ K := by positivity
  refine ⟨2 * C₀ * (3 : ℝ) ^ K + 1, by nlinarith [mul_pos hC₀ h3], ?_⟩
  intro Ω Ωs E hE hs hD hX
  have hc : Continuous E := continuousOn_univ.mp hE.2.2.1.1
  have hi : Function.Injective E := injOn_univ.mp hE.2.2.1.2.1
  have htp := fun a b c (hac : a ≠ c) => (htp₀ E hE hs a b c hac).1
  rw [s03_cb_curve hi hs hD hX]
  have hcomp : IsCompact (E '' {z : ℂ | ‖z‖ = 1}) := s07d_p3_circle_compact.image hc
  have hne : (E '' {z : ℂ | ‖z‖ = 1}).Nonempty := ⟨E 1, 1, by simp, rfl⟩
  obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := hcomp.exists_infDist_eq_dist hne (E 0)
  have hy' : ‖y‖ = 1 := hy
  have hdy : infDist (E 0) (E '' {z : ℂ | ‖z‖ = 1}) = ‖E 0 - E y‖ := by rw [hxy, dist_eq_norm]
  have hay : (0 : ℂ) ≠ y := fun h => by
    rw [← h, norm_zero] at hy'
    exact zero_ne_one hy'
  have hfar : ∀ z : ℂ, ‖z‖ = 1 → ‖E 0 - E z‖ ≤ C₀ * (3 : ℝ) ^ K * ‖E 0 - E y‖ := by
    intro z hz
    have hle : ‖(0 : ℂ) - z‖ ≤ 3 * ‖(0 : ℂ) - y‖ := by
      rw [zero_sub, zero_sub, norm_neg, norm_neg, hz, hy']
      norm_num
    exact s07d_p3_tp_apply hK (by norm_num) hi htp hC₀ hay hle
  rw [hdy]
  refine diam_le_of_forall_dist_le (by positivity) ?_
  rintro _ ⟨z₁, hz₁, rfl⟩ _ ⟨z₂, hz₂, rfl⟩
  rw [dist_eq_norm]
  have e1 := hfar z₁ hz₁
  have e2 := hfar z₂ hz₂
  calc ‖E z₁ - E z₂‖ ≤ ‖E 0 - E z₁‖ + ‖E 0 - E z₂‖ := by
        rw [norm_sub_rev (E 0) (E z₁)]
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * (C₀ * (3 : ℝ) ^ K * ‖E 0 - E y‖) := by linarith
    _ ≤ (2 * C₀ * (3 : ℝ) ^ K + 1) * ‖E 0 - E y‖ := by nlinarith [norm_nonneg (E 0 - E y)]

/-- P3 helper (distances through the inversion `invAt x₀`, `x₀ ∈ Ω`): for `a ∈ Ωs`, with
`W = invPairΩs Ωs x₀`, `r = |a - x₀|`, `δ = d(a, Γ)`, `d₀ = d(x₀, Γ)`:
`d₀ ≤ r ≤ δ + diam Γ + d₀`, `d(1/(a - x₀), Wᶜ) r d₀ ≤ δ ≤ d(1/(a - x₀), Wᶜ) r (δ + r)`, and
`d(a, Ωsᶜ) = δ`. -/
theorem s07d_p3_inv_dist {Ω Ωs : Set ℂ} (hΩo : IsOpen Ω) (hΩso : IsOpen Ωs) (hdisj : Disjoint Ω Ωs)
    (hcpt : IsCompact (curveOf Ω Ωs)) (hne : (curveOf Ω Ωs).Nonempty) {x₀ a : ℂ} (hx₀ : x₀ ∈ Ω)
    (ha : a ∈ Ωs) :
    infDist x₀ (curveOf Ω Ωs) ≤ ‖a - x₀‖ ∧
      ‖a - x₀‖ ≤ infDist a (curveOf Ω Ωs) + diam (curveOf Ω Ωs) + infDist x₀ (curveOf Ω Ωs) ∧
      infDist (invAt x₀ a) (invPairΩs Ωs x₀)ᶜ * (‖a - x₀‖ * infDist x₀ (curveOf Ω Ωs)) ≤
        infDist a (curveOf Ω Ωs) ∧
      infDist a (curveOf Ω Ωs) ≤ infDist (invAt x₀ a) (invPairΩs Ωs x₀)ᶜ *
        (‖a - x₀‖ * (infDist a (curveOf Ω Ωs) + ‖a - x₀‖)) ∧
      infDist a Ωsᶜ = infDist a (curveOf Ω Ωs) := by
  have hcs : curveOf Ωs Ω = curveOf Ω Ωs := by
    show (Ωs ∪ Ω)ᶜ = (Ω ∪ Ωs)ᶜ
    rw [union_comm]
  have hne' : (curveOf Ωs Ω).Nonempty := by
    rw [hcs]
    exact hne
  have hdx : infDist x₀ Ωᶜ = infDist x₀ (curveOf Ω Ωs) :=
    s07d_p3_infDist_compl hΩo hΩso hdisj hne hx₀
  have hda : infDist a Ωsᶜ = infDist a (curveOf Ω Ωs) := by
    rw [← hcs]
    exact s07d_p3_infDist_compl hΩso hΩo hdisj.symm hne' ha
  have haΩ : a ∉ Ω := fun h => Set.disjoint_left.1 hdisj h ha
  have hax : a ≠ x₀ := fun h => haΩ (h ▸ hx₀)
  have hr0 : 0 < ‖a - x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hax)
  have hδ0 : 0 ≤ infDist a (curveOf Ω Ωs) := infDist_nonneg
  have hA : infDist x₀ (curveOf Ω Ωs) ≤ ‖a - x₀‖ := by
    rw [← hdx, ← dist_eq_norm, dist_comm]
    exact infDist_le_dist_of_mem haΩ
  obtain ⟨γ, hγ, hγd⟩ := hcpt.exists_infDist_eq_dist hne a
  obtain ⟨γ₀, hγ₀, hγ₀d⟩ := hcpt.exists_infDist_eq_dist hne x₀
  have hγΩ : γ ∉ Ω := fun h => hγ (Or.inl h)
  have hγs : γ ∉ Ωs := fun h => hγ (Or.inr h)
  have hγx : γ ≠ x₀ := fun h => hγΩ (h ▸ hx₀)
  have hγd₀ : infDist x₀ (curveOf Ω Ωs) ≤ ‖γ - x₀‖ := by
    rw [← dist_eq_norm, dist_comm]
    exact infDist_le_dist_of_mem hγ
  have e1 : ‖a - γ‖ = infDist a (curveOf Ω Ωs) := by rw [hγd, dist_eq_norm]
  have hmem : invAt x₀ γ ∈ (invPairΩs Ωs x₀)ᶜ := by
    rintro (⟨p, hp, hpe⟩ | h0)
    · have h' : (p - x₀)⁻¹ = (γ - x₀)⁻¹ := hpe
      rw [inv_inj, sub_left_inj] at h'
      exact hγs (h' ▸ hp)
    · have h' : (γ - x₀)⁻¹ = 0 := h0
      rw [inv_eq_zero, sub_eq_zero] at h'
      exact hγx h'
  refine ⟨hA, ?_, ?_, ?_, hda⟩
  · have h1 : ‖γ - γ₀‖ ≤ diam (curveOf Ω Ωs) := by
      rw [← dist_eq_norm]
      exact dist_le_diam_of_mem hcpt.isBounded hγ hγ₀
    have e2 : ‖γ₀ - x₀‖ = infDist x₀ (curveOf Ω Ωs) := by rw [hγ₀d, dist_eq_norm, norm_sub_rev]
    calc ‖a - x₀‖ = ‖(a - γ) + (γ - γ₀) + (γ₀ - x₀)‖ := by
          congr 1
          ring
      _ ≤ ‖a - γ‖ + ‖γ - γ₀‖ + ‖γ₀ - x₀‖ := norm_add₃_le
      _ ≤ _ := by
          rw [e1, e2]
          linarith
  · have h1 := infDist_le_dist_of_mem (x := invAt x₀ a) hmem
    rw [dist_eq_norm, s07d_p3_invAt_sub hax hγx, e1] at h1
    have hpos : 0 < ‖a - x₀‖ * ‖γ - x₀‖ := mul_pos hr0 (norm_pos_iff.2 (sub_ne_zero.2 hγx))
    have h2 : infDist (invAt x₀ a) (invPairΩs Ωs x₀)ᶜ * (‖a - x₀‖ * ‖γ - x₀‖) ≤
        infDist a (curveOf Ω Ωs) := by
      rw [← le_div_iff₀ hpos]
      exact h1
    have h3 : 0 ≤ infDist (invAt x₀ a) (invPairΩs Ωs x₀)ᶜ := infDist_nonneg
    calc infDist (invAt x₀ a) (invPairΩs Ωs x₀)ᶜ * (‖a - x₀‖ * infDist x₀ (curveOf Ω Ωs))
        ≤ infDist (invAt x₀ a) (invPairΩs Ωs x₀)ᶜ * (‖a - x₀‖ * ‖γ - x₀‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hγd₀ hr0.le) h3
      _ ≤ _ := h2
  · have hWne : ((invPairΩs Ωs x₀)ᶜ).Nonempty := ⟨invAt x₀ γ, hmem⟩
    have hle : infDist a (curveOf Ω Ωs) / (‖a - x₀‖ * (infDist a (curveOf Ω Ωs) + ‖a - x₀‖)) ≤
        infDist (invAt x₀ a) (invPairΩs Ωs x₀)ᶜ := by
      refine (le_infDist hWne).2 fun q hq => ?_
      have hq0 : q ≠ 0 := fun h => hq (Or.inr h)
      obtain ⟨p, hp⟩ : ∃ p : ℂ, p = x₀ + q⁻¹ := ⟨_, rfl⟩
      have hpq : invAt x₀ p = q := by
        rw [hp]
        show (x₀ + q⁻¹ - x₀)⁻¹ = q
        rw [add_sub_cancel_left, inv_inv]
      have hps : p ∉ Ωs := fun h => hq (Or.inl ⟨p, h, hpq⟩)
      have hpx : p ≠ x₀ := by
        intro h
        have h' : q⁻¹ = 0 := by
          rw [hp] at h
          linear_combination h
        exact hq0 (inv_eq_zero.1 h')
      have ht : infDist a (curveOf Ω Ωs) ≤ ‖a - p‖ := by
        rw [← hda, ← dist_eq_norm]
        exact infDist_le_dist_of_mem hps
      rw [← hpq, dist_eq_norm, s07d_p3_invAt_sub hax hpx]
      have hpx' : ‖p - x₀‖ ≤ ‖a - p‖ + ‖a - x₀‖ := by
        calc ‖p - x₀‖ = ‖(a - x₀) - (a - p)‖ := by
              congr 1
              ring
          _ ≤ ‖a - x₀‖ + ‖a - p‖ := norm_sub_le _ _
          _ = ‖a - p‖ + ‖a - x₀‖ := by ring
      have hp0 : 0 < ‖p - x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hpx)
      have hden : 0 < ‖a - x₀‖ * (infDist a (curveOf Ω Ωs) + ‖a - x₀‖) :=
        mul_pos hr0 (by linarith)
      rw [div_le_div_iff₀ hden (mul_pos hr0 hp0)]
      nlinarith [mul_le_mul_of_nonneg_left hpx' (mul_nonneg hδ0 hr0.le),
        mul_le_mul_of_nonneg_right ht (sq_nonneg ‖a - x₀‖)]
    have hden : 0 < ‖a - x₀‖ * (infDist a (curveOf Ω Ωs) + ‖a - x₀‖) := mul_pos hr0 (by linarith)
    exact (div_le_iff₀ hden).1 hle

/-- P3 helper (P3.3, converse; Schwarz–Pick for `ψ = 1/g⁻¹` on `B(a, r)`): for `g : 𝔻* → Ωs`
conformal, `a = g (jRefl z)`, `b = g (jRefl z')`, `B(a, r) ⊆ Ωs` and `|b - a| ≤ r/2`:
`d_𝔻(z, z') ≤ 3|b - a|/r`. -/
theorem s07d_p3_ext_small {Ωs : Set ℂ} {g : ℂ → ℂ} (hg : IsConformalOnto g unitDiscExterior Ωs)
    {z z' : ℂ} (hz : z ∈ unitDisc) (hz' : z' ∈ unitDisc) (hz0 : z ≠ 0) (hz0' : z' ≠ 0) {r : ℝ}
    (hr : 0 < r) (hB : ball (g (jRefl z)) r ⊆ Ωs)
    (hab : ‖g (jRefl z') - g (jRefl z)‖ ≤ r / 2) :
    diskDist z z' ≤ 3 * (‖g (jRefl z') - g (jRefl z)‖ / r) := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hψ := hg.symm hEo
  have hgm : ∀ v ∈ Ωs, Function.invFunOn g unitDiscExterior v ∈ unitDiscExterior := fun v hv => by
    have h1 := mem_image_of_mem (Function.invFunOn g unitDiscExterior) hv
    rwa [hψ.2.2] at h1
  have hl : ∀ w ∈ unitDiscExterior, Function.invFunOn g unitDiscExterior (g w) = w := fun w hw =>
    hg.2.1.leftInvOn_invFunOn hw
  have hψd := hψ.1
  generalize Function.invFunOn g unitDiscExterior = ψ at hgm hl hψd
  have hb : g (jRefl z') ∈ ball (g (jRefl z)) r := by
    rw [mem_ball, dist_eq_norm]
    linarith
  have hψa : ψ (g (jRefl z)) = jRefl z := hl _ (s07d_p3_jRefl_int hz hz0)
  have hψb : ψ (g (jRefl z')) = jRefl z' := hl _ (s07d_p3_jRefl_int hz' hz0')
  have hc1 : ‖conj z‖ < 1 := by
    rw [Complex.norm_conj]
    exact mem_ball_zero_iff.mp hz
  have hinv : ∀ w : ℂ, (jRefl w)⁻¹ = conj w := fun w => by
    show ((conj w)⁻¹)⁻¹ = conj w
    rw [inv_inv]
  have hkD : ∀ x ∈ ball (g (jRefl z)) r, ‖(ψ x)⁻¹‖ < 1 := fun x hx => by
    have h1 : 1 < ‖ψ x‖ := hgm x (hB hx)
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ h1
  have hkd : DifferentiableOn ℂ (fun x => (ψ x)⁻¹) (ball (g (jRefl z)) r) := fun x hx => by
    have h1 : 1 < ‖ψ x‖ := hgm x (hB hx)
    have hne : ψ x ≠ 0 := norm_pos_iff.1 (by linarith)
    exact ((hψd.mono hB) x hx).inv hne
  have hhd : DifferentiableOn ℂ (fun x => blaschke (conj z) ((ψ x)⁻¹)) (ball (g (jRefl z)) r) :=
    (differentiableOn_blaschke hc1).comp hkd fun x hx => mem_ball_zero_iff.mpr (hkD x hx)
  have haa : blaschke (conj z) ((ψ (g (jRefl z)))⁻¹) = 0 := by
    rw [hψa, hinv]
    show (conj z - conj z) / (1 - conj (conj z) * conj z) = 0
    rw [sub_self, zero_div]
  have hhm : MapsTo (fun x => blaschke (conj z) ((ψ x)⁻¹)) (ball (g (jRefl z)) r)
      (closedBall ((fun x => blaschke (conj z) ((ψ x)⁻¹)) (g (jRefl z))) 1) := by
    intro x hx
    show blaschke (conj z) ((ψ x)⁻¹) ∈ closedBall (blaschke (conj z) ((ψ (g (jRefl z)))⁻¹)) 1
    rw [haa, mem_closedBall, dist_zero_right]
    exact (blaschke_mem_unitDisc hc1 (hkD x hx)).le
  have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hhd hhm hb
  have hβ : ‖blaschke (conj z) (conj z')‖ ≤ ‖g (jRefl z') - g (jRefl z)‖ / r := by
    have e : blaschke (conj z) ((ψ (g (jRefl z')))⁻¹) = blaschke (conj z) (conj z') := by
      rw [hψb, hinv]
    rw [e, haa, dist_zero_right, dist_eq_norm, div_mul_eq_mul_div, one_mul] at hsch
    exact hsch
  have hu : conj z ∈ unitDisc := mem_ball_zero_iff.mpr hc1
  have hv : conj z' ∈ unitDisc := mem_ball_zero_iff.mpr (by
    rw [Complex.norm_conj]
    exact mem_ball_zero_iff.mp hz')
  rw [← s07d_p3_dd_conj, s07d_p3_dd_blaschke hu hv, s07d_p3_dd0_eq]
  exact s03_dd_arcosh (norm_nonneg _) hβ (by rw [div_le_iff₀ hr]; linarith)

/-- P3.3 (Koebe, outside, on the collar): for a bounded `K`-quasicircle and `g : 𝔻* → Ωs` conformal
with `g(∞) = ∞`, write `G z = g (jRefl z)` for `z ∈ 𝔻 ∖ {0}`. If `d(G z, Γ) ≤ diam Γ`, then the two
Koebe comparisons of P3.2 hold for `G` with `d(·, Γ)` (constants depending only on `K`, `D`). -/
theorem s07d_p3_koebe_ext (K D : ℝ) (hK : 1 ≤ K) (hD : 0 ≤ D) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Ω Ωs : Set ℂ) (g : ℂ → ℂ), IsBoundedKQuasicircle Ω Ωs K →
      IsConformalOnto g unitDiscExterior Ωs → Tendsto g (cocompact ℂ) (cocompact ℂ) →
      ∀ z ∈ unitDisc, ∀ z' ∈ unitDisc, z ≠ 0 → z' ≠ 0 →
        infDist (g (jRefl z)) (curveOf Ω Ωs) ≤ diam (curveOf Ω Ωs) →
        infDist (g (jRefl z')) (curveOf Ω Ωs) ≤ diam (curveOf Ω Ωs) →
        (diskDist z z' ≤ D →
          ‖g (jRefl z) - g (jRefl z')‖ ≤ C * diskDist z z' * infDist (g (jRefl z)) (curveOf Ω Ωs) ∧
            infDist (g (jRefl z)) (curveOf Ω Ωs) ≤ C * infDist (g (jRefl z')) (curveOf Ω Ωs)) ∧
        (‖g (jRefl z) - g (jRefl z')‖ ≤ infDist (g (jRefl z)) (curveOf Ω Ωs) / 2 →
          diskDist z z' * infDist (g (jRefl z)) (curveOf Ω Ωs) ≤
            C * ‖g (jRefl z) - g (jRefl z')‖) := by
  -- Route: invert at the deep point `x₀ = F₀ 0` (`s07d_p3_deep`); `f̃ = outerPt g x₀ ∘ conj` is
  -- conformal onto `W = invPairΩs Ωs x₀` (`s07_outer_conformal`), and P3.2 for `f̃` transfers via
  -- `s07d_p3_inv_dist` (all of `|a - x₀|`, `d₀`, `diam Γ` comparable on the collar). The converse is
  -- Schwarz–Pick on `B(a, d(a, Γ)) ⊆ Ωs` (`s07d_p3_ext_small`).
  obtain ⟨C₁, hC₁, hKi⟩ := s07d_p3_koebe_int D hD
  obtain ⟨C₄, hC₄, hdeep⟩ := s07d_p3_deep K hK
  have hC₁0 : 0 ≤ C₁ := by linarith
  have hC₄0 : 0 ≤ C₄ := by linarith
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = 2 * C₄ + 1 := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by linarith
  have hP : 0 ≤ C₁ * M * (M + C₄) := mul_nonneg (mul_nonneg hC₁0 (by linarith)) (by linarith)
  have hCM : C₁ * M ≤ C₁ * M * (M + C₄) + 3 := by
    have h1 : C₁ * M * 1 ≤ C₁ * M * (M + C₄) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC₁0 (by linarith))
    linarith
  refine ⟨C₁ * M * (M + C₄) + 3, by linarith, ?_⟩
  intro Ω Ωs g hq hg hgInf z hz z' hz' hz0 hz0' hca hcb
  obtain ⟨F₀, hF₀q, hF₀s, hF₀D, hF₀E⟩ := id hq
  have hi : Function.Injective F₀ := injOn_univ.mp hF₀q.2.2.1.2.1
  have hc : Continuous F₀ := continuousOn_univ.mp hF₀q.2.2.1.1
  obtain ⟨T, hT⟩ := t1_homeomorph hF₀q hF₀s
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hΩo : IsOpen Ω := by
    rw [← hF₀D, ← hT]
    exact T.isOpenMap _ isOpen_ball
  have hΩso : IsOpen Ωs := by
    rw [← hF₀E, ← hT]
    exact T.isOpenMap _ hEo
  have hdisj : Disjoint Ω Ωs := by
    rw [← hF₀D, ← hF₀E, disjoint_image_iff hi]
    refine Set.disjoint_left.2 fun x h1 h2 => ?_
    have h1' : ‖x‖ < 1 := mem_ball_zero_iff.mp h1
    have h2' : 1 < ‖x‖ := h2
    linarith
  have hΓe := s03_cb_curve hi hF₀s hF₀D hF₀E
  have hcpt : IsCompact (curveOf Ω Ωs) := by
    rw [hΓe]
    exact s07d_p3_circle_compact.image hc
  have hne : (curveOf Ω Ωs).Nonempty := by
    rw [hΓe]
    exact ⟨F₀ 1, 1, by simp, rfl⟩
  have hx₀ : F₀ 0 ∈ Ω := by
    rw [← hF₀D]
    exact mem_image_of_mem F₀ (mem_ball_self one_pos)
  have hx₀s : F₀ 0 ∉ Ωs := fun h => Set.disjoint_left.1 hdisj hx₀ h
  have hΔ := hdeep Ω Ωs F₀ hF₀q hF₀s hF₀D hF₀E
  have hd₀ : 0 < infDist (F₀ 0) (curveOf Ω Ωs) :=
    (hcpt.isClosed.notMem_iff_infDist_pos hne).1 fun h => h (Or.inl hx₀)
  have hf := s07_outer_conformal hg hgInf hx₀s
  have ha : g (jRefl z) ∈ Ωs := by
    rw [← hg.2.2]
    exact mem_image_of_mem g (s07d_p3_jRefl_int hz hz0)
  have hb : g (jRefl z') ∈ Ωs := by
    rw [← hg.2.2]
    exact mem_image_of_mem g (s07d_p3_jRefl_int hz' hz0')
  have hax : g (jRefl z) ≠ F₀ 0 := fun h => hx₀s (h ▸ ha)
  have hbx : g (jRefl z') ≠ F₀ 0 := fun h => hx₀s (h ▸ hb)
  obtain ⟨hA1, hA2, hA3, hA4, hA5⟩ := s07d_p3_inv_dist hΩo hΩso hdisj hcpt hne hx₀ ha
  obtain ⟨hB1, hB2, hB3, hB4, -⟩ := s07d_p3_inv_dist hΩo hΩso hdisj hcpt hne hx₀ hb
  have hu : conj z ∈ unitDisc := mem_ball_zero_iff.mpr (by
    rw [Complex.norm_conj]
    exact mem_ball_zero_iff.mp hz)
  have hv : conj z' ∈ unitDisc := mem_ball_zero_iff.mpr (by
    rw [Complex.norm_conj]
    exact mem_ball_zero_iff.mp hz')
  have hfu : outerPt g (F₀ 0) (conj (conj z)) = invAt (F₀ 0) (g (jRefl z)) :=
    s07_outerPt_conj ((map_ne_zero _).2 hz0)
  have hfv : outerPt g (F₀ 0) (conj (conj z')) = invAt (F₀ 0) (g (jRefl z')) :=
    s07_outerPt_conj ((map_ne_zero _).2 hz0')
  obtain ⟨hK1, -⟩ := hKi _ _ hf (conj z) hu (conj z') hv
  rw [hfu, hfv, s07d_p3_dd_conj] at hK1
  -- abbreviations
  have hdd0 : 0 ≤ diskDist z z' := s02_diskDist_nonneg hz hz'
  have hδa0 : 0 ≤ infDist (g (jRefl z)) (curveOf Ω Ωs) := infDist_nonneg
  have hδb0 : 0 ≤ infDist (g (jRefl z')) (curveOf Ω Ωs) := infDist_nonneg
  have hdA0 : 0 ≤ infDist (invAt (F₀ 0) (g (jRefl z))) (invPairΩs Ωs (F₀ 0))ᶜ := infDist_nonneg
  have hdB0 : 0 ≤ infDist (invAt (F₀ 0) (g (jRefl z'))) (invPairΩs Ωs (F₀ 0))ᶜ := infDist_nonneg
  have hra : 0 < ‖g (jRefl z) - F₀ 0‖ := hd₀.trans_le hA1
  have hrb : 0 < ‖g (jRefl z') - F₀ 0‖ := hd₀.trans_le hB1
  have hraM : ‖g (jRefl z) - F₀ 0‖ ≤ M * infDist (F₀ 0) (curveOf Ω Ωs) := by
    rw [hMdef]
    linarith
  have hrbM : ‖g (jRefl z') - F₀ 0‖ ≤ M * infDist (F₀ 0) (curveOf Ω Ωs) := by
    rw [hMdef]
    linarith
  refine ⟨fun hdD => ⟨?_, ?_⟩, fun hsm => ?_⟩
  · obtain ⟨k1, -⟩ := hK1 hdD
    rw [s07d_p3_invAt_sub hax hbx, div_le_iff₀ (mul_pos hra hrb)] at k1
    have e2 : ‖g (jRefl z) - g (jRefl z')‖ * infDist (F₀ 0) (curveOf Ω Ωs) ≤
        C₁ * M * diskDist z z' * infDist (g (jRefl z)) (curveOf Ω Ωs) *
          infDist (F₀ 0) (curveOf Ω Ωs) := by
      calc ‖g (jRefl z) - g (jRefl z')‖ * infDist (F₀ 0) (curveOf Ω Ωs)
          ≤ C₁ * diskDist z z' * infDist (invAt (F₀ 0) (g (jRefl z))) (invPairΩs Ωs (F₀ 0))ᶜ *
              (‖g (jRefl z) - F₀ 0‖ * ‖g (jRefl z') - F₀ 0‖) * infDist (F₀ 0) (curveOf Ω Ωs) :=
            mul_le_mul_of_nonneg_right k1 hd₀.le
        _ = C₁ * diskDist z z' * ‖g (jRefl z') - F₀ 0‖ *
              (infDist (invAt (F₀ 0) (g (jRefl z))) (invPairΩs Ωs (F₀ 0))ᶜ *
                (‖g (jRefl z) - F₀ 0‖ * infDist (F₀ 0) (curveOf Ω Ωs))) := by ring
        _ ≤ C₁ * diskDist z z' * ‖g (jRefl z') - F₀ 0‖ *
              infDist (g (jRefl z)) (curveOf Ω Ωs) :=
            mul_le_mul_of_nonneg_left hA3 (mul_nonneg (mul_nonneg hC₁0 hdd0) hrb.le)
        _ ≤ C₁ * diskDist z z' * (M * infDist (F₀ 0) (curveOf Ω Ωs)) *
              infDist (g (jRefl z)) (curveOf Ω Ωs) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hrbM (mul_nonneg hC₁0 hdd0)) hδa0
        _ = C₁ * M * diskDist z z' * infDist (g (jRefl z)) (curveOf Ω Ωs) *
              infDist (F₀ 0) (curveOf Ω Ωs) := by ring
    have e3 := le_of_mul_le_mul_right e2 hd₀
    calc ‖g (jRefl z) - g (jRefl z')‖
        ≤ C₁ * M * diskDist z z' * infDist (g (jRefl z)) (curveOf Ω Ωs) := e3
      _ ≤ (C₁ * M * (M + C₄) + 3) * diskDist z z' * infDist (g (jRefl z)) (curveOf Ω Ωs) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCM hdd0) hδa0
  · obtain ⟨-, k2⟩ := hK1 hdD
    have hsum : infDist (g (jRefl z)) (curveOf Ω Ωs) + ‖g (jRefl z) - F₀ 0‖ ≤
        (C₄ + M) * infDist (F₀ 0) (curveOf Ω Ωs) := by
      rw [hMdef]
      linarith
    have hdBd : infDist (invAt (F₀ 0) (g (jRefl z'))) (invPairΩs Ωs (F₀ 0))ᶜ *
        (infDist (F₀ 0) (curveOf Ω Ωs) * infDist (F₀ 0) (curveOf Ω Ωs)) ≤
        infDist (g (jRefl z')) (curveOf Ω Ωs) :=
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hB1 hd₀.le) hdB0).trans hB3
    have hMd : 0 ≤ M * infDist (F₀ 0) (curveOf Ω Ωs) := mul_nonneg (by linarith) hd₀.le
    calc infDist (g (jRefl z)) (curveOf Ω Ωs)
        ≤ infDist (invAt (F₀ 0) (g (jRefl z))) (invPairΩs Ωs (F₀ 0))ᶜ *
            (‖g (jRefl z) - F₀ 0‖ *
              (infDist (g (jRefl z)) (curveOf Ω Ωs) + ‖g (jRefl z) - F₀ 0‖)) := hA4
      _ ≤ (C₁ * infDist (invAt (F₀ 0) (g (jRefl z'))) (invPairΩs Ωs (F₀ 0))ᶜ) *
            ((M * infDist (F₀ 0) (curveOf Ω Ωs)) *
              ((C₄ + M) * infDist (F₀ 0) (curveOf Ω Ωs))) :=
          mul_le_mul k2 (mul_le_mul hraM hsum (by linarith) hMd)
            (mul_nonneg hra.le (by linarith)) (mul_nonneg hC₁0 hdB0)
      _ = C₁ * M * (C₄ + M) * (infDist (invAt (F₀ 0) (g (jRefl z'))) (invPairΩs Ωs (F₀ 0))ᶜ *
            (infDist (F₀ 0) (curveOf Ω Ωs) * infDist (F₀ 0) (curveOf Ω Ωs))) := by ring
      _ ≤ C₁ * M * (C₄ + M) * infDist (g (jRefl z')) (curveOf Ω Ωs) :=
          mul_le_mul_of_nonneg_left hdBd
            (mul_nonneg (mul_nonneg hC₁0 (by linarith)) (by linarith))
      _ ≤ (C₁ * M * (M + C₄) + 3) * infDist (g (jRefl z')) (curveOf Ω Ωs) := by
          rw [add_comm C₄ M]
          exact mul_le_mul_of_nonneg_right (by linarith) hδb0
  · have hδa : 0 < infDist (g (jRefl z)) (curveOf Ω Ωs) :=
      (hcpt.isClosed.notMem_iff_infDist_pos hne).1 fun h => h (Or.inr ha)
    have hB : ball (g (jRefl z)) (infDist (g (jRefl z)) (curveOf Ω Ωs)) ⊆ Ωs := by
      intro y hy
      by_contra hyc
      have h1 := infDist_le_dist_of_mem (x := g (jRefl z)) (show y ∈ Ωsᶜ from hyc)
      rw [hA5, dist_comm] at h1
      rw [mem_ball] at hy
      linarith
    have hsm' : ‖g (jRefl z') - g (jRefl z)‖ ≤ infDist (g (jRefl z)) (curveOf Ω Ωs) / 2 := by
      rw [norm_sub_rev]
      exact hsm
    have h1 := s07d_p3_ext_small hg hz hz' hz0 hz0' hδa hB hsm'
    rw [norm_sub_rev] at h1
    have h2 := mul_le_mul_of_nonneg_right h1 hδa.le
    rw [mul_assoc, div_mul_cancel₀ _ hδa.ne'] at h2
    calc diskDist z z' * infDist (g (jRefl z)) (curveOf Ω Ωs)
        ≤ 3 * ‖g (jRefl z) - g (jRefl z')‖ := h2
      _ ≤ (C₁ * M * (M + C₄) + 3) * ‖g (jRefl z) - g (jRefl z')‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

/-- P3.4 (the q.c. reflection, `lem_three_point`): for a `K`-q.c. homeomorphism `E` of `ℂ` with
`E(𝔻) = Ω`, `E(𝔻*) = Ωs` and `u ∈ 𝔻 ∖ {0}`:
* `|E u - E (jRefl u)| ≤ C d(E (jRefl u), Γ)`;
* `|E u - E (jRefl u)| ≤ C d(E u, Γ)` when `|u| ≥ 1/2`;
* `diam Γ ≤ C d(E u, Γ)` when `|u| ≤ 1/2`. -/
theorem s07d_p3_qc_refl (K : ℝ) (hK : 1 ≤ K) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Ω Ωs : Set ℂ) (E : ℂ → ℂ), IsKQC E univ K → E '' univ = univ → E '' unitDisc = Ω →
      E '' unitDiscExterior = Ωs → ∀ u ∈ unitDisc,
        (u ≠ 0 → ‖E u - E (jRefl u)‖ ≤ C * infDist (E (jRefl u)) (curveOf Ω Ωs)) ∧
        (1 / 2 ≤ ‖u‖ → ‖E u - E (jRefl u)‖ ≤ C * infDist (E u) (curveOf Ω Ωs)) ∧
        (‖u‖ ≤ 1 / 2 → diam (curveOf Ω Ωs) ≤ C * infDist (E u) (curveOf Ω Ωs)) := by
  obtain ⟨C₀, hC₀, htp₀⟩ := lem_three_point K hK
  have h23 : (2 : ℝ) ^ K ≤ (3 : ℝ) ^ K := Real.rpow_le_rpow (by norm_num) (by norm_num) (by linarith)
  have h3 : 0 < (3 : ℝ) ^ K := by positivity
  refine ⟨2 * C₀ * (3 : ℝ) ^ K + 1, by nlinarith [mul_pos hC₀ h3], ?_⟩
  intro Ω Ωs E hE hs hD hX u hu
  have hc : Continuous E := continuousOn_univ.mp hE.2.2.1.1
  have hi : Function.Injective E := injOn_univ.mp hE.2.2.1.2.1
  have htp := fun a b c (hac : a ≠ c) => (htp₀ E hE hs a b c hac).1
  rw [s03_cb_curve hi hs hD hX]
  have hcomp : IsCompact (E '' {z : ℂ | ‖z‖ = 1}) := s07d_p3_circle_compact.image hc
  have hne : (E '' {z : ℂ | ‖z‖ = 1}).Nonempty := ⟨E 1, 1, by simp, rfl⟩
  -- nearest point of `Γ = E(∂𝔻)`
  have hnear : ∀ x : ℂ, ∃ y : ℂ, ‖y‖ = 1 ∧
      infDist x (E '' {z : ℂ | ‖z‖ = 1}) = ‖x - E y‖ := by
    intro x
    obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := hcomp.exists_infDist_eq_dist hne x
    exact ⟨y, hy, by rw [hxy, dist_eq_norm]⟩
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  have hCa : C₀ * (2 : ℝ) ^ K ≤ 2 * C₀ * (3 : ℝ) ^ K + 1 := by nlinarith [mul_pos hC₀ h3]
  have hCb : C₀ * (3 : ℝ) ^ K ≤ 2 * C₀ * (3 : ℝ) ^ K + 1 := by nlinarith [mul_pos hC₀ h3]
  refine ⟨fun hu0 => ?_, fun hu2 => ?_, fun hu2 => ?_⟩
  · -- center `jRefl u`, ratio `1 + |u| ≤ 2`
    have hn : 0 < ‖u‖ := norm_pos_iff.2 hu0
    obtain ⟨y, hy, hdy⟩ := hnear (E (jRefl u))
    have hjn := s07d_p3_jRefl_norm u
    have hjy : ‖jRefl u‖ - 1 ≤ ‖jRefl u - y‖ := by
      have := norm_sub_norm_le (jRefl u) y; rwa [hy] at this
    have hinv : 1 < ‖u‖⁻¹ := one_lt_inv₀ hn |>.2 hu1
    have hay : jRefl u ≠ y := fun h => by rw [h, hy] at hjn; linarith
    have hsub := s07d_p3_jRefl_sub hu0 hu1.le
    have hle : ‖jRefl u - u‖ ≤ 2 * ‖jRefl u - y‖ := by
      rw [norm_sub_rev, hsub]
      rw [hjn] at hjy
      have : (1 - ‖u‖ ^ 2) / ‖u‖ = (1 + ‖u‖) * (‖u‖⁻¹ - 1) := by field_simp; ring
      rw [this]
      nlinarith
    have h := s07d_p3_tp_apply hK (by norm_num) hi htp hC₀ hay hle
    rw [norm_sub_rev, hdy]
    calc ‖E (jRefl u) - E u‖ ≤ C₀ * (2 : ℝ) ^ K * ‖E (jRefl u) - E y‖ := h
      _ ≤ _ := mul_le_mul_of_nonneg_right hCa (norm_nonneg _)
  · -- center `u`, ratio `(1 + |u|)/|u| ≤ 3`
    have hn : 0 < ‖u‖ := by linarith
    have hu0 : u ≠ 0 := norm_pos_iff.1 hn
    obtain ⟨y, hy, hdy⟩ := hnear (E u)
    have huy : 1 - ‖u‖ ≤ ‖u - y‖ := by
      have := norm_sub_norm_le y u; rw [hy, norm_sub_rev] at this; exact this
    have hay : u ≠ y := fun h => by rw [h, hy] at hu1; linarith
    have hsub := s07d_p3_jRefl_sub hu0 hu1.le
    have hle : ‖u - jRefl u‖ ≤ 3 * ‖u - y‖ := by
      rw [hsub, div_le_iff₀ hn]
      nlinarith
    have h := s07d_p3_tp_apply hK (by norm_num) hi htp hC₀ hay hle
    rw [hdy]
    calc ‖E u - E (jRefl u)‖ ≤ C₀ * (3 : ℝ) ^ K * ‖E u - E y‖ := h
      _ ≤ _ := mul_le_mul_of_nonneg_right hCb (norm_nonneg _)
  · -- `|u| ≤ 1/2`: every boundary point is within `C₀ 3^K d` of `E u`
    obtain ⟨y, hy, hdy⟩ := hnear (E u)
    have huy : 1 / 2 ≤ ‖u - y‖ := by
      have := norm_sub_norm_le y u; rw [hy, norm_sub_rev] at this; linarith
    have hay : u ≠ y := fun h => by rw [h, hy] at hu2; linarith
    have hfar : ∀ z : ℂ, ‖z‖ = 1 → ‖E u - E z‖ ≤ C₀ * (3 : ℝ) ^ K * ‖E u - E y‖ := by
      intro z hz
      have hle : ‖u - z‖ ≤ 3 * ‖u - y‖ := by
        have := norm_sub_le u z; rw [hz] at this
        have : ‖u - z‖ ≤ ‖u‖ + 1 := by
          calc ‖u - z‖ ≤ ‖u‖ + ‖z‖ := norm_sub_le u z
            _ = ‖u‖ + 1 := by rw [hz]
        linarith
      exact s07d_p3_tp_apply hK (by norm_num) hi htp hC₀ hay hle
    rw [hdy]
    refine diam_le_of_forall_dist_le (by positivity) ?_
    rintro _ ⟨z₁, hz₁, rfl⟩ _ ⟨z₂, hz₂, rfl⟩
    rw [dist_eq_norm]
    have e1 := hfar z₁ hz₁
    have e2 := hfar z₂ hz₂
    calc ‖E z₁ - E z₂‖ ≤ ‖E u - E z₁‖ + ‖E u - E z₂‖ := by
          rw [norm_sub_rev (E u) (E z₁)]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * (C₀ * (3 : ℝ) ^ K * ‖E u - E y‖) := by linarith
      _ ≤ (2 * C₀ * (3 : ℝ) ^ K + 1) * ‖E u - E y‖ := by nlinarith [norm_nonneg (E u - E y)]

/-- P3.5 (core: displacement of Ahlfors' reflection). Take a bounded `K`-quasicircle with welding
`f, g, h` and any closed-disk homeomorphism `F` that is `L₀`-bi-Lipschitz for `d_𝔻` with `F = h` on
`∂𝔻` (e.g. `F = E(h)` from `thm_DE`). For `z ∈ 𝔻 ∖ {0}`, put `a = g (jRefl z) ∈ Ωs` and
`μ a = f (F z)`. Then:
* `|μ a - a| ≤ C d(a, Γ)`;
* `min(d(a, Γ), diam Γ) ≤ C d(μ a, Γ)`;
* `diam Γ ≤ C d(f (F 0), Γ)`, i.e. the point sent to `∞` is deep. -/
theorem s07d_p3_displacement (K L₀ : ℝ) (hK : 1 ≤ K) (hL₀ : 1 ≤ L₀) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Ω Ωs : Set ℂ) (f g h F : ℂ → ℂ), IsBoundedKQuasicircle Ω Ωs K →
      IsDiskWelding Ω Ωs f g h → IsClosedDiskHomeo F → EqOn F h (sphere (0 : ℂ) 1) →
      IsDiskBiLip F L₀ →
        (∀ z ∈ unitDisc, z ≠ 0 →
          ‖f (F z) - g (jRefl z)‖ ≤ C * infDist (g (jRefl z)) (curveOf Ω Ωs) ∧
            min (infDist (g (jRefl z)) (curveOf Ω Ωs)) (diam (curveOf Ω Ωs)) ≤
              C * infDist (f (F z)) (curveOf Ω Ωs)) ∧
        diam (curveOf Ω Ωs) ≤ C * infDist (f (F 0)) (curveOf Ω Ωs) := by
  -- `hL₀` is not needed: `s07_sb_maps` already gives `1 ≤ L₀` from `IsDiskBiLip F L₀`, so the
  -- statement stays true without it.
  have _hL₀ := hL₀
  obtain ⟨C₄, hC₄, hR⟩ := s07d_p3_qc_refl K hK
  have hKK : 1 ≤ K * K := by nlinarith
  obtain ⟨LA, cA, -, -, hQI⟩ := s07d_p3_qc_qi (K * K) hKK
  set D := max (L₀ * morseD (L₀ * LA) (L₀ * cA)) 0 with hDdef
  have hD0 : 0 ≤ D := le_max_right _ _
  obtain ⟨C₂, hC₂, hKo⟩ := s07d_p3_koebe_int D hD0
  have hC₂D : 0 ≤ C₂ * D := mul_nonneg (by linarith) hD0
  refine ⟨(C₂ * D + C₂ + 1) * (C₄ + 1) + 1, by nlinarith, ?_⟩
  intro Ω Ωs f g h F hΓ hw hF hFh hFL
  obtain ⟨E, hEq, hEs, hE1, hE2⟩ := id hΓ
  have hf := hw.1
  have hg := hw.2.1
  have hgInf := hw.2.2.1
  obtain ⟨P, hPq, hPs, hP0, hPF⟩ := s07_weld_inner hEq hEs hE2 hg hgInf
  obtain ⟨hA0q, hA0s, hA0b⟩ := s07d_p3_A0 hΓ hw hEq hEs hE1 hPq hPs hP0 hPF
  set A₀ := Function.invFunOn f unitDisc ∘ (E ∘ P) with hA0def
  have hA0QI := hQI A₀ hA0q hA0s
  have hbd : HasDiskBoundaryValues A₀ F := fun ζ hζ => by rw [hFh hζ]; exact hA0b ζ hζ
  have hsame := lem_same_boundary A₀ F LA cA L₀ hA0QI hF hFL hbd
  have hDz : ∀ z ∈ unitDisc, diskDist (A₀ z) (F z) ≤ D := fun z hz =>
    (hsame z hz).trans (le_max_left _ _)
  obtain ⟨hFmaps, -⟩ := s07_sb_maps hF hFL
  have hA0maps : MapsTo A₀ unitDisc unitDisc := fun z hz => hA0s ▸ mem_image_of_mem A₀ hz
  have hPmem : ∀ z ∈ unitDisc, P z ∈ unitDisc := fun z hz => hPs ▸ mem_image_of_mem P hz
  have hfA0 : ∀ z ∈ unitDisc, f (A₀ z) = E (P z) := fun z hz => by
    have hm : E (P z) ∈ f '' unitDisc := by
      rw [hf.2.2, ← hE1]; exact mem_image_of_mem E (hPmem z hz)
    exact Function.invFunOn_eq hm
  -- the curve and the two sides
  have hi : Function.Injective E := injOn_univ.mp hEq.2.2.1.2.1
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hΩso : IsOpen Ωs := hg.isOpen (isOpen_lt continuous_const continuous_norm)
  have hdisj : Disjoint Ω Ωs := by
    rw [← hE1, ← hE2]
    refine (Set.disjoint_image_iff hi).2 ?_
    refine Set.disjoint_left.2 fun z hz1 hz2 => ?_
    have h1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz1
    have h2 : 1 < ‖z‖ := hz2
    linarith
  have hne : (curveOf Ω Ωs).Nonempty := by
    rw [s03_cb_curve hi hEs hE1 hE2]; exact ⟨E 1, 1, by simp, rfl⟩
  have hdΩ : ∀ w ∈ Ω, infDist w Ωᶜ = infDist w (curveOf Ω Ωs) := fun w hw' =>
    s07d_p3_infDist_compl hΩo hΩso hdisj hne hw'
  -- Koebe at `A₀ z` and `F z` (bounded hyperbolic distance)
  have hK1 : ∀ z ∈ unitDisc,
      ‖f (A₀ z) - f (F z)‖ ≤ C₂ * D * infDist (f (A₀ z)) (curveOf Ω Ωs) ∧
        infDist (f (A₀ z)) (curveOf Ω Ωs) ≤ C₂ * infDist (f (F z)) (curveOf Ω Ωs) := by
    intro z hz
    have hu := hA0maps hz
    have hv := hFmaps hz
    obtain ⟨h1, h2⟩ := (hKo Ω f hf (A₀ z) hu (F z) hv).1 (hDz z hz)
    have hfu : f (A₀ z) ∈ Ω := hf.2.2 ▸ mem_image_of_mem f hu
    have hfv : f (F z) ∈ Ω := hf.2.2 ▸ mem_image_of_mem f hv
    rw [hdΩ _ hfu] at h1 h2
    rw [hdΩ _ hfv] at h2
    refine ⟨h1.trans ?_, h2⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hDz z hz) (by linarith))
      infDist_nonneg
  have hlip : ∀ x y : ℂ, infDist x (curveOf Ω Ωs) ≤ infDist y (curveOf Ω Ωs) + ‖x - y‖ :=
    fun x y => by
      have := infDist_le_infDist_add_dist (x := x) (y := y) (s := curveOf Ω Ωs)
      rwa [dist_eq_norm] at this
  have hC₄0 : 0 ≤ C₄ := by linarith
  refine ⟨fun z hz hz0 => ?_, ?_⟩
  · have hPz := hPmem z hz
    have hPz0 : P z ≠ 0 := fun h0 =>
      hz0 (hPq.2.2.1.2.1 hz (mem_ball_self one_pos) (h0.trans hP0.symm))
    have ha : g (jRefl z) = E (jRefl (P z)) := (hPF z hz hz0).symm
    obtain ⟨hk1, hk2⟩ := hK1 z hz
    rw [hfA0 z hz] at hk1 hk2
    obtain ⟨r1, r2, r3⟩ := hR Ω Ωs E hEq hEs hE1 hE2 (P z) hPz
    rw [ha]
    set a := E (jRefl (P z)) with hadef
    set Ru := E (P z) with hRudef
    set μ := f (F z) with hμdef
    set da := infDist a (curveOf Ω Ωs)
    set dR := infDist Ru (curveOf Ω Ωs)
    set dμ := infDist μ (curveOf Ω Ωs)
    have hda0 : 0 ≤ da := infDist_nonneg
    have hdR0 : 0 ≤ dR := infDist_nonneg
    have hdμ0 : 0 ≤ dμ := infDist_nonneg
    have r1' : ‖Ru - a‖ ≤ C₄ * da := r1 hPz0
    have hRa : dR ≤ (C₄ + 1) * da := by
      have := hlip Ru a; nlinarith
    constructor
    · have e1 : ‖Ru - μ‖ ≤ C₂ * D * ((C₄ + 1) * da) :=
        hk1.trans (mul_le_mul_of_nonneg_left hRa hC₂D)
      calc ‖μ - a‖ ≤ ‖μ - Ru‖ + ‖Ru - a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ = ‖Ru - μ‖ + ‖Ru - a‖ := by rw [norm_sub_rev μ Ru]
        _ ≤ C₂ * D * ((C₄ + 1) * da) + C₄ * da := add_le_add e1 r1'
        _ ≤ ((C₂ * D + C₂ + 1) * (C₄ + 1) + 1) * da := by nlinarith
    · by_cases hu2 : 1 / 2 ≤ ‖P z‖
      · have h2 : ‖Ru - a‖ ≤ C₄ * dR := r2 hu2
        have h3 : da ≤ (C₄ + 1) * dR := by
          have := hlip a Ru; rw [norm_sub_rev] at this; nlinarith
        have h4 : da ≤ (C₄ + 1) * C₂ * dμ := by
          calc da ≤ (C₄ + 1) * dR := h3
            _ ≤ (C₄ + 1) * (C₂ * dμ) := mul_le_mul_of_nonneg_left hk2 (by linarith)
            _ = (C₄ + 1) * C₂ * dμ := by ring
        calc min da (diam (curveOf Ω Ωs)) ≤ da := min_le_left _ _
          _ ≤ (C₄ + 1) * C₂ * dμ := h4
          _ ≤ ((C₂ * D + C₂ + 1) * (C₄ + 1) + 1) * dμ := by
              apply mul_le_mul_of_nonneg_right _ hdμ0; nlinarith
      · have hu2' : ‖P z‖ ≤ 1 / 2 := (lt_of_not_ge hu2).le
        have h2 : diam (curveOf Ω Ωs) ≤ C₄ * dR := r3 hu2'
        calc min da (diam (curveOf Ω Ωs)) ≤ diam (curveOf Ω Ωs) := min_le_right _ _
          _ ≤ C₄ * dR := h2
          _ ≤ C₄ * (C₂ * dμ) := mul_le_mul_of_nonneg_left hk2 hC₄0
          _ ≤ ((C₂ * D + C₂ + 1) * (C₄ + 1) + 1) * dμ := by
              rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ hdμ0; nlinarith
  · have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
    obtain ⟨-, hk2⟩ := hK1 0 h0
    rw [hfA0 0 h0, hP0] at hk2
    obtain ⟨-, -, r3⟩ := hR Ω Ωs E hEq hEs hE1 hE2 0 h0
    have h2 := r3 (by rw [norm_zero]; norm_num)
    have hdμ0 : 0 ≤ infDist (f (F 0)) (curveOf Ω Ωs) := infDist_nonneg
    calc diam (curveOf Ω Ωs) ≤ C₄ * infDist (E 0) (curveOf Ω Ωs) := h2
      _ ≤ C₄ * (C₂ * infDist (f (F 0)) (curveOf Ω Ωs)) := mul_le_mul_of_nonneg_left hk2 hC₄0
      _ ≤ ((C₂ * D + C₂ + 1) * (C₄ + 1) + 1) * infDist (f (F 0)) (curveOf Ω Ωs) := by
          rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ hdμ0; nlinarith


/-- P3 helper: two-sided infinitesimal bounds `ϖ(z)|Df v| ≤ C ϖ(fz)|v|`, `ϖ(fz)|v| ≤ C ϖ(z)|Df v|`
with positive Jacobian give `|∂̄f| < |∂f|` and dilatation quotient `≤ C²`. -/
theorem s07d_p3_dq_bound {f : ℂ → ℂ} {z : ℂ} {C : ℝ} (hC : 0 ≤ C) (hd : DifferentiableAt ℝ f z)
    (hdet : 0 < (fderiv ℝ f z).det) (hz : 0 < varpi z)
    (hu : ∀ v : ℂ, varpi z * ‖fderiv ℝ f z v‖ ≤ C * varpi (f z) * ‖v‖)
    (hl : ∀ v : ℂ, varpi (f z) * ‖v‖ ≤ C * varpi z * ‖fderiv ℝ f z v‖) :
    ‖dzbar f z‖ < ‖dz f z‖ ∧ dilatationQuotient f z ≤ C ^ 2 := by
  have hJ : (fderiv ℝ f z).det = jacobian f z := det_fderiv_eq_jacobian hd
  have hJ' : jacobian f z = ‖dz f z‖ ^ 2 - ‖dzbar f z‖ ^ 2 := rfl
  have hlt : ‖dzbar f z‖ < ‖dz f z‖ := by
    have h1 : ‖dzbar f z‖ ^ 2 < ‖dz f z‖ ^ 2 := by linarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1
  refine ⟨hlt, ?_⟩
  set p := dz f z with hpdef
  set q := dzbar f z with hqdef
  have hp : 0 < ‖p‖ := (norm_nonneg _).trans_lt hlt
  have hp0 : p ≠ 0 := norm_pos_iff.1 hp
  set w := q / p with hwdef
  have hw1 : ‖w‖ < 1 := by rw [hwdef, norm_div, div_lt_one hp]; exact hlt
  have hqw : q = w * p := by rw [hwdef, div_mul_cancel₀ _ hp0]
  set e := Complex.exp (-(arg w : ℂ) * I) with hedef
  have hwe : w * e = (‖w‖ : ℂ) := by
    have h := Complex.norm_mul_exp_arg_mul_I w
    calc w * e = (‖w‖ : ℂ) * Complex.exp (arg w * I) * Complex.exp (-(arg w : ℂ) * I) := by
          rw [h]
      _ = (‖w‖ : ℂ) * Complex.exp (arg w * I + -(arg w : ℂ) * I) := by
          rw [mul_assoc, ← Complex.exp_add]
      _ = (‖w‖ : ℂ) := by
          rw [show (arg w : ℂ) * I + -(arg w : ℂ) * I = 0 by ring, Complex.exp_zero, mul_one]
  set v₁ := Complex.exp (((arg w / 2 : ℝ) : ℂ) * I) with hv1
  have hv1n : ‖v₁‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hconj : conj v₁ = v₁ * e := by
    rw [hv1, hedef, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    congr 1
    push_cast
    ring
  have hA1 : fderiv ℝ f z v₁ = v₁ * p * ((1 + ‖w‖ : ℝ) : ℂ) := by
    rw [fderiv_eq_dz_dzbar hd, hconj, ← hpdef, ← hqdef, hqw]
    push_cast
    linear_combination (v₁ * p) * hwe
  have hA2 : fderiv ℝ f z (I * v₁) = I * v₁ * p * ((1 - ‖w‖ : ℝ) : ℂ) := by
    rw [fderiv_eq_dz_dzbar hd, map_mul, Complex.conj_I, hconj, ← hpdef, ← hqdef, hqw]
    push_cast
    linear_combination (-(I * v₁ * p)) * hwe
  have hw0 := norm_nonneg w
  have n1 : ‖fderiv ℝ f z v₁‖ = ‖p‖ * (1 + ‖w‖) := by
    rw [hA1, norm_mul, norm_mul, hv1n, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    ring
  have n2 : ‖fderiv ℝ f z (I * v₁)‖ = ‖p‖ * (1 - ‖w‖) := by
    rw [hA2, norm_mul, norm_mul, norm_mul, Complex.norm_I, hv1n, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
    ring
  have nv2 : ‖I * v₁‖ = 1 := by rw [norm_mul, Complex.norm_I, hv1n, one_mul]
  have h1 := hu v₁
  have h2 := hl (I * v₁)
  rw [n1, hv1n] at h1
  rw [n2, nv2] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 hC
  have key : varpi z * ‖p‖ * (1 + ‖w‖) ≤ varpi z * ‖p‖ * (C ^ 2 * (1 - ‖w‖)) := by
    nlinarith
  have key2 := le_of_mul_le_mul_left key (mul_pos hz hp)
  show (1 + ‖w‖) / (1 - ‖w‖) ≤ C ^ 2
  rw [div_le_iff₀ (by linarith)]
  exact key2

/-- P3.6 (Douady–Earle, q.c. form): if `h` admits a `K₀`-q.c. extension, it has an extension `F`
to `𝔻̄` with inverse `Fi` such that:
* `F` is a closed-disk homeomorphism, `L`-bi-Lipschitz for `d_𝔻`;
* `F` is `L`-q.c. on `𝔻`.

`F = E(h)` from `thm_DE`. Its dilatation is bounded by `s07_de_inf`, and
`isKQC_of_isC1Quasiconformal` turns that into the q.c. bound. -/
theorem s07d_p3_de_qc (K₀ : ℝ) (hK₀ : 1 ≤ K₀) : ∃ L : ℝ, 1 ≤ L ∧ ∀ h : ℂ → ℂ, IsCircleHomeo h →
    AdmitsQCDiskExt h K₀ → ∃ F Fi : ℂ → ℂ, IsClosedDiskHomeo F ∧ EqOn F h (sphere (0 : ℂ) 1) ∧
      IsDiskBiLip F L ∧ IsKQC F unitDisc L ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, Fi (F z) = z ∧ F (Fi z) = z := by
  obtain ⟨C, hC, hinf⟩ := s07_de_inf K₀ hK₀
  have hCC : C ≤ C ^ 2 := by nlinarith
  refine ⟨C ^ 2, by nlinarith, fun h hh hadm => ?_⟩
  obtain ⟨φ, hφb, hφc, hor, hF, hFh, han, hdet⟩ := s07_de_extension hh
  obtain ⟨H, hH, hHs, hHb⟩ := hadm
  have hhφ : ∀ ζ : Circle, h ζ = φ ζ := by
    intro ζ
    have hζ : (ζ : ℂ) ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr (Circle.norm_coe ζ)
    rw [← hFh hζ]
    exact extension_eq_boundary φ ζ
  obtain ⟨hbij, -, G, hGc, hGl, hGr⟩ := extension_isHomeomorphOn φ hφb hφc
  have hFD : MapsTo (extension φ) unitDisc unitDisc := fun z hz =>
    mem_ball_zero_iff.mpr (extension_mem_disk φ hφb hφc z (mem_ball_zero_iff.mp hz))
  have hGD : MapsTo G unitDisc unitDisc := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hbij.surjOn (ball_subset_closedBall hw)
    rw [hGl hx]
    rcases (mem_closedBall_zero_iff.mp hx).lt_or_eq with h1 | h1
    · exact mem_ball_zero_iff.mpr h1
    · exfalso
      have hx' : x ∈ Submonoid.unitSphere ℂ := mem_sphere_zero_iff_norm.mpr h1
      have e : extension φ x = (φ ⟨x, hx'⟩ : ℂ) := extension_eq_boundary φ ⟨x, hx'⟩
      have hn := Circle.norm_coe (φ ⟨x, hx'⟩)
      have hw1 := mem_ball_zero_iff.mp hw
      rw [e] at hw1
      linarith
  have hFG : ∀ w ∈ unitDisc, extension φ (G w) = w := fun w hw => hGr (ball_subset_closedBall hw)
  have hGF : ∀ z ∈ unitDisc, G (extension φ z) = z := fun z hz =>
    hGl (ball_subset_closedBall hz)
  have hd : ∀ z ∈ unitDisc, DifferentiableAt ℝ (extension φ) z := fun z hz =>
    (han z hz).differentiableAt
  have hbl : IsDiskBiLip (extension φ) C :=
    s07_de_bilip_of_inf hFD hGD hFG hGF (hGc.mono ball_subset_closedBall) hd hdet
      (fun z hz v => (hinf φ hφb hφc hor H h hH hHs hHb hhφ z hz v).1)
      (fun z hz v => (hinf φ hφb hφc hor H h hH hHs hHb hhφ z hz v).2)
  have hdd : ∀ x ∈ unitDisc, ∀ y ∈ unitDisc, 0 ≤ diskDist x y := fun x hx y hy => by
    rw [s07d_p3_dd_blaschke hx hy]
    have hb := blaschke_mem_unitDisc (mem_ball_zero_iff.mp hx) (mem_ball_zero_iff.mp hy)
    exact (norm_nonneg _).trans (s07d_p3_dd0_bounds hb).1
  refine ⟨extension φ, G, hF, hFh, fun x hx y hy => ?_, ?_, fun z hz => ⟨hGl hz, hGr hz⟩⟩
  · obtain ⟨h1, h2⟩ := hbl x hx y hy
    exact ⟨h1.trans (mul_le_mul_of_nonneg_right hCC (hdd x hx y hy)),
      h2.trans (mul_le_mul_of_nonneg_right hCC (hdd _ (hFD hx) _ (hFD hy)))⟩
  · have hinj : InjOn (extension φ) unitDisc := hbij.injOn.mono ball_subset_closedBall
    have hinv : ContinuousOn (Function.invFunOn (extension φ) unitDisc)
        (extension φ '' unitDisc) := by
      have hsub : extension φ '' unitDisc ⊆ closedBall (0 : ℂ) 1 :=
        (image_subset_iff.2 hFD).trans ball_subset_closedBall
      refine (hGc.mono hsub).congr ?_
      rintro _ ⟨x, hx, rfl⟩
      rw [hGl (ball_subset_closedBall hx)]
      exact hinj.leftInvOn_invFunOn hx
    refine isKQC_of_isC1Quasiconformal ⟨isOpen_ball, by nlinarith, (han.contDiffOn isOpen_ball.uniqueDiffOn),
      ⟨hF.2.mono ball_subset_closedBall, hinj, rfl, hinv⟩, fun z hz => ?_⟩
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hvz : 0 < varpi z := by
      show 0 < 1 - ‖z‖ ^ 2
      nlinarith [norm_nonneg z]
    exact s07d_p3_dq_bound (by linarith) (hd z hz) (hdet z hz) hvz
      (fun v => (hinf φ hφb hφc hor H h hH hHs hHb hhφ z hz v).1)
      (fun v => (hinf φ hφb hφc hor H h hH hHs hHb hhφ z hz v).2)

/-- P3 helper: the inverse of a closed-disk homeomorphism is continuous on `𝔻̄` (compactness). -/
theorem s07d_p3_inv_contOn {F Fi : ℂ → ℂ} (hF : IsClosedDiskHomeo F)
    (hFi : ∀ z ∈ closedBall (0 : ℂ) 1, Fi (F z) = z ∧ F (Fi z) = z) :
    ContinuousOn Fi (closedBall (0 : ℂ) 1) := by
  rw [continuousOn_iff_isClosed]
  intro t ht
  have hc : IsClosed (F '' (closedBall (0 : ℂ) 1 ∩ t)) :=
    (((isCompact_closedBall (0 : ℂ) 1).inter_right ht).image_of_continuousOn
      (hF.2.mono inter_subset_left)).isClosed
  refine ⟨F '' (closedBall (0 : ℂ) 1 ∩ t), hc, ?_⟩
  ext w
  constructor
  · rintro ⟨hwt, hw⟩
    obtain ⟨x, hx, rfl⟩ := hF.1.surjOn hw
    refine ⟨⟨x, ⟨hx, ?_⟩, rfl⟩, hw⟩
    have hxt : Fi (F x) ∈ t := hwt
    rwa [(hFi x hx).1] at hxt
  · rintro ⟨⟨x, ⟨hx, hxt⟩, rfl⟩, hw⟩
    refine ⟨?_, hw⟩
    show Fi (F x) ∈ t
    rw [(hFi x hx).1]
    exact hxt

/-- P3.7 (gluing; `s07u_glue` with `E = jRefl ∘ Fi ∘ jRefl`): for an extension `F` of the welding
`h` with `F 0 = 0`, the map `Φ = f` on `𝔻`, `Φ = g ∘ jRefl ∘ Fi ∘ jRefl` on `𝔻*` is a global
q.c. map. Ahlfors' reflection is then `ρ = Φ ∘ jRefl ∘ Φ⁻¹`. -/
theorem s07d_p3_glue {Ω Ωs : Set ℂ} {K K₁ : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K)
    {f g h F Fi : ℂ → ℂ} (hw : IsDiskWelding Ω Ωs f g h) (hF : IsClosedDiskHomeo F)
    (hFh : EqOn F h (sphere (0 : ℂ) 1)) (hF0 : F 0 = 0) (hFq : IsKQC F unitDisc K₁)
    (hFi : ∀ z ∈ closedBall (0 : ℂ) 1, Fi (F z) = z ∧ F (Fi z) = z) :
    ∃ Φ : ℂ → ℂ, IsKQC Φ univ K₁ ∧ Φ '' univ = univ ∧ (∀ z ∈ unitDisc, Φ z = f z) ∧
      ∀ z ∈ unitDiscExterior, Φ z = g (jRefl (Fi (jRefl z))) := by
  have hsph : ∀ ζ ∈ sphere (0 : ℂ) 1, F ζ ∈ sphere (0 : ℂ) 1 := fun ζ hζ => by
    rw [hFh hζ]
    exact hw.2.2.2.1 hζ
  -- `F(𝔻) = 𝔻`: `F(𝔻)` is open in `𝔻̄`, and `F(∂𝔻) ⊆ ∂𝔻`
  have hFD : ∀ z ∈ unitDisc, F z ∈ unitDisc := by
    intro z hz
    have h1 : F '' unitDisc ⊆ closedBall (0 : ℂ) 1 :=
      image_subset_iff.2 fun x hx => hF.1.mapsTo (ball_subset_closedBall hx)
    have h2 : F '' unitDisc ⊆ interior (closedBall (0 : ℂ) 1) :=
      (isOpen_image_of_isKQC hFq).subset_interior_iff.2 h1
    rw [interior_closedBall (0 : ℂ) one_ne_zero] at h2
    exact h2 (mem_image_of_mem F hz)
  have hFs : F '' unitDisc = unitDisc := by
    refine Subset.antisymm (image_subset_iff.2 hFD) fun w hw => ?_
    obtain ⟨x, hx, rfl⟩ := hF.1.surjOn (ball_subset_closedBall hw)
    refine ⟨x, ?_, rfl⟩
    rcases (mem_closedBall_zero_iff.mp hx).lt_or_eq with h1 | h1
    · exact mem_ball_zero_iff.mpr h1
    · exfalso
      have h2 := hsph x (mem_sphere_zero_iff_norm.mpr h1)
      have hw1 := mem_ball_zero_iff.mp hw
      rw [mem_sphere_zero_iff_norm] at h2
      linarith
  have hbv : HasDiskBoundaryValues F h := fun ζ hζ => by
    have h1 := (hF.2 ζ (sphere_subset_closedBall hζ)).tendsto
    rw [hFh hζ] at h1
    exact h1.mono_left (nhdsWithin_mono _ ball_subset_closedBall)
  have hh : IsCircleHomeo h := s07_circleHomeo_of_qcExt hFq hFs hbv
  -- the inverse `Fi` on `𝔻`
  have hFiD : ∀ w ∈ unitDisc, Fi w ∈ unitDisc := by
    intro w hw
    have hw' : w ∈ F '' unitDisc := by rw [hFs]; exact hw
    obtain ⟨x, hx, rfl⟩ := hw'
    rw [(hFi x (ball_subset_closedBall hx)).1]
    exact hx
  have hFis : Fi '' unitDisc = unitDisc :=
    Subset.antisymm (image_subset_iff.2 hFiD) fun z hz =>
      ⟨F z, hFD z hz, (hFi z (ball_subset_closedBall hz)).1⟩
  have hFi0 : Fi 0 = 0 := by
    have h1 := (hFi 0 (mem_closedBall_self zero_le_one)).1
    rwa [hF0] at h1
  have hinj : InjOn F unitDisc := hF.1.injOn.mono ball_subset_closedBall
  have hFiq : IsKQC Fi unitDisc K₁ := by
    have h1 := thm7_2_inv hFq
    rw [hFs] at h1
    refine ad_isKQC_congr h1 fun w hw => ?_
    have hw' : w ∈ F '' unitDisc := by rw [hFs]; exact hw
    obtain ⟨x, hx, rfl⟩ := hw'
    rw [(hFi x (ball_subset_closedBall hx)).1, hinj.leftInvOn_invFunOn hx]
  -- reflect `Fi` to a symmetric global q.c. map `E`
  obtain ⟨Hx, hHx⟩ :=
    thm13_3_boundary_correspondence isJordanDomain_unitDisc isJordanDomain_unitDisc ⟨K₁, hFiq⟩ hFis
  obtain ⟨E, hEq, hEs, hEFi, -, hsym, -⟩ := ab_reflect hFiq hFis hFi0 hHx
  obtain ⟨T, hT⟩ := t1_homeomorph hEq hEs
  have hEc : Continuous E := by
    rw [← hT]
    exact T.continuous
  have hext : ∀ z ∈ unitDiscExterior, E z = jRefl (Fi (jRefl z)) := by
    intro z hz
    obtain ⟨hjD, hj0⟩ := s07d_p3_jRefl_ext hz
    have h1 := hsym (jRefl z) hj0
    have e1 : (conj (jRefl z))⁻¹ = z := s07d_p3_jRefl_jRefl z
    rw [e1, hEFi hjD] at h1
    exact h1
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEsx : E '' unitDiscExterior = unitDiscExterior := by
    refine Subset.antisymm ?_ fun w hw => ?_
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨hjD, hj0⟩ := s07d_p3_jRefl_ext hz
      rw [hext z hz]
      refine s07d_p3_jRefl_int (hFiD _ hjD) fun hu0 => hj0 ?_
      have h1 := (hFi (jRefl z) (ball_subset_closedBall hjD)).2
      rw [hu0, hF0] at h1
      exact h1.symm
    · obtain ⟨hvD, hv0⟩ := s07d_p3_jRefl_ext hw
      have hFv0 : F (jRefl w) ≠ 0 := fun h0 => hv0 (hinj hvD (mem_ball_self one_pos)
        (h0.trans hF0.symm))
      have hz := s07d_p3_jRefl_int (hFD _ hvD) hFv0
      refine ⟨jRefl (F (jRefl w)), hz, ?_⟩
      rw [hext _ hz, s07d_p3_jRefl_jRefl, (hFi _ (ball_subset_closedBall hvD)).1,
        s07d_p3_jRefl_jRefl]
  have hEinf : Tendsto E (cocompact ℂ) (cocompact ℂ) := by
    rw [← hT]
    exact T.isClosedEmbedding.tendsto_cocompact
  have hFicont := s07d_p3_inv_contOn hF hFi
  have hEb : ∀ ζ ∈ sphere (0 : ℂ) 1, Tendsto E (𝓝[unitDiscExterior] (h ζ)) (𝓝 ζ) := by
    intro ζ hζ
    have hζc : ζ ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hζ
    have hFζ : F ζ ∈ sphere (0 : ℂ) 1 := hsph ζ hζ
    have hcl : F ζ ∈ closure unitDisc := by
      rw [show closure unitDisc = closedBall (0 : ℂ) 1 from closure_ball (0 : ℂ) one_ne_zero]
      exact sphere_subset_closedBall hFζ
    have hnb : (𝓝[unitDisc] (F ζ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
    have t1 : Tendsto E (𝓝[unitDisc] (F ζ)) (𝓝 (E (F ζ))) :=
      hEc.continuousAt.continuousWithinAt.tendsto
    have t2 : Tendsto Fi (𝓝[unitDisc] (F ζ)) (𝓝 ζ) := by
      have h1 := (hFicont (F ζ) (sphere_subset_closedBall hFζ)).tendsto
      rw [(hFi ζ hζc).1] at h1
      exact h1.mono_left (nhdsWithin_mono _ ball_subset_closedBall)
    have t3 : Tendsto E (𝓝[unitDisc] (F ζ)) (𝓝 ζ) :=
      t2.congr' (eventually_nhdsWithin_of_forall fun w hw => (hEFi hw).symm)
    have heq : E (F ζ) = ζ := tendsto_nhds_unique t1 t3
    have t4 : Tendsto E (𝓝 (F ζ)) (𝓝 ζ) := by
      have h1 := hEc.continuousAt (x := F ζ)
      rw [ContinuousAt, heq] at h1
      exact h1
    rw [← hFh hζ]
    exact t4.mono_left nhdsWithin_le_nhds
  obtain ⟨Φ, hΦq, hΦs, hΦf, hΦg, -, -⟩ :=
    s07u_glue hq hw hh (t3b_isKQC_restrict hEq hEo (subset_univ _)) hEsx hEinf hEb
  exact ⟨Φ, hΦq, hΦs, hΦf, fun z hz => by rw [hΦg z hz, hext z hz]⟩

/-- P3 helper: the Möbius map `(z - c)/(1 - c̄ z)` has the left inverse `(w + c)/(1 + c̄ w)` off its
pole, and its values avoid the pole of that inverse. -/
theorem s07d_p3_mob_inv {c z : ℂ} (hc : conj c * c ≠ 1) (hz : 1 - conj c * z ≠ 0) :
    1 + conj c * ((z - c) / (1 - conj c * z)) ≠ 0 ∧
      ((z - c) / (1 - conj c * z) + c) / (1 + conj c * ((z - c) / (1 - conj c * z))) = z := by
  have hc' : 1 - conj c * c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have e : 1 + conj c * ((z - c) / (1 - conj c * z)) = (1 - conj c * c) / (1 - conj c * z) := by
    field_simp
    ring
  have e2 : (z - c) / (1 - conj c * z) + c = z * (1 - conj c * c) / (1 - conj c * z) := by
    rw [div_add' _ _ _ hz]
    congr 1
    ring
  refine ⟨by rw [e]; exact div_ne_zero hc' hz, ?_⟩
  rw [e, e2, div_div_div_cancel_right₀ hz, mul_div_assoc, div_self hc', mul_one]

/-- P3 helper: the inverse Möbius map `(w + c)/(1 + c̄ w)` has the left inverse
`(z - c)/(1 - c̄ z)` off its pole. -/
theorem s07d_p3_mob_inv' {c w : ℂ} (hc : conj c * c ≠ 1) (hw : 1 + conj c * w ≠ 0) :
    1 - conj c * ((w + c) / (1 + conj c * w)) ≠ 0 ∧
      ((w + c) / (1 + conj c * w) - c) / (1 - conj c * ((w + c) / (1 + conj c * w))) = w := by
  have hc' : 1 - conj c * c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have e : 1 - conj c * ((w + c) / (1 + conj c * w)) = (1 - conj c * c) / (1 + conj c * w) := by
    field_simp
    ring
  have e2 : (w + c) / (1 + conj c * w) - c = w * (1 - conj c * c) / (1 + conj c * w) := by
    rw [div_sub' hw]
    congr 1
    ring
  refine ⟨by rw [e]; exact div_ne_zero hc' hw, ?_⟩
  rw [e, e2, div_div_div_cancel_right₀ hw, mul_div_assoc, div_self hc', mul_one]

/-- P3 helper (the transfer map). For a global `Q`-q.c. map `κ₀` of `ℂ` onto `ℂ` with
`0 ∉ κ₀(𝔻̄)`, let `p` be the zero of `κ₀` (`|p| > 1`). Put `c = -1/p`, `ν = diskAut c` (so
`ν(∞) = p̄`, with pole `q = -p̄`), `σ = conj ∘ ν`, and `H = jRefl ∘ κ₀ ∘ σ`, set to `0` at `q`. Then
`H` is a global `Q`-q.c. map of `ℂ` onto `ℂ` that equals `jRefl ∘ κ₀ ∘ σ` on `𝔻̄`, `σ` preserves `𝔻`
and `∂𝔻`, and `|σ 0| |p| = 1`. -/
theorem s07d_p3_transfer_map {Q : ℝ} {κ₀ : ℂ → ℂ} (hκ : IsKQC κ₀ univ Q) (hκs : κ₀ '' univ = univ)
    (h0 : (0 : ℂ) ∉ κ₀ '' closedBall (0 : ℂ) 1) :
    ∃ H σ : ℂ → ℂ, IsKQC H univ Q ∧ H '' univ = univ ∧
      σ '' unitDisc = unitDisc ∧ σ '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, H z = jRefl (κ₀ (σ z))) ∧
      ∀ p : ℂ, κ₀ p = 0 → ‖σ 0‖ * ‖p‖ ≤ 1 := by
  obtain ⟨p, -, hp⟩ : (0 : ℂ) ∈ κ₀ '' univ := hκs.symm ▸ mem_univ _
  have hp1 : 1 < ‖p‖ := by
    by_contra hle
    exact h0 ⟨p, mem_closedBall_zero_iff.mpr (not_lt.mp hle), hp⟩
  have hp0 : p ≠ 0 := norm_pos_iff.mp (one_pos.trans hp1)
  have hcp0 : conj p ≠ 0 := (map_ne_zero _).mpr hp0
  set c : ℂ := -p⁻¹ with hc
  have hcn : ‖c‖ < 1 := by
    rw [hc, norm_neg, norm_inv]
    exact inv_lt_one_of_one_lt₀ hp1
  have hcc : conj c = -(conj p)⁻¹ := by rw [hc, map_neg, map_inv₀]
  have hc1 : conj c * c ≠ 1 := by
    intro h
    have h2 := congrArg norm h
    rw [norm_mul, Complex.norm_conj, norm_one] at h2
    nlinarith [norm_nonneg c]
  set q : ℂ := -conj p with hq
  have hpole : ∀ z, 1 - conj c * z = 0 ↔ z = q := by
    intro z
    have e : (1 - conj c * z) * conj p = conj p + z := by
      rw [hcc]
      field_simp
      ring
    constructor
    · intro h
      have h3 : conj p + z = 0 := by rw [← e, h, zero_mul]
      rw [hq]
      linear_combination h3
    · intro h
      have h3 : (1 - conj c * z) * conj p = 0 := by rw [e, h, hq]; ring
      exact (mul_eq_zero.mp h3).resolve_right hcp0
  have hpole' : ∀ w, 1 + conj c * w = 0 ↔ w = conj p := by
    intro w
    have e : (1 + conj c * w) * conj p = conj p - w := by
      rw [hcc]
      field_simp
      ring
    constructor
    · intro h
      have h3 : conj p - w = 0 := by rw [← e, h, zero_mul]
      linear_combination -h3
    · intro h
      have h3 : (1 + conj c * w) * conj p = 0 := by rw [e, h]; ring
      exact (mul_eq_zero.mp h3).resolve_right hcp0
  set ν : ℂ → ℂ := fun z => (z - c) / (1 - conj c * z) with hνdef
  set ν' : ℂ → ℂ := fun w => (w + c) / (1 + conj c * w) with hν'def
  have hνν' : ∀ z, z ≠ q → ν z ≠ conj p ∧ ν' (ν z) = z := by
    intro z hz
    have hd : 1 - conj c * z ≠ 0 := fun h => hz ((hpole z).mp h)
    obtain ⟨h1, h2⟩ := s07d_p3_mob_inv hc1 hd
    exact ⟨fun h => h1 ((hpole' _).mpr h), h2⟩
  have hν'ν : ∀ w, w ≠ conj p → ν' w ≠ q ∧ ν (ν' w) = w := by
    intro w hw
    have hd : 1 + conj c * w ≠ 0 := fun h => hw ((hpole' w).mp h)
    obtain ⟨h1, h2⟩ := s07d_p3_mob_inv' hc1 hd
    exact ⟨fun h => h1 ((hpole _).mpr h), h2⟩
  -- `ν` is conformal from `ℂ ∖ {q}` onto `ℂ ∖ {p̄}`
  have hνconf : IsConformalOnto ν {q}ᶜ {conj p}ᶜ := by
    refine ⟨fun z hz => ?_, fun z₁ hz₁ z₂ hz₂ h => ?_, ?_⟩
    · have hd : 1 - conj c * z ≠ 0 := fun h => hz ((hpole z).mp h)
      exact ((differentiableAt_id.sub_const c).div
        ((differentiableAt_const _).sub (differentiableAt_id.const_mul _)) hd).differentiableWithinAt
    · rw [← (hνν' z₁ hz₁).2, ← (hνν' z₂ hz₂).2, h]
    · ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (hνν' z hz).1
      · intro hw
        exact ⟨ν' w, (hν'ν w hw).1, (hν'ν w hw).2⟩
  have hν1 : IsKQC ν {q}ᶜ 1 := isKQC_one_of_conformal isOpen_compl_singleton hνconf
  -- the conjugated map `κ̃ = conj ∘ κ₀ ∘ conj`
  set κt : ℂ → ℂ := fun z => conj (κ₀ (conj z)) with hκtdef
  have hκt : IsKQC κt univ Q := by
    have := abR_x_isKQC_conj hκ
    rwa [preimage_univ] at this
  have hκts : κt '' univ = univ := by
    refine eq_univ_of_forall fun y => ?_
    obtain ⟨x, -, hx⟩ : conj y ∈ κ₀ '' univ := hκs.symm ▸ mem_univ _
    exact ⟨conj x, mem_univ _, by
      show conj (κ₀ (conj (conj x))) = y
      rw [Complex.conj_conj, hx, Complex.conj_conj]⟩
  have hκti : Function.Injective κt := fun x y h =>
    hκt.2.2.1.2.1 (mem_univ x) (mem_univ y) h
  have hκtp : κt (conj p) = 0 := by
    show conj (κ₀ (conj (conj p))) = 0
    rw [Complex.conj_conj, hp, map_zero]
  have hκtr : IsKQC κt {conj p}ᶜ Q := t3b_isKQC_restrict hκt isOpen_compl_singleton (subset_univ _)
  have hκtim : κt '' {conj p}ᶜ = {0}ᶜ := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩ h
      exact hy (hκti ((mem_singleton_iff.mp h).trans hκtp.symm))
    · intro hw
      obtain ⟨y, -, rfl⟩ : w ∈ κt '' univ := hκts.symm ▸ mem_univ _
      refine ⟨y, fun h => hw ?_, rfl⟩
      rw [mem_singleton_iff.mp h, hκtp]
      exact mem_singleton _
  -- the inversion
  have hinvconf : IsConformalOnto (fun w : ℂ => w⁻¹) {0}ᶜ {0}ᶜ := by
    refine ⟨fun w hw => (differentiableAt_inv hw).differentiableWithinAt,
      fun x _ y _ h => inv_injective h, ?_⟩
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact inv_ne_zero hy
    · intro hw
      exact ⟨w⁻¹, inv_ne_zero hw, inv_inv w⟩
  have hinv1 : IsKQC (fun w : ℂ => w⁻¹) {0}ᶜ 1 :=
    isKQC_one_of_conformal isOpen_compl_singleton hinvconf
  have h12 : IsKQC (κt ∘ ν) {q}ᶜ (1 * Q) :=
    thm7_1_comp hν1 hκtr (by rw [hνconf.2.2])
  have h12im : (κt ∘ ν) '' {q}ᶜ = {0}ᶜ := by rw [image_comp, hνconf.2.2, hκtim]
  have h123 : IsKQC ((fun w : ℂ => w⁻¹) ∘ (κt ∘ ν)) {q}ᶜ (1 * Q * 1) :=
    thm7_1_comp h12 hinv1 h12im.le
  rw [one_mul, mul_one] at h123
  set H : ℂ → ℂ := fun z => if z = q then 0 else (κt (ν z))⁻¹ with hHdef
  have hHq : H q = 0 := if_pos rfl
  have hHne : ∀ z, z ≠ q → H z = (κt (ν z))⁻¹ := fun z hz => if_neg hz
  have hHcomp : EqOn H ((fun w : ℂ => w⁻¹) ∘ (κt ∘ ν)) {q}ᶜ := fun z hz => hHne z hz
  have hHpq : IsKQC H {q}ᶜ Q := ad_isKQC_congr h123 hHcomp
  have hκν0 : ∀ z, z ≠ q → κt (ν z) ≠ 0 := by
    intro z hz h
    have : κt (ν z) ∈ ({0}ᶜ : Set ℂ) := by
      rw [← h12im]
      exact ⟨z, hz, rfl⟩
    exact this h
  -- continuity at the pole: `ν → ∞`, so `κt ∘ ν → ∞`, so `H → 0`
  have hνlim : Tendsto ν (𝓝[≠] q) (cocompact ℂ) := by
    have hqc : q ≠ c := by
      intro h
      have h2 : ‖q‖ = ‖c‖ := by rw [h]
      rw [hq, norm_neg, Complex.norm_conj] at h2
      linarith
    have h1 : Tendsto (fun z => ‖z - c‖) (𝓝[≠] q) (𝓝 ‖q - c‖) :=
      ((continuous_id.sub continuous_const).norm.tendsto q).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun z => ‖1 - conj c * z‖) (𝓝[≠] q) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h3 : Tendsto (fun z => ‖1 - conj c * z‖) (𝓝 q) (𝓝 ‖1 - conj c * q‖) :=
          ((continuous_const.sub (continuous_const.mul continuous_id)).norm.tendsto q)
        rw [(hpole q).mpr rfl, norm_zero] at h3
        exact h3.mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun z hz =>
          norm_pos_iff.mpr fun h => hz ((hpole z).mp h)
    have h4 : Tendsto (fun z => ‖z - c‖ * ‖1 - conj c * z‖⁻¹) (𝓝[≠] q) atTop :=
      Filter.Tendsto.pos_mul_atTop (norm_pos_iff.mpr (sub_ne_zero.mpr hqc)) h1
        (tendsto_inv_nhdsGT_zero.comp h2)
    have h5 : Tendsto (fun z => ‖ν z‖) (𝓝[≠] q) atTop := by
      refine h4.congr fun z => ?_
      show ‖z - c‖ * ‖1 - conj c * z‖⁻¹ = ‖(z - c) / (1 - conj c * z)‖
      rw [norm_div, div_eq_mul_inv]
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_norm_atTop_iff_cobounded.mp h5
  obtain ⟨Tκ, hTκ⟩ := t1_homeomorph hκt hκts
  have hκlim : Tendsto κt (cocompact ℂ) (cocompact ℂ) := hTκ ▸ Tκ.isClosedEmbedding.tendsto_cocompact
  have hinvlim : Tendsto (fun w : ℂ => w⁻¹) (cocompact ℂ) (𝓝 0) := by
    have := tendsto_inv₀_cobounded (α := ℂ)
    rwa [Metric.cobounded_eq_cocompact] at this
  have hHlim : Tendsto H (𝓝[≠] q) (𝓝 (H q)) := by
    rw [hHq]
    refine (hinvlim.comp (hκlim.comp hνlim)).congr' ?_
    exact eventually_nhdsWithin_of_forall fun z hz => (hHne z hz).symm
  have hHc : ContinuousOn H univ := by
    intro z _
    by_cases hz : z = q
    · subst hz
      exact (continuousWithinAt_compl_self.mp hHlim).continuousWithinAt
    · exact ((hHpq.2.2.1.1 z hz).continuousAt
        (isOpen_compl_singleton.mem_nhds hz)).continuousWithinAt
  have hHi : InjOn H univ := by
    intro z₁ _ z₂ _ h
    by_cases h1 : z₁ = q
    · by_cases h2 : z₂ = q
      · rw [h1, h2]
      · exfalso
        rw [h1, hHq, hHne z₂ h2] at h
        exact inv_ne_zero (hκν0 z₂ h2) h.symm
    · by_cases h2 : z₂ = q
      · exfalso
        rw [h2, hHq, hHne z₁ h1] at h
        exact inv_ne_zero (hκν0 z₁ h1) h
      · exact hHpq.2.2.1.2.1 h1 h2 h
  have hHs : H '' univ = univ := by
    refine eq_univ_of_forall fun w => ?_
    by_cases hw : w = 0
    · exact ⟨q, mem_univ _, hw ▸ hHq⟩
    · have : w⁻¹ ∈ (κt ∘ ν) '' {q}ᶜ := by rw [h12im]; exact inv_ne_zero hw
      obtain ⟨z, hz, hzw⟩ := this
      exact ⟨z, mem_univ _, by rw [hHne z hz]; exact (congrArg (·⁻¹) hzw).trans (inv_inv w)⟩
  have hHhom : IsHomeomorphOnto H univ univ := by
    have := qcl_f_isHomeomorphOnto_of_injOn isOpen_univ hHc hHi
    rwa [hHs] at this
  -- the disk part: `σ = conj ∘ ν` preserves `𝔻` and `∂𝔻`
  have hνd : ∀ z, ν z = diskAut c z := fun z => rfl
  have hν'd : ∀ w, ν' w = diskAut (-c) w := by
    intro w
    show (w + c) / (1 + conj c * w) = (w - -c) / (1 - star (-c) * w)
    rw [sub_neg_eq_add, star_neg]
    congr 1
    show 1 + conj c * w = 1 - -conj c * w
    ring
  have hcn' : ‖-c‖ < 1 := by rwa [norm_neg]
  have hqball : ∀ z ∈ closedBall (0 : ℂ) 1, z ≠ q := by
    intro z hz h
    have h2 : ‖z‖ = ‖q‖ := by rw [h]
    rw [hq, norm_neg, Complex.norm_conj] at h2
    have := mem_closedBall_zero_iff.mp hz
    linarith
  set σ : ℂ → ℂ := fun z => conj (ν z) with hσdef
  have hσS : ∀ (P : ℝ → Prop), (∀ z : ℂ, P ‖z‖ → ‖z‖ ≤ 1) →
      (∀ z : ℂ, P ‖z‖ → P ‖diskAut c z‖) → (∀ z : ℂ, P ‖z‖ → P ‖diskAut (-c) z‖) →
      σ '' {z : ℂ | P ‖z‖} = {z : ℂ | P ‖z‖} := by
    intro P hP1 hPc hPc'
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      show P ‖conj (ν z)‖
      rw [Complex.norm_conj, hνd]
      exact hPc z hz
    · intro hw
      have hw' : P ‖conj w‖ := by rw [Complex.norm_conj]; exact hw
      refine ⟨ν' (conj w), ?_, ?_⟩
      · show P ‖ν' (conj w)‖
        rw [hν'd]
        exact hPc' _ hw'
      · show conj (ν (ν' (conj w))) = w
        rw [hνd, hν'd, diskAut_neg_left_inv hcn (hP1 _ hw'), Complex.conj_conj]
  have hσD : σ '' unitDisc = unitDisc := by
    have := hσS (fun r => r < 1) (fun z hz => hz.le)
      (fun z hz => diskAut_maps_disk_to_disk c z hcn hz)
      (fun z hz => diskAut_maps_disk_to_disk (-c) z hcn' hz)
    have e : unitDisc = {z : ℂ | ‖z‖ < 1} := by
      ext z
      exact mem_ball_zero_iff
    rw [e]
    exact this
  have hσC : σ '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 := by
    have := hσS (fun r => r = 1) (fun z hz => hz.le)
      (fun z hz => diskAut_norm_eq_one c z hcn hz)
      (fun z hz => diskAut_norm_eq_one (-c) z hcn' hz)
    have e : sphere (0 : ℂ) 1 = {z : ℂ | ‖z‖ = 1} := by
      ext z
      exact mem_sphere_zero_iff_norm
    rw [e]
    exact this
  refine ⟨H, σ, b4_isKQC_univ_of_punctured hHhom hHpq, hHs, hσD, hσC, fun z hz => ?_, ?_⟩
  · rw [hHne z (hqball z hz)]
    rfl
  · intro p' hp'
    have hpp : p' = p := hκ.2.2.1.2.1 (mem_univ _) (mem_univ _) (hp'.trans hp.symm)
    have hσ0 : σ 0 = conj p⁻¹ := by
      show conj ((0 - c) / (1 - conj c * 0)) = conj p⁻¹
      rw [hc]
      simp
    rw [hpp, hσ0, Complex.norm_conj, norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp0)]

/-- P3 helper: a welding stays a welding when its circle map is changed off `∂𝔻`. -/
theorem s07d_p3_weld_congr {Ω Ωs : Set ℂ} {f g h h' : ℂ → ℂ} (hw : IsDiskWelding Ω Ωs f g h)
    (hhh : EqOn h h' (sphere (0 : ℂ) 1)) : IsDiskWelding Ω Ωs f g h' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  refine ⟨h1, h2, h3, fun ζ hζ => ?_, fun ζ hζ => ?_⟩
  · rw [← hhh hζ]
    exact h4 hζ
  · rw [← hhh hζ]
    exact h5 ζ hζ

/-- P3 helper: a closed-disk homeomorphism that is q.c. on `𝔻` and maps `∂𝔻` into `∂𝔻` maps `𝔻`
onto `𝔻`. -/
theorem s07d_p3_disk_onto {F : ℂ → ℂ} {K : ℝ} (hF : IsClosedDiskHomeo F) (hFq : IsKQC F unitDisc K)
    (hsph : ∀ ζ ∈ sphere (0 : ℂ) 1, F ζ ∈ sphere (0 : ℂ) 1) :
    (∀ z ∈ unitDisc, F z ∈ unitDisc) ∧ F '' unitDisc = unitDisc := by
  have hFD : ∀ z ∈ unitDisc, F z ∈ unitDisc := by
    intro z hz
    have h1 : F '' unitDisc ⊆ closedBall (0 : ℂ) 1 :=
      image_subset_iff.2 fun x hx => hF.1.mapsTo (ball_subset_closedBall hx)
    have h2 : F '' unitDisc ⊆ interior (closedBall (0 : ℂ) 1) :=
      (isOpen_image_of_isKQC hFq).subset_interior_iff.2 h1
    rw [interior_closedBall (0 : ℂ) one_ne_zero] at h2
    exact h2 (mem_image_of_mem F hz)
  refine ⟨hFD, Subset.antisymm (image_subset_iff.2 hFD) fun w hw => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hF.1.surjOn (ball_subset_closedBall hw)
  refine ⟨x, ?_, rfl⟩
  rcases (mem_closedBall_zero_iff.mp hx).lt_or_eq with h1 | h1
  · exact mem_ball_zero_iff.mpr h1
  · exfalso
    have h2 := hsph x (mem_sphere_zero_iff_norm.mpr h1)
    have hw1 := mem_ball_zero_iff.mp hw
    rw [mem_sphere_zero_iff_norm] at h2
    linarith

/-- P3 helper: `diskAut (-b)` inverts `diskAut b` on `𝔻̄`. -/
theorem s07d_p3_diskAut_inv {b u : ℂ} (hb : ‖b‖ < 1) (hu : ‖u‖ ≤ 1) :
    diskAut (-b) (diskAut b u) = u := by
  have hb' : ‖-b‖ < 1 := by rwa [norm_neg]
  have h := diskAut_neg_left_inv hb' hu
  rwa [neg_neg] at h

/-- P3 helper (normalisation): for a welding `(f, g, h)` of a bounded `K`-quasicircle there are
`a ∈ 𝔻` and an extension `F` of `M⁻¹ ∘ h` (`M = diskMobius 0 a`) with `F 0 = 0`, a closed-disk
homeomorphism, `L`-bi-Lipschitz for `d_𝔻` and `L`-q.c. on `𝔻`, with inverse `Fi` on `𝔻̄`, such that
`(f ∘ M, g, F)` is a welding. `F = diskAut b ∘ F₁` with `F₁` from P3.6 and `b = F₁ 0`, `a = -b`. -/
theorem s07d_p3_normal (K : ℝ) (hK : 1 ≤ K) : ∃ L : ℝ, 1 ≤ L ∧
    ∀ Ω Ωs : Set ℂ, IsBoundedKQuasicircle Ω Ωs K → ∀ f g h : ℂ → ℂ, IsDiskWelding Ω Ωs f g h →
      ∃ F Fi : ℂ → ℂ, ∃ a ∈ unitDisc, IsDiskWelding Ω Ωs (fun z => f (diskMobius 0 a z)) g F ∧
        IsClosedDiskHomeo F ∧ F 0 = 0 ∧ IsDiskBiLip F L ∧ IsKQC F unitDisc L ∧
        (∀ z ∈ closedBall (0 : ℂ) 1, Fi (F z) = z ∧ F (Fi z) = z) ∧
        ∀ ζ ∈ sphere (0 : ℂ) 1, diskMobius 0 a (F ζ) = h ζ := by
  obtain ⟨L, hL, hde⟩ := s07d_p3_de_qc (K * K) (one_le_mul_of_one_le_of_one_le hK hK)
  refine ⟨L, hL, fun Ω Ωs hq f g h hw => ?_⟩
  have hext := s07_weld_admitsExt hq hw
  obtain ⟨H₀, hH₀q, hH₀s, hH₀b⟩ := id hext
  have hh : IsCircleHomeo h := s07_circleHomeo_of_qcExt hH₀q hH₀s hH₀b
  obtain ⟨F₁, F₁i, hF₁, hF₁h, hF₁b, hF₁q, hF₁i⟩ := hde h hh hext
  have hsph : ∀ ζ ∈ sphere (0 : ℂ) 1, F₁ ζ ∈ sphere (0 : ℂ) 1 := fun ζ hζ => by
    rw [hF₁h hζ]
    exact hw.2.2.2.1 hζ
  obtain ⟨hF₁D, -⟩ := s07d_p3_disk_onto hF₁ hF₁q hsph
  set b : ℂ := F₁ 0 with hbdef
  have hbD : b ∈ unitDisc := hF₁D 0 (mem_ball_self one_pos)
  have hb : ‖b‖ < 1 := mem_ball_zero_iff.mp hbD
  have hb' : ‖-b‖ < 1 := by rwa [norm_neg]
  have hF₁cb : ∀ z ∈ closedBall (0 : ℂ) 1, ‖F₁ z‖ ≤ 1 := fun z hz =>
    mem_closedBall_zero_iff.mp (hF₁.1.mapsTo hz)
  set F : ℂ → ℂ := fun z => diskAut b (F₁ z) with hFdef
  set Fi : ℂ → ℂ := fun w => F₁i (diskAut (-b) w) with hFidef
  have hdcb : ∀ c : ℂ, ‖c‖ < 1 → ∀ u : ℂ, ‖u‖ ≤ 1 → diskAut c u ∈ closedBall (0 : ℂ) 1 :=
    fun c hc u hu => mem_closedBall_zero_iff.mpr (diskAut_norm_le_one c u hc hu)
  have hinv : ∀ z ∈ closedBall (0 : ℂ) 1, Fi (F z) = z ∧ F (Fi z) = z := by
    intro z hz
    constructor
    · show F₁i (diskAut (-b) (diskAut b (F₁ z))) = z
      rw [s07d_p3_diskAut_inv hb (hF₁cb z hz)]
      exact (hF₁i z hz).1
    · show diskAut b (F₁ (F₁i (diskAut (-b) z))) = z
      rw [(hF₁i _ (hdcb (-b) hb' z (mem_closedBall_zero_iff.mp hz))).2]
      exact diskAut_neg_left_inv hb (mem_closedBall_zero_iff.mp hz)
  have hFmaps : MapsTo F (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := fun z hz =>
    hdcb b hb _ (hF₁cb z hz)
  have hFimaps : MapsTo Fi (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
    intro w hw
    obtain ⟨x, hx, hxy⟩ := hF₁.1.surjOn (hdcb (-b) hb' w (mem_closedBall_zero_iff.mp hw))
    show F₁i (diskAut (-b) w) ∈ closedBall (0 : ℂ) 1
    rw [← hxy, (hF₁i x hx).1]
    exact hx
  have hFcd : IsClosedDiskHomeo F := by
    refine ⟨InvOn.bijOn ⟨fun z hz => (hinv z hz).1, fun z hz => (hinv z hz).2⟩ hFmaps hFimaps,
      ?_⟩
    intro z hz
    have h1 : ContinuousAt (diskAut b) (F₁ z) :=
      (diskAut_differentiableAt b (F₁ z) hb (hF₁cb z hz)).continuousAt
    exact h1.comp_continuousWithinAt (hF₁.2 z hz)
  have hF0 : F 0 = 0 := diskAut_self b hb
  have hFD1 : ∀ z ∈ unitDisc, F₁ z ∈ unitDisc := hF₁D
  have hFbl : IsDiskBiLip F L := by
    intro x hx y hy
    have e : diskDist (F x) (F y) = diskDist (F₁ x) (F₁ y) :=
      s07d_p3_dd_inv hbD (hFD1 x hx) (hFD1 y hy)
    rw [e]
    exact hF₁b x hx y hy
  have hFq : IsKQC F unitDisc L := by
    have hbl : IsKQC (blaschke b) unitDisc 1 :=
      isKQC_one_of_conformal isOpen_ball (isConformalOnto_blaschke hb)
    have h1 := thm7_1_comp hF₁q hbl (image_subset_iff.2 fun z hz => hFD1 z hz)
    rw [mul_one] at h1
    exact ad_isKQC_congr h1 fun z _ => rfl
  have ha : ‖-b‖ < 1 := hb'
  obtain ⟨hw', -⟩ := s07b_weld_mobius hw hh 0 0 ha
  have hg : (fun w => g (exp (-(((0 : ℝ) : ℂ) * I)) * w)) = g := by
    funext w
    simp
  rw [hg] at hw'
  refine ⟨F, Fi, -b, mem_ball_zero_iff.mpr ha, s07d_p3_weld_congr hw' fun ζ hζ => ?_, hFcd, hF0,
    hFbl, hFq, hinv, fun ζ hζ => ?_⟩
  · show diskMobius (-0) (-(exp (((0 : ℝ) : ℂ) * I) * -b)) (h (exp (-(((0 : ℝ) : ℂ) * I)) * ζ)) =
      diskAut b (F₁ ζ)
    have e1 : exp (-(((0 : ℝ) : ℂ) * I)) * ζ = ζ := by simp
    have e2 : -(exp (((0 : ℝ) : ℂ) * I) * -b) = b := by simp
    rw [e1, e2, ← hF₁h hζ]
    show exp (((-0 : ℝ) : ℂ) * I) * ((F₁ ζ - b) / (1 - conj b * F₁ ζ)) = diskAut b (F₁ ζ)
    rw [neg_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
    rfl
  · show exp (((0 : ℝ) : ℂ) * I) * ((F ζ - -b) / (1 - conj (-b) * F ζ)) = h ζ
    rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
    show diskAut (-b) (diskAut b (F₁ ζ)) = h ζ
    rw [s07d_p3_diskAut_inv hb (hF₁cb ζ (sphere_subset_closedBall hζ)), hF₁h hζ]

/-- P3 helper: the two sides of a bounded quasicircle are open and disjoint, and the curve is
nonempty. -/
theorem s07d_p3_qc_top {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K) :
    IsOpen Ω ∧ IsOpen Ωs ∧ Disjoint Ω Ωs ∧ (curveOf Ω Ωs).Nonempty := by
  obtain ⟨F₀, hF₀q, hF₀s, hF₀D, hF₀E⟩ := id hq
  have hi : Function.Injective F₀ := injOn_univ.mp hF₀q.2.2.1.2.1
  obtain ⟨T, hT⟩ := t1_homeomorph hF₀q hF₀s
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hF₀D, ← hT]
    exact T.isOpenMap _ isOpen_ball
  · rw [← hF₀E, ← hT]
    exact T.isOpenMap _ hEo
  · rw [← hF₀D, ← hF₀E, disjoint_image_iff hi]
    refine Set.disjoint_left.2 fun x h1 h2 => ?_
    have h1' : ‖x‖ < 1 := mem_ball_zero_iff.mp h1
    have h2' : 1 < ‖x‖ := h2
    linarith
  · rw [s03_cb_curve hi hF₀s hF₀D hF₀E]
    exact ⟨F₀ 1, 1, by simp, rfl⟩

/-- P3 helper (points on opposite sides): if `z ∈ U` and `w ∉ U`, both `z` and `w` are within
`|z - w|` of the curve. -/
theorem s07d_p3_opp {U V : Set ℂ} (hUo : IsOpen U) (hVo : IsOpen V) (hdisj : Disjoint U V)
    (hne : (curveOf U V).Nonempty) {z w : ℂ} (hz : z ∈ U) (hw : w ∉ U) :
    infDist z (curveOf U V) ≤ ‖z - w‖ ∧ infDist w (curveOf U V) ≤ ‖z - w‖ := by
  have hc1 := s07d_p3_infDist_compl hUo hVo hdisj hne hz
  constructor
  · rw [← hc1, ← dist_eq_norm]
    exact infDist_le_dist_of_mem hw
  · by_cases hwV : w ∈ V
    · have hswap : curveOf V U = curveOf U V := by
        show (V ∪ U)ᶜ = (U ∪ V)ᶜ
        rw [union_comm]
      have hne' : (curveOf V U).Nonempty := by rw [hswap]; exact hne
      have hc2 := s07d_p3_infDist_compl hVo hUo hdisj.symm hne' hwV
      rw [hswap] at hc2
      rw [← hc2, norm_sub_rev, ← dist_eq_norm]
      exact infDist_le_dist_of_mem fun h => Set.disjoint_left.1 hdisj hz h
    · have hwc : w ∈ curveOf U V := by
        show w ∉ U ∪ V
        exact fun h => h.elim hw hwV
      rw [infDist_zero_of_mem hwc]
      exact norm_nonneg _

/-- P3 helper: `jRefl ∘ Fi ∘ jRefl` maps `𝔻*` onto `𝔻*` when `F` maps `𝔻` onto `𝔻` with
`F 0 = 0`. -/
theorem s07d_p3_E_ext {F Fi : ℂ → ℂ} (hF : IsClosedDiskHomeo F) (hF0 : F 0 = 0)
    (hFD : ∀ z ∈ unitDisc, F z ∈ unitDisc) (hFs : F '' unitDisc = unitDisc)
    (hFi : ∀ z ∈ closedBall (0 : ℂ) 1, Fi (F z) = z ∧ F (Fi z) = z) :
    (fun z => jRefl (Fi (jRefl z))) '' unitDiscExterior = unitDiscExterior := by
  have hFiD : ∀ v ∈ unitDisc, Fi v ∈ unitDisc ∧ (v ≠ 0 → Fi v ≠ 0) := by
    intro v hv
    have hv' : v ∈ F '' unitDisc := by rw [hFs]; exact hv
    obtain ⟨x, hx, rfl⟩ := hv'
    rw [(hFi x (ball_subset_closedBall hx)).1]
    refine ⟨hx, fun h1 h2 => h1 ?_⟩
    rw [h2, hF0]
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨h1, h2⟩ := s07d_p3_jRefl_ext hz
    exact s07d_p3_jRefl_int (hFiD _ h1).1 ((hFiD _ h1).2 h2)
  · intro hw
    obtain ⟨h1, h2⟩ := s07d_p3_jRefl_ext hw
    have hF1 : F (jRefl w) ≠ 0 := fun h =>
      h2 (hF.1.injOn (ball_subset_closedBall h1) (mem_closedBall_self zero_le_one) (h.trans hF0.symm))
    refine ⟨jRefl (F (jRefl w)), s07d_p3_jRefl_int (hFD _ h1) hF1, ?_⟩
    show jRefl (Fi (jRefl (jRefl (F (jRefl w))))) = w
    rw [s07d_p3_jRefl_jRefl, (hFi _ (ball_subset_closedBall h1)).1, s07d_p3_jRefl_jRefl]

/-- P3 helper (displacement on the collar): if `ρ` moves points of `Ωs` by `≤ C d(·, Γ)`, with
`min(d(a), diam Γ) ≤ C d(ρ a)`, and the point `x₀` sent to `∞` is deep, then on the collar
`d(x) < c diam Γ` with `c C < 1`, `ρ` moves points by `≤ C² d(x)`, is an involution, avoids `x₀`
and `d(ρ x) ≤ (1 + C²) d(x)`. -/
theorem s07d_p3_col_disp {Ω Ωs : Set ℂ} {ρ : ℂ → ℂ} {x₀ : ℂ} {C c : ℝ} (hC : 1 ≤ C)
    (hcC : c * C < 1) (hR2 : ∀ x ∈ curveOf Ω Ωs, ρ x = x)
    (hR3 : ∀ z ∈ Ω, z ≠ x₀ → ρ z ∈ Ωs ∧ ρ (ρ z) = z)
    (hR4 : ∀ z ∈ Ωs, ρ z ∈ Ω ∧ ρ z ≠ x₀ ∧ ρ (ρ z) = z)
    (hdS : ∀ x ∈ Ωs, ‖ρ x - x‖ ≤ C * infDist x (curveOf Ω Ωs) ∧
      min (infDist x (curveOf Ω Ωs)) (diam (curveOf Ω Ωs)) ≤ C * infDist (ρ x) (curveOf Ω Ωs))
    (hx₀ : diam (curveOf Ω Ωs) ≤ C * infDist x₀ (curveOf Ω Ωs)) (x : ℂ)
    (hx : infDist x (curveOf Ω Ωs) < c * diam (curveOf Ω Ωs)) :
    ‖ρ x - x‖ ≤ C * C * infDist x (curveOf Ω Ωs) ∧ ρ (ρ x) = x ∧ x ≠ x₀ ∧
      infDist (ρ x) (curveOf Ω Ωs) ≤ (1 + C * C) * infDist x (curveOf Ω Ωs) := by
  set Γ := curveOf Ω Ωs with hΓdef
  have hΔ : 0 ≤ diam Γ := diam_nonneg
  have hkey : ∀ t : ℝ, t < c * diam Γ → diam Γ ≤ C * t → False := by
    intro t h1 h2
    have h3 : C * t < C * (c * diam Γ) := mul_lt_mul_of_pos_left h1 (by linarith)
    have h4 : c * C * diam Γ ≤ 1 * diam Γ := mul_le_mul_of_nonneg_right hcC.le hΔ
    have h5 : C * (c * diam Γ) = c * C * diam Γ := by ring
    linarith
  have hd0 : 0 ≤ infDist x Γ := infDist_nonneg
  have hx0 : x ≠ x₀ := by
    intro h
    exact hkey _ hx (by rw [h]; exact hx₀)
  have hmain : ‖ρ x - x‖ ≤ C * C * infDist x Γ ∧ ρ (ρ x) = x := by
    by_cases hxΩ : x ∈ Ω
    · obtain ⟨haS, hρρ⟩ := hR3 x hxΩ hx0
      obtain ⟨hd1, hd2⟩ := hdS (ρ x) haS
      rw [hρρ] at hd1 hd2
      have hda : infDist (ρ x) Γ ≤ C * infDist x Γ := by
        by_cases h : infDist (ρ x) Γ ≤ diam Γ
        · rwa [min_eq_left h] at hd2
        · exfalso
          rw [min_eq_right (le_of_not_ge h)] at hd2
          exact hkey _ hx hd2
      refine ⟨?_, hρρ⟩
      rw [norm_sub_rev]
      calc ‖x - ρ x‖ ≤ C * infDist (ρ x) Γ := hd1
        _ ≤ C * (C * infDist x Γ) := mul_le_mul_of_nonneg_left hda (by linarith)
        _ = C * C * infDist x Γ := by ring
    · by_cases hxS : x ∈ Ωs
      · refine ⟨(hdS x hxS).1.trans ?_, (hR4 x hxS).2.2⟩
        have h1 : C * 1 ≤ C * C := mul_le_mul_of_nonneg_left hC (by linarith)
        have h2 : C * infDist x Γ ≤ C * C * infDist x Γ := by
          have := mul_le_mul_of_nonneg_right h1 hd0
          linarith
        exact h2
      · have hxΓ : x ∈ Γ := by
          show x ∉ Ω ∪ Ωs
          exact fun h => h.elim hxΩ hxS
        rw [hR2 x hxΓ, hR2 x hxΓ, sub_self, norm_zero]
        exact ⟨mul_nonneg (by nlinarith) hd0, rfl⟩
  refine ⟨hmain.1, hmain.2, hx0, ?_⟩
  have h1 := infDist_le_infDist_add_dist (s := Γ) (x := ρ x) (y := x)
  rw [dist_eq_norm] at h1
  linarith [hmain.1]

/-- P3 helper (small scale, same side): on the collar `d < c diam Γ` (with `c (1 + P) ≤ 1`), if
`|z - w| < ε d(z)` then `|ρ z - ρ w| ≤ S |z - w|`. Koebe on the side of `z` (P3.2 or P3.3, converse)
gives `d_𝔻 ≤ C ε` for the preimages; the bi-Lipschitz `F` carries this to the other side, where the
forward Koebe bound (P3.3 or P3.2) applies. -/
theorem s07d_p3_col_small (K L₀ P c : ℝ) (hK : 1 ≤ K) (hL₀ : 1 ≤ L₀) (hP : 0 ≤ P) (hc : 0 < c)
    (hcP : c * (1 + P) ≤ 1) : ∃ ε S : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ 0 ≤ S ∧
    ∀ (Ω Ωs : Set ℂ) (f g F Fi ρ : ℂ → ℂ) (x₀ : ℂ), IsBoundedKQuasicircle Ω Ωs K →
      IsDiskWelding Ω Ωs f g F → IsDiskBiLip F L₀ →
      (∀ z ∈ closedBall (0 : ℂ) 1, Fi (F z) = z ∧ F (Fi z) = z) →
      (∀ x ∈ Ωs, ∃ u ∈ unitDisc, u ≠ 0 ∧ F u ∈ unitDisc ∧ x = g (jRefl u) ∧ ρ x = f (F u)) →
      (∀ x ∈ Ω, x ≠ x₀ → ∃ v ∈ unitDisc, v ≠ 0 ∧ Fi v ∈ unitDisc ∧ Fi v ≠ 0 ∧ x = f v ∧
        ρ x = g (jRefl (Fi v))) →
      (∀ x : ℂ, infDist x (curveOf Ω Ωs) < c * diam (curveOf Ω Ωs) →
        x ≠ x₀ ∧ infDist (ρ x) (curveOf Ω Ωs) ≤ (1 + P) * infDist x (curveOf Ω Ωs)) →
      ∀ z w : ℂ, infDist z (curveOf Ω Ωs) < c * diam (curveOf Ω Ωs) →
        infDist w (curveOf Ω Ωs) < c * diam (curveOf Ω Ωs) →
        ‖z - w‖ < ε * infDist z (curveOf Ω Ωs) → ‖ρ z - ρ w‖ ≤ S * ‖z - w‖ := by
  obtain ⟨C₂, hC₂, hKi⟩ := s07d_p3_koebe_int 1 zero_le_one
  obtain ⟨C₃, hC₃, hKe⟩ := s07d_p3_koebe_ext K 1 hK zero_le_one
  set M : ℝ := L₀ * C₂ * C₃ with hMdef
  have hLC₂ : 1 ≤ L₀ * C₂ := one_le_mul_of_one_le_of_one_le hL₀ hC₂
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hLC₂ hC₃
  set ε : ℝ := 1 / (2 * M) with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hMε : M * ε = 1 / 2 := by
    rw [hεdef]
    field_simp
  have hXε : ∀ X : ℝ, X ≤ M → X * ε ≤ 1 := by
    intro X hX
    have := mul_le_mul_of_nonneg_right hX hε.le
    linarith
  have hε2 : ε ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_right hM hε.le
    linarith
  have hL₀C₂ : L₀ * C₂ ≤ M := by
    have := mul_le_mul_of_nonneg_left hC₃ (by linarith : (0 : ℝ) ≤ L₀ * C₂)
    rw [hMdef]
    linarith
  have hL₀C₃ : L₀ * C₃ ≤ M := by
    have := mul_le_mul_of_nonneg_right hC₂ (mul_nonneg (by linarith) (by linarith) : (0 : ℝ) ≤ L₀ * C₃)
    have e : C₂ * (L₀ * C₃) = L₀ * C₂ * C₃ := by ring
    rw [hMdef]
    linarith
  have hc1 : c ≤ 1 := by nlinarith
  refine ⟨ε, C₂ * C₃ * L₀ * (1 + P), hε, hε2, by positivity, ?_⟩
  intro Ω Ωs f g F Fi ρ x₀ hq hw hFb hFi hrS hrΩ hcol z w hz hw' hzw
  obtain ⟨hΩo, hΩso, hdisj, hne⟩ := s07d_p3_qc_top hq
  set Γ := curveOf Ω Ωs with hΓdef
  have hΔ : 0 ≤ diam Γ := diam_nonneg
  have hd0 : 0 < infDist z Γ := by
    by_contra h
    have h1 : ε * infDist z Γ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε.le (not_lt.mp h)
    linarith [norm_nonneg (z - w)]
  have hzw2 : ‖z - w‖ ≤ infDist z Γ / 2 := by
    have := mul_le_mul_of_nonneg_right hε2 hd0.le
    linarith
  have hzw1 : ‖z - w‖ < infDist z Γ := by linarith
  have hcΔ : ∀ x : ℂ, infDist x Γ < c * diam Γ → infDist x Γ ≤ diam Γ := by
    intro x hx
    have := mul_le_mul_of_nonneg_right hc1 hΔ
    linarith
  have hρΔ : ∀ x : ℂ, infDist x Γ < c * diam Γ → infDist (ρ x) Γ ≤ diam Γ := by
    intro x hx
    have h1 := (hcol x hx).2
    have h2 : (1 + P) * infDist x Γ ≤ (1 + P) * (c * diam Γ) :=
      mul_le_mul_of_nonneg_left hx.le (by linarith)
    have h3 : (1 + P) * (c * diam Γ) = c * (1 + P) * diam Γ := by ring
    have h4 := mul_le_mul_of_nonneg_right hcP hΔ
    linarith
  have hzΓ : z ∉ Γ := fun h => by
    rw [infDist_zero_of_mem h] at hd0
    exact lt_irrefl _ hd0
  have hzU : z ∈ Ω ∪ Ωs := not_not.mp hzΓ
  rcases hzU with hzΩ | hzS
  · -- `z ∈ Ω`: Koebe inside (converse), then Koebe outside (forward)
    have hwΩ : w ∈ Ω := by
      by_contra hwΩ
      have := (s07d_p3_opp hΩo hΩso hdisj hne hzΩ hwΩ).1
      linarith
    obtain ⟨v, hv, hv0, hFiv, hFiv0, hzv, hρz⟩ := hrΩ z hzΩ (hcol z hz).1
    obtain ⟨v', hv', hv0', hFiv', hFiv0', hwv, hρw⟩ := hrΩ w hwΩ (hcol w hw').1
    have hc1 := s07d_p3_infDist_compl hΩo hΩso hdisj hne hzΩ
    obtain ⟨-, hconv⟩ := hKi Ω f hw.1 v hv v' hv'
    have h1 : diskDist v v' * infDist z Γ ≤ C₂ * ‖z - w‖ := by
      rw [← hc1, hzv, hwv]
      refine hconv ?_
      rw [← hzv, ← hwv, hc1]
      exact hzw2
    have hdd : diskDist v v' ≤ C₂ * ε := by
      refine le_of_mul_le_mul_right ?_ hd0
      calc diskDist v v' * infDist z Γ ≤ C₂ * ‖z - w‖ := h1
        _ ≤ C₂ * (ε * infDist z Γ) := mul_le_mul_of_nonneg_left hzw.le (by linarith)
        _ = C₂ * ε * infDist z Γ := by ring
    have hFv : F (Fi v) = v := (hFi v (ball_subset_closedBall hv)).2
    have hFv' : F (Fi v') = v' := (hFi v' (ball_subset_closedBall hv')).2
    have h2 : diskDist (Fi v) (Fi v') ≤ L₀ * diskDist v v' := by
      have := (hFb (Fi v) hFiv (Fi v') hFiv').2
      rwa [hFv, hFv'] at this
    have hD1 : diskDist (Fi v) (Fi v') ≤ 1 := by
      have h3 : L₀ * diskDist v v' ≤ L₀ * (C₂ * ε) := mul_le_mul_of_nonneg_left hdd (by linarith)
      have h4 := hXε (L₀ * C₂) hL₀C₂
      have h5 : L₀ * (C₂ * ε) = L₀ * C₂ * ε := by ring
      linarith
    have hρzΔ : infDist (g (jRefl (Fi v))) Γ ≤ diam Γ := by rw [← hρz]; exact hρΔ z hz
    have hρwΔ : infDist (g (jRefl (Fi v'))) Γ ≤ diam Γ := by rw [← hρw]; exact hρΔ w hw'
    obtain ⟨hfwd, -⟩ :=
      hKe Ω Ωs g hq hw.2.1 hw.2.2.1 (Fi v) hFiv (Fi v') hFiv' hFiv0 hFiv0' hρzΔ hρwΔ
    have h3 := (hfwd hD1).1
    rw [← hρz, ← hρw] at h3
    have hA : C₃ * diskDist (Fi v) (Fi v') ≤ C₃ * (L₀ * diskDist v v') :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have hB : infDist (ρ z) Γ ≤ (1 + P) * infDist z Γ := (hcol z hz).2
    have hvv : 0 ≤ diskDist v v' := s02_diskDist_nonneg hv hv'
    have e1 := mul_le_mul hA hB infDist_nonneg
      (mul_nonneg (by linarith) (mul_nonneg (by linarith) hvv))
    have e2 : C₃ * (L₀ * diskDist v v') * ((1 + P) * infDist z Γ) =
        C₃ * L₀ * (1 + P) * (diskDist v v' * infDist z Γ) := by ring
    have e3 : C₃ * L₀ * (1 + P) * (diskDist v v' * infDist z Γ) ≤
        C₃ * L₀ * (1 + P) * (C₂ * ‖z - w‖) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e4 : C₃ * L₀ * (1 + P) * (C₂ * ‖z - w‖) = C₂ * C₃ * L₀ * (1 + P) * ‖z - w‖ := by ring
    linarith
  · -- `z ∈ Ωs`: Koebe outside (converse), then Koebe inside (forward)
    have hswap : curveOf Ωs Ω = Γ := by
      show (Ωs ∪ Ω)ᶜ = (Ω ∪ Ωs)ᶜ
      rw [union_comm]
    have hwS : w ∈ Ωs := by
      by_contra hwS
      have hne' : (curveOf Ωs Ω).Nonempty := by rw [hswap]; exact hne
      have := (s07d_p3_opp hΩso hΩo hdisj.symm hne' hzS hwS).1
      rw [hswap] at this
      linarith
    obtain ⟨u, hu, hu0, hFu, hzu, hρz⟩ := hrS z hzS
    obtain ⟨u', hu', hu0', hFu', hwu, hρw⟩ := hrS w hwS
    have hzΔ : infDist (g (jRefl u)) Γ ≤ diam Γ := by rw [← hzu]; exact hcΔ z hz
    have hwΔ : infDist (g (jRefl u')) Γ ≤ diam Γ := by rw [← hwu]; exact hcΔ w hw'
    obtain ⟨-, hconv⟩ := hKe Ω Ωs g hq hw.2.1 hw.2.2.1 u hu u' hu' hu0 hu0' hzΔ hwΔ
    have h1 : diskDist u u' * infDist z Γ ≤ C₃ * ‖z - w‖ := by
      rw [hzu, hwu]
      refine hconv ?_
      rw [← hzu, ← hwu]
      exact hzw2
    have hdd : diskDist u u' ≤ C₃ * ε := by
      refine le_of_mul_le_mul_right ?_ hd0
      calc diskDist u u' * infDist z Γ ≤ C₃ * ‖z - w‖ := h1
        _ ≤ C₃ * (ε * infDist z Γ) := mul_le_mul_of_nonneg_left hzw.le (by linarith)
        _ = C₃ * ε * infDist z Γ := by ring
    have h2 : diskDist (F u) (F u') ≤ L₀ * diskDist u u' := (hFb u hu u' hu').1
    have hD1 : diskDist (F u) (F u') ≤ 1 := by
      have h3 : L₀ * diskDist u u' ≤ L₀ * (C₃ * ε) := mul_le_mul_of_nonneg_left hdd (by linarith)
      have h4 := hXε (L₀ * C₃) hL₀C₃
      have h5 : L₀ * (C₃ * ε) = L₀ * C₃ * ε := by ring
      linarith
    obtain ⟨hfwd, -⟩ := hKi Ω f hw.1 (F u) hFu (F u') hFu'
    have h3 := (hfwd hD1).1
    rw [← hρz, ← hρw] at h3
    have hsub : Γ ⊆ Ωᶜ := fun x hx hxΩ => hx (Or.inl hxΩ)
    have h4 : infDist (ρ z) Ωᶜ ≤ infDist (ρ z) Γ := infDist_le_infDist_of_subset hsub hne
    have hB : infDist (ρ z) Ωᶜ ≤ (1 + P) * infDist z Γ := h4.trans (hcol z hz).2
    have hA : C₂ * diskDist (F u) (F u') ≤ C₂ * (L₀ * diskDist u u') :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have huu : 0 ≤ diskDist u u' := s02_diskDist_nonneg hu hu'
    have e1 := mul_le_mul hA hB infDist_nonneg
      (mul_nonneg (by linarith) (mul_nonneg (by linarith) huu))
    have e2 : C₂ * (L₀ * diskDist u u') * ((1 + P) * infDist z Γ) =
        C₂ * L₀ * (1 + P) * (diskDist u u' * infDist z Γ) := by ring
    have e3 : C₂ * L₀ * (1 + P) * (diskDist u u' * infDist z Γ) ≤
        C₂ * L₀ * (1 + P) * (C₃ * ‖z - w‖) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e4 : C₂ * L₀ * (1 + P) * (C₃ * ‖z - w‖) = C₂ * C₃ * L₀ * (1 + P) * ‖z - w‖ := by ring
    linarith

/-- P3 helper (the collar bi-Lipschitz bound). On the collar `d(·, Γ) < c₀ diam Γ` the reflection
`ρ` is `L`-bi-Lipschitz.
Choice of the collar: with `C₅` from P3.5, `P = C₅²`, `c = 1/(2(1 + P))` gives `c C₅ < 1` (so the
deep point `x₀ = Φ 0`, with `diam Γ ≤ C₅ d(x₀)`, is off the collar, and `min(d(ρ x), diam Γ) =
d(ρ x)` there) and `c (1 + P) ≤ 1` (so `ρ` of a collar point satisfies the hypothesis
`d ≤ diam Γ` of P3.3). The upper bound holds on the collar `c`; the lower bound applies it to
`ρ z, ρ w`, which lie in the collar `c` when `z, w` lie in `c₀ = c/(1 + P)`. -/
theorem s07d_p3_collar (K L₀ : ℝ) (hK : 1 ≤ K) (hL₀ : 1 ≤ L₀) : ∃ L c₀ : ℝ, L₀ ≤ L ∧ 0 < c₀ ∧
    ∀ (Ω Ωs : Set ℂ) (f g F Fi ρ : ℂ → ℂ) (x₀ : ℂ), IsBoundedKQuasicircle Ω Ωs K →
      IsDiskWelding Ω Ωs f g F → IsClosedDiskHomeo F → F 0 = 0 → IsDiskBiLip F L₀ →
      (∀ z ∈ closedBall (0 : ℂ) 1, Fi (F z) = z ∧ F (Fi z) = z) → x₀ = f 0 →
      (∀ x ∈ curveOf Ω Ωs, ρ x = x) →
      (∀ z ∈ Ω, z ≠ x₀ → ρ z ∈ Ωs ∧ ρ (ρ z) = z) →
      (∀ z ∈ Ωs, ρ z ∈ Ω ∧ ρ z ≠ x₀ ∧ ρ (ρ z) = z) →
      (∀ x ∈ Ωs, ∃ u ∈ unitDisc, u ≠ 0 ∧ F u ∈ unitDisc ∧ x = g (jRefl u) ∧ ρ x = f (F u)) →
      (∀ x ∈ Ω, x ≠ x₀ → ∃ v ∈ unitDisc, v ≠ 0 ∧ Fi v ∈ unitDisc ∧ Fi v ≠ 0 ∧ x = f v ∧
        ρ x = g (jRefl (Fi v))) →
      ∀ z w : ℂ, infDist z (curveOf Ω Ωs) < c₀ * diam (curveOf Ω Ωs) →
        infDist w (curveOf Ω Ωs) < c₀ * diam (curveOf Ω Ωs) →
          ‖ρ z - ρ w‖ ≤ L * ‖z - w‖ ∧ ‖z - w‖ ≤ L * ‖ρ z - ρ w‖ := by
  obtain ⟨C₅, hC₅, hdisp⟩ := s07d_p3_displacement K L₀ hK hL₀
  set P : ℝ := C₅ * C₅ with hPdef
  have hP0 : 0 ≤ P := by positivity
  have hPC : C₅ ≤ P := by nlinarith
  set c : ℝ := 1 / (2 * (1 + P)) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hcP' : c * (1 + P) = 1 / 2 := by
    rw [hcdef]
    field_simp
  have hcP : c * (1 + P) ≤ 1 := by linarith
  have hcC : c * C₅ < 1 := by
    have := mul_le_mul_of_nonneg_left (by linarith : C₅ ≤ 1 + P) hc0.le
    linarith
  obtain ⟨ε, S, hε, -, hS, hsmall⟩ := s07d_p3_col_small K L₀ P c hK hL₀ hP0 hc0 hcP
  set U : ℝ := S + 1 + 2 * P / ε with hUdef
  have hU0 : 0 ≤ U := by rw [hUdef]; positivity
  have hP1 : 0 < 1 + P := by linarith
  refine ⟨U + L₀, c / (1 + P), by linarith, div_pos hc0 hP1, ?_⟩
  intro Ω Ωs f g F Fi ρ x₀ hq hw hF hF0 hFb hFi hx₀ hR2 hR3 hR4 hrS hrΩ z w hz hw'
  set Γ := curveOf Ω Ωs with hΓdef
  have hΔ : 0 ≤ diam Γ := diam_nonneg
  obtain ⟨hd1, hd3⟩ := hdisp Ω Ωs f g F F hq hw hF (fun _ _ => rfl) hFb
  have hdS : ∀ x ∈ Ωs, ‖ρ x - x‖ ≤ C₅ * infDist x Γ ∧
      min (infDist x Γ) (diam Γ) ≤ C₅ * infDist (ρ x) Γ := by
    intro x hx
    obtain ⟨u, hu, hu0, -, hxu, hρx⟩ := hrS x hx
    obtain ⟨h1, h2⟩ := hd1 u hu hu0
    rw [hρx, hxu]
    exact ⟨h1, h2⟩
  have hx₀' : diam Γ ≤ C₅ * infDist x₀ Γ := by
    rw [hx₀]
    have := hd3
    rwa [hF0] at this
  have hcol : ∀ x : ℂ, infDist x Γ < c * diam Γ →
      ‖ρ x - x‖ ≤ P * infDist x Γ ∧ ρ (ρ x) = x ∧ x ≠ x₀ ∧
        infDist (ρ x) Γ ≤ (1 + P) * infDist x Γ := fun x hx =>
    s07d_p3_col_disp hC₅ hcC hR2 hR3 hR4 hdS hx₀' x hx
  have hsm := hsmall Ω Ωs f g F Fi ρ x₀ hq hw hFb hFi hrS hrΩ fun x hx =>
    ⟨(hcol x hx).2.2.1, (hcol x hx).2.2.2⟩
  have hSU : S ≤ U := by
    have : 0 ≤ 2 * P / ε := by positivity
    rw [hUdef]
    linarith
  -- the upper bound on the collar `c`
  have hup : ∀ z w : ℂ, infDist z Γ < c * diam Γ → infDist w Γ < c * diam Γ →
      ‖ρ z - ρ w‖ ≤ U * ‖z - w‖ := by
    intro z w hz hw
    by_cases h1 : ‖z - w‖ < ε * infDist z Γ
    · exact (hsm z w hz hw h1).trans (mul_le_mul_of_nonneg_right hSU (norm_nonneg _))
    · by_cases h2 : ‖w - z‖ < ε * infDist w Γ
      · have := hsm w z hw hz h2
        rw [norm_sub_rev (ρ w), norm_sub_rev w] at this
        exact this.trans (mul_le_mul_of_nonneg_right hSU (norm_nonneg _))
      · rw [not_lt] at h1 h2
        rw [norm_sub_rev w] at h2
        have hdz : infDist z Γ ≤ ‖z - w‖ / ε := by
          rw [le_div_iff₀ hε]
          linarith
        have hdw : infDist w Γ ≤ ‖z - w‖ / ε := by
          rw [le_div_iff₀ hε]
          linarith
        have hmz := (hcol z hz).1
        have hmw := (hcol w hw).1
        have htri : ‖ρ z - ρ w‖ ≤ ‖ρ z - z‖ + ‖z - w‖ + ‖w - ρ w‖ := by
          have e : ρ z - ρ w = (ρ z - z) + (z - w) + (w - ρ w) := by abel
          rw [e]
          linarith [norm_add_le (ρ z - z) (z - w), norm_add_le (ρ z - z + (z - w)) (w - ρ w)]
        rw [norm_sub_rev w] at htri
        have h3 : P * infDist z Γ ≤ P * (‖z - w‖ / ε) := mul_le_mul_of_nonneg_left hdz hP0
        have h4 : P * infDist w Γ ≤ P * (‖z - w‖ / ε) := mul_le_mul_of_nonneg_left hdw hP0
        have h5 : U * ‖z - w‖ = S * ‖z - w‖ + ‖z - w‖ + 2 * (P * (‖z - w‖ / ε)) := by
          rw [hUdef]
          ring
        have h6 : 0 ≤ S * ‖z - w‖ := mul_nonneg hS (norm_nonneg _)
        linarith
  have hc₀c : c / (1 + P) * diam Γ ≤ c * diam Γ := by
    apply mul_le_mul_of_nonneg_right _ hΔ
    rw [div_le_iff₀ hP1]
    nlinarith
  have hzc : infDist z Γ < c * diam Γ := lt_of_lt_of_le hz hc₀c
  have hwc : infDist w Γ < c * diam Γ := lt_of_lt_of_le hw' hc₀c
  have hρc : ∀ x : ℂ, infDist x Γ < c / (1 + P) * diam Γ → infDist (ρ x) Γ < c * diam Γ := by
    intro x hx
    have h1 := (hcol x (lt_of_lt_of_le hx hc₀c)).2.2.2
    have h2 : (1 + P) * infDist x Γ < (1 + P) * (c / (1 + P) * diam Γ) :=
      mul_lt_mul_of_pos_left hx hP1
    have h3 : (1 + P) * (c / (1 + P) * diam Γ) = c * diam Γ := by
      field_simp
    linarith
  have hUL : ∀ t : ℝ, 0 ≤ t → U * t ≤ (U + L₀) * t := fun t ht =>
    mul_le_mul_of_nonneg_right (by linarith) ht
  refine ⟨(hup z w hzc hwc).trans (hUL _ (norm_nonneg _)), ?_⟩
  have h1 := hup (ρ z) (ρ w) (hρc z hz) (hρc w hw')
  rw [(hcol z hzc).2.1, (hcol w hwc).2.1] at h1
  exact h1.trans (hUL _ (norm_nonneg _))

/-- **P3 data** (consumer form for P6; leader-approved addition 2026-11-06). This is the construction
behind `s07d_p3_reflection` for a given welding `(f, g, h)`, with its internal data exposed:
* `F` is the extension of the normalised welding `M⁻¹ ∘ h` (`M = diskMobius 0 a`): a closed-disk
  homeomorphism with `F 0 = 0`, `L`-bi-Lipschitz for `d_𝔻`, and `L`-q.c. on `𝔻`;
* `Fi` is its inverse on `𝔻̄`;
* `Φ = f ∘ M` on `𝔻` and `Φ = g ∘ jRefl ∘ Fi ∘ jRefl` on `𝔻*`.
The reflection `ρ` has the same properties as in `s07d_p3_reflection`. -/
theorem s07d_p3_reflection_data (K : ℝ) (hK : 1 ≤ K) : ∃ L c₀ : ℝ, 1 ≤ L ∧ 0 < c₀ ∧
    ∀ Ω Ωs : Set ℂ, IsBoundedKQuasicircle Ω Ωs K → ∀ f g h : ℂ → ℂ, IsDiskWelding Ω Ωs f g h →
      ∃ ρ Φ F Fi : ℂ → ℂ, ∃ a ∈ unitDisc,
      ((∀ z ∈ unitDisc, Φ z = f (diskMobius 0 a z)) ∧ IsKQC Φ univ L ∧
        Φ '' univ = univ ∧ Φ '' unitDisc = Ω ∧ Φ '' unitDiscExterior = Ωs) ∧
      (IsClosedDiskHomeo F ∧ F 0 = 0 ∧ IsDiskBiLip F L ∧ IsKQC F unitDisc L ∧
        (∀ z ∈ closedBall (0 : ℂ) 1, Fi (F z) = z ∧ F (Fi z) = z) ∧
        (∀ z ∈ unitDiscExterior, Φ z = g (jRefl (Fi (jRefl z)))) ∧
        ∀ ζ ∈ sphere (0 : ℂ) 1, diskMobius 0 a (F ζ) = h ζ) ∧
      (∀ z : ℂ, z ≠ 0 → ρ (Φ z) = Φ (jRefl z)) ∧
      (∀ x ∈ curveOf Ω Ωs, ρ x = x) ∧
      (∀ z ∈ Ω, z ≠ Φ 0 → ρ z ∈ Ωs ∧ ρ (ρ z) = z) ∧
      (∀ z ∈ Ωs, ρ z ∈ Ω ∧ ρ z ≠ Φ 0 ∧ ρ (ρ z) = z) ∧
      (∀ z w : ℂ, infDist z (curveOf Ω Ωs) < c₀ * diam (curveOf Ω Ωs) →
        infDist w (curveOf Ω Ωs) < c₀ * diam (curveOf Ω Ωs) →
          ‖ρ z - ρ w‖ ≤ L * ‖z - w‖ ∧ ‖z - w‖ ≤ L * ‖ρ z - ρ w‖) ∧
      ∀ (Q : ℝ) (κ₀ : ℂ → ℂ), IsKQC κ₀ univ Q → κ₀ '' univ = univ → κ₀ '' unitDisc ⊆ unitDisc →
        (0 : ℂ) ∉ κ₀ '' closedBall (0 : ℂ) 1 →
        ∃ G : ℂ → ℂ, IsKQC G univ (L * Q) ∧ G '' univ = univ ∧
          G '' unitDisc = ρ '' (Φ '' (κ₀ '' unitDisc)) ∧
          G '' sphere (0 : ℂ) 1 = ρ '' (Φ '' (κ₀ '' sphere (0 : ℂ) 1)) ∧
          ∃ w₀ ∈ unitDisc, G 0 = Φ (jRefl (κ₀ w₀)) ∧ ∀ p : ℂ, κ₀ p = 0 → ‖w₀‖ * ‖p‖ ≤ 1 := by
  obtain ⟨L₁, hL₁, hnorm⟩ := s07d_p3_normal K hK
  -- `s07d_p3_collar` fixes the collar: with `C₅` from P3.5 and `P = C₅²` it takes
  -- `c₀ = c/(1 + P)`, `c = 1/(2(1 + P))`, so that `c₀ ≤ c < 1/C₅` (the deep point `Φ 0` is off the
  -- collar) and `(1 + P) c ≤ 1` (P3.3 applies to `ρ` of collar points).
  obtain ⟨L, c₀, hLL, hc₀, hcol⟩ := s07d_p3_collar K L₁ hK hL₁
  have hL : 1 ≤ L := hL₁.trans hLL
  refine ⟨L, c₀, hL, hc₀, fun Ω Ωs hq f g h hw => ?_⟩
  obtain ⟨F, Fi, a, ha, hw', hF, hF0, hFb, hFq, hFi, hFh⟩ := hnorm Ω Ωs hq f g h hw
  obtain ⟨Φ, hΦq, hΦs, hΦD, hΦE⟩ := s07d_p3_glue hq hw' hF (fun _ _ => rfl) hF0 hFq hFi
  obtain ⟨T, hT⟩ := t1_homeomorph hΦq hΦs
  have hΦi : Function.Injective Φ := by rw [← hT]; exact T.injective
  have hTs : ∀ z, T.symm (Φ z) = z := fun z => by rw [← hT]; exact T.symm_apply_apply z
  have hsph : ∀ ζ ∈ sphere (0 : ℂ) 1, F ζ ∈ sphere (0 : ℂ) 1 := fun ζ hζ => hw'.2.2.2.1 hζ
  obtain ⟨hFD, hFs⟩ := s07d_p3_disk_onto hF hFq hsph
  have hFiD : ∀ v ∈ unitDisc, Fi v ∈ unitDisc ∧ (v ≠ 0 → Fi v ≠ 0) := by
    intro v hv
    have hv' : v ∈ F '' unitDisc := by rw [hFs]; exact hv
    obtain ⟨x, hx, rfl⟩ := hv'
    rw [(hFi x (ball_subset_closedBall hx)).1]
    refine ⟨hx, fun h1 h2 => h1 ?_⟩
    rw [h2, hF0]
  have hΩ : Φ '' unitDisc = Ω := by
    rw [← hw'.1.2.2]
    exact image_congr fun z hz => hΦD z hz
  have hΩs : Φ '' unitDiscExterior = Ωs := by
    rw [image_congr fun z hz => hΦE z hz, ← hw'.2.1.2.2]
    conv_rhs => rw [← s07d_p3_E_ext hF hF0 hFD hFs hFi]
    rw [image_image]
  have hΓ : ∀ z : ℂ, Φ z ∈ curveOf Ω Ωs → ‖z‖ = 1 := by
    intro z hz
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · apply hz
      left
      rw [← hΩ]
      exact mem_image_of_mem Φ (mem_ball_zero_iff.mpr h1)
    · apply hz
      right
      rw [← hΩs]
      exact mem_image_of_mem Φ h1
  set ρ : ℂ → ℂ := fun x => Φ (jRefl (T.symm x)) with hρdef
  have hR1 : ∀ z, ρ (Φ z) = Φ (jRefl z) := fun z => by
    show Φ (jRefl (T.symm (Φ z))) = Φ (jRefl z)
    rw [hTs]
  have hjR1 : ∀ z : ℂ, ‖z‖ = 1 → jRefl z = z := fun z hz => by
    rw [s07d_p3_jRefl_eq, hz]
    simp
  have hsurj : ∀ x, ∃ z, Φ z = x := fun x => by
    obtain ⟨z, -, hz⟩ : x ∈ Φ '' univ := by rw [hΦs]; exact mem_univ x
    exact ⟨z, hz⟩
  have hR2 : ∀ x ∈ curveOf Ω Ωs, ρ x = x := by
    intro x hx
    obtain ⟨z, rfl⟩ := hsurj x
    rw [hR1, hjR1 z (hΓ z hx)]
  have hR3 : ∀ z ∈ Ω, z ≠ Φ 0 → ρ z ∈ Ωs ∧ ρ (ρ z) = z := by
    intro z hz hz0
    rw [← hΩ] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    have hu0 : u ≠ 0 := fun h => hz0 (by rw [h])
    refine ⟨?_, by rw [hR1 u, hR1 (jRefl u), s07d_p3_jRefl_jRefl]⟩
    rw [hR1, ← hΩs]
    exact mem_image_of_mem Φ (s07d_p3_jRefl_int hu hu0)
  have hR4 : ∀ z ∈ Ωs, ρ z ∈ Ω ∧ ρ z ≠ Φ 0 ∧ ρ (ρ z) = z := by
    intro z hz
    rw [← hΩs] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    obtain ⟨hj1, hj0⟩ := s07d_p3_jRefl_ext hu
    refine ⟨?_, fun h => hj0 (hΦi ((hR1 u).symm.trans h)), by rw [hR1 u, hR1 (jRefl u), s07d_p3_jRefl_jRefl]⟩
    rw [hR1, ← hΩ]
    exact mem_image_of_mem Φ hj1
  have hrS : ∀ x ∈ Ωs, ∃ u ∈ unitDisc, u ≠ 0 ∧ F u ∈ unitDisc ∧
      x = g (jRefl u) ∧ ρ x = (fun z => f (diskMobius 0 a z)) (F u) := by
    intro x hx
    rw [← hΩs] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨hv, hv0⟩ := s07d_p3_jRefl_ext hy
    obtain ⟨hu, hu0⟩ := hFiD _ hv
    have hFu : F (Fi (jRefl y)) = jRefl y := (hFi _ (ball_subset_closedBall hv)).2
    refine ⟨Fi (jRefl y), hu, hu0 hv0, by rw [hFu]; exact hv, hΦE y hy, ?_⟩
    rw [hR1, hFu]
    exact hΦD _ hv
  have hrΩ : ∀ x ∈ Ω, x ≠ Φ 0 → ∃ v ∈ unitDisc, v ≠ 0 ∧ Fi v ∈ unitDisc ∧ Fi v ≠ 0 ∧
      x = (fun z => f (diskMobius 0 a z)) v ∧ ρ x = g (jRefl (Fi v)) := by
    intro x hx hx0
    rw [← hΩ] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    have hv0 : v ≠ 0 := fun h => hx0 (by rw [h])
    refine ⟨v, hv, hv0, (hFiD v hv).1, (hFiD v hv).2 hv0, hΦD v hv, ?_⟩
    rw [hR1, hΦE _ (s07d_p3_jRefl_int hv hv0), s07d_p3_jRefl_jRefl]
  have hx₀ : Φ 0 = (fun z => f (diskMobius 0 a z)) 0 := hΦD 0 (mem_ball_self one_pos)
  have hFbL : IsDiskBiLip F L := by
    intro x hx y hy
    obtain ⟨h1, h2⟩ := hFb x hx y hy
    exact ⟨h1.trans (mul_le_mul_of_nonneg_right hLL (s02_diskDist_nonneg hx hy)),
      h2.trans (mul_le_mul_of_nonneg_right hLL (s02_diskDist_nonneg (hFD x hx) (hFD y hy)))⟩
  have hΦL : IsKQC Φ univ L := hΦq.mono hLL
  refine ⟨ρ, Φ, F, Fi, a, ha, ⟨fun z hz => hΦD z hz, hΦL, hΦs, hΩ, hΩs⟩,
    ⟨hF, hF0, hFbL, hFq.mono hLL, hFi, hΦE, hFh⟩, fun z _ => hR1 z, hR2, hR3, hR4,
    hcol Ω Ωs _ g F Fi ρ (Φ 0) hq hw' hF hF0 hFb hFi hx₀ hR2 hR3 hR4 hrS hrΩ, ?_⟩
  -- transfer: `G = Φ ∘ H` with `H = jRefl ∘ κ₀ ∘ σ` on `𝔻̄` (`s07d_p3_transfer_map`)
  intro Q κ₀ hκ hκs _hκD h0
  obtain ⟨H, σ, hHq, hHs, hσD, hσC, hHeq, hσ0⟩ := s07d_p3_transfer_map hκ hκs h0
  have hG := thm7_1_comp hHq hΦL (subset_univ _)
  rw [mul_comm] at hG
  have himg : ∀ S ⊆ closedBall (0 : ℂ) 1, σ '' S = S →
      (Φ ∘ H) '' S = ρ '' (Φ '' (κ₀ '' S)) := by
    intro S hS hσS
    have e1 : (Φ ∘ H) '' S = (fun x => Φ (jRefl (κ₀ x))) '' (σ '' S) := by
      rw [image_image]
      exact image_congr fun z hz => by
        show Φ (H z) = Φ (jRefl (κ₀ (σ z)))
        rw [hHeq z (hS hz)]
    have e2 : ρ '' (Φ '' (κ₀ '' S)) = (fun x => Φ (jRefl (κ₀ x))) '' S := by
      rw [image_image, image_image]
      exact image_congr fun z _ => hR1 _
    rw [e1, hσS, e2]
  have hσ0D : σ 0 ∈ unitDisc := by
    rw [← hσD]
    exact mem_image_of_mem σ (mem_ball_self one_pos)
  refine ⟨Φ ∘ H, hG, by rw [image_comp, hHs, hΦs], himg _ ball_subset_closedBall hσD,
    himg _ sphere_subset_closedBall hσC, σ 0, hσ0D, ?_, hσ0⟩
  show Φ (H 0) = Φ (jRefl (κ₀ (σ 0)))
  rw [hHeq 0 (mem_closedBall_self zero_le_one)]

/-! ## P6 (w1): per-arc assembly, `s07d_p6_weak`, and `s07d_b2_b5` -/

/-- P6 helper: `diskMobius 0 a ∘ diskMobius 0 (-a) = id` on `𝔻̄`. -/
theorem s07d_p6_mob_id {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    diskMobius 0 a (diskMobius 0 (-a) z) = z := by
  have hca : conj a * a ≠ 1 := by
    intro h
    have h1 : ‖conj a * a‖ = 1 := by rw [h, norm_one]
    rw [norm_mul, Complex.norm_conj] at h1
    nlinarith [norm_nonneg a]
  have hne : 1 + conj a * z ≠ 0 := by
    intro h
    have h1 : conj a * z = -1 := by linear_combination h
    have h2 : ‖conj a * z‖ = 1 := by rw [h1, norm_neg, norm_one]
    rw [norm_mul, Complex.norm_conj] at h2
    nlinarith [norm_nonneg a, norm_nonneg z, mul_le_mul ha.le hz (norm_nonneg z) zero_le_one]
  have e1 : diskMobius 0 (-a) z = (z + a) / (1 + conj a * z) := by
    show Complex.exp (((0 : ℝ) : ℂ) * I) * ((z - -a) / (1 - conj (-a) * z)) = _
    rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, map_neg, sub_neg_eq_add,
      neg_mul, sub_neg_eq_add]
  rw [e1]
  show Complex.exp (((0 : ℝ) : ℂ) * I) * (((z + a) / (1 + conj a * z) - a) /
    (1 - conj a * ((z + a) / (1 + conj a * z)))) = z
  rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  exact (s07d_p3_mob_inv' hca hne).2

/-- P6 helper: `log (f ∘ M)' ∈ BMOA` for a Möbius map `M = diskMobius 0 a` when `log f' ∈ BMOA`
(`f` a Riemann map of a bounded quasicircle domain). -/
theorem s07d_p6_bmoa {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {a : ℂ} (ha : ‖a‖ < 1) (hB : LogDerivBMOA f) :
    LogDerivBMOA (fun z => f (diskMobius 0 a z)) := by
  have hfM := s07b_comp_mob_conformal hf 0 ha
  have ha' : ‖-a‖ < 1 := by rwa [norm_neg]
  refine s07b_bmoa_of_mobius hq hfM 0 ha' ?_
  have hC := (thm_shen_wei_B (Or.inl hq) hf).mp hB
  have hDo : IsOpen unitDisc := isOpen_ball
  have heq : schwarzCarlesonMeasure
      (fun z => (fun z => f (diskMobius 0 a z)) (diskMobius 0 (-a) z)) = schwarzCarlesonMeasure f := by
    unfold schwarzCarlesonMeasure
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem hDo.measurableSet] with z hz
    have hev : (fun z => (fun z => f (diskMobius 0 a z)) (diskMobius 0 (-a) z)) =ᶠ[𝓝 z] f :=
      Filter.eventually_of_mem (hDo.mem_nhds hz) fun x hx => by
        show f (diskMobius 0 a (diskMobius 0 (-a) x)) = f x
        rw [s07d_p6_mob_id ha (mem_ball_zero_iff.mp hx).le]
    rw [schwarzian_congr (hev.filter_mono nhdsWithin_le_nhds)]
  rw [heq]
  exact hC

/-- P6 helper (Euclidean cone ⇒ polar cone): if `|z| < 1`, `|z - e^{it}| ≤ 3(1 - |z|)` and
`|z - e^{it}| ≤ 1/2`, then `z = |z| e^{is}` with `|s - t| ≤ 10 (1 - |z|)`. -/
theorem s07d_p6_polar {z : ℂ} {t : ℝ} (hz : ‖z‖ < 1)
    (h1 : ‖z - Complex.exp (t * I)‖ ≤ 3 * (1 - ‖z‖)) (h2 : ‖z - Complex.exp (t * I)‖ ≤ 1 / 2) :
    ∃ s : ℝ, z = (‖z‖ : ℂ) * Complex.exp (s * I) ∧ |s - t| ≤ 10 * (1 - ‖z‖) := by
  have het : ‖Complex.exp (t * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I t
  have hρ : 1 / 2 ≤ ‖z‖ := by
    have := norm_sub_norm_le (Complex.exp (t * I)) z
    rw [het, norm_sub_rev] at this
    linarith
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hρ
    linarith
  set ρ := ‖z‖ with hρdef
  set x := z * Complex.exp (-(t * I)) with hxdef
  have hxn : ‖x‖ = ρ := by
    rw [hxdef, norm_mul, show -(↑t * I) = ((-t : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  set θ := arg x with hθdef
  have hx : x = (ρ : ℂ) * Complex.exp (θ * I) := by
    have := Complex.norm_mul_exp_arg_mul_I x
    rw [hxn] at this
    exact this.symm
  refine ⟨t + θ, ?_, ?_⟩
  · have hz' : z = x * Complex.exp (t * I) := by
      rw [hxdef, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    rw [hz', hx, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · have hθπ : |θ| ≤ π := abs_arg_le_pi x
    have hrot : ‖z - Complex.exp (t * I)‖ = ‖(ρ : ℂ) * Complex.exp (θ * I) - 1‖ := by
      have hz' : z - Complex.exp (t * I) = (x - 1) * Complex.exp (t * I) := by
        rw [hxdef, sub_mul, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
          mul_one, one_mul]
      rw [hz', norm_mul, het, mul_one, hx]
    set u := Complex.exp (θ * I) with hudef
    have hu : u.re ^ 2 + u.im ^ 2 = 1 := by
      have h := Complex.norm_exp_ofReal_mul_I θ
      rw [← hudef, Complex.norm_def, Real.sqrt_eq_one, Complex.normSq_apply] at h
      nlinarith [h]
    have hkey : ‖(ρ : ℂ) * u - 1‖ ^ 2 = (1 - ρ) ^ 2 + ρ * ‖u - 1‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.one_re, Complex.one_im]
      nlinarith [hu]
    have hch := s07d_p2_ah_chord θ hθπ
    have hch' : 2 * |θ| ≤ π * ‖u - 1‖ := by
      rw [hudef, mul_comm (θ : ℂ) I]
      exact hch
    have hd : ‖z - Complex.exp (t * I)‖ ^ 2 ≤ 9 * (1 - ρ) ^ 2 := by
      have h0 : 0 ≤ ‖z - Complex.exp (t * I)‖ := norm_nonneg _
      nlinarith
    rw [hrot, hkey] at hd
    have hu2 : ‖u - 1‖ ^ 2 ≤ 18 * (1 - ρ) ^ 2 := by
      nlinarith [sq_nonneg (1 - ρ), sq_nonneg ‖u - 1‖]
    have hθ2 : (2 * |θ|) ^ 2 ≤ (π * ‖u - 1‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hch' 2
    have hπ : π < 3.15 := Real.pi_lt_d2
    have hθ3 : |θ| ^ 2 ≤ (10 * (1 - ρ)) ^ 2 := by
      have e1 : (π * ‖u - 1‖) ^ 2 = π ^ 2 * ‖u - 1‖ ^ 2 := by ring
      have e2 : π ^ 2 ≤ 10 := by nlinarith [Real.pi_pos]
      nlinarith [sq_nonneg (1 - ρ), sq_nonneg ‖u - 1‖, sq_nonneg θ, sq_abs θ]
    have h1ρ : 0 ≤ 1 - ρ := by linarith
    have := (sq_le_sq₀ (abs_nonneg θ) (by positivity)).mp hθ3
    rwa [add_sub_cancel_left]

/-- P6 helper: on a parameter interval of length `≤ π` the arclength parametrisation has a
`π/2`-Lipschitz inverse, so `|{t ∈ [a, b] : e^{it} ∈ S}| ≤ (π/2) μH¹(S)`. -/
theorem s07d_p6_hvol {a b : ℝ} (hab : b - a ≤ π) (S : Set ℂ) :
    volume {t : ℝ | t ∈ Icc a b ∧ Complex.exp (t * I) ∈ S} ≤
      ENNReal.ofReal (π / 2) * μH[1] S := by
  set T := {t : ℝ | t ∈ Icc a b ∧ Complex.exp (t * I) ∈ S} with hTdef
  set e : ℝ → ℂ := fun t => Complex.exp (t * I) with hedef
  have hlip : ∀ t ∈ T, ∀ t' ∈ T, |t - t'| ≤ π / 2 * ‖e t - e t'‖ := by
    intro t ht t' ht'
    have h1 : |t - t'| ≤ π := by
      rw [abs_le]
      constructor <;> linarith [ht.1.1, ht.1.2, ht'.1.1, ht'.1.2]
    have hc := s07d_p2_ah_chord (t - t') h1
    have hr := s07d_p6_rot t t'
    have : ‖e t - e t'‖ = ‖Complex.exp (I * ((t - t' : ℝ) : ℂ)) - 1‖ := hr
    rw [this]
    linarith
  set g := Function.invFunOn e T with hgdef
  have hg : ∀ y ∈ e '' T, g y ∈ T ∧ e (g y) = y := fun y hy =>
    ⟨Function.invFunOn_mem hy, Function.invFunOn_eq hy⟩
  have hgl : LipschitzOnWith (Real.toNNReal (π / 2)) g (e '' T) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
    rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, dist_eq_norm]
    have := hlip _ (hg y hy).1 _ (hg y' hy').1
    rwa [(hg y hy).2, (hg y' hy').2] at this
  have hTsub : T ⊆ g '' (e '' T) := by
    intro t ht
    refine ⟨e t, mem_image_of_mem e ht, ?_⟩
    have h1 := hg (e t) (mem_image_of_mem e ht)
    have h2 := hlip _ h1.1 _ ht
    rw [h1.2, sub_self, norm_zero, mul_zero] at h2
    have := abs_nonpos_iff.mp h2
    linarith
  have h1 := hgl.hausdorffMeasure_image_le (d := 1) zero_le_one
  rw [ENNReal.rpow_one] at h1
  have heS : e '' T ⊆ S := by
    rintro _ ⟨t, ht, rfl⟩
    exact ht.2
  calc volume T = μH[1] T := by rw [hausdorffMeasure_real]
    _ ≤ μH[1] (g '' (e '' T)) := measure_mono hTsub
    _ ≤ ((Real.toNNReal (π / 2) : ℝ≥0) : ℝ≥0∞) * μH[1] (e '' T) := h1
    _ ≤ ENNReal.ofReal (π / 2) * μH[1] S := by
        rw [ENNReal.ofReal]
        gcongr

/-- P6 helper: for a measurable `A` inside the arc `circleArc a b`,
`|A| ≤ |{t ∈ [a, b] : e^{it} ∈ A}|`. -/
theorem s07d_p6_arcvol {a b : ℝ} {A : Set ℂ} (hA : A ⊆ circleArc a b)
    (hAm : MeasurableSet A) :
    circleLen A ≤ volume {t : ℝ | t ∈ Icc a b ∧ Complex.exp (t * I) ∈ A} := by
  rw [s07_circleLen_shift A hAm a]
  have hsub : (fun θ : ℝ => Complex.exp (θ * I)) ⁻¹' A ∩ Ioc a (a + 2 * π) ⊆
      {t : ℝ | t ∈ Icc a b ∧ Complex.exp (t * I) ∈ A} ∪ {a + 2 * π} := by
    rintro t ⟨htA, hta1, hta2⟩
    by_cases htb : t ≤ b
    · exact Or.inl ⟨⟨hta1.le, htb⟩, htA⟩
    · right
      obtain ⟨t', ht', he⟩ := hA htA
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
      have him := congrArg Complex.im hn
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.add_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im] at him
      have hn' : t' = t + n * (2 * π) := by
        have : t' = t + ((n : ℝ) * (2 * π)) := by
          simp at him
          linarith
        exact this
      have hlt : t' < t := by linarith [ht'.2]
      have hn1 : (n : ℝ) < 0 := by
        by_contra hc
        rw [not_lt] at hc
        have : 0 ≤ (n : ℝ) * (2 * π) := mul_nonneg hc (by positivity)
        linarith
      have hn2 : (n : ℝ) ≤ -1 := by
        have h0 : n < 0 := by exact_mod_cast hn1
        have : n ≤ -1 := by omega
        exact_mod_cast this
      have : a + 2 * π ≤ t := by nlinarith [ht'.1, Real.pi_pos]
      exact mem_singleton_iff.mpr (le_antisymm hta2 this)
  calc volume ((fun θ : ℝ => Complex.exp (θ * I)) ⁻¹' A ∩ Ioc a (a + 2 * π))
      ≤ volume ({t : ℝ | t ∈ Icc a b ∧ Complex.exp (t * I) ∈ A} ∪ {a + 2 * π}) := measure_mono hsub
    _ ≤ volume {t : ℝ | t ∈ Icc a b ∧ Complex.exp (t * I) ∈ A} + volume ({a + 2 * π} : Set ℝ) :=
        measure_union_le _ _
    _ = _ := by rw [Real.volume_singleton, add_zero]

/-- P6 helper (exterior Poisson bound): for `|w| > 1` the exterior Poisson kernel is at most
`(|w| + 1)/(|w| - 1)`, so the exterior Poisson integral of `S` is at most
`(2π)⁻¹ (|w| + 1)/(|w| - 1) |S|`. -/
theorem s07d_p6_extP {w : ℂ} (hw : 1 < ‖w‖) (S : Set ℂ) (hS : MeasurableSet S) :
    (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (‖w‖ ^ 2 - 1) / ‖Complex.exp (t * I) - w‖ ^ 2 *
        S.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) ≤
      (2 * π)⁻¹ * ((‖w‖ + 1) / (‖w‖ - 1) * (circleLen S).toReal) := by
  have hw1 : 0 < ‖w‖ - 1 := by linarith
  have hden : ∀ t : ℝ, ‖w‖ - 1 ≤ ‖Complex.exp (t * I) - w‖ := fun t => by
    have := norm_sub_norm_le w (Complex.exp (t * I))
    rw [Complex.norm_exp_ofReal_mul_I, norm_sub_rev] at this
    linarith
  have hk : ∀ t : ℝ, (‖w‖ ^ 2 - 1) / ‖Complex.exp (t * I) - w‖ ^ 2 ≤ (‖w‖ + 1) / (‖w‖ - 1) := by
    intro t
    have h1 : (‖w‖ - 1) ^ 2 ≤ ‖Complex.exp (t * I) - w‖ ^ 2 :=
      pow_le_pow_left₀ hw1.le (hden t) 2
    have h2 : 0 < (‖w‖ - 1) ^ 2 := by positivity
    calc (‖w‖ ^ 2 - 1) / ‖Complex.exp (t * I) - w‖ ^ 2 ≤ (‖w‖ ^ 2 - 1) / (‖w‖ - 1) ^ 2 :=
          div_le_div_of_nonneg_left (by nlinarith) h2 h1
      _ = (‖w‖ + 1) / (‖w‖ - 1) := by
          rw [show ‖w‖ ^ 2 - 1 = (‖w‖ + 1) * (‖w‖ - 1) by ring, pow_two, mul_div_mul_right _ _ hw1.ne']
  have hkc : Continuous fun t : ℝ => (‖w‖ ^ 2 - 1) / ‖Complex.exp (t * I) - w‖ ^ 2 := by
    refine Continuous.div continuous_const (by fun_prop) fun t => ?_
    exact (pow_pos (lt_of_lt_of_le hw1 (hden t)) 2).ne'
  set T := (fun t : ℝ => Complex.exp (t * I)) ⁻¹' S with hTdef
  have hTm : MeasurableSet T := hS.preimage (by fun_prop)
  have hind : ∀ t : ℝ, S.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) =
      T.indicator (fun _ => (1 : ℝ)) t := fun t => by
    by_cases h : Complex.exp (t * I) ∈ S
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show t ∈ T from h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show t ∉ T from h)]
  have hindm : Measurable fun t : ℝ => T.indicator (fun _ => (1 : ℝ)) t :=
    measurable_const.indicator hTm
  have hint1 : IntervalIntegrable (fun t : ℝ => (‖w‖ ^ 2 - 1) / ‖Complex.exp (t * I) - w‖ ^ 2 *
      S.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I))) volume 0 (2 * π) := by
    simp_rw [hind]
    refine (hkc.intervalIntegrable 0 (2 * π)).mono_fun
      ((hkc.measurable.mul hindm).aestronglyMeasurable) (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    unfold Set.indicator; split_ifs <;> norm_num
  have hint2 : IntervalIntegrable (fun t : ℝ => (‖w‖ + 1) / (‖w‖ - 1) *
      T.indicator (fun _ => (1 : ℝ)) t) volume 0 (2 * π) := by
    refine (intervalIntegrable_const (c := (‖w‖ + 1) / (‖w‖ - 1))).mono_fun
      ((measurable_const.mul hindm).aestronglyMeasurable) (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    unfold Set.indicator; split_ifs <;> norm_num
  have hmono : ∫ t in (0 : ℝ)..2 * π, (‖w‖ ^ 2 - 1) / ‖Complex.exp (t * I) - w‖ ^ 2 *
        S.indicator (fun _ => (1 : ℝ)) (Complex.exp (t * I)) ≤
      ∫ t in (0 : ℝ)..2 * π, (‖w‖ + 1) / (‖w‖ - 1) * T.indicator (fun _ => (1 : ℝ)) t := by
    refine intervalIntegral.integral_mono_on (by positivity) hint1 hint2 fun t _ => ?_
    rw [hind]
    exact mul_le_mul_of_nonneg_right (hk t) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hval : ∫ t in (0 : ℝ)..2 * π, (‖w‖ + 1) / (‖w‖ - 1) * T.indicator (fun _ => (1 : ℝ)) t =
      (‖w‖ + 1) / (‖w‖ - 1) * (circleLen S).toReal := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le (by positivity)]
    congr 1
    rw [integral_indicator_const _ hTm, smul_eq_mul, mul_one, measureReal_restrict_apply hTm,
      s07_circleLen_shift S hS 0, zero_add]
    rfl
  rw [← hval]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

/-- P6 helper: the reflection extension of a closed-disk homeomorphism `F` with `F 0 = 0`,
`F(∂𝔻) ⊆ ∂𝔻`, `F(𝔻) = 𝔻`: `R = F` on `𝔻̄`, `R = jRefl ∘ F ∘ jRefl` on `𝔻*`, is a continuous
bijection of `ℂ`. -/
theorem s07d_p6_rext {F : ℂ → ℂ} (hF : IsClosedDiskHomeo F) (hF0 : F 0 = 0)
    (hsph : ∀ ζ ∈ sphere (0 : ℂ) 1, F ζ ∈ sphere (0 : ℂ) 1) (hFD : ∀ z ∈ unitDisc, F z ∈ unitDisc)
    (hFs : F '' unitDisc = unitDisc) :
    ∃ R : ℂ → ℂ, Continuous R ∧ Function.Injective R ∧ Function.Surjective R ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, R z = F z) ∧
      ∀ z ∈ unitDiscExterior, R z = jRefl (F (jRefl z)) := by
  classical
  have hjR1 : ∀ z : ℂ, ‖z‖ = 1 → jRefl z = z := fun z hz => by
    rw [s07d_p3_jRefl_eq, hz]
    simp
  have hF0' : ∀ z ∈ closedBall (0 : ℂ) 1, z ≠ 0 → F z ≠ 0 := fun z hz hz0 h =>
    hz0 (hF.1.injOn hz (mem_closedBall_self zero_le_one) (h.trans hF0.symm))
  have hjc : ContinuousOn jRefl ({0}ᶜ : Set ℂ) := by
    refine ContinuousOn.inv₀ Complex.continuous_conj.continuousOn fun z hz => ?_
    rw [map_ne_zero]
    exact hz
  set R : ℂ → ℂ := fun z => if ‖z‖ ≤ 1 then F z else jRefl (F (jRefl z)) with hRdef
  have hRc : Continuous R := by
    refine continuous_if_le continuous_norm continuous_const ?_ ?_ ?_
    · have : {x : ℂ | ‖x‖ ≤ 1} = closedBall 0 1 := by ext x; simp
      rw [this]
      exact hF.2
    · have hm1 : MapsTo jRefl {x : ℂ | 1 ≤ ‖x‖} (closedBall 0 1 \ {0}) := by
        intro x hx
        have hx0 : 0 < ‖x‖ := lt_of_lt_of_le one_pos hx
        refine ⟨mem_closedBall_zero_iff.mpr ?_, fun h => ?_⟩
        · rw [s07d_p3_jRefl_norm]
          exact inv_le_one_of_one_le₀ hx
        · have := s07d_p3_jRefl_norm x
          rw [mem_singleton_iff.mp h, norm_zero] at this
          exact (inv_ne_zero hx0.ne') this.symm
      have hc1 : ContinuousOn jRefl {x : ℂ | 1 ≤ ‖x‖} := hjc.mono fun x hx h => by
        have hx' : (1 : ℝ) ≤ ‖x‖ := hx
        rw [mem_singleton_iff.mp h, norm_zero] at hx'
        linarith
      have hc2 : ContinuousOn (fun z => F (jRefl z)) {x : ℂ | 1 ≤ ‖x‖} :=
        hF.2.comp hc1 fun x hx => (hm1 hx).1
      refine hjc.comp hc2 fun x hx => ?_
      exact hF0' _ (hm1 hx).1 (hm1 hx).2
    · intro x hx
      have hx' : ‖x‖ = 1 := hx
      rw [hjR1 x hx', hjR1 _ (mem_sphere_zero_iff_norm.mp (hsph x (mem_sphere_zero_iff_norm.mpr hx')))]
  have hRin : ∀ z ∈ closedBall (0 : ℂ) 1, R z = F z := fun z hz => by
    show (if ‖z‖ ≤ 1 then F z else jRefl (F (jRefl z))) = F z
    exact ite_eq_left_iff.mpr fun h => absurd (mem_closedBall_zero_iff.mp hz) h
  have hRout : ∀ z ∈ unitDiscExterior, R z = jRefl (F (jRefl z)) := fun z hz => by
    have hz1 : 1 < ‖z‖ := hz
    show (if ‖z‖ ≤ 1 then F z else jRefl (F (jRefl z))) = _
    exact ite_eq_right_iff.mpr fun h => absurd h (not_le.mpr hz1)
  have hout : ∀ z ∈ unitDiscExterior, jRefl (F (jRefl z)) ∈ unitDiscExterior ∧
      F (jRefl z) ∈ unitDisc ∧ jRefl z ∈ unitDisc := by
    intro z hz
    obtain ⟨hj1, hj0⟩ := s07d_p3_jRefl_ext hz
    have hF1 := hFD _ hj1
    exact ⟨s07d_p3_jRefl_int hF1 (hF0' _ (ball_subset_closedBall hj1) hj0), hF1, hj1⟩
  refine ⟨R, hRc, fun z₁ z₂ h => ?_, fun y => ?_, hRin, hRout⟩
  · rcases le_or_gt ‖z₁‖ 1 with h1 | h1 <;> rcases le_or_gt ‖z₂‖ 1 with h2 | h2
    · have hz1 : z₁ ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr h1
      have hz2 : z₂ ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr h2
      rw [hRin z₁ hz1, hRin z₂ hz2] at h
      exact hF.1.injOn hz1 hz2 h
    · have hz1 : z₁ ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr h1
      rw [hRin z₁ hz1, hRout z₂ h2] at h
      have := (hout z₂ h2).1
      rw [← h] at this
      have h3 := mem_closedBall_zero_iff.mp (hF.1.mapsTo hz1)
      have h4 : 1 < ‖F z₁‖ := this
      linarith
    · have hz2 : z₂ ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr h2
      rw [hRin z₂ hz2, hRout z₁ h1] at h
      have := (hout z₁ h1).1
      rw [h] at this
      have h3 := mem_closedBall_zero_iff.mp (hF.1.mapsTo hz2)
      have h4 : 1 < ‖F z₂‖ := this
      linarith
    · rw [hRout z₁ h1, hRout z₂ h2] at h
      have h' := congrArg jRefl h
      rw [s07d_p3_jRefl_jRefl, s07d_p3_jRefl_jRefl] at h'
      have h'' := hF.1.injOn (ball_subset_closedBall (hout z₁ h1).2.2)
        (ball_subset_closedBall (hout z₂ h2).2.2) h'
      have h''' := congrArg jRefl h''
      rwa [s07d_p3_jRefl_jRefl, s07d_p3_jRefl_jRefl] at h'''
  · rcases le_or_gt ‖y‖ 1 with hy | hy
    · obtain ⟨x, hx, rfl⟩ := hF.1.surjOn (mem_closedBall_zero_iff.mpr hy)
      exact ⟨x, hRin x hx⟩
    · obtain ⟨hj1, hj0⟩ := s07d_p3_jRefl_ext (show y ∈ unitDiscExterior from hy)
      have hj1' : jRefl y ∈ F '' unitDisc := by rw [hFs]; exact hj1
      obtain ⟨x, hx, hxe⟩ := hj1'
      have hx0 : x ≠ 0 := fun h => hj0 (by rw [← hxe, h, hF0])
      have hxo := s07d_p3_jRefl_int hx hx0
      refine ⟨jRefl x, ?_⟩
      rw [hRout _ hxo, s07d_p3_jRefl_jRefl, hxe, s07d_p3_jRefl_jRefl]

/-- P6 helper: upper Ahlfors regularity passes through a map that is `L`-bi-Lipschitz on the set. -/
theorem s07d_p6_armap {Y : Set ℂ} {ρ : ℂ → ℂ} {L M : ℝ} (hL : 0 < L)
    (hbl : ∀ x ∈ Y, ∀ y ∈ Y, ‖ρ x - ρ y‖ ≤ L * ‖x - y‖ ∧ ‖x - y‖ ≤ L * ‖ρ x - ρ y‖)
    (hAR : ∀ z : ℂ, ∀ r : ℝ, 0 < r → μH[1] (Y ∩ ball z r) ≤ ENNReal.ofReal (M * r)) :
    ∀ z : ℂ, ∀ r : ℝ, 0 < r → μH[1] (ρ '' Y ∩ ball z r) ≤ ENNReal.ofReal (2 * L ^ 2 * M * r) := by
  intro z r hr
  rcases (ρ '' Y ∩ ball z r).eq_empty_or_nonempty with he | ⟨y₀, ⟨x₀, hx₀, rfl⟩, hy₀⟩
  · rw [he, measure_empty]
    exact bot_le
  have hsub : ρ '' Y ∩ ball z r ⊆ ρ '' (Y ∩ ball x₀ (2 * L * r)) := by
    rintro _ ⟨⟨x, hx, rfl⟩, hxz⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    rw [mem_ball, dist_eq_norm] at hxz hy₀ ⊢
    have h1 : ‖ρ x - ρ x₀‖ < 2 * r := by
      calc ‖ρ x - ρ x₀‖ = ‖(ρ x - z) - (ρ x₀ - z)‖ := by congr 1; ring
        _ ≤ ‖ρ x - z‖ + ‖ρ x₀ - z‖ := norm_sub_le _ _
        _ < 2 * r := by linarith
    calc ‖x - x₀‖ ≤ L * ‖ρ x - ρ x₀‖ := (hbl x hx x₀ hx₀).2
      _ < L * (2 * r) := mul_lt_mul_of_pos_left h1 hL
      _ = 2 * L * r := by ring
  have hlip : ∀ x ∈ Y ∩ ball x₀ (2 * L * r), ∀ y ∈ Y ∩ ball x₀ (2 * L * r),
      dist (ρ x) (ρ y) ≤ L * dist x y := fun x hx y hy => by
    rw [dist_eq_norm, dist_eq_norm]
    exact (hbl x hx.1 y hy.1).1
  calc μH[1] (ρ '' Y ∩ ball z r) ≤ μH[1] (ρ '' (Y ∩ ball x₀ (2 * L * r))) := measure_mono hsub
    _ ≤ ENNReal.ofReal L * μH[1] (Y ∩ ball x₀ (2 * L * r)) := s07d_p2_ah_lip hL.le hlip
    _ ≤ ENNReal.ofReal L * ENNReal.ofReal (M * (2 * L * r)) :=
        by gcongr; exact hAR x₀ _ (by positivity)
    _ = ENNReal.ofReal (2 * L ^ 2 * M * r) := by
        rw [← ENNReal.ofReal_mul hL.le]
        congr 1
        ring

/-- P6 helper (stage A, the sawtooth over a short arc; P1 + P2). Let `Φ` be a global `L`-q.c.
map, holomorphic on `𝔻`, with `Φ' = e^φ` and `φ'` Carleson with constant `A`. For an arc
`I = [a, b]` of length `ℓ ≤ 1/6` and a measurable `A' ⊆ I` with `|A'| ≥ (3/4)ℓ` there are a sawtooth
domain `𝒟 ⊆ 𝔻 ∩ B(c, 9ℓ/8)` (`c = (1 - ℓ/2) e^{i(a+b)/2}`), a `Q`-q.c. `κ : 𝔻 → 𝒟` bi-Lipschitz at
scale `ℓ/8`, a scale `s > 0` and a measurable `X ⊆ A' ∩ closure 𝒟` with `μH¹(X) ≥ ℓ/π`, such that
`Φ(∂𝒟)` is `M`-upper Ahlfors-regular, `μH¹(Φ(∂𝒟)) ≤ M s ℓ/8` and `μH¹(Φ(X)) ≥ (s/M) μH¹(X)`.
`Q, M` depend only on `(L, A)`. -/
theorem s07d_p6_stageA (L A : ℝ) (hL : 1 ≤ L) (hA : 0 ≤ A) : ∃ Q M : ℝ, 1 ≤ Q ∧ 1 ≤ M ∧
    ∀ Φ φ : ℂ → ℂ, IsKQC Φ univ L → Φ '' univ = univ → DifferentiableOn ℂ Φ unitDisc →
      DifferentiableOn ℂ φ unitDisc → (∀ z ∈ unitDisc, Complex.exp (φ z) = deriv Φ z) →
      (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
        derivCarlesonMeasure (deriv φ) (unitDisc ∩ ball ζ r) ≤ ENNReal.ofReal (A * r)) →
      ∀ a b : ℝ, a < b → b - a ≤ 1 / 6 → ∀ A' ⊆ circleArc a b, MeasurableSet A' →
        ENNReal.ofReal (3 / 4 * (b - a)) ≤ circleLen A' →
        ∃ (𝒟 : Set ℂ) (κ : ℂ → ℂ) (s : ℝ) (X : Set ℂ), 0 < s ∧ IsOpen 𝒟 ∧
          IsKQC κ univ Q ∧ κ '' univ = univ ∧ κ '' unitDisc = 𝒟 ∧
          κ '' closedBall (0 : ℂ) 1 = closure 𝒟 ∧ κ '' sphere (0 : ℂ) 1 = frontier 𝒟 ∧
          (∀ z w : ℂ, (b - a) / 8 * ‖z - w‖ ≤ Q * ‖κ z - κ w‖ ∧
            ‖κ z - κ w‖ ≤ Q * ((b - a) / 8) * ‖z - w‖) ∧
          𝒟 ⊆ unitDisc ∩ ball (((1 - (b - a) / 2 : ℝ) : ℂ) * Complex.exp (((a + b) / 2 : ℝ) * I))
            (9 * ((b - a) / 8)) ∧
          X ⊆ A' ∧ X ⊆ closure 𝒟 ∧ MeasurableSet X ∧ ENNReal.ofReal ((b - a) / π) ≤ μH[1] X ∧
          (∀ x : ℂ, ∀ r : ℝ, 0 < r → μH[1] (Φ '' frontier 𝒟 ∩ ball x r) ≤ ENNReal.ofReal (M * r)) ∧
          μH[1] (Φ '' frontier 𝒟) ≤ ENNReal.ofReal (M * s * ((b - a) / 8)) ∧
          ENNReal.ofReal (s / M) * μH[1] X ≤ μH[1] (Φ '' X) := by
  obtain ⟨C₁, hC₁, hP1⟩ := s07d_p1_sawtooth A (1 / 10) (1 / 12) hA (by norm_num) (by norm_num)
  obtain ⟨Q, hQ, hkap⟩ := s07d_p2_kappa 9 (by norm_num)
  obtain ⟨M, hM, hah⟩ := s07d_p2_ahlfors 9 C₁ L (by norm_num) hC₁.le hL
  refine ⟨Q, M, hQ, hM, fun Φ φ hΦq hΦs hΦd hφd hφe hcar a b hab hℓ A' hAs hAm hAl => ?_⟩
  have hℓ0 : 0 < b - a := sub_pos.mpr hab
  obtain ⟨E, hEsub, hEc, hEv, hEφ⟩ := hP1 φ hφd hcar (a - (b - a)) (b + (b - a)) (by linarith)
    (by linarith)
  have hEm : MeasurableSet E := hEc.measurableSet
  -- `|[a, b] ∖ E| ≤ ℓ/4`
  have hdiff : volume (Icc a b \ E) ≤ ENNReal.ofReal ((b - a) / 4) := by
    have hIv : volume (Icc (a - (b - a)) (b + (b - a))) = ENNReal.ofReal (3 * (b - a)) := by
      rw [Real.volume_Icc]
      congr 1
      ring
    have h1 : volume (Icc (a - (b - a)) (b + (b - a)) \ E) + volume E = ENNReal.ofReal (3 * (b - a)) := by
      rw [← hIv]
      have := measure_diff_add_inter (μ := volume) (Icc (a - (b - a)) (b + (b - a))) hEm
      rwa [inter_eq_right.mpr hEsub] at this
    have h2 : volume (Icc (a - (b - a)) (b + (b - a)) \ E) +
        ENNReal.ofReal ((1 - 1 / 12) * (b + (b - a) - (a - (b - a)))) ≤
        ENNReal.ofReal ((b - a) / 4) + ENNReal.ofReal ((1 - 1 / 12) * (b + (b - a) - (a - (b - a)))) := by
      calc _ ≤ volume (Icc (a - (b - a)) (b + (b - a)) \ E) + volume E := by gcongr
        _ = _ := by
          rw [h1, ← ENNReal.ofReal_add (by positivity) (by nlinarith)]
          congr 1
          ring
    have h3 := ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top h2
    exact (measure_mono (diff_subset_diff_left (Icc_subset_Icc (by linarith) (by linarith)))).trans h3
  set TA := {t : ℝ | t ∈ Icc a b ∧ Complex.exp (t * I) ∈ A'} with hTAdef
  have hTA : ENNReal.ofReal (3 / 4 * (b - a)) ≤ volume TA := hAl.trans (s07d_p6_arcvol hAs hAm)
  have hET : ENNReal.ofReal ((b - a) / 2) ≤ volume (E ∩ TA) := by
    have hsplit : TA ⊆ (E ∩ TA) ∪ (Icc a b \ E) := fun t ht => by
      by_cases h : t ∈ E
      · exact Or.inl ⟨h, ht⟩
      · exact Or.inr ⟨ht.1, h⟩
    have h1 : ENNReal.ofReal ((b - a) / 2) + ENNReal.ofReal ((b - a) / 4) ≤
        volume (E ∩ TA) + ENNReal.ofReal ((b - a) / 4) := by
      calc ENNReal.ofReal ((b - a) / 2) + ENNReal.ofReal ((b - a) / 4)
          = ENNReal.ofReal (3 / 4 * (b - a)) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            ring
        _ ≤ volume TA := hTA
        _ ≤ volume (E ∩ TA) + volume (Icc a b \ E) := (measure_mono hsplit).trans (measure_union_le _ _)
        _ ≤ _ := by gcongr
    exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top h1
  -- the vertex set `Ep = e^{i(E ∩ [a, b])}`
  set Ep : Set ℂ := (fun t : ℝ => Complex.exp (t * I)) '' (E ∩ Icc a b) with hEpdef
  have hEpc : IsClosed Ep :=
    ((isCompact_Icc.inter_left hEc).image (by fun_prop)).isClosed
  have hEpn : Ep.Nonempty := by
    have hne : volume (E ∩ TA) ≠ 0 := by
      intro h
      rw [h] at hET
      have : (0 : ℝ) < (b - a) / 2 := by positivity
      exact absurd (ENNReal.ofReal_pos.mpr this) (not_lt.mpr hET)
    obtain ⟨t, htE, htT⟩ := nonempty_of_measure_ne_zero hne
    exact ⟨_, t, ⟨htE, htT.1⟩, rfl⟩
  have hEps : Ep ⊆ sphere (0 : ℂ) 1 := by
    rintro _ ⟨t, -, rfl⟩
    exact mem_sphere_zero_iff_norm.mpr (Complex.norm_exp_ofReal_mul_I t)
  set m : ℝ := (a + b) / 2 with hmdef
  set c : ℂ := ((1 - (b - a) / 2 : ℝ) : ℂ) * Complex.exp (m * I) with hcdef
  set ρ₀ : ℝ := (b - a) / 8 with hρ₀def
  have hcn : ‖c‖ = 1 - (b - a) / 2 := by
    rw [hcdef, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  have hcD : ∀ ζ ∈ Ep, ‖ζ - c‖ ≤ b - a := by
    rintro _ ⟨t, ⟨-, htab⟩, rfl⟩
    have h1 : ‖Complex.exp (t * I) - Complex.exp (m * I)‖ ≤ (b - a) / 2 := by
      refine (s07d_p6_chord t m).trans ?_
      rw [abs_le]
      constructor <;> linarith [htab.1, htab.2]
    have h2 : ‖Complex.exp (m * I) - c‖ = (b - a) / 2 := by
      rw [hcdef, show Complex.exp (m * I) - ((1 - (b - a) / 2 : ℝ) : ℂ) * Complex.exp (m * I) =
        (((b - a) / 2 : ℝ) : ℂ) * Complex.exp (m * I) by push_cast; ring, norm_mul,
        Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    calc ‖Complex.exp (t * I) - c‖ ≤ ‖Complex.exp (t * I) - Complex.exp (m * I)‖ +
          ‖Complex.exp (m * I) - c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ b - a := by linarith
  obtain ⟨hDo, hball, hsub, hstar, hcone, hcl⟩ := s07d_p2_saw Ep c ρ₀ (b - a) hEps hEpn
    (by positivity) (by rw [hcn]; linarith) hcD
  set 𝒟 : Set ℂ := {z : ℂ | ∃ ζ ∈ Ep, ∃ b ∈ ball c ρ₀, ∃ t ∈ Ioc (0 : ℝ) 1, z = ζ + t • (b - ζ)}
    with h𝒟def
  have h9 : 𝒟 ⊆ unitDisc ∩ ball c (9 * ρ₀) := by
    have : b - a + ρ₀ = 9 * ρ₀ := by rw [hρ₀def]; ring
    rw [← this]
    exact hsub
  -- `|φ - φ(w₁)| ≤ C₁` on `𝒟` (P1 on the tripled arc)
  set w₁ : ℂ := ((1 - (b + (b - a) - (a - (b - a))) : ℝ) : ℂ) *
    Complex.exp ((((a - (b - a)) + (b + (b - a))) / 2 : ℝ) * I) with hw₁def
  have hφb : ∀ z ∈ 𝒟, ‖φ z - φ w₁‖ ≤ C₁ := by
    intro z hz
    obtain ⟨ζ, hζ, h1, h2⟩ := hcone z hz
    obtain ⟨t, ⟨htE, htab⟩, rfl⟩ := hζ
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp (hsub hz).1
    have hc' : 1 - ‖c‖ - ρ₀ = 3 * (b - a) / 8 := by rw [hcn, hρ₀def]; ring
    rw [hc'] at h1
    have h1' : ‖z - Complex.exp (t * I)‖ ≤ 3 * (1 - ‖z‖) := by
      have key : (3 * (b - a) / 8) * ‖z - Complex.exp (t * I)‖ ≤ (3 * (b - a) / 8) * (3 * (1 - ‖z‖)) := by
        rw [hρ₀def] at h1
        linarith
      exact le_of_mul_le_mul_left key (by positivity)
    have h2' : ‖z - Complex.exp (t * I)‖ ≤ 1 / 2 := by
      rw [hρ₀def] at h2
      linarith
    obtain ⟨s', hzs, hst⟩ := s07d_p6_polar hz1 h1' h2'
    have h1ρ : 1 - ‖z‖ ≤ ‖z - Complex.exp (t * I)‖ := by
      have := norm_sub_norm_le (Complex.exp (t * I)) z
      rw [Complex.norm_exp_ofReal_mul_I, norm_sub_rev] at this
      linarith
    have := hEφ t htE ‖z‖ s' hz1 (by rw [hρ₀def] at h2; linarith) (by linarith)
    rw [← hzs] at this
    exact this
  set s : ℝ := Real.exp (φ w₁).re with hsdef
  have hder : ∀ z ∈ 𝒟, Real.exp (-C₁) * s ≤ ‖deriv Φ z‖ ∧ ‖deriv Φ z‖ ≤ Real.exp C₁ * s := by
    intro z hz
    have hzD := (hsub hz).1
    rw [← hφe z hzD, Complex.norm_exp]
    have hre : |(φ z).re - (φ w₁).re| ≤ C₁ := by
      rw [← Complex.sub_re]
      exact (Complex.abs_re_le_norm _).trans (hφb z hz)
    rw [abs_le] at hre
    constructor
    · rw [hsdef, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    · rw [hsdef, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
  obtain ⟨κ, hκq, hκs, hκD, hκcl, hκfr, hκbl⟩ :=
    hkap 𝒟 c ρ₀ (by positivity) hDo hball (h9.trans inter_subset_right) hstar
  obtain ⟨hAR, hlen, hBl⟩ :=
    hah 𝒟 c ρ₀ s Φ (by positivity) (Real.exp_pos _) hDo hball h9 hstar hΦq hΦs hΦd hder
  have hXcl : Ep ∩ A' ⊆ closure 𝒟 := by
    intro x hx
    have : x ∈ closure 𝒟 ∩ sphere (0 : ℂ) 1 := by
      rw [hcl hEpc]
      exact hx.1
    exact this.1
  have hX : ENNReal.ofReal ((b - a) / π) ≤ μH[1] (Ep ∩ A') := by
    have h1 : E ∩ TA ⊆ {t : ℝ | t ∈ Icc a b ∧ Complex.exp (t * I) ∈ Ep ∩ A'} :=
      fun t ht => ⟨ht.2.1, ⟨t, ⟨ht.1, ht.2.1⟩, rfl⟩, ht.2.2⟩
    have h2 := s07d_p6_hvol (a := a) (b := b) (by linarith [Real.pi_gt_three]) (Ep ∩ A')
    have h3 : ENNReal.ofReal ((b - a) / 2) ≤ ENNReal.ofReal (π / 2) * μH[1] (Ep ∩ A') :=
      hET.trans ((measure_mono h1).trans h2)
    calc ENNReal.ofReal ((b - a) / π) = ENNReal.ofReal (2 / π) * ENNReal.ofReal ((b - a) / 2) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
      _ ≤ ENNReal.ofReal (2 / π) * (ENNReal.ofReal (π / 2) * μH[1] (Ep ∩ A')) := by gcongr
      _ = μH[1] (Ep ∩ A') := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            show 2 / π * (π / 2) = 1 by field_simp, ENNReal.ofReal_one, one_mul]
  exact ⟨𝒟, κ, s, Ep ∩ A', Real.exp_pos _, hDo, hκq, hκs, hκD, hκcl, hκfr, hκbl, h9,
    inter_subset_right, hXcl, hEpc.measurableSet.inter hAm, hX, hAR, hlen, (hBl _ hXcl).1⟩

/-- P6 helper (the transferred centre is deep): with `κ` as in stage A (bi-Lipschitz at scale
`ℓ/8` with constant `Q`, `κ(𝔻) ⊆ 𝔻 ∩ B(c, 9ℓ/8)`, `|c| = 1 - ℓ/2`, `ℓ ≤ 1/(16 Q)`), every
`w₀ ∈ 𝔻` with `|w₀| |p| ≤ 1` at the zero `p` of `κ` has `u = κ(w₀) ∈ 𝔻 ∖ {0}` and
`cosh d_𝔻(u, c_I) ≤ 1 + 128 Q` for the top point `c_I` (`|c_I| = 1 - ℓ`, `|c_I - c| ≤ ℓ/2`). -/
theorem s07d_p6_deep {Q ℓ : ℝ} {c cI w₀ : ℂ} {κ : ℂ → ℂ} (hQ : 1 ≤ Q) (hℓ : 0 < ℓ)
    (hℓQ : ℓ ≤ 1 / (16 * Q)) (hc : ‖c‖ = 1 - ℓ / 2) (hcI : ‖cI‖ = 1 - ℓ) (hcc : ‖cI - c‖ ≤ ℓ / 2)
    (hκs : κ '' univ = univ) (hκD : κ '' unitDisc ⊆ unitDisc ∩ ball c (9 * (ℓ / 8)))
    (hκC : κ '' closedBall (0 : ℂ) 1 ⊆ closedBall c (9 * (ℓ / 8)))
    (hκbl : ∀ z w : ℂ, ℓ / 8 * ‖z - w‖ ≤ Q * ‖κ z - κ w‖ ∧ ‖κ z - κ w‖ ≤ Q * (ℓ / 8) * ‖z - w‖)
    (hw₀ : w₀ ∈ unitDisc) (hw₀p : ∀ p : ℂ, κ p = 0 → ‖w₀‖ * ‖p‖ ≤ 1) :
    κ w₀ ∈ unitDisc ∧ κ w₀ ≠ 0 ∧ diskCoshDist (κ w₀) cI ≤ 1 + 128 * Q := by
  have hQ0 : 0 < Q := by linarith
  have hℓ16 : ℓ ≤ 1 / 16 := hℓQ.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith)
  have hℓQ' : 16 * Q * ℓ ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hℓQ
    linarith
  -- the zero `p` of `κ` is far out: `|p| ≥ 2`
  obtain ⟨p, -, hp⟩ : (0 : ℂ) ∈ κ '' univ := by rw [hκs]; exact mem_univ _
  have h1 : ‖κ 1 - c‖ ≤ 9 * (ℓ / 8) := by
    have := hκC (mem_image_of_mem κ (mem_closedBall_zero_iff.mpr (by rw [norm_one])))
    rwa [mem_closedBall, dist_eq_norm] at this
  have hκ1 : 1 / 2 ≤ ‖κ 1‖ := by
    have := norm_sub_norm_le c (κ 1)
    rw [norm_sub_rev] at this
    linarith
  have hp2 : 2 ≤ ‖p‖ := by
    have h2 := (hκbl p 1).2
    rw [hp, zero_sub, norm_neg] at h2
    have h3 : ‖p - 1‖ ≤ ‖p‖ + 1 := by
      have := norm_sub_le p 1
      rwa [norm_one] at this
    have h4 : 1 / 2 ≤ Q * (ℓ / 8) * (‖p‖ + 1) :=
      hκ1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))
    nlinarith [norm_nonneg p]
  have hw₀2 : ‖w₀‖ ≤ 1 / 2 := by
    have := hw₀p p hp
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith [norm_nonneg w₀]
  set u := κ w₀ with hudef
  have huD : u ∈ unitDisc ∩ ball c (9 * (ℓ / 8)) := hκD (mem_image_of_mem κ hw₀)
  have hu0 : u ≠ 0 := by
    intro h
    have := huD.2
    rw [h, mem_ball, dist_eq_norm, zero_sub, norm_neg, hc] at this
    linarith
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp huD.1
  -- depth: `1 - |u| ≥ ℓ/(16 Q)`
  have hdeep : ℓ / (16 * Q) ≤ 1 - ‖u‖ := by
    have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    set ζ : ℂ := u * ((‖u‖⁻¹ : ℝ) : ℂ) with hζdef
    have hζ1 : ‖ζ‖ = 1 := by
      rw [hζdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hun),
        mul_inv_cancel₀ hun.ne']
    have hζu : ‖ζ - u‖ = 1 - ‖u‖ := by
      rw [hζdef, show u * ((‖u‖⁻¹ : ℝ) : ℂ) - u = u * (((‖u‖⁻¹ - 1) : ℝ) : ℂ) by push_cast; ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by
          rw [sub_nonneg]; exact one_le_inv₀ hun |>.mpr hu1.le)]
      field_simp
    obtain ⟨x, -, hx⟩ : ζ ∈ κ '' univ := by rw [hκs]; exact mem_univ _
    have hx1 : 1 ≤ ‖x‖ := by
      by_contra hlt
      rw [not_le] at hlt
      have := (hκD (mem_image_of_mem κ (mem_ball_zero_iff.mpr hlt))).1
      rw [hx] at this
      have h' : ‖ζ‖ < 1 := mem_ball_zero_iff.mp this
      rw [hζ1] at h'
      exact lt_irrefl _ h'
    have hxw : 1 / 2 ≤ ‖x - w₀‖ := by
      have := norm_sub_norm_le x w₀
      linarith
    have h2 := (hκbl x w₀).1
    rw [hx, ← hudef, hζu] at h2
    have h3 : ℓ / 8 * (1 / 2) ≤ Q * (1 - ‖u‖) :=
      (mul_le_mul_of_nonneg_left hxw (by positivity)).trans h2
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨huD.1, hu0, ?_⟩
  have hucI : ‖u - cI‖ ≤ 2 * ℓ := by
    have h1 : ‖u - c‖ < 9 * (ℓ / 8) := by
      have := huD.2
      rwa [mem_ball, dist_eq_norm] at this
    calc ‖u - cI‖ ≤ ‖u - c‖ + ‖c - cI‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * ℓ := by rw [norm_sub_rev c cI]; linarith
  have hA1 : ℓ / (16 * Q) ≤ 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
  have hA2 : ℓ ≤ 1 - ‖cI‖ ^ 2 := by rw [hcI]; nlinarith
  have hpos1 : 0 < ℓ / (16 * Q) := by positivity
  have hprod : ℓ / (16 * Q) * ℓ ≤ (1 - ‖u‖ ^ 2) * (1 - ‖cI‖ ^ 2) :=
    mul_le_mul hA1 hA2 hℓ.le (hpos1.le.trans hA1)
  have hnum : 2 * ‖u - cI‖ ^ 2 ≤ 8 * ℓ ^ 2 := by nlinarith [norm_nonneg (u - cI)]
  unfold diskCoshDist
  have hpp : 0 < ℓ / (16 * Q) * ℓ := by positivity
  have hfrac : 2 * ‖u - cI‖ ^ 2 / ((1 - ‖u‖ ^ 2) * (1 - ‖cI‖ ^ 2)) ≤ 128 * Q := by
    rw [div_le_iff₀ (hpp.trans_le hprod)]
    calc 2 * ‖u - cI‖ ^ 2 ≤ 8 * ℓ ^ 2 := hnum
      _ = 128 * Q * (ℓ / (16 * Q) * ℓ) := by field_simp; ring
      _ ≤ 128 * Q * ((1 - ‖u‖ ^ 2) * (1 - ‖cI‖ ^ 2)) := mul_le_mul_of_nonneg_left hprod (by positivity)
  linarith

/-- P6 helper: `circleLen` is subadditive. -/
theorem s07d_p6_cl_union (S T : Set ℂ) : circleLen (S ∪ T) ≤ circleLen S + circleLen T := by
  unfold circleLen
  refine (measure_mono fun θ hθ => ?_).trans (measure_union_le _ _)
  rcases hθ.2 with h | h
  · exact Or.inl ⟨hθ.1, h⟩
  · exact Or.inr ⟨hθ.1, h⟩

/-- P6 helper: `circleLen` is finite. -/
theorem s07d_p6_cl_ne_top (S : Set ℂ) : circleLen S ≠ ⊤ := by
  unfold circleLen
  refine ne_top_of_le_ne_top (b := volume (Ico (0 : ℝ) (2 * π))) ?_ (measure_mono fun θ h => h.1)
  rw [Real.volume_Ico]
  exact ENNReal.ofReal_ne_top

/-- P6 helper: `|circleArc a b| = b - a` for `a ≤ b ≤ a + 2π`. -/
theorem s07d_p6_cl_arc {a b : ℝ} (hab : a ≤ b) (hb : b - a ≤ 2 * π) :
    circleLen (circleArc a b) = ENNReal.ofReal (b - a) := by
  rw [circleArc, s07_circleLen_exp_image a (Icc a b) measurableSet_Icc
    (Icc_subset_Icc le_rfl (by linarith)), Real.volume_Icc]

/-- P6 core (normalised welding, `Φ`-coordinates). For a bounded `K`-quasicircle with welding
`(f, g, h)` and `log f' ∈ BMOA`, take the P3 data (`Φ = f ∘ M` on `𝔻`, `M = diskMobius 0 a`, `F` the
normalised extension of `M⁻¹ ∘ h`, `Fi = F⁻¹`). Then `Fi` satisfies a lower-bound weak pair on
short arcs: `|A| ≥ (3/4)|I| ⇒ |Fi(A)| ≥ β |Fi(I)|` for `|I| ≤ ℓ₀`.
Route: stage A (P1 + P2) gives the sawtooth `𝒟` over `A`; the P3 transfer gives `V = G(𝔻) =
ρ(Φ(𝒟)) ⊆ Ωs` with upper Ahlfors-regular boundary; P6c gives harmonic measure `≥ δ` at `G 0` for
`Φ(X) ⊆ ∂V`; P5 moves it to `Ωs` at `w = jRefl(Fi u)` (`u = κ w₀`); the exterior Poisson bound gives
`|Fi(A)| ≥ π δ (1 - |Fi u|)`; P6a gives `|Fi(I)| ≤ C (1 - |Fi u|)` (`u` is deep, `s07d_p6_deep`). -/
theorem s07d_p6_core {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K)
    {f g h : ℂ → ℂ} (hw : IsDiskWelding Ω Ωs f g h) (hB : LogDerivBMOA f) :
    ∃ F Fi : ℂ → ℂ, ∃ a ∈ unitDisc,
      (∀ ζ ∈ sphere (0 : ℂ) 1, F ζ ∈ sphere (0 : ℂ) 1 ∧ Fi ζ ∈ sphere (0 : ℂ) 1) ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, Fi (F z) = z ∧ F (Fi z) = z) ∧
      (∀ ζ ∈ sphere (0 : ℂ) 1, diskMobius 0 a (F ζ) = h ζ) ∧
      ∃ β ℓ₀ : ℝ, 0 < β ∧ 0 < ℓ₀ ∧ ℓ₀ ≤ 1 ∧ ∀ a' b' : ℝ, a' < b' → b' - a' ≤ ℓ₀ →
        ∀ A ⊆ circleArc a' b', MeasurableSet A → ENNReal.ofReal (3 / 4 * (b' - a')) ≤ circleLen A →
          ENNReal.ofReal β * circleLen (Fi '' circleArc a' b') ≤ circleLen (Fi '' A) := by
  obtain ⟨F₀, hF₀q, -, -, -⟩ := id hq
  have hK : 1 ≤ K := hF₀q.2.1
  obtain ⟨L, c₀, hL, hc₀, hdata⟩ := s07d_p3_reflection_data K hK
  obtain ⟨ρ, Φ, F, Fi, a, ha, ⟨hΦD, hΦq, hΦs, hΩ, hΩs⟩, ⟨hF, hF0, hFb, hFq, hFi, hΦE, hFh⟩,
    -, hR2, hR3, -, hcol, htr⟩ := hdata Ω Ωs hq f g h hw
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  -- `F` and `Fi` preserve `∂𝔻`
  have hsph : ∀ ζ ∈ sphere (0 : ℂ) 1, F ζ ∈ sphere (0 : ℂ) 1 := by
    intro ζ hζ
    have hc : F ζ ∈ closedBall (0 : ℂ) 1 := hF.1.mapsTo (sphere_subset_closedBall hζ)
    rcases (mem_closedBall_zero_iff.mp hc).lt_or_eq with hlt | heq
    · exfalso
      have h1 : diskMobius 0 a (F ζ) ∈ unitDisc := by
        rw [← (s07b_mob_conformal 0 ha1).2.2]
        exact mem_image_of_mem _ (mem_ball_zero_iff.mpr hlt)
      rw [hFh ζ hζ] at h1
      have h2 : ‖h ζ‖ = 1 := mem_sphere_zero_iff_norm.mp (hw.2.2.2.1 hζ)
      have h3 : ‖h ζ‖ < 1 := mem_ball_zero_iff.mp h1
      rw [h2] at h3
      exact lt_irrefl _ h3
    · exact mem_sphere_zero_iff_norm.mpr heq
  obtain ⟨hFD, hFs⟩ := s07d_p3_disk_onto hF hFq hsph
  have hFisph : ∀ ζ ∈ sphere (0 : ℂ) 1, Fi ζ ∈ sphere (0 : ℂ) 1 := by
    intro ζ hζ
    have hc : Fi ζ ∈ closedBall (0 : ℂ) 1 := by
      obtain ⟨x, hx, hxe⟩ := hF.1.surjOn (sphere_subset_closedBall hζ)
      rw [← hxe, (hFi x hx).1]
      exact hx
    rcases (mem_closedBall_zero_iff.mp hc).lt_or_eq with hlt | heq
    · exfalso
      have h1 := hFD _ (mem_ball_zero_iff.mpr hlt)
      rw [(hFi ζ (sphere_subset_closedBall hζ)).2] at h1
      have h' : ‖ζ‖ < 1 := mem_ball_zero_iff.mp h1
      rw [mem_sphere_zero_iff_norm.mp hζ] at h'
      exact lt_irrefl _ h'
    · exact mem_sphere_zero_iff_norm.mpr heq
  refine ⟨F, Fi, a, ha, fun ζ hζ => ⟨hsph ζ hζ, hFisph ζ hζ⟩, hFi, hFh, ?_⟩
  -- `Φ`: a homeomorphism with `Φ(∂𝔻) ⊆ Γ`
  obtain ⟨T, hT⟩ := t1_homeomorph hΦq hΦs
  have hΦc : Continuous Φ := by rw [← hT]; exact T.continuous
  have hΦi : Function.Injective Φ := by rw [← hT]; exact T.injective
  have hΦsur : Function.Surjective Φ := by rw [← hT]; exact T.surjective
  have hΦΓ : ∀ ζ ∈ sphere (0 : ℂ) 1, Φ ζ ∈ curveOf Ω Ωs := by
    intro ζ hζ
    have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
    show Φ ζ ∉ Ω ∪ Ωs
    rintro (h1 | h1)
    · rw [← hΩ] at h1
      obtain ⟨z, hz, hze⟩ := h1
      rw [hΦi hze] at hz
      have h' : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hz
      rw [hζ1] at h'
      exact lt_irrefl _ h'
    · rw [← hΩs] at h1
      obtain ⟨z, hz, hze⟩ := h1
      rw [hΦi hze] at hz
      have h' : 1 < ‖ζ‖ := hz
      rw [hζ1] at h'
      exact lt_irrefl _ h'
  have hΓsub : curveOf Ω Ωs ⊆ Φ '' sphere (0 : ℂ) 1 := by
    intro x hx
    obtain ⟨z, rfl⟩ := hΦsur x
    refine ⟨z, ?_, rfl⟩
    rcases lt_trichotomy ‖z‖ 1 with h1 | h1 | h1
    · exact absurd (Or.inl (hΩ ▸ mem_image_of_mem Φ (mem_ball_zero_iff.mpr h1))) hx
    · exact mem_sphere_zero_iff_norm.mpr h1
    · exact absurd (Or.inr (hΩs ▸ mem_image_of_mem Φ (show z ∈ unitDiscExterior from h1))) hx
  have hΓb : Bornology.IsBounded (curveOf Ω Ωs) :=
    ((isCompact_sphere (0 : ℂ) 1).image hΦc).isBounded.subset hΓsub
  have hΓd : 0 < diam (curveOf Ω Ωs) := by
    have h1 : Φ 1 ∈ curveOf Ω Ωs := hΦΓ 1 (by simp)
    have h2 : Φ (-1) ∈ curveOf Ω Ωs := hΦΓ (-1) (by simp)
    have hne : Φ 1 ≠ Φ (-1) := fun h => by
      have := hΦi h
      norm_num at this
    exact lt_of_lt_of_le (dist_pos.mpr hne) (dist_le_diam_of_mem hΓb h1 h2)
  -- uniform continuity of `Φ` on `B̄(0, 2)` (for the collar)
  obtain ⟨δu, hδu, hunif⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_closedBall (0 : ℂ) 2).uniformContinuousOn_of_continuous hΦc.continuousOn)
    (c₀ * diam (curveOf Ω Ωs)) (by positivity)
  -- `Φ' = e^φ` with `φ'` Carleson (`f ∘ M`)
  have hfM := s07b_comp_mob_conformal hw.1 0 ha1
  have hBM := s07d_p6_bmoa hq hw.1 ha1 hB
  obtain ⟨φ, hφd, -, hφe, A, hA, hcar⟩ := s07d_p1_logderiv _ hfM.1
    (fun z hz => deriv_ne_zero_of_injOn isOpen_ball hfM.1 hfM.2.1 hz) hBM
  have hΦd : DifferentiableOn ℂ Φ unitDisc := hfM.1.congr hΦD
  have hφe' : ∀ z ∈ unitDisc, Complex.exp (φ z) = deriv Φ z := fun z hz => by
    rw [Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) hΦD)]
    exact hφe z hz
  obtain ⟨Qk, M, hQk, hM, hstA⟩ := s07d_p6_stageA L A hL hA
  obtain ⟨δ, hδ, hharm⟩ := s07d_p6_harm (L * Qk) (2 * L ^ 2 * M) (1 / (L * M ^ 2))
    (one_le_mul_of_one_le_of_one_le hL hQk) (by positivity) (by positivity)
  obtain ⟨Cs, hCs, hscale⟩ := s07d_p6_scale L (Real.arcosh (1 + 128 * Qk)) hL
    (Real.arcosh_nonneg (by linarith))
  -- `Gg = Φ ∘ R`: a homeomorphism of `ℂ` equal to `g` on `𝔻*`
  obtain ⟨R, hRc, hRi, hRs, hRin, hRout⟩ := s07d_p6_rext hF hF0 hsph hFD hFs
  have hGgc : Continuous fun z => Φ (R z) := hΦc.comp hRc
  have hGg : IsHomeomorphOnto (fun z => Φ (R z)) univ univ := by
    have h1 := qcl_f_isHomeomorphOnto_of_injOn isOpen_univ hGgc.continuousOn
      (hΦi.comp hRi).injOn
    have hsurj : (fun z => Φ (R z)) '' univ = univ :=
      image_univ_of_surjective (f := fun z => Φ (R z)) (hΦsur.comp hRs)
    rw [hsurj] at h1
    exact h1
  have hGgg : EqOn (fun z => Φ (R z)) g unitDiscExterior := by
    intro z hz
    show Φ (R z) = g z
    rw [hRout z hz]
    have hj := s07d_p3_jRefl_ext hz
    have hFj : F (jRefl z) ∈ unitDisc := hFD _ hj.1
    have hFj0 : F (jRefl z) ≠ 0 := fun h0 => hj.2 (hF.1.injOn (ball_subset_closedBall hj.1)
      (mem_closedBall_self zero_le_one) (h0.trans hF0.symm))
    rw [hΦE _ (s07d_p3_jRefl_int hFj hFj0), s07d_p3_jRefl_jRefl,
      (hFi _ (ball_subset_closedBall hj.1)).1, s07d_p3_jRefl_jRefl]
  refine ⟨π * δ / Cs, min (1 / (16 * Qk)) (δu / 4), by positivity, by positivity,
    (min_le_left _ _).trans (by rw [div_le_one (by positivity)]; linarith), ?_⟩
  intro a' b' hab hℓ A' hAs hAm hAl
  have hℓ0 : 0 < b' - a' := sub_pos.mpr hab
  have hℓQ : b' - a' ≤ 1 / (16 * Qk) := hℓ.trans (min_le_left _ _)
  have hℓu : b' - a' ≤ δu / 4 := hℓ.trans (min_le_right _ _)
  have hℓ16 : b' - a' ≤ 1 / 16 := hℓQ.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith)
  obtain ⟨𝒟, κ, s, X0, hs, hDo, hκq, hκs, hκD, hκcl, hκfr, hκbl, h9, hXA, hXcl, hXm, hXμ, hAR,
    hlen, hΦX⟩ := hstA Φ φ hΦq hΦs hΦd hφd hφe' hcar a' b' hab (by linarith) A' hAs hAm hAl
  -- the points `c`, `c_I`, `ζ₀` on the radius through the midpoint
  have hnorm : ∀ r : ℝ, 0 ≤ r → ‖((r : ℝ) : ℂ) * Complex.exp (((a' + b') / 2 : ℝ) * I)‖ = r :=
    fun r hr => by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hr]
  have hdiffn : ∀ r r' : ℝ, ‖((r : ℝ) : ℂ) * Complex.exp (((a' + b') / 2 : ℝ) * I) -
      ((r' : ℝ) : ℂ) * Complex.exp (((a' + b') / 2 : ℝ) * I)‖ = |r - r'| := fun r r' => by
    rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
  set c : ℂ := ((1 - (b' - a') / 2 : ℝ) : ℂ) * Complex.exp (((a' + b') / 2 : ℝ) * I) with hcdef
  set cI : ℂ := ((1 - (b' - a') : ℝ) : ℂ) * Complex.exp (((a' + b') / 2 : ℝ) * I) with hcIdef
  have hcn : ‖c‖ = 1 - (b' - a') / 2 := hnorm _ (by linarith)
  have hcIn : ‖cI‖ = 1 - (b' - a') := hnorm _ (by linarith)
  have hcc : ‖cI - c‖ ≤ (b' - a') / 2 := by
    rw [hcIdef, hcdef, hdiffn]
    rw [abs_le]
    constructor <;> linarith
  have hcl9 : closure 𝒟 ⊆ closedBall c (9 * ((b' - a') / 8)) :=
    (closure_mono (h9.trans inter_subset_right)).trans closure_ball_subset_closedBall
  have h0c : ∀ z ∈ closedBall c (9 * ((b' - a') / 8)), z ≠ 0 := by
    intro z hz h
    rw [h, mem_closedBall, dist_eq_norm, zero_sub, norm_neg, hcn] at hz
    linarith
  have h0 : (0 : ℂ) ∉ κ '' closedBall (0 : ℂ) 1 := by
    rw [hκcl]
    exact fun h => h0c 0 (hcl9 h) rfl
  obtain ⟨G, hGq, hGs, hGD, hGS, w₀, hw₀, hG0, hw₀p⟩ :=
    htr Qk κ hκq hκs (by rw [hκD]; exact h9.trans inter_subset_left) h0
  obtain ⟨huD, hu0, hucosh⟩ := s07d_p6_deep hQk hℓ0 hℓQ hcn hcIn hcc hκs (by rw [hκD]; exact h9)
    (by rw [hκcl]; exact hcl9) hκbl hw₀ hw₀p
  have hdist : diskDist (κ w₀) cI ≤ Real.arcosh (1 + 128 * Qk) := by
    show Real.arcosh (diskCoshDist (κ w₀) cI) ≤ _
    have hu1 : ‖κ w₀‖ < 1 := mem_ball_zero_iff.mp huD
    have h1 : 1 ≤ diskCoshDist (κ w₀) cI := by
      unfold diskCoshDist
      have hA1 : 0 < 1 - ‖κ w₀‖ ^ 2 := by nlinarith [norm_nonneg (κ w₀)]
      have hA2 : 0 < 1 - ‖cI‖ ^ 2 := by rw [hcIn]; nlinarith
      have : 0 ≤ 2 * ‖κ w₀ - cI‖ ^ 2 / ((1 - ‖κ w₀‖ ^ 2) * (1 - ‖cI‖ ^ 2)) := by positivity
      linarith
    exact (Real.arcosh_le_arcosh (by linarith) (by linarith)).mpr hucosh
  -- a Riemann map `ψ` of `V = G(𝔻)` with `ψ 0 = G 0`
  have hVq : IsBoundedKQuasicircle (G '' unitDisc) (G '' unitDiscExterior) (L * Qk) :=
    ⟨G, hGq, hGs, rfl, rfl⟩
  obtain ⟨ψ₀, hψ₀⟩ := s07_exists_riemannMap hVq
  obtain ⟨p, hp, hpe⟩ : G 0 ∈ ψ₀ '' unitDisc := by
    rw [hψ₀.2.2]
    exact mem_image_of_mem G (mem_ball_self one_pos)
  obtain ⟨hψ, hψ0, -⟩ := s02_disc_recenter hψ₀ hp
  -- `Φ(∂𝒟)` lies in the collar, so `ρ` is `L`-bi-Lipschitz there
  have hYcol : ∀ y ∈ Φ '' frontier 𝒟, infDist y (curveOf Ω Ωs) < c₀ * diam (curveOf Ω Ωs) := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ closedBall c (9 * ((b' - a') / 8)) := hcl9 (frontier_subset_closure hz)
    rw [mem_closedBall, dist_eq_norm] at hz'
    set ζ₀ : ℂ := ((1 : ℝ) : ℂ) * Complex.exp (((a' + b') / 2 : ℝ) * I) with hζ₀def
    have hζ₀1 : ‖ζ₀‖ = 1 := hnorm 1 zero_le_one
    have hcζ : ‖c - ζ₀‖ = (b' - a') / 2 := by
      rw [hcdef, hζ₀def, hdiffn, abs_of_nonpos (by linarith)]
      ring
    have hzζ : ‖z - ζ₀‖ ≤ 13 * (b' - a') / 8 := by
      calc ‖z - ζ₀‖ ≤ ‖z - c‖ + ‖c - ζ₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 13 * (b' - a') / 8 := by rw [hcζ]; linarith
    have hz2 : z ∈ closedBall (0 : ℂ) 2 := by
      rw [mem_closedBall_zero_iff]
      have := norm_le_norm_add_norm_sub' z ζ₀
      rw [norm_sub_rev] at hzζ
      linarith [norm_sub_rev ζ₀ z]
    have hζ2 : ζ₀ ∈ closedBall (0 : ℂ) 2 := by
      rw [mem_closedBall_zero_iff, hζ₀1]
      norm_num
    have hd := hunif z hz2 ζ₀ hζ2 (by rw [dist_eq_norm]; linarith)
    exact (infDist_le_dist_of_mem (hΦΓ ζ₀ (mem_sphere_zero_iff_norm.mpr hζ₀1))).trans_lt hd
  have hYbl : ∀ x ∈ Φ '' frontier 𝒟, ∀ y ∈ Φ '' frontier 𝒟,
      ‖ρ x - ρ y‖ ≤ L * ‖x - y‖ ∧ ‖x - y‖ ≤ L * ‖ρ x - ρ y‖ :=
    fun x hx y hy => hcol x y (hYcol x hx) (hYcol y hy)
  have hGSe : G '' sphere (0 : ℂ) 1 = ρ '' (Φ '' frontier 𝒟) := by rw [hGS, hκfr]
  have hARG : ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      μH[1] (G '' sphere 0 1 ∩ ball z r) ≤ ENNReal.ofReal (2 * L ^ 2 * M * r) := by
    rw [hGSe]
    exact s07d_p6_armap (by positivity) hYbl hAR
  obtain ⟨Ψ, hΨh, hΨψ, -, hharmX⟩ := hharm (G '' unitDisc) (ψ₀ ∘ blaschke (-p)) G hψ hGq hGs rfl
    (by rw [hψ0, hpe]) hARG
  -- `X = Φ(X0) ⊆ Γ ∩ ∂V` carries a fixed fraction of `|∂V|`
  have hX0s : X0 ⊆ sphere (0 : ℂ) 1 := hXA.trans (hAs.trans (s07_circleArc_subset a' b'))
  have hX0fr : X0 ⊆ frontier 𝒟 := by
    intro x hx
    rw [hDo.frontier_eq]
    refine ⟨hXcl hx, fun h => ?_⟩
    have h1 : ‖x‖ < 1 := mem_ball_zero_iff.mp (h9 h).1
    rw [mem_sphere_zero_iff_norm.mp (hX0s hx)] at h1
    exact lt_irrefl _ h1
  have hXsubG : Φ '' X0 ⊆ G '' sphere (0 : ℂ) 1 := by
    rw [hGSe]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨Φ x, mem_image_of_mem Φ (hX0fr hx), hR2 _ (hΦΓ x (hX0s hx))⟩
  have hXm' : MeasurableSet (Φ '' X0) :=
    hXm.image_of_continuousOn_injOn hΦc.continuousOn hΦi.injOn
  have hGlen : μH[1] (G '' sphere (0 : ℂ) 1) ≤
      ENNReal.ofReal L * ENNReal.ofReal (M * s * ((b' - a') / 8)) := by
    rw [hGSe]
    calc μH[1] (ρ '' (Φ '' frontier 𝒟)) ≤ ENNReal.ofReal L * μH[1] (Φ '' frontier 𝒟) :=
          s07d_p2_ah_lip (by positivity) fun x hx y hy => by
            rw [dist_eq_norm, dist_eq_norm]
            exact (hYbl x hx y hy).1
      _ ≤ _ := by gcongr
  have hXlow : ENNReal.ofReal (s / M * ((b' - a') / π)) ≤ μH[1] (Φ '' X0) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    calc ENNReal.ofReal (s / M) * ENNReal.ofReal ((b' - a') / π) ≤
          ENNReal.ofReal (s / M) * μH[1] X0 := by gcongr
      _ ≤ _ := hΦX
  have hXne : μH[1] (Φ '' X0) ≠ 0 :=
    (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hXlow).ne'
  have hθ : ENNReal.ofReal (1 / (L * M ^ 2)) * μH[1] (G '' sphere (0 : ℂ) 1) ≤ μH[1] (Φ '' X0) := by
    have hM0 : 0 < M := by linarith
    have hL0 : 0 < L := by linarith
    calc ENNReal.ofReal (1 / (L * M ^ 2)) * μH[1] (G '' sphere (0 : ℂ) 1)
        ≤ ENNReal.ofReal (1 / (L * M ^ 2)) *
          (ENNReal.ofReal L * ENNReal.ofReal (M * s * ((b' - a') / 8))) := by gcongr
      _ = ENNReal.ofReal (s * (b' - a') / (8 * M)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
      _ ≤ ENNReal.ofReal (s / M * ((b' - a') / π)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [show s / M * ((b' - a') / π) = s * (b' - a') / (M * π) by ring]
          exact div_le_div_of_nonneg_left (by positivity) (by positivity)
            (by nlinarith [Real.pi_lt_four])
      _ ≤ _ := hXlow
  have hδX := hharmX (Φ '' X0) hXm' hXsubG hXne hθ
  -- P5: from `V` at `ψ 0` to `Ωs` at `w = jRefl (Fi u)`
  obtain ⟨x₁, hx₁, hx₁e⟩ : κ w₀ ∈ F '' unitDisc := by rw [hFs]; exact huD
  have hFiu : Fi (κ w₀) = x₁ := by rw [← hx₁e, (hFi x₁ (ball_subset_closedBall hx₁)).1]
  have hx₁0 : x₁ ≠ 0 := fun h => hu0 (by rw [← hx₁e, h, hF0])
  have hwE : jRefl (Fi (κ w₀)) ∈ unitDiscExterior := by
    rw [hFiu]
    exact s07d_p3_jRefl_int hx₁ hx₁0
  have hzw : g (jRefl (Fi (κ w₀))) = (ψ₀ ∘ blaschke (-p)) 0 := by
    rw [hψ0, hpe, hG0, hΦE _ (s07d_p3_jRefl_int huD hu0), s07d_p3_jRefl_jRefl]
  have hVW : G '' unitDisc ⊆ Ωs := by
    rw [hGD, hκD]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hyD := (h9 hy).1
    have hy0 : y ≠ 0 := h0c y (hcl9 (subset_closure hy))
    exact (hR3 (Φ y) (hΩ ▸ mem_image_of_mem Φ hyD) fun h => hy0 (hΦi h)).1
  have hXGg : Φ '' X0 ⊆ (fun z => Φ (R z)) '' sphere (0 : ℂ) 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hxs := hX0s hx
    refine ⟨Fi x, hFisph x hxs, ?_⟩
    show Φ (R (Fi x)) = Φ x
    rw [hRin _ (sphere_subset_closedBall (hFisph x hxs)), (hFi x (sphere_subset_closedBall hxs)).2]
  have hP5 := s07d_p5_transfer_ext hψ hw.2.1 hVW hΨh hΨψ hGg hGgg (Φ '' X0) hXm' hXGg
    (mem_ball_self one_pos) hwE hzw
  have hext := s07d_p6_extP hwE ((fun z => Φ (R z)) ⁻¹' (Φ '' X0)) (hXm'.preimage hGgc.measurable)
  -- `|Fi(A)| ≥ π δ (1 - |Fi u|)`
  set r := ‖Fi (κ w₀)‖ with hrdef
  have hr0 : 0 < r := by rw [hrdef, hFiu]; exact norm_pos_iff.mpr hx₁0
  have hr1 : r < 1 := by rw [hrdef, hFiu]; exact mem_ball_zero_iff.mp hx₁
  set Lc := (circleLen ((fun z => Φ (R z)) ⁻¹' (Φ '' X0))).toReal with hLcdef
  have hLc0 : 0 ≤ Lc := ENNReal.toReal_nonneg
  have hmain : π * δ * (1 - r) ≤ Lc := by
    have h := hδX.trans (hP5.trans hext)
    rw [s07d_p3_jRefl_norm, ← hrdef] at h
    have hq : (2 * π)⁻¹ * ((r⁻¹ + 1) / (r⁻¹ - 1) * Lc) = (1 + r) * Lc / (2 * π * (1 - r)) := by
      have : 1 - r ≠ 0 := by linarith
      field_simp
    rw [hq, le_div_iff₀ (by have := Real.pi_pos; nlinarith)] at h
    nlinarith [Real.pi_pos]
  have hsubA : circleLen ((fun z => Φ (R z)) ⁻¹' (Φ '' X0)) ≤ circleLen (Fi '' A') := by
    unfold circleLen
    refine measure_mono fun θ hθ => ⟨hθ.1, ?_⟩
    obtain ⟨x, hx, hxe⟩ := hθ.2
    have he : Complex.exp (θ * I) ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall_zero_iff, Complex.norm_exp_ofReal_mul_I]
    have hxR : x = R (Complex.exp (θ * I)) := hΦi hxe
    rw [hRin _ he] at hxR
    rw [hxR] at hx
    exact ⟨F (Complex.exp (θ * I)), hXA hx, (hFi _ he).1⟩
  have hsc := hscale F Fi hF hF0 hFb hFq hFi a' b' hab (by linarith) (κ w₀) huD hdist
  have hCs' : Cs ≠ 0 := hCs.ne'
  calc ENNReal.ofReal (π * δ / Cs) * circleLen (Fi '' circleArc a' b')
      ≤ ENNReal.ofReal (π * δ / Cs) * ENNReal.ofReal (Cs * (1 - r)) := by gcongr
    _ = ENNReal.ofReal (π * δ * (1 - r)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ ≤ circleLen ((fun z => Φ (R z)) ⁻¹' (Φ '' X0)) := by
        rw [ENNReal.ofReal_le_iff_le_toReal (s07d_p6_cl_ne_top _)]
        exact hmain
    _ ≤ _ := hsubA

/-- **P6** (w1; per-arc assembly). For a bounded `K`-quasicircle with welding `h` and
`log f' ∈ BMOA`, the inverse welding `k = h⁻¹` is a circle homeomorphism satisfying one
lower-bound weak `A∞` pair on short arcs: `|A| ≥ (1 - α)|I| ⇒ |k(A)| ≥ β |k(I)|`. -/
theorem s07d_p6_weak {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K)
    {f g h : ℂ → ℂ} (hw : IsDiskWelding Ω Ωs f g h) (hB : LogDerivBMOA f) :
    ∃ k : ℂ → ℂ, IsCircleHomeo k ∧
      (∀ ζ ∈ sphere (0 : ℂ) 1, k ζ ∈ sphere (0 : ℂ) 1 ∧ h (k ζ) = ζ ∧ k (h ζ) = ζ) ∧
      ∃ α β ℓ₀ : ℝ, 0 < α ∧ 0 < β ∧ 0 < ℓ₀ ∧
      ∀ a b : ℝ, a < b → b - a ≤ ℓ₀ → ∀ A ⊆ circleArc a b, MeasurableSet A →
        ENNReal.ofReal (1 - α) * circleLen (circleArc a b) ≤ circleLen A →
          ENNReal.ofReal β * circleLen (k '' circleArc a b) ≤ circleLen (k '' A) := by
  -- Route: `s07d_p6_core` gives the weak pair for `Fi` (normalised coordinates); `k ∘ M = Fi` on
  -- `∂𝔻`, so P7c makes `k ∘ M` strongly quasisymmetric, hence `k = (k ∘ M) ∘ M⁻¹` too
  -- (`sqs_circle_comp`, `sqs_circle_mobius`); strong quasisymmetry gives the pair for `k` with
  -- `α = min (δ(1/2)) (1/2)`, `β = 1/2`, `ℓ₀ = 2π`.
  obtain ⟨F, Fi, a, ha, hsph, hFi, hFh, β, ℓ₀, hβ, hℓ₀, hℓ₁, hcore⟩ := s07d_p6_core hq hw hB
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  obtain ⟨H₀, hH₀q, hH₀s, hH₀b⟩ := id (s07_weld_admitsExt hq hw)
  have hh : IsCircleHomeo h := s07_circleHomeo_of_qcExt hH₀q hH₀s hH₀b
  obtain ⟨k, hk⟩ := s07b_circle_inv hh
  obtain ⟨H, hHm, hHc, hHp, hHl⟩ := hh
  obtain ⟨Gk, hGm, hGc, hGp, hGl, -, -⟩ :=
    s07_inv_lift hHm hHc hHp hHl fun ζ hζ => ⟨(hk ζ hζ).1, (hk ζ hζ).2.1⟩
  -- `k₁ = k ∘ M` is a circle homeomorphism equal to `Fi` on `∂𝔻`
  obtain ⟨δM, hδM⟩ := sqs_circle_mobius 0 a ha
  obtain ⟨HM, hHMm, hHMc, hHMp, hHMl⟩ := hδM.1
  have hk₁c : IsCircleHomeo (fun z => k (diskMobius 0 a z)) :=
    ⟨Gk ∘ HM, hGm.comp hHMm, hGc.comp hHMc, fun θ => by simp only [Function.comp, hHMp, hGp],
      fun θ => by
        show k (diskMobius 0 a (Complex.exp (θ * I))) = _
        rw [hHMl, hGl]
        rfl⟩
  have hk₁Fi : ∀ ζ ∈ sphere (0 : ℂ) 1, k (diskMobius 0 a ζ) = Fi ζ := by
    intro ζ hζ
    have h1 : diskMobius 0 a ζ = h (Fi ζ) := by
      rw [← hFh _ (hsph ζ hζ).2, (hFi ζ (sphere_subset_closedBall hζ)).2]
    rw [h1, (hk _ (hsph ζ hζ).2).2.2]
  have himg : ∀ S ⊆ sphere (0 : ℂ) 1, (fun z => k (diskMobius 0 a z)) '' S = Fi '' S :=
    fun S hS => image_congr fun ζ hζ => hk₁Fi ζ (hS hζ)
  obtain ⟨δf, hδf⟩ := s07d_p7_sqs_compl (1 / 4) β ℓ₀ (by norm_num) hβ hℓ₀
  have hk₁ : IsStronglyQSWith (fun z => k (diskMobius 0 a z)) δf := by
    refine hδf _ hk₁c fun a' b' hab hℓ A hA hAm hAl => ?_
    rw [himg _ (s07_circleArc_subset a' b'), himg _ (hA.trans (s07_circleArc_subset a' b'))]
    refine hcore a' b' hab hℓ A hA hAm ?_
    rw [s07d_p6_cl_arc hab.le (by linarith [Real.pi_gt_three]),
      ← ENNReal.ofReal_mul (by norm_num)] at hAl
    convert hAl using 2
    ring
  have ha' : -a ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [norm_neg]; exact ha1)
  obtain ⟨δk, hδk⟩ := sqs_circle_comp _ _ ⟨δf, hk₁⟩ (sqs_circle_mobius 0 (-a) ha')
  have hkeq : EqOn k ((fun z => k (diskMobius 0 a z)) ∘ diskMobius 0 (-a)) (sphere (0 : ℂ) 1) :=
    fun ζ hζ => by
      show k ζ = k (diskMobius 0 a (diskMobius 0 (-a) ζ))
      rw [s07d_p6_mob_id ha1 (mem_sphere_zero_iff_norm.mp hζ).le]
  have hkS : IsStronglyQSWith k δk := s07_qi_sqs_congr hδk hkeq
  obtain ⟨hδ0, hq2⟩ := hkS.2 (1 / 2) (by norm_num)
  refine ⟨k, hkS.1, hk, min (δk (1 / 2)) (1 / 2), 1 / 2, 2 * π, lt_min hδ0 (by norm_num),
    by norm_num, by positivity, ?_⟩
  intro a' b' hab hℓ A hA hAm hAl
  have hIc : IsClosed (circleArc a' b') :=
    (isCompact_Icc.image (by fun_prop : Continuous fun θ : ℝ => Complex.exp (θ * I))).isClosed
  have hEm : MeasurableSet (circleArc a' b' \ A) := hIc.measurableSet.diff hAm
  -- `|I ∖ A| ≤ α |I|`
  have hsplit : circleLen (circleArc a' b' \ A) + circleLen A = circleLen (circleArc a' b') := by
    unfold circleLen
    have hm : MeasurableSet {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ Complex.exp (θ * I) ∈ A} :=
      measurableSet_Ico.inter (hAm.preimage (by fun_prop))
    rw [← measure_union _ hm]
    · congr 1
      ext θ
      constructor
      · rintro (h | h)
        · exact ⟨h.1, h.2.1⟩
        · exact ⟨h.1, hA h.2⟩
      · rintro ⟨h1, h2⟩
        by_cases h3 : Complex.exp (θ * I) ∈ A
        · exact Or.inr ⟨h1, h3⟩
        · exact Or.inl ⟨h1, h2, h3⟩
    · rw [Set.disjoint_left]
      rintro θ ⟨-, -, h⟩ ⟨-, h'⟩
      exact h h'
  set α := min (δk (1 / 2)) (1 / 2) with hαdef
  have hα1 : α ≤ 1 / 2 := min_le_right _ _
  have hα0 : 0 ≤ α := (lt_min hδ0 (by norm_num)).le
  have hfinI := s07d_p6_cl_ne_top (circleArc a' b')
  have hE : circleLen (circleArc a' b' \ A) ≤ ENNReal.ofReal (δk (1 / 2)) * circleLen (circleArc a' b') := by
    have h1 : circleLen (circleArc a' b' \ A) + ENNReal.ofReal (1 - α) * circleLen (circleArc a' b') ≤
        ENNReal.ofReal α * circleLen (circleArc a' b') +
          ENNReal.ofReal (1 - α) * circleLen (circleArc a' b') := by
      calc _ ≤ circleLen (circleArc a' b' \ A) + circleLen A := by gcongr
        _ = circleLen (circleArc a' b') := hsplit
        _ = _ := by
            rw [← add_mul, ← ENNReal.ofReal_add hα0 (by linarith)]
            simp
    have h2 := ENNReal.le_of_add_le_add_right
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinI) h1
    exact h2.trans (by gcongr; exact min_le_left _ _)
  have h3 := hq2 a' b' hab hℓ (circleArc a' b' \ A) diff_subset hEm hE
  -- `|k(I)| ≤ |k(A)| + |k(I ∖ A)| ≤ |k(A)| + |k(I)|/2`
  have hkI : circleLen (k '' circleArc a' b') ≤ circleLen (k '' A) + circleLen (k '' (circleArc a' b' \ A)) := by
    calc circleLen (k '' circleArc a' b') = circleLen (k '' A ∪ k '' (circleArc a' b' \ A)) := by
          rw [← image_union, union_diff_cancel hA]
      _ ≤ _ := s07d_p6_cl_union _ _
  have hfinK := s07d_p6_cl_ne_top (k '' circleArc a' b')
  have h4 : ENNReal.ofReal (1 / 2) * circleLen (k '' circleArc a' b') +
      ENNReal.ofReal (1 / 2) * circleLen (k '' circleArc a' b') ≤
      circleLen (k '' A) + ENNReal.ofReal (1 / 2) * circleLen (k '' circleArc a' b') := by
    calc _ = circleLen (k '' circleArc a' b') := by
          rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
      _ ≤ _ := hkI.trans (by gcongr)
  exact ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinK) h4

/-- **B2 ⇒ B5** (w1): `thm_shen_wei_B5` (→). From P6, P7c and `sqs_circle_inv`. -/
theorem s07d_b2_b5 {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K)
    {f g h : ℂ → ℂ} (hw : IsDiskWelding Ω Ωs f g h) (hB : LogDerivBMOA f) :
    IsStronglyQS h := by
  obtain ⟨k, hk, hkh, α, β, ℓ₀, hα, hβ, hℓ₀, hweak⟩ := s07d_p6_weak hq hw hB
  obtain ⟨δf, hδf⟩ := s07d_p7_sqs_compl α β ℓ₀ hα hβ hℓ₀
  exact sqs_circle_inv k h ⟨δf, hδf k hk hweak⟩ fun ζ hζ =>
    ⟨hw.2.2.2.1 hζ, (hkh ζ hζ).2.2⟩

/-- Theorem 2.13 `thm:shen-wei`, (B2) ⇔ (B5), `sec02-prelim.tex:598`: `log f' ∈ BMOA` iff the
welding `h = f⁻¹ ∘ g` is strongly quasisymmetric (stated for bounded quasicircles, where the
welding is `IsDiskWelding`). -/
theorem thm_shen_wei_B5 {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K)
    {f g h : ℂ → ℂ} (hw : IsDiskWelding Ω Ωs f g h) :
    LogDerivBMOA f ↔ IsStronglyQS h := by
  -- (B2) ⇒ (B5) is `s07d_b2_b5` (Round BMO P6/P7); (B5) ⇒ (B2) is `s07b_B5_bwd`.
  exact ⟨s07d_b2_b5 hq hw, s07b_B5_bwd hq hw⟩

end EpsteinVMO
