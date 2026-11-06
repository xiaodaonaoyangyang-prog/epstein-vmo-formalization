import EpsteinVMO.S07_Transfer
import EpsteinVMO.S07c_FKPSmall
import TakhtajanTeo.Ch1.CuiBound
import VanishingCarleson.MainTheorem

/-!
# Shen–Wei (B5), (V5): host module (Round B)

Created by the leader on 2026-11-05 (Round B, `collaboration/ROUND_B.md`). This module hosts the proofs of
the Shen–Wei items whose proofs need `S07` (Carathéodory extension, `sqs_circle_inv`, the welding gluing of
Lane U), the Takhtajan–Teo pointwise Schwarzian bound (`TakhtajanTeo.CUI.cui_pointwise_gen`, Lane A) and the
vendored `VanishingCarleson.main_theorem` (Lane C; importable since bypass V1, see `VENDORED.md`).

`thm_shen_wei_B5` and `thm_shen_wei_V5` will be moved here from `S02_Prelim` byte-identically (docstring and
statement unchanged) when their proofs are assembled; they have no users in `S02`–`S13`.
`thm_shen_wei_B5` was moved on to `S07d_BMO` byte-identically (Round BMO P8, 2026-11-06), since its
(→) direction is `s07d_b2_b5` there.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace EpsteinVMO

open LiZhongQC

/-- W-AZ1 helper (layer cake, cubic kernel; the `k = 3` analogue of `s02_vc_layer`): writing
`h²/(h + d)³ = ∫_d^∞ 3h²/(h + s)⁴ ds` (`s02_vc_tail`) and using Tonelli,
`∫ h²/(h + |z − ξ|)³ dμ = ∫_0^∞ 3h²/(h + s)⁴ μ(D(ξ, s)) ds`; the growth bounds `a s` (`s < δ`) and `b s`
(all `s`) give at most `3a/2 + 3bh²/(2δ²)`. -/
theorem s07b_az1_layer {μ : Measure ℂ} [SFinite μ] {ξ : ℂ} {h a b δ : ℝ} (hh : 0 < h) (hδ : 0 < δ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsmall : ∀ s : ℝ, 0 < s → s < δ → μ (ball ξ s) ≤ ENNReal.ofReal (a * s))
    (hall : ∀ s : ℝ, 0 < s → μ (ball ξ s) ≤ ENNReal.ofReal (b * s)) :
    ∫⁻ z, ENNReal.ofReal (h ^ 2 / (h + ‖z - ξ‖) ^ 3) ∂μ ≤
      ENNReal.ofReal (3 / 2 * a + 3 / 2 * b * h ^ 2 / δ ^ 2) := by
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ≥0∞, G = fun s =>
      ENNReal.ofReal (h ^ 2) * ENNReal.ofReal (((3 : ℕ) : ℝ) / (h + s) ^ (3 + 1)) := ⟨_, rfl⟩
  have hGm : Measurable G := by
    rw [hG]
    exact measurable_const.mul (ENNReal.measurable_ofReal.comp (by fun_prop))
  have hrep : ∀ z : ℂ, ENNReal.ofReal (h ^ 2 / (h + ‖z - ξ‖) ^ 3) =
      ∫⁻ s, (Ioi ‖z - ξ‖).indicator G s := by
    intro z
    rw [lintegral_indicator measurableSet_Ioi]
    simp only [hG]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      s02_vc_tail hh (norm_nonneg _) (by norm_num : 1 ≤ 3), ← ENNReal.ofReal_mul (sq_nonneg h)]
    congr 1
    ring
  have hFm : Measurable (Function.uncurry fun (z : ℂ) (s : ℝ) => (Ioi ‖z - ξ‖).indicator G s) := by
    show Measurable fun p : ℂ × ℝ => (Ioi ‖p.1 - ξ‖).indicator G p.2
    have e : (fun p : ℂ × ℝ => (Ioi ‖p.1 - ξ‖).indicator G p.2) =
        fun p : ℂ × ℝ => if ‖p.1 - ξ‖ < p.2 then G p.2 else 0 := by
      funext p
      simp only [Set.indicator_apply, mem_Ioi]
    rw [e]
    exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop))
      (hGm.comp measurable_snd) measurable_const
  obtain ⟨A, hA⟩ : ∃ A : ℝ → ℝ≥0∞, A = fun s =>
      ENNReal.ofReal (3 / 2 * a * h ^ 2) * ENNReal.ofReal (((2 : ℕ) : ℝ) / (h + s) ^ (2 + 1)) :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ → ℝ≥0∞, B = fun s =>
      ENNReal.ofReal (3 / 2 * b * h ^ 2) * ENNReal.ofReal (((2 : ℕ) : ℝ) / (h + s) ^ (2 + 1)) :=
    ⟨_, rfl⟩
  have hAm : Measurable A := by
    rw [hA]
    exact measurable_const.mul (ENNReal.measurable_ofReal.comp (by fun_prop))
  have key : ∀ s : ℝ, 0 < s → ∀ c : ℝ, 0 ≤ c → μ (ball ξ s) ≤ ENNReal.ofReal (c * s) →
      G s * μ (ball ξ s) ≤
        ENNReal.ofReal (3 / 2 * c * h ^ 2) * ENNReal.ofReal (((2 : ℕ) : ℝ) / (h + s) ^ (2 + 1)) := by
    intro s hs c hc hμ
    have hp : 0 < h + s := by linarith
    refine (mul_le_mul_right hμ _).trans ?_
    rw [hG]
    dsimp only
    rw [← ENNReal.ofReal_mul (sq_nonneg h),
      ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg h) (div_nonneg (by norm_num) (pow_nonneg hp.le _))),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hc) (sq_nonneg h))]
    apply ENNReal.ofReal_le_ofReal
    have e1 : h ^ 2 * (((3 : ℕ) : ℝ) / (h + s) ^ (3 + 1)) * (c * s) =
        3 / 2 * c * h ^ 2 * (((2 : ℕ) : ℝ) / (h + s) ^ (2 + 1)) * (s / (h + s)) := by
      field_simp
      ring
    rw [e1]
    exact mul_le_of_le_one_right
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc) (sq_nonneg h))
        (div_nonneg (by norm_num) (pow_nonneg hp.le _)))
      ((div_le_one hp).mpr (by linarith))
  have hpt : ∀ s : ℝ, G s * μ (ball ξ s) ≤ (Ioi 0).indicator A s + (Ici δ).indicator B s := by
    intro s
    rcases le_or_gt s 0 with hs | hs
    · rw [ball_eq_empty.mpr hs, measure_empty, mul_zero]
      exact zero_le
    rcases lt_or_ge s δ with hsδ | hsδ
    · rw [Set.indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs), hA]
      exact (key s hs a ha (hsmall s hs hsδ)).trans le_self_add
    · rw [Set.indicator_of_mem (show s ∈ Ici δ from hsδ), hB]
      exact (key s hs b hb (hall s hs)).trans le_add_self
  have hAi : ∫⁻ s in Ioi 0, A s = ENNReal.ofReal (3 / 2 * a) := by
    simp only [hA]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, s02_vc_tail hh le_rfl (by norm_num : 1 ≤ 2),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) ha) (sq_nonneg h))]
    congr 1
    rw [add_zero]
    field_simp
  have hBi : ∫⁻ s in Ici δ, B s = ENNReal.ofReal (3 / 2 * b * h ^ 2 * (1 / (h + δ) ^ 2)) := by
    rw [setLIntegral_congr Ioi_ae_eq_Ici.symm]
    simp only [hB]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, s02_vc_tail hh hδ.le (by norm_num : 1 ≤ 2),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hb) (sq_nonneg h))]
  calc ∫⁻ z, ENNReal.ofReal (h ^ 2 / (h + ‖z - ξ‖) ^ 3) ∂μ
      = ∫⁻ z, (∫⁻ s, (Ioi ‖z - ξ‖).indicator G s) ∂μ := lintegral_congr fun z => hrep z
    _ = ∫⁻ s, ∫⁻ z, (Ioi ‖z - ξ‖).indicator G s ∂μ := lintegral_lintegral_swap hFm.aemeasurable
    _ = ∫⁻ s, G s * μ (ball ξ s) := by
        refine lintegral_congr fun s => ?_
        have e : (fun z : ℂ => (Ioi ‖z - ξ‖).indicator G s) =
            (ball ξ s).indicator (fun _ => G s) := by
          funext z
          by_cases hz : ‖z - ξ‖ < s
          · rw [Set.indicator_of_mem (show s ∈ Ioi ‖z - ξ‖ from hz),
              Set.indicator_of_mem (show z ∈ ball ξ s by rwa [mem_ball, dist_eq_norm])]
          · rw [Set.indicator_of_notMem (show s ∉ Ioi ‖z - ξ‖ from hz),
              Set.indicator_of_notMem (show z ∉ ball ξ s by rwa [mem_ball, dist_eq_norm])]
        rw [e, lintegral_indicator_const measurableSet_ball]
    _ ≤ ∫⁻ s, ((Ioi 0).indicator A s + (Ici δ).indicator B s) := lintegral_mono hpt
    _ = (∫⁻ s in Ioi 0, A s) + ∫⁻ s in Ici δ, B s := by
        rw [lintegral_add_left (hAm.indicator measurableSet_Ioi),
          lintegral_indicator measurableSet_Ioi, lintegral_indicator measurableSet_Ici]
    _ ≤ ENNReal.ofReal (3 / 2 * a + 3 / 2 * b * h ^ 2 / δ ^ 2) := by
        have hbh : 0 ≤ 3 / 2 * b * h ^ 2 := mul_nonneg (mul_nonneg (by norm_num) hb) (sq_nonneg h)
        rw [hAi, hBi, ← ENNReal.ofReal_add (mul_nonneg (by norm_num) ha)
          (mul_nonneg hbh (div_nonneg zero_le_one (pow_nonneg (by linarith) _)))]
        apply ENNReal.ofReal_le_ofReal
        have : 3 / 2 * b * h ^ 2 * (1 / (h + δ) ^ 2) ≤ 3 / 2 * b * h ^ 2 / δ ^ 2 := by
          rw [mul_one_div]
          exact div_le_div_of_nonneg_left hbh (by positivity)
            (pow_le_pow_left₀ hδ.le (by linarith) 2)
        linarith

/-- W-AZ1 (AZ (4), via Cui): for a global `K`-q.c. `F`, conformal on `𝔻`, with `∂̄F = ν ∂F` a.e. and
`|ν| ≤ k < 1` a.e., `|S_F(z)|²(1−|z|²)³ ≤ 576/(π(1−k²)) ∫_{𝔻ᶜ} (1−|z|²)|ν(w)|²/|w−z|⁴ dA(w)` on `𝔻`
(`TakhtajanTeo.CUI.cui_pointwise_gen` with `f = id`, `Ω = 𝔻`, and `schwarzian_of_analyticAt`). -/
theorem s07b_az1_pointwise {F ν : ℂ → ℂ} {K k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hF : IsKQC F univ K) (hFD : DifferentiableOn ℂ F unitDisc)
    (hν : ∀ᵐ w, dzbar F w = ν w * dz F w) (hνk : ∀ᵐ w, ‖ν w‖ ≤ k) {z : ℂ} (hz : z ∈ unitDisc) :
    ENNReal.ofReal (‖schwarzian F z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) ≤
      ENNReal.ofReal (576 / (π * (1 - k ^ 2))) *
        ∫⁻ w in unitDiscᶜ, ENNReal.ofReal ((1 - ‖z‖ ^ 2) * (‖ν w‖ ^ 2 / ‖w - z‖ ^ 4)) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hzq : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hUo : IsOpen unitDisc := isOpen_ball
  have hcui := TakhtajanTeo.CUI.cui_pointwise_gen (Ω := unitDisc) (f := id) hk0 hk1 hF hUo hFD
    differentiableOn_id (injOn_id _) (by rw [image_id]) hν hνk hz
  simp only [id_eq, deriv_id, norm_one, mul_one] at hcui
  rw [← schwarzian_of_analyticAt (hFD.analyticAt (hUo.mem_nhds hz))] at hcui
  have hR : ∫⁻ w in unitDiscᶜ, ENNReal.ofReal ((1 - ‖z‖ ^ 2) * (‖ν w‖ ^ 2 / ‖w - z‖ ^ 4)) =
      ENNReal.ofReal (1 - ‖z‖ ^ 2) *
        ∫⁻ w in unitDiscᶜ, ENNReal.ofReal (‖ν w‖ ^ 2 / ‖w - z‖ ^ 4) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun w => ENNReal.ofReal_mul hzq
  rw [hR, mul_left_comm]
  calc ENNReal.ofReal (‖schwarzian F z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3)
      = ENNReal.ofReal (1 - ‖z‖ ^ 2) *
          ENNReal.ofReal (‖schwarzian F z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 2) := by
        rw [← ENNReal.ofReal_mul hzq]
        congr 1
        ring
    _ ≤ _ := by gcongr

/-- W-AZ1 kernel bounds (AZ (5), the `z`-integrals): for `|w| > 1`,
`∫_𝔻 (1−|z|²)/|w−z|⁴ ≤ A/(|w|−1)`; and for `ζ ∈ ∂𝔻`, `r > 0`, `|w−ζ| ≥ 2r`,
`∫_{𝔻∩D(ζ,r)} (1−|z|²)/|w−z|⁴ ≤ A r³/|w−ζ|⁴`. -/
theorem s07b_az1_kernel : ∃ A : ℝ, 0 < A ∧
    (∀ w : ℂ, 1 < ‖w‖ →
      ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) / ‖w - z‖ ^ 4) ≤
        ENNReal.ofReal (A / (‖w‖ - 1))) ∧
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → ∀ w : ℂ, 2 * r ≤ ‖w - ζ‖ →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal ((1 - ‖z‖ ^ 2) / ‖w - z‖ ^ 4) ≤
        ENNReal.ofReal (A * r ^ 3 / ‖w - ζ‖ ^ 4)) := by
  refine ⟨32 * π, by positivity, fun w hw => ?_, fun ζ hζ r hr w hw => ?_⟩
  · set l := ‖w‖ - 1 with hl
    have hl0 : 0 < l := by linarith
    have hsub : unitDisc ⊆ {z : ℂ | l < ‖z - w‖} := fun z hz => by
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      have h := norm_sub_norm_le w z
      rw [norm_sub_rev] at h
      show l < ‖z - w‖
      linarith
    have hpt : ∀ z ∈ unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) / ‖w - z‖ ^ 4) ≤
        2 * ‖z - w‖ₑ ^ (-(3 : ℝ)) := by
      intro z hz
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      have hd : l < ‖z - w‖ := hsub hz
      have hd0 : 0 < ‖z - w‖ := hl0.trans hd
      have h := norm_sub_norm_le w z
      rw [norm_sub_rev] at h
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_pos hd0, ← ENNReal.ofReal_ofNat 2,
        ← ENNReal.ofReal_mul (by norm_num)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_sub_rev w z, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hd0.le,
        Real.rpow_natCast]
      have h1 : 1 - ‖z‖ ^ 2 ≤ 2 * ‖z - w‖ := by nlinarith [norm_nonneg z]
      have e : 2 * (‖z - w‖ ^ 3)⁻¹ * ‖z - w‖ ^ 4 = 2 * ‖z - w‖ := by
        field_simp
      rw [div_le_iff₀ (by positivity), e]
      exact h1
    have hm : MeasurableSet (unitDisc : Set ℂ) := measurableSet_ball
    calc ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) / ‖w - z‖ ^ 4)
        ≤ ∫⁻ z in {z : ℂ | l < ‖z - w‖}, 2 * ‖z - w‖ₑ ^ (-(3 : ℝ)) :=
          (setLIntegral_mono' hm hpt).trans (lintegral_mono_set hsub)
      _ = 2 * (ENNReal.ofReal (2 * π) * ENNReal.ofReal (-l ^ ((2 : ℝ) - 3) / (2 - 3))) := by
          rw [lintegral_const_mul' _ _ (by norm_num),
            lintegral_compl_ball_sub_enorm_rpow_neg (by norm_num) hl0 w]
      _ ≤ ENNReal.ofReal (32 * π / l) := by
          have e : -l ^ ((2 : ℝ) - 3) / (2 - 3) = l⁻¹ := by
            norm_num [Real.rpow_neg_one]
          rw [e, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have := mul_pos Real.pi_pos (inv_pos.mpr hl0)
          rw [div_eq_mul_inv]
          nlinarith
  · have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
    set d := ‖w - ζ‖ with hd
    have hd0 : 0 < d := by linarith
    have hpt : ∀ z ∈ unitDisc ∩ ball ζ r, ENNReal.ofReal ((1 - ‖z‖ ^ 2) / ‖w - z‖ ^ 4) ≤
        ENNReal.ofReal (32 * r / d ^ 4) := by
      intro z hz
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz.1
      have hzr : ‖z - ζ‖ < r := mem_ball_iff_norm.mp hz.2
      have h1 := norm_sub_norm_le ζ z
      rw [hζ1, norm_sub_rev] at h1
      have h2 : 1 - ‖z‖ ^ 2 ≤ 2 * r := by nlinarith [norm_nonneg z]
      have h20 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      have h3 : d / 2 ≤ ‖w - z‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub w z ζ
        linarith
      have h4 : (d / 2) ^ 4 ≤ ‖w - z‖ ^ 4 := pow_le_pow_left₀ (by positivity) h3 4
      refine ENNReal.ofReal_le_ofReal ?_
      have hwz : 0 < ‖w - z‖ := lt_of_lt_of_le (by positivity) h3
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ d ^ 4),
        mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 32 * r)]
    have hm : MeasurableSet (unitDisc ∩ ball ζ r) := measurableSet_ball.inter measurableSet_ball
    have hpi : ((NNReal.pi : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal π := by
      rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
    calc ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal ((1 - ‖z‖ ^ 2) / ‖w - z‖ ^ 4)
        ≤ ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (32 * r / d ^ 4) := setLIntegral_mono' hm hpt
      _ = ENNReal.ofReal (32 * r / d ^ 4) * volume (unitDisc ∩ ball ζ r) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (32 * r / d ^ 4) * volume (ball ζ r) := by
          gcongr
          exact inter_subset_right
      _ = ENNReal.ofReal (32 * π * r ^ 3 / d ^ 4) := by
          rw [Complex.volume_ball, hpi, ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring

/-- W-AZ1 box estimate (AZ (5)), one box at a time, with a Carleson bound `M` for boxes `s < 2` and a
smaller bound `ε` for boxes `s < η` at the same `ζ`: for `0 < r < η/2`,
`∫_{𝔻∩D(ζ,r)} ∫_{𝔻ᶜ} (1−|z|²)|ν(w)|²/|w−z|⁴ ≤ A (ε + M r²/η² + r²) r`
(uniform case: `ε = M`, `η = 2`; vanishing case: `ε` small, then `r` small). -/
theorem s07b_az1_box : ∃ A : ℝ, 0 < A ∧ ∀ {ν : ℂ → ℂ}, Measurable ν → (∀ᵐ w, ‖ν w‖ ≤ 1) →
    ∀ {M ε η : ℝ}, 0 ≤ M → 0 ≤ ε → 0 < η → η ≤ 2 → ∀ ζ ∈ sphere (0 : ℂ) 1,
      (∀ s : ℝ, 0 < s → s < 2 →
        ∫⁻ w in unitDiscExterior ∩ ball ζ s, ENNReal.ofReal (‖ν w‖ ^ 2 / (‖w‖ ^ 2 - 1)) ≤
          ENNReal.ofReal (M * s)) →
      (∀ s : ℝ, 0 < s → s < η →
        ∫⁻ w in unitDiscExterior ∩ ball ζ s, ENNReal.ofReal (‖ν w‖ ^ 2 / (‖w‖ ^ 2 - 1)) ≤
          ENNReal.ofReal (ε * s)) →
      ∀ r : ℝ, 0 < r → r < η / 2 →
        ∫⁻ z in unitDisc ∩ ball ζ r, ∫⁻ w in unitDiscᶜ,
            ENNReal.ofReal ((1 - ‖z‖ ^ 2) * (‖ν w‖ ^ 2 / ‖w - z‖ ^ 4)) ≤
          ENNReal.ofReal (A * (ε + M * r ^ 2 / η ^ 2 + r ^ 2) * r) := by
  obtain ⟨A₀, hA₀, hKa, hKb⟩ := s07b_az1_kernel
  refine ⟨30 * A₀, by positivity, ?_⟩
  intro ν hνm hν1 M ε η hM hε hη0 hη2 ζ hζ hbM hbε r hr0 hrη
  have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
  have hr2 : 2 * r < η := by linarith
  have hEm : MeasurableSet unitDiscExterior :=
    show MeasurableSet {z : ℂ | 1 < ‖z‖} from measurableSet_lt measurable_const measurable_norm
  obtain ⟨K, hK⟩ : ∃ K : ℂ → ℝ≥0∞, K = fun w =>
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal ((1 - ‖z‖ ^ 2) / ‖w - z‖ ^ 4) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℂ → ℝ, D = fun w => ‖ν w‖ ^ 2 / (‖w‖ ^ 2 - 1) := ⟨_, rfl⟩
  have hDm : Measurable fun w => ENNReal.ofReal (D w) := by
    rw [hD]
    fun_prop
  -- Tonelli: `∫_Q ∫_{𝔻ᶜ} = ∫_{𝔻ᶜ} |ν|² K`
  have hstep1 : ∫⁻ z in unitDisc ∩ ball ζ r, ∫⁻ w in unitDiscᶜ,
      ENNReal.ofReal ((1 - ‖z‖ ^ 2) * (‖ν w‖ ^ 2 / ‖w - z‖ ^ 4)) =
        ∫⁻ w in unitDiscᶜ, ENNReal.ofReal (‖ν w‖ ^ 2) * K w := by
    have e : ∀ z w : ℂ, ENNReal.ofReal ((1 - ‖z‖ ^ 2) * (‖ν w‖ ^ 2 / ‖w - z‖ ^ 4)) =
        ENNReal.ofReal (‖ν w‖ ^ 2) * ENNReal.ofReal ((1 - ‖z‖ ^ 2) / ‖w - z‖ ^ 4) := by
      intro z w
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      ring
    simp_rw [e]
    have hm : Measurable fun p : ℂ × ℂ =>
        ENNReal.ofReal (‖ν p.2‖ ^ 2) * ENNReal.ofReal ((1 - ‖p.1‖ ^ 2) / ‖p.2 - p.1‖ ^ 4) := by
      fun_prop
    rw [lintegral_lintegral_swap hm.aemeasurable]
    refine lintegral_congr fun w => ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hK]
  -- `𝔻ᶜ = 𝔻*` up to the null circle
  have hae : (unitDiscᶜ : Set ℂ) =ᵐ[volume] unitDiscExterior := by
    refine ae_eq_set.mpr ⟨measure_mono_null (fun w hw => ?_)
      (Measure.addHaar_sphere (μ := volume) (0 : ℂ) 1), measure_mono_null (fun w hw => ?_) measure_empty⟩
    · have h1 : ¬ ‖w‖ < 1 := fun h => hw.1 (mem_ball_zero_iff.mpr h)
      have h2 : ¬ 1 < ‖w‖ := hw.2
      exact mem_sphere_zero_iff_norm.mpr (le_antisymm (not_lt.mp h2) (not_lt.mp h1))
    · exact absurd (show (1 : ℝ) < ‖w‖ from hw.1)
        (not_lt.mpr (mem_ball_zero_iff.mp (not_not.mp hw.2)).le)
  -- near part `𝔻* ∩ D(ζ, 2r)`
  have hnear : ∫⁻ w in unitDiscExterior ∩ ball ζ (2 * r), ENNReal.ofReal (‖ν w‖ ^ 2) * K w ≤
      ENNReal.ofReal (4 * A₀ * (ε * (2 * r))) := by
    have hNm : MeasurableSet (unitDiscExterior ∩ ball ζ (2 * r)) := hEm.inter measurableSet_ball
    calc ∫⁻ w in unitDiscExterior ∩ ball ζ (2 * r), ENNReal.ofReal (‖ν w‖ ^ 2) * K w
        ≤ ∫⁻ w in unitDiscExterior ∩ ball ζ (2 * r),
            ENNReal.ofReal (4 * A₀) * ENNReal.ofReal (‖ν w‖ ^ 2 / (‖w‖ ^ 2 - 1)) := by
          refine setLIntegral_mono' hNm fun w hw => ?_
          have hw1 : 1 < ‖w‖ := hw.1
          have hwr : ‖w - ζ‖ < 2 * r := mem_ball_iff_norm.mp hw.2
          have h := norm_sub_norm_le w ζ
          have hw3 : ‖w‖ < 3 := by linarith
          have hKw : K w ≤ ENNReal.ofReal (A₀ / (‖w‖ - 1)) := by
            simp only [hK]
            exact (lintegral_mono_set inter_subset_left).trans (hKa w hw1)
          refine (mul_le_mul' le_rfl hKw).trans ?_
          rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have ht1 : ‖w‖ - 1 ≠ 0 := by linarith
          have ht2 : ‖w‖ ^ 2 - 1 ≠ 0 := by nlinarith
          have e : ‖ν w‖ ^ 2 * (A₀ / (‖w‖ - 1)) =
              A₀ * (‖w‖ + 1) * (‖ν w‖ ^ 2 / (‖w‖ ^ 2 - 1)) := by
            field_simp
            ring
          rw [e]
          exact mul_le_mul_of_nonneg_right (by nlinarith)
            (div_nonneg (sq_nonneg _) (by nlinarith))
      _ = ENNReal.ofReal (4 * A₀) *
            ∫⁻ w in unitDiscExterior ∩ ball ζ (2 * r), ENNReal.ofReal (‖ν w‖ ^ 2 / (‖w‖ ^ 2 - 1)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (4 * A₀) * ENNReal.ofReal (ε * (2 * r)) := by
          gcongr
          exact hbε (2 * r) (by positivity) hr2
      _ = ENNReal.ofReal (4 * A₀ * (ε * (2 * r))) := (ENNReal.ofReal_mul (by positivity)).symm
  -- far part `|w − ζ| ≥ 1` (`|ν| ≤ 1`)
  have hfar : ∫⁻ w in (unitDiscExterior \ ball ζ (2 * r)) \ ball ζ 1,
      ENNReal.ofReal (‖ν w‖ ^ 2) * K w ≤ ENNReal.ofReal (A₀ * r ^ 3 * (2 * π * 2)) := by
    have hGm : MeasurableSet ((unitDiscExterior \ ball ζ (2 * r)) \ ball ζ 1) :=
      (hEm.diff measurableSet_ball).diff measurableSet_ball
    calc ∫⁻ w in (unitDiscExterior \ ball ζ (2 * r)) \ ball ζ 1, ENNReal.ofReal (‖ν w‖ ^ 2) * K w
        ≤ ∫⁻ w in (unitDiscExterior \ ball ζ (2 * r)) \ ball ζ 1,
            ENNReal.ofReal (A₀ * r ^ 3) * ‖w - ζ‖ₑ ^ (-(4 : ℝ)) := by
          refine setLIntegral_mono_ae' hGm ?_
          filter_upwards [hν1] with w hw1 hw
          have hd : 1 ≤ ‖w - ζ‖ := by
            have := hw.2
            rw [mem_ball, dist_eq_norm, not_lt] at this
            exact this
          have h2r : 2 * r ≤ ‖w - ζ‖ := by
            have := hw.1.2
            rw [mem_ball, dist_eq_norm, not_lt] at this
            exact this
          have hd0 : 0 < ‖w - ζ‖ := by linarith
          have hνw : ENNReal.ofReal (‖ν w‖ ^ 2) ≤ 1 :=
            ENNReal.ofReal_le_one.mpr (by nlinarith [norm_nonneg (ν w)])
          have hKw : K w ≤ ENNReal.ofReal (A₀ * r ^ 3 / ‖w - ζ‖ ^ 4) := by
            simp only [hK]
            exact hKb ζ hζ r hr0 w h2r
          refine (mul_le_mul' hνw hKw).trans (le_of_eq ?_)
          rw [one_mul, ← ofReal_norm, ENNReal.ofReal_rpow_of_pos hd0,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hd0.le, Real.rpow_natCast]
          ring
      _ ≤ ∫⁻ w in {w : ℂ | 1 / 2 < ‖w - ζ‖}, ENNReal.ofReal (A₀ * r ^ 3) * ‖w - ζ‖ₑ ^ (-(4 : ℝ)) := by
          refine lintegral_mono_set fun w hw => ?_
          have := hw.2
          rw [mem_ball, dist_eq_norm, not_lt] at this
          show 1 / 2 < ‖w - ζ‖
          linarith
      _ = ENNReal.ofReal (A₀ * r ^ 3) *
            (ENNReal.ofReal (2 * π) * ENNReal.ofReal (-(1 / 2 : ℝ) ^ ((2 : ℝ) - 4) / (2 - 4))) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_compl_ball_sub_enorm_rpow_neg (by norm_num) (by norm_num) ζ]
      _ = ENNReal.ofReal (A₀ * r ^ 3 * (2 * π * 2)) := by
          have e : -(1 / 2 : ℝ) ^ ((2 : ℝ) - 4) / (2 - 4) = 2 := by
            rw [show (2 : ℝ) - 4 = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num),
              Real.rpow_natCast]
            norm_num
          rw [e, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  -- middle part `2r ≤ |w − ζ| < 1`: layer cake against `D dA` on `𝔻* ∩ D(ζ, 1)`
  have hmid : ∫⁻ w in (unitDiscExterior \ ball ζ (2 * r)) ∩ ball ζ 1,
      ENNReal.ofReal (‖ν w‖ ^ 2) * K w ≤
        ENNReal.ofReal (27 / 2 * A₀ * r) *
          ENNReal.ofReal (3 / 2 * ε + 3 / 2 * M * r ^ 2 / η ^ 2) := by
    have hGm : MeasurableSet ((unitDiscExterior \ ball ζ (2 * r)) ∩ ball ζ 1) :=
      (hEm.diff measurableSet_ball).inter measurableSet_ball
    have hkm : Measurable fun w : ℂ => ENNReal.ofReal (r ^ 2 / (r + ‖w - ζ‖) ^ 3) := by
      fun_prop
    set μ' : Measure ℂ := (volume.restrict (unitDiscExterior ∩ ball ζ 1)).withDensity
      fun w => ENNReal.ofReal (D w) with hμ'
    have hμb : ∀ s : ℝ, μ' (ball ζ s) =
        ∫⁻ w in ball ζ s ∩ (unitDiscExterior ∩ ball ζ 1), ENNReal.ofReal (D w) := by
      intro s
      rw [hμ', withDensity_apply _ measurableSet_ball, Measure.restrict_restrict measurableSet_ball]
    have hsub : ∀ s : ℝ, ball ζ s ∩ (unitDiscExterior ∩ ball ζ 1) ⊆ unitDiscExterior ∩ ball ζ s :=
      fun s w hw => ⟨hw.2.1, hw.1⟩
    have hsub1 : ∀ s : ℝ, ball ζ s ∩ (unitDiscExterior ∩ ball ζ 1) ⊆ unitDiscExterior ∩ ball ζ 1 :=
      fun s w hw => hw.2
    have hall : ∀ s : ℝ, 0 < s → μ' (ball ζ s) ≤ ENNReal.ofReal (M * s) := by
      intro s hs
      rw [hμb, hD]
      rcases lt_or_ge s 1 with h1 | h1
      · exact (lintegral_mono_set (hsub s)).trans (hbM s hs (by linarith))
      · refine (lintegral_mono_set (hsub1 s)).trans ((hbM 1 one_pos (by norm_num)).trans ?_)
        exact ENNReal.ofReal_le_ofReal (by nlinarith)
    have hsmall : ∀ s : ℝ, 0 < s → s < η → μ' (ball ζ s) ≤ ENNReal.ofReal (ε * s) := by
      intro s hs hsη
      rw [hμb, hD]
      exact (lintegral_mono_set (hsub s)).trans (hbε s hs hsη)
    have hlay := s07b_az1_layer (μ := μ') (ξ := ζ) hr0 hη0 hε hM hsmall hall
    calc ∫⁻ w in (unitDiscExterior \ ball ζ (2 * r)) ∩ ball ζ 1, ENNReal.ofReal (‖ν w‖ ^ 2) * K w
        ≤ ∫⁻ w in (unitDiscExterior \ ball ζ (2 * r)) ∩ ball ζ 1, ENNReal.ofReal (27 / 2 * A₀ * r) *
            (ENNReal.ofReal (D w) * ENNReal.ofReal (r ^ 2 / (r + ‖w - ζ‖) ^ 3)) := by
          refine setLIntegral_mono' hGm fun w hw => ?_
          have hw1 : 1 < ‖w‖ := hw.1.1
          have h2r : 2 * r ≤ ‖w - ζ‖ := by
            have := hw.1.2
            rw [mem_ball, dist_eq_norm, not_lt] at this
            exact this
          have hd1 : ‖w - ζ‖ < 1 := mem_ball_iff_norm.mp hw.2
          have hd0 : 0 < ‖w - ζ‖ := by linarith
          have h := norm_sub_norm_le w ζ
          rw [hζ1] at h
          have hKw : K w ≤ ENNReal.ofReal (A₀ * r ^ 3 / ‖w - ζ‖ ^ 4) := by
            simp only [hK]
            exact hKb ζ hζ r hr0 w h2r
          refine (mul_le_mul' le_rfl hKw).trans ?_
          have hD0 : 0 ≤ D w := by
            rw [hD]
            exact div_nonneg (sq_nonneg _) (by nlinarith)
          rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul hD0,
            ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have ht2 : ‖w‖ ^ 2 - 1 ≠ 0 := by nlinarith
          have hn : ‖ν w‖ ^ 2 = (‖w‖ ^ 2 - 1) * D w := by
            rw [hD]
            field_simp
          have h1 : ‖w‖ ^ 2 - 1 ≤ 4 * ‖w - ζ‖ := by nlinarith
          have h3 : (r + ‖w - ζ‖) ^ 3 ≤ 27 / 8 * ‖w - ζ‖ ^ 3 := by
            have : r + ‖w - ζ‖ ≤ 3 / 2 * ‖w - ζ‖ := by linarith
            calc (r + ‖w - ζ‖) ^ 3 ≤ (3 / 2 * ‖w - ζ‖) ^ 3 :=
                  pow_le_pow_left₀ (by positivity) this 3
              _ = 27 / 8 * ‖w - ζ‖ ^ 3 := by ring
          rw [hn]
          calc (‖w‖ ^ 2 - 1) * D w * (A₀ * r ^ 3 / ‖w - ζ‖ ^ 4)
              ≤ 4 * ‖w - ζ‖ * D w * (A₀ * r ^ 3 / ‖w - ζ‖ ^ 4) := by
                gcongr
            _ = (27 / 2 * A₀ * D w * r ^ 3) / (27 / 8 * ‖w - ζ‖ ^ 3) := by
                field_simp
                ring
            _ ≤ (27 / 2 * A₀ * D w * r ^ 3) / (r + ‖w - ζ‖) ^ 3 :=
                div_le_div_of_nonneg_left (by positivity) (by positivity) h3
            _ = 27 / 2 * A₀ * r * (D w * (r ^ 2 / (r + ‖w - ζ‖) ^ 3)) := by
                field_simp
      _ = ENNReal.ofReal (27 / 2 * A₀ * r) *
            ∫⁻ w in (unitDiscExterior \ ball ζ (2 * r)) ∩ ball ζ 1,
              ENNReal.ofReal (D w) * ENNReal.ofReal (r ^ 2 / (r + ‖w - ζ‖) ^ 3) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (27 / 2 * A₀ * r) *
            ∫⁻ w in unitDiscExterior ∩ ball ζ 1,
              ENNReal.ofReal (D w) * ENNReal.ofReal (r ^ 2 / (r + ‖w - ζ‖) ^ 3) := by
          exact mul_le_mul' le_rfl (lintegral_mono_set (fun w hw => ⟨hw.1.1, hw.2⟩))
      _ = ENNReal.ofReal (27 / 2 * A₀ * r) * ∫⁻ w, ENNReal.ofReal (r ^ 2 / (r + ‖w - ζ‖) ^ 3) ∂μ' := by
          rw [hμ', lintegral_withDensity_eq_lintegral_mul _ hDm hkm]
          rfl
      _ ≤ _ := by gcongr
  -- assembly
  have hcover : unitDiscExterior ⊆ ((unitDiscExterior ∩ ball ζ (2 * r)) ∪
      ((unitDiscExterior \ ball ζ (2 * r)) ∩ ball ζ 1)) ∪
        ((unitDiscExterior \ ball ζ (2 * r)) \ ball ζ 1) := by
    intro w hw
    by_cases h1 : w ∈ ball ζ (2 * r)
    · exact Or.inl (Or.inl ⟨hw, h1⟩)
    · by_cases h2 : w ∈ ball ζ 1
      · exact Or.inl (Or.inr ⟨⟨hw, h1⟩, h2⟩)
      · exact Or.inr ⟨⟨hw, h1⟩, h2⟩
  rw [hstep1, setLIntegral_congr hae]
  refine (lintegral_mono_set hcover).trans ?_
  refine (lintegral_union_le _ _ _).trans ?_
  refine (add_le_add (lintegral_union_le _ _ _) le_rfl).trans ?_
  refine (add_le_add (add_le_add hnear hmid) hfar).trans ?_
  have hX : 0 ≤ M * r ^ 2 / η ^ 2 := by positivity
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hπ := Real.pi_le_four
  have e : 3 / 2 * M * r ^ 2 / η ^ 2 = 3 / 2 * (M * r ^ 2 / η ^ 2) := by ring
  rw [e]
  nlinarith [mul_nonneg (mul_nonneg hA₀.le hr0.le) hε, mul_nonneg (mul_nonneg hA₀.le hr0.le) hX,
    mul_nonneg (mul_nonneg hA₀.le hr0.le) (mul_nonneg (sq_nonneg r) (by linarith : (0 : ℝ) ≤ 30 - 4 * π))]

/-- W-AZ1 helper: a coefficient `ν` with `∂̄F = ν ∂F` a.e. agrees a.e. with the (measurable) complex
dilatation of the `K`-q.c. map `F`, since `∂F ≠ 0` a.e. (`thm9_6_cor2_jacobian_pos`). -/
theorem s07b_az1_ae {F ν : ℂ → ℂ} {K : ℝ} (hF : IsKQC F univ K)
    (hν : ∀ᵐ w, dzbar F w = ν w * dz F w) : ∀ᵐ w, ν w = LiZhongQC.complexDilatation F w := by
  have hJ := thm9_6_cor2_jacobian_pos hF
  rw [Measure.restrict_univ] at hJ
  filter_upwards [hJ, hν] with w hw h
  have hjac : jacobian F w = ‖dz F w‖ ^ 2 - ‖dzbar F w‖ ^ 2 := rfl
  have hp : dz F w ≠ 0 := by
    intro h0
    rw [hjac, h0, norm_zero] at hw
    nlinarith [norm_nonneg (dzbar F w)]
  show ν w = dzbar F w / dz F w
  rw [h, mul_div_cancel_right₀ _ hp]

/-- W-AZ1 helper: replace `ν` by the measurable `complexDilatation F` (a.e. equal, `s07b_az1_ae`). -/
theorem s07b_az1_prep {F ν : ℂ → ℂ} {K k : ℝ} (hF : IsKQC F univ K)
    (hν : ∀ᵐ w, dzbar F w = ν w * dz F w) (hνk : ∀ᵐ w, ‖ν w‖ ≤ k) :
    ∃ ν' : ℂ → ℂ, Measurable ν' ∧ (∀ᵐ w, ν w = ν' w) ∧ (∀ᵐ w, dzbar F w = ν' w * dz F w) ∧
      ∀ᵐ w, ‖ν' w‖ ≤ k := by
  have hνν' := s07b_az1_ae hF hν
  refine ⟨LiZhongQC.complexDilatation F, (measurable_dzbar F).div (measurable_dz F), hνν', ?_, ?_⟩
  · filter_upwards [hν, hνν'] with w h1 h2
    rw [← h2]
    exact h1
  · filter_upwards [hνk, hνν'] with w h1 h2
    rw [← h2]
    exact h1

/-- W-AZ1 helper: on a measurable `S ⊆ 𝔻`, the Schwarzian Carleson measure is bounded by the integrated
pointwise bound `s07b_az1_pointwise`. -/
theorem s07b_az1_smeas {F ν : ℂ → ℂ} {K k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hF : IsKQC F univ K) (hFD : DifferentiableOn ℂ F unitDisc)
    (hν : ∀ᵐ w, dzbar F w = ν w * dz F w) (hνk : ∀ᵐ w, ‖ν w‖ ≤ k) {S : Set ℂ} (hS : MeasurableSet S)
    (hSD : S ⊆ unitDisc) :
    schwarzCarlesonMeasure F S ≤ ENNReal.ofReal (576 / (π * (1 - k ^ 2))) *
      ∫⁻ z in S, ∫⁻ w in unitDiscᶜ, ENNReal.ofReal ((1 - ‖z‖ ^ 2) * (‖ν w‖ ^ 2 / ‖w - z‖ ^ 4)) := by
  have e : schwarzCarlesonMeasure F S =
      ∫⁻ z in S, ENNReal.ofReal (‖schwarzian F z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) := by
    unfold schwarzCarlesonMeasure
    rw [withDensity_apply _ hS, Measure.restrict_restrict hS, inter_eq_left.mpr hSD]
  rw [e, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact setLIntegral_mono' hS fun z hz => s07b_az1_pointwise hk0 hk1 hF hFD hν hνk (hSD hz)

/-- W-AZ1 helper (covering): `𝔻` is covered by `D(0, 3/5)` and the four boxes `𝔻 ∩ D(±1, 9/10)`,
`𝔻 ∩ D(±i, 9/10)`. -/
theorem s07b_az1_cover : unitDisc ⊆ ball (0 : ℂ) (3 / 5) ∪
    ((unitDisc ∩ ball 1 (9 / 10) ∪ unitDisc ∩ ball (-1) (9 / 10)) ∪
      (unitDisc ∩ ball I (9 / 10) ∪ unitDisc ∩ ball (-I) (9 / 10))) := by
  intro z hz
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  by_cases h0 : ‖z‖ < 3 / 5
  · exact Or.inl (mem_ball_zero_iff.mpr h0)
  right
  push Not at h0
  have hu : 9 / 25 ≤ z.re ^ 2 + z.im ^ 2 := by nlinarith
  have hu1 : z.re ^ 2 + z.im ^ 2 < 1 := by nlinarith [norm_nonneg z]
  have key : ∀ t s : ℝ, 0 ≤ t → s ^ 2 ≤ t ^ 2 → t ^ 2 + s ^ 2 = z.re ^ 2 + z.im ^ 2 →
      t ^ 2 + s ^ 2 - 2 * t + 1 < 81 / 100 := by
    intro t s ht hst hts
    by_contra hc
    push Not at hc
    have h2t : 2 * t ≤ (t ^ 2 + s ^ 2) + 19 / 100 := by linarith
    have hsq : (2 * t) ^ 2 ≤ ((t ^ 2 + s ^ 2) + 19 / 100) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2t 2
    rw [hts] at hsq
    nlinarith [mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hu1.le)]
  have hb : ∀ c : ℂ, ‖z - c‖ ^ 2 < 81 / 100 → z ∈ ball c (9 / 10) := by
    intro c h
    rw [mem_ball, dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by nlinarith)
  have n1 : ∀ c : ℂ, ‖z - c‖ ^ 2 = (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 := by
    intro c
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  by_cases hxy : z.im ^ 2 ≤ z.re ^ 2
  · left
    rcases le_or_gt 0 z.re with hx | hx
    · refine Or.inl ⟨hz, hb 1 ?_⟩
      rw [n1]
      have := key z.re z.im hx hxy rfl
      simp only [Complex.one_re, Complex.one_im]
      nlinarith
    · refine Or.inr ⟨hz, hb (-1) ?_⟩
      rw [n1]
      have := key (-z.re) z.im (by linarith) (by nlinarith) (by ring)
      simp only [Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im]
      nlinarith
  · right
    push Not at hxy
    rcases le_or_gt 0 z.im with hy | hy
    · refine Or.inl ⟨hz, hb I ?_⟩
      rw [n1]
      have := key z.im z.re hy hxy.le (by ring)
      simp only [Complex.I_re, Complex.I_im]
      nlinarith
    · refine Or.inr ⟨hz, hb (-I) ?_⟩
      rw [n1]
      have := key (-z.im) z.re (by linarith) (by nlinarith) (by ring)
      simp only [Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
      nlinarith

/-- W-AZ1 helper (inner disc): for `|ν| ≤ 1` a.e., the Schwarzian Carleson measure of `D(0, 3/5)` is
finite: on it `∫_{𝔻ᶜ} (1−|z|²)|ν|²/|w−z|⁴ ≤ ∫_{|w−z|>2/5} |w−z|⁻⁴ = 25π/4`. -/
theorem s07b_az1_inner {F ν : ℂ → ℂ} {K k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hF : IsKQC F univ K) (hFD : DifferentiableOn ℂ F unitDisc)
    (hν : ∀ᵐ w, dzbar F w = ν w * dz F w) (hνk : ∀ᵐ w, ‖ν w‖ ≤ k) :
    schwarzCarlesonMeasure F (ball (0 : ℂ) (3 / 5)) ≤ ENNReal.ofReal (576 / (π * (1 - k ^ 2))) *
      (ENNReal.ofReal (2 * π * (25 / 8)) * (ENNReal.ofReal (3 / 5) ^ 2 * NNReal.pi)) := by
  have hSD : ball (0 : ℂ) (3 / 5) ⊆ unitDisc := ball_subset_ball (by norm_num)
  refine (s07b_az1_smeas hk0 hk1 hF hFD hν hνk measurableSet_ball hSD).trans ?_
  gcongr
  have hpt : ∀ z ∈ ball (0 : ℂ) (3 / 5), ∫⁻ w in unitDiscᶜ,
      ENNReal.ofReal ((1 - ‖z‖ ^ 2) * (‖ν w‖ ^ 2 / ‖w - z‖ ^ 4)) ≤ ENNReal.ofReal (2 * π * (25 / 8)) := by
    intro z hz
    have hz1 : ‖z‖ < 3 / 5 := mem_ball_zero_iff.mp hz
    have hsub : (unitDiscᶜ : Set ℂ) ⊆ {w : ℂ | 2 / 5 < ‖w - z‖} := by
      intro w hw
      have hw1 : 1 ≤ ‖w‖ := not_lt.mp fun h => hw (mem_ball_zero_iff.mpr h)
      have := norm_sub_norm_le w z
      show 2 / 5 < ‖w - z‖
      linarith
    have hcm : MeasurableSet (unitDiscᶜ : Set ℂ) := measurableSet_ball.compl
    calc ∫⁻ w in unitDiscᶜ, ENNReal.ofReal ((1 - ‖z‖ ^ 2) * (‖ν w‖ ^ 2 / ‖w - z‖ ^ 4))
        ≤ ∫⁻ w in unitDiscᶜ, ‖w - z‖ₑ ^ (-(4 : ℝ)) := by
          refine setLIntegral_mono_ae' hcm ?_
          filter_upwards [hνk] with w hwk hw
          have hd : 2 / 5 < ‖w - z‖ := hsub hw
          have hd0 : 0 < ‖w - z‖ := by linarith
          rw [← ofReal_norm, ENNReal.ofReal_rpow_of_pos hd0]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hd0.le, Real.rpow_natCast]
          have hn1 : ‖ν w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (ν w)]
          have hz0 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
          have hz2 : 1 - ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
          rw [mul_div_assoc', div_le_iff₀ (by positivity), inv_mul_cancel₀ (by positivity)]
          nlinarith [sq_nonneg ‖ν w‖, mul_le_mul hz2 hn1 (sq_nonneg ‖ν w‖) zero_le_one]
      _ ≤ ∫⁻ w in {w : ℂ | 2 / 5 < ‖w - z‖}, ‖w - z‖ₑ ^ (-(4 : ℝ)) := lintegral_mono_set hsub
      _ = ENNReal.ofReal (2 * π) * ENNReal.ofReal (-(2 / 5 : ℝ) ^ ((2 : ℝ) - 4) / (2 - 4)) :=
          lintegral_compl_ball_sub_enorm_rpow_neg (by norm_num) (by norm_num) z
      _ = ENNReal.ofReal (2 * π * (25 / 8)) := by
          have e : -(2 / 5 : ℝ) ^ ((2 : ℝ) - 4) / (2 - 4) = 25 / 8 := by
            rw [show (2 : ℝ) - 4 = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num),
              Real.rpow_natCast]
            norm_num
          rw [e, ← ENNReal.ofReal_mul (by positivity)]
  calc ∫⁻ z in ball (0 : ℂ) (3 / 5), ∫⁻ w in unitDiscᶜ,
        ENNReal.ofReal ((1 - ‖z‖ ^ 2) * (‖ν w‖ ^ 2 / ‖w - z‖ ^ 4))
      ≤ ∫⁻ z in ball (0 : ℂ) (3 / 5), ENNReal.ofReal (2 * π * (25 / 8)) :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = ENNReal.ofReal (2 * π * (25 / 8)) * (ENNReal.ofReal (3 / 5) ^ 2 * NNReal.pi) := by
        rw [setLIntegral_const, Complex.volume_ball]

/-- W-AZ1 helper (core box estimate for `F`): `s07b_az1_smeas` + `s07b_az1_box`, applied to the
measurable representative `complexDilatation F` of `ν` (`s07b_az1_prep`). -/
theorem s07b_az1_core {F ν : ℂ → ℂ} {K k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hF : IsKQC F univ K) (hFD : DifferentiableOn ℂ F unitDisc)
    (hν : ∀ᵐ w, dzbar F w = ν w * dz F w) (hνk : ∀ᵐ w, ‖ν w‖ ≤ k) :
    ∃ L : ℝ, 0 < L ∧ ∀ {M ε η : ℝ}, 0 ≤ M → 0 ≤ ε → 0 < η → η ≤ 2 → ∀ ζ ∈ sphere (0 : ℂ) 1,
      (∀ s : ℝ, 0 < s → s < 2 →
        ∫⁻ w in unitDiscExterior ∩ ball ζ s, ENNReal.ofReal (‖ν w‖ ^ 2 / (‖w‖ ^ 2 - 1)) ≤
          ENNReal.ofReal (M * s)) →
      (∀ s : ℝ, 0 < s → s < η →
        ∫⁻ w in unitDiscExterior ∩ ball ζ s, ENNReal.ofReal (‖ν w‖ ^ 2 / (‖w‖ ^ 2 - 1)) ≤
          ENNReal.ofReal (ε * s)) →
      ∀ r : ℝ, 0 < r → r < η / 2 →
        schwarzCarlesonMeasure F (unitDisc ∩ ball ζ r) ≤
          ENNReal.ofReal (L * (ε + M * r ^ 2 / η ^ 2 + r ^ 2) * r) := by
  obtain ⟨A, hA, hbox⟩ := s07b_az1_box
  obtain ⟨ν', hν'm, hνν', hν', hν'k⟩ := s07b_az1_prep hF hν hνk
  have hk2 : 0 < 1 - k ^ 2 := by nlinarith
  have hc0 : 0 < 576 / (π * (1 - k ^ 2)) := div_pos (by norm_num) (mul_pos Real.pi_pos hk2)
  have hν'1 : ∀ᵐ w, ‖ν' w‖ ≤ 1 := hν'k.mono fun w h => h.trans hk1.le
  have hint : ∀ S : Set ℂ, ∫⁻ w in S, ENNReal.ofReal (‖ν w‖ ^ 2 / (‖w‖ ^ 2 - 1)) =
      ∫⁻ w in S, ENNReal.ofReal (‖ν' w‖ ^ 2 / (‖w‖ ^ 2 - 1)) := fun S =>
    lintegral_congr_ae (ae_restrict_of_ae (hνν'.mono fun w h => by simp only [h]))
  refine ⟨576 / (π * (1 - k ^ 2)) * A, mul_pos hc0 hA, ?_⟩
  intro M ε η hM hε hη hη2 ζ hζ hMb hεb r hr hrη
  have hb := hbox hν'm hν'1 hM hε hη hη2 ζ hζ (fun s hs hs2 => by rw [← hint]; exact hMb s hs hs2)
    (fun s hs hsη => by rw [← hint]; exact hεb s hs hsη) r hr hrη
  calc schwarzCarlesonMeasure F (unitDisc ∩ ball ζ r)
      ≤ ENNReal.ofReal (576 / (π * (1 - k ^ 2))) * ∫⁻ z in unitDisc ∩ ball ζ r, ∫⁻ w in unitDiscᶜ,
          ENNReal.ofReal ((1 - ‖z‖ ^ 2) * (‖ν' w‖ ^ 2 / ‖w - z‖ ^ 4)) :=
        s07b_az1_smeas hk0 hk1 hF hFD hν' hν'k (measurableSet_ball.inter measurableSet_ball)
          inter_subset_left
    _ ≤ ENNReal.ofReal (576 / (π * (1 - k ^ 2))) *
          ENNReal.ofReal (A * (ε + M * r ^ 2 / η ^ 2 + r ^ 2) * r) := mul_le_mul' le_rfl hb
    _ = ENNReal.ofReal (576 / (π * (1 - k ^ 2)) * A * (ε + M * r ^ 2 / η ^ 2 + r ^ 2) * r) := by
        rw [← ENNReal.ofReal_mul hc0.le]
        congr 1
        ring

/-- **W-AZ1, uniform** ([AZ] Thm 1, first half; (B1) ⇒ (B3)): let `F` be a global `K`-q.c. homeomorphism,
conformal on `𝔻`, with `∂̄F = ν ∂F` a.e., `|ν| ≤ k < 1` a.e., and `|ν|²/(|w|²−1) dA ∈ CM(𝔻*)`. Then
`|S_F|²(1−|z|²)³ dA ∈ CM(𝔻)`. -/
theorem s07b_az1_B3 {F ν : ℂ → ℂ} {K k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hF : IsKQC F univ K) (hFD : DifferentiableOn ℂ F unitDisc)
    (hν : ∀ᵐ w, dzbar F w = ν w * dz F w) (hνk : ∀ᵐ w, ‖ν w‖ ≤ k)
    (hC : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ w in unitDiscExterior ∩ ball ζ r, ENNReal.ofReal (‖ν w‖ ^ 2 / (‖w‖ ^ 2 - 1)) ≤
        C * ENNReal.ofReal r) :
    IsCarlesonDisk (schwarzCarlesonMeasure F) := by
  obtain ⟨L, hL, hcore⟩ := s07b_az1_core hk0 hk1 hF hFD hν hνk
  obtain ⟨C, hCtop, hCb⟩ := hC
  have hM : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  have hMb : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ s : ℝ, 0 < s → s < 2 →
      ∫⁻ w in unitDiscExterior ∩ ball ζ s, ENNReal.ofReal (‖ν w‖ ^ 2 / (‖w‖ ^ 2 - 1)) ≤
        ENNReal.ofReal (C.toReal * s) := by
    intro ζ hζ s hs hs2
    refine (hCb ζ hζ s hs hs2).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCtop]
  obtain ⟨B9, hB9⟩ : ∃ B : ℝ≥0∞, B = ENNReal.ofReal (L * (2 * C.toReal + 1)) := ⟨_, rfl⟩
  have hsmall : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 1 →
      schwarzCarlesonMeasure F (unitDisc ∩ ball ζ r) ≤ B9 * ENNReal.ofReal r := by
    intro ζ hζ r hr hr1
    refine (hcore hM hM (by norm_num) le_rfl ζ hζ (hMb ζ hζ) (hMb ζ hζ) r hr (by linarith)).trans ?_
    rw [hB9, ← ENNReal.ofReal_mul (mul_nonneg hL.le (by linarith))]
    refine ENNReal.ofReal_le_ofReal ?_
    have hr2 : r ^ 2 ≤ 1 := by nlinarith
    have hX : C.toReal + C.toReal * r ^ 2 / 2 ^ 2 + r ^ 2 ≤ 2 * C.toReal + 1 := by
      nlinarith [mul_le_of_le_one_right hM hr2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX hL.le) hr.le
  have hbox9 : ∀ p : ℂ, ‖p‖ = 1 →
      schwarzCarlesonMeasure F (unitDisc ∩ ball p (9 / 10)) ≤ B9 := by
    intro p hp
    refine (hsmall p (mem_sphere_zero_iff_norm.mpr hp) (9 / 10) (by norm_num) (by norm_num)).trans ?_
    have h1 : ENNReal.ofReal (9 / 10) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    calc B9 * ENNReal.ofReal (9 / 10) ≤ B9 * 1 := mul_le_mul' le_rfl h1
      _ = B9 := mul_one _
  have hI0 : schwarzCarlesonMeasure F (ball (0 : ℂ) (3 / 5)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
        ENNReal.coe_ne_top))) (s07b_az1_inner hk0 hk1 hF hFD hν hνk)
  have hD : schwarzCarlesonMeasure F unitDisc ≤
      schwarzCarlesonMeasure F (ball (0 : ℂ) (3 / 5)) + ((B9 + B9) + (B9 + B9)) := by
    refine (measure_mono s07b_az1_cover).trans ?_
    refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
    refine (measure_union_le _ _).trans (add_le_add ?_ ?_)
    · exact (measure_union_le _ _).trans (add_le_add (hbox9 1 norm_one)
        (hbox9 (-1) (by rw [norm_neg, norm_one])))
    · exact (measure_union_le _ _).trans (add_le_add (hbox9 I Complex.norm_I)
        (hbox9 (-I) (by rw [norm_neg, Complex.norm_I])))
  have h9 : B9 ≠ ⊤ := by
    rw [hB9]
    exact ENNReal.ofReal_ne_top
  refine ⟨B9 + (schwarzCarlesonMeasure F (ball (0 : ℂ) (3 / 5)) + ((B9 + B9) + (B9 + B9))), ?_, ?_⟩
  · exact ENNReal.add_ne_top.mpr ⟨h9, ENNReal.add_ne_top.mpr ⟨hI0, ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨h9, h9⟩, ENNReal.add_ne_top.mpr ⟨h9, h9⟩⟩⟩⟩
  · intro ζ hζ r hr hr2
    rcases lt_or_ge r 1 with hr1 | hr1
    · exact (hsmall ζ hζ r hr hr1).trans (mul_le_mul' le_self_add le_rfl)
    · have h1 : 1 ≤ ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hr1
      calc schwarzCarlesonMeasure F (unitDisc ∩ ball ζ r)
          ≤ schwarzCarlesonMeasure F unitDisc := measure_mono inter_subset_left
        _ ≤ schwarzCarlesonMeasure F (ball (0 : ℂ) (3 / 5)) + ((B9 + B9) + (B9 + B9)) := hD
        _ ≤ (B9 + (schwarzCarlesonMeasure F (ball (0 : ℂ) (3 / 5)) + ((B9 + B9) + (B9 + B9)))) *
              1 := by
            rw [mul_one]
            exact le_add_self
        _ ≤ _ := mul_le_mul' le_rfl h1

/-- **W-AZ1, vanishing** ((V1) ⇒ (V3)): as `s07b_az1_B3`, and if moreover
`|ν|²/(|w|²−1) dA ∈ CM₀(𝔻*)` (box masses `≤ ε r` for `r < δ(ε)`), then `|S_F|²(1−|z|²)³ dA ∈ CM₀(𝔻)`. -/
theorem s07b_az1_V3 {F ν : ℂ → ℂ} {K k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hF : IsKQC F univ K) (hFD : DifferentiableOn ℂ F unitDisc)
    (hν : ∀ᵐ w, dzbar F w = ν w * dz F w) (hνk : ∀ᵐ w, ‖ν w‖ ≤ k)
    (hC : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ w in unitDiscExterior ∩ ball ζ r, ENNReal.ofReal (‖ν w‖ ^ 2 / (‖w‖ ^ 2 - 1)) ≤
        C * ENNReal.ofReal r)
    (hC0 : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < δ →
      ∫⁻ w in unitDiscExterior ∩ ball ζ r, ENNReal.ofReal (‖ν w‖ ^ 2 / (‖w‖ ^ 2 - 1)) ≤
        ENNReal.ofReal (ε * r)) :
    IsVanishingCarlesonDisk (schwarzCarlesonMeasure F) := by
  refine ⟨s07b_az1_B3 hk0 hk1 hF hFD hν hνk hC, ?_⟩
  obtain ⟨L, hL, hcore⟩ := s07b_az1_core hk0 hk1 hF hFD hν hνk
  obtain ⟨C, hCtop, hCb⟩ := hC
  have hM : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  have hMb : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ s : ℝ, 0 < s → s < 2 →
      ∫⁻ w in unitDiscExterior ∩ ball ζ s, ENNReal.ofReal (‖ν w‖ ^ 2 / (‖w‖ ^ 2 - 1)) ≤
        ENNReal.ofReal (C.toReal * s) := by
    intro ζ hζ s hs hs2
    refine (hCb ζ hζ s hs hs2).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCtop]
  intro ε' hε'
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = ε' / (3 * L) := ⟨_, rfl⟩
  have h3L : 0 < 3 * L := by linarith
  have he0 : 0 < e := by
    rw [he]
    exact div_pos hε' h3L
  obtain ⟨δ, hδ, hδb⟩ := hC0 e he0
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min δ 2 := ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hη]
    exact lt_min hδ (by norm_num)
  have hη2 : η ≤ 2 := by
    rw [hη]
    exact min_le_right _ _
  have hηδ : η ≤ δ := by
    rw [hη]
    exact min_le_left _ _
  refine ⟨min (η / 2) (min (min 1 e) (e * η ^ 2 / (C.toReal + 1))), ?_, ?_⟩
  · exact lt_min (by linarith) (lt_min (lt_min one_pos he0)
      (div_pos (mul_pos he0 (pow_pos hη0 2)) (by linarith)))
  intro ζ hζ r hr hrτ
  have hrη : r < η / 2 := lt_of_lt_of_le hrτ (min_le_left _ _)
  have hr1 : r < 1 := lt_of_lt_of_le hrτ
    ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hre : r < e := lt_of_lt_of_le hrτ
    ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hrm : r < e * η ^ 2 / (C.toReal + 1) := lt_of_lt_of_le hrτ
    ((min_le_right _ _).trans (min_le_right _ _))
  refine (hcore hM he0.le hη0 hη2 ζ hζ (hMb ζ hζ)
    (fun s hs hsη => hδb ζ hζ s hs (lt_of_lt_of_le hsη hηδ)) r hr hrη).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hr2 : r ^ 2 ≤ r := by nlinarith
  have hMr : C.toReal * r ^ 2 / η ^ 2 ≤ e := by
    rw [div_le_iff₀ (pow_pos hη0 2)]
    have h1 : r * (C.toReal + 1) < e * η ^ 2 := by
      rwa [lt_div_iff₀ (by linarith)] at hrm
    nlinarith [mul_le_mul_of_nonneg_left hr2 hM]
  have hX : e + C.toReal * r ^ 2 / η ^ 2 + r ^ 2 ≤ 3 * e := by linarith
  have hLe : L * (3 * e) = ε' := by
    rw [he]
    calc L * (3 * (ε' / (3 * L))) = ε' * (3 * L) / (3 * L) := by ring
      _ = ε' := mul_div_cancel_right₀ ε' h3L.ne'
  calc L * (e + C.toReal * r ^ 2 / η ^ 2 + r ^ 2) * r ≤ L * (3 * e) * r :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX hL.le) hr.le
    _ = ε' * r := by rw [hLe]



/-- Two continuous lifts of the same circle map differ by a constant. -/
theorem s07b_ssa_lift_const {k : ℂ → ℂ} {H K : ℝ → ℝ} (hHc : Continuous H) (hKc : Continuous K)
    (hH : ∀ θ : ℝ, k (Complex.exp (θ * Complex.I)) = Complex.exp (H θ * Complex.I))
    (hK : ∀ θ : ℝ, k (Complex.exp (θ * Complex.I)) = Complex.exp (K θ * Complex.I)) :
    ∃ c : ℝ, ∀ θ : ℝ, K θ = H θ + c := by
  have hint : ∀ θ : ℝ, ∃ n : ℤ, K θ - H θ = n * (2 * π) := by
    intro θ
    have h := (hK θ).symm.trans (hH θ)
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.intCast_re, Complex.intCast_im, mul_zero, mul_one, zero_mul,
      add_zero, sub_zero, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat] at this
    linarith
  have hDc : Continuous fun θ => K θ - H θ := hKc.sub hHc
  have hloc : IsLocallyConstant fun θ => K θ - H θ := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun θ => ?_
    filter_upwards [(hDc.continuousAt (x := θ)).eventually (Metric.ball_mem_nhds _ Real.two_pi_pos)]
      with y hy
    obtain ⟨m, hm⟩ := hint y
    obtain ⟨n, hn⟩ := hint θ
    rw [Real.dist_eq] at hy
    show K y - H y = K θ - H θ
    rw [hm, hn] at hy ⊢
    have hpi : 0 < 2 * π := Real.two_pi_pos
    have h1 : |((m : ℝ) - n)| < 1 := by
      have : |(m : ℝ) * (2 * π) - n * (2 * π)| = |((m : ℝ) - n)| * (2 * π) := by
        rw [← sub_mul, abs_mul, abs_of_pos hpi]
      rw [this] at hy
      exact (mul_lt_iff_lt_one_left hpi).1 hy
    have h2 : ((m - n : ℤ) : ℝ) < 1 := by push_cast; exact (abs_lt.1 h1).2
    have h3 : (-1 : ℝ) < ((m - n : ℤ) : ℝ) := by push_cast; exact (abs_lt.1 h1).1
    have h2' : m - n < 1 := by exact_mod_cast h2
    have h3' : -1 < m - n := by exact_mod_cast h3
    have : m = n := by omega
    rw [this]
  refine ⟨K 0 - H 0, fun θ => ?_⟩
  have : K θ - H θ = K 0 - H 0 := hloc.apply_eq_of_preconnectedSpace θ 0
  linarith

/-- Image measure along an absolutely continuous lift: `|H(A)| = ∫_A u` for measurable `A ⊆ [a, b]`
(from `s07_ssv_cv` with `φ = 1_{H(A)}`). -/
theorem s07b_ssa_image {H u : ℝ → ℝ} (hH : StrictMono H) (hHc : Continuous H)
    (hui : ∀ a b : ℝ, IntegrableOn u (Icc a b))
    (hHu : ∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t) (hpos : ∀ᵐ t, 0 < u t)
    {a b : ℝ} (hab : a ≤ b) {A : Set ℝ} (hA : MeasurableSet A) (hAs : A ⊆ Icc a b) :
    volume (H '' A) = ∫⁻ t in A, ENNReal.ofReal (u t) := by
  have hHA : MeasurableSet (H '' A) :=
    hA.image_of_continuousOn_injOn hHc.continuousOn hH.injective.injOn
  have hsub : H '' A ⊆ Icc (H a) (H b) := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨hH.monotone (hAs ht).1, hH.monotone (hAs ht).2⟩
  have hcv := s07_ssv_cv hH hHc hui hHu hpos hab ((H '' A).indicator fun _ => (1 : ℝ≥0∞))
    ((measurable_const).indicator hHA)
  have hL : ∫⁻ s in Icc (H a) (H b), (H '' A).indicator (fun _ => (1 : ℝ≥0∞)) s = volume (H '' A) := by
    rw [lintegral_indicator_const hHA, one_mul, Measure.restrict_apply hHA, inter_eq_left.2 hsub]
  have hR : ∫⁻ t in Icc a b, (H '' A).indicator (fun _ => (1 : ℝ≥0∞)) (H t) * ENNReal.ofReal (u t) =
      ∫⁻ t in A, ENNReal.ofReal (u t) := by
    have he : (fun t => (H '' A).indicator (fun _ => (1 : ℝ≥0∞)) (H t) * ENNReal.ofReal (u t)) =
        A.indicator fun t => ENNReal.ofReal (u t) := by
      funext t
      by_cases ht : t ∈ A
      · rw [indicator_of_mem (mem_image_of_mem H ht), indicator_of_mem ht, one_mul]
      · have ht' : H t ∉ H '' A := fun h => ht (hH.injective.mem_set_image.1 h)
        rw [indicator_of_notMem ht', indicator_of_notMem ht, zero_mul]
    rw [he, lintegral_indicator hA, Measure.restrict_restrict hA, inter_eq_left.2 hAs]
  rw [← hL, hcv, hR]

/-- **Short-arc power and doubling bounds** (John–Nirenberg + Cauchy–Schwarz + Jensen). If `log u`
has mean oscillation `≤ η₀` on every subinterval of `[a, b]`, then:
* `|H(A)| ≤ C₀ (|A|/(b-a))^{1/2} |H([a, b])|`;
* `η₁ (H b - H a) ≤ H b' - H a'` for `[a', b'] ⊆ [a, b]` with `b - a ≤ 5 (b' - a')`. -/
theorem s07b_ssa_short : ∃ η₀ C₀ η₁ : ℝ, 0 < η₀ ∧ 0 < C₀ ∧ 0 < η₁ ∧ ∀ (H u : ℝ → ℝ),
    StrictMono H → Continuous H → (∀ a b : ℝ, IntegrableOn u (Icc a b)) →
    (∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t) → (∀ᵐ t, 0 < u t) →
    (∀ a b : ℝ, IntegrableOn (fun t => Real.log (u t)) (Icc a b)) →
    ∀ a b : ℝ, a < b →
    (∀ p q : ℝ, a ≤ p → p < q → q ≤ b →
      (∫ t in p..q, |Real.log (u t) - (∫ s in p..q, Real.log (u s)) / (q - p)|) / (q - p) ≤ η₀) →
    (∀ A ⊆ Icc a b, MeasurableSet A →
      volume (H '' A) ≤
        ENNReal.ofReal (C₀ * ((volume A).toReal / (b - a)) ^ (1 / 2 : ℝ)) * volume (H '' Icc a b)) ∧
    ∀ a' b' : ℝ, a ≤ a' → a' < b' → b' ≤ b → b - a ≤ 5 * (b' - a') →
      η₁ * (H b - H a) ≤ H b' - H a' := by
  obtain ⟨KJ, hKJ, hmom⟩ := s07_jn_moment
  set C₂ : ℝ := Real.exp 1 + KJ * (1 / 16) ^ 2 with hC₂
  have hC₂pos : 0 < C₂ := by positivity
  refine ⟨1 / 32, Real.sqrt C₂, Real.exp (-(5 * (1 / 32))) / (5 * Real.sqrt C₂), by norm_num,
    Real.sqrt_pos.2 hC₂pos, by positivity, ?_⟩
  intro H u hH hHc hui hHu hpos hli a b hab hosc
  have hL : 0 < b - a := sub_pos.2 hab
  set c : ℝ := (∫ s in a..b, Real.log (u s)) / (b - a) with hc
  -- John–Nirenberg for `2 log u`
  have hα₂ : ∀ p q : ℝ, IntegrableOn (fun t => 2 * Real.log (u t)) (Icc p q) :=
    fun p q => (hli p q).const_mul 2
  have hosc2 : ∀ p q : ℝ, a ≤ p → p < q → q ≤ b →
      (∫ t in p..q, |2 * Real.log (u t) - (∫ s in p..q, 2 * Real.log (u s)) / (q - p)|) / (q - p)
        ≤ 1 / 16 := by
    intro p q hap hpq hqb
    have h1 : (fun t => |2 * Real.log (u t) - (∫ s in p..q, 2 * Real.log (u s)) / (q - p)|) =
        fun t => 2 * |Real.log (u t) - (∫ s in p..q, Real.log (u s)) / (q - p)| := by
      funext t
      rw [intervalIntegral.integral_const_mul,
        show 2 * Real.log (u t) - 2 * (∫ s in p..q, Real.log (u s)) / (q - p) =
          2 * (Real.log (u t) - (∫ s in p..q, Real.log (u s)) / (q - p)) by ring,
        abs_mul, abs_two]
    rw [h1, intervalIntegral.integral_const_mul, mul_div_assoc]
    have := hosc p q hap hpq hqb
    linarith
  have hJ := hmom (fun t => 2 * Real.log (u t)) hα₂ a b (1 / 16) (by norm_num) le_rfl hosc2 a b
    le_rfl hab le_rfl
  have hJe : ∀ x : ℝ, 2 * Real.log (u x) - (∫ s in a..b, 2 * Real.log (u s)) / (b - a) =
      2 * (Real.log (u x) - c) := by
    intro x
    rw [intervalIntegral.integral_const_mul, hc]
    ring
  -- `∫_I e^{2s} ≤ C₂ |I|`
  have hE : ∫⁻ x in Icc a b, ENNReal.ofReal (Real.exp (2 * (Real.log (u x) - c))) ≤
      ENNReal.ofReal (C₂ * (b - a)) := by
    rw [← setLIntegral_congr Ico_ae_eq_Icc]
    calc ∫⁻ x in Ico a b, ENNReal.ofReal (Real.exp (2 * (Real.log (u x) - c)))
        ≤ ∫⁻ x in Ico a b, (ENNReal.ofReal (Real.exp 1) +
          ENNReal.ofReal ((2 * Real.log (u x) - (∫ s in a..b, 2 * Real.log (u s)) / (b - a)) ^ 2 *
            Real.exp |2 * Real.log (u x) - (∫ s in a..b, 2 * Real.log (u s)) / (b - a)|)) := by
          refine lintegral_mono fun x => ?_
          rw [hJe x]
          set y := 2 * (Real.log (u x) - c)
          have hT : 0 ≤ y ^ 2 * Real.exp |y| := by positivity
          rw [← ENNReal.ofReal_add (Real.exp_pos 1).le hT]
          refine ENNReal.ofReal_le_ofReal ?_
          rcases le_or_gt |y| 1 with hy | hy
          · have : Real.exp y ≤ Real.exp 1 := Real.exp_le_exp.2 ((le_abs_self y).trans hy)
            linarith
          · have h1 : Real.exp y ≤ Real.exp |y| := Real.exp_le_exp.2 (le_abs_self y)
            have h2 : 1 ≤ y ^ 2 := by
              rw [← sq_abs]
              nlinarith
            have h3 : Real.exp |y| ≤ y ^ 2 * Real.exp |y| :=
              le_mul_of_one_le_left (Real.exp_pos _).le h2
            linarith [Real.exp_pos 1]
      _ = ENNReal.ofReal (Real.exp 1) * volume (Ico a b) + ∫⁻ x in Ico a b,
          ENNReal.ofReal ((2 * Real.log (u x) - (∫ s in a..b, 2 * Real.log (u s)) / (b - a)) ^ 2 *
            Real.exp |2 * Real.log (u x) - (∫ s in a..b, 2 * Real.log (u s)) / (b - a)|) := by
          rw [lintegral_add_left measurable_const, setLIntegral_const]
      _ ≤ ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal (b - a) +
          ENNReal.ofReal (KJ * (1 / 16) ^ 2 * (b - a)) := by
          rw [Real.volume_Ico]
          exact add_le_add le_rfl hJ
      _ = ENNReal.ofReal (C₂ * (b - a)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos 1).le, ← ENNReal.ofReal_add (by positivity)
            (by positivity), hC₂]
          congr 1
          ring
  -- `u = e^c e^s` a.e.
  have hu : ∀ᵐ x, ENNReal.ofReal (u x) =
      ENNReal.ofReal (Real.exp c) * ENNReal.ofReal (Real.exp (Real.log (u x) - c)) := by
    filter_upwards [hpos] with x hx
    rw [← ENNReal.ofReal_mul (Real.exp_pos c).le, ← Real.exp_add, add_sub_cancel,
      Real.exp_log hx]
  -- Cauchy–Schwarz via AM–GM: `|H(A)| ≤ e^c √(C₂ |I| |A|)`
  have hCS : ∀ A ⊆ Icc a b, MeasurableSet A →
      volume (H '' A) ≤ ENNReal.ofReal (Real.exp c *
        Real.sqrt (C₂ * (b - a) * (volume A).toReal)) := by
    intro A hAs hAm
    have hAfin : volume A ≠ ⊤ :=
      ((measure_mono hAs).trans_lt (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)).ne
    rw [s07b_ssa_image hH hHc hui hHu hpos hab.le hAm hAs,
      lintegral_congr_ae (ae_restrict_of_ae hu), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ENNReal.ofReal_mul (Real.exp_pos c).le]
    refine mul_le_mul' le_rfl ?_
    set V := (volume A).toReal with hV
    have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
    rcases hV0.eq_or_lt with hV0' | hVpos
    · have hA0 : volume A = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).1 hV0'.symm with h | h
        · exact h
        · exact absurd h hAfin
      rw [Measure.restrict_eq_zero.2 hA0, lintegral_zero_measure]
      exact bot_le
    set S := Real.sqrt (C₂ * (b - a) * V) with hS
    have hSpos : 0 < S := Real.sqrt_pos.2 (by positivity)
    have hSS : S ^ 2 = C₂ * (b - a) * V := Real.sq_sqrt (by positivity)
    set lam := S / (C₂ * (b - a)) with hlam
    have hlam0 : 0 < lam := by positivity
    have hI2 : ∫⁻ x in A, ENNReal.ofReal (Real.exp (2 * (Real.log (u x) - c))) ≤
        ENNReal.ofReal (C₂ * (b - a)) := (lintegral_mono_set hAs).trans hE
    have hpt : ∫⁻ x in A, ENNReal.ofReal (Real.exp (Real.log (u x) - c)) ≤
        ∫⁻ x in A, (ENNReal.ofReal (lam / 2) *
          ENNReal.ofReal (Real.exp (2 * (Real.log (u x) - c))) + ENNReal.ofReal (1 / (2 * lam))) := by
      refine lintegral_mono fun x => ?_
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
        (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      set E := Real.exp (Real.log (u x) - c)
      have hE2 : Real.exp (2 * (Real.log (u x) - c)) = E ^ 2 := by
        rw [sq, ← Real.exp_add]
        ring_nf
      rw [hE2]
      have key : lam / 2 * E ^ 2 + 1 / (2 * lam) - E = (lam * E - 1) ^ 2 / (2 * lam) := by
        field_simp
        ring
      have : 0 ≤ (lam * E - 1) ^ 2 / (2 * lam) := by positivity
      linarith
    rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      setLIntegral_const] at hpt
    refine hpt.trans ((add_le_add (mul_le_mul_of_nonneg_left hI2 bot_le)
      (le_of_eq (congrArg (fun x => ENNReal.ofReal (1 / (2 * lam)) * x)
        (ENNReal.ofReal_toReal hAfin).symm))).trans (le_of_eq ?_))
    rw [← hV, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    rw [hlam]
    field_simp
    nlinarith [hSS]
  -- the image of an interval
  have hIcc : ∀ p q : ℝ, p ≤ q → volume (H '' Icc p q) = ENNReal.ofReal (H q - H p) := by
    intro p q hpq
    have himg : H '' Icc p q = Icc (H p) (H q) := by
      refine Subset.antisymm ?_ (intermediate_value_Icc hpq hHc.continuousOn)
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨hH.monotone ht.1, hH.monotone ht.2⟩
    rw [himg, Real.volume_Icc]
  -- Jensen
  have hjen : Real.exp c * (b - a) ≤ H b - H a := s07_ssc_jensen hui hHu hpos hli hab
  -- the bound for `A = I`
  have hup : H b - H a ≤ Real.exp c * Real.sqrt C₂ * (b - a) := by
    have h := hCS (Icc a b) subset_rfl measurableSet_Icc
    rw [hIcc a b hab.le, Real.volume_Icc, ENNReal.toReal_ofReal hL.le] at h
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
    have h3 : Real.sqrt (C₂ * (b - a) * (b - a)) = Real.sqrt C₂ * (b - a) := by
      rw [mul_assoc, Real.sqrt_mul hC₂pos.le, Real.sqrt_mul_self hL.le]
    rw [h3] at h2
    linarith
  refine ⟨fun A hAs hAm => ?_, fun a' b' haa' hab' hb'b h5 => ?_⟩
  · -- power form
    refine (hCS A hAs hAm).trans ?_
    rw [hIcc a b hab.le, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    set V := (volume A).toReal
    have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
    have h1 : Real.sqrt (C₂ * (b - a) * V) =
        Real.sqrt C₂ * (V / (b - a)) ^ (1 / 2 : ℝ) * (b - a) := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_div' _ hL.le]
      rw [show C₂ * (b - a) * V = C₂ * (V * (b - a)) by ring, Real.sqrt_mul hC₂pos.le,
        Real.sqrt_mul hV0]
      rw [mul_assoc (Real.sqrt C₂), div_mul_eq_mul_div, mul_div_assoc, Real.div_sqrt]
    rw [h1]
    have hp : 0 ≤ Real.sqrt C₂ * (V / (b - a)) ^ (1 / 2 : ℝ) := by positivity
    calc Real.exp c * (Real.sqrt C₂ * (V / (b - a)) ^ (1 / 2 : ℝ) * (b - a))
        = Real.sqrt C₂ * (V / (b - a)) ^ (1 / 2 : ℝ) * (Real.exp c * (b - a)) := by ring
      _ ≤ Real.sqrt C₂ * (V / (b - a)) ^ (1 / 2 : ℝ) * (H b - H a) :=
          mul_le_mul_of_nonneg_left hjen hp
  · -- doubling
    have hL' : 0 < b' - a' := sub_pos.2 hab'
    set cJ : ℝ := (∫ s in a'..b', Real.log (u s)) / (b' - a') with hcJ
    have hjenJ : Real.exp cJ * (b' - a') ≤ H b' - H a' := s07_ssc_jensen hui hHu hpos hli hab'
    -- `cJ ≥ c - 5 η₀`
    have hint : ∀ p q : ℝ, IntervalIntegrable (fun t => Real.log (u t)) volume p q := fun p q =>
      (hli (min p q) (max p q)).intervalIntegrable
    have habs : ∀ p q : ℝ, IntervalIntegrable (fun t => |Real.log (u t) - c|) volume p q :=
      fun p q => ((hint p q).sub intervalIntegrable_const).abs
    have hsub : ∫ t in a'..b', (Real.log (u t) - c) = (cJ - c) * (b' - a') := by
      rw [intervalIntegral.integral_sub (hint a' b') intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul, hcJ]
      field_simp
    have hmono : ∫ t in a'..b', |Real.log (u t) - c| ≤ ∫ t in a..b, |Real.log (u t) - c| := by
      rw [intervalIntegral.integral_of_le hab'.le, intervalIntegral.integral_of_le hab.le]
      refine setIntegral_mono_set ?_ (Filter.Eventually.of_forall fun t => abs_nonneg _)
        (Filter.Eventually.of_forall (Ioc_subset_Ioc haa' hb'b))
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).1 (habs a b))
    have hle : |∫ t in a'..b', (Real.log (u t) - c)| ≤ ∫ t in a'..b', |Real.log (u t) - c| :=
      intervalIntegral.abs_integral_le_integral_abs hab'.le
    have hos := hosc a b le_rfl hab le_rfl
    rw [div_le_iff₀ hL] at hos
    have hcJ5 : c - 5 * (1 / 32) ≤ cJ := by
      have h1 : -((cJ - c) * (b' - a')) ≤ (1 / 32) * (b - a) := by
        have := neg_abs_le (∫ t in a'..b', (Real.log (u t) - c))
        rw [hsub] at this hle
        linarith [abs_nonneg ((cJ - c) * (b' - a')), neg_le_abs ((cJ - c) * (b' - a'))]
      by_contra hcon
      have hlt : cJ - c < -(5 * (1 / 32)) := by linarith
      have : -((cJ - c) * (b' - a')) > 5 * (1 / 32) * (b' - a') := by nlinarith
      nlinarith
    have hexp : Real.exp c * Real.exp (-(5 * (1 / 32))) ≤ Real.exp cJ := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have hsq : 0 < Real.sqrt C₂ := Real.sqrt_pos.2 hC₂pos
    have hec : 0 < Real.exp c := Real.exp_pos c
    have he5 : 0 < Real.exp (-(5 * (1 / 32))) := Real.exp_pos _
    calc Real.exp (-(5 * (1 / 32))) / (5 * Real.sqrt C₂) * (H b - H a)
        ≤ Real.exp (-(5 * (1 / 32))) / (5 * Real.sqrt C₂) *
            (Real.exp c * Real.sqrt C₂ * (b - a)) :=
          mul_le_mul_of_nonneg_left hup (by positivity)
      _ = Real.exp c * Real.exp (-(5 * (1 / 32))) * ((b - a) / 5) := by
          field_simp
      _ ≤ Real.exp cJ * (b' - a') := by
          refine mul_le_mul hexp (by linarith) (by positivity) (Real.exp_pos _).le
      _ ≤ H b' - H a' := hjenJ

/-- The SS data of `k` on an arbitrary continuous lift `K`. `K` differs from the lift in
`IsStronglySymmetric` by a constant, so the density `u` is the same. -/
theorem s07b_ssa_lift_data {k : ℂ → ℂ} (hk : IsStronglySymmetric k) {K : ℝ → ℝ} (hKc : Continuous K)
    (hl : ∀ θ : ℝ, k (Complex.exp (θ * Complex.I)) = Complex.exp (K θ * Complex.I)) :
    ∃ u : ℝ → ℝ, StrictMono K ∧ (∀ θ : ℝ, K (θ + 2 * π) = K θ + 2 * π) ∧
      (∀ a b : ℝ, IntegrableOn u (Icc a b)) ∧
      (∀ θ : ℝ, K θ = K 0 + ∫ t in (0 : ℝ)..θ, u t) ∧ (∀ᵐ t, 0 < u t) ∧
      (∀ a b : ℝ, IntegrableOn (fun t => Real.log (u t)) (Icc a b)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a < b → b - a ≤ δ →
        (∫ t in a..b, |Real.log (u t) - (∫ s in a..b, Real.log (u s)) / (b - a)|) / (b - a) ≤ ε := by
  obtain ⟨H, u, hH, hHc, hper, hlH, hui, hHu, hpos, hli, hv⟩ := hk
  obtain ⟨c, hc⟩ := s07b_ssa_lift_const hHc hKc hlH hl
  refine ⟨u, fun x y hxy => ?_, fun θ => ?_, hui, fun θ => ?_, hpos, hli, hv⟩
  · rw [hc x, hc y]
    linarith [hH hxy]
  · rw [hc (θ + 2 * π), hc θ, hper]
    ring
  · linarith [hc θ, hc 0, hHu θ]

/-- **SS ⇒ A∞, lift form** (input of C1v; `sec02-prelim.tex`: `SS ⊆ SQS`). For a strongly symmetric
circle map `k`, every continuous lift `K`:
* is strictly increasing;
* satisfies the power form on arcs of length `≤ 2π`;
* satisfies the doubling bound;
* maps only null sets to null sets. -/
theorem s07b_ssa_pow {k : ℂ → ℂ} (hk : IsStronglySymmetric k) {K : ℝ → ℝ} (hKc : Continuous K)
    (hl : ∀ θ : ℝ, k (Complex.exp (θ * Complex.I)) = Complex.exp (K θ * Complex.I)) :
    StrictMono K ∧
    (∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ a b : ℝ, a < b → b - a ≤ 2 * π → ∀ A ⊆ Icc a b,
      MeasurableSet A → volume (K '' A) ≤
        ENNReal.ofReal (C * ((volume A).toReal / (b - a)) ^ δ) * volume (K '' Icc a b)) ∧
    (∃ η : ℝ, 0 < η ∧ ∀ a a' b' c : ℝ, a ≤ a' → a' < b' → b' ≤ c → c - a ≤ 2 * π →
      c - a ≤ 5 * (b' - a') → η * (K c - K a) ≤ K b' - K a') ∧
    ∀ A : Set ℝ, MeasurableSet A → volume (K '' A) = 0 → volume A = 0 := by
  obtain ⟨u, hKm, hKper, hui, hKu, hpos, hli, hv⟩ := s07b_ssa_lift_data hk hKc hl
  obtain ⟨η₀, C₀, η₁, hη₀, hC₀, hη₁, hS⟩ := s07b_ssa_short
  obtain ⟨δ', hδ', hδv⟩ := hv η₀ hη₀
  have hSab : ∀ a b : ℝ, a < b → b - a ≤ δ' →
      (∀ A ⊆ Icc a b, MeasurableSet A →
        volume (K '' A) ≤
          ENNReal.ofReal (C₀ * ((volume A).toReal / (b - a)) ^ (1 / 2 : ℝ)) * volume (K '' Icc a b)) ∧
      ∀ a' b' : ℝ, a ≤ a' → a' < b' → b' ≤ b → b - a ≤ 5 * (b' - a') →
        η₁ * (K b - K a) ≤ K b' - K a' := fun a b hab hba =>
    hS K u hKm hKc hui hKu hpos hli a b hab fun p q hap hpq hqb => hδv p q hpq (by linarith)
  have hpi : 0 < 2 * π := Real.two_pi_pos
  refine ⟨hKm, ?_, ?_, ?_⟩
  · -- power form
    set N₀ : ℝ := 2 * π / δ' + 1 with hN₀
    have hN₀1 : 1 ≤ N₀ := by
      have : 0 ≤ 2 * π / δ' := by positivity
      linarith
    have hN₀h : 1 ≤ N₀ ^ (1 / 2 : ℝ) := Real.one_le_rpow hN₀1 (by norm_num)
    refine ⟨C₀ * N₀ * N₀ ^ (1 / 2 : ℝ), 1 / 2, by positivity, by norm_num,
      fun a b hab hab2 A hAs hAm => ?_⟩
    have hL : 0 < b - a := sub_pos.2 hab
    have hAfin : volume A ≠ ⊤ :=
      ((measure_mono hAs).trans_lt (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)).ne
    set V := (volume A).toReal with hV
    have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
    by_cases hshort : b - a ≤ δ'
    · refine ((hSab a b hab hshort).1 A hAs hAm).trans
        (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le)
      have hx : 0 ≤ (V / (b - a)) ^ (1 / 2 : ℝ) := by positivity
      have h1 : 1 ≤ N₀ * N₀ ^ (1 / 2 : ℝ) := by nlinarith
      nlinarith [mul_nonneg (mul_nonneg hC₀.le hx) (sub_nonneg.2 h1)]
    · have hlong : δ' < b - a := lt_of_not_ge hshort
      set N : ℕ := ⌈(b - a) / δ'⌉₊ with hNdef
      have hN1 : (b - a) / δ' ≤ N := Nat.le_ceil _
      have hNlt : (N : ℝ) < (b - a) / δ' + 1 := Nat.ceil_lt_add_one (by positivity)
      have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN1
      have hN0 : 0 < N := by exact_mod_cast hNpos
      set ℓ : ℝ := (b - a) / N with hℓ
      have hℓpos : 0 < ℓ := by positivity
      have hℓδ : ℓ ≤ δ' := by
        rw [hℓ, div_le_iff₀ hNpos]
        rw [div_le_iff₀ hδ'] at hN1
        linarith
      have hNℓ : (N : ℝ) * ℓ = b - a := by
        rw [hℓ]
        field_simp
      have hNN₀ : (N : ℝ) ≤ N₀ := by
        have : (b - a) / δ' ≤ 2 * π / δ' := div_le_div_of_nonneg_right hab2 hδ'.le
        linarith
      set J : ℕ → Set ℝ := fun i => Icc (a + i * ℓ) (a + (i + 1) * ℓ) with hJ
      have hJsub : ∀ i ∈ Finset.range N, J i ⊆ Icc a b := by
        intro i hi x hx
        have hi' : (i : ℝ) + 1 ≤ N := by
          have : i + 1 ≤ N := Finset.mem_range.1 hi
          exact_mod_cast this
        refine ⟨by nlinarith [hx.1, (Nat.cast_nonneg i : (0 : ℝ) ≤ i)], ?_⟩
        have := hx.2
        nlinarith
      -- the cover
      have hcover : A ⊆ ⋃ i ∈ Finset.range N, A ∩ J i := by
        intro x hx
        have hxI := hAs hx
        have h0 : 0 ≤ (x - a) / ℓ := div_nonneg (by linarith [hxI.1]) hℓpos.le
        have hN' : (x - a) / ℓ ≤ N := by
          rw [div_le_iff₀ hℓpos]
          linarith [hxI.2]
        set j := ⌊(x - a) / ℓ⌋₊
        have hj1 : (j : ℝ) ≤ (x - a) / ℓ := Nat.floor_le h0
        have hj2 : (x - a) / ℓ < j + 1 := Nat.lt_floor_add_one _
        rw [mem_iUnion₂]
        by_cases hjN : j < N
        · refine ⟨j, Finset.mem_range.2 hjN, hx, ?_, ?_⟩
          · rw [le_div_iff₀ hℓpos] at hj1
            linarith
          · rw [div_lt_iff₀ hℓpos] at hj2
            linarith
        · have hjN' : (N : ℝ) ≤ j := by exact_mod_cast not_lt.1 hjN
          have hNm : ((N - 1 : ℕ) : ℝ) = N - 1 := by
            rw [Nat.cast_sub (by omega), Nat.cast_one]
          refine ⟨N - 1, Finset.mem_range.2 (by omega), hx, ?_, ?_⟩
          · rw [hNm]
            have : (N : ℝ) ≤ (x - a) / ℓ := hjN'.trans hj1
            rw [le_div_iff₀ hℓpos] at this
            nlinarith
          · rw [hNm]
            nlinarith [hxI.2]
      -- each piece
      have hpiece : ∀ i ∈ Finset.range N, volume (K '' (A ∩ J i)) ≤
          ENNReal.ofReal (C₀ * (V / ℓ) ^ (1 / 2 : ℝ)) * volume (K '' Icc a b) := by
        intro i hi
        have hlen : a + (i + 1) * ℓ - (a + i * ℓ) = ℓ := by ring
        have hlt : a + i * ℓ < a + (i + 1) * ℓ := by linarith
        have h := (hSab _ _ hlt (by rw [hlen]; exact hℓδ)).1 (A ∩ J i) inter_subset_right
          (hAm.inter measurableSet_Icc)
        rw [hlen] at h
        refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_)
          (measure_mono (image_mono (hJsub i hi))))
        have hm : (volume (A ∩ J i)).toReal ≤ V :=
          ENNReal.toReal_mono hAfin (measure_mono inter_subset_left)
        have := Real.rpow_le_rpow (div_nonneg ENNReal.toReal_nonneg hℓpos.le)
          (div_le_div_of_nonneg_right hm hℓpos.le) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        exact mul_le_mul_of_nonneg_left this hC₀.le
      have himg : K '' A ⊆ ⋃ i ∈ Finset.range N, K '' (A ∩ J i) := by
        refine (image_mono hcover).trans ?_
        rw [image_iUnion₂]
      calc volume (K '' A) ≤ ∑ i ∈ Finset.range N, volume (K '' (A ∩ J i)) :=
            (measure_mono himg).trans (measure_biUnion_finset_le _ _)
        _ ≤ ∑ i ∈ Finset.range N,
            ENNReal.ofReal (C₀ * (V / ℓ) ^ (1 / 2 : ℝ)) * volume (K '' Icc a b) :=
            Finset.sum_le_sum hpiece
        _ = ENNReal.ofReal (N * (C₀ * (V / ℓ) ^ (1 / 2 : ℝ))) * volume (K '' Icc a b) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
              ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
        _ ≤ ENNReal.ofReal (C₀ * N₀ * N₀ ^ (1 / 2 : ℝ) * (V / (b - a)) ^ (1 / 2 : ℝ)) *
            volume (K '' Icc a b) := by
            refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
            have hVℓ : V / ℓ = N * (V / (b - a)) := by
              rw [hℓ]
              field_simp
            rw [hVℓ, Real.mul_rpow (Nat.cast_nonneg N) (by positivity)]
            have hNh : (N : ℝ) ^ (1 / 2 : ℝ) ≤ N₀ ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow (Nat.cast_nonneg N) hNN₀ (by norm_num)
            have hx : 0 ≤ (V / (b - a)) ^ (1 / 2 : ℝ) := by positivity
            have hNh0 : 0 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by positivity
            have e1 : (N : ℝ) * (C₀ * ((N : ℝ) ^ (1 / 2 : ℝ) * (V / (b - a)) ^ (1 / 2 : ℝ))) =
                C₀ * (V / (b - a)) ^ (1 / 2 : ℝ) * ((N : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ)) := by ring
            have e2 : C₀ * N₀ * N₀ ^ (1 / 2 : ℝ) * (V / (b - a)) ^ (1 / 2 : ℝ) =
                C₀ * (V / (b - a)) ^ (1 / 2 : ℝ) * (N₀ * N₀ ^ (1 / 2 : ℝ)) := by ring
            rw [e1, e2]
            exact mul_le_mul_of_nonneg_left (mul_le_mul hNN₀ hNh hNh0 (by linarith))
              (mul_nonneg hC₀.le hx)
  · -- doubling
    set g : ℝ → ℝ := fun x => K (x + δ' / 5) - K x with hg
    have hgc : Continuous g := (hKc.comp (continuous_id.add continuous_const)).sub hKc
    have hgp : Function.Periodic g (2 * π) := by
      intro x
      show K (x + 2 * π + δ' / 5) - K (x + 2 * π) = K (x + δ' / 5) - K x
      rw [show x + 2 * π + δ' / 5 = x + δ' / 5 + 2 * π by ring, hKper, hKper]
      ring
    obtain ⟨m, ⟨x₀, hx₀⟩, hmin⟩ :=
      (hgp.compact_of_continuous hpi.ne' hgc).exists_isLeast (range_nonempty g)
    have hm : 0 < m := by
      rw [← hx₀]
      exact sub_pos.2 (hKm (by linarith))
    refine ⟨min η₁ (m / (2 * π)), lt_min hη₁ (by positivity),
      fun a a' b' c haa' hab' hb'c hc2 h5 => ?_⟩
    have hnn : 0 ≤ K c - K a := sub_nonneg.2 (hKm.monotone (by linarith))
    by_cases hs : c - a ≤ δ'
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hnn).trans
        ((hSab a c (by linarith) hs).2 a' b' haa' hab' hb'c h5)
    · have hlong : δ' < c - a := lt_of_not_ge hs
      have h1 : m ≤ K b' - K a' := by
        have := hmin ⟨a', rfl⟩
        have h2 : K (a' + δ' / 5) ≤ K b' := hKm.monotone (by linarith)
        show m ≤ K b' - K a'
        have : m ≤ K (a' + δ' / 5) - K a' := this
        linarith
      have h2 : K c - K a ≤ 2 * π := by
        have := hKm.monotone (show c ≤ a + 2 * π by linarith)
        rw [hKper] at this
        linarith
      calc min η₁ (m / (2 * π)) * (K c - K a) ≤ m / (2 * π) * (K c - K a) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hnn
        _ ≤ m / (2 * π) * (2 * π) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = m := by field_simp
        _ ≤ K b' - K a' := h1
  · -- null sets
    intro A hA h0
    have hn : ∀ n : ℤ, volume (A ∩ Icc (n : ℝ) (n + 1)) = 0 := by
      intro n
      have hsub : A ∩ Icc (n : ℝ) (n + 1) ⊆ Icc (n : ℝ) (n + 1) := inter_subset_right
      have hm := hA.inter (measurableSet_Icc (a := (n : ℝ)) (b := n + 1))
      have himg := s07b_ssa_image hKm hKc hui hKu hpos (by linarith : (n : ℝ) ≤ n + 1) hm hsub
      have h1 : volume (K '' (A ∩ Icc (n : ℝ) (n + 1))) = 0 :=
        measure_mono_null (image_mono inter_subset_left) h0
      rw [himg] at h1
      have hae : AEMeasurable (fun t => ENNReal.ofReal (u t))
          (volume.restrict (A ∩ Icc (n : ℝ) (n + 1))) :=
        ((hui n (n + 1)).mono_set hsub).aemeasurable.ennreal_ofReal
      rw [lintegral_eq_zero_iff' hae] at h1
      have h2 : ∀ᵐ t ∂(volume.restrict (A ∩ Icc (n : ℝ) (n + 1))), False := by
        filter_upwards [h1, ae_restrict_of_ae hpos] with t ht ht'
        have : ENNReal.ofReal (u t) = 0 := ht
        rw [ENNReal.ofReal_eq_zero] at this
        linarith
      have h3 := ae_iff.1 h2
      simp only [not_false_eq_true, setOf_true, Measure.restrict_apply_univ] at h3
      exact h3
    refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null hn)
    rw [mem_iUnion]
    exact ⟨⌊x⌋, hx, Int.floor_le x, (Int.lt_floor_add_one x).le⟩


/-- T1 helper: the derivative Carleson measure of a set, as a set integral over `𝔻`. -/
theorem s07b_fkph_c_muE (φ : ℂ → ℂ) {E : Set ℂ} (hE : MeasurableSet E) :
    derivCarlesonMeasure φ E =
      ∫⁻ u in unitDisc ∩ E, ENNReal.ofReal (‖φ u‖ ^ 2 * (1 - ‖u‖ ^ 2)) := by
  show ((volume.restrict unitDisc).withDensity
    fun z => ENNReal.ofReal (‖φ z‖ ^ 2 * (1 - ‖z‖ ^ 2))) E = _
  rw [withDensity_apply _ hE, Measure.restrict_restrict hE, inter_comm]

/-- T1 helper (Whitney–Fubini swap with radius `3/4`; variant of `s02_sw_whitney`, constant `90`). -/
theorem s07b_fkph_c_whit {F : ℂ → ℝ≥0∞} (hF : Measurable F) {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1)
    (r : ℝ) :
    (∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) *
        ∫⁻ w in ball z (3 * (1 - ‖z‖) / 4), F w) ≤
      ENNReal.ofReal 90 * ∫⁻ w in unitDisc ∩ ball ζ (2 * r), F w := by
  have hBm : MeasurableSet (unitDisc ∩ ball ζ r) := measurableSet_ball.inter measurableSet_ball
  have hB'm : MeasurableSet (unitDisc ∩ ball ζ (2 * r)) :=
    measurableSet_ball.inter measurableSet_ball
  have hζ1 : ‖ζ‖ = 1 := by simpa using hζ
  obtain ⟨S, hS⟩ : ∃ S : Set (ℂ × ℂ), S = {p | dist p.2 p.1 < 3 * (1 - ‖p.1‖) / 4} := ⟨_, rfl⟩
  have hmemS : ∀ z w, (z, w) ∈ S ↔ dist w z < 3 * (1 - ‖z‖) / 4 := by
    intro z w
    rw [hS]
    rfl
  have hSm : MeasurableSet S := by
    rw [hS]
    exact (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet
  have ham : Measurable fun z : ℂ => ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) :=
    Measurable.ennreal_ofReal (by fun_prop)
  have hG : Measurable fun p : ℂ × ℂ =>
      ENNReal.ofReal (((1 - ‖p.1‖) ^ 2)⁻¹) * S.indicator (fun q => F q.2) p :=
    (ham.comp measurable_fst).mul ((hF.comp measurable_snd).indicator hSm)
  have heq : ∀ z, ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) * ∫⁻ w in ball z (3 * (1 - ‖z‖) / 4), F w =
      ∫⁻ w, ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) * S.indicator (fun q => F q.2) (z, w) := by
    intro z
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun w => ?_
    by_cases hw : (z, w) ∈ S
    · rw [Set.indicator_of_mem hw,
        Set.indicator_of_mem (show w ∈ ball z (3 * (1 - ‖z‖) / 4) from (hmemS z w).1 hw)]
    · rw [Set.indicator_of_notMem hw, mul_zero,
        Set.indicator_of_notMem
          (show w ∉ ball z (3 * (1 - ‖z‖) / 4) from fun h => hw ((hmemS z w).2 h))]
  have hpw : ∀ w, (∫⁻ z in unitDisc ∩ ball ζ r,
      ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) * S.indicator (fun q => F q.2) (z, w)) ≤
        (unitDisc ∩ ball ζ (2 * r)).indicator (fun w => ENNReal.ofReal 90 * F w) w := by
    intro w
    by_cases hw : w ∈ unitDisc ∩ ball ζ (2 * r)
    · rw [Set.indicator_of_mem hw]
      have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw.1
      obtain ⟨v, hv⟩ : ∃ v : ℝ, v = 1 - ‖w‖ := ⟨_, rfl⟩
      have hv0 : 0 < v := by linarith
      have hvol : volume (ball w (3 * v)) = ENNReal.ofReal ((3 * v) ^ 2 * π) := by
        rw [Complex.volume_ball, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (3 * v) ^ 2),
          ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 3 * v), ← NNReal.coe_real_pi,
          ENNReal.ofReal_coe_nnreal]
      calc (∫⁻ z in unitDisc ∩ ball ζ r,
            ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) * S.indicator (fun q => F q.2) (z, w))
          ≤ ∫⁻ z in unitDisc ∩ ball ζ r,
              (ball w (3 * v)).indicator (fun _ => ENNReal.ofReal (49 / 16 * (v ^ 2)⁻¹) * F w) z := by
            refine setLIntegral_mono' hBm fun z hz => ?_
            by_cases hzw : (z, w) ∈ S
            · have hd := (hmemS z w).1 hzw
              have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz.1
              rw [dist_eq_norm] at hd
              have t1 := norm_sub_norm_le w z
              have t2 := norm_sub_norm_le z w
              rw [norm_sub_rev] at t2
              have hzv : z ∈ ball w (3 * v) := by
                rw [mem_ball, dist_eq_norm, norm_sub_rev]
                linarith
              rw [Set.indicator_of_mem hzw, Set.indicator_of_mem hzv]
              refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
              have hu : 4 / 7 * v ≤ 1 - ‖z‖ := by linarith
              have h49 : 16 / 49 * v ^ 2 ≤ (1 - ‖z‖) ^ 2 := by nlinarith
              calc ((1 - ‖z‖) ^ 2)⁻¹ ≤ (16 / 49 * v ^ 2)⁻¹ := inv_anti₀ (by positivity) h49
                _ = 49 / 16 * (v ^ 2)⁻¹ := by rw [mul_inv]; norm_num
            · rw [Set.indicator_of_notMem hzw, mul_zero]
              exact bot_le
        _ ≤ ∫⁻ z, (ball w (3 * v)).indicator
              (fun _ => ENNReal.ofReal (49 / 16 * (v ^ 2)⁻¹) * F w) z :=
            setLIntegral_le_lintegral _ _
        _ = ENNReal.ofReal (49 / 16 * (v ^ 2)⁻¹) * F w * volume (ball w (3 * v)) :=
            lintegral_indicator_const measurableSet_ball _
        _ ≤ ENNReal.ofReal 90 * F w := by
            rw [hvol, mul_right_comm,
              ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 49 / 16 * (v ^ 2)⁻¹)]
            refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
            have e : 49 / 16 * (v ^ 2)⁻¹ * ((3 * v) ^ 2 * π) = 441 / 16 * π := by field_simp; ring
            rw [e]
            linarith [Real.pi_lt_d2]
    · rw [Set.indicator_of_notMem hw]
      refine le_of_eq ((setLIntegral_congr_fun hBm (g := fun _ => 0) fun z hz => ?_).trans
        lintegral_zero)
      by_cases hzw : (z, w) ∈ S
      · exfalso
        apply hw
        have hd := (hmemS z w).1 hzw
        have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz.1
        have hzζ : dist z ζ < r := hz.2
        rw [dist_eq_norm] at hd hzζ
        have t1 := norm_sub_norm_le w z
        have t3 := norm_sub_norm_le ζ z
        rw [norm_sub_rev ζ z, hζ1] at t3
        refine ⟨mem_ball_zero_iff.mpr (by linarith), ?_⟩
        rw [mem_ball, dist_eq_norm]
        calc ‖w - ζ‖ ≤ ‖w - z‖ + ‖z - ζ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ < 2 * r := by linarith
      · simp only [Set.indicator_of_notMem hzw, mul_zero]
  calc (∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) *
        ∫⁻ w in ball z (3 * (1 - ‖z‖) / 4), F w)
      = ∫⁻ z in unitDisc ∩ ball ζ r, ∫⁻ w,
          ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) * S.indicator (fun q => F q.2) (z, w) :=
        setLIntegral_congr_fun hBm fun z _ => heq z
    _ = ∫⁻ w, ∫⁻ z in unitDisc ∩ ball ζ r,
          ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) * S.indicator (fun q => F q.2) (z, w) :=
        lintegral_lintegral_swap hG.aemeasurable
    _ ≤ ∫⁻ w, (unitDisc ∩ ball ζ (2 * r)).indicator (fun w => ENNReal.ofReal 90 * F w) w :=
        lintegral_mono fun w => hpw w
    _ = ENNReal.ofReal 90 * ∫⁻ w in unitDisc ∩ ball ζ (2 * r), F w := by
        rw [lintegral_indicator hB'm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- T1 helper: measurability of the Carleson density of `f''/f'`. -/
theorem s07b_fkph_c_Fmeas (f : ℂ → ℂ) :
    Measurable fun u : ℂ =>
      ENNReal.ofReal (‖deriv (deriv f) u / deriv f u‖ ^ 2 * (1 - ‖u‖ ^ 2)) := by
  have h1 : Measurable fun u : ℂ => deriv (deriv f) u / deriv f u :=
    (measurable_deriv _).div (measurable_deriv _)
  exact Measurable.ennreal_ofReal ((h1.norm.pow_const 2).mul
    (measurable_const.sub (measurable_norm.pow_const 2)))

/-- T1 helper: distance between two points on the same ray. -/
theorem s07b_fkph_c_radsub {ζ : ℂ} (hζ : ‖ζ‖ = 1) (a b : ℝ) :
    ‖(a : ℂ) * ζ - (b : ℂ) * ζ‖ = |a - b| := by
  rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, hζ, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- T1 block C1 (little Bloch, AZ/Pommerenke): `log f' ∈ VMOA` ⇒ `(1 − |z|²)|f''/f'(z)| → 0` as `|z| → 1`
(sub-mean value `s02_sw_meanValue` on `D(z, (1−|z|)/2)` + the CM₀ bound on the box `𝔻 ∩ D(z/|z|, 2(1−|z|))`). -/
theorem s07b_fkph_c_bloch {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (hv : LogDerivVMOA f) :
    ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ ∀ z : ℂ, s < ‖z‖ → ‖z‖ < 1 →
      (1 - ‖z‖ ^ 2) * ‖deriv (deriv f) z / deriv f z‖ ≤ ε := by
  intro ε hε
  obtain ⟨hφd, -⟩ := s02_sw_logDeriv hf
  obtain ⟨δ, hδ, hCM⟩ := hv.2 (ε ^ 2 / 32) (by positivity)
  refine ⟨max (1 / 2) (1 - δ / 4), le_max_of_le_left (by norm_num),
    max_lt (by norm_num) (by linarith), ?_⟩
  intro z hz hz1
  have hz2 : 1 / 2 < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
  have hzδ : 1 - δ / 4 < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hz
  have hn0 : 0 < ‖z‖ := by linarith
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = 1 - ‖z‖ := ⟨_, rfl⟩
  have hd0 : 0 < d := by linarith
  obtain ⟨ζ, hζd⟩ : ∃ ζ : ℂ, ζ = ((‖z‖⁻¹ : ℝ) : ℂ) * z := ⟨_, rfl⟩
  have hζ1 : ‖ζ‖ = 1 := by
    rw [hζd, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hn0.le),
      inv_mul_cancel₀ hn0.ne']
  have hζs : ζ ∈ sphere (0 : ℂ) 1 := by rw [mem_sphere_zero_iff_norm]; exact hζ1
  have hzζ : ‖z - ζ‖ = d := by
    have e : ((‖z‖ : ℝ) : ℂ) * ζ = z := by
      rw [hζd, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hn0.ne', Complex.ofReal_one,
        one_mul]
    have e2 : ((1 : ℝ) : ℂ) * ζ = ζ := by simp
    have h := s07b_fkph_c_radsub hζ1 ‖z‖ 1
    rw [e, e2, abs_of_nonpos (by linarith)] at h
    rw [h, hd]
    ring
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = d / 2 := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hsub : closedBall z ρ ⊆ unitDisc := by
    intro u hu
    show u ∈ Metric.ball (0 : ℂ) 1
    rw [mem_ball_zero_iff]
    rw [mem_closedBall, dist_eq_norm] at hu
    have := norm_le_insert' u z
    linarith
  have hMV := s02_sw_meanValue hρ0 (hφd.mono hsub)
  beta_reduce at hMV
  have hball : ball z ρ ⊆ unitDisc ∩ (unitDisc ∩ ball ζ (4 * ρ)) := by
    intro u hu
    have hu1 := hsub (ball_subset_closedBall hu)
    refine ⟨hu1, hu1, ?_⟩
    rw [mem_ball, dist_eq_norm] at hu ⊢
    have := norm_sub_le_norm_sub_add_norm_sub u z ζ
    linarith
  have hpt : ∀ u ∈ ball z ρ, ENNReal.ofReal (‖deriv (deriv f) u / deriv f u‖ ^ 2) ≤
      ENNReal.ofReal ρ⁻¹ *
        ENNReal.ofReal (‖deriv (deriv f) u / deriv f u‖ ^ 2 * (1 - ‖u‖ ^ 2)) := by
    intro u hu
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hρ0.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mem_ball, dist_eq_norm] at hu
    have t := norm_le_insert' u z
    have hu1 : ‖u‖ < 1 := by linarith
    have h1 : ρ ≤ 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
    have h2 : 1 ≤ ρ⁻¹ * (1 - ‖u‖ ^ 2) := by
      rw [← div_eq_inv_mul, le_div_iff₀ hρ0]
      linarith
    have h3 := sq_nonneg ‖deriv (deriv f) u / deriv f u‖
    nlinarith
  have hint : (∫⁻ u in ball z ρ, ENNReal.ofReal (‖deriv (deriv f) u / deriv f u‖ ^ 2)) ≤
      ENNReal.ofReal ρ⁻¹ * derivCarlesonMeasure (fun z => deriv (deriv f) z / deriv f z)
        (unitDisc ∩ ball ζ (4 * ρ)) := by
    rw [s07b_fkph_c_muE _
      (show MeasurableSet (unitDisc ∩ ball ζ (4 * ρ)) from measurableSet_ball.inter measurableSet_ball)]
    calc (∫⁻ u in ball z ρ, ENNReal.ofReal (‖deriv (deriv f) u / deriv f u‖ ^ 2))
        ≤ ∫⁻ u in ball z ρ, ENNReal.ofReal ρ⁻¹ *
            ENNReal.ofReal (‖deriv (deriv f) u / deriv f u‖ ^ 2 * (1 - ‖u‖ ^ 2)) :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = ENNReal.ofReal ρ⁻¹ * ∫⁻ u in ball z ρ,
            ENNReal.ofReal (‖deriv (deriv f) u / deriv f u‖ ^ 2 * (1 - ‖u‖ ^ 2)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono_set hball)
  have hCMz := hCM ζ hζs (4 * ρ) (by positivity) (by rw [hρ]; linarith)
  have hcomb := hMV.trans (hint.trans (mul_le_mul' le_rfl hCMz))
  rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (inv_nonneg.mpr hρ0.le),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hcomb
  have e : ρ⁻¹ * (ε ^ 2 / 32 * (4 * ρ)) = ε ^ 2 / 8 := by field_simp; ring
  rw [e] at hcomb
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ‖deriv (deriv f) z / deriv f z‖ := ⟨_, rfl⟩
  rw [← hP] at hcomb ⊢
  have hP0 : 0 ≤ P := by rw [hP]; exact norm_nonneg _
  have hpi := mul_le_mul_of_nonneg_left Real.pi_gt_three.le (mul_nonneg (sq_nonneg P) (sq_nonneg ρ))
  have hPd : (2 * d * P) ^ 2 ≤ ε ^ 2 := by
    rw [hρ] at hcomb hpi
    nlinarith
  have hx : 2 * d * P ≤ ε := by
    by_contra hc
    push Not at hc
    nlinarith
  have h1 : 1 - ‖z‖ ^ 2 ≤ 2 * d := by rw [hd]; nlinarith
  calc (1 - ‖z‖ ^ 2) * P ≤ 2 * d * P := mul_le_mul_of_nonneg_right h1 hP0
    _ ≤ ε := hx

/-- T1 helper: measurability of `z ↦ ∫_{D(z, 3(1−|z|)/4)} G`. -/
theorem s07b_fkph_c_Imeas {G : ℂ → ℝ≥0∞} (hG : Measurable G) :
    Measurable fun z : ℂ => ∫⁻ u in ball z (3 * (1 - ‖z‖) / 4), G u := by
  obtain ⟨S, hS⟩ : ∃ S : Set (ℂ × ℂ), S = {p | dist p.2 p.1 < 3 * (1 - ‖p.1‖) / 4} := ⟨_, rfl⟩
  have hmemS : ∀ z w, (z, w) ∈ S ↔ dist w z < 3 * (1 - ‖z‖) / 4 := by
    intro z w
    rw [hS]
    rfl
  have hSm : MeasurableSet S := by
    rw [hS]
    exact (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet
  have hIeq : ∀ z, (∫⁻ u in ball z (3 * (1 - ‖z‖) / 4), G u) =
      ∫⁻ u, S.indicator (fun q => G q.2) (z, u) := by
    intro z
    rw [← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun w => ?_
    by_cases hw : (z, w) ∈ S
    · rw [Set.indicator_of_mem hw,
        Set.indicator_of_mem (show w ∈ ball z (3 * (1 - ‖z‖) / 4) from (hmemS z w).1 hw)]
    · rw [Set.indicator_of_notMem hw,
        Set.indicator_of_notMem
          (show w ∉ ball z (3 * (1 - ‖z‖) / 4) from fun h => hw ((hmemS z w).2 h))]
  have h := Measurable.lintegral_prod_right' (ν := (volume : Measure ℂ))
    ((hG.comp measurable_snd).indicator hSm)
  have he : (fun z : ℂ => ∫⁻ u in ball z (3 * (1 - ‖z‖) / 4), G u) =
      fun z => ∫⁻ u, S.indicator (fun q => G q.2) (z, u) := funext hIeq
  rw [he]
  exact h

/-- T1 helper: the tail `μ(𝔻 ∩ {|u| > 1 − 1/(N+1)})` of a finite measure is eventually small. -/
theorem s07b_fkph_c_tail {μ : Measure ℂ} (hμ : μ unitDisc ≠ ⊤) {c : ℝ≥0∞} (hc : 0 < c) :
    ∃ N : ℕ, μ (unitDisc ∩ {u : ℂ | 1 - 1 / ((N : ℝ) + 1) < ‖u‖}) < c := by
  obtain ⟨T, hT⟩ : ∃ T : ℕ → Set ℂ,
      T = fun n : ℕ => unitDisc ∩ {u : ℂ | 1 - 1 / ((n : ℝ) + 1) < ‖u‖} := ⟨_, rfl⟩
  have hTm : ∀ n, MeasurableSet (T n) := by
    intro n
    rw [hT]
    exact measurableSet_ball.inter (measurableSet_lt measurable_const measurable_norm)
  have hTa : Antitone T := by
    intro m n hmn u hu
    simp only [hT] at hu ⊢
    refine ⟨hu.1, ?_⟩
    show 1 - 1 / ((m : ℝ) + 1) < ‖u‖
    have h2 : 1 - 1 / ((n : ℝ) + 1) < ‖u‖ := hu.2
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) hmn'
    linarith
  have hTi : (⋂ n, T n) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro u hu
    rw [Set.mem_iInter] at hu
    have h0 := hu 0
    simp only [hT] at h0
    have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp h0.1
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < 1 - ‖u‖ by linarith)
    have hn' := hu n
    simp only [hT] at hn'
    have h2 : 1 - 1 / ((n : ℝ) + 1) < ‖u‖ := hn'.2
    linarith
  have hT0 : μ (T 0) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hμ (measure_mono ?_)
    intro u hu
    simp only [hT] at hu
    exact hu.1
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hTm n).nullMeasurableSet) hTa
    ⟨0, hT0⟩
  rw [hTi, measure_empty] at hlim
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hc)).exists
  refine ⟨N, ?_⟩
  have h : μ (T N) < c := hN
  rw [hT] at h
  exact h

/-- T1 helper: `a(z)² / (1 − |z|²) ≤ 200 (1 − |z|)⁻² I` for the square-root majorant. -/
theorem s07b_fkph_c_majsq {z : ℂ} (hz : z ∈ unitDisc) (I : ℝ≥0∞) :
    ENNReal.ofReal (Real.sqrt (200 * I.toReal / (1 - ‖z‖)) ^ 2 / (1 - ‖z‖ ^ 2)) ≤
      ENNReal.ofReal 200 * (ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) * I) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hd0 : 0 < 1 - ‖z‖ := by linarith
  have hJ0 : 0 ≤ I.toReal := ENNReal.toReal_nonneg
  rw [Real.sq_sqrt (div_nonneg (by linarith) hd0.le)]
  have hle : 1 - ‖z‖ ≤ 1 - ‖z‖ ^ 2 := by
    have e : 1 - ‖z‖ ^ 2 = (1 - ‖z‖) + ‖z‖ * (1 - ‖z‖) := by ring
    have := mul_nonneg (norm_nonneg z) hd0.le
    linarith
  have hreal : 200 * I.toReal / (1 - ‖z‖) / (1 - ‖z‖ ^ 2) ≤
      200 * (((1 - ‖z‖) ^ 2)⁻¹ * I.toReal) := by
    calc 200 * I.toReal / (1 - ‖z‖) / (1 - ‖z‖ ^ 2) ≤ 200 * I.toReal / (1 - ‖z‖) / (1 - ‖z‖) :=
          div_le_div_of_nonneg_left (div_nonneg (by linarith) hd0.le) hd0 hle
      _ = 200 * (((1 - ‖z‖) ^ 2)⁻¹ * I.toReal) := by
          field_simp
  calc ENNReal.ofReal (200 * I.toReal / (1 - ‖z‖) / (1 - ‖z‖ ^ 2))
      ≤ ENNReal.ofReal (200 * (((1 - ‖z‖) ^ 2)⁻¹ * I.toReal)) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal 200 * (ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) * ENNReal.ofReal I.toReal) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 200),
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((1 - ‖z‖) ^ 2)⁻¹)]
    _ ≤ _ := mul_le_mul' le_rfl (mul_le_mul' le_rfl ENNReal.ofReal_toReal_le)

/-- T1 helper: the pointwise square-root majorant (sub-mean value on `D(w, (1−|z|)/4)`). -/
theorem s07b_fkph_c_majpt {φ : ℂ → ℂ} (hφd : DifferentiableOn ℂ φ unitDisc) {G : ℂ → ℝ≥0∞}
    {t s : ℝ} (hs : s = (2 * t + 1) / 3)
    (hGeq : ∀ u, t < ‖u‖ → G u = ENNReal.ofReal (‖φ u‖ ^ 2 * (1 - ‖u‖ ^ 2)))
    {z w : ℂ} (hz : z ∈ unitDisc) (hfin : (∫⁻ u in ball z (3 * (1 - ‖z‖) / 4), G u) ≠ ⊤)
    (hw : w ∈ ball z ((1 - ‖z‖) / 2)) (hsw : s < ‖w‖) :
    ‖w‖ * ((1 - ‖w‖ ^ 2) * ‖φ w‖) ≤
      Real.sqrt (200 * (∫⁻ u in ball z (3 * (1 - ‖z‖) / 4), G u).toReal / (1 - ‖z‖)) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = 1 - ‖z‖ := ⟨_, rfl⟩
  have hd0 : 0 < d := by linarith
  rw [mem_ball, dist_eq_norm] at hw
  have tw := norm_le_insert' w z
  have hds : d < 2 * (1 - s) := by linarith only [tw, hw, hsw, hd]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = d / 4 := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hsub : closedBall w ρ ⊆ unitDisc := by
    intro u hu
    show u ∈ Metric.ball (0 : ℂ) 1
    rw [mem_ball_zero_iff]
    rw [mem_closedBall, dist_eq_norm] at hu
    have := norm_le_insert' u w
    linarith only [this, hu, tw, hw, hρ, hd, hd0]
  have hMV := s02_sw_meanValue hρ0 (hφd.mono hsub)
  beta_reduce at hMV
  have hpt : ∀ u ∈ ball w ρ, ENNReal.ofReal (‖φ u‖ ^ 2) ≤ ENNReal.ofReal ρ⁻¹ * G u := by
    intro u hu
    rw [mem_ball, dist_eq_norm] at hu
    have t1 := norm_le_insert' u w
    have t2 := norm_le_insert' w u
    rw [norm_sub_rev w u] at t2
    have htu : t < ‖u‖ := by linarith only [t2, hu, hsw, hρ, hds, hs]
    have hu1 : ‖u‖ < 1 := by linarith only [t1, hu, tw, hw, hρ, hd, hd0]
    have hu2 : ρ ≤ 1 - ‖u‖ := by linarith only [t1, hu, tw, hw, hρ, hd]
    have h1 : ρ ≤ 1 - ‖u‖ ^ 2 := by
      have e : 1 - ‖u‖ ^ 2 = (1 - ‖u‖) + ‖u‖ * (1 - ‖u‖) := by ring
      have := mul_nonneg (norm_nonneg u) (sub_nonneg.mpr hu1.le)
      linarith
    have h2 : 1 ≤ ρ⁻¹ * (1 - ‖u‖ ^ 2) := by
      rw [← div_eq_inv_mul, le_div_iff₀ hρ0]
      linarith
    rw [hGeq u htu, ← ENNReal.ofReal_mul (inv_nonneg.mpr hρ0.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h3 := sq_nonneg ‖φ u‖
    calc ‖φ u‖ ^ 2 = ‖φ u‖ ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖φ u‖ ^ 2 * (ρ⁻¹ * (1 - ‖u‖ ^ 2)) := mul_le_mul_of_nonneg_left h2 h3
      _ = ρ⁻¹ * (‖φ u‖ ^ 2 * (1 - ‖u‖ ^ 2)) := by ring
  have hint : (∫⁻ u in ball w ρ, ENNReal.ofReal (‖φ u‖ ^ 2)) ≤
      ENNReal.ofReal ρ⁻¹ * ∫⁻ u in ball z (3 * (1 - ‖z‖) / 4), G u := by
    calc (∫⁻ u in ball w ρ, ENNReal.ofReal (‖φ u‖ ^ 2))
        ≤ ∫⁻ u in ball w ρ, ENNReal.ofReal ρ⁻¹ * G u := setLIntegral_mono' measurableSet_ball hpt
      _ = ENNReal.ofReal ρ⁻¹ * ∫⁻ u in ball w ρ, G u :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by
          refine mul_le_mul' le_rfl (lintegral_mono_set ?_)
          intro u hu
          rw [mem_ball, dist_eq_norm] at hu ⊢
          have := norm_sub_le_norm_sub_add_norm_sub u w z
          linarith only [this, hu, hw, hρ, hd]
  have hcomb := hMV.trans hint
  obtain ⟨J, hJ⟩ : ∃ J : ℝ, J = (∫⁻ u in ball z (3 * (1 - ‖z‖) / 4), G u).toReal := ⟨_, rfl⟩
  have hIJ : (∫⁻ u in ball z (3 * (1 - ‖z‖) / 4), G u) = ENNReal.ofReal J := by
    rw [hJ, ENNReal.ofReal_toReal hfin]
  have hJ0 : 0 ≤ J := by rw [hJ]; exact ENNReal.toReal_nonneg
  rw [hIJ, ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (inv_nonneg.mpr hρ0.le),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (inv_nonneg.mpr hρ0.le) hJ0)] at hcomb
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ‖φ w‖ := ⟨_, rfl⟩
  rw [← hP] at hcomb
  have hP0 : 0 ≤ P := by rw [hP]; exact norm_nonneg _
  have hρJ : P ^ 2 * (π * ρ ^ 2) * ρ ≤ J := by
    have h := mul_le_mul_of_nonneg_right hcomb hρ0.le
    rw [show ρ⁻¹ * J * ρ = J by field_simp] at h
    exact h
  have hw1 : ‖w‖ < 1 := by linarith only [tw, hw, hd, hd0]
  have tz := norm_le_insert' z w
  rw [norm_sub_rev z w] at tz
  have ew : 1 - ‖w‖ ^ 2 = (1 - ‖w‖) * (1 + ‖w‖) := by ring
  have hwq0 : 0 ≤ 1 - ‖w‖ ^ 2 := by
    rw [ew]
    exact mul_nonneg (by linarith) (by positivity)
  have e2 : 1 - ‖w‖ ^ 2 ≤ 3 * d := by
    have h1w : 1 - ‖w‖ ≤ 3 * d / 2 := by linarith only [tz, hw, hd]
    have hle : (1 - ‖w‖) * (1 + ‖w‖) ≤ (3 * d / 2) * 2 :=
      mul_le_mul h1w (by linarith) (by positivity) (by positivity)
    linarith
  have hx0 : 0 ≤ ‖w‖ * ((1 - ‖w‖ ^ 2) * P) := mul_nonneg (norm_nonneg _) (mul_nonneg hwq0 hP0)
  have hx1 : ‖w‖ * ((1 - ‖w‖ ^ 2) * P) ≤ 3 * d * P := by
    calc ‖w‖ * ((1 - ‖w‖ ^ 2) * P) ≤ 1 * ((1 - ‖w‖ ^ 2) * P) :=
          mul_le_mul_of_nonneg_right hw1.le (mul_nonneg hwq0 hP0)
      _ ≤ 3 * d * P := by rw [one_mul]; exact mul_le_mul_of_nonneg_right e2 hP0
  rw [← hP, ← hJ, ← hd, Real.le_sqrt hx0 (div_nonneg (by linarith) hd0.le), le_div_iff₀ hd0]
  have hsq : (‖w‖ * ((1 - ‖w‖ ^ 2) * P)) ^ 2 ≤ (3 * d * P) ^ 2 := pow_le_pow_left₀ hx0 hx1 2
  have hsq' := mul_le_mul_of_nonneg_right hsq hd0.le
  have e4 : (3 * d * P) ^ 2 * d = 9 * (P ^ 2 * d ^ 3) := by ring
  rw [e4] at hsq'
  have hpi : 3 * (P ^ 2 * d ^ 3) ≤ π * (P ^ 2 * d ^ 3) :=
    mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by positivity)
  rw [hρ] at hρJ
  have e3 : P ^ 2 * (π * (d / 4) ^ 2) * (d / 4) = π * (P ^ 2 * d ^ 3) / 64 := by ring
  rw [e3] at hρJ
  have hPd : 0 ≤ P ^ 2 * d ^ 3 := by positivity
  linarith

/-- T1 block C1 (Whitney-sup majorant): for `log f' ∈ VMOA`, the Becker dilatation
`|w|(1 − |w|²)|f''/f'(w)|` on the Whitney disc `D(z, (1−|z|)/2)`, restricted to `s < |w|`, has a measurable
majorant `a(z)` whose Carleson measure `a²/(1−|z|²) dA` has norm `≤ ε` (sub-mean value on `D(w, (1−|z|)/4)`,
the Whitney–Fubini swap `s02_sw_whitney` with radius `3/4`, then CM₀ for small boxes and the tail
`μ(𝔻 ∩ {|w| > s'}) → 0` for large ones). -/
theorem s07b_fkph_c_major {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (hv : LogDerivVMOA f) :
    ∀ ε : ℝ, 0 < ε → ∀ r : ℝ, r < 1 → ∃ (s : ℝ) (a : ℂ → ℝ), r ≤ s ∧ s < 1 ∧ Measurable a ∧
      (∀ z, 0 ≤ a z) ∧
      (∀ z ∈ unitDisc, ∀ w ∈ ball z ((1 - ‖z‖) / 2), s < ‖w‖ →
        ‖w‖ * ((1 - ‖w‖ ^ 2) * ‖deriv (deriv f) w / deriv f w‖) ≤ a z) ∧
      ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ ρ : ℝ, 0 < ρ → ρ < 2 →
        ∫⁻ z in unitDisc ∩ ball ζ ρ, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
          ≤ ENNReal.ofReal (ε * ρ) := by
  intro ε hε r hr
  obtain ⟨hφd, -⟩ := s02_sw_logDeriv hf
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure ℂ,
      μ = derivCarlesonMeasure (fun z => deriv (deriv f) z / deriv f z) := ⟨_, rfl⟩
  have hv' : IsVanishingCarlesonDisk μ := by rw [hμ]; exact hv
  have hμE : ∀ E : Set ℂ, MeasurableSet E → μ E =
      ∫⁻ u in unitDisc ∩ E, ENNReal.ofReal (‖deriv (deriv f) u / deriv f u‖ ^ 2 * (1 - ‖u‖ ^ 2)) := by
    intro E hE
    rw [hμ]
    exact s07b_fkph_c_muE _ hE
  have hFm := s07b_fkph_c_Fmeas f
  obtain ⟨δ, hδ, hCM⟩ := hv'.2 (ε / 36000) (by positivity)
  have hμfin : μ unitDisc ≠ ⊤ := s02_cm_total hv'.1
  have htarget : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 36000 * δ) := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨N, hN⟩ := s07b_fkph_c_tail hμfin htarget
  -- the radii
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = max (1 - 1 / ((N : ℝ) + 1)) (max r 0) := ⟨_, rfl⟩
  have htN : 1 - 1 / ((N : ℝ) + 1) ≤ t := by rw [ht]; exact le_max_left _ _
  have htr : r ≤ t := by rw [ht]; exact (le_max_left r 0).trans (le_max_right _ _)
  have ht1 : t < 1 := by
    rw [ht]
    refine max_lt ?_ (max_lt hr one_pos)
    have : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (2 * t + 1) / 3 := ⟨_, rfl⟩
  -- the cut-off density `G = 1_{|u| > t} |φ|²(1 − |u|²)`
  have hmeasT : MeasurableSet {u : ℂ | t < ‖u‖} :=
    measurableSet_lt measurable_const measurable_norm
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℝ≥0∞, G = {u : ℂ | t < ‖u‖}.indicator
      (fun u => ENNReal.ofReal (‖deriv (deriv f) u / deriv f u‖ ^ 2 * (1 - ‖u‖ ^ 2))) := ⟨_, rfl⟩
  have hGm : Measurable G := by
    rw [hG]
    exact hFm.indicator hmeasT
  have hGle : ∀ u, G u ≤
      ENNReal.ofReal (‖deriv (deriv f) u / deriv f u‖ ^ 2 * (1 - ‖u‖ ^ 2)) := by
    intro u
    rw [hG]
    by_cases hu : u ∈ {u : ℂ | t < ‖u‖}
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu]
      exact bot_le
  have hGeq : ∀ u, t < ‖u‖ → G u =
      ENNReal.ofReal (‖deriv (deriv f) u / deriv f u‖ ^ 2 * (1 - ‖u‖ ^ 2)) := by
    intro u hu
    rw [hG]
    exact Set.indicator_of_mem (show u ∈ {u : ℂ | t < ‖u‖} from hu) _
  have hIm := s07b_fkph_c_Imeas hGm
  have hIfin : ∀ z ∈ unitDisc, (∫⁻ u in ball z (3 * (1 - ‖z‖) / 4), G u) ≠ ⊤ := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    refine ne_top_of_le_ne_top hμfin ?_
    rw [hμE unitDisc (show MeasurableSet unitDisc from measurableSet_ball)]
    calc (∫⁻ u in ball z (3 * (1 - ‖z‖) / 4), G u)
        ≤ ∫⁻ u in ball z (3 * (1 - ‖z‖) / 4),
            ENNReal.ofReal (‖deriv (deriv f) u / deriv f u‖ ^ 2 * (1 - ‖u‖ ^ 2)) :=
          lintegral_mono fun u => hGle u
      _ ≤ _ := by
          refine lintegral_mono_set ?_
          intro u hu
          rw [mem_ball, dist_eq_norm] at hu
          have := norm_le_insert' u z
          have hu1 : u ∈ unitDisc := by
            show u ∈ Metric.ball (0 : ℂ) 1
            exact mem_ball_zero_iff.mpr (by linarith only [this, hu, hz1])
          exact ⟨hu1, hu1⟩
  obtain ⟨a, ha⟩ : ∃ a : ℂ → ℝ, a = fun z =>
      Real.sqrt (200 * (∫⁻ u in ball z (3 * (1 - ‖z‖) / 4), G u).toReal / (1 - ‖z‖)) := ⟨_, rfl⟩
  have ham : Measurable a := by
    rw [ha]
    exact ((hIm.ennreal_toReal.const_mul 200).div (measurable_const.sub measurable_norm)).sqrt
  refine ⟨s, a, by rw [hs]; linarith, by rw [hs]; linarith, ham,
    fun z => by rw [ha]; exact Real.sqrt_nonneg _, ?_, ?_⟩
  · -- pointwise majorant
    intro z hz w hw hsw
    rw [ha]
    exact s07b_fkph_c_majpt (φ := fun z => deriv (deriv f) z / deriv f z) hφd hs hGeq hz
      (hIfin z hz) hw hsw
  · -- the Carleson bound
    intro ζ hζ ρ hρ0 hρ2
    have hstep1 : (∫⁻ z in unitDisc ∩ ball ζ ρ, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))) ≤
        ENNReal.ofReal 200 * ∫⁻ z in unitDisc ∩ ball ζ ρ, ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) *
          ∫⁻ u in ball z (3 * (1 - ‖z‖) / 4), G u := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' (measurableSet_ball.inter measurableSet_ball) fun z hz => ?_
      rw [ha]
      exact s07b_fkph_c_majsq hz.1 _
    have hstep2 := s07b_fkph_c_whit hGm hζ ρ
    have hstep3 : (∫⁻ u in unitDisc ∩ ball ζ (2 * ρ), G u) ≤ ENNReal.ofReal (ε * ρ / 18000) := by
      rcases lt_or_ge (2 * ρ) δ with hsm | hlg
      · have h := hCM ζ hζ (2 * ρ) (by positivity) hsm
        rw [hμE _ (show MeasurableSet (unitDisc ∩ ball ζ (2 * ρ)) from
          measurableSet_ball.inter measurableSet_ball)] at h
        calc (∫⁻ u in unitDisc ∩ ball ζ (2 * ρ), G u)
            ≤ ∫⁻ u in unitDisc ∩ ball ζ (2 * ρ),
                ENNReal.ofReal (‖deriv (deriv f) u / deriv f u‖ ^ 2 * (1 - ‖u‖ ^ 2)) :=
              lintegral_mono fun u => hGle u
          _ ≤ ∫⁻ u in unitDisc ∩ (unitDisc ∩ ball ζ (2 * ρ)),
                ENNReal.ofReal (‖deriv (deriv f) u / deriv f u‖ ^ 2 * (1 - ‖u‖ ^ 2)) :=
              lintegral_mono_set fun u hu => ⟨hu.1, hu⟩
          _ ≤ ENNReal.ofReal (ε / 36000 * (2 * ρ)) := h
          _ = ENNReal.ofReal (ε * ρ / 18000) := by congr 1; ring
      · have hEm : MeasurableSet (unitDisc ∩ {u : ℂ | 1 - 1 / ((N : ℝ) + 1) < ‖u‖}) :=
          measurableSet_ball.inter (measurableSet_lt measurable_const measurable_norm)
        have hTN := hμE _ hEm
        calc (∫⁻ u in unitDisc ∩ ball ζ (2 * ρ), G u) ≤ ∫⁻ u in unitDisc, G u :=
              lintegral_mono_set Set.inter_subset_left
          _ = ∫⁻ u in {u : ℂ | t < ‖u‖} ∩ unitDisc,
                ENNReal.ofReal (‖deriv (deriv f) u / deriv f u‖ ^ 2 * (1 - ‖u‖ ^ 2)) := by
              rw [hG, lintegral_indicator hmeasT, Measure.restrict_restrict hmeasT]
          _ ≤ ∫⁻ u in unitDisc ∩ (unitDisc ∩ {u : ℂ | 1 - 1 / ((N : ℝ) + 1) < ‖u‖}),
                ENNReal.ofReal (‖deriv (deriv f) u / deriv f u‖ ^ 2 * (1 - ‖u‖ ^ 2)) := by
              refine lintegral_mono_set ?_
              intro u hu
              have hu1 : t < ‖u‖ := hu.1
              refine ⟨hu.2, hu.2, ?_⟩
              show 1 - 1 / ((N : ℝ) + 1) < ‖u‖
              linarith
          _ = μ (unitDisc ∩ {u : ℂ | 1 - 1 / ((N : ℝ) + 1) < ‖u‖}) := hTN.symm
          _ ≤ ENNReal.ofReal (ε / 36000 * δ) := hN.le
          _ ≤ ENNReal.ofReal (ε * ρ / 18000) := by
              refine ENNReal.ofReal_le_ofReal ?_
              have := mul_le_mul_of_nonneg_left hlg hε.le
              linarith
    calc (∫⁻ z in unitDisc ∩ ball ζ ρ, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)))
        ≤ ENNReal.ofReal 200 * (ENNReal.ofReal 90 * ∫⁻ u in unitDisc ∩ ball ζ (2 * ρ), G u) :=
          hstep1.trans (mul_le_mul' le_rfl hstep2)
      _ ≤ ENNReal.ofReal 200 * (ENNReal.ofReal 90 * ENNReal.ofReal (ε * ρ / 18000)) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl hstep3)
      _ = ENNReal.ofReal (ε * ρ) := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 90),
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 200)]
          congr 1
          ring

/-- T1 block C1 (derivative of the Becker map `B(z) = f(z) + (1/z̄ − z) f'(z)`, written at the inner point
`z`): `B` is `C¹` on `𝔻 ∖ {0}` with `∂B = (1/z̄ − z) f''(z)` and `∂̄B = −f'(z)/z̄²`. -/
theorem s07b_fkph_c_dB {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) {z : ℂ} (hz : z ∈ unitDisc)
    (hz0 : z ≠ 0) :
    ContDiffAt ℝ 1 (fun w => f w + ((conj w)⁻¹ - w) * deriv f w) z ∧
      ∀ v : ℂ, fderiv ℝ (fun w => f w + ((conj w)⁻¹ - w) * deriv f w) z v =
        ((conj z)⁻¹ - z) * deriv (deriv f) z * v - ((conj z)⁻¹) ^ 2 * deriv f z * conj v := by
  have hzD : unitDisc ∈ 𝓝 z := isOpen_ball.mem_nhds hz
  have hc : conj z ≠ 0 := by rw [map_ne_zero]; exact hz0
  have hdf : DifferentiableOn ℂ (deriv f) unitDisc := hf.deriv isOpen_ball
  have h1 : HasDerivAt f (deriv f z) z := ((hf z hz).differentiableAt hzD).hasDerivAt
  have h2 : HasDerivAt (deriv f) (deriv (deriv f) z) z :=
    ((hdf z hz).differentiableAt hzD).hasDerivAt
  have hconj : HasFDerivAt (fun w : ℂ => conj w) (Complex.conjCLE : ℂ →L[ℝ] ℂ) z := by
    exact Complex.conjCLE.hasFDerivAt
  have hinv : HasFDerivAt (fun w : ℂ => (conj w)⁻¹)
      (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-((conj z) ^ 2)⁻¹)).restrictScalars ℝ).comp
        (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z :=
    ((hasDerivAt_inv hc).hasFDerivAt.restrictScalars ℝ).comp z hconj
  have hg : HasFDerivAt (fun w : ℂ => (conj w)⁻¹ - w)
      ((((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-((conj z) ^ 2)⁻¹)).restrictScalars ℝ).comp
        (Complex.conjCLE : ℂ →L[ℝ] ℂ)) - ContinuousLinearMap.id ℝ ℂ) z :=
    hinv.sub (hasFDerivAt_id z)
  have hB : HasFDerivAt (fun w => f w + ((conj w)⁻¹ - w) * deriv f w)
      (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f z)).restrictScalars ℝ) +
        (((conj z)⁻¹ - z) •
            ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv (deriv f) z)).restrictScalars ℝ) +
          deriv f z • ((((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
            (-((conj z) ^ 2)⁻¹)).restrictScalars ℝ).comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)) -
              ContinuousLinearMap.id ℝ ℂ))) z := by
    exact (h1.hasFDerivAt.restrictScalars ℝ).add (hg.fun_mul (h2.hasFDerivAt.restrictScalars ℝ))
  refine ⟨?_, ?_⟩
  · have c1 : ContDiffAt ℝ 1 f z :=
      ((hf.contDiffOn isOpen_ball).contDiffAt hzD).restrict_scalars ℝ
    have c2 : ContDiffAt ℝ 1 (deriv f) z :=
      ((hdf.contDiffOn isOpen_ball).contDiffAt hzD).restrict_scalars ℝ
    have c3 : ContDiffAt ℝ 1 (fun w : ℂ => conj w) z := by
      exact Complex.conjCLE.contDiff.contDiffAt
    have c4 : ContDiffAt ℝ 1 (fun w : ℂ => (conj w)⁻¹) z := by
      exact c3.inv hc
    exact c1.add ((c4.sub contDiffAt_id).mul c2)
  · intro v
    rw [hB.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, inv_pow]
    all_goals ring

/-- T1 block C1 (dilatation of `Φ = ι ∘ g⁻¹ ∘ B`, `ι w = 1/w̄`): if `B(z) ∈ Ωs` and `Φ` agrees near `z`
with `w ↦ conj (g⁻¹(B w))⁻¹`, then `Φ` is `C¹` at `z`, `∂Φ(z) ≠ 0`, and
`μ_Φ(z) = −(1 − |z|²) z · conj (f''/f'(z))` (so `|μ_Φ(z)| = |z|(1−|z|²)|f''/f'(z)|`). -/
theorem s07b_fkph_c_dil {Ω Ωs : Set ℂ} {f g Φ : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (hg : IsConformalOnto g unitDiscExterior Ωs) {z : ℂ} (hz : z ∈ unitDisc) (hz0 : z ≠ 0)
    (hB : f z + ((conj z)⁻¹ - z) * deriv f z ∈ Ωs)
    (hΦ : ∀ᶠ w in 𝓝 z, Φ w =
      conj ((Function.invFunOn g unitDiscExterior (f w + ((conj w)⁻¹ - w) * deriv f w))⁻¹)) :
    ContDiffAt ℝ 1 Φ z ∧ LiZhongQC.dz Φ z ≠ 0 ∧
      LiZhongQC.complexDilatation Φ z =
        -(((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * z * conj (deriv (deriv f) z / deriv f z)) := by
  obtain ⟨hC, hD⟩ := s07b_fkph_c_dB hf.1 hz hz0
  have hUo : IsOpen unitDiscExterior := by
    show IsOpen {w : ℂ | 1 < ‖w‖}
    exact isOpen_lt continuous_const continuous_norm
  have hR := RMT.differentiableOn_invFunOn_of_injOn hUo hg.1 hg.2.1
  rw [hg.2.2] at hR
  obtain ⟨hΩo, hGd⟩ := hR
  set y := f z + ((conj z)⁻¹ - z) * deriv f z with hy
  have hyim : y ∈ g '' unitDiscExterior := by rw [hg.2.2]; exact hB
  have hu : Function.invFunOn g unitDiscExterior y ∈ unitDiscExterior := Function.invFunOn_mem hyim
  have hu1 : 1 < ‖Function.invFunOn g unitDiscExterior y‖ := hu
  have hu0 : Function.invFunOn g unitDiscExterior y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu1
    linarith
  have hyN : Ωs ∈ 𝓝 y := hΩo.mem_nhds hB
  have hGy : HasDerivAt (Function.invFunOn g unitDiscExterior)
      (deriv (Function.invFunOn g unitDiscExterior) y) y :=
    ((hGd y hB).differentiableAt hyN).hasDerivAt
  -- `G'(y) ≠ 0` from `g ∘ G = id` near `y`
  have hG'0 : deriv (Function.invFunOn g unitDiscExterior) y ≠ 0 := by
    have hgu : HasDerivAt g (deriv g (Function.invFunOn g unitDiscExterior y))
        (Function.invFunOn g unitDiscExterior y) :=
      ((hg.1 _ hu).differentiableAt (hUo.mem_nhds hu)).hasDerivAt
    have h1 := hgu.comp y hGy
    have heq : (g ∘ Function.invFunOn g unitDiscExterior) =ᶠ[𝓝 y] id := by
      refine Filter.eventually_of_mem hyN ?_
      intro y' hy'
      have hy'im : y' ∈ g '' unitDiscExterior := by rw [hg.2.2]; exact hy'
      exact Function.invFunOn_eq hy'im
    have h2 := (hasDerivAt_id y).congr_of_eventuallyEq heq
    have h3 := h1.unique h2
    intro h0
    rw [h0, mul_zero] at h3
    exact zero_ne_one h3
  obtain ⟨h', hh'⟩ : ∃ h' : ℂ, h' = -deriv (Function.invFunOn g unitDiscExterior) y /
      Function.invFunOn g unitDiscExterior y ^ 2 := ⟨_, rfl⟩
  have hh'0 : h' ≠ 0 := by
    rw [hh']
    exact div_ne_zero (neg_ne_zero.mpr hG'0) (pow_ne_zero 2 hu0)
  have hH : HasDerivAt (fun y' => (Function.invFunOn g unitDiscExterior y')⁻¹) h' y := by
    rw [hh']
    exact hGy.inv hu0
  have hBd : HasFDerivAt (fun w => f w + ((conj w)⁻¹ - w) * deriv f w)
      (fderiv ℝ (fun w => f w + ((conj w)⁻¹ - w) * deriv f w) z) z :=
    (hC.differentiableAt one_ne_zero).hasFDerivAt
  have hHB : HasFDerivAt
      (fun w => (Function.invFunOn g unitDiscExterior (f w + ((conj w)⁻¹ - w) * deriv f w))⁻¹)
      (((ContinuousLinearMap.toSpanSingleton ℂ h').restrictScalars ℝ).comp
          (fderiv ℝ (fun w => f w + ((conj w)⁻¹ - w) * deriv f w) z)) z :=
    HasFDerivAt.comp (g := fun y' => (Function.invFunOn g unitDiscExterior y')⁻¹)
      (f := fun w => f w + ((conj w)⁻¹ - w) * deriv f w) z (hH.hasFDerivAt.restrictScalars ℝ) hBd
  have hconj : HasFDerivAt (fun x : ℂ => conj x) (Complex.conjCLE : ℂ →L[ℝ] ℂ)
      ((Function.invFunOn g unitDiscExterior (f z + ((conj z)⁻¹ - z) * deriv f z))⁻¹) := by
    exact Complex.conjCLE.hasFDerivAt
  have hΨ : HasFDerivAt
      (fun w => conj ((Function.invFunOn g unitDiscExterior (f w + ((conj w)⁻¹ - w) * deriv f w))⁻¹))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
        (((ContinuousLinearMap.toSpanSingleton ℂ h').restrictScalars ℝ).comp
          (fderiv ℝ (fun w => f w + ((conj w)⁻¹ - w) * deriv f w) z))) z :=
    HasFDerivAt.comp (g := fun x : ℂ => conj x)
      (f := fun w => (Function.invFunOn g unitDiscExterior (f w + ((conj w)⁻¹ - w) * deriv f w))⁻¹)
      z hconj hHB
  have hΦd := hΨ.congr_of_eventuallyEq hΦ
  have hDΦ : ∀ v : ℂ, fderiv ℝ Φ z v =
      conj h' * conj (((conj z)⁻¹ - z) * deriv (deriv f) z) * conj v -
        conj h' * conj (((conj z)⁻¹) ^ 2 * deriv f z) * v := by
    intro v
    rw [hΦd.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, hD v, map_mul, map_sub,
      Complex.conj_conj]
    all_goals ring
  have hf'0 : deriv f z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz
  have hc : conj z ≠ 0 := by rw [map_ne_zero]; exact hz0
  have hb0 : conj h' * conj (((conj z)⁻¹) ^ 2 * deriv f z) ≠ 0 := by
    refine mul_ne_zero ((map_ne_zero _).mpr hh'0) ((map_ne_zero _).mpr ?_)
    exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hc)) hf'0
  have hdz : LiZhongQC.dz Φ z = -(conj h' * conj (((conj z)⁻¹) ^ 2 * deriv f z)) := by
    show (fderiv ℝ Φ z 1 - I * fderiv ℝ Φ z I) / 2 = _
    rw [hDΦ, hDΦ, map_one, Complex.conj_I]
    linear_combination ((conj h' * conj (((conj z)⁻¹ - z) * deriv (deriv f) z) +
      conj h' * conj (((conj z)⁻¹) ^ 2 * deriv f z)) / 2) * Complex.I_sq
  have hdzbar : LiZhongQC.dzbar Φ z = conj h' * conj (((conj z)⁻¹ - z) * deriv (deriv f) z) := by
    show (fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 = _
    rw [hDΦ, hDΦ, map_one, Complex.conj_I]
    linear_combination (-(conj h' * conj (((conj z)⁻¹ - z) * deriv (deriv f) z) +
      conj h' * conj (((conj z)⁻¹) ^ 2 * deriv f z)) / 2) * Complex.I_sq
  refine ⟨?_, ?_, ?_⟩
  · -- `C¹`
    have cG : ContDiffAt ℝ 1 (Function.invFunOn g unitDiscExterior) y :=
      ((hGd.contDiffOn hΩo).contDiffAt hyN).restrict_scalars ℝ
    have cH := cG.inv hu0
    have cHB := cH.comp z hC
    have cΨ := (Complex.conjCLE.contDiff.contDiffAt (x := _)).comp z cHB
    have cΨ' : ContDiffAt ℝ 1 (fun w =>
        conj ((Function.invFunOn g unitDiscExterior (f w + ((conj w)⁻¹ - w) * deriv f w))⁻¹)) z := by
      exact cΨ
    exact cΨ'.congr_of_eventuallyEq hΦ
  · rw [hdz]
    exact neg_ne_zero.mpr hb0
  · show LiZhongQC.dzbar Φ z / LiZhongQC.dz Φ z = _
    rw [hdz, hdzbar]
    have hm : ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) = 1 - z * conj z := by
      rw [Complex.mul_conj']
      push_cast
      ring
    rw [hm]
    have hh'c : conj h' ≠ 0 := (map_ne_zero _).mpr hh'0
    have hf'c : conj (deriv f z) ≠ 0 := (map_ne_zero _).mpr hf'0
    simp only [map_mul, map_sub, map_inv₀, map_pow, map_div₀, Complex.conj_conj]
    field_simp

/-- T1 block C2 (boundary decay): if `f` is holomorphic on `𝔻` and extends continuously to `𝔻̄`, then
`(1 − |z|)|f'(z)| → 0` as `|z| → 1` (Cauchy estimate on `D(z, (1−|z|)/2)` + uniform continuity). -/
theorem s07b_fkph_c_fprime {f F : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hFc : ContinuousOn F (closedBall (0 : ℂ) 1)) (hFf : ∀ z ∈ unitDisc, F z = f z) :
    ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ ∀ z : ℂ, s < ‖z‖ → ‖z‖ < 1 →
      (1 - ‖z‖) * ‖deriv f z‖ ≤ ε := by
  intro ε hε
  have huc := (isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous hFc
  rw [Metric.uniformContinuousOn_iff_le] at huc
  obtain ⟨δ, hδ, hU⟩ := huc (ε / 2) (by linarith)
  refine ⟨max 0 (1 - δ), le_max_left _ _, max_lt (by norm_num) (by linarith), ?_⟩
  intro z hz hz1
  have hzδ : 1 - ‖z‖ < δ := by
    have := le_max_right 0 (1 - δ)
    linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (1 - ‖z‖) / 2 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; linarith
  have hcl : closedBall z r ⊆ unitDisc := by
    intro w hw
    show w ∈ Metric.ball (0 : ℂ) 1
    rw [mem_ball_zero_iff]
    rw [mem_closedBall, dist_eq_norm] at hw
    have := norm_le_insert' w z
    linarith
  have hd : DiffContOnCl ℂ (fun w => f w - f z) (ball z r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z hr0.ne']
    exact (hf.mono hcl).sub_const (f z)
  have hzD : z ∈ unitDisc := hcl (mem_closedBall_self hr0.le)
  have hC : ∀ w ∈ sphere z r, ‖f w - f z‖ ≤ ε / 2 := by
    intro w hw
    have hwD := hcl (sphere_subset_closedBall hw)
    have hwc : w ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hwD
    have hzc : z ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hzD
    rw [mem_sphere] at hw
    have h := hU w hwc z hzc (by rw [hw]; linarith)
    rw [dist_eq_norm, hFf w hwD, hFf z hzD] at h
    exact h
  have h := norm_deriv_le_of_forall_mem_sphere_norm_le hr0 hd hC
  rw [deriv_sub_const, le_div_iff₀ hr0] at h
  have e : (1 - ‖z‖) * ‖deriv f z‖ = 2 * (‖deriv f z‖ * r) := by rw [hr]; ring
  rw [e]
  linarith

/-- T1 helper: `e^K − 1 ≤ 2K` for `0 ≤ K ≤ 1/2`. -/
theorem s07b_fkph_c_expK {K : ℝ} (h0 : 0 ≤ K) (h1 : K ≤ 1 / 2) : Real.exp K - 1 ≤ 2 * K := by
  have h := Real.add_one_le_exp (-K)
  have he : Real.exp K * Real.exp (-K) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hp := Real.exp_pos K
  have h2 : Real.exp K * (1 - K) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left h hp.le]
  have h3 : Real.exp K ≤ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hp.le]
  nlinarith [mul_le_mul_of_nonneg_right h3 h0]

/-- T1 helper: `e^{-T}(e^{εT} − 1) ≤ ε` for `T ≥ 0`, `0 ≤ ε ≤ 1/2`. -/
theorem s07b_fkph_c_expT {T ε : ℝ} (hT : 0 ≤ T) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :
    Real.exp (-T) * (Real.exp (ε * T) - 1) ≤ ε := by
  have a1 : Real.exp (ε * T) * Real.exp (-(ε * T)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have a2 := Real.add_one_le_exp (-(ε * T))
  have hpe := Real.exp_pos (ε * T)
  have hA : Real.exp (ε * T) - 1 ≤ ε * T * Real.exp (ε * T) := by
    nlinarith [mul_le_mul_of_nonneg_left a2 hpe.le]
  have hq := Real.quadratic_le_exp_of_nonneg (x := T / 2) (by positivity)
  have hT2 : T ≤ Real.exp (T / 2) := by nlinarith [sq_nonneg (T - 2)]
  have hm : Real.exp (-T) * Real.exp (ε * T) ≤ Real.exp (-(T / 2)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hinv : Real.exp (-(T / 2)) * Real.exp (T / 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hpT := Real.exp_pos (-T)
  have hph := Real.exp_pos (-(T / 2))
  calc Real.exp (-T) * (Real.exp (ε * T) - 1)
      ≤ Real.exp (-T) * (ε * T * Real.exp (ε * T)) := mul_le_mul_of_nonneg_left hA hpT.le
    _ = ε * T * (Real.exp (-T) * Real.exp (ε * T)) := by ring
    _ ≤ ε * T * Real.exp (-(T / 2)) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ ε * (Real.exp (T / 2) * Real.exp (-(T / 2))) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT2 hph.le) hε0
    _ = ε := by rw [mul_comm (Real.exp (T / 2)), hinv, mul_one]

/-- T1 helper (Grönwall for `f'` along a path in `𝔻`): if `|f''(γ)||γ'| ≤ K|f'(γ)|` on `[0, T]`, then
`|f'(γ t) − f'(γ 0)| ≤ |f'(γ 0)|(e^{Kt} − 1)`. -/
theorem s07b_fkph_c_gron {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) {γ γ' : ℝ → ℂ} {T K : ℝ}
    (hK : 0 ≤ K) (hγ : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt γ (γ' t) t)
    (hγD : ∀ t ∈ Icc (0 : ℝ) T, γ t ∈ unitDisc)
    (hφ : ∀ t ∈ Icc (0 : ℝ) T, ‖deriv (deriv f) (γ t)‖ * ‖γ' t‖ ≤ K * ‖deriv f (γ t)‖) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ‖deriv f (γ t) - deriv f (γ 0)‖ ≤ ‖deriv f (γ 0)‖ * (Real.exp (K * t) - 1) := by
  have hdf : DifferentiableOn ℂ (deriv f) unitDisc := hf.deriv isOpen_ball
  have hu : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt (fun s => deriv f (γ s) - deriv f (γ 0))
      (deriv (deriv f) (γ t) * γ' t) t := by
    intro t ht
    have h1 : HasDerivAt (deriv f) (deriv (deriv f) (γ t)) (γ t) :=
      ((hdf (γ t) (hγD t ht)).differentiableAt (isOpen_ball.mem_nhds (hγD t ht))).hasDerivAt
    exact (h1.comp t (hγ t ht)).sub_const _
  have hb : ∀ s ∈ Ico (0 : ℝ) T, ‖deriv (deriv f) (γ s) * γ' s‖ ≤
      K * ‖deriv f (γ s) - deriv f (γ 0)‖ + K * ‖deriv f (γ 0)‖ := by
    intro s hs
    have hs' := Ico_subset_Icc_self hs
    have h2 := norm_sub_norm_le (deriv f (γ s)) (deriv f (γ 0))
    rw [norm_mul]
    calc ‖deriv (deriv f) (γ s)‖ * ‖γ' s‖ ≤ K * ‖deriv f (γ s)‖ := hφ s hs'
      _ ≤ K * (‖deriv f (γ s) - deriv f (γ 0)‖ + ‖deriv f (γ 0)‖) :=
          mul_le_mul_of_nonneg_left (by linarith) hK
      _ = _ := by ring
  intro t ht
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun s => deriv f (γ s) - deriv f (γ 0)) (δ := 0) (K := K) (ε := K * ‖deriv f (γ 0)‖)
    (fun s hs => (hu s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hu s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (by simp) hb t ht
  rw [sub_zero] at hg
  rcases eq_or_lt_of_le hK with h0 | hpos
  · subst h0
    rw [gronwallBound_K0] at hg
    simpa using hg
  · rw [gronwallBound_of_K_ne_0 hpos.ne'] at hg
    simp only [zero_mul, zero_add] at hg
    rwa [mul_div_cancel_left₀ _ hpos.ne'] at hg

/-- T1 helper (straight segment): if `|f''(w)||b − a| ≤ K|f'(w)|` on `[a, b] ⊆ 𝔻`, `K ≤ 1/2`, then
`|f'(b) − f'(a)| ≤ 2K|f'(a)|` and `|f(b) − f(a) − f'(a)(b − a)| ≤ 2K|f'(a)||b − a|`. -/
theorem s07b_fkph_c_seg {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) {a b : ℂ} {K : ℝ}
    (hK0 : 0 ≤ K) (hK : K ≤ 1 / 2)
    (hD : ∀ t ∈ Icc (0 : ℝ) 1, a + (t : ℂ) * (b - a) ∈ unitDisc)
    (hφ : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv (deriv f) (a + (t : ℂ) * (b - a))‖ * ‖b - a‖ ≤
      K * ‖deriv f (a + (t : ℂ) * (b - a))‖) :
    ‖deriv f b - deriv f a‖ ≤ 2 * K * ‖deriv f a‖ ∧
      ‖f b - f a - deriv f a * (b - a)‖ ≤ 2 * K * ‖deriv f a‖ * ‖b - a‖ := by
  have hγ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => a + (s : ℂ) * (b - a)) (b - a) t :=
    fun t _ => by
      simpa using ((hasDerivAt_id t).ofReal_comp.mul_const (b - a)).const_add a
  have hg := s07b_fkph_c_gron hf hK0 hγ hD hφ
  have h0 : a + ((0 : ℝ) : ℂ) * (b - a) = a := by simp
  have h1 : a + ((1 : ℝ) : ℂ) * (b - a) = b := by simp
  have hbd : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖deriv f (a + (t : ℂ) * (b - a)) - deriv f a‖ ≤ 2 * K * ‖deriv f a‖ := by
    intro t ht
    have h := hg t ht
    simp only [h0] at h
    refine h.trans ?_
    have hKt : K * t ≤ K := mul_le_of_le_one_right hK0 ht.2
    have he := s07b_fkph_c_expK (mul_nonneg hK0 ht.1) (hKt.trans hK)
    have hex : Real.exp (K * t) - 1 ≤ 2 * K := by linarith
    nlinarith [norm_nonneg (deriv f a)]
  refine ⟨by simpa [h1] using hbd 1 ⟨zero_le_one, le_rfl⟩, ?_⟩
  have hdG : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt
      (fun s : ℝ => f (a + (s : ℂ) * (b - a)) - deriv f a * (a + (s : ℂ) * (b - a)))
      ((deriv f (a + (t : ℂ) * (b - a)) - deriv f a) * (b - a)) t := by
    intro t ht
    have h1' : HasDerivAt f (deriv f (a + (t : ℂ) * (b - a))) (a + (t : ℂ) * (b - a)) :=
      ((hf _ (hD t ht)).differentiableAt (isOpen_ball.mem_nhds (hD t ht))).hasDerivAt
    have h2 := (h1'.comp t (hγ t ht)).sub ((hγ t ht).const_mul (deriv f a))
    rw [sub_mul]
    exact h2
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖(deriv f (a + (t : ℂ) * (b - a)) - deriv f a) * (b - a)‖ ≤
      2 * K * ‖deriv f a‖ * ‖b - a‖ := by
    intro t ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbd t (Ico_subset_Icc_self ht)) (norm_nonneg _)
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun s : ℝ => f (a + (s : ℂ) * (b - a)) - deriv f a * (a + (s : ℂ) * (b - a)))
    (fun t ht => (hdG t ht).hasDerivWithinAt) hbound 1 ⟨zero_le_one, le_rfl⟩
  have e : f (a + ((1 : ℝ) : ℂ) * (b - a)) - deriv f a * (a + ((1 : ℝ) : ℂ) * (b - a)) -
      (f (a + ((0 : ℝ) : ℂ) * (b - a)) - deriv f a * (a + ((0 : ℝ) : ℂ) * (b - a))) =
      f b - f a - deriv f a * (b - a) := by
    rw [h0, h1]
    ring
  rw [e, sub_zero, mul_one] at hm
  exact hm

/-- T1 helper (radial leg, Grönwall in the log-depth variable `t = log(D/depth)`): along the radius from
`(1 − D)ζ` down to `(1 − δ)ζ`, if `s|f''| ≤ ε|f'|` at depth `s ∈ [δ, D]`, then
`δ|f'((1−δ)ζ) − f'((1−D)ζ)| ≤ εD|f'((1−D)ζ)|` and `f` is affine with slope `f'((1−D)ζ)` up to
`2εD|f'((1−D)ζ)|`. -/
theorem s07b_fkph_c_rad {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    {ε δ D : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) (hδ : 0 < δ) (hδD : δ ≤ D) (hD1 : D < 1)
    (hφ : ∀ s : ℝ, δ ≤ s → s ≤ D →
      s * ‖deriv (deriv f) (((1 - s : ℝ) : ℂ) * ζ)‖ ≤ ε * ‖deriv f (((1 - s : ℝ) : ℂ) * ζ)‖) :
    δ * ‖deriv f (((1 - δ : ℝ) : ℂ) * ζ) - deriv f (((1 - D : ℝ) : ℂ) * ζ)‖ ≤
        ε * D * ‖deriv f (((1 - D : ℝ) : ℂ) * ζ)‖ ∧
      ‖f (((1 - δ : ℝ) : ℂ) * ζ) - f (((1 - D : ℝ) : ℂ) * ζ) -
          deriv f (((1 - D : ℝ) : ℂ) * ζ) * (((1 - δ : ℝ) : ℂ) * ζ - ((1 - D : ℝ) : ℂ) * ζ)‖ ≤
        2 * ε * D * ‖deriv f (((1 - D : ℝ) : ℂ) * ζ)‖ := by
  have hD0 : 0 < D := hδ.trans_le hδD
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Real.log (D / δ) := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by
    rw [hT]
    exact Real.log_nonneg ((one_le_div hδ).mpr hδD)
  have hexpT : D * Real.exp (-T) = δ := by
    rw [hT, Real.exp_neg, Real.exp_log (div_pos hD0 hδ)]
    field_simp
  obtain ⟨γ, hγd⟩ : ∃ γ : ℝ → ℂ, γ = fun t => ((1 - D * Real.exp (-t) : ℝ) : ℂ) * ζ := ⟨_, rfl⟩
  obtain ⟨γ', hγ'd⟩ : ∃ γ' : ℝ → ℂ, γ' = fun t => ((D * Real.exp (-t) : ℝ) : ℂ) * ζ := ⟨_, rfl⟩
  have hγ : ∀ t : ℝ, HasDerivAt γ (γ' t) t := by
    intro t
    rw [hγd, hγ'd]
    have h1 : HasDerivAt (fun s : ℝ => 1 - D * Real.exp (-s)) (D * Real.exp (-t)) t := by
      have := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).const_mul D
      rw [show D * Real.exp (-t) = -(D * (Real.exp (-t) * -1)) by ring]
      exact this.const_sub 1
    exact h1.ofReal_comp.mul_const ζ
  have hs : ∀ t ∈ Icc (0 : ℝ) T, δ ≤ D * Real.exp (-t) ∧ D * Real.exp (-t) ≤ D := by
    intro t ht
    constructor
    · rw [← hexpT]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [ht.2])) hD0.le
    · exact mul_le_of_le_one_right hD0.le (Real.exp_le_one_iff.mpr (by linarith [ht.1]))
  have hnorm : ∀ t ∈ Icc (0 : ℝ) T, ‖γ t‖ = 1 - D * Real.exp (-t) := by
    intro t ht
    rw [hγd]
    simp only
    rw [norm_mul, hζ, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith [(hs t ht).2])]
  have hγD : ∀ t ∈ Icc (0 : ℝ) T, γ t ∈ unitDisc := by
    intro t ht
    show γ t ∈ Metric.ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, hnorm t ht]
    linarith [hδ.trans_le (hs t ht).1]
  have hγ'n : ∀ t, ‖γ' t‖ = D * Real.exp (-t) := by
    intro t
    rw [hγ'd]
    simp only
    rw [norm_mul, hζ, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hφ' : ∀ t ∈ Icc (0 : ℝ) T, ‖deriv (deriv f) (γ t)‖ * ‖γ' t‖ ≤ ε * ‖deriv f (γ t)‖ := by
    intro t ht
    rw [hγ'n, mul_comm]
    have := hφ (D * Real.exp (-t)) (hs t ht).1 (hs t ht).2
    rw [hγd]
    exact this
  have hg := s07b_fkph_c_gron hf hε0 (fun t _ => hγ t) hγD hφ'
  have hγ0 : γ 0 = ((1 - D : ℝ) : ℂ) * ζ := by
    rw [hγd]
    simp
  have hγT : γ T = ((1 - δ : ℝ) : ℂ) * ζ := by
    rw [hγd]
    simp only
    rw [hexpT]
  rw [← hγ0, ← hγT]
  set A := ‖deriv f (γ 0)‖ with hA
  have hA0 : 0 ≤ A := norm_nonneg _
  refine ⟨?_, ?_⟩
  · have h1 := hg T ⟨hT0, le_rfl⟩
    have h2 := s07b_fkph_c_expT hT0 hε0 hε
    calc δ * ‖deriv f (γ T) - deriv f (γ 0)‖ ≤ δ * (A * (Real.exp (ε * T) - 1)) :=
          mul_le_mul_of_nonneg_left h1 hδ.le
      _ = A * D * (Real.exp (-T) * (Real.exp (ε * T) - 1)) := by rw [← hexpT]; ring
      _ ≤ A * D * ε := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ε * D * A := by ring
  · -- `G t = f(γ t) − f'(γ 0) γ t`, compared with the boundary function `Bf`
    have hdG : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt
        (fun s : ℝ => f (γ s) - deriv f (γ 0) * γ s - (f (γ 0) - deriv f (γ 0) * γ 0))
        ((deriv f (γ t) - deriv f (γ 0)) * γ' t) t := by
      intro t ht
      have h1' : HasDerivAt f (deriv f (γ t)) (γ t) :=
        ((hf _ (hγD t ht)).differentiableAt (isOpen_ball.mem_nhds (hγD t ht))).hasDerivAt
      have h2 := ((h1'.comp t (hγ t)).sub ((hγ t).const_mul (deriv f (γ 0)))).sub_const
        (f (γ 0) - deriv f (γ 0) * γ 0)
      rw [sub_mul]
      exact h2
    have hε1 : 0 < 1 - ε := by linarith
    obtain ⟨Bf, hBf⟩ : ∃ Bf : ℝ → ℝ, Bf = fun t => A * D *
        ((1 - Real.exp (-((1 - ε) * t))) / (1 - ε) - (1 - Real.exp (-t))) := ⟨_, rfl⟩
    have hBd : ∀ t, HasDerivAt Bf (A * D * (Real.exp (-((1 - ε) * t)) - Real.exp (-t))) t := by
      intro t
      rw [hBf]
      have e1 : HasDerivAt (fun s : ℝ => Real.exp (-((1 - ε) * s)))
          (Real.exp (-((1 - ε) * t)) * (-(1 - ε))) t := by
        have := (Real.hasDerivAt_exp (-((1 - ε) * t))).comp t
          (((hasDerivAt_id t).const_mul (1 - ε)).neg)
        rw [show Real.exp (-((1 - ε) * t)) * (-(1 - ε)) =
          Real.exp (-((1 - ε) * id t)) * -((1 - ε) * 1) by simp]
        exact this
      have e2 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-t) * (-1)) t :=
        (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
      have := ((((e1.const_sub 1).div_const (1 - ε)).sub (e2.const_sub 1))).const_mul (A * D)
      convert this using 1
      field_simp
    have hbound : ∀ t ∈ Ico (0 : ℝ) T, ‖(deriv f (γ t) - deriv f (γ 0)) * γ' t‖ ≤
        A * D * (Real.exp (-((1 - ε) * t)) - Real.exp (-t)) := by
      intro t ht
      have ht' := Ico_subset_Icc_self ht
      rw [norm_mul, hγ'n]
      have e : A * D * (Real.exp (-((1 - ε) * t)) - Real.exp (-t)) =
          A * (Real.exp (ε * t) - 1) * (D * Real.exp (-t)) := by
        have : Real.exp (-((1 - ε) * t)) = Real.exp (ε * t) * Real.exp (-t) := by
          rw [← Real.exp_add]
          ring_nf
        rw [this]
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (hg t ht') (by positivity)
    have hm := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun s : ℝ => f (γ s) - deriv f (γ 0) * γ s - (f (γ 0) - deriv f (γ 0) * γ 0))
      (fun t ht => (hdG t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hdG t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (B := Bf) (by rw [hBf]; simp) hBd hbound ⟨hT0, le_rfl⟩
    have e : f (γ T) - deriv f (γ 0) * γ T - (f (γ 0) - deriv f (γ 0) * γ 0) =
        f (γ T) - f (γ 0) - deriv f (γ 0) * (γ T - γ 0) := by ring
    rw [e] at hm
    refine hm.trans ?_
    rw [hBf]
    simp only
    have h3 : Real.exp (-T) ≤ Real.exp (-((1 - ε) * T)) := Real.exp_le_exp.mpr (by nlinarith)
    have h4 := Real.exp_pos (-((1 - ε) * T))
    have h5 : Real.exp (-((1 - ε) * T)) ≤ Real.exp (-((1 - ε) * T)) / (1 - ε) :=
      le_div_self h4.le hε1 (by linarith)
    have h6 : (1 - Real.exp (-((1 - ε) * T))) / (1 - ε) - (1 - Real.exp (-T)) ≤ 2 * ε := by
      rw [sub_div]
      have h7 : 1 / (1 - ε) ≤ 1 + 2 * ε := by
        rw [div_le_iff₀ hε1]
        nlinarith
      linarith
    calc A * D * ((1 - Real.exp (-((1 - ε) * T))) / (1 - ε) - (1 - Real.exp (-T)))
        ≤ A * D * (2 * ε) := mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = 2 * ε * D * A := by ring

/-- T1 helper: `‖a + t(b − a)‖² = (1−t)‖a‖² + t‖b‖² − t(1−t)‖b − a‖²`. -/
theorem s07b_fkph_c_chord (a b : ℂ) (t : ℝ) :
    ‖a + (t : ℂ) * (b - a)‖ ^ 2 = (1 - t) * ‖a‖ ^ 2 + t * ‖b‖ ^ 2 - t * (1 - t) * ‖b - a‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.add_im, Complex.mul_im,
    Complex.sub_im]
  ring

/-- T1 helper: the radial projection `z ↦ z/|z|` is `2/|z₁|`-Lipschitz at `z₁`. -/
theorem s07b_fkph_c_proj {z₁ z₂ : ℂ} (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0) :
    ‖((‖z₁‖⁻¹ : ℝ) : ℂ) * z₁ - ((‖z₂‖⁻¹ : ℝ) : ℂ) * z₂‖ ≤ 2 * ‖z₁ - z₂‖ / ‖z₁‖ := by
  have hn1 : 0 < ‖z₁‖ := norm_pos_iff.mpr h₁
  have hn2 : 0 < ‖z₂‖ := norm_pos_iff.mpr h₂
  have e : ((‖z₁‖⁻¹ : ℝ) : ℂ) * z₁ - ((‖z₂‖⁻¹ : ℝ) : ℂ) * z₂ =
      ((‖z₁‖⁻¹ : ℝ) : ℂ) * (z₁ - z₂) + (((‖z₁‖⁻¹ - ‖z₂‖⁻¹ : ℝ)) : ℂ) * z₂ := by
    push_cast
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    Real.norm_eq_abs]
  have h3 : |‖z₁‖⁻¹ - ‖z₂‖⁻¹| * ‖z₂‖ = |‖z₂‖ - ‖z₁‖| / ‖z₁‖ := by
    rw [inv_sub_inv hn1.ne' hn2.ne', abs_div, abs_of_pos (mul_pos hn1 hn2)]
    field_simp
  have h4 : |‖z₂‖ - ‖z₁‖| ≤ ‖z₁ - z₂‖ := by
    rw [abs_sub_comm]
    exact abs_norm_sub_norm_le z₁ z₂
  rw [h3]
  have h5 : |‖z₂‖ - ‖z₁‖| / ‖z₁‖ ≤ ‖z₁ - z₂‖ / ‖z₁‖ := div_le_div_of_nonneg_right h4 hn1.le
  have h6 : ‖z₁‖⁻¹ * ‖z₁ - z₂‖ = ‖z₁ - z₂‖ / ‖z₁‖ := by ring
  rw [h6]
  have h7 : 2 * ‖z₁ - z₂‖ / ‖z₁‖ = ‖z₁ - z₂‖ / ‖z₁‖ + ‖z₁ - z₂‖ / ‖z₁‖ := by ring
  linarith

/-- T1 helper: the norm along a segment is below the convex combination of the endpoint norms. -/
theorem s07b_fkph_c_segnorm (a b : ℂ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ‖a + (t : ℂ) * (b - a)‖ ≤ (1 - t) * ‖a‖ + t * ‖b‖ := by
  have e : a + (t : ℂ) * (b - a) = ((1 - t : ℝ) : ℂ) * a + (t : ℂ) * b := by
    push_cast
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by linarith),
    Real.norm_of_nonneg h0]

/-- T1 helper: lower bound for the norm along a segment. -/
theorem s07b_fkph_c_segnorm_ge (a b : ℂ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ‖a‖ - ‖b - a‖ ≤ ‖a + (t : ℂ) * (b - a)‖ := by
  have h := norm_sub_norm_le a (-((t : ℂ) * (b - a)))
  rw [norm_neg, sub_neg_eq_add, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0] at h
  have h2 : t * ‖b - a‖ ≤ ‖b - a‖ := mul_le_of_le_one_left (norm_nonneg _) h1
  linarith

/-- T1 helper (core of `s07b_fkph_c_aff`, with `|z₁| ≤ |z₂|`, i.e. `z₁` the deeper point). -/
theorem s07b_fkph_c_affcore {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) {ε η : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 100) (hη0 : 0 < η) (hη : η ≤ 1 / 8)
    (hB : ∀ u : ℂ, 1 - 4 * η < ‖u‖ → ‖u‖ < 1 → (1 - ‖u‖) * ‖deriv (deriv f) u‖ ≤ ε * ‖deriv f u‖)
    {z₁ z₂ : ℂ} (h₁ : 1 - η < ‖z₁‖) (h₁' : ‖z₁‖ < 1) (h₂ : 1 - η < ‖z₂‖) (h₂' : ‖z₂‖ < 1)
    (hd : ‖z₁ - z₂‖ ≤ η) (h12 : ‖z₁‖ ≤ ‖z₂‖) :
    ∃ p ∈ unitDisc, ‖z₁ - z₂‖ ≤ 1 - ‖p‖ ∧
      ‖f z₁ - f z₂ - deriv f p * (z₁ - z₂)‖ ≤ 100 * ε * ‖deriv f p‖ * ‖z₁ - z₂‖ ∧
      (1 - ‖z₁‖) * ‖deriv f z₁ - deriv f p‖ ≤ 100 * ε * ‖deriv f p‖ * ‖z₁ - z₂‖ ∧
      (1 - ‖z₂‖) * ‖deriv f z₂ - deriv f p‖ ≤ 100 * ε * ‖deriv f p‖ * ‖z₁ - z₂‖ := by
  obtain ⟨d, hdd⟩ : ∃ d : ℝ, d = ‖z₁ - z₂‖ := ⟨_, rfl⟩
  rw [← hdd]
  rw [← hdd] at hd
  have hd0 : 0 ≤ d := by rw [hdd]; exact norm_nonneg _
  have hd21 : ‖z₂ - z₁‖ = d := by rw [hdd]; exact norm_sub_rev _ _
  have hmem : ∀ u : ℂ, ‖u‖ < 1 → u ∈ unitDisc := by
    intro u hu
    show u ∈ Metric.ball (0 : ℂ) 1
    exact mem_ball_zero_iff.mpr hu
  have hδ₂ : 0 < 1 - ‖z₂‖ := by linarith
  rcases le_or_gt d (1 - ‖z₂‖) with hA | hBc
  · -- Case A: the straight segment from `z₁` to `z₂` (depth `≥ 1 − |z₂|` along it)
    have hnu : ∀ t ∈ Icc (0 : ℝ) 1, 1 - ‖z₂‖ ≤ 1 - ‖z₁ + (t : ℂ) * (z₂ - z₁)‖ ∧
        1 - 4 * η < ‖z₁ + (t : ℂ) * (z₂ - z₁)‖ := by
      intro t ht
      have h1 := s07b_fkph_c_segnorm z₁ z₂ ht.1 ht.2
      have h2 := s07b_fkph_c_segnorm_ge z₁ z₂ ht.1 ht.2
      rw [hd21] at h2
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr h12)]
      · linarith
    obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ε * d / (1 - ‖z₂‖) := ⟨_, rfl⟩
    have hK0 : 0 ≤ K := by rw [hK]; positivity
    have hKε : K ≤ ε := by
      rw [hK, div_le_iff₀ hδ₂]
      exact mul_le_mul_of_nonneg_left hA hε0
    have hKd : (1 - ‖z₂‖) * K = ε * d := by
      rw [hK]
      field_simp
    have hφ : ∀ t ∈ Icc (0 : ℝ) 1,
        ‖deriv (deriv f) (z₁ + (t : ℂ) * (z₂ - z₁))‖ * ‖z₂ - z₁‖ ≤
          K * ‖deriv f (z₁ + (t : ℂ) * (z₂ - z₁))‖ := by
      intro t ht
      obtain ⟨hu1, hu2⟩ := hnu t ht
      have e1 : (1 - ‖z₂‖) * ‖deriv (deriv f) (z₁ + (t : ℂ) * (z₂ - z₁))‖ ≤
          ε * ‖deriv f (z₁ + (t : ℂ) * (z₂ - z₁))‖ :=
        (mul_le_mul_of_nonneg_right hu1 (norm_nonneg _)).trans (hB _ hu2 (by linarith))
      rw [hd21, hK, div_mul_eq_mul_div, le_div_iff₀ hδ₂]
      nlinarith [mul_le_mul_of_nonneg_right e1 hd0]
    have hDs : ∀ t ∈ Icc (0 : ℝ) 1, z₁ + (t : ℂ) * (z₂ - z₁) ∈ unitDisc := by
      intro t ht
      have := (hnu t ht).1
      exact hmem _ (by linarith)
    obtain ⟨hs1, hs2⟩ := s07b_fkph_c_seg hf hK0 (by linarith) hDs hφ
    rw [hd21] at hs2
    set A := ‖deriv f z₁‖ with hAd
    have hA0 : 0 ≤ A := norm_nonneg _
    refine ⟨z₁, hmem _ h₁', by linarith, ?_, ?_, ?_⟩
    · have e : ‖f z₁ - f z₂ - deriv f z₁ * (z₁ - z₂)‖ = ‖f z₂ - f z₁ - deriv f z₁ * (z₂ - z₁)‖ := by
        rw [← norm_neg]
        congr 1
        ring
      rw [e]
      refine hs2.trans ?_
      have : K * (A * d) ≤ ε * (A * d) := mul_le_mul_of_nonneg_right hKε (by positivity)
      nlinarith [mul_nonneg hε0 (mul_nonneg hA0 hd0)]
    · rw [sub_self, norm_zero, mul_zero]
      positivity
    · calc (1 - ‖z₂‖) * ‖deriv f z₂ - deriv f z₁‖ ≤ (1 - ‖z₂‖) * (2 * K * A) :=
            mul_le_mul_of_nonneg_left hs1 hδ₂.le
        _ = 2 * A * ((1 - ‖z₂‖) * K) := by ring
        _ = 2 * ε * A * d := by rw [hKd]; ring
        _ ≤ 100 * ε * A * d := by nlinarith [mul_nonneg hε0 (mul_nonneg hA0 hd0)]
  · -- Case B: the box path through depth `D = (1 − |z₂|) + d`
    obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (1 - ‖z₂‖) + d := ⟨_, rfl⟩
    have hD2 : D ≤ 2 * d := by linarith
    have hDd : d ≤ D := by linarith
    have hD1 : D < 1 := by linarith
    have hn1 : 0 < ‖z₁‖ := by linarith
    have hn2 : 0 < ‖z₂‖ := by linarith
    have hz₁0 : z₁ ≠ 0 := norm_pos_iff.mp hn1
    have hz₂0 : z₂ ≠ 0 := norm_pos_iff.mp hn2
    have hδ₁D : 1 - ‖z₁‖ ≤ D := by
      have := norm_sub_norm_le z₂ z₁
      rw [hd21] at this
      linarith
    have hδ₁ : 0 < 1 - ‖z₁‖ := by linarith
    obtain ⟨ζ₁, hζ₁d⟩ : ∃ ζ : ℂ, ζ = ((‖z₁‖⁻¹ : ℝ) : ℂ) * z₁ := ⟨_, rfl⟩
    obtain ⟨ζ₂, hζ₂d⟩ : ∃ ζ : ℂ, ζ = ((‖z₂‖⁻¹ : ℝ) : ℂ) * z₂ := ⟨_, rfl⟩
    have hζn : ∀ z : ℂ, 0 < ‖z‖ → ‖((‖z‖⁻¹ : ℝ) : ℂ) * z‖ = 1 := by
      intro z hz
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hz.le),
        inv_mul_cancel₀ hz.ne']
    have hζ₁ : ‖ζ₁‖ = 1 := by rw [hζ₁d]; exact hζn z₁ hn1
    have hζ₂ : ‖ζ₂‖ = 1 := by rw [hζ₂d]; exact hζn z₂ hn2
    have hzeq : ∀ z : ℂ, 0 < ‖z‖ →
        (((1 - (1 - ‖z‖)) : ℝ) : ℂ) * (((‖z‖⁻¹ : ℝ) : ℂ) * z) = z := by
      intro z hz
      rw [sub_sub_cancel, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hz.ne',
        Complex.ofReal_one, one_mul]
    have hz1eq : (((1 - (1 - ‖z₁‖)) : ℝ) : ℂ) * ζ₁ = z₁ := by rw [hζ₁d]; exact hzeq z₁ hn1
    have hz2eq : (((1 - (1 - ‖z₂‖)) : ℝ) : ℂ) * ζ₂ = z₂ := by rw [hζ₂d]; exact hzeq z₂ hn2
    have hnr : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ s : ℝ, s ≤ 1 → ‖((1 - s : ℝ) : ℂ) * ζ‖ = 1 - s := by
      intro ζ hζ s hs
      rw [norm_mul, hζ, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have hrφ : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ s : ℝ, 0 < s → s ≤ D →
        s * ‖deriv (deriv f) (((1 - s : ℝ) : ℂ) * ζ)‖ ≤ ε * ‖deriv f (((1 - s : ℝ) : ℂ) * ζ)‖ := by
      intro ζ hζ s hs0 hsD
      have hn := hnr ζ hζ s (by linarith)
      have h := hB (((1 - s : ℝ) : ℂ) * ζ) (by rw [hn]; linarith) (by rw [hn]; linarith)
      rw [hn, sub_sub_cancel] at h
      exact h
    have R1 := s07b_fkph_c_rad hf hζ₁ hε0 (by linarith) hδ₁ hδ₁D hD1
      (fun s hs hs' => hrφ ζ₁ hζ₁ s (by linarith) hs')
    have R2 := s07b_fkph_c_rad hf hζ₂ hε0 (by linarith) hδ₂ (by linarith) hD1
      (fun s hs hs' => hrφ ζ₂ hζ₂ s (by linarith) hs')
    obtain ⟨p₁, hp₁⟩ : ∃ p : ℂ, p = ((1 - D : ℝ) : ℂ) * ζ₁ := ⟨_, rfl⟩
    obtain ⟨p₂, hp₂⟩ : ∃ p : ℂ, p = ((1 - D : ℝ) : ℂ) * ζ₂ := ⟨_, rfl⟩
    rw [hz1eq, ← hp₁] at R1
    rw [hz2eq, ← hp₂] at R2
    obtain ⟨R1a, R1b⟩ := R1
    obtain ⟨R2a, R2b⟩ := R2
    have hp1n : ‖p₁‖ = 1 - D := by rw [hp₁]; exact hnr ζ₁ hζ₁ D hD1.le
    have hp2n : ‖p₂‖ = 1 - D := by rw [hp₂]; exact hnr ζ₂ hζ₂ D hD1.le
    have hzp2 : ‖z₂ - p₂‖ = d := by
      have h := s07b_fkph_c_radsub hζ₂ (1 - (1 - ‖z₂‖)) (1 - D)
      rw [hz2eq, ← hp₂, abs_of_nonneg (by linarith)] at h
      rw [h]
      linarith
    have hp21 : ‖p₂ - p₁‖ ≤ 3 * d := by
      have hpr := s07b_fkph_c_proj hz₁0 hz₂0
      rw [← hζ₁d, ← hζ₂d, ← hdd] at hpr
      have e : p₂ - p₁ = ((1 - D : ℝ) : ℂ) * (ζ₂ - ζ₁) := by rw [hp₁, hp₂]; ring
      rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), norm_sub_rev]
      have h3 : 2 * d / ‖z₁‖ ≤ 3 * d := by
        rw [div_le_iff₀ hn1]
        nlinarith
      have h4 : (1 - D) * ‖ζ₁ - ζ₂‖ ≤ ‖ζ₁ - ζ₂‖ :=
        mul_le_of_le_one_left (norm_nonneg _) (by linarith)
      linarith
    -- the chord `p₁ → p₂` stays at depth `≥ D` and inside `|u| > 1 − 4η`
    have hchord : ∀ t ∈ Icc (0 : ℝ) 1, D ≤ 1 - ‖p₁ + (t : ℂ) * (p₂ - p₁)‖ ∧
        1 - 4 * η < ‖p₁ + (t : ℂ) * (p₂ - p₁)‖ := by
      intro t ht
      have h1 := s07b_fkph_c_segnorm p₁ p₂ ht.1 ht.2
      rw [hp1n, hp2n] at h1
      refine ⟨by linarith, ?_⟩
      have hid := s07b_fkph_c_chord p₁ p₂ t
      rw [hp1n, hp2n] at hid
      have htt : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
      have htt0 : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (by linarith [ht.2])
      have hsq : ‖p₂ - p₁‖ ^ 2 ≤ (3 * d) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp21 2
      have hprod : t * (1 - t) * ‖p₂ - p₁‖ ^ 2 ≤ 1 / 4 * (3 * d) ^ 2 :=
        mul_le_mul htt hsq (sq_nonneg _) (by norm_num)
      have hid' : ‖p₁ + (t : ℂ) * (p₂ - p₁)‖ ^ 2 = (1 - D) ^ 2 - t * (1 - t) * ‖p₂ - p₁‖ ^ 2 := by
        rw [hid]
        ring
      have hR : 1 - 2 * η < 1 - D := by linarith
      have hR0 : 0 ≤ 1 - 2 * η := by linarith
      have hRsq : (1 - 2 * η) ^ 2 < (1 - D) ^ 2 := pow_lt_pow_left₀ hR hR0 two_ne_zero
      have h9 : (3 * d) ^ 2 ≤ (3 * η) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      have hpoly : (1 - 4 * η) ^ 2 + 1 / 4 * (3 * η) ^ 2 < (1 - 2 * η) ^ 2 := by
        have : (1 - 2 * η) ^ 2 - ((1 - 4 * η) ^ 2 + 1 / 4 * (3 * η) ^ 2) = η * (4 - 57 / 4 * η) := by
          ring
        have h2 : 0 < η * (4 - 57 / 4 * η) := mul_pos hη0 (by linarith)
        linarith
      have hfin : (1 - 4 * η) ^ 2 < ‖p₁ + (t : ℂ) * (p₂ - p₁)‖ ^ 2 := by
        rw [hid']
        linarith
      by_contra hc
      push Not at hc
      have := pow_le_pow_left₀ (norm_nonneg _) hc 2
      linarith
    have hφc : ∀ t ∈ Icc (0 : ℝ) 1,
        ‖deriv (deriv f) (p₁ + (t : ℂ) * (p₂ - p₁))‖ * ‖p₂ - p₁‖ ≤
          (3 * ε) * ‖deriv f (p₁ + (t : ℂ) * (p₂ - p₁))‖ := by
      intro t ht
      obtain ⟨hu1, hu2⟩ := hchord t ht
      have e1 : D * ‖deriv (deriv f) (p₁ + (t : ℂ) * (p₂ - p₁))‖ ≤
          ε * ‖deriv f (p₁ + (t : ℂ) * (p₂ - p₁))‖ :=
        (mul_le_mul_of_nonneg_right hu1 (norm_nonneg _)).trans (hB _ hu2 (by linarith))
      have e2 : ‖deriv (deriv f) (p₁ + (t : ℂ) * (p₂ - p₁))‖ * ‖p₂ - p₁‖ ≤
          ‖deriv (deriv f) (p₁ + (t : ℂ) * (p₂ - p₁))‖ * (3 * D) :=
        mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      nlinarith
    have hDc : ∀ t ∈ Icc (0 : ℝ) 1, p₁ + (t : ℂ) * (p₂ - p₁) ∈ unitDisc := by
      intro t ht
      have := (hchord t ht).1
      exact hmem _ (by linarith)
    obtain ⟨C1, C2⟩ := s07b_fkph_c_seg hf (by positivity) (by linarith) hDc hφc
    set A := ‖deriv f p₁‖ with hAd
    have hA0 : 0 ≤ A := norm_nonneg _
    have hA2 : ‖deriv f p₂‖ ≤ 2 * A := by
      have := norm_le_insert' (deriv f p₂) (deriv f p₁)
      linarith [mul_le_mul_of_nonneg_right hε hA0]
    have hεA : 0 ≤ ε * A := mul_nonneg hε0 hA0
    refine ⟨p₁, hmem _ (by rw [hp1n]; linarith), by rw [hp1n]; linarith, ?_, ?_, ?_⟩
    · have e : f z₁ - f z₂ - deriv f p₁ * (z₁ - z₂) =
          (f z₁ - f p₁ - deriv f p₁ * (z₁ - p₁)) - (f z₂ - f p₂ - deriv f p₂ * (z₂ - p₂)) -
            (f p₂ - f p₁ - deriv f p₁ * (p₂ - p₁)) - (deriv f p₂ - deriv f p₁) * (z₂ - p₂) := by
        ring
      rw [e]
      have n4 : ‖(deriv f p₂ - deriv f p₁) * (z₂ - p₂)‖ ≤ 2 * (3 * ε) * A * d := by
        rw [norm_mul, hzp2]
        exact mul_le_mul_of_nonneg_right C1 hd0
      have hX2 : 2 * ε * D * ‖deriv f p₂‖ ≤ 2 * ε * (2 * d) * (2 * A) := by
        have := mul_le_mul_of_nonneg_left (mul_le_mul hD2 hA2 (norm_nonneg _) (by linarith)) hε0
        linarith
      have hX1 : 2 * ε * D * A ≤ 2 * ε * (2 * d) * A := by
        linarith [mul_le_mul_of_nonneg_right hD2 hεA]
      have hX3 : 2 * (3 * ε) * A * ‖p₂ - p₁‖ ≤ 2 * (3 * ε) * A * (3 * d) :=
        mul_le_mul_of_nonneg_left hp21 (by positivity)
      have t1 := norm_sub_le
        ((f z₁ - f p₁ - deriv f p₁ * (z₁ - p₁)) - (f z₂ - f p₂ - deriv f p₂ * (z₂ - p₂)) -
          (f p₂ - f p₁ - deriv f p₁ * (p₂ - p₁))) ((deriv f p₂ - deriv f p₁) * (z₂ - p₂))
      have t2 := norm_sub_le
        ((f z₁ - f p₁ - deriv f p₁ * (z₁ - p₁)) - (f z₂ - f p₂ - deriv f p₂ * (z₂ - p₂)))
        (f p₂ - f p₁ - deriv f p₁ * (p₂ - p₁))
      have t3 := norm_sub_le (f z₁ - f p₁ - deriv f p₁ * (z₁ - p₁))
        (f z₂ - f p₂ - deriv f p₂ * (z₂ - p₂))
      linarith [mul_nonneg hεA hd0]
    · have : ε * D * A ≤ ε * (2 * d) * A := by linarith [mul_le_mul_of_nonneg_right hD2 hεA]
      linarith [mul_nonneg hεA hd0]
    · have t1 := norm_sub_le_norm_sub_add_norm_sub (deriv f z₂) (deriv f p₂) (deriv f p₁)
      have hX2 : ε * D * ‖deriv f p₂‖ ≤ ε * (2 * d) * (2 * A) := by
        have := mul_le_mul_of_nonneg_left (mul_le_mul hD2 hA2 (norm_nonneg _) (by linarith)) hε0
        linarith
      have h6 : (1 - ‖z₂‖) * ‖deriv f p₂ - deriv f p₁‖ ≤ d * (2 * (3 * ε) * A) :=
        mul_le_mul (by linarith) C1 (norm_nonneg _) hd0
      have h7 : (1 - ‖z₂‖) * ‖deriv f z₂ - deriv f p₁‖ ≤
          (1 - ‖z₂‖) * ‖deriv f z₂ - deriv f p₂‖ + (1 - ‖z₂‖) * ‖deriv f p₂ - deriv f p₁‖ := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left t1 hδ₂.le
      linarith [mul_nonneg hεA hd0]

/-- T1 block C2 (affine approximation at the hyperbolic scale; the Becker–Pommerenke estimate): if
`(1 − |u|)|f''/f'(u)| ≤ ε` on the collar `1 − 4η < |u| < 1`, then for `z₁, z₂` with `1 − η < |zᵢ| < 1`,
`|z₁ − z₂| ≤ η`, there is a reference point `p` with `|z₁ − z₂| ≤ 1 − |p|` such that `f` is affine with
slope `f'(p)` up to `100 ε |f'(p)| |z₁ − z₂|` between `z₁, z₂`, and `(1 − |zᵢ|)|f'(zᵢ) − f'(p)|` is of the
same size. (Straight segment if `|z₁ − z₂| ≤ 1 − |zᵢ|`; otherwise the box path through depth
`2|z₁ − z₂|`, with Grönwall in the log-depth variable on the radial legs.) -/
theorem s07b_fkph_c_aff {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hf' : ∀ z ∈ unitDisc, deriv f z ≠ 0) {ε η : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100) (hη0 : 0 < η)
    (hη : η ≤ 1 / 8)
    (hB : ∀ u : ℂ, 1 - 4 * η < ‖u‖ → ‖u‖ < 1 → (1 - ‖u‖) * ‖deriv (deriv f) u / deriv f u‖ ≤ ε)
    {z₁ z₂ : ℂ} (h₁ : 1 - η < ‖z₁‖) (h₁' : ‖z₁‖ < 1) (h₂ : 1 - η < ‖z₂‖) (h₂' : ‖z₂‖ < 1)
    (hd : ‖z₁ - z₂‖ ≤ η) :
    ∃ p ∈ unitDisc, ‖z₁ - z₂‖ ≤ 1 - ‖p‖ ∧
      ‖f z₁ - f z₂ - deriv f p * (z₁ - z₂)‖ ≤ 100 * ε * ‖deriv f p‖ * ‖z₁ - z₂‖ ∧
      (1 - ‖z₁‖) * ‖deriv f z₁ - deriv f p‖ ≤ 100 * ε * ‖deriv f p‖ * ‖z₁ - z₂‖ ∧
      (1 - ‖z₂‖) * ‖deriv f z₂ - deriv f p‖ ≤ 100 * ε * ‖deriv f p‖ * ‖z₁ - z₂‖ := by
  have hBm : ∀ u : ℂ, 1 - 4 * η < ‖u‖ → ‖u‖ < 1 →
      (1 - ‖u‖) * ‖deriv (deriv f) u‖ ≤ ε * ‖deriv f u‖ := by
    intro u hu1 hu2
    have h := hB u hu1 hu2
    have hu : u ∈ unitDisc := by
      show u ∈ Metric.ball (0 : ℂ) 1
      exact mem_ball_zero_iff.mpr hu2
    have hpos : 0 < ‖deriv f u‖ := norm_pos_iff.mpr (hf' u hu)
    rw [norm_div, mul_div_assoc', div_le_iff₀ hpos] at h
    exact h
  rcases le_total ‖z₁‖ ‖z₂‖ with h12 | h21
  · exact s07b_fkph_c_affcore hf hε0 hε hη0 hη hBm h₁ h₁' h₂ h₂' hd h12
  · obtain ⟨p, hp, hp1, hp2, hp3, hp4⟩ :=
      s07b_fkph_c_affcore hf hε0 hε hη0 hη hBm h₂ h₂' h₁ h₁' (by rw [norm_sub_rev]; exact hd) h21
    have e1 : ‖z₂ - z₁‖ = ‖z₁ - z₂‖ := norm_sub_rev _ _
    have e2 : ‖f z₂ - f z₁ - deriv f p * (z₂ - z₁)‖ = ‖f z₁ - f z₂ - deriv f p * (z₁ - z₂)‖ := by
      rw [← norm_neg]
      congr 1
      ring
    rw [e1] at hp1 hp2 hp3 hp4
    rw [e2] at hp2
    exact ⟨p, hp, hp1, hp2, hp4, hp3⟩

/-- T1 helper: `|1/z̄ − z| = (1 − |z|²)/|z|`. -/
theorem s07b_fkph_c_tnorm {z : ℂ} (h0 : 0 < ‖z‖) (h1 : ‖z‖ ≤ 1) :
    ‖(conj z)⁻¹ - z‖ = (1 - ‖z‖ ^ 2) / ‖z‖ := by
  have hz : z ≠ 0 := norm_pos_iff.mp h0
  have hc : conj z ≠ 0 := by rw [map_ne_zero]; exact hz
  have e : (conj z)⁻¹ - z = (1 - z * conj z) * (conj z)⁻¹ := by
    rw [sub_mul, one_mul, mul_assoc, mul_inv_cancel₀ hc, mul_one]
  have e2 : (1 : ℂ) - z * conj z = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [e, e2, norm_mul, norm_inv, Complex.norm_conj, Complex.norm_real,
    Real.norm_of_nonneg (by nlinarith), div_eq_mul_inv]

/-- T1 helper: `|1/z̄ − z| ≤ 3(1 − |z|)` for `1/2 ≤ |z| < 1`. -/
theorem s07b_fkph_c_tbd {z : ℂ} (h0 : 1 / 2 ≤ ‖z‖) (h1 : ‖z‖ < 1) :
    ‖(conj z)⁻¹ - z‖ ≤ 3 * (1 - ‖z‖) := by
  have hp : 0 < ‖z‖ := by linarith
  rw [s07b_fkph_c_tnorm hp h1.le, div_le_iff₀ hp]
  nlinarith [mul_nonneg (sub_nonneg.mpr h1.le) (by linarith : (0 : ℝ) ≤ 2 * ‖z‖ - 1)]

/-- T1 helper: `ι z = 1/z̄` expands distances inside `𝔻`. -/
theorem s07b_fkph_c_iotadiff {z₁ z₂ : ℂ} (h₁ : 0 < ‖z₁‖) (h₁' : ‖z₁‖ < 1) (h₂ : 0 < ‖z₂‖)
    (h₂' : ‖z₂‖ < 1) : ‖z₁ - z₂‖ ≤ ‖(conj z₁)⁻¹ - (conj z₂)⁻¹‖ := by
  have hc₁ : conj z₁ ≠ 0 := by rw [map_ne_zero]; exact norm_pos_iff.mp h₁
  have hc₂ : conj z₂ ≠ 0 := by rw [map_ne_zero]; exact norm_pos_iff.mp h₂
  rw [inv_sub_inv hc₁ hc₂, norm_div, norm_mul, ← map_sub]
  simp only [Complex.norm_conj]
  rw [norm_sub_rev z₁ z₂, le_div_iff₀ (mul_pos h₁ h₂)]
  have : ‖z₁‖ * ‖z₂‖ ≤ 1 := by nlinarith
  nlinarith [norm_nonneg (z₂ - z₁)]

/-- T1 helper: `|1/z̄ − w| ≥ 1 − |z|` for `0 < |z| < 1`, `|w| < 1`. -/
theorem s07b_fkph_c_iotalow {z w : ℂ} (h0 : 0 < ‖z‖) (h1 : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    1 - ‖z‖ ≤ ‖(conj z)⁻¹ - w‖ := by
  have h := norm_sub_norm_le ((conj z)⁻¹) w
  rw [norm_inv, Complex.norm_conj] at h
  have hinv : ‖z‖⁻¹ * ‖z‖ = 1 := inv_mul_cancel₀ h0.ne'
  have h2 : ‖z‖⁻¹ * (‖z‖ - 1) ^ 2 = ‖z‖⁻¹ * ‖z‖ * ‖z‖ - 2 * (‖z‖⁻¹ * ‖z‖) + ‖z‖⁻¹ := by ring
  rw [hinv] at h2
  have h3 := mul_nonneg (inv_nonneg.mpr h0.le) (sq_nonneg (‖z‖ - 1))
  linarith

/-- T1 helper (uniform separation): a continuous injective `F` on `𝔻̄` separates points at distance
`≥ η` by a fixed `m > 0` (compactness). -/
theorem s07b_fkph_c_sep {F : ℂ → ℂ} (hFc : ContinuousOn F (closedBall (0 : ℂ) 1))
    (hFi : InjOn F (closedBall (0 : ℂ) 1)) {η : ℝ} (hη : 0 < η) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ closedBall (0 : ℂ) 1, ∀ y ∈ closedBall (0 : ℂ) 1, η ≤ ‖x - y‖ →
      m ≤ ‖F x - F y‖ := by
  obtain ⟨S, hS⟩ : ∃ S : Set (ℂ × ℂ), S = (closedBall (0 : ℂ) 1 ×ˢ closedBall (0 : ℂ) 1) ∩
      {q | η ≤ ‖q.1 - q.2‖} := ⟨_, rfl⟩
  have hSc : IsCompact S := by
    rw [hS]
    exact ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).inter_right
      (isClosed_le continuous_const (continuous_fst.sub continuous_snd).norm)
  have hg : ContinuousOn (fun q : ℂ × ℂ => ‖F q.1 - F q.2‖) S := by
    have h1 : ContinuousOn (fun q : ℂ × ℂ => F q.1) S :=
      hFc.comp continuous_fst.continuousOn (fun q hq => by rw [hS] at hq; exact hq.1.1)
    have h2 : ContinuousOn (fun q : ℂ × ℂ => F q.2) S :=
      hFc.comp continuous_snd.continuousOn (fun q hq => by rw [hS] at hq; exact hq.1.2)
    exact (h1.sub h2).norm
  have hmemS : ∀ x ∈ closedBall (0 : ℂ) 1, ∀ y ∈ closedBall (0 : ℂ) 1, η ≤ ‖x - y‖ → (x, y) ∈ S := by
    intro x hx y hy hxy
    rw [hS]
    exact ⟨⟨hx, hy⟩, hxy⟩
  rcases S.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, ?_⟩
    intro x hx y hy hxy
    have := hmemS x hx y hy hxy
    rw [he] at this
    simp at this
  · obtain ⟨q, hq, hmin⟩ := hSc.exists_isMinOn hne hg
    have hq' := hq
    rw [hS] at hq'
    refine ⟨‖F q.1 - F q.2‖, ?_, ?_⟩
    · rw [norm_pos_iff, sub_ne_zero]
      intro hFq
      have h3 := hFi hq'.1.1 hq'.1.2 hFq
      have h2 : η ≤ ‖q.1 - q.2‖ := hq'.2
      rw [h3, sub_self, norm_zero] at h2
      linarith
    · intro x hx y hy hxy
      exact isMinOn_iff.mp hmin _ (hmemS x hx y hy hxy)

/-- T1 helper (open mapping of the Becker map): if `|∂B(z)| < |∂̄B(z)|`, then `B` maps neighbourhoods
of `z` onto neighbourhoods of `B(z)` (inverse function theorem, via `s07b_fkph_c_dB`). -/
theorem s07b_fkph_c_open {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) {z : ℂ} (hz : z ∈ unitDisc)
    (hz0 : z ≠ 0)
    (hlt : ‖((conj z)⁻¹ - z) * deriv (deriv f) z‖ < ‖((conj z)⁻¹) ^ 2 * deriv f z‖) :
    ∀ U ∈ 𝓝 z, (fun w => f w + ((conj w)⁻¹ - w) * deriv f w) '' U ∈
      𝓝 (f z + ((conj z)⁻¹ - z) * deriv f z) := by
  obtain ⟨hC, hD⟩ := s07b_fkph_c_dB hf hz hz0
  have hinj : Function.Injective
      ((fderiv ℝ (fun w => f w + ((conj w)⁻¹ - w) * deriv f w) z : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    rw [ContinuousLinearMap.coe_coe, hD v] at hv
    have h : ((conj z)⁻¹ - z) * deriv (deriv f) z * v = ((conj z)⁻¹) ^ 2 * deriv f z * conj v :=
      sub_eq_zero.mp hv
    have hn := congrArg norm h
    rw [norm_mul (((conj z)⁻¹ - z) * deriv (deriv f) z) v,
      norm_mul (((conj z)⁻¹) ^ 2 * deriv f z) (conj v), Complex.norm_conj] at hn
    by_contra hv0
    have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    have := mul_right_cancel₀ hvp.ne' hn
    linarith
  obtain ⟨e, he⟩ : ∃ e : ℂ ≃L[ℝ] ℂ, (e : ℂ →L[ℝ] ℂ) =
      fderiv ℝ (fun w => f w + ((conj w)⁻¹ - w) * deriv f w) z :=
    ⟨(LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv,
      ContinuousLinearMap.ext fun v => rfl⟩
  have hS : HasStrictFDerivAt (fun w => f w + ((conj w)⁻¹ - w) * deriv f w) (e : ℂ →L[ℝ] ℂ) z := by
    rw [he]
    exact hC.hasStrictFDerivAt one_ne_zero
  intro U hU
  have := image_mem_map (m := fun w => f w + ((conj w)⁻¹ - w) * deriv f w) hU
  rwa [hS.map_nhds_eq_of_equiv] at this

/-- T1 helper (local injectivity of the Becker map at the hyperbolic scale, from `s07b_fkph_c_aff`). -/
theorem s07b_fkph_c_nearinj {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hf' : ∀ z ∈ unitDisc, deriv f z ≠ 0) {ε η : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 1000) (hη0 : 0 < η)
    (hη : η ≤ 1 / 8)
    (hB : ∀ u : ℂ, 1 - 4 * η < ‖u‖ → ‖u‖ < 1 → (1 - ‖u‖) * ‖deriv (deriv f) u / deriv f u‖ ≤ ε)
    {z₁ z₂ : ℂ} (h₁ : 1 - η < ‖z₁‖) (h₁' : ‖z₁‖ < 1) (h₂ : 1 - η < ‖z₂‖) (h₂' : ‖z₂‖ < 1)
    (hd : ‖z₁ - z₂‖ ≤ η) (hne : z₁ ≠ z₂) :
    f z₁ + ((conj z₁)⁻¹ - z₁) * deriv f z₁ ≠ f z₂ + ((conj z₂)⁻¹ - z₂) * deriv f z₂ := by
  obtain ⟨p, hp, -, E0, E1, E2⟩ :=
    s07b_fkph_c_aff hf hf' hε0 (by linarith) hη0 hη hB h₁ h₁' h₂ h₂' hd
  have hA : 0 < ‖deriv f p‖ := norm_pos_iff.mpr (hf' p hp)
  have hd0 : 0 < ‖z₁ - z₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have ht₁ := s07b_fkph_c_tbd (z := z₁) (by linarith) h₁'
  have ht₂ := s07b_fkph_c_tbd (z := z₂) (by linarith) h₂'
  have hι := s07b_fkph_c_iotadiff (z₁ := z₁) (z₂ := z₂) (by linarith) h₁' (by linarith) h₂'
  intro heq
  have key : deriv f p * ((conj z₁)⁻¹ - (conj z₂)⁻¹) =
      -(f z₁ - f z₂ - deriv f p * (z₁ - z₂)) - ((conj z₁)⁻¹ - z₁) * (deriv f z₁ - deriv f p) +
        ((conj z₂)⁻¹ - z₂) * (deriv f z₂ - deriv f p) := by
    linear_combination heq
  have hn := congrArg norm key
  rw [norm_mul (deriv f p)] at hn
  have a1 := norm_add_le (-(f z₁ - f z₂ - deriv f p * (z₁ - z₂)) -
    ((conj z₁)⁻¹ - z₁) * (deriv f z₁ - deriv f p)) (((conj z₂)⁻¹ - z₂) * (deriv f z₂ - deriv f p))
  have a2 := norm_sub_le (-(f z₁ - f z₂ - deriv f p * (z₁ - z₂)))
    (((conj z₁)⁻¹ - z₁) * (deriv f z₁ - deriv f p))
  rw [norm_neg] at a2
  rw [norm_mul] at a1 a2
  have m1 := mul_le_mul_of_nonneg_right ht₁ (norm_nonneg (deriv f z₁ - deriv f p))
  have m2 := mul_le_mul_of_nonneg_right ht₂ (norm_nonneg (deriv f z₂ - deriv f p))
  have m3 := mul_le_mul_of_nonneg_left hι hA.le
  have m4 := mul_le_mul_of_nonneg_right hε (mul_pos hA hd0).le
  have m5 := mul_pos hA hd0
  linarith

/-- T1 helper (the Becker map avoids `f(𝔻)` near the collar, from `s07b_fkph_c_aff`). -/
theorem s07b_fkph_c_nearom {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hf' : ∀ z ∈ unitDisc, deriv f z ≠ 0) {ε η : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 3200) (hη0 : 0 < η)
    (hη : η ≤ 1 / 8)
    (hB : ∀ u : ℂ, 1 - 4 * η < ‖u‖ → ‖u‖ < 1 → (1 - ‖u‖) * ‖deriv (deriv f) u / deriv f u‖ ≤ ε)
    {z w : ℂ} (h₁ : 1 - η < ‖z‖) (h₁' : ‖z‖ < 1) (h₂ : 1 - η < ‖w‖) (h₂' : ‖w‖ < 1)
    (hd : ‖z - w‖ ≤ η) :
    f z + ((conj z)⁻¹ - z) * deriv f z ≠ f w := by
  obtain ⟨p, hp, -, E0, E1, -⟩ :=
    s07b_fkph_c_aff hf hf' hε0 (by linarith) hη0 hη hB h₁ h₁' h₂ h₂' hd
  have hA : 0 < ‖deriv f p‖ := norm_pos_iff.mpr (hf' p hp)
  have hδ : 0 < 1 - ‖z‖ := by linarith
  have ht := s07b_fkph_c_tbd (z := z) (by linarith) h₁'
  have hl1 := s07b_fkph_c_iotalow (z := z) (w := w) (by linarith) h₁' h₂'
  have hl2 : ‖z - w‖ - 3 * (1 - ‖z‖) ≤ ‖(conj z)⁻¹ - w‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub z ((conj z)⁻¹) w
    rw [norm_sub_rev z ((conj z)⁻¹)] at this
    linarith
  have hl : ‖z - w‖ / 8 + (1 - ‖z‖) / 2 ≤ ‖(conj z)⁻¹ - w‖ := by linarith
  intro heq
  have key : deriv f p * ((conj z)⁻¹ - w) =
      -(f z - f w - deriv f p * (z - w)) - ((conj z)⁻¹ - z) * (deriv f z - deriv f p) := by
    linear_combination heq
  have hn := congrArg norm key
  rw [norm_mul (deriv f p)] at hn
  have a2 := norm_sub_le (-(f z - f w - deriv f p * (z - w)))
    (((conj z)⁻¹ - z) * (deriv f z - deriv f p))
  rw [norm_neg, norm_mul] at a2
  have m1 := mul_le_mul_of_nonneg_right ht (norm_nonneg (deriv f z - deriv f p))
  have m3 := mul_le_mul_of_nonneg_left hl hA.le
  have m4 := mul_le_mul_of_nonneg_right hε (mul_nonneg hA.le (norm_nonneg (z - w)))
  have m5 := mul_pos hA hδ
  linarith

/-- T1 block C2 (collar injectivity of the Becker map, and its image lies off `Ω̄`): for `f` conformal on
`𝔻` with a continuous injective extension `F` to `𝔻̄` and little Bloch, the map
`B(z) = f(z) + (1/z̄ − z) f'(z)` is injective on a thin collar `A_r` and `B(A_r) ∩ Ω̄ = ∅`
(`s07b_fkph_c_aff` at small separation, uniform separation of `F` + `s07b_fkph_c_fprime` at large separation;
`B(z) = f(w)` forces `|w − 1/z̄| ≤ 8·100 ε |w − 1/z̄|`; off `Ω̄` by the open-mapping property of `B`,
`s07b_fkph_c_dB`). -/
theorem s07b_fkph_c_inj {Ω : Set ℂ} {f F : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (hFc : ContinuousOn F (closedBall (0 : ℂ) 1)) (hFi : InjOn F (closedBall (0 : ℂ) 1))
    (hFf : ∀ z ∈ unitDisc, F z = f z)
    (hLB : ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ ∀ z : ℂ, s < ‖z‖ → ‖z‖ < 1 →
      (1 - ‖z‖ ^ 2) * ‖deriv (deriv f) z / deriv f z‖ ≤ ε) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      InjOn (fun z => f z + ((conj z)⁻¹ - z) * deriv f z) {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} ∧
      ∀ z : ℂ, r < ‖z‖ → ‖z‖ < 1 → f z + ((conj z)⁻¹ - z) * deriv f z ∉ closure Ω := by
  have hfd : DifferentiableOn ℂ f unitDisc := hf.1
  have hf' : ∀ z ∈ unitDisc, deriv f z ≠ 0 := fun z hz =>
    deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz
  have hmem : ∀ u : ℂ, ‖u‖ < 1 → u ∈ unitDisc := by
    intro u hu
    show u ∈ Metric.ball (0 : ℂ) 1
    exact mem_ball_zero_iff.mpr hu
  have hcl : ∀ u : ℂ, ‖u‖ < 1 → u ∈ closedBall (0 : ℂ) 1 := fun u hu =>
    mem_closedBall_zero_iff.mpr hu.le
  obtain ⟨s₀, hs₀0, hs₀1, hs₀⟩ := hLB (1 / 10000) (by norm_num)
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min (1 / 16) ((1 - s₀) / 8) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; exact lt_min (by norm_num) (by linarith)
  have hη16 : η ≤ 1 / 16 := by rw [hη]; exact min_le_left _ _
  have hηs : η ≤ (1 - s₀) / 8 := by rw [hη]; exact min_le_right _ _
  have hB : ∀ u : ℂ, 1 - 4 * (2 * η) < ‖u‖ → ‖u‖ < 1 →
      (1 - ‖u‖) * ‖deriv (deriv f) u / deriv f u‖ ≤ 1 / 10000 := by
    intro u hu1 hu2
    have h := hs₀ u (by linarith) hu2
    have hu0 := norm_nonneg u
    have h2 : 1 - ‖u‖ ≤ 1 - ‖u‖ ^ 2 := by nlinarith
    exact (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)).trans h
  obtain ⟨m, hm0, hm⟩ := s07b_fkph_c_sep hFc hFi hη0
  obtain ⟨s₁, hs₁0, hs₁1, hs₁⟩ := s07b_fkph_c_fprime hfd hFc hFf (m / 12) (by positivity)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = max (1 - η) s₁ := ⟨_, rfl⟩
  have hr1 : 1 - η ≤ r := by rw [hr]; exact le_max_left _ _
  have hrs : s₁ ≤ r := by rw [hr]; exact le_max_right _ _
  have hrlt : r < 1 := by rw [hr]; exact max_lt (by linarith) hs₁1
  -- in the collar, `|1/z̄ − z||f'(z)| ≤ 3(1 − |z|)|f'(z)| ≤ m/4`
  have hfar : ∀ z : ℂ, r < ‖z‖ → ‖z‖ < 1 → ‖((conj z)⁻¹ - z) * deriv f z‖ ≤ m / 4 := by
    intro z hz hz1
    rw [norm_mul]
    have h1 := s07b_fkph_c_tbd (z := z) (by linarith) hz1
    have h2 := hs₁ z (by linarith) hz1
    have h3 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (deriv f z))
    linarith
  -- `B(z) ∉ Ω = f(𝔻)` on the collar
  have hnotΩ : ∀ z : ℂ, r < ‖z‖ → ‖z‖ < 1 → f z + ((conj z)⁻¹ - z) * deriv f z ∉ Ω := by
    intro z hz hz1 hin
    rw [← hf.2.2] at hin
    obtain ⟨w, hw, hwe⟩ := hin
    have hw1 : ‖w‖ < 1 := by
      have : w ∈ Metric.ball (0 : ℂ) 1 := hw
      exact mem_ball_zero_iff.mp this
    rcases le_or_gt η ‖z - w‖ with hfa | hne'
    · have h := hm z (hcl _ hz1) w (hcl _ hw1) hfa
      rw [hFf z (hmem _ hz1), hFf w hw] at h
      have e : f z - f w = -(((conj z)⁻¹ - z) * deriv f z) := by linear_combination -hwe
      rw [e, norm_neg] at h
      linarith [hfar z hz hz1]
    · have hw2 : 1 - 2 * η < ‖w‖ := by
        have := norm_le_insert' z w
        linarith
      exact s07b_fkph_c_nearom hfd hf' (by norm_num) (by norm_num) (by linarith) (by linarith) hB
        (by linarith) hz1 hw2 hw1 (by linarith) hwe.symm
  refine ⟨r, by linarith, hrlt, ?_, ?_⟩
  · intro z₁ hz₁ z₂ hz₂ heq
    obtain ⟨hz₁a, hz₁b⟩ := hz₁
    obtain ⟨hz₂a, hz₂b⟩ := hz₂
    simp only at heq
    by_contra hne
    rcases le_or_gt η ‖z₁ - z₂‖ with hfa | hne'
    · have h := hm z₁ (hcl _ hz₁b) z₂ (hcl _ hz₂b) hfa
      rw [hFf z₁ (hmem _ hz₁b), hFf z₂ (hmem _ hz₂b)] at h
      have e : f z₁ - f z₂ =
          ((conj z₂)⁻¹ - z₂) * deriv f z₂ - ((conj z₁)⁻¹ - z₁) * deriv f z₁ := by
        linear_combination heq
      rw [e] at h
      have := norm_sub_le (((conj z₂)⁻¹ - z₂) * deriv f z₂) (((conj z₁)⁻¹ - z₁) * deriv f z₁)
      linarith [hfar z₁ hz₁a hz₁b, hfar z₂ hz₂a hz₂b]
    · exact s07b_fkph_c_nearinj hfd hf' (by norm_num) (by norm_num) (by linarith) (by linarith) hB
        (by linarith) hz₁b (by linarith) hz₂b (by linarith) hne heq
  · intro z hz hz1 hzc
    have hz0' : 0 < ‖z‖ := by linarith
    have hz0 : z ≠ 0 := norm_pos_iff.mp hz0'
    have hzD := hmem z hz1
    have hfz : 0 < ‖deriv f z‖ := norm_pos_iff.mpr (hf' z hzD)
    have hlt : ‖((conj z)⁻¹ - z) * deriv (deriv f) z‖ < ‖((conj z)⁻¹) ^ 2 * deriv f z‖ := by
      have h := hs₀ z (by linarith) hz1
      rw [norm_div, mul_div_assoc', div_le_iff₀ hfz] at h
      rw [norm_mul, norm_mul, norm_pow, norm_inv, Complex.norm_conj,
        s07b_fkph_c_tnorm hz0' hz1.le, div_mul_eq_mul_div, inv_pow, ← div_eq_inv_mul,
        div_lt_div_iff₀ hz0' (pow_pos hz0' 2)]
      have hx2 : ‖z‖ ^ 2 ≤ ‖z‖ := by nlinarith
      have h4 := mul_le_mul_of_nonneg_right h (sq_nonneg ‖z‖)
      have h5 := mul_le_mul_of_nonneg_left hx2 hfz.le
      nlinarith [mul_pos hfz hz0']
    have hU : {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} ∈ 𝓝 z :=
      ((isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨hz, hz1⟩
    have hV := s07b_fkph_c_open hfd hzD hz0 hlt _ hU
    obtain ⟨y, hyV, hyΩ⟩ := mem_closure_iff_nhds.mp hzc _ hV
    obtain ⟨z', hz', hz'e⟩ := hyV
    rw [← hz'e] at hyΩ
    exact hnotΩ z' hz'.1 hz'.2 hyΩ

/-- T1 block C3 (boundary continuity of `g⁻¹`): let `g` map `𝔻*` conformally onto `Ωs` with `g(∞) = ∞`, and
boundary values `g → G(ζ)` at every `ζ ∈ 𝕋` (from outside), `G` injective on `𝕋` with `G(𝕋) ∩ Ωs = ∅`. Then
`g⁻¹(w) → ζ` as `w → G(ζ)` within `Ωs` (compactness; a limit point off `𝕋` would put `G(ζ)` in `Ωs`). -/
theorem s07b_fkph_c_ginv {Ωs : Set ℂ} {g G : ℂ → ℂ} (hg : IsConformalOnto g unitDiscExterior Ωs)
    (hgInf : Tendsto g (cocompact ℂ) (cocompact ℂ))
    (hb : ∀ ζ ∈ sphere (0 : ℂ) 1, Tendsto g (𝓝[unitDiscExterior] ζ) (𝓝 (G ζ)))
    (hGi : InjOn G (sphere (0 : ℂ) 1)) (hGs : ∀ ζ ∈ sphere (0 : ℂ) 1, G ζ ∉ Ωs) :
    ∀ ζ ∈ sphere (0 : ℂ) 1,
      Tendsto (Function.invFunOn g unitDiscExterior) (𝓝[Ωs] (G ζ)) (𝓝 ζ) := by
  intro ζ hζ
  have hUo : IsOpen unitDiscExterior := by
    show IsOpen {w : ℂ | 1 < ‖w‖}
    exact isOpen_lt continuous_const continuous_norm
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ → ℂ, ψ = Function.invFunOn g unitDiscExterior := ⟨_, rfl⟩
  rw [← hψ]
  have hψU : ∀ᶠ w in 𝓝[Ωs] (G ζ), ψ w ∈ unitDiscExterior := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw' : w ∈ g '' unitDiscExterior := by rw [hg.2.2]; exact hw
    rw [hψ]
    exact Function.invFunOn_mem hw'
  have hgψ : Tendsto (fun w => g (ψ w)) (𝓝[Ωs] (G ζ)) (𝓝 (G ζ)) := by
    have hev : ∀ᶠ w in 𝓝[Ωs] (G ζ), id w = g (ψ w) := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw' : w ∈ g '' unitDiscExterior := by rw [hg.2.2]; exact hw
      rw [hψ]
      exact (Function.invFunOn_eq hw').symm
    exact (tendsto_id.mono_right nhdsWithin_le_nhds).congr' hev
  have hmapU : map ψ (𝓝[Ωs] (G ζ)) ≤ 𝓟 unitDiscExterior := tendsto_principal.mpr hψU
  -- a cluster point `x` of `ψ` with `g → c` at `x` (within `𝔻*`) forces `c = G(ζ)`
  have key : ∀ x c, Tendsto g (𝓝[unitDiscExterior] x) (𝓝 c) →
      MapClusterPt x (𝓝[Ωs] (G ζ)) ψ → c = G ζ := by
    intro x c hx hcl
    have hF : (𝓝 x ⊓ map ψ (𝓝[Ωs] (G ζ))).NeBot := ClusterPt.neBot hcl
    have h1 : Tendsto g (𝓝 x ⊓ map ψ (𝓝[Ωs] (G ζ))) (𝓝 c) :=
      hx.mono_left (show 𝓝 x ⊓ map ψ (𝓝[Ωs] (G ζ)) ≤ 𝓝[unitDiscExterior] x from
        le_inf inf_le_left (inf_le_right.trans hmapU))
    have h3 : Tendsto g (map ψ (𝓝[Ωs] (G ζ))) (𝓝 (G ζ)) := tendsto_map'_iff.mpr hgψ
    have h2 : Tendsto g (𝓝 x ⊓ map ψ (𝓝[Ωs] (G ζ))) (𝓝 (G ζ)) := h3.mono_left inf_le_right
    exact tendsto_nhds_unique h1 h2
  -- `ψ` eventually lies in a compact subset of `{|z| ≥ 1}`
  have hcc := hgInf (isCompact_closedBall (G ζ) 1).compl_mem_cocompact
  obtain ⟨K, hK, hKsub⟩ := mem_cocompact.mp (mem_map.mp hcc)
  have hs : IsCompact (K ∩ {z : ℂ | 1 ≤ ‖z‖}) :=
    hK.inter_right (isClosed_le continuous_const continuous_norm)
  have hmem : ∀ᶠ w in 𝓝[Ωs] (G ζ), ψ w ∈ K ∩ {z : ℂ | 1 ≤ ‖z‖} := by
    filter_upwards [hψU, inter_mem_nhdsWithin Ωs (ball_mem_nhds (G ζ) one_pos)] with w hw1 hw2
    have hw' : w ∈ g '' unitDiscExterior := by rw [hg.2.2]; exact hw2.1
    have hgw : g (ψ w) = w := by rw [hψ]; exact Function.invFunOn_eq hw'
    have hn : 1 < ‖ψ w‖ := hw1
    refine ⟨?_, hn.le⟩
    by_contra hk
    have h := hKsub hk
    apply h
    show g (ψ w) ∈ closedBall (G ζ) 1
    rw [hgw]
    exact ball_subset_closedBall hw2.2
  refine hs.tendsto_nhds_of_unique_mapClusterPt hmem ?_
  intro x hx hcl
  have hx1 : 1 ≤ ‖x‖ := hx.2
  rcases eq_or_lt_of_le hx1 with h1 | h1
  · have hxs : x ∈ sphere (0 : ℂ) 1 := by rw [mem_sphere_zero_iff_norm]; exact h1.symm
    exact hGi hxs hζ (key x (G x) (hb x hxs) hcl)
  · exfalso
    have hxU : x ∈ unitDiscExterior := h1
    have hc : Tendsto g (𝓝[unitDiscExterior] x) (𝓝 (g x)) :=
      ((hg.1 x hxU).differentiableAt (hUo.mem_nhds hxU)).continuousAt.continuousWithinAt
    have hgx := key x (g x) hc hcl
    apply hGs ζ hζ
    rw [← hgx, ← hg.2.2]
    exact Set.mem_image_of_mem g hxU

/-- T1 helper: a circle homeomorphism has a continuous right inverse on `𝕋` (via the induced bijection
of `Circle`, `s07_de_circleMap`, and compactness), and is injective on `𝕋`. -/
theorem s07b_fkph_c_circinv {h : ℂ → ℂ} (hh : IsCircleHomeo h) :
    ∃ k : ℂ → ℂ, (∀ ζ ∈ sphere (0 : ℂ) 1, k ζ ∈ sphere (0 : ℂ) 1 ∧ h (k ζ) = ζ) ∧
      ContinuousOn k (sphere (0 : ℂ) 1) ∧ InjOn h (sphere (0 : ℂ) 1) := by
  classical
  obtain ⟨c, hcb, hcc, -, hcv⟩ := s07_de_circleMap hh
  have hcc' : Continuous (Equiv.ofBijective c hcb) := hcc
  obtain ⟨e, he⟩ : ∃ e : Circle ≃ₜ Circle, e = hcc'.homeoOfEquivCompactToT2 := ⟨_, rfl⟩
  have hec : ∀ x, e x = c x := by
    intro x
    rw [he]
    rfl
  obtain ⟨j, hj⟩ : ∃ j : sphere (0 : ℂ) 1 → Circle, j = fun x => ⟨x.1, x.2⟩ := ⟨_, rfl⟩
  have jcoe : ∀ x, ((j x : Circle) : ℂ) = x.1 := by
    intro x
    rw [hj]
  obtain ⟨k, hk⟩ : ∃ k : ℂ → ℂ, k = fun ζ =>
      if hζ : ζ ∈ sphere (0 : ℂ) 1 then ((e.symm (j ⟨ζ, hζ⟩) : Circle) : ℂ) else 0 := ⟨_, rfl⟩
  have hkS : ∀ ζ (hζ : ζ ∈ sphere (0 : ℂ) 1), k ζ = ((e.symm (j ⟨ζ, hζ⟩) : Circle) : ℂ) := by
    intro ζ hζ
    rw [hk]
    exact dif_pos hζ
  refine ⟨k, fun ζ hζ => ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hkS ζ hζ]
    exact (e.symm (j ⟨ζ, hζ⟩)).2
  · rw [hkS ζ hζ, ← hcv, ← hec, Homeomorph.apply_symm_apply, jcoe]
  · refine continuousOn_iff_continuous_domRestrict.mpr ?_
    have heq : (fun x : sphere (0 : ℂ) 1 => k x.1) = fun x => ((e.symm (j x) : Circle) : ℂ) := by
      funext x
      exact hkS x.1 x.2
    show Continuous fun x : sphere (0 : ℂ) 1 => k x.1
    rw [heq]
    have hjc : Continuous j := by
      rw [hj]
      exact continuous_subtype_val.subtype_mk _
    have hvc : Continuous fun x : Circle => (x : ℂ) := by
      exact continuous_subtype_val
    exact hvc.comp (e.symm.continuous.comp hjc)
  · intro a ha b hb hab
    have h1 : c (j ⟨a, ha⟩) = c (j ⟨b, hb⟩) := by
      apply Circle.ext
      rw [hcv, hcv, jcoe, jcoe]
      exact hab
    have h2 := hcb.1 h1
    have h3 : ((j ⟨a, ha⟩ : Circle) : ℂ) = ((j ⟨b, hb⟩ : Circle) : ℂ) := by rw [h2]
    rw [jcoe, jcoe] at h3
    exact h3

/-- T1 helper: `|−(1 − |z|²) z c̄| = |z|(1 − |z|²)|c|` on `𝔻̄`. -/
theorem s07b_fkph_c_munorm {z : ℂ} (hz : ‖z‖ ≤ 1) (c : ℂ) :
    ‖-(((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * z * conj c)‖ = ‖z‖ * ((1 - ‖z‖ ^ 2) * ‖c‖) := by
  have h0 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  rw [norm_neg, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg h0]
  ring

/-- T1 helper: `|z| (1 − |z|²)|c| ≤ ε` from `(1 − |z|²)|c| ≤ ε` on `𝔻̄`. -/
theorem s07b_fkph_c_le1 {z c : ℂ} {ε : ℝ} (hz : ‖z‖ ≤ 1) (h : (1 - ‖z‖ ^ 2) * ‖c‖ ≤ ε) :
    ‖z‖ * ((1 - ‖z‖ ^ 2) * ‖c‖) ≤ ε := by
  have hnn : 0 ≤ (1 - ‖z‖ ^ 2) * ‖c‖ := mul_nonneg (by nlinarith [norm_nonneg z]) (norm_nonneg _)
  calc ‖z‖ * ((1 - ‖z‖ ^ 2) * ‖c‖) ≤ 1 * ((1 - ‖z‖ ^ 2) * ‖c‖) :=
        mul_le_mul_of_nonneg_right hz hnn
    _ ≤ ε := by rw [one_mul]; exact h

/-- T1 helper: the reflection `ι ζ = 1/ζ̄` fixes `𝕋`. -/
theorem s07b_fkph_c_iota {ζ : ℂ} (hζ : ‖ζ‖ = 1) : conj (ζ⁻¹) = ζ := by
  have h : ζ * conj ζ = 1 := by
    rw [Complex.mul_conj', hζ]
    norm_num
  rw [map_inv₀]
  exact inv_eq_of_mul_eq_one_left h

/-- T1 helper: off `Ω̄ = T(𝔻̄)` lies in `Ωs = T(𝔻*)`. -/
theorem s07b_fkph_c_cls {Ω Ωs : Set ℂ} (T : ℂ ≃ₜ ℂ) (hF1 : T '' unitDisc = Ω)
    (hF2 : T '' unitDiscExterior = Ωs) {y : ℂ} (hy : y ∉ closure Ω) : y ∈ Ωs := by
  have hcl : closure Ω = T '' closedBall (0 : ℂ) 1 := by
    rw [← hF1, ← T.image_closure]
    show T '' closure (ball (0 : ℂ) 1) = _
    rw [closure_ball (0 : ℂ) one_ne_zero]
  rw [← hF2]
  refine ⟨T.symm y, ?_, T.apply_symm_apply y⟩
  show 1 < ‖T.symm y‖
  by_contra hle
  apply hy
  rw [hcl]
  exact ⟨T.symm y, mem_closedBall_zero_iff.mpr (not_lt.mp hle), T.apply_symm_apply y⟩

/-- T1 helper: `T(𝕋)` misses `Ωs = T(𝔻*)`. -/
theorem s07b_fkph_c_bdnot {Ωs : Set ℂ} (T : ℂ ≃ₜ ℂ) (hF2 : T '' unitDiscExterior = Ωs) {y : ℂ}
    (hy : y ∈ T '' sphere (0 : ℂ) 1) : y ∉ Ωs := by
  intro hyΩ
  rw [← hF2] at hyΩ
  obtain ⟨a, ha, hay⟩ := hy
  obtain ⟨b, hb, hby⟩ := hyΩ
  have hab : b = a := T.injective (hby.trans hay.symm)
  have hb1 : 1 < ‖b‖ := hb
  rw [hab, mem_sphere_zero_iff_norm.mp ha] at hb1
  exact lt_irrefl _ hb1

/-- T1 helper: the boundary values of `g` at `ζ ∈ 𝕋` are `f̄(h(ζ))`. -/
theorem s07b_fkph_c_bval {f g h φ : ℂ → ℂ}
    (hhb : ∀ ζ ∈ sphere (0 : ℂ) 1, ∃ x : ℂ, Tendsto f (𝓝[unitDisc] (h ζ)) (𝓝 x) ∧
      Tendsto g (𝓝[unitDiscExterior] ζ) (𝓝 x))
    (hhS : MapsTo h (sphere 0 1) (sphere 0 1))
    (hφc : ContinuousOn φ (closedBall (0 : ℂ) 1)) (hφf : ∀ z ∈ unitDisc, φ z = f z) :
    ∀ ζ ∈ sphere (0 : ℂ) 1, Tendsto g (𝓝[unitDiscExterior] ζ) (𝓝 (φ (h ζ))) := by
  intro ζ hζ
  obtain ⟨x, hfx, hgx⟩ := hhb ζ hζ
  have hξ : h ζ ∈ sphere (0 : ℂ) 1 := hhS hζ
  have hne : (𝓝[unitDisc] (h ζ)).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.1
    show h ζ ∈ closure (ball (0 : ℂ) 1)
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact sphere_subset_closedBall hξ
  have h1 : Tendsto φ (𝓝[unitDisc] (h ζ)) (𝓝 (φ (h ζ))) :=
    (hφc (h ζ) (sphere_subset_closedBall hξ)).mono ball_subset_closedBall
  have h2 : Tendsto f (𝓝[unitDisc] (h ζ)) (𝓝 (φ (h ζ))) :=
    h1.congr' (eventually_nhdsWithin_of_forall fun z hz => hφf z hz)
  have hx : x = φ (h ζ) := tendsto_nhds_unique hfx h2
  rw [← hx]
  exact hgx

/-- T1 helper: the Becker map tends to `f̄(ζ)` at `ζ ∈ 𝕋` from the collar `{1/2 < |z| < 1}`
(`(1/z̄ − z) f'(z) → 0` by `s07b_fkph_c_fprime`). -/
theorem s07b_fkph_c_Blim {f φ : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hφc : ContinuousOn φ (closedBall (0 : ℂ) 1)) (hφf : ∀ z ∈ unitDisc, φ z = f z)
    {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) :
    Tendsto (fun w => f w + ((conj w)⁻¹ - w) * deriv f w)
      (𝓝[{z : ℂ | 1 / 2 < ‖z‖ ∧ ‖z‖ < 1}] ζ) (𝓝 (φ ζ)) := by
  have hsub : {z : ℂ | 1 / 2 < ‖z‖ ∧ ‖z‖ < 1} ⊆ unitDisc := by
    intro z hz
    show z ∈ Metric.ball (0 : ℂ) 1
    exact mem_ball_zero_iff.mpr hz.2
  have h1 : Tendsto f (𝓝[{z : ℂ | 1 / 2 < ‖z‖ ∧ ‖z‖ < 1}] ζ) (𝓝 (φ ζ)) := by
    have h0 : Tendsto φ (𝓝[{z : ℂ | 1 / 2 < ‖z‖ ∧ ‖z‖ < 1}] ζ) (𝓝 (φ ζ)) :=
      (hφc ζ (sphere_subset_closedBall hζ)).mono (hsub.trans ball_subset_closedBall)
    exact h0.congr' (eventually_nhdsWithin_of_forall fun z hz => hφf z (hsub hz))
  have h2 : Tendsto (fun w => ((conj w)⁻¹ - w) * deriv f w)
      (𝓝[{z : ℂ | 1 / 2 < ‖z‖ ∧ ‖z‖ < 1}] ζ) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨s, hs0, hs1, hs⟩ := s07b_fkph_c_fprime hf hφc hφf (ε / 8) (by positivity)
    have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
    have hev : ∀ᶠ w in 𝓝 ζ, s < ‖w‖ :=
      (continuous_norm.tendsto ζ).eventually (lt_mem_nhds (by rw [hζ1]; exact hs1))
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with w hw hwA
    have hw1 : 1 / 2 < ‖w‖ := hwA.1
    have hw2 : ‖w‖ < 1 := hwA.2
    have hb := hs w hw hw2
    rw [dist_zero_right, norm_mul, s07b_fkph_c_tnorm (by linarith) hw2.le]
    have ht : (1 - ‖w‖ ^ 2) / ‖w‖ ≤ 4 * (1 - ‖w‖) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 3 * ‖w‖ - 1) (by linarith : (0 : ℝ) < 1 - ‖w‖)]
    calc (1 - ‖w‖ ^ 2) / ‖w‖ * ‖deriv f w‖ ≤ 4 * (1 - ‖w‖) * ‖deriv f w‖ :=
          mul_le_mul_of_nonneg_right ht (norm_nonneg _)
      _ = 4 * ((1 - ‖w‖) * ‖deriv f w‖) := by ring
      _ ≤ 4 * (ε / 8) := mul_le_mul_of_nonneg_left hb (by norm_num)
      _ < ε := by linarith
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact h3

/-- T1 helper: `ι ∘ g⁻¹ ∘ B` tends to `ζ'` at a boundary point, if `B → G(ζ')` from `A` with
`B(A) ⊆ Ωs` (`s07b_fkph_c_ginv`, then continuity of `ι` at `ζ' ∈ 𝕋`). -/
theorem s07b_fkph_c_bdlim {Ωs A : Set ℂ} {g G Bf : ℂ → ℂ}
    (hg : IsConformalOnto g unitDiscExterior Ωs) (hgInf : Tendsto g (cocompact ℂ) (cocompact ℂ))
    (hb : ∀ ζ ∈ sphere (0 : ℂ) 1, Tendsto g (𝓝[unitDiscExterior] ζ) (𝓝 (G ζ)))
    (hGi : InjOn G (sphere (0 : ℂ) 1)) (hGs : ∀ ζ ∈ sphere (0 : ℂ) 1, G ζ ∉ Ωs)
    (hBA : ∀ z ∈ A, Bf z ∈ Ωs) {ζ ζ' : ℂ} (hζ' : ζ' ∈ sphere (0 : ℂ) 1)
    (hBl : Tendsto Bf (𝓝[A] ζ) (𝓝 (G ζ'))) :
    Tendsto (fun z => conj ((Function.invFunOn g unitDiscExterior (Bf z))⁻¹)) (𝓝[A] ζ)
      (𝓝 ζ') := by
  have h1 := s07b_fkph_c_ginv hg hgInf hb hGi hGs ζ' hζ'
  have h2 : Tendsto Bf (𝓝[A] ζ) (𝓝[Ωs] (G ζ')) :=
    tendsto_nhdsWithin_iff.mpr ⟨hBl, eventually_nhdsWithin_of_forall hBA⟩
  have h3 := h1.comp h2
  have hn : ‖ζ'‖ = 1 := mem_sphere_zero_iff_norm.mp hζ'
  have hζ0 : ζ' ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  have h4 := (Complex.continuous_conj.tendsto _).comp ((tendsto_inv₀ hζ0).comp h3)
  rw [s07b_fkph_c_iota hn] at h4
  exact h4

/-- **T1** (Becker–Pommerenke collar). For a bounded quasicircle with welding `h` and `log f' ∈ VMOA`,
there is a collar `A_r = {r < |z| < 1}` and a map `Φ`, `K'`-qc on `A_r`, continuous and injective on
`A_r ∪ 𝕋`, mapping `A_r` into `𝔻` and `𝕋` to `𝕋` with `h ∘ Φ = id` on `𝕋` (so `Φ|_𝕋 = h⁻¹`), whose
dilatation tends to `0` at `𝕋` and, for every `ε > 0`, has on a thinner collar `A_s` a measurable
Whitney majorant `a` (`|μ_Φ| ≤ a(z)` a.e. on `D(z, (1-|z|)/2) ∩ A_s`, `z ∈ 𝔻`) whose Carleson measure
`a(z)²/(1-|z|²) dA` on `𝔻` has norm `≤ ε`. (`Φ = ι ∘ g⁻¹ ∘ F_B ∘ ι`, `ι z = 1/z̄`,
`F_B(w) = f(1/w̄) + (w - 1/w̄) f'(1/w̄)`.) -/
theorem s07b_fkph_collar {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K)
    {f g h : ℂ → ℂ} (hw : IsDiskWelding Ω Ωs f g h) (hf : LogDerivVMOA f) :
    ∃ (r K' : ℝ) (Φ : ℂ → ℂ), 0 < r ∧ r < 1 ∧
      IsKQC Φ {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} K' ∧
      ContinuousOn Φ {z : ℂ | r < ‖z‖ ∧ ‖z‖ ≤ 1} ∧ InjOn Φ {z : ℂ | r < ‖z‖ ∧ ‖z‖ ≤ 1} ∧
      MapsTo Φ {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} unitDisc ∧
      (∀ ζ ∈ sphere (0 : ℂ) 1, Φ ζ ∈ sphere (0 : ℂ) 1 ∧ h (Φ ζ) = ζ) ∧
      (∀ ε : ℝ, 0 < ε → ∃ s : ℝ, r ≤ s ∧ s < 1 ∧
        ∀ᵐ z, s < ‖z‖ → ‖z‖ < 1 → ‖LiZhongQC.complexDilatation Φ z‖ ≤ ε) ∧
      (∀ ε : ℝ, 0 < ε → ∃ (s : ℝ) (a : ℂ → ℝ), r ≤ s ∧ s < 1 ∧ Measurable a ∧ (∀ z, 0 ≤ a z) ∧
        (∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) → s < ‖w‖ →
          ‖LiZhongQC.complexDilatation Φ w‖ ≤ a z) ∧
        ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ ρ : ℝ, 0 < ρ → ρ < 2 →
          ∫⁻ z in unitDisc ∩ ball ζ ρ, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
            ≤ ENNReal.ofReal (ε * ρ)) := by
  obtain ⟨hfc, hg, hgInf, hhS, hhb⟩ := id hw
  obtain ⟨F, hFq, hFs, hF1, hF2⟩ := id hq
  obtain ⟨T, hT⟩ := t1_homeomorph hFq hFs
  rw [← hT] at hF1 hF2
  obtain ⟨φ, hφc, hφi, hφf, hφs⟩ :=
    s07_carath_core T.continuous.continuousOn T.injective.injOn hF1 hfc
  obtain ⟨H, hHq, hHs, hHb⟩ := s07_weld_admitsExt hq hw
  have hh := s07_circleHomeo_of_qcExt hHq hHs hHb
  obtain ⟨k, hkS, hkc, hhi⟩ := s07b_fkph_c_circinv hh
  have hLB := s07b_fkph_c_bloch hfc hf
  obtain ⟨r₀, -, hr₀1, hinj, hnotΩ⟩ := s07b_fkph_c_inj hfc hφc hφi hφf hLB
  obtain ⟨r₁, -, hr₁1, hr₁⟩ := hLB (1 / 2) (by norm_num)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = max (max r₀ r₁) (1 / 2) := ⟨_, rfl⟩
  have hrr₀ : r₀ ≤ r := by rw [hr]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hrr₁ : r₁ ≤ r := by rw [hr]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hrh : 1 / 2 ≤ r := by rw [hr]; exact le_max_right _ _
  have hr1 : r < 1 := by rw [hr]; exact max_lt (max_lt hr₀1 hr₁1) (by norm_num)
  -- the Becker map, `g⁻¹`, and the collar map
  obtain ⟨Bf, hBf⟩ : ∃ Bf : ℂ → ℂ, Bf = fun z => f z + ((conj z)⁻¹ - z) * deriv f z := ⟨_, rfl⟩
  have hBz : ∀ z, Bf z = f z + ((conj z)⁻¹ - z) * deriv f z := by
    intro z
    rw [hBf]
  rw [← hBf] at hinj
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ → ℂ, ψ = Function.invFunOn g unitDiscExterior := ⟨_, rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℂ → ℂ, Φ = fun z => if ‖z‖ = 1 then k z else conj ((ψ (Bf z))⁻¹) :=
    ⟨_, rfl⟩
  have hΦS : ∀ z, ‖z‖ = 1 → Φ z = k z := by
    intro z hz
    rw [hΦ]
    exact if_pos hz
  have hΦA : ∀ z, ‖z‖ ≠ 1 → Φ z = conj ((ψ (Bf z))⁻¹) := by
    intro z hz
    rw [hΦ]
    exact if_neg hz
  have hAo : IsOpen {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hBΩs : ∀ z, r < ‖z‖ → ‖z‖ < 1 → Bf z ∈ Ωs := by
    intro z h1 h2
    refine s07b_fkph_c_cls T hF1 hF2 ?_
    rw [hBz]
    exact hnotΩ z (lt_of_le_of_lt hrr₀ h1) h2
  have hψ1 : ∀ y ∈ Ωs, ψ y ∈ unitDiscExterior ∧ g (ψ y) = y := by
    intro y hy
    have hy' : y ∈ g '' unitDiscExterior := by rw [hg.2.2]; exact hy
    rw [hψ]
    exact ⟨Function.invFunOn_mem hy', Function.invFunOn_eq hy'⟩
  -- dilatation on the collar
  have hdil : ∀ z, r < ‖z‖ → ‖z‖ < 1 → ContDiffAt ℝ 1 Φ z ∧ LiZhongQC.dz Φ z ≠ 0 ∧
      LiZhongQC.complexDilatation Φ z =
        -(((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * z * conj (deriv (deriv f) z / deriv f z)) := by
    intro z h1 h2
    have hz : z ∈ unitDisc := by
      show z ∈ Metric.ball (0 : ℂ) 1
      exact mem_ball_zero_iff.mpr h2
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h1
      linarith only [h1, hrh]
    refine s07b_fkph_c_dil hfc hg hz hz0 ?_ ?_
    · have h := hBΩs z h1 h2
      rw [hBz] at h
      exact h
    · filter_upwards [hAo.mem_nhds ⟨h1, h2⟩] with w hw
      rw [hΦA w (ne_of_lt hw.2), hψ, hBz]
  have hmuN : ∀ z, r < ‖z‖ → ‖z‖ < 1 → ‖LiZhongQC.complexDilatation Φ z‖ =
      ‖z‖ * ((1 - ‖z‖ ^ 2) * ‖deriv (deriv f) z / deriv f z‖) := by
    intro z h1 h2
    rw [(hdil z h1 h2).2.2]
    exact s07b_fkph_c_munorm h2.le _
  have hΦin : ∀ z, r < ‖z‖ → ‖z‖ < 1 → ‖Φ z‖ < 1 := by
    intro z h1 h2
    rw [hΦA z (ne_of_lt h2), Complex.norm_conj, norm_inv]
    have hn : 1 < ‖ψ (Bf z)‖ := (hψ1 _ (hBΩs z h1 h2)).1
    exact (inv_lt_one₀ (by linarith)).mpr hn
  -- injectivity on `A_r ∪ 𝕋`
  have hinjA : InjOn Φ {z : ℂ | r < ‖z‖ ∧ ‖z‖ ≤ 1} := by
    intro z₁ hz₁ z₂ hz₂ he
    have hz₁' : r < ‖z₁‖ ∧ ‖z₁‖ ≤ 1 := hz₁
    have hz₂' : r < ‖z₂‖ ∧ ‖z₂‖ ≤ 1 := hz₂
    rcases eq_or_lt_of_le hz₁'.2 with e1 | e1 <;> rcases eq_or_lt_of_le hz₂'.2 with e2 | e2
    · rw [hΦS z₁ e1, hΦS z₂ e2] at he
      rw [← (hkS z₁ (mem_sphere_zero_iff_norm.mpr e1)).2,
        ← (hkS z₂ (mem_sphere_zero_iff_norm.mpr e2)).2, he]
    · exfalso
      have n1 : ‖Φ z₁‖ = 1 := by
        rw [hΦS z₁ e1]
        exact mem_sphere_zero_iff_norm.mp (hkS z₁ (mem_sphere_zero_iff_norm.mpr e1)).1
      have n2 := hΦin z₂ hz₂'.1 e2
      rw [he] at n1
      linarith
    · exfalso
      have n2 : ‖Φ z₂‖ = 1 := by
        rw [hΦS z₂ e2]
        exact mem_sphere_zero_iff_norm.mp (hkS z₂ (mem_sphere_zero_iff_norm.mpr e2)).1
      have n1 := hΦin z₁ hz₁'.1 e1
      rw [he] at n1
      linarith
    · rw [hΦA z₁ (ne_of_lt e1), hΦA z₂ (ne_of_lt e2)] at he
      have h1 : ψ (Bf z₁) = ψ (Bf z₂) := inv_injective ((starRingEnd ℂ).injective he)
      have h2 : Bf z₁ = Bf z₂ := by
        rw [← (hψ1 _ (hBΩs z₁ hz₁'.1 e1)).2, ← (hψ1 _ (hBΩs z₂ hz₂'.1 e2)).2, h1]
      exact hinj ⟨lt_of_le_of_lt hrr₀ hz₁'.1, e1⟩ ⟨lt_of_le_of_lt hrr₀ hz₂'.1, e2⟩ h2
  -- quasiconformality on `A_r`
  have hCD : ContDiffOn ℝ 1 Φ {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} :=
    fun z hz => (hdil z hz.1 hz.2).1.contDiffWithinAt
  have hKQC : IsKQC Φ {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} 3 := by
    refine isKQC_of_isC1Quasiconformal ⟨hAo, by norm_num, hCD,
      qcl_f_isHomeomorphOnto_of_injOn hAo hCD.continuousOn
        (hinjA.mono (show {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} ⊆ {z : ℂ | r < ‖z‖ ∧ ‖z‖ ≤ 1} from
          fun z hz => ⟨hz.1, hz.2.le⟩)), fun z hz => ?_⟩
    obtain ⟨-, hdz0, -⟩ := hdil z hz.1 hz.2
    have hm2 : ‖LiZhongQC.complexDilatation Φ z‖ ≤ 1 / 2 := by
      rw [hmuN z hz.1 hz.2]
      exact s07b_fkph_c_le1 hz.2.le (hr₁ z (lt_of_le_of_lt hrr₁ hz.1) hz.2)
    have hdzbar : LiZhongQC.dzbar Φ z = LiZhongQC.complexDilatation Φ z * LiZhongQC.dz Φ z := by
      show LiZhongQC.dzbar Φ z = LiZhongQC.dzbar Φ z / LiZhongQC.dz Φ z * LiZhongQC.dz Φ z
      rw [div_mul_cancel₀ _ hdz0]
    have hdzn : 0 < ‖LiZhongQC.dz Φ z‖ := norm_pos_iff.mpr hdz0
    refine ⟨?_, ?_⟩
    · rw [hdzbar, norm_mul]
      calc ‖LiZhongQC.complexDilatation Φ z‖ * ‖LiZhongQC.dz Φ z‖
          ≤ 1 / 2 * ‖LiZhongQC.dz Φ z‖ := mul_le_mul_of_nonneg_right hm2 hdzn.le
        _ < ‖LiZhongQC.dz Φ z‖ := by linarith
    · show (1 + ‖LiZhongQC.complexDilatation Φ z‖) / (1 - ‖LiZhongQC.complexDilatation Φ z‖) ≤ 3
      rw [div_le_iff₀ (by linarith)]
      linarith
  -- continuity on `A_r ∪ 𝕋`
  have hbv := s07b_fkph_c_bval hhb hhS hφc hφf
  have hGi : InjOn (fun x => φ (h x)) (sphere (0 : ℂ) 1) := by
    intro a ha b hb hab
    exact hhi ha hb (hφi (sphere_subset_closedBall (hhS ha)) (sphere_subset_closedBall (hhS hb)) hab)
  have hGs : ∀ ζ ∈ sphere (0 : ℂ) 1, (fun x => φ (h x)) ζ ∉ Ωs := by
    intro ζ hζ
    refine s07b_fkph_c_bdnot T hF2 ?_
    rw [← hφs]
    exact mem_image_of_mem φ (hhS hζ)
  have hcont : ContinuousOn Φ {z : ℂ | r < ‖z‖ ∧ ‖z‖ ≤ 1} := by
    intro z hz
    have hz' : r < ‖z‖ ∧ ‖z‖ ≤ 1 := hz
    rcases eq_or_lt_of_le hz'.2 with e | e
    · have hzS : z ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr e
      obtain ⟨hkz, hhk⟩ := hkS z hzS
      have hin : Tendsto Φ (𝓝[{w : ℂ | r < ‖w‖ ∧ ‖w‖ < 1}] z) (𝓝 (k z)) := by
        have hBl0 := s07b_fkph_c_Blim hfc.1 hφc hφf hzS
        have hBl : Tendsto Bf (𝓝[{w : ℂ | r < ‖w‖ ∧ ‖w‖ < 1}] z) (𝓝 (φ (h (k z)))) := by
          rw [hhk, hBf]
          refine hBl0.mono_left (nhdsWithin_mono z ?_)
          intro w hw
          exact ⟨lt_of_le_of_lt hrh hw.1, hw.2⟩
        have hlim := s07b_fkph_c_bdlim (G := fun x => φ (h x)) (Bf := Bf)
          (A := {w : ℂ | r < ‖w‖ ∧ ‖w‖ < 1}) hg hgInf hbv hGi hGs
          (fun w hw => hBΩs w hw.1 hw.2) hkz hBl
        refine hlim.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with w hw
        rw [hΦA w (ne_of_lt hw.2), hψ]
      have hon : Tendsto Φ (𝓝[sphere (0 : ℂ) 1] z) (𝓝 (k z)) := by
        have hk1 : Tendsto k (𝓝[sphere (0 : ℂ) 1] z) (𝓝 (k z)) := hkc z hzS
        refine hk1.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with w hw
        rw [hΦS w (mem_sphere_zero_iff_norm.mp hw)]
      have hun : Tendsto Φ (𝓝[{w : ℂ | r < ‖w‖ ∧ ‖w‖ < 1} ∪ sphere (0 : ℂ) 1] z) (𝓝 (k z)) := by
        rw [nhdsWithin_union]
        exact hin.sup hon
      show Tendsto Φ (𝓝[{z : ℂ | r < ‖z‖ ∧ ‖z‖ ≤ 1}] z) (𝓝 (Φ z))
      rw [hΦS z e]
      refine hun.mono_left (nhdsWithin_mono z ?_)
      intro w hw
      have hw' : r < ‖w‖ ∧ ‖w‖ ≤ 1 := hw
      rcases eq_or_lt_of_le hw'.2 with e' | e'
      · exact Or.inr (mem_sphere_zero_iff_norm.mpr e')
      · exact Or.inl ⟨hw'.1, e'⟩
    · exact (hdil z hz'.1 e).1.continuousAt.continuousWithinAt
  refine ⟨r, 3, Φ, by linarith only [hrh], hr1, hKQC, hcont, hinjA, ?_, ?_, ?_, ?_⟩
  · intro z hz
    show Φ z ∈ Metric.ball (0 : ℂ) 1
    exact mem_ball_zero_iff.mpr (hΦin z hz.1 hz.2)
  · intro ζ hζ
    rw [hΦS ζ (mem_sphere_zero_iff_norm.mp hζ)]
    exact hkS ζ hζ
  · intro ε hε
    obtain ⟨s', -, hs'1, hs'⟩ := hLB ε hε
    refine ⟨max s' r, le_max_right _ _, max_lt hs'1 hr1, Filter.Eventually.of_forall ?_⟩
    intro z h1 h2
    have h1' : r < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) h1
    rw [hmuN z h1' h2]
    exact s07b_fkph_c_le1 h2.le (hs' z (lt_of_le_of_lt (le_max_left _ _) h1) h2)
  · intro ε hε
    obtain ⟨s, a, hrs, hs1, ham, ha0, hapt, haC⟩ := s07b_fkph_c_major hfc hf ε hε r hr1
    refine ⟨s, a, hrs, hs1, ham, ha0, fun z hz => Filter.Eventually.of_forall ?_, haC⟩
    intro w hw hsw
    have hw' := hw
    rw [mem_ball, dist_eq_norm] at hw'
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have tw := norm_le_insert' w z
    have hw1 : ‖w‖ < 1 := by linarith only [hw', tw, hz1]
    rw [hmuN w (lt_of_le_of_lt hrs hsw) hw1]
    exact hapt z hz w hw hsw


/-- The dilatation of the reflection `ι ∘ f ∘ ι`, `ι z = (z̄)⁻¹`:
`μ_{ι∘f∘ι}(z) = conj(μ_f(ι z)) · z² / z̄²`. -/
theorem s07b_fkph_t_refl_dil {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0)
    (hd : DifferentiableAt ℝ f (conj z)⁻¹) (hf0 : f (conj z)⁻¹ ≠ 0) :
    LiZhongQC.complexDilatation (fun w => (conj (f (conj w)⁻¹))⁻¹) z =
      conj (LiZhongQC.complexDilatation f (conj z)⁻¹) * (z ^ 2 / conj z ^ 2) := by
  set g : ℂ → ℂ := fun w => conj (f (conj w)) with hg
  have hF : (fun w => (conj (f (conj w)⁻¹))⁻¹) = nxInvConj g := by
    funext w
    show (conj (f (conj w)⁻¹))⁻¹ = (conj (f (conj w⁻¹)))⁻¹
    rw [map_inv₀]
  have hd' : DifferentiableAt ℝ f (conj z⁻¹) := by rwa [map_inv₀]
  obtain ⟨hgd, hdz, hdzbar⟩ := abR_x_dz_dzbar_conj hd'
  have hgz : g z⁻¹ ≠ 0 := (map_ne_zero _).2 (by rwa [map_inv₀])
  have h1 : LiZhongQC.complexDilatation g z⁻¹ =
      conj (LiZhongQC.complexDilatation f (conj z)⁻¹) := by
    show dzbar g z⁻¹ / dz g z⁻¹ = conj (dzbar f (conj z)⁻¹ / dz f (conj z)⁻¹)
    rw [hdz, hdzbar, map_inv₀, map_div₀]
  rw [hF, nxI2_dilatation_invConj_at hz hgz hgd, h1]

/-- A.e. statements transport along the reflection `ι z = (z̄)⁻¹`. -/
theorem s07b_fkph_t_ae_refl {P : ℂ → Prop} (h : ∀ᵐ z, P z) : ∀ᵐ z, P (conj z)⁻¹ := by
  have h1 : ∀ᵐ z, P (conj z) := gzE_conj_measurePreserving.quasiMeasurePreserving.ae h
  exact (nx_ae_inv h1).mono fun z hz => by rwa [map_inv₀] at hz

/-- The normalized solution of an `ι`-symmetric Beltrami coefficient is `ι`-symmetric; hence it
preserves `𝔻`, `𝕋` and `𝔻*`. -/
theorem s07b_fkph_t_symm_sol {μ : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k) (hk : k < 1)
    (hμ : IsBeltramiCoeff μ univ k)
    (hsym : ∀ z : ℂ, z ≠ 0 → μ z = conj (μ (conj z)⁻¹) * (z ^ 2 / conj z ^ 2)) :
    ∃ (F : ℂ → ℂ) (K : ℝ), IsKQC F univ K ∧ F '' univ = univ ∧ F 0 = 0 ∧
      (∀ᵐ z, LiZhongQC.complexDilatation F z = μ z) ∧
      (∀ z : ℂ, F (conj z)⁻¹ = (conj (F z))⁻¹) ∧
      ∀ z : ℂ, (‖F z‖ < 1 ↔ ‖z‖ < 1) ∧ (‖F z‖ = 1 ↔ ‖z‖ = 1) := by
  obtain ⟨F, ⟨-, hFs, hF0, hF1, hFd⟩, hFK, -⟩ := thm13_7_normalized_existence hk0 hk hμ
  set K := (1 + k) / (1 - k) with hKdef
  obtain ⟨e, he⟩ := t1_homeomorph hFK hFs
  have hFinj : Function.Injective F := he ▸ e.injective
  have hFc : Continuous F := he ▸ e.continuous
  have hFne : ∀ z : ℂ, z ≠ 0 → F z ≠ 0 := fun z hz h => hz (hFinj (h.trans hF0.symm))
  set G : ℂ → ℂ := fun z => (conj (F (conj z)⁻¹))⁻¹ with hG
  -- `G` is a homeomorphism of the plane
  have he0 : e 0 = 0 := by rw [he]; exact hF0
  obtain ⟨E, hE⟩ := nxI1_exists_homeo e he0
  set E' : ℂ ≃ₜ ℂ := (Complex.conjLIE.toHomeomorph.trans E).trans Complex.conjLIE.toHomeomorph
  have hGE : ⇑E' = G := by
    funext z
    show conj (E (conj z)) = (conj (F (conj z)⁻¹))⁻¹
    rw [hE]
    show conj (e (conj z)⁻¹)⁻¹ = (conj (F (conj z)⁻¹))⁻¹
    rw [he, map_inv₀]
  have hGh : IsHomeomorphOnto G univ univ := hGE ▸ nxI1_isHomeomorphOnto_of_homeomorph E'
  have hGs : G '' univ = univ := hGh.2.2.1
  -- `G` is `K`-qc off `0`
  have hinv0 : IsKQC (fun w : ℂ => w⁻¹) {0}ᶜ 1 :=
    isKQC_one_of_conformal isOpen_compl_singleton nx_inv_isConformalOnto
  have h1 := thm7_1_comp hinv0 hFK (subset_univ _)
  have hsub : (F ∘ fun w : ℂ => w⁻¹) '' {0}ᶜ ⊆ {0}ᶜ := by
    rintro _ ⟨z, hz, rfl⟩
    exact hFne _ (inv_ne_zero hz)
  have h2 := thm7_1_comp h1 hinv0 hsub
  rw [one_mul, mul_one] at h2
  have h3 := abR_x_isKQC_conj h2
  have hpre : conj ⁻¹' ({0}ᶜ : Set ℂ) = {0}ᶜ := by
    ext z
    simp
  rw [hpre] at h3
  have hG0 : IsKQC G {0}ᶜ K := by
    convert h3 using 1
    funext z
    show (conj (F (conj z)⁻¹))⁻¹ = conj ((F (conj z)⁻¹)⁻¹)
    rw [map_inv₀]
  -- removability of `0`
  have hcnt : ∀ x : ℝ, {y : ℝ | (x : ℂ) + (y : ℂ) * I ∈ ({0} : Set ℂ)}.Countable := by
    intro x
    refine (Set.countable_singleton (0 : ℝ)).mono fun y hy => ?_
    have h := congrArg Complex.im (mem_singleton_iff.mp hy)
    simpa using h
  have hcnt' : ∀ y : ℝ, {x : ℝ | (x : ℂ) + (y : ℂ) * I ∈ ({0} : Set ℂ)}.Countable := by
    intro y
    refine (Set.countable_singleton (0 : ℝ)).mono fun x hx => ?_
    have h := congrArg Complex.re (mem_singleton_iff.mp hx)
    simpa using h
  have hK1 : (1 : ℝ) ≤ K := hFK.2.1
  have hGK : IsKQC G univ K := by
    refine s13x_removable isOpen_univ hK1 (by rw [hGs]; exact hGh) (measure_singleton 0)
      (Filter.Eventually.of_forall hcnt) (Filter.Eventually.of_forall hcnt') fun z hz => ?_
    exact ⟨{0}ᶜ, isOpen_compl_singleton, hz.2, subset_univ _, hG0⟩
  -- the dilatation of `G`
  have hne : ∀ᵐ z : ℂ, z ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton 0)
  have hdiff : ∀ᵐ z : ℂ, DifferentiableAt ℝ F z := by
    have := thm9_3_differentiable_ae hFK
    rwa [Measure.restrict_univ] at this
  have hGd : ∀ᵐ z, LiZhongQC.complexDilatation G z = μ z := by
    filter_upwards [hne, s07b_fkph_t_ae_refl hdiff, s07b_fkph_t_ae_refl hFd] with z hz hd hμz
    rw [s07b_fkph_t_refl_dil hz hd (hFne _ (inv_ne_zero ((map_ne_zero _).2 hz))), hμz, ← hsym z hz]
  have hGF : G = F := thm13_5_uniqueness_plane ⟨K, hGK⟩ ⟨K, hFK⟩ hGs hFs
    (hGd.mp (hFd.mono fun z h1 h2 => h2.trans h1.symm))
    (by simp [hG, hF0]) (by simp [hG, hF1]) hF0 hF1
  have hι : ∀ z : ℂ, F (conj z)⁻¹ = (conj (F z))⁻¹ := by
    intro z
    have h := congrFun hGF z
    rw [← h]
    exact (abR_t_conj_inv_inv _).symm
  -- consequences for the norm
  have hone : ∀ z : ℂ, ‖F z‖ = 1 ↔ ‖z‖ = 1 := by
    intro z
    constructor
    · intro h
      have hz : z ≠ 0 := fun h0 => by rw [h0, hF0, norm_zero] at h; exact zero_ne_one h
      have hw : (conj (F z))⁻¹ = F z := abR_t_inv_conj_of_norm_one h
      have hzz : (conj z)⁻¹ = z := hFinj ((hι z).trans hw)
      have hn := congrArg norm hzz
      rw [abR_t_norm_inv_conj] at hn
      have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
      have : ‖z‖ * ‖z‖ = 1 := by
        nth_rewrite 1 [← hn]
        exact inv_mul_cancel₀ hpos.ne'
      nlinarith [this]
    · intro h
      have hz : z ≠ 0 := fun h0 => by rw [h0, norm_zero] at h; exact zero_ne_one h
      have hw := hι z
      rw [abR_t_inv_conj_of_norm_one h] at hw
      have hn := congrArg norm hw
      rw [abR_t_norm_inv_conj] at hn
      have hpos : 0 < ‖F z‖ := norm_pos_iff.2 (hFne z hz)
      have : ‖F z‖ * ‖F z‖ = 1 := by
        nth_rewrite 1 [hn]
        exact inv_mul_cancel₀ hpos.ne'
      nlinarith [this]
  have hin : ∀ z : ℂ, ‖z‖ < 1 → ‖F z‖ < 1 := by
    intro z hz
    by_contra hge'
    have hge := not_lt.mp hge'
    have hivt := isPreconnected_ball.intermediate_value (mem_ball_self one_pos)
      (show z ∈ ball (0 : ℂ) 1 by rwa [mem_ball, dist_zero_right])
      (hFc.norm.continuousOn (s := ball (0 : ℂ) 1))
    rw [hF0, norm_zero] at hivt
    obtain ⟨w, hw, hw1⟩ := hivt ⟨zero_le_one, hge⟩
    rw [mem_ball, dist_zero_right] at hw
    exact (ne_of_lt hw) ((hone w).1 hw1)
  refine ⟨F, K, hFK, hFs, hF0, hFd, hι, fun z => ⟨⟨fun h => ?_, hin z⟩, hone z⟩⟩
  by_contra hge'
  have hge := not_lt.mp hge'
  rcases hge.eq_or_lt with h1 | h1
  · exact (ne_of_lt h) ((hone z).2 h1.symm)
  · have hz : z ≠ 0 := fun h0 => by rw [h0, norm_zero] at h1; linarith
    have hc : ‖(conj z)⁻¹‖ < 1 := by
      rw [abR_t_norm_inv_conj]
      exact inv_lt_one_of_one_lt₀ h1
    have h2 := hin _ hc
    rw [hι, abR_t_norm_inv_conj] at h2
    have hpos : 0 < ‖F z‖ := norm_pos_iff.2 (hFne z hz)
    have := (inv_lt_one₀ hpos).1 h2
    linarith

/-- The symmetric extension `Φ̃ = Φ ∪ ι ∘ Φ ∘ ι` of a collar map is `K'`-qc on the annulus
`{t < |z| < 1/t}` (the circle is removable). -/
theorem s07b_fkph_t_ext {r t K' : ℝ} {Φ : ℂ → ℂ} (hrt : r ≤ t) (ht0 : 0 < t) (ht1 : t < 1)
    (hqc : IsKQC Φ {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} K')
    (hcont : ContinuousOn Φ {z : ℂ | r < ‖z‖ ∧ ‖z‖ ≤ 1})
    (hinj : InjOn Φ {z : ℂ | r < ‖z‖ ∧ ‖z‖ ≤ 1})
    (hmaps : MapsTo Φ {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} unitDisc)
    (hT : MapsTo Φ (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1))
    (h0 : ∀ z : ℂ, t < ‖z‖ → ‖z‖ < 1 → Φ z ≠ 0) :
    IsKQC (fun z => if ‖z‖ ≤ 1 then Φ z else (conj (Φ (conj z)⁻¹))⁻¹)
      {z : ℂ | t < ‖z‖ ∧ ‖z‖ < t⁻¹} K' := by
  set Φt : ℂ → ℂ := fun z => if ‖z‖ ≤ 1 then Φ z else (conj (Φ (conj z)⁻¹))⁻¹ with hΦt
  set R : ℂ → ℂ := fun z => (conj (Φ (conj z)⁻¹))⁻¹ with hR
  set W : Set ℂ := {z : ℂ | t < ‖z‖ ∧ ‖z‖ < t⁻¹} with hW
  have hrt' : r < 1 := hrt.trans_lt ht1
  have ht1' : 1 < t⁻¹ := one_lt_inv₀ ht0 |>.2 ht1
  have hWo : IsOpen W :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hK1 : (1 : ℝ) ≤ K' := hqc.2.1
  -- the reflection `ι w = (w̄)⁻¹`
  have hιn : ∀ w : ℂ, ‖(conj w)⁻¹‖ = ‖w‖⁻¹ := abR_t_norm_inv_conj
  have hιT : ∀ w : ℂ, ‖w‖ = 1 → (conj w)⁻¹ = w := fun w hw => abR_t_inv_conj_of_norm_one hw
  have hΦT : ∀ w : ℂ, ‖w‖ = 1 → ‖Φ w‖ = 1 := fun w hw => by
    have := hT (show w ∈ sphere (0 : ℂ) 1 by rwa [mem_sphere, dist_zero_right])
    rwa [mem_sphere, dist_zero_right] at this
  have hΦD : ∀ w : ℂ, r < ‖w‖ → ‖w‖ < 1 → ‖Φ w‖ < 1 := fun w h1 h2 => by
    have := hmaps (show w ∈ {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} from ⟨h1, h2⟩)
    simpa [unitDisc] using this
  -- outside `𝕋` the reflected point lies in the collar
  have hιW : ∀ w : ℂ, 1 ≤ ‖w‖ → ‖w‖ < t⁻¹ → t < ‖(conj w)⁻¹‖ ∧ ‖(conj w)⁻¹‖ ≤ 1 := by
    intro w h1 h2
    have hw0 : 0 < ‖w‖ := lt_of_lt_of_le one_pos h1
    rw [hιn]
    exact ⟨(lt_inv_comm₀ hw0 ht0).1 h2, inv_le_one_of_one_le₀ h1⟩
  have hΦne : ∀ w : ℂ, t < ‖w‖ → ‖w‖ ≤ 1 → Φ w ≠ 0 := by
    intro w h1 h2
    rcases h2.lt_or_eq with h2 | h2
    · exact h0 w h1 h2
    · intro h
      have := hΦT w h2
      rw [h, norm_zero] at this
      exact zero_ne_one this
  have hRT : ∀ w : ℂ, ‖w‖ = 1 → R w = Φ w := by
    intro w hw
    show (conj (Φ (conj w)⁻¹))⁻¹ = Φ w
    rw [hιT w hw, hιT _ (hΦT w hw)]
  -- continuity
  have hc1 : ContinuousOn Φt (W ∩ {z : ℂ | ‖z‖ ≤ 1}) := by
    have hm : ContinuousOn Φ (W ∩ {z : ℂ | ‖z‖ ≤ 1}) :=
      hcont.mono fun z hz => ⟨hrt.trans_lt hz.1.1, hz.2⟩
    refine hm.congr fun z hz => ?_
    show (if ‖z‖ ≤ 1 then Φ z else R z) = Φ z
    rw [if_pos (show ‖z‖ ≤ 1 from hz.2)]
  have hRc : ContinuousOn R (W ∩ {z : ℂ | 1 ≤ ‖z‖}) := by
    have hι : ContinuousOn (fun w : ℂ => (conj w)⁻¹) (W ∩ {z : ℂ | 1 ≤ ‖z‖}) :=
      fun w hw => (Complex.continuous_conj.continuousAt.inv₀ ((map_ne_zero _).2
        (norm_pos_iff.1 (lt_of_lt_of_le one_pos hw.2)))).continuousWithinAt
    have hmap : MapsTo (fun w : ℂ => (conj w)⁻¹) (W ∩ {z : ℂ | 1 ≤ ‖z‖})
        {z : ℂ | r < ‖z‖ ∧ ‖z‖ ≤ 1} := fun w hw =>
      ⟨hrt.trans_lt (hιW w hw.2 hw.1.2).1, (hιW w hw.2 hw.1.2).2⟩
    have h2 := hcont.comp hι hmap
    refine fun w hw => ((Complex.continuous_conj.continuousAt.comp_continuousWithinAt
      (h2 w hw)).inv₀ ?_)
    exact (map_ne_zero _).2 (hΦne _ (hιW w hw.2 hw.1.2).1 (hιW w hw.2 hw.1.2).2)
  have hc2 : ContinuousOn Φt (W ∩ {z : ℂ | 1 ≤ ‖z‖}) := by
    refine hRc.congr fun z hz => ?_
    show (if ‖z‖ ≤ 1 then Φ z else R z) = R z
    by_cases h : ‖z‖ ≤ 1
    · rw [if_pos h, hRT z (le_antisymm h hz.2)]
    · rw [if_neg h]
  have hcl1 : IsClosed {z : ℂ | ‖z‖ ≤ 1} := isClosed_le continuous_norm continuous_const
  have hcl2 : IsClosed {z : ℂ | 1 ≤ ‖z‖} := isClosed_le continuous_const continuous_norm
  have hcW : ContinuousOn Φt W := by
    intro z hz
    have hu : W = (W ∩ {z : ℂ | ‖z‖ ≤ 1}) ∪ (W ∩ {z : ℂ | 1 ≤ ‖z‖}) := by
      ext w
      constructor
      · intro hw
        rcases le_total ‖w‖ 1 with h | h
        · exact Or.inl ⟨hw, h⟩
        · exact Or.inr ⟨hw, h⟩
      · rintro (hw | hw)
        · exact hw.1
        · exact hw.1
    rw [hu]
    refine ContinuousWithinAt.union ?_ ?_
    · by_cases h : ‖z‖ ≤ 1
      · exact hc1 z ⟨hz, h⟩
      · refine continuousWithinAt_of_notMem_closure fun hc => h ?_
        exact (closure_mono inter_subset_right).trans hcl1.closure_subset hc
    · by_cases h : 1 ≤ ‖z‖
      · exact hc2 z ⟨hz, h⟩
      · refine continuousWithinAt_of_notMem_closure fun hc => h ?_
        exact (closure_mono inter_subset_right).trans hcl2.closure_subset hc
  -- the three regions are preserved
  have hreg : ∀ z ∈ W, (‖z‖ < 1 → ‖Φt z‖ < 1) ∧ (‖z‖ = 1 → ‖Φt z‖ = 1) ∧
      (1 < ‖z‖ → 1 < ‖Φt z‖) := by
    intro z hz
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · show ‖if ‖z‖ ≤ 1 then Φ z else R z‖ < 1
      rw [if_pos h.le]
      exact hΦD z (hrt.trans_lt hz.1) h
    · show ‖if ‖z‖ ≤ 1 then Φ z else R z‖ = 1
      rw [if_pos h.le]
      exact hΦT z h
    · show 1 < ‖if ‖z‖ ≤ 1 then Φ z else R z‖
      rw [if_neg (not_le.2 h)]
      show 1 < ‖(conj (Φ (conj z)⁻¹))⁻¹‖
      have hι := hιW z h.le hz.2
      have hlt : ‖(conj z)⁻¹‖ < 1 := by
        rw [hιn]
        exact inv_lt_one_of_one_lt₀ h
      have h1 := hΦD _ (hrt.trans_lt hι.1) hlt
      have hpos : 0 < ‖Φ (conj z)⁻¹‖ := norm_pos_iff.2 (h0 _ hι.1 hlt)
      rw [hιn]
      exact (one_lt_inv₀ hpos).2 h1
  -- injectivity
  have hinjW : InjOn Φt W := by
    intro z hz w hw hzw
    have hz' := hreg z hz
    have hw' := hreg w hw
    rcases lt_trichotomy ‖z‖ 1 with h1 | h1 | h1 <;> rcases lt_trichotomy ‖w‖ 1 with h2 | h2 | h2
    · have e1 : Φt z = Φ z := if_pos h1.le
      have e2 : Φt w = Φ w := if_pos h2.le
      exact hinj ⟨hrt.trans_lt hz.1, h1.le⟩ ⟨hrt.trans_lt hw.1, h2.le⟩ (e1 ▸ e2 ▸ hzw)
    · have := hz'.1 h1; rw [hzw, hw'.2.1 h2] at this; exact absurd this (lt_irrefl 1)
    · have := hz'.1 h1; rw [hzw] at this; exact absurd (hw'.2.2 h2) (not_lt.2 this.le)
    · have := hw'.1 h2; rw [← hzw, hz'.2.1 h1] at this; exact absurd this (lt_irrefl 1)
    · have e1 : Φt z = Φ z := if_pos h1.le
      have e2 : Φt w = Φ w := if_pos h2.le
      exact hinj ⟨hrt.trans_lt hz.1, h1.le⟩ ⟨hrt.trans_lt hw.1, h2.le⟩ (e1 ▸ e2 ▸ hzw)
    · have := hz'.2.1 h1; rw [hzw] at this; exact absurd (hw'.2.2 h2) (by rw [this]; exact lt_irrefl 1)
    · have := hw'.1 h2; rw [← hzw] at this; exact absurd (hz'.2.2 h1) (not_lt.2 this.le)
    · have := hw'.2.1 h2; rw [← hzw] at this; exact absurd (hz'.2.2 h1) (by rw [this]; exact lt_irrefl 1)
    · have e1 : Φt z = R z := if_neg (not_le.2 h1)
      have e2 : Φt w = R w := if_neg (not_le.2 h2)
      have h := e1 ▸ e2 ▸ hzw
      have hR' : Φ (conj z)⁻¹ = Φ (conj w)⁻¹ := by
        have := congrArg (fun x : ℂ => (conj x)⁻¹) h
        simpa only [hR, abR_t_conj_inv_inv] using this
      have hzι := hιW z h1.le hz.2
      have hwι := hιW w h2.le hw.2
      have := hinj ⟨hrt.trans_lt hzι.1, hzι.2⟩ ⟨hrt.trans_lt hwι.1, hwι.2⟩ hR'
      have := congrArg (fun x : ℂ => (conj x)⁻¹) this
      simpa only [abR_t_conj_inv_inv] using this
  have hhom : IsHomeomorphOnto Φt W (Φt '' W) := qcl_f_isHomeomorphOnto_of_injOn hWo hcW hinjW
  -- local quasiconformality off `𝕋`
  set V : Set ℂ := {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < t⁻¹} with hV
  have hVo : IsOpen V :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hV0 : V ⊆ {0}ᶜ := fun z hz h0z => by
    rw [mem_singleton_iff] at h0z
    have := hz.1
    rw [h0z, norm_zero] at this
    linarith
  set V' : Set ℂ := {z : ℂ | t < ‖z‖ ∧ ‖z‖ < 1} with hV'
  have hV'o : IsOpen V' :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hinvV : IsKQC (fun w : ℂ => w⁻¹) V 1 :=
    isKQC_one_of_conformal hVo (D' := (fun w : ℂ => w⁻¹) '' V)
      ⟨nx_inv_isConformalOnto.1.mono hV0, nx_inv_isConformalOnto.2.1.mono hV0, rfl⟩
  have hinv0 : IsKQC (fun w : ℂ => w⁻¹) {0}ᶜ 1 :=
    isKQC_one_of_conformal isOpen_compl_singleton nx_inv_isConformalOnto
  have hΦV' : IsKQC Φ V' K' := nx_isKQC_restrict hqc hV'o fun z hz => ⟨hrt.trans_lt hz.1, hz.2⟩
  have hs1 : (fun w : ℂ => w⁻¹) '' V ⊆ V' := by
    rintro _ ⟨z, hz, rfl⟩
    have hz0 : 0 < ‖z‖ := lt_trans one_pos hz.1
    refine ⟨?_, ?_⟩
    · show t < ‖z⁻¹‖
      rw [norm_inv]
      exact (lt_inv_comm₀ hz0 ht0).1 hz.2
    · show ‖z⁻¹‖ < 1
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ hz.1
  have c1 := thm7_1_comp hinvV hΦV' hs1
  have hs2 : (Φ ∘ fun w : ℂ => w⁻¹) '' V ⊆ {0}ᶜ := by
    rintro _ ⟨z, hz, rfl⟩
    have h := hs1 ⟨z, hz, rfl⟩
    exact h0 _ h.1 h.2
  have c2 := thm7_1_comp c1 hinv0 hs2
  rw [one_mul, mul_one] at c2
  have c3 := abR_x_isKQC_conj c2
  have hpre : conj ⁻¹' V = V := by
    ext z
    simp [hV, Complex.norm_conj]
  rw [hpre] at c3
  have hout : IsKQC Φt V K' := by
    refine ad_isKQC_congr c3 fun z hz => ?_
    show (if ‖z‖ ≤ 1 then Φ z else R z) = conj ((Φ (conj z)⁻¹)⁻¹)
    rw [if_neg (not_le.2 hz.1), map_inv₀]
  have hin : IsKQC Φt V' K' := by
    refine ad_isKQC_congr hΦV' fun z hz => ?_
    show (if ‖z‖ ≤ 1 then Φ z else R z) = Φ z
    rw [if_pos hz.2.le]
  -- removability of `𝕋`
  have hLv : ∀ x : ℝ, {y : ℝ | (x : ℂ) + (y : ℂ) * I ∈ sphere (0 : ℂ) 1}.Countable := by
    intro x
    refine (abR_c_countable_circle x).mono fun y hy => ?_
    have h := abR_c_norm_eq_one (show ‖(x : ℂ) + (y : ℂ) * I‖ = 1 by
      simpa [mem_sphere, dist_zero_right] using hy)
    show y ^ 2 + x ^ 2 = 1
    linarith
  have hLh : ∀ y : ℝ, {x : ℝ | (x : ℂ) + (y : ℂ) * I ∈ sphere (0 : ℂ) 1}.Countable := by
    intro y
    refine (abR_c_countable_circle y).mono fun x hx => ?_
    exact abR_c_norm_eq_one (show ‖(x : ℂ) + (y : ℂ) * I‖ = 1 by
      simpa [mem_sphere, dist_zero_right] using hx)
  refine s13x_removable hWo hK1 hhom (Measure.addHaar_sphere volume 0 1)
    (Filter.Eventually.of_forall hLv) (Filter.Eventually.of_forall hLh) fun z hz => ?_
  have hz1 : ‖z‖ ≠ 1 := fun h => hz.2 (by rw [mem_sphere, dist_zero_right]; exact h)
  rcases lt_or_gt_of_ne hz1 with h | h
  · exact ⟨V', hV'o, ⟨hz.1.1, h⟩, fun w hw => ⟨hw.1, hw.2.trans ht1'⟩, hin⟩
  · exact ⟨V, hVo, ⟨h, hz.1.2⟩, fun w hw => ⟨ht1.trans hw.1, hw.2⟩, hout⟩

/-- **M1a** (symmetric factorization). For a collar map `Φ` and `r ≤ s < 1` there are a qc self-map
`F` of `ℂ` with `F(𝔻) = 𝔻` and `μ_F = μ_Φ · 1_{A_s}` a.e. on `𝔻`, an open `U ⊇ 𝕋` and an injective
holomorphic `Ψ` on `U`, mapping `𝕋` to `𝕋` and `U ∩ 𝔻` into `𝔻`, with `Φ = Ψ ∘ F` on `𝕋`.
(`F` = normalized solution of the `ι`-symmetric extension of `μ_Φ · 1_{A_s}`, `ι z = (conj z)⁻¹`;
`Ψ = Φ̃ ∘ F⁻¹` with `Φ̃ = Φ ∪ ι ∘ Φ ∘ ι`, conformal across `𝕋` by removability.) -/
theorem s07b_fkph_t_factor {r s K' : ℝ} {Φ : ℂ → ℂ} (hr0 : 0 < r) (hrs : r ≤ s) (hs1 : s < 1)
    (hqc : IsKQC Φ {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} K')
    (hcont : ContinuousOn Φ {z : ℂ | r < ‖z‖ ∧ ‖z‖ ≤ 1})
    (hinj : InjOn Φ {z : ℂ | r < ‖z‖ ∧ ‖z‖ ≤ 1})
    (hmaps : MapsTo Φ {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} unitDisc)
    (hT : MapsTo Φ (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1)) :
    ∃ (F Ψ : ℂ → ℂ) (K : ℝ) (U : Set ℂ), IsKQC F univ K ∧ F '' univ = univ ∧
      F '' unitDisc = unitDisc ∧ F 0 = 0 ∧
      (∀ᵐ z, z ∈ unitDisc → LiZhongQC.complexDilatation F z =
        {z : ℂ | s < ‖z‖ ∧ ‖z‖ < 1}.indicator (LiZhongQC.complexDilatation Φ) z) ∧
      IsOpen U ∧ sphere (0 : ℂ) 1 ⊆ U ∧ DifferentiableOn ℂ Ψ U ∧ InjOn Ψ U ∧
      MapsTo Ψ (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1) ∧ (∀ w ∈ U, ‖w‖ < 1 → ‖Ψ w‖ < 1) ∧
      ∀ ζ ∈ sphere (0 : ℂ) 1, Φ ζ = Ψ (F ζ) := by
  set A : Set ℂ := {z : ℂ | s < ‖z‖ ∧ ‖z‖ < 1} with hA
  set Ar : Set ℂ := {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} with hAr
  have hAo : IsOpen A :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hAro : IsOpen Ar :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hK1 : (1 : ℝ) ≤ K' := hqc.2.1
  set k : ℝ := (K' - 1) / (K' + 1) with hk
  have hk0 : 0 ≤ k := div_nonneg (by linarith) (by linarith)
  have hk1 : k < 1 := (div_lt_one (by linarith)).2 (by linarith)
  -- a.e. facts on the collar, and their reflections
  have hbd : ∀ᵐ z, z ∈ Ar → ‖LiZhongQC.complexDilatation Φ z‖ ≤ k :=
    (ae_restrict_iff' hAro.measurableSet).1 (isKQC_maxDilatation_le hqc).2
  have hdf : ∀ᵐ z, z ∈ Ar → DifferentiableAt ℝ Φ z :=
    (ae_restrict_iff' hAro.measurableSet).1 (thm9_3_differentiable_ae hqc)
  have hbdι := s07b_fkph_t_ae_refl hbd
  have hdfι := s07b_fkph_t_ae_refl hdf
  -- the clipped truncated dilatation `ν` and its symmetric extension `μ̂`
  set c : ℂ → ℂ := fun z => if ‖LiZhongQC.complexDilatation Φ z‖ ≤ k then
    LiZhongQC.complexDilatation Φ z else 0 with hc
  set ν : ℂ → ℂ := A.indicator c with hν
  set μh : ℂ → ℂ := fun z => if ‖z‖ < 1 then ν z else if 1 < ‖z‖ then
    conj (ν (conj z)⁻¹) * (z ^ 2 / conj z ^ 2) else 0 with hμh
  have hμΦm : Measurable (LiZhongQC.complexDilatation Φ) :=
    show Measurable fun z => dzbar Φ z / dz Φ z from (measurable_dzbar Φ).div (measurable_dz Φ)
  have hcm : Measurable c :=
    Measurable.ite (measurableSet_le hμΦm.norm measurable_const) hμΦm measurable_const
  have hνm : Measurable ν := hcm.indicator hAo.measurableSet
  have hιm : Measurable fun z : ℂ => (conj z)⁻¹ := Complex.continuous_conj.measurable.inv
  have hμhm : Measurable μh := by
    refine Measurable.ite (measurableSet_lt measurable_norm measurable_const) hνm
      (Measurable.ite (measurableSet_lt measurable_const measurable_norm) ?_ measurable_const)
    exact (Complex.continuous_conj.measurable.comp (hνm.comp hιm)).mul
      ((measurable_id.pow_const 2).div (Complex.continuous_conj.measurable.pow_const 2))
  have hcb : ∀ z, ‖c z‖ ≤ k := by
    intro z
    show ‖if ‖LiZhongQC.complexDilatation Φ z‖ ≤ k then LiZhongQC.complexDilatation Φ z else 0‖ ≤ k
    split_ifs with h
    · exact h
    · rw [norm_zero]; exact hk0
  have hνb : ∀ z, ‖ν z‖ ≤ k := by
    intro z
    by_cases h : z ∈ A
    · rw [hν, indicator_of_mem h]; exact hcb z
    · rw [hν, indicator_of_notMem h, norm_zero]; exact hk0
  have hrot : ∀ z : ℂ, z ≠ 0 → ‖z ^ 2 / conj z ^ 2‖ = 1 := by
    intro z hz
    rw [norm_div, norm_pow, norm_pow, Complex.norm_conj]
    exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.2 hz))
  have hμhb : ∀ z, ‖μh z‖ ≤ k := by
    intro z
    show ‖if ‖z‖ < 1 then ν z else if 1 < ‖z‖ then
      conj (ν (conj z)⁻¹) * (z ^ 2 / conj z ^ 2) else 0‖ ≤ k
    split_ifs with h1 h2
    · exact hνb z
    · have hz : z ≠ 0 := fun h0 => by rw [h0, norm_zero] at h2; linarith
      rw [norm_mul, Complex.norm_conj, hrot z hz, mul_one]
      exact hνb _
    · rw [norm_zero]; exact hk0
  have hBel : IsBeltramiCoeff μh univ k :=
    ⟨hμhm.aestronglyMeasurable, Filter.Eventually.of_forall hμhb⟩
  -- `μ̂` is `ι`-symmetric
  have hsym : ∀ z : ℂ, z ≠ 0 → μh z = conj (μh (conj z)⁻¹) * (z ^ 2 / conj z ^ 2) := by
    intro z hz
    have hcz : conj z ≠ 0 := (map_ne_zero _).2 hz
    have hn := abR_t_norm_inv_conj z
    have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
    rcases lt_trichotomy ‖z‖ 1 with h | h | h
    · have h' : 1 < ‖(conj z)⁻¹‖ := by rw [hn]; exact (one_lt_inv₀ hpos).2 h
      have e1 : μh z = ν z := if_pos h
      have e2 : μh (conj z)⁻¹ = conj (ν (conj (conj z)⁻¹)⁻¹) *
          ((conj z)⁻¹ ^ 2 / conj (conj z)⁻¹ ^ 2) :=
        (if_neg (not_lt.2 h'.le)).trans (if_pos h')
      rw [e1, e2, abR_t_conj_inv_inv, map_mul, Complex.conj_conj, map_div₀, map_pow, map_pow,
        map_inv₀, Complex.conj_conj, map_inv₀]
      field_simp
    · have hι : (conj z)⁻¹ = z := abR_t_inv_conj_of_norm_one h
      have e1 : μh z = 0 := (if_neg (not_lt.2 h.ge)).trans (if_neg (not_lt.2 h.le))
      rw [hι, e1, map_zero, zero_mul]
    · have h' : ‖(conj z)⁻¹‖ < 1 := by rw [hn]; exact inv_lt_one_of_one_lt₀ h
      have e1 : μh z = conj (ν (conj z)⁻¹) * (z ^ 2 / conj z ^ 2) :=
        (if_neg (not_lt.2 h.le)).trans (if_pos h)
      have e2 : μh (conj z)⁻¹ = ν (conj z)⁻¹ := if_pos h'
      rw [e1, e2]
  obtain ⟨F, K, hFK, hFs, hF0, hFd, hFι, hFn⟩ := s07b_fkph_t_symm_sol hk0 hk1 hBel hsym
  obtain ⟨e, he⟩ := t1_homeomorph hFK hFs
  have hFinj : Function.Injective F := he ▸ e.injective
  -- a radius `t ≥ s` beyond which `Φ` has no zero
  obtain ⟨t, hst, ht1, h0⟩ : ∃ t : ℝ, s ≤ t ∧ t < 1 ∧
      ∀ z : ℂ, t < ‖z‖ → ‖z‖ < 1 → Φ z ≠ 0 := by
    by_cases hex : ∃ z₀ : ℂ, r < ‖z₀‖ ∧ ‖z₀‖ < 1 ∧ Φ z₀ = 0
    · obtain ⟨z₀, hz₀r, hz₀1, hz₀⟩ := hex
      refine ⟨max s ‖z₀‖, le_max_left _ _, max_lt hs1 hz₀1, fun z h1 h2 hz => ?_⟩
      have := hinj ⟨hrs.trans_lt ((le_max_left _ _).trans_lt h1), h2.le⟩ ⟨hz₀r, hz₀1.le⟩
        (hz.trans hz₀.symm)
      rw [this] at h1
      exact absurd ((le_max_right _ _).trans_lt h1) (lt_irrefl _)
    · exact ⟨s, le_rfl, hs1, fun z h1 h2 hz => hex ⟨z, hrs.trans_lt h1, h2, hz⟩⟩
  have hrt : r ≤ t := hrs.trans hst
  have ht0 : 0 < t := hr0.trans_le hrt
  have hΦt := s07b_fkph_t_ext hrt ht0 ht1 hqc hcont hinj hmaps hT h0
  set Φt : ℂ → ℂ := fun z => if ‖z‖ ≤ 1 then Φ z else (conj (Φ (conj z)⁻¹))⁻¹ with hΦtdef
  set W : Set ℂ := {z : ℂ | t < ‖z‖ ∧ ‖z‖ < t⁻¹} with hW
  have hWo : IsOpen W :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have ht1' : 1 < t⁻¹ := (one_lt_inv₀ ht0).2 ht1
  have hFW : IsKQC F W K := nx_isKQC_restrict hFK hWo (subset_univ _)
  -- the dilatations of `Φ̃` and `F` agree a.e. on `W`
  have hTnull : ∀ᵐ z : ℂ, ‖z‖ ≠ 1 := by
    have h := compl_mem_ae_iff.mpr (Measure.addHaar_sphere volume (0 : ℂ) 1)
    filter_upwards [h] with z hz hz1
    exact hz (by rw [mem_sphere, dist_zero_right]; exact hz1)
  have hne : ∀ᵐ z : ℂ, z ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton 0)
  have hV'o : IsOpen {z : ℂ | t < ‖z‖ ∧ ‖z‖ < 1} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hVo : IsOpen {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < t⁻¹} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hdil : ∀ᵐ z ∂(volume.restrict W),
      LiZhongQC.complexDilatation Φt z = LiZhongQC.complexDilatation F z := by
    refine (ae_restrict_iff' hWo.measurableSet).2 ?_
    filter_upwards [hTnull, hne, hFd, hbd, hbdι, hdfι] with z hz1 hz0 hFz hb hbι hdι hzW
    rw [hFz]
    rcases lt_or_gt_of_ne hz1 with h | h
    · -- inside: `Φ̃ = Φ` near `z`
      have hzV : z ∈ {z : ℂ | t < ‖z‖ ∧ ‖z‖ < 1} := ⟨hzW.1, h⟩
      rw [abR_t_complexDilatation_congr hV'o (g := Φ) (fun w hw => by
        show (if ‖w‖ ≤ 1 then Φ w else (conj (Φ (conj w)⁻¹))⁻¹) = Φ w
        rw [if_pos hw.2.le]) hzV]
      have hzA : z ∈ A := ⟨hst.trans_lt hzW.1, h⟩
      have e1 : μh z = ν z := if_pos h
      rw [e1, hν, indicator_of_mem hzA]
      show LiZhongQC.complexDilatation Φ z = if ‖LiZhongQC.complexDilatation Φ z‖ ≤ k then
        LiZhongQC.complexDilatation Φ z else 0
      rw [if_pos (hb ⟨hrs.trans_lt hzA.1, h⟩)]
    · -- outside: `Φ̃ = ι ∘ Φ ∘ ι` near `z`
      have hzV : z ∈ {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < t⁻¹} := ⟨h, hzW.2⟩
      rw [abR_t_complexDilatation_congr hVo (g := fun w => (conj (Φ (conj w)⁻¹))⁻¹)
        (fun w hw => by
          show (if ‖w‖ ≤ 1 then Φ w else (conj (Φ (conj w)⁻¹))⁻¹) = (conj (Φ (conj w)⁻¹))⁻¹
          rw [if_neg (not_le.2 hw.1)]) hzV]
      have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
      have hιn : ‖(conj z)⁻¹‖ = ‖z‖⁻¹ := abR_t_norm_inv_conj z
      have hι1 : ‖(conj z)⁻¹‖ < 1 := by rw [hιn]; exact inv_lt_one_of_one_lt₀ h
      have hιt : t < ‖(conj z)⁻¹‖ := by rw [hιn]; exact (lt_inv_comm₀ hpos ht0).1 hzW.2
      have hιAr : (conj z)⁻¹ ∈ Ar := ⟨hrt.trans_lt hιt, hι1⟩
      have hιA : (conj z)⁻¹ ∈ A := ⟨hst.trans_lt hιt, hι1⟩
      rw [s07b_fkph_t_refl_dil hz0 (hdι hιAr) (h0 _ hιt hι1)]
      have e1 : μh z = conj (ν (conj z)⁻¹) * (z ^ 2 / conj z ^ 2) :=
        (if_neg (not_lt.2 h.le)).trans (if_pos h)
      rw [e1, hν, indicator_of_mem hιA]
      show conj (LiZhongQC.complexDilatation Φ (conj z)⁻¹) * (z ^ 2 / conj z ^ 2) =
        conj (if ‖LiZhongQC.complexDilatation Φ (conj z)⁻¹‖ ≤ k then
          LiZhongQC.complexDilatation Φ (conj z)⁻¹ else 0) * (z ^ 2 / conj z ^ 2)
      rw [if_pos (hbι hιAr)]
  have hconf := s27u_b_conformal_of_dilatation_eq hFW hΦt hdil
  -- `F` preserves `𝕋`
  have hFT : ∀ w ∈ sphere (0 : ℂ) 1, ∃ z, ‖z‖ = 1 ∧ F z = w := by
    intro w hw
    have hw1 : ‖w‖ = 1 := by rwa [mem_sphere, dist_zero_right] at hw
    obtain ⟨z, -, rfl⟩ : w ∈ F '' univ := by rw [hFs]; exact mem_univ w
    exact ⟨z, (hFn z).2.1 hw1, rfl⟩
  have hTW : ∀ z : ℂ, ‖z‖ = 1 → z ∈ W := fun z hz => ⟨by rw [hz]; exact ht1, by rw [hz]; exact ht1'⟩
  have hleft : ∀ z ∈ W, Function.invFunOn F W (F z) = z := fun z hz =>
    hFinj.injOn.leftInvOn_invFunOn hz
  refine ⟨F, Φt ∘ Function.invFunOn F W, K, F '' W, hFK, hFs, ?_, hF0, ?_, ?_, ?_, hconf.1,
    hconf.2.1, ?_, ?_, ?_⟩
  · -- `F(𝔻) = 𝔻`
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz1 : ‖z‖ < 1 := by simpa [unitDisc] using hz
      show F z ∈ ball (0 : ℂ) 1
      rw [mem_ball, dist_zero_right]
      exact (hFn z).1.2 hz1
    · intro hw
      obtain ⟨z, -, rfl⟩ : w ∈ F '' univ := by rw [hFs]; exact mem_univ w
      have hw1 : ‖F z‖ < 1 := by simpa [unitDisc] using hw
      refine ⟨z, ?_, rfl⟩
      show z ∈ ball (0 : ℂ) 1
      rw [mem_ball, dist_zero_right]
      exact (hFn z).1.1 hw1
  · -- `μ_F = μ_Φ · 1_{A_s}` a.e. on `𝔻`
    filter_upwards [hFd, hbd] with z hFz hb hzD
    have hz1 : ‖z‖ < 1 := by simpa [unitDisc] using hzD
    have e1 : μh z = ν z := if_pos hz1
    rw [hFz, e1, hν]
    by_cases hzA : z ∈ A
    · rw [indicator_of_mem hzA, indicator_of_mem hzA]
      show (if ‖LiZhongQC.complexDilatation Φ z‖ ≤ k then LiZhongQC.complexDilatation Φ z else 0) =
        LiZhongQC.complexDilatation Φ z
      rw [if_pos (hb ⟨hrs.trans_lt hzA.1, hz1⟩)]
    · rw [indicator_of_notMem hzA, indicator_of_notMem hzA]
  · -- `F(W)` is open
    rw [← he]
    exact e.isOpenMap W hWo
  · -- `𝕋 ⊆ F(W)`
    intro w hw
    obtain ⟨z, hz1, rfl⟩ := hFT w hw
    exact ⟨z, hTW z hz1, rfl⟩
  · -- `Ψ(𝕋) ⊆ 𝕋`
    intro w hw
    obtain ⟨z, hz1, rfl⟩ := hFT w hw
    show Φt (Function.invFunOn F W (F z)) ∈ sphere (0 : ℂ) 1
    rw [hleft z (hTW z hz1)]
    show (if ‖z‖ ≤ 1 then Φ z else (conj (Φ (conj z)⁻¹))⁻¹) ∈ sphere (0 : ℂ) 1
    rw [if_pos hz1.le]
    exact hT (by rw [mem_sphere, dist_zero_right]; exact hz1)
  · -- `Ψ` maps the inside to the inside
    rintro _ ⟨z, hzW, rfl⟩ hw
    have hz1 : ‖z‖ < 1 := (hFn z).1.1 hw
    show ‖Φt (Function.invFunOn F W (F z))‖ < 1
    rw [hleft z hzW]
    show ‖if ‖z‖ ≤ 1 then Φ z else (conj (Φ (conj z)⁻¹))⁻¹‖ < 1
    rw [if_pos hz1.le]
    have := hmaps (show z ∈ Ar from ⟨hrt.trans_lt hzW.1, hz1⟩)
    simpa [unitDisc] using this
  · -- `Φ = Ψ ∘ F` on `𝕋`
    intro ζ hζ
    have hζ1 : ‖ζ‖ = 1 := by rwa [mem_sphere, dist_zero_right] at hζ
    show Φ ζ = Φt (Function.invFunOn F W (F ζ))
    rw [hleft ζ (hTW ζ hζ1)]
    show Φ ζ = if ‖ζ‖ ≤ 1 then Φ ζ else (conj (Φ (conj ζ)⁻¹))⁻¹
    rw [if_pos hζ1.le]

/-- A function with a one-sided local maximum from the left has nonnegative derivative there. -/
theorem s07b_fkph_t_deriv_nonneg_left {f : ℝ → ℝ} {f' x₀ : ℝ} (hf : HasDerivAt f f' x₀)
    (h : ∀ᶠ y in 𝓝[<] x₀, f y ≤ f x₀) : 0 ≤ f' := by
  have ht := (hasDerivAt_iff_tendsto_slope.1 hf).mono_left (nhdsLT_le_nhdsNE x₀)
  refine ge_of_tendsto ht ?_
  filter_upwards [h, self_mem_nhdsWithin] with y hy hy'
  rw [slope_def_field]
  have hy'' : y < x₀ := hy'
  exact div_nonneg_iff.2 (Or.inr ⟨sub_nonpos.2 hy, (sub_neg.2 hy'').le⟩)

/-- A function with a one-sided local maximum from the right has nonpositive derivative there. -/
theorem s07b_fkph_t_deriv_nonpos_right {f : ℝ → ℝ} {f' x₀ : ℝ} (hf : HasDerivAt f f' x₀)
    (h : ∀ᶠ y in 𝓝[>] x₀, f y ≤ f x₀) : f' ≤ 0 := by
  have ht := (hasDerivAt_iff_tendsto_slope.1 hf).mono_left (nhdsGT_le_nhdsNE x₀)
  refine le_of_tendsto ht ?_
  filter_upwards [h, self_mem_nhdsWithin] with y hy hy'
  rw [slope_def_field]
  have hy'' : x₀ < y := hy'
  exact div_nonpos_iff.2 (Or.inr ⟨sub_nonpos.2 hy, (sub_pos.2 hy'').le⟩)

/-- A continuous `2π`-periodic function is uniformly continuous, in the form used for the
oscillation estimate. -/
theorem s07b_fkph_t_periodic_uc {g : ℝ → ℝ} (hg : Continuous g) (hp : ∀ t, g (t + 2 * π) = g t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 2 * π ∧ ∀ t s : ℝ, |t - s| ≤ δ → |g t - g s| ≤ ε := by
  have hpi : 0 < 2 * π := Real.two_pi_pos
  have huc := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := -(2 * π)) (b := 4 * π)).uniformContinuousOn_of_continuous hg.continuousOn)
  obtain ⟨δ₁, hδ₁, hδ⟩ := huc ε hε
  refine ⟨min (δ₁ / 2) (2 * π), lt_min (half_pos hδ₁) hpi, min_le_right _ _, fun t s hts => ?_⟩
  have hper : Function.Periodic g (2 * π) := hp
  have hk1 : ((⌊t / (2 * π)⌋ : ℤ) : ℝ) ≤ t / (2 * π) := Int.floor_le _
  have hk2 : t / (2 * π) < ((⌊t / (2 * π)⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  set k : ℤ := ⌊t / (2 * π)⌋
  have h1 : (k : ℝ) * (2 * π) ≤ t := by rwa [le_div_iff₀ hpi] at hk1
  have h2 : t < ((k : ℝ) + 1) * (2 * π) := by rwa [div_lt_iff₀ hpi] at hk2
  have hts1 := abs_le.1 hts
  have hmin : min (δ₁ / 2) (2 * π) ≤ δ₁ / 2 := min_le_left _ _
  have hmin2 : min (δ₁ / 2) (2 * π) ≤ 2 * π := min_le_right _ _
  have ht' : t - k * (2 * π) ∈ Icc (-(2 * π)) (4 * π) := ⟨by linarith, by linarith⟩
  have hs' : s - k * (2 * π) ∈ Icc (-(2 * π)) (4 * π) := ⟨by linarith, by linarith⟩
  have hd : dist (t - k * (2 * π)) (s - k * (2 * π)) < δ₁ := by
    rw [Real.dist_eq, show t - k * (2 * π) - (s - k * (2 * π)) = t - s by ring]
    linarith [half_lt_self hδ₁]
  have := hδ _ ht' _ hs' hd
  rw [Real.dist_eq, hper.sub_int_mul_eq, hper.sub_int_mul_eq] at this
  exact this.le

/-- `exp (x i) = 1` for real `x` forces `x ∈ 2πℤ`. -/
theorem s07b_fkph_t_exp_eq_one {x : ℝ} (h : Complex.exp (x * Complex.I) = 1) :
    ∃ n : ℤ, x = n * (2 * π) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp at this
  linarith

/-- The real part of a complex-valued derivative. -/
theorem s07b_fkph_t_re_deriv {k : ℝ → ℂ} {d c : ℂ} {x₀ : ℝ} (hk : HasDerivAt k d x₀) :
    HasDerivAt (fun t => (k t / c).re) (d / c).re x₀ := by
  have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x₀ (hk.div_const c)
  simpa only [Function.comp_def, Complex.reCLM_apply] using this

/-- **Boundary lift of a holomorphic circle map.** An injective holomorphic `Ψ` near `𝕋`, mapping
`𝕋` to `𝕋` and the inside to the inside, has a `C¹` lift `P` with `P' = p > 0` periodic and
`P (φ + 2π) = P φ + 2π`. -/
theorem s07b_fkph_t_circle_lift {Ψ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hTU : sphere (0 : ℂ) 1 ⊆ U) (hΨd : DifferentiableOn ℂ Ψ U) (hΨi : InjOn Ψ U)
    (hΨT : MapsTo Ψ (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1))
    (hΨin : ∀ w ∈ U, ‖w‖ < 1 → ‖Ψ w‖ < 1) :
    ∃ P p : ℝ → ℝ, Continuous p ∧ (∀ φ, 0 < p φ) ∧ (∀ φ, p (φ + 2 * π) = p φ) ∧
      (∀ φ, HasDerivAt P (p φ) φ) ∧ (∀ φ, P (φ + 2 * π) = P φ + 2 * π) ∧
      ∀ φ : ℝ, Ψ (Complex.exp (φ * Complex.I)) = Complex.exp (P φ * Complex.I) := by
  have hΨ1 : ∀ ζ ∈ sphere (0 : ℂ) 1, ‖Ψ ζ‖ = 1 := fun ζ hζ => mem_sphere_zero_iff_norm.1 (hΨT hζ)
  have hΨ0 : ∀ ζ ∈ sphere (0 : ℂ) 1, Ψ ζ ≠ 0 := fun ζ hζ h => by
    have := hΨ1 ζ hζ
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hdΨ : ∀ ζ ∈ U, HasDerivAt Ψ (deriv Ψ ζ) ζ := fun ζ hζ =>
    ((hΨd ζ hζ).differentiableAt (hU.mem_nhds hζ)).hasDerivAt
  -- tangential direction: `ζ Ψ'(ζ) / Ψ(ζ)` is real
  have hQim : ∀ ζ ∈ sphere (0 : ℂ) 1, (ζ * deriv Ψ ζ / Ψ ζ).im = 0 := by
    intro ζ hζ
    have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.1 hζ
    have he : ∀ s : ℝ, HasDerivAt (fun t : ℝ => ζ * Complex.exp (t * I))
        (ζ * (Complex.exp (s * I) * I)) s := by
      intro s
      have := (((hasDerivAt_id (s : ℂ)).mul_const I).cexp.const_mul ζ).comp_ofReal
      simpa using this
    have hS : ∀ t : ℝ, ζ * Complex.exp (t * I) ∈ sphere (0 : ℂ) 1 := fun t => by
      rw [mem_sphere_zero_iff_norm, norm_mul, hζ1, Complex.norm_exp_ofReal_mul_I, one_mul]
    have hk : HasDerivAt (fun t : ℝ => Ψ (ζ * Complex.exp (t * I)))
        (deriv Ψ ζ * (ζ * I)) 0 := by
      have h0 := (hdΨ _ (hTU (hS 0))).comp (0 : ℝ) (he 0)
      simpa [Function.comp_def] using h0
    have hf := s07b_fkph_t_re_deriv (c := Ψ ζ) hk
    have hle : ∀ t : ℝ, (Ψ (ζ * Complex.exp (t * I)) / Ψ ζ).re ≤
        (Ψ (ζ * Complex.exp ((0 : ℝ) * I)) / Ψ ζ).re := by
      intro t
      have h0 : (Ψ (ζ * Complex.exp (((0 : ℝ) : ℂ) * I)) / Ψ ζ) = 1 := by
        simp [div_self (hΨ0 ζ hζ)]
      rw [h0, Complex.one_re]
      refine (Complex.re_le_norm _).trans ?_
      rw [norm_div, hΨ1 _ (hS t), hΨ1 ζ hζ, div_one]
    have h1 := s07b_fkph_t_deriv_nonneg_left hf (Filter.Eventually.of_forall hle)
    have h2 := s07b_fkph_t_deriv_nonpos_right hf (Filter.Eventually.of_forall hle)
    have h3 : (deriv Ψ ζ * (ζ * I) / Ψ ζ).re = -(ζ * deriv Ψ ζ / Ψ ζ).im := by
      rw [show deriv Ψ ζ * (ζ * I) / Ψ ζ = I * (ζ * deriv Ψ ζ / Ψ ζ) by ring]
      simp
    linarith
  -- radial direction: its real part is nonnegative
  have hQre : ∀ ζ ∈ sphere (0 : ℂ) 1, 0 ≤ (ζ * deriv Ψ ζ / Ψ ζ).re := by
    intro ζ hζ
    have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.1 hζ
    have hk : HasDerivAt (fun r : ℝ => Ψ (r * ζ)) (deriv Ψ ζ * ζ) 1 := by
      have hr : HasDerivAt (fun r : ℝ => (r : ℂ) * ζ) ζ 1 := by
        have := ((hasDerivAt_id ((1 : ℝ) : ℂ)).mul_const ζ).comp_ofReal
        simpa using this
      have hd1 : HasDerivAt Ψ (deriv Ψ ζ) (((1 : ℝ) : ℂ) * ζ) := by
        simpa using hdΨ ζ (hTU hζ)
      have h0 := hd1.comp (1 : ℝ) hr
      simpa [Function.comp_def] using h0
    have hf := s07b_fkph_t_re_deriv (c := Ψ ζ) hk
    have hc : Continuous fun r : ℝ => (r : ℂ) * ζ := by fun_prop
    have hev : ∀ᶠ r : ℝ in 𝓝 (1 : ℝ), (r : ℂ) * ζ ∈ U :=
      hc.continuousAt.eventually_mem (by simpa using hU.mem_nhds (hTU hζ))
    have hev2 : ∀ᶠ r : ℝ in 𝓝 (1 : ℝ), 0 < r := lt_mem_nhds one_pos
    have hle : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), (Ψ (r * ζ) / Ψ ζ).re ≤ (Ψ (((1 : ℝ) : ℂ) * ζ) / Ψ ζ).re := by
      filter_upwards [nhdsWithin_le_nhds hev, nhdsWithin_le_nhds hev2, self_mem_nhdsWithin]
        with r hrU hr0 hr1
      have hr1' : r < 1 := hr1
      have h0 : Ψ (((1 : ℝ) : ℂ) * ζ) / Ψ ζ = 1 := by simp [div_self (hΨ0 ζ hζ)]
      rw [h0, Complex.one_re]
      refine (Complex.re_le_norm _).trans ?_
      rw [norm_div, hΨ1 ζ hζ, div_one]
      refine (hΨin _ hrU ?_).le
      rw [norm_mul, hζ1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      exact hr1'
    have h1 := s07b_fkph_t_deriv_nonneg_left hf hle
    rwa [show deriv Ψ ζ * ζ / Ψ ζ = ζ * deriv Ψ ζ / Ψ ζ by ring] at h1
  have hQne : ∀ ζ ∈ sphere (0 : ℂ) 1, ζ * deriv Ψ ζ / Ψ ζ ≠ 0 := by
    intro ζ hζ
    have hζ0 : ζ ≠ 0 := by
      intro h
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hζ
      exact zero_ne_one hζ
    exact div_ne_zero (mul_ne_zero hζ0 (LiZhongQC.deriv_ne_zero_of_injOn hU hΨd hΨi (hTU hζ)))
      (hΨ0 ζ hζ)
  -- the density `p`
  set w : ℝ → ℂ := fun φ => Complex.exp (φ * I) with hw
  have hwS : ∀ φ, w φ ∈ sphere (0 : ℂ) 1 := fun φ => by
    rw [mem_sphere_zero_iff_norm]
    exact Complex.norm_exp_ofReal_mul_I φ
  have hwU : ∀ φ, w φ ∈ U := fun φ => hTU (hwS φ)
  have hwc : Continuous w := by fun_prop
  have hwper : ∀ φ, w (φ + 2 * π) = w φ := by
    intro φ
    show Complex.exp (((φ + 2 * π : ℝ) : ℂ) * I) = Complex.exp (φ * I)
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hw' : ∀ φ : ℝ, HasDerivAt w (w φ * I) φ := by
    intro φ
    have := ((hasDerivAt_id (φ : ℂ)).mul_const I).cexp.comp_ofReal
    simpa [hw] using this
  set p : ℝ → ℝ := fun φ => (w φ * deriv Ψ (w φ) / Ψ (w φ)).re with hp
  have hpc : Continuous p := by
    refine continuous_iff_continuousAt.2 fun φ => ?_
    have hd1 : ContinuousAt (deriv Ψ) (w φ) :=
      ((hΨd.deriv hU) (w φ) (hwU φ)).differentiableAt (hU.mem_nhds (hwU φ)) |>.continuousAt
    have hd2 : ContinuousAt Ψ (w φ) := (hdΨ _ (hwU φ)).continuousAt
    have hQ : ContinuousAt (fun z => z * deriv Ψ z / Ψ z) (w φ) :=
      (continuousAt_id.mul hd1).div hd2 (hΨ0 _ (hwS φ))
    exact Complex.continuous_re.continuousAt.comp (hQ.comp hwc.continuousAt)
  have hppos : ∀ φ, 0 < p φ := by
    intro φ
    refine lt_of_le_of_ne (hQre _ (hwS φ)) fun h => hQne _ (hwS φ) ?_
    exact Complex.ext (by simpa using h.symm) (by simpa using hQim _ (hwS φ))
  have hpper : ∀ φ, p (φ + 2 * π) = p φ := by
    intro φ
    show (w (φ + 2 * π) * deriv Ψ (w (φ + 2 * π)) / Ψ (w (φ + 2 * π))).re = p φ
    rw [hwper]
  have hQp : ∀ φ, w φ * deriv Ψ (w φ) = (p φ : ℂ) * Ψ (w φ) := by
    intro φ
    have h : w φ * deriv Ψ (w φ) / Ψ (w φ) = (p φ : ℂ) :=
      Complex.ext (by simp [hp]) (by simpa using hQim _ (hwS φ))
    exact (div_eq_iff (hΨ0 _ (hwS φ))).1 h
  -- the lift
  set P₀ : ℝ := Complex.arg (Ψ 1)
  set P : ℝ → ℝ := fun φ => P₀ + ∫ t in (0 : ℝ)..φ, p t with hP
  have hPd : ∀ φ, HasDerivAt P (p φ) φ := fun φ =>
    ((hpc.integral_hasStrictDerivAt 0 φ).hasDerivAt).const_add P₀
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun φ => (hPd φ).continuousAt
  set E : ℝ → ℂ := fun φ => Ψ (w φ) * Complex.exp (-((P φ : ℂ) * I)) with hE
  have hEd : ∀ φ, HasDerivAt E 0 φ := by
    intro φ
    have h1 := (hdΨ _ (hwU φ)).comp φ (hw' φ)
    have h2 := (((hPd φ).ofReal_comp.mul_const I).neg).cexp
    have h3 := h1.mul h2
    refine h3.congr_deriv ?_
    try simp only [Function.comp_apply]
    linear_combination (Complex.exp (-((P φ : ℂ) * I)) * I) * (hQp φ)
  have hEc : ∀ φ, E φ = E 0 := fun φ =>
    is_const_of_deriv_eq_zero (fun x => (hEd x).differentiableAt) (fun x => (hEd x).deriv) φ 0
  have hE0 : E 0 = 1 := by
    have h1 : Ψ 1 = Complex.exp (P₀ * I) := by
      have := Complex.norm_mul_exp_arg_mul_I (Ψ 1)
      rw [hΨ1 1 (by simp)] at this
      simpa using this.symm
    show Ψ (Complex.exp (((0 : ℝ) : ℂ) * I)) * Complex.exp (-((P 0 : ℂ) * I)) = 1
    have hP0 : P 0 = P₀ := by simp [hP]
    rw [hP0, Complex.ofReal_zero, zero_mul, Complex.exp_zero, h1, ← Complex.exp_add, add_neg_cancel,
      Complex.exp_zero]
  have hlift : ∀ φ : ℝ, Ψ (w φ) = Complex.exp (P φ * I) := by
    intro φ
    have h := (hEc φ).trans hE0
    rw [hE] at h
    simp only at h
    rw [Complex.exp_neg] at h
    exact (mul_inv_eq_one₀ (Complex.exp_ne_zero _)).1 h
  -- the period of `P`
  have hpI : ∀ a b : ℝ, IntervalIntegrable p volume a b := fun a b => hpc.intervalIntegrable a b
  set c : ℝ := ∫ t in (0 : ℝ)..0 + 2 * π, p t with hc
  have hPadd : ∀ φ, P (φ + 2 * π) = P φ + c := by
    intro φ
    have h1 := intervalIntegral.integral_add_adjacent_intervals (hpI 0 φ) (hpI φ (φ + 2 * π))
    have h2 := (show Function.Periodic p (2 * π) from hpper).intervalIntegral_add_eq φ 0
    show P₀ + ∫ t in (0 : ℝ)..φ + 2 * π, p t = (P₀ + ∫ t in (0 : ℝ)..φ, p t) + c
    rw [← h1, h2]
    ring
  have hcpos : 0 < c := by
    have hpi : (0 : ℝ) < 0 + 2 * π := by linarith [Real.two_pi_pos]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on (hpI _ _) (fun x _ => hppos x) hpi
  have hcexp : Complex.exp (c * I) = 1 := by
    have h1 := hlift (0 + 2 * π)
    rw [show (0 : ℝ) + 2 * π = 0 + 2 * π from rfl, hwper, hlift 0, hPadd 0] at h1
    have h2 : Complex.exp ((P 0 : ℂ) * I) * Complex.exp (c * I) =
        Complex.exp ((P 0 : ℂ) * I) * 1 := by
      rw [mul_one, ← Complex.exp_add, h1]
      push_cast
      ring_nf
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) h2
  obtain ⟨n, hn⟩ := s07b_fkph_t_exp_eq_one hcexp
  have hpi : 0 < 2 * π := Real.two_pi_pos
  have hn1 : 1 ≤ n := by
    by_contra h
    have h' : n ≤ 0 := by omega
    have : (n : ℝ) ≤ 0 := by exact_mod_cast h'
    nlinarith
  have hn2 : n ≤ 1 := by
    by_contra h
    have h' : 2 ≤ n := by omega
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h'
    have hc4 : 2 * (2 * π) ≤ c := by rw [hn]; nlinarith
    have hP2 : P (0 + 2 * π) = P 0 + c := hPadd 0
    have hmem : P 0 + 2 * π ∈ Icc (P 0) (P (0 + 2 * π)) := ⟨by linarith, by linarith⟩
    obtain ⟨φ₁, hφ₁, hPφ₁⟩ := intermediate_value_Icc (by linarith) hPc.continuousOn hmem
    have hφ0 : φ₁ ≠ 0 := by
      intro h0
      rw [h0] at hPφ₁
      linarith
    have hφ2 : φ₁ ≠ 0 + 2 * π := by
      intro h0
      rw [h0] at hPφ₁
      linarith
    have heq : Ψ (w φ₁) = Ψ (w 0) := by
      rw [hlift, hlift, hPφ₁]
      push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    have hw1 := hΨi (hwU φ₁) (hwU 0) heq
    have hexp : Complex.exp (φ₁ * I) = 1 := by
      have : w 0 = 1 := by simp [hw]
      rw [← this]
      exact hw1
    obtain ⟨m, hm⟩ := s07b_fkph_t_exp_eq_one hexp
    have hlo : 0 < φ₁ := lt_of_le_of_ne hφ₁.1 (Ne.symm hφ0)
    have hhi : φ₁ < 2 * π := by
      have := lt_of_le_of_ne hφ₁.2 hφ2
      linarith
    have hm1 : (0 : ℝ) < m := by
      by_contra hh
      have : (m : ℝ) ≤ 0 := not_lt.mp hh
      nlinarith
    have hm2 : (m : ℝ) < 1 := by
      by_contra hh
      have : (1 : ℝ) ≤ m := not_lt.mp hh
      nlinarith
    have hm1' : 0 < m := by exact_mod_cast hm1
    have hm2' : m < 1 := by exact_mod_cast hm2
    omega
  have hn' : n = 1 := le_antisymm hn2 hn1
  have hc2 : c = 2 * π := by rw [hn, hn']; push_cast; ring
  refine ⟨P, p, hpc, hppos, hpper, hPd, fun φ => by rw [hPadd, hc2], fun φ => hlift φ⟩

/-- **M1b** (boundary calculus). If `F|_𝕋` has an absolutely continuous lift `H₁ = H₁(0) + ∫ u₁`
whose `log u₁` has mean oscillation `≤ η` on every arc, and `Φ = Ψ ∘ F` on `𝕋` with `Ψ` injective
holomorphic near `𝕋`, mapping `𝕋` to `𝕋` and the inside to the inside, then `Φ|_𝕋` has an
absolutely continuous increasing lift `H = P ∘ H₁ + c`, `u = (P' ∘ H₁) u₁`, whose `log u` has mean
oscillation `≤ η + ε` on all short arcs. -/
theorem s07b_fkph_t_compose {Φ F Ψ : ℂ → ℂ} {U : Set ℂ} {H₁ u₁ : ℝ → ℝ} {η : ℝ}
    (hU : IsOpen U) (hTU : sphere (0 : ℂ) 1 ⊆ U) (hΨd : DifferentiableOn ℂ Ψ U) (hΨi : InjOn Ψ U)
    (hΨT : MapsTo Ψ (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1))
    (hΨin : ∀ w ∈ U, ‖w‖ < 1 → ‖Ψ w‖ < 1)
    (hΦ : ∀ ζ ∈ sphere (0 : ℂ) 1, Φ ζ = Ψ (F ζ))
    (hH : StrictMono H₁) (hHc : Continuous H₁) (hper : ∀ θ : ℝ, H₁ (θ + 2 * π) = H₁ θ + 2 * π)
    (hl : ∀ θ : ℝ, F (Complex.exp (θ * Complex.I)) = Complex.exp (H₁ θ * Complex.I))
    (hui : ∀ a b : ℝ, IntegrableOn u₁ (Icc a b))
    (hrep : ∀ θ : ℝ, H₁ θ = H₁ 0 + ∫ t in (0 : ℝ)..θ, u₁ t) (hpos : ∀ᵐ t, 0 < u₁ t)
    (hli : ∀ a b : ℝ, IntegrableOn (fun t => Real.log (u₁ t)) (Icc a b))
    (hosc : ∀ a b : ℝ, a < b → b - a ≤ 2 * π →
      (∫ t in a..b, |Real.log (u₁ t) - (∫ s in a..b, Real.log (u₁ s)) / (b - a)|) / (b - a) ≤ η) :
    ∃ H u : ℝ → ℝ, StrictMono H ∧ Continuous H ∧ (∀ θ : ℝ, H (θ + 2 * π) = H θ + 2 * π) ∧
      (∀ θ : ℝ, Φ (Complex.exp (θ * Complex.I)) = Complex.exp (H θ * Complex.I)) ∧
      (∀ a b : ℝ, IntegrableOn u (Icc a b)) ∧
      (∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t) ∧ (∀ᵐ t, 0 < u t) ∧
      (∀ a b : ℝ, IntegrableOn (fun t => Real.log (u t)) (Icc a b)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a < b → b - a ≤ δ →
        (∫ t in a..b, |Real.log (u t) - (∫ s in a..b, Real.log (u s)) / (b - a)|) / (b - a)
          ≤ η + ε := by
  obtain ⟨P, p, hpc, hpp, hpper, hP, hPper, hPl⟩ :=
    s07b_fkph_t_circle_lift hU hTU hΨd hΨi hΨT hΨin
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun φ => (hP φ).continuousAt
  have hPmono : StrictMono P := strictMono_of_hasDerivAt_pos hP hpp
  set u : ℝ → ℝ := fun t => u₁ t * p (H₁ t) with hu
  have hpHc : Continuous fun t => p (H₁ t) := hpc.comp hHc
  -- `H₁` has derivative `u₁` almost everywhere
  have hloc : LocallyIntegrable u₁ volume := by
    rw [locallyIntegrable_iff]
    intro k hk
    obtain ⟨a, ha⟩ := hk.bddBelow
    obtain ⟨b, hb⟩ := hk.bddAbove
    exact (hui a b).mono_set fun x hx => ⟨ha hx, hb hx⟩
  have hH₁d : ∀ᵐ t, HasDerivAt H₁ (u₁ t) t := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hloc] with t ht
    have h := (ht 0).const_add (H₁ 0)
    have he : (fun x => H₁ 0 + ∫ s in (0 : ℝ)..x, u₁ s) = H₁ := funext fun x => (hrep x).symm
    rwa [he] at h
  -- `P` is Lipschitz
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
    ((show Function.Periodic p (2 * π) from hpper).isBounded_of_continuous
      Real.two_pi_pos.ne' hpc)
  have hPL : LipschitzWith ⟨max C 0, le_max_right _ _⟩ P := by
    refine lipschitzWith_of_nnnorm_deriv_le (fun x => (hP x).differentiableAt) fun x => ?_
    change ((‖deriv P x‖₊ : ℝ≥0) : ℝ) ≤ max C 0
    rw [coe_nnnorm, (hP x).deriv]
    exact (hC _ ⟨x, rfl⟩).trans (le_max_left _ _)
  -- integrability of `log u`
  have hlog : ∀ᵐ t, Real.log (u t) = Real.log (u₁ t) + Real.log (p (H₁ t)) := by
    filter_upwards [hpos] with t ht
    exact Real.log_mul ht.ne' (hpp _).ne'
  have hgc : Continuous fun t => Real.log (p (H₁ t)) := hpHc.log fun t => (hpp _).ne'
  have hlogu : ∀ a b : ℝ, IntegrableOn (fun t => Real.log (u t)) (Icc a b) := by
    intro a b
    refine ((hli a b).add (hgc.continuousOn.integrableOn_Icc)).congr ?_
    filter_upwards [ae_restrict_of_ae hlog] with t ht
    exact ht.symm
  refine ⟨P ∘ H₁, u, hPmono.comp hH, hPc.comp hHc, fun θ => ?_, fun θ => ?_,
    fun a b => (hui a b).mul_continuousOn hpHc.continuousOn isCompact_Icc, fun θ => ?_, ?_, hlogu, ?_⟩
  · show P (H₁ (θ + 2 * π)) = P (H₁ θ) + 2 * π
    rw [hper, hPper]
  · show Φ (Complex.exp (θ * Complex.I)) = Complex.exp ((P (H₁ θ) : ℂ) * Complex.I)
    have hS : Complex.exp (θ * Complex.I) ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm]
      exact Complex.norm_exp_ofReal_mul_I θ
    rw [hΦ _ hS, hl θ, hPl]
  · -- change of variables through absolute continuity
    have hII : IntervalIntegrable u₁ volume 0 θ := (hui (0 ⊓ θ) (0 ⊔ θ)).intervalIntegrable
    have hAC1 : AbsolutelyContinuousOnInterval (fun x => ∫ s in (0 : ℝ)..x, u₁ s) 0 θ :=
      hII.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
    have hAC0 : AbsolutelyContinuousOnInterval (fun _ : ℝ => H₁ 0) 0 θ :=
      (LipschitzWith.const (H₁ 0)).lipschitzOnWith.absolutelyContinuousOnInterval
    have hAC2 : AbsolutelyContinuousOnInterval H₁ 0 θ :=
      (hAC0.add hAC1).congr fun x _ => (hrep x).symm
    have hAC3 : AbsolutelyContinuousOnInterval (P ∘ H₁) 0 θ :=
      hPL.comp_absolutelyContinuousOnInterval hAC2
    have hFTC := hAC3.integral_deriv_eq_sub
    have hcongr : ∫ t in (0 : ℝ)..θ, deriv (P ∘ H₁) t = ∫ t in (0 : ℝ)..θ, u t := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hH₁d] with t ht _
      rw [((hP (H₁ t)).comp t ht).deriv]
      exact mul_comm _ _
    simp only [Function.comp_apply] at hFTC hcongr ⊢
    linarith
  · filter_upwards [hpos] with t ht
    exact mul_pos ht (hpp _)
  -- the oscillation estimate
  intro ε hε
  set g : ℝ → ℝ := fun t => Real.log (p (H₁ t)) with hg
  have hgp : ∀ t, g (t + 2 * π) = g t := by
    intro t
    show Real.log (p (H₁ (t + 2 * π))) = Real.log (p (H₁ t))
    rw [hper, hpper]
  obtain ⟨δ, hδ, hδ2, hδg⟩ := s07b_fkph_t_periodic_uc hgc hgp hε
  refine ⟨δ, hδ, fun a b hab hba => ?_⟩
  have hL : 0 < b - a := sub_pos.2 hab
  have hIi : ∀ {v : ℝ → ℝ}, IntegrableOn v (Icc a b) → IntervalIntegrable v volume a b :=
    fun h => (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).2 h
  have hf₁ : IntervalIntegrable (fun t => Real.log (u₁ t)) volume a b := hIi (hli a b)
  have hgI : IntervalIntegrable g volume a b := hgc.intervalIntegrable a b
  have hint : ∫ t in a..b, Real.log (u t) =
      (∫ t in a..b, Real.log (u₁ t)) + ∫ t in a..b, g t := by
    rw [← intervalIntegral.integral_add hf₁ hgI]
    exact intervalIntegral.integral_congr_ae (hlog.mono fun t ht _ => ht)
  set A₁ : ℝ := (∫ s in a..b, Real.log (u₁ s)) / (b - a) with hA₁
  set A₂ : ℝ := (∫ s in a..b, g s) / (b - a) with hA₂
  have havg : (∫ s in a..b, Real.log (u s)) / (b - a) = A₁ + A₂ := by rw [hint, add_div]
  have hg2 : ∀ t ∈ Icc a b, |g t - A₂| ≤ ε := by
    intro t ht
    have h1 : g t - A₂ = (∫ s in a..b, (g t - g s)) / (b - a) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hgI,
        intervalIntegral.integral_const, smul_eq_mul, sub_div, mul_div_cancel_left₀ _ hL.ne']
    rw [h1, abs_div, abs_of_pos hL, div_le_iff₀ hL]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := ε)
      (f := fun s => g t - g s) (fun s hs => ?_)
    · rw [Real.norm_eq_abs, abs_of_pos hL] at hb
      linarith
    · rw [uIoc_of_le hab.le] at hs
      rw [Real.norm_eq_abs]
      refine hδg t s ?_
      refine le_trans ?_ hba
      exact abs_sub_le_iff.2 ⟨by linarith [ht.2, hs.1], by linarith [ht.1, hs.2]⟩
  have hpt : (fun t => |Real.log (u t) - (A₁ + A₂)|) ≤ᵐ[volume.restrict (Icc a b)]
      fun t => |Real.log (u₁ t) - A₁| + ε := by
    filter_upwards [ae_restrict_of_ae hlog, ae_restrict_mem measurableSet_Icc] with t ht ht'
    rw [ht]
    calc |Real.log (u₁ t) + Real.log (p (H₁ t)) - (A₁ + A₂)|
        = |(Real.log (u₁ t) - A₁) + (g t - A₂)| := by
          congr 1
          simp only [hg]
          ring
      _ ≤ |Real.log (u₁ t) - A₁| + |g t - A₂| := abs_add_le _ _
      _ ≤ |Real.log (u₁ t) - A₁| + ε := by linarith [hg2 t ht']
  have hmono := intervalIntegral.integral_mono_ae_restrict hab.le
    ((hIi (hlogu a b)).sub intervalIntegrable_const).abs
    (((hf₁.sub intervalIntegrable_const).abs).add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_add ((hf₁.sub intervalIntegrable_const).abs)
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hos := hosc a b hab (hba.trans hδ2)
  rw [← hA₁, div_le_iff₀ hL] at hos
  rw [havg, div_le_iff₀ hL]
  nlinarith

/-- **M1b** (uniqueness of the density). Two continuous lifts of the same circle map, both
absolutely continuous, have a.e. equal densities (the lifts differ by a constant in `2πℤ`). -/
theorem s07b_fkph_t_lift_ae {Φ : ℂ → ℂ} {H u H' u' : ℝ → ℝ} (hHc : Continuous H)
    (hH'c : Continuous H')
    (hl : ∀ θ : ℝ, Φ (Complex.exp (θ * Complex.I)) = Complex.exp (H θ * Complex.I))
    (hl' : ∀ θ : ℝ, Φ (Complex.exp (θ * Complex.I)) = Complex.exp (H' θ * Complex.I))
    (hui : ∀ a b : ℝ, IntegrableOn u (Icc a b)) (hui' : ∀ a b : ℝ, IntegrableOn u' (Icc a b))
    (hrep : ∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t)
    (hrep' : ∀ θ : ℝ, H' θ = H' 0 + ∫ t in (0 : ℝ)..θ, u' t) :
    u =ᵐ[volume] u' := by
  -- the lifts differ by a value in `2πℤ` at every point
  have hint : ∀ θ : ℝ, ∃ n : ℤ, H θ - H' θ = n * (2 * π) := by
    intro θ
    have h := (hl θ).symm.trans (hl' θ)
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.intCast_re, Complex.intCast_im, mul_zero, mul_one, zero_mul,
      add_zero, sub_zero, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat] at this
    linarith
  -- hence by a constant
  have hDc : Continuous fun θ => H θ - H' θ := hHc.sub hH'c
  have hloc : IsLocallyConstant fun θ => H θ - H' θ := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun θ => ?_
    filter_upwards [(hDc.continuousAt (x := θ)).eventually (Metric.ball_mem_nhds _ Real.two_pi_pos)]
      with y hy
    obtain ⟨m, hm⟩ := hint y
    obtain ⟨n, hn⟩ := hint θ
    rw [Real.dist_eq] at hy
    show H y - H' y = H θ - H' θ
    rw [hm, hn] at hy ⊢
    have hpi : 0 < 2 * π := Real.two_pi_pos
    have h1 : |((m : ℝ) - n)| < 1 := by
      have : |(m : ℝ) * (2 * π) - n * (2 * π)| = |((m : ℝ) - n)| * (2 * π) := by
        rw [← sub_mul, abs_mul, abs_of_pos hpi]
      rw [this] at hy
      exact (mul_lt_iff_lt_one_left hpi).1 hy
    have h2 : ((m - n : ℤ) : ℝ) < 1 := by push_cast; exact (abs_lt.1 h1).2
    have h3 : (-1 : ℝ) < ((m - n : ℤ) : ℝ) := by push_cast; exact (abs_lt.1 h1).1
    have h2' : m - n < 1 := by exact_mod_cast h2
    have h3' : -1 < m - n := by exact_mod_cast h3
    have : m = n := by omega
    rw [this]
  have hconst : ∀ θ : ℝ, H θ - H' θ = H 0 - H' 0 := fun θ =>
    hloc.apply_eq_of_preconnectedSpace θ 0
  -- the indefinite integrals agree
  have hI : (fun x => ∫ t in (0 : ℝ)..x, u t) = fun x => ∫ t in (0 : ℝ)..x, u' t := by
    funext x
    have h1 := hrep x
    have h2 := hrep' x
    have h3 := hconst x
    linarith
  -- Lebesgue differentiation
  have hli : ∀ {v : ℝ → ℝ}, (∀ a b : ℝ, IntegrableOn v (Icc a b)) → LocallyIntegrable v volume := by
    intro v hv
    rw [locallyIntegrable_iff]
    intro k hk
    obtain ⟨a, ha⟩ := hk.bddBelow
    obtain ⟨b, hb⟩ := hk.bddAbove
    exact (hv a b).mono_set fun x hx => ⟨ha hx, hb hx⟩
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral (hli hui),
    LocallyIntegrable.ae_hasDerivAt_integral (hli hui')]
    with x hx hx'
  have h1 := hx 0
  have h2 := hx' 0
  rw [← hI] at h2
  exact h1.unique h2

/-- **T2** (Shen, VMO paper Thm 8.2, collar form). The boundary map of a collar map as in
`s07b_fkph_collar` is strongly symmetric. Proof plan (M1): for `ε > 0` pick `s` from both smallness
clauses, truncate `μ̂ = μ_Φ · 1_{A_s}` and its reflection, solve `F̂` (normalized, `F̂(0) = 0`), `F̂(𝔻) = 𝔻`;
`Ψ = Φ̃ ∘ F̂⁻¹` is conformal near `𝕋` (`Φ̃ = Φ ∪ ι ∘ Φ ∘ ι`); `Φ|_𝕋 = Ψ|_𝕋 ∘ F̂|_𝕋`, so
`osc(log Φ') ≤ osc(log Ψ' ∘ F̂) + osc(log F̂') ≤ o(1) + C √ε` (SMALL with the majorant `min a ε₀`). -/
theorem s07b_fkph_ss_of_collar {r K' : ℝ} {Φ : ℂ → ℂ} (hr0 : 0 < r) (hr1 : r < 1)
    (hqc : IsKQC Φ {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} K')
    (hcont : ContinuousOn Φ {z : ℂ | r < ‖z‖ ∧ ‖z‖ ≤ 1})
    (hinj : InjOn Φ {z : ℂ | r < ‖z‖ ∧ ‖z‖ ≤ 1})
    (hmaps : MapsTo Φ {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} unitDisc)
    (hT : MapsTo Φ (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1))
    (hac : ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, r ≤ s ∧ s < 1 ∧
      ∀ᵐ z, s < ‖z‖ → ‖z‖ < 1 → ‖LiZhongQC.complexDilatation Φ z‖ ≤ ε)
    (hcm : ∀ ε : ℝ, 0 < ε → ∃ (s : ℝ) (a : ℂ → ℝ), r ≤ s ∧ s < 1 ∧ Measurable a ∧ (∀ z, 0 ≤ a z) ∧
      (∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) → s < ‖w‖ →
        ‖LiZhongQC.complexDilatation Φ w‖ ≤ a z) ∧
      ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ ρ : ℝ, 0 < ρ → ρ < 2 →
        ∫⁻ z in unitDisc ∩ ball ζ ρ, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
          ≤ ENNReal.ofReal (ε * ρ)) :
    IsStronglySymmetric Φ := by
  obtain ⟨ε₀, hε₀, hsm⟩ := s07c_fkps_small
  -- for every tolerance `η > 0` one decomposition with oscillation `≤ η + ε` on short arcs
  have key : ∀ η : ℝ, 0 < η → ∃ H u : ℝ → ℝ, StrictMono H ∧ Continuous H ∧
      (∀ θ : ℝ, H (θ + 2 * π) = H θ + 2 * π) ∧
      (∀ θ : ℝ, Φ (Complex.exp (θ * Complex.I)) = Complex.exp (H θ * Complex.I)) ∧
      (∀ a b : ℝ, IntegrableOn u (Icc a b)) ∧
      (∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t) ∧ (∀ᵐ t, 0 < u t) ∧
      (∀ a b : ℝ, IntegrableOn (fun t => Real.log (u t)) (Icc a b)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a < b → b - a ≤ δ →
        (∫ t in a..b, |Real.log (u t) - (∫ s in a..b, Real.log (u s)) / (b - a)|) / (b - a)
          ≤ η + ε := by
    intro η hη
    obtain ⟨ε₁, hε₁p, hsm'⟩ := hsm η hη
    have hε₁ : 0 < min ε₀ ε₁ := lt_min hε₀ hε₁p
    obtain ⟨s₁, hrs₁, hs₁, hac₁⟩ := hac ε₀ hε₀
    obtain ⟨s₂, a, hrs₂, hs₂, ham, ha0, hmaj, hcm₂⟩ := hcm _ hε₁
    obtain ⟨F, Ψ, K, U, hF, hFs, hFD, hF0, hFμ, hU, hTU, hΨd, hΨi, hΨT, hΨin, hΦ⟩ :=
      s07b_fkph_t_factor hr0 (hrs₁.trans (le_max_left s₁ s₂)) (max_lt hs₁ hs₂) hqc hcont hinj
        hmaps hT
    -- the majorant `min a ε₀` of the truncated dilatation
    have hWD : ∀ z ∈ unitDisc, ∀ w ∈ ball z ((1 - ‖z‖) / 2), w ∈ unitDisc := by
      intro z hz w hw
      have hz1 : ‖z‖ < 1 := by simpa [unitDisc] using hz
      have hwz : ‖w - z‖ < (1 - ‖z‖) / 2 := by simpa [dist_eq_norm] using hw
      show w ∈ ball (0 : ℂ) 1
      rw [mem_ball, dist_zero_right]
      calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ < 1 := by linarith
    have hmaj' : ∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) →
        ‖LiZhongQC.complexDilatation F w‖ ≤ min (a z) ε₀ := by
      intro z hz
      filter_upwards [hFμ, hac₁, hmaj z hz] with w h1 h2 h3 hw
      rw [h1 (hWD z hz w hw)]
      by_cases hA : w ∈ {z : ℂ | max s₁ s₂ < ‖z‖ ∧ ‖z‖ < 1}
      · rw [indicator_of_mem hA]
        exact le_min (h3 hw ((le_max_right s₁ s₂).trans_lt hA.1))
          (h2 ((le_max_left s₁ s₂).trans_lt hA.1) hA.2)
      · rw [indicator_of_notMem hA, norm_zero]
        exact le_min (ha0 z) hε₀.le
    have hcarl : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ ρ : ℝ, 0 < ρ → ρ < 2 →
        ∫⁻ z in unitDisc ∩ ball ζ ρ, ENNReal.ofReal (min (a z) ε₀ ^ 2 / (1 - ‖z‖ ^ 2))
          ≤ ENNReal.ofReal (min ε₀ ε₁ * ρ) := by
      intro ζ hζ ρ hρ hρ2
      refine le_trans (setLIntegral_mono' (isOpen_ball.measurableSet.inter measurableSet_ball)
        fun z hz => ?_) (hcm₂ ζ hζ ρ hρ hρ2)
      have hz1 : ‖z‖ < 1 := by simpa [unitDisc] using hz.1
      have hd : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hd)
      exact pow_le_pow_left₀ (le_min (ha0 z) hε₀.le) (min_le_left _ _) 2
    obtain ⟨H₁, u₁, hH, hHc, hper, hl, hui, hrep, hpos, hli, hosc⟩ :=
      hsm' F (fun z => min (a z) ε₀) K _ hF hFs hFD hF0 (ham.min measurable_const)
        (fun z => le_min (ha0 z) hε₀.le) (fun z _ => min_le_right _ _) hmaj' hε₁.le
        (min_le_right _ _) hcarl
    exact s07b_fkph_t_compose hU hTU hΨd hΨi hΨT hΨin hΦ hH hHc hper hl hui hrep hpos hli
      fun a b hab hb2 => hosc a b hab hb2
  -- the base decomposition; the oscillation of `log u` does not depend on the representative
  obtain ⟨H, u, hH, hHc, hper, hl, hui, hrep, hpos, hli, -⟩ := key 1 one_pos
  refine ⟨H, u, hH, hHc, hper, hl, hui, hrep, hpos, hli, fun ε hε => ?_⟩
  obtain ⟨H', u', -, hH'c, -, hl', hui', hrep', -, -, hv'⟩ := key (ε / 2) (half_pos hε)
  obtain ⟨δ, hδ, hδv⟩ := hv' (ε / 2) (half_pos hε)
  have hae : u' =ᵐ[volume] u := s07b_fkph_t_lift_ae hH'c hHc hl' hl hui' hui hrep' hrep
  refine ⟨δ, hδ, fun a b hab hba => ?_⟩
  have hlog : ∀ᵐ t, Real.log (u' t) = Real.log (u t) := hae.mono fun t ht => by rw [ht]
  have hmean : (∫ s in a..b, Real.log (u' s)) = ∫ s in a..b, Real.log (u s) :=
    intervalIntegral.integral_congr_ae (hlog.mono fun t ht _ => ht)
  have hosc' : (∫ t in a..b, |Real.log (u' t) - (∫ s in a..b, Real.log (u' s)) / (b - a)|) =
      ∫ t in a..b, |Real.log (u t) - (∫ s in a..b, Real.log (u s)) / (b - a)| := by
    rw [hmean]
    exact intervalIntegral.integral_congr_ae (hlog.mono fun t ht _ => by rw [ht])
  have h := hδv a b hab hba
  rw [hosc'] at h
  linarith

/-- The boundary map of a strongly symmetric `Φ` is onto `𝕋` (its lift is continuous and
`H (θ + 2π) = H θ + 2π`). -/
theorem s07b_fkph_t_ss_surj {Φ : ℂ → ℂ} (hΦ : IsStronglySymmetric Φ) :
    ∀ ζ ∈ sphere (0 : ℂ) 1, ∃ ξ ∈ sphere (0 : ℂ) 1, Φ ξ = ζ := by
  obtain ⟨H, u, -, hHc, hper, hl, -⟩ := hΦ
  intro ζ hζ
  have hpi : 0 < 2 * π := Real.two_pi_pos
  have hk1 : ((⌊(Complex.arg ζ - H 0) / (2 * π)⌋ : ℤ) : ℝ) ≤ (Complex.arg ζ - H 0) / (2 * π) :=
    Int.floor_le _
  have hk2 : (Complex.arg ζ - H 0) / (2 * π) < ((⌊(Complex.arg ζ - H 0) / (2 * π)⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  set k : ℤ := ⌊(Complex.arg ζ - H 0) / (2 * π)⌋
  have h1 : (k : ℝ) * (2 * π) ≤ Complex.arg ζ - H 0 := by rwa [le_div_iff₀ hpi] at hk1
  have h2 : Complex.arg ζ - H 0 < ((k : ℝ) + 1) * (2 * π) := by rwa [div_lt_iff₀ hpi] at hk2
  have hmem : Complex.arg ζ - k * (2 * π) ∈ Icc (H 0) (H (0 + 2 * π)) := by
    rw [hper]
    constructor <;> linarith
  obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc (by linarith) hHc.continuousOn hmem
  refine ⟨Complex.exp (θ * Complex.I), ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm]
    exact Complex.norm_exp_ofReal_mul_I θ
  · rw [hl, hθ]
    have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.1 hζ
    have hz := Complex.norm_mul_exp_arg_mul_I ζ
    rw [hζ1, Complex.ofReal_one, one_mul] at hz
    push_cast
    rw [sub_mul, Complex.exp_sub,
      show (k : ℂ) * (2 * π) * Complex.I = k * (2 * π * Complex.I) by ring,
      Complex.exp_int_mul_two_pi_mul_I, div_one, hz]

/-- **(V2) ⇒ (V5)**: the forward half of `thm_shen_wei_V5`. -/
theorem s07b_fkph_V5_fwd {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K)
    {f g h : ℂ → ℂ} (hw : IsDiskWelding Ω Ωs f g h) (hf : LogDerivVMOA f) :
    IsStronglySymmetric h := by
  obtain ⟨r, K', Φ, hr0, hr1, hqc, hcont, hinj, hmaps, hT, hac, hcm⟩ := s07b_fkph_collar hq hw hf
  have hΦ := s07b_fkph_ss_of_collar hr0 hr1 hqc hcont hinj hmaps (fun ζ hζ => (hT ζ hζ).1) hac hcm
  refine ss_circle_inv Φ h hΦ fun ζ hζ => ?_
  obtain ⟨ξ, hξ, hξζ⟩ := s07b_fkph_t_ss_surj hΦ ζ hζ
  rw [← hξζ, (hT ξ hξ).2]
  exact ⟨hξ, rfl⟩



/-! ## Lane C (w6, Round B): Cayley transfer C1–C6, C1v, C5v', C6v

Frozen interface `collaboration/w6_vcB/w6_C_iface.lean` (md5 910a2fa1). Prefix `s0c_`.
`s0c_v_bmo_log_A2` is a copy of VC's `ps_bmo_log_of_A2` (VanishingCarleson/ProofSteps.lean),
which is `private` upstream. -/

section W6LaneC

/-! ## C1 part 1: the closed formula `H = T ∘ K ∘ α` -/

/-- `α(T s) = s` on `(-2π, 0)`, with `α t = 2 arctan t - π`, `T s = tan((s + π)/2)`. -/
theorem s0c_c1_alpha_T {s : ℝ} (hs : s ∈ Ioo (-(2 * π)) 0) :
    2 * Real.arctan (Real.tan ((s + π) / 2)) - π = s := by
  rw [Real.arctan_tan (by linarith [hs.1]) (by linarith [hs.2])]
  ring

theorem s0c_c1_T_alpha (t : ℝ) : Real.tan ((2 * Real.arctan t - π + π) / 2) = t := by
  rw [show (2 * Real.arctan t - π + π) / 2 = Real.arctan t by ring, Real.tan_arctan]

theorem s0c_c1_alpha_mem (t : ℝ) : 2 * Real.arctan t - π ∈ Ioo (-(2 * π)) 0 := by
  constructor <;> linarith [Real.neg_pi_div_two_lt_arctan t, Real.arctan_lt_pi_div_two t]

theorem s0c_c1_alpha_strictMono : StrictMono fun t : ℝ => 2 * Real.arctan t - π :=
  fun a b hab => by linarith [Real.arctan_strictMono hab]

theorem s0c_c1_T_strictMonoOn : StrictMonoOn (fun s : ℝ => Real.tan ((s + π) / 2))
    (Ioo (-(2 * π)) 0) := fun a ha b hb hab =>
  Real.strictMonoOn_tan ⟨by linarith [ha.1], by linarith [ha.2]⟩
    ⟨by linarith [hb.1], by linarith [hb.2]⟩ (by linarith)

theorem s0c_c1_T_hasDerivAt {s : ℝ} (hs : s ∈ Ioo (-(2 * π)) 0) :
    HasDerivAt (fun s : ℝ => Real.tan ((s + π) / 2))
      (1 / Real.cos ((s + π) / 2) ^ 2 * (1 / 2)) s := by
  have hc : Real.cos ((s + π) / 2) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hs.1], by linarith [hs.2]⟩).ne'
  have h1 : HasDerivAt (fun s : ℝ => (s + π) / 2) (1 / 2) s := by
    simpa using ((hasDerivAt_id s).add_const π).div_const 2
  exact (Real.hasDerivAt_tan hc).comp s h1

theorem s0c_c1_cc (t : ℝ) :
    VanishingCarleson.cayley (t : ℂ) = exp (((2 * Real.arctan t - π : ℝ) : ℂ) * I) := by
  rw [← VanishingCarleson.cayleyCircle_coe, VanishingCarleson.cayleyCircle, Circle.coe_exp]

theorem s0c_c1_cayleyInv_exp {s : ℝ} (hs : s ∈ Ioo (-(2 * π)) 0) :
    VanishingCarleson.cayleyInv (exp ((s : ℂ) * I)) = (Real.tan ((s + π) / 2) : ℂ) := by
  have e : exp ((s : ℂ) * I) = VanishingCarleson.cayley (Real.tan ((s + π) / 2) : ℂ) := by
    rw [s0c_c1_cc, s0c_c1_alpha_T hs]
  rw [e, VanishingCarleson.cayleyInv_cayley]
  intro h
  have := congrArg Complex.im h
  rw [Complex.ofReal_im, Complex.neg_im, Complex.I_im] at this
  norm_num at this

/-- A normalized lift (`K 0 = 0`) of a circle homeomorphism fixing `1`. -/
theorem s0c_c1_lift {k : ℂ → ℂ} (hk : IsCircleHomeo k) (hk1 : k 1 = 1) :
    ∃ K : ℝ → ℝ, StrictMono K ∧ Continuous K ∧ (∀ θ, K (θ + 2 * π) = K θ + 2 * π) ∧
      (∀ θ : ℝ, k (exp (θ * I)) = exp (K θ * I)) ∧ K 0 = 0 := by
  obtain ⟨K, hm, hc, hp, he⟩ := hk
  have h0 : exp ((K 0 : ℂ) * I) = 1 := by
    rw [← he 0]
    simpa using hk1
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h0
  have hK0 : K 0 = n * (2 * π) := by
    have h1 : (K 0 : ℂ) = n * (2 * π) :=
      mul_right_cancel₀ Complex.I_ne_zero (by rw [hn]; ring)
    exact_mod_cast h1
  refine ⟨fun θ => K θ - n * (2 * π), fun a b hab => by simpa using hm hab,
    hc.sub continuous_const, fun θ => ?_, fun θ => ?_, ?_⟩
  · show K (θ + 2 * π) - _ = K θ - _ + 2 * π
    rw [hp]
    ring
  · rw [he θ]
    have e1 : exp ((n : ℂ) * (2 * π) * I) = 1 := by
      rw [Complex.exp_eq_one_iff]
      exact ⟨n, by ring⟩
    push_cast
    rw [sub_mul, Complex.exp_sub, e1, div_one]
  · show K 0 - _ = 0
    rw [hK0]
    ring

theorem s0c_c1_Kmem {K : ℝ → ℝ} (hK : StrictMono K) (hper : ∀ θ, K (θ + 2 * π) = K θ + 2 * π)
    (hK0 : K 0 = 0) {s : ℝ} (hs : s ∈ Ioo (-(2 * π)) 0) : K s ∈ Ioo (-(2 * π)) 0 := by
  have h2 : K (-(2 * π)) = -(2 * π) := by
    have := hper (-(2 * π))
    rw [show -(2 * π) + 2 * π = 0 by ring, hK0] at this
    linarith
  exact ⟨h2 ▸ hK hs.1, hK0 ▸ hK hs.2⟩

theorem s0c_c1_H {k : ℂ → ℂ} {K : ℝ → ℝ} (hK : StrictMono K)
    (hper : ∀ θ, K (θ + 2 * π) = K θ + 2 * π) (hl : ∀ θ : ℝ, k (exp (θ * I)) = exp (K θ * I))
    (hK0 : K 0 = 0) (t : ℝ) :
    VanishingCarleson.cayleyInv (k (VanishingCarleson.cayley t)) =
      (Real.tan ((K (2 * Real.arctan t - π) + π) / 2) : ℂ) := by
  rw [s0c_c1_cc, hl, s0c_c1_cayleyInv_exp (s0c_c1_Kmem hK hper hK0 (s0c_c1_alpha_mem t))]

theorem s0c_c1_Hmono {K : ℝ → ℝ} (hK : StrictMono K) (hper : ∀ θ, K (θ + 2 * π) = K θ + 2 * π)
    (hK0 : K 0 = 0) : StrictMono fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2) :=
  fun a b hab => s0c_c1_T_strictMonoOn (s0c_c1_Kmem hK hper hK0 (s0c_c1_alpha_mem a))
    (s0c_c1_Kmem hK hper hK0 (s0c_c1_alpha_mem b)) (hK (s0c_c1_alpha_strictMono hab))

theorem s0c_c1_Hcont {K : ℝ → ℝ} (hK : StrictMono K) (hKc : Continuous K)
    (hper : ∀ θ, K (θ + 2 * π) = K θ + 2 * π) (hK0 : K 0 = 0) :
    Continuous fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2) := by
  have hin : Continuous fun t => (K (2 * Real.arctan t - π) + π) / 2 := by
    have : Continuous fun t : ℝ => 2 * Real.arctan t - π := by fun_prop
    exact ((hKc.comp this).add continuous_const).div_const 2
  exact Real.continuousOn_tan_Ioo.comp_continuous hin fun t => by
    have h := s0c_c1_Kmem hK hper hK0 (s0c_c1_alpha_mem t)
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem s0c_c1_Hsurj {K : ℝ → ℝ} (hK : StrictMono K) (hKc : Continuous K)
    (hper : ∀ θ, K (θ + 2 * π) = K θ + 2 * π) (hK0 : K 0 = 0) :
    Function.Surjective fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2) := by
  intro y
  have h2 : K (-(2 * π)) = -(2 * π) := by
    have := hper (-(2 * π))
    rw [show -(2 * π) + 2 * π = 0 by ring, hK0] at this
    linarith
  have hy := s0c_c1_alpha_mem y
  have hmem : 2 * Real.arctan y - π ∈ Ioo (K (-(2 * π))) (K 0) := by rw [h2, hK0]; exact hy
  obtain ⟨θ, hθ, hKθ⟩ := intermediate_value_Ioo (by linarith [Real.pi_pos]) hKc.continuousOn hmem
  refine ⟨Real.tan ((θ + π) / 2), ?_⟩
  show Real.tan ((K (2 * Real.arctan (Real.tan ((θ + π) / 2)) - π) + π) / 2) = y
  rw [s0c_c1_alpha_T hθ, hKθ, s0c_c1_T_alpha]

/-! ## C1 part 2: null sets, absolute continuity, `A_∞` (from the interval threshold) -/

/-- Images under `α` and `T` and `K` preserve measurability. -/
theorem s0c_c1_meas_img {f : ℝ → ℝ} {s X : Set ℝ} (hf : ContinuousOn f s) (hi : InjOn f s)
    (hX : MeasurableSet X) (hXs : X ⊆ s) : MeasurableSet (f '' X) :=
  hX.image_of_continuousOn_injOn (hf.mono hXs) (hi.mono hXs)

/-! ## C1 part 3: the interval threshold -/

theorem s0c_c1_T_contOn :
    ContinuousOn (fun s : ℝ => Real.tan ((s + π) / 2)) (Ioo (-(2 * π)) 0) :=
  fun _ hs => (s0c_c1_T_hasDerivAt hs).continuousAt.continuousWithinAt

theorem s0c_c1_imgIcc {f : ℝ → ℝ} {x y : ℝ} (hxy : x ≤ y) (hf : MonotoneOn f (Icc x y))
    (hc : ContinuousOn f (Icc x y)) : f '' Icc x y = Icc (f x) (f y) := by
  refine Subset.antisymm ?_ (intermediate_value_Icc hxy hc)
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨hf (left_mem_Icc.mpr hxy) ht ht.1, hf ht (right_mem_Icc.mpr hxy) ht.2⟩

theorem s0c_c1_TIcc {p q : ℝ} (hp : -(2 * π) < p) (hq : q < 0) (hpq : p ≤ q) :
    (fun s : ℝ => Real.tan ((s + π) / 2)) '' Icc p q =
      Icc (Real.tan ((p + π) / 2)) (Real.tan ((q + π) / 2)) := by
  have hsub : Icc p q ⊆ Ioo (-(2 * π)) 0 := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  exact s0c_c1_imgIcc hpq (s0c_c1_T_strictMonoOn.monotoneOn.mono hsub) (s0c_c1_T_contOn.mono hsub)

theorem s0c_c1_Tvol {X : Set ℝ} (hX : MeasurableSet X) (hXs : X ⊆ Ioo (-(2 * π)) 0) :
    volume ((fun s : ℝ => Real.tan ((s + π) / 2)) '' X) =
      ∫⁻ s in X, ENNReal.ofReal (1 / (2 * Real.sin (s / 2) ^ 2)) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul hX
    (fun s hs => (s0c_c1_T_hasDerivAt (hXs hs)).hasDerivWithinAt)
    (s0c_c1_T_strictMonoOn.injOn.mono hXs) (fun _ => 1)
  simp only [setLIntegral_const, one_mul, mul_one] at h
  rw [h]
  refine setLIntegral_congr_fun hX (fun s _ => ?_)
  have hc : Real.cos ((s + π) / 2) = -Real.sin (s / 2) := by
    rw [show (s + π) / 2 = s / 2 + π / 2 by ring, Real.cos_add_pi_div_two]
  rw [hc, neg_sq, abs_of_nonneg (by positivity)]
  congr 1
  ring

/-- Volume of a reflected set. -/
theorem s0c_c1_vol_refl (c : ℝ) {X : Set ℝ} (hX : MeasurableSet X) :
    volume ((fun s : ℝ => c - s) '' X) = volume X := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul hX
    (fun s _ => ((hasDerivAt_id s).const_sub c).hasDerivWithinAt)
    (fun x _ y _ hxy => by simpa using hxy) (fun _ => 1)
  simpa [setLIntegral_const] using h

theorem s0c_c1_sin_lb {y : ℝ} (h0 : 0 ≤ y) (hπ : y ≤ π) :
    2 / π * min y (π - y) ≤ Real.sin y := by
  rcases le_total y (π / 2) with h | h
  · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans
      (Real.mul_le_sin h0 h)
  · rw [← Real.sin_pi_sub]
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)).trans
      (Real.mul_le_sin (by linarith) (by linarith))

theorem s0c_c1_sin_ub {y : ℝ} (h0 : 0 ≤ y) (hπ : y ≤ π) : Real.sin y ≤ min y (π - y) :=
  le_min (Real.sin_le h0) (by rw [← Real.sin_pi_sub]; exact Real.sin_le (by linarith))

/-- Two-sided bound for `|T(X)|` on an interval `[p, q]` with `|[p,q]| ≤ Λ·dist([p,q], {-2π,0})`. -/
theorem s0c_c1_TB {p q Λ : ℝ} (hp : -(2 * π) < p) (hq : q < 0) (hpq : p ≤ q) (hΛ : 0 ≤ Λ)
    (hlen : q - p ≤ Λ * min (p + 2 * π) (-q)) {X : Set ℝ} (hX : MeasurableSet X)
    (hXs : X ⊆ Icc p q) :
    2 / ((1 + Λ) ^ 2 * min (p + 2 * π) (-q) ^ 2) * (volume X).toReal ≤
        (volume ((fun s : ℝ => Real.tan ((s + π) / 2)) '' X)).toReal ∧
      (volume ((fun s : ℝ => Real.tan ((s + π) / 2)) '' X)).toReal ≤
        π ^ 2 / (2 * min (p + 2 * π) (-q) ^ 2) * (volume X).toReal := by
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = min (p + 2 * π) (-q) := ⟨_, rfl⟩
  rw [← hεdef] at hlen ⊢
  have hε : 0 < ε := by rw [hεdef]; exact lt_min (by linarith) (by linarith)
  have hεp : ε ≤ p + 2 * π := by rw [hεdef]; exact min_le_left _ _
  have hεq : ε ≤ -q := by rw [hεdef]; exact min_le_right _ _
  have hXs' : X ⊆ Ioo (-(2 * π)) 0 := fun s hs =>
    ⟨by linarith [(hXs hs).1], by linarith [(hXs hs).2]⟩
  have hb : ∀ s ∈ X, ε / π ≤ Real.sin (-(s / 2)) ∧ Real.sin (-(s / 2)) ≤ (1 + Λ) * ε / 2 := by
    intro s hs
    obtain ⟨h1, h2⟩ := hXs hs
    have hy0 : 0 ≤ -(s / 2) := by linarith
    have hyπ : -(s / 2) ≤ π := by linarith
    have hΛε : (1 + Λ) * ε / 2 = ε / 2 + Λ * ε / 2 := by ring
    constructor
    · refine le_trans ?_ (s0c_c1_sin_lb hy0 hyπ)
      have : ε / 2 ≤ min (-(s / 2)) (π - -(s / 2)) := le_min (by linarith) (by linarith)
      calc ε / π = 2 / π * (ε / 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
    · refine (s0c_c1_sin_ub hy0 hyπ).trans ?_
      rcases min_choice (p + 2 * π) (-q) with hc | hc
      · rw [← hεdef] at hc
        exact (min_le_right _ _).trans (by rw [hΛε]; linarith)
      · rw [← hεdef] at hc
        exact (min_le_left _ _).trans (by rw [hΛε]; linarith)
  have hval : ∀ s ∈ X, 2 / ((1 + Λ) ^ 2 * ε ^ 2) ≤ 1 / (2 * Real.sin (s / 2) ^ 2) ∧
      1 / (2 * Real.sin (s / 2) ^ 2) ≤ π ^ 2 / (2 * ε ^ 2) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hb s hs
    have hS : Real.sin (s / 2) ^ 2 = Real.sin (-(s / 2)) ^ 2 := by rw [Real.sin_neg, neg_sq]
    rw [hS]
    obtain ⟨S, hSd⟩ : ∃ S, S = Real.sin (-(s / 2)) := ⟨_, rfl⟩
    rw [← hSd] at h1 h2 ⊢
    have hS0 : 0 < S := lt_of_lt_of_le (by positivity) h1
    have h2S : 0 < 2 * S ^ 2 := mul_pos two_pos (pow_pos hS0 2)
    constructor
    · rw [div_le_div_iff₀ (by positivity) h2S]
      have h4 := pow_le_pow_left₀ hS0.le h2 2
      have e : ((1 + Λ) * ε / 2) ^ 2 = (1 + Λ) ^ 2 * ε ^ 2 / 4 := by ring
      rw [e] at h4
      linarith
    · rw [div_le_div_iff₀ h2S (by positivity)]
      have h4 := pow_le_pow_left₀ (by positivity) h1 2
      have e : (ε / π) ^ 2 * π ^ 2 = ε ^ 2 := by field_simp
      have h5 : ε ^ 2 ≤ S ^ 2 * π ^ 2 := by
        rw [← e]; exact mul_le_mul_of_nonneg_right h4 (sq_nonneg π)
      nlinarith
  rw [s0c_c1_Tvol hX hXs']
  have hlo : ENNReal.ofReal (2 / ((1 + Λ) ^ 2 * ε ^ 2)) * volume X ≤
      ∫⁻ s in X, ENNReal.ofReal (1 / (2 * Real.sin (s / 2) ^ 2)) :=
    (setLIntegral_const X _).symm.trans_le
      (setLIntegral_mono' hX fun s hs => ENNReal.ofReal_le_ofReal (hval s hs).1)
  have hhi : ∫⁻ s in X, ENNReal.ofReal (1 / (2 * Real.sin (s / 2) ^ 2)) ≤
      ENNReal.ofReal (π ^ 2 / (2 * ε ^ 2)) * volume X :=
    (setLIntegral_mono' hX fun s hs => ENNReal.ofReal_le_ofReal (hval s hs).2).trans_eq
      (setLIntegral_const X _)
  have hXf : volume X ≠ ⊤ := ne_top_of_le_ne_top
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (measure_mono hXs)
  have hRf : ENNReal.ofReal (π ^ 2 / (2 * ε ^ 2)) * volume X ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hXf
  constructor
  · have := ENNReal.toReal_mono (ne_top_of_le_ne_top hRf hhi) hlo
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  · have := ENNReal.toReal_mono hRf hhi
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this

/-- Doubling of the lift `K` from the power form of its inverse `G`. -/
theorem s0c_c1_dbl {K G : ℝ → ℝ} (hK : StrictMono K) (hG : StrictMono G)
    (hGK : ∀ θ, G (K θ) = θ) (hper : ∀ θ, K (θ + 2 * π) = K θ + 2 * π)
    {C' δ' : ℝ} (hC' : 0 < C') (hδ' : 0 < δ')
    (hP : ∀ a b : ℝ, a < b → b - a ≤ 2 * π → ∀ A ⊆ Icc a b, MeasurableSet A →
      volume (G '' A) ≤
        ENNReal.ofReal (C' * ((volume A).toReal / (b - a)) ^ δ') * volume (G '' Icc a b)) :
    ∀ a a' b' c : ℝ, a ≤ a' → a' < b' → b' ≤ c → c - a ≤ 2 * π → c - a ≤ 5 * (b' - a') →
      (1 / (5 * C')) ^ δ'⁻¹ * (K c - K a) ≤ K b' - K a' := by
  intro a a' b' c ha hab hb hc h5
  have himg : ∀ x y, G '' Icc (K x) (K y) = Icc x y := fun x y => by
    ext t
    constructor
    · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
      exact ⟨(hGK x).symm.trans_le (hG.monotone h1), (hG.monotone h2).trans_eq (hGK y)⟩
    · intro ht
      exact ⟨K t, ⟨hK.monotone ht.1, hK.monotone ht.2⟩, hGK t⟩
  have hac : a < c := by linarith
  have hKac : K a < K c := hK hac
  have hKc2 : K c - K a ≤ 2 * π := by
    have := hK.monotone (show c ≤ a + 2 * π by linarith)
    rw [hper] at this
    linarith
  have hKab : 0 ≤ K b' - K a' := sub_nonneg.mpr (hK.monotone hab.le)
  have h := hP (K a) (K c) hKac hKc2 (Icc (K a') (K b'))
    (Icc_subset_Icc (hK.monotone ha) (hK.monotone hb)) measurableSet_Icc
  rw [himg, himg, Real.volume_Icc, Real.volume_Icc, Real.volume_Icc,
    ENNReal.toReal_ofReal hKab] at h
  obtain ⟨r, hr⟩ : ∃ r, r = (K b' - K a') / (K c - K a) := ⟨_, rfl⟩
  rw [← hr] at h
  have hr0 : 0 ≤ r := by rw [hr]; exact div_nonneg hKab (by linarith)
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal (mul_nonneg hC'.le (Real.rpow_nonneg hr0 _)),
    ENNReal.toReal_ofReal (by linarith)] at h'
  have h1 : 1 / (5 * C') ≤ r ^ δ' := by
    rw [div_le_iff₀ (by positivity)]
    by_contra hlt
    push_neg at hlt
    nlinarith [mul_lt_mul_of_pos_left hlt (sub_pos.mpr hac)]
  have h2 : (1 / (5 * C')) ^ δ'⁻¹ ≤ r :=
    calc (1 / (5 * C')) ^ δ'⁻¹ ≤ (r ^ δ') ^ δ'⁻¹ :=
          Real.rpow_le_rpow (by positivity) h1 (by positivity)
      _ = r := Real.rpow_rpow_inv hr0 hδ'.ne'
  calc (1 / (5 * C')) ^ δ'⁻¹ * (K c - K a) ≤ r * (K c - K a) :=
        mul_le_mul_of_nonneg_right h2 (by linarith)
    _ = K b' - K a' := by rw [hr]; field_simp

/-- The local case: on `[p, q]` with `|[p,q]| ≤ 4·dist([p,q], {-2π,0})`, small `T`-measure
of `Y` forces small `T`-measure of `K(Y)`. -/
theorem s0c_c1_loc {K : ℝ → ℝ} (hK : StrictMono K) (hKc : Continuous K)
    (hper : ∀ θ, K (θ + 2 * π) = K θ + 2 * π) (hK0 : K 0 = 0)
    {C δ η : ℝ} (hC : 0 < C) (hδ : 0 < δ) (hη : 0 < η)
    (hP : ∀ a b : ℝ, a < b → b - a ≤ 2 * π → ∀ A ⊆ Icc a b, MeasurableSet A →
      volume (K '' A) ≤
        ENNReal.ofReal (C * ((volume A).toReal / (b - a)) ^ δ) * volume (K '' Icc a b))
    (hD : ∀ a a' b' c : ℝ, a ≤ a' → a' < b' → b' ≤ c → c - a ≤ 2 * π →
      c - a ≤ 5 * (b' - a') → η * (K c - K a) ≤ K b' - K a')
    {p q : ℝ} (hp : -(2 * π) < p) (hq : q < 0) (hpq : p < q)
    (hlen : q - p ≤ 4 * min (p + 2 * π) (-q))
    {Y : Set ℝ} (hY : MeasurableSet Y) (hYs : Y ⊆ Icc p q)
    (hsmall : (volume ((fun s : ℝ => Real.tan ((s + π) / 2)) '' Y)).toReal ≤
      4 / (25 * π ^ 2) * (1 / (2 * (π ^ 2 * (1 + 1 / η) ^ 2 / 4) * C)) ^ δ⁻¹ *
        (Real.tan ((q + π) / 2) - Real.tan ((p + π) / 2))) :
    (volume ((fun s : ℝ => Real.tan ((s + π) / 2)) '' (K '' Y))).toReal ≤
      1 / 2 * (Real.tan ((K q + π) / 2) - Real.tan ((K p + π) / 2)) := by
  obtain ⟨M₂, hM₂⟩ : ∃ M₂, M₂ = π ^ 2 * (1 + 1 / η) ^ 2 / 4 := ⟨_, rfl⟩
  rw [← hM₂] at hsmall
  have hM₂0 : 0 < M₂ := by rw [hM₂]; positivity
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ = (1 / (2 * M₂ * C)) ^ δ⁻¹ := ⟨_, rfl⟩
  rw [← hx₀] at hsmall
  have hx₀0 : 0 ≤ x₀ := by rw [hx₀]; positivity
  have hx₀δ : x₀ ^ δ = 1 / (2 * M₂ * C) := by
    rw [hx₀]; exact Real.rpow_inv_rpow (by positivity) hδ.ne'
  have hK2 : K (-(2 * π)) = -(2 * π) := by
    have := hper (-(2 * π))
    rw [show -(2 * π) + 2 * π = 0 by ring, hK0] at this
    linarith
  have hε : 0 < min (p + 2 * π) (-q) := lt_min (by linarith) (by linarith)
  have hεp := min_le_left (p + 2 * π) (-q)
  have hεq := min_le_right (p + 2 * π) (-q)
  obtain ⟨hTY, -⟩ := s0c_c1_TB hp hq hpq.le (by norm_num) hlen hY hYs
  obtain ⟨-, hTJ⟩ := s0c_c1_TB hp hq hpq.le (by norm_num) hlen measurableSet_Icc subset_rfl
  have hTpq : Real.tan ((p + π) / 2) ≤ Real.tan ((q + π) / 2) :=
    s0c_c1_T_strictMonoOn.monotoneOn ⟨hp, by linarith⟩ ⟨by linarith, hq⟩ hpq.le
  rw [s0c_c1_TIcc hp hq hpq.le, Real.volume_Icc, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hTpq), ENNReal.toReal_ofReal (by linarith)] at hTJ
  obtain ⟨y, hyd⟩ : ∃ y, y = (volume Y).toReal := ⟨_, rfl⟩
  rw [← hyd] at hTY
  have hy0 : 0 ≤ y := by rw [hyd]; exact ENNReal.toReal_nonneg
  have hyb : y / (q - p) ≤ x₀ := by
    rw [div_le_iff₀ (by linarith)]
    have h2 : 4 / (25 * π ^ 2) * x₀ * (Real.tan ((q + π) / 2) - Real.tan ((p + π) / 2)) ≤
        4 / (25 * π ^ 2) * x₀ * (π ^ 2 / (2 * min (p + 2 * π) (-q) ^ 2) * (q - p)) :=
      mul_le_mul_of_nonneg_left hTJ (by positivity)
    have h3 := (hTY.trans hsmall).trans h2
    have e1 : 4 / (25 * π ^ 2) * x₀ * (π ^ 2 / (2 * min (p + 2 * π) (-q) ^ 2) * (q - p)) =
        2 / ((1 + 4) ^ 2 * min (p + 2 * π) (-q) ^ 2) * (x₀ * (q - p)) := by
      field_simp
      ring
    rw [e1] at h3
    exact le_of_mul_le_mul_left h3 (by positivity)
  -- the `K`-side
  have hKp : -(2 * π) < K p := by rw [← hK2]; exact hK hp
  have hKq : K q < 0 := by rw [← hK0]; exact hK hq
  have hKpq : K p < K q := hK hpq
  have hd1 : η * (K q - K p) ≤ -K q := by
    have := hD p q 0 0 hpq.le hq le_rfl (by linarith) (by linarith)
    rw [hK0] at this
    nlinarith [mul_neg_of_pos_of_neg hη hKq]
  have hd2 : η * (K q - K p) ≤ K p + 2 * π := by
    have := hD (-(2 * π)) (-(2 * π)) p q le_rfl hp hpq.le (by linarith) (by linarith)
    rw [hK2] at this
    nlinarith
  have hlenK : K q - K p ≤ 1 / η * min (K p + 2 * π) (-K q) := by
    have := le_min hd2 hd1
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hη]
    linarith
  have hKYm : MeasurableSet (K '' Y) :=
    hY.image_of_continuousOn_injOn hKc.continuousOn hK.injective.injOn
  have hKYs : K '' Y ⊆ Icc (K p) (K q) := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨hK.monotone (hYs hs).1, hK.monotone (hYs hs).2⟩
  have hKIcc : K '' Icc p q = Icc (K p) (K q) :=
    s0c_c1_imgIcc hpq.le (hK.monotone.monotoneOn _) hKc.continuousOn
  obtain ⟨-, hTKY⟩ := s0c_c1_TB hKp hKq hKpq.le (by positivity) hlenK hKYm hKYs
  obtain ⟨hTKJ, -⟩ := s0c_c1_TB hKp hKq hKpq.le (by positivity) hlenK measurableSet_Icc subset_rfl
  have hTKpq : Real.tan ((K p + π) / 2) ≤ Real.tan ((K q + π) / 2) :=
    s0c_c1_T_strictMonoOn.monotoneOn ⟨hKp, by linarith⟩ ⟨by linarith, hKq⟩ hKpq.le
  rw [s0c_c1_TIcc hKp hKq hKpq.le, Real.volume_Icc, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hTKpq), ENNReal.toReal_ofReal (by linarith)] at hTKJ
  -- power form
  have hpw := hP p q hpq (by linarith) Y hYs hY
  rw [hKIcc, Real.volume_Icc, ← hyd] at hpw
  have hpw' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top) hpw
  have hyq : 0 ≤ y / (q - p) := div_nonneg hy0 (by linarith)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hC.le (Real.rpow_nonneg hyq _)),
    ENNReal.toReal_ofReal (by linarith)] at hpw'
  have hrp : (y / (q - p)) ^ δ ≤ 1 / (2 * M₂ * C) :=
    hx₀δ ▸ Real.rpow_le_rpow hyq hyb hδ.le
  have hkY : (volume (K '' Y)).toReal ≤ C * (1 / (2 * M₂ * C)) * (K q - K p) :=
    hpw'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrp hC.le) (by linarith))
  obtain ⟨ε', hε'⟩ : ∃ ε', ε' = min (K p + 2 * π) (-K q) := ⟨_, rfl⟩
  rw [← hε'] at hTKY hTKJ
  have hε'0 : 0 < ε' := by rw [hε']; exact lt_min (by linarith) (by linarith)
  calc (volume ((fun s : ℝ => Real.tan ((s + π) / 2)) '' (K '' Y))).toReal
      ≤ π ^ 2 / (2 * ε' ^ 2) * (volume (K '' Y)).toReal := hTKY
    _ ≤ π ^ 2 / (2 * ε' ^ 2) * (C * (1 / (2 * M₂ * C)) * (K q - K p)) :=
        mul_le_mul_of_nonneg_left hkY (by positivity)
    _ = 1 / 2 * (2 / ((1 + 1 / η) ^ 2 * ε' ^ 2) * (K q - K p)) := by
        rw [hM₂]
        field_simp
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hTKJ (by norm_num)

/-- `cot x ≥ 3 cot 3x` for `0 < x`, `3x < π`. -/
theorem s0c_c1_cot3 {x : ℝ} (hx : 0 < x) (hx3 : 3 * x < π) :
    3 * (Real.tan (3 * x))⁻¹ ≤ (Real.tan x)⁻¹ := by
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx (by linarith)
  have hs3 : 0 < Real.sin (3 * x) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hx3
  have hc : 0 ≤ Real.cos x :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, inv_div, inv_div, ← mul_div_assoc,
    div_le_div_iff₀ hs3 hs]
  have key : Real.cos x * Real.sin (3 * x) - 3 * Real.cos (3 * x) * Real.sin x =
      8 * Real.sin x ^ 3 * Real.cos x := by
    rw [Real.sin_three_mul, Real.cos_three_mul]
    linear_combination (-12 * Real.sin x * Real.cos x) * Real.sin_sq_add_cos_sq x
  nlinarith [mul_nonneg (pow_nonneg hs.le 3) hc]

/-- The cotangent comparison behind the global case. -/
theorem s0c_c1_cot_sum {p q r η : ℝ} (hη : 0 < η) (hp : 0 < p) (hpq : p < q) (hr : 0 < r)
    (hqr : q + r < 2 * π) (h1 : η * q ≤ q - p) (h2 : η * p ≤ r) :
    (Real.tan (p / 2))⁻¹ + (Real.tan (r / 2))⁻¹ ≤
      π ^ 2 / 4 * (1 + 1 / η) / η * ((Real.tan (p / 2))⁻¹ - (Real.tan (q / 2))⁻¹) := by
  have hη1 : η < 1 := by nlinarith
  have sp : 0 < Real.sin (p / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have sq : 0 < Real.sin (q / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have sr : 0 < Real.sin (r / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsum : (Real.tan (p / 2))⁻¹ + (Real.tan (r / 2))⁻¹ =
      Real.sin ((p + r) / 2) / (Real.sin (p / 2) * Real.sin (r / 2)) := by
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, inv_div, inv_div,
      show (p + r) / 2 = p / 2 + r / 2 by ring, Real.sin_add]
    field_simp
    ring
  have hdif : (Real.tan (p / 2))⁻¹ - (Real.tan (q / 2))⁻¹ =
      Real.sin ((q - p) / 2) / (Real.sin (p / 2) * Real.sin (q / 2)) := by
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, inv_div, inv_div,
      show (q - p) / 2 = q / 2 - p / 2 by ring, Real.sin_sub]
    field_simp
  have hA : Real.sin ((p + r) / 2) ≤ (1 + 1 / η) * (π / 2) * Real.sin (r / 2) := by
    have u := s0c_c1_sin_ub (y := (p + r) / 2) (by linarith) (by linarith)
    have l := s0c_c1_sin_lb (y := r / 2) (by linarith) (by linarith)
    have hm : min ((p + r) / 2) (π - (p + r) / 2) ≤ (1 + 1 / η) * min (r / 2) (π - r / 2) := by
      rw [mul_min_of_nonneg _ _ (by positivity)]
      refine le_min ((min_le_left _ _).trans ?_) ((min_le_right _ _).trans ?_)
      · have : p ≤ r / η := by rw [le_div_iff₀ hη]; linarith
        have e : (1 + 1 / η) * (r / 2) = r / 2 + r / η / 2 := by ring
        rw [e]
        linarith
      · have e : (1 + 1 / η) * (π - r / 2) = (π - r / 2) + 1 / η * (π - r / 2) := by ring
        have : 0 ≤ 1 / η * (π - r / 2) := mul_nonneg (by positivity) (by linarith)
        rw [e]
        linarith
    calc Real.sin ((p + r) / 2) ≤ (1 + 1 / η) * min (r / 2) (π - r / 2) := u.trans hm
      _ = (1 + 1 / η) * (π / 2) * (2 / π * min (r / 2) (π - r / 2)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left l (by positivity)
  have hB : Real.sin (q / 2) ≤ 1 / η * (π / 2) * Real.sin ((q - p) / 2) := by
    have u := s0c_c1_sin_ub (y := q / 2) (by linarith) (by linarith)
    have l := s0c_c1_sin_lb (y := (q - p) / 2) (by linarith) (by linarith)
    have hm : min (q / 2) (π - q / 2) ≤ 1 / η * min ((q - p) / 2) (π - (q - p) / 2) := by
      rw [mul_min_of_nonneg _ _ (by positivity)]
      refine le_min ((min_le_left _ _).trans ?_) ((min_le_right _ _).trans ?_)
      · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hη]
        nlinarith
      · have h1η : 1 ≤ 1 / η := by rw [le_div_iff₀ hη]; linarith
        have hpos : 0 ≤ π - (q - p) / 2 := by linarith
        nlinarith [mul_nonneg (sub_nonneg.mpr h1η) hpos]
    calc Real.sin (q / 2) ≤ 1 / η * min ((q - p) / 2) (π - (q - p) / 2) := u.trans hm
      _ = 1 / η * (π / 2) * (2 / π * min ((q - p) / 2) (π - (q - p) / 2)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left l (by positivity)
  have hprod := mul_le_mul hA hB sq.le (by positivity)
  rw [hsum, hdif, div_le_iff₀ (mul_pos sp sr)]
  have e : π ^ 2 / 4 * (1 + 1 / η) / η *
      (Real.sin ((q - p) / 2) / (Real.sin (p / 2) * Real.sin (q / 2))) *
        (Real.sin (p / 2) * Real.sin (r / 2)) =
      π ^ 2 / 4 * (1 + 1 / η) / η * Real.sin ((q - p) / 2) * Real.sin (r / 2) /
        Real.sin (q / 2) := by
    field_simp
  rw [e, le_div_iff₀ sq]
  calc Real.sin ((p + r) / 2) * Real.sin (q / 2) ≤ _ := hprod
    _ = _ := by ring

/-- The threshold for `H = T ∘ K ∘ α` on `[a, b]` with `a + b ≥ 0` (real-valued form). -/
theorem s0c_c1_half {K : ℝ → ℝ} (hK : StrictMono K) (hKc : Continuous K)
    (hper : ∀ θ, K (θ + 2 * π) = K θ + 2 * π) (hK0 : K 0 = 0)
    {C δ η : ℝ} (hC : 0 < C) (hδ : 0 < δ) (hη : 0 < η)
    (hP : ∀ a b : ℝ, a < b → b - a ≤ 2 * π → ∀ A ⊆ Icc a b, MeasurableSet A →
      volume (K '' A) ≤
        ENNReal.ofReal (C * ((volume A).toReal / (b - a)) ^ δ) * volume (K '' Icc a b))
    (hD : ∀ a a' b' c : ℝ, a ≤ a' → a' < b' → b' ≤ c → c - a ≤ 2 * π →
      c - a ≤ 5 * (b' - a') → η * (K c - K a) ≤ K b' - K a')
    {a b : ℝ} (hab : a < b) (hsum : 0 ≤ a + b) {F : Set ℝ} (hFs : F ⊆ Icc a b)
    (hF : MeasurableSet F)
    (hFv : (volume F).toReal ≤
      4 / (25 * π ^ 2) * (1 / (2 * (π ^ 2 * (1 + 1 / η) ^ 2 / 4) * C)) ^ δ⁻¹ / 3 * (b - a)) :
    (volume ((fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2)) '' F)).toReal ≤
      (1 - 1 / (2 * (π ^ 2 / 4 * (1 + 1 / η) / η + 1))) *
        (Real.tan ((K (2 * Real.arctan b - π) + π) / 2) -
          Real.tan ((K (2 * Real.arctan a - π) + π) / 2)) := by
  obtain ⟨βL, hβL⟩ : ∃ βL, βL =
      4 / (25 * π ^ 2) * (1 / (2 * (π ^ 2 * (1 + 1 / η) ^ 2 / 4) * C)) ^ δ⁻¹ := ⟨_, rfl⟩
  rw [← hβL] at hFv
  obtain ⟨C₉, hC₉⟩ : ∃ C₉, C₉ = π ^ 2 / 4 * (1 + 1 / η) / η := ⟨_, rfl⟩
  rw [← hC₉]
  have hβL0 : 0 ≤ βL := by rw [hβL]; positivity
  have hC₉0 : 0 < C₉ := by rw [hC₉]; positivity
  have hK2 : K (-(2 * π)) = -(2 * π) := by
    have := hper (-(2 * π))
    rw [show -(2 * π) + 2 * π = 0 by ring, hK0] at this
    linarith
  obtain ⟨s₁, hs₁⟩ : ∃ s, s = 2 * Real.arctan a - π := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂⟩ : ∃ s, s = 2 * Real.arctan b - π := ⟨_, rfl⟩
  have hs₁m : s₁ ∈ Ioo (-(2 * π)) 0 := hs₁ ▸ s0c_c1_alpha_mem a
  have hs₂m : s₂ ∈ Ioo (-(2 * π)) 0 := hs₂ ▸ s0c_c1_alpha_mem b
  have hs12 : s₁ < s₂ := by rw [hs₁, hs₂]; exact s0c_c1_alpha_strictMono hab
  have hnear : -s₂ ≤ s₁ + 2 * π := by
    have : Real.arctan (-b) ≤ Real.arctan a := Real.arctan_strictMono.monotone (by linarith)
    rw [Real.arctan_neg] at this
    rw [hs₁, hs₂]
    linarith
  have hTa : Real.tan ((s₁ + π) / 2) = a := by rw [hs₁]; exact s0c_c1_T_alpha a
  have hTb : Real.tan ((s₂ + π) / 2) = b := by rw [hs₂]; exact s0c_c1_T_alpha b
  rw [← hs₁, ← hs₂]
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = (fun t : ℝ => 2 * Real.arctan t - π) '' F := ⟨_, rfl⟩
  have hYm : MeasurableSet Y := by
    rw [hYdef]
    exact hF.image_of_continuousOn_injOn (by fun_prop)
      s0c_c1_alpha_strictMono.injective.injOn
  have hYs : Y ⊆ Icc s₁ s₂ := by
    rw [hYdef, hs₁, hs₂]
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨s0c_c1_alpha_strictMono.monotone (hFs ht).1,
      s0c_c1_alpha_strictMono.monotone (hFs ht).2⟩
  have hTY : (fun s : ℝ => Real.tan ((s + π) / 2)) '' Y = F := by
    rw [hYdef, image_image]
    exact (image_congr fun t _ => s0c_c1_T_alpha t).trans (image_id' F)
  have hHF : (fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2)) '' F =
      (fun s : ℝ => Real.tan ((s + π) / 2)) '' (K '' Y) := by
    rw [hYdef, image_image, image_image]
  rw [hHF]
  have hFv' : (volume ((fun s : ℝ => Real.tan ((s + π) / 2)) '' Y)).toReal ≤
      βL / 3 * (b - a) := by rw [hTY]; exact hFv
  have hKs₁ := s0c_c1_Kmem hK hper hK0 hs₁m
  have hKs₂ := s0c_c1_Kmem hK hper hK0 hs₂m
  have hTK12 : Real.tan ((K s₁ + π) / 2) ≤ Real.tan ((K s₂ + π) / 2) :=
    s0c_c1_T_strictMonoOn.monotoneOn hKs₁ hKs₂ (hK.monotone hs12.le)
  -- finiteness: everything lives in `T(K([s₁, s₂]))`
  have hKIcc : ∀ x y, x ≤ y → K '' Icc x y = Icc (K x) (K y) := fun x y hxy =>
    s0c_c1_imgIcc hxy (hK.monotone.monotoneOn _) hKc.continuousOn
  have hbig : ∀ Z ⊆ Y, volume ((fun s : ℝ => Real.tan ((s + π) / 2)) '' (K '' Z)) ≠ ⊤ := by
    intro Z hZ
    refine ne_top_of_le_ne_top (b := volume (Icc (Real.tan ((K s₁ + π) / 2))
      (Real.tan ((K s₂ + π) / 2)))) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (measure_mono ?_)
    rw [← s0c_c1_TIcc hKs₁.1 hKs₂.2 (hK.monotone hs12.le), ← hKIcc _ _ hs12.le]
    exact image_mono (image_mono (hZ.trans hYs))
  by_cases hloc : s₂ - s₁ ≤ 4 * min (s₁ + 2 * π) (-s₂)
  · have h := s0c_c1_loc hK hKc hper hK0 hC hδ hη hP hD hs₁m.1 hs₂m.2 hs12 hloc hYm hYs (by
      rw [hTa, hTb, ← hβL]
      exact hFv'.trans (by nlinarith))
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (sub_nonneg.mpr hTK12))
    have : 1 / (2 * (C₉ + 1)) ≤ 1 / 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith
  · push_neg at hloc
    rw [min_eq_right hnear] at hloc
    have hε : 0 < -s₂ := by linarith [hs₂m.2]
    have h5 : s₁ < 5 * s₂ := by linarith
    have h3m : 3 * s₂ ∈ Ioo (-(2 * π)) 0 := ⟨by linarith [hs₁m.1], by linarith⟩
    have hDloc : s₂ - 3 * s₂ ≤ 4 * min (3 * s₂ + 2 * π) (-s₂) := by
      rw [mul_min_of_nonneg _ _ (by norm_num)]
      exact le_min (by linarith [hs₁m.1, Real.pi_pos]) (by linarith)
    -- `λ(D) ≥ λ(J)/3`
    have hlam : b - a ≤ 3 * (b - Real.tan ((3 * s₂ + π) / 2)) := by
      have hx : 0 < -s₂ / 2 := by linarith
      have hx3 : 3 * (-s₂ / 2) < π := by linarith [hs₁m.1, Real.pi_pos]
      have hc3 := s0c_c1_cot3 hx hx3
      have e1 : b = (Real.tan (-s₂ / 2))⁻¹ := by
        rw [← hTb, show (s₂ + π) / 2 = π / 2 - -s₂ / 2 by ring, Real.tan_pi_div_two_sub]
      have e2 : Real.tan ((3 * s₂ + π) / 2) = (Real.tan (3 * (-s₂ / 2)))⁻¹ := by
        rw [show (3 * s₂ + π) / 2 = π / 2 - 3 * (-s₂ / 2) by ring, Real.tan_pi_div_two_sub]
      have e3 : -(Real.tan (-s₂ / 2))⁻¹ ≤ a := by
        rw [← hTa]
        have hm : Real.tan ((-(2 * π) + -s₂ + π) / 2) ≤ Real.tan ((s₁ + π) / 2) :=
          s0c_c1_T_strictMonoOn.monotoneOn ⟨by linarith, by linarith [hs₂m.1]⟩ hs₁m
            (by linarith)
        rwa [show (-(2 * π) + -s₂ + π) / 2 = -(π / 2 - -s₂ / 2) by ring, Real.tan_neg,
          Real.tan_pi_div_two_sub] at hm
      rw [e2]
      linarith
    -- the local piece
    obtain ⟨YD, hYD⟩ : ∃ YD, YD = Y ∩ Icc (3 * s₂) s₂ := ⟨_, rfl⟩
    have hYDm : MeasurableSet YD := by rw [hYD]; exact hYm.inter measurableSet_Icc
    have hYDs : YD ⊆ Icc (3 * s₂) s₂ := by rw [hYD]; exact inter_subset_right
    have hfinTY : volume ((fun s : ℝ => Real.tan ((s + π) / 2)) '' Y) ≠ ⊤ := by
      rw [hTY]
      exact ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (measure_mono hFs)
    have hTYD : (volume ((fun s : ℝ => Real.tan ((s + π) / 2)) '' YD)).toReal ≤
        βL * (Real.tan ((s₂ + π) / 2) - Real.tan ((3 * s₂ + π) / 2)) := by
      have hmono : (volume ((fun s : ℝ => Real.tan ((s + π) / 2)) '' YD)).toReal ≤
          (volume ((fun s : ℝ => Real.tan ((s + π) / 2)) '' Y)).toReal :=
        ENNReal.toReal_mono hfinTY (measure_mono (image_mono (by rw [hYD]; exact inter_subset_left)))
      rw [hTb]
      nlinarith [mul_le_mul_of_nonneg_left hlam (by positivity : (0 : ℝ) ≤ βL / 3)]
    have hloc2 := s0c_c1_loc hK hKc hper hK0 hC hδ hη hP hD h3m.1 hs₂m.2 (by linarith) hDloc
      hYDm hYDs (by rw [← hβL]; exact hTYD)
    -- the rest
    obtain ⟨R, hR⟩ : ∃ R, R = Y \ Icc (3 * s₂) s₂ := ⟨_, rfl⟩
    have hK3 := s0c_c1_Kmem hK hper hK0 h3m
    have hRsub : (fun s : ℝ => Real.tan ((s + π) / 2)) '' (K '' R) ⊆
        Icc (Real.tan ((K s₁ + π) / 2)) (Real.tan ((K (3 * s₂) + π) / 2)) := by
      rw [← s0c_c1_TIcc hKs₁.1 hK3.2 (hK.monotone (by linarith)), ← hKIcc _ _ (by linarith)]
      refine image_mono (image_mono ?_)
      rw [hR]
      rintro s ⟨hsY, hsD⟩
      have hs := hYs hsY
      refine ⟨hs.1, ?_⟩
      by_contra hlt
      push_neg at hlt
      exact hsD ⟨hlt.le, hs.2⟩
    have hTK3 : Real.tan ((K s₁ + π) / 2) ≤ Real.tan ((K (3 * s₂) + π) / 2) :=
      s0c_c1_T_strictMonoOn.monotoneOn hKs₁ hK3 (hK.monotone (by linarith))
    have hRv : (volume ((fun s : ℝ => Real.tan ((s + π) / 2)) '' (K '' R))).toReal ≤
        Real.tan ((K (3 * s₂) + π) / 2) - Real.tan ((K s₁ + π) / 2) := by
      have := ENNReal.toReal_mono (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (measure_mono hRsub)
      rwa [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hTK3)] at this
    have hYU : Y = YD ∪ R := by rw [hYD, hR]; exact (inter_union_diff Y _).symm
    have hun : (volume ((fun s : ℝ => Real.tan ((s + π) / 2)) '' (K '' Y))).toReal ≤
        (volume ((fun s : ℝ => Real.tan ((s + π) / 2)) '' (K '' YD))).toReal +
          (volume ((fun s : ℝ => Real.tan ((s + π) / 2)) '' (K '' R))).toReal := by
      have hYDY : YD ⊆ Y := by rw [hYD]; exact inter_subset_left
      have hRY : R ⊆ Y := by rw [hR]; exact diff_subset
      rw [← ENNReal.toReal_add (hbig _ hYDY) (hbig _ hRY)]
      refine ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hbig _ hYDY, hbig _ hRY⟩) ?_
      rw [hYU, image_union, image_union]
      exact measure_union_le _ _
    -- the cotangent comparison
    have hc1 : η * (-K (3 * s₂)) ≤ -K (3 * s₂) - -K s₂ := by
      have := hD (3 * s₂) (3 * s₂) s₂ 0 le_rfl (by linarith) hs₂m.2.le
        (by linarith [hs₁m.1]) (by linarith)
      rw [hK0] at this
      linarith
    have hc2 : η * (-K s₂) ≤ K s₁ + 2 * π := by
      have := hD s₂ 0 (-s₂) (-s₂) hs₂m.2.le hε le_rfl (by linarith [hs₁m.1]) (by linarith)
      rw [hK0] at this
      have hm1 : K (-s₂) ≤ K s₁ + 2 * π := by
        rw [← hper]; exact hK.monotone hnear
      have hm2 : 0 ≤ K (-s₂) := by rw [← hK0]; exact hK.monotone hε.le
      nlinarith
    have hcs := s0c_c1_cot_sum hη (p := -K s₂) (q := -K (3 * s₂)) (r := K s₁ + 2 * π)
      (by linarith [hKs₂.2]) (by linarith [hK (show 3 * s₂ < s₂ by linarith)])
      (by linarith [hKs₁.1]) (by linarith [hK (show s₁ < 3 * s₂ by linarith)]) hc1 hc2
    rw [← hC₉] at hcs
    have v1 : Real.tan ((K s₂ + π) / 2) = (Real.tan (-K s₂ / 2))⁻¹ := by
      rw [show (K s₂ + π) / 2 = π / 2 - -K s₂ / 2 by ring, Real.tan_pi_div_two_sub]
    have v2 : Real.tan ((K (3 * s₂) + π) / 2) = (Real.tan (-K (3 * s₂) / 2))⁻¹ := by
      rw [show (K (3 * s₂) + π) / 2 = π / 2 - -K (3 * s₂) / 2 by ring, Real.tan_pi_div_two_sub]
    have v3 : Real.tan ((K s₁ + π) / 2) = -(Real.tan ((K s₁ + 2 * π) / 2))⁻¹ := by
      rw [show (K s₁ + π) / 2 = -(π / 2 - (K s₁ + 2 * π) / 2) by ring, Real.tan_neg,
        Real.tan_pi_div_two_sub]
    rw [← v1, ← v2] at hcs
    rw [show (Real.tan ((K s₁ + 2 * π) / 2))⁻¹ = -Real.tan ((K s₁ + π) / 2) by rw [v3]; ring]
      at hcs
    -- assemble
    obtain ⟨X, hX⟩ : ∃ X, X = Real.tan ((K s₂ + π) / 2) - Real.tan ((K (3 * s₂) + π) / 2) :=
      ⟨_, rfl⟩
    have hX0 : 0 ≤ X := by
      rw [hX]
      exact sub_nonneg.mpr (s0c_c1_T_strictMonoOn.monotoneOn hK3 hKs₂
        (hK.monotone (by linarith)))
    obtain ⟨S, hS⟩ : ∃ S, S = Real.tan ((K s₂ + π) / 2) - Real.tan ((K s₁ + π) / 2) := ⟨_, rfl⟩
    have hSX : S ≤ C₉ * X := by
      rw [hS, hX]
      convert hcs using 1
    have hkey : S / (2 * (C₉ + 1)) ≤ X / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have e2 : X / 2 * (2 * (C₉ + 1)) = C₉ * X + X := by ring
      rw [e2]
      linarith only [hSX, hX0]
    have e : (1 - 1 / (2 * (C₉ + 1))) * S = S - S / (2 * (C₉ + 1)) := by
      field_simp
    rw [← hS, e]
    have := hun.trans (add_le_add hloc2 hRv)
    linarith only [this, hkey, hX, hS]

/-- The interval threshold for `H = T ∘ K ∘ α` on all of `ℝ`. -/
theorem s0c_c1_thr {K : ℝ → ℝ} (hK : StrictMono K) (hKc : Continuous K)
    (hper : ∀ θ, K (θ + 2 * π) = K θ + 2 * π) (hK0 : K 0 = 0)
    (hpow : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ a b : ℝ, a < b → b - a ≤ 2 * π → ∀ A ⊆ Icc a b,
      MeasurableSet A → volume (K '' A) ≤
        ENNReal.ofReal (C * ((volume A).toReal / (b - a)) ^ δ) * volume (K '' Icc a b))
    (hdbl : ∃ η : ℝ, 0 < η ∧ ∀ a a' b' c : ℝ, a ≤ a' → a' < b' → b' ≤ c → c - a ≤ 2 * π →
      c - a ≤ 5 * (b' - a') → η * (K c - K a) ≤ K b' - K a') :
    ∃ β θ : ℝ, 0 < β ∧ β ≤ 1 ∧ 0 < θ ∧ θ < 1 ∧ ∀ a b : ℝ, a < b → ∀ F ⊆ Icc a b,
      MeasurableSet F → volume F ≤ ENNReal.ofReal (β * (b - a)) →
        volume ((fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2)) '' F) ≤
          ENNReal.ofReal θ *
            volume ((fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2)) '' Icc a b) := by
  obtain ⟨C, δ, hC, hδ, hP⟩ := hpow
  obtain ⟨η, hη, hD⟩ := hdbl
  obtain ⟨βL, hβL⟩ : ∃ βL, βL =
      4 / (25 * π ^ 2) * (1 / (2 * (π ^ 2 * (1 + 1 / η) ^ 2 / 4) * C)) ^ δ⁻¹ := ⟨_, rfl⟩
  obtain ⟨C₉, hC₉⟩ : ∃ C₉, C₉ = π ^ 2 / 4 * (1 + 1 / η) / η := ⟨_, rfl⟩
  have hβL0 : 0 < βL := by rw [hβL]; positivity
  have hC₉0 : 0 < C₉ := by rw [hC₉]; positivity
  have hθ1 : 0 < 1 / (2 * (C₉ + 1)) := by positivity
  have hθ2 : 1 / (2 * (C₉ + 1)) ≤ 1 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  refine ⟨min (βL / 3) 1, 1 - 1 / (2 * (C₉ + 1)), lt_min (by positivity) one_pos,
    min_le_right _ _, by linarith, by linarith, ?_⟩
  intro a b hab F hFs hFm hFv
  have hm := s0c_c1_Hmono hK hper hK0
  have hc := s0c_c1_Hcont hK hKc hper hK0
  have hHIcc : (fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2)) '' Icc a b =
      Icc (Real.tan ((K (2 * Real.arctan a - π) + π) / 2))
        (Real.tan ((K (2 * Real.arctan b - π) + π) / 2)) :=
    s0c_c1_imgIcc hab.le (hm.monotone.monotoneOn _) hc.continuousOn
  have hFr : (volume F).toReal ≤ βL / 3 * (b - a) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hFv
    rw [ENNReal.toReal_ofReal (mul_nonneg (by positivity) (by linarith))] at this
    exact this.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith))
  have hmab : Real.tan ((K (2 * Real.arctan a - π) + π) / 2) ≤
      Real.tan ((K (2 * Real.arctan b - π) + π) / 2) := hm.monotone hab.le
  suffices hr : (volume ((fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2)) '' F)).toReal ≤
      (1 - 1 / (2 * (C₉ + 1))) * (Real.tan ((K (2 * Real.arctan b - π) + π) / 2) -
        Real.tan ((K (2 * Real.arctan a - π) + π) / 2)) by
    have hfin : volume ((fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2)) '' F) ≠ ⊤ :=
      ne_top_of_le_ne_top (b := volume ((fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2)) ''
        Icc a b)) (by rw [hHIcc, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (measure_mono (image_mono hFs))
    rw [hHIcc, Real.volume_Icc, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal hr
  rw [hβL] at hFr
  rcases le_or_gt 0 (a + b) with hs | hs
  · have := s0c_c1_half hK hKc hper hK0 hC hδ hη hP hD hab hs hFs hFm hFr
    rwa [← hC₉] at this
  · -- reflection `K̃ = ρ ∘ K ∘ ρ`, `ρ s = -2π - s`; then `H̃ t = -H(-t)`
    have hρ : ∀ x, K (x - 2 * π) = K x - 2 * π := fun x => by
      have := hper (x - 2 * π)
      rw [sub_add_cancel] at this
      linarith
    have hK2 : K (-(2 * π)) = -(2 * π) := by
      have := hρ 0
      rw [zero_sub, hK0] at this
      linarith
    have hKt : StrictMono fun s => -(2 * π) - K (-(2 * π) - s) := fun x y hxy => by
      have := hK (show -(2 * π) - y < -(2 * π) - x by linarith)
      simp only
      linarith
    have hKtc : Continuous fun s => -(2 * π) - K (-(2 * π) - s) := by
      exact continuous_const.sub (hKc.comp (continuous_const.sub continuous_id))
    have hKtp : ∀ θ, (fun s => -(2 * π) - K (-(2 * π) - s)) (θ + 2 * π) =
        (fun s => -(2 * π) - K (-(2 * π) - s)) θ + 2 * π := fun θ => by
      simp only
      rw [show -(2 * π) - (θ + 2 * π) = (-(2 * π) - θ) - 2 * π by ring, hρ]
      ring
    have hKt0 : (fun s => -(2 * π) - K (-(2 * π) - s)) 0 = 0 := by
      simp only
      rw [sub_zero, hK2]
      ring
    have himgρ : ∀ X : Set ℝ, (fun s => -(2 * π) - K (-(2 * π) - s)) '' X =
        (fun s : ℝ => -(2 * π) - s) '' (K '' ((fun s : ℝ => -(2 * π) - s) '' X)) := fun X => by
      rw [image_image, image_image]
    have hPt : ∀ a b : ℝ, a < b → b - a ≤ 2 * π → ∀ A ⊆ Icc a b, MeasurableSet A →
        volume ((fun s => -(2 * π) - K (-(2 * π) - s)) '' A) ≤
          ENNReal.ofReal (C * ((volume A).toReal / (b - a)) ^ δ) *
            volume ((fun s => -(2 * π) - K (-(2 * π) - s)) '' Icc a b) := by
      intro a b hab hab2 A hA hAm
      have hρA : MeasurableSet ((fun s : ℝ => -(2 * π) - s) '' A) :=
        hAm.image_of_continuousOn_injOn (by fun_prop) (fun x _ y _ hxy => by simpa using hxy)
      have hKρA : MeasurableSet (K '' ((fun s : ℝ => -(2 * π) - s) '' A)) :=
        hρA.image_of_continuousOn_injOn hKc.continuousOn hK.injective.injOn
      have hρI : (fun s : ℝ => -(2 * π) - s) '' Icc a b = Icc (-(2 * π) - b) (-(2 * π) - a) :=
        image_const_sub_Icc _ _ _
      have hKρI : MeasurableSet (K '' ((fun s : ℝ => -(2 * π) - s) '' Icc a b)) :=
        (measurableSet_Icc.image_of_continuousOn_injOn (by fun_prop)
          (fun x _ y _ hxy => by simpa using hxy)).image_of_continuousOn_injOn
          hKc.continuousOn hK.injective.injOn
      rw [himgρ, himgρ, s0c_c1_vol_refl _ hKρA, s0c_c1_vol_refl _ hKρI]
      have h := hP (-(2 * π) - b) (-(2 * π) - a) (by linarith) (by linarith)
        ((fun s : ℝ => -(2 * π) - s) '' A) (hρI ▸ image_mono hA) hρA
      rw [s0c_c1_vol_refl _ hAm, show -(2 * π) - a - (-(2 * π) - b) = b - a by ring] at h
      rwa [hρI]
    have hDt : ∀ a a' b' c : ℝ, a ≤ a' → a' < b' → b' ≤ c → c - a ≤ 2 * π →
        c - a ≤ 5 * (b' - a') →
          η * ((fun s => -(2 * π) - K (-(2 * π) - s)) c -
            (fun s => -(2 * π) - K (-(2 * π) - s)) a) ≤
          (fun s => -(2 * π) - K (-(2 * π) - s)) b' -
            (fun s => -(2 * π) - K (-(2 * π) - s)) a' := by
      intro a a' b' c h1 h2 h3 h4 h5
      have := hD (-(2 * π) - c) (-(2 * π) - b') (-(2 * π) - a') (-(2 * π) - a) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith)
      simp only
      linarith
    have hid : ∀ t, Real.tan (((fun s => -(2 * π) - K (-(2 * π) - s))
        (2 * Real.arctan (-t) - π) + π) / 2) = -Real.tan ((K (2 * Real.arctan t - π) + π) / 2) := by
      intro t
      simp only
      rw [Real.arctan_neg, show -(2 * π) - (2 * -Real.arctan t - π) = 2 * Real.arctan t - π by ring,
        show (-(2 * π) - K (2 * Real.arctan t - π) + π) / 2 =
          -((K (2 * Real.arctan t - π) + π) / 2) by ring, Real.tan_neg]
    have hFt : (fun t : ℝ => 0 - t) '' F ⊆ Icc (-b) (-a) := by
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨by linarith [(hFs ht).2], by linarith [(hFs ht).1]⟩
    have hFtm : MeasurableSet ((fun t : ℝ => 0 - t) '' F) :=
      hFm.image_of_continuousOn_injOn (by fun_prop) (fun x _ y _ hxy => by simpa using hxy)
    have hFtv : (volume ((fun t : ℝ => 0 - t) '' F)).toReal ≤
        4 / (25 * π ^ 2) * (1 / (2 * (π ^ 2 * (1 + 1 / η) ^ 2 / 4) * C)) ^ δ⁻¹ / 3 *
          (-a - -b) := by
      rw [s0c_c1_vol_refl _ hFm, show -a - -b = b - a by ring]
      exact hFr
    have h := s0c_c1_half hKt hKtc hKtp hKt0 hC hδ hη hPt hDt (by linarith : -b < -a)
      (by linarith) hFt hFtm hFtv
    rw [hid, hid, ← hC₉] at h
    have hHm : MeasurableSet ((fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2)) '' F) :=
      hFm.image_of_continuousOn_injOn hc.continuousOn hm.injective.injOn
    have himg : (fun t => Real.tan (((fun s => -(2 * π) - K (-(2 * π) - s))
        (2 * Real.arctan t - π) + π) / 2)) '' ((fun t : ℝ => 0 - t) '' F) =
        (fun u : ℝ => 0 - u) '' ((fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2)) '' F) := by
      rw [image_image, image_image]
      refine image_congr fun t _ => ?_
      rw [zero_sub, hid, zero_sub]
    rw [himg, s0c_c1_vol_refl _ hHm] at h
    linarith

/-- Null sets: `|X| = 0 ↔ |H(X)| = 0` for `H = T ∘ K ∘ α`. -/
theorem s0c_c1_null {K : ℝ → ℝ} (hK : StrictMono K)
    (hper : ∀ θ, K (θ + 2 * π) = K θ + 2 * π) (hK0 : K 0 = 0)
    (hpow : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ a b : ℝ, a < b → b - a ≤ 2 * π → ∀ A ⊆ Icc a b,
      MeasurableSet A → volume (K '' A) ≤
        ENNReal.ofReal (C * ((volume A).toReal / (b - a)) ^ δ) * volume (K '' Icc a b))
    (hrev : ∀ A : Set ℝ, MeasurableSet A → volume (K '' A) = 0 → volume A = 0)
    {X : Set ℝ} (hX : MeasurableSet X) :
    volume X = 0 ↔
      volume ((fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2)) '' X) = 0 := by
  have hαd : ∀ x : ℝ, HasDerivAt (fun t : ℝ => 2 * Real.arctan t - π) (2 * (1 / (1 + x ^ 2))) x :=
    fun x => ((Real.hasDerivAt_arctan x).const_mul 2).sub_const π
  have hαD : Differentiable ℝ fun t : ℝ => 2 * Real.arctan t - π :=
    fun x => (hαd x).differentiableAt
  have hTD : DifferentiableOn ℝ (fun s : ℝ => Real.tan ((s + π) / 2)) (Ioo (-(2 * π)) 0) :=
    fun s hs => (s0c_c1_T_hasDerivAt hs).differentiableAt.differentiableWithinAt
  have hAm : MeasurableSet ((fun t : ℝ => 2 * Real.arctan t - π) '' X) :=
    hX.image_of_continuousOn_injOn hαD.continuous.continuousOn
      s0c_c1_alpha_strictMono.injective.injOn
  have hAs : (fun t : ℝ => 2 * Real.arctan t - π) '' X ⊆ Ioo (-(2 * π)) 0 := by
    rintro _ ⟨t, -, rfl⟩
    exact s0c_c1_alpha_mem t
  have hKA : K '' ((fun t : ℝ => 2 * Real.arctan t - π) '' X) ⊆ Ioo (-(2 * π)) 0 := by
    rintro _ ⟨s, hs, rfl⟩
    exact s0c_c1_Kmem hK hper hK0 (hAs hs)
  have hHX : (fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2)) '' X =
      (fun s : ℝ => Real.tan ((s + π) / 2)) ''
        (K '' ((fun t : ℝ => 2 * Real.arctan t - π) '' X)) := by
    rw [image_image, image_image]
  have hXA : X = (fun s : ℝ => Real.tan ((s + π) / 2)) ''
      ((fun t : ℝ => 2 * Real.arctan t - π) '' X) := by
    rw [image_image]
    exact ((image_congr fun t _ => s0c_c1_T_alpha t).trans (image_id' X)).symm
  have hαT : (fun t : ℝ => 2 * Real.arctan t - π) ''
      ((fun s : ℝ => Real.tan ((s + π) / 2)) ''
        (K '' ((fun t : ℝ => 2 * Real.arctan t - π) '' X))) =
        K '' ((fun t : ℝ => 2 * Real.arctan t - π) '' X) := by
    rw [image_image]
    exact (image_congr fun s hs => s0c_c1_alpha_T (hKA hs)).trans (image_id' _)
  constructor
  · intro h0
    have hA0 := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      hαD.differentiableOn h0
    have hKA0 : volume (K '' ((fun t : ℝ => 2 * Real.arctan t - π) '' X)) = 0 := by
      obtain ⟨C, δ, hC, hδ, hP⟩ := hpow
      have h := hP (-(2 * π)) 0 (by linarith [Real.pi_pos]) (by linarith) _
        (hAs.trans Ioo_subset_Icc_self) hAm
      rw [hA0, ENNReal.toReal_zero, zero_div, Real.zero_rpow hδ.ne', mul_zero,
        ENNReal.ofReal_zero, zero_mul] at h
      exact nonpos_iff_eq_zero.mp h
    rw [hHX]
    exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume (hTD.mono hKA) hKA0
  · intro h0
    rw [hHX] at h0
    have hKA0 : volume (K '' ((fun t : ℝ => 2 * Real.arctan t - π) '' X)) = 0 := by
      rw [← hαT]
      exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
        hαD.differentiableOn h0
    have hA0 := hrev _ hAm hKA0
    rw [hXA]
    exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume (hTD.mono hAs) hA0

/-- Absolute continuity and `A_∞` of a strictly increasing continuous surjection `Hf` of `ℝ`
with the null-set equivalence and the interval threshold (Stieltjes measure route). -/
theorem s0c_c1_reg_core {Hf : ℝ → ℝ} (hm : StrictMono Hf) (hc : Continuous Hf)
    (hsurj : Function.Surjective Hf)
    (hnull : ∀ X : Set ℝ, MeasurableSet X → (volume X = 0 ↔ volume (Hf '' X) = 0))
    {β θ : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hthr : ∀ a b : ℝ, a < b → ∀ F ⊆ Icc a b, MeasurableSet F →
      volume F ≤ ENNReal.ofReal (β * (b - a)) →
        volume (Hf '' F) ≤ ENNReal.ofReal θ * volume (Hf '' Icc a b)) :
    VanishingCarleson.LocallyAbsolutelyContinuous Hf ∧
      VanishingCarleson.AInfinityWeight (deriv Hf) := by
  let SH : StieltjesFunction ℝ := ⟨Hf, hm.monotone, fun x => hc.continuousWithinAt⟩
  let e : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective Hf hm hsurj
  have he : (e : ℝ → ℝ) = Hf := StrictMono.coe_orderIsoOfSurjective ..
  have himg : ∀ X : Set ℝ, Hf '' X = e.symm ⁻¹' X := fun X => by
    rw [← he]
    exact e.image_eq_preimage_symm X
  have hms : Measurable e.symm := e.symm.continuous.measurable
  have hSH : ∀ x, SH x = Hf x := fun x => rfl
  have hμ : SH.measure = Measure.map e.symm volume := by
    refine Measure.ext_of_Ioc' _ _
      (fun a b _ => by rw [SH.measure_Ioc]; exact ENNReal.ofReal_ne_top) (fun a b _ => ?_)
    rw [SH.measure_Ioc, Measure.map_apply hms measurableSet_Ioc, ← himg, ← he, e.image_Ioc,
      Real.volume_Ioc, he, hSH, hSH]
  have hval : ∀ X, MeasurableSet X → SH.measure X = volume (Hf '' X) := fun X hX => by
    rw [hμ, Measure.map_apply hms hX, himg]
  have hac : SH.measure ≪ volume := Measure.AbsolutelyContinuous.mk fun X hX h0 => by
    rw [hval X hX]
    exact (hnull X hX).mp h0
  have hwd : volume.withDensity (SH.measure.rnDeriv volume) = SH.measure :=
    Measure.withDensity_rnDeriv_eq _ _ hac
  have hint : ∀ X, MeasurableSet X →
      ∫ x in X, (SH.measure.rnDeriv volume x).toReal = (SH.measure X).toReal := by
    intro X hX
    rw [integral_toReal (Measure.measurable_rnDeriv _ _).aemeasurable
      (ae_restrict_of_ae (Measure.rnDeriv_lt_top _ _)), ← withDensity_apply _ hX, hwd]
  have hgi : ∀ X, MeasurableSet X → SH.measure X ≠ ⊤ →
      IntegrableOn (fun x => (SH.measure.rnDeriv volume x).toReal) X := by
    intro X hX hfin
    refine integrable_toReal_of_lintegral_ne_top
      (Measure.measurable_rnDeriv _ _).aemeasurable ?_
    rw [← withDensity_apply _ hX, hwd]
    exact hfin
  have hfinIoc : ∀ a b, SH.measure (Ioc a b) ≠ ⊤ := fun a b => by
    rw [SH.measure_Ioc]
    exact ENNReal.ofReal_ne_top
  have hderiv : ∀ᵐ x, deriv Hf x = (SH.measure.rnDeriv volume x).toReal :=
    SH.ae_hasDerivAt.mono fun x hx => hx.deriv
  have hIcc : ∀ a b, a ≤ b → SH.measure (Icc a b) = ENNReal.ofReal (Hf b - Hf a) := by
    intro a b _
    rw [hval _ measurableSet_Icc, ← he, e.image_Icc, Real.volume_Icc]
  refine ⟨⟨hc, fun a b hab =>
    ⟨fun x => (SH.measure.rnDeriv volume x).toReal, ?_, fun t ht => ?_⟩⟩, ?_⟩
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mpr
      (hgi _ measurableSet_Ioc (hfinIoc a b))
  · rw [intervalIntegral.integral_of_le ht.1, hint _ measurableSet_Ioc, SH.measure_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (SH.mono ht.1)), hSH, hSH]
    ring
  · obtain ⟨C, δ, hC, hδ, hcz⟩ := s07_cz_power hβ hβ1 hθ hθ1
    refine ⟨max C 1, min δ 1, le_max_right _ _, lt_min hδ one_pos, min_le_right _ _, ?_, ?_⟩
    · have hZm : MeasurableSet {x | SH.measure.rnDeriv volume x = 0} :=
        Measure.measurable_rnDeriv _ _ (measurableSet_singleton 0)
      have hZ : SH.measure {x | SH.measure.rnDeriv volume x = 0} = 0 := by
        have hw := withDensity_apply (μ := volume) (SH.measure.rnDeriv volume) hZm
        rw [hwd] at hw
        rw [hw]
        exact (setLIntegral_congr_fun hZm (g := fun _ => 0) fun x hx => hx).trans lintegral_zero
      have hZ0 : volume {x | SH.measure.rnDeriv volume x = 0} = 0 :=
        (hnull _ hZm).mpr (by rw [← hval _ hZm]; exact hZ)
      have hne : ∀ᵐ x, SH.measure.rnDeriv volume x ≠ 0 := by
        rw [ae_iff]
        simpa using hZ0
      filter_upwards [hderiv, Measure.rnDeriv_lt_top SH.measure volume, hne] with x hx hlt hne
      rw [hx]
      exact ENNReal.toReal_pos hne hlt.ne
    · intro a b hab E hEm hEs
      have key := hcz SH.measure hac (b - a) (fun a' b' hab' _ F hF hFm hFv => by
          rw [hval F hFm, hval _ measurableSet_Icc]
          exact hthr a' b' hab' F hF hFm hFv) a b hab le_rfl E hEs hEm
      have hP : 0 < Hf b - Hf a := sub_pos.mpr (hm hab)
      have hIccf : SH.measure (Icc a b) ≠ ⊤ := by
        rw [hIcc a b hab.le]; exact ENNReal.ofReal_ne_top
      rw [setIntegral_congr_ae hEm (hderiv.mono fun x hx _ => hx),
        setIntegral_congr_ae measurableSet_Icc (hderiv.mono fun x hx _ => hx),
        hint E hEm, hint _ measurableSet_Icc, hIcc a b hab.le,
        ENNReal.toReal_ofReal hP.le, div_le_iff₀ hP]
      have ht0 : 0 ≤ (volume E).toReal / (b - a) :=
        div_nonneg ENNReal.toReal_nonneg (by linarith)
      have ht1 : (volume E).toReal / (b - a) ≤ 1 := by
        rw [div_le_one (by linarith)]
        have h1 := measure_mono (μ := volume) hEs
        rw [Real.volume_Icc] at h1
        have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
        rwa [ENNReal.toReal_ofReal (by linarith)] at h2
      have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIccf) key
      rw [ENNReal.toReal_mul, hIcc a b hab.le, ENNReal.toReal_ofReal hP.le,
        ENNReal.toReal_ofReal (by positivity)] at h1
      have h2 : ((volume E).toReal / (b - a)) ^ δ ≤ ((volume E).toReal / (b - a)) ^ min δ 1 :=
        Real.rpow_le_rpow_of_exponent_ge' ht0 ht1 (le_min hδ.le zero_le_one) (min_le_left _ _)
      exact h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul (le_max_left _ _) h2
        (Real.rpow_nonneg ht0 _) (by positivity)) hP.le)

/-- C1 (W-CAY, uniform). -/
theorem s0c_cay_sqs {k : ℂ → ℂ} (hk : IsStronglyQS k) (hk1 : k 1 = 1) {H : ℝ → ℝ}
    (hH : ∀ t : ℝ, H t = (VanishingCarleson.cayleyInv (k (VanishingCarleson.cayley t))).re) :
    (∀ t : ℝ, VanishingCarleson.cayleyInv (k (VanishingCarleson.cayley t)) = H t) ∧
      (∀ ζ : Circle, ((VanishingCarleson.cayleyConj H ζ : Circle) : ℂ) = k ζ) ∧
      StrictMono H ∧ Function.Surjective H ∧ VanishingCarleson.LocallyAbsolutelyContinuous H ∧
      VanishingCarleson.AInfinityWeight (deriv H) := by
  classical
  obtain ⟨δf, hs⟩ := hk
  obtain ⟨K, hK, hKc, hper, hl, hK0⟩ := s0c_c1_lift hs.1 hk1
  have hHe : ∀ t, H t = Real.tan ((K (2 * Real.arctan t - π) + π) / 2) := fun t => by
    rw [hH, s0c_c1_H hK hper hl hK0, Complex.ofReal_re]
  have hHfun : H = fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2) := funext hHe
  obtain ⟨φ₀, hφ₀b, -, -, hφ₀v⟩ := s07_de_circleMap hs.1
  let kinv : ℂ → ℂ := fun ζ => if hζ : ζ ∈ sphere (0 : ℂ) 1 then
    ((Function.surjInv hφ₀b.surjective (⟨ζ, hζ⟩ : Circle) : Circle) : ℂ) else 0
  have hinv1 : ∀ ζ ∈ sphere (0 : ℂ) 1, kinv ζ ∈ sphere (0 : ℂ) 1 ∧ k (kinv ζ) = ζ := by
    intro ζ hζ
    simp only [kinv, hζ, ↓reduceDIte]
    refine ⟨mem_sphere_zero_iff_norm.mpr (Circle.norm_coe _), ?_⟩
    rw [← hφ₀v]
    exact congrArg Subtype.val (Function.surjInv_eq hφ₀b.surjective (⟨ζ, hζ⟩ : Circle))
  obtain ⟨δ', hs'⟩ := sqs_circle_inv k kinv ⟨δf, hs⟩ hinv1
  obtain ⟨G, hG, hGc, hGper, hGl, hKG, hGK⟩ := s07_inv_lift hK hKc hper hl hinv1
  obtain ⟨C, δ, hC, hδ, hP⟩ := s07_inv_power δ'
  have hpow : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ a b : ℝ, a < b → b - a ≤ 2 * π → ∀ A ⊆ Icc a b,
      MeasurableSet A → volume (K '' A) ≤
        ENNReal.ofReal (C * ((volume A).toReal / (b - a)) ^ δ) * volume (K '' Icc a b) :=
    ⟨C, δ, hC, hδ, fun a b hab hab2 A hA hAm =>
      hP kinv G K hs' hG hGc hGper hGl hK hGK hKG a b hab hab2 A hA hAm⟩
  have hrev : ∀ A : Set ℝ, MeasurableSet A → volume (K '' A) = 0 → volume A = 0 :=
    fun A hA h0 => s07_inv_null hs hK hKc hper hl hA h0
  obtain ⟨C₂, δ₂, hC₂, hδ₂, hP₂⟩ := s07_inv_power δf
  have hdbl : ∃ η : ℝ, 0 < η ∧ ∀ a a' b' c : ℝ, a ≤ a' → a' < b' → b' ≤ c → c - a ≤ 2 * π →
      c - a ≤ 5 * (b' - a') → η * (K c - K a) ≤ K b' - K a' :=
    ⟨_, by positivity, s0c_c1_dbl hK hG hGK hper hC₂ hδ₂ fun a b hab hab2 A hA hAm =>
      hP₂ k K G hs hK hKc hper hl hG hKG hGK a b hab hab2 A hA hAm⟩
  obtain ⟨β, θ, hβ, hβ1, hθ, hθ1, hthr⟩ := s0c_c1_thr hK hKc hper hK0 hpow hdbl
  have hm := s0c_c1_Hmono hK hper hK0
  have hsj := s0c_c1_Hsurj hK hKc hper hK0
  have hreg := s0c_c1_reg_core hm (s0c_c1_Hcont hK hKc hper hK0) hsj
    (fun X hX => s0c_c1_null hK hper hK0 hpow hrev hX) hβ hβ1 hθ hθ1 hthr
  rw [← hHfun] at hm hsj hreg
  refine ⟨fun t => by rw [s0c_c1_H hK hper hl hK0, hHe], fun ζ => ?_, hm, hsj, hreg.1, hreg.2⟩
  by_cases hζ : ζ = 1
  · subst hζ
    rw [VanishingCarleson.cayleyConj_one, Circle.coe_one, hk1]
  · rw [← VanishingCarleson.cayleyCircle_cayleyInv_re ζ hζ]
    generalize (VanishingCarleson.cayleyInv (ζ : ℂ)).re = s₀
    rw [VanishingCarleson.cayleyConj_cayleyCircle_coe, VanishingCarleson.cayleyCircle_coe, hHe,
      s0c_c1_cc (Real.tan _), s0c_c1_alpha_T (s0c_c1_Kmem hK hper hK0 (s0c_c1_alpha_mem s₀)),
      s0c_c1_cc s₀, hl]

/-! ## C1v helpers -/

/-- Mean oscillation is at most twice the mean deviation from any constant. -/
theorem s0c_v_osc_le {u : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hu : IntervalIntegrable u volume a b)
    (c : ℝ) :
    VanishingCarleson.intervalOscillation u a b ≤ 2 * ((∫ t in a..b, |u t - c|) / (b - a)) := by
  unfold VanishingCarleson.intervalOscillation VanishingCarleson.intervalAvg
  set m := (∫ t in a..b, u t) / (b - a) with hmdef
  have hba : 0 < b - a := sub_pos.mpr hab
  have hi1 : IntervalIntegrable (fun t => |u t - c|) volume a b :=
    (hu.sub intervalIntegrable_const).abs
  have hm : (b - a) * |c - m| ≤ ∫ t in a..b, |u t - c| := by
    have e : (b - a) * (c - m) = ∫ t in a..b, (c - u t) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hu,
        intervalIntegral.integral_const, smul_eq_mul, hmdef]
      field_simp
    have h1 : |∫ t in a..b, (c - u t)| ≤ ∫ t in a..b, |u t - c| :=
      (intervalIntegral.abs_integral_le_integral_abs hab.le).trans
        (le_of_eq (intervalIntegral.integral_congr fun t _ => abs_sub_comm _ _))
    rw [← e, abs_mul, abs_of_pos hba] at h1
    exact h1
  have hi : ∫ t in a..b, |u t - m| ≤ ∫ t in a..b, (|u t - c| + |c - m|) :=
    intervalIntegral.integral_mono_on hab.le (hu.sub intervalIntegrable_const).abs
      (hi1.add intervalIntegrable_const) fun t _ => by
        calc |u t - m| = |(u t - c) + (c - m)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
  rw [intervalIntegral.integral_add hi1 intervalIntegrable_const, intervalIntegral.integral_const,
    smul_eq_mul] at hi
  calc (∫ t in a..b, |u t - m|) / (b - a) ≤ (2 * ∫ t in a..b, |u t - c|) / (b - a) :=
        div_le_div_of_nonneg_right (by linarith) hba.le
    _ = _ := by ring

/-- Real form of the power bound on a subinterval. -/
theorem s0c_v_pw {K : ℝ → ℝ} (hK : StrictMono K) (hKc : Continuous K) {C δ : ℝ} (hC : 0 < C)
    (hP : ∀ a b : ℝ, a < b → b - a ≤ 2 * π → ∀ A ⊆ Icc a b, MeasurableSet A →
      volume (K '' A) ≤
        ENNReal.ofReal (C * ((volume A).toReal / (b - a)) ^ δ) * volume (K '' Icc a b))
    {a b p q : ℝ} (hab : a < b) (hl : b - a ≤ 2 * π) (hap : a ≤ p) (hpq : p ≤ q) (hqb : q ≤ b) :
    K q - K p ≤ C * ((q - p) / (b - a)) ^ δ * (K b - K a) := by
  have h := hP a b hab hl (Icc p q) (Icc_subset_Icc hap hqb) measurableSet_Icc
  have hi : ∀ x y : ℝ, x ≤ y → K '' Icc x y = Icc (K x) (K y) := fun x y hxy =>
    s0c_c1_imgIcc hxy (hK.monotone.monotoneOn _) hKc.continuousOn
  have hr : 0 ≤ ((q - p) / (b - a)) ^ δ :=
    Real.rpow_nonneg (div_nonneg (by linarith) (by linarith)) _
  have hKab : 0 ≤ K b - K a := sub_nonneg.mpr (hK.monotone hab.le)
  rw [hi p q hpq, hi a b hab.le, Real.volume_Icc, Real.volume_Icc, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith), ← ENNReal.ofReal_mul (by positivity)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) hKab)).mp h

/-- Relative continuity of a normalized lift with the power bound. -/
theorem s0c_v_rel {K : ℝ → ℝ} (hK : StrictMono K) (hKc : Continuous K)
    (hper : ∀ θ, K (θ + 2 * π) = K θ + 2 * π) (hK0 : K 0 = 0) {C δ : ℝ} (hC : 0 < C)
    (hδ : 0 < δ)
    (hP : ∀ a b : ℝ, a < b → b - a ≤ 2 * π → ∀ A ⊆ Icc a b, MeasurableSet A →
      volume (K '' A) ≤
        ENNReal.ofReal (C * ((volume A).toReal / (b - a)) ^ δ) * volume (K '' Icc a b))
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hCρ : C * ρ ^ δ ≤ 1 / 2)
    {s s' : ℝ} (hs : s ∈ Ioo (-(2 * π)) 0) (hs' : s' ∈ Ioo (-(2 * π)) 0)
    (hss : |s' - s| ≤ ρ * min (-s) (s + 2 * π)) :
    |K s' - K s| ≤ 2 * (C * ρ ^ δ) * min (-K s) (K s + 2 * π) := by
  have h2 : K (-(2 * π)) = -(2 * π) := by
    have := hper (-(2 * π))
    rw [show -(2 * π) + 2 * π = 0 by ring, hK0] at this
    linarith
  have hpi := Real.pi_pos
  set c := C * ρ ^ δ with hc
  have hc0 : 0 ≤ c := by positivity
  have hr : ∀ x y : ℝ, 0 ≤ x → 0 < y → x ≤ ρ * y → C * (x / y) ^ δ ≤ c := fun x y hx hy hxy =>
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (div_nonneg hx hy.le)
      ((div_le_iff₀ hy).mpr hxy) hδ.le) hC.le
  have hm1 := min_le_left (-s) (s + 2 * π)
  have hm2 := min_le_right (-s) (s + 2 * π)
  have hmρ1 : ρ * min (-s) (s + 2 * π) ≤ ρ * (-s) := mul_le_mul_of_nonneg_left hm1 hρ0
  have hmρ2 : ρ * min (-s) (s + 2 * π) ≤ ρ * (s + 2 * π) := mul_le_mul_of_nonneg_left hm2 hρ0
  have hKs := s0c_c1_Kmem hK hper hK0 hs
  have hKs' := s0c_c1_Kmem hK hper hK0 hs'
  rcases le_total s s' with hle | hle
  · have hd := abs_of_nonneg (sub_nonneg.mpr hle)
    rw [hd] at hss
    have hKd : 0 ≤ K s' - K s := sub_nonneg.mpr (hK.monotone hle)
    rw [abs_of_nonneg hKd]
    -- I₁ = [s, 0]
    have e1 := s0c_v_pw hK hKc hC hP (a := s) (b := 0) (p := s) (q := s') hs.2
      (by linarith [hs.1]) le_rfl hle hs'.2.le
    have r1 := hr (s' - s) (0 - s) (by linarith) (by linarith [hs.2])
      (hss.trans (hmρ1.trans (le_of_eq (by ring))))
    have hK0s : 0 ≤ K 0 - K s := by rw [hK0]; linarith [hKs.2]
    have b1 : K s' - K s ≤ c * (-K s) := by
      have := e1.trans (mul_le_mul_of_nonneg_right r1 hK0s)
      rw [hK0, zero_sub] at this; exact this
    -- I₂ = [-2π, s']
    have e2 := s0c_v_pw hK hKc hC hP (a := -(2 * π)) (b := s') (p := s) (q := s') hs'.1
      (by linarith [hs'.2]) hs.1.le hle le_rfl
    have r2 := hr (s' - s) (s' - -(2 * π)) (by linarith) (by linarith [hs'.1])
      (hss.trans (hmρ2.trans (mul_le_mul_of_nonneg_left (by linarith) hρ0)))
    have hK2 : 0 ≤ K s' - K (-(2 * π)) := by rw [h2]; linarith [hKs'.1]
    have b2 : K s' - K s ≤ c * (K s' + 2 * π) := by
      have := e2.trans (mul_le_mul_of_nonneg_right r2 hK2)
      rw [h2] at this; linarith
    rw [mul_min_of_nonneg _ _ (by positivity)]
    refine le_min ?_ ?_
    · nlinarith
    · nlinarith
  · have hd : |s' - s| = s - s' := by rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.mpr hle)
    rw [hd] at hss
    have hKd : K s' - K s ≤ 0 := sub_nonpos.mpr (hK.monotone hle)
    rw [abs_of_nonpos hKd]
    -- I₁ = [s', 0]
    have e1 := s0c_v_pw hK hKc hC hP (a := s') (b := 0) (p := s') (q := s) hs'.2
      (by linarith [hs'.1]) le_rfl hle hs.2.le
    have r1 := hr (s - s') (0 - s') (by linarith) (by linarith [hs'.2])
      (hss.trans (hmρ1.trans (mul_le_mul_of_nonneg_left (by linarith) hρ0)))
    have hK0s : 0 ≤ K 0 - K s' := by rw [hK0]; linarith [hKs'.2]
    have b1 : K s - K s' ≤ c * (-K s') := by
      have := e1.trans (mul_le_mul_of_nonneg_right r1 hK0s)
      rw [hK0, zero_sub] at this; exact this
    -- I₂ = [-2π, s]
    have e2 := s0c_v_pw hK hKc hC hP (a := -(2 * π)) (b := s) (p := s') (q := s) hs.1
      (by linarith [hs.2]) hs'.1.le hle le_rfl
    have r2 := hr (s - s') (s - -(2 * π)) (by linarith) (by linarith [hs.1])
      (hss.trans (hmρ2.trans (le_of_eq (by ring))))
    have hK2 : 0 ≤ K s - K (-(2 * π)) := by rw [h2]; linarith [hKs.1]
    have b2 : K s - K s' ≤ c * (K s + 2 * π) := by
      have := e2.trans (mul_le_mul_of_nonneg_right r2 hK2)
      rw [h2] at this; linarith
    rw [mul_min_of_nonneg _ _ (by positivity)]
    refine le_min ?_ ?_
    · nlinarith
    · nlinarith

/-- `log ∘ sin` is relatively Lipschitz on `(0, π)`. -/
theorem s0c_v_logsin {w w' η : ℝ} (hw : w ∈ Ioo 0 π) (hw' : w' ∈ Ioo 0 π) (hη : 0 ≤ η)
    (hη1 : π * η ≤ 1) (h : |w' - w| ≤ η * min w (π - w)) :
    |Real.log (Real.sin w') - Real.log (Real.sin w)| ≤ π * η := by
  have hpi := Real.pi_pos
  have hs : 0 < Real.sin w := Real.sin_pos_of_pos_of_lt_pi hw.1 hw.2
  have hs' : 0 < Real.sin w' := Real.sin_pos_of_pos_of_lt_pi hw'.1 hw'.2
  have hlb := s0c_c1_sin_lb hw.1.le hw.2.le
  have hmin : min w (π - w) ≤ π / 2 * Real.sin w := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    have := (div_mul_eq_mul_div 2 π (min w (π - w))) ▸ hlb
    rw [div_le_iff₀ hpi] at this
    linarith
  have hd : |Real.sin w' - Real.sin w| ≤ π * η / 2 * Real.sin w := by
    refine (Real.abs_sin_sub_sin_le _ _).trans (h.trans ?_)
    calc η * min w (π - w) ≤ η * (π / 2 * Real.sin w) := mul_le_mul_of_nonneg_left hmin hη
      _ = _ := by ring
  set x := Real.sin w' / Real.sin w with hx
  have hx0 : 0 < x := div_pos hs' hs
  have hx1 : |x - 1| ≤ π * η / 2 := by
    rw [hx, show Real.sin w' / Real.sin w - 1 = (Real.sin w' - Real.sin w) / Real.sin w by
      field_simp, abs_div, abs_of_pos hs, div_le_iff₀ hs]
    exact hd
  rw [← Real.log_div hs'.ne' hs.ne', ← hx]
  have hxa := abs_le.mp hx1
  have hxh : 1 / 2 ≤ x := by linarith
  rw [abs_le]
  constructor
  · have h1 := Real.one_sub_inv_le_log_of_pos hx0
    have h2 : 1 - x⁻¹ = (x - 1) / x := by field_simp
    have h3 : -(π * η) ≤ (x - 1) / x := by
      rw [le_div_iff₀ hx0]
      nlinarith
    linarith
  · have := Real.log_le_sub_one_of_pos hx0
    linarith

/-- Local Lipschitz bound for `log (1 + t²)`. -/
theorem s0c_v_log1p_one {x y : ℝ} (h : |y - x| ≤ 1) :
    Real.log (1 + y ^ 2) - Real.log (1 + x ^ 2) ≤ 2 * |y - x| := by
  have hx : 0 < 1 + x ^ 2 := by positivity
  have hy : 0 < 1 + y ^ 2 := by positivity
  rw [← Real.log_div hy.ne' hx.ne']
  refine (Real.log_le_sub_one_of_pos (div_pos hy hx)).trans ?_
  rw [div_sub_one hx.ne', div_le_iff₀ hx]
  have e : 1 + y ^ 2 - (1 + x ^ 2) = (y - x) * (y + x) := by ring
  rw [e]
  have h1 : (y - x) * (y + x) ≤ |y - x| * |y + x| := by rw [← abs_mul]; exact le_abs_self _
  have h2 : |y + x| ≤ 2 * |x| + 1 := by
    calc |y + x| = |(y - x) + 2 * x| := by ring_nf
      _ ≤ |y - x| + |2 * x| := abs_add_le _ _
      _ ≤ 1 + 2 * |x| := by rw [abs_mul, abs_two]; linarith
      _ = _ := by ring
  have h3 : 2 * |x| ≤ 1 + x ^ 2 := by
    have := sq_nonneg (|x| - 1)
    rw [sub_sq, sq_abs] at this
    linarith
  have h4 : |y + x| ≤ 2 * (1 + x ^ 2) := by linarith [sq_nonneg x]
  calc (y - x) * (y + x) ≤ |y - x| * |y + x| := h1
    _ ≤ |y - x| * (2 * (1 + x ^ 2)) := mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
    _ = _ := by ring

theorem s0c_v_log1p {x y : ℝ} (h : |y - x| ≤ 1) :
    |Real.log (1 + y ^ 2) - Real.log (1 + x ^ 2)| ≤ 2 * |y - x| := by
  rw [abs_le]
  have h' : |x - y| ≤ 1 := by rwa [abs_sub_comm]
  have := s0c_v_log1p_one h'
  rw [abs_sub_comm x y] at this
  exact ⟨by linarith, s0c_v_log1p_one h⟩

/-- `α t = 2 arctan t - π`: local increment bound. -/
theorem s0c_v_alpha_d {t t' : ℝ} (h : |t' - t| ≤ 1) :
    |(2 * Real.arctan t' - π) - (2 * Real.arctan t - π)| ≤ 4 * |t' - t| / (1 + t ^ 2) := by
  have h1 : |t * (t' - t)| ≤ |t| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h
  have h3 : 2 * |t| ≤ 1 + t ^ 2 := by
    have := sq_nonneg (|t| - 1)
    rw [sub_sq, sq_abs] at this
    linarith
  have hd : (1 + t ^ 2) / 2 ≤ 1 + t' * t := by
    have e : t' * t = t ^ 2 + t * (t' - t) := by ring
    rw [e]
    linarith [neg_abs_le (t * (t' - t))]
  have hpos : 0 < (1 + t ^ 2) / 2 := by positivity
  have ha := Real.arctan_add (x := t') (y := -t) (by nlinarith)
  rw [Real.arctan_neg] at ha
  have e : (2 * Real.arctan t' - π) - (2 * Real.arctan t - π) =
      2 * (Real.arctan t' + -Real.arctan t) := by ring
  rw [e, ha, abs_mul, abs_two]
  have hq : (t' + -t) / (1 - t' * -t) = (t' - t) / (1 + t' * t) := by ring_nf
  rw [hq]
  refine (mul_le_mul_of_nonneg_left Real.abs_arctan_le_abs (by norm_num)).trans ?_
  rw [abs_div, abs_of_pos (by linarith : 0 < 1 + t' * t)]
  calc 2 * (|t' - t| / (1 + t' * t)) ≤ 2 * (|t' - t| / ((1 + t ^ 2) / 2)) := by
        gcongr
    _ = _ := by field_simp; ring

/-- The distance of `α t` to `{-2π, 0}` is at least `2/(1+t²)`. -/
theorem s0c_v_alpha_m (t : ℝ) :
    2 / (1 + t ^ 2) ≤ min (-(2 * Real.arctan t - π)) (2 * Real.arctan t - π + 2 * π) := by
  have hpi := Real.pi_pos
  have ha1 := Real.neg_pi_div_two_lt_arctan t
  have ha2 := Real.arctan_lt_pi_div_two t
  have hub := s0c_c1_sin_ub (y := π / 2 - Real.arctan t) (by linarith) (by linarith)
  rw [Real.sin_pi_div_two_sub, Real.cos_arctan] at hub
  have hq : 0 < 1 + t ^ 2 := by positivity
  have hsq : √(1 + t ^ 2) ≤ 1 + t ^ 2 := (Real.sqrt_le_left hq.le).mpr (by nlinarith)
  have hsp : 0 < √(1 + t ^ 2) := Real.sqrt_pos.mpr hq
  have h1 : 1 / (1 + t ^ 2) ≤ 1 / √(1 + t ^ 2) := one_div_le_one_div_of_le hsp hsq
  have e : min (-(2 * Real.arctan t - π)) (2 * Real.arctan t - π + 2 * π) =
      2 * min (π / 2 - Real.arctan t) (π - (π / 2 - Real.arctan t)) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
    congr 1 <;> ring
  rw [e, div_eq_mul_one_div 2]
  linarith

/-- A.e. derivative of `H = T ∘ K ∘ α` for an absolutely continuous lift `K` with density `u`. -/
theorem s0c_v_deriv {K u : ℝ → ℝ} (hK : StrictMono K) (hper : ∀ θ, K (θ + 2 * π) = K θ + 2 * π)
    (hK0 : K 0 = 0) (hui : ∀ a b : ℝ, IntegrableOn u (Icc a b))
    (hKu : ∀ θ : ℝ, K θ = K 0 + ∫ t in (0 : ℝ)..θ, u t) (hpos : ∀ᵐ t, 0 < u t) :
    ∀ᵐ t, 0 < deriv (fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2)) t ∧
      Real.log (deriv (fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2)) t) =
        (-2 * Real.log (Real.sin (-K (2 * Real.arctan t - π) / 2)) - Real.log (1 + t ^ 2)) +
          Real.log (u (2 * Real.arctan t - π)) := by
  have hloc : MeasureTheory.LocallyIntegrable u volume := fun x =>
    ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), hui _ _⟩
  have hgood : ∀ᵐ x, HasDerivAt K (u x) x ∧ 0 < u x := by
    filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hloc, hpos] with x hx hx0
    exact ⟨((hx 0).const_add (K 0)).congr_of_eventuallyEq (Eventually.of_forall hKu), hx0⟩
  have hN0 : volume {x | ¬ (HasDerivAt K (u x) x ∧ 0 < u x)} = 0 := ae_iff.mp hgood
  have hTD : DifferentiableOn ℝ (fun s : ℝ => Real.tan ((s + π) / 2)) (Ioo (-(2 * π)) 0) :=
    fun s hs => (s0c_c1_T_hasDerivAt hs).differentiableAt.differentiableWithinAt
  have hsub : {t : ℝ | ¬ (HasDerivAt K (u (2 * Real.arctan t - π)) (2 * Real.arctan t - π) ∧
      0 < u (2 * Real.arctan t - π))} ⊆ (fun s : ℝ => Real.tan ((s + π) / 2)) ''
        ({x | ¬ (HasDerivAt K (u x) x ∧ 0 < u x)} ∩ Ioo (-(2 * π)) 0) := fun t ht =>
    ⟨2 * Real.arctan t - π, ⟨ht, s0c_c1_alpha_mem t⟩, s0c_c1_T_alpha t⟩
  have hT0 := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (hTD.mono inter_subset_right) (measure_mono_null inter_subset_left hN0)
  have hg : ∀ᵐ t, HasDerivAt K (u (2 * Real.arctan t - π)) (2 * Real.arctan t - π) ∧
      0 < u (2 * Real.arctan t - π) := ae_iff.mpr (measure_mono_null hsub hT0)
  filter_upwards [hg] with t ht
  obtain ⟨hKd, hu0⟩ := ht
  have hαd : HasDerivAt (fun t : ℝ => 2 * Real.arctan t - π) (2 * (1 / (1 + t ^ 2))) t :=
    ((Real.hasDerivAt_arctan t).const_mul 2).sub_const π
  have hKx := s0c_c1_Kmem hK hper hK0 (s0c_c1_alpha_mem t)
  have hd := (s0c_c1_T_hasDerivAt hKx).comp t (hKd.comp t hαd)
  have hcos : Real.cos ((K (2 * Real.arctan t - π) + π) / 2) =
      Real.sin (-K (2 * Real.arctan t - π) / 2) := by
    rw [show (K (2 * Real.arctan t - π) + π) / 2 = K (2 * Real.arctan t - π) / 2 + π / 2 by ring,
      Real.cos_add_pi_div_two, neg_div, Real.sin_neg]
  have hS : 0 < Real.sin (-K (2 * Real.arctan t - π) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hKx.2]) (by linarith [hKx.1])
  have hq : 0 < 1 + t ^ 2 := by positivity
  have heq : deriv (fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2)) t =
      u (2 * Real.arctan t - π) /
        (Real.sin (-K (2 * Real.arctan t - π) / 2) ^ 2 * (1 + t ^ 2)) := by
    rw [show (fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2)) =
      (fun s : ℝ => Real.tan ((s + π) / 2)) ∘ K ∘ (fun t : ℝ => 2 * Real.arctan t - π) from rfl,
      hd.deriv, hcos]
    field_simp
  rw [heq]
  refine ⟨by positivity, ?_⟩
  rw [Real.log_div hu0.ne' (by positivity), Real.log_mul (by positivity) hq.ne', Real.log_pow]
  push_cast
  ring

/-- Change of variables along `α t = 2 arctan t - π`. -/
theorem s0c_v_alpha_int {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntegrableOn f (Icc (2 * Real.arctan a - π) (2 * Real.arctan b - π))) :
    IntegrableOn (fun t => f (2 * Real.arctan t - π)) (Icc a b) ∧
      IntegrableOn (fun t => 2 / (1 + t ^ 2) * f (2 * Real.arctan t - π)) (Icc a b) ∧
      ∫ x in Icc (2 * Real.arctan a - π) (2 * Real.arctan b - π), f x =
        ∫ t in Icc a b, 2 / (1 + t ^ 2) * f (2 * Real.arctan t - π) := by
  have hαd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => 2 * Real.arctan t - π) (2 / (1 + t ^ 2)) t :=
    fun t => by
      have := ((Real.hasDerivAt_arctan t).const_mul 2).sub_const π
      convert this using 1
      ring
  have hαc : Continuous fun t : ℝ => 2 * Real.arctan t - π := by fun_prop
  have himg : (fun t : ℝ => 2 * Real.arctan t - π) '' Icc a b =
      Icc (2 * Real.arctan a - π) (2 * Real.arctan b - π) :=
    s0c_c1_imgIcc hab (s0c_c1_alpha_strictMono.monotone.monotoneOn _) hαc.continuousOn
  have hd' : ∀ x ∈ Icc a b, HasDerivWithinAt (fun t : ℝ => 2 * Real.arctan t - π)
      (2 / (1 + x ^ 2)) (Icc a b) x := fun x _ => (hαd x).hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => 2 * Real.arctan t - π) (Icc a b) :=
    s0c_c1_alpha_strictMono.injective.injOn
  have habs : ∀ t : ℝ, |2 / (1 + t ^ 2)| = 2 / (1 + t ^ 2) := fun t => abs_of_pos (by positivity)
  have hI := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc hd' hinj f).mp
    (himg ▸ hf)
  simp only [habs, smul_eq_mul] at hI
  have hE := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hd' hinj f
  simp only [habs, smul_eq_mul] at hE
  rw [himg] at hE
  refine ⟨?_, hI, hE⟩
  have hc : ContinuousOn (fun t : ℝ => (1 + t ^ 2) / 2) (Icc a b) := by fun_prop
  refine (hI.continuousOn_mul hc isCompact_Icc).congr_fun (fun t _ => ?_) measurableSet_Icc
  have : (0 : ℝ) < 1 + t ^ 2 := by positivity
  field_simp

/-- Mean of `f ∘ α` on a short interval, by the mean of `f` on the image. -/
theorem s0c_v_Best {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hb1 : b - a ≤ 1) (hf0 : ∀ x, 0 ≤ f x)
    (hf : IntegrableOn f (Icc (2 * Real.arctan a - π) (2 * Real.arctan b - π))) :
    ∫ t in a..b, f (2 * Real.arctan t - π) ≤
      6 * (b - a) * ((∫ x in (2 * Real.arctan a - π)..(2 * Real.arctan b - π), f x) /
        ((2 * Real.arctan b - π) - (2 * Real.arctan a - π))) := by
  have hαab : 2 * Real.arctan a - π < 2 * Real.arctan b - π := s0c_c1_alpha_strictMono hab
  obtain ⟨hI, hIw, hE⟩ := s0c_v_alpha_int hab.le hf
  rw [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hαab.le, ← integral_Icc_eq_integral_Ioc, hE]
  have hL : 0 < 2 / (1 + a ^ 2) := by positivity
  have hpt : ∀ t ∈ Icc a b, f (2 * Real.arctan t - π) ≤
      3 / (2 / (1 + a ^ 2)) * (2 / (1 + t ^ 2) * f (2 * Real.arctan t - π)) := by
    intro t ht
    have hq : (0 : ℝ) < 1 + t ^ 2 := by positivity
    have e : 3 / (2 / (1 + a ^ 2)) * (2 / (1 + t ^ 2)) = 3 * (1 + a ^ 2) / (1 + t ^ 2) := by
      field_simp
    rw [← mul_assoc, e]
    have h1 : (t - a) ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have h2 : t ^ 2 ≤ 2 * a ^ 2 + 2 * (t - a) ^ 2 := by nlinarith [sq_nonneg (t - 2 * a)]
    exact le_mul_of_one_le_left (hf0 _) ((one_le_div hq).mpr (by nlinarith))
  have hmono := setIntegral_mono_on hI (hIw.const_mul (3 / (2 / (1 + a ^ 2)))) measurableSet_Icc
    hpt
  rw [integral_const_mul] at hmono
  have hJ : 0 ≤ ∫ t in Icc a b, 2 / (1 + t ^ 2) * f (2 * Real.arctan t - π) :=
    setIntegral_nonneg measurableSet_Icc (fun t _ => mul_nonneg (by positivity) (hf0 _))
  have hD := s0c_v_alpha_d (t := a) (t' := b) (by rw [abs_of_nonneg (by linarith)]; exact hb1)
  rw [abs_of_pos (by linarith), abs_of_pos (by linarith)] at hD
  have hD0 : 0 < (2 * Real.arctan b - π) - (2 * Real.arctan a - π) := by linarith
  have hk : 3 / (2 / (1 + a ^ 2)) ≤
      6 * (b - a) / ((2 * Real.arctan b - π) - (2 * Real.arctan a - π)) := by
    rw [div_le_div_iff₀ hL hD0]
    have e : 4 * (b - a) / (1 + a ^ 2) = 2 * (b - a) * (2 / (1 + a ^ 2)) := by ring
    rw [e] at hD
    linarith
  refine hmono.trans ?_
  calc 3 / (2 / (1 + a ^ 2)) * (∫ t in Icc a b, 2 / (1 + t ^ 2) * f (2 * Real.arctan t - π))
      ≤ 6 * (b - a) / ((2 * Real.arctan b - π) - (2 * Real.arctan a - π)) *
          (∫ t in Icc a b, 2 / (1 + t ^ 2) * f (2 * Real.arctan t - π)) :=
        mul_le_mul_of_nonneg_right hk hJ
    _ = _ := by ring

/-- Pointwise oscillation of the smooth part `P` of `log H'`. -/
theorem s0c_v_Pest {K : ℝ → ℝ} (hK : StrictMono K) (hKc : Continuous K)
    (hper : ∀ θ, K (θ + 2 * π) = K θ + 2 * π) (hK0 : K 0 = 0) {C δ : ℝ} (hC : 0 < C)
    (hδ : 0 < δ)
    (hP : ∀ a b : ℝ, a < b → b - a ≤ 2 * π → ∀ A ⊆ Icc a b, MeasurableSet A →
      volume (K '' A) ≤
        ENNReal.ofReal (C * ((volume A).toReal / (b - a)) ^ δ) * volume (K '' Icc a b))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) (hc : 2 * π * (C * (2 * r) ^ δ) ≤ 1)
    {t t' : ℝ} (htt : |t' - t| ≤ r) :
    |(-2 * Real.log (Real.sin (-K (2 * Real.arctan t' - π) / 2)) - Real.log (1 + t' ^ 2)) -
        (-2 * Real.log (Real.sin (-K (2 * Real.arctan t - π) / 2)) - Real.log (1 + t ^ 2))| ≤
      4 * π * (C * (2 * r) ^ δ) + 2 * r := by
  have hpi := Real.pi_gt_three
  have hc0 : 0 ≤ C * (2 * r) ^ δ := by positivity
  have h1' : |t' - t| ≤ 1 := htt.trans (by linarith)
  have hαd := s0c_v_alpha_d h1'
  have hm := s0c_v_alpha_m t
  have hq : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have h1 : |(2 * Real.arctan t' - π) - (2 * Real.arctan t - π)| ≤
      (2 * r) * min (-(2 * Real.arctan t - π)) (2 * Real.arctan t - π + 2 * π) := by
    refine hαd.trans ?_
    calc 4 * |t' - t| / (1 + t ^ 2) ≤ 4 * r / (1 + t ^ 2) := by gcongr
      _ = 2 * r * (2 / (1 + t ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (by linarith)
  have hCρ : C * (2 * r) ^ δ ≤ 1 / 2 := by nlinarith
  have hrel := s0c_v_rel hK hKc hper hK0 hC hδ hP (by linarith) hCρ (s0c_c1_alpha_mem t)
    (s0c_c1_alpha_mem t') h1
  have hKs := s0c_c1_Kmem hK hper hK0 (s0c_c1_alpha_mem t)
  have hKs' := s0c_c1_Kmem hK hper hK0 (s0c_c1_alpha_mem t')
  have h2 : |(-K (2 * Real.arctan t' - π) / 2) - (-K (2 * Real.arctan t - π) / 2)| ≤
      (2 * (C * (2 * r) ^ δ)) * min (-K (2 * Real.arctan t - π) / 2)
        (π - (-K (2 * Real.arctan t - π) / 2)) := by
    rw [show (-K (2 * Real.arctan t' - π) / 2) - (-K (2 * Real.arctan t - π) / 2) =
      -(K (2 * Real.arctan t' - π) - K (2 * Real.arctan t - π)) / 2 by ring, abs_div, abs_neg,
      abs_two, div_le_iff₀ two_pos]
    refine hrel.trans (le_of_eq ?_)
    rw [mul_min_of_nonneg _ _ (by positivity), mul_min_of_nonneg _ _ (by positivity),
      min_mul_of_nonneg _ _ two_pos.le]
    congr 1 <;> ring
  have hls := s0c_v_logsin (w := -K (2 * Real.arctan t - π) / 2)
    (w' := -K (2 * Real.arctan t' - π) / 2) ⟨by linarith [hKs.2], by linarith [hKs.1]⟩
    ⟨by linarith [hKs'.2], by linarith [hKs'.1]⟩ (by positivity) (by linarith) h2
  have hl1 := s0c_v_log1p h1'
  rw [abs_le] at hls hl1 ⊢
  constructor <;> nlinarith

/-- `(A2)` forces `log w ∈ BMO`. Copied verbatim (up to name qualification) from VC's
`ps_bmo_log_of_A2` (VanishingCarleson/ProofSteps.lean), which is `private` upstream. -/
theorem s0c_v_bmo_log_A2 (h : ℝ → ℝ) (hh : StrictMono h)
    (hw : ∀ᵐ t ∂volume, 0 < deriv h t)
    (hα : ∀ u v : ℝ, u < v →
      IntervalIntegrable (fun t => Real.log (deriv h t)) volume u v)
    (A₀ : ℝ) (hA2 : VanishingCarleson.WeightA2 (deriv h) A₀) :
    VanishingCarleson.BMO (fun t => Real.log (deriv h t)) := by
  refine ⟨2 * A₀, fun c d hcd => ?_⟩
  set u : ℝ → ℝ := fun t => Real.log (deriv h t) with hu
  set m : ℝ := VanishingCarleson.intervalAvg u c d with hm
  have hdc : 0 < d - c := sub_pos.mpr hcd
  have hui : IntervalIntegrable u volume c d := hα c d hcd
  have hwi : IntervalIntegrable (deriv h) volume c d :=
    (hh.monotone.monotoneOn _).intervalIntegrable_deriv
  have humi : IntervalIntegrable (fun t => u t - m) volume c d := hui.sub intervalIntegrable_const
  have hint_um : ∫ t in c..d, (u t - m) = 0 := by
    rw [intervalIntegral.integral_sub hui intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, hm, VanishingCarleson.intervalAvg]
    field_simp
    ring
  have hexp_ae : ∀ᵐ t ∂volume, Real.exp (-m) * deriv h t = Real.exp (u t - m) := by
    filter_upwards [hw] with t ht
    rw [hu, sub_eq_add_neg, Real.exp_add, Real.exp_log ht, mul_comm]
  have hexp_int : IntervalIntegrable (fun t => Real.exp (u t - m)) volume c d :=
    (hwi.const_mul (Real.exp (-m))).congr_ae (ae_restrict_of_ae hexp_ae)
  have hexp_eq : ∫ t in c..d, Real.exp (u t - m) =
      Real.exp (-m) * ∫ t in c..d, deriv h t := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr_ae (hexp_ae.mono fun t ht _ => ht.symm)
  have hwint : ∫ t in c..d, deriv h t =
      VanishingCarleson.weightMean (deriv h) c d * (d - c) := by
    unfold VanishingCarleson.weightMean VanishingCarleson.intervalAvg
    field_simp
  have hA2' : VanishingCarleson.weightMean (deriv h) c d ≤ A₀ * Real.exp m := hA2 c d hcd
  have hexp_le : ∫ t in c..d, Real.exp (u t - m) ≤ A₀ * (d - c) := by
    rw [hexp_eq, hwint]
    calc Real.exp (-m) * (VanishingCarleson.weightMean (deriv h) c d * (d - c))
        ≤ Real.exp (-m) * (A₀ * Real.exp m * (d - c)) := by gcongr
      _ = A₀ * (d - c) * (Real.exp (-m) * Real.exp m) := by ring
      _ = A₀ * (d - c) := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hpt : ∀ t, |u t - m| ≤ 2 * Real.exp (u t - m) - (u t - m) := by
    intro t
    have h1 := Real.add_one_le_exp (u t - m)
    have h2 := Real.exp_pos (u t - m)
    rcases le_total 0 (u t - m) with h0 | h0
    · rw [abs_of_nonneg h0]
      linarith
    · rw [abs_of_nonpos h0]
      linarith
  have hmono : ∫ t in c..d, |u t - m| ≤ ∫ t in c..d, (2 * Real.exp (u t - m) - (u t - m)) :=
    intervalIntegral.integral_mono_on hcd.le humi.abs ((hexp_int.const_mul 2).sub humi)
      (fun t _ => hpt t)
  rw [intervalIntegral.integral_sub (hexp_int.const_mul 2) humi,
    intervalIntegral.integral_const_mul, hint_um] at hmono
  show (∫ t in c..d, |u t - m|) / (d - c) ≤ 2 * A₀
  rw [div_le_iff₀ hdc]
  linarith

/-- C1v (W-CAY, vanishing): for a strongly symmetric circle map `k` with `k 1 = 1`, the real
conjugate `H t = Re γ⁻¹(k(γ t))` is strongly symmetric on `ℝ` in VC's sense; `γ⁻¹(k(γ t))` is
real, and the VC Cayley conjugate of `H` is `k` on `∂𝔻`. -/
theorem s0c_cay_ss {k : ℂ → ℂ} (hk : IsStronglySymmetric k) (hk1 : k 1 = 1) {H : ℝ → ℝ}
    (hH : ∀ t : ℝ, H t = (VanishingCarleson.cayleyInv (k (VanishingCarleson.cayley t))).re) :
    (∀ t : ℝ, VanishingCarleson.cayleyInv (k (VanishingCarleson.cayley t)) = H t) ∧
      (∀ ζ : Circle, ((VanishingCarleson.cayleyConj H ζ : Circle) : ℂ) = k ζ) ∧
      VanishingCarleson.StronglySymmetric H := by
  classical
  have hch : IsCircleHomeo k := by
    obtain ⟨K, u, h1, h2, h3, h4, -⟩ := hk
    exact ⟨K, h1, h2, h3, h4⟩
  obtain ⟨K, hK, hKc, hper, hl, hK0⟩ := s0c_c1_lift hch hk1
  obtain ⟨-, hpow, hdbl, hrev⟩ := s07b_ssa_pow hk hKc hl
  obtain ⟨u, -, -, hui, hKu, hupos, hlui, hvmo⟩ := s07b_ssa_lift_data hk hKc hl
  have hHe : ∀ t, H t = Real.tan ((K (2 * Real.arctan t - π) + π) / 2) := fun t => by
    rw [hH, s0c_c1_H hK hper hl hK0, Complex.ofReal_re]
  have hHfun : H = fun t => Real.tan ((K (2 * Real.arctan t - π) + π) / 2) := funext hHe
  obtain ⟨β, θ, hβ, hβ1, hθ, hθ1, hthr⟩ := s0c_c1_thr hK hKc hper hK0 hpow hdbl
  have hm := s0c_c1_Hmono hK hper hK0
  have hsj := s0c_c1_Hsurj hK hKc hper hK0
  have hreg := s0c_c1_reg_core hm (s0c_c1_Hcont hK hKc hper hK0) hsj
    (fun X hX => s0c_c1_null hK hper hK0 hpow hrev hX) hβ hβ1 hθ hθ1 hthr
  have hae := s0c_v_deriv hK hper hK0 hui hKu hupos
  rw [← hHfun] at hm hsj hreg hae
  have hPc : Continuous fun t : ℝ =>
      -2 * Real.log (Real.sin (-K (2 * Real.arctan t - π) / 2)) - Real.log (1 + t ^ 2) := by
    have hs : Continuous fun t : ℝ => Real.sin (-K (2 * Real.arctan t - π) / 2) := by
      have : Continuous fun t : ℝ => 2 * Real.arctan t - π := by fun_prop
      exact Real.continuous_sin.comp ((hKc.comp this).neg.div_const 2)
    refine (continuous_const.mul (hs.log fun t => ?_)).sub
      ((continuous_const.add (continuous_pow 2)).log fun t => (by positivity : (0 : ℝ) < 1 + t ^ 2).ne')
    have hKx := s0c_c1_Kmem hK hper hK0 (s0c_c1_alpha_mem t)
    exact (Real.sin_pos_of_pos_of_lt_pi (by linarith [hKx.2]) (by linarith [hKx.1])).ne'
  have hBi : ∀ a b : ℝ, a ≤ b →
      IntervalIntegrable (fun t => Real.log (u (2 * Real.arctan t - π))) volume a b :=
    fun a b hab => (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (s0c_v_alpha_int hab (hlui _ _)).1
  have hLi : ∀ a b : ℝ, IntervalIntegrable (fun t => Real.log (deriv H t)) volume a b := by
    have h1 : ∀ a b : ℝ, a ≤ b →
        IntervalIntegrable (fun t => Real.log (deriv H t)) volume a b := fun a b hab =>
      ((hPc.intervalIntegrable a b).add (hBi a b hab)).congr_ae
        (ae_restrict_of_ae (hae.mono fun t ht => ht.2.symm))
    intro a b
    rcases le_total a b with h | h
    · exact h1 a b h
    · exact (h1 b a h).symm
  refine ⟨fun t => by rw [s0c_c1_H hK hper hl hK0, hHe], fun ζ => ?_,
    hm, hsj, hreg.1, hreg.2, ?_, ?_⟩
  · by_cases hζ : ζ = 1
    · subst hζ
      rw [VanishingCarleson.cayleyConj_one, Circle.coe_one, hk1]
    · rw [← VanishingCarleson.cayleyCircle_cayleyInv_re ζ hζ]
      generalize (VanishingCarleson.cayleyInv (ζ : ℂ)).re = s₀
      rw [VanishingCarleson.cayleyConj_cayleyCircle_coe, VanishingCarleson.cayleyCircle_coe, hHe,
        s0c_c1_cc (Real.tan _), s0c_c1_alpha_T (s0c_c1_Kmem hK hper hK0 (s0c_c1_alpha_mem s₀)),
        s0c_c1_cc s₀, hl]
  · obtain ⟨A₀, -, hA2⟩ := VanishingCarleson.a1_imp_a2 (deriv H) hreg.2
    exact s0c_v_bmo_log_A2 H hm (hae.mono fun t ht => ht.1) (fun a b _ => hLi a b) A₀ hA2
  · intro ε hε
    obtain ⟨C, δ, hC, hδ, hP⟩ := hpow
    obtain ⟨δ₂, hδ₂, hV⟩ := hvmo (ε / 24) (by positivity)
    have hpi := Real.pi_gt_three
    obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = min (1 / (2 * π)) (ε / (32 * π)) := ⟨_, rfl⟩
    have hc₀p : 0 < c₀ := by rw [hc₀]; exact lt_min (by positivity) (by positivity)
    obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℝ, ρ₀ = (c₀ / C) ^ δ⁻¹ := ⟨_, rfl⟩
    have hρ₀p : 0 < ρ₀ := by rw [hρ₀]; exact Real.rpow_pos_of_pos (div_pos hc₀p hC) _
    have hCρ₀ : C * ρ₀ ^ δ = c₀ := by
      rw [hρ₀, Real.rpow_inv_rpow (div_pos hc₀p hC).le hδ.ne']
      field_simp
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min (min (1 / 2) (ε / 16)) (min (δ₂ / 4) (ρ₀ / 2)) :=
      ⟨_, rfl⟩
    have hr0 : 0 < r := by
      rw [hr]
      exact lt_min (lt_min (by norm_num) (by positivity)) (lt_min (by positivity) (by positivity))
    have hr1 : r ≤ 1 / 2 := hr ▸ (min_le_left _ _).trans (min_le_left _ _)
    have hrε : r ≤ ε / 16 := hr ▸ (min_le_left _ _).trans (min_le_right _ _)
    have hrδ : r ≤ δ₂ / 4 := hr ▸ (min_le_right _ _).trans (min_le_left _ _)
    have hrρ : r ≤ ρ₀ / 2 := hr ▸ (min_le_right _ _).trans (min_le_right _ _)
    have hcle : C * (2 * r) ^ δ ≤ c₀ := hCρ₀ ▸
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) (by linarith) hδ.le) hC.le
    have hc1 : 2 * π * (C * (2 * r) ^ δ) ≤ 1 := by
      have := hcle.trans (hc₀ ▸ min_le_left _ _)
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    have hc2 : 4 * π * (C * (2 * r) ^ δ) ≤ ε / 8 := by
      have := hcle.trans (hc₀ ▸ min_le_right _ _)
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    refine ⟨r, hr0, csSup_le ⟨_, 0, r, hr0, by linarith, rfl⟩ ?_⟩
    rintro _ ⟨a, b, hab, hbr, rfl⟩
    have hba : 0 < b - a := by linarith
    have hαab : 2 * Real.arctan a - π < 2 * Real.arctan b - π := s0c_c1_alpha_strictMono hab
    obtain ⟨cB, hcB⟩ : ∃ cB : ℝ, cB = (∫ x in (2 * Real.arctan a - π)..(2 * Real.arctan b - π),
        Real.log (u x)) / ((2 * Real.arctan b - π) - (2 * Real.arctan a - π)) := ⟨_, rfl⟩
    obtain ⟨Pa, hPa⟩ : ∃ Pa : ℝ, Pa = -2 * Real.log (Real.sin (-K (2 * Real.arctan a - π) / 2)) -
        Real.log (1 + a ^ 2) := ⟨_, rfl⟩
    -- the `B` part
    have hD := s0c_v_alpha_d (t := a) (t' := b) (by rw [abs_of_nonneg (by linarith)]; linarith)
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)] at hD
    have hD4 : (2 * Real.arctan b - π) - (2 * Real.arctan a - π) ≤ δ₂ := by
      have : 4 * (b - a) / (1 + a ^ 2) ≤ 4 * (b - a) :=
        div_le_self (by linarith) (by nlinarith [sq_nonneg a])
      linarith
    have hVab := hV _ _ hαab hD4
    rw [← hcB] at hVab
    have hfi : IntegrableOn (fun x => |Real.log (u x) - cB|)
        (Icc (2 * Real.arctan a - π) (2 * Real.arctan b - π)) :=
      ((hlui _ _).sub (integrableOn_const (by simp))).abs
    have hBest := s0c_v_Best hab (by linarith) (fun x => abs_nonneg (Real.log (u x) - cB)) hfi
    have hBb : ∫ t in a..b, |Real.log (u (2 * Real.arctan t - π)) - cB| ≤ (b - a) * (ε / 4) := by
      refine hBest.trans ?_
      have := mul_le_mul_of_nonneg_left hVab (by linarith : (0 : ℝ) ≤ 6 * (b - a))
      linarith
    -- the `P` part
    have hX := (hPc.intervalIntegrable a b).sub (intervalIntegrable_const (μ := volume) (c := Pa))
    have hY := (hBi a b hab.le).sub (intervalIntegrable_const (μ := volume) (c := cB))
    have hPb : ∫ t in a..b, |(-2 * Real.log (Real.sin (-K (2 * Real.arctan t - π) / 2)) -
        Real.log (1 + t ^ 2)) - Pa| ≤ (b - a) * (ε / 4) := by
      have h := intervalIntegral.integral_mono_on hab.le hX.abs
        (intervalIntegrable_const (μ := volume) (c := ε / 4)) (fun t ht => by
          have := s0c_v_Pest hK hKc hper hK0 hC hδ hP hr0.le hr1 hc1
            (t := a) (t' := t) (by rw [abs_of_nonneg (by linarith [ht.1])]; linarith [ht.2])
          rw [← hPa] at this
          linarith)
      rwa [intervalIntegral.integral_const, smul_eq_mul] at h
    -- assembly
    refine (s0c_v_osc_le hab (hLi a b) (Pa + cB)).trans ?_
    have hcongr : ∫ t in a..b, |Real.log (deriv H t) - (Pa + cB)| =
        ∫ t in a..b, |((-2 * Real.log (Real.sin (-K (2 * Real.arctan t - π) / 2)) -
          Real.log (1 + t ^ 2)) - Pa) + (Real.log (u (2 * Real.arctan t - π)) - cB)| := by
      refine intervalIntegral.integral_congr_ae (hae.mono fun t ht _ => ?_)
      rw [ht.2]
      ring_nf
    have hsplit : ∫ t in a..b, |((-2 * Real.log (Real.sin (-K (2 * Real.arctan t - π) / 2)) -
          Real.log (1 + t ^ 2)) - Pa) + (Real.log (u (2 * Real.arctan t - π)) - cB)| ≤
        (∫ t in a..b, |(-2 * Real.log (Real.sin (-K (2 * Real.arctan t - π) / 2)) -
          Real.log (1 + t ^ 2)) - Pa|) +
        ∫ t in a..b, |Real.log (u (2 * Real.arctan t - π)) - cB| := by
      rw [← intervalIntegral.integral_add hX.abs hY.abs]
      exact intervalIntegral.integral_mono_on hab.le (hX.add hY).abs (hX.abs.add hY.abs)
        (fun t _ => abs_add_le _ _)
    rw [hcongr]
    have hfin : (∫ t in a..b, |((-2 * Real.log (Real.sin (-K (2 * Real.arctan t - π) / 2)) -
          Real.log (1 + t ^ 2)) - Pa) + (Real.log (u (2 * Real.arctan t - π)) - cB)|) / (b - a) ≤
        ε / 2 := by
      rw [div_le_iff₀ hba]
      linarith
    linarith


open VanishingCarleson in
/-- `β_h ≥ 0` everywhere: it is an infimum of non-negative reals (and `sInf ∅ = 0`). -/
theorem s0c_thC_betaPt_nonneg (h : ℝ → ℝ) (x y : ℝ) : 0 ≤ betaPt h x y := by
  unfold betaPt beta
  exact Real.sInf_nonneg fun _ ⟨_, _, hr, _⟩ => hr

open VanishingCarleson in
/-- `β_h(x, y) ≤ 1` for `y > 0` (Lemma (Crude Beta Bound)). -/
theorem s0c_thC_betaPt_le_one (h : ℝ → ℝ) (hh : StrictMono h) (x y : ℝ) (hy : 0 < y) :
    betaPt h x y ≤ 1 :=
  crude_beta_bound h hh (x - y) (x + y) (by linarith)

open VanishingCarleson in
/-- Joint measurability of `β_h`, via a piecewise combination of the continuity off the
`y = 0` line (`continuous_betaPt`) and the vanishing of `β_h` on `y ≤ 0`
(degenerate/reversed intervals). -/
theorem s0c_thC_betaPt_measurable (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h) :
    Measurable fun p : ℝ × ℝ => betaPt h p.1 p.2 := by
  classical
  have hzeroEq : ∀ a : ℝ, beta h a a = 0 := by
    intro a
    have hset_eq : { r : ℝ | ∃ κ τ : ℝ, 0 ≤ r ∧
        r = ((a - a) * (h a - h a))⁻¹ * ∫ t in a..a, |h t - (κ * t + τ)| } = {0} := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, sub_self, inv_zero,
        intervalIntegral.integral_same, mul_zero]
      constructor
      · rintro ⟨κ, τ, _, hr⟩; exact hr
      · rintro rfl; exact ⟨0, 0, le_refl 0, rfl⟩
    unfold beta
    rw [hset_eq, csInf_singleton]
  have hzeroGt : ∀ a b : ℝ, b < a → beta h a b = 0 := by
    intro a b hba
    have hset_sub : { r : ℝ | ∃ κ τ : ℝ, 0 ≤ r ∧
        r = ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (κ * t + τ)| } ⊆ {0} := by
      rintro r ⟨κ, τ, hr0, hreq⟩
      have hprod_pos : (0 : ℝ) < (b - a) * (h b - h a) :=
        mul_pos_of_neg_of_neg (by linarith) (sub_neg.mpr (hh hba))
      have hint_le : (∫ t in a..b, |h t - (κ * t + τ)|) ≤ 0 := by
        have hsym : ∫ t in a..b, |h t - (κ * t + τ)| = -∫ t in b..a, |h t - (κ * t + τ)| :=
          intervalIntegral.integral_symm _ _
        have hnn : (0 : ℝ) ≤ ∫ t in b..a, |h t - (κ * t + τ)| :=
          intervalIntegral.integral_nonneg hba.le (fun _ _ => abs_nonneg _)
        linarith [hsym, hnn]
      have hrle : r ≤ 0 := by
        rw [hreq]
        exact mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hprod_pos).le hint_le
      exact Set.mem_singleton_iff.mpr (le_antisymm hrle hr0)
    unfold beta
    by_cases hS : { r : ℝ | ∃ κ τ : ℝ, 0 ≤ r ∧
        r = ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (κ * t + τ)| }.Nonempty
    · obtain ⟨r₀, hr₀⟩ := hS
      have hr₀0 : r₀ = 0 := Set.mem_singleton_iff.mp (hset_sub hr₀)
      have hSeq : { r : ℝ | ∃ κ τ : ℝ, 0 ≤ r ∧
          r = ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (κ * t + τ)| } = {0} :=
        Set.Subset.antisymm hset_sub (Set.singleton_subset_iff.mpr (hr₀0 ▸ hr₀))
      rw [hSeq, csInf_singleton]
    · rw [Set.not_nonempty_iff_eq_empty] at hS
      rw [hS, Real.sInf_empty]
  have hzero : ∀ p : ℝ × ℝ, p.2 ≤ 0 → betaPt h p.1 p.2 = 0 := by
    intro p hp
    rcases hp.lt_or_eq with hlt | heq
    · exact hzeroGt (p.1 - p.2) (p.1 + p.2) (by linarith)
    · show beta h (p.1 - p.2) (p.1 + p.2) = 0
      rw [heq]
      simp only [sub_zero, add_zero]
      exact hzeroEq p.1
  have hs : MeasurableSet {p : ℝ × ℝ | 0 < p.2} := measurableSet_lt measurable_const measurable_snd
  have hf : ContinuousOn (fun p : ℝ × ℝ => betaPt h p.1 p.2) {p : ℝ × ℝ | 0 < p.2} :=
    (continuous_betaPt h hh hc).mono (fun p hp => ne_of_gt hp)
  have hg : ContinuousOn (fun _ : ℝ × ℝ => (0:ℝ)) {p : ℝ × ℝ | 0 < p.2}ᶜ := continuousOn_const
  have hpm := hf.measurable_piecewise hg hs
  have heq : Set.piecewise {p : ℝ × ℝ | 0 < p.2} (fun p : ℝ × ℝ => betaPt h p.1 p.2)
      (fun _ : ℝ × ℝ => (0:ℝ)) = fun p : ℝ × ℝ => betaPt h p.1 p.2 := by
    funext p
    by_cases hp : 0 < p.2
    · simp [Set.piecewise, hp]
    · have hp' : p ∉ {p : ℝ × ℝ | 0 < p.2} := hp
      rw [Set.piecewise_eq_of_notMem _ _ _ hp']
      exact (hzero p (not_lt.mp hp)).symm
  rwa [heq] at hpm


open VanishingCarleson in
/-- Measurability of the dilated beta-number `(x, y) ↦ β_h(x, c y)`. -/
theorem s0c_thC_betaPt_dil_measurable (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (c : ℝ) : Measurable fun p : ℝ × ℝ => betaPt h p.1 (c * p.2) :=
  (s0c_thC_betaPt_measurable h hh hc).comp (f := fun p : ℝ × ℝ => (p.1, c * p.2))
    (measurable_fst.prodMk (measurable_snd.const_mul c))

open VanishingCarleson in
/-- Measurability of the slice `Y ↦ β_h(x, Y)`. -/
theorem s0c_thC_betaPt_slice_measurable (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (x : ℝ) : Measurable (betaPt h x) :=
  (s0c_thC_betaPt_measurable h hh hc).comp (f := fun Y : ℝ => (x, Y))
    (measurable_const.prodMk measurable_id)

open VanishingCarleson in
/-- Tonelli decomposition of the box `lintegral` into an iterated `lintegral`. -/
theorem s0c_thC_box_eq_iter (F : ℝ → ℝ → ℝ)
    (hFm : Measurable fun p : ℝ × ℝ => F p.1 p.2) (a b : ℝ) :
    carlesonBoxLIntegral F a b =
      ∫⁻ x in Set.Ioc a b, ∫⁻ y in Set.Ioc (0:ℝ) (b - a), ENNReal.ofReal ((F x y) ^ 2 / y) := by
  have hg : Measurable fun p : ℝ × ℝ => ENNReal.ofReal ((F p.1 p.2) ^ 2 / p.2) :=
    ((hFm.pow_const 2).div measurable_snd).ennreal_ofReal
  unfold carlesonBoxLIntegral carlesonBox
  rw [Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict,
    MeasureTheory.lintegral_prod _ hg.aemeasurable]

open VanishingCarleson in
/-- **The `dy/y = dY/Y` scale invariance**: for `k > 0`, substituting `Y = k y`
in `∫ G(ky)²/y dy` over `(0, L]` gives `∫ G(Y)²/Y dY` over `(0, kL]`. -/
theorem s0c_thC_y_scale (k : ℝ) (hk : 0 < k) (L : ℝ) (G : ℝ → ℝ)
    (hG : Measurable G) :
    ∫⁻ y in Set.Ioc (0:ℝ) L, ENNReal.ofReal (G (k * y) ^ 2 / y) =
      ∫⁻ Y in Set.Ioc (0:ℝ) (k * L), ENNReal.ofReal (G Y ^ 2 / Y) := by
  have hk0 : k ≠ 0 := hk.ne'
  set f : ℝ → ENNReal := fun Y => ENNReal.ofReal (G Y ^ 2 / Y) with hfdef
  have hfmeas : Measurable f := (hG.pow_const 2).div measurable_id |>.ennreal_ofReal
  have hpt : ∀ y : ℝ, ENNReal.ofReal (G (k * y) ^ 2 / y) = ENNReal.ofReal k * f (k * y) := by
    intro y
    rcases eq_or_ne y 0 with hy0 | hy0
    · simp [hy0, hfdef]
    · show ENNReal.ofReal (G (k * y) ^ 2 / y) =
        ENNReal.ofReal k * ENNReal.ofReal (G (k * y) ^ 2 / (k * y))
      rw [← ENNReal.ofReal_mul hk.le]
      congr 1
      field_simp
  have step1 : (∫⁻ y in Set.Ioc (0:ℝ) L, ENNReal.ofReal (G (k * y) ^ 2 / y)) =
      ∫⁻ y in Set.Ioc (0:ℝ) L, ENNReal.ofReal k * f (k * y) := by
    congr 1
    exact funext hpt
  rw [step1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hpre : (fun y : ℝ => k * y) ⁻¹' (Set.Ioc (0:ℝ) (k * L)) = Set.Ioc (0:ℝ) L := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, by nlinarith⟩
      by_contra hy
      push Not at hy
      have hle : k * y ≤ k * 0 := mul_le_mul_of_nonneg_left hy hk.le
      simp at hle
      linarith
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
  have hmap : Measure.map (fun y : ℝ => k * y) volume = ENNReal.ofReal k⁻¹ • volume := by
    rw [Real.map_volume_mul_left hk0, abs_of_pos (inv_pos.mpr hk)]
  have hkey := setLIntegral_map (μ := volume) (f := f) (g := fun y : ℝ => k * y)
      (measurableSet_Ioc (a := (0:ℝ)) (b := k * L)) hfmeas (measurable_const_mul k)
  rw [hmap, hpre] at hkey
  rw [← hkey]
  have hsmul : (∫⁻ Y in Set.Ioc (0:ℝ) (k * L), f Y ∂(ENNReal.ofReal k⁻¹ • volume)) =
      ENNReal.ofReal k⁻¹ * ∫⁻ Y in Set.Ioc (0:ℝ) (k * L), f Y := by
    rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
  rw [hsmul, ← mul_assoc, ← ENNReal.ofReal_mul hk.le, mul_inv_cancel₀ hk0, ENNReal.ofReal_one,
    one_mul]

open VanishingCarleson in
/-- **Head bound (eq. `head-new`)**: after the change of variables `Y = 2^k y`, the region
`{x ∈ J, 0 < Y ≤ 2^k |J|}` lies in the Carleson box of the interval `J_k` concentric with
`J = [a, b]` of length `2^k |J|`. -/
theorem s0c_thC_head (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h) (a b : ℝ)
    (hab : a < b) (k : ℕ) :
    carlesonBoxLIntegral (fun x y => betaPt h x (2 ^ k * y)) a b ≤
      carlesonBoxLIntegral (betaPt h) ((a + b) / 2 - 2 ^ k * (b - a) / 2)
        ((a + b) / 2 + 2 ^ k * (b - a) / 2) := by
  have hβm := s0c_thC_betaPt_measurable h hh hc
  have hk : (0:ℝ) < 2 ^ k := by positivity
  have hk1 : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hL : b - a ≤ 2 ^ k * (b - a) := by
    have := mul_le_mul_of_nonneg_right hk1 (sub_pos.mpr hab).le
    linarith
  have hm : Measurable fun p : ℝ × ℝ => betaPt h p.1 (2 ^ k * p.2) :=
    s0c_thC_betaPt_dil_measurable h hh hc (2 ^ k)
  have hinner : ∀ x : ℝ,
      ∫⁻ y in Set.Ioc (0:ℝ) (b - a), ENNReal.ofReal (betaPt h x (2 ^ k * y) ^ 2 / y) =
        ∫⁻ Y in Set.Ioc (0:ℝ) (2 ^ k * (b - a)), ENNReal.ofReal (betaPt h x Y ^ 2 / Y) :=
    fun x => s0c_thC_y_scale (2 ^ k) hk (b - a) (betaPt h x)
      (s0c_thC_betaPt_slice_measurable h hh hc x)
  have hlen : (a + b) / 2 + 2 ^ k * (b - a) / 2 - ((a + b) / 2 - 2 ^ k * (b - a) / 2) =
      2 ^ k * (b - a) := by ring
  have e1 := s0c_thC_box_eq_iter (fun x y => betaPt h x (2 ^ k * y)) hm a b
  have e2 := s0c_thC_box_eq_iter (betaPt h) hβm ((a + b) / 2 - 2 ^ k * (b - a) / 2)
    ((a + b) / 2 + 2 ^ k * (b - a) / 2)
  have hsub : Set.Ioc a b ⊆
      Set.Ioc ((a + b) / 2 - 2 ^ k * (b - a) / 2) ((a + b) / 2 + 2 ^ k * (b - a) / 2) :=
    Set.Ioc_subset_Ioc (by linarith) (by linarith)
  rw [e1, e2, hlen, lintegral_congr hinner]
  exact lintegral_mono_set hsub

open VanishingCarleson in
/-- **Weighted Cauchy–Schwarz** for the scale average: if `0 ≤ c_k ≤ 1`, then
`(∑ 4^{-k} c_k)² ≤ (∑ 4^{-k}) (∑ 4^{-k} c_k²) = (4/3) ∑ 4^{-k} c_k²`. -/
theorem s0c_thC_sq_tsum_le (c : ℕ → ℝ) (hc0 : ∀ k, 0 ≤ c k) (hc1 : ∀ k, c k ≤ 1) :
    (∑' k : ℕ, (1 / 4 : ℝ) ^ k * c k) ^ 2 ≤ 4 / 3 * ∑' k : ℕ, (1 / 4 : ℝ) ^ k * c k ^ 2 := by
  have hw : Summable fun k : ℕ => (1 / 4 : ℝ) ^ k :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hwsum : ∑' k : ℕ, (1 / 4 : ℝ) ^ k = 4 / 3 := by
    rw [tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 4) (by norm_num)]
    norm_num
  have hf : Summable fun k : ℕ => (1 / 4 : ℝ) ^ k * c k :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (by positivity) (hc0 k))
      (fun k => mul_le_of_le_one_right (by positivity) (hc1 k)) hw
  have hg0 : ∀ k : ℕ, 0 ≤ (1 / 4 : ℝ) ^ k * c k ^ 2 :=
    fun k => mul_nonneg (by positivity) (sq_nonneg _)
  have hg : Summable fun k : ℕ => (1 / 4 : ℝ) ^ k * c k ^ 2 :=
    Summable.of_nonneg_of_le hg0
      (fun k => mul_le_of_le_one_right (by positivity) (pow_le_one₀ (hc0 k) (hc1 k))) hw
  refine le_of_tendsto' (hf.hasSum.tendsto_sum_nat.pow 2) fun n => ?_
  have hcs : (∑ k ∈ Finset.range n, (1 / 4 : ℝ) ^ k * c k) ^ 2 ≤
      (∑ k ∈ Finset.range n, (1 / 4 : ℝ) ^ k) *
        ∑ k ∈ Finset.range n, (1 / 4 : ℝ) ^ k * c k ^ 2 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun k _ => by positivity)
      (fun k _ => hg0 k) (fun k _ => le_of_eq (by ring))
  have h1 : ∑ k ∈ Finset.range n, (1 / 4 : ℝ) ^ k ≤ 4 / 3 :=
    calc ∑ k ∈ Finset.range n, (1 / 4 : ℝ) ^ k ≤ ∑' k : ℕ, (1 / 4 : ℝ) ^ k :=
          hw.sum_le_tsum _ fun k _ => by positivity
      _ = 4 / 3 := hwsum
  have h2 : ∑ k ∈ Finset.range n, (1 / 4 : ℝ) ^ k * c k ^ 2 ≤
      ∑' k : ℕ, (1 / 4 : ℝ) ^ k * c k ^ 2 :=
    hg.sum_le_tsum _ fun k _ => hg0 k
  exact hcs.trans (mul_le_mul h1 h2 (Finset.sum_nonneg fun k _ => hg0 k) (by norm_num))

open VanishingCarleson in
/-- Pointwise form of the weighted Cauchy–Schwarz bound, for the integrand of the box
integral: `Θ_h² / y ≤ ∑ (4/3) 4^{-k} β_h(x, 2^k y)² / y` (trivially for `y ≤ 0`). -/
theorem s0c_thC_pointwise (h : ℝ → ℝ) (hh : StrictMono h) (p : ℝ × ℝ) :
    ENNReal.ofReal (Theta h p.1 p.2 ^ 2 / p.2) ≤
      ∑' k : ℕ, ENNReal.ofReal (4 / 3 * (1 / 4 : ℝ) ^ k) *
        ENNReal.ofReal (betaPt h p.1 (2 ^ k * p.2) ^ 2 / p.2) := by
  rcases le_or_gt p.2 0 with hy | hy
  · rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hy)]
    exact bot_le
  set c : ℕ → ℝ := fun k => betaPt h p.1 (2 ^ k * p.2) with hcdef
  have hc0 : ∀ k, 0 ≤ c k := fun k => s0c_thC_betaPt_nonneg h _ _
  have hc1 : ∀ k, c k ≤ 1 := fun k => s0c_thC_betaPt_le_one h hh _ _ (mul_pos (by positivity) hy)
  have hTheta : Theta h p.1 p.2 = ∑' k : ℕ, (1 / 4 : ℝ) ^ k * c k := rfl
  have hterm0 : ∀ k : ℕ, 0 ≤ 4 / 3 * (1 / 4 : ℝ) ^ k * (c k ^ 2 / p.2) :=
    fun k => mul_nonneg (by positivity) (div_nonneg (sq_nonneg _) hy.le)
  have hsumm : Summable fun k : ℕ => 4 / 3 * (1 / 4 : ℝ) ^ k * (c k ^ 2 / p.2) := by
    refine Summable.of_nonneg_of_le hterm0 (fun k => ?_)
      ((summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 4) (by norm_num)).mul_left
        (4 / 3 / p.2))
    have hck : c k ^ 2 ≤ 1 := pow_le_one₀ (hc0 k) (hc1 k)
    have hq : 0 ≤ 4 / 3 / p.2 * (1 / 4 : ℝ) ^ k :=
      mul_nonneg (div_nonneg (by norm_num) hy.le) (by positivity)
    calc 4 / 3 * (1 / 4 : ℝ) ^ k * (c k ^ 2 / p.2) = 4 / 3 / p.2 * (1 / 4 : ℝ) ^ k * c k ^ 2 := by
          ring
      _ ≤ 4 / 3 / p.2 * (1 / 4 : ℝ) ^ k * 1 := mul_le_mul_of_nonneg_left hck hq
      _ = 4 / 3 / p.2 * (1 / 4 : ℝ) ^ k := mul_one _
  have heq : 4 / 3 * (∑' k : ℕ, (1 / 4 : ℝ) ^ k * c k ^ 2) / p.2 =
      ∑' k : ℕ, 4 / 3 * (1 / 4 : ℝ) ^ k * (c k ^ 2 / p.2) := by
    rw [show 4 / 3 * (∑' k : ℕ, (1 / 4 : ℝ) ^ k * c k ^ 2) / p.2 =
        4 / 3 / p.2 * ∑' k : ℕ, (1 / 4 : ℝ) ^ k * c k ^ 2 by ring, ← tsum_mul_left]
    exact tsum_congr fun k => by ring
  calc ENNReal.ofReal (Theta h p.1 p.2 ^ 2 / p.2)
      ≤ ENNReal.ofReal (∑' k : ℕ, 4 / 3 * (1 / 4 : ℝ) ^ k * (c k ^ 2 / p.2)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← heq, hTheta]
        exact div_le_div_of_nonneg_right (s0c_thC_sq_tsum_le c hc0 hc1) hy.le
    _ = ∑' k : ℕ, ENNReal.ofReal (4 / 3 * (1 / 4 : ℝ) ^ k * (c k ^ 2 / p.2)) :=
        ENNReal.ofReal_tsum_of_nonneg hterm0 hsumm
    _ = ∑' k : ℕ, ENNReal.ofReal (4 / 3 * (1 / 4 : ℝ) ^ k) *
          ENNReal.ofReal (betaPt h p.1 (2 ^ k * p.2) ^ 2 / p.2) := by
        refine tsum_congr fun k => ?_
        rw [ENNReal.ofReal_mul (by positivity)]

open VanishingCarleson in
/-- **Minkowski-type reduction** at the `ℝ≥0∞` level: if the box integrals of the dilated
beta-numbers `β_h(·, 2^k ·)` over `Q_J` are bounded by `u_k`, then
`∬_{Q_J} Θ_h² dxdy/y ≤ (4/3) ∑ 4^{-k} u_k`. -/
theorem s0c_thC_box_le (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h) (a b : ℝ)
    (u : ℕ → ℝ) (hu0 : ∀ k, 0 ≤ u k) (hus : Summable fun k => (1 / 4 : ℝ) ^ k * u k)
    (hu : ∀ k : ℕ, carlesonBoxLIntegral (fun x y => betaPt h x (2 ^ k * y)) a b ≤
      ENNReal.ofReal (u k)) :
    carlesonBoxLIntegral (Theta h) a b ≤
      ENNReal.ofReal (4 / 3 * ∑' k : ℕ, (1 / 4 : ℝ) ^ k * u k) := by
  have hmk : ∀ k : ℕ, Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (betaPt h p.1 (2 ^ k * p.2) ^ 2 / p.2) := fun k =>
    (((s0c_thC_betaPt_dil_measurable h hh hc (2 ^ k)).pow_const 2).div
      measurable_snd).ennreal_ofReal
  have hcu0 : ∀ k : ℕ, 0 ≤ 4 / 3 * (1 / 4 : ℝ) ^ k * u k :=
    fun k => mul_nonneg (by positivity) (hu0 k)
  have hcus : Summable fun k : ℕ => 4 / 3 * (1 / 4 : ℝ) ^ k * u k :=
    (hus.mul_left (4 / 3)).congr fun k => by ring
  calc carlesonBoxLIntegral (Theta h) a b
      ≤ ∫⁻ p in carlesonBox a b, ∑' k : ℕ, ENNReal.ofReal (4 / 3 * (1 / 4 : ℝ) ^ k) *
          ENNReal.ofReal (betaPt h p.1 (2 ^ k * p.2) ^ 2 / p.2) :=
        lintegral_mono fun p => s0c_thC_pointwise h hh p
    _ = ∑' k : ℕ, ∫⁻ p in carlesonBox a b, ENNReal.ofReal (4 / 3 * (1 / 4 : ℝ) ^ k) *
          ENNReal.ofReal (betaPt h p.1 (2 ^ k * p.2) ^ 2 / p.2) :=
        lintegral_tsum fun k => ((hmk k).const_mul _).aemeasurable
    _ = ∑' k : ℕ, ENNReal.ofReal (4 / 3 * (1 / 4 : ℝ) ^ k) *
          carlesonBoxLIntegral (fun x y => betaPt h x (2 ^ k * y)) a b := by
        refine tsum_congr fun k => ?_
        rw [lintegral_const_mul _ (hmk k)]
        rfl
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (4 / 3 * (1 / 4 : ℝ) ^ k) * ENNReal.ofReal (u k) :=
        tsum_le_tsum fun k => mul_le_mul_right (hu k) _
    _ = ∑' k : ℕ, ENNReal.ofReal (4 / 3 * (1 / 4 : ℝ) ^ k * u k) :=
        tsum_congr fun k => (ENNReal.ofReal_mul (by positivity)).symm
    _ = ENNReal.ofReal (∑' k : ℕ, 4 / 3 * (1 / 4 : ℝ) ^ k * u k) :=
        (ENNReal.ofReal_tsum_of_nonneg hcu0 hcus).symm
    _ = ENNReal.ofReal (4 / 3 * ∑' k : ℕ, (1 / 4 : ℝ) ^ k * u k) := by
        rw [← tsum_mul_left]
        exact congrArg ENNReal.ofReal (tsum_congr fun k => by ring)

/-- C2 (uniform Θ helper): `Θ_h² dxdy/y` is a Carleson measure on `𝕌` for `h' ∈ A_∞(ℝ)`
(no VMO hypothesis). -/
theorem s0c_theta_uniform (h : ℝ → ℝ) (hh : StrictMono h)
    (hac : VanishingCarleson.LocallyAbsolutelyContinuous h) (hsurj : Function.Surjective h)
    (hw : VanishingCarleson.AInfinityWeight (deriv h)) :
    VanishingCarleson.IsCarlesonFn (VanishingCarleson.Theta h) := by
  have hc : Continuous h := hac.1
  obtain ⟨Cβ, hCβ0, hCβ⟩ := VanishingCarleson.beta_carleson_uniform h hh hac hsurj hw
  have h12 : ∀ k : ℕ, (1 / 2 : ℝ) ^ k = (1 / 4) ^ k * 2 ^ k := fun k => by
    rw [← mul_pow]; norm_num
  have hlen : ∀ (a b : ℝ) (k : ℕ),
      (a + b) / 2 + 2 ^ k * (b - a) / 2 - ((a + b) / 2 - 2 ^ k * (b - a) / 2) =
        2 ^ k * (b - a) := fun a b k => by ring
  have hhead : ∀ a b : ℝ, a < b → ∀ k : ℕ,
      VanishingCarleson.carlesonBoxLIntegral
          (fun x y => VanishingCarleson.betaPt h x (2 ^ k * y)) a b ≤
        ENNReal.ofReal (Cβ * (2 ^ k * (b - a))) := by
    intro a b hab k
    have hpos : (0 : ℝ) < 2 ^ k * (b - a) := mul_pos (by positivity) (sub_pos.mpr hab)
    have hJk := hCβ ((a + b) / 2 - 2 ^ k * (b - a) / 2) ((a + b) / 2 + 2 ^ k * (b - a) / 2)
      (by linarith)
    rw [hlen] at hJk
    exact (s0c_thC_head h hh hc a b hab k).trans hJk
  refine ⟨8 / 3 * Cβ, mul_nonneg (by norm_num) hCβ0, fun a b hab => ?_⟩
  have hL : 0 < b - a := sub_pos.mpr hab
  have hgeom : ∀ k : ℕ, (1 / 4 : ℝ) ^ k * (Cβ * (2 ^ k * (b - a))) =
      Cβ * (b - a) * (1 / 2) ^ k := fun k => by rw [h12]; ring
  have hsum : Summable fun k : ℕ => (1 / 4 : ℝ) ^ k * (Cβ * (2 ^ k * (b - a))) :=
    (summable_geometric_two.mul_left (Cβ * (b - a))).congr fun k => (hgeom k).symm
  refine (s0c_thC_box_le h hh hc a b _
    (fun k => mul_nonneg hCβ0 (mul_nonneg (by positivity) hL.le)) hsum
    (hhead a b hab)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [tsum_congr hgeom, tsum_mul_left, tsum_geometric_two]
  ring

/-- Lane C helper: a pointwise domination `|F| ≤ C G` on `𝕌` passes the Carleson property
from `G` to `F`. -/
theorem s0c_isCarlesonFn_of_le (F G : ℝ → ℝ → ℝ) (C : ℝ)
    (hFG : ∀ x y : ℝ, 0 < y → |F x y| ≤ C * G x y) (hG : VanishingCarleson.IsCarlesonFn G) :
    VanishingCarleson.IsCarlesonFn F := by
  have hpt : ∀ a b : ℝ, VanishingCarleson.carlesonBoxLIntegral F a b ≤
      ENNReal.ofReal (C ^ 2) * VanishingCarleson.carlesonBoxLIntegral G a b := by
    intro a b
    unfold VanishingCarleson.carlesonBoxLIntegral
    rw [← lintegral_const_mul' _ _ (by finiteness)]
    apply lintegral_mono
    intro p
    show ENNReal.ofReal (F p.1 p.2 ^ 2 / p.2) ≤
      ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (G p.1 p.2 ^ 2 / p.2)
    by_cases hy : 0 < p.2
    · rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C ^ 2)]
      apply ENNReal.ofReal_le_ofReal
      have hFy := hFG p.1 p.2 hy
      have h1 : |F p.1 p.2| ^ 2 ≤ (C * G p.1 p.2) ^ 2 :=
        sq_le_sq' (by linarith [abs_nonneg (F p.1 p.2)]) hFy
      have hsq : F p.1 p.2 ^ 2 ≤ C ^ 2 * G p.1 p.2 ^ 2 := by
        rw [← sq_abs (F p.1 p.2)]
        calc |F p.1 p.2| ^ 2 ≤ (C * G p.1 p.2) ^ 2 := h1
          _ = C ^ 2 * G p.1 p.2 ^ 2 := by ring
      calc F p.1 p.2 ^ 2 / p.2 ≤ (C ^ 2 * G p.1 p.2 ^ 2) / p.2 :=
            div_le_div_of_nonneg_right hsq hy.le
        _ = C ^ 2 * (G p.1 p.2 ^ 2 / p.2) := by ring
    · push Not at hy
      have hle0 : F p.1 p.2 ^ 2 / p.2 ≤ 0 := div_nonpos_iff.mpr (Or.inl ⟨sq_nonneg _, hy⟩)
      rw [ENNReal.ofReal_of_nonpos hle0]
      exact bot_le
  obtain ⟨CG, hCGnn, hCGbd⟩ := hG
  refine ⟨C ^ 2 * CG, by positivity, fun a b hab => ?_⟩
  calc VanishingCarleson.carlesonBoxLIntegral F a b
      ≤ ENNReal.ofReal (C ^ 2) * VanishingCarleson.carlesonBoxLIntegral G a b := hpt a b
    _ ≤ ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (CG * (b - a)) :=
        mul_le_mul_right (hCGbd a b hab) _
    _ = ENNReal.ofReal (C ^ 2 * CG * (b - a)) := by
        rw [← ENNReal.ofReal_mul (by positivity), mul_assoc]

/-- C3 (uniform VC main theorem): for `h' ∈ A_∞(ℝ)`, `|μ_{e(h)}|² dxdy/y ∈ CM(𝕌)`,
`‖μ_{e(h)}‖ ≤ k < 1` on `𝕌`, and `μ_{e(h)}` is continuous on `𝕌`. -/
theorem s0c_de_uniform (h : ℝ → ℝ) (hh : StrictMono h)
    (hac : VanishingCarleson.LocallyAbsolutelyContinuous h) (hsurj : Function.Surjective h)
    (hw : VanishingCarleson.AInfinityWeight (deriv h)) :
    VanishingCarleson.IsCarlesonFn
        (fun x y => ‖_root_.complexDilatation (VanishingCarleson.douadyEarle h) (x + y * I)‖) ∧
      (∃ k : ℝ, k < 1 ∧ ∀ z : ℂ, 0 < z.im →
        ‖_root_.complexDilatation (VanishingCarleson.douadyEarle h) z‖ ≤ k) ∧
      ContinuousOn (_root_.complexDilatation (VanishingCarleson.douadyEarle h)) {z : ℂ | 0 < z.im} := by
  obtain ⟨ρ, hρ, hqs⟩ := VanishingCarleson.ainfty_imp_quasisymmetric h hh hsurj hac hw
  obtain ⟨C, hC, hfwd⟩ := VanishingCarleson.forward_to_theta ρ hρ
  obtain ⟨K, hK, hbound⟩ := VanishingCarleson.de_quasiconformal ρ hρ
  refine ⟨s0c_isCarlesonFn_of_le _ (VanishingCarleson.Theta h) C (fun x y hy => ?_)
      (s0c_theta_uniform h hh hac hsurj hw),
    ⟨(K - 1) / (K + 1), by rw [div_lt_one (by linarith)]; linarith, fun z hz => hbound h hqs z hz⟩,
    VanishingCarleson.continuousOn_complexDilatation_douadyEarle h hh hac.1 hsurj⟩
  exact (abs_of_nonneg (norm_nonneg _)).trans_le (hfwd h hqs x y hy)

/-- Lane C helper: the Douady–Earle extension maps `𝔻` onto `𝔻`, with an inverse continuous on `𝔻`. -/
theorem s0c_de_disk (φ : Circle → Circle) (hφ : Function.Bijective φ) (hφc : Continuous φ) :
    extension φ '' unitDisc = unitDisc ∧ InjOn (extension φ) unitDisc ∧
      ContinuousOn (extension φ) unitDisc ∧
      ∃ g : ℂ → ℂ, ContinuousOn g unitDisc ∧ InvOn g (extension φ) unitDisc unitDisc := by
  obtain ⟨hbij, hcont, ext_inv, hinvc, hinv⟩ := extension_isHomeomorphOn φ hφ hφc
  have hΦd : ∀ w : ℂ, ‖w‖ < 1 → ‖extension φ w‖ < 1 := extension_mem_disk φ hφ hφc
  have hsub : unitDisc ⊆ closedBall (0 : ℂ) 1 := ball_subset_closedBall
  have hid : ∀ w : ℂ, ‖w‖ < 1 → ‖ext_inv w‖ < 1 := by
    intro w hw
    have hwc : w ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr hw.le
    obtain ⟨x, hx, rfl⟩ := hbij.surjOn hwc
    rw [hinv.1 hx]
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hx) with hlt | heq
    · exact hlt
    · exfalso
      have hm : x ∈ Submonoid.unitSphere ℂ := mem_sphere_zero_iff_norm.2 heq
      have e : extension φ x = (φ ⟨x, hm⟩ : ℂ) := extension_eq_boundary φ ⟨x, hm⟩
      have h1 : ‖extension φ x‖ = 1 := by
        rw [e]
        exact Circle.norm_coe _
      linarith
  refine ⟨?_, hbij.injOn.mono hsub, hcont.mono hsub, ext_inv, hinvc.mono hsub, ?_, ?_⟩
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact mem_ball_zero_iff.mpr (hΦd z (mem_ball_zero_iff.mp hz))
    · intro hw
      have hw' := mem_ball_zero_iff.mp hw
      exact ⟨ext_inv w, mem_ball_zero_iff.mpr (hid w hw'),
        hinv.2 (mem_closedBall_zero_iff.mpr hw'.le)⟩
  · intro w hw
    exact hinv.1 (hsub hw)
  · intro w hw
    exact hinv.2 (hsub hw)

/-- C4 (bridge): the Douady–Earle extension of an orientation preserving circle homeomorphism
with `|μ| ≤ k < 1` on `𝔻` is `(1+k)/(1-k)`-quasiconformal on `𝔻` and maps `𝔻` onto `𝔻`. -/
theorem s0c_de_isKQC (φ : Circle → Circle) (hφ : Function.Bijective φ) (hφc : Continuous φ)
    (hor : HasIncreasingLift φ) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ z ∈ unitDisc, ‖LiZhongQC.complexDilatation (extension φ) z‖ ≤ k) :
    IsKQC (extension φ) unitDisc ((1 + k) / (1 - k)) ∧ extension φ '' unitDisc = unitDisc := by
  obtain ⟨himg, hinj, hcont, g, hgc, hginv⟩ := s0c_de_disk φ hφ hφc
  have hk1' : 0 < 1 - k := by linarith
  have hΦan := extension_analyticOn_disk φ hφ hφc
  have hΦc1 : ContDiffOn ℝ 1 (extension φ) unitDisc := hΦan.contDiffOn isOpen_ball.uniqueDiffOn
  have hgm : ∀ w ∈ unitDisc, g w ∈ unitDisc := by
    intro w hw
    rw [← himg] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    rw [hginv.1 ha]
    exact ha
  have hinvF : ∀ w ∈ unitDisc, Function.invFunOn (extension φ) unitDisc w = g w := by
    intro w hw
    have hex : ∃ a ∈ unitDisc, extension φ a = w := ⟨g w, hgm w hw, hginv.2 hw⟩
    exact hinj (Function.invFunOn_mem hex) (hgm w hw)
      ((Function.invFunOn_eq hex).trans (hginv.2 hw).symm)
  refine ⟨isKQC_of_isC1Quasiconformal ⟨isOpen_ball, ?_, hΦc1, ⟨hcont, hinj, rfl, ?_⟩,
    fun z hz => ⟨?_, ?_⟩⟩, himg⟩
  · rw [le_div_iff₀ hk1']
    linarith
  · rw [himg]
    exact hgc.congr hinvF
  · have hj := extension_jacobian_pos φ hφ hφc hor z (mem_ball_zero_iff.mp hz)
    unfold dz dzbar
    rw [norm_div, norm_div]
    exact div_lt_div_of_pos_right hj (by norm_num)
  · have hm := hb z hz
    have hm0 := norm_nonneg (LiZhongQC.complexDilatation (extension φ) z)
    unfold dilatationQuotient
    rw [div_le_div_iff₀ (by linarith) hk1']
    nlinarith

/-- Lane C helper: VC's Cayley map is LZ's. -/
theorem s0c_vc_cayley_eq : VanishingCarleson.cayley = LiZhongQC.cayley := rfl

/-- Lane C helper: `C'(z) = 2i/(z + i)²`. -/
theorem s0c_cc_hasDerivAt {z : ℂ} (hz : z + I ≠ 0) :
    HasDerivAt LiZhongQC.cayley (2 * I / (z + I) ^ 2) z := by
  have h := ((hasDerivAt_id z).sub_const I).div ((hasDerivAt_id z).add_const I) hz
  have e : LiZhongQC.cayley = fun w => (id w - I) / (id w + I) := rfl
  rw [e]
  convert h using 1
  simp only [id]
  field_simp
  ring

/-- Lane C helper: `‖z ± i‖² = x² + (y ± 1)²`. -/
theorem s0c_cc_normsq_add (z : ℂ) : ‖z + I‖ ^ 2 = z.re ^ 2 + (z.im + 1) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp
  ring

theorem s0c_cc_normsq_sub (z : ℂ) : ‖z - I‖ ^ 2 = z.re ^ 2 + (z.im - 1) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp
  ring

/-- Lane C helper: `1 - |C z|² = 4y/|z + i|²` on `ℍ`. -/
theorem s0c_cc_one_sub {z : ℂ} (hz : 0 < z.im) :
    1 - ‖LiZhongQC.cayley z‖ ^ 2 = 4 * z.im / ‖z + I‖ ^ 2 := by
  have hd : ‖z + I‖ ≠ 0 := norm_ne_zero_iff.mpr (cayley_den_ne_zero hz)
  have hd2 : ‖z + I‖ ^ 2 ≠ 0 := pow_ne_zero 2 hd
  unfold LiZhongQC.cayley
  rw [norm_div, div_pow, s0c_cc_normsq_sub]
  rw [eq_div_iff hd2, sub_mul, div_mul_cancel₀ _ hd2, s0c_cc_normsq_add]
  ring

/-- Lane C helper: `|C z - 1| = 2/|z + i|`. -/
theorem s0c_cc_sub_one {z : ℂ} (hz : z + I ≠ 0) : ‖LiZhongQC.cayley z - 1‖ = 2 / ‖z + I‖ := by
  have e : LiZhongQC.cayley z - 1 = -2 * I / (z + I) := by
    unfold LiZhongQC.cayley
    field_simp
    ring
  rw [e, norm_div, norm_mul, norm_neg, Complex.norm_I, mul_one]
  norm_num

/-- Lane C helper: complex boxes vs VC's `carlesonBoxLIntegral`. -/
theorem s0c_box_complex (G : ℂ → ℝ) (a b : ℝ) :
    ∫⁻ z in {z : ℂ | z.re ∈ Ioc a b ∧ z.im ∈ Ioc 0 (b - a)}, ENNReal.ofReal (G z ^ 2 / z.im) =
      VanishingCarleson.carlesonBoxLIntegral (fun x y => G (x + y * I)) a b := by
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  have h := hmp.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding
    (fun z => ENNReal.ofReal (G z ^ 2 / z.im)) {z : ℂ | z.re ∈ Ioc a b ∧ z.im ∈ Ioc 0 (b - a)}
  rw [← h]
  unfold VanishingCarleson.carlesonBoxLIntegral VanishingCarleson.carlesonBox
  have hs : Complex.measurableEquivRealProd.symm ⁻¹'
      {z : ℂ | z.re ∈ Ioc a b ∧ z.im ∈ Ioc 0 (b - a)} = Ioc a b ×ˢ Ioc (0 : ℝ) (b - a) := by
    ext p
    simp [Complex.measurableEquivRealProd_symm_apply]
  rw [hs]
  refine setLIntegral_congr_fun (measurableSet_Ioc.prod measurableSet_Ioc) fun p _ => ?_
  have e : (⟨p.1, p.2⟩ : ℂ) = (p.1 : ℂ) + p.2 * I := by apply Complex.ext <;> simp
  rw [Complex.measurableEquivRealProd_symm_apply, e]
  simp

/-- Lane C helper (change of variables `w = C z`): the disk measure `ν²/(1-|w|²) dA` of
`S ⊆ 𝔻` is `∫_{C⁻¹ S} ν(Cz)²/(y |z+i|²) dA`. -/
theorem s0c_cc_cov (ν : ℂ → ℝ) {S : Set ℂ} (hS : MeasurableSet S) (hS1 : S ⊆ unitDisc) :
    ((volume.restrict unitDisc).withDensity fun w => ENNReal.ofReal (ν w ^ 2 / (1 - ‖w‖ ^ 2))) S =
      ∫⁻ z in {z : ℂ | 0 < z.im ∧ LiZhongQC.cayley z ∈ S},
        ENNReal.ofReal (ν (LiZhongQC.cayley z) ^ 2 / (z.im * ‖z + I‖ ^ 2)) := by
  rw [withDensity_apply _ hS, Measure.restrict_restrict hS, inter_eq_left.mpr hS1]
  have hcm : Measurable LiZhongQC.cayley :=
    (measurable_id.sub_const I).div (measurable_id.add_const I)
  set T : Set ℂ := {z : ℂ | 0 < z.im ∧ LiZhongQC.cayley z ∈ S} with hTdef
  have hT : MeasurableSet T :=
    (measurableSet_lt measurable_const Complex.measurable_im).inter (hcm hS)
  have hinj : InjOn LiZhongQC.cayley T := fun x hx y hy hxy => by
    rw [← cayleyInv_cayley hx.1, ← cayleyInv_cayley hy.1, hxy]
  have hSeq : LiZhongQC.cayley '' T = S := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz.2
    · intro hw
      have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp (hS1 hw)
      refine ⟨cayleyInv w, ⟨cayleyInv_mem_upperHalf hw1, ?_⟩, cayley_cayleyInv hw1⟩
      rw [cayley_cayleyInv hw1]
      exact hw
  have hdet : ∀ d : ℂ,
      ((ContinuousLinearMap.toSpanSingleton ℂ d).restrictScalars ℝ).det = Complex.normSq d := by
    intro d
    simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hT
    (fun z hz => ((s0c_cc_hasDerivAt (cayley_den_ne_zero hz.1)).hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt) hinj (fun w => ENNReal.ofReal (ν w ^ 2 / (1 - ‖w‖ ^ 2)))
  rw [hSeq] at hcv
  rw [hcv]
  refine setLIntegral_congr_fun hT fun z hz => ?_
  have hy : 0 < z.im := hz.1
  have hd : ‖z + I‖ ≠ 0 := norm_ne_zero_iff.mpr (cayley_den_ne_zero hy)
  rw [hdet, Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _), s0c_cc_one_sub hy,
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  rw [norm_div, norm_mul, norm_pow, Complex.norm_I, mul_one]
  rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
  field_simp
  ring

/-- Lane C helper (C5, part near `C(∞) = 1`): `∫_{|z+i| > R} G²/(y|z+i|²) ≤ 8C/R` when
`G(x+iy)² dxdy/y` has Carleson constant `C` (dyadic annuli `2^j R ≤ |z+i| < 2^{j+1} R`). -/
theorem s0c_cc_far {G : ℂ → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ a b : ℝ, a < b → VanishingCarleson.carlesonBoxLIntegral (fun x y => G (x + y * I)) a b ≤
      ENNReal.ofReal (C * (b - a)))
    {R : ℝ} (hR : 0 < R) :
    ∫⁻ z in {z : ℂ | 0 < z.im ∧ R < ‖z + I‖}, ENNReal.ofReal (G z ^ 2 / (z.im * ‖z + I‖ ^ 2)) ≤
      ENNReal.ofReal (8 * C / R) := by
  have hn : Measurable fun z : ℂ => ‖z + I‖ := (measurable_id.add_const I).norm
  set A : ℕ → Set ℂ := fun j =>
    {z : ℂ | 0 < z.im ∧ 2 ^ j * R ≤ ‖z + I‖ ∧ ‖z + I‖ < 2 ^ (j + 1) * R} with hAdef
  have hAm : ∀ j, MeasurableSet (A j) := fun j =>
    (measurableSet_lt measurable_const Complex.measurable_im).inter
      ((measurableSet_le measurable_const hn).inter (measurableSet_lt hn measurable_const))
  have hcov : {z : ℂ | 0 < z.im ∧ R < ‖z + I‖} ⊆ ⋃ j, A j := by
    rintro z ⟨hy, hz⟩
    have h1 : 1 ≤ ‖z + I‖ / R := by rw [le_div_iff₀ hR]; linarith
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near h1 (by norm_num : (1 : ℝ) < 2)
    refine mem_iUnion.mpr ⟨n, hy, ?_, ?_⟩
    · rw [le_div_iff₀ hR] at hn1; linarith
    · rw [div_lt_iff₀ hR] at hn2; linarith
  have hpiece : ∀ j : ℕ, ∫⁻ z in A j, ENNReal.ofReal (G z ^ 2 / (z.im * ‖z + I‖ ^ 2)) ≤
      ENNReal.ofReal (4 * C / R * (1 / 2) ^ j) := by
    intro j
    set q : ℝ := 2 ^ j * R with hqdef
    have hq : 0 < q := by positivity
    set L : ℝ := 2 ^ (j + 1) * R with hLdef
    have hLq : L = 2 * q := by rw [hLdef, hqdef, pow_succ]; ring
    have hsub : A j ⊆ {z : ℂ | z.re ∈ Ioc (-L) L ∧ z.im ∈ Ioc 0 (L - -L)} := by
      rintro z ⟨hy, -, hzL⟩
      have h1 : |z.re| ≤ ‖z + I‖ := by
        have := Complex.abs_re_le_norm (z + I)
        simpa using this
      have h2 : z.im + 1 ≤ ‖z + I‖ := by
        have := Complex.im_le_norm (z + I)
        simpa using this
      refine ⟨⟨?_, ?_⟩, hy, ?_⟩
      · linarith [neg_abs_le z.re]
      · linarith [le_abs_self z.re]
      · linarith
    calc ∫⁻ z in A j, ENNReal.ofReal (G z ^ 2 / (z.im * ‖z + I‖ ^ 2))
        ≤ ∫⁻ z in A j, ENNReal.ofReal ((q ^ 2)⁻¹) * ENNReal.ofReal (G z ^ 2 / z.im) := by
          refine setLIntegral_mono' (hAm j) fun z hz => ?_
          obtain ⟨hy, hqz, -⟩ := hz
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have hn2 : q ^ 2 ≤ ‖z + I‖ ^ 2 := pow_le_pow_left₀ hq.le hqz 2
          have hg : 0 ≤ G z ^ 2 / z.im := div_nonneg (sq_nonneg _) hy.le
          rw [show G z ^ 2 / (z.im * ‖z + I‖ ^ 2) = (G z ^ 2 / z.im) / ‖z + I‖ ^ 2 by
            rw [div_div], inv_mul_eq_div]
          exact div_le_div_of_nonneg_left hg (by positivity) hn2
      _ = ENNReal.ofReal ((q ^ 2)⁻¹) * ∫⁻ z in A j, ENNReal.ofReal (G z ^ 2 / z.im) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((q ^ 2)⁻¹) *
            ∫⁻ z in {z : ℂ | z.re ∈ Ioc (-L) L ∧ z.im ∈ Ioc 0 (L - -L)},
              ENNReal.ofReal (G z ^ 2 / z.im) := by
          gcongr
      _ = ENNReal.ofReal ((q ^ 2)⁻¹) *
            VanishingCarleson.carlesonBoxLIntegral (fun x y => G (x + y * I)) (-L) L := by
          rw [s0c_box_complex]
      _ ≤ ENNReal.ofReal ((q ^ 2)⁻¹) * ENNReal.ofReal (C * (L - -L)) := by
          gcongr
          exact hC _ _ (by linarith)
      _ = ENNReal.ofReal (4 * C / R * (1 / 2) ^ j) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hLq, hqdef, one_div, inv_pow]
          field_simp
          ring
  have hs0 : ∀ j : ℕ, 0 ≤ 4 * C / R * (1 / 2 : ℝ) ^ j := fun j => by positivity
  have hss : Summable fun j : ℕ => 4 * C / R * (1 / 2 : ℝ) ^ j :=
    summable_geometric_two.mul_left _
  calc ∫⁻ z in {z : ℂ | 0 < z.im ∧ R < ‖z + I‖}, ENNReal.ofReal (G z ^ 2 / (z.im * ‖z + I‖ ^ 2))
      ≤ ∫⁻ z in ⋃ j, A j, ENNReal.ofReal (G z ^ 2 / (z.im * ‖z + I‖ ^ 2)) := lintegral_mono_set hcov
    _ ≤ ∑' j, ∫⁻ z in A j, ENNReal.ofReal (G z ^ 2 / (z.im * ‖z + I‖ ^ 2)) := lintegral_iUnion_le _ _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (4 * C / R * (1 / 2) ^ j) := tsum_le_tsum fun j => hpiece j
    _ = ENNReal.ofReal (∑' j : ℕ, 4 * C / R * (1 / 2 : ℝ) ^ j) :=
        (ENNReal.ofReal_tsum_of_nonneg hs0 hss).symm
    _ = ENNReal.ofReal (8 * C / R) := by
        rw [tsum_mul_left, tsum_geometric_two]
        ring_nf

/-- Lane C helper: `Im C⁻¹(ζ) = (1 - |ζ|²)/|1 - ζ|²`. -/
theorem s0c_cayleyInv_im (ζ : ℂ) :
    (LiZhongQC.cayleyInv ζ).im = (1 - Complex.normSq ζ) / Complex.normSq (1 - ζ) := by
  simp only [LiZhongQC.cayleyInv, Complex.div_im, Complex.mul_im, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
  ring

/-- Lane C helper (C5, boxes away from `1`): if `2r < |ζ - 1|`, then the pull-back of
`𝔻 ∩ D(ζ, r)` lies in one Carleson box of side `8r/|ζ-1|²` on which `|z + i| ≥ 4/(3|ζ-1|)`. -/
theorem s0c_cc_near {G : ℂ → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    {ζ : ℂ} {r : ℝ}
    (hC : ∀ a b : ℝ, a < b → b - a ≤ 8 * r / ‖ζ - 1‖ ^ 2 →
      VanishingCarleson.carlesonBoxLIntegral (fun x y => G (x + y * I)) a b ≤
        ENNReal.ofReal (C * (b - a)))
    (hζ : ‖ζ‖ = 1) (hr : 0 < r) (hd : 2 * r < ‖ζ - 1‖) :
    ∫⁻ z in {z : ℂ | 0 < z.im ∧ LiZhongQC.cayley z ∈ unitDisc ∩ ball ζ r},
        ENNReal.ofReal (G z ^ 2 / (z.im * ‖z + I‖ ^ 2)) ≤ ENNReal.ofReal (5 * C * r) := by
  set d : ℝ := ‖ζ - 1‖ with hddef
  have hd0 : 0 < d := by linarith
  have hζ1 : (1 : ℂ) - ζ ≠ 0 := by
    intro h
    have : ζ - 1 = 0 := by rw [show ζ - 1 = -(1 - ζ) by ring, h, neg_zero]
    rw [this, norm_zero] at hddef
    linarith
  have hd1 : ‖(1 : ℂ) - ζ‖ = d := by rw [hddef, norm_sub_rev]
  set z₀ : ℂ := LiZhongQC.cayleyInv ζ with hz₀
  have hz₀im : z₀.im = 0 := by
    rw [hz₀, s0c_cayleyInv_im, Complex.normSq_eq_norm_sq, hζ]
    simp
  set ρ : ℝ := 4 * r / d ^ 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  set T : Set ℂ := {z : ℂ | 0 < z.im ∧ LiZhongQC.cayley z ∈ unitDisc ∩ ball ζ r} with hT
  have hcm : Measurable LiZhongQC.cayley :=
    (measurable_id.sub_const I).div (measurable_id.add_const I)
  have hTm : MeasurableSet T :=
    (measurableSet_lt measurable_const Complex.measurable_im).inter
      (hcm (measurableSet_ball.inter measurableSet_ball))
  have hpt : ∀ z ∈ T, ‖z - z₀‖ < ρ ∧ 16 / (9 * d ^ 2) ≤ ‖z + I‖ ^ 2 := by
    rintro z ⟨hy, hw1, hwζ⟩
    have hw1' : ‖LiZhongQC.cayley z‖ < 1 := mem_ball_zero_iff.mp hw1
    have hwζ' : ‖LiZhongQC.cayley z - ζ‖ < r := mem_ball_iff_norm.mp hwζ
    have h1w : (1 : ℂ) - LiZhongQC.cayley z ≠ 0 := cayleyInv_den_ne_zero hw1'
    have hzw : LiZhongQC.cayleyInv (LiZhongQC.cayley z) = z := cayleyInv_cayley hy
    have hid : ∀ w : ℂ, (1 : ℂ) - w ≠ 0 → LiZhongQC.cayleyInv w - LiZhongQC.cayleyInv ζ =
        2 * I * (w - ζ) / ((1 - w) * (1 - ζ)) := by
      intro w hw
      unfold LiZhongQC.cayleyInv
      field_simp
      ring
    have hlow : d / 2 < ‖(1 : ℂ) - LiZhongQC.cayley z‖ := by
      have := norm_sub_norm_le ((1 : ℂ) - ζ) (LiZhongQC.cayley z - ζ)
      rw [show (1 : ℂ) - ζ - (LiZhongQC.cayley z - ζ) = 1 - LiZhongQC.cayley z by ring,
        hd1] at this
      linarith
    have hup : ‖LiZhongQC.cayley z - 1‖ < 3 * d / 2 := by
      have := norm_add_le (LiZhongQC.cayley z - ζ) (ζ - 1)
      rw [show LiZhongQC.cayley z - ζ + (ζ - 1) = LiZhongQC.cayley z - 1 by ring] at this
      linarith
    constructor
    · have e := hid _ h1w
      rw [hzw, ← hz₀] at e
      rw [e, norm_div, norm_mul, norm_mul, norm_mul, hd1, Complex.norm_I, mul_one,
        show ‖(2 : ℂ)‖ = 2 by norm_num, hρ, div_lt_div_iff₀ (by positivity) (by positivity)]
      have h2 : 0 ≤ ‖LiZhongQC.cayley z - ζ‖ := norm_nonneg _
      have h3 : d * d < 2 * ‖(1 : ℂ) - LiZhongQC.cayley z‖ * d := by nlinarith
      nlinarith [mul_lt_mul_of_pos_right hwζ' (by positivity : (0 : ℝ) < 2 * d ^ 2)]
    · have hsub := s0c_cc_sub_one (cayley_den_ne_zero hy)
      have hzI : 0 < ‖z + I‖ := norm_pos_iff.mpr (cayley_den_ne_zero hy)
      have hk : 4 / (3 * d) < ‖z + I‖ := by
        rw [hsub, div_lt_iff₀ hzI] at hup
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      have h0 : 0 ≤ 4 / (3 * d) := by positivity
      calc 16 / (9 * d ^ 2) = (4 / (3 * d)) ^ 2 := by field_simp; ring
        _ ≤ ‖z + I‖ ^ 2 := pow_le_pow_left₀ h0 hk.le 2
  set a : ℝ := z₀.re - ρ with ha
  set b : ℝ := z₀.re + ρ with hb
  have hab : a < b := by rw [ha, hb]; linarith
  have hsub : T ⊆ {z : ℂ | z.re ∈ Ioc a b ∧ z.im ∈ Ioc 0 (b - a)} := by
    intro z hz
    obtain ⟨hzz, -⟩ := hpt z hz
    have hre : |(z - z₀).re| ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
    have him : (z - z₀).im ≤ ‖z - z₀‖ := Complex.im_le_norm _
    rw [Complex.sub_re] at hre
    rw [Complex.sub_im, hz₀im, sub_zero] at him
    refine ⟨⟨?_, ?_⟩, hz.1, ?_⟩
    · rw [ha]; linarith [neg_abs_le (z.re - z₀.re)]
    · rw [hb]; linarith [le_abs_self (z.re - z₀.re)]
    · rw [ha, hb]; linarith
  calc ∫⁻ z in T, ENNReal.ofReal (G z ^ 2 / (z.im * ‖z + I‖ ^ 2))
      ≤ ∫⁻ z in T, ENNReal.ofReal (9 * d ^ 2 / 16) * ENNReal.ofReal (G z ^ 2 / z.im) := by
        refine setLIntegral_mono' hTm fun z hz => ?_
        obtain ⟨-, hn2⟩ := hpt z hz
        have hy : 0 < z.im := hz.1
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hg : 0 ≤ G z ^ 2 / z.im := div_nonneg (sq_nonneg _) hy.le
        have hpos : 0 < 16 / (9 * d ^ 2) := by positivity
        rw [show G z ^ 2 / (z.im * ‖z + I‖ ^ 2) = (G z ^ 2 / z.im) / ‖z + I‖ ^ 2 by
          rw [div_div]]
        calc (G z ^ 2 / z.im) / ‖z + I‖ ^ 2 ≤ (G z ^ 2 / z.im) / (16 / (9 * d ^ 2)) :=
              div_le_div_of_nonneg_left hg hpos hn2
          _ = 9 * d ^ 2 / 16 * (G z ^ 2 / z.im) := by field_simp
    _ = ENNReal.ofReal (9 * d ^ 2 / 16) * ∫⁻ z in T, ENNReal.ofReal (G z ^ 2 / z.im) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (9 * d ^ 2 / 16) *
          ∫⁻ z in {z : ℂ | z.re ∈ Ioc a b ∧ z.im ∈ Ioc 0 (b - a)},
            ENNReal.ofReal (G z ^ 2 / z.im) := by
        gcongr
    _ = ENNReal.ofReal (9 * d ^ 2 / 16) *
          VanishingCarleson.carlesonBoxLIntegral (fun x y => G (x + y * I)) a b := by
        rw [s0c_box_complex]
    _ ≤ ENNReal.ofReal (9 * d ^ 2 / 16) * ENNReal.ofReal (C * (b - a)) := by
        gcongr
        exact hC a b hab (le_of_eq (by rw [ha, hb, hρ]; ring))
    _ ≤ ENNReal.ofReal (5 * C * r) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have e : b - a = 8 * r / d ^ 2 := by rw [ha, hb, hρ]; ring
        rw [e]
        have e2 : 9 * d ^ 2 / 16 * (C * (8 * r / d ^ 2)) = 9 / 2 * C * r := by
          field_simp
          ring
        rw [e2]
        nlinarith [mul_nonneg hC0 hr.le]

/-- C5 (box transfer `CM(𝕌) → CM(𝔻)`): if `ν(γ z)² dxdy/y` is Carleson on `𝕌`, then
`ν(w)²/(1-|w|²) dA` is Carleson on `𝔻`. -/
theorem s0c_carleson_cayley {ν : ℂ → ℝ} (hν : Measurable ν) (hν0 : ∀ w, 0 ≤ ν w)
    (hC : VanishingCarleson.IsCarlesonFn fun x y => ν (VanishingCarleson.cayley (x + y * I))) :
    IsCarlesonDisk ((volume.restrict unitDisc).withDensity fun w =>
      ENNReal.ofReal (ν w ^ 2 / (1 - ‖w‖ ^ 2))) := by
  obtain ⟨C, hC0, hCb⟩ := hC
  have hCb' : ∀ a b : ℝ, a < b → VanishingCarleson.carlesonBoxLIntegral
      (fun x y => (fun z => ν (LiZhongQC.cayley z)) (x + y * I)) a b ≤
        ENNReal.ofReal (C * (b - a)) := hCb
  refine ⟨ENNReal.ofReal (12 * C), ENNReal.ofReal_ne_top, fun ζ hζ r hr hr2 => ?_⟩
  have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
  have hS : MeasurableSet (unitDisc ∩ ball ζ r) := measurableSet_ball.inter measurableSet_ball
  rw [s0c_cc_cov ν hS inter_subset_left, ← ENNReal.ofReal_mul (by positivity)]
  rcases le_or_gt ‖ζ - 1‖ (2 * r) with hcase | hcase
  · have hR : 0 < 2 / (3 * r) := by positivity
    have hsub : {z : ℂ | 0 < z.im ∧ LiZhongQC.cayley z ∈ unitDisc ∩ ball ζ r} ⊆
        {z : ℂ | 0 < z.im ∧ 2 / (3 * r) < ‖z + I‖} := by
      rintro z ⟨hy, -, hwζ⟩
      refine ⟨hy, ?_⟩
      have hwζ' : ‖LiZhongQC.cayley z - ζ‖ < r := mem_ball_iff_norm.mp hwζ
      have h3 : ‖LiZhongQC.cayley z - 1‖ < 3 * r := by
        have := norm_add_le (LiZhongQC.cayley z - ζ) (ζ - 1)
        rw [show LiZhongQC.cayley z - ζ + (ζ - 1) = LiZhongQC.cayley z - 1 by ring] at this
        linarith
      have hzI : 0 < ‖z + I‖ := norm_pos_iff.mpr (cayley_den_ne_zero hy)
      rw [s0c_cc_sub_one (cayley_den_ne_zero hy), div_lt_iff₀ hzI] at h3
      rw [div_lt_iff₀ (by positivity)]
      linarith
    refine (lintegral_mono_set hsub).trans ((s0c_cc_far (G := fun z => ν (LiZhongQC.cayley z))
      hC0 hCb' hR).trans (le_of_eq ?_))
    congr 1
    field_simp
    ring
  · refine (s0c_cc_near (G := fun z => ν (LiZhongQC.cayley z)) hC0
      (fun a b hab _ => hCb' a b hab) hζ1 hr hcase).trans ?_
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_nonneg hC0 hr.le]

/-- C5v' (box transfer `CM₀(𝕌) → CM₀(𝔻)` away from `γ(∞) = 1`). -/
theorem s0c_vcarleson_cayley {ν : ℂ → ℝ} (hν : Measurable ν) (hν0 : ∀ w, 0 ≤ ν w)
    (hC : VanishingCarleson.IsVanishingCarleson fun x y =>
      ν (VanishingCarleson.cayley (x + y * I))) :
    IsCarlesonDisk ((volume.restrict unitDisc).withDensity fun w =>
        ENNReal.ofReal (ν w ^ 2 / (1 - ‖w‖ ^ 2))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ ζ ∈ sphere (0 : ℂ) 1, 1 ≤ ‖ζ - 1‖ →
        ∀ r : ℝ, 0 < r → r < δ →
          ((volume.restrict unitDisc).withDensity fun w =>
            ENNReal.ofReal (ν w ^ 2 / (1 - ‖w‖ ^ 2))) (unitDisc ∩ ball ζ r) ≤
              ENNReal.ofReal (ε * r) := by
  refine ⟨s0c_carleson_cayley hν hν0 hC.1, fun ε hε => ?_⟩
  obtain ⟨δ', hδ', hV⟩ := hC.2 (ε / 5) (by positivity)
  have hV' : ∀ a b : ℝ, a < b → b - a ≤ δ' → VanishingCarleson.carlesonBoxLIntegral
      (fun x y => (fun z => ν (LiZhongQC.cayley z)) (x + y * I)) a b ≤
        ENNReal.ofReal (ε / 5 * (b - a)) := hV
  refine ⟨min (δ' / 8) (1 / 2), lt_min (by positivity) (by norm_num),
    fun ζ hζ hd r hr hrδ => ?_⟩
  have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
  have hS : MeasurableSet (unitDisc ∩ ball ζ r) := measurableSet_ball.inter measurableSet_ball
  rw [s0c_cc_cov ν hS inter_subset_left]
  have hr1 := lt_of_lt_of_le hrδ (min_le_right _ _)
  have hr8 := lt_of_lt_of_le hrδ (min_le_left _ _)
  have hcase : 2 * r < ‖ζ - 1‖ := by linarith
  have hd2 : 1 ≤ ‖ζ - 1‖ ^ 2 := one_le_pow₀ hd
  refine (s0c_cc_near (G := fun z => ν (LiZhongQC.cayley z)) (C := ε / 5) (by positivity)
    (fun a b hab hle => hV' a b hab (hle.trans ?_)) hζ1 hr hcase).trans ?_
  · exact (div_le_self (by positivity) hd2).trans (by linarith)
  · apply ENNReal.ofReal_le_ofReal
    linarith

/-- Lane C helper: `ι z = (conj z)⁻¹` maps `𝔻 \ {0}` into `𝔻*`. -/
theorem s0c_iota_ext {u : ℂ} (hu : u ∈ unitDisc) (hu0 : u ≠ 0) : (conj u)⁻¹ ∈ unitDiscExterior := by
  show 1 < ‖(conj u)⁻¹‖
  rw [abR_t_norm_inv_conj]
  exact (one_lt_inv₀ (norm_pos_iff.mpr hu0)).mpr (mem_ball_zero_iff.mp hu)

/-- Lane C helper: `ι z = (conj z)⁻¹` maps `𝔻*` into `𝔻 \ {0}`. -/
theorem s0c_iota_disk {z : ℂ} (hz : z ∈ unitDiscExterior) :
    (conj z)⁻¹ ∈ unitDisc ∧ (conj z)⁻¹ ≠ 0 := by
  have hz1 : 1 < ‖z‖ := hz
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz1; linarith
  refine ⟨?_, inv_ne_zero ((map_ne_zero _).2 hz0)⟩
  apply mem_ball_zero_iff.mpr
  rw [abR_t_norm_inv_conj]
  exact inv_lt_one_of_one_lt₀ hz1

/-- Lane C helper: pointwise dilatation of the reflected map `z ↦ 1/conj(h(1/z̄))` on `𝔻*`
(pointwise form of LZ `abR_exterior`). -/
theorem s0c_ext_dil {h : ℂ → ℂ} {z : ℂ} (hz : 1 < ‖z‖)
    (hd : DifferentiableAt ℝ h (conj z)⁻¹) (hne : h (conj z)⁻¹ ≠ 0) :
    ‖LiZhongQC.complexDilatation (fun z => (conj (h (conj z)⁻¹))⁻¹) z‖ =
      ‖LiZhongQC.complexDilatation h (conj z)⁻¹‖ := by
  have hz0 : z ≠ 0 := fun h0 => by rw [h0, norm_zero] at hz; linarith
  set g : ℂ → ℂ := fun w => conj (h (conj w)) with hgdef
  have hF : (fun z => (conj (h (conj z)⁻¹))⁻¹) = nxInvConj g := by
    funext z
    simp only [nxInvConj, hgdef, map_inv₀]
  have hc : conj z⁻¹ = (conj z)⁻¹ := map_inv₀ _ _
  have hd' : DifferentiableAt ℝ h (conj z⁻¹) := by rw [hc]; exact hd
  obtain ⟨hgd, hdz, hdzbar⟩ := abR_x_dz_dzbar_conj hd'
  have hgz : g z⁻¹ ≠ 0 := by
    show conj (h (conj z⁻¹)) ≠ 0
    rw [hc]
    exact (map_ne_zero _).2 hne
  rw [hF, nxI2_dilatation_invConj_at hz0 hgz hgd, norm_mul]
  have hn1 : ‖z ^ 2 / conj z ^ 2‖ = 1 := by
    rw [norm_div, norm_pow, norm_pow, Complex.norm_conj]
    exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.2 hz0))
  rw [hn1, mul_one, LiZhongQC.complexDilatation, LiZhongQC.complexDilatation, hdz, hdzbar,
    norm_div, norm_div, Complex.norm_conj, Complex.norm_conj, hc]

/-- Lane C helper (C6 box): if `m(w) = ν(1/w̄)` on `𝔻*` and `ν²/(1-|w|²) dA` has disk Carleson
bound `C'`, then `∫_{𝔻* ∩ D(ζ,r)} m²/(|w|²-1) ≤ 9 C' r` (change of variables `w = 1/ū`). -/
theorem s0c_ext_box {m ν : ℂ → ℝ} (hm : ∀ w ∈ unitDiscExterior, m w = ν (conj w)⁻¹)
    {C' : ℝ≥0∞} {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) {r : ℝ} (hr : 0 < r) (hr2 : r < 2)
    (hC : ((volume.restrict unitDisc).withDensity fun w =>
        ENNReal.ofReal (ν w ^ 2 / (1 - ‖w‖ ^ 2))) (unitDisc ∩ ball ζ r) ≤ C' * ENNReal.ofReal r) :
    ∫⁻ w in unitDiscExterior ∩ ball ζ r, ENNReal.ofReal (m w ^ 2 / (‖w‖ ^ 2 - 1)) ≤
      ENNReal.ofReal 9 * (C' * ENNReal.ofReal r) := by
  have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
  set ι : ℂ → ℂ := fun u => (conj u)⁻¹ with hιdef
  set S : Set ℂ := unitDiscExterior ∩ ball ζ r with hSdef
  set U : Set ℂ := unitDisc ∩ ({0}ᶜ ∩ ι ⁻¹' S) with hUdef
  have hιι : ∀ u, ι (ι u) = u := fun u => abR_t_conj_inv_inv u
  have hιn : ∀ u, ‖ι u‖ = ‖u‖⁻¹ := fun u => abR_t_norm_inv_conj u
  have hιm : Measurable ι := Complex.continuous_conj.measurable.inv
  have hSm : MeasurableSet S :=
    (isOpen_lt continuous_const continuous_norm).measurableSet.inter measurableSet_ball
  have hUm : MeasurableSet U :=
    measurableSet_ball.inter ((measurableSet_singleton 0).compl.inter (hιm hSm))
  have hinj : InjOn ι U := fun x _ y _ hxy => by rw [← hιι x, hxy, hιι]
  have himg : ι '' U = S := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu.2.2
    · intro hw
      obtain ⟨hw1, hw0⟩ := s0c_iota_disk hw.1
      exact ⟨ι w, ⟨hw1, hw0, by show ι (ι w) ∈ S; rw [hιι]; exact hw⟩, hιι w⟩
  have hUsub : U ⊆ unitDisc ∩ ball ζ r := by
    rintro u ⟨hu1, -, hw⟩
    refine ⟨hu1, ?_⟩
    obtain ⟨hw1, hwζ⟩ := hw
    have hw1' : 1 < ‖ι u‖ := hw1
    have hwζ' : ‖ι u - ζ‖ < r := mem_ball_iff_norm.mp hwζ
    have hw0 : ι u ≠ 0 := fun h => by rw [h, norm_zero] at hw1'; linarith
    have hζ0 : ζ ≠ 0 := fun h => by rw [h, norm_zero] at hζ1; norm_num at hζ1
    have hcw : conj (ι u) ≠ 0 := (map_ne_zero _).2 hw0
    have hcζ : conj ζ ≠ 0 := (map_ne_zero _).2 hζ0
    rw [mem_ball_iff_norm, ← hιι u]
    calc ‖(conj (ι u))⁻¹ - ζ‖ = ‖(conj (ι u))⁻¹ - (conj ζ)⁻¹‖ := by
          rw [abR_t_inv_conj_of_norm_one hζ1]
      _ = ‖ι u - ζ‖ / ‖ι u‖ := by
          rw [inv_sub_inv hcw hcζ, ← map_sub, norm_div, norm_mul, Complex.norm_conj,
            Complex.norm_conj, Complex.norm_conj, hζ1, mul_one, norm_sub_rev]
      _ ≤ ‖ι u - ζ‖ := div_le_self (norm_nonneg _) hw1'.le
      _ < r := hwζ'
  have hdet : ∀ d : ℂ, (((ContinuousLinearMap.toSpanSingleton ℂ d).restrictScalars ℝ).comp
      (conjCLE : ℂ →L[ℝ] ℂ)).det = -Complex.normSq d := by
    intro d
    have h1 : ((ContinuousLinearMap.toSpanSingleton ℂ d).restrictScalars ℝ).det =
        Complex.normSq d := by
      simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]
    have h1' : LinearMap.det (((ContinuousLinearMap.toSpanSingleton ℂ d).restrictScalars ℝ :
        ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = Complex.normSq d := h1
    have h2 : LinearMap.det ((conjCLE : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = -1 := Complex.det_conjAe
    rw [ContinuousLinearMap.det, show ((((ContinuousLinearMap.toSpanSingleton ℂ d).restrictScalars ℝ).comp
        (conjCLE : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) =
        (((ContinuousLinearMap.toSpanSingleton ℂ d).restrictScalars ℝ : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) ∘ₗ
          ((conjCLE : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) from rfl, LinearMap.det_comp, h1', h2, mul_neg_one]
  have heι : ι = (fun y : ℂ => y⁻¹) ∘ (conjCLE : ℂ →L[ℝ] ℂ) := by
    funext u
    simp [hιdef]
  have hder : ∀ u ∈ U, HasFDerivWithinAt ι
      (((ContinuousLinearMap.toSpanSingleton ℂ (-((conj u) ^ 2)⁻¹)).restrictScalars ℝ).comp
        (conjCLE : ℂ →L[ℝ] ℂ)) U u := by
    intro u hu
    have hc0 : conj u ≠ 0 := (map_ne_zero _).2 hu.2.1
    rw [heι]
    exact (((hasDerivAt_inv hc0).hasFDerivAt.restrictScalars ℝ).comp u
      (conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt).hasFDerivWithinAt
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hUm hder hinj
    (fun w => ENNReal.ofReal (m w ^ 2 / (‖w‖ ^ 2 - 1)))
  rw [himg] at hcv
  have hBm : MeasurableSet (unitDisc ∩ ball ζ r) := measurableSet_ball.inter measurableSet_ball
  rw [hcv]
  calc ∫⁻ u in U, ENNReal.ofReal |(((ContinuousLinearMap.toSpanSingleton ℂ
          (-((conj u) ^ 2)⁻¹)).restrictScalars ℝ).comp (conjCLE : ℂ →L[ℝ] ℂ)).det| *
          ENNReal.ofReal (m (ι u) ^ 2 / (‖ι u‖ ^ 2 - 1))
      ≤ ∫⁻ u in U, ENNReal.ofReal 9 * ENNReal.ofReal (ν u ^ 2 / (1 - ‖u‖ ^ 2)) := by
        refine setLIntegral_mono' hUm fun u hu => ?_
        obtain ⟨hu1, hu0, hw⟩ := hu
        have hu0' : u ≠ 0 := hu0
        have hmu : m (ι u) = ν u := by
          rw [hm _ hw.1]
          exact congrArg ν (hιι u)
        have ht0 : 0 < ‖u‖ := norm_pos_iff.mpr hu0'
        have ht1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu1
        have h3 : ‖u‖⁻¹ < 3 := by
          have h1 := norm_sub_norm_le (ι u) ζ
          have h2 : ‖ι u - ζ‖ < r := mem_ball_iff_norm.mp hw.2
          rw [hιn, hζ1] at h1
          linarith
        have h13 : 1 < 3 * ‖u‖ := by
          have := mul_lt_mul_of_pos_left h3 ht0
          rw [mul_inv_cancel₀ ht0.ne'] at this
          linarith
        rw [hdet, hmu, hιn, abs_neg, abs_of_nonneg (Complex.normSq_nonneg _),
          Complex.normSq_eq_norm_sq, norm_neg, norm_inv, norm_pow, Complex.norm_conj,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
        apply ENNReal.ofReal_le_ofReal
        set t := ‖u‖ with htdef
        have hne : 1 - t ^ 2 ≠ 0 := by nlinarith
        have hpos : 0 < 1 - t ^ 2 := by nlinarith
        have e1 : t⁻¹ ^ 2 - 1 = (1 - t ^ 2) / t ^ 2 := by field_simp
        rw [e1, div_div_eq_mul_div]
        have e2 : ((t ^ 2)⁻¹) ^ 2 * (ν u ^ 2 * t ^ 2 / (1 - t ^ 2)) =
            ν u ^ 2 / (1 - t ^ 2) * (t ^ 2)⁻¹ := by
          field_simp
        rw [e2, mul_comm (9 : ℝ)]
        have h9 : (t ^ 2)⁻¹ ≤ 9 := by
          rw [inv_le_comm₀ (by positivity) (by norm_num)]
          nlinarith
        exact mul_le_mul_of_nonneg_left h9 (div_nonneg (sq_nonneg _) hpos.le)
    _ = ENNReal.ofReal 9 * ∫⁻ u in U, ENNReal.ofReal (ν u ^ 2 / (1 - ‖u‖ ^ 2)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal 9 * ∫⁻ u in unitDisc ∩ ball ζ r, ENNReal.ofReal (ν u ^ 2 / (1 - ‖u‖ ^ 2)) := by
        gcongr <;> exact lintegral_mono_set hUsub
    _ = ENNReal.ofReal 9 * ((volume.restrict unitDisc).withDensity fun w =>
          ENNReal.ofReal (ν w ^ 2 / (1 - ‖w‖ ^ 2))) (unitDisc ∩ ball ζ r) := by
        rw [withDensity_apply _ hBm, Measure.restrict_restrict hBm,
          inter_eq_left.mpr inter_subset_left]
    _ ≤ ENNReal.ofReal 9 * (C' * ENNReal.ofReal r) := by
        gcongr

/-- Lane C helper: `|μ_e(h)|` read off on `𝔻` through the Cayley map. -/
theorem s0c_cd_root (f : ℂ → ℂ) (z : ℂ) :
    _root_.complexDilatation f z = LiZhongQC.complexDilatation f z := rfl

/-- Lane C helper (C6 core): the construction of C6 for any class `P` of boundary maps that
contains the normalizations `e^{is} k(M_a z)` and whose real conjugates satisfy the conclusions of
C1 and C3. Also returns the boundary map `φ` of `D` and the relation `|μ_E(w)| = |μ_D(1/w̄)|`. -/
theorem s0c_ext_core {k : ℂ → ℂ} (P : (ℂ → ℂ) → Prop) (hkc : IsCircleHomeo k)
    (hPk : ∀ (s : ℝ) (a : ℂ), a ∈ unitDisc → P fun z => exp (s * I) * k (diskMobius 0 a z))
    (hPH : ∀ (ψ : ℂ → ℂ) (H : ℝ → ℝ), P ψ → ψ 1 = 1 →
      (∀ t : ℝ, H t = (VanishingCarleson.cayleyInv (ψ (VanishingCarleson.cayley t))).re) →
      (∀ ζ : Circle, ((VanishingCarleson.cayleyConj H ζ : Circle) : ℂ) = ψ ζ) ∧ StrictMono H ∧
        Continuous H ∧ Function.Surjective H ∧
        VanishingCarleson.IsCarlesonFn
          (fun x y => ‖_root_.complexDilatation (VanishingCarleson.douadyEarle H) (x + y * I)‖) ∧
        ∃ kH : ℝ, kH < 1 ∧ ∀ z : ℂ, 0 < z.im →
          ‖_root_.complexDilatation (VanishingCarleson.douadyEarle H) z‖ ≤ kH) :
    ∃ (s t : ℝ) (a : ℂ), ‖a‖ < 1 ∧ ∃ (E : ℂ → ℂ) (K₁ k₀ C : ℝ),
      IsKQC E unitDiscExterior K₁ ∧ E '' unitDiscExterior = unitDiscExterior ∧
      Tendsto E (cocompact ℂ) (cocompact ℂ) ∧
      (∀ ξ ∈ sphere (0 : ℂ) 1,
        Tendsto E (𝓝[unitDiscExterior] ξ) (𝓝 (exp (s * I) * k (diskMobius t a ξ)))) ∧
      k₀ < 1 ∧ (∀ w ∈ unitDiscExterior, ‖LiZhongQC.complexDilatation E w‖ ≤ k₀) ∧
      (0 ≤ C ∧ ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
        ∫⁻ w in unitDiscExterior ∩ ball ζ r,
            ENNReal.ofReal (‖LiZhongQC.complexDilatation E w‖ ^ 2 / (‖w‖ ^ 2 - 1)) ≤
          ENNReal.ofReal (C * r)) ∧
      ∃ φ : Circle → Circle, Function.Bijective φ ∧ Continuous φ ∧ HasIncreasingLift φ ∧
        (∀ ζ : Circle, (φ ζ : ℂ) = exp (s * I) * k (diskMobius t a ζ)) ∧
        exp (s * I) * k (diskMobius t a 1) = 1 ∧
        ∀ w ∈ unitDiscExterior, ‖LiZhongQC.complexDilatation E w‖ =
          ‖LiZhongQC.complexDilatation (extension φ) (conj w)⁻¹‖ := by
  obtain ⟨φ₀, hφ₀b, hφ₀c, hφ₀l, hφ₀v⟩ := s07_de_circleMap hkc
  obtain ⟨himg₀, -, -, -⟩ := s0c_de_disk φ₀ hφ₀b hφ₀c
  obtain ⟨p, hp, hp0⟩ : ∃ p ∈ unitDisc, extension φ₀ p = 0 := by
    have : (0 : ℂ) ∈ extension φ₀ '' unitDisc := by rw [himg₀]; exact mem_ball_self one_pos
    exact this
  have hp1 : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
  have hnp : ‖-p‖ < 1 := by rwa [norm_neg]
  -- the Möbius map `A = g_{-p}`, `A 0 = p`
  have hA0 : diskAut (-p) 0 = p := by rw [diskAut_zero, neg_neg]
  have hAp : IsDiskAutPlus (diskAut (-p)) := ⟨1, -p, norm_one, hnp, fun w => (one_mul _).symm⟩
  have hAd : IsDiskAut (diskAut (-p)) := Or.inl hAp
  obtain ⟨ψA, hψA⟩ : ∃ ψA : Circle → Circle, ψA = diskAutToCircle _ hAd := ⟨_, rfl⟩
  have hψAv : ∀ ζ : Circle, diskAut (-p) (ζ : ℂ) = (ψA ζ : ℂ) := fun ζ => by
    rw [hψA]; exact diskAutToCircle_coe _ hAd ζ
  have hψAb : Function.Bijective ψA := by rw [hψA]; exact bijective_diskAutToCircle_of_isDiskAut _ hAd
  have hψAc : Continuous ψA := by rw [hψA]; exact continuous_diskAutToCircle _ hAd
  have hψAl : HasIncreasingLift ψA :=
    CircleLift.hasIncreasingLift_of_isDiskAutPlus hAp ψA (fun ζ => (hψAv ζ).symm)
  have hAM : ∀ z, diskAut (-p) z = diskMobius 0 (-p) z := fun z => by
    simp [diskAut, diskMobius, Complex.star_def]
  -- the rotation `c = e^{is}` with `c k(A 1) = 1`
  have hkA1 : k (diskAut (-p) 1) = (φ₀ (ψA 1) : ℂ) := by
    rw [hφ₀v, ← hψAv, Circle.coe_one]
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : ℂ, w₁ = k (diskAut (-p) 1) := ⟨_, rfl⟩
  have hw₁n : ‖w₁‖ = 1 := by rw [hw₁, hkA1, Circle.norm_coe]
  set s : ℝ := -arg w₁ with hs
  set c : ℂ := exp (s * I) with hcdef
  have hc1 : ‖c‖ = 1 := Complex.norm_exp_ofReal_mul_I s
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  have hcw : c * w₁ = 1 := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w₁]
    rw [hw₁n, ofReal_one, one_mul, hcdef, ← Complex.exp_add,
      show ((s : ℂ) * I + (arg w₁ : ℂ) * I) = 0 by rw [hs]; push_cast; ring, Complex.exp_zero]
  have hgp : IsDiskAutPlus (fun w => c * w) :=
    ⟨c, 0, hc1, by norm_num, fun w => by rw [diskAut_zero_left]⟩
  have hgd : IsDiskAut (fun w => c * w) := Or.inl hgp
  obtain ⟨ψg, hψg⟩ : ∃ ψg : Circle → Circle, ψg = diskAutToCircle _ hgd := ⟨_, rfl⟩
  have hψgv : ∀ ζ : Circle, c * (ζ : ℂ) = (ψg ζ : ℂ) := fun ζ => by
    rw [hψg]; exact diskAutToCircle_coe _ hgd ζ
  have hψgb : Function.Bijective ψg := by rw [hψg]; exact bijective_diskAutToCircle_of_isDiskAut _ hgd
  have hψgc : Continuous ψg := by rw [hψg]; exact continuous_diskAutToCircle _ hgd
  have hψgl : HasIncreasingLift ψg :=
    CircleLift.hasIncreasingLift_of_isDiskAutPlus hgp ψg (fun ζ => (hψgv ζ).symm)
  -- the normalized boundary map `φ = ψ` and its Douady–Earle extension `D`
  set φ : Circle → Circle := ψg ∘ φ₀ ∘ ψA with hφdef
  have hφb : Function.Bijective φ := hψgb.comp (hφ₀b.comp hψAb)
  have hφc : Continuous φ := hψgc.comp (hφ₀c.comp hψAc)
  have hφl : HasIncreasingLift φ :=
    CircleLift.hasIncreasingLift_comp hψgl (CircleLift.hasIncreasingLift_comp hφ₀l hψAl)
  set ψ : ℂ → ℂ := fun z => exp (s * I) * k (diskMobius 0 (-p) z) with hψdef
  have hφv : ∀ ζ : Circle, (φ ζ : ℂ) = ψ ζ := fun ζ => by
    show (ψg (φ₀ (ψA ζ)) : ℂ) = exp (s * I) * k (diskMobius 0 (-p) ζ)
    rw [← hψgv, hφ₀v, ← hψAv, hAM]
  have hψ : P ψ := hPk s (-p) (mem_ball_zero_iff.mpr hnp)
  have hψ1 : ψ 1 = 1 := by
    show exp (s * I) * k (diskMobius 0 (-p) 1) = 1
    rw [← hAM, ← hw₁]
    exact hcw
  set D : ℂ → ℂ := extension φ with hDdef
  have hD0 : D 0 = 0 := by
    have := extension_naturality φ₀ (fun w => c * w) (diskAut (-p)) ψg ψA hgd hAd hψgv hψAv
      hφ₀b hφ₀c hψgb hψAb 0 (by simp)
    rw [hDdef, hφdef, this, hA0, hp0, mul_zero]
  -- the real conjugate `H` (C1) and the uniform VC theorem (C3)
  set H : ℝ → ℝ := fun t => (VanishingCarleson.cayleyInv (ψ (VanishingCarleson.cayley t))).re
    with hHdef
  obtain ⟨hHconj, hHm, hHc, hHs, hCar, kH, hkH1, hkHb⟩ := hPH ψ H hψ hψ1 fun t => rfl
  have hφeq : VanishingCarleson.cayleyConj H = φ :=
    funext fun ζ => Subtype.ext ((hHconj ζ).trans (hφv ζ).symm)
  set ν : ℂ → ℝ := fun w => ‖LiZhongQC.complexDilatation D w‖ with hνdef
  have hνc : ∀ z : ℂ, 0 < z.im →
      ν (LiZhongQC.cayley z) = ‖_root_.complexDilatation (VanishingCarleson.douadyEarle H) z‖ := by
    intro z hz
    rw [VanishingCarleson.norm_complexDilatation_douadyEarle H hHm hHc hHs z hz, hφeq]
    rfl
  have hνm : Measurable ν := by
    have h1 := measurable_fderiv_apply_const ℝ D (1 : ℂ)
    have h2 := measurable_fderiv_apply_const ℝ D I
    simp only [hνdef, LiZhongQC.complexDilatation, dz, dzbar]
    exact (((h1.add (h2.const_mul I)).div_const 2).div ((h1.sub (h2.const_mul I)).div_const 2)).norm
  have hCν : VanishingCarleson.IsCarlesonFn fun x y => ν (VanishingCarleson.cayley (x + y * I)) := by
    refine s0c_isCarlesonFn_of_le _ _ 1 (fun x y hy => ?_) hCar
    have hy' : 0 < ((x : ℂ) + y * I).im := by simpa using hy
    rw [one_mul, abs_of_nonneg (norm_nonneg _)]
    exact (hνc _ hy').le
  obtain ⟨C', hC'top, hC'⟩ := s0c_carleson_cayley hνm (fun w => norm_nonneg _) hCν
  -- the bound `‖μ_D‖ ≤ k₁ < 1` on `𝔻` and C4
  set k₁ : ℝ := max kH 0 with hk₁
  have hk₁1 : k₁ < 1 := max_lt hkH1 one_pos
  have hbD : ∀ w ∈ unitDisc, ν w ≤ k₁ := by
    intro w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have him : 0 < (LiZhongQC.cayleyInv w).im := cayleyInv_mem_upperHalf hw1
    rw [← cayley_cayleyInv hw1, hνc _ him]
    exact (hkHb _ him).trans (le_max_left _ _)
  obtain ⟨hDK, hDimg⟩ := s0c_de_isKQC φ hφb hφc hφl (le_max_right _ _) hk₁1 hbD
  obtain ⟨-, hDinj, hDcont, -⟩ := s0c_de_disk φ hφb hφc
  obtain ⟨-, hDcl, -⟩ := extension_isHomeomorphOn φ hφb hφc
  have hDan := extension_analyticOn_disk φ hφb hφc
  have hDne : ∀ u ∈ unitDisc, u ≠ 0 → D u ≠ 0 := fun u hu hu0 hDu =>
    hu0 (hDinj hu (mem_ball_self one_pos) (hDu.trans hD0.symm))
  have hDmem : ∀ u ∈ unitDisc, D u ∈ unitDisc := fun u hu => hDimg ▸ mem_image_of_mem D hu
  -- the reflected map `E = ι ∘ D ∘ ι`
  set E : ℂ → ℂ := fun z => (conj (D (conj z)⁻¹))⁻¹ with hEdef
  obtain ⟨hEK, -⟩ := abR_exterior hDK hDimg hD0
  have hEdil : ∀ w ∈ unitDiscExterior, ‖LiZhongQC.complexDilatation E w‖ = ν (conj w)⁻¹ := by
    intro w hw
    obtain ⟨hu, hu0⟩ := s0c_iota_disk hw
    exact s0c_ext_dil hw (hDan.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hu))
      (hDne _ hu hu0)
  refine ⟨s, 0, -p, hnp, E, (1 + k₁) / (1 - k₁), k₁, 9 * C'.toReal, hEK, ?_, ?_, ?_, hk₁1,
    ?_, ⟨by positivity, ?_⟩, φ, hφb, hφc, hφl, fun ζ => hφv ζ, hψ1, hEdil⟩
  · -- `E(𝔻*) = 𝔻*`
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hu, hu0⟩ := s0c_iota_disk hz
      exact s0c_iota_ext (hDmem _ hu) (hDne _ hu hu0)
    · intro hw
      obtain ⟨hv, hv0⟩ := s0c_iota_disk hw
      rw [← hDimg] at hv
      obtain ⟨u, hu, hDu⟩ := hv
      have hu0 : u ≠ 0 := fun h => hv0 (by rw [← hDu, h]; exact hD0)
      refine ⟨(conj u)⁻¹, s0c_iota_ext hu hu0, ?_⟩
      show (conj (D (conj (conj u)⁻¹)⁻¹))⁻¹ = w
      rw [abR_t_conj_inv_inv]
      change (conj (extension φ u))⁻¹ = w
      rw [hDu, abR_t_conj_inv_inv]
  · -- `E → ∞` at `∞`
    have hev : ∀ᶠ z in cocompact ℂ, 1 < ‖z‖ := by
      rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_norm_cobounded_atTop.eventually_gt_atTop 1
    have hι0 : Tendsto (fun z : ℂ => (conj z)⁻¹) (cocompact ℂ) (𝓝[unitDisc] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, hev.mono fun z hz => (s0c_iota_disk hz).1⟩
      rw [← Metric.cobounded_eq_cocompact]
      have h := (Complex.continuous_conj.tendsto 0).comp (tendsto_inv₀_cobounded (α := ℂ))
      rw [map_zero] at h
      refine h.congr fun z => ?_
      simp [Function.comp, map_inv₀]
    have hD2 : Tendsto (fun z : ℂ => D (conj z)⁻¹) (cocompact ℂ) (𝓝 0) := by
      have hc : ContinuousWithinAt D unitDisc 0 :=
        (hDcl 0 (mem_closedBall_self zero_le_one)).mono ball_subset_closedBall
      rw [← hD0]
      exact hc.tendsto.comp hι0
    have hn : Tendsto (fun z : ℂ => ‖D (conj z)⁻¹‖) (cocompact ℂ) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨by simpa using hD2.norm, hev.mono fun z hz => ?_⟩
      obtain ⟨hu, hu0⟩ := s0c_iota_disk hz
      exact norm_pos_iff.mpr (hDne _ hu hu0)
    rw [← Metric.cobounded_eq_cocompact (α := ℂ)] at hn ⊢
    refine tendsto_norm_atTop_iff_cobounded.mp ((tendsto_inv_nhdsGT_zero.comp hn).congr fun z => ?_)
    simp [hEdef, Function.comp, norm_inv]
  · -- boundary values
    intro ξ hξ
    have hξ1 : ‖ξ‖ = 1 := mem_sphere_zero_iff_norm.mp hξ
    have hξ0 : conj ξ ≠ 0 := (map_ne_zero _).2 (norm_ne_zero_iff.mp (by rw [hξ1]; exact one_ne_zero))
    have hξm : ξ ∈ Submonoid.unitSphere ℂ := hξ
    have hDb : D ξ = ((φ (⟨ξ, hξm⟩ : Circle) : Circle) : ℂ) :=
      extension_eq_boundary φ (⟨ξ, hξm⟩ : Circle)
    have hDξ : D ξ = exp (s * I) * k (diskMobius 0 (-p) ξ) := hDb.trans (hφv (⟨ξ, hξm⟩ : Circle))
    have hDξ1 : ‖D ξ‖ = 1 := by rw [hDb, Circle.norm_coe]
    have hι : Tendsto (fun z : ℂ => (conj z)⁻¹) (𝓝[unitDiscExterior] ξ) (𝓝[closedBall 0 1] ξ) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun z hz =>
        ball_subset_closedBall (s0c_iota_disk hz).1⟩
      have h : Tendsto (fun z : ℂ => (conj z)⁻¹) (𝓝 ξ) (𝓝 (conj ξ)⁻¹) :=
        ((Complex.continuous_conj.continuousAt (x := ξ)).inv₀ hξ0).tendsto
      rw [abR_t_inv_conj_of_norm_one hξ1] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hD : Tendsto (fun z : ℂ => D (conj z)⁻¹) (𝓝[unitDiscExterior] ξ) (𝓝 (D ξ)) :=
      (hDcl ξ (mem_closedBall_zero_iff.mpr hξ1.le)).tendsto.comp hι
    have hDξ0 : conj (D ξ) ≠ 0 :=
      (map_ne_zero _).2 (norm_ne_zero_iff.mp (by rw [hDξ1]; exact one_ne_zero))
    have hout : Tendsto (fun v : ℂ => (conj v)⁻¹) (𝓝 (D ξ)) (𝓝 (conj (D ξ))⁻¹) :=
      ((Complex.continuous_conj.continuousAt (x := D ξ)).inv₀ hDξ0).tendsto
    rw [abR_t_inv_conj_of_norm_one hDξ1] at hout
    rw [← hDξ]
    exact hout.comp hD
  · -- dilatation bound
    intro w hw
    rw [hEdil w hw]
    exact hbD _ (s0c_iota_disk hw).1
  · -- box bound
    intro ζ hζ r hr hr2
    calc ∫⁻ w in unitDiscExterior ∩ ball ζ r,
            ENNReal.ofReal (‖LiZhongQC.complexDilatation E w‖ ^ 2 / (‖w‖ ^ 2 - 1))
        ≤ ENNReal.ofReal 9 * (C' * ENNReal.ofReal r) := s0c_ext_box hEdil hζ hr hr2 (hC' ζ hζ r hr hr2)
      _ = ENNReal.ofReal (9 * C'.toReal * r) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_toReal hC'top, mul_assoc]

/-- C6 (output for lanes U and A, B5 ⇐). -/
theorem s0c_ext_B {k : ℂ → ℂ} (hk : IsStronglyQS k) :
    ∃ (s t : ℝ) (a : ℂ), ‖a‖ < 1 ∧ ∃ (E : ℂ → ℂ) (K₁ k₀ C : ℝ),
      IsKQC E unitDiscExterior K₁ ∧ E '' unitDiscExterior = unitDiscExterior ∧
      Tendsto E (cocompact ℂ) (cocompact ℂ) ∧
      (∀ ξ ∈ sphere (0 : ℂ) 1,
        Tendsto E (𝓝[unitDiscExterior] ξ) (𝓝 (exp (s * I) * k (diskMobius t a ξ)))) ∧
      k₀ < 1 ∧ (∀ w ∈ unitDiscExterior, ‖LiZhongQC.complexDilatation E w‖ ≤ k₀) ∧
      0 ≤ C ∧ ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
        ∫⁻ w in unitDiscExterior ∩ ball ζ r,
            ENNReal.ofReal (‖LiZhongQC.complexDilatation E w‖ ^ 2 / (‖w‖ ^ 2 - 1)) ≤
          ENNReal.ofReal (C * r) := by
  obtain ⟨s, t, a, ha, E, K₁, k₀, C, h1, h2, h3, h4, h5, h6, ⟨h7, h8⟩, -⟩ :=
    s0c_ext_core IsStronglyQS hk.choose_spec.1
      (fun s a ha => by
        have e : (fun z => exp (s * I) * k (diskMobius 0 a z)) =
            diskMobius s 0 ∘ (k ∘ diskMobius 0 a) := by
          funext z
          simp [diskMobius]
        rw [e]
        exact sqs_circle_comp _ _ (sqs_circle_mobius s 0 (mem_ball_self one_pos))
          (sqs_circle_comp _ _ hk (sqs_circle_mobius 0 a ha)))
      (fun ψ H hψ hψ1 hH => by
        obtain ⟨-, hHconj, hHm, hHs, hHac, hHw⟩ := s0c_cay_sqs hψ hψ1 hH
        obtain ⟨hCar, hkH, -⟩ := s0c_de_uniform H hHm hHac hHs hHw
        exact ⟨hHconj, hHm, hHac.1, hHs, hCar, hkH⟩)
  exact ⟨s, t, a, ha, E, K₁, k₀, C, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- Lane C helper (C6v): one Cayley picture. For a normalized strongly symmetric boundary map,
the disk boxes of `|μ_D|²/(1-|w|²)` (`D` the Douady–Earle extension) at `ζ` with `‖ζ - 1‖ ≥ 1`
are `o(r)` uniformly (C1v + VC `main_theorem` + C5v'). -/
theorem s0c_vbox_half {ψ : ℂ → ℂ} (hψ : IsStronglySymmetric ψ) (hψ1 : ψ 1 = 1)
    {φ : Circle → Circle} (hφv : ∀ ζ : Circle, (φ ζ : ℂ) = ψ ζ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ ζ ∈ sphere (0 : ℂ) 1, 1 ≤ ‖ζ - 1‖ →
      ∀ r : ℝ, 0 < r → r < δ →
        ((volume.restrict unitDisc).withDensity fun w =>
          ENNReal.ofReal (‖LiZhongQC.complexDilatation (extension φ) w‖ ^ 2 / (1 - ‖w‖ ^ 2)))
            (unitDisc ∩ ball ζ r) ≤ ENNReal.ofReal (ε * r) := by
  set H : ℝ → ℝ := fun t => (VanishingCarleson.cayleyInv (ψ (VanishingCarleson.cayley t))).re
    with hHdef
  obtain ⟨-, hHconj, hSS⟩ := s0c_cay_ss hψ hψ1 (H := H) fun t => rfl
  have hHm : StrictMono H := hSS.1
  have hHc : Continuous H := hSS.2.2.1.1
  have hHs : Function.Surjective H := hSS.2.1
  have hφeq : VanishingCarleson.cayleyConj H = φ :=
    funext fun ζ => Subtype.ext ((hHconj ζ).trans (hφv ζ).symm)
  obtain ⟨hVC, -, -⟩ := VanishingCarleson.main_theorem H hSS
  set ν : ℂ → ℝ := fun w => ‖LiZhongQC.complexDilatation (extension φ) w‖ with hνdef
  have hνc : ∀ z : ℂ, 0 < z.im →
      ν (LiZhongQC.cayley z) = ‖_root_.complexDilatation (VanishingCarleson.douadyEarle H) z‖ := by
    intro z hz
    rw [VanishingCarleson.norm_complexDilatation_douadyEarle H hHm hHc hHs z hz, hφeq]
    rfl
  have hνm : Measurable ν := by
    have h1 := measurable_fderiv_apply_const ℝ (extension φ) (1 : ℂ)
    have h2 := measurable_fderiv_apply_const ℝ (extension φ) I
    simp only [hνdef, LiZhongQC.complexDilatation, dz, dzbar]
    exact (((h1.add (h2.const_mul I)).div_const 2).div ((h1.sub (h2.const_mul I)).div_const 2)).norm
  have hCν : VanishingCarleson.IsVanishingCarleson fun x y =>
      ν (VanishingCarleson.cayley (x + y * I)) := by
    refine VanishingCarleson.isVanishingCarleson_of_le _ _ 1 zero_le_one (fun x y hy => ?_) hVC
    have hy' : 0 < ((x : ℂ) + y * I).im := by simpa using hy
    rw [one_mul, abs_of_nonneg (norm_nonneg _)]
    exact (hνc _ hy').le
  exact (s0c_vcarleson_cayley hνm (fun w => norm_nonneg _) hCν).2

/-- Lane C helper (C6v): both Cayley pictures. The disk boxes of `|μ_D|²/(1-|w|²)` are `o(r)`
uniformly in `ζ ∈ ∂𝔻`; boxes near `1` are moved to `-1` by the rotated normalization
`ψ̃(z) = c ψ(-z)`, `D̃(w) = c D(-w)` (conformal naturality). -/
theorem s0c_vbox {ψ : ℂ → ℂ} (hψ : IsStronglySymmetric ψ) (hψ1 : ψ 1 = 1)
    {φ : Circle → Circle} (hφb : Function.Bijective φ) (hφc : Continuous φ)
    (hφv : ∀ ζ : Circle, (φ ζ : ℂ) = ψ ζ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < δ →
        ((volume.restrict unitDisc).withDensity fun w =>
          ENNReal.ofReal (‖LiZhongQC.complexDilatation (extension φ) w‖ ^ 2 / (1 - ‖w‖ ^ 2)))
            (unitDisc ∩ ball ζ r) ≤ ENNReal.ofReal (ε * r) := by
  -- the rotation `c = e^{is}` with `c ψ(-1) = 1`
  have hm1 : (-1 : ℂ) ∈ Submonoid.unitSphere ℂ := mem_sphere_zero_iff_norm.2 (by simp)
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : ℂ, w₁ = ψ (-1) := ⟨_, rfl⟩
  have hw₁n : ‖w₁‖ = 1 := by
    have h := congrArg norm (hφv ⟨-1, hm1⟩)
    rw [Circle.norm_coe] at h
    rw [hw₁]
    exact h.symm
  set s : ℝ := -arg w₁ with hs
  set c : ℂ := exp (s * I) with hcdef
  have hc1 : ‖c‖ = 1 := Complex.norm_exp_ofReal_mul_I s
  have hcw : c * w₁ = 1 := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w₁]
    rw [hw₁n, ofReal_one, one_mul, hcdef, ← Complex.exp_add,
      show ((s : ℂ) * I + (arg w₁ : ℂ) * I) = 0 by rw [hs]; push_cast; ring, Complex.exp_zero]
  have hgp : IsDiskAutPlus (fun w => c * w) :=
    ⟨c, 0, hc1, by norm_num, fun w => by rw [diskAut_zero_left]⟩
  have hgd : IsDiskAut (fun w => c * w) := Or.inl hgp
  obtain ⟨ψg, hψg⟩ : ∃ ψg : Circle → Circle, ψg = diskAutToCircle _ hgd := ⟨_, rfl⟩
  have hψgv : ∀ ζ : Circle, c * (ζ : ℂ) = (ψg ζ : ℂ) := fun ζ => by
    rw [hψg]; exact diskAutToCircle_coe _ hgd ζ
  have hψgb : Function.Bijective ψg := by
    rw [hψg]; exact bijective_diskAutToCircle_of_isDiskAut _ hgd
  have hψgc : Continuous ψg := by rw [hψg]; exact continuous_diskAutToCircle _ hgd
  have hRp : IsDiskAutPlus (fun w => (-1 : ℂ) * w) :=
    ⟨-1, 0, by simp, by norm_num, fun w => by rw [diskAut_zero_left]⟩
  have hRd : IsDiskAut (fun w => (-1 : ℂ) * w) := Or.inl hRp
  obtain ⟨ψR, hψR⟩ : ∃ ψR : Circle → Circle, ψR = diskAutToCircle _ hRd := ⟨_, rfl⟩
  have hψRv : ∀ ζ : Circle, (-1 : ℂ) * (ζ : ℂ) = (ψR ζ : ℂ) := fun ζ => by
    rw [hψR]; exact diskAutToCircle_coe _ hRd ζ
  have hψRb : Function.Bijective ψR := by
    rw [hψR]; exact bijective_diskAutToCircle_of_isDiskAut _ hRd
  have hψRc : Continuous ψR := by rw [hψR]; exact continuous_diskAutToCircle _ hRd
  -- the rotated picture
  set φ' : Circle → Circle := ψg ∘ φ ∘ ψR with hφ'def
  have hφ'b : Function.Bijective φ' := hψgb.comp (hφb.comp hψRb)
  set ψ' : ℂ → ℂ := fun z => c * ψ ((-1 : ℂ) * z) with hψ'def
  have hφ'v : ∀ ζ : Circle, (φ' ζ : ℂ) = ψ' ζ := fun ζ => by
    show (ψg (φ (ψR ζ)) : ℂ) = c * ψ ((-1 : ℂ) * ζ)
    rw [← hψgv, hφv, ← hψRv]
  have hψ' : IsStronglySymmetric ψ' := by
    have e : ψ' = diskMobius s 0 ∘ (ψ ∘ diskMobius π 0) := by
      funext z
      simp [hψ'def, hcdef, diskMobius, Complex.exp_pi_mul_I]
    rw [e]
    exact ss_circle_comp _ _ (ss_circle_mobius s 0 (mem_ball_self one_pos))
      (ss_circle_comp _ _ hψ (ss_circle_mobius π 0 (mem_ball_self one_pos)))
  have hψ'1 : ψ' 1 = 1 := by
    show c * ψ ((-1 : ℂ) * 1) = 1
    rw [mul_one, ← hw₁]
    exact hcw
  -- `|μ_{D̃}(w)| = |μ_D(-w)|` on `𝔻`
  have hDan := extension_analyticOn_disk φ hφb hφc
  have hdil : ∀ w ∈ unitDisc, ‖LiZhongQC.complexDilatation (extension φ') w‖ =
      ‖LiZhongQC.complexDilatation (extension φ) (-w)‖ := by
    intro w hw
    have hev : extension φ' =ᶠ[𝓝 w]
        (fun v => c * v) ∘ (extension φ ∘ fun v => (-1 : ℂ) * v) := by
      filter_upwards [isOpen_ball.mem_nhds hw] with v hv
      exact extension_naturality φ (fun w => c * w) (fun w => (-1 : ℂ) * w) ψg ψR hgd hRd hψgv
        hψRv hφb hφc hψgb hψRb v (mem_ball_zero_iff.mp hv).le
    have hmw : -w ∈ unitDisc :=
      mem_ball_zero_iff.mpr (by rw [norm_neg]; exact mem_ball_zero_iff.mp hw)
    have hDd : DifferentiableAt ℝ (extension φ) ((-1 : ℂ) * w) := by
      rw [neg_one_mul]
      exact hDan.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hmw)
    have hRdiff : DifferentiableAt ℂ (fun v : ℂ => (-1 : ℂ) * v) w :=
      (differentiableAt_id.const_mul _)
    have hRder : deriv (fun v : ℂ => (-1 : ℂ) * v) w = -1 := by
      simpa using (hasDerivAt_id w).const_mul (-1 : ℂ) |>.deriv
    have hcomp : DifferentiableAt ℝ (extension φ ∘ fun v => (-1 : ℂ) * v) w :=
      hDd.comp w (hRdiff.restrictScalars ℝ)
    have e1 : LiZhongQC.complexDilatation (extension φ') w =
        LiZhongQC.complexDilatation ((fun v => c * v) ∘ (extension φ ∘ fun v => (-1 : ℂ) * v)) w := by
      unfold LiZhongQC.complexDilatation dz dzbar
      rw [hev.fderiv_eq]
    have hcd : DifferentiableAt ℂ (fun v : ℂ => c * v) ((extension φ ∘ fun v => (-1 : ℂ) * v) w) :=
      differentiableAt_id.const_mul _
    have hcder : deriv (fun v : ℂ => c * v) ((extension φ ∘ fun v => (-1 : ℂ) * v) w) ≠ 0 := by
      rw [show deriv (fun v : ℂ => c * v) ((extension φ ∘ fun v => (-1 : ℂ) * v) w) = c by
        simp]
      exact Complex.exp_ne_zero _
    rw [e1, LiZhongQC.complexDilatation_comp_conformal_left hcomp hcd hcder,
      LiZhongQC.complexDilatation_comp_conformal_right hRdiff (by rw [hRder]; norm_num) hDd,
      norm_mul, hRder, neg_one_mul]
    simp
  -- box symmetry
  have hbox : ∀ ζ : ℂ, ∀ r : ℝ,
      ((volume.restrict unitDisc).withDensity fun w =>
        ENNReal.ofReal (‖LiZhongQC.complexDilatation (extension φ) w‖ ^ 2 / (1 - ‖w‖ ^ 2)))
          (unitDisc ∩ ball ζ r) =
      ((volume.restrict unitDisc).withDensity fun w =>
        ENNReal.ofReal (‖LiZhongQC.complexDilatation (extension φ') w‖ ^ 2 / (1 - ‖w‖ ^ 2)))
          (unitDisc ∩ ball (-ζ) r) := by
    intro ζ r
    have hm1 : MeasurableSet (unitDisc ∩ ball ζ r) := measurableSet_ball.inter measurableSet_ball
    have hm2 : MeasurableSet (unitDisc ∩ ball (-ζ) r) :=
      measurableSet_ball.inter measurableSet_ball
    rw [withDensity_apply _ hm1, withDensity_apply _ hm2, Measure.restrict_restrict hm1,
      Measure.restrict_restrict hm2, inter_eq_left.mpr inter_subset_left,
      inter_eq_left.mpr inter_subset_left]
    have hpre : (fun w : ℂ => -w) ⁻¹' (unitDisc ∩ ball (-ζ) r) = unitDisc ∩ ball ζ r := by
      ext w
      simp only [unitDisc, mem_preimage, mem_inter_iff, mem_ball, dist_neg_neg, dist_zero_right,
        norm_neg]
    have hfm : Measurable fun w : ℂ =>
        ENNReal.ofReal (‖LiZhongQC.complexDilatation (extension φ') w‖ ^ 2 / (1 - ‖w‖ ^ 2)) := by
      have h1 := measurable_fderiv_apply_const ℝ (extension φ') (1 : ℂ)
      have h2 := measurable_fderiv_apply_const ℝ (extension φ') I
      refine ENNReal.measurable_ofReal.comp (Measurable.div ?_ ?_)
      · simp only [LiZhongQC.complexDilatation, dz, dzbar]
        exact ((((h1.add (h2.const_mul I)).div_const 2).div
          ((h1.sub (h2.const_mul I)).div_const 2)).norm).pow_const 2
      · exact measurable_const.sub (measurable_norm.pow_const 2)
    rw [← (Measure.measurePreserving_neg (volume : Measure ℂ)).setLIntegral_comp_preimage hm2 hfm,
      hpre]
    refine setLIntegral_congr_fun hm1 fun w hw => ?_
    simp only [norm_neg]
    rw [hdil (-w) (mem_ball_zero_iff.mpr (by rw [norm_neg]; exact mem_ball_zero_iff.mp hw.1)),
      neg_neg]
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := s0c_vbox_half hψ hψ1 hφv ε hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := s0c_vbox_half hψ' hψ'1 hφ'v ε hε
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun ζ hζ r hr hrδ => ?_⟩
  by_cases hζ1 : 1 ≤ ‖ζ - 1‖
  · exact h₁ ζ hζ hζ1 r hr (hrδ.trans_le (min_le_left _ _))
  · rw [hbox ζ r]
    have hζn : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
    have h2 : (2 : ℝ) ≤ ‖ζ + 1‖ + ‖ζ - 1‖ := by
      have := norm_sub_le (ζ + 1) (ζ - 1)
      rw [show ζ + 1 - (ζ - 1) = 2 by ring] at this
      simpa using this
    have hn : 1 ≤ ‖-ζ - 1‖ := by
      rw [show -ζ - 1 = -(ζ + 1) by ring, norm_neg]
      linarith
    exact h₂ (-ζ) (by rw [mem_sphere_zero_iff_norm, norm_neg]; exact hζn) hn r hr
      (hrδ.trans_le (min_le_right _ _))

/-- C6v (output for lanes U and A, V5 ⇐): as C6 for a strongly symmetric circle map `k`, and in
addition `|μ_E|²/(|w|²-1) dA ∈ CM₀(𝔻*)`: the box ratio tends to `0` uniformly as `r → 0`. -/
theorem s0c_ext_V {k : ℂ → ℂ} (hk : IsStronglySymmetric k) :
    ∃ (s t : ℝ) (a : ℂ), ‖a‖ < 1 ∧ ∃ (E : ℂ → ℂ) (K₁ k₀ C : ℝ),
      IsKQC E unitDiscExterior K₁ ∧ E '' unitDiscExterior = unitDiscExterior ∧
      Tendsto E (cocompact ℂ) (cocompact ℂ) ∧
      (∀ ξ ∈ sphere (0 : ℂ) 1,
        Tendsto E (𝓝[unitDiscExterior] ξ) (𝓝 (exp (s * I) * k (diskMobius t a ξ)))) ∧
      k₀ < 1 ∧ (∀ w ∈ unitDiscExterior, ‖LiZhongQC.complexDilatation E w‖ ≤ k₀) ∧
      (0 ≤ C ∧ ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
        ∫⁻ w in unitDiscExterior ∩ ball ζ r,
            ENNReal.ofReal (‖LiZhongQC.complexDilatation E w‖ ^ 2 / (‖w‖ ^ 2 - 1)) ≤
          ENNReal.ofReal (C * r)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < δ →
        ∫⁻ w in unitDiscExterior ∩ ball ζ r,
            ENNReal.ofReal (‖LiZhongQC.complexDilatation E w‖ ^ 2 / (‖w‖ ^ 2 - 1)) ≤
          ENNReal.ofReal (ε * r) := by
  have hkc : IsCircleHomeo k := by
    obtain ⟨K, u, h1, h2, h3, h4, -⟩ := hk
    exact ⟨K, h1, h2, h3, h4⟩
  have hPk : ∀ (s t : ℝ) (a : ℂ), a ∈ unitDisc →
      IsStronglySymmetric fun z => exp (s * I) * k (diskMobius t a z) := fun s t a ha => by
    have e : (fun z => exp (s * I) * k (diskMobius t a z)) =
        diskMobius s 0 ∘ (k ∘ diskMobius t a) := by
      funext z
      simp [diskMobius]
    rw [e]
    exact ss_circle_comp _ _ (ss_circle_mobius s 0 (mem_ball_self one_pos))
      (ss_circle_comp _ _ hk (ss_circle_mobius t a ha))
  obtain ⟨s, t, a, ha, E, K₁, k₀, C, h1, h2, h3, h4, h5, h6, ⟨h7, h8⟩, φ, hφb, hφc, -, hφv, hψ1,
      hEd⟩ :=
    s0c_ext_core IsStronglySymmetric hkc (fun s a ha => hPk s 0 a ha)
      (fun ψ H hψ hψ1 hH => by
        obtain ⟨-, hHconj, hSS⟩ := s0c_cay_ss hψ hψ1 hH
        obtain ⟨hVC, hkH, -⟩ := VanishingCarleson.main_theorem H hSS
        exact ⟨hHconj, hSS.1, hSS.2.2.1.1, hSS.2.1, hVC.1, hkH⟩)
  refine ⟨s, t, a, ha, E, K₁, k₀, C, h1, h2, h3, h4, h5, h6, ⟨h7, h8⟩, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hV⟩ := s0c_vbox (hPk s t a (mem_ball_zero_iff.mpr ha)) hψ1 hφb hφc hφv
    (ε / 9) (by positivity)
  refine ⟨min δ 2, lt_min hδ two_pos, fun ζ hζ r hr hrδ => ?_⟩
  have hr2 : r < 2 := hrδ.trans_le (min_le_right _ _)
  calc ∫⁻ w in unitDiscExterior ∩ ball ζ r,
          ENNReal.ofReal (‖LiZhongQC.complexDilatation E w‖ ^ 2 / (‖w‖ ^ 2 - 1))
      ≤ ENNReal.ofReal 9 * (ENNReal.ofReal (ε / 9) * ENNReal.ofReal r) :=
        s0c_ext_box (m := fun w => ‖LiZhongQC.complexDilatation E w‖)
          (ν := fun u => ‖LiZhongQC.complexDilatation (extension φ) u‖) hEd hζ hr hr2
          (by rw [← ENNReal.ofReal_mul (by positivity)]
              exact hV ζ hζ r hr (hrδ.trans_le (min_le_left _ _)))
    _ = ENNReal.ofReal (ε * r) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

end W6LaneC


/-- A circle homeomorphism has a two-sided inverse on `∂𝔻`. -/
theorem s07b_circle_inv {h : ℂ → ℂ} (hh : IsCircleHomeo h) :
    ∃ hinv : ℂ → ℂ, ∀ ζ ∈ sphere (0 : ℂ) 1,
      hinv ζ ∈ sphere (0 : ℂ) 1 ∧ h (hinv ζ) = ζ ∧ hinv (h ζ) = ζ := by
  classical
  obtain ⟨φ, hφb, -, -, hφv⟩ := s07_de_circleMap hh
  set e := Equiv.ofBijective φ hφb with hedef
  have hmem : ∀ c : Circle, ((c : Circle) : ℂ) ∈ sphere (0 : ℂ) 1 := fun c => c.2
  refine ⟨fun ζ => if hζ : ζ ∈ sphere (0 : ℂ) 1 then ((e.symm ⟨ζ, hζ⟩ : Circle) : ℂ) else 0,
    fun ζ hζ => ⟨?_, ?_, ?_⟩⟩
  · simp only [hζ, ↓reduceDIte]
    exact hmem _
  · simp only [hζ, ↓reduceDIte]
    rw [← hφv]
    have h1 : φ (e.symm ⟨ζ, hζ⟩) = ⟨ζ, hζ⟩ := e.apply_symm_apply _
    rw [h1]
  · have hhζ : h ζ ∈ sphere (0 : ℂ) 1 := by
      rw [← hφv ⟨ζ, hζ⟩]
      exact hmem _
    simp only [hhζ, ↓reduceDIte]
    have hc : (⟨h ζ, hhζ⟩ : Circle) = φ ⟨ζ, hζ⟩ := Circle.ext (hφv ⟨ζ, hζ⟩).symm
    rw [hc]
    have h2 : e.symm (φ ⟨ζ, hζ⟩) = ⟨ζ, hζ⟩ := e.symm_apply_apply _
    rw [h2]

/-- The inverse of the disk Möbius map `M = diskMobius t a` on `∂𝔻`:
`M⁻¹ = diskMobius (-t) (-(e^{it} a))`. -/
theorem s07b_mob_inv (t : ℝ) {a : ℂ} (ha : ‖a‖ < 1) {y : ℂ} (hy : y ∈ sphere (0 : ℂ) 1) :
    diskMobius t a (diskMobius (-t) (-(exp (t * I) * a)) y) = y := by
  have hy1 : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
  have hEn : ‖exp (t * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I t
  have hEc : conj (exp (t * I)) = (exp (t * I))⁻¹ := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, Complex.exp_neg]
  have hEm : exp (((-t : ℝ) : ℂ) * I) = (exp (t * I))⁻¹ := by
    push_cast
    rw [neg_mul, Complex.exp_neg]
  have hE : exp (t * I) ≠ 0 := exp_ne_zero _
  set E := exp (t * I) with hEdef
  set D : ℂ := 1 + E⁻¹ * conj a * y with hDdef
  have hD : D ≠ 0 := by
    intro h0
    have h1 : E⁻¹ * conj a * y = -1 := by linear_combination h0
    have h2 := congrArg norm h1
    rw [norm_mul, norm_mul, norm_inv, hEn, Complex.norm_conj, hy1, norm_neg] at h2
    norm_num at h2
    linarith
  have hna : (1 : ℂ) - conj a * a ≠ 0 := by
    rw [← Complex.normSq_eq_conj_mul_self]
    intro h0
    have h1 : (Complex.normSq a : ℂ) = 1 := by linear_combination -h0
    have h2 : Complex.normSq a = 1 := by exact_mod_cast h1
    rw [Complex.normSq_eq_norm_sq] at h2
    nlinarith [norm_nonneg a]
  have hq : diskMobius (-t) (-(E * a)) y = E⁻¹ * (y + E * a) / D := by
    unfold diskMobius
    rw [hEm, map_neg, map_mul, hEc, hDdef]
    ring
  have h1 : E⁻¹ * (y + E * a) / D - a = E⁻¹ * y * (1 - conj a * a) / D := by
    rw [eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD, hDdef]
    linear_combination a * inv_mul_cancel₀ hE
  have h2 : 1 - conj a * (E⁻¹ * (y + E * a) / D) = (1 - conj a * a) / D := by
    rw [eq_div_iff hD, sub_mul, one_mul, mul_div_assoc', div_mul_cancel₀ _ hD, hDdef]
    linear_combination (-(conj a * a)) * inv_mul_cancel₀ hE
  rw [hq]
  show E * ((E⁻¹ * (y + E * a) / D - a) / (1 - conj a * (E⁻¹ * (y + E * a) / D))) = y
  rw [h1, h2, div_div_div_cancel_right₀ hD, mul_div_cancel_right₀ _ hna, ← mul_assoc,
    mul_inv_cancel₀ hE, one_mul]

/-- Helper: the disk Möbius map `diskMobius t a` (`‖a‖ < 1`) is a conformal map of `𝔻` onto `𝔻`. -/
theorem s07b_mob_conformal (t : ℝ) {a : ℂ} (ha : ‖a‖ < 1) :
    IsConformalOnto (diskMobius t a) unitDisc unitDisc := by
  have hE : ‖exp (t * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I t
  have hform : ∀ z, diskMobius t a z = exp (t * I) * diskAut a z := fun z => rfl
  have hna : ‖-a‖ < 1 := by rwa [norm_neg]
  refine ⟨fun z hz => ?_, fun z hz w hw hzw => ?_, ?_⟩
  · have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
    rw [show diskMobius t a = fun z => exp (t * I) * diskAut a z from funext hform]
    exact ((diskAut_differentiableAt a z ha hz1).const_mul _).differentiableWithinAt
  · have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
    have hw1 : ‖w‖ ≤ 1 := (mem_ball_zero_iff.mp hw).le
    rw [hform, hform] at hzw
    have h1 : diskAut a z = diskAut a w := mul_left_cancel₀ (exp_ne_zero _) hzw
    have hz' := diskAut_neg_left_inv hna hz1
    have hw' := diskAut_neg_left_inv hna hw1
    rw [neg_neg] at hz' hw'
    rw [← hz', ← hw', h1]
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hform]
      show _ ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff, norm_mul, hE, one_mul]
      exact diskAut_maps_disk_to_disk a z ha (mem_ball_zero_iff.mp hz)
    · intro hw
      have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
      have hv : ‖(exp (t * I))⁻¹ * w‖ < 1 := by
        rw [norm_mul, norm_inv, hE, inv_one, one_mul]
        exact hw1
      refine ⟨diskAut (-a) ((exp (t * I))⁻¹ * w), ?_, ?_⟩
      · exact mem_ball_zero_iff.mpr (diskAut_maps_disk_to_disk (-a) _ hna hv)
      · rw [hform, diskAut_neg_left_inv ha hv.le, ← mul_assoc, mul_inv_cancel₀ (exp_ne_zero _),
          one_mul]

/-- Helper: `f ∘ diskMobius t a` is a conformal map of `𝔻` onto `Ω` when `f` is. -/
theorem s07b_comp_mob_conformal {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (t : ℝ) {a : ℂ} (ha : ‖a‖ < 1) :
    IsConformalOnto (fun z => f (diskMobius t a z)) unitDisc Ω := by
  obtain ⟨hMd, hMi, hMs⟩ := s07b_mob_conformal t ha
  have hMm : MapsTo (diskMobius t a) unitDisc unitDisc := fun z hz =>
    hMs ▸ mem_image_of_mem _ hz
  refine ⟨hf.1.comp hMd hMm, hf.2.1.comp hMi hMm, ?_⟩
  rw [show (fun z => f (diskMobius t a z)) = f ∘ diskMobius t a from rfl, image_comp, hMs,
    hf.2.2]

/-- Helper: the curve of a bounded quasicircle is nonempty (`F 1 ∈ Γ`). -/
theorem s07b_curve_nonempty {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K) :
    ∃ x₀ : ℂ, x₀ ∈ curveOf Ω Ωs := by
  obtain ⟨F, hF, -, h1, h2⟩ := hq
  refine ⟨F 1, ?_⟩
  show F 1 ∉ Ω ∪ Ωs
  rintro (h | h)
  · rw [← h1] at h
    obtain ⟨u, hu, hu1⟩ := h
    have he : u = 1 := hF.2.2.1.2.1 (mem_univ _) (mem_univ _) hu1
    have hu' : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
    rw [he, norm_one] at hu'
    exact lt_irrefl _ hu'
  · rw [← h2] at h
    obtain ⟨u, hu, hu1⟩ := h
    have he : u = 1 := hF.2.2.1.2.1 (mem_univ _) (mem_univ _) hu1
    have hu' : 1 < ‖u‖ := hu
    rw [he, norm_one] at hu'
    exact lt_irrefl _ hu'

/-- Welding under Möbius precomposition and rotation: if `h` is the welding of `(f, g)`, then
`h' = M⁻¹ ∘ h ∘ e^{-is}` (`M = diskMobius t a`) is a circle homeomorphism and the welding of
`(f ∘ M, g ∘ e^{-is})`. -/
theorem s07b_weld_mobius {Ω Ωs : Set ℂ} {f g h : ℂ → ℂ} (hw : IsDiskWelding Ω Ωs f g h)
    (hh : IsCircleHomeo h) (s t : ℝ) {a : ℂ} (ha : ‖a‖ < 1) :
    IsDiskWelding Ω Ωs (fun z => f (diskMobius t a z)) (fun w => g (exp (-(s * I)) * w))
        (fun ζ => diskMobius (-t) (-(exp (t * I) * a)) (h (exp (-(s * I)) * ζ))) ∧
      IsCircleHomeo (fun ζ => diskMobius (-t) (-(exp (t * I) * a)) (h (exp (-(s * I)) * ζ))) := by
  obtain ⟨hf, hg, hgInf, hmaps, hwb⟩ := hw
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hRe : exp (-(s * I)) = exp (((-s : ℝ) : ℂ) * I) := by push_cast; ring_nf
  have hRn : ‖exp (-(s * I))‖ = 1 := by rw [hRe]; exact Complex.norm_exp_ofReal_mul_I _
  have hR0 : exp (-(s * I)) ≠ 0 := exp_ne_zero _
  set R := exp (-(s * I)) with hRdef
  set a' : ℂ := -(exp (t * I) * a) with ha'def
  have ha' : ‖a'‖ < 1 := by
    rw [ha'def, norm_neg, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact ha
  have hrotS : ∀ ζ ∈ sphere (0 : ℂ) 1, R * ζ ∈ sphere (0 : ℂ) 1 := fun ζ hζ => by
    rw [mem_sphere_zero_iff_norm, norm_mul, hRn, one_mul]
    exact mem_sphere_zero_iff_norm.mp hζ
  have hMinvS : ∀ y ∈ sphere (0 : ℂ) 1, diskMobius (-t) a' y ∈ sphere (0 : ℂ) 1 := fun y hy => by
    rw [mem_sphere_zero_iff_norm, show diskMobius (-t) a' y = exp (((-t : ℝ) : ℂ) * I) *
      diskAut a' y from rfl, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact diskAut_norm_eq_one a' y ha' (mem_sphere_zero_iff_norm.mp hy)
  -- the rotation is a conformal self-map of `𝔻*`
  have hrotE : ∀ w ∈ unitDiscExterior, R * w ∈ unitDiscExterior := fun w hw => by
    show 1 < ‖R * w‖
    rw [norm_mul, hRn, one_mul]
    exact hw
  have hrotIm : (fun w => R * w) '' unitDiscExterior = unitDiscExterior := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hrotE v hv
    · intro hw
      refine ⟨R⁻¹ * w, ?_, by
        show R * (R⁻¹ * w) = w
        rw [← mul_assoc, mul_inv_cancel₀ hR0, one_mul]⟩
      show 1 < ‖R⁻¹ * w‖
      rw [norm_mul, norm_inv, hRn, inv_one, one_mul]
      exact hw
  have hMc : ∀ p : ℂ, ‖p‖ ≤ 1 → ContinuousAt (diskMobius t a) p := fun p hp => by
    rw [show diskMobius t a = fun z => exp (t * I) * diskAut a z from rfl]
    exact ((diskAut_differentiableAt a p ha hp).const_mul _).continuousAt
  obtain ⟨-, -, hMs⟩ := s07b_mob_conformal t ha
  have hMm : MapsTo (diskMobius t a) unitDisc unitDisc := fun z hz =>
    hMs ▸ mem_image_of_mem _ hz
  refine ⟨⟨s07b_comp_mob_conformal hf t ha, ⟨?_, ?_, ?_⟩, ?_, fun ζ hζ => hMinvS _ (hmaps (hrotS ζ hζ)),
    fun ζ hζ => ?_⟩, ?_⟩
  · exact hg.1.comp (by fun_prop : DifferentiableOn ℂ (fun w : ℂ => R * w) unitDiscExterior) hrotE
  · exact hg.2.1.comp (fun v _ w _ hvw => mul_left_cancel₀ hR0 hvw) hrotE
  · rw [show (fun w => g (R * w)) = g ∘ fun w => R * w from rfl, image_comp, hrotIm, hg.2.2]
  · exact hgInf.comp (Homeomorph.mulLeft₀ R hR0).isClosedEmbedding.tendsto_cocompact
  · obtain ⟨x, hfx, hgx⟩ := hwb (R * ζ) (hrotS ζ hζ)
    refine ⟨x, ?_, ?_⟩
    · have hy := hmaps (hrotS ζ hζ)
      have hp := hMinvS _ hy
      have hMp : diskMobius t a (diskMobius (-t) a' (h (R * ζ))) = h (R * ζ) :=
        s07b_mob_inv t ha hy
      have hT : Tendsto (diskMobius t a) (𝓝[unitDisc] (diskMobius (-t) a' (h (R * ζ))))
          (𝓝[unitDisc] (h (R * ζ))) := by
        have := ((hMc _ (mem_sphere_zero_iff_norm.mp hp).le).continuousWithinAt
          (s := unitDisc)).tendsto_nhdsWithin hMm
        rwa [hMp] at this
      exact hfx.comp hT
    · have hT : Tendsto (fun w => R * w) (𝓝[unitDiscExterior] ζ)
          (𝓝[unitDiscExterior] (R * ζ)) :=
        ((continuous_const.mul continuous_id).continuousWithinAt).tendsto_nhdsWithin hrotE
      exact hgx.comp hT
  · obtain ⟨H, hHm, hHc, hHp, hHe⟩ := hh
    obtain ⟨-, hmono, hcont, hper⟩ := s07_mob_props ha' (-t)
    refine ⟨fun θ => -t + H (θ - s) + 2 * arg (1 - a' * exp (-((H (θ - s) : ℂ) * I))),
      hmono.comp (hHm.comp fun x y hxy => sub_lt_sub_right hxy s),
      hcont.comp (hHc.comp (continuous_id.sub continuous_const)), fun θ => ?_, fun θ => ?_⟩
    · show -t + H (θ + 2 * π - s) + 2 * arg (1 - a' * exp (-((H (θ + 2 * π - s) : ℂ) * I))) =
        -t + H (θ - s) + 2 * arg (1 - a' * exp (-((H (θ - s) : ℂ) * I))) + 2 * π
      rw [show θ + 2 * π - s = θ - s + 2 * π by ring, hHp]
      exact hper (H (θ - s))
    · have hrot : R * exp (θ * I) = exp (((θ - s : ℝ) : ℂ) * I) := by
        rw [hRdef, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      show diskMobius (-t) a' (h (R * exp (θ * I))) = _
      rw [hrot, hHe (θ - s), s07_mob_lift ha' (-t) (H (θ - s))]

/-- Möbius reduction, BMO: for `f : 𝔻 → Ω` conformal onto the bounded component of a bounded
quasicircle, `|S(f ∘ M)|²(1-|z|²)³ dA ∈ CM(𝔻)` implies `log f' ∈ BMOA`. -/
theorem s07b_bmoa_of_mobius {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K)
    {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) (t : ℝ) {a : ℂ} (ha : ‖a‖ < 1)
    (hC : IsCarlesonDisk (schwarzCarlesonMeasure (fun z => f (diskMobius t a z)))) :
    LogDerivBMOA f := by
  -- `f ∘ M` is another Riemann map of `Ω`: `Γ` is a BMO quasicircle, so `sup_Ω K_H < ∞`
  -- (Lemma 7.9 (i)), and `sup_Ω K_H` is computed with `f` as well
  have hfM := s07b_comp_mob_conformal hf t ha
  have hBM : LogDerivBMOA (fun z => f (diskMobius t a z)) :=
    (thm_shen_wei_B (Or.inl hq) hfM).mpr hC
  have hBQ : IsBMOQuasicircle Ω Ωs := ⟨⟨K, hq⟩, _, hfM, hBM⟩
  obtain ⟨x₀, hx₀⟩ := s07b_curve_nonempty hq
  have hsup := (lem_one_sided_i K Ω Ωs hq x₀ hx₀).mpr hBQ
  have heq : (⨆ p ∈ Ω, KH (invPairΩ Ω x₀) (invAt x₀ p)) =
      ⨆ b ∈ unitDisc, poissonP (pullbackMass f) b := by
    apply le_antisymm
    · refine iSup₂_le fun p hp => ?_
      rw [← hf.2.2] at hp
      obtain ⟨b, hb, rfl⟩ := hp
      rw [lem_one_sided K Ω Ωs hq f hf x₀ hx₀ b hb]
      exact le_iSup₂ (f := fun b _ => poissonP (pullbackMass f) b) b hb
    · refine iSup₂_le fun b hb => ?_
      rw [← lem_one_sided K Ω Ωs hq f hf x₀ hx₀ b hb]
      exact le_iSup₂ (f := fun p _ => KH (invPairΩ Ω x₀) (invAt x₀ p)) (f b)
        (hf.2.2 ▸ mem_image_of_mem f hb)
  rw [heq] at hsup
  rw [thm_shen_wei_B (Or.inl hq) hf, ← s07_carleson_smul, ← lem_one_sided_varpi,
    ← s07_carlesonNorm_lt_top]
  exact lt_of_le_of_lt (lem_kernel_test_b (pullbackMass f)).1
    (ENNReal.mul_lt_top (by norm_num) hsup)

/-- Möbius reduction, VMO: `|S(f ∘ M)|²(1-|z|²)³ dA ∈ CM₀(𝔻)` implies `log f' ∈ VMOA`. -/
theorem s07b_vmoa_of_mobius {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K)
    {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) (t : ℝ) {a : ℂ} (ha : ‖a‖ < 1)
    (hC : IsVanishingCarlesonDisk (schwarzCarlesonMeasure (fun z => f (diskMobius t a z)))) :
    LogDerivVMOA f := by
  -- as the BMO part, with Lemma 7.9 (ii) and Lemma 7.1 (c)
  have hfM := s07b_comp_mob_conformal hf t ha
  have hVM : LogDerivVMOA (fun z => f (diskMobius t a z)) := (thm_shen_wei_V hq hfM).mpr hC
  have hVQ : IsVMOQuasicircle Ω Ωs := ⟨⟨K, hq⟩, _, hfM, hVM⟩
  obtain ⟨x₀, hx₀⟩ := s07b_curve_nonempty hq
  have hD := (lem_one_sided_ii K Ω Ωs hq f hf x₀ hx₀).mpr hVQ
  have hP : DiskBoundaryVanishing (poissonP (pullbackMass f)) := by
    intro ε hε
    obtain ⟨r, hr, hra⟩ := hD ε hε
    refine ⟨r, hr, fun b h1 h2 => ?_⟩
    rw [← lem_one_sided K Ω Ωs hq f hf x₀ hx₀ b (mem_ball_zero_iff.mpr h2)]
    exact hra b h1 h2
  have hV := (lem_kernel_test_c (pullbackMass f)).mpr hP
  rw [lem_one_sided_varpi, s07_vanishingCarleson_smul] at hV
  exact (thm_shen_wei_V hq hf).mpr hV

/-- Helper for `s07b_B5_bwd`/`s07b_V5_bwd`: from an extension `E` of `e^{is} h⁻¹ ∘ M` (Lane C) the
welding gluing (Lane U) of `(f ∘ M, g ∘ e^{-is})` gives a global `K₁`-q.c. `Φ`, conformal on `𝔻`, with
`∂̄Φ = μ_Φ ∂Φ` a.e., `‖μ_Φ‖ ≤ k₀` a.e., the same exterior box integrals as `μ_E`, and
`S Φ = S(f ∘ M)` on `𝔻`. -/
theorem s07b_B5_glue {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K)
    {f g h hinv : ℂ → ℂ} (hw : IsDiskWelding Ω Ωs f g h) (hh : IsCircleHomeo h)
    (hinvP : ∀ ζ ∈ sphere (0 : ℂ) 1, hinv ζ ∈ sphere (0 : ℂ) 1 ∧ h (hinv ζ) = ζ ∧ hinv (h ζ) = ζ)
    (s t : ℝ) {a : ℂ} (ha : ‖a‖ < 1) {E : ℂ → ℂ} {K₁ k₀ : ℝ}
    (hE : IsKQC E unitDiscExterior K₁) (hEs : E '' unitDiscExterior = unitDiscExterior)
    (hEinf : Tendsto E (cocompact ℂ) (cocompact ℂ))
    (hEb : ∀ ξ ∈ sphere (0 : ℂ) 1,
      Tendsto E (𝓝[unitDiscExterior] ξ) (𝓝 (exp (s * I) * hinv (diskMobius t a ξ))))
    (hμ : ∀ w ∈ unitDiscExterior, ‖LiZhongQC.complexDilatation E w‖ ≤ k₀) :
    ∃ Φ : ℂ → ℂ, IsKQC Φ univ K₁ ∧ DifferentiableOn ℂ Φ unitDisc ∧
      (∀ᵐ w, dzbar Φ w = LiZhongQC.complexDilatation Φ w * dz Φ w) ∧
      (∀ᵐ w, ‖LiZhongQC.complexDilatation Φ w‖ ≤ k₀) ∧
      (∀ (ζ : ℂ) (r : ℝ), ∫⁻ w in unitDiscExterior ∩ ball ζ r,
          ENNReal.ofReal (‖LiZhongQC.complexDilatation Φ w‖ ^ 2 / (‖w‖ ^ 2 - 1)) =
        ∫⁻ w in unitDiscExterior ∩ ball ζ r,
          ENNReal.ofReal (‖LiZhongQC.complexDilatation E w‖ ^ 2 / (‖w‖ ^ 2 - 1))) ∧
      schwarzCarlesonMeasure Φ = schwarzCarlesonMeasure (fun z => f (diskMobius t a z)) := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hDo : IsOpen unitDisc := isOpen_ball
  have hk0 : 0 ≤ k₀ := (norm_nonneg _).trans (hμ 2 (by show (1 : ℝ) < ‖(2 : ℂ)‖; norm_num))
  obtain ⟨hw', hh'⟩ := s07b_weld_mobius hw hh s t ha
  have hRn : ‖exp (-(s * I))‖ = 1 := by
    rw [show -((s : ℂ) * I) = ((-s : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  -- boundary values of `E` at `h' ζ`: `e^{is} h⁻¹(M(M⁻¹(h(e^{-is} ζ)))) = ζ` (W1, W0)
  have hEb' : ∀ ζ ∈ sphere (0 : ℂ) 1, Tendsto E (𝓝[unitDiscExterior]
      (diskMobius (-t) (-(exp (t * I) * a)) (h (exp (-(s * I)) * ζ)))) (𝓝 ζ) := by
    intro ζ hζ
    have hRζ : exp (-(s * I)) * ζ ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_mul, hRn, one_mul]
      exact mem_sphere_zero_iff_norm.mp hζ
    have hy : h (exp (-(s * I)) * ζ) ∈ sphere (0 : ℂ) 1 := hw.2.2.2.1 hRζ
    have hval : exp (s * I) * hinv (diskMobius t a (diskMobius (-t) (-(exp (t * I) * a))
        (h (exp (-(s * I)) * ζ)))) = ζ := by
      rw [s07b_mob_inv t ha hy, (hinvP _ hRζ).2.2, ← mul_assoc, ← Complex.exp_add, add_neg_cancel,
        Complex.exp_zero, one_mul]
    have h1 := hEb (diskMobius (-t) (-(exp (t * I) * a)) (h (exp (-(s * I)) * ζ)))
      (hw'.2.2.2.1 hζ)
    rw [hval] at h1
    exact h1
  obtain ⟨Φ, hΦ, -, hΦf, -, hΦ0, hΦE⟩ := s07u_glue hq hw' hh' hE hEs hEinf hEb'
  refine ⟨Φ, hΦ, (s07b_comp_mob_conformal hw.1 t ha).1.congr hΦf, ?_, ?_, ?_, ?_⟩
  · have h1 := abW_ae_dilatation hΦ
    rw [Measure.restrict_univ] at h1
    filter_upwards [h1] with w hw1
    exact hw1.1
  · -- `∂𝔻` is null; `μ_Φ = 0` on `𝔻` and `μ_Φ = μ_E` on `𝔻*`
    have hsph : volume (sphere (0 : ℂ) 1) = 0 := Measure.addHaar_sphere volume 0 1
    filter_upwards [compl_mem_ae_iff.mpr hsph] with w hw1
    rcases lt_trichotomy ‖w‖ 1 with h1 | h1 | h1
    · rw [hΦ0 w (mem_ball_zero_iff.mpr h1), norm_zero]
      exact hk0
    · exact absurd (mem_sphere_zero_iff_norm.mpr h1) hw1
    · rw [hΦE w h1]
      exact hμ w h1
  · intro ζ r
    exact setLIntegral_congr_fun (hEo.inter isOpen_ball).measurableSet fun w hw1 => by
      rw [hΦE w hw1.1]
  · unfold schwarzCarlesonMeasure
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem hDo.measurableSet] with z hz
    have hev : Φ =ᶠ[𝓝 z] fun z => f (diskMobius t a z) :=
      Filter.eventually_of_mem (hDo.mem_nhds hz) hΦf
    rw [schwarzian_congr (hev.filter_mono nhdsWithin_le_nhds)]

/-- Theorem 2.13 `thm:shen-wei`, (B5) ⇒ (B2), `sec02-prelim.tex:598`: if the welding of a bounded
quasicircle is strongly quasisymmetric, then `log f' ∈ BMOA`. -/
theorem s07b_B5_bwd {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K)
    {f g h : ℂ → ℂ} (hw : IsDiskWelding Ω Ωs f g h) (hS : IsStronglyQS h) :
    LogDerivBMOA f := by
  have hh : IsCircleHomeo h := by
    obtain ⟨δf, hδ⟩ := hS
    exact hδ.1
  obtain ⟨hinv, hinvP⟩ := s07b_circle_inv hh
  have hk := sqs_circle_inv h hinv hS fun ζ hζ => ⟨(hinvP ζ hζ).1, (hinvP ζ hζ).2.1⟩
  obtain ⟨s, t, a, ha, E, K₁, k₀, C, hE, hEs, hEinf, hEb, hk1, hμ, hC0, hCb⟩ := s0c_ext_B hk
  obtain ⟨Φ, hΦ, hΦD, hν, hνk, hbox, hSeq⟩ :=
    s07b_B5_glue hq hw hh hinvP s t ha hE hEs hEinf hEb hμ
  have hk0 : 0 ≤ k₀ := (norm_nonneg _).trans (hμ 2 (by show (1 : ℝ) < ‖(2 : ℂ)‖; norm_num))
  have hB3 := s07b_az1_B3 hk0 hk1 hΦ hΦD hν hνk ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top,
    fun ζ hζ r hr hr2 => by
      rw [hbox ζ r, ← ENNReal.ofReal_mul hC0]
      exact hCb ζ hζ r hr hr2⟩
  rw [hSeq] at hB3
  exact s07b_bmoa_of_mobius hq hw.1 t ha hB3

/-- Theorem 2.13 `thm:shen-wei`, (V5) ⇒ (V2), `sec02-prelim.tex:604`: if the welding of a bounded
quasicircle is strongly symmetric, then `log f' ∈ VMOA`. -/
theorem s07b_V5_bwd {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K)
    {f g h : ℂ → ℂ} (hw : IsDiskWelding Ω Ωs f g h) (hS : IsStronglySymmetric h) :
    LogDerivVMOA f := by
  have hh : IsCircleHomeo h := by
    obtain ⟨H, u, hH, hHc, hper, hl, -⟩ := hS
    exact ⟨H, hH, hHc, hper, hl⟩
  obtain ⟨hinv, hinvP⟩ := s07b_circle_inv hh
  have hk := ss_circle_inv h hinv hS fun ζ hζ => ⟨(hinvP ζ hζ).1, (hinvP ζ hζ).2.1⟩
  obtain ⟨s, t, a, ha, E, K₁, k₀, C, hE, hEs, hEinf, hEb, hk1, hμ, ⟨hC0, hCb⟩, hV⟩ := s0c_ext_V hk
  obtain ⟨Φ, hΦ, hΦD, hν, hνk, hbox, hSeq⟩ :=
    s07b_B5_glue hq hw hh hinvP s t ha hE hEs hEinf hEb hμ
  have hk0 : 0 ≤ k₀ := (norm_nonneg _).trans (hμ 2 (by show (1 : ℝ) < ‖(2 : ℂ)‖; norm_num))
  have hV3 := s07b_az1_V3 hk0 hk1 hΦ hΦD hν hνk ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top,
    fun ζ hζ r hr hr2 => by
      rw [hbox ζ r, ← ENNReal.ofReal_mul hC0]
      exact hCb ζ hζ r hr hr2⟩
    fun ε hε => by
      obtain ⟨δ, hδ, hb⟩ := hV ε hε
      exact ⟨δ, hδ, fun ζ hζ r hr hrδ => by
        rw [hbox ζ r]
        exact hb ζ hζ r hr hrδ⟩
  rw [hSeq] at hV3
  exact s07b_vmoa_of_mobius hq hw.1 t ha hV3

/-- Theorem 2.13 `thm:shen-wei`, (V2) ⇔ (V5), `sec02-prelim.tex:604`: for bounded `f`,
`log f' ∈ VMOA` iff the welding is strongly symmetric. -/
theorem thm_shen_wei_V5 {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K)
    {f g h : ℂ → ℂ} (hw : IsDiskWelding Ω Ωs f g h) :
    LogDerivVMOA f ↔ IsStronglySymmetric h := by
  exact ⟨s07b_fkph_V5_fwd hq hw, s07b_V5_bwd hq hw⟩

end EpsteinVMO
