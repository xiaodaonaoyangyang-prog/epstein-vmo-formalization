import EpsteinVMO.S07_Transfer
import TauCeti.MeasureTheory.Integral.MaximalFunction
import TauCeti.Analysis.PDE.GreenFunction.Disk
import TauCeti.Analysis.PDE.Harnack.Planar
import TauCeti.Analysis.PDE.PoissonIntegral.Ball
import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl

/-!
# W-FKPH, SMALL chain (FKP Thm 2.5 for quasiconformal pullbacks)

Owner w3 (Round B, lane F; design `collaboration/DESIGN_w4_FKPH.md` §3 SMALL and §6, triage
`collaboration/TRIAGE_w3_FKPS.md`). This module will hold the milestones M2–M6 (prefix `s07c_fkps_`) and the
statement `s07c_fkps_small`: a quasiconformal self-map of `𝔻` fixing `0` whose dilatation is small in the
Whitney-sup Carleson sense has a strongly symmetric boundary map with `osc(log H') ≤ C √ε`.
`EpsteinVMO.S07b_ShenWei` imports this module.

Source: Fefferman–Kenig–Pipher, *The theory of weights and the Dirichlet problem for elliptic equations*,
Thm 2.5, Lemmas 2.9 and 2.10.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace EpsteinVMO

open LiZhongQC

/-- The `arg`-lift of a `2π`-periodic `f` agrees with `f` on the unit circle. -/
theorem s07c_fkps_m2_lift_circle (f : ℝ → ℝ) (hper : ∀ t, f (t + 2 * π) = f t) (t : ℝ) :
    f (Complex.arg (circleMap 0 1 t)) = f t := by
  have hP : Function.Periodic f (2 * π) := hper
  rw [circleMap, zero_add, ofReal_one, one_mul, arg_exp_mul_I, toIocMod]
  exact hP.sub_zsmul_eq _

/-- Pointwise: the real part of the Herglotz kernel on the unit circle is the Poisson kernel. -/
theorem s07c_fkps_m2_re_herglotz (z : ℂ) (t : ℝ) (c : ℝ) :
    (herglotzRieszKernel 0 z (circleMap 0 1 t) • (c : ℂ)).re =
      (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 * c := by
  have h1 : ‖Complex.exp (t * I)‖ = 1 := by
    rw [Complex.norm_exp_ofReal_mul_I]
  have hk := congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := z))
    (circleMap 0 1 t)
  rw [Function.comp_apply, poissonKernel_def] at hk
  rw [smul_eq_mul, re_mul_ofReal, ← hk]
  simp only [circleMap, zero_add, ofReal_one, one_mul, sub_zero, h1, one_pow]

/-- The Poisson integral is the real part of the Herglotz integral of the `arg`-lift. -/
theorem s07c_fkps_m2_poisson_eq_re (f : ℝ → ℝ) (hf : Continuous f)
    (hper : ∀ t, f (t + 2 * π) = f t) (z : ℂ) (hz : z ∉ sphere (0 : ℂ) 1) :
    (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 * f t =
      (Real.circleAverage (fun ζ ↦ herglotzRieszKernel 0 z ζ • ((f (Complex.arg ζ) : ℝ) : ℂ)) 0 1).re := by
  have hcont : Continuous fun t : ℝ => herglotzRieszKernel 0 z (circleMap 0 1 t) • ((f t : ℝ) : ℂ) := by
    have hne : ∀ t : ℝ, circleMap 0 1 t - 0 - (z - 0) ≠ 0 := by
      intro t h
      apply hz
      have : z = circleMap 0 1 t := by
        have := sub_eq_zero.mp h
        simpa using this.symm
      rw [this, mem_sphere_zero_iff_norm, norm_circleMap_zero, abs_one]
    simp only [herglotzRieszKernel_def]
    exact (((continuous_circleMap 0 1).sub continuous_const).add continuous_const).div
      ((continuous_circleMap 0 1).sub continuous_const |>.sub continuous_const) hne
      |>.smul (continuous_ofReal.comp hf)
  rw [Real.circleAverage_def, smul_re, smul_eq_mul]
  congr 1
  have hcongr : (fun θ : ℝ => herglotzRieszKernel 0 z (circleMap 0 1 θ) •
      ((f (Complex.arg (circleMap 0 1 θ)) : ℝ) : ℂ)) =
      fun θ : ℝ => herglotzRieszKernel 0 z (circleMap 0 1 θ) • ((f θ : ℝ) : ℂ) := by
    funext θ
    rw [s07c_fkps_m2_lift_circle f hper θ]
  have hre := intervalIntegral.intervalIntegral_re (μ := volume)
    (hcont.intervalIntegrable 0 (2 * π))
  simp only [RCLike.re_to_complex] at hre
  rw [hcongr, ← hre]
  refine intervalIntegral.integral_congr fun t _ => ?_
  exact (s07c_fkps_m2_re_herglotz z t (f t)).symm

/-- Harmonicity half of M2.1. -/
theorem s07c_fkps_m2_poisson_harmonic (f : ℝ → ℝ) (hf : Continuous f)
    (hper : ∀ t, f (t + 2 * π) = f t) :
    InnerProductSpace.HarmonicOnNhd (fun z : ℂ => (2 * π)⁻¹ *
      ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 * f t) unitDisc := by
  intro z hz
  have hzs : z ∈ (sphere (0 : ℂ) |(1 : ℝ)|)ᶜ := by
    rw [abs_one, mem_compl_iff, mem_sphere_zero_iff_norm]
    exact ne_of_lt (by simpa [unitDisc, mem_ball_zero_iff] using hz)
  have hint : CircleIntegrable (fun ζ : ℂ => ((f (Complex.arg ζ) : ℝ) : ℂ)) 0 1 := by
    have : (fun θ : ℝ => ((f (Complex.arg (circleMap 0 1 θ)) : ℝ) : ℂ)) =
        fun θ : ℝ => ((f θ : ℝ) : ℂ) := by
      funext θ; rw [s07c_fkps_m2_lift_circle f hper θ]
    unfold CircleIntegrable
    rw [this]
    exact (continuous_ofReal.comp hf).intervalIntegrable _ _
  have han := (analyticOnNhd_circleAverage_herglotzRieszKernel_smul hint) z hzs
  have hre := han.harmonicAt_re
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hre
  have hopen : IsOpen ((sphere (0 : ℂ) 1)ᶜ) := isClosed_sphere.isOpen_compl
  have hz1 : z ∈ (sphere (0 : ℂ) 1)ᶜ := by simpa [abs_one] using hzs
  filter_upwards [hopen.mem_nhds hz1] with w hw
  exact (s07c_fkps_m2_poisson_eq_re f hf hper w hw).symm

/-- Chord length on the unit circle: `‖e^{is} - 1‖ ≥ (2/π)|s|` for `|s| ≤ π`. -/
theorem s07c_fkps_m2_chord (s : ℝ) (hs : |s| ≤ π) :
    2 / π * |s| ≤ ‖Complex.exp (s * I) - 1‖ := by
  have hsq : ‖Complex.exp (s * I) - 1‖ ^ 2 = (2 * Real.sin (s / 2)) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sub_re, sub_im,
      exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, one_re, one_im]
    have h2 : s = 2 * (s / 2) := by ring
    rw [h2, Real.cos_two_mul, Real.sin_two_mul]
    have h3 : 2 * (s / 2) / 2 = s / 2 := by ring
    rw [h3]
    linear_combination (4 * (Real.cos (s / 2) ^ 2 - 1)) * Real.sin_sq_add_cos_sq (s / 2)
  have hn : ‖Complex.exp (s * I) - 1‖ = 2 * |Real.sin (s / 2)| := by
    have h0 : 0 ≤ 2 * |Real.sin (s / 2)| := by positivity
    rw [← abs_of_nonneg (norm_nonneg (Complex.exp (s * I) - 1)), ← abs_of_nonneg h0]
    apply sq_eq_sq_iff_abs_eq_abs _ _ |>.mp
    rw [hsq, mul_pow, mul_pow, sq_abs]
  have hhalf : |s / 2| ≤ π / 2 := by
    rw [abs_div, abs_two]; linarith
  have hj := Real.mul_abs_le_abs_sin hhalf
  rw [abs_div, abs_two] at hj
  rw [hn]
  have hpi : 0 < π := Real.pi_pos
  calc 2 / π * |s| = 2 * (2 / π * (|s| / 2)) := by ring
    _ ≤ 2 * |Real.sin (s / 2)| := by linarith

/-- `‖e^{it} - e^{iθ}‖ = ‖e^{i(t-θ)} - 1‖`. -/
theorem s07c_fkps_m2_chord_shift (t θ : ℝ) :
    ‖Complex.exp (t * I) - Complex.exp (θ * I)‖ = ‖Complex.exp (((t - θ : ℝ) : ℂ) * I) - 1‖ := by
  have h : Complex.exp (t * I) - Complex.exp (θ * I) =
      Complex.exp (θ * I) * (Complex.exp (((t - θ : ℝ) : ℂ) * I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- `e^{i(t + 2π)} = e^{it}`. -/
theorem s07c_fkps_m2_exp_periodic (t : ℝ) :
    Complex.exp (((t + 2 * π : ℝ) : ℂ) * I) = Complex.exp (t * I) := by
  have h : ((t + 2 * π : ℝ) : ℂ) * I = t * I + 2 * π * I := by push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- For `z ∈ 𝔻`, `e^{it} ≠ z`. -/
theorem s07c_fkps_m2_exp_ne (z : ℂ) (hz : z ∈ unitDisc) (t : ℝ) :
    Complex.exp (t * I) - z ≠ 0 := by
  intro h
  have h1 : ‖Complex.exp (t * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I t
  rw [sub_eq_zero.mp h] at h1
  have : ‖z‖ < 1 := by simpa [unitDisc, mem_ball_zero_iff] using hz
  linarith

/-- The Poisson kernel is continuous in `t` for a pole in `𝔻`. -/
theorem s07c_fkps_m2_kernel_cont (z : ℂ) (hz : z ∈ unitDisc) :
    Continuous fun t : ℝ => (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 := by
  refine continuous_const.div ?_ fun t => pow_ne_zero 2 (norm_ne_zero_iff.mpr
    (s07c_fkps_m2_exp_ne z hz t))
  fun_prop

/-- The Poisson kernel is nonnegative for a pole in `𝔻`. -/
theorem s07c_fkps_m2_kernel_nonneg (z : ℂ) (hz : z ∈ unitDisc) (t : ℝ) :
    0 ≤ (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 := by
  have : ‖z‖ < 1 := by simpa [unitDisc, mem_ball_zero_iff] using hz
  have h0 : 0 ≤ ‖z‖ := norm_nonneg z
  apply div_nonneg _ (sq_nonneg _)
  nlinarith

/-- The Poisson kernel has mass one: `(2π)⁻¹ ∫₀^{2π} P(z, t) dt = 1` for `z ∈ 𝔻`. -/
theorem s07c_fkps_m2_kernel_mass (z : ℂ) (hz : z ∈ unitDisc) :
    (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 = 1 := by
  have hw : z ∈ ball (0 : ℂ) 1 := hz
  have hc := InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul
    (f := fun _ : ℂ => (1 : ℝ)) (c := 0) (R := 1)
    (InnerProductSpace.harmonicOnNhd_const (1 : ℝ)) hw
  rw [Real.circleAverage_def] at hc
  simp only [Pi.smul_apply, smul_eq_mul, mul_one] at hc
  refine Eq.trans ?_ hc
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp [poissonKernel_def, circleMap, Complex.norm_exp_ofReal_mul_I]

/-- Shift of a period: `∫₀^{2π} = ∫_{θ-π}^{θ+π}` for `2π`-periodic integrands. -/
theorem s07c_fkps_m2_shift (g : ℝ → ℝ) (hg : ∀ t, g (t + 2 * π) = g t) (θ : ℝ) :
    ∫ t in (0 : ℝ)..2 * π, g t = ∫ t in (θ - π)..(θ + π), g t := by
  have hP : Function.Periodic g (2 * π) := hg
  have h := hP.intervalIntegral_add_eq 0 (θ - π)
  rw [zero_add, show θ - π + 2 * π = θ + π by ring] at h
  exact h

/-- Boundary values half of M2.1. -/
theorem s07c_fkps_m2_poisson_tendsto (f : ℝ → ℝ) (hf : Continuous f)
    (hper : ∀ t, f (t + 2 * π) = f t) (θ : ℝ) :
    Tendsto (fun z : ℂ => (2 * π)⁻¹ *
      ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 * f t)
      (𝓝[unitDisc] (Complex.exp (θ * I))) (𝓝 (f θ)) := by
  have hpi : 0 < π := Real.pi_pos
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.mp hf.continuousAt (ε / 2) (by linarith)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := θ - π) (b := θ + π)).exists_bound_of_continuousOn
    hf.continuousOn
  have hθI : θ ∈ Icc (θ - π) (θ + π) := ⟨by linarith, by linarith⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM θ hθI)
  set c : ℝ := 2 / π * min δ π with hcdef
  have hc : 0 < c := by
    have : 0 < min δ π := lt_min hδ hpi
    positivity
  set η : ℝ := min (c / 2) (ε * c ^ 2 / (64 * (M + 1))) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by positivity)
  refine ⟨η, hη, ?_⟩
  intro z hz hzd
  set d : ℝ := dist z (Complex.exp (θ * I)) with hddef
  have hd0 : 0 ≤ d := dist_nonneg
  have hdη : d < η := hzd
  have hdc : d < c / 2 := lt_of_lt_of_le hdη (min_le_left _ _)
  have hdε : d ≤ ε * c ^ 2 / (64 * (M + 1)) := le_of_lt (lt_of_lt_of_le hdη (min_le_right _ _))
  have hz1 : ‖z‖ < 1 := by simpa [unitDisc, mem_ball_zero_iff] using hz
  -- the kernel and the integrand
  set K : ℝ → ℝ := fun t => (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 with hKdef
  have hKc : Continuous K := s07c_fkps_m2_kernel_cont z hz
  have hK0 : ∀ t, 0 ≤ K t := s07c_fkps_m2_kernel_nonneg z hz
  have hKper : ∀ t, K (t + 2 * π) = K t := by
    intro t
    show (1 - ‖z‖ ^ 2) / ‖Complex.exp (((t + 2 * π : ℝ) : ℂ) * I) - z‖ ^ 2 =
      (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2
    rw [s07c_fkps_m2_exp_periodic t]
  have hmass : (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, K t = 1 := s07c_fkps_m2_kernel_mass z hz
  -- rewrite the difference as one integral
  have hdiff : (2 * π)⁻¹ * (∫ t in (0 : ℝ)..2 * π, K t * f t) - f θ =
      (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, K t * (f t - f θ) := by
    have hi1 : IntervalIntegrable (fun t => K t * f t) volume 0 (2 * π) :=
      (hKc.mul hf).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun t => K t * f θ) volume 0 (2 * π) :=
      (hKc.mul continuous_const).intervalIntegrable _ _
    have hsplit : (∫ t in (0 : ℝ)..2 * π, K t * (f t - f θ)) =
        (∫ t in (0 : ℝ)..2 * π, K t * f t) - (∫ t in (0 : ℝ)..2 * π, K t * f θ) := by
      rw [← intervalIntegral.integral_sub hi1 hi2]
      refine intervalIntegral.integral_congr fun t _ => ?_
      ring
    rw [hsplit, intervalIntegral.integral_mul_const, mul_sub]
    have : (2 * π)⁻¹ * ((∫ t in (0 : ℝ)..2 * π, K t) * f θ) = f θ := by
      rw [← mul_assoc, hmass, one_mul]
    rw [this]
  -- the pointwise bound
  set B : ℝ := 16 * M * d / c ^ 2 with hBdef
  have hpt : ∀ t ∈ Icc (θ - π) (θ + π), ‖K t * (f t - f θ)‖ ≤ K t * (ε / 2) + B := by
    intro t ht
    have hB0 : 0 ≤ B := by positivity
    rw [norm_mul, Real.norm_of_nonneg (hK0 t)]
    by_cases hnear : dist t θ < δ
    · have h1 : ‖f t - f θ‖ ≤ ε / 2 := by
        have := hfδ hnear
        rw [dist_eq_norm] at this
        exact le_of_lt this
      have := mul_le_mul_of_nonneg_left h1 (hK0 t)
      linarith
    · -- far from `θ`: the kernel is small
      have hfar : δ ≤ |t - θ| := by
        rw [Real.dist_eq] at hnear
        linarith [not_lt.mp hnear]
      have htθ : |t - θ| ≤ π := by
        rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      have hch : c ≤ ‖Complex.exp (t * I) - Complex.exp (θ * I)‖ := by
        rw [s07c_fkps_m2_chord_shift]
        refine le_trans ?_ (s07c_fkps_m2_chord (t - θ) htθ)
        rw [hcdef]
        have : min δ π ≤ |t - θ| := le_trans (min_le_left _ _) hfar
        have h2pi : 0 ≤ 2 / π := by positivity
        exact mul_le_mul_of_nonneg_left this h2pi
      have hden : c / 2 ≤ ‖Complex.exp (t * I) - z‖ := by
        have htri : ‖Complex.exp (t * I) - Complex.exp (θ * I)‖ ≤
            ‖Complex.exp (t * I) - z‖ + ‖z - Complex.exp (θ * I)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        have : ‖z - Complex.exp (θ * I)‖ = d := by rw [hddef, dist_eq_norm]
        linarith
      have hnum : 1 - ‖z‖ ^ 2 ≤ 2 * d := by
        have h1 : 1 - ‖z‖ ≤ d := by
          have hn1 : ‖Complex.exp (θ * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
          have := norm_sub_norm_le (Complex.exp (θ * I)) z
          rw [hn1] at this
          rw [hddef, dist_comm, dist_eq_norm]
          exact this
        have h0 : 0 ≤ ‖z‖ := norm_nonneg z
        nlinarith
      have hKle : K t ≤ 8 * d / c ^ 2 := by
        simp only [hKdef]
        have hpos : 0 < (c / 2) ^ 2 := by positivity
        have hsq : (c / 2) ^ 2 ≤ ‖Complex.exp (t * I) - z‖ ^ 2 := by
          have : 0 ≤ c / 2 := by linarith
          exact pow_le_pow_left₀ this hden 2
        calc (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2
            ≤ (2 * d) / ‖Complex.exp (t * I) - z‖ ^ 2 := by
              apply div_le_div_of_nonneg_right hnum (sq_nonneg _)
          _ ≤ (2 * d) / (c / 2) ^ 2 := by
              apply div_le_div_of_nonneg_left (by linarith) hpos hsq
          _ = 8 * d / c ^ 2 := by field_simp; ring
      have hfd : ‖f t - f θ‖ ≤ 2 * M := by
        have := norm_sub_le (f t) (f θ)
        linarith [hM t ht, hM θ hθI]
      have hprod : K t * ‖f t - f θ‖ ≤ 8 * d / c ^ 2 * (2 * M) :=
        mul_le_mul hKle hfd (norm_nonneg _) (by positivity)
      have : 8 * d / c ^ 2 * (2 * M) = B := by rw [hBdef]; ring
      have hKe : 0 ≤ K t * (ε / 2) := mul_nonneg (hK0 t) (by linarith)
      linarith
  -- integrate
  have hperI : ∀ t, K (t + 2 * π) * (f (t + 2 * π) - f θ) = K t * (f t - f θ) := by
    intro t; rw [hKper t, hper t]
  have hshift := s07c_fkps_m2_shift (fun t => K t * (f t - f θ)) hperI θ
  have hshiftK := s07c_fkps_m2_shift K hKper θ
  have hle : θ - π ≤ θ + π := by linarith
  have hint : ‖∫ t in (θ - π)..(θ + π), K t * (f t - f θ)‖ ≤
      ∫ t in (θ - π)..(θ + π), (K t * (ε / 2) + B) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hle
    · exact ae_of_all _ fun t ht => hpt t ⟨le_of_lt ht.1, ht.2⟩
    · exact ((hKc.mul continuous_const).add continuous_const).intervalIntegrable _ _
  have hval : ∫ t in (θ - π)..(θ + π), (K t * (ε / 2) + B) =
      (∫ t in (0 : ℝ)..2 * π, K t) * (ε / 2) + 2 * π * B := by
    rw [intervalIntegral.integral_add (f := fun t => K t * (ε / 2)) (g := fun _ => B)
      ((hKc.mul continuous_const).intervalIntegrable _ _) intervalIntegrable_const, intervalIntegral.integral_mul_const, ← hshiftK,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hmass' : (∫ t in (0 : ℝ)..2 * π, K t) = 2 * π := by
    have h2 : (2 * π) ≠ 0 := by positivity
    field_simp at hmass
    linarith
  have hBsmall : B ≤ ε / 4 := by
    rw [hBdef]
    have hc2 : 0 < c ^ 2 := by positivity
    rw [div_le_iff₀ hc2]
    have h1 : 16 * M * d ≤ 16 * (M + 1) * d := by nlinarith
    have h2 : 16 * (M + 1) * d ≤ 16 * (M + 1) * (ε * c ^ 2 / (64 * (M + 1))) := by
      apply mul_le_mul_of_nonneg_left hdε; positivity
    have h3 : 16 * (M + 1) * (ε * c ^ 2 / (64 * (M + 1))) = ε / 4 * c ^ 2 := by
      field_simp; ring
    linarith
  rw [dist_eq_norm]
  simp only [hKdef] at hdiff
  rw [hdiff, norm_mul, Real.norm_of_nonneg (by positivity), hshift]
  simp only [hKdef] at hint hval hmass'
  calc (2 * π)⁻¹ * ‖∫ t in (θ - π)..(θ + π), (1 - ‖z‖ ^ 2) /
        ‖Complex.exp (t * I) - z‖ ^ 2 * (f t - f θ)‖
      ≤ (2 * π)⁻¹ * ((2 * π) * (ε / 2) + 2 * π * B) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine hint.trans (le_of_eq ?_)
        rw [hval, hmass']
    _ = ε / 2 + B := by field_simp
    _ < ε := by linarith

/-- M2.1 (Poisson extension): for continuous `2π`-periodic `f`, `P f` is harmonic on `𝔻` and tends to
`f θ` at `e^{iθ}` from inside. -/
theorem s07c_fkps_m2_poisson (f : ℝ → ℝ) (hf : Continuous f) (hper : ∀ t, f (t + 2 * π) = f t) :
    InnerProductSpace.HarmonicOnNhd (fun z : ℂ => (2 * π)⁻¹ *
      ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 * f t) unitDisc ∧
    ∀ θ : ℝ, Tendsto (fun z : ℂ => (2 * π)⁻¹ *
      ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 * f t)
      (𝓝[unitDisc] (Complex.exp (θ * I))) (𝓝 (f θ)) := by
  exact ⟨s07c_fkps_m2_poisson_harmonic f hf hper, s07c_fkps_m2_poisson_tendsto f hf hper⟩

/-- One period of a `2π`-periodic `ℝ≥0∞`-valued function: `∫⁻_{(a, a+2π]} = ∫⁻_{(0, 2π]}`. -/
theorem s07c_fkps_m2_lint_period (h : ℝ → ℝ≥0∞) (hp : ∀ t, h (t + 2 * π) = h t) (a : ℝ) :
    ∫⁻ x in Ioc a (a + 2 * π), h x = ∫⁻ x in Ioc 0 (2 * π), h x := by
  have : Fact (0 < 2 * π) := ⟨by positivity⟩
  have hP : Function.Periodic h (2 * π) := hp
  have e1 := AddCircle.lintegral_preimage (T := 2 * π) a hP.lift
  have e2 := AddCircle.lintegral_preimage (T := 2 * π) 0 hP.lift
  rw [zero_add] at e2
  simp only [Function.Periodic.lift_coe] at e1 e2
  rw [e1, e2]

/-- `N` periods: `∫⁻_{(a, a+2πN]} = N ∫⁻_{(0, 2π]}`. -/
theorem s07c_fkps_m2_lint_periods (h : ℝ → ℝ≥0∞) (hp : ∀ t, h (t + 2 * π) = h t) (a : ℝ)
    (N : ℕ) :
    ∫⁻ x in Ioc a (a + 2 * π * N), h x = N * ∫⁻ x in Ioc 0 (2 * π), h x := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hpi : 0 ≤ 2 * π := by positivity
    have h1 : a ≤ a + 2 * π * N := by
      have : 0 ≤ 2 * π * (N : ℝ) := by positivity
      linarith
    have h2 : a + 2 * π * N ≤ a + 2 * π * N + 2 * π := by linarith
    have hU : Ioc a (a + 2 * π * ((N + 1 : ℕ) : ℝ)) =
        Ioc a (a + 2 * π * N) ∪ Ioc (a + 2 * π * N) (a + 2 * π * N + 2 * π) := by
      rw [Ioc_union_Ioc_eq_Ioc h1 h2]
      congr 1
      push_cast
      ring
    rw [hU, lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl), ih,
      s07c_fkps_m2_lint_period h hp]
    push_cast
    ring

/-- On `[0, 2π]` the maximal function of a periodic `f` is at most twice that of its restriction to
`(-π, 3π]`. -/
theorem s07c_fkps_m2_max_local (f : ℝ → ℝ) (hper : ∀ t, f (t + 2 * π) = f t) (θ : ℝ)
    (hθ : θ ∈ Icc 0 (2 * π)) :
    TauCeti.maximalFunction volume f θ ≤
      2 * TauCeti.maximalFunction volume (indicator (Ioc (-π) (3 * π)) f) θ := by
  have hpi : 0 < π := Real.pi_pos
  set g := indicator (Ioc (-π) (3 * π)) f with hgdef
  set Mg := TauCeti.maximalFunction volume g θ with hMgdef
  have hsub : ∀ r, r ≤ π → ball θ r ⊆ Ioc (-π) (3 * π) := by
    intro r hr x hx
    rw [Real.ball_eq_Ioo] at hx
    exact ⟨by linarith [hx.1, hθ.1], by linarith [hx.2, hθ.2]⟩
  have heq : ∀ r, r ≤ π → ∫⁻ y in ball θ r, ‖f y‖ₑ = ∫⁻ y in ball θ r, ‖g y‖ₑ := by
    intro r hr
    refine setLIntegral_congr_fun measurableSet_ball fun y hy => ?_
    rw [hgdef, indicator_of_mem (hsub r hr hy)]
  refine TauCeti.maximalFunction_le fun r hr => ?_
  by_cases hrπ : r < π
  · rw [setLAverage_eq]
    rw [heq r hrπ.le]
    have h1 := TauCeti.setLAverage_le_maximalFunction volume g θ hr
    rw [setLAverage_eq] at h1
    calc (∫⁻ y in ball θ r, ‖g y‖ₑ) / volume (ball θ r) ≤ Mg := h1
      _ ≤ 2 * Mg := by
        rw [two_mul]; exact le_add_self
  · have hrπ' : π ≤ r := not_lt.mp hrπ
    -- one period
    have hI : ∫⁻ y in Ioc 0 (2 * π), ‖f y‖ₑ = ∫⁻ y in ball θ π, ‖g y‖ₑ := by
      have hper' : ∀ t, ‖f (t + 2 * π)‖ₑ = ‖f t‖ₑ := fun t => by rw [hper t]
      have := s07c_fkps_m2_lint_period (fun y => ‖f y‖ₑ) hper' (θ - π)
      rw [← heq π le_rfl, ← this, Real.ball_eq_Ioo, show θ - π + 2 * π = θ + π by ring]
      exact setLIntegral_congr Ioo_ae_eq_Ioc.symm
    have hπavg := TauCeti.setLAverage_le_maximalFunction volume g θ hpi
    rw [setLAverage_eq, Real.volume_ball] at hπavg
    have hIle : ∫⁻ y in Ioc 0 (2 * π), ‖f y‖ₑ ≤ ENNReal.ofReal (2 * π) * Mg := by
      rw [hI]
      have hne0 : ENNReal.ofReal (2 * π) ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
      rw [ENNReal.div_le_iff hne0 ENNReal.ofReal_ne_top] at hπavg
      rw [mul_comm]; exact hπavg
    -- cover the ball by `N` periods
    set N : ℕ := ⌈r / π⌉₊ with hNdef
    have hN1 : r / π ≤ N := Nat.le_ceil _
    have hN2 : (N : ℝ) < r / π + 1 := Nat.ceil_lt_add_one (by positivity)
    have hcover : ball θ r ⊆ Ioc (θ - r) (θ - r + 2 * π * N) := by
      intro x hx
      rw [Real.ball_eq_Ioo] at hx
      refine ⟨hx.1, ?_⟩
      have : r ≤ π * N := by
        have := (div_le_iff₀ hpi).mp hN1
        linarith
      linarith [hx.2]
    have hper' : ∀ t, ‖f (t + 2 * π)‖ₑ = ‖f t‖ₑ := fun t => by rw [hper t]
    have hball : ∫⁻ y in ball θ r, ‖f y‖ₑ ≤ N * (ENNReal.ofReal (2 * π) * Mg) := by
      calc ∫⁻ y in ball θ r, ‖f y‖ₑ ≤ ∫⁻ y in Ioc (θ - r) (θ - r + 2 * π * N), ‖f y‖ₑ :=
            lintegral_mono_set hcover
        _ = N * ∫⁻ y in Ioc 0 (2 * π), ‖f y‖ₑ :=
            s07c_fkps_m2_lint_periods (fun y => ‖f y‖ₑ) hper' (θ - r) N
        _ ≤ N * (ENNReal.ofReal (2 * π) * Mg) := by gcongr
    have hcount : (N : ℝ≥0∞) * ENNReal.ofReal (2 * π) ≤ 2 * ENNReal.ofReal (2 * r) := by
      have hNr : (N : ℝ) * (2 * π) ≤ 2 * (2 * r) := by
        have h3 : (N : ℝ) ≤ 2 * r / π := by
          have : r / π + 1 ≤ 2 * r / π := by
            rw [show 2 * r / π = r / π + r / π by ring]
            have : 1 ≤ r / π := (one_le_div hpi).mpr hrπ'
            linarith
          linarith
        have := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ 2 * π)
        calc (N : ℝ) * (2 * π) ≤ 2 * r / π * (2 * π) := this
          _ = 2 * (2 * r) := by field_simp
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
        show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal hNr
    rw [setLAverage_eq, Real.volume_ball]
    have hne0 : ENNReal.ofReal (2 * r) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
    rw [ENNReal.div_le_iff hne0 ENNReal.ofReal_ne_top]
    calc ∫⁻ y in ball θ r, ‖f y‖ₑ ≤ N * (ENNReal.ofReal (2 * π) * Mg) := hball
      _ = ((N : ℝ≥0∞) * ENNReal.ofReal (2 * π)) * Mg := by ring
      _ ≤ (2 * ENNReal.ofReal (2 * r)) * Mg := by gcongr
      _ = 2 * Mg * ENNReal.ofReal (2 * r) := by ring

/-- M2.2 (Hardy–Littlewood on `𝕋`): the maximal function of a periodic `f` is bounded in `L²` of one
period. -/
theorem s07c_fkps_m2_maxL2 : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : ℝ → ℝ, Measurable f →
    (∀ t, f (t + 2 * π) = f t) →
    ∫⁻ θ in Icc 0 (2 * π), TauCeti.maximalFunction volume f θ ^ 2 ≤
      C * ∫⁻ θ in Icc 0 (2 * π), ‖f θ‖ₑ ^ 2 := by
  set CHL : ℝ≥0∞ := ENNReal.ofReal (2 * 2 * 2 ^ ((2 : ℝ) - 1) / ((2 : ℝ) - 1)) *
    4 ^ Module.finrank ℝ ℝ with hCHL
  refine ⟨8 * CHL, ?_, ?_⟩
  · rw [hCHL]
    exact ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp))
  intro f hf hper
  have hpi : 0 < π := Real.pi_pos
  set g := indicator (Ioc (-π) (3 * π)) f with hgdef
  have hgm : Measurable g := hf.indicator measurableSet_Ioc
  have hHL := TauCeti.lintegral_rpow_maximalFunction_le volume (f := g)
    hgm.enorm.aemeasurable (p := 2) (by norm_num)
  simp only [ENNReal.rpow_two] at hHL
  have hgsq : ∫⁻ x, ‖g x‖ₑ ^ 2 = ∫⁻ x in Ioc (-π) (3 * π), ‖f x‖ₑ ^ 2 := by
    rw [← lintegral_indicator measurableSet_Ioc]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Ioc (-π) (3 * π)
    · rw [hgdef, indicator_of_mem hx, indicator_of_mem hx]
    · rw [hgdef, indicator_of_notMem hx, indicator_of_notMem hx]
      simp
  have hper2 : ∀ t, ‖f (t + 2 * π)‖ₑ ^ 2 = ‖f t‖ₑ ^ 2 := fun t => by rw [hper t]
  have htwo := s07c_fkps_m2_lint_periods (fun x => ‖f x‖ₑ ^ 2) hper2 (-π) 2
  rw [show -π + 2 * π * ((2 : ℕ) : ℝ) = 3 * π by push_cast; ring] at htwo
  calc ∫⁻ θ in Icc 0 (2 * π), TauCeti.maximalFunction volume f θ ^ 2
      ≤ ∫⁻ θ in Icc 0 (2 * π), (2 * TauCeti.maximalFunction volume g θ) ^ 2 := by
        refine setLIntegral_mono' measurableSet_Icc fun θ hθ => ?_
        gcongr
        exact s07c_fkps_m2_max_local f hper θ hθ
    _ = 4 * ∫⁻ θ in Icc 0 (2 * π), TauCeti.maximalFunction volume g θ ^ 2 := by
        rw [← lintegral_const_mul' _ _ (by norm_num)]
        refine lintegral_congr fun θ => ?_
        rw [mul_pow]; norm_num
    _ ≤ 4 * ∫⁻ θ, TauCeti.maximalFunction volume g θ ^ 2 := by
        gcongr; exact Measure.restrict_le_self
    _ ≤ 4 * (CHL * ∫⁻ x, ‖g x‖ₑ ^ 2) := by gcongr
    _ = 4 * (CHL * (2 * ∫⁻ x in Ioc 0 (2 * π), ‖f x‖ₑ ^ 2)) := by
        rw [hgsq, htwo]; norm_num
    _ ≤ 4 * (CHL * (2 * ∫⁻ x in Icc 0 (2 * π), ‖f x‖ₑ ^ 2)) := by
        gcongr; exact Ioc_subset_Icc_self
    _ = 8 * CHL * ∫⁻ θ in Icc 0 (2 * π), ‖f θ‖ₑ ^ 2 := by ring

/-- Cone bound for the Poisson kernel: on `Γ_α(θ)`, with `δ = 1 - |z|` and `|t - θ| ≤ π`,
`P(z, t) ≤ ((α + 2)² π² / 2) · δ / (δ + |t - θ|)²`. -/
theorem s07c_fkps_m2_cone_kernel (α : ℝ) (hα : 0 < α) (θ : ℝ) (z : ℂ) (hz : z ∈ unitDisc)
    (hc : ‖z - Complex.exp (θ * I)‖ < α * (1 - ‖z‖)) (t : ℝ) (ht : |t - θ| ≤ π) :
    (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 ≤
      (α + 2) ^ 2 * π ^ 2 / 2 * ((1 - ‖z‖) / ((1 - ‖z‖) + |t - θ|) ^ 2) := by
  have hpi : 0 < π := Real.pi_pos
  have hz1 : ‖z‖ < 1 := by simpa [unitDisc, mem_ball_zero_iff] using hz
  set δ : ℝ := 1 - ‖z‖ with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set s : ℝ := |t - θ| with hsdef
  have hs0 : 0 ≤ s := abs_nonneg _
  set E : ℝ := ‖Complex.exp (t * I) - z‖ with hEdef
  have hE1 : δ ≤ E := by
    have := norm_sub_norm_le (Complex.exp (t * I)) z
    rw [Complex.norm_exp_ofReal_mul_I] at this
    rw [hδdef, hEdef]; exact this
  have hE2 : 2 / π * s - α * δ ≤ E := by
    have hch := s07c_fkps_m2_chord (t - θ) ht
    rw [← s07c_fkps_m2_chord_shift] at hch
    have htri : ‖Complex.exp (t * I) - Complex.exp (θ * I)‖ ≤ E + ‖z - Complex.exp (θ * I)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [hsdef]
    linarith
  have h2pi : 2 / π ≤ 1 := by
    rw [div_le_one hpi]; linarith [Real.pi_gt_three]
  have hD : 2 / π * (δ + s) ≤ (α + 2) * E := by
    have h1 : 0 ≤ α * (E - δ) := mul_nonneg hα.le (by linarith)
    have h2 : 2 / π * δ ≤ δ := by
      have := mul_le_mul_of_nonneg_right h2pi hδ.le
      linarith
    nlinarith
  have hDpos : 0 < 2 / π * (δ + s) := by positivity
  have hEpos : 0 < E := lt_of_lt_of_le hδ hE1
  have hnum : 1 - ‖z‖ ^ 2 ≤ 2 * δ := by
    have h0 : 0 ≤ ‖z‖ := norm_nonneg z
    rw [hδdef]; nlinarith
  have hsq : (2 / π * (δ + s)) ^ 2 ≤ ((α + 2) * E) ^ 2 :=
    pow_le_pow_left₀ hDpos.le hD 2
  have hα2 : 0 < (α + 2) ^ 2 := by positivity
  calc (1 - ‖z‖ ^ 2) / E ^ 2 ≤ (2 * δ) / E ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = (α + 2) ^ 2 * (2 * δ) / ((α + 2) * E) ^ 2 := by
        rw [mul_pow]; field_simp
    _ ≤ (α + 2) ^ 2 * (2 * δ) / (2 / π * (δ + s)) ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
    _ = (α + 2) ^ 2 * π ^ 2 / 2 * (δ / (δ + s) ^ 2) := by
        field_simp

/-- Dyadic majorant of `δ / (δ + |s|)²`. -/
theorem s07c_fkps_m2_dyadic (δ : ℝ) (hδ : 0 < δ) (s : ℝ) :
    ENNReal.ofReal (δ / (δ + |s|) ^ 2) ≤
      ∑' k : ℕ, (ball (0 : ℝ) (2 ^ k * δ)).indicator
        (fun _ => ENNReal.ofReal (4 / (4 ^ k * δ))) s := by
  have hs0 : 0 ≤ |s| := abs_nonneg s
  by_cases hsm : |s| < δ
  · have hmem : s ∈ ball (0 : ℝ) (2 ^ 0 * δ) := by
      rw [mem_ball, Real.dist_eq, sub_zero, pow_zero, one_mul]; exact hsm
    refine le_trans ?_ (ENNReal.le_tsum 0)
    rw [indicator_of_mem hmem]
    apply ENNReal.ofReal_le_ofReal
    rw [pow_zero, one_mul]
    rw [div_le_div_iff₀ (by positivity) hδ]
    nlinarith
  · have hge : 1 ≤ |s| / δ := by
      rw [le_div_iff₀ hδ]; linarith [not_lt.mp hsm]
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hge (by norm_num : (1 : ℝ) < 2)
    have hmem : s ∈ ball (0 : ℝ) (2 ^ (n + 1) * δ) := by
      rw [mem_ball, Real.dist_eq, sub_zero]
      have := (div_lt_iff₀ hδ).mp hn2
      linarith
    refine le_trans ?_ (ENNReal.le_tsum (n + 1))
    rw [indicator_of_mem hmem]
    apply ENNReal.ofReal_le_ofReal
    have hlow : 2 ^ n * δ ≤ |s| := (le_div_iff₀ hδ).mp hn1
    have h2n : 0 < (2 : ℝ) ^ n := by positivity
    have hden : (2 ^ n * δ) ^ 2 ≤ (δ + |s|) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    calc δ / (δ + |s|) ^ 2 ≤ δ / (2 ^ n * δ) ^ 2 :=
          div_le_div_of_nonneg_left hδ.le (by positivity) hden
      _ = 4 / (4 ^ (n + 1) * δ) := by
          rw [pow_succ, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
          field_simp
          ring

/-- Averaging a dyadic piece against `|h|` is controlled by the maximal function. -/
theorem s07c_fkps_m2_dyadic_avg (δ : ℝ) (hδ : 0 < δ) (k : ℕ) (h : ℝ → ℝ) (θ : ℝ)
    (S : Set ℝ) :
    ∫⁻ t in S, (ball (0 : ℝ) (2 ^ k * δ)).indicator
        (fun _ => ENNReal.ofReal (4 / (4 ^ k * δ))) (t - θ) * ‖h t‖ₑ ≤
      ENNReal.ofReal (8 / 2 ^ k) * TauCeti.maximalFunction volume h θ := by
  have hr : 0 < 2 ^ k * δ := by positivity
  have hpt : ∀ t, (ball (0 : ℝ) (2 ^ k * δ)).indicator
      (fun _ => ENNReal.ofReal (4 / (4 ^ k * δ))) (t - θ) * ‖h t‖ₑ =
      (ball θ (2 ^ k * δ)).indicator (fun t => ENNReal.ofReal (4 / (4 ^ k * δ)) * ‖h t‖ₑ) t := by
    intro t
    by_cases ht : t ∈ ball θ (2 ^ k * δ)
    · have ht' : t - θ ∈ ball (0 : ℝ) (2 ^ k * δ) := by
        rw [mem_ball, Real.dist_eq, sub_zero]; rw [mem_ball, Real.dist_eq] at ht; exact ht
      rw [indicator_of_mem ht', indicator_of_mem ht]
    · have ht' : t - θ ∉ ball (0 : ℝ) (2 ^ k * δ) := by
        rw [mem_ball, Real.dist_eq, sub_zero]; rw [mem_ball, Real.dist_eq] at ht; exact ht
      rw [indicator_of_notMem ht', indicator_of_notMem ht, zero_mul]
  have hav := TauCeti.setLAverage_le_maximalFunction volume h θ hr
  rw [setLAverage_eq, Real.volume_ball] at hav
  have hne0 : ENNReal.ofReal (2 * (2 ^ k * δ)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  rw [ENNReal.div_le_iff hne0 ENNReal.ofReal_ne_top] at hav
  calc ∫⁻ t in S, (ball (0 : ℝ) (2 ^ k * δ)).indicator
        (fun _ => ENNReal.ofReal (4 / (4 ^ k * δ))) (t - θ) * ‖h t‖ₑ
      ≤ ∫⁻ t, (ball (0 : ℝ) (2 ^ k * δ)).indicator
        (fun _ => ENNReal.ofReal (4 / (4 ^ k * δ))) (t - θ) * ‖h t‖ₑ :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ t in ball θ (2 ^ k * δ), ENNReal.ofReal (4 / (4 ^ k * δ)) * ‖h t‖ₑ := by
        simp_rw [hpt]
        exact lintegral_indicator measurableSet_ball _
    _ = ENNReal.ofReal (4 / (4 ^ k * δ)) * ∫⁻ t in ball θ (2 ^ k * δ), ‖h t‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (4 / (4 ^ k * δ)) *
          (TauCeti.maximalFunction volume h θ * ENNReal.ofReal (2 * (2 ^ k * δ))) := by
        gcongr
    _ = ENNReal.ofReal (4 / (4 ^ k * δ)) * ENNReal.ofReal (2 * (2 ^ k * δ)) *
          TauCeti.maximalFunction volume h θ := by ring
    _ = ENNReal.ofReal (4 / (4 ^ k * δ) * (2 * (2 ^ k * δ))) *
          TauCeti.maximalFunction volume h θ := by
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 / (4 ^ k * δ))]
    _ = ENNReal.ofReal (8 / 2 ^ k) * TauCeti.maximalFunction volume h θ := by
        congr 2
        rw [show (4 : ℝ) ^ k = 2 ^ k * 2 ^ k by rw [← mul_pow]; norm_num]
        field_simp
        ring

/-- `∑ₖ 8 / 2ᵏ = 16` in `ℝ≥0∞`. -/
theorem s07c_fkps_m2_tsum_eight : ∑' k : ℕ, ENNReal.ofReal (8 / 2 ^ k) = 16 := by
  have h : ∀ k : ℕ, ENNReal.ofReal (8 / 2 ^ k) = 8 * 2⁻¹ ^ k := by
    intro k
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (by norm_num), ← inv_pow,
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  simp_rw [h]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  norm_num

/-- Nontangential control in `lintegral` form, any aperture `α > 0` (also used by M4/M5):
on `Γ_α(θ)`, `(2π)⁻¹ ∫₀^{2π} P(z, t) |h(t)| dt ≤ C · M h(θ)`. -/
theorem s07c_fkps_m2_nt_lint (α : ℝ) (hα : 0 < α) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ h : ℝ → ℝ,
    Measurable h → (∀ t, h (t + 2 * π) = h t) → ∀ (θ : ℝ) (z : ℂ), z ∈ unitDisc →
    ‖z - Complex.exp (θ * I)‖ < α * (1 - ‖z‖) →
    ENNReal.ofReal (2 * π)⁻¹ * ∫⁻ t in Icc 0 (2 * π),
      ENNReal.ofReal ((1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2) * ‖h t‖ₑ ≤
      C * TauCeti.maximalFunction volume h θ := by
  have hpi : 0 < π := Real.pi_pos
  set Cα : ℝ := (α + 2) ^ 2 * π ^ 2 / 2 with hCα
  refine ⟨ENNReal.ofReal (2 * π)⁻¹ * ENNReal.ofReal Cα * 16,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (by norm_num), ?_⟩
  intro h hh hper θ z hz hc
  have hz1 : ‖z‖ < 1 := by simpa [unitDisc, mem_ball_zero_iff] using hz
  set δ : ℝ := 1 - ‖z‖ with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set Pk : ℝ → ℝ≥0∞ := fun t =>
    ENNReal.ofReal ((1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2) * ‖h t‖ₑ with hPk
  have hPper : ∀ t, Pk (t + 2 * π) = Pk t := by
    intro t
    simp only [hPk]
    rw [s07c_fkps_m2_exp_periodic t, hper t]
  -- move to the period centred at `θ`
  have hIcc : ∫⁻ t in Icc 0 (2 * π), Pk t = ∫⁻ t in Ioc (θ - π) (θ + π), Pk t := by
    rw [← setLIntegral_congr Ioc_ae_eq_Icc, ← s07c_fkps_m2_lint_period Pk hPper (θ - π),
      show θ - π + 2 * π = θ + π by ring]
  -- pointwise dyadic bound
  set T : ℕ → ℝ → ℝ≥0∞ := fun k t => (ball (0 : ℝ) (2 ^ k * δ)).indicator
      (fun _ => ENNReal.ofReal (4 / (4 ^ k * δ))) (t - θ) * ‖h t‖ₑ with hT
  have hpt : ∀ t ∈ Ioc (θ - π) (θ + π), Pk t ≤ ENNReal.ofReal Cα * ∑' k, T k t := by
    intro t ht
    have htθ : |t - θ| ≤ π := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    have h1 := s07c_fkps_m2_cone_kernel α hα θ z hz hc t htθ
    have h2 := s07c_fkps_m2_dyadic δ hδ (t - θ)
    simp only [hPk, hT]
    rw [ENNReal.tsum_mul_right, ← mul_assoc]
    gcongr
    calc ENNReal.ofReal ((1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2)
        ≤ ENNReal.ofReal (Cα * (δ / (δ + |t - θ|) ^ 2)) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal Cα * ENNReal.ofReal (δ / (δ + |t - θ|) ^ 2) :=
          ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal Cα * ∑' k : ℕ, (ball (0 : ℝ) (2 ^ k * δ)).indicator
            (fun _ => ENNReal.ofReal (4 / (4 ^ k * δ))) (t - θ) := by gcongr
  have hTm : ∀ k, AEMeasurable (T k) (volume.restrict (Ioc (θ - π) (θ + π))) := by
    intro k
    apply Measurable.aemeasurable
    simp only [hT]
    refine Measurable.mul ?_ hh.enorm
    exact (measurable_const.indicator measurableSet_ball).comp (measurable_id.sub_const θ)
  calc ENNReal.ofReal (2 * π)⁻¹ * ∫⁻ t in Icc 0 (2 * π), Pk t
      = ENNReal.ofReal (2 * π)⁻¹ * ∫⁻ t in Ioc (θ - π) (θ + π), Pk t := by rw [hIcc]
    _ ≤ ENNReal.ofReal (2 * π)⁻¹ *
          ∫⁻ t in Ioc (θ - π) (θ + π), ENNReal.ofReal Cα * ∑' k, T k t := by
        exact mul_le_mul_of_nonneg_left (setLIntegral_mono' measurableSet_Ioc hpt) (zero_le)
    _ = ENNReal.ofReal (2 * π)⁻¹ * (ENNReal.ofReal Cα *
          ∑' k, ∫⁻ t in Ioc (θ - π) (θ + π), T k t) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_tsum hTm]
    _ ≤ ENNReal.ofReal (2 * π)⁻¹ * (ENNReal.ofReal Cα *
          ∑' k : ℕ, ENNReal.ofReal (8 / 2 ^ k) * TauCeti.maximalFunction volume h θ) := by
        gcongr with k
        exact s07c_fkps_m2_dyadic_avg δ hδ k h θ _
    _ = ENNReal.ofReal (2 * π)⁻¹ * ENNReal.ofReal Cα * 16 *
          TauCeti.maximalFunction volume h θ := by
        rw [ENNReal.tsum_mul_right, s07c_fkps_m2_tsum_eight]
        ring

/-- M2.3 (nontangential control): on the cone `Γ(θ)`, `|P f| ≤ C · M f(θ)`. -/
theorem s07c_fkps_m2_nontangential : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : ℝ → ℝ, Measurable f →
    (∀ t, f (t + 2 * π) = f t) → ∀ (θ : ℝ) (z : ℂ), z ∈ unitDisc →
    ‖z - Complex.exp (θ * I)‖ < 2 * (1 - ‖z‖) →
    ENNReal.ofReal |(2 * π)⁻¹ *
      ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 * f t| ≤
      C * TauCeti.maximalFunction volume f θ := by
  obtain ⟨C, hC, hbound⟩ := s07c_fkps_m2_nt_lint 2 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro f hf hper θ z hz hc
  have hpi : 0 < π := Real.pi_pos
  have hK0 : ∀ t : ℝ, 0 ≤ (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 := by
    intro t
    have : ‖z‖ < 1 := by simpa [unitDisc, mem_ball_zero_iff] using hz
    have h0 : 0 ≤ ‖z‖ := norm_nonneg z
    apply div_nonneg _ (sq_nonneg _)
    nlinarith
  refine le_trans ?_ (hbound f hf hper θ z hz hc)
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹),
    ENNReal.ofReal_mul (by positivity), intervalIntegral.integral_of_le (by positivity)]
  gcongr
  rw [← Real.enorm_eq_ofReal_abs]
  refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
  refine le_of_eq ?_
  rw [setLIntegral_congr Ioc_ae_eq_Icc]
  refine lintegral_congr fun t => ?_
  rw [enorm_mul, Real.enorm_eq_ofReal (hK0 t)]

/-- The maximal function of a `2π`-periodic `f` is `2π`-periodic. -/
theorem s07c_fkps_m2_max_periodic (f : ℝ → ℝ) (hper : ∀ t, f (t + 2 * π) = f t) (θ : ℝ) :
    TauCeti.maximalFunction volume f (θ + 2 * π) = TauCeti.maximalFunction volume f θ := by
  have hball : ∀ r : ℝ, ∫⁻ y in ball (θ + 2 * π) r, ‖f y‖ₑ = ∫⁻ y in ball θ r, ‖f y‖ₑ := by
    intro r
    rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
    rw [← lintegral_add_right_eq_self (μ := volume)
      (fun y => (ball (θ + 2 * π) r).indicator (fun y => ‖f y‖ₑ) y) (2 * π)]
    refine lintegral_congr fun y => ?_
    have hiff : y + 2 * π ∈ ball (θ + 2 * π) r ↔ y ∈ ball θ r := by
      rw [mem_ball, mem_ball, Real.dist_eq, Real.dist_eq, show y + 2 * π - (θ + 2 * π) = y - θ by ring]
    by_cases hy : y ∈ ball θ r
    · rw [indicator_of_mem (hiff.mpr hy), indicator_of_mem hy, hper y]
    · rw [indicator_of_notMem (fun h => hy (hiff.mp h)), indicator_of_notMem hy]
  simp only [TauCeti.maximalFunction_def, setLAverage_eq, Real.volume_ball, hball]

/-- A Carleson measure gives finite mass to `𝔻`: `ν(𝔻) ≤ 2A`. -/
theorem s07c_fkps_m2_carleson_disc (ν : Measure ℂ) (A : ℝ≥0∞)
    (hcar : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ν (unitDisc ∩ ball ζ r) ≤ A * ENNReal.ofReal r) :
    ν unitDisc ≤ A * ENNReal.ofReal 2 := by
  set s : ℕ → Set ℂ := fun n => unitDisc ∩ ball (1 : ℂ) (2 - 1 / ((n : ℝ) + 2)) with hsdef
  have hmono : Monotone s := by
    intro m n hmn
    apply inter_subset_inter_right
    apply ball_subset_ball
    have h1 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have h2 : ((m : ℝ) + 2) ≤ (n : ℝ) + 2 := by
      have : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
      linarith
    have := one_div_le_one_div_of_le h1 h2
    linarith
  have hU : unitDisc = ⋃ n, s n := by
    ext z
    simp only [mem_iUnion, hsdef, mem_inter_iff]
    constructor
    · intro hz
      have hz1 : ‖z‖ < 1 := by simpa [unitDisc, mem_ball_zero_iff] using hz
      have hd : dist z 1 < 2 := by
        rw [dist_eq_norm]
        calc ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ < 2 := by rw [norm_one]; linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (2 - dist z 1))
      refine ⟨n, hz, ?_⟩
      rw [mem_ball]
      have hpos : 0 < 2 - dist z 1 := by linarith
      have h3 : 1 / ((n : ℝ) + 2) < 2 - dist z 1 := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hpos] at hn
        nlinarith
      linarith
    · intro h
      obtain ⟨n, hz, _⟩ := h
      exact hz
  rw [hU, hmono.measure_iUnion]
  refine iSup_le fun n => ?_
  have hr : 0 < 2 - 1 / ((n : ℝ) + 2) := by
    have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num); have := Nat.cast_nonneg (α := ℝ) n; linarith
    linarith
  have hr2 : 2 - 1 / ((n : ℝ) + 2) < 2 := by
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have h1 : (1 : ℂ) ∈ sphere (0 : ℂ) 1 := by simp
  calc ν (s n) ≤ A * ENNReal.ofReal (2 - 1 / ((n : ℝ) + 2)) := hcar 1 h1 _ hr hr2
    _ ≤ A * ENNReal.ofReal 2 := by
        gcongr

/-- The Carleson bound for every radius `r > 0`. -/
theorem s07c_fkps_m2_carleson_all (ν : Measure ℂ) (A : ℝ≥0∞)
    (hcar : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ν (unitDisc ∩ ball ζ r) ≤ A * ENNReal.ofReal r)
    (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) 1) (r : ℝ) (hr : 0 < r) :
    ν (unitDisc ∩ ball ζ r) ≤ A * ENNReal.ofReal r := by
  by_cases h2 : r < 2
  · exact hcar ζ hζ r hr h2
  · calc ν (unitDisc ∩ ball ζ r) ≤ ν unitDisc := measure_mono inter_subset_left
      _ ≤ A * ENNReal.ofReal 2 := s07c_fkps_m2_carleson_disc ν A hcar
      _ ≤ A * ENNReal.ofReal r := by
          gcongr
          linarith [not_lt.mp h2]

/-- A closed ball of `ℝ` inside another one has a smaller radius. -/
theorem s07c_fkps_m2_closedBall_radius (x y r R : ℝ) (hr : 0 ≤ r)
    (h : closedBall x r ⊆ closedBall y R) : r ≤ R := by
  have h1 := h (show x + r ∈ closedBall x r by
    rw [mem_closedBall, Real.dist_eq, show x + r - x = r by ring, abs_of_nonneg hr])
  have h2 := h (show x - r ∈ closedBall x r by
    rw [mem_closedBall, Real.dist_eq, show x - r - x = -r by ring, abs_neg, abs_of_nonneg hr])
  rw [mem_closedBall, Real.dist_eq, abs_le] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- `‖z - e^{i arg z}‖ = 1 - ‖z‖` for `‖z‖ ≤ 1`. -/
theorem s07c_fkps_m2_norm_sub_exp_arg (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖z - Complex.exp (Complex.arg z * I)‖ = 1 - ‖z‖ := by
  have h : z - Complex.exp (Complex.arg z * I) =
      ((‖z‖ : ℂ) - 1) * Complex.exp (Complex.arg z * I) := by
    have hz' := Complex.norm_mul_exp_arg_mul_I z
    linear_combination -hz'
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, ← ofReal_one, ← ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  ring

/-- Chord ≤ arc: `‖e^{ia} - e^{ib}‖ ≤ |a - b|`. -/
theorem s07c_fkps_m2_chord_le (a b : ℝ) :
    ‖Complex.exp (a * I) - Complex.exp (b * I)‖ ≤ |a - b| := by
  rw [s07c_fkps_m2_chord_shift, mul_comm]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  simpa [Real.norm_eq_abs] using this

/-- Points of the arc `|θ - arg z| ≤ (1 - |z|)/2` see `z` inside the cone of aperture `2`. -/
theorem s07c_fkps_m2_arc_cone (z : ℂ) (hz : z ∈ unitDisc) (θ : ℝ)
    (hθ : θ ∈ closedBall (Complex.arg z) ((1 - ‖z‖) / 2)) :
    ‖z - Complex.exp (θ * I)‖ < 2 * (1 - ‖z‖) := by
  have hz1 : ‖z‖ < 1 := by simpa [unitDisc, mem_ball_zero_iff] using hz
  rw [mem_closedBall, Real.dist_eq] at hθ
  have h1 := s07c_fkps_m2_norm_sub_exp_arg z hz1.le
  have h2 := s07c_fkps_m2_chord_le (Complex.arg z) θ
  have htri : ‖z - Complex.exp (θ * I)‖ ≤ ‖z - Complex.exp (Complex.arg z * I)‖ +
      ‖Complex.exp (Complex.arg z * I) - Complex.exp (θ * I)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  rw [abs_sub_comm] at hθ
  linarith

/-- Covering lemma: if every `z ∈ T ⊆ 𝔻` has its arc `closedBall (arg z) ((1-|z|)/2)` inside a
`2π`-periodic measurable `U`, then `ν T ≤ 14 A |U ∩ (0, 2π]|`. -/
theorem s07c_fkps_m2_cover (ν : Measure ℂ) (A : ℝ≥0∞)
    (hcar : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ν (unitDisc ∩ ball ζ r) ≤ A * ENNReal.ofReal r)
    (U : Set ℝ) (hU : MeasurableSet U) (hUper : ∀ θ, θ + 2 * π ∈ U ↔ θ ∈ U)
    (T : Set ℂ) (hT : T ⊆ unitDisc)
    (hTU : ∀ z ∈ T, closedBall (Complex.arg z) ((1 - ‖z‖) / 2) ⊆ U) :
    ν T ≤ 14 * A * volume (U ∩ Ioc 0 (2 * π)) := by
  have hpi : 0 < π := Real.pi_pos
  have hpi3 : 3 < π := Real.pi_gt_three
  set x : ℂ → ℝ := fun z => Complex.arg z with hxdef
  set r : ℂ → ℝ := fun z => (1 - ‖z‖) / 2 with hrdef
  have hrpos : ∀ z ∈ T, 0 < r z := by
    intro z hz
    have : ‖z‖ < 1 := by simpa [unitDisc, mem_ball_zero_iff] using hT hz
    simp only [hrdef]; linarith
  have hrle : ∀ z ∈ T, r z ≤ 1 := by
    intro z _
    simp only [hrdef]; linarith [norm_nonneg z]
  obtain ⟨u, huT, hdisj, hcov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall T x r 1 hrle 4 (by norm_num)
  -- countability
  have hdisj' : u.PairwiseDisjoint fun b => ball (x b) (r b) :=
    hdisj.mono fun b => ball_subset_closedBall
  have hcount : u.Countable :=
    hdisj'.countable_of_isOpen (fun _ _ => isOpen_ball)
      (fun b hb => nonempty_ball.mpr (hrpos b (huT hb)))
  -- `T` is covered by the enlarged Carleson boxes
  have hsub : T ⊆ ⋃ b ∈ u, unitDisc ∩ ball (Complex.exp (x b * I)) (7 * (1 - ‖b‖)) := by
    intro z hz
    obtain ⟨b, hbu, hzb⟩ := hcov z hz
    have hb : b ∈ T := huT hbu
    have hrz := s07c_fkps_m2_closedBall_radius _ _ _ _ (hrpos z hz).le hzb
    have hxz : x z ∈ closedBall (x b) (4 * r b) := hzb (mem_closedBall_self (hrpos z hz).le)
    rw [mem_closedBall, Real.dist_eq] at hxz
    have hz1 : ‖z‖ < 1 := by simpa [unitDisc, mem_ball_zero_iff] using hT hz
    have h1 := s07c_fkps_m2_norm_sub_exp_arg z hz1.le
    have h2 := s07c_fkps_m2_chord_le (x z) (x b)
    have htri : ‖z - Complex.exp (x b * I)‖ ≤ ‖z - Complex.exp (x z * I)‖ +
        ‖Complex.exp (x z * I) - Complex.exp (x b * I)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have hrb := hrpos b hb
    simp only [hrdef] at hrz hxz hrb
    refine mem_iUnion₂.mpr ⟨b, hbu, hT hz, ?_⟩
    rw [mem_ball, dist_eq_norm]
    simp only [hxdef] at h2 htri hxz ⊢
    linarith
  -- measure bound
  have hboxes : ν T ≤ ∑' b : u, A * ENNReal.ofReal (7 * (1 - ‖(b : ℂ)‖)) := by
    calc ν T ≤ ν (⋃ b ∈ u, unitDisc ∩ ball (Complex.exp (x b * I)) (7 * (1 - ‖b‖))) :=
          measure_mono hsub
      _ ≤ ∑' b : u, ν (unitDisc ∩ ball (Complex.exp (x b * I)) (7 * (1 - ‖(b : ℂ)‖))) :=
          measure_biUnion_le ν hcount _
      _ ≤ ∑' b : u, A * ENNReal.ofReal (7 * (1 - ‖(b : ℂ)‖)) := by
          refine ENNReal.tsum_le_tsum fun b => ?_
          have hb := hrpos b (huT b.2)
          simp only [hrdef] at hb
          refine s07c_fkps_m2_carleson_all ν A hcar _ ?_ _ (by linarith)
          simp [Complex.norm_exp_ofReal_mul_I]
  have harcs : ∑' b : u, ENNReal.ofReal (1 - ‖(b : ℂ)‖) =
      volume (⋃ b ∈ u, closedBall (x b) (r b)) := by
    rw [measure_biUnion hcount hdisj (fun _ _ => measurableSet_closedBall)]
    refine tsum_congr fun b => ?_
    rw [Real.volume_closedBall]
    simp only [hrdef]
    congr 1; ring
  have hwin : (⋃ b ∈ u, closedBall (x b) (r b)) ⊆ U ∩ Ioc (-2 * π) (-2 * π + 2 * π * (2 : ℕ)) := by
    intro θ hθ
    obtain ⟨b, hbu, hθb⟩ := mem_iUnion₂.mp hθ
    have hb := huT hbu
    refine ⟨hTU b hb hθb, ?_⟩
    rw [mem_closedBall, Real.dist_eq, abs_le] at hθb
    have ha1 := Complex.neg_pi_lt_arg b
    have ha2 := Complex.arg_le_pi b
    have hrb := hrle b hb
    simp only [hxdef, hrdef] at hθb hrb
    constructor
    · linarith [hθb.1]
    · push_cast; linarith [hθb.2]
  have hper1 : ∀ t, U.indicator (fun _ => (1 : ℝ≥0∞)) (t + 2 * π) =
      U.indicator (fun _ => (1 : ℝ≥0∞)) t := by
    intro t
    by_cases ht : t ∈ U
    · rw [indicator_of_mem ((hUper t).mpr ht), indicator_of_mem ht]
    · rw [indicator_of_notMem (fun h => ht ((hUper t).mp h)), indicator_of_notMem ht]
  have htwo := s07c_fkps_m2_lint_periods (U.indicator fun _ => (1 : ℝ≥0∞)) hper1 (-2 * π) 2
  rw [lintegral_indicator_const hU, lintegral_indicator_const hU, one_mul, one_mul,
    Measure.restrict_apply hU, Measure.restrict_apply hU] at htwo
  have hvol : volume (⋃ b ∈ u, closedBall (x b) (r b)) ≤ 2 * volume (U ∩ Ioc 0 (2 * π)) := by
    calc volume (⋃ b ∈ u, closedBall (x b) (r b))
        ≤ volume (U ∩ Ioc (-2 * π) (-2 * π + 2 * π * (2 : ℕ))) := measure_mono hwin
      _ = 2 * volume (U ∩ Ioc 0 (2 * π)) := by
          rw [htwo]; norm_num
  calc ν T ≤ ∑' b : u, A * ENNReal.ofReal (7 * (1 - ‖(b : ℂ)‖)) := hboxes
    _ = 7 * A * ∑' b : u, ENNReal.ofReal (1 - ‖(b : ℂ)‖) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun b => ?_
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
        ring
    _ ≤ 7 * A * (2 * volume (U ∩ Ioc 0 (2 * π))) := by rw [harcs]; gcongr
    _ = 14 * A * volume (U ∩ Ioc 0 (2 * π)) := by ring

/-- Layer cake inequality for `ℝ≥0∞`-valued functions. -/
theorem s07c_fkps_m2_layercake {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ≥0∞)
    (hg : AEMeasurable g μ) :
    ∫⁻ s in Ioi (0 : ℝ), μ {a | ENNReal.ofReal s < g a} ≤ ∫⁻ a, g a ∂μ := by
  by_cases htop : μ {a | g a = ⊤} = 0
  · have hG : ∫⁻ a, ENNReal.ofReal ((g a).toReal) ∂μ =
        ∫⁻ s in Ioi (0 : ℝ), μ {a | s < (g a).toReal} :=
      lintegral_eq_lintegral_meas_lt μ (ae_of_all _ fun a => ENNReal.toReal_nonneg)
        hg.ennreal_toReal
    have hle : ∀ s : ℝ, 0 < s → μ {a | ENNReal.ofReal s < g a} ≤ μ {a | s < (g a).toReal} := by
      intro s hs
      calc μ {a | ENNReal.ofReal s < g a} ≤ μ ({a | s < (g a).toReal} ∪ {a | g a = ⊤}) := by
            apply measure_mono
            intro a ha
            simp only [mem_setOf_eq] at ha
            by_cases hga : g a = ⊤
            · exact Or.inr hga
            · left
              simp only [mem_setOf_eq]
              rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs.le, ENNReal.ofReal_toReal hga]
              exact ha
        _ ≤ μ {a | s < (g a).toReal} + μ {a | g a = ⊤} := measure_union_le _ _
        _ = μ {a | s < (g a).toReal} := by rw [htop, add_zero]
    calc ∫⁻ s in Ioi (0 : ℝ), μ {a | ENNReal.ofReal s < g a}
        ≤ ∫⁻ s in Ioi (0 : ℝ), μ {a | s < (g a).toReal} :=
          setLIntegral_mono' measurableSet_Ioi fun s hs => hle s hs
      _ = ∫⁻ a, ENNReal.ofReal ((g a).toReal) ∂μ := hG.symm
      _ ≤ ∫⁻ a, g a ∂μ := lintegral_mono fun a => ENNReal.ofReal_toReal_le
  · rw [lintegral_eq_top_of_measure_eq_top_ne_zero hg htop]
    exact le_top

/-- Measurability of the Poisson integral in the pole. -/
theorem s07c_fkps_m2_poisson_measurable (f : ℝ → ℝ) (hf : Measurable f) :
    Measurable fun z : ℂ => (2 * π)⁻¹ *
      ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 * f t := by
  refine Measurable.const_mul ?_ _
  have h2 : (0 : ℝ) ≤ 2 * π := by positivity
  simp_rw [intervalIntegral.integral_of_le h2]
  have hm : StronglyMeasurable (Function.uncurry fun (z : ℂ) (t : ℝ) =>
      (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 * f t) := by
    apply Measurable.stronglyMeasurable
    refine Measurable.mul ?_ (hf.comp measurable_snd)
    refine Measurable.div ?_ ?_
    · exact (measurable_const.sub ((continuous_norm.measurable.comp measurable_fst).pow_const 2))
    · refine (Measurable.pow_const ?_ 2)
      refine continuous_norm.measurable.comp ?_
      refine Measurable.sub ?_ measurable_fst
      exact (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp measurable_snd).mul_const I))
  exact (hm.integral_prod_right (ν := volume.restrict (Ioc 0 (2 * π)))).measurable

/-- M2.4 (Carleson embedding): if `ν(𝔻 ∩ D(ζ, r)) ≤ A r` for `ζ ∈ 𝕋`, `0 < r < 2`, then
`∫_𝔻 |P f|² dν ≤ C A ∫₀^{2π} |f|²`. -/
theorem s07c_fkps_m2_carleson : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (ν : Measure ℂ) (A : ℝ≥0∞),
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 → ν (unitDisc ∩ ball ζ r) ≤ A * ENNReal.ofReal r) →
    ∀ f : ℝ → ℝ, Measurable f → (∀ t, f (t + 2 * π) = f t) →
    ∫⁻ z in unitDisc, ‖(2 * π)⁻¹ *
      ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 * f t‖ₑ ^ 2 ∂ν ≤
      C * A * ∫⁻ θ in Icc 0 (2 * π), ‖f θ‖ₑ ^ 2 := by
  obtain ⟨C₂, hC₂, hNT⟩ := s07c_fkps_m2_nontangential
  obtain ⟨CH, hCH, hHL⟩ := s07c_fkps_m2_maxL2
  refine ⟨14 * C₂ ^ 2 * CH, ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
    (ENNReal.pow_ne_top hC₂)) hCH, ?_⟩
  intro ν A hcar f hf hper
  set F : ℂ → ℝ := fun z => (2 * π)⁻¹ *
      ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 * f t with hFdef
  have hFm : Measurable F := s07c_fkps_m2_poisson_measurable f hf
  set g : ℝ → ℝ≥0∞ := fun θ => (C₂ * TauCeti.maximalFunction volume f θ) ^ 2 with hgdef
  have hgm : Measurable g :=
    (measurable_const.mul (TauCeti.measurable_maximalFunction volume f)).pow_const 2
  have hgper : ∀ θ, g (θ + 2 * π) = g θ := by
    intro θ; simp only [hgdef]; rw [s07c_fkps_m2_max_periodic f hper θ]
  -- layer cake on the disc side
  have hL : ∫⁻ z in unitDisc, ‖F z‖ₑ ^ 2 ∂ν =
      ∫⁻ s in Ioi (0 : ℝ), (ν.restrict unitDisc) {z | s < F z ^ 2} := by
    rw [← lintegral_eq_lintegral_meas_lt (ν.restrict unitDisc)
      (ae_of_all _ fun z => sq_nonneg (F z)) (hFm.pow_const 2).aemeasurable]
    refine lintegral_congr fun z => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  -- the level-set comparison
  have hlev : ∀ s : ℝ, 0 < s → (ν.restrict unitDisc) {z | s < F z ^ 2} ≤
      14 * A * (volume.restrict (Ioc 0 (2 * π))) {θ | ENNReal.ofReal s < g θ} := by
    intro s hs
    have hUm : MeasurableSet {θ | ENNReal.ofReal s < g θ} := measurableSet_lt measurable_const hgm
    rw [Measure.restrict_apply' (show MeasurableSet unitDisc from measurableSet_ball),
      Measure.restrict_apply hUm]
    apply s07c_fkps_m2_cover ν A hcar _ hUm
    · intro θ; simp only [mem_setOf_eq, hgper θ]
    · exact inter_subset_right
    · intro z hz θ hθ
      have hzd : z ∈ unitDisc := hz.2
      have hcone := s07c_fkps_m2_arc_cone z hzd θ hθ
      have hnt := hNT f hf hper θ z hzd hcone
      simp only [mem_setOf_eq]
      have hFz : s < F z ^ 2 := hz.1
      have h1 : ENNReal.ofReal s < ENNReal.ofReal (F z ^ 2) :=
        (ENNReal.ofReal_lt_ofReal_iff (lt_trans hs hFz)).mpr hFz
      calc ENNReal.ofReal s < ENNReal.ofReal (F z ^ 2) := h1
        _ = ENNReal.ofReal |F z| ^ 2 := by
            rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
        _ ≤ g θ := by simp only [hgdef]; gcongr
  have hmeas : Measurable fun s : ℝ =>
      (volume.restrict (Ioc 0 (2 * π))) {θ | ENNReal.ofReal s < g θ} := by
    apply Antitone.measurable
    intro s₁ s₂ h12
    apply measure_mono
    intro θ hθ
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal h12) hθ
  calc ∫⁻ z in unitDisc, ‖F z‖ₑ ^ 2 ∂ν
      = ∫⁻ s in Ioi (0 : ℝ), (ν.restrict unitDisc) {z | s < F z ^ 2} := hL
    _ ≤ ∫⁻ s in Ioi (0 : ℝ), 14 * A *
          (volume.restrict (Ioc 0 (2 * π))) {θ | ENNReal.ofReal s < g θ} :=
        setLIntegral_mono' measurableSet_Ioi hlev
    _ = 14 * A * ∫⁻ s in Ioi (0 : ℝ),
          (volume.restrict (Ioc 0 (2 * π))) {θ | ENNReal.ofReal s < g θ} :=
        lintegral_const_mul _ hmeas
    _ ≤ 14 * A * ∫⁻ θ in Ioc 0 (2 * π), g θ :=
        mul_le_mul_of_nonneg_left (s07c_fkps_m2_layercake _ g hgm.aemeasurable) zero_le
    _ ≤ 14 * A * ∫⁻ θ in Icc 0 (2 * π), g θ := by
        gcongr; exact Ioc_subset_Icc_self
    _ = 14 * A * (C₂ ^ 2 * ∫⁻ θ in Icc 0 (2 * π), TauCeti.maximalFunction volume f θ ^ 2) := by
        rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top hC₂)]
        congr 1
        refine lintegral_congr fun θ => ?_
        simp only [hgdef]; rw [mul_pow]
    _ ≤ 14 * A * (C₂ ^ 2 * (CH * ∫⁻ θ in Icc 0 (2 * π), ‖f θ‖ₑ ^ 2)) := by
        gcongr; exact hHL f hf hper
    _ = 14 * C₂ ^ 2 * CH * A * ∫⁻ θ in Icc 0 (2 * π), ‖f θ‖ₑ ^ 2 := by ring

/-- M2.5 helper: the Herglotz kernel as a geometric series, `(e^{it}+w)/(e^{it}-w) = Σ eₙ (w e^{-it})ⁿ`. -/
theorem s07c_fkps_m2_lp_kernel_hasSum (w : ℂ) (hw : ‖w‖ < 1) (t : ℝ) :
    HasSum (fun n : ℕ => (if n = 0 then (1 : ℂ) else 2) * (w * Complex.exp (-(t * I))) ^ n)
      ((Complex.exp (t * I) + w) / (Complex.exp (t * I) - w)) := by
  have he : Complex.exp (t * I) ≠ 0 := Complex.exp_ne_zero _
  have hen : ‖Complex.exp (t * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I t
  have hq : ‖w * Complex.exp (-(t * I))‖ < 1 := by
    rw [norm_mul, Complex.exp_neg, norm_inv, hen, inv_one, mul_one]
    exact hw
  have hew : Complex.exp (t * I) - w ≠ 0 := by
    intro h
    have h' : Complex.exp (t * I) = w := sub_eq_zero.mp h
    rw [← h', hen] at hw
    exact lt_irrefl _ hw
  have hg := hasSum_geometric_of_norm_lt_one hq
  have hs := (hg.mul_left 2).sub (hasSum_ite_eq 0 (1 : ℂ))
  convert hs using 1
  · funext n
    by_cases hn : n = 0
    · subst hn
      norm_num
    · simp only [hn, if_false, sub_zero]
  · have h1q : 1 - w * Complex.exp (-(t * I)) ≠ 0 := by
      intro h
      have h' : w * Complex.exp (-(t * I)) = 1 := (sub_eq_zero.mp h).symm
      rw [h', norm_one] at hq
      exact lt_irrefl _ hq
    rw [Complex.exp_neg] at h1q ⊢
    field_simp
    ring

/-- M2.5 helper: the Fourier coefficient on `[0, 2π]` in exponential form. -/
theorem s07c_fkps_m2_lp_coeff_eq (F : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos F n =
      ((2 * π)⁻¹ : ℂ) * ∫ t in (0 : ℝ)..2 * π, Complex.exp (-((n : ℂ) * t * I)) * F t := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [fourierCoeffOn_eq_integral F n Real.two_pi_pos, Complex.real_smul]
  congr 1
  · push_cast
    ring
  · refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [fourier_coe_apply, smul_eq_mul]
    congr 2
    push_cast
    field_simp
    ring

/-- M2.5 helper: the Poisson integral of an integrable `f` is the real part of a power series with the
(doubled) Fourier coefficients of `f`. -/
theorem s07c_fkps_m2_lp_repr (f : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 (2 * π)) (w : ℂ)
    (hw : ‖w‖ < 1) :
    (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 * f t =
      (∑' n : ℕ, (if n = 0 then (1 : ℂ) else 2) *
        fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) n * w ^ n).re := by
  have h2 : (0 : ℝ) ≤ 2 * π := Real.two_pi_pos.le
  have hen : ∀ t : ℝ, ‖Complex.exp (t * I)‖ = 1 := fun t => Complex.norm_exp_ofReal_mul_I t
  have hne : ∀ t : ℝ, Complex.exp (t * I) - w ≠ 0 := by
    intro t h
    have h' : Complex.exp (t * I) = w := sub_eq_zero.mp h
    have h1 := hen t
    rw [h'] at h1
    linarith
  have hfC : IntervalIntegrable (fun t => (f t : ℂ)) volume 0 (2 * π) := ⟨hf.1.ofReal, hf.2.ofReal⟩
  have hkc : Continuous fun t : ℝ => (Complex.exp (t * I) + w) / (Complex.exp (t * I) - w) :=
    Continuous.div (by fun_prop) (by fun_prop) hne
  have hKi : IntervalIntegrable (fun t => (Complex.exp (t * I) + w) / (Complex.exp (t * I) - w) *
      (f t : ℂ)) volume 0 (2 * π) := hfC.continuousOn_mul hkc.continuousOn
  have hpt : ∀ t : ℝ, (1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 * f t =
      ((Complex.exp (t * I) + w) / (Complex.exp (t * I) - w) * (f t : ℂ)).re := by
    intro t
    have h := s07c_fkps_m2_re_herglotz w t (f t)
    rw [herglotzRieszKernel_def, circleMap_zero, sub_zero, sub_zero, ofReal_one, one_mul,
      smul_eq_mul] at h
    exact h.symm
  have hre : ∫ t in (0 : ℝ)..2 * π, (1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 * f t =
      (∫ t in (0 : ℝ)..2 * π, (Complex.exp (t * I) + w) / (Complex.exp (t * I) - w) *
        (f t : ℂ)).re := by
    simp_rw [hpt]
    have h := reCLM.intervalIntegral_comp_comm hKi
    simpa only [reCLM_apply] using h
  have hq : ∀ t : ℝ, ‖w * Complex.exp (-(t * I))‖ = ‖w‖ := by
    intro t
    rw [norm_mul, Complex.exp_neg, norm_inv, hen, inv_one, mul_one]
  have hFc : ∀ n : ℕ, Continuous fun t : ℝ =>
      (if n = 0 then (1 : ℂ) else 2) * (w * Complex.exp (-(t * I))) ^ n := fun n => by fun_prop
  have hFi : ∀ n : ℕ, Integrable (fun t : ℝ => (if n = 0 then (1 : ℂ) else 2) *
      (w * Complex.exp (-(t * I))) ^ n * (f t : ℂ)) (volume.restrict (Ioc 0 (2 * π))) := fun n =>
    (hfC.continuousOn_mul (hFc n).continuousOn).1
  have hfn : Integrable (fun t => ‖(f t : ℂ)‖) (volume.restrict (Ioc 0 (2 * π))) := hfC.1.norm
  have hbd : ∀ (n : ℕ) (t : ℝ), ‖(if n = 0 then (1 : ℂ) else 2) * (w * Complex.exp (-(t * I))) ^ n *
      (f t : ℂ)‖ ≤ 2 * ‖w‖ ^ n * ‖(f t : ℂ)‖ := by
    intro n t
    rw [norm_mul, norm_mul, norm_pow, hq]
    have he : ‖(if n = 0 then (1 : ℂ) else 2)‖ ≤ 2 := by
      by_cases hn : n = 0
      · simp only [hn, if_true, norm_one]
        norm_num
      · simp only [hn, if_false]
        norm_num
    have hp : 0 ≤ ‖w‖ ^ n * ‖(f t : ℂ)‖ := by positivity
    nlinarith
  have hsum : Summable fun n : ℕ => ∫ t : ℝ, ‖(if n = 0 then (1 : ℂ) else 2) *
      (w * Complex.exp (-(t * I))) ^ n * (f t : ℂ)‖ ∂(volume.restrict (Ioc 0 (2 * π))) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) (fun n => ?_)
      (((summable_geometric_of_lt_one (norm_nonneg w) hw).mul_left 2).mul_right
        (∫ t : ℝ, ‖(f t : ℂ)‖ ∂(volume.restrict (Ioc 0 (2 * π)))))
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _) (hfn.const_mul _)
      (ae_of_all _ fun t => hbd n t)
  have hS := hasSum_integral_of_summable_integral_norm hFi hsum
  have htsum : ∀ t : ℝ, ∑' n : ℕ, (if n = 0 then (1 : ℂ) else 2) * (w * Complex.exp (-(t * I))) ^ n *
      (f t : ℂ) = (Complex.exp (t * I) + w) / (Complex.exp (t * I) - w) * (f t : ℂ) := fun t =>
    ((s07c_fkps_m2_lp_kernel_hasSum w hw t).mul_right (f t : ℂ)).tsum_eq
  have hS' : HasSum (fun n : ℕ => ∫ t : ℝ, (if n = 0 then (1 : ℂ) else 2) *
      (w * Complex.exp (-(t * I))) ^ n * (f t : ℂ) ∂(volume.restrict (Ioc 0 (2 * π))))
      (∫ t : ℝ, (Complex.exp (t * I) + w) / (Complex.exp (t * I) - w) * (f t : ℂ)
        ∂(volume.restrict (Ioc 0 (2 * π)))) := by
    convert hS using 1
    exact integral_congr_ae (ae_of_all _ fun t => (htsum t).symm)
  have hterm : ∀ n : ℕ, ((2 * π)⁻¹ : ℂ) * ∫ t : ℝ, (if n = 0 then (1 : ℂ) else 2) *
      (w * Complex.exp (-(t * I))) ^ n * (f t : ℂ) ∂(volume.restrict (Ioc 0 (2 * π))) =
      (if n = 0 then (1 : ℂ) else 2) * fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) n *
        w ^ n := by
    intro n
    rw [s07c_fkps_m2_lp_coeff_eq, intervalIntegral.integral_of_le h2]
    have h : ∀ t : ℝ, (if n = 0 then (1 : ℂ) else 2) * (w * Complex.exp (-(t * I))) ^ n *
        (f t : ℂ) = ((if n = 0 then (1 : ℂ) else 2) * w ^ n) *
          (Complex.exp (-(((n : ℤ) : ℂ) * t * I)) * (f t : ℂ)) := by
      intro t
      rw [mul_pow, ← Complex.exp_nat_mul,
        show (n : ℂ) * -(t * I) = -(((n : ℤ) : ℂ) * t * I) by push_cast; ring]
      ring
    simp_rw [h, integral_const_mul]
    ring
  have hfin : ((2 * π)⁻¹ : ℂ) * ∫ t in (0 : ℝ)..2 * π,
      (Complex.exp (t * I) + w) / (Complex.exp (t * I) - w) * (f t : ℂ) =
      ∑' n : ℕ, (if n = 0 then (1 : ℂ) else 2) *
        fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) n * w ^ n := by
    rw [intervalIntegral.integral_of_le h2, ← (hS'.mul_left ((2 * π)⁻¹ : ℂ)).tsum_eq]
    exact tsum_congr hterm
  rw [hre, ← hfin, show ((2 * π)⁻¹ : ℂ) = (((2 * π)⁻¹ : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul]

/-- M2.5 helper: `‖f̂(n)‖ ≤ (2π)⁻¹ ∫₀^{2π} |f|`. -/
theorem s07c_fkps_m2_lp_coeff_norm (f : ℝ → ℝ) (n : ℤ) :
    ‖fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) n‖ ≤
      (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, ‖f t‖ := by
  have h2 : (0 : ℝ) ≤ 2 * π := by positivity
  rw [s07c_fkps_m2_lp_coeff_eq, norm_mul]
  have hc : ‖((2 * π)⁻¹ : ℂ)‖ = (2 * π)⁻¹ := by
    rw [norm_inv, show ((2 : ℂ) * π) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg h2]
  rw [hc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (intervalIntegral.norm_integral_le_integral_norm h2).trans (le_of_eq ?_)
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [norm_mul, Complex.norm_real]
  rw [show -((n : ℂ) * x * I) = ((-(n * x) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]

/-- M2.5 helper: the coefficients are uniformly bounded. -/
theorem s07c_fkps_m2_lp_coeff_bound (f : ℝ → ℝ) : ∃ A : ℝ, ∀ n : ℕ,
    ‖(if n = 0 then (1 : ℂ) else 2) * fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) n‖ ≤ A := by
  refine ⟨2 * ((2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, ‖f t‖), fun n => ?_⟩
  rw [norm_mul]
  have h1 : ‖(if n = 0 then (1 : ℂ) else 2)‖ ≤ 2 := by
    by_cases hn : n = 0
    · simp only [hn, if_true, norm_one]
      norm_num
    · simp only [hn, if_false]
      norm_num
  exact mul_le_mul h1 (s07c_fkps_m2_lp_coeff_norm f n) (norm_nonneg _) (by norm_num)

/-- M2.5 helper: a bound for the shifted derivative terms. -/
theorem s07c_fkps_m2_lp_dterm (a : ℕ → ℂ) (A : ℝ) (ha : ∀ n, ‖a n‖ ≤ A) (z : ℂ) (ρ : ℝ)
    (hz : ‖z‖ ≤ ρ) (n : ℕ) :
    ‖a (n + 1) * (((n + 1 : ℕ) : ℂ) * z ^ (n + 1 - 1))‖ ≤ A * ((n : ℝ) ^ 1 * ρ ^ n + ρ ^ n) := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (ha 0)
  rw [Nat.add_sub_cancel, norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
  have h1 : ‖z‖ ^ n ≤ ρ ^ n := pow_le_pow_left₀ (norm_nonneg z) hz n
  have h2 : ((n + 1 : ℕ) : ℝ) * ‖z‖ ^ n ≤ (n : ℝ) ^ 1 * ρ ^ n + ρ ^ n := by
    push_cast
    nlinarith [pow_nonneg (norm_nonneg z) n]
  calc ‖a (n + 1)‖ * (((n + 1 : ℕ) : ℝ) * ‖z‖ ^ n)
      ≤ A * (((n + 1 : ℕ) : ℝ) * ‖z‖ ^ n) :=
        mul_le_mul_of_nonneg_right (ha _) (by positivity)
    _ ≤ A * ((n : ℝ) ^ 1 * ρ ^ n + ρ ^ n) := mul_le_mul_of_nonneg_left h2 hA

/-- M2.5 helper: the summable majorant `A ((n+1) ρⁿ)` for `ρ < 1`. -/
theorem s07c_fkps_m2_lp_major (A ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    Summable fun n : ℕ => A * ((n : ℝ) ^ 1 * ρ ^ n + ρ ^ n) := by
  have hr : ‖ρ‖ < 1 := by rwa [Real.norm_of_nonneg hρ0]
  exact ((summable_pow_mul_geometric_of_norm_lt_one 1 hr).add
    (summable_geometric_of_lt_one hρ0 hρ)).mul_left A

/-- M2.5 helper: the termwise-differentiated series converges in the unit disc. -/
theorem s07c_fkps_m2_lp_dsummable (a : ℕ → ℂ) (A : ℝ) (ha : ∀ n, ‖a n‖ ≤ A) (z : ℂ) (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => a n * ((n : ℂ) * z ^ (n - 1)) := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_norm_bounded (s07c_fkps_m2_lp_major A ‖z‖ (norm_nonneg z) hz) fun n => ?_
  exact s07c_fkps_m2_lp_dterm a A ha z ‖z‖ le_rfl n

/-- M2.5 helper: a power series with bounded coefficients is differentiated termwise in the disc. -/
theorem s07c_fkps_m2_lp_hasDeriv (a : ℕ → ℂ) (A : ℝ) (ha : ∀ n, ‖a n‖ ≤ A) (z : ℂ) (hz : ‖z‖ < 1) :
    HasDerivAt (fun w => ∑' n : ℕ, a n * w ^ n) (∑' n : ℕ, a n * ((n : ℂ) * z ^ (n - 1))) z := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (ha 0)
  set ρ : ℝ := (1 + ‖z‖) / 2 with hρdef
  have hρ1 : ρ < 1 := by rw [hρdef]; linarith
  have hzρ : ‖z‖ < ρ := by rw [hρdef]; linarith
  have hρ0 : 0 ≤ ρ := (norm_nonneg z).trans hzρ.le
  have hzt : z ∈ ball (0 : ℂ) ρ := mem_ball_zero_iff.mpr hzρ
  have hu : Summable fun n : ℕ => A * ((n : ℝ) * ρ ^ (n - 1)) := by
    rw [← summable_nat_add_iff 1]
    refine (s07c_fkps_m2_lp_major A ρ hρ0 hρ1).congr fun n => ?_
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  refine hasDerivAt_tsum_of_isPreconnected (g := fun n w => a n * w ^ n)
    (g' := fun n w => a n * ((n : ℂ) * w ^ (n - 1))) hu isOpen_ball
    (convex_ball (0 : ℂ) ρ).isPreconnected (fun n y _ => (hasDerivAt_pow n y).const_mul (a n))
    (fun n y hy => ?_) hzt ?_ hzt
  · have hy' : ‖y‖ ≤ ρ := (mem_ball_zero_iff.mp hy).le
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
    have h1 : ‖y‖ ^ (n - 1) ≤ ρ ^ (n - 1) := pow_le_pow_left₀ (norm_nonneg y) hy' _
    calc ‖a n‖ * ((n : ℝ) * ‖y‖ ^ (n - 1)) ≤ A * ((n : ℝ) * ‖y‖ ^ (n - 1)) :=
          mul_le_mul_of_nonneg_right (ha n) (by positivity)
      _ ≤ A * ((n : ℝ) * ρ ^ (n - 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)) hA
  · have hr : ‖‖z‖‖ < 1 := by rwa [norm_norm]
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left A)
      fun n => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (ha n) (by positivity)

/-- M2.5 helper: the real gradient of the real part of a holomorphic function is bounded by `|F'|`. -/
theorem s07c_fkps_m2_lp_fderiv_le (F : ℂ → ℂ) (d z : ℂ) (hF : HasDerivAt F d z) (g : ℂ → ℝ)
    (hg : g =ᶠ[𝓝 z] fun w => (F w).re) : ‖fderiv ℝ g z‖ ≤ ‖d‖ := by
  have h1 := (hF.hasFDerivAt.restrictScalars ℝ)
  have h2 := (reCLM.hasFDerivAt (x := F z)).comp z h1
  have h3 : HasFDerivAt g (reCLM.comp ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ)) z :=
    h2.congr_of_eventuallyEq hg
  rw [h3.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg d) fun v => ?_
  simp only [ContinuousLinearMap.comp_apply, reCLM_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, smul_eq_mul, Real.norm_eq_abs]
  calc |(v * d).re| ≤ ‖v * d‖ := Complex.abs_re_le_norm _
    _ = ‖d‖ * ‖v‖ := by rw [norm_mul, mul_comm]

/-- M2.5 helper: `∫₀¹ r (1 - r) r^{2m} dr = 1/((2m+2)(2m+3))`. -/
theorem s07c_fkps_m2_lp_radial (m : ℕ) :
    ∫ r in (0 : ℝ)..1, r * (1 - r) * r ^ (2 * m) =
      1 / ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) := by
  have h : (fun r : ℝ => r * (1 - r) * r ^ (2 * m)) = fun r => r ^ (2 * m + 1) - r ^ (2 * m + 2) := by
    funext r
    ring
  rw [h, intervalIntegral.integral_sub ((continuous_pow _).intervalIntegrable _ _)
    ((continuous_pow _).intervalIntegrable _ _), integral_pow, integral_pow]
  have h2 : (2 * (m : ℝ) + 2) ≠ 0 := by positivity
  have h3 : (2 * (m : ℝ) + 3) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- M2.5 helper: the weighted area integral of a derivative polynomial. -/
theorem s07c_fkps_m2_lp_poly (a : ℕ → ℂ) (N : ℕ) :
    ∫ z in unitDisc, (1 - ‖z‖) * ‖∑ m ∈ Finset.range N, ((m + 1 : ℕ) : ℂ) * a (m + 1) * z ^ m‖ ^ 2 ≤
      2 * π * ∑ m ∈ Finset.range N, ‖a (m + 1)‖ ^ 2 / 4 := by
  have hp := s02_vd_disc_parseval (fun r => 1 - r) (by fun_prop)
    (fun m => ((m + 1 : ℕ) : ℂ) * a (m + 1)) N
  beta_reduce at hp
  rw [hp]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => ?_) (by positivity)
  rw [s07c_fkps_m2_lp_radial, norm_mul, Complex.norm_natCast, mul_pow]
  have hx : 0 ≤ ‖a (m + 1)‖ ^ 2 := sq_nonneg _
  have hq : ((m : ℝ) + 1) ^ 2 / ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc ((m + 1 : ℕ) : ℝ) ^ 2 * ‖a (m + 1)‖ ^ 2 * (1 / ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)))
      = ‖a (m + 1)‖ ^ 2 * (((m : ℝ) + 1) ^ 2 / ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))) := by
        push_cast
        ring
    _ ≤ ‖a (m + 1)‖ ^ 2 * (1 / 4) := mul_le_mul_of_nonneg_left hq hx
    _ = ‖a (m + 1)‖ ^ 2 / 4 := by ring

/-- M2.5 helper: Bessel's inequality for the positive-frequency coefficients. -/
theorem s07c_fkps_m2_lp_bessel (f : ℝ → ℝ)
    (hL2 : MemLp (fun t => (f t : ℂ)) 2 (volume.restrict (Ioc 0 (2 * π)))) (N : ℕ) :
    2 * π * ∑ m ∈ Finset.range N, ‖(if m + 1 = 0 then (1 : ℂ) else 2) *
        fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) ((m + 1 : ℕ) : ℤ)‖ ^ 2 / 4 ≤
      ∫ t in (0 : ℝ)..2 * π, ‖f t‖ ^ 2 := by
  have hs := hasSum_sq_fourierCoeffOn Real.two_pi_pos hL2
  have hterm : ∀ m ∈ Finset.range N, ‖(if m + 1 = 0 then (1 : ℂ) else 2) *
      fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) ((m + 1 : ℕ) : ℤ)‖ ^ 2 / 4 =
      ‖fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) ((m + 1 : ℕ) : ℤ)‖ ^ 2 := by
    intro m _
    rw [if_neg (Nat.succ_ne_zero m), norm_mul, mul_pow, show ‖(2 : ℂ)‖ = 2 by norm_num]
    ring
  rw [Finset.sum_congr rfl hterm]
  have hle : ∑ m ∈ Finset.range N,
      ‖fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) ((m + 1 : ℕ) : ℤ)‖ ^ 2 ≤
      (2 * π - 0)⁻¹ • ∫ x in (0 : ℝ)..2 * π, ‖(f x : ℂ)‖ ^ 2 := by
    rw [← hs.tsum_eq]
    have h := hs.summable.sum_le_tsum
      ((Finset.range N).map ⟨fun m : ℕ => ((m + 1 : ℕ) : ℤ), fun x y h => by simpa using h⟩)
      (fun i _ => sq_nonneg _)
    refine le_trans (le_of_eq ?_) h
    rw [Finset.sum_map]
    rfl
  simp only [smul_eq_mul, sub_zero, Complex.norm_real] at hle
  have hπ : (0 : ℝ) < 2 * π := Real.two_pi_pos
  calc 2 * π * ∑ m ∈ Finset.range N,
        ‖fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) ((m + 1 : ℕ) : ℤ)‖ ^ 2
      ≤ 2 * π * ((2 * π)⁻¹ * ∫ x in (0 : ℝ)..2 * π, ‖f x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hle hπ.le
    _ = ∫ t in (0 : ℝ)..2 * π, ‖f t‖ ^ 2 := by
        field_simp

/-- M2.5 helper: finite `L²` energy on `[0, 2π]` gives `MemLp 2` on `Ioc 0 (2π)`. -/
theorem s07c_fkps_m2_lp_memLp (f : ℝ → ℝ) (hf : Measurable f)
    (hfin : ∫⁻ θ in Icc 0 (2 * π), ‖f θ‖ₑ ^ 2 ≠ ⊤) :
    MemLp (fun t => (f t : ℂ)) 2 (volume.restrict (Ioc 0 (2 * π))) := by
  have hm : AEStronglyMeasurable (fun t => (f t : ℂ)) (volume.restrict (Ioc 0 (2 * π))) :=
    (Complex.measurable_ofReal.comp hf).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine ⟨hm.norm.pow 2, ?_⟩
  show ∫⁻ t in Ioc 0 (2 * π), ‖‖(f t : ℂ)‖ ^ 2‖ₑ < ⊤
  have h : ∀ t, ‖‖(f t : ℂ)‖ ^ 2‖ₑ = ‖f t‖ₑ ^ 2 := by
    intro t
    rw [Complex.norm_real, enorm_pow, enorm_norm]
  simp_rw [h]
  exact lt_of_le_of_lt (lintegral_mono_set Ioc_subset_Icc_self) (lt_top_iff_ne_top.mpr hfin)

/-- M2.5 helper: `MemLp 2` gives interval integrability. -/
theorem s07c_fkps_m2_lp_ii (f : ℝ → ℝ)
    (hL2 : MemLp (fun t => (f t : ℂ)) 2 (volume.restrict (Ioc 0 (2 * π)))) :
    IntervalIntegrable f volume 0 (2 * π) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
  have h := (hL2.integrable one_le_two).re
  exact h.congr (ae_of_all _ fun t => by simp)

/-- M2.5 helper: the Bochner energy is bounded by the lower-integral energy. -/
theorem s07c_fkps_m2_lp_rhs (f : ℝ → ℝ) :
    ENNReal.ofReal (∫ t in (0 : ℝ)..2 * π, ‖f t‖ ^ 2) ≤ ∫⁻ θ in Icc 0 (2 * π), ‖f θ‖ₑ ^ 2 := by
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
  by_cases hi : Integrable (fun t => ‖f t‖ ^ 2) (volume.restrict (Ioc 0 (2 * π)))
  · rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun t => by positivity)]
    refine (lintegral_mono fun t => le_of_eq ?_).trans (lintegral_mono_set Ioc_subset_Icc_self)
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  · rw [integral_undef hi, ENNReal.ofReal_zero]
    exact bot_le

/-- M2.5 helper: Fatou step for pointwise limits of continuous functions on the disc. -/
theorem s07c_fkps_m2_lp_fatou (G : ℂ → ℝ≥0∞) (P : ℕ → ℂ → ℂ) (hP : ∀ N, Continuous (P N))
    (D : ℂ → ℂ) (hD : ∀ z ∈ unitDisc, Tendsto (fun N => P N z) atTop (𝓝 (D z)))
    (hG : ∀ z ∈ unitDisc, G z ≤ ENNReal.ofReal ((1 - ‖z‖) * ‖D z‖ ^ 2)) (B : ℝ)
    (hB : ∀ N, ∫ z in unitDisc, (1 - ‖z‖) * ‖P N z‖ ^ 2 ≤ B) :
    ∫⁻ z in unitDisc, G z ≤ ENNReal.ofReal B := by
  have hD' : MeasurableSet unitDisc := (show MeasurableSet (ball (0 : ℂ) 1) from measurableSet_ball)
  have hc : ∀ N, Continuous fun z => (1 - ‖z‖) * ‖P N z‖ ^ 2 := fun N =>
    (continuous_const.sub continuous_norm).mul ((hP N).norm.pow 2)
  have hmeas : ∀ N, Measurable fun z => ENNReal.ofReal ((1 - ‖z‖) * ‖P N z‖ ^ 2) := fun N =>
    ENNReal.measurable_ofReal.comp (hc N).measurable
  have hlim : ∀ z ∈ unitDisc, ENNReal.ofReal ((1 - ‖z‖) * ‖D z‖ ^ 2) =
      liminf (fun N => ENNReal.ofReal ((1 - ‖z‖) * ‖P N z‖ ^ 2)) atTop := fun z hz =>
    (((ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_const_nhds.mul (((hD z hz).norm).pow 2)))).liminf_eq.symm
  calc ∫⁻ z in unitDisc, G z
      ≤ ∫⁻ z in unitDisc, liminf (fun N => ENNReal.ofReal ((1 - ‖z‖) * ‖P N z‖ ^ 2)) atTop :=
        setLIntegral_mono' hD' fun z hz => (hG z hz).trans (hlim z hz).le
    _ ≤ liminf (fun N => ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖) * ‖P N z‖ ^ 2)) atTop :=
        lintegral_liminf_le fun N => hmeas N
    _ ≤ ENNReal.ofReal B := by
        refine liminf_le_of_frequently_le' (Frequently.of_forall fun N => ?_)
        have hint : IntegrableOn (fun z => (1 - ‖z‖) * ‖P N z‖ ^ 2) unitDisc :=
          ((hc N).continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set
            ball_subset_closedBall
        have hnn : 0 ≤ᵐ[volume.restrict unitDisc] fun z => (1 - ‖z‖) * ‖P N z‖ ^ 2 := by
          refine (ae_restrict_iff' hD').mpr (ae_of_all _ fun z hz => ?_)
          have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
          have : (0 : ℝ) ≤ 1 - ‖z‖ := by linarith
          positivity
        rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
        exact ENNReal.ofReal_le_ofReal (hB N)

/-- M2.5 (Littlewood–Paley area bound): `∫_𝔻 |∇ P f|² (1 - |z|) dA ≤ C ∫₀^{2π} |f|²`. -/
theorem s07c_fkps_m2_area : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : ℝ → ℝ, Measurable f →
    (∀ t, f (t + 2 * π) = f t) →
    ∫⁻ z in unitDisc, ‖fderiv ℝ (fun w : ℂ => (2 * π)⁻¹ *
      ∫ t in (0 : ℝ)..2 * π, (1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 * f t) z‖ₑ ^ 2 *
        ENNReal.ofReal (1 - ‖z‖) ≤
      C * ∫⁻ θ in Icc 0 (2 * π), ‖f θ‖ₑ ^ 2 := by
  refine ⟨1, ENNReal.one_ne_top, fun f hf _hper => ?_⟩
  -- `_hper` is not needed: the integrals only see `[0, 2π]`.
  by_cases hfin : ∫⁻ θ in Icc 0 (2 * π), ‖f θ‖ₑ ^ 2 = ⊤
  · rw [hfin, one_mul]
    exact le_top
  rw [one_mul]
  have hL2 := s07c_fkps_m2_lp_memLp f hf hfin
  have hii := s07c_fkps_m2_lp_ii f hL2
  obtain ⟨A, hA⟩ := s07c_fkps_m2_lp_coeff_bound f
  have hdisc : ∀ z ∈ unitDisc, ‖z‖ < 1 := fun z hz => by
    simpa only [mem_ball_zero_iff] using (show z ∈ ball (0 : ℂ) 1 from hz)
  refine (s07c_fkps_m2_lp_fatou _
    (fun N z => ∑ m ∈ Finset.range N, ((m + 1 : ℕ) : ℂ) *
      ((if m + 1 = 0 then (1 : ℂ) else 2) *
        fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) ((m + 1 : ℕ) : ℤ)) * z ^ m)
    (fun N => by fun_prop)
    (fun z => ∑' n : ℕ, ((if n = 0 then (1 : ℂ) else 2) *
        fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) n) * ((n : ℂ) * z ^ (n - 1)))
    ?_ ?_ (∫ t in (0 : ℝ)..2 * π, ‖f t‖ ^ 2) ?_).trans (s07c_fkps_m2_lp_rhs f)
  · intro z hz
    have hs := (s07c_fkps_m2_lp_dsummable _ A hA z (hdisc z hz)).hasSum.tendsto_sum_nat
    refine ((hs.comp (tendsto_add_atTop_nat 1)).congr fun N => ?_)
    simp only [Function.comp_apply]
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun m _ => ?_
    push_cast
    ring
  · intro z hz
    have hz1 := hdisc z hz
    have hev : (fun w : ℂ => (2 * π)⁻¹ *
        ∫ t in (0 : ℝ)..2 * π, (1 - ‖w‖ ^ 2) / ‖Complex.exp (t * I) - w‖ ^ 2 * f t) =ᶠ[𝓝 z]
        fun w => (∑' n : ℕ, ((if n = 0 then (1 : ℂ) else 2) *
          fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) n) * w ^ n).re := by
      filter_upwards [isOpen_ball.mem_nhds (show z ∈ ball (0 : ℂ) 1 from hz)] with w hw
      exact s07c_fkps_m2_lp_repr f hii w (by simpa only [mem_ball_zero_iff] using hw)
    have hle := s07c_fkps_m2_lp_fderiv_le _ _ z (s07c_fkps_m2_lp_hasDeriv _ A hA z hz1) _ hev
    have h1 : (0 : ℝ) ≤ 1 - ‖z‖ := by linarith
    rw [ENNReal.ofReal_mul h1, mul_comm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    gcongr
  · intro N
    have hp := s07c_fkps_m2_lp_poly (fun n : ℕ => (if n = 0 then (1 : ℂ) else 2) *
      fourierCoeffOn Real.two_pi_pos (fun t => (f t : ℂ)) n) N
    beta_reduce at hp
    exact hp.trans (s07c_fkps_m2_lp_bessel f hL2 N)

/-! ## Milestone M3 (pullback package, Green representation, Green energy identity)
# SMALL chain, milestone M3 (pullback package, Green representation, Green energy identity): frozen-stub
interface DRAFT (w3)

Prefix `s07c_fkps_m3`.
There are no new definitions. Conventions (agreed with w2, always written inline):
* a real function `u` has the `ℂ`-valued gradient `g = u_x + i u_y`, and `⟨a, b⟩ = Re (conj a * b)`; for a test
  function `φ : ℂ → ℝ` the gradient is `∇φ z = fderiv ℝ φ z 1 + i fderiv ℝ φ z I`;
* test functions are `C¹` with compact support inside `𝔻` (this contains `C^∞_c(𝔻)`);
* `P[f](X) = (2π)⁻¹ ∫₀^{2π} (1 - |X|²)/|e^{it} - X|² f(t) dt`, exactly the M2 form;
* `∇_Y G₀(X, Y) = (1 - |X|²) / (2π · conj (X - Y) · (1 - X Ȳ))` is the gradient in `Y` of the Green function
  `G₀(X, Y) = (2π)⁻¹ log (|1 - X Ȳ| / |X - Y|)` of `𝔻` (so `-Δ_Y G₀(X, ·) = δ_X`, `G₀(X, ·) = 0` on `𝕋`);
  the truncated weight at `0` is `G♭(Y) = (2π)⁻¹ log (1 / max(|Y|, 1/2)) = (2π)⁻¹ min(log (1/|Y|), log 2)`, with
  `∇G♭(Y) = -Y / (2π |Y|²)` for `|Y| > 1/2` and `∇G♭ = 0` on `B(0, 1/2)`.

Stubs:
* `s07c_fkps_m3_kernel` (helper for w2's M4): `|∇_Y G₀(X, Y)| ≤ (1 - |X|²) / (2π |X - Y| max(|X - Y|, 1 - |X|))`.
* `s07c_fkps_m3a_pullback` (M3a, concrete): for `F` qc, `F(𝔻) = 𝔻`, `F 0 = 0`, `|μ_F| ≤ 1/2` a.e. on `𝔻`, and `v`
  `C²` on `ℂ` and harmonic on `𝔻`, the pullback `u₁ = v ∘ F` has a weak gradient `g ∈ L²(𝔻)` (P2), and solves
  `Δu₁ = -div V` weakly (P4) with `|V| ≤ 4 |μ_F| |g|` a.e. on `𝔻` (P3). `V = (A₁ - I) g`, `A₁` the pulled-back
  conductivity `J_F DF⁻¹ DF⁻ᵀ`.
* `s07c_fkps_m3b_green` (M3b, abstract): `u` continuous on `𝔻̄` with boundary values `f`, weak gradient `g`,
  `Δu = -div V` weakly, `V ∈ L²(𝔻)` ⟹ for a.e. `X ∈ 𝔻` (P5)
  `u X = P[f](X) - ∫_𝔻 ⟨∇_Y G₀(X, Y), V Y⟩ dY`, with an integrable integrand.
* `s07c_fkps_m3c_energy` (M3c = P7, abstract): under the M3b hypotheses, the Green energy identity with the
  truncated weight `G♭` (revised at w2's request, approved by the leader):
  `∫_𝔻 |g|² G♭ = ½ (⨍_𝕋 f² - ⨍_{|Y|=1/2} u²) - ∫_𝔻 ⟨V, g⟩ G♭ - ∫_{𝔻 \ B(0,1/2)} u ⟨V, ∇G♭⟩`,
  with the three integrands integrable. (Formally: test P4 with `φ = u G♭` and use
  `∫ ∇(u²/2)·∇G♭ = ½ (⨍_{|Y|=1/2} u² - ⨍_𝕋 f²)`, since `-ΔG♭` is the normalized arc length on `|Y| = 1/2`.)
* `s07c_fkps_m3` (assembly, the statement w2 consumes): M3a + M3b + M3c for `u₁ = v ∘ F`,
  `f θ = v (F (e^{iθ}))`.
-/

/-- The identity `|1 - X Ȳ|² - |X - Y|² = (1 - |X|²)(1 - |Y|²)`. -/
theorem s07c_fkps_m3_kernel_sq (X Y : ℂ) :
    ‖1 - X * conj Y‖ ^ 2 - ‖X - Y‖ ^ 2 = (1 - ‖X‖ ^ 2) * (1 - ‖Y‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

/-- M3 kernel bound (for w2's M4): for `X, Y ∈ 𝔻`, `Y ≠ X`, the gradient of the Green function of `𝔻` satisfies
`|∇_Y G₀(X, Y)| ≤ (1 - |X|²) / (2π |X - Y| max(|X - Y|, 1 - |X|))`
(from `|1 - X Ȳ| ≥ |X - Y|` and `|1 - X Ȳ| ≥ 1 - |X|`). -/
theorem s07c_fkps_m3_kernel : ∀ X ∈ unitDisc, ∀ Y ∈ unitDisc, Y ≠ X →
    ‖((1 - ‖X‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (X - Y) * (1 - X * conj Y))‖ ≤
      (1 - ‖X‖ ^ 2) / (2 * π * ‖X - Y‖ * max ‖X - Y‖ (1 - ‖X‖)) := by
  intro X hX Y hY hne
  have hXn : ‖X‖ < 1 := mem_ball_zero_iff.1 hX
  have hYn : ‖Y‖ < 1 := mem_ball_zero_iff.1 hY
  have ha : 0 ≤ 1 - ‖X‖ ^ 2 := by nlinarith [norm_nonneg X]
  have hd : 0 < ‖X - Y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne.symm)
  set w : ℂ := 1 - X * conj Y with hw
  have h1 : 1 - ‖X‖ ≤ ‖w‖ := by
    have hXY : ‖X * conj Y‖ ≤ ‖X‖ := by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_of_le_one_right (norm_nonneg X) hYn.le
    have := norm_sub_norm_le (1 : ℂ) (X * conj Y)
    rw [norm_one] at this
    rw [hw]; linarith
  have h2 : ‖X - Y‖ ≤ ‖w‖ := by
    have hk := s07c_fkps_m3_kernel_sq X Y
    have hpos : 0 ≤ (1 - ‖X‖ ^ 2) * (1 - ‖Y‖ ^ 2) :=
      mul_nonneg ha (by nlinarith [norm_nonneg Y])
    rw [← hw] at hk
    nlinarith [norm_nonneg w, norm_nonneg (X - Y)]
  have hm : 0 < max ‖X - Y‖ (1 - ‖X‖) := lt_max_of_lt_left hd
  have hmw : max ‖X - Y‖ (1 - ‖X‖) ≤ ‖w‖ := max_le h2 h1
  have hnorm : ‖((1 - ‖X‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (X - Y) * w)‖ =
      (1 - ‖X‖ ^ 2) / (2 * π * ‖X - Y‖ * ‖w‖) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ha, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hnorm]
  exact div_le_div_of_nonneg_left ha (by positivity) (by gcongr)

/-- Uniform convergence on a compact set survives post-composition with a continuous map. -/
theorem s07c_fkps_m3a_ucomp {E : Type*} [PseudoMetricSpace E] {Fn : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {C : Set ℂ}
    (hC : IsCompact C) (hF : Continuous F) (hu : TendstoUniformlyOn Fn F atTop C) (Φ : ℂ → E)
    (hΦ : Continuous Φ) : TendstoUniformlyOn (fun n z => Φ (Fn n z)) (fun z => Φ (F z)) atTop C := by
  have hN : IsCompact (cthickening 1 (F '' C)) := (hC.image hF).cthickening
  have huc := Metric.uniformContinuousOn_iff.1 (hN.uniformContinuousOn_of_continuous hΦ.continuousOn)
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδΦ⟩ := huc ε hε
  filter_upwards [hu (min δ 1) (lt_min hδ one_pos)] with n hn z hz
  have h1 := hn z hz
  have hFz : F z ∈ cthickening 1 (F '' C) := self_subset_cthickening _ ⟨z, hz, rfl⟩
  have hFnz : Fn n z ∈ cthickening 1 (F '' C) :=
    mem_cthickening_of_dist_le (Fn n z) (F z) 1 (F '' C) ⟨z, hz, rfl⟩
      (by rw [dist_comm]; exact (h1.trans_le (min_le_right _ _)).le)
  exact hδΦ _ hFz _ hFnz (h1.trans_le (min_le_left _ _))

/-- Uniform approximants of `F` on a compact `C` eventually map `C` into the compact `cthickening 1 (F '' C)`. -/
theorem s07c_fkps_m3a_mapsto {Fn : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {C : Set ℂ}
    (hu : TendstoUniformlyOn Fn F atTop C) :
    ∀ᶠ n in atTop, ∀ z ∈ C, Fn n z ∈ cthickening 1 (F '' C) := by
  rw [Metric.tendstoUniformlyOn_iff] at hu
  filter_upwards [hu 1 one_pos] with n hn z hz
  exact mem_cthickening_of_dist_le (Fn n z) (F z) 1 (F '' C) ⟨z, hz, rfl⟩
    (by rw [dist_comm]; exact (hn z hz).le)

/-- A sequence in `ℝ≥0∞` that is eventually below `η c` for every `η > 0` (with `c < ∞`) tends to `0`. -/
theorem s07c_fkps_m3a_ennreal_lim {b : ℕ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (h : ∀ η : ℝ≥0, 0 < η → ∀ᶠ n in atTop, b n ≤ η * c) : Tendsto b atTop (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  by_cases hc0 : c = 0
  · filter_upwards [h 1 one_pos] with n hn
    rw [hc0, mul_zero] at hn
    exact hn.trans zero_le
  · obtain ⟨η, hη, hlt⟩ := ENNReal.exists_nnreal_pos_mul_lt hc hε.ne'
    filter_upwards [h η hη] with n hn
    exact hn.trans hlt.le

/-- `z ↦ A z (G z)` is a.e. strongly measurable for continuous `A` and a.e. strongly measurable `G`. -/
theorem s07c_fkps_m3a_aesm_apply {μ : Measure ℂ} {A : ℂ → ℂ →L[ℝ] ℂ} {G : ℂ → ℂ} (hA : Continuous A)
    (hG : AEStronglyMeasurable G μ) : AEStronglyMeasurable (fun z => A z (G z)) μ :=
  (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := ℂ) (F := ℂ)).continuous.comp_aestronglyMeasurable
    (hA.aestronglyMeasurable.prodMk hG)

/-- The `L²` part of the chain rule `Φ ∘ F`: if `Fₙ → F` uniformly on the compact `C` and `Gₙ → G` in `L²(C)`,
then `DΦ(Fₙ) Gₙ → DΦ(F) G` in `L²(C)`, and `DΦ(F) G ∈ L²(C)`. -/
theorem s07c_fkps_m3a_chainL2 {Fn Gn : ℕ → ℂ → ℂ} {F G : ℂ → ℂ} {C : Set ℂ} (hC : IsCompact C)
    (hFc : Continuous F) (hu : TendstoUniformlyOn Fn F atTop C) (hFnc : ∀ n, Continuous (Fn n))
    (hGnm : ∀ n, AEStronglyMeasurable (Gn n) (volume.restrict C)) (hG : MemLp G 2 (volume.restrict C))
    (hGn : Tendsto (fun n => eLpNorm (fun z => Gn n z - G z) 2 (volume.restrict C)) atTop (𝓝 0))
    (Φ : ℂ → ℂ) (hΦ : ContDiff ℝ 1 Φ) :
    MemLp (fun z => fderiv ℝ Φ (F z) (G z)) 2 (volume.restrict C) ∧
      Tendsto (fun n => eLpNorm (fun z => fderiv ℝ Φ (Fn n z) (Gn n z) - fderiv ℝ Φ (F z) (G z)) 2
        (volume.restrict C)) atTop (𝓝 0) := by
  have hdΦ : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv one_ne_zero
  have hN : IsCompact (cthickening 1 (F '' C)) := (hC.image hFc).cthickening
  obtain ⟨M₀, hM₀⟩ := hN.exists_bound_of_continuousOn hdΦ.continuousOn
  set M : ℝ := max M₀ 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMb : ∀ w ∈ cthickening 1 (F '' C), ‖fderiv ℝ Φ w‖ ≤ M := fun w hw =>
    (hM₀ w hw).trans (le_max_left _ _)
  have hA : Continuous (fun z => fderiv ℝ Φ (F z)) := hdΦ.comp hFc
  have hAn : ∀ n, Continuous (fun z => fderiv ℝ Φ (Fn n z)) := fun n => hdΦ.comp (hFnc n)
  have hCm : MeasurableSet C := hC.measurableSet
  have hAG : AEStronglyMeasurable (fun z => fderiv ℝ Φ (F z) (G z)) (volume.restrict C) :=
    s07c_fkps_m3a_aesm_apply hA hG.aestronglyMeasurable
  refine ⟨hG.of_le_mul (c := M) hAG ?_, ?_⟩
  · filter_upwards [ae_restrict_mem hCm] with z hz
    exact ((fderiv ℝ Φ (F z)).le_opNorm (G z)).trans (mul_le_mul_of_nonneg_right
      (hMb _ (self_subset_cthickening _ ⟨z, hz, rfl⟩)) (norm_nonneg _))
  have hGt : eLpNorm G 2 (volume.restrict C) ≠ ⊤ := hG.eLpNorm_ne_top
  refine s07c_fkps_m3a_ennreal_lim (c := 1 + eLpNorm G 2 (volume.restrict C))
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hGt⟩) fun η hη => ?_
  have hlim : Tendsto (fun n => ENNReal.ofReal M * eLpNorm (fun z => Gn n z - G z) 2 (volume.restrict C))
      atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal M) hGn (Or.inr ENNReal.ofReal_ne_top)
    rwa [mul_zero] at this
  have hηpos : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.2 hη
  have hucA := Metric.tendstoUniformlyOn_iff.1 (s07c_fkps_m3a_ucomp hC hFc hu (fderiv ℝ Φ) hdΦ) η hη
  filter_upwards [hlim.eventually (Iic_mem_nhds hηpos), hucA, s07c_fkps_m3a_mapsto hu] with n h1 h2 h3
  have hsplit : (fun z => fderiv ℝ Φ (Fn n z) (Gn n z) - fderiv ℝ Φ (F z) (G z)) =
      (fun z => fderiv ℝ Φ (Fn n z) (Gn n z - G z)) +
        fun z => (fderiv ℝ Φ (Fn n z) - fderiv ℝ Φ (F z)) (G z) := by
    funext z
    simp only [Pi.add_apply, map_sub, ContinuousLinearMap.sub_apply]
    abel
  have hm1 : AEStronglyMeasurable (fun z => fderiv ℝ Φ (Fn n z) (Gn n z - G z)) (volume.restrict C) :=
    s07c_fkps_m3a_aesm_apply (hAn n) ((hGnm n).sub hG.aestronglyMeasurable)
  have hm2 : AEStronglyMeasurable (fun z => (fderiv ℝ Φ (Fn n z) - fderiv ℝ Φ (F z)) (G z))
      (volume.restrict C) :=
    s07c_fkps_m3a_aesm_apply ((hAn n).sub hA) hG.aestronglyMeasurable
  have hb1 : eLpNorm (fun z => fderiv ℝ Φ (Fn n z) (Gn n z - G z)) 2 (volume.restrict C) ≤
      ENNReal.ofReal M * eLpNorm (fun z => Gn n z - G z) 2 (volume.restrict C) := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm1 ?_ 2
    filter_upwards [ae_restrict_mem hCm] with z hz
    exact ((fderiv ℝ Φ (Fn n z)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hMb _ (h3 z hz)) (norm_nonneg _))
  have hb2 : eLpNorm (fun z => (fderiv ℝ Φ (Fn n z) - fderiv ℝ Φ (F z)) (G z)) 2 (volume.restrict C) ≤
      ENNReal.ofReal η * eLpNorm G 2 (volume.restrict C) := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm2 ?_ 2
    filter_upwards [ae_restrict_mem hCm] with z hz
    refine ((fderiv ℝ Φ (Fn n z) - fderiv ℝ Φ (F z)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have := h2 z hz
    rw [dist_eq_norm, norm_sub_rev] at this
    exact this.le
  rw [hsplit]
  refine (eLpNorm_add_le (by norm_num)).trans ?_
  rw [ENNReal.ofReal_coe_nnreal] at hb2
  rw [mul_add, mul_one]
  exact add_le_add (hb1.trans h1) hb2

/-- **Chain rule** (smooth `∘` Sobolev): if `F` has `L²` generalized partials `Fx, Fy` on `ℂ` and `Φ` is `C¹`,
then `Φ ∘ F` has the `L²` generalized partials `DΦ(F) Fx, DΦ(F) Fy` on `ℂ`. -/
theorem s07c_fkps_m3a_chain {F Fx Fy : ℂ → ℂ} (hF : HasGenPartials F Fx Fy univ 2) (Φ : ℂ → ℂ)
    (hΦ : ContDiff ℝ 1 Φ) :
    HasGenPartials (fun z => Φ (F z)) (fun z => fderiv ℝ Φ (F z) (Fx z))
      (fun z => fderiv ℝ Φ (F z) (Fy z)) univ 2 := by
  obtain ⟨hloc, Fn, hFnC, hFnU, hFnL⟩ := hF
  have hFc : Continuous F := by
    have := hFnU.continuousOn (Filter.Frequently.of_forall fun n => (hFnC n).continuousOn)
    rwa [continuousOn_univ] at this
  have hFnD : ∀ n, Differentiable ℝ (Fn n) := fun n =>
    differentiableOn_univ.mp ((hFnC n).differentiableOn one_ne_zero)
  have hFnc : ∀ n, Continuous (Fn n) := fun n => (hFnD n).continuous
  have hFnCD : ∀ n, ContDiff ℝ 1 (Fn n) := fun n => contDiffOn_univ.mp (hFnC n)
  have hgn : ∀ n (e : ℂ), Continuous (fun z => fderiv ℝ (Fn n) z e) := fun n e =>
    ((hFnCD n).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcomp : ∀ n (e : ℂ) z, fderiv ℝ (fun z => Φ (Fn n z)) z e = fderiv ℝ Φ (Fn n z) (fderiv ℝ (Fn n) z e) := by
    intro n e z
    rw [fderiv_fun_comp z ((hΦ.differentiable one_ne_zero) _) (hFnD n z)]
    rfl
  have hU : ∀ C ⊆ univ, IsCompact C → TendstoUniformlyOn Fn F atTop C := fun C _ hC =>
    (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).1 hFnU C (subset_univ C) hC
  have hL : ∀ C ⊆ univ, IsCompact C →
      (MemLp (fun z => fderiv ℝ Φ (F z) (Fx z)) 2 (volume.restrict C) ∧
        Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (fun z => Φ (Fn n z)) z 1 -
          fderiv ℝ Φ (F z) (Fx z)) 2 (volume.restrict C)) atTop (𝓝 0)) ∧
      (MemLp (fun z => fderiv ℝ Φ (F z) (Fy z)) 2 (volume.restrict C) ∧
        Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (fun z => Φ (Fn n z)) z I -
          fderiv ℝ Φ (F z) (Fy z)) 2 (volume.restrict C)) atTop (𝓝 0)) := by
    intro C hCs hC
    simp only [hcomp]
    exact ⟨s07c_fkps_m3a_chainL2 hC hFc (hU C hCs hC) hFnc (fun n => (hgn n 1).aestronglyMeasurable)
        (hloc C hCs hC).1 (hFnL C hCs hC).1 Φ hΦ,
      s07c_fkps_m3a_chainL2 hC hFc (hU C hCs hC) hFnc (fun n => (hgn n I).aestronglyMeasurable)
        (hloc C hCs hC).2 (hFnL C hCs hC).2 Φ hΦ⟩
  refine ⟨fun C hCs hC => ⟨(hL C hCs hC).1.1, (hL C hCs hC).2.1⟩, fun n z => Φ (Fn n z),
    fun n => (hΦ.comp (hFnCD n)).contDiffOn, ?_, fun C hCs hC => ⟨(hL C hCs hC).1.2, (hL C hCs hC).2.2⟩⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  exact fun C hCs hC => s07c_fkps_m3a_ucomp hC hFc (hU C hCs hC) Φ hΦ.continuous

/-- `fderiv` of a `C¹` real function vanishes off its topological support. -/
theorem s07c_fkps_m3a_fderiv_zero (φ : ℂ → ℝ) (z : ℂ) (hz : z ∉ tsupport φ) : fderiv ℝ φ z = 0 :=
  Function.notMem_support.1 fun h => hz (support_fderiv_subset ℝ h)

/-- Mollification of a `C¹` test function: for every `δ, ε > 0` there is a `C²` function `ψ` with compact support
in `cthickening δ (tsupport φ)` whose partials are uniformly `ε`-close to those of `φ`. -/
theorem s07c_fkps_m3a_moll (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ ψ : ℂ → ℝ, ContDiff ℝ 2 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ cthickening δ (tsupport φ) ∧
      ∀ z, |fderiv ℝ ψ z 1 - fderiv ℝ φ z 1| ≤ ε ∧ |fderiv ℝ ψ z I - fderiv ℝ φ z I| ≤ ε := by
  have hdφ : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hG : ∀ e : ℂ, Continuous (fun x => fderiv ℝ φ x e) := fun e => hdφ.clm_apply continuous_const
  have hGc : ∀ e : ℂ, HasCompactSupport (fun x => fderiv ℝ φ x e) := by
    intro e
    refine (hc.fderiv (𝕜 := ℝ)).mono fun x hx h => hx ?_
    simp only [h, ContinuousLinearMap.zero_apply]
  have huc : ∀ e : ℂ, UniformContinuous (fun x => fderiv ℝ φ x e) := fun e =>
    (hGc e).uniformContinuous_of_continuous (hG e)
  obtain ⟨r1, hr1, h1⟩ := Metric.uniformContinuous_iff.1 (huc 1) ε hε
  obtain ⟨r2, hr2, h2⟩ := Metric.uniformContinuous_iff.1 (huc I) ε hε
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = min (min r1 r2) δ := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hrdef]; exact lt_min (lt_min hr1 hr2) hδ
  have hrr1 : r ≤ r1 := by rw [hrdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hrr2 : r ≤ r2 := by rw [hrdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hrδ : r ≤ δ := by rw [hrdef]; exact min_le_right _ _
  let b : ContDiffBump (0 : ℂ) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hbr : b.rOut = r := rfl
  have hloc : LocallyIntegrable (b.normed volume) volume := b.integrable_normed.locallyIntegrable
  have key : ∀ (z e : ℂ), fderiv ℝ (convolution (b.normed volume) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume) z e =
      (convolution (b.normed volume) (fun x => fderiv ℝ φ x e) (ContinuousLinearMap.lsmul ℝ ℝ) volume) z := by
    intro z e
    have hd := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hloc hφ z
    have hex := (hc.fderiv (𝕜 := ℝ)).convolutionExists_right ((ContinuousLinearMap.lsmul ℝ ℝ).precompR ℂ) hloc hdφ z
    rw [hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hex, convolution_def]
    simp
  refine ⟨convolution (b.normed volume) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume, ?_, ?_, ?_, fun z => ⟨?_, ?_⟩⟩
  · exact b.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (n := 2) b.contDiff_normed
      hφ.continuous.locallyIntegrable
  · exact b.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hc
  · refine closure_minimal (fun x hx => ?_) isClosed_cthickening
    obtain ⟨a, ha, y, hy, rfl⟩ := Set.mem_add.1 (support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ) hx)
    rw [b.support_normed_eq, mem_ball_zero_iff, hbr] at ha
    refine mem_cthickening_of_dist_le _ y δ _ (subset_tsupport φ hy) ?_
    rw [dist_eq_norm, add_sub_cancel_right]
    exact ha.le.trans hrδ
  · rw [key z 1, ← Real.dist_eq]
    refine dist_convolution_le hε.le b.support_normed_eq.subset b.nonneg_normed b.integral_normed
      (hG 1).aestronglyMeasurable fun x hx => (h1 ?_).le
    rw [mem_ball, hbr] at hx
    exact hx.trans_le hrr1
  · rw [key z I, ← Real.dist_eq]
    refine dist_convolution_le hε.le b.support_normed_eq.subset b.nonneg_normed b.integral_normed
      (hG I).aestronglyMeasurable fun x hx => (h2 ?_).le
    rw [mem_ball, hbr] at hx
    exact hx.trans_le hrr2

/-- `D(ψ : ℂ → ℂ) z v = (Dψ z v : ℂ)` for a differentiable real `ψ`. -/
theorem s07c_fkps_m3a_fderiv_ofReal (ψ : ℂ → ℝ) (h : Differentiable ℝ ψ) (z v : ℂ) :
    fderiv ℝ (fun w => (ψ w : ℂ)) z v = (fderiv ℝ ψ z v : ℂ) := by
  have e := (ofRealCLM.hasFDerivAt.comp z (h z).hasFDerivAt).fderiv
  change fderiv ℝ (ofRealCLM ∘ ψ) z v = _
  rw [e]
  rfl

/-- The curl identity for `C²` tests: `∫ (ψ_y H_x - ψ_x H_y) = 0` for `H` with `L²` generalized partials on `ℂ`
(LZ `sp_integral_beta_eq_zero`). -/
theorem s07c_fkps_m3a_beta {H Hx Hy : ℂ → ℂ} (hH : HasGenPartials H Hx Hy univ 2) (ψ : ℂ → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) :
    ∫ z, ((fderiv ℝ ψ z I : ℂ) * Hx z - (fderiv ℝ ψ z 1 : ℂ) * Hy z) = 0 := by
  have hu : ContDiff ℝ 2 (fun w => (ψ w : ℂ)) := ofRealCLM.contDiff.comp hψ
  have hcu : HasCompactSupport (fun w => (ψ w : ℂ)) := hc.comp_left Complex.ofReal_zero
  have hd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have h0 := sp_integral_beta_eq_zero isOpen_univ hH hu hcu (subset_univ _)
  rw [Measure.restrict_univ] at h0
  simp only [sp_beta_eq, s07c_fkps_m3a_fderiv_ofReal ψ hd] at h0
  rw [integral_const_mul] at h0
  have hI : (I / 2 : ℂ) ≠ 0 := div_ne_zero Complex.I_ne_zero two_ne_zero
  exact (mul_eq_zero.1 h0).resolve_left hI

/-- Integrability on a compact `K` of `(a : ℂ) H_x - (b : ℂ) H_y` for continuous `a, b`. -/
theorem s07c_fkps_m3a_form_int {Hx Hy : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K) (hx : IntegrableOn Hx K)
    (hy : IntegrableOn Hy K) (a b : ℂ → ℝ) (ha : Continuous a) (hb : Continuous b) :
    IntegrableOn (fun z => (a z : ℂ) * Hx z - (b z : ℂ) * Hy z) K :=
  (hx.continuousOn_mul (Complex.continuous_ofReal.comp ha).continuousOn hK).sub
    (hy.continuousOn_mul (Complex.continuous_ofReal.comp hb).continuousOn hK)

/-- The curl identity for `C¹` tests: `∫ (φ_y H_x - φ_x H_y) = 0` (mollify `φ`, apply `s07c_fkps_m3a_beta`, pass to
the limit on the compact `cthickening 1 (tsupport φ)`). -/
theorem s07c_fkps_m3a_curl {H Hx Hy : ℂ → ℂ} (hH : HasGenPartials H Hx Hy univ 2) (φ : ℂ → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    ∫ z, ((fderiv ℝ φ z I : ℂ) * Hx z - (fderiv ℝ φ z 1 : ℂ) * Hy z) = 0 := by
  set K := cthickening 1 (tsupport φ) with hKdef
  have hK : IsCompact K := hc.isCompact.cthickening
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hHx : IntegrableOn Hx K := (hH.1 K (subset_univ _) hK).1.integrable one_le_two
  have hHy : IntegrableOn Hy K := (hH.1 K (subset_univ _) hK).2.integrable one_le_two
  have hdφ : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hφK : tsupport φ ⊆ K := self_subset_cthickening _
  have hform : ∀ ψ : ℂ → ℝ, tsupport ψ ⊆ K →
      ∫ z, ((fderiv ℝ ψ z I : ℂ) * Hx z - (fderiv ℝ ψ z 1 : ℂ) * Hy z) =
        ∫ z in K, ((fderiv ℝ ψ z I : ℂ) * Hx z - (fderiv ℝ ψ z 1 : ℂ) * Hy z) := by
    intro ψ hψK
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
    rw [s07c_fkps_m3a_fderiv_zero ψ z fun h => hz (hψK h)]
    simp
  have hA0 : 0 ≤ ∫ z in K, (‖Hx z‖ + ‖Hy z‖) :=
    setIntegral_nonneg hK.measurableSet fun z _ => add_nonneg (norm_nonneg _) (norm_nonneg _)
  set A := ∫ z in K, (‖Hx z‖ + ‖Hy z‖) with hAdef
  rw [hform φ hφK]
  refine norm_eq_zero.1 (le_antisymm ?_ (norm_nonneg _))
  refine le_of_forall_pos_le_add fun η hη => ?_
  have hA1 : 0 < A + 1 := by linarith
  set ε := η / (A + 1) with hεdef
  have hε : 0 < ε := div_pos hη hA1
  obtain ⟨ψ, hψ2, hψc, hψs, hψd⟩ := s07c_fkps_m3a_moll φ hφ hc 1 ε one_pos hε
  have h0 := s07c_fkps_m3a_beta hH ψ hψ2 hψc
  rw [hform ψ hψs] at h0
  have hdψ : Continuous (fderiv ℝ ψ) := hψ2.continuous_fderiv (by norm_num)
  have hIφ := s07c_fkps_m3a_form_int hK hHx hHy (fun z => fderiv ℝ φ z I) (fun z => fderiv ℝ φ z 1)
    (hdφ.clm_apply continuous_const) (hdφ.clm_apply continuous_const)
  have hIψ := s07c_fkps_m3a_form_int hK hHx hHy (fun z => fderiv ℝ ψ z I) (fun z => fderiv ℝ ψ z 1)
    (hdψ.clm_apply continuous_const) (hdψ.clm_apply continuous_const)
  have hbd : Integrable (fun z => ε * (‖Hx z‖ + ‖Hy z‖)) (volume.restrict K) :=
    (hHx.norm.add hHy.norm).const_mul ε
  calc ‖∫ z in K, ((fderiv ℝ φ z I : ℂ) * Hx z - (fderiv ℝ φ z 1 : ℂ) * Hy z)‖
      = ‖(∫ z in K, ((fderiv ℝ φ z I : ℂ) * Hx z - (fderiv ℝ φ z 1 : ℂ) * Hy z)) -
          ∫ z in K, ((fderiv ℝ ψ z I : ℂ) * Hx z - (fderiv ℝ ψ z 1 : ℂ) * Hy z)‖ := by rw [h0, sub_zero]
    _ = ‖∫ z in K, (((fderiv ℝ φ z I : ℂ) * Hx z - (fderiv ℝ φ z 1 : ℂ) * Hy z) -
          ((fderiv ℝ ψ z I : ℂ) * Hx z - (fderiv ℝ ψ z 1 : ℂ) * Hy z))‖ := by
        rw [integral_sub hIφ hIψ]
    _ ≤ ∫ z in K, ε * (‖Hx z‖ + ‖Hy z‖) := by
        refine norm_integral_le_of_norm_le hbd (Eventually.of_forall fun z => ?_)
        obtain ⟨h1, h2⟩ := hψd z
        have e : ((fderiv ℝ φ z I : ℂ) * Hx z - (fderiv ℝ φ z 1 : ℂ) * Hy z) -
            ((fderiv ℝ ψ z I : ℂ) * Hx z - (fderiv ℝ ψ z 1 : ℂ) * Hy z) =
            ((fderiv ℝ φ z I - fderiv ℝ ψ z I : ℝ) : ℂ) * Hx z -
              ((fderiv ℝ φ z 1 - fderiv ℝ ψ z 1 : ℝ) : ℂ) * Hy z := by
          push_cast; ring
        rw [e]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_sub_comm, abs_sub_comm (fderiv ℝ φ z 1), mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
          (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
    _ = ε * A := integral_const_mul ε _
    _ ≤ 0 + η := by
        rw [zero_add, hεdef, div_mul_eq_mul_div, div_le_iff₀ hA1]
        nlinarith

/-- A map with `L²` generalized partials on `ℂ` is continuous (locally uniform limit of `C¹` maps). -/
theorem s07c_fkps_m3a_cont {F Fx Fy : ℂ → ℂ} (hF : HasGenPartials F Fx Fy univ 2) : Continuous F := by
  obtain ⟨_, Fn, hFnC, hFnU, _⟩ := hF
  have := hFnU.continuousOn (Filter.Frequently.of_forall fun n => (hFnC n).continuousOn)
  rwa [continuousOn_univ] at this

/-- A real linear functional on `ℂ`: `L c = c.re L 1 + c.im L I`. -/
theorem s07c_fkps_m3a_lin (L : ℂ →L[ℝ] ℝ) (c : ℂ) : L c = c.re * L 1 + c.im * L I := by
  have e : c = c.re • (1 : ℂ) + c.im • I := by
    rw [Complex.real_smul, Complex.real_smul, mul_one]
    exact (Complex.re_add_im c).symm
  conv_lhs => rw [e]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- `Dv(w) c = Re(p(w) c)` with `p = v_x - i v_y`. -/
theorem s07c_fkps_m3a_dv (v : ℂ → ℝ) (w c : ℂ) :
    fderiv ℝ v w c = (((fderiv ℝ v w 1 : ℂ) - I * (fderiv ℝ v w I : ℂ)) * c).re := by
  rw [s07c_fkps_m3a_lin (fderiv ℝ v w) c]
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- Algebra for P2: `Re(pa) + i Re(pb) = conj(p ∂) + p ∂̄` with `∂ = (a - ib)/2`, `∂̄ = (a + ib)/2`. -/
theorem s07c_fkps_m3a_alg_g (p a b : ℂ) :
    (((p * a).re : ℂ) + I * ((p * b).re : ℂ)) = conj (p * ((a - I * b) / 2)) + p * ((a + I * b) / 2) := by
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.div_ofNat_re, Complex.div_ofNat_im] <;> ring

/-- Algebra for P4: with `g = conj(p∂) + p∂̄`, `V = -2p∂̄`, `Hx = pa`, `Hy = pb`, `w = x + iy`:
`Re(ḡ w) = -Im(y Hx - x Hy) - Re(V̄ w)`. -/
theorem s07c_fkps_m3a_alg_p4 (p a b : ℂ) (x y : ℝ) :
    (conj (conj (p * ((a - I * b) / 2)) + p * ((a + I * b) / 2)) * ((x : ℂ) + (y : ℂ) * I)).re =
      -(((y : ℂ) * (p * a) - (x : ℂ) * (p * b)).im) -
        (conj (-(2 * (p * ((a + I * b) / 2)))) * ((x : ℂ) + (y : ℂ) * I)).re := by
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.neg_re, Complex.neg_im, Complex.re_ofNat,
    Complex.im_ofNat]
  ring

/-- Pointwise bounds `|g|, |V| ≤ |p| (|a| + |b|)`. -/
theorem s07c_fkps_m3a_bd (p a b : ℂ) :
    ‖conj (p * ((a - I * b) / 2)) + p * ((a + I * b) / 2)‖ ≤ ‖p‖ * (‖a‖ + ‖b‖) ∧
      ‖-(2 * (p * ((a + I * b) / 2)))‖ ≤ ‖p‖ * (‖a‖ + ‖b‖) := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have h1 : ‖(a - I * b) / 2‖ ≤ (‖a‖ + ‖b‖) / 2 := by
    rw [norm_div, h2]
    gcongr
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
  have h1' : ‖(a + I * b) / 2‖ ≤ (‖a‖ + ‖b‖) / 2 := by
    rw [norm_div, h2]
    gcongr
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
  have k1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg p)
  have k2 := mul_le_mul_of_nonneg_left h1' (norm_nonneg p)
  constructor
  · refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_conj, norm_mul, norm_mul]
    linarith
  · rw [norm_neg, norm_mul, norm_mul, h2]
    linarith

/-- Pointwise P3: if `|A| + |B| ≤ K(|A| - |B|)` (`K ≥ 1`) and `|B/A| ≤ 1/2`, then
`|-2pB| ≤ 4 |B/A| |conj(pA) + pB|`. -/
theorem s07c_fkps_m3a_p3 (p A B : ℂ) (K : ℝ) (hK : 1 ≤ K) (h94 : ‖A‖ + ‖B‖ ≤ K * (‖A‖ - ‖B‖))
    (hμ : ‖B / A‖ ≤ 1 / 2) : ‖-(2 * (p * B))‖ ≤ 4 * ‖B / A‖ * ‖conj (p * A) + p * B‖ := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [norm_neg, norm_mul, norm_mul, h2]
  by_cases hA : A = 0
  · rw [hA, norm_zero] at h94
    have hB : ‖B‖ = 0 := le_antisymm (by nlinarith [norm_nonneg B]) (norm_nonneg B)
    rw [hB, mul_zero, mul_zero]
    positivity
  · have hAn : 0 < ‖A‖ := norm_pos_iff.2 hA
    have hm0 : 0 ≤ ‖B / A‖ := norm_nonneg _
    have hBm : ‖B‖ = ‖B / A‖ * ‖A‖ := by rw [norm_div, div_mul_cancel₀ _ hAn.ne']
    have hlow : ‖p‖ * ‖A‖ - ‖p‖ * ‖B‖ ≤ ‖conj (p * A) + p * B‖ := by
      have := norm_sub_norm_le (conj (p * A)) (-(p * B))
      rwa [sub_neg_eq_add, norm_neg, Complex.norm_conj, norm_mul, norm_mul] at this
    rw [hBm] at hlow ⊢
    have k := mul_le_mul_of_nonneg_left hlow (by positivity : (0 : ℝ) ≤ 4 * ‖B / A‖)
    have k2 : 0 ≤ ‖B / A‖ * (‖p‖ * ‖A‖) * (1 - 2 * ‖B / A‖) :=
      mul_nonneg (mul_nonneg hm0 (mul_nonneg (norm_nonneg p) hAn.le)) (by linarith)
    nlinarith

/-- For `h` complex-differentiable at `w`, `Dh(w) c = h'(w) c`. -/
theorem s07c_fkps_m3a_hderiv {h : ℂ → ℂ} {w : ℂ} (hd : DifferentiableAt ℂ h w) (c : ℂ) :
    fderiv ℝ h w c = deriv h w * c := by
  rw [(hd.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp [mul_comm]

/-- If `Re h = v` on an open `U` with `h` holomorphic, then `v_x - i v_y = h'` on `U`. -/
theorem s07c_fkps_m3a_p_eq {v : ℂ → ℝ} {h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hh : AnalyticOnNhd ℂ h U)
    (hre : U.EqOn (fun z => (h z).re) v) {w : ℂ} (hw : w ∈ U) :
    (fderiv ℝ v w 1 : ℂ) - I * (fderiv ℝ v w I : ℂ) = deriv h w := by
  have hd : DifferentiableAt ℂ h w := (hh w hw).differentiableAt
  have e : v =ᶠ[𝓝 w] (⇑reCLM ∘ h) := by
    filter_upwards [hU.mem_nhds hw] with z hz
    rw [Function.comp_apply, reCLM_apply]
    exact (hre hz).symm
  have hF := (reCLM.hasFDerivAt.comp w (hd.hasFDerivAt.restrictScalars ℝ)).congr_of_eventuallyEq e
  have k : ∀ c, fderiv ℝ v w c = (deriv h w * c).re := by
    intro c
    have := s07c_fkps_m3a_hderiv hd c
    rw [(hd.hasFDerivAt.restrictScalars ℝ).fderiv] at this
    rw [hF.fderiv, ContinuousLinearMap.comp_apply, reCLM_apply, this]
  rw [k, k]
  apply Complex.ext <;> simp

/-- A `C¹` cutoff of a holomorphic `h` on `𝔻`: for a compact `S ⊆ 𝔻` there is a `C¹` map `Φ : ℂ → ℂ` with
`DΦ(w) c = h'(w) c` for `w ∈ S`. -/
theorem s07c_fkps_m3a_cutoff {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (ball 0 1)) {S : Set ℂ} (hS : IsCompact S)
    (hSs : S ⊆ ball 0 1) :
    ∃ Φ : ℂ → ℂ, ContDiff ℝ 1 Φ ∧ ∀ w ∈ S, ∀ c, fderiv ℝ Φ w c = deriv h w * c := by
  obtain ⟨r, hr1, hSr⟩ := exists_lt_subset_ball hS.isClosed hSs
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℝ, s0 = max r (1 / 2) := ⟨_, rfl⟩
  have hs0p : 0 < s0 := by rw [hs0]; exact lt_max_of_lt_right (by norm_num)
  have hs01 : s0 < 1 := by rw [hs0]; exact max_lt hr1 (by norm_num)
  have hrs : r ≤ s0 := by rw [hs0]; exact le_max_left _ _
  let b : ContDiffBump (0 : ℂ) := ⟨s0, (s0 + 1) / 2, hs0p, by linarith⟩
  have hbin : b.rIn = s0 := rfl
  have hbout : b.rOut = (s0 + 1) / 2 := rfl
  refine ⟨fun w => ((b w : ℝ) : ℂ) * h w, ?_, ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun w => ?_
    by_cases hw : w ∈ ball (0 : ℂ) 1
    · exact (ofRealCLM.contDiff.comp b.contDiff).contDiffAt.mul
        (((hh w hw).contDiffAt).restrict_scalars ℝ)
    · have hwt : w ∉ tsupport b := by
        rw [b.tsupport_eq]
        intro hw'
        apply hw
        rw [mem_closedBall, hbout] at hw'
        rw [mem_ball]
        linarith
      have e := notMem_tsupport_iff_eventuallyEq.1 hwt
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [e] with z hz
      simp only [Pi.zero_apply] at hz
      simp [hz]
  · intro w hw c
    have hwb : w ∈ ball (0 : ℂ) s0 := ball_subset_ball hrs (hSr hw)
    have e : (fun w => ((b w : ℝ) : ℂ) * h w) =ᶠ[𝓝 w] h := by
      filter_upwards [isOpen_ball.mem_nhds hwb] with z hz
      rw [b.one_of_mem_closedBall (by rw [hbin]; exact ball_subset_closedBall hz)]
      simp
    rw [e.fderiv_eq]
    exact s07c_fkps_m3a_hderiv (hh w (hSs hw)).differentiableAt c

/-- M3a (pullback package). Let `F` be a `K`-qc homeomorphism of `ℂ` with `F(𝔻) = 𝔻`, `F 0 = 0` and
`|μ_F| ≤ 1/2` a.e. on `𝔻`, and let `v` be `C²` on `ℂ` and harmonic on `𝔻`. Then `u₁ = v ∘ F` has a weak gradient
`g ∈ L²(𝔻)` on `𝔻`, and there is `V` with
`|V| ≤ 4 |μ_F| |g|` a.e. on `𝔻` and `∫ ⟨g, ∇φ⟩ = -∫ ⟨V, ∇φ⟩` for every `C¹` test function `φ` supported in `𝔻`
(that is, `Δu₁ = -div V`). -/
theorem s07c_fkps_m3a_pullback : ∀ (F : ℂ → ℂ) (K : ℝ),
    IsKQC F univ K → F '' univ = univ → F '' unitDisc = unitDisc → F 0 = 0 →
    (∀ᵐ z, z ∈ unitDisc → ‖LiZhongQC.complexDilatation F z‖ ≤ 1 / 2) →
    ∀ v : ℂ → ℝ, ContDiff ℝ 2 v → InnerProductSpace.HarmonicOnNhd v unitDisc →
    ∃ g V : ℂ → ℂ, AEMeasurable g ∧ AEMeasurable V ∧
      (∫⁻ z in unitDisc, ‖g z‖ₑ ^ 2 < ⊤) ∧
      (∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
        ∫ z, (v (F z) : ℂ) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I) =
          -∫ z, (φ z : ℂ) * g z) ∧
      (∀ᵐ z, z ∈ unitDisc → ‖V z‖ ≤ 4 * ‖LiZhongQC.complexDilatation F z‖ * ‖g z‖) ∧
      (∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
        ∫ z, (conj (g z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re =
          -∫ z, (conj (V z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re) := by
  intro F K hq _hFuniv hFD _hF0 hμ v hv hharm
  -- `F '' univ = univ` and `F 0 = 0` are not needed: the package only uses `F(𝔻) = 𝔻` and the q.c. structure.
  have hP : HasGenPartials F (partialX F) (partialY F) univ 2 := (thm9_5_L2_derivatives hq).1
  have hFc : Continuous F := s07c_fkps_m3a_cont hP
  have hK1 : 1 ≤ K := hq.2.1
  have hdiff : ∀ᵐ z, DifferentiableAt ℝ F z := by
    have := thm9_3_differentiable_ae hq
    rwa [Measure.restrict_univ] at this
  have h94 : ∀ᵐ z, ‖dz F z‖ + ‖dzbar F z‖ ≤ K * (‖dz F z‖ - ‖dzbar F z‖) := by
    have := thm9_4_dilatation_ae hq
    rwa [Measure.restrict_univ] at this
  have hrel : ∀ᵐ z, dz F z = (partialX F z - I * partialY F z) / 2 ∧
      dzbar F z = (partialX F z + I * partialY F z) / 2 := by
    filter_upwards [hdiff] with z hz
    rw [partialX_eq_of_differentiableAt hz, partialY_eq_of_differentiableAt hz]
    exact ⟨rfl, rfl⟩
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hvd : Differentiable ℝ v := hv1.differentiable (by norm_num)
  have hdv : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by norm_num)
  obtain ⟨p, hp⟩ : ∃ p : ℂ → ℂ, p = fun w => (fderiv ℝ v w 1 : ℂ) - I * (fderiv ℝ v w I : ℂ) := ⟨_, rfl⟩
  have hpz : ∀ w, p w = (fderiv ℝ v w 1 : ℂ) - I * (fderiv ℝ v w I : ℂ) := fun w => by rw [hp]
  have hpc : Continuous p := by
    rw [hp]
    exact (Complex.continuous_ofReal.comp (hdv.clm_apply continuous_const)).sub
      (continuous_const.mul (Complex.continuous_ofReal.comp (hdv.clm_apply continuous_const)))
  have hpFc : Continuous fun z => p (F z) := hpc.comp hFc
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, g = fun z => conj (p (F z) * dz F z) + p (F z) * dzbar F z := ⟨_, rfl⟩
  have hgz : ∀ z, g z = conj (p (F z) * dz F z) + p (F z) * dzbar F z := fun z => by rw [hg]
  obtain ⟨V, hV⟩ : ∃ V : ℂ → ℂ, V = fun z => -(2 * (p (F z) * dzbar F z)) := ⟨_, rfl⟩
  have hVz : ∀ z, V z = -(2 * (p (F z) * dzbar F z)) := fun z => by rw [hV]
  have hdzm : Measurable (dz F) := by
    change Measurable fun z => (fderiv ℝ F z 1 - I * fderiv ℝ F z I) / 2
    exact ((measurable_fderiv_apply_const ℝ F 1).sub
      (measurable_const.mul (measurable_fderiv_apply_const ℝ F I))).div_const 2
  have hdzbm : Measurable (dzbar F) := by
    change Measurable fun z => (fderiv ℝ F z 1 + I * fderiv ℝ F z I) / 2
    exact ((measurable_fderiv_apply_const ℝ F 1).add
      (measurable_const.mul (measurable_fderiv_apply_const ℝ F I))).div_const 2
  have hgm : Measurable g := by
    rw [hg]
    exact (Complex.continuous_conj.measurable.comp (hpFc.measurable.mul hdzm)).add (hpFc.measurable.mul hdzbm)
  have hVm : Measurable V := by
    rw [hV]
    exact (measurable_const.mul (hpFc.measurable.mul hdzbm)).neg
  -- pointwise bounds `|g|, |V| ≤ |p ∘ F| (|F_x| + |F_y|)` a.e.
  have hbd : ∀ᵐ z, ‖g z‖ ≤ ‖p (F z)‖ * (‖partialX F z‖ + ‖partialY F z‖) ∧
      ‖V z‖ ≤ ‖p (F z)‖ * (‖partialX F z‖ + ‖partialY F z‖) := by
    filter_upwards [hrel] with z hz
    rw [hgz, hVz, hz.1, hz.2]
    exact s07c_fkps_m3a_bd _ _ _
  -- the holomorphic function with `Re h = v` on `𝔻`
  obtain ⟨h, hh, hre⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq
    (show InnerProductSpace.HarmonicOnNhd v (ball (0 : ℂ) 1) from hharm)
  refine ⟨g, V, hgm.aemeasurable, hVm.aemeasurable, ?_, ?_, ?_, ?_⟩
  · -- `L²` on `𝔻`
    have hCb : IsCompact (closedBall (0 : ℂ) 1) := isCompact_closedBall 0 1
    obtain ⟨M, hM⟩ := hCb.exists_bound_of_continuousOn hpFc.continuousOn
    have hFL := hP.1 (closedBall (0 : ℂ) 1) (subset_univ _) hCb
    have hS : MemLp (fun z => ‖partialX F z‖ + ‖partialY F z‖) 2 (volume.restrict (closedBall (0 : ℂ) 1)) :=
      hFL.1.norm.add hFL.2.norm
    have hgL : MemLp g 2 (volume.restrict (closedBall (0 : ℂ) 1)) := by
      refine hS.of_le_mul (c := M) hgm.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_closedBall, ae_restrict_of_ae hbd] with z hz hb
      rw [Real.norm_of_nonneg (by positivity)]
      exact hb.1.trans (mul_le_mul_of_nonneg_right (hM z hz) (by positivity))
    have hgD : MemLp g 2 (volume.restrict unitDisc) :=
      hgL.mono_measure (Measure.restrict_mono ball_subset_closedBall le_rfl)
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hgD.eLpNorm_lt_top
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using h
  · -- P2: the weak `∂̄` derivative of `v ∘ F` (times `2`) is `g`
    intro φ hφ hc _hs
    have hT : IsCompact (tsupport φ) := hc.isCompact
    have : IsFiniteMeasure (volume.restrict (tsupport φ)) :=
      isFiniteMeasure_restrict.2 hT.measure_lt_top.ne
    have hdφ : Differentiable ℝ φ := hφ.differentiable (by norm_num)
    have hdφc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
    have hψ : ContDiff ℝ 1 (fun z => (φ z : ℂ)) := ofRealCLM.contDiff.comp hφ
    have hcψ : HasCompactSupport (fun z => (φ z : ℂ)) := hc.comp_left Complex.ofReal_zero
    have hG := s07c_fkps_m3a_chain hP (fun w => (v w : ℂ)) (ofRealCLM.contDiff.comp hv1)
    have eGx : ∀ c : ℂ → ℂ, (fun z => fderiv ℝ (fun w => (v w : ℂ)) (F z) (c z)) =
        fun z => (fderiv ℝ v (F z) (c z) : ℂ) := fun c =>
      funext fun z => s07c_fkps_m3a_fderiv_ofReal v hvd (F z) (c z)
    rw [eGx, eGx] at hG
    obtain ⟨i1, i2⟩ := sp_ibp isOpen_univ hG hψ hcψ (subset_univ _)
    have i1' : ∫ z, (fderiv ℝ φ z 1 : ℂ) * (v (F z) : ℂ) =
        -∫ z, (φ z : ℂ) * (fderiv ℝ v (F z) (partialX F z) : ℂ) := by
      simp only [Measure.restrict_univ, s07c_fkps_m3a_fderiv_ofReal φ hdφ] at i1
      exact i1
    have i2' : ∫ z, (fderiv ℝ φ z I : ℂ) * (v (F z) : ℂ) =
        -∫ z, (φ z : ℂ) * (fderiv ℝ v (F z) (partialY F z) : ℂ) := by
      simp only [Measure.restrict_univ, s07c_fkps_m3a_fderiv_ofReal φ hdφ] at i2
      exact i2
    have hvF : Continuous fun z => (v (F z) : ℂ) := Complex.continuous_ofReal.comp (hv1.continuous.comp hFc)
    have hI : ∀ e : ℂ, Integrable fun z => (fderiv ℝ φ z e : ℂ) * (v (F z) : ℂ) := by
      intro e
      refine (ContinuousOn.integrableOn_compact hT
        ((Complex.continuous_ofReal.comp (hdφc.clm_apply continuous_const)).mul hvF).continuousOn
        ).integrable_of_forall_notMem_eq_zero fun z hz => ?_
      simp [s07c_fkps_m3a_fderiv_zero φ z hz]
    have hGL := hG.1 (tsupport φ) (subset_univ _) hT
    have hJ : ∀ c : ℂ → ℂ, MemLp (fun z => (fderiv ℝ v (F z) (c z) : ℂ)) 2 (volume.restrict (tsupport φ)) →
        Integrable fun z => (φ z : ℂ) * (fderiv ℝ v (F z) (c z) : ℂ) := by
      intro c hcL
      have hcI : IntegrableOn (fun z => (fderiv ℝ v (F z) (c z) : ℂ)) (tsupport φ) := hcL.integrable one_le_two
      refine (hcI.continuousOn_mul
        (Complex.continuous_ofReal.comp hφ.continuous).continuousOn hT).integrable_of_forall_notMem_eq_zero
        fun z hz => ?_
      simp [image_eq_zero_of_notMem_tsupport hz]
    have hJ1 := hJ (partialX F) hGL.1
    have hJ2 := hJ (partialY F) hGL.2
    calc ∫ z, (v (F z) : ℂ) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)
        = ∫ z, ((fderiv ℝ φ z 1 : ℂ) * (v (F z) : ℂ) + I * ((fderiv ℝ φ z I : ℂ) * (v (F z) : ℂ))) := by
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          ring
      _ = (∫ z, (fderiv ℝ φ z 1 : ℂ) * (v (F z) : ℂ)) + I * ∫ z, (fderiv ℝ φ z I : ℂ) * (v (F z) : ℂ) := by
          rw [integral_add (hI 1) ((hI I).const_mul I), integral_const_mul]
      _ = -((∫ z, (φ z : ℂ) * (fderiv ℝ v (F z) (partialX F z) : ℂ)) +
            I * ∫ z, (φ z : ℂ) * (fderiv ℝ v (F z) (partialY F z) : ℂ)) := by
          rw [i1', i2']
          ring
      _ = -∫ z, ((φ z : ℂ) * (fderiv ℝ v (F z) (partialX F z) : ℂ) +
            I * ((φ z : ℂ) * (fderiv ℝ v (F z) (partialY F z) : ℂ))) := by
          rw [integral_add hJ1 (hJ2.const_mul I), integral_const_mul]
      _ = -∫ z, (φ z : ℂ) * g z := by
          congr 1
          refine integral_congr_ae ?_
          filter_upwards [hrel] with z hz
          rw [hgz, s07c_fkps_m3a_dv v (F z) (partialX F z), s07c_fkps_m3a_dv v (F z) (partialY F z), hpz,
            hz.1, hz.2, ← s07c_fkps_m3a_alg_g]
          ring
  · -- P3
    filter_upwards [h94, hμ] with z h1 h3 hzD
    rw [hVz, hgz]
    exact s07c_fkps_m3a_p3 (p (F z)) (dz F z) (dzbar F z) K hK1 h1 (h3 hzD)
  · -- P4: `∫ Re(ḡ ∇φ) = -∫ Re(V̄ ∇φ)`, via the curl identity for `H = Φ ∘ F` with `Φ = h` near `F(supp φ)`
    intro φ hφ hc hs
    have hT : IsCompact (tsupport φ) := hc.isCompact
    have : IsFiniteMeasure (volume.restrict (tsupport φ)) :=
      isFiniteMeasure_restrict.2 hT.measure_lt_top.ne
    have hdφc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
    have hTD : F '' tsupport φ ⊆ ball (0 : ℂ) 1 := by
      rintro _ ⟨z, hz, rfl⟩
      have : F z ∈ F '' unitDisc := ⟨z, hs hz, rfl⟩
      rw [hFD] at this
      exact this
    obtain ⟨Φ, hΦ, hΦd⟩ := s07c_fkps_m3a_cutoff hh (hT.image hFc) hTD
    have hH := s07c_fkps_m3a_chain hP Φ hΦ
    have hcurl := s07c_fkps_m3a_curl hH φ hφ hc
    have hHL := hH.1 (tsupport φ) (subset_univ _) hT
    have hφx : Continuous fun z => fderiv ℝ φ z 1 := hdφc.clm_apply continuous_const
    have hφy : Continuous fun z => fderiv ℝ φ z I := hdφc.clm_apply continuous_const
    have hcI : Integrable fun z => ((fderiv ℝ φ z I : ℂ) * fderiv ℝ Φ (F z) (partialX F z) -
        (fderiv ℝ φ z 1 : ℂ) * fderiv ℝ Φ (F z) (partialY F z)) := by
      have := (s07c_fkps_m3a_form_int hT (hHL.1.integrable one_le_two) (hHL.2.integrable one_le_two)
        (fun z => fderiv ℝ φ z I) (fun z => fderiv ℝ φ z 1) hφy hφx).integrable_of_forall_notMem_eq_zero
        (fun z hz => by simp [s07c_fkps_m3a_fderiv_zero φ z hz])
      exact this
    have hcIm : Integrable fun z => ((fderiv ℝ φ z I : ℂ) * fderiv ℝ Φ (F z) (partialX F z) -
        (fderiv ℝ φ z 1 : ℂ) * fderiv ℝ Φ (F z) (partialY F z)).im :=
      hcI.norm.mono' (Complex.measurable_im.comp_aemeasurable hcI.aemeasurable).aestronglyMeasurable
        (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact Complex.abs_im_le_norm _)
    have him : ∫ z, ((fderiv ℝ φ z I : ℂ) * fderiv ℝ Φ (F z) (partialX F z) -
        (fderiv ℝ φ z 1 : ℂ) * fderiv ℝ Φ (F z) (partialY F z)).im = 0 := by
      have := Complex.imCLM.integral_comp_comm hcI
      simp only [Complex.imCLM_apply] at this
      rw [this, hcurl, Complex.zero_im]
    have hwc : Continuous fun z => ((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I :=
      (Complex.continuous_ofReal.comp hφx).add ((Complex.continuous_ofReal.comp hφy).mul continuous_const)
    have hFL := hP.1 (tsupport φ) (subset_univ _) hT
    have hBI : Integrable fun z => ‖p (F z)‖ * ‖((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I‖ *
        (‖partialX F z‖ + ‖partialY F z‖) := by
      have hS : IntegrableOn (fun z => ‖partialX F z‖ + ‖partialY F z‖) (tsupport φ) :=
        (hFL.1.integrable one_le_two).norm.add (hFL.2.integrable one_le_two).norm
      exact (hS.continuousOn_mul (hpFc.norm.mul hwc.norm).continuousOn hT).integrable_of_forall_notMem_eq_zero
        fun z hz => by simp [s07c_fkps_m3a_fderiv_zero φ z hz]
    have hterm : ∀ G : ℂ → ℂ, Measurable G →
        (∀ᵐ z, ‖G z‖ ≤ ‖p (F z)‖ * (‖partialX F z‖ + ‖partialY F z‖)) →
        Integrable fun z => (conj (G z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re := by
      intro G hGm hGb
      refine hBI.mono' (Complex.measurable_re.comp
        ((Complex.continuous_conj.measurable.comp hGm).mul hwc.measurable)).aestronglyMeasurable ?_
      filter_upwards [hGb] with z hz
      rw [Real.norm_eq_abs]
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_conj]
      exact (mul_le_mul_of_nonneg_right hz (norm_nonneg _)).trans_eq (by ring)
    have hVI := hterm V hVm (hbd.mono fun z hz => hz.2)
    have hpt : ∀ᵐ z, (conj (g z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re =
        -((fderiv ℝ φ z I : ℂ) * fderiv ℝ Φ (F z) (partialX F z) -
          (fderiv ℝ φ z 1 : ℂ) * fderiv ℝ Φ (F z) (partialY F z)).im -
        (conj (V z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re := by
      filter_upwards [hrel] with z hz
      by_cases hzT : z ∈ tsupport φ
      · have hFz : F z ∈ F '' tsupport φ := ⟨z, hzT, rfl⟩
        have hpd : p (F z) = deriv h (F z) := by
          rw [hpz]
          exact s07c_fkps_m3a_p_eq isOpen_ball hh hre (hTD hFz)
        rw [hΦd (F z) hFz, hΦd (F z) hFz, ← hpd, hgz, hVz, hz.1, hz.2]
        exact s07c_fkps_m3a_alg_p4 _ _ _ _ _
      · simp [s07c_fkps_m3a_fderiv_zero φ z hzT]
    calc ∫ z, (conj (g z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re
        = ∫ z, (-((fderiv ℝ φ z I : ℂ) * fderiv ℝ Φ (F z) (partialX F z) -
            (fderiv ℝ φ z 1 : ℂ) * fderiv ℝ Φ (F z) (partialY F z)).im -
            (conj (V z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re) :=
          integral_congr_ae hpt
      _ = (∫ z, -((fderiv ℝ φ z I : ℂ) * fderiv ℝ Φ (F z) (partialX F z) -
            (fderiv ℝ φ z 1 : ℂ) * fderiv ℝ Φ (F z) (partialY F z)).im) -
            ∫ z, (conj (V z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re :=
          integral_sub hcIm.neg hVI
      _ = -∫ z, (conj (V z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re := by
          rw [integral_neg, him, neg_zero, zero_sub]

/-- Polar coordinates for a radial function on `ℂ`: `∫⁻ G(|z|) dz = 2π ∫⁻_{r > 0} r G(r) dr`. -/
theorem s07c_fkps_m3b_radial (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ z : ℂ, G ‖z‖ = ENNReal.ofReal (2 * π) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * G r := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have ht : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := polarCoord_target
  rw [ht]
  calc ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal p.1 • G ‖Complex.polarCoord.symm p‖
      = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal p.1 * G p.1 := by
        refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) (fun p hp => ?_)
        rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1, smul_eq_mul]
    _ = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ _θ in Ioo (-π) π, ENNReal.ofReal r * G r := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        exact lintegral_prod _
          ((ENNReal.measurable_ofReal.comp measurable_fst).mul (hG.comp measurable_fst)).aemeasurable
    _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * G r * ENNReal.ofReal (2 * π) := by
        refine lintegral_congr fun r => ?_
        rw [setLIntegral_const, Real.volume_Ioo]
        congr 2
        ring
    _ = ENNReal.ofReal (2 * π) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * G r := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]

/-- `∫⁻_{B(c, R)} |z - c|⁻¹ dz = 2π R`. -/
theorem s07c_fkps_m3b_inv_ball (c : ℂ) (R : ℝ) :
    ∫⁻ z in ball c R, ENNReal.ofReal ‖z - c‖⁻¹ = ENNReal.ofReal (2 * π * R) := by
  set G : ℝ → ℝ≥0∞ := (Iio R).indicator (fun r => ENNReal.ofReal r⁻¹) with hGdef
  have hGm : Measurable G :=
    (ENNReal.measurable_ofReal.comp measurable_inv).indicator measurableSet_Iio
  have h1 : ∫⁻ z in ball c R, ENNReal.ofReal ‖z - c‖⁻¹ = ∫⁻ z, G ‖z - c‖ := by
    rw [← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun z => ?_
    simp only [hGdef, Set.indicator, mem_ball, dist_eq_norm, mem_Iio]
  have h2 : ∫⁻ z, G ‖z - c‖ = ∫⁻ z, G ‖z‖ :=
    lintegral_sub_right_eq_self (fun z => G ‖z‖) c
  have h3 : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * G r = ENNReal.ofReal R := by
    calc ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * G r = ∫⁻ r in Ioi (0 : ℝ), (Iio R).indicator 1 r := by
          refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
          by_cases hrR : r < R
          · simp only [hGdef, Set.indicator_of_mem (show r ∈ Iio R from hrR), Pi.one_apply]
            rw [← ENNReal.ofReal_mul hr.le, mul_inv_cancel₀ (ne_of_gt hr), ENNReal.ofReal_one]
          · simp only [hGdef, Set.indicator_of_notMem (show r ∉ Iio R from hrR), mul_zero]
      _ = volume (Ioi (0 : ℝ) ∩ Iio R) := by
          rw [lintegral_indicator_one measurableSet_Iio, Measure.restrict_apply measurableSet_Iio,
            inter_comm]
      _ = ENNReal.ofReal R := by
          rw [Ioi_inter_Iio, Real.volume_Ioo, sub_zero]
  rw [h1, h2, s07c_fkps_m3b_radial G hGm, h3, ← ENNReal.ofReal_mul (by positivity)]

/-- For `Y ∈ 𝔻`: `∫⁻_𝔻 |X - Y|⁻¹ dX ≤ 4π`. -/
theorem s07c_fkps_m3b_inv_disc (Y : ℂ) (hY : Y ∈ unitDisc) :
    ∫⁻ X in unitDisc, ENNReal.ofReal ‖X - Y‖⁻¹ ≤ ENNReal.ofReal (4 * π) := by
  have hsub : unitDisc ⊆ ball Y 2 := by
    intro X hX
    have hX' : ‖X‖ < 1 := mem_ball_zero_iff.1 hX
    have hY' : ‖Y‖ < 1 := mem_ball_zero_iff.1 hY
    rw [mem_ball, dist_eq_norm]
    calc ‖X - Y‖ ≤ ‖X‖ + ‖Y‖ := norm_sub_le X Y
      _ < 2 := by linarith
  calc ∫⁻ X in unitDisc, ENNReal.ofReal ‖X - Y‖⁻¹ ≤ ∫⁻ X in ball Y 2, ENNReal.ofReal ‖X - Y‖⁻¹ :=
        lintegral_mono_set hsub
    _ = ENNReal.ofReal (4 * π) := by
        rw [s07c_fkps_m3b_inv_ball Y 2]
        congr 1
        ring

/-- For `X, Y ∈ 𝔻`, `Y ≠ X`: `|∇_Y G₀(X, Y)| ≤ 1 / (π |X - Y|)`. -/
theorem s07c_fkps_m3b_kernel_le (X Y : ℂ) (hX : X ∈ unitDisc) (hY : Y ∈ unitDisc) (hne : Y ≠ X) :
    ‖((1 - ‖X‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (X - Y) * (1 - X * conj Y))‖ ≤ (π * ‖X - Y‖)⁻¹ := by
  have hk := s07c_fkps_m3_kernel X hX Y hY hne
  have hXn : ‖X‖ < 1 := mem_ball_zero_iff.1 hX
  have hd : 0 < ‖X - Y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne.symm)
  have hδ : 0 < 1 - ‖X‖ := by linarith
  refine hk.trans ?_
  rw [div_le_iff₀ (by positivity)]
  have hm : 1 - ‖X‖ ≤ max ‖X - Y‖ (1 - ‖X‖) := le_max_right _ _
  have hπ := Real.pi_pos
  have e1 : (π * ‖X - Y‖)⁻¹ * (2 * π * ‖X - Y‖ * max ‖X - Y‖ (1 - ‖X‖)) =
      2 * max ‖X - Y‖ (1 - ‖X‖) := by
    field_simp
  rw [e1]
  nlinarith [norm_nonneg X]

/-- For `φ ∈ C²`: `D(x ↦ Dφ(x) w)(z) v = D²φ(z) v w`. -/
theorem s07c_fkps_m3b_fderiv_apply (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (z v w : ℂ) :
    fderiv ℝ (fun x => fderiv ℝ φ x w) z v = fderiv ℝ (fderiv ℝ φ) z v w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)) z
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp

/-- For `φ ∈ C²`, `x ↦ Dφ(x) w` is `C¹`. -/
theorem s07c_fkps_m3b_contDiff_apply (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (w : ℂ) :
    ContDiff ℝ 1 (fun x => fderiv ℝ φ x w) :=
  (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- The Laplacian on `ℂ` in terms of first derivatives of the partials. -/
theorem s07c_fkps_m3b_lap (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (z : ℂ) :
    Laplacian.laplacian φ z = fderiv ℝ (fun x => fderiv ℝ φ x 1) z 1 + fderiv ℝ (fun x => fderiv ℝ φ x I) z I := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane, s07c_fkps_m3b_fderiv_apply φ hφ,
    s07c_fkps_m3b_fderiv_apply φ hφ]
  simp [iteratedFDeriv_two_apply]

/-- `∂_z̄` of `ψ = ∂_z φ = (φ_x - i φ_y)/2` is `Δφ/4`. -/
theorem s07c_fkps_m3b_dzbar_dz (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (z : ℂ) :
    dzbar (fun x => (1 / 2 : ℂ) * ((fderiv ℝ φ x 1 : ℂ) - I * (fderiv ℝ φ x I : ℂ))) z =
      (Laplacian.laplacian φ z : ℂ) / 4 := by
  set g₁ : ℂ → ℝ := fun x => fderiv ℝ φ x 1 with hg₁
  set g₂ : ℂ → ℝ := fun x => fderiv ℝ φ x I with hg₂
  have hd₁ : DifferentiableAt ℝ g₁ z :=
    ((s07c_fkps_m3b_contDiff_apply φ hφ 1).differentiable (by simp)) z
  have hd₂ : DifferentiableAt ℝ g₂ z :=
    ((s07c_fkps_m3b_contDiff_apply φ hφ I).differentiable (by simp)) z
  have h1 : HasFDerivAt (fun x => (g₁ x : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ g₁ z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hd₁.hasFDerivAt
  have h2 : HasFDerivAt (fun x => (g₂ x : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ g₂ z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hd₂.hasFDerivAt
  have hψ : fderiv ℝ (fun x => (1 / 2 : ℂ) * ((g₁ x : ℂ) - I * (g₂ x : ℂ))) z =
      (1 / 2 : ℂ) • (Complex.ofRealCLM.comp (fderiv ℝ g₁ z) -
        I • Complex.ofRealCLM.comp (fderiv ℝ g₂ z)) :=
    ((h1.sub (h2.const_mul I)).const_mul (1 / 2 : ℂ)).fderiv
  have hsym : fderiv ℝ (fderiv ℝ φ) z 1 I = fderiv ℝ (fderiv ℝ φ) z I 1 :=
    ((hφ.contDiffAt).isSymmSndFDerivAt (by simp)) 1 I
  show (fderiv ℝ (fun x => (1 / 2 : ℂ) * ((g₁ x : ℂ) - I * (g₂ x : ℂ))) z 1 +
      I * fderiv ℝ (fun x => (1 / 2 : ℂ) * ((g₁ x : ℂ) - I * (g₂ x : ℂ))) z I) / 2 = (Laplacian.laplacian φ z : ℂ) / 4
  rw [hψ, s07c_fkps_m3b_lap φ hφ z]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  rw [hg₁, hg₂, s07c_fkps_m3b_fderiv_apply φ hφ, s07c_fkps_m3b_fderiv_apply φ hφ,
    s07c_fkps_m3b_fderiv_apply φ hφ, s07c_fkps_m3b_fderiv_apply φ hφ, hsym]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Part A of the Green kernel identity (Cauchy–Pompeiu): for `φ ∈ C²` with compact support in `𝔻` and
`Y ∈ 𝔻`, `∫_𝔻 Δφ(X) / conj(X - Y) dX = -2π (φ_x(Y) + i φ_y(Y))`. -/
theorem s07c_fkps_m3b_greenA (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (hs : tsupport φ ⊆ unitDisc)
    (Y : ℂ) (hY : Y ∈ unitDisc) :
    ∫ X in unitDisc, (Laplacian.laplacian φ X : ℂ) / conj (X - Y) =
      -(2 * π) * ((fderiv ℝ φ Y 1 : ℂ) + (fderiv ℝ φ Y I : ℂ) * I) := by
  set ψ : ℂ → ℂ := fun x => (1 / 2 : ℂ) * ((fderiv ℝ φ x 1 : ℂ) - I * (fderiv ℝ φ x I : ℂ)) with hψdef
  have hψC : ContDiff ℝ 1 ψ := by
    have c1 := (Complex.ofRealCLM.contDiff.comp (s07c_fkps_m3b_contDiff_apply φ hφ 1))
    have c2 := (Complex.ofRealCLM.contDiff.comp (s07c_fkps_m3b_contDiff_apply φ hφ I))
    exact contDiff_const.mul (c1.sub (contDiff_const.mul c2))
  have hP := eq11_11_pompeiu (c := 0) (R := 1) one_pos hψC.contDiffOn hY
  have hcirc : (∮ z in C(0, 1), ψ z / (z - Y)) = 0 := by
    have heq : EqOn (fun z => ψ z / (z - Y)) (fun _ => (0 : ℂ)) (sphere (0 : ℂ) 1) := by
      intro z hz
      have hz' : z ∉ tsupport φ := by
        intro h
        have h1 : ‖z‖ < 1 := mem_ball_zero_iff.1 (hs h)
        rw [mem_sphere_zero_iff_norm] at hz
        linarith
      simp [hψdef, s07c_fkps_m3a_fderiv_zero φ z hz']
    rw [circleIntegral.integral_congr zero_le_one heq]
    show ∫ θ in (0 : ℝ)..2 * π, deriv (circleMap 0 1) θ • (0 : ℂ) = 0
    simp
  have hdz : ∀ z, dzbar ψ z = (Laplacian.laplacian φ z : ℂ) / 4 := s07c_fkps_m3b_dzbar_dz φ hφ
  simp only [hcirc, mul_zero, zero_sub, hdz] at hP
  -- `ψ Y = -(1/π) ∫ (Δφ/4)/(X - Y)`; conjugate
  have hconj : conj (ψ Y) = -(1 / π : ℂ) * ∫ X in unitDisc, (Laplacian.laplacian φ X : ℂ) / 4 / conj (X - Y) := by
    rw [hP, map_neg, map_mul, ← integral_conj]
    simp only [map_div₀, Complex.conj_ofReal, map_one, map_ofNat]
    rw [neg_mul]
    rfl
  have hψY : conj (ψ Y) = (1 / 2 : ℂ) * ((fderiv ℝ φ Y 1 : ℂ) + (fderiv ℝ φ Y I : ℂ) * I) := by
    simp only [hψdef, map_mul, map_sub, map_div₀, map_one, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I]
    ring
  have hint : ∫ X in unitDisc, (Laplacian.laplacian φ X : ℂ) / 4 / conj (X - Y) =
      (1 / 4 : ℂ) * ∫ X in unitDisc, (Laplacian.laplacian φ X : ℂ) / conj (X - Y) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    simp only
    ring
  rw [hψY, hint] at hconj
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have := hconj
  field_simp at this
  linear_combination (1 / 2 : ℂ) * this

/-- For `φ ∈ C²`, `Δφ` vanishes off `tsupport φ`. -/
theorem s07c_fkps_m3b_lap_zero (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (z : ℂ) (hz : z ∉ tsupport φ) :
    Laplacian.laplacian φ z = 0 := by
  have hev : ∀ w : ℂ, (fun x => fderiv ℝ φ x w) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    intro w
    filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hz] with x hx
    rw [s07c_fkps_m3a_fderiv_zero φ x hx, ContinuousLinearMap.zero_apply]
  rw [s07c_fkps_m3b_lap φ hφ, (hev 1).fderiv_eq, (hev I).fderiv_eq]
  simp

/-- For `φ ∈ C²` with compact support, `Δφ` is continuous and bounded. -/
theorem s07c_fkps_m3b_lap_cont (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    Continuous (Laplacian.laplacian φ) ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |Laplacian.laplacian φ x| ≤ M := by
  have e : Laplacian.laplacian φ = fun z =>
      fderiv ℝ (fun x => fderiv ℝ φ x 1) z 1 + fderiv ℝ (fun x => fderiv ℝ φ x I) z I :=
    funext (s07c_fkps_m3b_lap φ hφ)
  have hC : Continuous (Laplacian.laplacian φ) := by
    rw [e]
    exact (((s07c_fkps_m3b_contDiff_apply φ hφ 1).continuous_fderiv (by simp)).clm_apply
      continuous_const).add (((s07c_fkps_m3b_contDiff_apply φ hφ I).continuous_fderiv (by simp)).clm_apply
      continuous_const)
  refine ⟨hC, ?_⟩
  obtain ⟨M, hM⟩ := hC.bounded_above_of_compact_support (hc.laplacian)
  exact ⟨max M 0, le_max_right _ _, fun x => (Real.norm_eq_abs _ ▸ hM x).trans (le_max_left _ _)⟩

/-- For `Y ∈ 𝔻`, `X ↦ |X - Y|⁻¹` is integrable on `𝔻`. -/
theorem s07c_fkps_m3b_inv_integrable (Y : ℂ) (hY : Y ∈ unitDisc) :
    IntegrableOn (fun X : ℂ => ‖X - Y‖⁻¹) unitDisc := by
  refine ⟨(Measurable.inv (measurable_id.sub_const Y).norm).aestronglyMeasurable, ?_⟩
  show ∫⁻ X in unitDisc, ‖‖X - Y‖⁻¹‖ₑ < ⊤
  have heq : ∀ X : ℂ, ‖‖X - Y‖⁻¹‖ₑ = ENNReal.ofReal ‖X - Y‖⁻¹ := fun X =>
    Real.enorm_of_nonneg (inv_nonneg.2 (norm_nonneg _))
  simp only [heq]
  exact (s07c_fkps_m3b_inv_disc Y hY).trans_lt ENNReal.ofReal_lt_top

/-- The Green kernel of `𝔻` split into its Cauchy part and its holomorphic part. -/
theorem s07c_fkps_m3b_kernel_split (X Y : ℂ) (hX : X ∈ unitDisc) (hY : Y ∈ unitDisc) (hne : X ≠ Y) :
    ((1 - ‖X‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (X - Y) * (1 - X * conj Y)) =
      (2 * π : ℂ)⁻¹ * (1 / conj (X - Y) - X / (1 - X * conj Y)) := by
  have hXn : ‖X‖ < 1 := mem_ball_zero_iff.1 hX
  have hYn : ‖Y‖ < 1 := mem_ball_zero_iff.1 hY
  have h1 : conj (X - Y) ≠ 0 := by
    rw [map_ne_zero]
    exact sub_ne_zero.2 hne
  have h2 : (1 : ℂ) - X * conj Y ≠ 0 := by
    intro h
    have h' : X * conj Y = 1 := by linear_combination -h
    have hn : ‖X * conj Y‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      nlinarith [norm_nonneg X, norm_nonneg Y]
    rw [h', norm_one] at hn
    exact lt_irrefl _ hn
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hX2 : ((1 - ‖X‖ ^ 2 : ℝ) : ℂ) = 1 - X * conj X := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [hX2]
  rw [map_sub] at h1 ⊢
  field_simp
  ring

/-- Part B (harmonic part): `∫_𝔻 Δφ(X) · X/(1 - X Ȳ) dX = 0` for a test function `φ` on `𝔻` and `Y ∈ 𝔻`. -/
theorem s07c_fkps_m3b_greenB (Ω : TopologicalSpace.Opens ℂ) (hΩ : (Ω : Set ℂ) = unitDisc)
    (φ : TestFunction Ω ℝ ⊤) (Y : ℂ) (hY : Y ∈ unitDisc) :
    ∫ X in unitDisc, (Laplacian.laplacian (φ : ℂ → ℝ) X : ℂ) * (X / (1 - X * conj Y)) = 0 := by
  have hYn : ‖Y‖ < 1 := mem_ball_zero_iff.1 hY
  have hφ2 : ContDiff ℝ 2 (φ : ℂ → ℝ) := φ.contDiff.of_le (by simp)
  have hh : InnerProductSpace.HarmonicOnNhd (fun X : ℂ => X / (1 - X * conj Y)) Ω := by
    intro x hx
    rw [hΩ] at hx
    have hxn : ‖x‖ < 1 := mem_ball_zero_iff.1 hx
    have hden : (1 : ℂ) - x * conj Y ≠ 0 := by
      intro h
      have h' : x * conj Y = 1 := by linear_combination -h
      have hn : ‖x * conj Y‖ < 1 := by
        rw [norm_mul, Complex.norm_conj]
        nlinarith [norm_nonneg x, norm_nonneg Y]
      rw [h', norm_one] at hn
      exact lt_irrefl _ hn
    exact (analyticAt_id.div (analyticAt_const.sub (analyticAt_id.mul analyticAt_const)) hden).harmonicAt
  have h0 := hh.integral_laplacian_smul_eq_zero (μ := volume) φ
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [← h0]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    simp only [Complex.real_smul]
  · intro X hX
    have hX' : X ∉ tsupport (φ : ℂ → ℝ) := by
      intro h
      have h2 : X ∈ (Ω : Set ℂ) := φ.tsupport_subset h
      rw [hΩ] at h2
      exact hX h2
    rw [s07c_fkps_m3b_lap_zero _ hφ2 X hX', Complex.ofReal_zero, zero_mul]

/-- **Green kernel identity.** For a test function `φ` on `𝔻` and `Y ∈ 𝔻`,
`∫_𝔻 Δφ(X) ∇_Y G₀(X, Y) dX = -∇φ(Y)`. -/
theorem s07c_fkps_m3b_green_kernel (Ω : TopologicalSpace.Opens ℂ) (hΩ : (Ω : Set ℂ) = unitDisc)
    (φ : TestFunction Ω ℝ ⊤) (Y : ℂ) (hY : Y ∈ unitDisc) :
    ∫ X in unitDisc, (Laplacian.laplacian (φ : ℂ → ℝ) X : ℂ) *
        (((1 - ‖X‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (X - Y) * (1 - X * conj Y))) =
      -((fderiv ℝ (φ : ℂ → ℝ) Y 1 : ℂ) + (fderiv ℝ (φ : ℂ → ℝ) Y I : ℂ) * I) := by
  have hYn : ‖Y‖ < 1 := mem_ball_zero_iff.1 hY
  have hφ2 : ContDiff ℝ 2 (φ : ℂ → ℝ) := φ.contDiff.of_le (by simp)
  have hs : tsupport (φ : ℂ → ℝ) ⊆ unitDisc := by rw [← hΩ]; exact φ.tsupport_subset
  obtain ⟨hLc, M, hM0, hM⟩ := s07c_fkps_m3b_lap_cont _ hφ2 φ.hasCompactSupport
  set L : ℂ → ℝ := Laplacian.laplacian (φ : ℂ → ℝ) with hLdef
  have hfin : volume unitDisc ≠ ⊤ := measure_ball_lt_top.ne
  -- integrability of the two parts
  have hA : IntegrableOn (fun X => (L X : ℂ) / conj (X - Y)) unitDisc := by
    refine Integrable.mono' ((s07c_fkps_m3b_inv_integrable Y hY).const_mul M) ?_ ?_
    · exact ((Complex.continuous_ofReal.comp hLc).measurable.div
        (Complex.continuous_conj.measurable.comp (measurable_id.sub_const Y))).aestronglyMeasurable
    · refine Eventually.of_forall fun X => ?_
      rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hM X) (inv_nonneg.2 (norm_nonneg _))
  have hB : IntegrableOn (fun X => (L X : ℂ) * (X / (1 - X * conj Y))) unitDisc := by
    refine Measure.integrableOn_of_bounded (M := M * (1 - ‖Y‖)⁻¹) hfin ?_ ?_
    · exact ((Complex.continuous_ofReal.comp hLc).measurable.mul
        (measurable_id.div (measurable_const.sub (measurable_id.mul measurable_const)))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_ball] with X hX
      have hXn : ‖X‖ < 1 := mem_ball_zero_iff.1 hX
      have hlow : 1 - ‖Y‖ ≤ ‖1 - X * conj Y‖ := by
        have h1 := norm_sub_norm_le (1 : ℂ) (X * conj Y)
        rw [norm_one, norm_mul, Complex.norm_conj] at h1
        nlinarith [norm_nonneg X, norm_nonneg Y]
      have hpos : 0 < 1 - ‖Y‖ := by linarith
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul (hM X) ?_ (by positivity) hM0
      rw [div_le_iff₀ (hpos.trans_le hlow)]
      calc ‖X‖ ≤ 1 := hXn.le
        _ = (1 - ‖Y‖)⁻¹ * (1 - ‖Y‖) := (inv_mul_cancel₀ hpos.ne').symm
        _ ≤ (1 - ‖Y‖)⁻¹ * ‖1 - X * conj Y‖ := by gcongr
  have hneY : ∀ᵐ X ∂(volume : Measure ℂ), X ≠ Y := by
    rw [ae_iff]
    simp
  have hsplit : ∀ᵐ X ∂(volume.restrict unitDisc), (L X : ℂ) *
      (((1 - ‖X‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (X - Y) * (1 - X * conj Y))) =
      (2 * π : ℂ)⁻¹ * ((L X : ℂ) / conj (X - Y) - (L X : ℂ) * (X / (1 - X * conj Y))) := by
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hneY] with X hX hXY
    rw [s07c_fkps_m3b_kernel_split X Y hX hY hXY]
    ring
  rw [integral_congr_ae hsplit, integral_const_mul, integral_sub hA hB,
    s07c_fkps_m3b_greenA _ hφ2 hs Y hY, s07c_fkps_m3b_greenB Ω hΩ φ Y hY]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  ring

/-- Joint measurability of the Green kernel gradient. -/
theorem s07c_fkps_m3b_kernel_meas : Measurable (fun p : ℂ × ℂ =>
    ((1 - ‖p.1‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (p.1 - p.2) * (1 - p.1 * conj p.2))) :=
  (Complex.measurable_ofReal.comp (measurable_const.sub (measurable_fst.norm.pow_const 2))).div
    ((measurable_const.mul (Complex.continuous_conj.measurable.comp (measurable_fst.sub measurable_snd))).mul
      (measurable_const.sub (measurable_fst.mul (Complex.continuous_conj.measurable.comp measurable_snd))))

/-- For `X, Y ∈ 𝔻` (also `X = Y`, where the kernel is `0` by junk): `|K(X, Y)| ≤ π⁻¹ |X - Y|⁻¹`. -/
theorem s07c_fkps_m3b_kernel_le' (X Y : ℂ) (hX : X ∈ unitDisc) (hY : Y ∈ unitDisc) :
    ‖((1 - ‖X‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (X - Y) * (1 - X * conj Y))‖ ≤ π⁻¹ * ‖X - Y‖⁻¹ := by
  by_cases h : Y = X
  · subst h
    simp
  · rw [← mul_inv]
    exact s07c_fkps_m3b_kernel_le X Y hX hY h

/-- `L²` implies `L¹` on a set of finite measure (lintegral form). -/
theorem s07c_fkps_m3b_l1_of_l2 (V : ℂ → ℂ) (s : Set ℂ) (hs : volume s ≠ ⊤)
    (h : ∫⁻ z in s, ‖V z‖ₑ ^ 2 < ⊤) : ∫⁻ z in s, ‖V z‖ₑ < ⊤ := by
  have hpt : ∀ z, ‖V z‖ₑ ≤ 1 + ‖V z‖ₑ ^ 2 := by
    intro z
    by_cases h1 : ‖V z‖ₑ ≤ 1
    · exact le_add_right h1
    · push_neg at h1
      refine le_add_left ?_
      calc ‖V z‖ₑ = ‖V z‖ₑ * 1 := (mul_one _).symm
        _ ≤ ‖V z‖ₑ * ‖V z‖ₑ := mul_le_mul_of_nonneg_left h1.le zero_le
        _ = ‖V z‖ₑ ^ 2 := (sq _).symm
  calc ∫⁻ z in s, ‖V z‖ₑ ≤ ∫⁻ z in s, (1 + ‖V z‖ₑ ^ 2) := lintegral_mono hpt
    _ = volume s + ∫⁻ z in s, ‖V z‖ₑ ^ 2 := by
        rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hs.lt_top, h⟩

/-- Tonelli bound: `∫_𝔻 ∫_𝔻 |K(X, Y)| |V(Y)| dY dX < ∞` for `V ∈ L²(𝔻)`. -/
theorem s07c_fkps_m3b_tonelli (V : ℂ → ℂ) (hV : Measurable V) (hV2 : ∫⁻ z in unitDisc, ‖V z‖ₑ ^ 2 < ⊤) :
    ∫⁻ X in unitDisc, ∫⁻ Y in unitDisc,
      ‖((1 - ‖X‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (X - Y) * (1 - X * conj Y))‖ₑ * ‖V Y‖ₑ < ⊤ := by
  have hm : Measurable (fun p : ℂ × ℂ =>
      ‖((1 - ‖p.1‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (p.1 - p.2) * (1 - p.1 * conj p.2))‖ₑ * ‖V p.2‖ₑ) :=
    s07c_fkps_m3b_kernel_meas.enorm.mul (hV.comp measurable_snd).enorm
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have hin : ∀ Y ∈ unitDisc, ∫⁻ X in unitDisc,
      ‖((1 - ‖X‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (X - Y) * (1 - X * conj Y))‖ₑ ≤ ENNReal.ofReal 4 := by
    intro Y hY
    calc ∫⁻ X in unitDisc, ‖((1 - ‖X‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (X - Y) * (1 - X * conj Y))‖ₑ
        ≤ ∫⁻ X in unitDisc, ENNReal.ofReal π⁻¹ * ENNReal.ofReal ‖X - Y‖⁻¹ := by
          refine setLIntegral_mono' measurableSet_ball (fun X hX => ?_)
          rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (inv_nonneg.2 Real.pi_pos.le)]
          exact ENNReal.ofReal_le_ofReal (s07c_fkps_m3b_kernel_le' X Y hX hY)
      _ = ENNReal.ofReal π⁻¹ * ∫⁻ X in unitDisc, ENNReal.ofReal ‖X - Y‖⁻¹ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal π⁻¹ * ENNReal.ofReal (4 * π) := by
          gcongr
          exact s07c_fkps_m3b_inv_disc Y hY
      _ = ENNReal.ofReal 4 := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 Real.pi_pos.le)]
          congr 1
          field_simp
  calc ∫⁻ Y in unitDisc, ∫⁻ X in unitDisc,
        ‖((1 - ‖X‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (X - Y) * (1 - X * conj Y))‖ₑ * ‖V Y‖ₑ
      = ∫⁻ Y in unitDisc, (∫⁻ X in unitDisc,
          ‖((1 - ‖X‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (X - Y) * (1 - X * conj Y))‖ₑ) * ‖V Y‖ₑ := by
        refine lintegral_congr fun Y => ?_
        exact lintegral_mul_const _ ((s07c_fkps_m3b_kernel_meas.comp
          (measurable_id.prodMk measurable_const)).enorm)
    _ ≤ ∫⁻ Y in unitDisc, ENNReal.ofReal 4 * ‖V Y‖ₑ :=
        setLIntegral_mono' measurableSet_ball (fun Y hY => mul_le_mul_of_nonneg_right (hin Y hY) zero_le)
    _ = ENNReal.ofReal 4 * ∫⁻ Y in unitDisc, ‖V Y‖ₑ := lintegral_const_mul _ hV.enorm
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (s07c_fkps_m3b_l1_of_l2 V unitDisc measure_ball_lt_top.ne hV2)

/-- Pointwise: `|Re(conj K · V)|ₑ ≤ |K|ₑ |V|ₑ`. -/
theorem s07c_fkps_m3b_re_le (k v : ℂ) : ‖(conj k * v).re‖ₑ ≤ ‖k‖ₑ * ‖v‖ₑ := by
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
    ← ENNReal.ofReal_mul (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖(conj k * v).re‖ = |(conj k * v).re| := Real.norm_eq_abs _
    _ ≤ ‖conj k * v‖ := Complex.abs_re_le_norm _
    _ = ‖k‖ * ‖v‖ := by rw [norm_mul, Complex.norm_conj]

/-- For a.e. `X ∈ 𝔻`, `Y ↦ Re(conj K(X, Y) · V(Y))` is integrable on `𝔻`. -/
theorem s07c_fkps_m3b_ae_integrable (V : ℂ → ℂ) (hV : Measurable V)
    (hV2 : ∫⁻ z in unitDisc, ‖V z‖ₑ ^ 2 < ⊤) :
    ∀ᵐ X, X ∈ unitDisc →
      IntegrableOn (fun Y => (conj (((1 - ‖X‖ ^ 2 : ℝ) : ℂ) /
        (2 * π * conj (X - Y) * (1 - X * conj Y))) * V Y).re) unitDisc := by
  have hm : Measurable (fun p : ℂ × ℂ =>
      ‖((1 - ‖p.1‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (p.1 - p.2) * (1 - p.1 * conj p.2))‖ₑ * ‖V p.2‖ₑ) :=
    s07c_fkps_m3b_kernel_meas.enorm.mul (hV.comp measurable_snd).enorm
  have hX : Measurable (fun X => ∫⁻ Y in unitDisc,
      ‖((1 - ‖X‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (X - Y) * (1 - X * conj Y))‖ₑ * ‖V Y‖ₑ) :=
    hm.lintegral_prod_right'
  have hae := ae_lt_top hX (s07c_fkps_m3b_tonelli V hV hV2).ne
  refine (ae_restrict_iff' measurableSet_ball).1 ?_
  filter_upwards [hae] with X hXf
  refine ⟨(Complex.measurable_re.comp ((Complex.continuous_conj.measurable.comp
    (s07c_fkps_m3b_kernel_meas.comp (measurable_const.prodMk measurable_id))).mul hV)).aestronglyMeasurable, ?_⟩
  show ∫⁻ Y in unitDisc, ‖(conj (((1 - ‖X‖ ^ 2 : ℝ) : ℂ) /
      (2 * π * conj (X - Y) * (1 - X * conj Y))) * V Y).re‖ₑ < ⊤
  exact (lintegral_mono fun Y => s07c_fkps_m3b_re_le _ _).trans_lt hXf

/-- The potential `W(X) = ∫_𝔻 Re(conj K(X, Y) · V(Y)) dY` is integrable on `𝔻`. -/
theorem s07c_fkps_m3b_W_integrable (V : ℂ → ℂ) (hV : Measurable V)
    (hV2 : ∫⁻ z in unitDisc, ‖V z‖ₑ ^ 2 < ⊤) :
    IntegrableOn (fun X => ∫ Y in unitDisc, (conj (((1 - ‖X‖ ^ 2 : ℝ) : ℂ) /
        (2 * π * conj (X - Y) * (1 - X * conj Y))) * V Y).re) unitDisc := by
  have hsm : StronglyMeasurable (Function.uncurry fun X Y => (conj (((1 - ‖X‖ ^ 2 : ℝ) : ℂ) /
      (2 * π * conj (X - Y) * (1 - X * conj Y))) * V Y).re) :=
    (Complex.measurable_re.comp ((Complex.continuous_conj.measurable.comp
      s07c_fkps_m3b_kernel_meas).mul (hV.comp measurable_snd))).stronglyMeasurable
  refine ⟨(hsm.integral_prod_right (ν := volume.restrict unitDisc)).aestronglyMeasurable, ?_⟩
  show ∫⁻ X in unitDisc, ‖∫ Y in unitDisc, (conj (((1 - ‖X‖ ^ 2 : ℝ) : ℂ) /
      (2 * π * conj (X - Y) * (1 - X * conj Y))) * V Y).re‖ₑ < ⊤
  refine lt_of_le_of_lt ?_ (s07c_fkps_m3b_tonelli V hV hV2)
  refine lintegral_mono fun X => ?_
  exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun Y => s07c_fkps_m3b_re_le _ _)

/-- `u · a` is integrable for `u` continuous on `𝔻̄` and continuous `a` vanishing off `𝔻` (complex form). -/
theorem s07c_fkps_m3b_int_u (u : ℂ → ℝ) (hu : ContinuousOn u (closedBall 0 1)) (a : ℂ → ℂ)
    (ha : Continuous a) (h0 : ∀ z, z ∉ unitDisc → a z = 0) :
    Integrable (fun z => (u z : ℂ) * a z) := by
  refine (integrableOn_iff_integrable_of_support_subset (s := closedBall (0 : ℂ) 1) ?_).1 ?_
  · intro z hz
    by_contra hc
    apply hz
    have h1 : z ∉ unitDisc := fun h => hc (ball_subset_closedBall h)
    simp [h0 z h1]
  · exact ((continuous_ofReal.comp_continuousOn hu).mul ha.continuousOn).integrableOn_compact
      (isCompact_closedBall 0 1)

/-- `a · u` is integrable for `u` continuous on `𝔻̄` and continuous `a` vanishing off `𝔻` (real form). -/
theorem s07c_fkps_m3b_int_u_re (u : ℂ → ℝ) (hu : ContinuousOn u (closedBall 0 1)) (a : ℂ → ℝ)
    (ha : Continuous a) (h0 : ∀ z, z ∉ unitDisc → a z = 0) :
    Integrable (fun z => a z * u z) := by
  refine (integrableOn_iff_integrable_of_support_subset (s := closedBall (0 : ℂ) 1) ?_).1 ?_
  · intro z hz
    by_contra hc
    apply hz
    have h1 : z ∉ unitDisc := fun h => hc (ball_subset_closedBall h)
    simp [h0 z h1]
  · exact (ha.continuousOn.mul hu).integrableOn_compact (isCompact_closedBall 0 1)

/-- `a · g` is integrable for continuous `a` vanishing off `𝔻` and `g ∈ L²(𝔻)`. -/
theorem s07c_fkps_m3b_int_g (a : ℂ → ℂ) (ha : Continuous a) (h0 : ∀ z, z ∉ unitDisc → a z = 0)
    (g : ℂ → ℂ) (hg : AEMeasurable g) (hg2 : ∫⁻ z in unitDisc, ‖g z‖ₑ ^ 2 < ⊤) :
    Integrable (fun z => a z * g z) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn ha.continuousOn
  have hgi : IntegrableOn g unitDisc :=
    ⟨hg.aestronglyMeasurable.restrict, s07c_fkps_m3b_l1_of_l2 g unitDisc measure_ball_lt_top.ne hg2⟩
  have h1 : IntegrableOn (fun z => a z * g z) unitDisc := by
    refine Integrable.bdd_mul (c := C) hgi ha.aestronglyMeasurable ?_
    exact (ae_restrict_iff' measurableSet_ball).2
      (Eventually.of_forall fun z hz => hC z (ball_subset_closedBall hz))
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 h1
  intro z hz
  by_contra hc
  apply hz
  simp [h0 z hc]

/-- Real and imaginary parts of the weak-gradient identity (P2), tested with a `C¹` function `ψ`. -/
theorem s07c_fkps_m3b_P2_parts (u : ℂ → ℝ) (g : ℂ → ℂ) (hu : ContinuousOn u (closedBall 0 1))
    (hg : AEMeasurable g) (hg2 : ∫⁻ z in unitDisc, ‖g z‖ₑ ^ 2 < ⊤)
    (hP2 : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
      ∫ z, (u z : ℂ) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I) =
        -∫ z, (φ z : ℂ) * g z)
    (ψ : ℂ → ℝ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (ht : tsupport ψ ⊆ unitDisc) :
    ∫ z, fderiv ℝ ψ z 1 * u z = -∫ z, ψ z * (g z).re ∧
      ∫ z, fderiv ℝ ψ z I * u z = -∫ z, ψ z * (g z).im := by
  have hcd : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by simp)
  have hz0 : ∀ z, z ∉ unitDisc → fderiv ℝ ψ z = 0 := fun z hz =>
    s07c_fkps_m3a_fderiv_zero ψ z (fun h => hz (ht h))
  have hψ0 : ∀ z, z ∉ unitDisc → ψ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (fun h => hz (ht h))
  have hL : Integrable (fun z => (u z : ℂ) *
      (((fderiv ℝ ψ z 1 : ℝ) : ℂ) + ((fderiv ℝ ψ z I : ℝ) : ℂ) * I)) :=
    s07c_fkps_m3b_int_u u hu (fun z => ((fderiv ℝ ψ z 1 : ℝ) : ℂ) + ((fderiv ℝ ψ z I : ℝ) : ℂ) * I)
      ((continuous_ofReal.comp (hcd.clm_apply continuous_const)).add
        ((continuous_ofReal.comp (hcd.clm_apply continuous_const)).mul continuous_const))
      (fun z hz => by simp [hz0 z hz])
  have hR : Integrable (fun z => (ψ z : ℂ) * g z) :=
    s07c_fkps_m3b_int_g (fun z => (ψ z : ℂ)) (continuous_ofReal.comp hψ.continuous)
      (fun z hz => by simp [hψ0 z hz]) g hg hg2
  have h := hP2 ψ hψ hc ht
  have eLr := integral_re hL
  have eRr := integral_re hR
  have eLi := integral_im hL
  have eRi := integral_im hR
  simp only [RCLike.re_to_complex, RCLike.im_to_complex] at eLr eRr eLi eRi
  constructor
  · have h1 := congrArg Complex.re h
    rw [Complex.neg_re, ← eLr, ← eRr] at h1
    have e1 : ∀ z, ((u z : ℂ) * (((fderiv ℝ ψ z 1 : ℝ) : ℂ) + ((fderiv ℝ ψ z I : ℝ) : ℂ) * I)).re =
        fderiv ℝ ψ z 1 * u z := by
      intro z
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    have e2 : ∀ z, ((ψ z : ℂ) * g z).re = ψ z * (g z).re := by
      intro z
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    simp only [e1, e2] at h1
    exact h1
  · have h1 := congrArg Complex.im h
    rw [Complex.neg_im, ← eLi, ← eRi] at h1
    have e1 : ∀ z, ((u z : ℂ) * (((fderiv ℝ ψ z 1 : ℝ) : ℂ) + ((fderiv ℝ ψ z I : ℝ) : ℂ) * I)).im =
        fderiv ℝ ψ z I * u z := by
      intro z
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    have e2 : ∀ z, ((ψ z : ℂ) * g z).im = ψ z * (g z).im := by
      intro z
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    simp only [e1, e2] at h1
    exact h1

/-- The `u`-part of the weak Laplacian: `∫ Δφ · u = ∫ ⟨V, ∇φ⟩` (from (P2) twice and (P4)). -/
theorem s07c_fkps_m3b_u_part (u : ℂ → ℝ) (g V : ℂ → ℂ) (hu : ContinuousOn u (closedBall 0 1))
    (hg : AEMeasurable g) (hg2 : ∫⁻ z in unitDisc, ‖g z‖ₑ ^ 2 < ⊤)
    (hP2 : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
      ∫ z, (u z : ℂ) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I) =
        -∫ z, (φ z : ℂ) * g z)
    (hP4 : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
      ∫ z, (conj (g z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re =
        -∫ z, (conj (V z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re)
    (Ω : TopologicalSpace.Opens ℂ) (hΩ : (Ω : Set ℂ) = unitDisc) (φ : TestFunction Ω ℝ ⊤) :
    ∫ x, Laplacian.laplacian (φ : ℂ → ℝ) x * u x =
      ∫ z, (conj (V z) * (((fderiv ℝ (φ : ℂ → ℝ) z 1 : ℝ) : ℂ) +
        ((fderiv ℝ (φ : ℂ → ℝ) z I : ℝ) : ℂ) * I)).re := by
  have hφ2 : ContDiff ℝ 2 (φ : ℂ → ℝ) := φ.contDiff.of_le (by simp)
  have hφ1 : ContDiff ℝ 1 (φ : ℂ → ℝ) := φ.contDiff.of_le (by simp)
  have ht : tsupport (φ : ℂ → ℝ) ⊆ unitDisc := by rw [← hΩ]; exact φ.tsupport_subset
  have hc : HasCompactSupport (φ : ℂ → ℝ) := φ.hasCompactSupport
  have hcd : Continuous (fderiv ℝ (φ : ℂ → ℝ)) := hφ1.continuous_fderiv (by simp)
  have hz0 : ∀ z, z ∉ unitDisc → fderiv ℝ (φ : ℂ → ℝ) z = 0 := fun z hz =>
    s07c_fkps_m3a_fderiv_zero _ z (fun h => hz (ht h))
  have hD1 := s07c_fkps_m3b_contDiff_apply _ hφ2 1
  have hD2 := s07c_fkps_m3b_contDiff_apply _ hφ2 I
  have ht1 : tsupport (fun x => fderiv ℝ (φ : ℂ → ℝ) x 1) ⊆ unitDisc :=
    (tsupport_fderiv_apply_subset ℝ 1).trans ht
  have ht2 : tsupport (fun x => fderiv ℝ (φ : ℂ → ℝ) x I) ⊆ unitDisc :=
    (tsupport_fderiv_apply_subset ℝ I).trans ht
  have p1 : ∫ z, fderiv ℝ (fun x => fderiv ℝ (φ : ℂ → ℝ) x 1) z 1 * u z =
      -∫ z, fderiv ℝ (φ : ℂ → ℝ) z 1 * (g z).re :=
    (s07c_fkps_m3b_P2_parts u g hu hg hg2 hP2 _ hD1 (hc.fderiv_apply (𝕜 := ℝ) 1) ht1).1
  have p2 : ∫ z, fderiv ℝ (fun x => fderiv ℝ (φ : ℂ → ℝ) x I) z I * u z =
      -∫ z, fderiv ℝ (φ : ℂ → ℝ) z I * (g z).im :=
    (s07c_fkps_m3b_P2_parts u g hu hg hg2 hP2 _ hD2 (hc.fderiv_apply (𝕜 := ℝ) I) ht2).2
  have hi1 : Integrable (fun z => fderiv ℝ (fun x => fderiv ℝ (φ : ℂ → ℝ) x 1) z 1 * u z) :=
    s07c_fkps_m3b_int_u_re u hu (fun z => fderiv ℝ (fun x => fderiv ℝ (φ : ℂ → ℝ) x 1) z 1)
      ((hD1.continuous_fderiv (by simp)).clm_apply continuous_const)
      (fun z hz => by rw [s07c_fkps_m3a_fderiv_zero _ z (fun h => hz (ht1 h))]; rfl)
  have hi2 : Integrable (fun z => fderiv ℝ (fun x => fderiv ℝ (φ : ℂ → ℝ) x I) z I * u z) :=
    s07c_fkps_m3b_int_u_re u hu (fun z => fderiv ℝ (fun x => fderiv ℝ (φ : ℂ → ℝ) x I) z I)
      ((hD2.continuous_fderiv (by simp)).clm_apply continuous_const)
      (fun z hz => by rw [s07c_fkps_m3a_fderiv_zero _ z (fun h => hz (ht2 h))]; rfl)
  have hg1 : Integrable (fun z => fderiv ℝ (φ : ℂ → ℝ) z 1 * (g z).re) := by
    have h1 := (s07c_fkps_m3b_int_g (fun z => ((fderiv ℝ (φ : ℂ → ℝ) z 1 : ℝ) : ℂ))
      (continuous_ofReal.comp (hcd.clm_apply continuous_const)) (fun z hz => by simp [hz0 z hz])
      g hg hg2).re
    refine h1.congr (Eventually.of_forall fun z => ?_)
    simp
  have hg2' : Integrable (fun z => fderiv ℝ (φ : ℂ → ℝ) z I * (g z).im) := by
    have h1 := (s07c_fkps_m3b_int_g (fun z => ((fderiv ℝ (φ : ℂ → ℝ) z I : ℝ) : ℂ))
      (continuous_ofReal.comp (hcd.clm_apply continuous_const)) (fun z hz => by simp [hz0 z hz])
      g hg hg2).im
    refine h1.congr (Eventually.of_forall fun z => ?_)
    simp
  have hlap : ∀ x, Laplacian.laplacian (φ : ℂ → ℝ) x * u x =
      fderiv ℝ (fun x => fderiv ℝ (φ : ℂ → ℝ) x 1) x 1 * u x +
        fderiv ℝ (fun x => fderiv ℝ (φ : ℂ → ℝ) x I) x I * u x := by
    intro x
    rw [s07c_fkps_m3b_lap _ hφ2 x, add_mul]
  have hsum : ∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 * (g z).re + fderiv ℝ (φ : ℂ → ℝ) z I * (g z).im) =
      ∫ z, (conj (g z) * (((fderiv ℝ (φ : ℂ → ℝ) z 1 : ℝ) : ℂ) +
        ((fderiv ℝ (φ : ℂ → ℝ) z I : ℝ) : ℂ) * I)).re := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
    ring
  have hP := hP4 (φ : ℂ → ℝ) hφ1 hc ht
  simp only [hlap]
  rw [integral_add hi1 hi2, p1, p2, ← neg_add, ← integral_add hg1 hg2', hsum, hP, neg_neg]

/-- The potential part of the weak Laplacian: for measurable `V ∈ L²(𝔻)`,
`∫ Δφ(X) W(X) dX = -∫ ⟨V, ∇φ⟩` where `W(X) = ∫_𝔻 ⟨K(X, Y), V(Y)⟩ dY` (Fubini + the Green kernel identity). -/
theorem s07c_fkps_m3b_W_part (V : ℂ → ℂ) (hV : Measurable V) (hV2 : ∫⁻ z in unitDisc, ‖V z‖ₑ ^ 2 < ⊤)
    (Ω : TopologicalSpace.Opens ℂ) (hΩ : (Ω : Set ℂ) = unitDisc) (φ : TestFunction Ω ℝ ⊤) :
    ∫ x, Laplacian.laplacian (φ : ℂ → ℝ) x * ∫ Y in unitDisc, (conj (((1 - ‖x‖ ^ 2 : ℝ) : ℂ) /
        (2 * π * conj (x - Y) * (1 - x * conj Y))) * V Y).re =
      -∫ z, (conj (V z) * (((fderiv ℝ (φ : ℂ → ℝ) z 1 : ℝ) : ℂ) +
        ((fderiv ℝ (φ : ℂ → ℝ) z I : ℝ) : ℂ) * I)).re := by
  have hφ2 : ContDiff ℝ 2 (φ : ℂ → ℝ) := φ.contDiff.of_le (by simp)
  have ht : tsupport (φ : ℂ → ℝ) ⊆ unitDisc := by rw [← hΩ]; exact φ.tsupport_subset
  have hc : HasCompactSupport (φ : ℂ → ℝ) := φ.hasCompactSupport
  obtain ⟨hcont, M, hM0, hM⟩ := s07c_fkps_m3b_lap_cont _ hφ2 hc
  have hz0 : ∀ x, x ∉ unitDisc → Laplacian.laplacian (φ : ℂ → ℝ) x = 0 := fun x hx =>
    s07c_fkps_m3b_lap_zero _ hφ2 x (fun h => hx (ht h))
  have hfz : ∀ z, z ∉ unitDisc → fderiv ℝ (φ : ℂ → ℝ) z = 0 := fun z hz =>
    s07c_fkps_m3a_fderiv_zero _ z (fun h => hz (ht h))
  have e1 : ∫ x, Laplacian.laplacian (φ : ℂ → ℝ) x * ∫ Y in unitDisc, (conj (((1 - ‖x‖ ^ 2 : ℝ) : ℂ) /
        (2 * π * conj (x - Y) * (1 - x * conj Y))) * V Y).re =
      ∫ x in unitDisc, ∫ Y in unitDisc, Laplacian.laplacian (φ : ℂ → ℝ) x *
        (conj (((1 - ‖x‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (x - Y) * (1 - x * conj Y))) * V Y).re := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := unitDisc)
      (fun x hx => by rw [hz0 x hx, zero_mul])]
    refine setIntegral_congr_fun measurableSet_ball (fun x _ => ?_)
    exact (integral_const_mul _ _).symm
  have hmeas : Measurable (Function.uncurry fun x Y => Laplacian.laplacian (φ : ℂ → ℝ) x *
      (conj (((1 - ‖x‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (x - Y) * (1 - x * conj Y))) * V Y).re) :=
    (hcont.measurable.comp measurable_fst).mul (Complex.measurable_re.comp
      ((Complex.continuous_conj.measurable.comp s07c_fkps_m3b_kernel_meas).mul (hV.comp measurable_snd)))
  have hint : Integrable (Function.uncurry fun x Y => Laplacian.laplacian (φ : ℂ → ℝ) x *
      (conj (((1 - ‖x‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (x - Y) * (1 - x * conj Y))) * V Y).re)
      ((volume.restrict unitDisc).prod (volume.restrict unitDisc)) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖Function.uncurry (fun x Y => Laplacian.laplacian (φ : ℂ → ℝ) x *
      (conj (((1 - ‖x‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (x - Y) * (1 - x * conj Y))) * V Y).re) p‖ₑ
        ∂((volume.restrict unitDisc).prod (volume.restrict unitDisc)) < ⊤
    rw [lintegral_prod _ hmeas.enorm.aemeasurable]
    calc ∫⁻ x in unitDisc, ∫⁻ Y in unitDisc, ‖Function.uncurry (fun x Y =>
          Laplacian.laplacian (φ : ℂ → ℝ) x * (conj (((1 - ‖x‖ ^ 2 : ℝ) : ℂ) /
            (2 * π * conj (x - Y) * (1 - x * conj Y))) * V Y).re) (x, Y)‖ₑ
        ≤ ∫⁻ x in unitDisc, ∫⁻ Y in unitDisc, ENNReal.ofReal M *
          (‖((1 - ‖x‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (x - Y) * (1 - x * conj Y))‖ₑ * ‖V Y‖ₑ) := by
          refine lintegral_mono fun x => lintegral_mono fun Y => ?_
          simp only [Function.uncurry_apply_pair]
          rw [enorm_mul]
          refine mul_le_mul' ?_ (s07c_fkps_m3b_re_le _ _)
          rw [← ofReal_norm_eq_enorm]
          exact ENNReal.ofReal_le_ofReal ((Real.norm_eq_abs _).trans_le (hM x))
      _ = ENNReal.ofReal M * ∫⁻ x in unitDisc, ∫⁻ Y in unitDisc,
          ‖((1 - ‖x‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (x - Y) * (1 - x * conj Y))‖ₑ * ‖V Y‖ₑ := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun x => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (s07c_fkps_m3b_tonelli V hV hV2)
  have hin : ∀ Y ∈ unitDisc, ∫ x in unitDisc, Laplacian.laplacian (φ : ℂ → ℝ) x *
      (conj (((1 - ‖x‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (x - Y) * (1 - x * conj Y))) * V Y).re =
      -(conj (V Y) * (((fderiv ℝ (φ : ℂ → ℝ) Y 1 : ℝ) : ℂ) +
        ((fderiv ℝ (φ : ℂ → ℝ) Y I : ℝ) : ℂ) * I)).re := by
    intro Y hY
    have hF : IntegrableOn (fun x => (Laplacian.laplacian (φ : ℂ → ℝ) x : ℂ) *
        (((1 - ‖x‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (x - Y) * (1 - x * conj Y)))) unitDisc := by
      refine Integrable.mono' ((s07c_fkps_m3b_inv_integrable Y hY).const_mul (M * π⁻¹)) ?_ ?_
      · exact ((continuous_ofReal.comp hcont).measurable.mul (s07c_fkps_m3b_kernel_meas.comp
          (measurable_id.prodMk measurable_const))).aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun x hx => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc |Laplacian.laplacian (φ : ℂ → ℝ) x| *
              ‖((1 - ‖x‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (x - Y) * (1 - x * conj Y))‖
            ≤ M * (π⁻¹ * ‖x - Y‖⁻¹) :=
              mul_le_mul (hM x) (s07c_fkps_m3b_kernel_le' x Y hx hY) (norm_nonneg _) hM0
          _ = M * π⁻¹ * ‖x - Y‖⁻¹ := by ring
    have hG := s07c_fkps_m3b_green_kernel Ω hΩ φ Y hY
    have e2 : ∀ x, Laplacian.laplacian (φ : ℂ → ℝ) x *
        (conj (((1 - ‖x‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (x - Y) * (1 - x * conj Y))) * V Y).re =
        ((Laplacian.laplacian (φ : ℂ → ℝ) x : ℂ) *
          (((1 - ‖x‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (x - Y) * (1 - x * conj Y))) * conj (V Y)).re := by
      intro x
      simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    simp only [e2]
    have eR := integral_re (hF.mul_const (conj (V Y)))
    simp only [RCLike.re_to_complex] at eR
    rw [eR, integral_mul_const, hG]
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re,
      Complex.conj_im]
    ring
  rw [e1, integral_integral_swap hint, setIntegral_congr_fun (s := unitDisc) measurableSet_ball (fun Y hY => hin Y hY),
    integral_neg]
  congr 1
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by simp [hfz z hz])

/-- `u + W` is weakly harmonic on `𝔻` (for measurable `V`). -/
theorem s07c_fkps_m3b_weak (u : ℂ → ℝ) (g V : ℂ → ℂ) (hu : ContinuousOn u (closedBall 0 1))
    (hg : AEMeasurable g) (hV : Measurable V)
    (hg2 : ∫⁻ z in unitDisc, ‖g z‖ₑ ^ 2 < ⊤) (hV2 : ∫⁻ z in unitDisc, ‖V z‖ₑ ^ 2 < ⊤)
    (hP2 : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
      ∫ z, (u z : ℂ) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I) =
        -∫ z, (φ z : ℂ) * g z)
    (hP4 : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
      ∫ z, (conj (g z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re =
        -∫ z, (conj (V z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re)
    (Ω : TopologicalSpace.Opens ℂ) (hΩ : (Ω : Set ℂ) = unitDisc) :
    TauCeti.WeaklyHarmonicOn volume Ω (fun X => u X + ∫ Y in unitDisc, (conj (((1 - ‖X‖ ^ 2 : ℝ) : ℂ) /
        (2 * π * conj (X - Y) * (1 - X * conj Y))) * V Y).re) := by
  have hWi := s07c_fkps_m3b_W_integrable V hV hV2
  have huloc : LocallyIntegrableOn u unitDisc :=
    (hu.mono ball_subset_closedBall).locallyIntegrableOn measurableSet_ball
  refine TauCeti.weaklyHarmonicOn_iff.2 ⟨?_, fun φ => ?_⟩
  · rw [hΩ]
    exact huloc.add hWi.locallyIntegrableOn
  · have hφ2 : ContDiff ℝ 2 (φ : ℂ → ℝ) := φ.contDiff.of_le (by simp)
    have ht : tsupport (φ : ℂ → ℝ) ⊆ unitDisc := by rw [← hΩ]; exact φ.tsupport_subset
    obtain ⟨hcont, M, hM0, hM⟩ := s07c_fkps_m3b_lap_cont _ hφ2 φ.hasCompactSupport
    have hz0 : ∀ x, x ∉ unitDisc → Laplacian.laplacian (φ : ℂ → ℝ) x = 0 := fun x hx =>
      s07c_fkps_m3b_lap_zero _ hφ2 x (fun h => hx (ht h))
    have hiu : Integrable (fun x => Laplacian.laplacian (φ : ℂ → ℝ) x * u x) :=
      s07c_fkps_m3b_int_u_re u hu _ hcont hz0
    have hiW : Integrable (fun x => Laplacian.laplacian (φ : ℂ → ℝ) x *
        ∫ Y in unitDisc, (conj (((1 - ‖x‖ ^ 2 : ℝ) : ℂ) /
          (2 * π * conj (x - Y) * (1 - x * conj Y))) * V Y).re) := by
      refine (integrableOn_iff_integrable_of_support_subset (s := unitDisc) ?_).1
        (Integrable.bdd_mul (c := M) hWi hcont.aestronglyMeasurable
          (Eventually.of_forall fun x => (Real.norm_eq_abs _).trans_le (hM x)))
      intro x hx
      by_contra hc
      apply hx
      simp [hz0 x hc]
    simp only [smul_eq_mul, mul_add]
    rw [integral_add hiu hiW, s07c_fkps_m3b_u_part u g V hu hg hg2 hP2 hP4 Ω hΩ φ,
      s07c_fkps_m3b_W_part V hV hV2 Ω hΩ φ, add_neg_cancel]

/-- A function continuous on `𝔻` and tending to `0` at every point of `𝕋` is uniformly small near `𝕋`. -/
theorem s07c_fkps_m3b_unif (D : ℂ → ℝ) (hD : ContinuousOn D unitDisc)
    (hb : ∀ ζ ∈ sphere (0 : ℂ) 1, Tendsto D (𝓝[unitDisc] ζ) (𝓝 0)) (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ Z ∈ unitDisc, 1 - ‖Z‖ < η → |D Z| < ε := by
  have hc : ContinuousOn (unitDisc.indicator D) (closedBall 0 1) := by
    intro x hx
    by_cases hx1 : x ∈ unitDisc
    · have hev : unitDisc.indicator D =ᶠ[𝓝 x] D :=
        eventually_of_mem (isOpen_ball.mem_nhds hx1) fun z hz => indicator_of_mem hz D
      exact ((hD.continuousAt (isOpen_ball.mem_nhds hx1)).congr hev.symm).continuousWithinAt
    · have hxs : x ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm]
        exact le_antisymm (mem_closedBall_zero_iff.1 hx) (not_lt.1 fun h => hx1 (mem_ball_zero_iff.2 h))
      rw [ContinuousWithinAt, indicator_of_notMem hx1, ← ball_union_sphere, nhdsWithin_union, tendsto_sup]
      constructor
      · exact (hb x hxs).congr' (eventually_nhdsWithin_of_forall fun z hz => (indicator_of_mem hz D).symm)
      · refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
        have hz' : z ∉ unitDisc := by
          intro h
          have h1 := mem_ball_zero_iff.1 h
          rw [mem_sphere_zero_iff_norm.1 hz] at h1
          exact lt_irrefl _ h1
        exact (indicator_of_notMem hz' D).symm
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous hc) ε hε
  refine ⟨min δ 1, lt_min hδ one_pos, fun Z hZ hZη => ?_⟩
  have hZ1 : ‖Z‖ < 1 := mem_ball_zero_iff.1 hZ
  have hm1 := min_le_right δ 1
  have hm2 := min_le_left δ 1
  have hn : 0 < ‖Z‖ := by linarith
  have hne : (‖Z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hn.ne'
  have hζ : ‖Z / (‖Z‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), div_self hn.ne']
  have hZeq : Z = (‖Z‖ : ℂ) * (Z / (‖Z‖ : ℂ)) := by field_simp
  have hdiff : Z - Z / (‖Z‖ : ℂ) = ((‖Z‖ - 1 : ℝ) : ℂ) * (Z / (‖Z‖ : ℂ)) := by
    calc Z - Z / (‖Z‖ : ℂ) = (‖Z‖ : ℂ) * (Z / (‖Z‖ : ℂ)) - Z / (‖Z‖ : ℂ) := by rw [← hZeq]
      _ = _ := by push_cast; ring
  have hdist : dist Z (Z / (‖Z‖ : ℂ)) < δ := by
    rw [dist_eq_norm, hdiff, norm_mul, hζ, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have h1 := hδ' Z (ball_subset_closedBall hZ) _ (mem_closedBall_zero_iff.2 hζ.le) hdist
  have hζD : Z / (‖Z‖ : ℂ) ∉ unitDisc := by
    intro h
    have h2 := mem_ball_zero_iff.1 h
    rw [hζ] at h2
    exact lt_irrefl _ h2
  rw [indicator_of_mem hZ, indicator_of_notMem hζD, Real.dist_eq, sub_zero] at h1
  exact h1

/-- Tail smallness: for `F` with finite integral on `𝔻`, `∫_{𝔻 \ B(0, 1-η)} F` is small for small `η`. -/
theorem s07c_fkps_m3b_tail (F : ℂ → ℝ≥0∞) (hF : ∫⁻ z in unitDisc, F z ≠ ⊤) (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∫⁻ z in unitDisc \ ball 0 (1 - η), F z < ε := by
  obtain ⟨δ, hδ, hδ'⟩ := exists_pos_setLIntegral_lt_of_measure_lt (μ := volume.restrict unitDisc) hF hε
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hm : Tendsto ((volume.restrict unitDisc) ∘ fun n : ℕ => (ball (0 : ℂ) (1 - 1 / ((n : ℝ) + 2)))ᶜ)
      atTop (𝓝 ((volume.restrict unitDisc) (⋂ n : ℕ, (ball (0 : ℂ) (1 - 1 / ((n : ℝ) + 2)))ᶜ))) := by
    refine tendsto_measure_iInter_atTop (fun n => measurableSet_ball.compl.nullMeasurableSet) ?_ ?_
    · intro m n hmn
      refine compl_subset_compl.2 (ball_subset_ball ?_)
      have h1 : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
      have h2 : 1 / ((n : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    · refine ⟨0, ?_⟩
      rw [Measure.restrict_apply' hDm]
      exact ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  have h0 : (volume.restrict unitDisc) (⋂ n : ℕ, (ball (0 : ℂ) (1 - 1 / ((n : ℝ) + 2)))ᶜ) = 0 := by
    rw [Measure.restrict_apply' hDm]
    convert measure_empty (μ := (volume : Measure ℂ))
    ext z
    simp only [mem_inter_iff, mem_iInter, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
    intro hz hzD
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (mem_ball_zero_iff.1 hzD))
    refine hz n (mem_ball_zero_iff.2 ?_)
    have : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  rw [h0] at hm
  obtain ⟨n, hn⟩ := (hm.eventually_lt_const hδ).exists
  refine ⟨1 / ((n : ℝ) + 2), by positivity, ?_, ?_⟩
  · rw [div_lt_one (by positivity)]
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  · have h := hδ' (ball (0 : ℂ) (1 - 1 / ((n : ℝ) + 2)))ᶜ hn
    rwa [Measure.restrict_restrict measurableSet_ball.compl, inter_comm, ← diff_eq] at h

/-- Average of the Green kernel gradient over `B(X, ρ)`, `2ρ = 1 - |X|`:
`∫_{B(X,ρ)} |K(Z, Y)| dZ ≤ πρ² · 12 (2ρ) / (π max(|Y - X|, 2ρ)²)`. -/
theorem s07c_fkps_m3b_kavg (X Y : ℂ) (hX : X ∈ unitDisc) (hY : Y ∈ unitDisc) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ2 : 2 * ρ = 1 - ‖X‖) :
    ∫⁻ Z in ball X ρ, ‖((1 - ‖Z‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (Z - Y) * (1 - Z * conj Y))‖ₑ ≤
      ENNReal.ofReal (π * ρ ^ 2) * ENNReal.ofReal (12 * (2 * ρ) / (π * max ‖Y - X‖ (2 * ρ) ^ 2)) := by
  have hZD : ∀ Z ∈ ball X ρ, Z ∈ unitDisc := by
    intro Z hZ
    rw [mem_ball, dist_eq_norm] at hZ
    refine mem_ball_zero_iff.2 ?_
    have := norm_sub_norm_le Z X
    linarith
  rcases lt_or_ge ‖Y - X‖ (2 * ρ) with hnear | hfar
  · have hmax : max ‖Y - X‖ (2 * ρ) = 2 * ρ := max_eq_right hnear.le
    have hsub : ball X ρ ⊆ ball Y (3 * ρ) := by
      intro Z hZ
      rw [mem_ball, dist_eq_norm] at hZ ⊢
      have := norm_sub_le_norm_sub_add_norm_sub Z X Y
      rw [norm_sub_rev X Y] at this
      linarith
    calc ∫⁻ Z in ball X ρ, ‖((1 - ‖Z‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (Z - Y) * (1 - Z * conj Y))‖ₑ
        ≤ ∫⁻ Z in ball X ρ, ENNReal.ofReal π⁻¹ * ENNReal.ofReal ‖Z - Y‖⁻¹ := by
          refine setLIntegral_mono' measurableSet_ball fun Z hZ => ?_
          rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (inv_nonneg.2 Real.pi_pos.le)]
          exact ENNReal.ofReal_le_ofReal (s07c_fkps_m3b_kernel_le' Z Y (hZD Z hZ) hY)
      _ ≤ ∫⁻ Z in ball Y (3 * ρ), ENNReal.ofReal π⁻¹ * ENNReal.ofReal ‖Z - Y‖⁻¹ := lintegral_mono_set hsub
      _ = ENNReal.ofReal π⁻¹ * ENNReal.ofReal (2 * π * (3 * ρ)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, s07c_fkps_m3b_inv_ball]
      _ = ENNReal.ofReal (π * ρ ^ 2) * ENNReal.ofReal (12 * (2 * ρ) / (π * max ‖Y - X‖ (2 * ρ) ^ 2)) := by
          have h1 : (0 : ℝ) ≤ π * ρ ^ 2 := by positivity
          rw [hmax, ← ENNReal.ofReal_mul (inv_nonneg.2 Real.pi_pos.le), ← ENNReal.ofReal_mul h1]
          congr 1
          field_simp
          ring
  · have hd : 0 < ‖Y - X‖ := by linarith
    have hmax : max ‖Y - X‖ (2 * ρ) = ‖Y - X‖ := max_eq_left hfar
    have hpt : ∀ Z ∈ ball X ρ, ‖((1 - ‖Z‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (Z - Y) * (1 - Z * conj Y))‖ₑ ≤
        ENNReal.ofReal (12 * ρ / (π * ‖Y - X‖ ^ 2)) := by
      intro Z hZ
      have hZ' : ‖Z - X‖ < ρ := by rw [mem_ball, dist_eq_norm] at hZ; exact hZ
      have hZn : ‖Z‖ < 1 := mem_ball_zero_iff.1 (hZD Z hZ)
      have h1 : ‖X‖ - ‖Z‖ ≤ ‖Z - X‖ := by rw [norm_sub_rev]; exact norm_sub_norm_le X Z
      have hZY : ‖Y - X‖ / 2 ≤ ‖Z - Y‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub Y Z X
        rw [norm_sub_rev Y Z] at this
        linarith
      have hne : Y ≠ Z := by
        intro h
        have h0 : ‖Z - Y‖ = 0 := by rw [h, sub_self, norm_zero]
        linarith
      have hk := s07c_fkps_m3_kernel Z (hZD Z hZ) Y hY hne
      rw [← ofReal_norm_eq_enorm]
      refine ENNReal.ofReal_le_ofReal (hk.trans ?_)
      have hpos : 0 < ‖Z - Y‖ := by linarith
      have hm : ‖Z - Y‖ ≤ max ‖Z - Y‖ (1 - ‖Z‖) := le_max_left _ _
      have h3 : 1 - ‖Z‖ < 3 * ρ := by linarith
      have h4 : 1 - ‖Z‖ ^ 2 ≤ 2 * (1 - ‖Z‖) := by nlinarith [norm_nonneg Z]
      have hnum : 1 - ‖Z‖ ^ 2 ≤ 6 * ρ := by linarith
      have hden : 2 * π * (‖Y - X‖ / 2) * (‖Y - X‖ / 2) ≤ 2 * π * ‖Z - Y‖ * max ‖Z - Y‖ (1 - ‖Z‖) := by
        have h5 := mul_le_mul hZY (hZY.trans hm) (by linarith) hpos.le
        have hp := Real.pi_pos
        nlinarith
      calc (1 - ‖Z‖ ^ 2) / (2 * π * ‖Z - Y‖ * max ‖Z - Y‖ (1 - ‖Z‖))
          ≤ (6 * ρ) / (2 * π * (‖Y - X‖ / 2) * (‖Y - X‖ / 2)) :=
            div_le_div₀ (by linarith) hnum (mul_pos (mul_pos (by positivity) (half_pos hd)) (half_pos hd)) hden
        _ = 12 * ρ / (π * ‖Y - X‖ ^ 2) := by field_simp; ring
    calc ∫⁻ Z in ball X ρ, ‖((1 - ‖Z‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (Z - Y) * (1 - Z * conj Y))‖ₑ
        ≤ ∫⁻ Z in ball X ρ, ENNReal.ofReal (12 * ρ / (π * ‖Y - X‖ ^ 2)) :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = ENNReal.ofReal (12 * ρ / (π * ‖Y - X‖ ^ 2)) * ENNReal.ofReal (π * ρ ^ 2) := by
          rw [setLIntegral_const, Complex.volume_ball, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
            ← ENNReal.ofReal_pow hρ.le, ← ENNReal.ofReal_mul (sq_nonneg ρ), mul_comm (ρ ^ 2) π]
      _ ≤ ENNReal.ofReal (π * ρ ^ 2) * ENNReal.ofReal (12 * (2 * ρ) / (π * max ‖Y - X‖ (2 * ρ) ^ 2)) := by
          rw [mul_comm, hmax]
          refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) zero_le
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- `ofReal r * ofReal x ^ 2 = ofReal (r x²)` for `r, x ≥ 0`. -/
theorem s07c_fkps_m3b_ofReal_mul_sq (r x : ℝ) (hr : 0 ≤ r) (hx : 0 ≤ x) :
    ENNReal.ofReal r * ENNReal.ofReal x ^ 2 = ENNReal.ofReal (r * x ^ 2) := by
  rw [ENNReal.ofReal_mul hr, ENNReal.ofReal_pow hx]

/-- The `L²` norm of the averaged-kernel profile `12 c / (π max(|Y - X|, c)²)` is bounded independently
of `c`. -/
theorem s07c_fkps_m3b_profile (X : ℂ) (c : ℝ) (hc : 0 < c) :
    ∫⁻ Y, ENNReal.ofReal (12 * c / (π * max ‖Y - X‖ c ^ 2)) ^ 2 ≤ ENNReal.ofReal (432 / π) := by
  have hGm : Measurable (fun r : ℝ => ENNReal.ofReal (12 * c / (π * max r c ^ 2)) ^ 2) :=
    (ENNReal.measurable_ofReal.comp (measurable_const.div
      (measurable_const.mul ((measurable_id.max measurable_const).pow_const 2)))).pow_const 2
  have e1 : ∫⁻ Y, ENNReal.ofReal (12 * c / (π * max ‖Y - X‖ c ^ 2)) ^ 2 =
      ∫⁻ w : ℂ, ENNReal.ofReal (12 * c / (π * max ‖w‖ c ^ 2)) ^ 2 :=
    lintegral_sub_right_eq_self (fun w : ℂ => ENNReal.ofReal (12 * c / (π * max ‖w‖ c ^ 2)) ^ 2) X
  rw [e1, s07c_fkps_m3b_radial (fun r : ℝ => ENNReal.ofReal (12 * c / (π * max r c ^ 2)) ^ 2) hGm]
  have hA : (0 : ℝ) ≤ 144 / π ^ 2 := by positivity
  have hB : (0 : ℝ) ≤ 72 / π ^ 2 := by positivity
  have hK : (0 : ℝ) ≤ 144 * c ^ 2 / π ^ 2 := by positivity
  have hsplit : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * ENNReal.ofReal (12 * c / (π * max r c ^ 2)) ^ 2 ≤
      ENNReal.ofReal (144 / π ^ 2) + ENNReal.ofReal (72 / π ^ 2) := by
    rw [← Ioc_union_Ioi_eq_Ioi hc.le]
    refine (lintegral_union_le _ _ _).trans (add_le_add ?_ ?_)
    · calc ∫⁻ r in Ioc 0 c, ENNReal.ofReal r * ENNReal.ofReal (12 * c / (π * max r c ^ 2)) ^ 2
          ≤ ∫⁻ r in Ioc 0 c, ENNReal.ofReal (144 / (π ^ 2 * c)) := by
            refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
            rw [s07c_fkps_m3b_ofReal_mul_sq r (12 * c / (π * max r c ^ 2)) hr.1.le
              (div_nonneg (by linarith) (by positivity)), max_eq_right hr.2]
            refine ENNReal.ofReal_le_ofReal ?_
            calc r * (12 * c / (π * c ^ 2)) ^ 2 ≤ c * (12 * c / (π * c ^ 2)) ^ 2 :=
                  mul_le_mul_of_nonneg_right hr.2 (sq_nonneg _)
              _ = 144 / (π ^ 2 * c) := by field_simp; ring
        _ = ENNReal.ofReal (144 / π ^ 2) := by
            have h1 : (0 : ℝ) ≤ 144 / (π ^ 2 * c) := div_nonneg (by norm_num) (by positivity)
            rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul h1]
            congr 1
            field_simp
    · refine le_of_eq ?_
      calc ∫⁻ r in Ioi c, ENNReal.ofReal r * ENNReal.ofReal (12 * c / (π * max r c ^ 2)) ^ 2
          = ∫⁻ r in Ioi c, ENNReal.ofReal (144 * c ^ 2 / π ^ 2) * ENNReal.ofReal (r ^ (-3 : ℝ)) := by
            refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
            have hr0 : 0 < r := hc.trans hr
            rw [s07c_fkps_m3b_ofReal_mul_sq r (12 * c / (π * max r c ^ 2)) hr0.le
              (div_nonneg (by linarith) (by positivity)), max_eq_left (le_of_lt hr),
              ← ENNReal.ofReal_mul hK]
            congr 1
            rw [Real.rpow_neg hr0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            field_simp
            ring
        _ = ENNReal.ofReal (144 * c ^ 2 / π ^ 2) * ENNReal.ofReal (∫ r in Ioi c, r ^ (-3 : ℝ)) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt (by norm_num) hc)]
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
            exact Real.rpow_nonneg (hc.trans hr).le _
        _ = ENNReal.ofReal (72 / π ^ 2) := by
            rw [integral_Ioi_rpow_of_lt (by norm_num) hc, ← ENNReal.ofReal_mul hK]
            congr 1
            rw [show (-3 : ℝ) + 1 = -2 by norm_num, Real.rpow_neg hc.le,
              show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            field_simp
            ring
  calc ENNReal.ofReal (2 * π) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r *
        ENNReal.ofReal (12 * c / (π * max r c ^ 2)) ^ 2
      ≤ ENNReal.ofReal (2 * π) * (ENNReal.ofReal (144 / π ^ 2) + ENNReal.ofReal (72 / π ^ 2)) :=
        mul_le_mul_of_nonneg_left hsplit zero_le
    _ = ENNReal.ofReal (432 / π) := by
        rw [← ENNReal.ofReal_add hA hB, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * π)]
        congr 1
        field_simp
        ring

/-- Pointwise splitting `a v ≤ T a² + T⁻¹ v²` in `ℝ≥0∞`. -/
theorem s07c_fkps_m3b_amgm (a v T : ℝ≥0∞) (hT0 : T ≠ 0) (hT : T ≠ ⊤) :
    a * v ≤ T * a ^ 2 + T⁻¹ * v ^ 2 := by
  by_cases h : v ≤ T * a
  · calc a * v ≤ a * (T * a) := mul_le_mul_of_nonneg_left h zero_le
      _ = T * a ^ 2 := by ring
      _ ≤ _ := le_self_add
  · have h' : T * a < v := not_le.1 h
    have ha : a ≤ T⁻¹ * v := by
      calc a = T⁻¹ * (T * a) := by rw [← mul_assoc, ENNReal.inv_mul_cancel hT0 hT, one_mul]
        _ ≤ T⁻¹ * v := mul_le_mul_of_nonneg_left h'.le zero_le
    calc a * v ≤ T⁻¹ * v * v := mul_le_mul_of_nonneg_right ha zero_le
      _ = T⁻¹ * v ^ 2 := by ring
      _ ≤ _ := le_add_self

/-- The potential `W` averaged over `B(X, ρ)`, `2ρ = 1 - |X|`, is controlled by the kernel profile. -/
theorem s07c_fkps_m3b_Wball (V : ℂ → ℂ) (hV : Measurable V) (X : ℂ) (hX : X ∈ unitDisc) (ρ : ℝ)
    (hρ : 0 < ρ) (hρ2 : 2 * ρ = 1 - ‖X‖) :
    ‖∫ Z in ball X ρ, ∫ Y in unitDisc, (conj (((1 - ‖Z‖ ^ 2 : ℝ) : ℂ) /
        (2 * π * conj (Z - Y) * (1 - Z * conj Y))) * V Y).re‖ₑ ≤
      ENNReal.ofReal (π * ρ ^ 2) * ∫⁻ Y in unitDisc,
        ENNReal.ofReal (12 * (2 * ρ) / (π * max ‖Y - X‖ (2 * ρ) ^ 2)) * ‖V Y‖ₑ := by
  have hm : Measurable (fun p : ℂ × ℂ =>
      ‖((1 - ‖p.1‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (p.1 - p.2) * (1 - p.1 * conj p.2))‖ₑ * ‖V p.2‖ₑ) :=
    s07c_fkps_m3b_kernel_meas.enorm.mul (hV.comp measurable_snd).enorm
  calc ‖∫ Z in ball X ρ, ∫ Y in unitDisc, (conj (((1 - ‖Z‖ ^ 2 : ℝ) : ℂ) /
        (2 * π * conj (Z - Y) * (1 - Z * conj Y))) * V Y).re‖ₑ
      ≤ ∫⁻ Z in ball X ρ, ‖∫ Y in unitDisc, (conj (((1 - ‖Z‖ ^ 2 : ℝ) : ℂ) /
        (2 * π * conj (Z - Y) * (1 - Z * conj Y))) * V Y).re‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ Z in ball X ρ, ∫⁻ Y in unitDisc,
          ‖((1 - ‖Z‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (Z - Y) * (1 - Z * conj Y))‖ₑ * ‖V Y‖ₑ :=
        lintegral_mono fun Z => (enorm_integral_le_lintegral_enorm _).trans
          (lintegral_mono fun Y => s07c_fkps_m3b_re_le _ _)
    _ = ∫⁻ Y in unitDisc, ∫⁻ Z in ball X ρ,
          ‖((1 - ‖Z‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (Z - Y) * (1 - Z * conj Y))‖ₑ * ‖V Y‖ₑ :=
        lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ Y in unitDisc, (∫⁻ Z in ball X ρ,
          ‖((1 - ‖Z‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (Z - Y) * (1 - Z * conj Y))‖ₑ) * ‖V Y‖ₑ := by
        refine lintegral_congr fun Y => ?_
        exact lintegral_mul_const _ ((s07c_fkps_m3b_kernel_meas.comp
          (measurable_id.prodMk measurable_const)).enorm)
    _ ≤ ∫⁻ Y in unitDisc, (ENNReal.ofReal (π * ρ ^ 2) *
          ENNReal.ofReal (12 * (2 * ρ) / (π * max ‖Y - X‖ (2 * ρ) ^ 2))) * ‖V Y‖ₑ :=
        setLIntegral_mono' measurableSet_ball fun Y hY =>
          mul_le_mul_of_nonneg_right (s07c_fkps_m3b_kavg X Y hX hY ρ hρ hρ2) zero_le
    _ = ENNReal.ofReal (π * ρ ^ 2) * ∫⁻ Y in unitDisc,
          ENNReal.ofReal (12 * (2 * ρ) / (π * max ‖Y - X‖ (2 * ρ) ^ 2)) * ‖V Y‖ₑ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun Y => mul_assoc _ _ _

/-- Uniform decay of the profile-weighted `V` near `𝕋`. -/
theorem s07c_fkps_m3b_Wdecay (V : ℂ → ℂ) (hV : Measurable V) (hV2 : ∫⁻ z in unitDisc, ‖V z‖ₑ ^ 2 < ⊤)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ X ∈ unitDisc, 1 - ‖X‖ < η →
      ∫⁻ Y in unitDisc, ENNReal.ofReal (12 * (1 - ‖X‖) / (π * max ‖Y - X‖ (1 - ‖X‖) ^ 2)) * ‖V Y‖ₑ ≤
        ENNReal.ofReal ε := by
  have hLt : ∫⁻ z in unitDisc, ‖V z‖ₑ < ⊤ := s07c_fkps_m3b_l1_of_l2 V unitDisc measure_ball_lt_top.ne hV2
  have h3 : (0 : ℝ) ≤ ε / 3 := by positivity
  have hT0 : ENNReal.ofReal (ε * π / 1296) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hTt : ENNReal.ofReal (ε * π / 1296) ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨η₀, hη₀, hη₀1, htail⟩ := s07c_fkps_m3b_tail (fun z => ‖V z‖ₑ ^ 2) hV2.ne
    (ENNReal.ofReal (ε * π / 1296) * ENNReal.ofReal (ε / 3))
    (mul_ne_zero hT0 (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity))
  have hL0 : 0 ≤ (∫⁻ z in unitDisc, ‖V z‖ₑ).toReal := ENNReal.toReal_nonneg
  refine ⟨min (η₀ / 2) (ε * π * η₀ ^ 2 / (144 * ((∫⁻ z in unitDisc, ‖V z‖ₑ).toReal + 1))),
    lt_min (by positivity) (by positivity), fun X hX hXη => ?_⟩
  have hXn : ‖X‖ < 1 := mem_ball_zero_iff.1 hX
  have hc : 0 < 1 - ‖X‖ := by linarith
  have h1 : 1 - ‖X‖ < η₀ / 2 := hXη.trans_le (min_le_left _ _)
  have h2 : 1 - ‖X‖ < ε * π * η₀ ^ 2 / (144 * ((∫⁻ z in unitDisc, ‖V z‖ₑ).toReal + 1)) :=
    hXη.trans_le (min_le_right _ _)
  have hsplit : unitDisc ⊆ ball (0 : ℂ) (1 - η₀) ∪ (unitDisc \ ball 0 (1 - η₀)) := by
    intro z hz
    by_cases h : z ∈ ball (0 : ℂ) (1 - η₀)
    · exact Or.inl h
    · exact Or.inr ⟨hz, h⟩
  refine (lintegral_mono_set hsplit).trans ((lintegral_union_le _ _ _).trans ?_)
  have hthird : ENNReal.ofReal ε =
      ENNReal.ofReal (ε / 3) + (ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3)) := by
    rw [← ENNReal.ofReal_add h3 h3, ← ENNReal.ofReal_add h3 (add_nonneg h3 h3)]
    congr 1
    ring
  rw [hthird]
  refine add_le_add ?_ ?_
  · calc ∫⁻ Y in ball (0 : ℂ) (1 - η₀),
          ENNReal.ofReal (12 * (1 - ‖X‖) / (π * max ‖Y - X‖ (1 - ‖X‖) ^ 2)) * ‖V Y‖ₑ
        ≤ ∫⁻ Y in ball (0 : ℂ) (1 - η₀), ENNReal.ofReal (48 * (1 - ‖X‖) / (π * η₀ ^ 2)) * ‖V Y‖ₑ := by
          refine setLIntegral_mono' measurableSet_ball fun Y hY =>
            mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
          have hYn : ‖Y‖ < 1 - η₀ := mem_ball_zero_iff.1 hY
          have hd : η₀ / 2 ≤ ‖Y - X‖ := by
            have := norm_sub_norm_le X Y
            rw [norm_sub_rev] at this
            linarith
          have hm : η₀ / 2 ≤ max ‖Y - X‖ (1 - ‖X‖) := hd.trans (le_max_left _ _)
          calc 12 * (1 - ‖X‖) / (π * max ‖Y - X‖ (1 - ‖X‖) ^ 2)
              ≤ 12 * (1 - ‖X‖) / (π * (η₀ / 2) ^ 2) :=
                div_le_div₀ (by linarith) le_rfl (mul_pos Real.pi_pos (pow_pos (half_pos hη₀) 2))
                  (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hm 2) Real.pi_pos.le)
            _ = 48 * (1 - ‖X‖) / (π * η₀ ^ 2) := by field_simp; ring
      _ ≤ ENNReal.ofReal (48 * (1 - ‖X‖) / (π * η₀ ^ 2)) * ∫⁻ z in unitDisc, ‖V z‖ₑ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact mul_le_mul_of_nonneg_left (lintegral_mono_set (ball_subset_ball (by linarith))) zero_le
      _ ≤ ENNReal.ofReal (ε / 3) := by
          have h4 : (0 : ℝ) ≤ 48 * (1 - ‖X‖) / (π * η₀ ^ 2) := div_nonneg (by linarith) (by positivity)
          rw [← ENNReal.ofReal_toReal hLt.ne, ← ENNReal.ofReal_mul h4]
          refine ENNReal.ofReal_le_ofReal ?_
          have h2' := (lt_div_iff₀ (by positivity)).1 h2
          have hpe : 0 < π * η₀ ^ 2 := mul_pos Real.pi_pos (pow_pos hη₀ 2)
          rw [div_mul_eq_mul_div, div_le_iff₀ hpe]
          have h5 : 48 * (1 - ‖X‖) * (∫⁻ z in unitDisc, ‖V z‖ₑ).toReal ≤
              48 * (1 - ‖X‖) * ((∫⁻ z in unitDisc, ‖V z‖ₑ).toReal + 1) := by nlinarith
          nlinarith
  · have hmeas : Measurable (fun Y : ℂ => ENNReal.ofReal (ε * π / 1296) *
        ENNReal.ofReal (12 * (1 - ‖X‖) / (π * max ‖Y - X‖ (1 - ‖X‖) ^ 2)) ^ 2) :=
      measurable_const.mul ((ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_const.mul
        (((measurable_id.sub_const X).norm.max measurable_const).pow_const 2)))).pow_const 2)
    calc ∫⁻ Y in unitDisc \ ball (0 : ℂ) (1 - η₀),
          ENNReal.ofReal (12 * (1 - ‖X‖) / (π * max ‖Y - X‖ (1 - ‖X‖) ^ 2)) * ‖V Y‖ₑ
        ≤ ∫⁻ Y in unitDisc \ ball (0 : ℂ) (1 - η₀), (ENNReal.ofReal (ε * π / 1296) *
            ENNReal.ofReal (12 * (1 - ‖X‖) / (π * max ‖Y - X‖ (1 - ‖X‖) ^ 2)) ^ 2 +
            (ENNReal.ofReal (ε * π / 1296))⁻¹ * ‖V Y‖ₑ ^ 2) :=
          lintegral_mono fun Y => s07c_fkps_m3b_amgm _ _ _ hT0 hTt
      _ = ENNReal.ofReal (ε * π / 1296) * (∫⁻ Y in unitDisc \ ball (0 : ℂ) (1 - η₀),
            ENNReal.ofReal (12 * (1 - ‖X‖) / (π * max ‖Y - X‖ (1 - ‖X‖) ^ 2)) ^ 2) +
          (ENNReal.ofReal (ε * π / 1296))⁻¹ * ∫⁻ Y in unitDisc \ ball (0 : ℂ) (1 - η₀), ‖V Y‖ₑ ^ 2 := by
          rw [lintegral_add_left hmeas, lintegral_const_mul' _ _ hTt,
            lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hT0)]
      _ ≤ ENNReal.ofReal (ε * π / 1296) * ENNReal.ofReal (432 / π) +
          (ENNReal.ofReal (ε * π / 1296))⁻¹ * (ENNReal.ofReal (ε * π / 1296) * ENNReal.ofReal (ε / 3)) := by
          exact add_le_add (mul_le_mul_of_nonneg_left ((setLIntegral_le_lintegral _ _).trans
            (s07c_fkps_m3b_profile X (1 - ‖X‖) hc)) zero_le) (mul_le_mul_of_nonneg_left htail.le zero_le)
      _ = ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hT0 hTt, one_mul,
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ε * π / 1296)]
          congr 2
          field_simp
          ring

/-- Boundary data: `f` is continuous and `2π`-periodic, and `u - P[f]` is continuous on `𝔻` and tends to `0`
at every point of `𝕋`. -/
theorem s07c_fkps_m3b_DP (u : ℂ → ℝ) (f : ℝ → ℝ) (hu : ContinuousOn u (closedBall 0 1))
    (hb : ∀ θ : ℝ, u (Complex.exp (θ * I)) = f θ) :
    Continuous f ∧ (∀ t, f (t + 2 * π) = f t) ∧
      ContinuousOn (fun X : ℂ => u X - (2 * π)⁻¹ *
        ∫ t in (0 : ℝ)..2 * π, (1 - ‖X‖ ^ 2) / ‖Complex.exp (t * I) - X‖ ^ 2 * f t) unitDisc ∧
      ∀ ζ ∈ sphere (0 : ℂ) 1, Tendsto (fun X : ℂ => u X - (2 * π)⁻¹ *
        ∫ t in (0 : ℝ)..2 * π, (1 - ‖X‖ ^ 2) / ‖Complex.exp (t * I) - X‖ ^ 2 * f t)
        (𝓝[unitDisc] ζ) (𝓝 0) := by
  have hf : Continuous f := by
    have e : f = fun θ : ℝ => u (Complex.exp (θ * I)) := funext fun θ => (hb θ).symm
    rw [e]
    exact hu.comp_continuous ((Complex.continuous_ofReal.mul continuous_const).cexp) fun θ => by
      rw [mem_closedBall_zero_iff, Complex.norm_exp_ofReal_mul_I]
  have hper : ∀ t, f (t + 2 * π) = f t := by
    intro t
    rw [← hb, ← hb, s07c_fkps_m2_exp_periodic]
  have hP := s07c_fkps_m2_poisson f hf hper
  refine ⟨hf, hper, (hu.mono ball_subset_closedBall).sub hP.1.continuousOn, fun ζ hζ => ?_⟩
  have hζn : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.1 hζ
  have hζe : Complex.exp (↑(Complex.arg ζ) * I) = ζ := by
    have := Complex.norm_mul_exp_arg_mul_I ζ
    rwa [hζn, Complex.ofReal_one, one_mul] at this
  have hPt := hP.2 (Complex.arg ζ)
  rw [hζe] at hPt
  have hU : Tendsto u (𝓝[unitDisc] ζ) (𝓝 (f (Complex.arg ζ))) := by
    rw [← hb, hζe]
    exact ((hu ζ (mem_closedBall_zero_iff.2 hζn.le)).mono ball_subset_closedBall)
  have := hU.sub hPt
  rwa [sub_self] at this

/-- Uniform decay of a harmonic `H` that equals `D + W` a.e. on `𝔻`, from the uniform smallness of `D` and of
the ball averages of `W` near `𝕋` (mean value property on `B(X, (1 - |X|)/2)`). -/
theorem s07c_fkps_m3b_Hdecay (H D W : ℂ → ℝ) (hH : InnerProductSpace.HarmonicOnNhd H unitDisc)
    (hD : ContinuousOn D unitDisc) (hW : IntegrableOn W unitDisc)
    (hae : ∀ᵐ X, X ∈ unitDisc → H X = D X + W X)
    (hDs : ∀ ε > 0, ∃ η > 0, ∀ Z ∈ unitDisc, 1 - ‖Z‖ < η → |D Z| < ε)
    (hWs : ∀ ε > 0, ∃ η > 0, ∀ X ∈ unitDisc, 1 - ‖X‖ < η →
      ‖∫ Z in ball X ((1 - ‖X‖) / 2), W Z‖ ≤ π * ((1 - ‖X‖) / 2) ^ 2 * ε)
    (ε : ℝ) (hε : 0 < ε) : ∃ η > 0, ∀ X ∈ unitDisc, 1 - ‖X‖ < η → |H X| ≤ 2 * ε := by
  obtain ⟨η₁, hη₁, h1⟩ := hDs ε hε
  obtain ⟨η₂, hη₂, h2⟩ := hWs ε hε
  refine ⟨min (η₁ / 2) η₂, lt_min (by positivity) hη₂, fun X hX hXη => ?_⟩
  have hXn : ‖X‖ < 1 := mem_ball_zero_iff.1 hX
  have hXη1 : 1 - ‖X‖ < η₁ / 2 := hXη.trans_le (min_le_left _ _)
  have hW' := h2 X hX (hXη.trans_le (min_le_right _ _))
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = (1 - ‖X‖) / 2 := ⟨_, rfl⟩
  rw [← hρdef] at hW'
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  have hcb : closedBall X ρ ⊆ unitDisc := by
    intro Z hZ
    rw [mem_closedBall, dist_eq_norm] at hZ
    refine mem_ball_zero_iff.2 ?_
    have := norm_sub_norm_le Z X
    linarith
  have hmv : ∫ Z in ball X ρ, H Z = volume.real (ball X ρ) • H X :=
    (hH.mono hcb).setIntegral_ball_eq
  have hvol : volume.real (ball X ρ) = π * ρ ^ 2 := by
    rw [measureReal_def, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hρ.le, ENNReal.coe_toReal, NNReal.coe_real_pi]
    ring
  have hDi : IntegrableOn D (ball X ρ) :=
    ((hD.mono hcb).integrableOn_compact (isCompact_closedBall X ρ)).mono_set ball_subset_closedBall
  have hWi : IntegrableOn W (ball X ρ) := hW.mono_set (ball_subset_closedBall.trans hcb)
  have hint : ∫ Z in ball X ρ, H Z = (∫ Z in ball X ρ, D Z) + ∫ Z in ball X ρ, W Z := by
    rw [← integral_add hDi hWi]
    refine setIntegral_congr_ae measurableSet_ball ?_
    filter_upwards [hae] with Z hZ hZB
    exact hZ (hcb (ball_subset_closedBall hZB))
  have hDb : ‖∫ Z in ball X ρ, D Z‖ ≤ ε * volume.real (ball X ρ) := by
    refine norm_setIntegral_le_of_norm_le_const measure_ball_lt_top fun Z hZ => ?_
    have hZ' : ‖Z - X‖ < ρ := by rw [mem_ball, dist_eq_norm] at hZ; exact hZ
    have h3 : ‖X‖ - ‖Z‖ ≤ ‖Z - X‖ := by rw [norm_sub_rev]; exact norm_sub_norm_le X Z
    rw [Real.norm_eq_abs]
    exact (h1 Z (hcb (ball_subset_closedBall hZ)) (by rw [hρdef] at hZ'; linarith)).le
  rw [hvol] at hDb
  have hpos : 0 < π * ρ ^ 2 := mul_pos Real.pi_pos (pow_pos hρ 2)
  have e : π * ρ ^ 2 * H X = (∫ Z in ball X ρ, D Z) + ∫ Z in ball X ρ, W Z := by
    rw [← hint, hmv, hvol, smul_eq_mul]
  have key : π * ρ ^ 2 * |H X| ≤ π * ρ ^ 2 * (2 * ε) := by
    have h4 := norm_add_le (∫ Z in ball X ρ, D Z) (∫ Z in ball X ρ, W Z)
    rw [← e, Real.norm_eq_abs, abs_mul, abs_of_pos hpos] at h4
    linarith
  exact le_of_mul_le_mul_left key hpos

/-- A harmonic function on `𝔻` that tends to `0` uniformly at `𝕋` vanishes (Poisson representation of its
zero extension). -/
theorem s07c_fkps_m3b_zero (H : ℂ → ℝ) (hH : InnerProductSpace.HarmonicOnNhd H unitDisc)
    (hdec : ∀ ε > 0, ∃ η > 0, ∀ X ∈ unitDisc, 1 - ‖X‖ < η → |H X| ≤ ε) :
    ∀ X ∈ unitDisc, H X = 0 := by
  intro X hX
  have hE : InnerProductSpace.HarmonicContOnCl (unitDisc.indicator H) (ball 0 1) := by
    refine ⟨fun x hx => ?_, ?_⟩
    · have hev : unitDisc.indicator H =ᶠ[𝓝 x] H :=
        eventually_of_mem (isOpen_ball.mem_nhds hx) fun z hz => indicator_of_mem hz H
      exact (InnerProductSpace.harmonicAt_congr_nhds hev).2 (hH x hx)
    · rw [closure_ball 0 one_ne_zero]
      intro x hx
      by_cases hx1 : x ∈ unitDisc
      · have hev : unitDisc.indicator H =ᶠ[𝓝 x] H :=
          eventually_of_mem (isOpen_ball.mem_nhds hx1) fun z hz => indicator_of_mem hz H
        exact (((hH x hx1).1.continuousAt).congr hev.symm).continuousWithinAt
      · rw [Metric.continuousWithinAt_iff, indicator_of_notMem hx1]
        intro ε hε
        obtain ⟨η, hη, h⟩ := hdec (ε / 2) (half_pos hε)
        refine ⟨η, hη, fun {z} _ hzx => ?_⟩
        rw [Real.dist_eq, sub_zero]
        by_cases hz1 : z ∈ unitDisc
        · rw [indicator_of_mem hz1]
          have hxn : ‖x‖ = 1 :=
            le_antisymm (mem_closedBall_zero_iff.1 hx) (not_lt.1 fun h => hx1 (mem_ball_zero_iff.2 h))
          have h3 : ‖x‖ - ‖z‖ ≤ ‖x - z‖ := norm_sub_norm_le x z
          rw [dist_eq_norm, norm_sub_rev] at hzx
          exact (h z hz1 (by linarith)).trans_lt (half_lt_self hε)
        · rw [indicator_of_notMem hz1, abs_zero]
          exact hε
  have hP := hE.circleAverage_poissonKernel_smul (c := 0) (R := 1) hX
  rw [indicator_of_mem hX] at hP
  rw [← hP]
  have h0 : Real.circleAverage (poissonKernel 0 X • unitDisc.indicator H) 0 1 =
      Real.circleAverage (fun _ => (0 : ℝ)) 0 1 := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    rw [abs_one, mem_sphere_zero_iff_norm] at hz
    have hz' : z ∉ unitDisc := by
      intro h
      have h1 := mem_ball_zero_iff.1 h
      rw [hz] at h1
      exact lt_irrefl _ h1
    simp [indicator_of_notMem hz']
  rw [h0, Real.circleAverage_const]

/-- M3b (Green representation, a.e. form). Let `u` be continuous on `𝔻̄` with boundary values
`u (e^{iθ}) = f θ`, with weak gradient `g ∈ L²(𝔻)` on `𝔻`, and let `V ∈ L²(𝔻)` with `Δu = -div V` weakly on `𝔻`.
Then for a.e. `X ∈ 𝔻` the function `Y ↦ ⟨∇_Y G₀(X, Y), V Y⟩` is integrable on `𝔻` and
`u X = P[f](X) - ∫_𝔻 ⟨∇_Y G₀(X, Y), V Y⟩ dY`. -/
theorem s07c_fkps_m3b_green : ∀ (u : ℂ → ℝ) (f : ℝ → ℝ) (g V : ℂ → ℂ),
    ContinuousOn u (closedBall 0 1) → (∀ θ : ℝ, u (Complex.exp (θ * I)) = f θ) →
    AEMeasurable g → AEMeasurable V →
    (∫⁻ z in unitDisc, ‖g z‖ₑ ^ 2 < ⊤) → (∫⁻ z in unitDisc, ‖V z‖ₑ ^ 2 < ⊤) →
    (∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
      ∫ z, (u z : ℂ) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I) =
        -∫ z, (φ z : ℂ) * g z) →
    (∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
      ∫ z, (conj (g z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re =
        -∫ z, (conj (V z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re) →
    ∀ᵐ X, X ∈ unitDisc →
      IntegrableOn (fun Y => (conj (((1 - ‖X‖ ^ 2 : ℝ) : ℂ) /
        (2 * π * conj (X - Y) * (1 - X * conj Y))) * V Y).re) unitDisc ∧
      u X = (2 * π)⁻¹ * (∫ t in (0 : ℝ)..2 * π,
          (1 - ‖X‖ ^ 2) / ‖Complex.exp (t * I) - X‖ ^ 2 * f t) -
        ∫ Y in unitDisc, (conj (((1 - ‖X‖ ^ 2 : ℝ) : ℂ) /
          (2 * π * conj (X - Y) * (1 - X * conj Y))) * V Y).re := by
  intro u f g V hu hb hg hV hg2 hV2 hP2 hP4
  obtain ⟨hf, hper, hDc, hDb⟩ := s07c_fkps_m3b_DP u f hu hb
  have hVm : Measurable (hV.mk V) := hV.measurable_mk
  have hVeq : V =ᵐ[volume] hV.mk V := hV.ae_eq_mk
  have hVeqD : V =ᵐ[volume.restrict unitDisc] hV.mk V := ae_restrict_of_ae hVeq
  have hVm2 : ∫⁻ z in unitDisc, ‖hV.mk V z‖ₑ ^ 2 < ⊤ := by
    have e : ∫⁻ z in unitDisc, ‖V z‖ₑ ^ 2 = ∫⁻ z in unitDisc, ‖hV.mk V z‖ₑ ^ 2 :=
      lintegral_congr_ae (hVeqD.mono fun z hz => by simp only [hz])
    rw [← e]
    exact hV2
  have hP4m : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
      ∫ z, (conj (g z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re =
        -∫ z, (conj (hV.mk V z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re := by
    intro φ h1 h2 h3
    rw [hP4 φ h1 h2 h3]
    congr 1
    exact integral_congr_ae (hVeq.mono fun z hz => by simp only [hz])
  let Ω : TopologicalSpace.Opens ℂ := ⟨unitDisc, isOpen_ball⟩
  have hΩ : (Ω : Set ℂ) = unitDisc := rfl
  have hw := s07c_fkps_m3b_weak u g (hV.mk V) hu hg hVm hg2 hVm2 hP2 hP4m Ω hΩ
  have hPh : InnerProductSpace.HarmonicOnNhd (fun z : ℂ => (2 * π)⁻¹ *
      ∫ t in (0 : ℝ)..2 * π, (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) - z‖ ^ 2 * f t) (Ω : Set ℂ) :=
    s07c_fkps_m2_poisson_harmonic f hf hper
  obtain ⟨H, hH, hHae⟩ := (hw.sub (hPh.weaklyHarmonicOn (μ := volume))).exists_harmonicOnNhd_ae_eq
  have hHD : InnerProductSpace.HarmonicOnNhd H unitDisc := hH
  have hae : ∀ᵐ X, X ∈ unitDisc → H X = (u X - (2 * π)⁻¹ *
      ∫ t in (0 : ℝ)..2 * π, (1 - ‖X‖ ^ 2) / ‖Complex.exp (t * I) - X‖ ^ 2 * f t) +
      ∫ Y in unitDisc, (conj (((1 - ‖X‖ ^ 2 : ℝ) : ℂ) /
        (2 * π * conj (X - Y) * (1 - X * conj Y))) * hV.mk V Y).re := by
    filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1 hHae] with X hX hXD
    have h1 := hX hXD
    simp only [Pi.sub_apply] at h1
    linarith
  have hWi := s07c_fkps_m3b_W_integrable (hV.mk V) hVm hVm2
  have hWs : ∀ ε > 0, ∃ η > 0, ∀ X ∈ unitDisc, 1 - ‖X‖ < η →
      ‖∫ Z in ball X ((1 - ‖X‖) / 2), ∫ Y in unitDisc, (conj (((1 - ‖Z‖ ^ 2 : ℝ) : ℂ) /
        (2 * π * conj (Z - Y) * (1 - Z * conj Y))) * hV.mk V Y).re‖ ≤
        π * ((1 - ‖X‖) / 2) ^ 2 * ε := by
    intro ε hε
    obtain ⟨η, hη, h⟩ := s07c_fkps_m3b_Wdecay (hV.mk V) hVm hVm2 ε hε
    refine ⟨η, hη, fun X hX hXη => ?_⟩
    have hρ : 0 < (1 - ‖X‖) / 2 := by have := mem_ball_zero_iff.1 hX; linarith
    have hb := s07c_fkps_m3b_Wball (hV.mk V) hVm X hX ((1 - ‖X‖) / 2) hρ (by ring)
    rw [show 2 * ((1 - ‖X‖) / 2) = 1 - ‖X‖ by ring] at hb
    have hc := hb.trans (mul_le_mul_of_nonneg_left (h X hX hXη) zero_le)
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ π * ((1 - ‖X‖) / 2) ^ 2),
      ← ofReal_norm_eq_enorm] at hc
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) hε.le)).1 hc
  have hdec : ∀ ε > 0, ∃ η > 0, ∀ X ∈ unitDisc, 1 - ‖X‖ < η → |H X| ≤ ε := by
    intro ε hε
    obtain ⟨η, hη, h⟩ := s07c_fkps_m3b_Hdecay H _ _ hHD hDc hWi hae
      (fun ε hε => s07c_fkps_m3b_unif _ hDc hDb ε hε) hWs (ε / 2) (half_pos hε)
    exact ⟨η, hη, fun X hX hXη => by have := h X hX hXη; linarith⟩
  have hzero := s07c_fkps_m3b_zero H hHD hdec
  have hint := s07c_fkps_m3b_ae_integrable (hV.mk V) hVm hVm2
  filter_upwards [hint, hae] with X hXi hXe hXD
  have hWeq : ∫ Y in unitDisc, (conj (((1 - ‖X‖ ^ 2 : ℝ) : ℂ) /
        (2 * π * conj (X - Y) * (1 - X * conj Y))) * V Y).re =
      ∫ Y in unitDisc, (conj (((1 - ‖X‖ ^ 2 : ℝ) : ℂ) /
        (2 * π * conj (X - Y) * (1 - X * conj Y))) * hV.mk V Y).re :=
    integral_congr_ae (hVeqD.mono fun Y hY => by simp only [hY])
  refine ⟨(hXi hXD).congr (hVeqD.mono fun Y hY => by simp only [hY]), ?_⟩
  rw [hWeq]
  have h0 := hzero X hXD
  have h1 := hXe hXD
  linarith

/-- M3c helper: for a normalized bump `ρ` with `B̄(x, r) ⊆ 𝔻`, the complex gradient of the mollification
`ρ ⋆ 1_𝔻 u` at `x` is `(ρ ⋆ 1_𝔻 g)(x)` (from (P2) tested with `ρ(x - ·)`). -/
theorem s07c_fkps_m3c_moll_deriv (u : ℂ → ℝ) (g : ℂ → ℂ) (hu : ContinuousOn u (closedBall 0 1))
    (hP2 : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
      ∫ z, (u z : ℂ) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I) =
        -∫ z, (φ z : ℂ) * g z)
    (φ : ContDiffBump (0 : ℂ)) (x : ℂ) (hx : closedBall x φ.rOut ⊆ unitDisc) :
    ((fderiv ℝ (convolution (φ.normed volume) (unitDisc.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x 1 : ℝ) : ℂ) +
      ((fderiv ℝ (convolution (φ.normed volume) (unitDisc.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x I : ℝ) : ℂ) * I =
      (convolution (φ.normed volume) (unitDisc.indicator g) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x := by
  set ρ : ℂ → ℝ := φ.normed volume with hρdef
  have hρ1 : ContDiff ℝ 1 ρ := φ.contDiff_normed
  have hρc : HasCompactSupport ρ := φ.hasCompactSupport_normed
  have hts : tsupport ρ = closedBall 0 φ.rOut := φ.tsupport_normed_eq
  have hsupp : Function.support ρ = ball 0 φ.rOut := φ.support_normed_eq
  have huI : IntegrableOn u unitDisc :=
    (hu.integrableOn_compact (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall
  have hloc : LocallyIntegrable (unitDisc.indicator u) volume :=
    ((integrable_indicator_iff measurableSet_ball).2 huI).locallyIntegrable
  have hD := hρc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ1 hloc x
  have hex : ConvolutionExistsAt (fderiv ℝ ρ) (unitDisc.indicator u) x
      ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL ℂ) volume :=
    (hρc.fderiv (𝕜 := ℝ)).convolutionExists_left _ (hρ1.continuous_fderiv one_ne_zero) hloc x
  -- points `s ∉ 𝔻` are far from `x`
  have hout : ∀ s, s ∉ unitDisc → x - s ∉ tsupport ρ := by
    intro s hs h
    rw [hts, mem_closedBall_zero_iff] at h
    exact hs (hx (by rw [mem_closedBall, dist_eq_norm, norm_sub_rev]; exact h))
  have ev : ∀ v : ℂ, fderiv ℝ (convolution ρ (unitDisc.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x v =
      ∫ s, fderiv ℝ ρ (x - s) v * u s := by
    intro v
    rw [hD.fderiv, convolution_def, ContinuousLinearMap.integral_apply hex v]
    refine Eq.trans ?_ (integral_sub_left_eq_self (fun s => fderiv ℝ ρ (x - s) v * u s) volume x)
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul, sub_sub_cancel]
    by_cases ht : x - t ∈ unitDisc
    · rw [indicator_of_mem ht]
    · have h0 := s07c_fkps_m3a_fderiv_zero ρ t (by simpa using hout (x - t) ht)
      rw [indicator_of_notMem ht, h0]
      simp
  -- the reflected kernel `ψ = ρ(x - ·)` is a test function on `𝔻`
  set ψ : ℂ → ℝ := fun s => ρ (x - s) with hψdef
  have hψ1 : ContDiff ℝ 1 ψ := hρ1.comp (contDiff_const.sub contDiff_id)
  have hψd : ∀ s v, fderiv ℝ ψ s v = -fderiv ℝ ρ (x - s) v := by
    intro s v
    have h := ((hρ1.differentiable one_ne_zero) (x - s)).hasFDerivAt.comp s ((hasFDerivAt_id s).const_sub x)
    rw [show ψ = ρ ∘ HSub.hSub x from rfl, h.fderiv]
    simp
  have hψ0 : ∀ s, s ∉ closedBall x φ.rOut → ψ s = 0 := by
    intro s hs
    refine Function.notMem_support.1 fun h0 => hs ?_
    have h : x - s ∈ Function.support ρ := h0
    rw [hsupp, mem_ball_zero_iff] at h
    rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
    exact h.le
  have hψc : HasCompactSupport ψ := HasCompactSupport.intro (isCompact_closedBall x φ.rOut) hψ0
  have hψb : tsupport ψ ⊆ closedBall x φ.rOut :=
    closure_minimal (fun s hs => by_contra fun h => (Function.mem_support.1 hs) (hψ0 s h)) isClosed_closedBall
  have hψt : tsupport ψ ⊆ unitDisc := hψb.trans hx
  have P := hP2 ψ hψ1 hψc hψt
  -- integrability of the two real pieces
  have hint : ∀ v : ℂ, Integrable (fun s => fderiv ℝ ρ (x - s) v * u s) := fun v =>
    s07c_fkps_m3b_int_u_re u hu (fun s => fderiv ℝ ρ (x - s) v)
      (((hρ1.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)).clm_apply continuous_const)
      (fun s hs => by rw [s07c_fkps_m3a_fderiv_zero ρ (x - s) (hout s hs)]; rfl)
  have hL : ∫ z, (u z : ℂ) * (((fderiv ℝ ψ z 1 : ℝ) : ℂ) + ((fderiv ℝ ψ z I : ℝ) : ℂ) * I) =
      -((((∫ s, fderiv ℝ ρ (x - s) 1 * u s : ℝ)) : ℂ) + ((∫ s, fderiv ℝ ρ (x - s) I * u s : ℝ) : ℂ) * I) := by
    have e : ∀ z, (u z : ℂ) * (((fderiv ℝ ψ z 1 : ℝ) : ℂ) + ((fderiv ℝ ψ z I : ℝ) : ℂ) * I) =
        -((((fderiv ℝ ρ (x - z) 1 * u z : ℝ)) : ℂ) + ((fderiv ℝ ρ (x - z) I * u z : ℝ) : ℂ) * I) := by
      intro z
      rw [hψd, hψd]
      push_cast
      ring
    simp only [e]
    have i1 : Integrable (fun s => ((fderiv ℝ ρ (x - s) 1 * u s : ℝ) : ℂ)) := (hint 1).ofReal
    have i2 : Integrable (fun s => ((fderiv ℝ ρ (x - s) I * u s : ℝ) : ℂ)) := (hint I).ofReal
    have hadd := integral_add i1 (i2.mul_const I)
    rw [integral_neg, hadd, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]
  have hR : (convolution ρ (unitDisc.indicator g) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x = ∫ s, (ψ s : ℂ) * g s := by
    rw [convolution_def]
    refine Eq.trans ?_ (integral_sub_left_eq_self (fun s => (ψ s : ℂ) * g s) volume x)
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hψdef, ContinuousLinearMap.lsmul_apply, sub_sub_cancel, Complex.real_smul]
    by_cases ht : x - t ∈ unitDisc
    · rw [indicator_of_mem ht]
    · have h0 : ρ t = 0 := image_eq_zero_of_notMem_tsupport (by simpa using hout (x - t) ht)
      rw [h0]
      simp
  rw [ev, ev, hR]
  rw [hL] at P
  exact neg_injective P

/-- M3c helper (mollification of the data): for `R < 1` and `δ > 0` there is a `C¹` function `w` with
`|w - u| ≤ δ` on `B̄(0, R)` and `∫_{B(0,R)} |∇w - g|² ≤ δ`. -/
theorem s07c_fkps_m3c_moll (u : ℂ → ℝ) (g : ℂ → ℂ) (hu : ContinuousOn u (closedBall 0 1))
    (hg : AEMeasurable g) (hg2 : ∫⁻ z in unitDisc, ‖g z‖ₑ ^ 2 < ⊤)
    (hP2 : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
      ∫ z, (u z : ℂ) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I) =
        -∫ z, (φ z : ℂ) * g z)
    (R : ℝ) (hR1 : R < 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ w : ℂ → ℝ, ContDiff ℝ 1 w ∧ (∀ x ∈ closedBall (0 : ℂ) R, |w x - u x| ≤ δ) ∧
      ∫⁻ z in ball (0 : ℂ) R, ‖((fderiv ℝ w z 1 : ℝ) : ℂ) + ((fderiv ℝ w z I : ℝ) : ℂ) * I - g z‖ₑ ^ 2 ≤
        ENNReal.ofReal δ := by
  obtain ⟨η, hη, huc⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous hu) δ hδ
  have hc0 : 0 < (1 - R) / 2 := by linarith
  set r : ℕ → ℝ := fun n => (1 - R) / 2 * (1 / ((n : ℝ) + 1)) with hrdef
  have hr0 : ∀ n, 0 < r n := fun n => by positivity
  have hrle : ∀ n, r n ≤ (1 - R) / 2 := fun n => by
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    calc r n ≤ (1 - R) / 2 * 1 := mul_le_mul_of_nonneg_left h1 hc0.le
      _ = _ := mul_one _
  set phi : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨r n / 2, r n, half_pos (hr0 n), half_lt_self (hr0 n)⟩ with hphi
  have hrt : Tendsto (fun n => (phi n).rOut) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((1 - R) / 2)
    rw [mul_zero] at this
    exact this
  have hgm : MemLp g 2 (volume.restrict unitDisc) := by
    have h2 : eLpNorm g 2 (volume.restrict unitDisc) < ⊤ := by
      rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
        hg.aestronglyMeasurable.restrict]
      simpa using hg2
    exact h2
  have hGm : MemLp (unitDisc.indicator g) 2 volume :=
    (memLp_indicator_iff_restrict (measurableSet_ball (x := (0 : ℂ)) (ε := 1)).nullMeasurableSet).2 hgm
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  have hT := TauCeti.tendsto_eLpNorm_normed_convolution_sub (mu := volume) (p := 2)
    ENNReal.ofNat_ne_top hrt hGm
  have hsq : (0 : ℝ) < Real.sqrt δ := Real.sqrt_pos.2 hδ
  obtain ⟨n, hn1, hn2⟩ := ((hT.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hsq))).and
    (hrt.eventually (gt_mem_nhds hη))).exists
  have huI : IntegrableOn u unitDisc :=
    (hu.integrableOn_compact (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall
  have hloc : LocallyIntegrable (unitDisc.indicator u) volume :=
    ((integrable_indicator_iff measurableSet_ball).2 huI).locallyIntegrable
  have hrn : (phi n).rOut = r n := rfl
  refine ⟨convolution ((phi n).normed volume) (unitDisc.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume,
    (phi n).hasCompactSupport_normed.contDiff_convolution_left _ (phi n).contDiff_normed hloc, ?_, ?_⟩
  · intro x hx
    have hxn : ‖x‖ ≤ R := mem_closedBall_zero_iff.1 hx
    have hxD : x ∈ unitDisc := mem_ball_zero_iff.2 (by linarith [hrle n, hr0 n])
    have h := ContDiffBump.dist_normed_convolution_le (φ := phi n) (x₀ := x) (ε := δ) (μ := volume)
      hloc.aestronglyMeasurable ?_
    · rw [indicator_of_mem hxD, Real.dist_eq] at h
      exact h
    · intro y hy
      have hy' : dist y x < r n := hy
      have hyx : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := norm_sub_norm_le y x
      rw [dist_eq_norm] at hy'
      have hyn : ‖y‖ < 1 := by linarith [hrle n]
      rw [indicator_of_mem (show y ∈ unitDisc from mem_ball_zero_iff.2 hyn), indicator_of_mem hxD]
      refine (huc y (mem_closedBall_zero_iff.2 hyn.le) x (mem_closedBall_zero_iff.2 (by linarith)) ?_).le
      rw [dist_eq_norm]
      rw [hrn] at hn2
      linarith
  · have hcont : Continuous (convolution ((phi n).normed volume) (unitDisc.indicator g)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
      (phi n).hasCompactSupport_normed.continuous_convolution_left _ ((phi n).contDiff_normed (n := 1)).continuous
        (hGm.locallyIntegrable one_le_two)
    have hint_eq : ∫⁻ z in ball (0 : ℂ) R, ‖((fderiv ℝ (convolution ((phi n).normed volume)
          (unitDisc.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume) z 1 : ℝ) : ℂ) +
          ((fderiv ℝ (convolution ((phi n).normed volume)
          (unitDisc.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume) z I : ℝ) : ℂ) * I - g z‖ₑ ^ 2 =
        ∫⁻ z in ball (0 : ℂ) R, ‖(convolution ((phi n).normed volume) (unitDisc.indicator g)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume - unitDisc.indicator g) z‖ₑ ^ 2 := by
      refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
      have hzn := mem_ball_zero_iff.1 hz
      have hzD : z ∈ unitDisc := mem_ball_zero_iff.2 (by linarith)
      have hcb : closedBall z (phi n).rOut ⊆ unitDisc := by
        intro y hy
        rw [mem_closedBall, dist_eq_norm, hrn] at hy
        have hyz : ‖y‖ - ‖z‖ ≤ ‖y - z‖ := norm_sub_norm_le y z
        exact mem_ball_zero_iff.2 (by linarith [hrle n])
      rw [s07c_fkps_m3c_moll_deriv u g hu hP2 (phi n) z hcb, Pi.sub_apply, indicator_of_mem hzD]
    rw [hint_eq]
    refine (setLIntegral_le_lintegral _ _).trans ?_
    have hE := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := volume) two_ne_zero ENNReal.ofNat_ne_top
      (hcont.aestronglyMeasurable.sub hGm.aestronglyMeasurable)
    simp only [ENNReal.toReal_ofNat] at hE
    have hX : ∫⁻ z, ‖(convolution ((phi n).normed volume) (unitDisc.indicator g)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume - unitDisc.indicator g) z‖ₑ ^ 2 =
        (eLpNorm (convolution ((phi n).normed volume) (unitDisc.indicator g)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume - unitDisc.indicator g) 2 volume) ^ 2 := by
      have hs : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := fun x => by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
      rw [hE, hs]
      simp only [← ENNReal.rpow_natCast, Nat.cast_ofNat]
    rw [hX]
    calc _ ≤ ENNReal.ofReal (Real.sqrt δ) ^ 2 := pow_le_pow_left₀ zero_le hn1.le 2
      _ = ENNReal.ofReal δ := by rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg δ), Real.sq_sqrt hδ.le]

/-- M3c helper: a function continuous on `𝔻̄` is in `L²(𝔻)`. -/
theorem s07c_fkps_m3c_l2_cont (a : ℂ → ℂ) (ha : ContinuousOn a (closedBall 0 1)) :
    ∫⁻ z in unitDisc, ‖a z‖ₑ ^ 2 < ⊤ := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn ha
  calc ∫⁻ z in unitDisc, ‖a z‖ₑ ^ 2 ≤ ∫⁻ _ in unitDisc, ENNReal.ofReal M ^ 2 := by
        refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
        rw [← ofReal_norm]
        exact pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal (hM z (ball_subset_closedBall hz))) 2
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top (by simp) measure_ball_lt_top

/-- M3c helper: `L²(𝔻)` is closed under addition. -/
theorem s07c_fkps_m3c_l2_add (a b : ℂ → ℂ) (ha' : AEMeasurable a) (ha : ∫⁻ z in unitDisc, ‖a z‖ₑ ^ 2 < ⊤)
    (hb : ∫⁻ z in unitDisc, ‖b z‖ₑ ^ 2 < ⊤) : ∫⁻ z in unitDisc, ‖a z + b z‖ₑ ^ 2 < ⊤ := by
  have hpt : ∀ z, ‖a z + b z‖ₑ ^ 2 ≤ 3 * (‖a z‖ₑ ^ 2 + ‖b z‖ₑ ^ 2) := by
    intro z
    have h1 : ‖a z‖ₑ * ‖b z‖ₑ ≤ ‖a z‖ₑ ^ 2 + ‖b z‖ₑ ^ 2 := by
      have := s07c_fkps_m3b_amgm (‖a z‖ₑ) (‖b z‖ₑ) 1 one_ne_zero ENNReal.one_ne_top
      simpa using this
    calc ‖a z + b z‖ₑ ^ 2 ≤ (‖a z‖ₑ + ‖b z‖ₑ) ^ 2 := pow_le_pow_left₀ zero_le (enorm_add_le _ _) 2
      _ = ‖a z‖ₑ ^ 2 + ‖b z‖ₑ ^ 2 + 2 * (‖a z‖ₑ * ‖b z‖ₑ) := by ring
      _ ≤ ‖a z‖ₑ ^ 2 + ‖b z‖ₑ ^ 2 + 2 * (‖a z‖ₑ ^ 2 + ‖b z‖ₑ ^ 2) := by gcongr
      _ = 3 * (‖a z‖ₑ ^ 2 + ‖b z‖ₑ ^ 2) := by ring
  calc ∫⁻ z in unitDisc, ‖a z + b z‖ₑ ^ 2 ≤ ∫⁻ z in unitDisc, 3 * (‖a z‖ₑ ^ 2 + ‖b z‖ₑ ^ 2) :=
        lintegral_mono fun z => hpt z
    _ ≤ 3 * ((∫⁻ z in unitDisc, ‖a z‖ₑ ^ 2) + ∫⁻ z in unitDisc, ‖b z‖ₑ ^ 2) := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left' (ha'.enorm.pow_const 2).restrict]
    _ < ⊤ := ENNReal.mul_lt_top (by simp) (ENNReal.add_lt_top.2 ⟨ha, hb⟩)

/-- M3c helper: `b ⟨k₁, k₂⟩` is integrable for `k₁, k₂ ∈ L²(𝔻)` and `b` bounded on `𝔻`, if it vanishes off `𝔻`. -/
theorem s07c_fkps_m3c_int (b : ℂ → ℝ) (hb : AEStronglyMeasurable b (volume.restrict unitDisc)) (M : ℝ)
    (hbM : ∀ z ∈ unitDisc, |b z| ≤ M) (k₁ k₂ : ℂ → ℂ) (h₁ : AEMeasurable k₁) (h₂ : AEMeasurable k₂)
    (h₁2 : ∫⁻ z in unitDisc, ‖k₁ z‖ₑ ^ 2 < ⊤) (h₂2 : ∫⁻ z in unitDisc, ‖k₂ z‖ₑ ^ 2 < ⊤)
    (h0 : ∀ z, z ∉ unitDisc → b z * (conj (k₁ z) * k₂ z).re = 0) :
    Integrable (fun z => b z * (conj (k₁ z) * k₂ z).re) := by
  refine (integrableOn_iff_integrable_of_support_subset (s := unitDisc) fun z hz => ?_).1 ⟨?_, ?_⟩
  · by_contra h
    exact hz (h0 z h)
  · exact hb.mul ((Complex.continuous_re.comp_aestronglyMeasurable
      (((Complex.continuous_conj.comp_aestronglyMeasurable h₁.aestronglyMeasurable).mul
        h₂.aestronglyMeasurable))).restrict)
  · show ∫⁻ z in unitDisc, ‖b z * (conj (k₁ z) * k₂ z).re‖ₑ < ⊤
    calc ∫⁻ z in unitDisc, ‖b z * (conj (k₁ z) * k₂ z).re‖ₑ
        ≤ ∫⁻ z in unitDisc, ENNReal.ofReal M * (1 * ‖k₁ z‖ₑ ^ 2 + 1⁻¹ * ‖k₂ z‖ₑ ^ 2) := by
          refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
          rw [enorm_mul]
          refine mul_le_mul' ?_ ((s07c_fkps_m3b_re_le _ _).trans ?_)
          · rw [← ofReal_norm, Real.norm_eq_abs]
            exact ENNReal.ofReal_le_ofReal (hbM z hz)
          · exact s07c_fkps_m3b_amgm _ _ 1 one_ne_zero ENNReal.one_ne_top
      _ < ⊤ := by
          simp only [one_mul, inv_one]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          rw [lintegral_add_left' (h₁.enorm.pow_const 2).restrict]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨h₁2, h₂2⟩)

/-- M3c helper (Q, (P4) tested with `u ψ`): for a `C¹` test function `ψ` with `tsupport ψ ⊆ B(0, R)`, `R < 1`,
`∫ ψ ⟨g + V, g⟩ = -∫ u ⟨g + V, ∇ψ⟩` (test (P4) with `w ψ`, `w` a mollification of `u`, and let `w → u`). -/
theorem s07c_fkps_m3c_Q (u : ℂ → ℝ) (g V : ℂ → ℂ) (hu : ContinuousOn u (closedBall 0 1))
    (hg : AEMeasurable g) (hV : AEMeasurable V)
    (hg2 : ∫⁻ z in unitDisc, ‖g z‖ₑ ^ 2 < ⊤) (hV2 : ∫⁻ z in unitDisc, ‖V z‖ₑ ^ 2 < ⊤)
    (hP2 : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
      ∫ z, (u z : ℂ) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I) =
        -∫ z, (φ z : ℂ) * g z)
    (hP4 : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
      ∫ z, (conj (g z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re =
        -∫ z, (conj (V z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re)
    (ψ : ℂ → ℝ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (R : ℝ) (hR1 : R < 1)
    (ht : tsupport ψ ⊆ ball 0 R) :
    ∫ z, ψ z * (conj (g z + V z) * g z).re =
      -∫ z, u z * (conj (g z + V z) * (((fderiv ℝ ψ z 1 : ℝ) : ℂ) + ((fderiv ℝ ψ z I : ℝ) : ℂ) * I)).re := by
  have hRD : ball (0 : ℂ) R ⊆ unitDisc := ball_subset_ball hR1.le
  have htD : tsupport ψ ⊆ unitDisc := ht.trans hRD
  have hh : AEMeasurable (fun z => g z + V z) := hg.add hV
  have hh2 : ∫⁻ z in unitDisc, ‖g z + V z‖ₑ ^ 2 < ⊤ := s07c_fkps_m3c_l2_add g V hg hg2 hV2
  have hh1 : ∫⁻ z in unitDisc, ‖g z + V z‖ₑ < ⊤ :=
    s07c_fkps_m3b_l1_of_l2 (fun z => g z + V z) unitDisc measure_ball_lt_top.ne hh2
  set Gψ : ℂ → ℂ := fun z => ((fderiv ℝ ψ z 1 : ℝ) : ℂ) + ((fderiv ℝ ψ z I : ℝ) : ℂ) * I with hGψ
  have hdψ : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  have hGψc : Continuous Gψ :=
    (continuous_ofReal.comp (hdψ.clm_apply continuous_const)).add
      ((continuous_ofReal.comp (hdψ.clm_apply continuous_const)).mul continuous_const)
  have hψ0 : ∀ z, z ∉ tsupport ψ → ψ z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hGψ0 : ∀ z, z ∉ tsupport ψ → Gψ z = 0 := fun z hz => by
    simp [hGψ, s07c_fkps_m3a_fderiv_zero ψ z hz]
  obtain ⟨Mψ, hMψ⟩ := hc.exists_bound_of_continuous hψ.continuous
  obtain ⟨M1, hM1⟩ := (hc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hdψ
  have hMψ0 : 0 ≤ Mψ := (norm_nonneg _).trans (hMψ 0)
  have hM10 : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0)
  have hGψb : ∀ z, ‖Gψ z‖ ≤ 2 * M1 := by
    intro z
    have e1 : ‖fderiv ℝ ψ z 1‖ ≤ M1 := (ContinuousLinearMap.le_of_opNorm_le _ (hM1 z) 1).trans (by simp)
    have e2 : ‖fderiv ℝ ψ z I‖ ≤ M1 := (ContinuousLinearMap.le_of_opNorm_le _ (hM1 z) I).trans (by simp)
    calc ‖Gψ z‖ ≤ ‖((fderiv ℝ ψ z 1 : ℝ) : ℂ)‖ + ‖((fderiv ℝ ψ z I : ℝ) : ℂ) * I‖ := norm_add_le _ _
      _ ≤ M1 + M1 := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real]
          exact add_le_add e1 e2
      _ = 2 * M1 := by ring
  obtain ⟨Mu, hMu⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hu
  have huD : AEStronglyMeasurable u (volume.restrict unitDisc) :=
    (hu.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
  have hψD : AEStronglyMeasurable ψ (volume.restrict unitDisc) := hψ.continuous.aestronglyMeasurable
  have hGψ2 : ∫⁻ z in unitDisc, ‖Gψ z‖ₑ ^ 2 < ⊤ := s07c_fkps_m3c_l2_cont Gψ hGψc.continuousOn
  have iA : Integrable (fun z => ψ z * (conj (g z + V z) * g z).re) :=
    s07c_fkps_m3c_int ψ hψD Mψ (fun z _ => hMψ z) _ g hh hg hh2 hg2
      (fun z hz => by rw [hψ0 z (fun h => hz (htD h)), zero_mul])
  have iB : Integrable (fun z => u z * (conj (g z + V z) * Gψ z).re) :=
    s07c_fkps_m3c_int u huD Mu (fun z hz => hMu z (ball_subset_closedBall hz)) _ Gψ hh
      hGψc.aemeasurable hh2 hGψ2 (fun z hz => by rw [hGψ0 z (fun h => hz (htD h))]; simp)
  -- the estimate for a fixed mollification parameter `δ ∈ (0, 1]`
  set D := (∫ z, ψ z * (conj (g z + V z) * g z).re) + ∫ z, u z * (conj (g z + V z) * Gψ z).re with hD
  set K : ℝ≥0∞ := ENNReal.ofReal Mψ * ((∫⁻ z in unitDisc, ‖g z + V z‖ₑ ^ 2) + 1) +
    ENNReal.ofReal (2 * M1) * ∫⁻ z in unitDisc, ‖g z + V z‖ₑ with hK
  have hKt : K ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.add_ne_top.2 ⟨hh2.ne, ENNReal.one_ne_top⟩), ENNReal.mul_ne_top ENNReal.ofReal_ne_top hh1.ne⟩
  have key : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ‖D‖ₑ ≤ ENNReal.ofReal (Real.sqrt δ) * K := by
    intro δ hδ hδ1
    obtain ⟨w, hw, hwu, hwg⟩ := s07c_fkps_m3c_moll u g hu hg hg2 hP2 R hR1 δ hδ
    set Gw : ℂ → ℂ := fun z => ((fderiv ℝ w z 1 : ℝ) : ℂ) + ((fderiv ℝ w z I : ℝ) : ℂ) * I with hGw
    have hdw : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
    have hGwc : Continuous Gw :=
      (continuous_ofReal.comp (hdw.clm_apply continuous_const)).add
        ((continuous_ofReal.comp (hdw.clm_apply continuous_const)).mul continuous_const)
    obtain ⟨Mw, hMw⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hw.continuous.continuousOn
    -- (P4) tested with `w ψ`
    have hφ1 : ContDiff ℝ 1 (fun z => w z * ψ z) := hw.mul hψ
    have hφc : HasCompactSupport (fun z => w z * ψ z) := hc.mul_left
    have hφt : tsupport (fun z => w z * ψ z) ⊆ unitDisc := (tsupport_mul_subset_right).trans htD
    have hgrad : ∀ z, ((fderiv ℝ (fun z => w z * ψ z) z 1 : ℝ) : ℂ) +
        ((fderiv ℝ (fun z => w z * ψ z) z I : ℝ) : ℂ) * I = (ψ z : ℂ) * Gw z + (w z : ℂ) * Gψ z := by
      intro z
      have e := fderiv_mul (𝕜 := ℝ) ((hw.differentiable one_ne_zero) z) ((hψ.differentiable one_ne_zero) z)
      rw [show (fun z => w z * ψ z) = w * ψ from rfl, e]
      simp only [hGw, hGψ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      push_cast
      ring
    have hP := hP4 _ hφ1 hφc hφt
    simp only [hgrad] at hP
    have hGφc : Continuous (fun z => (ψ z : ℂ) * Gw z + (w z : ℂ) * Gψ z) :=
      ((continuous_ofReal.comp hψ.continuous).mul hGwc).add ((continuous_ofReal.comp hw.continuous).mul hGψc)
    have hGφ0 : ∀ z, z ∉ unitDisc → (ψ z : ℂ) * Gw z + (w z : ℂ) * Gψ z = 0 := fun z hz => by
      rw [hψ0 z (fun h => hz (htD h)), hGψ0 z (fun h => hz (htD h))]; simp
    have hGφ2 := s07c_fkps_m3c_l2_cont _ hGφc.continuousOn
    have one_bd : ∀ z ∈ unitDisc, |(1 : ℝ)| ≤ 1 := fun _ _ => by simp
    have iG := s07c_fkps_m3c_int (fun _ => 1) aestronglyMeasurable_const 1 one_bd g _ hg hGφc.aemeasurable
      hg2 hGφ2 (fun z hz => by rw [hGφ0 z hz]; simp)
    have iV := s07c_fkps_m3c_int (fun _ => 1) aestronglyMeasurable_const 1 one_bd V _ hV hGφc.aemeasurable
      hV2 hGφ2 (fun z hz => by rw [hGφ0 z hz]; simp)
    simp only [one_mul] at iG iV
    have iC : Integrable (fun z => ψ z * (conj (g z + V z) * Gw z).re) :=
      s07c_fkps_m3c_int ψ hψD Mψ (fun z _ => hMψ z) _ Gw hh hGwc.aemeasurable hh2
        (s07c_fkps_m3c_l2_cont Gw hGwc.continuousOn) (fun z hz => by rw [hψ0 z (fun h => hz (htD h)), zero_mul])
    have iD : Integrable (fun z => w z * (conj (g z + V z) * Gψ z).re) :=
      s07c_fkps_m3c_int w hw.continuous.aestronglyMeasurable Mw
        (fun z hz => by have := hMw z (ball_subset_closedBall hz); rwa [Real.norm_eq_abs] at this) _ Gψ hh
        hGψc.aemeasurable hh2 hGψ2 (fun z hz => by rw [hGψ0 z (fun h => hz (htD h))]; simp)
    have h0 : ∫ z, (ψ z * (conj (g z + V z) * Gw z).re + w z * (conj (g z + V z) * Gψ z).re) = 0 := by
      have e : ∀ z, ψ z * (conj (g z + V z) * Gw z).re + w z * (conj (g z + V z) * Gψ z).re =
          (conj (g z) * ((ψ z : ℂ) * Gw z + (w z : ℂ) * Gψ z)).re +
            (conj (V z) * ((ψ z : ℂ) * Gw z + (w z : ℂ) * Gψ z)).re := by
        intro z
        simp only [map_add, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
          Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
      simp only [e]
      rw [integral_add iG iV, hP, neg_add_cancel]
    have hDe : D = ∫ z, (ψ z * (conj (g z + V z) * (g z - Gw z)).re +
        (u z - w z) * (conj (g z + V z) * Gψ z).re) := by
      have iAB : Integrable (fun z => ψ z * (conj (g z + V z) * g z).re +
          u z * (conj (g z + V z) * Gψ z).re) := iA.add iB
      have iCD : Integrable (fun z => ψ z * (conj (g z + V z) * Gw z).re +
          w z * (conj (g z + V z) * Gψ z).re) := iC.add iD
      rw [hD, ← integral_add iA iB, ← sub_zero (∫ z, _ + _), ← h0, ← integral_sub iAB iCD]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im]
      ring
    rw [hDe]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    set T : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt δ) with hT
    have hsq : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
    have hT0 : T ≠ 0 := by rw [hT, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hsq
    have hTt : T ≠ ⊤ := ENNReal.ofReal_ne_top
    have hpt : ∀ z, ‖ψ z * (conj (g z + V z) * (g z - Gw z)).re + (u z - w z) * (conj (g z + V z) * Gψ z).re‖ₑ ≤
        (ball (0 : ℂ) R).indicator (fun z => ENNReal.ofReal Mψ * (T * ‖g z + V z‖ₑ ^ 2) +
          ENNReal.ofReal Mψ * (T⁻¹ * ‖Gw z - g z‖ₑ ^ 2) +
          ENNReal.ofReal δ * ENNReal.ofReal (2 * M1) * ‖g z + V z‖ₑ) z := by
      intro z
      by_cases hz : z ∈ ball (0 : ℂ) R
      · rw [indicator_of_mem hz]
        refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [enorm_mul, ← mul_add]
          refine mul_le_mul' ?_ ((s07c_fkps_m3b_re_le _ _).trans ?_)
          · rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hMψ z)
          · rw [enorm_sub_rev (g z)]; exact s07c_fkps_m3b_amgm _ _ T hT0 hTt
        · rw [enorm_mul, mul_assoc]
          refine mul_le_mul' ?_ ((s07c_fkps_m3b_re_le _ _).trans ?_)
          · rw [← ofReal_norm, Real.norm_eq_abs, abs_sub_comm]
            exact ENNReal.ofReal_le_ofReal (hwu z (ball_subset_closedBall hz))
          · rw [mul_comm]
            refine mul_le_mul' ?_ le_rfl
            rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hGψb z)
      · rw [indicator_of_notMem hz, hψ0 z (fun h => hz (ht h)), hGψ0 z (fun h => hz (ht h))]
        simp
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_indicator measurableSet_ball]
    have hm1 : AEMeasurable (fun z => ENNReal.ofReal Mψ * (T * ‖g z + V z‖ₑ ^ 2)) (volume.restrict (ball 0 R)) :=
      (aemeasurable_const.mul (aemeasurable_const.mul (hh.enorm.pow_const 2))).restrict
    have hm2 : AEMeasurable (fun z => ENNReal.ofReal Mψ * (T * ‖g z + V z‖ₑ ^ 2) +
        ENNReal.ofReal Mψ * (T⁻¹ * ‖Gw z - g z‖ₑ ^ 2)) (volume.restrict (ball 0 R)) :=
      hm1.add (aemeasurable_const.mul (aemeasurable_const.mul
        (((hGwc.aemeasurable.sub hg).enorm.pow_const 2)))).restrict
    rw [lintegral_add_left' hm2, lintegral_add_left' hm1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ hTt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hT0),
      lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    have hδT : ENNReal.ofReal δ = T * T := by
      rw [hT, ← ENNReal.ofReal_mul hsq.le, Real.mul_self_sqrt hδ.le]
    have hTδ : T⁻¹ * ENNReal.ofReal δ = T := by
      rw [hδT, ← mul_assoc, ENNReal.inv_mul_cancel hT0 hTt, one_mul]
    have hδT' : ENNReal.ofReal δ ≤ T := by
      rw [hT]; refine ENNReal.ofReal_le_ofReal ?_
      calc δ = Real.sqrt δ * Real.sqrt δ := (Real.mul_self_sqrt hδ.le).symm
        _ ≤ Real.sqrt δ * 1 := by
            gcongr; rw [Real.sqrt_le_one]; exact hδ1
        _ = Real.sqrt δ := mul_one _
    calc ENNReal.ofReal Mψ * (T * ∫⁻ z in ball (0 : ℂ) R, ‖g z + V z‖ₑ ^ 2) +
          ENNReal.ofReal Mψ * (T⁻¹ * ∫⁻ z in ball (0 : ℂ) R, ‖Gw z - g z‖ₑ ^ 2) +
          ENNReal.ofReal δ * ENNReal.ofReal (2 * M1) * ∫⁻ z in ball (0 : ℂ) R, ‖g z + V z‖ₑ
        ≤ ENNReal.ofReal Mψ * (T * ∫⁻ z in unitDisc, ‖g z + V z‖ₑ ^ 2) +
          ENNReal.ofReal Mψ * (T⁻¹ * ENNReal.ofReal δ) +
          T * ENNReal.ofReal (2 * M1) * ∫⁻ z in unitDisc, ‖g z + V z‖ₑ := by
          gcongr
      _ = T * K := by rw [hTδ, hK]; ring
  -- conclusion: `‖D‖ₑ ≤ √δ K` for all small `δ` forces `D = 0`
  have hlim : Tendsto (fun δ : ℝ => ENNReal.ofReal (Real.sqrt δ) * K) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun δ : ℝ => ENNReal.ofReal (Real.sqrt δ)) (𝓝[>] 0) (𝓝 0) := by
      have := ((ENNReal.continuous_ofReal.comp Real.continuous_sqrt).tendsto 0)
      simp only [Function.comp_def, Real.sqrt_zero, ENNReal.ofReal_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    have := ENNReal.Tendsto.mul_const h1 (Or.inr hKt)
    rwa [zero_mul] at this
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ‖D‖ₑ ≤ ENNReal.ofReal (Real.sqrt δ) * K := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
    exact key δ hδ.1 hδ.2.le
  have hD0 : ‖D‖ₑ ≤ 0 := ge_of_tendsto hlim hev
  have hD00 : D = 0 := by simpa using hD0
  linarith [hD00, hD]

/-- M3c helper: radial test functions `ψ(Y) = ∫_{|Y|²}^1 k` for continuous `k` vanishing on `[1 - 1/N, ∞)`:
`ψ` is `C¹` with compact support in `B(0, 1 - 1/(4N))`, `∇ψ(Y) = -2 k(|Y|²) Y`, `|ψ| ≤ B` on `𝔻` if `|k| ≤ B`. -/
theorem s07c_fkps_m3c_radial (k : ℝ → ℝ) (hk : Continuous k) (N : ℝ) (hN : 1 ≤ N)
    (hk0 : ∀ s, 1 - 1 / N ≤ s → k s = 0) (B : ℝ) (hB : ∀ s, |k s| ≤ B) :
    ContDiff ℝ 1 (fun Y : ℂ => ∫ s in ‖Y‖ ^ 2..1, k s) ∧
      HasCompactSupport (fun Y : ℂ => ∫ s in ‖Y‖ ^ 2..1, k s) ∧
      tsupport (fun Y : ℂ => ∫ s in ‖Y‖ ^ 2..1, k s) ⊆ ball 0 (1 - 1 / (4 * N)) ∧
      (∀ Y : ℂ, ((fderiv ℝ (fun Y : ℂ => ∫ s in ‖Y‖ ^ 2..1, k s) Y 1 : ℝ) : ℂ) +
        ((fderiv ℝ (fun Y : ℂ => ∫ s in ‖Y‖ ^ 2..1, k s) Y I : ℝ) : ℂ) * I = ((-2 * k (‖Y‖ ^ 2) : ℝ) : ℂ) * Y) ∧
      (∀ Y : ℂ, ‖Y‖ < 1 → |∫ s in ‖Y‖ ^ 2..1, k s| ≤ B) ∧
      (∀ Y : ℂ, 1 ≤ ‖Y‖ → ∫ s in ‖Y‖ ^ 2..1, k s = 0) := by
  have hN0 : 0 < N := by linarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set Φ : ℝ → ℝ := fun t => ∫ s in t..1, k s with hΦ
  have hΦd : ∀ t, HasDerivAt Φ (-k t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_left (hk.intervalIntegrable _ _) (hk.stronglyMeasurableAtFilter _ _)
      hk.continuousAt
  have hΦ1 : ContDiff ℝ 1 Φ := by
    refine contDiff_one_iff_deriv.2 ⟨fun t => (hΦd t).differentiableAt, ?_⟩
    rw [show deriv Φ = fun t => -k t from funext fun t => (hΦd t).deriv]
    exact hk.neg
  have hΦ0 : ∀ t, 1 - 1 / N ≤ t → Φ t = 0 := by
    intro t ht
    have e : ∫ s in t..1, k s = ∫ _ in t..1, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      refine hk0 s ?_
      have h1 := (Set.mem_uIcc.1 hs)
      have h2 : 1 - 1 / N ≤ 1 := by have : 0 < 1 / N := by positivity
                                    linarith
      rcases h1 with h | h
      · linarith [h.1]
      · linarith [h.1]
    simp only [hΦ, e, intervalIntegral.integral_zero]
  have hψ0 : ∀ Y : ℂ, 1 - 1 / (2 * N) ≤ ‖Y‖ → Φ (‖Y‖ ^ 2) = 0 := by
    intro Y hY
    refine hΦ0 _ ?_
    have h1 : 0 ≤ 1 - 1 / (2 * N) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    have h2 : (1 - 1 / (2 * N)) ^ 2 ≤ ‖Y‖ ^ 2 := pow_le_pow_left₀ h1 hY 2
    have h3 : 1 - 1 / N ≤ (1 - 1 / (2 * N)) ^ 2 := by
      have : (1 - 1 / (2 * N)) ^ 2 = 1 - 1 / N + (1 / (2 * N)) ^ 2 := by field_simp; ring
      rw [this]; nlinarith [sq_nonneg (1 / (2 * N))]
    linarith
  have hsub : ∀ Y : ℂ, Y ∉ closedBall (0 : ℂ) (1 - 1 / (2 * N)) → Φ (‖Y‖ ^ 2) = 0 := fun Y hY =>
    hψ0 Y (by rw [mem_closedBall_zero_iff, not_le] at hY; exact hY.le)
  have hts : tsupport (fun Y : ℂ => Φ (‖Y‖ ^ 2)) ⊆ closedBall 0 (1 - 1 / (2 * N)) :=
    closure_minimal (fun Y hY => by_contra fun h => (Function.mem_support.1 hY) (hsub Y h)) isClosed_closedBall
  refine ⟨hΦ1.comp (contDiff_norm_sq ℝ), HasCompactSupport.intro (isCompact_closedBall _ _) hsub,
    hts.trans (closedBall_subset_ball ?_), fun Y => ?_, fun Y hY => ?_, fun Y hY => hψ0 Y ?_⟩
  · have : 1 / (4 * N) < 1 / (2 * N) := one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith
  · have hn : HasFDerivAt (fun Y : ℂ => ‖Y‖ ^ 2) (2 • (innerSL ℝ Y).comp (ContinuousLinearMap.id ℝ ℂ)) Y :=
      (hasFDerivAt_id Y).norm_sq
    have hc := (hΦd (‖Y‖ ^ 2)).comp_hasFDerivAt Y hn
    rw [show (fun Y : ℂ => ∫ s in ‖Y‖ ^ 2..1, k s) = Φ ∘ fun Y : ℂ => ‖Y‖ ^ 2 from rfl, hc.fderiv]
    apply Complex.ext <;>
      simp [Complex.inner, Complex.mul_re, Complex.mul_im] <;> ring
  · have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := ‖Y‖ ^ 2) (b := 1) (C := B)
      (f := k) fun s _ => by rw [Real.norm_eq_abs]; exact hB s
    rw [Real.norm_eq_abs] at h1
    refine h1.trans ?_
    have h2 : |1 - ‖Y‖ ^ 2| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith [norm_nonneg Y]
    calc B * |1 - ‖Y‖ ^ 2| ≤ B * 1 := mul_le_mul_of_nonneg_left h2 hB0
      _ = B := mul_one B
  · have : 0 < 1 / (2 * N) := by positivity
    linarith

/-- M3c helper: the cutoffs `σₙ(s) = max 0 (min 1 (min (N(s - 1/4) + 1) (N(1 - s) - 1)))`, `N = n + 2`, are eventually
equal to the indicator of `[1/4, 1)`. -/
theorem s07c_fkps_m3c_sig (s : ℝ) : ∀ᶠ n : ℕ in atTop,
    max 0 (min 1 (min (((n : ℝ) + 2) * (s - 1 / 4) + 1) (((n : ℝ) + 2) * (1 - s) - 1))) =
      (Ico (1 / 4 : ℝ) 1).indicator 1 s := by
  rcases lt_or_ge s (1 / 4) with h | h
  · rw [indicator_of_notMem (show s ∉ Ico (1 / 4 : ℝ) 1 from fun h' => (not_le.2 h) h'.1)]
    filter_upwards [eventually_ge_atTop ⌈1 / (1 / 4 - s)⌉₊] with n hn
    have h1 : 1 / (1 / 4 - s) ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have h2 : (1 : ℝ) ≤ n * (1 / 4 - s) := by
      rwa [div_le_iff₀ (by linarith)] at h1
    refine max_eq_left ((min_le_right _ _).trans ((min_le_left _ _).trans ?_))
    nlinarith
  · rcases lt_or_ge s 1 with h' | h'
    · rw [indicator_of_mem (show s ∈ Ico (1 / 4 : ℝ) 1 from ⟨h, h'⟩), Pi.one_apply]
      filter_upwards [eventually_ge_atTop ⌈2 / (1 - s)⌉₊] with n hn
      have h1 : 2 / (1 - s) ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
      have h2 : (2 : ℝ) ≤ n * (1 - s) := by
        rwa [div_le_iff₀ (by linarith)] at h1
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [min_eq_left (le_min (by nlinarith) (by nlinarith)), max_eq_right zero_le_one]
    · rw [indicator_of_notMem (show s ∉ Ico (1 / 4 : ℝ) 1 from fun h'' => (not_lt.2 h') h''.2)]
      refine Eventually.of_forall fun n => max_eq_left ((min_le_right _ _).trans ((min_le_right _ _).trans ?_))
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith

/-- M3c helper: for `0 ≤ t < 1`, `∫_t^1 σₙ(s) / (4π max(s, 1/4)) ds → (4π)⁻¹ log (1 / max(t, 1/4))`. -/
theorem s07c_fkps_m3c_Phi (t : ℝ) (ht1 : t < 1) :
    Tendsto (fun n : ℕ => ∫ s in t..1,
      max 0 (min 1 (min (((n : ℝ) + 2) * (s - 1 / 4) + 1) (((n : ℝ) + 2) * (1 - s) - 1))) *
        (4 * π * max s (1 / 4))⁻¹) atTop (𝓝 ((4 * π)⁻¹ * Real.log (1 / max t (1 / 4)))) := by
  have hpi := Real.pi_pos
  set F : ℝ → ℝ := fun s => (4 * π * max s (1 / 4))⁻¹ with hF
  have hFc : Continuous F := (continuous_const.mul (continuous_id.max continuous_const)).inv₀ fun s =>
    (mul_pos (mul_pos four_pos hpi) (lt_max_of_lt_right (by norm_num : (0 : ℝ) < 1 / 4))).ne'
  have hFb : ∀ s, |F s| ≤ π⁻¹ := by
    intro s
    have h4 : (1 / 4 : ℝ) ≤ max s (1 / 4) := le_max_right _ _
    rw [abs_of_pos (by simp only [hF]; positivity)]
    calc F s ≤ (4 * π * (1 / 4))⁻¹ := by
          simp only [hF]
          exact inv_anti₀ (by positivity) (by gcongr)
      _ = π⁻¹ := by ring_nf
  have hlim : Tendsto (fun n : ℕ => ∫ s in t..1,
      max 0 (min 1 (min (((n : ℝ) + 2) * (s - 1 / 4) + 1) (((n : ℝ) + 2) * (1 - s) - 1))) * F s) atTop
      (𝓝 (∫ s in t..1, (Ico (1 / 4 : ℝ) 1).indicator 1 s * F s)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => π⁻¹) ?_ ?_
      intervalIntegrable_const ?_
    · refine Eventually.of_forall fun n => (Continuous.aestronglyMeasurable ?_)
      exact (continuous_const.max (continuous_const.min (((continuous_const.mul
        (continuous_id.sub continuous_const)).add continuous_const).min
        ((continuous_const.mul (continuous_const.sub continuous_id)).sub continuous_const)))).mul hFc
    · refine Eventually.of_forall fun n => Eventually.of_forall fun s _ => ?_
      rw [Real.norm_eq_abs, abs_mul]
      have h0 : |max 0 (min 1 (min (((n : ℝ) + 2) * (s - 1 / 4) + 1) (((n : ℝ) + 2) * (1 - s) - 1)))| ≤ 1 := by
        rw [abs_of_nonneg (le_max_left _ _)]
        exact max_le zero_le_one (min_le_left _ _)
      calc _ ≤ 1 * π⁻¹ := mul_le_mul h0 (hFb s) (abs_nonneg _) zero_le_one
        _ = π⁻¹ := one_mul _
    · refine Eventually.of_forall fun s _ => ?_
      exact tendsto_const_nhds.congr' ((s07c_fkps_m3c_sig s).mono fun n hn => by beta_reduce; rw [hn])
  have hne : ∀ c : ℝ, ∀ᵐ s ∂(volume : Measure ℝ), s ≠ c := fun c => by
    rw [ae_iff]; simp
  set m := max t (1 / 4) with hm
  have hm4 : 1 / 4 ≤ m := le_max_right _ _
  have htm : t ≤ m := le_max_left _ _
  have hm1 : m < 1 := max_lt ht1 (by norm_num)
  have hm0 : 0 < m := by linarith
  have hval : ∫ s in t..1, (Ico (1 / 4 : ℝ) 1).indicator 1 s * F s = (4 * π)⁻¹ * Real.log (1 / m) := by
    calc ∫ s in t..1, (Ico (1 / 4 : ℝ) 1).indicator 1 s * F s
        = ∫ s in t..1, (Ioc m 1).indicator (fun s => (4 * π)⁻¹ * s⁻¹) s := by
          refine intervalIntegral.integral_congr_ae ?_
          filter_upwards [hne (1 / 4), hne 1] with s hs4 hs1 hst
          rw [Set.uIoc_of_le ht1.le] at hst
          by_cases hsm : m < s
          · have hs1' : s < 1 := lt_of_le_of_ne hst.2 hs1
            rw [indicator_of_mem (⟨by linarith, hs1'⟩ : s ∈ Ico (1 / 4 : ℝ) 1), indicator_of_mem (show s ∈ Ioc m 1 from ⟨hsm, hst.2⟩),
              Pi.one_apply, one_mul, hF]
            beta_reduce
            rw [max_eq_left (by linarith : (1 / 4 : ℝ) ≤ s), mul_inv]
          · have hs4' : s < 1 / 4 := by
              rcases lt_or_ge t (1 / 4) with h | h
              · have : m = 1 / 4 := max_eq_right h.le
                exact lt_of_le_of_ne (by linarith [not_lt.1 hsm]) hs4
              · have : m = t := max_eq_left h
                linarith [hst.1, not_lt.1 hsm]
            rw [indicator_of_notMem (show s ∉ Ico (1 / 4 : ℝ) 1 from fun h => (not_le.2 hs4') h.1), indicator_of_notMem (show s ∉ Ioc m 1 from fun h => hsm h.1), zero_mul]
      _ = ∫ s in m..1, (4 * π)⁻¹ * s⁻¹ := by
          rw [intervalIntegral.integral_of_le ht1.le, setIntegral_indicator measurableSet_Ioc, Ioc_inter_Ioc,
            max_eq_right htm, min_self, ← intervalIntegral.integral_of_le hm1.le]
      _ = (4 * π)⁻¹ * Real.log (1 / m) := by
          rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hm0 one_pos]
  rw [← hval]
  exact hlim

/-- M3c helper: the radial profiles `kₙ(s) = σₙ(s) / (4π max(s, 1/4))` are continuous, vanish on
`[1 - 1/(n+2), ∞)` and are bounded by `π⁻¹`. -/
theorem s07c_fkps_m3c_kn (n : ℕ) :
    Continuous (fun s : ℝ => max 0 (min 1 (min (((n : ℝ) + 2) * (s - 1 / 4) + 1) (((n : ℝ) + 2) * (1 - s) - 1))) *
      (4 * π * max s (1 / 4))⁻¹) ∧
    (∀ s : ℝ, 1 - 1 / ((n : ℝ) + 2) ≤ s →
      max 0 (min 1 (min (((n : ℝ) + 2) * (s - 1 / 4) + 1) (((n : ℝ) + 2) * (1 - s) - 1))) *
        (4 * π * max s (1 / 4))⁻¹ = 0) ∧
    ∀ s : ℝ, |max 0 (min 1 (min (((n : ℝ) + 2) * (s - 1 / 4) + 1) (((n : ℝ) + 2) * (1 - s) - 1))) *
      (4 * π * max s (1 / 4))⁻¹| ≤ π⁻¹ := by
  have hpi := Real.pi_pos
  have hN0 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  refine ⟨?_, fun s hs => ?_, fun s => ?_⟩
  · exact (continuous_const.max (continuous_const.min (((continuous_const.mul
        (continuous_id.sub continuous_const)).add continuous_const).min
        ((continuous_const.mul (continuous_const.sub continuous_id)).sub continuous_const)))).mul
      ((continuous_const.mul (continuous_id.max continuous_const)).inv₀ fun s =>
        (mul_pos (mul_pos four_pos hpi) (lt_max_of_lt_right (by norm_num : (0 : ℝ) < 1 / 4))).ne')
  · have h1 : (1 - s) * ((n : ℝ) + 2) ≤ 1 := (le_div_iff₀ hN0).1 (by linarith)
    rw [max_eq_left ((min_le_right _ _).trans ((min_le_right _ _).trans (by nlinarith))), zero_mul]
  · have h4 : (1 / 4 : ℝ) ≤ max s (1 / 4) := le_max_right _ _
    have h0 : |max 0 (min 1 (min (((n : ℝ) + 2) * (s - 1 / 4) + 1) (((n : ℝ) + 2) * (1 - s) - 1)))| ≤ 1 := by
      rw [abs_of_nonneg (le_max_left _ _)]
      exact max_le zero_le_one (min_le_left _ _)
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (4 * π * max s (1 / 4))⁻¹)]
    calc _ ≤ 1 * (4 * π * (1 / 4))⁻¹ :=
          mul_le_mul h0 (inv_anti₀ (by positivity) (by gcongr)) (by positivity) zero_le_one
      _ = π⁻¹ := by ring

/-- M3c helper: `(4π)⁻¹ log (1 / max(t², 1/4)) = (2π)⁻¹ log (1 / max(t, 1/2))` for `t ≥ 0`. -/
theorem s07c_fkps_m3c_Gconv (t : ℝ) (ht : 0 ≤ t) :
    (4 * π)⁻¹ * Real.log (1 / max (t ^ 2) (1 / 4)) = (2 * π)⁻¹ * Real.log (1 / max t (1 / 2)) := by
  have e : max (t ^ 2) (1 / 4) = (max t (1 / 2)) ^ 2 := by
    rcases le_total t (1 / 2) with h | h
    · rw [max_eq_right h, max_eq_right (by nlinarith)]; norm_num
    · rw [max_eq_left h, max_eq_left (by nlinarith)]
  rw [e, ← one_div_pow, Real.log_pow]
  push_cast
  ring

/-- M3c helper (S2, `ψ = G♭` in Q): `∫_𝔻 ⟨g + V, g⟩ G♭ = -∫_{𝔻 \ B(0,1/2)} u ⟨g + V, -Y/(2π|Y|²)⟩`. -/
theorem s07c_fkps_m3c_S2 (u : ℂ → ℝ) (g V : ℂ → ℂ) (hu : ContinuousOn u (closedBall 0 1))
    (hg : AEMeasurable g) (hV : AEMeasurable V)
    (hg2 : ∫⁻ z in unitDisc, ‖g z‖ₑ ^ 2 < ⊤) (hV2 : ∫⁻ z in unitDisc, ‖V z‖ₑ ^ 2 < ⊤)
    (hP2 : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
      ∫ z, (u z : ℂ) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I) =
        -∫ z, (φ z : ℂ) * g z)
    (hP4 : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
      ∫ z, (conj (g z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re =
        -∫ z, (conj (V z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re) :
    ∫ Y in unitDisc, (conj (g Y + V Y) * g Y).re * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2))) =
      -∫ Y in unitDisc \ ball 0 (1 / 2), u Y * (conj (g Y + V Y) * (-Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re := by
  have hpi := Real.pi_pos
  have hh : AEMeasurable (fun z => g z + V z) := hg.add hV
  have hh2 := s07c_fkps_m3c_l2_add g V hg hg2 hV2
  have hh1 : ∫⁻ z in unitDisc, ‖g z + V z‖ₑ < ⊤ :=
    s07c_fkps_m3b_l1_of_l2 (fun z => g z + V z) unitDisc measure_ball_lt_top.ne hh2
  have hhI : Integrable (fun z => (conj (g z + V z) * g z).re) (volume.restrict unitDisc) := by
    have := s07c_fkps_m3c_int (unitDisc.indicator fun _ => (1 : ℝ))
      (aestronglyMeasurable_const.indicator measurableSet_ball) 1
      (fun z hz => by rw [indicator_of_mem hz]; norm_num) (fun z => g z + V z) g hh hg hh2 hg2
      (fun z hz => by rw [indicator_of_notMem hz, zero_mul])
    have e : (fun z => unitDisc.indicator (fun _ => (1 : ℝ)) z * (conj (g z + V z) * g z).re) =
        unitDisc.indicator (fun z => (conj (g z + V z) * g z).re) := funext fun z => by
      by_cases hz : z ∈ unitDisc
      · rw [indicator_of_mem hz, indicator_of_mem hz, one_mul]
      · rw [indicator_of_notMem hz, indicator_of_notMem hz, zero_mul]
    rw [e] at this
    exact (integrable_indicator_iff (s := unitDisc) measurableSet_ball).1 this
  obtain ⟨Mu, hMu⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hu
  have hMu0 : 0 ≤ Mu := (norm_nonneg _).trans (hMu 0 (mem_closedBall_self zero_le_one))
  have hum : AEStronglyMeasurable u (volume.restrict unitDisc) :=
    (hu.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
  have haI : Integrable (fun z => ‖g z + V z‖) (volume.restrict unitDisc) :=
    ⟨hh.aestronglyMeasurable.norm.restrict, by
      show ∫⁻ z in unitDisc, ‖‖g z + V z‖‖ₑ < ⊤
      simpa only [enorm_norm] using hh1⟩
  set K : ℕ → ℝ → ℝ := fun n s =>
    max 0 (min 1 (min (((n : ℝ) + 2) * (s - 1 / 4) + 1) (((n : ℝ) + 2) * (1 - s) - 1))) *
      (4 * π * max s (1 / 4))⁻¹ with hKdef
  have hrad := fun n : ℕ => s07c_fkps_m3c_radial (K n) (s07c_fkps_m3c_kn n).1 ((n : ℝ) + 2)
    (by linarith [n.cast_nonneg (α := ℝ)]) (s07c_fkps_m3c_kn n).2.1 π⁻¹ (s07c_fkps_m3c_kn n).2.2
  have hK0 : ∀ n : ℕ, ∀ z : ℂ, z ∉ unitDisc → K n (‖z‖ ^ 2) = 0 := fun n z hz => by
    have h1 : 1 ≤ ‖z‖ := not_lt.1 fun h => hz (mem_ball_zero_iff.2 h)
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    exact (s07c_fkps_m3c_kn n).2.1 _ (by nlinarith)
  have key : ∀ n : ℕ, ∫ z in unitDisc, (∫ s in ‖z‖ ^ 2..1, K n s) * (conj (g z + V z) * g z).re =
      -∫ z in unitDisc, u z * (conj (g z + V z) * (((-2 * K n (‖z‖ ^ 2) : ℝ) : ℂ) * z)).re := by
    intro n
    obtain ⟨h1, h2, h3, h4, -, h6⟩ := hrad n
    have hR : 1 - 1 / (4 * ((n : ℝ) + 2)) < 1 := by
      have : 0 < 1 / (4 * ((n : ℝ) + 2)) := by positivity
      linarith
    have hQ := s07c_fkps_m3c_Q u g V hu hg hV hg2 hV2 hP2 hP4 _ h1 h2 _ hR h3
    simp_rw [h4] at hQ
    have eL : ∫ z in unitDisc, (∫ s in ‖z‖ ^ 2..1, K n s) * (conj (g z + V z) * g z).re =
        ∫ z, (∫ s in ‖z‖ ^ 2..1, K n s) * (conj (g z + V z) * g z).re :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        rw [h6 z (not_lt.1 fun h => hz (mem_ball_zero_iff.2 h)), zero_mul]
    have eR : ∫ z in unitDisc, u z * (conj (g z + V z) * (((-2 * K n (‖z‖ ^ 2) : ℝ) : ℂ) * z)).re =
        ∫ z, u z * (conj (g z + V z) * (((-2 * K n (‖z‖ ^ 2) : ℝ) : ℂ) * z)).re :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        rw [hK0 n z hz]; simp
    rw [eL, eR]
    exact hQ
  have hL : Tendsto (fun n : ℕ => ∫ z in unitDisc, (∫ s in ‖z‖ ^ 2..1, K n s) * (conj (g z + V z) * g z).re)
      atTop (𝓝 (∫ Y in unitDisc, (conj (g Y + V Y) * g Y).re * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2))))) := by
    refine tendsto_integral_of_dominated_convergence (fun z => π⁻¹ * ‖(conj (g z + V z) * g z).re‖)
      (fun n => ?_) (hhI.norm.const_mul _) (fun n => ?_) ?_
    · exact (hrad n).1.continuous.aestronglyMeasurable.mul hhI.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun z hz => ?_)
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right ((hrad n).2.2.2.2.1 z (mem_ball_zero_iff.1 hz)) (norm_nonneg _)
    · refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun z hz => ?_)
      have hz1 : ‖z‖ ^ 2 < 1 := by
        have := mem_ball_zero_iff.1 hz
        nlinarith [norm_nonneg z]
      have := (s07c_fkps_m3c_Phi _ hz1).mul_const ((conj (g z + V z) * g z).re)
      rw [s07c_fkps_m3c_Gconv _ (norm_nonneg z)] at this
      rw [mul_comm ((conj (g z + V z) * g z).re)]
      exact this
  have hR : Tendsto (fun n : ℕ => ∫ z in unitDisc,
      u z * (conj (g z + V z) * (((-2 * K n (‖z‖ ^ 2) : ℝ) : ℂ) * z)).re) atTop
      (𝓝 (∫ Y in unitDisc \ ball 0 (1 / 2), u Y * (conj (g Y + V Y) * (-Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re)) := by
    rw [diff_eq, ← setIntegral_indicator measurableSet_ball.compl]
    refine tendsto_integral_of_dominated_convergence (fun z => Mu * (2 * π⁻¹) * ‖g z + V z‖)
      (fun n => ?_) (haI.const_mul _) (fun n => ?_) ?_
    · have hc : Continuous (fun z : ℂ => ((-2 * K n (‖z‖ ^ 2) : ℝ) : ℂ) * z) :=
        (Complex.continuous_ofReal.comp (continuous_const.mul
          ((s07c_fkps_m3c_kn n).1.comp (continuous_norm.pow 2)))).mul continuous_id
      exact hum.mul (Complex.continuous_re.comp_aestronglyMeasurable
        ((Complex.continuous_conj.comp_aestronglyMeasurable hh.aestronglyMeasurable.restrict).mul
          hc.aestronglyMeasurable))
    · refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun z hz => ?_)
      have hu' : ‖u z‖ ≤ Mu := hMu z (ball_subset_closedBall hz)
      have hz' : ‖z‖ ≤ 1 := (mem_ball_zero_iff.1 hz).le
      have hk : |-2 * K n (‖z‖ ^ 2)| ≤ 2 * π⁻¹ := by
        have := (s07c_fkps_m3c_kn n).2.2 (‖z‖ ^ 2)
        calc |-2 * K n (‖z‖ ^ 2)| = 2 * |K n (‖z‖ ^ 2)| := by rw [abs_mul]; norm_num
          _ ≤ 2 * π⁻¹ := by linarith
      have hc : ‖((-2 * K n (‖z‖ ^ 2) : ℝ) : ℂ) * z‖ ≤ 2 * π⁻¹ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc _ ≤ 2 * π⁻¹ * 1 := mul_le_mul hk hz' (norm_nonneg _) (by positivity)
          _ = _ := mul_one _
      have hre : ‖(conj (g z + V z) * (((-2 * K n (‖z‖ ^ 2) : ℝ) : ℂ) * z)).re‖ ≤
          ‖g z + V z‖ * (2 * π⁻¹) := by
        rw [Real.norm_eq_abs]
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_left hc (norm_nonneg _)
      rw [norm_mul]
      calc _ ≤ Mu * (‖g z + V z‖ * (2 * π⁻¹)) := mul_le_mul hu' hre (norm_nonneg _) hMu0
        _ = _ := by ring
    · refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun z hz => ?_)
      have hzn := mem_ball_zero_iff.1 hz
      refine tendsto_const_nhds.congr' ((s07c_fkps_m3c_sig (‖z‖ ^ 2)).mono fun n hn => ?_)
      have hK : K n (‖z‖ ^ 2) = (Ico (1 / 4 : ℝ) 1).indicator 1 (‖z‖ ^ 2) * (4 * π * max (‖z‖ ^ 2) (1 / 4))⁻¹ := by
        rw [hKdef]; beta_reduce; rw [hn]
      beta_reduce
      rw [hK]
      by_cases hz2 : z ∈ ball (0 : ℂ) (1 / 2)
      · have h2 := mem_ball_zero_iff.1 hz2
        rw [indicator_of_notMem (show z ∉ (ball (0 : ℂ) (1 / 2))ᶜ from fun h => h hz2),
          indicator_of_notMem (show ‖z‖ ^ 2 ∉ Ico (1 / 4 : ℝ) 1 from fun h => by
            have := h.1; nlinarith [norm_nonneg z])]
        simp
      · have h2 : 1 / 2 ≤ ‖z‖ := not_lt.1 fun h => hz2 (mem_ball_zero_iff.2 h)
        have h4 : 1 / 4 ≤ ‖z‖ ^ 2 := by nlinarith
        rw [indicator_of_mem (show z ∈ (ball (0 : ℂ) (1 / 2))ᶜ from hz2),
          indicator_of_mem (show ‖z‖ ^ 2 ∈ Ico (1 / 4 : ℝ) 1 from ⟨h4, by nlinarith [norm_nonneg z]⟩),
          Pi.one_apply, one_mul, max_eq_left h4]
        have hn0 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith)
        have hp0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpi.ne'
        have e : -z / ((2 * π * ‖z‖ ^ 2 : ℝ) : ℂ) = ((-2 * (4 * π * ‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * z := by
          push_cast
          field_simp
          ring
        rw [e]
  have hlim := tendsto_nhds_unique hL ((hR.neg).congr fun n => (key n).symm)
  exact hlim

/-- M3c helper (P, the polar identity): for `C¹` `w` and `0 < a ≤ b`,
`∫_{B(0,b) \ B(0,a)} w ⟨∇w, Y/(2π|Y|²)⟩ = ∫₀^{2π} ((4π)⁻¹ w(b e^{it})² - (4π)⁻¹ w(a e^{it})²) dt`. -/
theorem s07c_fkps_m3c_polar (w : ℂ → ℝ) (hw : ContDiff ℝ 1 w) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ Y in ball (0 : ℂ) b \ ball 0 a, w Y * (conj (((fderiv ℝ w Y 1 : ℝ) : ℂ) + ((fderiv ℝ w Y I : ℝ) : ℂ) * I) *
      (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re =
    ∫ t in (0 : ℝ)..2 * π, ((4 * π)⁻¹ * w ((b : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2 -
      (4 * π)⁻¹ * w ((a : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2) := by
  have hpi := Real.pi_pos
  set F : ℂ → ℝ := fun Y => w Y * (conj (((fderiv ℝ w Y 1 : ℝ) : ℂ) + ((fderiv ℝ w Y I : ℝ) : ℂ) * I) *
    (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re with hFdef
  set E : ℝ → ℂ := fun θ => Complex.exp ((θ : ℂ) * I) with hEdef
  set H : ℝ × ℝ → ℝ := fun p =>
    (2 * π)⁻¹ * (w ((p.1 : ℂ) * E p.2) * fderiv ℝ w ((p.1 : ℂ) * E p.2) (E p.2)) with hHdef
  have hEc : Continuous E := Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hdw : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  have hφc : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * E p.2) :=
    (Complex.continuous_ofReal.comp continuous_fst).mul (hEc.comp continuous_snd)
  have hHc : Continuous H := continuous_const.mul ((hw.continuous.comp hφc).mul
    ((hdw.comp hφc).clm_apply (hEc.comp continuous_snd)))
  have hnE : ∀ r θ : ℝ, 0 < r → ‖(r : ℂ) * E θ‖ = r := fun r θ hr => by
    show ‖(r : ℂ) * Complex.exp ((θ : ℂ) * I)‖ = r
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hE : ∀ θ : ℝ, E θ = (Real.cos θ : ℝ) • (1 : ℂ) + (Real.sin θ : ℝ) • I := fun θ => by
    show Complex.exp ((θ : ℂ) * I) = _
    rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
  have hkey : ∀ r θ : ℝ, 0 < r → r * F ((r : ℂ) * E θ) = H (r, θ) := by
    intro r θ hr
    have hD : ∀ P : ℂ, fderiv ℝ w P (E θ) =
        Real.cos θ * fderiv ℝ w P 1 + Real.sin θ * fderiv ℝ w P I := fun P => by
      rw [hE, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
    have hp0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpi.ne'
    have hre : ∀ D1 D2 : ℝ, (conj ((D1 : ℂ) + (D2 : ℂ) * I) * ((r : ℂ) * E θ / ((2 * π * r ^ 2 : ℝ) : ℂ))).re =
        (Real.cos θ * D1 + Real.sin θ * D2) / (2 * π * r) := fun D1 D2 => by
      have e : (r : ℂ) * E θ / ((2 * π * r ^ 2 : ℝ) : ℂ) =
          ((Real.cos θ / (2 * π * r) : ℝ) : ℂ) + ((Real.sin θ / (2 * π * r) : ℝ) : ℂ) * I := by
        rw [hE, Complex.real_smul, Complex.real_smul]
        push_cast
        field_simp
      rw [e]
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    simp only [hFdef, hHdef]
    rw [hnE r θ hr, hre, hD]
    field_simp
  have hmem : ∀ r θ : ℝ, 0 < r → ((r : ℂ) * E θ ∈ ball (0 : ℂ) b \ ball 0 a ↔ r ∈ Ico a b) := fun r θ hr => by
    rw [Set.mem_sdiff, mem_ball_zero_iff, mem_ball_zero_iff, hnE r θ hr, mem_Ico, not_lt, and_comm]
  have hA : MeasurableSet (ball (0 : ℂ) b \ ball 0 a) := measurableSet_ball.diff measurableSet_ball
  have hsymm : ∀ p : ℝ × ℝ, Complex.polarCoord.symm p = (p.1 : ℂ) * E p.2 := fun p => by
    rw [Complex.polarCoord_symm_apply]
    show _ = (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I)
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hbox : IntegrableOn (fun z : ℝ × ℝ => H z.swap) (Ioo (-π) π ×ˢ Ico a b) :=
    ((hHc.comp continuous_swap).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioo_subset_Icc_self Ico_subset_Icc_self)
  have hper : Function.Periodic (fun θ : ℝ =>
      (4 * π)⁻¹ * w ((b : ℂ) * E θ) ^ 2 - (4 * π)⁻¹ * w ((a : ℂ) * E θ) ^ 2) (2 * π) := by
    intro θ
    have e : E (θ + 2 * π) = E θ := by
      show Complex.exp (((θ + 2 * π : ℝ) : ℂ) * I) = Complex.exp ((θ : ℂ) * I)
      have := Complex.exp_mul_I_periodic (θ : ℂ)
      push_cast
      exact this
    simp only [e]
  have hpp := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at hpp
  calc ∫ Y in ball (0 : ℂ) b \ ball 0 a, F Y = ∫ Y, (ball (0 : ℂ) b \ ball 0 a).indicator F Y :=
        (integral_indicator hA).symm
    _ = ∫ p in polarCoord.target, p.1 • (ball (0 : ℂ) b \ ball 0 a).indicator F (Complex.polarCoord.symm p) :=
        (Complex.integral_comp_polarCoord_symm _).symm
    _ = ∫ p in polarCoord.target, (Ico a b ×ˢ (univ : Set ℝ)).indicator H p := by
        refine setIntegral_congr_fun polarCoord.open_target.measurableSet fun p hp => ?_
        have hp' : p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π := hp
        have hp1 : 0 < p.1 := hp'.1
        rw [hsymm, smul_eq_mul]
        by_cases hr : p.1 ∈ Ico a b
        · rw [indicator_of_mem ((hmem p.1 p.2 hp1).2 hr),
            indicator_of_mem (show p ∈ Ico a b ×ˢ (univ : Set ℝ) from ⟨hr, trivial⟩)]
          exact hkey p.1 p.2 hp1
        · rw [indicator_of_notMem (fun h => hr ((hmem p.1 p.2 hp1).1 h)),
            indicator_of_notMem (show p ∉ Ico a b ×ˢ (univ : Set ℝ) from fun h => hr h.1), mul_zero]
    _ = ∫ p in Ico a b ×ˢ Ioo (-π) π, H p := by
        have e : polarCoord.target ∩ Ico a b ×ˢ (univ : Set ℝ) = Ico a b ×ˢ Ioo (-π) π := by
          show Ioi (0 : ℝ) ×ˢ Ioo (-π) π ∩ Ico a b ×ˢ (univ : Set ℝ) = _
          rw [prod_inter_prod, inter_univ,
            inter_eq_right.2 fun x hx => mem_Ioi.2 (lt_of_lt_of_le ha (mem_Ico.1 hx).1)]
        rw [setIntegral_indicator (measurableSet_Ico.prod MeasurableSet.univ), e]
    _ = ∫ p in Ioo (-π) π ×ˢ Ico a b, H p.swap := (setIntegral_prod_swap _ _ _).symm
    _ = ∫ θ in Ioo (-π) π, ∫ r in Ico a b, H (r, θ) := setIntegral_prod _ hbox
    _ = ∫ θ in Ioo (-π) π, ((4 * π)⁻¹ * w ((b : ℂ) * E θ) ^ 2 - (4 * π)⁻¹ * w ((a : ℂ) * E θ) ^ 2) := by
        refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
        have hd : ∀ r : ℝ, HasDerivAt (fun r : ℝ => (4 * π)⁻¹ * w ((r : ℂ) * E θ) ^ 2) (H (r, θ)) r := by
          intro r
          have hl : HasDerivAt (fun r : ℝ => (r : ℂ) * E θ) (E θ) r := by
            simpa using ((hasDerivAt_id r).ofReal_comp).mul_const (E θ)
          have hc := ((hw.differentiable one_ne_zero) ((r : ℂ) * E θ)).hasFDerivAt.comp_hasDerivAt r hl
          have := (hc.pow 2).const_mul (4 * π)⁻¹
          refine this.congr_deriv ?_
          show _ = (2 * π)⁻¹ * (w ((r : ℂ) * E θ) * fderiv ℝ w ((r : ℂ) * E θ) (E θ))
          rw [Function.comp_apply]
          push_cast
          ring
        rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
            ((hHc.comp (Continuous.prodMk_left θ)).intervalIntegrable a b)]
    _ = _ := by
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith), hpp]

/-- M3c helper (S3b, the polar identity for `u` on `B(0,b) \ B(0,1/2)`, `b < 1`): mollify (P) and let the
mollification parameter tend to `0`. -/
theorem s07c_fkps_m3c_S3b (u : ℂ → ℝ) (g : ℂ → ℂ) (hu : ContinuousOn u (closedBall 0 1))
    (hg : AEMeasurable g) (hg2 : ∫⁻ z in unitDisc, ‖g z‖ₑ ^ 2 < ⊤)
    (hP2 : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
      ∫ z, (u z : ℂ) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I) =
        -∫ z, (φ z : ℂ) * g z)
    (b : ℝ) (hb2 : 1 / 2 ≤ b) (hb1 : b < 1) :
    ∫ Y in ball (0 : ℂ) b \ ball 0 (1 / 2), u Y * (conj (g Y) * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re =
      ∫ t in (0 : ℝ)..2 * π, ((4 * π)⁻¹ * u ((b : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2 -
        (4 * π)⁻¹ * u (((1 / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2) := by
  have hpi := Real.pi_pos
  have hb0 : 0 ≤ b := by linarith
  have hA : MeasurableSet (ball (0 : ℂ) b \ ball 0 (1 / 2)) := measurableSet_ball.diff measurableSet_ball
  have hAD : ball (0 : ℂ) b \ ball 0 (1 / 2) ⊆ unitDisc := fun Y hY => ball_subset_ball hb1.le hY.1
  have hAb : ball (0 : ℂ) b \ ball 0 (1 / 2) ⊆ closedBall 0 b := fun Y hY => ball_subset_closedBall hY.1
  have hZm : Measurable (fun Y : ℂ => Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ)) :=
    measurable_id.div (Complex.measurable_ofReal.comp ((continuous_const.mul (continuous_norm.pow 2)).measurable))
  have hreb : ∀ Y ∈ ball (0 : ℂ) b \ ball 0 (1 / 2), ∀ a : ℂ,
      ‖(conj a * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re‖ ≤ ‖a‖ * π⁻¹ := by
    intro Y hY a
    have h2 : 1 / 2 ≤ ‖Y‖ := not_lt.1 fun h => hY.2 (mem_ball_zero_iff.2 h)
    have hY0 : 0 < ‖Y‖ := by linarith
    rw [Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), div_le_iff₀ (by positivity),
      show π⁻¹ * (2 * π * ‖Y‖ ^ 2) = 2 * ‖Y‖ ^ 2 * (π⁻¹ * π) by ring, inv_mul_cancel₀ hpi.ne', mul_one]
    nlinarith [mul_nonneg hY0.le (by linarith : (0 : ℝ) ≤ 2 * ‖Y‖ - 1)]
  obtain ⟨Mu, hMu⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hu
  have hMu0 : 0 ≤ Mu := (norm_nonneg _).trans (hMu 0 (mem_closedBall_self zero_le_one))
  have hub : ∀ Y ∈ closedBall (0 : ℂ) b, |u Y| ≤ Mu := fun Y hY => by
    have := hMu Y (closedBall_subset_closedBall hb1.le hY)
    rwa [Real.norm_eq_abs] at this
  have hg1 : ∫⁻ z in unitDisc, ‖g z‖ₑ < ⊤ := s07c_fkps_m3b_l1_of_l2 g unitDisc measure_ball_lt_top.ne hg2
  have hgA : Integrable (fun z => ‖g z‖) (volume.restrict (ball (0 : ℂ) b \ ball 0 (1 / 2))) :=
    ⟨hg.aestronglyMeasurable.norm.restrict, by
      show ∫⁻ z in ball (0 : ℂ) b \ ball 0 (1 / 2), ‖‖g z‖‖ₑ < ⊤
      simp only [enorm_norm]
      exact lt_of_le_of_lt (lintegral_mono_set hAD) hg1⟩
  have hum : AEStronglyMeasurable u (volume.restrict (ball (0 : ℂ) b \ ball 0 (1 / 2))) :=
    (hu.mono (hAD.trans ball_subset_closedBall)).aestronglyMeasurable hA
  have iX : Integrable (fun Y => u Y * (conj (g Y) * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re)
      (volume.restrict (ball (0 : ℂ) b \ ball 0 (1 / 2))) := by
    refine Integrable.mono' (hgA.const_mul (Mu * π⁻¹)) (hum.mul (Complex.continuous_re.comp_aestronglyMeasurable
      ((Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable.restrict).mul
        hZm.aestronglyMeasurable))) ((ae_restrict_iff' hA).2 (Eventually.of_forall fun Y hY => ?_))
    rw [norm_mul, Real.norm_eq_abs (u Y)]
    calc _ ≤ Mu * (‖g Y‖ * π⁻¹) := mul_le_mul (hub Y (hAb hY)) (hreb Y hY _) (norm_nonneg _) hMu0
      _ = Mu * π⁻¹ * ‖g Y‖ := by ring
  have hcirc : ∀ c : ℝ, 0 ≤ c → c ≤ b → ∀ t : ℝ,
      (c : ℂ) * Complex.exp ((t : ℂ) * I) ∈ closedBall (0 : ℂ) b := fun c hc0 hcb t => by
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hc0]
    exact hcb
  have hEc : Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * I)) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hcont : ∀ v : ℂ → ℝ, ContinuousOn v (closedBall 0 b) → ∀ c : ℝ, 0 ≤ c → c ≤ b →
      Continuous (fun t : ℝ => v ((c : ℂ) * Complex.exp ((t : ℂ) * I))) := fun v hv c hc0 hcb =>
    hv.comp_continuous (continuous_const.mul hEc) (hcirc c hc0 hcb)
  have hub' : ContinuousOn u (closedBall 0 b) := hu.mono (closedBall_subset_closedBall hb1.le)
  have hfc : ∀ v : ℂ → ℝ, ContinuousOn v (closedBall 0 b) →
      Continuous (fun t : ℝ => (4 * π)⁻¹ * v ((b : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2 -
        (4 * π)⁻¹ * v (((1 / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2) := fun v hv =>
    (continuous_const.mul ((hcont v hv b hb0 le_rfl).pow 2)).sub
      (continuous_const.mul ((hcont v hv _ (by norm_num) hb2).pow 2))
  set Xu := ∫ Y in ball (0 : ℂ) b \ ball 0 (1 / 2), u Y * (conj (g Y) * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re
    with hXu
  set Ru := ∫ t in (0 : ℝ)..2 * π, ((4 * π)⁻¹ * u ((b : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2 -
        (4 * π)⁻¹ * u (((1 / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2) with hRu
  set T0 : ℝ≥0∞ := ENNReal.ofReal π⁻¹ * (∫⁻ z in unitDisc, ‖g z‖ₑ) +
    ENNReal.ofReal ((Mu + 1) * π⁻¹) * (volume unitDisc + 1) + ENNReal.ofReal (2 * Mu + 1) with hT0
  have hT0t : T0 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg1.ne, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.2 ⟨measure_ball_lt_top.ne, ENNReal.one_ne_top⟩)⟩, ENNReal.ofReal_ne_top⟩
  have key : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ‖Xu - Ru‖ₑ ≤ ENNReal.ofReal (Real.sqrt δ) * T0 := by
    intro δ hδ hδ1
    set T : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt δ) with hT
    have hsq : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
    have hT0' : T ≠ 0 := by rw [hT, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hsq
    have hTt : T ≠ ⊤ := ENNReal.ofReal_ne_top
    have hδT : ENNReal.ofReal δ = T * T := by
      rw [hT, ← ENNReal.ofReal_mul hsq.le, Real.mul_self_sqrt hδ.le]
    have hTδ : T⁻¹ * ENNReal.ofReal δ = T := by
      rw [hδT, ← mul_assoc, ENNReal.inv_mul_cancel hT0' hTt, one_mul]
    have hδT' : ENNReal.ofReal δ ≤ T := by
      rw [hT]; refine ENNReal.ofReal_le_ofReal ?_
      calc δ = Real.sqrt δ * Real.sqrt δ := (Real.mul_self_sqrt hδ.le).symm
        _ ≤ Real.sqrt δ * 1 := by
            gcongr; rw [Real.sqrt_le_one]; exact hδ1
        _ = Real.sqrt δ := mul_one _
    obtain ⟨w, hw, hwu, hwg⟩ := s07c_fkps_m3c_moll u g hu hg hg2 hP2 b hb1 δ hδ
    set Gw : ℂ → ℂ := fun z => ((fderiv ℝ w z 1 : ℝ) : ℂ) + ((fderiv ℝ w z I : ℝ) : ℂ) * I with hGw
    have hP : ∫ Y in ball (0 : ℂ) b \ ball 0 (1 / 2), w Y * (conj (Gw Y) * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re =
        ∫ t in (0 : ℝ)..2 * π, ((4 * π)⁻¹ * w ((b : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2 -
          (4 * π)⁻¹ * w (((1 / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2) :=
      s07c_fkps_m3c_polar w hw (1 / 2) b (by norm_num) hb2
    have hdw : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
    have hGwc : Continuous Gw :=
      (Complex.continuous_ofReal.comp (hdw.clm_apply continuous_const)).add
        ((Complex.continuous_ofReal.comp (hdw.clm_apply continuous_const)).mul continuous_const)
    have hwb : ∀ Y ∈ closedBall (0 : ℂ) b, |w Y| ≤ Mu + 1 := fun Y hY => by
      have h1 := hwu Y hY
      have h2 := hub Y hY
      have h3 := abs_sub_abs_le_abs_sub (w Y) (u Y)
      linarith
    have hGA : Integrable (fun z => ‖Gw z‖) (volume.restrict (ball (0 : ℂ) b \ ball 0 (1 / 2))) :=
      (hGwc.norm.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) b)).mono_set hAb
    have iW : Integrable (fun Y => w Y * (conj (Gw Y) * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re)
        (volume.restrict (ball (0 : ℂ) b \ ball 0 (1 / 2))) := by
      refine Integrable.mono' (hGA.const_mul ((Mu + 1) * π⁻¹)) (hw.continuous.aestronglyMeasurable.mul
        (Complex.continuous_re.comp_aestronglyMeasurable
          ((Complex.continuous_conj.comp hGwc).aestronglyMeasurable.mul hZm.aestronglyMeasurable)))
        ((ae_restrict_iff' hA).2 (Eventually.of_forall fun Y hY => ?_))
      rw [norm_mul, Real.norm_eq_abs (w Y)]
      calc _ ≤ (Mu + 1) * (‖Gw Y‖ * π⁻¹) :=
            mul_le_mul (hwb Y (hAb hY)) (hreb Y hY _) (norm_nonneg _) (by linarith)
        _ = _ := by ring
    -- the area term
    have hX : ‖Xu - ∫ Y in ball (0 : ℂ) b \ ball 0 (1 / 2),
        w Y * (conj (Gw Y) * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re‖ₑ ≤
        T * (ENNReal.ofReal π⁻¹ * (∫⁻ z in unitDisc, ‖g z‖ₑ) +
          ENNReal.ofReal ((Mu + 1) * π⁻¹) * (volume unitDisc + 1)) := by
      rw [hXu, ← integral_sub iX iW]
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      have hpt : ∀ Y ∈ ball (0 : ℂ) b \ ball 0 (1 / 2),
          ‖u Y * (conj (g Y) * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re -
            w Y * (conj (Gw Y) * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re‖ₑ ≤
          ENNReal.ofReal (δ * π⁻¹) * ‖g Y‖ₑ +
            ENNReal.ofReal ((Mu + 1) * π⁻¹) * (T * 1 ^ 2 + T⁻¹ * ‖Gw Y - g Y‖ₑ ^ 2) := by
        intro Y hY
        have e : u Y * (conj (g Y) * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re -
            w Y * (conj (Gw Y) * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re =
            (u Y - w Y) * (conj (g Y) * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re +
              w Y * (conj (g Y - Gw Y) * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re := by
          simp only [map_sub, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
          ring
        have hr : ‖(u Y - w Y) * (conj (g Y) * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re +
            w Y * (conj (g Y - Gw Y) * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re‖ ≤
            δ * π⁻¹ * ‖g Y‖ + (Mu + 1) * π⁻¹ * ‖Gw Y - g Y‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul, Real.norm_eq_abs (u Y - w Y), abs_sub_comm]
            calc _ ≤ δ * (‖g Y‖ * π⁻¹) := mul_le_mul (hwu Y (hAb hY)) (hreb Y hY _) (norm_nonneg _) hδ.le
              _ = _ := by ring
          · rw [norm_mul, Real.norm_eq_abs (w Y)]
            calc _ ≤ (Mu + 1) * (‖g Y - Gw Y‖ * π⁻¹) :=
                  mul_le_mul (hwb Y (hAb hY)) (hreb Y hY _) (norm_nonneg _) (by linarith)
              _ = _ := by rw [norm_sub_rev]; ring
        rw [e, ← ofReal_norm]
        refine (ENNReal.ofReal_le_ofReal hr).trans ?_
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (p := δ * π⁻¹) (by positivity),
          ENNReal.ofReal_mul (p := (Mu + 1) * π⁻¹) (by positivity), ofReal_norm, ofReal_norm]
        gcongr
        have := s07c_fkps_m3b_amgm 1 ‖Gw Y - g Y‖ₑ T hT0' hTt
        rwa [one_mul] at this
      refine (setLIntegral_mono' hA hpt).trans ?_
      have hm1 : AEMeasurable (fun Y => ENNReal.ofReal (δ * π⁻¹) * ‖g Y‖ₑ)
          (volume.restrict (ball (0 : ℂ) b \ ball 0 (1 / 2))) := (aemeasurable_const.mul hg.enorm).restrict
      rw [lintegral_add_left' hm1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' aemeasurable_const,
        setLIntegral_const, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hT0')]
      have hA1 : ∫⁻ z in ball (0 : ℂ) b \ ball 0 (1 / 2), ‖g z‖ₑ ≤ ∫⁻ z in unitDisc, ‖g z‖ₑ :=
        lintegral_mono_set hAD
      have hA2 : volume (ball (0 : ℂ) b \ ball 0 (1 / 2)) ≤ volume unitDisc := measure_mono hAD
      have hA3 : ∫⁻ z in ball (0 : ℂ) b \ ball 0 (1 / 2), ‖Gw z - g z‖ₑ ^ 2 ≤ ENNReal.ofReal δ :=
        (lintegral_mono_set diff_subset).trans hwg
      rw [ENNReal.ofReal_mul hδ.le]
      calc _ ≤ T * ENNReal.ofReal π⁻¹ * (∫⁻ z in unitDisc, ‖g z‖ₑ) +
            ENNReal.ofReal ((Mu + 1) * π⁻¹) * (T * 1 ^ 2 * volume unitDisc + T⁻¹ * ENNReal.ofReal δ) := by
            gcongr
        _ = _ := by rw [hTδ]; ring
    -- the boundary term
    have hR : ‖Ru - ∫ t in (0 : ℝ)..2 * π, ((4 * π)⁻¹ * w ((b : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2 -
        (4 * π)⁻¹ * w (((1 / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2)‖ ≤ δ * (2 * Mu + 1) := by
      have hsq2 : ∀ Y ∈ closedBall (0 : ℂ) b, |u Y ^ 2 - w Y ^ 2| ≤ δ * (2 * Mu + 1) := fun Y hY => by
        rw [sq_sub_sq, abs_mul, mul_comm]
        have h1 : |u Y - w Y| ≤ δ := by rw [abs_sub_comm]; exact hwu Y hY
        have h2 := hub Y hY
        have h3 := hwb Y hY
        have h4 : |u Y + w Y| ≤ 2 * Mu + 1 := abs_le.2
          ⟨by linarith [(abs_le.1 h2).1, (abs_le.1 h3).1], by linarith [(abs_le.1 h2).2, (abs_le.1 h3).2]⟩
        exact mul_le_mul h1 h4 (abs_nonneg _) hδ.le
      rw [hRu, ← intervalIntegral.integral_sub ((hfc u hub').intervalIntegrable _ _)
        ((hfc w hw.continuous.continuousOn).intervalIntegrable _ _)]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := (4 * π)⁻¹ * (2 * (δ * (2 * Mu + 1)))) fun t _ => ?_).trans (le_of_eq ?_)
      · have e : (4 * π)⁻¹ * u ((b : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2 -
            (4 * π)⁻¹ * u (((1 / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2 -
            ((4 * π)⁻¹ * w ((b : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2 -
              (4 * π)⁻¹ * w (((1 / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2) =
            (4 * π)⁻¹ * ((u ((b : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2 - w ((b : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2) -
              (u (((1 / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2 -
                w (((1 / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2)) := by ring
        rw [e, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
        have k1 := hsq2 _ (hcirc b hb0 le_rfl t)
        have k2 := hsq2 _ (hcirc _ (by norm_num) hb2 t)
        gcongr
        exact abs_le.2 ⟨by linarith [(abs_le.1 k1).1, (abs_le.1 k2).2], by linarith [(abs_le.1 k1).2, (abs_le.1 k2).1]⟩
      · rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
          show (4 * π)⁻¹ * (2 * (δ * (2 * Mu + 1))) * (2 * π) = δ * (2 * Mu + 1) * ((4 * π)⁻¹ * (4 * π)) by ring,
          inv_mul_cancel₀ (by positivity), mul_one]
    have hR' : ‖Ru - ∫ t in (0 : ℝ)..2 * π, ((4 * π)⁻¹ * w ((b : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2 -
        (4 * π)⁻¹ * w (((1 / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2)‖ₑ ≤ T * ENNReal.ofReal (2 * Mu + 1) := by
      rw [← ofReal_norm]
      refine (ENNReal.ofReal_le_ofReal hR).trans ?_
      rw [ENNReal.ofReal_mul hδ.le]
      gcongr
    rw [show Xu - Ru = (Xu - ∫ Y in ball (0 : ℂ) b \ ball 0 (1 / 2),
        w Y * (conj (Gw Y) * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re) -
        (Ru - ∫ t in (0 : ℝ)..2 * π, ((4 * π)⁻¹ * w ((b : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2 -
          (4 * π)⁻¹ * w (((1 / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2)) by rw [hP]; ring]
    refine enorm_sub_le.trans ?_
    rw [hT0, mul_add]
    exact add_le_add hX hR'
  have hlim : Tendsto (fun δ : ℝ => ENNReal.ofReal (Real.sqrt δ) * T0) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun δ : ℝ => ENNReal.ofReal (Real.sqrt δ)) (𝓝[>] 0) (𝓝 0) := by
      have := ((ENNReal.continuous_ofReal.comp Real.continuous_sqrt).tendsto 0)
      simp only [Function.comp_def, Real.sqrt_zero, ENNReal.ofReal_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    have := ENNReal.Tendsto.mul_const h1 (Or.inr hT0t)
    rwa [zero_mul] at this
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ‖Xu - Ru‖ₑ ≤ ENNReal.ofReal (Real.sqrt δ) * T0 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
    exact key δ hδ.1 hδ.2.le
  have h0 : ‖Xu - Ru‖ₑ ≤ 0 := ge_of_tendsto hlim hev
  have h00 : Xu - Ru = 0 := by simpa using h0
  linarith

/-- M3c helper: `u ⟨k, Y/(2π|Y|²)⟩` is integrable on `𝔻 \ B(0,1/2)` for `k ∈ L²(𝔻)` and `u` continuous on `𝔻̄`. -/
theorem s07c_fkps_m3c_intA (u : ℂ → ℝ) (k : ℂ → ℂ) (hu : ContinuousOn u (closedBall 0 1))
    (hk : AEMeasurable k) (hk2 : ∫⁻ z in unitDisc, ‖k z‖ₑ ^ 2 < ⊤) :
    IntegrableOn (fun Y => u Y * (conj (k Y) * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re) (unitDisc \ ball 0 (1 / 2)) := by
  have hpi := Real.pi_pos
  have hA : MeasurableSet (unitDisc \ ball (0 : ℂ) (1 / 2)) := measurableSet_ball.diff measurableSet_ball
  have hAD : unitDisc \ ball (0 : ℂ) (1 / 2) ⊆ unitDisc := diff_subset
  obtain ⟨Mu, hMu⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hu
  have hMu0 : 0 ≤ Mu := (norm_nonneg _).trans (hMu 0 (mem_closedBall_self zero_le_one))
  have hk1 : ∫⁻ z in unitDisc, ‖k z‖ₑ < ⊤ := s07c_fkps_m3b_l1_of_l2 k unitDisc measure_ball_lt_top.ne hk2
  have hkA : Integrable (fun z => ‖k z‖) (volume.restrict (unitDisc \ ball (0 : ℂ) (1 / 2))) :=
    ⟨hk.aestronglyMeasurable.norm.restrict, by
      show ∫⁻ z in unitDisc \ ball (0 : ℂ) (1 / 2), ‖‖k z‖‖ₑ < ⊤
      simp only [enorm_norm]
      exact lt_of_le_of_lt (lintegral_mono_set hAD) hk1⟩
  have hZm : Measurable (fun Y : ℂ => Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ)) :=
    measurable_id.div (Complex.measurable_ofReal.comp ((continuous_const.mul (continuous_norm.pow 2)).measurable))
  refine Integrable.mono' (hkA.const_mul (Mu * π⁻¹))
    (((hu.mono (hAD.trans ball_subset_closedBall)).aestronglyMeasurable hA).mul
      (Complex.continuous_re.comp_aestronglyMeasurable
        ((Complex.continuous_conj.comp_aestronglyMeasurable hk.aestronglyMeasurable.restrict).mul
          hZm.aestronglyMeasurable))) ((ae_restrict_iff' hA).2 (Eventually.of_forall fun Y hY => ?_))
  have h2 : 1 / 2 ≤ ‖Y‖ := not_lt.1 fun h => hY.2 (mem_ball_zero_iff.2 h)
  have hY0 : 0 < ‖Y‖ := by linarith
  have hZ : ‖Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ)‖ ≤ π⁻¹ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), div_le_iff₀ (by positivity),
      show π⁻¹ * (2 * π * ‖Y‖ ^ 2) = 2 * ‖Y‖ ^ 2 * (π⁻¹ * π) by ring, inv_mul_cancel₀ hpi.ne', mul_one]
    nlinarith [mul_nonneg hY0.le (by linarith : (0 : ℝ) ≤ 2 * ‖Y‖ - 1)]
  have hre : ‖(conj (k Y) * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re‖ ≤ ‖k Y‖ * π⁻¹ := by
    rw [Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left hZ (norm_nonneg _)
  rw [norm_mul]
  calc _ ≤ Mu * (‖k Y‖ * π⁻¹) := mul_le_mul (hMu Y (ball_subset_closedBall hY.1)) hre (norm_nonneg _) hMu0
    _ = Mu * π⁻¹ * ‖k Y‖ := by ring

/-- M3c helper (S3): `∫_{𝔻 \ B(0,1/2)} u ⟨g, Y/(2π|Y|²)⟩ = ∫₀^{2π} ((4π)⁻¹ f² - (4π)⁻¹ u(e^{it}/2)²)`
(S3b on `B(0, cₙ) \ B(0,1/2)`, `cₙ ↑ 1`). -/
theorem s07c_fkps_m3c_S3 (u : ℂ → ℝ) (f : ℝ → ℝ) (g : ℂ → ℂ) (hu : ContinuousOn u (closedBall 0 1))
    (hb : ∀ θ : ℝ, u (Complex.exp (θ * I)) = f θ)
    (hg : AEMeasurable g) (hg2 : ∫⁻ z in unitDisc, ‖g z‖ₑ ^ 2 < ⊤)
    (hP2 : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
      ∫ z, (u z : ℂ) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I) =
        -∫ z, (φ z : ℂ) * g z) :
    ∫ Y in unitDisc \ ball 0 (1 / 2), u Y * (conj (g Y) * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re =
      ∫ t in (0 : ℝ)..2 * π, ((4 * π)⁻¹ * f t ^ 2 -
        (4 * π)⁻¹ * u (((1 / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2) := by
  have hpi := Real.pi_pos
  set c : ℕ → ℝ := fun n => 1 - 1 / 2 * (1 / ((n : ℝ) + 1)) with hc
  have hc1 : ∀ n, c n < 1 := fun n => by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    simp only [hc]; linarith
  have hc2 : ∀ n, 1 / 2 ≤ c n := fun n => by
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    simp only [hc]; linarith
  have hcm : Monotone c := fun m n hmn => by
    have h := (Nat.cast_le (α := ℝ)).2 hmn
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) (by linarith)
    simp only [hc]; linarith
  have hct : Tendsto c atTop (𝓝 1) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 2 : ℝ)).const_sub 1
    rw [mul_zero, sub_zero] at this
    exact this
  have hcirc : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ t : ℝ,
      (r : ℂ) * Complex.exp ((t : ℂ) * I) ∈ closedBall (0 : ℂ) 1 := fun r hr0 hr1 t => by
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hEc : Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * I)) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hcont : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → Continuous (fun t : ℝ => u ((r : ℂ) * Complex.exp ((t : ℂ) * I))) :=
    fun r hr0 hr1 => hu.comp_continuous (continuous_const.mul hEc) (hcirc r hr0 hr1)
  obtain ⟨Mu, hMu⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hu
  have hsqb : ∀ Y ∈ closedBall (0 : ℂ) 1, |(4 * π)⁻¹ * u Y ^ 2| ≤ (4 * π)⁻¹ * Mu ^ 2 := fun Y hY => by
    have h := hMu Y hY
    rw [Real.norm_eq_abs] at h
    rw [abs_mul, abs_of_pos (by positivity), abs_of_nonneg (sq_nonneg _), ← sq_abs]
    gcongr
  -- the boundary side
  have hR : Tendsto (fun n => ∫ t in (0 : ℝ)..2 * π, ((4 * π)⁻¹ * u ((c n : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2 -
      (4 * π)⁻¹ * u (((1 / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2)) atTop
      (𝓝 (∫ t in (0 : ℝ)..2 * π, ((4 * π)⁻¹ * f t ^ 2 -
        (4 * π)⁻¹ * u (((1 / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * ((4 * π)⁻¹ * Mu ^ 2))
      (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => Eventually.of_forall fun t _ => ?_)
      intervalIntegrable_const (Eventually.of_forall fun t _ => ?_)
    · have h0 : 0 ≤ c n := by linarith [hc2 n]
      exact ((continuous_const.mul ((hcont (c n) h0 (hc1 n).le).pow 2)).sub
        (continuous_const.mul ((hcont _ (by norm_num) (by norm_num)).pow 2))).aestronglyMeasurable
    · have h0 : 0 ≤ c n := by linarith [hc2 n]
      have k1 := hsqb _ (hcirc (c n) h0 (hc1 n).le t)
      have k2 := hsqb _ (hcirc (1 / 2) (by norm_num) (by norm_num) t)
      rw [Real.norm_eq_abs]
      exact abs_le.2 ⟨by linarith [(abs_le.1 k1).1, (abs_le.1 k2).2], by linarith [(abs_le.1 k1).2, (abs_le.1 k2).1]⟩
    · have h1 : Tendsto (fun n => (c n : ℂ) * Complex.exp ((t : ℂ) * I)) atTop (𝓝 (Complex.exp ((t : ℂ) * I))) := by
        have := ((Complex.continuous_ofReal.tendsto 1).comp hct).mul_const (Complex.exp ((t : ℂ) * I))
        rwa [Complex.ofReal_one, one_mul] at this
      have h2 : Tendsto (fun n => (c n : ℂ) * Complex.exp ((t : ℂ) * I)) atTop
          (𝓝[closedBall 0 1] (Complex.exp ((t : ℂ) * I))) :=
        tendsto_nhdsWithin_iff.2 ⟨h1, Eventually.of_forall fun n =>
          hcirc (c n) (by linarith [hc2 n]) (hc1 n).le t⟩
      have h3 := (hu _ (by simpa using hcirc 1 zero_le_one le_rfl t)).tendsto.comp h2
      rw [hb t] at h3
      exact ((h3.pow 2).const_mul _).sub_const _
  -- the area side
  have hS : ∀ n, MeasurableSet (ball (0 : ℂ) (c n) \ ball 0 (1 / 2)) := fun n =>
    measurableSet_ball.diff measurableSet_ball
  have hSm : Monotone (fun n => ball (0 : ℂ) (c n) \ ball 0 (1 / 2)) := fun m n hmn =>
    diff_subset_diff_left (ball_subset_ball (hcm hmn))
  have hU : (⋃ n, ball (0 : ℂ) (c n) \ ball 0 (1 / 2)) = unitDisc \ ball 0 (1 / 2) := by
    ext Y
    simp only [mem_iUnion, Set.mem_sdiff]
    constructor
    · rintro ⟨n, h1, h2⟩
      exact ⟨ball_subset_ball (hc1 n).le h1, h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨n, hn⟩ := (hct.eventually (lt_mem_nhds (mem_ball_zero_iff.1 h1))).exists
      exact ⟨n, mem_ball_zero_iff.2 hn, h2⟩
  have hI := s07c_fkps_m3c_intA u g hu hg hg2
  rw [← hU] at hI
  have hL := tendsto_setIntegral_of_monotone hS hSm hI
  rw [hU] at hL
  exact tendsto_nhds_unique hL (hR.congr fun n =>
    (s07c_fkps_m3c_S3b u g hu hg hg2 hP2 (c n) (hc2 n) (hc1 n)).symm)

/-- M3c (P7, the Green energy identity with the truncated weight). Under the hypotheses of M3b, with
`G♭(Y) = (2π)⁻¹ log (1 / max(|Y|, 1/2))` (so `∇G♭(Y) = -Y / (2π |Y|²)` for `|Y| > 1/2`, `∇G♭ = 0` on `B(0, 1/2)`),
the functions `|g|² G♭`, `⟨V, g⟩ G♭` (on `𝔻`) and `u ⟨V, ∇G♭⟩` (on `𝔻 \ B(0, 1/2)`) are integrable and
`∫_𝔻 |g|² G♭ = ½ ((2π)⁻¹ ∫₀^{2π} f² - (2π)⁻¹ ∫₀^{2π} u(e^{it}/2)² dt) - ∫_𝔻 ⟨V, g⟩ G♭
  - ∫_{𝔻 \ B(0,1/2)} u ⟨V, -Y/(2π|Y|²)⟩`. -/
theorem s07c_fkps_m3c_energy : ∀ (u : ℂ → ℝ) (f : ℝ → ℝ) (g V : ℂ → ℂ),
    ContinuousOn u (closedBall 0 1) → (∀ θ : ℝ, u (Complex.exp (θ * I)) = f θ) →
    AEMeasurable g → AEMeasurable V →
    (∫⁻ z in unitDisc, ‖g z‖ₑ ^ 2 < ⊤) → (∫⁻ z in unitDisc, ‖V z‖ₑ ^ 2 < ⊤) →
    (∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
      ∫ z, (u z : ℂ) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I) =
        -∫ z, (φ z : ℂ) * g z) →
    (∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
      ∫ z, (conj (g z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re =
        -∫ z, (conj (V z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re) →
    IntegrableOn (fun Y => ‖g Y‖ ^ 2 * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2)))) unitDisc ∧
    IntegrableOn (fun Y => (conj (V Y) * g Y).re * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2)))) unitDisc ∧
    IntegrableOn (fun Y => u Y * (conj (V Y) * (-Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re) (unitDisc \ ball 0 (1 / 2)) ∧
    ∫ Y in unitDisc, ‖g Y‖ ^ 2 * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2))) =
      1 / 2 * ((2 * π)⁻¹ * (∫ t in (0 : ℝ)..2 * π, f t ^ 2) -
          (2 * π)⁻¹ * (∫ t in (0 : ℝ)..2 * π, u (Complex.exp (t * I) / 2) ^ 2)) -
        (∫ Y in unitDisc, (conj (V Y) * g Y).re * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2)))) -
        ∫ Y in unitDisc \ ball 0 (1 / 2), u Y * (conj (V Y) * (-Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re := by
  intro u f g V hu hb hg hV hg2 hV2 hP2 hP4
  have hpi := Real.pi_pos
  set G : ℂ → ℝ := fun Y => (2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2)) with hGdef
  have hm : ∀ Y : ℂ, 0 < max ‖Y‖ (1 / 2) := fun Y => lt_max_of_lt_right (by norm_num)
  have hGc : Continuous G := continuous_const.mul
    ((continuous_const.div (continuous_norm.max continuous_const) fun Y => (hm Y).ne').log
      fun Y => (one_div_pos.2 (hm Y)).ne')
  obtain ⟨MG, hMG⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hGc.continuousOn
  have hre : ∀ z : ℂ, (conj z * z).re = ‖z‖ ^ 2 := fun z => by
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have conv : ∀ X : ℂ → ℝ, Integrable (fun z => unitDisc.indicator G z * X z) →
      IntegrableOn (fun z => X z * G z) unitDisc := fun X h => by
    have e : (fun z => unitDisc.indicator G z * X z) = unitDisc.indicator (fun z => X z * G z) := funext fun z => by
      by_cases hz : z ∈ unitDisc
      · rw [indicator_of_mem hz, indicator_of_mem hz, mul_comm]
      · rw [indicator_of_notMem hz, indicator_of_notMem hz, zero_mul]
    rw [e] at h
    exact (integrable_indicator_iff (s := unitDisc) measurableSet_ball).1 h
  have hGm : AEStronglyMeasurable (unitDisc.indicator G) (volume.restrict unitDisc) :=
    hGc.aestronglyMeasurable.indicator measurableSet_ball
  have hGb : ∀ z ∈ unitDisc, |unitDisc.indicator G z| ≤ MG := fun z hz => by
    rw [indicator_of_mem hz, ← Real.norm_eq_abs]
    exact hMG z (ball_subset_closedBall hz)
  have hG0 : ∀ (X : ℂ → ℝ) (z : ℂ), z ∉ unitDisc → unitDisc.indicator G z * X z = 0 := fun X z hz => by
    rw [indicator_of_notMem hz, zero_mul]
  have i1 : IntegrableOn (fun Y => ‖g Y‖ ^ 2 * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2)))) unitDisc :=
    (conv _ (s07c_fkps_m3c_int _ hGm MG hGb g g hg hg hg2 hg2 (hG0 _))).congr_fun
      (fun z _ => by simp only [hre, hGdef]) measurableSet_ball
  have i2 : IntegrableOn (fun Y => (conj (V Y) * g Y).re * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2)))) unitDisc :=
    conv _ (s07c_fkps_m3c_int _ hGm MG hGb V g hV hg hV2 hg2 (hG0 _))
  have i3 : IntegrableOn (fun Y => u Y * (conj (V Y) * (-Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re)
      (unitDisc \ ball 0 (1 / 2)) :=
    (s07c_fkps_m3c_intA u V hu hV hV2).neg.congr_fun
      (fun z _ => by simp only [Pi.neg_apply, neg_div, mul_neg, Complex.neg_re]) (measurableSet_ball.diff measurableSet_ball)
  have i4 : IntegrableOn (fun Y => -(u Y * (conj (g Y) * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re))
      (unitDisc \ ball 0 (1 / 2)) := (s07c_fkps_m3c_intA u g hu hg hg2).neg
  refine ⟨i1, i2, i3, ?_⟩
  have hS2 := s07c_fkps_m3c_S2 u g V hu hg hV hg2 hV2 hP2 hP4
  have hS3 := s07c_fkps_m3c_S3 u f g hu hb hg hg2 hP2
  have eL : ∫ Y in unitDisc, (conj (g Y + V Y) * g Y).re * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2))) =
      (∫ Y in unitDisc, ‖g Y‖ ^ 2 * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2)))) + ∫ Y in unitDisc, (conj (V Y) * g Y).re * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2))) := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun Y => ?_)
    simp only [map_add, add_mul, Complex.add_re, hre]
  have eR : ∫ Y in unitDisc \ ball 0 (1 / 2),
      u Y * (conj (g Y + V Y) * (-Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re =
      -(∫ Y in unitDisc \ ball 0 (1 / 2), u Y * (conj (g Y) * (Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re) +
        ∫ Y in unitDisc \ ball 0 (1 / 2), u Y * (conj (V Y) * (-Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re := by
    rw [← integral_neg, ← integral_add i4 i3]
    refine integral_congr_ae (Eventually.of_forall fun Y => ?_)
    simp only [map_add, add_mul, Complex.add_re, neg_div, mul_neg, Complex.neg_re]
    ring
  have hEc : Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * I)) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hmem : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ t : ℝ, (r : ℂ) * Complex.exp ((t : ℂ) * I) ∈ closedBall (0 : ℂ) 1 :=
    fun r hr0 hr1 t => by
      rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hr0]
      exact hr1
  have hfc : Continuous f := by
    rw [show f = fun t : ℝ => u (((1 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * I)) from
      funext fun t => by rw [Complex.ofReal_one, one_mul, hb t]]
    exact hu.comp_continuous (continuous_const.mul hEc) (hmem 1 zero_le_one le_rfl)
  have hhc : Continuous (fun t : ℝ => u (((1 / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * I))) :=
    hu.comp_continuous (continuous_const.mul hEc) (hmem (1 / 2) (by norm_num) (by norm_num))
  have e2 : ∀ t : ℝ, Complex.exp ((t : ℂ) * I) / 2 = ((1 / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * I) := fun t => by
    push_cast; ring
  simp_rw [e2]
  have j1 : IntervalIntegrable (fun t : ℝ => (4 * π)⁻¹ * f t ^ 2) volume 0 (2 * π) :=
    (continuous_const.mul (hfc.pow 2)).intervalIntegrable _ _
  have j2 : IntervalIntegrable (fun t : ℝ => (4 * π)⁻¹ * u (((1 / 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * I)) ^ 2)
      volume 0 (2 * π) := (continuous_const.mul (hhc.pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub j1 j2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hS3
  rw [eL, eR, hS3] at hS2
  linear_combination hS2

/-- M3 (assembly; the statement M4–M6 consume). For `F` as in M3a and `v` `C²` on `ℂ` and harmonic on `𝔻`, with
`u₁ = v ∘ F` and `f θ = v (F (e^{iθ}))`, there are `g, V` (AE-measurable, in `L²(𝔻)`) with:
(P2) `g` is the weak gradient of `u₁` on `𝔻`; (P3) `|V| ≤ 4 |μ_F| |g|` a.e. on `𝔻`; (P4) `Δu₁ = -div V` weakly;
(P5) the Green representation of M3b for a.e. `X ∈ 𝔻`; (P7) the truncated Green energy identity of M3c. -/
theorem s07c_fkps_m3 : ∀ (F : ℂ → ℂ) (K : ℝ),
    IsKQC F univ K → F '' univ = univ → F '' unitDisc = unitDisc → F 0 = 0 →
    (∀ᵐ z, z ∈ unitDisc → ‖LiZhongQC.complexDilatation F z‖ ≤ 1 / 2) →
    ∀ v : ℂ → ℝ, ContDiff ℝ 2 v → InnerProductSpace.HarmonicOnNhd v unitDisc →
    ∃ g V : ℂ → ℂ, AEMeasurable g ∧ AEMeasurable V ∧
      (∫⁻ z in unitDisc, ‖g z‖ₑ ^ 2 < ⊤) ∧ (∫⁻ z in unitDisc, ‖V z‖ₑ ^ 2 < ⊤) ∧
      (∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
        ∫ z, (v (F z) : ℂ) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I) =
          -∫ z, (φ z : ℂ) * g z) ∧
      (∀ᵐ z, z ∈ unitDisc → ‖V z‖ ≤ 4 * ‖LiZhongQC.complexDilatation F z‖ * ‖g z‖) ∧
      (∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ unitDisc →
        ∫ z, (conj (g z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re =
          -∫ z, (conj (V z) * (((fderiv ℝ φ z 1 : ℝ) : ℂ) + ((fderiv ℝ φ z I : ℝ) : ℂ) * I)).re) ∧
      (∀ᵐ X, X ∈ unitDisc →
        IntegrableOn (fun Y => (conj (((1 - ‖X‖ ^ 2 : ℝ) : ℂ) /
          (2 * π * conj (X - Y) * (1 - X * conj Y))) * V Y).re) unitDisc ∧
        v (F X) = (2 * π)⁻¹ * (∫ t in (0 : ℝ)..2 * π,
            (1 - ‖X‖ ^ 2) / ‖Complex.exp (t * I) - X‖ ^ 2 * v (F (Complex.exp (t * I)))) -
          ∫ Y in unitDisc, (conj (((1 - ‖X‖ ^ 2 : ℝ) : ℂ) /
            (2 * π * conj (X - Y) * (1 - X * conj Y))) * V Y).re) ∧
      IntegrableOn (fun Y => ‖g Y‖ ^ 2 * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2)))) unitDisc ∧
      IntegrableOn (fun Y => (conj (V Y) * g Y).re * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2)))) unitDisc ∧
      IntegrableOn (fun Y => v (F Y) * (conj (V Y) * (-Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re)
        (unitDisc \ ball 0 (1 / 2)) ∧
      ∫ Y in unitDisc, ‖g Y‖ ^ 2 * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2))) =
        1 / 2 * ((2 * π)⁻¹ * (∫ t in (0 : ℝ)..2 * π, v (F (Complex.exp (t * I))) ^ 2) -
            (2 * π)⁻¹ * (∫ t in (0 : ℝ)..2 * π, v (F (Complex.exp (t * I) / 2)) ^ 2)) -
          (∫ Y in unitDisc, (conj (V Y) * g Y).re * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2)))) -
          ∫ Y in unitDisc \ ball 0 (1 / 2), v (F Y) * (conj (V Y) * (-Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re := by
  intro F K hq hFu hFD hF0 hμ v hv hharm
  obtain ⟨g, V, hgm, hVm, hg2, hP2, hP3, hP4⟩ := s07c_fkps_m3a_pullback F K hq hFu hFD hF0 hμ v hv hharm
  have hFc : Continuous F := continuousOn_univ.1 hq.2.2.1.1
  have hu : ContinuousOn (fun z => v (F z)) (closedBall 0 1) := (hv.continuous.comp hFc).continuousOn
  have hb : ∀ θ : ℝ, (fun z => v (F z)) (Complex.exp (θ * I)) = (fun θ : ℝ => v (F (Complex.exp (θ * I)))) θ :=
    fun θ => rfl
  -- `V ∈ L²(𝔻)` from `|V| ≤ 4 |μ| |g| ≤ 2 |g|`
  have hVL : ∫⁻ z in unitDisc, ‖V z‖ₑ ^ 2 < ⊤ := by
    have hD : MeasurableSet unitDisc := (measurableSet_ball : MeasurableSet (ball (0 : ℂ) 1))
    have hle : ∀ᵐ z ∂(volume.restrict unitDisc), ‖V z‖ₑ ^ 2 ≤ 4 * ‖g z‖ₑ ^ 2 := by
      filter_upwards [ae_restrict_mem hD, ae_restrict_of_ae hP3, ae_restrict_of_ae hμ] with z hz h3 hm
      have k3 := h3 hz
      have km := hm hz
      have k : ‖V z‖ ≤ 2 * ‖g z‖ := by
        have := mul_le_mul_of_nonneg_right km (norm_nonneg (g z))
        nlinarith [norm_nonneg (g z), norm_nonneg (LiZhongQC.complexDilatation F z)]
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ENNReal.ofReal_pow (norm_nonneg _), show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg (V z)])
    calc ∫⁻ z in unitDisc, ‖V z‖ₑ ^ 2 ≤ ∫⁻ z in unitDisc, 4 * ‖g z‖ₑ ^ 2 := lintegral_mono_ae hle
      _ = 4 * ∫⁻ z in unitDisc, ‖g z‖ₑ ^ 2 := lintegral_const_mul' 4 _ (by norm_num)
      _ < ⊤ := ENNReal.mul_lt_top (by norm_num) hg2
  have h5 := s07c_fkps_m3b_green (fun z => v (F z)) (fun θ : ℝ => v (F (Complex.exp (θ * I)))) g V hu hb hgm hVm
    hg2 hVL hP2 hP4
  have h7 := s07c_fkps_m3c_energy (fun z => v (F z)) (fun θ : ℝ => v (F (Complex.exp (θ * I)))) g V hu hb hgm hVm
    hg2 hVL hP2 hP4
  exact ⟨g, V, hgm, hVm, hg2, hVL, hP2, hP3, hP4, h5, h7.1, h7.2.1, h7.2.2.1, h7.2.2.2⟩

/-- M4.1 helper: the Whitney majorant hypothesis, swapped. For a.e. `w ∈ 𝔻`, `m w ≤ a z` for a.e. `z` in the
smaller ball `B(w, δ(w)/4)`. -/
theorem s07c_fkps_m4_ae_swap {m a : ℂ → ℝ} (hm : AEMeasurable m) (ha : Measurable a)
    (hM : ∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) → m w ≤ a z) :
    ∀ᵐ w, w ∈ unitDisc → ∀ᵐ z, z ∈ ball w ((1 - ‖w‖) / 4) → m w ≤ a z := by
  set m' := hm.mk m with hm'_def
  have hmm' : m =ᵐ[volume] m' := hm.ae_eq_mk
  set S : Set (ℂ × ℂ) :=
    {p | p.2 ∈ unitDisc ∧ dist p.1 p.2 < (1 - ‖p.2‖) / 2 ∧ a p.2 < m' p.1} with hS_def
  have hSm : MeasurableSet S := by
    refine (measurableSet_ball.preimage measurable_snd).inter
      ((measurableSet_lt (measurable_fst.dist measurable_snd) ?_).inter
        (measurableSet_lt (ha.comp measurable_snd) (hm.measurable_mk.comp measurable_fst)))
    exact (measurable_const.sub measurable_snd.norm).div_const _
  have hslice : ∀ z, volume ((fun w => (w, z)) ⁻¹' S) = 0 := by
    intro z
    rw [measure_eq_zero_iff_ae_notMem]
    by_cases hz : z ∈ unitDisc
    · filter_upwards [hM z hz, hmm'] with w hw hww
      rintro ⟨-, hd, hlt⟩
      have h1 := hw (by rw [mem_ball]; exact hd)
      rw [hww] at h1
      exact (not_lt.2 h1) hlt
    · exact ae_of_all _ (fun w hw => hz hw.1)
  have hprod : (volume.prod volume : Measure (ℂ × ℂ)) S = 0 := by
    rw [Measure.prod_apply_symm hSm]
    simp [hslice]
  have hnull := Measure.measure_ae_null_of_prod_null hprod
  filter_upwards [hnull, hmm'] with w hw hww hw𝔻
  have hw' : volume (Prod.mk w ⁻¹' S) = 0 := hw
  rw [measure_eq_zero_iff_ae_notMem] at hw'
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 (show w ∈ ball (0 : ℂ) 1 from hw𝔻)
  have hδw : 0 < 1 - ‖w‖ := by linarith
  filter_upwards [hw'] with z hz hzb
  have hz1 : ‖z - w‖ < (1 - ‖w‖) / 4 := by rw [mem_ball, dist_eq_norm] at hzb; exact hzb
  have h1 := norm_sub_norm_le z w
  by_contra hcon
  push Not at hcon
  apply hz
  refine ⟨?_, ?_, ?_⟩
  · show z ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff]; linarith
  · show dist w z < (1 - ‖z‖) / 2
    rw [dist_eq_norm, norm_sub_rev]; linarith
  · show a z < m' w
    rw [← hww]; exact hcon

/-- M4.1 helper: the Whitney average bound. For a.e. `w ∈ 𝔻`,
`m(w)² |B(w, δ/4)| ≤ ∫_{B(w, δ/4)} a²`. -/
theorem s07c_fkps_m4_whitney_avg {m a : ℂ → ℝ} (hm : AEMeasurable m) (ha : Measurable a)
    (hm0 : ∀ z, 0 ≤ m z)
    (hM : ∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) → m w ≤ a z) :
    ∀ᵐ w, w ∈ unitDisc →
      ENNReal.ofReal (m w ^ 2 * (π * ((1 - ‖w‖) / 4) ^ 2)) ≤
        ∫⁻ z in ball w ((1 - ‖w‖) / 4), ENNReal.ofReal (a z ^ 2) := by
  filter_upwards [s07c_fkps_m4_ae_swap hm ha hM] with w hw hw𝔻
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 (show w ∈ ball (0 : ℂ) 1 from hw𝔻)
  have hq : (0 : ℝ) ≤ (1 - ‖w‖) / 4 := by linarith
  have hvol : volume (ball w ((1 - ‖w‖) / 4)) = ENNReal.ofReal (π * ((1 - ‖w‖) / 4) ^ 2) := by
    rw [Complex.volume_ball, ← ENNReal.ofReal_pow hq, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1; ring
  rw [ENNReal.ofReal_mul (sq_nonneg _), ← hvol, ← setLIntegral_const]
  refine lintegral_mono_ae ?_
  filter_upwards [(ae_restrict_iff' measurableSet_ball).2 (hw hw𝔻)] with z hz
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hm0 w) hz 2)

/-- M4.1 helper: the radial projection. Every `w ∈ 𝔻` is at distance `1 - |w|` from some `ζ ∈ ∂𝔻`. -/
theorem s07c_fkps_m4_radial {w : ℂ} (hw : ‖w‖ < 1) :
    ∃ ζ ∈ sphere (0 : ℂ) 1, ‖w - ζ‖ = 1 - ‖w‖ := by
  by_cases h0 : w = 0
  · refine ⟨1, by simp, ?_⟩
    simp [h0]
  · have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 h0
    have hc : ((‖w‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hn
    refine ⟨w / (‖w‖ : ℂ), ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, norm_norm, div_self hn]
    · have he : w - w / (‖w‖ : ℂ) = (((‖w‖ - 1 : ℝ)) : ℂ) * (w / (‖w‖ : ℂ)) := by
        push_cast
        rw [sub_mul, one_mul, mul_div_assoc', mul_div_cancel_left₀ w hc]
      rw [he, norm_mul, Complex.norm_real, norm_div, Complex.norm_real, norm_norm, div_self hn, mul_one,
        Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring

/-- M4.1 helper: the pointwise bound `m ≤ 4 √ε` a.e. on `𝔻`. -/
theorem s07c_fkps_m4_ptwise_aux {m a : ℂ → ℝ} {ε : ℝ} (hm : AEMeasurable m) (ha : Measurable a)
    (hm0 : ∀ z, 0 ≤ m z) (hε : 0 ≤ ε)
    (hM : ∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) → m w ≤ a z)
    (hC : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
        ≤ ENNReal.ofReal (ε * r)) :
    ∀ᵐ w, w ∈ unitDisc → m w ≤ 4 * Real.sqrt ε := by
  filter_upwards [s07c_fkps_m4_whitney_avg hm ha hm0 hM] with w hw hw𝔻
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 (show w ∈ ball (0 : ℂ) 1 from hw𝔻)
  have hδ0 : 0 < 1 - ‖w‖ := by linarith
  obtain ⟨ζ, hζ, hwζ⟩ := s07c_fkps_m4_radial hw1
  have hsub : ball w ((1 - ‖w‖) / 4) ⊆ unitDisc ∩ ball ζ (5 * (1 - ‖w‖) / 4) := by
    intro z hz
    have hz1 : ‖z - w‖ < (1 - ‖w‖) / 4 := by rw [mem_ball, dist_eq_norm] at hz; exact hz
    have h1 := norm_sub_norm_le z w
    refine ⟨?_, ?_⟩
    · show z ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff]; linarith
    · rw [mem_ball, dist_eq_norm]
      have h2 := norm_sub_le_norm_sub_add_norm_sub z w ζ
      linarith
  have hpt : ∀ z ∈ ball w ((1 - ‖w‖) / 4), ENNReal.ofReal (a z ^ 2) ≤
      ENNReal.ofReal (5 * (1 - ‖w‖) / 2) * ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)) := by
    intro z hz
    have hz1 : ‖z - w‖ < (1 - ‖w‖) / 4 := by rw [mem_ball, dist_eq_norm] at hz; exact hz
    have h1 := norm_sub_norm_le z w
    have h1' := norm_sub_norm_le w z
    rw [norm_sub_rev w z] at h1'
    have hzn : ‖z‖ < 1 := by linarith
    have hq : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have hqle : 1 - ‖z‖ ^ 2 ≤ 5 * (1 - ‖w‖) / 2 := by nlinarith [norm_nonneg z]
    rw [← ENNReal.ofReal_mul (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    calc a z ^ 2 = (1 - ‖z‖ ^ 2) * (a z ^ 2 / (1 - ‖z‖ ^ 2)) := by field_simp [hq.ne']
      _ ≤ 5 * (1 - ‖w‖) / 2 * (a z ^ 2 / (1 - ‖z‖ ^ 2)) :=
          mul_le_mul_of_nonneg_right hqle (div_nonneg (sq_nonneg _) hq.le)
  have hmain : ENNReal.ofReal (m w ^ 2 * (π * ((1 - ‖w‖) / 4) ^ 2)) ≤
      ENNReal.ofReal (5 * (1 - ‖w‖) / 2 * (ε * (5 * (1 - ‖w‖) / 4))) := by
    calc ENNReal.ofReal (m w ^ 2 * (π * ((1 - ‖w‖) / 4) ^ 2))
        ≤ ∫⁻ z in ball w ((1 - ‖w‖) / 4), ENNReal.ofReal (a z ^ 2) := hw hw𝔻
      _ ≤ ∫⁻ z in ball w ((1 - ‖w‖) / 4),
            ENNReal.ofReal (5 * (1 - ‖w‖) / 2) * ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)) :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = ENNReal.ofReal (5 * (1 - ‖w‖) / 2) *
            ∫⁻ z in ball w ((1 - ‖w‖) / 4), ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (5 * (1 - ‖w‖) / 2) *
            ∫⁻ z in unitDisc ∩ ball ζ (5 * (1 - ‖w‖) / 4), ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)) :=
          mul_le_mul_right (lintegral_mono_set hsub) _
      _ ≤ ENNReal.ofReal (5 * (1 - ‖w‖) / 2) * ENNReal.ofReal (ε * (5 * (1 - ‖w‖) / 4)) :=
          mul_le_mul_right (hC ζ hζ _ (by linarith) (by linarith [norm_nonneg w])) _
      _ = ENNReal.ofReal (5 * (1 - ‖w‖) / 2 * (ε * (5 * (1 - ‖w‖) / 4))) :=
          (ENNReal.ofReal_mul (by linarith)).symm
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hmain
  have hδ2 : 0 < (1 - ‖w‖) ^ 2 := by positivity
  have h16 : m w ^ 2 * π * (1 - ‖w‖) ^ 2 ≤ 50 * ε * (1 - ‖w‖) ^ 2 := by nlinarith [hreal]
  have h50 : m w ^ 2 * π ≤ 50 * ε := le_of_mul_le_mul_right h16 hδ2
  have hsq : m w ^ 2 ≤ 16 * ε := by nlinarith [Real.pi_gt_d2, sq_nonneg (m w)]
  calc m w = Real.sqrt (m w ^ 2) := (Real.sqrt_sq (hm0 w)).symm
    _ ≤ Real.sqrt (16 * ε) := Real.sqrt_le_sqrt hsq
    _ = 4 * Real.sqrt ε := by
        rw [Real.sqrt_mul (by norm_num), show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- M4.1 helper: `𝔻` is covered by the two boxes `𝔻 ∩ B(±1, 3/2)`. -/
theorem s07c_fkps_m4_cover :
    unitDisc ⊆ (unitDisc ∩ ball (1 : ℂ) (3 / 2)) ∪ (unitDisc ∩ ball (-1 : ℂ) (3 / 2)) := by
  intro z hz
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 (show z ∈ ball (0 : ℂ) 1 from hz)
  rcases lt_or_ge ‖z - 1‖ (3 / 2) with h1 | h1
  · exact Or.inl ⟨hz, by rw [mem_ball, dist_eq_norm]; exact h1⟩
  rcases lt_or_ge ‖z - -1‖ (3 / 2) with h2 | h2
  · exact Or.inr ⟨hz, by rw [mem_ball, dist_eq_norm]; exact h2⟩
  exfalso
  have e1 : ‖z - 1‖ ^ 2 = (z.re - 1) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have e2 : ‖z - -1‖ ^ 2 = (z.re + 1) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have e0 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  nlinarith [mul_self_le_mul_self (by norm_num) h1, mul_self_le_mul_self (by norm_num) h2,
    mul_self_lt_mul_self (norm_nonneg z) hz1]

/-- M4.1 helper: the Carleson bound for `m²/δ`, with constant `20`. -/
theorem s07c_fkps_m4_carl_aux {m a : ℂ → ℝ} {ε : ℝ} (hm : AEMeasurable m) (ha : Measurable a)
    (hm0 : ∀ z, 0 ≤ m z) (hε : 0 ≤ ε)
    (hM : ∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) → m w ≤ a z)
    (hC : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
        ≤ ENNReal.ofReal (ε * r)) :
    ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (m z ^ 2 / (1 - ‖z‖))
        ≤ ENNReal.ofReal (20 * ε * r) := by
  classical
  intro ζ hζ r hr0 hr2
  have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.1 hζ
  set S : Set ℂ := unitDisc ∩ ball ζ r with hS
  have hSm : MeasurableSet S := measurableSet_ball.inter measurableSet_ball
  set T : Set ℂ := unitDisc ∩ ball ζ (5 * r / 4) with hT
  have hTm : MeasurableSet T := measurableSet_ball.inter measurableSet_ball
  set F : ℂ → ℂ → ℝ≥0∞ := fun w z =>
    if w ∈ S ∧ dist z w < (1 - ‖w‖) / 4 then
      ENNReal.ofReal (16 / (π * (1 - ‖w‖) ^ 3)) * ENNReal.ofReal (a z ^ 2) else 0 with hF
  -- (a) the a.e. Whitney bound, written as an iterated integral
  have h1 : ∫⁻ w in S, ENNReal.ofReal (m w ^ 2 / (1 - ‖w‖)) ≤ ∫⁻ w, ∫⁻ z, F w z := by
    rw [← lintegral_indicator hSm]
    refine lintegral_mono_ae ?_
    filter_upwards [s07c_fkps_m4_whitney_avg hm ha hm0 hM] with w hw
    by_cases hwS : w ∈ S
    · rw [Set.indicator_of_mem hwS]
      have hw𝔻 : w ∈ unitDisc := hwS.1
      have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 (show w ∈ ball (0 : ℂ) 1 from hw𝔻)
      have hδ : 0 < 1 - ‖w‖ := by linarith
      have hk0 : (0 : ℝ) ≤ 16 / (π * (1 - ‖w‖) ^ 3) :=
        (div_pos (by norm_num) (mul_pos Real.pi_pos (pow_pos hδ 3))).le
      calc ENNReal.ofReal (m w ^ 2 / (1 - ‖w‖))
          = ENNReal.ofReal (16 / (π * (1 - ‖w‖) ^ 3)) *
              ENNReal.ofReal (m w ^ 2 * (π * ((1 - ‖w‖) / 4) ^ 2)) := by
            rw [← ENNReal.ofReal_mul hk0]
            congr 1
            field_simp [hδ.ne', Real.pi_pos.ne']
            ring
        _ ≤ ENNReal.ofReal (16 / (π * (1 - ‖w‖) ^ 3)) *
              ∫⁻ z in ball w ((1 - ‖w‖) / 4), ENNReal.ofReal (a z ^ 2) := mul_le_mul_right (hw hw𝔻) _
        _ = ∫⁻ z in ball w ((1 - ‖w‖) / 4),
              ENNReal.ofReal (16 / (π * (1 - ‖w‖) ^ 3)) * ENNReal.ofReal (a z ^ 2) :=
            (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
        _ = ∫⁻ z, F w z := by
            rw [← lintegral_indicator measurableSet_ball]
            refine lintegral_congr (fun z => ?_)
            by_cases hz : z ∈ ball w ((1 - ‖w‖) / 4)
            · rw [Set.indicator_of_mem hz, hF]
              simp only
              rw [if_pos ⟨hwS, mem_ball.1 hz⟩]
            · rw [Set.indicator_of_notMem hz, hF]
              simp only
              rw [if_neg (fun h => hz (mem_ball.2 h.2))]
    · rw [Set.indicator_of_notMem hwS]
      exact zero_le
  -- (b) Tonelli
  have hFm : Measurable (Function.uncurry F) := by
    show Measurable (fun p : ℂ × ℂ =>
      if p.1 ∈ S ∧ dist p.2 p.1 < (1 - ‖p.1‖) / 4 then
        ENNReal.ofReal (16 / (π * (1 - ‖p.1‖) ^ 3)) * ENNReal.ofReal (a p.2 ^ 2) else 0)
    refine Measurable.ite ?_ ?_ measurable_const
    · exact (hSm.preimage measurable_fst).inter (measurableSet_lt (measurable_snd.dist measurable_fst)
        ((measurable_const.sub measurable_fst.norm).div_const _))
    · exact (Measurable.ennreal_ofReal (measurable_const.div (measurable_const.mul
        ((measurable_const.sub measurable_fst.norm).pow_const 3)))).mul
        ((ha.comp measurable_snd).pow_const 2).ennreal_ofReal
  have h2 : ∫⁻ w, ∫⁻ z, F w z = ∫⁻ z, ∫⁻ w, F w z := lintegral_lintegral_swap hFm.aemeasurable
  -- (c) the inner integral, for fixed `z`
  have h3 : ∀ z, ∫⁻ w, F w z ≤
      T.indicator (fun z => ENNReal.ofReal (125 / 18 * (a z ^ 2 / (1 - ‖z‖ ^ 2)))) z := by
    intro z
    by_cases hzT : z ∈ T
    · rw [Set.indicator_of_mem hzT]
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 (show z ∈ ball (0 : ℂ) 1 from hzT.1)
      have hδz : 0 < 1 - ‖z‖ := by linarith
      have hc0 : (0 : ℝ) ≤ 125 / (4 * π * (1 - ‖z‖) ^ 3) * a z ^ 2 :=
        mul_nonneg (div_pos (by norm_num) (mul_pos (mul_pos (by norm_num) Real.pi_pos)
          (pow_pos hδz 3))).le (sq_nonneg _)
      calc ∫⁻ w, F w z
          ≤ ∫⁻ w, (ball z ((1 - ‖z‖) / 3)).indicator
              (fun _ => ENNReal.ofReal (125 / (4 * π * (1 - ‖z‖) ^ 3) * a z ^ 2)) w := by
            refine lintegral_mono (fun w => ?_)
            rw [hF]
            simp only
            split_ifs with hc
            · obtain ⟨hwS, hd⟩ := hc
              have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 (show w ∈ ball (0 : ℂ) 1 from hwS.1)
              have hδw : 0 < 1 - ‖w‖ := by linarith
              have hzw : ‖z - w‖ < (1 - ‖w‖) / 4 := by rw [dist_eq_norm] at hd; exact hd
              have e1 := norm_sub_norm_le z w
              have e2 := norm_sub_norm_le w z
              rw [norm_sub_rev w z] at e2
              have hlow : 4 / 5 * (1 - ‖z‖) ≤ 1 - ‖w‖ := by linarith
              have hwb : w ∈ ball z ((1 - ‖z‖) / 3) := by
                rw [mem_ball, dist_eq_norm, norm_sub_rev]; linarith
              rw [Set.indicator_of_mem hwb, ← ENNReal.ofReal_mul
                (div_pos (by norm_num) (mul_pos Real.pi_pos (pow_pos hδw 3))).le]
              apply ENNReal.ofReal_le_ofReal
              refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
              calc 16 / (π * (1 - ‖w‖) ^ 3) ≤ 16 / (π * (4 / 5 * (1 - ‖z‖)) ^ 3) :=
                    div_le_div_of_nonneg_left (by norm_num)
                      (mul_pos Real.pi_pos (pow_pos (by positivity) 3))
                      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hlow 3)
                        Real.pi_pos.le)
                _ = 125 / (4 * π * (1 - ‖z‖) ^ 3) := by
                    field_simp [hδz.ne', Real.pi_pos.ne']
                    ring
            · exact zero_le
        _ = ENNReal.ofReal (125 / (4 * π * (1 - ‖z‖) ^ 3) * a z ^ 2) *
              volume (ball z ((1 - ‖z‖) / 3)) := lintegral_indicator_const measurableSet_ball _
        _ = ENNReal.ofReal (125 / (4 * π * (1 - ‖z‖) ^ 3) * a z ^ 2 * (π * ((1 - ‖z‖) / 3) ^ 2)) := by
            rw [Complex.volume_ball, ← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_coe_nnreal,
              NNReal.coe_real_pi, ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul hc0]
            congr 1; ring
        _ ≤ ENNReal.ofReal (125 / 18 * (a z ^ 2 / (1 - ‖z‖ ^ 2))) := by
            apply ENNReal.ofReal_le_ofReal
            have hq : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
            have hq2 : (1 - ‖z‖ ^ 2) / (1 - ‖z‖) ≤ 2 := by
              rw [div_le_iff₀ hδz]; nlinarith [norm_nonneg z]
            set b := a z ^ 2 / (1 - ‖z‖ ^ 2) with hb
            have hb0 : 0 ≤ b := div_nonneg (sq_nonneg _) hq.le
            have hab : a z ^ 2 = (1 - ‖z‖ ^ 2) * b := by rw [hb]; field_simp [hq.ne']
            rw [hab]
            calc 125 / (4 * π * (1 - ‖z‖) ^ 3) * ((1 - ‖z‖ ^ 2) * b) * (π * ((1 - ‖z‖) / 3) ^ 2)
                = 125 / 36 * ((1 - ‖z‖ ^ 2) / (1 - ‖z‖)) * b := by
                  field_simp [hδz.ne', Real.pi_pos.ne']
                  ring
              _ ≤ 125 / 36 * 2 * b := by gcongr
              _ = 125 / 18 * b := by ring
    · rw [Set.indicator_of_notMem hzT]
      have h0 : ∀ w, F w z = 0 := by
        intro w
        rw [hF]
        simp only
        rw [if_neg]
        rintro ⟨hwS, hd⟩
        apply hzT
        have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 (show w ∈ ball (0 : ℂ) 1 from hwS.1)
        have hwζ : ‖w - ζ‖ < r := by
          have := hwS.2; rw [mem_ball, dist_eq_norm] at this; exact this
        have hzw : ‖z - w‖ < (1 - ‖w‖) / 4 := by rw [dist_eq_norm] at hd; exact hd
        have e1 := norm_sub_norm_le z w
        have e3 := norm_sub_norm_le ζ w
        rw [norm_sub_rev ζ w, hζ1] at e3
        refine ⟨?_, ?_⟩
        · show z ∈ ball (0 : ℂ) 1
          rw [mem_ball_zero_iff]; linarith
        · rw [mem_ball, dist_eq_norm]
          have e4 := norm_sub_le_norm_sub_add_norm_sub z w ζ
          linarith
      simp [h0]
  -- (d) assembly
  have hfin : ∫⁻ z in T, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)) ≤
      ENNReal.ofReal (ε * (5 * r / 4)) ∨
      ∫⁻ z in T, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)) ≤ ENNReal.ofReal (3 * ε) := by
    rcases lt_or_ge r (8 / 5) with hr | hr
    · exact Or.inl (hC ζ hζ _ (by linarith) (by linarith))
    · refine Or.inr ?_
      calc ∫⁻ z in T, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
          ≤ ∫⁻ z in unitDisc, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)) :=
            lintegral_mono_set inter_subset_left
        _ ≤ ∫⁻ z in (unitDisc ∩ ball (1 : ℂ) (3 / 2)) ∪ (unitDisc ∩ ball (-1 : ℂ) (3 / 2)),
              ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)) := lintegral_mono_set s07c_fkps_m4_cover
        _ ≤ (∫⁻ z in unitDisc ∩ ball (1 : ℂ) (3 / 2), ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))) +
              ∫⁻ z in unitDisc ∩ ball (-1 : ℂ) (3 / 2), ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)) :=
            lintegral_union_le _ _ _
        _ ≤ ENNReal.ofReal (ε * (3 / 2)) + ENNReal.ofReal (ε * (3 / 2)) :=
            add_le_add (hC 1 (by simp) _ (by norm_num) (by norm_num))
              (hC (-1) (by simp) _ (by norm_num) (by norm_num))
        _ = ENNReal.ofReal (3 * ε) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring
  calc ∫⁻ w in S, ENNReal.ofReal (m w ^ 2 / (1 - ‖w‖))
      ≤ ∫⁻ w, ∫⁻ z, F w z := h1
    _ = ∫⁻ z, ∫⁻ w, F w z := h2
    _ ≤ ∫⁻ z, T.indicator (fun z => ENNReal.ofReal (125 / 18 * (a z ^ 2 / (1 - ‖z‖ ^ 2)))) z :=
        lintegral_mono (fun z => h3 z)
    _ = ∫⁻ z in T, ENNReal.ofReal (125 / 18 * (a z ^ 2 / (1 - ‖z‖ ^ 2))) := lintegral_indicator hTm _
    _ = ENNReal.ofReal (125 / 18) * ∫⁻ z in T, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)) := by
        simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 125 / 18)]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (20 * ε * r) := by
        rcases hfin with hf | hf
        · calc ENNReal.ofReal (125 / 18) * ∫⁻ z in T, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
              ≤ ENNReal.ofReal (125 / 18) * ENNReal.ofReal (ε * (5 * r / 4)) := mul_le_mul_right hf _
            _ = ENNReal.ofReal (125 / 18 * (ε * (5 * r / 4))) := (ENNReal.ofReal_mul (by norm_num)).symm
            _ ≤ ENNReal.ofReal (20 * ε * r) := ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hε hr0.le])
        · rcases lt_or_ge r (8 / 5) with hr | hr
          · -- the first alternative also holds here; recompute it
            calc ENNReal.ofReal (125 / 18) * ∫⁻ z in T, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
                ≤ ENNReal.ofReal (125 / 18) * ENNReal.ofReal (ε * (5 * r / 4)) :=
                  mul_le_mul_right (hC ζ hζ _ (by linarith) (by linarith)) _
              _ = ENNReal.ofReal (125 / 18 * (ε * (5 * r / 4))) := (ENNReal.ofReal_mul (by norm_num)).symm
              _ ≤ ENNReal.ofReal (20 * ε * r) :=
                  ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hε hr0.le])
          · calc ENNReal.ofReal (125 / 18) * ∫⁻ z in T, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
                ≤ ENNReal.ofReal (125 / 18) * ENNReal.ofReal (3 * ε) := mul_le_mul_right hf _
              _ = ENNReal.ofReal (125 / 18 * (3 * ε)) := (ENNReal.ofReal_mul (by norm_num)).symm
              _ ≤ ENNReal.ofReal (20 * ε * r) := ENNReal.ofReal_le_ofReal (by nlinarith)

/-- M4.1: from a Whitney majorant to pointwise and Carleson bounds. If `m ≤ a z` a.e. on every Whitney ball
`B(z, δ(z)/2)`, `z ∈ 𝔻`, and `a²/(1-|z|²) dA` has Carleson norm `≤ ε` on boxes `𝔻 ∩ B(ζ, r)`, then `m ≤ C √ε`
a.e. on `𝔻`, and `m²/(1-|z|) dA` has Carleson norm `≤ C ε`. -/
theorem s07c_fkps_m4_pointwise : ∃ C : ℝ, 0 < C ∧ ∀ (m a : ℂ → ℝ) (ε : ℝ),
    AEMeasurable m → Measurable a → (∀ z, 0 ≤ m z) → (∀ z, 0 ≤ a z) → 0 ≤ ε →
    (∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) → m w ≤ a z) →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
        ≤ ENNReal.ofReal (ε * r)) →
    (∀ᵐ w, w ∈ unitDisc → m w ≤ C * Real.sqrt ε) ∧
    ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (m z ^ 2 / (1 - ‖z‖))
        ≤ ENNReal.ofReal (C * ε * r) := by
  refine ⟨20, by norm_num, ?_⟩
  intro m a ε hm ha hm0 _ha0 hε hM hC
  -- `0 ≤ a` is not needed: only `a²` enters.
  refine ⟨?_, s07c_fkps_m4_carl_aux hm ha hm0 hε hM hC⟩
  filter_upwards [s07c_fkps_m4_ptwise_aux hm ha hm0 hε hM hC] with w hw hw𝔻
  have := hw hw𝔻
  nlinarith [Real.sqrt_nonneg ε]


/-! ### Stage A: dyadic geometry -/

theorem s07c_fkps_m4_tau_mem (z : ℂ) :
    (if 0 < arg z then arg z else arg z + 2 * π) ∈ Ioc 0 (2 * π) := by
  have h1 := neg_pi_lt_arg z
  have h2 := arg_le_pi z
  split_ifs with h
  · exact ⟨h, by linarith [Real.pi_pos]⟩
  · push Not at h
    exact ⟨by linarith, by linarith⟩

theorem s07c_fkps_m4_tau_polar (z : ℂ) :
    (‖z‖ : ℂ) * exp (((if 0 < arg z then arg z else arg z + 2 * π : ℝ) : ℂ) * I) = z := by
  split_ifs
  · exact norm_mul_exp_arg_mul_I z
  · push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    exact norm_mul_exp_arg_mul_I z

theorem s07c_fkps_m4_tau_measurable :
    Measurable fun z : ℂ => if 0 < arg z then arg z else arg z + 2 * π :=
  Measurable.ite (measurableSet_lt measurable_const measurable_arg) measurable_arg
    (measurable_arg.add_const _)

theorem s07c_fkps_m4_exp_dist (a b : ℝ) : ‖exp (a * I) - exp (b * I)‖ ≤ |a - b| := by
  have h : exp (a * I) - exp (b * I) = exp (b * I) * (exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, ← Real.norm_eq_abs]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- `‖z - e^{iτ(z)}‖ = 1 - ‖z‖` for `‖z‖ ≤ 1`. -/
theorem s07c_fkps_m4_tau_dist {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖z - exp (((if 0 < arg z then arg z else arg z + 2 * π : ℝ) : ℂ) * I)‖ = 1 - ‖z‖ := by
  set e := exp (((if 0 < arg z then arg z else arg z + 2 * π : ℝ) : ℂ) * I) with he
  have hp : (‖z‖ : ℂ) * e = z := s07c_fkps_m4_tau_polar z
  have h1 : z - e = (((‖z‖ - 1 : ℝ)) : ℂ) * e := by
    push_cast
    rw [sub_mul, one_mul, hp]
  rw [h1, norm_mul, Complex.norm_real, he, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs,
    abs_of_nonpos (by linarith)]
  ring

theorem s07c_fkps_m4_arc_mem {θ : ℝ} (hθ : θ ∈ Ioc 0 (2 * π)) (j : ℕ) :
    θ ∈ Ioc (2 * π * ((⌈θ * 2 ^ j / (2 * π)⌉₊ - 1 : ℕ) : ℝ) / 2 ^ j)
      (2 * π * (((⌈θ * 2 ^ j / (2 * π)⌉₊ - 1 : ℕ) : ℝ) + 1) / 2 ^ j) := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hpw : (0 : ℝ) < 2 ^ j := by positivity
  set x := θ * 2 ^ j / (2 * π) with hx
  have hx0 : 0 < x := div_pos (mul_pos hθ.1 hpw) h2π
  have hn1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hx0).ne'
  have hcast : ((⌈x⌉₊ - 1 : ℕ) : ℝ) = (⌈x⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
  have hc1 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
  have hc2 : x ≤ ⌈x⌉₊ := Nat.le_ceil x
  have hxe : x * (2 * π) = θ * 2 ^ j := by rw [hx]; field_simp
  rw [hcast]
  constructor
  · rw [div_lt_iff₀ hpw]
    nlinarith
  · rw [le_div_iff₀ hpw]
    nlinarith

theorem s07c_fkps_m4_arc_uniq {θ : ℝ} {j k k' : ℕ}
    (h : θ ∈ Ioc (2 * π * (k : ℝ) / 2 ^ j) (2 * π * ((k : ℝ) + 1) / 2 ^ j))
    (h' : θ ∈ Ioc (2 * π * (k' : ℝ) / 2 ^ j) (2 * π * ((k' : ℝ) + 1) / 2 ^ j)) : k = k' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 : ((k : ℝ) + 1) ≤ k' := by exact_mod_cast hlt
    have h2 : 2 * π * ((k : ℝ) + 1) / 2 ^ j ≤ 2 * π * (k' : ℝ) / 2 ^ j := by gcongr
    linarith [h.2, h'.1]
  · have h1 : ((k' : ℝ) + 1) ≤ k := by exact_mod_cast hlt
    have h2 : 2 * π * ((k' : ℝ) + 1) / 2 ^ j ≤ 2 * π * (k : ℝ) / 2 ^ j := by gcongr
    linarith [h.1, h'.2]

theorem s07c_fkps_m4_arc_anc {i j k : ℕ} (hij : i ≤ j) :
    Ioc (2 * π * (k : ℝ) / 2 ^ j) (2 * π * ((k : ℝ) + 1) / 2 ^ j) ⊆
      Ioc (2 * π * ((k / 2 ^ (j - i) : ℕ) : ℝ) / 2 ^ i)
        (2 * π * (((k / 2 ^ (j - i) : ℕ) : ℝ) + 1) / 2 ^ i) := by
  intro θ hθ
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have hm : 0 < 2 ^ d := by positivity
  have h2 : k + 1 ≤ (k / 2 ^ d + 1) * 2 ^ d := by
    nlinarith [Nat.div_add_mod k (2 ^ d), Nat.mod_lt k hm]
  have hpw : (2 : ℝ) ^ (i + d) = 2 ^ i * 2 ^ d := pow_add 2 i d
  have hi : (0 : ℝ) < 2 ^ i := by positivity
  have hd : (0 : ℝ) < 2 ^ d := by positivity
  have hq1 : ((k / 2 ^ d : ℕ) : ℝ) * 2 ^ d ≤ k := by exact_mod_cast Nat.div_mul_le_self k (2 ^ d)
  have hq2 : (k : ℝ) + 1 ≤ (((k / 2 ^ d : ℕ) : ℝ) + 1) * 2 ^ d := by exact_mod_cast h2
  obtain ⟨hθ1, hθ2⟩ := hθ
  rw [hpw] at hθ1 hθ2
  constructor
  · calc 2 * π * ((k / 2 ^ d : ℕ) : ℝ) / 2 ^ i
        = 2 * π * (((k / 2 ^ d : ℕ) : ℝ) * 2 ^ d) / (2 ^ i * 2 ^ d) := by field_simp
      _ ≤ 2 * π * (k : ℝ) / (2 ^ i * 2 ^ d) := by gcongr
      _ < θ := hθ1
  · calc θ ≤ 2 * π * ((k : ℝ) + 1) / (2 ^ i * 2 ^ d) := hθ2
      _ ≤ 2 * π * ((((k / 2 ^ d : ℕ) : ℝ) + 1) * 2 ^ d) / (2 ^ i * 2 ^ d) := by gcongr
      _ = 2 * π * (((k / 2 ^ d : ℕ) : ℝ) + 1) / 2 ^ i := by field_simp

theorem s07c_fkps_m4_arc_vol {j k : ℕ} (hk : k < 2 ^ j) :
    Ioc (2 * π * (k : ℝ) / 2 ^ j) (2 * π * ((k : ℝ) + 1) / 2 ^ j) ∩ Ioc 0 (2 * π) =
        Ioc (2 * π * (k : ℝ) / 2 ^ j) (2 * π * ((k : ℝ) + 1) / 2 ^ j) ∧
      volume (Ioc (2 * π * (k : ℝ) / 2 ^ j) (2 * π * ((k : ℝ) + 1) / 2 ^ j)) =
        ENNReal.ofReal (2 * π / 2 ^ j) := by
  have hpw : (0 : ℝ) < 2 ^ j := by positivity
  have hk1 : (k : ℝ) + 1 ≤ 2 ^ j := by exact_mod_cast hk
  refine ⟨inter_eq_left.2 ?_, ?_⟩
  · intro θ hθ
    refine ⟨lt_of_le_of_lt (by positivity) hθ.1, hθ.2.trans ?_⟩
    rw [div_le_iff₀ hpw]
    nlinarith [Real.pi_pos]
  · rw [Real.volume_Ioc]
    congr 1
    field_simp
    ring

theorem s07c_fkps_m4_arc_out {j k : ℕ} (hk : 2 ^ j ≤ k) :
    Ioc (2 * π * (k : ℝ) / 2 ^ j) (2 * π * ((k : ℝ) + 1) / 2 ^ j) ∩ Ioc 0 (2 * π) = ∅ := by
  have hpw : (0 : ℝ) < 2 ^ j := by positivity
  have hk1 : (2 : ℝ) ^ j ≤ k := by exact_mod_cast hk
  ext θ
  simp only [mem_inter_iff, mem_Ioc, mem_empty_iff_false, iff_false, not_and]
  intro h1 _ h4
  have : 2 * π ≤ 2 * π * (k : ℝ) / 2 ^ j := by
    rw [le_div_iff₀ hpw]
    nlinarith [Real.pi_pos]
  linarith [h1.1]

theorem s07c_fkps_m4_tile_measurable (j k : ℕ) :
    MeasurableSet {z : ℂ | (1 / 2 : ℝ) ^ (j + 1) < 1 - ‖z‖ ∧ 1 - ‖z‖ ≤ (1 / 2 : ℝ) ^ j ∧
      (if 0 < arg z then arg z else arg z + 2 * π) ∈
        Ioc (2 * π * (k : ℝ) / 2 ^ j) (2 * π * ((k : ℝ) + 1) / 2 ^ j)} :=
  (measurableSet_lt measurable_const (measurable_const.sub measurable_norm)).inter
    ((measurableSet_le (measurable_const.sub measurable_norm) measurable_const).inter
      (measurableSet_Ioc.preimage s07c_fkps_m4_tau_measurable))

theorem s07c_fkps_m4_tile_disjoint :
    Pairwise (Function.onFun Disjoint fun p : ℕ × ℕ =>
      {z : ℂ | (1 / 2 : ℝ) ^ (p.1 + 1) < 1 - ‖z‖ ∧ 1 - ‖z‖ ≤ (1 / 2 : ℝ) ^ p.1 ∧
        (if 0 < arg z then arg z else arg z + 2 * π) ∈
          Ioc (2 * π * (p.2 : ℝ) / 2 ^ p.1) (2 * π * ((p.2 : ℝ) + 1) / 2 ^ p.1)}) := by
  intro p q hpq
  rw [Function.onFun, Set.disjoint_left]
  rintro z ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
  by_cases hj : p.1 = q.1
  · apply hpq
    have hk : p.2 = q.2 := by
      rw [hj] at a3
      exact s07c_fkps_m4_arc_uniq a3 b3
    exact Prod.ext hj hk
  · rcases Nat.lt_or_gt_of_ne hj with hlt | hlt
    · have : (1 / 2 : ℝ) ^ q.1 ≤ (1 / 2 : ℝ) ^ (p.1 + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hlt
      linarith
    · have : (1 / 2 : ℝ) ^ p.1 ≤ (1 / 2 : ℝ) ^ (q.1 + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hlt
      linarith

theorem s07c_fkps_m4_tile_cover :
    unitDisc ⊆ ⋃ p : ℕ × ℕ,
      {z : ℂ | (1 / 2 : ℝ) ^ (p.1 + 1) < 1 - ‖z‖ ∧ 1 - ‖z‖ ≤ (1 / 2 : ℝ) ^ p.1 ∧
        (if 0 < arg z then arg z else arg z + 2 * π) ∈
          Ioc (2 * π * (p.2 : ℝ) / 2 ^ p.1) (2 * π * ((p.2 : ℝ) + 1) / 2 ^ p.1)} := by
  intro z hz
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 (show z ∈ ball (0 : ℂ) 1 from hz)
  have hδ : 0 < 1 - ‖z‖ := by linarith
  have hδ1 : 1 - ‖z‖ ≤ 1 := by linarith [norm_nonneg z]
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (one_le_one_div hδ hδ1) (by norm_num : (1 : ℝ) < 2)
  have hpn : (0 : ℝ) < 2 ^ n := by positivity
  set θ := if 0 < arg z then arg z else arg z + 2 * π with hθ
  refine mem_iUnion.2 ⟨(n, ⌈θ * 2 ^ n / (2 * π)⌉₊ - 1), ?_, ?_, ?_⟩
  · show (1 / 2 : ℝ) ^ (n + 1) < 1 - ‖z‖
    rw [one_div_pow, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hn2
    linarith
  · show 1 - ‖z‖ ≤ (1 / 2 : ℝ) ^ n
    rw [one_div_pow, le_div_iff₀ hpn]
    rw [le_div_iff₀ hδ] at hn1
    linarith
  · exact s07c_fkps_m4_arc_mem (s07c_fkps_m4_tau_mem z) n

/-- Cone containment: a tile lies in the cone of aperture `16` at every point of its arc. -/
theorem s07c_fkps_m4_tile_cone {j k : ℕ} {z : ℂ} {θ : ℝ}
    (hz : (1 / 2 : ℝ) ^ (j + 1) < 1 - ‖z‖ ∧ 1 - ‖z‖ ≤ (1 / 2 : ℝ) ^ j ∧
      (if 0 < arg z then arg z else arg z + 2 * π) ∈
        Ioc (2 * π * (k : ℝ) / 2 ^ j) (2 * π * ((k : ℝ) + 1) / 2 ^ j))
    (hθ : θ ∈ Ioc (2 * π * (k : ℝ) / 2 ^ j) (2 * π * ((k : ℝ) + 1) / 2 ^ j)) :
    z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 16 * (1 - ‖z‖) := by
  obtain ⟨h1, h2, h3⟩ := hz
  have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 1) := by positivity
  have hz1 : ‖z‖ < 1 := by linarith
  refine ⟨show z ∈ ball (0 : ℂ) 1 by rw [mem_ball_zero_iff]; exact hz1, ?_⟩
  set τ := if 0 < arg z then arg z else arg z + 2 * π with hτ
  have hd1 : ‖z - exp (τ * I)‖ = 1 - ‖z‖ := s07c_fkps_m4_tau_dist hz1.le
  have hd2 : ‖exp (τ * I) - exp (θ * I)‖ ≤ |τ - θ| := s07c_fkps_m4_exp_dist τ θ
  have hlen : |τ - θ| ≤ 2 * π * (1 / 2 : ℝ) ^ j := by
    have e : 2 * π * ((k : ℝ) + 1) / 2 ^ j - 2 * π * (k : ℝ) / 2 ^ j = 2 * π * (1 / 2 : ℝ) ^ j := by
      rw [one_div_pow]; field_simp; ring
    rw [abs_le]
    constructor <;> linarith [h3.1, h3.2, hθ.1, hθ.2]
  have hhalf : (1 / 2 : ℝ) ^ j = 2 * (1 / 2 : ℝ) ^ (j + 1) := by rw [pow_succ]; ring
  have htri := norm_sub_le_norm_sub_add_norm_sub z (exp (τ * I)) (exp (θ * I))
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

/-- Box containment: the tiles below the dyadic arc `J i k'` lie in the Carleson box
`𝔻 ∩ B(e^{i·2π(k'+1)/2^i}, 8 (1/2)^i)`. -/
theorem s07c_fkps_m4_tile_box {i j k : ℕ} (hij : i ≤ j) {z : ℂ}
    (hz : (1 / 2 : ℝ) ^ (j + 1) < 1 - ‖z‖ ∧ 1 - ‖z‖ ≤ (1 / 2 : ℝ) ^ j ∧
      (if 0 < arg z then arg z else arg z + 2 * π) ∈
        Ioc (2 * π * (k : ℝ) / 2 ^ j) (2 * π * ((k : ℝ) + 1) / 2 ^ j)) :
    z ∈ unitDisc ∩
      ball (exp (((2 * π * (((k / 2 ^ (j - i) : ℕ) : ℝ) + 1) / 2 ^ i : ℝ) : ℂ) * I))
        (8 * (1 / 2 : ℝ) ^ i) := by
  obtain ⟨h1, h2, h3⟩ := hz
  have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 1) := by positivity
  have hz1 : ‖z‖ < 1 := by linarith
  refine ⟨show z ∈ ball (0 : ℂ) 1 by rw [mem_ball_zero_iff]; exact hz1, ?_⟩
  have h3' := s07c_fkps_m4_arc_anc hij h3
  set q := k / 2 ^ (j - i) with hq
  set τ := if 0 < arg z then arg z else arg z + 2 * π with hτ
  set c : ℝ := 2 * π * ((q : ℝ) + 1) / 2 ^ i with hc
  have hd1 : ‖z - exp (τ * I)‖ = 1 - ‖z‖ := s07c_fkps_m4_tau_dist hz1.le
  have hd2 : ‖exp (τ * I) - exp (c * I)‖ ≤ |τ - c| := s07c_fkps_m4_exp_dist τ c
  have hlen : |τ - c| ≤ 2 * π * (1 / 2 : ℝ) ^ i := by
    have e : c - 2 * π * (q : ℝ) / 2 ^ i = 2 * π * (1 / 2 : ℝ) ^ i := by
      rw [hc, one_div_pow]; field_simp; ring
    rw [abs_le]
    constructor <;> linarith [h3'.1, h3'.2]
  have hji : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ i := pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
  have hpi : (0 : ℝ) < (1 / 2 : ℝ) ^ i := by positivity
  have htri := norm_sub_le_norm_sub_add_norm_sub z (exp (τ * I)) (exp (c * I))
  rw [mem_ball, dist_eq_norm]
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

/-! ### Stage B: discrete telescoping on the dyadic tree -/

theorem s07c_fkps_m4_sqrt_step_real {u a : ℝ} (hu : 0 ≤ u) (ha : 0 ≤ a) :
    2 * Real.sqrt u + a / Real.sqrt (u + a) ≤ 2 * Real.sqrt (u + a) := by
  rcases eq_or_lt_of_le (add_nonneg hu ha) with h0 | hpos
  · have hu0 : u = 0 := by linarith
    have ha0 : a = 0 := by linarith
    simp [hu0, ha0]
  · have hs := Real.sqrt_pos.2 hpos
    have hsu := Real.sq_sqrt hu
    have hsv := Real.sq_sqrt hpos.le
    have key : a / Real.sqrt (u + a) ≤ 2 * Real.sqrt (u + a) - 2 * Real.sqrt u := by
      rw [div_le_iff₀ hs]
      nlinarith [sq_nonneg (Real.sqrt (u + a) - Real.sqrt u)]
    linarith

theorem s07c_fkps_m4_sqrt_step {u a : ℝ≥0∞} (hu : u ≠ ⊤) (ha : a ≠ ⊤) :
    2 * u ^ (1 / 2 : ℝ) + a / (u + a) ^ (1 / 2 : ℝ) ≤ 2 * (u + a) ^ (1 / 2 : ℝ) := by
  rw [← ENNReal.ofReal_toReal hu, ← ENNReal.ofReal_toReal ha]
  have hu' : 0 ≤ u.toReal := ENNReal.toReal_nonneg
  have ha' : 0 ≤ a.toReal := ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_add hu' ha', ENNReal.ofReal_rpow_of_nonneg hu' (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (add_nonneg hu' ha') (by norm_num), ← Real.sqrt_eq_rpow,
    ← Real.sqrt_eq_rpow]
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (u.toReal + a.toReal)) with h0 | hpos
  · have hz : u.toReal + a.toReal = 0 := by
      rw [eq_comm, Real.sqrt_eq_zero (add_nonneg hu' ha')] at h0
      exact h0
    have hu0 : u.toReal = 0 := by linarith
    have ha0 : a.toReal = 0 := by linarith
    simp [hu0, ha0]
  · rw [← ENNReal.ofReal_div_of_pos hpos, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (div_nonneg ha' hpos.le)]
    exact ENNReal.ofReal_le_ofReal (s07c_fkps_m4_sqrt_step_real hu' ha')

/-- Telescoping I: `∑ a_j / (a_0 + ⋯ + a_j)^{1/2} ≤ 2 (∑ a_j)^{1/2}`. -/
theorem s07c_fkps_m4_tele_phi (a : ℕ → ℝ≥0∞) :
    ∑' j, a j / (∑ i ∈ Finset.range j, a i + a j) ^ (1 / 2 : ℝ) ≤
      2 * (∑' j, a j) ^ (1 / 2 : ℝ) := by
  by_cases htop : ∑' j, a j = ⊤
  · rw [htop, ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top two_ne_zero]
    exact le_top
  have hfin : ∀ n, ∑ i ∈ Finset.range n, a i ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top htop (sum_le_tsum _)
  have hpart : ∀ n, ∑ j ∈ Finset.range n, a j / (∑ i ∈ Finset.range j, a i + a j) ^ (1 / 2 : ℝ) ≤
      2 * (∑ i ∈ Finset.range n, a i) ^ (1 / 2 : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hfa : a n ≠ ⊤ := ne_top_of_le_ne_top (hfin (n + 1))
        (by rw [Finset.sum_range_succ]; exact le_add_self)
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      calc ∑ j ∈ Finset.range n, a j / (∑ i ∈ Finset.range j, a i + a j) ^ (1 / 2 : ℝ) +
            a n / (∑ i ∈ Finset.range n, a i + a n) ^ (1 / 2 : ℝ)
          ≤ 2 * (∑ i ∈ Finset.range n, a i) ^ (1 / 2 : ℝ) +
            a n / (∑ i ∈ Finset.range n, a i + a n) ^ (1 / 2 : ℝ) := by gcongr
        _ ≤ 2 * (∑ i ∈ Finset.range n, a i + a n) ^ (1 / 2 : ℝ) :=
            s07c_fkps_m4_sqrt_step (hfin n) hfa
  refine ENNReal.tsum_le_of_sum_range_le (fun n => (hpart n).trans ?_)
  gcongr
  exact sum_le_tsum _

/-- Telescoping II: `∑ ((a_0 + ⋯ + a_j)^{1/2} - (a_0 + ⋯ + a_{j-1})^{1/2}) ≤ (∑ a_j)^{1/2}`. -/
theorem s07c_fkps_m4_tele_d (a : ℕ → ℝ≥0∞) :
    ∑' j, ((∑ i ∈ Finset.range j, a i + a j) ^ (1 / 2 : ℝ) - (∑ i ∈ Finset.range j, a i) ^ (1 / 2 : ℝ)) ≤
      (∑' j, a j) ^ (1 / 2 : ℝ) := by
  have hpart : ∀ n, ∑ j ∈ Finset.range n,
      ((∑ i ∈ Finset.range j, a i + a j) ^ (1 / 2 : ℝ) - (∑ i ∈ Finset.range j, a i) ^ (1 / 2 : ℝ)) =
      (∑ i ∈ Finset.range n, a i) ^ (1 / 2 : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      exact add_tsub_cancel_of_le (ENNReal.rpow_le_rpow le_self_add (by norm_num))
  refine ENNReal.tsum_le_of_sum_range_le (fun n => ?_)
  rw [hpart n]
  gcongr
  exact sum_le_tsum _

theorem s07c_fkps_m4_idx {i j : ℕ} (k : ℕ) (hij : i ≤ j) : k / 2 ^ (j + 1 - i) = k / 2 / 2 ^ (j - i) := by
  rw [Nat.div_div_eq_div_mul, ← pow_succ']
  congr 2
  omega

/-- The parent relation for the truncated sums: `s'(j+1, k) = s(j, k/2)`. -/
theorem s07c_fkps_m4_sum_parent (α : ℕ → ℕ → ℝ≥0∞) (j k : ℕ) :
    ∑ i ∈ Finset.range (j + 1), α i (k / 2 ^ (j + 1 - i)) =
      ∑ i ∈ Finset.range j, α i (k / 2 / 2 ^ (j - i)) + α j (k / 2) := by
  rw [Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [s07c_fkps_m4_idx k (Finset.mem_range.1 hi).le]
  · congr 1
    rw [show j + 1 - j = 1 by omega, pow_one]

/-- `s(j, k) ≤ ∑_{i ≤ j} d(i, k / 2^(j-i))` with `d = s - s'`. -/
theorem s07c_fkps_m4_tele_tree (α s s' d : ℕ → ℕ → ℝ≥0∞)
    (hs : ∀ j k, s j k = (∑ i ∈ Finset.range j, α i (k / 2 ^ (j - i)) + α j k) ^ (1 / 2 : ℝ))
    (hs' : ∀ j k, s' j k = (∑ i ∈ Finset.range j, α i (k / 2 ^ (j - i))) ^ (1 / 2 : ℝ))
    (hd : ∀ j k, d j k = s j k - s' j k) :
    ∀ j k, s j k ≤ ∑ i ∈ Finset.range (j + 1), d i (k / 2 ^ (j - i)) := by
  intro j
  induction j with
  | zero =>
    intro k
    rw [Finset.sum_range_one, hd, hs', Nat.sub_self, pow_zero, Nat.div_one]
    simp
  | succ j ih =>
    intro k
    have hpar : s' (j + 1) k = s j (k / 2) := by
      rw [hs', hs, s07c_fkps_m4_sum_parent]
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, Nat.div_one]
    calc s (j + 1) k ≤ d (j + 1) k + s' (j + 1) k := by rw [hd]; exact le_tsub_add
      _ = d (j + 1) k + s j (k / 2) := by rw [hpar]
      _ ≤ d (j + 1) k + ∑ i ∈ Finset.range (j + 1), d i (k / 2 / 2 ^ (j - i)) := by
          gcongr
          exact ih _
      _ = ∑ i ∈ Finset.range (j + 1), d i (k / 2 ^ (j + 1 - i)) + d (j + 1) k := by
          rw [add_comm]
          congr 1
          refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [s07c_fkps_m4_idx k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]

/-- A finite ancestor sum as a `tsum` over the tree. -/
theorem s07c_fkps_m4_anc_tsum (f : ℕ → ℕ → ℝ≥0∞) (j k : ℕ) :
    ∑ i ∈ Finset.range (j + 1), f i (k / 2 ^ (j - i)) =
      ∑' q : ℕ × ℕ, if q.1 ≤ j ∧ q.2 = k / 2 ^ (j - q.1) then f q.1 q.2 else 0 := by
  have h1 := tsum_prod (f := fun (i k' : ℕ) =>
    if i ≤ j ∧ k' = k / 2 ^ (j - i) then f i k' else 0)
  rw [h1]
  have h2 : ∀ i : ℕ, (∑' k' : ℕ, if i ≤ j ∧ k' = k / 2 ^ (j - i) then f i k' else 0) =
      if i ≤ j then f i (k / 2 ^ (j - i)) else 0 := by
    intro i
    by_cases hi : i ≤ j
    · simp only [hi, true_and, if_true]
      exact tsum_ite_eq (k / 2 ^ (j - i)) (fun k' => f i k')
    · simp [hi]
  simp_rw [h2]
  rw [tsum_eq_sum (s := Finset.range (j + 1))]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [if_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
  · intro i hi
    rw [if_neg]
    intro h
    exact hi (Finset.mem_range.2 (Nat.lt_succ_iff.2 h))

/-- The swap: `∑_Q s_Q b_Q ≤ ∑_{Q'} d_{Q'} ∑_{Q ⊆ Q'} b_Q`. -/
theorem s07c_fkps_m4_tree_swap (s d b : ℕ → ℕ → ℝ≥0∞)
    (hle : ∀ j k, s j k ≤ ∑ i ∈ Finset.range (j + 1), d i (k / 2 ^ (j - i))) :
    ∑' p : ℕ × ℕ, s p.1 p.2 * b p.1 p.2 ≤
      ∑' q : ℕ × ℕ, d q.1 q.2 *
        ∑' p : ℕ × ℕ, if q.1 ≤ p.1 ∧ q.2 = p.2 / 2 ^ (p.1 - q.1) then b p.1 p.2 else 0 := by
  calc ∑' p : ℕ × ℕ, s p.1 p.2 * b p.1 p.2
      ≤ ∑' p : ℕ × ℕ, (∑' q : ℕ × ℕ,
          if q.1 ≤ p.1 ∧ q.2 = p.2 / 2 ^ (p.1 - q.1) then d q.1 q.2 else 0) * b p.1 p.2 := by
        refine tsum_le_tsum (fun p => mul_le_mul_left ?_ _)
        rw [← s07c_fkps_m4_anc_tsum]
        exact hle p.1 p.2
    _ = ∑' p : ℕ × ℕ, ∑' q : ℕ × ℕ,
          if q.1 ≤ p.1 ∧ q.2 = p.2 / 2 ^ (p.1 - q.1) then d q.1 q.2 * b p.1 p.2 else 0 := by
        congr 1
        ext p
        rw [← ENNReal.tsum_mul_right]
        congr 1
        ext q
        split_ifs <;> simp
    _ = ∑' q : ℕ × ℕ, ∑' p : ℕ × ℕ,
          if q.1 ≤ p.1 ∧ q.2 = p.2 / 2 ^ (p.1 - q.1) then d q.1 q.2 * b p.1 p.2 else 0 :=
        tsum_comm
    _ = _ := by
        congr 1
        ext q
        rw [← ENNReal.tsum_mul_left]
        congr 1
        ext p
        split_ifs <;> simp

/-- Sums over the arcs containing `θ` are sums along the chain `k_j(θ) = ⌈θ 2^j/2π⌉ - 1`. -/
theorem s07c_fkps_m4_chain_tsum {θ : ℝ} (hθ : θ ∈ Ioc 0 (2 * π)) (f : ℕ → ℕ → ℝ≥0∞) :
    ∑' p : ℕ × ℕ, (Ioc (2 * π * (p.2 : ℝ) / 2 ^ p.1) (2 * π * ((p.2 : ℝ) + 1) / 2 ^ p.1)).indicator
        (fun _ => f p.1 p.2) θ =
      ∑' j, f j (⌈θ * 2 ^ j / (2 * π)⌉₊ - 1) := by
  have h1 := tsum_prod (f := fun (j k : ℕ) =>
    (Ioc (2 * π * (k : ℝ) / 2 ^ j) (2 * π * ((k : ℝ) + 1) / 2 ^ j)).indicator (fun _ => f j k) θ)
  rw [h1]
  congr 1
  ext j
  rw [tsum_eq_single (⌈θ * 2 ^ j / (2 * π)⌉₊ - 1)]
  · exact Set.indicator_of_mem (s07c_fkps_m4_arc_mem hθ j) _
  · intro k hk
    rw [Set.indicator_of_notMem]
    intro hmem
    exact hk (s07c_fkps_m4_arc_uniq hmem (s07c_fkps_m4_arc_mem hθ j))

theorem s07c_fkps_m4_chain_anc {θ : ℝ} (hθ : θ ∈ Ioc 0 (2 * π)) {i j : ℕ} (hij : i ≤ j) :
    (⌈θ * 2 ^ j / (2 * π)⌉₊ - 1) / 2 ^ (j - i) = ⌈θ * 2 ^ i / (2 * π)⌉₊ - 1 :=
  s07c_fkps_m4_arc_uniq (s07c_fkps_m4_arc_anc hij (s07c_fkps_m4_arc_mem hθ j))
    (s07c_fkps_m4_arc_mem hθ i)

theorem s07c_fkps_m4_out_anc {i j k : ℕ} (hij : i ≤ j) (hk : 2 ^ j ≤ k) : 2 ^ i ≤ k / 2 ^ (j - i) := by
  rw [Nat.le_div_iff_mul_le (by positivity), ← pow_add, Nat.add_sub_cancel' hij]
  exact hk

/-! ### Stage C: Hölder steps and assembly -/

/-- A Carleson measure with norm `κ` has total mass `≤ 3κ` on `𝔻`. -/
theorem s07c_fkps_m4_disc_mass {G : ℂ → ℝ≥0∞} {κ : ℝ} (hκ : 0 ≤ κ)
    (hC : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, G z ≤ ENNReal.ofReal (κ * r)) :
    ∫⁻ z in unitDisc, G z ≤ ENNReal.ofReal (3 * κ) :=
  calc ∫⁻ z in unitDisc, G z
      ≤ ∫⁻ z in (unitDisc ∩ ball (1 : ℂ) (3 / 2)) ∪ (unitDisc ∩ ball (-1 : ℂ) (3 / 2)), G z :=
        lintegral_mono_set s07c_fkps_m4_cover
    _ ≤ (∫⁻ z in unitDisc ∩ ball (1 : ℂ) (3 / 2), G z) + ∫⁻ z in unitDisc ∩ ball (-1 : ℂ) (3 / 2), G z :=
        lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal (κ * (3 / 2)) + ENNReal.ofReal (κ * (3 / 2)) :=
        add_le_add (hC 1 (by simp) _ (by norm_num) (by norm_num)) (hC (-1) (by simp) _ (by norm_num) (by norm_num))
    _ = ENNReal.ofReal (3 * κ) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

theorem s07c_fkps_m4_div_delta (a : ℝ≥0∞) {δ c : ℝ} (hδ : 0 < δ) (hc : δ ≤ c) :
    a / ENNReal.ofReal δ ≤ ENNReal.ofReal c * (a / ENNReal.ofReal (δ ^ 2)) := by
  have h0 : ENNReal.ofReal δ ≠ 0 := (ENNReal.ofReal_pos.2 hδ).ne'
  have ht : ENNReal.ofReal δ ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.ofReal_pow hδ.le, div_eq_mul_inv, div_eq_mul_inv, ENNReal.inv_pow]
  calc a * (ENNReal.ofReal δ)⁻¹
      = (ENNReal.ofReal δ * (ENNReal.ofReal δ)⁻¹) * (a * (ENNReal.ofReal δ)⁻¹) := by
        rw [ENNReal.mul_inv_cancel h0 ht, one_mul]
    _ = ENNReal.ofReal δ * (a * (ENNReal.ofReal δ)⁻¹ ^ 2) := by ring
    _ ≤ ENNReal.ofReal c * (a * (ENNReal.ofReal δ)⁻¹ ^ 2) :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal hc) _

/-- Cauchy–Schwarz on one tile, for the measure `dA/δ`. -/
theorem s07c_fkps_m4_tile_holder {Φ Ψ : ℂ → ℝ≥0∞} (hΦ : Measurable Φ) (hΨ : Measurable Ψ)
    {S : Set ℂ} (hS : MeasurableSet S) {c : ℝ} (hSc : ∀ z ∈ S, 0 < 1 - ‖z‖ ∧ 1 - ‖z‖ ≤ c) :
    ∫⁻ z in S, Φ z * Ψ z / ENNReal.ofReal (1 - ‖z‖) ≤
      (ENNReal.ofReal c * ∫⁻ z in S, Φ z ^ 2 / ENNReal.ofReal ((1 - ‖z‖) ^ 2)) ^ (1 / 2 : ℝ) *
        (∫⁻ z in S, Ψ z ^ 2 / ENNReal.ofReal (1 - ‖z‖)) ^ (1 / 2 : ℝ) := by
  have hw : Measurable fun z : ℂ => (ENNReal.ofReal (1 - ‖z‖))⁻¹ :=
    (measurable_const.sub measurable_norm).ennreal_ofReal.inv
  have hconv : ∀ F : ℂ → ℝ≥0∞, Measurable F →
      ∫⁻ z, F z ∂((volume.restrict S).withDensity fun z : ℂ => (ENNReal.ofReal (1 - ‖z‖))⁻¹) =
        ∫⁻ z in S, F z / ENNReal.ofReal (1 - ‖z‖) := by
    intro F hF
    rw [lintegral_withDensity_eq_lintegral_mul _ hw hF]
    refine lintegral_congr (fun z => ?_)
    simp only [Pi.mul_apply]
    rw [ENNReal.div_eq_inv_mul]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq
    ((volume.restrict S).withDensity fun z : ℂ => (ENNReal.ofReal (1 - ‖z‖))⁻¹)
    Real.HolderConjugate.two_two hΦ.aemeasurable hΨ.aemeasurable
  simp only [Pi.mul_apply, ENNReal.rpow_two] at hH
  rw [show (∫⁻ z, Φ z * Ψ z ∂((volume.restrict S).withDensity fun z : ℂ => (ENNReal.ofReal (1 - ‖z‖))⁻¹)) =
      ∫⁻ z in S, Φ z * Ψ z / ENNReal.ofReal (1 - ‖z‖) from hconv (fun z => Φ z * Ψ z) (hΦ.mul hΨ),
    show (∫⁻ z, Φ z ^ 2 ∂((volume.restrict S).withDensity fun z : ℂ => (ENNReal.ofReal (1 - ‖z‖))⁻¹)) =
      ∫⁻ z in S, Φ z ^ 2 / ENNReal.ofReal (1 - ‖z‖) from hconv (fun z => Φ z ^ 2) (hΦ.pow_const 2),
    show (∫⁻ z, Ψ z ^ 2 ∂((volume.restrict S).withDensity fun z : ℂ => (ENNReal.ofReal (1 - ‖z‖))⁻¹)) =
      ∫⁻ z in S, Ψ z ^ 2 / ENNReal.ofReal (1 - ‖z‖) from hconv (fun z => Ψ z ^ 2) (hΨ.pow_const 2)] at hH
  refine hH.trans ?_
  gcongr
  calc ∫⁻ z in S, Φ z ^ 2 / ENNReal.ofReal (1 - ‖z‖)
      ≤ ∫⁻ z in S, ENNReal.ofReal c * (Φ z ^ 2 / ENNReal.ofReal ((1 - ‖z‖) ^ 2)) :=
        setLIntegral_mono' hS (fun z hz => s07c_fkps_m4_div_delta _ (hSc z hz).1 (hSc z hz).2)
    _ = ENNReal.ofReal c * ∫⁻ z in S, Φ z ^ 2 / ENNReal.ofReal ((1 - ‖z‖) ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem s07c_fkps_m4_weight_step {x b s : ℝ≥0∞} (hx : s = 0 → x = 0) (h : s ≠ ⊤ ∨ b = 0) :
    x ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ) ≤ (x / s) ^ (1 / 2 : ℝ) * (s * b) ^ (1 / 2 : ℝ) := by
  rcases eq_or_ne s 0 with hs0 | hs0
  · rw [hx hs0, ENNReal.zero_rpow_of_pos (by norm_num), zero_mul]
    exact zero_le
  rcases h with hst | hb0
  · rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ← mul_assoc, ENNReal.div_mul_cancel hs0 hst]
  · rw [hb0, ENNReal.zero_rpow_of_pos (by norm_num), mul_zero]
    exact zero_le

theorem s07c_fkps_m4_count_holder (u v : ℕ × ℕ → ℝ≥0∞) :
    ∑' p, u p ^ (1 / 2 : ℝ) * v p ^ (1 / 2 : ℝ) ≤
      (∑' p, u p) ^ (1 / 2 : ℝ) * (∑' p, v p) ^ (1 / 2 : ℝ) := by
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure (ℕ × ℕ))
    Real.HolderConjugate.two_two (measurable_of_countable (fun p => u p ^ (1 / 2 : ℝ))).aemeasurable
    (measurable_of_countable (fun p => v p ^ (1 / 2 : ℝ))).aemeasurable
  have e : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_mul]; norm_num
  simp only [lintegral_count, Pi.mul_apply, e] at hH
  exact hH

theorem s07c_fkps_m4_sqrt_prod {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (I : ℝ≥0∞) :
    (ENNReal.ofReal a * I) ^ (1 / 2 : ℝ) * (ENNReal.ofReal b * I) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt (a * b)) * I := by
  have hI : I ^ (1 / 2 : ℝ) * I ^ (1 / 2 : ℝ) = I := by
    rw [← pow_two, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg ha (by norm_num), ENNReal.ofReal_rpow_of_nonneg hb (by norm_num),
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_mul ha, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  calc ENNReal.ofReal √a * I ^ (1 / 2 : ℝ) * (ENNReal.ofReal √b * I ^ (1 / 2 : ℝ))
      = ENNReal.ofReal √a * ENNReal.ofReal √b * (I ^ (1 / 2 : ℝ) * I ^ (1 / 2 : ℝ)) := by ring
    _ = ENNReal.ofReal √a * ENNReal.ofReal √b * I := by rw [hI]

/-- M4.2: tent-space duality on `𝔻` (Coifman–Meyer–Stein, `T¹₂ × T^∞₂`). If `Ψ² dA/δ` is a Carleson measure
with norm `≤ κ`, then `∫_𝔻 Φ Ψ dA/δ ≤ C √κ ∫_𝕋 A(Φ)`, where `A(Φ)(θ)² = ∫_{cone 16 θ} Φ² dA/δ²`. -/
theorem s07c_fkps_m4_duality : ∃ C : ℝ, 0 < C ∧ ∀ (Φ Ψ : ℂ → ℝ≥0∞) (κ : ℝ),
    Measurable Φ → Measurable Ψ → 0 ≤ κ →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, Ψ z ^ 2 / ENNReal.ofReal (1 - ‖z‖) ≤ ENNReal.ofReal (κ * r)) →
    ∫⁻ z in unitDisc, Φ z * Ψ z / ENNReal.ofReal (1 - ‖z‖) ≤
      ENNReal.ofReal (C * Real.sqrt κ) *
        ∫⁻ θ in Ioc (0 : ℝ) (2 * π),
          (∫⁻ z in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 16 * (1 - ‖z‖)},
            Φ z ^ 2 / ENNReal.ofReal ((1 - ‖z‖) ^ 2)) ^ (1 / 2 : ℝ) := by
  refine ⟨2, by norm_num, ?_⟩
  intro Φ Ψ κ hΦ hΨ hκ hC
  classical
  -- arcs, tiles and the chain
  obtain ⟨J, hJ⟩ : ∃ J : ℕ → ℕ → Set ℝ, ∀ j k,
      J j k = Ioc (2 * π * (k : ℝ) / 2 ^ j) (2 * π * ((k : ℝ) + 1) / 2 ^ j) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℕ → Set ℂ, ∀ j k, T j k =
      {z : ℂ | (1 / 2 : ℝ) ^ (j + 1) < 1 - ‖z‖ ∧ 1 - ‖z‖ ≤ (1 / 2 : ℝ) ^ j ∧
        (if 0 < arg z then arg z else arg z + 2 * π) ∈
          Ioc (2 * π * (k : ℝ) / 2 ^ j) (2 * π * ((k : ℝ) + 1) / 2 ^ j)} := ⟨_, fun _ _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ → ℕ → ℕ, ∀ θ j, c θ j = ⌈θ * 2 ^ j / (2 * π)⌉₊ - 1 := ⟨_, fun _ _ => rfl⟩
  have hJm : ∀ j k, MeasurableSet (J j k) := fun j k => by rw [hJ]; exact measurableSet_Ioc
  have hTm : ∀ j k, MeasurableSet (T j k) := fun j k => by
    rw [hT]; exact s07c_fkps_m4_tile_measurable j k
  have hTd : Pairwise (Function.onFun Disjoint fun p : ℕ × ℕ => T p.1 p.2) := by
    intro p q hpq
    have h := s07c_fkps_m4_tile_disjoint hpq
    simp only [Function.onFun] at h ⊢
    rw [hT, hT]
    exact h
  have hTc : unitDisc ⊆ ⋃ p : ℕ × ℕ, T p.1 p.2 := by
    simp_rw [hT]; exact s07c_fkps_m4_tile_cover
  have hTsub : ∀ j k, ∀ z ∈ T j k, 0 < 1 - ‖z‖ ∧ 1 - ‖z‖ ≤ (1 / 2 : ℝ) ^ j := by
    intro j k z hz
    rw [hT] at hz
    exact ⟨lt_of_le_of_lt (by positivity) hz.1, hz.2.1⟩
  have hTe : ∀ j k, 2 ^ j ≤ k → T j k = ∅ := by
    intro j k hk
    rw [hT, Set.eq_empty_iff_forall_notMem]
    intro z hz
    have h := s07c_fkps_m4_arc_out hk
    rw [Set.eq_empty_iff_forall_notMem] at h
    exact h _ ⟨hz.2.2, s07c_fkps_m4_tau_mem z⟩
  have hchain : ∀ θ ∈ Ioc 0 (2 * π), ∀ f : ℕ → ℕ → ℝ≥0∞,
      ∑' p : ℕ × ℕ, (J p.1 p.2).indicator (fun _ => f p.1 p.2) θ = ∑' j, f j (c θ j) := by
    intro θ hθ f
    simp_rw [hJ, hc]
    exact s07c_fkps_m4_chain_tsum hθ f
  have hcanc : ∀ θ ∈ Ioc 0 (2 * π), ∀ i j, i ≤ j → c θ j / 2 ^ (j - i) = c θ i := by
    intro θ hθ i j hij
    rw [hc, hc]
    exact s07c_fkps_m4_chain_anc hθ hij
  have hcmem : ∀ θ ∈ Ioc 0 (2 * π), ∀ j, θ ∈ J j (c θ j) := by
    intro θ hθ j
    rw [hJ, hc]
    exact s07c_fkps_m4_arc_mem hθ j
  -- tile quantities
  obtain ⟨α, hα⟩ : ∃ α : ℕ → ℕ → ℝ≥0∞, ∀ j k,
      α j k = ∫⁻ z in T j k, Φ z ^ 2 / ENNReal.ofReal ((1 - ‖z‖) ^ 2) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℕ → ℝ≥0∞, ∀ j k,
      b j k = ∫⁻ z in T j k, Ψ z ^ 2 / ENNReal.ofReal (1 - ‖z‖) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℕ → ℝ≥0∞, ∀ j k,
      s j k = (∑ i ∈ Finset.range j, α i (k / 2 ^ (j - i)) + α j k) ^ (1 / 2 : ℝ) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s' : ℕ → ℕ → ℝ≥0∞, ∀ j k,
      s' j k = (∑ i ∈ Finset.range j, α i (k / 2 ^ (j - i))) ^ (1 / 2 : ℝ) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℕ → ℝ≥0∞, ∀ j k, d j k = s j k - s' j k := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Sd, hSd⟩ : ∃ Sd : ℝ → ℝ≥0∞, ∀ θ,
      Sd θ = (∑' p : ℕ × ℕ, (J p.1 p.2).indicator (fun _ => α p.1 p.2) θ) ^ (1 / 2 : ℝ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ → ℝ≥0∞, ∀ θ,
      A θ = (∫⁻ z in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 16 * (1 - ‖z‖)},
        Φ z ^ 2 / ENNReal.ofReal ((1 - ‖z‖) ^ 2)) ^ (1 / 2 : ℝ) := ⟨_, fun _ => rfl⟩
  have hIA : (∫⁻ θ in Ioc (0 : ℝ) (2 * π),
      (∫⁻ z in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 16 * (1 - ‖z‖)},
        Φ z ^ 2 / ENNReal.ofReal ((1 - ‖z‖) ^ 2)) ^ (1 / 2 : ℝ)) = ∫⁻ θ in Ioc (0 : ℝ) (2 * π), A θ := by
    simp_rw [hA]
  rw [hIA]
  -- vanishing outside `(0, 2π]`
  have hα0 : ∀ j k, 2 ^ j ≤ k → α j k = 0 := by
    intro j k hk; rw [hα, hTe j k hk]; simp
  have hs0 : ∀ j k, 2 ^ j ≤ k → s j k = 0 ∧ s' j k = 0 := by
    intro j k hk
    have hsum : ∑ i ∈ Finset.range j, α i (k / 2 ^ (j - i)) = 0 :=
      Finset.sum_eq_zero (fun i hi => hα0 _ _ (s07c_fkps_m4_out_anc (Finset.mem_range.1 hi).le hk))
    rw [hs, hs', hsum, hα0 j k hk, add_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
    exact ⟨rfl, rfl⟩
  have hd0 : ∀ j k, 2 ^ j ≤ k → d j k = 0 := by
    intro j k hk; rw [hd, (hs0 j k hk).1]; simp
  -- the chain form of `s`, `s'`, `Sd`
  have hcs : ∀ θ ∈ Ioc 0 (2 * π), ∀ j,
      s j (c θ j) = (∑ i ∈ Finset.range j, α i (c θ i) + α j (c θ j)) ^ (1 / 2 : ℝ) ∧
      s' j (c θ j) = (∑ i ∈ Finset.range j, α i (c θ i)) ^ (1 / 2 : ℝ) := by
    intro θ hθ j
    have hsum : ∑ i ∈ Finset.range j, α i (c θ j / 2 ^ (j - i)) = ∑ i ∈ Finset.range j, α i (c θ i) :=
      Finset.sum_congr rfl (fun i hi => by rw [hcanc θ hθ i j (Finset.mem_range.1 hi).le])
    rw [hs, hs', hsum]
    exact ⟨rfl, rfl⟩
  have hSdc : ∀ θ ∈ Ioc 0 (2 * π), Sd θ = (∑' j, α j (c θ j)) ^ (1 / 2 : ℝ) := by
    intro θ hθ
    rw [hSd, hchain θ hθ α]
  -- `Sd ≤ A`: the dyadic cone lies in the cone of aperture `16`
  have hF5 : ∀ θ, Sd θ ≤ A θ := by
    intro θ
    rw [hSd, hA]
    gcongr
    have e : ∀ p : ℕ × ℕ, (J p.1 p.2).indicator (fun _ => α p.1 p.2) θ =
        ∫⁻ z in (if θ ∈ J p.1 p.2 then T p.1 p.2 else ∅), Φ z ^ 2 / ENNReal.ofReal ((1 - ‖z‖) ^ 2) := by
      intro p
      split_ifs with h
      · rw [Set.indicator_of_mem h, hα]
      · rw [Set.indicator_of_notMem h]; simp
    calc ∑' p : ℕ × ℕ, (J p.1 p.2).indicator (fun _ => α p.1 p.2) θ
        = ∑' p : ℕ × ℕ, ∫⁻ z in (if θ ∈ J p.1 p.2 then T p.1 p.2 else ∅),
            Φ z ^ 2 / ENNReal.ofReal ((1 - ‖z‖) ^ 2) := tsum_congr e
      _ = ∫⁻ z in ⋃ p : ℕ × ℕ, (if θ ∈ J p.1 p.2 then T p.1 p.2 else ∅),
            Φ z ^ 2 / ENNReal.ofReal ((1 - ‖z‖) ^ 2) := by
          rw [lintegral_iUnion]
          · intro p; split_ifs
            · exact hTm _ _
            · exact MeasurableSet.empty
          · intro p p' hpp'
            have h := hTd hpp'
            simp only [Function.onFun] at h ⊢
            split_ifs
            · exact h
            all_goals simp
      _ ≤ _ := by
          refine lintegral_mono_set (fun z hz => ?_)
          obtain ⟨p, hp⟩ := mem_iUnion.1 hz
          split_ifs at hp with h
          · rw [hT] at hp
            rw [hJ] at h
            exact s07c_fkps_m4_tile_cone hp h
          · simp at hp
  -- the two telescoping bounds along the chain
  have hX_pt : ∀ θ ∈ Ioc 0 (2 * π),
      ∑' p : ℕ × ℕ, (J p.1 p.2).indicator (fun _ => α p.1 p.2 / s p.1 p.2) θ ≤ 2 * Sd θ := by
    intro θ hθ
    calc ∑' p : ℕ × ℕ, (J p.1 p.2).indicator (fun _ => α p.1 p.2 / s p.1 p.2) θ
        = ∑' j, α j (c θ j) / s j (c θ j) := hchain θ hθ (fun j k => α j k / s j k)
      _ = ∑' j, α j (c θ j) / (∑ i ∈ Finset.range j, α i (c θ i) + α j (c θ j)) ^ (1 / 2 : ℝ) := by
          congr 1; ext j; rw [(hcs θ hθ j).1]
      _ ≤ 2 * (∑' j, α j (c θ j)) ^ (1 / 2 : ℝ) := s07c_fkps_m4_tele_phi (fun j => α j (c θ j))
      _ = 2 * Sd θ := by rw [hSdc θ hθ]
  have hY_pt : ∀ θ ∈ Ioc 0 (2 * π),
      ∑' p : ℕ × ℕ, (J p.1 p.2).indicator (fun _ => d p.1 p.2) θ ≤ Sd θ := by
    intro θ hθ
    calc ∑' p : ℕ × ℕ, (J p.1 p.2).indicator (fun _ => d p.1 p.2) θ
        = ∑' j, d j (c θ j) := hchain θ hθ d
      _ = ∑' j, ((∑ i ∈ Finset.range j, α i (c θ i) + α j (c θ j)) ^ (1 / 2 : ℝ) -
            (∑ i ∈ Finset.range j, α i (c θ i)) ^ (1 / 2 : ℝ)) := by
          congr 1; ext j; rw [hd, (hcs θ hθ j).1, (hcs θ hθ j).2]
      _ ≤ (∑' j, α j (c θ j)) ^ (1 / 2 : ℝ) := s07c_fkps_m4_tele_d (fun j => α j (c θ j))
      _ = Sd θ := by rw [hSdc θ hθ]
  -- arc integrals
  have harc : ∀ (p : ℕ × ℕ) (e : ℝ≥0∞), ∫⁻ θ in Ioc 0 (2 * π), (J p.1 p.2).indicator (fun _ => e) θ =
      e * volume (J p.1 p.2 ∩ Ioc 0 (2 * π)) := by
    intro p e
    rw [lintegral_indicator_const (hJm p.1 p.2), Measure.restrict_apply (hJm p.1 p.2)]
  -- the `Φ`-sum
  have hX : ∑' p : ℕ × ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ p.1) * α p.1 p.2 / s p.1 p.2 ≤
      ENNReal.ofReal (1 / π) * ∫⁻ θ in Ioc 0 (2 * π), Sd θ := by
    have hterm : ∀ p : ℕ × ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ p.1) * α p.1 p.2 / s p.1 p.2 =
        ENNReal.ofReal (1 / (2 * π)) *
          ∫⁻ θ in Ioc 0 (2 * π), (J p.1 p.2).indicator (fun _ => α p.1 p.2 / s p.1 p.2) θ := by
      intro p
      rw [harc]
      rcases lt_or_ge p.2 (2 ^ p.1) with hk | hk
      · obtain ⟨e1, e2⟩ := s07c_fkps_m4_arc_vol hk
        rw [hJ, e1, e2]
        have hr : ENNReal.ofReal ((1 / 2 : ℝ) ^ p.1) =
            ENNReal.ofReal (1 / (2 * π)) * ENNReal.ofReal (2 * π / 2 ^ p.1) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [one_div_pow]
          field_simp
        rw [mul_div_assoc, hr]
        ring
      · rw [hα0 _ _ hk]
        simp
    calc ∑' p : ℕ × ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ p.1) * α p.1 p.2 / s p.1 p.2
        = ∑' p : ℕ × ℕ, ENNReal.ofReal (1 / (2 * π)) *
            ∫⁻ θ in Ioc 0 (2 * π), (J p.1 p.2).indicator (fun _ => α p.1 p.2 / s p.1 p.2) θ :=
          tsum_congr hterm
      _ = ENNReal.ofReal (1 / (2 * π)) * ∑' p : ℕ × ℕ,
            ∫⁻ θ in Ioc 0 (2 * π), (J p.1 p.2).indicator (fun _ => α p.1 p.2 / s p.1 p.2) θ :=
          ENNReal.tsum_mul_left
      _ = ENNReal.ofReal (1 / (2 * π)) * ∫⁻ θ in Ioc 0 (2 * π),
            ∑' p : ℕ × ℕ, (J p.1 p.2).indicator (fun _ => α p.1 p.2 / s p.1 p.2) θ := by
          congr 1
          exact (lintegral_tsum (fun p : ℕ × ℕ => (measurable_const.indicator (hJm p.1 p.2)).aemeasurable)).symm
      _ ≤ ENNReal.ofReal (1 / (2 * π)) * ∫⁻ θ in Ioc 0 (2 * π), 2 * Sd θ :=
          mul_le_mul_right (setLIntegral_mono' measurableSet_Ioc hX_pt) _
      _ = ENNReal.ofReal (1 / π) * ∫⁻ θ in Ioc 0 (2 * π), Sd θ := by
          rw [lintegral_const_mul' 2 _ (by simp), ← mul_assoc]
          congr 1
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  -- the Carleson box bound
  have hbox : ∀ q : ℕ × ℕ,
      (∑' p : ℕ × ℕ, if q.1 ≤ p.1 ∧ q.2 = p.2 / 2 ^ (p.1 - q.1) then b p.1 p.2 else 0) ≤
        ENNReal.ofReal (24 * κ * (1 / 2 : ℝ) ^ q.1) := by
    intro q
    have e1 : (∑' p : ℕ × ℕ, if q.1 ≤ p.1 ∧ q.2 = p.2 / 2 ^ (p.1 - q.1) then b p.1 p.2 else 0) =
        ∫⁻ z in ⋃ p : ℕ × ℕ, (if q.1 ≤ p.1 ∧ q.2 = p.2 / 2 ^ (p.1 - q.1) then T p.1 p.2 else ∅),
          Ψ z ^ 2 / ENNReal.ofReal (1 - ‖z‖) := by
      rw [lintegral_iUnion]
      · congr 1
        ext p
        split_ifs
        · rw [hb]
        · simp
      · intro p; split_ifs
        · exact hTm _ _
        · exact MeasurableSet.empty
      · intro p p' hpp'
        have h := hTd hpp'
        simp only [Function.onFun] at h ⊢
        split_ifs
        · exact h
        all_goals simp
    have hsub : (⋃ p : ℕ × ℕ, (if q.1 ≤ p.1 ∧ q.2 = p.2 / 2 ^ (p.1 - q.1) then T p.1 p.2 else ∅)) ⊆
        unitDisc ∩ ball (exp (((2 * π * ((q.2 : ℝ) + 1) / 2 ^ q.1 : ℝ) : ℂ) * I)) (8 * (1 / 2 : ℝ) ^ q.1) := by
      intro z hz
      obtain ⟨p, hp⟩ := mem_iUnion.1 hz
      split_ifs at hp with hdesc
      · rw [hT] at hp
        have h := s07c_fkps_m4_tile_box hdesc.1 hp
        rw [← hdesc.2] at h
        exact h
      · simp at hp
    rw [e1]
    have hpi : (0 : ℝ) < (1 / 2 : ℝ) ^ q.1 := by positivity
    rcases le_or_gt 3 q.1 with hi | hi
    · have h3 : (1 / 2 : ℝ) ^ q.1 ≤ (1 / 2 : ℝ) ^ 3 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hi
      calc _ ≤ ∫⁻ z in unitDisc ∩ ball (exp (((2 * π * ((q.2 : ℝ) + 1) / 2 ^ q.1 : ℝ) : ℂ) * I))
              (8 * (1 / 2 : ℝ) ^ q.1), Ψ z ^ 2 / ENNReal.ofReal (1 - ‖z‖) := lintegral_mono_set hsub
        _ ≤ ENNReal.ofReal (κ * (8 * (1 / 2 : ℝ) ^ q.1)) :=
            hC _ (by rw [mem_sphere_zero_iff_norm]; exact Complex.norm_exp_ofReal_mul_I _) _
              (by positivity) (by norm_num at h3 ⊢; linarith)
        _ ≤ ENNReal.ofReal (24 * κ * (1 / 2 : ℝ) ^ q.1) :=
            ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hκ hpi.le])
    · have h2 : (1 / 2 : ℝ) ^ 2 ≤ (1 / 2 : ℝ) ^ q.1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      calc _ ≤ ∫⁻ z in unitDisc, Ψ z ^ 2 / ENNReal.ofReal (1 - ‖z‖) :=
            lintegral_mono_set (hsub.trans inter_subset_left)
        _ ≤ ENNReal.ofReal (3 * κ) := s07c_fkps_m4_disc_mass hκ hC
        _ ≤ ENNReal.ofReal (24 * κ * (1 / 2 : ℝ) ^ q.1) :=
            ENNReal.ofReal_le_ofReal (by norm_num at h2; nlinarith)
  -- the `Ψ`-sum
  have hY : ∑' p : ℕ × ℕ, s p.1 p.2 * b p.1 p.2 ≤
      ENNReal.ofReal (12 * κ / π) * ∫⁻ θ in Ioc 0 (2 * π), Sd θ := by
    have hle := s07c_fkps_m4_tele_tree α s s' d hs hs' hd
    have hterm : ∀ q : ℕ × ℕ, d q.1 q.2 * ENNReal.ofReal (24 * κ * (1 / 2 : ℝ) ^ q.1) =
        ENNReal.ofReal (12 * κ / π) *
          ∫⁻ θ in Ioc 0 (2 * π), (J q.1 q.2).indicator (fun _ => d q.1 q.2) θ := by
      intro q
      rw [harc]
      rcases lt_or_ge q.2 (2 ^ q.1) with hk | hk
      · obtain ⟨e1, e2⟩ := s07c_fkps_m4_arc_vol hk
        rw [hJ, e1, e2]
        have hr : ENNReal.ofReal (24 * κ * (1 / 2 : ℝ) ^ q.1) =
            ENNReal.ofReal (12 * κ / π) * ENNReal.ofReal (2 * π / 2 ^ q.1) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [one_div_pow]
          field_simp
          ring
        rw [hr]
        ring
      · rw [hd0 _ _ hk]
        simp
    calc ∑' p : ℕ × ℕ, s p.1 p.2 * b p.1 p.2
        ≤ ∑' q : ℕ × ℕ, d q.1 q.2 *
            ∑' p : ℕ × ℕ, (if q.1 ≤ p.1 ∧ q.2 = p.2 / 2 ^ (p.1 - q.1) then b p.1 p.2 else 0) :=
          s07c_fkps_m4_tree_swap s d b hle
      _ ≤ ∑' q : ℕ × ℕ, d q.1 q.2 * ENNReal.ofReal (24 * κ * (1 / 2 : ℝ) ^ q.1) :=
          tsum_le_tsum (fun q => mul_le_mul_right (hbox q) _)
      _ = ∑' q : ℕ × ℕ, ENNReal.ofReal (12 * κ / π) *
            ∫⁻ θ in Ioc 0 (2 * π), (J q.1 q.2).indicator (fun _ => d q.1 q.2) θ := tsum_congr hterm
      _ = ENNReal.ofReal (12 * κ / π) * ∑' q : ℕ × ℕ,
            ∫⁻ θ in Ioc 0 (2 * π), (J q.1 q.2).indicator (fun _ => d q.1 q.2) θ := ENNReal.tsum_mul_left
      _ = ENNReal.ofReal (12 * κ / π) * ∫⁻ θ in Ioc 0 (2 * π),
            ∑' q : ℕ × ℕ, (J q.1 q.2).indicator (fun _ => d q.1 q.2) θ := by
          congr 1
          exact (lintegral_tsum (fun q : ℕ × ℕ => (measurable_const.indicator (hJm q.1 q.2)).aemeasurable)).symm
      _ ≤ ENNReal.ofReal (12 * κ / π) * ∫⁻ θ in Ioc 0 (2 * π), Sd θ :=
          mul_le_mul_right (setLIntegral_mono' measurableSet_Ioc hY_pt) _
  -- the trivial case `κ > 0`, `∫ A = ∞`
  by_cases htriv : 0 < κ ∧ ∫⁻ θ in Ioc (0 : ℝ) (2 * π), A θ = ⊤
  · rw [htriv.2, ENNReal.mul_top (ENNReal.ofReal_pos.2 (mul_pos two_pos (Real.sqrt_pos.2 htriv.1))).ne']
    exact le_top
  have hgood : ∀ p : ℕ × ℕ, s p.1 p.2 ≠ ⊤ ∨ b p.1 p.2 = 0 := by
    intro p
    by_cases hκ0 : κ = 0
    · right
      have h1 : b p.1 p.2 ≤ ∑' p' : ℕ × ℕ,
          (if p.1 ≤ p'.1 ∧ p.2 = p'.2 / 2 ^ (p'.1 - p.1) then b p'.1 p'.2 else 0) := by
        refine le_trans (le_of_eq ?_) (le_tsum _ p)
        simp
      have h2 := h1.trans (hbox p)
      rw [hκ0] at h2
      simpa using h2
    · left
      have hIAf : ∫⁻ θ in Ioc (0 : ℝ) (2 * π), A θ ≠ ⊤ :=
        fun h => htriv ⟨lt_of_le_of_ne hκ (Ne.symm hκ0), h⟩
      rcases lt_or_ge p.2 (2 ^ p.1) with hk | hk
      · obtain ⟨e1, e2⟩ := s07c_fkps_m4_arc_vol hk
        have hJsub : J p.1 p.2 ⊆ Ioc 0 (2 * π) := by rw [hJ, ← e1]; exact inter_subset_right
        have hex : ∃ θ ∈ J p.1 p.2, A θ ≠ ⊤ := by
          by_contra hne
          push Not at hne
          apply hIAf
          have hJtop : ∫⁻ θ in J p.1 p.2, A θ = ⊤ := by
            rw [setLIntegral_congr_fun (hJm _ _) (fun θ hθ => hne θ hθ), setLIntegral_const, hJ, e2,
              ENNReal.top_mul (ENNReal.ofReal_pos.2 (by positivity)).ne']
          exact eq_top_iff.2 (hJtop ▸ lintegral_mono_set hJsub)
        obtain ⟨θ, hθJ, hθA⟩ := hex
        have hθ : θ ∈ Ioc 0 (2 * π) := hJsub hθJ
        have hcp : c θ p.1 = p.2 := by
          have h1 := hcmem θ hθ p.1
          rw [hJ] at h1 hθJ
          exact s07c_fkps_m4_arc_uniq h1 hθJ
        have hsS : s p.1 p.2 ≤ Sd θ := by
          rw [← hcp, (hcs θ hθ p.1).1, hSdc θ hθ]
          gcongr
          rw [← Finset.sum_range_succ (fun i => α i (c θ i))]
          exact sum_le_tsum _
        exact ne_top_of_le_ne_top hθA (hsS.trans (hF5 θ))
      · rw [(hs0 _ _ hk).1]
        exact ENNReal.zero_ne_top
  -- assembly
  have hL1 : ∀ p : ℕ × ℕ, ∫⁻ z in T p.1 p.2, Φ z * Ψ z / ENNReal.ofReal (1 - ‖z‖) ≤
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ p.1) * α p.1 p.2 / s p.1 p.2) ^ (1 / 2 : ℝ) *
        (s p.1 p.2 * b p.1 p.2) ^ (1 / 2 : ℝ) := by
    intro p
    refine (s07c_fkps_m4_tile_holder hΦ hΨ (hTm _ _) (hTsub p.1 p.2)).trans ?_
    rw [← hα, ← hb]
    refine s07c_fkps_m4_weight_step ?_ (hgood p)
    intro h0
    rw [hs] at h0
    rcases ENNReal.rpow_eq_zero_iff.1 h0 with ⟨h, _⟩ | ⟨_, h⟩
    · rw [(add_eq_zero.1 h).2, mul_zero]
    · norm_num at h
  have hIS : ∫⁻ θ in Ioc (0 : ℝ) (2 * π), Sd θ ≤ ∫⁻ θ in Ioc (0 : ℝ) (2 * π), A θ :=
    lintegral_mono (fun θ => hF5 θ)
  have hπ3 : (3 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_three]
  have hreal : Real.sqrt (1 / π * (12 * κ / π)) ≤ 2 * Real.sqrt κ := by
    have h4 : 1 / π * (12 * κ / π) ≤ 4 * κ := by
      rw [show 1 / π * (12 * κ / π) = 12 * κ / π ^ 2 by field_simp, div_le_iff₀ (by positivity)]
      nlinarith
    calc Real.sqrt (1 / π * (12 * κ / π)) ≤ Real.sqrt (4 * κ) := Real.sqrt_le_sqrt h4
      _ = 2 * Real.sqrt κ := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  calc ∫⁻ z in unitDisc, Φ z * Ψ z / ENNReal.ofReal (1 - ‖z‖)
      ≤ ∑' p : ℕ × ℕ, ∫⁻ z in T p.1 p.2, Φ z * Ψ z / ENNReal.ofReal (1 - ‖z‖) :=
        (lintegral_mono_set hTc).trans (lintegral_iUnion_le _ _)
    _ ≤ ∑' p : ℕ × ℕ, (ENNReal.ofReal ((1 / 2 : ℝ) ^ p.1) * α p.1 p.2 / s p.1 p.2) ^ (1 / 2 : ℝ) *
          (s p.1 p.2 * b p.1 p.2) ^ (1 / 2 : ℝ) := tsum_le_tsum hL1
    _ ≤ (∑' p : ℕ × ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ p.1) * α p.1 p.2 / s p.1 p.2) ^ (1 / 2 : ℝ) *
          (∑' p : ℕ × ℕ, s p.1 p.2 * b p.1 p.2) ^ (1 / 2 : ℝ) :=
        s07c_fkps_m4_count_holder (fun p => ENNReal.ofReal ((1 / 2 : ℝ) ^ p.1) * α p.1 p.2 / s p.1 p.2)
          (fun p => s p.1 p.2 * b p.1 p.2)
    _ ≤ (ENNReal.ofReal (1 / π) * ∫⁻ θ in Ioc 0 (2 * π), Sd θ) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal (12 * κ / π) * ∫⁻ θ in Ioc 0 (2 * π), Sd θ) ^ (1 / 2 : ℝ) := by
        gcongr
    _ = ENNReal.ofReal (Real.sqrt (1 / π * (12 * κ / π))) * ∫⁻ θ in Ioc 0 (2 * π), Sd θ :=
        s07c_fkps_m4_sqrt_prod (by positivity) (by positivity) _
    _ ≤ ENNReal.ofReal (2 * Real.sqrt κ) * ∫⁻ θ in Ioc (0 : ℝ) (2 * π), A θ := by
        gcongr

/-- M4.3 helper: Cauchy–Schwarz with weight `k`, `(∫ k h)² ≤ (∫ k)(∫ k h²)`. -/
theorem s07c_fkps_m4_cs {μ : Measure ℂ} {k h : ℂ → ℝ≥0∞} (hk : Measurable k) (hh : Measurable h) :
    (∫⁻ Y, k Y * h Y ∂μ) ^ 2 ≤ (∫⁻ Y, k Y ∂μ) * ∫⁻ Y, k Y * h Y ^ 2 ∂μ := by
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.withDensity k) Real.HolderConjugate.two_two
    (aemeasurable_const (b := (1 : ℝ≥0∞))) hh.aemeasurable
  have e1 : ∫⁻ a, h a ∂(μ.withDensity k) = ∫⁻ a, k a * h a ∂μ :=
    lintegral_withDensity_eq_lintegral_mul _ hk hh
  have e2 : ∫⁻ _a, (1 : ℝ≥0∞) ∂(μ.withDensity k) = ∫⁻ a, k a ∂μ := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hk measurable_const]
    simp only [Pi.mul_apply, mul_one]
  have e3 : ∫⁻ a, h a ^ 2 ∂(μ.withDensity k) = ∫⁻ a, k a * h a ^ 2 ∂μ :=
    lintegral_withDensity_eq_lintegral_mul _ hk (hh.pow_const 2)
  simp only [Pi.mul_apply, one_mul, ENNReal.rpow_two, one_pow] at hH
  rw [e1, e2, e3] at hH
  have hsq : ∀ a : ℝ≥0∞, (a ^ (1 / 2 : ℝ)) ^ 2 = a := fun a => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  calc (∫⁻ Y, k Y * h Y ∂μ) ^ 2
      ≤ ((∫⁻ Y, k Y ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ Y, k Y * h Y ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = _ := by rw [mul_pow, hsq, hsq]

/-- M4.3 helper: `∫_{B(z, ρ)} |ζ - z|⁻¹ = 2πρ` (from `LiZhongQC.lintegral_ball_sub_enorm_rpow_neg`). -/
theorem s07c_fkps_m4_ball_inv (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ ζ in ball z ρ, ‖ζ - z‖ₑ ^ (-1 : ℝ) = ENNReal.ofReal (2 * π * ρ) := by
  rw [lintegral_ball_sub_enorm_rpow_neg (a := 1) (by norm_num) hρ z,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  norm_num

/-- M4.3 helper (near part, Schur test): for `h ≥ 0` measurable,
`∫_{B(X, δ/4)} (∫_{B(X, δ/2)} |Y - Z|⁻¹ h(Y) dY)² dZ ≤ (2πδ)² ∫_{B(X, δ/2)} h²`. -/
theorem s07c_fkps_m4_near_schur {h : ℂ → ℝ≥0∞} (hh : Measurable h) (X : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ Z in ball X (δ / 4), (∫⁻ Y in ball X (δ / 2), ‖Y - Z‖ₑ ^ (-1 : ℝ) * h Y) ^ 2 ≤
      ENNReal.ofReal (2 * π * δ) ^ 2 * ∫⁻ Y in ball X (δ / 2), h Y ^ 2 := by
  have hk : ∀ Z : ℂ, Measurable fun Y : ℂ => ‖Y - Z‖ₑ ^ (-1 : ℝ) := fun Z =>
    ((measurable_id.sub_const Z).enorm).pow_const _
  have hk' : ∀ Y : ℂ, Measurable fun Z : ℂ => ‖Y - Z‖ₑ ^ (-1 : ℝ) := fun Y =>
    ((measurable_const.sub measurable_id).enorm).pow_const _
  have hrev : ∀ Y Z : ℂ, ‖Y - Z‖ₑ = ‖Z - Y‖ₑ := fun Y Z => by
    rw [← ofReal_norm, ← ofReal_norm, norm_sub_rev Y Z]
  have hkb : ∀ Z ∈ ball X (δ / 4),
      ∫⁻ Y in ball X (δ / 2), ‖Y - Z‖ₑ ^ (-1 : ℝ) ≤ ENNReal.ofReal (2 * π * δ) := by
    intro Z hZ
    rw [← s07c_fkps_m4_ball_inv Z hδ]
    refine lintegral_mono_set ?_
    intro Y hY
    rw [mem_ball, dist_eq_norm] at hY hZ ⊢
    have := norm_sub_le_norm_sub_add_norm_sub Y X Z
    rw [norm_sub_rev X Z] at this
    linarith
  have hkb' : ∀ Y ∈ ball X (δ / 2),
      ∫⁻ Z in ball X (δ / 4), ‖Y - Z‖ₑ ^ (-1 : ℝ) ≤ ENNReal.ofReal (2 * π * δ) := by
    intro Y hY
    rw [← s07c_fkps_m4_ball_inv Y hδ]
    calc ∫⁻ Z in ball X (δ / 4), ‖Y - Z‖ₑ ^ (-1 : ℝ)
        = ∫⁻ Z in ball X (δ / 4), ‖Z - Y‖ₑ ^ (-1 : ℝ) := lintegral_congr (fun Z => by rw [hrev])
      _ ≤ _ := by
        refine lintegral_mono_set ?_
        intro Z hZ
        rw [mem_ball, dist_eq_norm] at hY hZ ⊢
        have := norm_sub_le_norm_sub_add_norm_sub Z X Y
        rw [norm_sub_rev X Y] at this
        linarith
  calc ∫⁻ Z in ball X (δ / 4), (∫⁻ Y in ball X (δ / 2), ‖Y - Z‖ₑ ^ (-1 : ℝ) * h Y) ^ 2
      ≤ ∫⁻ Z in ball X (δ / 4), ENNReal.ofReal (2 * π * δ) *
          ∫⁻ Y in ball X (δ / 2), ‖Y - Z‖ₑ ^ (-1 : ℝ) * h Y ^ 2 :=
        setLIntegral_mono' measurableSet_ball (fun Z hZ =>
          (s07c_fkps_m4_cs (hk Z) hh).trans (mul_le_mul_left (hkb Z hZ) _))
    _ = ENNReal.ofReal (2 * π * δ) * ∫⁻ Z in ball X (δ / 4),
          ∫⁻ Y in ball X (δ / 2), ‖Y - Z‖ₑ ^ (-1 : ℝ) * h Y ^ 2 :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (2 * π * δ) * ∫⁻ Y in ball X (δ / 2),
          (∫⁻ Z in ball X (δ / 4), ‖Y - Z‖ₑ ^ (-1 : ℝ)) * h Y ^ 2 := by
        congr 1
        rw [lintegral_lintegral_swap]
        · exact lintegral_congr (fun Y => lintegral_mul_const _ (hk' Y))
        · exact ((((measurable_snd.sub measurable_fst).enorm).pow_const _).mul
            ((hh.comp measurable_snd).pow_const 2)).aemeasurable
    _ ≤ ENNReal.ofReal (2 * π * δ) * ∫⁻ Y in ball X (δ / 2), ENNReal.ofReal (2 * π * δ) * h Y ^ 2 :=
        mul_le_mul_right (setLIntegral_mono' measurableSet_ball
          (fun Y hY => mul_le_mul_left (hkb' Y hY) _)) _
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, sq]

/-- M4.3 helper: `|Z - Y| ≤ |1 - Z Ȳ|` on the closed disc. -/
theorem s07c_fkps_m4_conj_bound {Z Y : ℂ} (hZ : ‖Z‖ ≤ 1) (hY : ‖Y‖ ≤ 1) :
    ‖Z - Y‖ ≤ ‖1 - Z * conj Y‖ := by
  have e : ‖1 - Z * conj Y‖ ^ 2 = ‖Z - Y‖ ^ 2 + (1 - ‖Z‖ ^ 2) * (1 - ‖Y‖ ^ 2) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
    ring
  have h0 : 0 ≤ (1 - ‖Z‖ ^ 2) * (1 - ‖Y‖ ^ 2) :=
    mul_nonneg (by nlinarith [norm_nonneg Z]) (by nlinarith [norm_nonneg Y])
  nlinarith [norm_nonneg (Z - Y), norm_nonneg (1 - Z * conj Y)]

/-- M4.3 helper: the Green-gradient kernel is `≤ 1/(π |Z - Y|)` for `Z ∈ 𝔻`, `|Y| ≤ 1`. -/
theorem s07c_fkps_m4_kernel_near {Z Y : ℂ} (hZ : ‖Z‖ < 1) (hY : ‖Y‖ ≤ 1) :
    ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / (2 * π * ‖Z - Y‖ * ‖1 - Z * conj Y‖)) ≤
      ENNReal.ofReal π⁻¹ * ‖Y - Z‖ₑ ^ (-1 : ℝ) := by
  rcases eq_or_ne Y Z with rfl | hne
  · simp
  have hd : 0 < ‖Z - Y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne.symm)
  have hc : 1 - ‖Z‖ ≤ ‖1 - Z * conj Y‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) (Z * conj Y)
    have h2 : ‖Z * conj Y‖ ≤ ‖Z‖ := by
      rw [norm_mul, Complex.norm_conj]; nlinarith [norm_nonneg Z]
    rw [norm_one] at h1; linarith
  have hc0 : 0 < ‖1 - Z * conj Y‖ := by linarith
  rw [← ofReal_norm, norm_sub_rev Y Z, ENNReal.rpow_neg_one, ← ENNReal.ofReal_inv_of_pos hd,
    ← ENNReal.ofReal_mul (inv_nonneg.2 Real.pi_pos.le)]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_iff₀ (by positivity)]
  have : π⁻¹ * ‖Z - Y‖⁻¹ * (2 * π * ‖Z - Y‖ * ‖1 - Z * conj Y‖) =
      (π⁻¹ * π) * (‖Z - Y‖⁻¹ * ‖Z - Y‖) * (2 * ‖1 - Z * conj Y‖) := by ring
  rw [this, inv_mul_cancel₀ Real.pi_ne_zero, inv_mul_cancel₀ hd.ne']
  nlinarith [norm_nonneg Z]

/-- M4.3 helper: away from `X`, on the cone of aperture `16` at `t`, the Green-gradient kernel at
`Z ∈ B(X, δ_X/4)` is `≤ 9604 P(X, t)`. -/
theorem s07c_fkps_m4_kernel_far {X Z Y : ℂ} {t : ℝ} (hX : ‖X‖ < 1) (hZ : ‖Z - X‖ < (1 - ‖X‖) / 4)
    (hY : ‖Y‖ < 1) (hXY : (1 - ‖X‖) / 2 ≤ ‖Y - X‖) (hYt : ‖Y - exp (t * I)‖ < 16 * (1 - ‖Y‖)) :
    (1 - ‖Z‖ ^ 2) / (2 * π * ‖Z - Y‖ * ‖1 - Z * conj Y‖) ≤
      9604 * ((1 - ‖X‖ ^ 2) / ‖exp (t * I) - X‖ ^ 2) := by
  have h1 := norm_sub_norm_le Z X
  have hZn : ‖Z‖ < 1 := by linarith
  have hd : ‖Y - X‖ / 2 ≤ ‖Z - Y‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub Y Z X
    rw [norm_sub_rev Y Z] at this; linarith
  have hc : ‖Z - Y‖ ≤ ‖1 - Z * conj Y‖ := s07c_fkps_m4_conj_bound hZn.le hY.le
  have hYX := norm_sub_norm_le X Y
  rw [norm_sub_rev X Y] at hYX
  have he : ‖exp (t * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I t
  have ha : ‖exp (t * I) - X‖ ≤ 49 * ‖Y - X‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub (exp (t * I)) Y X
    rw [norm_sub_rev (exp (t * I)) Y] at this; linarith
  have ha0 : 1 - ‖X‖ ≤ ‖exp (t * I) - X‖ := by
    have := norm_sub_norm_le (exp (t * I)) X
    rw [he] at this; linarith
  have hδ : 0 < 1 - ‖X‖ := by linarith
  have hd0 : 0 < ‖Z - Y‖ := by linarith
  have hQ : 0 ≤ 1 - ‖X‖ ^ 2 := by nlinarith [norm_nonneg X]
  have hN : 1 - ‖Z‖ ^ 2 ≤ 5 / 2 * (1 - ‖X‖ ^ 2) := by
    have h1' := norm_sub_norm_le X Z
    rw [norm_sub_rev X Z] at h1'
    have e1 : 1 - ‖Z‖ ^ 2 ≤ 2 * (1 - ‖Z‖) := by nlinarith [sq_nonneg (1 - ‖Z‖)]
    have e2 : 1 - ‖X‖ ≤ 1 - ‖X‖ ^ 2 := by nlinarith [norm_nonneg X]
    linarith
  have hN0 : 0 ≤ 1 - ‖Z‖ ^ 2 := by nlinarith [norm_nonneg Z]
  have ha2 : ‖exp (t * I) - X‖ ^ 2 ≤ 9604 * (‖Z - Y‖ * ‖1 - Z * conj Y‖) := by
    have h98 : ‖exp (t * I) - X‖ ≤ 98 * ‖Z - Y‖ := by linarith
    nlinarith [norm_nonneg (exp (t * I) - X)]
  rw [← mul_div_assoc, div_le_div_iff₀ (mul_pos (mul_pos (by positivity) hd0) (by linarith))
    (pow_pos (by linarith) 2)]
  have hp : 0 ≤ (1 - ‖X‖ ^ 2) * (‖Z - Y‖ * ‖1 - Z * conj Y‖) :=
    mul_nonneg hQ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc (1 - ‖Z‖ ^ 2) * ‖exp (t * I) - X‖ ^ 2
      ≤ (5 / 2 * (1 - ‖X‖ ^ 2)) * (9604 * (‖Z - Y‖ * ‖1 - Z * conj Y‖)) :=
        mul_le_mul hN ha2 (sq_nonneg _) (by linarith)
    _ ≤ 9604 * (1 - ‖X‖ ^ 2) * (2 * π * ‖Z - Y‖ * ‖1 - Z * conj Y‖) := by
        nlinarith [mul_nonneg hp (show (0 : ℝ) ≤ 2 * π - 5 / 2 by linarith [Real.pi_gt_three])]

/-- M4.3 helper: measurability of the Green-gradient kernel in `Y`. -/
theorem s07c_fkps_m4_kernel_meas (Z : ℂ) :
    Measurable fun Y : ℂ => ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / (2 * π * ‖Z - Y‖ * ‖1 - Z * conj Y‖)) :=
  (measurable_const.div ((measurable_const.mul (measurable_const.sub measurable_id).norm).mul
    (measurable_const.sub (measurable_const.mul Complex.continuous_conj.measurable)).norm)).ennreal_ofReal

/-- M4.3 helper (far part): for `Z ∈ B(X, δ_X/4)`, the part of the absolute potential over
`𝔻 \ B(X, δ_X/2)` is `≤ C √ε · 9604 ∫ P(X, t) S_g(t) dt`, by the tent-space duality. -/
theorem s07c_fkps_m4_far_pt {C2 : ℝ}
    (hD : ∀ (Φ Ψ : ℂ → ℝ≥0∞) (κ : ℝ), Measurable Φ → Measurable Ψ → 0 ≤ κ →
      (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
        ∫⁻ z in unitDisc ∩ ball ζ r, Ψ z ^ 2 / ENNReal.ofReal (1 - ‖z‖) ≤ ENNReal.ofReal (κ * r)) →
      ∫⁻ z in unitDisc, Φ z * Ψ z / ENNReal.ofReal (1 - ‖z‖) ≤
        ENNReal.ofReal (C2 * Real.sqrt κ) *
          ∫⁻ θ in Ioc (0 : ℝ) (2 * π),
            (∫⁻ z in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 16 * (1 - ‖z‖)},
              Φ z ^ 2 / ENNReal.ofReal ((1 - ‖z‖) ^ 2)) ^ (1 / 2 : ℝ))
    {g : ℂ → ℂ} {Ψ : ℂ → ℝ≥0∞} {ε : ℝ} (hg : Measurable g) (hΨ : Measurable Ψ) (hε : 0 ≤ ε)
    (hcar : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, Ψ z ^ 2 / ENNReal.ofReal (1 - ‖z‖) ≤ ENNReal.ofReal (ε * r))
    {X Z : ℂ} (hX : ‖X‖ < 1) (hZ : ‖Z - X‖ < (1 - ‖X‖) / 4) :
    ∫⁻ Y in unitDisc, (ball X ((1 - ‖X‖) / 2))ᶜ.indicator (fun Y =>
        ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / (2 * π * ‖Z - Y‖ * ‖1 - Z * conj Y‖)) *
          (Ψ Y * ‖g Y‖₊)) Y ≤
      ENNReal.ofReal (C2 * Real.sqrt ε) * (ENNReal.ofReal 9604 *
        ∫⁻ t in Ioc (0 : ℝ) (2 * π), ENNReal.ofReal ((1 - ‖X‖ ^ 2) / ‖exp (t * I) - X‖ ^ 2) *
          (∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (t * I)‖ < 16 * (1 - ‖z‖)},
            (‖g Y‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ)) := by
  have hK := s07c_fkps_m4_kernel_meas Z
  set Φ : ℂ → ℝ≥0∞ := (ball X ((1 - ‖X‖) / 2))ᶜ.indicator (fun Y =>
    ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / (2 * π * ‖Z - Y‖ * ‖1 - Z * conj Y‖)) *
      ENNReal.ofReal (1 - ‖Y‖) * ‖g Y‖₊) with hΦdef
  have hΦ : Measurable Φ :=
    ((hK.mul (measurable_const.sub measurable_norm).ennreal_ofReal).mul
      hg.nnnorm.coe_nnreal_ennreal).indicator measurableSet_ball.compl
  have hmain := hD Φ Ψ ε hΦ hΨ hε hcar
  have hsq' : ∀ a : ℝ≥0∞, (a ^ 2) ^ (1 / 2 : ℝ) = a := fun a => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  calc ∫⁻ Y in unitDisc, (ball X ((1 - ‖X‖) / 2))ᶜ.indicator (fun Y =>
        ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / (2 * π * ‖Z - Y‖ * ‖1 - Z * conj Y‖)) *
          (Ψ Y * ‖g Y‖₊)) Y
      = ∫⁻ Y in unitDisc, Φ Y * Ψ Y / ENNReal.ofReal (1 - ‖Y‖) := by
        refine setLIntegral_congr_fun measurableSet_ball (fun Y hY => ?_)
        have hY1 : ‖Y‖ < 1 := mem_ball_zero_iff.1 hY
        have hδY : 0 < 1 - ‖Y‖ := by linarith
        by_cases hYB : Y ∈ ball X ((1 - ‖X‖) / 2)
        · have : Y ∉ (ball X ((1 - ‖X‖) / 2))ᶜ := fun h => h hYB
          simp only [hΦdef, indicator_of_notMem this, zero_mul, ENNReal.zero_div]
        · have : Y ∈ (ball X ((1 - ‖X‖) / 2))ᶜ := hYB
          simp only [hΦdef, indicator_of_mem this]
          generalize ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / (2 * π * ‖Z - Y‖ * ‖1 - Z * conj Y‖)) = k
          rw [show k * ENNReal.ofReal (1 - ‖Y‖) * (‖g Y‖₊ : ℝ≥0∞) * Ψ Y =
              k * (Ψ Y * ‖g Y‖₊) * ENNReal.ofReal (1 - ‖Y‖) by ring,
            ENNReal.mul_div_cancel_right (by simpa using hδY) ENNReal.ofReal_ne_top]
    _ ≤ _ := hmain
    _ ≤ _ := by
        refine mul_le_mul_right ?_ _
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_mono' measurableSet_Ioc (fun t _ => ?_)
        have hcone : MeasurableSet {z : ℂ | z ∈ unitDisc ∧ ‖z - exp (t * I)‖ < 16 * (1 - ‖z‖)} :=
          measurableSet_ball.inter (measurableSet_lt (measurable_id.sub_const _).norm
            (measurable_const.mul (measurable_const.sub measurable_norm)))
        have hpt : ∀ Y ∈ {z : ℂ | z ∈ unitDisc ∧ ‖z - exp (t * I)‖ < 16 * (1 - ‖z‖)},
            Φ Y ^ 2 / ENNReal.ofReal ((1 - ‖Y‖) ^ 2) ≤
              ENNReal.ofReal (9604 * ((1 - ‖X‖ ^ 2) / ‖exp (t * I) - X‖ ^ 2)) ^ 2 *
                (‖g Y‖₊ : ℝ≥0∞) ^ 2 := by
          intro Y hY
          obtain ⟨hY𝔻, hYt⟩ := hY
          have hY1 : ‖Y‖ < 1 := mem_ball_zero_iff.1 hY𝔻
          have hδY : 0 < 1 - ‖Y‖ := by linarith
          by_cases hYB : Y ∈ ball X ((1 - ‖X‖) / 2)
          · have : Y ∉ (ball X ((1 - ‖X‖) / 2))ᶜ := fun h => h hYB
            simp only [hΦdef, indicator_of_notMem this]
            simp
          · have : Y ∈ (ball X ((1 - ‖X‖) / 2))ᶜ := hYB
            have hXY : (1 - ‖X‖) / 2 ≤ ‖Y - X‖ := by
              rw [mem_ball, dist_eq_norm] at hYB; exact not_lt.1 hYB
            have hk := ENNReal.ofReal_le_ofReal (s07c_fkps_m4_kernel_far hX hZ hY1 hXY hYt)
            simp only [hΦdef, indicator_of_mem this]
            generalize ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / (2 * π * ‖Z - Y‖ * ‖1 - Z * conj Y‖)) = k at hk ⊢
            rw [ENNReal.ofReal_pow hδY.le,
              show (k * ENNReal.ofReal (1 - ‖Y‖) * (‖g Y‖₊ : ℝ≥0∞)) ^ 2 =
                (k * (‖g Y‖₊ : ℝ≥0∞)) ^ 2 * ENNReal.ofReal (1 - ‖Y‖) ^ 2 by ring,
              ENNReal.mul_div_cancel_right (pow_ne_zero 2 (by simpa using hδY))
                (ENNReal.pow_ne_top ENNReal.ofReal_ne_top), mul_pow]
            gcongr
        calc (∫⁻ z in {z : ℂ | z ∈ unitDisc ∧ ‖z - exp (t * I)‖ < 16 * (1 - ‖z‖)},
              Φ z ^ 2 / ENNReal.ofReal ((1 - ‖z‖) ^ 2)) ^ (1 / 2 : ℝ)
            ≤ (∫⁻ z in {z : ℂ | z ∈ unitDisc ∧ ‖z - exp (t * I)‖ < 16 * (1 - ‖z‖)},
                ENNReal.ofReal (9604 * ((1 - ‖X‖ ^ 2) / ‖exp (t * I) - X‖ ^ 2)) ^ 2 *
                  (‖g z‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) :=
              ENNReal.rpow_le_rpow (setLIntegral_mono' hcone hpt) (by norm_num)
          _ = ENNReal.ofReal (9604 * ((1 - ‖X‖ ^ 2) / ‖exp (t * I) - X‖ ^ 2)) *
                (∫⁻ z in {z : ℂ | z ∈ unitDisc ∧ ‖z - exp (t * I)‖ < 16 * (1 - ‖z‖)},
                  (‖g z‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) := by
              rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
                ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hsq']
          _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), mul_assoc]

/-- M4.3 core (aperture-parametrised FKP Lemma 2.9, `Ñ F` part): for `X` in the cone of aperture `α` at `θ` and
`β ≥ 2α + 1`, the Whitney `L²` average of the absolute potential at `X` is `≤ C ε (S_β(θ)² + P[S₁₆](X)²)`, with `C`
independent of `α, β`. `s07c_fkps_m4_ntF` is the case `α = 2`, `β = 16`; `s07c_fkps_m5_ntF16` is `α = 16`, `β = 34`. -/
theorem s07c_fkps_m4_ntF_core : ∃ C : ℝ, 0 < C ∧ ∀ (α β : ℝ), 0 < α → 2 * α + 1 ≤ β →
    ∀ (g V : ℂ → ℂ) (m : ℂ → ℝ) (ε : ℝ),
    AEMeasurable g → AEMeasurable V → AEMeasurable m → (∀ z, 0 ≤ m z) → 0 ≤ ε →
    (∀ᵐ z, z ∈ unitDisc → ‖V z‖ ≤ m z * ‖g z‖) →
    (∀ᵐ z, z ∈ unitDisc → m z ≤ Real.sqrt ε) →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (m z ^ 2 / (1 - ‖z‖)) ≤ ENNReal.ofReal (ε * r)) →
    ∀ (θ : ℝ) (X : ℂ), X ∈ unitDisc → ‖X - exp (θ * I)‖ < α * (1 - ‖X‖) →
      (∫⁻ Z in ball X ((1 - ‖X‖) / 4),
          (∫⁻ Y in unitDisc,
            ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / (2 * π * ‖Z - Y‖ * ‖1 - Z * conj Y‖)) * ‖V Y‖₊) ^ 2) /
          ENNReal.ofReal ((1 - ‖X‖) ^ 2) ≤
        ENNReal.ofReal (C * ε) *
          ((∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < β * (1 - ‖z‖)}, (‖g Y‖₊ : ℝ≥0∞) ^ 2) +
            (∫⁻ t in Ioc (0 : ℝ) (2 * π),
              ENNReal.ofReal ((1 - ‖X‖ ^ 2) / ‖exp (t * I) - X‖ ^ 2) *
                (∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (t * I)‖ < 16 * (1 - ‖z‖)},
                  (‖g Y‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ)) ^ 2) := by
  obtain ⟨C2, hC2, hD⟩ := s07c_fkps_m4_duality
  refine ⟨8 + 9604 ^ 2 * C2 ^ 2 * π, by positivity, ?_⟩
  intro α β hα hαβ g V m ε hg hV hm hm0 hε hVm hmle hcar θ X hX hXθ
  have hX1 : ‖X‖ < 1 := mem_ball_zero_iff.1 hX
  have hδ : 0 < 1 - ‖X‖ := by linarith
  have h𝔻 : MeasurableSet unitDisc := measurableSet_ball
  -- measurable representatives
  have hg' : Measurable (hg.mk g) := hg.measurable_mk
  have hgg : g =ᵐ[volume] hg.mk g := hg.ae_eq_mk
  set Ψ : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal |hm.mk m z| with hΨdef
  have hΨ : Measurable Ψ := (continuous_abs.measurable.comp hm.measurable_mk).ennreal_ofReal
  have hmΨ : ∀ᵐ z, ENNReal.ofReal (m z) = Ψ z := by
    filter_upwards [hm.ae_eq_mk] with z hz
    simp only [hΨdef, ← hz, abs_of_nonneg (hm0 z)]
  have hcarΨ : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, Ψ z ^ 2 / ENNReal.ofReal (1 - ‖z‖) ≤ ENNReal.ofReal (ε * r) := by
    intro ζ hζ r hr hr2
    refine le_trans (le_of_eq ?_) (hcar ζ hζ r hr hr2)
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem (h𝔻.inter measurableSet_ball), ae_restrict_of_ae hmΨ]
      with z hz hzΨ
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz.1
    rw [ENNReal.ofReal_div_of_pos (by linarith), ENNReal.ofReal_pow (hm0 z), hzΨ]
  have hVΨ : ∀ᵐ Y ∂volume.restrict unitDisc, (‖V Y‖₊ : ℝ≥0∞) ≤ Ψ Y * ‖hg.mk g Y‖₊ := by
    filter_upwards [ae_restrict_mem h𝔻, ae_restrict_of_ae hVm, ae_restrict_of_ae hgg,
      ae_restrict_of_ae hmΨ] with Y hY h1 h2 h3
    rw [← h3, ← h2, ← enorm_eq_nnnorm, ← enorm_eq_nnnorm, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_mul (hm0 Y)]
    exact ENNReal.ofReal_le_ofReal (h1 hY)
  have hΨle : ∀ᵐ Y ∂volume.restrict unitDisc, Ψ Y ≤ ENNReal.ofReal (Real.sqrt ε) := by
    filter_upwards [ae_restrict_mem h𝔻, ae_restrict_of_ae hmle, ae_restrict_of_ae hmΨ]
      with Y hY h1 h3
    rw [← h3]; exact ENNReal.ofReal_le_ofReal (h1 hY)
  -- geometry
  have hBsub : ball X ((1 - ‖X‖) / 2) ⊆ unitDisc := by
    intro Y hY
    rw [mem_ball, dist_eq_norm] at hY
    show Y ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff]
    have := norm_sub_norm_le Y X
    linarith
  have hBcone : ball X ((1 - ‖X‖) / 2) ⊆
      {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < β * (1 - ‖z‖)} := by
    intro Y hY
    refine ⟨hBsub hY, ?_⟩
    rw [mem_ball, dist_eq_norm] at hY
    have h1 := norm_sub_le_norm_sub_add_norm_sub Y X (exp (θ * I))
    have h2 := norm_sub_norm_le Y X
    have hβ0 : 0 < β := by linarith
    have h3 : (1 - ‖X‖) / 2 < 1 - ‖Y‖ := by linarith
    have h4 : (2 * α + 1) * (1 - ‖X‖) ≤ β * (1 - ‖X‖) := mul_le_mul_of_nonneg_right hαβ hδ.le
    have h5 : β * ((1 - ‖X‖) / 2) < β * (1 - ‖Y‖) := mul_lt_mul_of_pos_left h3 hβ0
    nlinarith
  have hSg : ∀ t : ℝ,
      ∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (t * I)‖ < 16 * (1 - ‖z‖)}, (‖hg.mk g Y‖₊ : ℝ≥0∞) ^ 2 =
        ∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (t * I)‖ < 16 * (1 - ‖z‖)}, (‖g Y‖₊ : ℝ≥0∞) ^ 2 :=
    fun t => lintegral_congr_ae (ae_restrict_of_ae (hgg.mono fun Y h => by simp only [h]))
  have hAg : ∫⁻ Y in ball X ((1 - ‖X‖) / 2), (‖hg.mk g Y‖₊ : ℝ≥0∞) ^ 2 ≤
      ∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < β * (1 - ‖z‖)}, (‖g Y‖₊ : ℝ≥0∞) ^ 2 := by
    rw [show (∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < β * (1 - ‖z‖)}, (‖g Y‖₊ : ℝ≥0∞) ^ 2) =
        ∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < β * (1 - ‖z‖)}, (‖hg.mk g Y‖₊ : ℝ≥0∞) ^ 2 from
      lintegral_congr_ae (ae_restrict_of_ae (hgg.mono fun Y h => by simp only [h]))]
    exact lintegral_mono_set hBcone
  set A := ∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < β * (1 - ‖z‖)},
    (‖g Y‖₊ : ℝ≥0∞) ^ 2 with hAdef
  set P := ∫⁻ t in Ioc (0 : ℝ) (2 * π),
    ENNReal.ofReal ((1 - ‖X‖ ^ 2) / ‖exp (t * I) - X‖ ^ 2) *
      (∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (t * I)‖ < 16 * (1 - ‖z‖)},
        (‖g Y‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) with hPdef
  have hP' : ∫⁻ t in Ioc (0 : ℝ) (2 * π),
      ENNReal.ofReal ((1 - ‖X‖ ^ 2) / ‖exp (t * I) - X‖ ^ 2) *
        (∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (t * I)‖ < 16 * (1 - ‖z‖)},
          (‖hg.mk g Y‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) = P :=
    lintegral_congr (fun t => by rw [hSg t])
  set cF := ENNReal.ofReal (C2 * Real.sqrt ε) * (ENNReal.ofReal 9604 * P) with hcF
  set a := ENNReal.ofReal (π⁻¹ * Real.sqrt ε) with ha
  -- pointwise split
  have hpt : ∀ Z ∈ ball X ((1 - ‖X‖) / 4),
      ∫⁻ Y in unitDisc,
          ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / (2 * π * ‖Z - Y‖ * ‖1 - Z * conj Y‖)) * ‖V Y‖₊ ≤
        a * (∫⁻ Y in ball X ((1 - ‖X‖) / 2), ‖Y - Z‖ₑ ^ (-1 : ℝ) * ‖hg.mk g Y‖₊) + cF := by
    intro Z hZ
    have hZX : ‖Z - X‖ < (1 - ‖X‖) / 4 := by rw [mem_ball, dist_eq_norm] at hZ; exact hZ
    have hZ1 : ‖Z‖ < 1 := by have := norm_sub_norm_le Z X; linarith
    set f : ℂ → ℝ≥0∞ := fun Y =>
      ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / (2 * π * ‖Z - Y‖ * ‖1 - Z * conj Y‖)) *
        (Ψ Y * ‖hg.mk g Y‖₊) with hfdef
    have hf : Measurable f :=
      (s07c_fkps_m4_kernel_meas Z).mul (hΨ.mul hg'.nnnorm.coe_nnreal_ennreal)
    calc ∫⁻ Y in unitDisc,
          ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / (2 * π * ‖Z - Y‖ * ‖1 - Z * conj Y‖)) * ‖V Y‖₊
        ≤ ∫⁻ Y in unitDisc, f Y := lintegral_mono_ae (hVΨ.mono fun Y h => mul_le_mul_right h _)
      _ = ∫⁻ Y in unitDisc, ((ball X ((1 - ‖X‖) / 2)).indicator f Y +
            (ball X ((1 - ‖X‖) / 2))ᶜ.indicator f Y) :=
          lintegral_congr (fun Y => (indicator_self_add_compl_apply _ _ _).symm)
      _ = (∫⁻ Y in unitDisc, (ball X ((1 - ‖X‖) / 2)).indicator f Y) +
            ∫⁻ Y in unitDisc, (ball X ((1 - ‖X‖) / 2))ᶜ.indicator f Y :=
          lintegral_add_left (hf.indicator measurableSet_ball) _
      _ ≤ _ := by
          refine add_le_add ?_ ?_
          · calc ∫⁻ Y in unitDisc, (ball X ((1 - ‖X‖) / 2)).indicator f Y
                ≤ ∫⁻ Y, (ball X ((1 - ‖X‖) / 2)).indicator f Y := setLIntegral_le_lintegral _ _
              _ = ∫⁻ Y in ball X ((1 - ‖X‖) / 2), f Y := lintegral_indicator measurableSet_ball _
              _ ≤ ∫⁻ Y in ball X ((1 - ‖X‖) / 2), a * (‖Y - Z‖ₑ ^ (-1 : ℝ) * ‖hg.mk g Y‖₊) := by
                  refine lintegral_mono_ae ?_
                  filter_upwards [ae_restrict_mem measurableSet_ball,
                    ae_restrict_of_ae_restrict_of_subset hBsub hΨle] with Y hYB hYΨ
                  have hY1 : ‖Y‖ ≤ 1 := (mem_ball_zero_iff.1 (hBsub hYB)).le
                  calc f Y ≤ (ENNReal.ofReal π⁻¹ * ‖Y - Z‖ₑ ^ (-1 : ℝ)) *
                        (ENNReal.ofReal (Real.sqrt ε) * ‖hg.mk g Y‖₊) :=
                        mul_le_mul' (s07c_fkps_m4_kernel_near hZ1 hY1) (mul_le_mul_left hYΨ _)
                    _ = a * (‖Y - Z‖ₑ ^ (-1 : ℝ) * ‖hg.mk g Y‖₊) := by
                        rw [ha, ENNReal.ofReal_mul (inv_nonneg.2 Real.pi_pos.le)]; ring
              _ = a * ∫⁻ Y in ball X ((1 - ‖X‖) / 2), ‖Y - Z‖ₑ ^ (-1 : ℝ) * ‖hg.mk g Y‖₊ :=
                  lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          · refine (s07c_fkps_m4_far_pt hD hg' hΨ hε hcarΨ hX1 hZX).trans (le_of_eq ?_)
            rw [hP']
  -- integrate
  have hsq_add : ∀ x y : ℝ≥0∞, (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
    intro x y
    have := ENNReal.rpow_add_le_mul_rpow_add_rpow x y (p := 2) (by norm_num)
    simp only [ENNReal.rpow_two] at this
    rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one, mul_add] at this
    exact this
  have hq : (0 : ℝ) ≤ (1 - ‖X‖) / 4 := by linarith
  have hvol : volume (ball X ((1 - ‖X‖) / 4)) = ENNReal.ofReal (π * ((1 - ‖X‖) / 4) ^ 2) := by
    rw [Complex.volume_ball, ← ENNReal.ofReal_pow hq, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1; ring
  have hCε : (0 : ℝ) ≤ (8 + 9604 ^ 2 * C2 ^ 2 * π) * ε := by positivity
  have e1 : 2 * a ^ 2 * (ENNReal.ofReal (2 * π * (1 - ‖X‖)) ^ 2 * A) =
      ENNReal.ofReal (8 * ε * (1 - ‖X‖) ^ 2) * A := by
    rw [show (2 : ℝ≥0∞) * a ^ 2 * (ENNReal.ofReal (2 * π * (1 - ‖X‖)) ^ 2 * A) =
        (ENNReal.ofReal 2 * a ^ 2 * ENNReal.ofReal (2 * π * (1 - ‖X‖)) ^ 2) * A by
          rw [ENNReal.ofReal_ofNat]; ring]
    rw [ha, ← ENNReal.ofReal_pow (mul_nonneg (inv_nonneg.2 Real.pi_pos.le) (Real.sqrt_nonneg ε)),
      ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 * π * (1 - ‖X‖)),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (π⁻¹ * Real.sqrt ε) ^ 2)]
    congr 2
    rw [show 2 * (π⁻¹ * Real.sqrt ε) ^ 2 * (2 * π * (1 - ‖X‖)) ^ 2 =
        8 * (π⁻¹ * π) ^ 2 * Real.sqrt ε ^ 2 * (1 - ‖X‖) ^ 2 by ring,
      inv_mul_cancel₀ Real.pi_ne_zero, Real.sq_sqrt hε]
    ring
  have e2 : 2 * cF ^ 2 * ENNReal.ofReal (π * ((1 - ‖X‖) / 4) ^ 2) =
      ENNReal.ofReal (9604 ^ 2 * C2 ^ 2 * π * ε * (1 - ‖X‖) ^ 2 / 8) * P ^ 2 := by
    have hc0 : (0 : ℝ) ≤ C2 * Real.sqrt ε := mul_nonneg hC2.le (Real.sqrt_nonneg ε)
    rw [hcF, show (2 : ℝ≥0∞) * (ENNReal.ofReal (C2 * Real.sqrt ε) * (ENNReal.ofReal 9604 * P)) ^ 2 *
        ENNReal.ofReal (π * ((1 - ‖X‖) / 4) ^ 2) =
        (ENNReal.ofReal 2 * ENNReal.ofReal (C2 * Real.sqrt ε) ^ 2 * ENNReal.ofReal 9604 ^ 2 *
          ENNReal.ofReal (π * ((1 - ‖X‖) / 4) ^ 2)) * P ^ 2 by
        rw [ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]; ring]
    rw [← ENNReal.ofReal_pow hc0, ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 9604),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (C2 * Real.sqrt ε) ^ 2),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (C2 * Real.sqrt ε) ^ 2 * 9604 ^ 2)]
    congr 2
    rw [mul_pow, Real.sq_sqrt hε]
    ring
  have e3 : ENNReal.ofReal ((8 + 9604 ^ 2 * C2 ^ 2 * π) * ε) * (A + P ^ 2) *
        ENNReal.ofReal ((1 - ‖X‖) ^ 2) =
      ENNReal.ofReal ((8 + 9604 ^ 2 * C2 ^ 2 * π) * ε * (1 - ‖X‖) ^ 2) * A +
        ENNReal.ofReal ((8 + 9604 ^ 2 * C2 ^ 2 * π) * ε * (1 - ‖X‖) ^ 2) * P ^ 2 := by
    rw [ENNReal.ofReal_mul hCε]; ring
  have hr0 : (0 : ℝ) ≤ 9604 ^ 2 * C2 ^ 2 * π * ε * (1 - ‖X‖) ^ 2 := by positivity
  have hr1 : (0 : ℝ) ≤ 8 * ε * (1 - ‖X‖) ^ 2 := by positivity
  refine ENNReal.div_le_of_le_mul ?_
  calc ∫⁻ Z in ball X ((1 - ‖X‖) / 4),
        (∫⁻ Y in unitDisc,
          ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / (2 * π * ‖Z - Y‖ * ‖1 - Z * conj Y‖)) * ‖V Y‖₊) ^ 2
      ≤ ∫⁻ Z in ball X ((1 - ‖X‖) / 4),
          (2 * a ^ 2 * (∫⁻ Y in ball X ((1 - ‖X‖) / 2), ‖Y - Z‖ₑ ^ (-1 : ℝ) * ‖hg.mk g Y‖₊) ^ 2 +
            2 * cF ^ 2) := by
        refine setLIntegral_mono' measurableSet_ball (fun Z hZ => ?_)
        calc _ ≤ (a * (∫⁻ Y in ball X ((1 - ‖X‖) / 2), ‖Y - Z‖ₑ ^ (-1 : ℝ) * ‖hg.mk g Y‖₊) + cF) ^ 2 := by
              gcongr; exact hpt Z hZ
          _ ≤ _ := (hsq_add _ _).trans_eq (by ring)
    _ = 2 * a ^ 2 * (∫⁻ Z in ball X ((1 - ‖X‖) / 4),
          (∫⁻ Y in ball X ((1 - ‖X‖) / 2), ‖Y - Z‖ₑ ^ (-1 : ℝ) * ‖hg.mk g Y‖₊) ^ 2) +
          2 * cF ^ 2 * volume (ball X ((1 - ‖X‖) / 4)) := by
        rw [lintegral_add_right _ measurable_const,
          lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num)
            (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)), setLIntegral_const]
    _ ≤ 2 * a ^ 2 * (ENNReal.ofReal (2 * π * (1 - ‖X‖)) ^ 2 * A) +
          2 * cF ^ 2 * ENNReal.ofReal (π * ((1 - ‖X‖) / 4) ^ 2) := by
        refine add_le_add (mul_le_mul_right ?_ _) (le_of_eq (by rw [hvol]))
        exact (s07c_fkps_m4_near_schur hg'.nnnorm.coe_nnreal_ennreal X hδ).trans
          (mul_le_mul_right hAg _)
    _ = ENNReal.ofReal (8 * ε * (1 - ‖X‖) ^ 2) * A +
          ENNReal.ofReal (9604 ^ 2 * C2 ^ 2 * π * ε * (1 - ‖X‖) ^ 2 / 8) * P ^ 2 := by
        rw [e1, e2]
    _ ≤ ENNReal.ofReal ((8 + 9604 ^ 2 * C2 ^ 2 * π) * ε * (1 - ‖X‖) ^ 2) * A +
          ENNReal.ofReal ((8 + 9604 ^ 2 * C2 ^ 2 * π) * ε * (1 - ‖X‖) ^ 2) * P ^ 2 := by
        refine add_le_add (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
          (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
        · nlinarith
        · nlinarith
    _ = _ := e3.symm

/-- M4.3, FKP Lemma 2.9 (`Ñ F` part), plane case. Let `‖V‖ ≤ m ‖g‖` a.e. on `𝔻`, `m ≤ √ε` a.e. on `𝔻`, and
`m²/δ dA` Carleson with norm `≤ ε`. For `X` in the cone of aperture `2` at `θ`, the Whitney `L²` average of the
absolute potential `Z ↦ ∫⁻ |∇_Y G₀(Z, Y)| ‖V Y‖` over `B(X, δ(X)/4)` is at most
`C ε (S_g(θ)² + P[S_g](X)²)`. -/
theorem s07c_fkps_m4_ntF : ∃ C : ℝ, 0 < C ∧ ∀ (g V : ℂ → ℂ) (m : ℂ → ℝ) (ε : ℝ),
    AEMeasurable g → AEMeasurable V → AEMeasurable m → (∀ z, 0 ≤ m z) → 0 ≤ ε →
    (∀ᵐ z, z ∈ unitDisc → ‖V z‖ ≤ m z * ‖g z‖) →
    (∀ᵐ z, z ∈ unitDisc → m z ≤ Real.sqrt ε) →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (m z ^ 2 / (1 - ‖z‖)) ≤ ENNReal.ofReal (ε * r)) →
    ∀ (θ : ℝ) (X : ℂ), X ∈ unitDisc → ‖X - exp (θ * I)‖ < 2 * (1 - ‖X‖) →
      (∫⁻ Z in ball X ((1 - ‖X‖) / 4),
          (∫⁻ Y in unitDisc,
            ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / (2 * π * ‖Z - Y‖ * ‖1 - Z * conj Y‖)) * ‖V Y‖₊) ^ 2) /
          ENNReal.ofReal ((1 - ‖X‖) ^ 2) ≤
        ENNReal.ofReal (C * ε) *
          ((∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 16 * (1 - ‖z‖)}, (‖g Y‖₊ : ℝ≥0∞) ^ 2) +
            (∫⁻ t in Ioc (0 : ℝ) (2 * π),
              ENNReal.ofReal ((1 - ‖X‖ ^ 2) / ‖exp (t * I) - X‖ ^ 2) *
                (∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (t * I)‖ < 16 * (1 - ‖z‖)},
                  (‖g Y‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ)) ^ 2) := by
  obtain ⟨C, hC, hcore⟩ := s07c_fkps_m4_ntF_core
  exact ⟨C, hC, fun g V m ε hg hV hm hm0 hε hVm hmle hcar θ X hX hXθ =>
    hcore 2 16 (by norm_num) (by norm_num) g V m ε hg hV hm hm0 hε hVm hmle hcar θ X hX hXθ⟩

/-- M5.1 helper: for `|Y| ≤ 1`, the set of `θ ∈ [0, 2π]` with `|Y - e^{iθ}| < β δ(Y)` has measure
`≤ 3π (β + 1) δ(Y)` (it lies in three arcs of half-length `π(β+1)δ(Y)/2` around `τ Y`, `τ Y ± 2π`). -/
theorem s07c_fkps_m5_arc_meas {Y : ℂ} (hY : ‖Y‖ ≤ 1) {β : ℝ} (hβ : 0 < β) :
    volume ({θ : ℝ | ‖Y - exp (θ * I)‖ < β * (1 - ‖Y‖)} ∩ Icc 0 (2 * π)) ≤
      ENNReal.ofReal (3 * π * ((β + 1) * (1 - ‖Y‖))) := by
  have hδ0 : 0 ≤ 1 - ‖Y‖ := by linarith
  have hφ := s07c_fkps_m4_tau_dist hY
  have hφmem := s07c_fkps_m4_tau_mem Y
  set φ : ℝ := if 0 < arg Y then arg Y else arg Y + 2 * π with hφdef
  set c : ℝ := π * ((β + 1) * (1 - ‖Y‖)) / 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hsub : {θ : ℝ | ‖Y - exp (θ * I)‖ < β * (1 - ‖Y‖)} ∩ Icc 0 (2 * π) ⊆
      ball φ c ∪ ball (φ + 2 * π) c ∪ ball (φ - 2 * π) c := by
    rintro θ ⟨hθ, hθI⟩
    have hθ' : ‖Y - exp (θ * I)‖ < β * (1 - ‖Y‖) := hθ
    have hch : ‖exp (θ * I) - exp (φ * I)‖ < (β + 1) * (1 - ‖Y‖) := by
      have := norm_sub_le_norm_sub_add_norm_sub (exp (θ * I)) Y (exp (φ * I))
      rw [norm_sub_rev (exp (θ * I)) Y] at this
      linarith
    rw [s07c_fkps_m2_chord_shift] at hch
    have hkey : ∀ s : ℝ, |s| ≤ π → ‖exp (s * I) - 1‖ < (β + 1) * (1 - ‖Y‖) → |s| < c := by
      intro s hs hlt
      have h1 := s07c_fkps_m2_chord s hs
      have h2 : 2 / π * |s| < (β + 1) * (1 - ‖Y‖) := lt_of_le_of_lt h1 hlt
      rw [hc, lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have hpi := Real.pi_pos
      rw [div_mul_eq_mul_div, div_lt_iff₀ hpi] at h2
      nlinarith
    obtain ⟨hθ0, hθ2⟩ := hθI
    obtain ⟨hφ0, hφ2⟩ := hφmem
    rcases le_or_gt |θ - φ| π with h | h
    · left; left
      rw [mem_ball, Real.dist_eq]
      exact hkey _ h hch
    · rcases lt_or_ge 0 (θ - φ) with hpos | hneg
      · left; right
        rw [show θ - φ = (θ - φ - 2 * π) + 2 * π by ring, s07c_fkps_m2_exp_periodic] at hch
        have hs : |θ - φ - 2 * π| ≤ π := by
          rw [abs_of_pos hpos] at h
          rw [abs_le]; constructor <;> linarith
        rw [mem_ball, Real.dist_eq, show θ - (φ + 2 * π) = θ - φ - 2 * π by ring]
        exact hkey _ hs hch
      · right
        rw [← s07c_fkps_m2_exp_periodic] at hch
        have hs : |θ - φ + 2 * π| ≤ π := by
          rw [abs_of_nonpos hneg] at h
          rw [abs_le]; constructor <;> linarith
        rw [mem_ball, Real.dist_eq, show θ - (φ - 2 * π) = θ - φ + 2 * π by ring]
        exact hkey _ hs hch
  calc volume ({θ : ℝ | ‖Y - exp (θ * I)‖ < β * (1 - ‖Y‖)} ∩ Icc 0 (2 * π))
      ≤ volume (ball φ c ∪ ball (φ + 2 * π) c ∪ ball (φ - 2 * π) c) := measure_mono hsub
    _ ≤ volume (ball φ c) + volume (ball (φ + 2 * π) c) + volume (ball (φ - 2 * π) c) :=
        (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
    _ = ENNReal.ofReal (3 * π * ((β + 1) * (1 - ‖Y‖))) := by
        rw [Real.volume_ball, Real.volume_ball, Real.volume_ball, ← ENNReal.ofReal_add (by positivity)
          (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [hc]; ring

/-- M5.1 (cone Fubini): for `Y ∈ 𝔻` the set of `θ ∈ [0, 2π]` with `Y` in the cone of aperture `β` at `θ` has
measure `≤ 4π(β+1) δ(Y)`. -/
theorem s07c_fkps_m5_aperture (β : ℝ) (hβ : 0 < β) (Φ : ℂ → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ θ in Icc 0 (2 * π), ∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < β * (1 - ‖z‖)}, Φ Y ≤
      ENNReal.ofReal (4 * π * (β + 1)) * ∫⁻ Y in unitDisc, Φ Y * ENNReal.ofReal (1 - ‖Y‖) := by
  set S : Set (ℝ × ℂ) := {p | p.2 ∈ unitDisc ∧ ‖p.2 - exp (p.1 * I)‖ < β * (1 - ‖p.2‖)} with hSdef
  have hSo : IsOpen S :=
    (isOpen_ball.preimage continuous_snd).inter
      (isOpen_lt (f := fun p : ℝ × ℂ => ‖p.2 - exp (p.1 * I)‖) (g := fun p : ℝ × ℂ => β * (1 - ‖p.2‖))
        (by fun_prop) (by fun_prop))
  have hS : MeasurableSet S := hSo.measurableSet
  have hcone : ∀ θ : ℝ,
      MeasurableSet {z : ℂ | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < β * (1 - ‖z‖)} := fun θ =>
    (isOpen_ball.inter (isOpen_lt (f := fun z : ℂ => ‖z - exp (θ * I)‖)
      (g := fun z : ℂ => β * (1 - ‖z‖)) (by fun_prop) (by fun_prop))).measurableSet
  calc ∫⁻ θ in Icc 0 (2 * π), ∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < β * (1 - ‖z‖)}, Φ Y
      = ∫⁻ θ in Icc 0 (2 * π), ∫⁻ Y, S.indicator (fun p => Φ p.2) (θ, Y) := by
        refine lintegral_congr (fun θ => ?_)
        rw [← lintegral_indicator (hcone θ)]
        rfl
    _ = ∫⁻ Y, ∫⁻ θ in Icc 0 (2 * π), S.indicator (fun p => Φ p.2) (θ, Y) :=
        lintegral_lintegral_swap ((hΦ.comp measurable_snd).indicator hS).aemeasurable
    _ ≤ ∫⁻ Y, unitDisc.indicator
          (fun Y => ENNReal.ofReal (4 * π * (β + 1)) * (Φ Y * ENNReal.ofReal (1 - ‖Y‖))) Y := by
        refine lintegral_mono (fun Y => ?_)
        by_cases hY : Y ∈ unitDisc
        · have hY1 : ‖Y‖ < 1 := mem_ball_zero_iff.1 hY
          have hθm : MeasurableSet {θ : ℝ | ‖Y - exp (θ * I)‖ < β * (1 - ‖Y‖)} :=
            (isOpen_lt (f := fun θ : ℝ => ‖Y - exp (θ * I)‖) (g := fun _ : ℝ => β * (1 - ‖Y‖))
              (by fun_prop) continuous_const).measurableSet
          have he : (fun θ : ℝ => S.indicator (fun p => Φ p.2) (θ, Y)) =
              {θ : ℝ | ‖Y - exp (θ * I)‖ < β * (1 - ‖Y‖)}.indicator (fun _ => Φ Y) := by
            funext θ
            simp only [hSdef, Set.indicator, Set.mem_setOf_eq, hY, true_and]
          rw [he, lintegral_indicator_const hθm, Measure.restrict_apply hθm,
            indicator_of_mem hY]
          calc Φ Y * volume ({θ : ℝ | ‖Y - exp (θ * I)‖ < β * (1 - ‖Y‖)} ∩ Icc 0 (2 * π))
              ≤ Φ Y * ENNReal.ofReal (3 * π * ((β + 1) * (1 - ‖Y‖))) :=
                mul_le_mul_right (s07c_fkps_m5_arc_meas hY1.le hβ) _
            _ ≤ Φ Y * ENNReal.ofReal (4 * π * (β + 1) * (1 - ‖Y‖)) := by
                refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
                have : 0 ≤ π * ((β + 1) * (1 - ‖Y‖)) :=
                  mul_nonneg Real.pi_pos.le (mul_nonneg (by linarith) (by linarith))
                nlinarith
            _ = _ := by
                rw [ENNReal.ofReal_mul (by positivity)]; ring
        · have he : (fun θ : ℝ => S.indicator (fun p => Φ p.2) (θ, Y)) = fun _ => 0 := by
            funext θ
            simp only [hSdef, Set.indicator, Set.mem_setOf_eq, hY, false_and, if_false]
          rw [he, lintegral_zero]
          exact zero_le
    _ = _ := by
        have h𝔻 : MeasurableSet unitDisc := measurableSet_ball
        rw [lintegral_indicator h𝔻,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- M5.2/M5.3 helper: the Whitney incidence set `{(Z, Y) | |Y - Z| < δ(Z)/4}` is measurable. -/
theorem s07c_fkps_m5_wset_meas :
    MeasurableSet {p : ℂ × ℂ | dist p.2 p.1 < (1 - ‖p.1‖) / 4} :=
  (isOpen_lt (f := fun p : ℂ × ℂ => dist p.2 p.1) (g := fun p : ℂ × ℂ => (1 - ‖p.1‖) / 4)
    (continuous_snd.dist continuous_fst) (by fun_prop)).measurableSet

/-- M5.2/M5.3 helper: Whitney incidence geometry. If `Z ∈ 𝔻` and `|Y - Z| < δ(Z)/4` then `Y ∈ 𝔻`,
`4δ(Y)/5 < δ(Z) < 4δ(Y)/3` and `|Z - Y| < δ(Y)/3`. -/
theorem s07c_fkps_m5_wgeom {Z Y : ℂ} (hZ : ‖Z‖ < 1) (hYZ : dist Y Z < (1 - ‖Z‖) / 4) :
    ‖Y‖ < 1 ∧ 4 * (1 - ‖Y‖) / 5 < 1 - ‖Z‖ ∧ 3 * (1 - ‖Z‖) / 4 < 1 - ‖Y‖ ∧
      dist Z Y < (1 - ‖Y‖) / 3 := by
  rw [dist_eq_norm] at hYZ
  have h1 := norm_sub_norm_le Y Z
  have h2 := norm_sub_norm_le Z Y
  rw [norm_sub_rev Z Y] at h2
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  linarith

/-- M5.3 (Whitney averaging, upper bound): `∫_𝔻 δ_Z⁻¹ ∫_{B(Z, δ_Z/4)} h dZ ≤ 2 ∫_𝔻 h δ`. -/
theorem s07c_fkps_m5_whitney_upper (h : ℂ → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ Z in unitDisc, (∫⁻ Y in ball Z ((1 - ‖Z‖) / 4), h Y) / ENNReal.ofReal (1 - ‖Z‖) ≤
      ENNReal.ofReal 2 * ∫⁻ Y in unitDisc, h Y * ENNReal.ofReal (1 - ‖Y‖) := by
  set B : Set (ℂ × ℂ) := {p | dist p.2 p.1 < (1 - ‖p.1‖) / 4} with hBdef
  have hB : MeasurableSet B := s07c_fkps_m5_wset_meas
  have h𝔻 : MeasurableSet unitDisc := measurableSet_ball
  set F : ℂ × ℂ → ℝ≥0∞ := B.indicator (fun p => h p.2 * (ENNReal.ofReal (1 - ‖p.1‖))⁻¹) with hFdef
  have hF : Measurable F :=
    ((hh.comp measurable_snd).mul
      ((measurable_const.sub measurable_fst.norm).ennreal_ofReal.inv)).indicator hB
  calc ∫⁻ Z in unitDisc, (∫⁻ Y in ball Z ((1 - ‖Z‖) / 4), h Y) / ENNReal.ofReal (1 - ‖Z‖)
      = ∫⁻ Z in unitDisc, ∫⁻ Y, F (Z, Y) := by
        refine lintegral_congr (fun Z => ?_)
        rw [ENNReal.div_eq_inv_mul, ← lintegral_const_mul _ hh, ← lintegral_indicator measurableSet_ball]
        refine lintegral_congr (fun Y => ?_)
        simp only [hFdef, hBdef, Set.indicator, mem_ball, Set.mem_setOf_eq]
        split_ifs <;> ring
    _ = ∫⁻ Y, ∫⁻ Z in unitDisc, F (Z, Y) := lintegral_lintegral_swap hF.aemeasurable
    _ ≤ ∫⁻ Y, unitDisc.indicator
          (fun Y => ENNReal.ofReal 2 * (h Y * ENNReal.ofReal (1 - ‖Y‖))) Y := by
        refine lintegral_mono (fun Y => ?_)
        by_cases hY : Y ∈ unitDisc
        · have hY1 : ‖Y‖ < 1 := mem_ball_zero_iff.1 hY
          have hδY : 0 < 1 - ‖Y‖ := by linarith
          rw [indicator_of_mem hY]
          have hpt : ∀ Z ∈ unitDisc, F (Z, Y) ≤ (ball Y ((1 - ‖Y‖) / 3)).indicator
              (fun _ => h Y * ENNReal.ofReal (5 / (4 * (1 - ‖Y‖)))) Z := by
            intro Z hZ
            have hZ1 : ‖Z‖ < 1 := mem_ball_zero_iff.1 hZ
            by_cases hZY : dist Y Z < (1 - ‖Z‖) / 4
            · obtain ⟨-, hlo, -, hd⟩ := s07c_fkps_m5_wgeom hZ1 hZY
              have hZB : Z ∈ ball Y ((1 - ‖Y‖) / 3) := hd
              have hmem : (Z, Y) ∈ B := hZY
              simp only [hFdef, indicator_of_mem hmem, indicator_of_mem hZB]
              refine mul_le_mul_right ?_ _
              have hδZ : 0 < 1 - ‖Z‖ := by linarith
              rw [← ENNReal.ofReal_inv_of_pos hδZ]
              refine ENNReal.ofReal_le_ofReal ?_
              rw [inv_le_iff_one_le_mul₀ hδZ, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
              linarith
            · have hmem : (Z, Y) ∉ B := hZY
              simp only [hFdef, indicator_of_notMem hmem]
              exact zero_le
          calc ∫⁻ Z in unitDisc, F (Z, Y)
              ≤ ∫⁻ Z in unitDisc, (ball Y ((1 - ‖Y‖) / 3)).indicator
                  (fun _ => h Y * ENNReal.ofReal (5 / (4 * (1 - ‖Y‖)))) Z := setLIntegral_mono' h𝔻 hpt
            _ ≤ ∫⁻ Z, (ball Y ((1 - ‖Y‖) / 3)).indicator
                  (fun _ => h Y * ENNReal.ofReal (5 / (4 * (1 - ‖Y‖)))) Z := setLIntegral_le_lintegral _ _
            _ = h Y * ENNReal.ofReal (5 / (4 * (1 - ‖Y‖))) * volume (ball Y ((1 - ‖Y‖) / 3)) :=
                lintegral_indicator_const measurableSet_ball _
            _ = h Y * ENNReal.ofReal (5 * π / 36 * (1 - ‖Y‖)) := by
                rw [Complex.volume_ball, ← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_coe_nnreal,
                  NNReal.coe_real_pi, ← ENNReal.ofReal_mul (sq_nonneg _), mul_assoc,
                  ← ENNReal.ofReal_mul (by positivity)]
                congr 2
                field_simp
                ring
            _ ≤ ENNReal.ofReal 2 * (h Y * ENNReal.ofReal (1 - ‖Y‖)) := by
                rw [mul_comm (ENNReal.ofReal 2), mul_assoc, ← ENNReal.ofReal_mul hδY.le]
                refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
                nlinarith [Real.pi_lt_d2]
        · rw [indicator_of_notMem hY]
          have hz : ∀ Z ∈ unitDisc, F (Z, Y) = 0 := by
            intro Z hZ
            have hZ1 : ‖Z‖ < 1 := mem_ball_zero_iff.1 hZ
            have hmem : (Z, Y) ∉ B := by
              intro hZY
              exact hY (mem_ball_zero_iff.2 (s07c_fkps_m5_wgeom hZ1 hZY).1)
            simp only [hFdef, indicator_of_notMem hmem]
          rw [setLIntegral_congr_fun h𝔻 hz, lintegral_zero]
    _ = _ := by
        rw [lintegral_indicator h𝔻, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- M5.2 (Whitney averaging, lower bound): `∫_𝔻 h ≤ 36 ∫_𝔻 δ_Z⁻² ∫_{B(Z, δ_Z/4)} h dZ`. -/
theorem s07c_fkps_m5_whitney_lower (h : ℂ → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ Y in unitDisc, h Y ≤ ENNReal.ofReal 36 * ∫⁻ Z in unitDisc,
      (∫⁻ Y in ball Z ((1 - ‖Z‖) / 4), h Y) / ENNReal.ofReal ((1 - ‖Z‖) ^ 2) := by
  set B : Set (ℂ × ℂ) := {p | dist p.2 p.1 < (1 - ‖p.1‖) / 4} with hBdef
  have hB : MeasurableSet B := s07c_fkps_m5_wset_meas
  have h𝔻 : MeasurableSet unitDisc := measurableSet_ball
  set F : ℂ × ℂ → ℝ≥0∞ :=
    B.indicator (fun p => h p.2 * (ENNReal.ofReal ((1 - ‖p.1‖) ^ 2))⁻¹) with hFdef
  have hF : Measurable F :=
    ((hh.comp measurable_snd).mul
      (((measurable_const.sub measurable_fst.norm).pow_const 2).ennreal_ofReal.inv)).indicator hB
  have hR : ∫⁻ Z in unitDisc, (∫⁻ Y in ball Z ((1 - ‖Z‖) / 4), h Y) / ENNReal.ofReal ((1 - ‖Z‖) ^ 2) =
      ∫⁻ Z in unitDisc, ∫⁻ Y, F (Z, Y) := by
    refine lintegral_congr (fun Z => ?_)
    rw [ENNReal.div_eq_inv_mul, ← lintegral_const_mul _ hh, ← lintegral_indicator measurableSet_ball]
    refine lintegral_congr (fun Y => ?_)
    simp only [hFdef, hBdef, Set.indicator, mem_ball, Set.mem_setOf_eq]
    split_ifs <;> ring
  rw [hR, lintegral_lintegral_swap (f := fun Z Y => F (Z, Y)) hF.aemeasurable]
  have hpt : ∀ Y ∈ unitDisc, h Y ≤ ENNReal.ofReal 36 * ∫⁻ Z in unitDisc, F (Z, Y) := by
    intro Y hY
    have hY1 : ‖Y‖ < 1 := mem_ball_zero_iff.1 hY
    have hδY : 0 < 1 - ‖Y‖ := by linarith
    have hsub : ball Y ((1 - ‖Y‖) / 5) ⊆ unitDisc := by
      intro Z hZ
      rw [mem_ball, dist_eq_norm] at hZ
      show Z ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff]
      have := norm_sub_norm_le Z Y
      linarith
    have hlow : ∀ Z ∈ ball Y ((1 - ‖Y‖) / 5),
        h Y * ENNReal.ofReal (25 / (36 * (1 - ‖Y‖) ^ 2)) ≤ F (Z, Y) := by
      intro Z hZ
      rw [mem_ball, dist_eq_norm] at hZ
      have h1 := norm_sub_norm_le Z Y
      have h2 := norm_sub_norm_le Y Z
      rw [norm_sub_rev Y Z] at h2
      have hlo : 4 * (1 - ‖Y‖) / 5 < 1 - ‖Z‖ := by linarith
      have hhi : 1 - ‖Z‖ < 6 * (1 - ‖Y‖) / 5 := by linarith
      have hmem : (Z, Y) ∈ B := by
        show dist Y Z < (1 - ‖Z‖) / 4
        rw [dist_eq_norm, norm_sub_rev]
        linarith
      simp only [hFdef, indicator_of_mem hmem]
      refine mul_le_mul_right ?_ _
      have hδZ : 0 < 1 - ‖Z‖ := by linarith
      rw [← ENNReal.ofReal_inv_of_pos (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_iff₀ (by positivity)]
      have hsq : (1 - ‖Z‖) ^ 2 ≤ (6 * (1 - ‖Y‖) / 5) ^ 2 := pow_le_pow_left₀ hδZ.le hhi.le 2
      have hpos : 0 < ((1 - ‖Z‖) ^ 2)⁻¹ := by positivity
      calc (25 : ℝ) = ((1 - ‖Z‖) ^ 2)⁻¹ * (1 - ‖Z‖) ^ 2 * 25 := by
            rw [inv_mul_cancel₀ (by positivity)]; ring
        _ ≤ ((1 - ‖Z‖) ^ 2)⁻¹ * (6 * (1 - ‖Y‖) / 5) ^ 2 * 25 := by gcongr
        _ = ((1 - ‖Z‖) ^ 2)⁻¹ * (36 * (1 - ‖Y‖) ^ 2) := by ring
    calc h Y ≤ ENNReal.ofReal 36 * (h Y * ENNReal.ofReal (25 / (36 * (1 - ‖Y‖) ^ 2)) *
          volume (ball Y ((1 - ‖Y‖) / 5))) := by
          rw [Complex.volume_ball, ← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_coe_nnreal,
            NNReal.coe_real_pi, ← ENNReal.ofReal_mul (sq_nonneg _), mul_assoc,
            ← ENNReal.ofReal_mul (by positivity), mul_comm (ENNReal.ofReal 36), mul_assoc,
            ← ENNReal.ofReal_mul (by positivity)]
          have : 25 / (36 * (1 - ‖Y‖) ^ 2) * (((1 - ‖Y‖) / 5) ^ 2 * π) * 36 = π := by
            field_simp
            ring
          rw [this]
          calc h Y = h Y * 1 := (mul_one _).symm
            _ ≤ h Y * ENNReal.ofReal π := by
                refine mul_le_mul_right ?_ _
                rw [← ENNReal.ofReal_one]
                exact ENNReal.ofReal_le_ofReal (by linarith [Real.pi_gt_three])
      _ = ENNReal.ofReal 36 * ∫⁻ Z in ball Y ((1 - ‖Y‖) / 5),
            h Y * ENNReal.ofReal (25 / (36 * (1 - ‖Y‖) ^ 2)) := by
          rw [setLIntegral_const]
      _ ≤ ENNReal.ofReal 36 * ∫⁻ Z in ball Y ((1 - ‖Y‖) / 5), F (Z, Y) :=
          mul_le_mul_right (setLIntegral_mono' measurableSet_ball hlow) _
      _ ≤ ENNReal.ofReal 36 * ∫⁻ Z in unitDisc, F (Z, Y) :=
          mul_le_mul_right (lintegral_mono_set hsub) _
  calc ∫⁻ Y in unitDisc, h Y
      ≤ ∫⁻ Y in unitDisc, ENNReal.ofReal 36 * ∫⁻ Z in unitDisc, F (Z, Y) := setLIntegral_mono' h𝔻 hpt
    _ ≤ ∫⁻ Y, ENNReal.ofReal 36 * ∫⁻ Z in unitDisc, F (Z, Y) := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal 36 * ∫⁻ Y, ∫⁻ Z in unitDisc, F (Z, Y) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- M5.4: M4.3 (`s07c_fkps_m4_ntF`) for `X` in the cone of aperture `16` at `θ`. The near ball `B(X, δ_X/2)` then
lies in the cone of aperture `34`, which replaces `16` in the first term on the right. -/
theorem s07c_fkps_m5_ntF16 : ∃ C : ℝ, 0 < C ∧ ∀ (g V : ℂ → ℂ) (m : ℂ → ℝ) (ε : ℝ),
    AEMeasurable g → AEMeasurable V → AEMeasurable m → (∀ z, 0 ≤ m z) → 0 ≤ ε →
    (∀ᵐ z, z ∈ unitDisc → ‖V z‖ ≤ m z * ‖g z‖) →
    (∀ᵐ z, z ∈ unitDisc → m z ≤ Real.sqrt ε) →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (m z ^ 2 / (1 - ‖z‖)) ≤ ENNReal.ofReal (ε * r)) →
    ∀ (θ : ℝ) (X : ℂ), X ∈ unitDisc → ‖X - exp (θ * I)‖ < 16 * (1 - ‖X‖) →
      (∫⁻ Z in ball X ((1 - ‖X‖) / 4),
          (∫⁻ Y in unitDisc,
            ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / (2 * π * ‖Z - Y‖ * ‖1 - Z * conj Y‖)) * ‖V Y‖₊) ^ 2) /
          ENNReal.ofReal ((1 - ‖X‖) ^ 2) ≤
        ENNReal.ofReal (C * ε) *
          ((∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 34 * (1 - ‖z‖)}, (‖g Y‖₊ : ℝ≥0∞) ^ 2) +
            (∫⁻ t in Ioc (0 : ℝ) (2 * π),
              ENNReal.ofReal ((1 - ‖X‖ ^ 2) / ‖exp (t * I) - X‖ ^ 2) *
                (∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (t * I)‖ < 16 * (1 - ‖z‖)},
                  (‖g Y‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ)) ^ 2) := by
  obtain ⟨C, hC, hcore⟩ := s07c_fkps_m4_ntF_core
  exact ⟨C, hC, fun g V m ε hg hV hm hm0 hε hVm hmle hcar θ X hX hXθ =>
    hcore 16 34 (by norm_num) (by norm_num) g V m ε hg hV hm hm0 hε hVm hmle hcar θ X hX hXθ⟩

/-- M5.5 helper: `Z ↦ ∫_{B(Z, δ_Z/4)} k` is measurable. -/
theorem s07c_fkps_m5_wball_meas {k : ℂ → ℝ≥0∞} (hk : Measurable k) :
    Measurable fun Z : ℂ => ∫⁻ Y in ball Z ((1 - ‖Z‖) / 4), k Y := by
  have hB : MeasurableSet {p : ℂ × ℂ | dist p.2 p.1 < (1 - ‖p.1‖) / 4} := s07c_fkps_m5_wset_meas
  have he : (fun Z : ℂ => ∫⁻ Y in ball Z ((1 - ‖Z‖) / 4), k Y) = fun Z =>
      ∫⁻ Y, {p : ℂ × ℂ | dist p.2 p.1 < (1 - ‖p.1‖) / 4}.indicator (fun p => k p.2) (Z, Y) := by
    funext Z
    rw [← lintegral_indicator measurableSet_ball]
    rfl
  rw [he]
  exact ((hk.comp measurable_snd).indicator hB).lintegral_prod_right'

/-- M5.5 helper: `θ ↦ ∫_{cone β θ} Φ` is measurable. -/
theorem s07c_fkps_m5_cone_meas (β : ℝ) {Φ : ℂ → ℝ≥0∞} (hΦ : Measurable Φ) :
    Measurable fun θ : ℝ =>
      ∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < β * (1 - ‖z‖)}, Φ Y := by
  set S : Set (ℝ × ℂ) := {p | p.2 ∈ unitDisc ∧ ‖p.2 - exp (p.1 * I)‖ < β * (1 - ‖p.2‖)} with hSdef
  have hS : MeasurableSet S :=
    ((isOpen_ball.preimage continuous_snd).inter
      (isOpen_lt (f := fun p : ℝ × ℂ => ‖p.2 - exp (p.1 * I)‖) (g := fun p : ℝ × ℂ => β * (1 - ‖p.2‖))
        (by fun_prop) (by fun_prop))).measurableSet
  have he : (fun θ : ℝ =>
      ∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < β * (1 - ‖z‖)}, Φ Y) = fun θ =>
      ∫⁻ Y, S.indicator (fun p => Φ p.2) (θ, Y) := by
    funext θ
    have hc : MeasurableSet {z : ℂ | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < β * (1 - ‖z‖)} :=
      (isOpen_ball.inter (isOpen_lt (f := fun z : ℂ => ‖z - exp (θ * I)‖)
        (g := fun z : ℂ => β * (1 - ‖z‖)) (by fun_prop) (by fun_prop))).measurableSet
    rw [← lintegral_indicator hc]
    rfl
  rw [he]
  exact ((hΦ.comp measurable_snd).indicator hS).lintegral_prod_right'

/-- M5.5 helper: `(x^{1/2})² = x` and `(x²)^{1/2} = x` in `ℝ≥0∞`. -/
theorem s07c_fkps_m5_sqrt_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

/-- M5.5 (Whitney-level tent duality): if `m ≤ a z` a.e. on every Whitney ball `B(z, δ(z)/2)`, `a²/(1-|z|²)` is
Carleson with norm `≤ ε`, and `R θ` bounds the Whitney `L²` averages of `u` over the cone of aperture `16` at `θ`,
then `∫_𝔻 |u| m |g| ≤ C √ε (∫_𝕋 R)^{1/2} (∫_𝔻 |g|² δ)^{1/2}`. -/
theorem s07c_fkps_m5_duality_w : ∃ C : ℝ, 0 < C ∧ ∀ (g : ℂ → ℂ) (m a u : ℂ → ℝ) (R : ℝ → ℝ≥0∞) (ε : ℝ),
    AEMeasurable g → AEMeasurable m → Measurable a → Measurable u → Measurable R →
    (∀ z, 0 ≤ m z) → (∀ z, 0 ≤ a z) → 0 ≤ ε →
    (∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) → m w ≤ a z) →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)) ≤ ENNReal.ofReal (ε * r)) →
    (∀ θ : ℝ, ∀ Z ∈ {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 16 * (1 - ‖z‖)},
      (∫⁻ Y in ball Z ((1 - ‖Z‖) / 4), ENNReal.ofReal (u Y ^ 2)) / ENNReal.ofReal ((1 - ‖Z‖) ^ 2) ≤ R θ) →
    ∫⁻ Y in unitDisc, ENNReal.ofReal (|u Y| * m Y * ‖g Y‖) ≤
      ENNReal.ofReal (C * Real.sqrt ε) * (∫⁻ θ in Icc 0 (2 * π), R θ) ^ (1 / 2 : ℝ) *
        (∫⁻ Y in unitDisc, (‖g Y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 - ‖Y‖)) ^ (1 / 2 : ℝ) := by
  obtain ⟨C2, hC2, hD⟩ := s07c_fkps_m4_duality
  refine ⟨1080 * C2, by positivity, ?_⟩
  intro g m a u R ε hg hm ha hu hRm hm0 ha0 hε hM hC hR
  have h𝔻 : MeasurableSet unitDisc := measurableSet_ball
  have hg' : Measurable (hg.mk g) := hg.measurable_mk
  have hm' : Measurable (hm.mk m) := hm.measurable_mk
  -- the Whitney ball integrals
  set Au : ℂ → ℝ≥0∞ := fun Z => ∫⁻ Y in ball Z ((1 - ‖Z‖) / 4), ENNReal.ofReal (u Y ^ 2) with hAu
  set Ag : ℂ → ℝ≥0∞ := fun Z => ∫⁻ Y in ball Z ((1 - ‖Z‖) / 4), (‖hg.mk g Y‖₊ : ℝ≥0∞) ^ 2 with hAg
  have hAum : Measurable Au := s07c_fkps_m5_wball_meas (hu.pow_const 2).ennreal_ofReal
  have hAgm : Measurable Ag := s07c_fkps_m5_wball_meas (hg'.nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hinvm : Measurable fun Z : ℂ => (ENNReal.ofReal (1 - ‖Z‖))⁻¹ :=
    (measurable_const.sub measurable_norm).ennreal_ofReal.inv
  set Φ : ℂ → ℝ≥0∞ := fun Z => Au Z ^ (1 / 2 : ℝ) * Ag Z ^ (1 / 2 : ℝ) * (ENNReal.ofReal (1 - ‖Z‖))⁻¹
    with hΦdef
  have hΦ : Measurable Φ := ((hAum.pow_const _).mul (hAgm.pow_const _)).mul hinvm
  set Ψ : ℂ → ℝ≥0∞ := fun Z => ENNReal.ofReal (a Z) with hΨdef
  have hΨ : Measurable Ψ := ha.ennreal_ofReal
  -- Carleson for Ψ
  have hcarΨ : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, Ψ z ^ 2 / ENNReal.ofReal (1 - ‖z‖) ≤ ENNReal.ofReal (2 * ε * r) := by
    intro ζ hζ r hr hr2
    calc ∫⁻ z in unitDisc ∩ ball ζ r, Ψ z ^ 2 / ENNReal.ofReal (1 - ‖z‖)
        ≤ ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal 2 * ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)) := by
          refine setLIntegral_mono' (h𝔻.inter measurableSet_ball) (fun z hz => ?_)
          have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz.1
          have hδ : 0 < 1 - ‖z‖ := by linarith
          have h1 : 1 - ‖z‖ ≠ 0 := hδ.ne'
          have h2 : 1 + ‖z‖ ≠ 0 := by positivity
          rw [hΨdef, ← ENNReal.ofReal_pow (ha0 z), ← ENNReal.ofReal_div_of_pos hδ,
            ← ENNReal.ofReal_mul (by norm_num)]
          refine ENNReal.ofReal_le_ofReal ?_
          have e : a z ^ 2 / (1 - ‖z‖) = (1 + ‖z‖) * (a z ^ 2 / (1 - ‖z‖ ^ 2)) := by
            rw [show 1 - ‖z‖ ^ 2 = (1 - ‖z‖) * (1 + ‖z‖) by ring]
            field_simp
          rw [e]
          exact mul_le_mul_of_nonneg_right (by linarith)
            (div_nonneg (sq_nonneg _) (by nlinarith [norm_nonneg z]))
      _ = ENNReal.ofReal 2 * ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (ε * r) := mul_le_mul_right (hC ζ hζ r hr hr2) _
      _ = ENNReal.ofReal (2 * ε * r) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]; ring_nf
  -- Step A: Whitney averaging + Hölder on each Whitney ball
  have hstepA : ∫⁻ Y in unitDisc, ENNReal.ofReal (|u Y| * m Y * ‖g Y‖) ≤
      ENNReal.ofReal 36 * ∫⁻ Z in unitDisc, Φ Z * Ψ Z / ENNReal.ofReal (1 - ‖Z‖) := by
    have hk : Measurable fun Y : ℂ => ENNReal.ofReal (|u Y| * hm.mk m Y * ‖hg.mk g Y‖) :=
      (((continuous_abs.measurable.comp hu).mul hm').mul hg'.norm).ennreal_ofReal
    calc ∫⁻ Y in unitDisc, ENNReal.ofReal (|u Y| * m Y * ‖g Y‖)
        = ∫⁻ Y in unitDisc, ENNReal.ofReal (|u Y| * hm.mk m Y * ‖hg.mk g Y‖) := by
          refine lintegral_congr_ae (ae_restrict_of_ae ?_)
          filter_upwards [hm.ae_eq_mk, hg.ae_eq_mk] with Y h1 h2
          rw [h1, h2]
      _ ≤ ENNReal.ofReal 36 * ∫⁻ Z in unitDisc,
            (∫⁻ Y in ball Z ((1 - ‖Z‖) / 4), ENNReal.ofReal (|u Y| * hm.mk m Y * ‖hg.mk g Y‖)) /
              ENNReal.ofReal ((1 - ‖Z‖) ^ 2) := s07c_fkps_m5_whitney_lower _ hk
      _ ≤ ENNReal.ofReal 36 * ∫⁻ Z in unitDisc, Φ Z * Ψ Z / ENNReal.ofReal (1 - ‖Z‖) := by
          refine mul_le_mul_right (setLIntegral_mono' h𝔻 (fun Z hZ => ?_)) _
          have hZ1 : ‖Z‖ < 1 := mem_ball_zero_iff.1 hZ
          have hδ : 0 < 1 - ‖Z‖ := by linarith
          have hb0 : ENNReal.ofReal (1 - ‖Z‖) ≠ 0 := by simpa using hδ
          have hbt : ENNReal.ofReal (1 - ‖Z‖) ≠ ⊤ := ENNReal.ofReal_ne_top
          -- a.e. bound on the ball
          have hball : ∫⁻ Y in ball Z ((1 - ‖Z‖) / 4), ENNReal.ofReal (|u Y| * hm.mk m Y * ‖hg.mk g Y‖) ≤
              Ψ Z * ∫⁻ Y in ball Z ((1 - ‖Z‖) / 4), ENNReal.ofReal |u Y| * ‖hg.mk g Y‖₊ := by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae (hM Z hZ),
              ae_restrict_of_ae hm.ae_eq_mk] with Y hY h1 h2
            have hY2 : Y ∈ ball Z ((1 - ‖Z‖) / 2) := by
              rw [mem_ball] at hY ⊢; linarith
            have hle : hm.mk m Y ≤ a Z := by rw [← h2]; exact h1 hY2
            rw [← enorm_eq_nnnorm, ← ofReal_norm, ← ENNReal.ofReal_mul (abs_nonneg _),
              ← ENNReal.ofReal_mul (ha0 Z)]
            refine ENNReal.ofReal_le_ofReal ?_
            have hp : 0 ≤ |u Y| * ‖hg.mk g Y‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
            calc |u Y| * hm.mk m Y * ‖hg.mk g Y‖ = hm.mk m Y * (|u Y| * ‖hg.mk g Y‖) := by ring
              _ ≤ a Z * (|u Y| * ‖hg.mk g Y‖) := mul_le_mul_of_nonneg_right hle hp
          -- Hölder on the ball
          have hhol : ∫⁻ Y in ball Z ((1 - ‖Z‖) / 4), ENNReal.ofReal |u Y| * ‖hg.mk g Y‖₊ ≤
              Au Z ^ (1 / 2 : ℝ) * Ag Z ^ (1 / 2 : ℝ) := by
            have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (ball Z ((1 - ‖Z‖) / 4)))
              Real.HolderConjugate.two_two
              ((continuous_abs.measurable.comp hu).ennreal_ofReal).aemeasurable
              hg'.nnnorm.coe_nnreal_ennreal.aemeasurable
            simp only [Pi.mul_apply, ENNReal.rpow_two] at hH
            refine hH.trans (le_of_eq ?_)
            congr 2
            refine lintegral_congr (fun Y => ?_)
            rw [Function.comp_apply, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
          have hsq : ENNReal.ofReal ((1 - ‖Z‖) ^ 2) = ENNReal.ofReal (1 - ‖Z‖) * ENNReal.ofReal (1 - ‖Z‖) := by
            rw [sq, ENNReal.ofReal_mul hδ.le]
          calc (∫⁻ Y in ball Z ((1 - ‖Z‖) / 4), ENNReal.ofReal (|u Y| * hm.mk m Y * ‖hg.mk g Y‖)) /
                ENNReal.ofReal ((1 - ‖Z‖) ^ 2)
              ≤ Ψ Z * (Au Z ^ (1 / 2 : ℝ) * Ag Z ^ (1 / 2 : ℝ)) / ENNReal.ofReal ((1 - ‖Z‖) ^ 2) :=
                ENNReal.div_le_div_right (hball.trans (mul_le_mul_right hhol _)) _
            _ = Φ Z * Ψ Z / ENNReal.ofReal (1 - ‖Z‖) := by
                rw [hsq]
                simp only [hΦdef, div_eq_mul_inv]
                rw [ENNReal.mul_inv (Or.inl hb0) (Or.inl hbt)]
                ring
  -- Step B: tent duality
  have hstepB := hD Φ Ψ (2 * ε) hΦ hΨ (by positivity) hcarΨ
  -- Step C: bound the area integrals of Φ
  set Q : ℝ → ℝ≥0∞ := fun θ =>
    ∫⁻ Z in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 16 * (1 - ‖z‖)}, Ag Z / ENNReal.ofReal ((1 - ‖Z‖) ^ 2)
    with hQdef
  have hAgδ : Measurable fun Z : ℂ => Ag Z / ENNReal.ofReal ((1 - ‖Z‖) ^ 2) :=
    hAgm.div ((measurable_const.sub measurable_norm).pow_const 2).ennreal_ofReal
  have hQm : Measurable Q := s07c_fkps_m5_cone_meas 16 hAgδ
  have hstepC : ∀ θ : ℝ,
      (∫⁻ Z in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 16 * (1 - ‖z‖)},
        Φ Z ^ 2 / ENNReal.ofReal ((1 - ‖Z‖) ^ 2)) ^ (1 / 2 : ℝ) ≤
        R θ ^ (1 / 2 : ℝ) * Q θ ^ (1 / 2 : ℝ) := by
    intro θ
    have hcone : MeasurableSet {z : ℂ | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 16 * (1 - ‖z‖)} :=
      (isOpen_ball.inter (isOpen_lt (f := fun z : ℂ => ‖z - exp (θ * I)‖)
        (g := fun z : ℂ => 16 * (1 - ‖z‖)) (by fun_prop) (by fun_prop))).measurableSet
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [hQdef, ← lintegral_const_mul _ hAgδ]
    refine setLIntegral_mono' hcone (fun Z hZ => ?_)
    have hZ1 : ‖Z‖ < 1 := mem_ball_zero_iff.1 hZ.1
    have hδ : 0 < 1 - ‖Z‖ := by linarith
    have hpt := hR θ Z hZ
    rw [hΦdef, ENNReal.ofReal_pow hδ.le]
    simp only []
    rw [mul_pow, mul_pow, s07c_fkps_m5_sqrt_sq, s07c_fkps_m5_sqrt_sq, ← ENNReal.inv_pow]
    rw [ENNReal.ofReal_pow hδ.le] at hpt
    calc Au Z * Ag Z * (ENNReal.ofReal (1 - ‖Z‖) ^ 2)⁻¹ / ENNReal.ofReal (1 - ‖Z‖) ^ 2
        = (Au Z / ENNReal.ofReal (1 - ‖Z‖) ^ 2) * (Ag Z / ENNReal.ofReal (1 - ‖Z‖) ^ 2) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]; ring
      _ ≤ R θ * (Ag Z / ENNReal.ofReal (1 - ‖Z‖) ^ 2) := mul_le_mul_left hpt _
  -- Step D: integrate in θ
  have hQint : ∫⁻ θ in Icc 0 (2 * π), Q θ ≤
      ENNReal.ofReal (136 * π) * ∫⁻ Y in unitDisc, (‖hg.mk g Y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 - ‖Y‖) := by
    calc ∫⁻ θ in Icc 0 (2 * π), Q θ
        ≤ ENNReal.ofReal (4 * π * (16 + 1)) *
            ∫⁻ Z in unitDisc, Ag Z / ENNReal.ofReal ((1 - ‖Z‖) ^ 2) * ENNReal.ofReal (1 - ‖Z‖) :=
          s07c_fkps_m5_aperture 16 (by norm_num) _ hAgδ
      _ ≤ ENNReal.ofReal (4 * π * (16 + 1)) * ∫⁻ Z in unitDisc, Ag Z / ENNReal.ofReal (1 - ‖Z‖) := by
          refine mul_le_mul_right (setLIntegral_mono' h𝔻 (fun Z hZ => le_of_eq ?_)) _
          have hZ1 : ‖Z‖ < 1 := mem_ball_zero_iff.1 hZ
          have hδ : 0 < 1 - ‖Z‖ := by linarith
          have hb0 : ENNReal.ofReal (1 - ‖Z‖) ≠ 0 := by simpa using hδ
          have hbt : ENNReal.ofReal (1 - ‖Z‖) ≠ ⊤ := ENNReal.ofReal_ne_top
          rw [ENNReal.ofReal_pow hδ.le, div_eq_mul_inv, div_eq_mul_inv, ENNReal.inv_pow, sq,
            mul_assoc, mul_assoc, ENNReal.inv_mul_cancel hb0 hbt, mul_one]
      _ ≤ ENNReal.ofReal (4 * π * (16 + 1)) *
            (ENNReal.ofReal 2 * ∫⁻ Y in unitDisc, (‖hg.mk g Y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 - ‖Y‖)) :=
          mul_le_mul_right (s07c_fkps_m5_whitney_upper _
            (hg'.nnnorm.coe_nnreal_ennreal.pow_const 2)) _
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]; ring_nf
  have hstepD : ∫⁻ θ in Ioc (0 : ℝ) (2 * π),
      (∫⁻ Z in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 16 * (1 - ‖z‖)},
        Φ Z ^ 2 / ENNReal.ofReal ((1 - ‖Z‖) ^ 2)) ^ (1 / 2 : ℝ) ≤
      (∫⁻ θ in Icc 0 (2 * π), R θ) ^ (1 / 2 : ℝ) * (∫⁻ θ in Icc 0 (2 * π), Q θ) ^ (1 / 2 : ℝ) := by
    calc _ ≤ ∫⁻ θ in Ioc (0 : ℝ) (2 * π), R θ ^ (1 / 2 : ℝ) * Q θ ^ (1 / 2 : ℝ) :=
          setLIntegral_mono' measurableSet_Ioc (fun θ _ => hstepC θ)
      _ ≤ (∫⁻ θ in Ioc (0 : ℝ) (2 * π), (R θ ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
            (∫⁻ θ in Ioc (0 : ℝ) (2 * π), (Q θ ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
          ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two
            (hRm.pow_const _).aemeasurable (hQm.pow_const _).aemeasurable
      _ ≤ _ := by
          simp only [ENNReal.rpow_two, s07c_fkps_m5_sqrt_sq]
          gcongr <;> exact Ioc_subset_Icc_self
  -- Step E: combine
  have hgg : ∫⁻ Y in unitDisc, (‖hg.mk g Y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 - ‖Y‖) =
      ∫⁻ Y in unitDisc, (‖g Y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 - ‖Y‖) :=
    lintegral_congr_ae (ae_restrict_of_ae (hg.ae_eq_mk.mono fun Y h => by simp only [h]))
  set Rint := ∫⁻ θ in Icc 0 (2 * π), R θ with hRint
  set G := ∫⁻ Y in unitDisc, (‖g Y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 - ‖Y‖) with hGdef
  have hQG : (∫⁻ θ in Icc 0 (2 * π), Q θ) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt (136 * π)) * G ^ (1 / 2 : ℝ) := by
    rw [hgg] at hQint
    calc (∫⁻ θ in Icc 0 (2 * π), Q θ) ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal (136 * π) * G) ^ (1 / 2 : ℝ) := by
          exact ENNReal.rpow_le_rpow hQint (by norm_num)
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg (by positivity)
            (by norm_num), Real.sqrt_eq_rpow]
  have hreal : 36 * (C2 * Real.sqrt (2 * ε)) * Real.sqrt (136 * π) ≤ 1080 * C2 * Real.sqrt ε := by
    have h1 : Real.sqrt (2 * ε) * Real.sqrt (136 * π) ≤ 30 * Real.sqrt ε := by
      rw [← Real.sqrt_mul (by linarith)]
      calc Real.sqrt (2 * ε * (136 * π)) ≤ Real.sqrt (30 ^ 2 * ε) :=
            Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_d2])
        _ = 30 * Real.sqrt ε := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hC2.le]
  calc ∫⁻ Y in unitDisc, ENNReal.ofReal (|u Y| * m Y * ‖g Y‖)
      ≤ ENNReal.ofReal 36 * ∫⁻ Z in unitDisc, Φ Z * Ψ Z / ENNReal.ofReal (1 - ‖Z‖) := hstepA
    _ ≤ ENNReal.ofReal 36 * (ENNReal.ofReal (C2 * Real.sqrt (2 * ε)) *
          (Rint ^ (1 / 2 : ℝ) * (∫⁻ θ in Icc 0 (2 * π), Q θ) ^ (1 / 2 : ℝ))) :=
        mul_le_mul_right (hstepB.trans (mul_le_mul_right hstepD _)) _
    _ ≤ ENNReal.ofReal 36 * (ENNReal.ofReal (C2 * Real.sqrt (2 * ε)) *
          (Rint ^ (1 / 2 : ℝ) * (ENNReal.ofReal (Real.sqrt (136 * π)) * G ^ (1 / 2 : ℝ)))) := by
        gcongr
    _ = ENNReal.ofReal (36 * (C2 * Real.sqrt (2 * ε)) * Real.sqrt (136 * π)) * Rint ^ (1 / 2 : ℝ) *
          G ^ (1 / 2 : ℝ) := by
        have hX : 0 ≤ C2 * Real.sqrt (2 * ε) := mul_nonneg hC2.le (Real.sqrt_nonneg _)
        rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hX), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 36)]
        ring
    _ ≤ _ := by gcongr

/-- M5.6 (nontangential control of `u`): under (P5') and the M4.3 hypotheses, for `Z` in the cone of aperture `16`
at `θ`, the Whitney `L²` average of `u` at `Z` is `≤ C (M f(θ)² + ε (S₃₄(θ)² + P[S₁₆](Z)²))`. -/
theorem s07c_fkps_m5_ntu : ∃ C : ℝ, 0 < C ∧ ∀ (g V : ℂ → ℂ) (m u : ℂ → ℝ) (f : ℝ → ℝ) (ε : ℝ),
    AEMeasurable g → AEMeasurable V → AEMeasurable m → Measurable u → Measurable f →
    (∀ t, f (t + 2 * π) = f t) → (∀ z, 0 ≤ m z) → 0 ≤ ε →
    (∀ᵐ z, z ∈ unitDisc → ‖V z‖ ≤ m z * ‖g z‖) →
    (∀ᵐ z, z ∈ unitDisc → m z ≤ Real.sqrt ε) →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (m z ^ 2 / (1 - ‖z‖)) ≤ ENNReal.ofReal (ε * r)) →
    (∀ᵐ X, X ∈ unitDisc → ENNReal.ofReal |u X| ≤
      ENNReal.ofReal (2 * π)⁻¹ * (∫⁻ t in Icc 0 (2 * π),
        ENNReal.ofReal ((1 - ‖X‖ ^ 2) / ‖exp (t * I) - X‖ ^ 2) * ‖f t‖ₑ) +
      ∫⁻ Y in unitDisc,
        ENNReal.ofReal ((1 - ‖X‖ ^ 2) / (2 * π * ‖X - Y‖ * ‖1 - X * conj Y‖)) * ‖V Y‖₊) →
    ∀ (θ : ℝ), ∀ Z ∈ {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 16 * (1 - ‖z‖)},
      (∫⁻ Y in ball Z ((1 - ‖Z‖) / 4), ENNReal.ofReal (u Y ^ 2)) / ENNReal.ofReal ((1 - ‖Z‖) ^ 2) ≤
        ENNReal.ofReal C * (TauCeti.maximalFunction volume f θ ^ 2 + ENNReal.ofReal ε *
          ((∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 34 * (1 - ‖z‖)}, (‖g Y‖₊ : ℝ≥0∞) ^ 2) +
            (∫⁻ t in Ioc (0 : ℝ) (2 * π),
              ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / ‖exp (t * I) - Z‖ ^ 2) *
                (∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (t * I)‖ < 16 * (1 - ‖z‖)},
                  (‖g Y‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ)) ^ 2)) := by
  obtain ⟨C4, hC4, hF⟩ := s07c_fkps_m5_ntF16
  obtain ⟨CP, hCPt, hP⟩ := s07c_fkps_m2_nt_lint 22 (by norm_num)
  refine ⟨CP.toReal ^ 2 * π + 2 * C4 + 1, by positivity, ?_⟩
  intro g V m u f ε hg hV hm hu hf hper hm0 hε hVb hmb hcar hP5 θ Z hZ
  have hZ1 : ‖Z‖ < 1 := mem_ball_zero_iff.1 hZ.1
  have hδ : 0 < 1 - ‖Z‖ := by linarith
  set M := TauCeti.maximalFunction volume f θ with hMdef
  set c := CP.toReal with hcdef
  have hCP : CP = ENNReal.ofReal c := (ENNReal.ofReal_toReal hCPt).symm
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  set B : ℂ → ℝ≥0∞ := fun X => ∫⁻ Y in unitDisc,
      ENNReal.ofReal ((1 - ‖X‖ ^ 2) / (2 * π * ‖X - Y‖ * ‖1 - X * conj Y‖)) * ‖V Y‖₊ with hBdef
  have hsq2 : ∀ x y : ℝ≥0∞, (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
    intro x y
    have h := ENNReal.rpow_add_le_mul_rpow_add_rpow x y (p := 2) (by norm_num)
    rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one, mul_add] at h
    simpa only [ENNReal.rpow_two] using h
  -- pointwise bound on the Whitney ball
  have hpt : ∀ᵐ Y ∂(volume.restrict (ball Z ((1 - ‖Z‖) / 4))),
      ENNReal.ofReal (u Y ^ 2) ≤ 2 * (CP * M) ^ 2 + 2 * B Y ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hP5] with Y hY hY5
    obtain ⟨hY1, -, h3, -⟩ := s07c_fkps_m5_wgeom hZ1 hY
    have hY𝔻 : Y ∈ unitDisc := mem_ball_zero_iff.2 hY1
    have hcone : ‖Y - exp (θ * I)‖ < 22 * (1 - ‖Y‖) := by
      have hYZ : ‖Y - Z‖ < (1 - ‖Z‖) / 4 := by rw [← dist_eq_norm]; exact hY
      have htri := norm_sub_le_norm_sub_add_norm_sub Y Z (exp (θ * I))
      have h2 := hZ.2
      linarith
    have hA := hP f hf hper θ Y hY𝔻 hcone
    have hu5 := hY5 hY𝔻
    calc ENNReal.ofReal (u Y ^ 2) = ENNReal.ofReal |u Y| ^ 2 := by
          rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      _ ≤ (CP * M + B Y) ^ 2 := by
          gcongr
          exact hu5.trans (add_le_add hA le_rfl)
      _ ≤ _ := hsq2 _ _
  have hvol : volume (ball Z ((1 - ‖Z‖) / 4)) =
      ENNReal.ofReal ((1 - ‖Z‖) ^ 2) * ENNReal.ofReal (π / 16) := by
    rw [Complex.volume_ball, ← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_coe_nnreal,
      NNReal.coe_real_pi, ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1; ring
  have hδ0 : ENNReal.ofReal ((1 - ‖Z‖) ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hδ 2)).ne'
  have hδt : ENNReal.ofReal ((1 - ‖Z‖) ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hFZ := hF g V m ε hg hV hm hm0 hε hVb hmb hcar θ Z hZ.1 hZ.2
  generalize hT : ((∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 34 * (1 - ‖z‖)}, (‖g Y‖₊ : ℝ≥0∞) ^ 2) +
      (∫⁻ t in Ioc (0 : ℝ) (2 * π),
        ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / ‖exp (t * I) - Z‖ ^ 2) *
          (∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (t * I)‖ < 16 * (1 - ‖z‖)},
            (‖g Y‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ)) ^ 2) = T at hFZ ⊢
  have hcπ : 0 ≤ c ^ 2 * π := mul_nonneg (sq_nonneg c) Real.pi_pos.le
  calc (∫⁻ Y in ball Z ((1 - ‖Z‖) / 4), ENNReal.ofReal (u Y ^ 2)) / ENNReal.ofReal ((1 - ‖Z‖) ^ 2)
      ≤ (∫⁻ Y in ball Z ((1 - ‖Z‖) / 4), (2 * (CP * M) ^ 2 + 2 * B Y ^ 2)) /
          ENNReal.ofReal ((1 - ‖Z‖) ^ 2) :=
        ENNReal.div_le_div_right (lintegral_mono_ae hpt) _
    _ = 2 * (CP * M) ^ 2 * ENNReal.ofReal (π / 16) +
          2 * ((∫⁻ Y in ball Z ((1 - ‖Z‖) / 4), B Y ^ 2) / ENNReal.ofReal ((1 - ‖Z‖) ^ 2)) := by
        rw [lintegral_add_left measurable_const, setLIntegral_const, hvol,
          lintegral_const_mul' _ _ (by simp), ENNReal.add_div]
        congr 1
        · rw [mul_comm (ENNReal.ofReal ((1 - ‖Z‖) ^ 2)), ← mul_assoc, ENNReal.mul_div_cancel_right hδ0 hδt]
        · rw [mul_div_assoc]
    _ ≤ 2 * (CP * M) ^ 2 * ENNReal.ofReal (π / 16) + 2 * (ENNReal.ofReal (C4 * ε) * T) :=
        add_le_add le_rfl (mul_le_mul_right hFZ 2)
    _ ≤ ENNReal.ofReal (c ^ 2 * π + 2 * C4 + 1) * M ^ 2 +
          ENNReal.ofReal (c ^ 2 * π + 2 * C4 + 1) * (ENNReal.ofReal ε * T) := by
        refine add_le_add ?_ ?_
        · have hc : 2 * CP ^ 2 * ENNReal.ofReal (π / 16) ≤ ENNReal.ofReal (c ^ 2 * π + 2 * C4 + 1) := by
            rw [hCP, ← ENNReal.ofReal_pow hc0,
              show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
              ← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            nlinarith [Real.pi_pos, hC4]
          calc 2 * (CP * M) ^ 2 * ENNReal.ofReal (π / 16) = (2 * CP ^ 2 * ENNReal.ofReal (π / 16)) * M ^ 2 := by
                ring
            _ ≤ _ := by gcongr
        · calc 2 * (ENNReal.ofReal (C4 * ε) * T) = ENNReal.ofReal (2 * C4) * (ENNReal.ofReal ε * T) := by
                rw [ENNReal.ofReal_mul hC4.le, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
                  ENNReal.ofReal_ofNat]
                ring
            _ ≤ _ := by
                gcongr
                linarith
    _ = _ := by rw [mul_add]

/-- M5 helper: `√x √y ≤ x + y` in `ℝ≥0∞`. -/
theorem s07c_fkps_m5_amgm (x y : ℝ≥0∞) : x ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ) ≤ x + y := by
  calc x ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ) ≤ (x + y) ^ (1 / 2 : ℝ) * (x + y) ^ (1 / 2 : ℝ) :=
        mul_le_mul' (ENNReal.rpow_le_rpow le_self_add (by norm_num))
          (ENNReal.rpow_le_rpow le_add_self (by norm_num))
    _ = x + y := by rw [← sq, s07c_fkps_m5_sqrt_sq]

/-- M5 helper (absorption): `E ≤ A + E/2` with `E < ⊤` gives `E ≤ 2A`. -/
theorem s07c_fkps_m5_absorb {E A : ℝ≥0∞} (hE : E ≠ ⊤) (h : E ≤ A + 2⁻¹ * E) : E ≤ 2 * A := by
  have h2 : 2⁻¹ * E + 2⁻¹ * E ≤ A + 2⁻¹ * E := by
    rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]; exact h
  have h3 : 2⁻¹ * E ≤ A := ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top (by simp) hE) h2
  calc E = 2 * (2⁻¹ * E) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ 2 * A := by gcongr

/-- M5 helper: the truncated Green function `G♭(Y) = (2π)⁻¹ log(1/max(|Y|, 1/2))` satisfies `0 ≤ G♭ ≤ 1` and
`δ(Y) ≤ 10 G♭(Y)` on `𝔻`. -/
theorem s07c_fkps_m5_gflat {Y : ℂ} (hY : ‖Y‖ < 1) :
    0 ≤ (2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2)) ∧
      (2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2)) ≤ 1 ∧
      1 - ‖Y‖ ≤ 10 * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2))) := by
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  have hlog2 := Real.log_two_lt_d9
  have hlog2' := Real.log_two_gt_d9
  set μ := max ‖Y‖ (1 / 2) with hμ
  have hμ1 : μ ≤ 1 := max_le hY.le (by norm_num)
  have hμ2 : 1 / 2 ≤ μ := le_max_right _ _
  have hμ0 : 0 < μ := by linarith
  have hL0 : 0 ≤ Real.log (1 / μ) := Real.log_nonneg (by rw [le_div_iff₀ hμ0]; linarith)
  have hL2 : Real.log (1 / μ) ≤ Real.log 2 :=
    Real.log_le_log (by positivity) (by rw [div_le_iff₀ hμ0]; linarith)
  have hinv : 0 < (2 * π)⁻¹ := by positivity
  have hY0 := norm_nonneg Y
  refine ⟨mul_nonneg hinv.le hL0, ?_, ?_⟩
  · calc (2 * π)⁻¹ * Real.log (1 / μ) ≤ (2 * π)⁻¹ * 1 := by gcongr; linarith
      _ ≤ 1 := by rw [mul_one]; exact inv_le_one_of_one_le₀ (by linarith)
  · have key : 2 * π * (1 - ‖Y‖) ≤ 10 * Real.log (1 / μ) := by
      rcases le_or_gt (1 / 2) ‖Y‖ with h | h
      · have hμe : μ = ‖Y‖ := max_eq_left h
        have hpos : 0 < ‖Y‖ := by linarith
        have hLd : 1 - ‖Y‖ ≤ Real.log (1 / μ) := by
          rw [hμe, one_div, Real.log_inv]
          linarith [Real.log_le_sub_one_of_pos hpos]
        have hδ0 : 0 ≤ 1 - ‖Y‖ := by linarith
        nlinarith [mul_le_mul_of_nonneg_right (show 2 * π ≤ 10 by linarith) hδ0]
      · have hμe : μ = 1 / 2 := max_eq_right h.le
        have hL : Real.log (1 / μ) = Real.log 2 := by rw [hμe]; norm_num
        have : 2 * π * (1 - ‖Y‖) ≤ 2 * π := by nlinarith
        rw [hL]; linarith
    rw [show 10 * ((2 * π)⁻¹ * Real.log (1 / μ)) = 10 * Real.log (1 / μ) / (2 * π) by ring,
      le_div_iff₀ (by positivity)]
    linarith

/-- M5 helper: cone integrals of `|g|²` are measurable in `θ`, and `∫_𝕋 ∫_{Γ_β(θ)} |g|² ≤ 4π(β+1) ∫_𝔻 |g|² δ`. -/
theorem s07c_fkps_m5_cone_bd (β : ℝ) (hβ : 0 < β) {g : ℂ → ℂ} (hg : AEMeasurable g) :
    Measurable (fun θ : ℝ =>
      ∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < β * (1 - ‖z‖)}, (‖g Y‖₊ : ℝ≥0∞) ^ 2) ∧
    ∫⁻ θ in Icc 0 (2 * π),
        ∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < β * (1 - ‖z‖)}, (‖g Y‖₊ : ℝ≥0∞) ^ 2 ≤
      ENNReal.ofReal (4 * π * (β + 1)) *
        ∫⁻ Y in unitDisc, (‖g Y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 - ‖Y‖) := by
  have hΦ : Measurable fun Y => (‖hg.mk g Y‖₊ : ℝ≥0∞) ^ 2 :=
    hg.measurable_mk.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hgg : ∀ s : Set ℂ, ∫⁻ Y in s, (‖g Y‖₊ : ℝ≥0∞) ^ 2 = ∫⁻ Y in s, (‖hg.mk g Y‖₊ : ℝ≥0∞) ^ 2 :=
    fun s => lintegral_congr_ae (ae_restrict_of_ae (hg.ae_eq_mk.mono fun Y h => by simp only [h]))
  have hT : ∫⁻ Y in unitDisc, (‖g Y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 - ‖Y‖) =
      ∫⁻ Y in unitDisc, (‖hg.mk g Y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 - ‖Y‖) :=
    lintegral_congr_ae (ae_restrict_of_ae (hg.ae_eq_mk.mono fun Y h => by simp only [h]))
  simp only [hgg, hT]
  exact ⟨s07c_fkps_m5_cone_meas β hΦ, s07c_fkps_m5_aperture β hβ _ hΦ⟩

/-- M5 helper: `∫_𝔻 |g|² δ ≤ 10 ∫_𝔻 |g|² G♭` and `∫_𝔻 |g|² G♭ ≤ ∫_𝔻 |g|²`. -/
theorem s07c_fkps_m5_energy (g : ℂ → ℂ) :
    ∫⁻ Y in unitDisc, (‖g Y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 - ‖Y‖) ≤ ENNReal.ofReal 10 *
      ∫⁻ Y in unitDisc, ENNReal.ofReal (‖g Y‖ ^ 2 * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2)))) ∧
    ∫⁻ Y in unitDisc, ENNReal.ofReal (‖g Y‖ ^ 2 * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2)))) ≤
      ∫⁻ Y in unitDisc, (‖g Y‖₊ : ℝ≥0∞) ^ 2 := by
  have h𝔻 : MeasurableSet unitDisc := measurableSet_ball
  constructor
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' h𝔻 (fun Y hY => ?_)
    obtain ⟨-, -, hGδ⟩ := s07c_fkps_m5_gflat (mem_ball_zero_iff.1 hY)
    rw [← enorm_eq_nnnorm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [mul_le_mul_of_nonneg_left hGδ (sq_nonneg ‖g Y‖)]
  · refine setLIntegral_mono' h𝔻 (fun Y hY => ?_)
    obtain ⟨-, hG1, -⟩ := s07c_fkps_m5_gflat (mem_ball_zero_iff.1 hY)
    rw [← enorm_eq_nnnorm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (sq_nonneg _) hG1)

/-- M5 helper (second term of (P7')): if `|V| ≤ m |g|` and `m ≤ c` a.e. on `𝔻`, then
`∫_𝔻 |V| |g| G♭ ≤ c ∫_𝔻 |g|² G♭`. -/
theorem s07c_fkps_m5_term2 {g V : ℂ → ℂ} {m : ℂ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hVb : ∀ᵐ z, z ∈ unitDisc → ‖V z‖ ≤ m z * ‖g z‖) (hmb : ∀ᵐ z, z ∈ unitDisc → m z ≤ c) :
    (∫⁻ Y in unitDisc,
        ENNReal.ofReal (‖V Y‖ * ‖g Y‖ * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2))))) ≤
      ENNReal.ofReal c *
        ∫⁻ Y in unitDisc, ENNReal.ofReal (‖g Y‖ ^ 2 * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2)))) := by
  have h𝔻 : MeasurableSet unitDisc := measurableSet_ball
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem h𝔻, ae_restrict_of_ae hVb, ae_restrict_of_ae hmb] with Y hY hVY hmY
  obtain ⟨hG0, -, -⟩ := s07c_fkps_m5_gflat (mem_ball_zero_iff.1 hY)
  rw [← ENNReal.ofReal_mul hc]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : ‖V Y‖ ≤ c * ‖g Y‖ := (hVY hY).trans (mul_le_mul_of_nonneg_right (hmY hY) (norm_nonneg _))
  have := mul_le_mul_of_nonneg_right h1 (mul_nonneg (norm_nonneg (g Y)) hG0)
  nlinarith [this]

/-- M5 helper (third term of (P7')): `∫_{𝔻 ∖ B(0,1/2)} |u| |V| / (2π|Y|) ≤ π⁻¹ ∫_𝔻 |u| m |g|` when `|V| ≤ m|g|`. -/
theorem s07c_fkps_m5_term3 {g V : ℂ → ℂ} {m u : ℂ → ℝ} (hm0 : ∀ z, 0 ≤ m z)
    (hVb : ∀ᵐ z, z ∈ unitDisc → ‖V z‖ ≤ m z * ‖g z‖) :
    (∫⁻ Y in unitDisc \ ball 0 (1 / 2), ENNReal.ofReal (|u Y| * ‖V Y‖ / (2 * π * ‖Y‖))) ≤
      ENNReal.ofReal π⁻¹ * ∫⁻ Y in unitDisc, ENNReal.ofReal (|u Y| * m Y * ‖g Y‖) := by
  have h𝔻 : MeasurableSet unitDisc := measurableSet_ball
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc _ ≤ ∫⁻ Y in unitDisc \ ball 0 (1 / 2),
        ENNReal.ofReal π⁻¹ * ENNReal.ofReal (|u Y| * m Y * ‖g Y‖) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem (h𝔻.diff measurableSet_ball), ae_restrict_of_ae hVb] with Y hY hVY
        have hY12 : 1 / 2 ≤ ‖Y‖ := by
          have h := hY.2
          rw [mem_ball_zero_iff, not_lt] at h
          exact h
        have hVY' := hVY hY.1
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 Real.pi_pos.le)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hYpos : 0 < ‖Y‖ := by linarith
        rw [div_le_iff₀ (by positivity)]
        have hu0 := abs_nonneg (u Y)
        have hp : 0 ≤ |u Y| * m Y * ‖g Y‖ := mul_nonneg (mul_nonneg hu0 (hm0 Y)) (norm_nonneg _)
        calc |u Y| * ‖V Y‖ ≤ |u Y| * (m Y * ‖g Y‖) := mul_le_mul_of_nonneg_left hVY' hu0
          _ = (|u Y| * m Y * ‖g Y‖) * 1 := by ring
          _ ≤ (|u Y| * m Y * ‖g Y‖) * (2 * ‖Y‖) := mul_le_mul_of_nonneg_left (by linarith) hp
          _ = π⁻¹ * (|u Y| * m Y * ‖g Y‖) * (2 * π * ‖Y‖) := by
              rw [show π⁻¹ * (|u Y| * m Y * ‖g Y‖) * (2 * π * ‖Y‖) =
                (|u Y| * m Y * ‖g Y‖) * (2 * ‖Y‖) * (π⁻¹ * π) by ring,
                inv_mul_cancel₀ Real.pi_ne_zero, mul_one]
    _ ≤ _ := lintegral_mono_set Set.sdiff_subset

/-- M5 helper: boundary control of `h = S^{1/2}` for a periodic `S` with `∫_𝕋 S < ∞`:
`∫_𝕋 (M h)² ≤ C ∫_𝕋 S`, and `P[S^{1/2}](Z) ≤ C M h(θ)` on the cone of aperture `16` at `θ`. -/
theorem s07c_fkps_m5_sqrt_bdry : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ S : ℝ → ℝ≥0∞, Measurable S →
    (∀ t, S (t + 2 * π) = S t) → ∫⁻ t in Icc 0 (2 * π), S t ≠ ⊤ →
    (∫⁻ θ in Icc 0 (2 * π),
        TauCeti.maximalFunction volume (fun t => (S t ^ (1 / 2 : ℝ)).toReal) θ ^ 2 ≤
      C * ∫⁻ t in Icc 0 (2 * π), S t) ∧
    ∀ θ : ℝ, ∀ Z ∈ {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 16 * (1 - ‖z‖)},
      ∫⁻ t in Ioc (0 : ℝ) (2 * π),
          ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / ‖exp (t * I) - Z‖ ^ 2) * S t ^ (1 / 2 : ℝ) ≤
        C * TauCeti.maximalFunction volume (fun t => (S t ^ (1 / 2 : ℝ)).toReal) θ := by
  obtain ⟨CP, hCPt, hP16⟩ := s07c_fkps_m2_nt_lint 16 (by norm_num)
  obtain ⟨CM, hCMt, hML2⟩ := s07c_fkps_m2_maxL2
  refine ⟨CM + ENNReal.ofReal (2 * π) * CP,
    ENNReal.add_ne_top.2 ⟨hCMt, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCPt⟩, ?_⟩
  intro S hSm hSper hSfin
  set h : ℝ → ℝ := fun t => (S t ^ (1 / 2 : ℝ)).toReal with hh
  have hhm : Measurable h := (hSm.pow_const _).ennreal_toReal
  have hhper : ∀ t, h (t + 2 * π) = h t := fun t => by simp only [hh, hSper]
  have hhe : ∀ᵐ t ∂(volume.restrict (Icc 0 (2 * π))), ‖h t‖ₑ = S t ^ (1 / 2 : ℝ) := by
    filter_upwards [ae_lt_top hSm hSfin] with t ht
    simp only [hh]
    rw [← ofReal_norm, Real.norm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ht.ne
  have hL2 : ∫⁻ t in Icc 0 (2 * π), ‖h t‖ₑ ^ 2 = ∫⁻ t in Icc 0 (2 * π), S t :=
    lintegral_congr_ae (hhe.mono fun t ht => by simp only [ht, s07c_fkps_m5_sqrt_sq])
  refine ⟨?_, ?_⟩
  · calc _ ≤ CM * ∫⁻ t in Icc 0 (2 * π), ‖h t‖ₑ ^ 2 := hML2 h hhm hhper
      _ ≤ _ := by rw [hL2]; exact mul_le_mul_left le_self_add _
  · intro θ Z hZ
    have h1 := hP16 h hhm hhper θ Z hZ.1 hZ.2
    calc ∫⁻ t in Ioc (0 : ℝ) (2 * π),
          ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / ‖exp (t * I) - Z‖ ^ 2) * S t ^ (1 / 2 : ℝ)
        ≤ ∫⁻ t in Icc 0 (2 * π),
          ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / ‖exp (t * I) - Z‖ ^ 2) * S t ^ (1 / 2 : ℝ) :=
          lintegral_mono_set Ioc_subset_Icc_self
      _ = ∫⁻ t in Icc 0 (2 * π), ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / ‖exp (t * I) - Z‖ ^ 2) * ‖h t‖ₑ :=
          lintegral_congr_ae (hhe.mono fun t ht => by simp only [ht])
      _ = ENNReal.ofReal (2 * π) * (ENNReal.ofReal (2 * π)⁻¹ * ∫⁻ t in Icc 0 (2 * π),
            ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / ‖exp (t * I) - Z‖ ^ 2) * ‖h t‖ₑ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * π),
            mul_inv_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0), ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (2 * π) * (CP * TauCeti.maximalFunction volume h θ) := mul_le_mul_right h1 _
      _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_left le_add_self _

/-- M5 helper (duality step): under the M5 package without (P7'), with `T = ∫_𝔻 |g|² δ < ∞`,
`∫_𝔻 |u| m |g| ≤ (∫_𝕋 f² + ε T)^{1/2} (C ε T)^{1/2}` (M5.5 with `R` from M5.6). -/
theorem s07c_fkps_m5_dual : ∃ C : ℝ, 0 < C ∧ ∀ (g V : ℂ → ℂ) (m a u : ℂ → ℝ) (f : ℝ → ℝ) (ε : ℝ),
    AEMeasurable g → AEMeasurable V → AEMeasurable m → Measurable a → Measurable u → Measurable f →
    (∀ t, f (t + 2 * π) = f t) → (∀ z, 0 ≤ m z) → (∀ z, 0 ≤ a z) → 0 ≤ ε →
    (∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) → m w ≤ a z) →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)) ≤ ENNReal.ofReal (ε * r)) →
    (∀ᵐ z, z ∈ unitDisc → ‖V z‖ ≤ m z * ‖g z‖) →
    ∫⁻ Y in unitDisc, (‖g Y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 - ‖Y‖) ≠ ⊤ →
    (∀ᵐ X, X ∈ unitDisc → ENNReal.ofReal |u X| ≤
      ENNReal.ofReal (2 * π)⁻¹ * (∫⁻ t in Icc 0 (2 * π),
        ENNReal.ofReal ((1 - ‖X‖ ^ 2) / ‖exp (t * I) - X‖ ^ 2) * ‖f t‖ₑ) +
      ∫⁻ Y in unitDisc,
        ENNReal.ofReal ((1 - ‖X‖ ^ 2) / (2 * π * ‖X - Y‖ * ‖1 - X * conj Y‖)) * ‖V Y‖₊) →
    ∫⁻ Y in unitDisc, ENNReal.ofReal (|u Y| * m Y * ‖g Y‖) ≤
      ((∫⁻ t in Icc 0 (2 * π), ‖f t‖ₑ ^ 2) + ENNReal.ofReal ε *
          ∫⁻ Y in unitDisc, (‖g Y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 - ‖Y‖)) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (C * ε) *
          ∫⁻ Y in unitDisc, (‖g Y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 - ‖Y‖)) ^ (1 / 2 : ℝ) := by
  obtain ⟨C1, hC1, hPW⟩ := s07c_fkps_m4_pointwise
  obtain ⟨Cd, hCd, hDW⟩ := s07c_fkps_m5_duality_w
  obtain ⟨Cu, hCu, hNTU⟩ := s07c_fkps_m5_ntu
  obtain ⟨C5, hC5t, hSB⟩ := s07c_fkps_m5_sqrt_bdry
  obtain ⟨CM, hCMt, hML2⟩ := s07c_fkps_m2_maxL2
  set K : ℝ := C1 ^ 2 + C1 + 1 with hKdef
  have hK : 0 < K := by positivity
  set W : ℝ≥0∞ := ENNReal.ofReal (4 * π * (34 + 1)) + C5 ^ 2 * (C5 * ENNReal.ofReal (4 * π * (16 + 1)))
    with hWdef
  have hWt : W ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hC5t) (ENNReal.mul_ne_top hC5t ENNReal.ofReal_ne_top)⟩
  set w := W.toReal with hwdef
  have hw0 : 0 ≤ w := ENNReal.toReal_nonneg
  have hW : W = ENNReal.ofReal w := (ENNReal.ofReal_toReal hWt).symm
  set cM := CM.toReal with hcMdef
  have hcM0 : 0 ≤ cM := ENNReal.toReal_nonneg
  have hCM : CM = ENNReal.ofReal cM := (ENNReal.ofReal_toReal hCMt).symm
  set C' : ℝ := Cu * (cM + K * w + 1) with hC'def
  have hC' : 0 < C' := by positivity
  refine ⟨Cd ^ 2 * C', by positivity, ?_⟩
  intro g V m a u f ε hg hV hm ha hu hf hper hm0 ha0 hε hM hC hVb hTfin hP5
  obtain ⟨hmb, hmcar⟩ := hPW m a ε hm ha hm0 ha0 hε hM hC
  have hKε : 0 ≤ K * ε := by positivity
  have hmb' : ∀ᵐ z, z ∈ unitDisc → m z ≤ Real.sqrt (K * ε) := by
    filter_upwards [hmb] with z hz hz𝔻
    refine (hz hz𝔻).trans ?_
    rw [Real.sqrt_mul hK.le]
    have hC1K : C1 ≤ Real.sqrt K := by
      rw [show C1 = Real.sqrt (C1 ^ 2) from (Real.sqrt_sq hC1.le).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    exact mul_le_mul_of_nonneg_right hC1K (Real.sqrt_nonneg _)
  have hmcar' : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (m z ^ 2 / (1 - ‖z‖)) ≤ ENNReal.ofReal (K * ε * r) := by
    intro ζ hζ r hr hr2
    refine (hmcar ζ hζ r hr hr2).trans (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ ε * r := by positivity
    nlinarith
  obtain ⟨hS16m, hA16⟩ := s07c_fkps_m5_cone_bd 16 (by norm_num) hg
  obtain ⟨hS34m, hA34⟩ := s07c_fkps_m5_cone_bd 34 (by norm_num) hg
  set T := ∫⁻ Y in unitDisc, (‖g Y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 - ‖Y‖) with hTdef
  set F := ∫⁻ t in Icc 0 (2 * π), ‖f t‖ₑ ^ 2 with hFdef
  set S16 : ℝ → ℝ≥0∞ := fun θ : ℝ =>
    ∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 16 * (1 - ‖z‖)}, (‖g Y‖₊ : ℝ≥0∞) ^ 2 with hS16
  set S34 : ℝ → ℝ≥0∞ := fun θ : ℝ =>
    ∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 34 * (1 - ‖z‖)}, (‖g Y‖₊ : ℝ≥0∞) ^ 2 with hS34
  have hS16per : ∀ t, S16 (t + 2 * π) = S16 t := by
    intro t
    simp only [hS16, s07c_fkps_m2_exp_periodic]
  have hA16fin : ∫⁻ θ in Icc 0 (2 * π), S16 θ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTfin) hA16
  obtain ⟨hMh2, hPterm⟩ := hSB S16 hS16m hS16per hA16fin
  set Mf := TauCeti.maximalFunction volume f with hMf
  set Mh := TauCeti.maximalFunction volume (fun t => (S16 t ^ (1 / 2 : ℝ)).toReal) with hMh
  have hMfm : Measurable Mf := TauCeti.measurable_maximalFunction volume f
  have hMhm : Measurable Mh := TauCeti.measurable_maximalFunction volume _
  set R : ℝ → ℝ≥0∞ := fun θ =>
    ENNReal.ofReal Cu * (Mf θ ^ 2 + ENNReal.ofReal (K * ε) * (S34 θ + (C5 * Mh θ) ^ 2)) with hRdef
  have hRm : Measurable R :=
    measurable_const.mul ((hMfm.pow_const 2).add
      (measurable_const.mul (hS34m.add ((measurable_const.mul hMhm).pow_const 2))))
  have hRbound : ∀ θ : ℝ, ∀ Z ∈ {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 16 * (1 - ‖z‖)},
      (∫⁻ Y in ball Z ((1 - ‖Z‖) / 4), ENNReal.ofReal (u Y ^ 2)) / ENNReal.ofReal ((1 - ‖Z‖) ^ 2) ≤
        R θ := by
    intro θ Z hZ
    refine (hNTU g V m u f (K * ε) hg hV hm hu hf hper hm0 hKε hVb hmb' hmcar' hP5 θ Z hZ).trans ?_
    rw [hRdef]
    refine mul_le_mul_right (add_le_add le_rfl (mul_le_mul_right (add_le_add le_rfl ?_) _)) _
    gcongr
    exact hPterm θ Z hZ
  have hdual := hDW g m a u R ε hg hm ha hu hRm hm0 ha0 hε hM hC hRbound
  set Rint := ∫⁻ θ in Icc 0 (2 * π), R θ with hRint
  have hRint1 : Rint ≤ ENNReal.ofReal Cu * (CM * F + ENNReal.ofReal (K * ε) * (W * T)) := by
    have e1 : Rint = ENNReal.ofReal Cu * ((∫⁻ θ in Icc 0 (2 * π), Mf θ ^ 2) + ENNReal.ofReal (K * ε) *
        ((∫⁻ θ in Icc 0 (2 * π), S34 θ) + C5 ^ 2 * ∫⁻ θ in Icc 0 (2 * π), Mh θ ^ 2)) := by
      simp only [hRint, hRdef, mul_pow]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left (hMfm.pow_const 2),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hS34m,
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top hC5t)]
    have hMf2 : ∫⁻ θ in Icc 0 (2 * π), Mf θ ^ 2 ≤ CM * F := hML2 f hf hper
    rw [e1]
    calc _ ≤ ENNReal.ofReal Cu * (CM * F + ENNReal.ofReal (K * ε) *
          (ENNReal.ofReal (4 * π * (34 + 1)) * T +
            C5 ^ 2 * (C5 * (ENNReal.ofReal (4 * π * (16 + 1)) * T)))) :=
          mul_le_mul_right (add_le_add hMf2 (mul_le_mul_right (add_le_add hA34
            (mul_le_mul_right (hMh2.trans (mul_le_mul_right hA16 _)) _)) _)) _
      _ = _ := by rw [hWdef]; ring
  have hRint2 : Rint ≤ ENNReal.ofReal C' * (F + ENNReal.ofReal ε * T) := by
    refine hRint1.trans ?_
    rw [hCM, hW, ENNReal.ofReal_mul hK.le]
    calc ENNReal.ofReal Cu * (ENNReal.ofReal cM * F + ENNReal.ofReal K * ENNReal.ofReal ε * (ENNReal.ofReal w * T))
        = ENNReal.ofReal (Cu * cM) * F + ENNReal.ofReal (Cu * K * w) * (ENNReal.ofReal ε * T) := by
          rw [ENNReal.ofReal_mul hCu.le, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Cu * K),
            ENNReal.ofReal_mul hCu.le]
          ring
      _ ≤ ENNReal.ofReal C' * F + ENNReal.ofReal C' * (ENNReal.ofReal ε * T) := by
          refine add_le_add (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
            (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
          · have : 0 ≤ Cu * (K * w) := by positivity
            rw [hC'def]; nlinarith
          · have : 0 ≤ Cu * cM := by positivity
            rw [hC'def]; nlinarith
      _ = _ := by rw [mul_add]
  have hscal : ENNReal.ofReal (Cd * Real.sqrt ε) * ENNReal.ofReal C' ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Cd ^ 2 * C' * ε) ^ (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hC'.le (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Cd * Real.sqrt ε)]
    congr 1
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Cd ^ 2 * C'),
      Real.sqrt_mul (sq_nonneg Cd), Real.sqrt_sq hCd.le]
    ring
  calc ∫⁻ Y in unitDisc, ENNReal.ofReal (|u Y| * m Y * ‖g Y‖)
      ≤ ENNReal.ofReal (Cd * Real.sqrt ε) * Rint ^ (1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) := hdual
    _ ≤ ENNReal.ofReal (Cd * Real.sqrt ε) * (ENNReal.ofReal C' * (F + ENNReal.ofReal ε * T)) ^ (1 / 2 : ℝ) *
          T ^ (1 / 2 : ℝ) :=
        mul_le_mul_left (mul_le_mul_right (ENNReal.rpow_le_rpow hRint2 (by norm_num)) _) _
    _ = (F + ENNReal.ofReal ε * T) ^ (1 / 2 : ℝ) * (ENNReal.ofReal (Cd ^ 2 * C' * ε) * T) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← hscal]
        ring

/-- M5 helper (output (ii)): M5.4 at `X = 0`, averaged over `θ`:
`∫_{B(0,1/4)} (∫_𝔻 K |V|)² ≤ C ε ∫_𝔻 |g|² δ`. -/
theorem s07c_fkps_m5_origin : ∃ C : ℝ, 0 < C ∧ ∀ (g V : ℂ → ℂ) (m : ℂ → ℝ) (ε : ℝ),
    AEMeasurable g → AEMeasurable V → AEMeasurable m → (∀ z, 0 ≤ m z) → 0 ≤ ε →
    (∀ᵐ z, z ∈ unitDisc → ‖V z‖ ≤ m z * ‖g z‖) →
    (∀ᵐ z, z ∈ unitDisc → m z ≤ Real.sqrt ε) →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (m z ^ 2 / (1 - ‖z‖)) ≤ ENNReal.ofReal (ε * r)) →
    (∫⁻ Z in ball 0 (1 / 4), (∫⁻ Y in unitDisc,
        ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / (2 * π * ‖Z - Y‖ * ‖1 - Z * conj Y‖)) * ‖V Y‖₊) ^ 2) ≤
      ENNReal.ofReal (C * ε) * ∫⁻ Y in unitDisc, (‖g Y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 - ‖Y‖) := by
  obtain ⟨C4, hC4, hF16⟩ := s07c_fkps_m5_ntF16
  have hpi := Real.pi_gt_three
  set w2 : ℝ := 4 * π * (34 + 1) + 2 * π * (2 * π * (4 * π * (16 + 1))) with hw2def
  have hw2 : 0 < w2 := by positivity
  refine ⟨C4 * w2, by positivity, ?_⟩
  intro g V m ε hg hV hm hm0 hε hVb hmb hcar
  obtain ⟨hS16m, hA16⟩ := s07c_fkps_m5_cone_bd 16 (by norm_num) hg
  obtain ⟨-, hA34⟩ := s07c_fkps_m5_cone_bd 34 (by norm_num) hg
  set T := ∫⁻ Y in unitDisc, (‖g Y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 - ‖Y‖) with hTdef
  set S16 : ℝ → ℝ≥0∞ := fun θ : ℝ =>
    ∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 16 * (1 - ‖z‖)}, (‖g Y‖₊ : ℝ≥0∞) ^ 2 with hS16
  set S34 : ℝ → ℝ≥0∞ := fun θ : ℝ =>
    ∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 34 * (1 - ‖z‖)}, (‖g Y‖₊ : ℝ≥0∞) ^ 2 with hS34
  have h0cone : ∀ θ : ℝ, (0 : ℂ) ∈ unitDisc ∧ ‖(0 : ℂ) - exp (θ * I)‖ < 16 * (1 - ‖(0 : ℂ)‖) := by
    intro θ
    refine ⟨mem_ball_self one_pos, ?_⟩
    simp
  set L := ∫⁻ Z in ball (0 : ℂ) (1 / 4), (∫⁻ Y in unitDisc,
      ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / (2 * π * ‖Z - Y‖ * ‖1 - Z * conj Y‖)) * ‖V Y‖₊) ^ 2 with hLdef
  set Q := ∫⁻ t in Ioc (0 : ℝ) (2 * π), S16 t ^ (1 / 2 : ℝ) with hQdef
  have e1 : ((1 : ℝ) - ‖(0 : ℂ)‖) / 4 = 1 / 4 := by simp
  have e2 : ENNReal.ofReal ((1 - ‖(0 : ℂ)‖) ^ 2) = 1 := by simp
  have e3 : ∀ t : ℝ, ENNReal.ofReal ((1 - ‖(0 : ℂ)‖ ^ 2) / ‖exp (t * I) - 0‖ ^ 2) = 1 := by
    intro t; simp
  have hLθ : ∀ θ : ℝ, L ≤ ENNReal.ofReal (C4 * ε) * (S34 θ + Q ^ 2) := by
    intro θ
    have h := hF16 g V m ε hg hV hm hm0 hε hVb hmb hcar θ 0 (h0cone θ).1 (h0cone θ).2
    rw [e1, e2, div_one] at h
    simp only [e3, one_mul] at h
    exact h
  have hQ : Q ^ 2 ≤ ENNReal.ofReal (2 * π) * ∫⁻ t in Icc 0 (2 * π), S16 t := by
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioc (0 : ℝ) (2 * π)))
      Real.HolderConjugate.two_two (aemeasurable_const : AEMeasurable (fun _ : ℝ => (1 : ℝ≥0∞)) _)
      (hS16m.pow_const (1 / 2 : ℝ)).aemeasurable
    simp only [Pi.mul_apply, one_mul, one_pow, ENNReal.rpow_two, s07c_fkps_m5_sqrt_sq,
      setLIntegral_const, Real.volume_Ioc, sub_zero] at hH
    calc Q ^ 2 ≤ ((ENNReal.ofReal (2 * π)) ^ (1 / 2 : ℝ) *
          (∫⁻ t in Ioc (0 : ℝ) (2 * π), S16 t) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
      _ = ENNReal.ofReal (2 * π) * ∫⁻ t in Ioc (0 : ℝ) (2 * π), S16 t := by
          rw [mul_pow, s07c_fkps_m5_sqrt_sq, s07c_fkps_m5_sqrt_sq]
      _ ≤ _ := mul_le_mul_right (lintegral_mono_set Ioc_subset_Icc_self) _
  have hint : ENNReal.ofReal (2 * π) * L ≤ ENNReal.ofReal (C4 * ε) *
      ((∫⁻ θ in Icc 0 (2 * π), S34 θ) + ENNReal.ofReal (2 * π) * Q ^ 2) := by
    calc ENNReal.ofReal (2 * π) * L = ∫⁻ θ in Icc 0 (2 * π), L := by
          rw [setLIntegral_const, Real.volume_Icc, sub_zero, mul_comm]
      _ ≤ ∫⁻ θ in Icc 0 (2 * π), ENNReal.ofReal (C4 * ε) * (S34 θ + Q ^ 2) :=
          lintegral_mono fun θ => hLθ θ
      _ = _ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right _ measurable_const,
            setLIntegral_const, Real.volume_Icc, sub_zero, mul_comm (Q ^ 2)]
  have hw2eq : ENNReal.ofReal (4 * π * (34 + 1)) + ENNReal.ofReal (2 * π) * (ENNReal.ofReal (2 * π) *
      ENNReal.ofReal (4 * π * (16 + 1))) = ENNReal.ofReal w2 := by
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * π),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * π),
      ← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 4 * π * (34 + 1))
        (by positivity : (0 : ℝ) ≤ 2 * π * (2 * π * (4 * π * (16 + 1))))]
  have hfin : ENNReal.ofReal (2 * π) * L ≤ ENNReal.ofReal (2 * π) * (ENNReal.ofReal (C4 * w2 * ε) * T) := by
    calc ENNReal.ofReal (2 * π) * L ≤ ENNReal.ofReal (C4 * ε) *
          ((∫⁻ θ in Icc 0 (2 * π), S34 θ) + ENNReal.ofReal (2 * π) * Q ^ 2) := hint
      _ ≤ ENNReal.ofReal (C4 * ε) * (ENNReal.ofReal (4 * π * (34 + 1)) * T + ENNReal.ofReal (2 * π) *
          (ENNReal.ofReal (2 * π) * (ENNReal.ofReal (4 * π * (16 + 1)) * T))) :=
          mul_le_mul_right (add_le_add hA34 (mul_le_mul_right (hQ.trans (mul_le_mul_right hA16 _)) _)) _
      _ = ENNReal.ofReal (C4 * ε) * ENNReal.ofReal w2 * T := by
          rw [← hw2eq]; ring
      _ = ENNReal.ofReal (C4 * w2 * ε) * T := by
          rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C4 * ε), show C4 * ε * w2 = C4 * w2 * ε by ring]
      _ ≤ ENNReal.ofReal (2 * π) * (ENNReal.ofReal (C4 * w2 * ε) * T) := by
          refine le_mul_of_one_le_left zero_le (ENNReal.one_le_ofReal.2 (by linarith))
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top).1 hfin

/-- M5 (FKP Lemma 2.10 + absorption, plane case). There are `ε₀, C > 0` such that, for the abstract M3 package
(`‖V‖ ≤ m ‖g‖` a.e. on `𝔻`, `m ≤ a z` a.e. on Whitney balls with `a²/(1-|z|²)` Carleson of norm `ε ≤ ε₀`, finite
energy, (P5') and (P7')), the area function is bounded by the data, `∫_𝕋 S₁₆² ≤ C ∫_𝕋 f²`, and the absolute
potential is small at the origin in Whitney `L²`, `∫_{B(0,1/4)} (∫_𝔻 K |V|)² ≤ C ε ∫_𝕋 f²`. -/
theorem s07c_fkps_m5 : ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧
    ∀ (g V : ℂ → ℂ) (m a u : ℂ → ℝ) (f : ℝ → ℝ) (ε : ℝ),
    AEMeasurable g → AEMeasurable V → AEMeasurable m → Measurable a → Measurable u → Measurable f →
    (∀ t, f (t + 2 * π) = f t) → (∀ z, 0 ≤ m z) → (∀ z, 0 ≤ a z) → 0 ≤ ε → ε ≤ ε₀ →
    (∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) → m w ≤ a z) →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)) ≤ ENNReal.ofReal (ε * r)) →
    (∀ᵐ z, z ∈ unitDisc → ‖V z‖ ≤ m z * ‖g z‖) →
    (∫⁻ z in unitDisc, (‖g z‖₊ : ℝ≥0∞) ^ 2) < ⊤ →
    (∀ᵐ X, X ∈ unitDisc → ENNReal.ofReal |u X| ≤
      ENNReal.ofReal (2 * π)⁻¹ * (∫⁻ t in Icc 0 (2 * π),
        ENNReal.ofReal ((1 - ‖X‖ ^ 2) / ‖exp (t * I) - X‖ ^ 2) * ‖f t‖ₑ) +
      ∫⁻ Y in unitDisc,
        ENNReal.ofReal ((1 - ‖X‖ ^ 2) / (2 * π * ‖X - Y‖ * ‖1 - X * conj Y‖)) * ‖V Y‖₊) →
    ((∫⁻ Y in unitDisc,
        ENNReal.ofReal (‖g Y‖ ^ 2 * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2))))) ≤
      ENNReal.ofReal (4 * π)⁻¹ * (∫⁻ t in Icc 0 (2 * π), ‖f t‖ₑ ^ 2) +
        (∫⁻ Y in unitDisc,
          ENNReal.ofReal (‖V Y‖ * ‖g Y‖ * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2))))) +
        (∫⁻ Y in unitDisc \ ball 0 (1 / 2), ENNReal.ofReal (|u Y| * ‖V Y‖ / (2 * π * ‖Y‖)))) →
    ((∫⁻ θ in Icc 0 (2 * π),
        ∫⁻ Y in {z | z ∈ unitDisc ∧ ‖z - exp (θ * I)‖ < 16 * (1 - ‖z‖)}, (‖g Y‖₊ : ℝ≥0∞) ^ 2) ≤
      ENNReal.ofReal C * ∫⁻ t in Icc 0 (2 * π), ‖f t‖ₑ ^ 2) ∧
    ((∫⁻ Z in ball 0 (1 / 4), (∫⁻ Y in unitDisc,
        ENNReal.ofReal ((1 - ‖Z‖ ^ 2) / (2 * π * ‖Z - Y‖ * ‖1 - Z * conj Y‖)) * ‖V Y‖₊) ^ 2) ≤
      ENNReal.ofReal (C * ε) * ∫⁻ t in Icc 0 (2 * π), ‖f t‖ₑ ^ 2) := by
  obtain ⟨C1, hC1, hPW⟩ := s07c_fkps_m4_pointwise
  obtain ⟨C6, hC6, hDu⟩ := s07c_fkps_m5_dual
  obtain ⟨C7, hC7, hOr⟩ := s07c_fkps_m5_origin
  have hpi := Real.pi_gt_three
  set K : ℝ := C1 ^ 2 + C1 + 1 with hKdef
  have hK : 0 < K := by positivity
  set aF : ℝ := 2 * ((4 * π)⁻¹ + 1) with haFdef
  have haF : 0 < aF := by positivity
  have hden : 0 < 16 * C1 ^ 2 + 40 * (1 + C6) + 1 := by positivity
  refine ⟨1 / (16 * C1 ^ 2 + 40 * (1 + C6) + 1), 680 * π * aF + C7 * K * 10 * aF, by positivity,
    by positivity, ?_⟩
  intro g V m a u f ε hg hV hm ha hu hf hper hm0 ha0 hε hεε₀ hM hC hVb hgfin hP5 hP7
  have hεX : ε * (16 * C1 ^ 2 + 40 * (1 + C6) + 1) ≤ 1 := (le_div_iff₀ hden).1 hεε₀
  obtain ⟨hmb, hmcar⟩ := hPW m a ε hm ha hm0 ha0 hε hM hC
  have hKε : 0 ≤ K * ε := by positivity
  have hmb' : ∀ᵐ z, z ∈ unitDisc → m z ≤ Real.sqrt (K * ε) := by
    filter_upwards [hmb] with z hz hz𝔻
    refine (hz hz𝔻).trans ?_
    rw [Real.sqrt_mul hK.le]
    have hC1K : C1 ≤ Real.sqrt K := by
      rw [show C1 = Real.sqrt (C1 ^ 2) from (Real.sqrt_sq hC1.le).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    exact mul_le_mul_of_nonneg_right hC1K (Real.sqrt_nonneg _)
  have hmcar' : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (m z ^ 2 / (1 - ‖z‖)) ≤ ENNReal.ofReal (K * ε * r) := by
    intro ζ hζ r hr hr2
    refine (hmcar ζ hζ r hr hr2).trans (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ ε * r := by positivity
    nlinarith
  obtain ⟨hTE, hEle1⟩ := s07c_fkps_m5_energy g
  set T := ∫⁻ Y in unitDisc, (‖g Y‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal (1 - ‖Y‖) with hTdef
  set E := ∫⁻ Y in unitDisc,
    ENNReal.ofReal (‖g Y‖ ^ 2 * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2)))) with hEdef
  set F := ∫⁻ t in Icc 0 (2 * π), ‖f t‖ₑ ^ 2 with hFdef
  have hEfin : E ≠ ⊤ := ne_top_of_le_ne_top hgfin.ne hEle1
  have hTfin : T ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEfin) hTE
  have hterm2 := s07c_fkps_m5_term2 (by positivity : (0 : ℝ) ≤ C1 * Real.sqrt ε) hVb hmb
  have hterm3 := s07c_fkps_m5_term3 (u := u) hm0 hVb
  have hdual := hDu g V m a u f ε hg hV hm ha hu hf hper hm0 ha0 hε hM hC hVb hTfin hP5
  have hpi1 : ENNReal.ofReal π⁻¹ ≤ 1 := ENNReal.ofReal_le_one.2 (inv_le_one_of_one_le₀ (by linarith))
  have hterm3' : (∫⁻ Y in unitDisc \ ball 0 (1 / 2), ENNReal.ofReal (|u Y| * ‖V Y‖ / (2 * π * ‖Y‖))) ≤
      F + ENNReal.ofReal ε * T + ENNReal.ofReal (C6 * ε) * T := by
    refine hterm3.trans ((mul_le_mul_right hdual _).trans ?_)
    calc ENNReal.ofReal π⁻¹ * ((F + ENNReal.ofReal ε * T) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal (C6 * ε) * T) ^ (1 / 2 : ℝ))
        ≤ 1 * ((F + ENNReal.ofReal ε * T) ^ (1 / 2 : ℝ) * (ENNReal.ofReal (C6 * ε) * T) ^ (1 / 2 : ℝ)) :=
          mul_le_mul_left hpi1 _
      _ ≤ _ := by rw [one_mul]; exact s07c_fkps_m5_amgm _ _
  -- absorption
  have hsq : C1 * Real.sqrt ε ≤ 1 / 4 := by
    have h1 : (C1 * Real.sqrt ε) ^ 2 = C1 ^ 2 * ε := by rw [mul_pow, Real.sq_sqrt hε]
    have h2 : C1 ^ 2 * ε * 16 ≤ 1 := by nlinarith [sq_nonneg C1]
    nlinarith [mul_nonneg hC1.le (Real.sqrt_nonneg ε)]
  have hXε : (1 + C6) * ε * 40 ≤ 1 := by nlinarith [sq_nonneg C1]
  have hcoefE : ENNReal.ofReal (C1 * Real.sqrt ε) + ENNReal.ofReal ε * ENNReal.ofReal 10 +
      ENNReal.ofReal (C6 * ε) * ENNReal.ofReal 10 ≤ 2⁻¹ := by
    rw [← ENNReal.ofReal_mul hε, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C6 * ε),
      ← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ C1 * Real.sqrt ε) (by positivity : (0 : ℝ) ≤ ε * 10),
      ← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ C1 * Real.sqrt ε + ε * 10)
        (by positivity : (0 : ℝ) ≤ C6 * ε * 10)]
    rw [show (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 2) by
      rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div]]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith
  have hEle : E ≤ ENNReal.ofReal ((4 * π)⁻¹ + 1) * F + 2⁻¹ * E := by
    calc E ≤ ENNReal.ofReal (4 * π)⁻¹ * F + ENNReal.ofReal (C1 * Real.sqrt ε) * E +
          (F + ENNReal.ofReal ε * T + ENNReal.ofReal (C6 * ε) * T) :=
          hP7.trans (add_le_add (add_le_add le_rfl hterm2) hterm3')
      _ ≤ ENNReal.ofReal (4 * π)⁻¹ * F + ENNReal.ofReal (C1 * Real.sqrt ε) * E +
          (F + ENNReal.ofReal ε * (ENNReal.ofReal 10 * E) +
            ENNReal.ofReal (C6 * ε) * (ENNReal.ofReal 10 * E)) :=
          add_le_add le_rfl (add_le_add (add_le_add le_rfl (mul_le_mul_right hTE _))
            (mul_le_mul_right hTE _))
      _ = (ENNReal.ofReal (4 * π)⁻¹ + 1) * F +
          (ENNReal.ofReal (C1 * Real.sqrt ε) + ENNReal.ofReal ε * ENNReal.ofReal 10 +
            ENNReal.ofReal (C6 * ε) * ENNReal.ofReal 10) * E := by
          ring
      _ ≤ _ := by
          refine add_le_add (mul_le_mul_left (le_of_eq ?_) F) (mul_le_mul_left hcoefE E)
          rw [ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ (4 * π)⁻¹) zero_le_one, ENNReal.ofReal_one]
  have hEF : E ≤ ENNReal.ofReal aF * F := by
    refine (s07c_fkps_m5_absorb hEfin hEle).trans (le_of_eq ?_)
    rw [haFdef, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_assoc]
  have hTF : T ≤ ENNReal.ofReal (10 * aF) * F := by
    refine hTE.trans ((mul_le_mul_right hEF _).trans (le_of_eq ?_))
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10)]
  refine ⟨?_, ?_⟩
  · -- (i) the area function
    calc _ ≤ ENNReal.ofReal (4 * π * (16 + 1)) * T := (s07c_fkps_m5_cone_bd 16 (by norm_num) hg).2
      _ ≤ ENNReal.ofReal (4 * π * (16 + 1)) * (ENNReal.ofReal (10 * aF) * F) := mul_le_mul_right hTF _
      _ = ENNReal.ofReal (680 * π * aF) * F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * π * (16 + 1))]
          congr 2; ring
      _ ≤ _ := by
          refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) F
          have : 0 ≤ C7 * K * 10 * aF := by positivity
          linarith
  · -- (ii) the potential at the origin
    calc _ ≤ ENNReal.ofReal (C7 * (K * ε)) * T := hOr g V m (K * ε) hg hV hm hm0 hKε hVb hmb' hmcar'
      _ ≤ ENNReal.ofReal (C7 * (K * ε)) * (ENNReal.ofReal (10 * aF) * F) := mul_le_mul_right hTF _
      _ = ENNReal.ofReal (C7 * K * 10 * aF * ε) * F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C7 * (K * ε))]
          congr 2; ring
      _ ≤ _ := by
          refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) F
          have : 0 ≤ 680 * π * aF * ε := by positivity
          nlinarith

/-! ## Block A (M6G): the global step at the origin -/

/-- M6.A1: a Whitney majorant bounded by `ε₀` on `𝔻` bounds the dilatation by `ε₀` a.e. on `𝔻` (countably many
Whitney balls cover `𝔻`). -/
theorem s07c_fkps_m6_dil_le {F : ℂ → ℂ} {a : ℂ → ℝ} {ε₀ : ℝ} (hle : ∀ z ∈ unitDisc, a z ≤ ε₀)
    (hW : ∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) →
      ‖LiZhongQC.complexDilatation F w‖ ≤ a z) :
    ∀ᵐ w, w ∈ unitDisc → ‖LiZhongQC.complexDilatation F w‖ ≤ ε₀ := by
  set D : Set ℂ := unitDisc ∩ range (fun q : ℚ × ℚ => ((q.1 : ℝ) : ℂ) + ((q.2 : ℝ) : ℂ) * I) with hD
  have hDc : D.Countable := (countable_range _).mono inter_subset_right
  have hall : ∀ᵐ w, ∀ z (hz : z ∈ D), w ∈ ball z ((1 - ‖z‖) / 2) →
      ‖LiZhongQC.complexDilatation F w‖ ≤ a z :=
    (ae_ball_iff hDc).2 fun z hz => hW z hz.1
  filter_upwards [hall] with w hw hwD
  have hw1 : ‖w‖ < 1 := by
    have : w ∈ ball (0 : ℂ) 1 := hwD
    simpa using this
  set d : ℝ := (1 - ‖w‖) / 8 with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  obtain ⟨q₁, hq₁, hq₁'⟩ : ∃ q : ℚ, w.re < q ∧ (q : ℝ) < w.re + d :=
    exists_rat_btwn (by linarith)
  obtain ⟨q₂, hq₂, hq₂'⟩ : ∃ q : ℚ, w.im < q ∧ (q : ℝ) < w.im + d :=
    exists_rat_btwn (by linarith)
  set z : ℂ := ((q₁ : ℝ) : ℂ) + ((q₂ : ℝ) : ℂ) * I with hz
  have hre : (w - z).re = w.re - q₁ := by simp [hz]
  have him : (w - z).im = w.im - q₂ := by simp [hz]
  have hwz : ‖w - z‖ < 2 * d := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
    rw [hre, him, abs_of_neg (by linarith), abs_of_neg (by linarith)]
    linarith
  have hz1 : ‖z‖ < 1 - 6 * d := by
    have : ‖z‖ ≤ ‖w‖ + ‖w - z‖ := by
      calc ‖z‖ = ‖w - (w - z)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖w‖ + ‖w - z‖ := norm_sub_le _ _
    rw [hd] at hwz ⊢
    linarith
  have hzD : z ∈ D := by
    refine ⟨?_, ⟨(q₁, q₂), rfl⟩⟩
    show z ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff]
    linarith
  have hwb : w ∈ ball z ((1 - ‖z‖) / 2) := by
    rw [mem_ball, dist_eq_norm]
    linarith
  exact (hw z hzD hwb).trans (hle z hzD.1)

/-- M6.A2: a `K`-q.c. homeomorphism of `ℂ` with `|μ_F| ≤ k < 1` a.e. on `𝔻` is `(1+k)/(1-k)`-q.c. on `𝔻`
(LZ `s29_m_isKQC_of_maxDilatation_le`). -/
theorem s07c_fkps_m6_kqc {F : ℂ → ℂ} {K k : ℝ} (hF : IsKQC F univ K) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hμ : ∀ᵐ w, w ∈ unitDisc → ‖LiZhongQC.complexDilatation F w‖ ≤ k) :
    IsKQC F unitDisc ((1 + k) / (1 - k)) := by
  have hFD : IsKQC F unitDisc K := ac_t_isKQC_restrict hF isOpen_ball (subset_univ _)
  have hk1' : 0 < 1 - k := by linarith
  have hK' : 1 ≤ (1 + k) / (1 - k) := by
    rw [le_div_iff₀ hk1']
    linarith
  refine s29_m_isKQC_of_maxDilatation_le hFD hK' ?_
  show essSup (fun z => ENNReal.ofReal ((‖dz F z‖ + ‖dzbar F z‖) / (‖dz F z‖ - ‖dzbar F z‖)))
    (volume.restrict unitDisc) ≤ _
  refine essSup_le_of_ae_le _ ?_
  have hμ' : ∀ᵐ z ∂(volume.restrict unitDisc), ‖LiZhongQC.complexDilatation F z‖ ≤ k :=
    (ae_restrict_iff' measurableSet_ball).2 hμ
  filter_upwards [hμ', thm9_6_cor2_jacobian_pos hFD] with z h1 h2
  change ‖dzbar F z / dz F z‖ ≤ k at h1
  change 0 < ‖dz F z‖ ^ 2 - ‖dzbar F z‖ ^ 2 at h2
  have hA : 0 < ‖dz F z‖ := by
    by_contra h
    have h0 : ‖dz F z‖ = 0 := le_antisymm (not_lt.1 h) (norm_nonneg _)
    rw [h0] at h2
    nlinarith [norm_nonneg (dzbar F z)]
  have hB : ‖dzbar F z‖ ≤ k * ‖dz F z‖ := by
    rw [norm_div, div_le_iff₀ hA] at h1
    exact h1
  have hAB : 0 < ‖dz F z‖ - ‖dzbar F z‖ := by nlinarith [norm_nonneg (dzbar F z)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_div_iff₀ hAB hk1']
  nlinarith

/-- M6.A3 helper: the pointwise bound of the Green-potential kernel. -/
theorem s07c_fkps_m6_kern_enorm_le (X Y V : ℂ) (hX : ‖X‖ ≤ 1) :
    ‖(conj (((1 - ‖X‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (X - Y) * (1 - X * conj Y))) * V).re‖ₑ ≤
      ENNReal.ofReal ((1 - ‖X‖ ^ 2) / (2 * π * ‖X - Y‖ * ‖1 - X * conj Y‖)) * ‖V‖₊ := by
  have h1 : 0 ≤ 1 - ‖X‖ ^ 2 := by nlinarith [norm_nonneg X]
  have hc : ‖((1 - ‖X‖ ^ 2 : ℝ) : ℂ) / (2 * π * conj (X - Y) * (1 - X * conj Y))‖ =
      (1 - ‖X‖ ^ 2) / (2 * π * ‖X - Y‖ * ‖1 - X * conj Y‖) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le]
    norm_num
  have hk0 : 0 ≤ (1 - ‖X‖ ^ 2) / (2 * π * ‖X - Y‖ * ‖1 - X * conj Y‖) := by
    rw [← hc]; exact norm_nonneg _
  rw [Real.enorm_eq_ofReal_abs, ← enorm_eq_nnnorm, ← ofReal_norm, ← ENNReal.ofReal_mul hk0]
  refine ENNReal.ofReal_le_ofReal ((Complex.abs_re_le_norm _).trans ?_)
  rw [norm_mul, Complex.norm_conj, hc]

/-- M6.A3 helper: the absolute Green potential dominates the signed one. -/
theorem s07c_fkps_m6_pot_le (V : ℂ → ℂ) (X : ℂ) (hX : ‖X‖ ≤ 1) :
    ENNReal.ofReal |∫ Y in unitDisc, (conj (((1 - ‖X‖ ^ 2 : ℝ) : ℂ) /
        (2 * π * conj (X - Y) * (1 - X * conj Y))) * V Y).re| ≤
      ∫⁻ Y in unitDisc, ENNReal.ofReal ((1 - ‖X‖ ^ 2) / (2 * π * ‖X - Y‖ * ‖1 - X * conj Y‖)) * ‖V Y‖₊ := by
  rw [← Real.enorm_eq_ofReal_abs]
  exact (enorm_integral_le_lintegral_enorm _).trans
    (lintegral_mono fun Y => s07c_fkps_m6_kern_enorm_le X Y (V Y) hX)

/-- M6.A3 helper: the Poisson integral is dominated by the Poisson integral of `|f|`. -/
theorem s07c_fkps_m6_bdry_le (f : ℝ → ℝ) (X : ℂ) (hX : ‖X‖ ≤ 1) :
    ENNReal.ofReal |∫ t in (0 : ℝ)..2 * π, (1 - ‖X‖ ^ 2) / ‖Complex.exp (t * I) - X‖ ^ 2 * f t| ≤
      ∫⁻ t in Icc 0 (2 * π), ENNReal.ofReal ((1 - ‖X‖ ^ 2) / ‖Complex.exp (t * I) - X‖ ^ 2) * ‖f t‖ₑ := by
  have h1 : 0 ≤ 1 - ‖X‖ ^ 2 := by nlinarith [norm_nonneg X]
  rw [← Real.enorm_eq_ofReal_abs, intervalIntegral.integral_of_le (by positivity)]
  refine (enorm_integral_le_lintegral_enorm _).trans ((lintegral_mono fun t => ?_).trans
    (lintegral_mono_set Ioc_subset_Icc_self))
  rw [enorm_mul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (div_nonneg h1 (sq_nonneg _))]

/-- M6.A3 helper: `∫₀^{2π} f² ≤ ∫_{[0,2π]} |f|²` in `ℝ≥0∞`. -/
theorem s07c_fkps_m6_sq_le (f : ℝ → ℝ) :
    ENNReal.ofReal (∫ t in (0 : ℝ)..2 * π, f t ^ 2) ≤ ∫⁻ t in Icc 0 (2 * π), ‖f t‖ₑ ^ 2 := by
  rw [intervalIntegral.integral_of_le (by positivity)]
  refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
  rw [← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans ((lintegral_mono fun t => ?_).trans
    (lintegral_mono_set Ioc_subset_Icc_self))
  rw [enorm_pow]

/-- M6.A3 helper: the truncated Green weight is nonnegative on `𝔻`. -/
theorem s07c_fkps_m6_gflat_nonneg {Y : ℂ} (hY : Y ∈ unitDisc) :
    0 ≤ (2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2)) := by
  have hY1 : ‖Y‖ < 1 := by simpa using (show Y ∈ ball (0 : ℂ) 1 from hY)
  have hm0 : 0 < max ‖Y‖ (1 / 2) := lt_max_of_lt_right (by norm_num)
  have hm1 : max ‖Y‖ (1 / 2) ≤ 1 := max_le hY1.le (by norm_num)
  exact mul_nonneg (by positivity) (Real.log_nonneg (one_le_one_div hm0 hm1))

/-- M6.A3 (M3 + M5 at the origin): for every `v` that is `C²` on `ℂ` and harmonic on `𝔻`, the `L²` distance on
`B(0, 1/4)` between `v ∘ F` and the Poisson integral of its boundary values `f = v ∘ F ∘ e^{i·}` is
`≤ C ε ∫ f²`. (M3 (P5) a.e. on `𝔻`, `|potential| ≤ ∫ K |V|`, then M5 (ii) with `m = 4|μ_F|`, majorant `4a`.) -/
theorem s07c_fkps_m6_test : ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧ ∀ (F : ℂ → ℂ) (a : ℂ → ℝ) (K ε : ℝ),
    IsKQC F univ K → F '' univ = univ → F '' unitDisc = unitDisc → F 0 = 0 →
    Measurable a → (∀ z, 0 ≤ a z) → (∀ z ∈ unitDisc, a z ≤ ε₀) →
    (∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) →
      ‖LiZhongQC.complexDilatation F w‖ ≤ a z) →
    0 ≤ ε → ε ≤ ε₀ →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
        ≤ ENNReal.ofReal (ε * r)) →
    ∀ v : ℂ → ℝ, ContDiff ℝ 2 v → InnerProductSpace.HarmonicOnNhd v unitDisc →
      ∫⁻ X in ball (0 : ℂ) (1 / 4), ENNReal.ofReal ((v (F X) - (2 * π)⁻¹ *
          ∫ t in (0 : ℝ)..2 * π,
            (1 - ‖X‖ ^ 2) / ‖Complex.exp (t * I) - X‖ ^ 2 * v (F (Complex.exp (t * I)))) ^ 2) ≤
        ENNReal.ofReal (C * ε) * ∫⁻ t in Icc 0 (2 * π), ‖v (F (Complex.exp (t * I)))‖ₑ ^ 2 := by
  obtain ⟨ε₅, C₅, hε₅, hC₅, hM5⟩ := s07c_fkps_m5
  refine ⟨min (ε₅ / 16) (1 / 2), 16 * C₅, lt_min (by positivity) (by norm_num), by positivity, ?_⟩
  intro F a K ε hF hsurj hFD hF0 ha ha0 hale hW hε hεε hcarl v hv hvh
  have hμ : ∀ᵐ w, w ∈ unitDisc → ‖LiZhongQC.complexDilatation F w‖ ≤ 1 / 2 :=
    (s07c_fkps_m6_dil_le hale hW).mono fun w hw hwD => (hw hwD).trans (min_le_right _ _)
  obtain ⟨g, V, hg, hV, hg2, -, -, hP3, -, hP5, hI1, hI2, hI3, hP7⟩ :=
    s07c_fkps_m3 F K hF hsurj hFD hF0 hμ v hv hvh
  have hFc : Continuous F := continuousOn_univ.mp hF.2.2.1.1
  have hec : Continuous fun t : ℝ => Complex.exp (t * I) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hfc : Continuous fun t : ℝ => v (F (Complex.exp (t * I))) := hv.continuous.comp (hFc.comp hec)
  have hmeas : Measurable fun z => 4 * ‖LiZhongQC.complexDilatation F z‖ :=
    (((measurable_dzbar F).div (measurable_dz F)).norm).const_mul 4
  have hper : ∀ t : ℝ, v (F (Complex.exp (((t + 2 * π : ℝ) : ℂ) * I))) = v (F (Complex.exp (t * I))) := by
    intro t
    have : (((t + 2 * π : ℝ) : ℂ) * I) = (t : ℂ) * I + 2 * π * I := by push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hε16 : 16 * ε ≤ ε₅ := by
    have := hεε.trans (min_le_left _ _)
    linarith
  -- Whitney majorant `4a` for `m = 4|μ_F|`
  have hW4 : ∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) →
      4 * ‖LiZhongQC.complexDilatation F w‖ ≤ 4 * a z := fun z hz =>
    (hW z hz).mono fun w hw hwb => by linarith [hw hwb]
  -- Carleson for `4a` with norm `16 ε`
  have hcarl4 : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal ((4 * a z) ^ 2 / (1 - ‖z‖ ^ 2)) ≤
        ENNReal.ofReal (16 * ε * r) := by
    intro ζ hζ r hr0 hr2
    have heq : (fun z => ENNReal.ofReal ((4 * a z) ^ 2 / (1 - ‖z‖ ^ 2))) =
        fun z => ENNReal.ofReal 16 * ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)) := by
      funext z
      rw [← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    rw [heq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal 16 * ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
        ≤ ENNReal.ofReal 16 * ENNReal.ofReal (ε * r) := by gcongr; exact hcarl ζ hζ r hr0 hr2
      _ = ENNReal.ofReal (16 * ε * r) := by rw [← ENNReal.ofReal_mul (by norm_num)]; ring_nf
  -- (P5') from (P5)
  have hP5' : ∀ᵐ X, X ∈ unitDisc → ENNReal.ofReal |v (F X)| ≤
      ENNReal.ofReal (2 * π)⁻¹ * (∫⁻ t in Icc 0 (2 * π),
        ENNReal.ofReal ((1 - ‖X‖ ^ 2) / ‖Complex.exp (t * I) - X‖ ^ 2) *
          ‖v (F (Complex.exp (t * I)))‖ₑ) +
      ∫⁻ Y in unitDisc,
        ENNReal.ofReal ((1 - ‖X‖ ^ 2) / (2 * π * ‖X - Y‖ * ‖1 - X * conj Y‖)) * ‖V Y‖₊ := by
    filter_upwards [hP5] with X hX hXD
    obtain ⟨-, heq⟩ := hX hXD
    have hX1 : ‖X‖ ≤ 1 := by
      have : X ∈ ball (0 : ℂ) 1 := hXD
      rw [mem_ball_zero_iff] at this
      exact this.le
    set B := ∫ t in (0 : ℝ)..2 * π,
      (1 - ‖X‖ ^ 2) / ‖Complex.exp (t * I) - X‖ ^ 2 * v (F (Complex.exp (t * I)))
    set W := ∫ Y in unitDisc, (conj (((1 - ‖X‖ ^ 2 : ℝ) : ℂ) /
      (2 * π * conj (X - Y) * (1 - X * conj Y))) * V Y).re
    have habs : |v (F X)| ≤ (2 * π)⁻¹ * |B| + |W| := by
      rw [heq]
      calc |(2 * π)⁻¹ * B - W| ≤ |(2 * π)⁻¹ * B| + |W| := abs_sub _ _
        _ = (2 * π)⁻¹ * |B| + |W| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * π)⁻¹)]
    calc ENNReal.ofReal |v (F X)| ≤ ENNReal.ofReal ((2 * π)⁻¹ * |B| + |W|) :=
          ENNReal.ofReal_le_ofReal habs
      _ ≤ ENNReal.ofReal ((2 * π)⁻¹ * |B|) + ENNReal.ofReal |W| := ENNReal.ofReal_add_le
      _ ≤ _ := by
          rw [ENNReal.ofReal_mul (by positivity)]
          gcongr
          · exact s07c_fkps_m6_bdry_le (fun t => v (F (Complex.exp (t * I)))) X hX1
          · exact s07c_fkps_m6_pot_le V X hX1
  -- (P7') from (P7)
  have hP7' : (∫⁻ Y in unitDisc,
        ENNReal.ofReal (‖g Y‖ ^ 2 * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2))))) ≤
      ENNReal.ofReal (4 * π)⁻¹ * (∫⁻ t in Icc 0 (2 * π), ‖v (F (Complex.exp (t * I)))‖ₑ ^ 2) +
        (∫⁻ Y in unitDisc,
          ENNReal.ofReal (‖V Y‖ * ‖g Y‖ * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2))))) +
        (∫⁻ Y in unitDisc \ ball 0 (1 / 2), ENNReal.ofReal (|v (F Y)| * ‖V Y‖ / (2 * π * ‖Y‖))) := by
    set T1 := ∫ t in (0 : ℝ)..2 * π, v (F (Complex.exp (t * I))) ^ 2
    set T2 := ∫ t in (0 : ℝ)..2 * π, v (F (Complex.exp (t * I) / 2)) ^ 2
    set I2 := ∫ Y in unitDisc, (conj (V Y) * g Y).re * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2)))
    set I3 := ∫ Y in unitDisc \ ball 0 (1 / 2),
      v (F Y) * (conj (V Y) * (-Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))).re
    have hT2 : 0 ≤ T2 := intervalIntegral.integral_nonneg (by positivity) fun t _ => sq_nonneg _
    have h4 : (4 * π)⁻¹ = 1 / 2 * (2 * π)⁻¹ := by
      rw [mul_inv, mul_inv]; ring
    have hle : ∫ Y in unitDisc, ‖g Y‖ ^ 2 * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2))) ≤
        (4 * π)⁻¹ * T1 + |I2| + |I3| := by
      rw [hP7, h4]
      have h2π : 0 ≤ (2 * π)⁻¹ * T2 := mul_nonneg (by positivity) hT2
      nlinarith [neg_abs_le I2, neg_abs_le I3]
    rw [← ofReal_integral_eq_lintegral_ofReal hI1
      ((ae_restrict_iff' measurableSet_ball).2 (ae_of_all _ fun Y hY =>
        mul_nonneg (sq_nonneg _) (s07c_fkps_m6_gflat_nonneg hY)))]
    calc ENNReal.ofReal (∫ Y in unitDisc, ‖g Y‖ ^ 2 * ((2 * π)⁻¹ * Real.log (1 / max ‖Y‖ (1 / 2))))
        ≤ ENNReal.ofReal ((4 * π)⁻¹ * T1 + |I2| + |I3|) := ENNReal.ofReal_le_ofReal hle
      _ ≤ ENNReal.ofReal ((4 * π)⁻¹ * T1) + ENNReal.ofReal |I2| + ENNReal.ofReal |I3| :=
          ENNReal.ofReal_add_le.trans (by gcongr; exact ENNReal.ofReal_add_le)
      _ ≤ _ := by
          rw [ENNReal.ofReal_mul (by positivity)]
          gcongr
          · exact s07c_fkps_m6_sq_le (fun t => v (F (Complex.exp (t * I))))
          · rw [← Real.enorm_eq_ofReal_abs]
            refine (enorm_integral_le_lintegral_enorm _).trans
              (setLIntegral_mono' measurableSet_ball fun Y hY => ?_)
            rw [Real.enorm_eq_ofReal_abs]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [abs_mul, abs_of_nonneg (s07c_fkps_m6_gflat_nonneg hY)]
            refine mul_le_mul_of_nonneg_right ?_ (s07c_fkps_m6_gflat_nonneg hY)
            refine (Complex.abs_re_le_norm _).trans ?_
            rw [norm_mul, Complex.norm_conj]
          · rw [← Real.enorm_eq_ofReal_abs]
            refine (enorm_integral_le_lintegral_enorm _).trans
              (setLIntegral_mono' (measurableSet_ball.diff measurableSet_ball) fun Y hY => ?_)
            rw [Real.enorm_eq_ofReal_abs]
            refine ENNReal.ofReal_le_ofReal ?_
            have hY0 : 0 < ‖Y‖ := by
              have h := hY.2
              rw [mem_ball_zero_iff, not_lt] at h
              linarith
            have hn : ‖conj (V Y) * (-Y / ((2 * π * ‖Y‖ ^ 2 : ℝ) : ℂ))‖ = ‖V Y‖ / (2 * π * ‖Y‖) := by
              rw [norm_mul, Complex.norm_conj, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (by positivity)]
              field_simp
            rw [abs_mul, mul_div_assoc]
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact (Complex.abs_re_le_norm _).trans hn.le
  have hM := (hM5 g V (fun z => 4 * ‖LiZhongQC.complexDilatation F z‖) (fun z => 4 * a z)
    (fun X => v (F X)) (fun t => v (F (Complex.exp (t * I)))) (16 * ε) hg hV hmeas.aemeasurable
    (ha.const_mul 4) (hv.continuous.comp hFc).measurable hfc.measurable hper
    (fun z => by positivity) (fun z => by linarith [ha0 z]) (by linarith) hε16 hW4 hcarl4 hP3
    (by simpa only [enorm_eq_nnnorm] using hg2) hP5' hP7').2
  -- the target from (P5) and M5 (ii)
  have hpt : ∀ᵐ X ∂(volume.restrict (ball (0 : ℂ) (1 / 4))),
      ENNReal.ofReal ((v (F X) - (2 * π)⁻¹ *
          ∫ t in (0 : ℝ)..2 * π,
            (1 - ‖X‖ ^ 2) / ‖Complex.exp (t * I) - X‖ ^ 2 * v (F (Complex.exp (t * I)))) ^ 2) ≤
        (∫⁻ Y in unitDisc,
          ENNReal.ofReal ((1 - ‖X‖ ^ 2) / (2 * π * ‖X - Y‖ * ‖1 - X * conj Y‖)) * ‖V Y‖₊) ^ 2 := by
    refine (ae_restrict_iff' measurableSet_ball).2 ?_
    filter_upwards [hP5] with X hX hXB
    have hX4 : ‖X‖ < 1 / 4 := mem_ball_zero_iff.1 hXB
    have hXD : X ∈ unitDisc := by
      show X ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff]
      linarith
    obtain ⟨-, heq⟩ := hX hXD
    rw [heq, sub_sub_cancel_left, neg_sq, ← sq_abs, ENNReal.ofReal_pow (abs_nonneg _)]
    gcongr
    exact s07c_fkps_m6_pot_le V X (by linarith)
  calc ∫⁻ X in ball (0 : ℂ) (1 / 4), ENNReal.ofReal ((v (F X) - (2 * π)⁻¹ *
          ∫ t in (0 : ℝ)..2 * π,
            (1 - ‖X‖ ^ 2) / ‖Complex.exp (t * I) - X‖ ^ 2 * v (F (Complex.exp (t * I)))) ^ 2)
      ≤ ∫⁻ X in ball (0 : ℂ) (1 / 4), (∫⁻ Y in unitDisc,
          ENNReal.ofReal ((1 - ‖X‖ ^ 2) / (2 * π * ‖X - Y‖ * ‖1 - X * conj Y‖)) * ‖V Y‖₊) ^ 2 :=
        lintegral_mono_ae hpt
    _ ≤ ENNReal.ofReal (C₅ * (16 * ε)) *
          ∫⁻ t in Icc 0 (2 * π), ‖v (F (Complex.exp (t * I)))‖ₑ ^ 2 := hM
    _ = ENNReal.ofReal (16 * C₅ * ε) *
          ∫⁻ t in Icc 0 (2 * π), ‖v (F (Complex.exp (t * I)))‖ₑ ^ 2 := by
          rw [show C₅ * (16 * ε) = 16 * C₅ * ε by ring]

/-- M6.A4 helper (area mean value): a function harmonic on `𝔻` has `∫_{B(0,R)} u = π R² u(0)` for `0 ≤ R < 1`. -/
theorem s07c_fkps_m6_area_mean {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u unitDisc) {R : ℝ}
    (hR0 : 0 ≤ R) (hR1 : R < 1) :
    ∫ z in ball (0 : ℂ) R, u z = π * R ^ 2 * u 0 := by
  have hsub : closedBall (0 : ℂ) R ⊆ unitDisc := closedBall_subset_ball hR1
  have hcont : ContinuousOn u (closedBall (0 : ℂ) R) := (hu.mono hsub).continuousOn
  have hps : Continuous fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hint : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * ((u (Complex.polarCoord.symm p + 0) : ℝ) : ℂ))
      (Set.Ioo 0 R ×ˢ Set.Ioo (-π) π) := by
    refine IntegrableOn.mono_set ?_ (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
    refine ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) ?_
    refine (Complex.continuous_ofReal.comp continuous_fst).continuousOn.mul ?_
    refine Complex.continuous_ofReal.comp_continuousOn (hcont.comp
      ((hps.add continuous_const).continuousOn) ?_)
    intro p hp
    rw [mem_closedBall_zero_iff]
    show ‖Complex.polarCoord.symm p + 0‖ ≤ R
    rw [add_zero, Complex.norm_polarCoord_symm, abs_of_nonneg hp.1.1]
    exact hp.1.2
  have hpol := LiZhongQC.setIntegral_ball_eq_polar' (g := fun z => ((u z : ℝ) : ℂ)) 0 hR0 hint
  have hcirc : ∀ r ∈ uIcc 0 R, (∫ θ in (0 : ℝ)..(2 * π), (r : ℂ) * ((u (circleMap 0 r θ) : ℝ) : ℂ)) =
      (r : ℂ) * ((2 * π * u 0 : ℝ) : ℂ) := by
    intro r hr
    rw [uIcc_of_le hR0] at hr
    have hh : InnerProductSpace.HarmonicOnNhd u (closedBall 0 |r|) := by
      refine hu.mono (closedBall_subset_ball ?_)
      rw [abs_of_nonneg hr.1]
      exact lt_of_le_of_lt hr.2 hR1
    have hm := hh.circleAverage_eq
    rw [Real.circleAverage_def, smul_eq_mul] at hm
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
    congr 2
    rw [← hm]
    field_simp
  rw [intervalIntegral.integral_congr hcirc, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, integral_id, integral_complex_ofReal] at hpol
  have h2 : ((∫ z in ball (0 : ℂ) R, u z : ℝ) : ℂ) = ((π * R ^ 2 * u 0 : ℝ) : ℂ) := by
    rw [hpol]; push_cast; ring
  exact_mod_cast h2

/-- M6.A4 helper: the area of a disc. -/
theorem s07c_fkps_m6_vol_ball {r : ℝ} (hr : 0 ≤ r) :
    volume (ball (0 : ℂ) r) = ENNReal.ofReal (π * r ^ 2) := by
  rw [Complex.volume_ball, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_mul (by positivity), mul_comm]

/-- M6.A4 helper (`L¹ ≤ L²` by AM–GM): `|∫_S w| ≤ L/(2s) + s V/2` when `∫_S w² ≤ L` and `|S| = V`. -/
theorem s07c_fkps_m6_amgm {w : ℂ → ℝ} {S : Set ℂ} {s L V : ℝ} (hs : 0 < s) (hL0 : 0 ≤ L) (hV0 : 0 ≤ V)
    (hS : volume S = ENNReal.ofReal V) (hL : ∫⁻ X in S, ENNReal.ofReal (w X ^ 2) ≤ ENNReal.ofReal L) :
    |∫ X in S, w X| ≤ (2 * s)⁻¹ * L + s / 2 * V := by
  have hpt : ∀ X, ‖w X‖ₑ ≤ ENNReal.ofReal (2 * s)⁻¹ * ENNReal.ofReal (w X ^ 2) + ENNReal.ofReal (s / 2) := by
    intro X
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have key : 2 * s * |w X| ≤ w X ^ 2 + s ^ 2 := by
      nlinarith [sq_nonneg (|w X| - s), sq_abs (w X)]
    have h2s : 0 < 2 * s := by positivity
    calc |w X| ≤ (w X ^ 2 + s ^ 2) / (2 * s) := by
          rw [le_div_iff₀ h2s]; linarith
      _ = (2 * s)⁻¹ * w X ^ 2 + s / 2 := by field_simp
  have hE : ENNReal.ofReal |∫ X in S, w X| ≤ ENNReal.ofReal ((2 * s)⁻¹ * L + s / 2 * V) := by
    rw [← Real.enorm_eq_ofReal_abs]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc ∫⁻ X in S, ‖w X‖ₑ
        ≤ ∫⁻ X in S, (ENNReal.ofReal (2 * s)⁻¹ * ENNReal.ofReal (w X ^ 2) + ENNReal.ofReal (s / 2)) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (2 * s)⁻¹ * (∫⁻ X in S, ENNReal.ofReal (w X ^ 2)) +
            ENNReal.ofReal (s / 2) * volume S := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            setLIntegral_const]
      _ ≤ ENNReal.ofReal (2 * s)⁻¹ * ENNReal.ofReal L + ENNReal.ofReal (s / 2) * ENNReal.ofReal V := by
          rw [hS]; gcongr
      _ = ENNReal.ofReal ((2 * s)⁻¹ * L + s / 2 * V) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hE

/-- M6.A4 helper (Mori at the origin): a `K`-q.c. self-map of `𝔻` fixing `0` with `K ≤ 5/4` has
`|F X| ≤ 16 |X|^{4/5}`. -/
theorem s07c_fkps_m6_mori {F : ℂ → ℂ} {K : ℝ} (hF : IsKQC F unitDisc K) (himg : F '' unitDisc = unitDisc)
    (hF0 : F 0 = 0) (hK : K ≤ 5 / 4) {X : ℂ} (hX : X ∈ unitDisc) :
    ‖F X‖ ≤ 16 * ‖X‖ ^ (4 / 5 : ℝ) := by
  have hK1 : 1 ≤ K := hF.2.1
  have hX1 : ‖X‖ < 1 := mem_ball_zero_iff.1 hX
  by_cases hX0 : X = 0
  · rw [hX0, hF0, norm_zero]
    positivity
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hm := thm15_2_mori hF himg hF0 hX h0 hX0
  rw [hF0, sub_zero, sub_zero] at hm
  have hexp : (4 / 5 : ℝ) ≤ 1 / K := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have := Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg X) hX1.le (by norm_num) hexp
  linarith

/-- M6.A4 helper (one real test function): if `|v ∘ F| ≤ 16 q⁴` on `B(0, q⁵)` and the `L²(B(0,1/4))` distance
of `v ∘ F` to the Poisson integral `P` of `f = v ∘ F ∘ e^{i·}` is `≤ A q^{20}`, then
`|∫_{B(0,1/4)} v ∘ F| ≤ (π/16)(17 + A) q⁴ + (A + 1) q^{10}` (mean value of `P` on `B(0, q⁵)` and `B(0, 1/4)`). -/
theorem s07c_fkps_m6_mom_one {F : ℂ → ℂ} {v : ℂ → ℝ} {q A : ℝ} (hFc : Continuous F) (hv : Continuous v)
    (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) (hA : 0 ≤ A)
    (hbd : ∀ X : ℂ, ‖X‖ < q ^ 5 → |v (F X)| ≤ 16 * q ^ 4)
    (hL2 : ∫⁻ X in ball (0 : ℂ) (1 / 4), ENNReal.ofReal ((v (F X) - (2 * π)⁻¹ *
          ∫ t in (0 : ℝ)..2 * π,
            (1 - ‖X‖ ^ 2) / ‖Complex.exp (t * I) - X‖ ^ 2 * v (F (Complex.exp (t * I)))) ^ 2) ≤
        ENNReal.ofReal (A * q ^ 20)) :
    |∫ X in ball (0 : ℂ) (1 / 4), v (F X)| ≤ π / 16 * (17 + A) * q ^ 4 + (A + 1) * q ^ 10 := by
  set f : ℝ → ℝ := fun t => v (F (Complex.exp (t * I))) with hf_def
  have hec : Continuous fun t : ℝ => Complex.exp (t * I) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hfc : Continuous f := hv.comp (hFc.comp hec)
  have hper : ∀ t, f (t + 2 * π) = f t := by
    intro t
    show v (F (Complex.exp (((t + 2 * π : ℝ) : ℂ) * I))) = v (F (Complex.exp (t * I)))
    have : (((t + 2 * π : ℝ) : ℂ) * I) = (t : ℂ) * I + 2 * π * I := by push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  set P : ℂ → ℝ := fun X => (2 * π)⁻¹ *
    ∫ t in (0 : ℝ)..2 * π, (1 - ‖X‖ ^ 2) / ‖Complex.exp (t * I) - X‖ ^ 2 * f t with hP_def
  have hPh : InnerProductSpace.HarmonicOnNhd P unitDisc := s07c_fkps_m2_poisson_harmonic f hfc hper
  have hP0 : P 0 = (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, f t := by
    show (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖(0 : ℂ)‖ ^ 2) / ‖Complex.exp (t * I) - 0‖ ^ 2 * f t = _
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [norm_zero, sub_zero, Complex.norm_exp_ofReal_mul_I]
    norm_num
  set m := P 0
  have hvF : Continuous fun X => v (F X) := hv.comp hFc
  -- integrability and the decomposition `∫ v∘F = π ρ² m + ∫ w` on `B(0, ρ)`, `ρ < 1`
  have hdec : ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 →
      ∫ X in ball (0 : ℂ) ρ, v (F X) = π * ρ ^ 2 * m + ∫ X in ball (0 : ℂ) ρ, (v (F X) - P X) := by
    intro ρ hρ0 hρ1
    have hi1 : IntegrableOn (fun X => v (F X)) (ball (0 : ℂ) ρ) :=
      (hvF.continuousOn.integrableOn_compact (isCompact_closedBall 0 ρ)).mono_set ball_subset_closedBall
    have hi2 : IntegrableOn P (ball (0 : ℂ) ρ) :=
      (((hPh.mono (closedBall_subset_ball hρ1)).continuousOn).integrableOn_compact
        (isCompact_closedBall 0 ρ)).mono_set ball_subset_closedBall
    rw [integral_sub hi1 hi2, s07c_fkps_m6_area_mean hPh hρ0 hρ1]
    ring
  -- the `L²` bound restricted to smaller balls
  have hL2' : ∀ ρ : ℝ, ρ ≤ 1 / 4 →
      ∫⁻ X in ball (0 : ℂ) ρ, ENNReal.ofReal ((v (F X) - P X) ^ 2) ≤ ENNReal.ofReal (A * q ^ 20) :=
    fun ρ hρ => (lintegral_mono_set (ball_subset_ball hρ)).trans hL2
  have hq5 : 0 < q ^ 5 := by positivity
  have hq51 : q ^ 5 ≤ 1 / 4 := by
    have : q ^ 5 ≤ (1 / 2) ^ 5 := pow_le_pow_left₀ hq0.le hq1 5
    linarith [show ((1 : ℝ) / 2) ^ 5 = 1 / 32 by norm_num]
  -- (a) the boundary moment `m`
  have hwa := s07c_fkps_m6_amgm (w := fun X => v (F X) - P X) hq5 (by positivity) (by positivity)
    (s07c_fkps_m6_vol_ball hq5.le) (hL2' _ hq51)
  have hda := hdec (q ^ 5) hq5.le (by linarith)
  have hba : |∫ X in ball (0 : ℂ) (q ^ 5), v (F X)| ≤ 16 * q ^ 4 * (π * (q ^ 5) ^ 2) := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := ball (0 : ℂ) (q ^ 5))
      (f := fun X => v (F X)) (C := 16 * q ^ 4) (measure_ball_lt_top) (fun X hX => by
        rw [Real.norm_eq_abs]; exact hbd X (mem_ball_zero_iff.1 hX))
    rw [Real.norm_eq_abs, measureReal_def, s07c_fkps_m6_vol_ball hq5.le,
      ENNReal.toReal_ofReal (by positivity)] at h
    exact h
  have hm : π * q ^ 10 * |m| ≤ 16 * q ^ 4 * (π * q ^ 10) + (A / 2 + π / 2) * q ^ 15 := by
    have e1 : π * (q ^ 5) ^ 2 * m = (∫ X in ball (0 : ℂ) (q ^ 5), v (F X)) -
        ∫ X in ball (0 : ℂ) (q ^ 5), (v (F X) - P X) := by rw [hda]; ring
    have e2 : (2 * q ^ 5)⁻¹ * (A * q ^ 20) + q ^ 5 / 2 * (π * (q ^ 5) ^ 2) = (A / 2 + π / 2) * q ^ 15 := by
      field_simp
    have e3 : |π * (q ^ 5) ^ 2 * m| = π * q ^ 10 * |m| := by
      rw [abs_mul, abs_of_nonneg (by positivity)]; ring
    rw [← e3, e1]
    refine (abs_sub _ _).trans ?_
    have h16 : 16 * q ^ 4 * (π * (q ^ 5) ^ 2) = 16 * q ^ 4 * (π * q ^ 10) := by ring
    linarith [hwa, hba]
  have hm' : |m| ≤ (17 + A) * q ^ 4 := by
    have hpq : 0 < π * q ^ 10 := by positivity
    have hq1' : q ≤ 1 := by linarith
    have hq54 : q ^ 5 ≤ q ^ 4 := pow_le_pow_of_le_one hq0.le hq1' (by norm_num)
    have h1 : |m| ≤ 16 * q ^ 4 + (A / 2 + π / 2) / π * q ^ 5 := by
      rw [← mul_le_mul_iff_of_pos_left hpq]
      calc π * q ^ 10 * |m| ≤ 16 * q ^ 4 * (π * q ^ 10) + (A / 2 + π / 2) * q ^ 15 := hm
        _ = π * q ^ 10 * (16 * q ^ 4 + (A / 2 + π / 2) / π * q ^ 5) := by
          field_simp
    have h2 : (A / 2 + π / 2) / π ≤ A + 1 := by
      rw [div_le_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    have h3 : (A / 2 + π / 2) / π * q ^ 5 ≤ (A + 1) * q ^ 4 :=
      mul_le_mul h2 hq54 (by positivity) (by positivity)
    linarith
  -- (b) the `B(0, 1/4)` average
  have hq10 : 0 < q ^ 10 := by positivity
  have hwb := s07c_fkps_m6_amgm (w := fun X => v (F X) - P X) hq10 (by positivity) (by positivity)
    (s07c_fkps_m6_vol_ball (by norm_num : (0 : ℝ) ≤ 1 / 4)) (hL2' _ le_rfl)
  have hdb := hdec (1 / 4) (by norm_num) (by norm_num)
  have e4 : (2 * q ^ 10)⁻¹ * (A * q ^ 20) + q ^ 10 / 2 * (π * (1 / 4) ^ 2) = (A / 2 + π / 32) * q ^ 10 := by
    field_simp; ring
  rw [e4] at hwb
  rw [hdb]
  refine (abs_add_le _ _).trans ?_
  have hπm : |π * (1 / 4) ^ 2 * m| ≤ π / 16 * (17 + A) * q ^ 4 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have : π * (1 / 4) ^ 2 = π / 16 := by ring
    rw [this, mul_assoc]
    exact mul_le_mul_of_nonneg_left hm' (by positivity)
  have hπ32 : (A / 2 + π / 32) * q ^ 10 ≤ (A + 1) * q ^ 10 := by
    refine mul_le_mul_of_nonneg_right ?_ hq10.le
    linarith [Real.pi_lt_four]
  linarith

/-- M6.A4 (moments; the only use of `F 0 = 0`): `|⨍_{B(0,1/4)} Fⁿ| ≤ C ε^{1/5}` for `n ≥ 1`. Route: A3 for
`v = Re zⁿ, Re (-i zⁿ)`, the mean-value property of `P[f]` on `B(0, r)` and on `B(0, 1/4)`, and Mori
(LZ `thm15_2_mori` with `K' = (1+ε₀)/(1-ε₀) ≤ 5/4`): `|⨍_θ F(e^{iθ})ⁿ| ≤ 16 r^{4/5} + C √ε / r`. -/
theorem s07c_fkps_m6_moment : ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧ ∀ (F : ℂ → ℂ) (a : ℂ → ℝ) (K ε : ℝ),
    IsKQC F univ K → F '' univ = univ → F '' unitDisc = unitDisc → F 0 = 0 →
    Measurable a → (∀ z, 0 ≤ a z) → (∀ z ∈ unitDisc, a z ≤ ε₀) →
    (∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) →
      ‖LiZhongQC.complexDilatation F w‖ ≤ a z) →
    0 ≤ ε → ε ≤ ε₀ →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
        ≤ ENNReal.ofReal (ε * r)) →
    ∀ n : ℕ, 1 ≤ n →
      ‖(16 / π : ℂ) * ∫ X in ball (0 : ℂ) (1 / 4), F X ^ n‖ ≤ C * ε ^ (1 / 5 : ℝ) := by
  obtain ⟨ε₃, C₃, hε₃, hC₃, hA3⟩ := s07c_fkps_m6_test
  set A : ℝ := 2 * π * C₃ with hA_def
  have hA0 : 0 ≤ A := by positivity
  refine ⟨min ε₃ ((1 / 2) ^ 20), 13 * A + 45, lt_min hε₃ (by norm_num), by positivity, ?_⟩
  intro F a K ε hF hsurj hFD hF0 ha ha0 hale hW hε hεε hcarl n hn
  set ε₀ := min ε₃ ((1 / 2) ^ 20) with hε₀_def
  have hε₀3 : ε₀ ≤ ε₃ := min_le_left _ _
  have hε₀s : ε₀ ≤ (1 / 2) ^ 20 := min_le_right _ _
  have hε₀9 : ε₀ ≤ 1 / 9 := hε₀s.trans (by norm_num)
  have hε₀0 : 0 ≤ ε₀ := hε.trans hεε
  have hFc : Continuous F := continuousOn_univ.mp hF.2.2.1.1
  -- `F` is `K'`-q.c. on `𝔻`, `K' ≤ 5/4`
  have hKD := s07c_fkps_m6_kqc hF hε₀0 (by linarith) (s07c_fkps_m6_dil_le hale hW)
  have hK54 : (1 + ε₀) / (1 - ε₀) ≤ 5 / 4 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  -- `F` maps the closed disc into the closed disc
  have hcl : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖F z‖ ≤ 1 := by
    intro z hz
    have hzc : z ∈ closure unitDisc := by
      show z ∈ closure (ball (0 : ℂ) 1)
      rw [closure_ball 0 one_ne_zero, mem_closedBall_zero_iff]; exact hz
    have h1 := image_closure_subset_closure_image hFc ⟨z, hzc, rfl⟩
    rw [hFD] at h1
    have h2 : F z ∈ closedBall (0 : ℂ) 1 := by
      have : closure unitDisc = closedBall (0 : ℂ) 1 := closure_ball 0 one_ne_zero
      rw [← this]; exact h1
    exact mem_closedBall_zero_iff.1 h2
  have hpow : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖F z ^ n‖ ≤ ‖F z‖ := fun z hz => by
    rw [norm_pow]; exact pow_le_of_le_one (norm_nonneg _) (hcl z hz) (by omega)
  -- the two real test functions
  set v₁ : ℂ → ℝ := fun z => (z ^ n).re with hv₁
  set v₂ : ℂ → ℝ := fun z => (z ^ n).im with hv₂
  have hv₁c : ContDiff ℝ 2 v₁ := by
    have : ContDiff ℝ 2 (fun z : ℂ => Complex.reCLM (z ^ n)) :=
      Complex.reCLM.contDiff.comp (contDiff_id.pow n)
    simpa using this
  have hv₂c : ContDiff ℝ 2 v₂ := by
    have : ContDiff ℝ 2 (fun z : ℂ => Complex.imCLM (z ^ n)) :=
      Complex.imCLM.contDiff.comp (contDiff_id.pow n)
    simpa using this
  have hv₁h : InnerProductSpace.HarmonicOnNhd v₁ unitDisc := fun z _ =>
    (analyticAt_id.pow n).harmonicAt_re
  have hv₂h : InnerProductSpace.HarmonicOnNhd v₂ unitDisc := by
    have heq : v₂ = fun z : ℂ => (-I * z ^ n).re := by
      funext z; simp [hv₂]
    rw [heq]
    exact fun z _ => ((analyticAt_const.mul (analyticAt_id.pow n))).harmonicAt_re
  -- the core estimate at scale `q`
  have hcore : ∀ q : ℝ, 0 < q → q ≤ 1 / 2 → ε ≤ q ^ 20 → q ^ 20 ≤ ε₃ →
      ‖(16 / π : ℂ) * ∫ X in ball (0 : ℂ) (1 / 4), F X ^ n‖ ≤ (13 * A + 45) * q ^ 4 := by
    intro q hq0 hq1 hεq hq3
    have hcarl' : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
        ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)) ≤
          ENNReal.ofReal (q ^ 20 * r) := fun ζ hζ r hr0 hr2 =>
      (hcarl ζ hζ r hr0 hr2).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hεq hr0.le))
    have hale' : ∀ z ∈ unitDisc, a z ≤ ε₃ := fun z hz => (hale z hz).trans hε₀3
    have hL2 : ∀ v : ℂ → ℝ, ContDiff ℝ 2 v → InnerProductSpace.HarmonicOnNhd v unitDisc →
        (∀ z : ℂ, ‖z‖ ≤ 1 → |v (F z)| ≤ 1) →
        ∫⁻ X in ball (0 : ℂ) (1 / 4), ENNReal.ofReal ((v (F X) - (2 * π)⁻¹ *
            ∫ t in (0 : ℝ)..2 * π,
              (1 - ‖X‖ ^ 2) / ‖Complex.exp (t * I) - X‖ ^ 2 * v (F (Complex.exp (t * I)))) ^ 2) ≤
          ENNReal.ofReal (A * q ^ 20) := by
      intro v hvc hvh hv1
      refine (hA3 F a K (q ^ 20) hF hsurj hFD hF0 ha ha0 hale' hW (by positivity) hq3 hcarl' v hvc hvh).trans ?_
      have hb : ∫⁻ t in Icc 0 (2 * π), ‖v (F (Complex.exp (t * I)))‖ₑ ^ 2 ≤ ENNReal.ofReal (2 * π) := by
        calc ∫⁻ t in Icc 0 (2 * π), ‖v (F (Complex.exp (t * I)))‖ₑ ^ 2 ≤ ∫⁻ t in Icc 0 (2 * π), 1 := by
              refine lintegral_mono fun t => ?_
              have h1 : ‖v (F (Complex.exp (t * I)))‖ₑ ≤ 1 := by
                rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_one]
                refine ENNReal.ofReal_le_ofReal (hv1 _ ?_)
                rw [Complex.norm_exp_ofReal_mul_I]
              calc ‖v (F (Complex.exp (t * I)))‖ₑ ^ 2 ≤ 1 ^ 2 := by gcongr
                _ = 1 := one_pow 2
          _ = ENNReal.ofReal (2 * π) := by
              rw [setLIntegral_const, one_mul, Real.volume_Icc, sub_zero]
      calc ENNReal.ofReal (C₃ * q ^ 20) * ∫⁻ t in Icc 0 (2 * π), ‖v (F (Complex.exp (t * I)))‖ₑ ^ 2
          ≤ ENNReal.ofReal (C₃ * q ^ 20) * ENNReal.ofReal (2 * π) := by gcongr
        _ = ENNReal.ofReal (A * q ^ 20) := by
            rw [← ENNReal.ofReal_mul (by positivity), hA_def]; ring_nf
    have hbd : ∀ v : ℂ → ℝ, (∀ w : ℂ, |v w| ≤ ‖w ^ n‖) →
        ∀ X : ℂ, ‖X‖ < q ^ 5 → |v (F X)| ≤ 16 * q ^ 4 := by
      intro v hvw X hX
      have hq5 : q ^ 5 ≤ 1 := by
        have : q ^ 5 ≤ (1 / 2) ^ 5 := pow_le_pow_left₀ hq0.le hq1 5
        linarith [show ((1 : ℝ) / 2) ^ 5 = 1 / 32 by norm_num]
      have hXD : X ∈ unitDisc := mem_ball_zero_iff.2 (by linarith)
      have hmo := s07c_fkps_m6_mori hKD hFD hF0 hK54 hXD
      have hr : ‖X‖ ^ (4 / 5 : ℝ) ≤ (q ^ 5) ^ (4 / 5 : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _) hX.le (by norm_num)
      have hq4 : (q ^ 5) ^ (4 / 5 : ℝ) = q ^ 4 := by
        rw [← Real.rpow_natCast q 5, ← Real.rpow_mul hq0.le,
          show ((5 : ℕ) : ℝ) * (4 / 5) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc |v (F X)| ≤ ‖F X ^ n‖ := hvw _
        _ ≤ ‖F X‖ := hpow X (mem_ball_zero_iff.1 hXD).le
        _ ≤ 16 * ‖X‖ ^ (4 / 5 : ℝ) := hmo
        _ ≤ 16 * q ^ 4 := by rw [← hq4]; linarith
    have hv₁w : ∀ w : ℂ, |v₁ w| ≤ ‖w ^ n‖ := fun w => Complex.abs_re_le_norm _
    have hv₂w : ∀ w : ℂ, |v₂ w| ≤ ‖w ^ n‖ := fun w => Complex.abs_im_le_norm _
    have hv1 : ∀ v : ℂ → ℝ, (∀ w : ℂ, |v w| ≤ ‖w ^ n‖) → ∀ z : ℂ, ‖z‖ ≤ 1 → |v (F z)| ≤ 1 :=
      fun v hvw z hz => (hvw _).trans ((hpow z hz).trans (hcl z hz))
    have h1 := s07c_fkps_m6_mom_one hFc hv₁c.continuous hq0 hq1 hA0 (hbd v₁ hv₁w)
      (hL2 v₁ hv₁c hv₁h (hv1 v₁ hv₁w))
    have h2 := s07c_fkps_m6_mom_one hFc hv₂c.continuous hq0 hq1 hA0 (hbd v₂ hv₂w)
      (hL2 v₂ hv₂c hv₂h (hv1 v₂ hv₂w))
    -- recombine real and imaginary parts
    have hint : IntegrableOn (fun X => F X ^ n) (ball (0 : ℂ) (1 / 4)) :=
      ((hFc.pow n).continuousOn.integrableOn_compact (isCompact_closedBall 0 _)).mono_set
        ball_subset_closedBall
    set J := ∫ X in ball (0 : ℂ) (1 / 4), F X ^ n
    have hJre : J.re = ∫ X in ball (0 : ℂ) (1 / 4), v₁ (F X) := (integral_re hint).symm
    have hJim : J.im = ∫ X in ball (0 : ℂ) (1 / 4), v₂ (F X) := (integral_im hint).symm
    have hq1' : q ≤ 1 := by linarith
    have hq104 : q ^ 10 ≤ q ^ 4 := pow_le_pow_of_le_one hq0.le hq1' (by norm_num)
    have hJ : ‖J‖ ≤ 2 * (π / 16 * (17 + A) * q ^ 4 + (A + 1) * q ^ 10) := by
      refine (Complex.norm_le_abs_re_add_abs_im J).trans ?_
      rw [hJre, hJim]
      linarith
    have hn16 : ‖(16 / π : ℂ)‖ = 16 / π := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le]
      norm_num
    rw [norm_mul, hn16]
    have hπ : 0 < π := Real.pi_pos
    calc 16 / π * ‖J‖ ≤ 16 / π * (2 * (π / 16 * (17 + A) * q ^ 4 + (A + 1) * q ^ 10)) :=
          mul_le_mul_of_nonneg_left hJ (by positivity)
      _ = 2 * (17 + A) * q ^ 4 + 32 / π * (A + 1) * q ^ 10 := by field_simp; ring
      _ ≤ 2 * (17 + A) * q ^ 4 + 11 * (A + 1) * q ^ 4 := by
          have h32 : 32 / π ≤ 11 := by
            rw [div_le_iff₀ hπ]; linarith [Real.pi_gt_three]
          have : 32 / π * (A + 1) * q ^ 10 ≤ 11 * (A + 1) * q ^ 4 :=
            mul_le_mul (mul_le_mul_of_nonneg_right h32 (by positivity)) hq104 (by positivity)
              (by positivity)
          linarith
      _ = (13 * A + 45) * q ^ 4 := by ring
  -- choose the scale
  have hq20 : ∀ x : ℝ, 0 ≤ x → (x ^ (1 / 20 : ℝ)) ^ 20 = x := by
    intro x hx
    rw [show (1 / 20 : ℝ) = ((20 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow hx (by norm_num)
  have hhalf : ∀ x : ℝ, 0 ≤ x → x ≤ (1 / 2) ^ 20 → x ^ (1 / 20 : ℝ) ≤ 1 / 2 := by
    intro x hx hxs
    have h := Real.rpow_le_rpow hx hxs (by norm_num : (0 : ℝ) ≤ 1 / 20)
    rw [show (1 / 20 : ℝ) = ((20 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)] at h
    rwa [show (1 / 20 : ℝ) = ((20 : ℕ) : ℝ)⁻¹ by norm_num]
  rcases hε.lt_or_eq with hεp | hε0
  · -- `ε > 0`: `q = ε^{1/20}`
    set q := ε ^ (1 / 20 : ℝ)
    have hq0 : 0 < q := Real.rpow_pos_of_pos hεp _
    have h := hcore q hq0 (hhalf ε hε (hεε.trans hε₀s)) (hq20 ε hε).ge
      ((hq20 ε hε).le.trans (hεε.trans hε₀3))
    have h5 : ε ^ (1 / 5 : ℝ) = q ^ 4 := by
      rw [← Real.rpow_natCast q 4, ← Real.rpow_mul hε]
      norm_num
    rw [h5]; exact h
  · -- `ε = 0`: let `q → 0`
    subst hε0
    rw [Real.zero_rpow (by norm_num), mul_zero]
    set M := ‖(16 / π : ℂ) * ∫ X in ball (0 : ℂ) (1 / 4), F X ^ n‖
    by_contra hM
    push Not at hM
    set C := 13 * A + 45
    have hC : 0 < C := by positivity
    set q₀ := ε₀ ^ (1 / 20 : ℝ)
    have hε₀p : 0 < ε₀ := lt_min hε₃ (by norm_num)
    have hq₀ : 0 < q₀ := Real.rpow_pos_of_pos hε₀p _
    set q := min q₀ (min (1 / 2) (M / (2 * C)))
    have hq0 : 0 < q := lt_min hq₀ (lt_min (by norm_num) (by positivity))
    have hqq₀ : q ≤ q₀ := min_le_left _ _
    have hq1 : q ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hqM : q ≤ M / (2 * C) := (min_le_right _ _).trans (min_le_right _ _)
    have hq3 : q ^ 20 ≤ ε₃ := by
      have : q ^ 20 ≤ q₀ ^ 20 := pow_le_pow_left₀ hq0.le hqq₀ 20
      rw [hq20 ε₀ hε₀p.le] at this
      exact this.trans hε₀3
    have h := hcore q hq0 hq1 (by positivity) hq3
    have hq4 : q ^ 4 ≤ q := pow_le_of_le_one hq0.le (by linarith) (by norm_num)
    have : C * q ≤ M / 2 := by
      calc C * q ≤ C * (M / (2 * C)) := mul_le_mul_of_nonneg_left hqM hC.le
        _ = M / 2 := by field_simp
    nlinarith

/-- M6.A5 helper (`thm15_1` at the origin): a `K`-q.c. self-map of `𝔻` fixing `0` with `K ≤ 8/7` maps
`closedBall 0 (1/4)` into `closedBall 0 (1/2)`. -/
theorem s07c_fkps_m6_half {F : ℂ → ℂ} {K : ℝ} (hF : IsKQC F unitDisc K) (himg : F '' unitDisc = unitDisc)
    (hF0 : F 0 = 0) (hK : K ≤ 8 / 7) {X : ℂ} (hX : ‖X‖ ≤ 1 / 4) : ‖F X‖ ≤ 1 / 2 := by
  have hK1 : 1 ≤ K := hF.2.1
  have hXD : X ∈ unitDisc := mem_ball_zero_iff.2 (by linarith)
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have h := thm15_1 hF himg hXD h0
  simp only [hF0, sub_zero, map_zero, zero_mul, div_one] at h
  have hα0 : 0 < 1 / K := by positivity
  have hα78 : 7 / 8 ≤ 1 / K := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hX2 : 15 / 16 ≤ 1 - ‖X‖ ^ 2 := by nlinarith [norm_nonneg X]
  have hX21 : 1 - ‖X‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg X]
  have hden : 15 / 16 ≤ (1 - ‖X‖ ^ 2) ^ (1 / (2 * K)) := by
    have h1 : 1 / (2 * K) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    calc (15 / 16 : ℝ) ≤ 1 - ‖X‖ ^ 2 := hX2
      _ = (1 - ‖X‖ ^ 2) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge' (by linarith) hX21 (by positivity) h1
  have hnum : (4 : ℝ) ^ (1 - 1 / K) * ‖X‖ ^ (1 / K) ≤ 15 / 32 := by
    have h1 : ‖X‖ ^ (1 / K) ≤ (1 / 4 : ℝ) ^ (1 / K) := Real.rpow_le_rpow (norm_nonneg _) hX hα0.le
    have h2 : (4 : ℝ) ^ (1 - 1 / K) * (1 / 4 : ℝ) ^ (1 / K) = (4 : ℝ) ^ (1 - 2 * (1 / K)) := by
      rw [one_div (4 : ℝ), Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num),
        ← Real.rpow_add (by norm_num)]
      ring_nf
    have h3 : (4 : ℝ) ^ (1 - 2 * (1 / K)) ≤ (4 : ℝ) ^ (-(3 / 4) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h4 : (4 : ℝ) ^ (-(3 / 4) : ℝ) ≤ 15 / 32 := by
      rw [Real.rpow_neg (by norm_num)]
      have h5 : (32 / 15 : ℝ) ≤ (4 : ℝ) ^ (3 / 4 : ℝ) := by
        by_contra hc
        push Not at hc
        have h6 : ((4 : ℝ) ^ (3 / 4 : ℝ)) ^ 4 < (32 / 15) ^ 4 :=
          pow_lt_pow_left₀ hc (by positivity) (by norm_num)
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          show (3 / 4 : ℝ) * ((4 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h6
        norm_num at h6
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      norm_num
      linarith
    calc (4 : ℝ) ^ (1 - 1 / K) * ‖X‖ ^ (1 / K) ≤ (4 : ℝ) ^ (1 - 1 / K) * (1 / 4 : ℝ) ^ (1 / K) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := h2
      _ ≤ _ := h3.trans h4
  calc ‖F X‖ ≤ _ := h
    _ ≤ (15 / 32) / (15 / 16) := div_le_div₀ (by norm_num) hnum (by norm_num) hden
    _ = 1 / 2 := by norm_num

/-- M6.A5 helper: the Poisson kernel is the real part of the Herglotz kernel. -/
theorem s07c_fkps_m6_pk_re (e w : ℂ) (he : ‖e‖ = 1) :
    (1 - ‖w‖ ^ 2) / ‖e - w‖ ^ 2 = ((e + w) / (e - w)).re := by
  have h1 : e.re ^ 2 + e.im ^ 2 = 1 := by
    have := Complex.sq_norm e
    rw [he, Complex.normSq_apply] at this
    nlinarith
  have h2 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [div_re, Complex.normSq_eq_norm_sq, ← add_div]
  congr 1
  simp only [add_re, sub_re, add_im, sub_im]
  rw [h2]
  linear_combination -h1

/-- M6.A5 helper (finite geometric expansion): `ζ/(1-ζ) = Σ_{k<N} ζ^{k+1} + ζ^{N+1}/(1-ζ)`. -/
theorem s07c_fkps_m6_geom (ζ : ℂ) (hζ : ζ ≠ 1) (N : ℕ) :
    ζ / (1 - ζ) = (∑ k ∈ Finset.range N, ζ ^ (k + 1)) + ζ ^ (N + 1) / (1 - ζ) := by
  have h1 : (1 : ℂ) - ζ ≠ 0 := sub_ne_zero.2 hζ.symm
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, Finset.sum_range_succ]
    field_simp
    ring

/-- M6.A5 helper: the Poisson kernel at `|w| ≤ 1/2` is log-Lipschitz with constant `4` in the boundary
variable. -/
theorem s07c_fkps_m6_pk_lip (w : ℂ) (hw : ‖w‖ ≤ 1 / 2) (τ τ' : ℝ) :
    (1 - ‖w‖ ^ 2) / ‖Complex.exp (τ' * I) - w‖ ^ 2 ≤
      Real.exp (4 * |τ - τ'|) * ((1 - ‖w‖ ^ 2) / ‖Complex.exp (τ * I) - w‖ ^ 2) := by
  set d := ‖Complex.exp (τ * I) - w‖
  set d' := ‖Complex.exp (τ' * I) - w‖
  have hlow : ∀ t : ℝ, 1 / 2 ≤ ‖Complex.exp (t * I) - w‖ := by
    intro t
    have := norm_sub_norm_le (Complex.exp (t * I)) w
    rw [Complex.norm_exp_ofReal_mul_I] at this
    linarith
  have hd' : 1 / 2 ≤ d' := hlow τ'
  have hd : 1 / 2 ≤ d := hlow τ
  have hee : ‖Complex.exp (τ * I) - Complex.exp (τ' * I)‖ ≤ |τ - τ'| := by
    have hx : Complex.exp (τ * I) = Complex.exp (τ' * I) * Complex.exp (I * ((τ - τ' : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hx, ← mul_sub_one, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact (Real.norm_exp_I_mul_ofReal_sub_one_le).trans_eq (Real.norm_eq_abs _)
  set Δ := |τ - τ'|
  have hΔ : 0 ≤ Δ := abs_nonneg _
  have hdd : d ≤ d' * (1 + 2 * Δ) := by
    have : d ≤ d' + Δ := by
      calc d = ‖(Complex.exp (τ' * I) - w) + (Complex.exp (τ * I) - Complex.exp (τ' * I))‖ := by
            rw [show (Complex.exp (τ' * I) - w) + (Complex.exp (τ * I) - Complex.exp (τ' * I)) =
              Complex.exp (τ * I) - w by ring]
        _ ≤ d' + ‖Complex.exp (τ * I) - Complex.exp (τ' * I)‖ := norm_add_le _ _
        _ ≤ d' + Δ := by linarith
    nlinarith
  have hexp : 1 + 2 * Δ ≤ Real.exp (2 * Δ) := by linarith [Real.add_one_le_exp (2 * Δ)]
  have hd2 : d ^ 2 ≤ Real.exp (4 * Δ) * d' ^ 2 := by
    have h1 : d ≤ d' * Real.exp (2 * Δ) := hdd.trans (mul_le_mul_of_nonneg_left hexp (by linarith))
    have h2 : d ^ 2 ≤ (d' * Real.exp (2 * Δ)) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    have h3 : (d' * Real.exp (2 * Δ)) ^ 2 = Real.exp (4 * Δ) * d' ^ 2 := by
      rw [mul_pow, sq (Real.exp _), ← Real.exp_add]; ring_nf
    linarith
  have hN : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left hd2 hN
  nlinarith

/-- M6.A5 helper (interpolation): `x ≤ a`, `x ≤ b` give `x ≤ a^{5/6} b^{1/6}`. -/
theorem s07c_fkps_m6_interp {x a b : ℝ} (hx : 0 ≤ x) (ha : x ≤ a) (hb : x ≤ b) :
    x ≤ a ^ (5 / 6 : ℝ) * b ^ (1 / 6 : ℝ) := by
  have h1 : x = x ^ (5 / 6 : ℝ) * x ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_add' hx (by norm_num)]; norm_num
  rw [h1]
  exact mul_le_mul (Real.rpow_le_rpow hx ha (by norm_num)) (Real.rpow_le_rpow hx hb (by norm_num))
    (by positivity) (Real.rpow_nonneg (hx.trans ha) _)

/-- M6.A5 helper: `Σ_{k<N} r^{k+1} ≤ r/(1-r)` for `0 ≤ r < 1`. -/
theorem s07c_fkps_m6_geom_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, r ^ (k + 1) ≤ r / (1 - r) := by
  have h : (1 - r) * ∑ k ∈ Finset.range N, r ^ (k + 1) = r - r ^ (N + 1) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, mul_add, ih]; ring
  rw [le_div_iff₀ (by linarith), mul_comm, h]
  linarith [pow_nonneg hr0 (N + 1)]

/-- M6.A5 helper: Poisson kernel bounds at `|w| ≤ 1/2`. -/
theorem s07c_fkps_m6_pk_bounds (w : ℂ) (hw : ‖w‖ ≤ 1 / 2) (τ : ℝ) :
    1 / 3 ≤ (1 - ‖w‖ ^ 2) / ‖Complex.exp (τ * I) - w‖ ^ 2 ∧
      (1 - ‖w‖ ^ 2) / ‖Complex.exp (τ * I) - w‖ ^ 2 ≤ 4 := by
  have h1 := norm_sub_norm_le (Complex.exp (τ * I)) w
  have h2 := norm_sub_le (Complex.exp (τ * I)) w
  rw [Complex.norm_exp_ofReal_mul_I] at h1 h2
  have hw0 := norm_nonneg w
  have hd0 : 0 < ‖Complex.exp (τ * I) - w‖ ^ 2 := by nlinarith
  constructor
  · rw [le_div_iff₀ hd0]; nlinarith
  · rw [div_le_iff₀ hd0]; nlinarith

/-- M6.A5 helper: the averaged Poisson integrand is continuous on `closedBall 0 (1/4)`. -/
theorem s07c_fkps_m6_pk_contOn {F : ℂ → ℂ} (hFc : Continuous F)
    (hF2 : ∀ X : ℂ, ‖X‖ ≤ 1 / 4 → ‖F X‖ ≤ 1 / 2) (τ : ℝ) :
    ContinuousOn (fun X => (1 - ‖F X‖ ^ 2) / ‖Complex.exp (τ * I) - F X‖ ^ 2)
      (closedBall (0 : ℂ) (1 / 4)) := by
  refine (continuous_const.sub (hFc.norm.pow 2)).continuousOn.div
    ((continuous_const.sub hFc).norm.pow 2).continuousOn fun X hX => ?_
  have h := hF2 X (mem_closedBall_zero_iff.1 hX)
  have h1 := norm_sub_norm_le (Complex.exp (τ * I)) (F X)
  rw [Complex.norm_exp_ofReal_mul_I] at h1
  have : 0 < ‖Complex.exp (τ * I) - F X‖ := by linarith
  positivity

/-- M6.A5 helper (Fourier side of `ρ`): with `|F| ≤ 1/2` on `closedBall 0 (1/4)` and moments
`|⨍_{B(0,1/4)} F^k| ≤ B` (`k ≥ 1`), `|2π ρ(τ) - 1| ≤ 2 B^{5/6} r/(1-r)`, `r = 2^{-1/6}`. -/
theorem s07c_fkps_m6_rho_fourier {F : ℂ → ℂ} {B : ℝ} (hFc : Continuous F)
    (hF2 : ∀ X : ℂ, ‖X‖ ≤ 1 / 4 → ‖F X‖ ≤ 1 / 2) (hB : 0 ≤ B)
    (hM : ∀ k : ℕ, 1 ≤ k → ‖(16 / π : ℂ) * ∫ X in ball (0 : ℂ) (1 / 4), F X ^ k‖ ≤ B) (τ : ℝ) :
    |2 * π * (8 / π ^ 2 * ∫ X in ball (0 : ℂ) (1 / 4),
        (1 - ‖F X‖ ^ 2) / ‖Complex.exp (τ * I) - F X‖ ^ 2) - 1| ≤
      2 * B ^ (5 / 6 : ℝ) * ((1 / 2 : ℝ) ^ (1 / 6 : ℝ) / (1 - (1 / 2 : ℝ) ^ (1 / 6 : ℝ))) := by
  have hπ : 0 < π := Real.pi_pos
  set e := Complex.exp (τ * I) with he_def
  have he1 : ‖e‖ = 1 := Complex.norm_exp_ofReal_mul_I τ
  have he0 : e ≠ 0 := Complex.exp_ne_zero _
  set S := ball (0 : ℂ) (1 / 4)
  have hvol : volume.real S = π / 16 := by
    rw [measureReal_def, s07c_fkps_m6_vol_ball (by norm_num), ENNReal.toReal_ofReal (by positivity)]
    ring
  have hFS : ∀ X ∈ closedBall (0 : ℂ) (1 / 4), ‖F X‖ ≤ 1 / 2 := fun X hX =>
    hF2 X (mem_closedBall_zero_iff.1 hX)
  have hne : ∀ X ∈ closedBall (0 : ℂ) (1 / 4), e - F X ≠ 0 := by
    intro X hX h
    have h1 := hFS X hX
    rw [sub_eq_zero] at h
    rw [← h, he1] at h1
    norm_num at h1
  set Q : ℂ → ℂ := fun X => F X / (e - F X) with hQ_def
  have hQc : ContinuousOn Q (closedBall (0 : ℂ) (1 / 4)) :=
    hFc.continuousOn.div (continuous_const.sub hFc).continuousOn hne
  have hint : ∀ {g : ℂ → ℂ}, ContinuousOn g (closedBall (0 : ℂ) (1 / 4)) → IntegrableOn g S :=
    fun hg => (hg.integrableOn_compact (isCompact_closedBall 0 _)).mono_set ball_subset_closedBall
  -- `P = 1 + 2 Re Q` on the closed ball
  have hPQ : ∀ X ∈ closedBall (0 : ℂ) (1 / 4),
      (1 - ‖F X‖ ^ 2) / ‖e - F X‖ ^ 2 = 1 + 2 * (Q X).re := by
    intro X hX
    rw [s07c_fkps_m6_pk_re e (F X) he1]
    have h1 := hne X hX
    have : (e + F X) / (e - F X) = 1 + 2 * Q X := by
      simp only [hQ_def]; field_simp; ring
    rw [this]
    simp
  have hPint : ∫ X in S, (1 - ‖F X‖ ^ 2) / ‖e - F X‖ ^ 2 = π / 16 + 2 * (∫ X in S, Q X).re := by
    have hQre : IntegrableOn (fun X => 2 * (Q X).re) S := (hint hQc).re.const_mul 2
    have hre : ∫ X in S, (Q X).re = (∫ X in S, Q X).re := integral_re (hint hQc)
    rw [setIntegral_congr_fun measurableSet_ball (fun X hX => hPQ X (ball_subset_closedBall hX)),
      integral_add (integrableOn_const measure_ball_lt_top.ne) hQre,
      integral_const_mul, hre, setIntegral_const, hvol, smul_eq_mul, mul_one]
  have hmain : |2 * π * (8 / π ^ 2 * ∫ X in S, (1 - ‖F X‖ ^ 2) / ‖e - F X‖ ^ 2) - 1| ≤
      32 / π * ‖∫ X in S, Q X‖ := by
    rw [hPint]
    have : 2 * π * (8 / π ^ 2 * (π / 16 + 2 * (∫ X in S, Q X).re)) - 1 =
        32 / π * (∫ X in S, Q X).re := by field_simp; ring
    rw [this, abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
  -- the moments bound and their decay
  have hMk : ∀ k : ℕ, 1 ≤ k → 32 / π * ‖∫ X in S, F X ^ k‖ ≤ 2 * B := by
    intro k hk
    have h := hM k hk
    have hn : ‖(16 / π : ℂ)‖ = 16 / π := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hπ.le]; norm_num
    rw [norm_mul, hn] at h
    have : 32 / π * ‖∫ X in S, F X ^ k‖ = 2 * (16 / π * ‖∫ X in S, F X ^ k‖) := by ring
    linarith
  have hMd : ∀ k : ℕ, 32 / π * ‖∫ X in S, F X ^ k‖ ≤ 2 * (1 / 2 : ℝ) ^ k := by
    intro k
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := S) (f := fun X => F X ^ k)
      (C := (1 / 2 : ℝ) ^ k) measure_ball_lt_top (fun X hX => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hFS X (ball_subset_closedBall hX)) k)
    rw [hvol] at h
    calc 32 / π * ‖∫ X in S, F X ^ k‖ ≤ 32 / π * ((1 / 2 : ℝ) ^ k * (π / 16)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 2 * (1 / 2 : ℝ) ^ k := by field_simp; ring
  set r : ℝ := (1 / 2 : ℝ) ^ (1 / 6 : ℝ) with hr_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)
  have hMi : ∀ k : ℕ, 1 ≤ k → 32 / π * ‖∫ X in S, F X ^ k‖ ≤ 2 * B ^ (5 / 6 : ℝ) * r ^ k := by
    intro k hk
    have h := s07c_fkps_m6_interp (by positivity) (hMk k hk) (hMd k)
    have h1 : (2 * B) ^ (5 / 6 : ℝ) * (2 * (1 / 2 : ℝ) ^ k) ^ (1 / 6 : ℝ) =
        2 * B ^ (5 / 6 : ℝ) * r ^ k := by
      rw [Real.mul_rpow (by norm_num) hB, Real.mul_rpow (by norm_num) (by positivity),
        ← Real.rpow_natCast (1 / 2 : ℝ) k, ← Real.rpow_mul (by norm_num), mul_comm (k : ℝ),
        Real.rpow_mul (by norm_num), Real.rpow_natCast, ← hr_def]
      have h2 : (2 : ℝ) ^ (5 / 6 : ℝ) * (2 : ℝ) ^ (1 / 6 : ℝ) = 2 := by
        rw [← Real.rpow_add (by norm_num)]; norm_num
      calc (2 : ℝ) ^ (5 / 6 : ℝ) * B ^ (5 / 6 : ℝ) * ((2 : ℝ) ^ (1 / 6 : ℝ) * r ^ k)
          = ((2 : ℝ) ^ (5 / 6 : ℝ) * (2 : ℝ) ^ (1 / 6 : ℝ)) * B ^ (5 / 6 : ℝ) * r ^ k := by ring
        _ = 2 * B ^ (5 / 6 : ℝ) * r ^ k := by rw [h2]
    linarith
  -- the expansion of `∫ Q`
  have hexp : ∀ N : ℕ, 32 / π * ‖∫ X in S, Q X‖ ≤
      2 * B ^ (5 / 6 : ℝ) * (r / (1 - r)) + 2 * (1 / 2 : ℝ) ^ N := by
    intro N
    set R : ℂ → ℂ := fun X => (F X / e) ^ (N + 1) / (1 - F X / e) with hR_def
    have hne' : ∀ X ∈ closedBall (0 : ℂ) (1 / 4), F X / e ≠ 1 := by
      intro X hX h
      have h1 := hFS X hX
      rw [div_eq_one_iff_eq he0] at h
      rw [h, he1] at h1
      norm_num at h1
    have hQR : ∀ X ∈ closedBall (0 : ℂ) (1 / 4),
        Q X = (∑ k ∈ Finset.range N, F X ^ (k + 1) / e ^ (k + 1)) + R X := by
      intro X hX
      have h1 : Q X = (F X / e) / (1 - F X / e) := by
        simp only [hQ_def]
        have := hne X hX
        field_simp
      rw [h1, s07c_fkps_m6_geom _ (hne' X hX) N]
      simp only [div_pow, hR_def]
    have hRc : ContinuousOn R (closedBall (0 : ℂ) (1 / 4)) := by
      refine ((hFc.div_const e).pow (N + 1)).continuousOn.div
        (continuous_const.sub (hFc.div_const e)).continuousOn fun X hX => ?_
      exact sub_ne_zero.2 (hne' X hX).symm
    have hkc : ∀ k : ℕ, ContinuousOn (fun X => F X ^ (k + 1) / e ^ (k + 1)) (closedBall (0 : ℂ) (1 / 4)) :=
      fun k => ((hFc.pow (k + 1)).div_const _).continuousOn
    have hJ : ∫ X in S, Q X =
        (∑ k ∈ Finset.range N, (∫ X in S, F X ^ (k + 1)) / e ^ (k + 1)) + ∫ X in S, R X := by
      rw [setIntegral_congr_fun measurableSet_ball (fun X hX => hQR X (ball_subset_closedBall hX)),
        integral_add (integrable_finsetSum _ fun k _ => hint (hkc k)) (hint hRc),
        integral_finsetSum _ fun k _ => hint (hkc k)]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      exact integral_div _ _
    have hRb : ‖∫ X in S, R X‖ ≤ (1 / 2 : ℝ) ^ N * (π / 16) := by
      have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := S) (f := R)
        (C := (1 / 2 : ℝ) ^ N) measure_ball_lt_top (fun X hX => by
          have hX' := ball_subset_closedBall hX
          have h1 : ‖F X / e‖ ≤ 1 / 2 := by rw [norm_div, he1, div_one]; exact hFS X hX'
          have h2 : 1 / 2 ≤ ‖1 - F X / e‖ := by
            have := norm_sub_norm_le (1 : ℂ) (F X / e)
            rw [norm_one] at this; linarith
          simp only [hR_def]
          rw [norm_div, norm_pow, div_le_iff₀ (by linarith)]
          calc ‖F X / e‖ ^ (N + 1) ≤ (1 / 2 : ℝ) ^ (N + 1) := pow_le_pow_left₀ (norm_nonneg _) h1 _
            _ = (1 / 2 : ℝ) ^ N * (1 / 2) := pow_succ _ _
            _ ≤ (1 / 2 : ℝ) ^ N * ‖1 - F X / e‖ := mul_le_mul_of_nonneg_left h2 (by positivity))
      rwa [hvol] at h
    rw [hJ]
    calc 32 / π * ‖(∑ k ∈ Finset.range N, (∫ X in S, F X ^ (k + 1)) / e ^ (k + 1)) + ∫ X in S, R X‖
        ≤ 32 / π * ((∑ k ∈ Finset.range N, ‖∫ X in S, F X ^ (k + 1)‖) + ‖∫ X in S, R X‖) := by
          refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add
            ((norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun k _ => ?_)) le_rfl)) (by positivity)
          rw [norm_div, norm_pow, he1, one_pow, div_one]
      _ = (∑ k ∈ Finset.range N, 32 / π * ‖∫ X in S, F X ^ (k + 1)‖) + 32 / π * ‖∫ X in S, R X‖ := by
          rw [mul_add, Finset.mul_sum]
      _ ≤ (∑ k ∈ Finset.range N, 2 * B ^ (5 / 6 : ℝ) * r ^ (k + 1)) + 2 * (1 / 2 : ℝ) ^ N := by
          refine add_le_add (Finset.sum_le_sum fun k _ => hMi (k + 1) (by omega)) ?_
          calc 32 / π * ‖∫ X in S, R X‖ ≤ 32 / π * ((1 / 2 : ℝ) ^ N * (π / 16)) :=
                mul_le_mul_of_nonneg_left hRb (by positivity)
            _ = 2 * (1 / 2 : ℝ) ^ N := by field_simp; ring
      _ ≤ 2 * B ^ (5 / 6 : ℝ) * (r / (1 - r)) + 2 * (1 / 2 : ℝ) ^ N := by
          rw [← Finset.mul_sum]
          gcongr
          exact s07c_fkps_m6_geom_le hr0.le hr1 N
  -- let `N → ∞`
  refine (hmain.trans ?_)
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < δ / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  linarith [hexp N]

/-- M6.A5 helper (Poisson representation of the averaged harmonic measure): for `v` harmonic near `𝔻̄` and
`|F| ≤ 1/2` on `closedBall 0 (1/4)`, `16/π ∫_{B(0,1/4)} v ∘ F = ∫₀^{2π} v(e^{iτ}) ρ(τ) dτ`. -/
theorem s07c_fkps_m6_rho_rep {F : ℂ → ℂ} (hFc : Continuous F)
    (hF2 : ∀ X : ℂ, ‖X‖ ≤ 1 / 4 → ‖F X‖ ≤ 1 / 2) {v : ℂ → ℝ}
    (hv : InnerProductSpace.HarmonicOnNhd v (closedBall 0 1)) :
    16 / π * ∫ X in ball (0 : ℂ) (1 / 4), v (F X) =
      ∫ τ in (0 : ℝ)..2 * π, v (Complex.exp (τ * I)) * (8 / π ^ 2 *
        ∫ X in ball (0 : ℂ) (1 / 4), (1 - ‖F X‖ ^ 2) / ‖Complex.exp (τ * I) - F X‖ ^ 2) := by
  have hπ : 0 < π := Real.pi_pos
  set S := ball (0 : ℂ) (1 / 4)
  set G : ℂ → ℝ → ℝ := fun X τ =>
    (1 - ‖F X‖ ^ 2) / ‖Complex.exp (τ * I) - F X‖ ^ 2 * v (Complex.exp (τ * I)) with hG_def
  -- the Poisson formula at `F X`
  have hpt : ∀ X ∈ S, v (F X) = (2 * π)⁻¹ * ∫ τ in Ioc (0 : ℝ) (2 * π), G X τ := by
    intro X hX
    have hX4 : ‖X‖ ≤ 1 / 4 := (mem_ball_zero_iff.1 hX).le
    have hw : F X ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.2 (by linarith [hF2 X hX4])
    have h := hv.circleAverage_poissonKernel_smul hw
    rw [Real.circleAverage_def, smul_eq_mul] at h
    rw [← h, ← intervalIntegral.integral_of_le (by positivity)]
    congr 1
    refine intervalIntegral.integral_congr fun τ _ => ?_
    show poissonKernel 0 (F X) (circleMap 0 1 τ) * v (circleMap 0 1 τ) = G X τ
    rw [poissonKernel_def]
    simp only [hG_def, circleMap, zero_add, Complex.ofReal_one, one_mul, sub_zero,
      Complex.norm_exp_ofReal_mul_I, one_pow]
  -- integrability on the product
  have hvc : ContinuousOn v (closedBall 0 1) := hv.continuousOn
  have hGc : ContinuousOn (Function.uncurry G) (closedBall (0 : ℂ) (1 / 4) ×ˢ Icc 0 (2 * π)) := by
    have hec : Continuous fun p : ℂ × ℝ => Complex.exp (p.2 * I) :=
      Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
    refine ContinuousOn.mul ?_ (hvc.comp hec.continuousOn fun p _ => ?_)
    · refine (continuous_const.sub ((hFc.comp continuous_fst).norm.pow 2)).continuousOn.div
        ((hec.sub (hFc.comp continuous_fst)).norm.pow 2).continuousOn fun p hp => ?_
      have h := hF2 p.1 (mem_closedBall_zero_iff.1 hp.1)
      have h1 := norm_sub_norm_le (Complex.exp (p.2 * I)) (F p.1)
      rw [Complex.norm_exp_ofReal_mul_I] at h1
      have : 0 < ‖Complex.exp (p.2 * I) - F p.1‖ := by linarith
      positivity
    · rw [mem_closedBall_zero_iff, Complex.norm_exp_ofReal_mul_I]
  have hGi : Integrable (Function.uncurry G) ((volume.restrict S).prod (volume.restrict (Ioc 0 (2 * π)))) := by
    rw [Measure.prod_restrict]
    exact (hGc.integrableOn_compact ((isCompact_closedBall 0 _).prod isCompact_Icc)).mono_set
      (prod_mono ball_subset_closedBall Ioc_subset_Icc_self)
  have hswap := integral_integral_swap hGi
  rw [setIntegral_congr_fun measurableSet_ball hpt, integral_const_mul, hswap,
    intervalIntegral.integral_of_le (by positivity)]
  rw [← mul_assoc]
  refine (integral_const_mul (μ := volume.restrict (Ioc (0 : ℝ) (2 * π))) (16 / π * (2 * π)⁻¹ : ℝ) _).symm.trans ?_
  refine setIntegral_congr_fun measurableSet_Ioc fun τ _ => ?_
  show 16 / π * (2 * π)⁻¹ * ∫ X in S, G X τ = _
  simp only [hG_def]
  rw [integral_mul_const]
  field_simp
  ring

/-- M6.A5 (the averaged harmonic measure `ρ = ⨍_{X ∈ B(0,1/4)} ω^{F X}`, density w.r.t. `dτ`): it is positive,
`2π`-periodic, log-Lipschitz (`|F| ≤ 1/2` on `B(0, 1/4)` by LZ `thm15_1`), uniformly close to `1/(2π)` (A4 and the
Fourier series of the Poisson kernel), and represents the `B(0,1/4)`-average of `v ∘ F` for `v` harmonic near
`𝔻̄`. -/
theorem s07c_fkps_m6_rho : ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧ ∀ (F : ℂ → ℂ) (a : ℂ → ℝ) (K ε : ℝ) (ρ : ℝ → ℝ),
    IsKQC F univ K → F '' univ = univ → F '' unitDisc = unitDisc → F 0 = 0 →
    Measurable a → (∀ z, 0 ≤ a z) → (∀ z ∈ unitDisc, a z ≤ ε₀) →
    (∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) →
      ‖LiZhongQC.complexDilatation F w‖ ≤ a z) →
    0 ≤ ε → ε ≤ ε₀ →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
        ≤ ENNReal.ofReal (ε * r)) →
    (∀ τ : ℝ, ρ τ = 8 / π ^ 2 *
      ∫ X in ball (0 : ℂ) (1 / 4), (1 - ‖F X‖ ^ 2) / ‖Complex.exp (τ * I) - F X‖ ^ 2) →
    (∀ τ : ℝ, 0 < ρ τ) ∧ (∀ τ : ℝ, ρ (τ + 2 * π) = ρ τ) ∧
    (∀ τ τ' : ℝ, ρ τ' ≤ Real.exp (4 * |τ - τ'|) * ρ τ) ∧
    (∀ τ : ℝ, |2 * π * ρ τ - 1| ≤ C * ε ^ (1 / 6 : ℝ)) ∧
    ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (closedBall 0 1) →
      16 / π * ∫ X in ball (0 : ℂ) (1 / 4), v (F X) =
        ∫ τ in (0 : ℝ)..2 * π, v (Complex.exp (τ * I)) * ρ τ := by
  obtain ⟨ε₄, C₄, hε₄, hC₄, hA4⟩ := s07c_fkps_m6_moment
  set r : ℝ := (1 / 2 : ℝ) ^ (1 / 6 : ℝ) with hr_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)
  refine ⟨min ε₄ (1 / 15), 2 * C₄ ^ (5 / 6 : ℝ) * (r / (1 - r)), lt_min hε₄ (by norm_num),
    mul_pos (mul_pos two_pos (Real.rpow_pos_of_pos hC₄ _)) (div_pos hr0 (by linarith)), ?_⟩
  intro F a K ε ρ hF hsurj hFD hF0 ha ha0 hale hW hε hεε hcarl hρ
  set ε₀ := min ε₄ (1 / 15) with hε₀_def
  have hε₀0 : 0 ≤ ε₀ := hε.trans hεε
  have hε₀15 : ε₀ ≤ 1 / 15 := min_le_right _ _
  have hKD := s07c_fkps_m6_kqc hF hε₀0 (by linarith) (s07c_fkps_m6_dil_le hale hW)
  have hK87 : (1 + ε₀) / (1 - ε₀) ≤ 8 / 7 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hFc : Continuous F := continuousOn_univ.mp hF.2.2.1.1
  have hF2 : ∀ X : ℂ, ‖X‖ ≤ 1 / 4 → ‖F X‖ ≤ 1 / 2 := fun X hX =>
    s07c_fkps_m6_half hKD hFD hF0 hK87 hX
  have hint : ∀ τ : ℝ, IntegrableOn (fun X => (1 - ‖F X‖ ^ 2) / ‖Complex.exp (τ * I) - F X‖ ^ 2)
      (ball (0 : ℂ) (1 / 4)) := fun τ =>
    ((s07c_fkps_m6_pk_contOn hFc hF2 τ).integrableOn_compact (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall
  have hvol : volume.real (ball (0 : ℂ) (1 / 4)) = π / 16 := by
    rw [measureReal_def, s07c_fkps_m6_vol_ball (by norm_num), ENNReal.toReal_ofReal (by positivity)]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro τ
    rw [hρ τ]
    have h := setIntegral_mono_on (integrableOn_const measure_ball_lt_top.ne) (hint τ) measurableSet_ball
      (fun X hX => (s07c_fkps_m6_pk_bounds (F X) (hF2 X (mem_ball_zero_iff.1 hX).le) τ).1)
    rw [setIntegral_const, hvol, smul_eq_mul] at h
    have hπ := Real.pi_pos
    exact mul_pos (by positivity) (lt_of_lt_of_le (by positivity) h)
  · intro τ
    rw [hρ, hρ]
    have hpe : Complex.exp (((τ + 2 * π : ℝ) : ℂ) * I) = Complex.exp (τ * I) := by
      rw [show ((τ + 2 * π : ℝ) : ℂ) * I = (τ : ℂ) * I + 2 * π * I by push_cast; ring,
        Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    rw [hpe]
  · intro τ τ'
    rw [hρ τ', hρ τ]
    have h := setIntegral_mono_on (hint τ') ((hint τ).const_mul (Real.exp (4 * |τ - τ'|)))
      measurableSet_ball (fun X hX => s07c_fkps_m6_pk_lip (F X) (hF2 X (mem_ball_zero_iff.1 hX).le) τ τ')
    rw [integral_const_mul] at h
    calc 8 / π ^ 2 * ∫ X in ball (0 : ℂ) (1 / 4), (1 - ‖F X‖ ^ 2) / ‖Complex.exp (τ' * I) - F X‖ ^ 2
        ≤ 8 / π ^ 2 * (Real.exp (4 * |τ - τ'|) *
            ∫ X in ball (0 : ℂ) (1 / 4), (1 - ‖F X‖ ^ 2) / ‖Complex.exp (τ * I) - F X‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by ring
  · intro τ
    rw [hρ τ]
    have hB0 : 0 ≤ C₄ * ε ^ (1 / 5 : ℝ) := mul_nonneg hC₄.le (Real.rpow_nonneg hε _)
    have h := s07c_fkps_m6_rho_fourier hFc hF2 hB0 (fun k hk => hA4 F a K ε hF hsurj hFD hF0 ha ha0
      (fun z hz => (hale z hz).trans (min_le_left _ _)) hW hε (hεε.trans (min_le_left _ _)) hcarl k hk) τ
    have hB : (C₄ * ε ^ (1 / 5 : ℝ)) ^ (5 / 6 : ℝ) = C₄ ^ (5 / 6 : ℝ) * ε ^ (1 / 6 : ℝ) := by
      rw [Real.mul_rpow hC₄.le (Real.rpow_nonneg hε _), ← Real.rpow_mul hε]
      norm_num
    rw [hB, ← hr_def] at h
    calc _ ≤ 2 * (C₄ ^ (5 / 6 : ℝ) * ε ^ (1 / 6 : ℝ)) * (r / (1 - r)) := h
      _ = 2 * C₄ ^ (5 / 6 : ℝ) * (r / (1 - r)) * ε ^ (1 / 6 : ℝ) := by ring
  · intro v hv
    rw [s07c_fkps_m6_rho_rep hFc hF2 hv]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    simp only [hρ τ]

/-- M6.A6 helper (trigonometric approximation): every continuous function on `ℝ/2πℤ` is uniformly within `δ`
of the boundary values `v(e^{iτ})` of a harmonic polynomial `v = Re p`. -/
theorem s07c_fkps_m6_trig_approx (Φ : C(AddCircle (2 * π), ℝ)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ v : ℂ → ℝ, ContDiff ℝ 2 v ∧ InnerProductSpace.HarmonicOnNhd v univ ∧
      ∀ τ : ℝ, |v (Complex.exp (τ * I)) - Φ (τ : AddCircle (2 * π))| ≤ δ := by
  haveI : Fact (0 < 2 * π) := ⟨by positivity⟩
  set Φc : C(AddCircle (2 * π), ℂ) := (⟨fun x : ℝ => (x : ℂ), Complex.continuous_ofReal⟩ : C(ℝ, ℂ)).comp Φ
  have hmem : Φc ∈ closure ((Submodule.span ℂ (range (@fourier (2 * π)))) : Set C(AddCircle (2 * π), ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    exact mem_univ _
  obtain ⟨q, hq, hdist⟩ := Metric.mem_closure_iff.1 hmem δ hδ
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hq
  set c' : ℤ → ℂ := fun n => if 0 ≤ n then c n else conj (c n) with hc'_def
  set p : ℂ → ℂ := fun z => ∑ n ∈ c.support, c' n * z ^ n.natAbs with hp_def
  have han : ∀ z, AnalyticAt ℂ p z := fun z =>
    Finset.analyticAt_fun_sum _ fun n _ => analyticAt_const.mul (analyticAt_id.pow _)
  have hharm : InnerProductSpace.HarmonicOnNhd (fun z => (p z).re) univ := fun z _ => (han z).harmonicAt_re
  refine ⟨fun z => (p z).re, contDiff_iff_contDiffAt.2 fun z => (hharm z (mem_univ z)).1, hharm, ?_⟩
  intro τ
  have hq_eval : q (τ : AddCircle (2 * π)) = ∑ n ∈ c.support, c n * Complex.exp (n * (τ * I)) := by
    rw [← hc, Finsupp.sum, ContinuousMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ContinuousMap.smul_apply, smul_eq_mul, fourier_coe_apply]
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    congr 2
    push_cast
    field_simp
  have hterm : ∀ n : ℤ, (c' n * Complex.exp (τ * I) ^ n.natAbs).re = (c n * Complex.exp (n * (τ * I))).re := by
    intro n
    rw [← Complex.exp_nat_mul]
    by_cases hn : 0 ≤ n
    · simp only [hc'_def, if_pos hn]
      have : ((n.natAbs : ℕ) : ℂ) = (n : ℂ) := by
        rw [Nat.cast_natAbs, abs_of_nonneg hn]
      rw [this]
    · simp only [hc'_def, if_neg hn]
      have h1 : ((n.natAbs : ℕ) : ℂ) = -(n : ℂ) := by
        rw [Nat.cast_natAbs, abs_of_neg (by omega), Int.cast_neg]
      rw [h1, ← Complex.conj_re (c n * Complex.exp (n * (τ * I))), map_mul, ← Complex.exp_conj]
      congr 3
      simp [Complex.conj_ofReal]
  have hre : (p (Complex.exp (τ * I))).re = (q (τ : AddCircle (2 * π))).re := by
    rw [hq_eval]
    simp only [hp_def, Complex.re_sum]
    exact Finset.sum_congr rfl fun n _ => hterm n
  have hΦ : (Φc (τ : AddCircle (2 * π))).re = Φ (τ : AddCircle (2 * π)) := by
    simp [Φc]
  have h1 := ContinuousMap.dist_apply_le_dist (f := Φc) (g := q) (τ : AddCircle (2 * π))
  show |(p (Complex.exp (τ * I))).re - Φ (τ : AddCircle (2 * π))| ≤ δ
  rw [hre, ← hΦ, ← Complex.sub_re]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [← dist_eq_norm, dist_comm]
  linarith

/-- M6.A6 helper (Cauchy–Schwarz from AM–GM): `|∫_S w| ≤ √(L V)` when `∫_S w² ≤ L` and `|S| = V`. -/
theorem s07c_fkps_m6_cs {w : ℂ → ℝ} {S : Set ℂ} {L V : ℝ} (hL0 : 0 ≤ L) (hV0 : 0 ≤ V)
    (hS : volume S = ENNReal.ofReal V) (hL : ∫⁻ X in S, ENNReal.ofReal (w X ^ 2) ≤ ENNReal.ofReal L) :
    |∫ X in S, w X| ≤ Real.sqrt (L * V) := by
  refine le_of_forall_pos_le_add fun t ht => ?_
  set a := Real.sqrt L
  set b := Real.sqrt V
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have haL : a ^ 2 = L := Real.sq_sqrt hL0
  have hbV : b ^ 2 = V := Real.sq_sqrt hV0
  set u := t / (a + b + 1)
  have hu : 0 < u := by positivity
  have hs : 0 < (a + u) / (b + u) := by positivity
  have h := s07c_fkps_m6_amgm hs hL0 hV0 hS hL
  have hsq : Real.sqrt (L * V) = a * b := by rw [Real.sqrt_mul hL0]
  rw [hsq]
  have e1 : (2 * ((a + u) / (b + u)))⁻¹ * L = a ^ 2 * (b + u) / (2 * (a + u)) := by
    rw [haL]; field_simp
  have e2 : (a + u) / (b + u) / 2 * V = (a + u) * b ^ 2 / (2 * (b + u)) := by
    rw [hbV]; field_simp
  have h1 : a ^ 2 * (b + u) / (2 * (a + u)) ≤ a * (b + u) / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg ha (mul_nonneg hu.le (add_nonneg hb hu.le))]
  have h2 : (a + u) * b ^ 2 / (2 * (b + u)) ≤ (a + u) * b / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hb (mul_nonneg hu.le (add_nonneg ha hu.le))]
  have h3 : a * (b + u) / 2 + (a + u) * b / 2 = a * b + u * (a + b) / 2 := by ring
  have h4 : u * (a + b) / 2 ≤ t := by
    have : u * (a + b + 1) = t := by
      show t / (a + b + 1) * (a + b + 1) = t
      field_simp
    nlinarith
  rw [e1, e2] at h
  linarith

/-- M6.A6 helper: a positive function with the log-Lipschitz bound `ρ τ' ≤ e^{4|τ-τ'|} ρ τ` is continuous. -/
theorem s07c_fkps_m6_loglip_cont {ρ : ℝ → ℝ} (hpos : ∀ τ, 0 < ρ τ)
    (hlip : ∀ τ τ' : ℝ, ρ τ' ≤ Real.exp (4 * |τ - τ'|) * ρ τ) : Continuous ρ := by
  rw [Metric.continuous_iff]
  intro τ η hη
  have hρ := hpos τ
  have hc : Continuous fun x : ℝ => (Real.exp (4 * |x|) - 1) * ρ τ := by fun_prop
  obtain ⟨d, hd, hd'⟩ := Metric.continuous_iff.1 hc 0 η hη
  refine ⟨d, hd, fun τ' hτ' => ?_⟩
  have hx := hd' (τ' - τ) (by rwa [Real.dist_eq, sub_zero, ← Real.dist_eq])
  simp only [abs_zero, mul_zero, Real.exp_zero, sub_self, zero_mul, Real.dist_eq, sub_zero] at hx
  have h1 := hlip τ τ'
  have h2 := hlip τ' τ
  have habs : |τ - τ'| = |τ' - τ| := abs_sub_comm _ _
  rw [habs] at h1
  set q := Real.exp (4 * |τ' - τ|)
  have hq1 : 1 ≤ q := Real.one_le_exp (by positivity)
  have hqi : q * ρ τ' ≥ ρ τ := by linarith
  rw [Real.dist_eq, abs_lt]
  have hx' : (q - 1) * ρ τ < η := lt_of_le_of_lt (le_abs_self _) hx
  constructor
  · -- ρ τ' ≥ ρ τ / q ≥ ρ τ - (q - 1) ρ τ
    have : ρ τ - (q - 1) * ρ τ ≤ ρ τ' := by
      have hq0 : 0 < q := by positivity
      have h3 : ρ τ ≤ q * ρ τ' := hqi
      nlinarith [hpos τ', mul_nonneg (sq_nonneg (q - 1)) hρ.le, hq0]
    linarith
  · linarith

/-- M6.A6 helper (the duality for one test function, A3 + A5 + the area mean value of the Poisson integral):
`|∫₀^{2π} v(e^{iτ}) ρ(τ) dτ - (2π)⁻¹ ∫₀^{2π} v(F(e^{it})) dt| ≤ C √ε (∫₀^{2π} v(F(e^{it}))² dt)^{1/2}`. -/
theorem s07c_fkps_m6_dual : ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧ ∀ (F : ℂ → ℂ) (a : ℂ → ℝ) (K ε : ℝ) (ρ : ℝ → ℝ),
    IsKQC F univ K → F '' univ = univ → F '' unitDisc = unitDisc → F 0 = 0 →
    Measurable a → (∀ z, 0 ≤ a z) → (∀ z ∈ unitDisc, a z ≤ ε₀) →
    (∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) →
      ‖LiZhongQC.complexDilatation F w‖ ≤ a z) →
    0 ≤ ε → ε ≤ ε₀ →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
        ≤ ENNReal.ofReal (ε * r)) →
    (∀ τ : ℝ, ρ τ = 8 / π ^ 2 *
      ∫ X in ball (0 : ℂ) (1 / 4), (1 - ‖F X‖ ^ 2) / ‖Complex.exp (τ * I) - F X‖ ^ 2) →
    ∀ v : ℂ → ℝ, ContDiff ℝ 2 v → InnerProductSpace.HarmonicOnNhd v univ →
      |(∫ τ in (0 : ℝ)..2 * π, v (Complex.exp (τ * I)) * ρ τ) -
          (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, v (F (Complex.exp (t * I)))| ≤
        C * Real.sqrt ε * Real.sqrt (∫ t in (0 : ℝ)..2 * π, v (F (Complex.exp (t * I))) ^ 2) := by
  obtain ⟨ε₃, C₃, hε₃, hC₃, hA3⟩ := s07c_fkps_m6_test
  obtain ⟨ε₅, C₅, hε₅, hC₅, hA5⟩ := s07c_fkps_m6_rho
  refine ⟨min ε₃ ε₅, Real.sqrt (16 * C₃ / π), lt_min hε₃ hε₅,
    Real.sqrt_pos.2 (by have := Real.pi_pos; positivity), ?_⟩
  intro F a K ε ρ hF hsurj hFD hF0 ha ha0 hale hW hε hεε hcarl hρ v hvc hvh
  have hπ : 0 < π := Real.pi_pos
  have hvD : InnerProductSpace.HarmonicOnNhd v unitDisc := fun z _ => hvh z (mem_univ z)
  have hrep := (hA5 F a K ε ρ hF hsurj hFD hF0 ha ha0 (fun z hz => (hale z hz).trans (min_le_right _ _)) hW hε
    (hεε.trans (min_le_right _ _)) hcarl hρ).2.2.2.2 v (fun z _ => hvh z (mem_univ z))
  have hL2 := hA3 F a K ε hF hsurj hFD hF0 ha ha0 (fun z hz => (hale z hz).trans (min_le_left _ _)) hW hε
    (hεε.trans (min_le_left _ _)) hcarl v hvc hvD
  have hFc : Continuous F := continuousOn_univ.mp hF.2.2.1.1
  have hv : Continuous v := hvc.continuous
  set f : ℝ → ℝ := fun t => v (F (Complex.exp (t * I))) with hf_def
  have hec : Continuous fun t : ℝ => Complex.exp (t * I) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hfc : Continuous f := hv.comp (hFc.comp hec)
  have hper : ∀ t, f (t + 2 * π) = f t := by
    intro t
    show v (F (Complex.exp (((t + 2 * π : ℝ) : ℂ) * I))) = v (F (Complex.exp (t * I)))
    have : (((t + 2 * π : ℝ) : ℂ) * I) = (t : ℂ) * I + 2 * π * I := by push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  set P : ℂ → ℝ := fun X => (2 * π)⁻¹ *
    ∫ t in (0 : ℝ)..2 * π, (1 - ‖X‖ ^ 2) / ‖Complex.exp (t * I) - X‖ ^ 2 * f t with hP_def
  have hPh : InnerProductSpace.HarmonicOnNhd P unitDisc := s07c_fkps_m2_poisson_harmonic f hfc hper
  have hP0 : P 0 = (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, f t := by
    show (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, (1 - ‖(0 : ℂ)‖ ^ 2) / ‖Complex.exp (t * I) - 0‖ ^ 2 * f t = _
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [norm_zero, sub_zero, Complex.norm_exp_ofReal_mul_I]
    norm_num
  have hvF : Continuous fun X => v (F X) := hv.comp hFc
  have hi1 : IntegrableOn (fun X => v (F X)) (ball (0 : ℂ) (1 / 4)) :=
    (hvF.continuousOn.integrableOn_compact (isCompact_closedBall 0 (1 / 4))).mono_set ball_subset_closedBall
  have hi2 : IntegrableOn P (ball (0 : ℂ) (1 / 4)) :=
    (((hPh.mono (closedBall_subset_ball (by norm_num))).continuousOn).integrableOn_compact
      (isCompact_closedBall 0 (1 / 4))).mono_set ball_subset_closedBall
  have hdec : ∫ X in ball (0 : ℂ) (1 / 4), v (F X) =
      π * (1 / 4) ^ 2 * P 0 + ∫ X in ball (0 : ℂ) (1 / 4), (v (F X) - P X) := by
    rw [integral_sub hi1 hi2, s07c_fkps_m6_area_mean hPh (by norm_num) (by norm_num)]
    ring
  set N := ∫ t in (0 : ℝ)..2 * π, f t ^ 2 with hN_def
  have hN0 : 0 ≤ N := intervalIntegral.integral_nonneg (by positivity) fun t _ => sq_nonneg _
  have hNe : ∫⁻ t in Icc 0 (2 * π), ‖v (F (Complex.exp (t * I)))‖ₑ ^ 2 = ENNReal.ofReal N := by
    have h1 : ∀ t : ℝ, ‖v (F (Complex.exp (t * I)))‖ₑ ^ 2 = ENNReal.ofReal (f t ^ 2) := by
      intro t
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [lintegral_congr h1, hN_def, intervalIntegral.integral_of_le (by positivity),
      ← integral_Icc_eq_integral_Ioc, ofReal_integral_eq_lintegral_ofReal]
    · exact (hfc.pow 2).integrableOn_Icc
    · exact ae_of_all _ fun t => sq_nonneg _
  rw [hNe, ← ENNReal.ofReal_mul (by positivity)] at hL2
  have hcs := s07c_fkps_m6_cs (w := fun X => v (F X) - P X) (by positivity) (by positivity)
    (s07c_fkps_m6_vol_ball (by norm_num : (0 : ℝ) ≤ 1 / 4)) hL2
  rw [← hrep, hdec, hP0]
  have e : 16 / π * (π * (1 / 4) ^ 2 * ((2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, f t) +
      ∫ X in ball (0 : ℂ) (1 / 4), (v (F X) - P X)) - (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, f t =
      16 / π * ∫ X in ball (0 : ℂ) (1 / 4), (v (F X) - P X) := by
    field_simp
    ring
  rw [e, abs_mul, abs_of_pos (by positivity)]
  have hfin : 16 / π * Real.sqrt (C₃ * ε * N * (π * (1 / 4) ^ 2)) =
      Real.sqrt (16 * C₃ / π) * Real.sqrt ε * Real.sqrt N := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    rw [show (16 / π : ℝ) = Real.sqrt ((16 / π) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
    ring
  calc 16 / π * |∫ X in ball (0 : ℂ) (1 / 4), (v (F X) - P X)|
      ≤ 16 / π * Real.sqrt (C₃ * ε * N * (π * (1 / 4) ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = _ := hfin

/-- M6.A6 helper (Urysohn bump on the circle): for `K` compact inside an open `U ⊆ (a, a + 2π)` there is a
continuous `Φ` on `ℝ/2πℤ` with `0 ≤ Φ ≤ 1`, `Φ = 1` on `K` and `Φ = 0` off `U` (read on `[a, a + 2π)`). -/
theorem s07c_fkps_m6_bump {K U : Set ℝ} {a : ℝ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUJ : U ⊆ Ioo a (a + 2 * π)) :
    ∃ Φ : C(AddCircle (2 * π), ℝ), ∀ τ ∈ Ico a (a + 2 * π),
      0 ≤ Φ (τ : AddCircle (2 * π)) ∧ Φ (τ : AddCircle (2 * π)) ≤ 1 ∧
        (τ ∈ K → Φ (τ : AddCircle (2 * π)) = 1) ∧ (τ ∉ U → Φ (τ : AddCircle (2 * π)) = 0) := by
  haveI : Fact (0 < 2 * π) := ⟨by have := Real.pi_pos; positivity⟩
  obtain ⟨g, hg1, hg0, -, hg01⟩ := exists_continuous_one_zero_of_isCompact hK hU.isClosed_compl
    (disjoint_compl_right_iff_subset.2 hKU)
  have ha : g a = 0 := hg0 (show a ∈ Uᶜ from fun h => lt_irrefl a (hUJ h).1)
  have hb : g (a + 2 * π) = 0 := hg0 (show a + 2 * π ∈ Uᶜ from fun h => lt_irrefl _ (hUJ h).2)
  refine ⟨⟨AddCircle.liftIco (2 * π) a g,
    AddCircle.liftIco_continuous (ha.trans hb.symm) g.continuous.continuousOn⟩, ?_⟩
  intro τ hτ
  have e : AddCircle.liftIco (2 * π) a g (τ : AddCircle (2 * π)) = g τ := AddCircle.liftIco_coe_apply hτ
  refine ⟨?_, ?_, fun h => ?_, fun h => ?_⟩ <;> simp only [ContinuousMap.coe_mk, e]
  · exact (hg01 τ).1
  · exact (hg01 τ).2
  · exact hg1 h
  · exact hg0 h

/-- M6.A6 helper (pointwise bookkeeping): `|g - φ| ≤ δ`, `0 ≤ φ ≤ 1`, `e, d ∈ {0, 1}`, and either `d = 1` or
`φ = e` give `|g - e| ≤ δ + d` and `g² ≤ e + d + 3δ` (`δ ≤ 1`). -/
theorem s07c_fkps_m6_pt {g φ e d δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hg : |g - φ| ≤ δ) (h0 : 0 ≤ φ)
    (h1 : φ ≤ 1) (he : e = 0 ∨ e = 1) (hd : d = 0 ∨ d = 1)
    (hc : d = 1 ∨ (e = 1 ∧ φ = 1) ∨ (e = 0 ∧ φ = 0)) :
    |g - e| ≤ δ + d ∧ g ^ 2 ≤ e + d + 3 * δ := by
  have hd0 : 0 ≤ d := by rcases hd with rfl | rfl <;> norm_num
  have he0 : 0 ≤ e ∧ e ≤ 1 := by rcases he with rfl | rfl <;> norm_num
  obtain ⟨hg1, hg2⟩ := abs_le.1 hg
  have hsq : g ^ 2 ≤ (φ + δ) ^ 2 := by
    have h3 : 0 ≤ φ + δ - g := by linarith
    have h4 : 0 ≤ φ + δ + g := by linarith
    nlinarith [mul_nonneg h3 h4]
  have hφδ : (φ + δ) ^ 2 ≤ φ + 3 * δ := by
    nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), mul_nonneg hδ0 (sub_nonneg.2 hδ1),
      mul_nonneg hδ0 (sub_nonneg.2 h1)]
  rcases hc with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, by linarith⟩
  · exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, by linarith⟩
  · exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, by linarith⟩

/-- M6.A6 helper: `∫_S 1_D = |D ∩ S|`. -/
theorem s07c_fkps_m6_int_ind {S D : Set ℝ} (hD : MeasurableSet D) :
    ∫ x in S, D.indicator (1 : ℝ → ℝ) x = volume.real (D ∩ S) := by
  rw [integral_indicator_one hD, measureReal_restrict_apply hD]

/-- M6.A6 helper: `1_D` is integrable on a set of finite measure. -/
theorem s07c_fkps_m6_ind_int {S D : Set ℝ} (hS : volume S ≠ ∞) (hD : MeasurableSet D) :
    IntegrableOn (D.indicator (1 : ℝ → ℝ)) S :=
  (integrableOn_const (C := (1 : ℝ)) hS).indicator hD

/-- M6.A6 helper: `|f| ≤ c (δ + 1_D)` on `S` gives `|∫_S f| ≤ c (δ |S| + |D ∩ S|)`. -/
theorem s07c_fkps_m6_int_bd {f : ℝ → ℝ} {S D : Set ℝ} {c δ : ℝ} (hS : MeasurableSet S) (hSf : volume S ≠ ∞)
    (hD : MeasurableSet D) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hpt : ∀ x ∈ S, |f x| ≤ c * (δ + D.indicator 1 x)) :
    |∫ x in S, f x| ≤ c * (δ * volume.real S + volume.real (D ∩ S)) := by
  have hi1 : IntegrableOn (fun _ => δ) S := integrableOn_const hSf
  have hi2 := s07c_fkps_m6_ind_int hSf hD
  have hi : IntegrableOn (fun x => c * (δ + D.indicator (1 : ℝ → ℝ) x)) S := (hi1.add hi2).const_mul c
  have h := norm_integral_le_of_norm_le hi (ae_restrict_of_forall_mem hS fun x hx => by
    rw [Real.norm_eq_abs]; exact hpt x hx)
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_add (f := fun _ => δ) (g := fun x => D.indicator (1 : ℝ → ℝ) x) hi1 hi2,
    setIntegral_const, s07c_fkps_m6_int_ind hD, smul_eq_mul, mul_comm (volume.real S)]

/-- M6.A6 helper (the measure step, pure real analysis): if `ρ` is continuous, bounded and `2π`-periodic, `H` is
a strictly increasing lift of a circle homeomorphism, and the duality bound holds for every harmonic test
function on `ℂ`, then `|∫_{H(A)} ρ - |A|/(2π)| ≤ C √ε √|A|` for measurable `A ⊆ (s, s + 2π)`. -/
theorem s07c_fkps_m6_meas_core {ρ H : ℝ → ℝ} {C ε M : ℝ} (hC : 0 ≤ C)
    (hρc : Continuous ρ) (hρM : ∀ τ, |ρ τ| ≤ M) (hρper : ∀ τ, ρ (τ + 2 * π) = ρ τ)
    (hHm : StrictMono H) (hHc : Continuous H) (hHper : ∀ θ, H (θ + 2 * π) = H θ + 2 * π)
    (hdual : ∀ v : ℂ → ℝ, ContDiff ℝ 2 v → InnerProductSpace.HarmonicOnNhd v univ →
      |(∫ τ in (0 : ℝ)..2 * π, v (Complex.exp (τ * I)) * ρ τ) -
          (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, v (Complex.exp (H t * I))| ≤
        C * Real.sqrt ε * Real.sqrt (∫ t in (0 : ℝ)..2 * π, v (Complex.exp (H t * I)) ^ 2))
    {s : ℝ} {A : Set ℝ} (hA : MeasurableSet A) (hAs : A ⊆ Ioo s (s + 2 * π)) :
    |(∫ τ in H '' A, ρ τ) - (volume A).toReal / (2 * π)| ≤
      C * Real.sqrt ε * Real.sqrt (volume A).toReal := by
  have hπ : 0 < π := Real.pi_pos
  have hM : 0 ≤ M := (abs_nonneg _).trans (hρM 0)
  set a := H s with ha_def
  set J := Ioo a (a + 2 * π) with hJ_def
  set W := Ioo s (s + 2 * π) with hW_def
  have hJm : MeasurableSet J := measurableSet_Ioo
  have hWm : MeasurableSet W := measurableSet_Ioo
  have hJf : volume J ≠ ∞ := by rw [hJ_def, Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hWf : volume W ≠ ∞ := by rw [hW_def, Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hJr : volume.real J = 2 * π := by rw [hJ_def, Real.volume_real_Ioo_of_le (by linarith)]; ring
  have hWr : volume.real W = 2 * π := by rw [hW_def, Real.volume_real_Ioo_of_le (by linarith)]; ring
  have hec : Continuous fun τ : ℝ => Complex.exp (τ * I) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hep : ∀ τ : ℝ, Complex.exp (((τ + 2 * π : ℝ) : ℂ) * I) = Complex.exp (τ * I) := by
    intro τ
    rw [show ((τ + 2 * π : ℝ) : ℂ) * I = (τ : ℂ) * I + 2 * π * I by push_cast; ring, Complex.exp_add,
      Complex.exp_two_pi_mul_I, mul_one]
  have hwin : ∀ f : ℝ → ℝ, (∀ t, f (t + 2 * π) = f t) → ∀ c : ℝ,
      ∫ t in (0 : ℝ)..2 * π, f t = ∫ t in Ioo c (c + 2 * π), f t := by
    intro f hf c
    have h := Function.Periodic.intervalIntegral_add_eq (T := 2 * π) hf 0 c
    rw [zero_add] at h
    rw [h, intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  -- the duality on the windows `J` and `W`
  have hdualW : ∀ v : ℂ → ℝ, ContDiff ℝ 2 v → InnerProductSpace.HarmonicOnNhd v univ →
      |(∫ τ in J, v (Complex.exp (τ * I)) * ρ τ) - (2 * π)⁻¹ * ∫ t in W, v (Complex.exp (H t * I))| ≤
        C * Real.sqrt ε * Real.sqrt (∫ t in W, v (Complex.exp (H t * I)) ^ 2) := by
    intro v hv hvh
    have h := hdual v hv hvh
    have hp1 : ∀ t : ℝ, v (Complex.exp (((t + 2 * π : ℝ) : ℂ) * I)) * ρ (t + 2 * π) =
        v (Complex.exp (t * I)) * ρ t := by
      intro t; rw [hep, hρper]
    have hp2 : ∀ t : ℝ, v (Complex.exp ((H (t + 2 * π) : ℂ) * I)) = v (Complex.exp (H t * I)) := by
      intro t; rw [hHper, hep]
    have hp3 : ∀ t : ℝ, v (Complex.exp ((H (t + 2 * π) : ℂ) * I)) ^ 2 = v (Complex.exp (H t * I)) ^ 2 := by
      intro t; rw [hp2]
    have e1 := hwin (fun t => v (Complex.exp (t * I)) * ρ t) hp1 a
    have e2 := hwin (fun t => v (Complex.exp (H t * I))) hp2 s
    have e3 := hwin (fun t => v (Complex.exp (H t * I)) ^ 2) hp3 s
    rw [e1, e2, e3] at h
    exact h
  -- the image set
  set E := H '' A with hE_def
  have hEm : MeasurableSet E := hA.image_of_continuousOn_injOn hHc.continuousOn hHm.injective.injOn
  have hWJ : ∀ θ ∈ W, H θ ∈ J := fun θ h => ⟨hHm h.1, (hHm h.2).trans_eq (hHper s)⟩
  have hEJ : E ⊆ J := by
    rintro _ ⟨θ, hθ, rfl⟩
    exact hWJ θ (hAs hθ)
  have hAE : ∀ θ, θ ∈ A ↔ H θ ∈ E := by
    intro θ
    refine ⟨fun h => mem_image_of_mem H h, fun h => ?_⟩
    obtain ⟨θ', h', he⟩ := h
    rwa [← hHm.injective he]
  have hAr : (volume A).toReal = volume.real (A ∩ W) := by
    rw [inter_eq_self_of_subset_left hAs, measureReal_def]
  -- the estimate at scale `δ`
  set B := M * (2 * π + 2) + 2 with hB
  have key : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      |(∫ τ in E, ρ τ) - (volume A).toReal / (2 * π)| ≤
        C * Real.sqrt ε * Real.sqrt ((volume A).toReal + (2 + 6 * π) * δ) + B * δ := by
    intro δ hδ hδ1
    set ν : Measure ℝ := volume.restrict J + Measure.map H (volume.restrict W) with hν
    haveI : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.2 hJf
    haveI : IsFiniteMeasure (volume.restrict W) := isFiniteMeasure_restrict.2 hWf
    haveI : IsFiniteMeasure ν := by rw [hν]; infer_instance
    have hδ' : ENNReal.ofReal δ ≠ 0 := (ENNReal.ofReal_pos.2 hδ).ne'
    obtain ⟨K, hKE, hKc, hK⟩ := hEm.exists_isClosed_diff_lt (μ := ν) (measure_ne_top ν E) hδ'
    obtain ⟨U, hUE, hUo, -, hU⟩ := hEm.exists_isOpen_diff_lt (μ := ν) (measure_ne_top ν E) hδ'
    set U' := U ∩ J with hU'_def
    set D := U' \ K with hD_def
    have hU'o : IsOpen U' := hUo.inter isOpen_Ioo
    have hDm : MeasurableSet D := hU'o.measurableSet.diff hKc.measurableSet
    have hKU : K ⊆ U' := fun x hx => ⟨hUE (hKE hx), hEJ (hKE hx)⟩
    have hKcpt : IsCompact K :=
      (isCompact_Icc (a := a) (b := a + 2 * π)).of_isClosed_subset hKc
        (fun x hx => Ioo_subset_Icc_self (hEJ (hKE hx)))
    have hνD : ν D ≤ ENNReal.ofReal (2 * δ) := by
      have hsub : D ⊆ (U \ E) ∪ (E \ K) := by
        intro x hx
        by_cases h : x ∈ E
        · exact Or.inr ⟨h, hx.2⟩
        · exact Or.inl ⟨hx.1.1, h⟩
      calc ν D ≤ ν ((U \ E) ∪ (E \ K)) := measure_mono hsub
        _ ≤ ν (U \ E) + ν (E \ K) := measure_union_le _ _
        _ ≤ ENNReal.ofReal δ + ENNReal.ofReal δ := add_le_add hU.le hK.le
        _ = ENNReal.ofReal (2 * δ) := by rw [← ENNReal.ofReal_add hδ.le hδ.le]; ring_nf
    have hνD' : ν D = volume (D ∩ J) + volume (H ⁻¹' D ∩ W) := by
      rw [hν, Measure.add_apply, Measure.restrict_apply hDm, Measure.map_apply hHc.measurable hDm,
        Measure.restrict_apply (hHc.measurable hDm)]
    have hDJ : volume.real (D ∩ J) ≤ 2 * δ := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) (le_self_add.trans (by rw [← hνD']; exact hνD))
    have hDW : volume.real (H ⁻¹' D ∩ W) ≤ 2 * δ := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) (le_add_self.trans (by rw [← hνD']; exact hνD))
    -- the bump and its trigonometric approximation
    obtain ⟨Φ, hΦ⟩ := s07c_fkps_m6_bump hKcpt hU'o hKU inter_subset_right
    obtain ⟨v, hvc, hvh, hvΦ⟩ := s07c_fkps_m6_trig_approx Φ hδ
    set g : ℝ → ℝ := fun τ => v (Complex.exp (τ * I)) with hg_def
    have hgc : Continuous g := hvc.continuous.comp hec
    have hptJ : ∀ τ ∈ J, |g τ - E.indicator 1 τ| ≤ δ + D.indicator 1 τ ∧
        g τ ^ 2 ≤ E.indicator 1 τ + D.indicator 1 τ + 3 * δ := by
      intro τ hτ
      obtain ⟨h0, h1, hK1, hU0⟩ := hΦ τ (Ioo_subset_Ico_self hτ)
      refine s07c_fkps_m6_pt hδ.le hδ1 (hvΦ τ) h0 h1 ?_ ?_ ?_
      · by_cases h : τ ∈ E
        · right; exact Set.indicator_of_mem h _
        · left; exact Set.indicator_of_notMem h _
      · by_cases h : τ ∈ D
        · right; exact Set.indicator_of_mem h _
        · left; exact Set.indicator_of_notMem h _
      · by_cases hD : τ ∈ D
        · left; exact Set.indicator_of_mem hD _
        · right
          by_cases hk : τ ∈ K
          · left; exact ⟨Set.indicator_of_mem (hKE hk) _, hK1 hk⟩
          · right
            have hu : τ ∉ U' := fun hu => hD ⟨hu, hk⟩
            have he : τ ∉ E := fun he => hu ⟨hUE he, hτ⟩
            exact ⟨Set.indicator_of_notMem he _, hU0 hu⟩
    have hptW : ∀ θ ∈ W, |g (H θ) - A.indicator 1 θ| ≤ δ + (H ⁻¹' D).indicator 1 θ ∧
        g (H θ) ^ 2 ≤ A.indicator 1 θ + (H ⁻¹' D).indicator 1 θ + 3 * δ := by
      intro θ hθ
      have e1 : A.indicator (1 : ℝ → ℝ) θ = E.indicator 1 (H θ) := by
        by_cases h : θ ∈ A
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hAE θ).1 h)]; rfl
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hAE θ).2 h'))]
      have e2 : (H ⁻¹' D).indicator (1 : ℝ → ℝ) θ = D.indicator 1 (H θ) := by
        by_cases h : H θ ∈ D
        · rw [Set.indicator_of_mem (show θ ∈ H ⁻¹' D from h), Set.indicator_of_mem h]; rfl
        · rw [Set.indicator_of_notMem (show θ ∉ H ⁻¹' D from h), Set.indicator_of_notMem h]
      rw [e1, e2]
      exact hptJ (H θ) (hWJ θ hθ)
    -- (i) the `ρ` side
    have hρi : IntegrableOn ρ J := hρc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    have hgρi : IntegrableOn (fun τ => g τ * ρ τ) J :=
      (hgc.mul hρc).integrableOn_Icc.mono_set Ioo_subset_Icc_self
    have hX : ∫ τ in E, ρ τ = ∫ τ in J, E.indicator ρ τ := by
      rw [setIntegral_indicator hEm, inter_eq_self_of_subset_right hEJ]
    have h1 : |(∫ τ in E, ρ τ) - ∫ τ in J, g τ * ρ τ| ≤ M * (δ * (2 * π) + 2 * δ) := by
      rw [hX, ← integral_sub (hρi.indicator hEm) hgρi]
      refine (s07c_fkps_m6_int_bd hJm hJf hDm hM hδ.le fun τ hτ => ?_).trans ?_
      · have e : E.indicator ρ τ - g τ * ρ τ = (E.indicator 1 τ - g τ) * ρ τ := by
          by_cases h : τ ∈ E
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply]; ring
          · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; ring
        rw [e, abs_mul, abs_sub_comm]
        have hnn : 0 ≤ δ + D.indicator (1 : ℝ → ℝ) τ :=
          add_nonneg hδ.le (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
        exact (mul_le_mul (hptJ τ hτ).1 (hρM τ) (abs_nonneg _) hnn).trans_eq (mul_comm _ _)
      · rw [hJr]
        exact mul_le_mul_of_nonneg_left (by linarith) hM
    -- (ii) the `|A|` side
    have hgHc : Continuous fun θ => g (H θ) := hgc.comp hHc
    have hgHi : IntegrableOn (fun θ => g (H θ)) W := hgHc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    have hAi := s07c_fkps_m6_ind_int hWf hA
    have hDi := s07c_fkps_m6_ind_int hWf (hHc.measurable hDm)
    have hY : (volume A).toReal / (2 * π) = (2 * π)⁻¹ * ∫ θ in W, A.indicator 1 θ := by
      rw [s07c_fkps_m6_int_ind hA, ← hAr]; ring
    have hsubI : ∫ θ in W, (g (H θ) - A.indicator 1 θ) =
        (∫ θ in W, g (H θ)) - ∫ θ in W, A.indicator 1 θ := integral_sub hgHi hAi
    have h2 : |(2 * π)⁻¹ * (∫ θ in W, g (H θ)) - (volume A).toReal / (2 * π)| ≤
        (2 * π)⁻¹ * (δ * (2 * π) + 2 * δ) := by
      rw [hY, ← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹), ← hsubI]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine (s07c_fkps_m6_int_bd hWm hWf (hHc.measurable hDm) zero_le_one hδ.le fun θ hθ => ?_).trans ?_
      · rw [one_mul]; exact (hptW θ hθ).1
      · rw [hWr, one_mul]; linarith [hDW]
    -- (iii) the `L²` norm
    have h3 : ∫ θ in W, g (H θ) ^ 2 ≤ (volume A).toReal + (2 + 6 * π) * δ := by
      have hmono : ∫ θ in W, g (H θ) ^ 2 ≤
          ∫ θ in W, (A.indicator 1 θ + (H ⁻¹' D).indicator 1 θ + 3 * δ) :=
        setIntegral_mono_on ((hgHc.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
          ((hAi.add hDi).add (integrableOn_const hWf)) hWm (fun θ hθ => (hptW θ hθ).2)
      rw [integral_add (f := fun θ => A.indicator (1 : ℝ → ℝ) θ + (H ⁻¹' D).indicator 1 θ)
          (g := fun _ => 3 * δ) (hAi.add hDi) (integrableOn_const hWf),
        integral_add (f := fun θ => A.indicator (1 : ℝ → ℝ) θ) (g := fun θ => (H ⁻¹' D).indicator 1 θ) hAi hDi,
        s07c_fkps_m6_int_ind hA, s07c_fkps_m6_int_ind (hHc.measurable hDm), setIntegral_const, smul_eq_mul,
        hWr, ← hAr] at hmono
      linarith [hDW]
    -- (iv) the duality and the triangle inequality
    have hd : |(∫ τ in J, g τ * ρ τ) - (2 * π)⁻¹ * ∫ t in W, g (H t)| ≤
        C * Real.sqrt ε * Real.sqrt (∫ t in W, g (H t) ^ 2) := hdualW v hvc hvh
    have hCε : 0 ≤ C * Real.sqrt ε := mul_nonneg hC (Real.sqrt_nonneg _)
    have h4 := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h3) hCε
    have h5 : (2 * π)⁻¹ * (δ * (2 * π) + 2 * δ) ≤ 2 * δ := by
      have e : (2 * π)⁻¹ * (δ * (2 * π) + 2 * δ) = δ + δ / π := by field_simp
      rw [e]
      have : δ / π ≤ δ := div_le_self hδ.le (by linarith [Real.pi_gt_three])
      linarith
    have htri := abs_sub_le (∫ τ in E, ρ τ) (∫ τ in J, g τ * ρ τ) ((volume A).toReal / (2 * π))
    have htri2 := abs_sub_le (∫ τ in J, g τ * ρ τ) ((2 * π)⁻¹ * ∫ t in W, g (H t))
      ((volume A).toReal / (2 * π))
    have hB' : M * (δ * (2 * π) + 2 * δ) + 2 * δ = B * δ := by rw [hB]; ring
    linarith
  -- `δ → 0`
  set φ : ℝ → ℝ := fun δ => C * Real.sqrt ε * Real.sqrt ((volume A).toReal + (2 + 6 * π) * δ) + B * δ
    with hφ
  have hφc : Continuous φ :=
    (continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.add
      (continuous_const.mul continuous_id)))).add (continuous_const.mul continuous_id)
  have h0 : φ 0 = C * Real.sqrt ε * Real.sqrt (volume A).toReal := by
    show C * Real.sqrt ε * Real.sqrt ((volume A).toReal + (2 + 6 * π) * 0) + B * 0 = _
    rw [mul_zero, add_zero, mul_zero, add_zero]
  rw [← h0]
  refine ge_of_tendsto ((hφc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
  exact key δ hδ.1 hδ.2.le

/-- M6.A6 (measure form of the duality): `m(A) = ∫_{H(A)} ρ` satisfies `|m(A) - |A|/(2π)| ≤ C √ε √|A|` for every
measurable `A` inside one period. Route: A3 + A5 give `|∫ ψ dm - ⨍ ψ| ≤ C √ε ‖ψ‖₂` for `ψ = φ ∘ H`, `φ` a real
trigonometric polynomial (boundary values of `Re p`, `p` a complex polynomial); these are dense in `L²(dθ + m)`
(continuous functions are dense; trigonometric polynomials are uniformly dense in `C(𝕋)`). -/
theorem s07c_fkps_m6_meas : ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧
    ∀ (F : ℂ → ℂ) (a : ℂ → ℝ) (K ε : ℝ) (H ρ : ℝ → ℝ),
    IsKQC F univ K → F '' univ = univ → F '' unitDisc = unitDisc → F 0 = 0 →
    Measurable a → (∀ z, 0 ≤ a z) → (∀ z ∈ unitDisc, a z ≤ ε₀) →
    (∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) →
      ‖LiZhongQC.complexDilatation F w‖ ≤ a z) →
    0 ≤ ε → ε ≤ ε₀ →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
        ≤ ENNReal.ofReal (ε * r)) →
    StrictMono H → Continuous H → (∀ θ : ℝ, H (θ + 2 * π) = H θ + 2 * π) →
    (∀ θ : ℝ, F (Complex.exp (θ * Complex.I)) = Complex.exp (H θ * Complex.I)) →
    (∀ τ : ℝ, ρ τ = 8 / π ^ 2 *
      ∫ X in ball (0 : ℂ) (1 / 4), (1 - ‖F X‖ ^ 2) / ‖Complex.exp (τ * I) - F X‖ ^ 2) →
    ∀ (s : ℝ) (A : Set ℝ), MeasurableSet A → A ⊆ Icc s (s + 2 * π) →
      |(∫ τ in H '' A, ρ τ) - (volume A).toReal / (2 * π)| ≤
        C * Real.sqrt ε * Real.sqrt (volume A).toReal := by
  obtain ⟨ε₁, C₁, hε₁, hC₁, hdual⟩ := s07c_fkps_m6_dual
  obtain ⟨ε₅, C₅, hε₅, hC₅, hA5⟩ := s07c_fkps_m6_rho
  refine ⟨min ε₁ ε₅, C₁, lt_min hε₁ hε₅, hC₁, ?_⟩
  intro F a K ε H ρ hF hsurj hFD hF0 ha ha0 hale hW hε hεε hcarl hHm hHc hHper hFH hρ s A hA hAs
  have hπ : 0 < π := Real.pi_pos
  obtain ⟨hpos, hper, hlip, hbd, -⟩ := hA5 F a K ε ρ hF hsurj hFD hF0 ha ha0
    (fun z hz => (hale z hz).trans (min_le_right _ _)) hW hε (hεε.trans (min_le_right _ _)) hcarl hρ
  have hρc : Continuous ρ := s07c_fkps_m6_loglip_cont hpos hlip
  have hρM : ∀ τ, |ρ τ| ≤ (1 + C₅ * ε ^ (1 / 6 : ℝ)) / (2 * π) := by
    intro τ
    rw [abs_of_pos (hpos τ), le_div_iff₀ (by positivity)]
    have := (abs_le.1 (hbd τ)).2
    linarith
  have hd : ∀ v : ℂ → ℝ, ContDiff ℝ 2 v → InnerProductSpace.HarmonicOnNhd v univ →
      |(∫ τ in (0 : ℝ)..2 * π, v (Complex.exp (τ * I)) * ρ τ) -
          (2 * π)⁻¹ * ∫ t in (0 : ℝ)..2 * π, v (Complex.exp (H t * I))| ≤
        C₁ * Real.sqrt ε * Real.sqrt (∫ t in (0 : ℝ)..2 * π, v (Complex.exp (H t * I)) ^ 2) := by
    intro v hv hvh
    have h := hdual F a K ε ρ hF hsurj hFD hF0 ha ha0 (fun z hz => (hale z hz).trans (min_le_left _ _)) hW hε
      (hεε.trans (min_le_left _ _)) hcarl hρ v hv hvh
    simp only [hFH] at h
    exact h
  -- reduce to the open window `(s, s + 2π)` (the endpoints are null on both sides)
  set A' := A ∩ Ioo s (s + 2 * π) with hA'_def
  have hA'm : MeasurableSet A' := hA.inter measurableSet_Ioo
  have hvol : volume A' = volume A := by
    refine measure_congr ?_
    have h0 : A =ᵐ[volume] A := Filter.EventuallyEq.rfl
    have h1 : A' =ᵐ[volume] A ∩ Icc s (s + 2 * π) := h0.inter (Ioo_ae_eq_Icc (μ := volume))
    rwa [inter_eq_self_of_subset_left hAs] at h1
  have himg : (H '' A') =ᵐ[volume] (H '' A) := by
    rw [ae_eq_set]
    constructor
    · rw [sdiff_eq_empty.2 (image_mono inter_subset_left), measure_empty]
    · refine measure_mono_null (t := {H s, H (s + 2 * π)}) ?_ ((Set.toFinite _).measure_zero _)
      rintro _ ⟨⟨θ, hθ, rfl⟩, hn⟩
      have hθ' := hAs hθ
      by_cases h1 : θ = s
      · exact Or.inl (congrArg H h1)
      by_cases h2 : θ = s + 2 * π
      · exact Or.inr (congrArg H h2)
      exact absurd ⟨θ, ⟨hθ, lt_of_le_of_ne hθ'.1 (Ne.symm h1), lt_of_le_of_ne hθ'.2 h2⟩, rfl⟩ hn
  have hcore := s07c_fkps_m6_meas_core hC₁.le hρc hρM hper hHm hHc hHper hd hA'm
    (inter_subset_right : A' ⊆ Ioo s (s + 2 * π))
  rw [setIntegral_congr_set himg, hvol] at hcore
  exact hcore

/-- M6.A7 helper: a continuous lift `H` with `H(θ + 2π) = H θ + 2π` is surjective (`H θ - θ` is periodic, hence
bounded). -/
theorem s07c_fkps_m6_lift_surj {H : ℝ → ℝ} (hHc : Continuous H)
    (hHper : ∀ θ, H (θ + 2 * π) = H θ + 2 * π) : Function.Surjective H := by
  have hp : Function.Periodic (fun θ => H θ - θ) (2 * π) := by
    intro θ
    show H (θ + 2 * π) - (θ + 2 * π) = H θ - θ
    rw [hHper]; ring
  obtain ⟨R, hR⟩ := (hp.compact_of_continuous (by have := Real.pi_pos; positivity : (0 : ℝ) < 2 * π).ne'
    (hHc.sub continuous_id)).isBounded.exists_norm_le
  have hb : ∀ θ, |H θ - θ| ≤ R := fun θ => by
    have := hR _ ⟨θ, rfl⟩
    rwa [Real.norm_eq_abs] at this
  refine hHc.surjective (tendsto_atTop_atTop.2 fun b => ⟨b + R, fun θ hθ => ?_⟩)
    (tendsto_atBot_atBot.2 fun b => ⟨b - R, fun θ hθ => ?_⟩)
  · linarith [(abs_le.1 (hb θ)).1]
  · linarith [(abs_le.1 (hb θ)).2]

/-- M6.A7 helper: a continuous bounded `ρ ≥ c` has `c |S| ≤ ∫_S ρ` on a set of finite measure. -/
theorem s07c_fkps_m6_int_low {ρ : ℝ → ℝ} (hρc : Continuous ρ) {c M : ℝ} (hlow : ∀ τ, c ≤ ρ τ)
    (hM : ∀ τ, |ρ τ| ≤ M) {S : Set ℝ} (hS : MeasurableSet S) (hSf : volume S ≠ ∞) :
    c * volume.real S ≤ ∫ τ in S, ρ τ := by
  have hi : IntegrableOn ρ S := Measure.integrableOn_of_bounded hSf hρc.aestronglyMeasurable
    (ae_of_all _ fun τ => by rw [Real.norm_eq_abs]; exact hM τ)
  have h := setIntegral_mono_on (integrableOn_const hSf) hi hS (fun τ _ => hlow τ)
  rwa [setIntegral_const, smul_eq_mul, mul_comm] at h

/-- M6.A (block output, the global step): `H` is absolutely continuous with density `u ≥ 0`, and with the
averaged harmonic density `ρ` (positive, periodic, log-Lipschitz, `ρ ≈ 1/(2π)`) the defect `2π ρ(H) u - 1` has
`∫_A |2π ρ(H) u - 1| ≤ C √ε √|A|` on every measurable `A` inside one period. -/
theorem s07c_fkps_m6_global : ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧
    ∀ (F : ℂ → ℂ) (a : ℂ → ℝ) (K ε : ℝ) (H : ℝ → ℝ),
    IsKQC F univ K → F '' univ = univ → F '' unitDisc = unitDisc → F 0 = 0 →
    Measurable a → (∀ z, 0 ≤ a z) → (∀ z ∈ unitDisc, a z ≤ ε₀) →
    (∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) →
      ‖LiZhongQC.complexDilatation F w‖ ≤ a z) →
    0 ≤ ε → ε ≤ ε₀ →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
        ≤ ENNReal.ofReal (ε * r)) →
    StrictMono H → Continuous H → (∀ θ : ℝ, H (θ + 2 * π) = H θ + 2 * π) →
    (∀ θ : ℝ, F (Complex.exp (θ * Complex.I)) = Complex.exp (H θ * Complex.I)) →
    ∃ u ρ : ℝ → ℝ, (∀ a b : ℝ, IntegrableOn u (Icc a b)) ∧
      (∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t) ∧ (∀ t : ℝ, 0 ≤ u t) ∧
      (∀ τ : ℝ, 0 < ρ τ) ∧ (∀ τ : ℝ, ρ (τ + 2 * π) = ρ τ) ∧
      (∀ τ τ' : ℝ, ρ τ' ≤ Real.exp (4 * |τ - τ'|) * ρ τ) ∧
      (∀ τ : ℝ, |2 * π * ρ τ - 1| ≤ C * ε ^ (1 / 6 : ℝ)) ∧
      ∀ (s : ℝ) (A : Set ℝ), MeasurableSet A → A ⊆ Icc s (s + 2 * π) →
        ∫ t in A, |2 * π * ρ (H t) * u t - 1| ≤ C * Real.sqrt ε * Real.sqrt (volume A).toReal := by
  obtain ⟨ε₆, C₆, hε₆, hC₆, hA6⟩ := s07c_fkps_m6_meas
  obtain ⟨ε₅, C₅, hε₅, hC₅, hA5⟩ := s07c_fkps_m6_rho
  have hπ : 0 < π := Real.pi_pos
  refine ⟨min (min ε₆ ε₅) (((2 * C₅)⁻¹) ^ 6), max C₅ (4 * π * C₆),
    lt_min (lt_min hε₆ hε₅) (by positivity), lt_max_of_lt_left hC₅, ?_⟩
  intro F a K ε H hF hsurj hFD hF0 ha ha0 hale hW hε hεε hcarl hHm hHc hHper hFH
  have hale6 : ∀ z ∈ unitDisc, a z ≤ ε₆ := fun z hz =>
    (hale z hz).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hale5 : ∀ z ∈ unitDisc, a z ≤ ε₅ := fun z hz =>
    (hale z hz).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε6 : ε ≤ ε₆ := hεε.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hε5 : ε ≤ ε₅ := hεε.trans ((min_le_left _ _).trans (min_le_right _ _))
  set ρ : ℝ → ℝ := fun τ => 8 / π ^ 2 *
    ∫ X in ball (0 : ℂ) (1 / 4), (1 - ‖F X‖ ^ 2) / ‖Complex.exp (τ * I) - F X‖ ^ 2 with hρ_def
  have hρ : ∀ τ : ℝ, ρ τ = 8 / π ^ 2 *
      ∫ X in ball (0 : ℂ) (1 / 4), (1 - ‖F X‖ ^ 2) / ‖Complex.exp (τ * I) - F X‖ ^ 2 := fun τ => rfl
  obtain ⟨hpos, hper, hlip, hbd, -⟩ := hA5 F a K ε ρ hF hsurj hFD hF0 ha ha0 hale5 hW hε hε5 hcarl hρ
  have hρc : Continuous ρ := s07c_fkps_m6_loglip_cont hpos hlip
  have hmeas : ∀ (s : ℝ) (A : Set ℝ), MeasurableSet A → A ⊆ Icc s (s + 2 * π) →
      |(∫ τ in H '' A, ρ τ) - (volume A).toReal / (2 * π)| ≤
        C₆ * Real.sqrt ε * Real.sqrt (volume A).toReal := fun s A hA hAs =>
    hA6 F a K ε H ρ hF hsurj hFD hF0 ha ha0 hale6 hW hε hε6 hcarl hHm hHc hHper hFH hρ s A hA hAs
  -- `ρ` is pinched between `1/(4π)` and `1`
  have hsmall : C₅ * ε ^ (1 / 6 : ℝ) ≤ 1 / 2 := by
    have h1 : ε ^ (1 / 6 : ℝ) ≤ (2 * C₅)⁻¹ := by
      have h2 : ε ≤ ((2 * C₅)⁻¹) ^ 6 := hεε.trans (min_le_right _ _)
      calc ε ^ (1 / 6 : ℝ) ≤ (((2 * C₅)⁻¹) ^ 6) ^ (1 / 6 : ℝ) := Real.rpow_le_rpow hε h2 (by norm_num)
        _ = (2 * C₅)⁻¹ := by
          rw [show (1 / 6 : ℝ) = ((6 : ℕ) : ℝ)⁻¹ by norm_num]
          exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
    calc C₅ * ε ^ (1 / 6 : ℝ) ≤ C₅ * (2 * C₅)⁻¹ := mul_le_mul_of_nonneg_left h1 hC₅.le
      _ = 1 / 2 := by field_simp
  have hρlow : ∀ τ, (4 * π)⁻¹ ≤ ρ τ := by
    intro τ
    have h1 := (abs_le.1 (hbd τ)).1
    rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
    have e : ρ τ * (4 * π) = 2 * (2 * π * ρ τ) := by ring
    rw [e]
    linarith
  have hρM : ∀ τ, |ρ τ| ≤ 1 := by
    intro τ
    rw [abs_of_pos (hpos τ)]
    have h1 := (abs_le.1 (hbd τ)).2
    nlinarith [mul_pos (sub_pos.2 Real.pi_gt_three) (hpos τ)]
  -- the Stieltjes measure of `H` pushes forward to Lebesgue measure
  have hHs := s07c_fkps_m6_lift_surj hHc hHper
  set Hs : StieltjesFunction ℝ := ⟨H, hHm.monotone, fun x => hHc.continuousWithinAt⟩ with hHs_def
  set μ : Measure ℝ := Hs.measure with hμ_def
  have hμIoc : ∀ x y, μ (Ioc x y) = ENNReal.ofReal (H y - H x) := fun x y => Hs.measure_Ioc x y
  have hpre : ∀ x y, H ⁻¹' Ioc (H x) (H y) = Ioc x y := by
    intro x y
    ext t
    simp only [mem_preimage, mem_Ioc, hHm.lt_iff_lt, hHm.le_iff_le]
  have hmap : Measure.map H μ = volume := by
    refine (Measure.ext_of_Ioc volume (Measure.map H μ) fun c d _ => ?_).symm
    obtain ⟨x, rfl⟩ := hHs c
    obtain ⟨y, rfl⟩ := hHs d
    rw [Measure.map_apply hHc.measurable measurableSet_Ioc, hpre, hμIoc, Real.volume_Ioc]
  have hHim : ∀ B : Set ℝ, MeasurableSet B → μ B = volume (H '' B) := by
    intro B hB
    rw [← hmap, Measure.map_apply hHc.measurable
      (hB.image_of_continuousOn_injOn hHc.continuousOn hHm.injective.injOn), preimage_image_eq _ hHm.injective]
  -- absolute continuity (A6 on null sets, one period at a time)
  have hac : μ ≪ volume := by
    refine Measure.AbsolutelyContinuous.mk fun N hN hN0 => ?_
    rw [hHim N hN]
    have hcov : H '' N ⊆ ⋃ n : ℤ, H '' (N ∩ Ico (2 * π * n) (2 * π * n + 2 * π)) := by
      rintro _ ⟨t, ht, rfl⟩
      refine mem_iUnion.2 ⟨⌊t / (2 * π)⌋, t, ⟨ht, ?_, ?_⟩, rfl⟩
      · have := Int.floor_le (t / (2 * π))
        rw [le_div_iff₀ (by positivity)] at this
        linarith
      · have := Int.lt_floor_add_one (t / (2 * π))
        rw [div_lt_iff₀ (by positivity)] at this
        linarith
    refine measure_mono_null hcov (measure_iUnion_null fun n => ?_)
    have hAnm : MeasurableSet (N ∩ Ico (2 * π * n) (2 * π * n + 2 * π)) := hN.inter measurableSet_Ico
    have hAn0 : volume (N ∩ Ico (2 * π * n) (2 * π * n + 2 * π)) = 0 := measure_mono_null inter_subset_left hN0
    have h6 := hmeas (2 * π * n) _ hAnm (inter_subset_right.trans Ico_subset_Icc_self)
    rw [hAn0, ENNReal.toReal_zero, zero_div, sub_zero, Real.sqrt_zero, mul_zero] at h6
    have hI0 := abs_nonpos_iff.1 h6
    have hfin : volume (H '' (N ∩ Ico (2 * π * n) (2 * π * n + 2 * π))) ≠ ∞ := by
      refine ne_top_of_le_ne_top (measure_Icc_lt_top (a := H (2 * π * n)) (b := H (2 * π * n + 2 * π))).ne
        (measure_mono ?_)
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨hHm.monotone ht.2.1, hHm.monotone ht.2.2.le⟩
    have hlow := s07c_fkps_m6_int_low hρc hρlow hρM
      (hAnm.image_of_continuousOn_injOn hHc.continuousOn hHm.injective.injOn) hfin
    rw [hI0] at hlow
    have h0 : volume.real (H '' (N ∩ Ico (2 * π * n) (2 * π * n + 2 * π))) = 0 :=
      le_antisymm (le_of_mul_le_mul_left (by rw [mul_zero]; exact hlow) (by positivity)) measureReal_nonneg
    exact (measureReal_eq_zero_iff hfin).1 h0
  -- the density `u` (Radon–Nikodym)
  set r := μ.rnDeriv volume with hr_def
  have hrm : Measurable r := Measure.measurable_rnDeriv μ volume
  have hwd : volume.withDensity r = μ := Measure.withDensity_rnDeriv_eq μ volume hac
  have hrfin : ∀ᵐ t ∂volume, r t < ∞ := Measure.rnDeriv_lt_top μ volume
  have hlint : ∀ S : Set ℝ, ∫⁻ t in S, r t = μ S := fun S => Measure.setLIntegral_rnDeriv hac S
  set u : ℝ → ℝ := fun t => (r t).toReal with hu_def
  have hum : Measurable u := hrm.ennreal_toReal
  have hu0 : ∀ t, 0 ≤ u t := fun t => ENNReal.toReal_nonneg
  have huI : ∀ x y : ℝ, IntegrableOn u (Icc x y) := fun x y =>
    integrable_toReal_of_lintegral_ne_top hrm.aemeasurable (by rw [hlint]; exact measure_Icc_lt_top.ne)
  have huIoc : ∀ x y : ℝ, ENNReal.ofReal (∫ t in Ioc x y, u t) = ENNReal.ofReal (H y - H x) := by
    intro x y
    rw [ofReal_integral_eq_lintegral_ofReal ((huI x y).mono_set Ioc_subset_Icc_self) (ae_of_all _ hu0),
      ← hμIoc, ← hlint]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hrfin] with t ht
    exact ENNReal.ofReal_toReal ht.ne
  have hHint : ∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t := by
    intro θ
    rcases le_total 0 θ with h | h
    · rw [intervalIntegral.integral_of_le h]
      have e := huIoc 0 θ
      rw [ENNReal.ofReal_eq_ofReal_iff (setIntegral_nonneg measurableSet_Ioc fun t _ => hu0 t)
        (by linarith [hHm.monotone h])] at e
      linarith
    · rw [intervalIntegral.integral_of_ge h]
      have e := huIoc θ 0
      rw [ENNReal.ofReal_eq_ofReal_iff (setIntegral_nonneg measurableSet_Ioc fun t _ => hu0 t)
        (by linarith [hHm.monotone h])] at e
      linarith
  -- change of variables `∫_B ρ(H) u = ∫_{H(B)} ρ`
  have hcv : ∀ B : Set ℝ, MeasurableSet B → ∫ t in B, ρ (H t) * u t = ∫ τ in H '' B, ρ τ := by
    intro B hB
    have hHB := hB.image_of_continuousOn_injOn hHc.continuousOn hHm.injective.injOn
    have e1 : ∫ τ in H '' B, ρ τ ∂(Measure.map H μ) = ∫ t in B, ρ (H t) ∂μ := by
      rw [setIntegral_map hHB hρc.aestronglyMeasurable hHc.aemeasurable, preimage_image_eq _ hHm.injective]
    have e2 : ∫ t in B, ρ (H t) ∂(volume.withDensity r) = ∫ t in B, (r t).toReal • ρ (H t) :=
      setIntegral_withDensity_eq_setIntegral_toReal_smul' B hrm (ae_restrict_of_ae hrfin) _
    rw [hmap] at e1
    rw [hwd] at e2
    rw [e1, e2]
    refine setIntegral_congr_fun hB fun t _ => ?_
    show ρ (H t) * (r t).toReal = (r t).toReal • ρ (H t)
    rw [smul_eq_mul, mul_comm]
  have hfI : ∀ x y : ℝ, IntegrableOn (fun t => ρ (H t) * u t) (Icc x y) := fun x y =>
    (huI x y).bdd_mul (hρc.comp hHc).aestronglyMeasurable
      (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact hρM (H t))
  refine ⟨u, ρ, huI, hHint, hu0, hpos, hper, hlip, fun τ => (hbd τ).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hε _)), ?_⟩
  intro s A hA hAs
  set f : ℝ → ℝ := fun t => 2 * π * ρ (H t) * u t - 1 with hf_def
  have hfm : Measurable f := ((measurable_const.mul (hρc.comp hHc).measurable).mul hum).sub measurable_const
  have hIf : volume (Icc s (s + 2 * π)) ≠ ∞ := measure_Icc_lt_top.ne
  have hfIcc : IntegrableOn f (Icc s (s + 2 * π)) := by
    have h1 : IntegrableOn (fun t => 2 * π * ρ (H t) * u t) (Icc s (s + 2 * π)) := by
      refine (show IntegrableOn (fun t => 2 * π * (ρ (H t) * u t)) (Icc s (s + 2 * π)) volume from (hfI s (s + 2 * π)).const_mul (2 * π)).congr_fun
        (fun t _ => ?_) measurableSet_Icc
      show 2 * π * (ρ (H t) * u t) = 2 * π * ρ (H t) * u t
      ring
    exact h1.sub (integrableOn_const hIf)
  have hAf : volume A ≠ ∞ := ne_top_of_le_ne_top hIf (measure_mono hAs)
  -- the defect on sub-sets of `A`
  have hdef : ∀ B : Set ℝ, MeasurableSet B → B ⊆ A →
      |∫ t in B, f t| ≤ 2 * π * C₆ * Real.sqrt ε * Real.sqrt (volume A).toReal := by
    intro B hB hBA
    have hBs : B ⊆ Icc s (s + 2 * π) := hBA.trans hAs
    have hBf : volume B ≠ ∞ := ne_top_of_le_ne_top hIf (measure_mono hBs)
    have hBI' : IntegrableOn (fun t => 2 * π * ρ (H t) * u t) B := by
      refine (show IntegrableOn (fun t => 2 * π * (ρ (H t) * u t)) B volume from ((hfI s (s + 2 * π)).mono_set hBs).const_mul (2 * π)).congr_fun
        (fun t _ => ?_) hB
      show 2 * π * (ρ (H t) * u t) = 2 * π * ρ (H t) * u t
      ring
    have e : ∫ t in B, f t = 2 * π * ((∫ τ in H '' B, ρ τ) - (volume B).toReal / (2 * π)) := by
      show ∫ t in B, (2 * π * ρ (H t) * u t - 1) = _
      rw [integral_sub hBI' (integrableOn_const hBf), setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
      have e3 : ∫ t in B, 2 * π * ρ (H t) * u t = 2 * π * ∫ t in B, ρ (H t) * u t := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun hB fun t _ => ?_
        ring
      rw [e3, hcv B hB]
      field_simp
    rw [e, abs_mul, abs_of_pos (by positivity)]
    have h6 := hmeas s B hB hBs
    have hmono : Real.sqrt (volume B).toReal ≤ Real.sqrt (volume A).toReal :=
      Real.sqrt_le_sqrt (ENNReal.toReal_mono hAf (measure_mono hBA))
    calc 2 * π * |(∫ τ in H '' B, ρ τ) - (volume B).toReal / (2 * π)|
        ≤ 2 * π * (C₆ * Real.sqrt ε * Real.sqrt (volume B).toReal) :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
      _ ≤ 2 * π * (C₆ * Real.sqrt ε * Real.sqrt (volume A).toReal) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono (by positivity)) (by positivity)
      _ = _ := by ring
  -- `L¹` via the sign split
  set P := A ∩ {t | 0 ≤ f t} with hP_def
  set Q := A ∩ {t | f t < 0} with hQ_def
  have hPm : MeasurableSet P := hA.inter (measurableSet_le measurable_const hfm)
  have hQm : MeasurableSet Q := hA.inter (measurableSet_lt hfm measurable_const)
  have hfa : IntegrableOn (fun t => |f t|) A := (hfIcc.mono_set hAs).abs
  have hPQ : A = P ∪ Q := by
    ext t
    constructor
    · intro h
      by_cases h' : 0 ≤ f t
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, lt_of_not_ge h'⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  have hdisj : Disjoint P Q := Set.disjoint_left.2 fun t hP hQ =>
    (not_lt.2 (show 0 ≤ f t from hP.2)) (show f t < 0 from hQ.2)
  have hsplit : ∫ t in A, |f t| = (∫ t in P, f t) - ∫ t in Q, f t := by
    rw [hPQ, setIntegral_union hdisj hQm (hfa.mono_set inter_subset_left) (hfa.mono_set inter_subset_left),
      setIntegral_congr_fun hPm (fun t ht => abs_of_nonneg ht.2),
      setIntegral_congr_fun hQm (fun t ht => abs_of_neg ht.2), integral_neg]
    ring
  show ∫ t in A, |f t| ≤ _
  rw [hsplit]
  have h1 := hdef P hPm inter_subset_left
  have h2 := hdef Q hQm inter_subset_left
  have hCmax : 4 * π * C₆ ≤ max C₅ (4 * π * C₆) := le_max_right _ _
  have hsq : 0 ≤ Real.sqrt ε * Real.sqrt (volume A).toReal := by positivity
  calc (∫ t in P, f t) - ∫ t in Q, f t ≤ |∫ t in P, f t| + |∫ t in Q, f t| := by
        linarith [le_abs_self (∫ t in P, f t), neg_abs_le (∫ t in Q, f t)]
    _ ≤ 2 * π * C₆ * Real.sqrt ε * Real.sqrt (volume A).toReal +
          2 * π * C₆ * Real.sqrt ε * Real.sqrt (volume A).toReal := add_le_add h1 h2
    _ = 4 * π * C₆ * (Real.sqrt ε * Real.sqrt (volume A).toReal) := by ring
    _ ≤ max C₅ (4 * π * C₆) * (Real.sqrt ε * Real.sqrt (volume A).toReal) :=
        mul_le_mul_of_nonneg_right hCmax hsq
    _ = _ := by ring

/-! ## Block B (M6R): renormalisation (output frozen now; internal stubs frozen at block start) -/

/-! ## Block B internal stubs -/

/-- B1 (conjugation + reflection): `G₀ = φ_{F z}⁻¹ ∘ F ∘ φ_z` is a `K`-q.c. self-map of `𝔻` fixing `0`
(LZ `thm7_1_comp`, `isKQC_one_of_conformal`); its reflection in `∂𝔻` (LZ `thm13_3_boundary_correspondence`,
`ab_reflect`) is a `K`-q.c. homeomorphism `G` of `ℂ` agreeing with `G₀` on `𝔻`, and `F ∘ φ_z = φ_{F z} ∘ G` on `𝔻̄`
(continuity on `∂𝔻`). -/
theorem s07c_fkps_m6_rn_conj {F : ℂ → ℂ} {K : ℝ} {z : ℂ} {φ : ℂ → ℂ}
    (hφ : ∀ y, φ y = (y + z) / (1 + conj z * y)) (hF : IsKQC F univ K)
    (hFD : F '' unitDisc = unitDisc) (hz : z ∈ unitDisc) :
    ∃ G : ℂ → ℂ, IsKQC G univ K ∧ G '' univ = univ ∧ G '' unitDisc = unitDisc ∧ G 0 = 0 ∧
      (∀ y ∈ unitDisc, G y = (F (φ y) - F z) / (1 - conj (F z) * F (φ y))) ∧
      ∀ y ∈ closedBall (0 : ℂ) 1, F (φ y) = (G y + F z) / (1 + conj (F z) * G y) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hnz : ‖-z‖ < 1 := by rwa [norm_neg]
  have hφfun : φ = diskAut (-z) := by
    funext y
    rw [hφ]
    show (y + z) / (1 + conj z * y) = (y - -z) / (1 - star (-z) * y)
    rw [star_neg, Complex.star_def, sub_neg_eq_add, neg_mul, sub_neg_eq_add]
  have hFK : IsKQC F unitDisc K := ac_t_isKQC_restrict hF isOpen_ball (subset_univ _)
  have hFmap : MapsTo F unitDisc unitDisc := fun x hx => hFD ▸ mem_image_of_mem F hx
  have hc1 : ‖F z‖ < 1 := mem_ball_zero_iff.mp (hFmap hz)
  have himgA : ∀ a : ℂ, ‖a‖ < 1 → diskAut a '' unitDisc = unitDisc := by
    intro a ha
    ext u
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact mem_ball_zero_iff.mpr (diskAut_maps_disk_to_disk a w ha (mem_ball_zero_iff.mp hw))
    · intro hu
      have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
      exact ⟨diskAut (-a) u,
        mem_ball_zero_iff.mpr (diskAut_maps_disk_to_disk (-a) u (by rwa [norm_neg]) hu1),
        diskAut_neg_left_inv ha hu1.le⟩
  have hconf : ∀ a : ℂ, ‖a‖ < 1 → IsConformalOnto (diskAut a) unitDisc unitDisc := fun a ha =>
    ⟨fun x hx => (diskAut_differentiableAt a x ha (mem_ball_zero_iff.mp hx).le).differentiableWithinAt,
      fun x hx y hy hxy => diskAut_inj ha (mem_ball_zero_iff.mp hx).le (mem_ball_zero_iff.mp hy).le hxy,
      himgA a ha⟩
  have hφK : IsKQC φ unitDisc 1 := by
    rw [hφfun]
    exact isKQC_one_of_conformal isOpen_ball (hconf _ hnz)
  have hψK : IsKQC (diskAut (F z)) unitDisc 1 := isKQC_one_of_conformal isOpen_ball (hconf _ hc1)
  have hφimg : φ '' unitDisc = unitDisc := by
    rw [hφfun]
    exact himgA _ hnz
  have h1 := thm7_1_comp hφK hFK hφimg.subset
  have hFφimg : (F ∘ φ) '' unitDisc = unitDisc := by rw [image_comp, hφimg, hFD]
  have h2 := thm7_1_comp h1 hψK hFφimg.subset
  rw [one_mul, mul_one] at h2
  have hG₀img : (diskAut (F z) ∘ (F ∘ φ)) '' unitDisc = unitDisc := by
    rw [image_comp, hFφimg]
    exact himgA _ hc1
  have hφ0 : φ 0 = z := by rw [hφ]; simp
  have hG₀0 : (diskAut (F z) ∘ (F ∘ φ)) 0 = 0 := by
    rw [Function.comp_apply, Function.comp_apply, hφ0]
    exact diskAut_self (F z) hc1
  obtain ⟨Fx, hFx⟩ :=
    thm13_3_boundary_correspondence isJordanDomain_unitDisc isJordanDomain_unitDisc ⟨K, h2⟩ hG₀img
  obtain ⟨g, hg, hgs, hgG, -, -, -⟩ := ab_reflect h2 hG₀img hG₀0 hFx
  have hgc : Continuous g := continuousOn_univ.mp hg.2.2.1.1
  have hFc : Continuous F := continuousOn_univ.mp hF.2.2.1.1
  have hgy : ∀ y ∈ unitDisc, g y = diskAut (F z) (F (φ y)) := fun y hy => by
    rw [hgG hy, Function.comp_apply, Function.comp_apply]
  have hgform : ∀ y ∈ unitDisc, g y = (F (φ y) - F z) / (1 - conj (F z) * F (φ y)) := fun y hy => by
    rw [hgy y hy]
    show (F (φ y) - F z) / (1 - star (F z) * F (φ y)) = _
    rw [Complex.star_def]
  refine ⟨g, hg, hgs, ?_, ?_, hgform, ?_⟩
  · rw [hgG.image_eq]
    exact hG₀img
  · rw [hgG (mem_ball_self one_pos)]
    exact hG₀0
  · -- the identity on `𝔻` (invert `φ_{F z}⁻¹`), then on `𝔻̄` by continuity
    have hin : EqOn (fun y => F (φ y)) (fun y => (g y + F z) / (1 + conj (F z) * g y)) unitDisc := by
      intro y hy
      have hFy : ‖F (φ y)‖ < 1 :=
        mem_ball_zero_iff.mp (hFmap (hφimg ▸ mem_image_of_mem φ hy))
      have e := diskAut_neg_left_inv (a := -F z) (by rwa [norm_neg]) (u := F (φ y)) hFy.le
      rw [neg_neg] at e
      show F (φ y) = (g y + F z) / (1 + conj (F z) * g y)
      rw [hgy y hy]
      calc F (φ y) = diskAut (-F z) (diskAut (F z) (F (φ y))) := e.symm
        _ = _ := by
          show (diskAut (F z) (F (φ y)) - -F z) / (1 - star (-F z) * diskAut (F z) (F (φ y))) = _
          rw [star_neg, Complex.star_def, sub_neg_eq_add, neg_mul, sub_neg_eq_add]
    have hcl : closure unitDisc = closedBall (0 : ℂ) 1 := closure_ball (0 : ℂ) one_ne_zero
    have hgcb : ∀ y ∈ closedBall (0 : ℂ) 1, ‖g y‖ ≤ 1 := by
      intro y hy
      have hy' : y ∈ closure unitDisc := by rw [hcl]; exact hy
      have h3 : g y ∈ closure (g '' unitDisc) := image_closure_subset_closure_image hgc ⟨y, hy', rfl⟩
      rw [hgG.image_eq, hG₀img, hcl] at h3
      exact mem_closedBall_zero_iff.mp h3
    have hden : ∀ y ∈ closedBall (0 : ℂ) 1, (1 : ℂ) + conj (F z) * g y ≠ 0 := by
      intro y hy h
      have h4 : ‖conj (F z) * g y‖ < 1 := by
        rw [norm_mul, Complex.norm_conj]
        calc ‖F z‖ * ‖g y‖ ≤ ‖F z‖ * 1 := mul_le_mul_of_nonneg_left (hgcb y hy) (norm_nonneg _)
          _ < 1 := by rw [mul_one]; exact hc1
      have h' : conj (F z) * g y = -1 := by linear_combination h
      rw [h', norm_neg, norm_one] at h4
      exact lt_irrefl _ h4
    have hφden : ∀ y ∈ closedBall (0 : ℂ) 1, (1 : ℂ) + conj z * y ≠ 0 := by
      intro y hy h
      have h4 : ‖conj z * y‖ < 1 := by
        rw [norm_mul, Complex.norm_conj]
        calc ‖z‖ * ‖y‖ ≤ ‖z‖ * 1 :=
              mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hy) (norm_nonneg _)
          _ < 1 := by rw [mul_one]; exact hz1
      have h' : conj z * y = -1 := by linear_combination h
      rw [h', norm_neg, norm_one] at h4
      exact lt_irrefl _ h4
    have hφc : ContinuousOn φ (closedBall (0 : ℂ) 1) := by
      rw [show φ = fun y => (y + z) / (1 + conj z * y) from funext hφ]
      exact ContinuousOn.div (by fun_prop) (by fun_prop) hφden
    have hL : ContinuousOn (fun y => F (φ y)) (closedBall (0 : ℂ) 1) := hFc.comp_continuousOn hφc
    have hR : ContinuousOn (fun y => (g y + F z) / (1 + conj (F z) * g y)) (closedBall (0 : ℂ) 1) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) hden
    intro y hy
    have hsub : closedBall (0 : ℂ) 1 ⊆ closure unitDisc := by rw [hcl]
    exact hin.of_subset_closure hL hR ball_subset_closedBall hsub hy

/-- B2 helper (w4): the Möbius denominators `1 ± ā w` do not vanish for `|a|, |w| < 1`. -/
theorem s07c_fkps_m6_rn_w4_den {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    1 + conj a * w ≠ 0 ∧ 1 - conj a * w ≠ 0 := by
  have h : ‖conj a * w‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg a, norm_nonneg w]
  constructor
  · intro h0
    have h1 : conj a * w = -1 := by linear_combination h0
    rw [h1, norm_neg, norm_one] at h
    exact lt_irrefl _ h
  · intro h0
    have h1 : conj a * w = 1 := by linear_combination -h0
    rw [h1, norm_one] at h
    exact lt_irrefl _ h

/-- B2 helper (w4): `1 - ā a ≠ 0` for `|a| < 1`. -/
theorem s07c_fkps_m6_rn_w4_num {a : ℂ} (ha : ‖a‖ < 1) : (1 : ℂ) - conj a * a ≠ 0 := by
  have e : (1 : ℂ) - conj a * a = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']
    push_cast
    ring
  rw [e]
  exact Complex.ofReal_ne_zero.2 (ne_of_gt (by nlinarith [norm_nonneg a]))

/-- B2 helper (w4): the disc automorphism `w ↦ (w - a)/(1 - ā w)` maps `𝔻` into `𝔻` (S07 `s07_de_mob_varpi`). -/
theorem s07c_fkps_m6_rn_w4_mem_sub {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    ‖(w - a) / (1 - conj a * w)‖ < 1 := by
  have h := s07_de_mob_varpi ha hw.le
  have hden := diskAut_denom_ne_zero a w ha hw.le
  have hpos : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖w‖ ^ 2) / ‖1 - star a * w‖ ^ 2 :=
    div_pos (mul_pos (by nlinarith [norm_nonneg a]) (by nlinarith [norm_nonneg w]))
      (pow_pos (norm_pos_iff.2 hden) 2)
  have h2 : ‖diskAut a w‖ ^ 2 < 1 := by linarith
  have h3 : ‖diskAut a w‖ < 1 := by nlinarith [norm_nonneg (diskAut a w)]
  exact h3

/-- B2 helper (w4): `w ↦ (w + a)/(1 + ā w)` maps `𝔻` into `𝔻`. -/
theorem s07c_fkps_m6_rn_w4_mem_add {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    ‖(w + a) / (1 + conj a * w)‖ < 1 := by
  have h := s07c_fkps_m6_rn_w4_mem_sub (a := -a) (by rwa [norm_neg]) hw
  rwa [map_neg, sub_neg_eq_add, neg_mul, sub_neg_eq_add] at h

/-- B2 helper (w4): `(w ↦ (w - a)/(1 - ā w))` has derivative `(1 - ā a)/(1 - ā w)²`. -/
theorem s07c_fkps_m6_rn_w4_hd_sub {a w : ℂ} (hden : 1 - conj a * w ≠ 0) :
    HasDerivAt (fun v => (v - a) / (1 - conj a * v)) ((1 - conj a * a) / (1 - conj a * w) ^ 2) w := by
  have h := ((hasDerivAt_id' w).sub_const a).div (((hasDerivAt_id' w).const_mul (conj a)).const_sub 1) hden
  convert h using 1
  ring

/-- B2 helper (w4): `(w ↦ (w + a)/(1 + ā w))` has derivative `(1 - ā a)/(1 + ā w)²`. -/
theorem s07c_fkps_m6_rn_w4_hd_add {a w : ℂ} (hden : 1 + conj a * w ≠ 0) :
    HasDerivAt (fun v => (v + a) / (1 + conj a * v)) ((1 - conj a * a) / (1 + conj a * w) ^ 2) w := by
  have h := ((hasDerivAt_id' w).add_const a).div (((hasDerivAt_id' w).const_mul (conj a)).const_add 1) hden
  convert h using 1
  ring

/-- B2 helper (w4): `(w ↦ (w + a)/(1 + ā w))` inverts `(w ↦ (w - a)/(1 - ā w))` on `𝔻`. -/
theorem s07c_fkps_m6_rn_w4_inv_sub {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    ((w - a) / (1 - conj a * w) + a) / (1 + conj a * ((w - a) / (1 - conj a * w))) = w := by
  have hd := (s07c_fkps_m6_rn_w4_den ha hw).2
  have hq : (w - a) / (1 - conj a * w) * (1 - conj a * w) = w - a := div_mul_cancel₀ _ hd
  rw [div_eq_iff (s07c_fkps_m6_rn_w4_den ha (s07c_fkps_m6_rn_w4_mem_sub ha hw)).1]
  linear_combination hq

/-- B2 helper (w4): `(w ↦ (w - a)/(1 - ā w))` inverts `(w ↦ (w + a)/(1 + ā w))` on `𝔻`. -/
theorem s07c_fkps_m6_rn_w4_inv_add {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    ((w + a) / (1 + conj a * w) - a) / (1 - conj a * ((w + a) / (1 + conj a * w))) = w := by
  have hd := (s07c_fkps_m6_rn_w4_den ha hw).1
  have hq : (w + a) / (1 + conj a * w) * (1 + conj a * w) = w + a := div_mul_cancel₀ _ hd
  rw [div_eq_iff (s07c_fkps_m6_rn_w4_den ha (s07c_fkps_m6_rn_w4_mem_add ha hw)).2]
  linear_combination hq

/-- B2 helper (w4): the complex dilatation vanishes where the map is not `ℝ`-differentiable. -/
theorem s07c_fkps_m6_rn_w4_cd_nd {f : ℂ → ℂ} {p : ℂ} (h : ¬ DifferentiableAt ℝ f p) :
    LiZhongQC.complexDilatation f p = 0 := by
  show (fderiv ℝ f p 1 + I * fderiv ℝ f p I) / 2 / ((fderiv ℝ f p 1 - I * fderiv ℝ f p I) / 2) = 0
  rw [fderiv_zero_of_not_differentiableAt h]
  simp

/-- B2 (dilatation under conformal conjugation): if `G = φ_c⁻¹ ∘ F ∘ φ_z` on `𝔻` and `F(𝔻) ⊆ 𝔻`, then
`|μ_G| = |μ_F| ∘ φ_z` at every point of `𝔻` (LZ `eq6_2_dz_comp`/`eq6_2_dzbar_comp`; where `F` is not
`ℝ`-differentiable at `φ_z y`, neither is `G` at `y`, and both dilatations are `0`). -/
theorem s07c_fkps_m6_rn_dil {F G : ℂ → ℂ} {z c : ℂ} {φ : ℂ → ℂ}
    (hφ : ∀ y, φ y = (y + z) / (1 + conj z * y)) (hz : z ∈ unitDisc) (hc : c ∈ unitDisc)
    (hFD : MapsTo F unitDisc unitDisc)
    (hG : ∀ y ∈ unitDisc, G y = (F (φ y) - c) / (1 - conj c * F (φ y))) :
    ∀ y ∈ unitDisc, ‖LiZhongQC.complexDilatation G y‖ = ‖LiZhongQC.complexDilatation F (φ y)‖ := by
  intro y hy
  have hy1 : ‖y‖ < 1 := mem_ball_zero_iff.1 hy
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hc1 : ‖c‖ < 1 := mem_ball_zero_iff.1 hc
  have hUo : IsOpen unitDisc := isOpen_ball
  have hφfun : φ = fun v => (v + z) / (1 + conj z * v) := funext hφ
  have hp1 : ‖φ y‖ < 1 := by rw [hφ]; exact s07c_fkps_m6_rn_w4_mem_add hz1 hy1
  have hpD : φ y ∈ unitDisc := mem_ball_zero_iff.2 hp1
  have hFp : ‖F (φ y)‖ < 1 := mem_ball_zero_iff.1 (hFD hpD)
  by_cases hd : DifferentiableAt ℝ F (φ y)
  · -- `G = M_c ∘ F ∘ φ` near `y`, with `M_c`, `φ` holomorphic and locally invertible
    have hEq : EqOn G ((fun v => (v - c) / (1 - conj c * v)) ∘ (F ∘ φ)) unitDisc := fun w hw => hG w hw
    have hφd : HasDerivAt φ ((1 - conj z * z) / (1 + conj z * y) ^ 2) y := by
      rw [hφfun]
      exact s07c_fkps_m6_rn_w4_hd_add (s07c_fkps_m6_rn_w4_den hz1 hy1).1
    have hMd := s07c_fkps_m6_rn_w4_hd_sub (a := c) (w := F (φ y)) (s07c_fkps_m6_rn_w4_den hc1 hFp).2
    have hFφ : DifferentiableAt ℝ (F ∘ φ) y := hd.comp y (hφd.differentiableAt.restrictScalars ℝ)
    have hφne : deriv φ y ≠ 0 := by
      rw [hφd.deriv]
      exact div_ne_zero (s07c_fkps_m6_rn_w4_num hz1) (pow_ne_zero 2 (s07c_fkps_m6_rn_w4_den hz1 hy1).1)
    have hMne : deriv (fun v => (v - c) / (1 - conj c * v)) ((F ∘ φ) y) ≠ 0 := by
      rw [show (F ∘ φ) y = F (φ y) from rfl, hMd.deriv]
      exact div_ne_zero (s07c_fkps_m6_rn_w4_num hc1) (pow_ne_zero 2 (s07c_fkps_m6_rn_w4_den hc1 hFp).2)
    have e1 := LiZhongQC.complexDilatation_comp_conformal_left hFφ hMd.differentiableAt hMne
    have e2 := LiZhongQC.complexDilatation_comp_conformal_right hφd.differentiableAt hφne hd
    rw [LiZhongQC.abR_t_complexDilatation_congr hUo hEq hy, e1, e2, norm_mul, norm_div, Complex.norm_conj,
      div_self (norm_ne_zero_iff.2 hφne), mul_one]
  · -- neither side is differentiable: `F = M_c⁻¹ ∘ G ∘ φ⁻¹` near `φ y`
    have hR : LiZhongQC.complexDilatation F (φ y) = 0 := s07c_fkps_m6_rn_w4_cd_nd hd
    have hL : ¬ DifferentiableAt ℝ G y := by
      intro hG'
      apply hd
      set ψ : ℂ → ℂ := fun w => (w - z) / (1 - conj z * w) with hψ_def
      set Mi : ℂ → ℂ := fun v => (v + c) / (1 + conj c * v) with hMi_def
      have hEq : EqOn F (Mi ∘ G ∘ ψ) unitDisc := by
        intro w hw
        have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
        have hψ1 : ‖ψ w‖ < 1 := s07c_fkps_m6_rn_w4_mem_sub hz1 hw1
        have hφψ : φ (ψ w) = w := by rw [hφ]; exact s07c_fkps_m6_rn_w4_inv_sub hz1 hw1
        have hFw : ‖F w‖ < 1 := mem_ball_zero_iff.1 (hFD hw)
        show F w = Mi (G (ψ w))
        rw [hG (ψ w) (mem_ball_zero_iff.2 hψ1), hφψ]
        exact (s07c_fkps_m6_rn_w4_inv_sub hc1 hFw).symm
      have hψφ : ψ (φ y) = y := by rw [hφ]; exact s07c_fkps_m6_rn_w4_inv_add hz1 hy1
      have hGy1 : ‖G y‖ < 1 := by rw [hG y hy]; exact s07c_fkps_m6_rn_w4_mem_sub hc1 hFp
      have hψd : DifferentiableAt ℝ ψ (φ y) :=
        (s07c_fkps_m6_rn_w4_hd_sub (s07c_fkps_m6_rn_w4_den hz1 hp1).2).differentiableAt.restrictScalars ℝ
      have hGd : DifferentiableAt ℝ G (ψ (φ y)) := by rw [hψφ]; exact hG'
      have hMid : DifferentiableAt ℝ Mi (G (ψ (φ y))) := by
        rw [hψφ]
        exact (s07c_fkps_m6_rn_w4_hd_add (s07c_fkps_m6_rn_w4_den hc1 hGy1).1).differentiableAt.restrictScalars ℝ
      have hcomp : DifferentiableAt ℝ (Mi ∘ G ∘ ψ) (φ y) := hMid.comp (φ y) (hGd.comp (φ y) hψd)
      exact hcomp.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hUo.mem_nhds hpD) hEq)
    rw [hR, s07c_fkps_m6_rn_w4_cd_nd hL]

/-- B3 (null sets): `φ_z⁻¹(s) ∩ 𝔻` is null when `s` is (Mathlib
`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` for `φ_z⁻¹ = g_z`). -/
theorem s07c_fkps_m6_rn_null {z : ℂ} {φ : ℂ → ℂ} (hφ : ∀ y, φ y = (y + z) / (1 + conj z * y))
    (hz : z ∈ unitDisc) {s : Set ℂ} (hs : volume s = 0) :
    volume {y | y ∈ unitDisc ∧ φ y ∈ s} = 0 := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hnz : ‖-z‖ < 1 := by rwa [norm_neg]
  have hφd : ∀ u, φ u = diskAut (-z) u := fun u => by
    rw [hφ]
    show (u + z) / (1 + conj z * u) = (u - -z) / (1 - star (-z) * u)
    rw [star_neg, Complex.star_def, sub_neg_eq_add, neg_mul, sub_neg_eq_add]
  -- `{y ∈ 𝔻 | φ y ∈ s} ⊆ g_z(s ∩ 𝔻)` with `g_z = φ_z⁻¹` differentiable on `𝔻`
  have hdiff : DifferentiableOn ℝ (diskAut z) (s ∩ unitDisc) := fun x hx =>
    ((diskAut_differentiableAt z x hz1 (mem_ball_zero_iff.mp hx.2).le).restrictScalars ℝ).differentiableWithinAt
  have h0 : volume (diskAut z '' (s ∩ unitDisc)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff
      (measure_mono_null inter_subset_left hs)
  refine measure_mono_null ?_ h0
  rintro y ⟨hy, hys⟩
  have hy1 : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
  refine ⟨φ y, ⟨hys, ?_⟩, ?_⟩
  · rw [hφd]
    exact mem_ball_zero_iff.mpr (diskAut_maps_disk_to_disk _ _ hnz hy1)
  · rw [hφd]
    exact diskAut_neg_left_inv hz1 hy1.le

/-- B4 (Möbius invariance): `φ_z` maps `𝔻` into `𝔻`, preserves `cosh d` (S07 `s07_de_mob_dist`) and
`1 - |φ_z w|² = (1 - |z|²)(1 - |w|²)/|1 + z̄ w|²` (S07 `s07_de_mob_varpi`). -/
theorem s07c_fkps_m6_rn_inv {z w y : ℂ} {φ : ℂ → ℂ} (hφ : ∀ y, φ y = (y + z) / (1 + conj z * y))
    (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hy : y ∈ unitDisc) :
    φ w ∈ unitDisc ∧ diskCoshDist (φ w) (φ y) = diskCoshDist w y ∧
      1 - ‖φ w‖ ^ 2 = (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) / ‖1 + conj z * w‖ ^ 2 := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hnz : ‖-z‖ < 1 := by rwa [norm_neg]
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hy1 : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
  have hφb : ∀ u, φ u = blaschke (-z) u := fun u => by
    rw [hφ]
    show (u + z) / (1 + conj z * u) = (u - -z) / (1 - conj (-z) * u)
    rw [map_neg, sub_neg_eq_add, neg_mul, sub_neg_eq_add]
  have hφd : ∀ u, φ u = diskAut (-z) u := fun u => by
    rw [hφ]
    show (u + z) / (1 + conj z * u) = (u - -z) / (1 - star (-z) * u)
    rw [star_neg, Complex.star_def, sub_neg_eq_add, neg_mul, sub_neg_eq_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [hφd]
    exact mem_ball_zero_iff.mpr (diskAut_maps_disk_to_disk _ _ hnz hw1)
  · rw [hφb w, hφb y]
    exact s02_diskCoshDist_blaschke hnz hw1 hy1
  · rw [hφd, s07_de_mob_varpi hnz hw1.le, norm_neg, star_neg, Complex.star_def, neg_mul,
      sub_neg_eq_add]

/-- B5 helper (w4): the real Jacobian of `v ↦ d v` (a complex-linear map viewed over `ℝ`) is `|d|²`. -/
theorem s07c_fkps_m6_rn_w4_det (d : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ : ℂ →L[ℝ] ℂ).det = ‖d‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
    Complex.normSq_eq_norm_sq]

/-- B5 helper (w4): `|φ_z'(y)| = (1 - |z|²)/|1 + z̄ y|²`. -/
theorem s07c_fkps_m6_rn_w4_ndiv {z : ℂ} (hz : ‖z‖ < 1) (y : ℂ) :
    ‖(1 - conj z * z) / (1 + conj z * y) ^ 2‖ = (1 - ‖z‖ ^ 2) / ‖1 + conj z * y‖ ^ 2 := by
  have e : (1 : ℂ) - conj z * z = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']
    push_cast
    ring
  rw [norm_div, e, Complex.norm_of_nonneg (by nlinarith [norm_nonneg z]), norm_pow]

/-- B5 helper (w4): `φ_z(𝔻) = 𝔻`. -/
theorem s07c_fkps_m6_rn_w4_image {z : ℂ} {φ : ℂ → ℂ} (hφ : ∀ y, φ y = (y + z) / (1 + conj z * y))
    (hz : ‖z‖ < 1) : φ '' unitDisc = unitDisc := by
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    rw [hφ]
    exact mem_ball_zero_iff.2 (s07c_fkps_m6_rn_w4_mem_add hz (mem_ball_zero_iff.1 hy))
  · intro x hx
    have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.1 hx
    refine ⟨(x - z) / (1 - conj z * x), mem_ball_zero_iff.2 (s07c_fkps_m6_rn_w4_mem_sub hz hx1), ?_⟩
    rw [hφ]
    exact s07c_fkps_m6_rn_w4_inv_sub hz hx1

/-- B5 helper (w4): `φ_z` is injective on `𝔻`. -/
theorem s07c_fkps_m6_rn_w4_injOn {z : ℂ} {φ : ℂ → ℂ} (hφ : ∀ y, φ y = (y + z) / (1 + conj z * y))
    (hz : ‖z‖ < 1) : InjOn φ unitDisc := by
  intro a ha b hb hab
  have e1 := s07c_fkps_m6_rn_w4_inv_add hz (mem_ball_zero_iff.1 ha)
  have e2 := s07c_fkps_m6_rn_w4_inv_add hz (mem_ball_zero_iff.1 hb)
  rw [← hφ a] at e1
  rw [← hφ b] at e2
  rw [← e1, ← e2, hab]

/-- B5 (Möbius change of variables): `∫_𝔻 f = ∫_𝔻 |φ_z'|² f ∘ φ_z` (Mathlib
`lintegral_image_eq_lintegral_abs_det_fderiv_mul`, DE `det_diskAutFDeriv`, `diskAut_image_ball`). -/
theorem s07c_fkps_m6_rn_cov {z : ℂ} {φ : ℂ → ℂ} (hφ : ∀ y, φ y = (y + z) / (1 + conj z * y))
    (hz : z ∈ unitDisc) (f : ℂ → ℝ≥0∞) :
    ∫⁻ x in unitDisc, f x = ∫⁻ y in unitDisc,
      ENNReal.ofReal (((1 - ‖z‖ ^ 2) / ‖1 + conj z * y‖ ^ 2) ^ 2) * f (φ y) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hs : MeasurableSet (unitDisc : Set ℂ) := measurableSet_ball
  have hφfun : φ = fun v => (v + z) / (1 + conj z * v) := funext hφ
  have hf' : ∀ y ∈ unitDisc, HasFDerivWithinAt φ
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        ((1 - conj z * z) / (1 + conj z * y) ^ 2)).restrictScalars ℝ : ℂ →L[ℝ] ℂ) unitDisc y := by
    intro y hy
    have h : HasDerivAt φ ((1 - conj z * z) / (1 + conj z * y) ^ 2) y := by
      rw [hφfun]
      exact s07c_fkps_m6_rn_w4_hd_add (s07c_fkps_m6_rn_w4_den hz1 (mem_ball_zero_iff.1 hy)).1
    exact (h.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hf'
    (s07c_fkps_m6_rn_w4_injOn hφ hz1) f
  rw [s07c_fkps_m6_rn_w4_image hφ hz1] at key
  rw [key]
  refine setLIntegral_congr_fun hs (fun y _ => ?_)
  show ENNReal.ofReal |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
      ((1 - conj z * z) / (1 + conj z * y) ^ 2)).restrictScalars ℝ : ℂ →L[ℝ] ℂ).det| * f (φ y) = _
  rw [s07c_fkps_m6_rn_w4_det, abs_of_nonneg (sq_nonneg _), s07c_fkps_m6_rn_w4_ndiv hz1]

/-- B6 (`cosh` form of the triangle inequality, S02 `s02_diskDist_triangle`):
`cosh d(x, w) ≤ 2 cosh d(x, y) cosh d(y, w)`. -/
theorem s07c_fkps_m6_rn_ctri {x y w : ℂ} (hx : x ∈ unitDisc) (hy : y ∈ unitDisc) (hw : w ∈ unitDisc) :
    diskCoshDist x w ≤ 2 * diskCoshDist x y * diskCoshDist y w := by
  have hge : ∀ a b : ℂ, a ∈ unitDisc → b ∈ unitDisc → 1 ≤ diskCoshDist a b := by
    intro a b ha hb
    have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
    have hb1 : ‖b‖ < 1 := mem_ball_zero_iff.mp hb
    have hpa : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
    have hpb : 0 < 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
    have h0 : 0 ≤ 2 * ‖a - b‖ ^ 2 / ((1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2)) := by positivity
    unfold diskCoshDist
    linarith
  have hc : ∀ a b : ℂ, a ∈ unitDisc → b ∈ unitDisc → Real.cosh (diskDist a b) = diskCoshDist a b :=
    fun a b ha hb => Real.cosh_arcosh (hge a b ha hb)
  have hn : ∀ a b : ℂ, a ∈ unitDisc → b ∈ unitDisc → 0 ≤ diskDist a b :=
    fun a b ha hb => Real.arcosh_nonneg (hge a b ha hb)
  have htri := s02_diskDist_triangle hx hy hw
  have hp := hn x y hx hy
  have hq := hn y w hy hw
  rw [← hc x w hx hw, ← hc x y hx hy, ← hc y w hy hw]
  calc Real.cosh (diskDist x w) ≤ Real.cosh (diskDist x y + diskDist y w) := by
        rw [Real.cosh_le_cosh, abs_of_nonneg (hn x w hx hw), abs_of_nonneg (by linarith)]
        exact htri
    _ = Real.cosh (diskDist x y) * Real.cosh (diskDist y w) +
          Real.sinh (diskDist x y) * Real.sinh (diskDist y w) := Real.cosh_add _ _
    _ ≤ 2 * Real.cosh (diskDist x y) * Real.cosh (diskDist y w) := by
        have h1 : Real.sinh (diskDist x y) ≤ Real.cosh (diskDist x y) := (Real.sinh_lt_cosh _).le
        have h2 : Real.sinh (diskDist y w) ≤ Real.cosh (diskDist y w) := (Real.sinh_lt_cosh _).le
        have h4 : 0 ≤ Real.sinh (diskDist y w) := Real.sinh_nonneg_iff.mpr hq
        have h5 := mul_le_mul h1 h2 h4 (Real.cosh_pos _).le
        nlinarith

/-- B7 (hyperbolic balls are Whitney-sized): on `cosh d(w, x) < 5` the weights `1 - |·|²` agree up to `10` and
`|w - x| ≤ 5(1 - |x|²)`. -/
theorem s07c_fkps_m6_rn_hyp {w x : ℂ} (hw : w ∈ unitDisc) (hx : x ∈ unitDisc) (h : diskCoshDist w x < 5) :
    1 - ‖x‖ ^ 2 ≤ 10 * (1 - ‖w‖ ^ 2) ∧ 1 - ‖w‖ ^ 2 ≤ 10 * (1 - ‖x‖ ^ 2) ∧
      ‖w - x‖ ≤ 5 * (1 - ‖x‖ ^ 2) := by
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
  have hp : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hq : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  have hd : ‖w - x‖ ^ 2 < 2 * ((1 - ‖w‖ ^ 2) * (1 - ‖x‖ ^ 2)) := by
    have h' : 2 * ‖w - x‖ ^ 2 / ((1 - ‖w‖ ^ 2) * (1 - ‖x‖ ^ 2)) < 4 := by
      unfold diskCoshDist at h
      linarith
    have h'' := (div_lt_iff₀ (mul_pos hp hq)).mp h'
    linarith
  have hab : |‖w‖ - ‖x‖| ≤ ‖w - x‖ := abs_norm_sub_norm_le w x
  have e1 : (‖w‖ - ‖x‖) ^ 2 ≤ ‖w - x‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hab 2
  have e2 : (‖w‖ + ‖x‖) ^ 2 ≤ 4 := by nlinarith [norm_nonneg w, norm_nonneg x]
  have e3 : ((1 - ‖x‖ ^ 2) - (1 - ‖w‖ ^ 2)) ^ 2 ≤ 4 * ‖w - x‖ ^ 2 := by
    have e4 : ((1 - ‖x‖ ^ 2) - (1 - ‖w‖ ^ 2)) ^ 2 = (‖w‖ - ‖x‖) ^ 2 * (‖w‖ + ‖x‖) ^ 2 := by ring
    rw [e4]
    calc (‖w‖ - ‖x‖) ^ 2 * (‖w‖ + ‖x‖) ^ 2 ≤ ‖w - x‖ ^ 2 * 4 :=
          mul_le_mul e1 e2 (sq_nonneg _) (sq_nonneg _)
      _ = 4 * ‖w - x‖ ^ 2 := by ring
  have hqp : 1 - ‖x‖ ^ 2 ≤ 10 * (1 - ‖w‖ ^ 2) := by
    by_contra hc
    replace hc := not_le.mp hc
    nlinarith [mul_pos hq (sub_pos.mpr hc)]
  have hpq : 1 - ‖w‖ ^ 2 ≤ 10 * (1 - ‖x‖ ^ 2) := by
    by_contra hc
    replace hc := not_le.mp hc
    nlinarith [mul_pos hp (sub_pos.mpr hc)]
  refine ⟨hqp, hpq, ?_⟩
  by_contra hc
  replace hc := not_le.mp hc
  have h5 : 0 ≤ 5 * (1 - ‖x‖ ^ 2) := by positivity
  have h6 : (5 * (1 - ‖x‖ ^ 2)) ^ 2 < ‖w - x‖ ^ 2 := pow_lt_pow_left₀ hc h5 (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hpq hq.le]

/-- B8 (Whitney balls are hyperbolically small): `w ∈ B(y, (1 - |y|)/2)` gives `w ∈ 𝔻`, `cosh d(w, y) ≤ 2`. -/
theorem s07c_fkps_m6_rn_wb {w y : ℂ} (hy : y ∈ unitDisc) (hw : w ∈ ball y ((1 - ‖y‖) / 2)) :
    w ∈ unitDisc ∧ diskCoshDist w y ≤ 2 := by
  have hy1 : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
  have hd : ‖w - y‖ < (1 - ‖y‖) / 2 := by rw [← dist_eq_norm]; exact mem_ball.mp hw
  have hwn : ‖w‖ ≤ ‖y‖ + ‖w - y‖ := by
    calc ‖w‖ = ‖y + (w - y)‖ := by ring_nf
      _ ≤ ‖y‖ + ‖w - y‖ := norm_add_le _ _
  have hw1 : ‖w‖ < 1 := by linarith
  refine ⟨mem_ball_zero_iff.mpr hw1, ?_⟩
  have hp : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hq : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
  have hA : (1 - ‖y‖) / 2 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w, norm_nonneg (w - y)]
  have hB : 1 - ‖y‖ ≤ 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
  have hC : 2 * ‖w - y‖ ^ 2 ≤ (1 - ‖y‖) / 2 * (1 - ‖y‖) := by nlinarith [norm_nonneg (w - y)]
  have hD : (1 - ‖y‖) / 2 * (1 - ‖y‖) ≤ (1 - ‖w‖ ^ 2) * (1 - ‖y‖ ^ 2) :=
    mul_le_mul hA hB (by linarith) hp.le
  have hE : 2 * ‖w - y‖ ^ 2 / ((1 - ‖w‖ ^ 2) * (1 - ‖y‖ ^ 2)) ≤ 1 :=
    (div_le_one (mul_pos hp hq)).mpr (hC.trans hD)
  unfold diskCoshDist
  linarith

/-- B9 (invariant majorant, pointwise): from the Whitney majorant `a` (M4 `s07c_fkps_m4_whitney_avg`:
`|μ_F(x)|² ≲ (1 - |x|)⁻² ∫_{B(x, (1-|x|)/4)} a²`), a.e. on `cosh d(·, x₀) ≤ 2`,
`|μ_F|² ≤ 32 ∫_{D(x₀)} a²/(1 - |w|²)²` (B6: `B(x, (1-|x|)/4) ⊆ D(x₀)`). -/
theorem s07c_fkps_m6_rn_whit {F : ℂ → ℂ} {a : ℂ → ℝ} (ha : Measurable a)
    (hW : ∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) →
      ‖LiZhongQC.complexDilatation F w‖ ≤ a z) :
    ∀ x₀ ∈ unitDisc, ∀ᵐ x, x ∈ unitDisc → diskCoshDist x x₀ ≤ 2 →
      ENNReal.ofReal (‖LiZhongQC.complexDilatation F x‖ ^ 2) ≤ 32 *
        ∫⁻ w in {w | w ∈ unitDisc ∧ diskCoshDist w x₀ < 5},
          ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2) := by
  intro x₀ hx₀
  have hx01 : ‖x₀‖ < 1 := mem_ball_zero_iff.mp hx₀
  have hq0 : 0 < 1 - ‖x₀‖ ^ 2 := by nlinarith [norm_nonneg x₀]
  have hm : AEMeasurable fun w => ‖LiZhongQC.complexDilatation F w‖ :=
    ((measurable_dzbar F).div (measurable_dz F)).norm.aemeasurable
  have hm0 : ∀ w, 0 ≤ ‖LiZhongQC.complexDilatation F w‖ := fun w => norm_nonneg _
  filter_upwards [s07c_fkps_m4_whitney_avg hm ha hm0 hW] with x hx hx𝔻 hxd
  have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx𝔻
  have hr : 0 < (1 - ‖x‖) / 4 := by linarith
  have hq : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  -- geometry of the small ball `B(x, (1 - |x|)/4)`
  have hgeo : ∀ w ∈ ball x ((1 - ‖x‖) / 4), w ∈ unitDisc ∧ 0 < 1 - ‖w‖ ^ 2 ∧
      3 * (1 - ‖x‖) / 4 ≤ 1 - ‖w‖ ^ 2 ∧ 1 - ‖w‖ ^ 2 ≤ 10 * ((1 - ‖x‖) / 4) ∧
      ‖w - x‖ < (1 - ‖x‖) / 4 := by
    intro w hw
    have hd : ‖w - x‖ < (1 - ‖x‖) / 4 := by rw [← dist_eq_norm]; exact mem_ball.mp hw
    have hwn : ‖w‖ ≤ ‖x‖ + ‖w - x‖ := by
      calc ‖w‖ = ‖x + (w - x)‖ := by ring_nf
        _ ≤ ‖x‖ + ‖w - x‖ := norm_add_le _ _
    have hxn : ‖x‖ ≤ ‖w‖ + ‖w - x‖ := by
      calc ‖x‖ = ‖w - (w - x)‖ := by ring_nf
        _ ≤ ‖w‖ + ‖w - x‖ := norm_sub_le _ _
    have hw1 : ‖w‖ < 1 := by linarith
    have h1w : 1 - ‖w‖ ^ 2 ≤ 2 * (1 - ‖w‖) := by nlinarith [norm_nonneg w]
    refine ⟨mem_ball_zero_iff.mpr hw1, by nlinarith [norm_nonneg w], ?_, ?_, hd⟩
    · nlinarith [norm_nonneg w, norm_nonneg (w - x)]
    · linarith
  -- the small ball lies in `D(x₀)`
  have hball : ball x ((1 - ‖x‖) / 4) ⊆ {w | w ∈ unitDisc ∧ diskCoshDist w x₀ < 5} := by
    intro w hw
    obtain ⟨hw𝔻, hp, hA, -, hd⟩ := hgeo w hw
    refine ⟨hw𝔻, ?_⟩
    have hB : 1 - ‖x‖ ≤ 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    have hC : 12 * ‖w - x‖ ^ 2 ≤ 3 * (1 - ‖x‖) / 4 * (1 - ‖x‖) := by
      nlinarith [norm_nonneg (w - x)]
    have hD : 3 * (1 - ‖x‖) / 4 * (1 - ‖x‖) ≤ (1 - ‖w‖ ^ 2) * (1 - ‖x‖ ^ 2) :=
      mul_le_mul hA hB (by linarith) hp.le
    have hE : 2 * ‖w - x‖ ^ 2 / ((1 - ‖w‖ ^ 2) * (1 - ‖x‖ ^ 2)) ≤ 1 / 6 := by
      rw [div_le_div_iff₀ (mul_pos hp hq) (by norm_num)]
      nlinarith
    have hE0 : 0 ≤ 2 * ‖w - x‖ ^ 2 / ((1 - ‖w‖ ^ 2) * (1 - ‖x‖ ^ 2)) :=
      div_nonneg (by positivity) (mul_pos hp hq).le
    have hwx : diskCoshDist w x ≤ 7 / 6 := by unfold diskCoshDist; linarith
    have hwx0 : 0 ≤ diskCoshDist w x := by unfold diskCoshDist; linarith
    have hB0 : 0 ≤ diskCoshDist x x₀ := by
      have : 0 ≤ 2 * ‖x - x₀‖ ^ 2 / ((1 - ‖x‖ ^ 2) * (1 - ‖x₀‖ ^ 2)) :=
        div_nonneg (by positivity) (mul_pos hq hq0).le
      unfold diskCoshDist
      linarith
    have ht := s07c_fkps_m6_rn_ctri hw𝔻 hx𝔻 hx₀
    show diskCoshDist w x₀ < 5
    nlinarith [mul_le_mul hwx hxd hB0 (by norm_num : (0 : ℝ) ≤ 7 / 6)]
  -- on the small ball, `a² ≤ 100 r² · a²/(1 - |w|²)²`
  have hpt : ∀ w ∈ ball x ((1 - ‖x‖) / 4), ENNReal.ofReal (a w ^ 2) ≤
      ENNReal.ofReal (100 * ((1 - ‖x‖) / 4) ^ 2) * ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2) := by
    intro w hw
    obtain ⟨-, hp, -, hpl, -⟩ := hgeo w hw
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hp2 : (1 - ‖w‖ ^ 2) ^ 2 ≤ 100 * ((1 - ‖x‖) / 4) ^ 2 := by nlinarith
    have hpne : (1 - ‖w‖ ^ 2) ^ 2 ≠ 0 := by positivity
    calc a w ^ 2 = a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2 * (1 - ‖w‖ ^ 2) ^ 2 := by field_simp
      _ ≤ a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2 * (100 * ((1 - ‖x‖) / 4) ^ 2) :=
          mul_le_mul_of_nonneg_left hp2 (by positivity)
      _ = 100 * ((1 - ‖x‖) / 4) ^ 2 * (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2) := by ring
  have hI : ∫⁻ z in ball x ((1 - ‖x‖) / 4), ENNReal.ofReal (a z ^ 2) ≤
      ENNReal.ofReal (100 * ((1 - ‖x‖) / 4) ^ 2) *
        ∫⁻ w in {w | w ∈ unitDisc ∧ diskCoshDist w x₀ < 5}, ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2) := by
    calc ∫⁻ z in ball x ((1 - ‖x‖) / 4), ENNReal.ofReal (a z ^ 2)
        ≤ ∫⁻ z in ball x ((1 - ‖x‖) / 4), ENNReal.ofReal (100 * ((1 - ‖x‖) / 4) ^ 2) *
            ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2) ^ 2) := setLIntegral_mono' measurableSet_ball hpt
      _ = ENNReal.ofReal (100 * ((1 - ‖x‖) / 4) ^ 2) *
            ∫⁻ z in ball x ((1 - ‖x‖) / 4), ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2) ^ 2) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := mul_le_mul_right (lintegral_mono_set hball) _
  have hpos : ENNReal.ofReal (π * ((1 - ‖x‖) / 4) ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  refine (ENNReal.mul_le_mul_iff_left hpos ENNReal.ofReal_ne_top).mp ?_
  calc ENNReal.ofReal (‖LiZhongQC.complexDilatation F x‖ ^ 2) * ENNReal.ofReal (π * ((1 - ‖x‖) / 4) ^ 2)
      = ENNReal.ofReal (‖LiZhongQC.complexDilatation F x‖ ^ 2 * (π * ((1 - ‖x‖) / 4) ^ 2)) :=
        (ENNReal.ofReal_mul (sq_nonneg _)).symm
    _ ≤ ENNReal.ofReal (100 * ((1 - ‖x‖) / 4) ^ 2) *
          ∫⁻ w in {w | w ∈ unitDisc ∧ diskCoshDist w x₀ < 5},
            ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2) := (hx hx𝔻).trans hI
    _ ≤ ENNReal.ofReal (32 * (π * ((1 - ‖x‖) / 4) ^ 2)) *
          ∫⁻ w in {w | w ∈ unitDisc ∧ diskCoshDist w x₀ < 5},
            ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_gt_d2, sq_nonneg (1 - ‖x‖)])) le_rfl
    _ = 32 * (∫⁻ w in {w | w ∈ unitDisc ∧ diskCoshDist w x₀ < 5},
            ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2)) * ENNReal.ofReal (π * ((1 - ‖x‖) / 4) ^ 2) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        ring

/-- B10 (sup bound): `a ≤ ε₀` on `𝔻` gives `∫_{D(x₀)} a²/(1 - |w|²)² ≤ 8000 ε₀²` (B7: `D(x₀)` lies in a disc of
radius `5(1 - |x₀|²)` on which `1 - |w|² ≥ (1 - |x₀|²)/10`). -/
theorem s07c_fkps_m6_rn_bd {a : ℂ → ℝ} {ε₀ : ℝ} (ha0 : ∀ z, 0 ≤ a z) (hale : ∀ z ∈ unitDisc, a z ≤ ε₀) :
    ∀ x₀ ∈ unitDisc, ∫⁻ w in {w | w ∈ unitDisc ∧ diskCoshDist w x₀ < 5},
      ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2) ≤ ENNReal.ofReal (8000 * ε₀ ^ 2) := by
  intro x₀ hx₀
  have hx1 : ‖x₀‖ < 1 := mem_ball_zero_iff.mp hx₀
  have hq : 0 < 1 - ‖x₀‖ ^ 2 := by nlinarith [norm_nonneg x₀]
  have hDm : MeasurableSet {w | w ∈ unitDisc ∧ diskCoshDist w x₀ < 5} := by
    have hmeas : Measurable fun w => diskCoshDist w x₀ := by
      show Measurable fun w => 1 + 2 * ‖w - x₀‖ ^ 2 / ((1 - ‖w‖ ^ 2) * (1 - ‖x₀‖ ^ 2))
      fun_prop
    exact measurableSet_ball.inter (measurableSet_lt hmeas measurable_const)
  have hpt : ∀ w ∈ {w | w ∈ unitDisc ∧ diskCoshDist w x₀ < 5},
      ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2) ≤
        ENNReal.ofReal (100 * ε₀ ^ 2 / (1 - ‖x₀‖ ^ 2) ^ 2) := by
    rintro w ⟨hw, hwd⟩
    obtain ⟨h1, -, -⟩ := s07c_fkps_m6_rn_hyp hw hx₀ hwd
    apply ENNReal.ofReal_le_ofReal
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have hp : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    have ha2 : a w ^ 2 ≤ ε₀ ^ 2 := pow_le_pow_left₀ (ha0 w) (hale w hw) 2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hq2 : (1 - ‖x₀‖ ^ 2) ^ 2 ≤ 100 * (1 - ‖w‖ ^ 2) ^ 2 := by nlinarith
    calc a w ^ 2 * (1 - ‖x₀‖ ^ 2) ^ 2 ≤ ε₀ ^ 2 * (100 * (1 - ‖w‖ ^ 2) ^ 2) :=
          mul_le_mul ha2 hq2 (sq_nonneg _) (sq_nonneg _)
      _ = 100 * ε₀ ^ 2 * (1 - ‖w‖ ^ 2) ^ 2 := by ring
  have hsub : {w | w ∈ unitDisc ∧ diskCoshDist w x₀ < 5} ⊆ closedBall x₀ (5 * (1 - ‖x₀‖ ^ 2)) := by
    rintro w ⟨hw, hwd⟩
    rw [mem_closedBall, dist_eq_norm]
    exact (s07c_fkps_m6_rn_hyp hw hx₀ hwd).2.2
  have hvol : volume (closedBall x₀ (5 * (1 - ‖x₀‖ ^ 2))) =
      ENNReal.ofReal (π * (5 * (1 - ‖x₀‖ ^ 2)) ^ 2) := by
    rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_coe_nnreal,
      NNReal.coe_real_pi, ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    ring
  calc ∫⁻ w in {w | w ∈ unitDisc ∧ diskCoshDist w x₀ < 5}, ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2)
      ≤ ∫⁻ w in {w | w ∈ unitDisc ∧ diskCoshDist w x₀ < 5},
          ENNReal.ofReal (100 * ε₀ ^ 2 / (1 - ‖x₀‖ ^ 2) ^ 2) := setLIntegral_mono' hDm hpt
    _ = ENNReal.ofReal (100 * ε₀ ^ 2 / (1 - ‖x₀‖ ^ 2) ^ 2) *
          volume {w | w ∈ unitDisc ∧ diskCoshDist w x₀ < 5} := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal (100 * ε₀ ^ 2 / (1 - ‖x₀‖ ^ 2) ^ 2) *
          volume (closedBall x₀ (5 * (1 - ‖x₀‖ ^ 2))) := mul_le_mul_right (measure_mono hsub) _
    _ = ENNReal.ofReal (100 * ε₀ ^ 2 / (1 - ‖x₀‖ ^ 2) ^ 2 * (π * (5 * (1 - ‖x₀‖ ^ 2)) ^ 2)) := by
        rw [hvol, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (8000 * ε₀ ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have e : 100 * ε₀ ^ 2 / (1 - ‖x₀‖ ^ 2) ^ 2 * (π * (5 * (1 - ‖x₀‖ ^ 2)) ^ 2) =
            2500 * π * ε₀ ^ 2 := by
          field_simp
          ring
        rw [e]
        nlinarith [Real.pi_lt_d2, sq_nonneg ε₀]

/-- B11 (measurability of the hyperbolic average, Mathlib `Measurable.lintegral_prod_right'`). -/
theorem s07c_fkps_m6_rn_meas {a : ℂ → ℝ} (ha : Measurable a) :
    Measurable fun x => ∫⁻ w in {w | w ∈ unitDisc ∧ diskCoshDist w x < 5},
      ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2) := by
  have hS : MeasurableSet {p : ℂ × ℂ | p.2 ∈ unitDisc ∧ diskCoshDist p.2 p.1 < 5} := by
    refine ((show MeasurableSet (ball (0 : ℂ) 1) from measurableSet_ball).preimage measurable_snd).inter
      (measurableSet_lt (f := fun p : ℂ × ℂ => diskCoshDist p.2 p.1) (g := fun _ => (5 : ℝ)) ?_ measurable_const)
    show Measurable fun p : ℂ × ℂ => 1 + 2 * ‖p.2 - p.1‖ ^ 2 / ((1 - ‖p.2‖ ^ 2) * (1 - ‖p.1‖ ^ 2))
    fun_prop
  have hg : Measurable fun w : ℂ => ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2) :=
    (by fun_prop : Measurable fun w : ℂ => a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2).ennreal_ofReal
  have hF : Measurable ({p : ℂ × ℂ | p.2 ∈ unitDisc ∧ diskCoshDist p.2 p.1 < 5}.indicator
      fun p : ℂ × ℂ => ENNReal.ofReal (a p.2 ^ 2 / (1 - ‖p.2‖ ^ 2) ^ 2)) :=
    (hg.comp measurable_snd).indicator hS
  have key : ∀ x : ℂ, ∫⁻ w in {w | w ∈ unitDisc ∧ diskCoshDist w x < 5},
      ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2) =
      ∫⁻ w, ({p : ℂ × ℂ | p.2 ∈ unitDisc ∧ diskCoshDist p.2 p.1 < 5}.indicator
        fun p : ℂ × ℂ => ENNReal.ofReal (a p.2 ^ 2 / (1 - ‖p.2‖ ^ 2) ^ 2)) (x, w) := by
    intro x
    rw [← lintegral_indicator (show MeasurableSet {w : ℂ | w ∈ unitDisc ∧ diskCoshDist w x < 5} from
      hS.preimage measurable_prodMk_left)]
    rfl
  simp_rw [key]
  exact hF.lintegral_prod_right'

/-- B12 helper (w4): `cosh d` is symmetric. -/
theorem s07c_fkps_m6_rn_w4_cd_symm (w x : ℂ) : diskCoshDist w x = diskCoshDist x w := by
  show 1 + 2 * ‖w - x‖ ^ 2 / ((1 - ‖w‖ ^ 2) * (1 - ‖x‖ ^ 2)) =
    1 + 2 * ‖x - w‖ ^ 2 / ((1 - ‖x‖ ^ 2) * (1 - ‖w‖ ^ 2))
  rw [norm_sub_rev, mul_comm (1 - ‖w‖ ^ 2)]

/-- B12 (Carleson norm of the hyperbolic average, Fubini as in M4 `s07c_fkps_m4_carl_aux`): `x ∈ D(w)` iff
`w ∈ D(x)`, `∫_{D(w)} (1 - |x|²)⁻¹ ≤ 250π(1 - |w|²)` and `D(w) ∩ B(ζ, r) ≠ ∅ ⇒ w ∈ B(ζ, 101 r)` (B7). -/
theorem s07c_fkps_m6_rn_carl0 {a : ℂ → ℝ} {ε : ℝ} (ha : Measurable a) (hε : 0 ≤ ε)
    (hC : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
        ≤ ENNReal.ofReal (ε * r)) :
    ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ x in unitDisc ∩ ball ζ r, ENNReal.ofReal (1 / (1 - ‖x‖ ^ 2)) *
        ∫⁻ w in {w | w ∈ unitDisc ∧ diskCoshDist w x < 5}, ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2)
        ≤ ENNReal.ofReal (80000 * ε * r) := by
  classical
  intro ζ hζ r hr0 hr2
  have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.1 hζ
  set S : Set ℂ := unitDisc ∩ ball ζ r with hS
  have hSm : MeasurableSet S := measurableSet_ball.inter measurableSet_ball
  set W : Set ℂ := unitDisc ∩ ball ζ (11 * r) with hW
  have hWm : MeasurableSet W := measurableSet_ball.inter measurableSet_ball
  set F : ℂ → ℂ → ℝ≥0∞ := fun x w =>
    if x ∈ S ∧ w ∈ unitDisc ∧ diskCoshDist w x < 5 then
      ENNReal.ofReal (1 / (1 - ‖x‖ ^ 2)) * ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2) else 0 with hF
  have hD : ∀ x : ℂ, MeasurableSet {w : ℂ | w ∈ unitDisc ∧ diskCoshDist w x < 5} := by
    intro x
    refine (show MeasurableSet (ball (0 : ℂ) 1) from measurableSet_ball).inter
      (measurableSet_lt (f := fun w : ℂ => diskCoshDist w x) (g := fun _ => (5 : ℝ)) ?_ measurable_const)
    show Measurable fun w : ℂ => 1 + 2 * ‖w - x‖ ^ 2 / ((1 - ‖w‖ ^ 2) * (1 - ‖x‖ ^ 2))
    fun_prop
  -- (a) the double integral, written with an indicator on `ℂ × ℂ`
  have h1 : ∫⁻ x in S, ENNReal.ofReal (1 / (1 - ‖x‖ ^ 2)) *
        ∫⁻ w in {w | w ∈ unitDisc ∧ diskCoshDist w x < 5}, ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2)
      = ∫⁻ x, ∫⁻ w, F x w := by
    rw [← lintegral_indicator hSm]
    refine lintegral_congr (fun x => ?_)
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_indicator (hD x)]
      refine lintegral_congr (fun w => ?_)
      by_cases hw : w ∈ {w : ℂ | w ∈ unitDisc ∧ diskCoshDist w x < 5}
      · rw [Set.indicator_of_mem hw, hF]
        simp only
        rw [if_pos ⟨hx, hw.1, hw.2⟩]
      · rw [Set.indicator_of_notMem hw, hF]
        simp only
        rw [if_neg (fun h => hw ⟨h.2.1, h.2.2⟩)]
    · rw [Set.indicator_of_notMem hx]
      have h0 : ∀ w, F x w = 0 := by
        intro w
        rw [hF]
        simp only
        rw [if_neg (fun h => hx h.1)]
      simp [h0]
  -- (b) Tonelli
  have hFm : Measurable (Function.uncurry F) := by
    show Measurable (fun p : ℂ × ℂ =>
      if p.1 ∈ S ∧ p.2 ∈ unitDisc ∧ diskCoshDist p.2 p.1 < 5 then
        ENNReal.ofReal (1 / (1 - ‖p.1‖ ^ 2)) * ENNReal.ofReal (a p.2 ^ 2 / (1 - ‖p.2‖ ^ 2) ^ 2) else 0)
    refine Measurable.ite ?_ ?_ measurable_const
    · refine (hSm.preimage measurable_fst).inter
        (((show MeasurableSet (ball (0 : ℂ) 1) from measurableSet_ball).preimage measurable_snd).inter
        (measurableSet_lt (f := fun p : ℂ × ℂ => diskCoshDist p.2 p.1) (g := fun _ => (5 : ℝ)) ?_
          measurable_const))
      show Measurable fun p : ℂ × ℂ => 1 + 2 * ‖p.2 - p.1‖ ^ 2 / ((1 - ‖p.2‖ ^ 2) * (1 - ‖p.1‖ ^ 2))
      fun_prop
    · exact (by fun_prop : Measurable fun p : ℂ × ℂ => 1 / (1 - ‖p.1‖ ^ 2)).ennreal_ofReal.mul
        ((by fun_prop : Measurable fun p : ℂ × ℂ => a p.2 ^ 2 / (1 - ‖p.2‖ ^ 2) ^ 2).ennreal_ofReal)
  -- (c) the inner integral in `x`, for fixed `w` (B7: `x ∈ D(w)` lies in `B̄(w, 5(1-|w|²))`, weight `≤ 10`)
  have h3 : ∀ w, ∫⁻ x, F x w ≤
      W.indicator (fun w => ENNReal.ofReal (250 * π * (a w ^ 2 / (1 - ‖w‖ ^ 2)))) w := by
    intro w
    by_cases hwW : w ∈ W
    · rw [Set.indicator_of_mem hwW]
      have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 (show w ∈ ball (0 : ℂ) 1 from hwW.1)
      have hρw : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
      have hq0 : 0 ≤ a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
      have hc0 : (0 : ℝ) ≤ 10 / (1 - ‖w‖ ^ 2) * (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2) :=
        mul_nonneg (div_pos (by norm_num) hρw).le hq0
      calc ∫⁻ x, F x w
          ≤ ∫⁻ x, (closedBall w (5 * (1 - ‖w‖ ^ 2))).indicator
              (fun _ => ENNReal.ofReal (10 / (1 - ‖w‖ ^ 2) * (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2))) x := by
            refine lintegral_mono (fun x => ?_)
            rw [hF]
            simp only
            split_ifs with hc
            · obtain ⟨hxS, hwD, hd⟩ := hc
              have hxD : x ∈ unitDisc := hxS.1
              have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.1 (show x ∈ ball (0 : ℂ) 1 from hxD)
              have hρx : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
              have hd' : diskCoshDist x w < 5 := by rw [s07c_fkps_m6_rn_w4_cd_symm]; exact hd
              obtain ⟨hA, -, hB⟩ := s07c_fkps_m6_rn_hyp hxD hwD hd'
              have hxb : x ∈ closedBall w (5 * (1 - ‖w‖ ^ 2)) := by
                rw [mem_closedBall, dist_eq_norm]; exact hB
              rw [Set.indicator_of_mem hxb, ← ENNReal.ofReal_mul (div_pos one_pos hρx).le]
              apply ENNReal.ofReal_le_ofReal
              refine mul_le_mul_of_nonneg_right ?_ hq0
              rw [div_le_div_iff₀ hρx hρw]
              linarith
            · exact zero_le
        _ = ENNReal.ofReal (10 / (1 - ‖w‖ ^ 2) * (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2)) *
              volume (closedBall w (5 * (1 - ‖w‖ ^ 2))) :=
            lintegral_indicator_const measurableSet_closedBall _
        _ = ENNReal.ofReal (10 / (1 - ‖w‖ ^ 2) * (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2) *
              ((5 * (1 - ‖w‖ ^ 2)) ^ 2 * π)) := by
            rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_coe_nnreal,
              NNReal.coe_real_pi, ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul hc0]
        _ = ENNReal.ofReal (250 * π * (a w ^ 2 / (1 - ‖w‖ ^ 2))) := by
            congr 1
            field_simp
            try ring
    · rw [Set.indicator_of_notMem hwW]
      have h0 : ∀ x, F x w = 0 := by
        intro x
        rw [hF]
        simp only
        refine if_neg (fun hc => ?_)
        obtain ⟨hxS, hwD, hd⟩ := hc
        apply hwW
        have hxD : x ∈ unitDisc := hxS.1
        have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.1 (show x ∈ ball (0 : ℂ) 1 from hxD)
        have hxζ : ‖x - ζ‖ < r := by
          have := hxS.2; rw [mem_ball, dist_eq_norm] at this; exact this
        obtain ⟨-, -, hwx⟩ := s07c_fkps_m6_rn_hyp hwD hxD hd
        have e3 := norm_sub_norm_le ζ x
        rw [norm_sub_rev ζ x, hζ1] at e3
        have hρx : 1 - ‖x‖ ^ 2 ≤ 2 * (1 - ‖x‖) := by nlinarith [norm_nonneg x]
        refine ⟨hwD, ?_⟩
        rw [mem_ball, dist_eq_norm]
        have e4 := norm_sub_le_norm_sub_add_norm_sub w x ζ
        linarith
      simp [h0]
  -- (d) the Carleson bound on the enlarged box `𝔻 ∩ B(ζ, 11 r)` (whole disc for `11 r ≥ 2`)
  have h5 : ∫⁻ w in W, ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2)) ≤ ENNReal.ofReal (17 * ε * r) := by
    rcases lt_or_ge (11 * r) 2 with hr | hr
    · calc ∫⁻ w in W, ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2))
          ≤ ENNReal.ofReal (ε * (11 * r)) := hC ζ hζ _ (by linarith) hr
        _ ≤ ENNReal.ofReal (17 * ε * r) := ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hε hr0.le])
    · calc ∫⁻ w in W, ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2))
          ≤ ∫⁻ z in unitDisc, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)) :=
            lintegral_mono_set inter_subset_left
        _ ≤ ∫⁻ z in (unitDisc ∩ ball (1 : ℂ) (3 / 2)) ∪ (unitDisc ∩ ball (-1 : ℂ) (3 / 2)),
              ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)) := lintegral_mono_set s07c_fkps_m4_cover
        _ ≤ (∫⁻ z in unitDisc ∩ ball (1 : ℂ) (3 / 2), ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))) +
              ∫⁻ z in unitDisc ∩ ball (-1 : ℂ) (3 / 2), ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2)) :=
            lintegral_union_le _ _ _
        _ ≤ ENNReal.ofReal (ε * (3 / 2)) + ENNReal.ofReal (ε * (3 / 2)) :=
            add_le_add (hC 1 (by simp) _ (by norm_num) (by norm_num))
              (hC (-1) (by simp) _ (by norm_num) (by norm_num))
        _ = ENNReal.ofReal (3 * ε) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring
        _ ≤ ENNReal.ofReal (17 * ε * r) :=
            ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hε (show (0 : ℝ) ≤ 11 * r - 2 by linarith)])
  -- (e) assembly: `250 π · 17 ≤ 80000`
  calc ∫⁻ x in S, ENNReal.ofReal (1 / (1 - ‖x‖ ^ 2)) *
        ∫⁻ w in {w | w ∈ unitDisc ∧ diskCoshDist w x < 5}, ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2)
      = ∫⁻ x, ∫⁻ w, F x w := h1
    _ = ∫⁻ w, ∫⁻ x, F x w := lintegral_lintegral_swap hFm.aemeasurable
    _ ≤ ∫⁻ w, W.indicator (fun w => ENNReal.ofReal (250 * π * (a w ^ 2 / (1 - ‖w‖ ^ 2)))) w :=
        lintegral_mono (fun w => h3 w)
    _ = ∫⁻ w in W, ENNReal.ofReal (250 * π * (a w ^ 2 / (1 - ‖w‖ ^ 2))) := lintegral_indicator hWm _
    _ = ENNReal.ofReal (250 * π) * ∫⁻ w in W, ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2)) := by
        simp_rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 250 * π)]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (250 * π) * ENNReal.ofReal (17 * ε * r) := mul_le_mul_right h5 _
    _ = ENNReal.ofReal (250 * π * (17 * ε * r)) := (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (80000 * ε * r) :=
        ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_le_four, mul_nonneg hε hr0.le])

/-- B13 helper (w4): the Poisson-type kernel in terms of `cosh d`:
`(1 - |c|²)/|1 - c̄ x|² = 2/((cosh d(c, x) + 1)(1 - |x|²))`. -/
theorem s07c_fkps_m6_rn_w4_kern {c x : ℂ} (hc : ‖c‖ < 1) (hx : ‖x‖ < 1) :
    (1 - ‖c‖ ^ 2) / ‖1 - conj c * x‖ ^ 2 = 2 / ((diskCoshDist c x + 1) * (1 - ‖x‖ ^ 2)) := by
  have hρc : 0 < 1 - ‖c‖ ^ 2 := by nlinarith [norm_nonneg c]
  have hρx : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  have hid : ‖1 - conj c * x‖ ^ 2 = ‖c - x‖ ^ 2 + (1 - ‖c‖ ^ 2) * (1 - ‖x‖ ^ 2) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
    ring
  have hs : 0 < ‖c - x‖ ^ 2 + (1 - ‖c‖ ^ 2) * (1 - ‖x‖ ^ 2) :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hρc hρx)
  show _ = 2 / ((1 + 2 * ‖c - x‖ ^ 2 / ((1 - ‖c‖ ^ 2) * (1 - ‖x‖ ^ 2)) + 1) * (1 - ‖x‖ ^ 2))
  rw [hid]
  have hρc' := hρc.ne'
  have hρx' := hρx.ne'
  have hs' := hs.ne'
  field_simp
  try ring

/-- B13 helper (w4): for `a, y ∈ 𝔻`, `(1 - |φ y|²)/(1 - |y|²) = |φ'(y)|` and the kernel identity
`P_a(y) = P_{φ a}(φ y) |φ'(y)|` (B4: `φ` preserves `cosh d`). -/
theorem s07c_fkps_m6_rn_w4_pullpt {z : ℂ} {φ : ℂ → ℂ} (hφ : ∀ y, φ y = (y + z) / (1 + conj z * y))
    (hz : z ∈ unitDisc) {a y : ℂ} (ha : a ∈ unitDisc) (hy : y ∈ unitDisc) :
    (1 - ‖φ y‖ ^ 2) / (1 - ‖y‖ ^ 2) = (1 - ‖z‖ ^ 2) / ‖1 + conj z * y‖ ^ 2 ∧
    (1 - ‖a‖ ^ 2) / ‖1 - conj a * y‖ ^ 2 =
      (1 - ‖φ a‖ ^ 2) / ‖1 - conj (φ a) * φ y‖ ^ 2 * ((1 - ‖z‖ ^ 2) / ‖1 + conj z * y‖ ^ 2) := by
  have hy1 : ‖y‖ < 1 := mem_ball_zero_iff.1 hy
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.1 ha
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  obtain ⟨hφa, hcd, -⟩ := s07c_fkps_m6_rn_inv hφ hz ha hy
  obtain ⟨hφy, -, hρ⟩ := s07c_fkps_m6_rn_inv hφ hz hy hy
  have hρy : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
  have hρa : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hρz : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hdz : 0 < ‖1 + conj z * y‖ ^ 2 := pow_pos (norm_pos_iff.2 (s07c_fkps_m6_rn_w4_den hz1 hy1).1) 2
  have hρy' := hρy.ne'
  have hρz' := hρz.ne'
  have hdz' := hdz.ne'
  have hdn : ‖1 + conj z * y‖ ≠ 0 := norm_ne_zero_iff.2 (s07c_fkps_m6_rn_w4_den hz1 hy1).1
  have hR : (1 - ‖φ y‖ ^ 2) / (1 - ‖y‖ ^ 2) = (1 - ‖z‖ ^ 2) / ‖1 + conj z * y‖ ^ 2 := by
    rw [hρ]
    field_simp
  refine ⟨hR, ?_⟩
  have hφy' : 1 - ‖φ y‖ ^ 2 = (1 - ‖z‖ ^ 2) / ‖1 + conj z * y‖ ^ 2 * (1 - ‖y‖ ^ 2) := by
    rw [hρ]
    ring
  have hq : 0 ≤ 2 * ‖a - y‖ ^ 2 / ((1 - ‖a‖ ^ 2) * (1 - ‖y‖ ^ 2)) :=
    div_nonneg (by positivity) (mul_pos hρa hρy).le
  have hcd1 : 0 < diskCoshDist a y + 1 := by
    show 0 < 1 + 2 * ‖a - y‖ ^ 2 / ((1 - ‖a‖ ^ 2) * (1 - ‖y‖ ^ 2)) + 1
    linarith
  have hcd1' := hcd1.ne'
  rw [s07c_fkps_m6_rn_w4_kern ha1 hy1,
    s07c_fkps_m6_rn_w4_kern (mem_ball_zero_iff.1 hφa) (mem_ball_zero_iff.1 hφy), hcd, hφy']
  field_simp

/-- B13 (Möbius invariance of Carleson measures): the pull-back `g(φ_z y) (1 - |φ_z y|²)/(1 - |y|²) dA(y)` of a
Carleson measure `g dA` of norm `C` has norm `≤ 432 C` (S02 `s02_vc_kernel_bound`, `s02_vc_box_le`; the kernel
identity `P_{φ_z w}(φ_z y) |φ_z'(y)| = P_w(y)` from B4 and B5). -/
theorem s07c_fkps_m6_rn_mobcarl {g : ℂ → ℝ} {C : ℝ} (hgm : Measurable g) (hC0 : 0 ≤ C)
    (hC : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ x in unitDisc ∩ ball ζ r, ENNReal.ofReal (g x) ≤ ENNReal.ofReal (C * r))
    {z : ℂ} {φ : ℂ → ℂ} (hφ : ∀ y, φ y = (y + z) / (1 + conj z * y)) (hz : z ∈ unitDisc) :
    ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ y in unitDisc ∩ ball ζ r, ENNReal.ofReal (g (φ y) * ((1 - ‖φ y‖ ^ 2) / (1 - ‖y‖ ^ 2)))
        ≤ ENNReal.ofReal (432 * C * r) := by
  intro ζ hζ r hr0 hr2
  have hφfun : φ = fun v => (v + z) / (1 + conj z * v) := funext hφ
  have hφm : Measurable φ := by
    rw [hφfun]
    exact (measurable_id.add_const z).div (measurable_const.add (measurable_const.mul measurable_id))
  have hU : MeasurableSet (unitDisc : Set ℂ) := measurableSet_ball
  have hBm : ∀ (ξ : ℂ) (s : ℝ), MeasurableSet (unitDisc ∩ ball ξ s) :=
    fun _ _ => measurableSet_ball.inter measurableSet_ball
  set H : ℂ → ℝ≥0∞ := fun y => ENNReal.ofReal (g (φ y) * ((1 - ‖φ y‖ ^ 2) / (1 - ‖y‖ ^ 2))) with hH
  have hHm : Measurable H :=
    ((hgm.comp hφm).mul (by fun_prop : Measurable fun y => (1 - ‖φ y‖ ^ 2) / (1 - ‖y‖ ^ 2))).ennreal_ofReal
  have hgm' : Measurable fun x => ENNReal.ofReal (g x) := hgm.ennreal_ofReal
  -- the Carleson measure `ν = g dA`
  have hν : ∀ ξ ∈ sphere (0 : ℂ) 1, ∀ s : ℝ, 0 < s → s < 2 →
      volume.withDensity (fun x => ENNReal.ofReal (g x)) (unitDisc ∩ ball ξ s) ≤ ENNReal.ofReal (C * s) := by
    intro ξ hξ s hs0 hs2
    rw [withDensity_apply _ (hBm ξ s)]
    exact hC ξ hξ s hs0 hs2
  -- kernel bound for the pull-back `λ = H dA`, via B5 and `P_a(y) = P_{φ a}(φ y) |φ'(y)|`
  have key : ∀ a ∈ unitDisc, ∫⁻ y in unitDisc, ENNReal.ofReal ((1 - ‖a‖ ^ 2) / ‖1 - conj a * y‖ ^ 2)
      ∂(volume.withDensity H) ≤ ENNReal.ofReal (108 * C) := by
    intro a ha
    have hb := (s07c_fkps_m6_rn_inv hφ hz ha ha).1
    have hK := s02_vc_kernel_bound (μ := volume.withDensity (fun x => ENNReal.ofReal (g x))) hC0 hν
      (mem_ball_zero_iff.1 hb)
    refine le_trans (le_of_eq ?_) hK
    calc ∫⁻ y in unitDisc, ENNReal.ofReal ((1 - ‖a‖ ^ 2) / ‖1 - conj a * y‖ ^ 2) ∂(volume.withDensity H)
        = ∫⁻ y in unitDisc, H y * ENNReal.ofReal ((1 - ‖a‖ ^ 2) / ‖1 - conj a * y‖ ^ 2) := by
          rw [restrict_withDensity hU, lintegral_withDensity_eq_lintegral_mul _ hHm (by fun_prop)]
          rfl
      _ = ∫⁻ y in unitDisc, ENNReal.ofReal (((1 - ‖z‖ ^ 2) / ‖1 + conj z * y‖ ^ 2) ^ 2) *
            (ENNReal.ofReal (g (φ y)) * ENNReal.ofReal ((1 - ‖φ a‖ ^ 2) / ‖1 - conj (φ a) * φ y‖ ^ 2)) := by
          refine setLIntegral_congr_fun hU (fun y hy => ?_)
          obtain ⟨hR, hK'⟩ := s07c_fkps_m6_rn_w4_pullpt hφ hz ha hy
          have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
          have hJ0 : 0 ≤ (1 - ‖z‖ ^ 2) / ‖1 + conj z * y‖ ^ 2 :=
            div_nonneg (by nlinarith [norm_nonneg z]) (sq_nonneg _)
          show ENNReal.ofReal (g (φ y) * ((1 - ‖φ y‖ ^ 2) / (1 - ‖y‖ ^ 2))) *
              ENNReal.ofReal ((1 - ‖a‖ ^ 2) / ‖1 - conj a * y‖ ^ 2) =
            ENNReal.ofReal (((1 - ‖z‖ ^ 2) / ‖1 + conj z * y‖ ^ 2) ^ 2) *
              (ENNReal.ofReal (g (φ y)) * ENNReal.ofReal ((1 - ‖φ a‖ ^ 2) / ‖1 - conj (φ a) * φ y‖ ^ 2))
          rw [hR, hK', ENNReal.ofReal_mul' hJ0, ENNReal.ofReal_mul' hJ0, ENNReal.ofReal_pow hJ0]
          ring
      _ = ∫⁻ x in unitDisc, ENNReal.ofReal (g x) *
            ENNReal.ofReal ((1 - ‖φ a‖ ^ 2) / ‖1 - conj (φ a) * x‖ ^ 2) :=
          (s07c_fkps_m6_rn_cov hφ hz (fun x => ENNReal.ofReal (g x) *
            ENNReal.ofReal ((1 - ‖φ a‖ ^ 2) / ‖1 - conj (φ a) * x‖ ^ 2))).symm
      _ = ∫⁻ x in unitDisc, ENNReal.ofReal ((1 - ‖φ a‖ ^ 2) / ‖1 - conj (φ a) * x‖ ^ 2)
            ∂(volume.withDensity (fun x => ENNReal.ofReal (g x))) := by
          rw [restrict_withDensity hU, lintegral_withDensity_eq_lintegral_mul _ hgm' (by fun_prop)]
          rfl
  -- boxes: `s02_vc_box_le` for `r < 1`, the whole disc (`a = 0`) for `r ≥ 1`
  rcases lt_or_ge r 1 with hr1 | hr1
  · have hξr := s02_vc_box_le (μ := volume.withDensity H) hζ hr0 hr1
    have ha : (((1 - r : ℝ) : ℂ) * ζ) ∈ unitDisc := by
      refine mem_ball_zero_iff.2 ?_
      rw [norm_mul, Complex.norm_of_nonneg (by linarith), mem_sphere_zero_iff_norm.1 hζ]
      linarith
    rw [withDensity_apply _ (hBm ζ r)] at hξr
    calc ∫⁻ y in unitDisc ∩ ball ζ r, H y
        ≤ ENNReal.ofReal (4 * r) * ∫⁻ y in unitDisc,
            ENNReal.ofReal ((1 - ‖((1 - r : ℝ) : ℂ) * ζ‖ ^ 2) / ‖1 - conj (((1 - r : ℝ) : ℂ) * ζ) * y‖ ^ 2)
            ∂(volume.withDensity H) := hξr
      _ ≤ ENNReal.ofReal (4 * r) * ENNReal.ofReal (108 * C) := mul_le_mul_right (key _ ha) _
      _ = ENNReal.ofReal (432 * C * r) := by
          rw [← ENNReal.ofReal_mul (by linarith)]
          congr 1
          ring
  · have hb := key 0 (mem_ball_self one_pos)
    calc ∫⁻ y in unitDisc ∩ ball ζ r, H y
        ≤ ∫⁻ y in unitDisc, H y := lintegral_mono_set inter_subset_left
      _ = ∫⁻ y in unitDisc, ENNReal.ofReal ((1 - ‖(0 : ℂ)‖ ^ 2) / ‖1 - conj (0 : ℂ) * y‖ ^ 2)
            ∂(volume.withDensity H) := by
          rw [restrict_withDensity hU, lintegral_withDensity_eq_lintegral_mul _ hHm (by fun_prop)]
          refine lintegral_congr (fun y => ?_)
          simp
      _ ≤ ENNReal.ofReal (108 * C) := hb
      _ ≤ ENNReal.ofReal (432 * C * r) :=
          ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hC0 (sub_nonneg.2 hr1)])

/-- M6.B (block output, Möbius renormalisation): for `z ∈ 𝔻` the conjugate `G = φ_{F z}⁻¹ ∘ F ∘ φ_z`
(`φ_c(y) = (y + c)/(1 + c̄ y)`), extended by reflection, is again in the SMALL class with constants `C ε₀`, `C ε`:
`|μ_G| = |μ_F| ∘ φ_z` a.e. on `𝔻`; the new majorant is a Whitney average of `(a ∘ φ_z)²` over `𝔻 ∩ B(y, 2δ_y)`;
its Carleson norm is controlled by Möbius invariance (`s02_vc_kernel_bound`, `s02_vc_box_le`). -/
theorem s07c_fkps_m6_renorm : ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : ℂ → ℂ) (a : ℂ → ℝ) (K ε₀ ε : ℝ),
    IsKQC F univ K → F '' univ = univ → F '' unitDisc = unitDisc → F 0 = 0 →
    Measurable a → (∀ z, 0 ≤ a z) → (∀ z ∈ unitDisc, a z ≤ ε₀) →
    (∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) →
      ‖LiZhongQC.complexDilatation F w‖ ≤ a z) →
    0 ≤ ε →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
        ≤ ENNReal.ofReal (ε * r)) →
    ∀ z ∈ unitDisc, ∃ (G : ℂ → ℂ) (b : ℂ → ℝ),
      IsKQC G univ K ∧ G '' univ = univ ∧ G '' unitDisc = unitDisc ∧ G 0 = 0 ∧
      Measurable b ∧ (∀ y, 0 ≤ b y) ∧ (∀ y ∈ unitDisc, b y ≤ C * ε₀) ∧
      (∀ y ∈ unitDisc, ∀ᵐ w, w ∈ ball y ((1 - ‖y‖) / 2) →
        ‖LiZhongQC.complexDilatation G w‖ ≤ b y) ∧
      (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
        ∫⁻ y in unitDisc ∩ ball ζ r, ENNReal.ofReal (b y ^ 2 / (1 - ‖y‖ ^ 2))
          ≤ ENNReal.ofReal (C * ε * r)) ∧
      ∀ y ∈ closedBall (0 : ℂ) 1,
        F ((y + z) / (1 + conj z * y)) = (G y + F z) / (1 + conj (F z) * G y) := by
  refine ⟨2 * 10 ^ 9, by norm_num, ?_⟩
  intro F a K ε₀ ε hF _hFs hFD _hF0 ha ha0 hale hW hε hC z hz
  -- `_hFs`, `_hF0` are not needed: `G` is built from `F` on `𝔻̄` only and normalised by `φ_{F z}⁻¹`
  obtain ⟨φ, hφe⟩ : ∃ φ : ℂ → ℂ, φ = fun y => (y + z) / (1 + conj z * y) := ⟨_, rfl⟩
  have hφ : ∀ y, φ y = (y + z) / (1 + conj z * y) := fun y => by rw [hφe]
  have hφm : Measurable φ := by
    rw [hφe]
    exact (measurable_id.add measurable_const).div (measurable_const.add (measurable_const.mul measurable_id))
  obtain ⟨G, hGK, hGs, hGD, hG0, hGf, hid⟩ := s07c_fkps_m6_rn_conj hφ hF hFD hz
  have hFmap : MapsTo F unitDisc unitDisc := fun x hx => hFD ▸ mem_image_of_mem F hx
  have hFz : F z ∈ unitDisc := hFmap hz
  have hdil := s07c_fkps_m6_rn_dil hφ hz hFz hFmap hGf
  -- the hyperbolic average `L` and the majorant `b = √(32 L ∘ φ)`
  obtain ⟨L, hL⟩ : ∃ L : ℂ → ℝ≥0∞, L = fun x => ∫⁻ w in {w | w ∈ unitDisc ∧ diskCoshDist w x < 5},
      ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2) := ⟨_, rfl⟩
  have hLx : ∀ x, L x = ∫⁻ w in {w | w ∈ unitDisc ∧ diskCoshDist w x < 5},
      ENNReal.ofReal (a w ^ 2 / (1 - ‖w‖ ^ 2) ^ 2) := fun x => by rw [hL]
  have hLm : Measurable L := by
    rw [hL]
    exact s07c_fkps_m6_rn_meas ha
  have hε₀ : 0 ≤ ε₀ := (ha0 0).trans (hale 0 (mem_ball_self one_pos))
  have hLbd : ∀ x ∈ unitDisc, L x ≤ ENNReal.ofReal (8000 * ε₀ ^ 2) := fun x hx => by
    rw [hLx]
    exact s07c_fkps_m6_rn_bd ha0 hale x hx
  have hLfin : ∀ x ∈ unitDisc, L x ≠ ⊤ := fun x hx => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hLbd x hx)
  obtain ⟨b, hb⟩ : ∃ b : ℂ → ℝ, b = fun y => Real.sqrt (32 * (L (φ y)).toReal) := ⟨_, rfl⟩
  have hby : ∀ y, b y = Real.sqrt (32 * (L (φ y)).toReal) := fun y => by rw [hb]
  have hbm : Measurable b := by
    rw [hb]
    exact ((ENNReal.measurable_toReal.comp (hLm.comp hφm)).const_mul 32).sqrt
  have hb2 : ∀ y, b y ^ 2 = 32 * (L (φ y)).toReal := fun y => by
    rw [hby, Real.sq_sqrt (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)]
  refine ⟨G, b, hGK, hGs, hGD, hG0, hbm, fun y => by rw [hby]; exact Real.sqrt_nonneg _, ?_, ?_, ?_, ?_⟩
  · -- sup bound
    intro y hy
    have hφy := (s07c_fkps_m6_rn_inv hφ hz hy hy).1
    have h1 : (L (φ y)).toReal ≤ 8000 * ε₀ ^ 2 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hLbd _ hφy)
    have hC0 : 0 ≤ 2 * 10 ^ 9 * ε₀ := mul_nonneg (by norm_num) hε₀
    rw [hby, ← Real.sqrt_sq hC0]
    exact Real.sqrt_le_sqrt (by nlinarith)
  · -- Whitney bound for `G`
    intro y hy
    have hφy := (s07c_fkps_m6_rn_inv hφ hz hy hy).1
    have hwh := s07c_fkps_m6_rn_whit ha hW (φ y) hφy
    have hnull := s07c_fkps_m6_rn_null hφ hz (ae_iff.mp hwh)
    rw [ae_iff]
    refine measure_mono_null ?_ hnull
    intro w hw
    have hw' : ¬ (w ∈ ball y ((1 - ‖y‖) / 2) → ‖LiZhongQC.complexDilatation G w‖ ≤ b y) := hw
    rw [not_imp] at hw'
    obtain ⟨hwb, hwlt⟩ := hw'
    obtain ⟨hw𝔻, hwc⟩ := s07c_fkps_m6_rn_wb hy hwb
    refine ⟨hw𝔻, fun hP => hwlt ?_⟩
    have hinv := s07c_fkps_m6_rn_inv hφ hz hw𝔻 hy
    have h1 := hP hinv.1 (by rw [hinv.2.1]; exact hwc)
    rw [← hLx] at h1
    have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (hLfin _ hφy)) h1
    rw [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul, ENNReal.toReal_ofNat] at h3
    rw [hdil w hw𝔻, hby]
    exact (le_abs_self _).trans (Real.abs_le_sqrt h3)
  · -- Carleson bound for `b`
    have hg : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
        ∫⁻ x in unitDisc ∩ ball ζ r, ENNReal.ofReal (32 * (L x).toReal / (1 - ‖x‖ ^ 2)) ≤
          ENNReal.ofReal (32 * 80000 * ε * r) := by
      intro ζ hζ r hr0 hr2
      have h := s07c_fkps_m6_rn_carl0 ha hε hC ζ hζ r hr0 hr2
      simp only [← hLx] at h
      calc ∫⁻ x in unitDisc ∩ ball ζ r, ENNReal.ofReal (32 * (L x).toReal / (1 - ‖x‖ ^ 2))
          = ∫⁻ x in unitDisc ∩ ball ζ r, ENNReal.ofReal 32 * (ENNReal.ofReal (1 / (1 - ‖x‖ ^ 2)) * L x) := by
            refine setLIntegral_congr_fun (measurableSet_ball.inter measurableSet_ball) fun x hx => ?_
            have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx.1
            have hq : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
            rw [← ENNReal.ofReal_toReal (hLfin x hx.1), ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (by norm_num), ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
            congr 1
            field_simp
        _ = ENNReal.ofReal 32 * ∫⁻ x in unitDisc ∩ ball ζ r, ENNReal.ofReal (1 / (1 - ‖x‖ ^ 2)) * L x :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal 32 * ENNReal.ofReal (80000 * ε * r) := mul_le_mul_right h _
        _ = ENNReal.ofReal (32 * 80000 * ε * r) := by
            rw [← ENNReal.ofReal_mul (by norm_num)]
            ring_nf
    have hmc := s07c_fkps_m6_rn_mobcarl (g := fun x => 32 * (L x).toReal / (1 - ‖x‖ ^ 2))
      (C := 32 * 80000 * ε)
      (((ENNReal.measurable_toReal.comp hLm).const_mul 32).div
        (measurable_const.sub (measurable_norm.pow_const 2))) (mul_nonneg (by norm_num) hε) hg hφ hz
    intro ζ hζ r hr0 hr2
    calc ∫⁻ y in unitDisc ∩ ball ζ r, ENNReal.ofReal (b y ^ 2 / (1 - ‖y‖ ^ 2))
        = ∫⁻ y in unitDisc ∩ ball ζ r, ENNReal.ofReal (32 * (L (φ y)).toReal / (1 - ‖φ y‖ ^ 2) *
            ((1 - ‖φ y‖ ^ 2) / (1 - ‖y‖ ^ 2))) := by
          refine setLIntegral_congr_fun (measurableSet_ball.inter measurableSet_ball) fun y hy => ?_
          have hφy := (s07c_fkps_m6_rn_inv hφ hz hy.1 hy.1).1
          have hq : 0 < 1 - ‖φ y‖ ^ 2 := by
            have := mem_ball_zero_iff.mp hφy
            nlinarith [norm_nonneg (φ y)]
          rw [hb2]
          congr 1
          field_simp
      _ ≤ ENNReal.ofReal (432 * (32 * 80000 * ε) * r) := hmc ζ hζ r hr0 hr2
      _ ≤ ENNReal.ofReal (2 * 10 ^ 9 * ε * r) := by
          apply ENNReal.ofReal_le_ofReal
          nlinarith [mul_nonneg hε hr0.le]
  · -- the conjugation identity on `𝔻̄`
    intro y hy
    rw [← hφ y]
    exact hid y hy

/-! ## Block C internal stubs (w6 DRAFT)

Notation used inline (no new definitions): for `‖c‖ < 1`,
`Φ_c t = t + 2 arg (1 + c e^{-it})` is the lift of `φ_c y = (y + c)/(1 + c̄ y)` on `∂𝔻`, and
`P_c t = (1 - ‖c‖²)/‖e^{it} + c‖²` is its derivative. -/

/-! ### C1: Möbius lift calculus, log-Lipschitz bounds, densities, positional lemma -/

/-- C1.1 (lift of `φ_c`): `φ_c(e^{it}) = e^{iΦ_c t}`, `Φ_c' = P_c > 0`, `Φ_c` strictly increasing and
`2π`-equivariant (S07 `s07_mob_lift`, `s07_mob_hasDerivAt` with `a = -c`). -/
theorem s07c_fkps_m6_mob {c : ℂ} (hc : ‖c‖ < 1) :
    (∀ t : ℝ, (Complex.exp (t * I) + c) / (1 + conj c * Complex.exp (t * I)) =
      Complex.exp (((t + 2 * arg (1 + c * Complex.exp (-(t * I))) : ℝ) : ℂ) * I)) ∧
    (∀ t : ℝ, HasDerivAt (fun t : ℝ => t + 2 * arg (1 + c * Complex.exp (-(t * I))))
      ((1 - ‖c‖ ^ 2) / ‖Complex.exp (t * I) + c‖ ^ 2) t) ∧
    (∀ t : ℝ, 0 < (1 - ‖c‖ ^ 2) / ‖Complex.exp (t * I) + c‖ ^ 2) ∧
    StrictMono (fun t : ℝ => t + 2 * arg (1 + c * Complex.exp (-(t * I)))) ∧
    (∀ t : ℝ, (t + 2 * π) + 2 * arg (1 + c * Complex.exp (-((t + 2 * π : ℝ) * I))) =
      (t + 2 * arg (1 + c * Complex.exp (-(t * I)))) + 2 * π) := by
  have hc' : ‖-c‖ < 1 := by rwa [norm_neg]
  have hfun : (fun t : ℝ => t + 2 * arg (1 + c * Complex.exp (-(t * I)))) =
      fun t : ℝ => 0 + t + 2 * arg (1 - (-c) * Complex.exp (-(t * I))) := by
    funext t
    rw [neg_mul, sub_neg_eq_add, zero_add]
  have hder : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t + 2 * arg (1 + c * Complex.exp (-(t * I))))
      ((1 - ‖c‖ ^ 2) / ‖Complex.exp (t * I) + c‖ ^ 2) t := by
    intro t
    have h := s07_mob_hasDerivAt hc' 0 t
    rw [← hfun, norm_neg, sub_neg_eq_add] at h
    exact h
  have hpos : ∀ t : ℝ, 0 < (1 - ‖c‖ ^ 2) / ‖Complex.exp (t * I) + c‖ ^ 2 := by
    intro t
    have h1 : 0 < 1 - ‖c‖ ^ 2 := by nlinarith [norm_nonneg c]
    have h2 : Complex.exp (t * I) + c ≠ 0 := by
      intro h
      have h3 : ‖Complex.exp (t * I)‖ = ‖c‖ := by rw [eq_neg_of_add_eq_zero_left h, norm_neg]
      rw [Complex.norm_exp_ofReal_mul_I] at h3
      linarith
    have h4 : 0 < ‖Complex.exp (t * I) + c‖ := norm_pos_iff.mpr h2
    positivity
  refine ⟨fun t => ?_, hder, hpos, strictMono_of_hasDerivAt_pos hder hpos, fun t => ?_⟩
  · have h := s07_mob_lift hc' 0 t
    have hL : diskMobius 0 (-c) (Complex.exp (t * I)) =
        (Complex.exp (t * I) + c) / (1 + conj c * Complex.exp (t * I)) := by
      simp [diskMobius]
    rw [hL] at h
    simpa only [zero_add, neg_mul, sub_neg_eq_add] using h
  · have he : Complex.exp (-(((t + 2 * π : ℝ) : ℂ) * I)) = Complex.exp (-(t * I)) := by
      rw [show -(((t + 2 * π : ℝ) : ℂ) * I) = -(t * I) - 2 * π * I by push_cast; ring,
        Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
    rw [he]
    ring

/-- C1.2 (cosine form): if `-c = ‖c‖ e^{iτ_c}` then `‖e^{iτ} + c‖² = 1 + ‖c‖² - 2‖c‖ cos(τ - τ_c)`. -/
theorem s07c_fkps_m6_mob_cos (c : ℂ) (τc τ : ℝ) (hc : -c = (‖c‖ : ℂ) * Complex.exp (τc * I)) :
    ‖Complex.exp (τ * I) + c‖ ^ 2 = 1 + ‖c‖ ^ 2 - 2 * ‖c‖ * Real.cos (τ - τc) := by
  set r : ℝ := ‖c‖ with hr
  have hsub : Complex.exp (τ * I) + c = Complex.exp (τ * I) - (r : ℂ) * Complex.exp (τc * I) := by
    rw [← hc]
    ring
  rw [hsub, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero,
    add_zero]
  rw [Real.cos_sub]
  linear_combination Real.sin_sq_add_cos_sq τ + r ^ 2 * Real.sin_sq_add_cos_sq τc

/-- C1.3 (log-Lipschitz bound for `P_c`): if `‖e^{ix} + c‖ ≥ m` between `t` and `t'`, then
`P_c t' ≤ e^{2|t' - t|/m} P_c t` (`|∂_x log ‖e^{ix} + c‖²| ≤ 2/‖e^{ix} + c‖`). -/
theorem s07c_fkps_m6_mob_loglip {c : ℂ} (hc : ‖c‖ < 1) {m t t' : ℝ} (hm : 0 < m)
    (hmt : ∀ x ∈ uIcc t t', m ≤ ‖Complex.exp (x * I) + c‖) :
    (1 - ‖c‖ ^ 2) / ‖Complex.exp (t' * I) + c‖ ^ 2 ≤
      Real.exp (2 * |t' - t| / m) * ((1 - ‖c‖ ^ 2) / ‖Complex.exp (t * I) + c‖ ^ 2) := by
  have hA : 0 < 1 - ‖c‖ ^ 2 := by nlinarith [norm_nonneg c]
  have hg : m ≤ ‖Complex.exp (t * I) + c‖ := hmt t left_mem_uIcc
  have hg' : m ≤ ‖Complex.exp (t' * I) + c‖ := hmt t' right_mem_uIcc
  set g := ‖Complex.exp (t * I) + c‖ with hgdef
  set g' := ‖Complex.exp (t' * I) + c‖ with hg'def
  have hgp : 0 < g := hm.trans_le hg
  have hgp' : 0 < g' := hm.trans_le hg'
  have hlip : g ≤ g' + |t' - t| := by
    have h1 : g ≤ g' + ‖Complex.exp (t * I) - Complex.exp (t' * I)‖ := by
      calc g = ‖(Complex.exp (t' * I) + c) + (Complex.exp (t * I) - Complex.exp (t' * I))‖ := by
            rw [hgdef]; ring_nf
        _ ≤ _ := norm_add_le _ _
    have h2 := s07c_fkps_m4_exp_dist t t'
    rw [abs_sub_comm] at h2
    linarith
  set d := |t' - t| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  have hq : g ≤ g' * Real.exp (d / m) := by
    have h1 : 1 + d / m ≤ Real.exp (d / m) := by linarith [Real.add_one_le_exp (d / m)]
    have h2 : d ≤ g' * (d / m) := by
      rw [mul_div_assoc', le_div_iff₀ hm]
      nlinarith
    have h3 : g' * (1 + d / m) ≤ g' * Real.exp (d / m) := mul_le_mul_of_nonneg_left h1 hgp'.le
    nlinarith
  have hsq : g ^ 2 ≤ g' ^ 2 * Real.exp (2 * d / m) := by
    have he : Real.exp (2 * d / m) = Real.exp (d / m) ^ 2 := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [he, ← mul_pow]
    exact pow_le_pow_left₀ hgp.le hq 2
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left hsq hA.le
  nlinarith

/-- C1.4 (Poisson box): for `z = r e^{is₀}`, `0 ≤ r < 1`: `‖z‖ = r`, `Φ_z s₀ = s₀`, `‖e^{i(s₀+x)} + z‖ ≥ 1` and
`(1 - r²)/4 ≤ P_z(s₀ + x)` for `|x| ≤ π/2`, and `P_z(s₀ + x) ≤ 2(1 - r²)` for `|x| ≤ 2π/3`. -/
theorem s07c_fkps_m6_poisson_box {r s₀ : ℝ} {z : ℂ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hz : z = (r : ℂ) * Complex.exp (s₀ * I)) :
    ‖z‖ = r ∧ s₀ + 2 * arg (1 + z * Complex.exp (-(s₀ * I))) = s₀ ∧
    (∀ x : ℝ, |x| ≤ π / 2 → 1 ≤ ‖Complex.exp ((s₀ + x : ℝ) * I) + z‖) ∧
    (∀ x : ℝ, |x| ≤ π / 2 →
      (1 - r ^ 2) / 4 ≤ (1 - ‖z‖ ^ 2) / ‖Complex.exp ((s₀ + x : ℝ) * I) + z‖ ^ 2) ∧
    (∀ x : ℝ, |x| ≤ 2 * π / 3 →
      (1 - ‖z‖ ^ 2) / ‖Complex.exp ((s₀ + x : ℝ) * I) + z‖ ^ 2 ≤ 2 * (1 - r ^ 2)) := by
  have hzn : ‖z‖ = r := by
    rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hcz : -z = ((‖z‖ : ℝ) : ℂ) * Complex.exp (((s₀ + π : ℝ) : ℂ) * I) := by
    rw [hzn, hz]
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hN : ∀ x : ℝ, ‖Complex.exp ((s₀ + x : ℝ) * I) + z‖ ^ 2 = 1 + r ^ 2 + 2 * r * Real.cos x := by
    intro x
    rw [s07c_fkps_m6_mob_cos z (s₀ + π) (s₀ + x) hcz, hzn,
      show s₀ + x - (s₀ + π) = x - π by ring, Real.cos_sub_pi]
    ring
  have hr2 : 0 ≤ 1 - r ^ 2 := by nlinarith
  refine ⟨hzn, ?_, ?_, ?_, ?_⟩
  · have : (1 : ℂ) + z * Complex.exp (-(s₀ * I)) = ((1 + r : ℝ) : ℂ) := by
      rw [hz, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
      push_cast
      ring
    rw [this, Complex.arg_ofReal_of_nonneg (by linarith)]
    ring
  · intro x hx
    have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc ⟨by linarith [neg_abs_le x],
      by linarith [le_abs_self x]⟩
    have h := hN x
    have h0 := norm_nonneg (Complex.exp ((s₀ + x : ℝ) * I) + z)
    nlinarith [mul_nonneg hr0 hc]
  · intro x hx
    have hc1 := Real.cos_le_one x
    have h := hN x
    have hpos : 0 < ‖Complex.exp ((s₀ + x : ℝ) * I) + z‖ ^ 2 := by
      have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc ⟨by linarith [neg_abs_le x],
        by linarith [le_abs_self x]⟩
      nlinarith [mul_nonneg hr0 hc]
    rw [hzn, div_le_div_iff₀ (by norm_num) hpos]
    nlinarith [mul_le_mul_of_nonneg_left hc1 hr0]
  · intro x hx
    have hcx : -(1 / 2) ≤ Real.cos x := by
      rw [← Real.cos_abs]
      have h1 : Real.cos (2 * π / 3) = -(1 / 2) := by
        rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
      rw [← h1]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) (by linarith [Real.pi_pos]) hx
    have h := hN x
    have hpos : 3 / 4 ≤ ‖Complex.exp ((s₀ + x : ℝ) * I) + z‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hcx hr0, sq_nonneg (r - 1 / 2)]
    rw [hzn, div_le_iff₀ (lt_of_lt_of_le (by norm_num) hpos)]
    nlinarith

/-- C1.5 (conjugated lifts): if `F ∘ φ_z = φ_{F z} ∘ G` on `𝔻̄` and `H`, `T` are continuous lifts of `F`, `G`, then
`H ∘ Φ_z = Φ_{F z} ∘ T + 2πk` for one `k ∈ ℤ`. -/
theorem s07c_fkps_m6_conj_lift {F G : ℂ → ℂ} {z : ℂ} {H T : ℝ → ℝ} (hz : ‖z‖ < 1) (hw : ‖F z‖ < 1)
    (hFG : ∀ y ∈ closedBall (0 : ℂ) 1,
      F ((y + z) / (1 + conj z * y)) = (G y + F z) / (1 + conj (F z) * G y))
    (hHc : Continuous H) (hHF : ∀ θ : ℝ, F (Complex.exp (θ * Complex.I)) = Complex.exp (H θ * Complex.I))
    (hTc : Continuous T) (hTG : ∀ θ : ℝ, G (Complex.exp (θ * Complex.I)) = Complex.exp (T θ * Complex.I)) :
    ∃ k : ℤ, ∀ t : ℝ, H (t + 2 * arg (1 + z * Complex.exp (-(t * I)))) =
      (T t + 2 * arg (1 + F z * Complex.exp (-(T t * I)))) + 2 * π * k := by
  obtain ⟨hz1, hzd, -, -, -⟩ := s07c_fkps_m6_mob hz
  obtain ⟨hw1, hwd, -, -, -⟩ := s07c_fkps_m6_mob hw
  have hzc : Continuous (fun t : ℝ => t + 2 * arg (1 + z * Complex.exp (-(t * I)))) :=
    continuous_iff_continuousAt.mpr fun t => (hzd t).continuousAt
  have hwc : Continuous (fun t : ℝ => t + 2 * arg (1 + F z * Complex.exp (-(t * I)))) :=
    continuous_iff_continuousAt.mpr fun t => (hwd t).continuousAt
  have hpt : ∀ t : ℝ, ∃ n : ℤ, H (t + 2 * arg (1 + z * Complex.exp (-(t * I)))) =
      (T t + 2 * arg (1 + F z * Complex.exp (-(T t * I)))) + 2 * π * n := by
    intro t
    have hy : Complex.exp (t * I) ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall_zero_iff, Complex.norm_exp_ofReal_mul_I]
    have he : Complex.exp ((H (t + 2 * arg (1 + z * Complex.exp (-(t * I)))) : ℂ) * I) =
        Complex.exp (((T t + 2 * arg (1 + F z * Complex.exp (-(T t * I))) : ℝ) : ℂ) * I) := by
      rw [← hHF, ← hz1 t, hFG _ hy, hTG t, hw1 (T t)]
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, add_zero, mul_one, Complex.add_im, Complex.intCast_re,
      Complex.intCast_im, Complex.mul_re, sub_zero, Complex.re_ofNat,
      Complex.im_ofNat] at this
    linarith
  choose n hn using hpt
  set f : ℝ → ℝ := fun t => (H (t + 2 * arg (1 + z * Complex.exp (-(t * I)))) -
      (T t + 2 * arg (1 + F z * Complex.exp (-(T t * I))))) / (2 * π) with hfdef
  have hfc : Continuous f := by
    have h1 : Continuous fun t : ℝ => H (t + 2 * arg (1 + z * Complex.exp (-(t * I)))) :=
      hHc.comp hzc
    have h2 : Continuous fun t : ℝ => T t + 2 * arg (1 + F z * Complex.exp (-(T t * I))) :=
      hwc.comp hTc
    exact (h1.sub h2).div_const _
  have hfn : ∀ t, f t = n t := by
    intro t
    rw [hfdef]
    simp only
    rw [hn t]
    field_simp
    ring
  have hconst : ∀ t, n t = n 0 := by
    intro t
    by_contra hne
    have hIVT := intermediate_value_uIcc (a := (0 : ℝ)) (b := t) hfc.continuousOn
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `n t < n 0`
      have hv : ((n 0 : ℝ) - 1 / 2) ∈ uIcc (f 0) (f t) := by
        rw [hfn, hfn]
        have : (n t : ℝ) ≤ (n 0 : ℝ) - 1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
        exact ⟨by rw [min_le_iff]; right; linarith, by rw [le_max_iff]; left; linarith⟩
      obtain ⟨s, -, hs⟩ := hIVT hv
      rw [hfn] at hs
      have h2 : (2 * n s : ℝ) = 2 * n 0 - 1 := by linarith
      have h3 : 2 * n s = 2 * n 0 - 1 := by exact_mod_cast h2
      omega
    · have hv : ((n 0 : ℝ) + 1 / 2) ∈ uIcc (f 0) (f t) := by
        rw [hfn, hfn]
        have : (n 0 : ℝ) + 1 ≤ (n t : ℝ) := by exact_mod_cast Int.add_one_le_of_lt hgt
        exact ⟨by rw [min_le_iff]; left; linarith, by rw [le_max_iff]; right; linarith⟩
      obtain ⟨s, -, hs⟩ := hIVT hv
      rw [hfn] at hs
      have h2 : (2 * n s : ℝ) = 2 * n 0 + 1 := by linarith
      have h3 : 2 * n s = 2 * n 0 + 1 := by exact_mod_cast h2
      omega
  exact ⟨n 0, fun t => by rw [hn t, hconst t]⟩

/-- C1.6 (densities are a.e. unique). -/
theorem s07c_fkps_m6_dens_ae {H u u' : ℝ → ℝ}
    (hu : ∀ a b : ℝ, IntegrableOn u (Icc a b)) (hu' : ∀ a b : ℝ, IntegrableOn u' (Icc a b))
    (h : ∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t)
    (h' : ∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u' t) :
    u =ᵐ[volume] u' := by
  have hl : LocallyIntegrable u volume := fun x =>
    ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), hu _ _⟩
  have hl' : LocallyIntegrable u' volume := fun x =>
    ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), hu' _ _⟩
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hl,
    _root_.LocallyIntegrable.ae_hasDerivAt_integral hl'] with t h1 h2
  have e1 : H = fun θ => H 0 + ∫ s in (0 : ℝ)..θ, u s := funext h
  have e2 : H = fun θ => H 0 + ∫ s in (0 : ℝ)..θ, u' s := funext h'
  have d1 : HasDerivAt H (u t) t := by rw [e1]; exact (h1 0).const_add _
  have d2 : HasDerivAt H (u' t) t := by rw [e2]; exact (h2 0).const_add _
  exact d1.unique d2

/-- C1.7 (a.e. chain rule): from `H ∘ Φ_z = Φ_w ∘ T + 2πk` with `H' = u`, `T' = v` (absolutely continuous),
`u(Φ_z t) P_z(t) = P_w(T t) v(t)` for a.e. `t` (Lebesgue differentiation; `Φ_z` pulls null sets back to null sets
since `Φ_z' > 0`). -/
theorem s07c_fkps_m6_ae_chain {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) {H T u v : ℝ → ℝ} {k : ℤ}
    (hu : ∀ a b : ℝ, IntegrableOn u (Icc a b)) (hH : ∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t)
    (hv : ∀ a b : ℝ, IntegrableOn v (Icc a b)) (hT : ∀ θ : ℝ, T θ = T 0 + ∫ t in (0 : ℝ)..θ, v t)
    (hHT : ∀ t : ℝ, H (t + 2 * arg (1 + z * Complex.exp (-(t * I)))) =
      (T t + 2 * arg (1 + w * Complex.exp (-(T t * I)))) + 2 * π * k) :
    ∀ᵐ t : ℝ, u (t + 2 * arg (1 + z * Complex.exp (-(t * I)))) *
        ((1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) + z‖ ^ 2) =
      (1 - ‖w‖ ^ 2) / ‖Complex.exp (T t * I) + w‖ ^ 2 * v t := by
  obtain ⟨-, hzd, hzP, hzm, -⟩ := s07c_fkps_m6_mob hz
  obtain ⟨-, hwd, -, -, -⟩ := s07c_fkps_m6_mob hw
  have hl : LocallyIntegrable u volume := fun x =>
    ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), hu _ _⟩
  have hlv : LocallyIntegrable v volume := fun x =>
    ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), hv _ _⟩
  have eH : H = fun θ => H 0 + ∫ s in (0 : ℝ)..θ, u s := funext hH
  have eT : T = fun θ => T 0 + ∫ s in (0 : ℝ)..θ, v s := funext hT
  have dH : ∀ᵐ s, HasDerivAt H (u s) s := by
    filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hl] with s hs
    rw [eH]
    exact (hs 0).const_add _
  have dT : ∀ᵐ t, HasDerivAt T (v t) t := by
    filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hlv] with s hs
    rw [eT]
    exact (hs 0).const_add _
  set Φ : ℝ → ℝ := fun t => t + 2 * arg (1 + z * Complex.exp (-(t * I))) with hΦ
  have hΦc : Continuous Φ := continuous_iff_continuousAt.mpr fun t => (hzd t).continuousAt
  -- pull back the null set where `H` fails to have derivative `u`
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (measure_eq_zero_iff_ae_notMem.mpr
    (dH.mono fun s hs hs' => hs' hs) : volume {s | ¬ HasDerivAt H (u s) s} = 0)
  have hS : MeasurableSet (Φ ⁻¹' N) := hNm.preimage hΦc.measurable
  have hpre : volume (Φ ⁻¹' N) = 0 := by
    have himg := s07_volume_image_deriv hzd hzm.injective _ hS
    have hsub : Φ '' (Φ ⁻¹' N) ⊆ N := image_preimage_subset _ _
    have h0 : ∫⁻ x in Φ ⁻¹' N, ENNReal.ofReal |(1 - ‖z‖ ^ 2) / ‖Complex.exp (x * I) + z‖ ^ 2| = 0 := by
      rw [← himg]
      exact measure_mono_null hsub hN0
    have hmeas : Measurable fun x : ℝ =>
        ENNReal.ofReal |(1 - ‖z‖ ^ 2) / ‖Complex.exp (x * I) + z‖ ^ 2| := by
      apply ENNReal.measurable_ofReal.comp
      fun_prop
    have hae := (lintegral_eq_zero_iff hmeas).mp h0
    rw [Filter.EventuallyEq, ae_restrict_iff' hS] at hae
    refine measure_eq_zero_iff_ae_notMem.mpr ?_
    filter_upwards [hae] with x hx hxS
    have := hx hxS
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at this
    have := hzP x
    rw [abs_of_pos this] at *
    linarith
  have dHΦ : ∀ᵐ t, HasDerivAt H (u (Φ t)) (Φ t) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hpre] with t ht
    by_contra hne
    exact ht (hNsub hne)
  filter_upwards [dT, dHΦ] with t hTd hHd
  have d1 : HasDerivAt (fun t => H (Φ t)) (u (Φ t) * ((1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) + z‖ ^ 2)) t :=
    hHd.comp t (hzd t)
  have d2 : HasDerivAt (fun t => (T t + 2 * arg (1 + w * Complex.exp (-(T t * I)))) + 2 * π * k)
      ((1 - ‖w‖ ^ 2) / ‖Complex.exp (T t * I) + w‖ ^ 2 * v t) t :=
    ((hwd (T t)).comp t hTd).add_const _
  have heq : (fun t => H (Φ t)) =
      fun t => (T t + 2 * arg (1 + w * Complex.exp (-(T t * I)))) + 2 * π * k := funext hHT
  rw [heq] at d1
  exact d1.unique d2

/-- C1.8 (deviation from the global step): with the block A data on one period,
`∫_x^y |u - 1| ≤ 2C√ε√(y - x) + 2δ(y - x)` (`|u - 1| ≤ |2πρ(T)u - 1| + δ u`, `u ≤ 2(|2πρ(T)u - 1| + 1)`). -/
theorem s07c_fkps_m6_dev {T u ρ : ℝ → ℝ} {C ε δ x y : ℝ} (hxy : x ≤ y) (hy : y ≤ x + 2 * π)
    (hu : IntegrableOn u (Icc x y)) (hu0 : ∀ t, 0 ≤ u t) (hTc : Continuous T)
    (hρ0 : ∀ τ, 0 < ρ τ) (hρL : ∀ τ τ' : ℝ, ρ τ' ≤ Real.exp (4 * |τ - τ'|) * ρ τ)
    (hρ : ∀ τ, |2 * π * ρ τ - 1| ≤ δ) (hδ : δ ≤ 1 / 2)
    (hA : ∀ (s : ℝ) (A : Set ℝ), MeasurableSet A → A ⊆ Icc s (s + 2 * π) →
      ∫ t in A, |2 * π * ρ (T t) * u t - 1| ≤ C * Real.sqrt ε * Real.sqrt (volume A).toReal) :
    ∫ t in x..y, |u t - 1| ≤ 2 * (C * Real.sqrt ε * Real.sqrt (y - x)) + 2 * δ * (y - x) := by
  have hρc : Continuous ρ := by
    rw [continuous_iff_continuousAt]
    intro τ
    have hup : ∀ τ', ρ τ' ≤ Real.exp (4 * |τ - τ'|) * ρ τ := fun τ' => hρL τ τ'
    have hlo : ∀ τ', Real.exp (-(4 * |τ - τ'|)) * ρ τ ≤ ρ τ' := fun τ' => by
      have := hρL τ' τ
      rw [abs_sub_comm] at this
      rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
      exact this
    have g1 : Continuous fun τ' => Real.exp (-(4 * |τ - τ'|)) * ρ τ := by fun_prop
    have g2 : Continuous fun τ' => Real.exp (4 * |τ - τ'|) * ρ τ := by fun_prop
    have t1 := g1.tendsto τ
    have t2 := g2.tendsto τ
    simp only [sub_self, abs_zero, mul_zero, neg_zero, Real.exp_zero, one_mul] at t1 t2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le t1 t2 hlo hup
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hρ 0)
  have hpt : ∀ t, |u t - 1| ≤ 2 * |2 * π * ρ (T t) * u t - 1| + 2 * δ := by
    intro t
    have hp := hρ (T t)
    have hu' := hu0 t
    set p := 2 * π * ρ (T t) with hpdef
    set k := |p * u t - 1| with hk
    have hk1 := le_abs_self (p * u t - 1)
    have hk2 := neg_abs_le (p * u t - 1)
    rw [abs_le] at hp
    have e1 : (1 - p) * u t ≤ δ * u t := mul_le_mul_of_nonneg_right (by linarith) hu'
    have e2 : (p - 1) * u t ≤ δ * u t := mul_le_mul_of_nonneg_right (by linarith) hu'
    have e0 : (1 / 2) * u t ≤ p * u t := mul_le_mul_of_nonneg_right (by linarith) hu'
    have e3 : u t ≤ 2 * (k + 1) := by linarith
    have e4 : δ * u t ≤ δ * (2 * (k + 1)) := mul_le_mul_of_nonneg_left e3 hδ0
    have e5 : δ * k ≤ (1 / 2) * k := mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
    rw [abs_le]
    constructor <;> nlinarith
  have hII : IntervalIntegrable u volume x y :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mpr hu
  have hkI : IntegrableOn (fun t => |2 * π * ρ (T t) * u t - 1|) (Icc x y) := by
    have h1 : IntegrableOn (fun t => 2 * π * ρ (T t) * u t) (Icc x y) :=
      IntegrableOn.continuousOn_mul (by fun_prop) hu isCompact_Icc
    exact (h1.sub (continuous_const.integrableOn_Icc)).abs
  have hkII : IntervalIntegrable (fun t => |2 * π * ρ (T t) * u t - 1|) volume x y :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mpr hkI
  have hmono : ∫ t in x..y, |u t - 1| ≤ ∫ t in x..y, (2 * |2 * π * ρ (T t) * u t - 1| + 2 * δ) :=
    intervalIntegral.integral_mono_on hxy (hII.sub intervalIntegrable_const).abs
      ((hkII.const_mul 2).add intervalIntegrable_const) (fun t _ => hpt t)
  have hAk := hA x (Icc x y) measurableSet_Icc (Icc_subset_Icc le_rfl hy)
  rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)] at hAk
  rw [intervalIntegral.integral_add (hkII.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hk' : ∫ t in x..y, |2 * π * ρ (T t) * u t - 1| = ∫ t in Icc x y, |2 * π * ρ (T t) * u t - 1| := by
    rw [intervalIntegral.integral_of_le hxy, integral_Icc_eq_integral_Ioc]
  rw [hk'] at hmono
  nlinarith

/-- C1.9 (positional lemma): if `T` is `1/16`-close to a translation on `[t₀ - 2π/3, t₀ + 2π/3]` and
`Φ_w ∘ T` grows by at most `π` there, then `T([t₀ - 1/16, t₀ + 1/16])` stays `1/16`-away from the expanding point
`-w/‖w‖` of `φ_w`: otherwise `Φ_w ∘ T` would cover `Φ_w([τ_w - π/2, τ_w + π/2])`, of length
`≥ 2π - π(1 - ‖w‖²) > π`. -/
theorem s07c_fkps_m6_position {w : ℂ} (hw : ‖w‖ < 1) {T : ℝ → ℝ} (hTm : Monotone T) {t₀ : ℝ}
    (hrot : ∀ x y : ℝ, t₀ - 2 * π / 3 ≤ x → x ≤ y → y ≤ t₀ + 2 * π / 3 → y - x - 1 / 16 ≤ T y - T x)
    (hH : (T (t₀ + 2 * π / 3) + 2 * arg (1 + w * Complex.exp (-(T (t₀ + 2 * π / 3) * I)))) -
        (T (t₀ - 2 * π / 3) + 2 * arg (1 + w * Complex.exp (-(T (t₀ - 2 * π / 3) * I)))) ≤ π) :
    ∀ τ ∈ Icc (T (t₀ - 1 / 16)) (T (t₀ + 1 / 16)), 1 / 16 ≤ ‖Complex.exp (τ * I) + w‖ := by
  intro τ hτ
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨-, hwd, -, hwm, hwp⟩ := s07c_fkps_m6_mob hw
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ → ℝ, Φ = fun σ : ℝ => σ + 2 * arg (1 + w * Complex.exp (-(σ * I))) := ⟨_, rfl⟩
  have hwd' : ∀ σ : ℝ, HasDerivAt Φ ((1 - ‖w‖ ^ 2) / ‖Complex.exp (σ * I) + w‖ ^ 2) σ := by
    rw [hΦ]; exact hwd
  have hwm' : StrictMono Φ := by rw [hΦ]; exact hwm
  have hwp' : ∀ σ : ℝ, Φ (σ + 2 * π) = Φ σ + 2 * π := by rw [hΦ]; exact hwp
  have hH' : Φ (T (t₀ + 2 * π / 3)) - Φ (T (t₀ - 2 * π / 3)) ≤ π := by rw [hΦ]; exact hH
  clear hwd hwm hwp hH hΦ
  have hτn : ‖Complex.exp (τ * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I τ
  have hr15 : 15 / 16 < ‖w‖ := by
    have := norm_sub_norm_le (Complex.exp (τ * I)) (-w)
    rw [sub_neg_eq_add, norm_neg, hτn] at this
    linarith
  have hcw : -w = ((‖w‖ : ℝ) : ℂ) * Complex.exp (arg (-w) * I) := by
    rw [← norm_neg w]
    exact (Complex.norm_mul_exp_arg_mul_I (-w)).symm
  have hcos : ∀ σ : ℝ, ‖Complex.exp (σ * I) + w‖ ^ 2 = 1 + ‖w‖ ^ 2 - 2 * ‖w‖ * Real.cos (σ - arg (-w)) :=
    fun σ => s07c_fkps_m6_mob_cos w _ σ hcw
  -- reduce `τ - arg(-w)` into `(-π, π]`
  have hmem := toIocMod_mem_Ioc Real.two_pi_pos (-π) (τ - arg (-w))
  have hdec := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (-π) (τ - arg (-w))
  generalize toIocMod Real.two_pi_pos (-π) (τ - arg (-w)) = y at hmem hdec
  generalize toIocDiv Real.two_pi_pos (-π) (τ - arg (-w)) = j at hdec
  rw [zsmul_eq_mul] at hdec
  obtain ⟨τw, hτw⟩ : ∃ τw : ℝ, τw = arg (-w) + (j : ℝ) * (2 * π) := ⟨_, rfl⟩
  have hcosσ : ∀ σ : ℝ, Real.cos (σ - arg (-w)) = Real.cos (σ - τw) := by
    intro σ
    rw [show σ - arg (-w) = (σ - τw) + (j : ℝ) * (2 * π) by rw [hτw]; ring,
      Real.cos_add_int_mul_two_pi]
  have hyτ : y = τ - τw := by rw [hτw]; linarith
  have hyπ : |y| ≤ π := abs_le.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  -- `|y| < 1/7`
  have hsq : ‖Complex.exp (τ * I) + w‖ ^ 2 < 1 / 256 := by
    have := norm_nonneg (Complex.exp (τ * I) + w)
    nlinarith
  rw [hcos τ, hcosσ τ, ← hyτ] at hsq
  have hcy := Real.cos_le_one_sub_mul_cos_sq hyπ
  have he0 : 0 ≤ 2 / π ^ 2 * y ^ 2 := by positivity
  have hr0 : 0 ≤ ‖w‖ := norm_nonneg w
  have h1 : 2 * ‖w‖ * (2 / π ^ 2 * y ^ 2) < 1 / 256 := by
    nlinarith [mul_le_mul_of_nonneg_left hcy (by linarith : (0 : ℝ) ≤ 2 * ‖w‖), sq_nonneg (1 - ‖w‖)]
  have h2 : 2 / π ^ 2 * y ^ 2 < 1 / 480 := by
    nlinarith [mul_le_mul_of_nonneg_right hr15.le he0]
  have hπ4 := Real.pi_le_four
  have hπ0 := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have h3 : y ^ 2 < 1 / 49 := by
    have e : y ^ 2 = (2 / π ^ 2 * y ^ 2) * (π ^ 2 / 2) := by field_simp
    rw [e]
    have : π ^ 2 / 2 ≤ 8 := by nlinarith
    nlinarith
  have hy7 : |y| < 1 / 7 := abs_lt.mpr ⟨by nlinarith, by nlinarith⟩
  -- positions of `T` at the ends
  have hb : τ + 2 * π / 3 - 1 / 8 ≤ T (t₀ + 2 * π / 3) := by
    have := hrot (t₀ + 1 / 16) (t₀ + 2 * π / 3) (by linarith) (by linarith) le_rfl
    linarith [hτ.2]
  have ha : T (t₀ - 2 * π / 3) ≤ τ - 2 * π / 3 + 1 / 8 := by
    have := hrot (t₀ - 2 * π / 3) (t₀ - 1 / 16) le_rfl (by linarith) (by linarith)
    linarith [hτ.1]
  have hb' : τw + π / 2 ≤ T (t₀ + 2 * π / 3) := by
    have := neg_abs_le y
    linarith
  have ha' : T (t₀ - 2 * π / 3) ≤ τw - π / 2 := by
    have := le_abs_self y
    linarith
  have m1 : Φ (τw + π / 2) ≤ Φ (T (t₀ + 2 * π / 3)) := hwm'.monotone hb'
  have m2 : Φ (T (t₀ - 2 * π / 3)) ≤ Φ (τw - π / 2) := hwm'.monotone ha'
  have hper : Φ (τw + 3 * π / 2) = Φ (τw - π / 2) + 2 * π := by
    have := hwp' (τw - π / 2)
    rw [show τw - π / 2 + 2 * π = τw + 3 * π / 2 by ring] at this
    exact this
  -- the far half-circle is short
  have hfar : Φ (τw + 3 * π / 2) - Φ (τw + π / 2) ≤ (1 - ‖w‖ ^ 2) * (τw + 3 * π / 2 - (τw + π / 2)) := by
    have hcont : Continuous Φ := continuous_iff_continuousAt.mpr fun σ => (hwd' σ).continuousAt
    refine Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc (τw + π / 2) (τw + 3 * π / 2))
      hcont.continuousOn (fun σ _ => (hwd' σ).differentiableAt.differentiableWithinAt) ?_ _
      ⟨le_rfl, by linarith⟩ _ ⟨by linarith, le_rfl⟩ (by linarith)
    intro σ hσ
    rw [interior_Icc] at hσ
    rw [(hwd' σ).deriv]
    have hc : Real.cos (σ - τw) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith [hσ.1]) (by linarith [hσ.2])
    have hN1 : 1 ≤ ‖Complex.exp (σ * I) + w‖ ^ 2 := by
      rw [hcos σ, hcosσ σ]
      nlinarith [mul_nonneg hr0 (neg_nonneg.mpr hc), sq_nonneg ‖w‖]
    have hnum : 0 ≤ 1 - ‖w‖ ^ 2 := by
      have := mul_le_mul hw.le hw.le hr0 zero_le_one
      rw [← sq, mul_one] at this
      linarith
    exact div_le_self hnum hN1
  have : π < Φ (T (t₀ + 2 * π / 3)) - Φ (T (t₀ - 2 * π / 3)) := by
    have hr2 : 0 < ‖w‖ ^ 2 := by positivity
    nlinarith
  linarith

/-! ### C2: per-arc small A∞ -/

/-- C2.1 (reduction): `∫_I |u - c| ≤ δ c |I|` with `δ ≤ 1/2` gives `∫_I |u - u_I| ≤ 4δ ∫_I u`. -/
theorem s07c_fkps_m6_reduce {u : ℝ → ℝ} {a b c δ : ℝ} (hab : a < b) (hu : IntegrableOn u (Icc a b))
    (hu0 : ∀ t, 0 ≤ u t) (hc : 0 < c) (hδ : δ ≤ 1 / 2)
    (h : ∫ t in a..b, |u t - c| ≤ δ * c * (b - a)) :
    ∫ t in a..b, |u t - (∫ s in a..b, u s) / (b - a)| ≤ 4 * δ * ∫ t in a..b, u t := by
  have hba : 0 < b - a := by linarith
  have hII : IntervalIntegrable u volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hu
  have h1 := s07_ssv_osc_const hab hII c
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hba] at h1
  have hac : IntervalIntegrable (fun t => |u t - c|) volume a b := (hII.sub intervalIntegrable_const).abs
  have h2 : c * (b - a) - ∫ t in a..b, u t ≤ ∫ t in a..b, |u t - c| := by
    have : ∫ t in a..b, (c - u t) ≤ ∫ t in a..b, |u t - c| :=
      intervalIntegral.integral_mono_on hab.le (intervalIntegrable_const.sub hII) hac
        (fun t _ => by rw [abs_sub_comm]; exact le_abs_self _)
    rwa [intervalIntegral.integral_sub intervalIntegrable_const hII, intervalIntegral.integral_const,
      smul_eq_mul, mul_comm] at this
  have h0 : 0 ≤ ∫ t in a..b, |u t - c| := intervalIntegral.integral_nonneg hab.le (fun t _ => abs_nonneg _)
  have hcb : 0 < c * (b - a) := mul_pos hc hba
  have hδ0 : 0 ≤ δ := by
    by_contra hn
    rw [not_le] at hn
    have : δ * c * (b - a) < 0 := by rw [mul_assoc]; exact mul_neg_of_neg_of_pos hn hcb
    linarith
  have h3 : c * (b - a) ≤ 2 * ∫ t in a..b, u t := by nlinarith
  have h4 : δ * (c * (b - a)) ≤ δ * (2 * ∫ t in a..b, u t) := mul_le_mul_of_nonneg_left h3 hδ0
  nlinarith

/-- C2.2 (change of variables along a `C¹` increasing map, integrable integrand; Mathlib
`integral_image_eq_integral_abs_deriv_smul`). -/
theorem s07c_fkps_m6_cov {Φ P f : ℝ → ℝ} {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) (hΦ : StrictMono Φ)
    (hd : ∀ t, HasDerivAt Φ (P t) t) (hP : ∀ t, 0 < P t)
    (hf : IntegrableOn f (Icc (Φ t₁) (Φ t₂))) :
    ∫ s in (Φ t₁)..(Φ t₂), f s = ∫ t in t₁..t₂, f (Φ t) * P t := by
  have hcont : Continuous Φ := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  have himg : Φ '' Icc t₁ t₂ = Icc (Φ t₁) (Φ t₂) := by
    apply Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨hΦ.monotone ht.1, hΦ.monotone ht.2⟩
    · exact intermediate_value_Icc ht hcont.continuousOn
  have h := integral_image_eq_integral_abs_deriv_smul (s := Icc t₁ t₂) measurableSet_Icc
    (fun t _ => (hd t).hasDerivWithinAt) hΦ.injective.injOn f
  rw [himg] at h
  rw [intervalIntegral.integral_of_le (hΦ.monotone ht), intervalIntegral.integral_of_le ht,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc, h]
  refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  simp only [smul_eq_mul, abs_of_pos (hP t)]
  ring

/-- C2.3 (core estimate on `B = [t₁, t₂]`): if `g = P(T) v` a.e. on `B`, `P` is `L`-log-Lipschitz on `T(B)`, `ρ` is
`4`-log-Lipschitz and `∫_B |2πρ(T)v - 1| ≤ E`, then with `c' = P(T t₁)/(2πρ(T t₁))` and `N = (L + 4)|T(B)|`,
`∫_B |g - c'| ≤ c'((e^N - 1)|B| + e^N E)`. -/
theorem s07c_fkps_m6_core {g T v ρ P : ℝ → ℝ} {t₁ t₂ L E : ℝ} (ht : t₁ ≤ t₂) (hL : 0 ≤ L)
    (hTm : Monotone T) (hTc : Continuous T)
    (hv : IntegrableOn v (Icc t₁ t₂)) (hv0 : ∀ t, 0 ≤ v t)
    (hρ0 : ∀ τ, 0 < ρ τ) (hρL : ∀ τ τ' : ℝ, ρ τ' ≤ Real.exp (4 * |τ - τ'|) * ρ τ)
    (hP0 : ∀ τ, 0 < P τ) (hPc : Continuous P)
    (hPL : ∀ τ ∈ Icc (T t₁) (T t₂), ∀ τ' ∈ Icc (T t₁) (T t₂), P τ' ≤ Real.exp (L * |τ - τ'|) * P τ)
    (hE : ∫ t in t₁..t₂, |2 * π * ρ (T t) * v t - 1| ≤ E)
    (hg : ∀ᵐ t, t ∈ Icc t₁ t₂ → g t = P (T t) * v t) :
    ∫ t in t₁..t₂, |g t - P (T t₁) / (2 * π * ρ (T t₁))| ≤
      P (T t₁) / (2 * π * ρ (T t₁)) *
        ((Real.exp ((L + 4) * (T t₂ - T t₁)) - 1) * (t₂ - t₁) +
          Real.exp ((L + 4) * (T t₂ - T t₁)) * E) := by
  have hD : 0 ≤ T t₂ - T t₁ := by linarith [hTm ht]
  have hρc : Continuous ρ := by
    rw [continuous_iff_continuousAt]
    intro τ
    have hup : ∀ τ', ρ τ' ≤ Real.exp (4 * |τ - τ'|) * ρ τ := fun τ' => hρL τ τ'
    have hlo : ∀ τ', Real.exp (-(4 * |τ - τ'|)) * ρ τ ≤ ρ τ' := fun τ' => by
      have := hρL τ' τ
      rw [abs_sub_comm] at this
      rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
      exact this
    have g1 : Continuous fun τ' => Real.exp (-(4 * |τ - τ'|)) * ρ τ := by fun_prop
    have g2 : Continuous fun τ' => Real.exp (4 * |τ - τ'|) * ρ τ := by fun_prop
    have t1 := g1.tendsto τ
    have t2 := g2.tendsto τ
    simp only [sub_self, abs_zero, mul_zero, neg_zero, Real.exp_zero, one_mul] at t1 t2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le t1 t2 hlo hup
  set N := (L + 4) * (T t₂ - T t₁) with hNdef
  have hN0 : 0 ≤ N := mul_nonneg (by linarith) hD
  have hρ1 := hρ0 (T t₁)
  have hP1 := hP0 (T t₁)
  set c' := P (T t₁) / (2 * π * ρ (T t₁)) with hc'
  have hc'0 : 0 < c' := div_pos hP1 (by positivity)
  have heN : 1 ≤ Real.exp N := Real.one_le_exp hN0
  have hpt : ∀ t ∈ Icc t₁ t₂, |P (T t) * v t - c'| ≤
      c' * ((Real.exp N - 1) + Real.exp N * |2 * π * ρ (T t) * v t - 1|) := by
    intro t ht'
    have hTt : T t ∈ Icc (T t₁) (T t₂) := ⟨hTm ht'.1, hTm ht'.2⟩
    have hT1 : T t₁ ∈ Icc (T t₁) (T t₂) := ⟨le_rfl, hTm ht⟩
    set d := |T t₁ - T t| with hd
    have hd' : |T t - T t₁| = d := abs_sub_comm _ _
    have hdD : d ≤ T t₂ - T t₁ := by
      rw [hd, abs_sub_comm, abs_of_nonneg (by linarith [hTt.1])]
      linarith [hTt.2]
    have hd0 : 0 ≤ d := abs_nonneg _
    have hPt := hP0 (T t)
    have hρt := hρ0 (T t)
    have hPa : P (T t) ≤ Real.exp (L * d) * P (T t₁) := hPL _ hT1 _ hTt
    have hPb : P (T t₁) ≤ Real.exp (L * d) * P (T t) := by rw [← hd']; exact hPL _ hTt _ hT1
    have hρa : ρ (T t₁) ≤ Real.exp (4 * d) * ρ (T t) := by rw [← hd']; exact hρL _ _
    have hρb : ρ (T t) ≤ Real.exp (4 * d) * ρ (T t₁) := hρL _ _
    set q := P (T t) / P (T t₁) * (ρ (T t₁) / ρ (T t)) with hq
    have hqpos : 0 < q := by positivity
    have hq1 : q ≤ Real.exp ((L + 4) * d) := by
      have e1 : P (T t) / P (T t₁) ≤ Real.exp (L * d) := (div_le_iff₀ hP1).mpr hPa
      have e2 : ρ (T t₁) / ρ (T t) ≤ Real.exp (4 * d) := (div_le_iff₀ hρt).mpr hρa
      calc q ≤ Real.exp (L * d) * Real.exp (4 * d) :=
            mul_le_mul e1 e2 (by positivity) (by positivity)
        _ = Real.exp ((L + 4) * d) := by rw [← Real.exp_add]; ring_nf
    have hq2 : Real.exp (-((L + 4) * d)) ≤ q := by
      have e1 : Real.exp (-(L * d)) ≤ P (T t) / P (T t₁) := by
        rw [le_div_iff₀ hP1, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
        exact hPb
      have e2 : Real.exp (-(4 * d)) ≤ ρ (T t₁) / ρ (T t) := by
        rw [le_div_iff₀ hρt, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
        exact hρb
      calc Real.exp (-((L + 4) * d)) = Real.exp (-(L * d)) * Real.exp (-(4 * d)) := by
            rw [← Real.exp_add]; ring_nf
        _ ≤ q := mul_le_mul e1 e2 (by positivity) (by positivity)
    have hqN : q ≤ Real.exp N := hq1.trans (Real.exp_le_exp.mpr (by nlinarith))
    have hqN' : Real.exp (-N) ≤ q := (Real.exp_le_exp.mpr (by nlinarith)).trans hq2
    have hsum : 2 ≤ Real.exp N + Real.exp (-N) := by
      linarith [Real.add_one_le_exp N, Real.add_one_le_exp (-N)]
    have hq_1 : |q - 1| ≤ Real.exp N - 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    set w := 2 * π * ρ (T t) * v t with hw
    have hid : P (T t) * v t - c' = c' * ((q - 1) + q * (w - 1)) := by
      rw [hc', hq, hw]
      field_simp
      ring
    rw [hid, abs_mul, abs_of_pos hc'0]
    refine mul_le_mul_of_nonneg_left ?_ hc'0.le
    calc |(q - 1) + q * (w - 1)| ≤ |q - 1| + |q * (w - 1)| := abs_add_le _ _
      _ = |q - 1| + q * |w - 1| := by rw [abs_mul, abs_of_pos hqpos]
      _ ≤ (Real.exp N - 1) + Real.exp N * |w - 1| := by
          gcongr
  have hII : IntervalIntegrable v volume t₁ t₂ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht).mpr hv
  have hPT : Continuous fun t => P (T t) := hPc.comp hTc
  have hgv : IntervalIntegrable (fun t => P (T t) * v t) volume t₁ t₂ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht).mpr
      (IntegrableOn.continuousOn_mul hPT.continuousOn hv isCompact_Icc)
  have hkI : IntervalIntegrable (fun t => |2 * π * ρ (T t) * v t - 1|) volume t₁ t₂ := by
    have h1 : IntegrableOn (fun t => 2 * π * ρ (T t) * v t) (Icc t₁ t₂) :=
      IntegrableOn.continuousOn_mul (by fun_prop) hv isCompact_Icc
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le ht).mpr
      ((h1.sub (continuous_const.integrableOn_Icc)).abs)
  have hcongr : ∫ t in t₁..t₂, |g t - c'| = ∫ t in t₁..t₂, |P (T t) * v t - c'| := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hg] with t hgt hmem
    rw [uIoc_of_le ht] at hmem
    rw [hgt (Ioc_subset_Icc_self hmem)]
  rw [hcongr]
  have hmono : ∫ t in t₁..t₂, |P (T t) * v t - c'| ≤
      ∫ t in t₁..t₂, c' * ((Real.exp N - 1) + Real.exp N * |2 * π * ρ (T t) * v t - 1|) :=
    intervalIntegral.integral_mono_on ht (hgv.sub intervalIntegrable_const).abs
      ((intervalIntegrable_const.add (hkI.const_mul _)).const_mul _) hpt
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add intervalIntegrable_const (hkI.const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul] at hmono
  refine hmono.trans (mul_le_mul_of_nonneg_left ?_ hc'0.le)
  have := mul_le_mul_of_nonneg_left hE (by linarith : (0 : ℝ) ≤ Real.exp N)
  nlinarith

/-- Helper for `_short`: block A gives `|(T y - T x) - (y - x)| ≤ 2C√ε√(y - x) + 2δ(y - x)` on one period. -/
theorem s07c_fkps_m6_sh_incr {T v ρ : ℝ → ℝ} {C ε δ x y : ℝ} (hxy : x ≤ y) (hy : y ≤ x + 2 * π)
    (hv : ∀ a b : ℝ, IntegrableOn v (Icc a b)) (hT : ∀ θ : ℝ, T θ = T 0 + ∫ t in (0 : ℝ)..θ, v t)
    (hv0 : ∀ t, 0 ≤ v t) (hTc : Continuous T)
    (hρ0 : ∀ τ, 0 < ρ τ) (hρL : ∀ τ τ' : ℝ, ρ τ' ≤ Real.exp (4 * |τ - τ'|) * ρ τ)
    (hρ : ∀ τ, |2 * π * ρ τ - 1| ≤ δ) (hδ : δ ≤ 1 / 2)
    (hA : ∀ (s : ℝ) (A : Set ℝ), MeasurableSet A → A ⊆ Icc s (s + 2 * π) →
      ∫ t in A, |2 * π * ρ (T t) * v t - 1| ≤ C * Real.sqrt ε * Real.sqrt (volume A).toReal) :
    |(T y - T x) - (y - x)| ≤ 2 * (C * Real.sqrt ε * Real.sqrt (y - x)) + 2 * δ * (y - x) := by
  have hd := s07c_fkps_m6_dev hxy hy (hv x y) hv0 hTc hρ0 hρL hρ hδ hA
  have hii : ∀ c d : ℝ, IntervalIntegrable v volume c d := fun c d =>
    IntegrableOn.intervalIntegrable (hv (min c d) (max c d))
  have hsub : T y - T x = ∫ t in x..y, v t := by
    rw [hT y, hT x, ← intervalIntegral.integral_interval_sub_left (hii 0 y) (hii 0 x)]
    ring
  have hlen : ∫ t in x..y, (v t - 1) = (T y - T x) - (y - x) := by
    rw [intervalIntegral.integral_sub (hii x y) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, mul_one, hsub]
  rw [← hlen]
  exact (intervalIntegral.abs_integral_le_integral_abs hxy).trans hd

/-- Helper for `_short`: two-sided mean value bounds. -/
theorem s07c_fkps_m6_sh_mvt {Φ P : ℝ → ℝ} {x y m M : ℝ} (hxy : x ≤ y)
    (hd : ∀ t, HasDerivAt Φ (P t) t)
    (hm : ∀ t ∈ Icc x y, m ≤ P t) (hM : ∀ t ∈ Icc x y, P t ≤ M) :
    m * (y - x) ≤ Φ y - Φ x ∧ Φ y - Φ x ≤ M * (y - x) := by
  have hc : Continuous Φ := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  have hdo : DifferentiableOn ℝ Φ (interior (Icc x y)) :=
    fun t _ => (hd t).differentiableAt.differentiableWithinAt
  constructor
  · exact Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc x y) hc.continuousOn hdo
      (fun t ht => by rw [(hd t).deriv]; exact hm t (interior_subset ht)) x ⟨le_rfl, hxy⟩ y
      ⟨hxy, le_rfl⟩ hxy
  · exact Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc x y) hc.continuousOn hdo
      (fun t ht => by rw [(hd t).deriv]; exact hM t (interior_subset ht)) x ⟨le_rfl, hxy⟩ y
      ⟨hxy, le_rfl⟩ hxy

/-- Helper for `_short`: transfer of the core estimate on `B = [t₁, t₂]` back to `Φ(B)`, when `P = Φ'`
oscillates by at most `e^β` on `B`. -/
theorem s07c_fkps_m6_sh_transfer {Φ P u : ℝ → ℝ} {t₁ t₂ β c' X : ℝ} (ht : t₁ < t₂) (hβ : 0 ≤ β)
    (hΦ : StrictMono Φ) (hd : ∀ t, HasDerivAt Φ (P t) t) (hP : ∀ t, 0 < P t)
    (hPβ : ∀ t ∈ Icc t₁ t₂, P t ≤ Real.exp β * P t₁ ∧ P t₁ ≤ Real.exp β * P t)
    (hu : IntegrableOn u (Icc (Φ t₁) (Φ t₂))) (hc' : 0 < c')
    (hX : ∫ t in t₁..t₂, |u (Φ t) * P t - c'| ≤ c' * X) :
    ∫ s in (Φ t₁)..(Φ t₂), |u s - c' / P t₁| ≤
      Real.exp β * (X / (t₂ - t₁) + (Real.exp β - 1)) * (c' / P t₁) * (Φ t₂ - Φ t₁) := by
  have hB : 0 < t₂ - t₁ := by linarith
  have hP1 := hP t₁
  have heβ : 1 ≤ Real.exp β := Real.one_le_exp hβ
  set c := c' / P t₁ with hc
  have hc0 : 0 < c := div_pos hc' hP1
  have hcont : Continuous Φ := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  have himg : Φ '' Icc t₁ t₂ = Icc (Φ t₁) (Φ t₂) := by
    apply Subset.antisymm
    · rintro _ ⟨t, ht', rfl⟩
      exact ⟨hΦ.monotone ht'.1, hΦ.monotone ht'.2⟩
    · exact intermediate_value_Icc ht.le hcont.continuousOn
  -- integrability of `u ∘ Φ · P` on `B`
  have hint : IntegrableOn (fun t => u (Φ t) * P t) (Icc t₁ t₂) := by
    have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Icc t₁ t₂) measurableSet_Icc
      (fun t _ => (hd t).hasDerivWithinAt) hΦ.injective.injOn u).mp (by rw [himg]; exact hu)
    refine h.congr_fun (fun t _ => ?_) measurableSet_Icc
    simp only [smul_eq_mul, abs_of_pos (hP t)]
    ring
  have hPint : IntegrableOn P (Icc t₁ t₂) := by
    have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Icc t₁ t₂) measurableSet_Icc
      (fun t _ => (hd t).hasDerivWithinAt) hΦ.injective.injOn (fun _ => (1 : ℝ))).mp
      (by rw [himg]; exact continuous_const.integrableOn_Icc)
    refine h.congr_fun (fun t _ => ?_) measurableSet_Icc
    simp only [smul_eq_mul, abs_of_pos (hP t), mul_one]
  have hcov := s07c_fkps_m6_cov (f := fun s => |u s - c|) ht.le hΦ hd hP
    ((hu.sub continuous_const.integrableOn_Icc).abs)
  rw [hcov]
  have hI1 : IntervalIntegrable (fun t => |u (Φ t) * P t - c'|) volume t₁ t₂ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.le).mpr
      ((hint.sub continuous_const.integrableOn_Icc).abs)
  have hI2 : IntervalIntegrable (fun t => |u (Φ t) - c| * P t) volume t₁ t₂ := by
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le ht.le).mpr ?_
    refine IntegrableOn.congr_fun (f := fun t => |u (Φ t) * P t - c * P t|)
      ((hint.sub (hPint.const_mul c)).abs) (fun t _ => ?_) measurableSet_Icc
    show |u (Φ t) * P t - c * P t| = |u (Φ t) - c| * P t
    rw [show u (Φ t) * P t - c * P t = (u (Φ t) - c) * P t by ring, abs_mul, abs_of_pos (hP t)]
  have hpt : ∀ t ∈ Icc t₁ t₂, |u (Φ t) - c| * P t ≤ |u (Φ t) * P t - c'| + c' * (Real.exp β - 1) := by
    intro t ht'
    obtain ⟨h1, h2⟩ := hPβ t ht'
    have hPt := hP t
    have hq1 : P t / P t₁ ≤ Real.exp β := (div_le_iff₀ hP1).mpr h1
    have hq2 : Real.exp (-β) ≤ P t / P t₁ := by
      rw [le_div_iff₀ hP1, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
      exact h2
    have hsum : 2 ≤ Real.exp β + Real.exp (-β) := by
      linarith [Real.add_one_le_exp β, Real.add_one_le_exp (-β)]
    have habs : |c' - c * P t| ≤ c' * (Real.exp β - 1) := by
      have e : c' - c * P t = c' * (1 - P t / P t₁) := by rw [hc]; field_simp
      rw [e, abs_mul, abs_of_pos hc']
      exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) hc'.le
    have e : |u (Φ t) - c| * P t = |(u (Φ t) * P t - c') + (c' - c * P t)| := by
      rw [show (u (Φ t) * P t - c') + (c' - c * P t) = (u (Φ t) - c) * P t by ring, abs_mul,
        abs_of_pos hPt]
    rw [e]
    exact (abs_add_le _ _).trans (by linarith)
  have hmono := intervalIntegral.integral_mono_on ht.le hI2 (hI1.add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_add hI1 intervalIntegrable_const, intervalIntegral.integral_const,
    smul_eq_mul] at hmono
  -- lower bound on `|Φ(B)|`
  have hlow : Real.exp (-β) * P t₁ * (t₂ - t₁) ≤ Φ t₂ - Φ t₁ := by
    refine (s07c_fkps_m6_sh_mvt ht.le hd (m := Real.exp (-β) * P t₁) (M := Real.exp β * P t₁)
      (fun t ht' => ?_) (fun t ht' => (hPβ t ht').1)).1
    rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
    exact (hPβ t ht').2
  have hX0 : 0 ≤ X := by
    have : 0 ≤ ∫ t in t₁..t₂, |u (Φ t) * P t - c'| :=
      intervalIntegral.integral_nonneg ht.le (fun t _ => abs_nonneg _)
    by_contra hn
    rw [not_le] at hn
    nlinarith
  have hcB : c' * (t₂ - t₁) ≤ Real.exp β * c * (Φ t₂ - Φ t₁) := by
    have h1 : c * (Real.exp (-β) * P t₁ * (t₂ - t₁)) ≤ c * (Φ t₂ - Φ t₁) :=
      mul_le_mul_of_nonneg_left hlow hc0.le
    have h2 : c * (Real.exp (-β) * P t₁ * (t₂ - t₁)) = Real.exp (-β) * (c' * (t₂ - t₁)) := by
      rw [hc]; field_simp
    rw [h2, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)] at h1
    linarith
  have hfin : Real.exp β * (X / (t₂ - t₁) + (Real.exp β - 1)) * c * (Φ t₂ - Φ t₁) =
      (X / (t₂ - t₁) + (Real.exp β - 1)) * (Real.exp β * c * (Φ t₂ - Φ t₁)) := by ring
  rw [hfin]
  have hk : 0 ≤ X / (t₂ - t₁) + (Real.exp β - 1) := by positivity
  have := mul_le_mul_of_nonneg_left hcB hk
  have e2 : (X / (t₂ - t₁) + (Real.exp β - 1)) * (c' * (t₂ - t₁)) =
      c' * X + c' * (Real.exp β - 1) * (t₂ - t₁) := by field_simp
  linarith

/-- Helper for `_short`: the powers of `ε` used in the short-arc estimate. -/
theorem s07c_fkps_m6_sh_eps {ε CB κ : ℝ} (hε : 0 < ε) (hCB : 1 ≤ CB) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (h : CB * ε ≤ κ ^ 6) :
    0 < ε ^ (1 / 3 : ℝ) ∧ ε ^ (1 / 3 : ℝ) ≤ κ ∧
    Real.sqrt ε = ε ^ (1 / 3 : ℝ) * Real.sqrt (ε ^ (1 / 3 : ℝ)) ∧
    Real.sqrt (CB * ε) ≤ κ ∧ Real.sqrt (CB * ε) ≤ CB * Real.sqrt ε ∧
    ε ^ (1 / 6 : ℝ) ≤ κ ∧ (CB * ε) ^ (1 / 6 : ℝ) ≤ κ := by
  have hCB0 : 0 < CB := by linarith
  have hεCB : ε ≤ CB * ε := le_mul_of_one_le_left hε.le hCB
  have hεκ : ε ≤ κ ^ 6 := hεCB.trans h
  have h3 : 0 < ε ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hε _
  obtain ⟨e3, he3⟩ : ∃ e3 : ℝ, e3 = ε ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  rw [← he3] at h3 ⊢
  have hε3 : ε = e3 ^ 3 := by
    rw [he3, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num
  have hroot : ∀ q : ℝ, 0 ≤ q → q ≤ κ ^ 6 → q ^ (1 / 6 : ℝ) ≤ κ := fun q hq hq' => by
    have h1 : q ^ (1 / 6 : ℝ) ≤ (κ ^ 6) ^ (1 / 6 : ℝ) := Real.rpow_le_rpow hq hq' (by norm_num)
    have h2 : (κ ^ 6) ^ (1 / 6 : ℝ) = κ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hκ.le]; norm_num
    linarith
  have he3κ : e3 ≤ κ := by
    have h1 : e3 ≤ (κ ^ 6) ^ (1 / 3 : ℝ) := by
      rw [he3]; exact Real.rpow_le_rpow hε.le hεκ (by norm_num)
    have h2 : (κ ^ 6) ^ (1 / 3 : ℝ) = κ ^ 2 := by
      rw [show κ ^ 6 = (κ ^ 2) ^ (3 : ℕ) by ring, ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity)]; norm_num
    have : κ ^ 2 ≤ κ := by rw [sq]; exact mul_le_of_le_one_left hκ.le hκ1
    linarith
  have hsε : Real.sqrt ε = e3 * Real.sqrt e3 := by
    rw [hε3, show e3 ^ 3 = e3 ^ 2 * e3 by ring, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h3.le]
  have hsCB : Real.sqrt (CB * ε) ≤ CB * Real.sqrt ε := by
    calc Real.sqrt (CB * ε) ≤ Real.sqrt (CB ^ 2 * ε) := Real.sqrt_le_sqrt (by nlinarith)
      _ = CB * Real.sqrt ε := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hCB0.le]
  have hsCBκ : Real.sqrt (CB * ε) ≤ κ := by
    have h1 := Real.sqrt_le_sqrt h
    rw [show κ ^ 6 = (κ ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)] at h1
    have h2 : κ ^ 3 ≤ κ := by
      rw [show κ ^ 3 = κ ^ 2 * κ by ring]
      exact mul_le_of_le_one_left hκ.le (by rw [sq]; nlinarith)
    linarith
  exact ⟨h3, he3κ, hsε, hsCBκ, hsCB, hroot ε hε.le hεκ, hroot _ (by positivity) h⟩

/-- Helper for `_short`: the bounds on `|T(B)|` and `E` on `B`. -/
theorem s07c_fkps_m6_sh_ME {A B D e3 β : ℝ} (he3 : 0 < e3) (hβlo : e3 ≤ 4 * β) (hβhi : β ≤ 4 * e3)
    (hA0 : 0 ≤ A) (hA : A ≤ D * (e3 * Real.sqrt e3)) (hD : 0 ≤ D) (hB : B ≤ 1) (he31 : e3 ≤ 1 / 4) :
    β + (2 * (A * Real.sqrt β) + 2 * B * β) ≤ (12 + 4 * D) * e3 ∧
      A * Real.sqrt β ≤ 2 * D * e3 * β := by
  have hβ0 : 0 < β := by linarith
  have hs : Real.sqrt e3 * Real.sqrt β ≤ 2 * β := by
    have h1 : Real.sqrt e3 ≤ Real.sqrt (4 * β) := Real.sqrt_le_sqrt hβlo
    have h2 : Real.sqrt (4 * β) = 2 * Real.sqrt β := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have h3 : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ0.le
    have h4 := mul_le_mul_of_nonneg_right (h1.trans h2.le) (Real.sqrt_nonneg β)
    linarith
  have hE : A * Real.sqrt β ≤ 2 * D * e3 * β := by
    calc A * Real.sqrt β ≤ D * (e3 * Real.sqrt e3) * Real.sqrt β :=
          mul_le_mul_of_nonneg_right hA (Real.sqrt_nonneg _)
      _ = D * e3 * (Real.sqrt e3 * Real.sqrt β) := by ring
      _ ≤ D * e3 * (2 * β) := mul_le_mul_of_nonneg_left hs (mul_nonneg hD he3.le)
      _ = 2 * D * e3 * β := by ring
  refine ⟨?_, hE⟩
  have h1 : D * e3 * β ≤ D * e3 := by
    have := mul_le_mul_of_nonneg_left (show β ≤ 1 by linarith) (mul_nonneg hD he3.le)
    linarith
  have h2 : B * β ≤ β := by
    have := mul_le_mul_of_nonneg_right hB hβ0.le
    linarith
  linarith

/-- Helper for `_short`: the arc `B = [t₁, t₂] = Φ⁻¹([x, y])` around the fixed point `s₀ = Φ s₀`. -/
theorem s07c_fkps_m6_sh_arc {Φ P : ℝ → ℝ} {s₀ ρ' e3 x y : ℝ} (he3 : 0 < e3) (hρ' : 0 < ρ')
    (hd : ∀ t, HasDerivAt Φ (P t) t) (hP : ∀ t, 0 < P t) (hΦm : StrictMono Φ) (hΦs₀ : Φ s₀ = s₀)
    (hB : ∀ t, |t - s₀| ≤ 2 * e3 → ρ' / 4 ≤ P t ∧ P t ≤ 4 * ρ')
    (hs₀ : s₀ = (x + y) / 2) (hℓ : y - x = ρ' * e3) :
    ∃ t₁ t₂ : ℝ, t₁ < t₂ ∧ Φ t₁ = x ∧ Φ t₂ = y ∧ e3 ≤ 4 * (t₂ - t₁) ∧ t₂ - t₁ ≤ 4 * e3 ∧
      ∀ t ∈ Icc t₁ t₂, |t - s₀| ≤ 2 * e3 := by
  have hΦc : Continuous Φ := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  have hℓp : 0 < y - x := by rw [hℓ]; positivity
  have hup := (s07c_fkps_m6_sh_mvt (by linarith : s₀ ≤ s₀ + 2 * e3) hd
    (fun t ht => (hB t (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).1)
    (fun t ht => (hB t (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).2)).1
  have hdn := (s07c_fkps_m6_sh_mvt (by linarith : s₀ - 2 * e3 ≤ s₀) hd
    (fun t ht => (hB t (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).1)
    (fun t ht => (hB t (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).2)).1
  have hhalf : ρ' / 4 * (s₀ + 2 * e3 - s₀) = (y - x) / 2 := by rw [hℓ]; ring
  have hhalf' : ρ' / 4 * (s₀ - (s₀ - 2 * e3)) = (y - x) / 2 := by rw [hℓ]; ring
  rw [hhalf, hΦs₀] at hup
  rw [hhalf', hΦs₀] at hdn
  obtain ⟨t₂, ht₂, hΦt₂⟩ := intermediate_value_Icc (by linarith : s₀ ≤ s₀ + 2 * e3) hΦc.continuousOn
    (show y ∈ Icc (Φ s₀) (Φ (s₀ + 2 * e3)) from ⟨by rw [hΦs₀]; linarith, by linarith⟩)
  obtain ⟨t₁, ht₁, hΦt₁⟩ := intermediate_value_Icc (by linarith : s₀ - 2 * e3 ≤ s₀) hΦc.continuousOn
    (show x ∈ Icc (Φ (s₀ - 2 * e3)) (Φ s₀) from ⟨by linarith, by rw [hΦs₀]; linarith⟩)
  have ht12 : t₁ < t₂ := by
    by_contra hn
    rw [not_lt] at hn
    have := hΦm.monotone hn
    rw [hΦt₁, hΦt₂] at this
    linarith
  have hBin : ∀ t ∈ Icc t₁ t₂, |t - s₀| ≤ 2 * e3 := fun t ht =>
    abs_le.mpr ⟨by linarith [ht.1, ht₁.1], by linarith [ht.2, ht₂.2]⟩
  refine ⟨t₁, t₂, ht12, hΦt₁, hΦt₂, ?_, by linarith [ht₁.1, ht₂.2], hBin⟩
  have h := (s07c_fkps_m6_sh_mvt ht12.le hd (m := 0) (M := 4 * ρ')
    (fun t _ => (hP t).le) (fun t ht => (hB t (hBin t ht)).2)).2
  rw [hΦt₁, hΦt₂, hℓ] at h
  by_contra hn
  rw [not_le] at hn
  have := mul_lt_mul_of_pos_left hn hρ'
  linarith

/-- Helper for `_short`: `P_z` oscillates by at most `e^{2|B|}` on `B` when `‖e^{it} + z‖ ≥ 1` there. -/
theorem s07c_fkps_m6_sh_pbeta {z : ℂ} (hz : ‖z‖ < 1) {t₁ t₂ : ℝ} (ht12 : t₁ ≤ t₂)
    (h1 : ∀ t ∈ Icc t₁ t₂, 1 ≤ ‖Complex.exp (t * I) + z‖) :
    ∀ t ∈ Icc t₁ t₂,
      (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) + z‖ ^ 2 ≤
        Real.exp (2 * (t₂ - t₁)) * ((1 - ‖z‖ ^ 2) / ‖Complex.exp (t₁ * I) + z‖ ^ 2) ∧
      (1 - ‖z‖ ^ 2) / ‖Complex.exp (t₁ * I) + z‖ ^ 2 ≤
        Real.exp (2 * (t₂ - t₁)) * ((1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) + z‖ ^ 2) := by
  obtain ⟨-, -, hzP, -, -⟩ := s07c_fkps_m6_mob hz
  intro t ht
  have hsub : uIcc t₁ t ⊆ Icc t₁ t₂ := uIcc_subset_Icc ⟨le_rfl, ht12⟩ ht
  have hsub' : uIcc t t₁ ⊆ Icc t₁ t₂ := by rw [uIcc_comm]; exact hsub
  have l1 := s07c_fkps_m6_mob_loglip hz (m := 1) (t := t₁) (t' := t) one_pos
    fun q hq => h1 q (hsub hq)
  have l2 := s07c_fkps_m6_mob_loglip hz (m := 1) (t := t) (t' := t₁) one_pos
    fun q hq => h1 q (hsub' hq)
  have hd : 2 * |t - t₁| / 1 ≤ 2 * (t₂ - t₁) := by
    rw [div_one, abs_of_nonneg (by linarith [ht.1])]; linarith [ht.2]
  have hd' : 2 * |t₁ - t| / 1 ≤ 2 * (t₂ - t₁) := by rwa [abs_sub_comm]
  exact ⟨l1.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hd) (hzP t₁).le),
    l2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hd') (hzP t).le)⟩

/-- Helper for `_short`: the hypotheses of C1.9 from block A for `G` and `F`. -/
theorem s07c_fkps_m6_sh_pos {w : ℂ} (hw : ‖w‖ < 1) {T H Φ P : ℝ → ℝ} {k : ℤ}
    {s₀ ρ' AT BT AH BH : ℝ} (hρ' : 0 < ρ') (hρ'18 : ρ' ≤ 1 / 18) (hTm : Monotone T)
    (hT : ∀ x y : ℝ, x ≤ y → y ≤ x + 2 * π →
      |(T y - T x) - (y - x)| ≤ 2 * (AT * Real.sqrt (y - x)) + 2 * BT * (y - x))
    (hH : ∀ x y : ℝ, x ≤ y → y ≤ x + 2 * π →
      |(H y - H x) - (y - x)| ≤ 2 * (AH * Real.sqrt (y - x)) + 2 * BH * (y - x))
    (hAT : AT ≤ 1 / 320) (hBT : BT ≤ 1 / 320) (hAH : AH ≤ 1 / 320) (hBH : BH ≤ 1 / 320)
    (hd : ∀ t, HasDerivAt Φ (P t) t) (hP : ∀ t, 0 < P t) (hΦm : StrictMono Φ)
    (hhi : ∀ t, |t - s₀| ≤ 2 * π / 3 → P t ≤ 4 * ρ')
    (hk : ∀ t, H (Φ t) = (T t + 2 * arg (1 + w * Complex.exp (-(T t * I)))) + 2 * π * k) :
    ∀ τ ∈ Icc (T (s₀ - 1 / 16)) (T (s₀ + 1 / 16)), 1 / 16 ≤ ‖Complex.exp (τ * I) + w‖ := by
  have hπ3 := Real.pi_gt_three
  have hπ4 := Real.pi_le_four
  have hrot : ∀ x' y' : ℝ, s₀ - 2 * π / 3 ≤ x' → x' ≤ y' → y' ≤ s₀ + 2 * π / 3 →
      y' - x' - 1 / 16 ≤ T y' - T x' := by
    intro x' y' h1 h2 h3
    have hinc := (abs_le.mp (hT x' y' h2 (by linarith))).1
    have hs : Real.sqrt (y' - x') ≤ 3 := by
      have := Real.sqrt_le_sqrt (show y' - x' ≤ 3 ^ 2 by linarith)
      rwa [Real.sqrt_sq (by norm_num)] at this
    have ea : AT * Real.sqrt (y' - x') ≤ 1 / 320 * 3 := by
      have := mul_le_mul_of_nonneg_right hAT (Real.sqrt_nonneg (y' - x'))
      have := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 1 / 320)
      linarith
    have eb : BT * (y' - x') ≤ 1 / 320 * 6 := by
      have := mul_le_mul_of_nonneg_right hBT (sub_nonneg.mpr h2)
      linarith
    linarith
  have hp := (s07c_fkps_m6_sh_mvt (by linarith : s₀ - 2 * π / 3 ≤ s₀ + 2 * π / 3) hd (m := 0)
    (M := 4 * ρ') (fun t _ => (hP t).le)
    (fun t ht => hhi t (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩))).2
  have hp0 : Φ (s₀ - 2 * π / 3) ≤ Φ (s₀ + 2 * π / 3) := hΦm.monotone (by linarith)
  have hp2 : Φ (s₀ + 2 * π / 3) - Φ (s₀ - 2 * π / 3) ≤ 2 := by
    have := mul_le_mul hρ'18 hπ4 Real.pi_pos.le (by norm_num : (0 : ℝ) ≤ 1 / 18)
    linarith
  have hinc := (abs_le.mp (hH _ _ hp0 (by linarith))).2
  have hs : Real.sqrt (Φ (s₀ + 2 * π / 3) - Φ (s₀ - 2 * π / 3)) ≤ 2 := by
    have := Real.sqrt_le_sqrt (show Φ (s₀ + 2 * π / 3) - Φ (s₀ - 2 * π / 3) ≤ 2 ^ 2 by linarith)
    rwa [Real.sqrt_sq (by norm_num)] at this
  have ea : AH * Real.sqrt (Φ (s₀ + 2 * π / 3) - Φ (s₀ - 2 * π / 3)) ≤ 1 / 320 * 2 := by
    have := mul_le_mul_of_nonneg_right hAH (Real.sqrt_nonneg (Φ (s₀ + 2 * π / 3) - Φ (s₀ - 2 * π / 3)))
    have := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 1 / 320)
    linarith
  have eb : BH * (Φ (s₀ + 2 * π / 3) - Φ (s₀ - 2 * π / 3)) ≤ 1 / 320 * 2 := by
    have := mul_le_mul_of_nonneg_right hBH (sub_nonneg.mpr hp0)
    linarith
  have h2 := hk (s₀ + 2 * π / 3)
  have h3 := hk (s₀ - 2 * π / 3)
  refine s07c_fkps_m6_position hw hTm hrot ?_
  linarith

/-- Helper for `_short`: from the core estimate on `B` to the per-arc estimate on `Φ(B)`. -/
theorem s07c_fkps_m6_sh_fin {Φ P u : ℝ → ℝ} {t₁ t₂ e3 M E c' CM CE Cδ : ℝ}
    (ht : t₁ < t₂) (he3 : 0 < e3) (hβhi : t₂ - t₁ ≤ 4 * e3)
    (hΦ : StrictMono Φ) (hd : ∀ t, HasDerivAt Φ (P t) t) (hP : ∀ t, 0 < P t)
    (hPβ : ∀ t ∈ Icc t₁ t₂,
      P t ≤ Real.exp (2 * (t₂ - t₁)) * P t₁ ∧ P t₁ ≤ Real.exp (2 * (t₂ - t₁)) * P t)
    (hu : IntegrableOn u (Icc (Φ t₁) (Φ t₂))) (hu0 : ∀ t, 0 ≤ u t) (hc' : 0 < c')
    (hCM : 0 ≤ CM) (hCE : 0 ≤ CE)
    (hM0 : 0 ≤ M) (hM : M ≤ CM * e3) (hE0 : 0 ≤ E) (hE : E ≤ CE * e3 * (t₂ - t₁))
    (hCδ : 3 * (72 * CM + 3 * CE + 16) ≤ Cδ) (hsmall : Cδ * e3 ≤ 1 / 2)
    (hX : ∫ t in t₁..t₂, |u (Φ t) * P t - c'| ≤
      c' * ((Real.exp ((32 + 4) * M) - 1) * (t₂ - t₁) + Real.exp ((32 + 4) * M) * E)) :
    ∫ t in (Φ t₁)..(Φ t₂), |u t - (∫ s in (Φ t₁)..(Φ t₂), u s) / (Φ t₂ - Φ t₁)| ≤
      4 * Cδ * e3 * ∫ t in (Φ t₁)..(Φ t₂), u t := by
  have hβ0 : 0 < t₂ - t₁ := by linarith
  have hCδ48 : 48 ≤ Cδ := by linarith
  have he3s : e3 ≤ 1 / 96 := by
    have := mul_le_mul_of_nonneg_right hCδ48 he3.le
    linarith
  have h36 : 36 * M ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_right (show 36 * CM ≤ Cδ by linarith) he3.le
    linarith
  have hexpM : Real.exp ((32 + 4) * M) - 1 ≤ 72 * M := by
    have h := Real.abs_exp_sub_one_le (x := (32 + 4) * M) (abs_le.mpr ⟨by linarith, by linarith⟩)
    rw [abs_of_nonneg (show 0 ≤ (32 + 4) * M by linarith)] at h
    have := le_abs_self (Real.exp ((32 + 4) * M) - 1)
    linarith
  have hexpβ : Real.exp (2 * (t₂ - t₁)) - 1 ≤ 4 * (t₂ - t₁) := by
    have h := Real.abs_exp_sub_one_le (x := 2 * (t₂ - t₁)) (abs_le.mpr ⟨by linarith, by linarith⟩)
    rw [abs_of_nonneg (show 0 ≤ 2 * (t₂ - t₁) by linarith)] at h
    have := le_abs_self (Real.exp (2 * (t₂ - t₁)) - 1)
    linarith
  have hEβ : E / (t₂ - t₁) ≤ CE * e3 := by rw [div_le_iff₀ hβ0]; exact hE
  have hM1 : 1 ≤ Real.exp ((32 + 4) * M) := Real.one_le_exp (by linarith)
  have hβ1 : 1 ≤ Real.exp (2 * (t₂ - t₁)) := Real.one_le_exp (by linarith)
  have hXβ : ((Real.exp ((32 + 4) * M) - 1) * (t₂ - t₁) + Real.exp ((32 + 4) * M) * E) / (t₂ - t₁) ≤
      72 * CM * e3 + 2 * CE * e3 := by
    rw [add_div, mul_div_assoc, div_self hβ0.ne', mul_one, mul_div_assoc]
    have h1 : Real.exp ((32 + 4) * M) ≤ 2 := by linarith
    have h2 : Real.exp ((32 + 4) * M) * (E / (t₂ - t₁)) ≤ 2 * (CE * e3) :=
      mul_le_mul h1 hEβ (div_nonneg hE0 hβ0.le) (by norm_num)
    have h3 := mul_le_mul_of_nonneg_left hM (by norm_num : (0 : ℝ) ≤ 72)
    generalize E / (t₂ - t₁) = q at h2 ⊢
    linarith
  have hX0 : 0 ≤ ((Real.exp ((32 + 4) * M) - 1) * (t₂ - t₁) + Real.exp ((32 + 4) * M) * E) /
      (t₂ - t₁) :=
    div_nonneg (add_nonneg (mul_nonneg (by linarith) hβ0.le) (mul_nonneg (by linarith) hE0)) hβ0.le
  have hδ : Real.exp (2 * (t₂ - t₁)) *
      (((Real.exp ((32 + 4) * M) - 1) * (t₂ - t₁) + Real.exp ((32 + 4) * M) * E) / (t₂ - t₁) +
        (Real.exp (2 * (t₂ - t₁)) - 1)) ≤ Cδ * e3 := by
    generalize ((Real.exp ((32 + 4) * M) - 1) * (t₂ - t₁) + Real.exp ((32 + 4) * M) * E) /
      (t₂ - t₁) = q at hXβ hX0 ⊢
    have h1 : Real.exp (2 * (t₂ - t₁)) ≤ 2 := by linarith
    have h16 : Real.exp (2 * (t₂ - t₁)) - 1 ≤ 16 * e3 := by linarith
    have h2 := mul_le_mul h1 (add_le_add hXβ h16) (add_nonneg hX0 (by linarith)) (by norm_num)
    have h3 := mul_le_mul_of_nonneg_right (show 2 * (72 * CM + 2 * CE + 16) ≤ Cδ by linarith) he3.le
    linarith
  have htr := s07c_fkps_m6_sh_transfer ht (by linarith : (0 : ℝ) ≤ 2 * (t₂ - t₁)) hΦ hd hP hPβ hu
    hc' hX
  have hΦlt : Φ t₁ < Φ t₂ := hΦ ht
  have hc0 : 0 < c' / P t₁ := div_pos hc' (hP t₁)
  have hred := s07c_fkps_m6_reduce hΦlt hu hu0 hc0 (hδ.trans hsmall) htr
  have hI0 : 0 ≤ ∫ t in (Φ t₁)..(Φ t₂), u t :=
    intervalIntegral.integral_nonneg hΦlt.le (fun t _ => hu0 t)
  refine hred.trans ?_
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ (by norm_num : (0 : ℝ) ≤ 4)) hI0
  exact this.trans_eq (by ring)

/-- C2.4 (short arcs, the R-trick): for `|I| ≤ ℓ₀ ε^{1/3}` put `R = ε^{-1/3}`, `z = (1 - R|I|) e^{is₀}` (`s₀` the
centre of `I`), take `G` from block B and its lift `T`, block A for `G`; `B = Φ_z⁻¹(I)` has `|B| ≍ 1/R` (C1.4),
`u(Φ_z) P_z = P_w(T) v` a.e. (C1.5, C1.7), C1.9 (with C1.8 for `F` on `Φ_z([s₀ ± 2π/3])` and for `G`) keeps `T(B)` off
the expanding point, C2.3 with `L = 32`, back to `I` by C2.2 and C1.3/C1.4 for `P_z` on `B`, then C2.1. -/
theorem s07c_fkps_m6_short : ∃ ε₀ ℓ₀ C : ℝ, 0 < ε₀ ∧ 0 < ℓ₀ ∧ 0 < C ∧
    ∀ (F : ℂ → ℂ) (a : ℂ → ℝ) (K ε : ℝ) (H u : ℝ → ℝ),
    IsKQC F univ K → F '' univ = univ → F '' unitDisc = unitDisc → F 0 = 0 →
    Measurable a → (∀ z, 0 ≤ a z) → (∀ z ∈ unitDisc, a z ≤ ε₀) →
    (∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) →
      ‖LiZhongQC.complexDilatation F w‖ ≤ a z) →
    0 ≤ ε → ε ≤ ε₀ →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
        ≤ ENNReal.ofReal (ε * r)) →
    StrictMono H → Continuous H → (∀ θ : ℝ, H (θ + 2 * π) = H θ + 2 * π) →
    (∀ θ : ℝ, F (Complex.exp (θ * Complex.I)) = Complex.exp (H θ * Complex.I)) →
    (∀ a b : ℝ, IntegrableOn u (Icc a b)) → (∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t) →
    ∀ a b : ℝ, a < b → b - a ≤ ℓ₀ * ε ^ (1 / 3 : ℝ) →
      ∫ t in a..b, |u t - (∫ s in a..b, u s) / (b - a)| ≤ C * ε ^ (1 / 3 : ℝ) * ∫ t in a..b, u t := by
  obtain ⟨εG, CG, hεG, hCG, hG⟩ := s07c_fkps_m6_global
  obtain ⟨CB, hCB, hB⟩ := s07c_fkps_m6_renorm
  have hCB0 : 0 < CB := lt_of_lt_of_le one_pos hCB
  have hD0 : 0 < CG * CB := mul_pos hCG hCB0
  obtain ⟨CM, hCM⟩ : ∃ CM : ℝ, CM = 12 + 4 * (CG * CB) := ⟨_, rfl⟩
  obtain ⟨Cδ, hCδ⟩ : ∃ Cδ : ℝ, Cδ = 3 * (72 * CM + 3 * (2 * (CG * CB)) + 16) := ⟨_, rfl⟩
  have hCMp : 0 < CM := by rw [hCM]; positivity
  have hCδp : 0 < Cδ := by rw [hCδ]; positivity
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = min (1 / 320) (min (1 / (320 * CG)) (1 / (320 * Cδ))) := ⟨_, rfl⟩
  have hκp : 0 < κ := by
    rw [hκ]
    exact lt_min (by norm_num) (lt_min (div_pos one_pos (mul_pos (by norm_num) hCG))
      (div_pos one_pos (mul_pos (by norm_num) hCδp)))
  have hκ1 : κ ≤ 1 / 320 := by rw [hκ]; exact min_le_left _ _
  have hκG : CG * κ ≤ 1 / 320 := by
    have h1 : κ ≤ 1 / (320 * CG) := by rw [hκ]; exact (min_le_right _ _).trans (min_le_left _ _)
    have h2 : CG * (1 / (320 * CG)) = 1 / 320 := by
      have := hCG.ne'
      field_simp
    calc CG * κ ≤ CG * (1 / (320 * CG)) := mul_le_mul_of_nonneg_left h1 hCG.le
      _ = 1 / 320 := h2
  have hκδ : Cδ * κ ≤ 1 / 320 := by
    have h1 : κ ≤ 1 / (320 * Cδ) := by rw [hκ]; exact (min_le_right _ _).trans (min_le_right _ _)
    have h2 : Cδ * (1 / (320 * Cδ)) = 1 / 320 := by
      have := hCδp.ne'
      field_simp
    calc Cδ * κ ≤ Cδ * (1 / (320 * Cδ)) := mul_le_mul_of_nonneg_left h1 hCδp.le
      _ = 1 / 320 := h2
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℝ, ε₀ = min (min (εG / CB) (1 / (2 * CB))) (κ ^ 6 / CB) := ⟨_, rfl⟩
  have hε₀p : 0 < ε₀ := by
    rw [hε₀]
    exact lt_min (lt_min (div_pos hεG hCB0) (div_pos one_pos (mul_pos two_pos hCB0)))
      (div_pos (pow_pos hκp 6) hCB0)
  refine ⟨ε₀, 1 / 18, 4 * Cδ, hε₀p, by norm_num, mul_pos (by norm_num) hCδp, ?_⟩
  intro F a K ε H u hF hFs hFD hF0 ha ha0 hale hW hε hεε₀ hC hHm hHc hHp hHF hui hrep x y hxy hshort
  -- smallness of `ε`
  have hmulCB : ∀ q : ℝ, ε₀ ≤ q / CB → CB * ε₀ ≤ q := fun q h => by
    have := mul_le_mul_of_nonneg_left h hCB0.le
    rwa [mul_div_cancel₀ _ hCB0.ne'] at this
  have hCBε₀ : CB * ε₀ ≤ 1 / 2 := hmulCB (1 / 2) (by
    rw [hε₀, div_div]; exact (min_le_left _ _).trans (min_le_right _ _))
  have hCBε₀G : CB * ε₀ ≤ εG :=
    hmulCB εG (by rw [hε₀]; exact (min_le_left _ _).trans (min_le_left _ _))
  have hCBε₀κ : CB * ε₀ ≤ κ ^ 6 := hmulCB _ (by rw [hε₀]; exact min_le_right _ _)
  have hε₀G : ε₀ ≤ εG := (le_mul_of_one_le_left hε₀p.le hCB).trans hCBε₀G
  have hCBεε₀ : CB * ε ≤ CB * ε₀ := mul_le_mul_of_nonneg_left hεε₀ hCB0.le
  have hCBεG : CB * ε ≤ εG := hCBεε₀.trans hCBε₀G
  have hCBεκ : CB * ε ≤ κ ^ 6 := hCBεε₀.trans hCBε₀κ
  have hεG' : ε ≤ εG := hεε₀.trans hε₀G
  have hεp : 0 < ε := by
    rcases hε.lt_or_eq with h | h
    · exact h
    · rw [← h, Real.zero_rpow (by norm_num), mul_zero] at hshort; linarith
  obtain ⟨h3, he3κ, hsε, hsCBκ, hsCB, h6, h6'⟩ :=
    s07c_fkps_m6_sh_eps hεp hCB hκp (hκ1.trans (by norm_num)) hCBεκ
  generalize he3 : ε ^ (1 / 3 : ℝ) = e3 at h3 he3κ hsε hshort ⊢
  have he3s : e3 ≤ 1 / 320 := he3κ.trans hκ1
  have hse3 : Real.sqrt e3 ≤ 1 := by
    have := Real.sqrt_le_sqrt (show e3 ≤ 1 by linarith)
    rwa [Real.sqrt_one] at this
  have hcH : CG * Real.sqrt ε ≤ 1 / 320 := by
    have h1 : Real.sqrt ε ≤ κ := by
      rw [hsε]; exact (mul_le_of_le_one_right h3.le hse3).trans he3κ
    exact (mul_le_mul_of_nonneg_left h1 hCG.le).trans hκG
  have hcT : CG * Real.sqrt (CB * ε) ≤ 1 / 320 := (mul_le_mul_of_nonneg_left hsCBκ hCG.le).trans hκG
  have hδF : CG * ε ^ (1 / 6 : ℝ) ≤ 1 / 320 := (mul_le_mul_of_nonneg_left h6 hCG.le).trans hκG
  have hδG : CG * (CB * ε) ^ (1 / 6 : ℝ) ≤ 1 / 320 := (mul_le_mul_of_nonneg_left h6' hCG.le).trans hκG
  have hsmall : Cδ * e3 ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left he3κ hCδp.le).trans (hκδ.trans (by norm_num))
  -- block A for `F`
  obtain ⟨u', ρF, hui', hrep', hu0', hρF0, -, hρFL, hρFδ, hAF⟩ := hG F a K ε H hF hFs hFD hF0 ha ha0
    (fun z hz => (hale z hz).trans hε₀G) hW hε hεG' hC hHm hHc hHp hHF
  have hae : u =ᵐ[volume] u' := s07c_fkps_m6_dens_ae hui hui' hrep hrep'
  have e1 : ∫ s in x..y, u s = ∫ s in x..y, u' s :=
    intervalIntegral.integral_congr_ae (hae.mono fun t ht _ => ht)
  have e2 : ∫ t in x..y, |u t - (∫ s in x..y, u s) / (y - x)| =
      ∫ t in x..y, |u' t - (∫ s in x..y, u' s) / (y - x)| := by
    rw [e1]
    exact intervalIntegral.integral_congr_ae (hae.mono fun t ht _ => by rw [ht])
  rw [e2, e1]
  -- the renormalisation point `z = (1 - ρ') e^{is₀}`
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℝ, s₀ = (x + y) / 2 := ⟨_, rfl⟩
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : ℝ, ρ' = (y - x) / e3 := ⟨_, rfl⟩
  have hρ'0 : 0 < ρ' := by rw [hρ']; exact div_pos (sub_pos.mpr hxy) h3
  have hρ'18 : ρ' ≤ 1 / 18 := by rw [hρ', div_le_iff₀ h3]; exact hshort
  have hℓe : y - x = ρ' * e3 := by rw [hρ', div_mul_cancel₀ _ h3.ne']
  have hr0 : 0 ≤ 1 - ρ' := by linarith
  have hr1 : 1 - ρ' < 1 := by linarith
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = ((1 - ρ' : ℝ) : ℂ) * Complex.exp (s₀ * I) := ⟨_, rfl⟩
  obtain ⟨hzn, hΦs₀, hz1, hzlo, hzhi⟩ := s07c_fkps_m6_poisson_box hr0 hr1 hz
  have hzr : ‖z‖ < 1 := by rw [hzn]; exact hr1
  have hzD : z ∈ unitDisc := mem_ball_zero_iff.mpr hzr
  have hsq : ρ' ^ 2 ≤ ρ' := by rw [sq]; exact mul_le_of_le_one_left hρ'0.le (by linarith)
  have h1r1 : ρ' ≤ 1 - (1 - ρ') ^ 2 := by
    have : 1 - (1 - ρ') ^ 2 = 2 * ρ' - ρ' ^ 2 := by ring
    linarith
  have h1r2 : 1 - (1 - ρ') ^ 2 ≤ 2 * ρ' := by
    have : 1 - (1 - ρ') ^ 2 = 2 * ρ' - ρ' ^ 2 := by ring
    linarith [sq_nonneg ρ']
  -- block B, the lift `T` of `G`, block A for `G`
  obtain ⟨G, bG, hG1, hG2, hG3, hG4, hbm, hb0, hble, hbW, hbC, hFG⟩ :=
    hB F a K ε₀ ε hF hFs hFD hF0 ha ha0 hale hW hε hC z hzD
  have hμ := s07c_fkps_m6_dil_le hble hbW
  have hK' := s07c_fkps_m6_kqc hG1 (mul_nonneg hCB0.le hε₀p.le)
    (lt_of_le_of_lt hCBε₀ (by norm_num)) hμ
  have hGc : Continuous G := continuousOn_univ.mp hG1.2.2.1.1
  have hbv : HasDiskBoundaryValues G G := fun ζ _ =>
    hGc.continuousAt.continuousWithinAt.tendsto
  obtain ⟨T, hTm, hTc, hTp, hTG⟩ := s07_circleHomeo_of_qcExt hK' hG3 hbv
  obtain ⟨v, ρG, hv, hrepT, hv0, hρG0, -, hρGL, hρGδ, hAG⟩ := hG G bG K (CB * ε) T hG1 hG2 hG3 hG4
    hbm hb0 (fun q hq => (hble q hq).trans hCBε₀G) hbW (mul_nonneg hCB0.le hε) hCBεG hbC
    hTm hTc hTp hTG
  have hwD : F z ∈ unitDisc := by rw [← hFD]; exact mem_image_of_mem F hzD
  have hw : ‖F z‖ < 1 := mem_ball_zero_iff.mp hwD
  obtain ⟨k, hk⟩ := s07c_fkps_m6_conj_lift hzr hw hFG hHc hHF hTc hTG
  have hch := s07c_fkps_m6_ae_chain hzr hw hui' hrep' hv hrepT hk
  obtain ⟨-, hzd, hzP, hzm, -⟩ := s07c_fkps_m6_mob hzr
  obtain ⟨-, -, hwP, -, -⟩ := s07c_fkps_m6_mob hw
  -- opaque names for `Φ_z` and `P_z`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ → ℝ, Φ = fun t : ℝ => t + 2 * arg (1 + z * Complex.exp (-(t * I))) :=
    ⟨_, rfl⟩
  obtain ⟨Pz, hPz⟩ : ∃ P : ℝ → ℝ, P = fun t : ℝ => (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) + z‖ ^ 2 :=
    ⟨_, rfl⟩
  have hzd' : ∀ t, HasDerivAt Φ (Pz t) t := by rw [hΦ, hPz]; exact hzd
  have hzP' : ∀ t, 0 < Pz t := by rw [hPz]; exact hzP
  have hzm' : StrictMono Φ := by rw [hΦ]; exact hzm
  have hΦs₀' : Φ s₀ = s₀ := by rw [hΦ]; exact hΦs₀
  have hπ3 := Real.pi_gt_three
  have hzhi' : ∀ t, |t - s₀| ≤ 2 * π / 3 → Pz t ≤ 4 * ρ' := by
    intro t ht
    have h := hzhi (t - s₀) ht
    rw [add_sub_cancel] at h
    rw [hPz]
    show (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) + z‖ ^ 2 ≤ 4 * ρ'
    linarith
  have hB2 : ∀ t, |t - s₀| ≤ 2 * e3 → ρ' / 4 ≤ Pz t ∧ Pz t ≤ 4 * ρ' := by
    intro t ht
    have ht' : |t - s₀| ≤ π / 2 := by linarith
    have h := hzlo (t - s₀) ht'
    rw [add_sub_cancel] at h
    refine ⟨?_, hzhi' t (by linarith)⟩
    rw [hPz]
    show ρ' / 4 ≤ (1 - ‖z‖ ^ 2) / ‖Complex.exp (t * I) + z‖ ^ 2
    have := div_le_div_of_nonneg_right h1r1 (by norm_num : (0 : ℝ) ≤ 4)
    linarith
  have hz1' : ∀ t, |t - s₀| ≤ 2 * e3 → 1 ≤ ‖Complex.exp (t * I) + z‖ := by
    intro t ht
    have h := hz1 (t - s₀) (by linarith)
    rwa [add_sub_cancel] at h
  have hk' : ∀ t, H (Φ t) = (T t + 2 * arg (1 + F z * Complex.exp (-(T t * I)))) + 2 * π * k := by
    rw [hΦ]; exact hk
  have hch' : ∀ᵐ t : ℝ, u' (Φ t) * Pz t =
      (1 - ‖F z‖ ^ 2) / ‖Complex.exp (T t * I) + F z‖ ^ 2 * v t := by
    rw [hΦ, hPz]; exact hch
  clear hzd hzP hzm hΦs₀ hzlo hzhi hz1 hk hch
  -- the arc `B = [t₁, t₂]`, `Φ(B) = [x, y]`
  obtain ⟨t₁, t₂, ht12, hΦt₁, hΦt₂, hβlo, hβhi, hBin⟩ :=
    s07c_fkps_m6_sh_arc h3 hρ'0 hzd' hzP' hzm' hΦs₀' hB2 hs₀ hℓe
  -- `T(B)` stays away from the expanding point of `φ_{F z}`
  have hpos := s07c_fkps_m6_sh_pos hw hρ'0 hρ'18 hTm.monotone
    (fun x' y' h1 h2 => s07c_fkps_m6_sh_incr h1 h2 hv hrepT hv0 hTc hρG0 hρGL hρGδ
      (hδG.trans (by norm_num)) hAG)
    (fun x' y' h1 h2 => s07c_fkps_m6_sh_incr h1 h2 hui' hrep' hu0' hHc hρF0 hρFL hρFδ
      (hδF.trans (by norm_num)) hAF)
    hcT hδG hcH hδF hzd' hzP' hzm' hzhi' hk'
  -- the core estimate on `B`
  have hPwc : Continuous fun τ : ℝ => (1 - ‖F z‖ ^ 2) / ‖Complex.exp (τ * I) + F z‖ ^ 2 := by
    refine continuous_const.div (by fun_prop) (fun τ h0 => ?_)
    have := hwP τ
    rw [h0, div_zero] at this
    exact lt_irrefl _ this
  have ht₁s : s₀ - 1 / 16 ≤ t₁ := by
    have := (abs_le.mp (hBin t₁ ⟨le_rfl, ht12.le⟩)).1
    linarith
  have ht₂s : t₂ ≤ s₀ + 1 / 16 := by
    have := (abs_le.mp (hBin t₂ ⟨ht12.le, le_rfl⟩)).2
    linarith
  have hTB : ∀ τ ∈ Icc (T t₁) (T t₂), τ ∈ Icc (T (s₀ - 1 / 16)) (T (s₀ + 1 / 16)) := fun τ hτ =>
    ⟨(hTm.monotone ht₁s).trans hτ.1, hτ.2.trans (hTm.monotone ht₂s)⟩
  have hPL : ∀ τ ∈ Icc (T t₁) (T t₂), ∀ τ' ∈ Icc (T t₁) (T t₂),
      (1 - ‖F z‖ ^ 2) / ‖Complex.exp (τ' * I) + F z‖ ^ 2 ≤
        Real.exp (32 * |τ - τ'|) * ((1 - ‖F z‖ ^ 2) / ‖Complex.exp (τ * I) + F z‖ ^ 2) := by
    intro τ hτ τ' hτ'
    have h := s07c_fkps_m6_mob_loglip hw (m := 1 / 16) (t := τ) (t' := τ') (by norm_num)
      (fun q hq => hpos q (hTB q ((uIcc_subset_Icc hτ hτ') hq)))
    rwa [show 2 * |τ' - τ| / (1 / 16) = 32 * |τ - τ'| by rw [abs_sub_comm]; ring] at h
  have hEB : ∫ t in t₁..t₂, |2 * π * ρG (T t) * v t - 1| ≤
      CG * Real.sqrt (CB * ε) * Real.sqrt (t₂ - t₁) := by
    have h := hAG t₁ (Icc t₁ t₂) measurableSet_Icc (Icc_subset_Icc le_rfl (by linarith))
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)] at h
    rwa [intervalIntegral.integral_of_le ht12.le, ← integral_Icc_eq_integral_Ioc]
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = (1 - ‖F z‖ ^ 2) / ‖Complex.exp (T t₁ * I) + F z‖ ^ 2 /
      (2 * π * ρG (T t₁)) := ⟨_, rfl⟩
  have hc'0 : 0 < c' := by
    rw [hc']
    exact div_pos (hwP _) (mul_pos (mul_pos two_pos Real.pi_pos) (hρG0 _))
  have hcore := s07c_fkps_m6_core (g := fun t => u' (Φ t) * Pz t) (T := T) (v := v) (ρ := ρG)
    (P := fun τ : ℝ => (1 - ‖F z‖ ^ 2) / ‖Complex.exp (τ * I) + F z‖ ^ 2) (L := 32) ht12.le
    (by norm_num) hTm.monotone hTc (hv t₁ t₂) hv0 hρG0 hρGL hwP hPwc hPL hEB
    (hch'.mono fun t h _ => h)
  beta_reduce at hcore
  rw [← hc'] at hcore
  -- `|T(B)|` and `E`
  have hTinc := s07c_fkps_m6_sh_incr ht12.le (by linarith) hv hrepT hv0 hTc hρG0 hρGL hρGδ
    (hδG.trans (by norm_num)) hAG
  have hAle : CG * Real.sqrt (CB * ε) ≤ CG * CB * (e3 * Real.sqrt e3) := by
    calc CG * Real.sqrt (CB * ε) ≤ CG * (CB * Real.sqrt ε) := mul_le_mul_of_nonneg_left hsCB hCG.le
      _ = CG * CB * (e3 * Real.sqrt e3) := by rw [hsε]; ring
  obtain ⟨hME1, hME2⟩ := s07c_fkps_m6_sh_ME (A := CG * Real.sqrt (CB * ε))
    (B := CG * (CB * ε) ^ (1 / 6 : ℝ)) (D := CG * CB) h3 hβlo hβhi
    (mul_nonneg hCG.le (Real.sqrt_nonneg _)) hAle hD0.le (hδG.trans (by norm_num)) (by linarith)
  have hM : T t₂ - T t₁ ≤ CM * e3 := by
    have := (abs_le.mp hTinc).2
    rw [hCM]
    linarith
  -- `P_z` on `B`, and the conclusion
  have hPβ : ∀ t ∈ Icc t₁ t₂,
      Pz t ≤ Real.exp (2 * (t₂ - t₁)) * Pz t₁ ∧ Pz t₁ ≤ Real.exp (2 * (t₂ - t₁)) * Pz t := by
    rw [hPz]
    exact s07c_fkps_m6_sh_pbeta hzr ht12.le (fun t ht => hz1' t (hBin t ht))
  have hfin := s07c_fkps_m6_sh_fin (CM := CM) (CE := 2 * (CG * CB)) (Cδ := Cδ)
    (E := CG * Real.sqrt (CB * ε) * Real.sqrt (t₂ - t₁)) ht12 h3 hβhi hzm'
    hzd' hzP' hPβ (hui' _ _) hu0' hc'0 hCMp.le (mul_pos two_pos hD0).le
    (sub_nonneg.mpr (hTm.monotone ht12.le)) hM
    (mul_nonneg (mul_nonneg hCG.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) hME2
    hCδ.symm.le hsmall hcore
  rwa [hΦt₁, hΦt₂] at hfin

/-! ### C3: small A∞ ⇒ small BMO -/

/-- Helper for C3 (`s07c_fkps_m6_jn_lower`): an integrable nonnegative `u` on `[a, b]` agrees a.e. on `[a, b]`
with a measurable nonnegative function. -/
theorem s07c_fkps_m6_jn_mod {u : ℝ → ℝ} {a b : ℝ} (hu : IntegrableOn u (Icc a b)) (hu0 : ∀ t, 0 ≤ u t) :
    ∃ w : ℝ → ℝ, Measurable w ∧ (∀ t, 0 ≤ w t) ∧ ∀ᵐ t, t ∈ Icc a b → u t = w t := by
  have hm := hu.aemeasurable
  refine ⟨fun t => max (AEMeasurable.mk u hm t) 0, hm.measurable_mk.max measurable_const,
    fun t => le_max_right _ _, ?_⟩
  filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp hm.ae_eq_mk] with t ht htI
  rw [← ht htI]
  exact (max_eq_left (hu0 t)).symm

/-- Helper for C3 (Chebyshev on a cell): if `∫_q^r |u - c| ≤ η c (r - q)` then
`|{κ c ≤ |u - c|} ∩ [q, r)| ≤ (η/κ)(r - q)`. -/
theorem s07c_fkps_m6_jn_cheb {u : ℝ → ℝ} {q r c κ η : ℝ} (hqr : q < r) (hc : 0 < c) (hκ : 0 < κ)
    (hη : 0 ≤ η) (hi : IntegrableOn u (Icc q r))
    (hosc : ∫ t in q..r, |u t - c| ≤ η * (c * (r - q))) :
    volume ({t | κ * c ≤ |u t - c|} ∩ Ico q r) ≤ ENNReal.ofReal (η / κ * (r - q)) := by
  have hfi0 : IntegrableOn (fun t => |u t - c|) (Icc q r) :=
    (hi.sub (continuous_const (y := c)).integrableOn_Icc).abs
  have hfi : IntegrableOn (fun t => |u t - c|) (Ico q r) := hfi0.mono_set Ico_subset_Icc_self
  have h := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Ico q r))
    (Eventually.of_forall fun t => abs_nonneg (u t - c)) hfi (κ * c)
  rw [measureReal_def, Measure.restrict_apply' measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hqr.le] at h
  have hfin : volume ({t | κ * c ≤ |u t - c|} ∩ Ico q r) ≠ ⊤ :=
    ((measure_mono inter_subset_right).trans_lt measure_Ico_lt_top).ne
  have hqr' : 0 ≤ r - q := by linarith
  rw [ENNReal.le_ofReal_iff_toReal_le hfin (by positivity)]
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = (volume ({t | κ * c ≤ |u t - c|} ∩ Ico q r)).toReal := ⟨_, rfl⟩
  rw [← hV] at h ⊢
  have h2 := h.trans hosc
  rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
  have h3 : c * (V * κ) ≤ c * (η * (r - q)) := by
    calc c * (V * κ) = κ * c * V := by ring
      _ ≤ η * (c * (r - q)) := h2
      _ = c * (η * (r - q)) := by ring
  exact le_of_mul_le_mul_left h3 hc

/-- C3.1 (upper tail): `log x ≤ x - 1` gives `∫_I (log(u/u_I))₊ ≤ η|I|`. -/
theorem s07c_fkps_m6_jn_upper {u : ℝ → ℝ} {a b η : ℝ} (hab : a < b) (hu : IntegrableOn u (Icc a b))
    (hu0 : ∀ t, 0 ≤ u t) (hpos : 0 < ∫ t in a..b, u t)
    (hA : ∫ t in a..b, |u t - (∫ s in a..b, u s) / (b - a)| ≤ η * ∫ t in a..b, u t) :
    IntegrableOn (fun t => max (Real.log (u t / ((∫ s in a..b, u s) / (b - a)))) 0) (Icc a b) ∧
    ∫ t in a..b, max (Real.log (u t / ((∫ s in a..b, u s) / (b - a)))) 0 ≤ η * (b - a) := by
  have hba : 0 < b - a := by linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (∫ s in a..b, u s) / (b - a) := ⟨_, rfl⟩
  rw [← hc] at hA ⊢
  have hc0 : 0 < c := hc ▸ div_pos hpos hba
  have hbd : ∀ t, max (Real.log (u t / c)) 0 ≤ |u t - c| / c := by
    intro t
    refine max_le ?_ (div_nonneg (abs_nonneg _) hc0.le)
    rcases (hu0 t).lt_or_eq with ht | ht
    · have h1 := Real.log_le_sub_one_of_pos (div_pos ht hc0)
      have h2 : u t / c - 1 = (u t - c) / c := by field_simp
      rw [h2] at h1
      refine h1.trans ?_
      gcongr
      exact le_abs_self _
    · rw [← ht, zero_div, Real.log_zero]
      exact div_nonneg (abs_nonneg _) hc0.le
  have hgi : IntegrableOn (fun t => |u t - c| / c) (Icc a b) :=
    (hu.sub (continuous_const (y := c)).integrableOn_Icc).abs.div_const c
  have hfm : AEStronglyMeasurable (fun t => max (Real.log (u t / c)) 0) (volume.restrict (Icc a b)) :=
    ((Real.measurable_log.comp_aemeasurable (hu.aemeasurable.div_const c)).max
      aemeasurable_const).aestronglyMeasurable
  have hfi : IntegrableOn (fun t => max (Real.log (u t / c)) 0) (Icc a b) := by
    refine Integrable.mono' hgi hfm (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact hbd t
  refine ⟨hfi, ?_⟩
  calc ∫ t in a..b, max (Real.log (u t / c)) 0 ≤ ∫ t in a..b, |u t - c| / c :=
        intervalIntegral.integral_mono_on hab.le
          ((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hfi)
          ((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hgi) fun t _ => hbd t
    _ = (∫ t in a..b, |u t - c|) / c := intervalIntegral.integral_div _ _
    _ ≤ (η * ∫ t in a..b, u t) / c := by gcongr
    _ = η * (b - a) := by
        rw [hc]
        field_simp [hpos.ne', hba.ne']

/-- C3.2 (dyadic Lebesgue differentiation on `(a, b]`): a.e. `x` with `u x < θ` lies in a dyadic subinterval
`D_{j,m}` with `∫_{D_{j,m}} u < θ |D_{j,m}|` (Mathlib `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub`). -/
theorem s07c_fkps_m6_jn_ldiff {u : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hu : IntegrableOn u (Icc a b)) :
    ∀ᵐ x, x ∈ Ioc a b → ∀ θ : ℝ, u x < θ → ∃ j m : ℕ, m < 2 ^ j ∧
      x ∈ Ioc (a + (m : ℝ) * (b - a) / (2 : ℝ) ^ j) (a + ((m : ℝ) + 1) * (b - a) / (2 : ℝ) ^ j) ∧
      (∫ t in (a + (m : ℝ) * (b - a) / (2 : ℝ) ^ j)..(a + ((m : ℝ) + 1) * (b - a) / (2 : ℝ) ^ j), u t) <
        θ * ((b - a) / (2 : ℝ) ^ j) := by
  -- Lebesgue points (`s07_jn_lebesgue`, half-open cells `[c, c + r)`) of `u 1_{[a,b]}`; a.e. `x` is no
  -- dyadic endpoint, so the half-open cell of `x` is also its `Ioc` cell
  have hba : 0 < b - a := by linarith
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = (Icc a b).indicator u := ⟨_, rfl⟩
  have hgi : Integrable g := hg ▸ hu.integrable_indicator measurableSet_Icc
  have hgu : ∀ t ∈ Icc a b, g t = u t := fun t ht => by
    rw [hg]
    exact indicator_of_mem ht u
  have hL := s07_jn_lebesgue (g := g) fun _ _ => hgi.integrableOn
  have hE : ∀ᵐ x : ℝ, ∀ j : ℕ, ∀ n : ℤ, x ≠ a + n * ((b - a) / 2 ^ j) := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro n
    exact compl_mem_ae_iff.mpr (measure_singleton _)
  filter_upwards [hL, hE] with x hx hxE
  intro hxI θ hθ
  have hxI' : x ∈ Icc a b := Ioc_subset_Icc_self hxI
  obtain ⟨ρ, hρ, hρP⟩ := hx ((θ - u x) / 2) (by linarith)
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt ((b - a) / ρ) one_lt_two
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (b - a) / 2 ^ j := ⟨_, rfl⟩
  have hpw : (0 : ℝ) < 2 ^ j := by positivity
  have hs0 : 0 < s := hs ▸ div_pos hba hpw
  have hsb : (2 : ℝ) ^ j * s = b - a := by
    rw [hs]
    field_simp
  have hsρ : s < ρ := by
    rw [hs, div_lt_iff₀ hpw]
    rw [div_lt_iff₀ hρ] at hj
    linarith
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = ⌊(x - a) / s⌋ := ⟨_, rfl⟩
  have hxC : x ∈ Ico (a + k * s) (a + (k + 1) * s) := (s07_cz_cell_iff hs0 k).mp hk.symm
  have hxl : x ≠ a + k * s := by
    rw [hs]
    exact hxE j k
  have hxl' : a + k * s < x := lt_of_le_of_ne hxC.1 (Ne.symm hxl)
  have hk0 : 0 ≤ k := by
    by_contra h
    rw [not_le] at h
    have h1 : k ≤ -1 := by omega
    have h2 : (k : ℝ) ≤ -1 := by exact_mod_cast h1
    have h3 := hxC.2
    have h4 := hxI.1
    nlinarith
  have hk2 : k < 2 ^ j := by
    by_contra h
    rw [not_lt] at h
    have h2 : (2 : ℝ) ^ j ≤ k := by exact_mod_cast h
    have h4 := hxI.2
    nlinarith
  have hmk : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0
  have hmR : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast hmk
  have hm : k.toNat < 2 ^ j := by
    have h := hk2
    rw [← hmk] at h
    exact_mod_cast h
  have hk1 : (k : ℝ) + 1 ≤ 2 ^ j := by
    have h : k + 1 ≤ 2 ^ j := hk2
    exact_mod_cast h
  have e1 : a + ((k.toNat : ℕ) : ℝ) * (b - a) / (2 : ℝ) ^ j = a + k * s := by
    rw [hmR, hs]
    ring
  have e2 : a + (((k.toNat : ℕ) : ℝ) + 1) * (b - a) / (2 : ℝ) ^ j = a + k * s + s := by
    rw [hmR, hs]
    ring
  refine ⟨j, k.toNat, hm, ?_, ?_⟩
  · rw [e1, e2]
    exact ⟨hxl', by linarith [hxC.2]⟩
  · rw [e1, e2, ← hs]
    have hc1 : a ≤ a + k * s := by
      have : (0 : ℝ) ≤ k * s := mul_nonneg (by exact_mod_cast hk0) hs0.le
      linarith
    have hc2 : a + k * s + s ≤ b := by nlinarith
    have hP := hρP (a + k * s) s hs0 hsρ ⟨hxC.1, by linarith [hxC.2]⟩
    have hint : ∫ t in (a + k * s)..(a + k * s + s), g t = ∫ t in (a + k * s)..(a + k * s + s), u t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le (by linarith)] at ht
      exact hgu t ⟨hc1.trans ht.1, ht.2.trans hc2⟩
    rw [hint, hgu x hxI', abs_le] at hP
    have h5 : (∫ t in (a + k * s)..(a + k * s + s), u t) / s < θ := by linarith [hP.2]
    rwa [div_lt_iff₀ hs0] at h5

/-- C3.3 (Calderón–Zygmund step): for `0 < λ ≤ u_I` and small A∞ on all subintervals of `I`,
`|{u < λ/2} ∩ I| ≤ 5η |{u < λ} ∩ I|`. Stopping intervals: maximal dyadic `J ⊆ I` with `u_J < λ/√2` (C3.2); the parent
gives `u_J ≥ (1 - 2η)λ/√2`, so `|{u < λ/2} ∩ J| ≤ 4η|J|` and `|{u < λ} ∩ J| ≥ (1 - 5η/2)|J|`. -/
theorem s07c_fkps_m6_jn_step : ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ (u : ℝ → ℝ) (a b η l : ℝ), a < b → 0 ≤ η → η ≤ η₁ →
    IntegrableOn u (Icc a b) → (∀ t, 0 ≤ u t) → 0 < l → l ≤ (∫ s in a..b, u s) / (b - a) →
    (∀ c d : ℝ, a ≤ c → c < d → d ≤ b →
      ∫ t in c..d, |u t - (∫ s in c..d, u s) / (d - c)| ≤ η * ∫ t in c..d, u t) →
    (volume ({t | u t < l / 2} ∩ Ioc a b)).toReal ≤ 5 * η * (volume ({t | u t < l} ∩ Ioc a b)).toReal := by
  -- η₁ = 1/40, stopping level θ = 3λ/4 (cells of `s07_jn_step`): on a maximal dyadic `J ⊆ [a, b)` with
  -- `u_J < θ` the parent gives `u_J ≥ (1 - 2η)θ`, so (Chebyshev, `s07c_fkps_m6_jn_cheb`)
  -- `|{u < λ/2} ∩ J| ≤ 4η|J|` and `|J \ {u < λ}| ≤ 3η|J|`; a.e. point of `{u < λ/2} ∩ [a, b)` is covered
  refine ⟨1 / 40, by norm_num, ?_⟩
  intro u a b η l hab hη0 hη1 hu hu0 hl hlc hosc
  classical
  have hba : 0 < b - a := by linarith
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 3 / 4 * l := ⟨_, rfl⟩
  have hsub_int : ∀ p q : ℝ, a ≤ p → q ≤ b → IntegrableOn u (Icc p q) := fun p q hp hq =>
    hu.mono_set (Icc_subset_Icc hp hq)
  have hii : ∀ p q : ℝ, a ≤ p → p ≤ q → q ≤ b → IntervalIntegrable u volume p q :=
    fun p q hp hpq hq => (intervalIntegrable_iff_integrableOn_Icc_of_le hpq).mpr (hsub_int p q hp hq)
  -- dyadic cells of `[a, b)`
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, s = fun n => (b - a) / 2 ^ n := ⟨_, rfl⟩
  have hs0 : ∀ n, 0 < s n := fun n => by
    simp only [hs]
    exact div_pos hba (by positivity)
  have hs1 : ∀ n, s (n + 1) = s n / 2 := fun n => by
    simp only [hs]
    rw [pow_succ, div_div]
  have hs00 : s 0 = b - a := by simp [hs]
  obtain ⟨K, hK⟩ : ∃ K : ℕ → ℝ → ℤ, K = fun n x => ⌊(x - a) / s n⌋ := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ → ℤ → Set ℝ,
      C = fun n (k : ℤ) => Ico (a + k * s n) (a + (k + 1) * s n) := ⟨_, rfl⟩
  have hKC : ∀ n x k, K n x = k ↔ x ∈ C n k := fun n x k => by
    simp only [hK, hC]
    exact s07_cz_cell_iff (hs0 n) k
  have hmemC : ∀ n x, x ∈ C n (K n x) := fun n x => (hKC n x _).mp rfl
  have hnest : ∀ n x, C (n + 1) (K (n + 1) x) ⊆ C n (K n x) := fun n x => by
    simp only [hK, hC]
    rw [hs1]
    exact s07_cz_cell_nest (hs0 n)
  have hnest' : ∀ m n, m ≤ n → ∀ x, C n (K n x) ⊆ C m (K m x) := by
    intro m n hmn x
    induction n, hmn using Nat.le_induction with
    | base => exact subset_rfl
    | succ n _ ih => exact (hnest n x).trans ih
  have hsame : ∀ m n, m ≤ n → ∀ x y, K n y = K n x → K m y = K m x := by
    intro m n hmn x y h
    exact (hKC m y _).mpr (hnest' m n hmn x ((hKC n y _).mp h))
  have eab : a + (b - a) = b := by ring
  have hK0 : ∀ x ∈ Ico a b, K 0 x = 0 := by
    intro x hx
    rw [hKC]
    simp only [hC, hs00, Int.cast_zero, zero_mul, add_zero, zero_add, one_mul, eab]
    exact hx
  have hC0 : ∀ x ∈ Ico a b, C 0 (K 0 x) = Ico a b := by
    intro x hx
    rw [hK0 x hx]
    simp only [hC, hs00, Int.cast_zero, zero_mul, add_zero, zero_add, one_mul, eab]
  have hCeq : ∀ n k, C n k = Ico (a + k * s n) (a + k * s n + s n) := fun n k => by
    simp only [hC]
    congr 1
    ring
  -- the stopping quantity: mean of `u` over a cell
  obtain ⟨dv, hdv⟩ : ∃ dv : ℕ → ℤ → ℝ,
      dv = fun n (k : ℤ) => (∫ t in (a + k * s n)..(a + k * s n + s n), u t) / s n := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ × ℤ → Set ℝ, A = fun p => {x | x ∈ Ico a b ∧
      dv p.1 (K p.1 x) < θ ∧ (∀ m < p.1, ¬ dv m (K m x) < θ) ∧ K p.1 x = p.2} :=
    ⟨_, rfl⟩
  -- each nonempty `A p` is the whole cell `C p.1 p.2`
  have hAcell : ∀ p : ℕ × ℤ, ∀ x₀ ∈ A p, A p = C p.1 p.2 := by
    intro p x₀ hx₀
    simp only [hA, mem_ofPred_eq] at hx₀
    obtain ⟨hx₀J, hx₀b, hx₀g, hx₀k⟩ := hx₀
    ext y
    simp only [hA, mem_ofPred_eq]
    constructor
    · rintro ⟨-, -, -, hyk⟩
      exact (hKC _ _ _).mp hyk
    · intro hy
      have hyk : K p.1 y = K p.1 x₀ := by rw [hx₀k]; exact (hKC _ _ _).mpr hy
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← hC0 x₀ hx₀J]
        exact hnest' 0 p.1 (Nat.zero_le _) x₀ ((hKC _ _ _).mp hyk)
      · rw [hyk]
        exact hx₀b
      · intro m hm
        rw [hsame m p.1 hm.le x₀ y hyk]
        exact hx₀g m hm
      · rw [hyk, hx₀k]
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro p q hpq
    rw [Function.onFun, Set.disjoint_left]
    intro x hxp hxq
    simp only [hA, mem_ofPred_eq] at hxp hxq
    obtain ⟨-, hpb, hpg, hpk⟩ := hxp
    obtain ⟨-, hqb, hqg, hqk⟩ := hxq
    rcases lt_trichotomy p.1 q.1 with h | h | h
    · exact hqg p.1 h hpb
    · apply hpq
      refine Prod.ext h ?_
      rw [← hpk, ← hqk, h]
    · exact hpg q.1 h hqb
  have hAJ : ∀ p, A p ⊆ Ico a b := fun p x hx => by
    simp only [hA, mem_ofPred_eq] at hx
    exact hx.1
  -- the two (outer) measures compared on the cells
  obtain ⟨T₁, hT₁⟩ : ∃ T : Set ℝ, T = {t | u t < l / 2} := ⟨_, rfl⟩
  obtain ⟨T₂, hT₂⟩ : ∃ T : Set ℝ, T = {t | u t < l} := ⟨_, rfl⟩
  have hterm : ∀ p : ℕ × ℤ, MeasurableSet (A p) ∧
      volume.restrict T₁ (A p) ≤ ENNReal.ofReal (5 * η) * volume.restrict T₂ (A p) := by
    intro p
    by_cases hne : (A p).Nonempty
    · obtain ⟨x₀, hx₀⟩ := hne
      have hAp := hAcell p x₀ hx₀
      have hsubJ : C p.1 p.2 ⊆ Ico a b := hAp ▸ hAJ p
      simp only [hA, mem_ofPred_eq] at hx₀
      obtain ⟨hx₀J, hx₀b, hx₀g, hx₀k⟩ := hx₀
      have hmeas : MeasurableSet (A p) := by rw [hAp, hCeq]; exact measurableSet_Ico
      refine ⟨hmeas, ?_⟩
      obtain ⟨q, hq⟩ : ∃ q : ℝ, q = a + p.2 * s p.1 := ⟨_, rfl⟩
      have hQ : C p.1 p.2 = Ico q (q + s p.1) := by rw [hCeq, hq]
      have hsn := hs0 p.1
      obtain ⟨haq, hqb⟩ := s07_jn_ico_sub hsn (hQ ▸ hsubJ)
      -- the cell is stopping
      have hgood : (∫ t in q..q + s p.1, u t) < θ * s p.1 := by
        have h := hx₀b
        rw [hx₀k, hdv] at h
        simp only at h
        rw [← hq, div_lt_iff₀ hsn] at h
        exact h
      -- level 0 is not stopping (`u_I ≥ λ > θ`)
      have hn0 : p.1 ≠ 0 := by
        intro h0
        have hb0 := hx₀b
        rw [h0, hK0 x₀ hx₀J, hdv] at hb0
        simp only [Int.cast_zero, zero_mul, add_zero, hs00, eab] at hb0
        have : θ < l := by rw [hθ]; linarith
        linarith
      obtain ⟨m, hm⟩ : ∃ m, p.1 = m + 1 := Nat.exists_eq_succ_of_ne_zero hn0
      have hpar := hx₀g m (by omega)
      rw [not_lt, hdv] at hpar
      simp only at hpar
      obtain ⟨L, hL⟩ : ∃ L : ℝ, L = a + (K m x₀ : ℝ) * s m := ⟨_, rfl⟩
      rw [← hL, le_div_iff₀ (hs0 m)] at hpar
      have hsub : Ico q (q + s p.1) ⊆ Ico L (L + s m) := by
        rw [← hQ, hL, ← hCeq, ← hx₀k, hm]
        exact hnest m x₀
      obtain ⟨hLq, hqL⟩ := s07_jn_ico_sub hsn hsub
      have hparJ : Ico L (L + s m) ⊆ Ico a b := by
        rw [hL, ← hCeq, ← hC0 x₀ hx₀J]
        exact hnest' 0 m (Nat.zero_le _) x₀
      obtain ⟨haL, hLb⟩ := s07_jn_ico_sub (hs0 m) hparJ
      have hsm : s m = 2 * s p.1 := by rw [hm, hs1]; ring
      have hIP : θ * (2 * s p.1) ≤ ∫ t in L..L + s m, u t := by
        rw [← hsm]
        exact hpar
      -- parent oscillation ⇒ `∫_J u ≥ (1/2 - η) ∫_P u`
      obtain ⟨cP, hcP⟩ : ∃ cP : ℝ, cP = (∫ t in L..L + s m, u t) / (L + s m - L) := ⟨_, rfl⟩
      have hoscP := hosc L (L + s m) haL (by linarith [hs0 m]) hLb
      rw [← hcP] at hoscP
      have huP : IntervalIntegrable (fun t => |u t - cP|) volume L (L + s m) :=
        ((hii L (L + s m) haL (by linarith [hs0 m]) hLb).sub intervalIntegrable_const).abs
      have hJP : ∫ t in q..q + s p.1, |u t - cP| ≤ ∫ t in L..L + s m, |u t - cP| :=
        intervalIntegral.integral_mono_interval hLq (by linarith) hqL
          (Eventually.of_forall fun t => abs_nonneg _) huP
      have hiJ := hii q (q + s p.1) haq (by linarith) hqb
      have hdiff : |(∫ t in q..q + s p.1, u t) - cP * s p.1| ≤ ∫ t in q..q + s p.1, |u t - cP| := by
        have e : (∫ t in q..q + s p.1, u t) - cP * s p.1 = ∫ t in q..q + s p.1, (u t - cP) := by
          rw [intervalIntegral.integral_sub hiJ intervalIntegrable_const,
            intervalIntegral.integral_const, smul_eq_mul, show q + s p.1 - q = s p.1 by ring]
          ring
        rw [e]
        exact intervalIntegral.abs_integral_le_integral_abs (by linarith)
      have hcPs : cP * s p.1 = (∫ t in L..L + s m, u t) / 2 := by
        rw [hcP, show L + s m - L = s m by ring, hsm, div_mul_eq_mul_div,
          div_eq_div_iff (mul_pos two_pos hsn).ne' two_ne_zero]
        ring
      have hIJlow : (1 - 2 * η) * θ * s p.1 ≤ ∫ t in q..q + s p.1, u t := by
        have h2 : (∫ t in L..L + s m, u t) / 2 - η * ∫ t in L..L + s m, u t ≤
            ∫ t in q..q + s p.1, u t := by
          have h3 := (abs_le.mp (hdiff.trans (hJP.trans hoscP))).1
          rw [hcPs] at h3
          linarith
        have h4 : (1 / 2 - η) * (θ * (2 * s p.1)) ≤ (1 / 2 - η) * ∫ t in L..L + s m, u t :=
          mul_le_mul_of_nonneg_left hIP (by linarith)
        linarith
      -- the cell mean `u_J ∈ [(1 - 2η)θ, θ)`
      obtain ⟨uJ, huJ⟩ : ∃ uJ : ℝ, uJ = (∫ t in q..q + s p.1, u t) / (q + s p.1 - q) := ⟨_, rfl⟩
      have hqs : q + s p.1 - q = s p.1 := by ring
      have hIJ : ∫ t in q..q + s p.1, u t = uJ * s p.1 := by
        rw [huJ, hqs, div_mul_cancel₀ _ hsn.ne']
      have huJlo : (1 - 2 * η) * θ ≤ uJ := by
        have h := hIJlow
        rw [hIJ] at h
        exact le_of_mul_le_mul_right h hsn
      have huJhi : uJ < θ := by
        have h := hgood
        rw [hIJ] at h
        exact lt_of_mul_lt_mul_right h hsn.le
      rw [hθ] at huJlo huJhi
      have huJ0 : 0 < uJ := by nlinarith
      have hoscJ := hosc q (q + s p.1) haq (by linarith) hqb
      rw [← huJ, hIJ] at hoscJ
      have hosc' : ∫ t in q..q + s p.1, |u t - uJ| ≤ η * (uJ * (q + s p.1 - q)) := by
        rw [hqs]
        exact hoscJ
      have hiJ' := hsub_int q (q + s p.1) haq hqb
      have hc1 := s07c_fkps_m6_jn_cheb (by linarith : q < q + s p.1) huJ0
        (by norm_num : (0 : ℝ) < 1 / 4) hη0 hiJ' hosc'
      have hc2 := s07c_fkps_m6_jn_cheb (by linarith : q < q + s p.1) huJ0
        (by norm_num : (0 : ℝ) < 1 / 3) hη0 hiJ' hosc'
      rw [hqs] at hc1 hc2
      rw [Measure.restrict_apply hmeas, Measure.restrict_apply hmeas, hAp, hQ]
      have h1 : volume (Ico q (q + s p.1) ∩ T₁) ≤ ENNReal.ofReal (4 * η * s p.1) := by
        refine (measure_mono ?_).trans (hc1.trans_eq ?_)
        · intro t ht
          refine ⟨?_, ht.1⟩
          have h : u t < l / 2 := by
            have h' := ht.2
            rw [hT₁] at h'
            exact h'
          show 1 / 4 * uJ ≤ |u t - uJ|
          rw [abs_sub_comm]
          refine le_trans ?_ (le_abs_self _)
          nlinarith
        · congr 1
          ring
      have h2 : volume (Ico q (q + s p.1) \ T₂) ≤ ENNReal.ofReal (3 * η * s p.1) := by
        refine (measure_mono ?_).trans (hc2.trans_eq ?_)
        · intro t ht
          refine ⟨?_, ht.1⟩
          have h : ¬ u t < l := by
            have h' := ht.2
            rw [hT₂] at h'
            exact h'
          rw [not_lt] at h
          show 1 / 3 * uJ ≤ |u t - uJ|
          refine le_trans ?_ (le_abs_self _)
          linarith
        · congr 1
          ring
      have h3 : ENNReal.ofReal ((1 - 3 * η) * s p.1) ≤ volume (Ico q (q + s p.1) ∩ T₂) := by
        have hv : ENNReal.ofReal (s p.1) ≤
            volume (Ico q (q + s p.1) ∩ T₂) + ENNReal.ofReal (3 * η * s p.1) := by
          calc ENNReal.ofReal (s p.1) = volume (Ico q (q + s p.1)) := by rw [Real.volume_Ico, hqs]
            _ ≤ volume (Ico q (q + s p.1) ∩ T₂) + volume (Ico q (q + s p.1) \ T₂) := by
              refine (measure_mono ?_).trans (measure_union_le _ _)
              intro t ht
              by_cases htT : t ∈ T₂
              · exact Or.inl ⟨ht, htT⟩
              · exact Or.inr ⟨ht, htT⟩
            _ ≤ volume (Ico q (q + s p.1) ∩ T₂) + ENNReal.ofReal (3 * η * s p.1) := by gcongr
        have e : (1 - 3 * η) * s p.1 = s p.1 - 3 * η * s p.1 := by ring
        rw [e, ENNReal.ofReal_sub _ (mul_nonneg (mul_nonneg (by norm_num) hη0) hsn.le)]
        exact tsub_le_iff_right.mpr hv
      have hηs : 0 ≤ η * s p.1 := mul_nonneg hη0 hsn.le
      calc volume (Ico q (q + s p.1) ∩ T₁) ≤ ENNReal.ofReal (4 * η * s p.1) := h1
        _ ≤ ENNReal.ofReal (5 * η) * ENNReal.ofReal ((1 - 3 * η) * s p.1) := by
            rw [← ENNReal.ofReal_mul (by linarith)]
            apply ENNReal.ofReal_le_ofReal
            nlinarith [mul_nonneg hηs (by linarith : (0 : ℝ) ≤ 1 - 15 * η)]
        _ ≤ ENNReal.ofReal (5 * η) * volume (Ico q (q + s p.1) ∩ T₂) := mul_le_mul_right h3 _
    · rw [not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
  -- coverage: a.e. point of `T₁ ∩ [a, b)` lies in a stopping cell (Lebesgue points of `u 1_{[a,b]}`)
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = (Icc a b).indicator u := ⟨_, rfl⟩
  have hgi : Integrable g := hg ▸ hu.integrable_indicator measurableSet_Icc
  have hgu : ∀ t ∈ Icc a b, g t = u t := fun t ht => by
    rw [hg]
    exact indicator_of_mem ht u
  have hnull : volume ((T₁ ∩ Ico a b) \ ⋃ p, A p) = 0 := by
    have hLp := s07_jn_lebesgue (g := g) fun _ _ => hgi.integrableOn
    rw [ae_iff] at hLp
    refine measure_mono_null ?_ hLp
    intro x hx
    obtain ⟨⟨hxT, hxJ⟩, hxA⟩ := hx
    have hxu : u x < l / 2 := by
      rw [hT₁] at hxT
      exact hxT
    have hxI : x ∈ Icc a b := Ico_subset_Icc_self hxJ
    intro hP
    apply hxA
    obtain ⟨ρ, hρ, hρP⟩ := hP ((θ - g x) / 2) (by rw [hgu x hxI, hθ]; linarith)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((b - a) / ρ) one_lt_two
    have hsn : s n < ρ := by
      simp only [hs]
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hρ] at hn
      linarith
    have hbad : ∃ n, dv n (K n x) < θ := by
      refine ⟨n, ?_⟩
      have hcell : C n (K n x) ⊆ Ico a b := by
        rw [← hC0 x hxJ]
        exact hnest' 0 n (Nat.zero_le _) x
      rw [hCeq] at hcell
      obtain ⟨hc1, hc2⟩ := s07_jn_ico_sub (hs0 n) hcell
      have h := hρP (a + (K n x : ℝ) * s n) (s n) (hs0 n) hsn (by rw [← hCeq]; exact hmemC n x)
      have hint : ∫ t in (a + (K n x : ℝ) * s n)..(a + (K n x : ℝ) * s n + s n), g t =
          ∫ t in (a + (K n x : ℝ) * s n)..(a + (K n x : ℝ) * s n + s n), u t := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le (by linarith [hs0 n])] at ht
        exact hgu t ⟨hc1.trans ht.1, ht.2.trans hc2⟩
      rw [hint, hgu x hxI, abs_le] at h
      rw [hdv]
      simp only
      linarith [h.2]
    refine mem_iUnion.mpr ⟨(Nat.find hbad, K (Nat.find hbad) x), ?_⟩
    simp only [hA, mem_ofPred_eq]
    exact ⟨hxJ, Nat.find_spec hbad, fun m hm => Nat.find_min hbad hm, trivial⟩
  have hAm : ∀ p, MeasurableSet (A p) := fun p => (hterm p).1
  have hGm := MeasurableSet.iUnion hAm
  have key := s07_cz_sum hAm hdisj fun p => (hterm p).2
  have hIoc : Ioc a b =ᵐ[volume] Ico a b := Ico_ae_eq_Ioc.symm
  have e1 : volume ({t | u t < l / 2} ∩ Ioc a b) = volume (T₁ ∩ Ico a b) := by
    rw [hT₁]
    exact measure_congr (ae_eq_set_inter (ae_eq_refl _) hIoc)
  have e2 : volume ({t | u t < l} ∩ Ioc a b) = volume (T₂ ∩ Ico a b) := by
    rw [hT₂]
    exact measure_congr (ae_eq_set_inter (ae_eq_refl _) hIoc)
  have hE : volume ({t | u t < l / 2} ∩ Ioc a b) ≤
      ENNReal.ofReal (5 * η) * volume ({t | u t < l} ∩ Ioc a b) := by
    rw [e1, e2]
    calc volume (T₁ ∩ Ico a b)
        ≤ volume ((⋃ p, A p) ∩ T₁) + volume ((T₁ ∩ Ico a b) \ ⋃ p, A p) := by
          refine (measure_mono fun x hx => ?_).trans (measure_union_le _ _)
          by_cases hxA : x ∈ ⋃ p, A p
          · exact Or.inl ⟨hxA, hx.1⟩
          · exact Or.inr ⟨hx, hxA⟩
      _ = volume.restrict T₁ (⋃ p, A p) := by rw [hnull, add_zero, Measure.restrict_apply hGm]
      _ ≤ ENNReal.ofReal (5 * η) * volume.restrict T₂ (⋃ p, A p) := key
      _ ≤ ENNReal.ofReal (5 * η) * volume (T₂ ∩ Ico a b) := by
          rw [Measure.restrict_apply hGm]
          have hsu : (⋃ p, A p) ∩ T₂ ⊆ T₂ ∩ Ico a b := fun x hx => ⟨hx.2, iUnion_subset hAJ hx.1⟩
          exact mul_le_mul_right (measure_mono hsu) _
  have hfin : volume ({t | u t < l} ∩ Ioc a b) ≠ ⊤ :=
    ((measure_mono inter_subset_right).trans_lt measure_Ioc_lt_top).ne
  have h5 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hE
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at h5
  exact h5

/-- Helper for C3 (`s07c_fkps_m6_jn_lower` for measurable `u`, `C = 20`): iterating `s07c_fkps_m6_jn_step` from
`|{u < u_I/2} ∩ I| ≤ 2η|I|` gives `|{u < u_I/2^(k+1)} ∩ I| ≤ (5η)^k 2η|I|`; hence `u > 0` a.e. on `I`, and
`(log(u_I/u))₊ ≤ 2|u - u_I|/u_I + 2 log 2 · #{k : u < u_I/2^(k+1)}` integrates to `≤ 20η|I|`. -/
theorem s07c_fkps_m6_jn_lowm : ∃ η₂ : ℝ, 0 < η₂ ∧ ∀ (u : ℝ → ℝ) (a b η : ℝ), Measurable u → a < b → 0 ≤ η →
    η ≤ η₂ → IntegrableOn u (Icc a b) → (∀ t, 0 ≤ u t) → 0 < ∫ s in a..b, u s →
    (∀ c d : ℝ, a ≤ c → c < d → d ≤ b →
      ∫ t in c..d, |u t - (∫ s in c..d, u s) / (d - c)| ≤ η * ∫ t in c..d, u t) →
    (∀ᵐ t, t ∈ Icc a b → 0 < u t) ∧
    IntegrableOn (fun t => max (Real.log ((∫ s in a..b, u s) / (b - a) / u t)) 0) (Icc a b) ∧
    ∫ t in a..b, max (Real.log ((∫ s in a..b, u s) / (b - a) / u t)) 0 ≤ 20 * η * (b - a) := by
  obtain ⟨η₁, hη₁, hstep⟩ := s07c_fkps_m6_jn_step
  refine ⟨min η₁ (1 / 40), lt_min hη₁ (by norm_num), ?_⟩
  intro u a b η hum hab hη0 hη2 hu hu0 hpos hosc
  have hηa : η ≤ η₁ := hη2.trans (min_le_left _ _)
  have hηb : η ≤ 1 / 40 := hη2.trans (min_le_right _ _)
  have hba : 0 < b - a := by linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (∫ s in a..b, u s) / (b - a) := ⟨_, rfl⟩
  rw [← hc]
  have hc0 : 0 < c := hc ▸ div_pos hpos hba
  have hIc : ∫ t in a..b, u t = c * (b - a) := by rw [hc, div_mul_cancel₀ _ hba.ne']
  have hoscI : ∫ t in a..b, |u t - c| ≤ η * (c * (b - a)) := by
    have h := hosc a b le_rfl hab le_rfl
    rw [← hc, hIc] at h
    exact h
  have hIoc : Ioc a b =ᵐ[volume] Ico a b := Ico_ae_eq_Ioc.symm
  have hfinS : ∀ k : ℕ, volume ({t | u t < c / 2 ^ k} ∩ Ioc a b) ≠ ⊤ := fun k =>
    ((measure_mono inter_subset_right).trans_lt measure_Ioc_lt_top).ne
  -- base level (Chebyshev) and the CZ recursion
  have hbase : (volume ({t | u t < c / 2 ^ (0 + 1)} ∩ Ioc a b)).toReal ≤ 2 * η * (b - a) := by
    have hch := s07c_fkps_m6_jn_cheb hab hc0 (by norm_num : (0 : ℝ) < 1 / 2) hη0 hu hoscI
    have e : volume ({t | u t < c / 2 ^ (0 + 1)} ∩ Ioc a b) =
        volume ({t | u t < c / 2 ^ (0 + 1)} ∩ Ico a b) :=
      measure_congr (ae_eq_set_inter (ae_eq_refl _) hIoc)
    have h1 : volume ({t | u t < c / 2 ^ (0 + 1)} ∩ Ico a b) ≤ ENNReal.ofReal (2 * η * (b - a)) := by
      refine (measure_mono ?_).trans (hch.trans_eq ?_)
      · intro t ht
        refine ⟨?_, ht.2⟩
        have h : u t < c / 2 ^ (0 + 1) := ht.1
        rw [zero_add, pow_one] at h
        show 1 / 2 * c ≤ |u t - c|
        rw [abs_sub_comm]
        refine le_trans ?_ (le_abs_self _)
        linarith
      · congr 1
        ring
    rw [e]
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (mul_nonneg two_pos.le hη0) hba.le) h1
  have hrec : ∀ k : ℕ, (volume ({t | u t < c / 2 ^ (k + 1)} ∩ Ioc a b)).toReal ≤
      5 * η * (volume ({t | u t < c / 2 ^ k} ∩ Ioc a b)).toReal := by
    intro k
    have hlev : c / 2 ^ k ≤ (∫ s in a..b, u s) / (b - a) := by
      rw [← hc]
      exact div_le_self hc0.le (one_le_pow₀ one_le_two)
    have h := hstep u a b η (c / 2 ^ k) hab hη0 hηa hu hu0 (div_pos hc0 (by positivity)) hlev hosc
    rw [div_div, ← pow_succ] at h
    exact h
  have hgeo : ∀ k : ℕ, (volume ({t | u t < c / 2 ^ (k + 1)} ∩ Ioc a b)).toReal ≤
      (5 * η) ^ k * (2 * η * (b - a)) := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, one_mul]
      exact hbase
    | succ k ih =>
      calc (volume ({t | u t < c / 2 ^ (k + 1 + 1)} ∩ Ioc a b)).toReal
          ≤ 5 * η * (volume ({t | u t < c / 2 ^ (k + 1)} ∩ Ioc a b)).toReal := hrec (k + 1)
        _ ≤ 5 * η * ((5 * η) ^ k * (2 * η * (b - a))) := mul_le_mul_of_nonneg_left ih (by linarith)
        _ = (5 * η) ^ (k + 1) * (2 * η * (b - a)) := by ring
  -- `u > 0` a.e. on `I`
  have hZ : volume ({t | u t ≤ 0} ∩ Ioc a b) = 0 := by
    have hle : ∀ k : ℕ, (volume ({t | u t ≤ 0} ∩ Ioc a b)).toReal ≤ (5 * η) ^ k * (2 * η * (b - a)) := by
      intro k
      refine le_trans (ENNReal.toReal_mono (hfinS (k + 1)) (measure_mono ?_)) (hgeo k)
      intro t ht
      exact ⟨lt_of_le_of_lt ht.1 (div_pos hc0 (by positivity)), ht.2⟩
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : (0 : ℝ) ≤ 5 * η)
      (by linarith : 5 * η < 1)).mul_const (2 * η * (b - a))
    rw [zero_mul] at ht
    have h0 := ge_of_tendsto' ht hle
    have hfin : volume ({t | u t ≤ 0} ∩ Ioc a b) ≠ ⊤ :=
      ((measure_mono inter_subset_right).trans_lt measure_Ioc_lt_top).ne
    rcases (ENNReal.toReal_eq_zero_iff _).mp (le_antisymm h0 ENNReal.toReal_nonneg) with h | h
    · exact h
    · exact absurd h hfin
  have hpos_ae : ∀ᵐ t, t ∈ Icc a b → 0 < u t := by
    have hnull : volume ({t | u t ≤ 0} ∩ Ioc a b ∪ {a}) = 0 :=
      measure_union_null hZ (measure_singleton a)
    rw [ae_iff]
    refine measure_mono_null ?_ hnull
    intro t ht
    have ht' : ¬ (t ∈ Icc a b → 0 < u t) := ht
    rw [not_imp, not_lt] at ht'
    by_cases hta : t = a
    · exact Or.inr hta
    · exact Or.inl ⟨ht'.2, lt_of_le_of_ne ht'.1.1 (Ne.symm hta), ht'.1.2⟩
  -- pointwise layer bound
  have hL0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpt : ∀ t, ENNReal.ofReal (max (Real.log (c / u t)) 0) ≤ ENNReal.ofReal (2 * |u t - c| / c) +
      ENNReal.ofReal (2 * Real.log 2) *
        ∑' k : ℕ, Set.indicator {x | u x < c / 2 ^ (k + 1)} (1 : ℝ → ℝ≥0∞) t := by
    intro t
    rcases (hu0 t).lt_or_eq with hut | hut
    · by_cases hbig : c / 2 ≤ u t
      · refine le_trans ?_ le_self_add
        apply ENNReal.ofReal_le_ofReal
        refine max_le ?_ (div_nonneg (mul_nonneg two_pos.le (abs_nonneg _)) hc0.le)
        have h1 := Real.log_le_sub_one_of_pos (div_pos hc0 hut)
        have h2 : c / u t - 1 = (c - u t) / u t := by field_simp
        have h3 : (c - u t) / u t ≤ |u t - c| / u t :=
          div_le_div_of_nonneg_right (by rw [abs_sub_comm]; exact le_abs_self _) hut.le
        have h4 : |u t - c| / u t ≤ |u t - c| / (c / 2) :=
          div_le_div_of_nonneg_left (abs_nonneg _) (half_pos hc0) hbig
        have h5 : |u t - c| / (c / 2) = 2 * |u t - c| / c := by field_simp
        linarith
      · rw [not_le] at hbig
        refine le_trans ?_ le_add_self
        classical
        have hP : ∃ n : ℕ, c / 2 ^ (n + 1) ≤ u t := by
          obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (c / u t) one_lt_two
          refine ⟨n, ?_⟩
          rw [div_lt_iff₀ hut] at hn
          rw [div_le_iff₀ (by positivity)]
          have h2 : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := pow_le_pow_right₀ one_le_two (Nat.le_succ n)
          nlinarith
        obtain ⟨N, hN⟩ : ∃ N, N = Nat.find hP := ⟨_, rfl⟩
        have hNspec : c / 2 ^ (N + 1) ≤ u t := by
          rw [hN]
          exact Nat.find_spec hP
        have hNmin : ∀ k < N, u t < c / 2 ^ (k + 1) := fun k hk => by
          rw [hN] at hk
          exact not_le.mp (Nat.find_min hP hk)
        have hN1 : 1 ≤ N := by
          rcases Nat.eq_zero_or_pos N with h0 | h0
          · rw [h0, zero_add, pow_one] at hNspec
            linarith
          · exact h0
        have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
        have e : Real.log ((2 : ℝ) ^ (N + 1)) = ((N : ℝ) + 1) * Real.log 2 := by
          rw [Real.log_pow]
          push_cast
          ring
        have hlog : Real.log (c / u t) ≤ ((N : ℝ) + 1) * Real.log 2 := by
          rw [← e]
          refine Real.log_le_log (div_pos hc0 hut) ?_
          rw [div_le_iff₀ hut]
          rw [div_le_iff₀ (by positivity)] at hNspec
          linarith
        have hf : max (Real.log (c / u t)) 0 ≤ 2 * Real.log 2 * N := by
          refine max_le ?_ (mul_nonneg (mul_nonneg two_pos.le hL0.le) (Nat.cast_nonneg N))
          nlinarith
        calc ENNReal.ofReal (max (Real.log (c / u t)) 0) ≤ ENNReal.ofReal (2 * Real.log 2 * N) :=
              ENNReal.ofReal_le_ofReal hf
          _ = ENNReal.ofReal (2 * Real.log 2) * (N : ℝ≥0∞) := by
              rw [ENNReal.ofReal_mul (mul_nonneg two_pos.le hL0.le), ENNReal.ofReal_natCast]
          _ ≤ ENNReal.ofReal (2 * Real.log 2) *
                ∑' k : ℕ, Set.indicator {x | u x < c / 2 ^ (k + 1)} (1 : ℝ → ℝ≥0∞) t := by
              refine mul_le_mul_right ?_ _
              calc (N : ℝ≥0∞) = ∑ k ∈ Finset.range N, (1 : ℝ≥0∞) := by simp
                _ ≤ ∑ k ∈ Finset.range N, Set.indicator {x | u x < c / 2 ^ (k + 1)} (1 : ℝ → ℝ≥0∞) t := by
                    refine Finset.sum_le_sum fun k hk => ?_
                    rw [indicator_of_mem (hNmin k (Finset.mem_range.mp hk))]
                    exact le_rfl
                _ ≤ _ := sum_le_tsum _
    · rw [← hut, div_zero, Real.log_zero, max_self, ENNReal.ofReal_zero]
      exact zero_le
  -- integrate the layer bound over `(a, b]`
  have hm1 : Measurable fun t => ENNReal.ofReal (2 * |u t - c| / c) :=
    (((hum.sub measurable_const).abs.const_mul 2).div_const c).ennreal_ofReal
  have hm2 : ∀ k : ℕ, Measurable (Set.indicator {x | u x < c / 2 ^ (k + 1)} (1 : ℝ → ℝ≥0∞)) :=
    fun k => measurable_one.indicator (measurableSet_lt hum measurable_const)
  have hint1 : IntegrableOn (fun t => 2 * |u t - c| / c) (Ioc a b) := by
    have h : IntegrableOn (fun t => 2 * |u t - c| / c) (Icc a b) :=
      (((hu.sub (continuous_const (y := c)).integrableOn_Icc).abs).const_mul 2).div_const c
    exact h.mono_set Ioc_subset_Icc_self
  have hI1 : ∫⁻ t in Ioc a b, ENNReal.ofReal (2 * |u t - c| / c) ≤ ENNReal.ofReal (2 * η * (b - a)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint1 (Eventually.of_forall fun t =>
      div_nonneg (mul_nonneg two_pos.le (abs_nonneg _)) hc0.le)]
    apply ENNReal.ofReal_le_ofReal
    rw [← intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul, div_le_iff₀ hc0]
    linarith
  have hI2 : ∀ k : ℕ, ∫⁻ t in Ioc a b, Set.indicator {x | u x < c / 2 ^ (k + 1)} (1 : ℝ → ℝ≥0∞) t ≤
      ENNReal.ofReal ((5 * η) ^ k * (2 * η * (b - a))) := by
    intro k
    rw [lintegral_indicator_one (measurableSet_lt hum measurable_const),
      Measure.restrict_apply (measurableSet_lt hum measurable_const),
      ← ENNReal.ofReal_toReal (hfinS (k + 1))]
    exact ENNReal.ofReal_le_ofReal (hgeo k)
  have h5 : 5 * η < 1 := by linarith
  have h50 : (0 : ℝ) ≤ 5 * η := by linarith
  have hB : 0 ≤ 2 * η * (b - a) := mul_nonneg (mul_nonneg two_pos.le hη0) hba.le
  have hnn : ∀ k : ℕ, 0 ≤ (5 * η) ^ k * (2 * η * (b - a)) := fun k => mul_nonneg (pow_nonneg h50 k) hB
  have hsum : Summable fun k : ℕ => (5 * η) ^ k * (2 * η * (b - a)) :=
    (summable_geometric_of_lt_one h50 h5).mul_right _
  have hL1 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2)]
  obtain ⟨ι, hι⟩ : ∃ ι : ℝ, ι = (1 - 5 * η)⁻¹ := ⟨_, rfl⟩
  have hι0 : 0 < ι := hι ▸ inv_pos.mpr (by linarith)
  have hι1 : ι * (1 - 5 * η) = 1 := by
    rw [hι]
    exact inv_mul_cancel₀ (by linarith)
  have hι2 : ι ≤ 2 := by nlinarith
  have hLι : Real.log 2 * ι ≤ 2 := by nlinarith
  have hlin : ∫⁻ t in Ioc a b, ENNReal.ofReal (max (Real.log (c / u t)) 0) ≤
      ENNReal.ofReal (20 * η * (b - a)) := by
    calc ∫⁻ t in Ioc a b, ENNReal.ofReal (max (Real.log (c / u t)) 0)
        ≤ ∫⁻ t in Ioc a b, (ENNReal.ofReal (2 * |u t - c| / c) + ENNReal.ofReal (2 * Real.log 2) *
            ∑' k : ℕ, Set.indicator {x | u x < c / 2 ^ (k + 1)} (1 : ℝ → ℝ≥0∞) t) :=
          lintegral_mono fun t => hpt t
      _ = (∫⁻ t in Ioc a b, ENNReal.ofReal (2 * |u t - c| / c)) + ENNReal.ofReal (2 * Real.log 2) *
            ∑' k : ℕ, ∫⁻ t in Ioc a b, Set.indicator {x | u x < c / 2 ^ (k + 1)} (1 : ℝ → ℝ≥0∞) t := by
          rw [lintegral_add_left hm1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_tsum fun k => (hm2 k).aemeasurable]
      _ ≤ ENNReal.ofReal (2 * η * (b - a)) + ENNReal.ofReal (2 * Real.log 2) *
            ∑' k : ℕ, ENNReal.ofReal ((5 * η) ^ k * (2 * η * (b - a))) :=
          add_le_add hI1 (mul_le_mul_right (tsum_le_tsum hI2) _)
      _ = ENNReal.ofReal (2 * η * (b - a) + 2 * Real.log 2 * (ι * (2 * η * (b - a)))) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum, tsum_mul_right, tsum_geometric_of_lt_one h50 h5,
            ← hι, ← ENNReal.ofReal_mul (mul_nonneg two_pos.le hL0.le),
            ← ENNReal.ofReal_add hB (mul_nonneg (mul_nonneg two_pos.le hL0.le) (mul_nonneg hι0.le hB))]
      _ ≤ ENNReal.ofReal (20 * η * (b - a)) := by
          apply ENNReal.ofReal_le_ofReal
          have hB' : 0 ≤ η * (b - a) := mul_nonneg hη0 hba.le
          have h6 := mul_le_mul_of_nonneg_right hLι hB'
          linarith
  -- integrability and the integral
  have hFm : Measurable fun t => max (Real.log (c / u t)) 0 :=
    (Real.measurable_log.comp (measurable_const.div hum)).max measurable_const
  have hlt : ∫⁻ t in Ioc a b, ENNReal.ofReal (max (Real.log (c / u t)) 0) < ⊤ :=
    hlin.trans_lt ENNReal.ofReal_lt_top
  have hiIoc : IntegrableOn (fun t => max (Real.log (c / u t)) 0) (Ioc a b) :=
    ⟨hFm.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun t => le_max_right _ _)).mpr hlt⟩
  refine ⟨hpos_ae, (integrableOn_Icc_iff_integrableOn_Ioc).mpr hiIoc, ?_⟩
  have e := integral_eq_lintegral_of_nonneg_ae (μ := volume.restrict (Ioc a b))
    (f := fun t => max (Real.log (c / u t)) 0) (Eventually.of_forall fun t => le_max_right _ _)
    hFm.aestronglyMeasurable
  rw [intervalIntegral.integral_of_le hab.le, e]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (mul_nonneg (by norm_num) hη0) hba.le) hlin

/-- C3.4 (lower tail): iterating C3.3 from `|{u < u_I/2} ∩ I| ≤ 2η|I|` (Chebyshev) gives `u > 0` a.e. on `I` and
`∫_I (log(u_I/u))₊ ≤ Cη|I|` (on `{u_I/2 ≤ u < u_I}`: `log(u_I/u) ≤ 2(1 - u/u_I)`; dyadic layers below). -/
theorem s07c_fkps_m6_jn_lower : ∃ η₂ C : ℝ, 0 < η₂ ∧ 0 < C ∧
    ∀ (u : ℝ → ℝ) (a b η : ℝ), a < b → 0 ≤ η → η ≤ η₂ →
    IntegrableOn u (Icc a b) → (∀ t, 0 ≤ u t) → 0 < ∫ s in a..b, u s →
    (∀ c d : ℝ, a ≤ c → c < d → d ≤ b →
      ∫ t in c..d, |u t - (∫ s in c..d, u s) / (d - c)| ≤ η * ∫ t in c..d, u t) →
    (∀ᵐ t, t ∈ Icc a b → 0 < u t) ∧
    IntegrableOn (fun t => max (Real.log ((∫ s in a..b, u s) / (b - a) / u t)) 0) (Icc a b) ∧
    ∫ t in a..b, max (Real.log ((∫ s in a..b, u s) / (b - a) / u t)) 0 ≤ C * η * (b - a) := by
  -- `C = 20`: pass to a measurable nonnegative representative `w` of `u` on `[a, b]`
  -- (`s07c_fkps_m6_jn_mod`) and apply `s07c_fkps_m6_jn_lowm`
  obtain ⟨η₂, hη₂, hlow⟩ := s07c_fkps_m6_jn_lowm
  refine ⟨η₂, 20, hη₂, by norm_num, ?_⟩
  intro u a b η hab hη0 hη2 hu hu0 hpos hosc
  obtain ⟨w, hwm, hw0, huw⟩ := s07c_fkps_m6_jn_mod hu hu0
  have hcg : ∀ (φ : ℝ → ℝ) (c d : ℝ), a ≤ c → c ≤ d → d ≤ b →
      ∫ t in c..d, φ (u t) = ∫ t in c..d, φ (w t) := by
    intro φ c d hac hcd hdb
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [huw] with t ht htI
    rw [uIoc_of_le hcd] at htI
    rw [ht ⟨hac.trans htI.1.le, htI.2.trans hdb⟩]
  have hiu : ∀ c d : ℝ, a ≤ c → c ≤ d → d ≤ b → ∫ t in c..d, u t = ∫ t in c..d, w t :=
    fun c d h1 h2 h3 => hcg (fun x => x) c d h1 h2 h3
  have hoscw : ∀ c d : ℝ, a ≤ c → c < d → d ≤ b →
      ∫ t in c..d, |w t - (∫ s in c..d, w s) / (d - c)| ≤ η * ∫ t in c..d, w t := by
    intro c d h1 h2 h3
    have e1 := hiu c d h1 h2.le h3
    have e2 : ∫ t in c..d, |u t - (∫ s in c..d, u s) / (d - c)| =
        ∫ t in c..d, |w t - (∫ s in c..d, w s) / (d - c)| := by
      rw [e1]
      exact hcg (fun x => |x - (∫ s in c..d, w s) / (d - c)|) c d h1 h2.le h3
    rw [← e2, ← e1]
    exact hosc c d h1 h2 h3
  have hposw : 0 < ∫ s in a..b, w s := by
    rw [← hiu a b le_rfl hab.le le_rfl]
    exact hpos
  have hwi : IntegrableOn w (Icc a b) := hu.congr_fun_ae ((ae_restrict_iff' measurableSet_Icc).mpr huw)
  obtain ⟨h1, h2, h3⟩ := hlow w a b η hwm hab hη0 hη2 hwi hw0 hposw hoscw
  rw [hiu a b le_rfl hab.le le_rfl]
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [h1, huw] with t h1t hut htI
    rw [hut htI]
    exact h1t htI
  · refine h2.congr_fun_ae ((ae_restrict_iff' measurableSet_Icc).mpr ?_)
    filter_upwards [huw] with t ht htI
    rw [ht htI]
  · have e3 : ∫ t in a..b, max (Real.log ((∫ s in a..b, w s) / (b - a) / u t)) 0 =
        ∫ t in a..b, max (Real.log ((∫ s in a..b, w s) / (b - a) / w t)) 0 :=
      hcg (fun x => max (Real.log ((∫ s in a..b, w s) / (b - a) / x)) 0) a b le_rfl hab.le le_rfl
    rw [e3]
    exact h3

/-! ### Block C outputs (frozen statements), proved from the internal stubs -/

/-- M6.C (per-arc small A∞, the R-trick): on every arc of length `≤ 2π` the density `u` of `H` satisfies
`⨍_I |u - u_I| ≤ C ε^{1/8} u_I`. Arcs with `ℓ ≥ ℓ₀ ε^{1/3}`: block A at `z = 0`. Shorter arcs: block B at
`z = (1 - R ℓ) e^{i s₀}`, `R = ε^{-1/3}`, then block A for `G`; the Möbius factors oscillate `O(1/R)` on `I`, the
defect contributes `O(√(R ε))`, and the image arc stays off the expanding point of `φ_{F z}` because
`|H(I') - |I'|| = o(1)` globally. -/
theorem s07c_fkps_m6_ainf : ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧
    ∀ (F : ℂ → ℂ) (a : ℂ → ℝ) (K ε : ℝ) (H u : ℝ → ℝ),
    IsKQC F univ K → F '' univ = univ → F '' unitDisc = unitDisc → F 0 = 0 →
    Measurable a → (∀ z, 0 ≤ a z) → (∀ z ∈ unitDisc, a z ≤ ε₀) →
    (∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) →
      ‖LiZhongQC.complexDilatation F w‖ ≤ a z) →
    0 ≤ ε → ε ≤ ε₀ →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
        ≤ ENNReal.ofReal (ε * r)) →
    StrictMono H → Continuous H → (∀ θ : ℝ, H (θ + 2 * π) = H θ + 2 * π) →
    (∀ θ : ℝ, F (Complex.exp (θ * Complex.I)) = Complex.exp (H θ * Complex.I)) →
    (∀ a b : ℝ, IntegrableOn u (Icc a b)) → (∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t) →
    ∀ a b : ℝ, a < b → b - a ≤ 2 * π →
      ∫ t in a..b, |u t - (∫ s in a..b, u s) / (b - a)| ≤ C * ε ^ (1 / 8 : ℝ) * ∫ t in a..b, u t := by
  obtain ⟨εG, CG, hεG, hCG, hG⟩ := s07c_fkps_m6_global
  obtain ⟨εS, ℓ₀, CS, hεS, hℓ₀, hCS, hS⟩ := s07c_fkps_m6_short
  set D : ℝ := 2 * CG / Real.sqrt ℓ₀ + 2 * CG with hD
  have hsℓ₀ : 0 < Real.sqrt ℓ₀ := Real.sqrt_pos.mpr hℓ₀
  have hDp : 0 < D := by positivity
  set ε₀ : ℝ := min (min εG εS) (min 1 ((1 / (2 * D)) ^ 8)) with hε₀
  have hε₀p : 0 < ε₀ := lt_min (lt_min hεG hεS) (lt_min one_pos (by positivity))
  refine ⟨ε₀, 4 * D + CS, hε₀p, by positivity, ?_⟩
  intro F a K ε H u hF hFs hFD hF0 ha ha0 hale hW hε hεε₀ hC hHm hHc hHp hHF hui hrep x y hxy hy
  have hε₀G : ε₀ ≤ εG := (min_le_left _ _).trans (min_le_left _ _)
  have hε₀S : ε₀ ≤ εS := (min_le_left _ _).trans (min_le_right _ _)
  have hε1 : ε ≤ 1 := hεε₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεD : ε ≤ (1 / (2 * D)) ^ 8 := hεε₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨u', ρ, hui', hrep', hu0', hρ0, -, hρL, hρδ, hA⟩ := hG F a K ε H hF hFs hFD hF0 ha ha0
    (fun z hz => (hale z hz).trans hε₀G) hW hε (hεε₀.trans hε₀G) hC hHm hHc hHp hHF
  have hae : u =ᵐ[volume] u' := s07c_fkps_m6_dens_ae hui hui' hrep hrep'
  have e1 : ∫ s in x..y, u s = ∫ s in x..y, u' s :=
    intervalIntegral.integral_congr_ae (hae.mono fun t ht _ => ht)
  have e2 : ∫ t in x..y, |u t - (∫ s in x..y, u s) / (y - x)| =
      ∫ t in x..y, |u' t - (∫ s in x..y, u' s) / (y - x)| := by
    rw [e1]
    exact intervalIntegral.integral_congr_ae (hae.mono fun t ht _ => by rw [ht])
  rw [e2, e1]
  have h8 : 0 ≤ ε ^ (1 / 8 : ℝ) := Real.rpow_nonneg hε _
  have hrt6 : ε ^ (1 / 6 : ℝ) ≤ ε ^ (1 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge' hε hε1 (by norm_num) (by norm_num)
  have hrt3 : ε ^ (1 / 3 : ℝ) ≤ ε ^ (1 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge' hε hε1 (by norm_num) (by norm_num)
  have hD8 : D * ε ^ (1 / 8 : ℝ) ≤ 1 / 2 := by
    have h1 : ε ^ (1 / 8 : ℝ) ≤ ((1 / (2 * D)) ^ 8) ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow hε hεD (by norm_num)
    have h2 : ((1 / (2 * D)) ^ 8) ^ (1 / 8 : ℝ) = 1 / (2 * D) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [h2] at h1
    calc D * ε ^ (1 / 8 : ℝ) ≤ D * (1 / (2 * D)) := mul_le_mul_of_nonneg_left h1 hDp.le
      _ = 1 / 2 := by field_simp
  have hint' : 0 ≤ ∫ t in x..y, u' t := intervalIntegral.integral_nonneg hxy.le (fun t _ => hu0' t)
  by_cases hshort : y - x ≤ ℓ₀ * ε ^ (1 / 3 : ℝ)
  · -- short arcs: the R-trick
    refine (hS F a K ε H u' hF hFs hFD hF0 ha ha0 (fun z hz => (hale z hz).trans hε₀S) hW hε
      (hεε₀.trans hε₀S) hC hHm hHc hHp hHF hui' hrep' x y hxy hshort).trans ?_
    have : CS * ε ^ (1 / 3 : ℝ) ≤ (4 * D + CS) * ε ^ (1 / 8 : ℝ) := by
      have := mul_le_mul_of_nonneg_left hrt3 hCS.le
      nlinarith
    exact mul_le_mul_of_nonneg_right this hint'
  · -- long arcs: block A at the origin
    rw [not_le] at hshort
    have hδ : CG * ε ^ (1 / 6 : ℝ) ≤ 1 / 2 := by
      have h1 : CG * ε ^ (1 / 6 : ℝ) ≤ CG * ε ^ (1 / 8 : ℝ) := mul_le_mul_of_nonneg_left hrt6 hCG.le
      have h2 : CG * ε ^ (1 / 8 : ℝ) ≤ D * ε ^ (1 / 8 : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ h8
        have : 0 ≤ 2 * CG / Real.sqrt ℓ₀ := by positivity
        linarith
      linarith
    have hdev := s07c_fkps_m6_dev (T := H) (u := u') (ρ := ρ) (C := CG) (ε := ε)
      hxy.le (by linarith) (hui' x y) hu0' hHc hρ0 hρL hρδ hδ hA
    -- `√ε √|I| ≤ ε^{1/3} |I| / √ℓ₀` on long arcs
    have hs1 : Real.sqrt ε = ε ^ (1 / 3 : ℝ) * Real.sqrt (ε ^ (1 / 3 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hε,
        ← Real.rpow_add' hε (by norm_num)]
      norm_num
    have hs2 : Real.sqrt (ε ^ (1 / 3 : ℝ)) * Real.sqrt ℓ₀ ≤ Real.sqrt (y - x) := by
      rw [← Real.sqrt_mul (Real.rpow_nonneg hε _)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hsl : 0 ≤ Real.sqrt (y - x) := Real.sqrt_nonneg _
    have h3 : 0 ≤ ε ^ (1 / 3 : ℝ) := Real.rpow_nonneg hε _
    have key : Real.sqrt ε * Real.sqrt (y - x) * Real.sqrt ℓ₀ ≤ ε ^ (1 / 3 : ℝ) * (y - x) := by
      rw [hs1]
      calc ε ^ (1 / 3 : ℝ) * Real.sqrt (ε ^ (1 / 3 : ℝ)) * Real.sqrt (y - x) * Real.sqrt ℓ₀
          = ε ^ (1 / 3 : ℝ) * (Real.sqrt (ε ^ (1 / 3 : ℝ)) * Real.sqrt ℓ₀) * Real.sqrt (y - x) := by
            ring
        _ ≤ ε ^ (1 / 3 : ℝ) * Real.sqrt (y - x) * Real.sqrt (y - x) := by gcongr
        _ = ε ^ (1 / 3 : ℝ) * (y - x) := by
            rw [mul_assoc, Real.mul_self_sqrt (by linarith)]
    have key' : Real.sqrt ε * Real.sqrt (y - x) ≤ ε ^ (1 / 8 : ℝ) * (y - x) / Real.sqrt ℓ₀ := by
      rw [le_div_iff₀ hsℓ₀]
      exact key.trans (mul_le_mul_of_nonneg_right hrt3 (by linarith))
    have hlong : ∫ t in x..y, |u' t - 1| ≤ D * ε ^ (1 / 8 : ℝ) * 1 * (y - x) := by
      refine hdev.trans ?_
      have h4 : 2 * (CG * Real.sqrt ε * Real.sqrt (y - x)) ≤
          2 * CG / Real.sqrt ℓ₀ * ε ^ (1 / 8 : ℝ) * (y - x) := by
        have := mul_le_mul_of_nonneg_left key' (by positivity : (0 : ℝ) ≤ 2 * CG)
        calc 2 * (CG * Real.sqrt ε * Real.sqrt (y - x))
            = 2 * CG * (Real.sqrt ε * Real.sqrt (y - x)) := by ring
          _ ≤ 2 * CG * (ε ^ (1 / 8 : ℝ) * (y - x) / Real.sqrt ℓ₀) := this
          _ = 2 * CG / Real.sqrt ℓ₀ * ε ^ (1 / 8 : ℝ) * (y - x) := by ring
      have h5 : 2 * (CG * ε ^ (1 / 6 : ℝ)) * (y - x) ≤ 2 * CG * ε ^ (1 / 8 : ℝ) * (y - x) := by
        have := mul_le_mul_of_nonneg_left hrt6 hCG.le
        nlinarith
      rw [hD]
      nlinarith
    have hred := s07c_fkps_m6_reduce hxy (hui' x y) hu0' one_pos hD8 hlong
    refine hred.trans (mul_le_mul_of_nonneg_right ?_ hint')
    nlinarith

/-- M6.C (small A∞ ⇒ small BMO, John–Nirenberg / Calderón–Zygmund type): if `u ≥ 0` has positive mass on every
interval and `⨍_J |u - u_J| ≤ η u_J` on every interval of length `≤ 2π`, `η ≤ η₀`, then `u > 0` a.e., `log u` is
locally integrable and its mean oscillation on such intervals is `≤ C η`. Upper tail: `log x ≤ x - 1`. Lower tail:
maximal dyadic subintervals of `{u < 2^{-k} u_I}` give `|E_{k+1}| ≤ 5η |E_k|`. -/
theorem s07c_fkps_m6_jn : ∃ η₀ C : ℝ, 0 < η₀ ∧ 0 < C ∧ ∀ (u : ℝ → ℝ) (η : ℝ), 0 ≤ η → η ≤ η₀ →
    (∀ a b : ℝ, IntegrableOn u (Icc a b)) → (∀ t : ℝ, 0 ≤ u t) →
    (∀ a b : ℝ, a < b → 0 < ∫ t in a..b, u t) →
    (∀ a b : ℝ, a < b → b - a ≤ 2 * π →
      ∫ t in a..b, |u t - (∫ s in a..b, u s) / (b - a)| ≤ η * ∫ t in a..b, u t) →
    (∀ᵐ t, 0 < u t) ∧ (∀ a b : ℝ, IntegrableOn (fun t => Real.log (u t)) (Icc a b)) ∧
    ∀ a b : ℝ, a < b → b - a ≤ 2 * π →
      (∫ t in a..b, |Real.log (u t) - (∫ s in a..b, Real.log (u s)) / (b - a)|) / (b - a) ≤ C * η := by
  obtain ⟨η₂, CL, hη₂, hCL, hL⟩ := s07c_fkps_m6_jn_lower
  refine ⟨η₂, 2 * (1 + CL), hη₂, by positivity, ?_⟩
  intro u η hη hηη₂ hui hu0 hpos hA
  have hsub : ∀ a b : ℝ, b - a ≤ 2 * π → ∀ c d : ℝ, a ≤ c → c < d → d ≤ b →
      ∫ t in c..d, |u t - (∫ s in c..d, u s) / (d - c)| ≤ η * ∫ t in c..d, u t :=
    fun a b hb c d hac hcd hdb => hA c d hcd (by linarith)
  have hlow := fun (a b : ℝ) (hab : a < b) (hb : b - a ≤ 2 * π) =>
    hL u a b η hab hη hηη₂ (hui a b) hu0 (hpos a b hab) (hsub a b hb)
  have h2π : (0 : ℝ) < 2 * π := Real.two_pi_pos
  -- (i) `u > 0` a.e.
  have hae : ∀ᵐ t, 0 < u t := by
    have h : ∀ n : ℤ, ∀ᵐ t, t ∈ Icc (2 * π * n) (2 * π * n + 2 * π) → 0 < u t := fun n =>
      (hlow _ _ (by linarith) (by linarith)).1
    rw [← ae_all_iff] at h
    filter_upwards [h] with t ht
    apply ht ⌊t / (2 * π)⌋
    have h1 := Int.floor_le (t / (2 * π))
    have h2 := Int.lt_floor_add_one (t / (2 * π))
    have e : t = 2 * π * (t / (2 * π)) := by field_simp
    constructor <;> nlinarith
  -- pointwise splitting of `log u` around `log c`
  have hsplit : ∀ c : ℝ, 0 < c → ∀ t : ℝ, 0 < u t →
      |Real.log (u t) - Real.log c| ≤
        max (Real.log (u t / c)) 0 + max (Real.log (c / u t)) 0 := by
    intro c hc t ht
    rw [Real.log_div ht.ne' hc.ne', Real.log_div hc.ne' ht.ne']
    rcases le_total 0 (Real.log (u t) - Real.log c) with h | h
    · rw [abs_of_nonneg h]
      have := le_max_left (Real.log (u t) - Real.log c) 0
      have := le_max_right (Real.log c - Real.log (u t)) 0
      linarith
    · rw [abs_of_nonpos h]
      have := le_max_right (Real.log (u t) - Real.log c) 0
      have := le_max_left (Real.log c - Real.log (u t)) 0
      linarith
  have hmeas : ∀ a b : ℝ, AEStronglyMeasurable (fun t => Real.log (u t)) (volume.restrict (Icc a b)) :=
    fun a b => (Real.measurable_log.comp_aemeasurable (hui a b).aemeasurable).aestronglyMeasurable
  -- (ii) on intervals of length `≤ 2π`
  have hloc : ∀ a b : ℝ, a < b → b - a ≤ 2 * π →
      IntegrableOn (fun t => Real.log (u t)) (Icc a b) := by
    intro a b hab hb
    have hc : 0 < (∫ s in a..b, u s) / (b - a) := div_pos (hpos a b hab) (by linarith)
    obtain ⟨-, hlI, -⟩ := hlow a b hab hb
    obtain ⟨huI, -⟩ := s07c_fkps_m6_jn_upper hab (hui a b) hu0 (hpos a b hab) (hA a b hab hb)
    refine Integrable.mono' ((huI.add hlI).add (continuous_const (y := |Real.log
      ((∫ s in a..b, u s) / (b - a))|)).integrableOn_Icc) (hmeas a b) ?_
    refine Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs]
    rcases (hu0 t).lt_or_eq with ht | ht
    · have := hsplit _ hc t ht
      have := abs_sub_abs_le_abs_sub (Real.log (u t)) (Real.log ((∫ s in a..b, u s) / (b - a)))
      simp only [Pi.add_apply]
      linarith
    · rw [← ht, Real.log_zero, abs_zero]
      exact add_nonneg (add_nonneg (le_max_right _ _) (le_max_right _ _)) (abs_nonneg _)
  have hint : ∀ a b : ℝ, IntegrableOn (fun t => Real.log (u t)) (Icc a b) := by
    have hstep : ∀ x : ℝ, ∀ n : ℕ, IntegrableOn (fun t => Real.log (u t)) (Icc x (x + 2 * π * n)) := by
      intro x n
      induction n with
      | zero => simp
      | succ n ih =>
        have h1 := hloc (x + 2 * π * n) (x + 2 * π * n + 2 * π) (by linarith) (by linarith)
        have h2 := ih.union h1
        rwa [Icc_union_Icc_eq_Icc (by nlinarith [Real.pi_pos, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
          (by linarith), show x + 2 * π * n + 2 * π = x + 2 * π * ((n + 1 : ℕ) : ℝ) by push_cast; ring]
          at h2
    intro a b
    obtain ⟨n, hn⟩ := exists_nat_ge ((b - a) / (2 * π))
    refine (hstep a n).mono_set (Icc_subset_Icc le_rfl ?_)
    have := (div_le_iff₀ h2π).mp hn
    linarith
  refine ⟨hae, hint, fun a b hab hb => ?_⟩
  -- (iii) mean oscillation
  have hba : 0 < b - a := by linarith
  obtain ⟨-, hlI, hlB⟩ := hlow a b hab hb
  obtain ⟨huI, huB⟩ := s07c_fkps_m6_jn_upper hab (hui a b) hu0 (hpos a b hab) (hA a b hab hb)
  have hc : 0 < (∫ s in a..b, u s) / (b - a) := div_pos (hpos a b hab) hba
  have hII : IntervalIntegrable (fun t => Real.log (u t)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr (hint a b)
  refine (s07_ssv_osc_const hab hII (Real.log ((∫ s in a..b, u s) / (b - a)))).trans ?_
  have hmono : ∫ t in a..b, |Real.log (u t) - Real.log ((∫ s in a..b, u s) / (b - a))| ≤
      ∫ t in a..b, (max (Real.log (u t / ((∫ s in a..b, u s) / (b - a)))) 0 +
        max (Real.log ((∫ s in a..b, u s) / (b - a) / u t)) 0) := by
    refine intervalIntegral.integral_mono_ae hab.le ?_
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr (huI.add hlI)) ?_
    · exact (hII.sub intervalIntegrable_const).abs
    · filter_upwards [hae] with t ht
      exact hsplit _ hc t ht
  have hsum : ∫ t in a..b, (max (Real.log (u t / ((∫ s in a..b, u s) / (b - a)))) 0 +
        max (Real.log ((∫ s in a..b, u s) / (b - a) / u t)) 0) ≤
      η * (b - a) + CL * η * (b - a) := by
    rw [intervalIntegral.integral_add ((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr huI)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hlI)]
    linarith
  have hfin : (∫ t in a..b, |Real.log (u t) - Real.log ((∫ s in a..b, u s) / (b - a))|) / (b - a) ≤
      (1 + CL) * η := by
    rw [div_le_iff₀ hba]
    have : (1 + CL) * η * (b - a) = η * (b - a) + CL * η * (b - a) := by ring
    linarith [hmono.trans hsum]
  linarith

/-- **SMALL** (FKP Thm 2.5 for qc pullbacks of `Δ`; v3, the pre-approved `∀ η ∃ ε₁` form). There is
`ε₀ > 0` such that for every `η > 0` there is `ε₁ > 0` with: if `F` is a `K`-qc homeomorphism of `ℂ` with
`F(𝔻) = 𝔻`, `F(0) = 0`, and `a` is a measurable Whitney majorant of `|μ_F|` on `𝔻` (`|μ_F| ≤ a(z)` a.e. on
`D(z, (1-|z|)/2)` for every `z ∈ 𝔻`) with `a ≤ ε₀` on `𝔻` and the Carleson norm of `a(z)²/(1-|z|²) dA` on
`𝔻` at most `ε ≤ ε₁`, then the boundary lift `H` of `F|_𝕋` is absolutely continuous, `H' > 0` a.e., and
the mean oscillation of `log H'` on every arc is at most `η`. (`F(0) = 0` excludes disk automorphisms,
which have `μ = 0` and non-constant `|H'|`. v2 asked for the rate `C √ε`; the available route through Mori
gives only a power of `ε` (triage `collaboration/TRIAGE_w4_FKPS_M6.md` §1), whence the qualitative form.) -/
theorem s07c_fkps_small : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ η : ℝ, 0 < η → ∃ ε₁ : ℝ, 0 < ε₁ ∧
    ∀ (F : ℂ → ℂ) (a : ℂ → ℝ) (K ε : ℝ),
    IsKQC F univ K → F '' univ = univ → F '' unitDisc = unitDisc → F 0 = 0 →
    Measurable a → (∀ z, 0 ≤ a z) → (∀ z ∈ unitDisc, a z ≤ ε₀) →
    (∀ z ∈ unitDisc, ∀ᵐ w, w ∈ ball z ((1 - ‖z‖) / 2) →
      ‖LiZhongQC.complexDilatation F w‖ ≤ a z) →
    0 ≤ ε → ε ≤ ε₁ →
    (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (a z ^ 2 / (1 - ‖z‖ ^ 2))
        ≤ ENNReal.ofReal (ε * r)) →
    ∃ H u : ℝ → ℝ, StrictMono H ∧ Continuous H ∧ (∀ θ : ℝ, H (θ + 2 * π) = H θ + 2 * π) ∧
      (∀ θ : ℝ, F (Complex.exp (θ * Complex.I)) = Complex.exp (H θ * Complex.I)) ∧
      (∀ a b : ℝ, IntegrableOn u (Icc a b)) ∧
      (∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t) ∧ (∀ᵐ t, 0 < u t) ∧
      (∀ a b : ℝ, IntegrableOn (fun t => Real.log (u t)) (Icc a b)) ∧
      ∀ a b : ℝ, a < b → b - a ≤ 2 * π →
        (∫ t in a..b, |Real.log (u t) - (∫ s in a..b, Real.log (u s)) / (b - a)|) / (b - a)
          ≤ η := by
  obtain ⟨εG, CG, hεG, hCG, hG⟩ := s07c_fkps_m6_global
  obtain ⟨εA, CA, hεA, hCA, hA⟩ := s07c_fkps_m6_ainf
  obtain ⟨η₀, CJ, hη₀, hCJ, hJ⟩ := s07c_fkps_m6_jn
  set ε₀ : ℝ := min (min εG εA) (1 / 2) with hε₀
  have hε₀p : 0 < ε₀ := lt_min (lt_min hεG hεA) (by norm_num)
  refine ⟨ε₀, hε₀p, fun η hη => ?_⟩
  set x : ℝ := min η₀ (η / CJ) / CA with hx
  have hxp : 0 < x := div_pos (lt_min hη₀ (div_pos hη hCJ)) hCA
  refine ⟨min ε₀ (x ^ 8), lt_min hε₀p (pow_pos hxp 8), ?_⟩
  intro F a K ε hF hFs hFD hF0 ha ha0 hale hW hε hε₁ hC
  have hεε₀ : ε ≤ ε₀ := hε₁.trans (min_le_left _ _)
  have hε₀G : ε₀ ≤ εG := (min_le_left _ _).trans (min_le_left _ _)
  have hε₀A : ε₀ ≤ εA := (min_le_left _ _).trans (min_le_right _ _)
  have hε₀h : ε₀ ≤ 1 / 2 := min_le_right _ _
  -- the boundary lift
  have hμ := s07c_fkps_m6_dil_le hale hW
  have hK' := s07c_fkps_m6_kqc hF hε₀p.le (by linarith) hμ
  have hFc : Continuous F := continuousOn_univ.mp hF.2.2.1.1
  have hb : HasDiskBoundaryValues F F := fun ζ _ =>
    hFc.continuousAt.continuousWithinAt.tendsto
  obtain ⟨H, hHm, hHc, hHp, hHF⟩ := s07_circleHomeo_of_qcExt hK' hFD hb
  have haleG : ∀ z ∈ unitDisc, a z ≤ εG := fun z hz => (hale z hz).trans hε₀G
  have haleA : ∀ z ∈ unitDisc, a z ≤ εA := fun z hz => (hale z hz).trans hε₀A
  obtain ⟨u, ρ, hui, hrep, hu0, -⟩ := hG F a K ε H hF hFs hFD hF0 ha ha0 haleG hW hε
    (hεε₀.trans hε₀G) hC hHm hHc hHp hHF
  have hAinf := hA F a K ε H u hF hFs hFD hF0 ha ha0 haleA hW hε (hεε₀.trans hε₀A) hC hHm hHc hHp
    hHF hui hrep
  -- the A∞ constant is small
  have hrt : ε ^ (1 / 8 : ℝ) ≤ x := by
    have h1 : ε ^ (1 / 8 : ℝ) ≤ (x ^ 8) ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow hε (hε₁.trans (min_le_right _ _)) (by norm_num)
    have h2 : (x ^ 8) ^ (1 / 8 : ℝ) = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxp.le]
      norm_num
    linarith
  have hη' : CA * ε ^ (1 / 8 : ℝ) ≤ min η₀ (η / CJ) := by
    have := mul_le_mul_of_nonneg_left hrt hCA.le
    rwa [hx, mul_div_cancel₀ _ hCA.ne'] at this
  have hη'0 : 0 ≤ CA * ε ^ (1 / 8 : ℝ) := mul_nonneg hCA.le (Real.rpow_nonneg hε _)
  have hpos : ∀ a b : ℝ, a < b → 0 < ∫ t in a..b, u t := by
    intro a b hab
    have hii : ∀ c d : ℝ, IntervalIntegrable u volume c d := fun c d =>
      IntegrableOn.intervalIntegrable (hui (min c d) (max c d))
    have hsub : (∫ t in a..b, u t) = (∫ t in (0 : ℝ)..b, u t) - ∫ t in (0 : ℝ)..a, u t :=
      (intervalIntegral.integral_interval_sub_left (hii 0 b) (hii 0 a)).symm
    have h1 := hrep a
    have h2 := hrep b
    have h3 := hHm hab
    linarith
  obtain ⟨hpos', hlog, hosc⟩ := hJ u (CA * ε ^ (1 / 8 : ℝ)) hη'0 (hη'.trans (min_le_left _ _)) hui hu0
    hpos hAinf
  refine ⟨H, u, hHm, hHc, hHp, hHF, hui, hrep, hpos', hlog, fun a b hab hb2 => ?_⟩
  refine (hosc a b hab hb2).trans ?_
  have := mul_le_mul_of_nonneg_left (hη'.trans (min_le_right _ _)) hCJ.le
  rwa [mul_div_cancel₀ _ hCJ.ne'] at this

end EpsteinVMO
