import EpsteinVMO.S02_Prelim
import EpsteinVMO.S03_Coarse
import LiZhongQC.Lemmas.CaratheodoryJordan

/-!
# §7 Carleson measures in the disk and transfer across the curve

Source: `sec07-transfer.tex`.

## Section-local definitions (shared with §8, §11)

* Disk notation: `varpi` (`ϖ = 1 - |z|²`), `diskKernel` (`k_a`), `varpiMeasure` (`ϖ m`),
  `poissonP` (`𝒫_m`), `carlesonNorm` (`‖·‖_CM`), `DiskBoundaryVanishing`
  (`lim_{r↑1} sup_{r<|a|<1} F(a) = 0`).
* Coarse maps of `𝔻`: `IsDiskQI`, `HasDiskBoundaryValues`, `IsClosedDiskHomeo`, `IsDiskBiLip`,
  `IsBiLipDiskDiffeo`, the Morse constants `morseD` (7.3).
* The far side: `IsRoundCircle`, `pullbackMass` (`m_f`), `jRefl` (`j`), `outerPt`, `farMass`
  (`m^*`), `IsFarSideMap` (`A = f⁻¹ ∘ R ∘ g ∘ j`). Example 7.12: `hpDist`, `hpKernel`, `powerMap`.

## Imported from `S02_Prelim` (w1)

`IsDiskWelding` (conformal welding `h = f⁻¹ ∘ g|_{∂𝔻}`), `IsCircleHomeo`, `IsStronglyQS`,
`IsStronglyQSWith h δf` (with the modulus `δf`, the "strong quasisymmetry data"),
`IsStronglySymmetric`. Section-local here: `AdmitsQCDiskExt`, `diskMobius`, `dzC`,
`carlesonPullback`.

The strong quasisymmetry of the boundary map `x ↦ x|x|^{α-1}` in Example 7.12 is a statement about
`SQS(ℝ)`, defined in §11 (`S11_HalfPlane`, which imports this file); it is stated there.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace EpsteinVMO

open LiZhongQC

/-! ## Disk notation -/

/-- `ϖ(z) = 1 - |z|²` (`sec07-transfer.tex:14`). -/
def varpi (z : ℂ) : ℝ := 1 - ‖z‖ ^ 2

/-- The disk kernel `k_a(z) = ϖ(a)ϖ(z)/|1 - ā z|²` (`sec07-transfer.tex:17`). -/
def diskKernel (a z : ℂ) : ℝ := varpi a * varpi z / ‖1 - conj a * z‖ ^ 2

/-- The measure `ϖ m` on `𝔻`: `d(ϖ m) = ϖ dm` (`m` restricted to `𝔻`). -/
def varpiMeasure (m : Measure ℂ) : Measure ℂ :=
  (m.restrict unitDisc).withDensity fun z => ENNReal.ofReal (varpi z)

/-- `𝒫_m(a) = ∫_𝔻 k_a dm ∈ [0, ∞]` (`sec07-transfer.tex:24`). -/
def poissonP (m : Measure ℂ) (a : ℂ) : ℝ≥0∞ :=
  ∫⁻ z in unitDisc, ENNReal.ofReal (diskKernel a z) ∂m

/-- The Carleson norm `‖μ‖_CM = sup {μ(𝔻 ∩ D(ζ,r))/r : ζ ∈ ∂𝔻, 0 < r < 2}` (§2.5). -/
def carlesonNorm (μ : Measure ℂ) : ℝ≥0∞ :=
  ⨆ ζ ∈ sphere (0 : ℂ) 1, ⨆ r ∈ Ioo (0 : ℝ) 2, μ (unitDisc ∩ ball ζ r) / ENNReal.ofReal r

/-- `lim_{r↑1} sup_{r<|a|<1} F(a) = 0`. -/
def DiskBoundaryVanishing (F : ℂ → ℝ≥0∞) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ r : ℝ, r < 1 ∧ ∀ a : ℂ, r < ‖a‖ → ‖a‖ < 1 → F a ≤ ε

/-- `|1 - ā z|² = (1 - |a|²)(1 - |z|²) + |a - z|²`. -/
theorem s07_norm_one_sub_conj_mul_sq (a z : ℂ) :
    ‖1 - conj a * z‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) + ‖a - z‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re,
    Complex.one_im]
  ring

/-- `0 < ϖ(z)` on `𝔻`. -/
theorem s07_varpi_pos {z : ℂ} (hz : z ∈ unitDisc) : 0 < varpi z := by
  have h : ‖z‖ < 1 := by simpa [unitDisc] using hz
  have h0 := norm_nonneg z
  unfold varpi
  nlinarith

/-- Display `sec07-transfer.tex:17`: `k_a(z) = sech²(d_𝔻(a,z)/2) = ϖ(a)ϖ(z)/|1 - ā z|²`. -/
theorem sec07_kernel_formula (a z : ℂ) (ha : a ∈ unitDisc) (hz : z ∈ unitDisc) :
    diskKernel a z = ((Real.cosh (diskDist a z / 2))⁻¹) ^ 2 := by
  have hva := s07_varpi_pos ha
  have hvz := s07_varpi_pos hz
  have hx : 1 ≤ diskCoshDist a z := by
    unfold diskCoshDist
    have : 0 ≤ 2 * ‖a - z‖ ^ 2 / ((1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2)) := by
      unfold varpi at hva hvz; positivity
    linarith
  have hc : Real.cosh (diskDist a z / 2) ^ 2 = (1 + diskCoshDist a z) / 2 := by
    have h2 := Real.cosh_two_mul (diskDist a z / 2)
    have h3 := Real.cosh_sq (diskDist a z / 2)
    rw [mul_div_cancel₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)] at h2
    unfold diskDist at h2 h3 ⊢
    rw [Real.cosh_arcosh hx] at h2
    linarith
  rw [inv_pow, hc]
  unfold diskKernel diskCoshDist
  rw [s07_norm_one_sub_conj_mul_sq]
  unfold varpi at hva hvz ⊢
  field_simp
  ring

/-! ## The kernel test -/

/-- Lemma 7.1 (a), `lem:kernel-test` (`sec07-transfer.tex:32`). For a positive Borel measure
`m` on `𝔻` and `ν = ϖ m`: `𝒫_m(a) = ∫_𝔻 ϖ(a)/|1 - ā z|² dν(z)`. -/
theorem lem_kernel_test_a (m : Measure ℂ) (a : ℂ) (ha : a ∈ unitDisc) :
    poissonP m a =
      ∫⁻ z in unitDisc, ENNReal.ofReal (varpi a / ‖1 - conj a * z‖ ^ 2) ∂varpiMeasure m := by
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hva := s07_varpi_pos ha
  have hmv : Measurable fun z : ℂ => ENNReal.ofReal (varpi z) := by
    unfold varpi; fun_prop
  have hmg : Measurable fun z : ℂ => ENNReal.ofReal (varpi a / ‖1 - conj a * z‖ ^ 2) := by
    fun_prop
  unfold varpiMeasure poissonP
  rw [setLIntegral_withDensity_eq_setLIntegral_mul _ hmv hmg hD, Measure.restrict_restrict hD,
    inter_self]
  refine setLIntegral_congr_fun hD fun z hz => ?_
  have hvz := s07_varpi_pos hz
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul hvz.le]
  unfold diskKernel
  congr 1
  ring

/-- `‖1 - ā z‖ ≥ 1 - ‖a‖` on `𝔻`. -/
theorem s07_one_sub_norm_le (a z : ℂ) (hz : z ∈ unitDisc) (ha : 0 ≤ 1 - ‖a‖) :
    1 - ‖a‖ ≤ ‖1 - conj a * z‖ := by
  have h : ‖z‖ < 1 := by simpa [unitDisc] using hz
  have h1 : ‖conj a * z‖ ≤ ‖a‖ := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_of_le_one_right (norm_nonneg a) h.le
  have h2 := norm_sub_norm_le (1 : ℂ) (conj a * z)
  rw [norm_one] at h2
  linarith

/-- (7.2) `eq:denominator`, as a helper (Lemma 7.1 (b) uses it; the labelled statement is below). -/
theorem s07_denominator (a z : ℂ) (ha : a ∈ unitDisc) (ha0 : a ≠ 0) (hz : z ∈ unitDisc) :
    max (1 - ‖a‖) (‖a / (‖a‖ : ℂ) - z‖ / 2) ≤ ‖1 - conj a * z‖ := by
  have ha1 : ‖a‖ < 1 := by simpa [unitDisc] using ha
  have hz1 : ‖z‖ < 1 := by simpa [unitDisc] using hz
  have hδ := s07_one_sub_norm_le a z hz (by linarith)
  have hr : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hrC : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h1 : a * conj a = (‖a‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have key : a / (‖a‖ : ℂ) - (‖a‖ : ℂ) * z = a / (‖a‖ : ℂ) * (1 - conj a * z) := by
    field_simp
    linear_combination z * h1
  have hζ : ‖a / (‖a‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
  have hn : ‖a / (‖a‖ : ℂ) - (‖a‖ : ℂ) * z‖ = ‖1 - conj a * z‖ := by
    rw [key, norm_mul, hζ, one_mul]
  have htri : ‖a / (‖a‖ : ℂ) - z‖ ≤ ‖a / (‖a‖ : ℂ) - (‖a‖ : ℂ) * z‖ + ‖(‖a‖ : ℂ) * z - z‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hrz : ‖(‖a‖ : ℂ) * z - z‖ ≤ 1 - ‖a‖ := by
    have : (‖a‖ : ℂ) * z - z = -(((1 - ‖a‖ : ℝ) : ℂ) * z) := by push_cast; ring
    rw [this, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact mul_le_of_le_one_right (by linarith) hz1.le
  rw [max_le_iff]
  constructor
  · exact hδ
  · rw [hn] at htri
    linarith

/-- `μ(𝔻 ∩ D(ζ, r)) ≤ ‖μ‖_CM r` for `ζ ∈ ∂𝔻`, `0 < r < 2`. -/
theorem s07_le_carlesonNorm (μ : Measure ℂ) (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) 1) (r : ℝ)
    (hr0 : 0 < r) (hr2 : r < 2) :
    μ (unitDisc ∩ ball ζ r) ≤ carlesonNorm μ * ENNReal.ofReal r := by
  have h : μ (unitDisc ∩ ball ζ r) / ENNReal.ofReal r ≤ carlesonNorm μ := by
    unfold carlesonNorm
    exact le_iSup₂_of_le ζ hζ (le_iSup₂_of_le r ⟨hr0, hr2⟩ le_rfl)
  rwa [ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hr0).ne' ENNReal.ofReal_ne_top] at h

/-- (7.1) `eq:total-mass`, as a helper (Lemma 7.1 (b) uses it; the labelled statement is below). -/
theorem s07_total_mass (μ : Measure ℂ) :
    μ unitDisc ≤ ENNReal.ofReal (2 * Real.sqrt 2) * carlesonNorm μ := by
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hs2' : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' two_pos]; norm_num
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hcover : unitDisc ⊆ (unitDisc ∩ ball 1 (Real.sqrt 2)) ∪
      (unitDisc ∩ ball (-1) (Real.sqrt 2)) := by
    intro z hz
    have hz1 : ‖z‖ < 1 := by simpa [unitDisc] using hz
    have hpar : ‖z - 1‖ ^ 2 + ‖z + 1‖ ^ 2 = 2 * ‖z‖ ^ 2 + 2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
      ring
    by_contra hcon
    simp only [mem_union, mem_inter_iff, mem_ball, dist_eq_norm, not_or, not_and,
      not_lt, sub_neg_eq_add] at hcon
    have h1 := hcon.1 hz
    have h2 := hcon.2 hz
    have h0 := norm_nonneg z
    nlinarith [Real.sqrt_nonneg 2]
  have hb1 : (1 : ℂ) ∈ sphere (0 : ℂ) 1 := by simp
  have hb2 : (-1 : ℂ) ∈ sphere (0 : ℂ) 1 := by simp
  calc μ unitDisc ≤ μ ((unitDisc ∩ ball 1 (Real.sqrt 2)) ∪ (unitDisc ∩ ball (-1) (Real.sqrt 2))) :=
        measure_mono hcover
    _ ≤ μ (unitDisc ∩ ball 1 (Real.sqrt 2)) + μ (unitDisc ∩ ball (-1) (Real.sqrt 2)) :=
        measure_union_le _ _
    _ ≤ carlesonNorm μ * ENNReal.ofReal (Real.sqrt 2) +
          carlesonNorm μ * ENNReal.ofReal (Real.sqrt 2) :=
        add_le_add (s07_le_carlesonNorm μ 1 hb1 _ hs2 hs2')
          (s07_le_carlesonNorm μ (-1) hb2 _ hs2 hs2')
    _ = ENNReal.ofReal (2 * Real.sqrt 2) * carlesonNorm μ := by
        rw [two_mul, ENNReal.ofReal_add hs2.le hs2.le]
        ring

/-- `‖a/|a|‖ = 1` for `a ≠ 0`. -/
theorem s07_norm_div_norm (a : ℂ) (ha0 : a ≠ 0) : a / (‖a‖ : ℂ) ∈ sphere (0 : ℂ) 1 := by
  have hr : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    div_self hr.ne']

/-- `‖(1 - r) ζ‖ = 1 - r` for `ζ ∈ ∂𝔻`, `r ≤ 1`. -/
theorem s07_norm_shift (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) 1) (r : ℝ) (hr1 : r ≤ 1) :
    ‖((1 - r : ℝ) : ℂ) * ζ‖ = 1 - r := by
  have hζ1 : ‖ζ‖ = 1 := by simpa using hζ
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), hζ1, mul_one]

/-- `𝒫_m(a) ≤ 2/(1-|a|) ν(𝔻)`. -/
theorem s07_poissonP_le_mass (m : Measure ℂ) (a : ℂ) (ha : a ∈ unitDisc) :
    poissonP m a ≤ ENNReal.ofReal (2 / (1 - ‖a‖)) * varpiMeasure m unitDisc := by
  have ha1 : ‖a‖ < 1 := by simpa [unitDisc] using ha
  have hpos : 0 < 1 - ‖a‖ := by linarith
  rw [lem_kernel_test_a m a ha, ← setLIntegral_const]
  refine setLIntegral_mono measurable_const fun z hz => ENNReal.ofReal_le_ofReal ?_
  have h1 := s07_one_sub_norm_le a z hz hpos.le
  have hN2 : (1 - ‖a‖) ^ 2 ≤ ‖1 - conj a * z‖ ^ 2 := pow_le_pow_left₀ hpos.le h1 2
  have hNpos : 0 < ‖1 - conj a * z‖ ^ 2 := by
    have : 0 < ‖1 - conj a * z‖ := lt_of_lt_of_le hpos h1
    positivity
  rw [div_le_div_iff₀ hNpos hpos]
  unfold varpi
  nlinarith [mul_nonneg (sq_nonneg (1 - ‖a‖)) hpos.le, norm_nonneg a]

/-- `ν(𝔻) ≤ 4/ϖ(a) 𝒫_m(a)` (since `|1 - ā z| < 2`). -/
theorem s07_mass_le_poissonP (m : Measure ℂ) (a : ℂ) (ha : a ∈ unitDisc) :
    varpiMeasure m unitDisc ≤ ENNReal.ofReal (4 / varpi a) * poissonP m a := by
  have ha1 : ‖a‖ < 1 := by simpa [unitDisc] using ha
  have hva := s07_varpi_pos ha
  have hlow : ENNReal.ofReal (varpi a / 4) * varpiMeasure m unitDisc ≤ poissonP m a := by
    rw [lem_kernel_test_a m a ha, ← setLIntegral_const]
    refine setLIntegral_mono (by fun_prop) fun z hz => ENNReal.ofReal_le_ofReal ?_
    have hz1 : ‖z‖ < 1 := by simpa [unitDisc] using hz
    have h1 := s07_one_sub_norm_le a z hz (by linarith)
    have hNpos : 0 < ‖1 - conj a * z‖ ^ 2 := by
      have : 0 < ‖1 - conj a * z‖ := by linarith
      positivity
    have hN : ‖1 - conj a * z‖ ≤ 2 := by
      have := norm_sub_le (1 : ℂ) (conj a * z)
      rw [norm_one, norm_mul, Complex.norm_conj] at this
      nlinarith [norm_nonneg a, norm_nonneg z]
    have hN2 : ‖1 - conj a * z‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (1 - conj a * z)]
    exact div_le_div_of_nonneg_left hva.le hNpos hN2
  calc varpiMeasure m unitDisc
      = ENNReal.ofReal (4 / varpi a) *
          (ENNReal.ofReal (varpi a / 4) * varpiMeasure m unitDisc) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          show 4 / varpi a * (varpi a / 4) = 1 by field_simp, ENNReal.ofReal_one, one_mul]
    _ ≤ _ := mul_le_mul_right hlow _

/-- Lower bound of (b): `ν(S(ζ, r)) ≤ 4r 𝒫_m((1-r)ζ)` for `0 < r ≤ 1`. -/
theorem s07_ball_le_poissonP (m : Measure ℂ) (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) 1) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    varpiMeasure m (unitDisc ∩ ball ζ r) ≤
      ENNReal.ofReal (4 * r) * poissonP m (((1 - r : ℝ) : ℂ) * ζ) := by
  have hζ1 : ‖ζ‖ = 1 := by simpa using hζ
  have hna := s07_norm_shift ζ hζ r hr1
  have ha : ((1 - r : ℝ) : ℂ) * ζ ∈ unitDisc := by
    simp only [unitDisc, mem_ball_zero_iff, hna]; linarith
  have hζc : ζ * conj ζ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ1]; simp
  have hlow : ENNReal.ofReal (1 / (4 * r)) * varpiMeasure m (unitDisc ∩ ball ζ r) ≤
      poissonP m (((1 - r : ℝ) : ℂ) * ζ) := by
    rw [lem_kernel_test_a m _ ha, ← setLIntegral_const]
    refine le_trans (setLIntegral_mono (by fun_prop) fun z hz => ENNReal.ofReal_le_ofReal ?_)
      (lintegral_mono_set inter_subset_left)
    have hz1 : ‖z‖ < 1 := by simpa [unitDisc] using hz.1
    have hzζ : ‖ζ - z‖ < r := by rw [← dist_eq_norm, dist_comm]; exact hz.2
    have key : ζ * (1 - conj (((1 - r : ℝ) : ℂ) * ζ) * z) = ζ - ((1 - r : ℝ) : ℂ) * z := by
      rw [map_mul, Complex.conj_ofReal]
      linear_combination (-(((1 - r : ℝ) : ℂ)) * z) * hζc
    have hNeq : ‖1 - conj (((1 - r : ℝ) : ℂ) * ζ) * z‖ = ‖ζ - ((1 - r : ℝ) : ℂ) * z‖ := by
      rw [← key, norm_mul, hζ1, one_mul]
    have hN : ‖1 - conj (((1 - r : ℝ) : ℂ) * ζ) * z‖ < 2 * r := by
      rw [hNeq]
      have h1 : ζ - ((1 - r : ℝ) : ℂ) * z = (ζ - z) + ((r : ℝ) : ℂ) * z := by push_cast; ring
      rw [h1]
      refine (norm_add_le _ _).trans_lt ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      nlinarith
    have hNpos : 0 < ‖1 - conj (((1 - r : ℝ) : ℂ) * ζ) * z‖ := by
      have := s07_one_sub_norm_le (((1 - r : ℝ) : ℂ) * ζ) z hz.1 (by rw [hna]; linarith)
      rw [hna] at this; linarith
    have hv : r ≤ varpi (((1 - r : ℝ) : ℂ) * ζ) := by
      unfold varpi; rw [hna]; nlinarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc varpiMeasure m (unitDisc ∩ ball ζ r)
      = ENNReal.ofReal (4 * r) *
          (ENNReal.ofReal (1 / (4 * r)) * varpiMeasure m (unitDisc ∩ ball ζ r)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          mul_one_div_cancel (by positivity), ENNReal.ofReal_one, one_mul]
    _ ≤ _ := mul_le_mul_right hlow _

/-- Pointwise dyadic domination of the integrand of (a) (`a ≠ 0`, `δ = 1 - |a|`,
`ζ = a/|a|`). -/
theorem s07_shell_bound (a z : ℂ) (ha : a ∈ unitDisc) (ha0 : a ≠ 0) (hz : z ∈ unitDisc) :
    ENNReal.ofReal (varpi a / ‖1 - conj a * z‖ ^ 2) ≤
      ∑' k : ℕ, ENNReal.ofReal (24 / (4 ^ (k + 1) * (1 - ‖a‖))) *
        (ball (a / (‖a‖ : ℂ)) (2 ^ (k + 1) * (1 - ‖a‖))).indicator 1 z := by
  classical
  have ha1 : ‖a‖ < 1 := by simpa [unitDisc] using ha
  have hδ0 : 0 < 1 - ‖a‖ := by linarith
  have hex : ∃ j : ℕ, dist z (a / (‖a‖ : ℂ)) < 2 ^ (j + 1) * (1 - ‖a‖) := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (dist z (a / (‖a‖ : ℂ)) / (1 - ‖a‖))
      (one_lt_two : (1 : ℝ) < 2)
    refine ⟨j, ?_⟩
    rw [div_lt_iff₀ hδ0] at hj
    have h2 : (2 : ℝ) ^ j * (1 - ‖a‖) ≤ 2 ^ (j + 1) * (1 - ‖a‖) := by
      gcongr
      · norm_num
      · omega
    linarith
  set j := Nat.find hex with hjdef
  have hj : dist z (a / (‖a‖ : ℂ)) < 2 ^ (j + 1) * (1 - ‖a‖) := Nat.find_spec hex
  have hden := s07_denominator a z ha ha0 hz
  have hN : 2 ^ j * (1 - ‖a‖) / 2 ≤ ‖1 - conj a * z‖ := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0, pow_zero, one_mul]
      have := (le_max_left _ _).trans hden
      linarith
    · have hmin : ¬ dist z (a / (‖a‖ : ℂ)) < 2 ^ (j - 1 + 1) * (1 - ‖a‖) :=
        Nat.find_min hex (by omega)
      rw [Nat.sub_add_cancel hpos, not_lt, dist_eq_norm, norm_sub_rev] at hmin
      have := (le_max_right _ _).trans hden
      linarith
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have h4 : (4 : ℝ) ^ (j + 1) = 4 * ((2 : ℝ) ^ j) ^ 2 := by
    rw [← pow_mul, pow_succ, mul_comm (4 : ℝ), mul_comm j 2, pow_mul]; norm_num
  have hreal : varpi a / ‖1 - conj a * z‖ ^ 2 ≤ 32 / (4 ^ (j + 1) * (1 - ‖a‖)) := by
    have hNpos : 0 < ‖1 - conj a * z‖ := lt_of_lt_of_le (by positivity) hN
    have hva : varpi a ≤ 2 * (1 - ‖a‖) := by
      unfold varpi; nlinarith [norm_nonneg a]
    rw [div_le_div_iff₀ (by positivity) (by positivity), h4]
    have hN2 := mul_le_mul hN hN (by positivity) hNpos.le
    have hv0 : 0 ≤ varpi a := (s07_varpi_pos ha).le
    nlinarith [mul_le_mul_of_nonneg_right hva
      (show 0 ≤ 4 * ((2 : ℝ) ^ j) ^ 2 * (1 - ‖a‖) by positivity)]
  have hfun : (fun k : ℕ => 24 / (4 ^ (k + j + 1) * (1 - ‖a‖))) =
      fun k : ℕ => 24 / (4 ^ (j + 1) * (1 - ‖a‖)) * (1 / 4 : ℝ) ^ k := by
    funext k
    rw [show k + j + 1 = k + (j + 1) by ring, pow_add, one_div_pow]
    field_simp
  have hsum : Summable fun k : ℕ => 24 / (4 ^ (j + 1) * (1 - ‖a‖)) * (1 / 4 : ℝ) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have htail : ENNReal.ofReal (32 / (4 ^ (j + 1) * (1 - ‖a‖))) =
      ∑' k : ℕ, ENNReal.ofReal (24 / (4 ^ (k + j + 1) * (1 - ‖a‖))) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) (hfun ▸ hsum), hfun,
      tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    congr 1
    field_simp
    norm_num
  set F : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (24 / (4 ^ (k + 1) * (1 - ‖a‖))) *
    (ball (a / (‖a‖ : ℂ)) (2 ^ (k + 1) * (1 - ‖a‖))).indicator 1 z with hF
  calc ENNReal.ofReal (varpi a / ‖1 - conj a * z‖ ^ 2)
      ≤ ENNReal.ofReal (32 / (4 ^ (j + 1) * (1 - ‖a‖))) := ENNReal.ofReal_le_ofReal hreal
    _ = ∑' k : ℕ, ENNReal.ofReal (24 / (4 ^ (k + j + 1) * (1 - ‖a‖))) := htail
    _ = ∑' k : ℕ, F (k + j) := by
        congr 1
        funext k
        have hmem : z ∈ ball (a / (‖a‖ : ℂ)) (2 ^ (k + j + 1) * (1 - ‖a‖)) := by
          rw [mem_ball]
          refine hj.trans_le ?_
          gcongr
          · norm_num
          · omega
        rw [hF]
        simp only
        rw [indicator_of_mem hmem, Pi.one_apply, mul_one]
    _ ≤ ∑' k : ℕ, F k := ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective j) F

/-- Integrated dyadic bound: `𝒫_m(a) ≤ ∑_k 24/(4^{k+1}δ) ν(S(ζ, 2^{k+1}δ))`. -/
theorem s07_poissonP_le_tsum (m : Measure ℂ) (a : ℂ) (ha : a ∈ unitDisc) (ha0 : a ≠ 0) :
    poissonP m a ≤ ∑' k : ℕ, ENNReal.ofReal (24 / (4 ^ (k + 1) * (1 - ‖a‖))) *
      varpiMeasure m (unitDisc ∩ ball (a / (‖a‖ : ℂ)) (2 ^ (k + 1) * (1 - ‖a‖))) := by
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hmk : ∀ k : ℕ, Measurable fun z : ℂ =>
      ENNReal.ofReal (24 / (4 ^ (k + 1) * (1 - ‖a‖))) *
        (ball (a / (‖a‖ : ℂ)) (2 ^ (k + 1) * (1 - ‖a‖))).indicator 1 z :=
    fun k => (measurable_one.indicator measurableSet_ball).const_mul _
  rw [lem_kernel_test_a m a ha]
  calc ∫⁻ z in unitDisc, ENNReal.ofReal (varpi a / ‖1 - conj a * z‖ ^ 2) ∂varpiMeasure m
      ≤ ∫⁻ z in unitDisc, ∑' k : ℕ, ENNReal.ofReal (24 / (4 ^ (k + 1) * (1 - ‖a‖))) *
          (ball (a / (‖a‖ : ℂ)) (2 ^ (k + 1) * (1 - ‖a‖))).indicator 1 z ∂varpiMeasure m :=
        setLIntegral_mono (Measurable.ennreal_tsum hmk) fun z hz => s07_shell_bound a z ha ha0 hz
    _ = _ := by
        rw [lintegral_tsum fun k => (hmk k).aemeasurable]
        congr 1
        funext k
        rw [lintegral_const_mul _ (measurable_one.indicator measurableSet_ball),
          lintegral_indicator_one measurableSet_ball, Measure.restrict_apply measurableSet_ball,
          inter_comm]

/-- `∑_k 12/2^k = 24`. -/
theorem s07_tsum_twelve : ∑' k : ℕ, ENNReal.ofReal (12 / 2 ^ k) = 24 := by
  have hfun : (fun k : ℕ => (12 : ℝ) / 2 ^ k) = fun k : ℕ => 12 * (1 / 2 : ℝ) ^ k := by
    funext k; rw [one_div_pow]; ring
  have hs : Summable fun k : ℕ => (12 : ℝ) / 2 ^ k := hfun ▸ summable_geometric_two.mul_left 12
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs, hfun, tsum_mul_left,
    tsum_geometric_two]
  norm_num

/-- `𝒫_m(a) ≤ ∑_k B_k 12/2^k` whenever `ν(S(ζ, 2^{k+1}δ)) ≤ B_k 2^{k+1}δ`. -/
theorem s07_poissonP_le_of_balls (m : Measure ℂ) (a : ℂ) (ha : a ∈ unitDisc) (ha0 : a ≠ 0)
    (B : ℕ → ℝ≥0∞) (hB : ∀ k : ℕ,
      varpiMeasure m (unitDisc ∩ ball (a / (‖a‖ : ℂ)) (2 ^ (k + 1) * (1 - ‖a‖))) ≤
        B k * ENNReal.ofReal (2 ^ (k + 1) * (1 - ‖a‖))) :
    poissonP m a ≤ ∑' k : ℕ, B k * ENNReal.ofReal (12 / 2 ^ k) := by
  have ha1 : ‖a‖ < 1 := by simpa [unitDisc] using ha
  have hδ0 : 0 < 1 - ‖a‖ := by linarith
  refine (s07_poissonP_le_tsum m a ha ha0).trans (ENNReal.tsum_le_tsum fun k => ?_)
  calc ENNReal.ofReal (24 / (4 ^ (k + 1) * (1 - ‖a‖))) *
        varpiMeasure m (unitDisc ∩ ball (a / (‖a‖ : ℂ)) (2 ^ (k + 1) * (1 - ‖a‖)))
      ≤ ENNReal.ofReal (24 / (4 ^ (k + 1) * (1 - ‖a‖))) *
          (B k * ENNReal.ofReal (2 ^ (k + 1) * (1 - ‖a‖))) := mul_le_mul_right (hB k) _
    _ = B k * ENNReal.ofReal (12 / 2 ^ k) := by
        rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [show (4 : ℝ) ^ (k + 1) = 2 ^ (k + 1) * 2 ^ (k + 1) by
          rw [← mul_pow]; norm_num, pow_succ (2 : ℝ) k]
        field_simp
        ring

/-- `ν(S(ζ, r)) ≤ 2 ‖ν‖_CM r` for every `r > 0`. -/
theorem s07_ball_le_two_mul (μ : Measure ℂ) (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) 1) (r : ℝ)
    (hr0 : 0 < r) :
    μ (unitDisc ∩ ball ζ r) ≤ 2 * carlesonNorm μ * ENNReal.ofReal r := by
  rcases lt_or_ge r 2 with hr2 | hr2
  · calc μ (unitDisc ∩ ball ζ r) ≤ carlesonNorm μ * ENNReal.ofReal r :=
          s07_le_carlesonNorm μ ζ hζ r hr0 hr2
      _ ≤ 2 * carlesonNorm μ * ENNReal.ofReal r := by
          rw [mul_assoc]; exact le_mul_of_one_le_left' (by norm_num)
  · have hs2 : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' two_pos]; norm_num
    calc μ (unitDisc ∩ ball ζ r) ≤ μ unitDisc := measure_mono inter_subset_left
      _ ≤ ENNReal.ofReal (2 * Real.sqrt 2) * carlesonNorm μ := s07_total_mass μ
      _ ≤ ENNReal.ofReal (2 * r) * carlesonNorm μ :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _
      _ = 2 * carlesonNorm μ * ENNReal.ofReal r := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]; ring

/-- Lemma 7.1 (b), `lem:kernel-test` (`sec07-transfer.tex:38`):
`‖ν‖_CM ≤ 4 sup_a 𝒫_m(a)` and `sup_a 𝒫_m(a) ≤ 80 ‖ν‖_CM`. No local finiteness is assumed. -/
theorem lem_kernel_test_b (m : Measure ℂ) :
    carlesonNorm (varpiMeasure m) ≤ 4 * ⨆ a ∈ unitDisc, poissonP m a ∧
      ⨆ a ∈ unitDisc, poissonP m a ≤ 80 * carlesonNorm (varpiMeasure m) := by
  have h0D : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hP0 : varpiMeasure m unitDisc ≤ 4 * poissonP m 0 := by
    have := s07_mass_le_poissonP m 0 h0D
    simpa [varpi] using this
  constructor
  · unfold carlesonNorm
    refine iSup₂_le fun ζ hζ => iSup₂_le fun r hr => ?_
    rcases le_or_gt r 1 with hr1 | hr1
    · have ha : ((1 - r : ℝ) : ℂ) * ζ ∈ unitDisc := by
        simp only [unitDisc, mem_ball_zero_iff, s07_norm_shift ζ hζ r hr1]; linarith [hr.1]
      refine ENNReal.div_le_of_le_mul ?_
      calc varpiMeasure m (unitDisc ∩ ball ζ r)
          ≤ ENNReal.ofReal (4 * r) * poissonP m (((1 - r : ℝ) : ℂ) * ζ) :=
            s07_ball_le_poissonP m ζ hζ r hr.1 hr1
        _ = 4 * poissonP m (((1 - r : ℝ) : ℂ) * ζ) * ENNReal.ofReal r := by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]; ring
        _ ≤ 4 * (⨆ a ∈ unitDisc, poissonP m a) * ENNReal.ofReal r := by
            gcongr
            exact le_iSup₂_of_le (f := fun a (_ : a ∈ unitDisc) => poissonP m a) _ ha le_rfl
    · refine ENNReal.div_le_of_le_mul ?_
      calc varpiMeasure m (unitDisc ∩ ball ζ r) ≤ varpiMeasure m unitDisc :=
            measure_mono inter_subset_left
        _ ≤ 4 * poissonP m 0 := hP0
        _ ≤ 4 * (⨆ a ∈ unitDisc, poissonP m a) := by
            gcongr
            exact le_iSup₂_of_le (f := fun a (_ : a ∈ unitDisc) => poissonP m a) _ h0D le_rfl
        _ ≤ 4 * (⨆ a ∈ unitDisc, poissonP m a) * ENNReal.ofReal r :=
            le_mul_of_one_le_right' (by
              rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr1.le)
  · refine iSup₂_le fun a ha => ?_
    by_cases ha0 : a = 0
    · subst ha0
      have hs2 : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' two_pos]; norm_num
      calc poissonP m 0 ≤ ENNReal.ofReal (2 / (1 - ‖(0 : ℂ)‖)) * varpiMeasure m unitDisc :=
            s07_poissonP_le_mass m 0 ha
        _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal (2 * Real.sqrt 2) *
              carlesonNorm (varpiMeasure m)) := by
            rw [norm_zero, sub_zero, div_one]; gcongr; exact s07_total_mass _
        _ = ENNReal.ofReal (2 * (2 * Real.sqrt 2)) * carlesonNorm (varpiMeasure m) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
        _ ≤ ENNReal.ofReal 80 * carlesonNorm (varpiMeasure m) :=
            mul_le_mul_left (ENNReal.ofReal_le_ofReal (by nlinarith)) _
        _ = 80 * carlesonNorm (varpiMeasure m) := by rw [ENNReal.ofReal_ofNat]
    · have hζ := s07_norm_div_norm a ha0
      have ha1 : ‖a‖ < 1 := by simpa [unitDisc] using ha
      calc poissonP m a ≤ ∑' k : ℕ, 2 * carlesonNorm (varpiMeasure m) *
            ENNReal.ofReal (12 / 2 ^ k) :=
            s07_poissonP_le_of_balls m a ha ha0 _ fun k =>
              s07_ball_le_two_mul _ _ hζ _ (mul_pos (by positivity) (by linarith))
        _ = 2 * carlesonNorm (varpiMeasure m) * 24 := by
            rw [ENNReal.tsum_mul_left, s07_tsum_twelve]
        _ ≤ 80 * carlesonNorm (varpiMeasure m) := by
            rw [mul_comm 2, mul_assoc, mul_comm]
            gcongr
            norm_num

/-- Lemma 7.1 (c), last sentence, as a helper (the (c) equivalence uses it; the labelled
statement is below). -/
theorem s07_kernel_test_c_bdd (m : Measure ℂ) (h : DiskBoundaryVanishing (poissonP m)) :
    ⨆ a ∈ unitDisc, poissonP m a < ⊤ := by
  obtain ⟨r, hr1, hr⟩ := h 1 one_pos
  set ρ : ℝ := (max r 0 + 1) / 2 with hρ
  have hm0 := le_max_right r 0
  have hmr := le_max_left r 0
  have hm1 : max r 0 < 1 := max_lt hr1 one_pos
  have hρ0 : 0 ≤ ρ := by rw [hρ]; linarith
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have hρr : r < ρ := by rw [hρ]; linarith
  have hnρ : ‖(ρ : ℂ)‖ = ρ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0]
  have hρD : (ρ : ℂ) ∈ unitDisc := by simp only [unitDisc, mem_ball_zero_iff, hnρ]; exact hρ1
  have hPρ : poissonP m ρ ≤ 1 := hr ρ (by rw [hnρ]; exact hρr) (by rw [hnρ]; exact hρ1)
  have hν : varpiMeasure m unitDisc < ⊤ :=
    calc varpiMeasure m unitDisc ≤ ENNReal.ofReal (4 / varpi ρ) * poissonP m ρ :=
          s07_mass_le_poissonP m ρ hρD
      _ ≤ ENNReal.ofReal (4 / varpi ρ) * 1 := mul_le_mul_right hPρ _
      _ < ⊤ := by rw [mul_one]; exact ENNReal.ofReal_lt_top
  have hK : max 1 (ENNReal.ofReal (2 / (1 - ρ)) * varpiMeasure m unitDisc) < ⊤ :=
    max_lt ENNReal.one_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hν)
  refine lt_of_le_of_lt (iSup₂_le fun a ha => ?_) hK
  have ha1 : ‖a‖ < 1 := by simpa [unitDisc] using ha
  by_cases hρa : ρ < ‖a‖
  · exact (hr a (hρr.trans hρa) ha1).trans (le_max_left _ _)
  · push_neg at hρa
    refine le_trans ?_ (le_max_right _ _)
    refine (s07_poissonP_le_mass m a ha).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

/-- Lemma 7.1 (c), `lem:kernel-test` (`sec07-transfer.tex:40`):
`ν ∈ CM₀(𝔻)` iff `lim_{r↑1} sup_{r<|a|<1} 𝒫_m(a) = 0`. -/
theorem lem_kernel_test_c (m : Measure ℂ) :
    IsVanishingCarlesonDisk (varpiMeasure m) ↔ DiskBoundaryVanishing (poissonP m) := by
  constructor
  · rintro ⟨⟨C0, hC0, hC0b⟩, hvan⟩
    have hCM : carlesonNorm (varpiMeasure m) ≤ C0 := by
      unfold carlesonNorm
      exact iSup₂_le fun ζ hζ => iSup₂_le fun r hr =>
        ENNReal.div_le_of_le_mul (hC0b ζ hζ r hr.1 hr.2)
    have hCt : carlesonNorm (varpiMeasure m) ≠ ⊤ := ne_top_of_le_ne_top hC0 hCM
    set C := carlesonNorm (varpiMeasure m) with hC
    intro ε hε
    rcases eq_or_ne ε ⊤ with hεt | hεt
    · exact ⟨0, zero_lt_one, fun _ _ _ => hεt ▸ le_top⟩
    set e := ε.toReal with he_def
    have he : 0 < e := ENNReal.toReal_pos hε.ne' hεt
    have hC' : 0 ≤ C.toReal := ENNReal.toReal_nonneg
    obtain ⟨δ0, hδ0, hδ0b⟩ := hvan (e / 48) (by positivity)
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
      (show 0 < e / (96 * (C.toReal + 1)) by positivity) (show (1 / 2 : ℝ) < 1 by norm_num)
    have h2N : (0 : ℝ) < 2 ^ N := by positivity
    refine ⟨max 0 (1 - δ0 / 2 ^ N), max_lt one_pos (by
      have : 0 < δ0 / 2 ^ N := by positivity
      linarith), fun a ha1 ha2 => ?_⟩
    have ha : a ∈ unitDisc := by simpa [unitDisc] using ha2
    have hapos : 0 < ‖a‖ := lt_of_le_of_lt (le_max_left _ _) ha1
    have ha0 : a ≠ 0 := norm_pos_iff.mp hapos
    have hζ := s07_norm_div_norm a ha0
    have hδ0' : 0 < 1 - ‖a‖ := by linarith
    have hsmall : 2 ^ N * (1 - ‖a‖) < δ0 := by
      have h := lt_of_le_of_lt (le_max_right _ _) ha1
      have : 1 - ‖a‖ < δ0 / 2 ^ N := by linarith
      rwa [lt_div_iff₀ h2N, mul_comm] at this
    set B : ℕ → ℝ≥0∞ := fun k => if k < N then ENNReal.ofReal (e / 48) else 2 * C with hB
    have hBk : ∀ k : ℕ,
        varpiMeasure m (unitDisc ∩ ball (a / (‖a‖ : ℂ)) (2 ^ (k + 1) * (1 - ‖a‖))) ≤
          B k * ENNReal.ofReal (2 ^ (k + 1) * (1 - ‖a‖)) := by
      intro k
      by_cases hk : k < N
      · simp only [hB, if_pos hk]
        have hrk : 2 ^ (k + 1) * (1 - ‖a‖) < δ0 := by
          refine lt_of_le_of_lt ?_ hsmall
          gcongr
          · norm_num
          · omega
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact hδ0b _ hζ _ (by positivity) hrk
      · simp only [hB, if_neg hk]
        exact s07_ball_le_two_mul _ _ hζ _ (by positivity)
    have hP := s07_poissonP_le_of_balls m a ha ha0 B hBk
    set w : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (12 / 2 ^ k) with hw
    set g : ℕ → ℝ≥0∞ := fun k => if N ≤ k then 2 * C * w k else 0 with hg
    have hterm : ∀ k, B k * w k ≤ ENNReal.ofReal (e / 48) * w k + g k := by
      intro k
      by_cases hk : k < N
      · simp only [hB, hg, if_pos hk, if_neg (not_le.mpr hk), add_zero, le_refl]
      · simp only [hB, hg, if_neg hk, if_pos (not_lt.mp hk)]
        exact le_add_self
    have hg_sum : ∑' k, g k = 2 * C * ENNReal.ofReal (1 / 2 ^ N) * 24 := by
      rw [← (ENNReal.summable (f := fun n => g (n + N))).sum_add_tsum_nat_add']
      have h1 : ∑ i ∈ Finset.range N, g i = 0 :=
        Finset.sum_eq_zero fun i hi => by
          simp only [hg, Finset.mem_range] at hi ⊢
          rw [if_neg (by omega)]
      have h2 : ∀ i : ℕ, g (i + N) = 2 * C * ENNReal.ofReal (1 / 2 ^ N) * w i := by
        intro i
        simp only [hg, hw, if_pos (show N ≤ i + N by omega)]
        rw [show (12 : ℝ) / 2 ^ (i + N) = 1 / 2 ^ N * (12 / 2 ^ i) by
          rw [pow_add]; field_simp, ENNReal.ofReal_mul (by positivity)]
        ring
      rw [h1, zero_add, tsum_congr h2, ENNReal.tsum_mul_left, s07_tsum_twelve]
    have hfin : 2 * C * ENNReal.ofReal (1 / 2 ^ N) * 24 ≤ ENNReal.ofReal (e / 2) := by
      rw [← ENNReal.ofReal_toReal hCt]
      rw [show (2 : ℝ≥0∞) * ENNReal.ofReal C.toReal * ENNReal.ofReal (1 / 2 ^ N) * 24 =
          ENNReal.ofReal (48 * C.toReal * (1 / 2) ^ N) by
        rw [one_div_pow, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_ofNat 24,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring]
      refine ENNReal.ofReal_le_ofReal ?_
      have hq : (0 : ℝ) ≤ (1 / 2) ^ N := by positivity
      have := mul_lt_mul_of_pos_left hN (show (0 : ℝ) < 48 * (C.toReal + 1) by positivity)
      have h96 : 48 * (C.toReal + 1) * (e / (96 * (C.toReal + 1))) = e / 2 := by
        field_simp; ring
      have h1 : 48 * C.toReal * (1 / 2) ^ N ≤ 48 * (C.toReal + 1) * (1 / 2) ^ N := by
        gcongr; linarith
      exact (h1.trans this.le).trans h96.le
    calc poissonP m a ≤ ∑' k, B k * w k := hP
      _ ≤ ∑' k, (ENNReal.ofReal (e / 48) * w k + g k) := ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (e / 48) * 24 + 2 * C * ENNReal.ofReal (1 / 2 ^ N) * 24 := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, s07_tsum_twelve, hg_sum]
      _ ≤ ENNReal.ofReal (e / 2) + ENNReal.ofReal (e / 2) := by
          gcongr
          rw [← ENNReal.ofReal_ofNat 24, ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (by linarith)
      _ = ε := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves, he_def,
            ENNReal.ofReal_toReal hεt]
  · intro h
    have hS := s07_kernel_test_c_bdd m h
    obtain ⟨hb1, -⟩ := lem_kernel_test_b m
    refine ⟨⟨4 * ⨆ a ∈ unitDisc, poissonP m a, ENNReal.mul_ne_top (by norm_num) hS.ne,
      fun ζ hζ r hr0 hr2 =>
        (s07_le_carlesonNorm _ ζ hζ r hr0 hr2).trans (mul_le_mul_left hb1 _)⟩, ?_⟩
    intro ε hε
    obtain ⟨r0, hr01, hr0⟩ := h (ENNReal.ofReal (ε / 4)) (ENNReal.ofReal_pos.mpr (by positivity))
    have hm1 : max r0 0 < 1 := max_lt hr01 one_pos
    refine ⟨1 - max r0 0, by linarith, fun ζ hζ r hr hrδ => ?_⟩
    have hr1 : r ≤ 1 := by linarith [le_max_right r0 0]
    have hna := s07_norm_shift ζ hζ r hr1
    calc varpiMeasure m (unitDisc ∩ ball ζ r)
        ≤ ENNReal.ofReal (4 * r) * poissonP m (((1 - r : ℝ) : ℂ) * ζ) :=
          s07_ball_le_poissonP m ζ hζ r hr hr1
      _ ≤ ENNReal.ofReal (4 * r) * ENNReal.ofReal (ε / 4) := by
          gcongr
          exact hr0 _ (by rw [hna]; linarith [le_max_left r0 0]) (by rw [hna]; linarith)
      _ = ENNReal.ofReal (ε * r) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

/-- Lemma 7.1 (c), last sentence (`sec07-transfer.tex:41`): the uniform vanishing already
implies `sup_a 𝒫_m(a) < ∞`. -/
theorem lem_kernel_test_c_bdd (m : Measure ℂ) (h : DiskBoundaryVanishing (poissonP m)) :
    ⨆ a ∈ unitDisc, poissonP m a < ⊤ := by
  exact s07_kernel_test_c_bdd m h

/-- (7.1) `eq:total-mass` (`sec07-transfer.tex:52`): `ν(𝔻) ≤ 2√2 ‖ν‖_CM` (for every positive
measure, since `𝔻 ⊂ S(1,√2) ∪ S(-1,√2)`). -/
theorem eq_total_mass (μ : Measure ℂ) :
    μ unitDisc ≤ ENNReal.ofReal (2 * Real.sqrt 2) * carlesonNorm μ := by
  exact s07_total_mass μ

/-- (7.2) `eq:denominator` (`sec07-transfer.tex:60`): for `a ≠ 0`, `δ = 1 - |a|`, `ζ = a/|a|`,
`|1 - ā z| ≥ max {δ, ½|ζ - z|}` on `𝔻`. -/
theorem eq_denominator (a z : ℂ) (ha : a ∈ unitDisc) (ha0 : a ≠ 0) (hz : z ∈ unitDisc) :
    max (1 - ‖a‖) (‖a / (‖a‖ : ℂ) - z‖ / 2) ≤ ‖1 - conj a * z‖ := by
  exact s07_denominator a z ha ha0 hz

/-- `k_a(x) ≤ e^{d(x, z)} k_a(z)` on `𝔻` (the kernel is `e^{d}`-Lipschitz in log). -/
theorem s07_diskKernel_le_exp (a x z : ℂ) (ha : a ∈ unitDisc) (hx : x ∈ unitDisc)
    (hz : z ∈ unitDisc) : diskKernel a x ≤ Real.exp (diskDist x z) * diskKernel a z := by
  rw [sec07_kernel_formula a x ha hx, sec07_kernel_formula a z ha hz, inv_pow, inv_pow]
  have hu : 0 ≤ diskDist a x := s02_diskDist_nonneg ha hx
  have hD : 0 ≤ diskDist x z := s02_diskDist_nonneg hx hz
  have htri : diskDist a z ≤ diskDist a x + diskDist x z := s02_diskDist_triangle ha hx hz
  have h0 : 0 ≤ diskDist a z := s02_diskDist_nonneg ha hz
  have hc1 : Real.cosh (diskDist a z / 2) ≤ Real.cosh ((diskDist a x + diskDist x z) / 2) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    linarith
  have hc2 : Real.cosh ((diskDist a x + diskDist x z) / 2) ≤
      Real.exp (diskDist x z / 2) * Real.cosh (diskDist a x / 2) := by
    rw [Real.cosh_eq, Real.cosh_eq]
    have e1 : Real.exp ((diskDist a x + diskDist x z) / 2) =
        Real.exp (diskDist x z / 2) * Real.exp (diskDist a x / 2) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-((diskDist a x + diskDist x z) / 2)) ≤
        Real.exp (diskDist x z / 2) * Real.exp (-(diskDist a x / 2)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    rw [e1]
    linarith
  have hcz : 0 < Real.cosh (diskDist a z / 2) := Real.cosh_pos _
  have hcx : 0 < Real.cosh (diskDist a x / 2) := Real.cosh_pos _
  have hsq : Real.cosh (diskDist a z / 2) ^ 2 ≤
      Real.exp (diskDist x z) * Real.cosh (diskDist a x / 2) ^ 2 := by
    have h := pow_le_pow_left₀ hcz.le (hc1.trans hc2) 2
    have he : Real.exp (diskDist x z / 2) ^ 2 = Real.exp (diskDist x z) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rwa [mul_pow, he] at h
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- Lemma 7.2, `lem:displacement` (`sec07-transfer.tex:122`), (7.3) `eq:displacement`: if
`d_𝔻(A y, B y) ≤ M` for all `y`, then `e^{-M} 𝒫_{B_*m} ≤ 𝒫_{A_*m} ≤ e^{M} 𝒫_{B_*m}`. -/
theorem lem_displacement {Y : Type*} [MeasurableSpace Y] (m : Measure Y) (A B : Y → ℂ)
    (hA : Measurable A) (hB : Measurable B) (hAD : ∀ y, A y ∈ unitDisc)
    (hBD : ∀ y, B y ∈ unitDisc) (M : ℝ) (hM : ∀ y, diskDist (A y) (B y) ≤ M)
    (a : ℂ) (ha : a ∈ unitDisc) :
    ENNReal.ofReal (Real.exp (-M)) * poissonP (m.map B) a ≤ poissonP (m.map A) a ∧
      poissonP (m.map A) a ≤ ENNReal.ofReal (Real.exp M) * poissonP (m.map B) a := by
  have hk : Measurable fun z => ENNReal.ofReal (diskKernel a z) := by
    unfold diskKernel varpi; fun_prop
  have hP : ∀ C : Y → ℂ, Measurable C → (∀ y, C y ∈ unitDisc) →
      poissonP (m.map C) a = ∫⁻ y, ENNReal.ofReal (diskKernel a (C y)) ∂m := by
    intro C hC hCD
    unfold poissonP
    have hDm : MeasurableSet unitDisc := measurableSet_ball
    rw [setLIntegral_map hDm hk hC,
      show C ⁻¹' unitDisc = univ from eq_univ_of_forall hCD, Measure.restrict_univ]
  have hnn : ∀ z ∈ unitDisc, 0 ≤ diskKernel a z := fun z hz => by
    rw [sec07_kernel_formula a z ha hz]; positivity
  have hpt : ∀ y, ENNReal.ofReal (diskKernel a (A y)) ≤
      ENNReal.ofReal (Real.exp M) * ENNReal.ofReal (diskKernel a (B y)) := by
    intro y
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ((s07_diskKernel_le_exp a _ _ ha (hAD y) (hBD y)).trans ?_)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hM y)) (hnn _ (hBD y))
  have hpt' : ∀ y, ENNReal.ofReal (Real.exp (-M)) * ENNReal.ofReal (diskKernel a (B y)) ≤
      ENNReal.ofReal (diskKernel a (A y)) := by
    intro y
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := s07_diskKernel_le_exp a _ _ ha (hBD y) (hAD y)
    rw [s02_diskDist_comm (hBD y) (hAD y)] at h1
    have h2 : Real.exp (diskDist (A y) (B y)) * diskKernel a (A y) ≤
        Real.exp M * diskKernel a (A y) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hM y)) (hnn _ (hAD y))
    have h3 : Real.exp (-M) * Real.exp M = 1 := by rw [← Real.exp_add]; simp
    have h4 := mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos (-M)).le
    rw [← mul_assoc, h3, one_mul] at h4
    exact h4
  have hkB : Measurable fun y => ENNReal.ofReal (diskKernel a (B y)) := hk.comp hB
  rw [hP A hA hAD, hP B hB hBD]
  constructor
  · rw [← lintegral_const_mul _ hkB]; exact lintegral_mono hpt'
  · rw [← lintegral_const_mul _ hkB]; exact lintegral_mono hpt

/-! ## Quasi-isometries with the same boundary values -/

/-- `A` is an `(L, c)`-quasi-isometry of `(𝔻, d_𝔻)` (no continuity assumed)
(`sec07-transfer.tex:146`). -/
def IsDiskQI (A : ℂ → ℂ) (L c : ℝ) : Prop :=
  MapsTo A unitDisc unitDisc ∧ ∀ x ∈ unitDisc, ∀ y ∈ unitDisc,
    L⁻¹ * diskDist x y - c ≤ diskDist (A x) (A y) ∧ diskDist (A x) (A y) ≤ L * diskDist x y + c

/-- `A : 𝔻 → 𝔻` has boundary values `h`: `A(z) → h(ζ)` as `z → ζ ∈ ∂𝔻`
(`sec07-transfer.tex:144`). -/
def HasDiskBoundaryValues (A h : ℂ → ℂ) : Prop :=
  ∀ ζ ∈ sphere (0 : ℂ) 1, Tendsto A (𝓝[unitDisc] ζ) (𝓝 (h ζ))

/-- `S = λ + c` of (7.4) `eq:morse-constants`. -/
def morseS (lam c : ℝ) : ℝ := lam + c

/-- `a₁ = λ S` of (7.4). -/
def morseA1 (lam c : ℝ) : ℝ := lam * morseS lam c

/-- `b₁ = λ S (2S + c)` of (7.4). -/
def morseB1 (lam c : ℝ) : ℝ := lam * morseS lam c * (2 * morseS lam c + c)

/-- `r_* = arcosh(2 a₁)` of (7.4). -/
def morseR (lam c : ℝ) : ℝ := Real.arcosh (2 * morseA1 lam c)

/-- `M_* = (2a₁ + 1) r_* + b₁` of (7.4). -/
def morseM (lam c : ℝ) : ℝ := (2 * morseA1 lam c + 1) * morseR lam c + morseB1 lam c

/-- `D_*(λ, c) = arsinh(√2 sinh M_*)` (`sec07-transfer.tex:153`). -/
def morseD (lam c : ℝ) : ℝ := Real.arsinh (Real.sqrt 2 * Real.sinh (morseM lam c))

/-- Morse M1 (coordinates): `⟨X, Y⟩ = -X₀Y₀ + Re X' Re Y' + Im X' Im Y'`. -/
theorem s07_mo_Bc (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) (X Y : ℝ × ℂ) :
    B X Y = -X.1 * Y.1 + X.2.re * Y.2.re + X.2.im * Y.2.im := by
  rw [hB, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- `1 ≤ cosh d_𝔻(p, q)` on `𝔻`. -/
theorem s07_mo_one_le_coshDist {p q : ℂ} (hp : p ∈ unitDisc) (hq : q ∈ unitDisc) :
    1 ≤ diskCoshDist p q := by
  have hp1 : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
  have hq1 : ‖q‖ < 1 := mem_ball_zero_iff.mp hq
  have h1 : 0 < 1 - ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
  have h2 : 0 < 1 - ‖q‖ ^ 2 := by nlinarith [norm_nonneg q]
  unfold diskCoshDist
  have : 0 ≤ 2 * ‖p - q‖ ^ 2 / ((1 - ‖p‖ ^ 2) * (1 - ‖q‖ ^ 2)) :=
    div_nonneg (by positivity) (mul_pos h1 h2).le
  linarith

/-- `cosh d_𝔻(p, q) = diskCoshDist p q` on `𝔻`. -/
theorem s07_mo_cosh_dist {p q : ℂ} (hp : p ∈ unitDisc) (hq : q ∈ unitDisc) :
    Real.cosh (diskDist p q) = diskCoshDist p q :=
  Real.cosh_arcosh (s07_mo_one_le_coshDist hp hq)

/-- `cosh x = 1 + 2 sinh² (x/2)`. -/
theorem s07_mo_cosh_half (x : ℝ) : Real.cosh x = 1 + 2 * Real.sinh (x / 2) ^ 2 := by
  have h := Real.cosh_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring, Real.cosh_sq] at h
  linarith

/-- Morse M1: `P` maps `𝔻` into the upper sheet `⟨X, X⟩ = -1, X₀ > 0`, and
`cosh d_𝔻(p, q) = -⟨P p, P q⟩`. -/
theorem s07_mo_hyp (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) (P : ℂ → ℝ × ℂ)
    (hP : ∀ p, P p = ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p))
    {p : ℂ} (hp : p ∈ unitDisc) :
    B (P p) (P p) = -1 ∧ 0 < (P p).1 ∧ ∀ q ∈ unitDisc, diskCoshDist p q = -B (P p) (P q) := by
  have hBc := s07_mo_Bc B hB
  have hp1 : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
  have hpn : 0 < 1 - ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
  have key : ∀ q ∈ unitDisc, diskCoshDist p q = -B (P p) (P q) := by
    intro q hq
    have hq1 : ‖q‖ < 1 := mem_ball_zero_iff.mp hq
    have hqn : 0 < 1 - ‖q‖ ^ 2 := by nlinarith [norm_nonneg q]
    have hsub : ‖p - q‖ ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 - 2 * (p * conj q).re := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
    have hre : ((((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p) *
        conj (((2 / (1 - ‖q‖ ^ 2) : ℝ) : ℂ) * q)).re =
        (2 / (1 - ‖p‖ ^ 2)) * (2 / (1 - ‖q‖ ^ 2)) * (p * conj q).re := by
      rw [map_mul, Complex.conj_ofReal,
        show (((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p) * (((2 / (1 - ‖q‖ ^ 2) : ℝ) : ℂ) * conj q) =
          (((2 / (1 - ‖p‖ ^ 2)) * (2 / (1 - ‖q‖ ^ 2)) : ℝ) : ℂ) * (p * conj q) by push_cast; ring,
        Complex.re_ofReal_mul]
    rw [hB, hP p, hP q]
    dsimp only
    rw [hre]
    unfold diskCoshDist
    rw [hsub]
    have hpn' := hpn.ne'
    have hqn' := hqn.ne'
    generalize ‖p‖ ^ 2 = n at hpn' ⊢
    generalize ‖q‖ ^ 2 = m at hqn' ⊢
    generalize (p * conj q).re = r
    field_simp
    ring
  have hpp : diskCoshDist p p = 1 := by
    unfold diskCoshDist
    simp
  refine ⟨?_, ?_, key⟩
  · have := key p hp
    rw [hpp] at this
    linarith
  · rw [hP p]
    exact div_pos (by positivity) hpn

/-- Morse M1: every point `X` of the upper sheet is `P p` for `p = X'/(1 + X₀) ∈ 𝔻`. -/
theorem s07_mo_hyp_inv (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) (P : ℂ → ℝ × ℂ)
    (hP : ∀ p, P p = ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p))
    {X : ℝ × ℂ} (hX : B X X = -1) (hX0 : 0 < X.1) :
    X.2 / ((1 + X.1 : ℝ) : ℂ) ∈ unitDisc ∧ P (X.2 / ((1 + X.1 : ℝ) : ℂ)) = X := by
  have hBc := s07_mo_Bc B hB
  have hw : ‖X.2‖ ^ 2 = X.1 ^ 2 - 1 := by
    have h := hBc X X
    rw [hX] at h
    rw [Complex.sq_norm, Complex.normSq_apply]
    linear_combination (-1 : ℝ) * h
  have hk : 0 < 1 + X.1 := by linarith
  have hk' : 1 + X.1 ≠ 0 := hk.ne'
  have hnorm : ‖X.2 / ((1 + X.1 : ℝ) : ℂ)‖ ^ 2 = (X.1 - 1) / (1 + X.1) := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hk.le, div_pow, hw]
    field_simp
    ring
  have hlt : ‖X.2 / ((1 + X.1 : ℝ) : ℂ)‖ ^ 2 < 1 := by
    rw [hnorm, div_lt_one hk]
    linarith
  refine ⟨mem_ball_zero_iff.mpr (by nlinarith [norm_nonneg (X.2 / ((1 + X.1 : ℝ) : ℂ))]), ?_⟩
  rw [hP, hnorm]
  have h1 : (2 / (1 - (X.1 - 1) / (1 + X.1)) : ℝ) = 1 + X.1 := by
    field_simp
    ring
  have h2 : (1 + (X.1 - 1) / (1 + X.1)) / (1 - (X.1 - 1) / (1 + X.1)) = X.1 := by
    field_simp
    ring
  rw [h1, h2]
  have hkc : ((1 + X.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk'
  refine Prod.ext rfl ?_
  dsimp only
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hkc]

/-- Cramer's rule for a `3 × 3` homogeneous system with nonzero determinant. -/
theorem s07_mo_cramer3 {p0 p1 p2 q0 q1 q2 r0 r1 r2 z0 z1 z2 : ℝ}
    (hdet : p0 * (q1 * r2 - q2 * r1) - p1 * (q0 * r2 - q2 * r0) + p2 * (q0 * r1 - q1 * r0) ≠ 0)
    (hp : p0 * z0 + p1 * z1 + p2 * z2 = 0) (hq : q0 * z0 + q1 * z1 + q2 * z2 = 0)
    (hr : r0 * z0 + r1 * z1 + r2 * z2 = 0) : z0 = 0 ∧ z1 = 0 ∧ z2 = 0 := by
  have e0 : z0 * (p0 * (q1 * r2 - q2 * r1) - p1 * (q0 * r2 - q2 * r0) +
      p2 * (q0 * r1 - q1 * r0)) = 0 := by
    linear_combination (q1 * r2 - q2 * r1) * hp + (r1 * p2 - r2 * p1) * hq +
      (p1 * q2 - p2 * q1) * hr
  have e1 : z1 * (p0 * (q1 * r2 - q2 * r1) - p1 * (q0 * r2 - q2 * r0) +
      p2 * (q0 * r1 - q1 * r0)) = 0 := by
    linear_combination (q2 * r0 - q0 * r2) * hp + (r2 * p0 - r0 * p2) * hq +
      (p2 * q0 - p0 * q2) * hr
  have e2 : z2 * (p0 * (q1 * r2 - q2 * r1) - p1 * (q0 * r2 - q2 * r0) +
      p2 * (q0 * r1 - q1 * r0)) = 0 := by
    linear_combination (q0 * r1 - q1 * r0) * hp + (r0 * p1 - r1 * p0) * hq +
      (p0 * q1 - p1 * q0) * hr
  exact ⟨(mul_eq_zero.mp e0).resolve_right hdet, (mul_eq_zero.mp e1).resolve_right hdet,
    (mul_eq_zero.mp e2).resolve_right hdet⟩

/-- Parseval for a Lorentz-orthonormal frame, in coordinates. -/
theorem s07_mo_parseval_real {u0 u1 u2 v0 v1 v2 w0 w1 w2 : ℝ}
    (huu : -u0 * u0 + u1 * u1 + u2 * u2 = -1) (hvv : -v0 * v0 + v1 * v1 + v2 * v2 = 1)
    (hww : -w0 * w0 + w1 * w1 + w2 * w2 = 1) (huv : -u0 * v0 + u1 * v1 + u2 * v2 = 0)
    (huw : -u0 * w0 + u1 * w1 + u2 * w2 = 0) (hvw : -v0 * w0 + v1 * w1 + v2 * w2 = 0)
    (x0 x1 x2 y0 y1 y2 : ℝ) :
    -x0 * y0 + x1 * y1 + x2 * y2 =
      -((-x0 * u0 + x1 * u1 + x2 * u2) * (-y0 * u0 + y1 * u1 + y2 * u2)) +
        (-x0 * v0 + x1 * v1 + x2 * v2) * (-y0 * v0 + y1 * v1 + y2 * v2) +
        (-x0 * w0 + x1 * w1 + x2 * w2) * (-y0 * w0 + y1 * w1 + y2 * w2) := by
  have key : (-u0 * u0 + u1 * u1 + u2 * u2) * (-v0 * v0 + v1 * v1 + v2 * v2) *
        (-w0 * w0 + w1 * w1 + w2 * w2) +
      2 * (-u0 * v0 + u1 * v1 + u2 * v2) * (-u0 * w0 + u1 * w1 + u2 * w2) *
        (-v0 * w0 + v1 * w1 + v2 * w2) -
      (-u0 * u0 + u1 * u1 + u2 * u2) * (-v0 * w0 + v1 * w1 + v2 * w2) ^ 2 -
      (-v0 * v0 + v1 * v1 + v2 * v2) * (-u0 * w0 + u1 * w1 + u2 * w2) ^ 2 -
      (-w0 * w0 + w1 * w1 + w2 * w2) * (-u0 * v0 + u1 * v1 + u2 * v2) ^ 2 =
      -((-u0) * (v1 * w2 - v2 * w1) - u1 * ((-v0) * w2 - v2 * (-w0)) +
        u2 * ((-v0) * w1 - v1 * (-w0))) ^ 2 := by ring
  rw [huu, hvv, hww, huv, huw, hvw] at key
  have hD : (-u0) * (v1 * w2 - v2 * w1) - u1 * ((-v0) * w2 - v2 * (-w0)) +
      u2 * ((-v0) * w1 - v1 * (-w0)) ≠ 0 := by
    intro h
    rw [h] at key
    norm_num at key
  have hp : (-u0) * (x0 - (-(-x0 * u0 + x1 * u1 + x2 * u2) * u0 +
        (-x0 * v0 + x1 * v1 + x2 * v2) * v0 + (-x0 * w0 + x1 * w1 + x2 * w2) * w0)) +
      u1 * (x1 - (-(-x0 * u0 + x1 * u1 + x2 * u2) * u1 +
        (-x0 * v0 + x1 * v1 + x2 * v2) * v1 + (-x0 * w0 + x1 * w1 + x2 * w2) * w1)) +
      u2 * (x2 - (-(-x0 * u0 + x1 * u1 + x2 * u2) * u2 +
        (-x0 * v0 + x1 * v1 + x2 * v2) * v2 + (-x0 * w0 + x1 * w1 + x2 * w2) * w2)) = 0 := by
    linear_combination (-x0 * u0 + x1 * u1 + x2 * u2) * huu -
      (-x0 * v0 + x1 * v1 + x2 * v2) * huv - (-x0 * w0 + x1 * w1 + x2 * w2) * huw
  have hq : (-v0) * (x0 - (-(-x0 * u0 + x1 * u1 + x2 * u2) * u0 +
        (-x0 * v0 + x1 * v1 + x2 * v2) * v0 + (-x0 * w0 + x1 * w1 + x2 * w2) * w0)) +
      v1 * (x1 - (-(-x0 * u0 + x1 * u1 + x2 * u2) * u1 +
        (-x0 * v0 + x1 * v1 + x2 * v2) * v1 + (-x0 * w0 + x1 * w1 + x2 * w2) * w1)) +
      v2 * (x2 - (-(-x0 * u0 + x1 * u1 + x2 * u2) * u2 +
        (-x0 * v0 + x1 * v1 + x2 * v2) * v2 + (-x0 * w0 + x1 * w1 + x2 * w2) * w2)) = 0 := by
    linear_combination (-x0 * u0 + x1 * u1 + x2 * u2) * huv -
      (-x0 * v0 + x1 * v1 + x2 * v2) * hvv - (-x0 * w0 + x1 * w1 + x2 * w2) * hvw
  have hr : (-w0) * (x0 - (-(-x0 * u0 + x1 * u1 + x2 * u2) * u0 +
        (-x0 * v0 + x1 * v1 + x2 * v2) * v0 + (-x0 * w0 + x1 * w1 + x2 * w2) * w0)) +
      w1 * (x1 - (-(-x0 * u0 + x1 * u1 + x2 * u2) * u1 +
        (-x0 * v0 + x1 * v1 + x2 * v2) * v1 + (-x0 * w0 + x1 * w1 + x2 * w2) * w1)) +
      w2 * (x2 - (-(-x0 * u0 + x1 * u1 + x2 * u2) * u2 +
        (-x0 * v0 + x1 * v1 + x2 * v2) * v2 + (-x0 * w0 + x1 * w1 + x2 * w2) * w2)) = 0 := by
    linear_combination (-x0 * u0 + x1 * u1 + x2 * u2) * huw -
      (-x0 * v0 + x1 * v1 + x2 * v2) * hvw - (-x0 * w0 + x1 * w1 + x2 * w2) * hww
  obtain ⟨hz0, hz1, hz2⟩ := s07_mo_cramer3 hD hp hq hr
  linear_combination (-y0) * hz0 + y1 * hz1 + y2 * hz2

/-- Morse M1: Parseval for a Lorentz-orthonormal frame `(e₀, e₁, e₂)`:
`⟨X, Y⟩ = -⟨X, e₀⟩⟨Y, e₀⟩ + ⟨X, e₁⟩⟨Y, e₁⟩ + ⟨X, e₂⟩⟨Y, e₂⟩`. -/
theorem s07_mo_parseval (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) {e₀ e₁ e₂ : ℝ × ℂ}
    (hon : B e₀ e₀ = -1 ∧ B e₁ e₁ = 1 ∧ B e₂ e₂ = 1 ∧ B e₀ e₁ = 0 ∧ B e₀ e₂ = 0 ∧ B e₁ e₂ = 0)
    (X Y : ℝ × ℂ) :
    B X Y = -(B X e₀ * B Y e₀) + B X e₁ * B Y e₁ + B X e₂ * B Y e₂ := by
  have hBc := s07_mo_Bc B hB
  obtain ⟨h00, h11, h22, h01, h02, h12⟩ := hon
  rw [hBc] at h00 h11 h22 h01 h02 h12
  simp only [hBc]
  exact s07_mo_parseval_real h00 h11 h22 h01 h02 h12 _ _ _ _ _ _

/-- Frame from two points `X, Y` of the upper sheet with `⟨X, Y⟩ = -c`, `c² = s² + 1`, `s > 0`. -/
theorem s07_mo_frame_vec (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) {X Y : ℝ × ℂ} {c s : ℝ}
    (hXX : B X X = -1) (hYY : B Y Y = -1) (hXY : B X Y = -c) (hcs : c ^ 2 = s ^ 2 + 1)
    (hs : 0 < s) :
    ∃ e₁ e₂ : ℝ × ℂ, (B X X = -1 ∧ B e₁ e₁ = 1 ∧ B e₂ e₂ = 1 ∧ B X e₁ = 0 ∧ B X e₂ = 0 ∧
      B e₁ e₂ = 0) ∧ Y = c • X + s • e₁ := by
  have hBc := s07_mo_Bc B hB
  obtain ⟨E, hE⟩ : ∃ E : ℝ × ℂ, E = s⁻¹ • (Y - c • X) := ⟨_, rfl⟩
  have hYE : Y = c • X + s • E := by
    rw [hE, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    abel
  have hE1 : E.1 = s⁻¹ * (Y.1 - c * X.1) := by rw [hE]; simp
  have hE2 : E.2.re = s⁻¹ * (Y.2.re - c * X.2.re) := by rw [hE]; simp
  have hE3 : E.2.im = s⁻¹ * (Y.2.im - c * X.2.im) := by rw [hE]; simp
  have hXXc := hXX
  rw [hBc] at hXXc hYY hXY
  have hEEc : -E.1 * E.1 + E.2.re * E.2.re + E.2.im * E.2.im = 1 := by
    have hq : -(Y.1 - c * X.1) * (Y.1 - c * X.1) + (Y.2.re - c * X.2.re) * (Y.2.re - c * X.2.re) +
        (Y.2.im - c * X.2.im) * (Y.2.im - c * X.2.im) = s ^ 2 := by
      linear_combination hYY - 2 * c * hXY + c ^ 2 * hXXc + hcs
    rw [hE1, hE2, hE3]
    calc _ = (s⁻¹) ^ 2 * (-(Y.1 - c * X.1) * (Y.1 - c * X.1) +
          (Y.2.re - c * X.2.re) * (Y.2.re - c * X.2.re) +
          (Y.2.im - c * X.2.im) * (Y.2.im - c * X.2.im)) := by ring
      _ = 1 := by rw [hq]; field_simp
  have hXEc : -X.1 * E.1 + X.2.re * E.2.re + X.2.im * E.2.im = 0 := by
    have hq : -X.1 * (Y.1 - c * X.1) + X.2.re * (Y.2.re - c * X.2.re) +
        X.2.im * (Y.2.im - c * X.2.im) = 0 := by
      linear_combination hXY - c * hXXc
    rw [hE1, hE2, hE3]
    calc _ = s⁻¹ * (-X.1 * (Y.1 - c * X.1) + X.2.re * (Y.2.re - c * X.2.re) +
          X.2.im * (Y.2.im - c * X.2.im)) := by ring
      _ = 0 := by rw [hq]; ring
  refine ⟨E, (-(X.2.re * E.2.im - X.2.im * E.2.re),
    ⟨X.2.im * E.1 - X.1 * E.2.im, X.1 * E.2.re - X.2.re * E.1⟩), ⟨hXX, ?_, ?_, ?_, ?_, ?_⟩, hYE⟩
  · rw [hBc]; exact hEEc
  · rw [hBc]
    dsimp only
    linear_combination (-X.1 * E.1 + X.2.re * E.2.re + X.2.im * E.2.im) * hXEc -
      (-E.1 * E.1 + E.2.re * E.2.re + E.2.im * E.2.im) * hXXc + hEEc
  · rw [hBc]; exact hXEc
  · rw [hBc]
    dsimp only
    ring
  · rw [hBc]
    dsimp only
    ring

/-- Morse M1: for `a ≠ b` in `𝔻` there is an orthonormal frame `(P a, e₁, e₂)` with
`P b = cosh d(a, b) P a + sinh d(a, b) e₁` (the geodesic through `a`, `b` is the `(e₀, e₁)`-plane). -/
theorem s07_mo_frame (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) (P : ℂ → ℝ × ℂ)
    (hP : ∀ p, P p = ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p))
    {a b : ℂ} (ha : a ∈ unitDisc) (hb : b ∈ unitDisc) (hab : a ≠ b) :
    ∃ e₁ e₂ : ℝ × ℂ, (B (P a) (P a) = -1 ∧ B e₁ e₁ = 1 ∧ B e₂ e₂ = 1 ∧ B (P a) e₁ = 0 ∧
      B (P a) e₂ = 0 ∧ B e₁ e₂ = 0) ∧
      P b = Real.cosh (diskDist a b) • P a + Real.sinh (diskDist a b) • e₁ := by
  obtain ⟨hPa, -, hda⟩ := s07_mo_hyp B hB P hP ha
  obtain ⟨hPb, -, -⟩ := s07_mo_hyp B hB P hP hb
  have hc1 : 1 < diskCoshDist a b := by
    have hp1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
    have hq1 : ‖b‖ < 1 := mem_ball_zero_iff.mp hb
    have h1 : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
    have h2 : 0 < 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
    have hn : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
    unfold diskCoshDist
    have : 0 < 2 * ‖a - b‖ ^ 2 / ((1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2)) :=
      div_pos (by positivity) (mul_pos h1 h2)
    linarith
  have hd : 0 < diskDist a b := Real.arcosh_pos hc1
  have hcosh := s07_mo_cosh_dist ha hb
  exact s07_mo_frame_vec B hB hPa hPb (by rw [hcosh]; linarith [hda b hb]) (Real.cosh_sq _)
    (Real.sinh_pos_iff.mpr hd)

/-- Two points of the upper sheet have `⟨X, Y⟩ < 0`. -/
theorem s07_mo_sheet_neg (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) {X Y : ℝ × ℂ} (hX : B X X = -1)
    (hX0 : 0 < X.1) (hY : B Y Y = -1) (hY0 : 0 < Y.1) : B X Y < 0 := by
  have hBc := s07_mo_Bc B hB
  rw [hBc] at hX hY ⊢
  have hx : X.1 ^ 2 - 1 = X.2.re ^ 2 + X.2.im ^ 2 := by linear_combination (-1 : ℝ) * hX
  have hy : Y.1 ^ 2 - 1 = Y.2.re ^ 2 + Y.2.im ^ 2 := by linear_combination (-1 : ℝ) * hY
  have hcs : (X.2.re * Y.2.re + X.2.im * Y.2.im) ^ 2 ≤ (X.1 ^ 2 - 1) * (Y.1 ^ 2 - 1) := by
    rw [hx, hy]
    nlinarith [sq_nonneg (X.2.re * Y.2.im - X.2.im * Y.2.re)]
  have hx1 : 1 ≤ X.1 ^ 2 := by nlinarith [sq_nonneg X.2.re, sq_nonneg X.2.im]
  have hy1 : 1 ≤ Y.1 ^ 2 := by nlinarith [sq_nonneg Y.2.re, sq_nonneg Y.2.im]
  have hlt : (X.2.re * Y.2.re + X.2.im * Y.2.im) ^ 2 < (X.1 * Y.1) ^ 2 := by nlinarith
  have hP : 0 < X.1 * Y.1 := mul_pos hX0 hY0
  by_contra hcon
  push_neg at hcon
  have h1 : X.1 * Y.1 ≤ X.2.re * Y.2.re + X.2.im * Y.2.im := by linarith
  nlinarith [mul_le_mul h1 h1 hP.le (by linarith)]

/-- Morse M1: Fermi coordinates relative to the geodesic of a frame `(e₀, e₁, e₂)` (`e₀` in the
upper sheet): with `ρ = arsinh ⟨P ·, e₂⟩` (signed distance) and `υ = arsinh(⟨P ·, e₁⟩ / cosh ρ)`
(arclength of the projection), `cosh d = cosh ρ_p cosh ρ_q cosh(υ_p - υ_q) - sinh ρ_p sinh ρ_q`
(`eq:fermi-2d`). -/
theorem s07_mo_fermi (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) (P : ℂ → ℝ × ℂ)
    (hP : ∀ p, P p = ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p))
    {e₀ e₁ e₂ : ℝ × ℂ}
    (hon : B e₀ e₀ = -1 ∧ B e₁ e₁ = 1 ∧ B e₂ e₂ = 1 ∧ B e₀ e₁ = 0 ∧ B e₀ e₂ = 0 ∧ B e₁ e₂ = 0)
    (he₀ : 0 < e₀.1) (ρ υ : ℂ → ℝ) (hρ : ∀ p, ρ p = Real.arsinh (B (P p) e₂))
    (hυ : ∀ p, υ p = Real.arsinh (B (P p) e₁ / Real.cosh (ρ p))) {p q : ℂ} (hp : p ∈ unitDisc)
    (hq : q ∈ unitDisc) :
    diskCoshDist p q = Real.cosh (ρ p) * Real.cosh (ρ q) * Real.cosh (υ p - υ q) -
      Real.sinh (ρ p) * Real.sinh (ρ q) := by
  have hcoord : ∀ z ∈ unitDisc, -B (P z) e₀ = Real.cosh (ρ z) * Real.cosh (υ z) ∧
      B (P z) e₁ = Real.cosh (ρ z) * Real.sinh (υ z) ∧ B (P z) e₂ = Real.sinh (ρ z) := by
    intro z hz
    obtain ⟨hzz, hz0, -⟩ := s07_mo_hyp B hB P hP hz
    have hpar := s07_mo_parseval B hB hon (P z) (P z)
    rw [hzz] at hpar
    have hneg : B (P z) e₀ < 0 := s07_mo_sheet_neg B hB hzz hz0 hon.1 he₀
    have hs2 : Real.sinh (ρ z) = B (P z) e₂ := by rw [hρ, Real.sinh_arsinh]
    have hcρ : 0 < Real.cosh (ρ z) := Real.cosh_pos _
    have hs1 : Real.sinh (υ z) = B (P z) e₁ / Real.cosh (ρ z) := by rw [hυ, Real.sinh_arsinh]
    have hCs : Real.cosh (ρ z) * Real.sinh (υ z) = B (P z) e₁ := by
      rw [hs1]
      field_simp
    have e1 := Real.cosh_sq (ρ z)
    have e2 := Real.cosh_sq (υ z)
    have h1 : (Real.cosh (ρ z) * Real.cosh (υ z)) ^ 2 = (-B (P z) e₀) ^ 2 := by
      linear_combination Real.cosh (ρ z) ^ 2 * e2 +
        (Real.cosh (ρ z) * Real.sinh (υ z) + B (P z) e₁) * hCs + e1 +
        (Real.sinh (ρ z) + B (P z) e₂) * hs2 - hpar
    have hc1 : Real.cosh (ρ z) * Real.cosh (υ z) = -B (P z) e₀ :=
      (pow_left_inj₀ (mul_pos hcρ (Real.cosh_pos _)).le (by linarith) two_ne_zero).mp h1
    exact ⟨hc1.symm, hCs.symm, hs2.symm⟩
  obtain ⟨hpd, -, hpdist⟩ := s07_mo_hyp B hB P hP hp
  obtain ⟨a0, a1, a2⟩ := hcoord p hp
  obtain ⟨b0, b1, b2⟩ := hcoord q hq
  rw [hpdist q hq, s07_mo_parseval B hB hon (P p) (P q), Real.cosh_sub]
  linear_combination (-B (P q) e₀) * a0 + (Real.cosh (ρ p) * Real.cosh (υ p)) * b0 -
    B (P q) e₁ * a1 - (Real.cosh (ρ p) * Real.sinh (υ p)) * b1 - B (P q) e₂ * a2 -
    Real.sinh (ρ p) * b2

/-- Fermi coordinates: `cosh d = cosh(ρ_p - ρ_q) + 2 cosh ρ_p cosh ρ_q sinh²((υ_p - υ_q)/2)`. -/
theorem s07_mo_fermi_expand (ρ υ : ℂ → ℝ)
    (hF : ∀ p ∈ unitDisc, ∀ q ∈ unitDisc, diskCoshDist p q = Real.cosh (ρ p) * Real.cosh (ρ q) *
      Real.cosh (υ p - υ q) - Real.sinh (ρ p) * Real.sinh (ρ q))
    {p q : ℂ} (hp : p ∈ unitDisc) (hq : q ∈ unitDisc) :
    Real.cosh (diskDist p q) = Real.cosh (ρ p - ρ q) +
      2 * Real.cosh (ρ p) * Real.cosh (ρ q) * Real.sinh ((υ p - υ q) / 2) ^ 2 := by
  rw [s07_mo_cosh_dist hp hq, hF p hp q hq, s07_mo_cosh_half (υ p - υ q), Real.cosh_sub]
  ring

/-- Morse M1 (projection estimate): if `|ρ_p|, |ρ_q| ≥ r ≥ 0` then
`cosh r · sinh(|υ_p - υ_q|/2) ≤ sinh(d(p, q)/2)`. -/
theorem s07_mo_fermi_proj (ρ υ : ℂ → ℝ)
    (hF : ∀ p ∈ unitDisc, ∀ q ∈ unitDisc, diskCoshDist p q = Real.cosh (ρ p) * Real.cosh (ρ q) *
      Real.cosh (υ p - υ q) - Real.sinh (ρ p) * Real.sinh (ρ q))
    {p q : ℂ} (hp : p ∈ unitDisc) (hq : q ∈ unitDisc) {r : ℝ} (hr : 0 ≤ r) (hrp : r ≤ |ρ p|)
    (hrq : r ≤ |ρ q|) :
    Real.cosh r * Real.sinh (|υ p - υ q| / 2) ≤ Real.sinh (diskDist p q / 2) := by
  have hexp := s07_mo_fermi_expand ρ υ hF hp hq
  rw [s07_mo_cosh_half (diskDist p q)] at hexp
  have hcp : Real.cosh r ≤ Real.cosh (ρ p) := Real.cosh_le_cosh.mpr (by rwa [abs_of_nonneg hr])
  have hcq : Real.cosh r ≤ Real.cosh (ρ q) := Real.cosh_le_cosh.mpr (by rwa [abs_of_nonneg hr])
  have hc1 := Real.one_le_cosh (ρ p - ρ q)
  have hcr := Real.cosh_pos r
  have habs : Real.sinh (|υ p - υ q| / 2) ^ 2 = Real.sinh ((υ p - υ q) / 2) ^ 2 := by
    rw [show |υ p - υ q| / 2 = |(υ p - υ q) / 2| by rw [abs_div, abs_two], ← Real.abs_sinh,
      sq_abs]
  have hsn : 0 ≤ Real.sinh ((υ p - υ q) / 2) ^ 2 := sq_nonneg _
  have hcc : Real.cosh r ^ 2 ≤ Real.cosh (ρ p) * Real.cosh (ρ q) := by
    rw [sq]; exact mul_le_mul hcp hcq hcr.le (by linarith)
  have hl : 0 ≤ Real.cosh r * Real.sinh (|υ p - υ q| / 2) :=
    mul_nonneg hcr.le (Real.sinh_nonneg_iff.mpr (by positivity))
  have hrr : 0 ≤ Real.sinh (diskDist p q / 2) :=
    Real.sinh_nonneg_iff.mpr (by linarith [s02_diskDist_nonneg hp hq])
  refine (pow_le_pow_iff_left₀ hl hrr two_ne_zero).mp ?_
  rw [mul_pow, habs]
  nlinarith [mul_le_mul_of_nonneg_right hcc hsn]

/-- Morse M1 (path through the projections): `d(p, q) ≤ |ρ_p| + |υ_p - υ_q| + |ρ_q|`. -/
theorem s07_mo_fermi_tri (ρ υ : ℂ → ℝ)
    (hF : ∀ p ∈ unitDisc, ∀ q ∈ unitDisc, diskCoshDist p q = Real.cosh (ρ p) * Real.cosh (ρ q) *
      Real.cosh (υ p - υ q) - Real.sinh (ρ p) * Real.sinh (ρ q))
    {p q : ℂ} (hp : p ∈ unitDisc) (hq : q ∈ unitDisc) :
    diskDist p q ≤ |ρ p| + |υ p - υ q| + |ρ q| := by
  have hd := hF p hp q hq
  rw [← s07_mo_cosh_dist hp hq] at hd
  have hsa : 0 ≤ Real.sinh |ρ p| := Real.sinh_nonneg_iff.mpr (abs_nonneg _)
  have hsb : 0 ≤ Real.sinh |υ p - υ q| := Real.sinh_nonneg_iff.mpr (abs_nonneg _)
  have hsc : 0 ≤ Real.sinh |ρ q| := Real.sinh_nonneg_iff.mpr (abs_nonneg _)
  have hsac : 0 ≤ Real.sinh (|ρ p| + |ρ q|) :=
    Real.sinh_nonneg_iff.mpr (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hS : -(Real.sinh (ρ p) * Real.sinh (ρ q)) ≤ Real.sinh |ρ p| * Real.sinh |ρ q| := by
    rw [← Real.abs_sinh, ← Real.abs_sinh, ← abs_mul]
    exact neg_le_abs _
  have hsum : Real.cosh (|ρ p| + |υ p - υ q| + |ρ q|) =
      (Real.cosh |ρ p| * Real.cosh |ρ q| + Real.sinh |ρ p| * Real.sinh |ρ q|) *
        Real.cosh |υ p - υ q| + Real.sinh (|ρ p| + |ρ q|) * Real.sinh |υ p - υ q| := by
    rw [show |ρ p| + |υ p - υ q| + |ρ q| = (|ρ p| + |ρ q|) + |υ p - υ q| by ring, Real.cosh_add,
      Real.cosh_add]
  have hb1 := Real.one_le_cosh (υ p - υ q)
  have hle : Real.cosh (diskDist p q) ≤ Real.cosh (|ρ p| + |υ p - υ q| + |ρ q|) := by
    rw [hd, hsum, Real.cosh_abs, Real.cosh_abs, Real.cosh_abs]
    nlinarith [mul_nonneg hsac hsb, mul_nonneg hsa hsc,
      mul_le_mul_of_nonneg_left hb1 (mul_nonneg hsa hsc)]
  have h := Real.cosh_le_cosh.mp hle
  rw [abs_of_nonneg (s02_diskDist_nonneg hp hq), abs_of_nonneg (by positivity)] at h
  exact h

/-- Morse M1: the signed distance `ρ` to the geodesic is `1`-Lipschitz. -/
theorem s07_mo_fermi_lip (ρ υ : ℂ → ℝ)
    (hF : ∀ p ∈ unitDisc, ∀ q ∈ unitDisc, diskCoshDist p q = Real.cosh (ρ p) * Real.cosh (ρ q) *
      Real.cosh (υ p - υ q) - Real.sinh (ρ p) * Real.sinh (ρ q))
    {p q : ℂ} (hp : p ∈ unitDisc) (hq : q ∈ unitDisc) :
    |ρ p - ρ q| ≤ diskDist p q := by
  have hexp := s07_mo_fermi_expand ρ υ hF hp hq
  have hle : Real.cosh (ρ p - ρ q) ≤ Real.cosh (diskDist p q) := by
    rw [hexp]
    have := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (Real.cosh_pos (ρ p)).le) (Real.cosh_pos (ρ q)).le) (sq_nonneg (Real.sinh ((υ p - υ q) / 2)))
    linarith
  have h := Real.cosh_le_cosh.mp hle
  rwa [abs_of_nonneg (s02_diskDist_nonneg hp hq)] at h

/-- `⟨c U + s V, W⟩ = c ⟨U, W⟩ + s ⟨V, W⟩`. -/
theorem s07_mo_B_comb (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) (c s : ℝ) (U V W : ℝ × ℂ) :
    B (c • U + s • V) W = c * B U W + s * B V W := by
  simp only [s07_mo_Bc B hB, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

/-- `⟨·, ·⟩` is symmetric. -/
theorem s07_mo_B_symm (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) (U V : ℝ × ℂ) : B U V = B V U := by
  rw [s07_mo_Bc B hB, s07_mo_Bc B hB]
  ring

/-- `⟨W, c U + s V⟩ = c ⟨W, U⟩ + s ⟨W, V⟩`. -/
theorem s07_mo_B_combr (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) (c s : ℝ) (U V W : ℝ × ℂ) :
    B W (c • U + s • V) = c * B W U + s * B W V := by
  rw [s07_mo_B_symm B hB, s07_mo_B_comb B hB, s07_mo_B_symm B hB U, s07_mo_B_symm B hB V]

/-- For an orthonormal frame with `e₀` in the upper sheet, `e₁,₀² ≤ e₀,₀² - 1`. -/
theorem s07_mo_time (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) {e₀ e₁ e₂ : ℝ × ℂ}
    (hon : B e₀ e₀ = -1 ∧ B e₁ e₁ = 1 ∧ B e₂ e₂ = 1 ∧ B e₀ e₁ = 0 ∧ B e₀ e₂ = 0 ∧ B e₁ e₂ = 0) :
    e₁.1 ^ 2 ≤ e₀.1 ^ 2 - 1 := by
  have hBc := s07_mo_Bc B hB
  obtain ⟨h00, h11, -, h01, -, -⟩ := hon
  rw [hBc] at h00 h11 h01
  have hx : e₀.1 ^ 2 - 1 = e₀.2.re ^ 2 + e₀.2.im ^ 2 := by linear_combination (-1 : ℝ) * h00
  have hy : 1 + e₁.1 ^ 2 = e₁.2.re ^ 2 + e₁.2.im ^ 2 := by linear_combination (-1 : ℝ) * h11
  have hd : e₀.1 * e₁.1 = e₀.2.re * e₁.2.re + e₀.2.im * e₁.2.im := by
    linear_combination (-1 : ℝ) * h01
  have hcs : (e₀.1 * e₁.1) ^ 2 ≤ (e₀.1 ^ 2 - 1) * (1 + e₁.1 ^ 2) := by
    rw [hd, hx, hy]
    nlinarith [sq_nonneg (e₀.2.re * e₁.2.im - e₀.2.im * e₁.2.re)]
  nlinarith [hcs]

/-- The `P`-preimage of a point of `𝔻`: `(P p)' / (1 + (P p)₀) = p`. -/
theorem s07_mo_P_left_inv (P : ℂ → ℝ × ℂ)
    (hP : ∀ p, P p = ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p))
    {p : ℂ} (hp : p ∈ unitDisc) : (P p).2 / ((1 + (P p).1 : ℝ) : ℂ) = p := by
  have hp1 : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
  have hpn : 0 < 1 - ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
  rw [hP]
  dsimp only
  have h1 : 1 + (1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2) = 2 / (1 - ‖p‖ ^ 2) := by
    field_simp
    ring
  rw [h1]
  have h2 : ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (div_pos two_pos hpn).ne'
  rw [mul_div_cancel_left₀ _ h2]

/-- `P` is injective on `𝔻`. -/
theorem s07_mo_P_inj (P : ℂ → ℝ × ℂ)
    (hP : ∀ p, P p = ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p))
    {p q : ℂ} (hp : p ∈ unitDisc) (hq : q ∈ unitDisc) (h : P p = P q) : p = q := by
  rw [← s07_mo_P_left_inv P hP hp, ← s07_mo_P_left_inv P hP hq, h]

/-- The unit-speed geodesic `γ(t) = P⁻¹(cosh t e₀ + sinh t e₁)` of a frame. -/
theorem s07_mo_geod (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) (P : ℂ → ℝ × ℂ)
    (hP : ∀ p, P p = ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p))
    {e₀ e₁ e₂ : ℝ × ℂ}
    (hon : B e₀ e₀ = -1 ∧ B e₁ e₁ = 1 ∧ B e₂ e₂ = 1 ∧ B e₀ e₁ = 0 ∧ B e₀ e₂ = 0 ∧ B e₁ e₂ = 0)
    (he₀ : 0 < e₀.1) (γ : ℝ → ℂ)
    (hγ : ∀ t, γ t = (Real.cosh t • e₀ + Real.sinh t • e₁).2 /
      ((1 + (Real.cosh t • e₀ + Real.sinh t • e₁).1 : ℝ) : ℂ)) :
    (∀ t, γ t ∈ unitDisc) ∧ (∀ t, P (γ t) = Real.cosh t • e₀ + Real.sinh t • e₁) ∧
      ∀ s t, diskDist (γ s) (γ t) = |s - t| := by
  have ht := s07_mo_time B hB hon
  obtain ⟨h00, h11, -, h01, -, -⟩ := hon
  have h10 : B e₁ e₀ = 0 := (s07_mo_B_symm B hB e₁ e₀).trans h01
  have hX : ∀ t, B (Real.cosh t • e₀ + Real.sinh t • e₁) (Real.cosh t • e₀ + Real.sinh t • e₁) = -1 ∧
      0 < (Real.cosh t • e₀ + Real.sinh t • e₁).1 := by
    intro t
    constructor
    · rw [s07_mo_B_comb B hB, s07_mo_B_combr B hB, s07_mo_B_combr B hB, h00, h11, h01, h10]
      linear_combination (-1 : ℝ) * Real.cosh_sq t
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      have hc := Real.cosh_pos t
      have hcs := Real.cosh_sq t
      by_contra hcon
      push_neg at hcon
      have h1 : 0 ≤ Real.cosh t * e₀.1 := (mul_pos hc he₀).le
      have h2 : Real.cosh t * e₀.1 ≤ -(Real.sinh t * e₁.1) := by linarith
      have h3 := mul_self_le_mul_self h1 h2
      have h4 : Real.sinh t ^ 2 * e₁.1 ^ 2 ≤ Real.sinh t ^ 2 * (e₀.1 ^ 2 - 1) :=
        mul_le_mul_of_nonneg_left ht (sq_nonneg _)
      nlinarith [sq_nonneg (Real.sinh t), sq_nonneg e₀.1]
  have hin : ∀ t, γ t ∈ unitDisc ∧ P (γ t) = Real.cosh t • e₀ + Real.sinh t • e₁ := by
    intro t
    rw [hγ t]
    exact s07_mo_hyp_inv B hB P hP (hX t).1 (hX t).2
  refine ⟨fun t => (hin t).1, fun t => (hin t).2, fun s t => ?_⟩
  have hc : diskCoshDist (γ s) (γ t) = Real.cosh (s - t) := by
    rw [(s07_mo_hyp B hB P hP (hin s).1).2.2 _ (hin t).1, (hin s).2, (hin t).2,
      s07_mo_B_comb B hB, s07_mo_B_combr B hB, s07_mo_B_combr B hB, h00, h11, h01, h10,
      Real.cosh_sub]
    ring
  show Real.arcosh (diskCoshDist (γ s) (γ t)) = |s - t|
  rw [hc, ← Real.cosh_abs, Real.arcosh_cosh (abs_nonneg _)]

/-- Coefficient limits for the geodesic: `cosh t / (1 + cosh t a + sinh t b) → 1/(a + b)` and
`sinh t / (1 + cosh t a + sinh t b) → 1/(a + b)` as `t → ∞`. -/
theorem s07_mo_line_coef {a b : ℝ} (hk : 0 < a + b) :
    Tendsto (fun t => Real.cosh t / (1 + (Real.cosh t * a + Real.sinh t * b))) atTop
      (𝓝 (1 / (a + b))) ∧
    Tendsto (fun t => Real.sinh t / (1 + (Real.cosh t * a + Real.sinh t * b))) atTop
      (𝓝 (1 / (a + b))) := by
  have hv : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have hden : (2 * (0 : ℝ) + (1 + 0 ^ 2) * a + (1 - 0 ^ 2) * b) ≠ 0 := by
    norm_num
    linarith
  have hid : ∀ t : ℝ, Real.cosh t * (2 * Real.exp (-t)) = 1 + Real.exp (-t) ^ 2 ∧
      Real.sinh t * (2 * Real.exp (-t)) = 1 - Real.exp (-t) ^ 2 := by
    intro t
    have e : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    constructor
    · rw [Real.cosh_eq]
      linear_combination e
    · rw [Real.sinh_eq]
      linear_combination e
  have hden' : ∀ t : ℝ, 2 * Real.exp (-t) + (1 + Real.exp (-t) ^ 2) * a +
      (1 - Real.exp (-t) ^ 2) * b =
      (2 * Real.exp (-t)) * (1 + (Real.cosh t * a + Real.sinh t * b)) := by
    intro t
    rw [← (hid t).1, ← (hid t).2]
    ring
  have h2v : ∀ t : ℝ, 2 * Real.exp (-t) ≠ 0 := fun t => by positivity
  constructor
  · have hf : ContinuousAt (fun v : ℝ => (1 + v ^ 2) / (2 * v + (1 + v ^ 2) * a +
        (1 - v ^ 2) * b)) 0 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) hden
    have h := hf.tendsto.comp hv
    rw [show (1 + (0 : ℝ) ^ 2) / (2 * 0 + (1 + 0 ^ 2) * a + (1 - 0 ^ 2) * b) = 1 / (a + b) by
      norm_num] at h
    refine h.congr (fun t => ?_)
    show (1 + Real.exp (-t) ^ 2) / (2 * Real.exp (-t) + (1 + Real.exp (-t) ^ 2) * a +
      (1 - Real.exp (-t) ^ 2) * b) = _
    rw [hden', ← (hid t).1, mul_comm (Real.cosh t), mul_div_mul_left _ _ (h2v t)]
  · have hf : ContinuousAt (fun v : ℝ => (1 - v ^ 2) / (2 * v + (1 + v ^ 2) * a +
        (1 - v ^ 2) * b)) 0 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) hden
    have h := hf.tendsto.comp hv
    rw [show (1 - (0 : ℝ) ^ 2) / (2 * 0 + (1 + 0 ^ 2) * a + (1 - 0 ^ 2) * b) = 1 / (a + b) by
      norm_num] at h
    refine h.congr (fun t => ?_)
    show (1 - Real.exp (-t) ^ 2) / (2 * Real.exp (-t) + (1 + Real.exp (-t) ^ 2) * a +
      (1 - Real.exp (-t) ^ 2) * b) = _
    rw [hden', ← (hid t).2, mul_comm (Real.sinh t), mul_div_mul_left _ _ (h2v t)]

/-- Morse M1: the unit-speed geodesic `γ(t) = P⁻¹(cosh t e₀ + sinh t e₁)` of a frame, with
ideal endpoints `ω± = (e₀' ± e₁')/(e₀,₀ ± e₁,₀) ∈ ∂𝔻`. -/
theorem s07_mo_line (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) (P : ℂ → ℝ × ℂ)
    (hP : ∀ p, P p = ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p))
    {e₀ e₁ e₂ : ℝ × ℂ}
    (hon : B e₀ e₀ = -1 ∧ B e₁ e₁ = 1 ∧ B e₂ e₂ = 1 ∧ B e₀ e₁ = 0 ∧ B e₀ e₂ = 0 ∧ B e₁ e₂ = 0)
    (he₀ : 0 < e₀.1) :
    0 < e₀.1 + e₁.1 ∧ 0 < e₀.1 - e₁.1 ∧
      ‖(e₀.2 + e₁.2) / ((e₀.1 + e₁.1 : ℝ) : ℂ)‖ = 1 ∧ ‖(e₀.2 - e₁.2) / ((e₀.1 - e₁.1 : ℝ) : ℂ)‖ = 1 ∧
      ∃ γ : ℝ → ℂ, (∀ t, γ t ∈ unitDisc) ∧ P (γ 0) = e₀ ∧ (∀ t, B (P (γ t)) e₂ = 0) ∧
        (∀ s t, diskDist (γ s) (γ t) = |s - t|) ∧
        Tendsto γ atTop (𝓝 ((e₀.2 + e₁.2) / ((e₀.1 + e₁.1 : ℝ) : ℂ))) ∧
        Tendsto γ atBot (𝓝 ((e₀.2 - e₁.2) / ((e₀.1 - e₁.1 : ℝ) : ℂ))) := by
  have hBc := s07_mo_Bc B hB
  have ht := s07_mo_time B hB hon
  obtain ⟨hg, hgP, hgd⟩ := s07_mo_geod B hB P hP hon he₀ _ (fun t => rfl)
  obtain ⟨h00, h11, -, h01, h02, h12⟩ := hon
  have hlt : |e₁.1| < e₀.1 := by
    rw [← abs_of_pos he₀]
    exact sq_lt_sq.mp (by linarith)
  have hkp : 0 < e₀.1 + e₁.1 := by linarith [neg_abs_le e₁.1]
  have hkm : 0 < e₀.1 - e₁.1 := by linarith [le_abs_self e₁.1]
  rw [hBc] at h00 h11 h01
  have hnp : ‖e₀.2 + e₁.2‖ = e₀.1 + e₁.1 := by
    refine (pow_left_inj₀ (norm_nonneg _) hkp.le two_ne_zero).mp ?_
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im]
    linear_combination h00 + h11 + 2 * h01
  have hnm : ‖e₀.2 - e₁.2‖ = e₀.1 - e₁.1 := by
    refine (pow_left_inj₀ (norm_nonneg _) hkm.le two_ne_zero).mp ?_
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    linear_combination h00 + h11 - 2 * h01
  refine ⟨hkp, hkm, ?_, ?_, _, hg, ?_, ?_, hgd, ?_, ?_⟩
  · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hkp.le, hnp, div_self hkp.ne']
  · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hkm.le, hnm, div_self hkm.ne']
  · rw [hgP 0]
    simp
  · intro t
    rw [hgP t, s07_mo_B_comb B hB, h02, h12]
    ring
  · have hγ : ∀ t : ℝ, ((Real.cosh t / (1 + (Real.cosh t * e₀.1 + Real.sinh t * e₁.1)) : ℝ) : ℂ) *
        e₀.2 + ((Real.sinh t / (1 + (Real.cosh t * e₀.1 + Real.sinh t * e₁.1)) : ℝ) : ℂ) * e₁.2 =
        (Real.cosh t • e₀ + Real.sinh t • e₁).2 /
          ((1 + (Real.cosh t • e₀ + Real.sinh t • e₁).1 : ℝ) : ℂ) := by
      intro t
      simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, smul_eq_mul,
        Complex.real_smul]
      push_cast
      ring
    obtain ⟨hα, hβ⟩ := s07_mo_line_coef hkp
    have h := (((Complex.continuous_ofReal.tendsto _).comp hα).mul_const e₀.2).add
      (((Complex.continuous_ofReal.tendsto _).comp hβ).mul_const e₁.2)
    have hval : (e₀.2 + e₁.2) / ((e₀.1 + e₁.1 : ℝ) : ℂ) =
        ((1 / (e₀.1 + e₁.1) : ℝ) : ℂ) * e₀.2 + ((1 / (e₀.1 + e₁.1) : ℝ) : ℂ) * e₁.2 := by
      push_cast
      ring
    rw [hval]
    exact h.congr hγ
  · have hk' : 0 < e₀.1 + -e₁.1 := by linarith
    obtain ⟨hα, hβ⟩ := s07_mo_line_coef hk'
    have hα' := hα.comp tendsto_neg_atBot_atTop
    have hβ' := hβ.comp tendsto_neg_atBot_atTop
    have hγ : ∀ t : ℝ, ((((fun t => Real.cosh t / (1 + (Real.cosh t * e₀.1 +
        Real.sinh t * -e₁.1))) ∘ Neg.neg) t : ℝ) : ℂ) * e₀.2 -
        ((((fun t => Real.sinh t / (1 + (Real.cosh t * e₀.1 + Real.sinh t * -e₁.1))) ∘
          Neg.neg) t : ℝ) : ℂ) * e₁.2 =
        (Real.cosh t • e₀ + Real.sinh t • e₁).2 /
          ((1 + (Real.cosh t • e₀ + Real.sinh t • e₁).1 : ℝ) : ℂ) := by
      intro t
      simp only [Function.comp, Real.cosh_neg, Real.sinh_neg, Prod.snd_add, Prod.smul_snd,
        Prod.fst_add, Prod.smul_fst, smul_eq_mul, Complex.real_smul]
      push_cast
      ring
    have h := (((Complex.continuous_ofReal.tendsto _).comp hα').mul_const e₀.2).sub
      (((Complex.continuous_ofReal.tendsto _).comp hβ').mul_const e₁.2)
    have hval : (e₀.2 - e₁.2) / ((e₀.1 - e₁.1 : ℝ) : ℂ) =
        ((1 / (e₀.1 + -e₁.1) : ℝ) : ℂ) * e₀.2 - ((1 / (e₀.1 + -e₁.1) : ℝ) : ℂ) * e₁.2 := by
      rw [← sub_eq_add_neg]
      push_cast
      ring
    rw [hval]
    exact h.congr hγ

/-- Morse M2: the geodesic through `a, b ∈ 𝔻`, parametrized proportionally to arclength. -/
theorem s07_mo_segment {a b : ℂ} (ha : a ∈ unitDisc) (hb : b ∈ unitDisc) :
    ∃ σ : ℝ → ℂ, σ 0 = a ∧ σ 1 = b ∧ (∀ t, σ t ∈ unitDisc) ∧
      ∀ s t, diskDist (σ s) (σ t) = |s - t| * diskDist a b := by
  by_cases hab : a = b
  · subst hab
    have h0 : diskDist a a = 0 := by
      show Real.arcosh (diskCoshDist a a) = 0
      have : diskCoshDist a a = 1 := by
        unfold diskCoshDist
        simp
      rw [this, Real.arcosh_zero]
    refine ⟨fun _ => a, rfl, rfl, fun _ => ha, fun s t => ?_⟩
    rw [h0, mul_zero]
  obtain ⟨B, hB⟩ : ∃ B : ℝ × ℂ → ℝ × ℂ → ℝ, ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℝ × ℂ, ∀ p, P p = ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2),
      ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p) := ⟨_, fun _ => rfl⟩
  obtain ⟨e₁, e₂, hon, hPb⟩ := s07_mo_frame B hB P hP ha hb hab
  have he₀ := (s07_mo_hyp B hB P hP ha).2.1
  obtain ⟨hg, hgP, hgd⟩ := s07_mo_geod B hB P hP hon he₀ _ (fun t => rfl)
  have hd0 : 0 ≤ diskDist a b := s02_diskDist_nonneg ha hb
  refine ⟨fun t => (Real.cosh (t * diskDist a b) • P a + Real.sinh (t * diskDist a b) • e₁).2 /
      ((1 + (Real.cosh (t * diskDist a b) • P a +
        Real.sinh (t * diskDist a b) • e₁).1 : ℝ) : ℂ), ?_, ?_, fun t => hg _, fun s t => ?_⟩
  · apply s07_mo_P_inj P hP (hg _) ha
    rw [hgP]
    simp
  · apply s07_mo_P_inj P hP (hg _) hb
    rw [hgP, one_mul, hPb]
  · show diskDist (_ : ℂ) _ = _
    rw [hgd, ← sub_mul, abs_mul, abs_of_nonneg hd0]

/-- Morse M2 (Step 1): the polygon `η` through points `q n` with `d(q n, q (n+1)) ≤ S`, run over
`[n, n+1]` at constant speed, is `S`-Lipschitz and `S`-close to `q ⌊s⌋` and `q ⌈s⌉`. -/
theorem s07_mo_polygon {S : ℝ} (hS0 : 0 ≤ S) (q : ℤ → ℂ) (hq : ∀ n, q n ∈ unitDisc)
    (hS : ∀ n, diskDist (q n) (q (n + 1)) ≤ S) :
    ∃ η : ℝ → ℂ, (∀ τ, η τ ∈ unitDisc) ∧ (∀ n : ℤ, η n = q n) ∧
      (∀ s t, diskDist (η s) (η t) ≤ S * |s - t|) ∧
      ∀ s, diskDist (η s) (q ⌊s⌋) ≤ S ∧ diskDist (η s) (q ⌈s⌉) ≤ S := by
  have hseg : ∀ n : ℤ, ∃ σ : ℝ → ℂ, σ 0 = q n ∧ σ 1 = q (n + 1) ∧ (∀ t, σ t ∈ unitDisc) ∧
      ∀ s t, diskDist (σ s) (σ t) = |s - t| * diskDist (q n) (q (n + 1)) :=
    fun n => s07_mo_segment (hq n) (hq (n + 1))
  choose σ hσ0 hσ1 hσD hσd using hseg
  have hdn : ∀ n, 0 ≤ diskDist (q n) (q (n + 1)) := fun n => s02_diskDist_nonneg (hq n) (hq _)
  have hηD : ∀ τ, σ ⌊τ⌋ (Int.fract τ) ∈ unitDisc := fun τ => hσD _ _
  have hηn : ∀ n : ℤ, σ ⌊(n : ℝ)⌋ (Int.fract (n : ℝ)) = q n := by
    intro n
    rw [Int.floor_intCast, Int.fract_intCast, hσ0]
  have hcell : ∀ s t : ℝ, ⌊s⌋ = ⌊t⌋ →
      diskDist (σ ⌊s⌋ (Int.fract s)) (σ ⌊t⌋ (Int.fract t)) ≤ S * |s - t| := by
    intro s t hst
    rw [← hst, hσd, ← Int.self_sub_floor, ← Int.self_sub_floor, hst,
      show s - ⌊t⌋ - (t - ⌊t⌋) = s - t by ring, mul_comm]
    exact mul_le_mul_of_nonneg_right (hS _) (abs_nonneg _)
  have hend : ∀ s : ℝ, diskDist (σ ⌊s⌋ (Int.fract s)) (q (⌊s⌋ + 1)) ≤
      S * ((⌊s⌋ : ℝ) + 1 - s) := by
    intro s
    rw [← hσ1, hσd, ← Int.self_sub_floor]
    have h1 : |s - ⌊s⌋ - 1| = (⌊s⌋ : ℝ) + 1 - s := by
      rw [abs_of_nonpos (by linarith [Int.lt_floor_add_one s])]
      ring
    rw [h1, mul_comm]
    exact mul_le_mul_of_nonneg_right (hS _) (by linarith [Int.lt_floor_add_one s])
  have hmain : ∀ k : ℕ, ∀ s t : ℝ, s ≤ t → ⌊t⌋ - ⌊s⌋ = k →
      diskDist (σ ⌊s⌋ (Int.fract s)) (σ ⌊t⌋ (Int.fract t)) ≤ S * (t - s) := by
    intro k
    induction k with
    | zero =>
      intro s t hst hk
      have h : ⌊s⌋ = ⌊t⌋ := by push_cast at hk; omega
      have := hcell s t h
      rwa [abs_sub_comm, abs_of_nonneg (by linarith)] at this
    | succ k ih =>
      intro s t hst hk
      have hm := hηn (⌊s⌋ + 1)
      have hfm : ⌊(((⌊s⌋ + 1 : ℤ) : ℝ))⌋ = ⌊s⌋ + 1 := Int.floor_intCast _
      have hmt : (((⌊s⌋ + 1 : ℤ) : ℝ)) ≤ t := by
        have h1 : ⌊s⌋ + 1 ≤ ⌊t⌋ := by push_cast at hk; omega
        have h2 : (((⌊s⌋ + 1 : ℤ) : ℝ)) ≤ (⌊t⌋ : ℝ) := by exact_mod_cast h1
        linarith [Int.floor_le t]
      have hk' : ⌊t⌋ - ⌊(((⌊s⌋ + 1 : ℤ) : ℝ))⌋ = k := by
        rw [hfm]
        push_cast at hk ⊢
        omega
      have h1 := ih _ t hmt hk'
      rw [hm] at h1
      have h2 := hend s
      have htri := s02_diskDist_triangle (hηD s) (hq (⌊s⌋ + 1)) (hηD t)
      push_cast at h1
      linarith
  refine ⟨fun τ => σ ⌊τ⌋ (Int.fract τ), hηD, hηn, fun s t => ?_, fun s => ?_⟩
  · rcases le_total s t with hst | hst
    · have hk : ⌊t⌋ - ⌊s⌋ = ((⌊t⌋ - ⌊s⌋).toNat : ℤ) :=
        (Int.toNat_of_nonneg (by linarith [Int.floor_le_floor hst])).symm
      have := hmain _ s t hst hk
      rwa [abs_sub_comm, abs_of_nonneg (by linarith)]
    · have hk : ⌊s⌋ - ⌊t⌋ = ((⌊s⌋ - ⌊t⌋).toNat : ℤ) :=
        (Int.toNat_of_nonneg (by linarith [Int.floor_le_floor hst])).symm
      have := hmain _ t s hst hk
      show diskDist (σ ⌊s⌋ (Int.fract s)) (σ ⌊t⌋ (Int.fract t)) ≤ _
      rw [s02_diskDist_comm (hηD s) (hηD t), abs_of_nonneg (by linarith)]
      exact this
  · have hfl : diskDist (σ ⌊s⌋ (Int.fract s)) (q ⌊s⌋) ≤ S := by
      rw [← hσ0, hσd, sub_zero, abs_of_nonneg (Int.fract_nonneg s)]
      calc Int.fract s * diskDist (q ⌊s⌋) (q (⌊s⌋ + 1)) ≤ 1 * diskDist (q ⌊s⌋) (q (⌊s⌋ + 1)) :=
            mul_le_mul_of_nonneg_right (Int.fract_lt_one s).le (hdn _)
        _ ≤ S := by rw [one_mul]; exact hS _
    refine ⟨hfl, ?_⟩
    have h1 := Int.floor_le_ceil s
    have h2 := Int.ceil_le_floor_add_one s
    rcases (show ⌈s⌉ = ⌊s⌋ ∨ ⌈s⌉ = ⌊s⌋ + 1 by omega) with h | h
    · show diskDist (σ ⌊s⌋ (Int.fract s)) _ ≤ S
      rw [h]
      exact hfl
    · show diskDist (σ ⌊s⌋ (Int.fract s)) _ ≤ S
      rw [h]
      have := hend s
      have h3 := Int.floor_le s
      nlinarith

/-- `sinh y ≤ y cosh y` for `y ≥ 0` (mean value theorem). -/
theorem s07_mo_sinh_le {y : ℝ} (hy : 0 ≤ y) : Real.sinh y ≤ y * Real.cosh y := by
  have h := (convex_Icc (0 : ℝ) y).image_sub_le_mul_sub_of_deriv_le
    Real.continuous_sinh.continuousOn Real.differentiable_sinh.differentiableOn
    (C := Real.cosh y) (fun x hx => by
      rw [interior_Icc] at hx
      rw [Real.deriv_sinh]
      exact Real.cosh_le_cosh.mpr (by rw [abs_of_pos hx.1, abs_of_nonneg hy]; exact hx.2.le))
    0 ⟨le_rfl, hy⟩ y ⟨hy, le_rfl⟩ hy
  rw [Real.sinh_zero, sub_zero, sub_zero] at h
  linarith [mul_comm y (Real.cosh y)]

/-- Morse M3 (Step 2, excursions are short): an `S`-Lipschitz curve on `[T₁, T₂]` with endpoints
on the geodesic (`ρ = 0`) and the quasi-geodesic bound `S(t - s) ≤ a₁ d(η s, η t) + b₁` stays
within `M_*` of the geodesic.  Only the three Fermi estimates are used. -/
theorem s07_mo_excursion (lam c : ℝ) (hlam : 1 ≤ lam) (hc : 0 ≤ c) (ρ υ : ℂ → ℝ)
    (hproj : ∀ p ∈ unitDisc, ∀ q ∈ unitDisc, ∀ r : ℝ, 0 ≤ r → r ≤ |ρ p| → r ≤ |ρ q| →
      Real.cosh r * Real.sinh (|υ p - υ q| / 2) ≤ Real.sinh (diskDist p q / 2))
    (htri : ∀ p ∈ unitDisc, ∀ q ∈ unitDisc, diskDist p q ≤ |ρ p| + |υ p - υ q| + |ρ q|)
    (hlip : ∀ p ∈ unitDisc, ∀ q ∈ unitDisc, |ρ p - ρ q| ≤ diskDist p q)
    (η : ℝ → ℂ) (hη : ∀ τ, η τ ∈ unitDisc) {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂)
    (hLip : ∀ s t, diskDist (η s) (η t) ≤ morseS lam c * |s - t|)
    (hqg : ∀ s t, T₁ ≤ s → s ≤ t → t ≤ T₂ →
      morseS lam c * (t - s) ≤ morseA1 lam c * diskDist (η s) (η t) + morseB1 lam c)
    (h₁ : ρ (η T₁) = 0) (h₂ : ρ (η T₂) = 0) :
    ∀ τ ∈ Icc T₁ T₂, |ρ (η τ)| ≤ morseM lam c := by
  intro τ₀ hτ₀
  have hS1 : 1 ≤ morseS lam c := by unfold morseS; linarith
  have ha1 : 1 ≤ morseA1 lam c := by unfold morseA1; nlinarith [hS1]
  have hb0 : 0 ≤ morseB1 lam c := by
    unfold morseB1
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hcr : Real.cosh (morseR lam c) = 2 * morseA1 lam c := Real.cosh_arcosh (by linarith)
  have hr0 : 0 ≤ morseR lam c := Real.arcosh_nonneg (by linarith)
  rw [show morseM lam c = (2 * morseA1 lam c + 1) * morseR lam c + morseB1 lam c from rfl]
  generalize morseR lam c = r at *
  generalize morseB1 lam c = b₁ at *
  generalize morseA1 lam c = a₁ at *
  generalize morseS lam c = S at *
  have hgl : ∀ s t, |ρ (η s) - ρ (η t)| ≤ S * |s - t| :=
    fun s t => (hlip _ (hη s) _ (hη t)).trans (hLip s t)
  have hgc : Continuous fun τ => |ρ (η τ)| := by
    have : Continuous fun τ => ρ (η τ) := by
      refine (LipschitzWith.of_dist_le_mul (K := S.toNNReal) fun x y => ?_).continuous
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by linarith)]
      exact hgl x y
    exact this.abs
  by_cases hτr : |ρ (η τ₀)| ≤ r
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * a₁) hr0]
  push_neg at hτr
  -- the last time `s ≤ τ₀` and the first time `t ≥ τ₀` with `|ρ| ≤ r`
  have hAc : IsClosed (Icc T₁ τ₀ ∩ {σ | |ρ (η σ)| ≤ r}) :=
    isClosed_Icc.inter (isClosed_le hgc continuous_const)
  have hAne : (Icc T₁ τ₀ ∩ {σ | |ρ (η σ)| ≤ r}).Nonempty :=
    ⟨T₁, ⟨le_rfl, hτ₀.1⟩, by show |ρ (η T₁)| ≤ r; rw [h₁, abs_zero]; exact hr0⟩
  have hAb : BddAbove (Icc T₁ τ₀ ∩ {σ | |ρ (η σ)| ≤ r}) := ⟨τ₀, fun σ hσ => hσ.1.2⟩
  have hsA := hAc.csSup_mem hAne hAb
  obtain ⟨s, hsdef⟩ : ∃ s, s = sSup (Icc T₁ τ₀ ∩ {σ | |ρ (η σ)| ≤ r}) := ⟨_, rfl⟩
  rw [← hsdef] at hsA
  have hs_le : |ρ (η s)| ≤ r := hsA.2
  have hsT1 : T₁ ≤ s := hsA.1.1
  have hsτ : s < τ₀ := by
    refine lt_of_le_of_ne hsA.1.2 (fun h => ?_)
    rw [h] at hs_le
    exact absurd hs_le (not_le.mpr hτr)
  have hright : ∀ σ, s < σ → σ ≤ τ₀ → r < |ρ (η σ)| := by
    intro σ h1 h2
    by_contra h
    push_neg at h
    have hσ : σ ∈ Icc T₁ τ₀ ∩ {σ | |ρ (η σ)| ≤ r} := ⟨⟨by linarith, h2⟩, h⟩
    have := le_csSup hAb hσ
    rw [← hsdef] at this
    linarith
  have hBc : IsClosed (Icc τ₀ T₂ ∩ {σ | |ρ (η σ)| ≤ r}) :=
    isClosed_Icc.inter (isClosed_le hgc continuous_const)
  have hBne : (Icc τ₀ T₂ ∩ {σ | |ρ (η σ)| ≤ r}).Nonempty :=
    ⟨T₂, ⟨hτ₀.2, le_rfl⟩, by show |ρ (η T₂)| ≤ r; rw [h₂, abs_zero]; exact hr0⟩
  have hBb : BddBelow (Icc τ₀ T₂ ∩ {σ | |ρ (η σ)| ≤ r}) := ⟨τ₀, fun σ hσ => hσ.1.1⟩
  have htB := hBc.csInf_mem hBne hBb
  obtain ⟨t, htdef⟩ : ∃ t, t = sInf (Icc τ₀ T₂ ∩ {σ | |ρ (η σ)| ≤ r}) := ⟨_, rfl⟩
  rw [← htdef] at htB
  have ht_le : |ρ (η t)| ≤ r := htB.2
  have htT2 : t ≤ T₂ := htB.1.2
  have hτt : τ₀ < t := by
    refine lt_of_le_of_ne htB.1.1 (fun h => ?_)
    rw [← h] at ht_le
    exact absurd ht_le (not_le.mpr hτr)
  have hleft : ∀ σ, τ₀ ≤ σ → σ < t → r < |ρ (η σ)| := by
    intro σ h1 h2
    by_contra h
    push_neg at h
    have hσ : σ ∈ Icc τ₀ T₂ ∩ {σ | |ρ (η σ)| ≤ r} := ⟨⟨h1, by linarith⟩, h⟩
    have := csInf_le hBb hσ
    rw [← htdef] at this
    linarith
  have hr_s : r ≤ |ρ (η s)| := by
    have ht : Tendsto (fun τ => |ρ (η τ)|) (𝓝[>] s) (𝓝 (|ρ (η s)|)) :=
      (hgc.tendsto s).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT hsτ] with σ hσ
    exact (hright σ hσ.1 hσ.2.le).le
  have hr_t : r ≤ |ρ (η t)| := by
    have ht : Tendsto (fun τ => |ρ (η τ)|) (𝓝[<] t) (𝓝 (|ρ (η t)|)) :=
      (hgc.tendsto t).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT hτt] with σ hσ
    exact (hleft σ hσ.1.le hσ.2).le
  have hr_on : ∀ σ ∈ Icc s t, r ≤ |ρ (η σ)| := by
    intro σ hσ
    rcases eq_or_lt_of_le hσ.1 with h | h
    · rw [← h]
      exact hr_s
    rcases eq_or_lt_of_le hσ.2 with h' | h'
    · rw [h']
      exact hr_t
    rcases le_total σ τ₀ with h'' | h''
    · exact (hright σ h h'').le
    · exact (hleft σ h'' h').le
  have hst : s < t := hsτ.trans hτt
  -- the length estimate on `[s, t]`, for every subdivision into `n` pieces
  have hbound : ∀ n : ℕ, 1 ≤ n → S * (t - s) ≤
      2 * a₁ * r + b₁ + S * (t - s) / 2 * Real.cosh (S * (t - s) / 2 / n) := by
    intro n hn
    have hN : (0 : ℝ) < n := by exact_mod_cast hn
    obtain ⟨pts, hpts⟩ : ∃ pts : ℕ → ℝ, pts = fun i : ℕ => s + (i : ℝ) * ((t - s) / n) := ⟨_, rfl⟩
    have hnl : (n : ℝ) * ((t - s) / n) = t - s := by field_simp
    have hl0 : 0 ≤ (t - s) / n := div_nonneg (by linarith) hN.le
    have hp_in : ∀ i, i ≤ n → pts i ∈ Icc s t := by
      intro i hi
      have hi' : (i : ℝ) ≤ n := by exact_mod_cast hi
      rw [hpts]
      constructor
      · have : 0 ≤ (i : ℝ) * ((t - s) / n) := mul_nonneg (Nat.cast_nonneg _) hl0
        linarith
      · have : (i : ℝ) * ((t - s) / n) ≤ n * ((t - s) / n) := mul_le_mul_of_nonneg_right hi' hl0
        linarith
    have hp_step : ∀ i, pts (i + 1) - pts i = (t - s) / n := by
      intro i
      rw [hpts]
      push_cast
      ring
    have hp0 : pts 0 = s := by
      rw [hpts]
      simp
    have hpn : pts n = t := by
      rw [hpts]
      show s + (n : ℝ) * ((t - s) / n) = t
      linarith
    obtain ⟨y, hy⟩ : ∃ y, y = S * (t - s) / 2 / n := ⟨_, rfl⟩
    rw [← hy]
    have hy0 : 0 ≤ y := by
      rw [hy]
      exact div_nonneg (div_nonneg (mul_nonneg (by linarith) (by linarith)) two_pos.le) hN.le
    have hcr0 : 0 < Real.cosh r := Real.cosh_pos r
    have hterm : ∀ i ∈ Finset.range n,
        |υ (η (pts (i + 1))) - υ (η (pts i))| ≤ 2 * Real.sinh y / Real.cosh r := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hA := hp_in i hi'.le
      have hB := hp_in (i + 1) hi'
      have hpr := hproj _ (hη (pts i)) _ (hη (pts (i + 1))) r hr0 (hr_on _ hA) (hr_on _ hB)
      have hd : diskDist (η (pts i)) (η (pts (i + 1))) / 2 ≤ y := by
        have := hLip (pts i) (pts (i + 1))
        rw [abs_sub_comm, hp_step, abs_of_nonneg hl0] at this
        rw [hy, show S * (t - s) / 2 / n = S * ((t - s) / n) / 2 by ring]
        linarith
      have h1 : Real.sinh (diskDist (η (pts i)) (η (pts (i + 1))) / 2) ≤ Real.sinh y :=
        Real.sinh_le_sinh.mpr hd
      have h2 : |υ (η (pts i)) - υ (η (pts (i + 1)))| / 2 ≤
          Real.sinh (|υ (η (pts i)) - υ (η (pts (i + 1)))| / 2) :=
        Real.self_le_sinh_iff.mpr (by positivity)
      rw [abs_sub_comm, le_div_iff₀ hcr0]
      nlinarith [mul_le_mul_of_nonneg_left h2 hcr0.le]
    have hsum : |υ (η t) - υ (η s)| ≤ n * (2 * Real.sinh y / Real.cosh r) := by
      have htel := Finset.sum_range_sub (fun i => υ (η (pts i))) n
      rw [hpn, hp0] at htel
      rw [← htel]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hυb : |υ (η t) - υ (η s)| ≤ S * (t - s) * Real.cosh y / (2 * a₁) := by
      rw [← hcr]
      refine hsum.trans ?_
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hcr0]
      have hny : (n : ℝ) * 2 * y = S * (t - s) := by
        rw [hy]
        field_simp
      calc (n : ℝ) * (2 * Real.sinh y) = n * 2 * Real.sinh y := by ring
        _ ≤ n * 2 * (y * Real.cosh y) :=
            mul_le_mul_of_nonneg_left (s07_mo_sinh_le hy0) (by positivity)
        _ = (n * 2 * y) * Real.cosh y := by ring
        _ = S * (t - s) * Real.cosh y := by rw [hny]
    have hd := htri _ (hη s) _ (hη t)
    rw [abs_sub_comm (υ (η s))] at hd
    have hq := hqg s t hsT1 hst.le htT2
    have ha0 : (0 : ℝ) < a₁ := by linarith
    have h3 : a₁ * diskDist (η s) (η t) ≤ a₁ * (r + S * (t - s) * Real.cosh y / (2 * a₁) + r) :=
      mul_le_mul_of_nonneg_left (by linarith) ha0.le
    have h4 : a₁ * (r + S * (t - s) * Real.cosh y / (2 * a₁) + r) =
        2 * a₁ * r + S * (t - s) / 2 * Real.cosh y := by
      field_simp
      ring
    linarith
  have hlim : Tendsto (fun n : ℕ => 2 * a₁ * r + b₁ + S * (t - s) / 2 *
      Real.cosh (S * (t - s) / 2 / n)) atTop (𝓝 (2 * a₁ * r + b₁ + S * (t - s) / 2 * 1)) := by
    have h0 := (Real.continuous_cosh.tendsto 0).comp
      (tendsto_const_div_atTop_nhds_zero_nat (S * (t - s) / 2))
    rw [Real.cosh_zero] at h0
    exact tendsto_const_nhds.add (h0.const_mul _)
  have hfin : S * (t - s) ≤ 2 * a₁ * r + b₁ + S * (t - s) / 2 * 1 :=
    ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨1, hbound⟩)
  have e1 : |ρ (η τ₀)| ≤ |ρ (η s)| + S * (τ₀ - s) := by
    have h := hgl τ₀ s
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ τ₀ - s)] at h
    have := abs_sub_abs_le_abs_sub (ρ (η τ₀)) (ρ (η s))
    linarith
  have e2 : |ρ (η τ₀)| ≤ |ρ (η t)| + S * (t - τ₀) := by
    have h := hgl τ₀ t
    rw [abs_sub_comm τ₀ t, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - τ₀)] at h
    have := abs_sub_abs_le_abs_sub (ρ (η τ₀)) (ρ (η t))
    linarith
  linarith

/-- `d_𝔻(a, a) = 0`. -/
theorem s07_mo_dist_self (a : ℂ) : diskDist a a = 0 := by
  show Real.arcosh (diskCoshDist a a) = 0
  have : diskCoshDist a a = 1 := by
    unfold diskCoshDist
    simp
  rw [this, Real.arcosh_zero]

/-- `⟨α U, W⟩ = α ⟨U, W⟩`. -/
theorem s07_mo_B_smul (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) (α : ℝ) (U W : ℝ × ℂ) :
    B (α • U) W = α * B U W := by
  simp only [s07_mo_Bc B hB, Prod.smul_fst, Prod.smul_snd, Complex.smul_re, Complex.smul_im,
    smul_eq_mul]
  ring

/-- `⟨W, α U⟩ = α ⟨W, U⟩`. -/
theorem s07_mo_B_smulr (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) (α : ℝ) (U W : ℝ × ℂ) :
    B W (α • U) = α * B W U := by
  rw [s07_mo_B_symm B hB, s07_mo_B_smul B hB, s07_mo_B_symm B hB U]

/-- Gram determinant identity: if `u, v ⟂ f₂` for an orthonormal frame `(f₀, f₁, f₂)`, then
`⟨X, f₂⟩² · det G(u, v) = det G(u, v, X)`. -/
theorem s07_mo_gram (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) {f₀ f₁ f₂ : ℝ × ℂ}
    (hon : B f₀ f₀ = -1 ∧ B f₁ f₁ = 1 ∧ B f₂ f₂ = 1 ∧ B f₀ f₁ = 0 ∧ B f₀ f₂ = 0 ∧ B f₁ f₂ = 0)
    (u v X : ℝ × ℂ) (hu : B u f₂ = 0) (hv : B v f₂ = 0) :
    B X f₂ ^ 2 * (B u u * B v v - B u v ^ 2) =
      B u u * B v v * B X X + 2 * B u v * B u X * B v X - B u u * B v X ^ 2 -
        B v v * B u X ^ 2 - B X X * B u v ^ 2 := by
  have e := s07_mo_parseval B hB hon
  rw [e u u, e v v, e u v, e u X, e v X, e X X, hu, hv]
  ring

/-- Continuity of the Gram ratio `det G(u, v, X) / det G(u, v)` where `det G(u, v) ≠ 0`. -/
theorem s07_mo_ratio_cont (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) (X : ℝ × ℂ)
    {p₀ : (ℝ × ℂ) × (ℝ × ℂ)} (h0 : B p₀.1 p₀.1 * B p₀.2 p₀.2 - B p₀.1 p₀.2 ^ 2 ≠ 0) :
    ContinuousAt (fun p : (ℝ × ℂ) × (ℝ × ℂ) =>
      (B p.1 p.1 * B p.2 p.2 * B X X + 2 * B p.1 p.2 * B p.1 X * B p.2 X -
        B p.1 p.1 * B p.2 X ^ 2 - B p.2 p.2 * B p.1 X ^ 2 - B X X * B p.1 p.2 ^ 2) /
      (B p.1 p.1 * B p.2 p.2 - B p.1 p.2 ^ 2)) p₀ := by
  have hBeq : B = fun U V => -U.1 * V.1 + U.2.re * V.2.re + U.2.im * V.2.im :=
    funext fun U => funext fun V => s07_mo_Bc B hB U V
  subst hBeq
  exact ContinuousAt.div (by fun_prop) (by fun_prop) h0

/-- The normalized hyperboloid point: `(1, 2p/(1 + |p|²)) = ((1 - |p|²)/(1 + |p|²)) P p`. -/
theorem s07_mo_psi (P : ℂ → ℝ × ℂ)
    (hP : ∀ p, P p = ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p))
    {p : ℂ} (hp : p ∈ unitDisc) :
    ((1 : ℝ), ((2 / (1 + ‖p‖ ^ 2) : ℝ) : ℂ) * p) = ((1 - ‖p‖ ^ 2) / (1 + ‖p‖ ^ 2)) • P p := by
  have hp1 : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
  have hpn : 0 < 1 - ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
  have hpn' := hpn.ne'
  have hpp : (1 + ‖p‖ ^ 2) ≠ 0 := by positivity
  rw [hP]
  refine Prod.ext ?_ ?_
  · simp only [Prod.smul_fst, smul_eq_mul]
    field_simp
  · simp only [Prod.smul_snd, Complex.real_smul]
    rw [← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    field_simp

/-- Morse M4, one step: for the geodesic through `q (-N)`, `q N` (with `λ c < N`), the excursion bound
gives `det G(ψ(q(-N)), ψ(q N), P z) / det G(ψ(q(-N)), ψ(q N)) ≤ sinh² M_*`, where `η 0 = z`. -/
theorem s07_mo_qi_step (lam c : ℝ) (hlam : 1 ≤ lam) (hc : 0 ≤ c) (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) (P : ℂ → ℝ × ℂ)
    (hP : ∀ p, P p = ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p))
    (ψ : ℂ → ℝ × ℂ) (hψ : ψ = fun z => ((1 : ℝ), ((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * z))
    (q : ℤ → ℂ) (hqD : ∀ n, q n ∈ unitDisc)
    (hqlo : ∀ m n : ℤ, lam⁻¹ * |(m : ℝ) - n| - c ≤ diskDist (q m) (q n))
    (η : ℝ → ℂ) (hηD : ∀ τ, η τ ∈ unitDisc) (hηn : ∀ n : ℤ, η n = q n)
    (hηL : ∀ s t, diskDist (η s) (η t) ≤ morseS lam c * |s - t|)
    (hqg : ∀ s t : ℝ, s ≤ t →
      morseS lam c * (t - s) ≤ morseA1 lam c * diskDist (η s) (η t) + morseB1 lam c)
    (z : ℂ) (hη0 : η 0 = z) (N : ℕ) (hNr : lam * c < N) :
    (B (ψ (q (-(N : ℤ)))) (ψ (q (-(N : ℤ)))) * B (ψ (q (N : ℤ))) (ψ (q (N : ℤ))) * B (P z) (P z) +
        2 * B (ψ (q (-(N : ℤ)))) (ψ (q (N : ℤ))) * B (ψ (q (-(N : ℤ)))) (P z) *
          B (ψ (q (N : ℤ))) (P z) -
        B (ψ (q (-(N : ℤ)))) (ψ (q (-(N : ℤ)))) * B (ψ (q (N : ℤ))) (P z) ^ 2 -
        B (ψ (q (N : ℤ))) (ψ (q (N : ℤ))) * B (ψ (q (-(N : ℤ)))) (P z) ^ 2 -
        B (P z) (P z) * B (ψ (q (-(N : ℤ)))) (ψ (q (N : ℤ))) ^ 2) /
      (B (ψ (q (-(N : ℤ)))) (ψ (q (-(N : ℤ)))) * B (ψ (q (N : ℤ))) (ψ (q (N : ℤ))) -
        B (ψ (q (-(N : ℤ)))) (ψ (q (N : ℤ))) ^ 2) ≤ Real.sinh (morseM lam c) ^ 2 := by
  have hlam0 : 0 < lam := by linarith
  have ha := hqD (-(N : ℤ))
  have hb := hqD (N : ℤ)
  have hab_d : 0 < diskDist (q (-(N : ℤ))) (q (N : ℤ)) := by
    have h := hqlo (-(N : ℤ)) (N : ℤ)
    have habs : |(((-(N : ℤ) : ℤ)) : ℝ) - ((N : ℤ) : ℝ)| = 2 * N := by
      push_cast
      rw [show -(N : ℝ) - N = -(2 * N) by ring, abs_neg, abs_of_nonneg (by positivity)]
    rw [habs] at h
    have hc' : c < lam⁻¹ * (2 * N) := by
      rw [inv_mul_eq_div, lt_div_iff₀ hlam0]
      nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    linarith
  have hab : q (-(N : ℤ)) ≠ q (N : ℤ) := fun h => by
    rw [h, s07_mo_dist_self] at hab_d
    exact lt_irrefl _ hab_d
  obtain ⟨f₁, f₂, honN, hPb⟩ := s07_mo_frame B hB P hP ha hb hab
  have hf₀ := (s07_mo_hyp B hB P hP ha).2.1
  obtain ⟨ρN, hρN⟩ : ∃ ρN : ℂ → ℝ, ρN = fun p => Real.arsinh (B (P p) f₂) := ⟨_, rfl⟩
  obtain ⟨υN, hυN⟩ : ∃ υN : ℂ → ℝ,
      υN = fun p => Real.arsinh (B (P p) f₁ / Real.cosh (ρN p)) := ⟨_, rfl⟩
  have hF : ∀ p ∈ unitDisc, ∀ q' ∈ unitDisc, diskCoshDist p q' =
      Real.cosh (ρN p) * Real.cosh (ρN q') * Real.cosh (υN p - υN q') -
        Real.sinh (ρN p) * Real.sinh (ρN q') := fun p hp q' hq' =>
    s07_mo_fermi B hB P hP honN hf₀ ρN υN (fun p => by rw [hρN]) (fun p => by rw [hυN]) hp hq'
  have h₁ : ρN (η (((-(N : ℤ) : ℤ)) : ℝ)) = 0 := by
    rw [hηn, hρN]
    dsimp only
    rw [honN.2.2.2.2.1, Real.arsinh_zero]
  have h₂ : ρN (η ((N : ℤ) : ℝ)) = 0 := by
    rw [hηn, hρN]
    dsimp only
    rw [hPb, s07_mo_B_comb B hB, honN.2.2.2.2.1, honN.2.2.2.2.2, mul_zero, mul_zero, add_zero,
      Real.arsinh_zero]
  have hT : (((-(N : ℤ) : ℤ)) : ℝ) ≤ ((N : ℤ) : ℝ) := by
    push_cast
    linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hexc := s07_mo_excursion lam c hlam hc ρN υN
    (fun p hp q' hq' r hr hrp hrq => s07_mo_fermi_proj ρN υN hF hp hq' hr hrp hrq)
    (fun p hp q' hq' => s07_mo_fermi_tri ρN υN hF hp hq')
    (fun p hp q' hq' => s07_mo_fermi_lip ρN υN hF hp hq') η hηD hT hηL
    (fun s t _ hst _ => hqg s t hst) h₁ h₂ 0
    ⟨by push_cast; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)],
      by push_cast; exact Nat.cast_nonneg N⟩
  rw [hη0, hρN] at hexc
  dsimp only at hexc
  have hB2 : |B (P z) f₂| ≤ Real.sinh (morseM lam c) := by
    obtain ⟨h1, h2⟩ := abs_le.mp hexc
    refine abs_le.mpr ⟨?_, ?_⟩
    · have h := Real.sinh_le_sinh.mpr (show -Real.arsinh (B (P z) f₂) ≤ morseM lam c by
        linarith)
      rw [Real.sinh_neg, Real.sinh_arsinh] at h
      linarith
    · have h := Real.sinh_le_sinh.mpr h2
      rwa [Real.sinh_arsinh] at h
  -- the Gram ratio at the normalized endpoints equals `⟨P z, f₂⟩²`
  have hα : ψ (q (-(N : ℤ))) = ((1 - ‖q (-(N : ℤ))‖ ^ 2) / (1 + ‖q (-(N : ℤ))‖ ^ 2)) •
      P (q (-(N : ℤ))) := by
    rw [hψ]
    exact s07_mo_psi P hP ha
  have hβ : ψ (q (N : ℤ)) = ((1 - ‖q (N : ℤ)‖ ^ 2) / (1 + ‖q (N : ℤ)‖ ^ 2)) • P (q (N : ℤ)) := by
    rw [hψ]
    exact s07_mo_psi P hP hb
  have hu : B (ψ (q (-(N : ℤ)))) f₂ = 0 := by
    rw [hα, s07_mo_B_smul B hB, honN.2.2.2.2.1, mul_zero]
  have hv : B (ψ (q (N : ℤ))) f₂ = 0 := by
    rw [hβ, s07_mo_B_smul B hB, hPb, s07_mo_B_comb B hB, honN.2.2.2.2.1, honN.2.2.2.2.2]
    ring
  have hg := s07_mo_gram B hB honN _ _ (P z) hu hv
  have hα0 : 0 < (1 - ‖q (-(N : ℤ))‖ ^ 2) / (1 + ‖q (-(N : ℤ))‖ ^ 2) := by
    have h1 : ‖q (-(N : ℤ))‖ < 1 := mem_ball_zero_iff.mp ha
    have h2 : 0 < 1 - ‖q (-(N : ℤ))‖ ^ 2 := by nlinarith [norm_nonneg (q (-(N : ℤ)))]
    positivity
  have hβ0 : 0 < (1 - ‖q (N : ℤ)‖ ^ 2) / (1 + ‖q (N : ℤ)‖ ^ 2) := by
    have h1 : ‖q (N : ℤ)‖ < 1 := mem_ball_zero_iff.mp hb
    have h2 : 0 < 1 - ‖q (N : ℤ)‖ ^ 2 := by nlinarith [norm_nonneg (q (N : ℤ))]
    positivity
  have hPab : B (P (q (-(N : ℤ)))) (P (q (N : ℤ))) =
      -Real.cosh (diskDist (q (-(N : ℤ))) (q (N : ℤ))) := by
    rw [s07_mo_cosh_dist ha hb, (s07_mo_hyp B hB P hP ha).2.2 _ hb]
    ring
  have hG2 : B (ψ (q (-(N : ℤ)))) (ψ (q (-(N : ℤ)))) * B (ψ (q (N : ℤ))) (ψ (q (N : ℤ))) -
      B (ψ (q (-(N : ℤ)))) (ψ (q (N : ℤ))) ^ 2 < 0 := by
    rw [hα, hβ, s07_mo_B_smul B hB, s07_mo_B_smulr B hB, s07_mo_B_smul B hB,
      s07_mo_B_smulr B hB, s07_mo_B_smul B hB, s07_mo_B_smulr B hB, honN.1,
      (s07_mo_hyp B hB P hP hb).1, hPab]
    have hs := Real.sinh_pos_iff.mpr hab_d
    have e : ∀ α β d : ℝ, α * (α * -1) * (β * (β * -1)) - (α * (β * -Real.cosh d)) ^ 2 =
        -(α * β) ^ 2 * Real.sinh d ^ 2 := by
      intro α β d
      linear_combination (-(α * β) ^ 2) * Real.cosh_sq d
    rw [e]
    have := mul_pos (pow_pos (mul_pos hα0 hβ0) 2) (pow_pos hs 2)
    linarith
  rw [← hg, mul_div_assoc, div_self hG2.ne, mul_one, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hB2 2

/-- Morse M4, the limit: if the Gram ratios at `ψ(Q(γ(∓N)))` are `≤ K` for all large `N`, then
`⟨X, e₂⟩² ≤ K`, where `γ` is the geodesic through `e₀` in direction `e₁` and `Q` has boundary values
`id`. -/
theorem s07_mo_qi_limit (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re)
    (ψ : ℂ → ℝ × ℂ) (hψ : ψ = fun z => ((1 : ℝ), ((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * z))
    {e₀ e₁ e₂ : ℝ × ℂ}
    (hon : B e₀ e₀ = -1 ∧ B e₁ e₁ = 1 ∧ B e₂ e₂ = 1 ∧ B e₀ e₁ = 0 ∧ B e₀ e₂ = 0 ∧ B e₁ e₂ = 0)
    (hkp : 0 < e₀.1 + e₁.1) (hkm : 0 < e₀.1 - e₁.1) {ωp ωm : ℂ}
    (hωp : ωp = (e₀.2 + e₁.2) / ((e₀.1 + e₁.1 : ℝ) : ℂ))
    (hωm : ωm = (e₀.2 - e₁.2) / ((e₀.1 - e₁.1 : ℝ) : ℂ)) (hnp : ‖ωp‖ = 1) (hnm : ‖ωm‖ = 1)
    (Q : ℂ → ℂ) (hbd : HasDiskBoundaryValues Q id) (γ : ℝ → ℂ) (hγD : ∀ t, γ t ∈ unitDisc)
    (hγtop : Tendsto γ atTop (𝓝 ωp)) (hγbot : Tendsto γ atBot (𝓝 ωm)) (X : ℝ × ℂ) (K : ℝ)
    (N₀ : ℕ) (hstep : ∀ N : ℕ, N₀ ≤ N →
      (B (ψ (Q (γ (-(N : ℝ))))) (ψ (Q (γ (-(N : ℝ))))) * B (ψ (Q (γ N))) (ψ (Q (γ N))) * B X X +
          2 * B (ψ (Q (γ (-(N : ℝ))))) (ψ (Q (γ N))) * B (ψ (Q (γ (-(N : ℝ))))) X *
            B (ψ (Q (γ N))) X -
          B (ψ (Q (γ (-(N : ℝ))))) (ψ (Q (γ (-(N : ℝ))))) * B (ψ (Q (γ N))) X ^ 2 -
          B (ψ (Q (γ N))) (ψ (Q (γ N))) * B (ψ (Q (γ (-(N : ℝ))))) X ^ 2 -
          B X X * B (ψ (Q (γ (-(N : ℝ))))) (ψ (Q (γ N))) ^ 2) /
        (B (ψ (Q (γ (-(N : ℝ))))) (ψ (Q (γ (-(N : ℝ))))) * B (ψ (Q (γ N))) (ψ (Q (γ N))) -
          B (ψ (Q (γ (-(N : ℝ))))) (ψ (Q (γ N))) ^ 2) ≤ K) :
    B X e₂ ^ 2 ≤ K := by
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (ℝ × ℂ) × (ℝ × ℂ) → ℝ, Φ = fun p =>
      (B p.1 p.1 * B p.2 p.2 * B X X + 2 * B p.1 p.2 * B p.1 X * B p.2 X - B p.1 p.1 * B p.2 X ^ 2 -
        B p.2 p.2 * B p.1 X ^ 2 - B X X * B p.1 p.2 ^ 2) / (B p.1 p.1 * B p.2 p.2 - B p.1 p.2 ^ 2) :=
    ⟨_, rfl⟩
  have hψc : Continuous ψ := by
    rw [hψ]
    exact continuous_const.prodMk ((Complex.continuous_ofReal.comp (continuous_const.div
      (continuous_const.add (continuous_norm.pow 2))
      (fun z => (by positivity : (0 : ℝ) < 1 + ‖z‖ ^ 2).ne'))).mul continuous_id)
  have hψp : ψ ωp = (e₀.1 + e₁.1)⁻¹ • e₀ + (e₀.1 + e₁.1)⁻¹ • e₁ := by
    rw [hψ]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      field_simp
    · simp only [Prod.snd_add, Prod.smul_snd, Complex.real_smul]
      rw [hnp, hωp]
      push_cast
      field_simp
      ring
  have hψm : ψ ωm = (e₀.1 - e₁.1)⁻¹ • e₀ + (-(e₀.1 - e₁.1)⁻¹) • e₁ := by
    rw [hψ]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      field_simp
      ring
    · simp only [Prod.snd_add, Prod.smul_snd, Complex.real_smul]
      rw [hnm, hωm]
      push_cast
      field_simp
      ring
  obtain ⟨h00, h11, h22, h01, h02, h12⟩ := hon
  have h10 : B e₁ e₀ = 0 := (s07_mo_B_symm B hB _ _).trans h01
  have hBv : ∀ a b a' b' : ℝ, B (a • e₀ + b • e₁) (a' • e₀ + b' • e₁) = -(a * a') + b * b' := by
    intro a b a' b'
    rw [s07_mo_B_comb B hB, s07_mo_B_combr B hB, s07_mo_B_combr B hB, h00, h11, h01, h10]
    ring
  have hBe₂ : ∀ a b : ℝ, B (a • e₀ + b • e₁) e₂ = 0 := by
    intro a b
    rw [s07_mo_B_comb B hB, h02, h12]
    ring
  have hG2i : B (ψ ωm) (ψ ωm) * B (ψ ωp) (ψ ωp) - B (ψ ωm) (ψ ωp) ^ 2 ≠ 0 := by
    rw [hψm, hψp, hBv, hBv, hBv]
    have h1 : (e₀.1 - e₁.1)⁻¹ ≠ 0 := inv_ne_zero hkm.ne'
    have h2 : (e₀.1 + e₁.1)⁻¹ ≠ 0 := inv_ne_zero hkp.ne'
    intro h
    have : (2 * (e₀.1 - e₁.1)⁻¹ * (e₀.1 + e₁.1)⁻¹) ^ 2 = 0 := by linear_combination -h
    exact mul_ne_zero (mul_ne_zero two_ne_zero h1) h2 (pow_eq_zero_iff two_ne_zero |>.mp this)
  have hgi := s07_mo_gram B hB ⟨h00, h11, h22, h01, h02, h12⟩ (ψ ωm) (ψ ωp) X
    (by rw [hψm]; exact hBe₂ _ _) (by rw [hψp]; exact hBe₂ _ _)
  have hPhii : Φ (ψ ωm, ψ ωp) = B X e₂ ^ 2 := by
    rw [hΦ]
    dsimp only
    rw [← hgi, mul_div_assoc, div_self hG2i, mul_one]
  have hQp : Tendsto (fun N : ℕ => Q (γ N)) atTop (𝓝 ωp) := by
    have hγN : Tendsto (fun N : ℕ => γ N) atTop (𝓝[unitDisc] ωp) :=
      tendsto_nhdsWithin_iff.mpr ⟨hγtop.comp tendsto_natCast_atTop_atTop,
        Eventually.of_forall fun N => hγD _⟩
    exact (hbd ωp (mem_sphere_zero_iff_norm.mpr hnp)).comp hγN
  have hQm : Tendsto (fun N : ℕ => Q (γ (-(N : ℝ)))) atTop (𝓝 ωm) := by
    have hγN : Tendsto (fun N : ℕ => γ (-(N : ℝ))) atTop (𝓝[unitDisc] ωm) :=
      tendsto_nhdsWithin_iff.mpr ⟨hγbot.comp (tendsto_neg_atTop_atBot.comp
        tendsto_natCast_atTop_atTop), Eventually.of_forall fun N => hγD _⟩
    exact (hbd ωm (mem_sphere_zero_iff_norm.mpr hnm)).comp hγN
  have hFt : Tendsto (fun N : ℕ => (ψ (Q (γ (-(N : ℝ)))), ψ (Q (γ N)))) atTop
      (𝓝 (ψ ωm, ψ ωp)) :=
    ((hψc.tendsto _).comp hQm).prodMk_nhds ((hψc.tendsto _).comp hQp)
  have hΦc : ContinuousAt Φ (ψ ωm, ψ ωp) := by
    rw [hΦ]
    exact s07_mo_ratio_cont B hB X hG2i
  have hle : Φ (ψ ωm, ψ ωp) ≤ K :=
    le_of_tendsto (hΦc.tendsto.comp hFt) (eventually_atTop.mpr ⟨N₀, fun N hN => by
      rw [hΦ]
      exact hstep N hN⟩)
  rwa [hPhii] at hle

/-- Morse M4 (Steps 1–3): for a `(λ, c)`-quasi-isometry `Q` with boundary values `id` and an
orthonormal frame `(P x, e₁, e₂)` at `x`, `Q x` lies within `M_*` of the geodesic through `x` with
normal `e₂`: `|⟨P(Q x), e₂⟩| ≤ sinh M_*`. -/
theorem s07_mo_qi_normal (lam c : ℝ) (hlam : 1 ≤ lam) (hc : 0 ≤ c) (Q : ℂ → ℂ)
    (hQ : IsDiskQI Q lam c) (hbd : HasDiskBoundaryValues Q id) (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) (P : ℂ → ℝ × ℂ)
    (hP : ∀ p, P p = ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p))
    {x : ℂ} (hx : x ∈ unitDisc) {e₁ e₂ : ℝ × ℂ}
    (hon : B (P x) (P x) = -1 ∧ B e₁ e₁ = 1 ∧ B e₂ e₂ = 1 ∧ B (P x) e₁ = 0 ∧ B (P x) e₂ = 0 ∧
      B e₁ e₂ = 0) :
    |B (P (Q x)) e₂| ≤ Real.sinh (morseM lam c) := by
  have hS1 : 1 ≤ morseS lam c := by unfold morseS; linarith
  have hlam0 : 0 < lam := by linarith
  have hM0 : 0 ≤ morseM lam c := by
    have ha1 : 1 ≤ morseA1 lam c := by unfold morseA1; nlinarith [hS1]
    have hb0 : 0 ≤ morseB1 lam c := by
      unfold morseB1
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have hr0 : 0 ≤ morseR lam c := Real.arcosh_nonneg (by linarith)
    show 0 ≤ (2 * morseA1 lam c + 1) * morseR lam c + morseB1 lam c
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * morseA1 lam c + 1) hr0]
  have hsM : 0 ≤ Real.sinh (morseM lam c) := Real.sinh_nonneg_iff.mpr hM0
  -- the geodesic through `x` in direction `e₁`
  have he₀ : 0 < (P x).1 := (s07_mo_hyp B hB P hP hx).2.1
  obtain ⟨hkp, hkm, hnp, hnm, γ, hγD, hγ0, -, hγd, hγtop, hγbot⟩ :=
    s07_mo_line B hB P hP hon he₀
  have hγx : γ 0 = x := s07_mo_P_inj P hP (hγD 0) hx hγ0
  -- the images `q n = Q(γ n)` and the polygon through them
  obtain ⟨q, hq⟩ : ∃ q : ℤ → ℂ, q = fun n : ℤ => Q (γ (n : ℝ)) := ⟨_, rfl⟩
  have hqD : ∀ n, q n ∈ unitDisc := fun n => by rw [hq]; exact hQ.1 (hγD _)
  have hqup : ∀ m n : ℤ, diskDist (q m) (q n) ≤ lam * |(m : ℝ) - n| + c := by
    intro m n
    rw [hq]
    dsimp only
    rw [← hγd]
    exact (hQ.2 _ (hγD _) _ (hγD _)).2
  have hqlo : ∀ m n : ℤ, lam⁻¹ * |(m : ℝ) - n| - c ≤ diskDist (q m) (q n) := by
    intro m n
    rw [hq]
    dsimp only
    rw [← hγd]
    exact (hQ.2 _ (hγD _) _ (hγD _)).1
  have hqS : ∀ n, diskDist (q n) (q (n + 1)) ≤ morseS lam c := by
    intro n
    have h := hqup n (n + 1)
    have h1 : |(n : ℝ) - ((n + 1 : ℤ) : ℝ)| = 1 := by
      push_cast
      rw [show (n : ℝ) - (n + 1) = -1 by ring]
      norm_num
    rw [h1] at h
    unfold morseS
    linarith
  obtain ⟨η, hηD, hηn, hηL, hηq⟩ := s07_mo_polygon (by linarith : 0 ≤ morseS lam c) q hqD hqS
  -- the quasi-geodesic inequality
  have hqg : ∀ s t : ℝ, s ≤ t →
      morseS lam c * (t - s) ≤ morseA1 lam c * diskDist (η s) (η t) + morseB1 lam c := by
    intro s t hst
    have h1 := (hηq s).1
    have h2 := (hηq t).2
    have h3 := hqlo ⌊s⌋ ⌈t⌉
    have hfl : t - s ≤ ((⌈t⌉ : ℤ) : ℝ) - ⌊s⌋ := by linarith [Int.floor_le s, Int.le_ceil t]
    rw [abs_sub_comm, abs_of_nonneg (by linarith)] at h3
    have htri1 := s02_diskDist_triangle (hqD ⌊s⌋) (hηD s) (hqD ⌈t⌉)
    have htri2 := s02_diskDist_triangle (hηD s) (hηD t) (hqD ⌈t⌉)
    rw [s02_diskDist_comm (hqD _) (hηD s)] at htri1
    have hkey : lam⁻¹ * (t - s) - c ≤ 2 * morseS lam c + diskDist (η s) (η t) := by
      have : lam⁻¹ * (t - s) ≤ lam⁻¹ * (((⌈t⌉ : ℤ) : ℝ) - ⌊s⌋) :=
        mul_le_mul_of_nonneg_left hfl (inv_nonneg.mpr hlam0.le)
      linarith
    show morseS lam c * (t - s) ≤ lam * morseS lam c * diskDist (η s) (η t) +
      lam * morseS lam c * (2 * morseS lam c + c)
    have hLS : 0 ≤ lam * morseS lam c := mul_nonneg hlam0.le (by linarith)
    have hm := mul_le_mul_of_nonneg_left hkey hLS
    have he : lam * morseS lam c * (lam⁻¹ * (t - s) - c) =
        morseS lam c * (t - s) - lam * morseS lam c * c := by
      field_simp
    rw [he] at hm
    nlinarith [hm]
  have hη0 : η 0 = Q x := by
    have h := hηn 0
    rw [Int.cast_zero] at h
    rw [h, hq]
    dsimp only
    rw [Int.cast_zero, hγx]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ → ℝ × ℂ, ψ = fun z => ((1 : ℝ), ((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * z) :=
    ⟨_, rfl⟩
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (lam * c)
  have hle := s07_mo_qi_limit B hB ψ hψ hon hkp hkm rfl rfl hnp hnm Q hbd γ hγD hγtop hγbot
    (P (Q x)) (Real.sinh (morseM lam c) ^ 2) N₀ (fun N hN => by
      have h := s07_mo_qi_step lam c hlam hc B hB P hP ψ hψ q hqD hqlo η hηD hηn hηL hqg (Q x) hη0
        N (lt_of_lt_of_le hN₀ (by exact_mod_cast hN))
      rw [hq] at h
      simpa only [Int.cast_neg, Int.cast_natCast] using h)
  exact abs_le_of_sq_le_sq' hle hsM |> fun h => abs_le.mpr h

/-- Morse M4, the limit, for an arbitrary path: if the Gram ratios at `ψ(f(∓N))` are `≤ K` for all
large `N` and `f(±∞) = ω±` (the end points of the geodesic through `e₀` in direction `e₁`), then
`⟨X, e₂⟩² ≤ K`.  (`s07_mo_qi_limit` is the case `f = Q ∘ γ` with boundary values `id`.) -/
theorem s07_mo_qi_limit_gen (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re)
    (ψ : ℂ → ℝ × ℂ) (hψ : ψ = fun z => ((1 : ℝ), ((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * z))
    {e₀ e₁ e₂ : ℝ × ℂ}
    (hon : B e₀ e₀ = -1 ∧ B e₁ e₁ = 1 ∧ B e₂ e₂ = 1 ∧ B e₀ e₁ = 0 ∧ B e₀ e₂ = 0 ∧ B e₁ e₂ = 0)
    (hkp : 0 < e₀.1 + e₁.1) (hkm : 0 < e₀.1 - e₁.1) {ωp ωm : ℂ}
    (hωp : ωp = (e₀.2 + e₁.2) / ((e₀.1 + e₁.1 : ℝ) : ℂ))
    (hωm : ωm = (e₀.2 - e₁.2) / ((e₀.1 - e₁.1 : ℝ) : ℂ)) (hnp : ‖ωp‖ = 1) (hnm : ‖ωm‖ = 1)
    (f : ℝ → ℂ) (htop : Tendsto f atTop (𝓝 ωp)) (hbot : Tendsto f atBot (𝓝 ωm))
    (X : ℝ × ℂ) (K : ℝ)
    (N₀ : ℕ) (hstep : ∀ N : ℕ, N₀ ≤ N →
      (B (ψ (f (-(N : ℝ)))) (ψ (f (-(N : ℝ)))) * B (ψ (f N)) (ψ (f N)) * B X X +
          2 * B (ψ (f (-(N : ℝ)))) (ψ (f N)) * B (ψ (f (-(N : ℝ)))) X *
            B (ψ (f N)) X -
          B (ψ (f (-(N : ℝ)))) (ψ (f (-(N : ℝ)))) * B (ψ (f N)) X ^ 2 -
          B (ψ (f N)) (ψ (f N)) * B (ψ (f (-(N : ℝ)))) X ^ 2 -
          B X X * B (ψ (f (-(N : ℝ)))) (ψ (f N)) ^ 2) /
        (B (ψ (f (-(N : ℝ)))) (ψ (f (-(N : ℝ)))) * B (ψ (f N)) (ψ (f N)) -
          B (ψ (f (-(N : ℝ)))) (ψ (f N)) ^ 2) ≤ K) :
    B X e₂ ^ 2 ≤ K := by
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (ℝ × ℂ) × (ℝ × ℂ) → ℝ, Φ = fun p =>
      (B p.1 p.1 * B p.2 p.2 * B X X + 2 * B p.1 p.2 * B p.1 X * B p.2 X - B p.1 p.1 * B p.2 X ^ 2 -
        B p.2 p.2 * B p.1 X ^ 2 - B X X * B p.1 p.2 ^ 2) / (B p.1 p.1 * B p.2 p.2 - B p.1 p.2 ^ 2) :=
    ⟨_, rfl⟩
  have hψc : Continuous ψ := by
    rw [hψ]
    exact continuous_const.prodMk ((Complex.continuous_ofReal.comp (continuous_const.div
      (continuous_const.add (continuous_norm.pow 2))
      (fun z => (by positivity : (0 : ℝ) < 1 + ‖z‖ ^ 2).ne'))).mul continuous_id)
  have hψp : ψ ωp = (e₀.1 + e₁.1)⁻¹ • e₀ + (e₀.1 + e₁.1)⁻¹ • e₁ := by
    rw [hψ]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      field_simp
    · simp only [Prod.snd_add, Prod.smul_snd, Complex.real_smul]
      rw [hnp, hωp]
      push_cast
      field_simp
      ring
  have hψm : ψ ωm = (e₀.1 - e₁.1)⁻¹ • e₀ + (-(e₀.1 - e₁.1)⁻¹) • e₁ := by
    rw [hψ]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      field_simp
      ring
    · simp only [Prod.snd_add, Prod.smul_snd, Complex.real_smul]
      rw [hnm, hωm]
      push_cast
      field_simp
      ring
  obtain ⟨h00, h11, h22, h01, h02, h12⟩ := hon
  have h10 : B e₁ e₀ = 0 := (s07_mo_B_symm B hB _ _).trans h01
  have hBv : ∀ a b a' b' : ℝ, B (a • e₀ + b • e₁) (a' • e₀ + b' • e₁) = -(a * a') + b * b' := by
    intro a b a' b'
    rw [s07_mo_B_comb B hB, s07_mo_B_combr B hB, s07_mo_B_combr B hB, h00, h11, h01, h10]
    ring
  have hBe₂ : ∀ a b : ℝ, B (a • e₀ + b • e₁) e₂ = 0 := by
    intro a b
    rw [s07_mo_B_comb B hB, h02, h12]
    ring
  have hG2i : B (ψ ωm) (ψ ωm) * B (ψ ωp) (ψ ωp) - B (ψ ωm) (ψ ωp) ^ 2 ≠ 0 := by
    rw [hψm, hψp, hBv, hBv, hBv]
    have h1 : (e₀.1 - e₁.1)⁻¹ ≠ 0 := inv_ne_zero hkm.ne'
    have h2 : (e₀.1 + e₁.1)⁻¹ ≠ 0 := inv_ne_zero hkp.ne'
    intro h
    have : (2 * (e₀.1 - e₁.1)⁻¹ * (e₀.1 + e₁.1)⁻¹) ^ 2 = 0 := by linear_combination -h
    exact mul_ne_zero (mul_ne_zero two_ne_zero h1) h2 (pow_eq_zero_iff two_ne_zero |>.mp this)
  have hgi := s07_mo_gram B hB ⟨h00, h11, h22, h01, h02, h12⟩ (ψ ωm) (ψ ωp) X
    (by rw [hψm]; exact hBe₂ _ _) (by rw [hψp]; exact hBe₂ _ _)
  have hPhii : Φ (ψ ωm, ψ ωp) = B X e₂ ^ 2 := by
    rw [hΦ]
    dsimp only
    rw [← hgi, mul_div_assoc, div_self hG2i, mul_one]
  have hQp : Tendsto (fun N : ℕ => f N) atTop (𝓝 ωp) :=
    htop.comp tendsto_natCast_atTop_atTop
  have hQm : Tendsto (fun N : ℕ => f (-(N : ℝ))) atTop (𝓝 ωm) :=
    hbot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hFt : Tendsto (fun N : ℕ => (ψ (f (-(N : ℝ))), ψ (f N))) atTop
      (𝓝 (ψ ωm, ψ ωp)) :=
    ((hψc.tendsto _).comp hQm).prodMk_nhds ((hψc.tendsto _).comp hQp)
  have hΦc : ContinuousAt Φ (ψ ωm, ψ ωp) := by
    rw [hΦ]
    exact s07_mo_ratio_cont B hB X hG2i
  have hle : Φ (ψ ωm, ψ ωp) ≤ K :=
    le_of_tendsto (hΦc.tendsto.comp hFt) (eventually_atTop.mpr ⟨N₀, fun N hN => by
      rw [hΦ]
      exact hstep N hN⟩)
  rwa [hPhii] at hle

/-- Morse M4 for arbitrary end points: if `Q` is a `(λ, c)`-quasi-isometry and `γ` a unit-speed
geodesic with `Q(γ(±∞)) = ω±`, the end points of the geodesic through `e₀` in direction `e₁`
(an orthonormal frame `(e₀, e₁, e₂)`, `e₀` future-pointing), then `Q ∘ γ` stays within `M_*` of that
geodesic: `|⟨P(Q(γ τ)), e₂⟩| ≤ sinh M_*`.  (`s07_mo_qi_normal` is the case `e₀ = P x`, boundary
values `id`.) -/
theorem s07_mo_qi_normal_gen (lam c : ℝ) (hlam : 1 ≤ lam) (hc : 0 ≤ c) (Q : ℂ → ℂ)
    (hQ : IsDiskQI Q lam c) (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) (P : ℂ → ℝ × ℂ)
    (hP : ∀ p, P p = ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p))
    (γ : ℝ → ℂ) (hγD : ∀ τ, γ τ ∈ unitDisc) (hγd : ∀ s t, diskDist (γ s) (γ t) = |s - t|)
    {e₀ e₁ e₂ : ℝ × ℂ}
    (hon : B e₀ e₀ = -1 ∧ B e₁ e₁ = 1 ∧ B e₂ e₂ = 1 ∧ B e₀ e₁ = 0 ∧ B e₀ e₂ = 0 ∧ B e₁ e₂ = 0)
    (he₀ : 0 < e₀.1)
    (htop : Tendsto (fun τ => Q (γ τ)) atTop (𝓝 ((e₀.2 + e₁.2) / ((e₀.1 + e₁.1 : ℝ) : ℂ))))
    (hbot : Tendsto (fun τ => Q (γ τ)) atBot (𝓝 ((e₀.2 - e₁.2) / ((e₀.1 - e₁.1 : ℝ) : ℂ)))) :
    ∀ τ, |B (P (Q (γ τ))) e₂| ≤ Real.sinh (morseM lam c) := by
  intro τ
  have hS1 : 1 ≤ morseS lam c := by unfold morseS; linarith
  have hlam0 : 0 < lam := by linarith
  have hM0 : 0 ≤ morseM lam c := by
    have ha1 : 1 ≤ morseA1 lam c := by unfold morseA1; nlinarith [hS1]
    have hb0 : 0 ≤ morseB1 lam c := by
      unfold morseB1
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have hr0 : 0 ≤ morseR lam c := Real.arcosh_nonneg (by linarith)
    show 0 ≤ (2 * morseA1 lam c + 1) * morseR lam c + morseB1 lam c
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * morseA1 lam c + 1) hr0]
  have hsM : 0 ≤ Real.sinh (morseM lam c) := Real.sinh_nonneg_iff.mpr hM0
  obtain ⟨hkp, hkm, hnp, hnm, -⟩ := s07_mo_line B hB P hP hon he₀
  -- the geodesic shifted by `τ`, and its image `f = Q ∘ γ'`
  obtain ⟨γ', hγ'⟩ : ∃ γ' : ℝ → ℂ, γ' = fun s => γ (s + τ) := ⟨_, rfl⟩
  have hγ'D : ∀ s, γ' s ∈ unitDisc := fun s => by rw [hγ']; exact hγD _
  have hγ'd : ∀ s t, diskDist (γ' s) (γ' t) = |s - t| := by
    intro s t
    rw [hγ']
    dsimp only
    rw [hγd, show s + τ - (t + τ) = s - t by ring]
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℂ, f = fun s => Q (γ' s) := ⟨_, rfl⟩
  have hftop : Tendsto f atTop (𝓝 ((e₀.2 + e₁.2) / ((e₀.1 + e₁.1 : ℝ) : ℂ))) := by
    rw [hf, hγ']
    exact htop.comp (tendsto_atTop_add_const_right _ τ tendsto_id)
  have hfbot : Tendsto f atBot (𝓝 ((e₀.2 - e₁.2) / ((e₀.1 - e₁.1 : ℝ) : ℂ))) := by
    rw [hf, hγ']
    exact hbot.comp (tendsto_atBot_add_const_right _ τ tendsto_id)
  -- the images `q n = f n` and the polygon through them
  obtain ⟨q, hq⟩ : ∃ q : ℤ → ℂ, q = fun n : ℤ => f (n : ℝ) := ⟨_, rfl⟩
  have hqD : ∀ n, q n ∈ unitDisc := fun n => by rw [hq, hf]; exact hQ.1 (hγ'D _)
  have hqup : ∀ m n : ℤ, diskDist (q m) (q n) ≤ lam * |(m : ℝ) - n| + c := by
    intro m n
    rw [hq, hf]
    dsimp only
    rw [← hγ'd]
    exact (hQ.2 _ (hγ'D _) _ (hγ'D _)).2
  have hqlo : ∀ m n : ℤ, lam⁻¹ * |(m : ℝ) - n| - c ≤ diskDist (q m) (q n) := by
    intro m n
    rw [hq, hf]
    dsimp only
    rw [← hγ'd]
    exact (hQ.2 _ (hγ'D _) _ (hγ'D _)).1
  have hqS : ∀ n, diskDist (q n) (q (n + 1)) ≤ morseS lam c := by
    intro n
    have h := hqup n (n + 1)
    have h1 : |(n : ℝ) - ((n + 1 : ℤ) : ℝ)| = 1 := by
      push_cast
      rw [show (n : ℝ) - (n + 1) = -1 by ring]
      norm_num
    rw [h1] at h
    unfold morseS
    linarith
  obtain ⟨η, hηD, hηn, hηL, hηq⟩ := s07_mo_polygon (by linarith : 0 ≤ morseS lam c) q hqD hqS
  -- the quasi-geodesic inequality
  have hqg : ∀ s t : ℝ, s ≤ t →
      morseS lam c * (t - s) ≤ morseA1 lam c * diskDist (η s) (η t) + morseB1 lam c := by
    intro s t hst
    have h1 := (hηq s).1
    have h2 := (hηq t).2
    have h3 := hqlo ⌊s⌋ ⌈t⌉
    have hfl : t - s ≤ ((⌈t⌉ : ℤ) : ℝ) - ⌊s⌋ := by linarith [Int.floor_le s, Int.le_ceil t]
    rw [abs_sub_comm, abs_of_nonneg (by linarith)] at h3
    have htri1 := s02_diskDist_triangle (hqD ⌊s⌋) (hηD s) (hqD ⌈t⌉)
    have htri2 := s02_diskDist_triangle (hηD s) (hηD t) (hqD ⌈t⌉)
    rw [s02_diskDist_comm (hqD _) (hηD s)] at htri1
    have hkey : lam⁻¹ * (t - s) - c ≤ 2 * morseS lam c + diskDist (η s) (η t) := by
      have : lam⁻¹ * (t - s) ≤ lam⁻¹ * (((⌈t⌉ : ℤ) : ℝ) - ⌊s⌋) :=
        mul_le_mul_of_nonneg_left hfl (inv_nonneg.mpr hlam0.le)
      linarith
    show morseS lam c * (t - s) ≤ lam * morseS lam c * diskDist (η s) (η t) +
      lam * morseS lam c * (2 * morseS lam c + c)
    have hLS : 0 ≤ lam * morseS lam c := mul_nonneg hlam0.le (by linarith)
    have hm := mul_le_mul_of_nonneg_left hkey hLS
    have he : lam * morseS lam c * (lam⁻¹ * (t - s) - c) =
        morseS lam c * (t - s) - lam * morseS lam c * c := by
      field_simp
    rw [he] at hm
    nlinarith [hm]
  have hη0 : η 0 = Q (γ τ) := by
    have h := hηn 0
    rw [Int.cast_zero] at h
    rw [h, hq, hf, hγ']
    dsimp only
    rw [Int.cast_zero, zero_add]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ → ℝ × ℂ, ψ = fun z => ((1 : ℝ), ((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * z) :=
    ⟨_, rfl⟩
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (lam * c)
  have hle := s07_mo_qi_limit_gen B hB ψ hψ hon hkp hkm rfl rfl hnp hnm f hftop hfbot
    (P (Q (γ τ))) (Real.sinh (morseM lam c) ^ 2) N₀ (fun N hN => by
      have h := s07_mo_qi_step lam c hlam hc B hB P hP ψ hψ q hqD hqlo η hηD hηn hηL hqg
        (Q (γ τ)) hη0 N (lt_of_lt_of_le hN₀ (by exact_mod_cast hN))
      rw [hq] at h
      simpa only [Int.cast_neg, Int.cast_natCast] using h)
  exact abs_le_of_sq_le_sq' hle hsM |> fun h => abs_le.mpr h

/-- Lemma 7.3, `lem:morse` (`sec07-transfer.tex:155`): a `(λ, c)`-quasi-isometry `Q` of `𝔻`
with boundary values `id` satisfies `d_𝔻(Qx, x) ≤ D_*(λ, c)`. -/
theorem lem_morse (lam c : ℝ) (hlam : 1 ≤ lam) (hc : 0 ≤ c) (Q : ℂ → ℂ)
    (hQ : IsDiskQI Q lam c) (hbd : HasDiskBoundaryValues Q id) :
    ∀ x ∈ unitDisc, diskDist (Q x) x ≤ morseD lam c := by
  intro x hx
  set B : ℝ × ℂ → ℝ × ℂ → ℝ := fun X Y => -X.1 * Y.1 + (X.2 * conj Y.2).re with hBdef
  set P : ℂ → ℝ × ℂ := fun p =>
    ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p) with hPdef
  have hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re := fun _ _ => rfl
  have hP : ∀ p, P p =
      ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p) := fun _ => rfl
  have hBsymm : ∀ X Y, B X Y = B Y X := by
    intro X Y
    rw [hB, hB, Complex.mul_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.conj_re, Complex.conj_im]
    ring
  obtain ⟨b, hb, hbx⟩ : ∃ b ∈ unitDisc, b ≠ x := by
    by_cases h0 : x = 0
    · refine ⟨1 / 2, ?_, ?_⟩
      · show (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1
        rw [mem_ball_zero_iff]
        norm_num
      · rw [h0]
        norm_num
    · exact ⟨0, mem_ball_self one_pos, fun h => h0 h.symm⟩
  obtain ⟨e₁, e₂, hon, -⟩ := s07_mo_frame B hB P hP hx hb hbx.symm
  obtain ⟨h00, h11, h22, h01, h02, h12⟩ := hon
  have hQx : Q x ∈ unitDisc := hQ.1 hx
  have k1 := s07_mo_qi_normal lam c hlam hc Q hQ hbd B hB P hP hx ⟨h00, h11, h22, h01, h02, h12⟩
  have k2 := s07_mo_qi_normal lam c hlam hc Q hQ hbd B hB P hP hx
    ⟨h00, h22, h11, h02, h01, (hBsymm e₂ e₁).trans h12⟩
  obtain ⟨hQQ, -, hdist⟩ := s07_mo_hyp B hB P hP hQx
  have hpar := s07_mo_parseval B hB ⟨h00, h11, h22, h01, h02, h12⟩ (P (Q x)) (P (Q x))
  have hcd : diskCoshDist (Q x) x = -B (P (Q x)) (P x) := hdist x hx
  have hsM : 0 ≤ Real.sinh (morseM lam c) := (abs_nonneg _).trans k1
  have hD0 : 0 ≤ diskDist (Q x) x := s02_diskDist_nonneg hQx hx
  -- `cosh D = -⟨P(Qx), P x⟩`, hence `sinh² D = ⟨P(Qx), e₁⟩² + ⟨P(Qx), e₂⟩²`
  have hcosh : Real.cosh (diskDist (Q x) x) = -B (P (Q x)) (P x) := by
    have h1 : 1 ≤ diskCoshDist (Q x) x := by
      have hu1 : ‖Q x‖ < 1 := mem_ball_zero_iff.mp hQx
      have hv1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
      have hu2 : 0 < 1 - ‖Q x‖ ^ 2 := by nlinarith [norm_nonneg (Q x)]
      have hv2 : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
      unfold diskCoshDist
      have : 0 ≤ 2 * ‖Q x - x‖ ^ 2 / ((1 - ‖Q x‖ ^ 2) * (1 - ‖x‖ ^ 2)) := by positivity
      linarith
    show Real.cosh (Real.arcosh (diskCoshDist (Q x) x)) = _
    rw [Real.cosh_arcosh h1, hcd]
  have hsq : Real.sinh (diskDist (Q x) x) ^ 2 ≤ (Real.sqrt 2 * Real.sinh (morseM lam c)) ^ 2 := by
    have hc2 := Real.cosh_sq (diskDist (Q x) x)
    have hs : B (P (Q x)) (P x) = B (P x) (P (Q x)) := hBsymm _ _
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have a1 : B (P (Q x)) e₁ ^ 2 ≤ Real.sinh (morseM lam c) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) k2 2
    have a2 : B (P (Q x)) e₂ ^ 2 ≤ Real.sinh (morseM lam c) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) k1 2
    have h3 : Real.cosh (diskDist (Q x) x) ^ 2 = B (P (Q x)) (P x) ^ 2 := by
      rw [hcosh]
      ring
    rw [hQQ] at hpar
    have e : Real.sinh (diskDist (Q x) x) ^ 2 = B (P (Q x)) e₁ ^ 2 + B (P (Q x)) e₂ ^ 2 := by
      linear_combination (-1 : ℝ) * hc2 + h3 + hpar
    linarith
  have hsD : Real.sinh (diskDist (Q x) x) ≤ Real.sqrt 2 * Real.sinh (morseM lam c) :=
    abs_le_of_sq_le_sq' hsq (by positivity) |>.2
  calc diskDist (Q x) x = Real.arsinh (Real.sinh (diskDist (Q x) x)) :=
        (Real.arsinh_sinh _).symm
    _ ≤ Real.arsinh (Real.sqrt 2 * Real.sinh (morseM lam c)) := Real.arsinh_le_arsinh.2 hsD
    _ = morseD lam c := rfl

/-- `F` is a homeomorphism of the closed disk `𝔻̄` onto itself (a continuous bijection of a
compact space onto a Hausdorff space). -/
def IsClosedDiskHomeo (F : ℂ → ℂ) : Prop :=
  BijOn F (closedBall 0 1) (closedBall 0 1) ∧ ContinuousOn F (closedBall 0 1)

/-- `F|_𝔻` is `L`-bi-Lipschitz for `d_𝔻`. -/
def IsDiskBiLip (F : ℂ → ℂ) (L : ℝ) : Prop :=
  ∀ x ∈ unitDisc, ∀ y ∈ unitDisc,
    diskDist (F x) (F y) ≤ L * diskDist x y ∧ diskDist x y ≤ L * diskDist (F x) (F y)

/-- `cosh d_𝔻(a, 0) = (1 + |a|²)/(1 - |a|²)`. -/
theorem s07_sb_cosh0 {a : ℂ} (ha : a ∈ unitDisc) :
    diskCoshDist a 0 = (1 + ‖a‖ ^ 2) / (1 - ‖a‖ ^ 2) := by
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have ha2 : 1 - ‖a‖ ^ 2 ≠ 0 := (by nlinarith [norm_nonneg a] : (0 : ℝ) < 1 - ‖a‖ ^ 2).ne'
  unfold diskCoshDist
  rw [sub_zero, norm_zero, zero_pow two_ne_zero, sub_zero, mul_one, eq_div_iff ha2, add_mul,
    div_mul_cancel₀ _ ha2]
  ring

/-- A point at `d_𝔻`-distance `≤ R` from `0` has `1 - |a|² ≥ 2/(cosh R + 1)`. -/
theorem s07_sb_far (R : ℝ) {a : ℂ} (ha : a ∈ unitDisc) (h : diskDist a 0 ≤ R) :
    2 / (Real.cosh R + 1) ≤ 1 - ‖a‖ ^ 2 := by
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have ha2 : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hd0 := s02_diskDist_nonneg ha h0
  have hc : Real.cosh (diskDist a 0) ≤ Real.cosh R :=
    Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg hd0, abs_of_nonneg (hd0.trans h)]; exact h)
  rw [s07_mo_cosh_dist ha h0, s07_sb_cosh0 ha, div_le_iff₀ ha2] at hc
  have hR := Real.one_le_cosh R
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- A point with `|a|² ≤ s < 1` has `d_𝔻(a, 0) ≤ arcosh((1 + s)/(1 - s))`. -/
theorem s07_sb_near {s : ℝ} (hs1 : s < 1) {a : ℂ} (ha : a ∈ unitDisc) (h : ‖a‖ ^ 2 ≤ s) :
    diskDist a 0 ≤ Real.arcosh ((1 + s) / (1 - s)) := by
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have ha2 : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hs2 : 0 < 1 - s := by linarith
  have hs0 : 0 ≤ s := (sq_nonneg ‖a‖).trans h
  show Real.arcosh (diskCoshDist a 0) ≤ _
  rw [s07_sb_cosh0 ha, Real.arcosh_le_arcosh (div_pos (by positivity) ha2)
    (div_pos (by linarith) hs2), div_le_div_iff₀ ha2 hs2]
  nlinarith [norm_nonneg a]

/-- SB1: a homeomorphism of `𝔻̄` that is bi-Lipschitz for `d_𝔻` on `𝔻` maps `𝔻` into `𝔻`
(a point of `𝔻` sent to `∂𝔻` would have `d_𝔻`-junk distance `0` to all other images), and
`1 ≤ L_F`. -/
theorem s07_sb_maps {F : ℂ → ℂ} {LF : ℝ} (hF : IsClosedDiskHomeo F) (hFL : IsDiskBiLip F LF) :
    MapsTo F unitDisc unitDisc ∧ 1 ≤ LF := by
  have hcl : ∀ x ∈ unitDisc, ‖F x‖ ≤ 1 := fun x hx =>
    mem_closedBall_zero_iff.mp (hF.1.mapsTo (ball_subset_closedBall hx))
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hh : (1 / 2 : ℂ) ∈ unitDisc := by
    show (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff]
    norm_num
  -- distinct points of `𝔻` are at positive distance
  have hpos : ∀ x ∈ unitDisc, ∀ y ∈ unitDisc, x ≠ y → 0 < diskDist x y := by
    intro x hx y hy hxy
    show 0 < Real.arcosh (diskCoshDist x y)
    apply Real.arcosh_pos
    have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
    have hy1 : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
    have hx2 : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    have hy2 : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
    have hn : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    unfold diskCoshDist
    have : 0 < 2 * ‖x - y‖ ^ 2 / ((1 - ‖x‖ ^ 2) * (1 - ‖y‖ ^ 2)) :=
      div_pos (mul_pos two_pos (pow_pos hn 2)) (mul_pos hx2 hy2)
    linarith
  -- images of points of `𝔻` lie in `𝔻̄`, so their `diskCoshDist` is `≥ 1`
  have hnn : ∀ x ∈ unitDisc, ∀ y ∈ unitDisc, 0 ≤ diskDist (F x) (F y) := by
    intro x hx y hy
    apply Real.arcosh_nonneg
    have h1 : 0 ≤ 1 - ‖F x‖ ^ 2 := by nlinarith [norm_nonneg (F x), hcl x hx]
    have h2 : 0 ≤ 1 - ‖F y‖ ^ 2 := by nlinarith [norm_nonneg (F y), hcl y hy]
    unfold diskCoshDist
    have : 0 ≤ 2 * ‖F x - F y‖ ^ 2 / ((1 - ‖F x‖ ^ 2) * (1 - ‖F y‖ ^ 2)) :=
      div_nonneg (by positivity) (mul_nonneg h1 h2)
    linarith
  have hLF : 1 ≤ LF := by
    have hd := hpos 0 h0 (1 / 2) hh (by norm_num)
    obtain ⟨h1, h2⟩ := hFL 0 h0 (1 / 2) hh
    have h3 := hnn 0 h0 (1 / 2) hh
    have hL0 : 0 ≤ LF := by
      by_contra hneg
      push_neg at hneg
      have : LF * diskDist 0 (1 / 2) < 0 := mul_neg_of_neg_of_pos hneg hd
      linarith
    have h4 : diskDist 0 (1 / 2) ≤ LF * (LF * diskDist 0 (1 / 2)) :=
      h2.trans (mul_le_mul_of_nonneg_left h1 hL0)
    by_contra hlt
    push_neg at hlt
    have h5 : LF * LF < 1 := by nlinarith
    have h6 : LF * LF * diskDist 0 (1 / 2) < 1 * diskDist 0 (1 / 2) :=
      mul_lt_mul_of_pos_right h5 hd
    rw [mul_assoc] at h6
    linarith
  refine ⟨fun x hx => ?_, hLF⟩
  rcases (hcl x hx).lt_or_eq with h | h
  · exact mem_ball_zero_iff.mpr h
  · -- This branch cannot occur: `|F x| = 1` makes the `diskCoshDist` denominator vanish, so the
    -- junk value `d_𝔻(F x, F y) = arcosh 1 = 0` and bi-Lipschitz would force `d_𝔻(x, y) ≤ 0`
    -- for some `y ≠ x` in `𝔻`.
    exfalso
    obtain ⟨y, hy, hyx⟩ : ∃ y ∈ unitDisc, y ≠ x := by
      by_cases hx0 : x = 0
      · exact ⟨1 / 2, hh, by rw [hx0]; norm_num⟩
      · exact ⟨0, h0, fun h' => hx0 h'.symm⟩
    have hz : diskDist (F x) (F y) = 0 := by
      show Real.arcosh (diskCoshDist (F x) (F y)) = 0
      have : diskCoshDist (F x) (F y) = 1 := by
        unfold diskCoshDist
        rw [h]
        simp
      rw [this, Real.arcosh_zero]
    have h1 := (hFL x hx y hy).2
    rw [hz, mul_zero] at h1
    have h2 := hpos x hx y hy hyx.symm
    linarith

/-- SB2: `F(𝔻) = 𝔻`. If `w = F ζ ∈ 𝔻` with `|ζ| = 1`, then for `x_n → ζ` in `𝔻` the points `F x_n`
stay `d_𝔻`-bounded, hence so do the `x_n`, contradicting `|x_n| → 1`. -/
theorem s07_sb_surj {F : ℂ → ℂ} {LF : ℝ} (hF : IsClosedDiskHomeo F) (hFL : IsDiskBiLip F LF) :
    SurjOn F unitDisc unitDisc := by
  obtain ⟨hmaps, hLF⟩ := s07_sb_maps hF hFL
  intro w hw
  obtain ⟨ζ, hζ, hζw⟩ := hF.1.surjOn (ball_subset_closedBall hw)
  rcases (mem_closedBall_zero_iff.mp hζ).lt_or_eq with h | h
  · exact ⟨ζ, mem_ball_zero_iff.mpr h, hζw⟩
  exfalso
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (1 + ‖w‖) / 2 := ⟨_, rfl⟩
  have hr1 : r < 1 := by rw [hr]; linarith
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hcont : Tendsto F (𝓝[unitDisc] ζ) (𝓝 w) := by
    rw [← hζw]
    exact (hF.2 ζ hζ).tendsto.mono_left (nhdsWithin_mono _ ball_subset_closedBall)
  have hev1 : ∀ᶠ x in 𝓝[unitDisc] ζ, ‖F x‖ < r :=
    hcont.norm.eventually (gt_mem_nhds (by rw [hr]; linarith))
  have hF0 := hmaps h0
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R =
      LF * (Real.arcosh ((1 + r ^ 2) / (1 - r ^ 2)) + diskDist (0 : ℂ) (F 0)) := ⟨_, rfl⟩
  have hbound : ∀ x ∈ unitDisc, ‖F x‖ < r → 2 / (Real.cosh R + 1) ≤ 1 - ‖x‖ ^ 2 := by
    intro x hx hFx
    apply s07_sb_far R hx
    have h1 : diskDist (F x) 0 ≤ Real.arcosh ((1 + r ^ 2) / (1 - r ^ 2)) :=
      s07_sb_near (by nlinarith) (hmaps hx) (pow_le_pow_left₀ (norm_nonneg _) hFx.le 2)
    have h2 := s02_diskDist_triangle (hmaps hx) h0 hF0
    have h3 := (hFL x hx 0 h0).2
    rw [hR]
    calc diskDist x 0 ≤ LF * diskDist (F x) (F 0) := h3
      _ ≤ LF * (Real.arcosh ((1 + r ^ 2) / (1 - r ^ 2)) + diskDist 0 (F 0)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hδ : 0 < 2 / (Real.cosh R + 1) := by
    have := Real.one_le_cosh R
    exact div_pos two_pos (by linarith)
  have hnorm : Tendsto (fun x : ℂ => ‖x‖ ^ 2) (𝓝[unitDisc] ζ) (𝓝 1) := by
    have h' : Tendsto (fun x : ℂ => ‖x‖ ^ 2) (𝓝 ζ) (𝓝 (‖ζ‖ ^ 2)) :=
      (continuous_norm.pow 2).tendsto ζ
    rw [h, one_pow] at h'
    exact h'.mono_left nhdsWithin_le_nhds
  have hev2 : ∀ᶠ x in 𝓝[unitDisc] ζ, 1 - 2 / (Real.cosh R + 1) < ‖x‖ ^ 2 :=
    hnorm.eventually (lt_mem_nhds (by linarith))
  haveI : (𝓝[unitDisc] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (by
    rw [show unitDisc = ball (0 : ℂ) 1 from rfl, closure_ball (0 : ℂ) one_ne_zero]
    exact hζ)
  obtain ⟨x, hx1, hx2, hxD⟩ := (hev1.and (hev2.and self_mem_nhdsWithin)).exists
  have := hbound x hxD hx1
  linarith

/-- SB2′: `F(∂𝔻) ⊆ ∂𝔻` (from SB2 and injectivity on `𝔻̄`). -/
theorem s07_sb_sphere {F : ℂ → ℂ} {LF : ℝ} (hF : IsClosedDiskHomeo F) (hFL : IsDiskBiLip F LF) :
    MapsTo F (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1) := by
  intro ζ hζ
  have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
  have hcl : ζ ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hζ
  rcases (mem_closedBall_zero_iff.mp (hF.1.mapsTo hcl)).lt_or_eq with h | h
  · exfalso
    obtain ⟨x, hx, hxζ⟩ := s07_sb_surj hF hFL (mem_ball_zero_iff.mpr h)
    have hxe := hF.1.injOn (ball_subset_closedBall hx) hcl hxζ
    have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
    rw [hxe] at hx1
    linarith
  · exact mem_sphere_zero_iff_norm.mpr h

/-- SB3: the inverse `G = F⁻¹` on `𝔻`, continuous at the boundary points `F ζ` (the inverse of a
continuous bijection of the compact `𝔻̄` is continuous). -/
theorem s07_sb_inv {F : ℂ → ℂ} {LF : ℝ} (hF : IsClosedDiskHomeo F) (hFL : IsDiskBiLip F LF) :
    ∃ G : ℂ → ℂ, MapsTo G unitDisc unitDisc ∧ (∀ w ∈ unitDisc, F (G w) = w) ∧
      (∀ z ∈ unitDisc, G (F z) = z) ∧
      ∀ ζ ∈ sphere (0 : ℂ) 1, Tendsto G (𝓝[unitDisc] (F ζ)) (𝓝 ζ) := by
  have hsurj := s07_sb_surj hF hFL
  have hinj := hF.1.injOn
  have hG : ∀ w ∈ unitDisc, Function.invFunOn F (closedBall (0 : ℂ) 1) w ∈ closedBall (0 : ℂ) 1 ∧
      F (Function.invFunOn F (closedBall (0 : ℂ) 1) w) = w := by
    intro w hw
    obtain ⟨x, hx, hxw⟩ := hsurj hw
    exact Function.invFunOn_pos ⟨x, ball_subset_closedBall hx, hxw⟩
  refine ⟨Function.invFunOn F (closedBall (0 : ℂ) 1), fun w hw => ?_, fun w hw => (hG w hw).2,
    fun z hz => hinj.leftInvOn_invFunOn (ball_subset_closedBall hz), fun ζ hζ => ?_⟩
  · obtain ⟨x, hx, hxw⟩ := hsurj hw
    obtain ⟨hG1, hG2⟩ := hG w hw
    rw [hinj hG1 (ball_subset_closedBall hx) (hG2.trans hxw.symm)]
    exact hx
  · have hcl : ζ ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hζ
    rw [_root_.tendsto_nhds]
    intro U hU hζU
    have hKc : IsCompact (F '' (closedBall (0 : ℂ) 1 \ U)) :=
      ((isCompact_closedBall (0 : ℂ) 1).diff hU).image_of_continuousOn (hF.2.mono diff_subset)
    have hnot : F ζ ∉ F '' (closedBall (0 : ℂ) 1 \ U) := by
      rintro ⟨x, ⟨hx, hxU⟩, hxζ⟩
      exact hxU (by rw [hinj hx hcl hxζ]; exact hζU)
    have hnhds : (F '' (closedBall (0 : ℂ) 1 \ U))ᶜ ∈ 𝓝 (F ζ) :=
      hKc.isClosed.isOpen_compl.mem_nhds hnot
    filter_upwards [nhdsWithin_le_nhds hnhds, self_mem_nhdsWithin] with w hwK hwD
    obtain ⟨hGw, hFGw⟩ := hG w hwD
    by_contra hGU
    exact hwK ⟨_, ⟨hGw, hGU⟩, hFGw⟩

/-- SB4: a `(L, c)`-quasi-isometry of `𝔻` with a boundary limit on `∂𝔻` has `1 ≤ L`
(`d_𝔻(A x₀, A x_n) → ∞` along `x_n → ζ` forces `L > 0`, and then `L⁻¹ ≤ L`). -/
theorem s07_sb_qi_one {A : ℂ → ℂ} {L c : ℝ} (hA : IsDiskQI A L c) {ζ w : ℂ}
    (hζ : ζ ∈ sphere (0 : ℂ) 1) (hw : ‖w‖ = 1) (hlim : Tendsto A (𝓝[unitDisc] ζ) (𝓝 w)) :
    1 ≤ L := by
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hc : 0 ≤ c := by
    have h := (hA.2 0 h0 0 h0).1
    rw [s07_mo_dist_self, s07_mo_dist_self, mul_zero] at h
    linarith
  by_cases hL : L ≤ 0
  · -- `A(𝔻)` is `d_𝔻`-bounded around `A 0`, so it stays in a smaller disk and `|w| < 1`
    exfalso
    have hA0 := hA.1 h0
    have hbd : ∀ x ∈ unitDisc, 2 / (Real.cosh (c + diskDist (A 0) 0) + 1) ≤ 1 - ‖A x‖ ^ 2 := by
      intro x hx
      apply s07_sb_far _ (hA.1 hx)
      have h1 := (hA.2 x hx 0 h0).2
      have h2 := s02_diskDist_triangle (hA.1 hx) hA0 h0
      have h3 : L * diskDist x 0 ≤ 0 := by nlinarith [s02_diskDist_nonneg hx h0]
      linarith
    have hδ : 0 < 2 / (Real.cosh (c + diskDist (A 0) 0) + 1) := by
      have := Real.one_le_cosh (c + diskDist (A 0) 0)
      exact div_pos two_pos (by linarith)
    have hnorm : Tendsto (fun x => ‖A x‖ ^ 2) (𝓝[unitDisc] ζ) (𝓝 1) := by
      have h' := hlim.norm.pow 2
      rwa [hw, one_pow] at h'
    have hev := hnorm.eventually
      (lt_mem_nhds (show 1 - 2 / (Real.cosh (c + diskDist (A 0) 0) + 1) < 1 by linarith))
    haveI : (𝓝[unitDisc] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (by
      rw [show unitDisc = ball (0 : ℂ) 1 from rfl, closure_ball (0 : ℂ) one_ne_zero]
      exact sphere_subset_closedBall hζ)
    obtain ⟨x, hx1, hxD⟩ := (hev.and self_mem_nhdsWithin).exists
    have := hbd x hxD
    linarith
  · -- `L > 0`: compare the two bounds along a geodesic, `L⁻¹ D - c ≤ L D + c` for all `D`
    push_neg at hL
    by_contra h1
    push_neg at h1
    obtain ⟨B, hB⟩ : ∃ B : ℝ × ℂ → ℝ × ℂ → ℝ, ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re :=
      ⟨_, fun _ _ => rfl⟩
    obtain ⟨P, hP⟩ : ∃ P : ℂ → ℝ × ℂ, ∀ p, P p =
        ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p) := ⟨_, fun _ => rfl⟩
    have hh : (1 / 2 : ℂ) ∈ unitDisc := by
      show (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff]
      norm_num
    obtain ⟨e₁, e₂, hon, -⟩ := s07_mo_frame B hB P hP h0 hh (by norm_num)
    obtain ⟨-, -, -, -, γ, hγD, -, -, hγd, -, -⟩ :=
      s07_mo_line B hB P hP hon (s07_mo_hyp B hB P hP h0).2.1
    have hLi : L < L⁻¹ := h1.trans ((one_lt_inv₀ hL).mpr h1)
    have hne : L⁻¹ - L ≠ 0 := (sub_pos.mpr hLi).ne'
    obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (2 * c + 1) / (L⁻¹ - L) := ⟨_, rfl⟩
    have hD0 : 0 < D := by
      rw [hD]
      exact div_pos (by linarith) (sub_pos.mpr hLi)
    have he : (L⁻¹ - L) * D = 2 * c + 1 := by
      rw [hD]
      field_simp
      exact div_self (by nlinarith : (0 : ℝ) < 1 - L ^ 2).ne'
    have hq := hA.2 (γ D) (hγD D) (γ 0) (hγD 0)
    rw [hγd, sub_zero, abs_of_pos hD0] at hq
    obtain ⟨hq1, hq2⟩ := hq
    nlinarith

/-- SB5: post-composing a `(L_A, c_A)`-quasi-isometry with an `L_F`-bi-Lipschitz self-map of `𝔻`
gives a `(L_F L_A, L_F c_A)`-quasi-isometry. -/
theorem s07_sb_qi_comp {A G : ℂ → ℂ} {LA cA LF : ℝ} (hA : IsDiskQI A LA cA)
    (hG : MapsTo G unitDisc unitDisc)
    (hGL : ∀ a ∈ unitDisc, ∀ b ∈ unitDisc,
      diskDist (G a) (G b) ≤ LF * diskDist a b ∧ diskDist a b ≤ LF * diskDist (G a) (G b))
    (hLF : 1 ≤ LF) :
    IsDiskQI (fun z => G (A z)) (LF * LA) (LF * cA) := by
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hcA : 0 ≤ cA := by
    have h := (hA.2 0 h0 0 h0).1
    rw [s07_mo_dist_self, s07_mo_dist_self, mul_zero] at h
    linarith
  have hLF0 : 0 < LF := by linarith
  refine ⟨fun x hx => hG (hA.1 hx), fun x hx y hy => ?_⟩
  obtain ⟨l1, u1⟩ := hA.2 x hx y hy
  obtain ⟨u2, l2⟩ := hGL _ (hA.1 hx) _ (hA.1 hy)
  refine ⟨?_, ?_⟩
  · show (LF * LA)⁻¹ * diskDist x y - LF * cA ≤ diskDist (G (A x)) (G (A y))
    have h3 : LF⁻¹ * diskDist (A x) (A y) ≤ diskDist (G (A x)) (G (A y)) := by
      rw [inv_mul_le_iff₀ hLF0]
      exact l2
    have h4 : LF⁻¹ * (LA⁻¹ * diskDist x y - cA) ≤ LF⁻¹ * diskDist (A x) (A y) :=
      mul_le_mul_of_nonneg_left l1 (inv_nonneg.mpr hLF0.le)
    have h5 : LF⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hLF
    have h6 : LF⁻¹ * cA ≤ LF * cA := mul_le_mul_of_nonneg_right (by linarith) hcA
    rw [mul_inv]
    linarith
  · show diskDist (G (A x)) (G (A y)) ≤ LF * LA * diskDist x y + LF * cA
    have := mul_le_mul_of_nonneg_left u1 hLF0.le
    linarith

/-- Lemma 7.4, `lem:same-boundary` (`sec07-transfer.tex:228`), (7.5) `eq:same-boundary`:
`sup_z d_𝔻(Az, Fz) ≤ L_F D_*(L_F L_A, L_F c_A)`. -/
theorem lem_same_boundary (A F : ℂ → ℂ) (LA cA LF : ℝ) (hA : IsDiskQI A LA cA)
    (hF : IsClosedDiskHomeo F) (hFL : IsDiskBiLip F LF) (hbd : HasDiskBoundaryValues A F) :
    ∀ z ∈ unitDisc, diskDist (A z) (F z) ≤ LF * morseD (LF * LA) (LF * cA) := by
  intro z hz
  obtain ⟨-, hLF⟩ := s07_sb_maps hF hFL
  obtain ⟨G, hGD, hFG, -, hGc⟩ := s07_sb_inv hF hFL
  have hGL : ∀ a ∈ unitDisc, ∀ b ∈ unitDisc,
      diskDist (G a) (G b) ≤ LF * diskDist a b ∧ diskDist a b ≤ LF * diskDist (G a) (G b) := by
    intro a ha b hb
    have h := hFL (G a) (hGD ha) (G b) (hGD hb)
    rw [hFG a ha, hFG b hb] at h
    exact ⟨h.2, h.1⟩
  have hQ := s07_sb_qi_comp hA hGD hGL hLF
  have h1 : (1 : ℂ) ∈ sphere (0 : ℂ) 1 := by simp
  have hLA : 1 ≤ LA :=
    s07_sb_qi_one hA h1 (mem_sphere_zero_iff_norm.mp (s07_sb_sphere hF hFL h1)) (hbd 1 h1)
  have hlam : 1 ≤ LF * LA := by nlinarith
  have hcA : 0 ≤ cA := by
    have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
    have h := (hA.2 0 h0 0 h0).1
    rw [s07_mo_dist_self, s07_mo_dist_self, mul_zero] at h
    linarith
  have hc : 0 ≤ LF * cA := mul_nonneg (by linarith) hcA
  have hbdQ : HasDiskBoundaryValues (fun z => G (A z)) id := fun ζ hζ =>
    (hGc ζ hζ).comp (tendsto_nhdsWithin_iff.mpr
      ⟨hbd ζ hζ, eventually_nhdsWithin_of_forall fun w hw => hA.1 hw⟩)
  have hM := lem_morse _ _ hlam hc _ hQ hbdQ z hz
  calc diskDist (A z) (F z) = diskDist (F (G (A z))) (F z) := by rw [hFG _ (hA.1 hz)]
    _ ≤ LF * diskDist (G (A z)) z := (hFL _ (hGD (hA.1 hz)) _ hz).1
    _ ≤ LF * morseD (LF * LA) (LF * cA) := mul_le_mul_of_nonneg_left hM (by linarith)

/-! ## Strong quasisymmetry and strong symmetry (definitions in `S02_Prelim`) -/

/-- `h` admits a `K₀`-quasiconformal extension to `𝔻`: a `K₀`-q.c. self-map of `𝔻` with
boundary values `h`. -/
def AdmitsQCDiskExt (h : ℂ → ℂ) (K₀ : ℝ) : Prop :=
  ∃ H : ℂ → ℂ, IsKQC H unitDisc K₀ ∧ H '' unitDisc = unitDisc ∧ HasDiskBoundaryValues H h

/-- The Möbius automorphism `z ↦ e^{it}(z - a)/(1 - ā z)` of `𝔻`. -/
def diskMobius (t : ℝ) (a z : ℂ) : ℂ := exp (t * I) * ((z - a) / (1 - conj a * z))

/-- Helper for `s07_cz_power`: termwise comparison of two measures on a countable disjoint
measurable family passes to the union. -/
theorem s07_cz_sum {ι : Type*} [Countable ι] {ρ₁ ρ₂ : Measure ℝ} {A : ι → Set ℝ}
    (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise (Function.onFun Disjoint A)) {c : ℝ≥0∞}
    (h : ∀ i, ρ₁ (A i) ≤ c * ρ₂ (A i)) : ρ₁ (⋃ i, A i) ≤ c * ρ₂ (⋃ i, A i) := by
  rw [measure_iUnion hd hA, measure_iUnion hd hA, ← ENNReal.tsum_mul_left]
  exact tsum_le_tsum h

/-- Helper for `s07_cz_power`: the dyadic-type cell of `x` of size `s` based at `a`. -/
theorem s07_cz_cell_iff {a s x : ℝ} (hs : 0 < s) (k : ℤ) :
    ⌊(x - a) / s⌋ = k ↔ x ∈ Ico (a + k * s) (a + (k + 1) * s) := by
  rw [Int.floor_eq_iff, le_div_iff₀ hs, div_lt_iff₀ hs, mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- Helper for `s07_cz_power`: the cell of size `s/2` of `x` lies in its cell of size `s`. -/
theorem s07_cz_cell_nest {a s x : ℝ} (hs : 0 < s) :
    Ico (a + ⌊(x - a) / (s / 2)⌋ * (s / 2)) (a + (⌊(x - a) / (s / 2)⌋ + 1) * (s / 2)) ⊆
      Ico (a + ⌊(x - a) / s⌋ * s) (a + (⌊(x - a) / s⌋ + 1) * s) := by
  have e : (x - a) / (s / 2) = 2 * ((x - a) / s) := by
    rw [div_div_eq_mul_div]
    ring
  rw [e]
  intro y hy
  obtain ⟨hy1, hy2⟩ := hy
  have h1 : ((2 * ⌊(x - a) / s⌋ : ℤ) : ℝ) ≤ ⌊2 * ((x - a) / s)⌋ := by
    exact_mod_cast Int.le_floor.mpr (by push_cast; linarith [Int.floor_le ((x - a) / s)])
  have h2' : ⌊2 * ((x - a) / s)⌋ < 2 * ⌊(x - a) / s⌋ + 2 :=
    Int.floor_lt.mpr (by push_cast; linarith [Int.lt_floor_add_one ((x - a) / s)])
  have h2 : ((⌊2 * ((x - a) / s)⌋ : ℤ) : ℝ) ≤ 2 * ⌊(x - a) / s⌋ + 1 := by
    exact_mod_cast (by omega : ⌊2 * ((x - a) / s)⌋ ≤ 2 * ⌊(x - a) / s⌋ + 1)
  push_cast at h1
  constructor
  · nlinarith
  · nlinarith

/-- Helper for `s07_cz_power`: Lebesgue density in the form used by the stopping argument: at
a.e. point of `F`, every small half-open interval containing it has `F`-density `> β/2`. -/
theorem s07_cz_density {F : Set ℝ} (hF : MeasurableSet F) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∀ᵐ x, x ∈ F → ∃ ε > 0, ∀ c r : ℝ, 0 < r → r < ε → x ∈ Ico c (c + r) →
      ENNReal.ofReal (β / 2 * r) < volume (F ∩ Ico c (c + r)) := by
  have hd := Besicovitch.ae_tendsto_measure_inter_div (volume : Measure ℝ) F
  rw [ae_restrict_iff' hF] at hd
  filter_upwards [hd] with x hx hxF
  have hτ : ENNReal.ofReal (1 / 2 + β / 4) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    linarith
  have hev : {r : ℝ | ENNReal.ofReal (1 / 2 + β / 4) <
      volume (F ∩ closedBall x r) / volume (closedBall x r)} ∈ 𝓝[>] (0 : ℝ) :=
    (hx hxF) (lt_mem_nhds hτ)
  obtain ⟨ε, hε, hεs⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨ε, hε, fun c r hr hrε hxc => ?_⟩
  have hB := hεs ⟨hr, hrε⟩
  simp only [mem_ofPred_eq, Real.volume_closedBall] at hB
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by simp; linarith)) (Or.inl ENNReal.ofReal_ne_top),
    ← ENNReal.ofReal_mul (by linarith)] at hB
  have hBfin : volume (closedBall x r) ≠ ∞ := measure_closedBall_lt_top.ne
  have hfin : volume (F ∩ closedBall x r) ≠ ∞ :=
    ((measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top).ne
  rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hfin, ← measureReal_def, inter_comm] at hB
  have hsub : Ico c (c + r) ⊆ closedBall x r := by
    intro y hy
    rw [mem_closedBall, Real.dist_eq, abs_le]
    obtain ⟨h1, h2⟩ := hy
    obtain ⟨h3, h4⟩ := hxc
    constructor <;> linarith
  have e1 := measureReal_inter_add_sdiff (μ := volume) (s := closedBall x r) hF hBfin
  have e2 := measureReal_inter_add_sdiff (μ := volume) (s := Ico c (c + r)) hF
    measure_Ico_lt_top.ne
  have hmono : volume.real (Ico c (c + r) \ F) ≤ volume.real (closedBall x r \ F) :=
    measureReal_mono (fun y hy => ⟨hsub hy.1, hy.2⟩)
      ((measure_mono (fun y hy => hy.1 : closedBall x r \ F ⊆ closedBall x r)).trans_lt
        measure_closedBall_lt_top).ne
  rw [measureReal_def volume (closedBall x r), Real.volume_closedBall,
    ENNReal.toReal_ofReal (by linarith)] at e1
  rw [measureReal_def volume (Ico c (c + r)), Real.volume_Ico,
    ENNReal.toReal_ofReal (by linarith)] at e2
  have hfin2 : volume (F ∩ Ico c (c + r)) ≠ ∞ :=
    ((measure_mono inter_subset_right).trans_lt measure_Ico_lt_top).ne
  rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hfin2, ← measureReal_def, inter_comm]
  nlinarith

/-- Helper for `s07_cz_power`: one Calderón–Zygmund step. If `|F| ≤ (β/2)|J|`, the union `G` of
the maximal dyadic subintervals of `J` on which `F` has density `> β/2` satisfies
`|G| ≤ (2/β)|F|` and `μ(F) ≤ θ μ(G)`. -/
theorem s07_cz_step {β θ : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {μ : Measure ℝ}
    (hμ : μ ≪ volume) {L : ℝ}
    (hP : ∀ a b : ℝ, a < b → b - a ≤ L → ∀ F ⊆ Icc a b, MeasurableSet F →
      volume F ≤ ENNReal.ofReal (β * (b - a)) → μ F ≤ ENNReal.ofReal θ * μ (Icc a b))
    {a b : ℝ} (hab : a < b) (hL : b - a ≤ L) {F : Set ℝ} (hFJ : F ⊆ Icc a b)
    (hF : MeasurableSet F) (hFs : volume F ≤ ENNReal.ofReal (β / 2 * (b - a))) :
    ∃ G, MeasurableSet G ∧ G ⊆ Icc a b ∧ volume G ≤ ENNReal.ofReal (2 / β) * volume F ∧
      μ F ≤ ENNReal.ofReal θ * μ G := by
  classical
  have hba : 0 < b - a := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, s = fun n => (b - a) / 2 ^ n := ⟨_, rfl⟩
  have hs0 : ∀ n, 0 < s n := fun n => by
    simp only [hs]
    exact div_pos hba (by positivity)
  have hs1 : ∀ n, s (n + 1) = s n / 2 := fun n => by
    simp only [hs]
    rw [pow_succ, div_div]
  have hs00 : s 0 = b - a := by simp [hs]
  have hsle : ∀ n, s n ≤ b - a := fun n => by
    simp only [hs]
    exact div_le_self hba.le (one_le_pow₀ one_le_two)
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
  have hC0 : ∀ x ∈ Ico a b, C 0 (K 0 x) = Ico a b := by
    intro x hx
    have h0 : K 0 x = 0 := by
      rw [hKC]
      simp only [hC, hs00, Int.cast_zero, zero_mul, add_zero, zero_add, one_mul, eab]
      exact hx
    rw [h0]
    simp only [hC, hs00, Int.cast_zero, zero_mul, add_zero, zero_add, one_mul, eab]
  have hCeq : ∀ n k, C n k = Ico (a + k * s n) (a + k * s n + s n) := fun n k => by
    simp only [hC]
    congr 1
    ring
  have hvolC : ∀ n k, volume (C n k) = ENNReal.ofReal (s n) := fun n k => by
    rw [hCeq, Real.volume_Ico]
    congr 1
    ring
  have hμpt : ∀ y, μ {y} = 0 := fun y => hμ (Real.volume_singleton)
  obtain ⟨A, hA⟩ : ∃ A : ℕ × ℤ → Set ℝ, A = fun p => {x | x ∈ Ico a b ∧
      ENNReal.ofReal (β / 2 * s p.1) < volume (F ∩ C p.1 (K p.1 x)) ∧
      (∀ m < p.1, ¬ ENNReal.ofReal (β / 2 * s m) < volume (F ∩ C m (K m x))) ∧
      K p.1 x = p.2} := ⟨_, rfl⟩
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
  have hterm : ∀ p : ℕ × ℤ, MeasurableSet (A p) ∧
      μ.restrict F (A p) ≤ ENNReal.ofReal θ * μ (A p) ∧
      volume (A p) ≤ ENNReal.ofReal (2 / β) * volume.restrict F (A p) := by
    intro p
    by_cases hne : (A p).Nonempty
    · obtain ⟨x₀, hx₀⟩ := hne
      have hAp := hAcell p x₀ hx₀
      simp only [hA, mem_ofPred_eq] at hx₀
      obtain ⟨hx₀J, hx₀b, hx₀g, hx₀k⟩ := hx₀
      rw [hx₀k] at hx₀b
      have hmeas : MeasurableSet (A p) := by rw [hAp, hCeq]; exact measurableSet_Ico
      refine ⟨hmeas, ?_, ?_⟩
      · rw [Measure.restrict_apply hmeas, hAp, inter_comm]
        -- the parent cell is not selected, so the density is at most `β`
        have hn0 : p.1 ≠ 0 := by
          intro h0
          have hb0 := hx₀b
          rw [← hx₀k, h0, hC0 x₀ hx₀J, hs00] at hb0
          exact absurd ((measure_mono inter_subset_left).trans hFs) (not_le.mpr hb0)
        obtain ⟨m, hm⟩ : ∃ m, p.1 = m + 1 := Nat.exists_eq_succ_of_ne_zero hn0
        have hpar := hx₀g m (by omega)
        rw [not_lt] at hpar
        have hsub : C p.1 p.2 ⊆ C m (K m x₀) := by
          rw [← hx₀k, hm]
          exact hnest m x₀
        have hFc : volume (F ∩ C p.1 p.2) ≤
            ENNReal.ofReal (β * (a + p.2 * s p.1 + s p.1 - (a + p.2 * s p.1))) := by
          refine (measure_mono (inter_subset_inter_right F hsub)).trans (hpar.trans ?_)
          apply ENNReal.ofReal_le_ofReal
          rw [hm, hs1]
          ring_nf
          rfl
        have hsL : a + p.2 * s p.1 + s p.1 - (a + p.2 * s p.1) ≤ L := by
          linarith [hsle p.1, hs0 p.1]
        have key := hP (a + p.2 * s p.1) (a + p.2 * s p.1 + s p.1) (by linarith [hs0 p.1]) hsL
          (F ∩ C p.1 p.2) (by rw [hCeq]; exact inter_subset_right.trans Ico_subset_Icc_self)
          (hF.inter (by rw [hCeq]; exact measurableSet_Ico)) hFc
        refine key.trans (mul_le_mul_right ?_ _)
        rw [hCeq, ← Ico_union_right (by linarith [hs0 p.1])]
        exact (measure_union_le _ _).trans (by rw [hμpt, add_zero])
      · rw [Measure.restrict_apply hmeas, hAp, hvolC, inter_comm]
        calc ENNReal.ofReal (s p.1)
            = ENNReal.ofReal (2 / β) * ENNReal.ofReal (β / 2 * s p.1) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              congr 1
              field_simp
          _ ≤ ENNReal.ofReal (2 / β) * volume (F ∩ C p.1 p.2) := mul_le_mul_right hx₀b.le _
    · rw [not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
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
  have hAm : ∀ p, MeasurableSet (A p) := fun p => (hterm p).1
  refine ⟨⋃ p, A p, MeasurableSet.iUnion hAm, ?_, ?_, ?_⟩
  · exact iUnion_subset fun p x hx => by
      simp only [hA, mem_ofPred_eq] at hx
      exact Ico_subset_Icc_self hx.1
  · refine (s07_cz_sum hAm hdisj fun p => (hterm p).2.2).trans (mul_le_mul_right ?_ _)
    calc volume.restrict F (⋃ p, A p) ≤ volume.restrict F univ := measure_mono (subset_univ _)
      _ = volume F := Measure.restrict_apply_univ F
  · have hGm := MeasurableSet.iUnion hAm
    -- `F ⊆ G` up to a null set (Lebesgue density)
    have hnull : volume (F \ ⋃ p, A p) = 0 := by
      have hD := s07_cz_density hF hβ hβ1
      rw [ae_iff] at hD
      refine measure_mono_null (t := {x | ¬(x ∈ F → ∃ ε > 0, ∀ c r : ℝ, 0 < r → r < ε →
          x ∈ Ico c (c + r) → ENNReal.ofReal (β / 2 * r) < volume (F ∩ Ico c (c + r)))} ∪ {b})
        ?_ (measure_union_null hD Real.volume_singleton)
      intro x hx
      by_cases hxb : x = b
      · exact Or.inr hxb
      left
      intro hden
      apply hx.2
      obtain ⟨ε, hε, hεP⟩ := hden hx.1
      have hxJ : x ∈ Ico a b := ⟨(hFJ hx.1).1, lt_of_le_of_ne (hFJ hx.1).2 hxb⟩
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((b - a) / ε) one_lt_two
      have hsn : s n < ε := by
        simp only [hs]
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hε] at hn
        linarith
      have hbad : ∃ n, ENNReal.ofReal (β / 2 * s n) < volume (F ∩ C n (K n x)) := by
        refine ⟨n, ?_⟩
        rw [hCeq]
        exact hεP _ _ (hs0 n) hsn (by rw [← hCeq]; exact hmemC n x)
      refine mem_iUnion.mpr ⟨(Nat.find hbad, K (Nat.find hbad) x), ?_⟩
      simp only [hA, mem_ofPred_eq]
      exact ⟨hxJ, Nat.find_spec hbad, fun m hm => Nat.find_min hbad hm, trivial⟩
    have hμnull : μ (F \ ⋃ p, A p) = 0 := hμ hnull
    calc μ F ≤ μ (F ∩ ⋃ p, A p) + μ (F \ ⋃ p, A p) := measure_le_inter_add_sdiff μ F _
      _ = μ.restrict F (⋃ p, A p) := by rw [hμnull, add_zero, Measure.restrict_apply hGm, inter_comm]
      _ ≤ ENNReal.ofReal θ * μ (⋃ p, A p) := s07_cz_sum hAm hdisj fun p => (hterm p).2.1

/-- Helper for `s07_cz_power`: iterating `s07_cz_step`, `|F| ≤ (β/2)^k |J| ⇒ μ(F) ≤ θ^k μ(J)`. -/
theorem s07_cz_iter {β θ : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hθ : 0 < θ) {μ : Measure ℝ}
    (hμ : μ ≪ volume) {L : ℝ}
    (hP : ∀ a b : ℝ, a < b → b - a ≤ L → ∀ F ⊆ Icc a b, MeasurableSet F →
      volume F ≤ ENNReal.ofReal (β * (b - a)) → μ F ≤ ENNReal.ofReal θ * μ (Icc a b))
    {a b : ℝ} (hab : a < b) (hL : b - a ≤ L) (k : ℕ) :
    ∀ F ⊆ Icc a b, MeasurableSet F → volume F ≤ ENNReal.ofReal ((β / 2) ^ k * (b - a)) →
      μ F ≤ ENNReal.ofReal (θ ^ k) * μ (Icc a b) := by
  have hba : 0 < b - a := by linarith
  induction k with
  | zero =>
    intro F hFJ _ _
    rw [pow_zero, ENNReal.ofReal_one, one_mul]
    exact measure_mono hFJ
  | succ k ih =>
    intro F hFJ hF hFs
    have hq : (β / 2) ^ (k + 1) * (b - a) ≤ β / 2 * (b - a) :=
      mul_le_mul_of_nonneg_right (pow_le_of_le_one (by positivity) (by linarith)
        (Nat.succ_ne_zero k)) hba.le
    obtain ⟨G, hGm, hGJ, hGv, hμG⟩ := s07_cz_step hβ hβ1 hμ hP hab hL hFJ hF
      (hFs.trans (ENNReal.ofReal_le_ofReal hq))
    have hGs : volume G ≤ ENNReal.ofReal ((β / 2) ^ k * (b - a)) := by
      refine hGv.trans ?_
      calc ENNReal.ofReal (2 / β) * volume F
          ≤ ENNReal.ofReal (2 / β) * ENNReal.ofReal ((β / 2) ^ (k + 1) * (b - a)) :=
            mul_le_mul_right hFs _
        _ = ENNReal.ofReal ((β / 2) ^ k * (b - a)) := by
            rw [← ENNReal.ofReal_mul (by positivity), pow_succ]
            congr 1
            field_simp
    calc μ F ≤ ENNReal.ofReal θ * μ G := hμG
      _ ≤ ENNReal.ofReal θ * (ENNReal.ofReal (θ ^ k) * μ (Icc a b)) :=
          mul_le_mul_right (ih G hGJ hGm hGs) _
      _ = ENNReal.ofReal (θ ^ (k + 1)) * μ (Icc a b) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hθ.le, pow_succ, mul_comm θ]

/-- Helper (W-CZ, dyadic Calderón–Zygmund self-improvement, Lebesgue base): if a measure `μ ≪ dx`
satisfies the fixed-threshold condition `|F| ≤ β|J| ⇒ μ(F) ≤ θ μ(J)` on all intervals `J` of length
`≤ L`, then it satisfies the power form `μ(F) ≤ C (|F|/|J|)^δ μ(J)` there, with `C, δ` depending
only on `β, θ` (`C = θ⁻¹`, `δ = log θ / log (β/2)`). Proof: induction on `k` for
`|F| ≤ (β/2)^k |J|`, using the maximal dyadic subintervals of `J` on which `F` has density
`> β/2`. -/
theorem s07_cz_power {β θ : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ μ : Measure ℝ, μ ≪ volume → ∀ L : ℝ,
      (∀ a b : ℝ, a < b → b - a ≤ L → ∀ F ⊆ Icc a b, MeasurableSet F →
        volume F ≤ ENNReal.ofReal (β * (b - a)) → μ F ≤ ENNReal.ofReal θ * μ (Icc a b)) →
      ∀ a b : ℝ, a < b → b - a ≤ L → ∀ F ⊆ Icc a b, MeasurableSet F →
        μ F ≤ ENNReal.ofReal (C * ((volume F).toReal / (b - a)) ^ δ) * μ (Icc a b) := by
  classical
  have hq0 : 0 < β / 2 := by positivity
  have hq1 : β / 2 < 1 := by linarith
  have hlq : Real.log (β / 2) < 0 := Real.log_neg hq0 hq1
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = Real.log θ / Real.log (β / 2) := ⟨_, rfl⟩
  have hqδ : (β / 2) ^ δ = θ := by
    rw [Real.rpow_def_of_pos hq0, hδ]
    have : Real.log (β / 2) * (Real.log θ / Real.log (β / 2)) = Real.log θ := by
      rw [← mul_div_assoc]
      exact mul_div_cancel_left₀ _ hlq.ne
    rw [this, Real.exp_log hθ]
  refine ⟨θ⁻¹, δ, inv_pos.mpr hθ, by rw [hδ]; exact div_pos_of_neg_of_neg (Real.log_neg hθ hθ1) hlq,
    ?_⟩
  intro μ hμ L hP a b hab hL F hFJ hF
  have hba : 0 < b - a := by linarith
  have hFle : volume F ≤ ENNReal.ofReal (b - a) := (measure_mono hFJ).trans_eq Real.volume_Icc
  have hFfin : volume F ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hFle
  obtain ⟨t, ht⟩ : ∃ t, t = (volume F).toReal / (b - a) := ⟨_, rfl⟩
  rw [← ht]
  have htv : (volume F).toReal = t * (b - a) := by
    rw [ht]
    field_simp
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg ENNReal.toReal_nonneg hba.le
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one hba]
    exact ENNReal.toReal_le_of_le_ofReal hba.le hFle
  rcases ht0.eq_or_lt with h0 | hpos
  · have hF0 : volume F = 0 := by
      rw [← h0, zero_mul, ENNReal.toReal_eq_zero_iff] at htv
      exact htv.resolve_right hFfin
    rw [hμ hF0]
    exact bot_le
  · have hex : ∃ k : ℕ, (β / 2) ^ (k + 1) < t := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos hq1
      exact ⟨n, (pow_le_pow_of_le_one hq0.le hq1.le (Nat.le_succ n)).trans_lt hn⟩
    obtain ⟨k, hk⟩ : ∃ k, k = Nat.find hex := ⟨_, rfl⟩
    have hk1 : (β / 2) ^ (k + 1) < t := hk ▸ Nat.find_spec hex
    have hk2 : t ≤ (β / 2) ^ k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · rw [hk0, pow_zero]
        exact ht1
      · have hmin := Nat.find_min hex (hk ▸ Nat.sub_lt hk0 one_pos : k - 1 < Nat.find hex)
        rw [Nat.sub_add_cancel hk0] at hmin
        exact not_lt.mp hmin
    have hFk : volume F ≤ ENNReal.ofReal ((β / 2) ^ k * (b - a)) := by
      rw [ENNReal.le_ofReal_iff_toReal_le hFfin (mul_nonneg (by positivity) hba.le), htv]
      exact mul_le_mul_of_nonneg_right hk2 hba.le
    refine (s07_cz_iter hβ hβ1 hθ hμ hP hab hL k F hFJ hF hFk).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
    have hpow : θ ^ (k + 1) ≤ t ^ δ := by
      have hδ0 : 0 ≤ δ := by rw [hδ]; exact (div_pos_of_neg_of_neg (Real.log_neg hθ hθ1) hlq).le
      calc θ ^ (k + 1) = ((β / 2) ^ δ) ^ (k + 1) := by rw [hqδ]
        _ = ((β / 2) ^ (k + 1)) ^ δ := by
            rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le,
              ← Real.rpow_mul hq0.le, mul_comm]
        _ ≤ t ^ δ := Real.rpow_le_rpow (by positivity) hk1.le hδ0
    rw [le_inv_mul_iff₀ hθ, ← pow_succ']
    exact hpow

/-- Every `ζ ∈ ∂𝔻` is `e^{iθ}` with `θ ∈ [0, 2π)`. -/
theorem s07_exists_angle (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) 1) :
    ∃ θ ∈ Ico 0 (2 * π), exp (θ * I) = ζ := by
  have h1 : ‖ζ‖ = 1 := by simpa using hζ
  refine ⟨toIcoMod Real.two_pi_pos 0 (arg ζ), toIcoMod_mem_Ico' _ _, ?_⟩
  rw [← self_sub_toIcoDiv_zsmul]
  have h2 : exp (((arg ζ - toIcoDiv Real.two_pi_pos 0 (arg ζ) • (2 * π) : ℝ) : ℂ) * I) =
      exp ((arg ζ : ℂ) * I) :=
    Complex.exp_eq_exp_iff_exists_int.mpr ⟨-toIcoDiv Real.two_pi_pos 0 (arg ζ), by
      rw [zsmul_eq_mul]; push_cast; ring⟩
  rw [h2]
  have := Complex.norm_mul_exp_arg_mul_I ζ
  rwa [h1, Complex.ofReal_one, one_mul] at this

/-- `θ ↦ e^{iθ}` is injective on every half-open interval of length `2π`. -/
theorem s07_exp_injOn (c : ℝ) : InjOn (fun x : ℝ => exp (x * I)) (Ico c (c + 2 * π)) := by
  intro x hx y hy hxy
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hxy
  have him := congrArg Complex.im hn
  simp at him
  have hpi := Real.pi_pos
  have h1 : (n : ℝ) * (2 * π) < 2 * π := by nlinarith [hx.1, hx.2, hy.1, hy.2]
  have h2 : -(2 * π) < (n : ℝ) * (2 * π) := by nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hn1 : (n : ℝ) < 1 := by nlinarith
  have hn2 : (-1 : ℝ) < n := by nlinarith
  have hn0 : n = 0 := by
    have a : n < 1 := by exact_mod_cast hn1
    have b : -1 < n := by exact_mod_cast hn2
    omega
  subst hn0
  simpa using him

/-- `circleArc a b ⊆ ∂𝔻`. -/
theorem s07_circleArc_subset (a b : ℝ) : circleArc a b ⊆ sphere (0 : ℂ) 1 := by
  rintro _ ⟨θ, -, rfl⟩
  simp [Complex.norm_exp_ofReal_mul_I]

/-- A lift satisfies `H(θ - 2π) = H(θ) - 2π`. -/
theorem s07_lift_sub_two_pi {H : ℝ → ℝ} (hper : ∀ θ, H (θ + 2 * π) = H θ + 2 * π) (θ : ℝ) :
    H (θ - 2 * π) = H θ - 2 * π := by
  have := hper (θ - 2 * π)
  rw [sub_add_cancel] at this
  linarith

/-- A circle homeomorphism (given by its lift) maps measurable subsets of `∂𝔻` to measurable
sets. -/
theorem s07_measurableSet_image (h : ℂ → ℂ) (H : ℝ → ℝ) (hmono : StrictMono H)
    (hcont : Continuous H) (hper : ∀ θ, H (θ + 2 * π) = H θ + 2 * π)
    (heq : ∀ θ : ℝ, h (exp (θ * I)) = exp (H θ * I)) (E : Set ℂ) (hE : MeasurableSet E)
    (hEs : E ⊆ sphere (0 : ℂ) 1) : MeasurableSet (h '' E) := by
  have hexp : Continuous fun θ : ℝ => exp (θ * I) := by fun_prop
  have hT : MeasurableSet (Ico 0 (2 * π) ∩ (fun θ : ℝ => exp (θ * I)) ⁻¹' E) :=
    measurableSet_Ico.inter (hE.preimage hexp.measurable)
  have himg : h '' E = (fun θ : ℝ => exp (H θ * I)) ''
      (Ico 0 (2 * π) ∩ (fun θ : ℝ => exp (θ * I)) ⁻¹' E) := by
    ext w
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      obtain ⟨θ, hθ, rfl⟩ := s07_exists_angle ζ (hEs hζ)
      exact ⟨θ, ⟨hθ, hζ⟩, (heq θ).symm⟩
    · rintro ⟨θ, ⟨-, hθE⟩, rfl⟩
      exact ⟨_, hθE, heq θ⟩
  rw [himg]
  refine hT.image_of_continuousOn_injOn
    (by fun_prop : Continuous fun θ : ℝ => exp (H θ * I)).continuousOn ?_
  intro x hx y hy hxy
  have hH : ∀ z ∈ Ico 0 (2 * π), H z ∈ Ico (H 0) (H 0 + 2 * π) := fun z hz =>
    ⟨hmono.monotone hz.1, by rw [← hper 0, zero_add]; exact hmono hz.2⟩
  exact hmono.injective (s07_exp_injOn (H 0) (hH x hx.1) (hH y hy.1) hxy)

/-- A circle homeomorphism with lift `H` maps the arc `[a, b]` onto the arc `[H a, H b]`. -/
theorem s07_image_circleArc (h : ℂ → ℂ) (H : ℝ → ℝ) (hmono : StrictMono H)
    (hcont : Continuous H) (heq : ∀ θ : ℝ, h (exp (θ * I)) = exp (H θ * I)) (a b : ℝ)
    (hab : a ≤ b) : h '' circleArc a b = circleArc (H a) (H b) := by
  have hIcc : H '' Icc a b = Icc (H a) (H b) :=
    Subset.antisymm (image_subset_iff.mpr fun θ hθ => ⟨hmono.monotone hθ.1, hmono.monotone hθ.2⟩)
      (intermediate_value_Icc hab hcont.continuousOn)
  unfold circleArc
  rw [image_image, ← hIcc, image_image]
  exact image_congr fun θ _ => heq θ

/-- Group facts (`sec07-transfer.tex:285`, [TWS, proof of Cor. 3.4]): strongly quasisymmetric
homeomorphisms are closed under composition. -/
theorem sqs_circle_comp (h₁ h₂ : ℂ → ℂ) (h1 : IsStronglyQS h₁)
    (h2 : IsStronglyQS h₂) : IsStronglyQS (h₁ ∘ h₂) := by
  obtain ⟨δ₁, ⟨H₁, hm₁, hc₁, hp₁, he₁⟩, hq₁⟩ := h1
  obtain ⟨δ₂, ⟨H₂, hm₂, hc₂, hp₂, he₂⟩, hq₂⟩ := h2
  refine ⟨fun ε => δ₂ (δ₁ ε), ⟨H₁ ∘ H₂, hm₁.comp hm₂, hc₁.comp hc₂,
    fun θ => by simp only [Function.comp, hp₂, hp₁],
    fun θ => by simp only [Function.comp, he₂, he₁]⟩, fun ε hε => ?_⟩
  obtain ⟨hd1, hq1⟩ := hq₁ ε hε
  obtain ⟨hd2, hq2⟩ := hq₂ (δ₁ ε) hd1
  refine ⟨hd2, fun a b hab hab2 E hEI hE hlen => ?_⟩
  have hHab : H₂ a < H₂ b := hm₂ hab
  have hHab2 : H₂ b - H₂ a ≤ 2 * π := by
    have := hm₂.monotone (show b ≤ a + 2 * π by linarith)
    rw [hp₂] at this
    linarith
  have harc := s07_image_circleArc h₂ H₂ hm₂ hc₂ he₂ a b hab.le
  have hstep := hq2 a b hab hab2 E hEI hE hlen
  rw [harc] at hstep
  have hsub : h₂ '' E ⊆ circleArc (H₂ a) (H₂ b) := harc ▸ image_mono hEI
  have hmeas := s07_measurableSet_image h₂ H₂ hm₂ hc₂ hp₂ he₂ E hE
    (hEI.trans (s07_circleArc_subset a b))
  have := hq1 (H₂ a) (H₂ b) hHab hHab2 (h₂ '' E) hsub hmeas hstep
  rwa [image_comp, image_comp, harc]

/-- Arc length can be computed on any period: `|F| = |{θ ∈ (c, c + 2π] : e^{iθ} ∈ F}|`. -/
theorem s07_circleLen_shift (F : Set ℂ) (hF : MeasurableSet F) (c : ℝ) :
    circleLen F = volume ((fun θ : ℝ => exp (θ * I)) ⁻¹' F ∩ Ioc c (c + 2 * π)) := by
  set A := (fun θ : ℝ => exp (θ * I)) ⁻¹' F with hAdef
  have hA : MeasurableSet A := hF.preimage (by fun_prop)
  have hmem : ∀ θ : ℝ, θ + 2 * π ∈ A ↔ θ ∈ A := by
    intro θ
    simp only [hAdef, mem_preimage]
    rw [show ((θ + 2 * π : ℝ) : ℂ) * I = θ * I + 2 * π * I by push_cast; ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hper : Function.Periodic (A.indicator (1 : ℝ → ℝ)) (2 * π) := by
    intro θ
    by_cases h : θ ∈ A
    · simp [indicator, h, (hmem θ).mpr h]
    · have h' : θ + 2 * π ∉ A := fun h' => h ((hmem θ).mp h')
      simp [indicator, h, h']
  have hint : ∀ u : ℝ, ∫ θ in u..u + 2 * π, A.indicator (1 : ℝ → ℝ) θ =
      (volume (A ∩ Ioc u (u + 2 * π))).toReal := by
    intro u
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      integral_indicator_one hA, measureReal_def, Measure.restrict_apply hA]
  have hfin : ∀ u : ℝ, volume (A ∩ Ioc u (u + 2 * π)) ≠ ⊤ := fun u =>
    ((measure_mono inter_subset_right).trans_lt
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)).ne
  have h0 := hper.intervalIntegral_add_eq 0 c
  rw [hint, hint] at h0
  have h0' := (ENNReal.toReal_eq_toReal_iff' (hfin 0) (hfin c)).mp h0
  rw [← h0', zero_add]
  unfold circleLen
  refine measure_congr ?_
  have := (Ico_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := 2 * π))
  have hAA : A =ᵐ[volume] A := Filter.EventuallyEq.refl _ (fun x => x ∈ A)
  have h2 := ae_eq_set_inter hAA this
  rw [show {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ exp (θ * I) ∈ F} = A ∩ Ico 0 (2 * π) by
    ext θ; simp [hAdef, and_comm]]
  exact h2

/-- `|e^{i S}| = |S|` for a measurable `S ⊆ [c, c + 2π]`. -/
theorem s07_circleLen_exp_image (c : ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (hSc : S ⊆ Icc c (c + 2 * π)) :
    circleLen ((fun θ : ℝ => exp (θ * I)) '' S) = volume S := by
  have hexp : Continuous fun θ : ℝ => exp (θ * I) := by fun_prop
  have hFm : MeasurableSet ((fun θ : ℝ => exp (θ * I)) '' S) := by
    have hsplit : (fun θ : ℝ => exp (θ * I)) '' S = (fun θ : ℝ => exp (θ * I)) ''
        (S ∩ Ico c (c + 2 * π)) ∪ (fun θ : ℝ => exp (θ * I)) '' (S ∩ {c + 2 * π}) := by
      rw [← image_union, ← inter_union_distrib_left]
      congr 1
      refine (inter_eq_left.mpr fun θ hθ => ?_).symm
      rcases eq_or_lt_of_le (hSc hθ).2 with h | h
      · exact Or.inr h
      · exact Or.inl ⟨(hSc hθ).1, h⟩
    rw [hsplit]
    exact ((hS.inter measurableSet_Ico).image_of_continuousOn_injOn hexp.continuousOn
      ((s07_exp_injOn c).mono inter_subset_right)).union
      (((finite_singleton _).subset inter_subset_right).image _).measurableSet
  rw [s07_circleLen_shift _ hFm c]
  have hc2 : c < c + 2 * π := by linarith [Real.pi_pos]
  apply le_antisymm
  · calc volume ((fun θ : ℝ => exp (θ * I)) ⁻¹' ((fun θ : ℝ => exp (θ * I)) '' S) ∩
          Ioc c (c + 2 * π)) ≤ volume (S ∪ {c + 2 * π}) := by
          refine measure_mono fun θ hθ => ?_
          obtain ⟨⟨σ, hσ, hσθ⟩, hθ1, hθ2⟩ := hθ
          have hσθ' : exp (σ * I) = exp (θ * I) := hσθ
          rcases eq_or_lt_of_le hθ2 with h | h
          · exact Or.inr h
          · left
            rcases eq_or_lt_of_le (hSc hσ).2 with hσ2 | hσ2
            · exfalso
              have : exp (θ * I) = exp (c * I) := by
                rw [← hσθ', hσ2]
                push_cast
                rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
              have := s07_exp_injOn c ⟨hθ1.le, h⟩ ⟨le_refl c, hc2⟩ this
              linarith
            · rw [s07_exp_injOn c ⟨hθ1.le, h⟩ ⟨(hSc hσ).1, hσ2⟩ hσθ.symm]
              exact hσ
      _ ≤ volume S + volume ({c + 2 * π} : Set ℝ) := measure_union_le _ _
      _ = volume S := by rw [Real.volume_singleton, add_zero]
  · calc volume S ≤ volume (S \ {c}) + volume ({c} : Set ℝ) := by
          calc volume S ≤ volume ((S \ {c}) ∪ {c}) := measure_mono (by
                intro θ hθ
                by_cases h : θ = c
                · exact Or.inr h
                · exact Or.inl ⟨hθ, h⟩)
            _ ≤ _ := measure_union_le _ _
      _ = volume (S \ {c}) := by rw [Real.volume_singleton, add_zero]
      _ ≤ _ := by
          refine measure_mono fun θ hθ => ⟨⟨θ, hθ.1, rfl⟩, ?_, (hSc hθ.1).2⟩
          exact lt_of_le_of_ne (hSc hθ.1).1 (Ne.symm hθ.2)

/-- Helper for `sqs_circle_inv`: `θ ↦ e^{iθ}` maps measurable subsets of a closed period interval
`[c, c + 2π]` to measurable sets (it is injective on `[c, c + 2π)`). -/
theorem s07_inv_exp_meas (c : ℝ) {T : Set ℝ} (hT : MeasurableSet T)
    (hTc : T ⊆ Icc c (c + 2 * π)) : MeasurableSet ((fun θ : ℝ => exp (θ * I)) '' T) := by
  have hexp : Continuous fun θ : ℝ => exp (θ * I) := by fun_prop
  have hsplit : T = (T ∩ Ico c (c + 2 * π)) ∪ (T ∩ {c + 2 * π}) := by
    ext θ
    constructor
    · intro hθ
      by_cases h : θ = c + 2 * π
      · exact Or.inr ⟨hθ, h⟩
      · exact Or.inl ⟨hθ, (hTc hθ).1, lt_of_le_of_ne (hTc hθ).2 h⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  rw [hsplit, image_union]
  exact ((hT.inter measurableSet_Ico).image_of_continuousOn_injOn hexp.continuousOn
    ((s07_exp_injOn c).mono inter_subset_right)).union
    (((finite_singleton (c + 2 * π)).subset inter_subset_right).image _).measurableSet

/-- Helper for `sqs_circle_inv`: a lift commutes with all integer multiples of `2π`. -/
theorem s07_inv_per_int {H : ℝ → ℝ} (hper : ∀ θ, H (θ + 2 * π) = H θ + 2 * π) (n : ℤ)
    (θ : ℝ) : H (θ + n * (2 * π)) = H θ + n * (2 * π) := by
  induction n using Int.induction_on generalizing θ with
  | zero => simp
  | succ i ih =>
    push_cast at ih ⊢
    rw [show θ + ((i : ℝ) + 1) * (2 * π) = θ + (i : ℝ) * (2 * π) + 2 * π by ring, hper, ih]
    ring
  | pred i ih =>
    push_cast at ih ⊢
    rw [show θ + (-(i : ℝ) - 1) * (2 * π) = θ + -(i : ℝ) * (2 * π) - 2 * π by ring,
      s07_lift_sub_two_pi hper, ih]
    ring

/-- Helper for `sqs_circle_inv`: the strong quasisymmetry of `h` read on a lift `H`: for an
interval `[a, b]` of length `≤ 2π` and measurable `S ⊆ [a, b]`, `|S| ≤ δf(ε)(b - a)` implies
`|H(S)| ≤ ε |H([a, b])|` (`s07_circleLen_exp_image` on both sides). -/
theorem s07_inv_hlift {h : ℂ → ℂ} {δf : ℝ → ℝ} {H : ℝ → ℝ} (hs : IsStronglyQSWith h δf)
    (hH : StrictMono H) (hHc : Continuous H) (hper : ∀ θ, H (θ + 2 * π) = H θ + 2 * π)
    (hl : ∀ θ : ℝ, h (exp (θ * I)) = exp (H θ * I)) {ε : ℝ} (hε : 0 < ε) :
    ∀ a b : ℝ, a < b → b - a ≤ 2 * π → ∀ S ⊆ Icc a b, MeasurableSet S →
      volume S ≤ ENNReal.ofReal (δf ε * (b - a)) →
        volume (H '' S) ≤ ENNReal.ofReal ε * volume (H '' Icc a b) := by
  intro a b hab hab2 S hSI hSm hSlen
  obtain ⟨hd, hq⟩ := hs.2 ε hε
  have hIsub : Icc a b ⊆ Icc a (a + 2 * π) := fun θ hθ => ⟨hθ.1, by linarith [hθ.2]⟩
  have hHab2 : H b ≤ H a + 2 * π := by
    rw [← hper]
    exact hH.monotone (by linarith)
  have hHsub : ∀ T ⊆ Icc a b, H '' T ⊆ Icc (H a) (H a + 2 * π) := by
    rintro T hT _ ⟨θ, hθ, rfl⟩
    exact ⟨hH.monotone (hT hθ).1, (hH.monotone (hT hθ).2).trans hHab2⟩
  have hHm : ∀ T : Set ℝ, MeasurableSet T → MeasurableSet (H '' T) := fun T hT =>
    hT.image_of_continuousOn_injOn hHc.continuousOn hH.injective.injOn
  have himg : ∀ T : Set ℝ, h '' ((fun θ : ℝ => exp (θ * I)) '' T) =
      (fun θ : ℝ => exp (θ * I)) '' (H '' T) := by
    intro T
    rw [image_image, image_image]
    exact image_congr fun θ _ => hl θ
  have harc : circleArc a b = (fun θ : ℝ => exp (θ * I)) '' Icc a b := rfl
  have hlen : circleLen ((fun θ : ℝ => exp (θ * I)) '' S) ≤
      ENNReal.ofReal (δf ε) * circleLen (circleArc a b) := by
    rw [s07_circleLen_exp_image a S hSm (hSI.trans hIsub), harc,
      s07_circleLen_exp_image a _ measurableSet_Icc hIsub, Real.volume_Icc,
      ← ENNReal.ofReal_mul hd.le]
    exact hSlen
  have key := hq a b hab hab2 ((fun θ : ℝ => exp (θ * I)) '' S) (harc ▸ image_mono hSI)
    (s07_inv_exp_meas a hSm (hSI.trans hIsub)) hlen
  rw [harc, himg, himg, s07_circleLen_exp_image (H a) _ (hHm S hSm) (hHsub S hSI),
    s07_circleLen_exp_image (H a) _ (hHm _ measurableSet_Icc) (hHsub _ subset_rfl)] at key
  exact key

/-- Helper for `sqs_circle_inv`: the inverse `G = H⁻¹` of a lift `H` of `h` is a lift of the
inverse `hinv` on `∂𝔻`. -/
theorem s07_inv_lift {h hinv : ℂ → ℂ} {H : ℝ → ℝ} (hH : StrictMono H) (hHc : Continuous H)
    (hper : ∀ θ, H (θ + 2 * π) = H θ + 2 * π) (hl : ∀ θ : ℝ, h (exp (θ * I)) = exp (H θ * I))
    (hinv1 : ∀ ζ ∈ sphere (0 : ℂ) 1, hinv ζ ∈ sphere (0 : ℂ) 1 ∧ h (hinv ζ) = ζ) :
    ∃ G : ℝ → ℝ, StrictMono G ∧ Continuous G ∧ (∀ θ, G (θ + 2 * π) = G θ + 2 * π) ∧
      (∀ θ : ℝ, hinv (exp (θ * I)) = exp (G θ * I)) ∧ (∀ θ, H (G θ) = θ) ∧ ∀ θ, G (H θ) = θ := by
  -- `H - id` is `2π`-periodic and continuous, hence bounded
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hHc.sub continuous_id).continuousOn (s := Icc 0 (2 * π)))
  have hpd : Function.Periodic (fun θ => H θ - θ) (2 * π) := fun θ => by
    simp only
    rw [hper]
    ring
  have hbd : ∀ θ, |H θ - θ| ≤ M := by
    intro θ
    obtain ⟨y, hy, hyeq⟩ := hpd.exists_mem_Ico₀ Real.two_pi_pos θ
    have h1 := hM y (Ico_subset_Icc_self hy)
    rw [Real.norm_eq_abs] at h1
    rw [hyeq]
    exact h1
  have htop : Tendsto H atTop atTop := tendsto_atTop_mono (fun θ => by
    show θ + -M ≤ H θ
    linarith [(abs_le.mp (hbd θ)).1]) (tendsto_atTop_add_const_right _ (-M) tendsto_id)
  have hbot : Tendsto H atBot atBot := tendsto_atBot_mono (fun θ => by
    show H θ ≤ θ + M
    linarith [(abs_le.mp (hbd θ)).2]) (tendsto_atBot_add_const_right _ M tendsto_id)
  have hsurj : Function.Surjective H := hHc.surjective htop hbot
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = Function.surjInv hsurj := ⟨_, rfl⟩
  have hHG : ∀ θ, H (G θ) = θ := fun θ => by rw [hG]; exact Function.surjInv_eq hsurj θ
  have hGH : ∀ θ, G (H θ) = θ := fun θ => hH.injective (hHG (H θ))
  have hGm : StrictMono G := fun x y hxy => hH.lt_iff_lt.mp (by rw [hHG, hHG]; exact hxy)
  have hGc : Continuous G :=
    hGm.monotone.continuous_of_surjective fun θ => ⟨H θ, hGH θ⟩
  have hGper : ∀ θ, G (θ + 2 * π) = G θ + 2 * π := fun θ =>
    hH.injective (by rw [hHG, hper, hHG])
  have hGint : ∀ (n : ℤ) (θ : ℝ), G (θ + n * (2 * π)) = G θ + n * (2 * π) :=
    s07_inv_per_int hGper
  refine ⟨G, hGm, hGc, hGper, fun θ => ?_, hHG, hGH⟩
  have hζ : exp (θ * I) ∈ sphere (0 : ℂ) 1 :=
    s07_circleArc_subset θ θ ⟨θ, left_mem_Icc.mpr le_rfl, rfl⟩
  obtain ⟨hs1, hs2⟩ := hinv1 _ hζ
  obtain ⟨φ, -, hφ⟩ := s07_exists_angle _ hs1
  rw [← hφ, hl] at hs2
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hs2
  have hHφ : H φ = θ + n * (2 * π) := by
    have him := congrArg Complex.im hn
    simp at him
    linarith
  have hφG : φ = G θ + n * (2 * π) := by
    rw [← hGint, ← hHφ, hGH]
  rw [← hφ, hφG]
  exact Complex.exp_eq_exp_iff_exists_int.mpr ⟨n, by push_cast; ring⟩

/-- Helper for `sqs_circle_inv`: a lift `H` of a strongly quasisymmetric `h` maps sets of positive
measure to sets of positive measure (at a density point of `A`, `s07_inv_hlift` with `ε = 1/2`
contradicts `|H(A)| = 0`). -/
theorem s07_inv_null {h : ℂ → ℂ} {δf : ℝ → ℝ} {H : ℝ → ℝ} (hs : IsStronglyQSWith h δf)
    (hH : StrictMono H) (hHc : Continuous H) (hper : ∀ θ, H (θ + 2 * π) = H θ + 2 * π)
    (hl : ∀ θ : ℝ, h (exp (θ * I)) = exp (H θ * I)) {A : Set ℝ} (hA : MeasurableSet A)
    (h0 : volume (H '' A) = 0) : volume A = 0 := by
  by_contra hA0
  have hApos : 0 < volume A := pos_iff_ne_zero.mpr hA0
  obtain ⟨hd, -⟩ := hs.2 (1 / 2) (by norm_num)
  obtain ⟨δ', hδ'⟩ : ∃ δ' : ℝ, δ' = min (δf (1 / 2)) (1 / 2) := ⟨_, rfl⟩
  have hδ'0 : 0 < δ' := by rw [hδ']; exact lt_min hd (by norm_num)
  have hδ'1 : δ' ≤ 1 / 2 := by rw [hδ']; exact min_le_right _ _
  have hδ'f : δ' ≤ δf (1 / 2) := by rw [hδ']; exact min_le_left _ _
  -- a density point of `A`
  have hden := Besicovitch.ae_tendsto_measure_inter_div (volume : Measure ℝ) A
  have : (ae (volume.restrict A)).NeBot :=
    ae_neBot.mpr (fun h0 => hA0 (Measure.restrict_eq_zero.mp h0))
  obtain ⟨x, hxA, hx⟩ := ((ae_restrict_mem hA).and hden).exists
  have hτ : ENNReal.ofReal (1 - δ') < 1 := by
    rw [ENNReal.ofReal_lt_one]
    linarith
  obtain ⟨r, hrlt0, hr0, hrπ⟩ := ((hx.eventually (lt_mem_nhds hτ)).and
    (Ioo_mem_nhdsGT Real.pi_pos)).exists
  have hrlt : ENNReal.ofReal (1 - δ') <
      volume (A ∩ closedBall x r) / volume (closedBall x r) := hrlt0
  rw [Real.volume_closedBall, ENNReal.lt_div_iff_mul_lt (Or.inl (by simp; linarith))
    (Or.inl ENNReal.ofReal_ne_top), ← ENNReal.ofReal_mul (by linarith)] at hrlt
  rw [Real.closedBall_eq_Icc] at hrlt
  have hBfin : volume (Icc (x - r) (x + r)) ≠ ∞ := measure_Icc_lt_top.ne
  have hfin : volume (A ∩ Icc (x - r) (x + r)) ≠ ∞ :=
    ((measure_mono inter_subset_right).trans_lt measure_Icc_lt_top).ne
  rw [ENNReal.ofReal_lt_iff_lt_toReal (by nlinarith) hfin, ← measureReal_def, inter_comm] at hrlt
  have e1 := measureReal_inter_add_sdiff (μ := volume) (s := Icc (x - r) (x + r)) hA hBfin
  rw [measureReal_def volume (Icc (x - r) (x + r)), Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)] at e1
  -- the complement is small, so `s07_inv_hlift` applies
  have hSm : MeasurableSet (Icc (x - r) (x + r) \ A) := measurableSet_Icc.diff hA
  have hSlen : volume (Icc (x - r) (x + r) \ A) ≤
      ENNReal.ofReal (δf (1 / 2) * (x + r - (x - r))) := by
    rw [← ofReal_measureReal (((measure_mono (fun y hy => hy.1 :
      Icc (x - r) (x + r) \ A ⊆ Icc (x - r) (x + r))).trans_lt measure_Icc_lt_top).ne)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  have key := s07_inv_hlift hs hH hHc hper hl (ε := 1 / 2) (by norm_num) (x - r) (x + r)
    (by linarith) (by linarith) (Icc (x - r) (x + r) \ A) (fun y hy => hy.1) hSm hSlen
  have hIcc : H '' Icc (x - r) (x + r) = Icc (H (x - r)) (H (x + r)) :=
    Subset.antisymm (image_subset_iff.mpr fun θ hθ => ⟨hH.monotone hθ.1, hH.monotone hθ.2⟩)
      (intermediate_value_Icc (by linarith) hHc.continuousOn)
  have hsplit : H '' Icc (x - r) (x + r) ⊆
      H '' (Icc (x - r) (x + r) \ A) ∪ H '' A := by
    rintro _ ⟨θ, hθ, rfl⟩
    by_cases hθA : θ ∈ A
    · exact Or.inr ⟨θ, hθA, rfl⟩
    · exact Or.inl ⟨θ, ⟨hθ, hθA⟩, rfl⟩
  have hle : volume (H '' Icc (x - r) (x + r)) ≤ volume (H '' (Icc (x - r) (x + r) \ A)) :=
    (measure_mono hsplit).trans ((measure_union_le _ _).trans (by rw [h0, add_zero]))
  have hv := hle.trans key
  rw [hIcc, Real.volume_Icc] at hv
  have hpos : 0 < H (x + r) - H (x - r) := sub_pos.mpr (hH (by linarith))
  have hv' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    hv
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 1 / 2 by norm_num),
    ENNReal.toReal_ofReal hpos.le] at hv'
  linarith

/-- Helper for `sqs_circle_inv`: the dual threshold property for the inverse lift `G`, with `θ`
depending only on `δf` (`s07_inv_hlift` with `ε = 1/4` on the complement `G[a,b] ∖ G(A)`). -/
theorem s07_inv_dual {δf : ℝ → ℝ} (hδ : 0 < δf (1 / 4)) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ (h : ℂ → ℂ) (H G : ℝ → ℝ), IsStronglyQSWith h δf → StrictMono H →
      Continuous H → (∀ θ, H (θ + 2 * π) = H θ + 2 * π) →
      (∀ θ : ℝ, h (exp (θ * I)) = exp (H θ * I)) → StrictMono G → (∀ θ, H (G θ) = θ) →
      (∀ θ, G (H θ) = θ) → ∀ a b : ℝ, a < b → b - a ≤ 2 * π → ∀ A ⊆ Icc a b, MeasurableSet A →
        volume A ≤ ENNReal.ofReal (1 / 2 * (b - a)) →
          volume (G '' A) ≤ ENNReal.ofReal θ * volume (G '' Icc a b) := by
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = min (δf (1 / 4)) (1 / 2) := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; exact lt_min hδ (by norm_num)
  have hα1 : α ≤ 1 / 2 := by rw [hα]; exact min_le_right _ _
  have hαf : α ≤ δf (1 / 4) := by rw [hα]; exact min_le_left _ _
  refine ⟨1 - α, by linarith, by linarith, ?_⟩
  intro h H G hs hH hHc hper hl hG hHG hGH a b hab hab2 A hAI hA hAs
  have hpre : ∀ X : Set ℝ, G '' X = H ⁻¹' X := by
    intro X
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show H (G x) ∈ X
      rw [hHG]
      exact hx
    · intro hy
      exact ⟨H y, hy, hGH y⟩
  have hHGX : ∀ X : Set ℝ, H '' (G '' X) = X := fun X => by
    rw [image_image]
    simp [hHG]
  have hGI : G '' Icc a b = Icc (G a) (G b) := by
    rw [hpre]
    ext y
    simp only [mem_preimage, mem_Icc]
    rw [← hHG a, ← hHG b, hH.le_iff_le, hH.le_iff_le, hHG, hHG]
  have hGab : G a < G b := hG hab
  have hGab2 : G b - G a ≤ 2 * π := by
    have h1 : H (G b) ≤ H (G a + 2 * π) := by rw [hper, hHG, hHG]; linarith
    have h2 := hH.le_iff_le.mp h1
    linarith
  have hAm' : MeasurableSet (G '' A) := by rw [hpre]; exact hA.preimage hHc.measurable
  have hAsub : G '' A ⊆ Icc (G a) (G b) := hGI ▸ image_mono hAI
  obtain ⟨S, hS⟩ : ∃ S, S = Icc (G a) (G b) \ G '' A := ⟨_, rfl⟩
  have hSm : MeasurableSet S := hS ▸ measurableSet_Icc.diff hAm'
  have hSsub : S ⊆ Icc (G a) (G b) := hS ▸ fun y hy => hy.1
  have hvJ : volume.real (Icc (G a) (G b)) = G b - G a := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  have hsplit : volume.real (G '' A) + volume.real S = G b - G a := by
    rw [hS, measureReal_sdiff hAsub hAm' measure_Icc_lt_top.ne, hvJ]
    ring
  have hAr : volume.real A ≤ 1 / 2 * (b - a) := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by linarith) hAs
  have hHS : H '' S = Icc a b \ A := by
    rw [hS, image_sdiff hH.injective, ← hGI, hHGX, hHGX]
  have hHSr : volume.real (H '' S) = (b - a) - volume.real A := by
    rw [hHS, measureReal_sdiff hAI hA measure_Icc_lt_top.ne, measureReal_def volume (Icc a b),
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  have hAfin : volume (G '' A) ≠ ∞ := ((measure_mono hAsub).trans_lt measure_Icc_lt_top).ne
  rw [hGI, Real.volume_Icc, ← ENNReal.ofReal_mul (by linarith),
    ENNReal.le_ofReal_iff_toReal_le hAfin (mul_nonneg (by linarith) (by linarith)),
    ← measureReal_def]
  by_contra hcon
  rw [not_le] at hcon
  have hSlen : volume S ≤ ENNReal.ofReal (δf (1 / 4) * (G b - G a)) := by
    rw [← ofReal_measureReal ((measure_mono hSsub).trans_lt measure_Icc_lt_top).ne]
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  have key := s07_inv_hlift hs hH hHc hper hl (ε := 1 / 4) (by norm_num) (G a) (G b) hGab
    hGab2 S hSsub hSm hSlen
  have hHJ : H '' Icc (G a) (G b) = Icc a b := by rw [← hGI, hHGX]
  rw [hHJ, Real.volume_Icc] at key
  have key' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    key
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by linarith),
    ← measureReal_def, hHSr] at key'
  linarith

/-- Helper for `sqs_circle_inv`: the power form for the inverse lift `G`, with `C, δ` depending
only on `δf` (`s07_cz_power` for the measure `A ↦ |G(A)| = |H⁻¹(A)|`, absolutely continuous by
`s07_inv_null`, whose fixed-threshold condition is `s07_inv_dual`). -/
theorem s07_inv_power (δf : ℝ → ℝ) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ (h : ℂ → ℂ) (H G : ℝ → ℝ), IsStronglyQSWith h δf →
      StrictMono H → Continuous H → (∀ θ, H (θ + 2 * π) = H θ + 2 * π) →
      (∀ θ : ℝ, h (exp (θ * I)) = exp (H θ * I)) → StrictMono G → (∀ θ, H (G θ) = θ) →
      (∀ θ, G (H θ) = θ) → ∀ a b : ℝ, a < b → b - a ≤ 2 * π → ∀ A ⊆ Icc a b, MeasurableSet A →
        volume (G '' A) ≤
          ENNReal.ofReal (C * ((volume A).toReal / (b - a)) ^ δ) * volume (G '' Icc a b) := by
  by_cases hδ : 0 < δf (1 / 4)
  · obtain ⟨θ, hθ0, hθ1, hdual⟩ := s07_inv_dual hδ
    obtain ⟨C, δ, hC, hδ0, hcz⟩ := s07_cz_power (β := 1 / 2) (by norm_num) (by norm_num) hθ0 hθ1
    refine ⟨C, δ, hC, hδ0, ?_⟩
    intro h H G hs hH hHc hper hl hG hHG hGH a b hab hab2 A hAI hA
    have hpre : ∀ X : Set ℝ, G '' X = H ⁻¹' X := by
      intro X
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        show H (G x) ∈ X
        rw [hHG]
        exact hx
      · intro hy
        exact ⟨H y, hy, hGH y⟩
    have hμ : ∀ X : Set ℝ, MeasurableSet X → Measure.map H volume X = volume (G '' X) :=
      fun X hX => by rw [Measure.map_apply hHc.measurable hX, hpre]
    have hac : Measure.map H volume ≪ volume := by
      refine Measure.AbsolutelyContinuous.mk fun X hX hX0 => ?_
      rw [hμ X hX]
      refine s07_inv_null hs hH hHc hper hl ?_ (measure_mono_null ?_ hX0)
      · rw [hpre]
        exact hX.preimage hHc.measurable
      · rintro _ ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        rw [hHG]
        exact hx
    have key := hcz (Measure.map H volume) hac (2 * π)
      (fun a' b' hab' hab2' F hF hFm hFs => by
        rw [hμ F hFm, hμ _ measurableSet_Icc]
        exact hdual h H G hs hH hHc hper hl hG hHG hGH a' b' hab' hab2' F hF hFm hFs)
      a b hab hab2 A hAI hA
    rw [hμ A hA, hμ _ measurableSet_Icc] at key
    exact key
  · refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro h H G hs
    exact absurd (hs.2 (1 / 4) (by norm_num)).1 hδ

/-- Quantitative inverse of a strongly quasisymmetric map (`A_∞` of the inverse, used for
`thm_TWS`): for every modulus `δf` there are `C, δ > 0`, depending only on `δf`, such that for
every `h` with modulus `δf` and every inverse `hinv` of `h` on `∂𝔻`,
`|hinv(E)| ≤ C (|E|/|I|)^δ |hinv(I)|` for every arc `I = [a, b]` of length `≤ 2π` and measurable
`E ⊆ I`. -/
theorem s07_sqs_inv_power (δf : ℝ → ℝ) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h hinv : ℂ → ℂ, IsStronglyQSWith h δf →
      (∀ ζ ∈ sphere (0 : ℂ) 1, hinv ζ ∈ sphere (0 : ℂ) 1 ∧ h (hinv ζ) = ζ) →
      ∀ a b : ℝ, a < b → b - a ≤ 2 * π → ∀ E ⊆ circleArc a b, MeasurableSet E →
        circleLen (hinv '' E) ≤ ENNReal.ofReal (C * ((circleLen E).toReal / (b - a)) ^ δ) *
          circleLen (hinv '' circleArc a b) := by
  obtain ⟨C, δ, hC, hδ, hP⟩ := s07_inv_power δf
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro h hinv hs hinv1 a b hab hab2 E hEI hE
  obtain ⟨H, hH, hHc, hper, hl⟩ := hs.1
  obtain ⟨G, hG, hGc, hGper, hGl, hHG, hGH⟩ := s07_inv_lift hH hHc hper hl hinv1
  have hexp : Continuous fun θ : ℝ => exp (θ * I) := by fun_prop
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
  have hpre : ∀ X : Set ℝ, G '' X = H ⁻¹' X := by
    intro X
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show H (G x) ∈ X
      rw [hHG]
      exact hx
    · intro hy
      exact ⟨H y, hy, hGH y⟩
  have hGm : ∀ T : Set ℝ, MeasurableSet T → MeasurableSet (G '' T) := fun T hT => by
    rw [hpre]
    exact hT.preimage hHc.measurable
  have hIsub : Icc a b ⊆ Icc a (a + 2 * π) := fun θ hθ => ⟨hθ.1, by linarith [hθ.2]⟩
  have hGab2 : G b ≤ G a + 2 * π := by
    rw [← hGper]
    exact hG.monotone (by linarith)
  have hGsub : ∀ T ⊆ Icc a b, G '' T ⊆ Icc (G a) (G a + 2 * π) := by
    rintro T hT _ ⟨θ, hθ, rfl⟩
    exact ⟨hG.monotone (hT hθ).1, (hG.monotone (hT hθ).2).trans hGab2⟩
  have himg : ∀ T : Set ℝ, hinv '' ((fun θ : ℝ => exp (θ * I)) '' T) =
      (fun θ : ℝ => exp (θ * I)) '' (G '' T) := by
    intro T
    rw [image_image, image_image]
    exact image_congr fun θ _ => hGl θ
  have key := hP h H G hs hH hHc hper hl hG hHG hGH a b hab hab2 S hSI hSm
  rw [hES, show circleArc a b = (fun θ : ℝ => exp (θ * I)) '' Icc a b from rfl, himg, himg,
    s07_circleLen_exp_image a S hSm (hSI.trans hIsub),
    s07_circleLen_exp_image (G a) _ (hGm S hSm) (hGsub S hSI),
    s07_circleLen_exp_image (G a) _ (hGm _ measurableSet_Icc) (hGsub _ subset_rfl)]
  exact key

/-- Group facts (`sec07-transfer.tex:285`): the inverse of a strongly quasisymmetric
homeomorphism is strongly quasisymmetric. -/
theorem sqs_circle_inv (h hinv : ℂ → ℂ) (hh : IsStronglyQS h)
    (hinv1 : ∀ ζ ∈ sphere (0 : ℂ) 1, hinv ζ ∈ sphere (0 : ℂ) 1 ∧ h (hinv ζ) = ζ) :
    IsStronglyQS hinv := by
  obtain ⟨δf, hs⟩ := hh
  obtain ⟨H, hH, hHc, hper, hl⟩ := hs.1
  obtain ⟨G, hG, hGc, hGper, hGl, -, -⟩ := s07_inv_lift hH hHc hper hl hinv1
  obtain ⟨C, δ, hC, hδ, hP⟩ := s07_sqs_inv_power δf
  refine ⟨fun ε => (ε / C) ^ δ⁻¹, ⟨G, hG, hGc, hGper, hGl⟩, fun ε hε =>
    ⟨Real.rpow_pos_of_pos (div_pos hε hC) _, fun a b hab hab2 E hEI hE hlen => ?_⟩⟩
  have hba : 0 < b - a := by linarith
  have hI : circleLen (circleArc a b) = ENNReal.ofReal (b - a) := by
    rw [show circleArc a b = (fun θ : ℝ => exp (θ * I)) '' Icc a b from rfl,
      s07_circleLen_exp_image a _ measurableSet_Icc (fun θ hθ => ⟨hθ.1, by linarith [hθ.2]⟩),
      Real.volume_Icc]
  refine (hP h hinv hs hinv1 a b hab hab2 E hEI hE).trans
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
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

/-- For an injective map with derivative `D`, `|H(S)| = ∫_S |D|`. -/
theorem s07_volume_image_deriv {H D : ℝ → ℝ} (hd : ∀ x, HasDerivAt H (D x) x)
    (hinj : Function.Injective H) (S : Set ℝ) (hS : MeasurableSet S) :
    volume (H '' S) = ∫⁻ x in S, ENNReal.ofReal |D x| := by
  have hdet : ∀ d : ℝ, (ContinuousLinearMap.toSpanSingleton ℝ d).det = d := by
    intro d
    have : ((ContinuousLinearMap.toSpanSingleton ℝ d : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) =
        d • LinearMap.id := by
      ext
      simp
    rw [ContinuousLinearMap.det, this, LinearMap.det_smul, LinearMap.det_id, Module.finrank_self,
      pow_one, mul_one]
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    (fun x _ => (hd x).hasFDerivAt.hasFDerivWithinAt) hinj.injOn (fun _ => 1)
  simp only [mul_one, hdet, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, one_mul] at h
  exact h

/-- `1 - a e^{-iθ}` lies in the slit plane for `|a| < 1`. -/
theorem s07_mob_slit {a : ℂ} (ha : ‖a‖ < 1) (θ : ℝ) :
    1 - a * exp (-(θ * I)) ∈ slitPlane := by
  refine mem_slitPlane_iff.mpr (Or.inl ?_)
  have h1 : (a * exp (-(θ * I))).re ≤ ‖a‖ := by
    calc (a * exp (-(θ * I))).re ≤ ‖a * exp (-(θ * I))‖ := Complex.re_le_norm _
      _ = ‖a‖ := by
          rw [norm_mul, show -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I, mul_one]
  simp only [sub_re, one_re]
  linarith

/-- The lift of `diskMobius t a` on `∂𝔻`:
`e^{it} (ζ - a)/(1 - āζ) = e^{i(t + θ + 2 arg(1 - a e^{-iθ}))}`. -/
theorem s07_mob_lift {a : ℂ} (ha : ‖a‖ < 1) (t θ : ℝ) :
    diskMobius t a (exp (θ * I)) =
      exp (((t + θ + 2 * arg (1 - a * exp (-(θ * I))) : ℝ) : ℂ) * I) := by
  set z := exp (θ * I) with hz
  set w := 1 - a * exp (-(θ * I)) with hwdef
  have hw0 : w ≠ 0 := slitPlane_ne_zero (s07_mob_slit ha θ)
  have hze : z * exp (-(θ * I)) = 1 := by rw [hz, ← Complex.exp_add, add_neg_cancel, exp_zero]
  have hza : z - a = z * w := by rw [hwdef, mul_sub, mul_one, mul_left_comm, hze, mul_one]
  have hcw : conj w = 1 - conj a * z := by
    rw [hwdef, map_sub, map_one, map_mul, ← Complex.exp_conj, map_neg, map_mul,
      Complex.conj_ofReal, Complex.conj_I, hz]
    ring_nf
  have hpolar : (‖w‖ : ℂ) * exp (arg w * I) = w := norm_mul_exp_arg_mul_I w
  have hconj : conj w = (‖w‖ : ℂ) * exp (-(arg w * I)) := by
    conv_lhs => rw [← hpolar]
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    ring_nf
  have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw0
  have hq : w / conj w = exp (2 * arg w * I) := by
    rw [div_eq_iff (by rw [hconj]; exact mul_ne_zero hn (Complex.exp_ne_zero _)), hconj]
    conv_lhs => rw [← hpolar]
    rw [mul_left_comm, ← Complex.exp_add]
    ring_nf
  unfold diskMobius
  rw [hza, ← hcw, mul_div_assoc, hq, hz, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  push_cast
  ring_nf

/-- The derivative of the lift: `H'(θ) = (1 - |a|²)/|e^{iθ} - a|²`. -/
theorem s07_mob_hasDerivAt {a : ℂ} (ha : ‖a‖ < 1) (t θ : ℝ) :
    HasDerivAt (fun θ : ℝ => t + θ + 2 * arg (1 - a * exp (-(θ * I))))
      ((1 - ‖a‖ ^ 2) / ‖exp (θ * I) - a‖ ^ 2) θ := by
  have hin : HasDerivAt (fun θ : ℝ => -((θ : ℂ) * I)) (-(1 * I)) θ :=
    (((hasDerivAt_id θ).ofReal_comp).mul_const I).neg
  have hw : HasDerivAt (fun θ : ℝ => 1 - a * exp (-((θ : ℂ) * I)))
      (-(a * (exp (-((θ : ℂ) * I)) * -(1 * I)))) θ :=
    ((hin.cexp).const_mul a).const_sub 1
  have hlog := hw.clog_real (s07_mob_slit ha θ)
  have him : HasDerivAt (fun θ : ℝ => arg (1 - a * exp (-((θ : ℂ) * I))))
      (Complex.imCLM (-(a * (exp (-((θ : ℂ) * I)) * -(1 * I))) /
        (1 - a * exp (-((θ : ℂ) * I))))) θ := by
    have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hlog
    have hfun : (fun θ : ℝ => arg (1 - a * exp (-((θ : ℂ) * I)))) =
        ⇑Complex.imCLM ∘ fun x : ℝ => log (1 - a * exp (-((x : ℂ) * I))) := by
      funext x
      simp [Complex.log_im]
    rw [hfun]
    exact this
  have hH := (((hasDerivAt_id θ).const_add t).add (him.const_mul 2))
  convert hH using 1
  · funext x
    simp
  -- the value of the derivative
  set ζ := exp (θ * I) with hζ
  have hζn : ‖ζ‖ = 1 := by rw [hζ]; exact Complex.norm_exp_ofReal_mul_I θ
  have hζa : ζ - a ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h] at hζn
    linarith
  have he : exp (-((θ : ℂ) * I)) = ζ⁻¹ := by rw [hζ, ← Complex.exp_neg]
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have hq : -(a * (exp (-((θ : ℂ) * I)) * -(1 * I))) / (1 - a * exp (-((θ : ℂ) * I))) =
      I * (a * conj (ζ - a)) / (normSq (ζ - a) : ℂ) := by
    rw [he]
    have h1 : 1 - a * ζ⁻¹ = (ζ - a) / ζ := by field_simp
    rw [h1, show ((normSq (ζ - a) : ℝ) : ℂ) = (ζ - a) * conj (ζ - a) from
      (Complex.mul_conj _).symm]
    have hc : conj (ζ - a) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hζa
    field_simp
  rw [hq]
  have hre : (I * (a * conj (ζ - a)) / (normSq (ζ - a) : ℂ)).im =
      (a * conj (ζ - a)).re / normSq (ζ - a) := by
    rw [Complex.div_ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  simp only [Complex.imCLM_apply, hre]
  have hnz : (0 : ℝ) < normSq (ζ - a) := Complex.normSq_pos.mpr hζa
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  have hζn' : ζ.re * ζ.re + ζ.im * ζ.im = 1 := by
    have : normSq ζ = 1 := by rw [Complex.normSq_eq_norm_sq, hζn]; norm_num
    rwa [Complex.normSq_apply] at this
  field_simp
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im]
  linarith [hζn']

/-- The lift `H(θ) = t + θ + 2 arg(1 - a e^{-iθ})` of `diskMobius t a`: its derivative lies between
`(1-|a|)/(1+|a|)` and `(1+|a|)/(1-|a|)`, and `H` is a continuous increasing lift. -/
theorem s07_mob_props {a : ℂ} (ha1 : ‖a‖ < 1) (t : ℝ) :
    (∀ θ : ℝ, (1 - ‖a‖) / (1 + ‖a‖) ≤ (1 - ‖a‖ ^ 2) / ‖exp (θ * I) - a‖ ^ 2 ∧
      (1 - ‖a‖ ^ 2) / ‖exp (θ * I) - a‖ ^ 2 ≤ (1 + ‖a‖) / (1 - ‖a‖)) ∧
    StrictMono (fun θ : ℝ => t + θ + 2 * arg (1 - a * exp (-(θ * I)))) ∧
    Continuous (fun θ : ℝ => t + θ + 2 * arg (1 - a * exp (-(θ * I)))) ∧
    ∀ θ : ℝ, t + (θ + 2 * π) + 2 * arg (1 - a * exp (-(((θ + 2 * π : ℝ) : ℂ) * I))) =
      t + θ + 2 * arg (1 - a * exp (-(θ * I))) + 2 * π := by
  set H : ℝ → ℝ := fun θ => t + θ + 2 * arg (1 - a * exp (-(θ * I))) with hHdef
  set D : ℝ → ℝ := fun θ => (1 - ‖a‖ ^ 2) / ‖exp (θ * I) - a‖ ^ 2 with hDdef
  have hd : ∀ θ, HasDerivAt H (D θ) θ := fun θ => s07_mob_hasDerivAt ha1 t θ
  have hr0 : 0 < 1 - ‖a‖ := by linarith
  have hr1 : 0 < 1 + ‖a‖ := by linarith [norm_nonneg a]
  set c₀ := (1 - ‖a‖) / (1 + ‖a‖) with hc₀
  set C₀ := (1 + ‖a‖) / (1 - ‖a‖) with hC₀
  have hc0 : 0 < c₀ := div_pos hr0 hr1
  have hC0 : 0 < C₀ := div_pos hr1 hr0
  have hDb : ∀ θ, c₀ ≤ D θ ∧ D θ ≤ C₀ := by
    intro θ
    have hn1 : ‖exp (θ * I) - a‖ ≤ 1 + ‖a‖ := by
      calc _ ≤ ‖exp (θ * I)‖ + ‖a‖ := norm_sub_le _ _
        _ = 1 + ‖a‖ := by rw [Complex.norm_exp_ofReal_mul_I]
    have hn2 : 1 - ‖a‖ ≤ ‖exp (θ * I) - a‖ := by
      have := norm_sub_norm_le (exp (θ * I)) a
      rwa [Complex.norm_exp_ofReal_mul_I] at this
    have hnum : 1 - ‖a‖ ^ 2 = (1 - ‖a‖) * (1 + ‖a‖) := by ring
    have hnpos : 0 < ‖exp (θ * I) - a‖ := lt_of_lt_of_le hr0 hn2
    constructor
    · show (1 - ‖a‖) / (1 + ‖a‖) ≤ (1 - ‖a‖ ^ 2) / ‖exp (θ * I) - a‖ ^ 2
      rw [div_le_div_iff₀ hr1 (by positivity), hnum]
      have : ‖exp (θ * I) - a‖ ^ 2 ≤ (1 + ‖a‖) ^ 2 := pow_le_pow_left₀ hnpos.le hn1 2
      nlinarith
    · show (1 - ‖a‖ ^ 2) / ‖exp (θ * I) - a‖ ^ 2 ≤ (1 + ‖a‖) / (1 - ‖a‖)
      rw [div_le_div_iff₀ (by positivity) hr0, hnum]
      have : (1 - ‖a‖) ^ 2 ≤ ‖exp (θ * I) - a‖ ^ 2 := pow_le_pow_left₀ hr0.le hn2 2
      nlinarith
  have hmono : StrictMono H := strictMono_of_deriv_pos fun θ => by
    rw [(hd θ).deriv]
    exact lt_of_lt_of_le hc0 (hDb θ).1
  have hcont : Continuous H := continuous_iff_continuousAt.mpr fun θ => (hd θ).continuousAt
  have hper : ∀ θ : ℝ, H (θ + 2 * π) = H θ + 2 * π := by
    intro θ
    simp only [hHdef]
    rw [show -(((θ + 2 * π : ℝ) : ℂ) * I) = -((θ : ℂ) * I) + -(2 * π * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_neg (2 * π * I), Complex.exp_two_pi_mul_I, inv_one, mul_one]
    ring
  exact ⟨hDb, hmono, hcont, hper⟩

/-- `sec07-transfer.tex:287`: Möbius automorphisms of `∂𝔻` are strongly quasisymmetric. -/
theorem sqs_circle_mobius (t : ℝ) (a : ℂ) (ha : a ∈ unitDisc) :
    IsStronglyQS (diskMobius t a) := by
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  set H : ℝ → ℝ := fun θ => t + θ + 2 * arg (1 - a * exp (-(θ * I))) with hHdef
  set D : ℝ → ℝ := fun θ => (1 - ‖a‖ ^ 2) / ‖exp (θ * I) - a‖ ^ 2 with hDdef
  have hd : ∀ θ, HasDerivAt H (D θ) θ := fun θ => s07_mob_hasDerivAt ha1 t θ
  have hr0 : 0 < 1 - ‖a‖ := by linarith
  have hr1 : 0 < 1 + ‖a‖ := by linarith [norm_nonneg a]
  set c₀ := (1 - ‖a‖) / (1 + ‖a‖) with hc₀
  set C₀ := (1 + ‖a‖) / (1 - ‖a‖) with hC₀
  have hc0 : 0 < c₀ := div_pos hr0 hr1
  have hC0 : 0 < C₀ := div_pos hr1 hr0
  obtain ⟨hDb, hmono, hcont, hper⟩ : (∀ θ, c₀ ≤ D θ ∧ D θ ≤ C₀) ∧ StrictMono H ∧ Continuous H ∧
      ∀ θ : ℝ, H (θ + 2 * π) = H θ + 2 * π := s07_mob_props ha1 t
  have heq : ∀ θ : ℝ, diskMobius t a (exp (θ * I)) = exp (H θ * I) := fun θ =>
    s07_mob_lift ha1 t θ
  have hDabs : ∀ θ, ENNReal.ofReal |D θ| = ENNReal.ofReal (D θ) := fun θ => by
    rw [abs_of_pos (lt_of_lt_of_le hc0 (hDb θ).1)]
  have hup : ∀ S : Set ℝ, MeasurableSet S → volume (H '' S) ≤ ENNReal.ofReal C₀ * volume S := by
    intro S hS
    rw [s07_volume_image_deriv hd hmono.injective S hS, ← setLIntegral_const]
    exact lintegral_mono fun θ => by rw [hDabs]; exact ENNReal.ofReal_le_ofReal (hDb θ).2
  have hlow : ∀ S : Set ℝ, MeasurableSet S → ENNReal.ofReal c₀ * volume S ≤ volume (H '' S) := by
    intro S hS
    rw [s07_volume_image_deriv hd hmono.injective S hS, ← setLIntegral_const]
    exact lintegral_mono fun θ => by rw [hDabs]; exact ENNReal.ofReal_le_ofReal (hDb θ).1
  refine ⟨fun ε => ε * c₀ / C₀, ⟨H, hmono, hcont, hper, heq⟩, fun ε hε =>
    ⟨by positivity, fun a₁ b₁ hab hab2 E hEI hE hlen => ?_⟩⟩
  have hexp : Continuous fun θ : ℝ => exp (θ * I) := by fun_prop
  set S := Icc a₁ b₁ ∩ (fun θ : ℝ => exp (θ * I)) ⁻¹' E with hSdef
  have hSm : MeasurableSet S := measurableSet_Icc.inter (hE.preimage hexp.measurable)
  have hES : E = (fun θ : ℝ => exp (θ * I)) '' S := by
    ext z
    constructor
    · intro hz
      obtain ⟨θ, hθ, rfl⟩ := hEI hz
      exact ⟨θ, ⟨hθ, hz⟩, rfl⟩
    · rintro ⟨θ, hθ, rfl⟩
      exact hθ.2
  have hIsub : Icc a₁ b₁ ⊆ Icc a₁ (a₁ + 2 * π) := fun θ hθ => ⟨hθ.1, by linarith [hθ.2]⟩
  have hSsub : S ⊆ Icc a₁ (a₁ + 2 * π) := inter_subset_left.trans hIsub
  have hHab2 : H b₁ ≤ H a₁ + 2 * π := by
    have := hmono.monotone (show b₁ ≤ a₁ + 2 * π by linarith)
    rwa [hper] at this
  have hHsub : ∀ T ⊆ Icc a₁ b₁, H '' T ⊆ Icc (H a₁) (H a₁ + 2 * π) := by
    rintro T hT _ ⟨θ, hθ, rfl⟩
    exact ⟨hmono.monotone (hT hθ).1, (hmono.monotone (hT hθ).2).trans hHab2⟩
  have himg : ∀ T : Set ℝ, diskMobius t a '' ((fun θ : ℝ => exp (θ * I)) '' T) =
      (fun θ : ℝ => exp (θ * I)) '' (H '' T) := by
    intro T
    rw [image_image, image_image]
    exact image_congr fun θ _ => heq θ
  have hHm : ∀ T : Set ℝ, MeasurableSet T → MeasurableSet (H '' T) := fun T hT =>
    hT.image_of_continuousOn_injOn hcont.continuousOn hmono.injective.injOn
  have hlenE : circleLen E = volume S := by
    rw [hES]
    exact s07_circleLen_exp_image a₁ S hSm hSsub
  have hlenI : circleLen (circleArc a₁ b₁) = volume (Icc a₁ b₁) :=
    s07_circleLen_exp_image a₁ _ measurableSet_Icc hIsub
  have hlenhE : circleLen (diskMobius t a '' E) = volume (H '' S) := by
    rw [hES, himg]
    exact s07_circleLen_exp_image (H a₁) _ (hHm S hSm) (hHsub S inter_subset_left)
  have hlenhI : circleLen (diskMobius t a '' circleArc a₁ b₁) = volume (H '' Icc a₁ b₁) := by
    rw [show circleArc a₁ b₁ = (fun θ : ℝ => exp (θ * I)) '' Icc a₁ b₁ from rfl, himg]
    exact s07_circleLen_exp_image (H a₁) _ (hHm _ measurableSet_Icc) (hHsub _ subset_rfl)
  rw [hlenE, hlenI] at hlen
  rw [hlenhE, hlenhI]
  calc volume (H '' S) ≤ ENNReal.ofReal C₀ * volume S := hup S hSm
    _ ≤ ENNReal.ofReal C₀ * (ENNReal.ofReal (ε * c₀ / C₀) * volume (Icc a₁ b₁)) :=
        mul_le_mul_right hlen _
    _ = ENNReal.ofReal ε * (ENNReal.ofReal c₀ * volume (Icc a₁ b₁)) := by
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hC0.le, ← ENNReal.ofReal_mul hε.le]
        congr 2
        field_simp
    _ ≤ ENNReal.ofReal ε * volume (H '' Icc a₁ b₁) :=
        mul_le_mul_right (hlow _ measurableSet_Icc) _

/-- `conj e^{ix} = e^{-ix}`. -/
theorem s07_conj_exp (x : ℝ) : conj (exp (x * I)) = exp (((-x : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring_nf

/-- `c₀(circleArc a b) = circleArc (-b) (-a)`. -/
theorem s07_conj_circleArc (a b : ℝ) :
    (fun z => conj z) '' circleArc a b = circleArc (-b) (-a) := by
  ext w
  constructor
  · rintro ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩
    exact ⟨-θ, ⟨by linarith [hθ.2], by linarith [hθ.1]⟩, (s07_conj_exp θ).symm⟩
  · rintro ⟨φ, hφ, rfl⟩
    refine ⟨exp (((-φ : ℝ) : ℂ) * I), ⟨-φ, ⟨by linarith [hφ.2], by linarith [hφ.1]⟩, rfl⟩, ?_⟩
    simp only
    rw [s07_conj_exp, neg_neg]

/-- `|c₀(S)| = |S|` for measurable `S`. -/
theorem s07_circleLen_conj (S : Set ℂ) (hS : MeasurableSet S) :
    circleLen ((fun z => conj z) '' S) = circleLen S := by
  have hexp : Continuous fun θ : ℝ => exp (θ * I) := by fun_prop
  have himg : (fun z => conj z) '' S = (fun z => conj z) ⁻¹' S :=
    congrFun (image_eq_preimage_of_inverse (f := fun z : ℂ => conj z) (g := fun z : ℂ => conj z)
      (fun z => Complex.conj_conj z) (fun z => Complex.conj_conj z)) S
  unfold circleLen
  rw [himg]
  set B : Set ℝ := {θ | θ ∈ Ico 0 (2 * π) ∧ exp (θ * I) ∈ S} with hB
  set A : Set ℝ := {θ | θ ∈ Ico 0 (2 * π) ∧ exp (θ * I) ∈ (fun z => conj z) ⁻¹' S} with hA
  have hBm : MeasurableSet (B ∩ Ioo 0 (2 * π)) :=
    (measurableSet_Ico.inter (hS.preimage hexp.measurable)).inter measurableSet_Ioo
  have hAB : A ∩ Ioo 0 (2 * π) = (fun θ => 2 * π - θ) ⁻¹' (B ∩ Ioo 0 (2 * π)) := by
    ext θ
    simp only [hA, hB, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Ico, mem_Ioo]
    have hper : exp (((2 * π - θ : ℝ) : ℂ) * I) = conj (exp (θ * I)) := by
      rw [s07_conj_exp, show 2 * π - θ = -θ + 2 * π by ring]
      push_cast
      exact Complex.exp_mul_I_periodic _
    rw [hper]
    constructor
    · rintro ⟨⟨-, hθS⟩, h0, h2⟩
      exact ⟨⟨⟨by linarith, by linarith⟩, hθS⟩, by linarith, by linarith⟩
    · rintro ⟨⟨-, hθS⟩, h0, h2⟩
      exact ⟨⟨⟨by linarith, by linarith⟩, hθS⟩, by linarith, by linarith⟩
  have hnull : ∀ X : Set ℝ, X ⊆ Ico 0 (2 * π) → volume X = volume (X ∩ Ioo 0 (2 * π)) := by
    intro X hX
    refine le_antisymm ?_ (measure_mono inter_subset_left)
    calc volume X ≤ volume ((X ∩ Ioo 0 (2 * π)) ∪ {0}) := by
          refine measure_mono fun θ hθ => ?_
          rcases eq_or_lt_of_le (hX hθ).1 with h | h
          · exact Or.inr h.symm
          · exact Or.inl ⟨hθ, h, (hX hθ).2⟩
      _ ≤ volume (X ∩ Ioo 0 (2 * π)) + volume ({0} : Set ℝ) := measure_union_le _ _
      _ = volume (X ∩ Ioo 0 (2 * π)) := by rw [Real.volume_singleton, add_zero]
  rw [hnull A (fun θ hθ => hθ.1), hnull B (fun θ hθ => hθ.1), hAB]
  exact (volume.measurePreserving_sub_left (2 * π)).measure_preimage hBm.nullMeasurableSet

/-- `sec07-transfer.tex:289`: strong quasisymmetry is invariant under conjugation by
`c₀(ζ) = ζ̄`. -/
theorem sqs_circle_conj (h : ℂ → ℂ) (hh : IsStronglyQS h) :
    IsStronglyQS (fun z => conj (h (conj z))) := by
  obtain ⟨δ, ⟨H, hm, hc, hp, he⟩, hq⟩ := hh
  have hcomp : (fun z => conj (h (conj z))) =
      (fun z => conj z) ∘ h ∘ (fun z => conj z) := rfl
  refine ⟨δ, ⟨fun θ => -H (-θ), fun x y hxy => neg_lt_neg (hm (neg_lt_neg hxy)),
    by fun_prop, fun θ => ?_, fun θ => ?_⟩, fun ε hε => ?_⟩
  · show -H (-(θ + 2 * π)) = -H (-θ) + 2 * π
    rw [show -(θ + 2 * π) = -θ - 2 * π by ring, s07_lift_sub_two_pi hp]
    ring
  · simp only
    rw [s07_conj_exp, he, s07_conj_exp]
  obtain ⟨hd, hq1⟩ := hq ε hε
  refine ⟨hd, fun a b hab hab2 E hEI hE hlen => ?_⟩
  have hcm : Measurable fun z : ℂ => conj z := Complex.continuous_conj.measurable
  have hcE : MeasurableSet ((fun z => conj z) '' E) := by
    rw [congrFun (image_eq_preimage_of_inverse (f := fun z : ℂ => conj z)
      (g := fun z : ℂ => conj z) (fun z => Complex.conj_conj z) (fun z => Complex.conj_conj z)) E]
    exact hE.preimage hcm
  have hcEI : (fun z => conj z) '' E ⊆ circleArc (-b) (-a) :=
    (s07_conj_circleArc a b) ▸ image_mono hEI
  have harcm : MeasurableSet (circleArc a b) := by
    unfold circleArc
    exact (isCompact_Icc.image (by fun_prop)).isClosed.measurableSet
  have hlen' : circleLen ((fun z => conj z) '' E) ≤
      ENNReal.ofReal (δ ε) * circleLen (circleArc (-b) (-a)) := by
    rw [s07_circleLen_conj E hE, ← s07_conj_circleArc, s07_circleLen_conj _ harcm]
    exact hlen
  have hstep := hq1 (-b) (-a) (by linarith) (by linarith) _ hcEI hcE hlen'
  have hm1 := s07_measurableSet_image h H hm hc hp he _ hcE
    (hcEI.trans (s07_circleArc_subset _ _))
  have hm2 := s07_measurableSet_image h H hm hc hp he _
    (by unfold circleArc; exact (isCompact_Icc.image (by fun_prop)).isClosed.measurableSet)
    (s07_circleArc_subset (-b) (-a))
  rw [hcomp, image_comp, image_comp, image_comp, image_comp, s07_circleLen_conj _ hm1,
    s07_conj_circleArc, s07_circleLen_conj _ hm2]
  exact hstep

/-- Helper for `ss_circle_comp`/`ss_circle_inv` (John–Nirenberg core): Lebesgue points for
half-open cells. For a locally integrable `g`, at a.e. `x` the averages of `g` over all short
intervals `[c, c + r)` containing `x` converge to `g x`. -/
theorem s07_jn_lebesgue {g : ℝ → ℝ} (hg : ∀ a b : ℝ, IntegrableOn g (Icc a b)) :
    ∀ᵐ x, ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ c r : ℝ, 0 < r → r < ρ → x ∈ Ico c (c + r) →
      |(∫ t in c..c + r, g t) / r - g x| ≤ ε := by
  have hloc : LocallyIntegrable g volume := by
    rw [locallyIntegrable_iff]
    intro k hk
    obtain ⟨a, ha⟩ := hk.bddBelow
    obtain ⟨b, hb⟩ := hk.bddAbove
    exact (hg a b).mono_set fun y hy => ⟨ha hy, hb hy⟩
  have hL := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hloc 1
  filter_upwards [hL] with x hx
  intro ε hε
  have ht : Tendsto (fun r : ℝ => ⨍ y in closedBall x r, ‖g y - g x‖) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hx (fun _ => x) id tendsto_id (eventually_mem_nhdsWithin.mono fun r hr => by
      rw [one_mul]
      exact mem_closedBall_self (le_of_lt hr))
  have hev : {r : ℝ | ⨍ y in closedBall x r, ‖g y - g x‖ < ε / 2} ∈ 𝓝[>] (0 : ℝ) :=
    ht (gt_mem_nhds (by linarith))
  obtain ⟨ρ, hρ, hρs⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨ρ, hρ, fun c r hr hrρ hxc => ?_⟩
  have hB : ⨍ y in closedBall x r, ‖g y - g x‖ < ε / 2 := hρs ⟨hr, hrρ⟩
  have hBi : IntegrableOn (fun y => |g y - g x|) (closedBall x r) := by
    rw [Real.closedBall_eq_Icc]
    exact ((hg _ _).sub continuous_const.integrableOn_Icc).abs
  rw [setAverage_eq, measureReal_def, Real.volume_closedBall, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    at hB
  simp only [Real.norm_eq_abs] at hB
  have hBr : ∫ y in closedBall x r, |g y - g x| < ε * r := by
    have h2 : 0 < 2 * r := by linarith
    rw [inv_mul_lt_iff₀ h2] at hB
    linarith
  have hle : c ≤ c + r := by linarith
  have hgi : IntervalIntegrable g volume c (c + r) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mpr (hg _ _)
  have e : (∫ t in c..c + r, g t) / r - g x = (∫ t in c..c + r, (g t - g x)) / r := by
    rw [intervalIntegral.integral_sub hgi intervalIntegrable_const, intervalIntegral.integral_const,
      smul_eq_mul, show c + r - c = r by ring]
    field_simp
  rw [e, abs_div, abs_of_pos hr, div_le_iff₀ hr]
  have hsub : Ioc c (c + r) ⊆ closedBall x r := by
    intro y hy
    rw [mem_closedBall, Real.dist_eq, abs_le]
    obtain ⟨h1, h2⟩ := hy
    obtain ⟨h3, h4⟩ := hxc
    constructor <;> linarith
  calc |∫ t in c..c + r, (g t - g x)| ≤ ∫ t in c..c + r, |g t - g x| :=
        intervalIntegral.abs_integral_le_integral_abs hle
    _ = ∫ t in Ioc c (c + r), |g t - g x| := intervalIntegral.integral_of_le hle
    _ ≤ ∫ y in closedBall x r, |g y - g x| :=
        setIntegral_mono_set hBi (Eventually.of_forall fun y => abs_nonneg _) hsub.eventuallyLE
    _ ≤ ε * r := hBr.le

/-- Helper for `s07_jn_step`: endpoints of nested half-open intervals. -/
theorem s07_jn_ico_sub {l s L R : ℝ} (hs : 0 < s) (h : Ico l (l + s) ⊆ Ico L R) :
    L ≤ l ∧ l + s ≤ R := by
  have hl : l ∈ Ico L R := h ⟨le_rfl, by linarith⟩
  refine ⟨hl.1, ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  exact lt_irrefl R (h ⟨hl.2.le, hcon⟩).2

/-- Helper for `ss_circle_comp`/`ss_circle_inv` (John–Nirenberg core, one Calderón–Zygmund
step; cf. VC `TentEntropy.maxRatio_selfimprove`): if `α` has mean oscillation `≤ η` on all
subintervals of `[A, B]` and the tail bound `|{|α - α_I| > τ}| ≤ r |I|` holds on all of them, then
`|{|α - α_I| > τ + 4η}| ≤ (r/2) |I|` on all of them. Proof: stop on the maximal dyadic subcells of
`I` with `⨍ |α - α_I| > 2η`. -/
theorem s07_jn_step {α : ℝ → ℝ} (hαm : Measurable α) (hα : ∀ a b : ℝ, IntegrableOn α (Icc a b))
    {A B η : ℝ} (hη : 0 < η)
    (hosc : ∀ p q : ℝ, A ≤ p → p < q → q ≤ B →
      (∫ t in p..q, |α t - (∫ s in p..q, α s) / (q - p)|) / (q - p) ≤ η)
    {τ r : ℝ} (hτ : 0 ≤ τ) (hr : 0 ≤ r)
    (htail : ∀ p q : ℝ, A ≤ p → p < q → q ≤ B →
      volume {x ∈ Ico p q | τ < |α x - (∫ s in p..q, α s) / (q - p)|} ≤
        ENNReal.ofReal (r * (q - p))) :
    ∀ p q : ℝ, A ≤ p → p < q → q ≤ B →
      volume {x ∈ Ico p q | τ + 4 * η < |α x - (∫ s in p..q, α s) / (q - p)|} ≤
        ENNReal.ofReal (r / 2 * (q - p)) := by
  classical
  intro a b hAa hab hbB
  have hba : 0 < b - a := by linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (∫ s in a..b, α s) / (b - a) := ⟨_, rfl⟩
  rw [← hc]
  obtain ⟨D, hD⟩ : ∃ D : ℝ → ℝ, D = fun x => |α x - c| := ⟨_, rfl⟩
  have hDm : Measurable D := by
    rw [hD]
    exact (hαm.sub measurable_const).abs
  have hDi : ∀ x y : ℝ, IntegrableOn D (Icc x y) := fun x y => by
    rw [hD]
    exact ((hα x y).sub continuous_const.integrableOn_Icc).abs
  have hD0 : ∀ x, 0 ≤ D x := fun x => by
    rw [hD]
    exact abs_nonneg _
  have hDii : ∀ x y : ℝ, IntervalIntegrable D volume x y := fun x y =>
    IntegrableOn.intervalIntegrable (hDi (x ⊓ y) (x ⊔ y))
  have hosc0 : (∫ t in a..b, D t) / (b - a) ≤ η := by
    have h0 := hosc a b hAa hab hbB
    rw [← hc] at h0
    rw [hD]
    exact h0
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
  -- the stopping quantity: mean of `D` over a cell
  obtain ⟨dv, hdv⟩ : ∃ dv : ℕ → ℤ → ℝ,
      dv = fun n (k : ℤ) => (∫ t in (a + k * s n)..(a + k * s n + s n), D t) / s n := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ × ℤ → Set ℝ, A = fun p => {x | x ∈ Ico a b ∧
      2 * η < dv p.1 (K p.1 x) ∧ (∀ m < p.1, ¬ 2 * η < dv m (K m x)) ∧ K p.1 x = p.2} :=
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
  -- the two measures compared on the cells
  obtain ⟨T, hT⟩ : ∃ T : Set ℝ, T = {x | τ + 4 * η < D x} := ⟨_, rfl⟩
  have hTm : MeasurableSet T := by
    rw [hT]
    exact measurableSet_lt measurable_const hDm
  have hlin : ∀ l l' : ℝ, l ≤ l' →
      ENNReal.ofReal (∫ t in l..l', D t) = ∫⁻ t in Ico l l', ENNReal.ofReal (D t) := by
    intro l l' hll
    rw [intervalIntegral.integral_of_le hll, ← integral_Ico_eq_integral_Ioc]
    exact ofReal_integral_eq_lintegral_ofReal ((hDi l l').mono_set Ico_subset_Icc_self)
      (Eventually.of_forall fun t => hD0 t)
  have hterm : ∀ p : ℕ × ℤ, MeasurableSet (A p) ∧
      volume.restrict T (A p) ≤ ENNReal.ofReal (r / (2 * η)) *
        (volume.withDensity fun t => ENNReal.ofReal (D t)) (A p) := by
    intro p
    by_cases hne : (A p).Nonempty
    · obtain ⟨x₀, hx₀⟩ := hne
      have hAp := hAcell p x₀ hx₀
      have hsubJ : C p.1 p.2 ⊆ Ico a b := hAp ▸ hAJ p
      simp only [hA, mem_ofPred_eq] at hx₀
      obtain ⟨hx₀J, hx₀b, hx₀g, hx₀k⟩ := hx₀
      have hmeas : MeasurableSet (A p) := by rw [hAp, hCeq]; exact measurableSet_Ico
      refine ⟨hmeas, ?_⟩
      obtain ⟨l, hl⟩ : ∃ l : ℝ, l = a + p.2 * s p.1 := ⟨_, rfl⟩
      have hQ : C p.1 p.2 = Ico l (l + s p.1) := by rw [hCeq, hl]
      have hsn := hs0 p.1
      obtain ⟨hal, hlb⟩ := s07_jn_ico_sub hsn (hQ ▸ hsubJ)
      -- the cell is bad
      have hbad : 2 * η * s p.1 < ∫ t in l..l + s p.1, D t := by
        have h := hx₀b
        rw [hx₀k, hdv] at h
        simp only at h
        rw [← hl, lt_div_iff₀ hsn] at h
        exact h
      -- its parent is not bad
      have hn0 : p.1 ≠ 0 := by
        intro h0
        have hb0 := hx₀b
        rw [h0, hK0 x₀ hx₀J, hdv] at hb0
        simp only [Int.cast_zero, zero_mul, add_zero, hs00, eab] at hb0
        linarith
      obtain ⟨m, hm⟩ : ∃ m, p.1 = m + 1 := Nat.exists_eq_succ_of_ne_zero hn0
      have hpar := hx₀g m (by omega)
      rw [not_lt, hdv] at hpar
      simp only at hpar
      obtain ⟨L, hL⟩ : ∃ L : ℝ, L = a + (K m x₀ : ℝ) * s m := ⟨_, rfl⟩
      rw [← hL, div_le_iff₀ (hs0 m)] at hpar
      have hsub : Ico l (l + s p.1) ⊆ Ico L (L + s m) := by
        rw [← hQ, hL, ← hCeq, ← hx₀k, hm]
        exact hnest m x₀
      obtain ⟨hLl, hlL⟩ := s07_jn_ico_sub hsn hsub
      have hsm : s m = 2 * s p.1 := by rw [hm, hs1]; ring
      have hQP : ∫ t in l..l + s p.1, D t ≤ ∫ t in L..L + s m, D t :=
        intervalIntegral.integral_mono_interval hLl (by linarith) hlL
          (Eventually.of_forall fun t => hD0 t) (hDii _ _)
      have hint : ∫ t in l..l + s p.1, D t ≤ 4 * η * s p.1 := by
        have e : 2 * η * s m = 4 * η * s p.1 := by rw [hsm]; ring
        linarith
      -- the cell mean of `α` is within `4η` of `c`
      have hαi : IntervalIntegrable α volume l (l + s p.1) :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mpr (hα _ _)
      have hmean : |(∫ t in l..l + s p.1, α t) / (l + s p.1 - l) - c| ≤ 4 * η := by
        have e : (∫ t in l..l + s p.1, α t) / (l + s p.1 - l) - c =
            (∫ t in l..l + s p.1, (α t - c)) / s p.1 := by
          rw [intervalIntegral.integral_sub hαi intervalIntegrable_const,
            intervalIntegral.integral_const, smul_eq_mul, show l + s p.1 - l = s p.1 by ring]
          field_simp
        rw [e, abs_div, abs_of_pos hsn, div_le_iff₀ hsn]
        refine (intervalIntegral.abs_integral_le_integral_abs (by linarith)).trans ?_
        rw [hD] at hint
        exact hint
      have htl := htail l (l + s p.1) (hAa.trans hal) (by linarith) (hlb.trans hbB)
      rw [Measure.restrict_apply hmeas, hAp, hQ, withDensity_apply _ (by rw [← hQ, hCeq]; exact
        measurableSet_Ico), ← hlin _ _ (by linarith)]
      calc volume (Ico l (l + s p.1) ∩ T)
          ≤ volume {x ∈ Ico l (l + s p.1) |
              τ < |α x - (∫ s in l..l + s p.1, α s) / (l + s p.1 - l)|} := by
            refine measure_mono fun x hx => ⟨hx.1, ?_⟩
            have h1 : τ + 4 * η < |α x - c| := by
              have h2 := hx.2
              rw [hT] at h2
              rw [hD] at h2
              exact h2
            have h3 := abs_sub_le (α x) ((∫ t in l..l + s p.1, α t) / (l + s p.1 - l)) c
            linarith
        _ ≤ ENNReal.ofReal (r * (l + s p.1 - l)) := htl
        _ = ENNReal.ofReal (r / (2 * η)) * ENNReal.ofReal (2 * η * s p.1) := by
            rw [← ENNReal.ofReal_mul (div_nonneg hr (by linarith)), show l + s p.1 - l = s p.1 by
              ring]
            congr 1
            field_simp
        _ ≤ ENNReal.ofReal (r / (2 * η)) * ENNReal.ofReal (∫ t in l..l + s p.1, D t) :=
            mul_le_mul_right (ENNReal.ofReal_le_ofReal hbad.le) _
    · rw [not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
  have hAm : ∀ p, MeasurableSet (A p) := fun p => (hterm p).1
  have hGm := MeasurableSet.iUnion hAm
  have key := s07_cz_sum hAm hdisj fun p => (hterm p).2
  have hρ₂ : (volume.withDensity fun t => ENNReal.ofReal (D t)) (⋃ p, A p) ≤
      ENNReal.ofReal (η * (b - a)) := by
    calc (volume.withDensity fun t => ENNReal.ofReal (D t)) (⋃ p, A p)
        ≤ (volume.withDensity fun t => ENNReal.ofReal (D t)) (Ico a b) :=
          measure_mono (iUnion_subset hAJ)
      _ = ENNReal.ofReal (∫ t in a..b, D t) := by
          rw [withDensity_apply _ measurableSet_Ico, hlin a b hab.le]
      _ ≤ ENNReal.ofReal (η * (b - a)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [div_le_iff₀ hba] at hosc0
          exact hosc0
  -- off the cells, `D ≤ 2η` a.e. (Lebesgue points)
  have hnull : volume ({x ∈ Ico a b | τ + 4 * η < |α x - c|} \ ⋃ p, A p) = 0 := by
    have hLp := s07_jn_lebesgue hDi
    rw [ae_iff] at hLp
    refine measure_mono_null ?_ hLp
    intro x hx
    obtain ⟨⟨hxJ, hxD⟩, hxA⟩ := hx
    have hxD' : τ + 4 * η < D x := by rw [hD]; exact hxD
    intro hP
    apply hxA
    obtain ⟨ρ, hρ, hρP⟩ := hP ((D x - 2 * η) / 2) (by linarith)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((b - a) / ρ) one_lt_two
    have hsn : s n < ρ := by
      simp only [hs]
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hρ] at hn
      linarith
    have hbad : ∃ n, 2 * η < dv n (K n x) := by
      refine ⟨n, ?_⟩
      have h := hρP _ _ (hs0 n) hsn (by rw [← hCeq]; exact hmemC n x)
      rw [hdv]
      simp only
      rw [abs_le] at h
      linarith [h.1]
    refine mem_iUnion.mpr ⟨(Nat.find hbad, K (Nat.find hbad) x), ?_⟩
    simp only [hA, mem_ofPred_eq]
    exact ⟨hxJ, Nat.find_spec hbad, fun m hm => Nat.find_min hbad hm, trivial⟩
  calc volume {x ∈ Ico a b | τ + 4 * η < |α x - c|}
      ≤ volume ((⋃ p, A p) ∩ T) +
          volume ({x ∈ Ico a b | τ + 4 * η < |α x - c|} \ ⋃ p, A p) := by
        refine (measure_mono fun x hx => ?_).trans (measure_union_le _ _)
        by_cases hxA : x ∈ ⋃ p, A p
        · refine Or.inl ⟨hxA, ?_⟩
          rw [hT, mem_ofPred_eq, hD]
          exact hx.2
        · exact Or.inr ⟨hx, hxA⟩
    _ = volume.restrict T (⋃ p, A p) := by rw [hnull, add_zero, Measure.restrict_apply hGm]
    _ ≤ ENNReal.ofReal (r / (2 * η)) * ENNReal.ofReal (η * (b - a)) :=
        key.trans (mul_le_mul_right hρ₂ _)
    _ = ENNReal.ofReal (r / 2 * (b - a)) := by
        rw [← ENNReal.ofReal_mul (div_nonneg hr (by linarith))]
        congr 1
        field_simp

/-- Helper for `ss_circle_comp`/`ss_circle_inv` (John–Nirenberg core, geometric tail decay;
cf. VC `TentEntropy.maxRatio_geometric`): `|{|α - α_I| > 4ηk}| ≤ 2^{-k} |I|`. -/
theorem s07_jn_tail {α : ℝ → ℝ} (hαm : Measurable α) (hα : ∀ a b : ℝ, IntegrableOn α (Icc a b))
    {A B η : ℝ} (hη : 0 < η)
    (hosc : ∀ p q : ℝ, A ≤ p → p < q → q ≤ B →
      (∫ t in p..q, |α t - (∫ s in p..q, α s) / (q - p)|) / (q - p) ≤ η) (k : ℕ) :
    ∀ p q : ℝ, A ≤ p → p < q → q ≤ B →
      volume {x ∈ Ico p q | 4 * η * k < |α x - (∫ s in p..q, α s) / (q - p)|} ≤
        ENNReal.ofReal ((1 / 2) ^ k * (q - p)) := by
  induction k with
  | zero =>
    intro p q _ hpq _
    rw [pow_zero, one_mul, ← Real.volume_Ico]
    exact measure_mono fun x hx => hx.1
  | succ k ih =>
    intro p q hAp hpq hqB
    have h := s07_jn_step hαm hα hη hosc (τ := 4 * η * k) (r := (1 / 2) ^ k) (by positivity)
      (by positivity) ih p q hAp hpq hqB
    rw [show 4 * η * (k : ℝ) + 4 * η = 4 * η * ((k + 1 : ℕ) : ℝ) by push_cast; ring,
      show (1 / 2 : ℝ) ^ k / 2 = (1 / 2) ^ (k + 1) by ring] at h
    exact h

/-- Helper for `ss_circle_comp`/`ss_circle_inv` (John–Nirenberg exponential moment; cf. VC
`TentEntropy.exp_moment_bound`): small mean oscillation `η ≤ 1/16` on all subintervals of `[A, B]`
gives `∫_I s² e^{|s|} ≤ K η² |I|`, `s = α - α_I`, with a universal `K`. -/
theorem s07_jn_moment :
    ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ → ℝ, (∀ a b : ℝ, IntegrableOn α (Icc a b)) →
      ∀ A B η : ℝ, 0 < η → η ≤ 1 / 16 →
      (∀ p q : ℝ, A ≤ p → p < q → q ≤ B →
        (∫ t in p..q, |α t - (∫ s in p..q, α s) / (q - p)|) / (q - p) ≤ η) →
      ∀ p q : ℝ, A ≤ p → p < q → q ≤ B →
        ∫⁻ x in Ico p q, ENNReal.ofReal ((α x - (∫ s in p..q, α s) / (q - p)) ^ 2 *
          Real.exp |α x - (∫ s in p..q, α s) / (q - p)|) ≤
          ENNReal.ofReal (K * η ^ 2 * (q - p)) := by
  have hρ : ‖(2 / 3 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]
    norm_num
  have hsum : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * (2 / 3 : ℝ) ^ k) := by
    have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hρ
    have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hρ
    have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hρ
    refine ((h2.add (h1.mul_left 2)).add h0).congr fun k => ?_
    ring
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑' k : ℕ, ((k : ℝ) + 1) ^ 2 * (2 / 3 : ℝ) ^ k := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := hS ▸ tsum_nonneg fun k => by positivity
  have he : Real.exp (1 / 4) ≤ 4 / 3 := by
    have h1 : Real.exp (1 / 4) ^ 4 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h2 := Real.exp_one_lt_d9
    rw [← pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num : (4 : ℕ) ≠ 0), h1]
    norm_num at h2 ⊢
    linarith
  refine ⟨64 / 3 * S + 1, by positivity, ?_⟩
  intro α hα A B η hη hη16 hosc p q hAp hpq hqB
  have hq : 0 ≤ q - p := by linarith
  -- pass to a measurable representative
  have hae : AEMeasurable α volume := by
    have hU : (⋃ n : ℕ, Icc (-(n : ℝ)) n) = univ := by
      refine eq_univ_of_forall fun x => mem_iUnion.mpr ⟨⌈|x|⌉₊, ?_⟩
      exact abs_le.mp (Nat.le_ceil |x|)
    have h := (aemeasurable_iUnion_iff (μ := volume) (s := fun n : ℕ => Icc (-(n : ℝ)) n)
      (f := α)).mpr fun n => (hα _ _).aestronglyMeasurable.aemeasurable
    rwa [hU, Measure.restrict_univ] at h
  obtain ⟨α', hα'⟩ : ∃ α' : ℝ → ℝ, α' = hae.mk α := ⟨_, rfl⟩
  have hα'm : Measurable α' := hα' ▸ hae.measurable_mk
  have heq : α =ᵐ[volume] α' := hα' ▸ hae.ae_eq_mk
  have hαi' : ∀ a b : ℝ, IntegrableOn α' (Icc a b) := fun a b =>
    (hα a b).congr (ae_restrict_of_ae heq)
  have hI : ∀ x y : ℝ, (∫ t in x..y, α t) = ∫ t in x..y, α' t := fun x y =>
    intervalIntegral.integral_congr_ae (heq.mono fun t ht _ => ht)
  have hosc' : ∀ p q : ℝ, A ≤ p → p < q → q ≤ B →
      (∫ t in p..q, |α' t - (∫ s in p..q, α' s) / (q - p)|) / (q - p) ≤ η := by
    intro p' q' h1 h2 h3
    have h := hosc p' q' h1 h2 h3
    rw [hI p' q'] at h
    have e2 : (∫ t in p'..q', |α t - (∫ s in p'..q', α' s) / (q' - p')|) =
        ∫ t in p'..q', |α' t - (∫ s in p'..q', α' s) / (q' - p')| :=
      intervalIntegral.integral_congr_ae (heq.mono fun t ht _ => by rw [ht])
    rwa [e2] at h
  rw [hI p q]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (∫ s in p..q, α' s) / (q - p) := ⟨_, rfl⟩
  rw [← hc]
  rw [lintegral_congr_ae ((ae_restrict_of_ae heq).mono fun x hx => by
    show ENNReal.ofReal ((α x - c) ^ 2 * Real.exp |α x - c|) =
      ENNReal.ofReal ((α' x - c) ^ 2 * Real.exp |α' x - c|)
    rw [hx])]
  -- the tail sets
  obtain ⟨Sk, hSk⟩ : ∃ Sk : ℕ → Set ℝ, Sk = fun k : ℕ => {x ∈ Ico p q | 4 * η * k < |α' x - c|} :=
    ⟨_, rfl⟩
  have hSkm : ∀ k, MeasurableSet (Sk k) := fun k => by
    rw [hSk]
    exact measurableSet_Ico.inter (measurableSet_lt measurable_const
      ((hα'm.sub measurable_const).abs))
  have htl : ∀ k, volume (Sk k) ≤ ENNReal.ofReal ((1 / 2) ^ k * (q - p)) := fun k => by
    simp only [hSk, hc]
    exact s07_jn_tail hα'm hαi' hη hosc' k p q hAp hpq hqB
  -- staircase majorant
  have hpt : ∀ x ∈ Ico p q, ENNReal.ofReal ((α' x - c) ^ 2 * Real.exp |α' x - c|) ≤
      ∑' k : ℕ, (Sk k).indicator (fun _ => ENNReal.ofReal ((4 * η * ((k : ℝ) + 1)) ^ 2 *
        Real.exp (4 * η * ((k : ℝ) + 1)))) x := by
    intro x hx
    obtain ⟨t, ht⟩ : ∃ t, t = |α' x - c| := ⟨_, rfl⟩
    have hsq : (α' x - c) ^ 2 = t ^ 2 := by rw [ht, sq_abs]
    rw [hsq, ← ht]
    rcases (abs_nonneg (α' x - c)).eq_or_lt with h0 | h0
    · rw [← ht] at h0
      rw [← h0]
      simp
    · rw [← ht] at h0
      have hex : ∃ k : ℕ, t ≤ 4 * η * ((k : ℝ) + 1) := by
        obtain ⟨k, hk⟩ := exists_nat_gt (t / (4 * η))
        refine ⟨k, ?_⟩
        rw [div_lt_iff₀ (by positivity)] at hk
        nlinarith
      have hk0 := Nat.find_spec hex
      have hmem : x ∈ Sk (Nat.find hex) := by
        rw [hSk]
        refine ⟨hx, ?_⟩
        rw [← ht]
        rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
        · rw [h, Nat.cast_zero, mul_zero]
          exact h0
        · have hmin := Nat.find_min hex (Nat.sub_lt h one_pos)
          rw [not_le, Nat.cast_sub (show 1 ≤ Nat.find hex from h), Nat.cast_one, sub_add_cancel] at hmin
          exact hmin
      refine le_trans ?_ (ENNReal.le_tsum (Nat.find hex))
      rw [indicator_of_mem hmem]
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul (pow_le_pow_left₀ h0.le hk0 2) (Real.exp_le_exp.mpr hk0)
        (Real.exp_pos _).le (by positivity)
  have hterm : ∀ k : ℕ, (4 * η * ((k : ℝ) + 1)) ^ 2 * Real.exp (4 * η * ((k : ℝ) + 1)) *
      ((1 / 2) ^ k * (q - p)) ≤ 64 / 3 * η ^ 2 * (q - p) * (((k : ℝ) + 1) ^ 2 * (2 / 3) ^ k) := by
    intro k
    have hE : Real.exp (4 * η * ((k : ℝ) + 1)) ≤ (4 / 3) ^ (k + 1) := by
      calc Real.exp (4 * η * ((k : ℝ) + 1)) ≤ Real.exp (((k + 1 : ℕ) : ℝ) * (1 / 4)) :=
            Real.exp_le_exp.mpr (by push_cast; nlinarith)
        _ = Real.exp (1 / 4) ^ (k + 1) := Real.exp_nat_mul _ _
        _ ≤ (4 / 3) ^ (k + 1) := pow_le_pow_left₀ (Real.exp_pos _).le he _
    have hpow : (4 / 3 : ℝ) ^ (k + 1) * (1 / 2) ^ k = 4 / 3 * (2 / 3) ^ k := by
      rw [pow_succ, show (2 / 3 : ℝ) = 4 / 3 * (1 / 2) by norm_num, mul_pow]
      ring
    calc (4 * η * ((k : ℝ) + 1)) ^ 2 * Real.exp (4 * η * ((k : ℝ) + 1)) * ((1 / 2) ^ k * (q - p))
        ≤ (4 * η * ((k : ℝ) + 1)) ^ 2 * (4 / 3) ^ (k + 1) * ((1 / 2) ^ k * (q - p)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by positivity))
            (mul_nonneg (by positivity) hq)
      _ = 16 * η ^ 2 * ((k : ℝ) + 1) ^ 2 * ((4 / 3) ^ (k + 1) * (1 / 2) ^ k) * (q - p) := by ring
      _ = 64 / 3 * η ^ 2 * (q - p) * (((k : ℝ) + 1) ^ 2 * (2 / 3) ^ k) := by
          rw [hpow]
          ring
  calc ∫⁻ x in Ico p q, ENNReal.ofReal ((α' x - c) ^ 2 * Real.exp |α' x - c|)
      ≤ ∫⁻ x in Ico p q, ∑' k : ℕ, (Sk k).indicator (fun _ => ENNReal.ofReal
          ((4 * η * ((k : ℝ) + 1)) ^ 2 * Real.exp (4 * η * ((k : ℝ) + 1)))) x :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ico).mpr (Eventually.of_forall hpt))
    _ = ∑' k : ℕ, ∫⁻ x in Ico p q, (Sk k).indicator (fun _ => ENNReal.ofReal
          ((4 * η * ((k : ℝ) + 1)) ^ 2 * Real.exp (4 * η * ((k : ℝ) + 1)))) x :=
        lintegral_tsum fun k => (measurable_const.indicator (hSkm k)).aemeasurable
    _ ≤ ∑' k : ℕ, ENNReal.ofReal ((4 * η * ((k : ℝ) + 1)) ^ 2 * Real.exp (4 * η * ((k : ℝ) + 1)) *
          ((1 / 2) ^ k * (q - p))) := by
        refine tsum_le_tsum fun k => ?_
        rw [lintegral_indicator_const (hSkm k), Measure.restrict_apply (hSkm k),
          ENNReal.ofReal_mul (p := (4 * η * ((k : ℝ) + 1)) ^ 2 * Real.exp (4 * η * ((k : ℝ) + 1)))
            (by positivity)]
        exact mul_le_mul_right ((measure_mono inter_subset_left).trans (htl k)) _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (64 / 3 * η ^ 2 * (q - p) * (((k : ℝ) + 1) ^ 2 * (2 / 3) ^ k)) :=
        tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal (hterm k)
    _ = ENNReal.ofReal (∑' k : ℕ, 64 / 3 * η ^ 2 * (q - p) * (((k : ℝ) + 1) ^ 2 * (2 / 3) ^ k)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (by positivity) (by positivity))
          (hsum.mul_left _)).symm
    _ = ENNReal.ofReal (64 / 3 * η ^ 2 * (q - p) * S) := by rw [tsum_mul_left, hS]
    _ ≤ ENNReal.ofReal ((64 / 3 * S + 1) * η ^ 2 * (q - p)) := by
        apply ENNReal.ofReal_le_ofReal
        linarith [mul_nonneg (sq_nonneg η) hq]

/-- Helper for `s07_ssv_cv`: a function integrable on every compact interval is a.e.-measurable. -/
theorem s07_ssv_aemeas {f : ℝ → ℝ} (hf : ∀ a b : ℝ, IntegrableOn f (Icc a b)) :
    AEMeasurable f volume := by
  have hU : (⋃ n : ℕ, Icc (-(n : ℝ)) n) = univ := by
    refine eq_univ_of_forall fun x => mem_iUnion.mpr ⟨⌈|x|⌉₊, ?_⟩
    exact abs_le.mp (Nat.le_ceil |x|)
  have h := (aemeasurable_iUnion_iff (μ := volume) (s := fun n : ℕ => Icc (-(n : ℝ)) n)
    (f := f)).mpr fun n => (hf _ _).aestronglyMeasurable.aemeasurable
  rwa [hU, Measure.restrict_univ] at h

/-- Helper for `ss_circle_comp`/`ss_circle_inv`: change of variables along `H = H(0) + ∫ u`,
`∫_{[H a, H b]} φ = ∫_{[a, b]} φ(H) u` (the pushforward of `u dx` under `H` is `dx`). -/
theorem s07_ssv_cv {H u : ℝ → ℝ} (hH : StrictMono H) (hHc : Continuous H)
    (hui : ∀ a b : ℝ, IntegrableOn u (Icc a b))
    (hHu : ∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t) (hpos : ∀ᵐ t, 0 < u t)
    {a b : ℝ} (hab : a ≤ b) (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ s in Icc (H a) (H b), φ s = ∫⁻ t in Icc a b, φ (H t) * ENNReal.ofReal (u t) := by
  -- a measurable representative of `u`
  have hae := s07_ssv_aemeas hui
  obtain ⟨u', hu'⟩ : ∃ u' : ℝ → ℝ, u' = hae.mk u := ⟨_, rfl⟩
  have hu'm : Measurable u' := hu' ▸ hae.measurable_mk
  have heq : u =ᵐ[volume] u' := hu' ▸ hae.ae_eq_mk
  have hui' : ∀ x y : ℝ, IntegrableOn u' (Icc x y) := fun x y =>
    (hui x y).congr (ae_restrict_of_ae heq)
  have hii : ∀ x y : ℝ, IntervalIntegrable u' volume x y := fun x y =>
    IntegrableOn.intervalIntegrable (hui' (x ⊓ y) (x ⊔ y))
  have hI : ∀ x y : ℝ, (∫ t in x..y, u t) = ∫ t in x..y, u' t := fun x y =>
    intervalIntegral.integral_congr_ae (heq.mono fun t ht _ => ht)
  have hpos' : ∀ᵐ t, 0 < u' t := (hpos.and heq).mono fun t ht => ht.2 ▸ ht.1
  have hdiff : ∀ x y : ℝ, H y - H x = ∫ t in x..y, u' t := by
    intro x y
    rw [hHu y, hHu x, hI, hI]
    have := intervalIntegral.integral_interval_sub_left (hii 0 y) (hii 0 x)
    linarith
  have hmu : Measurable fun t => ENNReal.ofReal (u' t) := ENNReal.measurable_ofReal.comp hu'm
  have hlin : ∀ x y : ℝ, x ≤ y →
      ∫⁻ t in Icc x y, ENNReal.ofReal (u' t) = ENNReal.ofReal (H y - H x) := by
    intro x y hxy
    rw [hdiff, intervalIntegral.integral_of_le hxy, ← integral_Icc_eq_integral_Ioc]
    exact (ofReal_integral_eq_lintegral_ofReal (hui' x y)
      ((ae_restrict_of_ae hpos').mono fun t ht => ht.le)).symm
  have hHm : Measurable H := hHc.measurable
  -- the pushforward of `u' dx` on `[a, b]` is `dx` on `[H a, H b]`
  have hmap : Measure.map H ((volume.withDensity fun t => ENNReal.ofReal (u' t)).restrict
      (Icc a b)) = volume.restrict (Icc (H a) (H b)) := by
    haveI : IsFiniteMeasure ((volume.withDensity fun t => ENNReal.ofReal (u' t)).restrict
        (Icc a b)) := ⟨by
      rw [Measure.restrict_apply_univ, withDensity_apply _ measurableSet_Icc, hlin a b hab]
      exact ENNReal.ofReal_lt_top⟩
    refine Measure.ext_of_Iic _ _ fun y => ?_
    rw [Measure.map_apply hHm measurableSet_Iic, Measure.restrict_apply measurableSet_Iic,
      Measure.restrict_apply (hHm measurableSet_Iic),
      withDensity_apply _ ((hHm measurableSet_Iic).inter measurableSet_Icc)]
    rcases lt_or_ge y (H a) with hy | hy
    · have h1 : H ⁻¹' Iic y ∩ Icc a b = ∅ := by
        refine eq_empty_of_forall_notMem fun t ht => ?_
        have h3 : H a ≤ H t := hH.monotone ht.2.1
        have h4 : H t ≤ y := ht.1
        linarith
      have h2 : Iic y ∩ Icc (H a) (H b) = ∅ := by
        refine eq_empty_of_forall_notMem fun t ht => ?_
        have h3 : t ≤ y := ht.1
        have h4 : H a ≤ t := ht.2.1
        linarith
      rw [h1, h2]
      simp
    rcases le_or_gt (H b) y with hy' | hy'
    · have h1 : H ⁻¹' Iic y ∩ Icc a b = Icc a b :=
        inter_eq_right.mpr fun t ht => (hH.monotone ht.2).trans hy'
      have h2 : Iic y ∩ Icc (H a) (H b) = Icc (H a) (H b) :=
        inter_eq_right.mpr fun t ht => ht.2.trans hy'
      rw [h1, h2, hlin a b hab, Real.volume_Icc]
    · obtain ⟨z, hz, hzy⟩ := intermediate_value_Icc hab hHc.continuousOn ⟨hy, hy'.le⟩
      have h1 : H ⁻¹' Iic y ∩ Icc a b = Icc a z := by
        ext t
        simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Icc]
        rw [← hzy, hH.le_iff_le]
        constructor
        · rintro ⟨h, h', -⟩
          exact ⟨h', h⟩
        · rintro ⟨h', h⟩
          exact ⟨h, h', h.trans hz.2⟩
      have h2 : Iic y ∩ Icc (H a) (H b) = Icc (H a) y := by
        ext t
        simp only [mem_inter_iff, mem_Iic, mem_Icc]
        constructor
        · rintro ⟨h, h', -⟩
          exact ⟨h', h⟩
        · rintro ⟨h', h⟩
          exact ⟨h, h', h.trans hy'.le⟩
      rw [h1, h2, hlin a z hz.1, Real.volume_Icc, hzy]
  calc ∫⁻ s in Icc (H a) (H b), φ s
      = ∫⁻ s, φ s ∂(Measure.map H ((volume.withDensity fun t => ENNReal.ofReal (u' t)).restrict
          (Icc a b))) := by rw [hmap]
    _ = ∫⁻ t, φ (H t) ∂((volume.withDensity fun t => ENNReal.ofReal (u' t)).restrict
          (Icc a b)) := lintegral_map hφ hHm
    _ = ∫⁻ t in Icc a b, φ (H t) * ENNReal.ofReal (u' t) := by
        rw [setLIntegral_withDensity_eq_setLIntegral_mul _ hmu
          (show Measurable fun t => φ (H t) from hφ.comp hHm) measurableSet_Icc]
        refine lintegral_congr fun t => ?_
        show ENNReal.ofReal (u' t) * φ (H t) = φ (H t) * ENNReal.ofReal (u' t)
        exact mul_comm _ _
    _ = ∫⁻ t in Icc a b, φ (H t) * ENNReal.ofReal (u t) :=
        lintegral_congr_ae ((ae_restrict_of_ae heq).mono fun t ht => by
          show φ (H t) * ENNReal.ofReal (u' t) = φ (H t) * ENNReal.ofReal (u t)
          rw [ht])

/-- Helper for `ss_circle_comp`/`ss_circle_inv`: a lift is uniformly continuous. -/
theorem s07_ssv_unif {H : ℝ → ℝ} (hH : StrictMono H) (hHc : Continuous H)
    (hper : ∀ θ, H (θ + 2 * π) = H θ + 2 * π) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a ≤ b → b - a ≤ δ → H b - H a ≤ ε := by
  intro ε hε
  have hUC := (isCompact_Icc (a := (0 : ℝ)) (b := 4 * π)).uniformContinuousOn_of_continuous
    hHc.continuousOn
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  refine ⟨min (δ / 2) π, lt_min (by linarith) Real.pi_pos, fun a b hab hba => ?_⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = ⌊a / (2 * π)⌋ := ⟨_, rfl⟩
  have h2π := Real.two_pi_pos
  have h1 : (n : ℝ) * (2 * π) ≤ a := by
    have := Int.floor_le (a / (2 * π))
    rw [← hn, le_div_iff₀ h2π] at this
    exact this
  have h2 : a < (n : ℝ) * (2 * π) + 2 * π := by
    have := Int.lt_floor_add_one (a / (2 * π))
    rw [← hn, div_lt_iff₀ h2π] at this
    linarith
  have hc : ((-n : ℤ) : ℝ) = -(n : ℝ) := by push_cast; ring
  have ea := s07_inv_per_int hper (-n) a
  have eb := s07_inv_per_int hper (-n) b
  have hm := min_le_left (δ / 2) π
  have hm2 := min_le_right (δ / 2) π
  have hd := hδu (a + ((-n : ℤ) : ℝ) * (2 * π)) ⟨by rw [hc]; linarith, by rw [hc]; linarith⟩
    (b + ((-n : ℤ) : ℝ) * (2 * π)) ⟨by rw [hc]; linarith, by rw [hc]; nlinarith [Real.pi_pos]⟩
    (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  rw [ea, eb, Real.dist_eq, abs_lt] at hd
  linarith [hd.1]

/-- Helper for `ss_circle_comp`: a lift has an inverse lift. -/
theorem s07_ssv_inv {H : ℝ → ℝ} (hH : StrictMono H) (hHc : Continuous H)
    (hper : ∀ θ, H (θ + 2 * π) = H θ + 2 * π) :
    ∃ G : ℝ → ℝ, StrictMono G ∧ Continuous G ∧ (∀ θ, G (θ + 2 * π) = G θ + 2 * π) ∧
      (∀ θ, H (G θ) = θ) ∧ ∀ θ, G (H θ) = θ := by
  -- `H - id` is `2π`-periodic and continuous, hence bounded
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hHc.sub continuous_id).continuousOn (s := Icc 0 (2 * π)))
  have hpd : Function.Periodic (fun θ => H θ - θ) (2 * π) := fun θ => by
    simp only
    rw [hper]
    ring
  have hbd : ∀ θ, |H θ - θ| ≤ M := by
    intro θ
    obtain ⟨y, hy, hyeq⟩ := hpd.exists_mem_Ico₀ Real.two_pi_pos θ
    have h1 := hM y (Ico_subset_Icc_self hy)
    rw [Real.norm_eq_abs] at h1
    rw [hyeq]
    exact h1
  have htop : Tendsto H atTop atTop := tendsto_atTop_mono (fun θ => by
    show θ + -M ≤ H θ
    linarith [(abs_le.mp (hbd θ)).1]) (tendsto_atTop_add_const_right _ (-M) tendsto_id)
  have hbot : Tendsto H atBot atBot := tendsto_atBot_mono (fun θ => by
    show H θ ≤ θ + M
    linarith [(abs_le.mp (hbd θ)).2]) (tendsto_atBot_add_const_right _ M tendsto_id)
  have hsurj : Function.Surjective H := hHc.surjective htop hbot
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = Function.surjInv hsurj := ⟨_, rfl⟩
  have hHG : ∀ θ, H (G θ) = θ := fun θ => by rw [hG]; exact Function.surjInv_eq hsurj θ
  have hGH : ∀ θ, G (H θ) = θ := fun θ => hH.injective (hHG (H θ))
  have hGm : StrictMono G := fun x y hxy => hH.lt_iff_lt.mp (by rw [hHG, hHG]; exact hxy)
  have hGc : Continuous G :=
    hGm.monotone.continuous_of_surjective fun θ => ⟨H θ, hGH θ⟩
  have hGper : ∀ θ, G (θ + 2 * π) = G θ + 2 * π := fun θ =>
    hH.injective (by rw [hHG, hper, hHG])
  exact ⟨G, hGm, hGc, hGper, hHG, hGH⟩

/-- Helper for `ss_circle_inv`/`ss_circle_comp`: `e^{|x|} <= 1 + |x| e^{|x|}` and
`|x| e^{|x|} <= |x| + x^2 e^{|x|}`. -/
theorem s07_ssv_elem (x : ℝ) :
    Real.exp |x| ≤ 1 + |x| * Real.exp |x| ∧ |x| * Real.exp |x| ≤ |x| + x ^ 2 * Real.exp |x| := by
  have h1 := Real.add_one_le_exp (-|x|)
  have h2 : Real.exp (-|x|) * Real.exp |x| = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hex := Real.exp_pos |x|
  have h0 := abs_nonneg x
  have h3 : Real.exp |x| ≤ 1 + |x| * Real.exp |x| := by
    nlinarith [mul_le_mul_of_nonneg_right h1 hex.le]
  refine ⟨h3, ?_⟩
  rw [← sq_abs x]
  nlinarith [mul_le_mul_of_nonneg_left h3 h0]

/-- Helper for `ss_circle_inv`/`ss_circle_comp`: `|L| e^L <= e^c (|c| + 1) (1 + |L - c| e^{|L - c|})`. -/
theorem s07_ssv_elem2 (c L : ℝ) :
    |L| * Real.exp L ≤ Real.exp c * (|c| + 1) * (1 + |L - c| * Real.exp |L - c|) := by
  have h1 := (s07_ssv_elem (L - c)).1
  have h2 : Real.exp L ≤ Real.exp c * Real.exp |L - c| := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [le_abs_self (L - c)])
  have h3 : |L| ≤ |c| + |L - c| := by linarith [abs_sub_abs_le_abs_sub L c]
  have hc := Real.exp_pos c
  have hc0 := abs_nonneg c
  calc |L| * Real.exp L ≤ (|c| + |L - c|) * (Real.exp c * Real.exp |L - c|) :=
        mul_le_mul h3 h2 (Real.exp_pos _).le (by positivity)
    _ = Real.exp c * (|c| * Real.exp |L - c| + |L - c| * Real.exp |L - c|) := by ring
    _ ≤ Real.exp c * (|c| * (1 + |L - c| * Real.exp |L - c|) +
          (1 + |L - c| * Real.exp |L - c|)) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left h1 hc0)
          (by linarith)) hc.le
    _ = Real.exp c * (|c| + 1) * (1 + |L - c| * Real.exp |L - c|) := by ring

/-- Helper for `ss_circle_inv`/`ss_circle_comp`: the mean oscillation is at most twice the mean
deviation from any constant. -/
theorem s07_ssv_osc_const {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (c : ℝ) :
    (∫ t in a..b, |f t - (∫ s in a..b, f s) / (b - a)|) / (b - a) ≤
      2 * ((∫ t in a..b, |f t - c|) / (b - a)) := by
  have hba : 0 < b - a := by linarith
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (∫ s in a..b, f s) / (b - a) := ⟨_, rfl⟩
  rw [← hm]
  have hfc : IntervalIntegrable (fun t => |f t - c|) volume a b :=
    (hf.sub intervalIntegrable_const).abs
  have hmc : |m - c| ≤ (∫ t in a..b, |f t - c|) / (b - a) := by
    have e : m - c = (∫ t in a..b, (f t - c)) / (b - a) := by
      rw [hm, intervalIntegral.integral_sub hf intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul]
      field_simp
    rw [e, abs_div, abs_of_pos hba]
    exact div_le_div_of_nonneg_right (intervalIntegral.abs_integral_le_integral_abs hab.le) hba.le
  have hint : ∫ t in a..b, |f t - m| ≤ ∫ t in a..b, (|f t - c| + |m - c|) :=
    intervalIntegral.integral_mono_on hab.le (hf.sub intervalIntegrable_const).abs
      (hfc.add intervalIntegrable_const) fun t _ => by
        have := abs_sub_le (f t) c m
        rw [abs_sub_comm c m] at this
        exact this
  rw [intervalIntegral.integral_add hfc intervalIntegrable_const, intervalIntegral.integral_const,
    smul_eq_mul] at hint
  rw [le_div_iff₀ hba] at hmc
  have e2 : 2 * ((∫ t in a..b, |f t - c|) / (b - a)) * (b - a) = 2 * ∫ t in a..b, |f t - c| := by
    field_simp
  rw [div_le_iff₀ hba, e2]
  nlinarith

/-- Helper for `ss_circle_inv`/`ss_circle_comp`: finiteness of a lower integral on all short
intervals gives it on all compact intervals. -/
theorem s07_ssv_cover {g : ℝ → ℝ≥0∞} {δ : ℝ} (hδ : 0 < δ)
    (hg : ∀ p q : ℝ, p ≤ q → q - p ≤ δ → ∫⁻ t in Icc p q, g t ≠ ∞) (a b : ℝ) :
    ∫⁻ t in Icc a b, g t ≠ ∞ := by
  have key : ∀ n : ℕ, ∀ a b : ℝ, b - a ≤ n * δ → ∫⁻ t in Icc a b, g t ≠ ∞ := by
    intro n
    induction n with
    | zero =>
      intro a b hab
      rcases le_or_gt a b with h | h
      · exact hg a b h (by rw [Nat.cast_zero, zero_mul] at hab; linarith)
      · rw [Icc_eq_empty (not_le.mpr h), Measure.restrict_empty, lintegral_zero_measure]
        exact ENNReal.zero_ne_top
    | succ n ih =>
      intro a b hab
      rcases le_or_gt (b - a) δ with h | h
      · rcases le_or_gt a b with h' | h'
        · exact hg a b h' h
        · rw [Icc_eq_empty (not_le.mpr h'), Measure.restrict_empty, lintegral_zero_measure]
          exact ENNReal.zero_ne_top
      · have hsub : Icc a b ⊆ Icc a (a + δ) ∪ Icc (a + δ) b := fun t ht => by
          rcases le_or_gt t (a + δ) with h1 | h1
          · exact Or.inl ⟨ht.1, h1⟩
          · exact Or.inr ⟨h1.le, ht.2⟩
        push_cast at hab
        exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hg a (a + δ) (by linarith)
          (by linarith), ih (a + δ) b (by linarith)⟩)
          ((lintegral_mono_set hsub).trans (lintegral_union_le _ _ _))
  obtain ⟨n, hn⟩ := exists_nat_ge ((b - a) / δ)
  exact key n a b (by rwa [div_le_iff₀ hδ] at hn)

/-- Helper for `ss_circle_inv`/`ss_circle_comp`: the inverse `G` of a lift `H = H(0) + ∫ u` with
`u > 0` a.e. is quasi-measure-preserving (`H` maps null sets to null sets). -/
theorem s07_ssv_qmp {H u G : ℝ → ℝ} (hH : StrictMono H) (hHc : Continuous H)
    (hui : ∀ a b : ℝ, IntegrableOn u (Icc a b))
    (hHu : ∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t) (hpos : ∀ᵐ t, 0 < u t)
    (hGc : Continuous G) (hHG : ∀ θ, H (G θ) = θ) (hGH : ∀ θ, G (H θ) = θ) :
    QuasiMeasurePreserving G volume volume := by
  refine ⟨hGc.measurable, Measure.AbsolutelyContinuous.mk fun Z hZ hZ0 => ?_⟩
  rw [Measure.map_apply hGc.measurable hZ]
  have hpre : G ⁻¹' Z = H '' Z := by
    ext y
    constructor
    · intro hy
      exact ⟨G y, hy, hHG y⟩
    · rintro ⟨x, hx, rfl⟩
      show G (H x) ∈ Z
      rw [hGH]
      exact hx
  rw [hpre]
  have hU : Z = ⋃ n : ℕ, Z ∩ Icc (-(n : ℝ)) n := by
    rw [← inter_iUnion]
    refine (inter_eq_left.mpr fun x _ => mem_iUnion.mpr ⟨⌈|x|⌉₊, ?_⟩).symm
    exact abs_le.mp (Nat.le_ceil |x|)
  rw [hU, image_iUnion]
  refine measure_iUnion_null fun n => ?_
  have hnn : -(n : ℝ) ≤ n := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  obtain ⟨W, hWd⟩ : ∃ W : Set ℝ, W = H '' (Z ∩ Icc (-(n : ℝ)) n) := ⟨_, rfl⟩
  rw [← hWd]
  have hW : MeasurableSet W := hWd ▸
    (hZ.inter measurableSet_Icc).image_of_continuousOn_injOn hHc.continuousOn hH.injective.injOn
  have hWsub : W ⊆ Icc (H (-(n : ℝ))) (H n) := by
    rw [hWd]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hH.monotone hx.2.1, hH.monotone hx.2.2⟩
  have hcv := s07_ssv_cv hH hHc hui hHu hpos hnn (W.indicator 1) (measurable_one.indicator hW)
  have hL : ∫⁻ s in Icc (H (-(n : ℝ))) (H n), W.indicator 1 s = volume W := by
    rw [lintegral_indicator_one hW, Measure.restrict_apply hW, inter_eq_left.mpr hWsub]
  have hR : ∫⁻ t in Icc (-(n : ℝ)) n, W.indicator 1 (H t) * ENNReal.ofReal (u t) = 0 := by
    refine (lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞)) (ae_restrict_of_ae
      ((measure_eq_zero_iff_ae_notMem.mp hZ0).mono fun t ht => ?_))).trans lintegral_zero
    have hnot : H t ∉ W := by
      rw [hWd]
      rintro ⟨x, hx, hxt⟩
      exact ht (hH.injective hxt ▸ hx.1)
    show W.indicator 1 (H t) * ENNReal.ofReal (u t) = 0
    rw [indicator_of_notMem hnot, zero_mul]
  rw [← hL, hcv, hR]

/-- Helper for `ss_circle_inv`/`ss_circle_comp`: change of variables along the inverse lift,
`∫_{[a, b]} ψ(G) = ∫_{[G a, G b]} ψ u` (`s07_ssv_cv` at `G a`, `G b`). -/
theorem s07_ssv_cvG {H u G : ℝ → ℝ} (hH : StrictMono H) (hHc : Continuous H)
    (hui : ∀ a b : ℝ, IntegrableOn u (Icc a b))
    (hHu : ∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t) (hpos : ∀ᵐ t, 0 < u t)
    (hG : StrictMono G) (hGc : Continuous G) (hHG : ∀ θ, H (G θ) = θ) (hGH : ∀ θ, G (H θ) = θ)
    {a b : ℝ} (hab : a ≤ b) (ψ : ℝ → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ s in Icc a b, ψ (G s) = ∫⁻ x in Icc (G a) (G b), ψ x * ENNReal.ofReal (u x) := by
  have h : (∫⁻ s in Icc (H (G a)) (H (G b)), ψ (G s)) =
      ∫⁻ t in Icc (G a) (G b), ψ (G (H t)) * ENNReal.ofReal (u t) :=
    s07_ssv_cv hH hHc hui hHu hpos (hG.monotone hab) (fun s => ψ (G s)) (hψ.comp hGc.measurable)
  rw [hHG, hHG] at h
  rw [h]
  refine lintegral_congr fun x => ?_
  show ψ (G (H x)) * ENNReal.ofReal (u x) = ψ x * ENNReal.ofReal (u x)
  rw [hGH]

/-- Helper for `ss_circle_inv`/`ss_circle_comp`: the first-order exponential moment
`∫_{[A, B]} |s| e^{|s|} <= (η + K η²) (B - A)` (from `s07_jn_moment` and the oscillation bound). -/
theorem s07_ssv_mom : ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ → ℝ, (∀ a b : ℝ, IntegrableOn α (Icc a b)) →
    ∀ A B η : ℝ, 0 < η → η ≤ 1 / 16 →
    (∀ p q : ℝ, A ≤ p → p < q → q ≤ B →
      (∫ t in p..q, |α t - (∫ s in p..q, α s) / (q - p)|) / (q - p) ≤ η) → A < B →
    ∫⁻ x in Icc A B, ENNReal.ofReal (|α x - (∫ s in A..B, α s) / (B - A)| *
      Real.exp |α x - (∫ s in A..B, α s) / (B - A)|) ≤
      ENNReal.ofReal ((η + K * η ^ 2) * (B - A)) := by
  obtain ⟨K, hK, hmom⟩ := s07_jn_moment
  refine ⟨K, hK, fun α hα A B η hη hη16 hosc hAB => ?_⟩
  have hm := hmom α hα A B η hη hη16 hosc A B le_rfl hAB le_rfl
  have h1 := hosc A B le_rfl hAB le_rfl
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (∫ s in A..B, α s) / (B - A) := ⟨_, rfl⟩
  rw [← hc] at hm h1 ⊢
  rw [Measure.restrict_congr_set Ico_ae_eq_Icc] at hm
  have hBA : 0 < B - A := by linarith
  have hi : IntegrableOn (fun x => |α x - c|) (Icc A B) :=
    ((hα A B).sub continuous_const.integrableOn_Icc).abs
  have hl1 : ∫⁻ x in Icc A B, ENNReal.ofReal |α x - c| ≤ ENNReal.ofReal (η * (B - A)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => abs_nonneg _),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hAB.le]
    apply ENNReal.ofReal_le_ofReal
    rwa [div_le_iff₀ hBA] at h1
  calc ∫⁻ x in Icc A B, ENNReal.ofReal (|α x - c| * Real.exp |α x - c|)
      ≤ ∫⁻ x in Icc A B, (ENNReal.ofReal |α x - c| +
          ENNReal.ofReal ((α x - c) ^ 2 * Real.exp |α x - c|)) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_add (q := (α x - c) ^ 2 * Real.exp |α x - c|) (abs_nonneg _)
          (by positivity)]
        exact ENNReal.ofReal_le_ofReal (s07_ssv_elem (α x - c)).2
    _ = (∫⁻ x in Icc A B, ENNReal.ofReal |α x - c|) +
          ∫⁻ x in Icc A B, ENNReal.ofReal ((α x - c) ^ 2 * Real.exp |α x - c|) :=
        lintegral_add_left' (ENNReal.measurable_ofReal.comp_aemeasurable hi.aemeasurable) _
    _ ≤ ENNReal.ofReal (η * (B - A)) + ENNReal.ofReal (K * η ^ 2 * (B - A)) := add_le_add hl1 hm
    _ = ENNReal.ofReal ((η + K * η ^ 2) * (B - A)) := by
        rw [← ENNReal.ofReal_add (mul_nonneg hη.le hBA.le)
          (mul_nonneg (mul_nonneg hK.le (sq_nonneg η)) hBA.le)]
        congr 1
        ring
/-- Helper for `ss_circle_inv` and `hp_wmuc_cor10`: `s07_ssi_rep` with the periodicity of `H`
replaced by the uniform continuity `hGu` of the inverse `G` (its only use there). -/
theorem s07_ssi_rep_uc {H u G : ℝ → ℝ} (hH : StrictMono H) (hHc : Continuous H)
    (hui : ∀ a b : ℝ, IntegrableOn u (Icc a b))
    (hHu : ∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t) (hpos : ∀ᵐ t, 0 < u t)
    (hli : ∀ a b : ℝ, IntegrableOn (fun t => Real.log (u t)) (Icc a b))
    (hv : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a < b → b - a ≤ δ →
      (∫ t in a..b, |Real.log (u t) - (∫ s in a..b, Real.log (u s)) / (b - a)|) / (b - a) ≤ ε)
    (hG : StrictMono G) (hGc : Continuous G) (hHG : ∀ θ, H (G θ) = θ) (hGH : ∀ θ, G (H θ) = θ)
    (hGu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a ≤ b → b - a ≤ δ → G b - G a ≤ ε) :
    (∀ a b : ℝ, IntegrableOn (fun t => 1 / u (G t)) (Icc a b)) ∧
      (∀ θ : ℝ, G θ = G 0 + ∫ t in (0 : ℝ)..θ, 1 / u (G t)) ∧ (∀ᵐ t, 0 < 1 / u (G t)) ∧
      ∀ a b : ℝ, IntegrableOn (fun t => Real.log (1 / u (G t))) (Icc a b) := by
  -- a measurable representative of `u`, transported along `G`
  have hae := s07_ssv_aemeas hui
  obtain ⟨u', hu'⟩ : ∃ u' : ℝ → ℝ, u' = hae.mk u := ⟨_, rfl⟩
  have hu'm : Measurable u' := hu' ▸ hae.measurable_mk
  have heq : u =ᵐ[volume] u' := hu' ▸ hae.ae_eq_mk
  have hqmp := s07_ssv_qmp hH hHc hui hHu hpos hGc hHG hGH
  have heqG : ∀ᵐ t, u (G t) = u' (G t) := hqmp.ae_eq_comp heq
  have hposG : ∀ᵐ t, 0 < u (G t) := hqmp.ae hpos
  have hGm : Measurable fun t => u' (G t) := hu'm.comp hGc.measurable
  have hnn : ∀ᵐ t, 0 ≤ 1 / u (G t) := hposG.mono fun t ht => (one_div_pos.mpr ht).le
  -- `∫_{[x, y]} 1/u(G) = G y - G x`
  have hlin : ∀ x y : ℝ, x ≤ y →
      ∫⁻ t in Icc x y, ENNReal.ofReal (1 / u (G t)) = ENNReal.ofReal (G y - G x) := by
    intro x y hxy
    have h : (∫⁻ t in Icc x y, ENNReal.ofReal (1 / u' (G t))) =
        ∫⁻ z in Icc (G x) (G y), ENNReal.ofReal (1 / u' z) * ENNReal.ofReal (u z) :=
      s07_ssv_cvG hH hHc hui hHu hpos hG hGc hHG hGH hxy (fun z => ENNReal.ofReal (1 / u' z))
        (ENNReal.measurable_ofReal.comp (hu'm.const_div 1))
    rw [lintegral_congr_ae ((ae_restrict_of_ae heqG).mono fun t ht => by
      show ENNReal.ofReal (1 / u (G t)) = ENNReal.ofReal (1 / u' (G t))
      rw [ht]), h, lintegral_congr_ae ((ae_restrict_of_ae (hpos.and heq)).mono fun z hz => by
      show ENNReal.ofReal (1 / u' z) * ENNReal.ofReal (u z) = 1
      rw [← hz.2, ← ENNReal.ofReal_mul (one_div_pos.mpr hz.1).le, one_div_mul_cancel hz.1.ne',
        ENNReal.ofReal_one]), setLIntegral_one, Real.volume_Icc]
  have hint : ∀ a b : ℝ, IntegrableOn (fun t => 1 / u (G t)) (Icc a b) := by
    intro a b
    rcases le_or_gt a b with hab | hab
    · refine ⟨(show Measurable fun t => 1 / u' (G t) from hGm.const_div 1).aestronglyMeasurable.congr
        (ae_restrict_of_ae (heqG.mono fun t ht => by
          show 1 / u' (G t) = 1 / u (G t)
          rw [ht])), ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (ae_restrict_of_ae hnn), hlin a b hab]
      exact ENNReal.ofReal_lt_top
    · rw [Icc_eq_empty (not_le.mpr hab)]
      exact integrableOn_empty
  have hII : ∀ x y : ℝ, x ≤ y → ∫ t in x..y, 1 / u (G t) = G y - G x := by
    intro x y hxy
    rw [intervalIntegral.integral_of_le hxy, ← integral_Icc_eq_integral_Ioc,
      integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hnn) (hint x y).aestronglyMeasurable,
      hlin x y hxy, ENNReal.toReal_ofReal (by linarith [hG.monotone hxy])]
  have hrep : ∀ θ : ℝ, G θ = G 0 + ∫ t in (0 : ℝ)..θ, 1 / u (G t) := by
    intro θ
    rcases le_or_gt 0 θ with h | h
    · rw [hII 0 θ h]
      ring
    · rw [intervalIntegral.integral_symm, hII θ 0 h.le]
      ring
  -- `log (1/u(G))` is locally integrable: on short intervals by `s07_ssv_mom`, then by covering
  obtain ⟨K, hK, hmom⟩ := s07_ssv_mom
  obtain ⟨δ₁, hδ₁, hv₁⟩ := hv (1 / 16) (by norm_num)
  obtain ⟨δ, hδ, hδu⟩ := hGu δ₁ hδ₁
  have hshort : ∀ p q : ℝ, p ≤ q → q - p ≤ δ →
      ∫⁻ t in Icc p q, ENNReal.ofReal |Real.log (1 / u (G t))| ≠ ∞ := by
    intro p q hpq hqp
    rcases hpq.eq_or_lt with h | h
    · rw [setLIntegral_measure_zero _ _ (by rw [h, Real.volume_Icc, sub_self, ENNReal.ofReal_zero])]
      exact ENNReal.zero_ne_top
    have hAB : G p < G q := hG h
    have hBA := hδu p q hpq hqp
    have hm := hmom (fun t => Real.log (u t)) hli (G p) (G q) (1 / 16) (by norm_num) le_rfl
      (fun p' q' h1 h2 h3 => hv₁ p' q' h2 (by linarith)) hAB
    beta_reduce at hm
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (∫ s in G p..G q, Real.log (u s)) / (G q - G p) := ⟨_, rfl⟩
    rw [← hc] at hm
    have hcv : (∫⁻ t in Icc p q, ENNReal.ofReal |Real.log (u' (G t))|) =
        ∫⁻ x in Icc (G p) (G q), ENNReal.ofReal |Real.log (u' x)| * ENNReal.ofReal (u x) :=
      s07_ssv_cvG hH hHc hui hHu hpos hG hGc hHG hGH hpq
        (fun x => ENNReal.ofReal |Real.log (u' x)|)
        (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
          (Real.measurable_log.comp hu'm)))
    rw [lintegral_congr_ae ((ae_restrict_of_ae heqG).mono fun t ht => by
      show ENNReal.ofReal |Real.log (1 / u (G t))| = ENNReal.ofReal |Real.log (u' (G t))|
      rw [ht, one_div, Real.log_inv, abs_neg]), hcv]
    have hle : ∫⁻ x in Icc (G p) (G q), ENNReal.ofReal |Real.log (u' x)| * ENNReal.ofReal (u x) ≤
        ∫⁻ x in Icc (G p) (G q), ENNReal.ofReal (Real.exp c * (|c| + 1)) *
          (1 + ENNReal.ofReal (|Real.log (u x) - c| * Real.exp |Real.log (u x) - c|)) := by
      refine lintegral_mono_ae ((ae_restrict_of_ae (hpos.and heq)).mono fun x hx => ?_)
      rw [← hx.2, ← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add zero_le_one
          (q := |Real.log (u x) - c| * Real.exp |Real.log (u x) - c|) (by positivity),
        ← ENNReal.ofReal_mul (p := Real.exp c * (|c| + 1)) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have h1 := s07_ssv_elem2 c (Real.log (u x))
      rw [Real.exp_log hx.1] at h1
      exact h1
    refine ne_top_of_le_ne_top ?_ hle
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const,
      setLIntegral_one, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr
      ⟨ENNReal.ofReal_ne_top, ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm⟩)
  have hlog : ∀ a b : ℝ, IntegrableOn (fun t => Real.log (1 / u (G t))) (Icc a b) := by
    intro a b
    have hfin := s07_ssv_cover hδ hshort a b
    refine ⟨(show Measurable fun t => Real.log (1 / u' (G t)) from
      Real.measurable_log.comp (hGm.const_div 1)).aestronglyMeasurable.congr
        (ae_restrict_of_ae (heqG.mono fun t ht => by
          show Real.log (1 / u' (G t)) = Real.log (1 / u (G t))
          rw [ht])), ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs]
    exact lt_top_iff_ne_top.mpr hfin
  exact ⟨hint, hrep, hposG.mono fun t ht => one_div_pos.mpr ht, hlog⟩

/-- Helper for `ss_circle_inv` and `hp_wmuc_cor10`: `s07_ssi_osc` with the periodicity of `H`
replaced by the uniform continuity `hGu` of the inverse `G` (its only use there). -/
theorem s07_ssi_osc_uc {H u G : ℝ → ℝ} (hH : StrictMono H) (hHc : Continuous H)
    (hui : ∀ a b : ℝ, IntegrableOn u (Icc a b))
    (hHu : ∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t) (hpos : ∀ᵐ t, 0 < u t)
    (hli : ∀ a b : ℝ, IntegrableOn (fun t => Real.log (u t)) (Icc a b))
    (hv : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a < b → b - a ≤ δ →
      (∫ t in a..b, |Real.log (u t) - (∫ s in a..b, Real.log (u s)) / (b - a)|) / (b - a) ≤ ε)
    (hG : StrictMono G) (hGc : Continuous G) (hHG : ∀ θ, H (G θ) = θ) (hGH : ∀ θ, G (H θ) = θ)
    (hGu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a ≤ b → b - a ≤ δ → G b - G a ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a < b → b - a ≤ δ →
      (∫ t in a..b, |Real.log (1 / u (G t)) -
        (∫ s in a..b, Real.log (1 / u (G s))) / (b - a)|) / (b - a) ≤ ε := by
  intro ε hε
  obtain ⟨-, -, -, hlint⟩ := s07_ssi_rep_uc hH hHc hui hHu hpos hli hv hG hGc hHG hGH hGu
  obtain ⟨K, hK, hmom⟩ := s07_ssv_mom
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min (1 / 16) (ε / (4 * (1 + K))) := ⟨_, rfl⟩
  have hK4 : (0 : ℝ) < 4 * (1 + K) := by linarith
  have hη0 : 0 < η := by
    rw [hη]
    exact lt_min (by norm_num) (div_pos hε hK4)
  have hη16 : η ≤ 1 / 16 := hη ▸ min_le_left _ _
  have hηε : η ≤ ε / (4 * (1 + K)) := hη ▸ min_le_right _ _
  have hcoef : 0 ≤ η + K * η ^ 2 := add_nonneg hη0.le (mul_nonneg hK.le (sq_nonneg η))
  have hfin : 2 * (η + K * η ^ 2) ≤ ε := by
    have h1 : K * η ^ 2 ≤ K * η := mul_le_mul_of_nonneg_left (by nlinarith) hK.le
    have h2 : η * (4 * (1 + K)) ≤ ε := by rwa [le_div_iff₀ hK4] at hηε
    nlinarith [mul_pos hK hη0]
  obtain ⟨δ₁, hδ₁, hv₁⟩ := hv η hη0
  obtain ⟨δ, hδ, hδu⟩ := hGu δ₁ hδ₁
  refine ⟨δ, hδ, fun a b hab hba => ?_⟩
  have hba' : 0 < b - a := by linarith
  have hAB : G a < G b := hG hab
  have hBA := hδu a b hab.le hba
  have hm := hmom (fun t => Real.log (u t)) hli (G a) (G b) η hη0 hη16
    (fun p q h1 h2 h3 => hv₁ p q h2 (by linarith)) hAB
  beta_reduce at hm
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (∫ s in G a..G b, Real.log (u s)) / (G b - G a) := ⟨_, rfl⟩
  rw [← hc] at hm
  -- a measurable representative of `u`
  have hae := s07_ssv_aemeas hui
  obtain ⟨u', hu'⟩ : ∃ u' : ℝ → ℝ, u' = hae.mk u := ⟨_, rfl⟩
  have hu'm : Measurable u' := hu' ▸ hae.measurable_mk
  have heq : u =ᵐ[volume] u' := hu' ▸ hae.ae_eq_mk
  have hqmp := s07_ssv_qmp hH hHc hui hHu hpos hGc hHG hGH
  have heqG : ∀ᵐ t, u (G t) = u' (G t) := hqmp.ae_eq_comp heq
  -- Jensen: `e^c |J| <= ∫_J u = b - a`
  have hJ : Real.exp c * (G b - G a) ≤ b - a := by
    have hii : ∀ x y : ℝ, IntervalIntegrable u volume x y := fun x y =>
      IntegrableOn.intervalIntegrable (hui (x ⊓ y) (x ⊔ y))
    have hlii : IntervalIntegrable (fun t => Real.log (u t)) volume (G a) (G b) :=
      IntegrableOn.intervalIntegrable (hli (G a ⊓ G b) (G a ⊔ G b))
    have hba2 : b - a = ∫ t in G a..G b, u t := by
      have h1 := hHu (G b)
      have h2 := hHu (G a)
      rw [hHG] at h1 h2
      have := intervalIntegral.integral_interval_sub_left (hii 0 (G b)) (hii 0 (G a))
      linarith
    have hI : ∫ t in G a..G b, Real.log (u t) = c * (G b - G a) := by
      rw [hc]
      field_simp [(sub_pos.mpr hAB).ne']
    have hmono : ∫ t in G a..G b, Real.exp c * (1 + (Real.log (u t) - c)) ≤
        ∫ t in G a..G b, u t := by
      refine intervalIntegral.integral_mono_ae_restrict hAB.le
        ((intervalIntegrable_const.add (hlii.sub intervalIntegrable_const)).const_mul _)
        (hii _ _) ((ae_restrict_of_ae hpos).mono fun t ht => ?_)
      have e : Real.log (u t) = c + (Real.log (u t) - c) := by ring
      calc Real.exp c * (1 + (Real.log (u t) - c))
          ≤ Real.exp c * Real.exp (Real.log (u t) - c) :=
            mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (Real.log (u t) - c)])
              (Real.exp_pos c).le
        _ = u t := by rw [← Real.exp_add, ← e, Real.exp_log ht]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const
      (hlii.sub intervalIntegrable_const), intervalIntegral.integral_sub hlii intervalIntegrable_const,
      intervalIntegral.integral_const, intervalIntegral.integral_const, hI, smul_eq_mul,
      smul_eq_mul] at hmono
    rw [hba2]
    linarith
  -- the deviation from `-c` along `G`
  have hL : ∫⁻ t in Icc a b, ENNReal.ofReal |Real.log (1 / u (G t)) - -c| ≤
      ENNReal.ofReal ((η + K * η ^ 2) * (b - a)) := by
    have hcv : (∫⁻ t in Icc a b, ENNReal.ofReal |Real.log (u' (G t)) - c|) =
        ∫⁻ x in Icc (G a) (G b), ENNReal.ofReal |Real.log (u' x) - c| * ENNReal.ofReal (u x) :=
      s07_ssv_cvG hH hHc hui hHu hpos hG hGc hHG hGH hab.le
        (fun x => ENNReal.ofReal |Real.log (u' x) - c|)
        (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
          ((Real.measurable_log.comp hu'm).sub_const c)))
    rw [lintegral_congr_ae ((ae_restrict_of_ae heqG).mono fun t ht => by
      show ENNReal.ofReal |Real.log (1 / u (G t)) - -c| = ENNReal.ofReal |Real.log (u' (G t)) - c|
      rw [ht, one_div, Real.log_inv,
        show -Real.log (u' (G t)) - -c = -(Real.log (u' (G t)) - c) by ring, abs_neg]), hcv]
    calc ∫⁻ x in Icc (G a) (G b), ENNReal.ofReal |Real.log (u' x) - c| * ENNReal.ofReal (u x)
        ≤ ∫⁻ x in Icc (G a) (G b), ENNReal.ofReal (Real.exp c) *
            ENNReal.ofReal (|Real.log (u x) - c| * Real.exp |Real.log (u x) - c|) := by
          refine lintegral_mono_ae ((ae_restrict_of_ae (hpos.and heq)).mono fun x hx => ?_)
          rw [← hx.2, ← ENNReal.ofReal_mul (abs_nonneg _),
            ← ENNReal.ofReal_mul (Real.exp_pos c).le]
          apply ENNReal.ofReal_le_ofReal
          have e : Real.log (u x) = c + (Real.log (u x) - c) := by ring
          have hu : u x = Real.exp c * Real.exp (Real.log (u x) - c) := by
            rw [← Real.exp_add, ← e, Real.exp_log hx.1]
          calc |Real.log (u x) - c| * u x
              = |Real.log (u x) - c| * (Real.exp c * Real.exp (Real.log (u x) - c)) := by
                rw [← hu]
            _ ≤ |Real.log (u x) - c| * (Real.exp c * Real.exp |Real.log (u x) - c|) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                  (Real.exp_le_exp.mpr (le_abs_self _)) (Real.exp_pos c).le) (abs_nonneg _)
            _ = Real.exp c * (|Real.log (u x) - c| * Real.exp |Real.log (u x) - c|) := by ring
      _ = ENNReal.ofReal (Real.exp c) * ∫⁻ x in Icc (G a) (G b),
            ENNReal.ofReal (|Real.log (u x) - c| * Real.exp |Real.log (u x) - c|) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp c) * ENNReal.ofReal ((η + K * η ^ 2) * (G b - G a)) :=
          mul_le_mul_right hm _
      _ ≤ ENNReal.ofReal ((η + K * η ^ 2) * (b - a)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos c).le]
          apply ENNReal.ofReal_le_ofReal
          calc Real.exp c * ((η + K * η ^ 2) * (G b - G a))
              = (η + K * η ^ 2) * (Real.exp c * (G b - G a)) := by ring
            _ ≤ (η + K * η ^ 2) * (b - a) := mul_le_mul_of_nonneg_left hJ hcoef
  have hR : ∫ t in a..b, |Real.log (1 / u (G t)) - -c| ≤ (η + K * η ^ 2) * (b - a) := by
    have hi : IntegrableOn (fun t => |Real.log (1 / u (G t)) - -c|) (Icc a b) :=
      ((hlint a b).sub continuous_const.integrableOn_Icc).abs
    rw [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc]
    have h := ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun t => abs_nonneg _)
    rw [← h] at hL
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hcoef hba'.le)).mp hL
  refine (s07_ssv_osc_const hab ((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr
    (hlint a b)) (-c)).trans ?_
  calc 2 * ((∫ t in a..b, |Real.log (1 / u (G t)) - -c|) / (b - a))
      ≤ 2 * (η + K * η ^ 2) :=
        mul_le_mul_of_nonneg_left (by rw [div_le_iff₀ hba']; exact hR) (by norm_num)
    _ ≤ ε := hfin

/-- Helper for `ss_circle_inv`: the inverse lift `G = H⁻¹` is `G(0) + ∫ v` with `v = 1/u(G)`,
`v > 0` a.e., and `v`, `log v` locally integrable (`log v = -(log u)(G)`; integrability of
`|log u| u` on short intervals from `s07_jn_moment`). -/
theorem s07_ssi_rep {H u G : ℝ → ℝ} (hH : StrictMono H) (hHc : Continuous H)
    (hper : ∀ θ, H (θ + 2 * π) = H θ + 2 * π) (hui : ∀ a b : ℝ, IntegrableOn u (Icc a b))
    (hHu : ∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t) (hpos : ∀ᵐ t, 0 < u t)
    (hli : ∀ a b : ℝ, IntegrableOn (fun t => Real.log (u t)) (Icc a b))
    (hv : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a < b → b - a ≤ δ →
      (∫ t in a..b, |Real.log (u t) - (∫ s in a..b, Real.log (u s)) / (b - a)|) / (b - a) ≤ ε)
    (hG : StrictMono G) (hGc : Continuous G) (hHG : ∀ θ, H (G θ) = θ) (hGH : ∀ θ, G (H θ) = θ) :
    (∀ a b : ℝ, IntegrableOn (fun t => 1 / u (G t)) (Icc a b)) ∧
      (∀ θ : ℝ, G θ = G 0 + ∫ t in (0 : ℝ)..θ, 1 / u (G t)) ∧ (∀ᵐ t, 0 < 1 / u (G t)) ∧
      ∀ a b : ℝ, IntegrableOn (fun t => Real.log (1 / u (G t))) (Icc a b) := by
  have hGper : ∀ θ, G (θ + 2 * π) = G θ + 2 * π := fun θ => by
    have h := hper (G θ)
    rw [hHG] at h
    rw [← h, hGH]
  exact s07_ssi_rep_uc hH hHc hui hHu hpos hli hv hG hGc hHG hGH (s07_ssv_unif hG hGc hGper)

/-- Helper for `ss_circle_inv`: `log (1/u(G))` has vanishing mean oscillation. On `I` with
`J = G(I)`, `⨍_I |log u(G) - c| = ∫_J |log u - c| u / ∫_J u ≤ ⨍_J |s| e^{|s|} ≤ η + Kη²`
(`s = log u - (log u)_J`, Jensen `∫_J u ≥ |J| e^{(log u)_J}`, `s07_jn_moment`). -/
theorem s07_ssi_osc {H u G : ℝ → ℝ} (hH : StrictMono H) (hHc : Continuous H)
    (hper : ∀ θ, H (θ + 2 * π) = H θ + 2 * π) (hui : ∀ a b : ℝ, IntegrableOn u (Icc a b))
    (hHu : ∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t) (hpos : ∀ᵐ t, 0 < u t)
    (hli : ∀ a b : ℝ, IntegrableOn (fun t => Real.log (u t)) (Icc a b))
    (hv : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a < b → b - a ≤ δ →
      (∫ t in a..b, |Real.log (u t) - (∫ s in a..b, Real.log (u s)) / (b - a)|) / (b - a) ≤ ε)
    (hG : StrictMono G) (hGc : Continuous G) (hHG : ∀ θ, H (G θ) = θ) (hGH : ∀ θ, G (H θ) = θ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a < b → b - a ≤ δ →
      (∫ t in a..b, |Real.log (1 / u (G t)) -
        (∫ s in a..b, Real.log (1 / u (G s))) / (b - a)|) / (b - a) ≤ ε := by
  have hGper : ∀ θ, G (θ + 2 * π) = G θ + 2 * π := fun θ => by
    have h := hper (G θ)
    rw [hHG] at h
    rw [← h, hGH]
  exact s07_ssi_osc_uc hH hHc hui hHu hpos hli hv hG hGc hHG hGH (s07_ssv_unif hG hGc hGper)


/-- Helper for `ss_circle_comp`: `|a| e^b <= |a| e^{|a|} + |b| e^{|b|}`. -/
theorem s07_ssc_elem (a b : ℝ) :
    |a| * Real.exp b ≤ |a| * Real.exp |a| + |b| * Real.exp |b| := by
  have h1 : Real.exp b ≤ Real.exp |b| := Real.exp_le_exp.mpr (le_abs_self b)
  have ha := abs_nonneg a
  have hb := abs_nonneg b
  rcases le_total |b| |a| with h | h
  · have h2 : Real.exp |b| ≤ Real.exp |a| := Real.exp_le_exp.mpr h
    nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) ha, mul_nonneg hb (Real.exp_pos |b|).le]
  · nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_right h (Real.exp_pos |b|).le,
      mul_nonneg ha (Real.exp_pos |a|).le]

/-- Helper for `ss_circle_comp`: `∫_{[a, b]} u = H b - H a` as a lower integral (`s07_ssv_cv` with
`φ = 1`). -/
theorem s07_ssv_lin {H u : ℝ → ℝ} (hH : StrictMono H) (hHc : Continuous H)
    (hui : ∀ a b : ℝ, IntegrableOn u (Icc a b))
    (hHu : ∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t) (hpos : ∀ᵐ t, 0 < u t)
    {a b : ℝ} (hab : a ≤ b) :
    ∫⁻ t in Icc a b, ENNReal.ofReal (u t) = ENNReal.ofReal (H b - H a) := by
  have h : (∫⁻ s in Icc (H a) (H b), (1 : ℝ≥0∞)) = ∫⁻ t in Icc a b, 1 * ENNReal.ofReal (u t) :=
    s07_ssv_cv hH hHc hui hHu hpos hab (fun _ => 1) measurable_const
  rw [setLIntegral_one, Real.volume_Icc] at h
  rw [h]
  exact lintegral_congr fun t => (one_mul _).symm

/-- Helper for `ss_circle_comp`: Jensen, `e^{(log u)_{[A, B]}} (B - A) <= ∫_{[A, B]} u = H B - H A`. -/
theorem s07_ssc_jensen {H u : ℝ → ℝ} (hui : ∀ a b : ℝ, IntegrableOn u (Icc a b))
    (hHu : ∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t) (hpos : ∀ᵐ t, 0 < u t)
    (hli : ∀ a b : ℝ, IntegrableOn (fun t => Real.log (u t)) (Icc a b)) {A B : ℝ} (hAB : A < B) :
    Real.exp ((∫ s in A..B, Real.log (u s)) / (B - A)) * (B - A) ≤ H B - H A := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (∫ s in A..B, Real.log (u s)) / (B - A) := ⟨_, rfl⟩
  rw [← hc]
  have hii : ∀ x y : ℝ, IntervalIntegrable u volume x y := fun x y =>
    IntegrableOn.intervalIntegrable (hui (x ⊓ y) (x ⊔ y))
  have hlii : IntervalIntegrable (fun t => Real.log (u t)) volume A B :=
    IntegrableOn.intervalIntegrable (hli (A ⊓ B) (A ⊔ B))
  have hba2 : H B - H A = ∫ t in A..B, u t := by
    have h1 := hHu B
    have h2 := hHu A
    have := intervalIntegral.integral_interval_sub_left (hii 0 B) (hii 0 A)
    linarith
  have hI : ∫ t in A..B, Real.log (u t) = c * (B - A) := by
    rw [hc]
    field_simp [(sub_pos.mpr hAB).ne']
  have hmono : ∫ t in A..B, Real.exp c * (1 + (Real.log (u t) - c)) ≤ ∫ t in A..B, u t := by
    refine intervalIntegral.integral_mono_ae_restrict hAB.le
      ((intervalIntegrable_const.add (hlii.sub intervalIntegrable_const)).const_mul _)
      (hii _ _) ((ae_restrict_of_ae hpos).mono fun t ht => ?_)
    have e : Real.log (u t) = c + (Real.log (u t) - c) := by ring
    calc Real.exp c * (1 + (Real.log (u t) - c))
        ≤ Real.exp c * Real.exp (Real.log (u t) - c) :=
          mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (Real.log (u t) - c)])
            (Real.exp_pos c).le
      _ = u t := by rw [← Real.exp_add, ← e, Real.exp_log ht]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const
    (hlii.sub intervalIntegrable_const), intervalIntegral.integral_sub hlii intervalIntegrable_const,
    intervalIntegral.integral_const, intervalIntegral.integral_const, hI, smul_eq_mul,
    smul_eq_mul] at hmono
  rw [hba2]
  linarith

/-- Helper for `ss_circle_comp`: `∫_{[A, B]} |s₁| v <= e^{c₂} (∫ |s₁| e^{|s₁|} + ∫ |s₂| e^{|s₂|})`
with `s₁ = log u₁ - c₁`, `s₂ = log v - c₂` (pointwise `s07_ssc_elem`). -/
theorem s07_ssc_core {u₁ v : ℝ → ℝ} (hui₁ : ∀ a b : ℝ, IntegrableOn u₁ (Icc a b))
    (hpos₁ : ∀ᵐ t, 0 < u₁ t) (hposv : ∀ᵐ t, 0 < v t) (A B c₁ c₂ : ℝ) :
    ∫⁻ x in Icc A B, ENNReal.ofReal |Real.log (u₁ x) - c₁| * ENNReal.ofReal (v x) ≤
      ENNReal.ofReal (Real.exp c₂) *
        ((∫⁻ x in Icc A B, ENNReal.ofReal (|Real.log (u₁ x) - c₁| *
            Real.exp |Real.log (u₁ x) - c₁|)) +
          ∫⁻ x in Icc A B, ENNReal.ofReal (|Real.log (v x) - c₂| * Real.exp |Real.log (v x) - c₂|)) := by
  have hm : Measurable fun y : ℝ =>
      ENNReal.ofReal (|Real.log y - c₁| * Real.exp |Real.log y - c₁|) :=
    ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp
      (Real.measurable_log.sub_const c₁)).mul (Real.continuous_exp.measurable.comp
        (continuous_abs.measurable.comp (Real.measurable_log.sub_const c₁))))
  have hF : AEMeasurable (fun x => ENNReal.ofReal (|Real.log (u₁ x) - c₁| *
      Real.exp |Real.log (u₁ x) - c₁|)) (volume.restrict (Icc A B)) :=
    (hm.comp_aemeasurable (s07_ssv_aemeas hui₁)).restrict
  rw [← lintegral_add_left' hF, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ((ae_restrict_of_ae (hpos₁.and hposv)).mono fun x hx => ?_)
  show ENNReal.ofReal |Real.log (u₁ x) - c₁| * ENNReal.ofReal (v x) ≤
    ENNReal.ofReal (Real.exp c₂) *
      (ENNReal.ofReal (|Real.log (u₁ x) - c₁| * Real.exp |Real.log (u₁ x) - c₁|) +
        ENNReal.ofReal (|Real.log (v x) - c₂| * Real.exp |Real.log (v x) - c₂|))
  rw [← ENNReal.ofReal_mul (abs_nonneg _),
    ← ENNReal.ofReal_add (p := |Real.log (u₁ x) - c₁| * Real.exp |Real.log (u₁ x) - c₁|)
      (q := |Real.log (v x) - c₂| * Real.exp |Real.log (v x) - c₂|) (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (Real.exp_pos c₂).le]
  apply ENNReal.ofReal_le_ofReal
  have hv : v x = Real.exp c₂ * Real.exp (Real.log (v x) - c₂) := by
    rw [← Real.exp_add, show c₂ + (Real.log (v x) - c₂) = Real.log (v x) by ring,
      Real.exp_log hx.2]
  have h := s07_ssc_elem (Real.log (u₁ x) - c₁) (Real.log (v x) - c₂)
  calc |Real.log (u₁ x) - c₁| * v x
      = |Real.log (u₁ x) - c₁| * (Real.exp c₂ * Real.exp (Real.log (v x) - c₂)) := by rw [← hv]
    _ = Real.exp c₂ * (|Real.log (u₁ x) - c₁| * Real.exp (Real.log (v x) - c₂)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.exp_pos c₂).le

/-- Helper for `ss_circle_comp`: `H₁ ∘ H₂ = H₁(H₂ 0) + ∫ u₁(H₂) u₂`, with positive density a.e.
and locally integrable logarithm (`log u₁(H₂)` via the inverse lift of `H₂`, Cauchy–Schwarz and
`s07_jn_moment`). -/
theorem s07_ssc_rep {H₁ u₁ H₂ u₂ : ℝ → ℝ} (hH₁ : StrictMono H₁) (hH₁c : Continuous H₁)
    (hper₁ : ∀ θ, H₁ (θ + 2 * π) = H₁ θ + 2 * π) (hui₁ : ∀ a b : ℝ, IntegrableOn u₁ (Icc a b))
    (hHu₁ : ∀ θ : ℝ, H₁ θ = H₁ 0 + ∫ t in (0 : ℝ)..θ, u₁ t) (hpos₁ : ∀ᵐ t, 0 < u₁ t)
    (hli₁ : ∀ a b : ℝ, IntegrableOn (fun t => Real.log (u₁ t)) (Icc a b))
    (hv₁ : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a < b → b - a ≤ δ →
      (∫ t in a..b, |Real.log (u₁ t) - (∫ s in a..b, Real.log (u₁ s)) / (b - a)|) / (b - a) ≤ ε)
    (hH₂ : StrictMono H₂) (hH₂c : Continuous H₂)
    (hper₂ : ∀ θ, H₂ (θ + 2 * π) = H₂ θ + 2 * π) (hui₂ : ∀ a b : ℝ, IntegrableOn u₂ (Icc a b))
    (hHu₂ : ∀ θ : ℝ, H₂ θ = H₂ 0 + ∫ t in (0 : ℝ)..θ, u₂ t) (hpos₂ : ∀ᵐ t, 0 < u₂ t)
    (hli₂ : ∀ a b : ℝ, IntegrableOn (fun t => Real.log (u₂ t)) (Icc a b))
    (hv₂ : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a < b → b - a ≤ δ →
      (∫ t in a..b, |Real.log (u₂ t) - (∫ s in a..b, Real.log (u₂ s)) / (b - a)|) / (b - a) ≤ ε) :
    (∀ a b : ℝ, IntegrableOn (fun t => u₁ (H₂ t) * u₂ t) (Icc a b)) ∧
      (∀ θ : ℝ, H₁ (H₂ θ) = H₁ (H₂ 0) + ∫ t in (0 : ℝ)..θ, u₁ (H₂ t) * u₂ t) ∧
      (∀ᵐ t, 0 < u₁ (H₂ t) * u₂ t) ∧
      ∀ a b : ℝ, IntegrableOn (fun t => Real.log (u₁ (H₂ t) * u₂ t)) (Icc a b) := by
  -- `hper₁` is not needed (the statement stays true without it); kept for the frozen interface
  have _h := hper₁
  -- the inverse lift `G₂` of `H₂` and its density `v = 1/u₂(G₂)`
  obtain ⟨G₂, hG₂, hG₂c, hG₂per, hHG₂, hGH₂⟩ := s07_ssv_inv hH₂ hH₂c hper₂
  obtain ⟨hvi, hvrep, hvpos, hvli⟩ :=
    s07_ssi_rep hH₂ hH₂c hper₂ hui₂ hHu₂ hpos₂ hli₂ hv₂ hG₂ hG₂c hHG₂ hGH₂
  have hvv := s07_ssi_osc hH₂ hH₂c hper₂ hui₂ hHu₂ hpos₂ hli₂ hv₂ hG₂ hG₂c hHG₂ hGH₂
  have hq₂ := s07_ssv_qmp hG₂ hG₂c hvi hvrep hvpos hH₂c hGH₂ hHG₂
  -- a measurable representative of `u₁`, transported along `H₂`
  have hae₁ := s07_ssv_aemeas hui₁
  obtain ⟨u₁', hu₁'⟩ : ∃ u₁' : ℝ → ℝ, u₁' = hae₁.mk u₁ := ⟨_, rfl⟩
  have hu₁'m : Measurable u₁' := hu₁' ▸ hae₁.measurable_mk
  have heq₁ : u₁ =ᵐ[volume] u₁' := hu₁' ▸ hae₁.ae_eq_mk
  have heqH : ∀ᵐ t, u₁ (H₂ t) = u₁' (H₂ t) := hq₂.ae_eq_comp heq₁
  have hposH : ∀ᵐ t, 0 < u₁ (H₂ t) := hq₂.ae hpos₁
  have hwm : AEMeasurable (fun t => u₁ (H₂ t) * u₂ t) volume :=
    ((show AEMeasurable (fun t => u₁ (H₂ t)) volume from
      (hu₁'m.comp hH₂c.measurable).aemeasurable.congr (heqH.mono fun t ht => ht.symm)).mul
        (s07_ssv_aemeas hui₂))
  have hnn : ∀ᵐ t, 0 ≤ u₁ (H₂ t) * u₂ t :=
    (hposH.and hpos₂).mono fun t ht => (mul_pos ht.1 ht.2).le
  -- `∫_{[x, y]} u₁(H₂) u₂ = H₁(H₂ y) - H₁(H₂ x)`
  have hlin : ∀ x y : ℝ, x ≤ y → ∫⁻ t in Icc x y, ENNReal.ofReal (u₁ (H₂ t) * u₂ t) =
      ENNReal.ofReal (H₁ (H₂ y) - H₁ (H₂ x)) := by
    intro x y hxy
    have h : (∫⁻ s in Icc (H₂ x) (H₂ y), ENNReal.ofReal (u₁' s)) =
        ∫⁻ t in Icc x y, ENNReal.ofReal (u₁' (H₂ t)) * ENNReal.ofReal (u₂ t) :=
      s07_ssv_cv hH₂ hH₂c hui₂ hHu₂ hpos₂ hxy (fun s => ENNReal.ofReal (u₁' s))
        (ENNReal.measurable_ofReal.comp hu₁'m)
    have h1 : (∫⁻ s in Icc (H₂ x) (H₂ y), ENNReal.ofReal (u₁' s)) =
        ENNReal.ofReal (H₁ (H₂ y) - H₁ (H₂ x)) := by
      rw [← s07_ssv_lin hH₁ hH₁c hui₁ hHu₁ hpos₁ (hH₂.monotone hxy)]
      exact lintegral_congr_ae ((ae_restrict_of_ae heq₁).mono fun s hs => by
        show ENNReal.ofReal (u₁' s) = ENNReal.ofReal (u₁ s)
        rw [hs])
    rw [← h1, h]
    refine lintegral_congr_ae ((ae_restrict_of_ae ((heqH.and hposH).and hpos₂)).mono fun t ht => ?_)
    show ENNReal.ofReal (u₁ (H₂ t) * u₂ t) = ENNReal.ofReal (u₁' (H₂ t)) * ENNReal.ofReal (u₂ t)
    rw [← ht.1.1, ENNReal.ofReal_mul ht.1.2.le]
  have hint : ∀ a b : ℝ, IntegrableOn (fun t => u₁ (H₂ t) * u₂ t) (Icc a b) := by
    intro a b
    rcases le_or_gt a b with hab | hab
    · refine ⟨hwm.aestronglyMeasurable.restrict, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (ae_restrict_of_ae hnn), hlin a b hab]
      exact ENNReal.ofReal_lt_top
    · rw [Icc_eq_empty (not_le.mpr hab)]
      exact integrableOn_empty
  have hII : ∀ x y : ℝ, x ≤ y → ∫ t in x..y, u₁ (H₂ t) * u₂ t = H₁ (H₂ y) - H₁ (H₂ x) := by
    intro x y hxy
    rw [intervalIntegral.integral_of_le hxy, ← integral_Icc_eq_integral_Ioc,
      integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae hnn) (hint x y).aestronglyMeasurable,
      hlin x y hxy, ENNReal.toReal_ofReal (by linarith [hH₁.monotone (hH₂.monotone hxy)])]
  have hrep : ∀ θ : ℝ, H₁ (H₂ θ) = H₁ (H₂ 0) + ∫ t in (0 : ℝ)..θ, u₁ (H₂ t) * u₂ t := by
    intro θ
    rcases le_or_gt 0 θ with h | h
    · rw [hII 0 θ h]
      ring
    · rw [intervalIntegral.integral_symm, hII θ 0 h.le]
      ring
  -- `log u₁(H₂)` is locally integrable: on short intervals by `s07_ssc_core`, then by covering
  obtain ⟨K, hK, hmom⟩ := s07_ssv_mom
  obtain ⟨δa, hδa, hva⟩ := hv₁ (1 / 16) (by norm_num)
  obtain ⟨δb, hδb, hvb⟩ := hvv (1 / 16) (by norm_num)
  obtain ⟨δ, hδ, hδu⟩ := s07_ssv_unif hH₂ hH₂c hper₂ (min δa δb) (lt_min hδa hδb)
  have hshort : ∀ p q : ℝ, p ≤ q → q - p ≤ δ →
      ∫⁻ t in Icc p q, ENNReal.ofReal |Real.log (u₁ (H₂ t))| ≠ ∞ := by
    intro p q hpq hqp
    rcases hpq.eq_or_lt with h | h
    · rw [setLIntegral_measure_zero _ _ (by rw [h, Real.volume_Icc, sub_self, ENNReal.ofReal_zero])]
      exact ENNReal.zero_ne_top
    have hAB : H₂ p < H₂ q := hH₂ h
    have hBA := hδu p q hpq hqp
    have hma := min_le_left δa δb
    have hmb := min_le_right δa δb
    have hm₁ := hmom (fun t => Real.log (u₁ t)) hli₁ (H₂ p) (H₂ q) (1 / 16) (by norm_num) le_rfl
      (fun p' q' h1 h2 h3 => hva p' q' h2 (by linarith)) hAB
    have hm₂ := hmom (fun t => Real.log (1 / u₂ (G₂ t))) hvli (H₂ p) (H₂ q) (1 / 16) (by norm_num)
      le_rfl (fun p' q' h1 h2 h3 => hvb p' q' h2 (by linarith)) hAB
    beta_reduce at hm₁ hm₂
    obtain ⟨c₁, hc₁⟩ : ∃ c : ℝ, c = (∫ s in H₂ p..H₂ q, Real.log (u₁ s)) / (H₂ q - H₂ p) :=
      ⟨_, rfl⟩
    obtain ⟨c₂, hc₂⟩ : ∃ c : ℝ,
        c = (∫ s in H₂ p..H₂ q, Real.log (1 / u₂ (G₂ s))) / (H₂ q - H₂ p) := ⟨_, rfl⟩
    rw [← hc₁] at hm₁
    rw [← hc₂] at hm₂
    have hcv : (∫⁻ t in Icc p q, ENNReal.ofReal |Real.log (u₁' (H₂ t))|) =
        ∫⁻ x in Icc (H₂ p) (H₂ q), ENNReal.ofReal |Real.log (u₁' x)| *
          ENNReal.ofReal (1 / u₂ (G₂ x)) :=
      s07_ssv_cvG hG₂ hG₂c hvi hvrep hvpos hH₂ hH₂c hGH₂ hHG₂ hpq
        (fun x => ENNReal.ofReal |Real.log (u₁' x)|)
        (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
          (Real.measurable_log.comp hu₁'m)))
    rw [lintegral_congr_ae ((ae_restrict_of_ae heqH).mono fun t ht => by
      show ENNReal.ofReal |Real.log (u₁ (H₂ t))| = ENNReal.ofReal |Real.log (u₁' (H₂ t))|
      rw [ht]), hcv]
    have hva' : AEMeasurable (fun x => ENNReal.ofReal |c₁| * ENNReal.ofReal (1 / u₂ (G₂ x)))
        (volume.restrict (Icc (H₂ p) (H₂ q))) :=
      (ENNReal.measurable_ofReal.comp_aemeasurable (hvi (H₂ p) (H₂ q)).aemeasurable).const_mul _
    have hle : ∫⁻ x in Icc (H₂ p) (H₂ q), ENNReal.ofReal |Real.log (u₁' x)| *
          ENNReal.ofReal (1 / u₂ (G₂ x)) ≤
        (∫⁻ x in Icc (H₂ p) (H₂ q), ENNReal.ofReal |c₁| * ENNReal.ofReal (1 / u₂ (G₂ x))) +
          ∫⁻ x in Icc (H₂ p) (H₂ q), ENNReal.ofReal |Real.log (u₁ x) - c₁| *
            ENNReal.ofReal (1 / u₂ (G₂ x)) := by
      rw [← lintegral_add_left' hva']
      refine lintegral_mono_ae ((ae_restrict_of_ae heq₁).mono fun x hx => ?_)
      show ENNReal.ofReal |Real.log (u₁' x)| * ENNReal.ofReal (1 / u₂ (G₂ x)) ≤
        ENNReal.ofReal |c₁| * ENNReal.ofReal (1 / u₂ (G₂ x)) +
          ENNReal.ofReal |Real.log (u₁ x) - c₁| * ENNReal.ofReal (1 / u₂ (G₂ x))
      rw [← hx, ← add_mul]
      gcongr
      refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
      linarith [abs_sub_abs_le_abs_sub (Real.log (u₁ x)) c₁]
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨?_, ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr
        ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm₁,
          ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm₂⟩))
      (s07_ssc_core hui₁ hpos₁ hvpos (H₂ p) (H₂ q) c₁ c₂)⟩) hle
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      s07_ssv_lin hG₂ hG₂c hvi hvrep hvpos hAB.le]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hlog₁ : ∀ a b : ℝ, IntegrableOn (fun t => Real.log (u₁ (H₂ t))) (Icc a b) := by
    intro a b
    have hfin := s07_ssv_cover hδ hshort a b
    refine ⟨(show Measurable fun t => Real.log (u₁' (H₂ t)) from
      Real.measurable_log.comp (hu₁'m.comp hH₂c.measurable)).aestronglyMeasurable.congr
        (ae_restrict_of_ae (heqH.mono fun t ht => by
          show Real.log (u₁' (H₂ t)) = Real.log (u₁ (H₂ t))
          rw [ht])), ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs]
    exact lt_top_iff_ne_top.mpr hfin
  have hlog : ∀ a b : ℝ, IntegrableOn (fun t => Real.log (u₁ (H₂ t) * u₂ t)) (Icc a b) := fun a b =>
    ((hlog₁ a b).add (hli₂ a b)).congr (ae_restrict_of_ae ((hposH.and hpos₂).mono fun t ht => by
      show Real.log (u₁ (H₂ t)) + Real.log (u₂ t) = Real.log (u₁ (H₂ t) * u₂ t)
      rw [Real.log_mul ht.1.ne' ht.2.ne']))
  exact ⟨hint, hrep, (hposH.and hpos₂).mono fun t ht => mul_pos ht.1 ht.2, hlog⟩

/-- Helper for `ss_circle_comp`: `log (u₁(H₂) u₂)` has vanishing mean oscillation. The `log u₂`
part is the hypothesis; for `log u₁(H₂)`, on `I` with `J = H₂(I)` and `v₂ = (H₂⁻¹)'`,
`⨍_I |log u₁(H₂) - c| = ∫_J |log u₁ - c| v₂ / ∫_J v₂ ≤ ⨍_J (|s₁| e^{|s₁|} + |s₂| e^{|s₂|})`
(pointwise `|a| e^b ≤ |a| e^{|a|} + |b| e^{|b|}`, `s07_ssc_core`; Jensen `s07_ssc_jensen` for
`∫_J v₂`; `s07_ssv_mom` for both terms, with `s07_ssi_osc` for `log v₂`). -/
theorem s07_ssc_osc {H₁ u₁ H₂ u₂ : ℝ → ℝ} (hH₁ : StrictMono H₁) (hH₁c : Continuous H₁)
    (hper₁ : ∀ θ, H₁ (θ + 2 * π) = H₁ θ + 2 * π) (hui₁ : ∀ a b : ℝ, IntegrableOn u₁ (Icc a b))
    (hHu₁ : ∀ θ : ℝ, H₁ θ = H₁ 0 + ∫ t in (0 : ℝ)..θ, u₁ t) (hpos₁ : ∀ᵐ t, 0 < u₁ t)
    (hli₁ : ∀ a b : ℝ, IntegrableOn (fun t => Real.log (u₁ t)) (Icc a b))
    (hv₁ : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a < b → b - a ≤ δ →
      (∫ t in a..b, |Real.log (u₁ t) - (∫ s in a..b, Real.log (u₁ s)) / (b - a)|) / (b - a) ≤ ε)
    (hH₂ : StrictMono H₂) (hH₂c : Continuous H₂)
    (hper₂ : ∀ θ, H₂ (θ + 2 * π) = H₂ θ + 2 * π) (hui₂ : ∀ a b : ℝ, IntegrableOn u₂ (Icc a b))
    (hHu₂ : ∀ θ : ℝ, H₂ θ = H₂ 0 + ∫ t in (0 : ℝ)..θ, u₂ t) (hpos₂ : ∀ᵐ t, 0 < u₂ t)
    (hli₂ : ∀ a b : ℝ, IntegrableOn (fun t => Real.log (u₂ t)) (Icc a b))
    (hv₂ : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a < b → b - a ≤ δ →
      (∫ t in a..b, |Real.log (u₂ t) - (∫ s in a..b, Real.log (u₂ s)) / (b - a)|) / (b - a) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a < b → b - a ≤ δ →
      (∫ t in a..b, |Real.log (u₁ (H₂ t) * u₂ t) -
        (∫ s in a..b, Real.log (u₁ (H₂ s) * u₂ s)) / (b - a)|) / (b - a) ≤ ε := by
  intro ε hε
  -- the inverse lift `G₂` of `H₂` and its density `v = 1/u₂(G₂)`
  obtain ⟨G₂, hG₂, hG₂c, hG₂per, hHG₂, hGH₂⟩ := s07_ssv_inv hH₂ hH₂c hper₂
  obtain ⟨hvi, hvrep, hvpos, hvli⟩ :=
    s07_ssi_rep hH₂ hH₂c hper₂ hui₂ hHu₂ hpos₂ hli₂ hv₂ hG₂ hG₂c hHG₂ hGH₂
  have hvv := s07_ssi_osc hH₂ hH₂c hper₂ hui₂ hHu₂ hpos₂ hli₂ hv₂ hG₂ hG₂c hHG₂ hGH₂
  have hq₂ := s07_ssv_qmp hG₂ hG₂c hvi hvrep hvpos hH₂c hGH₂ hHG₂
  obtain ⟨-, -, -, hlw⟩ := s07_ssc_rep hH₁ hH₁c hper₁ hui₁ hHu₁ hpos₁ hli₁ hv₁
    hH₂ hH₂c hper₂ hui₂ hHu₂ hpos₂ hli₂ hv₂
  obtain ⟨K, hK, hmom⟩ := s07_ssv_mom
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min (1 / 16) (ε / (6 * (1 + K))) := ⟨_, rfl⟩
  have hK6 : (0 : ℝ) < 6 * (1 + K) := by linarith
  have hη0 : 0 < η := by
    rw [hη]
    exact lt_min (by norm_num) (div_pos hε hK6)
  have hη16 : η ≤ 1 / 16 := hη ▸ min_le_left _ _
  have hηε : η ≤ ε / (6 * (1 + K)) := hη ▸ min_le_right _ _
  have hcoef : 0 ≤ η + K * η ^ 2 := add_nonneg hη0.le (mul_nonneg hK.le (sq_nonneg η))
  have hfin : 2 * (2 * (η + K * η ^ 2) + η) ≤ ε := by
    have h1 : K * η ^ 2 ≤ K * η := mul_le_mul_of_nonneg_left (by nlinarith) hK.le
    have h2 : η * (6 * (1 + K)) ≤ ε := by rwa [le_div_iff₀ hK6] at hηε
    nlinarith [mul_pos hK hη0]
  obtain ⟨δa, hδa, hva⟩ := hv₁ η hη0
  obtain ⟨δb, hδb, hvb⟩ := hvv η hη0
  obtain ⟨δc, hδc, hvc⟩ := hv₂ η hη0
  obtain ⟨δd, hδd, hδu⟩ := s07_ssv_unif hH₂ hH₂c hper₂ (min δa δb) (lt_min hδa hδb)
  refine ⟨min δc δd, lt_min hδc hδd, fun a b hab hba => ?_⟩
  have hba' : 0 < b - a := by linarith
  have hbc : b - a ≤ δc := hba.trans (min_le_left _ _)
  have hbd : b - a ≤ δd := hba.trans (min_le_right _ _)
  have hAB : H₂ a < H₂ b := hH₂ hab
  have hBA := hδu a b hab.le hbd
  have hma := min_le_left δa δb
  have hmb := min_le_right δa δb
  have hm₁ := hmom (fun t => Real.log (u₁ t)) hli₁ (H₂ a) (H₂ b) η hη0 hη16
    (fun p q h1 h2 h3 => hva p q h2 (by linarith)) hAB
  have hm₂ := hmom (fun t => Real.log (1 / u₂ (G₂ t))) hvli (H₂ a) (H₂ b) η hη0 hη16
    (fun p q h1 h2 h3 => hvb p q h2 (by linarith)) hAB
  beta_reduce at hm₁ hm₂
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℝ, c = (∫ s in H₂ a..H₂ b, Real.log (u₁ s)) / (H₂ b - H₂ a) :=
    ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c : ℝ,
      c = (∫ s in H₂ a..H₂ b, Real.log (1 / u₂ (G₂ s))) / (H₂ b - H₂ a) := ⟨_, rfl⟩
  rw [← hc₁] at hm₁
  rw [← hc₂] at hm₂
  -- Jensen for `v` on `[H₂ a, H₂ b]`: `e^{c₂} |J| <= ∫_J v = b - a`
  have hJ := s07_ssc_jensen hvi hvrep hvpos hvli hAB
  rw [← hc₂, hGH₂, hGH₂] at hJ
  -- a measurable representative of `u₁`
  have hae₁ := s07_ssv_aemeas hui₁
  obtain ⟨u₁', hu₁'⟩ : ∃ u₁' : ℝ → ℝ, u₁' = hae₁.mk u₁ := ⟨_, rfl⟩
  have hu₁'m : Measurable u₁' := hu₁' ▸ hae₁.measurable_mk
  have heq₁ : u₁ =ᵐ[volume] u₁' := hu₁' ▸ hae₁.ae_eq_mk
  have heqH : ∀ᵐ t, u₁ (H₂ t) = u₁' (H₂ t) := hq₂.ae_eq_comp heq₁
  have hposH : ∀ᵐ t, 0 < u₁ (H₂ t) := hq₂.ae hpos₁
  -- the `log u₁(H₂)` part
  have hf : ∫⁻ t in Icc a b, ENNReal.ofReal |Real.log (u₁ (H₂ t)) - c₁| ≤
      ENNReal.ofReal (2 * (η + K * η ^ 2) * (b - a)) := by
    have hcv : (∫⁻ t in Icc a b, ENNReal.ofReal |Real.log (u₁' (H₂ t)) - c₁|) =
        ∫⁻ x in Icc (H₂ a) (H₂ b), ENNReal.ofReal |Real.log (u₁' x) - c₁| *
          ENNReal.ofReal (1 / u₂ (G₂ x)) :=
      s07_ssv_cvG hG₂ hG₂c hvi hvrep hvpos hH₂ hH₂c hGH₂ hHG₂ hab.le
        (fun x => ENNReal.ofReal |Real.log (u₁' x) - c₁|)
        (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
          ((Real.measurable_log.comp hu₁'m).sub_const c₁)))
    have hcv2 : (∫⁻ x in Icc (H₂ a) (H₂ b), ENNReal.ofReal |Real.log (u₁' x) - c₁| *
          ENNReal.ofReal (1 / u₂ (G₂ x))) =
        ∫⁻ x in Icc (H₂ a) (H₂ b), ENNReal.ofReal |Real.log (u₁ x) - c₁| *
          ENNReal.ofReal (1 / u₂ (G₂ x)) :=
      lintegral_congr_ae ((ae_restrict_of_ae heq₁).mono fun x hx => by
        show ENNReal.ofReal |Real.log (u₁' x) - c₁| * ENNReal.ofReal (1 / u₂ (G₂ x)) =
          ENNReal.ofReal |Real.log (u₁ x) - c₁| * ENNReal.ofReal (1 / u₂ (G₂ x))
        rw [hx])
    rw [lintegral_congr_ae ((ae_restrict_of_ae heqH).mono fun t ht => by
      show ENNReal.ofReal |Real.log (u₁ (H₂ t)) - c₁| = ENNReal.ofReal |Real.log (u₁' (H₂ t)) - c₁|
      rw [ht]), hcv, hcv2]
    have hJ0 : 0 ≤ H₂ b - H₂ a := (sub_pos.mpr hAB).le
    refine (s07_ssc_core hui₁ hpos₁ hvpos (H₂ a) (H₂ b) c₁ c₂).trans ?_
    calc ENNReal.ofReal (Real.exp c₂) * ((∫⁻ x in Icc (H₂ a) (H₂ b),
          ENNReal.ofReal (|Real.log (u₁ x) - c₁| * Real.exp |Real.log (u₁ x) - c₁|)) +
          ∫⁻ x in Icc (H₂ a) (H₂ b), ENNReal.ofReal (|Real.log (1 / u₂ (G₂ x)) - c₂| *
            Real.exp |Real.log (1 / u₂ (G₂ x)) - c₂|))
        ≤ ENNReal.ofReal (Real.exp c₂) * (ENNReal.ofReal ((η + K * η ^ 2) * (H₂ b - H₂ a)) +
            ENNReal.ofReal ((η + K * η ^ 2) * (H₂ b - H₂ a))) :=
          mul_le_mul_right (add_le_add hm₁ hm₂) _
      _ = ENNReal.ofReal (2 * (η + K * η ^ 2) * (Real.exp c₂ * (H₂ b - H₂ a))) := by
          rw [← ENNReal.ofReal_add (mul_nonneg hcoef hJ0) (mul_nonneg hcoef hJ0),
            ← ENNReal.ofReal_mul (Real.exp_pos c₂).le]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (2 * (η + K * η ^ 2) * (b - a)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hJ (by linarith))
  have hfi : IntegrableOn (fun t => Real.log (u₁ (H₂ t))) (Icc a b) :=
    ((hlw a b).sub (hli₂ a b)).congr (ae_restrict_of_ae ((hposH.and hpos₂).mono fun t ht => by
      show Real.log (u₁ (H₂ t) * u₂ t) - Real.log (u₂ t) = Real.log (u₁ (H₂ t))
      rw [Real.log_mul ht.1.ne' ht.2.ne']
      ring))
  have hfR : ∫ t in a..b, |Real.log (u₁ (H₂ t)) - c₁| ≤ 2 * (η + K * η ^ 2) * (b - a) := by
    have hi : IntegrableOn (fun t => |Real.log (u₁ (H₂ t)) - c₁|) (Icc a b) :=
      (hfi.sub continuous_const.integrableOn_Icc).abs
    rw [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc]
    have h := ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun t => abs_nonneg _)
    rw [← h] at hf
    exact (ENNReal.ofReal_le_ofReal_iff (by nlinarith)).mp hf
  -- the `log u₂` part
  obtain ⟨m₂, hm₂d⟩ : ∃ m : ℝ, m = (∫ s in a..b, Real.log (u₂ s)) / (b - a) := ⟨_, rfl⟩
  have hgR : ∫ t in a..b, |Real.log (u₂ t) - m₂| ≤ η * (b - a) := by
    have h := hvc a b hab hbc
    rw [← hm₂d, div_le_iff₀ hba'] at h
    exact h
  -- combine
  have hii : ∀ f : ℝ → ℝ, IntegrableOn f (Icc a b) → IntervalIntegrable f volume a b :=
    fun f h => (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr h
  have hA : IntervalIntegrable (fun t => |Real.log (u₁ (H₂ t)) - c₁|) volume a b :=
    hii _ (hfi.sub continuous_const.integrableOn_Icc).abs
  have hB : IntervalIntegrable (fun t => |Real.log (u₂ t) - m₂|) volume a b :=
    hii _ ((hli₂ a b).sub continuous_const.integrableOn_Icc).abs
  have hsum : ∫ t in a..b, |Real.log (u₁ (H₂ t) * u₂ t) - (c₁ + m₂)| ≤
      ∫ t in a..b, (|Real.log (u₁ (H₂ t)) - c₁| + |Real.log (u₂ t) - m₂|) := by
    refine intervalIntegral.integral_mono_ae_restrict hab.le
      (hii _ ((hlw a b).sub continuous_const.integrableOn_Icc).abs) (hA.add hB)
      (ae_restrict_of_ae ((hposH.and hpos₂).mono fun t ht => ?_))
    show |Real.log (u₁ (H₂ t) * u₂ t) - (c₁ + m₂)| ≤
      |Real.log (u₁ (H₂ t)) - c₁| + |Real.log (u₂ t) - m₂|
    rw [Real.log_mul ht.1.ne' ht.2.ne', show Real.log (u₁ (H₂ t)) + Real.log (u₂ t) - (c₁ + m₂) =
      (Real.log (u₁ (H₂ t)) - c₁) + (Real.log (u₂ t) - m₂) by ring]
    exact abs_add_le _ _
  rw [intervalIntegral.integral_add hA hB] at hsum
  refine (s07_ssv_osc_const hab (hii _ (hlw a b)) (c₁ + m₂)).trans ?_
  calc 2 * ((∫ t in a..b, |Real.log (u₁ (H₂ t) * u₂ t) - (c₁ + m₂)|) / (b - a))
      ≤ 2 * (2 * (η + K * η ^ 2) + η) :=
        mul_le_mul_of_nonneg_left (by rw [div_le_iff₀ hba']; nlinarith) (by norm_num)
    _ ≤ ε := hfin

/-- Group facts (`sec07-transfer.tex:285`): strongly symmetric homeomorphisms are closed under
composition. -/
theorem ss_circle_comp (h₁ h₂ : ℂ → ℂ) (h1 : IsStronglySymmetric h₁)
    (h2 : IsStronglySymmetric h₂) : IsStronglySymmetric (h₁ ∘ h₂) := by
  obtain ⟨H₁, u₁, hH₁, hH₁c, hper₁, hl₁, hui₁, hHu₁, hpos₁, hli₁, hv₁⟩ := h1
  obtain ⟨H₂, u₂, hH₂, hH₂c, hper₂, hl₂, hui₂, hHu₂, hpos₂, hli₂, hv₂⟩ := h2
  obtain ⟨hi, hrep, hp, hlog⟩ := s07_ssc_rep hH₁ hH₁c hper₁ hui₁ hHu₁ hpos₁ hli₁ hv₁
    hH₂ hH₂c hper₂ hui₂ hHu₂ hpos₂ hli₂ hv₂
  refine ⟨fun θ => H₁ (H₂ θ), fun t => u₁ (H₂ t) * u₂ t, hH₁.comp hH₂, hH₁c.comp hH₂c,
    fun θ => by simp only; rw [hper₂, hper₁], fun θ => ?_, hi, hrep, hp, hlog,
    s07_ssc_osc hH₁ hH₁c hper₁ hui₁ hHu₁ hpos₁ hli₁ hv₁ hH₂ hH₂c hper₂ hui₂ hHu₂ hpos₂ hli₂ hv₂⟩
  show h₁ (h₂ (exp (θ * I))) = exp (H₁ (H₂ θ) * I)
  rw [hl₂, hl₁]

/-- Group facts (`sec07-transfer.tex:285`): the inverse of a strongly symmetric homeomorphism is
strongly symmetric. -/
theorem ss_circle_inv (h hinv : ℂ → ℂ) (hh : IsStronglySymmetric h)
    (hinv1 : ∀ ζ ∈ sphere (0 : ℂ) 1, hinv ζ ∈ sphere (0 : ℂ) 1 ∧ h (hinv ζ) = ζ) :
    IsStronglySymmetric hinv := by
  obtain ⟨H, u, hH, hHc, hper, hl, hui, hHu, hpos, hli, hv⟩ := hh
  obtain ⟨G, hG, hGc, hGper, hGl, hHG, hGH⟩ := s07_inv_lift hH hHc hper hl hinv1
  obtain ⟨hi, hrep, hp, hlog⟩ := s07_ssi_rep hH hHc hper hui hHu hpos hli hv hG hGc hHG hGH
  exact ⟨G, fun t => 1 / u (G t), hG, hGc, hGper, hGl, hi, hrep, hp, hlog,
    s07_ssi_osc hH hHc hper hui hHu hpos hli hv hG hGc hHG hGH⟩

/-- A uniformly continuous function has small mean oscillation on short intervals:
if `|L t - L s| ≤ ε` for `s, t ∈ [a, b]`, then `(1/|I|) ∫_I |L - L_I| ≤ ε`. -/
theorem s07_meanOsc_le {L : ℝ → ℝ} (hL : Continuous L) {a b ε : ℝ} (hab : a < b)
    (hosc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |L t - L s| ≤ ε) :
    (∫ t in a..b, |L t - (∫ s in a..b, L s) / (b - a)|) / (b - a) ≤ ε := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hIoc : ∀ x ∈ Set.uIoc a b, x ∈ Icc a b := by
    intro x hx
    rw [uIoc_of_le hab.le] at hx
    exact ⟨hx.1.le, hx.2⟩
  have hpt : ∀ t ∈ Icc a b, |L t - (∫ s in a..b, L s) / (b - a)| ≤ ε := by
    intro t ht
    have hsplit : L t - (∫ s in a..b, L s) / (b - a) = (∫ s in a..b, (L t - L s)) / (b - a) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hL.intervalIntegrable a b),
        intervalIntegral.integral_const, smul_eq_mul]
      field_simp
    rw [hsplit, abs_div, abs_of_pos hba, div_le_iff₀ hba]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := ε)
      (f := fun s => L t - L s) (fun s hs => by
        rw [Real.norm_eq_abs]
        exact hosc s (hIoc s hs) t ht)
    rw [Real.norm_eq_abs, abs_of_pos hba] at h
    linarith
  rw [div_le_iff₀ hba]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := ε)
    (f := fun t => |L t - (∫ s in a..b, L s) / (b - a)|) (fun t ht => by
      rw [Real.norm_eq_abs, abs_abs]
      exact hpt t (hIoc t ht))
  rw [abs_of_pos hba] at h
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans h)

/-- `sec07-transfer.tex:287`: Möbius automorphisms of `∂𝔻` are strongly symmetric. -/
theorem ss_circle_mobius (t : ℝ) (a : ℂ) (ha : a ∈ unitDisc) :
    IsStronglySymmetric (diskMobius t a) := by
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  set H : ℝ → ℝ := fun θ => t + θ + 2 * arg (1 - a * exp (-(θ * I))) with hHdef
  set D : ℝ → ℝ := fun θ => (1 - ‖a‖ ^ 2) / ‖exp (θ * I) - a‖ ^ 2 with hDdef
  have hd : ∀ θ, HasDerivAt H (D θ) θ := fun θ => s07_mob_hasDerivAt ha1 t θ
  have hr0 : 0 < 1 - ‖a‖ := by linarith
  have hr1 : 0 < 1 + ‖a‖ := by linarith [norm_nonneg a]
  obtain ⟨hDb, hmono, hcont, hper⟩ : (∀ θ, (1 - ‖a‖) / (1 + ‖a‖) ≤ D θ ∧
      D θ ≤ (1 + ‖a‖) / (1 - ‖a‖)) ∧ StrictMono H ∧ Continuous H ∧
      ∀ θ : ℝ, H (θ + 2 * π) = H θ + 2 * π := s07_mob_props ha1 t
  have hDpos : ∀ θ, 0 < D θ := fun θ => lt_of_lt_of_le (div_pos hr0 hr1) (hDb θ).1
  have hne : ∀ z ∈ sphere (0 : ℂ) 1, ‖z - a‖ ^ 2 ≠ 0 := by
    intro z hz h
    have hz1 : ‖z‖ = 1 := by simpa using hz
    have : ‖z - a‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    rw [norm_eq_zero, sub_eq_zero] at this
    rw [this] at hz1
    linarith
  have hexpS : ∀ θ : ℝ, exp (θ * I) ∈ sphere (0 : ℂ) 1 := fun θ => by
    simp [Complex.norm_exp_ofReal_mul_I]
  have hDc : Continuous D := by
    simp only [hDdef]
    exact continuous_const.div (by fun_prop) fun θ => hne _ (hexpS θ)
  have hLc : Continuous fun θ => Real.log (D θ) := hDc.log fun θ => (hDpos θ).ne'
  refine ⟨H, D, hmono, hcont, hper, fun θ => s07_mob_lift ha1 t θ,
    fun _ _ => hDc.integrableOn_Icc, fun θ => ?_, ae_of_all _ hDpos,
    fun _ _ => hLc.integrableOn_Icc, fun ε hε => ?_⟩
  · have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := θ)
      (fun x _ => hd x) (hDc.intervalIntegrable 0 θ)
    linarith
  · -- `log D = g ∘ e^{i·}` with `g` uniformly continuous on the compact circle
    set g : ℂ → ℝ := fun z => Real.log ((1 - ‖a‖ ^ 2) / ‖z - a‖ ^ 2) with hgdef
    have hgc : ContinuousOn g (sphere (0 : ℂ) 1) := by
      intro z hz
      have hpos : 0 < (1 - ‖a‖ ^ 2) / ‖z - a‖ ^ 2 := by
        have : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
        have h2 := hne z hz
        positivity
      have hq : ContinuousAt (fun w : ℂ => (1 - ‖a‖ ^ 2) / ‖w - a‖ ^ 2) z :=
        continuousAt_const.div (by fun_prop) (hne z hz)
      exact (hq.log hpos.ne').continuousWithinAt
    obtain ⟨δ, hδ, hδb⟩ := Metric.uniformContinuousOn_iff.mp
      ((isCompact_sphere (0 : ℂ) 1).uniformContinuousOn_of_continuous hgc) ε hε
    refine ⟨δ / 2, by positivity, fun a₁ b₁ hab hlen => ?_⟩
    refine s07_meanOsc_le hLc hab fun s hs u hu => ?_
    have hdist : dist (exp (u * I)) (exp (s * I)) < δ := by
      rw [dist_eq_norm]
      have h1 : exp (u * I) - exp (s * I) = exp (s * I) * (exp (I * ((u - s : ℝ) : ℂ)) - 1) := by
        rw [mul_sub, mul_one, ← Complex.exp_add]
        push_cast
        ring_nf
      rw [h1, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      calc ‖exp (I * ((u - s : ℝ) : ℂ)) - 1‖ ≤ ‖u - s‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
        _ ≤ b₁ - a₁ := by
            rw [Real.norm_eq_abs, abs_le]
            constructor <;> linarith [hs.1, hs.2, hu.1, hu.2]
        _ < δ := by linarith
    have := hδb _ (hexpS u) _ (hexpS s) hdist
    rw [Real.dist_eq] at this
    exact this.le

/-- Local integrability on compact intervals is invariant under `t ↦ -t`. -/
theorem s07_integrableOn_comp_neg {f : ℝ → ℝ} (hf : ∀ a b : ℝ, IntegrableOn f (Icc a b))
    (a b : ℝ) : IntegrableOn (fun t => f (-t)) (Icc a b) := by
  have h := ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding (f := f) (s := Icc (-b) (-a))).2 (hf (-b) (-a))
  simpa [Function.comp_def, neg_preimage, neg_Icc] using h

/-- `sec07-transfer.tex:289`: strong symmetry is invariant under conjugation by `c₀`. -/
theorem ss_circle_conj (h : ℂ → ℂ) (hh : IsStronglySymmetric h) :
    IsStronglySymmetric (fun z => conj (h (conj z))) := by
  obtain ⟨H, u, hm, hc, hp, he, hui, hH, hpos, hli, hv⟩ := hh
  refine ⟨fun θ => -H (-θ), fun t => u (-t), fun x y hxy => neg_lt_neg (hm (neg_lt_neg hxy)),
    by fun_prop, fun θ => ?_, fun θ => ?_, s07_integrableOn_comp_neg hui, fun θ => ?_,
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae hpos,
    s07_integrableOn_comp_neg hli, fun ε hε => ?_⟩
  · show -H (-(θ + 2 * π)) = -H (-θ) + 2 * π
    rw [show -(θ + 2 * π) = -θ - 2 * π by ring, s07_lift_sub_two_pi hp]
    ring
  · simp only
    rw [s07_conj_exp, he, s07_conj_exp]
  · show -H (-θ) = -H (-0) + ∫ t in (0 : ℝ)..θ, u (-t)
    have hneg : (∫ t in (0 : ℝ)..θ, u (-t)) = ∫ t in -θ..-0, u t :=
      intervalIntegral.integral_comp_neg (f := u)
    rw [hneg, neg_zero, intervalIntegral.integral_symm 0 (-θ), hH (-θ)]
    ring
  · obtain ⟨δ, hδ, hδb⟩ := hv ε hε
    refine ⟨δ, hδ, fun a b hab hlen => ?_⟩
    have h1 := hδb (-b) (-a) (by linarith) (by linarith)
    have hin : (∫ s in a..b, Real.log (u (-s))) = ∫ s in -b..-a, Real.log (u s) :=
      intervalIntegral.integral_comp_neg (f := fun s => Real.log (u s))
    have hout : (∫ t in a..b,
        |Real.log (u (-t)) - (∫ s in -b..-a, Real.log (u s)) / (b - a)|) =
        ∫ t in -b..-a, |Real.log (u t) - (∫ s in -b..-a, Real.log (u s)) / (b - a)| :=
      intervalIntegral.integral_comp_neg
        (f := fun t => |Real.log (u t) - (∫ s in -b..-a, Real.log (u s)) / (b - a)|)
    rw [show -a - -b = b - a by ring] at h1
    simp only
    rw [hin, hout]
    exact h1

/-! ## Transfer by bi-Lipschitz extensions -/

/-- `F` is a homeomorphism of `𝔻̄` whose restriction to `𝔻` is an orientation-preserving `C¹`
diffeomorphism, `L`-bi-Lipschitz for `d_𝔻`. -/
def IsBiLipDiskDiffeo (F : ℂ → ℂ) (L : ℝ) : Prop :=
  IsClosedDiskHomeo F ∧ ContDiffOn ℝ 1 F unitDisc ∧
    (∀ z ∈ unitDisc, 0 < (fderiv ℝ F z).det) ∧ IsDiskBiLip F L

/-- Douady–Earle bridge: a circle homeomorphism `h` (`IsCircleHomeo`, lift `H`) induces a
bijective continuous self-map `φ` of `Circle` with an increasing lift, equal to `h` on `∂𝔻`. -/
theorem s07_de_circleMap {h : ℂ → ℂ} (hh : IsCircleHomeo h) :
    ∃ φ : Circle → Circle, Function.Bijective φ ∧ Continuous φ ∧ HasIncreasingLift φ ∧
      ∀ ζ : Circle, ((φ ζ : Circle) : ℂ) = h ζ := by
  obtain ⟨H, hHm, hHc, hHp, hHe⟩ := hh
  have hval : ∀ t : ℝ, h (Circle.exp t) = Circle.exp (H t) := fun t => by
    rw [Circle.coe_exp, Circle.coe_exp]
    exact hHe t
  have hmem : ∀ ζ : Circle, h ζ ∈ Submonoid.unitSphere ℂ := by
    intro ζ
    obtain ⟨t, rfl⟩ := Circle.exp_surjective ζ
    rw [hval t]
    exact (Circle.exp (H t)).2
  set φ : Circle → Circle := fun ζ => ⟨h ζ, hmem ζ⟩ with hφ
  have hcomp : ∀ t : ℝ, φ (Circle.exp t) = Circle.exp (H t) := fun t => Subtype.ext (hval t)
  have hper : ∀ (t : ℝ) (k : ℤ), H (t + k * (2 * π)) = H t + k * (2 * π) := by
    intro t k
    have h1 := CircleLift.lift_per_int (h := H) (d := 1)
      (fun s => by rw [hHp s]; push_cast; ring) t k
    rw [h1]
    push_cast
    ring
  have hq : IsQuotientMap (⇑Circle.exp) :=
    isLocalHomeomorph_circleExp.isOpenMap.isQuotientMap Circle.exp.continuous
      Circle.exp_surjective
  have hφc : Continuous φ := by
    rw [hq.continuous_iff]
    have hfe : φ ∘ ⇑Circle.exp = ⇑Circle.exp ∘ H := funext hcomp
    rw [hfe]
    exact Circle.exp.continuous.comp hHc
  have hinj : Function.Injective φ := by
    intro ζ₁ ζ₂ he
    obtain ⟨t₁, rfl⟩ := Circle.exp_surjective ζ₁
    obtain ⟨t₂, rfl⟩ := Circle.exp_surjective ζ₂
    rw [hcomp, hcomp, Circle.exp_eq_exp] at he
    obtain ⟨m, hm⟩ := he
    have h1 : H t₁ = H (t₂ + m * (2 * π)) := by
      rw [hper]
      exact hm
    rw [hHm.injective h1]
    exact Circle.exp_eq_exp.2 ⟨m, rfl⟩
  have hsurj : Function.Surjective φ := by
    intro ω
    obtain ⟨s, rfl⟩ := Circle.exp_surjective ω
    have h2π : 0 < 2 * π := by positivity
    set m : ℤ := ⌈(H 0 - s) / (2 * π)⌉ with hm
    have hlo : H 0 ≤ s + m * (2 * π) := by
      have h1 := Int.le_ceil ((H 0 - s) / (2 * π))
      rw [← hm, div_le_iff₀ h2π] at h1
      linarith
    have hhi : s + m * (2 * π) ≤ H (2 * π) := by
      have h1 := Int.ceil_lt_add_one ((H 0 - s) / (2 * π))
      rw [← hm] at h1
      have h2 : ((m : ℝ) - 1) * (2 * π) < H 0 - s := by
        rw [← lt_div_iff₀ h2π]
        linarith
      have h3 : H (2 * π) = H 0 + 2 * π := by
        have := hHp 0
        rwa [zero_add] at this
      rw [h3]
      linarith [show ((m : ℝ) - 1) * (2 * π) = m * (2 * π) - 2 * π by ring]
    obtain ⟨t, -, ht⟩ :=
      intermediate_value_Icc h2π.le hHc.continuousOn ⟨hlo, hhi⟩
    refine ⟨Circle.exp t, ?_⟩
    rw [hcomp, ht]
    exact Circle.exp_eq_exp.2 ⟨m, rfl⟩
  refine ⟨φ, ⟨hinj, hsurj⟩, hφc, ⟨H, hHm, hHp, fun t => ?_⟩, fun ζ => rfl⟩
  rw [hcomp t, Circle.coe_exp]

/-- The Douady–Earle orientation inequality `‖∂̄F‖ < ‖∂F‖`, in the form
`‖F′1 + i F′i‖ < ‖F′1 - i F′i‖` of `extension_jacobian_pos`, gives `det dF > 0`. -/
theorem s07_de_det_pos {F : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℝ F z)
    (h : ‖(fderiv ℝ F z) 1 + I * (fderiv ℝ F z) I‖ < ‖(fderiv ℝ F z) 1 - I * (fderiv ℝ F z) I‖) :
    0 < (fderiv ℝ F z).det := by
  -- `dz F z = (F′1 - i F′i)/2` and `dzbar F z = (F′1 + i F′i)/2` (LZ `Basic`), so the
  -- hypothesis is `‖dzbar‖ < ‖dz‖`, and `det = ‖dz‖² - ‖dzbar‖²` (`det_fderiv_eq_jacobian`).
  have hdz : dz F z = ((fderiv ℝ F z) 1 - I * (fderiv ℝ F z) I) / 2 := rfl
  have hdzb : dzbar F z = ((fderiv ℝ F z) 1 + I * (fderiv ℝ F z) I) / 2 := rfl
  have hlt : ‖dzbar F z‖ < ‖dz F z‖ := by
    rw [hdz, hdzb, norm_div, norm_div]
    exact div_lt_div_of_pos_right h (by norm_num)
  have hdet : (fderiv ℝ F z).det = jacobian F z := det_fderiv_eq_jacobian hF
  rw [hdet]
  show 0 < ‖dz F z‖ ^ 2 - ‖dzbar F z‖ ^ 2
  have h0 := norm_nonneg (dzbar F z)
  nlinarith

/-- Theorem 7.5 (`thm:DE`), existence part: for a circle homeomorphism `h` the Douady–Earle
extension `F = extension φ` of the induced `φ` is a homeomorphism of `𝔻̄` extending `h`,
real-analytic on `𝔻` with positive Jacobian. -/
theorem s07_de_extension {h : ℂ → ℂ} (hh : IsCircleHomeo h) :
    ∃ φ : Circle → Circle, Function.Bijective φ ∧ Continuous φ ∧ HasIncreasingLift φ ∧
      IsClosedDiskHomeo (extension φ) ∧ EqOn (extension φ) h (sphere 0 1) ∧
      AnalyticOnNhd ℝ (extension φ) unitDisc ∧
      ∀ z ∈ unitDisc, 0 < (fderiv ℝ (extension φ) z).det := by
  obtain ⟨φ, hφb, hφc, hor, hφv⟩ := s07_de_circleMap hh
  obtain ⟨hbij, hcont, -⟩ := extension_isHomeomorphOn φ hφb hφc
  have han : AnalyticOnNhd ℝ (extension φ) unitDisc :=
    isOpen_ball.analyticOn_iff_analyticOnNhd.mp (extension_analyticOn_disk φ hφb hφc)
  refine ⟨φ, hφb, hφc, hor, ⟨hbij, hcont⟩, fun z hz => ?_, han, fun z hz => ?_⟩
  · have hz' : z ∈ Submonoid.unitSphere ℂ := hz
    exact (extension_eq_boundary φ ⟨z, hz'⟩).trans (hφv _)
  · exact s07_de_det_pos (han z hz).differentiableAt
      (extension_jacobian_pos φ hφb hφc hor z (mem_ball_zero_iff.mp hz))

/-- Helper for `s07_tw_inf`: `sinh² (d_𝔻(p, q)/2) = |p - q|²/(ϖ(p) ϖ(q))`. -/
theorem s07_tw_sinh_sq {p q : ℂ} (hp : p ∈ unitDisc) (hq : q ∈ unitDisc) :
    Real.sinh (diskDist p q / 2) ^ 2 = ‖p - q‖ ^ 2 / (varpi p * varpi q) := by
  have h := s07_mo_cosh_dist hp hq
  rw [s07_mo_cosh_half] at h
  unfold diskCoshDist at h
  unfold varpi
  rw [mul_div_assoc] at h
  linarith

/-- Helper for `s07_tw_inf`: with `s = |p - q|/√(ϖ(p) ϖ(q))`, `2s/√(1 + s²) ≤ d_𝔻(p, q) ≤ 2s`. -/
theorem s07_tw_dist_bounds {p q : ℂ} (hp : p ∈ unitDisc) (hq : q ∈ unitDisc) :
    2 * (‖p - q‖ / √(varpi p * varpi q)) / √(1 + (‖p - q‖ / √(varpi p * varpi q)) ^ 2) ≤
        diskDist p q ∧
      diskDist p q ≤ 2 * (‖p - q‖ / √(varpi p * varpi q)) := by
  have hp1 : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
  have hq1 : ‖q‖ < 1 := mem_ball_zero_iff.mp hq
  have hvp : 0 < varpi p := by unfold varpi; nlinarith [norm_nonneg p]
  have hvq : 0 < varpi q := by unfold varpi; nlinarith [norm_nonneg q]
  have hd0 : 0 ≤ diskDist p q := s02_diskDist_nonneg hp hq
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ‖p - q‖ / √(varpi p * varpi q) := ⟨_, rfl⟩
  rw [← hs]
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hsh0 : 0 ≤ Real.sinh (diskDist p q / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
  have hsh : Real.sinh (diskDist p q / 2) = s := by
    have h2 : s ^ 2 = ‖p - q‖ ^ 2 / (varpi p * varpi q) := by
      rw [hs, div_pow, Real.sq_sqrt (mul_pos hvp hvq).le]
    rw [← s07_tw_sinh_sq hp hq] at h2
    exact (pow_left_inj₀ hsh0 hs0 two_ne_zero).mp h2.symm
  have hch : Real.cosh (diskDist p q / 2) = √(1 + s ^ 2) := by
    rw [← hsh, ← Real.cosh_sq', Real.sqrt_sq (Real.cosh_pos _).le]
  constructor
  · have h1 := s07_mo_sinh_le (by linarith : 0 ≤ diskDist p q / 2)
    rw [hsh, hch] at h1
    have hq0 : 0 < √(1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
    rw [div_le_iff₀ hq0]
    nlinarith [h1]
  · have h1 := Real.self_le_sinh_iff.mpr (by linarith : 0 ≤ diskDist p q / 2)
    rw [hsh] at h1
    linarith

/-- Helper for `s07_tw_jac`: `D v = a v + b v̄` with `a = (D 1 - i D i)/2`, `b = (D 1 + i D i)/2`. -/
theorem s07_tw_jac_decomp (D : ℂ →L[ℝ] ℂ) (v : ℂ) :
    D v = (D 1 - I * D I) / 2 * v + (D 1 + I * D I) / 2 * conj v := by
  have hv : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • I := by
    rw [Complex.real_smul, Complex.real_smul, mul_one]
    exact (Complex.re_add_im v).symm
  have hDv : D v = (v.re : ℂ) * D 1 + (v.im : ℂ) * D I := by
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  rw [hDv]
  conv_rhs => rw [← Complex.re_add_im v]
  rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  linear_combination ((v.im : ℂ) * D I) * Complex.I_sq

/-- Helper for `s07_tw_jac`: `det D = |a|² - |b|²`. -/
theorem s07_tw_jac_det (D : ℂ →L[ℝ] ℂ) :
    D.det = Complex.normSq ((D 1 - I * D I) / 2) - Complex.normSq ((D 1 + I * D I) / 2) := by
  show LinearMap.det (D : ℂ →ₗ[ℝ] ℂ) = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
    Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearMap.coe_coe]
  simp only [Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  norm_num
  ring

/-- The boundary function of a `K`-q.c. self-map of `𝔻` is an orientation-preserving circle
homeomorphism: `H` extends to a homeomorphism of `𝔻̄` (LZ `thm13_3_boundary_correspondence`),
which preserves the cyclic order on `∂𝔻` because `H` is sense preserving; the angular lift is
strictly increasing. -/
theorem s07_circleHomeo_of_qcExt {H h : ℂ → ℂ} {K : ℝ} (hH : IsKQC H unitDisc K)
    (hHs : H '' unitDisc = unitDisc) (hb : HasDiskBoundaryValues H h) : IsCircleHomeo h := by
  -- (a) the homeomorphic extension of `H` to `𝔻̄` (Thm 13.3), read in `ℂ` as `φ`
  set S : Set ℂ := closedBall (0 : ℂ) 1 with hS
  have hBS : unitDisc ⊆ S := ball_subset_closedBall
  have hsS : sphere (0 : ℂ) 1 ⊆ S := sphere_subset_closedBall
  have hclD : closure unitDisc = S := closure_ball (0 : ℂ) one_ne_zero
  have hclE : closure (toExt unitDisc) = toExt S := by
    rw [closure_toExt_of_isBounded' (show Bornology.IsBounded unitDisc from isBounded_ball), hclD]
  obtain ⟨G, hG1, hG2, hG3, hG4⟩ :=
    thm13_3_boundary_correspondence isJordanDomain_unitDisc isJordanDomain_unitDisc ⟨K, hH⟩ hHs
  rw [hclE] at hG2 hG3 hG4
  have hfin : ∀ z ∈ S, ∃ w : ℂ, w ∈ S ∧ G z = w := fun z hz => by
    have : G z ∈ toExt S := hG4 ▸ mem_image_of_mem G (mem_image_of_mem _ hz)
    obtain ⟨w, hw, hw'⟩ := this
    exact ⟨w, hw, hw'.symm⟩
  choose! φ hφS hφ using hfin
  have hφc : ContinuousOn φ S := by
    refine (OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_iff).2 ?_
    exact (hG2.comp OnePoint.continuous_coe.continuousOn fun z hz => mem_image_of_mem _ hz).congr
      fun z hz => (hφ z hz).symm
  have hφi : InjOn φ S := fun a ha b hb hab =>
    OnePoint.coe_injective (hG3 (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)
      (by rw [hφ a ha, hφ b hb, hab]))
  have hφH : ∀ z ∈ unitDisc, φ z = H z := fun z hz =>
    OnePoint.coe_injective ((hφ z (hBS hz)).symm.trans (hG1 z hz))
  have hφh : ∀ ζ ∈ sphere (0 : ℂ) 1, φ ζ = h ζ := fun ζ hζ => by
    have hcl : ζ ∈ closure unitDisc := by
      rw [hclD]
      exact hsS hζ
    have : (𝓝[unitDisc] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
    have h1 : Tendsto φ (𝓝[unitDisc] ζ) (𝓝 (φ ζ)) := ((hφc ζ (hsS hζ)).mono hBS).tendsto
    have h2 : Tendsto φ (𝓝[unitDisc] ζ) (𝓝 (h ζ)) :=
      (hb ζ hζ).congr' (eventually_mem_nhdsWithin.mono fun z hz => (hφH z hz).symm)
    exact tendsto_nhds_unique h1 h2
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hφ0 : φ 0 ∈ unitDisc := by
    rw [hφH 0 h0D, ← hHs]
    exact mem_image_of_mem H h0D
  have hφsph : ∀ ζ ∈ sphere (0 : ℂ) 1, φ ζ ∈ sphere (0 : ℂ) 1 := fun ζ hζ => by
    have h1 : ‖φ ζ‖ ≤ 1 := mem_closedBall_zero_iff.1 (hφS ζ (hsS hζ))
    refine mem_sphere_zero_iff_norm.2 (le_antisymm h1 (not_lt.1 fun hlt => ?_))
    have hmem : φ ζ ∈ H '' unitDisc := by
      rw [hHs]
      exact mem_ball_zero_iff.2 hlt
    obtain ⟨z, hz, hzw⟩ := hmem
    have hzζ := hφi (hBS hz) (hsS hζ) ((hφH z hz).trans hzw)
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    rw [hzζ, mem_sphere_zero_iff_norm.1 hζ] at hz1
    exact lt_irrefl _ hz1
  -- (b) the boundary loop `t ↦ h (e^{2πit})` winds once around `0`: homotope it inside `𝔻̄ \ {0}`
  -- to a small circle about `0`, where the local degree of `H` is `+1` (`qcl_r_hloc_of_isKQC`)
  have hE : ∀ t : ℝ, ‖Complex.exp (2 * π * I * t)‖ = 1 := fun t => by
    rw [show (2 : ℂ) * π * I * t = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  obtain ⟨ρ₁, hρ₁, hloc⟩ := qcl_r_hloc_of_isKQC hH h0D
  obtain ⟨ρ, hρ0, hρ1, hρ2⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < ρ₁ ∧ ρ < 1 :=
    ⟨min (ρ₁ / 2) (1 / 2), lt_min (half_pos hρ₁) one_half_pos,
      (min_le_left _ _).trans_lt (half_lt_self hρ₁), (min_le_right _ _).trans_lt (by norm_num)⟩
  obtain ⟨Hm, hHm⟩ : ∃ Hm : ℝ → ℝ → ℂ, ∀ s t : ℝ,
      Hm s t = φ (((ρ + s * (1 - ρ) : ℝ) : ℂ) * Complex.exp (2 * π * I * t)) :=
    ⟨_, fun _ _ => rfl⟩
  have hc01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have hc11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  have hrad : ∀ s ∈ Icc (0 : ℝ) 1, 0 < ρ + s * (1 - ρ) ∧ ρ + s * (1 - ρ) ≤ 1 := fun s hs => by
    constructor <;> nlinarith [hs.1, hs.2]
  have hnorm : ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 →
      ‖((ρ + s * (1 - ρ) : ℝ) : ℂ) * Complex.exp (2 * π * I * t)‖ = ρ + s * (1 - ρ) :=
    fun s t hs => by rw [norm_mul, hE t, mul_one, Complex.norm_of_nonneg (hrad s hs).1.le]
  have hmemS : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t : ℝ,
      ((ρ + s * (1 - ρ) : ℝ) : ℂ) * Complex.exp (2 * π * I * t) ∈ S :=
    fun s hs t => mem_closedBall_zero_iff.2 ((hnorm s t hs).trans_le (hrad s hs).2)
  have hcontArg : Continuous fun p : ℝ × ℝ =>
      ((ρ + p.1 * (1 - ρ) : ℝ) : ℂ) * Complex.exp (2 * π * I * (p.2 : ℂ)) :=
    (Complex.continuous_ofReal.comp (continuous_const.add (continuous_fst.mul continuous_const))).mul
      (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)))
  have hHmc : ContinuousOn (Function.uncurry Hm) (Icc 0 1 ×ˢ Icc 0 1) := by
    have hmaps : MapsTo (fun p : ℝ × ℝ =>
        ((ρ + p.1 * (1 - ρ) : ℝ) : ℂ) * Complex.exp (2 * π * I * (p.2 : ℂ)))
        (Icc 0 1 ×ˢ Icc 0 1) S := fun p hp => hmemS p.1 (mem_prod.1 hp).1 p.2
    exact (hφc.comp hcontArg.continuousOn hmaps).congr fun p _ => hHm p.1 p.2
  have hslice : ∀ s ∈ Icc (0 : ℝ) 1, ContinuousOn (Hm s) (Icc 0 1) := fun s hs =>
    hHmc.comp (continuousOn_const.prodMk continuousOn_id) fun t ht => mk_mem_prod hs ht
  have hE10 : Complex.exp (2 * π * I * ((1 : ℝ) : ℂ)) = Complex.exp (2 * π * I * ((0 : ℝ) : ℂ)) := by
    rw [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero,
      Complex.exp_two_pi_mul_I]
  have hper : ∀ s ∈ Icc (0 : ℝ) 1, Hm s 1 = Hm s 0 := fun s _ => by
    rw [hHm, hHm, hE10]
  have hw : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, Hm s t ≠ φ 0 := fun s hs t _ heq => by
    rw [hHm] at heq
    have h1 := hφi (hmemS s hs t) (hBS h0D) heq
    have h2 := hnorm s t hs
    rw [h1, norm_zero] at h2
    linarith [(hrad s hs).1]
  obtain ⟨L₀, hL₀c, hL₀e⟩ := exists_continuousOn_log_lift (hslice 0 hc01) (hw 0 hc01)
  have hL₀ : L₀ 1 - L₀ 0 = 2 * π * I := hloc ρ hρ0 hρ1 L₀ hL₀c fun t ht => by
    have hz : (ρ : ℂ) * Complex.exp (2 * π * I * t) ∈ unitDisc := by
      show _ ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff, norm_mul, hE t, mul_one, Complex.norm_of_nonneg hρ0.le]
      exact hρ2
    rw [hL₀e t ht, hHm, zero_mul, add_zero, zero_add, hφH _ hz, hφH 0 h0D]
  obtain ⟨L₁, hL₁c, hL₁e⟩ := exists_continuousOn_log_lift (hslice 1 hc11) (hw 1 hc11)
  have hL₁ : L₁ 1 - L₁ 0 = 2 * π * I := by
    rw [← hL₀]
    exact (lift_change_eq_of_homotopy hHmc hper hw hL₀c hL₁c hL₀e hL₁e).symm
  have hsph1 : ∀ t : ℝ, Hm 1 t ∈ sphere (0 : ℂ) 1 := fun t => by
    rw [hHm]
    exact hφsph _ (mem_sphere_zero_iff_norm.2 ((hnorm 1 t hc11).trans (by ring)))
  obtain ⟨M, hMc, hMe⟩ := exists_continuousOn_log_lift (w := 0) (hslice 1 hc11) fun t _ h0 => by
    have h1 := mem_sphere_zero_iff_norm.1 (hsph1 t)
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hM : M 1 - M 0 = 2 * π * I := by
    rw [← hL₁]
    refine (lift_change_eq_of_norm_sub_lt (γ := fun t => Hm 1 t - φ 0) (β := Hm 1)
      ((hslice 1 hc11).sub continuousOn_const) (hslice 1 hc11)
      (by show Hm 1 1 - φ 0 = Hm 1 0 - φ 0; rw [hper 1 hc11]) (hper 1 hc11) (fun t _ => ?_)
      hL₁c hMc hL₁e (fun t ht => by rw [hMe t ht, sub_zero])).symm
    show ‖Hm 1 t - φ 0 - Hm 1 t‖ < ‖Hm 1 t‖
    rw [sub_sub_cancel_left, norm_neg, mem_sphere_zero_iff_norm.1 (hsph1 t)]
    exact mem_ball_zero_iff.1 hφ0
  -- (c) the real lift `Hl θ = Im M(fract (θ/2π)) - 2π fract (θ/2π) + θ`
  have hMre : ∀ t ∈ Icc (0 : ℝ) 1, (M t).re = 0 := fun t ht => by
    have h1 := congrArg norm (hMe t ht)
    rw [sub_zero, Complex.norm_exp, mem_sphere_zero_iff_norm.1 (hsph1 t)] at h1
    exact (Real.exp_eq_one_iff _).1 h1
  have hMeq : ∀ t ∈ Icc (0 : ℝ) 1, M t = ((M t).im : ℂ) * I := fun t ht => by
    apply Complex.ext <;> simp [hMre t ht]
  have hA1 : (M 1).im - (M 0).im = 2 * π := by
    have := congrArg Complex.im hM
    simpa using this
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  have hfc : ContinuousOn (fun u : ℝ => (M u).im - 2 * π * u) (Icc 0 1) :=
    (Complex.continuous_im.comp_continuousOn hMc).sub (continuousOn_const.mul continuousOn_id)
  have hf01 : (fun u : ℝ => (M u).im - 2 * π * u) 0 = (fun u : ℝ => (M u).im - 2 * π * u) 1 := by
    show (M 0).im - 2 * π * 0 = (M 1).im - 2 * π * 1
    linarith [hA1]
  obtain ⟨Hl, hHl⟩ : ∃ Hl : ℝ → ℝ, ∀ θ : ℝ,
      Hl θ = (M (Int.fract (θ / (2 * π)))).im - 2 * π * Int.fract (θ / (2 * π)) + θ :=
    ⟨_, fun _ => rfl⟩
  have hc : Continuous Hl := by
    have hfc' := (hfc.comp_fract'' hf01).comp (continuous_id.div_const (2 * π))
    refine (hfc'.add continuous_id).congr fun θ => ?_
    rw [hHl]
    rfl
  have hfr : ∀ (θ : ℝ) (n : ℤ), Int.fract ((θ + 2 * π * n) / (2 * π)) = Int.fract (θ / (2 * π)) :=
    fun θ n => by rw [add_div, mul_div_cancel_left₀ (n : ℝ) h2π, Int.fract_add_intCast]
  have hshiftZ : ∀ (θ : ℝ) (n : ℤ), Hl (θ + 2 * π * n) = Hl θ + 2 * π * n := fun θ n => by
    rw [hHl, hHl, hfr]
    ring
  have hexp : ∀ θ : ℝ, h (Complex.exp (θ * I)) = Complex.exp (Hl θ * I) := fun θ => by
    have hu : Int.fract (θ / (2 * π)) ∈ Icc (0 : ℝ) 1 :=
      ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    have hθ : θ = 2 * π * Int.fract (θ / (2 * π)) + 2 * π * ⌊θ / (2 * π)⌋ := by
      have h1 := Int.fract_add_floor (θ / (2 * π))
      have h2 := div_mul_cancel₀ θ h2π
      linear_combination (-2 * π) * h1 - h2
    have hθc : (θ : ℂ) = 2 * π * ((Int.fract (θ / (2 * π)) : ℝ) : ℂ) +
        2 * π * ((⌊θ / (2 * π)⌋ : ℤ) : ℂ) := by
      exact_mod_cast hθ
    have hE1 : Complex.exp (θ * I) = Complex.exp (2 * π * I * (Int.fract (θ / (2 * π)) : ℝ)) :=
      Complex.exp_eq_exp_iff_exists_int.2 ⟨⌊θ / (2 * π)⌋, by linear_combination I * hθc⟩
    have hsp : Complex.exp (2 * π * I * (Int.fract (θ / (2 * π)) : ℝ)) ∈ sphere (0 : ℂ) 1 :=
      mem_sphere_zero_iff_norm.2 (hE _)
    have hMe' : Complex.exp (M (Int.fract (θ / (2 * π)))) =
        φ (Complex.exp (2 * π * I * (Int.fract (θ / (2 * π)) : ℝ))) := by
      rw [hMe _ hu, sub_zero, hHm, show ρ + 1 * (1 - ρ) = 1 by ring, Complex.ofReal_one, one_mul]
    rw [hE1, ← hφh _ hsp, ← hMe', hMeq _ hu, hHl]
    refine Complex.exp_eq_exp_iff_exists_int.2 ⟨-⌊θ / (2 * π)⌋, ?_⟩
    push_cast
    linear_combination (-I) * hθc
  -- (d) `Hl` is injective (since `h` is injective on `∂𝔻`), hence strictly monotone
  have hinj : Function.Injective Hl := fun a b hab => by
    have h1 : h (Complex.exp (a * I)) = h (Complex.exp (b * I)) := by rw [hexp, hexp, hab]
    have hsa : Complex.exp (a * I) ∈ sphere (0 : ℂ) 1 :=
      mem_sphere_zero_iff_norm.2 (Complex.norm_exp_ofReal_mul_I a)
    have hsb : Complex.exp (b * I) ∈ sphere (0 : ℂ) 1 :=
      mem_sphere_zero_iff_norm.2 (Complex.norm_exp_ofReal_mul_I b)
    have h2 : Complex.exp (a * I) = Complex.exp (b * I) :=
      hφi (hsS hsa) (hsS hsb) (by rw [hφh _ hsa, hφh _ hsb, h1])
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h2
    have hn1 := congrArg Complex.im hn
    simp at hn1
    have hn' : a = b + 2 * π * n := by linarith
    have h3 := hshiftZ b n
    rw [← hn', hab] at h3
    have h4 : (n : ℝ) = 0 := by
      have h5 : 2 * π * (n : ℝ) = 0 := by linarith
      rcases mul_eq_zero.1 h5 with h6 | h6
      · exact absurd h6 h2π
      · exact h6
    rw [hn', h4, mul_zero, add_zero]
  have hmono : StrictMono Hl := by
    rcases hc.strictMono_of_inj hinj with h1 | h1
    · exact h1
    · exfalso
      have h2 := h1 (show (0 : ℝ) < 0 + 2 * π * ((1 : ℤ) : ℝ) by push_cast; positivity)
      rw [hshiftZ] at h2
      push_cast at h2
      linarith [Real.pi_pos]
  refine ⟨Hl, hmono, hc, fun θ => ?_, hexp⟩
  simpa using hshiftZ θ 1

/-- Helper for `s07_de_mob_dist`: `1 - |g_a(x)|² = (1 - |a|²)(1 - |x|²)/|1 - ā x|²`. -/
theorem s07_de_mob_varpi {a x : ℂ} (ha : ‖a‖ < 1) (hx : ‖x‖ ≤ 1) :
    1 - ‖diskAut a x‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖x‖ ^ 2) / ‖1 - star a * x‖ ^ 2 := by
  have hP : ‖1 - star a * x‖ ≠ 0 := norm_ne_zero_iff.mpr (diskAut_denom_ne_zero a x ha hx)
  have key : ‖1 - star a * x‖ ^ 2 - ‖x - a‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖x‖ ^ 2) := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    ring
  show 1 - ‖(x - a) / (1 - star a * x)‖ ^ 2 = _
  rw [norm_div, div_pow, eq_div_iff (pow_ne_zero 2 hP), sub_mul,
    div_mul_cancel₀ _ (pow_ne_zero 2 hP), one_mul]
  linarith

/-- DE 2b: Möbius invariance of `d_𝔻`: `d_𝔻(g_a x, g_a y) = d_𝔻(x, y)` for `g_a(z) = (z - a)/(1 - ā z)`. -/
theorem s07_de_mob_dist {a x y : ℂ} (ha : ‖a‖ < 1) (hx : x ∈ unitDisc) (hy : y ∈ unitDisc) :
    diskDist (diskAut a x) (diskAut a y) = diskDist x y := by
  have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
  have hy1 : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
  have hP : ‖1 - star a * x‖ ≠ 0 := norm_ne_zero_iff.mpr (diskAut_denom_ne_zero a x ha hx1.le)
  have hQ : ‖1 - star a * y‖ ≠ 0 := norm_ne_zero_iff.mpr (diskAut_denom_ne_zero a y ha hy1.le)
  have hc : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hvx : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  have hvy : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
  have hnum : ‖diskAut a x - diskAut a y‖ =
      (1 - ‖a‖ ^ 2) * ‖x - y‖ / (‖1 - star a * x‖ * ‖1 - star a * y‖) := by
    rw [diskAut_sub_diskAut a x y ha hx1.le hy1.le, norm_div, norm_mul, norm_mul]
    congr 2
    have h : (1 : ℂ) - star a * a = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']
      push_cast
      ring
    rw [h, Complex.norm_real, Real.norm_of_nonneg hc.le]
  show Real.arcosh (1 + 2 * ‖diskAut a x - diskAut a y‖ ^ 2 /
      ((1 - ‖diskAut a x‖ ^ 2) * (1 - ‖diskAut a y‖ ^ 2))) =
    Real.arcosh (1 + 2 * ‖x - y‖ ^ 2 / ((1 - ‖x‖ ^ 2) * (1 - ‖y‖ ^ 2)))
  rw [hnum, s07_de_mob_varpi ha hx1.le, s07_de_mob_varpi ha hy1.le]
  congr 2
  generalize ‖1 - star a * x‖ = P at hP ⊢
  generalize ‖1 - star a * y‖ = Q at hQ ⊢
  field_simp

/-- Helper for `s07_de_lip_of_inf`: `d_𝔻(0, w) = log(1 + |w|) - log(1 - |w|)`. -/
theorem s07_de_dist0 {w : ℂ} (hw : ‖w‖ < 1) :
    diskDist 0 w = Real.log (1 + ‖w‖) - Real.log (1 - ‖w‖) := by
  have h0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hp : 0 < 1 + ‖w‖ := by linarith
  have hm : 0 < 1 - ‖w‖ := by linarith
  have hx : 0 ≤ Real.log (1 + ‖w‖) - Real.log (1 - ‖w‖) := by
    rw [sub_nonneg]
    exact Real.log_le_log hm (by linarith)
  have h2 : (1 : ℝ) - ‖w‖ ^ 2 ≠ 0 := by nlinarith
  have hc : Real.cosh (Real.log (1 + ‖w‖) - Real.log (1 - ‖w‖)) = diskCoshDist 0 w := by
    rw [Real.cosh_eq, Real.exp_sub, neg_sub, Real.exp_sub, Real.exp_log hp, Real.exp_log hm]
    show _ = 1 + 2 * ‖0 - w‖ ^ 2 / ((1 - ‖(0 : ℂ)‖ ^ 2) * (1 - ‖w‖ ^ 2))
    rw [zero_sub, norm_neg, norm_zero]
    field_simp
    ring
  show Real.arcosh (diskCoshDist 0 w) = _
  rw [← hc]
  exact Real.arcosh_cosh hx

/-- DE 2b (infinitesimal ⇒ global): if `ϖ(z)|DF(z)v| ≤ L ϖ(F z)|v|` on `𝔻` for a differentiable
self-map `F` of `𝔻`, then `F` is `L`-Lipschitz for `d_𝔻`. -/
theorem s07_de_lip_of_inf {F : ℂ → ℂ} {L : ℝ} (hF : MapsTo F unitDisc unitDisc)
    (hd : ∀ z ∈ unitDisc, DifferentiableAt ℝ F z)
    (hL : ∀ z ∈ unitDisc, ∀ v : ℂ, varpi z * ‖fderiv ℝ F z v‖ ≤ L * varpi (F z) * ‖v‖) :
    ∀ x ∈ unitDisc, ∀ y ∈ unitDisc, diskDist (F x) (F y) ≤ L * diskDist x y := by
  intro x hx y hy
  have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
  have hy1 : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
  have hnx : ‖-x‖ < 1 := by rwa [norm_neg]
  have hvpos : ∀ p ∈ unitDisc, 0 < varpi p := by
    intro p hp
    have hp1 : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
    show 0 < 1 - ‖p‖ ^ 2
    nlinarith [norm_nonneg p]
  obtain ⟨w, hwd⟩ : ∃ w : ℂ, w = diskAut x y := ⟨_, rfl⟩
  have hw1 : ‖w‖ < 1 := hwd ▸ diskAut_maps_disk_to_disk x y hx1 hy1
  have hAw : diskAut (-x) w = y := by
    have h := diskAut_neg_left_inv hnx (u := y) hy1.le
    rw [neg_neg] at h
    rw [hwd]
    exact h
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ‖w‖ := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hcdef ▸ norm_nonneg w
  have hc1 : c < 1 := hcdef ▸ hw1
  have hdxy : diskDist x y = Real.log (1 + c) - Real.log (1 - c) := by
    have h := s07_de_mob_dist hx1 hx hy
    rw [diskAut_self x hx1, ← hwd, s07_de_dist0 hw1, ← hcdef] at h
    exact h.symm
  -- the geodesic `γ s = g_{-x}(s w)` from `x` to `y` and its velocity
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ → ℂ, γ = fun s : ℝ => diskAut (-x) ((s : ℂ) * w) := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ → ℂ,
      V = fun s : ℝ => (1 - star (-x) * -x) / (1 - star (-x) * ((s : ℂ) * w)) ^ 2 * w := ⟨_, rfl⟩
  have hun : ∀ s ∈ Icc (0 : ℝ) 1, ‖(s : ℂ) * w‖ = s * c := by
    intro s hs
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1, hcdef]
  have hsc : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ s * c ∧ s * c < 1 := fun s hs =>
    ⟨mul_nonneg hs.1 hc0, (mul_le_of_le_one_left hc0 hs.2).trans_lt hc1⟩
  have hult : ∀ s ∈ Icc (0 : ℝ) 1, ‖(s : ℂ) * w‖ < 1 := by
    intro s hs
    rw [hun s hs]
    exact (hsc s hs).2
  have hγD : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ unitDisc := by
    intro s hs
    rw [hγdef]
    exact mem_ball_zero_iff.mpr (diskAut_maps_disk_to_disk _ _ hnx (hult s hs))
  have hFγD : ∀ s ∈ Icc (0 : ℝ) 1, F (γ s) ∈ unitDisc := fun s hs => hF (hγD s hs)
  have hγd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt γ (V s) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * w) w s := by
      simpa using ((hasDerivAt_id s).ofReal_comp).mul_const w
    rw [hγdef, hVdef]
    exact (hasDerivAt_diskAut hnx (hult s hs).le).comp s h1
  have hGd : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s => F (γ s)) (fderiv ℝ F (γ s) (V s)) s := fun s hs =>
    (hd _ (hγD s hs)).hasFDerivAt.comp_hasDerivAt s (hγd s hs)
  -- the infinitesimal bound along `γ`: `2 |(F ∘ γ)'(s)| / ϖ(F γ s) ≤ L · 2c/(1 - s²c²)`
  have hstar : ‖(1 : ℂ) - star (-x) * -x‖ = 1 - ‖x‖ ^ 2 := by
    have h : (1 : ℂ) - star (-x) * -x = ((1 - ‖x‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul', norm_neg]
      push_cast
      ring
    rw [h, Complex.norm_real, Real.norm_of_nonneg (by nlinarith [norm_nonneg x])]
  have hkey : ∀ s ∈ Icc (0 : ℝ) 1, 2 * (‖fderiv ℝ F (γ s) (V s)‖ / varpi (F (γ s))) ≤
      L * (c / (1 + s * c) - -c / (1 - s * c)) := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hsc s hs
    have hP : ‖1 - star (-x) * ((s : ℂ) * w)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (diskAut_denom_ne_zero _ _ hnx (hult s hs).le)
    have hvF : 0 < varpi (F (γ s)) := hvpos _ (hFγD s hs)
    have hvarpi : varpi (γ s) =
        (1 - ‖x‖ ^ 2) * (1 - (s * c) ^ 2) / ‖1 - star (-x) * ((s : ℂ) * w)‖ ^ 2 := by
      rw [hγdef]
      show 1 - ‖diskAut (-x) ((s : ℂ) * w)‖ ^ 2 = _
      rw [s07_de_mob_varpi hnx (hult s hs).le, norm_neg, hun s hs]
    have hDn : ‖V s‖ = (1 - ‖x‖ ^ 2) / ‖1 - star (-x) * ((s : ℂ) * w)‖ ^ 2 * c := by
      rw [hVdef]
      show ‖(1 - star (-x) * -x) / (1 - star (-x) * ((s : ℂ) * w)) ^ 2 * w‖ = _
      rw [norm_mul, norm_div, norm_pow, hstar, hcdef]
    have hq : 0 < (1 - ‖x‖ ^ 2) / ‖1 - star (-x) * ((s : ℂ) * w)‖ ^ 2 := by
      have : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
      positivity
    have hm : 0 < 1 - (s * c) ^ 2 := by nlinarith
    have hL' := hL (γ s) (hγD s hs) (V s)
    rw [hvarpi, hDn] at hL'
    have h2 : (1 - (s * c) ^ 2) * ‖fderiv ℝ F (γ s) (V s)‖ ≤ L * varpi (F (γ s)) * c := by
      have h3 : (1 - ‖x‖ ^ 2) / ‖1 - star (-x) * ((s : ℂ) * w)‖ ^ 2 *
            ((1 - (s * c) ^ 2) * ‖fderiv ℝ F (γ s) (V s)‖) ≤
          (1 - ‖x‖ ^ 2) / ‖1 - star (-x) * ((s : ℂ) * w)‖ ^ 2 * (L * varpi (F (γ s)) * c) := by
        calc _ = (1 - ‖x‖ ^ 2) * (1 - (s * c) ^ 2) / ‖1 - star (-x) * ((s : ℂ) * w)‖ ^ 2 *
              ‖fderiv ℝ F (γ s) (V s)‖ := by ring
          _ ≤ _ := hL'
          _ = _ := by ring
      exact le_of_mul_le_mul_left h3 hq
    have hrhs : L * (c / (1 + s * c) - -c / (1 - s * c)) = 2 * (L * c / (1 - (s * c) ^ 2)) := by
      have h4 : 1 + s * c ≠ 0 := by linarith
      have h5 : 1 - s * c ≠ 0 := by linarith
      rw [div_sub_div _ _ h4 h5, show (1 : ℝ) - (s * c) ^ 2 = (1 + s * c) * (1 - s * c) by ring]
      field_simp
      ring
    rw [hrhs]
    refine mul_le_mul_of_nonneg_left ?_ zero_le_two
    rw [div_le_div_iff₀ hvF hm]
    nlinarith [h2]
  -- Dini comparison of `f s = d(F x, F(γ s))` with `B s = L d(0, s w)`
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ → ℝ, f = fun s => diskDist (F x) (F (γ s)) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ → ℝ,
      B = fun s => L * (Real.log (1 + s * c) - Real.log (1 - s * c)) := ⟨_, rfl⟩
  have hBd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt B (L * (c / (1 + s * c) - -c / (1 - s * c))) s := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hsc s hs
    have hp : 1 + s * c ≠ 0 := by linarith
    have hm : 1 - s * c ≠ 0 := by linarith
    rw [hBdef]
    exact ((((hasDerivAt_mul_const c).const_add 1).log hp).sub
      (((hasDerivAt_mul_const c).const_sub 1).log hm)).const_mul L
  have hBc : ContinuousOn B (Icc 0 1) := fun s hs => (hBd s hs).continuousAt.continuousWithinAt
  have hFx : F x ∈ unitDisc := hF hx
  have hfc : ContinuousOn f (Icc 0 1) := by
    have hk : ContinuousOn (fun s => diskCoshDist (F x) (F (γ s))) (Icc 0 1) := by
      intro s hs
      have hG : ContinuousAt (fun s => F (γ s)) s := (hGd s hs).continuousAt
      have hne : (1 - ‖F x‖ ^ 2) * (1 - ‖F (γ s)‖ ^ 2) ≠ 0 :=
        (mul_pos (hvpos _ hFx) (hvpos _ (hFγD s hs))).ne'
      show ContinuousWithinAt
        (fun s => 1 + 2 * ‖F x - F (γ s)‖ ^ 2 / ((1 - ‖F x‖ ^ 2) * (1 - ‖F (γ s)‖ ^ 2))) _ s
      exact (continuousAt_const.add ((continuousAt_const.mul ((continuousAt_const.sub hG).norm.pow 2)).div
        (continuousAt_const.mul (continuousAt_const.sub (hG.norm.pow 2))) hne)).continuousWithinAt
    rw [hfdef]
    exact Real.continuousOn_arcosh.comp hk (fun s hs => s07_mo_one_le_coshDist hFx (hFγD s hs))
  have hγ0 : γ 0 = x := by
    rw [hγdef]
    show diskAut (-x) (((0 : ℝ) : ℂ) * w) = x
    rw [Complex.ofReal_zero, zero_mul, diskAut_zero, neg_neg]
  have h0 : f 0 ≤ B 0 := by
    rw [hfdef, hBdef]
    show diskDist (F x) (F (γ 0)) ≤ L * (Real.log (1 + 0 * c) - Real.log (1 - 0 * c))
    rw [hγ0, s07_mo_dist_self]
    simp
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ∀ r, L * (c / (1 + t * c) - -c / (1 - t * c)) < r →
      ∃ᶠ z in 𝓝[>] t, slope f t z < r := by
    intro t ht r hr
    have htI : t ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht
    have hG := hGd t htI
    have hvF : 0 < varpi (F (γ t)) := hvpos _ (hFγD t htI)
    have hsl : Tendsto (fun z => ‖slope (fun s => F (γ s)) t z‖) (𝓝[>] t)
        (𝓝 ‖fderiv ℝ F (γ t) (V t)‖) :=
      ((hasDerivAt_iff_tendsto_slope.mp hG).mono_left
        (nhdsWithin_mono _ (fun z hz => ne_of_gt hz))).norm
    have hvc : Tendsto (fun z => √(varpi (F (γ t)) * varpi (F (γ z)))) (𝓝[>] t)
        (𝓝 (√(varpi (F (γ t)) * varpi (F (γ t))))) := by
      have h : ContinuousAt (fun z => √(varpi (F (γ t)) * varpi (F (γ z)))) t := by
        show ContinuousAt (fun z => √((1 - ‖F (γ t)‖ ^ 2) * (1 - ‖F (γ z)‖ ^ 2))) t
        exact (continuousAt_const.mul (continuousAt_const.sub (hG.continuousAt.norm.pow 2))).sqrt
      exact h.tendsto.mono_left nhdsWithin_le_nhds
    rw [Real.sqrt_mul_self hvF.le] at hvc
    have hQ := (hsl.div hvc hvF.ne').const_mul 2
    have hlt : 2 * (‖fderiv ℝ F (γ t) (V t)‖ / varpi (F (γ t))) < r := (hkey t htI).trans_lt hr
    refine ((hQ.eventually (gt_mem_nhds hlt)).and (Ioo_mem_nhdsGT ht.2)).mono ?_ |>.frequently
    intro z hz
    obtain ⟨hzQ, hzt, hz1⟩ := hz
    have hzI : z ∈ Icc (0 : ℝ) 1 := ⟨ht.1.trans hzt.le, hz1.le⟩
    have hzt' : 0 < z - t := sub_pos.mpr hzt
    have htri := s02_diskDist_triangle hFx (hFγD t htI) (hFγD z hzI)
    have hub := (s07_tw_dist_bounds (hFγD t htI) (hFγD z hzI)).2
    have hsq : 0 < √(varpi (F (γ t)) * varpi (F (γ z))) :=
      Real.sqrt_pos.mpr (mul_pos hvF (hvpos _ (hFγD z hzI)))
    have hsl_eq : ‖slope (fun s => F (γ s)) t z‖ = ‖F (γ z) - F (γ t)‖ / (z - t) := by
      rw [slope_def_module, norm_smul, norm_inv, Real.norm_of_nonneg hzt'.le, inv_mul_eq_div]
    rw [hfdef, slope_def_field]
    show (diskDist (F x) (F (γ z)) - diskDist (F x) (F (γ t))) / (z - t) < r
    refine lt_of_le_of_lt (?_ : _ ≤ 2 * (‖slope (fun s => F (γ s)) t z‖ /
      √(varpi (F (γ t)) * varpi (F (γ z))))) hzQ
    rw [hsl_eq, div_le_iff₀ hzt']
    have he : 2 * (‖F (γ z) - F (γ t)‖ / (z - t) / √(varpi (F (γ t)) * varpi (F (γ z)))) *
        (z - t) = 2 * (‖F (γ t) - F (γ z)‖ / √(varpi (F (γ t)) * varpi (F (γ z)))) := by
      rw [norm_sub_rev]
      field_simp
    rw [he]
    linarith
  have hmain := image_le_of_liminf_slope_right_le_deriv_boundary hfc h0 hBc
    (fun s hs => (hBd s (Ico_subset_Icc_self hs)).hasDerivWithinAt) hbound
    (right_mem_Icc.mpr zero_le_one)
  rw [hfdef, hBdef] at hmain
  have hγ1 : γ 1 = y := by
    rw [hγdef]
    show diskAut (-x) (((1 : ℝ) : ℂ) * w) = y
    rw [Complex.ofReal_one, one_mul]
    exact hAw
  have hmain' : diskDist (F x) (F (γ 1)) ≤ L * (Real.log (1 + 1 * c) - Real.log (1 - 1 * c)) :=
    hmain
  rw [hγ1, one_mul] at hmain'
  rw [hdxy]
  exact hmain'

/-- DE 2b: a self-homeomorphism `F` of `𝔻` (inverse `G`), differentiable with positive Jacobian and
with `ϖ(F z)|v|/L ≤ ϖ(z)|DF(z)v| ≤ L ϖ(F z)|v|`, is `L`-bi-Lipschitz for `d_𝔻` (`s07_de_lip_of_inf`
for `F` and for `G`, differentiable by the inverse function theorem). -/
theorem s07_de_bilip_of_inf {F G : ℂ → ℂ} {L : ℝ} (hF : MapsTo F unitDisc unitDisc)
    (hG : MapsTo G unitDisc unitDisc) (hFG : ∀ w ∈ unitDisc, F (G w) = w)
    (hGF : ∀ z ∈ unitDisc, G (F z) = z) (hGc : ContinuousOn G unitDisc)
    (hd : ∀ z ∈ unitDisc, DifferentiableAt ℝ F z) (hdet : ∀ z ∈ unitDisc, 0 < (fderiv ℝ F z).det)
    (hu : ∀ z ∈ unitDisc, ∀ v : ℂ, varpi z * ‖fderiv ℝ F z v‖ ≤ L * varpi (F z) * ‖v‖)
    (hl : ∀ z ∈ unitDisc, ∀ v : ℂ, varpi (F z) * ‖v‖ ≤ L * varpi z * ‖fderiv ℝ F z v‖) :
    IsDiskBiLip F L := by
  have hDo : IsOpen unitDisc := isOpen_ball
  have hFL := s07_de_lip_of_inf hF hd hu
  -- `G` is differentiable on `𝔻` with `DF(G w) ∘ DG(w) = id` (inverse function theorem)
  have hGd : ∀ w ∈ unitDisc,
      DifferentiableAt ℝ G w ∧ ∀ v, fderiv ℝ F (G w) (fderiv ℝ G w v) = v := by
    intro w hw
    have hz : G w ∈ unitDisc := hG hw
    have hdn : (fderiv ℝ F (G w)).det ≠ 0 := (hdet _ hz).ne'
    obtain ⟨e, he⟩ : ∃ e : ℂ ≃L[ℝ] ℂ, (e : ℂ →L[ℝ] ℂ) = fderiv ℝ F (G w) :=
      ⟨(fderiv ℝ F (G w)).toContinuousLinearEquivOfDetNeZero hdn,
        ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _⟩
    have hFd : HasFDerivAt F (e : ℂ →L[ℝ] ℂ) (G w) := by
      rw [he]
      exact (hd _ hz).hasFDerivAt
    have hev : ∀ᶠ y in 𝓝 w, F (G y) = y := by
      filter_upwards [hDo.mem_nhds hw] with y hy
      exact hFG y hy
    have hD := HasFDerivAt.of_local_left_inverse ((hGc w hw).continuousAt (hDo.mem_nhds hw)) hFd hev
    refine ⟨hD.differentiableAt, fun v => ?_⟩
    rw [hD.fderiv, ← he]
    exact e.apply_symm_apply v
  have hGu : ∀ w ∈ unitDisc, ∀ v : ℂ, varpi w * ‖fderiv ℝ G w v‖ ≤ L * varpi (G w) * ‖v‖ := by
    intro w hw v
    have h := hl (G w) (hG hw) (fderiv ℝ G w v)
    rw [hFG w hw, (hGd w hw).2 v] at h
    exact h
  have hGL := s07_de_lip_of_inf hG (fun w hw => (hGd w hw).1) hGu
  intro x hx y hy
  refine ⟨hFL x hx y hy, ?_⟩
  have h := hGL (F x) (hF hx) (F y) (hF hy)
  rw [hGF x hx, hGF y hy] at h
  exact h

/-- DE 2b: two-sided bounds for a real-linear map of `ℂ` from its values at `1, i`:
`|Dv| ≤ (|D1| + |Di|)|v|` and `det D · |v| ≤ (|D1| + |Di|)|Dv|`. -/
theorem s07_de_linalg (D : ℂ →L[ℝ] ℂ) (v : ℂ) :
    ‖D v‖ ≤ (‖D 1‖ + ‖D I‖) * ‖v‖ ∧ D.det * ‖v‖ ≤ (‖D 1‖ + ‖D I‖) * ‖D v‖ := by
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = (D 1 - I * D I) / 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℂ, b = (D 1 + I * D I) / 2 := ⟨_, rfl⟩
  have hdec : D v = a * v + b * conj v := by rw [ha, hb]; exact s07_tw_jac_decomp D v
  have hdet : D.det = Complex.normSq a - Complex.normSq b := by
    rw [ha, hb]; exact s07_tw_jac_det D
  have hIn : ‖I * D I‖ = ‖D I‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  have han : ‖a‖ ≤ (‖D 1‖ + ‖D I‖) / 2 := by
    have h := norm_sub_le (D 1) (I * D I)
    rw [ha, norm_div, h2]
    linarith
  have hbn : ‖b‖ ≤ (‖D 1‖ + ‖D I‖) / 2 := by
    have h := norm_add_le (D 1) (I * D I)
    rw [hb, norm_div, h2]
    linarith
  have hab : ‖a‖ + ‖b‖ ≤ ‖D 1‖ + ‖D I‖ := by linarith
  constructor
  · have h : ‖D v‖ ≤ ‖a‖ * ‖v‖ + ‖b‖ * ‖v‖ := by
      rw [hdec]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg v]
  · have hid : (D.det : ℂ) * v = conj a * D v - b * conj (D v) := by
      rw [hdec, hdet, Complex.ofReal_sub, Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_conj_mul_self, map_add, map_mul, map_mul, Complex.conj_conj]
      ring
    have h : |D.det| * ‖v‖ ≤ ‖a‖ * ‖D v‖ + ‖b‖ * ‖D v‖ := by
      have h1 := congrArg norm hid
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h1
      rw [h1]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
    have h3 : D.det * ‖v‖ ≤ |D.det| * ‖v‖ :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg v)
    nlinarith [norm_nonneg (D v)]

/-- DE 2b: a `K`-q.c. self-map `H` of `𝔻` with `H 0 = 0` and boundary map `φ`, `φ 1 = 1`, extends by
reflection `z ↦ 1/z̄` to a normalized symmetric `K`-q.c. homeomorphism of `ℂ` (LZ `ab_reflect`,
`thm13_3_boundary_correspondence`). -/
theorem s07_de_reflect {K : ℝ} {φ : Circle → Circle} {H h : ℂ → ℂ} (hH : IsKQC H unitDisc K)
    (hHs : H '' unitDisc = unitDisc) (hb : HasDiskBoundaryValues H h) (hhφ : ∀ ζ : Circle, h ζ = φ ζ)
    (h0 : H 0 = 0) (h1 : φ 1 = 1) :
    ∃ G : ℂ → ℂ, IsKQC G univ K ∧ G '' univ = univ ∧ G 0 = 0 ∧ G 1 = 1 ∧
      (∀ z : ℂ, z ≠ 0 → G (conj z)⁻¹ = (conj (G z))⁻¹) ∧ ∀ ζ : Circle, G ζ = φ ζ := by
  obtain ⟨Fx, hFx⟩ :=
    thm13_3_boundary_correspondence isJordanDomain_unitDisc isJordanDomain_unitDisc ⟨K, hH⟩ hHs
  obtain ⟨g, hg, hgs, hgH, -, hsym, -⟩ := ab_reflect hH hHs h0 hFx
  have hgc : Continuous g := continuousOn_univ.mp hg.2.2.1.1
  -- on `∂𝔻`, `g` is the limit of `g = H` from inside, i.e. the boundary function `h`
  have hgb : ∀ ζ : Circle, g ζ = φ ζ := by
    intro ζ
    have hζ : (ζ : ℂ) ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.2 (Circle.norm_coe ζ)
    have hcl : (ζ : ℂ) ∈ closure unitDisc := by
      have hclD : closure unitDisc = closedBall (0 : ℂ) 1 := closure_ball (0 : ℂ) one_ne_zero
      rw [hclD]
      exact sphere_subset_closedBall hζ
    have : (𝓝[unitDisc] (ζ : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
    have h1 : Tendsto g (𝓝[unitDisc] (ζ : ℂ)) (𝓝 (g ζ)) :=
      hgc.continuousAt.continuousWithinAt.tendsto
    have h2 : Tendsto g (𝓝[unitDisc] (ζ : ℂ)) (𝓝 (h ζ)) :=
      (hb ζ hζ).congr' (eventually_mem_nhdsWithin.mono fun z hz => (hgH hz).symm)
    rw [← hhφ ζ]
    exact tendsto_nhds_unique h1 h2
  refine ⟨g, hg, hgs, ?_, ?_, hsym, hgb⟩
  · rw [hgH (mem_ball_self one_pos), h0]
  · have h2 := hgb 1
    rw [h1] at h2
    simpa using h2

/-- Helper for `s07_de_limit_circle`: `(z̄)⁻¹ = z` on `∂𝔻`. -/
theorem s07_de_inv_conj_unit {z : ℂ} (hz : ‖z‖ = 1) : (conj z)⁻¹ = z := by
  have h : conj z * z = 1 := by
    rw [Complex.conj_mul', hz]
    simp
  exact inv_eq_of_mul_eq_one_right h

/-- DE 2b: a symmetric `K`-q.c. homeomorphism `G` of `ℂ` fixing `0` maps `∂𝔻` onto itself and its
restriction is an orientation-preserving circle homeomorphism (`G(𝔻) = 𝔻`, `s07_circleHomeo_of_qcExt`,
`s07_de_circleMap`). -/
theorem s07_de_limit_circle {K : ℝ} {G : ℂ → ℂ} (hG : IsKQC G univ K) (hGs : G '' univ = univ)
    (h0 : G 0 = 0) (hsym : ∀ z : ℂ, z ≠ 0 → G (conj z)⁻¹ = (conj (G z))⁻¹) :
    ∃ ψ : Circle → Circle, Function.Bijective ψ ∧ Continuous ψ ∧ HasIncreasingLift ψ ∧
      ∀ ζ : Circle, (ψ ζ : ℂ) = G ζ := by
  have hgc : Continuous G := continuousOn_univ.mp hG.2.2.1.1
  have hinj : Function.Injective G := injOn_univ.mp hG.2.2.1.2.1
  have hnorm_inv : ∀ w : ℂ, ‖(conj w)⁻¹‖ = ‖w‖⁻¹ := fun w => by
    rw [norm_inv, Complex.norm_conj]
  have hne : ∀ z : ℂ, z ≠ 0 → G z ≠ 0 := fun z hz h => hz (hinj (h.trans h0.symm))
  -- `|G| = 1` on `∂𝔻`
  have hS : ∀ z : ℂ, ‖z‖ = 1 → ‖G z‖ = 1 := by
    intro z hz
    have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; exact one_ne_zero)
    have h := hsym z hz0
    rw [s07_de_inv_conj_unit hz] at h
    have h2 := congrArg norm h
    rw [hnorm_inv] at h2
    have hp : 0 < ‖G z‖ := norm_pos_iff.mpr (hne z hz0)
    have h3 : ‖G z‖ * ‖G z‖⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
    rw [← h2] at h3
    nlinarith
  -- `G` does not meet `∂𝔻` on `𝔻`
  have hD1 : ∀ z : ℂ, ‖z‖ < 1 → ‖G z‖ ≠ 1 := by
    intro z hz hGz
    rcases eq_or_ne z 0 with rfl | hz0
    · rw [h0, norm_zero] at hGz
      exact zero_ne_one hGz
    · have h := hsym z hz0
      rw [s07_de_inv_conj_unit hGz] at h
      have h2 := congrArg norm (hinj h)
      rw [hnorm_inv] at h2
      have h3 : 1 < ‖z‖⁻¹ := (one_lt_inv₀ (norm_pos_iff.mpr hz0)).mpr hz
      linarith
  -- `G(𝔻) ⊆ 𝔻` by connectedness
  have hsub : G '' unitDisc ⊆ unitDisc := by
    have hpc : IsPreconnected (G '' unitDisc) :=
      (convex_ball (0 : ℂ) 1).isPreconnected.image G hgc.continuousOn
    refine hpc.subset_left_of_subset_union (u := unitDisc) (v := {w : ℂ | 1 < ‖w‖}) isOpen_ball
      (isOpen_lt continuous_const continuous_norm) ?_ ?_ ?_
    · rw [Set.disjoint_left]
      intro w hw hw'
      have h1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
      have h2 : 1 < ‖w‖ := hw'
      linarith
    · rintro _ ⟨z, hz, rfl⟩
      rcases lt_or_gt_of_ne (hD1 z (mem_ball_zero_iff.mp hz)) with h | h
      · exact Or.inl (mem_ball_zero_iff.mpr h)
      · exact Or.inr h
    · exact ⟨0, ⟨0, mem_ball_self one_pos, h0⟩, mem_ball_self one_pos⟩
  -- `𝔻 ⊆ G(𝔻)`: points outside `𝔻̄` go outside by symmetry, points of `∂𝔻` to `∂𝔻`
  have hsup : unitDisc ⊆ G '' unitDisc := by
    intro w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    obtain ⟨z, -, rfl⟩ : w ∈ G '' univ := by
      rw [hGs]
      trivial
    refine ⟨z, mem_ball_zero_iff.mpr ?_, rfl⟩
    by_contra hz
    rw [not_lt] at hz
    rcases hz.lt_or_eq with hz | hz
    · have hz0 : z ≠ 0 := norm_pos_iff.mp (one_pos.trans hz)
      obtain ⟨z', hz'⟩ : ∃ z' : ℂ, z' = (conj z)⁻¹ := ⟨_, rfl⟩
      have hz'0 : z' ≠ 0 := by
        rw [hz']
        exact inv_ne_zero ((map_ne_zero _).mpr hz0)
      have hz'1 : ‖z'‖ < 1 := by
        rw [hz', hnorm_inv]
        exact inv_lt_one_of_one_lt₀ hz
      have hzz : (conj z')⁻¹ = z := by
        rw [hz', map_inv₀, Complex.conj_conj, inv_inv]
      have h := hsym z' hz'0
      rw [hzz] at h
      have hG' : ‖G z'‖ < 1 := mem_ball_zero_iff.mp (hsub ⟨z', mem_ball_zero_iff.mpr hz'1, rfl⟩)
      have hp : 0 < ‖G z'‖ := norm_pos_iff.mpr (hne z' hz'0)
      have h2 : ‖G z‖ = ‖G z'‖⁻¹ := by rw [h, hnorm_inv]
      have h3 : 1 < ‖G z'‖⁻¹ := (one_lt_inv₀ hp).mpr hG'
      linarith
    · exact absurd (hS z hz.symm) (ne_of_lt hw1)
  have himg : G '' unitDisc = unitDisc := hsub.antisymm hsup
  have hK : IsKQC G unitDisc K := ac_t_isKQC_restrict hG isOpen_ball (subset_univ _)
  have hbv : HasDiskBoundaryValues G G := fun ζ _ => hgc.continuousAt.continuousWithinAt.tendsto
  exact s07_de_circleMap (s07_circleHomeo_of_qcExt hK himg hbv)

/-- DE 2b: along circle homeomorphisms converging uniformly, `E(ψₙ)(0) → E(ψ)(0)` and
`DE(ψₙ)(0) → DE(ψ)(0)` (DE `extension_continuousOn_pair`, `extension_derivative_continuous`). -/
theorem s07_de_cont0 {ψ : ℕ → Circle → Circle} {ψ₀ : Circle → Circle}
    (hb : ∀ n, Function.Bijective (ψ n)) (hc : ∀ n, Continuous (ψ n))
    (hb₀ : Function.Bijective ψ₀) (hc₀ : Continuous ψ₀)
    (hu : TendstoUniformly (fun n ζ => (ψ n ζ : ℂ)) (fun ζ => (ψ₀ ζ : ℂ)) atTop) :
    Tendsto (fun n => extension (ψ n) 0) atTop (𝓝 (extension ψ₀ 0)) ∧
      Tendsto (fun n => fderiv ℝ (extension (ψ n)) 0) atTop (𝓝 (fderiv ℝ (extension ψ₀) 0)) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → C(Circle, Circle), (fun n => ⇑(Ψ n)) = ψ :=
    ⟨fun n => ⟨ψ n, hc n⟩, rfl⟩
  obtain ⟨Ψ₀, hΨ₀⟩ : ∃ Ψ₀ : C(Circle, Circle), ⇑Ψ₀ = ψ₀ := ⟨⟨ψ₀, hc₀⟩, rfl⟩
  subst hΨ hΨ₀
  have hT : Tendsto Ψ atTop (𝓝 Ψ₀) := by
    rw [ContinuousMap.tendsto_iff_tendstoUniformly]
    refine Metric.tendstoUniformly_iff.mpr ?_
    rw [Metric.tendstoUniformly_iff] at hu
    intro ε hε
    filter_upwards [hu ε hε] with n hn ζ
    exact hn ζ
  have hS : ∀ n, Ψ n ∈ {φ : C(Circle, Circle) | Function.Bijective φ} := hb
  have hTw : Tendsto Ψ atTop (𝓝[{φ : C(Circle, Circle) | Function.Bijective φ}] Ψ₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hT, Eventually.of_forall hS⟩
  have hD := (extension_derivative_continuous Ψ₀ hb₀).tendsto.comp hTw
  have h1 : Tendsto (fun n => fderiv ℝ (extension (Ψ n)) 0 1) atTop
      (𝓝 (fderiv ℝ (extension Ψ₀) 0 1)) := (continuous_fst.tendsto _).comp hD
  have hI : Tendsto (fun n => fderiv ℝ (extension (Ψ n)) 0 I) atTop
      (𝓝 (fderiv ℝ (extension Ψ₀) 0 I)) := (continuous_snd.tendsto _).comp hD
  have hDn : Tendsto (fun n => fderiv ℝ (extension (Ψ n)) 0) atTop
      (𝓝 (fderiv ℝ (extension Ψ₀) 0)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun n => ‖fderiv ℝ (extension (Ψ n)) 0 1 - fderiv ℝ (extension Ψ₀) 0 1‖ +
        ‖fderiv ℝ (extension (Ψ n)) 0 I - fderiv ℝ (extension Ψ₀) 0 I‖) atTop (𝓝 0) := by
      simpa using (tendsto_iff_norm_sub_tendsto_zero.mp h1).add
        (tendsto_iff_norm_sub_tendsto_zero.mp hI)
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
    have h := (s07_de_linalg (fderiv ℝ (extension (Ψ n)) 0 - fderiv ℝ (extension Ψ₀) 0) v).1
    simpa only [sub_apply] using h
  refine ⟨?_, hDn⟩
  obtain ⟨V, Gf, hV, hmem, hGc, hEq⟩ := extension_continuousOn_pair 0 (by norm_num) Ψ₀ hb₀
  have hP : Tendsto (fun n => ((0 : ℂ), Ψ n)) atTop (𝓝 ((0 : ℂ), Ψ₀)) :=
    tendsto_const_nhds.prodMk_nhds hT
  have hev : ∀ᶠ n in atTop, ((0 : ℂ), Ψ n) ∈ V := hP (hV.mem_nhds hmem)
  have hG := ((hGc _ hmem).continuousAt (hV.mem_nhds hmem)).tendsto.comp hP
  rw [← hEq _ hmem hb₀ (by norm_num)] at hG
  refine hG.congr' ?_
  filter_upwards [hev] with n hn
  exact (hEq _ hn (hb n) (by norm_num)).symm

/-- Helper for `s07_de_bound0`: rotating the target by `c = conj (φ 1)` normalizes `φ 1 = 1` and
keeps `|E(φ)(0)|`, `|DE(φ)(0) 1|`, `|DE(φ)(0) i|` and `det DE(φ)(0)` (`E` commutes with rotations,
DE `extension_naturality`). -/
theorem s07_de_rot {K : ℝ} {φ : Circle → Circle} (hφb : Function.Bijective φ)
    (hφc : Continuous φ) (hor : HasIncreasingLift φ) {H h : ℂ → ℂ} (hH : IsKQC H unitDisc K)
    (hHs : H '' unitDisc = unitDisc) (hb : HasDiskBoundaryValues H h)
    (hhφ : ∀ ζ : Circle, h ζ = φ ζ) (h0 : H 0 = 0) :
    ∃ φ' : Circle → Circle, Function.Bijective φ' ∧ Continuous φ' ∧ HasIncreasingLift φ' ∧
      φ' 1 = 1 ∧ (∃ H' h' : ℂ → ℂ, IsKQC H' unitDisc K ∧ H' '' unitDisc = unitDisc ∧
        HasDiskBoundaryValues H' h' ∧ (∀ ζ : Circle, h' ζ = φ' ζ) ∧ H' 0 = 0) ∧
      ‖extension φ' 0‖ = ‖extension φ 0‖ ∧
      ‖fderiv ℝ (extension φ') 0 1‖ = ‖fderiv ℝ (extension φ) 0 1‖ ∧
      ‖fderiv ℝ (extension φ') 0 I‖ = ‖fderiv ℝ (extension φ) 0 I‖ ∧
      (fderiv ℝ (extension φ') 0).det = (fderiv ℝ (extension φ) 0).det := by
  obtain ⟨c, hcd⟩ : ∃ c : ℂ, c = conj (φ 1 : ℂ) := ⟨_, rfl⟩
  have hc1 : ‖c‖ = 1 := by rw [hcd, Complex.norm_conj, Circle.norm_coe]
  have hcc : c * (φ 1 : ℂ) = 1 := by
    rw [hcd, Complex.conj_mul', Circle.norm_coe]
    simp
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc1]; exact one_ne_zero)
  have hgp : IsDiskAutPlus (fun w => c * w) :=
    ⟨c, 0, hc1, by norm_num, fun w => by rw [diskAut_zero_left]⟩
  have hg : IsDiskAut (fun w => c * w) := Or.inl hgp
  have hid : IsDiskAut id := Or.inl isDiskAutPlus_id
  obtain ⟨ψg, hψg⟩ : ∃ ψg : Circle → Circle, ψg = diskAutToCircle _ hg := ⟨_, rfl⟩
  obtain ⟨ψh, hψh⟩ : ∃ ψh : Circle → Circle, ψh = diskAutToCircle _ hid := ⟨_, rfl⟩
  have hψgv : ∀ ζ : Circle, c * (ζ : ℂ) = (ψg ζ : ℂ) := fun ζ => by
    rw [hψg]
    exact diskAutToCircle_coe _ hg ζ
  have hψhv : ∀ ζ : Circle, id (ζ : ℂ) = (ψh ζ : ℂ) := fun ζ => by
    rw [hψh]
    exact diskAutToCircle_coe _ hid ζ
  have hψgb : Function.Bijective ψg := by
    rw [hψg]
    exact bijective_diskAutToCircle_of_isDiskAut _ hg
  have hψhb : Function.Bijective ψh := by
    rw [hψh]
    exact bijective_diskAutToCircle_of_isDiskAut _ hid
  have hψgc : Continuous ψg := by
    rw [hψg]
    exact continuous_diskAutToCircle _ hg
  have hψhc : Continuous ψh := by
    rw [hψh]
    exact continuous_diskAutToCircle _ hid
  have hψgl : HasIncreasingLift ψg :=
    CircleLift.hasIncreasingLift_of_isDiskAutPlus hgp ψg (fun ζ => (hψgv ζ).symm)
  have hψhl : HasIncreasingLift ψh :=
    CircleLift.hasIncreasingLift_of_isDiskAutPlus isDiskAutPlus_id ψh (fun ζ => (hψhv ζ).symm)
  have hval : ∀ ζ : Circle, ((ψg ∘ φ ∘ ψh) ζ : ℂ) = c * (φ ζ : ℂ) := fun ζ => by
    have h1 : ψh ζ = ζ := Subtype.ext (hψhv ζ).symm
    show (ψg (φ (ψh ζ)) : ℂ) = _
    rw [h1, ← hψgv]
  have hext : ∀ w : ℂ, ‖w‖ ≤ 1 → extension (ψg ∘ φ ∘ ψh) w = c * extension φ w := fun w hw =>
    extension_naturality φ (fun w => c * w) id ψg ψh hg hid hψgv hψhv hφb hφc hψgb hψhb w hw
  -- the rotated q.c. extension `c H`
  have himgR : (fun w => c * w) '' unitDisc = unitDisc := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      apply mem_ball_zero_iff.mpr
      show ‖c * u‖ < 1
      rw [norm_mul, hc1, one_mul]
      exact mem_ball_zero_iff.mp hu
    · intro hw
      refine ⟨conj c * w, ?_, ?_⟩
      · apply mem_ball_zero_iff.mpr
        rw [norm_mul, Complex.norm_conj, hc1, one_mul]
        exact mem_ball_zero_iff.mp hw
      · show c * (conj c * w) = w
        rw [← mul_assoc, Complex.mul_conj', hc1]
        simp
  have hR : IsKQC (fun w => c * w) unitDisc 1 :=
    isKQC_one_of_conformal (D' := unitDisc) isOpen_ball
      ⟨fun u _ => (differentiableAt_id.const_mul c).differentiableWithinAt,
        fun u _ u' _ hu => mul_left_cancel₀ hc0 hu, himgR⟩
  have hH' : IsKQC ((fun w => c * w) ∘ H) unitDisc (K * 1) := thm7_1_comp hH hR hHs.subset
  rw [mul_one] at hH'
  refine ⟨ψg ∘ φ ∘ ψh, hψgb.comp (hφb.comp hψhb), hψgc.comp (hφc.comp hψhc),
    CircleLift.hasIncreasingLift_comp hψgl (CircleLift.hasIncreasingLift_comp hor hψhl), ?_,
    ⟨(fun w => c * w) ∘ H, fun w => c * h w, hH', ?_, ?_, ?_, ?_⟩, ?_⟩
  · apply Subtype.ext
    rw [hval, hcc]
    rfl
  · rw [image_comp, hHs, himgR]
  · intro ζ hζ
    exact ((continuous_const.mul continuous_id).tendsto _).comp (hb ζ hζ)
  · intro ζ
    show c * h ζ = _
    rw [hval, hhφ]
  · show c * H 0 = 0
    rw [h0, mul_zero]
  -- the invariants at `0`
  have hE0 : extension (ψg ∘ φ ∘ ψh) 0 = c * extension φ 0 := hext 0 (by simp)
  have hEq : extension (ψg ∘ φ ∘ ψh) =ᶠ[𝓝 0] fun w => c * extension φ w := by
    filter_upwards [closedBall_mem_nhds (0 : ℂ) one_pos] with w hw
    exact hext w (mem_closedBall_zero_iff.mp hw)
  have hdiff : DifferentiableAt ℝ (extension φ) 0 :=
    ((isOpen_ball.analyticOn_iff_analyticOnNhd.mp (extension_analyticOn_disk φ hφb hφc)) 0
      (mem_ball_self one_pos)).differentiableAt
  have hD : fderiv ℝ (extension (ψg ∘ φ ∘ ψh)) 0 = c • fderiv ℝ (extension φ) 0 := by
    rw [hEq.fderiv_eq]
    exact fderiv_const_smul hdiff c
  have hDv : ∀ v : ℂ, fderiv ℝ (extension (ψg ∘ φ ∘ ψh)) 0 v = c * fderiv ℝ (extension φ) 0 v :=
    fun v => by
      rw [hD]
      rfl
  refine ⟨by rw [hE0, norm_mul, hc1, one_mul], by rw [hDv, norm_mul, hc1, one_mul],
    by rw [hDv, norm_mul, hc1, one_mul], ?_⟩
  rw [s07_tw_jac_det, s07_tw_jac_det, hDv 1, hDv I,
    show ∀ a b : ℂ, (c * a - I * (c * b)) / 2 = c * ((a - I * b) / 2) from fun a b => by ring,
    show ∀ a b : ℂ, (c * a + I * (c * b)) / 2 = c * ((a + I * b) / 2) from fun a b => by ring,
    Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_eq_norm_sq c, hc1]
  ring

/-- Helper for `s07_de_bound0` ([DE §5] compactness): over circle maps `φ` with a `K`-q.c.
extension fixing `0`, `|DE(φ)(0) 1| + |DE(φ)(0) i|`, `1/det DE(φ)(0)` and `1/ϖ(E(φ)(0))` are bounded.
By contradiction: normalize `φ 1 = 1` (`s07_de_rot`), reflect (`s07_de_reflect`), extract a limit
(`s03_wc_compact`), read its boundary map as a circle homeomorphism `ψ` (`s07_de_limit_circle`) and
pass to the limit (`s07_de_cont0`), where `det DE(ψ)(0) > 0` and `E(ψ)(0) ∈ 𝔻`. -/
theorem s07_de_bound0_key (K : ℝ) (hK : 1 ≤ K) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ φ : Circle → Circle, Function.Bijective φ → Continuous φ → HasIncreasingLift φ →
    ∀ H h : ℂ → ℂ, IsKQC H unitDisc K → H '' unitDisc = unitDisc → HasDiskBoundaryValues H h →
    (∀ ζ : Circle, h ζ = φ ζ) → H 0 = 0 →
      ‖fderiv ℝ (extension φ) 0 1‖ + ‖fderiv ℝ (extension φ) 0 I‖ ≤ C ∧
        1 ≤ C * (fderiv ℝ (extension φ) 0).det ∧ 1 ≤ C * varpi (extension φ 0) := by
  by_contra hcon
  have hbad : ∀ n : ℕ, ∃ φ : Circle → Circle, ∃ H h : ℂ → ℂ, Function.Bijective φ ∧
      Continuous φ ∧ HasIncreasingLift φ ∧ φ 1 = 1 ∧ IsKQC H unitDisc K ∧
      H '' unitDisc = unitDisc ∧ HasDiskBoundaryValues H h ∧ (∀ ζ : Circle, h ζ = φ ζ) ∧
      H 0 = 0 ∧ ¬ (‖fderiv ℝ (extension φ) 0 1‖ + ‖fderiv ℝ (extension φ) 0 I‖ ≤ (n : ℝ) + 1 ∧
        1 ≤ ((n : ℝ) + 1) * (fderiv ℝ (extension φ) 0).det ∧
        1 ≤ ((n : ℝ) + 1) * varpi (extension φ 0)) := by
    intro n
    by_contra hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    refine hcon ⟨(n : ℝ) + 1, by linarith, ?_⟩
    intro φ hφb hφc hor H h hH hHs hb hhφ h0
    obtain ⟨φ', hφ'b, hφ'c, hφ'l, hφ'1, ⟨H', h', hH', hH's, hb', hhφ', h0'⟩, hE, h1, hI, hdet⟩ :=
      s07_de_rot hφb hφc hor hH hHs hb hhφ h0
    have hv : varpi (extension φ' 0) = varpi (extension φ 0) := by
      show 1 - ‖extension φ' 0‖ ^ 2 = 1 - ‖extension φ 0‖ ^ 2
      rw [hE]
    by_contra hP
    exact hn ⟨φ', H', h', hφ'b, hφ'c, hφ'l, hφ'1, hH', hH's, hb', hhφ', h0', by
      rw [h1, hI, hdet, hv]
      exact hP⟩
  choose φs Hs hs hb hc hl h1 hK' hS hB hhφ h0 hP using hbad
  have hrefl := fun n => s07_de_reflect (hK' n) (hS n) (hB n) (hhφ n) (h0 n) (h1 n)
  choose Gs hGK hGs hG0 hG1 hGsym hGb using hrefl
  obtain ⟨ns, hns, G, -, hGK', hGs', hG0', -, -, -, hconv, -⟩ :=
    s03_wc_compact hK Gs hGK hGs hG0 hG1
  have hcpt := tendstoLocallyUniformly_iff_forall_isCompact.mp hconv
  have hpt : ∀ w, Tendsto (fun n => Gs (ns n) w) atTop (𝓝 (G w)) := fun w =>
    (hcpt {w} isCompact_singleton).tendsto_at (mem_singleton w)
  have hGinj : Function.Injective G := injOn_univ.mp hGK'.2.2.1.2.1
  -- the limit is symmetric
  have hsym : ∀ z : ℂ, z ≠ 0 → G (conj z)⁻¹ = (conj (G z))⁻¹ := by
    intro z hz
    have hGz : conj (G z) ≠ 0 := (map_ne_zero _).mpr (fun h => hz (hGinj (h.trans hG0'.symm)))
    have h1 : Tendsto (fun n => (conj (Gs (ns n) z))⁻¹) atTop (𝓝 (conj (G z))⁻¹) :=
      ((Complex.continuous_conj.tendsto _).comp (hpt z)).inv₀ hGz
    have h2 : Tendsto (fun n => Gs (ns n) (conj z)⁻¹) atTop (𝓝 (conj (G z))⁻¹) :=
      Tendsto.congr (fun n => (hGsym (ns n) z hz).symm) h1
    exact tendsto_nhds_unique (hpt _) h2
  obtain ⟨ψ, hψb, hψc, hψl, hψv⟩ := s07_de_limit_circle hGK' hGs' hG0' hsym
  -- uniform convergence of the boundary maps
  have hU : TendstoUniformly (fun n ζ => (φs (ns n) ζ : ℂ)) (fun ζ => (ψ ζ : ℂ)) atTop := by
    have hS1 := Metric.tendstoUniformlyOn_iff.mp (hcpt _ (isCompact_sphere (0 : ℂ) 1))
    refine Metric.tendstoUniformly_iff.mpr fun ε hε => ?_
    filter_upwards [hS1 ε hε] with n hn ζ
    rw [hψv, ← hGb (ns n) ζ]
    exact hn ζ (mem_sphere_zero_iff_norm.2 (Circle.norm_coe ζ))
  obtain ⟨hp_t, hD_t⟩ := s07_de_cont0 (fun n => hb (ns n)) (fun n => hc (ns n)) hψb hψc hU
  -- the limit quantities
  have han0 := (isOpen_ball.analyticOn_iff_analyticOnNhd.mp (extension_analyticOn_disk ψ hψb hψc)) 0
    (mem_ball_self one_pos)
  have hdetψ : 0 < (fderiv ℝ (extension ψ) 0).det :=
    s07_de_det_pos han0.differentiableAt (extension_jacobian_pos ψ hψb hψc hψl 0 (by simp))
  have hvψ : 0 < varpi (extension ψ 0) := by
    have h := extension_mem_disk ψ hψb hψc 0 (by simp)
    show 0 < 1 - ‖extension ψ 0‖ ^ 2
    nlinarith [norm_nonneg (extension ψ 0)]
  have hM_t : Tendsto (fun n => ‖fderiv ℝ (extension (φs (ns n))) 0 1‖ +
      ‖fderiv ℝ (extension (φs (ns n))) 0 I‖) atTop
      (𝓝 (‖fderiv ℝ (extension ψ) 0 1‖ + ‖fderiv ℝ (extension ψ) 0 I‖)) :=
    (((continuous_eval_const (1 : ℂ)).tendsto _).comp hD_t).norm.add
      (((continuous_eval_const I).tendsto _).comp hD_t).norm
  have hdet_t : Tendsto (fun n => (fderiv ℝ (extension (φs (ns n))) 0).det) atTop
      (𝓝 (fderiv ℝ (extension ψ) 0).det) :=
    (ContinuousLinearMap.continuous_det.tendsto _).comp hD_t
  have hv_t : Tendsto (fun n => varpi (extension (φs (ns n)) 0)) atTop
      (𝓝 (varpi (extension ψ 0))) :=
    ((continuous_const.sub (continuous_norm.pow 2)).tendsto _).comp hp_t
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = ‖fderiv ℝ (extension ψ) 0 1‖ + ‖fderiv ℝ (extension ψ) 0 I‖ :=
    ⟨_, rfl⟩
  obtain ⟨d, hdd⟩ : ∃ d : ℝ, d = (fderiv ℝ (extension ψ) 0).det := ⟨_, rfl⟩
  obtain ⟨w, hwd⟩ : ∃ w : ℝ, w = varpi (extension ψ 0) := ⟨_, rfl⟩
  rw [← hMd] at hM_t
  rw [← hdd] at hdet_t hdetψ
  rw [← hwd] at hv_t hvψ
  -- eventually the `ns k`-th map is not bad: contradiction
  have hns_t : Tendsto (fun k => (ns k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hns.tendsto_atTop
  have e1 := hM_t.eventually (gt_mem_nhds (lt_add_one M))
  have e2 := hdet_t.eventually (lt_mem_nhds (half_lt_self hdetψ))
  have e3 := hv_t.eventually (lt_mem_nhds (half_lt_self hvψ))
  have e4 := hns_t.eventually_ge_atTop (max M (max (2 / d) (2 / w)))
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := (e1.and (e2.and (e3.and e4))).exists
  have hk0 : (0 : ℝ) ≤ ns k := Nat.cast_nonneg _
  have hkM : M ≤ ns k := (le_max_left _ _).trans hk4
  have hkd : 2 / d ≤ ns k := ((le_max_left _ _).trans (le_max_right _ _)).trans hk4
  have hkw : 2 / w ≤ ns k := ((le_max_right _ _).trans (le_max_right _ _)).trans hk4
  apply hP (ns k)
  refine ⟨by linarith, ?_, ?_⟩
  · have hpos : 0 < (fderiv ℝ (extension (φs (ns k))) 0).det := (half_pos hdetψ).trans hk2
    calc (1 : ℝ) = 2 / d * (d / 2) := by field_simp
      _ ≤ (ns k : ℝ) * (fderiv ℝ (extension (φs (ns k))) 0).det :=
        mul_le_mul hkd hk2.le (half_pos hdetψ).le hk0
      _ ≤ _ := by nlinarith
  · have hpos : 0 < varpi (extension (φs (ns k)) 0) := (half_pos hvψ).trans hk3
    calc (1 : ℝ) = 2 / w * (w / 2) := by field_simp
      _ ≤ (ns k : ℝ) * varpi (extension (φs (ns k)) 0) :=
        mul_le_mul hkw hk3.le (half_pos hvψ).le hk0
      _ ≤ _ := by nlinarith

/-- DE 2b (compactness at `0`, [DE §5]): for boundary maps of `K`-q.c. self-maps `H` of `𝔻` with
`H 0 = 0`, `|DE(φ)(0) v| ≍ ϖ(E(φ)(0)) |v|` with a constant depending only on `K`. -/
theorem s07_de_bound0 (K : ℝ) (hK : 1 ≤ K) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ φ : Circle → Circle, Function.Bijective φ → Continuous φ → HasIncreasingLift φ →
    ∀ H h : ℂ → ℂ, IsKQC H unitDisc K → H '' unitDisc = unitDisc → HasDiskBoundaryValues H h →
    (∀ ζ : Circle, h ζ = φ ζ) → H 0 = 0 → ∀ v : ℂ,
      ‖fderiv ℝ (extension φ) 0 v‖ ≤ C * varpi (extension φ 0) * ‖v‖ ∧
        varpi (extension φ 0) * ‖v‖ ≤ C * ‖fderiv ℝ (extension φ) 0 v‖ := by
  obtain ⟨C, hC, hkey⟩ := s07_de_bound0_key K hK
  refine ⟨C * C, by nlinarith, ?_⟩
  intro φ hφb hφc hor H h hH hHs hb hhφ h0 v
  obtain ⟨hM, hdet, hv⟩ := hkey φ hφb hφc hor H h hH hHs hb hhφ h0
  obtain ⟨hl1, hl2⟩ := s07_de_linalg (fderiv ℝ (extension φ) 0) v
  have hv1 : varpi (extension φ 0) ≤ 1 := by
    show 1 - ‖extension φ 0‖ ^ 2 ≤ 1
    nlinarith [norm_nonneg (extension φ 0)]
  have hC0 : 0 ≤ C := by linarith
  have hnv := norm_nonneg v
  have hnD := norm_nonneg (fderiv ℝ (extension φ) 0 v)
  constructor
  · calc ‖fderiv ℝ (extension φ) 0 v‖ ≤ C * ‖v‖ :=
          hl1.trans (mul_le_mul_of_nonneg_right hM hnv)
      _ ≤ C * C * varpi (extension φ 0) * ‖v‖ := by
        have := mul_le_mul_of_nonneg_left hv (mul_nonneg hC0 hnv)
        nlinarith
  · have h1 : (fderiv ℝ (extension φ) 0).det * ‖v‖ ≤ C * ‖fderiv ℝ (extension φ) 0 v‖ :=
      hl2.trans (mul_le_mul_of_nonneg_right hM hnD)
    calc varpi (extension φ 0) * ‖v‖ ≤ ‖v‖ := by nlinarith
      _ ≤ C * (fderiv ℝ (extension φ) 0).det * ‖v‖ := by nlinarith
      _ = C * ((fderiv ℝ (extension φ) 0).det * ‖v‖) := by ring
      _ ≤ C * (C * ‖fderiv ℝ (extension φ) 0 v‖) := mul_le_mul_of_nonneg_left h1 hC0
      _ = C * C * ‖fderiv ℝ (extension φ) 0 v‖ := by ring

/-- Helper for `s07_de_natural`: `g_c` maps `𝔻` onto `𝔻`. -/
theorem s07_de_aut_image {c : ℂ} (hc : ‖c‖ < 1) : diskAut c '' unitDisc = unitDisc := by
  have hnc : ‖-c‖ < 1 := by rwa [norm_neg]
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact mem_ball_zero_iff.mpr (diskAut_maps_disk_to_disk c z hc (mem_ball_zero_iff.mp hz))
  · intro hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    exact ⟨diskAut (-c) w, mem_ball_zero_iff.mpr (diskAut_maps_disk_to_disk _ _ hnc hw1),
      diskAut_neg_left_inv hc hw1.le⟩

/-- Helper for `s07_de_natural`: `g_c` is a conformal self-map of `𝔻`, hence `1`-q.c. -/
theorem s07_de_aut_qc {c : ℂ} (hc : ‖c‖ < 1) : IsKQC (diskAut c) unitDisc 1 :=
  isKQC_one_of_conformal (D' := unitDisc) isOpen_ball
    ⟨fun z hz =>
      (diskAut_differentiableAt c z hc (mem_ball_zero_iff.mp hz).le).differentiableWithinAt,
      fun _ hz _ hz' h => diskAut_inj hc (mem_ball_zero_iff.mp hz).le (mem_ball_zero_iff.mp hz').le h,
      s07_de_aut_image hc⟩

/-- DE 2b (naturality): for `z ∈ 𝔻`, `A = g_{-z}` (`A 0 = z`) and `B = g_{H z}` (`B (H z) = 0`),
`φ' = B ∘ φ ∘ A` on `∂𝔻` is again the boundary map of a `K`-q.c. self-map `B ∘ H ∘ A` fixing `0`, and
`E(φ') = B ∘ E(φ) ∘ A` on `𝔻̄` (DE `extension_naturality`). -/
theorem s07_de_natural {K : ℝ} {φ : Circle → Circle} (hφb : Function.Bijective φ)
    (hφc : Continuous φ) (hor : HasIncreasingLift φ) {H h : ℂ → ℂ} (hH : IsKQC H unitDisc K)
    (hHs : H '' unitDisc = unitDisc) (hb : HasDiskBoundaryValues H h)
    (hhφ : ∀ ζ : Circle, h ζ = φ ζ) {z : ℂ} (hz : z ∈ unitDisc) :
    ∃ φ' : Circle → Circle, Function.Bijective φ' ∧ Continuous φ' ∧ HasIncreasingLift φ' ∧
      IsKQC (fun w => diskAut (H z) (H (diskAut (-z) w))) unitDisc K ∧
      (fun w => diskAut (H z) (H (diskAut (-z) w))) '' unitDisc = unitDisc ∧
      HasDiskBoundaryValues (fun w => diskAut (H z) (H (diskAut (-z) w)))
        (fun w => diskAut (H z) (h (diskAut (-z) w))) ∧
      (∀ ζ : Circle, diskAut (H z) (h (diskAut (-z) ζ)) = φ' ζ) ∧
      ∀ w : ℂ, ‖w‖ ≤ 1 → extension φ' w = diskAut (H z) (extension φ (diskAut (-z) w)) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hnz : ‖-z‖ < 1 := by rwa [norm_neg]
  have hHz : H z ∈ unitDisc := hHs ▸ mem_image_of_mem H hz
  have ha : ‖H z‖ < 1 := mem_ball_zero_iff.mp hHz
  have hBp : IsDiskAutPlus (diskAut (H z)) := ⟨1, H z, norm_one, ha, fun w => (one_mul _).symm⟩
  have hAp : IsDiskAutPlus (diskAut (-z)) := ⟨1, -z, norm_one, hnz, fun w => (one_mul _).symm⟩
  have hB : IsDiskAut (diskAut (H z)) := Or.inl hBp
  have hA : IsDiskAut (diskAut (-z)) := Or.inl hAp
  -- the circle maps of `B = g_{H z}` and `A = g_{-z}`
  obtain ⟨ψB, hψB⟩ : ∃ ψB : Circle → Circle, ψB = diskAutToCircle _ hB := ⟨_, rfl⟩
  obtain ⟨ψA, hψA⟩ : ∃ ψA : Circle → Circle, ψA = diskAutToCircle _ hA := ⟨_, rfl⟩
  have hψBv : ∀ ζ : Circle, diskAut (H z) (ζ : ℂ) = (ψB ζ : ℂ) := fun ζ => by
    rw [hψB]
    exact diskAutToCircle_coe _ hB ζ
  have hψAv : ∀ ζ : Circle, diskAut (-z) (ζ : ℂ) = (ψA ζ : ℂ) := fun ζ => by
    rw [hψA]
    exact diskAutToCircle_coe _ hA ζ
  have hψBb : Function.Bijective ψB := by
    rw [hψB]
    exact bijective_diskAutToCircle_of_isDiskAut _ hB
  have hψAb : Function.Bijective ψA := by
    rw [hψA]
    exact bijective_diskAutToCircle_of_isDiskAut _ hA
  have hψBc : Continuous ψB := by
    rw [hψB]
    exact continuous_diskAutToCircle _ hB
  have hψAc : Continuous ψA := by
    rw [hψA]
    exact continuous_diskAutToCircle _ hA
  have hψBl : HasIncreasingLift ψB :=
    CircleLift.hasIncreasingLift_of_isDiskAutPlus hBp ψB (fun ζ => (hψBv ζ).symm)
  have hψAl : HasIncreasingLift ψA :=
    CircleLift.hasIncreasingLift_of_isDiskAutPlus hAp ψA (fun ζ => (hψAv ζ).symm)
  -- `B ∘ H ∘ A` is a `K`-q.c. self-map of `𝔻`
  have himgHA : (H ∘ diskAut (-z)) '' unitDisc = unitDisc := by
    rw [image_comp, s07_de_aut_image hnz, hHs]
  have hHA : IsKQC (H ∘ diskAut (-z)) unitDisc (1 * K) :=
    thm7_1_comp (s07_de_aut_qc hnz) hH (s07_de_aut_image hnz).subset
  have hBHA : IsKQC (diskAut (H z) ∘ (H ∘ diskAut (-z))) unitDisc (1 * K * 1) :=
    thm7_1_comp hHA (s07_de_aut_qc ha) himgHA.subset
  rw [one_mul, mul_one] at hBHA
  refine ⟨ψB ∘ φ ∘ ψA, hψBb.comp (hφb.comp hψAb), hψBc.comp (hφc.comp hψAc),
    CircleLift.hasIncreasingLift_comp hψBl (CircleLift.hasIncreasingLift_comp hor hψAl), hBHA, ?_, ?_, ?_, ?_⟩
  · show (diskAut (H z) ∘ (H ∘ diskAut (-z))) '' unitDisc = unitDisc
    rw [image_comp, himgHA, s07_de_aut_image ha]
  · intro ζ hζ
    have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.1 hζ
    have hη1 : ‖diskAut (-z) ζ‖ = 1 := diskAut_norm_eq_one (-z) ζ hnz hζ1
    have hηS : diskAut (-z) ζ ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.2 hη1
    have hAt : Tendsto (diskAut (-z)) (𝓝[unitDisc] ζ) (𝓝[unitDisc] (diskAut (-z) ζ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun w hw => ?_⟩
      · exact ((diskAut_differentiableAt (-z) ζ hnz hζ1.le).continuousAt.tendsto).mono_left
          nhdsWithin_le_nhds
      · exact mem_ball_zero_iff.mpr (diskAut_maps_disk_to_disk _ _ hnz (mem_ball_zero_iff.mp hw))
    have hηU : diskAut (-z) ζ ∈ Submonoid.unitSphere ℂ := hηS
    have hhη : ‖h (diskAut (-z) ζ)‖ ≤ 1 := by
      have := hhφ ⟨diskAut (-z) ζ, hηU⟩
      rw [show ((⟨diskAut (-z) ζ, hηU⟩ : Circle) : ℂ) = diskAut (-z) ζ from rfl] at this
      rw [this, Circle.norm_coe]
    exact ((diskAut_differentiableAt (H z) _ ha hhη).continuousAt.tendsto).comp
      ((hb _ hηS).comp hAt)
  · intro ζ
    rw [hψAv ζ, hhφ (ψA ζ), hψBv]
    rfl
  · intro w hw
    exact extension_naturality φ (diskAut (H z)) (diskAut (-z)) ψB ψA hB hA hψBv hψAv hφb hφc
      hψBb hψAb w hw

/-- DE 2b (all points): `ϖ(z)|DE(φ)(z)v| ≍ ϖ(E(φ)(z))|v|` on `𝔻` for boundary maps of `K`-q.c.
self-maps of `𝔻`, with a constant depending only on `K` (`s07_de_bound0` transported by
`s07_de_natural`). -/
theorem s07_de_inf (K : ℝ) (hK : 1 ≤ K) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ φ : Circle → Circle, Function.Bijective φ → Continuous φ → HasIncreasingLift φ →
    ∀ H h : ℂ → ℂ, IsKQC H unitDisc K → H '' unitDisc = unitDisc → HasDiskBoundaryValues H h →
    (∀ ζ : Circle, h ζ = φ ζ) → ∀ z ∈ unitDisc, ∀ v : ℂ,
      varpi z * ‖fderiv ℝ (extension φ) z v‖ ≤ C * varpi (extension φ z) * ‖v‖ ∧
        varpi (extension φ z) * ‖v‖ ≤ C * varpi z * ‖fderiv ℝ (extension φ) z v‖ := by
  obtain ⟨C, hC, hC0⟩ := s07_de_bound0 K hK
  refine ⟨C, hC, ?_⟩
  intro φ hφb hφc hor H h hH hHs hb hhφ z hz v
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hnz : ‖-z‖ < 1 := by rwa [norm_neg]
  have hHz : H z ∈ unitDisc := hHs ▸ mem_image_of_mem H hz
  have ha : ‖H z‖ < 1 := mem_ball_zero_iff.mp hHz
  have hA0 : diskAut (-z) 0 = z := by rw [diskAut_zero, neg_neg]
  -- the normalized map `B ∘ H ∘ A` (`A = g_{-z}`, `B = g_{H z}`) fixes `0`
  obtain ⟨φ', hφ'b, hφ'c, hφ'l, hqc, himg, hbv, hval, hext⟩ :=
    s07_de_natural hφb hφc hor hH hHs hb hhφ hz
  have hH0 : (fun w => diskAut (H z) (H (diskAut (-z) w))) 0 = 0 := by
    show diskAut (H z) (H (diskAut (-z) 0)) = 0
    rw [hA0, diskAut_self _ ha]
  obtain ⟨hup, hlo⟩ := hC0 φ' hφ'b hφ'c hφ'l _ _ hqc himg hbv hval hH0 v
  -- `E(φ') = B ∘ E(φ) ∘ A` near `0`: chain rule at `0`
  obtain ⟨p, hpd⟩ : ∃ p : ℂ, p = extension φ z := ⟨_, rfl⟩
  have hp : ‖p‖ < 1 := hpd ▸ extension_mem_disk φ hφb hφc z hz1
  have hE0 : extension φ' 0 = diskAut (H z) p := by
    rw [hext 0 (by simp), hA0, hpd]
  have hEq : extension φ' =ᶠ[𝓝 0] fun w => diskAut (H z) (extension φ (diskAut (-z) w)) := by
    filter_upwards [closedBall_mem_nhds (0 : ℂ) one_pos] with w hw
    exact hext w (mem_closedBall_zero_iff.mp hw)
  have han : AnalyticOnNhd ℝ (extension φ) unitDisc :=
    isOpen_ball.analyticOn_iff_analyticOnNhd.mp (extension_analyticOn_disk φ hφb hφc)
  have hEd : HasFDerivAt (extension φ) (fderiv ℝ (extension φ) z) (diskAut (-z) 0) := by
    rw [hA0]
    exact (han z hz).differentiableAt.hasFDerivAt
  have hAd := ((hasDerivAt_diskAut hnz (w := 0) (by simp)).hasFDerivAt).restrictScalars ℝ
  have hBd := ((hasDerivAt_diskAut ha (w := extension φ (diskAut (-z) 0))
    (by rw [hA0, ← hpd]; exact hp.le)).hasFDerivAt).restrictScalars ℝ
  have hcomp := hBd.comp (0 : ℂ) (hEd.comp (0 : ℂ) hAd)
  have hfd : fderiv ℝ (extension φ') 0 v =
      fderiv ℝ (extension φ) z (v * ((1 - star (-z) * -z) / (1 - star (-z) * 0) ^ 2)) *
        ((1 - star (H z) * H z) / (1 - star (H z) * extension φ (diskAut (-z) 0)) ^ 2) := by
    rw [hEq.fderiv_eq, show (fun w => diskAut (H z) (extension φ (diskAut (-z) w))) =
      diskAut (H z) ∘ extension φ ∘ diskAut (-z) from rfl, hcomp.fderiv]
    rfl
  rw [hA0, ← hpd] at hfd
  -- `|A'(0)| = ϖ(z)`, `|B'(p)| = β`, `ϖ(B p) = β ϖ(p)`
  have hvz : 0 < varpi z := by
    show 0 < 1 - ‖z‖ ^ 2
    nlinarith [norm_nonneg z]
  have ha' : (1 - star (-z) * -z) / (1 - star (-z) * 0) ^ 2 = ((varpi z : ℝ) : ℂ) := by
    rw [mul_zero, sub_zero, one_pow, div_one, Complex.star_def, Complex.conj_mul', norm_neg]
    show _ = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ)
    push_cast
    ring
  have hstarH : ‖(1 : ℂ) - star (H z) * H z‖ = 1 - ‖H z‖ ^ 2 := by
    have h : (1 : ℂ) - star (H z) * H z = ((1 - ‖H z‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']
      push_cast
      ring
    rw [h, Complex.norm_real, Real.norm_of_nonneg (by nlinarith [norm_nonneg (H z)])]
  have hQ : ‖1 - star (H z) * p‖ ≠ 0 := norm_ne_zero_iff.mpr (diskAut_denom_ne_zero _ _ ha hp.le)
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = (1 - ‖H z‖ ^ 2) / ‖1 - star (H z) * p‖ ^ 2 := ⟨_, rfl⟩
  have hβ0 : 0 < β := by
    have : 0 < 1 - ‖H z‖ ^ 2 := by nlinarith [norm_nonneg (H z)]
    rw [hβ]
    positivity
  have hvB : varpi (extension φ' 0) = β * varpi p := by
    rw [hE0]
    show 1 - ‖diskAut (H z) p‖ ^ 2 = β * (1 - ‖p‖ ^ 2)
    rw [s07_de_mob_varpi ha hp.le, hβ]
    ring
  have hN : ‖fderiv ℝ (extension φ') 0 v‖ = varpi z * ‖fderiv ℝ (extension φ) z v‖ * β := by
    rw [hfd, norm_mul, ha', mul_comm v, ← Complex.real_smul, map_smul, norm_smul,
      Real.norm_of_nonneg hvz.le, norm_div, norm_pow, hstarH, ← hβ]
  rw [← hpd]
  rw [hN, hvB] at hup hlo
  constructor
  · refine le_of_mul_le_mul_right ?_ hβ0
    linarith
  · refine le_of_mul_le_mul_right ?_ hβ0
    linarith

/-- Theorem 7.5, `thm:DE` (Douady–Earle, `sec07-transfer.tex:253`), in existence form: every
orientation-preserving homeomorphism `h` of `∂𝔻` has an extension `F = E(h)` to a homeomorphism
of `𝔻̄` that is a real-analytic orientation-preserving diffeomorphism of `𝔻`; if `h` admits a
`K₀`-q.c. extension, `F` and `F⁻¹` are `L`-Lipschitz for `d_𝔻` with `L` depending only on
`K₀`. -/
theorem thm_DE (K₀ : ℝ) (hK₀ : 1 ≤ K₀) : ∃ L : ℝ, 1 ≤ L ∧ ∀ h : ℂ → ℂ, IsCircleHomeo h →
    ∃ F : ℂ → ℂ, IsClosedDiskHomeo F ∧ EqOn F h (sphere 0 1) ∧
      AnalyticOnNhd ℝ F unitDisc ∧ (∀ z ∈ unitDisc, 0 < (fderiv ℝ F z).det) ∧
      (AdmitsQCDiskExt h K₀ → IsDiskBiLip F L) := by
  obtain ⟨C, hC, hinf⟩ := s07_de_inf K₀ hK₀
  refine ⟨C, hC, fun h hh => ?_⟩
  obtain ⟨φ, hφb, hφc, hor, hF, hFh, han, hdet⟩ := s07_de_extension hh
  refine ⟨extension φ, hF, hFh, han, hdet, ?_⟩
  rintro ⟨H, hH, hHs, hHb⟩
  have hhφ : ∀ ζ : Circle, h ζ = φ ζ := by
    intro ζ
    have hζ : (ζ : ℂ) ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr (Circle.norm_coe ζ)
    rw [← hFh hζ]
    exact extension_eq_boundary φ ζ
  -- the inverse of `E(φ)` on `𝔻̄` restricts to `𝔻`
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
  exact s07_de_bilip_of_inf hFD hGD hFG hGF (hGc.mono ball_subset_closedBall) hd hdet
    (fun z hz v => (hinf φ hφb hφc hor H h hH hHs hHb hhφ z hz v).1)
    (fun z hz v => (hinf φ hφb hφc hor H h hH hHs hHb hhφ z hz v).2)

/-- The Wirtinger derivative `∂ψ = ½(∂_x ψ - i ∂_y ψ)` of a map `ψ : ℂ → ℂ`. -/
def dzC (ψ : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ ψ z 1 - I * fderiv ℝ ψ z I) / 2

/-- `ψ^* λ = λ(ψ(z)) |∂ψ(z)| dA` on `𝔻`, for `λ = λ(z) dA`. -/
def carlesonPullback (ψ : ℂ → ℂ) (lam : ℂ → ℝ≥0∞) : Measure ℂ :=
  (volume.restrict unitDisc).withDensity fun z => lam (ψ z) * ‖dzC ψ z‖ₑ

/-- T1: infinitesimal bi-Lipschitz bounds at a point of differentiability (the metric
`2|dz|/ϖ(z)`): `ϖ(ψ z)|v| ≤ L ϖ(z)|Dψ(z) v|` and `ϖ(z)|Dψ(z) v| ≤ L ϖ(ψ z)|v|`. -/
theorem s07_tw_inf {ψ : ℂ → ℂ} {L : ℝ} (hψ : MapsTo ψ unitDisc unitDisc) (hL : IsDiskBiLip ψ L)
    {z : ℂ} (hz : z ∈ unitDisc) (hd : DifferentiableAt ℝ ψ z) (v : ℂ) :
    varpi (ψ z) * ‖v‖ ≤ L * varpi z * ‖fderiv ℝ ψ z v‖ ∧
      varpi z * ‖fderiv ℝ ψ z v‖ ≤ L * varpi (ψ z) * ‖v‖ := by
  rcases eq_or_ne v 0 with hv0 | hv0
  · rw [hv0]
    simp
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hvc : Continuous varpi := continuous_const.sub (continuous_norm.pow 2)
  have hvz : 0 < varpi z := by
    have : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    unfold varpi; nlinarith [norm_nonneg z]
  have hvψ : 0 < varpi (ψ z) := by
    have : ‖ψ z‖ < 1 := mem_ball_zero_iff.mp (hψ hz)
    unfold varpi; nlinarith [norm_nonneg (ψ z)]
  -- the line `ε ↦ z + ε v` and its image
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℂ, g = fun ε => z + ε • v := ⟨_, rfl⟩
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hg0 : g 0 = z := by rw [hg]; simp
  have hgD : ∀ᶠ ε in 𝓝[>] (0 : ℝ), g ε ∈ unitDisc ∧ 0 < ε := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), g ε ∈ unitDisc :=
      hgc.continuousAt.preimage_mem_nhds (by rw [hg0]; exact isOpen_ball.mem_nhds hz)
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with ε h1 h2
    exact ⟨h1, h2⟩
  have hgt : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    have h := (hgc.continuousAt (x := 0)).tendsto
    rw [hg0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hψt : Tendsto (fun ε => ψ (g ε)) (𝓝[>] (0 : ℝ)) (𝓝 (ψ z)) :=
    hd.continuousAt.tendsto.comp hgt
  -- the difference quotient
  have hder : HasDerivAt (fun ε => ψ (g ε)) (fderiv ℝ ψ z v) 0 := by
    have h1 : HasDerivAt g v 0 := by
      rw [hg]
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
    have h2 : HasFDerivAt ψ (fderiv ℝ ψ z) (g 0) := by rw [hg0]; exact hd.hasFDerivAt
    exact h2.comp_hasDerivAt 0 h1
  have hslope : Tendsto (fun ε : ℝ => ‖ψ (g ε) - ψ z‖ / ε) (𝓝[>] (0 : ℝ))
      (𝓝 ‖fderiv ℝ ψ z v‖) := by
    have h := (continuous_norm.tendsto _).comp hder.tendsto_slope_zero_right
    refine h.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
    simp only [Function.comp_apply, zero_add, hg0, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hε]
    rw [inv_mul_eq_div]
  have hnz : ∀ ε : ℝ, 0 < ε → ‖z - g ε‖ = ε * ‖v‖ := by
    intro ε hε
    rw [hg]
    show ‖z - (z + ε • v)‖ = ε * ‖v‖
    rw [show z - (z + ε • v) = -(ε • v) by abel, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos hε]
  have hnψ : ∀ ε, ‖ψ z - ψ (g ε)‖ = ‖ψ (g ε) - ψ z‖ := fun ε => norm_sub_rev _ _
  have hden : Tendsto (fun ε => √(varpi z * varpi (g ε))) (𝓝[>] (0 : ℝ)) (𝓝 (varpi z)) := by
    have h := (Real.continuous_sqrt.tendsto _).comp
      (tendsto_const_nhds.mul ((hvc.tendsto z).comp hgt) :
        Tendsto (fun ε => varpi z * varpi (g ε)) _ (𝓝 (varpi z * varpi z)))
    rw [Real.sqrt_mul_self hvz.le] at h
    exact h
  have hden' : Tendsto (fun ε => √(varpi (ψ z) * varpi (ψ (g ε)))) (𝓝[>] (0 : ℝ))
      (𝓝 (varpi (ψ z))) := by
    have h := (Real.continuous_sqrt.tendsto _).comp
      (tendsto_const_nhds.mul ((hvc.tendsto (ψ z)).comp hψt) :
        Tendsto (fun ε => varpi (ψ z) * varpi (ψ (g ε))) _ (𝓝 (varpi (ψ z) * varpi (ψ z))))
    rw [Real.sqrt_mul_self hvψ.le] at h
    exact h
  have hs : Tendsto (fun ε => ‖z - g ε‖ / √(varpi z * varpi (g ε))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun ε => ‖z - g ε‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (continuous_norm.tendsto _).comp (tendsto_const_nhds.sub hgt :
        Tendsto (fun ε => z - g ε) _ (𝓝 (z - z)))
      rw [sub_self, norm_zero] at h
      exact h
    have h := h1.div hden hvz.ne'
    rw [zero_div] at h
    exact h
  have hs' : Tendsto (fun ε => ‖ψ z - ψ (g ε)‖ / √(varpi (ψ z) * varpi (ψ (g ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun ε => ‖ψ z - ψ (g ε)‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (continuous_norm.tendsto _).comp (tendsto_const_nhds.sub hψt :
        Tendsto (fun ε => ψ z - ψ (g ε)) _ (𝓝 (ψ z - ψ z)))
      rw [sub_self, norm_zero] at h
      exact h
    have h := h1.div hden' hvψ.ne'
    rw [zero_div] at h
    exact h
  have hsq : ∀ {f : ℝ → ℝ}, Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0) →
      Tendsto (fun ε => √(1 + f ε ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    intro f hf
    have h := (Real.continuous_sqrt.tendsto _).comp
      ((tendsto_const_nhds.add (hf.pow 2)) : Tendsto (fun ε => 1 + f ε ^ 2) _ (𝓝 (1 + 0 ^ 2)))
    rw [show (1 : ℝ) + 0 ^ 2 = 1 by norm_num, Real.sqrt_one] at h
    exact h
  -- the eventual inequalities from the bi-Lipschitz bounds
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖v‖ / √(varpi z * varpi (g ε)) / √(1 + (‖z - g ε‖ / √(varpi z * varpi (g ε))) ^ 2) ≤
          L * (‖ψ (g ε) - ψ z‖ / ε / √(varpi (ψ z) * varpi (ψ (g ε)))) ∧
        ‖ψ (g ε) - ψ z‖ / ε / √(varpi (ψ z) * varpi (ψ (g ε))) /
            √(1 + (‖ψ z - ψ (g ε)‖ / √(varpi (ψ z) * varpi (ψ (g ε)))) ^ 2) ≤
          L * (‖v‖ / √(varpi z * varpi (g ε))) := by
    filter_upwards [hgD] with ε hε
    obtain ⟨hgε, hε0⟩ := hε
    have hψgε := hψ hgε
    have hA := hnz ε hε0
    obtain ⟨hd1, hd2⟩ := s07_tw_dist_bounds hz hgε
    obtain ⟨hd1', hd2'⟩ := s07_tw_dist_bounds (hψ hz) hψgε
    obtain ⟨hL1, hL2⟩ := hL z hz (g ε) hgε
    have hvε : 0 < varpi (g ε) := by
      have : ‖g ε‖ < 1 := mem_ball_zero_iff.mp hgε
      unfold varpi; nlinarith [norm_nonneg (g ε)]
    have hd0' := s02_diskDist_nonneg (hψ hz) hψgε
    rw [← hnψ ε]
    set r1 := √(varpi z * varpi (g ε)) with hr1d
    set r2 := √(varpi (ψ z) * varpi (ψ (g ε))) with hr2d
    set q1 := √(1 + (‖z - g ε‖ / r1) ^ 2) with hq1d
    set q2 := √(1 + (‖ψ z - ψ (g ε)‖ / r2) ^ 2) with hq2d
    set N := ‖ψ z - ψ (g ε)‖ with hNd
    have hr1 : 0 < r1 := Real.sqrt_pos.mpr (mul_pos hvz hvε)
    have hq1 : 0 < q1 := Real.sqrt_pos.mpr (by positivity)
    have hdpos : 0 < diskDist z (g ε) := by
      refine lt_of_lt_of_le ?_ hd1
      rw [hA]
      exact div_pos (mul_pos two_pos (div_pos (mul_pos hε0 hv) hr1)) hq1
    have hL0 : 0 ≤ L := by
      by_contra hneg
      rw [not_le] at hneg
      nlinarith [hL2]
    have key1 := hd1.trans (hL2.trans (mul_le_mul_of_nonneg_left hd2' hL0))
    have key2 := hd1'.trans (hL1.trans (mul_le_mul_of_nonneg_left hd2 hL0))
    rw [hA] at key1 key2
    have hεN : ε * (N / ε) = N := by field_simp
    have h2ε : 0 < 2 * ε := mul_pos two_pos hε0
    constructor
    · have e1 : 2 * (ε * ‖v‖ / r1) / q1 = 2 * ε * (‖v‖ / r1 / q1) := by ring
      have e2 : L * (2 * (N / r2)) = 2 * ε * (L * (N / ε / r2)) := by
        rw [show 2 * ε * (L * (N / ε / r2)) = L * (2 * (ε * (N / ε) / r2)) by ring, hεN]
      rw [e1, e2] at key1
      exact le_of_mul_le_mul_left key1 h2ε
    · have e3 : 2 * (N / r2) / q2 = 2 * ε * (N / ε / r2 / q2) := by
        rw [show 2 * ε * (N / ε / r2 / q2) = 2 * (ε * (N / ε) / r2) / q2 by ring, hεN]
      have e4 : L * (2 * (ε * ‖v‖ / r1)) = 2 * ε * (L * (‖v‖ / r1)) := by ring
      rw [e3, e4] at key2
      exact le_of_mul_le_mul_left key2 h2ε
  have hlim1L := ((tendsto_const_nhds (x := ‖v‖)).div hden hvz.ne').div (hsq hs) one_ne_zero
  have hlim1R := (tendsto_const_nhds (x := L)).mul (hslope.div hden' hvψ.ne')
  have hlim2L := (hslope.div hden' hvψ.ne').div (hsq hs') one_ne_zero
  have hlim2R := (tendsto_const_nhds (x := L)).mul
    ((tendsto_const_nhds (x := ‖v‖)).div hden hvz.ne')
  have h1 := le_of_tendsto_of_tendsto hlim1L hlim1R (hev.mono fun ε h => h.1)
  have h2 := le_of_tendsto_of_tendsto hlim2L hlim2R (hev.mono fun ε h => h.2)
  rw [div_one, div_le_iff₀ hvz,
    show L * (‖fderiv ℝ ψ z v‖ / varpi (ψ z)) * varpi z =
      L * varpi z * ‖fderiv ℝ ψ z v‖ / varpi (ψ z) by ring, le_div_iff₀ hvψ] at h1
  rw [div_one, div_le_iff₀ hvψ,
    show L * (‖v‖ / varpi z) * varpi (ψ z) = L * varpi (ψ z) * ‖v‖ / varpi z by ring,
    le_div_iff₀ hvz] at h2
  constructor
  · rw [mul_comm (varpi (ψ z)) ‖v‖]
    exact h1
  · rw [mul_comm (varpi z) ‖fderiv ℝ ψ z v‖]
    exact h2

/-- T2: for `D v = a v + b v̄` (`a = (D 1 - i D i)/2`, `det D = |a|² - |b|²`): a lower stretch
bound `m` gives `m |a| ≤ |det D|`, and for `det D ≥ 0` an upper stretch bound `M` gives
`det D ≤ M |a|`. -/
theorem s07_tw_jac (D : ℂ →L[ℝ] ℂ) {m M : ℝ} :
    ((∀ v : ℂ, m * ‖v‖ ≤ ‖D v‖) → m * ‖(D 1 - I * D I) / 2‖ ≤ |D.det|) ∧
      ((∀ v : ℂ, ‖D v‖ ≤ M * ‖v‖) → 0 ≤ D.det → D.det ≤ M * ‖(D 1 - I * D I) / 2‖) := by
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = (D 1 - I * D I) / 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℂ, b = (D 1 + I * D I) / 2 := ⟨_, rfl⟩
  have hdec : ∀ v, D v = a * v + b * conj v := fun v => by rw [ha, hb]; exact s07_tw_jac_decomp D v
  have hdet : D.det = Complex.normSq a - Complex.normSq b := by rw [ha, hb]; exact s07_tw_jac_det D
  rw [← ha]
  constructor
  · intro hm
    rcases lt_or_ge m 0 with hm0 | hm0
    · exact (mul_nonpos_of_nonpos_of_nonneg hm0.le (norm_nonneg a)).trans (abs_nonneg _)
    -- `D (ā w - b w̄) = det D · w`
    have hadj : ∀ w : ℂ, D (conj a * w - b * conj w) = (D.det : ℂ) * w := by
      intro w
      rw [hdec, hdet, map_sub, map_mul, map_mul, Complex.conj_conj, Complex.conj_conj]
      push_cast
      rw [← Complex.mul_conj a, ← Complex.mul_conj b]
      ring
    -- one of `w = 1, i` has `|ā w - b w̄| ≥ |a|`
    have hw : ∃ w : ℂ, ‖w‖ = 1 ∧ ‖a‖ ≤ ‖conj a * w - b * conj w‖ := by
      have h1 : conj a * 1 - b * conj 1 = conj a - b := by rw [map_one]; ring
      have h2 : conj a * I - b * conj I = I * (conj a + b) := by rw [Complex.conj_I]; ring
      have htri : 2 * ‖a‖ ≤ ‖conj a - b‖ + ‖conj a + b‖ := by
        have := norm_add_le (conj a - b) (conj a + b)
        rw [show conj a - b + (conj a + b) = 2 * conj a by ring, norm_mul, Complex.norm_conj,
          Complex.norm_two] at this
        linarith
      rcases le_total ‖a‖ ‖conj a - b‖ with h | h
      · exact ⟨1, norm_one, by rw [h1]; exact h⟩
      · refine ⟨I, Complex.norm_I, ?_⟩
        rw [h2, norm_mul, Complex.norm_I, one_mul]
        linarith
    obtain ⟨w, hw1, hwa⟩ := hw
    have h := hm (conj a * w - b * conj w)
    rw [hadj, norm_mul, hw1, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
    exact (mul_le_mul_of_nonneg_left hwa hm0).trans h
  · intro hM hdet0
    have haM : ‖a‖ ≤ M := by
      have h1 := hM 1
      have h2 := hM I
      rw [norm_one, mul_one] at h1
      rw [Complex.norm_I, mul_one] at h2
      rw [ha, norm_div, Complex.norm_two]
      have := norm_sub_le (D 1) (I * D I)
      rw [norm_mul, Complex.norm_I, one_mul] at this
      linarith
    have hna : Complex.normSq a = ‖a‖ * ‖a‖ := by rw [← Complex.norm_mul_self_eq_normSq]
    calc D.det ≤ Complex.normSq a := by rw [hdet]; linarith [Complex.normSq_nonneg b]
      _ = ‖a‖ * ‖a‖ := hna
      _ ≤ M * ‖a‖ := mul_le_mul_of_nonneg_right haM (norm_nonneg a)

/-- T3 (Morse, arbitrary end points): the image under a `(λ, c)`-quasi-isometry of a unit-speed
geodesic `γ`, with end points `ω₊, ω₋` (the end points of the geodesic through `w` in direction
`e₁`), stays within `M_*` of that geodesic: `|⟨P(Q(γ τ)), e₂⟩| ≤ sinh M_*`.  (Generalizes
`s07_mo_qi_normal`; same proof via `s07_mo_qi_step` and a limit as in `s07_mo_qi_limit` with the
end points given directly.) -/
theorem s07_tw_morse (lam c : ℝ) (hlam : 1 ≤ lam) (hc : 0 ≤ c) (Q : ℂ → ℂ)
    (hQ : IsDiskQI Q lam c) (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) (P : ℂ → ℝ × ℂ)
    (hP : ∀ p, P p = ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p))
    (γ : ℝ → ℂ) (hγD : ∀ τ, γ τ ∈ unitDisc) (hγd : ∀ s t, diskDist (γ s) (γ t) = |s - t|)
    {w : ℂ} (hw : w ∈ unitDisc) {e₁ e₂ : ℝ × ℂ}
    (hon : B (P w) (P w) = -1 ∧ B e₁ e₁ = 1 ∧ B e₂ e₂ = 1 ∧ B (P w) e₁ = 0 ∧ B (P w) e₂ = 0 ∧
      B e₁ e₂ = 0)
    (htop : Tendsto (fun τ => Q (γ τ)) atTop
      (𝓝 (((P w).2 + e₁.2) / (((P w).1 + e₁.1 : ℝ) : ℂ))))
    (hbot : Tendsto (fun τ => Q (γ τ)) atBot
      (𝓝 (((P w).2 - e₁.2) / (((P w).1 - e₁.1 : ℝ) : ℂ)))) :
    ∀ τ, |B (P (Q (γ τ))) e₂| ≤ Real.sinh (morseM lam c) := by
  exact s07_mo_qi_normal_gen lam c hlam hc Q hQ B hB P hP γ hγD hγd hon
    (s07_mo_hyp B hB P hP hw).2.1 htop hbot

/-- Helper for `s07_tw_ratio`: `|p - q| ≤ sinh(d_𝔻(p, q)/2)` on `𝔻`. -/
theorem s07_tw_norm_le_sinh {p q : ℂ} (hp : p ∈ unitDisc) (hq : q ∈ unitDisc) :
    ‖p - q‖ ≤ Real.sinh (diskDist p q / 2) := by
  have hsh := s07_tw_sinh_sq hp hq
  have hvp := s07_varpi_pos hp
  have hvq := s07_varpi_pos hq
  have hP1 : varpi p * varpi q ≤ 1 := by
    have h1 : varpi p ≤ 1 := by unfold varpi; nlinarith [norm_nonneg p]
    have h2 : varpi q ≤ 1 := by unfold varpi; nlinarith [norm_nonneg q]
    nlinarith
  have hsh0 : 0 ≤ Real.sinh (diskDist p q / 2) :=
    Real.sinh_nonneg_iff.mpr (by linarith [s02_diskDist_nonneg hp hq])
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hsh0 two_ne_zero]
  have he : ‖p - q‖ ^ 2 = Real.sinh (diskDist p q / 2) ^ 2 * (varpi p * varpi q) := by
    rw [hsh, div_mul_cancel₀ _ (mul_pos hvp hvq).ne']
  rw [he]
  calc Real.sinh (diskDist p q / 2) ^ 2 * (varpi p * varpi q)
      ≤ Real.sinh (diskDist p q / 2) ^ 2 * 1 := mul_le_mul_of_nonneg_left hP1 (sq_nonneg _)
    _ = Real.sinh (diskDist p q / 2) ^ 2 := mul_one _

/-- Helper for `s07_tw_ratio`: a `d_𝔻`-bi-Lipschitz self-map of `𝔻` has `1 ≤ L` and is an
`(L, 0)`-quasi-isometry. -/
theorem s07_tw_bilip_qi {ψ : ℂ → ℂ} {L : ℝ} (hψ : MapsTo ψ unitDisc unitDisc)
    (hL : IsDiskBiLip ψ L) : 1 ≤ L ∧ IsDiskQI ψ L 0 := by
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hh : (1 / 2 : ℂ) ∈ unitDisc := by
    show (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, norm_div, norm_one, Complex.norm_two]
    norm_num
  have hd : 0 < diskDist 0 (1 / 2 : ℂ) := by
    refine lt_of_lt_of_le ?_ (s07_tw_dist_bounds h0 hh).1
    have hn : 0 < ‖(0 : ℂ) - 1 / 2‖ := norm_pos_iff.mpr (by norm_num)
    exact div_pos (mul_pos two_pos (div_pos hn (Real.sqrt_pos.mpr
      (mul_pos (s07_varpi_pos h0) (s07_varpi_pos hh))))) (Real.sqrt_pos.mpr (by positivity))
  have hd' := s02_diskDist_nonneg (hψ h0) (hψ hh)
  obtain ⟨h1, h2⟩ := hL 0 h0 (1 / 2) hh
  have hL0 : 0 < L := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith
  have hL1 : 1 ≤ L := by
    by_contra hneg
    rw [not_le] at hneg
    have hLL : L * L < 1 := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h1 hL0.le
    nlinarith [mul_lt_mul_of_pos_right hLL hd]
  refine ⟨hL1, hψ, fun x hx y hy => ⟨?_, ?_⟩⟩
  · rw [sub_zero, inv_mul_le_iff₀ hL0]
    exact (hL x hx y hy).2
  · rw [add_zero]
    exact (hL x hx y hy).1

/-- Helper for `s07_tw_ratio`: a continuous lift of a circle map is onto `ℝ`. -/
theorem s07_tw_lift_surj {H : ℝ → ℝ} (hHc : Continuous H)
    (hper : ∀ θ, H (θ + 2 * π) = H θ + 2 * π) (y : ℝ) : ∃ θ, H θ = y := by
  have h2π : 0 < 2 * π := by positivity
  obtain ⟨n, hn⟩ := exists_nat_ge (|y - H 0| / (2 * π))
  have hn' : |y - H 0| ≤ n * (2 * π) := by
    rwa [div_le_iff₀ h2π] at hn
  have hp := s07_inv_per_int hper (n : ℤ) 0
  have hm := s07_inv_per_int hper (-(n : ℤ)) 0
  push_cast at hp hm
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hab : 0 + -(n : ℝ) * (2 * π) ≤ 0 + (n : ℝ) * (2 * π) := by nlinarith
  have hy : y ∈ Icc (H (0 + -(n : ℝ) * (2 * π))) (H (0 + (n : ℝ) * (2 * π))) := by
    rw [hp, hm]
    constructor <;> linarith [abs_le.mp hn']
  obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc hab hHc.continuousOn hy
  exact ⟨θ, hθ⟩

/-- Helper for `s07_tw_ratio`: `cos β = 2r/(1 + r²)`, `sin β = (1 - r²)/(1 + r²)` for
`β = 2 arctan((1 - r)/(1 + r))`. -/
theorem s07_tw_beta_cs {r : ℝ} (hr : -1 < r) :
    Real.cos (2 * Real.arctan ((1 - r) / (1 + r))) = 2 * r / (1 + r ^ 2) ∧
      Real.sin (2 * Real.arctan ((1 - r) / (1 + r))) = (1 - r ^ 2) / (1 + r ^ 2) := by
  have h1 : 0 < 1 + r := by linarith
  have h1' : 1 + r ≠ 0 := h1.ne'
  have h2 : 1 + r ^ 2 ≠ 0 := by positivity
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (1 - r) / (1 + r) := ⟨_, rfl⟩
  rw [← hy]
  have hq : 0 < 1 + y ^ 2 := by positivity
  have hy2 : 1 + y ^ 2 = 2 * (1 + r ^ 2) / (1 + r) ^ 2 := by
    rw [hy]
    field_simp
    ring
  have hc : Real.cos (Real.arctan y) ^ 2 = 1 / (1 + y ^ 2) := by
    rw [Real.cos_arctan, div_pow, one_pow, Real.sq_sqrt hq.le]
  have hsc : Real.sin (Real.arctan y) * Real.cos (Real.arctan y) = y / (1 + y ^ 2) := by
    rw [Real.sin_arctan, Real.cos_arctan, div_mul_div_comm, mul_one, Real.mul_self_sqrt hq.le]
  constructor
  · rw [Real.cos_two_mul, hc, hy2]
    field_simp
    ring
  · rw [Real.sin_two_mul, mul_assoc, hsc, hy2, hy]
    field_simp
    ring

/-- Helper for `s07_tw_ratio`: the hyperboloid frame at `w = r e^{it}` adapted to the geodesic
through `w` orthogonal to the radius (`e₁ = (0, i e^{it})`), whose end points are
`e^{i(t ± β)}`, `β = 2 arctan((1 - r)/(1 + r))`; `B(P p, e₁) = 2 Im(p e^{-it})/(1 - |p|²)`. -/
theorem s07_tw_frame (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) (P : ℂ → ℝ × ℂ)
    (hP : ∀ p, P p = ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p))
    {r t : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {w : ℂ} (hw : w = (r : ℂ) * exp (t * I))
    {e₁ e₂ : ℝ × ℂ} (he₁ : e₁ = (0, I * exp (t * I)))
    (he₂ : e₂ = (2 * r / (1 - r ^ 2), (((1 + r ^ 2) / (1 - r ^ 2) : ℝ) : ℂ) * exp (t * I))) :
    w ∈ unitDisc ∧ ‖w‖ = r ∧
      (B (P w) (P w) = -1 ∧ B e₁ e₁ = 1 ∧ B e₂ e₂ = 1 ∧ B (P w) e₁ = 0 ∧ B (P w) e₂ = 0 ∧
        B e₁ e₂ = 0) ∧
      ((P w).2 + e₁.2) / (((P w).1 + e₁.1 : ℝ) : ℂ) =
        exp ((t + 2 * Real.arctan ((1 - r) / (1 + r)) : ℝ) * I) ∧
      ((P w).2 - e₁.2) / (((P w).1 - e₁.1 : ℝ) : ℂ) =
        exp ((t - 2 * Real.arctan ((1 - r) / (1 + r)) : ℝ) * I) ∧
      ∀ p, B (P p) e₁ = 2 / (1 - ‖p‖ ^ 2) * (p * conj (exp (t * I))).im := by
  obtain ⟨E, hEd⟩ : ∃ E : ℂ, E = exp (t * I) := ⟨_, rfl⟩
  rw [← hEd] at hw he₁ he₂ ⊢
  have hE1 : ‖E‖ = 1 := by rw [hEd]; exact Complex.norm_exp_ofReal_mul_I t
  have hEc : E * conj E = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hE1]
    norm_num
  have key : ∀ a b : ℂ, a * E * conj (b * E) = a * conj b := by
    intro a b
    rw [map_mul]
    linear_combination (a * conj b) * hEc
  have hwn : ‖w‖ = r := by
    rw [hw, norm_mul, hE1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hwD : w ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hwn]; exact hr1)
  have hD : 0 < 1 - r ^ 2 := by nlinarith
  have hDc : (1 - (r : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hD.ne'
  have hSc : (1 + (r : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < 1 + r ^ 2).ne'
  have hPw : P w = ((1 + r ^ 2) / (1 - r ^ 2), ((2 * r / (1 - r ^ 2) : ℝ) : ℂ) * E) := by
    rw [hP, hwn, hw]
    congr 1
    push_cast
    ring
  obtain ⟨hcos, hsin⟩ := s07_tw_beta_cs (by linarith : -1 < r)
  refine ⟨hwD, hwn, ⟨(s07_mo_hyp B hB P hP hwD).1, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hB, he₁]
    dsimp only
    rw [key, Complex.conj_I]
    simp
  · rw [hB, he₂]
    dsimp only
    rw [key, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    field_simp
    ring
  · rw [hB, hPw, he₁]
    dsimp only
    rw [key, Complex.conj_I, Complex.re_ofReal_mul]
    simp
  · rw [hB, hPw, he₂]
    dsimp only
    rw [key, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  · rw [hB, he₁, he₂]
    dsimp only
    rw [key, Complex.conj_ofReal, mul_comm I, Complex.re_ofReal_mul]
    simp
  · rw [hPw, he₁]
    dsimp only
    rw [show (((t + 2 * Real.arctan ((1 - r) / (1 + r)) : ℝ) : ℂ) * I) =
        t * I + ((2 * Real.arctan ((1 - r) / (1 + r)) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_add, ← hEd, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      hcos, hsin]
    have hxA : 2 * r / (1 - r ^ 2) / ((1 + r ^ 2) / (1 - r ^ 2) + 0) = 2 * r / (1 + r ^ 2) := by
      rw [add_zero]
      field_simp
    have h1A : 1 / ((1 + r ^ 2) / (1 - r ^ 2) + 0) = (1 - r ^ 2) / (1 + r ^ 2) := by
      rw [add_zero]
      field_simp
    rw [← hxA, ← h1A]
    push_cast
    ring
  · rw [hPw, he₁]
    dsimp only
    rw [show (((t - 2 * Real.arctan ((1 - r) / (1 + r)) : ℝ) : ℂ) * I) =
        t * I + ((-(2 * Real.arctan ((1 - r) / (1 + r))) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_add, ← hEd, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg, hcos, hsin]
    have hxA : 2 * r / (1 - r ^ 2) / ((1 + r ^ 2) / (1 - r ^ 2) - 0) = 2 * r / (1 + r ^ 2) := by
      rw [sub_zero]
      field_simp
    have h1A : 1 / ((1 + r ^ 2) / (1 - r ^ 2) - 0) = (1 - r ^ 2) / (1 + r ^ 2) := by
      rw [sub_zero]
      field_simp
    rw [← hxA, ← h1A]
    push_cast
    ring
  · intro p
    rw [hB, hP p, he₁]
    dsimp only
    simp only [map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.conj_re, Complex.conj_im]
    ring

/-- Helper for `s07_tw_ratio`: `ϖ(p)(1 + P(p)₀) = 2`. -/
theorem s07_tw_varpi_P (P : ℂ → ℝ × ℂ)
    (hP : ∀ p, P p = ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p))
    {p : ℂ} (hp : p ∈ unitDisc) : varpi p * (1 + (P p).1) = 2 := by
  have hD : 1 - ‖p‖ ^ 2 ≠ 0 := (s07_varpi_pos hp).ne'
  rw [hP]
  unfold varpi
  dsimp only
  field_simp
  ring

/-- Helper for `s07_tw_ratio`: `ϖ(x) ≤ 2 cosh d_𝔻(x, y) ϖ(y)`. -/
theorem s07_tw_varpi_cmp {x y : ℂ} (hx : x ∈ unitDisc) (hy : y ∈ unitDisc) :
    varpi x ≤ 2 * Real.cosh (diskDist x y) * varpi y := by
  have hvx := s07_varpi_pos hx
  have hvy := s07_varpi_pos hy
  have hn := norm_nonneg x
  have hm := norm_nonneg y
  have hn1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
  have hm1 : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
  have hδ : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
  have key : varpi x ^ 2 ≤ 2 * varpi x * varpi y + 4 * ‖x - y‖ ^ 2 := by
    unfold varpi
    rcases le_total ‖y‖ ‖x‖ with h | h
    · have h' : 1 - ‖x‖ ^ 2 ≤ 1 - ‖y‖ ^ 2 := by nlinarith
      have h0 : 0 ≤ 1 - ‖x‖ ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h' h0, sq_nonneg ‖x - y‖, sq_nonneg (1 - ‖x‖ ^ 2)]
    · have hd : ‖y‖ - ‖x‖ ≤ ‖x - y‖ := by
        have := neg_abs_le (‖x‖ - ‖y‖)
        linarith
      have hd0 : 0 ≤ ‖y‖ - ‖x‖ := by linarith
      have hδ2 : (‖y‖ - ‖x‖) ^ 2 ≤ ‖x - y‖ ^ 2 := pow_le_pow_left₀ hd0 hd 2
      have hs : (‖y‖ + ‖x‖) ^ 2 ≤ 4 := by nlinarith
      have hmn : (‖y‖ - ‖x‖) ^ 2 * (‖y‖ + ‖x‖) ^ 2 ≤ (‖y‖ - ‖x‖) ^ 2 * 4 :=
        mul_le_mul_of_nonneg_left hs (sq_nonneg _)
      nlinarith [sq_nonneg (1 - ‖y‖ ^ 2)]
  have hc := s07_mo_cosh_dist hx hy
  unfold diskCoshDist at hc
  change Real.cosh (diskDist x y) = 1 + 2 * ‖x - y‖ ^ 2 / (varpi x * varpi y) at hc
  rw [hc]
  have he : 2 * (1 + 2 * ‖x - y‖ ^ 2 / (varpi x * varpi y)) * varpi y =
      (2 * varpi x * varpi y + 4 * ‖x - y‖ ^ 2) / varpi x := by
    field_simp
    ring
  rw [he, le_div_iff₀ hvx]
  nlinarith [key]

/-- Helper for `s07_tw_ratio`: `0 < tan x ≤ 2x` for `0 < x ≤ 1/4`. -/
theorem s07_tw_tan_le {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1 / 4) :
    0 < Real.tan x ∧ Real.tan x ≤ 2 * x := by
  have hπ := Real.pi_gt_three
  have hc : 1 / 2 ≤ Real.cos x := by
    have := Real.one_sub_sq_div_two_le_cos (x := x)
    nlinarith
  refine ⟨Real.tan_pos_of_pos_of_lt_pi_div_two h0 (by linarith), ?_⟩
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ (by linarith)]
  nlinarith [Real.sin_le h0.le]

/-- Helper for `s07_tw_ratio`: for a short arc `[a, b]` (`b - a < 1`) there is a unit-speed geodesic
from `e^{ia}` to `e^{ib}` on which `ϖ ≤ 2(b - a)` (its point closest to `0` is
`r' e^{i(a + b)/2}` with `(1 - r')/(1 + r') = tan((b - a)/4)`). -/
theorem s07_tw_src_geod {a b : ℝ} (hab : a < b) (hba : b - a < 1) :
    ∃ γ : ℝ → ℂ, (∀ τ, γ τ ∈ unitDisc) ∧ (∀ s τ, diskDist (γ s) (γ τ) = |s - τ|) ∧
      Tendsto γ atTop (𝓝 (exp (b * I))) ∧ Tendsto γ atBot (𝓝 (exp (a * I))) ∧
      ∀ τ, varpi (γ τ) ≤ 2 * (b - a) := by
  obtain ⟨B, hBd⟩ : ∃ B : ℝ × ℂ → ℝ × ℂ → ℝ,
      B = fun X Y => -X.1 * Y.1 + (X.2 * conj Y.2).re := ⟨_, rfl⟩
  have hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re := fun X Y => by rw [hBd]
  obtain ⟨P, hPd⟩ : ∃ P : ℂ → ℝ × ℂ,
      P = fun p => ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p) :=
    ⟨_, rfl⟩
  have hP : ∀ p, P p = ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p) :=
    fun p => by rw [hPd]
  obtain ⟨hτ0, hτ1⟩ := s07_tw_tan_le (by linarith : 0 < (b - a) / 4) (by linarith)
  obtain ⟨τ', hτd⟩ : ∃ τ' : ℝ, τ' = Real.tan ((b - a) / 4) := ⟨_, rfl⟩
  rw [← hτd] at hτ0 hτ1
  obtain ⟨r', hr'd⟩ : ∃ r' : ℝ, r' = (1 - τ') / (1 + τ') := ⟨_, rfl⟩
  have hr'0 : 0 ≤ r' := by rw [hr'd]; exact div_nonneg (by linarith) (by linarith)
  have hr'1 : r' < 1 := by rw [hr'd, div_lt_one (by linarith)]; linarith
  have hr'β : 2 * Real.arctan ((1 - r') / (1 + r')) = (b - a) / 2 := by
    have hq : (1 - r') / (1 + r') = τ' := by
      rw [hr'd]
      field_simp
      ring
    have hπ := Real.pi_gt_three
    rw [hq, hτd, Real.arctan_tan (by linarith) (by linarith)]
    ring
  obtain ⟨w', hw'⟩ : ∃ w' : ℂ, w' = (r' : ℂ) * exp (((a + b) / 2 : ℝ) * I) := ⟨_, rfl⟩
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : ℝ × ℂ, f₁ = (0, I * exp (((a + b) / 2 : ℝ) * I)) := ⟨_, rfl⟩
  obtain ⟨f₂, hf₂⟩ : ∃ f₂ : ℝ × ℂ, f₂ = (2 * r' / (1 - r' ^ 2),
      (((1 + r' ^ 2) / (1 - r' ^ 2) : ℝ) : ℂ) * exp (((a + b) / 2 : ℝ) * I)) := ⟨_, rfl⟩
  obtain ⟨hw'D, hw'n, hon', htop', hbot', -⟩ := s07_tw_frame B hB P hP hr'0 hr'1 hw' hf₁ hf₂
  rw [hr'β, show (a + b) / 2 + (b - a) / 2 = b by ring] at htop'
  rw [hr'β, show (a + b) / 2 - (b - a) / 2 = a by ring] at hbot'
  obtain ⟨-, -, -, -, γ, hγD, -, hγe₂, hγd, hγtop, hγbot⟩ :=
    s07_mo_line B hB P hP hon' (s07_mo_hyp B hB P hP hw'D).2.1
  rw [htop'] at hγtop
  rw [hbot'] at hγbot
  refine ⟨γ, hγD, hγd, hγtop, hγbot, fun τ => ?_⟩
  have hqD : γ τ ∈ unitDisc := hγD τ
  have hY : ∀ X : ℝ × ℂ, B X (1, 0) = -X.1 := fun X => by rw [hB]; simp
  have hY' : ∀ X : ℝ × ℂ, B (1, 0) X = -X.1 := fun X => by rw [hB]; simp
  have hp2 := s07_mo_parseval B hB hon' (P (γ τ)) (1, 0)
  rw [hY, hY', hY', hY', hγe₂ τ, hf₁] at hp2
  dsimp only at hp2
  have hge : 1 ≤ -B (P (γ τ)) (P w') := by
    rw [← (s07_mo_hyp B hB P hP hqD).2.2 _ hw'D]
    exact s07_mo_one_le_coshDist hqD hw'D
  have hPw'0 : 0 < (P w').1 := (s07_mo_hyp B hB P hP hw'D).2.1
  have hPq : (P w').1 ≤ (P (γ τ)).1 := by
    have h1 := mul_le_mul_of_nonneg_right hge hPw'0.le
    linarith
  have hvq := s07_tw_varpi_P P hP hqD
  have hvw := s07_tw_varpi_P P hP hw'D
  have hvqw : varpi (γ τ) ≤ varpi w' := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 := mul_lt_mul_of_pos_right hcon (by linarith : 0 < 1 + (P (γ τ)).1)
    have h2 := mul_le_mul_of_nonneg_left (by linarith : 1 + (P w').1 ≤ 1 + (P (γ τ)).1)
      (s07_varpi_pos hw'D).le
    linarith
  have hvw' : varpi w' ≤ 4 * τ' := by
    unfold varpi
    rw [hw'n, hr'd]
    have he : 1 - ((1 - τ') / (1 + τ')) ^ 2 = 4 * τ' / (1 + τ') ^ 2 := by
      field_simp
      ring
    rw [he]
    exact div_le_self (by linarith) (by nlinarith)
  linarith

/-- Helper for `s07_tw_ratio`: if `ψ ∘ γ` (`γ` a unit-speed geodesic) runs from `e^{i(t - β)}` to
`e^{i(t + β)}`, `β = β(w)`, `w = r e^{it}`, then some `ψ(γ τ₀)` lies within `|M_*|` of `w` (Morse,
and the intermediate value theorem on the diameter through `e^{it}`). -/
theorem s07_tw_cross {ψ : ℂ → ℂ} {L : ℝ} (hψ : MapsTo ψ unitDisc unitDisc) (hL : IsDiskBiLip ψ L)
    (hL1 : 1 ≤ L) (hQI : IsDiskQI ψ L 0) {γ : ℝ → ℂ} (hγD : ∀ τ, γ τ ∈ unitDisc)
    (hγd : ∀ s τ, diskDist (γ s) (γ τ) = |s - τ|) {r t : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (htop : Tendsto (fun τ => ψ (γ τ)) atTop
      (𝓝 (exp ((t + 2 * Real.arctan ((1 - r) / (1 + r)) : ℝ) * I))))
    (hbot : Tendsto (fun τ => ψ (γ τ)) atBot
      (𝓝 (exp ((t - 2 * Real.arctan ((1 - r) / (1 + r)) : ℝ) * I)))) :
    ∃ τ₀, diskDist (ψ (γ τ₀)) ((r : ℂ) * exp (t * I)) ≤ |morseM L 0| := by
  obtain ⟨B, hBd⟩ : ∃ B : ℝ × ℂ → ℝ × ℂ → ℝ,
      B = fun X Y => -X.1 * Y.1 + (X.2 * conj Y.2).re := ⟨_, rfl⟩
  have hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re := fun X Y => by rw [hBd]
  obtain ⟨P, hPd⟩ : ∃ P : ℂ → ℝ × ℂ,
      P = fun p => ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p) :=
    ⟨_, rfl⟩
  have hP : ∀ p, P p = ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p) :=
    fun p => by rw [hPd]
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (r : ℂ) * exp (t * I) := ⟨_, rfl⟩
  rw [← hw]
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : ℝ × ℂ, e₁ = (0, I * exp (t * I)) := ⟨_, rfl⟩
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : ℝ × ℂ, e₂ = (2 * r / (1 - r ^ 2),
      (((1 + r ^ 2) / (1 - r ^ 2) : ℝ) : ℂ) * exp (t * I)) := ⟨_, rfl⟩
  obtain ⟨hwD, -, hon, htopw, hbotw, hBe₁⟩ := s07_tw_frame B hB P hP hr0 hr1 hw he₁ he₂
  have hmorse := s07_tw_morse L 0 hL1 le_rfl ψ hQI B hB P hP γ hγD hγd hwD hon
    (by rw [htopw]; exact htop) (by rw [hbotw]; exact hbot)
  obtain ⟨β, hβd⟩ : ∃ β : ℝ, β = 2 * Real.arctan ((1 - r) / (1 + r)) := ⟨_, rfl⟩
  rw [← hβd] at htop hbot
  obtain ⟨-, hsin⟩ := s07_tw_beta_cs (by linarith : -1 < r)
  rw [← hβd] at hsin
  have hsinβ : 0 < Real.sin β := by
    rw [hsin]
    exact div_pos (by nlinarith) (by positivity)
  -- `ψ ∘ γ` is continuous
  have hfc : Continuous fun τ => ψ (γ τ) := by
    rw [continuous_iff_continuousAt]
    intro s
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun τ : ℝ => Real.sinh (L * |τ - s| / 2)) (𝓝 s) (𝓝 0) := by
      have hc : Continuous fun τ : ℝ => Real.sinh (L * |τ - s| / 2) := by fun_prop
      have h1 := hc.tendsto s
      rw [sub_self, abs_zero, mul_zero, zero_div, Real.sinh_zero] at h1
      exact h1
    refine squeeze_zero (fun τ => norm_nonneg _) (fun τ => ?_) hlim
    refine (s07_tw_norm_le_sinh (hψ (hγD τ)) (hψ (hγD s))).trans (Real.sinh_le_sinh.mpr ?_)
    have h1 := (hL _ (hγD τ) _ (hγD s)).1
    rw [hγd] at h1
    linarith
  -- it crosses the diameter through `e^{it}`
  obtain ⟨E, hEd⟩ : ∃ E : ℂ, E = exp (t * I) := ⟨_, rfl⟩
  have hEc : E * conj E = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hEd, Complex.norm_exp_ofReal_mul_I]
    norm_num
  obtain ⟨g, hgd⟩ : ∃ g : ℝ → ℝ, g = fun τ => (ψ (γ τ) * conj E).im := ⟨_, rfl⟩
  have hgc : Continuous g := by
    rw [hgd]
    exact Complex.continuous_im.comp (hfc.mul continuous_const)
  have hgtop : Tendsto g atTop (𝓝 (Real.sin β)) := by
    have h1 := (Complex.continuous_im.tendsto _).comp
      (htop.mul (tendsto_const_nhds (x := conj E)))
    rw [show ((t + β : ℝ) : ℂ) * I = t * I + β * I by push_cast; ring, Complex.exp_add, ← hEd,
      mul_right_comm, hEc, one_mul, Complex.exp_ofReal_mul_I_im] at h1
    rw [hgd]
    exact h1
  have hgbot : Tendsto g atBot (𝓝 (-Real.sin β)) := by
    have h1 := (Complex.continuous_im.tendsto _).comp
      (hbot.mul (tendsto_const_nhds (x := conj E)))
    rw [show ((t - β : ℝ) : ℂ) * I = t * I + ((-β : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_add, ← hEd, mul_right_comm, hEc, one_mul, Complex.exp_ofReal_mul_I_im,
      Real.sin_neg] at h1
    rw [hgd]
    exact h1
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hgtop.eventually (lt_mem_nhds hsinβ))
  obtain ⟨T', hT'⟩ := eventually_atBot.mp
    (hgbot.eventually (gt_mem_nhds (by linarith : -Real.sin β < 0)))
  obtain ⟨τ₀, -, hτ₀⟩ := intermediate_value_Icc (min_le_max (a := T) (b := T'))
    hgc.continuousOn ⟨(hT' _ (min_le_right T T')).le, (hT _ (le_max_left T T')).le⟩
  -- there, the distance to `w` is at most `|M_*|`
  refine ⟨τ₀, ?_⟩
  have hpD : ψ (γ τ₀) ∈ unitDisc := hψ (hγD τ₀)
  have hB1 : B (P (ψ (γ τ₀))) e₁ = 0 := by
    rw [hBe₁, ← hEd]
    have h1 : (ψ (γ τ₀) * conj E).im = 0 := by rw [hgd] at hτ₀; exact hτ₀
    rw [h1, mul_zero]
  have hpars := s07_mo_parseval B hB hon (P (ψ (γ τ₀))) (P (ψ (γ τ₀)))
  obtain ⟨hpp, -, hpcosh⟩ := s07_mo_hyp B hB P hP hpD
  rw [hpp, hB1] at hpars
  have hBw : B (P (ψ (γ τ₀))) (P w) ^ 2 ≤ Real.cosh (morseM L 0) ^ 2 := by
    rw [Real.cosh_sq]
    obtain ⟨hM1, hM2⟩ := abs_le.mp (hmorse τ₀)
    have h3 := sq_le_sq' hM1 hM2
    nlinarith
  have hcd : Real.cosh (diskDist (ψ (γ τ₀)) w) = -B (P (ψ (γ τ₀))) (P w) := by
    rw [s07_mo_cosh_dist hpD hwD, hpcosh _ hwD]
  have h1 : Real.cosh (diskDist (ψ (γ τ₀)) w) ≤ Real.cosh (morseM L 0) := by
    rw [← pow_le_pow_iff_left₀ (Real.cosh_pos _).le (Real.cosh_pos _).le two_ne_zero, hcd,
      neg_sq]
    exact hBw
  rw [Real.cosh_le_cosh, abs_of_nonneg (s02_diskDist_nonneg hpD hwD)] at h1
  exact h1

/-- T3 (ii): `ϖ(z) ≤ C |H⁻¹(I_{ψ z})|`, `I_w = [t - β(w), t + β(w)]` for `w = |w| e^{it}`, `C`
depending only on `L`.  The geodesic `γ_J` over `J = H⁻¹(I_w)` is sent by `ψ` near the geodesic over
`I_w`, which passes through `w` orthogonally to the diameter through `e^{it}`; by the intermediate
value theorem `ψ(γ_J)` meets that diameter within `M_*` of `w`, so `z` is within `L M_*` of `γ_J`,
and `ϖ ≲ |J|` on `γ_J`. -/
theorem s07_tw_ratio (L : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ (ψ h : ℂ → ℂ) (H : ℝ → ℝ), MapsTo ψ unitDisc unitDisc → IsDiskBiLip ψ L →
      HasDiskBoundaryValues ψ h → StrictMono H → Continuous H →
      (∀ θ, H (θ + 2 * π) = H θ + 2 * π) → (∀ θ : ℝ, h (exp (θ * I)) = exp (H θ * I)) →
      ∀ x ∈ unitDisc, ∀ t : ℝ, ψ x = (‖ψ x‖ : ℂ) * exp (t * I) →
        ENNReal.ofReal (varpi x) ≤ ENNReal.ofReal C *
          volume (H ⁻¹' Icc (t - 2 * Real.arctan ((1 - ‖ψ x‖) / (1 + ‖ψ x‖)))
            (t + 2 * Real.arctan ((1 - ‖ψ x‖) / (1 + ‖ψ x‖)))) := by
  refine ⟨4 * Real.cosh (L * |morseM L 0|), by positivity, ?_⟩
  intro ψ h H hψ hL hbd hH hHc hper hl x hx t hxt
  obtain ⟨hL1, hQI⟩ := s07_tw_bilip_qi hψ hL
  have hwD : ψ x ∈ unitDisc := hψ hx
  obtain ⟨r, hrd⟩ : ∃ r : ℝ, r = ‖ψ x‖ := ⟨_, rfl⟩
  rw [← hrd] at hxt ⊢
  have hr0 : 0 ≤ r := hrd ▸ norm_nonneg _
  have hr1 : r < 1 := hrd ▸ mem_ball_zero_iff.mp hwD
  obtain ⟨β, hβd⟩ : ∃ β : ℝ, β = 2 * Real.arctan ((1 - r) / (1 + r)) := ⟨_, rfl⟩
  rw [← hβd]
  have hβ0 : 0 < β := by
    rw [hβd]
    have := Real.arctan_pos.mpr
      (div_pos (by linarith : (0 : ℝ) < 1 - r) (by linarith : (0 : ℝ) < 1 + r))
    linarith
  -- the interval `J = [a, b] = H⁻¹(I_w)`
  obtain ⟨a, ha⟩ := s07_tw_lift_surj hHc hper (t - β)
  obtain ⟨b, hb⟩ := s07_tw_lift_surj hHc hper (t + β)
  have hab : a < b := hH.lt_iff_lt.mp (by rw [ha, hb]; linarith)
  have hpre : H ⁻¹' Icc (t - β) (t + β) = Icc a b := by
    ext θ
    simp only [mem_preimage, mem_Icc]
    rw [← ha, ← hb, hH.le_iff_le, hH.le_iff_le]
  have hC0 : 0 ≤ 4 * Real.cosh (L * |morseM L 0|) := by positivity
  rw [hpre, Real.volume_Icc, ← ENNReal.ofReal_mul hC0]
  apply ENNReal.ofReal_le_ofReal
  have hvx1 : varpi x ≤ 1 := by unfold varpi; nlinarith [norm_nonneg x]
  have hch1 : 1 ≤ Real.cosh (L * |morseM L 0|) := Real.one_le_cosh _
  rcases le_or_gt 1 (b - a) with hba | hba
  · nlinarith
  -- the geodesic over `J`, and its image
  obtain ⟨γ, hγD, hγd, hγtop, hγbot, hγv⟩ := s07_tw_src_geod hab hba
  have hftop : Tendsto (fun τ => ψ (γ τ)) atTop
      (𝓝 (exp ((t + 2 * Real.arctan ((1 - r) / (1 + r)) : ℝ) * I))) := by
    have hζ : exp ((b : ℂ) * I) ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm]
      exact Complex.norm_exp_ofReal_mul_I b
    have h1 := (hbd _ hζ).comp
      (tendsto_nhdsWithin_iff.mpr ⟨hγtop, Eventually.of_forall hγD⟩)
    rw [hl b, hb, hβd] at h1
    exact h1
  have hfbot : Tendsto (fun τ => ψ (γ τ)) atBot
      (𝓝 (exp ((t - 2 * Real.arctan ((1 - r) / (1 + r)) : ℝ) * I))) := by
    have hζ : exp ((a : ℂ) * I) ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm]
      exact Complex.norm_exp_ofReal_mul_I a
    have h1 := (hbd _ hζ).comp
      (tendsto_nhdsWithin_iff.mpr ⟨hγbot, Eventually.of_forall hγD⟩)
    rw [hl a, ha, hβd] at h1
    exact h1
  obtain ⟨τ₀, hdM⟩ := s07_tw_cross hψ hL hL1 hQI hγD hγd hr0 hr1 hftop hfbot
  rw [← hxt] at hdM
  -- `x` is within `L |M_*|` of `γ τ₀`
  have hqD : γ τ₀ ∈ unitDisc := hγD τ₀
  have hLM0 : 0 ≤ L * |morseM L 0| := mul_nonneg (by linarith) (abs_nonneg _)
  have hdx : diskDist x (γ τ₀) ≤ L * |morseM L 0| := by
    rw [s02_diskDist_comm hx hqD]
    exact (hL _ hqD _ hx).2.trans (mul_le_mul_of_nonneg_left hdM (by linarith))
  have hcmp := s07_tw_varpi_cmp hx hqD
  have hch : Real.cosh (diskDist x (γ τ₀)) ≤ Real.cosh (L * |morseM L 0|) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (s02_diskDist_nonneg hx hqD), abs_of_nonneg hLM0]
    exact hdx
  have hvq0 := s07_varpi_pos hqD
  have s1 := mul_le_mul_of_nonneg_right hch hvq0.le
  have s3 := mul_le_mul_of_nonneg_left (hγv τ₀) (Real.cosh_pos (L * |morseM L 0|)).le
  linarith

/-- Helper for `s07_tw_image`: every real number is within `π` of `2π ℤ` (after a shift). -/
theorem s07_tw_round (a : ℝ) : ∃ k : ℤ, |a + 2 * π * k| ≤ π := by
  refine ⟨round (-a / (2 * π)), ?_⟩
  have hπ := Real.pi_pos
  have hπ0 : π ≠ 0 := Real.pi_ne_zero
  have h := abs_sub_round (-a / (2 * π))
  have h2π : 2 * π * (-a / (2 * π)) = -a := by field_simp
  have he : a + 2 * π * ((round (-a / (2 * π)) : ℤ) : ℝ) =
      -(2 * π) * (-a / (2 * π) - round (-a / (2 * π))) := by
    linear_combination h2π
  rw [he, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 * π)
  linarith

/-- Helper for `s07_tw_image`: `|δ| ≤ π` and `1 - cos δ ≤ K u²` give `|δ| ≤ π (1 + K) u`. -/
theorem s07_tw_angle {δ K u : ℝ} (hδ : |δ| ≤ π) (hK : 0 ≤ K) (hu : 0 ≤ u)
    (h : 1 - Real.cos δ ≤ K * u ^ 2) : |δ| ≤ π * (1 + K) * u := by
  have hπ := Real.pi_pos
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = |δ| / 2 := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hy1 : y ≤ π / 2 := by rw [hy]; linarith
  have hsin := Real.mul_le_sin hy0 hy1
  have hcos : Real.cos δ = 1 - 2 * Real.sin y ^ 2 := by
    rw [← Real.cos_abs, show |δ| = 2 * y by rw [hy]; ring, Real.cos_two_mul']
    have := Real.sin_sq_add_cos_sq y
    linarith
  rw [hcos] at h
  have h2 : (2 / π * y) ^ 2 ≤ Real.sin y ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by positivity) hy0) hsin 2
  have h4 : 4 * y ^ 2 ≤ π ^ 2 * (K * u ^ 2 / 2) := by
    have e : 4 * y ^ 2 = π ^ 2 * (2 / π * y) ^ 2 := by
      field_simp
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h5 : K * u ^ 2 / 2 ≤ (1 + K) ^ 2 * u ^ 2 := by
    nlinarith [mul_nonneg (by nlinarith : (0 : ℝ) ≤ (1 + K) ^ 2 - K / 2) (sq_nonneg u)]
  have hb : 0 ≤ π * (1 + K) * u := mul_nonneg (mul_nonneg hπ.le (by linarith)) hu
  apply abs_le_of_sq_le_sq _ hb
  have hd : δ ^ 2 = (2 * y) ^ 2 := by
    rw [← sq_abs δ, show |δ| = 2 * y by rw [hy]; ring]
  rw [hd]
  calc (2 * y) ^ 2 = 4 * y ^ 2 := by ring
    _ ≤ π ^ 2 * (K * u ^ 2 / 2) := h4
    _ ≤ π ^ 2 * ((1 + K) ^ 2 * u ^ 2) := mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = (π * (1 + K) * u) ^ 2 := by ring

/-- Helper for `s07_tw_image`: `|e^{is} - e^{iθ}|² = 2 - 2 cos(s - θ)`. -/
theorem s07_tw_circ_dist (s θ : ℝ) :
    ‖exp (s * I) - exp (θ * I)‖ ^ 2 = 2 - 2 * Real.cos (s - θ) := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.exp_ofReal_mul_I_im, Real.cos_sub]
  linear_combination Real.sin_sq_add_cos_sq s + Real.sin_sq_add_cos_sq θ

/-- Helper for `s07_tw_image`: `0 < β(m) ≤ 2(1 - m)`, `β(m) = 2 arctan((1 - m)/(1 + m))`. -/
theorem s07_tw_beta_le {m : ℝ} (h0 : 0 ≤ m) (h1 : m < 1) :
    0 < 2 * Real.arctan ((1 - m) / (1 + m)) ∧ 2 * Real.arctan ((1 - m) / (1 + m)) ≤ 2 * (1 - m) := by
  have hy : 0 ≤ (1 - m) / (1 + m) := div_nonneg (by linarith) (by linarith)
  have hy1 : (1 - m) / (1 + m) ≤ 1 - m := div_le_self (by linarith) (by linarith)
  have h2 := Real.le_tan (Real.arctan_nonneg.mpr hy) (Real.arctan_lt_pi_div_two _)
  rw [Real.tan_arctan] at h2
  have h3 := Real.arctan_pos.mpr
    (div_pos (by linarith : (0 : ℝ) < 1 - m) (by linarith : (0 : ℝ) < 1 + m))
  constructor <;> linarith

/-- Helper for `s07_tw_image`: for a short arc `[a, b]` (`b - a < 1`) the geodesic over it has its
point closest to `0` at radius `r'` with `β(r') = (b - a)/2` and `1 - r' ≤ b - a`. -/
theorem s07_tw_arc_r {a b : ℝ} (hab : a < b) (hba : b - a < 1) :
    ∃ r' : ℝ, 0 ≤ r' ∧ r' < 1 ∧ 1 - r' ≤ b - a ∧
      2 * Real.arctan ((1 - r') / (1 + r')) = (b - a) / 2 := by
  obtain ⟨hτ0, hτ1⟩ := s07_tw_tan_le (by linarith : 0 < (b - a) / 4) (by linarith)
  obtain ⟨τ', hτd⟩ : ∃ τ' : ℝ, τ' = Real.tan ((b - a) / 4) := ⟨_, rfl⟩
  rw [← hτd] at hτ0 hτ1
  refine ⟨(1 - τ') / (1 + τ'), div_nonneg (by linarith) (by linarith),
    by rw [div_lt_one (by linarith)]; linarith, ?_, ?_⟩
  · have he : 1 - (1 - τ') / (1 + τ') = 2 * τ' / (1 + τ') := by
      field_simp
      ring
    rw [he, div_le_iff₀ (by linarith)]
    nlinarith
  · have hq : (1 - (1 - τ') / (1 + τ')) / (1 + (1 - τ') / (1 + τ')) = τ' := by
      field_simp
      ring
    have hπ := Real.pi_gt_three
    rw [hq, hτd, Real.arctan_tan (by linarith) (by linarith)]
    ring

/-- Helper for `s07_tw_image`: `B(P(n e^{it}), f₂)` for the normal `f₂` of the geodesic through
`r' e^{iμ}` orthogonal to the radius. -/
theorem s07_tw_B_polar (B : ℝ × ℂ → ℝ × ℂ → ℝ)
    (hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re) (P : ℂ → ℝ × ℂ)
    (hP : ∀ p, P p = ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p))
    {n r' t μ : ℝ} (hn0 : 0 ≤ n) (hn1 : n < 1) (hr0 : 0 ≤ r') (hr1 : r' < 1) {f₂ : ℝ × ℂ}
    (hf₂ : f₂ = (2 * r' / (1 - r' ^ 2), (((1 + r' ^ 2) / (1 - r' ^ 2) : ℝ) : ℂ) * exp (μ * I))) :
    B (P ((n : ℂ) * exp (t * I))) f₂ =
      (-2 * r' * (1 + n ^ 2) + 2 * n * (1 + r' ^ 2) * Real.cos (t - μ)) /
        ((1 - n ^ 2) * (1 - r' ^ 2)) := by
  have hn : ‖(n : ℂ) * exp (t * I)‖ = n := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hn0]
  have hD1 : 1 - n ^ 2 ≠ 0 := (by nlinarith : (0 : ℝ) < 1 - n ^ 2).ne'
  have hD2 : 1 - r' ^ 2 ≠ 0 := (by nlinarith : (0 : ℝ) < 1 - r' ^ 2).ne'
  have he : exp (t * I) * conj (exp (μ * I)) = exp (((t - μ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hre : ((((2 / (1 - n ^ 2) : ℝ) : ℂ) * ((n : ℂ) * exp (t * I))) *
      conj ((((1 + r' ^ 2) / (1 - r' ^ 2) : ℝ) : ℂ) * exp (μ * I))).re =
      2 / (1 - n ^ 2) * n * ((1 + r' ^ 2) / (1 - r' ^ 2)) * Real.cos (t - μ) := by
    rw [map_mul, Complex.conj_ofReal,
      show (((2 / (1 - n ^ 2) : ℝ) : ℂ) * ((n : ℂ) * exp (t * I))) *
        ((((1 + r' ^ 2) / (1 - r' ^ 2) : ℝ) : ℂ) * conj (exp (μ * I))) =
        ((2 / (1 - n ^ 2) * n * ((1 + r' ^ 2) / (1 - r' ^ 2)) : ℝ) : ℂ) *
          (exp (t * I) * conj (exp (μ * I))) by push_cast; ring,
      he, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rw [hB, hP, hn, hf₂]
  dsimp only
  rw [hre]
  field_simp

/-- Helper for `s07_tw_image`: from `|B(P(n e^{it}), f₂)| ≤ S` (see `s07_tw_B_polar`):
`1 - n ≤ (1 + 2S)(1 - r')`, and, for `n ≥ 1/2`, `1 - cos(t - μ) ≤ (4 + 4S(1 + 2S))(1 - r')²`. -/
theorem s07_tw_normal_est {n r' S δ : ℝ} (hn0 : 0 ≤ n) (hn1 : n < 1) (hr0 : 0 ≤ r') (hr1 : r' < 1)
    (h : |(-2 * r' * (1 + n ^ 2) + 2 * n * (1 + r' ^ 2) * Real.cos δ) /
      ((1 - n ^ 2) * (1 - r' ^ 2))| ≤ S) :
    1 - n ≤ (1 + 2 * S) * (1 - r') ∧
      (1 / 2 ≤ n → 1 - Real.cos δ ≤ (4 + 4 * S * (1 + 2 * S)) * (1 - r') ^ 2) := by
  have hD : 0 < (1 - n ^ 2) * (1 - r' ^ 2) := mul_pos (by nlinarith) (by nlinarith)
  have hS0 : 0 ≤ S := (abs_nonneg _).trans h
  rw [abs_le, le_div_iff₀ hD, div_le_iff₀ hD] at h
  obtain ⟨hlo, -⟩ := h
  have hc1 := Real.cos_le_one δ
  have hD4 : (1 - n ^ 2) * (1 - r' ^ 2) ≤ 4 * ((1 - n) * (1 - r')) := by
    have e : (1 - n ^ 2) * (1 - r' ^ 2) = ((1 - n) * (1 - r')) * ((1 + n) * (1 + r')) := by ring
    have h0 : 0 ≤ (1 - n) * (1 - r') := mul_nonneg (by linarith) (by linarith)
    have h4 : (1 + n) * (1 + r') ≤ 4 := by nlinarith
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left h4 h0]
  have hSD := mul_le_mul_of_nonneg_left hD4 hS0
  have part1 : 1 - n ≤ (1 + 2 * S) * (1 - r') := by
    rcases le_total r' n with hrn | hrn
    · nlinarith [mul_nonneg hS0 (by linarith : (0 : ℝ) ≤ 1 - r')]
    · have hcb : 2 * n * (1 + r' ^ 2) * Real.cos δ ≤ 2 * n * (1 + r' ^ 2) :=
        mul_le_of_le_one_right (by positivity) hc1
      have hN : 2 * ((r' - n) * (1 - r' * n)) ≤ S * ((1 - n ^ 2) * (1 - r' ^ 2)) := by
        linarith
      have h3 : (r' - n) * (1 - n) ≤ (r' - n) * (1 - r' * n) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
      have h1n : 0 < 1 - n := by linarith
      have h5 : r' - n ≤ 2 * S * (1 - r') := by
        by_contra hcon
        rw [not_le] at hcon
        have := mul_lt_mul_of_pos_left hcon h1n
        linarith
      linarith
  refine ⟨part1, fun hn2 => ?_⟩
  have hc0 : 0 ≤ 1 - Real.cos δ := by linarith
  have hlo' : 2 * n * (1 + r' ^ 2) * (1 - Real.cos δ) ≤
      2 * ((n - r') * (1 - n * r')) + S * ((1 - n ^ 2) * (1 - r' ^ 2)) := by
    linarith
  have hA : 2 * ((n - r') * (1 - n * r')) ≤ 4 * (1 - r') ^ 2 := by
    rcases le_total n r' with hnr | hnr
    · have h0 : 0 ≤ 1 - n * r' := by nlinarith
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r' - n) h0]
    · have h1 : n - r' ≤ 1 - r' := by linarith
      have h2 : 1 - n * r' ≤ 2 * (1 - r') := by
        nlinarith [mul_nonneg hr0 (by linarith : (0 : ℝ) ≤ n - r'), sq_nonneg (1 - r')]
      have h3 : 0 ≤ 1 - n * r' := by nlinarith
      nlinarith [mul_le_mul h1 h2 h3 (by linarith : (0 : ℝ) ≤ 1 - r')]
  have hB2 : S * ((1 - n ^ 2) * (1 - r' ^ 2)) ≤ 4 * S * (1 + 2 * S) * (1 - r') ^ 2 := by
    have h6 := mul_le_mul_of_nonneg_right part1 (by linarith : (0 : ℝ) ≤ 1 - r')
    have h7 := mul_le_mul_of_nonneg_left h6 hS0
    nlinarith [hSD, h7]
  have hm : 1 - Real.cos δ ≤ 2 * n * (1 + r' ^ 2) * (1 - Real.cos δ) :=
    le_mul_of_one_le_left hc0 (by nlinarith)
  nlinarith

/-- T3 (i): `ψ(𝔻 ∩ B(e^{iθ₀}, r))` lies in the box over `[H θ₀ - ρ, H θ₀ + ρ]` (mod `2π`) of
height `ρ`, `ρ = C (H(θ₀ + C r) - H(θ₀ - C r))`, `C` depending only on `L` (the geodesic through
`x` orthogonal to the radius has end points in `arc(θ₀ ± C r)`; its image is within `M_*` of the
geodesic over `H(arc(θ₀ ± C r))`). -/
theorem s07_tw_image (L : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (ψ h : ℂ → ℂ) (H : ℝ → ℝ), MapsTo ψ unitDisc unitDisc → IsDiskBiLip ψ L →
      HasDiskBoundaryValues ψ h → StrictMono H → Continuous H →
      (∀ θ, H (θ + 2 * π) = H θ + 2 * π) → (∀ θ : ℝ, h (exp (θ * I)) = exp (H θ * I)) →
      ∀ θ₀ r : ℝ, 0 < r → ∀ x ∈ unitDisc, ‖x - exp (θ₀ * I)‖ < r → ∀ t : ℝ,
        ψ x = (‖ψ x‖ : ℂ) * exp (t * I) →
        (∃ k : ℤ, |t + 2 * π * k - H θ₀| ≤ C * (H (θ₀ + C * r) - H (θ₀ - C * r))) ∧
          2 * Real.arctan ((1 - ‖ψ x‖) / (1 + ‖ψ x‖)) ≤ C * (H (θ₀ + C * r) - H (θ₀ - C * r)) := by
  obtain ⟨S, hSd⟩ : ∃ S : ℝ, S = |Real.sinh (morseM L 0)| := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hSd]; exact abs_nonneg _
  have hS1 : 0 < 1 + 2 * S := by linarith
  have hS2 : 0 < 2 * (1 + 2 * S) := by linarith
  obtain ⟨K, hKd⟩ : ∃ K : ℝ, K = 4 + 4 * S * (1 + 2 * S) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hKd]
    have := mul_nonneg hS0 hS1.le
    linarith
  have hπ := Real.pi_gt_three
  have hA1 : 0 ≤ 2 * π * (1 + 2 * S) := mul_nonneg (by positivity) hS1.le
  have hA2 : 0 ≤ π * (1 + K) := mul_nonneg Real.pi_pos.le (by linarith)
  have hA3 : 2 * (1 + 2 * S) ≤ 2 * π * (1 + 2 * S) := by
    have := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ π) hS1.le
    linarith
  obtain ⟨C, hCd⟩ : ∃ C : ℝ, C = 2 * π * (1 + 2 * S) + π * (1 + K) + 3 * π + 3 := ⟨_, rfl⟩
  refine ⟨C, by rw [hCd]; linarith, ?_⟩
  intro ψ h H hψ hL hbd hH _hHc _hper hl θ₀ r hr x hx hxr t hxt
  obtain ⟨hL1, hQI⟩ := s07_tw_bilip_qi hψ hL
  have hwD : ψ x ∈ unitDisc := hψ hx
  obtain ⟨n, hnd⟩ : ∃ n : ℝ, n = ‖ψ x‖ := ⟨_, rfl⟩
  rw [← hnd] at hxt ⊢
  have hn0 : 0 ≤ n := hnd ▸ norm_nonneg _
  have hn1 : n < 1 := hnd ▸ mem_ball_zero_iff.mp hwD
  obtain ⟨Δ, hΔd⟩ : ∃ Δ : ℝ, Δ = H (θ₀ + C * r) - H (θ₀ - C * r) := ⟨_, rfl⟩
  rw [← hΔd]
  have hC0 : 0 < C := by rw [hCd]; linarith
  have hCr : 0 < C * r := mul_pos hC0 hr
  have hΔ0 : 0 < Δ := by
    rw [hΔd]
    have := hH (by linarith : θ₀ - C * r < θ₀ + C * r)
    linarith
  obtain ⟨-, hβn⟩ := s07_tw_beta_le hn0 hn1
  rcases le_or_gt (1 / (2 * (1 + 2 * S))) Δ with hbig | hsmall
  · -- `ρ` is large: both conclusions hold with `π`
    have hCΔ : π ≤ C * Δ := by
      rw [div_le_iff₀ hS2] at hbig
      have h2 : 2 * π * (1 + 2 * S) ≤ C := by rw [hCd]; linarith
      have h3 := mul_le_mul_of_nonneg_right h2 hΔ0.le
      have h4 := mul_le_mul_of_nonneg_left hbig Real.pi_pos.le
      linarith
    obtain ⟨k₀, hk₀⟩ := s07_tw_round (t - H θ₀)
    refine ⟨⟨k₀, ?_⟩, ?_⟩
    · rw [show t + 2 * π * k₀ - H θ₀ = t - H θ₀ + 2 * π * k₀ by ring]
      linarith
    · have := Real.arctan_lt_pi_div_two ((1 - n) / (1 + n))
      linarith
  have hΔlt : Δ * (2 * (1 + 2 * S)) < 1 := by rwa [lt_div_iff₀ hS2] at hsmall
  -- polar form `x = |x| e^{is}` with `|s - θ₀| ≤ π`
  obtain ⟨k₁, hk₁⟩ := s07_tw_round (Complex.arg x - θ₀)
  obtain ⟨s, hsd⟩ : ∃ s : ℝ, s = Complex.arg x + 2 * π * k₁ := ⟨_, rfl⟩
  have hxs : x = (‖x‖ : ℂ) * exp (s * I) := by
    rw [hsd]
    push_cast
    rw [show ((Complex.arg x : ℂ) + 2 * (π : ℂ) * (k₁ : ℂ)) * I =
        (Complex.arg x : ℂ) * I + (k₁ : ℂ) * (2 * π * I) by ring, Complex.exp_add,
      Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.norm_mul_exp_arg_mul_I]
  have hsθ : |s - θ₀| ≤ π := by
    rw [hsd, show Complex.arg x + 2 * π * k₁ - θ₀ = Complex.arg x - θ₀ + 2 * π * k₁ by ring]
    exact hk₁
  obtain ⟨m, hmd⟩ : ∃ m : ℝ, m = ‖x‖ := ⟨_, rfl⟩
  rw [← hmd] at hxs
  have hm0 : 0 ≤ m := hmd ▸ norm_nonneg _
  have hm1 : m < 1 := hmd ▸ mem_ball_zero_iff.mp hx
  have hEθ : ‖exp (θ₀ * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ₀
  have hEs : ‖exp (s * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I s
  have hmr : 1 - m < r := by
    have h1 := norm_sub_norm_le (exp (θ₀ * I)) x
    rw [hEθ, norm_sub_rev, ← hmd] at h1
    linarith
  have hes : ‖exp (s * I) - exp (θ₀ * I)‖ < 2 * r := by
    have h1 : ‖exp (s * I) - x‖ = 1 - m := by
      rw [hxs, show exp (s * I) - (m : ℂ) * exp (s * I) = ((1 - m : ℝ) : ℂ) * exp (s * I) by
          push_cast; ring,
        norm_mul, hEs, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have h2 : exp (s * I) - exp (θ₀ * I) = (exp (s * I) - x) + (x - exp (θ₀ * I)) := by ring
    rw [h2]
    have h3 := norm_add_le (exp (s * I) - x) (x - exp (θ₀ * I))
    linarith
  have hsθ' : |s - θ₀| ≤ π * (1 + 2) * r := by
    refine s07_tw_angle hsθ (by norm_num) hr.le ?_
    have h1 := s07_tw_circ_dist s θ₀
    have h3 : ‖exp (s * I) - exp (θ₀ * I)‖ ^ 2 ≤ (2 * r) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hes.le 2
    rw [h1] at h3
    nlinarith
  obtain ⟨βx, hβxd⟩ : ∃ βx : ℝ, βx = 2 * Real.arctan ((1 - m) / (1 + m)) := ⟨_, rfl⟩
  obtain ⟨hβx0, hβx2⟩ := s07_tw_beta_le hm0 hm1
  rw [← hβxd] at hβx0 hβx2
  -- the hyperboloid model
  obtain ⟨B, hBd⟩ : ∃ B : ℝ × ℂ → ℝ × ℂ → ℝ,
      B = fun X Y => -X.1 * Y.1 + (X.2 * conj Y.2).re := ⟨_, rfl⟩
  have hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re := fun X Y => by rw [hBd]
  obtain ⟨P, hPd⟩ : ∃ P : ℂ → ℝ × ℂ,
      P = fun p => ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p) :=
    ⟨_, rfl⟩
  have hP : ∀ p, P p = ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p) :=
    fun p => by rw [hPd]
  -- the source geodesic through `x`, orthogonal to the radius
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : ℝ × ℂ, e₁ = (0, I * exp (s * I)) := ⟨_, rfl⟩
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : ℝ × ℂ, e₂ = (2 * m / (1 - m ^ 2),
      (((1 + m ^ 2) / (1 - m ^ 2) : ℝ) : ℂ) * exp (s * I)) := ⟨_, rfl⟩
  obtain ⟨-, -, hon, htopx, hbotx, -⟩ := s07_tw_frame B hB P hP hm0 hm1 hxs he₁ he₂
  rw [← hβxd] at htopx hbotx
  obtain ⟨-, -, -, -, γ, hγD, hγ0, -, hγd, hγtop, hγbot⟩ :=
    s07_mo_line B hB P hP hon (s07_mo_hyp B hB P hP hx).2.1
  rw [htopx] at hγtop
  rw [hbotx] at hγbot
  have hγx : γ 0 = x := s07_mo_P_inj P hP (hγD 0) hx hγ0
  -- the target arc `[a', b'] = H([s - βx, s + βx]) ⊆ [H(θ₀ - C r), H(θ₀ + C r)]`
  obtain ⟨a', ha'⟩ : ∃ a' : ℝ, a' = H (s - βx) := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : ℝ, b' = H (s + βx) := ⟨_, rfl⟩
  have hab' : a' < b' := by rw [ha', hb']; exact hH (by linarith)
  have hCge : (3 * π + 2) * r ≤ C * r :=
    mul_le_mul_of_nonneg_right (by rw [hCd]; linarith) hr.le
  obtain ⟨hs1, hs2⟩ := abs_le.mp hsθ'
  have hlo : H (θ₀ - C * r) ≤ a' := by rw [ha']; exact hH.monotone (by linarith)
  have hhi : b' ≤ H (θ₀ + C * r) := by rw [hb']; exact hH.monotone (by linarith)
  have hθlo : H (θ₀ - C * r) ≤ H θ₀ := hH.monotone (by linarith)
  have hθhi : H θ₀ ≤ H (θ₀ + C * r) := hH.monotone (by linarith)
  have hba' : b' - a' ≤ Δ := by rw [hΔd]; linarith
  have hΔ1 : Δ < 1 / 2 := by
    have := mul_le_mul_of_nonneg_left (by linarith : (2 : ℝ) ≤ 2 * (1 + 2 * S)) hΔ0.le
    linarith
  obtain ⟨r', hr'0, hr'1, hu, hr'β⟩ := s07_tw_arc_r hab' (by linarith)
  obtain ⟨μ, hμd⟩ : ∃ μ : ℝ, μ = (a' + b') / 2 := ⟨_, rfl⟩
  obtain ⟨w', hw'⟩ : ∃ w' : ℂ, w' = (r' : ℂ) * exp (μ * I) := ⟨_, rfl⟩
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : ℝ × ℂ, f₁ = (0, I * exp (μ * I)) := ⟨_, rfl⟩
  obtain ⟨f₂, hf₂⟩ : ∃ f₂ : ℝ × ℂ, f₂ = (2 * r' / (1 - r' ^ 2),
      (((1 + r' ^ 2) / (1 - r' ^ 2) : ℝ) : ℂ) * exp (μ * I)) := ⟨_, rfl⟩
  obtain ⟨hw'D, -, hon', htop', hbot', -⟩ := s07_tw_frame B hB P hP hr'0 hr'1 hw' hf₁ hf₂
  rw [hr'β, show μ + (b' - a') / 2 = b' by rw [hμd]; ring] at htop'
  rw [hr'β, show μ - (b' - a') / 2 = a' by rw [hμd]; ring] at hbot'
  have hftop : Tendsto (fun τ => ψ (γ τ)) atTop
      (𝓝 (((P w').2 + f₁.2) / (((P w').1 + f₁.1 : ℝ) : ℂ))) := by
    have hζ : exp (((s + βx : ℝ) : ℂ) * I) ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm]
      exact Complex.norm_exp_ofReal_mul_I _
    have h1 := (hbd _ hζ).comp
      (tendsto_nhdsWithin_iff.mpr ⟨hγtop, Eventually.of_forall hγD⟩)
    rw [hl (s + βx), ← hb'] at h1
    rw [htop']
    exact h1
  have hfbot : Tendsto (fun τ => ψ (γ τ)) atBot
      (𝓝 (((P w').2 - f₁.2) / (((P w').1 - f₁.1 : ℝ) : ℂ))) := by
    have hζ : exp (((s - βx : ℝ) : ℂ) * I) ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm]
      exact Complex.norm_exp_ofReal_mul_I _
    have h1 := (hbd _ hζ).comp
      (tendsto_nhdsWithin_iff.mpr ⟨hγbot, Eventually.of_forall hγD⟩)
    rw [hl (s - βx), ← ha'] at h1
    rw [hbot']
    exact h1
  -- Morse at `τ = 0`: `ψ x` is close to the geodesic over `[a', b']`
  have hm := s07_tw_morse L 0 hL1 le_rfl ψ hQI B hB P hP γ hγD hγd hw'D hon' hftop hfbot 0
  rw [hγx, hxt, s07_tw_B_polar B hB P hP hn0 hn1 hr'0 hr'1 hf₂] at hm
  have hmS := hm.trans (show Real.sinh (morseM L 0) ≤ S by rw [hSd]; exact le_abs_self _)
  obtain ⟨hne, hce⟩ := s07_tw_normal_est hn0 hn1 hr'0 hr'1 hmS
  have hu' : 1 - r' ≤ Δ := hu.trans hba'
  have hnΔ := mul_le_mul_of_nonneg_left hu' hS1.le
  have hn2 : 1 / 2 ≤ n := by linarith
  have hc := hce hn2
  rw [← hKd] at hc
  obtain ⟨k₂, hk₂⟩ := s07_tw_round (t - μ)
  have hδ := s07_tw_angle hk₂ hK0 (by linarith : (0 : ℝ) ≤ 1 - r')
    (by rw [show t - μ + 2 * π * k₂ = (t - μ) + k₂ * (2 * π) by ring,
      Real.cos_add_int_mul_two_pi]; exact hc)
  refine ⟨⟨k₂, ?_⟩, ?_⟩
  · have h1 := mul_le_mul_of_nonneg_left hu' hA2
    have h2 : (π * (1 + K) + 1) * Δ ≤ C * Δ :=
      mul_le_mul_of_nonneg_right (by rw [hCd]; linarith) hΔ0.le
    obtain ⟨hδ1, hδ2⟩ := abs_le.mp hδ
    have hμ1 : a' ≤ μ := by rw [hμd]; linarith
    have hμ2 : μ ≤ b' := by rw [hμd]; linarith
    rw [abs_le]
    constructor <;> linarith
  · have h3 : 2 * (1 + 2 * S) * Δ ≤ C * Δ :=
      mul_le_mul_of_nonneg_right (by rw [hCd]; linarith) hΔ0.le
    linarith

/-- Helper for `s07_tw_cov`: a `d_𝔻`-bi-Lipschitz self-map of `𝔻` is Euclidean-Lipschitz on each
`B(0, R)`, `R < 1` (`|Δψ| ≤ sinh(d'/2) ≤ (d'/2) cosh(d'/2)`, `d' ≤ |L| d`). -/
theorem s07_tw_lip {ψ : ℂ → ℂ} {L : ℝ} (hψ : MapsTo ψ unitDisc unitDisc) (hL : IsDiskBiLip ψ L)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : R < 1) : ∃ C : ℝ≥0, LipschitzOnWith C ψ (ball 0 R) := by
  have h1R : 0 < 1 - R ^ 2 := by nlinarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 4 * |L| / (1 - R ^ 2) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = |L| * Real.cosh (B / 2) / (1 - R ^ 2) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact div_nonneg (mul_nonneg (abs_nonneg L) (Real.cosh_pos _).le) h1R.le
  refine ⟨Real.toNNReal C, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  rw [Real.coe_toNNReal _ hC0, dist_eq_norm, dist_eq_norm]
  have hxR : ‖x‖ < R := mem_ball_zero_iff.mp hx
  have hyR : ‖y‖ < R := mem_ball_zero_iff.mp hy
  have hxD : x ∈ unitDisc := mem_ball_zero_iff.mpr (hxR.trans hR)
  have hyD : y ∈ unitDisc := mem_ball_zero_iff.mpr (hyR.trans hR)
  have hvx : 1 - R ^ 2 ≤ varpi x := by unfold varpi; nlinarith [norm_nonneg x]
  have hvy : 1 - R ^ 2 ≤ varpi y := by unfold varpi; nlinarith [norm_nonneg y]
  have hsq : 1 - R ^ 2 ≤ √(varpi x * varpi y) := by
    rw [← Real.sqrt_sq h1R.le]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hd := (s07_tw_dist_bounds hxD hyD).2
  have hd0 := s02_diskDist_nonneg hxD hyD
  have hd0' := s02_diskDist_nonneg (hψ hxD) (hψ hyD)
  have hdx : diskDist x y ≤ 2 * (‖x - y‖ / (1 - R ^ 2)) :=
    hd.trans (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (norm_nonneg _) h1R hsq) zero_le_two)
  have hxy2 : ‖x - y‖ ≤ 2 := by
    have := norm_sub_le x y
    linarith
  have hd' : diskDist (ψ x) (ψ y) ≤ |L| * (2 * (‖x - y‖ / (1 - R ^ 2))) :=
    (hL x hxD y hyD).1.trans ((mul_le_mul_of_nonneg_right (le_abs_self L) hd0).trans
      (mul_le_mul_of_nonneg_left hdx (abs_nonneg L)))
  have hdB : diskDist (ψ x) (ψ y) ≤ B := by
    refine hd'.trans ?_
    rw [hB, show 4 * |L| / (1 - R ^ 2) = |L| * (2 * (2 / (1 - R ^ 2))) by ring]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ zero_le_two) (abs_nonneg L)
    exact div_le_div_of_nonneg_right hxy2 h1R.le
  -- `|Δψ| ≤ sinh(d'/2)`
  have hsh := s07_tw_sinh_sq (hψ hxD) (hψ hyD)
  have hvψx : 0 < varpi (ψ x) := by
    have : ‖ψ x‖ < 1 := mem_ball_zero_iff.mp (hψ hxD)
    unfold varpi; nlinarith [norm_nonneg (ψ x)]
  have hvψy : 0 < varpi (ψ y) := by
    have : ‖ψ y‖ < 1 := mem_ball_zero_iff.mp (hψ hyD)
    unfold varpi; nlinarith [norm_nonneg (ψ y)]
  have hP1 : varpi (ψ x) * varpi (ψ y) ≤ 1 := by
    have h1 : varpi (ψ x) ≤ 1 := by unfold varpi; nlinarith [norm_nonneg (ψ x)]
    have h2 : varpi (ψ y) ≤ 1 := by unfold varpi; nlinarith [norm_nonneg (ψ y)]
    nlinarith
  have hsh0 : 0 ≤ Real.sinh (diskDist (ψ x) (ψ y) / 2) :=
    Real.sinh_nonneg_iff.mpr (by linarith)
  have hΔ : ‖ψ x - ψ y‖ ≤ Real.sinh (diskDist (ψ x) (ψ y) / 2) := by
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hsh0 two_ne_zero]
    have he : ‖ψ x - ψ y‖ ^ 2 =
        Real.sinh (diskDist (ψ x) (ψ y) / 2) ^ 2 * (varpi (ψ x) * varpi (ψ y)) := by
      rw [hsh, div_mul_cancel₀ _ (mul_pos hvψx hvψy).ne']
    rw [he]
    calc Real.sinh (diskDist (ψ x) (ψ y) / 2) ^ 2 * (varpi (ψ x) * varpi (ψ y))
        ≤ Real.sinh (diskDist (ψ x) (ψ y) / 2) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hP1 (sq_nonneg _)
      _ = _ := mul_one _
  have hch : Real.cosh (diskDist (ψ x) (ψ y) / 2) ≤ Real.cosh (B / 2) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  calc ‖ψ x - ψ y‖ ≤ Real.sinh (diskDist (ψ x) (ψ y) / 2) := hΔ
    _ ≤ diskDist (ψ x) (ψ y) / 2 * Real.cosh (diskDist (ψ x) (ψ y) / 2) :=
        s07_mo_sinh_le (by linarith)
    _ ≤ diskDist (ψ x) (ψ y) / 2 * Real.cosh (B / 2) :=
        mul_le_mul_of_nonneg_left hch (by linarith)
    _ ≤ |L| * (2 * (‖x - y‖ / (1 - R ^ 2))) / 2 * Real.cosh (B / 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.cosh_pos _).le
    _ = C * ‖x - y‖ := by rw [hC]; ring

/-- Change of variables for the pull-back: if `|∂ψ| ≤ Φ(ψ) |det Dψ|` at the points of
differentiability in `S`, then `∫_S λ(ψ)|∂ψ| ≤ ∫_{ψ(S)} λ Φ` (Rademacher on the sub-disks, where
`ψ` is Euclidean-Lipschitz, and `lintegral_image_eq_lintegral_abs_det_fderiv_mul`). -/
theorem s07_tw_cov {ψ : ℂ → ℂ} {L : ℝ} (hψ : MapsTo ψ unitDisc unitDisc) (hL : IsDiskBiLip ψ L)
    {S : Set ℂ} (hS : MeasurableSet S) (hSD : S ⊆ unitDisc) (lam Φ : ℂ → ℝ≥0∞)
    (hΦ : ∀ z ∈ S, DifferentiableAt ℝ ψ z →
      ‖dzC ψ z‖ₑ ≤ Φ (ψ z) * ENNReal.ofReal |(fderiv ℝ ψ z).det|) :
    ∫⁻ z in S, lam (ψ z) * ‖dzC ψ z‖ₑ ≤ ∫⁻ w in ψ '' S, lam w * Φ w := by
  -- `ψ` is injective on `𝔻`
  have hinj : InjOn ψ unitDisc := by
    intro x hx y hy hxy
    have h1 := (hL x hx y hy).2
    have h2 := (s07_tw_dist_bounds (hψ hx) (hψ hy)).2
    have h3 := (s07_tw_dist_bounds hx hy).1
    rw [hxy, sub_self, norm_zero, zero_div, mul_zero] at h2
    have h0 := s02_diskDist_nonneg (hψ hx) (hψ hy)
    rw [hxy] at h0 h1
    have hdd : diskDist (ψ y) (ψ y) = 0 := le_antisymm h2 h0
    rw [hdd, mul_zero] at h1
    have hvx : 0 < varpi x := by
      have : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
      unfold varpi; nlinarith [norm_nonneg x]
    have hvy : 0 < varpi y := by
      have : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
      unfold varpi; nlinarith [norm_nonneg y]
    have hr : 0 < √(varpi x * varpi y) := Real.sqrt_pos.mpr (mul_pos hvx hvy)
    have hq : 0 < √(1 + (‖x - y‖ / √(varpi x * varpi y)) ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have h4 : 2 * (‖x - y‖ / √(varpi x * varpi y)) ≤ 0 := by
      have h5 := h3.trans h1
      rw [div_le_iff₀ hq, zero_mul] at h5
      exact h5
    have h6 : ‖x - y‖ / √(varpi x * varpi y) ≤ 0 := by linarith
    rw [div_le_iff₀ hr, zero_mul] at h6
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h6)
  -- Rademacher: `ψ` is differentiable a.e. on `𝔻`
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ S → DifferentiableAt ℝ ψ z := by
    have hn : ∀ n : ℕ, ∀ᵐ z ∂(volume : Measure ℂ),
        z ∈ ball (0 : ℂ) (1 - 1 / ((n : ℝ) + 1)) → DifferentiableAt ℝ ψ z := by
      intro n
      have hR0 : 0 ≤ 1 - 1 / ((n : ℝ) + 1) := by
        rw [sub_nonneg, div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hR1 : 1 - 1 / ((n : ℝ) + 1) < 1 := by
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      obtain ⟨C, hC⟩ := s07_tw_lip hψ hL hR0 hR1
      filter_upwards [hC.ae_differentiableWithinAt_of_mem (μ := volume)] with z hz hzb
      exact (hz hzb).differentiableAt (isOpen_ball.mem_nhds hzb)
    filter_upwards [ae_all_iff.mpr hn] with z hz hzS
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp (hSD hzS)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by linarith : (0 : ℝ) < 1 - ‖z‖)
    exact hz n (mem_ball_zero_iff.mpr (by linarith))
  obtain ⟨S', hS'd⟩ : ∃ S' : Set ℂ, S' = S ∩ {z | DifferentiableAt ℝ ψ z} := ⟨_, rfl⟩
  have hS' : MeasurableSet S' := by
    rw [hS'd]
    exact hS.inter (measurableSet_of_differentiableAt ℝ ψ)
  have hSS' : S =ᵐ[(volume : Measure ℂ)] S' := by
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [hae] with z hz
    rw [hS'd]
    exact ⟨fun h => ⟨h, hz h⟩, fun h => h.1⟩
  have hS'S : S' ⊆ S := by
    rw [hS'd]
    exact inter_subset_left
  have hder : ∀ x ∈ S', HasFDerivWithinAt ψ (fderiv ℝ ψ x) S' x := by
    intro x hx
    rw [hS'd] at hx
    exact hx.2.hasFDerivAt.hasFDerivWithinAt
  calc ∫⁻ z in S, lam (ψ z) * ‖dzC ψ z‖ₑ = ∫⁻ z in S', lam (ψ z) * ‖dzC ψ z‖ₑ :=
        setLIntegral_congr hSS'
    _ ≤ ∫⁻ z in S', ENNReal.ofReal |(fderiv ℝ ψ z).det| * (lam (ψ z) * Φ (ψ z)) := by
        refine lintegral_mono_ae (ae_restrict_of_forall_mem hS' fun z hz => ?_)
        have hz' := hz
        rw [hS'd] at hz'
        calc lam (ψ z) * ‖dzC ψ z‖ₑ
            ≤ lam (ψ z) * (Φ (ψ z) * ENNReal.ofReal |(fderiv ℝ ψ z).det|) := by
              gcongr
              exact hΦ z hz'.1 hz'.2
          _ = ENNReal.ofReal |(fderiv ℝ ψ z).det| * (lam (ψ z) * Φ (ψ z)) := by ring
    _ = ∫⁻ w in ψ '' S', lam w * Φ w :=
        (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS' hder
          (hinj.mono (hS'S.trans hSD)) fun w => lam w * Φ w).symm
    _ ≤ ∫⁻ w in ψ '' S, lam w * Φ w := lintegral_mono_set (image_mono hS'S)

/-- Helper for `s07_tw_nu`: the chord is at most the arc, `|e^{iφ} - e^{ic}| ≤ |φ - c|`. -/
theorem s07_tw_chord (φ c : ℝ) : ‖exp (φ * I) - exp (c * I)‖ ≤ |φ - c| := by
  have h := s07_tw_circ_dist φ c
  have h2 := Real.one_sub_sq_div_two_le_cos (x := φ - c)
  have h3 : ‖exp (φ * I) - exp (c * I)‖ ^ 2 ≤ |φ - c| ^ 2 := by
    rw [h, sq_abs]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).mp h3

/-- Helper for `s07_tw_nu`: `1 - m ≤ 2 β(m)`, `β(m) = 2 arctan((1 - m)/(1 + m))`. -/
theorem s07_tw_one_sub_le_beta {m : ℝ} (h0 : 0 ≤ m) (h1 : m < 1) :
    1 - m ≤ 2 * (2 * Real.arctan ((1 - m) / (1 + m))) := by
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (1 - m) / (1 + m) := ⟨_, rfl⟩
  rw [← hy]
  have hy0 : 0 ≤ y := by rw [hy]; exact div_nonneg (by linarith) (by linarith)
  have hy1 : y ≤ 1 := by rw [hy, div_le_one (by linarith)]; linarith
  have hc : 1 / 2 ≤ Real.cos (y / 2) := by
    have := Real.one_sub_sq_div_two_le_cos (x := y / 2)
    nlinarith
  have hs : Real.sin (y / 2) ≤ y / 2 := Real.sin_le (by linarith)
  have ht : Real.tan (y / 2) ≤ y := by
    rw [Real.tan_eq_sin_div_cos, div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hc hy0]
  have hπ := Real.pi_gt_three
  have h3 : y / 2 ≤ Real.arctan y := by
    have := Real.arctan_strictMono.monotone ht
    rwa [Real.arctan_tan (by linarith) (by linarith)] at this
  have e : 1 - m = y * (1 + m) := by
    rw [hy]
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left (by linarith : 1 + m ≤ 2) hy0]

/-- Helper for `s07_tw_nu`: `μ(𝔻) ≤ 2 ‖μ‖_CM` (continuity from below along `𝔻 ∩ D(1, 2 - ε)`). -/
theorem s07_tw_disc_mass (μ : Measure ℂ) :
    μ unitDisc ≤ carlesonNorm μ * ENNReal.ofReal 2 := by
  have hU : unitDisc = ⋃ n : ℕ, unitDisc ∩ ball (1 : ℂ) (2 - 1 / ((n : ℝ) + 1)) := by
    ext w
    simp only [mem_iUnion, mem_inter_iff]
    constructor
    · intro hw
      have h1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by linarith : (0 : ℝ) < 1 - ‖w‖)
      refine ⟨n, hw, ?_⟩
      rw [mem_ball, dist_eq_norm]
      have := norm_sub_le w 1
      rw [norm_one] at this
      linarith
    · rintro ⟨n, hw, -⟩
      exact hw
  have hmono : Monotone fun n : ℕ => unitDisc ∩ ball (1 : ℂ) (2 - 1 / ((n : ℝ) + 1)) := by
    intro i j hij
    apply inter_subset_inter_right
    apply ball_subset_ball
    have hij' : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by
      have := (Nat.cast_le (α := ℝ)).mpr hij
      linarith
    have := one_div_le_one_div_of_le (by positivity) hij'
    linarith
  rw [hU, hmono.measure_iUnion]
  refine iSup_le fun n => ?_
  have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [n.cast_nonneg (α := ℝ)]
  refine (s07_le_carlesonNorm μ 1 (by simp) _ (by linarith) (by linarith)).trans ?_
  gcongr
  linarith

/-- The box-coordinate image `ν_k` of `λ dA` (`w ↦ (arg w + 2πk, β(w))`) is Carleson on boxes over
intervals of length `≤ 2π`: the box lies in `𝔻 ∩ B(e^{i(a+b)/2}, 3(b - a))`. -/
theorem s07_tw_nu (lam : ℂ → ℝ≥0∞) (k : ℤ) {a b : ℝ} (hab : a < b) (hb : b - a ≤ 2 * π) :
    ((volume.restrict unitDisc).withDensity lam).map
        (fun w => (Complex.arg w + 2 * π * k, 2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖))))
      (Icc a b ×ˢ Ioc 0 (b - a)) ≤
      3 * carlesonNorm ((volume.restrict unitDisc).withDensity lam) * ENNReal.ofReal (b - a) := by
  -- `hb` is not needed: the bound holds for every interval
  have _hb := hb
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hf : Measurable (fun w : ℂ =>
      (Complex.arg w + 2 * π * k, 2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖)))) := by
    refine Measurable.prodMk (Complex.measurable_arg.add_const _) ?_
    exact (Real.continuous_arctan.measurable.comp
      (by fun_prop : Measurable fun w : ℂ => (1 - ‖w‖) / (1 + ‖w‖))).const_mul 2
  rw [Measure.map_apply hf (measurableSet_Icc.prod measurableSet_Ioc)]
  obtain ⟨μ, hμd⟩ : ∃ μ : Measure ℂ, μ = (volume.restrict unitDisc).withDensity lam := ⟨_, rfl⟩
  rw [← hμd]
  obtain ⟨A, hAd⟩ : ∃ A : Set ℂ, A = (fun w : ℂ =>
      (Complex.arg w + 2 * π * k, 2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖)))) ⁻¹'
        (Icc a b ×ˢ Ioc 0 (b - a)) := ⟨_, rfl⟩
  rw [← hAd]
  have hμc : μ unitDiscᶜ = 0 := by
    rw [hμd]
    exact withDensity_absolutelyContinuous _ _
      (by rw [Measure.restrict_apply hDm.compl, compl_inter_self, measure_empty])
  have hAD : μ A ≤ μ (A ∩ unitDisc) := by
    have hsub : A ⊆ (A ∩ unitDisc) ∪ unitDiscᶜ := by
      intro w hw
      by_cases h : w ∈ unitDisc
      · exact Or.inl ⟨hw, h⟩
      · exact Or.inr h
    calc μ A ≤ μ ((A ∩ unitDisc) ∪ unitDiscᶜ) := measure_mono hsub
      _ ≤ μ (A ∩ unitDisc) + μ unitDiscᶜ := measure_union_le _ _
      _ = μ (A ∩ unitDisc) := by rw [hμc, add_zero]
  have h3 : 3 * carlesonNorm μ * ENNReal.ofReal (b - a) =
      carlesonNorm μ * ENNReal.ofReal (3 * (b - a)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat]
    ring
  rw [h3]
  refine hAD.trans ?_
  rcases le_or_gt 2 (3 * (b - a)) with hbig | hsmall
  · calc μ (A ∩ unitDisc) ≤ μ unitDisc := measure_mono inter_subset_right
      _ ≤ carlesonNorm μ * ENNReal.ofReal 2 := s07_tw_disc_mass μ
      _ ≤ carlesonNorm μ * ENNReal.ofReal (3 * (b - a)) := by
        gcongr
  -- `A ∩ 𝔻 ⊆ 𝔻 ∩ D(e^{ic}, 3(b - a))`, `c = (a + b)/2`
  have hsub : A ∩ unitDisc ⊆ unitDisc ∩ ball (exp (((a + b) / 2 : ℝ) * I)) (3 * (b - a)) := by
    rintro w ⟨hwA, hwD⟩
    refine ⟨hwD, ?_⟩
    rw [hAd] at hwA
    simp only [mem_preimage, mem_prod, mem_Icc, mem_Ioc] at hwA
    obtain ⟨⟨h1, h2⟩, -, h4⟩ := hwA
    have hm0 : 0 ≤ ‖w‖ := norm_nonneg w
    have hm1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hwD
    have hβ := s07_tw_one_sub_le_beta hm0 hm1
    obtain ⟨φ, hφd⟩ : ∃ φ : ℝ, φ = Complex.arg w + 2 * π * k := ⟨_, rfl⟩
    rw [← hφd] at h1 h2
    have hwφ : w = (‖w‖ : ℂ) * exp (φ * I) := by
      rw [hφd]
      push_cast
      rw [show ((Complex.arg w : ℂ) + 2 * (π : ℂ) * (k : ℂ)) * I =
          (Complex.arg w : ℂ) * I + (k : ℂ) * (2 * π * I) by ring, Complex.exp_add,
        Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.norm_mul_exp_arg_mul_I]
    have hEφ : ‖exp (φ * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I φ
    have hw1 : ‖w - exp (φ * I)‖ = 1 - ‖w‖ := by
      have e : w - exp (φ * I) = -(((1 - ‖w‖ : ℝ) : ℂ) * exp (φ * I)) := by
        conv_lhs => rw [hwφ]
        push_cast
        ring
      rw [e, norm_neg, norm_mul, hEφ, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
    have hch := s07_tw_chord φ ((a + b) / 2)
    have hφc : |φ - (a + b) / 2| ≤ (b - a) / 2 := by
      rw [abs_le]
      constructor <;> linarith
    have htri : ‖w - exp (((a + b) / 2 : ℝ) * I)‖ ≤
        ‖w - exp (φ * I)‖ + ‖exp (φ * I) - exp (((a + b) / 2 : ℝ) * I)‖ := by
      have e : w - exp (((a + b) / 2 : ℝ) * I) =
          (w - exp (φ * I)) + (exp (φ * I) - exp (((a + b) / 2 : ℝ) * I)) := by ring
      rw [e]
      exact norm_add_le _ _
    rw [mem_ball, dist_eq_norm]
    linarith
  calc μ (A ∩ unitDisc) ≤ μ (unitDisc ∩ ball (exp (((a + b) / 2 : ℝ) * I)) (3 * (b - a))) :=
        measure_mono hsub
    _ ≤ carlesonNorm μ * ENNReal.ofReal (3 * (b - a)) :=
        s07_le_carlesonNorm μ _ (by
          rw [mem_sphere_zero_iff_norm]
          exact Complex.norm_exp_ofReal_mul_I _) _ (by linarith) hsmall

/-- Helper for `s07_tw_box`: if `g(F_k w) = G(w)` for the three lifts `k = -1, 0, 1`, then
`∫_{⋃_k F_k⁻¹(B)} G dμ ≤ ∫_B g d(Σ_k (F_k)_* μ)`. -/
theorem s07_tw_box_aux (μ : Measure ℂ) (F : ℤ → ℂ → ℝ × ℝ) (hF : ∀ k, Measurable (F k))
    {g : ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) {B : Set (ℝ × ℝ)} (hB : MeasurableSet B)
    {G : ℂ → ℝ≥0∞} (hG : ∀ k w, g (F k w) = G w) :
    ∫⁻ w in F (-1) ⁻¹' B ∪ F 0 ⁻¹' B ∪ F 1 ⁻¹' B, G w ∂μ ≤
      ∫⁻ p in B, g p ∂(∑ k ∈ Finset.Icc (-1 : ℤ) 1, μ.map (F k)) := by
  have hrs : (∑ k ∈ Finset.Icc (-1 : ℤ) 1, μ.map (F k)).restrict B =
      ∑ k ∈ Finset.Icc (-1 : ℤ) 1, (μ.map (F k)).restrict B := by
    simp only [← Measure.restrictₗ_apply]
    exact map_sum _ _ _
  rw [hrs, lintegral_finsetSum_measure]
  have hI : Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hI, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have hk : ∀ k, ∫⁻ p in B, g p ∂μ.map (F k) = ∫⁻ w in F k ⁻¹' B, G w ∂μ := by
    intro k
    rw [setLIntegral_map hB hg (hF k)]
    exact lintegral_congr fun w => hG k w
  rw [hk, hk, hk]
  calc _ ≤ ∫⁻ w in F (-1) ⁻¹' B ∪ F 0 ⁻¹' B, G w ∂μ + ∫⁻ w in F 1 ⁻¹' B, G w ∂μ :=
        lintegral_union_le _ _ _
    _ ≤ _ := by
        rw [← add_assoc]
        gcongr
        exact lintegral_union_le _ _ _

/-- Transfer to the box: if every `w ∈ T` has box coordinates `(arg w + 2πk, β(w))` (some
`|k| ≤ 1`) in the box over `[a, b]`, then `∫_T λ(w) |H⁻¹(I_w)|/2β(w)` is at most the box integral of
`μ([t - s, t + s])/2s` against `ν = ν₋₁ + ν₀ + ν₁` (periodicity of `μ = |H⁻¹(·)|`). -/
theorem s07_tw_box (lam : ℂ → ℝ≥0∞) (hlam : Measurable lam) {H : ℝ → ℝ} (hH : StrictMono H)
    (hHc : Continuous H) (hper : ∀ θ, H (θ + 2 * π) = H θ + 2 * π) {T : Set ℂ}
    (hT : T ⊆ unitDisc) {a b : ℝ}
    (hTb : ∀ w ∈ T, ∃ k ∈ Finset.Icc (-1 : ℤ) 1, (Complex.arg w + 2 * π * k,
      2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖))) ∈ Icc a b ×ˢ Ioc 0 (b - a)) :
    ∫⁻ w in T, lam w * (volume (H ⁻¹' Icc
        (Complex.arg w - 2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖)))
        (Complex.arg w + 2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖)))) /
          ENNReal.ofReal (2 * (2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖))))) ≤
      ∫⁻ p in Icc a b ×ˢ Ioc 0 (b - a),
        Measure.map H volume (Icc (p.1 - p.2) (p.1 + p.2)) / ENNReal.ofReal (2 * p.2)
        ∂(∑ k ∈ Finset.Icc (-1 : ℤ) 1, ((volume.restrict unitDisc).withDensity lam).map
          (fun w => (Complex.arg w + 2 * π * k, 2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖))))) := by
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hbox : MeasurableSet (Icc a b ×ˢ Ioc 0 (b - a)) := measurableSet_Icc.prod measurableSet_Ioc
  -- `H` is an order isomorphism of `ℝ`, periodic up to `2π`
  have hsurj : Function.Surjective H := fun y => s07_tw_lift_surj hHc hper y
  obtain ⟨e, he⟩ : ∃ e : ℝ ≃o ℝ, ⇑e = H := ⟨StrictMono.orderIsoOfSurjective H hH hsurj, rfl⟩
  have hvol : ∀ x y, volume (H ⁻¹' Icc x y) = ENNReal.ofReal (e.symm y - e.symm x) := by
    intro x y
    rw [← he, e.preimage_Icc x y, Real.volume_Icc]
  have hmap : ∀ x y, Measure.map H volume (Icc x y) = ENNReal.ofReal (e.symm y - e.symm x) := by
    intro x y
    rw [Measure.map_apply hHc.measurable measurableSet_Icc, hvol]
  have hes : ∀ (k : ℤ) (y : ℝ), e.symm (y + 2 * π * k) = e.symm y + 2 * π * k := by
    intro k y
    apply e.injective
    rw [e.apply_symm_apply, he, show e.symm y + 2 * π * k = e.symm y + k * (2 * π) by ring,
      s07_inv_per_int hper k, ← he, e.apply_symm_apply]
    ring
  -- the integrands
  obtain ⟨g, hgd⟩ : ∃ g : ℝ × ℝ → ℝ≥0∞, g = fun p =>
      ENNReal.ofReal (e.symm (p.1 + p.2) - e.symm (p.1 - p.2)) / ENNReal.ofReal (2 * p.2) :=
    ⟨_, rfl⟩
  have hgm : Measurable g := by
    rw [hgd]
    have hc : Measurable fun y : ℝ => e.symm y := e.symm.continuous.measurable
    simp only [div_eq_mul_inv]
    exact (ENNReal.measurable_ofReal.comp ((hc.comp (measurable_fst.add measurable_snd)).sub
      (hc.comp (measurable_fst.sub measurable_snd)))).mul
      (ENNReal.measurable_ofReal.comp (measurable_snd.const_mul 2)).inv
  have hRg : ∀ p : ℝ × ℝ,
      Measure.map H volume (Icc (p.1 - p.2) (p.1 + p.2)) / ENNReal.ofReal (2 * p.2) = g p := by
    intro p
    rw [hmap, hgd]
  obtain ⟨F, hFd⟩ : ∃ F : ℤ → ℂ → ℝ × ℝ, F = fun (k : ℤ) w =>
      (Complex.arg w + 2 * π * (k : ℝ), 2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖))) := ⟨_, rfl⟩
  have hβm : Measurable fun w : ℂ => 2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖)) :=
    (Real.continuous_arctan.measurable.comp
      (by fun_prop : Measurable fun w : ℂ => (1 - ‖w‖) / (1 + ‖w‖))).const_mul 2
  have hFm : ∀ k, Measurable (F k) := by
    intro k
    rw [hFd]
    exact Measurable.prodMk (Complex.measurable_arg.add_const _) hβm
  obtain ⟨G, hGd⟩ : ∃ G : ℂ → ℝ≥0∞, G = fun w =>
      g (Complex.arg w, 2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖))) := ⟨_, rfl⟩
  have hGm : Measurable G := by
    rw [hGd]
    exact hgm.comp (Complex.measurable_arg.prodMk hβm)
  have hGk : ∀ k w, g (F k w) = G w := by
    intro k w
    simp only [hFd, hGd, hgd]
    generalize 2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖)) = β
    generalize Complex.arg w = φ
    rw [show φ + 2 * π * k + β = (φ + β) + 2 * π * k by ring,
      show φ + 2 * π * k - β = (φ - β) + 2 * π * k by ring, hes, hes, add_sub_add_right_eq_sub]
  have hLG : ∀ w, volume (H ⁻¹' Icc
        (Complex.arg w - 2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖)))
        (Complex.arg w + 2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖)))) /
          ENNReal.ofReal (2 * (2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖)))) = G w := by
    intro w
    simp only [hvol, hGd, hgd]
  -- `T` is covered by the three preimages of the box
  have hUm : MeasurableSet (F (-1) ⁻¹' (Icc a b ×ˢ Ioc 0 (b - a)) ∪
      F 0 ⁻¹' (Icc a b ×ˢ Ioc 0 (b - a)) ∪ F 1 ⁻¹' (Icc a b ×ˢ Ioc 0 (b - a))) :=
    ((hFm _ hbox).union (hFm _ hbox)).union (hFm _ hbox)
  have hTU : T ⊆ (F (-1) ⁻¹' (Icc a b ×ˢ Ioc 0 (b - a)) ∪
      F 0 ⁻¹' (Icc a b ×ˢ Ioc 0 (b - a)) ∪ F 1 ⁻¹' (Icc a b ×ˢ Ioc 0 (b - a))) ∩ unitDisc := by
    intro w hw
    obtain ⟨k, hk, hkb⟩ := hTb w hw
    have hkF : F k w ∈ Icc a b ×ˢ Ioc 0 (b - a) := by rw [hFd]; exact hkb
    rw [Finset.mem_Icc] at hk
    obtain ⟨hk1, hk2⟩ := hk
    refine ⟨?_, hT hw⟩
    interval_cases k
    · exact Or.inl (Or.inl hkF)
    · exact Or.inl (Or.inr hkF)
    · exact Or.inr hkF
  have hA := s07_tw_box_aux ((volume.restrict unitDisc).withDensity lam) F hFm hgm hbox hGk
  rw [hFd] at hA
  simp_rw [hRg]
  calc _ = ∫⁻ w in T, lam w * G w := lintegral_congr fun w => by rw [hLG w]
    _ ≤ ∫⁻ w in (F (-1) ⁻¹' (Icc a b ×ˢ Ioc 0 (b - a)) ∪
          F 0 ⁻¹' (Icc a b ×ˢ Ioc 0 (b - a)) ∪ F 1 ⁻¹' (Icc a b ×ˢ Ioc 0 (b - a))) ∩ unitDisc,
          lam w * G w :=
        lintegral_mono' (Measure.restrict_mono_set _ hTU) le_rfl
    _ = ∫⁻ w in F (-1) ⁻¹' (Icc a b ×ˢ Ioc 0 (b - a)) ∪
          F 0 ⁻¹' (Icc a b ×ˢ Ioc 0 (b - a)) ∪ F 1 ⁻¹' (Icc a b ×ˢ Ioc 0 (b - a)),
          (lam * G) w ∂(volume.restrict unitDisc) := by
        rw [Measure.restrict_restrict hUm]
        rfl
    _ = ∫⁻ w in F (-1) ⁻¹' (Icc a b ×ˢ Ioc 0 (b - a)) ∪
          F 0 ⁻¹' (Icc a b ×ˢ Ioc 0 (b - a)) ∪ F 1 ⁻¹' (Icc a b ×ˢ Ioc 0 (b - a)),
          G w ∂((volume.restrict unitDisc).withDensity lam) :=
        (setLIntegral_withDensity_eq_setLIntegral_mul _ hlam hGm hUm).symm
    _ ≤ _ := by
        rw [hFd]
        exact hA

/-- Helper for `s07_tw_embed`: membership in the cell `D k i` of size `S / 2 ^ k` of the grid
based at `α`. -/
theorem s07_twe_mem {α S : ℝ} (hS : 0 < S) {D : ℕ → ℤ → Set ℝ}
    (hD : ∀ k i, D k i = Ico (α + i * (S / 2 ^ k)) (α + (i + 1) * (S / 2 ^ k))) (k : ℕ) (i : ℤ)
    (x : ℝ) : x ∈ D k i ↔ ⌊(x - α) / (S / 2 ^ k)⌋ = i := by
  rw [hD, s07_cz_cell_iff (by positivity)]

/-- Helper for `s07_tw_embed`: two cells of the grid that meet are nested. -/
theorem s07_twe_nest {α S : ℝ} (hS : 0 < S) {D : ℕ → ℤ → Set ℝ}
    (hD : ∀ k i, D k i = Ico (α + i * (S / 2 ^ k)) (α + (i + 1) * (S / 2 ^ k))) {g k : ℕ}
    (hgk : g ≤ k) {i j : ℤ} {x : ℝ} (hx : x ∈ D k i) (hx' : x ∈ D g j) : D k i ⊆ D g j := by
  have h1 : ∀ n : ℕ, D (n + 1) ⌊(x - α) / (S / 2 ^ (n + 1))⌋ ⊆ D n ⌊(x - α) / (S / 2 ^ n)⌋ := by
    intro n
    have e : S / 2 ^ (n + 1) = S / 2 ^ n / 2 := by rw [pow_succ, div_div]
    rw [hD, hD, e]
    exact s07_cz_cell_nest (by positivity)
  have h2 : ∀ n, g ≤ n → D n ⌊(x - α) / (S / 2 ^ n)⌋ ⊆ D g ⌊(x - α) / (S / 2 ^ g)⌋ := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact subset_rfl
    | succ n _ ih => exact (h1 n).trans ih
  rw [← (s07_twe_mem hS hD k i x).mp hx, ← (s07_twe_mem hS hD g j x).mp hx']
  exact h2 k hgk

/-- Helper for `s07_tw_embed` (dyadic Carleson embedding): if `c` is a Carleson sequence on the
cells of the grid inside the top cell `D 0 i₀`, and `μ` gives at most half of a cell to subsets of
relative size `2 / 2 ^ q`, then `∑ c_J μ(J) / |J| ≤ (1 + 2 ^ (q + 1)) N μ(D 0 i₀)`. Stopping time
at the levels `2 ^ (q j) μ(D 0 i₀) / |D 0 i₀|`; the maximal cells of each level carry the
Carleson mass, and their union loses half of its `μ`-measure from one level to the next. -/
theorem s07_twe_stop {μ : Measure ℝ} {α S : ℝ} (hS : 0 < S) {D : ℕ → ℤ → Set ℝ}
    (hD : ∀ k i, D k i = Ico (α + i * (S / 2 ^ k)) (α + (i + 1) * (S / 2 ^ k))) (i₀ : ℤ)
    (hfin : μ (D 0 i₀) ≠ ⊤) {q : ℕ} (hq : 0 < q)
    (hdec : ∀ k i, D k i ⊆ D 0 i₀ → ∀ A ⊆ D k i, MeasurableSet A →
      2 ^ q * volume A ≤ 2 * ENNReal.ofReal (S / 2 ^ k) → μ A ≤ 2⁻¹ * μ (D k i))
    (c : ℕ → ℤ → ℝ≥0∞) (N : ℝ≥0∞) (hc0 : ∀ k i, c k i ≠ 0 → D k i ⊆ D 0 i₀)
    (hcar : ∀ g j, D g j ⊆ D 0 i₀ → ∑' p : ℕ × ℤ,
      {p : ℕ × ℤ | D p.1 p.2 ⊆ D g j}.indicator (fun p => c p.1 p.2) p ≤
        N * ENNReal.ofReal (S / 2 ^ g)) :
    ∑' p : ℕ × ℤ, c p.1 p.2 * (μ (D p.1 p.2) / ENNReal.ofReal (S / 2 ^ p.1)) ≤
      (1 + 2 ^ (q + 1)) * N * μ (D 0 i₀) := by
  classical
  have hs0 : ∀ k : ℕ, 0 < S / 2 ^ k := fun k => by positivity
  have hs2 : ∀ k : ℕ, S / 2 ^ k = 2 * (S / 2 ^ (k + 1)) := fun k => by rw [pow_succ]; ring
  have hsne : ∀ k : ℕ, ENNReal.ofReal (S / 2 ^ k) ≠ 0 := fun k =>
    (ENNReal.ofReal_pos.mpr (hs0 k)).ne'
  have hvol : ∀ k i, volume (D k i) = ENNReal.ofReal (S / 2 ^ k) := fun k i => by
    rw [hD, Real.volume_Ico]; congr 1; ring
  have hmeas : ∀ k i, MeasurableSet (D k i) := fun k i => by rw [hD]; exact measurableSet_Ico
  have hne : ∀ k (i : ℤ), α + i * (S / 2 ^ k) ∈ D k i := fun k i => by
    rw [hD]
    have e : (↑i + 1) * (S / 2 ^ k) = ↑i * (S / 2 ^ k) + S / 2 ^ k := by ring
    exact ⟨le_rfl, by linarith [hs0 k]⟩
  -- `B t k i`: the average of `μ` on `D k i` exceeds `t`
  obtain ⟨B, hB⟩ : ∃ B : ℝ≥0∞ → ℕ → ℤ → Prop,
      ∀ t k i, B t k i ↔ t * ENNReal.ofReal (S / 2 ^ k) < μ (D k i) :=
    ⟨fun t k i => t * ENNReal.ofReal (S / 2 ^ k) < μ (D k i), fun _ _ _ => Iff.rfl⟩
  -- `Mx t g j`: `D g j` is a maximal cell with `B t` inside the top cell
  obtain ⟨Mx, hMx⟩ : ∃ Mx : ℝ≥0∞ → ℕ → ℤ → Prop, ∀ t g j, Mx t g j ↔
      (D g j ⊆ D 0 i₀ ∧ B t g j ∧ ∀ k < g, ∀ i, D g j ⊆ D k i → ¬ B t k i) :=
    ⟨fun t g j => D g j ⊆ D 0 i₀ ∧ B t g j ∧ ∀ k < g, ∀ i, D g j ⊆ D k i → ¬ B t k i,
      fun _ _ _ => Iff.rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ≥0∞ → ℕ × ℤ → Set ℝ, ∀ t p x, x ∈ E t p ↔
      (Mx t p.1 p.2 ∧ x ∈ D p.1 p.2) :=
    ⟨fun t p => {x | Mx t p.1 p.2 ∧ x ∈ D p.1 p.2}, fun _ _ _ => Iff.rfl⟩
  have hEc : ∀ t p, (Mx t p.1 p.2 ∧ E t p = D p.1 p.2) ∨ (¬ Mx t p.1 p.2 ∧ E t p = ∅) := by
    intro t p
    by_cases h : Mx t p.1 p.2
    · exact Or.inl ⟨h, by ext x; rw [hE]; exact ⟨fun hx => hx.2, fun hx => ⟨h, hx⟩⟩⟩
    · exact Or.inr ⟨h, by
        ext x; rw [hE]; exact ⟨fun hx => absurd hx.1 h, fun hx => absurd hx (notMem_empty x)⟩⟩
  have hEmeas : ∀ t p, MeasurableSet (E t p) := by
    intro t p
    rcases hEc t p with ⟨-, h⟩ | ⟨-, h⟩
    · rw [h]; exact hmeas _ _
    · rw [h]; exact MeasurableSet.empty
  -- every cell with `B t` lies in a maximal one
  have hexist : ∀ t k i, B t k i → D k i ⊆ D 0 i₀ → ∃ g j, Mx t g j ∧ D k i ⊆ D g j := by
    intro t k i hb hk
    have hP : ∃ g, ∃ j, D k i ⊆ D g j ∧ B t g j := ⟨k, i, subset_rfl, hb⟩
    obtain ⟨j, hj, hbj⟩ := Nat.find_spec hP
    refine ⟨Nat.find hP, j, (hMx _ _ _).mpr ⟨?_, hbj, ?_⟩, hj⟩
    · exact s07_twe_nest hS hD (Nat.zero_le _) (hj (hne k i)) (hk (hne k i))
    · intro k' hk' i' hsub hb'
      exact Nat.find_min hP hk' ⟨i', hj.trans hsub, hb'⟩
  -- maximal cells that meet coincide
  have hkey : ∀ t g j g' j' x, Mx t g j → Mx t g' j' → g ≤ g' → x ∈ D g j → x ∈ D g' j' →
      g = g' ∧ j = j' := by
    intro t g j g' j' x h h' hle hx hx'
    rcases hle.lt_or_eq with hlt | heq
    · exact absurd ((hMx t g j).mp h).2.1
        (((hMx t g' j').mp h').2.2 g hlt j (s07_twe_nest hS hD hle hx' hx))
    · subst heq
      exact ⟨rfl, ((s07_twe_mem hS hD g j x).mp hx).symm.trans
        ((s07_twe_mem hS hD g j' x).mp hx')⟩
  have hsame : ∀ t g j g' j' x, Mx t g j → Mx t g' j' → x ∈ D g j → x ∈ D g' j' →
      g = g' ∧ j = j' := by
    intro t g j g' j' x h h' hx hx'
    rcases le_total g g' with hle | hle
    · exact hkey t g j g' j' x h h' hle hx hx'
    · obtain ⟨e1, e2⟩ := hkey t g' j' g j x h' h hle hx' hx
      exact ⟨e1.symm, e2.symm⟩
  have hEdisj : ∀ t, Pairwise (Function.onFun Disjoint (E t)) := by
    intro t p p' hpp'
    show Disjoint (E t p) (E t p')
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [hE] at hx hx'
    obtain ⟨e1, e2⟩ := hsame t _ _ _ _ x hx.1 hx'.1 hx.2 hx'.2
    exact hpp' (Prod.ext e1 e2)
  have hEle : ∀ t p, t * volume (E t p) ≤ μ (E t p) := by
    intro t p
    rcases hEc t p with ⟨h, he⟩ | ⟨-, he⟩
    · rw [he, hvol]; exact ((hB _ _ _).mp ((hMx _ _ _).mp h).2.1).le
    · rw [he]; simp
  -- the parent of a maximal cell does not have `B t`
  have hpar : ∀ t g j, ¬ B t 0 i₀ → Mx t g j →
      μ (D g j) ≤ 2 * t * ENNReal.ofReal (S / 2 ^ g) := by
    intro t g j hQ hm
    obtain ⟨hsub, hb, hmax⟩ := (hMx t g j).mp hm
    have hg : g ≠ 0 := by
      rintro rfl
      have hj : j = i₀ := ((s07_twe_mem hS hD 0 j _).mp (hne 0 j)).symm.trans
        ((s07_twe_mem hS hD 0 i₀ _).mp (hsub (hne 0 j)))
      rw [hj] at hb
      exact hQ hb
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    have hxp : α + j * (S / 2 ^ (g' + 1)) ∈
        D g' ⌊(α + j * (S / 2 ^ (g' + 1)) - α) / (S / 2 ^ g')⌋ :=
      (s07_twe_mem hS hD _ _ _).mpr rfl
    have hsp := s07_twe_nest hS hD (Nat.le_succ g') (hne (g' + 1) j) hxp
    have hnb := hmax g' (Nat.lt_succ_self g') _ hsp
    rw [hB, not_lt] at hnb
    calc μ (D (g' + 1) j) ≤ μ (D g' ⌊(α + j * (S / 2 ^ (g' + 1)) - α) / (S / 2 ^ g')⌋) :=
          measure_mono hsp
      _ ≤ t * ENNReal.ofReal (S / 2 ^ g') := hnb
      _ = 2 * t * ENNReal.ofReal (S / 2 ^ (g' + 1)) := by
        rw [hs2 g', ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]; ring
  -- the cells with `B t` carry Carleson mass at most `N |⋃ E t|`
  have hCU : ∀ t, ∑' p : ℕ × ℤ, (if B t p.1 p.2 then c p.1 p.2 else 0) ≤
      N * volume (⋃ p, E t p) := by
    intro t
    calc ∑' p : ℕ × ℤ, (if B t p.1 p.2 then c p.1 p.2 else 0)
        ≤ ∑' p : ℕ × ℤ, ∑' p' : ℕ × ℤ, (if Mx t p'.1 p'.2 then
            {q : ℕ × ℤ | D q.1 q.2 ⊆ D p'.1 p'.2}.indicator (fun q => c q.1 q.2) p else 0) := by
          refine tsum_le_tsum (fun p => ?_)
          by_cases hb : B t p.1 p.2
          · simp only [hb, ↓reduceIte]
            by_cases hc : c p.1 p.2 = 0
            · rw [hc]; exact zero_le
            · obtain ⟨g, j, hm, hsub⟩ := hexist t p.1 p.2 hb (hc0 _ _ hc)
              refine le_trans (le_of_eq ?_) (le_tsum (fun p' : ℕ × ℤ => if Mx t p'.1 p'.2 then
                {q : ℕ × ℤ | D q.1 q.2 ⊆ D p'.1 p'.2}.indicator (fun q => c q.1 q.2) p else 0) (g, j))
              simp only [hm, ↓reduceIte]
              exact (Set.indicator_of_mem
                (show p ∈ {q : ℕ × ℤ | D q.1 q.2 ⊆ D g j} from hsub) (fun q : ℕ × ℤ => c q.1 q.2)).symm
          · simp only [hb, ↓reduceIte, zero_le]
      _ = ∑' p' : ℕ × ℤ, ∑' p : ℕ × ℤ, (if Mx t p'.1 p'.2 then
            {q : ℕ × ℤ | D q.1 q.2 ⊆ D p'.1 p'.2}.indicator (fun q => c q.1 q.2) p else 0) :=
          tsum_comm
      _ ≤ ∑' p' : ℕ × ℤ, N * volume (E t p') := by
          refine tsum_le_tsum (fun p' => ?_)
          rcases hEc t p' with ⟨h, he⟩ | ⟨h, he⟩
          · simp only [h, ↓reduceIte]
            rw [he, hvol]
            exact hcar p'.1 p'.2 ((hMx _ _ _).mp h).1
          · simp only [h, ↓reduceIte, tsum_zero, zero_le]
      _ = N * volume (⋃ p, E t p) := by
          rw [measure_iUnion (hEdisj t) (hEmeas t), ENNReal.tsum_mul_left]
  have hmuU : ∀ t, t * volume (⋃ p, E t p) ≤ μ (⋃ p, E t p) := by
    intro t
    rw [measure_iUnion (hEdisj t) (hEmeas t), measure_iUnion (hEdisj t) (hEmeas t),
      ← ENNReal.tsum_mul_left]
    exact tsum_le_tsum (hEle t)
  -- decay: from level `t` to level `2 ^ q t` the union loses half of its measure
  have hdecay : ∀ t, ¬ B t 0 i₀ → μ (⋃ p, E (2 ^ q * t) p) ≤ 2⁻¹ * μ (⋃ p, E t p) := by
    intro t hQ
    have hle : t ≤ 2 ^ q * t := le_mul_of_one_le_left' (one_le_pow₀ one_le_two)
    have hBm : ∀ k i, B (2 ^ q * t) k i → B t k i := fun k i h => by
      rw [hB] at h ⊢
      exact lt_of_le_of_lt (mul_le_mul' hle le_rfl) h
    have hsubU : (⋃ p', E (2 ^ q * t) p') ⊆ ⋃ p, E t p := by
      intro x hx
      obtain ⟨p', hx'⟩ := mem_iUnion.mp hx
      obtain ⟨h', hxd⟩ := (hE _ _ _).mp hx'
      obtain ⟨hsub', hb', -⟩ := (hMx _ _ _).mp h'
      obtain ⟨g, j, hm, hs⟩ := hexist t _ _ (hBm _ _ hb') hsub'
      exact mem_iUnion.mpr ⟨(g, j), (hE _ _ _).mpr ⟨hm, hs hxd⟩⟩
    have hloc : ∀ p : ℕ × ℤ, μ ((⋃ p', E (2 ^ q * t) p') ∩ E t p) ≤ 2⁻¹ * μ (E t p) := by
      intro p
      rcases hEc t p with ⟨hm, he⟩ | ⟨-, he⟩
      · rw [he]
        obtain ⟨hsub, hb, -⟩ := (hMx _ _ _).mp hm
        obtain ⟨A, hA⟩ : ∃ A : Set ℝ, A = (⋃ p', E (2 ^ q * t) p') ∩ D p.1 p.2 := ⟨_, rfl⟩
        rw [← hA]
        have hAm : MeasurableSet A := by
          rw [hA]; exact (MeasurableSet.iUnion (hEmeas _)).inter (hmeas _ _)
        refine hdec p.1 p.2 hsub A (by rw [hA]; exact inter_subset_right) hAm ?_
        have ht0 : t ≠ 0 := by
          rintro rfl
          rw [hB, zero_mul] at hb
          rw [hB, not_lt, zero_mul] at hQ
          exact absurd (lt_of_lt_of_le hb (measure_mono hsub)) (not_lt.mpr hQ)
        have htop : t ≠ ⊤ := by
          rintro rfl
          rw [hB, ENNReal.top_mul (hsne _)] at hb
          exact not_top_lt hb
        have h1 : 2 ^ q * t * volume A ≤ μ A := by
          have hd' : Pairwise (Function.onFun Disjoint fun p' => E (2 ^ q * t) p' ∩ D p.1 p.2) :=
            fun p1 p2 h => Disjoint.mono inter_subset_left inter_subset_left (hEdisj _ h)
          have hm' : ∀ p', MeasurableSet (E (2 ^ q * t) p' ∩ D p.1 p.2) :=
            fun p' => (hEmeas _ p').inter (hmeas _ _)
          rw [hA, iUnion_inter, measure_iUnion hd' hm', measure_iUnion hd' hm',
            ← ENNReal.tsum_mul_left]
          refine tsum_le_tsum (fun p' => ?_)
          rcases hEc (2 ^ q * t) p' with ⟨h', he'⟩ | ⟨-, he'⟩
          · by_cases hint : (D p'.1 p'.2 ∩ D p.1 p.2).Nonempty
            · obtain ⟨x, hx', hx⟩ := hint
              have hin : D p'.1 p'.2 ⊆ D p.1 p.2 := by
                obtain ⟨hsub', hb', -⟩ := (hMx _ _ _).mp h'
                obtain ⟨g, j, hm2, hs⟩ := hexist t _ _ (hBm _ _ hb') hsub'
                obtain ⟨rfl, rfl⟩ := hsame t _ _ _ _ x hm2 hm (hs hx') hx
                exact hs
              rw [he', inter_eq_left.mpr hin]
              have := hEle (2 ^ q * t) p'
              rwa [he'] at this
            · rw [he', not_nonempty_iff_eq_empty.mp hint]; simp
          · rw [he']; simp
        refine (ENNReal.mul_le_mul_iff_right ht0 htop).mp ?_
        calc t * (2 ^ q * volume A) = 2 ^ q * t * volume A := by ring
          _ ≤ μ A := h1
          _ ≤ μ (D p.1 p.2) := measure_mono (by rw [hA]; exact inter_subset_right)
          _ ≤ 2 * t * ENNReal.ofReal (S / 2 ^ p.1) := hpar t p.1 p.2 hQ hm
          _ = t * (2 * ENNReal.ofReal (S / 2 ^ p.1)) := by ring
      · rw [he]; simp
    calc μ (⋃ p', E (2 ^ q * t) p') = μ (⋃ p, (⋃ p', E (2 ^ q * t) p') ∩ E t p) := by
          rw [← inter_iUnion, inter_eq_left.mpr hsubU]
      _ = ∑' p, μ ((⋃ p', E (2 ^ q * t) p') ∩ E t p) :=
          measure_iUnion (fun p1 p2 h => Disjoint.mono inter_subset_right inter_subset_right
            (hEdisj t h)) (fun p => (MeasurableSet.iUnion (hEmeas _)).inter (hEmeas t p))
      _ ≤ ∑' p, 2⁻¹ * μ (E t p) := tsum_le_tsum hloc
      _ = 2⁻¹ * μ (⋃ p, E t p) := by
          rw [ENNReal.tsum_mul_left, measure_iUnion (hEdisj t) (hEmeas t)]
  -- the levels `T j = 2 ^ (q j) μ(D 0 i₀) / |D 0 i₀|`
  obtain ⟨T, hT'⟩ : ∃ T : ℕ → ℝ≥0∞,
      T = fun j => ((2 : ℝ≥0∞) ^ q) ^ j * (μ (D 0 i₀) / ENNReal.ofReal (S / 2 ^ 0)) := ⟨_, rfl⟩
  have hT : ∀ j, T j = ((2 : ℝ≥0∞) ^ q) ^ j * (μ (D 0 i₀) / ENNReal.ofReal (S / 2 ^ 0)) :=
    fun j => by rw [hT']
  have hTQ : ∀ j, ¬ B (T j) 0 i₀ := by
    intro j h
    rw [hB, hT, mul_assoc, ENNReal.div_mul_cancel (hsne 0) ENNReal.ofReal_ne_top] at h
    have h1 : (1 : ℝ≥0∞) ≤ (2 ^ q) ^ j := one_le_pow₀ (one_le_pow₀ (by norm_num))
    exact absurd h (not_lt.mpr (le_mul_of_one_le_left' h1))
  have hTs : ∀ j, T (j + 1) = 2 ^ q * T j := fun j => by rw [hT, hT, pow_succ]; ring
  have hU0 : ∀ t, μ (⋃ p, E t p) ≤ μ (D 0 i₀) := fun t =>
    measure_mono (iUnion_subset fun p x hx =>
      ((hMx _ _ _).mp ((hE _ _ _).mp hx).1).1 ((hE _ _ _).mp hx).2)
  have hUj : ∀ j, μ (⋃ p, E (T j) p) ≤ 2⁻¹ ^ j * μ (D 0 i₀) := by
    intro j
    induction j with
    | zero => rw [pow_zero, one_mul]; exact hU0 _
    | succ j ih =>
      rw [hTs]
      calc μ (⋃ p, E (2 ^ q * T j) p) ≤ 2⁻¹ * μ (⋃ p, E (T j) p) := hdecay _ (hTQ j)
        _ ≤ 2⁻¹ * (2⁻¹ ^ j * μ (D 0 i₀)) := mul_le_mul' le_rfl ih
        _ = 2⁻¹ ^ (j + 1) * μ (D 0 i₀) := by ring
  -- each cell of the top cell sits between two consecutive levels
  have hcell : ∀ k i, D k i ⊆ D 0 i₀ → μ (D k i) ≤
      (T 0 + ∑' j, T (j + 1) * (if B (T j) k i then 1 else 0)) * ENNReal.ofReal (S / 2 ^ k) := by
    intro k i hk
    by_cases h0 : B (T 0) k i
    · have hlam : μ (D 0 i₀) / ENNReal.ofReal (S / 2 ^ 0) ≠ 0 := by
        intro h
        rw [hB, hT, h, mul_zero, zero_mul] at h0
        rcases ENNReal.div_eq_zero_iff.mp h with h | h
        · exact absurd (lt_of_lt_of_le h0 (measure_mono hk)) (by rw [h]; exact lt_irrefl 0)
        · exact ENNReal.ofReal_ne_top h
      have hfk : μ (D k i) ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono hk)
      have hm0 : μ (D 0 i₀) / ENNReal.ofReal (S / 2 ^ 0) * ENNReal.ofReal (S / 2 ^ k) ≠ 0 :=
        mul_ne_zero hlam (hsne k)
      have hmt : μ (D 0 i₀) / ENNReal.ofReal (S / 2 ^ 0) * ENNReal.ofReal (S / 2 ^ k) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.div_ne_top hfin (hsne 0)) ENNReal.ofReal_ne_top
      have hex : ∃ j, ¬ B (T (j + 1)) k i := by
        obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top hfk hm0)
        refine ⟨n, ?_⟩
        rw [hB, not_lt, hT]
        have hpn : (n : ℝ≥0∞) ≤ (2 ^ q) ^ (n + 1) := by
          calc (n : ℝ≥0∞) ≤ 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self.le
            _ ≤ (2 ^ q) ^ (n + 1) := by
              rw [← pow_mul]
              exact pow_le_pow_right₀ one_le_two (by nlinarith)
        calc μ (D k i) = μ (D k i) / (μ (D 0 i₀) / ENNReal.ofReal (S / 2 ^ 0) *
              ENNReal.ofReal (S / 2 ^ k)) * (μ (D 0 i₀) / ENNReal.ofReal (S / 2 ^ 0) *
              ENNReal.ofReal (S / 2 ^ k)) := (ENNReal.div_mul_cancel hm0 hmt).symm
          _ ≤ (2 ^ q) ^ (n + 1) * (μ (D 0 i₀) / ENNReal.ofReal (S / 2 ^ 0) *
              ENNReal.ofReal (S / 2 ^ k)) := mul_le_mul' (hn.le.trans hpn) le_rfl
          _ = (2 ^ q) ^ (n + 1) * (μ (D 0 i₀) / ENNReal.ofReal (S / 2 ^ 0)) *
              ENNReal.ofReal (S / 2 ^ k) := by ring
      obtain ⟨m, hj, hmin⟩ : ∃ m, ¬ B (T (m + 1)) k i ∧ ∀ m' < m, ¬ ¬ B (T (m' + 1)) k i :=
        ⟨Nat.find hex, Nat.find_spec hex, fun m' hm' => Nat.find_min hex hm'⟩
      have hbj : B (T m) k i := by
        rcases m with _ | m
        · exact h0
        · exact not_not.mp (hmin m (Nat.lt_succ_self m))
      rw [hB, not_lt] at hj
      calc μ (D k i) ≤ T (m + 1) * ENNReal.ofReal (S / 2 ^ k) := hj
        _ = (T (m + 1) * (if B (T m) k i then 1 else 0)) *
            ENNReal.ofReal (S / 2 ^ k) := by simp only [hbj, ↓reduceIte, mul_one]
        _ ≤ (T 0 + ∑' j, T (j + 1) * (if B (T j) k i then 1 else 0)) *
            ENNReal.ofReal (S / 2 ^ k) :=
          mul_le_mul' (le_add_left (le_tsum (fun j => T (j + 1) *
            (if B (T j) k i then 1 else 0)) m)) le_rfl
    · rw [hB, not_lt] at h0
      exact h0.trans (mul_le_mul' le_self_add le_rfl)
  have hterm : ∀ p : ℕ × ℤ, c p.1 p.2 * (μ (D p.1 p.2) / ENNReal.ofReal (S / 2 ^ p.1)) ≤
      T 0 * c p.1 p.2 + ∑' j, T (j + 1) * (if B (T j) p.1 p.2 then c p.1 p.2 else 0) := by
    intro p
    by_cases hc : c p.1 p.2 = 0
    · rw [hc, zero_mul]; exact zero_le
    · have h := hcell p.1 p.2 (hc0 _ _ hc)
      rw [← ENNReal.div_le_iff (hsne _) ENNReal.ofReal_ne_top] at h
      calc c p.1 p.2 * (μ (D p.1 p.2) / ENNReal.ofReal (S / 2 ^ p.1))
          ≤ c p.1 p.2 * (T 0 + ∑' j, T (j + 1) * (if B (T j) p.1 p.2 then 1 else 0)) :=
            mul_le_mul' le_rfl h
        _ = T 0 * c p.1 p.2 + ∑' j, T (j + 1) * (if B (T j) p.1 p.2 then c p.1 p.2 else 0) := by
          rw [mul_add, ← ENNReal.tsum_mul_left, mul_comm (c p.1 p.2) (T 0)]
          congr 1
          refine tsum_congr (fun j => ?_)
          split_ifs <;> ring
  have hsumc : ∑' p : ℕ × ℤ, c p.1 p.2 ≤ N * ENNReal.ofReal (S / 2 ^ 0) := by
    refine le_trans (tsum_le_tsum (fun p => ?_)) (hcar 0 i₀ subset_rfl)
    by_cases hc : c p.1 p.2 = 0
    · rw [hc]; exact zero_le
    · exact (Set.indicator_of_mem
        (show p ∈ {q : ℕ × ℤ | D q.1 q.2 ⊆ D 0 i₀} from hc0 _ _ hc)
        (fun q : ℕ × ℤ => c q.1 q.2)).symm.le
  calc ∑' p : ℕ × ℤ, c p.1 p.2 * (μ (D p.1 p.2) / ENNReal.ofReal (S / 2 ^ p.1))
      ≤ ∑' p : ℕ × ℤ, (T 0 * c p.1 p.2 +
          ∑' j, T (j + 1) * (if B (T j) p.1 p.2 then c p.1 p.2 else 0)) := tsum_le_tsum hterm
    _ = T 0 * ∑' p : ℕ × ℤ, c p.1 p.2 +
          ∑' j, T (j + 1) * ∑' p : ℕ × ℤ, (if B (T j) p.1 p.2 then c p.1 p.2 else 0) := by
        rw [tsum_add, ENNReal.tsum_mul_left, tsum_comm]
        simp only [ENNReal.tsum_mul_left]
    _ ≤ T 0 * (N * ENNReal.ofReal (S / 2 ^ 0)) +
          ∑' j, T (j + 1) * (N * volume (⋃ p, E (T j) p)) :=
        add_le_add (mul_le_mul' le_rfl hsumc)
          (tsum_le_tsum (fun j => mul_le_mul' le_rfl (hCU _)))
    _ ≤ N * μ (D 0 i₀) + ∑' j : ℕ, 2 ^ q * N * (2⁻¹ ^ j * μ (D 0 i₀)) := by
        refine add_le_add (le_of_eq ?_) (tsum_le_tsum (fun j => ?_))
        · rw [hT, pow_zero, one_mul, mul_left_comm,
            ENNReal.div_mul_cancel (hsne 0) ENNReal.ofReal_ne_top]
        · calc T (j + 1) * (N * volume (⋃ p, E (T j) p)) =
                2 ^ q * N * (T j * volume (⋃ p, E (T j) p)) := by rw [hTs]; ring
            _ ≤ 2 ^ q * N * μ (⋃ p, E (T j) p) := mul_le_mul' le_rfl (hmuU _)
            _ ≤ 2 ^ q * N * (2⁻¹ ^ j * μ (D 0 i₀)) := mul_le_mul' le_rfl (hUj j)
    _ = (1 + 2 ^ (q + 1)) * N * μ (D 0 i₀) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
          ENNReal.one_sub_inv_two, inv_inv]
        ring

/-- Helper for `s07_tw_embed`: `s07_twe_stop` summed over the three top cells
`[α - S, α)`, `[α, α + S)`, `[α + S, α + 2S)`. -/
theorem s07_twe_top3 {μ : Measure ℝ} {α S : ℝ} (hS : 0 < S) {D : ℕ → ℤ → Set ℝ}
    (hD : ∀ k i, D k i = Ico (α + i * (S / 2 ^ k)) (α + (i + 1) * (S / 2 ^ k)))
    (hfin : ∀ i, μ (D 0 i) ≠ ⊤) {q : ℕ} (hq : 0 < q)
    (hdec : ∀ k i, D k i ⊆ Ico (α - S) (α + 2 * S) → ∀ A ⊆ D k i, MeasurableSet A →
      2 ^ q * volume A ≤ 2 * ENNReal.ofReal (S / 2 ^ k) → μ A ≤ 2⁻¹ * μ (D k i))
    (c : ℕ → ℤ → ℝ≥0∞) (N : ℝ≥0∞)
    (hc0 : ∀ k i, c k i ≠ 0 → D k i ⊆ Ico (α - S) (α + 2 * S))
    (hcar : ∀ g j, D g j ⊆ Ico (α - S) (α + 2 * S) → ∑' p : ℕ × ℤ,
      {p : ℕ × ℤ | D p.1 p.2 ⊆ D g j}.indicator (fun p => c p.1 p.2) p ≤
        N * ENNReal.ofReal (S / 2 ^ g)) :
    ∑' p : ℕ × ℤ, c p.1 p.2 * (μ (D p.1 p.2) / ENNReal.ofReal (S / 2 ^ p.1)) ≤
      (1 + 2 ^ (q + 1)) * N * μ (Ico (α - S) (α + 2 * S)) := by
  classical
  have hD0 : ∀ i : ℤ, D 0 i = Ico (α + i * S) (α + i * S + S) := fun i => by
    rw [hD, pow_zero, div_one]; congr 1; ring
  have e1 : D 0 (-1) = Ico (α - S) α := by rw [hD0]; push_cast; congr 1 <;> ring
  have e2 : D 0 0 = Ico α (α + S) := by rw [hD0]; push_cast; congr 1 <;> ring
  have e3 : D 0 1 = Ico (α + S) (α + 2 * S) := by rw [hD0]; push_cast; congr 1 <;> ring
  have hR : Ico (α - S) (α + 2 * S) = (D 0 (-1) ∪ D 0 0) ∪ D 0 1 := by
    rw [e1, e2, e3, Ico_union_Ico_eq_Ico (by linarith) (by linarith),
      Ico_union_Ico_eq_Ico (by linarith) (by linarith)]
  have htop : ∀ k i, D k i ⊆ Ico (α - S) (α + 2 * S) →
      D k i ⊆ D 0 (-1) ∨ D k i ⊆ D 0 0 ∨ D k i ⊆ D 0 1 := by
    intro k i hk
    have hs0 : 0 < S / 2 ^ k := by positivity
    have hx : α + i * (S / 2 ^ k) ∈ D k i := by
      rw [hD]
      have e : (↑i + 1) * (S / 2 ^ k) = ↑i * (S / 2 ^ k) + S / 2 ^ k := by ring
      exact ⟨le_rfl, by linarith⟩
    have hxR : α + i * (S / 2 ^ k) ∈ (D 0 (-1) ∪ D 0 0) ∪ D 0 1 := by rw [← hR]; exact hk hx
    rcases hxR with (h | h) | h
    · exact Or.inl (s07_twe_nest hS hD (Nat.zero_le k) hx h)
    · exact Or.inr (Or.inl (s07_twe_nest hS hD (Nat.zero_le k) hx h))
    · exact Or.inr (Or.inr (s07_twe_nest hS hD (Nat.zero_le k) hx h))
  have hone : ∀ i₀ : ℤ, D 0 i₀ ⊆ Ico (α - S) (α + 2 * S) →
      ∑' p : ℕ × ℤ, (if D p.1 p.2 ⊆ D 0 i₀ then c p.1 p.2 else 0) *
        (μ (D p.1 p.2) / ENNReal.ofReal (S / 2 ^ p.1)) ≤ (1 + 2 ^ (q + 1)) * N * μ (D 0 i₀) := by
    intro i₀ hi₀
    refine s07_twe_stop hS hD i₀ (hfin i₀) hq (fun k i hk => hdec k i (hk.trans hi₀))
      (fun k i => if D k i ⊆ D 0 i₀ then c k i else 0) N ?_ ?_
    · intro k i h
      by_contra h'
      exact h (by simp only [h', ↓reduceIte])
    · intro g j hg
      refine le_trans (tsum_le_tsum (fun p => ?_)) (hcar g j (hg.trans hi₀))
      by_cases h : D p.1 p.2 ⊆ D g j
      · simp only [Set.indicator_of_mem (show p ∈ {p : ℕ × ℤ | D p.1 p.2 ⊆ D g j} from h)]
        split_ifs <;> simp
      · simp only [Set.indicator_of_notMem (show p ∉ {p : ℕ × ℤ | D p.1 p.2 ⊆ D g j} from h),
          le_refl]
  have hsplit : ∀ p : ℕ × ℤ, c p.1 p.2 * (μ (D p.1 p.2) / ENNReal.ofReal (S / 2 ^ p.1)) ≤
      (if D p.1 p.2 ⊆ D 0 (-1) then c p.1 p.2 else 0) *
        (μ (D p.1 p.2) / ENNReal.ofReal (S / 2 ^ p.1)) +
      (if D p.1 p.2 ⊆ D 0 0 then c p.1 p.2 else 0) *
        (μ (D p.1 p.2) / ENNReal.ofReal (S / 2 ^ p.1)) +
      (if D p.1 p.2 ⊆ D 0 1 then c p.1 p.2 else 0) *
        (μ (D p.1 p.2) / ENNReal.ofReal (S / 2 ^ p.1)) := by
    intro p
    by_cases hc : c p.1 p.2 = 0
    · rw [hc, zero_mul]; exact zero_le
    · rw [← add_mul, ← add_mul]
      refine mul_le_mul' ?_ le_rfl
      rcases htop _ _ (hc0 _ _ hc) with h | h | h
      · simp only [h, ↓reduceIte]; exact le_self_add.trans le_self_add
      · simp only [h, ↓reduceIte]; exact le_add_self.trans le_self_add
      · simp only [h, ↓reduceIte]; exact le_add_self
  have m1 : μ (Ico (α - S) (α + 2 * S)) = μ (Ico (α - S) (α + S)) + μ (D 0 1) := by
    rw [← Ico_union_Ico_eq_Ico (a := α - S) (b := α + S) (c := α + 2 * S) (by linarith)
      (by linarith), e3]
    exact measure_union Ico_disjoint_Ico_same measurableSet_Ico
  have m2 : μ (Ico (α - S) (α + S)) = μ (D 0 (-1)) + μ (D 0 0) := by
    rw [← Ico_union_Ico_eq_Ico (a := α - S) (b := α) (c := α + S) (by linarith) (by linarith),
      e1, e2]
    exact measure_union Ico_disjoint_Ico_same measurableSet_Ico
  refine (tsum_le_tsum hsplit).trans ?_
  rw [tsum_add, tsum_add]
  refine (add_le_add (add_le_add (hone _ ?_) (hone _ ?_)) (hone _ ?_)).trans (le_of_eq ?_)
  · rw [hR]; exact subset_union_left.trans subset_union_left
  · rw [hR]; exact subset_union_right.trans subset_union_left
  · rw [hR]; exact subset_union_right
  · rw [m1, m2]; ring

/-- thm_TWS T4 (Semmes Lemma 4.8, Carleson embedding + localized Fujii–Wilson): for an `A∞`
measure `μ` (power form on intervals of length `≤ ℓ`) and a Carleson measure `ν` on `ℝ × ℝ`, the
averages `μ([t - s, t + s]) / 2s` integrate over the box on `I` to at most `K N μ(3I)`. -/
theorem s07_tw_embed (C δ ℓ : ℝ) (hC : 0 < C) (hδ : 0 < δ) (hℓ : 0 < ℓ) : ∃ K : ℝ, 0 < K ∧
    ∀ μ : Measure ℝ, (∀ a b : ℝ, μ (Icc a b) ≠ ⊤) →
      (∀ a b : ℝ, a < b → b - a ≤ ℓ → ∀ A ⊆ Icc a b, MeasurableSet A →
        μ A ≤ ENNReal.ofReal (C * ((volume A).toReal / (b - a)) ^ δ) * μ (Icc a b)) →
      ∀ ν : Measure (ℝ × ℝ), ∀ N : ℝ≥0∞,
        (∀ a b : ℝ, a < b → b - a ≤ ℓ → ν (Icc a b ×ˢ Ioc 0 (b - a)) ≤ N * ENNReal.ofReal (b - a)) →
        ∀ a b : ℝ, a < b → 3 * (b - a) ≤ ℓ →
          ∫⁻ p in Icc a b ×ˢ Ioc 0 (b - a), μ (Icc (p.1 - p.2) (p.1 + p.2)) / ENNReal.ofReal (2 * p.2) ∂ν ≤
            ENNReal.ofReal K * N * μ (Icc (a - (b - a)) (b + (b - a))) := by
  classical
  -- `0 < ℓ` is not needed: it follows from `a < b` and `3 * (b - a) ≤ ℓ` below
  have _h := hℓ
  -- the stopping ratio `2 ^ q`: `C (2 / 2 ^ q) ^ δ < 1 / 2`
  have hlim : Tendsto (fun q : ℕ => C * ((2 : ℝ) / 2 ^ q) ^ δ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun q : ℕ => (2 : ℝ) / 2 ^ q) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul 2
      rw [mul_zero] at this
      refine this.congr (fun q => ?_)
      rw [div_pow, one_pow]; ring
    have h2 := ((Real.continuous_rpow_const hδ.le).tendsto 0).comp h1
    rw [Real.zero_rpow hδ.ne'] at h2
    have h3 := h2.const_mul C
    rw [mul_zero] at h3
    exact h3
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  have hq : 0 < q₀ + 1 := Nat.succ_pos _
  have hCq : C * ((2 : ℝ) / 2 ^ (q₀ + 1)) ^ δ < 1 / 2 := hq₀ (q₀ + 1) (Nat.le_succ _)
  refine ⟨9 * (1 + 2 ^ (q₀ + 1 + 1)), by positivity, ?_⟩
  intro μ hμfin hpow ν N hcar a b hab hℓ3
  obtain ⟨L, rfl⟩ : ∃ L, b = a + L := ⟨b - a, by ring⟩
  simp only [add_sub_cancel_left] at hℓ3 ⊢
  have hL : 0 < L := by linarith
  -- `μ` has no atoms
  have hpt : ∀ y, μ {y} = 0 := by
    intro y
    have h := hpow y (y + ℓ) (by linarith) (by linarith) {y}
      (fun z hz => by rw [mem_singleton_iff.mp hz]; exact ⟨le_rfl, by linarith⟩)
      (measurableSet_singleton y)
    rw [Real.volume_singleton, ENNReal.toReal_zero, zero_div, Real.zero_rpow hδ.ne', mul_zero,
      ENNReal.ofReal_zero, zero_mul] at h
    exact le_antisymm h zero_le
  -- the grid on `3I` and its Whitney pieces over `I`
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℤ → Set ℝ,
      ∀ k i, D k i = Ico (a + i * (L / 2 ^ k)) (a + (i + 1) * (L / 2 ^ k)) :=
    ⟨fun k i => Ico (a + i * (L / 2 ^ k)) (a + (i + 1) * (L / 2 ^ k)), fun _ _ => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ → ℤ → Set (ℝ × ℝ), ∀ k i, W k i =
      {t | t ∈ Icc a (a + L) ∧ min ⌊(t - a) / (L / 2 ^ k)⌋ (2 ^ k - 1) = i} ×ˢ
        Ioc (L / 2 ^ k / 2) (L / 2 ^ k) :=
    ⟨fun k i => {t | t ∈ Icc a (a + L) ∧ min ⌊(t - a) / (L / 2 ^ k)⌋ (2 ^ k - 1) = i} ×ˢ
        Ioc (L / 2 ^ k / 2) (L / 2 ^ k), fun _ _ => rfl⟩
  have hfin : ∀ i, μ (D 0 i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (hμfin (a + i * (L / 2 ^ 0)) (a + (i + 1) * (L / 2 ^ 0)))
      (measure_mono (by rw [hD]; exact Ico_subset_Icc_self))
  -- decay of `μ` on the cells, from the power form
  have hdec : ∀ k i, ∀ A ⊆ D k i, MeasurableSet A →
      2 ^ (q₀ + 1) * volume A ≤ 2 * ENNReal.ofReal (L / 2 ^ k) → μ A ≤ 2⁻¹ * μ (D k i) := by
    intro k i A hA hAm hvA
    have hs0 : 0 < L / 2 ^ k := by positivity
    have hsL : L / 2 ^ k ≤ L := div_le_self hL.le (one_le_pow₀ one_le_two)
    have hA' : A ⊆ Icc (a + i * (L / 2 ^ k)) (a + (i + 1) * (L / 2 ^ k)) :=
      hA.trans (by rw [hD]; exact Ico_subset_Icc_self)
    have hlen : a + (i + 1) * (L / 2 ^ k) - (a + i * (L / 2 ^ k)) = L / 2 ^ k := by ring
    have h := hpow _ _ (by linarith) (by rw [hlen]; linarith) A hA' hAm
    rw [hlen] at h
    have hvt : volume A ≠ ⊤ :=
      ((measure_mono hA).trans_lt (by rw [hD]; exact measure_Ico_lt_top)).ne
    have hv : 2 ^ (q₀ + 1) * (volume A).toReal ≤ 2 * (L / 2 ^ k) := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        hvA
      rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
        ENNReal.toReal_ofReal hs0.le] at this
    have hx : (volume A).toReal / (L / 2 ^ k) ≤ 2 / 2 ^ (q₀ + 1) := by
      rw [div_le_div_iff₀ hs0 (by positivity)]
      linarith [mul_comm (volume A).toReal (2 ^ (q₀ + 1))]
    have hrp : ((volume A).toReal / (L / 2 ^ k)) ^ δ ≤ (2 / 2 ^ (q₀ + 1)) ^ δ :=
      Real.rpow_le_rpow (div_nonneg ENNReal.toReal_nonneg hs0.le) hx hδ.le
    have hIcc : μ (Icc (a + i * (L / 2 ^ k)) (a + (i + 1) * (L / 2 ^ k))) ≤ μ (D k i) := by
      calc μ (Icc (a + i * (L / 2 ^ k)) (a + (i + 1) * (L / 2 ^ k)))
          ≤ μ (D k i ∪ {a + (i + 1) * (L / 2 ^ k)}) := by
            refine measure_mono (fun y hy => ?_)
            rw [hD]
            rcases eq_or_lt_of_le hy.2 with h | h
            · exact Or.inr h
            · exact Or.inl ⟨hy.1, h⟩
        _ ≤ μ (D k i) + μ {a + (i + 1) * (L / 2 ^ k)} := measure_union_le _ _
        _ = μ (D k i) := by rw [hpt, add_zero]
    calc μ A ≤ ENNReal.ofReal (C * ((volume A).toReal / (L / 2 ^ k)) ^ δ) *
          μ (Icc (a + i * (L / 2 ^ k)) (a + (i + 1) * (L / 2 ^ k))) := h
      _ ≤ 2⁻¹ * μ (D k i) := by
        refine mul_le_mul' ?_ hIcc
        calc ENNReal.ofReal (C * ((volume A).toReal / (L / 2 ^ k)) ^ δ)
            ≤ ENNReal.ofReal (1 / 2) :=
              ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left hrp hC.le).trans hCq.le)
          _ = 2⁻¹ := by
              rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  -- the Whitney pieces
  have hWloc : ∀ k i p, p ∈ W k i → a + i * (L / 2 ^ k) ≤ p.1 ∧
      p.1 ≤ a + i * (L / 2 ^ k) + L / 2 ^ k ∧ 0 ≤ i ∧ i ≤ 2 ^ k - 1 ∧
      L / 2 ^ k / 2 < p.2 ∧ p.2 ≤ L / 2 ^ k := by
    intro k i p hp
    rw [hW, mem_prod] at hp
    obtain ⟨⟨⟨ht1, ht2⟩, hi⟩, hs1, hs2⟩ := hp
    have hs0 : 0 < L / 2 ^ k := by positivity
    have hLk : (2 : ℝ) ^ k * (L / 2 ^ k) = L := by field_simp
    obtain ⟨f, hfdef⟩ : ∃ f : ℤ, f = ⌊(p.1 - a) / (L / 2 ^ k)⌋ := ⟨_, rfl⟩
    have hf1 := Int.floor_le ((p.1 - a) / (L / 2 ^ k))
    have hf2 := Int.lt_floor_add_one ((p.1 - a) / (L / 2 ^ k))
    have hf0 : 0 ≤ ⌊(p.1 - a) / (L / 2 ^ k)⌋ :=
      Int.floor_nonneg.mpr (div_nonneg (by linarith) hs0.le)
    rw [le_div_iff₀ hs0] at hf1
    rw [div_lt_iff₀ hs0] at hf2
    rw [← hfdef] at hi hf1 hf2 hf0
    have hk1 : (0 : ℤ) ≤ 2 ^ k - 1 := by
      have : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      linarith
    have hi1 : i ≤ f := by rw [← hi]; exact min_le_left _ _
    have hi2 : i ≤ 2 ^ k - 1 := by rw [← hi]; exact min_le_right _ _
    have hi0 : 0 ≤ i := by rw [← hi]; exact le_min hf0 hk1
    have hif : (i : ℝ) ≤ f := by exact_mod_cast hi1
    refine ⟨by linarith [mul_le_mul_of_nonneg_right hif hs0.le], ?_, hi0, hi2, hs1, hs2⟩
    rcases min_choice f (2 ^ k - 1) with h | h
    · have hif' : i = f := hi.symm.trans h
      subst hif'
      linarith [show ((i : ℝ) + 1) * (L / 2 ^ k) = i * (L / 2 ^ k) + L / 2 ^ k by ring]
    · have hi' : (i : ℝ) = 2 ^ k - 1 := by rw [← hi, h]; push_cast; ring
      rw [hi']
      linarith [show ((2 : ℝ) ^ k - 1) * (L / 2 ^ k) = 2 ^ k * (L / 2 ^ k) - L / 2 ^ k by ring]
  have hWmeas : ∀ k i, MeasurableSet (W k i) := by
    intro k i
    rw [hW]
    refine MeasurableSet.prod ?_ measurableSet_Ioc
    have hf : Measurable fun t : ℝ => min ⌊(t - a) / (L / 2 ^ k)⌋ ((2 : ℤ) ^ k - 1) :=
      (measurable_of_countable (fun z : ℤ => min z ((2 : ℤ) ^ k - 1))).comp
        (Int.measurable_floor.comp ((measurable_id.sub_const a).div_const _))
    exact measurableSet_Icc.inter (hf (measurableSet_singleton i))
  have hWdisj : Pairwise (Function.onFun Disjoint fun p : ℕ × ℤ => W p.1 p.2) := by
    intro p p' hpp'
    show Disjoint (W p.1 p.2) (W p'.1 p'.2)
    rw [Set.disjoint_left]
    intro x hx hx'
    have l1 := hWloc _ _ _ hx
    have l2 := hWloc _ _ _ hx'
    rcases lt_trichotomy p.1 p'.1 with h | h | h
    · have : L / 2 ^ p'.1 ≤ L / 2 ^ p.1 / 2 := by
        rw [div_div, ← pow_succ]
        exact div_le_div_of_nonneg_left hL.le (by positivity) (pow_le_pow_right₀ one_le_two h)
      linarith [l1.2.2.2.2.1, l2.2.2.2.2.2]
    · apply hpp'
      rw [hW, mem_prod] at hx hx'
      refine Prod.ext h ?_
      rw [← hx.1.2, ← hx'.1.2, h]
    · have : L / 2 ^ p.1 ≤ L / 2 ^ p'.1 / 2 := by
        rw [div_div, ← pow_succ]
        exact div_le_div_of_nonneg_left hL.le (by positivity) (pow_le_pow_right₀ one_le_two h)
      linarith [l2.2.2.2.2.1, l1.2.2.2.2.2]
  have hcover : Icc a (a + L) ×ˢ Ioc 0 L ⊆ ⋃ p : ℕ × ℤ, W p.1 p.2 := by
    intro p hp
    rw [mem_prod] at hp
    obtain ⟨ht, hs⟩ := hp
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (L / p.2) (by norm_num : (1 : ℝ) < 2)
    have hP : ∃ k : ℕ, L / 2 ^ k / 2 < p.2 := by
      refine ⟨n, ?_⟩
      rw [div_lt_iff₀ hs.1] at hn
      rw [div_div, div_lt_iff₀ (by positivity)]
      linarith [show p.2 * (2 ^ n * 2) = 2 * (2 ^ n * p.2) by ring,
        mul_pos (pow_pos (two_pos : (0 : ℝ) < 2) n) hs.1]
    have hk2 : p.2 ≤ L / 2 ^ Nat.find hP := by
      rcases Nat.eq_zero_or_pos (Nat.find hP) with h | h
      · rw [h, pow_zero, div_one]; exact hs.2
      · have := Nat.find_min hP (Nat.sub_lt h one_pos)
        rw [not_lt] at this
        calc p.2 ≤ L / 2 ^ (Nat.find hP - 1) / 2 := this
          _ = L / 2 ^ Nat.find hP := by rw [div_div, ← pow_succ, Nat.sub_add_cancel h]
    refine mem_iUnion.mpr ⟨(Nat.find hP,
      min ⌊(p.1 - a) / (L / 2 ^ Nat.find hP)⌋ (2 ^ Nat.find hP - 1)), ?_⟩
    rw [hW, mem_prod]
    exact ⟨⟨ht, rfl⟩, Nat.find_spec hP, hk2⟩
  -- the integrand on a Whitney piece is at most the averages over the three neighbours
  have hint : ∀ k i p, p ∈ W k i → μ (Icc (p.1 - p.2) (p.1 + p.2)) / ENNReal.ofReal (2 * p.2) ≤
      (μ (D k (i + -1)) + μ (D k (i + 0)) + μ (D k (i + 1))) / ENNReal.ofReal (L / 2 ^ k) := by
    intro k i p hp
    obtain ⟨h1, h2, -, -, h5, h6⟩ := hWloc k i p hp
    have hs0 : 0 < L / 2 ^ k := by positivity
    have hDe : ∀ e : ℤ, D k (i + e) = Ico (a + i * (L / 2 ^ k) + e * (L / 2 ^ k))
        (a + i * (L / 2 ^ k) + e * (L / 2 ^ k) + L / 2 ^ k) := fun e => by
      rw [hD]; push_cast; congr 1 <;> ring
    have hsub : Icc (p.1 - p.2) (p.1 + p.2) ⊆ (D k (i + -1) ∪ D k (i + 0) ∪ D k (i + 1)) ∪
        {a + i * (L / 2 ^ k) + 2 * (L / 2 ^ k)} := by
      intro y hy
      obtain ⟨hy1, hy2⟩ := hy
      rw [hDe, hDe, hDe]
      push_cast
      simp only [mem_union, mem_Ico, mem_singleton_iff]
      rcases lt_or_ge y (a + i * (L / 2 ^ k)) with c1 | c1
      · exact Or.inl (Or.inl (Or.inl ⟨by linarith, by linarith⟩))
      rcases lt_or_ge y (a + i * (L / 2 ^ k) + L / 2 ^ k) with c2 | c2
      · exact Or.inl (Or.inl (Or.inr ⟨by linarith, by linarith⟩))
      rcases lt_or_ge y (a + i * (L / 2 ^ k) + 2 * (L / 2 ^ k)) with c3 | c3
      · exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)
      · exact Or.inr (le_antisymm (by linarith) c3)
    calc μ (Icc (p.1 - p.2) (p.1 + p.2)) / ENNReal.ofReal (2 * p.2)
        ≤ μ (Icc (p.1 - p.2) (p.1 + p.2)) / ENNReal.ofReal (L / 2 ^ k) :=
          ENNReal.div_le_div_left (ENNReal.ofReal_le_ofReal (by linarith)) _
      _ ≤ _ := by
        refine ENNReal.div_le_div_right ?_ _
        calc μ (Icc (p.1 - p.2) (p.1 + p.2))
            ≤ μ ((D k (i + -1) ∪ D k (i + 0) ∪ D k (i + 1)) ∪
              {a + i * (L / 2 ^ k) + 2 * (L / 2 ^ k)}) := measure_mono hsub
          _ ≤ μ (D k (i + -1) ∪ D k (i + 0) ∪ D k (i + 1)) +
              μ {a + i * (L / 2 ^ k) + 2 * (L / 2 ^ k)} := measure_union_le _ _
          _ ≤ μ (D k (i + -1)) + μ (D k (i + 0)) + μ (D k (i + 1)) := by
            rw [hpt, add_zero]
            exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
  have hmain1 : ∫⁻ p in Icc a (a + L) ×ˢ Ioc 0 L,
      μ (Icc (p.1 - p.2) (p.1 + p.2)) / ENNReal.ofReal (2 * p.2) ∂ν ≤
      ∑' p : ℕ × ℤ, (μ (D p.1 (p.2 + -1)) + μ (D p.1 (p.2 + 0)) + μ (D p.1 (p.2 + 1))) /
        ENNReal.ofReal (L / 2 ^ p.1) * ν (W p.1 p.2) := by
    calc ∫⁻ p in Icc a (a + L) ×ˢ Ioc 0 L,
          μ (Icc (p.1 - p.2) (p.1 + p.2)) / ENNReal.ofReal (2 * p.2) ∂ν
        ≤ ∫⁻ p in ⋃ p : ℕ × ℤ, W p.1 p.2,
          μ (Icc (p.1 - p.2) (p.1 + p.2)) / ENNReal.ofReal (2 * p.2) ∂ν := lintegral_mono_set hcover
      _ ≤ ∑' p : ℕ × ℤ, ∫⁻ x in W p.1 p.2,
          μ (Icc (x.1 - x.2) (x.1 + x.2)) / ENNReal.ofReal (2 * x.2) ∂ν := lintegral_iUnion_le _ _
      _ ≤ _ := by
        refine tsum_le_tsum (fun p => ?_)
        calc ∫⁻ x in W p.1 p.2, μ (Icc (x.1 - x.2) (x.1 + x.2)) / ENNReal.ofReal (2 * x.2) ∂ν
            ≤ ∫⁻ _ in W p.1 p.2, (μ (D p.1 (p.2 + -1)) + μ (D p.1 (p.2 + 0)) +
                μ (D p.1 (p.2 + 1))) / ENNReal.ofReal (L / 2 ^ p.1) ∂ν :=
              setLIntegral_mono measurable_const (fun x hx => hint _ _ x hx)
          _ = _ := setLIntegral_const _ _
  have hshift : ∀ e : ℤ, ∑' p : ℕ × ℤ, μ (D p.1 (p.2 + e)) / ENNReal.ofReal (L / 2 ^ p.1) *
      ν (W p.1 p.2) = ∑' p : ℕ × ℤ, ν (W p.1 (p.2 - e)) *
        (μ (D p.1 p.2) / ENNReal.ofReal (L / 2 ^ p.1)) := by
    intro e
    refine Eq.trans ?_ (Equiv.tsum_eq (Equiv.prodCongr (Equiv.refl ℕ) (Equiv.addRight e))
      (fun p : ℕ × ℤ => ν (W p.1 (p.2 - e)) * (μ (D p.1 p.2) / ENNReal.ofReal (L / 2 ^ p.1))))
    refine tsum_congr (fun p => ?_)
    simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.coe_addRight, Prod.map_fst,
      Prod.map_snd, id_eq, add_sub_cancel_right]
    rw [mul_comm]
  -- each shifted sum is a Carleson embedding on the grid of `3I`
  have hE : ∀ e : ℤ, -1 ≤ e → e ≤ 1 → ∑' p : ℕ × ℤ, ν (W p.1 (p.2 - e)) *
      (μ (D p.1 p.2) / ENNReal.ofReal (L / 2 ^ p.1)) ≤
        (1 + 2 ^ (q₀ + 1 + 1)) * (3 * N) * μ (Ico (a - L) (a + 2 * L)) := by
    intro e he1 he2
    have he1' : (-1 : ℝ) ≤ e := by exact_mod_cast he1
    have he2' : (e : ℝ) ≤ 1 := by exact_mod_cast he2
    refine s07_twe_top3 hL hD hfin hq (fun k i _ => hdec k i) (fun k i => ν (W k (i - e)))
      (3 * N) ?_ ?_
    · intro k i h
      obtain ⟨x, hx⟩ : (W k (i - e)).Nonempty :=
        nonempty_iff_ne_empty.mpr (fun h' => h (by rw [h', measure_empty]))
      obtain ⟨-, -, h0, h1, -, -⟩ := hWloc _ _ _ hx
      have hs0 : 0 < L / 2 ^ k := by positivity
      have hLk : (2 : ℝ) ^ k * (L / 2 ^ k) = L := by field_simp
      have c0 : (-1 : ℝ) ≤ i := by
        have : (-1 : ℤ) ≤ i := by linarith
        exact_mod_cast this
      have c1 : (i : ℝ) ≤ 2 ^ k := by
        have : i ≤ 2 ^ k := by linarith
        exact_mod_cast this
      rw [hD]
      apply Ico_subset_Ico
      · linarith [mul_le_mul_of_nonneg_right c0 hs0.le,
          div_le_self hL.le (one_le_pow₀ (one_le_two : (1 : ℝ) ≤ 2) (n := k))]
      · linarith [mul_le_mul_of_nonneg_right c1 hs0.le,
          div_le_self hL.le (one_le_pow₀ (one_le_two : (1 : ℝ) ≤ 2) (n := k)),
          show ((i : ℝ) + 1) * (L / 2 ^ k) = i * (L / 2 ^ k) + L / 2 ^ k by ring]
    · intro g j _
      have hsg : 0 < L / 2 ^ g := by positivity
      have hsgL : L / 2 ^ g ≤ L := div_le_self hL.le (one_le_pow₀ one_le_two)
      obtain ⟨V, hV⟩ : ∃ V : ℕ × ℤ → Set (ℝ × ℝ),
          ∀ p, V p = if D p.1 p.2 ⊆ D g j then W p.1 (p.2 - e) else ∅ :=
        ⟨fun p => if D p.1 p.2 ⊆ D g j then W p.1 (p.2 - e) else ∅, fun _ => rfl⟩
      have hVm : ∀ p, MeasurableSet (V p) := fun p => by
        rw [hV]; split_ifs
        · exact hWmeas _ _
        · exact MeasurableSet.empty
      have hVd : Pairwise (Function.onFun Disjoint V) := by
        intro p p' hpp'
        show Disjoint (V p) (V p')
        rw [hV, hV]
        split_ifs
        · exact @hWdisj (p.1, p.2 - e) (p'.1, p'.2 - e) (fun h => hpp' (by
            simp only [Prod.mk.injEq, sub_left_inj] at h; exact Prod.ext h.1 h.2))
        all_goals simp
      have hsum : ∑' p : ℕ × ℤ, {p : ℕ × ℤ | D p.1 p.2 ⊆ D g j}.indicator
          (fun p => ν (W p.1 (p.2 - e))) p = ν (⋃ p, V p) := by
        rw [measure_iUnion hVd hVm]
        refine tsum_congr (fun p => ?_)
        rw [hV]
        by_cases h : D p.1 p.2 ⊆ D g j
        · rw [Set.indicator_of_mem (show p ∈ {p : ℕ × ℤ | D p.1 p.2 ⊆ D g j} from h)]
          simp only [h, ↓reduceIte]
        · rw [Set.indicator_of_notMem (show p ∉ {p : ℕ × ℤ | D p.1 p.2 ⊆ D g j} from h)]
          simp only [h, ↓reduceIte, measure_empty]
      have hbox : (⋃ p, V p) ⊆ Icc (a + j * (L / 2 ^ g) - L / 2 ^ g)
          (a + j * (L / 2 ^ g) + 2 * (L / 2 ^ g)) ×ˢ Ioc 0 (a + j * (L / 2 ^ g) +
            2 * (L / 2 ^ g) - (a + j * (L / 2 ^ g) - L / 2 ^ g)) := by
        intro x hx
        obtain ⟨p, hp⟩ := mem_iUnion.mp hx
        rw [hV] at hp
        split_ifs at hp with h
        · obtain ⟨l1, l2, -, -, l5, l6⟩ := hWloc _ _ _ hp
          have hs0 : 0 < L / 2 ^ p.1 := by positivity
          rw [hD, hD, Ico_subset_Ico_iff (by linarith [show ((p.2 : ℝ) + 1) * (L / 2 ^ p.1) =
            p.2 * (L / 2 ^ p.1) + L / 2 ^ p.1 by ring])] at h
          obtain ⟨h1, h2⟩ := h
          push_cast at l1 l2
          have E1 : ((p.2 : ℝ) + 1) * (L / 2 ^ p.1) = p.2 * (L / 2 ^ p.1) + L / 2 ^ p.1 := by ring
          have E2 : ((j : ℝ) + 1) * (L / 2 ^ g) = j * (L / 2 ^ g) + L / 2 ^ g := by ring
          have E3 : ((p.2 : ℝ) - e) * (L / 2 ^ p.1) = p.2 * (L / 2 ^ p.1) - e * (L / 2 ^ p.1) := by
            ring
          have B1 := mul_le_mul_of_nonneg_right he1' hs0.le
          have B2 := mul_le_mul_of_nonneg_right he2' hs0.le
          rw [mem_prod, mem_Icc, mem_Ioc]
          refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
        · exact absurd hp (notMem_empty x)
      have hC := hcar (a + j * (L / 2 ^ g) - L / 2 ^ g) (a + j * (L / 2 ^ g) + 2 * (L / 2 ^ g))
        (by linarith) (by linarith)
      refine le_trans (le_of_eq hsum) ((measure_mono hbox).trans (hC.trans (le_of_eq ?_)))
      rw [show a + j * (L / 2 ^ g) + 2 * (L / 2 ^ g) - (a + j * (L / 2 ^ g) - L / 2 ^ g) =
        3 * (L / 2 ^ g) by ring, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      ring
  have hK : ENNReal.ofReal (9 * (1 + 2 ^ (q₀ + 1 + 1))) = 9 * (1 + 2 ^ (q₀ + 1 + 1)) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by norm_num) (by positivity),
      ENNReal.ofReal_one, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_ofNat]
  have hR : μ (Ico (a - L) (a + 2 * L)) ≤ μ (Icc (a - L) (a + L + L)) :=
    measure_mono (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl (by linarith)))
  calc ∫⁻ p in Icc a (a + L) ×ˢ Ioc 0 L,
        μ (Icc (p.1 - p.2) (p.1 + p.2)) / ENNReal.ofReal (2 * p.2) ∂ν
      ≤ ∑' p : ℕ × ℤ, (μ (D p.1 (p.2 + -1)) + μ (D p.1 (p.2 + 0)) + μ (D p.1 (p.2 + 1))) /
        ENNReal.ofReal (L / 2 ^ p.1) * ν (W p.1 p.2) := hmain1
    _ = ∑' p : ℕ × ℤ, μ (D p.1 (p.2 + -1)) / ENNReal.ofReal (L / 2 ^ p.1) * ν (W p.1 p.2) +
        ∑' p : ℕ × ℤ, μ (D p.1 (p.2 + 0)) / ENNReal.ofReal (L / 2 ^ p.1) * ν (W p.1 p.2) +
        ∑' p : ℕ × ℤ, μ (D p.1 (p.2 + 1)) / ENNReal.ofReal (L / 2 ^ p.1) * ν (W p.1 p.2) := by
      rw [← tsum_add, ← tsum_add]
      refine tsum_congr (fun p => ?_)
      rw [ENNReal.add_div, ENNReal.add_div, add_mul, add_mul]
    _ = ∑' p : ℕ × ℤ, ν (W p.1 (p.2 - -1)) * (μ (D p.1 p.2) / ENNReal.ofReal (L / 2 ^ p.1)) +
        ∑' p : ℕ × ℤ, ν (W p.1 (p.2 - 0)) * (μ (D p.1 p.2) / ENNReal.ofReal (L / 2 ^ p.1)) +
        ∑' p : ℕ × ℤ, ν (W p.1 (p.2 - 1)) * (μ (D p.1 p.2) / ENNReal.ofReal (L / 2 ^ p.1)) := by
      rw [hshift, hshift, hshift]
    _ ≤ (1 + 2 ^ (q₀ + 1 + 1)) * (3 * N) * μ (Ico (a - L) (a + 2 * L)) +
        (1 + 2 ^ (q₀ + 1 + 1)) * (3 * N) * μ (Ico (a - L) (a + 2 * L)) +
        (1 + 2 ^ (q₀ + 1 + 1)) * (3 * N) * μ (Ico (a - L) (a + 2 * L)) :=
      add_le_add (add_le_add (hE _ (by norm_num) (by norm_num))
        (hE _ (by norm_num) (by norm_num))) (hE _ (by norm_num) (by norm_num))
    _ = ENNReal.ofReal (9 * (1 + 2 ^ (q₀ + 1 + 1))) * N * μ (Ico (a - L) (a + 2 * L)) := by
      rw [hK]; ring
    _ ≤ ENNReal.ofReal (9 * (1 + 2 ^ (q₀ + 1 + 1))) * N * μ (Icc (a - L) (a + L + L)) :=
      mul_le_mul' le_rfl hR

/-- Helper for `s07_tw_boxbound`: the pointwise bound behind the change of variables: if
`ϖ(z) ≤ C_r V` then `|∂ψ(z)| ≤ 4 L C_r V/(2β(ψ z)) |det Dψ(z)|` (T1, T2, `β ≤ 2ϖ`). -/
theorem s07_tw_pt {ψ : ℂ → ℂ} {L : ℝ} (hψ : MapsTo ψ unitDisc unitDisc) (hL : IsDiskBiLip ψ L)
    {z : ℂ} (hz : z ∈ unitDisc) (hd : DifferentiableAt ℝ ψ z) {V : ℝ≥0∞} {Cr : ℝ} (hCr : 0 < Cr)
    (hv : ENNReal.ofReal (varpi z) ≤ ENNReal.ofReal Cr * V) :
    ‖dzC ψ z‖ₑ ≤ ENNReal.ofReal (4 * L * Cr) *
      (V / ENNReal.ofReal (2 * (2 * Real.arctan ((1 - ‖ψ z‖) / (1 + ‖ψ z‖))))) *
        ENNReal.ofReal |(fderiv ℝ ψ z).det| := by
  obtain ⟨hL1, -⟩ := s07_tw_bilip_qi hψ hL
  have hw : ψ z ∈ unitDisc := hψ hz
  have hvz := s07_varpi_pos hz
  have hvw := s07_varpi_pos hw
  have hn0 : 0 ≤ ‖ψ z‖ := norm_nonneg _
  have hn1 : ‖ψ z‖ < 1 := mem_ball_zero_iff.mp hw
  obtain ⟨hβ0, hβ2⟩ := s07_tw_beta_le hn0 hn1
  obtain ⟨β, hβd⟩ : ∃ β : ℝ, β = 2 * Real.arctan ((1 - ‖ψ z‖) / (1 + ‖ψ z‖)) := ⟨_, rfl⟩
  rw [← hβd] at hβ0 hβ2 ⊢
  have hβϖ : β / 2 ≤ varpi (ψ z) := by
    unfold varpi
    nlinarith
  obtain ⟨D, hDd⟩ : ∃ D : ℂ →L[ℝ] ℂ, D = fderiv ℝ ψ z := ⟨_, rfl⟩
  rw [← hDd]
  have hLz : 0 < L * varpi z := mul_pos (by linarith) hvz
  have hm : ∀ v : ℂ, varpi (ψ z) / (L * varpi z) * ‖v‖ ≤ ‖D v‖ := by
    intro v
    rw [div_mul_eq_mul_div, div_le_iff₀ hLz]
    have := (s07_tw_inf hψ hL hz hd v).1
    rw [← hDd] at this
    linarith
  have hj := (s07_tw_jac D (m := varpi (ψ z) / (L * varpi z)) (M := 0)).1 hm
  rw [div_mul_eq_mul_div, div_le_iff₀ hLz] at hj
  have ha : ‖dzC ψ z‖ ≤ L / varpi (ψ z) * |D.det| * varpi z := by
    show ‖(fderiv ℝ ψ z 1 - I * fderiv ℝ ψ z I) / 2‖ ≤ _
    rw [← hDd, show L / varpi (ψ z) * |D.det| * varpi z = L * varpi z * |D.det| / varpi (ψ z) by
      ring, le_div_iff₀ hvw]
    linarith
  have hA0 : 0 ≤ L / varpi (ψ z) * |D.det| := mul_nonneg (div_nonneg (by linarith) hvw.le) (abs_nonneg _)
  have hreal : L / varpi (ψ z) * |D.det| * Cr ≤ 4 * L * Cr * (2 * β)⁻¹ * |D.det| := by
    have hinv : 1 / varpi (ψ z) ≤ 1 / (β / 2) := one_div_le_one_div_of_le (by linarith) hβϖ
    have hX : 0 ≤ |D.det| * L * Cr := mul_nonneg (mul_nonneg (abs_nonneg _) (by linarith)) hCr.le
    have := mul_le_mul_of_nonneg_left hinv hX
    calc L / varpi (ψ z) * |D.det| * Cr = |D.det| * L * Cr * (1 / varpi (ψ z)) := by ring
      _ ≤ |D.det| * L * Cr * (1 / (β / 2)) := this
      _ = 4 * L * Cr * (2 * β)⁻¹ * |D.det| := by rw [one_div_div]; ring
  have h4 : 0 ≤ 4 * L * Cr := by have := hCr.le; nlinarith
  calc ‖dzC ψ z‖ₑ = ENNReal.ofReal ‖dzC ψ z‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (L / varpi (ψ z) * |D.det| * varpi z) := ENNReal.ofReal_le_ofReal ha
    _ = ENNReal.ofReal (L / varpi (ψ z) * |D.det|) * ENNReal.ofReal (varpi z) :=
        ENNReal.ofReal_mul hA0
    _ ≤ ENNReal.ofReal (L / varpi (ψ z) * |D.det|) * (ENNReal.ofReal Cr * V) :=
        mul_le_mul_of_nonneg_left hv (by positivity)
    _ = ENNReal.ofReal (L / varpi (ψ z) * |D.det| * Cr) * V := by
        rw [ENNReal.ofReal_mul hA0, mul_assoc]
    _ ≤ ENNReal.ofReal (4 * L * Cr * (2 * β)⁻¹ * |D.det|) * V :=
        mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hreal) (by positivity)
    _ = ENNReal.ofReal (4 * L * Cr) * (V / ENNReal.ofReal (2 * β)) * ENNReal.ofReal |D.det| := by
        rw [ENNReal.ofReal_mul (mul_nonneg h4 (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ 2 * β))),
          ENNReal.ofReal_mul h4, ENNReal.ofReal_inv_of_pos (by linarith : (0 : ℝ) < 2 * β),
          ENNReal.div_eq_inv_mul]
        ring

/-- Helper for `s07_tw_boxbound`: the one-box estimate when the box coordinates of `ψ(S)` use
the lifts `k = -1, 0, 1` (T1, T2, `s07_tw_ratio`, `s07_tw_cov`, `s07_tw_box`, `s07_tw_nu`, T4
with `μ = H_* dθ` and T5 `s07_inv_power`). -/
theorem s07_tw_boxbound_core (L : ℝ) (δf : ℝ → ℝ) : ∃ K : ℝ, 0 < K ∧
    ∀ (ψ h : ℂ → ℂ) (H : ℝ → ℝ), MapsTo ψ unitDisc unitDisc → IsDiskBiLip ψ L →
      HasDiskBoundaryValues ψ h → IsStronglyQSWith h δf → StrictMono H → Continuous H →
      (∀ θ, H (θ + 2 * π) = H θ + 2 * π) → (∀ θ : ℝ, h (exp (θ * I)) = exp (H θ * I)) →
      ∀ lam : ℂ → ℝ≥0∞, Measurable lam → ∀ S ⊆ unitDisc, MeasurableSet S →
      ∀ a b : ℝ, a < b → 3 * (b - a) ≤ 2 * π →
      (∀ w ∈ ψ '' S, ∃ k ∈ Finset.Icc (-1 : ℤ) 1, (Complex.arg w + 2 * π * k,
        2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖))) ∈ Icc a b ×ˢ Ioc 0 (b - a)) →
      carlesonPullback ψ lam S ≤ ENNReal.ofReal K *
        carlesonNorm ((volume.restrict unitDisc).withDensity lam) *
          volume (H ⁻¹' Icc (a - (b - a)) (b + (b - a))) := by
  have hπ := Real.pi_gt_three
  obtain ⟨Cr, hCr, hratio⟩ := s07_tw_ratio L
  obtain ⟨C, δ, hC, hδ, hpow⟩ := s07_inv_power δf
  obtain ⟨Ke, hKe, hemb⟩ := s07_tw_embed C δ (2 * π) hC hδ (by positivity)
  refine ⟨36 * (|L| + 1) * Cr * Ke, by positivity, ?_⟩
  intro ψ h H hψ hL hbd hs hH hHc hper hl lam hlam S hSD hS a b hab hab3 hTb
  obtain ⟨hL1, -⟩ := s07_tw_bilip_qi hψ hL
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hHm : Measurable H := hHc.measurable
  have hsurj : Function.Surjective H := fun y => s07_tw_lift_surj hHc hper y
  obtain ⟨e, he⟩ : ∃ e : ℝ ≃o ℝ, ⇑e = H := ⟨StrictMono.orderIsoOfSurjective H hH hsurj, rfl⟩
  have hpre : ∀ X : Set ℝ, ⇑e.symm '' X = H ⁻¹' X := by
    intro X
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show H (e.symm x) ∈ X
      rw [← he, e.apply_symm_apply]
      exact hx
    · intro hy
      exact ⟨H y, hy, by rw [← he, e.symm_apply_apply]⟩
  obtain ⟨N, hNd⟩ : ∃ N : ℝ≥0∞, N = carlesonNorm ((volume.restrict unitDisc).withDensity lam) :=
    ⟨_, rfl⟩
  rw [← hNd]
  -- the pull-back as an integral over `S`, and the change of variables
  have hpb : carlesonPullback ψ lam S = ∫⁻ z in S, lam (ψ z) * ‖dzC ψ z‖ₑ := by
    unfold carlesonPullback
    rw [withDensity_apply _ hS, Measure.restrict_restrict hS, inter_eq_left.mpr hSD]
  have hcov := s07_tw_cov hψ hL hS hSD lam (fun w => ENNReal.ofReal (4 * L * Cr) *
      (volume (H ⁻¹' Icc (Complex.arg w - 2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖)))
        (Complex.arg w + 2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖)))) /
          ENNReal.ofReal (2 * (2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖)))))) (fun z hz hd =>
      s07_tw_pt hψ hL (hSD hz) hd hCr (hratio ψ h H hψ hL hbd hH hHc hper hl z (hSD hz)
        (Complex.arg (ψ z)) (Complex.norm_mul_exp_arg_mul_I _).symm))
  -- the transfer to the box
  obtain ⟨ν, hνd⟩ : ∃ ν : Measure (ℝ × ℝ), ν = ∑ k ∈ Finset.Icc (-1 : ℤ) 1,
      ((volume.restrict unitDisc).withDensity lam).map
        (fun w => (Complex.arg w + 2 * π * k, 2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖)))) :=
    ⟨_, rfl⟩
  have hbox := s07_tw_box lam hlam hH hHc hper (T := ψ '' S)
    (by rintro _ ⟨z, hz, rfl⟩; exact hψ (hSD hz)) hTb
  rw [← hνd] at hbox
  -- T4 for `μ = H_* dθ` and `ν`
  have hfin : ∀ a b : ℝ, Measure.map H volume (Icc a b) ≠ ⊤ := by
    intro a b
    rw [Measure.map_apply hHm measurableSet_Icc, ← hpre, e.symm.image_Icc, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hpow' : ∀ a b : ℝ, a < b → b - a ≤ 2 * π → ∀ A ⊆ Icc a b, MeasurableSet A →
      Measure.map H volume A ≤ ENNReal.ofReal (C * ((volume A).toReal / (b - a)) ^ δ) *
        Measure.map H volume (Icc a b) := by
    intro a b hab hab2 A hA hAm
    rw [Measure.map_apply hHm hAm, Measure.map_apply hHm measurableSet_Icc, ← hpre, ← hpre]
    exact hpow h H (⇑e.symm) hs hH hHc hper hl e.symm.strictMono
      (fun θ => by rw [← he, e.apply_symm_apply]) (fun θ => by rw [← he, e.symm_apply_apply])
      a b hab hab2 A hA hAm
  have hI : Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hcarl : ∀ a b : ℝ, a < b → b - a ≤ 2 * π →
      ν (Icc a b ×ˢ Ioc 0 (b - a)) ≤ 9 * N * ENNReal.ofReal (b - a) := by
    intro a b hab hab2
    rw [hνd, Measure.finsetSum_apply, hI, Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    have h1 := s07_tw_nu lam (-1) hab hab2
    have h2 := s07_tw_nu lam 0 hab hab2
    have h3 := s07_tw_nu lam 1 hab hab2
    rw [← hNd] at h1 h2 h3
    calc _ ≤ 3 * N * ENNReal.ofReal (b - a) + (3 * N * ENNReal.ofReal (b - a) +
          3 * N * ENNReal.ofReal (b - a)) := add_le_add h1 (add_le_add h2 h3)
      _ = 9 * N * ENNReal.ofReal (b - a) := by ring
  have hE := hemb (Measure.map H volume) hfin hpow' ν (9 * N) hcarl a b hab (by linarith)
  rw [Measure.map_apply hHm measurableSet_Icc] at hE
  -- assembly
  have hc0 : 0 ≤ 4 * L * Cr := by have := hCr.le; nlinarith
  calc carlesonPullback ψ lam S = ∫⁻ z in S, lam (ψ z) * ‖dzC ψ z‖ₑ := hpb
    _ ≤ _ := hcov
    _ = ENNReal.ofReal (4 * L * Cr) * ∫⁻ w in ψ '' S, lam w *
          (volume (H ⁻¹' Icc (Complex.arg w - 2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖)))
            (Complex.arg w + 2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖)))) /
          ENNReal.ofReal (2 * (2 * Real.arctan ((1 - ‖w‖) / (1 + ‖w‖))))) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        funext w
        ring
    _ ≤ ENNReal.ofReal (4 * L * Cr) * (ENNReal.ofReal Ke * (9 * N) *
          volume (H ⁻¹' Icc (a - (b - a)) (b + (b - a)))) :=
        mul_le_mul_of_nonneg_left (hbox.trans hE) (by positivity)
    _ = ENNReal.ofReal (4 * L * Cr * Ke * 9) * N *
          volume (H ⁻¹' Icc (a - (b - a)) (b + (b - a))) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hc0 hKe.le), ENNReal.ofReal_mul hc0,
          ENNReal.ofReal_ofNat]
        ring
    _ ≤ ENNReal.ofReal (36 * (|L| + 1) * Cr * Ke) * N *
          volume (H ⁻¹' Icc (a - (b - a)) (b + (b - a))) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (ENNReal.ofReal_le_ofReal ?_) (by positivity)) (by positivity)
        have h1 := mul_le_mul_of_nonneg_right (by linarith [le_abs_self L] : L ≤ |L| + 1)
          (mul_nonneg hCr.le hKe.le)
        nlinarith

/-- One box: if `ψ(S)` lies in the box over `[a, b]` (`3(b - a) ≤ 2π`), then
`(ψ^*λ)(S) ≤ K ‖λ‖_CM |H⁻¹([a - |I|, b + |I|])|`, `K` depending only on `L, δf` (T1, T2,
`s07_tw_ratio`, `s07_tw_cov`, `s07_tw_box`, `s07_tw_nu`, T4 with `μ = H⁻¹` and T5
`s07_inv_power`). -/
theorem s07_tw_boxbound (L : ℝ) (δf : ℝ → ℝ) : ∃ K : ℝ, 0 < K ∧
    ∀ (ψ h : ℂ → ℂ) (H : ℝ → ℝ), MapsTo ψ unitDisc unitDisc → IsDiskBiLip ψ L →
      HasDiskBoundaryValues ψ h → IsStronglyQSWith h δf → StrictMono H → Continuous H →
      (∀ θ, H (θ + 2 * π) = H θ + 2 * π) → (∀ θ : ℝ, h (exp (θ * I)) = exp (H θ * I)) →
      ∀ lam : ℂ → ℝ≥0∞, Measurable lam → ∀ S ⊆ unitDisc, MeasurableSet S →
      ∀ a b : ℝ, a < b → 3 * (b - a) ≤ 2 * π →
      (∀ x ∈ S, ∀ t : ℝ, ψ x = (‖ψ x‖ : ℂ) * exp (t * I) → ∃ k : ℤ,
        (t + 2 * π * k, 2 * Real.arctan ((1 - ‖ψ x‖) / (1 + ‖ψ x‖))) ∈ Icc a b ×ˢ Ioc 0 (b - a)) →
      carlesonPullback ψ lam S ≤ ENNReal.ofReal K *
        carlesonNorm ((volume.restrict unitDisc).withDensity lam) *
          volume (H ⁻¹' Icc (a - (b - a)) (b + (b - a))) := by
  obtain ⟨K, hK, hcore⟩ := s07_tw_boxbound_core L δf
  refine ⟨K, hK, ?_⟩
  intro ψ h H hψ hL hbd hs hH hHc hper hl lam hlam S hSD hS a b hab hab3 hSb
  have hπ := Real.pi_gt_three
  -- shift `[a, b]` by `2πk₀` so that `|a| ≤ π`; then only the lifts `-1, 0, 1` occur
  obtain ⟨k₀, hk₀⟩ := s07_tw_round a
  obtain ⟨hk₁, hk₂⟩ := abs_le.mp hk₀
  have hsurj : Function.Surjective H := fun y => s07_tw_lift_surj hHc hper y
  obtain ⟨e, he⟩ : ∃ e : ℝ ≃o ℝ, ⇑e = H := ⟨StrictMono.orderIsoOfSurjective H hH hsurj, rfl⟩
  have hvol : ∀ x y, volume (H ⁻¹' Icc x y) = ENNReal.ofReal (e.symm y - e.symm x) := by
    intro x y
    rw [← he, e.preimage_Icc x y, Real.volume_Icc]
  have hes : ∀ (k : ℤ) (y : ℝ), e.symm (y + 2 * π * k) = e.symm y + 2 * π * k := by
    intro k y
    apply e.injective
    rw [e.apply_symm_apply, he, show e.symm y + 2 * π * k = e.symm y + k * (2 * π) by ring,
      s07_inv_per_int hper k, ← he, e.apply_symm_apply]
    ring
  have hV : volume (H ⁻¹' Icc (a + 2 * π * k₀ - (b - a)) (b + 2 * π * k₀ + (b - a))) =
      volume (H ⁻¹' Icc (a - (b - a)) (b + (b - a))) := by
    rw [hvol, hvol, show a + 2 * π * k₀ - (b - a) = (a - (b - a)) + 2 * π * k₀ by ring,
      show b + 2 * π * k₀ + (b - a) = (b + (b - a)) + 2 * π * k₀ by ring, hes, hes,
      add_sub_add_right_eq_sub]
  have hc := hcore ψ h H hψ hL hbd hs hH hHc hper hl lam hlam S hSD hS (a + 2 * π * k₀)
    (b + 2 * π * k₀) (by linarith) (by linarith) ?_
  · rw [show b + 2 * π * k₀ - (a + 2 * π * k₀) = b - a by ring, hV] at hc
    exact hc
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨k, hk⟩ := hSb x hx (Complex.arg (ψ x)) (Complex.norm_mul_exp_arg_mul_I _).symm
  simp only [mem_prod, mem_Icc, mem_Ioc] at hk
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hk
  have ha1 := Complex.neg_pi_lt_arg (ψ x)
  have ha2 := Complex.arg_le_pi (ψ x)
  refine ⟨k + k₀, ?_, ?_⟩
  · rw [Finset.mem_Icc]
    have hl' : (-1 : ℝ) ≤ (k : ℝ) + k₀ :=
      le_of_mul_le_mul_left (by linarith : 2 * π * (-1) ≤ 2 * π * ((k : ℝ) + k₀)) (by positivity)
    have hu' : (k : ℝ) + k₀ < 2 :=
      lt_of_mul_lt_mul_left (by linarith : 2 * π * ((k : ℝ) + k₀) < 2 * π * 2) (by positivity)
    have hl'' : (-1 : ℤ) ≤ k + k₀ := by exact_mod_cast hl'
    have hu'' : k + k₀ < 2 := by exact_mod_cast hu'
    omega
  · simp only [mem_prod, mem_Icc, mem_Ioc]
    push_cast
    refine ⟨⟨by linarith, by linarith⟩, h3, by linarith⟩

/-- Helper for `s07_tw_total`: a `d_𝔻`-bi-Lipschitz self-map of `𝔻` is injective on `𝔻`. -/
theorem s07_tw_injOn {ψ : ℂ → ℂ} {L : ℝ} (hψ : MapsTo ψ unitDisc unitDisc)
    (hL : IsDiskBiLip ψ L) : InjOn ψ unitDisc := by
  intro x hx y hy hxy
  have h1 := (hL x hx y hy).2
  have h2 := (s07_tw_dist_bounds (hψ hx) (hψ hy)).2
  have h3 := (s07_tw_dist_bounds hx hy).1
  rw [hxy, sub_self, norm_zero, zero_div, mul_zero] at h2
  have h0 := s02_diskDist_nonneg (hψ hx) (hψ hy)
  rw [hxy] at h0 h1
  have hdd : diskDist (ψ y) (ψ y) = 0 := le_antisymm h2 h0
  rw [hdd, mul_zero] at h1
  have hvx : 0 < varpi x := by
    have : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
    unfold varpi; nlinarith [norm_nonneg x]
  have hvy : 0 < varpi y := by
    have : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
    unfold varpi; nlinarith [norm_nonneg y]
  have hr : 0 < √(varpi x * varpi y) := Real.sqrt_pos.mpr (mul_pos hvx hvy)
  have hq : 0 < √(1 + (‖x - y‖ / √(varpi x * varpi y)) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have h4 : 2 * (‖x - y‖ / √(varpi x * varpi y)) ≤ 0 := by
    have h5 := h3.trans h1
    rw [div_le_iff₀ hq, zero_mul] at h5
    exact h5
  have h6 : ‖x - y‖ / √(varpi x * varpi y) ≤ 0 := by linarith
  rw [div_le_iff₀ hr, zero_mul] at h6
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h6)

/-- Helper for `s07_tw_total`: a `d_𝔻`-bi-Lipschitz self-map of `𝔻` is continuous on `𝔻`
(`s07_tw_lip` on `B(0, (|x| + 1)/2)`). -/
theorem s07_tw_contOn {ψ : ℂ → ℂ} {L : ℝ} (hψ : MapsTo ψ unitDisc unitDisc)
    (hL : IsDiskBiLip ψ L) : ContinuousOn ψ unitDisc := by
  intro x hx
  have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
  obtain ⟨C, hC⟩ := s07_tw_lip hψ hL (R := (‖x‖ + 1) / 2) (by positivity) (by linarith)
  have hxb : x ∈ ball (0 : ℂ) ((‖x‖ + 1) / 2) := mem_ball_zero_iff.mpr (by linarith)
  exact ((hC.continuousOn x hxb).continuousAt (isOpen_ball.mem_nhds hxb)).continuousWithinAt

/-- The total mass: `(ψ^*λ)(𝔻) ≤ K ‖λ‖_CM` (three boxes over arcs of length `2π/3`, each with
`|H⁻¹(3I)| = 2π`, by `s07_tw_boxbound`). -/
theorem s07_tw_total (L : ℝ) (δf : ℝ → ℝ) : ∃ K : ℝ, 0 < K ∧
    ∀ ψ h : ℂ → ℂ, MapsTo ψ unitDisc unitDisc → IsDiskBiLip ψ L →
      HasDiskBoundaryValues ψ h → IsStronglyQSWith h δf → ∀ lam : ℂ → ℝ≥0∞, Measurable lam →
        carlesonPullback ψ lam unitDisc ≤
          ENNReal.ofReal K * carlesonNorm ((volume.restrict unitDisc).withDensity lam) := by
  obtain ⟨K, hK, hbox⟩ := s07_tw_boxbound L δf
  refine ⟨3 * (K * (2 * π)), by positivity, ?_⟩
  intro ψ h hψ hL hbd hs lam hlam
  obtain ⟨H, hH, hHc, hper, hl⟩ := hs.1
  have hπ := Real.pi_gt_three
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  -- `|H⁻¹(J)| = 2π` for intervals `J` of length `2π`
  have hsurj : Function.Surjective H := fun y => s07_tw_lift_surj hHc hper y
  obtain ⟨e, he⟩ : ∃ e : ℝ ≃o ℝ, ⇑e = H := ⟨StrictMono.orderIsoOfSurjective H hH hsurj, rfl⟩
  have hes : ∀ y, e.symm (y + 2 * π) = e.symm y + 2 * π := by
    intro y
    apply e.injective
    rw [e.apply_symm_apply, he, hper, ← he, e.apply_symm_apply]
  have hvol : ∀ a : ℝ, volume (H ⁻¹' Icc a (a + 2 * π)) = ENNReal.ofReal (2 * π) := by
    intro a
    rw [← he, e.preimage_Icc, Real.volume_Icc, hes]
    congr 1
    ring
  -- a measurable modification of `ψ` off `𝔻`
  classical
  obtain ⟨g, hgd⟩ : ∃ g : ℂ → ℂ, g = unitDisc.piecewise ψ (fun _ => 0) := ⟨_, rfl⟩
  have hgm : Measurable g := by
    rw [hgd]
    exact (s07_tw_contOn hψ hL).measurable_piecewise continuousOn_const hDm
  have hgψ : ∀ x ∈ unitDisc, g x = ψ x := by
    intro x hx
    rw [hgd]
    exact Set.piecewise_eq_of_mem _ _ _ hx
  -- the sectors `arg ψ ∈ [a, a + 2π/3]` and the null set `ψ = 0`
  obtain ⟨S, hSd⟩ : ∃ S : ℝ → Set ℂ, S = fun a =>
      unitDisc ∩ g ⁻¹' {w | w ≠ 0 ∧ Complex.arg w ∈ Icc a (a + 2 * π / 3)} := ⟨_, rfl⟩
  have hSm : ∀ a, MeasurableSet (S a) := by
    intro a
    rw [hSd]
    exact hDm.inter (hgm ((measurableSet_singleton 0).compl.inter
      (Complex.measurable_arg measurableSet_Icc)))
  have hsec : ∀ a : ℝ, carlesonPullback ψ lam (S a) ≤ ENNReal.ofReal K *
      carlesonNorm ((volume.restrict unitDisc).withDensity lam) * ENNReal.ofReal (2 * π) := by
    intro a
    have hSD : S a ⊆ unitDisc := by
      rw [hSd]
      exact inter_subset_left
    have hb := hbox ψ h H hψ hL hbd hs hH hHc hper hl lam hlam (S a) hSD (hSm a) a
      (a + 2 * π / 3) (by linarith) (by linarith) ?_
    · have e1 : a - (a + 2 * π / 3 - a) = a - 2 * π / 3 := by ring
      have e2 : a + 2 * π / 3 + (a + 2 * π / 3 - a) = a - 2 * π / 3 + 2 * π := by ring
      rw [e1, e2, hvol] at hb
      exact hb
    intro x hx t ht
    have hxD := hSD hx
    rw [hSd] at hx
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_Icc, hgψ x hxD] at hx
    obtain ⟨-, hx0, hxa1, hxa2⟩ := hx
    have hE : exp (t * I) = exp (Complex.arg (ψ x) * I) := by
      have h1 := Complex.norm_mul_exp_arg_mul_I (ψ x)
      have hn : (‖ψ x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx0
      exact mul_left_cancel₀ hn (ht.symm.trans h1.symm)
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hE
    have h2 : ((t - (Complex.arg (ψ x) + 2 * π * n) : ℝ) : ℂ) * I = 0 := by
      push_cast
      linear_combination hn
    have h3 : t - (Complex.arg (ψ x) + 2 * π * n) = 0 := by
      have := (mul_eq_zero.mp h2).resolve_right I_ne_zero
      exact_mod_cast this
    -- `0 < β(ψ x) ≤ π/2 < 2π/3`
    have hψx : ‖ψ x‖ < 1 := mem_ball_zero_iff.mp (hψ hxD)
    have hy0 : 0 < (1 - ‖ψ x‖) / (1 + ‖ψ x‖) := div_pos (by linarith) (by positivity)
    have hy1 : (1 - ‖ψ x‖) / (1 + ‖ψ x‖) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [norm_nonneg (ψ x)]
    have hβ0 : 0 < 2 * Real.arctan ((1 - ‖ψ x‖) / (1 + ‖ψ x‖)) := by
      have h4 := Real.arctan_strictMono hy0
      rw [Real.arctan_zero] at h4
      linarith
    have hβ1 : 2 * Real.arctan ((1 - ‖ψ x‖) / (1 + ‖ψ x‖)) ≤ π / 2 := by
      have h4 := Real.arctan_strictMono.monotone hy1
      rw [Real.arctan_one] at h4
      linarith
    refine ⟨-n, ?_⟩
    simp only [mem_prod, mem_Icc, mem_Ioc]
    push_cast
    refine ⟨⟨by linarith, by linarith⟩, hβ0, by linarith⟩
  obtain ⟨Z, hZd⟩ : ∃ Z : Set ℂ, Z = unitDisc ∩ g ⁻¹' {0} := ⟨_, rfl⟩
  have hZ : carlesonPullback ψ lam Z = 0 := by
    have hinj := s07_tw_injOn hψ hL
    have hsub : Z.Subsingleton := by
      intro x hx y hy
      rw [hZd] at hx hy
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff] at hx hy
      exact hinj hx.1 hy.1 (by rw [← hgψ x hx.1, ← hgψ y hy.1, hx.2, hy.2])
    exact withDensity_absolutelyContinuous _ _
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self (hsub.measure_zero volume))
  -- `𝔻 ⊆ Z ∪ S(-π) ∪ S(-π/3) ∪ S(π/3)`
  have hcov : unitDisc ⊆ Z ∪ S (-π) ∪ S (-π / 3) ∪ S (π / 3) := by
    intro x hx
    have hmS : ∀ a, ψ x ≠ 0 → a ≤ Complex.arg (ψ x) → Complex.arg (ψ x) ≤ a + 2 * π / 3 →
        x ∈ S a := by
      intro a h0 h1 h2
      rw [hSd]
      refine ⟨hx, ?_⟩
      show g x ≠ 0 ∧ Complex.arg (g x) ∈ Icc a (a + 2 * π / 3)
      rw [hgψ x hx]
      exact ⟨h0, h1, h2⟩
    have ha1 := Complex.neg_pi_lt_arg (ψ x)
    have ha2 := Complex.arg_le_pi (ψ x)
    by_cases h0 : ψ x = 0
    · refine Or.inl (Or.inl (Or.inl ?_))
      rw [hZd]
      refine ⟨hx, ?_⟩
      show g x = 0
      rw [hgψ x hx]
      exact h0
    rcases le_or_gt (Complex.arg (ψ x)) (-π / 3) with h1 | h1
    · exact Or.inl (Or.inl (Or.inr (hmS _ h0 (by linarith) (by linarith))))
    rcases le_or_gt (Complex.arg (ψ x)) (π / 3) with h2 | h2
    · exact Or.inl (Or.inr (hmS _ h0 (by linarith) (by linarith)))
    · exact Or.inr (hmS _ h0 (by linarith) (by linarith))
  calc carlesonPullback ψ lam unitDisc
      ≤ carlesonPullback ψ lam (Z ∪ S (-π) ∪ S (-π / 3) ∪ S (π / 3)) := measure_mono hcov
    _ ≤ carlesonPullback ψ lam Z + carlesonPullback ψ lam (S (-π)) +
          carlesonPullback ψ lam (S (-π / 3)) + carlesonPullback ψ lam (S (π / 3)) :=
        (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ ≤ 0 + ENNReal.ofReal K * carlesonNorm ((volume.restrict unitDisc).withDensity lam) *
            ENNReal.ofReal (2 * π) +
          ENNReal.ofReal K * carlesonNorm ((volume.restrict unitDisc).withDensity lam) *
            ENNReal.ofReal (2 * π) +
          ENNReal.ofReal K * carlesonNorm ((volume.restrict unitDisc).withDensity lam) *
            ENNReal.ofReal (2 * π) :=
        add_le_add (add_le_add (add_le_add hZ.le (hsec _)) (hsec _)) (hsec _)
    _ = _ := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_mul hK.le,
          ENNReal.ofReal_ofNat]
        ring

/-- Quasisymmetry of `H⁻¹` from the modulus `δf` (with `ρ = M |H(J)|`, `J = [θ₀ - s, θ₀ + s]`):
if `ρ ≤ π` then `|H⁻¹([H θ₀ - ρ, H θ₀ + ρ])| ≤ s/c` (strong quasisymmetry with `ε = 1/4M` on that
arc, which contains `J`); if `ρ > π` then `s ≥ c` (with `ε = 1/2M` on an arc of length `2π`). -/
theorem s07_tw_qs (δf : ℝ → ℝ) (M : ℝ) (hM : 1 ≤ M) : ∃ c : ℝ, 0 < c ∧
    ∀ (h : ℂ → ℂ) (H : ℝ → ℝ), IsStronglyQSWith h δf → StrictMono H → Continuous H →
      (∀ θ, H (θ + 2 * π) = H θ + 2 * π) → (∀ θ : ℝ, h (exp (θ * I)) = exp (H θ * I)) →
      ∀ θ₀ s : ℝ, 0 < s →
        (M * (H (θ₀ + s) - H (θ₀ - s)) ≤ π →
          volume (H ⁻¹' Icc (H θ₀ - M * (H (θ₀ + s) - H (θ₀ - s)))
            (H θ₀ + M * (H (θ₀ + s) - H (θ₀ - s)))) ≤ ENNReal.ofReal (s / c)) ∧
        (π < M * (H (θ₀ + s) - H (θ₀ - s)) → c ≤ s) := by
  have hπ := Real.pi_gt_three
  have hM0 : 0 < M := by linarith
  by_cases hd : 0 < δf (1 / (4 * M)) ∧ 0 < δf (1 / (2 * M))
  swap
  · -- no `h` has modulus `δf`
    refine ⟨1, one_pos, ?_⟩
    intro h H hs
    exact absurd ⟨(hs.2 _ (by positivity)).1, (hs.2 _ (by positivity)).1⟩ hd
  obtain ⟨hd1, hd2⟩ := hd
  obtain ⟨c, hcd⟩ : ∃ c : ℝ, c = min (δf (1 / (4 * M)) / 2) (min (π * δf (1 / (2 * M))) π) :=
    ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hcd]
    exact lt_min (half_pos hd1) (lt_min (mul_pos Real.pi_pos hd2) Real.pi_pos)
  have hc1 : c ≤ δf (1 / (4 * M)) / 2 := by rw [hcd]; exact min_le_left _ _
  have hc2 : c ≤ π * δf (1 / (2 * M)) := by
    rw [hcd]
    exact (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨c, hc0, ?_⟩
  intro h H hs hH hHc hper hl θ₀ s hs0
  have hsurj : Function.Surjective H := fun y => s07_tw_lift_surj hHc hper y
  obtain ⟨e, he⟩ : ∃ e : ℝ ≃o ℝ, ⇑e = H := ⟨StrictMono.orderIsoOfSurjective H hH hsurj, rfl⟩
  have himg : ∀ x y, volume (H '' Icc x y) = ENNReal.ofReal (H y - H x) := by
    intro x y
    rw [← he, e.image_Icc, Real.volume_Icc]
  obtain ⟨ℓ, hℓd⟩ : ∃ ℓ : ℝ, ℓ = H (θ₀ + s) - H (θ₀ - s) := ⟨_, rfl⟩
  rw [← hℓd]
  have hℓ0 : 0 < ℓ := by
    rw [hℓd]
    have := hH (by linarith : θ₀ - s < θ₀ + s)
    linarith
  have hJ : volume (H '' Icc (θ₀ - s) (θ₀ + s)) = ENNReal.ofReal ℓ := by rw [himg, hℓd]
  have hJlen : volume (Icc (θ₀ - s) (θ₀ + s)) = ENNReal.ofReal (2 * s) := by
    rw [Real.volume_Icc]
    congr 1
    ring
  -- strong quasisymmetry on an arc `[u, v] ⊇ J` whose image is long compared with `H(J)`
  have key : ∀ ε : ℝ, 0 < ε → ∀ u v : ℝ, u < v → v - u ≤ 2 * π → u ≤ θ₀ - s → θ₀ + s ≤ v →
      ε * (H v - H u) < ℓ → δf ε * (v - u) < 2 * s := by
    intro ε hε u v huv huv2 hu hv hlt
    by_contra hcon
    rw [not_lt] at hcon
    have h1 := s07_inv_hlift hs hH hHc hper hl hε u v huv huv2 (Icc (θ₀ - s) (θ₀ + s))
      (Icc_subset_Icc hu hv) measurableSet_Icc (by rw [hJlen]; exact ENNReal.ofReal_le_ofReal hcon)
    have hHuv : 0 ≤ H v - H u := sub_nonneg.mpr (hH.monotone huv.le)
    rw [hJ, himg, ← ENNReal.ofReal_mul hε.le,
      ENNReal.ofReal_le_ofReal_iff (mul_nonneg hε.le hHuv)] at h1
    linarith
  have hMℓ : ℓ ≤ M * ℓ := by
    have := mul_le_mul_of_nonneg_right hM hℓ0.le
    linarith
  have hθ1 : H θ₀ - H (θ₀ - s) ≤ ℓ := by
    rw [hℓd]
    have := hH.monotone (by linarith : θ₀ ≤ θ₀ + s)
    linarith
  have hθ2 : H (θ₀ + s) - H θ₀ ≤ ℓ := by
    rw [hℓd]
    have := hH.monotone (by linarith : θ₀ - s ≤ θ₀)
    linarith
  constructor
  · intro hρ
    obtain ⟨u, hu⟩ := s07_tw_lift_surj hHc hper (H θ₀ - M * ℓ)
    obtain ⟨v, hv⟩ := s07_tw_lift_surj hHc hper (H θ₀ + M * ℓ)
    have hρ0 : 0 < M * ℓ := mul_pos hM0 hℓ0
    have huv : u < v := hH.lt_iff_lt.mp (by rw [hu, hv]; linarith)
    have hpre : H ⁻¹' Icc (H θ₀ - M * ℓ) (H θ₀ + M * ℓ) = Icc u v := by
      ext θ
      simp only [mem_preimage, mem_Icc]
      rw [← hu, ← hv, hH.le_iff_le, hH.le_iff_le]
    rw [hpre, Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    have huv2 : v - u ≤ 2 * π := by
      have h1 : H v ≤ H (u + 2 * π) := by rw [hper, hu, hv]; linarith
      have := hH.le_iff_le.mp h1
      linarith
    have hs1 : u ≤ θ₀ - s := by
      rw [← hH.le_iff_le, hu]
      linarith
    have hs2 : θ₀ + s ≤ v := by
      rw [← hH.le_iff_le, hv]
      linarith
    have hk := key (1 / (4 * M)) (by positivity) u v huv huv2 hs1 hs2 (by
      rw [hu, hv, div_mul_eq_mul_div, one_mul, div_lt_iff₀ (by positivity)]
      nlinarith)
    rw [le_div_iff₀ hc0]
    have := mul_le_mul_of_nonneg_left hc1 (by linarith : 0 ≤ v - u)
    linarith
  · intro hρ
    rcases le_or_gt s π with hsπ | hsπ
    · have hk := key (1 / (2 * M)) (by positivity) (θ₀ - π) (θ₀ + π) (by linarith) (by linarith)
        (by linarith) (by linarith) (by
          rw [show θ₀ + π = (θ₀ - π) + 2 * π by ring, hper, div_mul_eq_mul_div, one_mul,
            div_lt_iff₀ (by positivity)]
          linarith)
      have e : θ₀ + π - (θ₀ - π) = 2 * π := by ring
      rw [e] at hk
      linarith
    · have hc3 : c ≤ π := by
        rw [hcd]
        exact (min_le_right _ _).trans (min_le_right _ _)
      linarith

/-- Theorem 7.6, `thm:TWS` ([TWS, Prop. 3.5], `sec07-transfer.tex:269`): for `ψ : 𝔻 → 𝔻`
`L`-bi-Lipschitz for `d_𝔻` with strongly quasisymmetric boundary values (modulus `δf`),
`‖ψ^* λ‖_CM ≤ C ‖λ‖_CM`, `C` depending only on `L` and `δf`. -/
theorem thm_TWS (L : ℝ) (δf : ℝ → ℝ) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ ψ h : ℂ → ℂ, MapsTo ψ unitDisc unitDisc → IsDiskBiLip ψ L →
      HasDiskBoundaryValues ψ h → IsStronglyQSWith h δf →
      ∀ lam : ℂ → ℝ≥0∞, Measurable lam →
        carlesonNorm (carlesonPullback ψ lam) ≤
          C * carlesonNorm ((volume.restrict unitDisc).withDensity lam) := by
  obtain ⟨C₄, hC₄, himg⟩ := s07_tw_image L
  obtain ⟨K, hK, hbox⟩ := s07_tw_boxbound L δf
  obtain ⟨Kt, hKt, htot⟩ := s07_tw_total L δf
  obtain ⟨c, hc, hqs⟩ := s07_tw_qs δf (3 * C₄) (by linarith)
  have hC₄0 : 0 < C₄ := by linarith
  refine ⟨ENNReal.ofReal ((K + Kt) * C₄ / c), ENNReal.ofReal_ne_top, ?_⟩
  intro ψ h hψ hL hbd hs lam hlam
  obtain ⟨H, hH, hHc, hper, hl⟩ := hs.1
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  show (⨆ ζ ∈ sphere (0 : ℂ) 1, ⨆ r ∈ Ioo (0 : ℝ) 2,
    carlesonPullback ψ lam (unitDisc ∩ ball ζ r) / ENNReal.ofReal r) ≤ _
  refine iSup₂_le fun ζ hζ => iSup₂_le fun r hr => ENNReal.div_le_of_le_mul ?_
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ : ℝ, exp (θ₀ * I) = ζ := by
    refine ⟨Complex.arg ζ, ?_⟩
    have h1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
    have h2 := Complex.norm_mul_exp_arg_mul_I ζ
    rw [h1, Complex.ofReal_one, one_mul] at h2
    exact h2
  have hCr : 0 < C₄ * r := mul_pos hC₄0 hr.1
  have hρ' : 0 < H (θ₀ + C₄ * r) - H (θ₀ - C₄ * r) := sub_pos.mpr (hH (by linarith))
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = C₄ * (H (θ₀ + C₄ * r) - H (θ₀ - C₄ * r)) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := hρ ▸ mul_pos hC₄0 hρ'
  have hM : 3 * C₄ * (H (θ₀ + C₄ * r) - H (θ₀ - C₄ * r)) = 3 * ρ := by rw [hρ]; ring
  obtain ⟨hqA, hqB⟩ := hqs h H hs hH hHc hper hl θ₀ (C₄ * r) hCr
  rw [hM] at hqA hqB
  have hS : MeasurableSet (unitDisc ∩ ball ζ r) := hDm.inter measurableSet_ball
  have hsub : unitDisc ∩ ball ζ r ⊆ unitDisc := inter_subset_left
  have hKK : ENNReal.ofReal (K * C₄ / c) ≤ ENNReal.ofReal ((K + Kt) * C₄ / c) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hC₄0.le) hc.le)
  have hKtK : ENNReal.ofReal (Kt * C₄ / c) ≤ ENNReal.ofReal ((K + Kt) * C₄ / c) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hC₄0.le) hc.le)
  have hsplit : ∀ K' : ℝ, 0 ≤ K' →
      ENNReal.ofReal K' * ENNReal.ofReal (C₄ * r / c) = ENNReal.ofReal (K' * C₄ / c) *
        ENNReal.ofReal r := by
    intro K' hK'
    rw [← ENNReal.ofReal_mul hK', ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rcases le_or_gt (3 * ρ) π with hsmall | hlarge
  · -- small `ρ`: `ψ(𝔻 ∩ B(ζ, r))` lies in one box
    have himgx : ∀ x ∈ unitDisc ∩ ball ζ r, ∀ t : ℝ, ψ x = (‖ψ x‖ : ℂ) * exp (t * I) →
        ∃ k : ℤ, (t + 2 * π * k, 2 * Real.arctan ((1 - ‖ψ x‖) / (1 + ‖ψ x‖))) ∈
          Icc (H θ₀ - ρ) (H θ₀ + ρ) ×ˢ Ioc 0 ((H θ₀ + ρ) - (H θ₀ - ρ)) := by
      intro x hx t ht
      have hxr : ‖x - exp (θ₀ * I)‖ < r := by
        rw [hθ₀]
        exact mem_ball_iff_norm.mp hx.2
      obtain ⟨⟨k, hk⟩, hβ⟩ := himg ψ h H hψ hL hbd hH hHc hper hl θ₀ r hr.1 x hx.1 hxr t ht
      rw [← hρ] at hk hβ
      have hψx : ‖ψ x‖ < 1 := mem_ball_zero_iff.mp (hψ hx.1)
      have hβ0 : 0 < 2 * Real.arctan ((1 - ‖ψ x‖) / (1 + ‖ψ x‖)) := by
        have h1 : 0 < (1 - ‖ψ x‖) / (1 + ‖ψ x‖) := div_pos (by linarith) (by positivity)
        have h2 := Real.arctan_strictMono h1
        rw [Real.arctan_zero] at h2
        linarith
      refine ⟨k, ⟨?_, ?_⟩, hβ0, by linarith⟩
      · linarith [(abs_le.mp hk).1]
      · linarith [(abs_le.mp hk).2]
    have hb := hbox ψ h H hψ hL hbd hs hH hHc hper hl lam hlam (unitDisc ∩ ball ζ r) hsub hS
      (H θ₀ - ρ) (H θ₀ + ρ) (by linarith) (by linarith) himgx
    have e1 : H θ₀ - ρ - (H θ₀ + ρ - (H θ₀ - ρ)) = H θ₀ - 3 * ρ := by ring
    have e2 : H θ₀ + ρ + (H θ₀ + ρ - (H θ₀ - ρ)) = H θ₀ + 3 * ρ := by ring
    rw [e1, e2] at hb
    calc carlesonPullback ψ lam (unitDisc ∩ ball ζ r)
        ≤ ENNReal.ofReal K * carlesonNorm ((volume.restrict unitDisc).withDensity lam) *
            ENNReal.ofReal (C₄ * r / c) := hb.trans (by gcongr; exact hqA hsmall)
      _ = ENNReal.ofReal (K * C₄ / c) * carlesonNorm ((volume.restrict unitDisc).withDensity lam) *
            ENNReal.ofReal r := by
          rw [mul_right_comm, hsplit K hK.le, mul_right_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKK zero_le) zero_le
  · -- large `ρ`: `r ≥ c/C₄`, use the total mass
    have hcr : c ≤ C₄ * r := hqB hlarge
    have h1 : 1 ≤ ENNReal.ofReal (C₄ * r / c) :=
      ENNReal.one_le_ofReal.mpr ((one_le_div hc).mpr hcr)
    calc carlesonPullback ψ lam (unitDisc ∩ ball ζ r)
        ≤ carlesonPullback ψ lam unitDisc := measure_mono hsub
      _ ≤ ENNReal.ofReal Kt * carlesonNorm ((volume.restrict unitDisc).withDensity lam) :=
          htot ψ h hψ hL hbd hs lam hlam
      _ ≤ ENNReal.ofReal Kt * carlesonNorm ((volume.restrict unitDisc).withDensity lam) *
            ENNReal.ofReal (C₄ * r / c) := le_mul_of_one_le_right' h1
      _ = ENNReal.ofReal (Kt * C₄ / c) * carlesonNorm ((volume.restrict unitDisc).withDensity lam) *
            ENNReal.ofReal r := by
          rw [mul_right_comm, hsplit Kt hKt.le, mul_right_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKtK zero_le) zero_le

/-- `G = F⁻¹` for a bi-Lipschitz diffeomorphism: an `L`-bi-Lipschitz self-map of `𝔻`, continuous on
`𝔻` and at the boundary points (`s07_sb_inv`), differentiable with positive Jacobian
(`HasFDerivAt.of_local_left_inverse`). -/
theorem s07_tw_inv {F : ℂ → ℂ} {L : ℝ} (hF : IsBiLipDiskDiffeo F L) :
    ∃ G : ℂ → ℂ, MapsTo G unitDisc unitDisc ∧ (∀ w ∈ unitDisc, F (G w) = w) ∧
      (∀ z ∈ unitDisc, G (F z) = z) ∧ IsDiskBiLip G L ∧
      (∀ ζ ∈ sphere (0 : ℂ) 1, Tendsto G (𝓝[unitDisc] (F ζ)) (𝓝 ζ)) ∧
      ContinuousOn G unitDisc ∧
      ∀ w ∈ unitDisc, DifferentiableAt ℝ G w ∧ 0 < (fderiv ℝ G w).det := by
  obtain ⟨hFh, hFc, hFdet, hFL⟩ := hF
  obtain ⟨G, hGD, hFG, hGF, hGb⟩ := s07_sb_inv hFh hFL
  have hDo : IsOpen unitDisc := isOpen_ball
  have hGL : IsDiskBiLip G L := by
    intro x hx y hy
    have h := hFL (G x) (hGD hx) (G y) (hGD hy)
    rw [hFG x hx, hFG y hy] at h
    exact ⟨h.2, h.1⟩
  have hGc : ContinuousOn G unitDisc := s07_tw_contOn hGD hGL
  refine ⟨G, hGD, hFG, hGF, hGL, hGb, hGc, ?_⟩
  -- inverse function theorem at `G w`: `DF(G w)` is invertible (`det > 0`)
  intro w hw
  have hz : G w ∈ unitDisc := hGD hw
  have hdet : (fderiv ℝ F (G w)).det ≠ 0 := (hFdet _ hz).ne'
  have hFd : HasFDerivAt F (fderiv ℝ F (G w)) (G w) :=
    ((hFc.differentiableOn one_ne_zero).differentiableAt (hDo.mem_nhds hz)).hasFDerivAt
  have hFd' : HasFDerivAt F
      ((fderiv ℝ F (G w)).toContinuousLinearEquivOfDetNeZero hdet : ℂ →L[ℝ] ℂ) (G w) := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact hFd
  have hev : ∀ᶠ y in 𝓝 w, F (G y) = y := by
    filter_upwards [hDo.mem_nhds hw] with y hy
    exact hFG y hy
  have hGd := HasFDerivAt.of_local_left_inverse ((hGc w hw).continuousAt (hDo.mem_nhds hw)) hFd' hev
  refine ⟨hGd.differentiableAt, ?_⟩
  rw [hGd.fderiv, ContinuousLinearEquiv.det_coe_symm,
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
  exact inv_pos.mpr (hFdet _ hz)

/-- The push-forward `F_*(b dA) = |det DG| (b ∘ G) dA` on `𝔻` (area formula for `G = F⁻¹`). -/
theorem s07_tw_push {F G : ℂ → ℂ} (hF : IsClosedDiskHomeo F) (hFD : MapsTo F unitDisc unitDisc)
    (hGD : MapsTo G unitDisc unitDisc) (hFG : ∀ w ∈ unitDisc, F (G w) = w)
    (hGF : ∀ z ∈ unitDisc, G (F z) = z) (hGc : ContinuousOn G unitDisc)
    (hGd : ∀ w ∈ unitDisc, DifferentiableAt ℝ G w) (b : ℂ → ℝ≥0∞) (hb : Measurable b) :
    ((volume.restrict unitDisc).withDensity b).map F =
      (volume.restrict unitDisc).withDensity
        (fun w => ENNReal.ofReal |(fderiv ℝ G w).det| * b (G w)) := by
  -- `hGc` and `hb` are not needed (differentiability of `G` on `𝔻` suffices; `withDensity` is
  -- defined for any density); the statement stays true without them
  have _hGc := hGc
  have _hb := hb
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  -- a measurable modification of `F` off `𝔻`
  classical
  obtain ⟨F', hF'd⟩ : ∃ F' : ℂ → ℂ, F' = unitDisc.piecewise F (fun _ => 0) := ⟨_, rfl⟩
  have hF'm : Measurable F' := by
    rw [hF'd]
    exact (hF.2.mono ball_subset_closedBall).measurable_piecewise continuousOn_const hDm
  have hF'F : ∀ z ∈ unitDisc, F' z = F z := by
    intro z hz
    rw [hF'd]
    exact Set.piecewise_eq_of_mem _ _ _ hz
  have hae : F =ᵐ[(volume.restrict unitDisc).withDensity b] F' := by
    refine (withDensity_absolutelyContinuous _ b).ae_le ?_
    filter_upwards [ae_restrict_mem hDm] with z hz
    exact (hF'F z hz).symm
  -- `F'⁻¹(s) ∩ 𝔻 = G(s ∩ 𝔻)`
  have himg : ∀ s : Set ℂ, F' ⁻¹' s ∩ unitDisc = G '' (s ∩ unitDisc) := by
    intro s
    ext z
    constructor
    · rintro ⟨hzs, hz⟩
      rw [mem_preimage, hF'F z hz] at hzs
      exact ⟨F z, ⟨hzs, hFD hz⟩, hGF z hz⟩
    · rintro ⟨w, ⟨hws, hw⟩, rfl⟩
      refine ⟨?_, hGD hw⟩
      rw [mem_preimage, hF'F _ (hGD hw), hFG w hw]
      exact hws
  have hinj : InjOn G unitDisc := by
    intro x hx y hy hxy
    rw [← hFG x hx, ← hFG y hy, hxy]
  ext s hs
  rw [Measure.map_congr hae, Measure.map_apply hF'm hs, withDensity_apply _ (hF'm hs),
    withDensity_apply _ hs, Measure.restrict_restrict (hF'm hs), Measure.restrict_restrict hs,
    himg s, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hs.inter hDm)
      (fun x hx => (hGd x hx.2).hasFDerivAt.hasFDerivWithinAt) (hinj.mono inter_subset_right) b]

/-- `ϖ` times a density on `𝔻`. -/
theorem s07_tw_varpi_dens {g : ℂ → ℝ≥0∞} (hg : AEMeasurable g (volume.restrict unitDisc)) :
    varpiMeasure ((volume.restrict unitDisc).withDensity g) =
      (volume.restrict unitDisc).withDensity fun w => ENNReal.ofReal (varpi w) * g w := by
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hvm : Measurable fun z : ℂ => ENNReal.ofReal (varpi z) :=
    ENNReal.measurable_ofReal.comp
      ((show Continuous varpi from continuous_const.sub (continuous_norm.pow 2)).measurable)
  rw [varpiMeasure, restrict_withDensity hDm, Measure.restrict_restrict hDm, inter_self,
    ← withDensity_mul₀ hg hvm.aemeasurable]
  congr 1
  funext w
  exact mul_comm _ _

/-- Monotonicity of the Carleson norm. -/
theorem s07_tw_cn_le {μ ν : Measure ℂ} {c : ℝ≥0∞} (h : ∀ s, MeasurableSet s → μ s ≤ c * ν s) :
    carlesonNorm μ ≤ c * carlesonNorm ν := by
  unfold carlesonNorm
  refine iSup₂_le fun ζ hζ => iSup₂_le fun r hr => ?_
  calc μ (unitDisc ∩ ball ζ r) / ENNReal.ofReal r
      ≤ c * ν (unitDisc ∩ ball ζ r) / ENNReal.ofReal r :=
        ENNReal.div_le_div_right (h _ (measurableSet_ball.inter measurableSet_ball)) _
    _ = c * (ν (unitDisc ∩ ball ζ r) / ENNReal.ofReal r) := mul_div_assoc _ _ _
    _ ≤ c * ⨆ ζ ∈ sphere (0 : ℂ) 1, ⨆ r ∈ Ioo (0 : ℝ) 2,
          ν (unitDisc ∩ ball ζ r) / ENNReal.ofReal r := by
        gcongr
        exact le_iSup₂_of_le ζ hζ (le_iSup₂_of_le r hr le_rfl)

/-- Proposition 7.7 (a), `prop:bilip-transfer` (`sec07-transfer.tex:295`): for `dm = b dA`,
`‖ϖ F_* m‖_CM ≤ L³ C ‖ϖ m‖_CM`, `C` the constant of Theorem 7.6 for `ψ = F⁻¹` (it depends on
`L` and on the modulus `δf` of `(F|_{∂𝔻})⁻¹`). -/
theorem prop_bilip_transfer_a (L : ℝ) (δf : ℝ → ℝ) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ F Finv : ℂ → ℂ, IsBiLipDiskDiffeo F L → IsStronglyQS F →
      (∀ ζ ∈ sphere (0 : ℂ) 1, Finv ζ ∈ sphere (0 : ℂ) 1 ∧ F (Finv ζ) = ζ) →
      IsStronglyQSWith Finv δf → ∀ b : ℂ → ℝ≥0∞, Measurable b →
        carlesonNorm (varpiMeasure (((volume.restrict unitDisc).withDensity b).map F)) ≤
          ENNReal.ofReal (L ^ 3) * C *
            carlesonNorm (varpiMeasure ((volume.restrict unitDisc).withDensity b)) := by
  obtain ⟨C, hC, hTWS⟩ := thm_TWS L δf
  refine ⟨C, hC, fun F Finv hF _ hinv hFinv b hb => ?_⟩
  obtain ⟨G, hGD, hFG, hGF, hGL, hGlim, hGc, hGd⟩ := s07_tw_inv hF
  obtain ⟨hFh, -, -, hFL⟩ := hF
  obtain ⟨hFD, hL1⟩ := s07_sb_maps hFh hFL
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hvc : Continuous varpi := continuous_const.sub (continuous_norm.pow 2)
  have hvm : Measurable fun z : ℂ => ENNReal.ofReal (varpi z) :=
    ENNReal.measurable_ofReal.comp hvc.measurable
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℂ → ℝ≥0∞, lam = fun z => ENNReal.ofReal (varpi z) * b z :=
    ⟨_, rfl⟩
  have hlam : Measurable lam := hlamdef ▸ hvm.mul hb
  have hbdG : HasDiskBoundaryValues G Finv := by
    intro ζ hζ
    have h1 := hGlim (Finv ζ) (hinv ζ hζ).1
    rwa [(hinv ζ hζ).2] at h1
  have hT := hTWS G Finv hGD hGL hbdG hFinv lam hlam
  have hgm : AEMeasurable (fun w => ENNReal.ofReal |(fderiv ℝ G w).det| * b (G w))
      (volume.restrict unitDisc) :=
    (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ G)))).aemeasurable.mul
      (hb.comp_aemeasurable (hGc.aemeasurable hDm))
  rw [s07_tw_push hFh hFD hGD hFG hGF hGc (fun w hw => (hGd w hw).1) b hb,
    s07_tw_varpi_dens hgm, s07_tw_varpi_dens hb.aemeasurable]
  have hLpos : 0 ≤ L := by linarith
  -- pointwise: `ϖ(w) det DG(w) ≤ L ϖ(G w) |∂G(w)|` (T1 upper bound + T2)
  have hpt : ∀ w ∈ unitDisc, ENNReal.ofReal (varpi w) *
      (ENNReal.ofReal |(fderiv ℝ G w).det| * b (G w)) ≤
        ENNReal.ofReal L * (lam (G w) * ‖dzC G w‖ₑ) := by
    intro w hw
    obtain ⟨hdw, hdet⟩ := hGd w hw
    have hv0 : 0 < varpi w := by
      have : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
      unfold varpi
      nlinarith [norm_nonneg w]
    have hvG : 0 ≤ varpi (G w) := by
      have : ‖G w‖ < 1 := mem_ball_zero_iff.mp (hGD hw)
      unfold varpi
      nlinarith [norm_nonneg (G w)]
    have hup : ∀ v : ℂ, ‖fderiv ℝ G w v‖ ≤ L * varpi (G w) / varpi w * ‖v‖ := by
      intro v
      have h := (s07_tw_inf hGD hGL hw hdw v).2
      rw [div_mul_eq_mul_div, le_div_iff₀ hv0]
      linarith
    have hj := (s07_tw_jac (fderiv ℝ G w) (m := 0)).2 hup hdet.le
    have key : varpi w * (fderiv ℝ G w).det ≤ L * varpi (G w) * ‖dzC G w‖ := by
      have e : dzC G w = (fderiv ℝ G w 1 - I * fderiv ℝ G w I) / 2 := rfl
      rw [e]
      calc varpi w * (fderiv ℝ G w).det
          ≤ varpi w * (L * varpi (G w) / varpi w * ‖(fderiv ℝ G w 1 - I * fderiv ℝ G w I) / 2‖) :=
            mul_le_mul_of_nonneg_left hj hv0.le
        _ = L * varpi (G w) * ‖(fderiv ℝ G w 1 - I * fderiv ℝ G w I) / 2‖ := by
            field_simp
    rw [abs_of_pos hdet, hlamdef]
    calc ENNReal.ofReal (varpi w) * (ENNReal.ofReal (fderiv ℝ G w).det * b (G w))
        = ENNReal.ofReal (varpi w * (fderiv ℝ G w).det) * b (G w) := by
          rw [ENNReal.ofReal_mul hv0.le, mul_assoc]
      _ ≤ ENNReal.ofReal (L * varpi (G w) * ‖dzC G w‖) * b (G w) := by gcongr
      _ = ENNReal.ofReal L * (ENNReal.ofReal (varpi (G w)) * b (G w) * ‖dzC G w‖ₑ) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hLpos hvG), ENNReal.ofReal_mul hLpos,
            ofReal_norm]
          ring
  have hle : ∀ s, MeasurableSet s →
      (volume.restrict unitDisc).withDensity (fun w => ENNReal.ofReal (varpi w) *
        (ENNReal.ofReal |(fderiv ℝ G w).det| * b (G w))) s ≤
        ENNReal.ofReal L * carlesonPullback G lam s := by
    intro s hs
    rw [withDensity_apply _ hs, carlesonPullback, withDensity_apply _ hs,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono_ae ((ae_restrict_of_ae (ae_restrict_mem hDm)).mono fun w hw => hpt w hw)
  have hL3 : ENNReal.ofReal L ≤ ENNReal.ofReal (L ^ 3) :=
    ENNReal.ofReal_le_ofReal (by
      have h2 : 1 ≤ L ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h2 hLpos])
  have hlam' : (volume.restrict unitDisc).withDensity lam =
      (volume.restrict unitDisc).withDensity fun w => ENNReal.ofReal (varpi w) * b w := by
    rw [hlamdef]
  calc _ ≤ ENNReal.ofReal L * carlesonNorm (carlesonPullback G lam) := s07_tw_cn_le hle
    _ ≤ ENNReal.ofReal L * (C * carlesonNorm ((volume.restrict unitDisc).withDensity lam)) := by
        gcongr
    _ ≤ _ := by
        rw [hlam', ← mul_assoc]
        gcongr

/-- Helper for `prop_bilip_transfer_b`: a Carleson measure has finite Carleson norm. -/
theorem s07_bt_cn_ne_top {μ : Measure ℂ} (hμ : IsCarlesonDisk μ) : carlesonNorm μ ≠ ⊤ := by
  obtain ⟨C, hC, hCb⟩ := hμ
  refine ne_top_of_le_ne_top hC ?_
  unfold carlesonNorm
  exact iSup₂_le fun ζ hζ => iSup₂_le fun r hr => ENNReal.div_le_of_le_mul (hCb ζ hζ r hr.1 hr.2)

/-- Helper for `prop_bilip_transfer_b`: for `ν ∈ CM₀`, `‖ν|_{ρ < |z|}‖_CM → 0` as `ρ ↑ 1`
(`ν(𝔻) < ∞` by (7.1); small boxes by `CM₀`, large boxes by `ν(𝔻 ∩ {ρ < |z|}) → 0`). -/
theorem s07_bt_tail {ν : Measure ℂ} (hν : IsVanishingCarlesonDisk ν) {η : ℝ} (hη : 0 < η) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      carlesonNorm (ν.restrict {z : ℂ | ρ < ‖z‖}) ≤ ENNReal.ofReal η := by
  obtain ⟨r₁, hr₁, hr₁b⟩ := hν.2 η hη
  have hfin : ν unitDisc ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (s07_bt_cn_ne_top hν.1))
      (s07_total_mass ν)
  -- `A n = 𝔻 ∩ {1 - 1/(n+1) < |z|}` decreases to `∅`
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Set ℂ,
      ∀ n, A n = unitDisc ∩ {z : ℂ | 1 - 1 / ((n : ℝ) + 1) < ‖z‖} := ⟨_, fun _ => rfl⟩
  have hAm : ∀ n, MeasurableSet (A n) := fun n => by
    rw [hA n]
    exact measurableSet_ball.inter (measurableSet_lt measurable_const measurable_norm)
  have hAa : Antitone A := by
    intro n k hnk z hz
    rw [hA] at hz ⊢
    have hnk' : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by
      have := (Nat.cast_le (α := ℝ)).mpr hnk
      linarith
    have : 1 / ((k : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) hnk'
    have h2 : 1 - 1 / ((k : ℝ) + 1) < ‖z‖ := hz.2
    exact ⟨hz.1, show 1 - 1 / ((n : ℝ) + 1) < ‖z‖ by linarith⟩
  have hAi : ⋂ n, A n = ∅ := by
    ext z
    simp only [mem_iInter, mem_empty_iff_false, iff_false]
    intro hz
    have h0 := hz 0
    rw [hA 0] at h0
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp h0.1
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < 1 - ‖z‖ by linarith)
    have hzn := hz n
    rw [hA n] at hzn
    have h2 : 1 - 1 / ((n : ℝ) + 1) < ‖z‖ := hzn.2
    linarith
  have hlim := tendsto_measure_iInter_atTop (μ := ν) (fun n => (hAm n).nullMeasurableSet) hAa
    ⟨0, ne_top_of_le_ne_top hfin (measure_mono (by rw [hA 0]; exact inter_subset_left))⟩
  rw [hAi, measure_empty] at hlim
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (η * r₁) := ENNReal.ofReal_pos.mpr (mul_pos hη hr₁)
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_atTop_zero.mp hlim) _ hpos
  have hAn : ν (A n) ≤ ENNReal.ofReal (η * r₁) := hn n le_rfl
  have hn1 : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hn2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have := n.cast_nonneg (α := ℝ)
    linarith
  refine ⟨1 - 1 / ((n : ℝ) + 1), by linarith, by linarith, ?_⟩
  unfold carlesonNorm
  refine iSup₂_le fun ζ hζ => iSup₂_le fun r hr => ENNReal.div_le_of_le_mul ?_
  rw [← ENNReal.ofReal_mul hη.le]
  rcases lt_or_ge r r₁ with h | h
  · exact (Measure.restrict_apply_le _ _).trans (hr₁b ζ hζ r hr.1 h)
  · have hSm : MeasurableSet (unitDisc ∩ ball ζ r) := measurableSet_ball.inter measurableSet_ball
    rw [Measure.restrict_apply hSm]
    calc ν (unitDisc ∩ ball ζ r ∩ {z : ℂ | 1 - 1 / ((n : ℝ) + 1) < ‖z‖}) ≤ ν (A n) := by
          rw [hA n]
          exact measure_mono fun z hz => ⟨hz.1.1, hz.2⟩
      _ ≤ ENNReal.ofReal (η * r₁) := hAn
      _ ≤ ENNReal.ofReal (η * r) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h hη.le)

/-- Helper for `prop_bilip_transfer_b`: `F` maps `{|z| ≤ ρ}` (`0 ≤ ρ < 1`) into some
`{|w| ≤ ρ'}` with `ρ' < 1` (compactness). -/
theorem s07_bt_rho {F : ℂ → ℂ} (hFc : ContinuousOn F (closedBall 0 1))
    (hFD : MapsTo F unitDisc unitDisc) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ ρ' : ℝ, ρ' < 1 ∧ ∀ z : ℂ, ‖z‖ ≤ ρ → ‖F z‖ ≤ ρ' := by
  have hsub : closedBall (0 : ℂ) ρ ⊆ closedBall 0 1 := closedBall_subset_closedBall hρ1.le
  obtain ⟨z₀, hz₀, hmax⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_isMaxOn
    ⟨0, mem_closedBall_self hρ0⟩ (continuous_norm.comp_continuousOn (hFc.mono hsub))
  have hz₀D : z₀ ∈ unitDisc :=
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz₀) hρ1)
  exact ⟨‖F z₀‖, mem_ball_zero_iff.mp (hFD hz₀D), fun z hz => hmax (mem_closedBall_zero_iff.mpr hz)⟩

/-- Proposition 7.7 (b), `prop:bilip-transfer` (`sec07-transfer.tex:304`): if `ϖ m ∈ CM₀` then
`ϖ F_* m ∈ CM₀`. -/
theorem prop_bilip_transfer_b (F : ℂ → ℂ) (L : ℝ) (hF : IsBiLipDiskDiffeo F L)
    (hsqs : IsStronglyQS F) (b : ℂ → ℝ≥0∞) (hb : Measurable b)
    (hm : IsVanishingCarlesonDisk (varpiMeasure ((volume.restrict unitDisc).withDensity b))) :
    IsVanishingCarlesonDisk
      (varpiMeasure (((volume.restrict unitDisc).withDensity b).map F)) := by
  obtain ⟨G, hGD, hFG, hGF, -, -, hGc, hGd⟩ := s07_tw_inv hF
  obtain ⟨hFD, -⟩ := s07_sb_maps hF.1 hF.2.2.2
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  -- the boundary inverse `(F|_{∂𝔻})⁻¹` is strongly quasisymmetric
  have hinv : ∀ ζ ∈ sphere (0 : ℂ) 1, Function.invFunOn F (closedBall 0 1) ζ ∈ sphere (0 : ℂ) 1 ∧
      F (Function.invFunOn F (closedBall 0 1) ζ) = ζ := by
    intro ζ hζ
    have hex : ∃ z ∈ closedBall (0 : ℂ) 1, F z = ζ := hF.1.1.surjOn (sphere_subset_closedBall hζ)
    have hmem := Function.invFunOn_mem hex
    have heq := Function.invFunOn_eq hex
    refine ⟨?_, heq⟩
    rw [mem_sphere_zero_iff_norm]
    rcases (mem_closedBall_zero_iff.mp hmem).lt_or_eq with h | h
    · exfalso
      have h1 := mem_ball_zero_iff.mp (hFD (mem_ball_zero_iff.mpr h))
      rw [heq, mem_sphere_zero_iff_norm.mp hζ] at h1
      exact lt_irrefl _ h1
    · exact h
  obtain ⟨δf, hδf⟩ := sqs_circle_inv F _ hsqs hinv
  obtain ⟨C, hC, hTr⟩ := prop_bilip_transfer_a L δf
  have hTb : ∀ b' : ℂ → ℝ≥0∞, Measurable b' →
      carlesonNorm (varpiMeasure (((volume.restrict unitDisc).withDensity b').map F)) ≤
        ENNReal.ofReal (L ^ 3) * C *
          carlesonNorm (varpiMeasure ((volume.restrict unitDisc).withDensity b')) :=
    fun b' hb' => hTr F (Function.invFunOn F (closedBall 0 1)) hF hsqs hinv hδf b' hb'
  have hKt : ENNReal.ofReal (L ^ 3) * C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC
  -- (a): `ϖ F_* m ∈ CM`
  refine ⟨⟨ENNReal.ofReal (L ^ 3) * C *
      carlesonNorm (varpiMeasure ((volume.restrict unitDisc).withDensity b)),
    ENNReal.mul_ne_top hKt (s07_bt_cn_ne_top hm.1), fun ζ hζ r hr0 hr2 => ?_⟩, ?_⟩
  · refine (s07_le_carlesonNorm _ ζ hζ r hr0 hr2).trans ?_
    gcongr
    exact hTb b hb
  -- vanishing: cut `m` at `|z| = ρ`; the inner part pushes into `{|w| ≤ ρ'}`
  intro ε hε
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = (ENNReal.ofReal (L ^ 3) * C).toReal := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := hKdef ▸ ENNReal.toReal_nonneg
  have hKe : ENNReal.ofReal (L ^ 3) * C = ENNReal.ofReal K := by
    rw [hKdef, ENNReal.ofReal_toReal hKt]
  have hη : 0 < ε / (K + 1) := div_pos hε (by linarith)
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := s07_bt_tail hm hη
  obtain ⟨ρ', hρ'1, hρ'⟩ := s07_bt_rho hF.1.2 hFD hρ0 hρ1
  refine ⟨min (1 - ρ') 2, lt_min (by linarith) two_pos, fun ζ hζ r hr0 hrδ => ?_⟩
  have hr1 : r < 1 - ρ' := lt_of_lt_of_le hrδ (min_le_left _ _)
  have hr2 : r < 2 := lt_of_lt_of_le hrδ (min_le_right _ _)
  obtain ⟨U, hU⟩ : ∃ U : Set ℂ, U = {z : ℂ | ρ < ‖z‖} := ⟨_, rfl⟩
  have hUm : MeasurableSet U := hU ▸ measurableSet_lt measurable_const measurable_norm
  have hbU : Measurable (U.indicator b) := hb.indicator hUm
  -- push-forward densities (`s07_tw_push`)
  have hM : ∀ b' : ℂ → ℝ≥0∞, Measurable b' →
      varpiMeasure (((volume.restrict unitDisc).withDensity b').map F) =
        (volume.restrict unitDisc).withDensity fun w => ENNReal.ofReal (varpi w) *
          (ENNReal.ofReal |(fderiv ℝ G w).det| * b' (G w)) := by
    intro b' hb'
    have hgm : AEMeasurable (fun w => ENNReal.ofReal |(fderiv ℝ G w).det| * b' (G w))
        (volume.restrict unitDisc) :=
      (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
        (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ G)))).aemeasurable.mul
        (hb'.comp_aemeasurable (hGc.aemeasurable hDm))
    rw [s07_tw_push hF.1 hFD hGD hFG hGF hGc (fun w hw => (hGd w hw).1) b' hb',
      s07_tw_varpi_dens hgm]
  -- `ϖ (1_U m) = (ϖ m)|_U`
  have hνU : varpiMeasure ((volume.restrict unitDisc).withDensity (U.indicator b)) =
      (varpiMeasure ((volume.restrict unitDisc).withDensity b)).restrict U := by
    rw [withDensity_indicator hUm, ← restrict_withDensity hUm b]
    unfold varpiMeasure
    rw [restrict_withDensity hUm (fun z => ENNReal.ofReal (varpi z)), Measure.restrict_restrict hDm,
      Measure.restrict_restrict hUm, Set.inter_comm unitDisc U]
  have hS : MeasurableSet (unitDisc ∩ ball ζ r) := measurableSet_ball.inter measurableSet_ball
  -- on boxes of size `r < 1 - ρ'`, only `1_U m` contributes
  have hstep : varpiMeasure (((volume.restrict unitDisc).withDensity b).map F)
      (unitDisc ∩ ball ζ r) ≤ varpiMeasure (((volume.restrict unitDisc).withDensity
        (U.indicator b)).map F) (unitDisc ∩ ball ζ r) := by
    rw [hM b hb, hM _ hbU, withDensity_apply _ hS, withDensity_apply _ hS]
    refine lintegral_mono_ae ((ae_restrict_mem hS).mono fun w hw => ?_)
    have hGU : G w ∈ U := by
      rw [hU]
      show ρ < ‖G w‖
      by_contra hcon
      rw [not_lt] at hcon
      have h1 := hρ' (G w) hcon
      rw [hFG w hw.1] at h1
      have h2 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
      have h3 : ‖w - ζ‖ < r := mem_ball_iff_norm.mp hw.2
      have h4 := norm_sub_norm_le ζ w
      rw [norm_sub_rev] at h4
      linarith
    show ENNReal.ofReal (varpi w) * (ENNReal.ofReal |(fderiv ℝ G w).det| * b (G w)) ≤
      ENNReal.ofReal (varpi w) * (ENNReal.ofReal |(fderiv ℝ G w).det| * U.indicator b (G w))
    rw [Set.indicator_of_mem hGU]
  calc varpiMeasure (((volume.restrict unitDisc).withDensity b).map F) (unitDisc ∩ ball ζ r)
      ≤ varpiMeasure (((volume.restrict unitDisc).withDensity (U.indicator b)).map F)
          (unitDisc ∩ ball ζ r) := hstep
    _ ≤ carlesonNorm (varpiMeasure (((volume.restrict unitDisc).withDensity
          (U.indicator b)).map F)) * ENNReal.ofReal r := s07_le_carlesonNorm _ ζ hζ r hr0 hr2
    _ ≤ ENNReal.ofReal (L ^ 3) * C * carlesonNorm
          ((varpiMeasure ((volume.restrict unitDisc).withDensity b)).restrict U) *
            ENNReal.ofReal r := by
        rw [← hνU]
        gcongr
        exact hTb _ hbU
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (ε / (K + 1)) * ENNReal.ofReal r := by
        rw [hKe, hU]
        gcongr
    _ ≤ ENNReal.ofReal (ε * r) := by
        rw [← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_mul (mul_nonneg hK0 hη.le)]
        apply ENNReal.ofReal_le_ofReal
        have hKε : K * (ε / (K + 1)) ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ (by linarith)]
          nlinarith
        exact mul_le_mul_of_nonneg_right hKε hr0.le

/-- Helper for `prop:qi-transfer`: strong quasisymmetry only depends on the values on `∂𝔻`. -/
theorem s07_qi_sqs_congr {h F : ℂ → ℂ} {δf : ℝ → ℝ} (hh : IsStronglyQSWith h δf)
    (hFh : EqOn F h (sphere (0 : ℂ) 1)) : IsStronglyQSWith F δf := by
  have hexp : ∀ θ : ℝ, Complex.exp (θ * Complex.I) ∈ sphere (0 : ℂ) 1 := fun θ =>
    mem_sphere_zero_iff_norm.2 (Complex.norm_exp_ofReal_mul_I θ)
  have harc : ∀ a b : ℝ, circleArc a b ⊆ sphere (0 : ℂ) 1 := by
    intro a b x hx
    obtain ⟨θ, -, rfl⟩ := hx
    exact hexp θ
  obtain ⟨⟨H, hH, hHc, hper, hl⟩, hq⟩ := hh
  refine ⟨⟨H, hH, hHc, hper, fun θ => ?_⟩, fun ε hε => ⟨(hq ε hε).1, ?_⟩⟩
  · rw [hFh (hexp θ), hl θ]
  · intro a b hab hb2 E hE hEm hlen
    rw [(hFh.mono (hE.trans (harc a b))).image_eq, (hFh.mono (harc a b)).image_eq]
    exact (hq ε hε).2 a b hab hb2 E hE hEm hlen

/-- Helper for `prop:qi-transfer`: the inverse of a bi-Lipschitz disk diffeomorphism is one (the
inverse of a continuous bijection of the compact `𝔻̄` is continuous; `C¹` on `𝔻` by the inverse
function theorem and continuity of operator inversion). -/
theorem s07_qi_inv_diffeo {F : ℂ → ℂ} {L : ℝ} (hF : IsBiLipDiskDiffeo F L) :
    ∃ Fi : ℂ → ℂ, IsBiLipDiskDiffeo Fi L ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, Fi (F z) = z ∧ F (Fi z) = z := by
  obtain ⟨G, hGD, hFG, -, hGL, -, hGc, hGd⟩ := s07_tw_inv hF
  obtain ⟨hFh, hFc, hFdet, -⟩ := hF
  have hDo : IsOpen unitDisc := isOpen_ball
  have hDcb : unitDisc ⊆ closedBall (0 : ℂ) 1 := ball_subset_closedBall
  obtain ⟨Fi, hFi⟩ : ∃ Fi : ℂ → ℂ, Fi = Function.invFunOn F (closedBall 0 1) := ⟨_, rfl⟩
  have hio : InvOn Fi F (closedBall 0 1) (closedBall 0 1) := hFi ▸ hFh.1.invOn_invFunOn
  have hFim : MapsTo Fi (closedBall 0 1) (closedBall 0 1) := hFi ▸ hFh.1.surjOn.mapsTo_invFunOn
  have hleft : ∀ z ∈ closedBall (0 : ℂ) 1, Fi (F z) = z := hio.1
  have hright : ∀ w ∈ closedBall (0 : ℂ) 1, F (Fi w) = w := hio.2
  -- `Fi = G` on `𝔻`
  have hFiG : EqOn Fi G unitDisc := fun w hw =>
    hFh.1.injOn (hFim (hDcb hw)) (hDcb (hGD hw)) (by rw [hright w (hDcb hw), hFG w hw])
  have hFiev : ∀ w ∈ unitDisc, Fi =ᶠ[𝓝 w] G := fun w hw =>
    Filter.eventuallyEq_of_mem (hDo.mem_nhds hw) hFiG
  have hFid : ∀ w ∈ unitDisc, fderiv ℝ Fi w = fderiv ℝ G w := fun w hw => (hFiev w hw).fderiv_eq
  -- continuity of `Fi` on `𝔻̄`: preimages of closed sets are compact images
  have hFic : ContinuousOn Fi (closedBall 0 1) := by
    rw [continuousOn_iff_isClosed]
    intro t ht
    refine ⟨F '' (t ∩ closedBall 0 1),
      (((isCompact_closedBall (0 : ℂ) 1).inter_left ht).image_of_continuousOn
        (hFh.2.mono inter_subset_right)).isClosed, ?_⟩
    ext w
    constructor
    · rintro ⟨hwt, hw⟩
      exact ⟨⟨Fi w, ⟨hwt, hFim hw⟩, hright w hw⟩, hw⟩
    · rintro ⟨⟨z, ⟨hzt, hz⟩, rfl⟩, hw⟩
      refine ⟨?_, hw⟩
      show Fi (F z) ∈ t
      rw [hleft z hz]
      exact hzt
  -- `DG(w) = DF(G w)⁻¹`, continuous in `w`
  have hGinv : ∀ w ∈ unitDisc, fderiv ℝ G w = Ring.inverse (fderiv ℝ F (G w)) := by
    intro w hw
    have hz : G w ∈ unitDisc := hGD hw
    have hdet : (fderiv ℝ F (G w)).det ≠ 0 := (hFdet _ hz).ne'
    have hFd : HasFDerivAt F (fderiv ℝ F (G w)) (G w) :=
      ((hFc.differentiableOn one_ne_zero).differentiableAt (hDo.mem_nhds hz)).hasFDerivAt
    have hFd' : HasFDerivAt F
        ((fderiv ℝ F (G w)).toContinuousLinearEquivOfDetNeZero hdet : ℂ →L[ℝ] ℂ) (G w) := by
      rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
      exact hFd
    have hev : ∀ᶠ y in 𝓝 w, F (G y) = y := by
      filter_upwards [hDo.mem_nhds hw] with y hy
      exact hFG y hy
    have hGd' := HasFDerivAt.of_local_left_inverse ((hGc w hw).continuousAt (hDo.mem_nhds hw))
      hFd' hev
    have hu : fderiv ℝ F (G w) = ((ContinuousLinearEquiv.toUnit
        ((fderiv ℝ F (G w)).toContinuousLinearEquivOfDetNeZero hdet) : (ℂ →L[ℝ] ℂ)ˣ) :
          ℂ →L[ℝ] ℂ) :=
      (ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ hdet).symm
    rw [hGd'.fderiv]
    exact ((congrArg Ring.inverse hu).trans (Ring.inverse_unit _)).symm
  have hFdc : ContinuousOn (fderiv ℝ F) unitDisc := hFc.continuousOn_fderiv_of_isOpen hDo le_rfl
  have hGdc : ContinuousOn (fderiv ℝ G) unitDisc := by
    intro w hw
    have hz : G w ∈ unitDisc := hGD hw
    have hdet : (fderiv ℝ F (G w)).det ≠ 0 := (hFdet _ hz).ne'
    have hu : fderiv ℝ F (G w) = ((ContinuousLinearEquiv.toUnit
        ((fderiv ℝ F (G w)).toContinuousLinearEquivOfDetNeZero hdet) : (ℂ →L[ℝ] ℂ)ˣ) :
          ℂ →L[ℝ] ℂ) :=
      (ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ hdet).symm
    have hinvc : ContinuousAt Ring.inverse (fderiv ℝ F (G w)) := by
      rw [hu]
      exact NormedRing.inverse_continuousAt _
    have hc : ContinuousAt (fun v => Ring.inverse (fderiv ℝ F (G v))) w :=
      ContinuousAt.comp (g := Ring.inverse) (f := fun v => fderiv ℝ F (G v)) hinvc
        (((hFdc _ hz).continuousAt (hDo.mem_nhds hz)).comp
        ((hGc w hw).continuousAt (hDo.mem_nhds hw)))
    refine (hc.congr ?_).continuousWithinAt
    filter_upwards [hDo.mem_nhds hw] with v hv
    exact (hGinv v hv).symm
  have hFi1 : ContDiffOn ℝ 1 Fi unitDisc := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from (zero_add 1).symm,
      contDiffOn_succ_iff_fderiv_of_isOpen hDo]
    refine ⟨fun w hw => ?_, fun h0 => absurd h0 (by simp), ?_⟩
    · exact (((hGd w hw).1.hasFDerivAt).congr_of_eventuallyEq
        (hFiev w hw)).differentiableAt.differentiableWithinAt
    · rw [contDiffOn_zero]
      exact hGdc.congr hFid
  refine ⟨Fi, ⟨⟨hio.symm.bijOn hFim hFh.1.mapsTo, hFic⟩, hFi1, fun w hw => ?_, ?_⟩,
    fun z hz => ⟨hleft z hz, hright z hz⟩⟩
  · rw [hFid w hw]
    exact (hGd w hw).2
  · intro x hx y hy
    rw [hFiG hx, hFiG hy]
    exact hGL x hx y hy

/-- Helper for `prop:qi-transfer`: `F_*(b dA) = b' dA` with a Borel density `b'`
(`b' = |det D F⁻¹| (b ∘ F⁻¹)` on `𝔻`), and `(F⁻¹)_*(b' dA) = b dA`. -/
theorem s07_qi_push_pair {F Fi : ℂ → ℂ} {L : ℝ} (hF : IsBiLipDiskDiffeo F L)
    (hFi : IsBiLipDiskDiffeo Fi L)
    (hinv : ∀ z ∈ closedBall (0 : ℂ) 1, Fi (F z) = z ∧ F (Fi z) = z)
    (b : ℂ → ℝ≥0∞) (hb : Measurable b) :
    ∃ b' : ℂ → ℝ≥0∞, Measurable b' ∧
      ((volume.restrict unitDisc).withDensity b).map F =
        (volume.restrict unitDisc).withDensity b' ∧
      ((volume.restrict unitDisc).withDensity b').map Fi =
        (volume.restrict unitDisc).withDensity b := by
  classical
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have hDo : IsOpen unitDisc := isOpen_ball
  have hDcb : unitDisc ⊆ closedBall (0 : ℂ) 1 := ball_subset_closedBall
  obtain ⟨hFD, -⟩ := s07_sb_maps hF.1 hF.2.2.2
  obtain ⟨hFiD, -⟩ := s07_sb_maps hFi.1 hFi.2.2.2
  have hFc : ContinuousOn F unitDisc := hF.1.2.mono hDcb
  have hFic : ContinuousOn Fi unitDisc := hFi.1.2.mono hDcb
  have hFd : ∀ z ∈ unitDisc, DifferentiableAt ℝ F z := fun z hz =>
    (hF.2.1.differentiableOn one_ne_zero).differentiableAt (hDo.mem_nhds hz)
  have hFid : ∀ z ∈ unitDisc, DifferentiableAt ℝ Fi z := fun z hz =>
    (hFi.2.1.differentiableOn one_ne_zero).differentiableAt (hDo.mem_nhds hz)
  have hleft : ∀ z ∈ unitDisc, Fi (F z) = z := fun z hz => (hinv z (hDcb hz)).1
  have hright : ∀ w ∈ unitDisc, F (Fi w) = w := fun w hw => (hinv w (hDcb hw)).2
  -- a Borel version of `Fi`
  obtain ⟨Fi', hFi'⟩ : ∃ Fi' : ℂ → ℂ, Fi' = unitDisc.piecewise Fi (fun _ => 0) := ⟨_, rfl⟩
  have hFi'm : Measurable Fi' := hFi' ▸ hFic.measurable_piecewise continuousOn_const hDm
  obtain ⟨b', hb'⟩ : ∃ b' : ℂ → ℝ≥0∞,
      b' = fun w => ENNReal.ofReal |(fderiv ℝ Fi w).det| * b (Fi' w) := ⟨_, rfl⟩
  have hb'm : Measurable b' := hb' ▸ (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
    (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ Fi)))).mul
      (hb.comp hFi'm)
  refine ⟨b', hb'm, ?_, ?_⟩
  · rw [s07_tw_push hF.1 hFD hFiD hright hleft hFic hFid b hb]
    refine withDensity_congr_ae ((ae_restrict_mem hDm).mono fun w hw => ?_)
    simp only [hb', hFi', Set.piecewise_eq_of_mem _ _ _ hw]
  · rw [s07_tw_push hFi.1 hFiD hFD hleft hright hFc hFd b' hb'm]
    refine withDensity_congr_ae ((ae_restrict_mem hDm).mono fun z hz => ?_)
    have hFz : F z ∈ unitDisc := hFD hz
    -- chain rule: `D Fi (F z) ∘ D F z = id`
    have hcomp : HasFDerivAt (Fi ∘ F) ((fderiv ℝ Fi (F z)).comp (fderiv ℝ F z)) z :=
      (hFid (F z) hFz).hasFDerivAt.comp z (hFd z hz).hasFDerivAt
    have hid : HasFDerivAt (Fi ∘ F) (ContinuousLinearMap.id ℝ ℂ) z := by
      refine (hasFDerivAt_id z).congr_of_eventuallyEq ?_
      filter_upwards [hDo.mem_nhds hz] with y hy
      exact hleft y hy
    have hdet : (fderiv ℝ F z).det * (fderiv ℝ Fi (F z)).det = 1 := by
      have h := congrArg ContinuousLinearMap.det (hcomp.unique hid)
      have e1 : ((fderiv ℝ Fi (F z)).comp (fderiv ℝ F z)).det =
          (fderiv ℝ Fi (F z)).det * (fderiv ℝ F z).det := LinearMap.det_comp _ _
      have e2 : (ContinuousLinearMap.id ℝ ℂ).det = 1 := LinearMap.det_id
      rw [e1, e2] at h
      rw [mul_comm]
      exact h
    show ENNReal.ofReal |(fderiv ℝ F z).det| * b' (F z) = b z
    rw [hb']
    show ENNReal.ofReal |(fderiv ℝ F z).det| *
      (ENNReal.ofReal |(fderiv ℝ Fi (F z)).det| * b (Fi' (F z))) = b z
    rw [hFi', Set.piecewise_eq_of_mem _ _ _ hFz, hleft z hz, ← mul_assoc,
      ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, hdet, abs_one, ENNReal.ofReal_one, one_mul]

/-- Helper for `prop:qi-transfer`, (7.9) `eq:AF-comparison`: `d_𝔻(Az, Fz) ≤ M` (Lemma 7.4), so
`𝒫_{F_*m} ≤ e^M 𝒫_{A_*m}` and `𝒫_{A_*m} ≤ e^M 𝒫_{F_*m}` (Lemma 7.2 with `Y = 𝔻`). -/
theorem s07_qi_AF {A F h : ℂ → ℂ} {LA cA LF : ℝ} (hA : IsDiskQI A LA cA) (hAm : Measurable A)
    (hbd : HasDiskBoundaryValues A h) (hF : IsClosedDiskHomeo F) (hFL : IsDiskBiLip F LF)
    (hFh : EqOn F h (sphere (0 : ℂ) 1)) (b : ℂ → ℝ≥0∞) (a : ℂ) (ha : a ∈ unitDisc) :
    poissonP (((volume.restrict unitDisc).withDensity b).map F) a ≤
        ENNReal.ofReal (Real.exp (LF * morseD (LF * LA) (LF * cA))) *
          poissonP (((volume.restrict unitDisc).withDensity b).map A) a ∧
      poissonP (((volume.restrict unitDisc).withDensity b).map A) a ≤
        ENNReal.ofReal (Real.exp (LF * morseD (LF * LA) (LF * cA))) *
          poissonP (((volume.restrict unitDisc).withDensity b).map F) a := by
  classical
  set M := LF * morseD (LF * LA) (LF * cA) with hM
  have hDm : MeasurableSet unitDisc := measurableSet_ball
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hFD := (s07_sb_maps hF hFL).1
  have hFA : HasDiskBoundaryValues A F := fun ζ hζ => by
    rw [hFh hζ]
    exact hbd ζ hζ
  have hd := lem_same_boundary A F LA cA LF hA hF hFL hFA
  have hM0 : 0 ≤ M := (s02_diskDist_nonneg (hA.1 h0) (hFD h0)).trans (hd 0 h0)
  -- Borel versions of `A` and `F`, equal to them on `𝔻` and with values in `𝔻`
  obtain ⟨A', hA'⟩ : ∃ A' : ℂ → ℂ, A' = unitDisc.piecewise A (fun _ => 0) := ⟨_, rfl⟩
  obtain ⟨F', hF'⟩ : ∃ F' : ℂ → ℂ, F' = unitDisc.piecewise F (fun _ => 0) := ⟨_, rfl⟩
  have hA'm : Measurable A' := hA' ▸ Measurable.piecewise hDm hAm measurable_const
  have hF'm : Measurable F' :=
    hF' ▸ (hF.2.mono ball_subset_closedBall).measurable_piecewise continuousOn_const hDm
  have hAD : ∀ y, A' y ∈ unitDisc := fun y => by
    rw [hA']
    by_cases hy : y ∈ unitDisc
    · rw [Set.piecewise_eq_of_mem _ _ _ hy]
      exact hA.1 hy
    · rw [Set.piecewise_eq_of_notMem _ _ _ hy]
      exact h0
  have hFD' : ∀ y, F' y ∈ unitDisc := fun y => by
    rw [hF']
    by_cases hy : y ∈ unitDisc
    · rw [Set.piecewise_eq_of_mem _ _ _ hy]
      exact hFD hy
    · rw [Set.piecewise_eq_of_notMem _ _ _ hy]
      exact h0
  have hM' : ∀ y, diskDist (A' y) (F' y) ≤ M := fun y => by
    rw [hA', hF']
    by_cases hy : y ∈ unitDisc
    · rw [Set.piecewise_eq_of_mem _ _ _ hy, Set.piecewise_eq_of_mem _ _ _ hy]
      exact hd y hy
    · rw [Set.piecewise_eq_of_notMem _ _ _ hy, Set.piecewise_eq_of_notMem _ _ _ hy,
        s07_mo_dist_self]
      exact hM0
  have hac := withDensity_absolutelyContinuous (volume.restrict unitDisc) b
  have hAe : A =ᵐ[(volume.restrict unitDisc).withDensity b] A' :=
    hac.ae_le ((ae_restrict_mem hDm).mono fun y hy => by rw [hA', Set.piecewise_eq_of_mem _ _ _ hy])
  have hFe : F =ᵐ[(volume.restrict unitDisc).withDensity b] F' :=
    hac.ae_le ((ae_restrict_mem hDm).mono fun y hy => by rw [hF', Set.piecewise_eq_of_mem _ _ _ hy])
  obtain ⟨h1, h2⟩ := lem_displacement ((volume.restrict unitDisc).withDensity b) A' F' hA'm hF'm
    hAD hFD' M hM' a ha
  rw [Measure.map_congr hAe, Measure.map_congr hFe]
  refine ⟨?_, h2⟩
  calc poissonP (((volume.restrict unitDisc).withDensity b).map F') a
      = ENNReal.ofReal (Real.exp M) * (ENNReal.ofReal (Real.exp (-M)) *
          poissonP (((volume.restrict unitDisc).withDensity b).map F') a) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp M) *
          poissonP (((volume.restrict unitDisc).withDensity b).map A') a := by
        gcongr

/-- Helper for `prop:qi-transfer`: `F = E(h)` (Theorem 7.5, `L = L(K₀)`) and `F⁻¹`; both are
bi-Lipschitz disk diffeomorphisms and they exchange `∂𝔻`. -/
theorem s07_qi_setup (K₀ : ℝ) : ∃ L : ℝ, 1 ≤ L ∧ ∀ h : ℂ → ℂ, IsStronglyQS h →
    AdmitsQCDiskExt h K₀ → ∃ F Fi : ℂ → ℂ, IsBiLipDiskDiffeo F L ∧ IsBiLipDiskDiffeo Fi L ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, Fi (F z) = z ∧ F (Fi z) = z) ∧
      EqOn F h (sphere (0 : ℂ) 1) ∧
      (∀ ζ ∈ sphere (0 : ℂ) 1, Fi ζ ∈ sphere (0 : ℂ) 1 ∧ F (Fi ζ) = ζ) ∧
      ∀ ζ ∈ sphere (0 : ℂ) 1, F ζ ∈ sphere (0 : ℂ) 1 ∧ Fi (F ζ) = ζ := by
  obtain ⟨L, hL, hDE⟩ := thm_DE (max K₀ 1) (le_max_right _ _)
  refine ⟨L, hL, fun h hh hext => ?_⟩
  have hK : max K₀ 1 = K₀ := by
    obtain ⟨H, hH, -, -⟩ := hext
    exact max_eq_left hH.2.1
  obtain ⟨δf, hδf⟩ := hh
  obtain ⟨F, hFh, hFeq, hFan, hFdet, hFbl⟩ := hDE h hδf.1
  have hF : IsBiLipDiskDiffeo F L :=
    ⟨hFh, hFan.contDiffOn isOpen_ball.uniqueDiffOn, hFdet, hFbl (by rw [hK]; exact hext)⟩
  obtain ⟨Fi, hFi, hinv⟩ := s07_qi_inv_diffeo hF
  -- mutually inverse self-maps of `𝔻̄` preserving `𝔻` exchange `∂𝔻`
  have key : ∀ P Q : ℂ → ℂ, IsClosedDiskHomeo Q → MapsTo P unitDisc unitDisc →
      (∀ w ∈ closedBall (0 : ℂ) 1, P (Q w) = w) → ∀ ζ ∈ sphere (0 : ℂ) 1,
        Q ζ ∈ sphere (0 : ℂ) 1 ∧ P (Q ζ) = ζ := by
    intro P Q hQ hPD hPQ ζ hζ
    have hPQζ := hPQ ζ (sphere_subset_closedBall hζ)
    refine ⟨?_, hPQζ⟩
    have hQc := mem_closedBall_zero_iff.mp (hQ.1.mapsTo (sphere_subset_closedBall hζ))
    rw [mem_sphere_zero_iff_norm]
    rcases hQc.lt_or_eq with hlt | heq
    · exfalso
      have h1 := mem_ball_zero_iff.mp (hPD (mem_ball_zero_iff.mpr hlt))
      rw [hPQζ, mem_sphere_zero_iff_norm.mp hζ] at h1
      exact lt_irrefl _ h1
    · exact heq
  refine ⟨F, Fi, hF, hFi, hinv, hFeq, key F Fi hFi.1 (s07_sb_maps hF.1 hF.2.2.2).1
    (fun w hw => (hinv w hw).2), key Fi F hF.1 (s07_sb_maps hFi.1 hFi.2.2.2).1
      (fun w hw => (hinv w hw).1)⟩

/-- Helper for `prop:qi-transfer`: `P ≤ c Q` on `𝔻` with `c < ∞` and `Q → 0` at `∂𝔻` give
`P → 0` at `∂𝔻`. -/
theorem s07_qi_dbv_le {P Q : ℂ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hPQ : ∀ a ∈ unitDisc, P a ≤ c * Q a) (hQ : DiskBoundaryVanishing Q) :
    DiskBoundaryVanishing P := by
  intro ε hε
  rcases eq_or_ne c 0 with hc0 | hc0
  · refine ⟨0, zero_lt_one, fun a _ ha1 => ?_⟩
    have h := hPQ a (mem_ball_zero_iff.mpr ha1)
    rw [hc0, zero_mul] at h
    exact h.trans bot_le
  obtain ⟨r, hr, hQr⟩ := hQ (ε / c) (ENNReal.div_pos hε.ne' hc)
  refine ⟨r, hr, fun a ha0 ha1 => ?_⟩
  calc P a ≤ c * Q a := hPQ a (mem_ball_zero_iff.mpr ha1)
    _ ≤ c * (ε / c) := by
        gcongr
        exact hQr a ha0 ha1
    _ = ε := ENNReal.mul_div_cancel hc0 hc

/-- Proposition 7.8, `prop:qi-transfer` (`sec07-transfer.tex:365`), norm bounds:
`C⁻¹ ‖ϖ m‖_CM ≤ ‖ϖ A_* m‖_CM ≤ C ‖ϖ m‖_CM`, `C` depending only on `K₀`, `L_A`, `c_A` and the
strong quasisymmetry data `δf`, `δg` of `h` and `h⁻¹`. -/
theorem prop_qi_transfer_norm (K₀ LA cA : ℝ) (δf δg : ℝ → ℝ) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ C ≠ 0 ∧
    ∀ h hinv A : ℂ → ℂ, IsStronglyQSWith h δf →
      (∀ ζ ∈ sphere (0 : ℂ) 1, hinv ζ ∈ sphere (0 : ℂ) 1 ∧ h (hinv ζ) = ζ) →
      IsStronglyQSWith hinv δg → AdmitsQCDiskExt h K₀ → Measurable A → IsDiskQI A LA cA →
      HasDiskBoundaryValues A h → ∀ b : ℂ → ℝ≥0∞, Measurable b →
        C⁻¹ * carlesonNorm (varpiMeasure ((volume.restrict unitDisc).withDensity b)) ≤
            carlesonNorm (varpiMeasure (((volume.restrict unitDisc).withDensity b).map A)) ∧
          carlesonNorm (varpiMeasure (((volume.restrict unitDisc).withDensity b).map A)) ≤
            C * carlesonNorm (varpiMeasure ((volume.restrict unitDisc).withDensity b)) := by
  obtain ⟨L, hL, hset⟩ := s07_qi_setup K₀
  obtain ⟨C₁, hC₁, hT₁⟩ := prop_bilip_transfer_a L δg
  obtain ⟨C₂, hC₂, hT₂⟩ := prop_bilip_transfer_a L δf
  obtain ⟨E, hE⟩ : ∃ E : ℝ≥0∞, E = ENNReal.ofReal (Real.exp (L * morseD (L * LA) (L * cA))) :=
    ⟨_, rfl⟩
  have hEt : E ≠ ⊤ := hE ▸ ENNReal.ofReal_ne_top
  have hE0 : E ≠ 0 := by
    rw [hE]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hL3 : ENNReal.ofReal (L ^ 3) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  refine ⟨320 * E * ENNReal.ofReal (L ^ 3) * (C₁ + C₂ + 1), ?_, ?_, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hEt)
      ENNReal.ofReal_ne_top) (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hC₁, hC₂⟩, ENNReal.one_ne_top⟩)
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hE0) hL3)
      (ne_of_gt (lt_of_lt_of_le one_pos le_add_self))
  intro h hinv A hh hinv1 hhinv hext hAm hA hbd b hb
  obtain ⟨F, Fi, hF, hFi, hFFi, hFh, hFis, hFsph⟩ := hset h ⟨δf, hh⟩ hext
  have hFq : IsStronglyQSWith F δf := s07_qi_sqs_congr hh hFh
  -- `F⁻¹ = h⁻¹` on `∂𝔻`
  have hFih : EqOn Fi hinv (sphere (0 : ℂ) 1) := fun ζ hζ =>
    hF.1.1.injOn (sphere_subset_closedBall (hFis ζ hζ).1)
      (sphere_subset_closedBall (hinv1 ζ hζ).1)
      (by rw [(hFis ζ hζ).2, hFh (hinv1 ζ hζ).1, (hinv1 ζ hζ).2])
  have hFiq : IsStronglyQSWith Fi δg := s07_qi_sqs_congr hhinv hFih
  obtain ⟨b', hb', hpush, hpull⟩ := s07_qi_push_pair hF hFi hFFi b hb
  -- Proposition 7.7 (a) for `F` and for `F⁻¹`
  have hFm := hT₁ F Fi hF ⟨δf, hFq⟩ hFis hFiq b hb
  have hFim := hT₂ Fi F hFi ⟨δg, hFiq⟩ hFsph hFq b' hb'
  rw [hpull, ← hpush] at hFim
  -- (7.9) and Lemma 7.1 (b)
  have hAF := fun a ha => s07_qi_AF hA hAm hbd hF.1 hF.2.2.2 hFh b a ha
  rw [← hE] at hAF
  have hSA : ⨆ a ∈ unitDisc, poissonP (((volume.restrict unitDisc).withDensity b).map A) a ≤
      E * ⨆ a ∈ unitDisc, poissonP (((volume.restrict unitDisc).withDensity b).map F) a :=
    iSup₂_le fun a ha => (hAF a ha).2.trans (by
      gcongr
      exact le_iSup₂ (f := fun a _ => poissonP (((volume.restrict unitDisc).withDensity b).map F) a)
        a ha)
  have hSF : ⨆ a ∈ unitDisc, poissonP (((volume.restrict unitDisc).withDensity b).map F) a ≤
      E * ⨆ a ∈ unitDisc, poissonP (((volume.restrict unitDisc).withDensity b).map A) a :=
    iSup₂_le fun a ha => (hAF a ha).1.trans (by
      gcongr
      exact le_iSup₂ (f := fun a _ => poissonP (((volume.restrict unitDisc).withDensity b).map A) a)
        a ha)
  have hkA := lem_kernel_test_b (((volume.restrict unitDisc).withDensity b).map A)
  have hkF := lem_kernel_test_b (((volume.restrict unitDisc).withDensity b).map F)
  have hC₁le : C₁ ≤ C₁ + C₂ + 1 := le_add_right le_self_add
  have hC₂le : C₂ ≤ C₁ + C₂ + 1 := le_add_right le_add_self
  constructor
  · rw [ENNReal.inv_mul_le_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hE0) hL3)
      (ne_of_gt (lt_of_lt_of_le one_pos le_add_self)))
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hEt)
        ENNReal.ofReal_ne_top)
        (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hC₁, hC₂⟩, ENNReal.one_ne_top⟩))]
    calc carlesonNorm (varpiMeasure ((volume.restrict unitDisc).withDensity b))
        ≤ ENNReal.ofReal (L ^ 3) * C₂ *
            carlesonNorm (varpiMeasure (((volume.restrict unitDisc).withDensity b).map F)) := hFim
      _ ≤ ENNReal.ofReal (L ^ 3) * C₂ *
            (4 * ⨆ a ∈ unitDisc, poissonP (((volume.restrict unitDisc).withDensity b).map F) a) := by
          gcongr
          exact hkF.1
      _ ≤ ENNReal.ofReal (L ^ 3) * C₂ * (4 * (E *
            ⨆ a ∈ unitDisc, poissonP (((volume.restrict unitDisc).withDensity b).map A) a)) := by
          gcongr
      _ ≤ ENNReal.ofReal (L ^ 3) * C₂ * (4 * (E * (80 *
            carlesonNorm (varpiMeasure (((volume.restrict unitDisc).withDensity b).map A))))) := by
          gcongr
          exact hkA.2
      _ = 320 * E * ENNReal.ofReal (L ^ 3) * C₂ *
            carlesonNorm (varpiMeasure (((volume.restrict unitDisc).withDensity b).map A)) := by
          ring
      _ ≤ 320 * E * ENNReal.ofReal (L ^ 3) * (C₁ + C₂ + 1) *
            carlesonNorm (varpiMeasure (((volume.restrict unitDisc).withDensity b).map A)) := by
          gcongr
  · calc carlesonNorm (varpiMeasure (((volume.restrict unitDisc).withDensity b).map A))
        ≤ 4 * ⨆ a ∈ unitDisc, poissonP (((volume.restrict unitDisc).withDensity b).map A) a :=
          hkA.1
      _ ≤ 4 * (E *
            ⨆ a ∈ unitDisc, poissonP (((volume.restrict unitDisc).withDensity b).map F) a) := by
          gcongr
      _ ≤ 4 * (E * (80 *
            carlesonNorm (varpiMeasure (((volume.restrict unitDisc).withDensity b).map F)))) := by
          gcongr
          exact hkF.2
      _ ≤ 4 * (E * (80 * (ENNReal.ofReal (L ^ 3) * C₁ *
            carlesonNorm (varpiMeasure ((volume.restrict unitDisc).withDensity b))))) := by
          gcongr
      _ = 320 * E * ENNReal.ofReal (L ^ 3) * C₁ *
            carlesonNorm (varpiMeasure ((volume.restrict unitDisc).withDensity b)) := by
          ring
      _ ≤ 320 * E * ENNReal.ofReal (L ^ 3) * (C₁ + C₂ + 1) *
            carlesonNorm (varpiMeasure ((volume.restrict unitDisc).withDensity b)) := by
          gcongr

/-- Proposition 7.8, `prop:qi-transfer` (`sec07-transfer.tex:356`), first equivalence: for `h`
strongly quasisymmetric with a `K₀`-q.c. extension and a Borel `(L_A, c_A)`-quasi-isometry `A`
with boundary values `h`, `ϖ m ∈ CM ⟺ ϖ A_* m ∈ CM` (`dm = b dA`). -/
theorem prop_qi_transfer_cm (h : ℂ → ℂ) (K₀ LA cA : ℝ) (hh : IsStronglyQS h)
    (hext : AdmitsQCDiskExt h K₀) (A : ℂ → ℂ) (hAm : Measurable A) (hA : IsDiskQI A LA cA)
    (hbd : HasDiskBoundaryValues A h) (b : ℂ → ℝ≥0∞) (hb : Measurable b) :
    IsCarlesonDisk (varpiMeasure ((volume.restrict unitDisc).withDensity b)) ↔
      IsCarlesonDisk (varpiMeasure (((volume.restrict unitDisc).withDensity b).map A)) := by
  obtain ⟨L, -, hset⟩ := s07_qi_setup K₀
  obtain ⟨F, Fi, -, -, -, hFh, hFis, -⟩ := hset h hh hext
  -- `h⁻¹ = F⁻¹` on `∂𝔻`
  have hhi : ∀ ζ ∈ sphere (0 : ℂ) 1, Fi ζ ∈ sphere (0 : ℂ) 1 ∧ h (Fi ζ) = ζ := fun ζ hζ =>
    ⟨(hFis ζ hζ).1, by rw [← hFh (hFis ζ hζ).1]; exact (hFis ζ hζ).2⟩
  obtain ⟨δf, hδf⟩ := hh
  obtain ⟨δg, hδg⟩ := sqs_circle_inv h Fi ⟨δf, hδf⟩ hhi
  obtain ⟨C, hC, hC0, hN⟩ := prop_qi_transfer_norm K₀ LA cA δf δg
  obtain ⟨hlo, hup⟩ := hN h Fi A hδf hhi hδg hext hAm hA hbd b hb
  rw [ENNReal.inv_mul_le_iff hC0 hC] at hlo
  constructor
  · intro hc
    exact ⟨_, ne_top_of_le_ne_top (ENNReal.mul_ne_top hC (s07_bt_cn_ne_top hc)) hup,
      fun ζ hζ r hr0 hr2 => s07_le_carlesonNorm _ ζ hζ r hr0 hr2⟩
  · intro hc
    exact ⟨_, ne_top_of_le_ne_top (ENNReal.mul_ne_top hC (s07_bt_cn_ne_top hc)) hlo,
      fun ζ hζ r hr0 hr2 => s07_le_carlesonNorm _ ζ hζ r hr0 hr2⟩

/-- Proposition 7.8, `prop:qi-transfer` (`sec07-transfer.tex:363`), second equivalence:
`ϖ m ∈ CM₀ ⟺ ϖ A_* m ∈ CM₀`. -/
theorem prop_qi_transfer_cm0 (h : ℂ → ℂ) (K₀ LA cA : ℝ) (hh : IsStronglyQS h)
    (hext : AdmitsQCDiskExt h K₀) (A : ℂ → ℂ) (hAm : Measurable A) (hA : IsDiskQI A LA cA)
    (hbd : HasDiskBoundaryValues A h) (b : ℂ → ℝ≥0∞) (hb : Measurable b) :
    IsVanishingCarlesonDisk (varpiMeasure ((volume.restrict unitDisc).withDensity b)) ↔
      IsVanishingCarlesonDisk
        (varpiMeasure (((volume.restrict unitDisc).withDensity b).map A)) := by
  obtain ⟨L, -, hset⟩ := s07_qi_setup K₀
  obtain ⟨F, Fi, hF, hFi, hinv, hFh, hFis, -⟩ := hset h hh hext
  obtain ⟨δf, hδf⟩ := hh
  have hFq : IsStronglyQSWith F δf := s07_qi_sqs_congr hδf hFh
  have hFiS : IsStronglyQS Fi := sqs_circle_inv F Fi ⟨δf, hFq⟩ hFis
  have hAF := fun a ha => s07_qi_AF hA hAm hbd hF.1 hF.2.2.2 hFh b a ha
  obtain ⟨b', hb', hpush, hpull⟩ := s07_qi_push_pair hF hFi hinv b hb
  constructor
  · -- `ϖ m ∈ CM₀ ⟹ ϖ F_* m ∈ CM₀` (Prop. 7.7 (b)) `⟹ 𝒫_{F_*m} → 0 ⟹ 𝒫_{A_*m} → 0`
    intro hv
    have h1 := prop_bilip_transfer_b F L hF ⟨δf, hFq⟩ b hb hv
    exact (lem_kernel_test_c _).mpr (s07_qi_dbv_le ENNReal.ofReal_ne_top
      (fun a ha => (hAF a ha).2) ((lem_kernel_test_c _).mp h1))
  · -- `𝒫_{A_*m} → 0 ⟹ 𝒫_{F_*m} → 0 ⟹ ϖ F_* m ∈ CM₀ ⟹ ϖ m = ϖ (F⁻¹)_* F_* m ∈ CM₀`
    intro hv
    have h1 := (lem_kernel_test_c _).mpr (s07_qi_dbv_le ENNReal.ofReal_ne_top
      (fun a ha => (hAF a ha).1) ((lem_kernel_test_c _).mp hv))
    rw [hpush] at h1
    have h2 := prop_bilip_transfer_b Fi L hFi hFiS b' hb' h1
    rwa [hpull] at h2

/-! ## The two sides of the curve -/

/-- `j(z) = 1/z̄`. -/
def jRefl (z : ℂ) : ℂ := (conj z)⁻¹

/-- The point `g(j(z))` of `Ω*`, read through `invAt x₀`; the point `z = 0` goes to `g(∞) = ∞`,
whose image under `invAt x₀` is `0`. -/
def outerPt (g : ℂ → ℂ) (x₀ z : ℂ) : ℂ := if z = 0 then 0 else invAt x₀ (g (jRefl z))

/-- The far-side chart `w ↦ outerPt g x₀ (w̄)` away from `0`. -/
theorem s07_outerPt_conj {g : ℂ → ℂ} {x₀ w : ℂ} (hw : w ≠ 0) :
    outerPt g x₀ (conj w) = invAt x₀ (g w⁻¹) := by
  have hw' : conj w ≠ 0 := by simpa using hw
  simp [outerPt, jRefl, hw']

/-- `w ↦ outerPt g x₀ (w̄)` is a conformal map of `𝔻` onto `invPairΩs Ωs x₀`. -/
theorem s07_outer_conformal {Ωs : Set ℂ} {g : ℂ → ℂ}
    (hg : IsConformalOnto g unitDiscExterior Ωs) (hgInf : Tendsto g (cocompact ℂ) (cocompact ℂ))
    {x₀ : ℂ} (hx₀ : x₀ ∉ Ωs) :
    IsConformalOnto (fun w => outerPt g x₀ (conj w)) unitDisc (invPairΩs Ωs x₀) := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hinvE : ∀ w ∈ unitDisc, w ≠ 0 → w⁻¹ ∈ unitDiscExterior := by
    intro w hw hw0
    have h1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have h0 : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    show 1 < ‖w⁻¹‖
    rw [norm_inv]
    exact one_lt_inv_iff₀.mpr ⟨h0, h1⟩
  have hgx : ∀ u ∈ unitDiscExterior, g u - x₀ ≠ 0 := by
    intro u hu h
    apply hx₀
    rw [← sub_eq_zero.mp h, ← hg.2.2]
    exact mem_image_of_mem g hu
  have hK : ∀ w ∈ unitDisc, w ≠ 0 → DifferentiableAt ℂ (fun u => invAt x₀ (g u⁻¹)) w := by
    intro w hw hw0
    have hgd : DifferentiableAt ℂ g w⁻¹ := hg.1.differentiableAt (hEo.mem_nhds (hinvE w hw hw0))
    exact ((hgd.comp w (differentiableAt_inv hw0)).sub_const x₀).inv (hgx _ (hinvE w hw hw0))
  have hev : ∀ w : ℂ, w ≠ 0 →
      (fun u => outerPt g x₀ (conj u)) =ᶠ[𝓝 w] fun u => invAt x₀ (g u⁻¹) := by
    intro w hw0
    filter_upwards [isOpen_ne.mem_nhds hw0] with u hu
    exact s07_outerPt_conj hu
  have h00 : outerPt g x₀ (conj 0) = 0 := by simp [outerPt]
  refine ⟨?_, ?_, ?_⟩
  · refine (differentiableOn_compl_singleton_and_continuousAt_iff
      (isOpen_ball.mem_nhds (mem_ball_self one_pos))).mp ⟨?_, ?_⟩
    · intro w hw
      exact ((hK w hw.1 hw.2).congr_of_eventuallyEq (hev w hw.2)).differentiableWithinAt
    · rw [← continuousWithinAt_compl_self, ContinuousWithinAt, h00]
      have hT : Tendsto (fun u => invAt x₀ (g u⁻¹)) (𝓝[≠] 0) (𝓝 0) := by
        have h1 : Tendsto (fun u : ℂ => u⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
          rw [← Metric.cobounded_eq_cocompact]
          exact tendsto_inv₀_nhdsNE_zero
        have h2 : Tendsto (fun v : ℂ => v - x₀) (cocompact ℂ) (cocompact ℂ) := by
          rw [← Metric.cobounded_eq_cocompact]
          exact tendsto_sub_const_cobounded x₀
        have h3 : Tendsto (fun v : ℂ => v⁻¹) (cocompact ℂ) (𝓝 0) := by
          rw [← Metric.cobounded_eq_cocompact]
          exact tendsto_inv₀_cobounded
        exact h3.comp (h2.comp (hgInf.comp h1))
      refine hT.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (s07_outerPt_conj hu).symm
  · intro w hw w' hw' h
    simp only at h
    by_cases hw0 : w = 0 <;> by_cases hw0' : w' = 0
    · rw [hw0, hw0']
    · exfalso
      rw [hw0, h00, s07_outerPt_conj hw0'] at h
      exact inv_ne_zero (hgx _ (hinvE w' hw' hw0')) h.symm
    · exfalso
      rw [hw0', h00, s07_outerPt_conj hw0] at h
      exact inv_ne_zero (hgx _ (hinvE w hw hw0)) h
    · rw [s07_outerPt_conj hw0, s07_outerPt_conj hw0'] at h
      simp only [invAt, inv_inj, sub_left_inj] at h
      exact inv_inj.mp (hg.2.1 (hinvE w hw hw0) (hinvE w' hw' hw0') h)
  · ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      by_cases hw0 : w = 0
      · right
        exact mem_singleton_iff.mpr (by rw [hw0]; exact h00)
      · left
        show outerPt g x₀ (conj w) ∈ invAt x₀ '' Ωs
        rw [s07_outerPt_conj hw0, ← hg.2.2]
        exact ⟨g w⁻¹, mem_image_of_mem g (hinvE w hw hw0), rfl⟩
    · rintro (⟨y, hy, rfl⟩ | hv)
      · rw [← hg.2.2] at hy
        obtain ⟨u, hu, rfl⟩ := hy
        have hu1 : 1 < ‖u‖ := hu
        have hu0 : u ≠ 0 := by
          intro h
          rw [h, norm_zero] at hu1
          linarith
        refine ⟨u⁻¹, ?_, ?_⟩
        · show u⁻¹ ∈ ball (0 : ℂ) 1
          rw [mem_ball_zero_iff, norm_inv]
          exact inv_lt_one_of_one_lt₀ hu1
        · simp only
          rw [s07_outerPt_conj (inv_ne_zero hu0), inv_inv]
      · rw [mem_singleton_iff.mp hv]
        exact ⟨0, mem_ball_self one_pos, h00⟩

/-- Carathéodory for the bounded component: if `f : 𝔻 → Ω` is conformal and `f → x` at `ζ ∈ ∂𝔻`,
then `f(u) → x` with `u ∈ 𝔻` forces `u → ζ`.  `Ω = F(𝔻)` is bounded because the global
homeomorphism `F` maps the compact disk `𝔻̄` onto a compact set; `∂Ω = F(∂𝔻)` is a Jordan curve;
LZ `caratheodory_jordan` gives a homeomorphism of `𝔻̄` onto `Ω̄` extending `f`. -/
theorem s07_disk_preimage_tendsto {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {ζ x : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1)
    (hfx : Tendsto f (𝓝[unitDisc] ζ) (𝓝 x)) {α : Type*} {l : Filter α} {u : α → ℂ}
    (hu : ∀ᶠ t in l, u t ∈ unitDisc) (hfu : Tendsto (fun t => f (u t)) l (𝓝 x)) :
    Tendsto u l (𝓝 ζ) := by
  obtain ⟨F, hFq, hFs, hF1, -⟩ := hΓ
  obtain ⟨e, rfl⟩ := t1_homeomorph hFq hFs
  have hbdd : Bornology.IsBounded Ω := by
    rw [← hF1]
    exact ((isCompact_closedBall (0 : ℂ) 1).image e.continuous).isBounded.subset
      (image_mono ball_subset_closedBall)
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hJ : IsJordanCurve (frontier (toExt Ω)) := by
    rw [frontier_toExt_of_isBounded' hbdd hΩo, ← hF1, ← e.image_frontier]
    show IsJordanCurve (toExt (e '' frontier (ball 0 1)))
    rw [frontier_ball (0 : ℂ) one_ne_zero]
    refine ⟨fun θ => ((e θ : ℂ) : ExtPlane), ?_, ?_, ?_⟩
    · exact OnePoint.continuous_coe.comp (e.continuous.comp continuous_subtype_val)
    · exact fun a b hab => Circle.coe_injective (e.injective (OnePoint.coe_injective hab))
    · unfold toExt
      ext w
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨θ, rfl⟩
        exact ⟨e θ, ⟨(θ : ℂ), mem_sphere_zero_iff_norm.2 (Circle.norm_coe θ), rfl⟩, rfl⟩
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨⟨z, hz⟩, rfl⟩
  obtain ⟨Fe, hFe1, hFe2, hFe3, -⟩ := caratheodory_jordan hbdd hf hJ
  have hcl : closure (toExt unitDisc) = toExt (closedBall (0 : ℂ) 1) := by
    rw [closure_toExt_of_isBounded' (show Bornology.IsBounded unitDisc from isBounded_ball)]
    show toExt (closure (ball (0 : ℂ) 1)) = _
    rw [closure_ball (0 : ℂ) one_ne_zero]
  set S : Set ℂ := closedBall 0 1 with hS
  set φ : ℂ → ExtPlane := fun z => Fe (z : ExtPlane) with hφ
  have hmapS : ∀ z ∈ S, (z : ExtPlane) ∈ closure (toExt unitDisc) := fun z hz => by
    rw [hcl]
    exact mem_image_of_mem _ hz
  have hφc : ContinuousOn φ S := hFe2.comp OnePoint.continuous_coe.continuousOn hmapS
  have hφi : InjOn φ S := fun a ha b hb hab => OnePoint.coe_injective (hFe3 (hmapS a ha) (hmapS b hb) hab)
  have hDS : unitDisc ⊆ S := ball_subset_closedBall
  have hζS : ζ ∈ S := sphere_subset_closedBall hζ
  -- `φ ζ = x`
  have hφζ : φ ζ = (x : ExtPlane) := by
    haveI : (𝓝[unitDisc] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
      show ζ ∈ closure (ball (0 : ℂ) 1)
      rw [closure_ball (0 : ℂ) one_ne_zero]
      exact hζS)
    have h1 : Tendsto φ (𝓝[unitDisc] ζ) (𝓝 (φ ζ)) :=
      (hφc ζ hζS).tendsto.mono_left (nhdsWithin_mono _ hDS)
    have h2 : Tendsto φ (𝓝[unitDisc] ζ) (𝓝 (x : ExtPlane)) :=
      ((OnePoint.continuous_coe.tendsto x).comp hfx).congr'
        (eventually_nhdsWithin_of_forall fun z hz => (hFe1 z hz).symm)
    exact tendsto_nhds_unique h1 h2
  have hlim : Tendsto (fun t => φ (u t)) l (𝓝 (x : ExtPlane)) :=
    ((OnePoint.continuous_coe.tendsto x).comp hfu).congr'
      (hu.mono fun t ht => (hFe1 (u t) ht).symm)
  have huS : ∀ᶠ t in l, u t ∈ S := hu.mono fun t ht => hDS ht
  refine (isCompact_closedBall (0 : ℂ) 1).tendsto_nhds_of_unique_mapClusterPt huS
    fun y hy hc => ?_
  have hmap : map u l ≤ 𝓟 S := tendsto_principal.2 huS
  have hc' : MapClusterPt (φ y) l (φ ∘ u) :=
    hc.tendsto_comp' ((hφc y hy).tendsto.mono_left (inf_le_inf_left _ hmap))
  have hne : (𝓝 (φ y) ⊓ 𝓝 (x : ExtPlane)).NeBot :=
    Filter.NeBot.mono (show (𝓝 (φ y) ⊓ map (φ ∘ u) l).NeBot from hc')
      (inf_le_inf_left _ hlim)
  exact hφi hy hζS ((eq_of_nhds_neBot hne).trans hφζ.symm)

/-- (7.10), inner factor: for the global `K`-q.c. map `F` of a bounded quasicircle and
`g : 𝔻* → Ω*` conformal with `g(∞) = ∞`, the map `P = j ∘ F⁻¹ ∘ g ∘ j` (with `P 0 = 0`) is a
`K`-q.c. self-map of `𝔻`; it is characterized by `F (j (P z)) = g (j z)` off `0`. -/
theorem s07_weld_inner {K : ℝ} {Ωs : Set ℂ} {F g : ℂ → ℂ} (hF : IsKQC F univ K)
    (hFs : F '' univ = univ) (hF2 : F '' unitDiscExterior = Ωs)
    (hg : IsConformalOnto g unitDiscExterior Ωs) (hgInf : Tendsto g (cocompact ℂ) (cocompact ℂ)) :
    ∃ P : ℂ → ℂ, IsKQC P unitDisc K ∧ P '' unitDisc = unitDisc ∧ P 0 = 0 ∧
      ∀ z ∈ unitDisc, z ≠ 0 → F (jRefl (P z)) = g (jRefl z) := by
  obtain ⟨e, rfl⟩ := t1_homeomorph hF hFs
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hΩso : IsOpen Ωs := hg.isOpen hEo
  set D0 : Set ℂ := unitDisc \ {0} with hD0
  have hD0o : IsOpen D0 := isOpen_ball.sdiff isClosed_singleton
  have hjj : ∀ z : ℂ, jRefl (jRefl z) = z := fun z => by
    show (conj (conj z)⁻¹)⁻¹ = z
    rw [map_inv₀, Complex.conj_conj, inv_inv]
  have hjE : ∀ z ∈ unitDisc, z ≠ 0 → jRefl z ∈ unitDiscExterior := fun z hz hz0 => by
    show 1 < ‖(conj z)⁻¹‖
    rw [norm_inv, Complex.norm_conj]
    exact (one_lt_inv₀ (norm_pos_iff.2 hz0)).2 (mem_ball_zero_iff.1 hz)
  have hjD : ∀ u ∈ unitDiscExterior, jRefl u ∈ unitDisc ∧ jRefl u ≠ 0 := fun u hu => by
    have hu1 : 1 < ‖u‖ := hu
    have hu0 : u ≠ 0 := norm_pos_iff.1 (one_pos.trans hu1)
    refine ⟨?_, inv_ne_zero ((map_ne_zero _).2 hu0)⟩
    show (conj u)⁻¹ ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, norm_inv, Complex.norm_conj]
    exact inv_lt_one_of_one_lt₀ hu1
  have heE : ∀ y ∈ Ωs, e.symm y ∈ unitDiscExterior := fun y hy => by
    rw [← hF2] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    rwa [e.symm_apply_apply]
  set P : ℂ → ℂ := fun z => if z = 0 then 0 else jRefl (e.symm (g (jRefl z))) with hP
  have hP0 : P 0 = 0 := ite_eq_left_iff.2 fun h => absurd rfl h
  have hPz : ∀ z : ℂ, z ≠ 0 → P z = jRefl (e.symm (g (jRefl z))) := fun z hz => if_neg hz
  -- `K`-q.c. on `𝔻 \ {0}`: `P = conj ∘ (inv ∘ e⁻¹ ∘ g ∘ inv) ∘ conj`
  have k1 : IsKQC (fun w : ℂ => w⁻¹) D0 1 :=
    nx_isKQC_restrict (by simpa only [sub_zero] using b4_qc_invShift_isKQC 0) hD0o
      (fun z hz => hz.2)
  have k2 : IsKQC g unitDiscExterior 1 := isKQC_one_of_conformal hEo hg
  have hinv : EqOn (⇑e.symm) (Function.invFunOn (⇑e) univ) Ωs := fun y _ => by
    apply e.injective
    rw [e.apply_symm_apply, Function.invFunOn_eq ⟨e.symm y, mem_univ _, e.apply_symm_apply y⟩]
  have k3 : IsKQC (⇑e.symm) Ωs K :=
    ad_isKQC_congr (nx_isKQC_restrict (thm7_2_inv hF) hΩso (by rw [hFs]; exact subset_univ _))
      hinv
  have k4 : IsKQC (fun w : ℂ => w⁻¹) unitDiscExterior 1 :=
    nx_isKQC_restrict (by simpa only [sub_zero] using b4_qc_invShift_isKQC 0) hEo
      (fun u hu => by
        have hu1 : 1 < ‖u‖ := hu
        exact norm_pos_iff.1 (one_pos.trans hu1))
  have hs1 : (fun w : ℂ => w⁻¹) '' D0 ⊆ unitDiscExterior := by
    rintro _ ⟨z, ⟨hz, hz0⟩, rfl⟩
    show 1 < ‖z⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.2 hz0)).2 (mem_ball_zero_iff.1 hz)
  have hs2 : (g ∘ fun w : ℂ => w⁻¹) '' D0 ⊆ Ωs := by
    rw [image_comp]
    exact (image_mono hs1).trans hg.2.2.le
  have hs3 : (⇑e.symm ∘ (g ∘ fun w : ℂ => w⁻¹)) '' D0 ⊆ unitDiscExterior := by
    rintro _ ⟨z, hz, rfl⟩
    exact heE _ (hs2 ⟨z, hz, rfl⟩)
  have c3 := thm7_1_comp (thm7_1_comp (thm7_1_comp k1 k2 hs1) k3 hs2) k4 hs3
  simp only [one_mul, mul_one] at c3
  have c4 := abR_x_isKQC_conj c3
  have hcD : conj ⁻¹' D0 = D0 := by
    ext z
    have e1 : conj z ∈ unitDisc ↔ z ∈ unitDisc := by
      show conj z ∈ ball (0 : ℂ) 1 ↔ z ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff, mem_ball_zero_iff, Complex.norm_conj]
    have e2 : conj z ∈ ({0} : Set ℂ) ↔ z ∈ ({0} : Set ℂ) := by
      rw [mem_singleton_iff, mem_singleton_iff, map_eq_zero]
    exact and_congr e1 (not_congr e2)
  rw [hcD] at c4
  have c5 : IsKQC P D0 K := ad_isKQC_congr c4 (fun z hz => by
    rw [hPz z hz.2]
    show (conj (e.symm (g (conj z)⁻¹)))⁻¹ = conj ((e.symm (g (conj z)⁻¹))⁻¹)
    rw [map_inv₀])
  -- `P` maps `𝔻 \ {0}` into itself
  have hPD0 : ∀ z ∈ unitDisc, z ≠ 0 → P z ∈ unitDisc ∧ P z ≠ 0 := fun z hz hz0 => by
    rw [hPz z hz0]
    exact hjD _ (heE _ (hg.2.2 ▸ mem_image_of_mem g (hjE z hz hz0)))
  -- continuity at `0`
  have hT : Tendsto (fun z => jRefl (e.symm (g (jRefl z)))) (𝓝[≠] 0) (𝓝 0) := by
    have h0 : Tendsto (fun z : ℂ => conj z) (𝓝[≠] 0) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨(Complex.continuous_conj.tendsto' 0 0 (map_zero _)).mono_left
        nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun z hz => by simpa using hz⟩
    have h1 : Tendsto jRefl (𝓝[≠] 0) (cocompact ℂ) := by
      rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_nhdsNE_zero.comp h0
    have h2 : Tendsto (⇑e.symm) (cocompact ℂ) (cocompact ℂ) :=
      e.symm.isClosedEmbedding.tendsto_cocompact
    have h3 : Tendsto jRefl (cocompact ℂ) (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have : (fun y : ℂ => ‖jRefl y‖) = fun y => ‖y‖⁻¹ := funext fun y => by
        show ‖(conj y)⁻¹‖ = _
        rw [norm_inv, Complex.norm_conj]
      rw [this]
      exact tendsto_inv_atTop_zero.comp tendsto_norm_cocompact_atTop
    exact h3.comp (h2.comp (hgInf.comp h1))
  have hPc : ContinuousOn P unitDisc := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      refine ContinuousAt.continuousWithinAt ?_
      rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hP0]
      refine hT.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (hPz u hu).symm
    · exact (c5.2.2.1.1.continuousAt (hD0o.mem_nhds ⟨hz, hz0⟩)).continuousWithinAt
  have hPi : InjOn P unitDisc := by
    intro z hz w hw h
    by_cases hz0 : z = 0 <;> by_cases hw0 : w = 0
    · rw [hz0, hw0]
    · exfalso
      rw [hz0, hP0] at h
      exact (hPD0 w hw hw0).2 h.symm
    · exfalso
      rw [hw0, hP0] at h
      exact (hPD0 z hz hz0).2 h
    · exact c5.2.2.1.2.1 ⟨hz, hz0⟩ ⟨hw, hw0⟩ h
  have hPs : P '' unitDisc = unitDisc := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      by_cases hz0 : z = 0
      · rw [hz0, hP0]
        exact mem_ball_self one_pos
      · exact (hPD0 z hz hz0).1
    · intro w hw
      by_cases hw0 : w = 0
      · exact ⟨0, mem_ball_self one_pos, by rw [hw0, hP0]⟩
      · have h1 : e (jRefl w) ∈ g '' unitDiscExterior := by
          rw [hg.2.2, ← hF2]
          exact mem_image_of_mem _ (hjE w hw hw0)
        obtain ⟨u, hu, hgu⟩ := h1
        obtain ⟨hjuD, hju0⟩ := hjD u hu
        refine ⟨jRefl u, hjuD, ?_⟩
        rw [hPz _ hju0, hjj, hgu, e.symm_apply_apply, hjj]
  have hK1 : 1 ≤ K := hF.2.1
  have hPK : IsKQC P unitDisc K := by
    refine s13x_removable (L := {0}) isOpen_ball hK1
      (qcl_f_isHomeomorphOnto_of_injOn isOpen_ball hPc hPi) (measure_singleton 0)
      (Eventually.of_forall fun x => Set.Subsingleton.countable fun y hy y' hy' => ?_)
      (Eventually.of_forall fun y => Set.Subsingleton.countable fun x hx x' hx' => ?_)
      (fun z hz => ⟨D0, hD0o, hz, sdiff_subset, c5⟩)
    · have hy0 : (x : ℂ) + (y : ℂ) * I = 0 := hy
      have hy0' : (x : ℂ) + (y' : ℂ) * I = 0 := hy'
      have h1 := congrArg Complex.im hy0
      have h2 := congrArg Complex.im hy0'
      simp at h1 h2
      rw [h1, h2]
    · have hx0 : (x : ℂ) + (y : ℂ) * I = 0 := hx
      have hx0' : (x' : ℂ) + (y : ℂ) * I = 0 := hx'
      have h1 := congrArg Complex.re hx0
      have h2 := congrArg Complex.re hx0'
      simp at h1 h2
      rw [h1, h2]
  refine ⟨P, hPK, hPs, hP0, fun z _ hz0 => ?_⟩
  rw [hPz z hz0, hjj, e.apply_symm_apply]

/-- (7.10): the welding `h` of a bounded `K`-quasicircle has the `K²`-q.c. extension
`f⁻¹ ∘ F ∘ P` to `𝔻` (`F ∘ j ∘ F⁻¹` is the reflection across the curve). -/
theorem s07_weld_admitsExt {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    {f g h : ℂ → ℂ} (hw : IsDiskWelding Ω Ωs f g h) : AdmitsQCDiskExt h (K * K) := by
  obtain ⟨hf, hg, hgInf, hhS, hhb⟩ := hw
  obtain ⟨F, hFq, hFs, hF1, hF2⟩ := id hΓ
  obtain ⟨P, hPq, hPs, hP0, hPF⟩ := s07_weld_inner hFq hFs hF2 hg hgInf
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
  refine ⟨fi ∘ (⇑e ∘ P), c2, ?_, fun ζ hζ => ?_⟩
  · rw [image_comp, image_comp, hPs, hF1]
    exact hfs.2.2
  obtain ⟨x, hfx, hgx⟩ := hhb ζ hζ
  have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.1 hζ
  have hζ0 : ζ ≠ 0 := norm_ne_zero_iff.1 (by rw [hζ1]; exact one_ne_zero)
  have hcl : ∀ w : ℂ, ‖w‖ = 1 → w ∈ closure unitDisc := fun w hw => by
    show w ∈ closure (ball (0 : ℂ) 1)
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact mem_closedBall_zero_iff.2 hw.le
  haveI : (𝓝[unitDisc] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hcl ζ hζ1)
  haveI : (𝓝[unitDisc] (h ζ)).NeBot :=
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

/-- Carathéodory, parametrized form: if `e` is continuous and injective on `𝔻̄` with `e(𝔻) = U`
and `f : 𝔻 → U` is conformal, then `f` extends to a continuous injection `φ` of `𝔻̄` with
`φ(∂𝔻) = e(∂𝔻)` (`U` is bounded, `∂U = e(∂𝔻)` is a Jordan curve; LZ `caratheodory_jordan`). -/
theorem s07_carath_core {U : Set ℂ} {e f : ℂ → ℂ} (he : ContinuousOn e (closedBall (0 : ℂ) 1))
    (hei : InjOn e (closedBall (0 : ℂ) 1)) (heU : e '' unitDisc = U)
    (hf : IsConformalOnto f unitDisc U) :
    ∃ φ : ℂ → ℂ, ContinuousOn φ (closedBall (0 : ℂ) 1) ∧ InjOn φ (closedBall (0 : ℂ) 1) ∧
      (∀ z ∈ unitDisc, φ z = f z) ∧ φ '' sphere (0 : ℂ) 1 = e '' sphere (0 : ℂ) 1 := by
  set S : Set ℂ := closedBall (0 : ℂ) 1 with hS
  have hU : IsOpen U := hf.isOpen isOpen_ball
  have hcb : IsCompact (e '' S) := (isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn he
  have hBS : unitDisc ⊆ S := ball_subset_closedBall
  have hSD : S \ unitDisc = sphere (0 : ℂ) 1 := closedBall_sdiff_ball
  have hUS : U ⊆ e '' S := heU ▸ image_mono hBS
  have hbdd : Bornology.IsBounded U := hcb.isBounded.subset hUS
  have hclD : closure unitDisc = S := closure_ball (0 : ℂ) one_ne_zero
  have hclU : closure U = e '' S := by
    refine Subset.antisymm (closure_minimal hUS hcb.isClosed) ?_
    have := ContinuousOn.image_closure (s := unitDisc) (by rw [hclD]; exact he)
    rwa [hclD, heU] at this
  have hfrU : frontier U = e '' sphere (0 : ℂ) 1 := by
    rw [hU.frontier_eq, hclU, ← heU, ← hei.image_sdiff_subset hBS, hSD]
  have hsS : ∀ θ : Circle, (θ : ℂ) ∈ S := fun θ =>
    sphere_subset_closedBall (mem_sphere_zero_iff_norm.2 (Circle.norm_coe θ))
  have hJ : IsJordanCurve (frontier (toExt U)) := by
    rw [frontier_toExt_of_isBounded' hbdd hU, hfrU]
    refine ⟨fun θ => ((e θ : ℂ) : ExtPlane), ?_, ?_, ?_⟩
    · exact OnePoint.continuous_coe.comp (he.comp_continuous continuous_subtype_val hsS)
    · exact fun a b hab => Circle.coe_injective (hei (hsS a) (hsS b) (OnePoint.coe_injective hab))
    · unfold toExt
      ext w
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨θ, rfl⟩
        exact ⟨e θ, ⟨(θ : ℂ), mem_sphere_zero_iff_norm.2 (Circle.norm_coe θ), rfl⟩, rfl⟩
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨⟨z, hz⟩, rfl⟩
  obtain ⟨Fe, hFe1, hFe2, hFe3, hFe4⟩ := caratheodory_jordan hbdd hf hJ
  have hclE : closure (toExt unitDisc) = toExt S := by
    rw [closure_toExt_of_isBounded' (show Bornology.IsBounded unitDisc from isBounded_ball), hclD]
  rw [hclE] at hFe2 hFe3 hFe4
  rw [closure_toExt_of_isBounded' hbdd, hclU] at hFe4
  have hfin : ∀ z ∈ S, ∃ w : ℂ, w ∈ e '' S ∧ Fe z = w := fun z hz => by
    have : Fe z ∈ toExt (e '' S) := hFe4 ▸ mem_image_of_mem Fe (mem_image_of_mem _ hz)
    obtain ⟨w, hw, hw'⟩ := this
    exact ⟨w, hw, hw'.symm⟩
  choose! φ hφS hφ using hfin
  have hφc : ContinuousOn φ S := by
    refine (OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_iff).2 ?_
    exact (hFe2.comp OnePoint.continuous_coe.continuousOn fun z hz => mem_image_of_mem _ hz).congr
      fun z hz => (hφ z hz).symm
  have hφi : InjOn φ S := fun a ha b hb hab =>
    OnePoint.coe_injective (hFe3 (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)
      (by rw [hφ a ha, hφ b hb, hab]))
  have hφf : ∀ z ∈ unitDisc, φ z = f z := fun z hz =>
    OnePoint.coe_injective ((hφ z (hBS hz)).symm.trans (hFe1 z hz))
  have hφimg : φ '' S = e '' S := by
    refine Subset.antisymm (fun _ ⟨z, hz, hzw⟩ => hzw ▸ hφS z hz) fun w hw => ?_
    have : ((w : ℂ) : ExtPlane) ∈ Fe '' toExt S := hFe4.symm ▸ mem_image_of_mem _ hw
    obtain ⟨_, ⟨z, hz, rfl⟩, hzw⟩ := this
    exact ⟨z, hz, OnePoint.coe_injective ((hφ z hz).symm.trans hzw)⟩
  have hφD : φ '' unitDisc = U := by
    rw [← hf.2.2]
    exact image_congr hφf
  refine ⟨φ, hφc, hφi, hφf, ?_⟩
  rw [← hSD, hφi.image_sdiff_subset hBS, hφimg, hφD, ← heU, ← hei.image_sdiff_subset hBS]

/-- The far-side chart `w ↦ outerPt g (F 0) (w̄)` of a bounded quasicircle extends to a
continuous injection of `𝔻̄` carrying `∂𝔻` onto `invAt (F 0) '' Γ` (`s07_carath_core` with
`e(z) = invAt (F 0) (F (1/z))`, `e 0 = 0`, and `s07_outer_conformal`). -/
theorem s07_outer_extends {K : ℝ} {Ωs : Set ℂ} {F g : ℂ → ℂ} (hF : IsKQC F univ K)
    (hFs : F '' univ = univ) (hF2 : F '' unitDiscExterior = Ωs)
    (hg : IsConformalOnto g unitDiscExterior Ωs) (hgInf : Tendsto g (cocompact ℂ) (cocompact ℂ)) :
    ∃ ψ : ℂ → ℂ, ContinuousOn ψ (closedBall (0 : ℂ) 1) ∧ InjOn ψ (closedBall (0 : ℂ) 1) ∧
      (∀ w ∈ unitDisc, ψ w = outerPt g (F 0) (conj w)) ∧
      ψ '' sphere (0 : ℂ) 1 = invAt (F 0) '' (F '' sphere (0 : ℂ) 1) := by
  obtain ⟨E, rfl⟩ := t1_homeomorph hF hFs
  set x₀ := E 0 with hx₀
  have hx₀s : x₀ ∉ Ωs := by
    rw [← hF2]
    rintro ⟨u, hu, hue⟩
    have hu0 : u = 0 := E.injective hue
    have hu1 : 1 < ‖u‖ := hu
    rw [hu0, norm_zero] at hu1
    exact absurd hu1 (by norm_num)
  have hEne : ∀ z : ℂ, z ≠ 0 → E z⁻¹ ≠ x₀ := fun z hz h => inv_ne_zero hz (E.injective h)
  set e : ℂ → ℂ := fun z => if z = 0 then 0 else invAt x₀ (E z⁻¹) with he
  have he0 : e 0 = 0 := ite_eq_left_iff.2 fun h => absurd rfl h
  have hez : ∀ z : ℂ, z ≠ 0 → e z = invAt x₀ (E z⁻¹) := fun z hz => if_neg hz
  have hez0 : ∀ z : ℂ, z ≠ 0 → e z ≠ 0 := fun z hz => by
    rw [hez z hz]
    exact inv_ne_zero (sub_ne_zero.2 (hEne z hz))
  have hec : Continuous e := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z = 0
    · subst hz
      rw [← continuousWithinAt_compl_self, ContinuousWithinAt, he0]
      have h1 : Tendsto (fun u : ℂ => u⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
        rw [← Metric.cobounded_eq_cocompact]
        exact tendsto_inv₀_nhdsNE_zero
      have h2 : Tendsto (⇑E) (cocompact ℂ) (cocompact ℂ) := E.isClosedEmbedding.tendsto_cocompact
      have h3 : Tendsto (fun v : ℂ => v - x₀) (cocompact ℂ) (cocompact ℂ) := by
        rw [← Metric.cobounded_eq_cocompact]
        exact tendsto_sub_const_cobounded x₀
      have h4 : Tendsto (fun v : ℂ => v⁻¹) (cocompact ℂ) (𝓝 0) := by
        rw [← Metric.cobounded_eq_cocompact]
        exact tendsto_inv₀_cobounded
      exact (h4.comp (h3.comp (h2.comp h1))).congr'
        (eventually_nhdsWithin_of_forall fun u hu => (hez u hu).symm)
    · have : ContinuousAt (fun z => invAt x₀ (E z⁻¹)) z := by
        show ContinuousAt (fun z => (E z⁻¹ - x₀)⁻¹) z
        exact ((E.continuous.continuousAt.comp (continuousAt_inv₀ hz)).sub
          continuousAt_const).inv₀ (sub_ne_zero.2 (hEne z hz))
      exact this.congr ((eventually_ne_nhds hz).mono fun u hu => (hez u hu).symm)
  have hei : Function.Injective e := by
    intro a b h
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · rw [ha, hb]
    · exfalso
      rw [ha, he0] at h
      exact hez0 b hb h.symm
    · exfalso
      rw [hb, he0] at h
      exact hez0 a ha h
    · rw [hez a ha, hez b hb] at h
      simp only [invAt, inv_inj, sub_left_inj] at h
      exact inv_injective (E.injective h)
  have hinvD : ∀ u : ℂ, u ∈ unitDiscExterior → u⁻¹ ∈ unitDisc ∧ u⁻¹ ≠ 0 := fun u hu => by
    have hu1 : 1 < ‖u‖ := hu
    have hu0 : u ≠ 0 := norm_pos_iff.1 (one_pos.trans hu1)
    refine ⟨?_, inv_ne_zero hu0⟩
    show u⁻¹ ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, norm_inv]
    exact inv_lt_one_of_one_lt₀ hu1
  have himg : e '' unitDisc = invPairΩs Ωs x₀ := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      by_cases hz0 : z = 0
      · right
        rw [hz0, he0]
        exact mem_singleton _
      · left
        rw [hez z hz0]
        refine mem_image_of_mem _ (hF2 ▸ mem_image_of_mem E ?_)
        show 1 < ‖z⁻¹‖
        rw [norm_inv]
        exact (one_lt_inv₀ (norm_pos_iff.2 hz0)).2 (mem_ball_zero_iff.1 hz)
    · rintro (⟨y, hy, rfl⟩ | hw)
      · rw [← hF2] at hy
        obtain ⟨u, hu, rfl⟩ := hy
        obtain ⟨huD, hu0⟩ := hinvD u hu
        exact ⟨u⁻¹, huD, by rw [hez _ hu0, inv_inv]⟩
      · rw [mem_singleton_iff.1 hw]
        exact ⟨0, mem_ball_self one_pos, he0⟩
  obtain ⟨ψ, hψc, hψi, hψf, hψs⟩ :=
    s07_carath_core hec.continuousOn hei.injOn himg (s07_outer_conformal hg hgInf hx₀s)
  refine ⟨ψ, hψc, hψi, hψf, ?_⟩
  rw [hψs]
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 hz
    have hz0 : z ≠ 0 := norm_ne_zero_iff.1 (by rw [hz1]; exact one_ne_zero)
    rw [hez z hz0]
    exact ⟨E z⁻¹, ⟨z⁻¹, mem_sphere_zero_iff_norm.2 (by rw [norm_inv, hz1, inv_one]), rfl⟩, rfl⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    have hu1 : ‖u‖ = 1 := mem_sphere_zero_iff_norm.1 hu
    have hu0 : u ≠ 0 := norm_ne_zero_iff.1 (by rw [hu1]; exact one_ne_zero)
    refine ⟨u⁻¹, mem_sphere_zero_iff_norm.2 (by rw [norm_inv, hu1, inv_one]), ?_⟩
    rw [hez _ (inv_ne_zero hu0), inv_inv]

/-- `sec07-transfer.tex:402–410`: for a bounded quasicircle, `f` and `g` extend to
homeomorphisms of the closures, so the welding `h` exists and is an orientation-preserving
homeomorphism of `∂𝔻`. -/
theorem sec07_welding_exists (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    (f g : ℂ → ℂ) (hf : IsConformalOnto f unitDisc Ω) (hg : IsConformalOnto g unitDiscExterior Ωs)
    (hgInf : Tendsto g (cocompact ℂ) (cocompact ℂ)) :
    ∃ h : ℂ → ℂ, IsDiskWelding Ω Ωs f g h ∧ IsCircleHomeo h := by
  obtain ⟨F, hFq, hFs, hF1, hF2⟩ := id hΓ
  obtain ⟨ψ, hψc, hψi, hψf, hψs⟩ := s07_outer_extends hFq hFs hF2 hg hgInf
  obtain ⟨E, rfl⟩ := t1_homeomorph hFq hFs
  obtain ⟨φ, hφc, hφi, hφf, hφs⟩ :=
    s07_carath_core E.continuous.continuousOn E.injective.injOn hF1 hf
  set x₀ := E 0 with hx₀
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hx₀s : ∀ y ∈ Ωs, y ≠ x₀ := by
    rw [← hF2]
    rintro _ ⟨u, hu, rfl⟩ h
    have hu0 : u = 0 := E.injective h
    have hu1 : 1 < ‖u‖ := hu
    rw [hu0, norm_zero] at hu1
    exact absurd hu1 (by norm_num)
  -- the boundary point of `g` at `ζ`
  have hgb : ∀ ζ ∈ sphere (0 : ℂ) 1, x₀ + (ψ (conj ζ))⁻¹ ∈ φ '' sphere (0 : ℂ) 1 ∧
      Tendsto g (𝓝[unitDiscExterior] ζ) (𝓝 (x₀ + (ψ (conj ζ))⁻¹)) := by
    intro ζ hζ
    have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.1 hζ
    have hcζ : conj ζ ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.2 (by rw [Complex.norm_conj, hζ1])
    have hζinv : ζ⁻¹ = conj ζ := inv_eq_of_mul_eq_one_right (by rw [Complex.mul_conj', hζ1]; norm_num)
    obtain ⟨_, ⟨η, hη, rfl⟩, hψη⟩ : ψ (conj ζ) ∈ invAt x₀ '' (E '' sphere (0 : ℂ) 1) :=
      hψs ▸ mem_image_of_mem ψ hcζ
    have hη1 : ‖η‖ = 1 := mem_sphere_zero_iff_norm.1 hη
    have hη0 : η ≠ 0 := norm_ne_zero_iff.1 (by rw [hη1]; exact one_ne_zero)
    have hEη : E η - x₀ ≠ 0 := sub_ne_zero.2 fun h => hη0 (E.injective h)
    have hψ0 : ψ (conj ζ) ≠ 0 := by rw [← hψη]; exact inv_ne_zero hEη
    have hx : x₀ + (ψ (conj ζ))⁻¹ = E η := by
      rw [← hψη]
      show x₀ + ((E η - x₀)⁻¹)⁻¹ = E η
      rw [inv_inv, add_sub_cancel]
    refine ⟨by rw [hx, hφs]; exact mem_image_of_mem E hη, ?_⟩
    -- `g u = x₀ + 1/ψ(1/u)` on `𝔻*`
    have hrep : ∀ u ∈ unitDiscExterior, g u = x₀ + (ψ u⁻¹)⁻¹ := fun u hu => by
      have hu1 : 1 < ‖u‖ := hu
      have hu0 : u ≠ 0 := norm_pos_iff.1 (one_pos.trans hu1)
      have huD : u⁻¹ ∈ unitDisc := by
        show u⁻¹ ∈ ball (0 : ℂ) 1
        rw [mem_ball_zero_iff, norm_inv]
        exact inv_lt_one_of_one_lt₀ hu1
      rw [hψf _ huD, s07_outerPt_conj (inv_ne_zero hu0), inv_inv]
      show g u = x₀ + ((g u - x₀)⁻¹)⁻¹
      rw [inv_inv, add_sub_cancel]
    have hinvT : Tendsto (fun u : ℂ => u⁻¹) (𝓝[unitDiscExterior] ζ)
        (𝓝[closedBall (0 : ℂ) 1] (conj ζ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun u hu => ?_⟩
      · have hζ0 : ζ ≠ 0 := norm_ne_zero_iff.1 (by rw [hζ1]; exact one_ne_zero)
        have := ((continuousAt_inv₀ hζ0).tendsto).mono_left
          (nhdsWithin_le_nhds (s := unitDiscExterior))
        rwa [hζinv] at this
      · have hu1 : 1 < ‖u‖ := hu
        rw [mem_closedBall_zero_iff, norm_inv]
        exact (inv_lt_one_of_one_lt₀ hu1).le
    have hψT := ((hψc _ (sphere_subset_closedBall hcζ)).tendsto.comp hinvT).inv₀ hψ0
    exact ((tendsto_const_nhds (x := x₀)).add hψT).congr'
      (eventually_nhdsWithin_of_forall fun u hu => (hrep u hu).symm)
  have hex : ∀ ζ ∈ sphere (0 : ℂ) 1, ∃ η ∈ sphere (0 : ℂ) 1, φ η = x₀ + (ψ (conj ζ))⁻¹ :=
    fun ζ hζ => (hgb ζ hζ).1
  choose! h hhS hhφ using hex
  have hw : IsDiskWelding Ω Ωs f g h := by
    refine ⟨hf, hg, hgInf, fun ζ hζ => hhS ζ hζ, fun ζ hζ => ⟨x₀ + (ψ (conj ζ))⁻¹, ?_, (hgb ζ hζ).2⟩⟩
    have hc := (hφc _ (sphere_subset_closedBall (hhS ζ hζ))).tendsto.mono_left
      (nhdsWithin_mono _ (ball_subset_closedBall (x := (0 : ℂ)) (ε := 1)))
    rw [hhφ ζ hζ] at hc
    exact hc.congr' (eventually_nhdsWithin_of_forall fun z hz => hφf z hz)
  obtain ⟨H, hH, hHs, hHb⟩ := s07_weld_admitsExt hΓ hw
  exact ⟨h, hw, s07_circleHomeo_of_qcExt hH hHs hHb⟩

/-- (7.10) `eq:welding-extension` (`sec07-transfer.tex:415`): the welding of a bounded
`K`-quasicircle admits a `K₀`-q.c. extension to `𝔻`, `K₀ = Q(K)²` depending only on `K`. -/
theorem eq_welding_extension (K : ℝ) (hK : 1 ≤ K) : ∃ K₀ : ℝ, 1 ≤ K₀ ∧
    ∀ Ω Ωs : Set ℂ, IsBoundedKQuasicircle Ω Ωs K → ∀ f g h : ℂ → ℂ,
      IsDiskWelding Ω Ωs f g h → AdmitsQCDiskExt h K₀ := by
  exact ⟨K * K, by nlinarith, fun Ω Ωs hΓ f g h hw => s07_weld_admitsExt hΓ hw⟩

/-- Lane U (B5 ⇐), helper: the unit circle is Lebesgue-null and meets every vertical and every
horizontal line in a countable set (at most two points), as `s13x_removable` requires. -/
theorem s07u_sphere_lines :
    volume (sphere (0 : ℂ) 1) = 0 ∧
      (∀ x : ℝ, {y : ℝ | (x : ℂ) + (y : ℂ) * I ∈ sphere (0 : ℂ) 1}.Countable) ∧
      ∀ y : ℝ, {x : ℝ | (x : ℂ) + (y : ℂ) * I ∈ sphere (0 : ℂ) 1}.Countable := by
  have key : ∀ x y : ℝ, (x : ℂ) + (y : ℂ) * I ∈ sphere (0 : ℂ) 1 → x ^ 2 + y ^ 2 = 1 := by
    intro x y h
    have h1 : ‖(x : ℂ) + (y : ℂ) * I‖ = 1 := mem_sphere_zero_iff_norm.1 h
    have h2 := Complex.sq_norm ((x : ℂ) + (y : ℂ) * I)
    rw [h1, Complex.normSq_add_mul_I] at h2
    linarith
  have fin2 : ∀ c : ℝ, {t : ℝ | t ^ 2 = c}.Countable := by
    intro c
    refine (Set.Finite.countable (Set.toFinite ({√c, -√c} : Set ℝ))).mono ?_
    intro t ht
    have ht' : t ^ 2 = c := ht
    have hc : 0 ≤ c := ht' ▸ sq_nonneg t
    have hsq : t ^ 2 = (√c) ^ 2 := by rw [Real.sq_sqrt hc]; exact ht'
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨Measure.addHaar_sphere volume 0 1, fun x => ?_, fun y => ?_⟩
  · refine (fin2 (1 - x ^ 2)).mono fun y hy => ?_
    have := key x y hy
    show y ^ 2 = 1 - x ^ 2
    linarith
  · refine (fin2 (1 - y ^ 2)).mono fun x hx => ?_
    have := key x y hx
    show x ^ 2 = 1 - y ^ 2
    linarith

/-- Lane U (B5 ⇐), helper: a conformal post-composition does not change the complex dilatation.
If `g` is holomorphic and injective on the open set `V`, `E` is continuous on the open set `U`
with `E(U) ⊆ V`, and `Φ = g ∘ E` on `U`, then `μ_Φ = μ_E` at every point of `U` (also where `E` is
not differentiable: then neither is `Φ`, and both sides are `0`). -/
theorem s07u_dilat_comp {U V : Set ℂ} {g E Φ : ℂ → ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hgd : DifferentiableOn ℂ g V) (hgi : InjOn g V) (hEc : ContinuousOn E U)
    (hEV : MapsTo E U V) (hΦ : EqOn Φ (g ∘ E) U) {z : ℂ} (hz : z ∈ U) :
    complexDilatation Φ z = complexDilatation E z := by
  have hev : Φ =ᶠ[𝓝 z] g ∘ E := Filter.eventually_of_mem (hU.mem_nhds hz) hΦ
  have hfd : fderiv ℝ Φ z = fderiv ℝ (g ∘ E) z := hev.fderiv_eq
  have hEz : E z ∈ V := hEV hz
  have hgdz : DifferentiableAt ℂ g (E z) := hgd.differentiableAt (hV.mem_nhds hEz)
  have hg0 : deriv g (E z) ≠ 0 := deriv_ne_zero_of_injOn hV hgd hgi hEz
  by_cases hE : DifferentiableAt ℝ E z
  · have hc : fderiv ℝ (g ∘ E) z = (fderiv ℝ g (E z)).comp (fderiv ℝ E z) :=
      fderiv_comp z (hgdz.restrictScalars ℝ) hE
    have hgR : ∀ v, fderiv ℝ g (E z) v = deriv g (E z) * v := by
      intro v
      rw [(hgdz.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
      simp [mul_comm]
    have hdz : dz Φ z = deriv g (E z) * dz E z := by
      simp only [dz, hfd, hc, ContinuousLinearMap.comp_apply, hgR]
      ring
    have hdzb : dzbar Φ z = deriv g (E z) * dzbar E z := by
      simp only [dzbar, hfd, hc, ContinuousLinearMap.comp_apply, hgR]
      ring
    show dzbar Φ z / dz Φ z = dzbar E z / dz E z
    rw [hdz, hdzb]
    exact mul_div_mul_left _ _ hg0
  · have hΦ' : ¬ DifferentiableAt ℝ Φ z := by
      intro hΦd
      have hs : HasStrictDerivAt g (deriv g (E z)) (E z) :=
        (hgd.analyticAt (hV.mem_nhds hEz)).hasStrictDerivAt
      have hinv : HasStrictDerivAt (hs.localInverse g (deriv g (E z)) (E z) hg0)
          (deriv g (E z))⁻¹ (g (E z)) := hs.to_localInverse hg0
      have hleft := hs.eventually_left_inverse hg0
      have hEcz : ContinuousAt E z := hEc.continuousAt (hU.mem_nhds hz)
      have hev2 : (hs.localInverse g (deriv g (E z)) (E z) hg0) ∘ Φ =ᶠ[𝓝 z] E := by
        filter_upwards [hev, Filter.Tendsto.eventually hEcz hleft] with x hx1 hx2
        rw [Function.comp_apply, hx1]
        exact hx2
      have h1 : DifferentiableAt ℂ (hs.localInverse g (deriv g (E z)) (E z) hg0) (Φ z) := by
        have hΦz : Φ z = g (E z) := hΦ hz
        rw [hΦz]
        exact HasDerivAt.differentiableAt (HasStrictDerivAt.hasDerivAt hinv)
      exact hE (((h1.restrictScalars ℝ).comp z hΦd).congr_of_eventuallyEq hev2.symm)
    simp only [complexDilatation, dz, dzbar, fderiv_zero_of_not_differentiableAt hE,
      fderiv_zero_of_not_differentiableAt hΦ', ContinuousLinearMap.zero_apply]

/-- Lane U (B5 ⇐), gluing: let `h` be the welding of a bounded quasicircle (`f : 𝔻 → Ω`,
`g : 𝔻* → Ωs`) and an orientation-preserving circle homeomorphism, and let `E` be a homeomorphism
of `𝔻*` onto itself, `K₁`-q.c., with `E(z) → ∞` as `z → ∞` and boundary values `h⁻¹`
(`E(z) → ζ` as `z → h(ζ)` in `𝔻*`).  Then `f` on `𝔻̄` (Carathéodory, `s07_carath_core`) and
`g ∘ E` on `𝔻*` glue to a homeomorphism of `ℂ`. -/
theorem s07u_glue_homeo {Ω Ωs : Set ℂ} {K K₁ : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K)
    {f g h E : ℂ → ℂ} (hw : IsDiskWelding Ω Ωs f g h) (hh : IsCircleHomeo h)
    (hE : IsKQC E unitDiscExterior K₁) (hEs : E '' unitDiscExterior = unitDiscExterior)
    (hEinf : Tendsto E (cocompact ℂ) (cocompact ℂ))
    (hEb : ∀ ζ ∈ sphere (0 : ℂ) 1, Tendsto E (𝓝[unitDiscExterior] (h ζ)) (𝓝 ζ)) :
    ∃ e : ℂ ≃ₜ ℂ, (∀ z ∈ unitDisc, e z = f z) ∧ ∀ z ∈ unitDiscExterior, e z = g (E z) := by
  obtain ⟨F, hFq, hFs, hF1, hF2⟩ := id hq
  obtain ⟨T, rfl⟩ := t1_homeomorph hFq hFs
  obtain ⟨hf, hg, hgInf, -, hwb⟩ := hw
  obtain ⟨φ, hφc, hφi, hφf, hφs⟩ :=
    s07_carath_core T.continuous.continuousOn T.injective.injOn hF1 hf
  obtain ⟨-, -, ⟨hEc, hEi, -, -⟩, -⟩ := hE
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hEm : ∀ z ∈ unitDiscExterior, E z ∈ unitDiscExterior := fun z hz =>
    hEs ▸ mem_image_of_mem E hz
  have hgc : ContinuousOn g unitDiscExterior := hg.1.continuousOn
  -- `h` maps `∂𝔻` onto `∂𝔻`
  have hsurj : ∀ ξ ∈ sphere (0 : ℂ) 1, ∃ ζ ∈ sphere (0 : ℂ) 1, h ζ = ξ := by
    obtain ⟨ψ, hψb, -, -, hψv⟩ := s07_de_circleMap hh
    intro ξ hξ
    have hξ' : ξ ∈ Submonoid.unitSphere ℂ := hξ
    obtain ⟨ζ, hζ⟩ := hψb.2 ⟨ξ, hξ'⟩
    refine ⟨ζ, (show (ζ : ℂ) ∈ sphere (0 : ℂ) 1 from ζ.2), ?_⟩
    rw [← hψv ζ, hζ]
  have hneb : ∀ ξ ∈ sphere (0 : ℂ) 1, (𝓝[unitDisc] ξ).NeBot := by
    intro ξ hξ
    apply mem_closure_iff_nhdsWithin_neBot.1
    show ξ ∈ closure (ball (0 : ℂ) 1)
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact sphere_subset_closedBall hξ
  -- the boundary values of `f` are those of `φ`
  have hfφ : ∀ ξ ∈ sphere (0 : ℂ) 1, Tendsto f (𝓝[unitDisc] ξ) (𝓝 (φ ξ)) := by
    intro ξ hξ
    have h1 : Tendsto φ (𝓝[unitDisc] ξ) (𝓝 (φ ξ)) :=
      (hφc ξ (sphere_subset_closedBall hξ)).mono ball_subset_closedBall
    exact h1.congr' (eventually_nhdsWithin_of_forall fun z hz => hφf z hz)
  -- from outside, `g ∘ E` tends to the same boundary values
  have hout : ∀ ξ ∈ sphere (0 : ℂ) 1,
      Tendsto (fun z => g (E z)) (𝓝[unitDiscExterior] ξ) (𝓝 (φ ξ)) := by
    intro ξ hξ
    obtain ⟨ζ, hζ, rfl⟩ := hsurj ξ hξ
    obtain ⟨x, hfx, hgx⟩ := hwb ζ hζ
    have := hneb (h ζ) hξ
    have hx : x = φ (h ζ) := tendsto_nhds_unique hfx (hfφ _ hξ)
    have hEt : Tendsto E (𝓝[unitDiscExterior] (h ζ)) (𝓝[unitDiscExterior] ζ) :=
      tendsto_nhdsWithin_iff.2 ⟨hEb ζ hζ, eventually_nhdsWithin_of_forall hEm⟩
    rw [← hx]
    exact hgx.comp hEt
  -- the glued map
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℂ → ℂ, Φ = fun z => if ‖z‖ ≤ 1 then φ z else g (E z) := ⟨_, rfl⟩
  have hΦin : ∀ z, ‖z‖ ≤ 1 → Φ z = φ z := fun z hz => by
    rw [hΦdef]
    exact if_pos hz
  have hΦout : ∀ z ∈ unitDiscExterior, Φ z = g (E z) := fun z hz => by
    rw [hΦdef]
    exact if_neg (not_le.2 hz)
  -- continuity
  have hcont : Continuous Φ := by
    refine continuous_iff_continuousAt.2 fun z => ?_
    rcases lt_trichotomy ‖z‖ 1 with hz | hz | hz
    · have hzb : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.2 hz
      have hev : φ =ᶠ[𝓝 z] Φ := by
        filter_upwards [isOpen_ball.mem_nhds hzb] with w hw
        exact (hΦin w (mem_ball_zero_iff.1 hw).le).symm
      exact (hφc.continuousAt (mem_of_superset (isOpen_ball.mem_nhds hzb)
        ball_subset_closedBall)).congr hev
    · have hzs : z ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.2 hz
      have hΦz : Φ z = φ z := hΦin z hz.le
      have h1 : ContinuousWithinAt Φ (closedBall (0 : ℂ) 1) z :=
        (hφc z (sphere_subset_closedBall hzs)).congr
          (fun w hw => hΦin w (mem_closedBall_zero_iff.1 hw)) hΦz
      have h2 : ContinuousWithinAt Φ unitDiscExterior z := by
        show Tendsto Φ (𝓝[unitDiscExterior] z) (𝓝 (Φ z))
        rw [hΦz]
        exact (hout z hzs).congr' (eventually_nhdsWithin_of_forall fun w hw => (hΦout w hw).symm)
      have hU : closedBall (0 : ℂ) 1 ∪ unitDiscExterior = univ := by
        ext w
        simp only [mem_union, mem_closedBall_zero_iff, mem_univ, iff_true]
        rcases le_or_gt ‖w‖ 1 with hw | hw
        · exact Or.inl hw
        · exact Or.inr hw
      have h3 := h1.union h2
      rwa [hU, continuousWithinAt_univ] at h3
    · have hzE : z ∈ unitDiscExterior := hz
      have hev : (fun w => g (E w)) =ᶠ[𝓝 z] Φ := by
        filter_upwards [hEo.mem_nhds hzE] with w hw
        exact (hΦout w hw).symm
      have hc1 : ContinuousAt E z := hEc.continuousAt (hEo.mem_nhds hzE)
      have hc2 : ContinuousAt g (E z) := hgc.continuousAt (hEo.mem_nhds (hEm z hzE))
      exact (hc2.comp hc1).congr hev
  -- images
  have hφimg : ∀ z, ‖z‖ ≤ 1 → ∃ u : ℂ, ‖u‖ ≤ 1 ∧ φ z = T u := by
    intro z hz
    rcases hz.lt_or_eq with hz | hz
    · have hzD : z ∈ unitDisc := mem_ball_zero_iff.2 hz
      have hm : φ z ∈ T '' unitDisc := by
        rw [hF1, ← hf.2.2, hφf z hzD]
        exact mem_image_of_mem f hzD
      obtain ⟨u, hu, hu'⟩ := hm
      exact ⟨u, (mem_ball_zero_iff.1 hu).le, hu'.symm⟩
    · have hm : φ z ∈ T '' sphere (0 : ℂ) 1 :=
        hφs ▸ mem_image_of_mem φ (mem_sphere_zero_iff_norm.2 hz)
      obtain ⟨u, hu, hu'⟩ := hm
      exact ⟨u, (mem_sphere_zero_iff_norm.1 hu).le, hu'.symm⟩
  have hgimg : ∀ z ∈ unitDiscExterior, ∃ u : ℂ, 1 < ‖u‖ ∧ g (E z) = T u := by
    intro z hz
    have hm : g (E z) ∈ T '' unitDiscExterior := by
      rw [hF2, ← hg.2.2]
      exact mem_image_of_mem g (hEm z hz)
    obtain ⟨u, hu, hu'⟩ := hm
    exact ⟨u, hu, hu'.symm⟩
  -- injectivity
  have hinj : Function.Injective Φ := by
    intro a b hab
    rcases le_or_gt ‖a‖ 1 with ha | ha <;> rcases le_or_gt ‖b‖ 1 with hb | hb
    · rw [hΦin a ha, hΦin b hb] at hab
      exact hφi (mem_closedBall_zero_iff.2 ha) (mem_closedBall_zero_iff.2 hb) hab
    · exfalso
      rw [hΦin a ha, hΦout b hb] at hab
      obtain ⟨u, hu, hu'⟩ := hφimg a ha
      obtain ⟨v, hv, hv'⟩ := hgimg b hb
      rw [hu', hv'] at hab
      rw [T.injective hab] at hu
      exact absurd hv (not_lt.2 hu)
    · exfalso
      rw [hΦout a ha, hΦin b hb] at hab
      obtain ⟨u, hu, hu'⟩ := hgimg a ha
      obtain ⟨v, hv, hv'⟩ := hφimg b hb
      rw [hu', hv'] at hab
      rw [T.injective hab] at hu
      exact absurd hu (not_lt.2 hv)
    · rw [hΦout a ha, hΦout b hb] at hab
      exact hEi ha hb (hg.2.1 (hEm a ha) (hEm b hb) hab)
  -- surjectivity
  have hsurjΦ : Function.Surjective Φ := by
    intro w
    obtain ⟨u, rfl⟩ := T.surjective w
    rcases le_or_gt ‖u‖ 1 with hu | hu
    · rcases hu.lt_or_eq with hu | hu
      · have hm : T u ∈ f '' unitDisc := by
          rw [hf.2.2, ← hF1]
          exact mem_image_of_mem T (mem_ball_zero_iff.2 hu)
        obtain ⟨z, hz, hz'⟩ := hm
        exact ⟨z, by rw [hΦin z (mem_ball_zero_iff.1 hz).le, hφf z hz, hz']⟩
      · have hm : T u ∈ φ '' sphere (0 : ℂ) 1 := by
          rw [hφs]
          exact mem_image_of_mem T (mem_sphere_zero_iff_norm.2 hu)
        obtain ⟨z, hz, hz'⟩ := hm
        exact ⟨z, by rw [hΦin z (mem_sphere_zero_iff_norm.1 hz).le, hz']⟩
    · have hm : T u ∈ g '' unitDiscExterior := by
        rw [hg.2.2, ← hF2]
        exact mem_image_of_mem T hu
      obtain ⟨y, hy, hy'⟩ := hm
      rw [← hEs] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact ⟨z, by rw [hΦout z hz, hy']⟩
  -- properness
  have hprop : Tendsto Φ (cocompact ℂ) (cocompact ℂ) := by
    have hev0 : ∀ᶠ z in cocompact ℂ, z ∈ unitDiscExterior := by
      filter_upwards [(isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact] with z hz
      exact not_le.1 fun h => hz (mem_closedBall_zero_iff.2 h)
    have hev : (fun z => g (E z)) =ᶠ[cocompact ℂ] Φ := by
      filter_upwards [hev0] with z hz
      exact (hΦout z hz).symm
    exact (hgInf.comp hEinf).congr' hev
  have hclosed : IsClosedMap Φ :=
    (isProperMap_iff_tendsto_cocompact.2 ⟨hcont, hprop⟩).isClosedMap
  have hH : IsHomeomorph Φ :=
    isHomeomorph_iff_continuous_isClosedMap_bijective.2 ⟨hcont, hclosed, hinj, hsurjΦ⟩
  refine ⟨IsHomeomorph.homeomorph Φ hH, fun z hz => ?_, fun z hz => ?_⟩
  · show Φ z = f z
    rw [hΦin z (mem_ball_zero_iff.1 hz).le, hφf z hz]
  · exact hΦout z hz

/-- Lane U (B5 ⇐), welding gluing (SCOPE_w4_B5V5 §2 piece U): under the hypotheses of
`s07u_glue_homeo`, the glued map `Φ` (`= f` on `𝔻`, `= g ∘ E` on `𝔻*`) is a `K₁`-q.c. map of `ℂ`
onto `ℂ` (the circle `∂𝔻` is removable, `s13x_removable`), conformal on `𝔻`, with complex
dilatation `0` on `𝔻` and `μ_Φ = μ_E` on `𝔻*`.  With `E` an extension of `h⁻¹` whose dilatation is
Carleson on `𝔻*`, this is the hypothesis (B1) of the Astala–Zinsmeister step for `f`. -/
theorem s07u_glue {Ω Ωs : Set ℂ} {K K₁ : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K)
    {f g h E : ℂ → ℂ} (hw : IsDiskWelding Ω Ωs f g h) (hh : IsCircleHomeo h)
    (hE : IsKQC E unitDiscExterior K₁) (hEs : E '' unitDiscExterior = unitDiscExterior)
    (hEinf : Tendsto E (cocompact ℂ) (cocompact ℂ))
    (hEb : ∀ ζ ∈ sphere (0 : ℂ) 1, Tendsto E (𝓝[unitDiscExterior] (h ζ)) (𝓝 ζ)) :
    ∃ Φ : ℂ → ℂ, IsKQC Φ univ K₁ ∧ Φ '' univ = univ ∧ (∀ z ∈ unitDisc, Φ z = f z) ∧
      (∀ z ∈ unitDiscExterior, Φ z = g (E z)) ∧ (∀ z ∈ unitDisc, complexDilatation Φ z = 0) ∧
      ∀ z ∈ unitDiscExterior, complexDilatation Φ z = complexDilatation E z := by
  obtain ⟨e, he1, he2⟩ := s07u_glue_homeo hq hw hh hE hEs hEinf hEb
  -- `1 ≤ K₁` is part of `IsKQC` (second conjunct), so the conformal side is `K₁`-q.c. too
  have hK1 : 1 ≤ K₁ := hE.2.1
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hDo : IsOpen unitDisc := isOpen_ball
  have hEm : MapsTo E unitDiscExterior unitDiscExterior := fun z hz =>
    hEs ▸ mem_image_of_mem E hz
  obtain ⟨hL0, hLv, hLh⟩ := s07u_sphere_lines
  have hhom : IsHomeomorphOnto (⇑e) univ (⇑e '' univ) := by
    refine ⟨e.continuous.continuousOn, e.injective.injOn, rfl, ?_⟩
    have hinv : Function.invFunOn (⇑e) univ = ⇑e.symm := by
      funext w
      apply e.injective
      rw [Function.invFunOn_eq ⟨e.symm w, mem_univ _, e.apply_symm_apply w⟩, e.apply_symm_apply]
    rw [hinv]
    exact e.symm.continuous.continuousOn
  have hQC : IsKQC (⇑e) univ K₁ := by
    refine s13x_removable isOpen_univ hK1 hhom hL0 (Eventually.of_forall hLv)
      (Eventually.of_forall hLh) fun z hz => ?_
    have hz1 : ‖z‖ ≠ 1 := fun h1 => hz.2 (mem_sphere_zero_iff_norm.2 h1)
    rcases lt_or_gt_of_ne hz1 with h1 | h1
    · exact ⟨unitDisc, hDo, mem_ball_zero_iff.2 h1, subset_univ _,
        ad_isKQC_congr ((isKQC_one_of_conformal hDo hw.1).mono hK1) he1⟩
    · have hc := thm7_1_comp hE (isKQC_one_of_conformal hEo hw.2.1) hEs.subset
      rw [mul_one] at hc
      exact ⟨unitDiscExterior, hEo, h1, subset_univ _, ad_isKQC_congr hc he2⟩
  refine ⟨e, hQC, image_univ.trans e.surjective.range_eq, he1, he2, fun z hz => ?_,
    fun z hz => s07u_dilat_comp hEo hEo hw.2.1.1 hw.2.1.2.1 hE.2.2.1.1 hEm he2 hz⟩
  -- on `𝔻`, `e = f ∘ id` with `f` conformal, so `μ_e = μ_id = 0`
  rw [s07u_dilat_comp hDo hDo hw.1.1 hw.1.2.1 continuousOn_id (mapsTo_id _) he1 hz]
  simp [complexDilatation, dz, dzbar, fderiv_id]

/-- The bounded curve `Γ` is a (round) circle. -/
def IsRoundCircle (Ω Ωs : Set ℂ) : Prop :=
  ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ curveOf Ω Ωs = sphere c r

/-- `m_f = (f⁻¹)_* m_Ω`, given by its density `¼ |Sf|² ϖ² dA` on `𝔻` ((2.6)
`eq:pullback-mass`). -/
def pullbackMass (f : ℂ → ℂ) : Measure ℂ :=
  (volume.restrict unitDisc).withDensity fun z =>
    ENNReal.ofReal (‖schwarzian f z‖ ^ 2 * varpi z ^ 2 / 4)

/-- `z ↦ 1/(f(z) - x₀)` is a conformal map of `𝔻` onto `invPairΩ Ω x₀` when `x₀ ∉ Ω`. -/
theorem s07_invAt_conformal {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {x₀ : ℂ} (hx₀ : x₀ ∉ Ω) :
    IsConformalOnto (fun z => invAt x₀ (f z)) unitDisc (invPairΩ Ω x₀) := by
  have hne : ∀ z ∈ unitDisc, f z - x₀ ≠ 0 := by
    intro z hz h
    apply hx₀
    rw [← sub_eq_zero.mp h, ← hf.2.2]
    exact mem_image_of_mem f hz
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact ((hf.1 z hz).sub_const x₀).inv (hne z hz)
  · intro z hz z' hz' h
    simp only [invAt, inv_inj, sub_left_inj] at h
    exact hf.2.1 hz hz' h
  · rw [invPairΩ, ← hf.2.2, image_image]

/-- A conformal map of `𝔻` has a Borel left inverse (Lusin–Souslin). -/
theorem s07_measurable_leftInv {F : ℂ → ℂ} (hFc : ContinuousOn F unitDisc)
    (hFi : InjOn F unitDisc) : ∃ G : ℂ → ℂ, Measurable G ∧ ∀ z ∈ unitDisc, G (F z) = z := by
  classical
  have hD : MeasurableSet unitDisc := measurableSet_ball
  set G : ℂ → ℂ := (F '' unitDisc).piecewise (Function.invFunOn F unitDisc) 0 with hGdef
  have hinv : ∀ z ∈ unitDisc, Function.invFunOn F unitDisc (F z) = z :=
    fun z hz => hFi.leftInvOn_invFunOn hz
  refine ⟨G, ?_, fun z hz => ?_⟩
  · intro B hB
    have hset : G ⁻¹' B = F '' (B ∩ unitDisc) ∪ ((fun _ : ℂ => (0 : ℂ)) ⁻¹' B \ F '' unitDisc) := by
      ext w
      by_cases hw : w ∈ F '' unitDisc
      · obtain ⟨z, hz, rfl⟩ := hw
        have hGz : G (F z) = z := by
          simp only [hGdef, piecewise_eq_of_mem _ _ _ (mem_image_of_mem F hz), hinv z hz]
        constructor
        · intro hzB
          left
          rw [mem_preimage, hGz] at hzB
          exact ⟨z, ⟨hzB, hz⟩, rfl⟩
        · rintro (⟨z', ⟨hz'B, hz'⟩, hzz'⟩ | ⟨-, hn⟩)
          · rw [mem_preimage, hGz, ← hFi hz' hz hzz']
            exact hz'B
          · exact absurd (mem_image_of_mem F hz) hn
      · have hGw : G w = 0 := by
          simp only [hGdef, piecewise_eq_of_notMem _ _ _ hw, Pi.zero_apply]
        constructor
        · intro hwB
          right
          rw [mem_preimage, hGw] at hwB
          exact ⟨hwB, hw⟩
        · rintro (⟨z, ⟨-, hz⟩, rfl⟩ | ⟨h0, -⟩)
          · exact absurd (mem_image_of_mem F hz) hw
          · rw [mem_preimage, hGw]
            exact h0
    rw [hset]
    exact ((hB.inter hD).image_of_continuousOn_injOn (hFc.mono inter_subset_right)
      (hFi.mono inter_subset_right)).union
      ((measurable_const hB).diff (hD.image_of_continuousOn_injOn hFc hFi))
  · simp only [hGdef, piecewise_eq_of_mem _ _ _ (mem_image_of_mem F hz), hinv z hz]

/-- The Schwarzian is unchanged by the inversion `invAt x₀`. -/
theorem s07_schwarzian_invAt {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {x₀ : ℂ} (hx₀ : x₀ ∉ Ω) {z : ℂ} (hz : z ∈ unitDisc) :
    schwarzian (fun w => invAt x₀ (f w)) z = schwarzian f z := by
  have hA : AnalyticAt ℂ f z := hf.1.analyticAt (isOpen_ball.mem_nhds hz)
  have hd : deriv f z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz
  have hfz : f z ∈ Ω := hf.2.2 ▸ mem_image_of_mem f hz
  have hden : (1 : ℂ) * f z + -x₀ ≠ 0 := by
    intro h
    apply hx₀
    rw [one_mul, add_neg_eq_zero] at h
    rw [← h]
    exact hfz
  have hfun : (fun w => invAt x₀ (f w)) = fun w => (0 * f w + 1) / (1 * f w + -x₀) := by
    funext w
    simp [invAt, sub_eq_add_neg]
  rw [hfun]
  exact schwarzian_mobius_comp_of_ne hA hd (by norm_num) hden

/-- Lemma 7.9, `lem:one-sided` (`sec07-transfer.tex:419`): `K_H(f(a)) = 𝒫_{m_f}(a)` (the
horoball quantities of the bounded curve read through `invAt x₀`, `x₀ ∈ Γ`). -/
theorem lem_one_sided (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    (f : ℂ → ℂ) (hf : IsConformalOnto f unitDisc Ω) (x₀ : ℂ) (hx₀ : x₀ ∈ curveOf Ω Ωs)
    (a : ℂ) (ha : a ∈ unitDisc) :
    KH (invPairΩ Ω x₀) (invAt x₀ (f a)) = poissonP (pullbackMass f) a := by
  -- `hΓ` is not needed: the identity holds for every conformal `f` and every `x₀ ∉ Ω`.
  have _h := hΓ
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hx₀Ω : x₀ ∉ Ω := fun h => hx₀ (Or.inl h)
  set F : ℂ → ℂ := fun z => invAt x₀ (f z) with hFdef
  have hF : IsConformalOnto F unitDisc (invPairΩ Ω x₀) := s07_invAt_conformal hf hx₀Ω
  obtain ⟨G, hGm, hGF⟩ := s07_measurable_leftInv hF.1.continuousOn hF.2.1
  have hk : Measurable fun z => ENNReal.ofReal (diskKernel a z) := by
    unfold diskKernel varpi; fun_prop
  have hφm : Measurable fun w => ENNReal.ofReal (diskKernel a (G w)) := hk.comp hGm
  have hΩ'm : MeasurableSet (invPairΩ Ω x₀) := by
    rw [← hF.2.2]
    exact hD.image_of_continuousOn_injOn hF.1.continuousOn hF.2.1
  have hker : ∀ z ∈ unitDisc, intrKernel (invPairΩ Ω x₀) (F a) (F z) = diskKernel a z := by
    intro z hz
    rw [eq_kernel_disk hF ha hz]
    rfl
  have hae : ∀ᵐ w ∂curvMass (invPairΩ Ω x₀), w ∈ invPairΩ Ω x₀ :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩ'm)
  have h1 : KH (invPairΩ Ω x₀) (F a) =
      ∫⁻ w, ENNReal.ofReal (diskKernel a (G w)) ∂curvMass (invPairΩ Ω x₀) := by
    unfold KH
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with w hw
    rw [← hF.2.2] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    rw [hGF z hz, hker z hz]
  show KH (invPairΩ Ω x₀) (F a) = _
  rw [h1, eq_pullback_mass_a hF hφm]
  unfold poissonP pullbackMass
  rw [restrict_withDensity hD, Measure.restrict_restrict hD, inter_self]
  have hdm : AEMeasurable (fun z => ENNReal.ofReal (‖schwarzian f z‖ ^ 2 * varpi z ^ 2 / 4))
      (volume.restrict unitDisc) := by
    have hS := s02_pullback_measurable_schwarzianHol f
    refine (Measurable.aemeasurable (f := fun z =>
      ENNReal.ofReal (‖schwarzianHol f z‖ ^ 2 * varpi z ^ 2 / 4)) ?_).congr ?_
    · unfold varpi; fun_prop
    · filter_upwards [ae_restrict_mem hD] with z hz
      rw [schwarzian_of_analyticAt (hf.1.analyticAt (isOpen_ball.mem_nhds hz))]
  rw [lintegral_withDensity_eq_lintegral_mul₀ hdm hk.aemeasurable]
  refine setLIntegral_congr_fun hD (fun z hz => ?_)
  simp only [Pi.mul_apply]
  rw [hGF z hz]
  simp only [hFdef, s07_schwarzian_invAt hf hx₀Ω hz, varpi]
  rw [mul_comm]

/-- `(μ.withDensity f).withDensity g = μ.withDensity (f * g)` for an arbitrary density `f` and a
measurable finite density `g`. -/
theorem s07_lintegral_withDensity_of_measurable (μ : Measure ℂ) [SigmaFinite μ]
    (f g : ℂ → ℝ≥0∞) (hg : Measurable g) (hgt : ∀ x, g x ≠ ⊤) :
    ∫⁻ x, g x ∂μ.withDensity f = ∫⁻ x, (f * g) x ∂μ := by
  obtain ⟨f', hf'm, hf'le, hf'eq⟩ := exists_measurable_le_forall_setLIntegral_eq μ f
  have hwd : μ.withDensity f = μ.withDensity f' := by
    ext t ht
    rw [withDensity_apply _ ht, withDensity_apply _ ht, hf'eq t]
  rw [hwd, lintegral_withDensity_eq_lintegral_mul _ hf'm hg]
  refine le_antisymm (lintegral_mono fun x => mul_le_mul_left (hf'le x) _) ?_
  obtain ⟨F, hFm, hFle, hFeq⟩ := exists_measurable_le_lintegral_eq μ (f * g)
  rw [hFeq]
  have hψle : ∀ x, F x * (g x)⁻¹ ≤ f x := by
    intro x
    by_cases h0 : g x = 0
    · have : F x = 0 := by
        have := hFle x
        simp only [Pi.mul_apply, h0, mul_zero, nonpos_iff_eq_zero] at this
        exact this
      simp [this]
    · calc F x * (g x)⁻¹ ≤ f x * g x * (g x)⁻¹ := mul_le_mul_left (hFle x) _
        _ = f x := by rw [mul_assoc, ENNReal.mul_inv_cancel h0 (hgt x), mul_one]
  have hψae : (fun x => F x * (g x)⁻¹) ≤ᵐ[μ] f' := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (hFm.mul hg.inv) fun t _ _ => ?_
    rw [← hf'eq t]
    exact lintegral_mono hψle
  refine lintegral_mono_ae ?_
  filter_upwards [hψae] with x hx
  simp only [Pi.mul_apply]
  by_cases h0 : g x = 0
  · have := hFle x
    simp only [Pi.mul_apply, h0, mul_zero, nonpos_iff_eq_zero] at this
    simp [this]
  · calc F x = F x * (g x)⁻¹ * g x := by
          rw [mul_assoc, ENNReal.inv_mul_cancel h0 (hgt x), mul_one]
      _ ≤ f' x * g x := mul_le_mul_left hx _

/-- `(μ.withDensity f).withDensity g = μ.withDensity (f * g)` for an arbitrary `f` and a measurable
finite `g`. -/
theorem s07_withDensity_withDensity (μ : Measure ℂ) [SigmaFinite μ] (f g : ℂ → ℝ≥0∞)
    (hg : Measurable g) (hgt : ∀ x, g x ≠ ⊤) :
    (μ.withDensity f).withDensity g = μ.withDensity (f * g) := by
  ext s hs
  rw [withDensity_apply _ hs, withDensity_apply _ hs, restrict_withDensity hs]
  exact s07_lintegral_withDensity_of_measurable _ f g hg hgt

/-- Lemma 7.9, `lem:one-sided` (`sec07-transfer.tex:421`): `ϖ m_f = ¼ |Sf|² ϖ³ dA`. -/
theorem lem_one_sided_varpi (f : ℂ → ℂ) :
    varpiMeasure (pullbackMass f) = (4 : ℝ≥0∞)⁻¹ • schwarzCarlesonMeasure f := by
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hmv : Measurable fun z : ℂ => ENNReal.ofReal (varpi z) := by
    unfold varpi; fun_prop
  unfold varpiMeasure pullbackMass schwarzCarlesonMeasure
  rw [restrict_withDensity hD, Measure.restrict_restrict hD, inter_self,
    s07_withDensity_withDensity _ _ _ hmv (fun _ => ENNReal.ofReal_ne_top),
    ← withDensity_smul' (4 : ℝ≥0∞)⁻¹ _ (by simp)]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem hD] with z hz
  have hvz := s07_varpi_pos hz
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity),
    show (4 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (4⁻¹) by rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; simp,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  unfold varpi
  ring

/-- Carleson measures are unchanged by the factor `¼`. -/
theorem s07_carleson_smul (μ : Measure ℂ) :
    IsCarlesonDisk ((4 : ℝ≥0∞)⁻¹ • μ) ↔ IsCarlesonDisk μ := by
  have h4 : ∀ x : ℝ≥0∞, 4 * (4⁻¹ * x) = x := fun x => by
    rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  constructor
  · rintro ⟨C, hC, hCb⟩
    refine ⟨4 * C, ENNReal.mul_ne_top (by norm_num) hC, fun ζ hζ r hr0 hr2 => ?_⟩
    have := hCb ζ hζ r hr0 hr2
    rw [Measure.smul_apply, smul_eq_mul] at this
    calc μ (unitDisc ∩ ball ζ r) = 4 * (4⁻¹ * μ (unitDisc ∩ ball ζ r)) := (h4 _).symm
      _ ≤ 4 * (C * ENNReal.ofReal r) := mul_le_mul_right this _
      _ = 4 * C * ENNReal.ofReal r := (mul_assoc _ _ _).symm
  · rintro ⟨C, hC, hCb⟩
    refine ⟨C, hC, fun ζ hζ r hr0 hr2 => ?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    calc 4⁻¹ * μ (unitDisc ∩ ball ζ r) ≤ 1 * μ (unitDisc ∩ ball ζ r) :=
          mul_le_mul_left (by norm_num) _
      _ ≤ C * ENNReal.ofReal r := by rw [one_mul]; exact hCb ζ hζ r hr0 hr2

/-- Vanishing Carleson measures are unchanged by the factor `¼`. -/
theorem s07_vanishingCarleson_smul (μ : Measure ℂ) :
    IsVanishingCarlesonDisk ((4 : ℝ≥0∞)⁻¹ • μ) ↔ IsVanishingCarlesonDisk μ := by
  have h4 : ∀ x : ℝ≥0∞, 4 * (4⁻¹ * x) = x := fun x => by
    rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  constructor
  · rintro ⟨hC, hv⟩
    refine ⟨(s07_carleson_smul μ).mp hC, fun ε hε => ?_⟩
    obtain ⟨δ, hδ, hδb⟩ := hv (ε / 4) (by positivity)
    refine ⟨δ, hδ, fun ζ hζ r hr0 hrδ => ?_⟩
    have := hδb ζ hζ r hr0 hrδ
    rw [Measure.smul_apply, smul_eq_mul] at this
    calc μ (unitDisc ∩ ball ζ r) = 4 * (4⁻¹ * μ (unitDisc ∩ ball ζ r)) := (h4 _).symm
      _ ≤ 4 * ENNReal.ofReal (ε / 4 * r) := mul_le_mul_right this _
      _ = ENNReal.ofReal (ε * r) := by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
  · rintro ⟨hC, hv⟩
    refine ⟨(s07_carleson_smul μ).mpr hC, fun ε hε => ?_⟩
    obtain ⟨δ, hδ, hδb⟩ := hv ε hε
    refine ⟨δ, hδ, fun ζ hζ r hr0 hrδ => ?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    calc 4⁻¹ * μ (unitDisc ∩ ball ζ r) ≤ 1 * μ (unitDisc ∩ ball ζ r) :=
          mul_le_mul_left (by norm_num) _
      _ ≤ ENNReal.ofReal (ε * r) := by rw [one_mul]; exact hδb ζ hζ r hr0 hrδ

/-- `‖ν‖_CM < ∞` iff `ν` is a Carleson measure. -/
theorem s07_carlesonNorm_lt_top (μ : Measure ℂ) : carlesonNorm μ < ⊤ ↔ IsCarlesonDisk μ := by
  constructor
  · intro h
    exact ⟨carlesonNorm μ, h.ne, fun ζ hζ r hr0 hr2 => s07_le_carlesonNorm μ ζ hζ r hr0 hr2⟩
  · rintro ⟨C, hC, hCb⟩
    refine lt_of_le_of_lt ?_ hC.lt_top
    unfold carlesonNorm
    refine iSup₂_le fun ζ hζ => iSup₂_le fun r hr => ?_
    exact ENNReal.div_le_of_le_mul (hCb ζ hζ r hr.1 hr.2)

/-- Precomposing with a disk automorphism `z ↦ c b(z)` keeps `lim_{|a|↑1} F(a) = 0`. -/
theorem s07_dbv_comp (G : ℂ → ℝ≥0∞) {c b : ℂ} (hc : ‖c‖ = 1) (hb : ‖b‖ < 1)
    (h : DiskBoundaryVanishing G) : DiskBoundaryVanishing fun a => G (c * blaschke b a) := by
  intro ε hε
  obtain ⟨r', hr'1, hr'⟩ := h ε hε
  set s := max r' 0 with hs
  have hs0 : 0 ≤ s := le_max_right _ _
  have hs1 : s < 1 := max_lt hr'1 one_pos
  have hb0 : 0 < 1 - ‖b‖ := by linarith
  set δ := (1 - s ^ 2) * (1 - ‖b‖) ^ 2 with hδ
  have hδ0 : 0 < δ := by
    have : 0 < 1 - s ^ 2 := by nlinarith
    positivity
  have hδ1 : δ ≤ 1 := by
    have h1 : 1 - s ^ 2 ≤ 1 := by nlinarith
    have h2 : (1 - ‖b‖) ^ 2 ≤ 1 := by nlinarith [norm_nonneg b]
    calc δ ≤ 1 * 1 := mul_le_mul h1 h2 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  refine ⟨1 - δ / 2, by linarith, fun a ha1 ha2 => hr' _ ?_ ?_⟩
  · have hB := blaschke_mem_unitDisc hb ha2
    have hkey := normSq_blaschke_key b a
    have hden : 1 - conj b * a ≠ 0 := blaschke_den_ne_zero hb ha2
    have hden' : 1 - ‖b‖ ≤ ‖1 - conj b * a‖ := by
      have : ‖conj b * a‖ ≤ ‖b‖ := by
        rw [norm_mul, Complex.norm_conj]
        nlinarith [norm_nonneg b, norm_nonneg a]
      have := norm_sub_norm_le (1 : ℂ) (conj b * a)
      rw [norm_one] at this
      linarith
    have hBn : ‖blaschke b a‖ ^ 2 * ‖1 - conj b * a‖ ^ 2 = ‖a - b‖ ^ 2 := by
      unfold blaschke
      rw [norm_div, div_pow, div_mul_cancel₀ _ (by positivity)]
    have hid : (1 - ‖blaschke b a‖ ^ 2) * ‖1 - conj b * a‖ ^ 2 =
        (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) := by
      rw [sub_mul, one_mul, hBn]
      simp only [Complex.normSq_eq_norm_sq] at hkey
      linarith
    have hA : 1 - ‖a‖ ^ 2 < δ := by nlinarith [norm_nonneg a]
    have hlow : (1 - ‖blaschke b a‖ ^ 2) * (1 - ‖b‖) ^ 2 < (1 - s ^ 2) * (1 - ‖b‖) ^ 2 := by
      have hD2 : (1 - ‖b‖) ^ 2 ≤ ‖1 - conj b * a‖ ^ 2 := by
        exact pow_le_pow_left₀ hb0.le hden' 2
      have hB1 : 0 ≤ 1 - ‖blaschke b a‖ ^ 2 := by nlinarith [norm_nonneg (blaschke b a)]
      calc (1 - ‖blaschke b a‖ ^ 2) * (1 - ‖b‖) ^ 2
          ≤ (1 - ‖blaschke b a‖ ^ 2) * ‖1 - conj b * a‖ ^ 2 := mul_le_mul_of_nonneg_left hD2 hB1
        _ = (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) := hid
        _ ≤ (1 - ‖a‖ ^ 2) * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by nlinarith [norm_nonneg a])
            nlinarith [norm_nonneg b]
        _ < δ := by linarith
    have hsB : s ^ 2 < ‖blaschke b a‖ ^ 2 := by
      have := lt_of_mul_lt_mul_right hlow (by positivity)
      linarith
    rw [norm_mul, hc, one_mul]
    calc r' ≤ s := le_max_left _ _
      _ < ‖blaschke b a‖ := by
          nlinarith [norm_nonneg (blaschke b a)]
  · rw [norm_mul, hc, one_mul]
    exact blaschke_mem_unitDisc hb ha2

/-- A bounded quasicircle domain has a Riemann map. -/
theorem s07_exists_riemannMap {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K) :
    ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω := by
  obtain ⟨F, hFq, hFu, hFD, -⟩ := hΓ
  obtain ⟨-, -, ⟨hFc, hFi, -, hFic⟩, -⟩ := hFq
  have hbij : Function.Bijective F := by
    refine ⟨fun x y h => hFi (mem_univ x) (mem_univ y) h, fun w => ?_⟩
    have hw : w ∈ F '' univ := by rw [hFu]; exact mem_univ w
    obtain ⟨z, -, hz⟩ := hw
    exact ⟨z, hz⟩
  have hinv : (Equiv.ofBijective F hbij).symm = Function.invFunOn F univ := by
    funext w
    apply hbij.1
    rw [Equiv.ofBijective_apply_symm_apply F hbij w]
    exact (Function.invFunOn_eq ⟨_, mem_univ _, Equiv.ofBijective_apply_symm_apply F hbij w⟩).symm
  have hFic' : Continuous (Function.invFunOn F univ) := by
    rw [hFu] at hFic
    exact continuousOn_univ.mp hFic
  let e : ℂ ≃ₜ ℂ :=
    { toEquiv := Equiv.ofBijective F hbij
      continuous_toFun := continuousOn_univ.mp hFc
      continuous_invFun := by
        show Continuous (Equiv.ofBijective F hbij).symm
        rw [hinv]
        exact hFic' }
  subst hFD
  have : SimplyConnectedSpace ↥(F '' unitDisc) := t1_simplyConnected_image e
  have hH : IsHyperbolicSimplyConnected (F '' unitDisc) := by
    refine ⟨e.isOpenMap _ isOpen_ball, (isConnected_ball one_pos).image F
      (hFc.mono (subset_univ _)), this, fun h => ?_⟩
    have h1 : F 1 ∈ F '' unitDisc := h ▸ mem_univ _
    obtain ⟨z, hz, hz1⟩ := h1
    rw [hbij.1 hz1] at hz
    simp [unitDisc] at hz
  obtain ⟨φ, hφ⟩ := lehto_exists_conformal hH
  exact ⟨_, hφ.symm hH.1⟩

/-- Lemma 7.9 (i), `lem:one-sided` (`sec07-transfer.tex:423`): `sup_Ω K_H < ∞` iff `Γ` is a BMO
quasicircle. -/
theorem lem_one_sided_i (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    (x₀ : ℂ) (hx₀ : x₀ ∈ curveOf Ω Ωs) :
    (⨆ p ∈ Ω, KH (invPairΩ Ω x₀) (invAt x₀ p)) < ⊤ ↔ IsBMOQuasicircle Ω Ωs := by
  have hsup : ∀ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω →
      (⨆ p ∈ Ω, KH (invPairΩ Ω x₀) (invAt x₀ p)) = ⨆ a ∈ unitDisc, poissonP (pullbackMass f) a := by
    intro f hf
    apply le_antisymm
    · refine iSup₂_le fun p hp => ?_
      rw [← hf.2.2] at hp
      obtain ⟨a, ha, rfl⟩ := hp
      rw [lem_one_sided K Ω Ωs hΓ f hf x₀ hx₀ a ha]
      exact le_iSup₂ (f := fun a _ => poissonP (pullbackMass f) a) a ha
    · refine iSup₂_le fun a ha => ?_
      rw [← lem_one_sided K Ω Ωs hΓ f hf x₀ hx₀ a ha]
      exact le_iSup₂ (f := fun p _ => KH (invPairΩ Ω x₀) (invAt x₀ p)) (f a)
        (hf.2.2 ▸ mem_image_of_mem f ha)
  have hiff : ∀ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω →
      ((⨆ p ∈ Ω, KH (invPairΩ Ω x₀) (invAt x₀ p)) < ⊤ ↔ LogDerivBMOA f) := by
    intro f hf
    rw [hsup f hf, thm_shen_wei_B (Or.inl hΓ) hf, ← s07_carleson_smul,
      ← lem_one_sided_varpi, ← s07_carlesonNorm_lt_top]
    obtain ⟨hb1, hb2⟩ := lem_kernel_test_b (pullbackMass f)
    constructor
    · intro h
      exact lt_of_le_of_lt hb1 (ENNReal.mul_lt_top (by norm_num) h)
    · intro h
      exact lt_of_le_of_lt hb2 (ENNReal.mul_lt_top (by norm_num) h)
  constructor
  · intro h
    obtain ⟨f, hf⟩ := s07_exists_riemannMap hΓ
    exact ⟨⟨K, hΓ⟩, f, hf, (hiff f hf).mp h⟩
  · rintro ⟨-, f, hf, hB⟩
    exact (hiff f hf).mpr hB

/-- Lemma 7.9 (ii), `lem:one-sided` (`sec07-transfer.tex:425`):
`lim_{r↑1} sup_{r<|a|<1} K_H(f(a)) = 0` iff `Γ` is a VMO quasicircle. -/
theorem lem_one_sided_ii (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    (f : ℂ → ℂ) (hf : IsConformalOnto f unitDisc Ω) (x₀ : ℂ) (hx₀ : x₀ ∈ curveOf Ω Ωs) :
    DiskBoundaryVanishing (fun a => KH (invPairΩ Ω x₀) (invAt x₀ (f a))) ↔
      IsVMOQuasicircle Ω Ωs := by
  have hiff : ∀ g : ℂ → ℂ, IsConformalOnto g unitDisc Ω →
      (DiskBoundaryVanishing (fun a => KH (invPairΩ Ω x₀) (invAt x₀ (g a))) ↔
        LogDerivVMOA g) := by
    intro g hg
    have hcongr : DiskBoundaryVanishing (fun a => KH (invPairΩ Ω x₀) (invAt x₀ (g a))) ↔
        DiskBoundaryVanishing (poissonP (pullbackMass g)) := by
      have heq : ∀ a : ℂ, ‖a‖ < 1 →
          KH (invPairΩ Ω x₀) (invAt x₀ (g a)) = poissonP (pullbackMass g) a := fun a ha =>
        lem_one_sided K Ω Ωs hΓ g hg x₀ hx₀ a (mem_ball_zero_iff.mpr ha)
      constructor
      · intro h ε hε
        obtain ⟨r, hr, hra⟩ := h ε hε
        refine ⟨r, hr, fun a h1 h2 => ?_⟩
        rw [← heq a h2]
        exact hra a h1 h2
      · intro h ε hε
        obtain ⟨r, hr, hra⟩ := h ε hε
        refine ⟨r, hr, fun a h1 h2 => ?_⟩
        show KH (invPairΩ Ω x₀) (invAt x₀ (g a)) ≤ ε
        rw [heq a h2]
        exact hra a h1 h2
    rw [hcongr, ← lem_kernel_test_c, lem_one_sided_varpi,
      s07_vanishingCarleson_smul, thm_shen_wei_V hΓ hg]
  constructor
  · intro h
    exact ⟨⟨K, hΓ⟩, f, hf, (hiff f hf).mp h⟩
  · rintro ⟨-, g, hg, hV⟩
    have h' := (hiff g hg).mpr hV
    obtain ⟨c, b, hc, hb, hfac⟩ := s02_riemannMap_factor hg hf
    have hcomp := s07_dbv_comp _ hc hb h'
    intro ε hε
    obtain ⟨r, hr, hra⟩ := hcomp ε hε
    refine ⟨r, hr, fun a h1 h2 => ?_⟩
    show KH (invPairΩ Ω x₀) (invAt x₀ (f a)) ≤ ε
    rw [(hfac a (mem_ball_zero_iff.mpr h2)).2]
    exact hra a h1 h2

/-- `m^* = ((g ∘ j)⁻¹)_* m_{Ω*}`, given by its density `¼ |S(g ∘ I)(z̄)|² ϖ² dA` on `𝔻`, `I(z) =
1/z` (`sec07-transfer.tex:522`). -/
def farMass (g : ℂ → ℂ) : Measure ℂ :=
  (volume.restrict unitDisc).withDensity fun z =>
    ENNReal.ofReal (‖schwarzian (fun u => g u⁻¹) (conj z)‖ ^ 2 * varpi z ^ 2 / 4)

/-- `A = f⁻¹ ∘ R ∘ g ∘ j` on `𝔻` (`sec07-transfer.tex:449`), `R = lab ∘ X*` the label map, all
read through `invAt x₀`. -/
def IsFarSideMap (Ω Ωs : Set ℂ) (f g : ℂ → ℂ) (x₀ : ℂ) (lab : ℂ × ℝ → ℂ) (A : ℂ → ℂ) :
    Prop :=
  ∀ z ∈ unitDisc, A z ∈ unitDisc ∧
    invAt x₀ (f (A z)) = lab (epstein (invPairΩs Ωs x₀) (outerPt g x₀ z))

/-- (0′) of Proposition 7.10 (a): if the bounded curve `Γ` is not a round circle, the transported
pair is not a line pair (a line not through `0 ∈ Ω*′` pulls back under `invAt x₀` to a circle
through `x₀`). -/
theorem s07_invPair_not_linePair {Ω Ωs : Set ℂ} {x₀ : ℂ} (hx₀ : x₀ ∈ curveOf Ω Ωs)
    (hnr : ¬ IsRoundCircle Ω Ωs) : ¬ IsLinePair (invPairΩ Ω x₀) (invPairΩs Ωs x₀) := by
  rintro ⟨a, b, ha, hΩ', hΩs'⟩
  apply hnr
  have hx : x₀ ∉ Ω ∧ x₀ ∉ Ωs := by
    simpa only [curveOf, mem_compl_iff, mem_union, not_or] using hx₀
  have hb : b.im < 0 := by
    have h0 : (0 : ℂ) ∈ invPairΩs Ωs x₀ := mem_union_right _ (mem_singleton 0)
    rw [hΩs'] at h0
    simpa using h0
  have hb0 : b.im ≠ 0 := hb.ne
  -- `y ≠ x₀` lies on `Γ` iff `invAt x₀ y` lies on the line
  have hchar : ∀ y : ℂ, y ≠ x₀ → (y ∈ curveOf Ω Ωs ↔ (a * invAt x₀ y + b).im = 0) := by
    intro y hy
    have h1 : invAt x₀ y ∈ invPairΩ Ω x₀ ↔ y ∈ Ω := by
      constructor
      · rintro ⟨y', hy', he⟩
        have : y' = y := sub_left_injective (inv_injective he)
        exact this ▸ hy'
      · exact fun h => mem_image_of_mem _ h
    have h2 : invAt x₀ y ∈ invPairΩs Ωs x₀ ↔ y ∈ Ωs := by
      constructor
      · rintro (⟨y', hy', he⟩ | h0)
        · have : y' = y := sub_left_injective (inv_injective he)
          exact this ▸ hy'
        · have h0' : (y - x₀)⁻¹ = 0 := h0
          rw [inv_eq_zero, sub_eq_zero] at h0'
          exact absurd h0' hy
      · exact fun h => mem_union_left _ (mem_image_of_mem _ h)
    rw [hΩ'] at h1
    rw [hΩs'] at h2
    simp only [mem_ofPred_eq] at h1 h2
    simp only [curveOf, mem_compl_iff, mem_union, not_or, ← h1, ← h2]
    constructor
    · rintro ⟨p, q⟩
      exact le_antisymm (not_lt.1 p) (not_lt.1 q)
    · intro h
      rw [h]
      exact ⟨lt_irrefl 0, lt_irrefl 0⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ⟨-a.im / (2 * b.im), a.re / (2 * b.im)⟩ := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by
    intro h
    apply ha
    rw [hc] at h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp only [zero_re, zero_im, div_eq_zero_iff, neg_eq_zero, mul_eq_zero, two_ne_zero,
      hb0, or_false, false_or] at h1 h2
    exact Complex.ext h2 h1
  refine ⟨x₀ + c, ‖c‖, norm_pos_iff.mpr hc0, ?_⟩
  ext y
  rw [mem_sphere, dist_eq_norm]
  by_cases hy : y = x₀
  · subst hy
    simp only [hx₀, true_iff, sub_add_cancel_left, norm_neg]
  rw [hchar y hy, show y - (x₀ + c) = (y - x₀) - c by ring]
  set v := y - x₀ with hv
  have hv0 : v ≠ 0 := sub_ne_zero.mpr hy
  have hN : normSq v ≠ 0 := (normSq_pos.mpr hv0).ne'
  have e1 : (a * v⁻¹ + b).im * normSq v = a.im * v.re - a.re * v.im + b.im * normSq v := by
    rw [add_im, mul_im, inv_re, inv_im]
    field_simp
    ring
  have e2 : (normSq (v - c) - normSq c) * b.im = a.im * v.re - a.re * v.im + b.im * normSq v := by
    rw [hc]
    simp only [normSq_apply, sub_re, sub_im]
    field_simp
    ring
  rw [← pow_left_inj₀ (norm_nonneg (v - c)) (norm_nonneg c) two_ne_zero, ← normSq_eq_norm_sq,
    ← normSq_eq_norm_sq]
  show (a * v⁻¹ + b).im = 0 ↔ _
  constructor
  · intro h
    rw [h, zero_mul] at e1
    rw [← e1] at e2
    rcases mul_eq_zero.mp e2 with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hb0
  · intro h
    rw [h, sub_self, zero_mul] at e2
    rw [← e2] at e1
    rcases mul_eq_zero.mp e1 with h' | h'
    · exact h'
    · exact absurd h' hN

/-- NOTES 14 for Proposition 7.10 (a): on a `K`-quasi pair, the label map `R = lab ∘ X*` grows at
most linearly in reverse, `|z| ≤ C (|R z| + 1)` on `Ω*`; hence `R z → ∞` as `z → ∞`
(`d(X*(z), X(R z)) ≤ D` from Lemma 3.5, `s03_cr_close`, and Lemma 2.3 on both sides). -/
theorem s07_label_norm_growth {Ω Ωs : Set ℂ} {K : ℝ} (h : IsKQuasiPair Ω Ωs K)
    (hnl : ¬ IsLinePair Ω Ωs) {lab : ℂ × ℝ → ℂ} (hlab : IsLabel Ω lab) :
    ∃ C : ℝ, ∀ z ∈ Ωs, ‖z‖ ≤ C * (‖lab (epstein Ωs z)‖ + 1) := by
  obtain ⟨D, hD⟩ := lem_width K
  set D' := max D 0 with hD'def
  have hD'0 : 0 ≤ D' := le_max_right _ _
  obtain ⟨hw1, -, hw3⟩ := hD Ω Ωs h hnl
  have hDg : ∀ q ∈ gap Ω Ωs, hdistSet q (horoUnion Ω) ≤ D' := fun q hq =>
    (hw1 q hq).1.trans (le_max_left _ _)
  have hDs : ∀ ws ∈ Ωs, hdistSet (epstein Ωs ws) (horoUnion Ω) ≤ D' := fun ws hws =>
    (hw3 ws hws).trans (le_max_left _ _)
  have hJ := s03_b0_jordanPair h
  have hJs := s03_b0_jordanPair (s03_qce_swap h)
  have hR := s02_jordanPair_riemannMap hJ
  have hRs := s02_jordanPair_riemannMap hJs
  have hsep := (prop_separation_b hJ hnl).2
  -- a point `y₀` of the curve
  obtain ⟨e, he1, he2⟩ := hJ
  have hy₀ : e 0 ∉ Ω := by
    rw [← he1]
    rintro ⟨w, hw, hew⟩
    have : w = 0 := e.injective hew
    rw [this] at hw
    simp [upperHalf] at hw
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = Real.cosh D' := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := hcdef ▸ Real.one_le_cosh D'
  refine ⟨(3 + 88 * c) * (1 + ‖e 0‖), fun z hz => ?_⟩
  obtain ⟨hv, hP, hd⟩ := s03_qik_pt h hnl hsep hlab hD'0 hDg hDs
    (Or.inr (Or.inl ⟨z, hz, rfl, rfl⟩))
  set v := lab (epstein Ωs z) with hvdef
  have hQ : epstein Ω v ∈ UHS := s03_wd_horoUnion_sub Ω (s03_qik_mem hR hv)
  have hPpos : 0 < (epstein Ωs z).2 := hP
  have hQpos : 0 < (epstein Ω v).2 := hQ
  obtain ⟨cl1, cl2⟩ := s03_cr_close (D := D') hQpos hPpos (by rw [s02_hdist_comm]; exact hd)
  rw [← hcdef] at cl1 cl2
  obtain ⟨-, -, -, hs4, -, hs6⟩ := lem_ep_position hRs hz
  obtain ⟨-, -, -, -, hq5, hq6⟩ := lem_ep_position hR hv
  have hdv : infDist v Ωᶜ ≤ ‖v‖ + ‖e 0‖ := by
    calc infDist v Ωᶜ ≤ dist v (e 0) := infDist_le_dist_of_mem hy₀
      _ = ‖v - e 0‖ := dist_eq_norm _ _
      _ ≤ ‖v‖ + ‖e 0‖ := norm_sub_le _ _
  have hdv0 : 0 ≤ infDist v Ωᶜ := infDist_nonneg
  have t1 := norm_sub_norm_le z (epstein Ωs z).1
  have t2 := norm_sub_norm_le (epstein Ωs z).1 (epstein Ω v).1
  have t3 := norm_sub_norm_le (epstein Ω v).1 v
  rw [norm_sub_rev] at t1 t2
  have m1 : 2 * c * (epstein Ω v).2 ≤ 2 * c * (4 * infDist v Ωᶜ) :=
    mul_le_mul_of_nonneg_left hq5 (by positivity)
  have hz1 : ‖z‖ ≤ ‖v‖ + (2 + 88 * c) * infDist v Ωᶜ := by nlinarith
  have hV := norm_nonneg v
  have hY := norm_nonneg (e 0)
  have hc0 : (0 : ℝ) ≤ 2 + 88 * c := by linarith
  have hz2 : ‖z‖ ≤ ‖v‖ + (2 + 88 * c) * (‖v‖ + ‖e 0‖) := by
    have := mul_le_mul_of_nonneg_left hdv hc0
    linarith
  nlinarith [mul_nonneg hY hV, mul_nonneg (by linarith : (0 : ℝ) ≤ 3 + 88 * c) (mul_nonneg hY hV)]

/-- Proposition 7.10 (a), boundary values: the far-side map `A` has boundary values `h`
(`g(j z) → x_ζ`; if `x_ζ ≠ x₀`, `R` extends by the identity at the finite point `1/(x_ζ - x₀)` of
`Γ′`, `cor_R_qi`; if `x_ζ = x₀`, `R → ∞` by `s07_label_norm_growth`; then Carathéodory,
`s07_disk_preimage_tendsto`). -/
theorem s07_farSide_boundaryValues {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    (hnr : ¬ IsRoundCircle Ω Ωs) {f g h : ℂ → ℂ} (hw : IsDiskWelding Ω Ωs f g h) {x₀ : ℂ}
    (hx₀ : x₀ ∈ curveOf Ω Ωs) {lab : ℂ × ℝ → ℂ} (hlab : IsLabel (invPairΩ Ω x₀) lab)
    {A : ℂ → ℂ} (hA : IsFarSideMap Ω Ωs f g x₀ lab A) : HasDiskBoundaryValues A h := by
  obtain ⟨hf, hg, hgInf, hhS, hlim⟩ := hw
  have hx : x₀ ∉ Ω ∧ x₀ ∉ Ωs := by
    simpa only [curveOf, mem_compl_iff, mem_union, not_or] using hx₀
  have hQP := s03_invPair_isKQuasiPair hΓ hx₀
  have hNL := s07_invPair_not_linePair hx₀ hnr
  obtain ⟨_, _, _, hRid⟩ := cor_R_qi K
  -- `Ω ∩ Ω* = ∅`
  have hdisj : Disjoint Ω Ωs := by
    obtain ⟨F, hFq, -, hF1, hF2⟩ := hΓ
    rw [← hF1, ← hF2]
    refine disjoint_image_of_injective ?_ ?_
    · exact fun a b hab => hFq.2.2.1.2.1 (mem_univ a) (mem_univ b) hab
    · rw [Set.disjoint_left]
      intro z hz1 hz2
      have h1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz1
      have h2 : 1 < ‖z‖ := hz2
      linarith
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hΩso : IsOpen Ωs := hg.isOpen hEo
  intro ζ hζ
  have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
  have hζ0 : ζ ≠ 0 := ne_zero_of_norm_ne_zero (by rw [hζ1]; exact one_ne_zero)
  obtain ⟨x, hfx, hgx⟩ := hlim ζ hζ
  have hhζ := hhS hζ
  have hAD : ∀ᶠ z in 𝓝[unitDisc] ζ, A z ∈ unitDisc :=
    eventually_nhdsWithin_of_forall fun z hz => (hA z hz).1
  refine s07_disk_preimage_tendsto hΓ hf hhζ hfx hAD ?_
  -- neighbourhood filters at the boundary are nontrivial
  haveI hDne : (𝓝[unitDisc] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    show ζ ∈ closure (ball (0 : ℂ) 1)
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact sphere_subset_closedBall hζ)
  -- `j z → ζ` from `𝔻` into `𝔻*`
  have hjt : Tendsto jRefl (𝓝[unitDisc] ζ) (𝓝[unitDiscExterior] ζ) := by
    have hjζ : jRefl ζ = ζ := by
      have hm : ζ * conj ζ = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ1]
        norm_num
      show (conj ζ)⁻¹ = ζ
      exact inv_eq_of_mul_eq_one_left hm
    have hjc : ContinuousAt jRefl ζ :=
      (Complex.continuous_conj.continuousAt).inv₀ (by simpa using hζ0)
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h1 := hjc.tendsto
      rw [hjζ] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (compl_singleton_mem_nhds hζ0)]
        with z hz hz0
      show 1 < ‖(conj z)⁻¹‖
      rw [norm_inv, Complex.norm_conj]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hz0)).2 (mem_ball_zero_iff.mp hz)
  have hgj : Tendsto (fun z => g (jRefl z)) (𝓝[unitDisc] ζ) (𝓝 x) := hgx.comp hjt
  have hgjΩs : ∀ᶠ z in 𝓝[unitDisc] ζ, g (jRefl z) ∈ Ωs :=
    hjt.eventually (eventually_nhdsWithin_of_forall fun w hw => hg.2.2 ▸ mem_image_of_mem g hw)
  have hz0 : ∀ᶠ z in 𝓝[unitDisc] ζ, z ≠ 0 :=
    nhdsWithin_le_nhds (compl_singleton_mem_nhds hζ0)
  have hout : ∀ᶠ z in 𝓝[unitDisc] ζ, outerPt g x₀ z = invAt x₀ (g (jRefl z)) :=
    hz0.mono fun z hz => if_neg hz
  -- `outer z ∈ Ω*′` and `f(A z) = x₀ + 1/R(outer z)`
  have houtΩs : ∀ z ∈ unitDisc, outerPt g x₀ z ∈ invPairΩs Ωs x₀ := by
    intro z hz
    by_cases h0 : z = 0
    · rw [show outerPt g x₀ z = 0 from if_pos h0]
      exact mem_union_right _ (mem_singleton 0)
    · rw [show outerPt g x₀ z = invAt x₀ (g (jRefl z)) from if_neg h0]
      refine mem_union_left _ (mem_image_of_mem _ ?_)
      rw [← hg.2.2]
      refine mem_image_of_mem g ?_
      show 1 < ‖(conj z)⁻¹‖
      rw [norm_inv, Complex.norm_conj]
      exact (one_lt_inv₀ (norm_pos_iff.mpr h0)).2 (mem_ball_zero_iff.mp hz)
  have hfA : ∀ z ∈ unitDisc,
      f (A z) = x₀ + (lab (epstein (invPairΩs Ωs x₀) (outerPt g x₀ z)))⁻¹ := by
    intro z hz
    rw [← (hA z hz).2]
    show f (A z) = x₀ + ((f (A z) - x₀)⁻¹)⁻¹
    rw [inv_inv]
    ring
  have hfA' : (fun z => f (A z)) =ᶠ[𝓝[unitDisc] ζ]
      fun z => x₀ + (lab (epstein (invPairΩs Ωs x₀) (outerPt g x₀ z)))⁻¹ :=
    eventually_nhdsWithin_of_forall hfA
  refine Tendsto.congr' hfA'.symm ?_
  have houtW : ∀ᶠ z in 𝓝[unitDisc] ζ, outerPt g x₀ z ∈ invPairΩs Ωs x₀ :=
    eventually_nhdsWithin_of_forall houtΩs
  -- `x ∈ Γ`
  have hxΩs : x ∉ Ωs := by
    intro hxs
    haveI : (𝓝[unitDisc] (h ζ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
      show h ζ ∈ closure (ball (0 : ℂ) 1)
      rw [closure_ball (0 : ℂ) one_ne_zero]
      exact sphere_subset_closedBall hhζ)
    obtain ⟨z, hz1, hz2⟩ := ((hfx.eventually (hΩso.mem_nhds hxs)).and
      (eventually_nhdsWithin_of_forall fun z hz => hf.2.2 ▸ mem_image_of_mem f hz)).exists
    exact Set.disjoint_left.1 hdisj hz2 hz1
  have hxΩ : x ∉ Ω := by
    intro hxs
    obtain ⟨z, hz1, hz2⟩ := ((hgj.eventually (hΩo.mem_nhds hxs)).and hgjΩs).exists
    exact Set.disjoint_left.1 hdisj hz1 hz2
  by_cases hxx : x = x₀
  · -- `x_ζ = x₀`: `outer z → ∞`, hence `R(outer z) → ∞`
    rw [hxx] at hgj ⊢
    obtain ⟨C, hC⟩ := s07_label_norm_growth hQP hNL hlab
    set C' := max C 1 with hC'def
    have hC'1 : 1 ≤ C' := le_max_right _ _
    have hC'pos : 0 < C' := by linarith
    have hd : Tendsto (fun z => ‖g (jRefl z) - x₀‖) (𝓝[unitDisc] ζ) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := (hgj.sub_const x₀).norm
        rwa [sub_self, norm_zero] at this
      · filter_upwards [hgjΩs] with z hz
        exact norm_pos_iff.mpr (sub_ne_zero.mpr fun h' => hx.2 (h' ▸ hz))
    have hO : Tendsto (fun z => ‖outerPt g x₀ z‖) (𝓝[unitDisc] ζ) atTop := by
      refine (tendsto_inv_nhdsGT_zero.comp hd).congr' ?_
      filter_upwards [hout] with z hz
      rw [hz]
      show ‖g (jRefl z) - x₀‖⁻¹ = ‖(g (jRefl z) - x₀)⁻¹‖
      rw [norm_inv]
    have hRn : Tendsto (fun z => ‖lab (epstein (invPairΩs Ωs x₀) (outerPt g x₀ z))‖)
        (𝓝[unitDisc] ζ) atTop := by
      refine tendsto_atTop_mono' _ ?_
        (tendsto_atTop_add_const_right _ (-1) (hO.atTop_div_const hC'pos))
      filter_upwards [houtW] with z hz
      have h1 := hC _ hz
      have h2 : C * (‖lab (epstein (invPairΩs Ωs x₀) (outerPt g x₀ z))‖ + 1) ≤
          C' * (‖lab (epstein (invPairΩs Ωs x₀) (outerPt g x₀ z))‖ + 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      rw [div_add' _ _ _ hC'pos.ne', div_le_iff₀ hC'pos]
      nlinarith
    have hinv : Tendsto (fun z => (lab (epstein (invPairΩs Ωs x₀) (outerPt g x₀ z)))⁻¹)
        (𝓝[unitDisc] ζ) (𝓝 0) := by
      refine squeeze_zero_norm (fun z => (norm_inv _).le) ?_
      exact tendsto_inv_atTop_zero.comp hRn
    simpa using (tendsto_const_nhds (x := x₀)).add hinv
  · -- `x_ζ ≠ x₀`: `outer z → p = 1/(x - x₀) ∈ Γ′` and `R → p`
    have hp0 : x - x₀ ≠ 0 := sub_ne_zero.mpr hxx
    set p := invAt x₀ x with hpdef
    have hpne : p ≠ 0 := inv_ne_zero hp0
    have hpΓ : p ∈ curveOf (invPairΩ Ω x₀) (invPairΩs Ωs x₀) := by
      simp only [curveOf, mem_compl_iff, mem_union, not_or]
      refine ⟨?_, ?_⟩
      · rintro ⟨y, hy, he⟩
        have : y = x := sub_left_injective (inv_injective he)
        exact hxΩ (this ▸ hy)
      · rintro (⟨y, hy, he⟩ | h0)
        · have : y = x := sub_left_injective (inv_injective he)
          exact hxΩs (this ▸ hy)
        · exact hpne h0
    have hpt : Tendsto (outerPt g x₀) (𝓝[unitDisc] ζ) (𝓝[invPairΩs Ωs x₀] p) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, houtW⟩
      refine Tendsto.congr' (hout.mono fun z hz => hz.symm) ?_
      exact ((hgj.sub_const x₀).inv₀ hp0)
    have hR := ((hRid _ _ hQP hNL lab hlab).2.2.2 p hpΓ).comp hpt
    have := (tendsto_const_nhds (x := x₀)).add (hR.inv₀ hpne)
    have e : x = x₀ + p⁻¹ := by
      show x = x₀ + ((x - x₀)⁻¹)⁻¹
      rw [inv_inv]
      ring
    rw [e]
    exact this

/-- Proposition 7.10 (a), `prop:opposite` (`sec07-transfer.tex:454`): `A` exists, is a Borel
quasi-isometry of `(𝔻, d_𝔻)` with constants depending only on `K`, and has boundary values
`h`. -/
theorem prop_opposite_a (K : ℝ) (hK : 1 ≤ K) : ∃ L c : ℝ,
    ∀ Ω Ωs : Set ℂ, IsBoundedKQuasicircle Ω Ωs K → ¬ IsRoundCircle Ω Ωs →
      ∀ f g h : ℂ → ℂ, IsDiskWelding Ω Ωs f g h → ∀ x₀ ∈ curveOf Ω Ωs,
      ∀ lab : ℂ × ℝ → ℂ, IsLabel (invPairΩ Ω x₀) lab →
        (∃ A, IsFarSideMap Ω Ωs f g x₀ lab A) ∧
        ∀ A, IsFarSideMap Ω Ωs f g x₀ lab A →
          IsDiskQI A L c ∧ Measurable (unitDisc.restrict A) ∧ HasDiskBoundaryValues A h := by
  -- `hK` is not needed: `cor_R_qi` holds for every `K` (the class is empty for `K < 1`).
  have _hK := hK
  obtain ⟨A₀, B₀, E₀, hRq⟩ := cor_R_qi K
  refine ⟨max A₀ 1, max B₀ 0, fun Ω Ωs hΓ hnr f g h hw x₀ hx₀ lab hlab => ?_⟩
  have hf := hw.1
  have hg := hw.2.1
  have hgInf := hw.2.2.1
  have hx : x₀ ∉ Ω ∧ x₀ ∉ Ωs := by
    simpa only [curveOf, mem_compl_iff, mem_union, not_or] using hx₀
  have hQP := s03_invPair_isKQuasiPair hΓ hx₀
  have hNL := s07_invPair_not_linePair hx₀ hnr
  obtain ⟨hR1, hR2, -, -⟩ := hRq _ _ hQP hNL lab hlab
  have hF := s07_invAt_conformal hf hx.1
  have hO := s07_outer_conformal hg hgInf hx.2
  have hconj : ∀ z ∈ unitDisc, conj z ∈ unitDisc := fun z hz => by
    show conj z ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, Complex.norm_conj]
    exact mem_ball_zero_iff.mp hz
  have hOmem : ∀ z ∈ unitDisc, outerPt g x₀ z ∈ invPairΩs Ωs x₀ := fun z hz => by
    rw [← hO.2.2]
    exact ⟨conj z, hconj z hz, by simp only [Complex.conj_conj]⟩
  have hex : ∀ z ∈ unitDisc, ∃ a ∈ unitDisc,
      invAt x₀ (f a) = lab (epstein (invPairΩs Ωs x₀) (outerPt g x₀ z)) := fun z hz => by
    have h1 := hR1 _ (hOmem z hz)
    rw [← hF.2.2] at h1
    obtain ⟨a, ha, he⟩ := h1
    exact ⟨a, ha, he⟩
  classical
  refine ⟨⟨fun z => if hz : z ∈ unitDisc then (hex z hz).choose else 0, fun z hz => ?_⟩,
    fun A hA => ?_⟩
  · simp only [dif_pos hz]
    exact (hex z hz).choose_spec
  -- the quasi-isometry bounds
  have hdc : ∀ a b : ℂ, diskDist (conj a) (conj b) = diskDist a b := fun a b => by
    unfold diskDist diskCoshDist
    rw [show conj a - conj b = conj (a - b) from (map_sub _ _ _).symm, Complex.norm_conj,
      Complex.norm_conj, Complex.norm_conj]
  have hL1 : 1 ≤ max A₀ 1 := le_max_right _ _
  have hLpos : 0 < max A₀ 1 := by linarith
  have hc0 : 0 ≤ max B₀ 0 := le_max_right _ _
  refine ⟨⟨fun z hz => (hA z hz).1, fun x hx y hy => ?_⟩, ?_,
    s07_farSide_boundaryValues hΓ hnr hw hx₀ hlab hA⟩
  · have hd1 : diskDist (A x) (A y) = poincareDist (invPairΩ Ω x₀)
        (lab (epstein (invPairΩs Ωs x₀) (outerPt g x₀ x)))
        (lab (epstein (invPairΩs Ωs x₀) (outerPt g x₀ y))) := by
      rw [← (hA x hx).2, ← (hA y hy).2]
      exact (subsec_poincare_dist hF (hA x hx).1 (hA y hy).1).symm
    have hd2 : poincareDist (invPairΩs Ωs x₀) (outerPt g x₀ x) (outerPt g x₀ y) =
        diskDist x y := by
      have h1 := subsec_poincare_dist hO (hconj x hx) (hconj y hy)
      simp only [Complex.conj_conj] at h1
      rw [h1, hdc]
    obtain ⟨u1, u2⟩ := hR2 _ (hOmem x hx) _ (hOmem y hy)
    rw [← hd1, hd2] at u1 u2
    have hD0 := s02_diskDist_nonneg (hA x hx).1 (hA y hy).1
    have hd0 := s02_diskDist_nonneg hx hy
    have hA₀ : A₀ ≤ max A₀ 1 := le_max_left _ _
    have hB₀ : B₀ ≤ max B₀ 0 := le_max_left _ _
    have v1 : A₀ * diskDist x y ≤ max A₀ 1 * diskDist x y :=
      mul_le_mul_of_nonneg_right hA₀ hd0
    have v2 : A₀ * diskDist (A x) (A y) ≤ max A₀ 1 * diskDist (A x) (A y) :=
      mul_le_mul_of_nonneg_right hA₀ hD0
    refine ⟨?_, by linarith⟩
    have hlow : diskDist x y ≤ max A₀ 1 * diskDist (A x) (A y) + max B₀ 0 := by linarith
    have hinv : (max A₀ 1)⁻¹ * (max A₀ 1 * diskDist (A x) (A y) + max B₀ 0) =
        diskDist (A x) (A y) + (max A₀ 1)⁻¹ * max B₀ 0 := by
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hLpos.ne', one_mul]
    have hLc : (max A₀ 1)⁻¹ * max B₀ 0 ≤ max B₀ 0 := by
      have := (inv_le_one₀ hLpos).2 hL1
      nlinarith
    have := mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hLpos.le)
    linarith
  · -- measurability: `A = G⁻¹ ∘ lab ∘ X* ∘ outer` on `𝔻`
    obtain ⟨Gi, hGm, hGi⟩ := s07_measurable_leftInv hF.1.continuousOn hF.2.1
    have hAG : ∀ z ∈ unitDisc, A z = Gi (lab (epstein (invPairΩs Ωs x₀) (outerPt g x₀ z))) :=
      fun z hz => by
        rw [← (hA z hz).2]
        exact (hGi (A z) (hA z hz).1).symm
    have hOc : ContinuousOn (outerPt g x₀) unitDisc := by
      have h1 := hO.1.continuousOn.comp Complex.continuous_conj.continuousOn hconj
      refine h1.congr fun z _ => ?_
      simp only [Function.comp_def, Complex.conj_conj]
    have hEp : ContinuousOn (epstein (invPairΩs Ωs x₀)) (invPairΩs Ωs x₀) := fun w hw =>
      (s02_epstein_differentiableAt ⟨_, hO⟩ hw).continuousAt.continuousWithinAt
    have hcont : Continuous (unitDisc.restrict
        (fun z => epstein (invPairΩs Ωs x₀) (outerPt g x₀ z))) :=
      (hEp.comp hOc hOmem).restrict
    have heq : unitDisc.restrict A = fun z : unitDisc =>
        Gi (lab (unitDisc.restrict (fun z => epstein (invPairΩs Ωs x₀) (outerPt g x₀ z)) z)) := by
      funext z
      exact hAG z z.2
    rw [heq]
    exact hGm.comp (hlab.1.comp hcont.measurable)

/-- (2.6) for an arbitrary (not necessarily measurable) integrand `φ`. -/
theorem s07_pullback_mass_any {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (φ : ℂ → ℝ≥0∞) :
    ∫⁻ w, φ w ∂curvMass Ω =
      ∫⁻ z in unitDisc, φ (f z) *
        ENNReal.ofReal (‖schwarzian f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 / 4) := by
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hDo : IsOpen unitDisc := isOpen_ball
  obtain ⟨G, hGm, hGf⟩ := s07_measurable_leftInv hf.1.continuousOn hf.2.1
  have hΩm : MeasurableSet Ω := by
    rw [← hf.2.2]
    exact hD.image_of_continuousOn_injOn hf.1.continuousOn hf.2.1
  have hne : ∀ z ∈ unitDisc, deriv f z ≠ 0 := fun z hz =>
    deriv_ne_zero_of_injOn hDo hf.1 hf.2.1 hz
  set h : ℂ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (‖schwarzianHol f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 / 4 / ‖deriv f z‖ ^ 2) with hhdef
  have hhm : Measurable h := by
    have h1 := s02_pullback_measurable_schwarzianHol f
    have h2 : Measurable (deriv f) := measurable_deriv f
    simp only [hhdef]
    fun_prop
  have hdf : ∀ z ∈ unitDisc,
      ENNReal.ofReal (schwarzNorm Ω (f z) ^ 2 * poincareDensity Ω (f z) ^ 2) = h z := by
    intro z hz
    have hd := s02_pullback_density hf hz
    have hn : 0 < ‖deriv f z‖ ^ 2 := by have := norm_pos_iff.mpr (hne z hz); positivity
    have hA := hf.1.analyticAt (hDo.mem_nhds hz)
    simp only [hhdef]
    rw [← schwarzian_of_analyticAt hA, ← hd]
    congr 1
    exact (mul_div_cancel_left₀ _ hn.ne').symm
  have hdm : AEMeasurable (fun w => ENNReal.ofReal (schwarzNorm Ω w ^ 2 * poincareDensity Ω w ^ 2))
      (volume.restrict Ω) := by
    refine (hhm.comp hGm).aemeasurable.congr ?_
    filter_upwards [ae_restrict_mem hΩm] with w hw
    rw [← hf.2.2] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    simp only [Function.comp, hGf z hz, hdf z hz]
  have hder : ∀ x ∈ unitDisc, HasFDerivWithinAt f
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f x)).restrictScalars ℝ)
      unitDisc x := fun x hx =>
    ((hf.1.differentiableAt (hDo.mem_nhds hx)).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt
  have hres : volume.restrict Ω = volume.restrict (f '' unitDisc) := by rw [hf.2.2]
  rw [curvMass, lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hdm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), hres,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hD hder hf.2.1]
  refine setLIntegral_congr_fun hD (fun z hz => ?_)
  have hd := s02_pullback_density hf hz
  simp only [Pi.mul_apply]
  rw [s02_pullback_det, ← mul_assoc, abs_of_nonneg (by positivity),
    ← ENNReal.ofReal_mul (by positivity), hd, mul_comm]

/-- The Schwarzian of the far-side chart is that of `g ∘ I`, away from `0`. -/
theorem s07_schwarzian_outer {Ωs : Set ℂ} {g : ℂ → ℂ}
    (hg : IsConformalOnto g unitDiscExterior Ωs) {x₀ : ℂ} (hx₀ : x₀ ∉ Ωs) {w : ℂ}
    (hw : w ∈ unitDisc) (hw0 : w ≠ 0) :
    schwarzian (fun u => outerPt g x₀ (conj u)) w = schwarzian (fun u => g u⁻¹) w := by
  have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hwE : w⁻¹ ∈ unitDiscExterior := by
    have h1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have h0 : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    show 1 < ‖w⁻¹‖
    rw [norm_inv]
    exact one_lt_inv_iff₀.mpr ⟨h0, h1⟩
  have hev : (fun u => outerPt g x₀ (conj u)) =ᶠ[𝓝[≠] w] fun u => invAt x₀ (g u⁻¹) := by
    refine nhdsWithin_le_nhds ?_
    filter_upwards [isOpen_ne.mem_nhds hw0] with u hu
    exact s07_outerPt_conj hu
  rw [schwarzian_congr hev]
  have hgA : AnalyticAt ℂ g w⁻¹ := hg.1.analyticAt (hEo.mem_nhds hwE)
  have hA : AnalyticAt ℂ (fun u => g u⁻¹) w := hgA.comp (analyticAt_inv hw0)
  have hd : deriv (fun u => g u⁻¹) w ≠ 0 := by
    have hgd : HasDerivAt g (deriv g w⁻¹) w⁻¹ :=
      (hg.1.differentiableAt (hEo.mem_nhds hwE)).hasDerivAt
    rw [show (fun u => g u⁻¹) = g ∘ Inv.inv from rfl, (hgd.comp w (hasDerivAt_inv hw0)).deriv]
    exact mul_ne_zero (deriv_ne_zero_of_injOn hEo hg.1 hg.2.1 hwE)
      (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hw0)))
  have hgw : g w⁻¹ ∈ Ωs := hg.2.2 ▸ mem_image_of_mem g hwE
  have hden : (1 : ℂ) * g w⁻¹ + -x₀ ≠ 0 := by
    intro h
    rw [one_mul, add_neg_eq_zero] at h
    rw [h] at hgw
    exact hx₀ hgw
  have hfun : (fun u => invAt x₀ (g u⁻¹)) = fun u => (0 * g u⁻¹ + 1) / (1 * g u⁻¹ + -x₀) := by
    funext u
    simp [invAt, sub_eq_add_neg]
  rw [hfun]
  exact schwarzian_mobius_comp_of_ne hA hd (by norm_num) hden

/-- Lebesgue measure on `𝔻` is invariant under `z ↦ z̄`. -/
theorem s07_setLIntegral_conj (Φ : ℂ → ℝ≥0∞) :
    ∫⁻ w in unitDisc, Φ (conj w) = ∫⁻ z in unitDisc, Φ z := by
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have himg : (fun w => conj w) '' unitDisc = unitDisc := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [unitDisc] using hw
    · intro hz
      exact ⟨conj z, by simpa [unitDisc] using hz, conj_conj z⟩
  have hder : ∀ x ∈ unitDisc, HasFDerivWithinAt (fun w => conj w)
      (conjCLE : ℂ →L[ℝ] ℂ) unitDisc x := fun x _ => conjCLE.hasFDerivAt.hasFDerivWithinAt
  have hdet : (conjCLE : ℂ →L[ℝ] ℂ).det = -1 := by
    rw [ContinuousLinearMap.det, ← det_conjAe]
    rfl
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hD hder
    (fun x _ y _ hxy => by have := congrArg (starRingEnd ℂ) hxy; simpa using this) Φ
  rw [himg] at h
  rw [h]
  refine setLIntegral_congr_fun hD (fun x _ => ?_)
  rw [hdet]
  simp

/-- Proposition 7.10 (b), `prop:opposite` (`sec07-transfer.tex:456`):
`K_*(f(a)) = 𝒫_{A_* m^*}(a) = ∫_𝔻 k_a(A z) dm^*(z)`. -/
theorem prop_opposite_b (K : ℝ) (Ω Ωs : Set ℂ) (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    (hnc : ¬ IsRoundCircle Ω Ωs) (f g : ℂ → ℂ) (hf : IsConformalOnto f unitDisc Ω)
    (hg : IsConformalOnto g unitDiscExterior Ωs) (hgInf : Tendsto g (cocompact ℂ) (cocompact ℂ))
    (x₀ : ℂ) (hx₀ : x₀ ∈ curveOf Ω Ωs) (lab : ℂ × ℝ → ℂ) (hlab : IsLabel (invPairΩ Ω x₀) lab)
    (A : ℂ → ℂ) (hA : IsFarSideMap Ω Ωs f g x₀ lab A) (a : ℂ) (ha : a ∈ unitDisc) :
    Kst (invPairΩ Ω x₀) (invPairΩs Ωs x₀) lab (invAt x₀ (f a)) =
      ∫⁻ z, ENNReal.ofReal (diskKernel a (A z)) ∂farMass g := by
  -- `hΓ`, `hnc` and `hlab` are not needed: the identity is a change of variables.
  have _h1 := hΓ
  have _h2 := hnc
  have _h3 := hlab
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hx₀Ω : x₀ ∉ Ω := fun h => hx₀ (Or.inl h)
  have hx₀Ωs : x₀ ∉ Ωs := fun h => hx₀ (Or.inr h)
  have hF : IsConformalOnto (fun z => invAt x₀ (f z)) unitDisc (invPairΩ Ω x₀) :=
    s07_invAt_conformal hf hx₀Ω
  have hH := s07_outer_conformal hg hgInf hx₀Ωs
  have hconjD : ∀ w ∈ unitDisc, conj w ∈ unitDisc := fun w hw => by simpa [unitDisc] using hw
  have h0v : ∀ᵐ w ∂(volume : Measure ℂ), w ≠ 0 := by
    rw [ae_iff]
    simp
  have h0 : ∀ᵐ w ∂(volume.restrict unitDisc), w ≠ 0 := ae_restrict_of_ae h0v
  -- the far-side density, made measurable on `𝔻 \ {0}`
  have hdm : AEMeasurable (fun z => ENNReal.ofReal
      (‖schwarzian (fun u => g u⁻¹) (conj z)‖ ^ 2 * varpi z ^ 2 / 4))
      (volume.restrict unitDisc) := by
    have hS := s02_pullback_measurable_schwarzianHol (fun u => g u⁻¹)
    refine (Measurable.aemeasurable (f := fun z => ENNReal.ofReal
      (‖schwarzianHol (fun u => g u⁻¹) (conj z)‖ ^ 2 * varpi z ^ 2 / 4)) ?_).congr ?_
    · have hc : Measurable fun z : ℂ => conj z := continuous_conj.measurable
      have := hS.comp hc
      unfold varpi
      fun_prop
    · filter_upwards [ae_restrict_mem hD, h0] with z hz hz0
      have hEo : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
      have hcz : conj z ≠ 0 := by simpa using hz0
      have hE : (conj z)⁻¹ ∈ unitDiscExterior := by
        show 1 < ‖(conj z)⁻¹‖
        rw [norm_inv, Complex.norm_conj]
        exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hz0, mem_ball_zero_iff.mp hz⟩
      have hA' : AnalyticAt ℂ (fun u => g u⁻¹) (conj z) :=
        (hg.1.analyticAt (hEo.mem_nhds hE)).comp (analyticAt_inv hcz)
      simp only [schwarzian_of_analyticAt hA']
  unfold Kst farMass
  rw [s07_pullback_mass_any hH, lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hdm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    ← s07_setLIntegral_conj (fun z => ((fun z => ENNReal.ofReal
      (‖schwarzian (fun u => g u⁻¹) (conj z)‖ ^ 2 * varpi z ^ 2 / 4)) *
      fun z => ENNReal.ofReal (diskKernel a (A z))) z)]
  refine setLIntegral_congr_fun_ae hD ?_
  filter_upwards [h0v] with w hw0 hw
  obtain ⟨hAw, hlw⟩ := hA (conj w) (hconjD w hw)
  have hker : intrKernel (invPairΩ Ω x₀) (invAt x₀ (f a)) (invAt x₀ (f (A (conj w)))) =
      diskKernel a (A (conj w)) := by
    rw [eq_kernel_disk hF ha hAw]
    rfl
  simp only [Pi.mul_apply, conj_conj]
  rw [← hlw, hker, s07_schwarzian_outer hg hx₀Ωs hw hw0, mul_comm]
  congr 3
  unfold varpi
  rw [Complex.norm_conj]

/-- Helper for Proposition 7.10 (c): `m* = conj_* m_ĝ` on boxes,
`(ϖ m*)(𝔻 ∩ D(ζ, r)) = (ϖ m_ĝ)(𝔻 ∩ D(ζ̄, r))` for `ĝ(w) = outerPt g c (w̄)`. -/
theorem s07_opp_mstar_box {Ωs : Set ℂ} {g : ℂ → ℂ} (hg : IsConformalOnto g unitDiscExterior Ωs)
    {c : ℂ} (hc : c ∉ Ωs) (ζ : ℂ) (r : ℝ) :
    varpiMeasure (farMass g) (unitDisc ∩ ball ζ r) =
      varpiMeasure (pullbackMass (fun w => outerPt g c (conj w))) (unitDisc ∩ ball (conj ζ) r) := by
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hmv : Measurable fun z : ℂ => ENNReal.ofReal (varpi z) := by
    unfold varpi; fun_prop
  have hform : ∀ d : ℂ → ℝ≥0∞, varpiMeasure ((volume.restrict unitDisc).withDensity d) =
      (volume.restrict unitDisc).withDensity (d * fun z => ENNReal.ofReal (varpi z)) := by
    intro d
    unfold varpiMeasure
    rw [restrict_withDensity hD, Measure.restrict_restrict hD, inter_self,
      s07_withDensity_withDensity _ _ _ hmv (fun _ => ENNReal.ofReal_ne_top)]
  have h0v : ∀ᵐ w ∂(volume : Measure ℂ), w ≠ 0 := by
    rw [ae_iff]
    simp
  have h0 : ∀ᵐ w ∂(volume.restrict unitDisc), w ≠ 0 := ae_restrict_of_ae h0v
  have hB1 : MeasurableSet (unitDisc ∩ ball ζ r) := hD.inter measurableSet_ball
  have hB2 : MeasurableSet (unitDisc ∩ ball (conj ζ) r) := hD.inter measurableSet_ball
  unfold farMass pullbackMass
  rw [hform, hform, withDensity_apply _ hB1, withDensity_apply _ hB2, ← lintegral_indicator hB1,
    ← lintegral_indicator hB2]
  refine Eq.trans ?_ (s07_setLIntegral_conj _)
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem hD, h0] with w hw hw0
  have hcw : conj w ∈ unitDisc := by simpa [unitDisc] using hw
  have hcw0 : conj w ≠ 0 := by simpa using hw0
  have hmem : conj w ∈ unitDisc ∩ ball (conj ζ) r ↔ w ∈ unitDisc ∩ ball ζ r := by
    simp only [mem_inter_iff, unitDisc, mem_ball, Complex.dist_conj_conj, dist_zero_right,
      Complex.norm_conj]
  have hv : varpi (conj w) = varpi w := by
    unfold varpi
    rw [Complex.norm_conj]
  by_cases hwB : w ∈ unitDisc ∩ ball ζ r
  · rw [indicator_of_mem hwB, indicator_of_mem (hmem.mpr hwB)]
    simp only [Pi.mul_apply]
    rw [hv, s07_schwarzian_outer hg hc hcw hcw0]
  · rw [indicator_of_notMem hwB, indicator_of_notMem (fun h => hwB (hmem.mp h))]

/-- Proposition 7.10 (c), identification of `m*` (`sec07-transfer.tex:510–520`), BMO part: if the
bounded far-side chart `ĝ(w) = outerPt g c (w̄) = τ(g(1/w))`, `τ = invAt c`, has
`log ĝ' ∈ BMOA`, then `ϖ m* ∈ CM`. -/
theorem s07_opp_mstar_bmo {Ωs : Set ℂ} {g : ℂ → ℂ} (hg : IsConformalOnto g unitDiscExterior Ωs)
    (hgInf : Tendsto g (cocompact ℂ) (cocompact ℂ)) {c : ℂ} (hc : c ∉ Ωs)
    (hB : LogDerivBMOA (fun w => outerPt g c (conj w))) :
    IsCarlesonDisk (varpiMeasure (farMass g)) := by
  -- (B2) ⇒ (B3) for `ĝ`, `|Sĝ|²ϖ³ dA = 4 ϖ m_ĝ`, and `m* = conj_* m_ĝ` on boxes
  have h1 := s02_sw_B_fwd (s07_outer_conformal hg hgInf hc) hB
  have h2 : IsCarlesonDisk (varpiMeasure (pullbackMass (fun w => outerPt g c (conj w)))) := by
    rw [lem_one_sided_varpi]
    exact (s07_carleson_smul _).mpr h1
  obtain ⟨C, hCt, hCb⟩ := h2
  refine ⟨C, hCt, fun ζ hζ r hr0 hr2 => ?_⟩
  have hcζ : conj ζ ∈ sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, Complex.norm_conj]
    exact mem_sphere_zero_iff_norm.mp hζ
  rw [s07_opp_mstar_box hg hc ζ r]
  exact hCb (conj ζ) hcζ r hr0 hr2

/-- Proposition 7.10 (c), identification of `m*`, VMO part: if `log ĝ' ∈ VMOA`, then
`ϖ m* ∈ CM₀`. -/
theorem s07_opp_mstar_vmo {Ωs : Set ℂ} {g : ℂ → ℂ} (hg : IsConformalOnto g unitDiscExterior Ωs)
    (hgInf : Tendsto g (cocompact ℂ) (cocompact ℂ)) {c : ℂ} (hc : c ∉ Ωs)
    (hV : LogDerivVMOA (fun w => outerPt g c (conj w))) :
    IsVanishingCarlesonDisk (varpiMeasure (farMass g)) := by
  -- (V2) ⇒ (V3) for `ĝ`, then the box identity as in the BMO part
  have h2 : IsVanishingCarlesonDisk
      (varpiMeasure (pullbackMass (fun w => outerPt g c (conj w)))) := by
    rw [lem_one_sided_varpi]
    exact (s07_vanishingCarleson_smul _).mpr (s02_sw_V_fwd (s07_outer_conformal hg hgInf hc) hV)
  refine ⟨s07_opp_mstar_bmo hg hgInf hc hV.1, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hb⟩ := h2.2 ε hε
  refine ⟨δ, hδ, fun ζ hζ r hr0 hrδ => ?_⟩
  have hcζ : conj ζ ∈ sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, Complex.norm_conj]
    exact mem_sphere_zero_iff_norm.mp hζ
  rw [s07_opp_mstar_box hg hc ζ r]
  exact hb (conj ζ) hcζ r hr0 hrδ

/-- A round circle through `x₀` is sent by `invAt x₀` to a straight line: the transported pair is
a line pair (`sec08-thmB.tex:9–12`, circle case of Theorem B). -/
theorem s07_round_linePair {K : ℝ} {Ω Ωs : Set ℂ} (hΓ : IsBoundedKQuasicircle Ω Ωs K)
    (hr : IsRoundCircle Ω Ωs) {x₀ : ℂ} (hx₀ : x₀ ∈ curveOf Ω Ωs) :
    IsLinePair (invPairΩ Ω x₀) (invPairΩs Ωs x₀) := by
  obtain ⟨c, r, hr0, hcur⟩ := hr
  have hx₀S : x₀ ∈ sphere c r := by rw [← hcur]; exact hx₀
  obtain ⟨F, hF, -, h1, h2⟩ := hΓ
  have hFc : ContinuousOn F univ := hF.2.2.1.1
  have hFi : InjOn F univ := hF.2.2.1.2.1
  -- the two sides of the circle
  set E : Set ℂ := {z | r < dist z c} with hE
  have hBo : IsOpen (ball c r) := isOpen_ball
  have hEo : IsOpen E := isOpen_lt continuous_const (continuous_id.dist continuous_const)
  have hBE : ∀ z, z ∈ ball c r → z ∈ E → False := fun z hb he => lt_asymm (mem_ball.mp hb) he
  have hBEd : Disjoint (ball c r) E := Set.disjoint_left.mpr fun z hb he => hBE z hb he
  have hsphB : ∀ z ∈ ball c r, z ∉ sphere c r := fun z hb hs => (mem_ball.mp hb).ne hs
  have hsphE : ∀ z ∈ E, z ∉ sphere c r := fun z he hs => (show r < dist z c from he).ne' hs
  have hcov : ∀ z, z ∈ ball c r ∨ z ∈ sphere c r ∨ z ∈ E := by
    intro z
    rcases lt_trichotomy (dist z c) r with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hΩS : ∀ z ∈ Ω, z ∉ sphere c r := fun z hz hs => by
    rw [← hcur] at hs
    exact hs (Or.inl hz)
  have hΩsS : ∀ z ∈ Ωs, z ∉ sphere c r := fun z hz hs => by
    rw [← hcur] at hs
    exact hs (Or.inr hz)
  have hcov2 : ∀ z, z ∉ sphere c r → z ∈ Ω ∨ z ∈ Ωs := by
    intro z hz
    by_contra h
    apply hz
    rw [← hcur]
    intro h'
    exact h h'
  have hdisj : ∀ z ∈ Ω, z ∉ Ωs := by
    intro z hz hzs
    rw [← h1] at hz
    rw [← h2] at hzs
    obtain ⟨u, hu, rfl⟩ := hz
    obtain ⟨v, hv, hvu⟩ := hzs
    have he : v = u := hFi (mem_univ _) (mem_univ _) hvu
    have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
    have hv1 : 1 < ‖v‖ := hv
    rw [he] at hv1
    linarith
  have hΩc : IsPreconnected Ω := by
    rw [← h1]
    exact (convex_ball (0 : ℂ) 1).isPreconnected.image F (hFc.mono (subset_univ _))
  have hΩsc : IsPreconnected Ωs := by
    rw [← h2]
    exact (isPreconnected_setOf_lt_norm zero_le_one).image F (hFc.mono (subset_univ _))
  have hside : ∀ S : Set ℂ, IsPreconnected S → (∀ z ∈ S, z ∉ sphere c r) →
      S ⊆ ball c r ∨ S ⊆ E := fun S hS hS' =>
    hS.subset_or_subset hBo hEo hBEd fun z hz => by
      rcases hcov z with h | h | h
      · exact Or.inl h
      · exact absurd h (hS' z hz)
      · exact Or.inr h
  have hΩb : Bornology.IsBounded Ω := by
    rw [← h1]
    exact ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn
      (hFc.mono (subset_univ _))).isBounded.subset (image_mono ball_subset_closedBall)
  have hEnot : ¬ E ⊆ Ω := by
    intro hsub
    obtain ⟨R, hR⟩ := hΩb.subset_closedBall c
    set t : ℝ := max R r + 1 with ht
    have ht0 : 0 ≤ t := by linarith [le_max_right R r]
    have hnt : dist (c + (t : ℂ)) c = t := by
      rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg ht0]
    have hz : c + (t : ℂ) ∈ E := by
      show r < dist (c + (t : ℂ)) c
      rw [hnt]
      linarith [le_max_right R r]
    have h' := mem_closedBall.mp (hR (hsub hz))
    rw [hnt] at h'
    linarith [le_max_left R r]
  have hcE : c + ((r + 1 : ℝ) : ℂ) ∈ E := by
    show r < dist (c + ((r + 1 : ℝ) : ℂ)) c
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    linarith
  have hsets : Ω = ball c r ∧ Ωs = E := by
    rcases hside Ω hΩc hΩS with hΩB | hΩE
    · have hEs : E ⊆ Ωs := fun z hz => by
        rcases hcov2 z (hsphE z hz) with h | h
        · exact absurd hz (fun hz' => hBE z (hΩB h) hz')
        · exact h
      rcases hside Ωs hΩsc hΩsS with hsB | hsE
      · exact absurd (hsB (hEs hcE)) (fun hb => hBE _ hb hcE)
      · refine ⟨Subset.antisymm hΩB fun z hz => ?_, Subset.antisymm hsE hEs⟩
        rcases hcov2 z (hsphB z hz) with h | h
        · exact h
        · exact absurd (hsE h) (fun he => hBE z hz he)
    · exfalso
      have hBs : ball c r ⊆ Ωs := fun z hz => by
        rcases hcov2 z (hsphB z hz) with h | h
        · exact absurd (hΩE h) (fun he => hBE z hz he)
        · exact h
      rcases hside Ωs hΩsc hΩsS with hsB | hsE
      · apply hEnot
        intro z hz
        rcases hcov2 z (hsphE z hz) with h | h
        · exact h
        · exact absurd hz (fun hz' => hBE z (hsB h) hz')
      · have h' : r < dist c c := hsE (hBs (mem_ball_self hr0))
        rw [dist_self] at h'
        linarith
  obtain ⟨hΩe, hΩse⟩ := hsets
  -- the line: `Im(a w + b) = -Re(u w) - 1/2`, `u = x₀ - c`
  set u : ℂ := x₀ - c with hudef
  have hu : ‖u‖ = r := by
    rw [hudef, ← dist_eq_norm]
    exact hx₀S
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    linarith
  have hnu : normSq u = r ^ 2 := by rw [← Complex.sq_norm, hu]
  set a : ℂ := -I * u with hadef
  set b : ℂ := ((-(1 / 2) : ℝ) : ℂ) * I with hbdef
  have hIm : ∀ w : ℂ, (a * w + b).im = -(u * w).re - 1 / 2 := by
    intro w
    simp only [hadef, hbdef, Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.neg_re,
      Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hcore : ∀ z : ℂ, z ≠ x₀ →
      (a * invAt x₀ z + b).im * (2 * normSq (z - x₀)) = r ^ 2 - normSq (z - c) := by
    intro z hz
    have hN : normSq (z - x₀) ≠ 0 := (Complex.normSq_pos.mpr (sub_ne_zero.mpr hz)).ne'
    have hzc : z - c = u + (z - x₀) := by rw [hudef]; ring
    have hre : (u * invAt x₀ z).re = (u * conj (z - x₀)).re / normSq (z - x₀) := by
      unfold invAt
      simp only [Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.conj_re,
        Complex.conj_im]
      ring
    rw [hIm, hre, hzc, Complex.normSq_add, hnu]
    field_simp
    ring
  have hinv : ∀ w : ℂ, invAt x₀ (x₀ + w⁻¹) = w := fun w => by
    unfold invAt
    rw [add_sub_cancel_left, inv_inv]
  have hne : ∀ w : ℂ, w ≠ 0 → x₀ + w⁻¹ ≠ x₀ := fun w hw h => by
    apply inv_ne_zero hw
    linear_combination h
  have hb0 : (a * 0 + b).im = -(1 / 2) := by
    rw [hIm]
    simp
  have hsq : ∀ z : ℂ, normSq (z - c) = dist z c ^ 2 := fun z => by
    rw [dist_eq_norm, Complex.sq_norm]
  refine ⟨a, b, mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hu0, ?_, ?_⟩
  · unfold invPairΩ
    rw [hΩe]
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzx : z ≠ x₀ := fun h => hsphB z hz (h ▸ hx₀S)
      have h := hcore z hzx
      have hN : 0 < normSq (z - x₀) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hzx)
      have hd : dist z c < r := mem_ball.mp hz
      have hd2 : normSq (z - c) < r ^ 2 := by
        rw [hsq]
        nlinarith [dist_nonneg (x := z) (y := c)]
      show 0 < (a * invAt x₀ z + b).im
      nlinarith
    · intro hw
      have hw' : 0 < (a * w + b).im := hw
      have hw0 : w ≠ 0 := by
        rintro rfl
        rw [hb0] at hw'
        linarith
      refine ⟨x₀ + w⁻¹, ?_, hinv w⟩
      have h := hcore _ (hne w hw0)
      rw [hinv] at h
      have hN : 0 < normSq (x₀ + w⁻¹ - x₀) :=
        Complex.normSq_pos.mpr (sub_ne_zero.mpr (hne w hw0))
      have hd2 : normSq (x₀ + w⁻¹ - c) < r ^ 2 := by nlinarith
      rw [hsq] at hd2
      rw [mem_ball]
      nlinarith [dist_nonneg (x := x₀ + w⁻¹) (y := c)]
  · unfold invPairΩs
    rw [hΩse]
    ext w
    constructor
    · rintro (⟨z, hz, rfl⟩ | hw)
      · have hzE : r < dist z c := hz
        have hzx : z ≠ x₀ := fun h => hsphE z hz (h ▸ hx₀S)
        have h := hcore z hzx
        have hN : 0 < normSq (z - x₀) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hzx)
        have hd2 : r ^ 2 < normSq (z - c) := by
          rw [hsq]
          nlinarith
        show (a * invAt x₀ z + b).im < 0
        nlinarith
      · rw [mem_singleton_iff.mp hw]
        show (a * 0 + b).im < 0
        rw [hb0]
        norm_num
    · intro hw
      have hw' : (a * w + b).im < 0 := hw
      by_cases hw0 : w = 0
      · exact Or.inr (mem_singleton_iff.mpr hw0)
      refine Or.inl ⟨x₀ + w⁻¹, ?_, hinv w⟩
      have h := hcore _ (hne w hw0)
      rw [hinv] at h
      have hN : 0 < normSq (x₀ + w⁻¹ - x₀) :=
        Complex.normSq_pos.mpr (sub_ne_zero.mpr (hne w hw0))
      have hd2 : r ^ 2 < normSq (x₀ + w⁻¹ - c) := by nlinarith
      rw [hsq] at hd2
      show r < dist (x₀ + w⁻¹) c
      nlinarith [dist_nonneg (x := x₀ + w⁻¹) (y := c)]

/-! ## Example 7.12: quasi-isometries do not preserve the kernel -/

/-- The hyperbolic distance of `ℍ` (curvature `-1`, metric `|dz|/y`). -/
def hpDist (z w : ℂ) : ℝ := Real.arcosh (1 + ‖z - w‖ ^ 2 / (2 * z.im * w.im))

/-- The kernel `k_z(w) = sech²(d_ℍ(z, w)/2)` of `ℍ`. -/
def hpKernel (z w : ℂ) : ℝ := ((Real.cosh (hpDist z w / 2))⁻¹) ^ 2

/-- `F_α(r e^{iθ}) = r^α e^{iθ}`. -/
def powerMap (α : ℝ) (z : ℂ) : ℂ := ((‖z‖ ^ α : ℝ) : ℂ) * exp (arg z * I)

/-- For `l ≥ 1` and `t ≥ 0`, `tanh (l t) ≤ l tanh t`, in the form
`sinh (l t) cosh t ≤ l cosh (l t) sinh t`. -/
theorem s07_sinh_mul_cosh_le {l : ℝ} (hl : 1 ≤ l) {t : ℝ} (ht : 0 ≤ t) :
    Real.sinh (l * t) * Real.cosh t ≤ l * Real.cosh (l * t) * Real.sinh t := by
  have hd : ∀ s, HasDerivAt
      (fun s => l * Real.cosh (l * s) * Real.sinh s - Real.sinh (l * s) * Real.cosh s)
      ((l ^ 2 - 1) * Real.sinh (l * s) * Real.sinh s) s := by
    intro s
    have h1 : HasDerivAt (fun s => l * s) l s := by simpa using (hasDerivAt_id s).const_mul l
    have := ((h1.cosh.const_mul l).mul (Real.hasDerivAt_sinh s)).sub
      (h1.sinh.mul (Real.hasDerivAt_cosh s))
    convert this using 1
    ring
  have hmono : MonotoneOn
      (fun s => l * Real.cosh (l * s) * Real.sinh s - Real.sinh (l * s) * Real.cosh s)
      (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun s _ => (hd s).continuousAt.continuousWithinAt)
      (fun s _ => (hd s).differentiableAt.differentiableWithinAt) ?_
    rw [interior_Ici]
    intro s hs
    rw [(hd s).deriv]
    have h1 : 0 < Real.sinh s := Real.sinh_pos_iff.mpr hs
    have h2 : 0 < Real.sinh (l * s) := Real.sinh_pos_iff.mpr (by nlinarith [mem_Ioi.mp hs])
    exact mul_nonneg (mul_nonneg (by nlinarith) h2.le) h1.le
  have key : l * Real.cosh (l * 0) * Real.sinh 0 - Real.sinh (l * 0) * Real.cosh 0 ≤
      l * Real.cosh (l * t) * Real.sinh t - Real.sinh (l * t) * Real.cosh t :=
    hmono (Set.mem_Ici.mpr (le_refl 0)) ht ht
  simp only [mul_zero, Real.sinh_zero, Real.cosh_zero, zero_mul, sub_zero] at key
  linarith

/-- For `l ≥ 1`, `t ↦ sinh (l t) / sinh t` is nondecreasing on `(0, ∞)`. -/
theorem s07_sinh_ratio_mono {l : ℝ} (hl : 1 ≤ l) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.sinh (l * x) * Real.sinh y ≤ Real.sinh (l * y) * Real.sinh x := by
  have hd : ∀ s, 0 < s → HasDerivAt (fun s => Real.sinh (l * s) / Real.sinh s)
      ((Real.cosh (l * s) * l * Real.sinh s - Real.sinh (l * s) * Real.cosh s) /
        Real.sinh s ^ 2) s := by
    intro s hs
    have h1 : HasDerivAt (fun s => l * s) l s := by simpa using (hasDerivAt_id s).const_mul l
    exact h1.sinh.div (Real.hasDerivAt_sinh s) (Real.sinh_pos_iff.mpr hs).ne'
  have hmono : MonotoneOn (fun s => Real.sinh (l * s) / Real.sinh s) (Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Ioi]
      exact fun s hs => (hd s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]
      intro s hs
      rw [(hd s hs).deriv]
      have := s07_sinh_mul_cosh_le hl (le_of_lt hs)
      exact div_nonneg (by linarith) (sq_nonneg _)
  have h : Real.sinh (l * x) / Real.sinh x ≤ Real.sinh (l * y) / Real.sinh y :=
    hmono hx (lt_of_lt_of_le hx hxy) hxy
  rwa [div_le_div_iff₀ (Real.sinh_pos_iff.mpr hx)
    (Real.sinh_pos_iff.mpr (lt_of_lt_of_le hx hxy))] at h

/-- `sinh² |c| = sinh² c`. -/
theorem s07_sinh_sq_abs (c : ℝ) : Real.sinh |c| ^ 2 = Real.sinh c ^ 2 := by
  rcases abs_choice c with h | h <;> rw [h]
  rw [Real.sinh_neg, neg_sq]

/-- `|a| ≤ |b| ⇒ sinh² a ≤ sinh² b`. -/
theorem s07_sinh_sq_le_of_abs_le {a b : ℝ} (h : |a| ≤ |b|) : Real.sinh a ^ 2 ≤ Real.sinh b ^ 2 := by
  rw [← s07_sinh_sq_abs a, ← s07_sinh_sq_abs b]
  exact pow_le_pow_left₀ (Real.sinh_nonneg_iff.mpr (abs_nonneg a)) (Real.sinh_le_sinh.mpr h) 2

/-- For `a, b ≥ 0`, `sinh² a ≤ sinh² b ⇒ a ≤ b`. -/
theorem s07_le_of_sinh_sq_le {a b : ℝ} (hb : 0 ≤ b) (h : Real.sinh a ^ 2 ≤ Real.sinh b ^ 2) :
    a ≤ b := by
  by_contra hlt
  have h1 := Real.sinh_lt_sinh.mpr (lt_of_not_ge hlt)
  have h2 := Real.sinh_nonneg_iff.mpr hb
  nlinarith

/-- The scaling inequality behind Example 7.12: if `sinh² y = P (sinh² x + q)` with `P ≥ 1`,
`q ≥ 0`, `y ≥ 0`, then `P (sinh² (l x) + q) ≤ sinh² (l y)` for `l ≥ 1`. -/
theorem s07_sinh_sq_scale {l P q x y : ℝ} (hl : 1 ≤ l) (hP : 1 ≤ P) (hq : 0 ≤ q) (hy : 0 ≤ y)
    (h : Real.sinh y ^ 2 = P * (Real.sinh x ^ 2 + q)) :
    P * (Real.sinh (l * x) ^ 2 + q) ≤ Real.sinh (l * y) ^ 2 := by
  have hl0 : 0 ≤ l := by linarith
  rw [← s07_sinh_sq_abs (l * x), abs_mul, abs_of_nonneg hl0]
  rw [← s07_sinh_sq_abs x] at h
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hYl : Real.sinh y ≤ Real.sinh (l * y) := Real.sinh_le_sinh.mpr (by nlinarith)
  have hY0 : 0 ≤ Real.sinh y := Real.sinh_nonneg_iff.mpr hy
  rcases hx0.lt_or_eq with hxp | hxz
  · set A := Real.sinh |x| with hA
    set B := Real.sinh (l * |x|) with hB
    set Y := Real.sinh y with hY
    set Z := Real.sinh (l * y) with hZ
    have hApos : 0 < A := Real.sinh_pos_iff.mpr hxp
    have hBA : A ≤ B := Real.sinh_le_sinh.mpr (by nlinarith)
    have hxy : |x| ≤ y := by
      refine s07_le_of_sinh_sq_le hy ?_
      rw [h]
      nlinarith [sq_nonneg A]
    have hmono : B * Y ≤ Z * A := s07_sinh_ratio_mono hl hxp hxy
    have e1 : (B * Y) ^ 2 ≤ (Z * A) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by linarith) hY0) hmono 2
    have h3 : (B * Y) ^ 2 = B ^ 2 * (P * (A ^ 2 + q)) := by rw [mul_pow, h]
    have h4 : P * q * A ^ 2 ≤ P * q * B ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hApos.le hBA 2)
        (mul_nonneg (by linarith) hq)
    have e2 : A ^ 2 * (P * (B ^ 2 + q)) ≤ A ^ 2 * Z ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left e2 (by positivity)
  · have hx : |x| = 0 := hxz.symm
    rw [hx, mul_zero, Real.sinh_zero]
    rw [hx, Real.sinh_zero] at h
    have : Real.sinh y ^ 2 ≤ Real.sinh (l * y) ^ 2 := pow_le_pow_left₀ hY0 hYl 2
    nlinarith

/-- Log-polar form of the hyperbolic quotient: for `p = R e^{iθ}`, `p' = R' e^{iθ'}` in `ℍ`,
`|p - p'|² / (2 Im p Im p') = 2 (sinh² ((log R - log R')/2) + sin² ((θ - θ')/2))
/ (sin θ sin θ')`. -/
theorem s07_hp_quot_polar {R R' θ θ' : ℝ} (hR : 0 < R) (hR' : 0 < R') (hs : 0 < Real.sin θ)
    (hs' : 0 < Real.sin θ') {p p' : ℂ} (hpre : p.re = R * Real.cos θ)
    (hpim : p.im = R * Real.sin θ) (hpre' : p'.re = R' * Real.cos θ')
    (hpim' : p'.im = R' * Real.sin θ') :
    ‖p - p'‖ ^ 2 / (2 * p.im * p'.im) = 2 * (1 / (Real.sin θ * Real.sin θ') *
      (Real.sinh ((Real.log R - Real.log R') / 2) ^ 2 + Real.sin ((θ - θ') / 2) ^ 2)) := by
  have hnorm : ‖p - p'‖ ^ 2 = R ^ 2 + R' ^ 2 -
      2 * R * R' * (Real.cos θ * Real.cos θ' + Real.sin θ * Real.sin θ') := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hpre, hpim, hpre',
      hpim']
    linear_combination R ^ 2 * Real.sin_sq_add_cos_sq θ + R' ^ 2 * Real.sin_sq_add_cos_sq θ'
  have hu : Real.cosh (Real.log R - Real.log R') = (R / R' + (R / R')⁻¹) / 2 := by
    rw [← Real.log_div hR.ne' hR'.ne', Real.cosh_log (div_pos hR hR')]
  have h2 := Real.cosh_two_mul ((Real.log R - Real.log R') / 2)
  rw [show 2 * ((Real.log R - Real.log R') / 2) = Real.log R - Real.log R' by ring,
    Real.cosh_sq] at h2
  have hS : Real.sinh ((Real.log R - Real.log R') / 2) ^ 2 =
      ((R / R' + (R / R')⁻¹) / 2 - 1) / 2 := by linarith
  have h3 := Real.cos_two_mul ((θ - θ') / 2)
  rw [show 2 * ((θ - θ') / 2) = θ - θ' by ring, Real.cos_sub] at h3
  have hT : Real.sin ((θ - θ') / 2) ^ 2 =
      (1 - (Real.cos θ * Real.cos θ' + Real.sin θ * Real.sin θ')) / 2 := by
    linarith [Real.sin_sq_add_cos_sq ((θ - θ') / 2)]
  rw [hnorm, hpim, hpim', hS, hT]
  field_simp
  ring

/-- `sinh² (d_ℍ(z, w)/2) = |z - w|² / (4 Im z Im w)`. -/
theorem s07_hpDist_sinh_sq {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    0 ≤ hpDist z w ∧
      Real.sinh (hpDist z w / 2) ^ 2 = ‖z - w‖ ^ 2 / (2 * z.im * w.im) / 2 := by
  have hQ : 0 ≤ ‖z - w‖ ^ 2 / (2 * z.im * w.im) := by positivity
  have h1 : 1 ≤ 1 + ‖z - w‖ ^ 2 / (2 * z.im * w.im) := by linarith
  refine ⟨Real.arcosh_nonneg h1, ?_⟩
  have h2 := Real.cosh_two_mul (hpDist z w / 2)
  rw [show 2 * (hpDist z w / 2) = hpDist z w by ring, Real.cosh_sq] at h2
  unfold hpDist at h2 ⊢
  rw [Real.cosh_arcosh h1] at h2
  linarith

theorem s07_powerMap_re (α : ℝ) (z : ℂ) :
    (powerMap α z).re = ‖z‖ ^ α * Real.cos (arg z) := by
  unfold powerMap
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem s07_powerMap_im (α : ℝ) (z : ℂ) :
    (powerMap α z).im = ‖z‖ ^ α * Real.sin (arg z) := by
  unfold powerMap
  rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- `0 < arg z < π` on the upper half-plane. -/
theorem s07_arg_mem_Ioo {z : ℂ} (hz : 0 < z.im) : 0 < arg z ∧ arg z < π := by
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_im] at hz; exact lt_irrefl 0 hz
  have hs : 0 < Real.sin (arg z) := by
    rw [Complex.sin_arg]; exact div_pos hz (norm_pos_iff.mpr hz0)
  refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hz.le) fun h => ?_,
    Complex.arg_lt_pi_iff.mpr (Or.inr hz.ne')⟩
  rw [← h, Real.sin_zero] at hs
  exact lt_irrefl 0 hs

/-- `log` maps `ℍ` conformally onto the strip `{0 < Im w < π}`, and `exp` maps the strip
conformally back onto `ℍ`. -/
theorem s07_log_exp_strip :
    IsConformalOnto Complex.log upperHalf {w : ℂ | 0 < w.im ∧ w.im < π} ∧
      IsConformalOnto Complex.exp {w : ℂ | 0 < w.im ∧ w.im < π} upperHalf := by
  have hne : ∀ z ∈ upperHalf, z ≠ 0 := fun z hz h => by
    have hz' : 0 < z.im := hz
    rw [h, Complex.zero_im] at hz'
    exact lt_irrefl 0 hz'
  have hlogS : ∀ z ∈ upperHalf, Complex.log z ∈ {w : ℂ | 0 < w.im ∧ w.im < π} := by
    intro z hz
    rw [mem_setOf_eq, Complex.log_im]
    exact s07_arg_mem_Ioo hz
  have hexpH : ∀ w ∈ {w : ℂ | 0 < w.im ∧ w.im < π}, Complex.exp w ∈ upperHalf := by
    intro w hw
    show 0 < (Complex.exp w).im
    rw [Complex.exp_im]
    exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hw.1 hw.2)
  have hlogexp : ∀ w ∈ {w : ℂ | 0 < w.im ∧ w.im < π}, Complex.log (Complex.exp w) = w :=
    fun w hw => Complex.log_exp (by linarith [hw.1, Real.pi_pos]) hw.2.le
  refine ⟨⟨fun z hz => (Complex.differentiableAt_log
    (Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hz)))).differentiableWithinAt,
    fun z hz w hw h => by rw [← Complex.exp_log (hne z hz), h, Complex.exp_log (hne w hw)], ?_⟩,
    ⟨Complex.differentiable_exp.differentiableOn,
    fun w hw w' hw' h => by rw [← hlogexp w hw, h, hlogexp w' hw'], ?_⟩⟩
  · refine Subset.antisymm (image_subset_iff.mpr hlogS) fun w hw => ?_
    exact ⟨Complex.exp w, hexpH w hw, hlogexp w hw⟩
  · refine Subset.antisymm (image_subset_iff.mpr hexpH) fun z hz => ?_
    exact ⟨Complex.log z, hlogS z hz, Complex.exp_log (hne z hz)⟩

/-- Example 7.12, `ex:power` (`sec07-transfer.tex:546`): `F_α` is a `max{α, α⁻¹}`-q.c. map of
`ℍ` onto itself. -/
theorem ex_power_qc (α : ℝ) (hα : 0 < α) :
    IsKQC (powerMap α) upperHalf (max α α⁻¹) ∧ powerMap α '' upperHalf = upperHalf := by
  set S : Set ℂ := {w : ℂ | 0 < w.im ∧ w.im < π} with hSdef
  set a : ℂ := (((α + 1) / 2 : ℝ) : ℂ) with hadef
  set b : ℂ := (((α - 1) / 2 : ℝ) : ℂ) with hbdef
  set A : ℂ → ℂ := fun z => a * z + b * conj z + 0 with hAdef
  have hAre : ∀ z, (A z).re = α * z.re := fun z => by
    simp only [hAdef, hadef, hbdef, add_zero, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  have hAim : ∀ z, (A z).im = z.im := fun z => by
    simp only [hAdef, hadef, hbdef, add_zero, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  have hHo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hSo : IsOpen S :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  obtain ⟨hlog, hexp⟩ := s07_log_exp_strip
  have hlog1 := isKQC_one_of_conformal hHo hlog
  have hexp1 := isKQC_one_of_conformal hSo hexp
  -- the affine stretch `A(s + iθ) = αs + iθ`
  have hna : ‖a‖ = (α + 1) / 2 := by
    rw [hadef, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hnb : ‖b‖ = |α - 1| / 2 := by
    rw [hbdef, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
  have hab : ‖b‖ < ‖a‖ := by
    rw [hna, hnb]
    have : |α - 1| < α + 1 := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
    linarith
  have hK : (‖a‖ + ‖b‖) / (‖a‖ - ‖b‖) = max α α⁻¹ := by
    rw [hna, hnb]
    rcases le_total 1 α with h | h
    · rw [abs_of_nonneg (by linarith), max_eq_left ((inv_le_one₀ hα).mpr h |>.trans h),
        show (α + 1) / 2 + (α - 1) / 2 = α by ring, show (α + 1) / 2 - (α - 1) / 2 = 1 by ring,
        div_one]
    · rw [abs_of_nonpos (by linarith), max_eq_right (h.trans ((one_le_inv₀ hα).mpr h)),
        show (α + 1) / 2 + -(α - 1) / 2 = 1 by ring, show (α + 1) / 2 - -(α - 1) / 2 = α by ring,
        one_div]
  have hAqc : IsKQC A S (max α α⁻¹) := by
    have h := isKQC_of_isC1Quasiconformal (affine_isC1Quasiconformal (C := 0) hab).1
    rw [hK] at h
    exact ac_t_isKQC_restrict h hSo (subset_univ S)
  have hAS : A '' S = S := by
    refine Subset.antisymm (image_subset_iff.mpr fun w hw => ?_) fun w hw => ?_
    · show 0 < (A w).im ∧ (A w).im < π
      rw [hAim]; exact hw
    · refine ⟨((w.re / α : ℝ) : ℂ) + (w.im : ℂ) * I, ?_, ?_⟩
      · have hw' : 0 < w.im ∧ w.im < π := by rw [hSdef] at hw; exact hw
        show 0 < (((w.re / α : ℝ) : ℂ) + (w.im : ℂ) * I).im ∧
          (((w.re / α : ℝ) : ℂ) + (w.im : ℂ) * I).im < π
        simpa using hw'
      · apply Complex.ext
        · rw [hAre]; simp; field_simp
        · rw [hAim]; simp
  have hsub1 : Complex.log '' upperHalf ⊆ S := hlog.2.2.subset
  have hc1 := thm7_1_comp hlog1 hAqc hsub1
  have hsub2 : (A ∘ Complex.log) '' upperHalf ⊆ S := by
    rw [image_comp, hlog.2.2, hAS]
  have hc2 := thm7_1_comp hc1 hexp1 hsub2
  rw [one_mul, mul_one] at hc2
  have heq : EqOn (powerMap α) (Complex.exp ∘ (A ∘ Complex.log)) upperHalf := by
    intro z hz
    have hz0 : z ≠ 0 := fun h => by
      have hz' : 0 < z.im := hz
      rw [h, Complex.zero_im] at hz'
      exact lt_irrefl 0 hz'
    have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hAl : A (Complex.log z) = ((α * Real.log ‖z‖ : ℝ) : ℂ) + (arg z : ℂ) * I := by
      apply Complex.ext
      · rw [hAre, Complex.log_re]; simp
      · rw [hAim, Complex.log_im]; simp
    simp only [Function.comp_apply]
    rw [hAl, Complex.exp_add, ← Complex.ofReal_exp, powerMap, Real.rpow_def_of_pos hr, mul_comm α]
  refine ⟨ad_isKQC_congr hc2 heq, ?_⟩
  rw [image_congr heq, image_comp, image_comp, hlog.2.2, hAS, hexp.2.2]

/-- Example 7.12, `ex:power` (`sec07-transfer.tex:552`): `F_α` is `max{α, α⁻¹}`-bi-Lipschitz
for the hyperbolic metric of `ℍ`. -/
theorem ex_power_bilip (α : ℝ) (hα : 0 < α) (z w : ℂ) (hz : z ∈ upperHalf)
    (hw : w ∈ upperHalf) :
    hpDist (powerMap α z) (powerMap α w) ≤ max α α⁻¹ * hpDist z w ∧
      hpDist z w ≤ max α α⁻¹ * hpDist (powerMap α z) (powerMap α w) := by
  have hzi : 0 < z.im := hz
  have hwi : 0 < w.im := hw
  set M := max α α⁻¹ with hMdef
  have hαM : α ≤ M := le_max_left _ _
  have hiM : α⁻¹ ≤ M := le_max_right _ _
  have hM1 : 1 ≤ M := by
    rcases le_total 1 α with h | h
    · linarith
    · exact le_trans (one_le_inv₀ hα |>.mpr h) hiM
  have hMα : 1 ≤ M * α := by
    have := mul_le_mul_of_nonneg_right hiM hα.le
    rwa [inv_mul_cancel₀ hα.ne'] at this
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_im] at hzi; exact lt_irrefl 0 hzi
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_im] at hwi; exact lt_irrefl 0 hwi
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hr' : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hs : 0 < Real.sin (arg z) := by rw [Complex.sin_arg]; exact div_pos hzi hr
  have hs' : 0 < Real.sin (arg w) := by rw [Complex.sin_arg]; exact div_pos hwi hr'
  set P := 1 / (Real.sin (arg z) * Real.sin (arg w)) with hPdef
  set q := Real.sin ((arg z - arg w) / 2) ^ 2 with hqdef
  set x := (Real.log ‖z‖ - Real.log ‖w‖) / 2 with hxdef
  have hP : 1 ≤ P := one_le_one_div (mul_pos hs hs')
    (by nlinarith [Real.sin_le_one (arg z), Real.sin_le_one (arg w)])
  have hq : 0 ≤ q := sq_nonneg _
  -- the two log-polar quotients
  have hQ := s07_hp_quot_polar hr hr' hs hs' (Complex.norm_mul_cos_arg z).symm
    (Complex.norm_mul_sin_arg z).symm (Complex.norm_mul_cos_arg w).symm
    (Complex.norm_mul_sin_arg w).symm
  have hQF := s07_hp_quot_polar (Real.rpow_pos_of_pos hr α) (Real.rpow_pos_of_pos hr' α) hs hs'
    (s07_powerMap_re α z) (s07_powerMap_im α z) (s07_powerMap_re α w) (s07_powerMap_im α w)
  rw [Real.log_rpow hr, Real.log_rpow hr',
    show (α * Real.log ‖z‖ - α * Real.log ‖w‖) / 2 = α * x by rw [hxdef]; ring] at hQF
  have hFz : 0 < (powerMap α z).im := by
    rw [s07_powerMap_im]; exact mul_pos (Real.rpow_pos_of_pos hr α) hs
  have hFw : 0 < (powerMap α w).im := by
    rw [s07_powerMap_im]; exact mul_pos (Real.rpow_pos_of_pos hr' α) hs'
  obtain ⟨hd0, hd⟩ := s07_hpDist_sinh_sq hzi hwi
  obtain ⟨hdF0, hdF⟩ := s07_hpDist_sinh_sq hFz hFw
  rw [hQ] at hd
  rw [hQF] at hdF
  have hd' : Real.sinh (hpDist z w / 2) ^ 2 = P * (Real.sinh x ^ 2 + q) := by
    rw [hd]; ring
  have hdF' : Real.sinh (hpDist (powerMap α z) (powerMap α w) / 2) ^ 2 =
      P * (Real.sinh (α * x) ^ 2 + q) := by
    rw [hdF]; ring
  constructor
  · have h1 : Real.sinh (α * x) ^ 2 ≤ Real.sinh (M * x) ^ 2 := by
      refine s07_sinh_sq_le_of_abs_le ?_
      rw [abs_mul, abs_mul, abs_of_pos hα, abs_of_pos (by linarith : 0 < M)]
      exact mul_le_mul_of_nonneg_right hαM (abs_nonneg x)
    have h2 := s07_sinh_sq_scale hM1 hP hq (by linarith) hd'
    have h3 : hpDist (powerMap α z) (powerMap α w) / 2 ≤ M * (hpDist z w / 2) := by
      refine s07_le_of_sinh_sq_le (by positivity) ?_
      rw [hdF']
      nlinarith
    linarith
  · have h1 : Real.sinh x ^ 2 ≤ Real.sinh (M * (α * x)) ^ 2 := by
      refine s07_sinh_sq_le_of_abs_le ?_
      rw [← mul_assoc, abs_mul (M * α), abs_of_pos (by linarith : 0 < M * α)]
      nlinarith [abs_nonneg x]
    have h2 := s07_sinh_sq_scale hM1 hP hq (by linarith) hdF'
    have h3 : hpDist z w / 2 ≤ M * (hpDist (powerMap α z) (powerMap α w) / 2) := by
      refine s07_le_of_sinh_sq_le (by positivity) ?_
      rw [hd']
      nlinarith
    linarith

theorem s07_powerMap_I_mul (α t : ℝ) (ht : 0 < t) : powerMap α (I * t) = I * ((t ^ α : ℝ) : ℂ) := by
  have hn : ‖I * (t : ℂ)‖ = t := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have harg : arg (I * (t : ℂ)) = π / 2 := by
    rw [Complex.arg_mul_real ht, Complex.arg_I]
  unfold powerMap
  rw [hn, harg]
  push_cast
  rw [Complex.exp_pi_div_two_mul_I, mul_comm]

theorem s07_hpDist_I_mul (t : ℝ) (ht : 1 ≤ t) : hpDist I (I * t) = Real.log t := by
  have ht0 : 0 < t := by linarith
  unfold hpDist
  have hn : ‖I - I * (t : ℂ)‖ ^ 2 = (t - 1) ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have him : (I * (t : ℂ)).im = t := by simp
  rw [hn, him, Complex.I_im]
  have : 1 + (t - 1) ^ 2 / (2 * 1 * t) = Real.cosh (Real.log t) := by
    rw [Real.cosh_log ht0]
    field_simp
    ring
  rw [this, Real.arcosh_cosh (Real.log_nonneg ht)]

theorem s07_hpKernel_I_mul (t : ℝ) (ht : 1 ≤ t) : hpKernel I (I * t) = 4 * t / (t + 1) ^ 2 := by
  have ht0 : 0 < t := by linarith
  unfold hpKernel
  rw [s07_hpDist_I_mul t ht, inv_pow]
  have hc : Real.cosh (Real.log t / 2) ^ 2 = (1 + Real.cosh (Real.log t)) / 2 := by
    have h2 := Real.cosh_two_mul (Real.log t / 2)
    have h3 := Real.cosh_sq (Real.log t / 2)
    rw [mul_div_cancel₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)] at h2
    linarith
  rw [hc, Real.cosh_log ht0]
  field_simp
  ring

/-- Example 7.12, `ex:power` (`sec07-transfer.tex:553`): `F_α(i) = i`, `d(i, iR) = log R` and
`d(F_α(i), F_α(iR)) = α log R` for `R > 1`. -/
theorem ex_power_dist (α : ℝ) (hα : 0 < α) (R : ℝ) (hR : 1 < R) :
    powerMap α I = I ∧ hpDist I (I * R) = Real.log R ∧
      hpDist (powerMap α I) (powerMap α (I * R)) = α * Real.log R := by
  have hR0 : 0 < R := by linarith
  have hI : powerMap α I = I := by
    have := s07_powerMap_I_mul α 1 one_pos
    simpa using this
  have hRα : 1 ≤ R ^ α := Real.one_le_rpow hR.le hα.le
  refine ⟨hI, s07_hpDist_I_mul R hR.le, ?_⟩
  rw [hI, s07_powerMap_I_mul α R hR0, s07_hpDist_I_mul _ hRα, Real.log_rpow hR0]

/-- (7.11) `eq:power-ratio` (`sec07-transfer.tex:556`):
`k_i(F_α(iR))/k_i(iR) = R^{α-1}(R+1)²/(R^α+1)²`. -/
theorem eq_power_ratio (α : ℝ) (hα : 0 < α) (R : ℝ) (hR : 1 < R) :
    hpKernel I (powerMap α (I * R)) / hpKernel I (I * R) =
      R ^ (α - 1) * (R + 1) ^ 2 / (R ^ α + 1) ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hRα : 1 ≤ R ^ α := Real.one_le_rpow hR.le hα.le
  rw [s07_powerMap_I_mul α R hR0, s07_hpKernel_I_mul _ hRα, s07_hpKernel_I_mul _ hR.le,
    Real.rpow_sub hR0, Real.rpow_one]
  have : 0 < R ^ α := by positivity
  field_simp

/-- The ratio of (7.11) is `R^{1-α} ((1 + R⁻¹)/(1 + R^{-α}))²`. -/
theorem s07_power_ratio_factor (α : ℝ) (hα : 0 < α) (R : ℝ) (hR : 1 < R) :
    hpKernel I (powerMap α (I * R)) / hpKernel I (I * R) =
      R ^ (1 - α) * ((1 + R⁻¹) / (1 + R ^ (-α))) ^ 2 := by
  have hR0 : 0 < R := by linarith
  rw [eq_power_ratio α hα R hR, Real.rpow_sub hR0, Real.rpow_sub hR0, Real.rpow_one,
    Real.rpow_neg hR0.le]
  have : 0 < R ^ α := by positivity
  field_simp

theorem s07_power_ratio_q_tendsto (α : ℝ) (hα : 0 < α) :
    Tendsto (fun R : ℝ => ((1 + R⁻¹) / (1 + R ^ (-α))) ^ 2) atTop (𝓝 1) := by
  have h1 : Tendsto (fun R : ℝ => 1 + R⁻¹) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add tendsto_inv_atTop_zero
  have h2 : Tendsto (fun R : ℝ => 1 + R ^ (-α)) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_rpow_neg_atTop hα)
  have := (h1.div h2 (by norm_num)).pow 2
  simpa using this

/-- (7.11) `eq:power-ratio` (`sec07-transfer.tex:557`): the ratio is `∼ R^{1-α}` as `R → ∞`. -/
theorem eq_power_ratio_asymp (α : ℝ) (hα : 0 < α) :
    Tendsto (fun R : ℝ => hpKernel I (powerMap α (I * R)) / hpKernel I (I * R) / R ^ (1 - α))
      atTop (𝓝 1) := by
  refine (s07_power_ratio_q_tendsto α hα).congr' ?_
  filter_upwards [eventually_gt_atTop 1] with R hR
  have hR0 : 0 < R := by linarith
  rw [s07_power_ratio_factor α hα R hR]
  have : 0 < R ^ (1 - α) := by positivity
  field_simp

/-- Example 7.12 (`sec07-transfer.tex:560`): the ratio tends to `0` if `α > 1`. -/
theorem ex_power_ratio_zero (α : ℝ) (hα : 1 < α) :
    Tendsto (fun R : ℝ => hpKernel I (powerMap α (I * R)) / hpKernel I (I * R)) atTop
      (𝓝 0) := by
  have hα0 : 0 < α := by linarith
  have h1 : Tendsto (fun R : ℝ => R ^ (1 - α)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (show 0 < α - 1 by linarith)
    simpa [neg_sub] using this
  have := h1.mul (s07_power_ratio_q_tendsto α hα0)
  rw [zero_mul] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with R hR
  rw [s07_power_ratio_factor α hα0 R hR]

/-- Example 7.12 (`sec07-transfer.tex:560`): the ratio tends to `∞` if `α < 1`. -/
theorem ex_power_ratio_top (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    Tendsto (fun R : ℝ => hpKernel I (powerMap α (I * R)) / hpKernel I (I * R)) atTop
      atTop := by
  have h1 : Tendsto (fun R : ℝ => R ^ (1 - α)) atTop atTop :=
    tendsto_rpow_atTop (by linarith)
  have := h1.atTop_mul_pos one_pos (s07_power_ratio_q_tendsto α hα)
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with R hR
  rw [s07_power_ratio_factor α hα R hR]

end EpsteinVMO
