import EpsteinVMO.Defs
import TakhtajanTeo.Ch2.S2_Remark22

/-!
# §2 Preliminaries (statements)

Source: `sec02-prelim.tex` of the paper (folder `正式稿-Epstein-VMO`).  The core objects are in
`EpsteinVMO.Defs`; this file states every lemma, proposition and displayed fact of §2 that is
used later, plus Lemma 3.4 (`lem:borel-label`, `sec03-coarse.tex:153`), which §2 already uses to
define labels.

## Conventions used here

* "`Ω ⊂ ℂ` is a simply connected proper subdomain" is the hypothesis
  `IsConformalOnto f unitDisc Ω` for a given Riemann map `f` (Liouville excludes `Ω = ℂ`).
* `d(w) = dist(w, ∂Ω)` is `infDist w Ωᶜ`.
* `S(f⁻¹)` on `Ω` is `schwarzian (Function.invFunOn f unitDisc)`.
* "`∞ ∈ Γ`" (Convention 2.1) is `IsJordanPair Ω Ωs`; "`Γ` is not a circle" is `¬ IsLinePair Ω Ωs`.
* Distances to sets in `ℍ³` are `hdistSet` / `hdistSets` (an `sInf` of an image, so no junk `0`
  from a bounded `⨅` in `ℝ`).
* Tangent vectors of `ℍ³ ⊆ ℂ × ℝ` at `q` are measured with `hypInner q`
  (`(|dW|² + dξ²)/ξ²`).
* The welding of Theorem 2.13 (Shen–Wei) is `IsDiskWelding` (`h = f⁻¹ ∘ g` on `∂𝔻`, via boundary
  limits); `IsCircleHomeo` (orientation-preserving circle homeomorphism, via a lift); strong
  quasisymmetry (with data `δf`) and strong symmetry are `IsStronglyQSWith`, `IsStronglyQS` and
  `IsStronglySymmetric`, with arc length `circleLen` (Lebesgue measure of the angle set, no
  `Measure.map`).  These are the project's only definitions of these notions.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace EpsteinVMO

open LiZhongQC

/-! ## Section-local definitions -/

/-- The hyperbolic distance `d(q, S) = inf_{p ∈ S} d(q, p)` from a point of `ℍ³` to a set
(`sInf` of the image; `0` for `S = ∅`). -/
def hdistSet (q : ℂ × ℝ) (S : Set (ℂ × ℝ)) : ℝ := sInf (hdist q '' S)

/-- The hyperbolic distance `d(S, T) = inf_{p ∈ S, p' ∈ T} d(p, p')` between two sets of `ℍ³`. -/
def hdistSets (S T : Set (ℂ × ℝ)) : ℝ := sInf (image2 hdist S T)

/-- The hyperbolic inner product `⟨a, b⟩_q = (Re(a₁ b̄₁) + a₂ b₂)/ξ²` of two tangent vectors
`a, b ∈ ℂ × ℝ` at `q = (W, ξ) ∈ ℍ³`. -/
def hypInner (q a b : ℂ × ℝ) : ℝ := ((a.1 * conj b.1).re + a.2 * b.2) / q.2 ^ 2

/-- The hyperbolic convex hull `CH(Γ)` of a closed set `Γ ∪ {∞}` with `∞ ∈ Γ`: the intersection
of the closed half-spaces whose closure at infinity contains `Γ`.  Their complements are the open
half-spaces over the open round disks of `ℂ̂` missing `Γ ∪ {∞}`, i.e. over open Euclidean disks
`D(c, r)` and open half-planes `{Im(a z + b) > 0}` disjoint from `Γ`. -/
def hypHull (Γ : Set ℂ) : Set (ℂ × ℝ) :=
  {q | q ∈ UHS ∧
    (∀ (c : ℂ) (r : ℝ), 0 < r → Disjoint (ball c r) Γ → r ^ 2 ≤ ‖q.1 - c‖ ^ 2 + q.2 ^ 2) ∧
    ∀ a b : ℂ, a ≠ 0 → Disjoint {z : ℂ | 0 < (a * z + b).im} Γ → (a * q.1 + b).im ≤ 0}

/-- Arc length `|E|` of a set `E ⊆ ∂𝔻`: the Lebesgue measure of `{θ ∈ [0, 2π) : e^{iθ} ∈ E}`. -/
def circleLen (E : Set ℂ) : ℝ≥0∞ :=
  volume {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ Complex.exp (θ * Complex.I) ∈ E}

/-- The closed arc `{e^{iθ} : a ≤ θ ≤ b}` of `∂𝔻`. -/
def circleArc (a b : ℝ) : Set ℂ := (fun θ : ℝ => Complex.exp (θ * Complex.I)) '' Icc a b

/-- `h` restricts to an orientation-preserving homeomorphism of `∂𝔻`: it has a lift
`h(e^{iθ}) = e^{iH(θ)}` with `H` continuous, strictly increasing, `H(θ + 2π) = H(θ) + 2π`. -/
def IsCircleHomeo (h : ℂ → ℂ) : Prop :=
  ∃ H : ℝ → ℝ, StrictMono H ∧ Continuous H ∧ (∀ θ : ℝ, H (θ + 2 * π) = H θ + 2 * π) ∧
    ∀ θ : ℝ, h (Complex.exp (θ * Complex.I)) = Complex.exp (H θ * Complex.I)

/-- `h` is the conformal welding `h = f⁻¹ ∘ g|_{∂𝔻}` of a bounded curve: `f : 𝔻 → Ω` and
`g : 𝔻* → Ωs` are conformal, `g(∞) = ∞`, `h` maps `∂𝔻` to itself, and the boundary values of `f`
at `h(ζ)` and of `g` at `ζ` agree.  Only the values of `h` on `∂𝔻` matter. -/
def IsDiskWelding (Ω Ωs : Set ℂ) (f g h : ℂ → ℂ) : Prop :=
  IsConformalOnto f unitDisc Ω ∧ IsConformalOnto g unitDiscExterior Ωs ∧
    Tendsto g (cocompact ℂ) (cocompact ℂ) ∧ MapsTo h (sphere 0 1) (sphere 0 1) ∧
    ∀ ζ ∈ sphere (0 : ℂ) 1, ∃ x : ℂ, Tendsto f (𝓝[unitDisc] (h ζ)) (𝓝 x) ∧
      Tendsto g (𝓝[unitDiscExterior] ζ) (𝓝 x)

/-- `h` is a strongly quasisymmetric homeomorphism of `∂𝔻` with modulus `δf` (the strong
quasisymmetry data, `sec02-prelim.tex:586`): `h` is an orientation-preserving circle homeomorphism
and for every `ε > 0`, `δf ε > 0` and `|E| ≤ δf(ε) |I|` implies `|h(E)| ≤ ε |h(I)|` for every arc
`I` and measurable `E ⊆ I`. -/
def IsStronglyQSWith (h : ℂ → ℂ) (δf : ℝ → ℝ) : Prop :=
  IsCircleHomeo h ∧ ∀ ε : ℝ, 0 < ε → 0 < δf ε ∧
    ∀ a b : ℝ, a < b → b - a ≤ 2 * π → ∀ E ⊆ circleArc a b, MeasurableSet E →
      circleLen E ≤ ENNReal.ofReal (δf ε) * circleLen (circleArc a b) →
        circleLen (h '' E) ≤ ENNReal.ofReal ε * circleLen (h '' circleArc a b)

/-- `h` is a strongly quasisymmetric homeomorphism of `∂𝔻`. -/
def IsStronglyQS (h : ℂ → ℂ) : Prop := ∃ δf : ℝ → ℝ, IsStronglyQSWith h δf

/-- `h` is strongly symmetric: an orientation-preserving circle homeomorphism, absolutely
continuous, with `log h' ∈ VMO(∂𝔻)` (`sec02-prelim.tex:589`).  On a lift `H`: `H = H(0) + ∫ u`,
`u > 0` a.e. (so `log 0 = 0` cannot hide a degenerate case), `log u` locally integrable, and its
mean oscillation `(1/|I|) ∫_I |log u - (log u)_I|` tends to `0` with the length of `I`. -/
def IsStronglySymmetric (h : ℂ → ℂ) : Prop :=
  ∃ H u : ℝ → ℝ, StrictMono H ∧ Continuous H ∧ (∀ θ : ℝ, H (θ + 2 * π) = H θ + 2 * π) ∧
    (∀ θ : ℝ, h (Complex.exp (θ * Complex.I)) = Complex.exp (H θ * Complex.I)) ∧
    (∀ a b : ℝ, IntegrableOn u (Icc a b)) ∧
    (∀ θ : ℝ, H θ = H 0 + ∫ t in (0 : ℝ)..θ, u t) ∧ (∀ᵐ t, 0 < u t) ∧
    (∀ a b : ℝ, IntegrableOn (fun t => Real.log (u t)) (Icc a b)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a < b → b - a ≤ δ →
      (∫ t in a..b, |Real.log (u t) - (∫ s in a..b, Real.log (u s)) / (b - a)|) / (b - a) ≤ ε

/-! ## §2.2 The Poincaré metric and the Schwarzian -/

/-! ### Hyperbolic distances: symmetry and triangle inequalities -/

/-- `arcosh (1 + |z - w|² / (2 Im z Im w))` is the distance of Mathlib's upper half-plane `ℍ`. -/
theorem s02_arcosh_uhp {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    Real.arcosh (1 + ‖z - w‖ ^ 2 / (2 * z.im * w.im)) =
      dist (UpperHalfPlane.mk z hz) (UpperHalfPlane.mk w hw) := by
  have h := UpperHalfPlane.cosh_dist (UpperHalfPlane.mk z hz) (UpperHalfPlane.mk w hw)
  rw [UpperHalfPlane.coe_mk, UpperHalfPlane.coe_mk, UpperHalfPlane.mk_im, UpperHalfPlane.mk_im,
    Complex.dist_eq] at h
  rw [← h, Real.arcosh_cosh dist_nonneg]

/-- `cosh d(p, q)` in `ℍ³` is symmetric. -/
theorem s02_coshDist_comm (p q : ℂ × ℝ) : coshDist p q = coshDist q p := by
  unfold coshDist
  rw [norm_sub_rev]
  ring

/-- The hyperbolic distance of `ℍ³` is symmetric. -/
theorem s02_hdist_comm (p q : ℂ × ℝ) : hdist p q = hdist q p := by
  unfold hdist
  rw [s02_coshDist_comm]

/-- `(z, t) ↦ (e (z - x₀), t)` with `|e| = 1` preserves `cosh d` in `ℍ³`. -/
theorem s02_coshDist_isometry {e x₀ : ℂ} (he : ‖e‖ = 1) (p q : ℂ × ℝ) :
    coshDist (e * (p.1 - x₀), p.2) (e * (q.1 - x₀), q.2) = coshDist p q := by
  unfold coshDist
  rw [← mul_sub, norm_mul, he, one_mul, sub_sub_sub_cancel_right]

/-- Folding `ℍ³` onto the vertical half-plane over `ℝ`: `(z, t) ↦ Re z + i √(t² + (Im z)²)` does not
increase the distance to points over `ℝ`. -/
theorem s02_coshDist_fold {a b : ℂ × ℝ} (ha : 0 < a.2) (hb : 0 < b.2) (hai : a.1.im = 0) :
    1 + ‖(⟨a.1.re, √(a.2 ^ 2 + a.1.im ^ 2)⟩ : ℂ) - ⟨b.1.re, √(b.2 ^ 2 + b.1.im ^ 2)⟩‖ ^ 2 /
      (2 * √(a.2 ^ 2 + a.1.im ^ 2) * √(b.2 ^ 2 + b.1.im ^ 2)) ≤ coshDist a b := by
  have hsa : √(a.2 ^ 2 + a.1.im ^ 2) = a.2 := by
    rw [hai, zero_pow two_ne_zero, add_zero, Real.sqrt_sq ha.le]
  set σ := √(b.2 ^ 2 + b.1.im ^ 2) with hσdef
  have hσ2 : σ ^ 2 = b.2 ^ 2 + b.1.im ^ 2 := Real.sq_sqrt (by positivity)
  have hσ : b.2 ≤ σ :=
    le_trans (le_abs_self _) (Real.abs_le_sqrt (by nlinarith [sq_nonneg b.1.im]))
  have hσpos : 0 < σ := lt_of_lt_of_le hb hσ
  have hn1 : ‖a.1 - b.1‖ ^ 2 = (a.1.re - b.1.re) ^ 2 + b.1.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [hai]
    ring
  have hn2 : ‖(⟨a.1.re, a.2⟩ : ℂ) - ⟨b.1.re, σ⟩‖ ^ 2 = (a.1.re - b.1.re) ^ 2 + (a.2 - σ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [hsa, hn2]
  unfold coshDist
  rw [hn1]
  set N := (a.1.re - b.1.re) ^ 2 + a.2 ^ 2 + b.2 ^ 2 + b.1.im ^ 2
  have hA : (a.1.re - b.1.re) ^ 2 + (a.2 - σ) ^ 2 = N - 2 * a.2 * σ := by
    linear_combination hσ2
  have hB : (a.1.re - b.1.re) ^ 2 + b.1.im ^ 2 + (a.2 - b.2) ^ 2 = N - 2 * a.2 * b.2 := by ring
  have hN : 0 ≤ N := by positivity
  rw [hA, hB]
  have key : (N - 2 * a.2 * σ) / (2 * a.2 * σ) ≤ (N - 2 * a.2 * b.2) / (2 * a.2 * b.2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg ha.le hN) (sub_nonneg.2 hσ)]
  linarith

/-- The triangle inequality in `ℍ³` when the first and last points lie over `ℝ`. -/
theorem s02_hdist_triangle_real {p q r : ℂ × ℝ} (hp : 0 < p.2) (hq : 0 < q.2) (hr : 0 < r.2)
    (hpi : p.1.im = 0) (hri : r.1.im = 0) : hdist p r ≤ hdist p q + hdist q r := by
  have hZ : ∀ c : ℂ × ℝ, 0 < c.2 → 0 < (⟨c.1.re, √(c.2 ^ 2 + c.1.im ^ 2)⟩ : ℂ).im :=
    fun c hc => Real.sqrt_pos.2 (by positivity)
  have hfold : ∀ a b : ℂ × ℝ, ∀ (ha : 0 < a.2) (hb : 0 < b.2), a.1.im = 0 →
      dist (UpperHalfPlane.mk _ (hZ a ha)) (UpperHalfPlane.mk _ (hZ b hb)) ≤ hdist a b := by
    intro a b ha hb hai
    rw [← s02_arcosh_uhp]
    unfold hdist
    have h1 := hZ a ha
    have h2 := hZ b hb
    have hpos : 0 < 1 + ‖(⟨a.1.re, √(a.2 ^ 2 + a.1.im ^ 2)⟩ : ℂ) -
        ⟨b.1.re, √(b.2 ^ 2 + b.1.im ^ 2)⟩‖ ^ 2 /
        (2 * (⟨a.1.re, √(a.2 ^ 2 + a.1.im ^ 2)⟩ : ℂ).im *
          (⟨b.1.re, √(b.2 ^ 2 + b.1.im ^ 2)⟩ : ℂ).im) := by
      have := div_nonneg (sq_nonneg ‖(⟨a.1.re, √(a.2 ^ 2 + a.1.im ^ 2)⟩ : ℂ) -
        ⟨b.1.re, √(b.2 ^ 2 + b.1.im ^ 2)⟩‖) (mul_pos (mul_pos two_pos h1) h2).le
      linarith
    have hfo := s02_coshDist_fold ha hb hai
    exact (Real.arcosh_le_arcosh hpos (by linarith)).2 hfo
  have hpr : hdist p r =
      dist (UpperHalfPlane.mk _ (hZ p hp)) (UpperHalfPlane.mk _ (hZ r hr)) := by
    rw [← s02_arcosh_uhp]
    unfold hdist
    congr 1
    have hsp : √(p.2 ^ 2 + p.1.im ^ 2) = p.2 := by
      rw [hpi, zero_pow two_ne_zero, add_zero, Real.sqrt_sq hp.le]
    have hsr : √(r.2 ^ 2 + r.1.im ^ 2) = r.2 := by
      rw [hri, zero_pow two_ne_zero, add_zero, Real.sqrt_sq hr.le]
    have hn1 : ‖p.1 - r.1‖ ^ 2 = (p.1.re - r.1.re) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [hpi, hri]
      ring
    show coshDist p r = 1 + ‖(⟨p.1.re, √(p.2 ^ 2 + p.1.im ^ 2)⟩ : ℂ) -
        ⟨r.1.re, √(r.2 ^ 2 + r.1.im ^ 2)⟩‖ ^ 2 /
        (2 * √(p.2 ^ 2 + p.1.im ^ 2) * √(r.2 ^ 2 + r.1.im ^ 2))
    rw [hsp, hsr, Complex.sq_norm, Complex.normSq_apply]
    unfold coshDist
    rw [hn1]
    simp
    ring
  rw [hpr, s02_hdist_comm q r]
  calc _ ≤ dist (UpperHalfPlane.mk _ (hZ p hp)) (UpperHalfPlane.mk _ (hZ q hq)) +
        dist (UpperHalfPlane.mk _ (hZ r hr)) (UpperHalfPlane.mk _ (hZ q hq)) := by
          rw [dist_comm (UpperHalfPlane.mk _ (hZ r hr))]
          exact dist_triangle _ _ _
    _ ≤ hdist p q + hdist r q := add_le_add (hfold p q hp hq hpi) (hfold r q hr hq hri)

/-- The triangle inequality for the hyperbolic distance of `ℍ³`. -/
theorem s02_hdist_triangle {p q r : ℂ × ℝ} (hp : p ∈ UHS) (hq : q ∈ UHS) (hr : r ∈ UHS) :
    hdist p r ≤ hdist p q + hdist q r := by
  set d := r.1 - p.1
  set e : ℂ := Complex.exp (↑(-Complex.arg d) * I)
  have he : ‖e‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hed : e * d = (‖d‖ : ℂ) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I d]
    rw [mul_left_comm, ← Complex.exp_add,
      show (↑(-Complex.arg d) * I + ↑(Complex.arg d) * I : ℂ) = 0 by push_cast; ring,
      Complex.exp_zero, mul_one]
  have hT : ∀ a b : ℂ × ℝ, hdist (e * (a.1 - p.1), a.2) (e * (b.1 - p.1), b.2) = hdist a b := by
    intro a b
    unfold hdist
    rw [s02_coshDist_isometry he]
  rw [← hT p r, ← hT p q, ← hT q r]
  refine s02_hdist_triangle_real hp hq hr ?_ ?_
  · simp
  · show (e * d).im = 0
    rw [hed, Complex.ofReal_im]

/-- `Im` of the Cayley map `a ↦ i(1 + a)/(1 - a)`: `(1 - |a|²)/|1 - a|²`. -/
theorem s02_cayley_im (a : ℂ) :
    (I * (1 + a) / (1 - a)).im = (1 - normSq a) / normSq (1 - a) := by
  rw [Complex.div_im]
  simp [Complex.normSq_apply]
  ring

/-- The Cayley map `a ↦ i(1 + a)/(1 - a)` sends `𝔻` into the upper half-plane. -/
theorem s02_cayley_im_pos {a : ℂ} (ha : a ∈ unitDisc) : 0 < (I * (1 + a) / (1 - a)).im := by
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have hn : normSq a < 1 := normSq_lt_one_iff.mpr ha1
  have hA : (1 : ℂ) - a ≠ 0 := by
    intro h
    have : a = 1 := (sub_eq_zero.mp h).symm
    rw [this, norm_one] at ha1
    exact lt_irrefl _ ha1
  rw [s02_cayley_im]
  exact div_pos (by linarith) (normSq_pos.mpr hA)

/-- The Cayley map carries `cosh d_𝔻` to `cosh d_ℍ`. -/
theorem s02_diskCoshDist_cayley {a z : ℂ} (ha : a ∈ unitDisc) (hz : z ∈ unitDisc) :
    diskCoshDist a z = 1 + ‖I * (1 + a) / (1 - a) - I * (1 + z) / (1 - z)‖ ^ 2 /
      (2 * (I * (1 + a) / (1 - a)).im * (I * (1 + z) / (1 - z)).im) := by
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hne : ∀ w : ℂ, ‖w‖ < 1 → (1 : ℂ) - w ≠ 0 := by
    intro w hw h
    have : w = 1 := (sub_eq_zero.mp h).symm
    rw [this, norm_one] at hw
    exact lt_irrefl _ hw
  have hA := hne a ha1
  have hZ := hne z hz1
  have hdiff : I * (1 + a) / (1 - a) - I * (1 + z) / (1 - z) =
      I * (2 * (a - z)) / ((1 - a) * (1 - z)) := by
    rw [div_sub_div _ _ hA hZ]
    ring
  have hna : normSq a < 1 := normSq_lt_one_iff.mpr ha1
  have hnz : normSq z < 1 := normSq_lt_one_iff.mpr hz1
  have hNA : normSq (1 - a) ≠ 0 := (normSq_pos.mpr hA).ne'
  have hNZ : normSq (1 - z) ≠ 0 := (normSq_pos.mpr hZ).ne'
  rw [hdiff, s02_cayley_im, s02_cayley_im, Complex.sq_norm, normSq_div, normSq_mul, normSq_mul,
    normSq_mul, normSq_I]
  unfold diskCoshDist
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  have h4 : normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq_apply]
  rw [h4]
  have h1a : 1 - normSq a ≠ 0 := by linarith
  have h1z : 1 - normSq z ≠ 0 := by linarith
  field_simp
  ring

/-- The Cayley map is an isometry from `(𝔻, d_𝔻)` onto Mathlib's `ℍ`. -/
theorem s02_diskDist_cayley {a z : ℂ} (ha : a ∈ unitDisc) (hz : z ∈ unitDisc) :
    diskDist a z = dist (UpperHalfPlane.mk _ (s02_cayley_im_pos ha))
      (UpperHalfPlane.mk _ (s02_cayley_im_pos hz)) := by
  rw [← s02_arcosh_uhp]
  unfold diskDist
  rw [s02_diskCoshDist_cayley ha hz]

/-- The Poincaré distance of `𝔻` is nonnegative. -/
theorem s02_diskDist_nonneg {a z : ℂ} (ha : a ∈ unitDisc) (hz : z ∈ unitDisc) :
    0 ≤ diskDist a z := by
  rw [s02_diskDist_cayley ha hz]
  exact dist_nonneg

/-- The Poincaré distance of `𝔻` is symmetric. -/
theorem s02_diskDist_comm {a z : ℂ} (ha : a ∈ unitDisc) (hz : z ∈ unitDisc) :
    diskDist a z = diskDist z a := by
  rw [s02_diskDist_cayley ha hz, s02_diskDist_cayley hz ha, dist_comm]

/-- The triangle inequality for the Poincaré distance of `𝔻`. -/
theorem s02_diskDist_triangle {a b c : ℂ} (ha : a ∈ unitDisc) (hb : b ∈ unitDisc)
    (hc : c ∈ unitDisc) : diskDist a c ≤ diskDist a b + diskDist b c := by
  rw [s02_diskDist_cayley ha hc, s02_diskDist_cayley ha hb, s02_diskDist_cayley hb hc]
  exact dist_triangle _ _ _

/-! ### The Poincaré density -/

/-- Schwarz–Pick at the origin: a holomorphic self-map `k` of `𝔻` has `|k'(0)| ≤ 1 - |k(0)|²`. -/
theorem s02_schwarz_pick_zero {k : ℂ → ℂ} (hk : DifferentiableOn ℂ k unitDisc)
    (hmaps : MapsTo k unitDisc unitDisc) : ‖deriv k 0‖ ≤ 1 - ‖k 0‖ ^ 2 := by
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  set c := k 0 with hcdef
  have hc : ‖c‖ < 1 := mem_ball_zero_iff.mp (hmaps h0)
  have hd : DifferentiableOn ℂ (blaschke c ∘ k) (ball 0 1) :=
    (differentiableOn_blaschke hc).comp hk hmaps
  have hm : MapsTo (blaschke c ∘ k) (ball 0 1) (closedBall ((blaschke c ∘ k) 0) 1) := by
    intro ζ hζ
    have h00 : (blaschke c ∘ k) 0 = 0 := by simp [Function.comp, ← hcdef]
    rw [h00, mem_closedBall_zero_iff]
    exact (blaschke_mem_unitDisc hc (mem_ball_zero_iff.mp (hmaps hζ))).le
  have hS := Complex.norm_deriv_le_one_of_mapsTo_ball hd hm one_pos
  have hkd : DifferentiableAt ℂ k 0 := hk.differentiableAt (isOpen_ball.mem_nhds h0)
  have hB : HasDerivAt (blaschke c) ((1 - c * conj c) / (1 - conj c * c) ^ 2) (k 0) :=
    hasDerivAt_blaschke hc hc
  have hchain := (hB.comp 0 hkd.hasDerivAt).deriv
  have hr : (0 : ℝ) < 1 - ‖c‖ ^ 2 := by nlinarith [norm_nonneg c]
  have e1 : c * conj c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e2 : conj c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by rw [mul_comm, e1]
  have hrc : (1 : ℂ) - ((‖c‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have e3 : (1 - c * conj c) / (1 - conj c * c) ^ 2 = (((1 - ‖c‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
    have e4 : (((1 - ‖c‖ ^ 2)⁻¹ : ℝ) : ℂ) = (1 - ((‖c‖ ^ 2 : ℝ) : ℂ))⁻¹ := by push_cast; ring
    rw [e1, e2, e4]
    generalize ((‖c‖ ^ 2 : ℝ) : ℂ) = t at hrc ⊢
    rw [pow_two, ← div_div, div_self hrc, one_div]
  rw [hchain, e3, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hr.le),
    inv_mul_le_iff₀ hr, mul_one] at hS
  exact hS

/-- The supremum defining `poincareDensity Ω (f z)` is attained, at `(1 - |z|²) |f'(z)|`. -/
theorem s02_poincareDensity_isGreatest {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {z : ℂ} (hz : z ∈ unitDisc) :
    IsGreatest {r : ℝ | ∃ g : ℂ → ℂ, DifferentiableOn ℂ g unitDisc ∧ MapsTo g unitDisc Ω ∧
      g 0 = f z ∧ r = ‖deriv g 0‖} ((1 - ‖z‖ ^ 2) * ‖deriv f z‖) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hfd : DifferentiableAt ℂ f z := hf.1.differentiableAt (isOpen_ball.mem_nhds hz)
  have hr : (0 : ℝ) ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  constructor
  · have hnz : ‖-z‖ < 1 := by simpa using hz1
    have hmaps : MapsTo (blaschke (-z)) unitDisc unitDisc := fun ζ hζ =>
      mem_ball_zero_iff.mpr (blaschke_mem_unitDisc hnz (mem_ball_zero_iff.mp hζ))
    refine ⟨f ∘ blaschke (-z), hf.1.comp (differentiableOn_blaschke hnz) hmaps, ?_, ?_, ?_⟩
    · intro ζ hζ
      rw [← hf.2.2]
      exact mem_image_of_mem f (hmaps hζ)
    · simp
    · have hB := hasDerivAt_blaschke hnz (by simp : ‖(0 : ℂ)‖ < 1)
      have hfd' : HasDerivAt f (deriv f (blaschke (-z) 0)) (blaschke (-z) 0) := by
        rw [blaschke_neg_zero]
        exact hfd.hasDerivAt
      rw [(hfd'.comp 0 hB).deriv, blaschke_neg_zero]
      have e : (1 - -z * conj (-z)) / (1 - conj (-z) * 0) ^ 2 = (((1 - ‖z‖ ^ 2 : ℝ)) : ℂ) := by
        rw [map_neg, neg_mul_neg, mul_zero, sub_zero, one_pow, div_one, Complex.mul_conj,
          Complex.normSq_eq_norm_sq]
        push_cast
        ring
      rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr, mul_comm]
  · rintro r ⟨g, hg, hgm, hg0, rfl⟩
    have hψ : IsConformalOnto (Function.invFunOn f unitDisc) Ω unitDisc := hf.symm isOpen_ball
    have hk : DifferentiableOn ℂ (Function.invFunOn f unitDisc ∘ g) unitDisc :=
      hψ.1.comp hg hgm
    have hkm : MapsTo (Function.invFunOn f unitDisc ∘ g) unitDisc unitDisc := by
      intro ζ hζ
      have hmem := mem_image_of_mem (Function.invFunOn f unitDisc) (hgm hζ)
      rw [hψ.2.2] at hmem
      exact hmem
    have hk0 : (Function.invFunOn f unitDisc ∘ g) 0 = z := by
      show Function.invFunOn f unitDisc (g 0) = z
      rw [hg0]
      exact hf.2.1.leftInvOn_invFunOn hz
    have hpick := s02_schwarz_pick_zero hk hkm
    rw [hk0] at hpick
    have heq : g =ᶠ[𝓝 0] f ∘ (Function.invFunOn f unitDisc ∘ g) := by
      filter_upwards [isOpen_ball.mem_nhds h0] with ζ hζ
      have hmem : g ζ ∈ f '' unitDisc := by
        rw [hf.2.2]
        exact hgm hζ
      exact (Function.invFunOn_eq hmem).symm
    have hkd : DifferentiableAt ℂ (Function.invFunOn f unitDisc ∘ g) 0 :=
      hk.differentiableAt (isOpen_ball.mem_nhds h0)
    have hfd' : HasDerivAt f (deriv f ((Function.invFunOn f unitDisc ∘ g) 0))
        ((Function.invFunOn f unitDisc ∘ g) 0) := by
      rw [hk0]
      exact hfd.hasDerivAt
    rw [heq.deriv_eq, (hfd'.comp 0 hkd.hasDerivAt).deriv, hk0, norm_mul, mul_comm (1 - _)]
    exact mul_le_mul_of_nonneg_left hpick (norm_nonneg _)

/-! ### Disc automorphisms and the pulled-back quantities -/

/-- `cosh d_𝔻` is invariant under the Blaschke factor `M_b`. -/
theorem s02_diskCoshDist_blaschke {b w u : ℂ} (hb : ‖b‖ < 1) (hw : ‖w‖ < 1) (hu : ‖u‖ < 1) :
    diskCoshDist (blaschke b w) (blaschke b u) = diskCoshDist w u := by
  have hDw := blaschke_den_ne_zero hb hw
  have hDu := blaschke_den_ne_zero hb hu
  have hdiff : blaschke b w - blaschke b u =
      (w - u) * (1 - b * conj b) / ((1 - conj b * w) * (1 - conj b * u)) := by
    simp only [blaschke]
    rw [div_sub_div _ _ hDw hDu]
    ring
  have hb2 : normSq (1 - b * conj b) = (1 - normSq b) ^ 2 := by
    rw [Complex.mul_conj, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.normSq_ofReal]
    ring
  have hnb : normSq b < 1 := normSq_lt_one_iff.mpr hb
  have hnw : normSq w < 1 := normSq_lt_one_iff.mpr hw
  have hnu : normSq u < 1 := normSq_lt_one_iff.mpr hu
  have hNw : normSq (1 - conj b * w) ≠ 0 := (normSq_pos.mpr hDw).ne'
  have hNu : normSq (1 - conj b * u) ≠ 0 := (normSq_pos.mpr hDu).ne'
  have h1b : 1 - normSq b ≠ 0 := by linarith
  have h1w : 1 - normSq w ≠ 0 := by linarith
  have h1u : 1 - normSq u ≠ 0 := by linarith
  unfold diskCoshDist
  rw [hdiff]
  simp only [Complex.sq_norm]
  rw [one_sub_normSq_blaschke hb hw, one_sub_normSq_blaschke hb hu, normSq_div, normSq_mul,
    normSq_mul, hb2]
  generalize normSq (1 - conj b * w) = A at hNw ⊢
  generalize normSq (1 - conj b * u) = B at hNu ⊢
  field_simp

/-- `cosh d_𝔻` is invariant under rotations. -/
theorem s02_diskCoshDist_rotate {c w u : ℂ} (hc : ‖c‖ = 1) :
    diskCoshDist (c * w) (c * u) = diskCoshDist w u := by
  unfold diskCoshDist
  rw [← mul_sub, norm_mul, norm_mul, norm_mul, hc, one_mul, one_mul, one_mul]

/-- Two Riemann maps of `Ω` differ by a disc automorphism: `F = f ∘ (c M_b)` on `𝔻`. -/
theorem s02_riemannMap_factor {Ω : Set ℂ} {f F : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (hF : IsConformalOnto F unitDisc Ω) :
    ∃ c b : ℂ, ‖c‖ = 1 ∧ ‖b‖ < 1 ∧ ∀ ζ ∈ unitDisc,
      Function.invFunOn f unitDisc (F ζ) = c * blaschke b ζ ∧ F ζ = f (c * blaschke b ζ) := by
  have hψ : IsConformalOnto (Function.invFunOn f unitDisc) Ω unitDisc := hf.symm isOpen_ball
  have hFm : MapsTo F unitDisc Ω := by
    intro ζ hζ
    rw [← hF.2.2]
    exact mem_image_of_mem F hζ
  have hh : IsConformalOnto (Function.invFunOn f unitDisc ∘ F) unitDisc unitDisc := by
    refine ⟨hψ.1.comp hF.1 hFm, hψ.2.1.comp hF.2.1 hFm, ?_⟩
    rw [Set.image_comp, hF.2.2, hψ.2.2]
  obtain ⟨c, b, hc, hb, heq⟩ := exists_rotation_blaschke_of_isConformalOnto_unitDisc hh
  refine ⟨c, b, hc, hb, fun ζ hζ => ⟨heq hζ, ?_⟩⟩
  have hmem : F ζ ∈ f '' unitDisc := by
    rw [hf.2.2]
    exact hFm hζ
  have h1 := heq hζ
  simp only [Function.comp_apply] at h1
  rw [← h1]
  exact (Function.invFunOn_eq hmem).symm

/-- The Schwarzian of a Riemann map, read through another one:
`|S F(z')| (1-|z'|²)² = |S f(z)| (1-|z|²)²` when `F(z') = f(z)`. -/
theorem s02_schwarzian_factor {Ω : Set ℂ} {f F : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (hF : IsConformalOnto F unitDisc Ω) {z z' : ℂ} (hz : z ∈ unitDisc) (hz' : z' ∈ unitDisc)
    (hFz : F z' = f z) :
    ‖schwarzian F z'‖ * (1 - ‖z'‖ ^ 2) ^ 2 = ‖schwarzian f z‖ * (1 - ‖z‖ ^ 2) ^ 2 := by
  obtain ⟨c, b, hc, hb, hcb⟩ := s02_riemannMap_factor hf hF
  have hz1' : ‖z'‖ < 1 := mem_ball_zero_iff.mp hz'
  have hM0 : c * blaschke b z' = z := by
    rw [← (hcb z' hz').1, hFz]
    exact hf.2.1.leftInvOn_invFunOn hz
  have hDz := blaschke_den_ne_zero hb hz1'
  -- the disc automorphism as a fractional linear map
  set M : ℂ → ℂ := fun w => (c * w + -(c * b)) / (-conj b * w + 1) with hMdef
  have hMeq : ∀ w, c * blaschke b w = M w := by
    intro w
    simp only [blaschke, hMdef]
    rw [mul_div_assoc']
    congr 1 <;> ring
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc
    exact zero_ne_one hc
  have hbb : (1 : ℂ) - b * conj b ≠ 0 := by
    rw [Complex.mul_conj, ← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact_mod_cast (by linarith [normSq_lt_one_iff.mpr hb] : (1 : ℝ) - normSq b ≠ 0)
  have hdet : c * 1 - -(c * b) * -conj b ≠ 0 := by
    have : c * 1 - -(c * b) * -conj b = c * (1 - b * conj b) := by ring
    rw [this]
    exact mul_ne_zero hc0 hbb
  have hden : -conj b * z' + 1 ≠ 0 := by
    have : -conj b * z' + 1 = 1 - conj b * z' := by ring
    rw [this]
    exact hDz
  have hMd : HasDerivAt M (c * ((1 - b * conj b) / (1 - conj b * z') ^ 2)) z' := by
    have h := (hasDerivAt_blaschke hb hz1').const_mul c
    have hfun : (fun w => c * blaschke b w) = M := funext hMeq
    rw [hfun] at h
    exact h
  have hMA : AnalyticAt ℂ M z' := by
    simp only [hMdef]
    exact (by fun_prop : AnalyticAt ℂ (fun w : ℂ => c * w + -(c * b)) z').div
      (by fun_prop : AnalyticAt ℂ (fun w : ℂ => -conj b * w + 1) z') hden
  have hMne : deriv M z' ≠ 0 := by
    rw [hMd.deriv]
    exact mul_ne_zero hc0 (div_ne_zero hbb (pow_ne_zero 2 hDz))
  have hzM : M z' = z := by rw [← hMeq, hM0]
  have hfA : AnalyticAt ℂ f (M z') := by
    rw [hzM]
    exact hf.1.analyticAt (isOpen_ball.mem_nhds hz)
  have hf' : deriv f (M z') ≠ 0 := by
    rw [hzM]
    exact deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz
  have hloc : F =ᶠ[𝓝 z'] f ∘ M := by
    filter_upwards [isOpen_ball.mem_nhds hz'] with ζ hζ
    rw [Function.comp_apply, ← hMeq]
    exact (hcb ζ hζ).2
  have hSM : schwarzian M z' = 0 := schwarzian_mobius hdet z'
  have hSF : schwarzian F z' = schwarzian f z * deriv M z' ^ 2 := by
    rw [schwarzian_congr (hloc.filter_mono nhdsWithin_le_nhds),
      eq19_1_chain_rule hMA hMne hfA hf', hzM, hSM, add_zero]
  -- `|M'(z')| (1 - |z'|²) = 1 - |z|²`
  have hnorm : ‖deriv M z'‖ * (1 - ‖z'‖ ^ 2) = 1 - ‖z‖ ^ 2 := by
    have h1 := one_sub_normSq_blaschke hb hz1'
    have hzn : ‖z‖ = ‖blaschke b z'‖ := by rw [← hM0, norm_mul, hc, one_mul]
    have hpos : 0 < normSq (1 - conj b * z') := normSq_pos.mpr hDz
    have hb1 : 0 ≤ 1 - normSq b := by linarith [normSq_lt_one_iff.mpr hb]
    have hn1 : ‖(1 : ℂ) - b * conj b‖ = 1 - normSq b := by
      rw [Complex.mul_conj, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_of_nonneg hb1]
    rw [hMd.deriv, hzn, Complex.sq_norm, Complex.sq_norm, h1, norm_mul, hc, one_mul, norm_div,
      norm_pow, hn1, Complex.sq_norm]
    field_simp
  rw [hSF, norm_mul, norm_pow, ← hnorm]
  ring

/-- (2.2) `eq:lambda-f`, `sec02-prelim.tex:69`: `λ(f(z)) |f'(z)| = 2/(1-|z|²)` for a conformal
`f : 𝔻 → Ω`. -/
theorem eq_lambda_f {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {z : ℂ}
    (hz : z ∈ unitDisc) :
    poincareDensity Ω (f z) * ‖deriv f z‖ = 2 / (1 - ‖z‖ ^ 2) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hr : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hne : ‖deriv f z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz)
  unfold poincareDensity
  rw [(s02_poincareDensity_isGreatest hf hz).csSup_eq]
  field_simp

/-- §2.2, `sec02-prelim.tex:73`: the distance of `(Ω, ρ)` pulls back to the Poincaré distance of
`𝔻`, `d_ρ(f a, f z) = d_𝔻(a, z)`. -/
theorem subsec_poincare_dist {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {a z : ℂ} (ha : a ∈ unitDisc) (hz : z ∈ unitDisc) :
    poincareDist Ω (f a) (f z) = diskDist a z := by
  unfold poincareDist
  have hS : {d : ℝ | ∃ (F : ℂ → ℂ) (a' z' : ℂ), IsConformalOnto F unitDisc Ω ∧ a' ∈ unitDisc ∧
      z' ∈ unitDisc ∧ F a' = f a ∧ F z' = f z ∧ d = diskDist a' z'} = {diskDist a z} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨f, a, z, hf, ha, hz, rfl, rfl, rfl⟩, ?_⟩
    rintro d ⟨F, a', z', hF, ha', hz', hFa, hFz, rfl⟩
    obtain ⟨c, b, hc, hb, hcb⟩ := s02_riemannMap_factor hf hF
    have e1 : c * blaschke b a' = a := by
      rw [← (hcb a' ha').1, hFa]
      exact hf.2.1.leftInvOn_invFunOn ha
    have e2 : c * blaschke b z' = z := by
      rw [← (hcb z' hz').1, hFz]
      exact hf.2.1.leftInvOn_invFunOn hz
    unfold diskDist
    rw [← e1, ← e2, s02_diskCoshDist_rotate hc,
      s02_diskCoshDist_blaschke hb (mem_ball_zero_iff.mp ha') (mem_ball_zero_iff.mp hz')]
  rw [hS, csInf_singleton]

/-- (2.4) `eq:s-disk`, `sec02-prelim.tex:91`: `s(f(z)) = ¼ |S f(z)| (1-|z|²)²`. -/
theorem eq_s_disk {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {z : ℂ}
    (hz : z ∈ unitDisc) :
    schwarzNorm Ω (f z) = ‖schwarzian f z‖ * (1 - ‖z‖ ^ 2) ^ 2 / 4 := by
  unfold schwarzNorm
  have hS : {r : ℝ | ∃ (F : ℂ → ℂ) (z' : ℂ), IsConformalOnto F unitDisc Ω ∧ z' ∈ unitDisc ∧
      F z' = f z ∧ r = ‖schwarzian F z'‖ * (1 - ‖z'‖ ^ 2) ^ 2 / 4} =
      {‖schwarzian f z‖ * (1 - ‖z‖ ^ 2) ^ 2 / 4} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨f, z, hf, hz, rfl, rfl⟩, ?_⟩
    rintro r ⟨F, z', hF, hz', hFz, rfl⟩
    rw [s02_schwarzian_factor hf hF hz hz' hFz]
  rw [hS, csSup_singleton]

/-- §2.2, `sec02-prelim.tex:82`: `s = |S(f⁻¹)|/λ²` on `Ω` (definition (2.3), here a property of
`schwarzNorm`). -/
theorem eq_def_s {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) :
    schwarzNorm Ω w = ‖schwarzian (Function.invFunOn f unitDisc) w‖ / poincareDensity Ω w ^ 2 := by
  have hw' : w ∈ f '' unitDisc := by rw [hf.2.2]; exact hw
  obtain ⟨z, hz, rfl⟩ := hw'
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hr : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hψ : IsConformalOnto (Function.invFunOn f unitDisc) Ω unitDisc := hf.symm isOpen_ball
  have hfA : AnalyticAt ℂ f z := hf.1.analyticAt (isOpen_ball.mem_nhds hz)
  have hf' : deriv f z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz
  have hψA : AnalyticAt ℂ (Function.invFunOn f unitDisc) (f z) :=
    hψ.1.analyticAt (hΩo.mem_nhds hw)
  have hψ' : deriv (Function.invFunOn f unitDisc) (f z) ≠ 0 :=
    deriv_ne_zero_of_injOn hΩo hψ.1 hψ.2.1 hw
  have hloc : Function.invFunOn f unitDisc ∘ f =ᶠ[𝓝 z] fun v => (1 * v + 0) / (0 * v + 1) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with v hv
    rw [Function.comp_apply, hf.2.1.leftInvOn_invFunOn hv]
    ring
  have hchain := eq19_1_chain_rule hfA hf' hψA hψ'
  rw [schwarzian_congr (hloc.filter_mono nhdsWithin_le_nhds),
    schwarzian_mobius (by norm_num)] at hchain
  -- `S(f⁻¹)(f z) f'(z)² = -S f(z)`
  have hSψ : ‖schwarzian (Function.invFunOn f unitDisc) (f z)‖ * ‖deriv f z‖ ^ 2 =
      ‖schwarzian f z‖ := by
    rw [← norm_pow, ← norm_mul, ← norm_neg (schwarzian f z)]
    congr 1
    linear_combination -hchain
  have hlam := eq_lambda_f hf hz
  have hfn : 0 < ‖deriv f z‖ := norm_pos_iff.mpr hf'
  have hlam' : poincareDensity Ω (f z) = 2 / ((1 - ‖z‖ ^ 2) * ‖deriv f z‖) := by
    rw [eq_div_iff (mul_ne_zero hr.ne' hfn.ne')]
    calc poincareDensity Ω (f z) * ((1 - ‖z‖ ^ 2) * ‖deriv f z‖)
        = (1 - ‖z‖ ^ 2) * (poincareDensity Ω (f z) * ‖deriv f z‖) := by ring
      _ = 2 := by rw [hlam]; field_simp
  rw [eq_s_disk hf hz, hlam', ← hSψ]
  field_simp
  ring

/-- (2.5) `eq:nehari`, `sec02-prelim.tex:98`: Kraus–Nehari, `0 ≤ s ≤ 3/2`. -/
theorem eq_nehari {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) :
    0 ≤ schwarzNorm Ω w ∧ schwarzNorm Ω w ≤ 3 / 2 := by
  obtain ⟨f, hf⟩ := hΩ
  have hw' : w ∈ f '' unitDisc := by rw [hf.2.2]; exact hw
  obtain ⟨z, hz, rfl⟩ := hw'
  rw [eq_s_disk hf hz]
  have hN := thm19_2_nehari (lehto_isUnivMero_of_isConformalOnto hf) hz
  constructor
  · positivity
  · linarith

/-! ### Möbius naturality of `λ` and `s` -/

/-- Möbius naturality: for `M(w) = (αw + β)/(γw + δ)` with no pole on `Ω`,
`λ_{M(Ω)}(M w) |M'(w)| = λ_Ω(w)` and `s_{M(Ω)}(M w) = s_Ω(w)`. -/
theorem s02_mobius_natural {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    {α β γ δ : ℂ} (hdet : α * δ - β * γ ≠ 0) (hden : ∀ w ∈ Ω, γ * w + δ ≠ 0) {w : ℂ}
    (hw : w ∈ Ω) :
    poincareDensity ((fun v => (α * v + β) / (γ * v + δ)) '' Ω) ((α * w + β) / (γ * w + δ)) *
        ‖(α * δ - β * γ) / (γ * w + δ) ^ 2‖ = poincareDensity Ω w ∧
      schwarzNorm ((fun v => (α * v + β) / (γ * v + δ)) '' Ω) ((α * w + β) / (γ * w + δ)) =
        schwarzNorm Ω w := by
  obtain ⟨f, hf⟩ := hΩ
  obtain ⟨z, hz, rfl⟩ : w ∈ f '' unitDisc := by rw [hf.2.2]; exact hw
  set M : ℂ → ℂ := fun v => (α * v + β) / (γ * v + δ) with hMdef
  have hfm : MapsTo f unitDisc Ω := by
    intro ζ hζ
    rw [← hf.2.2]
    exact mem_image_of_mem f hζ
  have hMd : DifferentiableOn ℂ M Ω := by
    intro v hv
    exact ((hasDerivAt_mobius (a := α) (b := β) (hden v hv)).differentiableAt).differentiableWithinAt
  have hMi : InjOn M Ω := by
    intro v₁ h₁ v₂ h₂ he
    have hd₁ := hden v₁ h₁
    have hd₂ := hden v₂ h₂
    simp only [hMdef] at he
    rw [div_eq_div_iff hd₁ hd₂] at he
    have : (α * δ - β * γ) * (v₁ - v₂) = 0 := by linear_combination he
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hdet
    · exact sub_eq_zero.mp h
  have hF : IsConformalOnto (fun ζ => (α * f ζ + β) / (γ * f ζ + δ)) unitDisc (M '' Ω) := by
    refine ⟨hMd.comp hf.1 hfm, hMi.comp hf.2.1 hfm, ?_⟩
    rw [show (fun ζ => (α * f ζ + β) / (γ * f ζ + δ)) = M ∘ f from rfl, Set.image_comp, hf.2.2]
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hfd : DifferentiableAt ℂ f z := hf.1.differentiableAt (isOpen_ball.mem_nhds hz)
  have hf' : deriv f z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz
  have hfn : 0 < ‖deriv f z‖ := norm_pos_iff.mpr hf'
  have hd0 := hden (f z) (hfm hz)
  constructor
  · have h1 := eq_lambda_f hF hz
    have h2 := eq_lambda_f hf hz
    have hc : deriv (fun ζ => (α * f ζ + β) / (γ * f ζ + δ)) z =
        (α * δ - β * γ) / (γ * f z + δ) ^ 2 * deriv f z :=
      ((hasDerivAt_mobius (a := α) (b := β) hd0).comp z hfd.hasDerivAt).deriv
    rw [hc, norm_mul, ← h2, ← mul_assoc] at h1
    exact mul_right_cancel₀ hfn.ne' h1
  · rw [eq_s_disk hF hz, eq_s_disk hf hz,
      schwarzian_mobius_comp_analytic (hf.1.analyticAt (isOpen_ball.mem_nhds hz)) hf' hdet]

/-- §2, `sec02-prelim.tex:21` and `:86`: Möbius naturality of `λ` and `s` under a similarity
`M(z) = a z + b`: `λ_{M(Ω)}(M w) |a| = λ_Ω(w)` and `s_{M(Ω)}(M w) = s_Ω(w)`. -/
theorem subsec_poincare_natural_affine {Ω : Set ℂ}
    (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {a b : ℂ} (ha : a ≠ 0) {w : ℂ}
    (hw : w ∈ Ω) :
    poincareDensity ((fun z => a * z + b) '' Ω) (a * w + b) * ‖a‖ = poincareDensity Ω w ∧
      schwarzNorm ((fun z => a * z + b) '' Ω) (a * w + b) = schwarzNorm Ω w := by
  have h := s02_mobius_natural (α := a) (β := b) (γ := 0) (δ := 1) hΩ (by simpa using ha)
    (fun _ _ => by simp) hw
  have hfun : (fun v => (a * v + b) / (0 * v + 1)) = fun z => a * z + b := by
    funext v
    simp
  rw [hfun] at h
  simpa using h

/-- §2, `sec02-prelim.tex:21` and `:86`: Möbius naturality of `λ` and `s` under the inversion
`M = invAt x₀` (`x₀ ∉ Ω`, so `M(Ω) ⊆ ℂ`): `λ_{M(Ω)}(M w) |M'(w)| = λ_Ω(w)`, `|M'(w)| = |w - x₀|⁻²`,
and `s_{M(Ω)}(M w) = s_Ω(w)`. -/
theorem subsec_poincare_natural_inv {Ω : Set ℂ}
    (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {x₀ : ℂ} (hx₀ : x₀ ∉ Ω) {w : ℂ}
    (hw : w ∈ Ω) :
    poincareDensity (invAt x₀ '' Ω) (invAt x₀ w) / ‖w - x₀‖ ^ 2 = poincareDensity Ω w ∧
      schwarzNorm (invAt x₀ '' Ω) (invAt x₀ w) = schwarzNorm Ω w := by
  have hden : ∀ v ∈ Ω, (1 : ℂ) * v + -x₀ ≠ 0 := by
    intro v hv h
    apply hx₀
    have : v = x₀ := by linear_combination h
    rw [← this]
    exact hv
  have h := s02_mobius_natural (α := 0) (β := 1) (γ := 1) (δ := -x₀) hΩ (by norm_num) hden hw
  have hfun : (fun v => (0 * v + 1) / (1 * v + -x₀)) = invAt x₀ := by
    funext v
    simp [invAt, sub_eq_add_neg]
  have hinv : (0 * w + 1) / (1 * w + -x₀) = invAt x₀ w := by
    rw [← hfun]
  have hn : ‖(0 * -x₀ - 1 * 1 : ℂ) / (1 * w + -x₀) ^ 2‖ = 1 / ‖w - x₀‖ ^ 2 := by
    rw [← sub_eq_add_neg, one_mul, norm_div, norm_pow]
    simp
  rw [hfun, hinv, hn] at h
  rw [div_eq_mul_one_div]
  exact h

/-- The holomorphic Schwarzian is a measurable function. -/
theorem s02_pullback_measurable_schwarzianHol (f : ℂ → ℂ) : Measurable (schwarzianHol f) := by
  have h1 : Measurable (deriv f) := measurable_deriv f
  have h2 : Measurable (deriv (deriv f)) := measurable_deriv _
  have h3 : Measurable (deriv fun w => deriv (deriv f) w / deriv f w) := measurable_deriv _
  unfold schwarzianHol
  exact h3.sub (measurable_const.mul ((h2.div h1).pow_const 2))

/-- The real Jacobian of a holomorphic map at `z` is `|f'(z)|²`. -/
theorem s02_pullback_det (c : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
  have h : (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ :
      ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = Algebra.lmul ℝ ℂ c := by
    ext w
    simp [mul_comm]
  rw [ContinuousLinearMap.det, h, ← Algebra.norm_apply, Algebra.norm_complex_apply,
    Complex.normSq_eq_norm_sq]

/-- The pulled-back density: `|f'|² s(f z)² λ(f z)² = ¼ |S f(z)|² (1-|z|²)²`. -/
theorem s02_pullback_density {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {z : ℂ} (hz : z ∈ unitDisc) :
    ‖deriv f z‖ ^ 2 * (schwarzNorm Ω (f z) ^ 2 * poincareDensity Ω (f z) ^ 2) =
      ‖schwarzian f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 / 4 := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hr : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hl := eq_lambda_f hf hz
  rw [eq_s_disk hf hz]
  have : ‖deriv f z‖ ^ 2 * poincareDensity Ω (f z) ^ 2 = (2 / (1 - ‖z‖ ^ 2)) ^ 2 := by
    rw [← hl]; ring
  calc ‖deriv f z‖ ^ 2 * ((‖schwarzian f z‖ * (1 - ‖z‖ ^ 2) ^ 2 / 4) ^ 2 *
        poincareDensity Ω (f z) ^ 2)
      = (‖deriv f z‖ ^ 2 * poincareDensity Ω (f z) ^ 2) *
        ((‖schwarzian f z‖ * (1 - ‖z‖ ^ 2) ^ 2 / 4) ^ 2) := by ring
    _ = ‖schwarzian f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 / 4 := by
      rw [this]; field_simp; ring

/-- (2.6) `eq:pullback-mass`, first formula, `sec02-prelim.tex:112`:
`f^* dm_Ω = ¼ |S f|² (1-|z|²)² dA`, as an identity of integrals of Borel functions. -/
theorem eq_pullback_mass_a {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ w, φ w ∂curvMass Ω =
      ∫⁻ z in unitDisc, φ (f z) *
        ENNReal.ofReal (‖schwarzian f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 / 4) := by
  classical
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hDo : IsOpen unitDisc := isOpen_ball
  set F : ℂ → ℂ := unitDisc.piecewise f 0 with hFdef
  have hFm : Measurable F :=
    hf.1.continuousOn.measurable_piecewise continuousOn_const hD
  have hFeq : ∀ z ∈ unitDisc, F z = f z := fun z hz => by simp [hFdef, hz]
  set c : ℂ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (‖schwarzianHol f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 / 4) with hcdef
  have hcm : Measurable c := by
    have := s02_pullback_measurable_schwarzianHol f
    simp only [hcdef]
    fun_prop
  have hceq : ∀ z ∈ unitDisc, c z =
      ENNReal.ofReal (‖schwarzian f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 / 4) := by
    intro z hz
    have hA : AnalyticAt ℂ f z := hf.1.analyticAt (hDo.mem_nhds hz)
    simp only [hcdef, schwarzian_of_analyticAt hA]
  have hset : ∀ t : Set ℂ, t ∩ Ω = f '' (F ⁻¹' t ∩ unitDisc) := by
    intro t
    ext w
    constructor
    · rintro ⟨hwt, hwΩ⟩
      rw [← hf.2.2] at hwΩ
      obtain ⟨z, hz, rfl⟩ := hwΩ
      refine ⟨z, ⟨?_, hz⟩, rfl⟩
      show F z ∈ t
      rw [hFeq z hz]
      exact hwt
    · rintro ⟨z, ⟨hzt, hz⟩, rfl⟩
      refine ⟨?_, hf.2.2 ▸ mem_image_of_mem f hz⟩
      have : F z ∈ t := hzt
      rwa [hFeq z hz] at this
  have hmeas : curvMass Ω = ((volume.restrict unitDisc).withDensity c).map F := by
    ext t ht
    have hpre : MeasurableSet (F ⁻¹' t ∩ unitDisc) := (hFm ht).inter hD
    rw [Measure.map_apply hFm ht, withDensity_apply _ (hFm ht), Measure.restrict_restrict (hFm ht),
      curvMass, withDensity_apply _ ht, Measure.restrict_restrict ht, hset t]
    have hder : ∀ x ∈ F ⁻¹' t ∩ unitDisc, HasFDerivWithinAt f
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f x)).restrictScalars ℝ)
        (F ⁻¹' t ∩ unitDisc) x := by
      intro x hx
      exact ((hf.1.differentiableAt (hDo.mem_nhds hx.2)).hasDerivAt.hasFDerivAt.restrictScalars
        ℝ).hasFDerivWithinAt
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hpre hder
      (hf.2.1.mono inter_subset_right)]
    refine setLIntegral_congr_fun hpre (fun x hx => ?_)
    rw [s02_pullback_det, abs_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity),
      s02_pullback_density hf hx.2, hceq x hx.2]
  rw [hmeas, lintegral_map hφ hFm]
  change ∫⁻ a, (φ ∘ F) a ∂(volume.restrict unitDisc).withDensity c = _
  rw [lintegral_withDensity_eq_lintegral_mul _ hcm (hφ.comp hFm)]
  refine setLIntegral_congr_fun hD (fun z hz => ?_)
  simp only [Pi.mul_apply, Function.comp, hFeq z hz, hceq z hz, mul_comm]

/-- (2.6) `eq:pullback-mass`, second formula, `sec02-prelim.tex:114`:
`(1-|z|²) f^* dm_Ω = ¼ |S f|² (1-|z|²)³ dA`, i.e. integrating `ψ(z)(1-|z|²)` against `f^* dm_Ω`
(written on `Ω` through `z = f⁻¹(w)`) gives `¼ ∫ ψ d(schwarzCarlesonMeasure f)`. -/
theorem eq_pullback_mass_b {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {ψ : ℂ → ℝ≥0∞} (hψ : Measurable ψ) :
    ∫⁻ w, ψ (Function.invFunOn f unitDisc w) *
        ENNReal.ofReal (1 - ‖Function.invFunOn f unitDisc w‖ ^ 2) ∂curvMass Ω =
      (∫⁻ z, ψ z ∂schwarzCarlesonMeasure f) / 4 := by
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
  set φ : ℂ → ℝ≥0∞ := fun w => ψ (G w) * ENNReal.ofReal (1 - ‖G w‖ ^ 2) with hφdef
  have hφm : Measurable φ :=
    (hψ.comp hGm).mul (ENNReal.measurable_ofReal.comp
      (measurable_const.sub (hGm.norm.pow_const 2)))
  have hae : ∀ᵐ w ∂curvMass Ω, w ∈ Ω := by
    unfold curvMass
    exact (withDensity_absolutelyContinuous (volume.restrict Ω) _).ae_le (ae_restrict_mem hΩm)
  have hL : ∫⁻ w, ψ (g w) * ENNReal.ofReal (1 - ‖g w‖ ^ 2) ∂curvMass Ω =
      ∫⁻ w, φ w ∂curvMass Ω := by
    refine lintegral_congr_ae (hae.mono fun w hw => ?_)
    simp only [hφdef, hGeq w hw]
  -- the Schwarzian density through `schwarzianHol` (measurable)
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
  rw [hL, eq_pullback_mass_a hf hφm, hR, lintegral_withDensity_eq_lintegral_mul _ hcm hψ,
    ENNReal.div_eq_inv_mul, ← lintegral_const_mul' _ _ (by norm_num)]
  refine setLIntegral_congr_fun hD (fun z hz => ?_)
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have ht : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hfz : f z ∈ Ω := hf.2.2 ▸ mem_image_of_mem f hz
  have hgz : g (f z) = z := hf.2.1.leftInvOn_invFunOn hz
  simp only [hφdef, Pi.mul_apply, hGeq (f z) hfz, hgz, hcdef, hSch z hz]
  rw [mul_assoc, ← ENNReal.ofReal_mul ht.le,
    show (1 - ‖z‖ ^ 2) * (‖schwarzianHol f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 / 4) =
      ‖schwarzianHol f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3 / 4 by ring,
    ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, ENNReal.div_eq_inv_mul]
  ring

/-! ### Basic facts on `λ`, `d_ρ` and `∂Ω` -/

/-- The Poincaré density is positive on `Ω`. -/
theorem s02_poincareDensity_pos {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    {w : ℂ} (hw : w ∈ Ω) : 0 < poincareDensity Ω w := by
  obtain ⟨f, hf⟩ := hΩ
  have hw' : w ∈ f '' unitDisc := by rw [hf.2.2]; exact hw
  obtain ⟨z, hz, rfl⟩ := hw'
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hr : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hfn : 0 < ‖deriv f z‖ :=
    norm_pos_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz)
  have h := eq_lambda_f hf hz
  have h2 : 0 < poincareDensity Ω (f z) * ‖deriv f z‖ := by rw [h]; positivity
  exact pos_of_mul_pos_left h2 hfn.le

/-- The image of a Riemann map is not all of `ℂ` (Liouville). -/
theorem s02_compl_nonempty {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) :
    Ωᶜ.Nonempty := by
  by_contra hne
  have hΩ : Ω = univ := by
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hne
    exact hne
  have hψ : IsConformalOnto (Function.invFunOn f unitDisc) Ω unitDisc := hf.symm isOpen_ball
  rw [hΩ] at hψ
  have hd : Differentiable ℂ (Function.invFunOn f unitDisc) := by
    intro x
    exact hψ.1.differentiableAt (isOpen_univ.mem_nhds (mem_univ x))
  have hb : Bornology.IsBounded (range (Function.invFunOn f unitDisc)) := by
    rw [← Set.image_univ, hψ.2.2]
    exact isBounded_ball
  have h0 : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have h1 : ((1 / 2 : ℝ) : ℂ) ∈ unitDisc := by
    rw [unitDisc, mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
    norm_num
  have e := Differentiable.apply_eq_apply_of_bounded hd hb (f 0) (f ((1 / 2 : ℝ) : ℂ))
  rw [hf.2.1.leftInvOn_invFunOn h0, hf.2.1.leftInvOn_invFunOn h1] at e
  have e' := congrArg Complex.re e
  simp at e'

/-- The distance from a point of `Ω` to `∂Ω` is positive. -/
theorem s02_infDist_pos {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) : 0 < infDist w Ωᶜ := by
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  exact (hΩo.isClosed_compl.notMem_iff_infDist_pos (s02_compl_nonempty hf)).mp
    (fun h => h hw)

/-- `d_ρ ≥ 0` on `Ω`. -/
theorem s02_poincareDist_nonneg {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    {p w : ℂ} (hp : p ∈ Ω) (hw : w ∈ Ω) : 0 ≤ poincareDist Ω p w := by
  obtain ⟨f, hf⟩ := hΩ
  obtain ⟨a, ha, rfl⟩ : p ∈ f '' unitDisc := by rw [hf.2.2]; exact hp
  obtain ⟨z, hz, rfl⟩ : w ∈ f '' unitDisc := by rw [hf.2.2]; exact hw
  rw [subsec_poincare_dist hf ha hz]
  exact s02_diskDist_nonneg ha hz

/-- `d_ρ` is symmetric on `Ω`. -/
theorem s02_poincareDist_comm {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    {p w : ℂ} (hp : p ∈ Ω) (hw : w ∈ Ω) : poincareDist Ω p w = poincareDist Ω w p := by
  obtain ⟨f, hf⟩ := hΩ
  obtain ⟨a, ha, rfl⟩ : p ∈ f '' unitDisc := by rw [hf.2.2]; exact hp
  obtain ⟨z, hz, rfl⟩ : w ∈ f '' unitDisc := by rw [hf.2.2]; exact hw
  rw [subsec_poincare_dist hf ha hz, subsec_poincare_dist hf hz ha]
  exact s02_diskDist_comm ha hz

/-- The triangle inequality for `d_ρ` on `Ω`. -/
theorem s02_poincareDist_triangle {Ω : Set ℂ}
    (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {p w w' : ℂ} (hp : p ∈ Ω) (hw : w ∈ Ω)
    (hw' : w' ∈ Ω) : poincareDist Ω p w' ≤ poincareDist Ω p w + poincareDist Ω w w' := by
  obtain ⟨f, hf⟩ := hΩ
  obtain ⟨a, ha, rfl⟩ : p ∈ f '' unitDisc := by rw [hf.2.2]; exact hp
  obtain ⟨z, hz, rfl⟩ : w ∈ f '' unitDisc := by rw [hf.2.2]; exact hw
  obtain ⟨z', hz', rfl⟩ : w' ∈ f '' unitDisc := by rw [hf.2.2]; exact hw'
  rw [subsec_poincare_dist hf ha hz', subsec_poincare_dist hf ha hz, subsec_poincare_dist hf hz hz']
  exact s02_diskDist_triangle ha hz hz'

/-! ### Kernel Lipschitz bounds -/

/-- `cosh (a + b) ≤ e^b cosh a` for `b ≥ 0`. -/
theorem s02_cosh_add_le {a b : ℝ} (hb : 0 ≤ b) :
    Real.cosh (a + b) ≤ Real.exp b * Real.cosh a := by
  rw [Real.cosh_eq, Real.cosh_eq, neg_add, Real.exp_add, Real.exp_add]
  have h1 : Real.exp (-b) ≤ Real.exp b := Real.exp_le_exp.2 (by linarith)
  have h2 := Real.exp_pos (-a)
  nlinarith

/-- `sech²(r/2) ≤ e^δ sech²(s/2)` when `0 ≤ s ≤ r + δ`, `δ ≥ 0`. -/
theorem s02_sech_sq_le {r s δ : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hδ : 0 ≤ δ) (hsr : s ≤ r + δ) :
    ((Real.cosh (r / 2))⁻¹) ^ 2 ≤ Real.exp δ * ((Real.cosh (s / 2))⁻¹) ^ 2 := by
  have hcs : Real.cosh (s / 2) ≤ Real.exp (δ / 2) * Real.cosh (r / 2) := by
    calc Real.cosh (s / 2) ≤ Real.cosh (r / 2 + δ / 2) := by
          rw [Real.cosh_le_cosh, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          linarith
      _ ≤ _ := s02_cosh_add_le (by linarith)
  have hpr := Real.cosh_pos (r / 2)
  have hps := Real.cosh_pos (s / 2)
  have he : Real.exp δ = Real.exp (δ / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he, inv_pow, inv_pow, ← div_eq_mul_inv, inv_eq_one_div,
    div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]
  exact pow_le_pow_left₀ hps.le hcs 2

/-! ### Busemann functions -/

/-! ### Koebe estimates -/

/-- `|(f ∘ M_{-z})'(0)| = (1 - |z|²) |f'(z)|`. -/
theorem s02_norm_deriv_comp_blaschke {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {z : ℂ} (hz : z ∈ unitDisc) :
    ‖deriv (f ∘ blaschke (-z)) 0‖ = (1 - ‖z‖ ^ 2) * ‖deriv f z‖ := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hnz : ‖-z‖ < 1 := by simpa using hz1
  have hr : (0 : ℝ) ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hfd : DifferentiableAt ℂ f z := hf.1.differentiableAt (isOpen_ball.mem_nhds hz)
  have hB := hasDerivAt_blaschke hnz (by simp : ‖(0 : ℂ)‖ < 1)
  have hfd' : HasDerivAt f (deriv f (blaschke (-z) 0)) (blaschke (-z) 0) := by
    rw [blaschke_neg_zero]
    exact hfd.hasDerivAt
  rw [(hfd'.comp 0 hB).deriv, blaschke_neg_zero]
  have e : (1 - -z * conj (-z)) / (1 - conj (-z) * 0) ^ 2 = (((1 - ‖z‖ ^ 2 : ℝ)) : ℂ) := by
    rw [map_neg, neg_mul_neg, mul_zero, sub_zero, one_pow, div_one, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr, mul_comm]

/-- Lemma 2.1(a) `lem:koebe`, `sec02-prelim.tex:118`: `d ≤ (1-|z|²)|f'(z)| ≤ 4d`, hence
`1/(2d) ≤ λ ≤ 2/d`, where `d = dist(f z, ∂Ω)`. -/
theorem lem_koebe_a {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {z : ℂ}
    (hz : z ∈ unitDisc) :
    infDist (f z) Ωᶜ ≤ (1 - ‖z‖ ^ 2) * ‖deriv f z‖ ∧
      (1 - ‖z‖ ^ 2) * ‖deriv f z‖ ≤ 4 * infDist (f z) Ωᶜ ∧
      1 / (2 * infDist (f z) Ωᶜ) ≤ poincareDensity Ω (f z) ∧
      poincareDensity Ω (f z) ≤ 2 / infDist (f z) Ωᶜ := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hr : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hfz : f z ∈ Ω := by rw [← hf.2.2]; exact mem_image_of_mem f hz
  have hd := s02_infDist_pos hf hfz
  have hne := s02_compl_nonempty hf
  have hfn : 0 < ‖deriv f z‖ :=
    norm_pos_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz)
  set d := infDist (f z) Ωᶜ
  set m := (1 - ‖z‖ ^ 2) * ‖deriv f z‖ with hm
  have hmpos : 0 < m := by positivity
  -- `d ≤ m`: the disc `D(f z, d)` lies in `Ω`
  have h1 : d ≤ m := by
    have hG := (s02_poincareDensity_isGreatest hf hz).2
    refine hG ⟨fun ζ => f z + (d : ℂ) * ζ, ?_, ?_, ?_, ?_⟩
    · exact (differentiableOn_const _).add ((differentiableOn_const _).mul differentiableOn_id)
    · intro ζ hζ
      by_contra hc
      have hc' : f z + (d : ℂ) * ζ ∈ Ωᶜ := hc
      have h := infDist_le_dist_of_mem (x := f z) hc'
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hd.le] at h
      have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
      nlinarith
    · simp
    · have : HasDerivAt (fun ζ : ℂ => f z + (d : ℂ) * ζ) (d : ℂ) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (d : ℂ)).const_add (f z)
      rw [this.deriv, Complex.norm_real, Real.norm_of_nonneg hd.le]
  -- `m ≤ 4 d`: Koebe's quarter theorem for `f ∘ M_{-z} - f z`
  have h2 : m ≤ 4 * d := by
    have hnz : ‖-z‖ < 1 := by simpa using hz1
    have hmaps : MapsTo (blaschke (-z)) unitDisc unitDisc := fun ζ hζ =>
      mem_ball_zero_iff.mpr (blaschke_mem_unitDisc hnz (mem_ball_zero_iff.mp hζ))
    have hinjB : InjOn (blaschke (-z)) unitDisc := (isConformalOnto_blaschke hnz).2.1
    have hm4 : m / 4 ≤ d := by
      refine (le_infDist hne).2 fun x hx => ?_
      have hDf : DifferentiableOn ℂ (fun ζ => (f ∘ blaschke (-z)) ζ - f z) (ball 0 1) :=
        (hf.1.comp (differentiableOn_blaschke hnz) hmaps).sub (differentiableOn_const _)
      have hinj : InjOn (fun ζ => (f ∘ blaschke (-z)) ζ - f z) (ball 0 1) := by
        intro ζ₁ h₁ ζ₂ h₂ he
        exact hinjB h₁ h₂ (hf.2.1 (hmaps h₁) (hmaps h₂) (sub_left_inj.mp he))
      have h0 : (fun ζ => (f ∘ blaschke (-z)) ζ - f z) 0 = 0 := by simp
      have hnot : x - f z ∉ (fun ζ => (f ∘ blaschke (-z)) ζ - f z) '' ball 0 1 := by
        rintro ⟨ζ, hζ, he⟩
        apply hx
        have : f (blaschke (-z) ζ) = x := by
          simp only [Function.comp_apply] at he
          linear_combination he
        rw [← this, ← hf.2.2]
        exact mem_image_of_mem f (hmaps hζ)
      have hK := koebe_quarter_of_not_mem hDf hinj h0 hnot
      have hdz : deriv (fun ζ => (f ∘ blaschke (-z)) ζ - f z) 0 =
          deriv (f ∘ blaschke (-z)) 0 := deriv_sub_const _
      rw [hdz, s02_norm_deriv_comp_blaschke hf hz, ← hm, ← norm_neg, neg_sub] at hK
      rw [dist_eq_norm]
      linarith
    linarith
  have hlam : poincareDensity Ω (f z) = 2 / m := by
    have h := eq_lambda_f hf hz
    rw [eq_div_iff hmpos.ne']
    calc poincareDensity Ω (f z) * m
        = (1 - ‖z‖ ^ 2) * (poincareDensity Ω (f z) * ‖deriv f z‖) := by rw [hm]; ring
      _ = 2 := by rw [h]; field_simp
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [hlam, div_le_div_iff₀ (by positivity) hmpos]
    linarith
  · rw [hlam]
    exact div_le_div_of_nonneg_left (by norm_num) hd h1

/-- (2.19) through a Riemann map; the proof of `eq_kernel_disk`, placed early for its users. -/
theorem s02_intrKernel_eq {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {a z : ℂ}
    (ha : a ∈ unitDisc) (hz : z ∈ unitDisc) :
    intrKernel Ω (f a) (f z) = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖1 - conj a * z‖ ^ 2 := by
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hna : normSq a < 1 := normSq_lt_one_iff.mpr ha1
  have hnz : normSq z < 1 := normSq_lt_one_iff.mpr hz1
  have hD := blaschke_den_ne_zero ha1 hz1
  have hND : normSq (1 - conj a * z) ≠ 0 := (normSq_pos.mpr hD).ne'
  have h1 : 1 ≤ diskCoshDist a z := by
    unfold diskCoshDist
    have h2a : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
    have h2z : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have : 0 ≤ 2 * ‖a - z‖ ^ 2 / ((1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2)) := by positivity
    linarith
  have hcosh : Real.cosh (diskDist a z) = diskCoshDist a z := Real.cosh_arcosh h1
  have hc2 : Real.cosh (diskDist a z / 2) ^ 2 = (1 + diskCoshDist a z) / 2 := by
    have h2 := Real.cosh_two_mul (diskDist a z / 2)
    have h3 := Real.cosh_sq (diskDist a z / 2)
    rw [show 2 * (diskDist a z / 2) = diskDist a z by ring, hcosh] at h2
    linarith
  unfold intrKernel
  rw [subsec_poincare_dist hf ha hz, inv_pow, hc2]
  unfold diskCoshDist
  have hkey := normSq_blaschke_key a z
  have h1a : 1 - normSq a ≠ 0 := by linarith
  have h1z : 1 - normSq z ≠ 0 := by linarith
  have hsw : ‖a - z‖ ^ 2 = normSq (z - a) := by rw [norm_sub_rev, Complex.sq_norm]
  rw [hsw]
  simp only [Complex.sq_norm]
  have hPne : (1 - normSq a) * (1 - normSq z) ≠ 0 := mul_ne_zero h1a h1z
  have hND' : normSq (1 - conj a * z) = (1 - normSq a) * (1 - normSq z) + normSq (z - a) := by
    linear_combination hkey
  rw [hND']
  generalize (1 - normSq a) * (1 - normSq z) = P at hPne ⊢
  generalize normSq (z - a) = X
  rw [show (1 + (1 + 2 * X / P)) / 2 = 1 + X / P by ring,
    show 1 + X / P = (P + X) / P by rw [add_div, div_self hPne], inv_div]

/-! ### Real derivatives and Wirtinger derivatives -/

/-- If `Dφ(w) v = Re(c v)`, then `∂_w φ = c / 2`. -/
theorem s02_wirtingerDz_eq {φ : ℂ → ℝ} {L : ℂ →L[ℝ] ℝ} {w c : ℂ} (hφ : HasFDerivAt φ L w)
    (hL : ∀ v, L v = (c * v).re) : wirtingerDz φ w = c / 2 := by
  unfold wirtingerDz
  rw [hφ.fderiv, hL, hL]
  apply Complex.ext <;> simp

/-- The real derivative of `x ↦ ‖h x‖²` for complex-differentiable `h`: `v ↦ Re(2 h̄ h' v)`. -/
theorem s02_hasFDerivAt_normSq {h : ℂ → ℂ} {h' w : ℂ} (hh : HasDerivAt h h' w) :
    ∃ L : ℂ →L[ℝ] ℝ, HasFDerivAt (fun x => ‖h x‖ ^ 2) L w ∧
      ∀ v, L v = (2 * conj (h w) * h' * v).re := by
  have hF := hh.hasFDerivAt.restrictScalars ℝ
  refine ⟨_, hF.norm_sq, fun v => ?_⟩
  simp [Complex.inner, Complex.mul_re, Complex.mul_im]
  ring

/-- The real derivative of `x ↦ log ‖h x‖²`: `v ↦ Re(2 h'/h v)`. -/
theorem s02_hasFDerivAt_log_normSq {h : ℂ → ℂ} {h' w : ℂ} (hh : HasDerivAt h h' w)
    (h0 : h w ≠ 0) :
    ∃ L : ℂ →L[ℝ] ℝ, HasFDerivAt (fun x => Real.log (‖h x‖ ^ 2)) L w ∧
      ∀ v, L v = (2 * h' / h w * v).re := by
  obtain ⟨L, hL, hLv⟩ := s02_hasFDerivAt_normSq hh
  have hn : ‖h w‖ ^ 2 ≠ 0 := by positivity
  refine ⟨_, hL.log hn, fun v => ?_⟩
  rw [ContinuousLinearMap.smul_apply, hLv, smul_eq_mul, ← Complex.re_ofReal_mul]
  congr 1
  have hc : conj (h w) * h w = ((‖h w‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hc0 : conj (h w) ≠ 0 := (map_ne_zero _).2 h0
  rw [Complex.ofReal_inv, ← hc]
  field_simp

/-- The real derivative of `x ↦ log (1 - ‖h x‖²)`: `v ↦ Re(-2 h̄ h' v / (1 - |h|²))`. -/
theorem s02_hasFDerivAt_log_one_sub_normSq {h : ℂ → ℂ} {h' w : ℂ} (hh : HasDerivAt h h' w)
    (h1 : ‖h w‖ < 1) :
    ∃ L : ℂ →L[ℝ] ℝ, HasFDerivAt (fun x => Real.log (1 - ‖h x‖ ^ 2)) L w ∧
      ∀ v, L v = (-2 * conj (h w) * h' / ((1 - ‖h w‖ ^ 2 : ℝ) : ℂ) * v).re := by
  obtain ⟨L, hL, hLv⟩ := s02_hasFDerivAt_normSq hh
  have hr : (0 : ℝ) < 1 - ‖h w‖ ^ 2 := by nlinarith [norm_nonneg (h w)]
  refine ⟨_, (hL.const_sub 1).log hr.ne', fun v => ?_⟩
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, hLv, smul_eq_mul,
    show -2 * conj (h w) * h' / ((1 - ‖h w‖ ^ 2 : ℝ) : ℂ) * v =
      ((-(1 - ‖h w‖ ^ 2)⁻¹ : ℝ) : ℂ) * (2 * conj (h w) * h' * v) by
      rw [Complex.ofReal_neg, Complex.ofReal_inv]; ring,
    Complex.re_ofReal_mul]
  ring

/-! ### The density `λ` and `A = ∂_w log λ` through the inverse Riemann map (I1, I2) -/

/-- `(f⁻¹)'(f z) f'(z) = 1`. -/
theorem s02_deriv_inv_mul {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {z : ℂ}
    (hz : z ∈ unitDisc) :
    deriv (Function.invFunOn f unitDisc) (f z) * deriv f z = 1 := by
  have hψd := hf.differentiableAt_invFunOn isOpen_ball hz
  have hfd : DifferentiableAt ℂ f z := hf.1.differentiableAt (isOpen_ball.mem_nhds hz)
  have hcomp : HasDerivAt (Function.invFunOn f unitDisc ∘ f)
      (deriv (Function.invFunOn f unitDisc) (f z) * deriv f z) z :=
    hψd.hasDerivAt.comp z hfd.hasDerivAt
  have heq : Function.invFunOn f unitDisc ∘ f =ᶠ[𝓝 z] id := by
    filter_upwards [isOpen_ball.mem_nhds hz] with v hv
    exact hf.2.1.leftInvOn_invFunOn hv
  rw [← hcomp.deriv, heq.deriv_eq, deriv_id]

/-- I1: `λ(w) = 2 |ψ'(w)| / (1 - |ψ(w)|²)` on `Ω`, `ψ = f⁻¹`. -/
theorem s02_poincareDensity_eq_inv {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {w : ℂ} (hw : w ∈ Ω) :
    poincareDensity Ω w = 2 * ‖deriv (Function.invFunOn f unitDisc) w‖ /
      (1 - ‖Function.invFunOn f unitDisc w‖ ^ 2) := by
  obtain ⟨z, hz, rfl⟩ : w ∈ f '' unitDisc := by rw [hf.2.2]; exact hw
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hr : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hfn : 0 < ‖deriv f z‖ :=
    norm_pos_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz)
  have hinv := congrArg norm (s02_deriv_inv_mul hf hz)
  rw [norm_mul, norm_one] at hinv
  have hl := eq_lambda_f hf hz
  rw [hf.2.1.leftInvOn_invFunOn hz, eq_div_iff hr.ne']
  have : poincareDensity Ω (f z) =
      poincareDensity Ω (f z) * (‖deriv (Function.invFunOn f unitDisc) (f z)‖ * ‖deriv f z‖) := by
    rw [hinv, mul_one]
  rw [this, show poincareDensity Ω (f z) *
      (‖deriv (Function.invFunOn f unitDisc) (f z)‖ * ‖deriv f z‖) * (1 - ‖z‖ ^ 2) =
      ‖deriv (Function.invFunOn f unitDisc) (f z)‖ *
        ((poincareDensity Ω (f z) * ‖deriv f z‖) * (1 - ‖z‖ ^ 2)) by ring, hl]
  field_simp

/-- I2 (on `Ω`): `A = ψ''/(2ψ') + ψ̄ ψ'/(1 - |ψ|²)`, `ψ = f⁻¹`. -/
theorem s02_logDensityDz_eq {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {w : ℂ} (hw : w ∈ Ω) :
    logDensityDz Ω w = deriv (deriv (Function.invFunOn f unitDisc)) w /
        (2 * deriv (Function.invFunOn f unitDisc) w) +
      conj (Function.invFunOn f unitDisc w) * deriv (Function.invFunOn f unitDisc) w /
        ((1 - ‖Function.invFunOn f unitDisc w‖ ^ 2 : ℝ) : ℂ) := by
  set ψ := Function.invFunOn f unitDisc with hψdef
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hψ : IsConformalOnto ψ Ω unitDisc := hf.symm isOpen_ball
  have hψU : ∀ x ∈ Ω, ‖ψ x‖ < 1 := by
    intro x hx
    have hmem := mem_image_of_mem ψ hx
    rw [hψ.2.2] at hmem
    exact mem_ball_zero_iff.mp hmem
  have hψ'ne : ∀ x ∈ Ω, deriv ψ x ≠ 0 := fun x hx =>
    deriv_ne_zero_of_injOn hΩo hψ.1 hψ.2.1 hx
  have hψA : AnalyticAt ℂ ψ w := hψ.1.analyticAt (hΩo.mem_nhds hw)
  have hψd : DifferentiableAt ℂ ψ w := hψA.differentiableAt
  have hψ'd : DifferentiableAt ℂ (deriv ψ) w := hψA.deriv.differentiableAt
  obtain ⟨L1, h1, h1v⟩ := s02_hasFDerivAt_log_normSq hψ'd.hasDerivAt (hψ'ne w hw)
  obtain ⟨L2, h2, h2v⟩ := s02_hasFDerivAt_log_one_sub_normSq hψd.hasDerivAt (hψU w hw)
  have hF : HasFDerivAt (fun x => Real.log 2 + (1 / 2 : ℝ) • Real.log (‖deriv ψ x‖ ^ 2) -
      Real.log (1 - ‖ψ x‖ ^ 2)) ((1 / 2 : ℝ) • L1 - L2) w :=
    ((h1.const_smul (1 / 2 : ℝ)).const_add (Real.log 2)).sub h2
  -- `log λ` agrees with this explicit function near `w`
  have heq : (fun x => Real.log (poincareDensity Ω x)) =ᶠ[𝓝 w]
      fun x => Real.log 2 + (1 / 2 : ℝ) • Real.log (‖deriv ψ x‖ ^ 2) -
        Real.log (1 - ‖ψ x‖ ^ 2) := by
    filter_upwards [hΩo.mem_nhds hw] with x hx
    have hr : (0 : ℝ) < 1 - ‖ψ x‖ ^ 2 := by nlinarith [norm_nonneg (ψ x), hψU x hx]
    have hn : 0 < ‖deriv ψ x‖ := norm_pos_iff.mpr (hψ'ne x hx)
    rw [s02_poincareDensity_eq_inv hf hx, ← hψdef, Real.log_div (by positivity) hr.ne',
      Real.log_mul (by norm_num) hn.ne', Real.log_pow, smul_eq_mul]
    push_cast
    ring
  unfold logDensityDz
  have hwz : wirtingerDz (fun x => Real.log (poincareDensity Ω x)) w =
      wirtingerDz (fun x => Real.log 2 + (1 / 2 : ℝ) • Real.log (‖deriv ψ x‖ ^ 2) -
        Real.log (1 - ‖ψ x‖ ^ 2)) w := by
    unfold wirtingerDz
    rw [heq.fderiv_eq]
  rw [hwz, s02_wirtingerDz_eq hF (c := deriv (deriv ψ) w / deriv ψ w +
    2 * conj (ψ w) * deriv ψ w / ((1 - ‖ψ w‖ ^ 2 : ℝ) : ℂ))]
  · ring
  · intro v
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, h1v, h2v,
      smul_eq_mul]
    rw [← Complex.re_ofReal_mul, ← Complex.sub_re]
    congr 1
    push_cast
    ring

/-- I2 (on `𝔻`): `A(f z) f'(z) = z̄/(1 - |z|²) - f''(z)/(2 f'(z))`. -/
theorem s02_logDensityDz_mul_deriv {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {z : ℂ} (hz : z ∈ unitDisc) :
    logDensityDz Ω (f z) * deriv f z =
      conj z / ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) - deriv (deriv f) z / (2 * deriv f z) := by
  set ψ := Function.invFunOn f unitDisc with hψdef
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hr : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hrc : ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hfz : f z ∈ Ω := by rw [← hf.2.2]; exact mem_image_of_mem f hz
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hψ : IsConformalOnto ψ Ω unitDisc := hf.symm isOpen_ball
  have hf' : deriv f z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz
  have hfA : AnalyticAt ℂ f z := hf.1.analyticAt (isOpen_ball.mem_nhds hz)
  have hψz : ψ (f z) = z := hf.2.1.leftInvOn_invFunOn hz
  have hψ1 : deriv ψ (f z) = (deriv f z)⁻¹ := eq_inv_of_mul_eq_one_left (s02_deriv_inv_mul hf hz)
  -- `ψ''(f z) f'(z) = -f''(z)/f'(z)²`, from `ψ'(f ζ) = 1/f'(ζ)` near `z`
  have hψ2 : deriv (deriv ψ) (f z) = -deriv (deriv f) z / deriv f z ^ 3 := by
    have hψA : AnalyticAt ℂ ψ (f z) := hψ.1.analyticAt (hΩo.mem_nhds hfz)
    have hc1 : HasDerivAt (deriv ψ ∘ f) (deriv (deriv ψ) (f z) * deriv f z) z :=
      hψA.deriv.differentiableAt.hasDerivAt.comp z hfA.differentiableAt.hasDerivAt
    have hc2 : HasDerivAt (fun ζ => (deriv f ζ)⁻¹) (-deriv (deriv f) z / deriv f z ^ 2) z :=
      hfA.deriv.differentiableAt.hasDerivAt.inv hf'
    have heq : deriv ψ ∘ f =ᶠ[𝓝 z] fun ζ => (deriv f ζ)⁻¹ := by
      filter_upwards [isOpen_ball.mem_nhds hz] with ζ hζ
      exact eq_inv_of_mul_eq_one_left (s02_deriv_inv_mul hf hζ)
    have h := hc1.deriv
    rw [heq.deriv_eq, hc2.deriv] at h
    calc deriv (deriv ψ) (f z) = deriv (deriv ψ) (f z) * deriv f z / deriv f z :=
          (mul_div_cancel_right₀ _ hf').symm
      _ = -deriv (deriv f) z / deriv f z ^ 2 / deriv f z := by rw [← h]
      _ = -deriv (deriv f) z / deriv f z ^ 3 := by rw [div_div, ← pow_succ]
  rw [s02_logDensityDz_eq hf hfz, ← hψdef, hψz, hψ1, hψ2]
  field_simp
  ring

/-- Lemma 2.1(b) `lem:koebe`, `sec02-prelim.tex:125`:
`|(1-|z|²) f''(z)/f'(z) - 2 z̄| ≤ 4`, hence `|A(w)| ≤ λ(w)`, `A = ∂_w log λ`. -/
theorem lem_koebe_b {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {z : ℂ}
    (hz : z ∈ unitDisc) :
    ‖(1 - ‖z‖ ^ 2 : ℂ) * deriv (deriv f) z / deriv f z - 2 * conj z‖ ≤ 4 ∧
      ‖logDensityDz Ω (f z)‖ ≤ poincareDensity Ω (f z) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hr : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hK : (1 - ‖z‖ ^ 2 : ℂ) = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have h1 : ‖(1 - ‖z‖ ^ 2 : ℂ) * deriv (deriv f) z / deriv f z - 2 * conj z‖ ≤ 4 := by
    rw [hK]
    exact kb_koebe_transform_ineq hf.1 hf.2.1 hz
  refine ⟨h1, ?_⟩
  have hf' : deriv f z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz
  have hfn : 0 < ‖deriv f z‖ := norm_pos_iff.mpr hf'
  have hrc : ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hI := s02_logDensityDz_mul_deriv hf hz
  have hq : conj z / ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) - deriv (deriv f) z / (2 * deriv f z) =
      -(((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv (deriv f) z / deriv f z - 2 * conj z) /
        (2 * ((1 - ‖z‖ ^ 2 : ℝ) : ℂ)) := by
    field_simp
    ring
  have hnorm : ‖logDensityDz Ω (f z)‖ * ‖deriv f z‖ ≤ 2 / (1 - ‖z‖ ^ 2) := by
    rw [← norm_mul, hI, hq, norm_div, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hr.le, ← hK, Complex.norm_two]
    rw [div_le_div_iff₀ (by positivity) hr]
    nlinarith
  rw [← eq_lambda_f hf hz] at hnorm
  exact le_of_mul_le_mul_right hnorm hfn

/-! ## §2.3 Horoballs and Busemann functions -/

/-- §2.3, `sec02-prelim.tex:164`: `B_w` is the closed Euclidean ball tangent to `ℂ` at `w` with
diameter `2/λ(w)`. -/
theorem subsec_horoballs_ball {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    {w : ℂ} (hw : w ∈ Ω) :
    horoball Ω w = {q | q ∈ UHS ∧
      ‖q.1 - w‖ ^ 2 + (q.2 - 1 / poincareDensity Ω w) ^ 2 ≤ (1 / poincareDensity Ω w) ^ 2} := by
  have hl := s02_poincareDensity_pos hΩ hw
  ext q
  refine and_congr_right fun hq => ?_
  have hξ : 0 < q.2 := hq
  unfold horoPhi
  rw [div_le_one (by positivity)]
  generalize poincareDensity Ω w = l at hl ⊢
  have key : ‖q.1 - w‖ ^ 2 + (q.2 - 1 / l) ^ 2 - (1 / l) ^ 2 =
      (l * (‖q.1 - w‖ ^ 2 + q.2 ^ 2) - 2 * q.2) / l := by
    field_simp
    ring
  constructor
  · intro h
    have : (l * (‖q.1 - w‖ ^ 2 + q.2 ^ 2) - 2 * q.2) / l ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hl.le
    linarith
  · intro h
    have h2 : (l * (‖q.1 - w‖ ^ 2 + q.2 ^ 2) - 2 * q.2) / l ≤ 0 := by linarith
    rw [div_le_iff₀ hl, zero_mul] at h2
    linarith

/-- Lemma 2.2 `lem:busemann`, (2.8) `eq:busemann-lip`, `sec02-prelim.tex:172`:
`|log Φ_q(w) - log Φ_{q'}(w)| ≤ d(q, q')`. -/
theorem lem_busemann {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) {q q' : ℂ × ℝ} (hq : q ∈ UHS) (hq' : q' ∈ UHS) :
    |Real.log (horoPhi Ω q w) - Real.log (horoPhi Ω q' w)| ≤ hdist q q' := by
  have hl := s02_poincareDensity_pos hΩ hw
  have hξ : 0 < q.2 := hq
  have hξ' : 0 < q'.2 := hq'
  unfold horoPhi
  set X := ‖q.1 - w‖ ^ 2 + q.2 ^ 2 with hX
  set X' := ‖q'.1 - w‖ ^ 2 + q'.2 ^ 2 with hX'
  have hXp : 0 < X := by positivity
  have hXp' : 0 < X' := by positivity
  set t := Real.log (poincareDensity Ω w * X / (2 * q.2)) -
    Real.log (poincareDensity Ω w * X' / (2 * q'.2)) with ht
  set R := X * q'.2 / (X' * q.2) with hR
  have hRpos : 0 < R := by positivity
  have hexp : Real.exp t = R := by
    rw [ht, Real.exp_sub, Real.exp_log (by positivity), Real.exp_log (by positivity), hR]
    field_simp
  have hcosh : Real.cosh t = (R + R⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg, hexp]
  -- the key inequality `cosh t ≤ cosh d(q, q')`
  have hkey : Real.cosh t ≤ coshDist q q' := by
    rw [hcosh]
    unfold coshDist
    have hn1 : ‖q.1 - q'.1‖ ^ 2 = (q.1.re - q'.1.re) ^ 2 + (q.1.im - q'.1.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have hn2 : X = (q.1.re - w.re) ^ 2 + (q.1.im - w.im) ^ 2 + q.2 ^ 2 := by
      rw [hX, Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have hn3 : X' = (q'.1.re - w.re) ^ 2 + (q'.1.im - w.im) ^ 2 + q'.2 ^ 2 := by
      rw [hX', Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have hdiff : 1 + (‖q.1 - q'.1‖ ^ 2 + (q.2 - q'.2) ^ 2) / (2 * q.2 * q'.2) - (R + R⁻¹) / 2 =
        ((X * (q'.1.re - w.re) - X' * (q.1.re - w.re)) ^ 2 +
          (X * (q'.1.im - w.im) - X' * (q.1.im - w.im)) ^ 2) / (2 * X * X' * q.2 * q'.2) := by
      rw [hR, hn1]
      field_simp
      rw [hn2, hn3]
      ring
    have : 0 ≤ ((X * (q'.1.re - w.re) - X' * (q.1.re - w.re)) ^ 2 +
        (X * (q'.1.im - w.im) - X' * (q.1.im - w.im)) ^ 2) / (2 * X * X' * q.2 * q'.2) := by
      positivity
    linarith
  unfold hdist
  rw [← Real.cosh_abs] at hkey
  have hc1 : 0 < Real.cosh |t| := Real.cosh_pos _
  rw [← Real.arcosh_cosh (abs_nonneg t)]
  exact (Real.arcosh_le_arcosh hc1 (lt_of_lt_of_le hc1 hkey)).2 hkey

/-- The inversion `invExt x₀` is an isometry of `ℍ³`: it preserves `cosh d`. -/
theorem s02_coshDist_invExt (x₀ : ℂ) {q p : ℂ × ℝ} (hq : 0 < q.2) (hp : 0 < p.2) :
    coshDist (invExt x₀ q) (invExt x₀ p) = coshDist q p := by
  unfold coshDist invExt
  dsimp only
  have hqp : q.1 - p.1 = (q.1 - x₀) - (p.1 - x₀) := by ring
  rw [hqp]
  generalize q.1 - x₀ = a
  generalize p.1 - x₀ = b
  generalize q.2 = s at hq ⊢
  generalize p.2 = t at hp ⊢
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.conj_re, Complex.conj_im]
  field_simp
  ring

/-- `invExt x₀` sends the point `(x₀ + c̄/(|c|² + h²), h/(|c|² + h²))` to `(c, h)`. -/
theorem s02_invExt_preimage (x₀ c : ℂ) {h : ℝ} (hh : 0 < h) :
    invExt x₀ (x₀ + conj c / ((‖c‖ ^ 2 + h ^ 2 : ℝ) : ℂ), h / (‖c‖ ^ 2 + h ^ 2)) = (c, h) := by
  have hM : 0 < ‖c‖ ^ 2 + h ^ 2 := by positivity
  have hMc : ((‖c‖ ^ 2 + h ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold invExt
  dsimp only
  rw [add_sub_cancel_left, norm_div, Complex.norm_conj, Complex.norm_real,
    Real.norm_of_nonneg hM.le]
  have hR : (‖c‖ / (‖c‖ ^ 2 + h ^ 2)) ^ 2 + (h / (‖c‖ ^ 2 + h ^ 2)) ^ 2 =
      1 / (‖c‖ ^ 2 + h ^ 2) := by
    field_simp
  rw [hR]
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [map_div₀, Complex.conj_conj, Complex.conj_ofReal]
    have hMc' : (‖c‖ : ℂ) ^ 2 + (h : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hM.ne'
    push_cast
    field_simp
  · dsimp only
    field_simp

/-- `Φ_q(w) = λ(w)/(2 ξ*)`, with `ξ*` the height of `invExt w q`. -/
theorem s02_horoPhi_invExt (Ω : Set ℂ) (w : ℂ) {q : ℂ × ℝ} (hq : 0 < q.2) :
    horoPhi Ω q w = poincareDensity Ω w / (2 * (invExt w q).2) := by
  unfold horoPhi invExt
  dsimp only
  have hR : 0 < ‖q.1 - w‖ ^ 2 + q.2 ^ 2 := by positivity
  field_simp

/-- Lemma 2.2 `lem:busemann`, `sec02-prelim.tex:175`: for `q ∉ B_w`, `d(q, B_w) = log Φ_q(w)`,
attained, and every nearest point of `B_w` lies on the geodesic ray from `q` to `w` (after the
inversion `invExt w`, which sends `w` to `∞`, the ray is the vertical ray going up from the image
of `q`). -/
theorem lem_busemann_nearest {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    {w : ℂ} (hw : w ∈ Ω) {q : ℂ × ℝ} (hq : q ∈ UHS) (hqB : q ∉ horoball Ω w) :
    hdistSet q (horoball Ω w) = Real.log (horoPhi Ω q w) ∧
      (∃ p ∈ horoball Ω w, hdist q p = Real.log (horoPhi Ω q w)) ∧
      ∀ p ∈ horoball Ω w, hdist q p = Real.log (horoPhi Ω q w) →
        (invExt w p).1 = (invExt w q).1 ∧ (invExt w q).2 ≤ (invExt w p).2 := by
  have hl := s02_poincareDensity_pos hΩ hw
  have hξ : 0 < q.2 := hq
  set l := poincareDensity Ω w with hldef
  set h := l / 2 with hhdef
  have hh : 0 < h := by positivity
  -- the height of `invExt w p` and the horoball
  have hht : ∀ p : ℂ × ℝ, 0 < p.2 → 0 < (invExt w p).2 := by
    intro p hp
    unfold invExt
    dsimp only
    positivity
  have hΦ : ∀ p : ℂ × ℝ, 0 < p.2 → horoPhi Ω p w = h / (invExt w p).2 := by
    intro p hp
    rw [s02_horoPhi_invExt Ω w hp, hhdef, div_div]
  have hBh : ∀ p ∈ horoball Ω w, h ≤ (invExt w p).2 := by
    intro p hpB
    have hp : 0 < p.2 := hpB.1
    have h1 := hpB.2
    rw [hΦ p hp, div_le_one (hht p hp)] at h1
    exact h1
  set s := (invExt w q).2 with hsdef
  have hs : 0 < s := hht q hξ
  have hsh : s < h := by
    have h1 : ¬ horoPhi Ω q w ≤ 1 := fun h1 => hqB ⟨hq, h1⟩
    rw [hΦ q hξ, div_le_one hs] at h1
    exact lt_of_not_ge h1
  have hΦq : horoPhi Ω q w = h / s := hΦ q hξ
  -- `cosh (log (h/s)) = 1 + (s - h)²/(2 s h)`
  have hlogpos : 0 < Real.log (h / s) := Real.log_pos ((one_lt_div hs).mpr hsh)
  have hcoshlog : Real.cosh (Real.log (h / s)) = 1 + (s - h) ^ 2 / (2 * s * h) := by
    rw [Real.cosh_log (by positivity)]
    field_simp
    ring
  -- lower bound
  have hlow : ∀ p ∈ horoball Ω w, Real.log (horoPhi Ω q w) ≤ hdist q p := by
    intro p hpB
    have hp : 0 < p.2 := hpB.1
    have hb := lem_busemann hΩ hw hq hpB.1
    have hΦp : 0 ≤ horoPhi Ω p w := by
      rw [hΦ p hp]
      exact (div_pos hh (hht p hp)).le
    have hlp : Real.log (horoPhi Ω p w) ≤ 0 := Real.log_nonpos hΦp hpB.2
    have := le_abs_self (Real.log (horoPhi Ω q w) - Real.log (horoPhi Ω p w))
    linarith
  -- the nearest point
  set c := (invExt w q).1 with hcdef
  set p₀ : ℂ × ℝ := (w + conj c / ((‖c‖ ^ 2 + h ^ 2 : ℝ) : ℂ), h / (‖c‖ ^ 2 + h ^ 2)) with hp₀
  have hp₀2 : 0 < p₀.2 := by
    rw [hp₀]
    dsimp only
    positivity
  have hinv₀ : invExt w p₀ = (c, h) := s02_invExt_preimage w c hh
  have hp₀B : p₀ ∈ horoball Ω w := by
    refine ⟨hp₀2, ?_⟩
    rw [hΦ p₀ hp₀2, hinv₀]
    dsimp only
    rw [div_self hh.ne']
  have hd₀ : hdist q p₀ = Real.log (horoPhi Ω q w) := by
    unfold hdist
    rw [← s02_coshDist_invExt w hξ hp₀2, hinv₀, hΦq, ← Real.arcosh_cosh hlogpos.le, hcoshlog]
    congr 1
    unfold coshDist
    rw [← hcdef, ← hsdef, sub_self, norm_zero]
    ring
  refine ⟨?_, ⟨p₀, hp₀B, hd₀⟩, ?_⟩
  · have hleast : IsLeast (hdist q '' horoball Ω w) (Real.log (horoPhi Ω q w)) := by
      refine ⟨⟨p₀, hp₀B, hd₀⟩, ?_⟩
      rintro x ⟨p, hpB, rfl⟩
      exact hlow p hpB
    exact hleast.csInf_eq
  · intro p hpB hdp
    have hp : 0 < p.2 := hpB.1
    have htB := hBh p hpB
    set t := (invExt w p).2 with htdef
    refine ⟨?_, by linarith⟩
    by_contra hne
    have hn : 0 < ‖c - (invExt w p).1‖ ^ 2 := by
      have : c - (invExt w p).1 ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0).symm
      positivity
    have hc1 : 1 ≤ coshDist q p := by
      unfold coshDist
      have : 0 ≤ (‖q.1 - p.1‖ ^ 2 + (q.2 - p.2) ^ 2) / (2 * q.2 * p.2) := by positivity
      linarith
    have hcd : coshDist q p = 1 + (s - h) ^ 2 / (2 * s * h) := by
      rw [← hcoshlog, ← hΦq, ← hdp]
      unfold hdist
      rw [Real.cosh_arcosh hc1]
    have ht : 0 < t := hht p hp
    have hst : s * s < t * h := by nlinarith
    have hmono : (s - h) ^ 2 / (2 * s * h) ≤ (s - t) ^ 2 / (2 * s * t) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.mpr htB) (sub_nonneg.mpr hst.le), hs]
    have hstrict : (s - t) ^ 2 / (2 * s * t) <
        (‖c - (invExt w p).1‖ ^ 2 + (s - t) ^ 2) / (2 * s * t) := by
      apply div_lt_div_of_pos_right _ (by positivity)
      linarith
    have hcd' : coshDist q p = 1 + (‖c - (invExt w p).1‖ ^ 2 + (s - t) ^ 2) / (2 * s * t) := by
      rw [← s02_coshDist_invExt w hξ hp]
      rfl
    linarith

/-! ## §2.4 The Epstein–Poincaré map -/

/-- `E(w, τ)` is the `invExt w`-preimage of the vertical point `(A, λ e^{-τ}/2)`. -/
theorem s02_invExt_normalGeod (Ω : Set ℂ) (w : ℂ) (hl : 0 < poincareDensity Ω w) (τ : ℝ) :
    invExt w (normalGeod Ω w τ) =
      (logDensityDz Ω w, poincareDensity Ω w * Real.exp (-τ) / 2) :=
  s02_invExt_preimage w _ (by positivity)

/-- The height of `E(w, τ)` is positive. -/
theorem s02_normalGeod_pos (Ω : Set ℂ) (w : ℂ) (hl : 0 < poincareDensity Ω w) (τ : ℝ) :
    0 < (normalGeod Ω w τ).2 := by
  unfold normalGeod
  dsimp only
  positivity

/-- `Φ_{E(w,τ)}(w) = e^τ`. -/
theorem s02_horoPhi_normalGeod (Ω : Set ℂ) (w : ℂ) (hl : 0 < poincareDensity Ω w) (τ : ℝ) :
    horoPhi Ω (normalGeod Ω w τ) w = Real.exp τ := by
  rw [s02_horoPhi_invExt Ω w (s02_normalGeod_pos Ω w hl τ), s02_invExt_normalGeod Ω w hl τ]
  dsimp only
  rw [Real.exp_neg]
  field_simp

/-- `log λ` is real-differentiable on `Ω`. -/
theorem s02_differentiableAt_logDensity {Ω : Set ℂ}
    (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ} (hw : w ∈ Ω) :
    DifferentiableAt ℝ (fun x => Real.log (poincareDensity Ω x)) w := by
  obtain ⟨f, hf⟩ := hΩ
  set ψ := Function.invFunOn f unitDisc with hψdef
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hψ : IsConformalOnto ψ Ω unitDisc := hf.symm isOpen_ball
  have hψU : ∀ x ∈ Ω, ‖ψ x‖ < 1 := by
    intro x hx
    have hmem := mem_image_of_mem ψ hx
    rw [hψ.2.2] at hmem
    exact mem_ball_zero_iff.mp hmem
  have hψ'ne : ∀ x ∈ Ω, deriv ψ x ≠ 0 := fun x hx =>
    deriv_ne_zero_of_injOn hΩo hψ.1 hψ.2.1 hx
  have hψA : AnalyticAt ℂ ψ w := hψ.1.analyticAt (hΩo.mem_nhds hw)
  have hψd : DifferentiableAt ℂ ψ w := hψA.differentiableAt
  have hψ'd : DifferentiableAt ℂ (deriv ψ) w := hψA.deriv.differentiableAt
  obtain ⟨L1, h1, -⟩ := s02_hasFDerivAt_log_normSq hψ'd.hasDerivAt (hψ'ne w hw)
  obtain ⟨L2, h2, -⟩ := s02_hasFDerivAt_log_one_sub_normSq hψd.hasDerivAt (hψU w hw)
  have hF : HasFDerivAt (fun x => Real.log 2 + (1 / 2 : ℝ) • Real.log (‖deriv ψ x‖ ^ 2) -
      Real.log (1 - ‖ψ x‖ ^ 2)) ((1 / 2 : ℝ) • L1 - L2) w :=
    ((h1.const_smul (1 / 2 : ℝ)).const_add (Real.log 2)).sub h2
  have heq : (fun x => Real.log (poincareDensity Ω x)) =ᶠ[𝓝 w]
      fun x => Real.log 2 + (1 / 2 : ℝ) • Real.log (‖deriv ψ x‖ ^ 2) -
        Real.log (1 - ‖ψ x‖ ^ 2) := by
    filter_upwards [hΩo.mem_nhds hw] with x hx
    have hr : (0 : ℝ) < 1 - ‖ψ x‖ ^ 2 := by nlinarith [norm_nonneg (ψ x), hψU x hx]
    have hn : 0 < ‖deriv ψ x‖ := norm_pos_iff.mpr (hψ'ne x hx)
    rw [s02_poincareDensity_eq_inv hf hx, ← hψdef, Real.log_div (by positivity) hr.ne',
      Real.log_mul (by norm_num) hn.ne', Real.log_pow, smul_eq_mul]
    push_cast
    ring
  exact (hF.congr_of_eventuallyEq heq).differentiableAt

/-- The real derivative of `φ : ℂ → ℝ` in terms of its Wirtinger derivative:
`Dφ(v) = Re(2 ∂φ · v)`. -/
theorem s02_fderiv_eq_wirtinger (φ : ℂ → ℝ) (w v : ℂ) :
    fderiv ℝ φ w v = (2 * wirtingerDz φ w * v).re := by
  have hv : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • I := by
    rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  unfold wirtingerDz
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- `invExt x₀` is inverted by the explicit preimage formula on `ℍ³`. -/
theorem s02_invExt_inv (x₀ : ℂ) {q : ℂ × ℝ} (hq : 0 < q.2) :
    (x₀ + conj (invExt x₀ q).1 /
        ((‖(invExt x₀ q).1‖ ^ 2 + (invExt x₀ q).2 ^ 2 : ℝ) : ℂ),
      (invExt x₀ q).2 / (‖(invExt x₀ q).1‖ ^ 2 + (invExt x₀ q).2 ^ 2)) = q := by
  obtain ⟨W, ξ⟩ := q
  dsimp only at hq ⊢
  unfold invExt
  dsimp only
  obtain ⟨u, rfl⟩ : ∃ u, W = x₀ + u := ⟨W - x₀, by ring⟩
  rw [add_sub_cancel_left]
  have hR : 0 < ‖u‖ ^ 2 + ξ ^ 2 := by positivity
  rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hR.le]
  have hS : (‖u‖ / (‖u‖ ^ 2 + ξ ^ 2)) ^ 2 + (ξ / (‖u‖ ^ 2 + ξ ^ 2)) ^ 2 =
      1 / (‖u‖ ^ 2 + ξ ^ 2) := by
    field_simp
  rw [hS]
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [map_div₀, Complex.conj_conj, Complex.conj_ofReal]
    have hRc : (‖u‖ : ℂ) ^ 2 + (ξ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hR.ne'
    push_cast
    field_simp
  · dsimp only
    field_simp

/-- The real derivative of `w' ↦ Φ_q(w')` at `w`: `v ↦ (λ/ξ) Re((A R - conj(W - w)) v)` with
`R = |W - w|² + ξ²`. -/
theorem s02_hasFDerivAt_horoPhi {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    {w : ℂ} (hw : w ∈ Ω) {q : ℂ × ℝ} (hq : 0 < q.2) :
    ∃ D : ℂ →L[ℝ] ℝ, HasFDerivAt (fun w' => horoPhi Ω q w') D w ∧
      ∀ v, D v = poincareDensity Ω w / q.2 *
        ((logDensityDz Ω w * ((‖q.1 - w‖ ^ 2 + q.2 ^ 2 : ℝ) : ℂ) - conj (q.1 - w)) * v).re := by
  have hl := s02_poincareDensity_pos hΩ hw
  obtain ⟨f, hf⟩ := hΩ
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hlogD := (s02_differentiableAt_logDensity ⟨f, hf⟩ hw).hasFDerivAt
  have hleq : poincareDensity Ω =ᶠ[𝓝 w] fun x => Real.exp (Real.log (poincareDensity Ω x)) := by
    filter_upwards [hΩo.mem_nhds hw] with x hx
    rw [Real.exp_log (s02_poincareDensity_pos ⟨f, hf⟩ hx)]
  have hlD := hlogD.exp.congr_of_eventuallyEq hleq
  have hsub : HasDerivAt (fun x => q.1 - x) (-1) w := (hasDerivAt_id w).const_sub q.1
  obtain ⟨Lr, hLr, hLrv⟩ := s02_hasFDerivAt_normSq hsub
  have hΦD := (hlD.mul (hLr.add_const (q.2 ^ 2))).mul_const ((2 * q.2)⁻¹)
  have hfun : (fun w' => horoPhi Ω q w') =
      fun y => poincareDensity Ω y * (‖q.1 - y‖ ^ 2 + q.2 ^ 2) * (2 * q.2)⁻¹ := by
    funext y
    unfold horoPhi
    rw [div_eq_mul_inv]
  rw [hfun]
  refine ⟨_, hΦD, fun v => ?_⟩
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
  rw [hLrv, Real.exp_log hl, s02_fderiv_eq_wirtinger]
  unfold logDensityDz
  generalize wirtingerDz (fun x => Real.log (poincareDensity Ω x)) w = A
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat]
  field_simp
  ring

/-- The critical set of `w' ↦ Φ_q(w')` at `w` is `range (E(w, ·))` (body of `lem_normal_a`). -/
theorem s02_critSet_eq {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) :
    {q | q ∈ UHS ∧ HasFDerivAt (fun w' => horoPhi Ω q w') (0 : ℂ →L[ℝ] ℝ) w} =
      range (normalGeod Ω w) := by
  have hl := s02_poincareDensity_pos hΩ hw
  -- `conj (W - w) = (invExt w q).1 · R`
  have hcu : ∀ q : ℂ × ℝ, 0 < q.2 →
      conj (q.1 - w) = (invExt w q).1 * ((‖q.1 - w‖ ^ 2 + q.2 ^ 2 : ℝ) : ℂ) := by
    intro q hq
    have hR : ((‖q.1 - w‖ ^ 2 + q.2 ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have : 0 < ‖q.1 - w‖ ^ 2 + q.2 ^ 2 := by positivity
      exact_mod_cast this.ne'
    unfold invExt
    dsimp only
    rw [div_mul_cancel₀ _ hR]
  ext q
  constructor
  · rintro ⟨hq, h0⟩
    have hq2 : 0 < q.2 := hq
    obtain ⟨D, hD, hDv⟩ := s02_hasFDerivAt_horoPhi hΩ hw hq2
    have hD0 : D = 0 := hD.unique h0
    set z := logDensityDz Ω w * ((‖q.1 - w‖ ^ 2 + q.2 ^ 2 : ℝ) : ℂ) - conj (q.1 - w) with hz
    have hz0 : z = 0 := by
      have h1 := hDv (conj z)
      rw [hD0, ContinuousLinearMap.zero_apply, Complex.mul_conj, Complex.ofReal_re] at h1
      have hc : poincareDensity Ω w / q.2 ≠ 0 := (div_pos hl hq2).ne'
      have h2 : Complex.normSq z = 0 := by
        rcases mul_eq_zero.mp h1.symm with h | h
        · exact absurd h hc
        · exact h
      exact Complex.normSq_eq_zero.mp h2
    have hR : ((‖q.1 - w‖ ^ 2 + q.2 ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have : 0 < ‖q.1 - w‖ ^ 2 + q.2 ^ 2 := by positivity
      exact_mod_cast this.ne'
    have hc1 : (invExt w q).1 = logDensityDz Ω w := by
      have h1 := hcu q hq2
      rw [hz, sub_eq_zero, h1] at hz0
      exact (mul_right_cancel₀ hR hz0).symm
    have hΦ := s02_horoPhi_invExt Ω w hq2
    have hh0 : 0 < (invExt w q).2 := by
      unfold invExt
      dsimp only
      positivity
    have hΦpos : 0 < horoPhi Ω q w := by
      rw [hΦ]
      positivity
    refine ⟨Real.log (horoPhi Ω q w), ?_⟩
    have hhτ : poincareDensity Ω w * Real.exp (-Real.log (horoPhi Ω q w)) / 2 =
        (invExt w q).2 := by
      rw [Real.exp_neg, Real.exp_log hΦpos, hΦ]
      field_simp
    conv_rhs => rw [← s02_invExt_inv w hq2]
    unfold normalGeod
    rw [hhτ, hc1]
  · rintro ⟨τ, rfl⟩
    have hq2 := s02_normalGeod_pos Ω w hl τ
    refine ⟨hq2, ?_⟩
    obtain ⟨D, hD, hDv⟩ := s02_hasFDerivAt_horoPhi hΩ hw hq2
    have hD0 : D = 0 := by
      ext v
      rw [hDv, hcu _ hq2, s02_invExt_normalGeod Ω w hl τ]
      simp
    rw [← hD0]
    exact hD

/-- `E(w, 0) = X(w)`. -/
theorem s02_normalGeod_zero (Ω : Set ℂ) (w : ℂ) (hl : 0 < poincareDensity Ω w) :
    normalGeod Ω w 0 = epstein Ω w := by
  unfold normalGeod epstein
  rw [neg_zero, Real.exp_zero, mul_one]
  generalize poincareDensity Ω w = l at hl ⊢
  generalize logDensityDz Ω w = A
  have hD : 0 < l ^ 2 + 4 * ‖A‖ ^ 2 := by positivity
  have hq : ‖A‖ ^ 2 + (l / 2) ^ 2 = (l ^ 2 + 4 * ‖A‖ ^ 2) / 4 := by ring
  rw [hq]
  refine Prod.ext ?_ ?_
  · dsimp only
    have hDc : ((l ^ 2 + 4 * ‖A‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    rw [Complex.ofReal_div]
    generalize ((l ^ 2 + 4 * ‖A‖ ^ 2 : ℝ) : ℂ) = Dc at hDc ⊢
    push_cast
    field_simp
  · dsimp only
    field_simp
    ring

/-- (2.9) `eq:epstein`, `sec02-prelim.tex:201`: `X(w)` is the unique point `q ∈ ∂B_w` at which
`w' ↦ Φ_q(w')` has a critical point at `w' = w`. -/
theorem eq_epstein {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) :
    {q | q ∈ UHS ∧ horoPhi Ω q w = 1 ∧
      HasFDerivAt (fun w' => horoPhi Ω q w') (0 : ℂ →L[ℝ] ℝ) w} = {epstein Ω w} := by
  have hl := s02_poincareDensity_pos hΩ hw
  have hcrit := s02_critSet_eq hΩ hw
  ext q
  constructor
  · rintro ⟨hq, h1, h0⟩
    have hm : q ∈ {q | q ∈ UHS ∧ HasFDerivAt (fun w' => horoPhi Ω q w') (0 : ℂ →L[ℝ] ℝ) w} :=
      ⟨hq, h0⟩
    rw [hcrit] at hm
    obtain ⟨τ, rfl⟩ := hm
    rw [s02_horoPhi_normalGeod Ω w hl τ, Real.exp_eq_one_iff] at h1
    rw [h1, s02_normalGeod_zero Ω w hl]
    exact mem_singleton _
  · intro hq
    rw [mem_singleton_iff] at hq
    subst hq
    have hm : normalGeod Ω w 0 ∈
        {q | q ∈ UHS ∧ HasFDerivAt (fun w' => horoPhi Ω q w') (0 : ℂ →L[ℝ] ℝ) w} := by
      rw [hcrit]
      exact ⟨0, rfl⟩
    rw [s02_normalGeod_zero Ω w hl] at hm
    refine ⟨hm.1, ?_, hm.2⟩
    rw [← s02_normalGeod_zero Ω w hl, s02_horoPhi_normalGeod Ω w hl 0, Real.exp_zero]

/-- (2.10) `eq:epstein-disk`, `sec02-prelim.tex:211`:
`Ep_𝔻(z) = (2z/(1+|z|²), (1-|z|²)/(1+|z|²))`; it parametrizes the totally geodesic plane
`{|W|² + ξ² = 1}` bounded by `∂𝔻`, and `Ep_𝔻(0) = j`. -/
theorem eq_epstein_disk :
    (∀ z ∈ unitDisc, epstein unitDisc z =
      (2 * z / ((1 + ‖z‖ ^ 2 : ℝ) : ℂ), (1 - ‖z‖ ^ 2) / (1 + ‖z‖ ^ 2))) ∧
      epstein unitDisc '' unitDisc = {q | q ∈ UHS ∧ ‖q.1‖ ^ 2 + q.2 ^ 2 = 1} ∧
      epstein unitDisc 0 = jPt := by
  have hid : IsConformalOnto (id : ℂ → ℂ) unitDisc unitDisc :=
    ⟨differentiableOn_id, injOn_id _, image_id _⟩
  have hform : ∀ z ∈ unitDisc, epstein unitDisc z =
      (2 * z / ((1 + ‖z‖ ^ 2 : ℝ) : ℂ), (1 - ‖z‖ ^ 2) / (1 + ‖z‖ ^ 2)) := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have ht : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have hl : poincareDensity unitDisc z = 2 / (1 - ‖z‖ ^ 2) := by
      have := eq_lambda_f hid hz
      rw [deriv_id, norm_one, mul_one] at this
      exact this
    have hA : logDensityDz unitDisc z = conj z / ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
      have h := s02_logDensityDz_mul_deriv hid hz
      simp only [deriv_id', deriv_const', mul_one, zero_div, sub_zero, id] at h
      exact h
    have hnA : ‖logDensityDz unitDisc z‖ = ‖z‖ / (1 - ‖z‖ ^ 2) := by
      rw [hA, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    unfold epstein
    rw [hnA, hl, hA, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
    generalize ‖z‖ = n at ht ⊢
    have hp : (0 : ℝ) < 1 + n ^ 2 := by positivity
    have hDr : (2 / (1 - n ^ 2)) ^ 2 + 4 * (n / (1 - n ^ 2)) ^ 2 =
        4 * (1 + n ^ 2) / (1 - n ^ 2) ^ 2 := by
      field_simp
      ring
    rw [hDr]
    refine Prod.ext ?_ ?_
    · dsimp only
      have hc1 : (1 - (n : ℂ) ^ 2) ≠ 0 := by exact_mod_cast ht.ne'
      have hc2 : (1 + (n : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hp.ne'
      push_cast
      field_simp
      ring
    · dsimp only
      field_simp
      ring
  refine ⟨hform, ?_, ?_⟩
  · ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hform z hz]
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      have ht : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      have hp : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
      refine ⟨div_pos ht hp, ?_⟩
      dsimp only
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp,
        Complex.norm_two]
      field_simp
      ring
    · obtain ⟨W, ξ⟩ := q
      rintro ⟨hq, hs⟩
      have hξ : 0 < ξ := hq
      dsimp only at hs
      have hp : 0 < 1 + ξ := by linarith
      have hWlt : ‖W‖ < 1 + ξ := by
        refine lt_of_pow_lt_pow_left₀ 2 hp.le ?_
        nlinarith
      set z : ℂ := W / ((1 + ξ : ℝ) : ℂ) with hzdef
      have hnz : ‖z‖ = ‖W‖ / (1 + ξ) := by
        rw [hzdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
      have hz : z ∈ unitDisc := by
        refine mem_ball_zero_iff.mpr ?_
        rw [hnz, div_lt_one hp]
        exact hWlt
      refine ⟨z, hz, ?_⟩
      rw [hform z hz]
      have hn2 : ‖z‖ ^ 2 = (1 - ξ) / (1 + ξ) := by
        rw [hnz, div_pow]
        field_simp
        nlinarith
      rw [hn2]
      refine Prod.ext ?_ ?_
      · dsimp only
        have hc : ((1 + ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
        rw [hzdef]
        push_cast
        have hc' : (1 + (ξ : ℂ)) ≠ 0 := by exact_mod_cast hp.ne'
        field_simp
        ring
      · dsimp only
        field_simp
        ring
  · rw [hform 0 (mem_ball_self one_pos)]
    simp [jPt]

/-- Möbius transformation law of `A = ∂ log λ`: for `M(w) = (αw + β)/(γw + δ)` with no pole on
`Ω`, `A_{M(Ω)}(M w) M'(w) = A_Ω(w) + γ/(γw + δ)`. -/
theorem s02_mobius_natural_A {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    {α β γ δ : ℂ} (hdet : α * δ - β * γ ≠ 0) (hden : ∀ w ∈ Ω, γ * w + δ ≠ 0) {w : ℂ}
    (hw : w ∈ Ω) :
    logDensityDz ((fun v => (α * v + β) / (γ * v + δ)) '' Ω) ((α * w + β) / (γ * w + δ)) *
        ((α * δ - β * γ) / (γ * w + δ) ^ 2) = logDensityDz Ω w + γ / (γ * w + δ) := by
  obtain ⟨f, hf⟩ := hΩ
  obtain ⟨z, hz, rfl⟩ : w ∈ f '' unitDisc := by rw [hf.2.2]; exact hw
  set M : ℂ → ℂ := fun v => (α * v + β) / (γ * v + δ) with hMdef
  have hfm : MapsTo f unitDisc Ω := by
    intro ζ hζ
    rw [← hf.2.2]
    exact mem_image_of_mem f hζ
  have hMd : DifferentiableOn ℂ M Ω := by
    intro v hv
    exact ((hasDerivAt_mobius (a := α) (b := β) (hden v hv)).differentiableAt).differentiableWithinAt
  have hMi : InjOn M Ω := by
    intro v₁ h₁ v₂ h₂ he
    have hd₁ := hden v₁ h₁
    have hd₂ := hden v₂ h₂
    simp only [hMdef] at he
    rw [div_eq_div_iff hd₁ hd₂] at he
    have : (α * δ - β * γ) * (v₁ - v₂) = 0 := by linear_combination he
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hdet
    · exact sub_eq_zero.mp h
  have hF : IsConformalOnto (fun ζ => (α * f ζ + β) / (γ * f ζ + δ)) unitDisc (M '' Ω) := by
    refine ⟨hMd.comp hf.1 hfm, hMi.comp hf.2.1 hfm, ?_⟩
    rw [show (fun ζ => (α * f ζ + β) / (γ * f ζ + δ)) = M ∘ f from rfl, Set.image_comp, hf.2.2]
  have hU : unitDisc ∈ 𝓝 z := isOpen_ball.mem_nhds hz
  have hfd : DifferentiableAt ℂ f z := hf.1.differentiableAt hU
  have hf' : deriv f z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz
  have hd0 := hden (f z) (hfm hz)
  have hDF : deriv (fun ζ => (α * f ζ + β) / (γ * f ζ + δ)) =ᶠ[𝓝 z]
      fun ζ => (α * δ - β * γ) / ((γ * f ζ + δ) * (γ * f ζ + δ)) * deriv f ζ := by
    filter_upwards [hU] with ζ hζ
    have hc : deriv (fun ζ => (α * f ζ + β) / (γ * f ζ + δ)) ζ =
        (α * δ - β * γ) / (γ * f ζ + δ) ^ 2 * deriv f ζ :=
      ((hasDerivAt_mobius (a := α) (b := β) (hden _ (hfm hζ))).comp ζ
        (hf.1.differentiableAt (isOpen_ball.mem_nhds hζ)).hasDerivAt).deriv
    rw [hc, sq]
  have hf2 : HasDerivAt (deriv f) (deriv (deriv f) z) z :=
    (hf.1.analyticAt hU).deriv.differentiableAt.hasDerivAt
  have hg : HasDerivAt (fun ζ => γ * f ζ + δ) (γ * deriv f z) z :=
    (hfd.hasDerivAt.const_mul γ).add_const δ
  have hK : HasDerivAt (fun ζ => (α * δ - β * γ) / ((γ * f ζ + δ) * (γ * f ζ + δ)) * deriv f ζ)
      (((0 * ((γ * f z + δ) * (γ * f z + δ)) - (α * δ - β * γ) *
          (γ * deriv f z * (γ * f z + δ) + (γ * f z + δ) * (γ * deriv f z))) /
          ((γ * f z + δ) * (γ * f z + δ)) ^ 2) * deriv f z +
        (α * δ - β * γ) / ((γ * f z + δ) * (γ * f z + δ)) * deriv (deriv f) z) z :=
    ((hasDerivAt_const z (α * δ - β * γ)).div (hg.mul hg) (mul_ne_zero hd0 hd0)).mul hf2
  have hF1 := hDF.eq_of_nhds
  have hF2 := hDF.deriv_eq.trans hK.deriv
  have h1 := s02_logDensityDz_mul_deriv hF hz
  have h2 := s02_logDensityDz_mul_deriv hf hz
  rw [hF1, hF2] at h1
  generalize logDensityDz (M '' Ω) ((α * f z + β) / (γ * f z + δ)) = X at h1 ⊢
  generalize logDensityDz Ω (f z) = Y at h2 ⊢
  generalize conj z / ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) = c at h1 h2
  generalize deriv (deriv f) z = s at h1 h2
  generalize deriv f z = p at h1 h2 hf' ⊢
  generalize γ * f z + δ = g at h1 hd0 ⊢
  have key : ((0 * (g * g) - (α * δ - β * γ) * (γ * p * g + g * (γ * p))) / (g * g) ^ 2 * p +
      (α * δ - β * γ) / (g * g) * s) / (2 * ((α * δ - β * γ) / (g * g) * p)) =
      s / (2 * p) - γ * p / g := by
    field_simp
    ring
  rw [key] at h1
  apply mul_right_cancel₀ hf'
  have h1' : X * ((α * δ - β * γ) / (g * g) * p) = X * ((α * δ - β * γ) / g ^ 2) * p := by ring
  rw [h1'] at h1
  linear_combination h1 - h2

/-- §2.4, `sec02-prelim.tex:216`: naturality `Ep_{M(Ω)} ∘ M = M ∘ Ep_Ω` for a similarity
`M(z) = a z + b`, whose Poincaré extension is `(W, ξ) ↦ (a W + b, |a| ξ)`. -/
theorem subsec_epstein_natural_affine {Ω : Set ℂ}
    (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {a b : ℂ} (ha : a ≠ 0) {w : ℂ}
    (hw : w ∈ Ω) :
    epstein ((fun z => a * z + b) '' Ω) (a * w + b) =
      (a * (epstein Ω w).1 + b, ‖a‖ * (epstein Ω w).2) := by
  have hlam := (subsec_poincare_natural_affine hΩ (b := b) ha hw).1
  have hA := s02_mobius_natural_A (α := a) (β := b) (γ := 0) (δ := 1) hΩ (by simpa using ha)
    (fun _ _ => by simp) hw
  simp only [zero_mul, zero_add, div_one, mul_one, mul_zero, sub_zero, one_pow,
    add_zero] at hA
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hlam' : poincareDensity ((fun z => a * z + b) '' Ω) (a * w + b) =
      poincareDensity Ω w / ‖a‖ := eq_div_of_mul_eq hna hlam
  have hA' : logDensityDz ((fun z => a * z + b) '' Ω) (a * w + b) = logDensityDz Ω w / a :=
    eq_div_of_mul_eq ha hA
  have hl0 := s02_poincareDensity_pos hΩ hw
  unfold epstein
  rw [hlam', hA', norm_div]
  generalize poincareDensity Ω w = l at hl0 ⊢
  generalize logDensityDz Ω w = A
  have hD : 0 < l ^ 2 + 4 * ‖A‖ ^ 2 := by positivity
  have hden' : (l / ‖a‖) ^ 2 + 4 * (‖A‖ / ‖a‖) ^ 2 = (l ^ 2 + 4 * ‖A‖ ^ 2) / ‖a‖ ^ 2 := by ring
  rw [hden']
  refine Prod.ext ?_ ?_
  · dsimp only
    have hsq : ((‖a‖ : ℂ)) ^ 2 = a * conj a := (mul_conj' a).symm
    have hca : conj a ≠ 0 := (map_ne_zero _).mpr ha
    have hDc : ((l ^ 2 + 4 * ‖A‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    rw [map_div₀, Complex.ofReal_div, Complex.ofReal_pow, hsq]
    generalize ((l ^ 2 + 4 * ‖A‖ ^ 2 : ℝ) : ℂ) = Dc at hDc ⊢
    field_simp
    ring
  · dsimp only
    field_simp

/-- §2.4, `sec02-prelim.tex:216`: naturality `Ep_{M(Ω)} ∘ M = M ∘ Ep_Ω` for the inversion
`M = invAt x₀` (`x₀ ∉ Ω`), with Poincaré extension `invExt x₀`. -/
theorem subsec_epstein_natural_inv {Ω : Set ℂ}
    (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {x₀ : ℂ} (hx₀ : x₀ ∉ Ω) {w : ℂ}
    (hw : w ∈ Ω) :
    epstein (invAt x₀ '' Ω) (invAt x₀ w) = invExt x₀ (epstein Ω w) := by
  have hden : ∀ v ∈ Ω, (1 : ℂ) * v + -x₀ ≠ 0 := by
    intro v hv h
    apply hx₀
    have : v = x₀ := by linear_combination h
    rw [← this]
    exact hv
  have hu0 : w - x₀ ≠ 0 := by
    intro h
    apply hx₀
    rw [← sub_eq_zero.mp h]
    exact hw
  have hlam := (subsec_poincare_natural_inv hΩ hx₀ hw).1
  have hA := s02_mobius_natural_A (α := 0) (β := 1) (γ := 1) (δ := -x₀) hΩ (by norm_num) hden hw
  have hfun : (fun v => (0 * v + 1) / (1 * v + -x₀)) = invAt x₀ := by
    funext v
    simp [invAt, sub_eq_add_neg]
  have hinv : (0 * w + 1) / (1 * w + -x₀) = invAt x₀ w := by
    rw [← hfun]
  have hM' : (0 * -x₀ - 1 * 1 : ℂ) / (1 * w + -x₀) ^ 2 = -1 / (w - x₀) ^ 2 := by ring
  have hM'' : (1 : ℂ) / (1 * w + -x₀) = 1 / (w - x₀) := by ring
  rw [hfun, hinv, hM', hM''] at hA
  have hA' : logDensityDz (invAt x₀ '' Ω) (invAt x₀ w) =
      -(w - x₀) ^ 2 * logDensityDz Ω w - (w - x₀) := by
    calc logDensityDz (invAt x₀ '' Ω) (invAt x₀ w)
        = logDensityDz (invAt x₀ '' Ω) (invAt x₀ w) * (-1 / (w - x₀) ^ 2) * (-(w - x₀) ^ 2) := by
          field_simp
      _ = (logDensityDz Ω w + 1 / (w - x₀)) * (-(w - x₀) ^ 2) := by rw [hA]
      _ = -(w - x₀) ^ 2 * logDensityDz Ω w - (w - x₀) := by
          field_simp
          ring
  have hlam' : poincareDensity (invAt x₀ '' Ω) (invAt x₀ w) =
      poincareDensity Ω w * ‖w - x₀‖ ^ 2 :=
    (div_eq_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr hu0))).mp hlam
  have hl0 := s02_poincareDensity_pos hΩ hw
  unfold epstein invExt
  rw [hlam', hA', show invAt x₀ w = (w - x₀)⁻¹ from rfl]
  dsimp only
  rw [add_sub_right_comm]
  generalize poincareDensity Ω w = l at hl0 ⊢
  generalize logDensityDz Ω w = A
  generalize w - x₀ = u at hu0 ⊢
  have hD0 : 0 < l ^ 2 + 4 * ‖A‖ ^ 2 := by positivity
  generalize hDd : l ^ 2 + 4 * ‖A‖ ^ 2 = D at hD0 ⊢
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD0.ne'
  have hDdef : (D : ℂ) = (l : ℂ) ^ 2 + 4 * (A * conj A) := by
    rw [← hDd, mul_conj']
    push_cast
    ring
  have hN2 : ((u + 4 * conj A / (D : ℂ)) * (conj u + 4 * A / (D : ℂ)) + (2 * (l : ℂ) / D) ^ 2) *
      (D : ℂ) ^ 2 = (u * D + 4 * conj A) * (conj u * D + 4 * A) + 4 * (l : ℂ) ^ 2 := by
    field_simp
    ring
  have hN0 : 0 < ‖u + 4 * conj A / (D : ℂ)‖ ^ 2 + (2 * l / D) ^ 2 := by positivity
  have K : (l * ‖u‖ ^ 2) ^ 2 + 4 * ‖-u ^ 2 * A - u‖ ^ 2 =
      ‖u‖ ^ 2 * D * (‖u + 4 * conj A / (D : ℂ)‖ ^ 2 + (2 * l / D) ^ 2) := by
    apply Complex.ofReal_injective
    push_cast
    simp only [← mul_conj', map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, conj_conj,
      Complex.conj_ofReal, map_ofNat]
    apply mul_right_cancel₀ hDc
    linear_combination (4 * u * conj u - u ^ 2 * conj u ^ 2 * D) * hDdef - u * conj u * hN2
  have hNc : ((‖u + 4 * conj A / (D : ℂ)‖ ^ 2 + (2 * l / D) ^ 2 : ℝ) : ℂ) * (D : ℂ) =
      u * conj u * (D : ℂ) + 4 * u * A + 4 * conj u * conj A + 4 := by
    push_cast
    simp only [← mul_conj', map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, conj_conj,
      Complex.conj_ofReal, map_ofNat]
    apply mul_right_cancel₀ hDc
    linear_combination (-4 : ℂ) * hDdef + hN2
  generalize ‖u + 4 * conj A / (D : ℂ)‖ ^ 2 + (2 * l / D) ^ 2 = N at hN0 K hNc ⊢
  rw [K]
  have hun : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
  have hDne : D ≠ 0 := hD0.ne'
  have hNne : N ≠ 0 := hN0.ne'
  refine Prod.ext ?_ ?_
  · dsimp only
    have hNc0 : (N : ℂ) ≠ 0 := by exact_mod_cast hNne
    have hcu : conj u ≠ 0 := (map_ne_zero _).mpr hu0
    push_cast
    simp only [← mul_conj', map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, conj_conj,
      Complex.conj_ofReal, map_ofNat]
    calc _ = ((D : ℂ) * N - 4 * conj u * conj A - 4) / (u * D * N) := by
          field_simp
          ring
      _ = (u * conj u * D + 4 * u * A) / (u * D * N) := by
          congr 1
          linear_combination hNc
      _ = _ := by
          field_simp
  · dsimp only
    field_simp

/-- Position of `X(w)` (body of `lem_ep_position`). -/
theorem s02_ep_position {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) :
    2 / (5 * poincareDensity Ω w) ≤ (epstein Ω w).2 ∧
      (epstein Ω w).2 ≤ 2 / poincareDensity Ω w ∧
      ‖(epstein Ω w).1 - w‖ ≤ 1 / poincareDensity Ω w ∧
      infDist w Ωᶜ / 5 ≤ (epstein Ω w).2 ∧ (epstein Ω w).2 ≤ 4 * infDist w Ωᶜ ∧
      ‖(epstein Ω w).1 - w‖ ≤ 2 * infDist w Ωᶜ := by
  have hl := s02_poincareDensity_pos hΩ hw
  obtain ⟨f, hf⟩ := hΩ
  obtain ⟨z, hz, rfl⟩ : w ∈ f '' unitDisc := by rw [hf.2.2]; exact hw
  have hA := (lem_koebe_b hf hz).2
  obtain ⟨-, -, hd1, hd2⟩ := lem_koebe_a hf hz
  have hd := s02_infDist_pos hf hw
  set l := poincareDensity Ω (f z) with hldef
  set a := ‖logDensityDz Ω (f z)‖ with hadef
  set d := infDist (f z) Ωᶜ
  have ha0 : 0 ≤ a := norm_nonneg _
  have hD : 0 < l ^ 2 + 4 * a ^ 2 := by positivity
  have hξ : (epstein Ω (f z)).2 = 2 * l / (l ^ 2 + 4 * a ^ 2) := rfl
  have hW : ‖(epstein Ω (f z)).1 - f z‖ = 4 * a / (l ^ 2 + 4 * a ^ 2) := by
    show ‖f z + 4 * conj (logDensityDz Ω (f z)) /
      ((poincareDensity Ω (f z) ^ 2 + 4 * ‖logDensityDz Ω (f z)‖ ^ 2 : ℝ) : ℂ) - f z‖ = _
    rw [add_sub_cancel_left, norm_div, norm_mul, Complex.norm_real, RCLike.norm_conj,
      Real.norm_of_nonneg hD.le]
    norm_num
    rw [hadef]
  -- the bounds in terms of `λ`
  have e1 : 2 / (5 * l) ≤ 2 * l / (l ^ 2 + 4 * a ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) hD]
    nlinarith
  have e2 : 2 * l / (l ^ 2 + 4 * a ^ 2) ≤ 2 / l := by
    rw [div_le_div_iff₀ hD hl]
    nlinarith
  have e3 : 4 * a / (l ^ 2 + 4 * a ^ 2) ≤ 1 / l := by
    rw [div_le_div_iff₀ hD hl]
    nlinarith [sq_nonneg (l - 2 * a)]
  -- `1/(2d) ≤ λ ≤ 2/d`
  have hl1 : 1 / l ≤ 2 * d := by
    rw [div_le_iff₀ hl]
    rw [div_le_iff₀ (by positivity)] at hd1
    linarith
  have hl2 : d / 2 ≤ 1 / l := by
    rw [le_div_iff₀ hl]
    rw [le_div_iff₀ hd] at hd2
    linarith
  rw [hξ, hW]
  refine ⟨e1, e2, e3, ?_, ?_, ?_⟩
  · have : d / 5 ≤ 2 / (5 * l) := by
      rw [show 2 / (5 * l) = 2 / 5 * (1 / l) by field_simp]
      linarith
    linarith
  · have : 2 / l ≤ 4 * d := by
      rw [show 2 / l = 2 * (1 / l) by ring]
      linarith
    linarith
  · linarith

/-- §2.4, `sec02-prelim.tex:218`: `X` extends continuously to `Γ` by the identity: `X(w) → (x, 0)`
as `w → x ∈ ∂Ω`, `w ∈ Ω`. -/
theorem subsec_epstein_boundary {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    {x : ℂ} (hx : x ∈ frontier Ω) :
    Tendsto (epstein Ω) (𝓝[Ω] x) (𝓝 (x, 0)) := by
  have hΩo : IsOpen Ω := by
    obtain ⟨f, hf⟩ := hΩ
    exact hf.isOpen isOpen_ball
  have hxc : x ∈ Ωᶜ := by
    intro h
    exact hx.2 (by rwa [hΩo.interior_eq])
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨ε / 4, by positivity, fun w hw hwd => ?_⟩
  obtain ⟨e0, -, -, -, e2, e3⟩ := s02_ep_position hΩ hw
  have hl := s02_poincareDensity_pos hΩ hw
  have hd : infDist w Ωᶜ ≤ ‖w - x‖ := by
    rw [← dist_eq_norm]
    exact infDist_le_dist_of_mem hxc
  rw [dist_eq_norm] at hwd
  have hpos : 0 < (epstein Ω w).2 := lt_of_lt_of_le (by positivity) e0
  rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, Real.dist_eq, sub_zero, abs_of_pos hpos]
  constructor
  · calc ‖(epstein Ω w).1 - x‖ = ‖((epstein Ω w).1 - w) + (w - x)‖ := by ring_nf
      _ ≤ ‖(epstein Ω w).1 - w‖ + ‖w - x‖ := norm_add_le _ _
      _ < ε := by linarith
  · linarith

/-- Lemma 2.3 `lem:ep-position`, (2.11) `eq:ep-position`, `sec02-prelim.tex:222`:
`2/(5λ) ≤ ξ_X ≤ 2/λ`, `|W_X - w| ≤ 1/λ`, hence `d/5 ≤ ξ_X ≤ 4d`, `|W_X - w| ≤ 2d`. -/
theorem lem_ep_position {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) :
    2 / (5 * poincareDensity Ω w) ≤ (epstein Ω w).2 ∧
      (epstein Ω w).2 ≤ 2 / poincareDensity Ω w ∧
      ‖(epstein Ω w).1 - w‖ ≤ 1 / poincareDensity Ω w ∧
      infDist w Ωᶜ / 5 ≤ (epstein Ω w).2 ∧ (epstein Ω w).2 ≤ 4 * infDist w Ωᶜ ∧
      ‖(epstein Ω w).1 - w‖ ≤ 2 * infDist w Ωᶜ := by
  exact s02_ep_position hΩ hw

/-- Lemma 2.4 `lem:normal`, `sec02-prelim.tex:242`: the set of `q ∈ ℍ³` at which `w` is a critical
point of `Φ_q` is the complete geodesic `γ_w = range (E(w, ·))` from `w` to `w + 1/A`. -/
theorem lem_normal_a {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) :
    {q | q ∈ UHS ∧ HasFDerivAt (fun w' => horoPhi Ω q w') (0 : ℂ →L[ℝ] ℝ) w} =
      range (normalGeod Ω w) := by
  exact s02_critSet_eq hΩ hw

/-- Lemma 2.4 `lem:normal`, `sec02-prelim.tex:245`: `τ ↦ E(w, τ)` is an arclength
parametrization of a geodesic of `ℍ³` with `E(w, 0) = X(w)`. -/
theorem lem_normal_b {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) :
    (∀ τ : ℝ, normalGeod Ω w τ ∈ UHS) ∧
      (∀ τ τ' : ℝ, hdist (normalGeod Ω w τ) (normalGeod Ω w τ') = |τ - τ'|) ∧
      normalGeod Ω w 0 = epstein Ω w := by
  have hl := s02_poincareDensity_pos hΩ hw
  refine ⟨fun τ => s02_normalGeod_pos Ω w hl τ, ?_, ?_⟩
  · intro τ τ'
    unfold hdist
    rw [← s02_coshDist_invExt w (s02_normalGeod_pos Ω w hl τ) (s02_normalGeod_pos Ω w hl τ'),
      s02_invExt_normalGeod Ω w hl τ, s02_invExt_normalGeod Ω w hl τ',
      ← Real.arcosh_cosh (abs_nonneg (τ - τ')), Real.cosh_abs]
    congr 1
    unfold coshDist
    dsimp only
    rw [sub_self, norm_zero, Real.cosh_eq]
    simp only [Real.exp_neg, Real.exp_sub]
    have h1 := Real.exp_pos τ
    have h2 := Real.exp_pos τ'
    field_simp
    ring
  · exact s02_normalGeod_zero Ω w hl

/-- (2.12) `eq:normal-flow`, `sec02-prelim.tex:248`: `log Φ_{E(w,τ)}(w) = τ`. -/
theorem eq_normal_flow {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) (τ : ℝ) :
    Real.log (horoPhi Ω (normalGeod Ω w τ) w) = τ := by
  rw [s02_horoPhi_normalGeod Ω w (s02_poincareDensity_pos hΩ hw) τ, Real.log_exp]

/-- Lemma 2.4 `lem:normal`, `sec02-prelim.tex:251`: `E(w, τ)` lies in the interior of `B_w` for
`τ < 0` and outside `B_w` for `τ > 0`. -/
theorem lem_normal_c {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) :
    (∀ τ : ℝ, τ < 0 → horoPhi Ω (normalGeod Ω w τ) w < 1) ∧
      ∀ τ : ℝ, 0 < τ → normalGeod Ω w τ ∉ horoball Ω w := by
  have hl := s02_poincareDensity_pos hΩ hw
  refine ⟨fun τ hτ => ?_, fun τ hτ hB => ?_⟩
  · rw [s02_horoPhi_normalGeod Ω w hl τ]
    exact Real.exp_lt_one_iff.mpr hτ
  · have h1 := hB.2
    rw [s02_horoPhi_normalGeod Ω w hl τ] at h1
    have := Real.one_lt_exp_iff.mpr hτ
    linarith

/-- The real derivative of `K(u, ξ) = (|u|² + ξ²)/(2ξ)`, so that `Φ_q(w) = λ(w) K(q - (w, 0))`. -/
theorem s02_hasFDerivAt_horoK {p : ℂ × ℝ} (hp : p.2 ≠ 0) :
    ∃ K' : ℂ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun q : ℂ × ℝ => (‖q.1‖ ^ 2 + q.2 ^ 2) / (2 * q.2)) K' p ∧
        ∀ a : ℂ × ℝ, K' a = ((p.1 * conj a.1).re + p.2 * a.2) / p.2 -
          (‖p.1‖ ^ 2 + p.2 ^ 2) * a.2 / (2 * p.2 ^ 2) := by
  have h1 : HasFDerivAt (fun q : ℂ × ℝ => ‖q.1‖ ^ 2)
      (2 • (innerSL ℝ p.1).comp (ContinuousLinearMap.fst ℝ ℂ ℝ)) p :=
    (hasFDerivAt_fst (p := p)).norm_sq
  have h2 := (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).pow 2
  have h3 : HasFDerivAt (fun q : ℂ × ℝ => 2 * q.2) ((2 : ℝ) • ContinuousLinearMap.snd ℝ ℂ ℝ) p :=
    (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).const_smul (2 : ℝ)
  have h2p : 2 * p.2 ≠ 0 := mul_ne_zero two_ne_zero hp
  have h4 := (hasFDerivAt_inv h2p).comp p h3
  have h5 := (h1.add h2).mul h4
  have hfun : (fun q : ℂ × ℝ => (‖q.1‖ ^ 2 + q.2 ^ 2) / (2 * q.2)) =
      fun q => (‖q.1‖ ^ 2 + q.2 ^ 2) * ((fun x : ℝ => x⁻¹) ∘ fun q : ℂ × ℝ => 2 * q.2) q := by
    funext q
    simp [div_eq_mul_inv]
  rw [hfun]
  refine ⟨_, h5, fun a => ?_⟩
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    innerSL_apply_apply, Complex.inner, ContinuousLinearMap.toSpanSingleton_apply,
    Function.comp_apply, smul_eq_mul, nsmul_eq_mul, Pi.add_apply]
  field_simp
  push_cast
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The velocity of the normal geodesic at `τ = 0`: with `l = λ(w)`, `A = ∂_w log λ` and
`D = |A|² + (l/2)²`, `∂_τ E(w, 0) = (Ā (l²/2)/D², (l/2)(l²/4 - |A|²)/D²)`. -/
theorem s02_hasDerivAt_normalGeod (Ω : Set ℂ) (w : ℂ) (hl : 0 < poincareDensity Ω w) :
    HasDerivAt (fun τ : ℝ => normalGeod Ω w τ)
      (conj (logDensityDz Ω w) *
          (((poincareDensity Ω w ^ 2 / 2) /
            (‖logDensityDz Ω w‖ ^ 2 + (poincareDensity Ω w / 2) ^ 2) ^ 2 : ℝ) : ℂ),
        poincareDensity Ω w / 2 * ((poincareDensity Ω w / 2) ^ 2 - ‖logDensityDz Ω w‖ ^ 2) /
          (‖logDensityDz Ω w‖ ^ 2 + (poincareDensity Ω w / 2) ^ 2) ^ 2) 0 := by
  unfold normalGeod
  generalize poincareDensity Ω w = l at hl ⊢
  generalize logDensityDz Ω w = A
  have hh : HasDerivAt (fun τ : ℝ => l * Real.exp (-τ) / 2) (-(l / 2)) 0 := by
    have := (((hasDerivAt_neg (0 : ℝ)).exp).const_mul l).div_const 2
    convert this using 1
    rw [neg_zero, Real.exp_zero]
    ring
  have hD : HasDerivAt (fun τ : ℝ => ‖A‖ ^ 2 + (l * Real.exp (-τ) / 2) ^ 2)
      (2 * (l / 2) * (-(l / 2))) 0 := by
    have := (hh.pow 2).const_add (‖A‖ ^ 2)
    convert this using 1
    simp
  have hD0 : ‖A‖ ^ 2 + (l * Real.exp (-0) / 2) ^ 2 ≠ 0 := by positivity
  have hD0' : ‖A‖ ^ 2 + (l / 2) ^ 2 ≠ 0 := by positivity
  have hc1 := ((hD.inv hD0).ofReal_comp.const_mul (conj A)).const_add w
  have hc2 := hh.div hD hD0
  have hc := hc1.prodMk hc2
  have hfun : (fun τ : ℝ => (w + conj A / ((‖A‖ ^ 2 + (l * Real.exp (-τ) / 2) ^ 2 : ℝ) : ℂ),
      (l * Real.exp (-τ) / 2) / (‖A‖ ^ 2 + (l * Real.exp (-τ) / 2) ^ 2))) =
      fun τ : ℝ => (w + conj A * (((‖A‖ ^ 2 + (l * Real.exp (-τ) / 2) ^ 2)⁻¹ : ℝ) : ℂ),
        (l * Real.exp (-τ) / 2) / (‖A‖ ^ 2 + (l * Real.exp (-τ) / 2) ^ 2)) := by
    funext τ
    rw [Complex.ofReal_inv, div_eq_mul_inv]
  rw [hfun]
  convert hc using 1
  simp only [neg_zero, Real.exp_zero, mul_one]
  refine Prod.ext ?_ ?_
  · dsimp only
    congr 1
    norm_cast
    field_simp
  · dsimp only
    field_simp
    ring

/-- Lemma 2.4 `lem:normal`, `sec02-prelim.tex:252`: where `X` is an immersion, `γ_w` is the
normal geodesic of `Σ` at `X(w)`: its velocity at `τ = 0` is orthogonal to `dX_w(ℂ)`. -/
theorem lem_normal_d {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) (himm : Function.Injective (fderiv ℝ (epstein Ω) w)) (v : ℂ) :
    hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w v)
      (deriv (fun τ : ℝ => normalGeod Ω w τ) 0) = 0 := by
  have hl := s02_poincareDensity_pos hΩ hw
  obtain ⟨f, hf⟩ := id hΩ
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  -- `himm` gives differentiability of `X` at `w`: otherwise `fderiv = 0`, which is not injective.
  have hXd : DifferentiableAt ℝ (epstein Ω) w := by
    by_contra h
    rw [fderiv_zero_of_not_differentiableAt h] at himm
    exact one_ne_zero (himm (by simp : (0 : ℂ →L[ℝ] ℂ × ℝ) 1 = (0 : ℂ →L[ℝ] ℂ × ℝ) 0))
  have hX := hXd.hasFDerivAt
  have hleq : poincareDensity Ω =ᶠ[𝓝 w] fun x => Real.exp (Real.log (poincareDensity Ω x)) := by
    filter_upwards [hΩo.mem_nhds hw] with x hx
    rw [Real.exp_log (s02_poincareDensity_pos hΩ hx)]
  obtain ⟨Ll, hLl⟩ : ∃ Ll, HasFDerivAt (poincareDensity Ω) Ll w :=
    ⟨_, (s02_differentiableAt_logDensity hΩ hw).hasFDerivAt.exp.congr_of_eventuallyEq hleq⟩
  have hp2 : 0 < (epstein Ω w).2 := by
    rw [← s02_normalGeod_zero Ω w hl]
    exact s02_normalGeod_pos Ω w hl 0
  set ι := ContinuousLinearMap.inl ℝ ℂ ℝ with hι
  have hpw : ((epstein Ω w).1 - w, (epstein Ω w).2) = epstein Ω w - ι w := by
    ext <;> simp [ι]
  obtain ⟨K', hK, hK'⟩ :=
    s02_hasFDerivAt_horoK (p := ((epstein Ω w).1 - w, (epstein Ω w).2)) hp2.ne'
  rw [hpw] at hK
  have hG := hLl.mul (hK.comp w (hX.sub ι.hasFDerivAt))
  have hH := hLl.mul (hK.comp w (ι.hasFDerivAt.const_sub (epstein Ω w)))
  have hΦ : ∀ q : ℂ × ℝ, ∀ w', horoPhi Ω q w' =
      poincareDensity Ω w' * (fun q : ℂ × ℝ => (‖q.1‖ ^ 2 + q.2 ^ 2) / (2 * q.2)) (q - ι w') := by
    intro q w'
    simp [horoPhi, ι, mul_div_assoc]
  -- `w' ↦ Φ_{X(w')}(w') ≡ 1` near `w`, since `X(w') = E(w', 0)` and `Φ_{E(w', τ)}(w') = e^τ`
  have hG0 : HasFDerivAt (fun w' => poincareDensity Ω w' *
      (fun q : ℂ × ℝ => (‖q.1‖ ^ 2 + q.2 ^ 2) / (2 * q.2)) (epstein Ω w' - ι w'))
      (0 : ℂ →L[ℝ] ℝ) w := by
    refine (hasFDerivAt_const (1 : ℝ) w).congr_of_eventuallyEq ?_
    filter_upwards [hΩo.mem_nhds hw] with x hx
    have hlx := s02_poincareDensity_pos hΩ hx
    rw [← hΦ, ← s02_normalGeod_zero Ω x hlx, s02_horoPhi_normalGeod Ω x hlx, Real.exp_zero]
  -- `w` is a critical point of `Φ_{X(w)}` (Lemma 2.4(a))
  have hH0 : HasFDerivAt (fun w' => poincareDensity Ω w' *
      (fun q : ℂ × ℝ => (‖q.1‖ ^ 2 + q.2 ^ 2) / (2 * q.2)) (epstein Ω w - ι w'))
      (0 : ℂ →L[ℝ] ℝ) w := by
    have hmem : epstein Ω w ∈
        {q | q ∈ UHS ∧ HasFDerivAt (fun w' => horoPhi Ω q w') (0 : ℂ →L[ℝ] ℝ) w} := by
      rw [lem_normal_a hΩ hw]
      exact ⟨0, s02_normalGeod_zero Ω w hl⟩
    have h := hmem.2
    simp only [hΦ] at h
    exact h
  have e1 := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) (hG.unique hG0)
  have e2 := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) (hH.unique hH0)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    map_sub, map_neg, smul_eq_mul, ContinuousLinearMap.zero_apply, Function.comp_apply,
    Pi.sub_apply] at e1 e2
  have hKd : K' (fderiv ℝ (epstein Ω) w v) = 0 := by
    have h : poincareDensity Ω w * K' (fderiv ℝ (epstein Ω) w v) = 0 := by
      linear_combination e1 - e2
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hl.ne'
    · exact h
  rw [hK'] at hKd
  rw [(s02_hasDerivAt_normalGeod Ω w hl).deriv]
  generalize fderiv ℝ (epstein Ω) w v = a at hKd ⊢
  unfold hypInner
  rw [div_eq_zero_iff]
  left
  unfold epstein at hKd
  dsimp only at hKd ⊢
  rw [add_sub_cancel_left] at hKd
  generalize poincareDensity Ω w = l at hl hKd ⊢
  generalize logDensityDz Ω w = A at hKd ⊢
  have hD : 0 < l ^ 2 + 4 * (A.re * A.re + A.im * A.im) := by
    nlinarith [mul_self_nonneg A.re, mul_self_nonneg A.im]
  have hq : 0 < A.re * A.re + A.im * A.im + (l / 2) ^ 2 := by
    nlinarith [mul_self_nonneg A.re, mul_self_nonneg A.im]
  -- `K'(a) = H/(8l²)` and `⟨a, ∂_τ E(w, 0)⟩ ξ² = (l/32) H / D₀²`
  have hH : (16 * l * (A.re * a.1.re - A.im * a.1.im) + 4 * l ^ 2 * a.2 -
      16 * (A.re * A.re + A.im * A.im) * a.2) / (8 * l ^ 2) = 0 := by
    convert hKd using 1
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.div_re, Complex.div_im]
    field_simp
    ring
  have hH0 : 16 * l * (A.re * a.1.re - A.im * a.1.im) + 4 * l ^ 2 * a.2 -
      16 * (A.re * A.re + A.im * A.im) * a.2 = 0 := by
    rcases div_eq_zero_iff.mp hH with h | h
    · exact h
    · exact absurd h (by positivity)
  convert (show l / 32 * (16 * l * (A.re * a.1.re - A.im * a.1.im) + 4 * l ^ 2 * a.2 -
      16 * (A.re * A.re + A.im * A.im) * a.2) / (A.re * A.re + A.im * A.im + (l / 2) ^ 2) ^ 2 = 0
      by rw [hH0]; ring) using 1
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, map_mul,
    Complex.conj_conj, Complex.conj_ofReal]
  field_simp
  ring

/-! ## §2.5 First fundamental form and curvature -/

/-- `ψ = f⁻¹`, `ψ'`, `ψ''` and `S(ψ)` are holomorphic, hence `C^∞`, on `Ω`. -/
theorem s02_contDiffOn_invFun {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.invFunOn f unitDisc) Ω ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (Function.invFunOn f unitDisc)) Ω ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (deriv (Function.invFunOn f unitDisc))) Ω ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (schwarzian (Function.invFunOn f unitDisc)) Ω := by
  set ψ := Function.invFunOn f unitDisc with hψdef
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hψ : IsConformalOnto ψ Ω unitDisc := hf.symm isOpen_ball
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
  refine ⟨(h0.contDiffOn hΩo).restrict_scalars ℝ, (h1.contDiffOn hΩo).restrict_scalars ℝ,
    (h2.contDiffOn hΩo).restrict_scalars ℝ, ((hS.contDiffOn hΩo).restrict_scalars ℝ).congr ?_⟩
  intro x hx
  exact schwarzian_of_analyticAt (h0.analyticAt (hΩo.mem_nhds hx))

/-- `λ = 2|ψ'|/(1-|ψ|²)` is `C^∞` on `Ω`. -/
theorem s02_contDiffOn_poincareDensity {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (poincareDensity Ω) Ω := by
  set ψ := Function.invFunOn f unitDisc with hψdef
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hψ : IsConformalOnto ψ Ω unitDisc := hf.symm isOpen_ball
  have hψU : ∀ x ∈ Ω, ‖ψ x‖ < 1 := by
    intro x hx
    have hmem := mem_image_of_mem ψ hx
    rw [hψ.2.2] at hmem
    exact mem_ball_zero_iff.mp hmem
  have hψ'ne : ∀ x ∈ Ω, deriv ψ x ≠ 0 := fun x hx =>
    deriv_ne_zero_of_injOn hΩo hψ.1 hψ.2.1 hx
  obtain ⟨h0, h1, -, -⟩ := s02_contDiffOn_invFun hf
  have hr : ∀ x ∈ Ω, 1 - ‖ψ x‖ ^ 2 ≠ 0 := by
    intro x hx
    have := hψU x hx
    nlinarith [norm_nonneg (ψ x)]
  have h := ((contDiffOn_const (c := (2 : ℝ))).mul (h1.norm ℝ hψ'ne)).div
    ((contDiffOn_const (c := (1 : ℝ))).sub (h0.norm_sq ℝ)) hr
  refine h.congr fun x hx => ?_
  rw [s02_poincareDensity_eq_inv hf hx]
  rfl

/-- `A = ∂_w log λ = ψ''/(2ψ') + ψ̄ψ'/(1-|ψ|²)` is `C^∞` on `Ω`. -/
theorem s02_contDiffOn_logDensityDz {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logDensityDz Ω) Ω := by
  set ψ := Function.invFunOn f unitDisc with hψdef
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hψ : IsConformalOnto ψ Ω unitDisc := hf.symm isOpen_ball
  have hψU : ∀ x ∈ Ω, ‖ψ x‖ < 1 := by
    intro x hx
    have hmem := mem_image_of_mem ψ hx
    rw [hψ.2.2] at hmem
    exact mem_ball_zero_iff.mp hmem
  have hψ'ne : ∀ x ∈ Ω, deriv ψ x ≠ 0 := fun x hx =>
    deriv_ne_zero_of_injOn hΩo hψ.1 hψ.2.1 hx
  obtain ⟨h0, h1, h2, -⟩ := s02_contDiffOn_invFun hf
  have hr : ∀ x ∈ Ω, ((1 - ‖ψ x‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    intro x hx
    have := hψU x hx
    have h3 : (1 : ℝ) - ‖ψ x‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg (ψ x)]
    exact_mod_cast h3
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => conj (ψ x)) Ω :=
    Complex.conjCLE.contDiff.comp_contDiffOn h0
  have hd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => ((1 - ‖ψ x‖ ^ 2 : ℝ) : ℂ)) Ω :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((contDiffOn_const (c := (1 : ℝ))).sub (h0.norm_sq ℝ))
  have h2' : ∀ x ∈ Ω, (2 : ℂ) * deriv ψ x ≠ 0 := fun x hx =>
    mul_ne_zero two_ne_zero (hψ'ne x hx)
  have h := (h2.mul (((contDiffOn_const (c := (2 : ℂ))).mul h1).inv h2')).add
    ((hc.mul h1).mul (hd.inv hr))
  refine h.congr fun x hx => ?_
  rw [s02_logDensityDz_eq hf hx, ← hψdef]
  simp only [Pi.inv_apply, div_eq_mul_inv]

/-- Lemma 2.5 `lem:fff`, `sec02-prelim.tex:276` (implicit): `X` is smooth on `Ω`. -/
theorem lem_fff_smooth {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (epstein Ω) Ω := by
  obtain ⟨f, hf⟩ := hΩ
  have hl := s02_contDiffOn_poincareDensity hf
  have hA := s02_contDiffOn_logDensityDz hf
  have hD : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => poincareDensity Ω w ^ 2 + 4 * ‖logDensityDz Ω w‖ ^ 2) Ω :=
    (hl.pow 2).add ((contDiffOn_const (c := (4 : ℝ))).mul (hA.norm_sq ℝ))
  have hDpos : ∀ w ∈ Ω, 0 < poincareDensity Ω w ^ 2 + 4 * ‖logDensityDz Ω w‖ ^ 2 :=
    fun w hw => by
      have := s02_poincareDensity_pos ⟨f, hf⟩ hw
      positivity
  have hDc : ∀ w ∈ Ω,
      ((poincareDensity Ω w ^ 2 + 4 * ‖logDensityDz Ω w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := fun w hw => by
    exact_mod_cast (hDpos w hw).ne'
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => conj (logDensityDz Ω w)) Ω :=
    Complex.conjCLE.contDiff.comp_contDiffOn hA
  have hDC : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => ((poincareDensity Ω w ^ 2 + 4 * ‖logDensityDz Ω w‖ ^ 2 : ℝ) : ℂ)) Ω :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hD
  have h1 := contDiffOn_id.add (((contDiffOn_const (c := (4 : ℂ))).mul hc).mul (hDC.inv hDc))
  have h2 := ((contDiffOn_const (c := (2 : ℝ))).mul hl).div hD fun w hw => (hDpos w hw).ne'
  refine (h1.prodMk h2).congr fun w hw => ?_
  simp only [epstein, Pi.inv_apply, div_eq_mul_inv, id]
  rfl

/-- First-fundamental-form helper: the real derivative of a real function is `v ↦ 2 Re(∂φ v)`. -/
theorem s02_fff_wirtinger {φ : ℂ → ℝ} {L : ℂ →L[ℝ] ℝ} {w : ℂ} (hφ : HasFDerivAt φ L w) (v : ℂ) :
    L v = 2 * (wirtingerDz φ w * v).re := by
  unfold wirtingerDz
  rw [hφ.fderiv]
  have hv : v = v.re • (1 : ℂ) + v.im • I := by apply Complex.ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- First-fundamental-form helper: the real-variable identity behind (2.13) (components of
`A, S, t` and of `dA`, `dX`). -/
theorem s02_fff_alg_re {l a1 a2 s1 s2 t1 t2 dl e1 e2 D dD dξ w1 w2 : ℝ} (hl : 0 < l)
    (hdl : dl = l * (2 * (a1 * t1 - a2 * t2)))
    (he1 : e1 = (a1 ^ 2 - a2 ^ 2 + s1 / 2) * t1 - (2 * a1 * a2 + s2 / 2) * t2 + l ^ 2 / 4 * t1)
    (he2 : e2 = (a1 ^ 2 - a2 ^ 2 + s1 / 2) * t2 + (2 * a1 * a2 + s2 / 2) * t1 - l ^ 2 / 4 * t2)
    (hD : D = l ^ 2 + 4 * (a1 ^ 2 + a2 ^ 2)) (hdD : dD = 2 * l * dl + 8 * (a1 * e1 + a2 * e2))
    (hdξ : dξ = 2 * dl / D - 2 * l * dD / D ^ 2)
    (hw1 : w1 = t1 + 4 * e1 / D - 4 * a1 * dD / D ^ 2)
    (hw2 : w2 = t2 - 4 * e2 / D + 4 * a2 * dD / D ^ 2) :
    (w1 ^ 2 + w2 ^ 2 + dξ ^ 2) / (2 * l / D) ^ 2 =
      (1 + (s1 ^ 2 + s2 ^ 2) / l ^ 4) * l ^ 2 * (t1 ^ 2 + t2 ^ 2) +
        2 * (s1 * (t1 ^ 2 - t2 ^ 2) - s2 * (2 * t1 * t2)) := by
  have hD0 : 0 < D := by rw [hD]; positivity
  subst hw1 hw2 hdξ
  subst hdD
  subst hdl he1 he2
  have hl0 : l ≠ 0 := hl.ne'
  have hD0' : D ≠ 0 := hD0.ne'
  field_simp
  subst hD
  ring

/-- First-fundamental-form helper: the algebraic identity behind (2.13).  With
`dλ = 2λ Re(A t)`, `dA = (A² + S/2) t + (λ²/4) t̄`, `D = λ² + 4|A|²`, the derivative
`(dW, dξ)` of `X = (w + 4Ā/D, 2λ/D)` has `⟨dX, dX⟩_X = (1 + (|S|/λ²)²) λ² |t|² + 2 Re(S t²)`. -/
theorem s02_fff_alg {l dl D dD dξ : ℝ} {A S t dA dW W : ℂ} (hl : 0 < l)
    (hdl : dl = l * (2 * (A * t).re))
    (hdA : dA = (A ^ 2 + S / 2) * t + ((l ^ 2 / 4 : ℝ) : ℂ) * conj t)
    (hD : D = l ^ 2 + 4 * ‖A‖ ^ 2) (hdD : dD = 2 * l * dl + 8 * (conj A * dA).re)
    (hdξ : dξ = 2 * dl / D - 2 * l * dD / D ^ 2)
    (hdW : dW = t + 4 * conj dA * ((D⁻¹ : ℝ) : ℂ) - 4 * conj A * ((dD / D ^ 2 : ℝ) : ℂ)) :
    hypInner (W, 2 * l / D) (dW, dξ) (dW, dξ) =
      (1 + (‖S‖ / l ^ 2) ^ 2) * l ^ 2 * ‖t‖ ^ 2 + 2 * (S * t ^ 2).re := by
  have key := s02_fff_alg_re (a1 := A.re) (a2 := A.im) (s1 := S.re) (s2 := S.im) (t1 := t.re)
    (t2 := t.im) (e1 := dA.re) (e2 := dA.im) (w1 := dW.re) (w2 := dW.im) hl
    (by rw [hdl, Complex.mul_re])
    (by rw [hdA]; simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.conj_re, Complex.conj_im]; ring)
    (by rw [hdA]; simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.conj_re, Complex.conj_im]; ring)
    (by rw [hD, Complex.sq_norm, Complex.normSq_apply]; ring)
    (by rw [hdD]; simp [Complex.mul_re])
    hdξ
    (by rw [hdW]; simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.mul_im,
          Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
          Complex.im_ofNat]; ring)
    (by rw [hdW]; simp only [Complex.sub_im, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
          Complex.im_ofNat]; ring)
  unfold hypInner
  convert key using 1
  · simp [Complex.mul_re]; ring
  · rw [div_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp [pow_two, Complex.mul_re, Complex.mul_im]
    ring

/-- First-fundamental-form helper: the derivative of `x ↦ (x + 4Ā/D, 2λ/D)`, `D = λ² + 4|A|²`,
for real-differentiable `λ > 0` and `A`. -/
theorem s02_fff_hasFDerivAt_ep {lam : ℂ → ℝ} {A : ℂ → ℂ} {Ll : ℂ →L[ℝ] ℝ} {LA : ℂ →L[ℝ] ℂ}
    {w : ℂ} (hl : HasFDerivAt lam Ll w) (hA : HasFDerivAt A LA w) (hpos : 0 < lam w) :
    ∃ L : ℂ →L[ℝ] ℂ × ℝ, HasFDerivAt (fun x => (x + 4 * conj (A x) /
        ((lam x ^ 2 + 4 * ‖A x‖ ^ 2 : ℝ) : ℂ), 2 * lam x / (lam x ^ 2 + 4 * ‖A x‖ ^ 2))) L w ∧
      ∀ v, L v = (v + 4 * conj (LA v) * (((lam w ^ 2 + 4 * ‖A w‖ ^ 2)⁻¹ : ℝ) : ℂ) -
          4 * conj (A w) * (((2 * lam w * Ll v + 8 * (conj (A w) * LA v).re) /
            (lam w ^ 2 + 4 * ‖A w‖ ^ 2) ^ 2 : ℝ) : ℂ),
        2 * Ll v / (lam w ^ 2 + 4 * ‖A w‖ ^ 2) -
          2 * lam w * (2 * lam w * Ll v + 8 * (conj (A w) * LA v).re) /
            (lam w ^ 2 + 4 * ‖A w‖ ^ 2) ^ 2) := by
  have hD := (hl.pow 2).add ((hA.norm_sq).const_mul 4)
  have hD0 : lam w ^ 2 + 4 * ‖A w‖ ^ 2 ≠ 0 := by positivity
  have hDi := (hasDerivAt_inv hD0).comp_hasFDerivAt w hD
  have hDic := (Complex.ofRealCLM.hasFDerivAt).comp w hDi
  have hcA := ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt).comp w hA
  have hW := (hasFDerivAt_id w).add ((hcA.const_mul (4 : ℂ)).mul hDic)
  have hξ := (hl.const_mul (2 : ℝ)).mul hDi
  refine ⟨_, (hW.prodMk hξ).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_),
    fun v => ?_⟩
  · refine Prod.ext ?_ ?_
    · simp [div_eq_mul_inv, mul_assoc]
    · simp [div_eq_mul_inv, mul_assoc]
  · refine Prod.ext ?_ ?_
    · simp [Complex.inner, div_eq_mul_inv]
      ring
    · simp [Complex.inner, div_eq_mul_inv]
      ring

/-- First-fundamental-form helper: `log λ` is real-differentiable on `Ω`. -/
theorem s02_fff_hasFDerivAt_log {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {w : ℂ} (hw : w ∈ Ω) :
    ∃ L : ℂ →L[ℝ] ℝ, HasFDerivAt (fun x => Real.log (poincareDensity Ω x)) L w := by
  set ψ := Function.invFunOn f unitDisc with hψdef
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hψ : IsConformalOnto ψ Ω unitDisc := hf.symm isOpen_ball
  have hψU : ∀ x ∈ Ω, ‖ψ x‖ < 1 := by
    intro x hx
    have hmem := mem_image_of_mem ψ hx
    rw [hψ.2.2] at hmem
    exact mem_ball_zero_iff.mp hmem
  have hψ'ne : ∀ x ∈ Ω, deriv ψ x ≠ 0 := fun x hx =>
    deriv_ne_zero_of_injOn hΩo hψ.1 hψ.2.1 hx
  have hψA : AnalyticAt ℂ ψ w := hψ.1.analyticAt (hΩo.mem_nhds hw)
  have hψd : DifferentiableAt ℂ ψ w := hψA.differentiableAt
  have hψ'd : DifferentiableAt ℂ (deriv ψ) w := hψA.deriv.differentiableAt
  obtain ⟨L1, h1, -⟩ := s02_hasFDerivAt_log_normSq hψ'd.hasDerivAt (hψ'ne w hw)
  obtain ⟨L2, h2, -⟩ := s02_hasFDerivAt_log_one_sub_normSq hψd.hasDerivAt (hψU w hw)
  have hF : HasFDerivAt (fun x => Real.log 2 + (1 / 2 : ℝ) • Real.log (‖deriv ψ x‖ ^ 2) -
      Real.log (1 - ‖ψ x‖ ^ 2)) ((1 / 2 : ℝ) • L1 - L2) w :=
    ((h1.const_smul (1 / 2 : ℝ)).const_add (Real.log 2)).sub h2
  have heq : (fun x => Real.log (poincareDensity Ω x)) =ᶠ[𝓝 w]
      fun x => Real.log 2 + (1 / 2 : ℝ) • Real.log (‖deriv ψ x‖ ^ 2) -
        Real.log (1 - ‖ψ x‖ ^ 2) := by
    filter_upwards [hΩo.mem_nhds hw] with x hx
    have hr : (0 : ℝ) < 1 - ‖ψ x‖ ^ 2 := by nlinarith [norm_nonneg (ψ x), hψU x hx]
    have hn : 0 < ‖deriv ψ x‖ := norm_pos_iff.mpr (hψ'ne x hx)
    rw [s02_poincareDensity_eq_inv hf hx, ← hψdef, Real.log_div (by positivity) hr.ne',
      Real.log_mul (by norm_num) hn.ne', Real.log_pow, smul_eq_mul]
    push_cast
    ring
  exact ⟨_, hF.congr_of_eventuallyEq heq⟩

/-- First-fundamental-form helper (ψ-derivative layer): `dλ(v) = 2 λ Re(A v)` on `Ω`. -/
theorem s02_fff_hasFDerivAt_lambda {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {w : ℂ} (hw : w ∈ Ω) :
    ∃ L : ℂ →L[ℝ] ℝ, HasFDerivAt (poincareDensity Ω) L w ∧
      ∀ v, L v = poincareDensity Ω w * (2 * (logDensityDz Ω w * v).re) := by
  obtain ⟨L, hL⟩ := s02_fff_hasFDerivAt_log hf hw
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hw
  have heq : poincareDensity Ω =ᶠ[𝓝 w] fun x => Real.exp (Real.log (poincareDensity Ω x)) := by
    filter_upwards [hΩo.mem_nhds hw] with x hx
    rw [Real.exp_log (s02_poincareDensity_pos ⟨f, hf⟩ hx)]
  refine ⟨_, hL.exp.congr_of_eventuallyEq heq, fun v => ?_⟩
  change Real.exp (Real.log (poincareDensity Ω w)) * L v = _
  rw [Real.exp_log hl, s02_fff_wirtinger hL v]
  rfl

/-- First-fundamental-form helper (ψ-derivative layer): `∂A = A² + S(ψ)/2` and `∂̄A = λ²/4` on `Ω`,
`ψ = f⁻¹`, i.e. `dA(v) = (A² + S(ψ)/2) v + (λ²/4) v̄`. -/
theorem s02_fff_hasFDerivAt_A {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {w : ℂ} (hw : w ∈ Ω) :
    ∃ LA : ℂ →L[ℝ] ℂ, HasFDerivAt (logDensityDz Ω) LA w ∧
      ∀ v, LA v = (logDensityDz Ω w ^ 2 + schwarzian (Function.invFunOn f unitDisc) w / 2) * v +
        ((poincareDensity Ω w ^ 2 / 4 : ℝ) : ℂ) * conj v := by
  set ψ := Function.invFunOn f unitDisc with hψdef
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hψ : IsConformalOnto ψ Ω unitDisc := hf.symm isOpen_ball
  have hψU : ‖ψ w‖ < 1 := by
    have hmem := mem_image_of_mem ψ hw
    rw [hψ.2.2] at hmem
    exact mem_ball_zero_iff.mp hmem
  have ha0 : deriv ψ w ≠ 0 := deriv_ne_zero_of_injOn hΩo hψ.1 hψ.2.1 hw
  have hψA : AnalyticAt ℂ ψ w := hψ.1.analyticAt (hΩo.mem_nhds hw)
  have ha : HasDerivAt ψ (deriv ψ w) w := hψA.differentiableAt.hasDerivAt
  have hb : HasDerivAt (deriv ψ) (deriv (deriv ψ) w) w := hψA.deriv.differentiableAt.hasDerivAt
  have hc : HasDerivAt (deriv (deriv ψ)) (deriv (deriv (deriv ψ)) w) w :=
    hψA.deriv.deriv.differentiableAt.hasDerivAt
  have hN : (0 : ℝ) < 1 - ‖ψ w‖ ^ 2 := by nlinarith [norm_nonneg (ψ w)]
  have hS : schwarzian ψ w = (deriv (deriv (deriv ψ)) w * deriv ψ w -
      deriv (deriv ψ) w * deriv (deriv ψ) w) / deriv ψ w ^ 2 -
      1 / 2 * (deriv (deriv ψ) w / deriv ψ w) ^ 2 := by
    rw [schwarzian_of_analyticAt hψA]
    show deriv (fun x => deriv (deriv ψ) x / deriv ψ x) w -
      (1 / 2) * (deriv (deriv ψ) w / deriv ψ w) ^ 2 = _
    rw [← (hc.div hb ha0).deriv]
    rfl
  have h1 := ((hc.div (hb.const_mul 2) (mul_ne_zero two_ne_zero ha0)).hasFDerivAt).restrictScalars ℝ
  have hcψ := ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt).comp w
    (ha.hasFDerivAt.restrictScalars ℝ)
  have hu0 : (1 : ℂ) - ψ w * conj (ψ w) ≠ 0 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact_mod_cast hN.ne'
  have hNc := ((ha.hasFDerivAt.restrictScalars ℝ).mul hcψ).const_sub (1 : ℂ)
  have hNi := (hasFDerivAt_inv' (𝕜 := ℝ) hu0).comp w hNc
  have h2 := (hcψ.mul (hb.hasFDerivAt.restrictScalars ℝ)).mul hNi
  have hnc : ∀ x : ℂ, (((1 - ‖x‖ ^ 2 : ℝ)) : ℂ) = 1 - x * conj x := fun x => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  refine ⟨_, (h1.add h2).congr_of_eventuallyEq ?_, fun v => ?_⟩
  · filter_upwards [hΩo.mem_nhds hw] with x hx
    rw [s02_logDensityDz_eq hf hx, ← hψdef, hnc]
    simp [div_eq_mul_inv, mul_assoc]
  · rw [s02_logDensityDz_eq hf hw, s02_poincareDensity_eq_inv hf hw, ← hψdef, hS, hnc]
    have hna : ((‖deriv ψ w‖ : ℝ) : ℂ) ^ 2 = deriv ψ w * conj (deriv ψ w) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    have hnu : ((‖ψ w‖ : ℝ) : ℂ) ^ 2 = ψ w * conj (ψ w) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    push_cast
    simp only [div_pow, mul_pow, hna, hnu]
    simp [ContinuousLinearMap.mulLeftRight_apply]
    have hu0' : (1 : ℂ) - conj (ψ w) * ψ w ≠ 0 := by rwa [mul_comm]
    have ha0' : conj (deriv ψ w) ≠ 0 := (map_ne_zero _).2 ha0
    field_simp
    ring

/-- First-fundamental-form helper: `X` is real-differentiable on `Ω`, with the derivative of
`s02_fff_hasFDerivAt_ep` (`λ` and `A` from the ψ-derivative layer). -/
theorem s02_fff_hasFDerivAt_epstein {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {w : ℂ} (hw : w ∈ Ω) :
    ∃ L : ℂ →L[ℝ] ℂ × ℝ, HasFDerivAt (epstein Ω) L w ∧ ∀ v,
      hypInner (epstein Ω w) (L v) (L v) =
        (1 + schwarzNorm Ω w ^ 2) * poincareDensity Ω w ^ 2 * ‖v‖ ^ 2 +
          2 * (schwarzian (Function.invFunOn f unitDisc) w * v ^ 2).re := by
  obtain ⟨Ll, hLl, hLlv⟩ := s02_fff_hasFDerivAt_lambda hf hw
  obtain ⟨LA, hLA, hLAv⟩ := s02_fff_hasFDerivAt_A hf hw
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hw
  obtain ⟨L, hL, hLv⟩ := s02_fff_hasFDerivAt_ep hLl hLA hl
  refine ⟨L, hL, fun v => ?_⟩
  rw [hLv v, eq_def_s hf hw]
  exact s02_fff_alg hl (hLlv v) (hLAv v) rfl rfl rfl rfl

/-- First-fundamental-form helper: `X` is real-differentiable on `Ω`. -/
theorem s02_epstein_differentiableAt {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    {w : ℂ} (hw : w ∈ Ω) : DifferentiableAt ℝ (epstein Ω) w := by
  obtain ⟨f, hf⟩ := hΩ
  obtain ⟨L, hL, -⟩ := s02_fff_hasFDerivAt_epstein hf hw
  exact hL.differentiableAt

/-- First-fundamental-form helper: `(1 - s)² |v|²_ρ ≤ I(v) ≤ (1 + s)² |v|²_ρ`. -/
theorem s02_fff_bounds {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) (v : ℂ) :
    (1 - schwarzNorm Ω w) ^ 2 * poincareDensity Ω w ^ 2 * ‖v‖ ^ 2 ≤
        hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w v) (fderiv ℝ (epstein Ω) w v) ∧
      hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w v) (fderiv ℝ (epstein Ω) w v) ≤
        (1 + schwarzNorm Ω w) ^ 2 * poincareDensity Ω w ^ 2 * ‖v‖ ^ 2 := by
  obtain ⟨f, hf⟩ := hΩ
  obtain ⟨L, hL, hLv⟩ := s02_fff_hasFDerivAt_epstein hf hw
  rw [hL.fderiv, hLv v]
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hw
  have hs := eq_def_s hf hw
  have hS : ‖schwarzian (Function.invFunOn f unitDisc) w‖ =
      schwarzNorm Ω w * poincareDensity Ω w ^ 2 := by
    rw [hs]; field_simp
  have hre : |(schwarzian (Function.invFunOn f unitDisc) w * v ^ 2).re| ≤
      schwarzNorm Ω w * poincareDensity Ω w ^ 2 * ‖v‖ ^ 2 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_pow, hS]
  have h1 := neg_abs_le (schwarzian (Function.invFunOn f unitDisc) w * v ^ 2).re
  have h2 := le_abs_self (schwarzian (Function.invFunOn f unitDisc) w * v ^ 2).re
  constructor <;> nlinarith

/-- Lemma 2.5 `lem:fff`, (2.13) `eq:fff`, first form, `sec02-prelim.tex:279`:
`I = X^* g_{ℍ³} = (1 + s²) ρ + 2 Re(S(f⁻¹) dw²)`. -/
theorem lem_fff {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) (v : ℂ) :
    hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w v) (fderiv ℝ (epstein Ω) w v) =
      (1 + schwarzNorm Ω w ^ 2) * poincareDensity Ω w ^ 2 * ‖v‖ ^ 2 +
        2 * (schwarzian (Function.invFunOn f unitDisc) w * v ^ 2).re := by
  obtain ⟨L, hL, hLv⟩ := s02_fff_hasFDerivAt_epstein hf hw
  rw [hL.fderiv]
  exact hLv v

/-- `S(f⁻¹)(f z) f'(z)² = -S f(z)` (chain rule for `f⁻¹ ∘ f = id`). -/
theorem s02_schwarzian_inv_comp {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {z : ℂ} (hz : z ∈ unitDisc) :
    schwarzian (Function.invFunOn f unitDisc) (f z) * deriv f z ^ 2 = -schwarzian f z := by
  have hw : f z ∈ Ω := by
    rw [← hf.2.2]
    exact mem_image_of_mem f hz
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hψ : IsConformalOnto (Function.invFunOn f unitDisc) Ω unitDisc := hf.symm isOpen_ball
  have hfA : AnalyticAt ℂ f z := hf.1.analyticAt (isOpen_ball.mem_nhds hz)
  have hf' : deriv f z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz
  have hψA : AnalyticAt ℂ (Function.invFunOn f unitDisc) (f z) :=
    hψ.1.analyticAt (hΩo.mem_nhds hw)
  have hψ' : deriv (Function.invFunOn f unitDisc) (f z) ≠ 0 :=
    deriv_ne_zero_of_injOn hΩo hψ.1 hψ.2.1 hw
  have hloc : Function.invFunOn f unitDisc ∘ f =ᶠ[𝓝 z] fun v => (1 * v + 0) / (0 * v + 1) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with v hv
    rw [Function.comp_apply, hf.2.1.leftInvOn_invFunOn hv]
    ring
  have hchain := eq19_1_chain_rule hfA hf' hψA hψ'
  rw [schwarzian_congr (hloc.filter_mono nhdsWithin_le_nhds),
    schwarzian_mobius (by norm_num)] at hchain
  linear_combination -hchain

/-- Polarization of `hypInner`: `⟨a+b, a+b⟩ = ⟨a,a⟩ + 2⟨a,b⟩ + ⟨b,b⟩`. -/
theorem s02_hypInner_add (q a b : ℂ × ℝ) :
    hypInner q (a + b) (a + b) = hypInner q a a + 2 * hypInner q a b + hypInner q b b := by
  unfold hypInner
  have h : (b.1 * conj a.1).re = (a.1 * conj b.1).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  simp only [Prod.fst_add, Prod.snd_add, map_add, add_mul, mul_add, Complex.add_re, h]
  ring

/-- `hypInner q a a = 0` forces `a = 0` when `q.2 ≠ 0`. -/
theorem s02_hypInner_self_eq_zero {q a : ℂ × ℝ} (hq : q.2 ≠ 0) (h : hypInner q a a = 0) :
    a = 0 := by
  unfold hypInner at h
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · have h' : a.1.re ^ 2 + a.1.im ^ 2 + a.2 ^ 2 = 0 := by
      rw [← h]
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    have h1 : a.1.re ^ 2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg a.1.im, sq_nonneg a.2]) (sq_nonneg _)
    have h2 : a.1.im ^ 2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg a.1.re, sq_nonneg a.2]) (sq_nonneg _)
    have h3 : a.2 ^ 2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg a.1.re, sq_nonneg a.1.im]) (sq_nonneg _)
    refine Prod.ext ?_ (pow_eq_zero_iff two_ne_zero |>.mp h3)
    apply Complex.ext
    · exact pow_eq_zero_iff two_ne_zero |>.mp h1
    · exact pow_eq_zero_iff two_ne_zero |>.mp h2
  · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hq

/-- Lemma 2.5 `lem:fff`, (2.13) `eq:fff`, second form, `sec02-prelim.tex:281`:
`f^* I = (1 + s²) ρ_𝔻 - 2 Re(S f dζ²)`. -/
theorem lem_fff_pullback {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {z : ℂ}
    (hz : z ∈ unitDisc) (v : ℂ) :
    hypInner (epstein Ω (f z)) (fderiv ℝ (fun ζ => epstein Ω (f ζ)) z v)
        (fderiv ℝ (fun ζ => epstein Ω (f ζ)) z v) =
      (1 + schwarzNorm Ω (f z) ^ 2) * (4 * ‖v‖ ^ 2 / (1 - ‖z‖ ^ 2) ^ 2) -
        2 * (schwarzian f z * v ^ 2).re := by
  have hfz : f z ∈ Ω := by
    rw [← hf.2.2]
    exact mem_image_of_mem f hz
  obtain ⟨L, hL, hLv⟩ := s02_fff_hasFDerivAt_epstein hf hfz
  have hfd : HasDerivAt f (deriv f z) z :=
    (hf.1.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hcomp := hL.comp z (hfd.hasFDerivAt.restrictScalars ℝ)
  have e : fderiv ℝ (fun ζ => epstein Ω (f ζ)) z v = L (v * deriv f z) := by
    rw [show (fun ζ => epstein Ω (f ζ)) = epstein Ω ∘ f from rfl, hcomp.fderiv]
    simp
  rw [e, hLv]
  have hl := eq_lambda_f hf hz
  have hr : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by
    have := mem_ball_zero_iff.mp hz
    nlinarith [norm_nonneg z]
  have h1 : poincareDensity Ω (f z) ^ 2 * ‖v * deriv f z‖ ^ 2 =
      4 * ‖v‖ ^ 2 / (1 - ‖z‖ ^ 2) ^ 2 := by
    calc poincareDensity Ω (f z) ^ 2 * ‖v * deriv f z‖ ^ 2 =
        (poincareDensity Ω (f z) * ‖deriv f z‖) ^ 2 * ‖v‖ ^ 2 := by
          rw [norm_mul]
          ring
      _ = 4 * ‖v‖ ^ 2 / (1 - ‖z‖ ^ 2) ^ 2 := by
          rw [hl, div_pow]
          ring
  have h2 : schwarzian (Function.invFunOn f unitDisc) (f z) * (v * deriv f z) ^ 2 =
      -(schwarzian f z * v ^ 2) := by
    calc schwarzian (Function.invFunOn f unitDisc) (f z) * (v * deriv f z) ^ 2 =
        (schwarzian (Function.invFunOn f unitDisc) (f z) * deriv f z ^ 2) * v ^ 2 := by ring
      _ = -(schwarzian f z * v ^ 2) := by
          rw [s02_schwarzian_inv_comp hf hz]
          ring
  rw [h2, Complex.neg_re, mul_assoc (1 + schwarzNorm Ω (f z) ^ 2), h1]
  ring

/-- Lemma 2.5 `lem:fff`, `sec02-prelim.tex:283`: the eigenvalues of `I` with respect to `ρ` are
`(1 ± s)²` (both attained). -/
theorem lem_fff_eigen {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) :
    (∀ v : ℂ,
      (1 - schwarzNorm Ω w) ^ 2 * poincareDensity Ω w ^ 2 * ‖v‖ ^ 2 ≤
        hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w v) (fderiv ℝ (epstein Ω) w v) ∧
      hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w v) (fderiv ℝ (epstein Ω) w v) ≤
        (1 + schwarzNorm Ω w) ^ 2 * poincareDensity Ω w ^ 2 * ‖v‖ ^ 2) ∧
    (∃ v : ℂ, v ≠ 0 ∧
      hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w v) (fderiv ℝ (epstein Ω) w v) =
        (1 + schwarzNorm Ω w) ^ 2 * poincareDensity Ω w ^ 2 * ‖v‖ ^ 2) ∧
    ∃ v : ℂ, v ≠ 0 ∧
      hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w v) (fderiv ℝ (epstein Ω) w v) =
        (1 - schwarzNorm Ω w) ^ 2 * poincareDensity Ω w ^ 2 * ‖v‖ ^ 2 := by
  obtain ⟨f, hf⟩ := id hΩ
  obtain ⟨S, hSdef⟩ : ∃ S, S = schwarzian (Function.invFunOn f unitDisc) w := ⟨_, rfl⟩
  have hl := s02_poincareDensity_pos hΩ hw
  have hS : ‖S‖ = schwarzNorm Ω w * poincareDensity Ω w ^ 2 := by
    rw [eq_def_s hf hw, ← hSdef]
    field_simp
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ((-(Complex.arg S / 2) : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = Complex.exp (c * I) := ⟨_, rfl⟩
  have hu1 : ‖u‖ = 1 := by
    rw [hu, hc]
    exact Complex.norm_exp_ofReal_mul_I _
  have hu0 : u ≠ 0 := by
    rw [hu]
    exact Complex.exp_ne_zero _
  have hz : (Complex.arg S : ℂ) * I + (c * I + c * I) = 0 := by
    rw [hc]
    push_cast
    ring
  have hSu : S * u ^ 2 = ((‖S‖ : ℝ) : ℂ) := by
    calc S * u ^ 2 = (‖S‖ * Complex.exp (Complex.arg S * I)) * (u * u) := by
          rw [Complex.norm_mul_exp_arg_mul_I, sq]
      _ = ‖S‖ * Complex.exp (Complex.arg S * I + (c * I + c * I)) := by
          rw [hu, Complex.exp_add, Complex.exp_add]
          ring
      _ = ‖S‖ := by rw [hz, Complex.exp_zero, mul_one]
  refine ⟨fun v => s02_fff_bounds hΩ hw v, ⟨u, hu0, ?_⟩, ⟨I * u, mul_ne_zero I_ne_zero hu0, ?_⟩⟩
  · have hQ := lem_fff hf hw u
    rw [← hSdef, hSu, hu1, Complex.ofReal_re, hS] at hQ
    rw [hQ, hu1]
    ring
  · have hQ := lem_fff hf hw (I * u)
    have h1 : S * (I * u) ^ 2 = -((‖S‖ : ℝ) : ℂ) := by
      rw [mul_pow, I_sq, neg_one_mul, mul_neg, hSu]
    rw [← hSdef, h1, Complex.neg_re, Complex.ofReal_re, hS, norm_mul, Complex.norm_I, one_mul,
      hu1] at hQ
    rw [hQ, norm_mul, Complex.norm_I, one_mul, hu1]
    ring

/-- (2.14) `eq:dX-norm`, `sec02-prelim.tex:286`: for `s ≤ 1`,
`(1-s)|v|_ρ ≤ |dX(v)| ≤ (1+s)|v|_ρ ≤ (5/2)|v|_ρ`. -/
theorem eq_dX_norm {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) (hs : schwarzNorm Ω w ≤ 1) (v : ℂ) :
    (1 - schwarzNorm Ω w) * (poincareDensity Ω w * ‖v‖) ≤
        √(hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w v) (fderiv ℝ (epstein Ω) w v)) ∧
      √(hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w v) (fderiv ℝ (epstein Ω) w v)) ≤
        (1 + schwarzNorm Ω w) * (poincareDensity Ω w * ‖v‖) ∧
      (1 + schwarzNorm Ω w) * (poincareDensity Ω w * ‖v‖) ≤
        5 / 2 * (poincareDensity Ω w * ‖v‖) := by
  obtain ⟨hlo, hup⟩ := s02_fff_bounds hΩ hw v
  obtain ⟨hs0, hs32⟩ := eq_nehari hΩ hw
  have hl := s02_poincareDensity_pos hΩ hw
  have hlv : 0 ≤ poincareDensity Ω w * ‖v‖ := by positivity
  refine ⟨?_, ?_, mul_le_mul_of_nonneg_right (by linarith) hlv⟩
  · refine Real.le_sqrt_of_sq_le ?_
    nlinarith
  · rw [← Real.sqrt_sq (by positivity : 0 ≤ (1 + schwarzNorm Ω w) * (poincareDensity Ω w * ‖v‖))]
    exact Real.sqrt_le_sqrt (by nlinarith)

/-- Lemma 2.5 `lem:fff`, `sec02-prelim.tex:290`: `|dX(v)| ≤ (5/2)|v|_ρ` always. -/
theorem eq_dX_norm_always {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) (v : ℂ) :
    √(hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w v) (fderiv ℝ (epstein Ω) w v)) ≤
      5 / 2 * (poincareDensity Ω w * ‖v‖) := by
  obtain ⟨-, hup⟩ := s02_fff_bounds hΩ hw v
  obtain ⟨hs0, hs32⟩ := eq_nehari hΩ hw
  have hl := s02_poincareDensity_pos hΩ hw
  have hlv : 0 ≤ poincareDensity Ω w * ‖v‖ := by positivity
  calc √(hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w v) (fderiv ℝ (epstein Ω) w v))
      ≤ (1 + schwarzNorm Ω w) * (poincareDensity Ω w * ‖v‖) := by
        rw [← Real.sqrt_sq (by positivity :
          0 ≤ (1 + schwarzNorm Ω w) * (poincareDensity Ω w * ‖v‖))]
        exact Real.sqrt_le_sqrt (by nlinarith)
    _ ≤ 5 / 2 * (poincareDensity Ω w * ‖v‖) :=
        mul_le_mul_of_nonneg_right (by linarith) hlv

/-- Lemma 2.5 `lem:fff`, `sec02-prelim.tex:291`: `X` is an immersion exactly on `{s ≠ 1}`. -/
theorem lem_fff_immersion {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) :
    Function.Injective (fderiv ℝ (epstein Ω) w) ↔ schwarzNorm Ω w ≠ 1 := by
  have hl := s02_poincareDensity_pos hΩ hw
  have hq2 : (epstein Ω w).2 ≠ 0 := by
    show 2 * poincareDensity Ω w / (poincareDensity Ω w ^ 2 + 4 * ‖logDensityDz Ω w‖ ^ 2) ≠ 0
    positivity
  obtain ⟨-, -, v₀, hv₀, hQ0⟩ := lem_fff_eigen hΩ hw
  constructor
  · intro hinj hs1
    rw [hs1, sub_self] at hQ0
    have h0 : hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w v₀)
        (fderiv ℝ (epstein Ω) w v₀) = 0 := by
      rw [hQ0]
      ring
    have h1 := s02_hypInner_self_eq_zero hq2 h0
    exact hv₀ (hinj (h1.trans (map_zero _).symm))
  · intro hs
    refine (injective_iff_map_eq_zero (fderiv ℝ (epstein Ω) w)).mpr fun v hv => ?_
    by_contra hv0
    have hb := (s02_fff_bounds hΩ hw v).1
    rw [hv] at hb
    have h00 : hypInner (epstein Ω w) 0 0 = 0 := by
      unfold hypInner
      simp
    rw [h00] at hb
    have h1 : 1 - schwarzNorm Ω w ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
    have h2 := norm_pos_iff.mpr hv0
    have h3 : 0 < (1 - schwarzNorm Ω w) ^ 2 * poincareDensity Ω w ^ 2 * ‖v‖ ^ 2 := by
      positivity
    linarith

/-- Lemma 2.5 `lem:fff`, `sec02-prelim.tex:291`: the area element of `X` is `|1-s²| dâ`: the Gram
determinant of `I` in the frame `(1, i)` is `((1-s²) λ²)²`. -/
theorem lem_fff_area {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) :
    hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w 1) (fderiv ℝ (epstein Ω) w 1) *
        hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w Complex.I)
          (fderiv ℝ (epstein Ω) w Complex.I) -
      hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w 1)
          (fderiv ℝ (epstein Ω) w Complex.I) ^ 2 =
      ((1 - schwarzNorm Ω w ^ 2) * poincareDensity Ω w ^ 2) ^ 2 := by
  obtain ⟨f, hf⟩ := id hΩ
  obtain ⟨S, hSdef⟩ : ∃ S, S = schwarzian (Function.invFunOn f unitDisc) w := ⟨_, rfl⟩
  have hl := s02_poincareDensity_pos hΩ hw
  have hS : ‖S‖ = schwarzNorm Ω w * poincareDensity Ω w ^ 2 := by
    rw [eq_def_s hf hw, ← hSdef]
    field_simp
  have hn : S.re ^ 2 + S.im ^ 2 = (schwarzNorm Ω w * poincareDensity Ω w ^ 2) ^ 2 := by
    rw [← hS, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hQ1 := lem_fff hf hw 1
  have hQI := lem_fff hf hw I
  have hQ2 := lem_fff hf hw (1 + I)
  rw [← hSdef] at hQ1 hQI hQ2
  rw [map_add, s02_hypInner_add] at hQ2
  have e1 : (S * 1 ^ 2).re = S.re := by simp
  have e2 : (S * I ^ 2).re = -S.re := by simp [sq]
  have e0 : (1 + I) ^ 2 = 2 * I := by
    rw [sq, add_mul, mul_add, mul_add, I_mul_I]
    ring
  have e3 : (S * (2 * I)).re = -2 * S.im := by
    rw [Complex.mul_re]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
      Complex.im_ofNat]
    ring
  have e4 : ‖(1 : ℂ) + I‖ ^ 2 = 2 := by
    norm_num [Complex.sq_norm, Complex.normSq_apply]
  rw [norm_one, e1] at hQ1
  rw [Complex.norm_I, e2] at hQI
  rw [e0, e3, e4] at hQ2
  have hB : hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w 1) (fderiv ℝ (epstein Ω) w I) =
      -2 * S.im := by
    linear_combination (hQ2 - hQ1 - hQI) / 2
  rw [hQ1, hQI, hB]
  linear_combination (-4) * hn

/-- Curvature helper: `n(w) = ∂_τ E(w, 0) = λξ · (X(w) - c(w))` with `X = (W, ξ)` and
`c(w) = (w, 1/λ)` the Euclidean centre of the horosphere `∂B_w`. -/
theorem s02_curv_normal_eq {Ω : Set ℂ} {w : ℂ} (hl : 0 < poincareDensity Ω w) :
    deriv (fun τ : ℝ => normalGeod Ω w τ) 0 =
      (((poincareDensity Ω w * (epstein Ω w).2 : ℝ) : ℂ) * ((epstein Ω w).1 - w),
        (epstein Ω w).2 * (poincareDensity Ω w * (epstein Ω w).2 - 1)) := by
  rw [(s02_hasDerivAt_normalGeod Ω w hl).deriv]
  unfold epstein
  generalize poincareDensity Ω w = l at hl ⊢
  generalize ‖logDensityDz Ω w‖ = r
  generalize conj (logDensityDz Ω w) = B
  have hN : r ^ 2 + (l / 2) ^ 2 ≠ 0 := by positivity
  have hD : l ^ 2 + 4 * r ^ 2 ≠ 0 := by positivity
  have hDc : ((l : ℂ) ^ 2 + 4 * (r : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hD
  refine Prod.ext ?_ ?_
  · dsimp only
    have e : l ^ 2 / 2 / (r ^ 2 + (l / 2) ^ 2) ^ 2 =
        l * (2 * l / (l ^ 2 + 4 * r ^ 2)) * 4 / (l ^ 2 + 4 * r ^ 2) := by
      field_simp
      ring
    rw [e]
    push_cast
    ring
  · dsimp only
    field_simp
    ring

/-- Curvature helper: the derivative of `n` in `w`, from `n = (λξ (W - w), ξ (λξ - 1))`,
`dλ(u) = 2λ Re(A u)` and `dX`. -/
theorem s02_curv_hasFDerivAt_normal {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    {w : ℂ} (hw : w ∈ Ω) :
    ∃ Ln : ℂ →L[ℝ] ℂ × ℝ, HasFDerivAt (fun w' => deriv (fun τ : ℝ => normalGeod Ω w' τ) 0) Ln w ∧
      ∀ u, Ln u =
        ((((poincareDensity Ω w * (2 * (logDensityDz Ω w * u).re)) * (epstein Ω w).2 +
              poincareDensity Ω w * (fderiv ℝ (epstein Ω) w u).2 : ℝ) : ℂ) *
            ((epstein Ω w).1 - w) +
          ((poincareDensity Ω w * (epstein Ω w).2 : ℝ) : ℂ) * ((fderiv ℝ (epstein Ω) w u).1 - u),
        (fderiv ℝ (epstein Ω) w u).2 * (poincareDensity Ω w * (epstein Ω w).2 - 1) +
          (epstein Ω w).2 * ((poincareDensity Ω w * (2 * (logDensityDz Ω w * u).re)) *
              (epstein Ω w).2 + poincareDensity Ω w * (fderiv ℝ (epstein Ω) w u).2)) := by
  obtain ⟨Ll, hLl, hLlv⟩ := s02_fff_hasFDerivAt_lambda hf hw
  obtain ⟨L, hL, -⟩ := s02_fff_hasFDerivAt_epstein hf hw
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have h1 := hL.fst
  have h2 := hL.snd
  have hlξ := hLl.mul h2
  have hc := (Complex.ofRealCLM.hasFDerivAt).comp w hlξ
  have hP := h1.sub (hasFDerivAt_id w)
  have hfirst := hc.mul hP
  have hsecond := h2.mul (hlξ.sub_const 1)
  refine ⟨_, (hfirst.prodMk hsecond).congr_of_eventuallyEq ?_, fun u => ?_⟩
  · filter_upwards [hΩo.mem_nhds hw] with x hx
    exact s02_curv_normal_eq (s02_poincareDensity_pos ⟨f, hf⟩ hx)
  · rw [hL.fderiv]
    refine Prod.ext ?_ ?_
    · simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        ContinuousLinearMap.id_apply, Complex.ofRealCLM_apply, smul_eq_mul,
        Function.comp_apply, Pi.mul_apply, Pi.sub_apply, id_eq, hLlv u]
      push_cast
      ring
    · simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_snd', smul_eq_mul, Pi.mul_apply, hLlv u]
      ring

/-- Curvature helper (algebra): `dX(v)` is Euclidean-orthogonal to `X - c`, for any value `dA` of
the derivative of `A` (the horosphere envelope condition). -/
theorem s02_curv_orth_alg {l dl D : ℝ} {A dA v : ℂ} (hl : 0 < l)
    (hdl : dl = l * (2 * (A * v).re)) (hD : D = l ^ 2 + 4 * ‖A‖ ^ 2) :
    ((4 * conj A / ((D : ℝ) : ℂ)) * conj (v + 4 * conj dA * ((D⁻¹ : ℝ) : ℂ) -
        4 * conj A * (((2 * l * dl + 8 * (conj A * dA).re) / D ^ 2 : ℝ) : ℂ))).re +
      (2 * l / D - 1 / l) *
        (2 * dl / D - 2 * l * (2 * l * dl + 8 * (conj A * dA).re) / D ^ 2) = 0 := by
  have h4 : 4 * conj A / ((D : ℝ) : ℂ) = conj A * ((4 / D : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h4]
  subst hdl
  simp only [map_sub, map_add, map_mul, Complex.conj_conj, Complex.conj_ofReal, map_ofNat,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.add_re, Complex.sub_im,
    Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat]
  rw [Complex.sq_norm, Complex.normSq_apply] at hD
  subst hD
  have hD0 : l ^ 2 + 4 * (A.re * A.re + A.im * A.im) ≠ 0 :=
    (by nlinarith [mul_self_nonneg A.re, mul_self_nonneg A.im, pow_pos hl 2] :
      (0 : ℝ) < l ^ 2 + 4 * (A.re * A.re + A.im * A.im)).ne'
  field_simp
  ring

/-- Curvature helper (algebra): the shape-operator pairing.  With `n = λξ P̂`, `P̂ = (P, ξ - 1/λ)`,
`Dn = d(λξ) P̂ + λξ (a - (u, -dλ/λ²))` and `a, b ⊥ P̂`, the Levi-Civita term gives
`⟨-∇_a n, b⟩ = -⟨a, b⟩ + (λ/ξ) ⟨(u, -dλ/λ²), b⟩_E`. -/
theorem s02_curv_shape_alg {l ξ dl : ℝ} {P u : ℂ} {q a b n Dn : ℂ × ℝ} (hl : 0 < l)
    (hξ : 0 < ξ) (hq : q.2 = ξ) (hn : n = (((l * ξ : ℝ) : ℂ) * P, ξ * (l * ξ - 1)))
    (hDn : Dn = ((((dl * ξ + l * a.2 : ℝ) : ℂ) * P + ((l * ξ : ℝ) : ℂ) * (a.1 - u),
      a.2 * (l * ξ - 1) + ξ * (dl * ξ + l * a.2))))
    (ha : (P * conj a.1).re + (ξ - 1 / l) * a.2 = 0)
    (hb : (P * conj b.1).re + (ξ - 1 / l) * b.2 = 0) :
    hypInner q (-(Dn - (a.2 / q.2) • n - (n.2 / q.2) • a +
        (((a.1 * conj n.1).re + a.2 * n.2) / q.2) • ((0 : ℂ), (1 : ℝ)))) b =
      -hypInner q a b + l / ξ * ((u * conj b.1).re - dl * b.2 / l ^ 2) := by
  subst hn hDn
  unfold hypInner
  rw [hq]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im] at ha hb
  simp only [Prod.fst_neg, Prod.snd_neg, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Complex.real_smul, mul_zero, mul_one,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.neg_re,
    Complex.neg_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im]
  have hl0 : l ≠ 0 := hl.ne'
  have hξ0 : ξ ≠ 0 := hξ.ne'
  linear_combination (norm := skip) (-l * b.2 / ξ ^ 2) * ha + (-dl / ξ) * hb
  field_simp
  ring

/-- Curvature helper (algebra): `(λ/ξ) ⟨(u, -dλ(u)/λ²), dX(v)⟩_E = λ² Re(u v̄) + Re(S u v)`, with
`dA(v) = (A² + S/2) v + (λ²/4) v̄`. -/
theorem s02_curv_M_alg {l dl dlu D : ℝ} {A S u v dA : ℂ} (hl : 0 < l)
    (hdl : dl = l * (2 * (A * v).re)) (hdlu : dlu = l * (2 * (A * u).re))
    (hdA : dA = (A ^ 2 + S / 2) * v + ((l ^ 2 / 4 : ℝ) : ℂ) * conj v)
    (hD : D = l ^ 2 + 4 * ‖A‖ ^ 2) :
    l / (2 * l / D) * ((u * conj (v + 4 * conj dA * ((D⁻¹ : ℝ) : ℂ) -
        4 * conj A * (((2 * l * dl + 8 * (conj A * dA).re) / D ^ 2 : ℝ) : ℂ))).re -
      dlu * (2 * dl / D - 2 * l * (2 * l * dl + 8 * (conj A * dA).re) / D ^ 2) / l ^ 2) =
      l ^ 2 * (u * conj v).re + (S * u * v).re := by
  subst hdl hdlu hdA
  rw [Complex.sq_norm, Complex.normSq_apply] at hD
  subst hD
  simp only [map_sub, map_add, map_mul, Complex.conj_conj, Complex.conj_ofReal, map_ofNat,
    pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.add_re, Complex.sub_im,
    Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.div_ofNat_re, Complex.div_ofNat_im]
  have hl0 : l ≠ 0 := hl.ne'
  have hD0 : l * l + 4 * (A.re * A.re + A.im * A.im) ≠ 0 :=
    (by nlinarith [mul_self_nonneg A.re, mul_self_nonneg A.im, mul_pos hl hl] :
      (0 : ℝ) < l * l + 4 * (A.re * A.re + A.im * A.im)).ne'
  field_simp
  ring

/-- Curvature helper: the polarized first fundamental form,
`I(u, v) = (1 + s²) λ² Re(u v̄) + 2 Re(S(f⁻¹) u v)` (from Lemma 2.5). -/
theorem s02_curv_fI {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) (u v : ℂ) :
    hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w u) (fderiv ℝ (epstein Ω) w v) =
      (1 + schwarzNorm Ω w ^ 2) * poincareDensity Ω w ^ 2 * (u * conj v).re +
        2 * (schwarzian (Function.invFunOn f unitDisc) w * u * v).re := by
  have h1 := lem_fff hf hw u
  have h2 := lem_fff hf hw v
  have h3 := lem_fff hf hw (u + v)
  rw [map_add, s02_hypInner_add] at h3
  generalize schwarzian (Function.invFunOn f unitDisc) w = S at h1 h2 h3 ⊢
  have hn : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 + 2 * (u * conj v).re := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.add_re, Complex.add_im]
    ring
  have hS : (S * (u + v) ^ 2).re = (S * u ^ 2).re + (S * v ^ 2).re + 2 * (S * u * v).re := by
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
    ring
  rw [hn, hS] at h3
  linear_combination (h3 - h1 - h2) / 2

/-- Curvature helper (algebra): with `I = (1+s²)λ² ρ̂ + 2Q` and `II = λ² ρ̂ + Q - I` in the frame
`(1, i)` (`Q = [[a, -b], [-b, -a]]`, `a² + b² = (sλ²)²`), `det(II - κ I)` factors as claimed.
The hypothesis `s ≠ 1` is the paper's own ("at points with `s ≠ 1`", i.e. off the fold set where
`X` fails to be an immersion); `s > 1` is allowed.  It is used only to clear the denominator
`1 - s`; `1 + s ≠ 0` comes from `s ≥ 0`. -/
theorem s02_curv_det_alg {l s a b κ : ℝ} (hl : 0 < l) (hs0 : 0 ≤ s) (hs : s ≠ 1)
    (hab : a ^ 2 + b ^ 2 = (s * l ^ 2) ^ 2) :
    ((l ^ 2 + a - ((1 + s ^ 2) * l ^ 2 + 2 * a)) - κ * ((1 + s ^ 2) * l ^ 2 + 2 * a)) *
        ((l ^ 2 - a - ((1 + s ^ 2) * l ^ 2 - 2 * a)) - κ * ((1 + s ^ 2) * l ^ 2 - 2 * a)) -
      ((-b - -2 * b) - κ * (-2 * b)) * ((-b - -2 * b) - κ * (-2 * b)) =
      (((1 + s ^ 2) * l ^ 2 + 2 * a) * ((1 + s ^ 2) * l ^ 2 - 2 * a) - (-2 * b) * (-2 * b)) *
        ((κ + s / (1 + s)) * (κ - s / (1 - s))) := by
  -- `hl` is not needed: the identity holds for every `l` (the statement stays true without it).
  have _hl := hl
  have hp : 1 + s ≠ 0 := by positivity
  have hm : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hX : (κ + s / (1 + s)) * (κ - s / (1 - s)) =
      ((1 + s) * (1 + κ) - 1) * ((1 - s) * (1 + κ) - 1) / ((1 + s) * (1 - s)) := by
    field_simp
    ring
  rw [hX, mul_div_assoc', eq_div_iff (mul_ne_zero hp hm)]
  linear_combination (-(2 * (1 + κ) - 1) ^ 2 * ((1 + s) * (1 - s)) +
    4 * (((1 + s) * (1 + κ) - 1) * ((1 - s) * (1 + κ) - 1))) * hab

/-- Proposition 2.6 `prop:curvature`, `sec02-prelim.tex:357` (BBVW): at `s ≠ 1` the principal
curvatures of `Σ` are `-s/(1+s)` and `s/(1-s)`.

The shape operator is `B = -∇n` for the unit normal `n(w) = ∂_τ E(w, 0)` (pointing away from
`w`), `∇` the Levi-Civita connection of `ξ⁻²(|dW|² + dξ²)`:
`∇_a n = Dn(a) - (a_ξ/ξ) n - (n_ξ/ξ) a + (⟨a, n⟩_E/ξ) e_ξ`.  With `I(u,v) = ⟨dX u, dX v⟩` and
`II(u,v) = ⟨B u, dX v⟩` in the frame `(1, i)`, the principal curvatures are the roots of
`det(II - κ I) = det I · (κ - κ₁)(κ - κ₂)`.  Hence `H = (κ₁ + κ₂)/2 = -κ₁κ₂ = s²/(1-s²)`, which with
the signed area element `(1-s²) dâ` (Lemma 2.5) is `H da = -det B da = s² dâ`. -/
theorem prop_curvature {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) (hs : schwarzNorm Ω w ≠ 1) :
    let s := schwarzNorm Ω w
    let q := epstein Ω w
    let dX : ℂ → ℂ × ℝ := fun v => fderiv ℝ (epstein Ω) w v
    let n : ℂ → ℂ × ℝ := fun w' => deriv (fun τ : ℝ => normalGeod Ω w' τ) 0
    let nab : ℂ → ℂ × ℝ := fun u =>
      fderiv ℝ n w u - ((dX u).2 / q.2) • n w - ((n w).2 / q.2) • dX u +
        ((((dX u).1 * conj (n w).1).re + (dX u).2 * (n w).2) / q.2) • ((0 : ℂ), (1 : ℝ))
    let fI : ℂ → ℂ → ℝ := fun u v => hypInner q (dX u) (dX v)
    let fII : ℂ → ℂ → ℝ := fun u v => hypInner q (-nab u) (dX v)
    ∀ κ : ℝ,
      (fII 1 1 - κ * fI 1 1) * (fII Complex.I Complex.I - κ * fI Complex.I Complex.I) -
          (fII 1 Complex.I - κ * fI 1 Complex.I) * (fII Complex.I 1 - κ * fI Complex.I 1) =
        (fI 1 1 * fI Complex.I Complex.I - fI 1 Complex.I * fI Complex.I 1) *
          ((κ + s / (1 + s)) * (κ - s / (1 - s))) := by
  intro s q dX n nab fI fII κ
  obtain ⟨f, hf⟩ := id hΩ
  have hl := s02_poincareDensity_pos hΩ hw
  obtain ⟨Ll, hLl, hLlv⟩ := s02_fff_hasFDerivAt_lambda hf hw
  obtain ⟨LA, hLA, hLAv⟩ := s02_fff_hasFDerivAt_A hf hw
  obtain ⟨L, hL, hLv⟩ := s02_fff_hasFDerivAt_ep hLl hLA hl
  have hX : fderiv ℝ (epstein Ω) w = L := hL.fderiv
  obtain ⟨Ln, hLn, hLnv⟩ := s02_curv_hasFDerivAt_normal hf hw
  have hnd : fderiv ℝ n w = Ln := hLn.fderiv
  have hnw : n w = (((poincareDensity Ω w * q.2 : ℝ) : ℂ) * (q.1 - w),
      q.2 * (poincareDensity Ω w * q.2 - 1)) := s02_curv_normal_eq hl
  set l := poincareDensity Ω w with hldef
  set A := logDensityDz Ω w with hAdef
  set S := schwarzian (Function.invFunOn f unitDisc) w with hSdef
  set D := l ^ 2 + 4 * ‖A‖ ^ 2 with hD
  have hD0 : 0 < D := by positivity
  have hξ : q.2 = 2 * l / D := rfl
  have hξ0 : 0 < q.2 := by rw [hξ]; positivity
  have hP : q.1 - w = 4 * conj A / ((D : ℝ) : ℂ) := by
    show w + 4 * conj A / ((D : ℝ) : ℂ) - w = _
    ring
  -- `dX(v) ⊥ X - c` (Euclidean)
  have horth : ∀ v, ((q.1 - w) * conj (dX v).1).re + (q.2 - 1 / l) * (dX v).2 = 0 := by
    intro v
    show ((q.1 - w) * conj (fderiv ℝ (epstein Ω) w v).1).re +
      (q.2 - 1 / l) * (fderiv ℝ (epstein Ω) w v).2 = 0
    rw [hX, hLv v, hP, hξ]
    exact s02_curv_orth_alg hl (hLlv v) rfl
  -- `II(u, v) = λ² Re(u v̄) + Re(S u v) - I(u, v)`
  have key : ∀ u v, fII u v = l ^ 2 * (u * conj v).re + (S * u * v).re - fI u v := by
    intro u v
    have h1 := s02_curv_shape_alg (q := q) (a := dX u) (b := dX v) (n := n w)
      (Dn := fderiv ℝ n w u) (u := u) (dl := Ll u) (P := q.1 - w) hl hξ0 rfl hnw
      (by rw [hnd, hLnv u, hLlv u]) (horth u) (horth v)
    have h2 : l / q.2 * ((u * conj (dX v).1).re - Ll u * (dX v).2 / l ^ 2) =
        l ^ 2 * (u * conj v).re + (S * u * v).re := by
      show l / q.2 * ((u * conj (fderiv ℝ (epstein Ω) w v).1).re -
        Ll u * (fderiv ℝ (epstein Ω) w v).2 / l ^ 2) = _
      rw [hX, hLv v, hξ]
      exact s02_curv_M_alg hl (hLlv v) (hLlv u) (hLAv v) rfl
    show hypInner q (-nab u) (dX v) = _
    rw [h1, h2]
    ring
  have hfI : ∀ u v, fI u v = (1 + s ^ 2) * l ^ 2 * (u * conj v).re + 2 * (S * u * v).re :=
    s02_curv_fI hf hw
  have hS : ‖S‖ = s * l ^ 2 := by
    rw [show s = schwarzNorm Ω w from rfl, eq_def_s hf hw, ← hSdef, ← hldef]
    field_simp
  have hs0 : 0 ≤ s := by
    rw [show s = schwarzNorm Ω w from rfl, eq_def_s hf hw]
    positivity
  have hab : S.re ^ 2 + S.im ^ 2 = (s * l ^ 2) ^ 2 := by
    rw [← hS, Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [key 1 1, key 1 I, key I 1, key I I, hfI 1 1, hfI 1 I, hfI I 1, hfI I I]
  simp only [map_one, conj_I, mul_one, one_mul, Complex.one_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.neg_re, mul_zero, mul_neg, neg_neg, zero_sub, Complex.mul_im, add_zero,
    zero_add]
  convert s02_curv_det_alg (κ := κ) hl hs0 hs hab using 1 <;> ring

/-- Proposition 2.6 `prop:curvature`, `sec02-prelim.tex:365`: the form `s² dâ` is smooth on `Ω`. -/
theorem prop_curvature_smooth {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => schwarzNorm Ω w ^ 2 * poincareDensity Ω w ^ 2) Ω := by
  obtain ⟨f, hf⟩ := hΩ
  have hl := s02_contDiffOn_poincareDensity hf
  obtain ⟨-, -, -, hS⟩ := s02_contDiffOn_invFun hf
  have hlne : ∀ w ∈ Ω, poincareDensity Ω w ^ 2 ≠ 0 := fun w hw =>
    pow_ne_zero 2 (s02_poincareDensity_pos ⟨f, hf⟩ hw).ne'
  have h := (hS.norm_sq ℝ).div (hl.pow 2) hlne
  refine h.congr fun w hw => ?_
  have hlp := s02_poincareDensity_pos ⟨f, hf⟩ hw
  show schwarzNorm Ω w ^ 2 * poincareDensity Ω w ^ 2 =
    ‖schwarzian (Function.invFunOn f unitDisc) w‖ ^ 2 / poincareDensity Ω w ^ 2
  rw [eq_def_s hf hw]
  field_simp

/-! ## §2.6 The horoball gap -/

/-- The domain `Ω = F(ℍ)` of a Jordan pair through `∞` has a Riemann map. -/
theorem s02_jordanPair_riemannMap {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) :
    ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω := by
  obtain ⟨F, hFΩ, -⟩ := hΓ
  have hconv : Convex ℝ upperHalf := convex_halfSpace_im_gt 0
  have hne : upperHalf.Nonempty := ⟨I, by simp [upperHalf]⟩
  have : ContractibleSpace ↥upperHalf := hconv.contractibleSpace hne
  have hsc : SimplyConnectedSpace ↥(F '' upperHalf) :=
    ContinuousMap.HomotopyEquiv.simplyConnectedSpace (F.image upperHalf).symm.toHomotopyEquiv
  subst hFΩ
  have hH : IsHyperbolicSimplyConnected (F '' upperHalf) := by
    refine ⟨F.isOpenMap _ (isOpen_lt continuous_const Complex.continuous_im),
      (hconv.isConnected hne).image F F.continuous.continuousOn, hsc, fun h => ?_⟩
    have h1 : F (-I) ∈ F '' upperHalf := h ▸ mem_univ _
    obtain ⟨z, hz, hzF⟩ := h1
    rw [F.injective hzF] at hz
    norm_num [upperHalf] at hz
  obtain ⟨φ, hφ⟩ := lehto_exists_conformal hH
  exact ⟨_, hφ.symm hH.1⟩

/-- `λ` is continuous on `Ω`. -/
theorem s02_continuousAt_poincareDensity {Ω : Set ℂ}
    (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ} (hw : w ∈ Ω) :
    ContinuousAt (poincareDensity Ω) w := by
  obtain ⟨f, hf⟩ := hΩ
  have h1 : ContinuousAt (Real.exp ∘ fun x => Real.log (poincareDensity Ω x)) w :=
    Real.continuous_exp.continuousAt.comp
      (s02_differentiableAt_logDensity ⟨f, hf⟩ hw).continuousAt
  refine h1.congr ?_
  filter_upwards [(hf.isOpen isOpen_ball).mem_nhds hw] with x hx
  show Real.exp (Real.log (poincareDensity Ω x)) = poincareDensity Ω x
  exact Real.exp_log (s02_poincareDensity_pos ⟨f, hf⟩ hx)

/-- Lemma 2.7 `lem:proper`, (2.15) `eq:proper`, `sec02-prelim.tex:386`: if `Φ_q(w) ≤ T` then
`d(w) ≥ ξ/(4T)` and `|W-w|² ≤ 4Tξ d(w) ≤ 4Tξ(|W-w| + |W-x₀|)` (`∞ ∈ Γ`, `x₀ ∈ Γ ∩ ℂ`). -/
theorem lem_proper {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) {x₀ : ℂ}
    (hx₀ : x₀ ∈ curveOf Ω Ωs) {q : ℂ × ℝ} (hq : q ∈ UHS) {w : ℂ} (hw : w ∈ Ω) {T : ℝ}
    (hT : horoPhi Ω q w ≤ T) :
    q.2 / (4 * T) ≤ infDist w Ωᶜ ∧ ‖q.1 - w‖ ^ 2 ≤ 4 * T * q.2 * infDist w Ωᶜ ∧
      4 * T * q.2 * infDist w Ωᶜ ≤ 4 * T * q.2 * (‖q.1 - w‖ + ‖q.1 - x₀‖) := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hΓ
  have hξ : 0 < q.2 := hq
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hw
  have hd := s02_infDist_pos hf hw
  have hx₀Ω : x₀ ∈ Ωᶜ := fun h => hx₀ (Or.inl h)
  obtain ⟨z, hz, rfl⟩ : w ∈ f '' unitDisc := by rw [hf.2.2]; exact hw
  have hk0 := (lem_koebe_a hf hz).2.2.1
  rw [div_le_iff₀ (by positivity)] at hk0
  unfold horoPhi at hT
  rw [div_le_iff₀ (by positivity)] at hT
  set d := infDist (f z) Ωᶜ
  set l := poincareDensity Ω (f z)
  set a := ‖q.1 - f z‖
  have hT0 : 0 < T := by
    have : 0 < l * (a ^ 2 + q.2 ^ 2) := by positivity
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    have key : 0 ≤ q.2 * (d * (4 * T) - q.2) := by
      nlinarith [mul_nonneg (sq_nonneg q.2) (sub_nonneg.mpr hk0),
        mul_nonneg hd.le (sub_nonneg.mpr hT), mul_nonneg (mul_nonneg hd.le hl.le) (sq_nonneg a)]
    have := (mul_nonneg_iff_of_pos_left hξ).mp key
    linarith
  · nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hk0),
      mul_nonneg hd.le (sub_nonneg.mpr hT), mul_nonneg (mul_nonneg hd.le hl.le) (sq_nonneg q.2)]
  · have h1 : d ≤ ‖f z - x₀‖ := by
      rw [← dist_eq_norm]
      exact infDist_le_dist_of_mem hx₀Ω
    have h2 : ‖f z - x₀‖ ≤ a + ‖q.1 - x₀‖ := by
      calc ‖f z - x₀‖ = ‖(q.1 - x₀) - (q.1 - f z)‖ := by congr 1; ring
        _ ≤ ‖q.1 - x₀‖ + ‖q.1 - f z‖ := norm_sub_le _ _
        _ = a + ‖q.1 - x₀‖ := add_comm _ _
    have h4 : 0 ≤ 4 * T * q.2 := by positivity
    exact mul_le_mul_of_nonneg_left (h1.trans h2) h4

/-- Lemma 2.7 `lem:proper`, `sec02-prelim.tex:393`: for compact `𝒬 ⊆ ℍ³` and `T < ∞`,
`{w : Φ_q(w) ≤ T for some q ∈ 𝒬}` is relatively compact in `Ω`. -/
theorem lem_proper_compact {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) {𝒬 : Set (ℂ × ℝ)}
    (h𝒬 : IsCompact 𝒬) (h𝒬U : 𝒬 ⊆ UHS) (T : ℝ) :
    ∃ K' : Set ℂ, IsCompact K' ∧ K' ⊆ Ω ∧
      {w | w ∈ Ω ∧ ∃ q ∈ 𝒬, horoPhi Ω q w ≤ T} ⊆ K' := by
  obtain ⟨F, hFΩ, hFs⟩ := id hΓ
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hΓ
  -- a point of the curve
  have hx₀ : F 0 ∈ curveOf Ω Ωs := by
    rintro (h | h)
    · rw [← hFΩ] at h
      obtain ⟨z, hz, hzF⟩ := h
      rw [F.injective hzF] at hz
      norm_num [upperHalf] at hz
    · rw [← hFs] at h
      obtain ⟨z, hz, hzF⟩ := h
      rw [F.injective hzF] at hz
      simp [lowerHalf] at hz
  set x₀ := F 0
  rcases 𝒬.eq_empty_or_nonempty with h0 | hne
  · refine ⟨∅, isCompact_empty, empty_subset _, ?_⟩
    rintro w ⟨-, q, hq, -⟩
    rw [h0] at hq
    exact hq.elim
  by_cases hT : T ≤ 0
  · refine ⟨∅, isCompact_empty, empty_subset _, ?_⟩
    rintro w ⟨hw, q, hq, hΦ⟩
    have hq2 : 0 < q.2 := h𝒬U hq
    have hl := s02_poincareDensity_pos ⟨f, hf⟩ hw
    have : 0 < horoPhi Ω q w := by unfold horoPhi; positivity
    linarith
  push Not at hT
  obtain ⟨q₀, hq₀, hmin⟩ := h𝒬.exists_isMinOn hne continuous_snd.continuousOn
  have hξ0 : 0 < q₀.2 := h𝒬U hq₀
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp h𝒬.isBounded
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM q₀ hq₀)
  set δ := q₀.2 / (4 * T) with hδ
  set B := 4 * T * M with hB
  set c := M + ‖x₀‖ with hc
  have hB0 : 0 ≤ B := by positivity
  have hc0 : 0 ≤ c := by positivity
  refine ⟨closedBall 0 (M + B + c) ∩ {w | δ ≤ infDist w Ωᶜ},
    (isCompact_closedBall 0 _).inter_right (isClosed_le continuous_const (continuous_infDist_pt Ωᶜ)),
    ?_, ?_⟩
  · rintro w ⟨-, hw⟩
    by_contra hwΩ
    have h1 : infDist w Ωᶜ = 0 := infDist_zero_of_mem hwΩ
    have h2 : 0 < δ := by positivity
    have h3 : δ ≤ infDist w Ωᶜ := hw
    linarith
  · rintro w ⟨hw, q, hq, hΦ⟩
    have hq2 : 0 < q.2 := h𝒬U hq
    obtain ⟨h1, h2, h3⟩ := lem_proper hΓ hx₀ (h𝒬U hq) hw hΦ
    have hM1 : ‖q.1‖ ≤ M := (norm_fst_le q).trans (hM q hq)
    have hM2 : q.2 ≤ M := by
      have := (norm_snd_le q).trans (hM q hq)
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans this
    have hqmin : q₀.2 ≤ q.2 := isMinOn_iff.mp hmin q hq
    refine ⟨?_, ?_⟩
    · set a := ‖q.1 - w‖
      have e1 : 4 * T * q.2 ≤ B := mul_le_mul_of_nonneg_left hM2 (by positivity)
      have e2 : ‖q.1 - x₀‖ ≤ c := (norm_sub_le _ _).trans (by linarith)
      have ha2 : a ^ 2 ≤ B * (a + c) :=
        calc a ^ 2 ≤ 4 * T * q.2 * (a + ‖q.1 - x₀‖) := h2.trans h3
          _ ≤ B * (a + c) :=
            mul_le_mul e1 (by linarith) (by positivity) hB0
      have hab : a ≤ B + c := by
        by_contra h
        push Not at h
        nlinarith [mul_nonneg hc0 (show 0 ≤ a - B by linarith)]
      rw [mem_closedBall_zero_iff]
      calc ‖w‖ = ‖q.1 - (q.1 - w)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖q.1‖ + a := norm_sub_le _ _
        _ ≤ M + B + c := by linarith
    · show δ ≤ infDist w Ωᶜ
      calc δ = q₀.2 / (4 * T) := hδ
        _ ≤ q.2 / (4 * T) := by gcongr
        _ ≤ infDist w Ωᶜ := h1

/-- Lemma 2.7 `lem:proper`, `sec02-prelim.tex:395`: `Φ_q` attains its minimum on `Ω`. -/
theorem lem_proper_min {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) {q : ℂ × ℝ} (hq : q ∈ UHS) :
    ∃ w ∈ Ω, ∀ w' ∈ Ω, horoPhi Ω q w ≤ horoPhi Ω q w' := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hΓ
  have hξ : 0 < q.2 := hq
  obtain ⟨w₀, hw₀⟩ : Ω.Nonempty := by
    rw [← hf.2.2]
    exact ⟨f 0, mem_image_of_mem f (mem_ball_self one_pos)⟩
  obtain ⟨K, hK, hKΩ, hsub⟩ := lem_proper_compact hΓ isCompact_singleton
    (singleton_subset_iff.mpr hq) (horoPhi Ω q w₀)
  have hw₀K : w₀ ∈ K := hsub ⟨hw₀, q, mem_singleton q, le_rfl⟩
  have hcont : ContinuousOn (fun w' => horoPhi Ω q w') K := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hlc := s02_continuousAt_poincareDensity ⟨f, hf⟩ (hKΩ hx)
    unfold horoPhi
    exact (hlc.mul (by fun_prop)).div_const _
  obtain ⟨wm, hwm, hmin⟩ := hK.exists_isMinOn ⟨w₀, hw₀K⟩ hcont
  refine ⟨wm, hKΩ hwm, fun w' hw' => ?_⟩
  by_cases h : horoPhi Ω q w' ≤ horoPhi Ω q w₀
  · exact isMinOn_iff.mp hmin w' (hsub ⟨hw', q, mem_singleton q, h⟩)
  · push Not at h
    exact (isMinOn_iff.mp hmin w₀ hw₀K).trans h.le

/-- Lemma 2.7 `lem:proper`, `sec02-prelim.tex:396`: `U` is closed in `ℍ³`. -/
theorem lem_proper_closed {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) :
    closure (horoUnion Ω) ∩ UHS = horoUnion Ω := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hΓ
  have hUH : horoUnion Ω ⊆ UHS := by
    intro p hp
    simp only [horoUnion, mem_iUnion] at hp
    obtain ⟨w, -, hpB⟩ := hp
    exact hpB.1
  refine Subset.antisymm ?_ (subset_inter subset_closure hUH)
  rintro q ⟨hqc, hq⟩
  by_contra hqU
  have hξ : 0 < q.2 := hq
  have h𝒬U : closedBall q (q.2 / 2) ⊆ UHS := by
    intro p hp
    have h1 : |p.2 - q.2| ≤ q.2 / 2 := by
      have := (norm_snd_le (p - q)).trans (mem_closedBall_iff_norm.mp hp)
      simpa [Real.norm_eq_abs] using this
    show 0 < p.2
    have := (abs_le.mp h1).1
    linarith
  obtain ⟨K, hK, hKΩ, hsub⟩ :=
    lem_proper_compact hΓ (isCompact_closedBall q (q.2 / 2)) h𝒬U 1
  -- near `q`, every `Φ_p` exceeds `1` on `K`
  have hev : ∀ᶠ p in 𝓝 q, ∀ w ∈ K, 1 < horoPhi Ω p w := by
    apply hK.eventually_forall_of_forall_eventually
    intro w hw
    have hwΩ := hKΩ hw
    have h1 : 1 < horoPhi Ω q w := by
      by_contra h
      push Not at h
      apply hqU
      simp only [horoUnion, mem_iUnion]
      exact ⟨w, hwΩ, hq, h⟩
    have hc : ContinuousAt (fun z : (ℂ × ℝ) × ℂ => horoPhi Ω z.1 z.2) (q, w) := by
      have hlc : ContinuousAt (poincareDensity Ω ∘ Prod.snd) (q, w) :=
        ContinuousAt.comp (x := (q, w)) (s02_continuousAt_poincareDensity ⟨f, hf⟩ hwΩ)
          continuous_snd.continuousAt
      unfold horoPhi
      exact (hlc.mul (by fun_prop)).div (by fun_prop) (by show (2 : ℝ) * q.2 ≠ 0; positivity)
    exact hc.eventually (lt_mem_nhds h1)
  have hball : closedBall q (q.2 / 2) ∈ 𝓝 q := closedBall_mem_nhds q (by positivity)
  obtain ⟨p, ⟨hpK, hp𝒬⟩, hpU⟩ := mem_closure_iff_nhds.mp hqc _ (hev.and hball)
  simp only [horoUnion, mem_iUnion] at hpU
  obtain ⟨w, hw, hpB⟩ := hpU
  have hwK : w ∈ K := hsub ⟨hw, p, hp𝒬, hpB.2⟩
  linarith [hpK w hwK, hpB.2]

/-- (2.16) `eq:dist-U`, `sec02-prelim.tex:397`: for `q ∉ U`, `d(q, U) = min_{w ∈ Ω} log Φ_q(w)`. -/
theorem eq_dist_U {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) {q : ℂ × ℝ} (hq : q ∈ UHS)
    (hqU : q ∉ horoUnion Ω) :
    ∃ w ∈ Ω, (∀ w' ∈ Ω, horoPhi Ω q w ≤ horoPhi Ω q w') ∧
      hdistSet q (horoUnion Ω) = Real.log (horoPhi Ω q w) := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hΓ
  have hξ : 0 < q.2 := hq
  obtain ⟨w, hw, hmin⟩ := lem_proper_min hΓ hq
  refine ⟨w, hw, hmin, ?_⟩
  have hqB : q ∉ horoball Ω w := by
    intro h
    apply hqU
    simp only [horoUnion, mem_iUnion]
    exact ⟨w, hw, h⟩
  obtain ⟨-, ⟨p, hpB, hp⟩, -⟩ := lem_busemann_nearest ⟨f, hf⟩ hw hq hqB
  have hΦq : 0 < horoPhi Ω q w := by
    have := s02_poincareDensity_pos ⟨f, hf⟩ hw
    unfold horoPhi
    positivity
  have hleast : IsLeast (hdist q '' horoUnion Ω) (Real.log (horoPhi Ω q w)) := by
    refine ⟨⟨p, ?_, hp⟩, ?_⟩
    · simp only [horoUnion, mem_iUnion]
      exact ⟨w, hw, hpB⟩
    rintro x ⟨p', hp', rfl⟩
    simp only [horoUnion, mem_iUnion] at hp'
    obtain ⟨w', hw', hp'B⟩ := hp'
    have hb := lem_busemann ⟨f, hf⟩ hw' hq hp'B.1
    have hl := s02_poincareDensity_pos ⟨f, hf⟩ hw'
    have hp'2 : 0 < p'.2 := hp'B.1
    have hΦp : 0 < horoPhi Ω p' w' := by
      unfold horoPhi
      positivity
    have hlp : Real.log (horoPhi Ω p' w') ≤ 0 := Real.log_nonpos hΦp.le hp'B.2
    have hmono : Real.log (horoPhi Ω q w) ≤ Real.log (horoPhi Ω q w') :=
      Real.log_le_log hΦq (hmin w' hw')
    have := le_abs_self (Real.log (horoPhi Ω q w') - Real.log (horoPhi Ω p' w'))
    linarith
  unfold hdistSet
  exact hleast.csInf_eq

/-- Proposition 2.8(a) `prop:separation`, `sec02-prelim.tex:422`: with `f(0) = 0`, the horoball of
`ρ` at `0` is the ball of Euclidean diameter `|f'(0)|` tangent at `0`. -/
theorem prop_separation_a_disk {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (hf0 : f 0 = 0) :
    horoball Ω 0 = {q | q ∈ UHS ∧ ‖q.1‖ ^ 2 + q.2 ^ 2 ≤ ‖deriv f 0‖ * q.2} := by
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hl := eq_lambda_f hf h0
  rw [hf0, norm_zero] at hl
  have hd : 0 < ‖deriv f 0‖ :=
    norm_pos_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 h0)
  have hl' : poincareDensity Ω 0 = 2 / ‖deriv f 0‖ := by
    rw [eq_div_iff hd.ne', hl]
    norm_num
  ext q
  refine and_congr_right fun hq => ?_
  have hξ : 0 < q.2 := hq
  unfold horoPhi
  rw [sub_zero, hl', div_le_one (by positivity), div_mul_eq_mul_div, div_le_iff₀ hd]
  constructor <;> intro h <;> nlinarith

/-- The `≤` half of the area theorem (TT `r22_sum` without the null-complement hypothesis): the
partial Grunsky sums of a normalized disjoint pair are at most `log |g'(∞)|²`. -/
theorem s02_r22_partial_le {f g : ℂ → ℂ} (h : TakhtajanTeo.Ch2.IsNormalizedDisjointPair f g)
    (N : ℕ) :
    ∑ j ∈ Finset.range N, (((j + 1 : ℕ) : ℝ) * ‖TakhtajanTeo.Ch2.grunsky f g (-((j : ℤ) + 1)) 0‖ ^ 2 +
      ((j + 1 : ℕ) : ℝ) * ‖TakhtajanTeo.Ch2.grunsky f g ((j : ℤ) + 1) 0‖ ^ 2) ≤
      Real.log (‖TakhtajanTeo.derivAtInfty g‖ ^ 2) := by
  obtain ⟨r, hr, -, hlim⟩ := TakhtajanTeo.Ch2.mg_radius_seq
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ,
      ∀ j, a j = ((j + 1 : ℕ) : ℝ) * ‖TakhtajanTeo.Ch2.grunsky f g (-((j : ℤ) + 1)) 0‖ ^ 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ,
      ∀ j, c j = ((j + 1 : ℕ) : ℝ) * ‖TakhtajanTeo.Ch2.grunsky f g ((j : ℤ) + 1) 0‖ ^ 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = Real.log (‖TakhtajanTeo.derivAtInfty g‖ ^ 2) := ⟨_, rfl⟩
  have ha0 : ∀ j, 0 ≤ a j := fun j => by rw [ha]; positivity
  have hc0 : ∀ j, 0 ≤ c j := fun j => by rw [hc]; positivity
  have hpi : 0 < π := Real.pi_pos
  obtain ⟨I, hI⟩ : ∃ I : ℕ → ℝ, ∀ n, I n = ∫ w in (f '' closedBall (0 : ℂ) (r n) ∪
      g '' {z : ℂ | 1 / r n ≤ ‖z‖})ᶜ, 1 / ‖w‖ ^ 2 := ⟨_, fun _ => rfl⟩
  have hI0 : ∀ n, 0 ≤ I n := fun n => by rw [hI]; exact integral_nonneg (fun w => by positivity)
  have hSf : ∀ n, Summable (fun j : ℕ => a j * (r n) ^ (2 * (j + 1))) := fun n => by
    have := (TakhtajanTeo.Ch2.r22_f_circle h (hr n).1 (hr n).2).1
    refine this.congr (fun j => ?_)
    rw [ha, mul_assoc]
  have hSg : ∀ n, Summable (fun j : ℕ => c j * (r n) ^ (2 * (j + 1))) := fun n => by
    have := (TakhtajanTeo.Ch2.r22_g_circle h (hr n).1 (hr n).2).1
    refine this.congr (fun j => ?_)
    rw [hc, mul_assoc]
  have hEq : ∀ n, (∑' j : ℕ, a j * (r n) ^ (2 * (j + 1))) + (∑' j : ℕ, c j * (r n) ^ (2 * (j + 1))) =
      K - 2 * Real.log ((r n) ^ 2) - I n / π := by
    intro n
    have h1 := TakhtajanTeo.Ch2.r22_gap_eq h (hr n).1 (hr n).2
    rw [← hI n] at h1
    have e1 : (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) *
        (‖TakhtajanTeo.Ch2.grunsky f g (-((j : ℤ) + 1)) 0‖ ^ 2 * (r n) ^ (2 * (j + 1)))) =
        ∑' j : ℕ, a j * (r n) ^ (2 * (j + 1)) := tsum_congr (fun j => by rw [ha, mul_assoc])
    have e2 : (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) *
        (‖TakhtajanTeo.Ch2.grunsky f g ((j : ℤ) + 1) 0‖ ^ 2 * (r n) ^ (2 * (j + 1)))) =
        ∑' j : ℕ, c j * (r n) ^ (2 * (j + 1)) := tsum_congr (fun j => by rw [hc, mul_assoc])
    rw [e1, e2, ← hK] at h1
    field_simp
    linarith
  have hw : ∀ j : ℕ, Tendsto (fun n => (r n) ^ (2 * (j + 1))) atTop (𝓝 1) := fun j => by
    simpa using hlim.pow (2 * (j + 1))
  have hlog : Tendsto (fun n => Real.log ((r n) ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (r n) ^ 2) atTop (𝓝 1) := by simpa using hlim.pow 2
    have := h1.log (by norm_num)
    simpa using this
  have hV' : Tendsto (fun n => K - 2 * Real.log ((r n) ^ 2)) atTop (𝓝 K) := by
    have h2 := (tendsto_const_nhds (x := K)).sub (hlog.const_mul 2)
    simpa using h2
  have hbound : ∑ j ∈ Finset.range N, (a j + c j) ≤ K := by
    have h1 : ∀ n, ∑ j ∈ Finset.range N, (a j + c j) * (r n) ^ (2 * (j + 1)) ≤
        K - 2 * Real.log ((r n) ^ 2) := by
      intro n
      have hs := (hSf n).add (hSg n)
      have h2 : ∑ j ∈ Finset.range N, (a j * (r n) ^ (2 * (j + 1)) + c j * (r n) ^ (2 * (j + 1))) ≤
          ∑' j : ℕ, (a j * (r n) ^ (2 * (j + 1)) + c j * (r n) ^ (2 * (j + 1))) :=
        Summable.sum_le_tsum (Finset.range N) (fun j _ => by
          have := ha0 j; have := hc0 j; have := (hr n).1; positivity) hs
      have h3 := (hSf n).tsum_add (hSg n)
      have h4 := hEq n
      have h5 : 0 ≤ I n / π := div_nonneg (hI0 n) hpi.le
      calc ∑ j ∈ Finset.range N, (a j + c j) * (r n) ^ (2 * (j + 1))
          = ∑ j ∈ Finset.range N, (a j * (r n) ^ (2 * (j + 1)) + c j * (r n) ^ (2 * (j + 1))) :=
            Finset.sum_congr rfl (fun j _ => add_mul _ _ _)
        _ ≤ _ := h2
        _ = K - 2 * Real.log ((r n) ^ 2) - I n / π := by rw [h3, h4]
        _ ≤ K - 2 * Real.log ((r n) ^ 2) := by linarith
    have h2 : Tendsto (fun n => ∑ j ∈ Finset.range N, (a j + c j) * (r n) ^ (2 * (j + 1))) atTop
        (𝓝 (∑ j ∈ Finset.range N, (a j + c j))) := by
      have := tendsto_finsetSum (Finset.range N) (fun j _ => (hw j).const_mul (a j + c j))
      simpa using this
    exact le_of_tendsto_of_tendsto h2 hV' (Eventually.of_forall h1)
  simpa only [ha, hc, hK] using hbound

/-- The two complementary domains of `F(𝔻)`, `F(𝔻*)` (`F` a homeomorphism of `ℂ`) are disjoint. -/
theorem s02_homeo_disjoint {Ω Ωs : Set ℂ}
    (hΓ : ∃ F : ℂ ≃ₜ ℂ, F '' unitDisc = Ω ∧ F '' unitDiscExterior = Ωs) : Disjoint Ω Ωs := by
  obtain ⟨F, rfl, rfl⟩ := hΓ
  refine (disjoint_image_iff F.injective).mpr (Set.disjoint_left.mpr fun z hz hz' => ?_)
  have h1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have h2 : 1 < ‖z‖ := hz'
  linarith

/-- Local open mapping for a holomorphic map injective on a punctured neighbourhood of `z₀`. -/
theorem s02_nhds_le_map_of_injOn {φ : ℂ → ℂ} {s : Set ℂ} {z₀ : ℂ} (hs : s ∈ 𝓝 z₀)
    (hd : DifferentiableOn ℂ φ s) (hinj : InjOn φ (s \ {z₀})) : 𝓝 (φ z₀) ≤ map φ (𝓝 z₀) := by
  refine (hd.analyticAt hs).eventually_constant_or_nhds_le_map_nhds.resolve_left ?_
  intro hev
  obtain ⟨ε, hε, hεb⟩ := Metric.mem_nhds_iff.mp (inter_mem hev hs)
  have hm : ∀ t : ℝ, 0 < t → t < ε → φ (z₀ + t) = φ z₀ ∧ z₀ + t ∈ s \ {z₀} := by
    intro t ht0 htε
    have hmem : z₀ + t ∈ ball z₀ ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht0]
      exact htε
    obtain ⟨h1, h2⟩ := hεb hmem
    refine ⟨h1, h2, fun h3 => ?_⟩
    have h4 : z₀ + t = z₀ := h3
    have h5 : (t : ℂ) = 0 := by simpa using h4
    exact ht0.ne' (by exact_mod_cast h5)
  obtain ⟨h1, h1s⟩ := hm (ε / 2) (by positivity) (by linarith)
  obtain ⟨h2, h2s⟩ := hm (ε / 4) (by positivity) (by linarith)
  have h3 := hinj h1s h2s (h1.trans h2.symm)
  have h4 : ((ε / 2 : ℝ) : ℂ) = ((ε / 4 : ℝ) : ℂ) := add_left_cancel h3
  have h5 : ε / 2 = ε / 4 := Complex.ofReal_injective h4
  linarith

/-- For `g : 𝔻* → Ω*` conformal onto the outer domain of a Jordan curve, `c = lim g(z)/z ≠ 0`:
otherwise `ζ ↦ g(1/ζ)` extends holomorphically to `0`, and its value `w₀` there contradicts either
injectivity (`w₀ ∈ Ω*`) or `w₀ ∈ Γ ⊆ ∂Ω` (the punctured neighbourhood image lies in `Ω*`). -/
theorem s02_ext_coeff_ne_zero {Ω Ωs : Set ℂ}
    (hΓ : ∃ F : ℂ ≃ₜ ℂ, F '' unitDisc = Ω ∧ F '' unitDiscExterior = Ωs) {g : ℂ → ℂ}
    (hg : IsConformalOnto g unitDiscExterior Ωs) {c : ℂ}
    (hc : Tendsto (fun z => g z / z) (Bornology.cobounded ℂ) (𝓝 c)) : c ≠ 0 := by
  have hdisj := s02_homeo_disjoint hΓ
  obtain ⟨F, hFΩ, hFΩs⟩ := hΓ
  rintro rfl
  have hextO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hext : ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ < 1 → ζ⁻¹ ∈ unitDiscExterior := by
    intro ζ h0 h1
    show 1 < ‖ζ⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr h0)).mpr h1
  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℂ, H = fun ζ => ζ * g ζ⁻¹ := ⟨_, rfl⟩
  have hH0 : H 0 = 0 := by rw [hH]; exact zero_mul _
  have hHlim : Tendsto H (𝓝[≠] 0) (𝓝 0) := by
    have h1 := hc.comp tendsto_inv₀_nhdsNE_zero
    refine h1.congr (fun ζ => ?_)
    rw [hH]
    show g ζ⁻¹ / ζ⁻¹ = ζ * g ζ⁻¹
    rw [div_inv_eq_mul, mul_comm]
  have hHd : DifferentiableOn ℂ H (ball 0 1) := by
    refine (differentiableOn_compl_singleton_and_continuousAt_iff (ball_mem_nhds 0 one_pos)).mp
      ⟨?_, ?_⟩
    · intro ζ hζ
      have hζ0 : ζ ≠ 0 := hζ.2
      have hz := hext ζ hζ0 (mem_ball_zero_iff.mp hζ.1)
      have hgd : DifferentiableAt ℂ g ζ⁻¹ := hg.1.differentiableAt (hextO.mem_nhds hz)
      rw [hH]
      exact (differentiableAt_id.mul (hgd.comp ζ (differentiableAt_inv hζ0))).differentiableWithinAt
    · rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hH0]
      exact hHlim
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, G = dslope H 0 := ⟨_, rfl⟩
  have hGd : DifferentiableOn ℂ G (ball 0 1) := by
    rw [hG]
    exact (differentiableOn_dslope (ball_mem_nhds 0 one_pos)).mpr hHd
  have hGe : ∀ ζ, ζ ≠ 0 → G ζ = g ζ⁻¹ := by
    intro ζ hζ
    rw [hG, dslope_of_ne _ hζ, slope_def_field, hH0, hH]
    field_simp
    ring
  have hGinj : InjOn G (ball 0 1 \ {0}) := by
    intro x hx y hy hxy
    have hx0 : x ≠ 0 := hx.2
    have hy0 : y ≠ 0 := hy.2
    rw [hGe x hx0, hGe y hy0] at hxy
    exact inv_injective (hg.2.1 (hext x hx0 (mem_ball_zero_iff.mp hx.1))
      (hext y hy0 (mem_ball_zero_iff.mp hy.1)) hxy)
  have hopen := s02_nhds_le_map_of_injOn (ball_mem_nhds 0 one_pos) hGd hGinj
  by_cases hw : G 0 ∈ Ωs
  · rw [← hg.2.2] at hw
    obtain ⟨z₁, hz₁, hgz⟩ := hw
    have hs1 : unitDiscExterior ∈ 𝓝 z₁ := hextO.mem_nhds hz₁
    have hopen1 := s02_nhds_le_map_of_injOn hs1 hg.1 (hg.2.1.mono sdiff_subset)
    rw [hgz] at hopen1
    have hR : 0 < ‖z₁‖ + 1 := by positivity
    have hA : g '' (ball z₁ 1 ∩ unitDiscExterior) ∈ 𝓝 (G 0) :=
      hopen1 (image_mem_map (inter_mem (ball_mem_nhds z₁ one_pos) hs1))
    have hB : G '' ball 0 (1 / (‖z₁‖ + 1)) ∈ 𝓝 (G 0) :=
      hopen (image_mem_map (ball_mem_nhds 0 (by positivity)))
    have hAB : ∀ᶠ w in 𝓝[≠] (G 0), w ∈ g '' (ball z₁ 1 ∩ unitDiscExterior) ∩
        G '' ball 0 (1 / (‖z₁‖ + 1)) := nhdsWithin_le_nhds (inter_mem hA hB)
    obtain ⟨w, ⟨hwA, hwB⟩, hwne⟩ := (hAB.and self_mem_nhdsWithin).exists
    obtain ⟨a, ⟨haB, ha⟩, rfl⟩ := hwA
    obtain ⟨b, hb, hbw⟩ := hwB
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hwne hbw.symm
    have hbR : ‖b‖ < 1 / (‖z₁‖ + 1) := mem_ball_zero_iff.mp hb
    have hb1 : ‖b‖ < 1 :=
      lt_of_lt_of_le hbR (by rw [div_le_one hR]; linarith [norm_nonneg z₁])
    rw [hGe b hb0] at hbw
    have hab := hg.2.1 (hext b hb0 hb1) ha hbw
    have h1 : ‖a‖ < ‖z₁‖ + 1 := by
      have h2 : ‖a - z₁‖ < 1 := by
        have := mem_ball.mp haB
        rwa [dist_eq_norm] at this
      calc ‖a‖ = ‖z₁ + (a - z₁)‖ := by ring_nf
        _ ≤ ‖z₁‖ + ‖a - z₁‖ := norm_add_le _ _
        _ < ‖z₁‖ + 1 := by linarith
    have h2 : ‖z₁‖ + 1 < ‖b⁻¹‖ := by
      rw [norm_inv, lt_inv_comm₀ hR (norm_pos_iff.mpr hb0)]
      rwa [one_div] at hbR
    rw [hab] at h2
    linarith
  · have hS : G '' ball 0 1 ∈ 𝓝 (G 0) := hopen (image_mem_map (ball_mem_nhds 0 one_pos))
    have hSsub : G '' ball 0 1 ⊆ insert (G 0) Ωs := by
      rintro _ ⟨ζ, hζ, rfl⟩
      by_cases hζ0 : ζ = 0
      · left
        rw [hζ0]
      · right
        rw [hGe ζ hζ0, ← hg.2.2]
        exact mem_image_of_mem g (hext ζ hζ0 (mem_ball_zero_iff.mp hζ))
    have hΩo : IsOpen Ω := by
      rw [← hFΩ]
      exact F.isOpenMap _ isOpen_ball
    have hcl : G 0 ∈ closure Ω := by
      have hp : F.symm (G 0) ∈ closure unitDisc := by
        rw [show unitDisc = ball (0 : ℂ) 1 from rfl, closure_ball (0 : ℂ) one_ne_zero,
          mem_closedBall_zero_iff]
        by_contra hlt
        push_neg at hlt
        rw [← hFΩs] at hw
        exact hw ⟨F.symm (G 0), hlt, F.apply_symm_apply (G 0)⟩
      have := image_closure_subset_closure_image F.continuous (mem_image_of_mem F hp)
      rwa [F.apply_symm_apply, hFΩ] at this
    obtain ⟨U, hUS, hUo, hwU⟩ := _root_.mem_nhds_iff.mp hS
    obtain ⟨w, hwU', hwΩ⟩ := mem_closure_iff.mp hcl U hUo hwU
    have hw0 : w = G 0 := by
      rcases hSsub (hUS hwU') with h | h
      · exact h
      · exact absurd h (Set.disjoint_left.mp hdisj hwΩ)
    rw [hw0] at hwΩ
    have hN : U ∩ Ω ∈ 𝓝 (G 0) := inter_mem (hUo.mem_nhds hwU) (hΩo.mem_nhds hwΩ)
    have hN' : ∀ᶠ v in 𝓝[≠] (G 0), v ∈ U ∩ Ω := nhdsWithin_le_nhds hN
    obtain ⟨v, ⟨hvU, hvΩ⟩, hvne⟩ := (hN'.and self_mem_nhdsWithin).exists
    rcases hSsub (hUS hvU) with h | h
    · exact hvne h
    · exact Set.disjoint_left.mp hdisj hvΩ h

/-- The area theorem for a normalized disjoint pair (TT `IsNormalizedDisjointPair`):
`|g'(∞)| ≥ 1`, and `|g'(∞)| = 1` forces `f = id` on `𝔻` (all `b_{-n,0}` vanish). -/
theorem s02_area_core {f g : ℂ → ℂ} (h : TakhtajanTeo.Ch2.IsNormalizedDisjointPair f g) :
    1 ≤ ‖TakhtajanTeo.derivAtInfty g‖ ∧
      (‖TakhtajanTeo.derivAtInfty g‖ = 1 → ∀ z ∈ unitDisc, f z = z) := by
  have hK := s02_r22_partial_le h
  have hne : TakhtajanTeo.derivAtInfty g ≠ 0 := by
    obtain ⟨hexp, -, -, -, -⟩ := (TakhtajanTeo.Ch2.grunsky_spec h).1
    rw [← hexp]
    exact Complex.exp_ne_zero _
  have hpos : 0 < ‖TakhtajanTeo.derivAtInfty g‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
  refine ⟨?_, fun heq => ?_⟩
  · have hlog0 : 0 ≤ Real.log (‖TakhtajanTeo.derivAtInfty g‖ ^ 2) := by simpa using hK 0
    have h1 := (Real.log_nonneg_iff hpos).mp hlog0
    by_contra hlt
    push_neg at hlt
    nlinarith [norm_nonneg (TakhtajanTeo.derivAtInfty g)]
  · rw [heq, one_pow, Real.log_one] at hK
    have hb : ∀ j : ℕ, TakhtajanTeo.Ch2.grunsky f g (-((j : ℤ) + 1)) 0 = 0 := by
      intro j
      have h2 := hK (j + 1)
      rw [Finset.sum_range_succ] at h2
      have h3 : 0 ≤ ∑ i ∈ Finset.range j,
          (((i + 1 : ℕ) : ℝ) * ‖TakhtajanTeo.Ch2.grunsky f g (-((i : ℤ) + 1)) 0‖ ^ 2 +
            ((i + 1 : ℕ) : ℝ) * ‖TakhtajanTeo.Ch2.grunsky f g ((i : ℤ) + 1) 0‖ ^ 2) :=
        Finset.sum_nonneg (fun i _ => by positivity)
      have h4 : 0 ≤ ((j + 1 : ℕ) : ℝ) * ‖TakhtajanTeo.Ch2.grunsky f g ((j : ℤ) + 1) 0‖ ^ 2 := by
        positivity
      have h6 : ((j + 1 : ℕ) : ℝ) * ‖TakhtajanTeo.Ch2.grunsky f g (-((j : ℤ) + 1)) 0‖ ^ 2 = 0 := by
        have : 0 ≤ ((j + 1 : ℕ) : ℝ) * ‖TakhtajanTeo.Ch2.grunsky f g (-((j : ℤ) + 1)) 0‖ ^ 2 := by
          positivity
        linarith
      have h7 : ‖TakhtajanTeo.Ch2.grunsky f g (-((j : ℤ) + 1)) 0‖ ^ 2 = 0 :=
        (mul_eq_zero.mp h6).resolve_left (by positivity)
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h7)
    obtain ⟨φ, hφs, hφf⟩ := TakhtajanTeo.Ch2.r22_f_series h
    intro z hz
    have hφ0 : φ z = 0 := by
      refine (hφs z hz).unique ?_
      convert hasSum_zero with n
      rcases n with _ | m
      · simp
      · rw [if_neg (Nat.succ_ne_zero m),
          show (-(((m + 1 : ℕ) : ℤ))) = -((m : ℤ) + 1) by push_cast; ring, hb m, neg_zero, zero_mul]
    have h2 := hφf z hz
    rwa [hφ0, Complex.exp_zero, mul_one] at h2

/-- Recentring a Riemann map at `p ∈ 𝔻`: `f ∘ B_{-p}` (`B_{-p}(z) = (z+p)/(1+p̄z)`) is again a
Riemann map, with value `f(p)` and derivative `f'(p)(1-|p|²)` at `0`. -/
theorem s02_disc_recenter {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {p : ℂ}
    (hp : p ∈ unitDisc) :
    IsConformalOnto (f ∘ blaschke (-p)) unitDisc Ω ∧ (f ∘ blaschke (-p)) 0 = f p ∧
      deriv (f ∘ blaschke (-p)) 0 = deriv f p * ((1 - ‖p‖ ^ 2 : ℝ) : ℂ) := by
  have hp1 : ‖-p‖ < 1 := by
    rw [norm_neg]
    exact mem_ball_zero_iff.mp hp
  have hB := isConformalOnto_blaschke hp1
  have hB0 : blaschke (-p) 0 = p := by
    show (0 - -p) / (1 - conj (-p) * 0) = p
    simp
  have hmaps : MapsTo (blaschke (-p)) unitDisc unitDisc := fun z hz =>
    mem_ball_zero_iff.mpr (blaschke_mem_unitDisc hp1 (mem_ball_zero_iff.mp hz))
  refine ⟨⟨hf.1.comp hB.1 hmaps, hf.2.1.comp hB.2.1 hmaps, by rw [image_comp, hB.2.2, hf.2.2]⟩,
    by rw [Function.comp_apply, hB0], ?_⟩
  have hBd := hasDerivAt_blaschke hp1 (show ‖(0 : ℂ)‖ < 1 by simp)
  have hfd : HasDerivAt f (deriv f p) (blaschke (-p) 0) := by
    rw [hB0]
    exact (hf.1.differentiableAt (isOpen_ball.mem_nhds hp)).hasDerivAt
  rw [(hfd.comp 0 hBd).deriv]
  congr 1
  rw [mul_zero, sub_zero, one_pow, div_one, map_neg, neg_mul_neg, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- Möbius normalization of two disjoint Riemann maps `f : 𝔻 → Ω`, `g : 𝔻 → Ω*` into a TT
normalized disjoint pair: with `Δ = f(0) - g(0)` and `B = -Δ²/f'(0)`,
`f₁(z) = B((f(z) - g(0))⁻¹ - Δ⁻¹)` on `𝔻` and `g₁(z) = B((g(1/z) - g(0))⁻¹ - Δ⁻¹)` on `𝔻*`
satisfy `IsNormalizedDisjointPair f₁ g₁`, and `g₁(z)/z → g₁'(∞) = -Δ²/(f'(0) g'(0))`. -/
theorem s02_normalize_pair {Ω Ωs : Set ℂ} (hd : Disjoint Ω Ωs) {f g : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (hg : IsConformalOnto g unitDisc Ωs) :
    TakhtajanTeo.Ch2.IsNormalizedDisjointPair
        (fun z => -(f 0 - g 0) ^ 2 / deriv f 0 * ((f z - g 0)⁻¹ - (f 0 - g 0)⁻¹))
        (fun z => -(f 0 - g 0) ^ 2 / deriv f 0 * ((g z⁻¹ - g 0)⁻¹ - (f 0 - g 0)⁻¹)) ∧
      Tendsto (fun z => -(f 0 - g 0) ^ 2 / deriv f 0 * ((g z⁻¹ - g 0)⁻¹ - (f 0 - g 0)⁻¹) / z)
        (Bornology.cobounded ℂ) (𝓝 (-(f 0 - g 0) ^ 2 / (deriv f 0 * deriv g 0))) ∧
      TakhtajanTeo.derivAtInfty
          (fun z => -(f 0 - g 0) ^ 2 / deriv f 0 * ((g z⁻¹ - g 0)⁻¹ - (f 0 - g 0)⁻¹)) =
        -(f 0 - g 0) ^ 2 / (deriv f 0 * deriv g 0) := by
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hfΩ : ∀ z ∈ unitDisc, f z ∈ Ω := fun z hz => hf.2.2 ▸ mem_image_of_mem f hz
  have hgΩ : ∀ z ∈ unitDisc, g z ∈ Ωs := fun z hz => hg.2.2 ▸ mem_image_of_mem g hz
  have hfg : ∀ z ∈ unitDisc, f z - g 0 ≠ 0 := fun z hz h =>
    Set.disjoint_left.mp hd (hfΩ z hz) (by rw [sub_eq_zero.mp h]; exact hgΩ 0 h0)
  have hΔ : f 0 - g 0 ≠ 0 := hfg 0 h0
  have ha : deriv f 0 ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 h0
  have hb : deriv g 0 ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hg.1 hg.2.1 h0
  obtain ⟨B, hBdef⟩ : ∃ B : ℂ, B = -(f 0 - g 0) ^ 2 / deriv f 0 := ⟨_, rfl⟩
  have hB : B ≠ 0 := by
    rw [hBdef]
    exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hΔ)) ha
  rw [← hBdef]
  have hinvD : ∀ z, z ∈ unitDiscExterior → z⁻¹ ∈ unitDisc ∧ z⁻¹ ≠ 0 := by
    intro z hz
    have hz1 : 1 < ‖z‖ := hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hz1
      linarith
    refine ⟨mem_ball_zero_iff.mpr ?_, inv_ne_zero hz0⟩
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hz1
  have hgz : ∀ z ∈ unitDiscExterior, g z⁻¹ - g 0 ≠ 0 := fun z hz h =>
    (hinvD z hz).2 (hg.2.1 (hinvD z hz).1 h0 (sub_eq_zero.mp h))
  have hlim : Tendsto (fun z => B * ((g z⁻¹ - g 0)⁻¹ - (f 0 - g 0)⁻¹) / z)
      (Bornology.cobounded ℂ) (𝓝 (-(f 0 - g 0) ^ 2 / (deriv f 0 * deriv g 0))) := by
    have hgd : HasDerivAt g (deriv g 0) 0 :=
      (hg.1.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt
    have hs := (hasDerivAt_iff_tendsto_slope.mp hgd).comp tendsto_inv₀_cobounded'
    have hs2 := ((hs.inv₀ hb).sub ((tendsto_inv₀_cobounded (α := ℂ)).mul_const
      (f 0 - g 0)⁻¹)).const_mul B
    have e : -(f 0 - g 0) ^ 2 / (deriv f 0 * deriv g 0) =
        B * ((deriv g 0)⁻¹ - 0 * (f 0 - g 0)⁻¹) := by
      rw [hBdef, zero_mul, sub_zero]
      field_simp
    rw [e]
    refine hs2.congr (fun z => ?_)
    simp only [Function.comp_apply, slope, vsub_eq_sub, smul_eq_mul, sub_zero, inv_inv, mul_inv]
    ring
  have hL0 : -(f 0 - g 0) ^ 2 / (deriv f 0 * deriv g 0) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hΔ)) (mul_ne_zero ha hb)
  refine ⟨⟨?_, ?_, by simp, ?_, ⟨?_, ?_, ?_⟩, ?_⟩, hlim, ?_⟩
  · intro z hz
    exact ((((hf.1 z hz).sub_const (g 0)).inv (hfg z hz)).sub_const _).const_mul B
  · intro x hx y hy hxy
    have h1 := sub_left_inj.mp (mul_left_cancel₀ hB hxy)
    exact hf.2.1 hx hy (sub_left_inj.mp (inv_injective h1))
  · have hfd : HasDerivAt f (deriv f 0) 0 :=
      (hf.1.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt
    have h1 : HasDerivAt (fun z => B * ((f z - g 0)⁻¹ - (f 0 - g 0)⁻¹))
        (B * (-deriv f 0 / (f 0 - g 0) ^ 2)) 0 :=
      (((hfd.sub_const (g 0)).inv (hfg 0 h0)).sub_const (f 0 - g 0)⁻¹).const_mul B
    rw [h1.deriv, hBdef]
    field_simp
  · intro z hz
    have hz0 := (hinvD z hz).2
    have hz0' : z ≠ 0 := fun h => hz0 (by rw [h, inv_zero])
    have hgd : DifferentiableAt ℂ g z⁻¹ :=
      hg.1.differentiableAt (isOpen_ball.mem_nhds (hinvD z hz).1)
    exact ((((hgd.comp z (differentiableAt_inv hz0')).sub_const (g 0)).inv (hgz z hz)).sub_const
      _).const_mul B |>.differentiableWithinAt
  · intro x hx y hy hxy
    have h1 := sub_left_inj.mp (mul_left_cancel₀ hB hxy)
    have h2 := sub_left_inj.mp (inv_injective h1)
    exact inv_injective (hg.2.1 (hinvD x hx).1 (hinvD y hy).1 h2)
  · rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    have h2 := hlim.norm.pos_mul_atTop (norm_pos_iff.mpr hL0) tendsto_norm_cobounded_atTop
    refine h2.congr' ?_
    filter_upwards [eventually_cobounded_le_norm 1] with z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      norm_num at hz
    rw [← norm_mul, div_mul_cancel₀ _ hz0]
  · rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have h1 := sub_left_inj.mp (mul_left_cancel₀ hB hxy)
    have h2 := sub_left_inj.mp (inv_injective h1)
    exact Set.disjoint_left.mp hd (hfΩ x hx) (h2 ▸ hgΩ _ (hinvD y hy).1)
  · show limUnder (cocompact ℂ) (fun z => B * ((g z⁻¹ - g 0)⁻¹ - (f 0 - g 0)⁻¹) / z) = _
    rw [← Metric.cobounded_eq_cocompact]
    exact hlim.limUnder_eq

/-- The two halves `F(ℍ)`, `F(ℍ⁻)` of a Jordan pair through `∞` are disjoint. -/
theorem s02_jordanPair_disjoint {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) : Disjoint Ω Ωs := by
  obtain ⟨F, rfl, rfl⟩ := hΓ
  refine (disjoint_image_iff F.injective).mpr (Set.disjoint_left.mpr fun z hz hz' => ?_)
  have h1 : 0 < z.im := hz
  have h2 : z.im < 0 := hz'
  linarith

/-- A Riemann map `f : 𝔻 → Ω` with `f(0) = w`, for any `w` in the domain of a Jordan pair. -/
theorem s02_riemannMap_at {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) {w : ℂ} (hw : w ∈ Ω) :
    ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω ∧ f 0 = w := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hΓ
  obtain ⟨p, hp, rfl⟩ : w ∈ f '' unitDisc := by rw [hf.2.2]; exact hw
  obtain ⟨h1, h2, -⟩ := s02_disc_recenter hf hp
  exact ⟨_, h1, h2⟩

/-- `Φ_q(f(p)) = (|W - f(p)|² + ξ²)/(D ξ)` with `D = |f'(p)|(1-|p|²) = 2/λ(f(p))`. -/
theorem s02_horoPhi_eq {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {p : ℂ}
    (hp : p ∈ unitDisc) (q : ℂ × ℝ) :
    horoPhi Ω q (f p) = (‖q.1 - f p‖ ^ 2 + q.2 ^ 2) / (‖deriv f p‖ * (1 - ‖p‖ ^ 2) * q.2) := by
  have hl := eq_lambda_f hf hp
  have hp1 : 0 < 1 - ‖p‖ ^ 2 := by
    have := mem_ball_zero_iff.mp hp
    nlinarith [norm_nonneg p]
  have hd : 0 < ‖deriv f p‖ :=
    norm_pos_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hp)
  have hlam : poincareDensity Ω (f p) = 2 / (‖deriv f p‖ * (1 - ‖p‖ ^ 2)) := by
    rw [eq_div_iff (by positivity), ← mul_assoc, hl]
    field_simp
  unfold horoPhi
  rw [hlam, div_mul_eq_mul_div, div_div,
    show ‖deriv f p‖ * (1 - ‖p‖ ^ 2) * (2 * q.2) = 2 * (‖deriv f p‖ * (1 - ‖p‖ ^ 2) * q.2) by ring,
    mul_div_mul_left _ _ two_ne_zero]

/-- Teo's inequality (BBVW Lemma 4.1 at general points): for disjoint `Ω`, `Ω*` with Riemann maps
`f`, `g` of `𝔻`, `|f'(p)|(1-|p|²) · |g'(ζ)|(1-|ζ|²) ≤ |f(p) - g(ζ)|²`. -/
theorem s02_teo_ineq {Ω Ωs : Set ℂ} (hd : Disjoint Ω Ωs) {f g : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (hg : IsConformalOnto g unitDisc Ωs) {p ζ : ℂ}
    (hp : p ∈ unitDisc) (hζ : ζ ∈ unitDisc) :
    ‖deriv f p‖ * (1 - ‖p‖ ^ 2) * (‖deriv g ζ‖ * (1 - ‖ζ‖ ^ 2)) ≤ ‖f p - g ζ‖ ^ 2 := by
  obtain ⟨hF, hF0, hF'⟩ := s02_disc_recenter hf hp
  obtain ⟨hG, hG0, hG'⟩ := s02_disc_recenter hg hζ
  obtain ⟨hN, -, hD⟩ := s02_normalize_pair hd hF hG
  have h1 := (s02_area_core hN).1
  rw [hD, hF0, hG0, hF', hG'] at h1
  have hp1 : 0 < 1 - ‖p‖ ^ 2 := by
    have := mem_ball_zero_iff.mp hp
    nlinarith [norm_nonneg p]
  have hζ1 : 0 < 1 - ‖ζ‖ ^ 2 := by
    have := mem_ball_zero_iff.mp hζ
    nlinarith [norm_nonneg ζ]
  have hfd : 0 < ‖deriv f p‖ :=
    norm_pos_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hp)
  have hgd : 0 < ‖deriv g ζ‖ :=
    norm_pos_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hg.1 hg.2.1 hζ)
  rw [norm_div, norm_neg, norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg hp1.le, Real.norm_of_nonneg hζ1.le,
    le_div_iff₀ (by positivity), one_mul] at h1
  exact h1

/-- Two open Euclidean balls of `ℍ³` tangent to `ℂ` at `w₁`, `w₂`, of diameters `D₁`, `D₂`, are
disjoint once `D₁ D₂ ≤ |w₁ - w₂|²` (Cauchy–Schwarz on the two chords at a common height). -/
theorem s02_open_horo_disjoint {w₁ w₂ : ℂ} {D₁ D₂ : ℝ} (hle : D₁ * D₂ ≤ ‖w₁ - w₂‖ ^ 2)
    {q : ℂ × ℝ} (hq : 0 < q.2) (h1 : ‖q.1 - w₁‖ ^ 2 + q.2 ^ 2 < D₁ * q.2)
    (h2 : ‖q.1 - w₂‖ ^ 2 + q.2 ^ 2 < D₂ * q.2) : False := by
  have h5 : ‖w₁ - w₂‖ ≤ ‖q.1 - w₁‖ + ‖q.1 - w₂‖ := by
    calc ‖w₁ - w₂‖ = ‖(q.1 - w₂) - (q.1 - w₁)‖ := by ring_nf
      _ ≤ ‖q.1 - w₂‖ + ‖q.1 - w₁‖ := norm_sub_le _ _
      _ = ‖q.1 - w₁‖ + ‖q.1 - w₂‖ := add_comm _ _
  have hs0 := norm_nonneg (q.1 - w₁)
  have ht0 := norm_nonneg (q.1 - w₂)
  generalize ‖q.1 - w₁‖ = s at h1 h5 hs0
  generalize ‖q.1 - w₂‖ = t at h2 h5 ht0
  generalize q.2 = ξ at hq h1 h2
  have hx : 0 < D₁ - ξ := by nlinarith [sq_nonneg s]
  have hy : 0 < D₂ - ξ := by nlinarith [sq_nonneg t]
  have hA : s ^ 2 < ξ * (D₁ - ξ) := by nlinarith
  have hC : t ^ 2 < ξ * (D₂ - ξ) := by nlinarith
  have h3 : (s * t) ^ 2 < ξ ^ 2 * ((D₁ - ξ) * (D₂ - ξ)) :=
    calc (s * t) ^ 2 = s ^ 2 * t ^ 2 := by ring
      _ ≤ s ^ 2 * (ξ * (D₂ - ξ)) := mul_le_mul_of_nonneg_left hC.le (sq_nonneg s)
      _ < ξ * (D₁ - ξ) * (ξ * (D₂ - ξ)) := mul_lt_mul_of_pos_right hA (by positivity)
      _ = ξ ^ 2 * ((D₁ - ξ) * (D₂ - ξ)) := by ring
  have hP : 0 ≤ (D₁ - ξ) * (D₂ - ξ) := by positivity
  have h4 : 2 * (s * t) ≤ (D₁ - ξ) * (D₂ - ξ) + ξ ^ 2 := by
    by_contra hcon
    push_neg at hcon
    have h7 := mul_pos (sub_pos.mpr hcon)
      (show 0 < 2 * (s * t) + ((D₁ - ξ) * (D₂ - ξ) + ξ ^ 2) by nlinarith)
    nlinarith [sq_nonneg ((D₁ - ξ) * (D₂ - ξ) - ξ ^ 2)]
  have h6 : ‖w₁ - w₂‖ ^ 2 ≤ (s + t) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h5 2
  nlinarith

/-- The hyperbolic distance between the closed horoballs of `ℍ³` tangent at `w₁`, `w₂` with
Euclidean diameters `D₁`, `D₂` (when `D₁ D₂ ≤ |w₁ - w₂|²`) is `log(|w₁ - w₂|²/(D₁ D₂))`. -/
theorem s02_hdist_horoballs {w₁ w₂ : ℂ} {D₁ D₂ : ℝ} (hD₁ : 0 < D₁) (hD₂ : 0 < D₂)
    (hle : D₁ * D₂ ≤ ‖w₁ - w₂‖ ^ 2) :
    hdistSets {q : ℂ × ℝ | q ∈ UHS ∧ ‖q.1 - w₁‖ ^ 2 + q.2 ^ 2 ≤ D₁ * q.2}
        {q : ℂ × ℝ | q ∈ UHS ∧ ‖q.1 - w₂‖ ^ 2 + q.2 ^ 2 ≤ D₂ * q.2} =
      Real.log (‖w₁ - w₂‖ ^ 2 / (D₁ * D₂)) := by
  obtain ⟨d, hd⟩ : ∃ d : ℂ, d = w₁ - w₂ := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ‖w₁ - w₂‖ := ⟨_, rfl⟩
  have hdδ : ‖d‖ = δ := by rw [hd, hδ]
  have hδab : ∀ z : ℂ, δ ≤ ‖z - w₁‖ + ‖z - w₂‖ := by
    intro z
    rw [hδ]
    calc ‖w₁ - w₂‖ = ‖(z - w₂) - (z - w₁)‖ := by ring_nf
      _ ≤ ‖z - w₂‖ + ‖z - w₁‖ := norm_sub_le _ _
      _ = ‖z - w₁‖ + ‖z - w₂‖ := add_comm _ _
  rw [← hδ]
  rw [← hδ] at hle
  have hδ0 : 0 ≤ δ := hδ ▸ norm_nonneg _
  have hDD : 0 < D₁ * D₂ := mul_pos hD₁ hD₂
  have hδp : 0 < δ := lt_of_le_of_ne hδ0 (fun h => by rw [← h] at hle; nlinarith)
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = δ ^ 2 / (D₁ * D₂) := ⟨_, rfl⟩
  rw [← hR]
  have hR0 : 0 < R := by rw [hR]; positivity
  have hR1 : 1 ≤ R := by rw [hR, one_le_div hDD]; exact hle
  have hL0 : 0 ≤ Real.log R := Real.log_nonneg hR1
  have hcL : Real.cosh (Real.log R) = (R + R⁻¹) / 2 := Real.cosh_log hR0
  have hconv : ∀ q q' : ℂ × ℝ, (R + R⁻¹) / 2 ≤ coshDist q q' → Real.log R ≤ hdist q q' := by
    intro q q' h
    unfold hdist
    rw [← Real.arcosh_cosh hL0, hcL]
    exact (Real.arcosh_le_arcosh (by positivity) (lt_of_lt_of_le (by positivity) h)).2 h
  have key : ∀ u v : ℂ × ℝ, 0 < u.2 → 0 < v.2 → R * u.2 ≤ v.2 →
      (R + R⁻¹) / 2 ≤ coshDist u v := by
    intro u v hu hv huv
    unfold coshDist
    have hA : (R + R⁻¹) / 2 ≤ 1 + (u.2 - v.2) ^ 2 / (2 * u.2 * v.2) := by
      rw [show 1 + (u.2 - v.2) ^ 2 / (2 * u.2 * v.2) = (u.2 ^ 2 + v.2 ^ 2) / (2 * u.2 * v.2) by
          field_simp; ring,
        show (R + R⁻¹) / 2 = (R ^ 2 + 1) / (2 * R) by field_simp,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : 0 ≤ (v.2 - R * u.2) * (R * v.2 - u.2) :=
        mul_nonneg (by linarith) (by nlinarith)
      nlinarith [h1]
    have hB : (u.2 - v.2) ^ 2 / (2 * u.2 * v.2) ≤
        (‖u.1 - v.1‖ ^ 2 + (u.2 - v.2) ^ 2) / (2 * u.2 * v.2) :=
      div_le_div_of_nonneg_right (by nlinarith [sq_nonneg ‖u.1 - v.1‖]) (by positivity)
    linarith
  unfold hdistSets
  refine IsLeast.csInf_eq ⟨?_, ?_⟩
  · obtain ⟨M, hM⟩ : ∃ M : ℝ, M = δ ^ 2 + D₁ ^ 2 := ⟨_, rfl⟩
    obtain ⟨N, hN⟩ : ∃ N : ℝ, N = δ ^ 2 + D₂ ^ 2 := ⟨_, rfl⟩
    have hM0 : 0 < M := by rw [hM]; positivity
    have hN0 : 0 < N := by rw [hN]; positivity
    have hnd : ∀ r : ℝ, ‖d * (r : ℂ)‖ ^ 2 = δ ^ 2 * r ^ 2 := by
      intro r
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, hdδ]
    refine ⟨(w₂ + d * ((δ ^ 2 / M : ℝ) : ℂ), D₁ * δ ^ 2 / M), ⟨?_, ?_⟩,
      (w₂ + d * ((D₂ ^ 2 / N : ℝ) : ℂ), D₂ * δ ^ 2 / N), ⟨?_, ?_⟩, ?_⟩
    · show 0 < D₁ * δ ^ 2 / M
      positivity
    · show ‖w₂ + d * ((δ ^ 2 / M : ℝ) : ℂ) - w₁‖ ^ 2 + (D₁ * δ ^ 2 / M) ^ 2 ≤
        D₁ * (D₁ * δ ^ 2 / M)
      rw [show w₂ + d * ((δ ^ 2 / M : ℝ) : ℂ) - w₁ = d * ((δ ^ 2 / M - 1 : ℝ) : ℂ) by
        rw [hd]; push_cast; ring, hnd]
      refine le_of_eq ?_
      rw [hM]
      field_simp
      ring
    · show 0 < D₂ * δ ^ 2 / N
      positivity
    · show ‖w₂ + d * ((D₂ ^ 2 / N : ℝ) : ℂ) - w₂‖ ^ 2 + (D₂ * δ ^ 2 / N) ^ 2 ≤
        D₂ * (D₂ * δ ^ 2 / N)
      rw [show w₂ + d * ((D₂ ^ 2 / N : ℝ) : ℂ) - w₂ = d * ((D₂ ^ 2 / N : ℝ) : ℂ) by ring, hnd]
      refine le_of_eq ?_
      rw [hN]
      field_simp
      ring
    · have hc : coshDist (w₂ + d * ((δ ^ 2 / M : ℝ) : ℂ), D₁ * δ ^ 2 / M)
          (w₂ + d * ((D₂ ^ 2 / N : ℝ) : ℂ), D₂ * δ ^ 2 / N) = (R + R⁻¹) / 2 := by
        unfold coshDist
        dsimp only
        rw [show w₂ + d * ((δ ^ 2 / M : ℝ) : ℂ) - (w₂ + d * ((D₂ ^ 2 / N : ℝ) : ℂ)) =
          d * ((δ ^ 2 / M - D₂ ^ 2 / N : ℝ) : ℂ) by push_cast; ring, hnd, hR, hM, hN]
        field_simp
        ring
      show Real.arcosh (coshDist _ _) = Real.log R
      rw [hc, ← hcL, Real.arcosh_cosh hL0]
  · rintro _ ⟨q₁, ⟨hq₁, hB₁⟩, q₂, ⟨hq₂, hB₂⟩, rfl⟩
    apply hconv
    have hq1 : 0 < q₁.2 := hq₁
    have hq2 : 0 < q₂.2 := hq₂
    rw [← s02_coshDist_invExt w₂ hq1 hq2]
    have hx : (invExt w₂ q₁).2 = q₁.2 / (‖q₁.1 - w₂‖ ^ 2 + q₁.2 ^ 2) := rfl
    have hy : (invExt w₂ q₂).2 = q₂.2 / (‖q₂.1 - w₂‖ ^ 2 + q₂.2 ^ 2) := rfl
    have hxle : (invExt w₂ q₁).2 ≤ D₁ / δ ^ 2 := by
      rw [hx, div_le_div_iff₀ (by positivity) (by positivity)]
      have hab := hδab q₁.1
      have ha0 := norm_nonneg (q₁.1 - w₁)
      have hb0 := norm_nonneg (q₁.1 - w₂)
      generalize ‖q₁.1 - w₁‖ = a at hab ha0 hB₁
      generalize ‖q₁.1 - w₂‖ = b at hab hb0 ⊢
      generalize q₁.2 = ξ at hq1 hB₁ ⊢
      have h1 : δ ^ 2 ≤ (a + b) ^ 2 := pow_le_pow_left₀ hδ0 hab 2
      have h2 : ξ ^ 2 * (a + b) ^ 2 ≤ (a ^ 2 + ξ ^ 2) * (b ^ 2 + ξ ^ 2) := by
        nlinarith [sq_nonneg (a * b - ξ ^ 2)]
      have h3 : (a ^ 2 + ξ ^ 2) * (b ^ 2 + ξ ^ 2) ≤ D₁ * ξ * (b ^ 2 + ξ ^ 2) :=
        mul_le_mul_of_nonneg_right hB₁ (by positivity)
      have h4 : ξ * (ξ * δ ^ 2) ≤ ξ * (D₁ * (b ^ 2 + ξ ^ 2)) := by
        nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg ξ)]
      exact le_of_mul_le_mul_left h4 hq1
    have hyge : 1 / D₂ ≤ (invExt w₂ q₂).2 := by
      rw [hy, div_le_div_iff₀ hD₂ (by positivity)]
      linarith
    have hxpos : 0 < (invExt w₂ q₁).2 := by rw [hx]; positivity
    have hypos : 0 < (invExt w₂ q₂).2 := by rw [hy]; positivity
    refine key _ _ hxpos hypos ?_
    calc R * (invExt w₂ q₁).2 ≤ R * (D₁ / δ ^ 2) := mul_le_mul_of_nonneg_left hxle hR0.le
      _ = 1 / D₂ := by rw [hR]; field_simp
      _ ≤ _ := hyge

/-- The closed horoball at `f(p)` is the closed tangent ball of Euclidean diameter
`|f'(p)|(1-|p|²)` (`s02_horoPhi_eq`). -/
theorem s02_horoball_eq {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {p : ℂ}
    (hp : p ∈ unitDisc) :
    horoball Ω (f p) =
      {q | q ∈ UHS ∧ ‖q.1 - f p‖ ^ 2 + q.2 ^ 2 ≤ ‖deriv f p‖ * (1 - ‖p‖ ^ 2) * q.2} := by
  have hp1 : 0 < 1 - ‖p‖ ^ 2 := by
    have := mem_ball_zero_iff.mp hp
    nlinarith [norm_nonneg p]
  have hD₁ : 0 < ‖deriv f p‖ * (1 - ‖p‖ ^ 2) :=
    mul_pos (norm_pos_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hp)) hp1
  ext q
  constructor
  · rintro ⟨hq, h⟩
    refine ⟨hq, ?_⟩
    rwa [s02_horoPhi_eq hf hp, div_le_one (mul_pos hD₁ hq)] at h
  · rintro ⟨hq, h⟩
    refine ⟨hq, ?_⟩
    rwa [s02_horoPhi_eq hf hp, div_le_one (mul_pos hD₁ hq)]

/-- Closed tangent balls of `ℍ³` with `D₁ D₂ < |w₁ - w₂|²` are disjoint. -/
theorem s02_closed_horo_disjoint {w₁ w₂ : ℂ} {D₁ D₂ : ℝ} (hlt : D₁ * D₂ < ‖w₁ - w₂‖ ^ 2)
    {q : ℂ × ℝ} (hq : 0 < q.2) (h1 : ‖q.1 - w₁‖ ^ 2 + q.2 ^ 2 ≤ D₁ * q.2)
    (h2 : ‖q.1 - w₂‖ ^ 2 + q.2 ^ 2 ≤ D₂ * q.2) : False := by
  have h5 : ‖w₁ - w₂‖ ≤ ‖q.1 - w₁‖ + ‖q.1 - w₂‖ := by
    calc ‖w₁ - w₂‖ = ‖(q.1 - w₂) - (q.1 - w₁)‖ := by ring_nf
      _ ≤ ‖q.1 - w₂‖ + ‖q.1 - w₁‖ := norm_sub_le _ _
      _ = ‖q.1 - w₁‖ + ‖q.1 - w₂‖ := add_comm _ _
  have hs0 := norm_nonneg (q.1 - w₁)
  have ht0 := norm_nonneg (q.1 - w₂)
  generalize ‖q.1 - w₁‖ = s at h1 h5 hs0
  generalize ‖q.1 - w₂‖ = t at h2 h5 ht0
  generalize q.2 = ξ at hq h1 h2
  have hx : 0 ≤ D₁ - ξ := by nlinarith [sq_nonneg s]
  have hy : 0 ≤ D₂ - ξ := by nlinarith [sq_nonneg t]
  have hA : s ^ 2 ≤ ξ * (D₁ - ξ) := by nlinarith
  have hC : t ^ 2 ≤ ξ * (D₂ - ξ) := by nlinarith
  have h3 : (s * t) ^ 2 ≤ ξ ^ 2 * ((D₁ - ξ) * (D₂ - ξ)) :=
    calc (s * t) ^ 2 = s ^ 2 * t ^ 2 := by ring
      _ ≤ s ^ 2 * (ξ * (D₂ - ξ)) := mul_le_mul_of_nonneg_left hC (sq_nonneg s)
      _ ≤ ξ * (D₁ - ξ) * (ξ * (D₂ - ξ)) := mul_le_mul_of_nonneg_right hA (by positivity)
      _ = ξ ^ 2 * ((D₁ - ξ) * (D₂ - ξ)) := by ring
  have hP : 0 ≤ (D₁ - ξ) * (D₂ - ξ) := by positivity
  have h4 : 2 * (s * t) ≤ (D₁ - ξ) * (D₂ - ξ) + ξ ^ 2 := by
    by_contra hcon
    push_neg at hcon
    have h7 := mul_pos (sub_pos.mpr hcon)
      (show 0 < 2 * (s * t) + ((D₁ - ξ) * (D₂ - ξ) + ξ ^ 2) by nlinarith)
    nlinarith [sq_nonneg ((D₁ - ξ) * (D₂ - ξ) - ξ ^ 2)]
  have h6 : ‖w₁ - w₂‖ ^ 2 ≤ (s + t) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h5 2
  nlinarith

/-- The image of an unbounded set under a homeomorphism of `ℂ` is unbounded. -/
theorem s02_image_unbounded (F : ℂ ≃ₜ ℂ) {S : Set ℂ} (hS : ∀ C : ℝ, ∃ z ∈ S, C < ‖z‖)
    (x : ℂ) (R : ℝ) : ∃ w ∈ F '' S, R < ‖w - x‖ := by
  by_contra hcon
  push_neg at hcon
  have hK : IsCompact (F.symm '' closedBall x R) :=
    (isCompact_closedBall x R).image F.symm.continuous
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  obtain ⟨z, hz, hzC⟩ := hS C
  have hmem : z ∈ F.symm '' closedBall x R := by
    refine ⟨F z, ?_, F.symm_apply_apply z⟩
    rw [mem_closedBall, dist_eq_norm]
    exact hcon _ (mem_image_of_mem F hz)
  linarith [hC z hmem]

/-- Both domains of a Jordan pair through `∞` are unbounded. -/
theorem s02_jordanPair_unbounded {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) :
    (∀ (x : ℂ) (R : ℝ), ∃ w ∈ Ω, R < ‖w - x‖) ∧ (∀ (x : ℂ) (R : ℝ), ∃ w ∈ Ωs, R < ‖w - x‖) := by
  obtain ⟨F, rfl, rfl⟩ := hΓ
  have hn : ∀ C : ℝ, C < ‖((|C| + 1 : ℝ) : ℂ) * I‖ := by
    intro C
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith [le_abs_self C]
  refine ⟨s02_image_unbounded F (fun C => ⟨((|C| + 1 : ℝ) : ℂ) * I, ?_, hn C⟩),
    s02_image_unbounded F (fun C => ⟨-(((|C| + 1 : ℝ) : ℂ) * I), ?_, by rw [norm_neg]; exact hn C⟩)⟩
  · show 0 < (((|C| + 1 : ℝ) : ℂ) * I).im
    rw [Complex.mul_I_im, Complex.ofReal_re]
    positivity
  · show (-(((|C| + 1 : ℝ) : ℂ) * I)).im < 0
    rw [Complex.neg_im, Complex.mul_I_im, Complex.ofReal_re]
    linarith [abs_nonneg C]

/-- A point of `Γ = (Ω ∪ Ω*)ᶜ` of a Jordan pair lies in `closure Ω`. -/
theorem s02_jordanPair_closure {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) {w : ℂ} (h1 : w ∉ Ω)
    (h2 : w ∉ Ωs) : w ∈ closure Ω := by
  obtain ⟨F, hFΩ, hFΩs⟩ := hΓ
  have hx : (F.symm w).im = 0 := by
    rcases lt_trichotomy (F.symm w).im 0 with h | h | h
    · exact absurd (hFΩs ▸ ⟨F.symm w, h, F.apply_symm_apply w⟩) h2
    · exact h
    · exact absurd (hFΩ ▸ ⟨F.symm w, h, F.apply_symm_apply w⟩) h1
  have hxc : F.symm w ∈ closure upperHalf := by
    refine Metric.mem_closure_iff.mpr fun ε hε => ⟨F.symm w + ((ε / 2 : ℝ) : ℂ) * I, ?_, ?_⟩
    · show 0 < (F.symm w + ((ε / 2 : ℝ) : ℂ) * I).im
      rw [Complex.add_im, Complex.mul_I_im, Complex.ofReal_re, hx]
      linarith
    · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
  have := image_closure_subset_closure_image F.continuous (mem_image_of_mem F hxc)
  rwa [F.apply_symm_apply, hFΩ] at this

/-- Equality in Teo's inequality forces a circle: if `|f'(0)| |g'(0)| = |f(0) - g(0)|²` for Riemann
maps of the two halves of a Jordan pair, then `Ω`, `Ω*` are complementary half-planes. -/
theorem s02_teo_eq_line {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) {f g : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (hg : IsConformalOnto g unitDisc Ωs)
    (heq : ‖deriv f 0‖ * ‖deriv g 0‖ = ‖f 0 - g 0‖ ^ 2) : IsLinePair Ω Ωs := by
  have hd := s02_jordanPair_disjoint hΓ
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  obtain ⟨hN, -, hD⟩ := s02_normalize_pair hd hf hg
  have hfΩ : ∀ z ∈ unitDisc, f z ∈ Ω := fun z hz => hf.2.2 ▸ mem_image_of_mem f hz
  have hgΩ : g 0 ∈ Ωs := hg.2.2 ▸ mem_image_of_mem g h0
  have hΔ : f 0 - g 0 ≠ 0 := fun h =>
    Set.disjoint_left.mp hd (hfΩ 0 h0) (by rw [sub_eq_zero.mp h]; exact hgΩ)
  have ha : deriv f 0 ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 h0
  have hnorm : ‖-(f 0 - g 0) ^ 2 / (deriv f 0 * deriv g 0)‖ = 1 := by
    rw [norm_div, norm_neg, norm_pow, norm_mul, heq,
      div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hΔ))]
  have hid := (s02_area_core hN).2 (by rw [hD]; exact hnorm)
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : ℂ, w₀ = g 0 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (f 0 - g 0)⁻¹ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℂ, B = -(f 0 - g 0) ^ 2 / deriv f 0 := ⟨_, rfl⟩
  have hB0 : B ≠ 0 := by
    rw [hB]
    exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hΔ)) ha
  have hc0 : c ≠ 0 := by rw [hc]; exact inv_ne_zero hΔ
  have hid' : ∀ z ∈ unitDisc, B * ((f z - w₀)⁻¹ - c) = z := by
    intro z hz
    rw [hB, hw₀, hc]
    exact hid z hz
  have hchar : ∀ w, w ∈ Ω ↔ w ≠ w₀ ∧ ‖(w - w₀)⁻¹ - c‖ < ‖B‖⁻¹ := by
    intro w
    constructor
    · intro hw
      obtain ⟨z, hz, rfl⟩ : w ∈ f '' unitDisc := by rw [hf.2.2]; exact hw
      refine ⟨fun h => Set.disjoint_left.mp hd hw (by rw [h, hw₀]; exact hgΩ), ?_⟩
      have e : (f z - w₀)⁻¹ - c = B⁻¹ * z :=
        calc (f z - w₀)⁻¹ - c = B⁻¹ * (B * ((f z - w₀)⁻¹ - c)) := by
              rw [← mul_assoc, inv_mul_cancel₀ hB0, one_mul]
          _ = B⁻¹ * z := by rw [hid' z hz]
      rw [e, norm_mul, norm_inv]
      exact mul_lt_of_lt_one_right (inv_pos.mpr (norm_pos_iff.mpr hB0)) (mem_ball_zero_iff.mp hz)
    · rintro ⟨hne, hlt⟩
      have hz : B * ((w - w₀)⁻¹ - c) ∈ unitDisc := by
        refine mem_ball_zero_iff.mpr ?_
        rw [norm_mul]
        calc ‖B‖ * ‖(w - w₀)⁻¹ - c‖ < ‖B‖ * ‖B‖⁻¹ :=
              mul_lt_mul_of_pos_left hlt (norm_pos_iff.mpr hB0)
          _ = 1 := mul_inv_cancel₀ (norm_ne_zero_iff.mpr hB0)
      have h1 := hid' _ hz
      have h2 := sub_left_inj.mp (mul_left_cancel₀ hB0 h1)
      have h3 := sub_left_inj.mp (inv_injective h2)
      rw [← hf.2.2]
      exact ⟨_, hz, h3⟩
  have hU := s02_jordanPair_unbounded hΓ
  have hr : ‖B‖⁻¹ = ‖c‖ := by
    rcases lt_trichotomy ‖B‖⁻¹ ‖c‖ with h | h | h
    · exfalso
      obtain ⟨w, hw, hR⟩ := hU.1 w₀ (‖c‖ - ‖B‖⁻¹)⁻¹
      obtain ⟨hne, hlt⟩ := (hchar w).mp hw
      have h1 : ‖c‖ - ‖B‖⁻¹ < ‖(w - w₀)⁻¹‖ := by
        have := norm_sub_norm_le c (w - w₀)⁻¹
        rw [norm_sub_rev] at this
        linarith
      rw [norm_inv] at h1
      have hvpos : 0 < ‖w - w₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      have := (lt_inv_comm₀ (sub_pos.mpr h) hvpos).mp h1
      linarith
    · exact h
    · exfalso
      obtain ⟨w, hw, hR⟩ := hU.2 w₀ (‖B‖⁻¹ - ‖c‖)⁻¹
      have hvpos : 0 < ‖w - w₀‖ := lt_trans (inv_pos.mpr (sub_pos.mpr h)) hR
      have h1 : ‖(w - w₀)⁻¹‖ < ‖B‖⁻¹ - ‖c‖ := by
        rw [norm_inv]
        exact (inv_lt_comm₀ hvpos (sub_pos.mpr h)).mpr hR
      have hw' : w ∈ Ω := (hchar w).mpr ⟨sub_ne_zero.mp (norm_pos_iff.mp hvpos),
        lt_of_le_of_lt (norm_sub_le _ _) (by linarith)⟩
      exact Set.disjoint_left.mp hd hw' hw
  have hhalf : ∀ w, w ∈ Ω ↔ 1 / 2 < (c * (w - w₀)).re := by
    intro w
    rw [hchar w, hr]
    have key : ∀ v : ℂ, v ≠ 0 → (‖v⁻¹ - c‖ < ‖c‖ ↔ 1 / 2 < (c * v).re) := by
      intro v hv
      have e : v⁻¹ - c = v⁻¹ * (1 - c * v) := by
        rw [mul_sub, mul_one, ← mul_assoc, mul_comm v⁻¹ c, mul_assoc, inv_mul_cancel₀ hv,
          mul_one]
      have hsq : ‖1 - c * v‖ ^ 2 = 1 + ‖c * v‖ ^ 2 - 2 * (c * v).re := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_one, one_mul,
          Complex.conj_re]
      rw [e, norm_mul, norm_inv, inv_mul_lt_iff₀ (norm_pos_iff.mpr hv),
        show ‖v‖ * ‖c‖ = ‖c * v‖ by rw [norm_mul, mul_comm]]
      constructor
      · intro hlt
        have := pow_lt_pow_left₀ hlt (norm_nonneg _) two_ne_zero
        linarith
      · intro hre
        refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
        linarith
    constructor
    · rintro ⟨hne, hlt⟩
      exact (key _ (sub_ne_zero.mpr hne)).mp hlt
    · intro hre
      have hne : w ≠ w₀ := by
        rintro rfl
        rw [sub_self, mul_zero, Complex.zero_re] at hre
        linarith
      exact ⟨hne, (key _ (sub_ne_zero.mpr hne)).mpr hre⟩
  have hlin : ∀ w : ℂ, (I * c * w + (-(I * c * w₀) - I * ((1 / 2 : ℝ) : ℂ))).im =
      (c * (w - w₀)).re - 1 / 2 := by
    intro w
    rw [show I * c * w + (-(I * c * w₀) - I * ((1 / 2 : ℝ) : ℂ)) =
      I * (c * (w - w₀) - ((1 / 2 : ℝ) : ℂ)) by ring, Complex.I_mul_im, Complex.sub_re,
      Complex.ofReal_re]
  have hΩso : IsOpen Ωs := by
    obtain ⟨F, -, hFΩs⟩ := hΓ
    rw [← hFΩs]
    exact F.isOpenMap _ (isOpen_lt Complex.continuous_im continuous_const)
  refine ⟨I * c, -(I * c * w₀) - I * ((1 / 2 : ℝ) : ℂ), mul_ne_zero I_ne_zero hc0, ?_, ?_⟩
  · ext w
    rw [hhalf w, mem_setOf_eq, hlin]
    constructor <;> intro h <;> linarith
  · ext w
    show w ∈ Ωs ↔ (I * c * w + (-(I * c * w₀) - I * ((1 / 2 : ℝ) : ℂ))).im < 0
    rw [hlin]
    constructor
    · intro hw
      by_contra hge
      push_neg at hge
      obtain ⟨ε, hε, hεb⟩ := Metric.isOpen_iff.mp hΩso w hw
      have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
      have hw' : w + ((ε * ‖c‖ / 2 : ℝ) : ℂ) * c⁻¹ ∈ Ωs := by
        refine hεb ?_
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by positivity), norm_inv]
        rw [show ε * ‖c‖ / 2 * ‖c‖⁻¹ = ε / 2 by field_simp]
        linarith
      have hwΩ : w + ((ε * ‖c‖ / 2 : ℝ) : ℂ) * c⁻¹ ∈ Ω := by
        rw [hhalf]
        rw [show c * (w + ((ε * ‖c‖ / 2 : ℝ) : ℂ) * c⁻¹ - w₀) =
          c * (w - w₀) + ((ε * ‖c‖ / 2 : ℝ) : ℂ) by field_simp; ring, Complex.add_re,
          Complex.ofReal_re]
        have : 0 < ε * ‖c‖ / 2 := by positivity
        linarith
      exact Set.disjoint_left.mp hd hwΩ hw'
    · intro hlt
      by_contra hw
      have hwΩ : w ∉ Ω := by
        rw [hhalf]
        linarith
      have hcl := s02_jordanPair_closure hΓ hwΩ hw
      have hsub : closure Ω ⊆ {w | 1 / 2 ≤ (c * (w - w₀)).re} :=
        closure_minimal (fun x hx => le_of_lt ((hhalf x).mp hx))
          (isClosed_le continuous_const (by fun_prop))
      have := hsub hcl
      simp only [mem_setOf_eq] at this
      linarith

/-- A Jordan pair through `∞` is symmetric: `(Ω*, Ω)` is one too (precompose with `z ↦ z̄`). -/
theorem s02_jordanPair_symm {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) : IsJordanPair Ωs Ω := by
  obtain ⟨F, h1, h2⟩ := hΓ
  refine ⟨Complex.conjCLE.toHomeomorph.trans F, ?_, ?_⟩
  · rw [← h2]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨conj x, ?_, rfl⟩
      have hx' : 0 < x.im := hx
      show (conj x).im < 0
      rw [Complex.conj_im]
      linarith
    · rintro ⟨y, hy, rfl⟩
      refine ⟨conj y, ?_, ?_⟩
      · have hy' : y.im < 0 := hy
        show 0 < (conj y).im
        rw [Complex.conj_im]
        linarith
      · show F (conj (conj y)) = F y
        rw [Complex.conj_conj]
  · rw [← h1]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨conj x, ?_, rfl⟩
      have hx' : x.im < 0 := hx
      show 0 < (conj x).im
      rw [Complex.conj_im]
      linarith
    · rintro ⟨y, hy, rfl⟩
      refine ⟨conj y, ?_, ?_⟩
      · have hy' : 0 < y.im := hy
        show (conj y).im < 0
        rw [Complex.conj_im]
        linarith
      · show F (conj (conj y)) = F y
        rw [Complex.conj_conj]

/-- For `g : 𝔻* → Ω*` conformal with `g(z)/z → c` and `x₀ ∉ Ω*`, the map
`ψ(ζ) = 1/(g(1/ζ) - x₀)` (`ψ(0) = 0`) is a Riemann map of `invPairΩs Ωs x₀` with `ψ'(0) = 1/c`. -/
theorem s02_invPair_riemannMap {Ω Ωs : Set ℂ}
    (hΓ : ∃ F : ℂ ≃ₜ ℂ, F '' unitDisc = Ω ∧ F '' unitDiscExterior = Ωs) {g : ℂ → ℂ}
    (hg : IsConformalOnto g unitDiscExterior Ωs) {c : ℂ}
    (hc : Tendsto (fun z => g z / z) (Bornology.cobounded ℂ) (𝓝 c)) {x₀ : ℂ} (hx₀ : x₀ ∉ Ωs) :
    ∃ ψ : ℂ → ℂ, IsConformalOnto ψ unitDisc (invPairΩs Ωs x₀) ∧ ψ 0 = 0 ∧ deriv ψ 0 = c⁻¹ := by
  have hc0 := s02_ext_coeff_ne_zero hΓ hg hc
  have hextO : IsOpen unitDiscExterior := isOpen_lt continuous_const continuous_norm
  have hext : ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ < 1 → ζ⁻¹ ∈ unitDiscExterior := by
    intro ζ h0 h1
    show 1 < ‖ζ⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr h0)).mpr h1
  have hgx : ∀ z ∈ unitDiscExterior, g z - x₀ ≠ 0 := by
    intro z hz h
    apply hx₀
    rw [← hg.2.2]
    exact ⟨z, hz, sub_eq_zero.mp h⟩
  obtain ⟨K, hK⟩ : ∃ K : ℂ → ℂ, K = Function.update (fun ζ => ζ * (g ζ⁻¹ - x₀)) 0 c :=
    ⟨_, rfl⟩
  have hKe : ∀ ζ : ℂ, ζ ≠ 0 → K ζ = ζ * (g ζ⁻¹ - x₀) := by
    intro ζ hζ
    rw [hK, Function.update_of_ne hζ]
  have hK0 : K 0 = c := by rw [hK, Function.update_self]
  have hKlim : Tendsto K (𝓝[≠] 0) (𝓝 c) := by
    have h1 := hc.comp tendsto_inv₀_nhdsNE_zero
    have h2 : Tendsto (fun ζ : ℂ => ζ * x₀) (𝓝[≠] 0) (𝓝 0) := by
      have h3 : Tendsto (fun ζ : ℂ => ζ * x₀) (𝓝 0) (𝓝 (0 * x₀)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at h3
      exact h3.mono_left nhdsWithin_le_nhds
    have h4 := h1.sub h2
    rw [sub_zero] at h4
    refine h4.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ζ hζ
    show g ζ⁻¹ / ζ⁻¹ - ζ * x₀ = K ζ
    rw [hKe ζ hζ, div_inv_eq_mul]
    ring
  have hKd : DifferentiableOn ℂ K (ball 0 1) := by
    refine (differentiableOn_compl_singleton_and_continuousAt_iff (ball_mem_nhds 0 one_pos)).mp
      ⟨?_, ?_⟩
    · intro ζ hζ
      have hζ0 : ζ ≠ 0 := hζ.2
      have hz := hext ζ hζ0 (mem_ball_zero_iff.mp hζ.1)
      have hgd : DifferentiableAt ℂ g ζ⁻¹ := hg.1.differentiableAt (hextO.mem_nhds hz)
      have hd : DifferentiableAt ℂ (fun ζ => ζ * (g ζ⁻¹ - x₀)) ζ :=
        differentiableAt_id.mul ((hgd.comp ζ (differentiableAt_inv hζ0)).sub_const x₀)
      have heq : K =ᶠ[𝓝 ζ] fun ζ => ζ * (g ζ⁻¹ - x₀) := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hζ0] with w hw
        exact hKe w hw
      exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt
    · rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hK0]
      exact hKlim
  have hKne : ∀ ζ ∈ ball (0 : ℂ) 1, K ζ ≠ 0 := by
    intro ζ hζ
    by_cases hζ0 : ζ = 0
    · rw [hζ0, hK0]
      exact hc0
    · rw [hKe ζ hζ0]
      exact mul_ne_zero hζ0 (hgx _ (hext ζ hζ0 (mem_ball_zero_iff.mp hζ)))
  have hψe : ∀ ζ : ℂ, ζ ≠ 0 → ζ * (K ζ)⁻¹ = (g ζ⁻¹ - x₀)⁻¹ := by
    intro ζ hζ
    rw [hKe ζ hζ, mul_inv, ← mul_assoc, mul_inv_cancel₀ hζ, one_mul]
  refine ⟨fun ζ => ζ * (K ζ)⁻¹, ⟨?_, ?_, ?_⟩, by simp, ?_⟩
  · intro ζ hζ
    exact differentiableWithinAt_id.mul ((hKd ζ hζ).inv (hKne ζ hζ))
  · intro x hx y hy hxy
    dsimp only at hxy
    by_cases hx0 : x = 0
    · by_cases hy0 : y = 0
      · rw [hx0, hy0]
      · exfalso
        rw [hx0, zero_mul, hψe y hy0] at hxy
        exact inv_ne_zero (hgx _ (hext y hy0 (mem_ball_zero_iff.mp hy))) hxy.symm
    · by_cases hy0 : y = 0
      · exfalso
        rw [hy0, zero_mul, hψe x hx0] at hxy
        exact inv_ne_zero (hgx _ (hext x hx0 (mem_ball_zero_iff.mp hx))) hxy
      · rw [hψe x hx0, hψe y hy0] at hxy
        have h1 : g x⁻¹ = g y⁻¹ := sub_left_injective (inv_injective hxy)
        exact inv_injective (hg.2.1 (hext x hx0 (mem_ball_zero_iff.mp hx))
          (hext y hy0 (mem_ball_zero_iff.mp hy)) h1)
  · ext w
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      by_cases hζ0 : ζ = 0
      · refine Or.inr ?_
        show ζ * (K ζ)⁻¹ = 0
        rw [hζ0, zero_mul]
      · refine Or.inl ⟨g ζ⁻¹, ?_, ?_⟩
        · rw [← hg.2.2]
          exact mem_image_of_mem g (hext ζ hζ0 (mem_ball_zero_iff.mp hζ))
        · show (g ζ⁻¹ - x₀)⁻¹ = ζ * (K ζ)⁻¹
          rw [hψe ζ hζ0]
    · rintro (⟨z, hz, rfl⟩ | hw)
      · rw [← hg.2.2] at hz
        obtain ⟨z', hz', rfl⟩ := hz
        have hz'1 : 1 < ‖z'‖ := hz'
        have hz'0 : z' ≠ 0 := by
          rintro rfl
          rw [norm_zero] at hz'1
          linarith
        refine ⟨z'⁻¹, ?_, ?_⟩
        · show z'⁻¹ ∈ ball (0 : ℂ) 1
          rw [mem_ball_zero_iff, norm_inv]
          exact inv_lt_one_of_one_lt₀ hz'1
        · show z'⁻¹ * (K z'⁻¹)⁻¹ = (g z' - x₀)⁻¹
          rw [hψe _ (inv_ne_zero hz'0), inv_inv]
      · refine ⟨0, mem_ball_self one_pos, ?_⟩
        rw [mem_singleton_iff.mp hw]
        show (0 : ℂ) * (K 0)⁻¹ = 0
        exact zero_mul _
  · have hKD0 : DifferentiableAt ℂ K 0 := hKd.differentiableAt (ball_mem_nhds 0 one_pos)
    have h1 : HasDerivAt (fun ζ : ℂ => ζ * (K ζ)⁻¹)
        (1 * (K 0)⁻¹ + (0 : ℂ) * deriv (fun ζ => (K ζ)⁻¹) 0) 0 :=
      (hasDerivAt_id (0 : ℂ)).mul (hKD0.inv (hKne 0 (mem_ball_self one_pos))).hasDerivAt
    rw [h1.deriv, hK0]
    ring

/-- Proposition 2.8(a) `prop:separation`, `sec02-prelim.tex:424`: for a bounded Jordan curve with
`g : 𝔻* → Ωs` conformal, `g(∞) = ∞`, `g'(∞) = lim g(z)/z = c`, the horoball of `ρ*` at `∞`
(transported through `invAt x₀`, `x₀ ∈ Γ`, which sends `∞` to `0`) is the half-space
`{ξ ≥ |g'(∞)|}`. -/
theorem prop_separation_a_infty {Ω Ωs : Set ℂ}
    (hΓ : ∃ F : ℂ ≃ₜ ℂ, F '' unitDisc = Ω ∧ F '' unitDiscExterior = Ωs) {g : ℂ → ℂ}
    (hg : IsConformalOnto g unitDiscExterior Ωs) {c : ℂ}
    (hc : Tendsto (fun z => g z / z) (Bornology.cobounded ℂ) (𝓝 c)) {x₀ : ℂ}
    (hx₀ : x₀ ∈ curveOf Ω Ωs) :
    {q | q ∈ UHS ∧ invExt x₀ q ∈ horoball (invPairΩs Ωs x₀) 0} = {q | q ∈ UHS ∧ ‖c‖ ≤ q.2} := by
  have hx₀s : x₀ ∉ Ωs := fun h => hx₀ (Or.inr h)
  have hc0 := s02_ext_coeff_ne_zero hΓ hg hc
  have hcp : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  obtain ⟨ψ, hψ, hψ0, hψd⟩ := s02_invPair_riemannMap hΓ hg hc hx₀s
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  ext q
  simp only [mem_setOf_eq]
  refine and_congr_right fun hq => ?_
  have hq' : 0 < q.2 := hq
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = ‖q.1 - x₀‖ ^ 2 + q.2 ^ 2 := ⟨_, rfl⟩
  have hNp : 0 < N := by
    rw [hN]
    positivity
  have hp2 : (invExt x₀ q).2 = q.2 / N := by
    rw [hN]
    rfl
  have hp2pos : 0 < (invExt x₀ q).2 := by
    rw [hp2]
    positivity
  have hnn : ‖(invExt x₀ q).1 - ψ 0‖ ^ 2 + (invExt x₀ q).2 ^ 2 = 1 / N := by
    rw [hψ0, sub_zero, hp2]
    have hp1 : (invExt x₀ q).1 = conj (q.1 - x₀) / ((N : ℝ) : ℂ) := by
      rw [hN]
      rfl
    rw [hp1, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hNp.le,
      div_pow, div_pow, ← add_div, ← hN, sq N, ← div_div, div_self hNp.ne']
  have hhoro := s02_horoPhi_eq hψ h0 (invExt x₀ q)
  rw [hnn, hψd, hp2, hψ0] at hhoro
  show (invExt x₀ q ∈ UHS ∧ horoPhi (invPairΩs Ωs x₀) (invExt x₀ q) 0 ≤ 1) ↔ ‖c‖ ≤ q.2
  rw [hhoro, norm_inv, norm_zero]
  have hN0 := hNp.ne'
  have hc1 := hcp.ne'
  have hq0 := hq'.ne'
  have e : 1 / N / (‖c‖⁻¹ * (1 - 0 ^ 2) * (q.2 / N)) = ‖c‖ / q.2 := by
    field_simp
    norm_num
  rw [e, div_le_one hq']
  exact ⟨fun h => h.2, fun h => ⟨hp2pos, h⟩⟩

/-- Proposition 2.8(a) `prop:separation`, `sec02-prelim.tex:426` (BBVW Lemma 4.1):
`|g'(∞)| ≥ |f'(0)|`, with equality only if `Γ` is a circle (then `Ω = D(0, |f'(0)|)`). -/
theorem prop_separation_a {Ω Ωs : Set ℂ}
    (hΓ : ∃ F : ℂ ≃ₜ ℂ, F '' unitDisc = Ω ∧ F '' unitDiscExterior = Ωs) {f g : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (hf0 : f 0 = 0)
    (hg : IsConformalOnto g unitDiscExterior Ωs) {c : ℂ}
    (hc : Tendsto (fun z => g z / z) (Bornology.cobounded ℂ) (𝓝 c)) :
    ‖deriv f 0‖ ≤ ‖c‖ ∧ (‖c‖ = ‖deriv f 0‖ → Ω = ball 0 ‖deriv f 0‖) := by
  have hdisj := s02_homeo_disjoint hΓ
  have hc0 := s02_ext_coeff_ne_zero hΓ hg hc
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = deriv f 0 := ⟨_, rfl⟩
  rw [← ha]
  have ha0 : a ≠ 0 := by
    rw [ha]
    exact deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 h0
  have hai : a⁻¹ ≠ 0 := inv_ne_zero ha0
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : ℂ → ℂ, f₁ = fun z => a⁻¹ * f z := ⟨_, rfl⟩
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : ℂ → ℂ, g₁ = fun z => a⁻¹ * g z := ⟨_, rfl⟩
  have hN : TakhtajanTeo.Ch2.IsNormalizedDisjointPair f₁ g₁ := by
    rw [hf₁, hg₁]
    refine ⟨hf.1.const_mul a⁻¹, fun x hx y hy hxy => hf.2.1 hx hy (mul_left_cancel₀ hai hxy),
      by simp [hf0], ?_, ⟨hg.1.const_mul a⁻¹, fun x hx y hy hxy =>
        hg.2.1 hx hy (mul_left_cancel₀ hai hxy), ?_⟩, ?_⟩
    · rw [deriv_const_mul _ (hf.1.differentiableAt (isOpen_ball.mem_nhds h0)), ← ha,
        inv_mul_cancel₀ ha0]
    · rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
      have h1 : Tendsto (fun z => ‖a⁻¹ * (g z / z)‖) (Bornology.cobounded ℂ) (𝓝 ‖a⁻¹ * c‖) :=
        (hc.const_mul a⁻¹).norm
      have h2 := h1.pos_mul_atTop (norm_pos_iff.mpr (mul_ne_zero hai hc0))
        tendsto_norm_cobounded_atTop
      refine h2.congr' ?_
      filter_upwards [eventually_cobounded_le_norm 1] with z hz
      have hz0 : z ≠ 0 := by
        rintro rfl
        norm_num at hz
      rw [← norm_mul, mul_assoc, div_mul_cancel₀ _ hz0]
    · have e1 : (fun z => a⁻¹ * f z) '' unitDisc = (fun w => a⁻¹ * w) '' Ω := by
        rw [← hf.2.2, image_image]
      have e2 : (fun z => a⁻¹ * g z) '' unitDiscExterior = (fun w => a⁻¹ * w) '' Ωs := by
        rw [← hg.2.2, image_image]
      rw [e1, e2]
      exact (disjoint_image_iff (mul_right_injective₀ hai)).mpr hdisj
  have hD : TakhtajanTeo.derivAtInfty g₁ = a⁻¹ * c := by
    show limUnder (cocompact ℂ) (fun z => g₁ z / z) = a⁻¹ * c
    refine Tendsto.limUnder_eq ?_
    rw [← Metric.cobounded_eq_cocompact, hg₁]
    simpa only [mul_div_assoc] using hc.const_mul a⁻¹
  obtain ⟨hge1, heq1⟩ := s02_area_core hN
  rw [hD] at hge1 heq1
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hnorm : ‖a⁻¹ * c‖ = ‖c‖ / ‖a‖ := by rw [norm_mul, norm_inv, inv_mul_eq_div]
  refine ⟨?_, fun heq => ?_⟩
  · rwa [hnorm, le_div_iff₀ hapos, one_mul] at hge1
  · have hid := heq1 (by rw [hnorm, heq, div_self hapos.ne'])
    have hfz : ∀ z ∈ unitDisc, f z = a * z := by
      intro z hz
      have h3 : a⁻¹ * f z = z := by
        have h2 := hid z hz
        rw [hf₁] at h2
        exact h2
      calc f z = a * (a⁻¹ * f z) := by rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
        _ = a * z := by rw [h3]
    rw [← hf.2.2]
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hfz z hz, mem_ball_zero_iff, norm_mul]
      exact mul_lt_of_lt_one_right hapos (mem_ball_zero_iff.mp hz)
    · intro hw
      have hz : a⁻¹ * w ∈ unitDisc := by
        refine mem_ball_zero_iff.mpr ?_
        rw [norm_mul, norm_inv, inv_mul_lt_iff₀ hapos, mul_one]
        exact mem_ball_zero_iff.mp hw
      exact ⟨_, hz, by rw [hfz _ hz, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul]⟩

/-- Proposition 2.8(b) `prop:separation`, `sec02-prelim.tex:427`: if `Γ` is not a circle, then
`B_w ∩ B*_{w*} = ∅` and `d(B_w, B*_{w*}) > 0` for all `w ∈ Ω`, `w* ∈ Ω*`; in particular
`U ∩ U* = ∅`. -/
theorem prop_separation_b {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) (hnc : ¬ IsLinePair Ω Ωs) :
    (∀ w ∈ Ω, ∀ ws ∈ Ωs, horoball Ω w ∩ horoball Ωs ws = ∅ ∧
      0 < hdistSets (horoball Ω w) (horoball Ωs ws)) ∧
      horoUnion Ω ∩ horoUnion Ωs = ∅ := by
  have hd := s02_jordanPair_disjoint hΓ
  have hΓs := s02_jordanPair_symm hΓ
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have e0 : (1 : ℝ) - ‖(0 : ℂ)‖ ^ 2 = 1 := by simp
  have hpair : ∀ w ∈ Ω, ∀ ws ∈ Ωs, horoball Ω w ∩ horoball Ωs ws = ∅ ∧
      0 < hdistSets (horoball Ω w) (horoball Ωs ws) := by
    intro w hw ws hws
    obtain ⟨f, hf, rfl⟩ := s02_riemannMap_at hΓ hw
    obtain ⟨g, hg, rfl⟩ := s02_riemannMap_at hΓs hws
    have hfd : 0 < ‖deriv f 0‖ :=
      norm_pos_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 h0)
    have hgd : 0 < ‖deriv g 0‖ :=
      norm_pos_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hg.1 hg.2.1 h0)
    have hle := s02_teo_ineq hd hf hg h0 h0
    rw [e0, mul_one, mul_one] at hle
    have hlt : ‖deriv f 0‖ * ‖deriv g 0‖ < ‖f 0 - g 0‖ ^ 2 :=
      lt_of_le_of_ne hle (fun h => hnc (s02_teo_eq_line hΓ hf hg h))
    have h2 : hdistSets (horoball Ω (f 0)) (horoball Ωs (g 0)) =
        Real.log (‖f 0 - g 0‖ ^ 2 / (‖deriv f 0‖ * ‖deriv g 0‖)) := by
      have hB1 := s02_horoball_eq hf h0
      have hB2 := s02_horoball_eq hg h0
      rw [e0, mul_one] at hB1 hB2
      rw [hB1, hB2]
      exact s02_hdist_horoballs hfd hgd hle
    refine ⟨eq_empty_of_forall_notMem fun q hq => ?_, ?_⟩
    · obtain ⟨⟨hq1, h1⟩, ⟨-, h3⟩⟩ := hq
      have hq1' : 0 < q.2 := hq1
      rw [s02_horoPhi_eq hf h0, e0, mul_one, div_le_one (mul_pos hfd hq1')] at h1
      rw [s02_horoPhi_eq hg h0, e0, mul_one, div_le_one (mul_pos hgd hq1')] at h3
      exact s02_closed_horo_disjoint hlt hq1' h1 h3
    · rw [h2]
      exact Real.log_pos ((one_lt_div (mul_pos hfd hgd)).mpr hlt)
  refine ⟨hpair, eq_empty_of_forall_notMem fun q hq => ?_⟩
  obtain ⟨hq1, hq2⟩ := hq
  simp only [horoUnion, mem_iUnion] at hq1 hq2
  obtain ⟨w, hw, hqw⟩ := hq1
  obtain ⟨ws, hws, hqws⟩ := hq2
  exact (eq_empty_iff_forall_notMem.mp (hpair w hw ws hws).1) q ⟨hqw, hqws⟩

/-- Proposition 2.8(c) `prop:separation`, `sec02-prelim.tex:430` (Teo, Prop. 7.1): the horoballs
at `f(p)` and `g(q)` have disjoint interiors, at distance
`D = log |(f(p) - g(q))² / (f'(p) g'(q) (1-|p|²)(|q|²-1))| ≥ 0`.

Here `∞ ∈ Γ`, so `g` has no pole and `𝔻*` is parametrized by `ζ = 1/q ∈ 𝔻`: we write
`g̃(ζ) = g(1/ζ)`, conformal `𝔻 → Ω*`, for which `|g'(q)|(|q|²-1) = |g̃'(ζ)|(1-|ζ|²)`. -/
theorem prop_separation_c {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) {f gt : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (hg : IsConformalOnto gt unitDisc Ωs) {p ζ : ℂ}
    (hp : p ∈ unitDisc) (hζ : ζ ∈ unitDisc) :
    {q | q ∈ UHS ∧ horoPhi Ω q (f p) < 1} ∩ {q | q ∈ UHS ∧ horoPhi Ωs q (gt ζ) < 1} = ∅ ∧
      hdistSets (horoball Ω (f p)) (horoball Ωs (gt ζ)) =
        Real.log (‖f p - gt ζ‖ ^ 2 /
          (‖deriv f p‖ * ‖deriv gt ζ‖ * (1 - ‖p‖ ^ 2) * (1 - ‖ζ‖ ^ 2))) ∧
      0 ≤ Real.log (‖f p - gt ζ‖ ^ 2 /
          (‖deriv f p‖ * ‖deriv gt ζ‖ * (1 - ‖p‖ ^ 2) * (1 - ‖ζ‖ ^ 2))) := by
  have hd := s02_jordanPair_disjoint hΓ
  have hle := s02_teo_ineq hd hf hg hp hζ
  have hp1 : 0 < 1 - ‖p‖ ^ 2 := by
    have := mem_ball_zero_iff.mp hp
    nlinarith [norm_nonneg p]
  have hζ1 : 0 < 1 - ‖ζ‖ ^ 2 := by
    have := mem_ball_zero_iff.mp hζ
    nlinarith [norm_nonneg ζ]
  have hD₁ : 0 < ‖deriv f p‖ * (1 - ‖p‖ ^ 2) :=
    mul_pos (norm_pos_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hp)) hp1
  have hD₂ : 0 < ‖deriv gt ζ‖ * (1 - ‖ζ‖ ^ 2) :=
    mul_pos (norm_pos_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hg.1 hg.2.1 hζ)) hζ1
  have hB1 : horoball Ω (f p) =
      {q | q ∈ UHS ∧ ‖q.1 - f p‖ ^ 2 + q.2 ^ 2 ≤ ‖deriv f p‖ * (1 - ‖p‖ ^ 2) * q.2} := by
    ext q
    constructor
    · rintro ⟨hq, h⟩
      refine ⟨hq, ?_⟩
      rwa [s02_horoPhi_eq hf hp, div_le_one (mul_pos hD₁ hq)] at h
    · rintro ⟨hq, h⟩
      refine ⟨hq, ?_⟩
      rwa [s02_horoPhi_eq hf hp, div_le_one (mul_pos hD₁ hq)]
  have hB2 : horoball Ωs (gt ζ) =
      {q | q ∈ UHS ∧ ‖q.1 - gt ζ‖ ^ 2 + q.2 ^ 2 ≤ ‖deriv gt ζ‖ * (1 - ‖ζ‖ ^ 2) * q.2} := by
    ext q
    constructor
    · rintro ⟨hq, h⟩
      refine ⟨hq, ?_⟩
      rwa [s02_horoPhi_eq hg hζ, div_le_one (mul_pos hD₂ hq)] at h
    · rintro ⟨hq, h⟩
      refine ⟨hq, ?_⟩
      rwa [s02_horoPhi_eq hg hζ, div_le_one (mul_pos hD₂ hq)]
  have e : ‖deriv f p‖ * ‖deriv gt ζ‖ * (1 - ‖p‖ ^ 2) * (1 - ‖ζ‖ ^ 2) =
      ‖deriv f p‖ * (1 - ‖p‖ ^ 2) * (‖deriv gt ζ‖ * (1 - ‖ζ‖ ^ 2)) := by ring
  rw [e]
  refine ⟨?_, ?_, Real.log_nonneg ((one_le_div (mul_pos hD₁ hD₂)).mpr hle)⟩
  · refine eq_empty_of_forall_notMem fun q hq => ?_
    obtain ⟨⟨hq1, h1⟩, ⟨-, h2⟩⟩ := hq
    rw [s02_horoPhi_eq hf hp, div_lt_one (mul_pos hD₁ hq1)] at h1
    rw [s02_horoPhi_eq hg hζ, div_lt_one (mul_pos hD₂ hq1)] at h2
    exact s02_open_horo_disjoint hle hq1 h1 h2
  · rw [hB1, hB2]
    exact s02_hdist_horoballs hD₁ hD₂ hle

/-- Schwarz–Pick monotonicity: `Ω₁ ⊆ Ω₂` gives `λ_{Ω₂} ≤ λ_{Ω₁}` on `Ω₁`. -/
theorem s02_poincareDensity_anti {Ω₁ Ω₂ : Set ℂ} {f₁ f₂ : ℂ → ℂ}
    (h1 : IsConformalOnto f₁ unitDisc Ω₁) (h2 : IsConformalOnto f₂ unitDisc Ω₂) (hsub : Ω₁ ⊆ Ω₂)
    {w : ℂ} (hw : w ∈ Ω₁) : poincareDensity Ω₂ w ≤ poincareDensity Ω₁ w := by
  obtain ⟨z1, hz1, rfl⟩ : w ∈ f₁ '' unitDisc := by rw [h1.2.2]; exact hw
  obtain ⟨z2, hz2, hz2e⟩ : f₁ z1 ∈ f₂ '' unitDisc := by rw [h2.2.2]; exact hsub hw
  have g1 := s02_poincareDensity_isGreatest h1 hz1
  have g2 := s02_poincareDensity_isGreatest h2 hz2
  rw [hz2e] at g2
  unfold poincareDensity
  rw [g1.csSup_eq, g2.csSup_eq]
  have hz11 : ‖z1‖ < 1 := mem_ball_zero_iff.mp hz1
  have hpos : 0 < (1 - ‖z1‖ ^ 2) * ‖deriv f₁ z1‖ :=
    mul_pos (by nlinarith [norm_nonneg z1])
      (norm_pos_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball h1.1 h1.2.1 hz1))
  have hle : (1 - ‖z1‖ ^ 2) * ‖deriv f₁ z1‖ ≤ (1 - ‖z2‖ ^ 2) * ‖deriv f₂ z2‖ := by
    obtain ⟨g, hg, hgm, hg0, hgr⟩ := g1.1
    exact g2.2 ⟨g, hg, hgm.mono_right hsub, hg0, hgr⟩
  exact div_le_div_of_nonneg_left (by norm_num) hpos hle

/-- `z ↦ c + r z` maps `𝔻` conformally onto `D(c, r)`. -/
theorem s02_affine_disk (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsConformalOnto (fun z => c + (r : ℂ) * z) unitDisc (ball c r) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  refine ⟨by fun_prop, fun z _ z' _ h => ?_, ?_⟩
  · simpa [hr0] using h
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz1 := mem_ball_zero_iff.mp hz
      show dist (c + (r : ℂ) * z) c < r
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr]
      nlinarith
    · intro hw
      refine ⟨(w - c) / r, ?_, ?_⟩
      · refine mem_ball_zero_iff.mpr ?_
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_lt_one hr,
          ← dist_eq_norm]
        exact hw
      · show c + (r : ℂ) * ((w - c) / r) = w
        field_simp
        ring

/-- A round disk `D(c, r) ⊆ Ω`: every point of the open half-ball over it lies in `U`. -/
theorem s02_disk_horoUnion {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {c : ℂ}
    {r : ℝ} (hr : 0 < r) (hD : ball c r ⊆ Ω) {q : ℂ × ℝ} (hq : q ∈ UHS)
    (hlt : ‖q.1 - c‖ ^ 2 + q.2 ^ 2 < r ^ 2) : q ∈ horoUnion Ω := by
  have hξ : 0 < q.2 := hq
  have hA := s02_affine_disk c hr
  set ρ := ‖q.1 - c‖ with hρdef
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  set s := r + q.2 with hs
  have hspos : 0 < s := by linarith
  set z0 : ℂ := (q.1 - c) / ((s : ℝ) : ℂ) with hz0
  have hnz : ‖z0‖ = ρ / s := by
    rw [hz0, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hspos]
  have hρs : ρ < s := by
    refine lt_of_pow_lt_pow_left₀ 2 hspos.le ?_
    nlinarith
  have hz : z0 ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hnz, div_lt_one hspos]; exact hρs)
  set w : ℂ := c + (r : ℂ) * z0 with hw
  have hwD : w ∈ ball c r := by
    rw [← hA.2.2]
    exact mem_image_of_mem _ hz
  have hlD := eq_lambda_f hA hz
  have hder : HasDerivAt (fun z => c + (r : ℂ) * z) (r : ℂ) z0 := by
    simpa using ((hasDerivAt_id z0).const_mul (r : ℂ)).const_add c
  rw [hder.deriv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hnz] at hlD
  change poincareDensity (ball c r) w * r = 2 / (1 - (ρ / s) ^ 2) at hlD
  have hmono := s02_poincareDensity_anti hA hf hD hwD
  have hs2 : 0 < s ^ 2 - ρ ^ 2 := by nlinarith
  have hlamD : poincareDensity (ball c r) w = 2 * s ^ 2 / (r * (s ^ 2 - ρ ^ 2)) := by
    rw [eq_div_iff (by positivity)]
    have h1 : 1 - (ρ / s) ^ 2 = (s ^ 2 - ρ ^ 2) / s ^ 2 := by field_simp
    rw [h1, div_div_eq_mul_div] at hlD
    calc poincareDensity (ball c r) w * (r * (s ^ 2 - ρ ^ 2)) =
        (poincareDensity (ball c r) w * r) * (s ^ 2 - ρ ^ 2) := by ring
      _ = 2 * s ^ 2 / (s ^ 2 - ρ ^ 2) * (s ^ 2 - ρ ^ 2) := by rw [hlD]
      _ = 2 * s ^ 2 := by field_simp
  have hsc : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
  have hdiff : q.1 - w = (q.1 - c) * ((q.2 / s : ℝ) : ℂ) := by
    have hrC : (r : ℂ) = ((s : ℝ) : ℂ) - (q.2 : ℂ) := by rw [hs]; push_cast; ring
    rw [hw, hz0, hrC]
    push_cast
    field_simp
    ring
  have hnd : ‖q.1 - w‖ = ρ * (q.2 / s) := by
    rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  refine mem_iUnion₂.mpr ⟨w, hD hwD, hq, ?_⟩
  show horoPhi Ω q w ≤ 1
  unfold horoPhi
  rw [hnd, div_le_one (by positivity)]
  have hX : 0 ≤ (ρ * (q.2 / s)) ^ 2 + q.2 ^ 2 := by positivity
  have key : q.2 * (ρ ^ 2 + s ^ 2) ≤ r * (s ^ 2 - ρ ^ 2) := by
    rw [hs]
    nlinarith [mul_pos hξ hr]
  have hY : s ^ 2 * ((ρ * (q.2 / s)) ^ 2 + q.2 ^ 2) = q.2 ^ 2 * (ρ ^ 2 + s ^ 2) := by
    field_simp
  calc poincareDensity Ω w * ((ρ * (q.2 / s)) ^ 2 + q.2 ^ 2)
      ≤ poincareDensity (ball c r) w * ((ρ * (q.2 / s)) ^ 2 + q.2 ^ 2) :=
        mul_le_mul_of_nonneg_right hmono hX
    _ = 2 * q.2 * (q.2 * (ρ ^ 2 + s ^ 2)) / (r * (s ^ 2 - ρ ^ 2)) := by
        rw [hlamD, div_mul_eq_mul_div, mul_assoc, hY]
        ring
    _ ≤ 2 * q.2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 * q.2)]

/-- Lemma 2.9 `lem:gap-hull`, `sec02-prelim.tex:464`: `𝒩 ⊆ CH(Γ)`. -/
theorem lem_gap_hull {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) :
    gap Ω Ωs ⊆ hypHull (curveOf Ω Ωs) := by
  intro q hq
  obtain ⟨hqU, hqn⟩ := hq
  have hξ : 0 < q.2 := hqU
  obtain ⟨F, hF1, hF2⟩ := id hΓ
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hLo : IsOpen lowerHalf := isOpen_lt Complex.continuous_im continuous_const
  have hΩo : IsOpen Ω := by
    rw [← hF1]
    exact F.isOpenMap _ hUo
  have hΩso : IsOpen Ωs := by
    rw [← hF2]
    exact F.isOpenMap _ hLo
  have hdisj : Disjoint Ω Ωs := by
    rw [← hF1, ← hF2, disjoint_image_iff F.injective]
    refine Set.disjoint_left.mpr fun z h1 h2 => ?_
    have h1' : 0 < z.im := h1
    have h2' : z.im < 0 := h2
    linarith
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hΓ
  obtain ⟨g, hg⟩ := s02_jordanPair_riemannMap (s02_jordanPair_symm hΓ)
  -- open disks missing `Γ`
  have hdisk : ∀ (c : ℂ) (r : ℝ), 0 < r → Disjoint (ball c r) (curveOf Ω Ωs) →
      r ^ 2 ≤ ‖q.1 - c‖ ^ 2 + q.2 ^ 2 := by
    intro c r hr hD
    by_contra hlt
    push Not at hlt
    have hsub : ball c r ⊆ Ω ∪ Ωs := by
      intro z hz
      have h := Set.disjoint_left.mp hD hz
      unfold curveOf at h
      rwa [Set.mem_compl_iff, not_not] at h
    rcases (convex_ball c r).isPreconnected.subset_or_subset hΩo hΩso hdisj hsub with h | h
    · exact hqn (Or.inl (s02_disk_horoUnion hf hr h hqU hlt))
    · exact hqn (Or.inr (s02_disk_horoUnion hg hr h hqU hlt))
  refine ⟨hqU, hdisk, ?_⟩
  -- open half-planes missing `Γ`: reduce to a disk inside the half-plane
  intro a b ha hP
  by_contra hlt
  push Not at hlt
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set R := q.2 ^ 2 * ‖a‖ / (a * q.1 + b).im with hR
  have hRpos : 0 < R := by positivity
  set r := R + (a * q.1 + b).im / ‖a‖ with hr
  have hrpos : 0 < r := by positivity
  set c : ℂ := q.1 + I * ((R * ‖a‖ : ℝ) : ℂ) / a with hc
  have hac : a * c + b = (a * q.1 + b) + I * ((R * ‖a‖ : ℝ) : ℂ) := by
    rw [hc]
    field_simp
    ring
  have hcW : ‖q.1 - c‖ = R := by
    rw [hc, show q.1 - (q.1 + I * ((R * ‖a‖ : ℝ) : ℂ) / a) = -(I * ((R * ‖a‖ : ℝ) : ℂ) / a) by
      ring, norm_neg, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  have him : (a * c + b).im = (a * q.1 + b).im + R * ‖a‖ := by
    rw [hac, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hsubP : ball c r ⊆ {z : ℂ | 0 < (a * z + b).im} := by
    intro z hz
    have hz' : ‖z - c‖ < r := by
      rw [← dist_eq_norm]
      exact hz
    show 0 < (a * z + b).im
    have e : a * z + b = (a * c + b) + a * (z - c) := by ring
    have h1 : -‖a * (z - c)‖ ≤ (a * (z - c)).im :=
      (neg_le_neg (abs_im_le_norm _)).trans (neg_abs_le _)
    rw [norm_mul] at h1
    rw [e, Complex.add_im, him]
    have h2 : ‖a‖ * ‖z - c‖ < ‖a‖ * r := mul_lt_mul_of_pos_left hz' hna
    have hr' : ‖a‖ * r = R * ‖a‖ + (a * q.1 + b).im := by
      rw [hr]
      field_simp
    linarith
  have h := hdisk c r hrpos (hP.mono_left hsubP)
  rw [hcW] at h
  have hr2 : r ^ 2 = R ^ 2 + 2 * q.2 ^ 2 + ((a * q.1 + b).im / ‖a‖) ^ 2 := by
    rw [hr, hR]
    field_simp
    ring
  have := pow_pos hξ 2
  nlinarith [sq_nonneg ((a * q.1 + b).im / ‖a‖)]

/-! ## §2.7 Labels and the intrinsic quantities -/

/-- For every `q ∈ ℍ³`, the set of minimizers of `Φ_q` on `Ω` is nonempty and compact
(the body of `subsec_labels_minimizers`, which does not use `q ∉ U`). -/
theorem s02_minSet {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) {q : ℂ × ℝ} (hq : q ∈ UHS) :
    {w | w ∈ Ω ∧ ∀ w' ∈ Ω, horoPhi Ω q w ≤ horoPhi Ω q w'}.Nonempty ∧
      IsCompact {w | w ∈ Ω ∧ ∀ w' ∈ Ω, horoPhi Ω q w ≤ horoPhi Ω q w'} := by
  have hΩ := s02_jordanPair_riemannMap hΓ
  obtain ⟨w₀, hw₀, hmin₀⟩ := lem_proper_min hΓ hq
  refine ⟨⟨w₀, hw₀, hmin₀⟩, ?_⟩
  obtain ⟨K', hK', hK'Ω, hsub⟩ := lem_proper_compact hΓ isCompact_singleton
    (singleton_subset_iff.mpr hq) (horoPhi Ω q w₀)
  have hSeq : {w | w ∈ Ω ∧ ∀ w' ∈ Ω, horoPhi Ω q w ≤ horoPhi Ω q w'} =
      K' ∩ horoPhi Ω q ⁻¹' Iic (horoPhi Ω q w₀) := by
    ext w
    constructor
    · rintro ⟨hw, hmin⟩
      exact ⟨hsub ⟨hw, q, mem_singleton q, hmin w₀ hw₀⟩, hmin w₀ hw₀⟩
    · rintro ⟨hwK, hwT⟩
      exact ⟨hK'Ω hwK, fun w' hw' => le_trans hwT (hmin₀ w' hw')⟩
  rw [hSeq]
  have hcont : ContinuousOn (horoPhi Ω q) K' := by
    intro w hw
    have h1 := s02_continuousAt_poincareDensity hΩ (hK'Ω hw)
    have h2 : ContinuousAt (fun w : ℂ => ‖q.1 - w‖ ^ 2 + q.2 ^ 2) w := by fun_prop
    exact ((h1.mul h2).div_const (2 * q.2)).continuousWithinAt
  exact hK'.of_isClosed_subset
    (hcont.preimage_isClosed_of_isClosed hK'.isClosed isClosed_Iic) inter_subset_left

/-- §2.7, `sec02-prelim.tex:488`: for `q ∈ ℍ³ ∖ U` the set `𝒜(q)` of minimizers of `Φ_q` on `Ω`
is nonempty and compact. -/
theorem subsec_labels_minimizers {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs)
    (hnc : ¬ IsLinePair Ω Ωs) {q : ℂ × ℝ} (hq : q ∈ UHS) (hqU : q ∉ horoUnion Ω) :
    {w | w ∈ Ω ∧ ∀ w' ∈ Ω, horoPhi Ω q w ≤ horoPhi Ω q w'}.Nonempty ∧
      IsCompact {w | w ∈ Ω ∧ ∀ w' ∈ Ω, horoPhi Ω q w ≤ horoPhi Ω q w'} := by
  -- `hnc` and `hqU` are not needed: the minimizer set is nonempty and compact for every `q ∈ ℍ³`
  -- (the statement stays true without them).
  have _h1 := hnc
  have _h2 := hqU
  exact s02_minSet hΓ hq

/-- `(q, w) ↦ Φ_q(w)` is jointly continuous on `ℍ³ × Ω`. -/
theorem s02_horoPhi_continuousOn {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) :
    ContinuousOn (fun p : (ℂ × ℝ) × ℂ => horoPhi Ω p.1 p.2) (UHS ×ˢ Ω) := by
  have hΩ := s02_jordanPair_riemannMap hΓ
  intro p hp
  have hq : 0 < p.1.2 := hp.1
  have h1 : ContinuousAt (fun p : (ℂ × ℝ) × ℂ => poincareDensity Ω p.2) p :=
    (s02_continuousAt_poincareDensity hΩ hp.2).comp continuousAt_snd
  have h2 : ContinuousAt (fun p : (ℂ × ℝ) × ℂ => ‖p.1.1 - p.2‖ ^ 2 + p.1.2 ^ 2) p := by
    fun_prop
  have h3 : ContinuousAt (fun p : (ℂ × ℝ) × ℂ => 2 * p.1.2) p := by fun_prop
  exact ((h1.mul h2).div h3 (by positivity)).continuousWithinAt

/-- Over a compact `𝒬 ⊆ ℍ³`, the graph `{(q, w) : q ∈ 𝒬, w ∈ 𝒜(q)}` of the minimizer sets is
compact (`lem_proper_compact` bounds the minimizers uniformly). -/
theorem s02_minGraph_compact {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) {𝒬 : Set (ℂ × ℝ)}
    (h𝒬 : IsCompact 𝒬) (h𝒬U : 𝒬 ⊆ UHS) :
    IsCompact {p : (ℂ × ℝ) × ℂ | p.1 ∈ 𝒬 ∧ p.2 ∈ Ω ∧
      ∀ w' ∈ Ω, horoPhi Ω p.1 p.2 ≤ horoPhi Ω p.1 w'} := by
  have hc := s02_horoPhi_continuousOn hΓ
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hΓ
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hw₀ : f 0 ∈ Ω := by
    rw [← hf.2.2]
    exact mem_image_of_mem f h0
  have hc₀ : ContinuousOn (fun q : ℂ × ℝ => horoPhi Ω q (f 0)) 𝒬 :=
    hc.comp (continuousOn_id.prodMk continuousOn_const) (fun q hq => ⟨h𝒬U hq, hw₀⟩)
  obtain ⟨T, hT⟩ := h𝒬.bddAbove_image hc₀
  obtain ⟨K', hK', hK'Ω, hsub⟩ := lem_proper_compact hΓ h𝒬 h𝒬U T
  have hS : IsCompact (𝒬 ×ˢ K') := h𝒬.prod hK'
  have heq : {p : (ℂ × ℝ) × ℂ | p.1 ∈ 𝒬 ∧ p.2 ∈ Ω ∧
      ∀ w' ∈ Ω, horoPhi Ω p.1 p.2 ≤ horoPhi Ω p.1 w'} = (𝒬 ×ˢ K') ∩ ⋂ w' ∈ Ω,
      ((𝒬 ×ˢ K') ∩ (fun p : (ℂ × ℝ) × ℂ => horoPhi Ω p.1 w' - horoPhi Ω p.1 p.2) ⁻¹' Ici 0) := by
    ext p
    constructor
    · rintro ⟨hp1, hp2, hp3⟩
      have hK : p.2 ∈ K' := hsub ⟨hp2, p.1, hp1, le_trans (hp3 _ hw₀) (hT ⟨p.1, hp1, rfl⟩)⟩
      refine ⟨⟨hp1, hK⟩, ?_⟩
      simp only [mem_iInter]
      intro w' hw'
      exact ⟨⟨hp1, hK⟩, sub_nonneg.mpr (hp3 w' hw')⟩
    · rintro ⟨⟨hp1, hK⟩, h⟩
      simp only [mem_iInter] at h
      exact ⟨hp1, hK'Ω hK, fun w' hw' => sub_nonneg.mp (h w' hw').2⟩
  rw [heq]
  refine hS.of_isClosed_subset ?_ inter_subset_left
  refine hS.isClosed.inter (isClosed_biInter fun w' hw' => ?_)
  refine ContinuousOn.preimage_isClosed_of_isClosed ?_ hS.isClosed isClosed_Ici
  have hsub2 : 𝒬 ×ˢ K' ⊆ UHS ×ˢ Ω := prod_mono h𝒬U hK'Ω
  have hA : ContinuousOn (fun p : (ℂ × ℝ) × ℂ => horoPhi Ω p.1 w') (𝒬 ×ˢ K') :=
    hc.comp (continuousOn_fst.prodMk continuousOn_const) (fun p hp => ⟨h𝒬U hp.1, hw'⟩)
  exact hA.sub (hc.mono hsub2)

/-- For closed `C`, `{q ∈ ℍ³ : 𝒜(q) ∩ C ≠ ∅}` is Borel: on each compact `𝒬ₙ` of an exhaustion
of `ℍ³` it is the projection of the compact set `s02_minGraph_compact ∩ (ℍ³ × C)`. -/
theorem s02_minProj_measurable {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) {C : Set ℂ}
    (hC : IsClosed C) :
    MeasurableSet {q : ℂ × ℝ | q ∈ UHS ∧
      ∃ w, (w ∈ Ω ∧ ∀ w' ∈ Ω, horoPhi Ω q w ≤ horoPhi Ω q w') ∧ w ∈ C} := by
  obtain ⟨𝒬, h𝒬⟩ : ∃ 𝒬 : ℕ → Set (ℂ × ℝ),
      𝒬 = fun n : ℕ => closedBall (0 : ℂ × ℝ) (n : ℝ) ∩ {q : ℂ × ℝ | 1 / ((n : ℝ) + 1) ≤ q.2} :=
      ⟨_, rfl⟩
  have hQc : ∀ n, IsCompact (𝒬 n) := by
    intro n
    rw [h𝒬]
    exact (isCompact_closedBall 0 _).inter_right (isClosed_le continuous_const continuous_snd)
  have hQU : ∀ n, 𝒬 n ⊆ UHS := by
    intro n q hq
    rw [h𝒬] at hq
    show 0 < q.2
    exact lt_of_lt_of_le (by positivity) hq.2
  have hcover : {q : ℂ × ℝ | q ∈ UHS ∧
      ∃ w, (w ∈ Ω ∧ ∀ w' ∈ Ω, horoPhi Ω q w ≤ horoPhi Ω q w') ∧ w ∈ C} =
      ⋃ n, Prod.fst '' ({p : (ℂ × ℝ) × ℂ | p.1 ∈ 𝒬 n ∧ p.2 ∈ Ω ∧
        ∀ w' ∈ Ω, horoPhi Ω p.1 p.2 ≤ horoPhi Ω p.1 w'} ∩ {p | p.2 ∈ C}) := by
    ext q
    constructor
    · rintro ⟨hq, w, hw, hwC⟩
      have hq' : 0 < q.2 := hq
      obtain ⟨n, hn⟩ := exists_nat_ge (max ‖q‖ (1 / q.2))
      have hqn : q ∈ 𝒬 n := by
        rw [h𝒬]
        refine ⟨?_, ?_⟩
        · rw [mem_closedBall, dist_zero_right]
          exact le_trans (le_max_left _ _) hn
        · show 1 / ((n : ℝ) + 1) ≤ q.2
          rw [div_le_iff₀ (by positivity)]
          have h1 := le_trans (le_max_right _ _) hn
          rw [div_le_iff₀ hq'] at h1
          nlinarith
      exact mem_iUnion.mpr ⟨n, (q, w), ⟨⟨hqn, hw.1, hw.2⟩, hwC⟩, rfl⟩
    · intro hq
      obtain ⟨n, p, ⟨⟨hp1, hp2, hp3⟩, hpC⟩, rfl⟩ := mem_iUnion.mp hq
      exact ⟨hQU n hp1, p.2, ⟨hp2, hp3⟩, hpC⟩
  rw [hcover]
  refine MeasurableSet.iUnion fun n => ?_
  refine IsClosed.measurableSet (IsCompact.isClosed ?_)
  exact ((s02_minGraph_compact hΓ (hQc n) (hQU n)).inter_right
    (hC.preimage continuous_snd)).image continuous_fst

/-- Lemma 3.4 `lem:borel-label`, `sec03-coarse.tex:153` (used in §2.7): a Borel label exists, and
`R = w ∘ X*` is Borel on `Ω*`. -/
theorem lem_borel_label {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) (hnc : ¬ IsLinePair Ω Ωs) :
    ∃ lab : ℂ × ℝ → ℂ, IsLabel Ω lab ∧ Measurable (fun z : Ωs => lab (epstein Ωs z)) := by
  -- `hnc` is not needed (the statement stays true for a line pair). The label is the
  -- lexicographic minimum `(m₁, m₂)` of the compact minimizer set `𝒜(q)`, for every `q ∈ ℍ³`.
  classical
  have _h := hnc
  have hUm : MeasurableSet UHS := (isOpen_lt continuous_const continuous_snd).measurableSet
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : ℂ × ℝ → ℝ, m₁ = fun q =>
      sInf (re '' {w | w ∈ Ω ∧ ∀ w' ∈ Ω, horoPhi Ω q w ≤ horoPhi Ω q w'}) := ⟨_, rfl⟩
  obtain ⟨m₂, hm₂⟩ : ∃ m₂ : ℂ × ℝ → ℝ, m₂ = fun q =>
      sInf (im '' ({w | w ∈ Ω ∧ ∀ w' ∈ Ω, horoPhi Ω q w ≤ horoPhi Ω q w'} ∩
        {w | w.re ≤ m₁ q})) := ⟨_, rfl⟩
  have hA1 : ∀ q ∈ UHS, (∀ w, (w ∈ Ω ∧ ∀ w' ∈ Ω, horoPhi Ω q w ≤ horoPhi Ω q w') →
      m₁ q ≤ w.re) ∧ ∃ w, (w ∈ Ω ∧ ∀ w' ∈ Ω, horoPhi Ω q w ≤ horoPhi Ω q w') ∧
        w.re = m₁ q := by
    intro q hq
    obtain ⟨hne, hcpt⟩ := s02_minSet hΓ hq
    have hc' := hcpt.image continuous_re
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [hm₁]
      exact csInf_le hc'.bddBelow (mem_image_of_mem re hw)
    · obtain ⟨w, hw, hwe⟩ := hc'.sInf_mem (hne.image re)
      refine ⟨w, hw, ?_⟩
      rw [hm₁]
      exact hwe
  have hA2 : ∀ q ∈ UHS, (∀ w, ((w ∈ Ω ∧ ∀ w' ∈ Ω, horoPhi Ω q w ≤ horoPhi Ω q w') ∧
      w.re ≤ m₁ q) → m₂ q ≤ w.im) ∧ ∃ w, ((w ∈ Ω ∧ ∀ w' ∈ Ω, horoPhi Ω q w ≤ horoPhi Ω q w') ∧
        w.re ≤ m₁ q) ∧ w.im = m₂ q := by
    intro q hq
    obtain ⟨hne, hcpt⟩ := s02_minSet hΓ hq
    obtain ⟨w₁, hw₁, hw₁e⟩ := (hA1 q hq).2
    have hcpt2 := hcpt.inter_right (isClosed_le continuous_re (continuous_const (y := m₁ q)))
    have hc' := hcpt2.image continuous_im
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [hm₂]
      exact csInf_le hc'.bddBelow (mem_image_of_mem im hw)
    · obtain ⟨w, hw, hwe⟩ := hc'.sInf_mem (Nonempty.image im ⟨w₁, hw₁, hw₁e.le⟩)
      refine ⟨w, hw, ?_⟩
      rw [hm₂]
      exact hwe
  have hlabmem : ∀ q ∈ UHS, (⟨m₁ q, m₂ q⟩ : ℂ) ∈ Ω ∧
      ∀ w' ∈ Ω, horoPhi Ω q ⟨m₁ q, m₂ q⟩ ≤ horoPhi Ω q w' := by
    intro q hq
    obtain ⟨w, ⟨hwM, hwr⟩, hwi⟩ := (hA2 q hq).2
    have hre : w.re = m₁ q := le_antisymm hwr ((hA1 q hq).1 w hwM)
    have hw : w = ⟨m₁ q, m₂ q⟩ := Complex.ext hre hwi
    rw [← hw]
    exact hwM
  have hm₁le : ∀ t : ℝ, {q | q ∈ UHS ∧ m₁ q ≤ t} = {q : ℂ × ℝ | q ∈ UHS ∧
      ∃ w, (w ∈ Ω ∧ ∀ w' ∈ Ω, horoPhi Ω q w ≤ horoPhi Ω q w') ∧ w ∈ {b : ℂ | b.re ≤ t}} := by
    intro t
    ext q
    constructor
    · rintro ⟨hq, h⟩
      obtain ⟨w, hw, hwe⟩ := (hA1 q hq).2
      refine ⟨hq, w, hw, ?_⟩
      show w.re ≤ t
      rw [hwe]
      exact h
    · rintro ⟨hq, w, hw, hwt⟩
      exact ⟨hq, le_trans ((hA1 q hq).1 w hw) hwt⟩
  have hM1 : Measurable (fun q => if q ∈ UHS then m₁ q else 0) := by
    refine measurable_of_Iic fun t => ?_
    have he : (fun q => if q ∈ UHS then m₁ q else 0) ⁻¹' Iic t =
        {q | q ∈ UHS ∧ m₁ q ≤ t} ∪ (UHSᶜ ∩ {_q | (0 : ℝ) ≤ t}) := by
      ext q
      by_cases hq : q ∈ UHS
      · simp [hq]
      · simp [hq]
    rw [he, hm₁le t]
    exact (s02_minProj_measurable hΓ (isClosed_le continuous_re continuous_const)).union
      (hUm.compl.inter (MeasurableSet.const _))
  have hm₂le : ∀ t : ℝ, {q | q ∈ UHS ∧ m₂ q ≤ t} = ⋂ k : ℕ, ⋃ r : ℚ,
      ((UHS ∩ (fun q => if q ∈ UHS then m₁ q else 0) ⁻¹' Ioi ((r : ℝ) - 1 / ((k : ℝ) + 1))) ∩
        {q : ℂ × ℝ | q ∈ UHS ∧ ∃ w, (w ∈ Ω ∧ ∀ w' ∈ Ω, horoPhi Ω q w ≤ horoPhi Ω q w') ∧
          w ∈ {b : ℂ | b.re ≤ r} ∩ {b : ℂ | b.im ≤ t}}) := by
    intro t
    ext q
    simp only [mem_iInter, mem_iUnion]
    constructor
    · rintro ⟨hq, h⟩ k
      obtain ⟨w, ⟨hwM, hwr⟩, hwi⟩ := (hA2 q hq).2
      have hre : w.re = m₁ q := le_antisymm hwr ((hA1 q hq).1 w hwM)
      have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show m₁ q < m₁ q + 1 / ((k : ℝ) + 1) by linarith)
      refine ⟨r, ⟨hq, ?_⟩, hq, w, hwM, ?_⟩
      · show (r : ℝ) - 1 / ((k : ℝ) + 1) < if q ∈ UHS then m₁ q else 0
        rw [if_pos hq]
        linarith
      · show w.re ≤ r ∧ w.im ≤ t
        rw [hre, hwi]
        exact ⟨hr1.le, h⟩
    · intro h
      obtain ⟨r0, ⟨hq, -⟩, -, w0, hw0M, hw0C⟩ := h 0
      refine ⟨hq, ?_⟩
      obtain ⟨hne, hcpt⟩ := s02_minSet hΓ hq
      have hT := hcpt.inter_right (isClosed_le continuous_im (continuous_const (y := t)))
      have hTne : ({w | w ∈ Ω ∧ ∀ w' ∈ Ω, horoPhi Ω q w ≤ horoPhi Ω q w'} ∩
          {b : ℂ | b.im ≤ t}).Nonempty := ⟨w0, hw0M, hw0C.2⟩
      obtain ⟨w, hwT, hwmin⟩ := hT.exists_isMinOn hTne continuous_re.continuousOn
      have hwle : w.re ≤ m₁ q := by
        by_contra hlt
        push_neg at hlt
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
        obtain ⟨r, ⟨-, hr⟩, -, w', hw'M, hw'C⟩ := h k
        have hr' : (r : ℝ) - 1 / ((k : ℝ) + 1) < m₁ q := by
          have h5 : (r : ℝ) - 1 / ((k : ℝ) + 1) < if q ∈ UHS then m₁ q else 0 := hr
          rwa [if_pos hq] at h5
        have h6 : w.re ≤ w'.re := isMinOn_iff.mp hwmin w' ⟨hw'M, hw'C.2⟩
        have h7 : w'.re ≤ r := hw'C.1
        linarith
      exact le_trans ((hA2 q hq).1 w ⟨hwT.1, hwle⟩) hwT.2
  have hM2 : Measurable (fun q => if q ∈ UHS then m₂ q else 0) := by
    refine measurable_of_Iic fun t => ?_
    have he : (fun q => if q ∈ UHS then m₂ q else 0) ⁻¹' Iic t =
        {q | q ∈ UHS ∧ m₂ q ≤ t} ∪ (UHSᶜ ∩ {_q | (0 : ℝ) ≤ t}) := by
      ext q
      by_cases hq : q ∈ UHS
      · simp [hq]
      · simp [hq]
    rw [he, hm₂le t]
    refine (MeasurableSet.iInter fun k => MeasurableSet.iUnion fun r => ?_).union
      (hUm.compl.inter (MeasurableSet.const _))
    exact (hUm.inter (hM1 measurableSet_Ioi)).inter (s02_minProj_measurable hΓ
      ((isClosed_le continuous_re continuous_const).inter
        (isClosed_le continuous_im continuous_const)))
  have hlab : Measurable (fun q : ℂ × ℝ =>
      (⟨if q ∈ UHS then m₁ q else 0, if q ∈ UHS then m₂ q else 0⟩ : ℂ)) := by
    have he : (fun q : ℂ × ℝ =>
        (⟨if q ∈ UHS then m₁ q else 0, if q ∈ UHS then m₂ q else 0⟩ : ℂ)) =
        fun q => ((if q ∈ UHS then m₁ q else 0 : ℝ) : ℂ) +
          ((if q ∈ UHS then m₂ q else 0 : ℝ) : ℂ) * I := by
      funext q
      apply Complex.ext <;> simp
    rw [he]
    exact (Complex.measurable_ofReal.comp hM1).add
      ((Complex.measurable_ofReal.comp hM2).mul_const I)
  have hΩs := s02_jordanPair_riemannMap (s02_jordanPair_symm hΓ)
  have hlam : Measurable (fun z : Ωs => poincareDensity Ωs z) := by
    have hco : ContinuousOn (poincareDensity Ωs) Ωs := fun w hw =>
      (s02_continuousAt_poincareDensity hΩs hw).continuousWithinAt
    exact (continuousOn_iff_continuous_restrict.mp hco).measurable
  have hA : Measurable (fun z : Ωs => logDensityDz Ωs z) := by
    have h1 : Measurable (logDensityDz Ωs) := by
      show Measurable fun w =>
        ((fderiv ℝ (fun x => Real.log (poincareDensity Ωs x)) w 1 : ℂ) -
          I * (fderiv ℝ (fun x => Real.log (poincareDensity Ωs x)) w I : ℂ)) / 2
      exact ((Complex.measurable_ofReal.comp (measurable_fderiv_apply_const ℝ _ 1)).sub
        (measurable_const.mul (Complex.measurable_ofReal.comp
          (measurable_fderiv_apply_const ℝ _ I)))).div_const 2
    exact h1.comp measurable_subtype_coe
  have hD : Measurable (fun z : Ωs =>
      poincareDensity Ωs z ^ 2 + 4 * ‖logDensityDz Ωs z‖ ^ 2) :=
    (hlam.pow_const 2).add (measurable_const.mul (hA.norm.pow_const 2))
  have hE : Measurable (fun z : Ωs => epstein Ωs z) := by
    show Measurable fun z : Ωs => ((z : ℂ) + 4 * conj (logDensityDz Ωs z) /
        ((poincareDensity Ωs z ^ 2 + 4 * ‖logDensityDz Ωs z‖ ^ 2 : ℝ) : ℂ),
      2 * poincareDensity Ωs z / (poincareDensity Ωs z ^ 2 + 4 * ‖logDensityDz Ωs z‖ ^ 2))
    exact (measurable_subtype_coe.add ((measurable_const.mul
      (Complex.continuous_conj.measurable.comp hA)).div
        (Complex.measurable_ofReal.comp hD))).prodMk ((measurable_const.mul hlam).div hD)
  refine ⟨fun q => ⟨if q ∈ UHS then m₁ q else 0, if q ∈ UHS then m₂ q else 0⟩,
    ⟨hlab, fun q hq => ?_⟩, hlab.comp hE⟩
  show (⟨if q ∈ UHS then m₁ q else 0, if q ∈ UHS then m₂ q else 0⟩ : ℂ) ∈ Ω ∧
    ∀ w ∈ Ω, horoPhi Ω q ⟨if q ∈ UHS then m₁ q else 0, if q ∈ UHS then m₂ q else 0⟩ ≤
      horoPhi Ω q w
  rw [if_pos hq.1, if_pos hq.1]
  exact hlabmem q hq.1

/-- Lemma 2.10 `lem:nearest`, `sec02-prelim.tex:503`: for `q ∈ ℍ³ ∖ U` and `w ∈ 𝒜(q)`,
`q = E(w, τ)` with `τ = d(q, U) > 0`, and `X(w)` is a point of `U` nearest to `q`. -/
theorem lem_nearest {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) (hnc : ¬ IsLinePair Ω Ωs)
    {q : ℂ × ℝ} (hq : q ∈ UHS) (hqU : q ∉ horoUnion Ω) {w : ℂ} (hw : w ∈ Ω)
    (hmin : ∀ w' ∈ Ω, horoPhi Ω q w ≤ horoPhi Ω q w') :
    q = normalGeod Ω w (hdistSet q (horoUnion Ω)) ∧ 0 < hdistSet q (horoUnion Ω) ∧
      epstein Ω w ∈ horoUnion Ω ∧ hdist q (epstein Ω w) = hdistSet q (horoUnion Ω) := by
  -- `hnc` is not needed (the statement stays true for a line pair).
  have _h := hnc
  have hΩ := s02_jordanPair_riemannMap hΓ
  have hl := s02_poincareDensity_pos hΩ hw
  have hq2 : 0 < q.2 := hq
  have hΩo : IsOpen Ω := by
    obtain ⟨f, hf⟩ := hΩ
    exact hf.isOpen isOpen_ball
  -- `w` is a critical point of `Φ_q`
  have hloc : IsLocalMin (fun w' => horoPhi Ω q w') w :=
    Filter.mem_of_superset (hΩo.mem_nhds hw) fun w' hw' => hmin w' hw'
  obtain ⟨D, hD, -⟩ := s02_hasFDerivAt_horoPhi hΩ hw hq2
  have hD0 : D = 0 := hloc.hasFDerivAt_eq_zero hD
  rw [hD0] at hD
  have hm : q ∈ {q | q ∈ UHS ∧ HasFDerivAt (fun w' => horoPhi Ω q w') (0 : ℂ →L[ℝ] ℝ) w} :=
    ⟨hq, hD⟩
  rw [lem_normal_a hΩ hw] at hm
  obtain ⟨τ, hτ⟩ := hm
  -- `d(q, U) = log Φ_q(w) = τ`
  obtain ⟨w₀, hw₀, hmin₀, hdU⟩ := eq_dist_U hΓ hq hqU
  have heqΦ : horoPhi Ω q w₀ = horoPhi Ω q w := le_antisymm (hmin₀ w hw) (hmin w₀ hw₀)
  have hΦτ : horoPhi Ω q w = Real.exp τ := by
    rw [← hτ, s02_horoPhi_normalGeod Ω w hl τ]
  have hdτ : hdistSet q (horoUnion Ω) = τ := by
    rw [hdU, heqΦ, hΦτ, Real.log_exp]
  have hτpos : 0 < τ := by
    have hqB : q ∉ horoball Ω w := fun h => hqU (mem_iUnion₂.mpr ⟨w, hw, h⟩)
    have h1 : ¬ horoPhi Ω q w ≤ 1 := fun h => hqB ⟨hq, h⟩
    rw [hΦτ] at h1
    push Not at h1
    exact Real.one_lt_exp_iff.mp h1
  obtain ⟨-, hgeo, hE0⟩ := lem_normal_b hΩ hw
  refine ⟨by rw [hdτ, hτ], by rw [hdτ]; exact hτpos, ?_, ?_⟩
  · refine mem_iUnion₂.mpr ⟨w, hw, ?_, ?_⟩
    · rw [← hE0]
      exact s02_normalGeod_pos Ω w hl 0
    · rw [← hE0, s02_horoPhi_normalGeod Ω w hl 0, Real.exp_zero]
  · rw [hdτ, ← hτ, ← hE0, hgeo, sub_zero, abs_of_pos hτpos]

/-- A half-plane `{σ Im(a z + b) > 0}` (`σ = ±1`): `s ≡ 0` and `λ(w) σ Im(a w + b) = |a|`. -/
theorem s02_halfplane (a b : ℂ) (ha : a ≠ 0) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (Ω : Set ℂ)
    (hΩ : ∀ z, z ∈ Ω ↔ 0 < σ * (a * z + b).im) :
    (∀ w ∈ Ω, schwarzNorm Ω w = 0) ∧
      ∀ w ∈ Ω, poincareDensity Ω w * (σ * (a * w + b).im) = ‖a‖ := by
  have hσσ : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hσabs : |σ| = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  set M : ℂ → ℂ := fun v => (((σ : ℂ) * I + b) * v + ((σ : ℂ) * I - b)) / ((-a) * v + a)
    with hMdef
  have hd1 : ∀ ζ ∈ unitDisc, (1 : ℂ) - ζ ≠ 0 := by
    intro ζ hζ h
    have h1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
    have : ζ = 1 := (sub_eq_zero.mp h).symm
    rw [this, norm_one] at h1
    exact lt_irrefl _ h1
  have hden : ∀ ζ ∈ unitDisc, (-a) * ζ + a ≠ 0 := fun ζ hζ => by
    rw [show (-a) * ζ + a = a * (1 - ζ) by ring]
    exact mul_ne_zero ha (hd1 ζ hζ)
  have hMζ : ∀ ζ ∈ unitDisc, a * M ζ + b = (σ : ℂ) * (I * (1 + ζ) / (1 - ζ)) := by
    intro ζ hζ
    have h1 := hd1 ζ hζ
    rw [hMdef]
    dsimp only
    rw [show (-a) * ζ + a = a * (1 - ζ) by ring]
    field_simp
    ring
  have him : ∀ ζ ∈ unitDisc, σ * (a * M ζ + b).im = (1 - normSq ζ) / normSq (1 - ζ) := by
    intro ζ hζ
    rw [hMζ ζ hζ, Complex.im_ofReal_mul, ← mul_assoc, hσσ, one_mul, s02_cayley_im]
  have himg : M '' unitDisc = Ω := by
    ext w
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      rw [hΩ, him ζ hζ]
      have := s02_cayley_im_pos hζ
      rwa [s02_cayley_im] at this
    · intro hw
      rw [hΩ] at hw
      set c : ℂ := (σ : ℂ) * (a * w + b) with hc
      have hcim : 0 < c.im := by
        rw [hc, Complex.im_ofReal_mul]
        exact hw
      have hcI : c + I ≠ 0 := by
        intro h
        have := congrArg Complex.im h
        simp at this
        linarith
      set ζ : ℂ := (c - I) / (c + I) with hζdef
      have hζ : ζ ∈ unitDisc := by
        refine mem_ball_zero_iff.mpr ?_
        rw [hζdef, norm_div, div_lt_one (norm_pos_iff.mpr hcI)]
        refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
          Complex.normSq_apply]
        simp
        nlinarith
      refine ⟨ζ, hζ, ?_⟩
      have e1 : 1 + ζ = 2 * c / (c + I) := by
        rw [hζdef]
        field_simp
        ring
      have e2 : 1 - ζ = 2 * I / (c + I) := by
        rw [hζdef]
        field_simp
        ring
      have hC : I * (1 + ζ) / (1 - ζ) = c := by
        rw [e1, e2]
        field_simp
      have key := hMζ ζ hζ
      rw [hC, hc, ← mul_assoc, ← ofReal_mul, hσσ, ofReal_one, one_mul] at key
      exact mul_left_cancel₀ ha (add_right_cancel key)
  have hid : IsConformalOnto (id : ℂ → ℂ) unitDisc unitDisc :=
    ⟨differentiableOn_id, injOn_id _, image_id _⟩
  have hdet : ((σ : ℂ) * I + b) * a - ((σ : ℂ) * I - b) * (-a) ≠ 0 := by
    rw [show ((σ : ℂ) * I + b) * a - ((σ : ℂ) * I - b) * (-a) = 2 * (σ : ℂ) * I * a by ring]
    have hσ0 : (σ : ℂ) ≠ 0 := by
      rw [ne_eq, ofReal_eq_zero]
      intro h
      rw [h] at hσσ
      norm_num at hσσ
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hσ0) I_ne_zero) ha
  have hl𝔻 : ∀ ζ ∈ unitDisc, poincareDensity unitDisc ζ = 2 / (1 - ‖ζ‖ ^ 2) := by
    intro ζ hζ
    have := eq_lambda_f hid hζ
    rw [deriv_id, norm_one, mul_one] at this
    exact this
  have hs𝔻 : ∀ ζ ∈ unitDisc, schwarzNorm unitDisc ζ = 0 := by
    intro ζ hζ
    have h0 : schwarzian (id : ℂ → ℂ) ζ = 0 := by
      have := schwarzian_mobius (a := 1) (b := 0) (c := 0) (d := 1) (by norm_num) ζ
      have hfun : (fun w : ℂ => (1 * w + 0) / (0 * w + 1)) = id := by
        funext w
        simp
      rwa [hfun] at this
    calc schwarzNorm unitDisc ζ = schwarzNorm unitDisc (id ζ) := rfl
      _ = ‖schwarzian id ζ‖ * (1 - ‖ζ‖ ^ 2) ^ 2 / 4 := eq_s_disk hid hζ
      _ = 0 := by rw [h0]; simp
  have hnat : ∀ ζ ∈ unitDisc,
      poincareDensity (M '' unitDisc) (M ζ) *
          ‖(((σ : ℂ) * I + b) * a - ((σ : ℂ) * I - b) * (-a)) / ((-a) * ζ + a) ^ 2‖ =
        poincareDensity unitDisc ζ ∧
      schwarzNorm (M '' unitDisc) (M ζ) = schwarzNorm unitDisc ζ :=
    fun ζ hζ => s02_mobius_natural (Ω := unitDisc) ⟨id, hid⟩ hdet hden hζ
  constructor
  · intro w hw
    rw [← himg] at hw ⊢
    obtain ⟨ζ, hζ, rfl⟩ := hw
    rw [(hnat ζ hζ).2, hs𝔻 ζ hζ]
  · intro w hw
    rw [← himg] at hw ⊢
    obtain ⟨ζ, hζ, rfl⟩ := hw
    have h1 := (hnat ζ hζ).1
    rw [hl𝔻 ζ hζ] at h1
    have hz1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
    have hpos : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
    have h1z : 0 < ‖1 - ζ‖ := norm_pos_iff.mpr (hd1 ζ hζ)
    have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hn : ‖(((σ : ℂ) * I + b) * a - ((σ : ℂ) * I - b) * (-a)) / ((-a) * ζ + a) ^ 2‖ =
        2 / (‖a‖ * ‖1 - ζ‖ ^ 2) := by
      rw [show ((σ : ℂ) * I + b) * a - ((σ : ℂ) * I - b) * (-a) = 2 * (σ : ℂ) * I * a by ring,
        show (-a) * ζ + a = a * (1 - ζ) by ring, norm_div, norm_pow, norm_mul, norm_mul,
        norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, hσabs]
      norm_num
      field_simp
    rw [hn] at h1
    rw [him ζ hζ, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    field_simp at h1 ⊢
    linarith

/-- `curvMass Ω = 0` when `s ≡ 0` on a measurable `Ω`. -/
theorem s02_curvMass_eq_zero (Ω : Set ℂ) (hm : MeasurableSet Ω)
    (h0 : ∀ w ∈ Ω, schwarzNorm Ω w = 0) : curvMass Ω = 0 := by
  unfold curvMass
  rw [withDensity_congr_ae (g := 0) ?_, withDensity_zero]
  filter_upwards [ae_restrict_mem hm] with w hw
  rw [h0 w hw]
  simp

/-- For a line pair the horoball gap is empty. -/
theorem s02_line_gap_empty (a b : ℂ) (ha : a ≠ 0) :
    gap {z | 0 < (a * z + b).im} {z | (a * z + b).im < 0} = ∅ := by
  have hU := s02_halfplane a b ha 1 (Or.inl rfl) {z | 0 < (a * z + b).im} (fun z => by simp)
  have hL := s02_halfplane a b ha (-1) (Or.inr rfl) {z | (a * z + b).im < 0}
    (fun z => by
      show (a * z + b).im < 0 ↔ 0 < -1 * (a * z + b).im
      rw [neg_one_mul, neg_pos])
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  rw [eq_empty_iff_forall_notMem]
  intro q hq
  unfold gap at hq
  obtain ⟨hqU, hq2⟩ := hq
  apply hq2
  have hξ : 0 < q.2 := hqU
  have hξa : 0 < ‖a‖ * q.2 := mul_pos hna hξ
  by_cases hu : 0 ≤ (a * q.1 + b).im
  · refine Or.inl ?_
    set w : ℂ := q.1 + I * ((‖a‖ * q.2 : ℝ) : ℂ) / a with hwdef
    have haw : a * w + b = (a * q.1 + b) + I * ((‖a‖ * q.2 : ℝ) : ℂ) := by
      rw [hwdef]
      field_simp
      ring
    have hwim : (a * w + b).im = (a * q.1 + b).im + ‖a‖ * q.2 := by
      rw [haw]
      simp
    have hw : w ∈ {z : ℂ | 0 < (a * z + b).im} := by
      show 0 < (a * w + b).im
      rw [hwim]
      linarith
    have hdist : ‖q.1 - w‖ = q.2 := by
      rw [hwdef, show q.1 - (q.1 + I * ((‖a‖ * q.2 : ℝ) : ℂ) / a) =
        -(I * ((‖a‖ * q.2 : ℝ) : ℂ) / a) by ring, norm_neg, norm_div, norm_mul,
        Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξa]
      field_simp
    have hl := hU.2 w hw
    rw [hwim, one_mul] at hl
    refine mem_iUnion₂.mpr ⟨w, hw, hqU, ?_⟩
    show horoPhi _ q w ≤ 1
    unfold horoPhi
    rw [hdist]
    set ℓ := poincareDensity {z : ℂ | 0 < (a * z + b).im} w
    have hℓ : 0 < ℓ := pos_of_mul_pos_left (hl ▸ hna) (by linarith)
    have h3 : ‖a‖ * (ℓ * q.2) ≤ ‖a‖ * 1 := by nlinarith [mul_nonneg hℓ.le hu]
    have hℓξ := le_of_mul_le_mul_left h3 hna
    rw [div_le_one (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hℓξ (by positivity : (0 : ℝ) ≤ 2 * q.2)]
  · refine Or.inr ?_
    push Not at hu
    set w : ℂ := q.1 - I * ((‖a‖ * q.2 : ℝ) : ℂ) / a with hwdef
    have haw : a * w + b = (a * q.1 + b) - I * ((‖a‖ * q.2 : ℝ) : ℂ) := by
      rw [hwdef]
      field_simp
      ring
    have hwim : (a * w + b).im = (a * q.1 + b).im - ‖a‖ * q.2 := by
      rw [haw]
      simp
    have hw : w ∈ {z : ℂ | (a * z + b).im < 0} := by
      show (a * w + b).im < 0
      rw [hwim]
      linarith
    have hdist : ‖q.1 - w‖ = q.2 := by
      rw [hwdef, show q.1 - (q.1 - I * ((‖a‖ * q.2 : ℝ) : ℂ) / a) =
        I * ((‖a‖ * q.2 : ℝ) : ℂ) / a by ring, norm_div, norm_mul,
        Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξa]
      field_simp
    have hl := hL.2 w hw
    rw [hwim] at hl
    refine mem_iUnion₂.mpr ⟨w, hw, hqU, ?_⟩
    show horoPhi _ q w ≤ 1
    unfold horoPhi
    rw [hdist]
    set ℓ := poincareDensity {z : ℂ | (a * z + b).im < 0} w
    have hℓ : 0 < ℓ := pos_of_mul_pos_left (hl ▸ hna) (by linarith)
    have h3 : ‖a‖ * (ℓ * q.2) ≤ ‖a‖ * 1 := by nlinarith [mul_nonneg hℓ.le (neg_nonneg.mpr hu.le)]
    have hℓξ := le_of_mul_le_mul_left h3 hna
    rw [div_le_one (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hℓξ (by positivity : (0 : ℝ) ≤ 2 * q.2)]

/-- Definition 2.11 `def:intrinsic`, `sec02-prelim.tex:527`: for a circle all four intrinsic
quantities (and the ambient ones) vanish; in this formalization this is a consequence of `s ≡ 0`
and `𝒩 = ∅`, not a separate case. -/
theorem def_intrinsic_circle {Ω Ωs : Set ℂ} (hl : IsLinePair Ω Ωs) (lab : ℂ × ℝ → ℂ) (p : ℂ)
    (P : ℂ × ℝ) :
    KH Ω p = 0 ∧ Kst Ω Ωs lab p = 0 ∧ KH2 Ω Ωs lab p = 0 ∧ KV Ω Ωs lab p = 0 ∧
      ambV Ω Ωs P = 0 ∧ ambH Ω Ωs P = 0 := by
  obtain ⟨a, b, ha, rfl, rfl⟩ := hl
  have hU := s02_halfplane a b ha 1 (Or.inl rfl) {z | 0 < (a * z + b).im} (fun z => by simp)
  have hL := s02_halfplane a b ha (-1) (Or.inr rfl) {z | (a * z + b).im < 0}
    (fun z => by
      show (a * z + b).im < 0 ↔ 0 < -1 * (a * z + b).im
      rw [neg_one_mul, neg_pos])
  have hmU : MeasurableSet {z : ℂ | 0 < (a * z + b).im} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hmL : MeasurableSet {z : ℂ | (a * z + b).im < 0} :=
    measurableSet_lt (by fun_prop) measurable_const
  have h1 := s02_curvMass_eq_zero _ hmU hU.1
  have h2 := s02_curvMass_eq_zero _ hmL hL.1
  have h3 := s02_line_gap_empty a b ha
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold KH
    rw [h1, lintegral_zero_measure]
  · unfold Kst
    rw [h2, lintegral_zero_measure]
  · unfold KH2 KH Kst
    rw [h1, h2, lintegral_zero_measure, lintegral_zero_measure, add_zero]
  · unfold KV
    rw [h3, Measure.restrict_empty, lintegral_zero_measure]
  · unfold ambV
    rw [h3, Measure.restrict_empty, lintegral_zero_measure]
  · unfold ambH
    rw [h1, h2, lintegral_zero_measure, lintegral_zero_measure, add_zero]

/-- (2.17) `eq:kernel-lip`, first part, `sec02-prelim.tex:542`: `|∇_ρ log k_p| ≤ 1`. -/
theorem eq_kernel_lip_a {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {p w : ℂ}
    (hp : p ∈ Ω) (hw : w ∈ Ω) :
    DifferentiableAt ℝ (fun x => Real.log (intrKernel Ω p x)) w ∧
      ∀ v : ℂ, |fderiv ℝ (fun x => Real.log (intrKernel Ω p x)) w v| ≤
        poincareDensity Ω w * ‖v‖ := by
  obtain ⟨f, hf⟩ := hΩ
  set ψ := Function.invFunOn f unitDisc with hψdef
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hψ : IsConformalOnto ψ Ω unitDisc := hf.symm isOpen_ball
  have hψU : ∀ x ∈ Ω, ψ x ∈ unitDisc := by
    intro x hx
    have hmem := mem_image_of_mem ψ hx
    rw [hψ.2.2] at hmem
    exact hmem
  have hfψ : ∀ x ∈ Ω, f (ψ x) = x := by
    intro x hx
    have hmem : x ∈ f '' unitDisc := by rw [hf.2.2]; exact hx
    exact Function.invFunOn_eq hmem
  set a := ψ p with hadef
  have ha : a ∈ unitDisc := hψU p hp
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have hfa : f a = p := hfψ p hp
  have hw1 : ‖ψ w‖ < 1 := mem_ball_zero_iff.mp (hψU w hw)
  have hψA : AnalyticAt ℂ ψ w := hψ.1.analyticAt (hΩo.mem_nhds hw)
  have hψd := hψA.differentiableAt.hasDerivAt
  have hD : (1 : ℂ) - conj a * ψ w ≠ 0 := blaschke_den_ne_zero ha1 hw1
  have hhd : HasDerivAt (fun x => 1 - conj a * ψ x) (-(conj a * deriv ψ w)) w := by
    simpa using (hψd.const_mul (conj a)).const_sub 1
  obtain ⟨L2, h2, h2v⟩ := s02_hasFDerivAt_log_one_sub_normSq hψd hw1
  obtain ⟨L3, h3, h3v⟩ := s02_hasFDerivAt_log_normSq hhd hD
  have hG : HasFDerivAt (fun x => Real.log (1 - ‖a‖ ^ 2) + Real.log (1 - ‖ψ x‖ ^ 2) -
      Real.log (‖1 - conj a * ψ x‖ ^ 2)) (L2 - L3) w :=
    (h2.const_add _).sub h3
  -- `log k_p` agrees with `G` on `Ω` (2.19)
  have heq : (fun x => Real.log (intrKernel Ω p x)) =ᶠ[𝓝 w]
      fun x => Real.log (1 - ‖a‖ ^ 2) + Real.log (1 - ‖ψ x‖ ^ 2) -
        Real.log (‖1 - conj a * ψ x‖ ^ 2) := by
    filter_upwards [hΩo.mem_nhds hw] with x hx
    have hx1 : ‖ψ x‖ < 1 := mem_ball_zero_iff.mp (hψU x hx)
    have hDx : (1 : ℂ) - conj a * ψ x ≠ 0 := blaschke_den_ne_zero ha1 hx1
    have hra : (0 : ℝ) < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
    have hrx : (0 : ℝ) < 1 - ‖ψ x‖ ^ 2 := by nlinarith [norm_nonneg (ψ x)]
    have hk := s02_intrKernel_eq hf ha (hψU x hx)
    rw [hfa, hfψ x hx] at hk
    rw [hk, Real.log_div (by positivity) (by positivity), Real.log_mul hra.ne' hrx.ne']
  have hK := hG.congr_of_eventuallyEq heq
  refine ⟨hK.differentiableAt, fun v => ?_⟩
  -- the derivative is `v ↦ Re(c v)` with `c = 2ψ'(ā - ψ̄)/((1-|ψ|²)(1-āψ))`
  set R : ℂ := ((1 - ‖ψ w‖ ^ 2 : ℝ) : ℂ) with hRdef
  have hr : (0 : ℝ) < 1 - ‖ψ w‖ ^ 2 := by nlinarith [norm_nonneg (ψ w)]
  have hR : R = 1 - conj (ψ w) * ψ w := by
    rw [hRdef, Complex.conj_mul']
    push_cast
    ring
  have hR0 : (1 : ℂ) - conj (ψ w) * ψ w ≠ 0 := by
    rw [← hR, hRdef]
    exact_mod_cast hr.ne'
  have hLv : (L2 - L3) v =
      (2 * deriv ψ w * conj (a - ψ w) / (R * (1 - conj a * ψ w)) * v).re := by
    rw [ContinuousLinearMap.sub_apply, h2v, h3v, ← Complex.sub_re]
    congr 1
    rw [hR, map_sub]
    have hD' : (1 : ℂ) - ψ w * conj a ≠ 0 := by rw [mul_comm]; exact hD
    have hR0' : (1 : ℂ) - ψ w * conj (ψ w) ≠ 0 := by rw [mul_comm]; exact hR0
    field_simp
    ring
  rw [hK.fderiv, hLv]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
  -- `|ā - ψ̄| ≤ |1 - āψ|` and `λ = 2|ψ'|/(1-|ψ|²)` (I1)
  have hle : ‖a - ψ w‖ ≤ ‖1 - conj a * ψ w‖ := by
    have hkey := normSq_blaschke_key a (ψ w)
    have hna : normSq a < 1 := normSq_lt_one_iff.mpr ha1
    have hnw : normSq (ψ w) < 1 := normSq_lt_one_iff.mpr hw1
    have hsq : ‖a - ψ w‖ ^ 2 ≤ ‖1 - conj a * ψ w‖ ^ 2 := by
      rw [norm_sub_rev, Complex.sq_norm, Complex.sq_norm]
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq
  have hDn : 0 < ‖1 - conj a * ψ w‖ := norm_pos_iff.mpr hD
  rw [s02_poincareDensity_eq_inv hf hw, ← hψdef, norm_div, norm_mul, norm_mul, norm_mul,
    RCLike.norm_conj, hRdef, Complex.norm_real, Real.norm_of_nonneg hr.le, Complex.norm_two,
    div_le_div_iff₀ (by positivity) hr]
  have h0 : 0 ≤ 2 * ‖deriv ψ w‖ * (1 - ‖ψ w‖ ^ 2) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hle h0]

/-- (2.17) `eq:kernel-lip`, second part, `sec02-prelim.tex:543`:
`k_p(w) ≤ e^{d_ρ(w,w')} k_p(w')`. -/
theorem eq_kernel_lip_b {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    {p w w' : ℂ} (hp : p ∈ Ω) (hw : w ∈ Ω) (hw' : w' ∈ Ω) :
    intrKernel Ω p w ≤ Real.exp (poincareDist Ω w w') * intrKernel Ω p w' := by
  unfold intrKernel
  exact s02_sech_sq_le (s02_poincareDist_nonneg hΩ hp hw) (s02_poincareDist_nonneg hΩ hp hw')
    (s02_poincareDist_nonneg hΩ hw hw') (s02_poincareDist_triangle hΩ hp hw hw')

/-- (2.17) `eq:kernel-lip`, third part, `sec02-prelim.tex:544`:
`k_p(w) ≤ e^{d_ρ(p,p')} k_{p'}(w)`. -/
theorem eq_kernel_lip_c {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    {p p' w : ℂ} (hp : p ∈ Ω) (hp' : p' ∈ Ω) (hw : w ∈ Ω) :
    intrKernel Ω p w ≤ Real.exp (poincareDist Ω p p') * intrKernel Ω p' w := by
  unfold intrKernel
  refine s02_sech_sq_le (s02_poincareDist_nonneg hΩ hp hw) (s02_poincareDist_nonneg hΩ hp' hw)
    (s02_poincareDist_nonneg hΩ hp hp') ?_
  have h := s02_poincareDist_triangle hΩ hp' hp hw
  rw [s02_poincareDist_comm hΩ hp' hp] at h
  linarith

/-- (2.18) `eq:kernel-exp`, `sec02-prelim.tex:547`: `e^{-r} ≤ sech²(r/2) ≤ 4 e^{-r}` (`r ≥ 0`). -/
theorem eq_kernel_exp {r : ℝ} (hr : 0 ≤ r) :
    Real.exp (-r) ≤ ((Real.cosh (r / 2))⁻¹) ^ 2 ∧
      ((Real.cosh (r / 2))⁻¹) ^ 2 ≤ 4 * Real.exp (-r) := by
  set y := Real.exp (r / 2) with hydef
  have hy : 1 ≤ y := Real.one_le_exp (by linarith)
  have hy0 : 0 < y := by linarith
  have hy2 : 1 ≤ y ^ 2 := one_le_pow₀ hy
  have e1 : Real.exp (-r) = 1 / y ^ 2 := by
    rw [sq, hydef, ← Real.exp_add, add_halves, Real.exp_neg, one_div]
  have e2 : (Real.cosh (r / 2))⁻¹ = 2 * y / (y ^ 2 + 1) := by
    rw [Real.cosh_eq, Real.exp_neg, ← hydef]
    field_simp
  rw [e1, e2, div_pow]
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 3 * y ^ 2 + 1) (sub_nonneg.2 hy2)]
  · rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg y, sq_nonneg (y ^ 2)]

/-- (2.19) `eq:kernel-disk`, `sec02-prelim.tex:551`:
`k_{f(a)}(f(z)) = (1-|a|²)(1-|z|²)/|1 - ā z|²`. -/
theorem eq_kernel_disk {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {a z : ℂ}
    (ha : a ∈ unitDisc) (hz : z ∈ unitDisc) :
    intrKernel Ω (f a) (f z) = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖1 - conj a * z‖ ^ 2 := by
  exact s02_intrKernel_eq hf ha hz

/-! ## §2.9 Carleson measures, BMO and VMO quasicircles -/

/-- Carleson helper: a Carleson measure gives `𝔻` finite mass (`𝔻 ⊆ D(1, 3/2) ∪ D(-1, 3/2)`). -/
theorem s02_cm_total {μ : Measure ℂ} (h : IsCarlesonDisk μ) : μ unitDisc ≠ ⊤ := by
  obtain ⟨C, hC, h⟩ := h
  have hsub : unitDisc ⊆ (unitDisc ∩ ball 1 (3 / 2)) ∪ (unitDisc ∩ ball (-1) (3 / 2)) := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    by_contra hc
    simp only [mem_union, mem_inter_iff, mem_ball, not_or, not_and, not_lt] at hc
    have h1 := hc.1 hz
    have h2 := hc.2 hz
    rw [dist_eq_norm] at h1 h2
    have e : ‖z - 1‖ ^ 2 + ‖z - -1‖ ^ 2 = 2 * ‖z‖ ^ 2 + 2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im]
      ring
    nlinarith [norm_nonneg z, mul_le_mul h1 h1 (by norm_num) (norm_nonneg _),
      mul_le_mul h2 h2 (by norm_num) (norm_nonneg _)]
  have hb : ∀ ζ ∈ sphere (0 : ℂ) 1, μ (unitDisc ∩ ball ζ (3 / 2)) ≠ ⊤ := fun ζ hζ =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top)
      (h ζ hζ (3 / 2) (by norm_num) (by norm_num))
  exact ne_top_of_le_ne_top
    (ENNReal.add_ne_top.2 ⟨hb 1 (by simp), hb (-1) (by simp)⟩)
    ((measure_mono hsub).trans (measure_union_le _ _))

/-- Shen–Wei helper (S0, `log f'`): for `f` conformal on `𝔻`, `φ' = f''/f'` is holomorphic on `𝔻`
and `S f = (φ')' − ½ φ'²` there. -/
theorem s02_sw_logDeriv {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) :
    DifferentiableOn ℂ (fun z => deriv (deriv f) z / deriv f z) unitDisc ∧
      ∀ z ∈ unitDisc, schwarzian f z =
        deriv (fun w => deriv (deriv f) w / deriv f w) z -
          1 / 2 * (deriv (deriv f) z / deriv f z) ^ 2 := by
  have han : AnalyticOnNhd ℂ f unitDisc := hf.1.analyticOnNhd isOpen_ball
  refine ⟨?_, fun z hz => ?_⟩
  · exact han.deriv.deriv.differentiableOn.div han.deriv.differentiableOn
      fun z hz => deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz
  · rw [schwarzian_of_analyticAt (han z hz)]
    rfl

/-- Shen–Wei helper (S0a, Bloch bound): `(1-|z|²)|f''/f'| ≤ 6` for univalent `f` on `𝔻`
(from `kb_koebe_transform_ineq`). -/
theorem s02_sw_bloch {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {z : ℂ}
    (hz : z ∈ unitDisc) :
    (1 - ‖z‖ ^ 2) * ‖deriv (deriv f) z / deriv f z‖ ≤ 6 := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have h := kb_koebe_transform_ineq hf.1 hf.2.1 hz
  have h1 := norm_sub_norm_le (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * deriv (deriv f) z / deriv f z)
    (2 * conj z)
  have h2 : ‖(2 : ℂ) * conj z‖ = 2 * ‖z‖ := by simp
  rw [mul_div_assoc, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by nlinarith [norm_nonneg z]), h2] at h1
  rw [mul_div_assoc] at h
  linarith

/-- Shen–Wei helper (S0b, area sub-mean value): `|g(z)|² π ρ² ≤ ∫_{D(z,ρ)} |g|² dA` for `g`
holomorphic on the closed disc. -/
theorem s02_sw_meanValue {g : ℂ → ℂ} {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : DifferentiableOn ℂ g (closedBall z ρ)) :
    ENNReal.ofReal (‖g z‖ ^ 2) * ENNReal.ofReal (π * ρ ^ 2) ≤
      ∫⁻ w in ball z ρ, ENNReal.ofReal (‖g w‖ ^ 2) := by
  classical
  have hgc : ContinuousOn g (closedBall z ρ) := hg.continuousOn
  obtain ⟨h, hh⟩ : ∃ h : ℂ → ℝ≥0∞,
      h = (ball z ρ).indicator fun w => ENNReal.ofReal (‖g w‖ ^ 2) := ⟨_, rfl⟩
  have hmeas : Measurable h := by
    rw [hh, ← Set.piecewise_eq_indicator]
    exact ContinuousOn.measurable_piecewise
      (ENNReal.continuous_ofReal.comp_continuousOn
        ((hgc.mono ball_subset_closedBall).norm.pow 2))
      continuousOn_const measurableSet_ball
  have hps : Continuous fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  -- on each circle of radius `r < ρ`: `2π |g z|² ≤ ∫ |g|²` (mean value for `g²`)
  have hpt : ∀ r ∈ Ioo 0 ρ, ENNReal.ofReal (2 * π * ‖g z‖ ^ 2) ≤
      ∫⁻ θ in Ioo (-π) π, h (z + circleMap 0 r θ) := by
    intro r hr
    have hr0 : 0 < r := hr.1
    have hsub : closedBall z r ⊆ closedBall z ρ := closedBall_subset_closedBall hr.2.le
    have hc : Continuous fun θ => g (circleMap z r θ) :=
      hgc.comp_continuous (continuous_circleMap z r) fun θ =>
        hsub (sphere_subset_closedBall (circleMap_mem_sphere z hr0.le θ))
    have hcm : ∀ θ, z + circleMap 0 r θ = circleMap z r θ := fun θ => by simp [circleMap]
    have hin : ∀ θ, h (z + circleMap 0 r θ) = ENNReal.ofReal (‖g (circleMap z r θ)‖ ^ 2) := by
      intro θ
      rw [hh, hcm, Set.indicator_of_mem]
      rw [mem_ball, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr0]
      exact hr.2
    simp_rw [hin]
    have hmv : Real.circleAverage (fun w => g w ^ 2) z r = g z ^ 2 := by
      apply DiffContOnCl.circleAverage
      apply DifferentiableOn.diffContOnCl
      rw [abs_of_pos hr0, closure_ball z hr0.ne']
      exact (hg.pow 2).mono hsub
    rw [Real.circleAverage_def] at hmv
    have hI : ∫ θ in (0 : ℝ)..2 * π, g (circleMap z r θ) ^ 2 = (2 * π : ℝ) • g z ^ 2 := by
      rw [← hmv, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
    have hper : Function.Periodic (fun θ => ‖g (circleMap z r θ)‖ ^ 2) (2 * π) :=
      fun θ => by simp [periodic_circleMap z r θ]
    have hint : ∫ θ in (-π)..π, ‖g (circleMap z r θ)‖ ^ 2 =
        ∫ θ in (0 : ℝ)..2 * π, ‖g (circleMap z r θ)‖ ^ 2 := by
      have := hper.intervalIntegral_add_eq (-π) 0
      rw [zero_add] at this
      rw [← this]
      congr 1
      ring
    have hle : 2 * π * ‖g z‖ ^ 2 ≤ ∫ θ in (-π)..π, ‖g (circleMap z r θ)‖ ^ 2 := by
      rw [hint]
      have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
        (f := fun θ => g (circleMap z r θ) ^ 2) (by positivity : (0 : ℝ) ≤ 2 * π)
      simp only [norm_pow] at h1
      rw [hI, norm_smul, Real.norm_of_nonneg (by positivity), norm_pow] at h1
      exact h1
    have hIi : IntegrableOn (fun θ => ‖g (circleMap z r θ)‖ ^ 2) (Ioo (-π) π) :=
      ((hc.norm.pow 2).integrableOn_Icc).mono_set Ioo_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hIi (ae_of_all _ fun θ => sq_nonneg _),
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    exact ENNReal.ofReal_le_ofReal hle
  have hid : ∫ r in (0 : ℝ)..ρ, r = ρ ^ 2 / 2 := by
    rw [integral_id]
    ring
  have hr : ∫⁻ r in Ioo (0 : ℝ) ρ, ENNReal.ofReal r = ENNReal.ofReal (ρ ^ 2 / 2) := by
    rw [← hid, intervalIntegral.integral_of_le hρ.le, integral_Ioc_eq_integral_Ioo,
      ofReal_integral_eq_lintegral_ofReal]
    · exact (continuous_id.integrableOn_Icc (a := (0 : ℝ)) (b := ρ)).mono_set Ioo_subset_Icc_self
    · exact (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun r hr => hr.1.le)
  have hbase : ENNReal.ofReal (‖g z‖ ^ 2) * ENNReal.ofReal (π * ρ ^ 2) =
      ∫⁻ r in Ioo 0 ρ, ENNReal.ofReal r * ENNReal.ofReal (2 * π * ‖g z‖ ^ 2) := by
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hr,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  calc ENNReal.ofReal (‖g z‖ ^ 2) * ENNReal.ofReal (π * ρ ^ 2)
      = ∫⁻ r in Ioo 0 ρ, ENNReal.ofReal r * ENNReal.ofReal (2 * π * ‖g z‖ ^ 2) := hbase
    _ ≤ ∫⁻ r in Ioo 0 ρ, ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal r * h (z + circleMap 0 r θ) := by
        refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact mul_le_mul_right (hpt r hr) _
    _ ≤ ∫⁻ r in Ioi 0, ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal r * h (z + circleMap 0 r θ) :=
        lintegral_mono_set Ioo_subset_Ioi_self
    _ = ∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 • h (z + Complex.polarCoord.symm p) := by
        rw [Complex.polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
          lintegral_prod _ ?_]
        · simp only [smul_eq_mul, kn_polar_symm_eq]
        · exact (measurable_fst.ennreal_ofReal.smul
            (hmeas.comp (measurable_const.add hps.measurable))).aemeasurable
    _ = ∫⁻ u, h (z + u) := Complex.lintegral_comp_polarCoord_symm fun u => h (z + u)
    _ = ∫⁻ w, h w := lintegral_add_left_eq_self h z
    _ = ∫⁻ w in ball z ρ, ENNReal.ofReal (‖g w‖ ^ 2) := by
        rw [hh, lintegral_indicator measurableSet_ball]

/-- Shen–Wei helper (S0c, L² Cauchy estimate): `|g'(z)|² ρ⁴ ≤ (16/π) ∫_{D(z,ρ)} |g|² dA`
(Cauchy at radius `ρ/2`, then S0b on the discs `D(w, ρ/2)`, `|w - z| = ρ/2`). -/
theorem s02_sw_cauchy {g : ℂ → ℂ} {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : DifferentiableOn ℂ g (closedBall z ρ)) :
    ENNReal.ofReal (‖deriv g z‖ ^ 2 * ρ ^ 4) ≤
      ENNReal.ofReal (16 / π) * ∫⁻ w in ball z ρ, ENNReal.ofReal (‖g w‖ ^ 2) := by
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ≥0∞, I = ∫⁻ w in ball z ρ, ENNReal.ofReal (‖g w‖ ^ 2) :=
    ⟨_, rfl⟩
  rw [← hIdef]
  rcases eq_or_ne I ⊤ with hI | hI
  · rw [hI, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
    exact le_top
  have hρ2 : 0 < ρ / 2 := half_pos hρ
  have hX : 0 ≤ 4 * I.toReal / (π * ρ ^ 2) := by positivity
  have hM : ∀ w ∈ sphere z (ρ / 2), ‖g w‖ ≤ Real.sqrt (4 * I.toReal / (π * ρ ^ 2)) := by
    intro w hw
    have hwz : dist w z = ρ / 2 := mem_sphere.mp hw
    have hsub : closedBall w (ρ / 2) ⊆ closedBall z ρ :=
      closedBall_subset_closedBall' (by rw [hwz]; linarith)
    have hsub' : ball w (ρ / 2) ⊆ ball z ρ := ball_subset_ball' (by rw [hwz]; linarith)
    have h1 := (s02_sw_meanValue hρ2 (hg.mono hsub)).trans (lintegral_mono_set hsub')
    rw [← hIdef, ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_toReal hI,
      ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg] at h1
    rw [Real.le_sqrt (norm_nonneg _) hX, le_div_iff₀ (by positivity)]
    nlinarith [h1]
  have hdc : DiffContOnCl ℂ g (ball z (ρ / 2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z hρ2.ne']
    exact hg.mono (closedBall_subset_closedBall (by linarith))
  have hcd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ2 hdc hM
  rw [le_div_iff₀ hρ2] at hcd
  have hsq := pow_le_pow_left₀ (by positivity) hcd 2
  rw [Real.sq_sqrt hX, le_div_iff₀ (by positivity)] at hsq
  rw [← ENNReal.ofReal_toReal hI, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
  nlinarith [hsq]

/-- Shen–Wei helper (S0d, Whitney–Tonelli): averaging over the Whitney discs
`W(z) = D(z, (1-|z|)/2)` of the points of a box costs a factor `9π/4 ≤ 8` and doubles the box:
if `w ∈ W(z)` then `(2/3)(1-|w|) < 1-|z| < 2(1-|w|)` and `|z - w| < 1-|w|`. -/
theorem s02_sw_whitney {F : ℂ → ℝ≥0∞} (hF : Measurable F) {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) *
        ∫⁻ w in ball z ((1 - ‖z‖) / 2), F w) ≤
      ENNReal.ofReal 8 * ∫⁻ w in unitDisc ∩ ball ζ (2 * r), F w := by
  -- `hr` is not needed: for `r ≤ 0` both boxes are empty and the bound is trivial.
  have _hr := hr
  have hBm : MeasurableSet (unitDisc ∩ ball ζ r) := measurableSet_ball.inter measurableSet_ball
  have hB'm : MeasurableSet (unitDisc ∩ ball ζ (2 * r)) :=
    measurableSet_ball.inter measurableSet_ball
  have hζ1 : ‖ζ‖ = 1 := by simpa using hζ
  obtain ⟨S, hS⟩ : ∃ S : Set (ℂ × ℂ), S = {p | dist p.2 p.1 < (1 - ‖p.1‖) / 2} := ⟨_, rfl⟩
  have hmemS : ∀ z w, (z, w) ∈ S ↔ dist w z < (1 - ‖z‖) / 2 := by
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
  have heq : ∀ z, ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) * ∫⁻ w in ball z ((1 - ‖z‖) / 2), F w =
      ∫⁻ w, ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) * S.indicator (fun q => F q.2) (z, w) := by
    intro z
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun w => ?_
    by_cases hw : (z, w) ∈ S
    · rw [Set.indicator_of_mem hw,
        Set.indicator_of_mem (show w ∈ ball z ((1 - ‖z‖) / 2) from (hmemS z w).1 hw)]
    · rw [Set.indicator_of_notMem hw, mul_zero,
        Set.indicator_of_notMem (show w ∉ ball z ((1 - ‖z‖) / 2) from fun h => hw ((hmemS z w).2 h))]
  -- for fixed `w`, the `z`-integral is at most `8 F(w) 1_{B(ζ,2r)}(w)`
  have hpw : ∀ w, (∫⁻ z in unitDisc ∩ ball ζ r,
      ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) * S.indicator (fun q => F q.2) (z, w)) ≤
        (unitDisc ∩ ball ζ (2 * r)).indicator (fun w => ENNReal.ofReal 8 * F w) w := by
    intro w
    by_cases hw : w ∈ unitDisc ∩ ball ζ (2 * r)
    · rw [Set.indicator_of_mem hw]
      have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw.1
      obtain ⟨v, hv⟩ : ∃ v : ℝ, v = 1 - ‖w‖ := ⟨_, rfl⟩
      have hv0 : 0 < v := by linarith
      have hvol : volume (ball w v) = ENNReal.ofReal (v ^ 2 * π) := by
        rw [Complex.volume_ball, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hv0.le,
          ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
      calc (∫⁻ z in unitDisc ∩ ball ζ r,
            ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) * S.indicator (fun q => F q.2) (z, w))
          ≤ ∫⁻ z in unitDisc ∩ ball ζ r,
              (ball w v).indicator (fun _ => ENNReal.ofReal (9 / 4 * (v ^ 2)⁻¹) * F w) z := by
            refine setLIntegral_mono' hBm fun z hz => ?_
            by_cases hzw : (z, w) ∈ S
            · have hd := (hmemS z w).1 hzw
              have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz.1
              rw [dist_eq_norm] at hd
              have t1 := norm_sub_norm_le w z
              have t2 := norm_sub_norm_le z w
              rw [norm_sub_rev] at t2
              have hzv : z ∈ ball w v := by
                rw [mem_ball, dist_eq_norm, norm_sub_rev]
                linarith
              rw [Set.indicator_of_mem hzw, Set.indicator_of_mem hzv]
              refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
              have hu : 2 / 3 * v < 1 - ‖z‖ := by linarith
              have h49 : 4 / 9 * v ^ 2 ≤ (1 - ‖z‖) ^ 2 := by nlinarith
              calc ((1 - ‖z‖) ^ 2)⁻¹ ≤ (4 / 9 * v ^ 2)⁻¹ := inv_anti₀ (by positivity) h49
                _ = 9 / 4 * (v ^ 2)⁻¹ := by rw [mul_inv]; norm_num
            · rw [Set.indicator_of_notMem hzw, mul_zero]
              exact bot_le
        _ ≤ ∫⁻ z, (ball w v).indicator (fun _ => ENNReal.ofReal (9 / 4 * (v ^ 2)⁻¹) * F w) z :=
            setLIntegral_le_lintegral _ _
        _ = ENNReal.ofReal (9 / 4 * (v ^ 2)⁻¹) * F w * volume (ball w v) :=
            lintegral_indicator_const measurableSet_ball _
        _ ≤ ENNReal.ofReal 8 * F w := by
            rw [hvol, mul_right_comm, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 9 / 4 * (v ^ 2)⁻¹)]
            refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
            have e : 9 / 4 * (v ^ 2)⁻¹ * (v ^ 2 * π) = 9 / 4 * π := by field_simp
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
        ∫⁻ w in ball z ((1 - ‖z‖) / 2), F w)
      = ∫⁻ z in unitDisc ∩ ball ζ r, ∫⁻ w,
          ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) * S.indicator (fun q => F q.2) (z, w) :=
        setLIntegral_congr_fun hBm fun z _ => heq z
    _ = ∫⁻ w, ∫⁻ z in unitDisc ∩ ball ζ r,
          ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) * S.indicator (fun q => F q.2) (z, w) :=
        lintegral_lintegral_swap hG.aemeasurable
    _ ≤ ∫⁻ w, (unitDisc ∩ ball ζ (2 * r)).indicator (fun w => ENNReal.ofReal 8 * F w) w :=
        lintegral_mono fun w => hpw w
    _ = ENNReal.ofReal 8 * ∫⁻ w in unitDisc ∩ ball ζ (2 * r), F w := by
        rw [lintegral_indicator hB'm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Shen–Wei helper (S1, pointwise): with `φ' = f''/f'`,
`|Sf|²(1-|z|²)³ ≤ 2|φ''|²(1-|z|²)³ + ½|φ'|⁴(1-|z|²)³`; the first term is at most
`(8192/π)(1-|z|)⁻² ∫_{W(z)} |φ'|²(1-|w|²)` (S0c with `ρ = (1-|z|)/2`, `1-|w|² ≥ ρ` on `W(z)`),
the second at most `18 |φ'|²(1-|z|²)` (S0a). -/
theorem s02_sw_pt {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {z : ℂ}
    (hz : z ∈ unitDisc) :
    ENNReal.ofReal (‖schwarzian f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) ≤
      ENNReal.ofReal 3000 * (ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) *
          ∫⁻ w in ball z ((1 - ‖z‖) / 2),
            ENNReal.ofReal (‖deriv (deriv f) w / deriv f w‖ ^ 2 * (1 - ‖w‖ ^ 2))) +
        ENNReal.ofReal 18 *
          ENNReal.ofReal (‖deriv (deriv f) z / deriv f z‖ ^ 2 * (1 - ‖z‖ ^ 2)) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  obtain ⟨hφd, hS⟩ := s02_sw_logDeriv hf
  have hB := s02_sw_bloch hf hz
  have hSz := hS z hz
  set u := 1 - ‖z‖ with hu
  have hu0 : 0 < u := by linarith
  set ρ := u / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  set s := 1 - ‖z‖ ^ 2 with hs
  have hs0 : 0 ≤ s := by nlinarith [norm_nonneg z]
  have hs4 : s ≤ 4 * ρ := by nlinarith [norm_nonneg z]
  have hsub : closedBall z ρ ⊆ unitDisc := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have t := norm_sub_norm_le w z
    exact mem_ball_zero_iff.mpr (by linarith)
  have hC := s02_sw_cauchy hρ0 (hφd.mono hsub)
  beta_reduce at hC
  have hJ : (∫⁻ w in ball z ρ, ENNReal.ofReal (‖deriv (deriv f) w / deriv f w‖ ^ 2)) ≤
      ENNReal.ofReal ρ⁻¹ * ∫⁻ w in ball z ρ,
        ENNReal.ofReal (‖deriv (deriv f) w / deriv f w‖ ^ 2 * (1 - ‖w‖ ^ 2)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_ball fun w hw => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [mem_ball, dist_eq_norm] at hw
    have t := norm_sub_norm_le w z
    have hw1 : ‖w‖ < 1 - ρ := by linarith
    have h1 : ρ ≤ 1 - ‖w‖ ^ 2 := by
      nlinarith [norm_nonneg w, mul_nonneg (norm_nonneg w) (by linarith : 0 ≤ 1 - ‖w‖)]
    calc ‖deriv (deriv f) w / deriv f w‖ ^ 2
        = ρ⁻¹ * (‖deriv (deriv f) w / deriv f w‖ ^ 2 * ρ) := by field_simp
      _ ≤ ρ⁻¹ * (‖deriv (deriv f) w / deriv f w‖ ^ 2 * (1 - ‖w‖ ^ 2)) := by gcongr
  set J' := ∫⁻ w in ball z ρ,
    ENNReal.ofReal (‖deriv (deriv f) w / deriv f w‖ ^ 2 * (1 - ‖w‖ ^ 2)) with hJ'
  set A := deriv (fun w => deriv (deriv f) w / deriv f w) z with hA
  set P := deriv (deriv f) z / deriv f z with hP
  have hN : ‖schwarzian f z‖ ≤ ‖A‖ + 1 / 2 * ‖P‖ ^ 2 := by
    rw [hSz]
    calc ‖A - 1 / 2 * P ^ 2‖ ≤ ‖A‖ + ‖1 / 2 * P ^ 2‖ := norm_sub_le _ _
      _ = ‖A‖ + 1 / 2 * ‖P‖ ^ 2 := by simp [norm_pow]
  have hN2 : ‖schwarzian f z‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 + 1 / 2 * ‖P‖ ^ 4 := by
    nlinarith [norm_nonneg (schwarzian f z), norm_nonneg A, sq_nonneg (‖A‖ - 1 / 2 * ‖P‖ ^ 2)]
  have hT1 : ENNReal.ofReal (2 * ‖A‖ ^ 2 * s ^ 3) ≤
      ENNReal.ofReal 3000 * (ENNReal.ofReal ((u ^ 2)⁻¹) * J') := by
    calc ENNReal.ofReal (2 * ‖A‖ ^ 2 * s ^ 3)
        ≤ ENNReal.ofReal (128 * ρ⁻¹) * ENNReal.ofReal (‖A‖ ^ 2 * ρ ^ 4) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have h3 : s ^ 3 ≤ (4 * ρ) ^ 3 := pow_le_pow_left₀ hs0 hs4 3
          calc 2 * ‖A‖ ^ 2 * s ^ 3 ≤ 2 * ‖A‖ ^ 2 * (4 * ρ) ^ 3 := by gcongr
            _ = 128 * ρ⁻¹ * (‖A‖ ^ 2 * ρ ^ 4) := by field_simp; ring
      _ ≤ ENNReal.ofReal (128 * ρ⁻¹) * (ENNReal.ofReal (16 / π) * (ENNReal.ofReal ρ⁻¹ * J')) :=
          mul_le_mul_right (hC.trans (mul_le_mul_right hJ _)) _
      _ = ENNReal.ofReal (128 * ρ⁻¹) * ENNReal.ofReal (16 / π) * ENNReal.ofReal ρ⁻¹ * J' := by
          ring
      _ ≤ ENNReal.ofReal 3000 * ENNReal.ofReal ((u ^ 2)⁻¹) * J' := by
          refine mul_le_mul_left ?_ _
          rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 128 * ρ⁻¹),
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 128 * ρ⁻¹ * (16 / π)),
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3000)]
          apply ENNReal.ofReal_le_ofReal
          have e : 128 * ρ⁻¹ * (16 / π) * ρ⁻¹ = 8192 / π * (u ^ 2)⁻¹ := by
            rw [hρ]
            field_simp
            ring
          rw [e]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [div_le_iff₀ Real.pi_pos]
          nlinarith [Real.pi_gt_three]
      _ = ENNReal.ofReal 3000 * (ENNReal.ofReal ((u ^ 2)⁻¹) * J') := mul_assoc _ _ _
  have hT2 : ENNReal.ofReal (1 / 2 * ‖P‖ ^ 4 * s ^ 3) ≤
      ENNReal.ofReal 18 * ENNReal.ofReal (‖P‖ ^ 2 * s) := by
    rw [← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    have h0 : 0 ≤ s * ‖P‖ := by positivity
    have h36 : (s * ‖P‖) ^ 2 ≤ 36 := by nlinarith
    have e : 1 / 2 * ‖P‖ ^ 4 * s ^ 3 = 1 / 2 * (s * ‖P‖) ^ 2 * (‖P‖ ^ 2 * s) := by ring
    rw [e]
    have h2 : 0 ≤ ‖P‖ ^ 2 * s := by positivity
    nlinarith
  calc ENNReal.ofReal (‖schwarzian f z‖ ^ 2 * s ^ 3)
      ≤ ENNReal.ofReal (2 * ‖A‖ ^ 2 * s ^ 3 + 1 / 2 * ‖P‖ ^ 4 * s ^ 3) := by
        apply ENNReal.ofReal_le_ofReal
        have := mul_le_mul_of_nonneg_right hN2 (pow_nonneg hs0 3)
        linarith
    _ = ENNReal.ofReal (2 * ‖A‖ ^ 2 * s ^ 3) + ENNReal.ofReal (1 / 2 * ‖P‖ ^ 4 * s ^ 3) :=
        ENNReal.ofReal_add (by positivity) (by positivity)
    _ ≤ _ := add_le_add hT1 hT2

/-- Shen–Wei helper (S1, boxes): `‖Sf‖²(1-|z|²)³ dA(B(ζ,r)) ≤ 25000 · |φ'|²(1-|z|²) dA(B(ζ,2r))`
(`3000 · 8 + 18 ≤ 25000`). -/
theorem s02_sw_box {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {ζ : ℂ}
    (hζ : ζ ∈ sphere (0 : ℂ) 1) {r : ℝ} (hr : 0 < r) :
    schwarzCarlesonMeasure f (unitDisc ∩ ball ζ r) ≤
      ENNReal.ofReal 25000 *
        derivCarlesonMeasure (fun z => deriv (deriv f) z / deriv f z)
          (unitDisc ∩ ball ζ (2 * r)) := by
  have hμ : ∀ (G : ℂ → ℝ≥0∞) (S : Set ℂ), MeasurableSet S → S ⊆ unitDisc →
      (volume.restrict unitDisc).withDensity G S = ∫⁻ z in S, G z := by
    intro G S hS hS1
    rw [withDensity_apply _ hS, Measure.restrict_restrict hS, inter_eq_left.mpr hS1]
  have hBm : MeasurableSet (unitDisc ∩ ball ζ r) := measurableSet_ball.inter measurableSet_ball
  have hB'm : MeasurableSet (unitDisc ∩ ball ζ (2 * r)) :=
    measurableSet_ball.inter measurableSet_ball
  obtain ⟨F, hF⟩ : ∃ F : ℂ → ℝ≥0∞,
      F = fun w => ENNReal.ofReal (‖deriv (deriv f) w / deriv f w‖ ^ 2 * (1 - ‖w‖ ^ 2)) :=
    ⟨_, rfl⟩
  have hFm : Measurable F := by
    rw [hF]
    exact ((((measurable_deriv _).div (measurable_deriv f)).norm.pow_const 2).mul
      (measurable_const.sub (measurable_norm.pow_const 2))).ennreal_ofReal
  have e1 : schwarzCarlesonMeasure f (unitDisc ∩ ball ζ r) =
      ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (‖schwarzian f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) :=
    hμ (fun z => ENNReal.ofReal (‖schwarzian f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3)) _ hBm
      inter_subset_left
  have e2 : derivCarlesonMeasure (fun z => deriv (deriv f) z / deriv f z)
      (unitDisc ∩ ball ζ (2 * r)) = ∫⁻ w in unitDisc ∩ ball ζ (2 * r), F w := by
    rw [hF]
    exact hμ (fun z => ENNReal.ofReal (‖deriv (deriv f) z / deriv f z‖ ^ 2 * (1 - ‖z‖ ^ 2))) _
      hB'm inter_subset_left
  rw [e1, e2]
  calc ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (‖schwarzian f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3)
      ≤ ∫⁻ z in unitDisc ∩ ball ζ r, (ENNReal.ofReal 3000 *
          (ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) * ∫⁻ w in ball z ((1 - ‖z‖) / 2), F w) +
          ENNReal.ofReal 18 * F z) :=
        setLIntegral_mono' hBm fun z hz => by
          rw [hF]
          exact s02_sw_pt hf hz.1
    _ = ENNReal.ofReal 3000 * (∫⁻ z in unitDisc ∩ ball ζ r,
          ENNReal.ofReal (((1 - ‖z‖) ^ 2)⁻¹) * ∫⁻ w in ball z ((1 - ‖z‖) / 2), F w) +
          ENNReal.ofReal 18 * ∫⁻ z in unitDisc ∩ ball ζ r, F z := by
        rw [lintegral_add_right _ (hFm.const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal 3000 * (ENNReal.ofReal 8 * ∫⁻ w in unitDisc ∩ ball ζ (2 * r), F w) +
          ENNReal.ofReal 18 * ∫⁻ w in unitDisc ∩ ball ζ (2 * r), F w :=
        add_le_add (mul_le_mul_right (s02_sw_whitney hFm hζ hr) _)
          (mul_le_mul_right (lintegral_mono_set
            (inter_subset_inter_right _ (ball_subset_ball (by linarith)))) _)
    _ ≤ ENNReal.ofReal 25000 * ∫⁻ w in unitDisc ∩ ball ζ (2 * r), F w := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num), ← add_mul,
          ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by norm_num)) _

/-- Shen–Wei (B2) ⇒ (B3), for every conformal `f` of `𝔻` (no quasidisk hypothesis): the forward
half of `thm_shen_wei_B`. -/
theorem s02_sw_B_fwd {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) :
    LogDerivBMOA f → IsCarlesonDisk (schwarzCarlesonMeasure f) := by
  rintro ⟨C, hC, h⟩
  have hM := s02_cm_total ⟨C, hC, h⟩
  refine ⟨ENNReal.ofReal 25000 * (C * ENNReal.ofReal 2 +
      derivCarlesonMeasure (fun z => deriv (deriv f) z / deriv f z) unitDisc),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top, hM⟩),
    fun ζ hζ r hr hr2 => ?_⟩
  refine (s02_sw_box hf hζ hr).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_right ?_ _
  rcases lt_or_ge r 1 with h1 | h1
  · calc derivCarlesonMeasure (fun z => deriv (deriv f) z / deriv f z) (unitDisc ∩ ball ζ (2 * r))
        ≤ C * ENNReal.ofReal (2 * r) := h ζ hζ (2 * r) (by positivity) (by linarith)
      _ = C * ENNReal.ofReal 2 * ENNReal.ofReal r := by
          rw [ENNReal.ofReal_mul (by norm_num), mul_assoc]
      _ ≤ _ := mul_le_mul_left le_self_add _
  · calc derivCarlesonMeasure (fun z => deriv (deriv f) z / deriv f z) (unitDisc ∩ ball ζ (2 * r))
        ≤ derivCarlesonMeasure (fun z => deriv (deriv f) z / deriv f z) unitDisc :=
          measure_mono inter_subset_left
      _ ≤ derivCarlesonMeasure (fun z => deriv (deriv f) z / deriv f z) unitDisc *
            ENNReal.ofReal r := by
          conv_lhs => rw [← mul_one (derivCarlesonMeasure _ unitDisc)]
          refine mul_le_mul_right ?_ _
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal h1
      _ ≤ _ := mul_le_mul_left le_add_self _

/-- Shen–Wei (V2) ⇒ (V3), for every conformal `f` of `𝔻`: the forward half of
`thm_shen_wei_V`. -/
theorem s02_sw_V_fwd {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) :
    LogDerivVMOA f → IsVanishingCarlesonDisk (schwarzCarlesonMeasure f) := by
  rintro ⟨hB, hv⟩
  refine ⟨s02_sw_B_fwd hf hB, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, h⟩ := hv (ε / 50000) (by positivity)
  refine ⟨δ / 2, by positivity, fun ζ hζ r hr hrδ => ?_⟩
  calc schwarzCarlesonMeasure f (unitDisc ∩ ball ζ r)
      ≤ ENNReal.ofReal 25000 * derivCarlesonMeasure (fun z => deriv (deriv f) z / deriv f z)
          (unitDisc ∩ ball ζ (2 * r)) := s02_sw_box hf hζ hr
    _ ≤ ENNReal.ofReal 25000 * ENNReal.ofReal (ε / 50000 * (2 * r)) :=
        mul_le_mul_right (h ζ hζ (2 * r) (by positivity) (by linarith)) _
    _ = ENNReal.ofReal (ε * r) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-- Shen–Wei V_bwd helper (V-a, holomorphy): for `f` conformal on `𝔻`, `S f` is holomorphic on `𝔻`
(`S f = (f''/f')' − ½ (f''/f')²` there, `s02_sw_logDeriv`). -/
theorem s02_va_schwarz_diff {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) :
    DifferentiableOn ℂ (schwarzian f) unitDisc := by
  obtain ⟨hφ, hS⟩ := s02_sw_logDeriv hf
  have hφa : AnalyticOnNhd ℂ (fun z => deriv (deriv f) z / deriv f z) unitDisc :=
    hφ.analyticOnNhd isOpen_ball
  have hG : DifferentiableOn ℂ (fun z => deriv (fun w => deriv (deriv f) w / deriv f w) z -
      1 / 2 * (deriv (deriv f) z / deriv f z) ^ 2) unitDisc :=
    hφa.deriv.differentiableOn.sub ((hφ.pow 2).const_mul _)
  exact hG.congr fun z hz => hS z hz

/-- Shen–Wei V_bwd helper (V-a, local mass): with `ρ = (1 − |z|)/2`, `D(z, ρ) ⊂ 𝔻` and
`1 − |w|² ≥ ρ` on it, so the sub-mean value inequality `s02_sw_meanValue` for `S f` gives
`|S f(z)|² π ρ⁵ ≤ λ_f(D(z, ρ))` for `λ_f = |S f|²(1 − |w|²)³ dA`. -/
theorem s02_va_mass {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {z : ℂ}
    (hz : z ∈ unitDisc) :
    ENNReal.ofReal (‖schwarzian f z‖ ^ 2 * (π * ((1 - ‖z‖) / 2) ^ 5)) ≤
      schwarzCarlesonMeasure f (ball z ((1 - ‖z‖) / 2)) := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = (1 - ‖z‖) / 2 := ⟨_, rfl⟩
  rw [← hρdef]
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  -- `‖w‖ ≤ 1 − ρ` on `D̄(z, ρ)`
  have hwn : ∀ w ∈ closedBall z ρ, ‖w‖ ≤ 1 - ρ := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    linarith [norm_sub_norm_le w z]
  have hcb : closedBall z ρ ⊆ unitDisc := fun w hw =>
    mem_ball_zero_iff.mpr (by linarith [hwn w hw])
  have hball : ball z ρ ⊆ unitDisc := ball_subset_closedBall.trans hcb
  have hmv := s02_sw_meanValue hρ ((s02_va_schwarz_diff hf).mono hcb)
  unfold schwarzCarlesonMeasure
  rw [withDensity_apply _ measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
    inter_eq_left.mpr hball]
  calc ENNReal.ofReal (‖schwarzian f z‖ ^ 2 * (π * ρ ^ 5))
      = ENNReal.ofReal (ρ ^ 3) *
          (ENNReal.ofReal (‖schwarzian f z‖ ^ 2) * ENNReal.ofReal (π * ρ ^ 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (pow_nonneg hρ.le 3)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (ρ ^ 3) * ∫⁻ w in ball z ρ, ENNReal.ofReal (‖schwarzian f w‖ ^ 2) :=
        mul_le_mul_right hmv _
    _ = ∫⁻ w in ball z ρ, ENNReal.ofReal (ρ ^ 3) * ENNReal.ofReal (‖schwarzian f w‖ ^ 2) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ w in ball z ρ, ENNReal.ofReal (‖schwarzian f w‖ ^ 2 * (1 - ‖w‖ ^ 2) ^ 3) := by
        refine setLIntegral_mono' measurableSet_ball fun w hw => ?_
        rw [← ENNReal.ofReal_mul (pow_nonneg hρ.le 3)]
        apply ENNReal.ofReal_le_ofReal
        have h1 := hwn w (ball_subset_closedBall hw)
        have h0 : 0 ≤ ‖w‖ * (1 - ‖w‖) := mul_nonneg (norm_nonneg w) (by linarith)
        have h2 : ρ ≤ 1 - ‖w‖ ^ 2 := by nlinarith
        have h3 : ρ ^ 3 ≤ (1 - ‖w‖ ^ 2) ^ 3 := pow_le_pow_left₀ hρ.le h2 3
        have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg ‖schwarzian f w‖)
        linarith

/-- Shen–Wei V_bwd helper (V-a, box inclusion): for `0 < |z| < 1`,
`D(z, (1 − |z|)/2) ⊂ 𝔻 ∩ D(z/|z|, 3(1 − |z|)/2)`. -/
theorem s02_va_ball_sub {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    ball z ((1 - ‖z‖) / 2) ⊆ unitDisc ∩ ball (z / (‖z‖ : ℂ)) (3 * (1 - ‖z‖) / 2) := by
  intro w hw
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hc : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hzn.ne'
  rw [mem_ball, dist_eq_norm] at hw
  refine ⟨mem_ball_zero_iff.mpr ?_, ?_⟩
  · linarith [norm_sub_norm_le w z]
  · -- `|z − z/|z|| = 1 − |z|`
    have hu : ‖z / (‖z‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hzn.le, div_self hzn.ne']
    have he : z - z / (‖z‖ : ℂ) = ((‖z‖ - 1 : ℝ) : ℂ) * (z / (‖z‖ : ℂ)) := by
      push_cast
      rw [sub_mul, one_mul, mul_div_cancel₀ _ hc]
    have h1 : ‖z - z / (‖z‖ : ℂ)‖ = 1 - ‖z‖ := by
      rw [he, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith)]
      ring
    rw [mem_ball, dist_eq_norm]
    linarith [norm_sub_le_norm_sub_add_norm_sub w z (z / (‖z‖ : ℂ))]

/-- Shen–Wei V_bwd helper (V-a = [SW] Lemma 4.1(2)): if `|S f|²(1 − |z|²)³ dA ∈ CM₀(𝔻)` then
`(1 − |z|²)² |S f(z)| → 0` as `|z| → 1`. From `s02_va_mass` and `s02_va_ball_sub`:
`|S f(z)|² π ρ⁵ ≤ λ_f(𝔻 ∩ D(ζ, 3ρ)) ≤ ε' · 3ρ` and `1 − |z|² ≤ 4ρ`. -/
theorem s02_va_decay {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (hv : IsVanishingCarlesonDisk (schwarzCarlesonMeasure f)) :
    ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, r < 1 ∧ ∀ z : ℂ, r < ‖z‖ → ‖z‖ < 1 →
      (1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzian f z‖ < ε := by
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := hv.2 (π * ε ^ 2 / 1536) (by positivity)
  refine ⟨max (1 / 2) (1 - δ / 3), max_lt (by norm_num) (by linarith), fun z hr hz1 => ?_⟩
  have hz2 : 1 / 2 < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hr
  have hz3 : 1 - δ / 3 < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hr
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz2; norm_num at hz2
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set ρ : ℝ := (1 - ‖z‖) / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  have hζ : z / (‖z‖ : ℂ) ∈ sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, Real.norm_of_nonneg hzn.le,
      div_self hzn.ne']
  have hm := (s02_va_mass hf (mem_ball_zero_iff.mpr hz1)).trans
    ((measure_mono (s02_va_ball_sub hz0 hz1)).trans
      (H _ hζ (3 * (1 - ‖z‖) / 2) (by linarith) (by linarith)))
  rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) (by linarith)), ← hρdef,
    show 3 * (1 - ‖z‖) / 2 = 3 * ρ by rw [hρdef]; ring] at hm
  -- `|S|² ρ⁴ ≤ ε²/512`
  have hS : ‖schwarzian f z‖ ^ 2 * ρ ^ 4 ≤ ε ^ 2 / 512 := by
    have h1 : π * ρ * (‖schwarzian f z‖ ^ 2 * ρ ^ 4) ≤ π * ρ * (ε ^ 2 / 512) := by
      linarith
    exact le_of_mul_le_mul_left h1 (by positivity)
  have hw : 1 - ‖z‖ ^ 2 ≤ 4 * ρ := by rw [hρdef]; nlinarith
  have hw0 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith
  have hsq : ((1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzian f z‖) ^ 2 < ε ^ 2 := by
    have h4 : (1 - ‖z‖ ^ 2) ^ 4 ≤ (4 * ρ) ^ 4 := pow_le_pow_left₀ hw0 hw 4
    calc ((1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzian f z‖) ^ 2
        = (1 - ‖z‖ ^ 2) ^ 4 * ‖schwarzian f z‖ ^ 2 := by ring
      _ ≤ (4 * ρ) ^ 4 * ‖schwarzian f z‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
      _ = 256 * (‖schwarzian f z‖ ^ 2 * ρ ^ 4) := by ring
      _ ≤ 256 * (ε ^ 2 / 512) := by linarith
      _ < ε ^ 2 := by nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq

/-- Shen–Wei V_bwd helper (V-c, real constant): a Carleson measure has a real Carleson constant. -/
theorem s02_vc_real {μ : Measure ℂ} (h : IsCarlesonDisk μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      μ (unitDisc ∩ ball ξ r) ≤ ENNReal.ofReal (C * r) := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C.toReal, ENNReal.toReal_nonneg, fun ξ hξ r hr0 hr2 => ?_⟩
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC]
  exact hb ξ hξ r hr0 hr2

/-- Shen–Wei V_bwd helper (V-c, total mass): `𝔻 ⊆ D(1, 3/2) ∪ D(−1, 3/2)`, so a Carleson constant `C`
bounds `μ(𝔻) ≤ 3C`. -/
theorem s02_vc_total {μ : Measure ℂ} {C : ℝ}
    (hC : ∀ ξ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      μ (unitDisc ∩ ball ξ r) ≤ ENNReal.ofReal (C * r)) :
    μ unitDisc ≤ ENNReal.ofReal (3 * C) := by
  have hsub : unitDisc ⊆ (unitDisc ∩ ball 1 (3 / 2)) ∪ (unitDisc ∩ ball (-1) (3 / 2)) := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    by_contra hc
    simp only [mem_union, mem_inter_iff, mem_ball, not_or, not_and, not_lt] at hc
    have h1 := hc.1 hz
    have h2 := hc.2 hz
    rw [dist_eq_norm] at h1 h2
    have e : ‖z - 1‖ ^ 2 + ‖z - -1‖ ^ 2 = 2 * ‖z‖ ^ 2 + 2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im]
      ring
    nlinarith [norm_nonneg z, mul_le_mul h1 h1 (by norm_num) (norm_nonneg _),
      mul_le_mul h2 h2 (by norm_num) (norm_nonneg _)]
  calc μ unitDisc
      ≤ μ (unitDisc ∩ ball 1 (3 / 2)) + μ (unitDisc ∩ ball (-1) (3 / 2)) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (C * (3 / 2)) + ENNReal.ofReal (C * (3 / 2)) :=
        add_le_add (hC 1 (by simp) _ (by norm_num) (by norm_num))
          (hC (-1) (by simp) _ (by norm_num) (by norm_num))
    _ = ENNReal.ofReal (3 * C) := by
        rcases le_or_gt 0 C with h0 | h0
        · rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
        · rw [ENNReal.ofReal_of_nonpos (by linarith : C * (3 / 2) ≤ 0),
            ENNReal.ofReal_of_nonpos (by linarith : 3 * C ≤ 0), add_zero]

/-- Shen–Wei V_bwd helper (V-c, growth at all radii): a real Carleson constant `C ≥ 0` gives
`μ(𝔻 ∩ D(ξ, s)) ≤ (3/2) C s` for every `s > 0` (`s02_vc_total` for `s ≥ 2`). -/
theorem s02_vc_growth {μ : Measure ℂ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ξ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      μ (unitDisc ∩ ball ξ r) ≤ ENNReal.ofReal (C * r))
    (ξ : ℂ) (hξ : ξ ∈ sphere (0 : ℂ) 1) (s : ℝ) (hs : 0 < s) :
    μ (unitDisc ∩ ball ξ s) ≤ ENNReal.ofReal (3 / 2 * C * s) := by
  rcases lt_or_ge s 2 with h2 | h2
  · exact (hC ξ hξ s hs h2).trans (ENNReal.ofReal_le_ofReal (by nlinarith))
  · exact (measure_mono inter_subset_left).trans
      ((s02_vc_total hC).trans (ENNReal.ofReal_le_ofReal (by nlinarith)))

/-- Shen–Wei V_bwd helper (V-c, kernel geometry): for `ζ = ρξ`, `|ξ| = 1`, `0 ≤ ρ < 1`, `h = 1 − ρ`
and `|z| ≤ 1`: `|1 − ζ̄z| = |ξ − ρz| ≥ max(h, |z − ξ| − h) ≥ (h + |z − ξ|)/3` and `1 − ρ² ≤ 2h`, so the
Poisson-type kernel is at most `18h/(h + |z − ξ|)²`. -/
theorem s02_vc_geom {ξ z : ℂ} (hξ : ξ ∈ sphere (0 : ℂ) 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hz : ‖z‖ ≤ 1) :
    (1 - ‖(ρ : ℂ) * ξ‖ ^ 2) / ‖1 - conj ((ρ : ℂ) * ξ) * z‖ ^ 2 ≤
      18 * (1 - ρ) / ((1 - ρ) + ‖z - ξ‖) ^ 2 := by
  have hξn : ‖ξ‖ = 1 := mem_sphere_zero_iff_norm.mp hξ
  have hcξ : conj ξ * ξ = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hξn]
    norm_num
  have he : 1 - conj ((ρ : ℂ) * ξ) * z = conj ξ * (ξ - (ρ : ℂ) * z) := by
    rw [map_mul, Complex.conj_ofReal]
    linear_combination (-1 : ℂ) * hcξ
  have hn : ‖1 - conj ((ρ : ℂ) * ξ) * z‖ = ‖ξ - (ρ : ℂ) * z‖ := by
    rw [he, norm_mul, Complex.norm_conj, hξn, one_mul]
  have hρξ : ‖(ρ : ℂ) * ξ‖ = ρ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0, hξn, mul_one]
  have hρz : ‖(ρ : ℂ) * z‖ = ρ * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0]
  have hzz : ‖(ρ : ℂ) * z - z‖ = (1 - ρ) * ‖z‖ := by
    rw [show (ρ : ℂ) * z - z = ((ρ - 1 : ℝ) : ℂ) * z by push_cast; ring, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hN1 : 1 - ρ ≤ ‖ξ - (ρ : ℂ) * z‖ := by
    have := norm_sub_norm_le ξ ((ρ : ℂ) * z)
    rw [hξn, hρz] at this
    nlinarith [mul_le_mul_of_nonneg_left hz hρ0]
  have hN2 : ‖z - ξ‖ - (1 - ρ) ≤ ‖ξ - (ρ : ℂ) * z‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub ξ ((ρ : ℂ) * z) z
    rw [norm_sub_rev ξ z, hzz] at this
    nlinarith [mul_le_mul_of_nonneg_left hz (by linarith : (0 : ℝ) ≤ 1 - ρ)]
  rw [hn, hρξ]
  have hN0 : 0 < ‖ξ - (ρ : ℂ) * z‖ := by linarith
  have h3 : (1 - ρ) + ‖z - ξ‖ ≤ 3 * ‖ξ - (ρ : ℂ) * z‖ := by linarith
  have h1 : ((1 - ρ) + ‖z - ξ‖) ^ 2 ≤ 9 * ‖ξ - (ρ : ℂ) * z‖ ^ 2 := by
    have := pow_le_pow_left₀ (by linarith [norm_nonneg (z - ξ)]) h3 2
    linarith [show (3 * ‖ξ - (ρ : ℂ) * z‖) ^ 2 = 9 * ‖ξ - (ρ : ℂ) * z‖ ^ 2 by ring]
  have h2 : 1 - ρ ^ 2 ≤ 2 * (1 - ρ) := by nlinarith
  have hpos : 0 < (1 - ρ) + ‖z - ξ‖ := by linarith [norm_nonneg (z - ξ)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc (1 - ρ ^ 2) * ((1 - ρ) + ‖z - ξ‖) ^ 2
      ≤ (2 * (1 - ρ)) * (9 * ‖ξ - (ρ : ℂ) * z‖ ^ 2) :=
        mul_le_mul h2 h1 (sq_nonneg _) (by linarith)
    _ = 18 * (1 - ρ) * ‖ξ - (ρ : ℂ) * z‖ ^ 2 := by ring

/-- Shen–Wei V_bwd helper (V-c, tail integral): `∫_c^∞ k/(h + s)^{k+1} ds = 1/(h + c)^k`. -/
theorem s02_vc_tail {h c : ℝ} (hh : 0 < h) (hc : 0 ≤ c) {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ s in Ioi c, ENNReal.ofReal (k / (h + s) ^ (k + 1)) = ENNReal.ofReal (1 / (h + c) ^ k) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
  have hk0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hder : ∀ x ∈ Ici c, HasDerivAt (fun s : ℝ => -((h + s) ^ (m + 1))⁻¹)
      (((m + 1 : ℕ) : ℝ) / (h + x) ^ (m + 1 + 1)) x := by
    intro x hx
    have hx0 : 0 < h + x := by linarith [mem_Ici.mp hx]
    have h1 : HasDerivAt (fun s : ℝ => h + s) 1 x := (hasDerivAt_id x).const_add h
    have h3 := ((h1.pow (m + 1)).inv (pow_ne_zero _ hx0.ne')).neg
    convert h3 using 1
    simp only [Pi.pow_apply, Nat.add_sub_cancel]
    field_simp
    ring
  have hpos : ∀ x ∈ Ioi c, 0 ≤ ((m + 1 : ℕ) : ℝ) / (h + x) ^ (m + 1 + 1) := fun x hx =>
    div_nonneg hk0.le (pow_nonneg (by linarith [mem_Ioi.mp hx]) _)
  have hlim : Tendsto (fun s : ℝ => -((h + s) ^ (m + 1))⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => (h + s) ^ (m + 1)) atTop atTop :=
      (tendsto_pow_atTop (by omega)).comp (tendsto_atTop_add_const_left atTop h tendsto_id)
    simpa using h1.inv_tendsto_atTop.neg
  have hint := integrableOn_Ioi_deriv_of_nonneg' hder hpos hlim
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' hder hpos hlim
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hpos)), hval]
  congr 1
  rw [zero_sub, neg_neg, one_div]

/-- Shen–Wei V_bwd helper (V-c, layer cake): writing `h/(h + d)² = ∫_d^∞ 2h/(h + s)³ ds` and using
Tonelli, `∫_𝔻 h/(h + |z − ξ|)² dμ = ∫_0^∞ 2h/(h + s)³ μ(𝔻 ∩ D(ξ, s)) ds`; the growth bounds `a s`
(`s < δ`) and `b s` (all `s`) then give at most `2a + 2bh/δ`. -/
theorem s02_vc_layer {μ : Measure ℂ} {ξ : ℂ} {h a b δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hsmall : ∀ s : ℝ, 0 < s → s < δ → μ (unitDisc ∩ ball ξ s) ≤ ENNReal.ofReal (a * s))
    (hall : ∀ s : ℝ, 0 < s → μ (unitDisc ∩ ball ξ s) ≤ ENNReal.ofReal (b * s)) :
    ∫⁻ z in unitDisc, ENNReal.ofReal (h / (h + ‖z - ξ‖) ^ 2) ∂μ ≤
      ENNReal.ofReal (2 * a + 2 * b * h / δ) := by
  -- `𝔻` has finite mass
  have hsub : unitDisc ⊆ ball ξ (‖ξ‖ + 2) := by
    intro z hz
    rw [mem_ball, dist_eq_norm]
    have := mem_ball_zero_iff.mp hz
    linarith [norm_sub_le z ξ]
  have hfin : μ unitDisc ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := b * (‖ξ‖ + 2))) ?_
    calc μ unitDisc = μ (unitDisc ∩ ball ξ (‖ξ‖ + 2)) := by rw [inter_eq_left.mpr hsub]
      _ ≤ _ := hall _ (by positivity)
  obtain ⟨ν, hν⟩ : ∃ ν : Measure ℂ, ν = μ.restrict unitDisc := ⟨_, rfl⟩
  have : IsFiniteMeasure ν := ⟨by rw [hν, Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  have hνb : ∀ s, ν (ball ξ s) = μ (unitDisc ∩ ball ξ s) := fun s => by
    rw [hν, Measure.restrict_apply measurableSet_ball, inter_comm]
  -- `h/(h + d)² = ∫_d^∞ 2h/(h + s)³ ds`
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ≥0∞, G = fun s =>
      ENNReal.ofReal h * ENNReal.ofReal (((2 : ℕ) : ℝ) / (h + s) ^ (2 + 1)) := ⟨_, rfl⟩
  have hGm : Measurable G := by
    rw [hG]
    exact measurable_const.mul (ENNReal.measurable_ofReal.comp (by fun_prop))
  have hrep : ∀ z : ℂ, ENNReal.ofReal (h / (h + ‖z - ξ‖) ^ 2) =
      ∫⁻ s, (Ioi ‖z - ξ‖).indicator G s := by
    intro z
    rw [lintegral_indicator measurableSet_Ioi]
    simp only [hG]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      s02_vc_tail hh (norm_nonneg _) (by norm_num : 1 ≤ 2), ← ENNReal.ofReal_mul hh.le]
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
  -- the dominating functions
  obtain ⟨A, hA⟩ : ∃ A : ℝ → ℝ≥0∞, A = fun s =>
      ENNReal.ofReal (2 * a * h) * ENNReal.ofReal (((1 : ℕ) : ℝ) / (h + s) ^ (1 + 1)) :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ → ℝ≥0∞, B = fun s =>
      ENNReal.ofReal (2 * b * h) * ENNReal.ofReal (((1 : ℕ) : ℝ) / (h + s) ^ (1 + 1)) :=
    ⟨_, rfl⟩
  have hAm : Measurable A := by
    rw [hA]
    exact measurable_const.mul (ENNReal.measurable_ofReal.comp (by fun_prop))
  have hBm : Measurable B := by
    rw [hB]
    exact measurable_const.mul (ENNReal.measurable_ofReal.comp (by fun_prop))
  have key : ∀ s : ℝ, 0 < s → ∀ c : ℝ, 0 ≤ c → μ (unitDisc ∩ ball ξ s) ≤ ENNReal.ofReal (c * s) →
      G s * μ (unitDisc ∩ ball ξ s) ≤
        ENNReal.ofReal (2 * c * h) * ENNReal.ofReal (((1 : ℕ) : ℝ) / (h + s) ^ (1 + 1)) := by
    intro s hs c hc hμ
    have hp : 0 < h + s := by linarith
    refine (mul_le_mul_right hμ _).trans ?_
    rw [hG]
    dsimp only
    rw [← ENNReal.ofReal_mul hh.le,
      ← ENNReal.ofReal_mul (mul_nonneg hh.le (div_nonneg (by norm_num) (pow_nonneg hp.le _))),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hc) hh.le)]
    apply ENNReal.ofReal_le_ofReal
    have e1 : h * (((2 : ℕ) : ℝ) / (h + s) ^ (2 + 1)) * (c * s) =
        2 * c * h * (((1 : ℕ) : ℝ) / (h + s) ^ (1 + 1)) * (s / (h + s)) := by
      field_simp
      ring
    rw [e1]
    exact mul_le_of_le_one_right
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc) hh.le)
        (div_nonneg (by norm_num) (pow_nonneg hp.le _)))
      ((div_le_one hp).mpr (by linarith))
  have hpt : ∀ s : ℝ, G s * μ (unitDisc ∩ ball ξ s) ≤
      (Ioi 0).indicator A s + (Ici δ).indicator B s := by
    intro s
    rcases le_or_gt s 0 with hs | hs
    · rw [ball_eq_empty.mpr hs, inter_empty, measure_empty, mul_zero]
      exact zero_le
    rcases lt_or_ge s δ with hsδ | hsδ
    · rw [Set.indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs), hA]
      exact (key s hs a ha (hsmall s hs hsδ)).trans le_self_add
    · rw [Set.indicator_of_mem (show s ∈ Ici δ from hsδ), hB]
      exact (key s hs b hb (hall s hs)).trans le_add_self
  have hAi : ∫⁻ s in Ioi 0, A s = ENNReal.ofReal (2 * a) := by
    simp only [hA]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, s02_vc_tail hh le_rfl le_rfl,
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) ha) hh.le)]
    congr 1
    rw [add_zero, pow_one]
    field_simp
  have hBi : ∫⁻ s in Ici δ, B s = ENNReal.ofReal (2 * b * h * (1 / (h + δ) ^ 1)) := by
    rw [setLIntegral_congr Ioi_ae_eq_Ici.symm]
    simp only [hB]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, s02_vc_tail hh hδ.le le_rfl,
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hb) hh.le)]
  calc ∫⁻ z in unitDisc, ENNReal.ofReal (h / (h + ‖z - ξ‖) ^ 2) ∂μ
      = ∫⁻ z, (∫⁻ s, (Ioi ‖z - ξ‖).indicator G s) ∂ν := by
        rw [hν]
        exact lintegral_congr fun z => hrep z
    _ = ∫⁻ s, ∫⁻ z, (Ioi ‖z - ξ‖).indicator G s ∂ν := lintegral_lintegral_swap hFm.aemeasurable
    _ = ∫⁻ s, G s * μ (unitDisc ∩ ball ξ s) := by
        refine lintegral_congr fun s => ?_
        have e : (fun z : ℂ => (Ioi ‖z - ξ‖).indicator G s) =
            (ball ξ s).indicator (fun _ => G s) := by
          funext z
          by_cases hz : ‖z - ξ‖ < s
          · rw [Set.indicator_of_mem (show s ∈ Ioi ‖z - ξ‖ from hz),
              Set.indicator_of_mem (show z ∈ ball ξ s by rwa [mem_ball, dist_eq_norm])]
          · rw [Set.indicator_of_notMem (show s ∉ Ioi ‖z - ξ‖ from hz),
              Set.indicator_of_notMem (show z ∉ ball ξ s by rwa [mem_ball, dist_eq_norm])]
        rw [e, lintegral_indicator_const measurableSet_ball, hνb]
    _ ≤ ∫⁻ s, ((Ioi 0).indicator A s + (Ici δ).indicator B s) := lintegral_mono hpt
    _ = (∫⁻ s in Ioi 0, A s) + ∫⁻ s in Ici δ, B s := by
        rw [lintegral_add_left (hAm.indicator measurableSet_Ioi),
          lintegral_indicator measurableSet_Ioi, lintegral_indicator measurableSet_Ici]
    _ ≤ ENNReal.ofReal (2 * a + 2 * b * h / δ) := by
        have hbh : 0 ≤ 2 * b * h := mul_nonneg (mul_nonneg (by norm_num) hb) hh.le
        rw [hAi, hBi, ← ENNReal.ofReal_add (mul_nonneg (by norm_num) ha)
          (mul_nonneg hbh (div_nonneg zero_le_one (pow_nonneg (by linarith) _)))]
        apply ENNReal.ofReal_le_ofReal
        have : 2 * b * h * (1 / (h + δ) ^ 1) ≤ 2 * b * h / δ := by
          rw [pow_one, mul_one_div]
          exact div_le_div_of_nonneg_left hbh hδ (by linarith)
        linarith

/-- Shen–Wei V_bwd helper (V-c, polar form): `ζ = |ζ| ξ` for some `|ξ| = 1`. -/
theorem s02_vc_polar (ζ : ℂ) : ∃ ξ ∈ sphere (0 : ℂ) 1, ζ = (‖ζ‖ : ℂ) * ξ := by
  by_cases h0 : ζ = 0
  · exact ⟨1, by simp, by simp [h0]⟩
  · have hc : (‖ζ‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
    refine ⟨ζ / (‖ζ‖ : ℂ), ?_, (mul_div_cancel₀ ζ hc).symm⟩
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr h0)]

/-- Shen–Wei V_bwd helper (V-c, reduction): with `ζ = |ζ| ξ`, the kernel integral is at most
`18 ∫_𝔻 h/(h + |z − ξ|)² dμ`, `h = 1 − |ζ|` (`s02_vc_geom`). -/
theorem s02_vc_reduce {μ : Measure ℂ} {ζ ξ : ℂ} (hξ : ξ ∈ sphere (0 : ℂ) 1)
    (hζξ : ζ = (‖ζ‖ : ℂ) * ξ) (hζ : ‖ζ‖ < 1) :
    ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2) ∂μ ≤
      ENNReal.ofReal 18 *
        ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖) / ((1 - ‖ζ‖) + ‖z - ξ‖) ^ 2) ∂μ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
  have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
  have hg := s02_vc_geom hξ (norm_nonneg ζ) hζ hz1
  rw [← hζξ] at hg
  rw [← ENNReal.ofReal_mul (by norm_num), ← mul_div_assoc]
  exact ENNReal.ofReal_le_ofReal hg

/-- Shen–Wei V_bwd helper (V-c = [SW] (3.2)/(3.4), `⇒`): a Carleson constant `C` bounds the kernel
integral `∫_𝔻 (1 − |ζ|²)/|1 − ζ̄z|² dμ(z) ≤ 108 C` for every `ζ ∈ 𝔻` (`s02_vc_geom`, `s02_vc_layer` with
`a = b = 3C/2`, `δ = 1`). -/
theorem s02_vc_kernel_bound {μ : Measure ℂ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ξ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
      μ (unitDisc ∩ ball ξ r) ≤ ENNReal.ofReal (C * r))
    {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2) ∂μ ≤
      ENNReal.ofReal (108 * C) := by
  obtain ⟨ξ, hξ, hζξ⟩ := s02_vc_polar ζ
  have hh : 0 < 1 - ‖ζ‖ := by linarith
  have hl := s02_vc_layer (μ := μ) (ξ := ξ) hh one_pos (by positivity : (0 : ℝ) ≤ 3 / 2 * C)
    (by positivity : (0 : ℝ) ≤ 3 / 2 * C) (fun s hs _ => s02_vc_growth hC0 hC ξ hξ s hs)
    (s02_vc_growth hC0 hC ξ hξ)
  refine (s02_vc_reduce hξ hζξ hζ).trans ((mul_le_mul_right hl _).trans ?_)
  rw [← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  rw [div_one]
  nlinarith [mul_nonneg hC0 (norm_nonneg ζ)]

/-- Shen–Wei V_bwd helper (V-c = [SW] (3.3), `⇒`): for `μ ∈ CM₀(𝔻)` the kernel integral tends to `0`
as `|ζ| → 1` (`s02_vc_layer` with `a = ε'`, `b = 3C/2`, `δ` from the vanishing condition). -/
theorem s02_vc_kernel_vanish {μ : Measure ℂ} (hv : IsVanishingCarlesonDisk μ) :
    ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, r < 1 ∧ ∀ ζ : ℂ, r < ‖ζ‖ → ‖ζ‖ < 1 →
      ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2) ∂μ ≤
        ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := s02_vc_real hv.1
  obtain ⟨δ, hδ, hsm⟩ := hv.2 (ε / 72) (by positivity)
  have hη : 0 < ε * δ / (108 * C + 1) := by positivity
  refine ⟨max 0 (1 - ε * δ / (108 * C + 1)), max_lt (by norm_num) (by linarith),
    fun ζ hr hζ => ?_⟩
  have hr1 : 1 - ε * δ / (108 * C + 1) < ‖ζ‖ := lt_of_le_of_lt (le_max_right _ _) hr
  obtain ⟨ξ, hξ, hζξ⟩ := s02_vc_polar ζ
  have hh : 0 < 1 - ‖ζ‖ := by linarith
  have hl := s02_vc_layer (μ := μ) (ξ := ξ) hh hδ (by positivity : (0 : ℝ) ≤ ε / 72)
    (by positivity : (0 : ℝ) ≤ 3 / 2 * C) (fun s hs hsδ => hsm ξ hξ s hs hsδ)
    (s02_vc_growth hC0 hC ξ hξ)
  refine (s02_vc_reduce hξ hζξ hζ).trans ((mul_le_mul_right hl _).trans ?_)
  rw [← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have h2 : (1 - ‖ζ‖) * (108 * C + 1) < ε * δ := by
    have : 1 - ‖ζ‖ < ε * δ / (108 * C + 1) := by linarith
    rwa [lt_div_iff₀ (by positivity)] at this
  have h3 : 2 * (3 / 2 * C) * (1 - ‖ζ‖) / δ ≤ ε / 36 := by
    rw [div_le_iff₀ hδ]
    nlinarith [mul_nonneg hC0 hh.le]
  linarith

/-- Shen–Wei V_bwd helper (V-c, kernel lower bound): for `|ξ| = 1`, `0 < r < 1`, `ζ = (1 − r)ξ` and
`z ∈ 𝔻 ∩ D(ξ, r)`: `|1 − ζ̄z| = |ξ − (1 − r)z| < 2r` and `1 − |ζ|² ≥ r`, so the kernel is `≥ 1/(4r)`. -/
theorem s02_vc_lower {ξ z : ℂ} (hξ : ξ ∈ sphere (0 : ℂ) 1) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hz : z ∈ unitDisc ∩ ball ξ r) :
    1 / (4 * r) ≤
      (1 - ‖((1 - r : ℝ) : ℂ) * ξ‖ ^ 2) / ‖1 - conj (((1 - r : ℝ) : ℂ) * ξ) * z‖ ^ 2 := by
  have hξn : ‖ξ‖ = 1 := mem_sphere_zero_iff_norm.mp hξ
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz.1
  have hzr : ‖z - ξ‖ < r := by
    have := hz.2
    rwa [mem_ball, dist_eq_norm] at this
  have hcξ : conj ξ * ξ = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hξn]
    norm_num
  have he : 1 - conj (((1 - r : ℝ) : ℂ) * ξ) * z = conj ξ * (ξ - ((1 - r : ℝ) : ℂ) * z) := by
    rw [map_mul, Complex.conj_ofReal]
    linear_combination (-1 : ℂ) * hcξ
  have hn : ‖1 - conj (((1 - r : ℝ) : ℂ) * ξ) * z‖ = ‖ξ - ((1 - r : ℝ) : ℂ) * z‖ := by
    rw [he, norm_mul, Complex.norm_conj, hξn, one_mul]
  have hN : ‖ξ - ((1 - r : ℝ) : ℂ) * z‖ < 2 * r := by
    have e2 : ξ - ((1 - r : ℝ) : ℂ) * z = (ξ - z) + ((r : ℝ) : ℂ) * z := by
      push_cast
      ring
    rw [e2]
    calc ‖(ξ - z) + ((r : ℝ) : ℂ) * z‖ ≤ ‖ξ - z‖ + ‖((r : ℝ) : ℂ) * z‖ := norm_add_le _ _
      _ < r + r := by
        rw [norm_sub_rev, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
        nlinarith [mul_lt_mul_of_pos_left hz1 hr0]
      _ = 2 * r := by ring
  have hN0 : 0 < ‖ξ - ((1 - r : ℝ) : ℂ) * z‖ := by
    have := norm_sub_norm_le ξ (((1 - r : ℝ) : ℂ) * z)
    rw [hξn, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at this
    nlinarith [norm_nonneg z, mul_lt_mul_of_pos_left hz1 (by linarith : (0 : ℝ) < 1 - r)]
  have hρ : ‖((1 - r : ℝ) : ℂ) * ξ‖ = 1 - r := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), hξn, mul_one]
  rw [hn, hρ, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_self_lt_mul_self hN0.le hN, mul_pos (mul_pos hr0 hr0) (sub_pos.mpr hr1)]

/-- Shen–Wei V_bwd helper (V-c, box by kernel): `μ(𝔻 ∩ D(ξ, r)) ≤ 4r · ∫_𝔻 k_ζ dμ` with
`ζ = (1 − r)ξ` (`s02_vc_lower`). -/
theorem s02_vc_box_le {μ : Measure ℂ} {ξ : ℂ} (hξ : ξ ∈ sphere (0 : ℂ) 1) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) :
    μ (unitDisc ∩ ball ξ r) ≤ ENNReal.ofReal (4 * r) *
      ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖((1 - r : ℝ) : ℂ) * ξ‖ ^ 2) /
        ‖1 - conj (((1 - r : ℝ) : ℂ) * ξ) * z‖ ^ 2) ∂μ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← setLIntegral_one]
  refine le_trans ?_ (lintegral_mono_set (inter_subset_left (t := ball ξ r)))
  refine setLIntegral_mono' (measurableSet_ball.inter measurableSet_ball) fun z hz => ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  have hl := s02_vc_lower hξ hr0 hr1 hz
  calc (1 : ℝ) = 4 * r * (1 / (4 * r)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)

/-- Shen–Wei V_bwd helper (V-c = [SW] (3.2)/(3.4), `⇐`): a uniformly bounded kernel integral gives a
Carleson measure (`s02_vc_box_le` for `r < 1`; `ζ = 0` bounds `μ(𝔻)` for `1 ≤ r < 2`). -/
theorem s02_vc_of_kernel {μ : Measure ℂ} {M : ℝ}
    (hM : ∀ ζ : ℂ, ‖ζ‖ < 1 →
      ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2) ∂μ ≤
        ENNReal.ofReal M) :
    IsCarlesonDisk μ := by
  have hM0 : μ unitDisc ≤ ENNReal.ofReal M := by
    have := hM 0 (by simp)
    simpa using this
  refine ⟨ENNReal.ofReal (4 * M), ENNReal.ofReal_ne_top, fun ξ hξ r hr0 hr2 => ?_⟩
  rw [← ENNReal.ofReal_mul' hr0.le]
  rcases lt_or_ge r 1 with h1 | h1
  · have hn : ‖((1 - r : ℝ) : ℂ) * ξ‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith),
        mem_sphere_zero_iff_norm.mp hξ]
      linarith
    refine (s02_vc_box_le hξ hr0 h1).trans ((mul_le_mul_right (hM _ hn) _).trans ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact le_of_eq (congrArg ENNReal.ofReal (by ring))
  · refine (measure_mono inter_subset_left).trans (hM0.trans ?_)
    rcases le_or_gt 0 M with hM1 | hM1
    · exact ENNReal.ofReal_le_ofReal (by nlinarith)
    · rw [ENNReal.ofReal_of_nonpos hM1.le]
      exact zero_le

/-- Shen–Wei V_bwd helper (V-c = [SW] (3.3), `⇐`): a Carleson measure whose kernel integral tends to
`0` as `|ζ| → 1` is in `CM₀(𝔻)` (`s02_vc_box_le`). -/
theorem s02_vc_vanishing_of_kernel {μ : Measure ℂ} (hc : IsCarlesonDisk μ)
    (h0 : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, r < 1 ∧ ∀ ζ : ℂ, r < ‖ζ‖ → ‖ζ‖ < 1 →
      ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2) ∂μ ≤
        ENNReal.ofReal ε) :
    IsVanishingCarlesonDisk μ := by
  refine ⟨hc, fun ε hε => ?_⟩
  obtain ⟨r₀, hr₀, H⟩ := h0 (ε / 4) (by positivity)
  refine ⟨min 1 (1 - r₀), lt_min one_pos (by linarith), fun ξ hξ r hr0 hrδ => ?_⟩
  have hr1 : r < 1 := lt_of_lt_of_le hrδ (min_le_left _ _)
  have hr2 : r < 1 - r₀ := lt_of_lt_of_le hrδ (min_le_right _ _)
  have hn : ‖((1 - r : ℝ) : ℂ) * ξ‖ = 1 - r := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith),
      mem_sphere_zero_iff_norm.mp hξ, mul_one]
  have hk := H _ (by rw [hn]; linarith) (by rw [hn]; linarith)
  refine (s02_vc_box_le hξ hr0 hr1).trans ((mul_le_mul_right hk _).trans ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact le_of_eq (congrArg ENNReal.ofReal (by ring))

-- Moved byte-identically from `EpsteinVMO/S12_Counter.lean` (w6) for V-d (leader decision 2026-11-04).
/-- Helper: circle Parseval for a finite sum of monomials with distinct exponents. -/
theorem s12_circle_parseval (s : Finset ℕ) (e : ℕ → ℕ) (he : InjOn e s) (b : ℕ → ℂ) {r : ℝ}
    (hr : 0 ≤ r) :
    Real.circleAverage (fun z => ‖∑ n ∈ s, b n * z ^ e n‖ ^ 2) 0 r =
      ∑ n ∈ s, ‖b n‖ ^ 2 * r ^ (2 * e n) := by
  set p : Polynomial ℂ := ∑ n ∈ s, Polynomial.monomial (e n) (b n) with hp
  have hev : ∀ z, p.eval z = ∑ n ∈ s, b n * z ^ e n := fun z => by
    simp [hp, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  have hco : ∀ k, p.coeff k = ∑ n ∈ s, if e n = k then b n else 0 := fun k => by
    simp [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  have hcoe : ∀ m ∈ s, p.coeff (e m) = b m := fun m hm => by
    rw [hco, Finset.sum_eq_single m]
    · simp
    · intro n hn hnm
      rw [if_neg]
      exact fun h => hnm (he hn hm h)
    · intro h
      exact absurd hm h
  have hsupp : p.support ⊆ s.image e := by
    intro k hk
    by_contra hk'
    apply Polynomial.mem_support_iff.mp hk
    rw [hco]
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [if_neg]
    exact fun h => hk' (Finset.mem_image.mpr ⟨n, hn, h⟩)
  have h1 : (fun z => ‖∑ n ∈ s, b n * z ^ e n‖ ^ 2) = fun z => ‖p.eval z‖ ^ 2 := by
    funext z
    rw [hev]
  rw [h1, TakhtajanTeo.polynomial_circle_average_sq p hr,
    Finset.sum_subset hsupp, Finset.sum_image fun x hx y hy h => he hx hy h]
  · exact Finset.sum_congr rfl fun n hn => by rw [hcoe n hn]
  · intro k _ hk
    rw [Polynomial.notMem_support_iff.mp hk, norm_zero]
    ring

-- Moved byte-identically from `EpsteinVMO/S12_Counter.lean` (w6) for V-d (leader decision 2026-11-04).
/-- Helper: weighted disc Parseval `∫_𝔻 W(|z|) |Σ b_n z^{e_n}|² = 2π Σ |b_n|² ∫₀¹ r W(r) r^{2e_n}`. -/
theorem s12_disc_parseval (W : ℝ → ℝ) (hW : Continuous W) (s : Finset ℕ) (e : ℕ → ℕ)
    (he : InjOn e s) (b : ℕ → ℂ) (P : ℂ → ℂ) (hP : ∀ z, P z = ∑ n ∈ s, b n * z ^ e n) :
    ∫ z in unitDisc, W ‖z‖ * ‖P z‖ ^ 2 =
      2 * π * ∑ n ∈ s, ‖b n‖ ^ 2 * ∫ r in (0 : ℝ)..1, r * W r * r ^ (2 * e n) := by
  have hPe : P = fun z => ∑ n ∈ s, b n * z ^ e n := funext hP
  subst hPe
  have hPc : Continuous fun z : ℂ => ∑ n ∈ s, b n * z ^ e n :=
    continuous_finsetSum _ fun n _ => by fun_prop
  have hF : Continuous fun z : ℂ => W ‖z‖ * ‖∑ n ∈ s, b n * z ^ e n‖ ^ 2 :=
    (hW.comp continuous_norm).mul (hPc.norm.pow 2)
  rw [TakhtajanTeo.integral_unitDisc_circleAverage _ hF]
  congr 1
  have hint : EqOn (fun r : ℝ => r * Real.circleAverage
      (fun z : ℂ => W ‖z‖ * ‖∑ n ∈ s, b n * z ^ e n‖ ^ 2) 0 r)
      (fun r => ∑ n ∈ s, ‖b n‖ ^ 2 * (r * W r * r ^ (2 * e n))) (uIcc 0 1) := by
    intro r hr
    have hr0 : 0 ≤ r := by
      rw [uIcc_of_le zero_le_one] at hr
      exact hr.1
    have havg : Real.circleAverage (fun z : ℂ => W ‖z‖ * ‖∑ n ∈ s, b n * z ^ e n‖ ^ 2) 0 r =
        W r * Real.circleAverage (fun z : ℂ => ‖∑ n ∈ s, b n * z ^ e n‖ ^ 2) 0 r := by
      rw [Real.circleAverage_congr_sphere
        (f₂ := fun z : ℂ => W r • ‖∑ n ∈ s, b n * z ^ e n‖ ^ 2), Real.circleAverage_fun_smul,
        smul_eq_mul]
      intro z hz
      have hz' : ‖z‖ = |r| := mem_sphere_zero_iff_norm.mp hz
      simp only [hz', abs_of_nonneg hr0, smul_eq_mul]
    dsimp only
    rw [havg, s12_circle_parseval s e he b hr0, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [intervalIntegral.integral_congr hint, intervalIntegral.integral_finsetSum]
  · exact Finset.sum_congr rfl fun n _ => intervalIntegral.integral_const_mul _ _
  · intro n _
    exact (by fun_prop : Continuous fun r : ℝ =>
      ‖b n‖ ^ 2 * (r * W r * r ^ (2 * e n))).intervalIntegrable _ _

/-- Shen–Wei V_bwd helper (V-d, weighted disc Parseval): for a continuous radial weight `W`,
`∫_𝔻 W(|z|) |Σ_{n<N} a_n z^n|² dA = 2π Σ_{n<N} |a_n|² ∫₀¹ r W(r) r^{2n} dr`
(`TakhtajanTeo.integral_unitDisc_circleAverage`, `TakhtajanTeo.polynomial_circle_average_sq`). -/
theorem s02_vd_disc_parseval (W : ℝ → ℝ) (hW : Continuous W) (a : ℕ → ℂ) (N : ℕ) :
    ∫ z in unitDisc, W ‖z‖ * ‖∑ n ∈ Finset.range N, a n * z ^ n‖ ^ 2 =
      2 * π * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 * ∫ r in (0 : ℝ)..1, r * W r * r ^ (2 * n) := by
  have h := s12_disc_parseval W hW (Finset.range N) id (fun _ _ _ _ h => h) a
    (fun z => ∑ n ∈ Finset.range N, a n * z ^ n) (fun _ => rfl)
  simp only [id] at h
  exact h

/-- Shen–Wei V_bwd helper (V-d, radial moment, weight `1 − r²`):
`∫₀¹ r (1 − r²) r^{2n} dr = 1/(2(n + 1)(n + 2))`. -/
theorem s02_vd_radial1 (n : ℕ) :
    ∫ r in (0 : ℝ)..1, r * (1 - r ^ 2) * r ^ (2 * n) =
      1 / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  have hi (j : ℕ) : IntervalIntegrable (fun r : ℝ => r ^ j) volume 0 1 :=
    (continuous_pow j).intervalIntegrable _ _
  have hpoly : (fun r : ℝ => r * (1 - r ^ 2) * r ^ (2 * n)) =
      fun r => r ^ (2 * n + 1) - r ^ (2 * n + 3) := by
    funext r
    simp only [pow_add]
    ring
  rw [hpoly, intervalIntegral.integral_sub (hi _) (hi _)]
  simp only [integral_pow, one_pow]
  push_cast
  field_simp
  ring

/-- Shen–Wei V_bwd helper (V-d, radial moment, weight `(1 − r²)³`):
`∫₀¹ r (1 − r²)³ r^{2n} dr = 3/((n + 1)(n + 2)(n + 3)(n + 4))`. -/
theorem s02_vd_radial3 (n : ℕ) :
    ∫ r in (0 : ℝ)..1, r * (1 - r ^ 2) ^ 3 * r ^ (2 * n) =
      3 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4)) := by
  have hi (j : ℕ) : IntervalIntegrable (fun r : ℝ => r ^ j) volume 0 1 :=
    (continuous_pow j).intervalIntegrable _ _
  have hpoly : (fun r : ℝ => r * (1 - r ^ 2) ^ 3 * r ^ (2 * n)) = fun r =>
      r ^ (2 * n + 1) - 3 * r ^ (2 * n + 3) + 3 * r ^ (2 * n + 5) - r ^ (2 * n + 7) := by
    funext r
    simp only [pow_add]
    ring
  rw [hpoly, intervalIntegral.integral_sub
      (((hi _).sub ((hi _).const_mul 3)).add ((hi _).const_mul 3)) (hi _),
    intervalIntegral.integral_add ((hi _).sub ((hi _).const_mul 3)) ((hi _).const_mul 3),
    intervalIntegral.integral_sub (hi _) ((hi _).const_mul 3),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp only [integral_pow, one_pow]
  push_cast
  field_simp
  ring

/-- Shen–Wei V_bwd helper (V-d, polynomial Littlewood–Paley): for `P = Σ_{n≤N} a_n z^n` and
`Q = Σ_{m<N} (m + 1) a_{m+1} z^m` (`= P'`), coefficientwise (`s02_vd_disc_parseval`,
`s02_vd_radial1/3`): the `n`-th term `π|a_n|²/((n+1)(n+2))` of the left side is at most
`π/2 |a_0|²` for `n = 0` and `(2/3) · 6πn|a_n|²/((n+1)(n+2)(n+3))` for `n ≥ 1`. -/
theorem s02_vd_poly (a : ℕ → ℂ) (N : ℕ) :
    ∫ z in unitDisc, (1 - ‖z‖ ^ 2) * ‖∑ n ∈ Finset.range (N + 1), a n * z ^ n‖ ^ 2 ≤
      π / 2 * ‖a 0‖ ^ 2 + 2 / 3 * ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 3 *
        ‖∑ m ∈ Finset.range N, ((m + 1 : ℕ) : ℂ) * a (m + 1) * z ^ m‖ ^ 2 := by
  have h1 := s02_vd_disc_parseval (fun t => 1 - t ^ 2) (by fun_prop) a (N + 1)
  have h2 := s02_vd_disc_parseval (fun t => (1 - t ^ 2) ^ 3) (by fun_prop)
    (fun m => ((m + 1 : ℕ) : ℂ) * a (m + 1)) N
  simp only [s02_vd_radial1, s02_vd_radial3] at h1 h2
  rw [h1, h2, Finset.sum_range_succ', mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    add_comm]
  refine add_le_add (le_of_eq (by push_cast; ring)) (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_mul, Complex.norm_natCast, mul_pow]
  push_cast
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hA := sq_nonneg ‖a (m + 1)‖
  have e1 : 2 * π * (‖a (m + 1)‖ ^ 2 * (1 / (2 * ((m : ℝ) + 1 + 1) * ((m : ℝ) + 1 + 2)))) =
      π * ‖a (m + 1)‖ ^ 2 / (((m : ℝ) + 2) * ((m : ℝ) + 3)) := by
    field_simp
    ring
  have e2 : 2 / 3 * (2 * π * (((m : ℝ) + 1) ^ 2 * ‖a (m + 1)‖ ^ 2 *
      (3 / (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((m : ℝ) + 4))))) =
      π * ‖a (m + 1)‖ ^ 2 / (((m : ℝ) + 2) * ((m : ℝ) + 3)) * (4 * ((m : ℝ) + 1) / ((m : ℝ) + 4)) := by
    field_simp
    ring
  rw [e1, e2]
  exact le_mul_of_one_le_right (by positivity) ((one_le_div (by positivity)).mpr (by linarith))

/-- Shen–Wei V_bwd helper (V-d, uniform limits): a uniform limit on `D̄` of continuous functions
passes to the weighted integrals over `𝔻` (dominated convergence on the finite measure). -/
theorem s02_vd_lim (W : ℝ → ℝ) (hW : Continuous W) {P : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hP : ∀ N, Continuous (P N)) (hf : ContinuousOn f (closedBall 0 1))
    (hU : TendstoUniformlyOn P f atTop (closedBall 0 1)) :
    Tendsto (fun N => ∫ z in unitDisc, W ‖z‖ * ‖P N z‖ ^ 2) atTop
      (𝓝 (∫ z in unitDisc, W ‖z‖ * ‖f z‖ ^ 2)) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hf
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    ((hW.comp continuous_norm).continuousOn (s := closedBall (0 : ℂ) 1))
  have hsub : unitDisc ⊆ closedBall (0 : ℂ) 1 := ball_subset_closedBall
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => K * (M + 1) ^ 2) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun N =>
      ((hW.comp continuous_norm).mul ((hP N).norm.pow 2)).aestronglyMeasurable
  · filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hU) 1 one_pos] with N hN
    filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet unitDisc)] with z hz
    have hz' := hsub hz
    have h1 : ‖P N z‖ ≤ M + 1 := by
      have := hN z hz'
      rw [dist_eq_norm] at this
      linarith [norm_sub_norm_le (P N z) (f z), hM z hz', norm_sub_rev (f z) (P N z)]
    rw [norm_mul, norm_pow, norm_norm]
    exact mul_le_mul (hK z hz') (pow_le_pow_left₀ (norm_nonneg _) h1 2) (by positivity)
      ((norm_nonneg _).trans (hK z hz'))
  · exact (continuousOn_const.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set hsub
  · filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet unitDisc)] with z hz
    exact ((hU.tendsto_at (hsub hz)).norm.pow 2).const_mul _

/-- Shen–Wei V_bwd helper (V-d, dilations): for `F` holomorphic on `𝔻` and `0 < r < 1`, the
inequality holds for `F_r(z) = F(rz)`: the dilated Taylor polynomials (Mathlib
`Complex.hasSum_taylorSeries_on_ball`, `TakhtajanTeo.Ch2.bergmanTaylorPoly_dilate_uniform`, and
`TakhtajanTeo.Ch2.faber_powerSeries_deriv` for `F'`) converge uniformly on `D̄`, so `s02_vd_poly` passes to
the limit by `s02_vd_lim`. -/
theorem s02_vd_dilate {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F unitDisc) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) :
    ∫ z in unitDisc, (1 - ‖z‖ ^ 2) * ‖F ((r : ℂ) * z)‖ ^ 2 ≤
      π / 2 * ‖F 0‖ ^ 2 + 2 / 3 * ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 3 *
        ‖(r : ℂ) * deriv F ((r : ℂ) * z)‖ ^ 2 := by
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
  have hL1 := (s02_vd_lim (fun t => 1 - t ^ 2) (by fun_prop)
    (fun N => continuous_finsetSum _ fun n _ => by fun_prop) hc1 hU1).comp
    (tendsto_add_atTop_nat 1)
  have hL2 := s02_vd_lim (fun t => (1 - t ^ 2) ^ 3) (by fun_prop)
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
  have hpN : ∀ N : ℕ, ∫ z in unitDisc, (1 - ‖z‖ ^ 2) *
      ‖∑ n ∈ Finset.range (N + 1), c n * (r : ℂ) ^ n * z ^ n‖ ^ 2 ≤
      π / 2 * ‖F 0‖ ^ 2 + 2 / 3 * (r ^ 2 * ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 3 *
        ‖∑ m ∈ Finset.range N, c (m + 1) * ((m + 1 : ℕ) : ℂ) * (r : ℂ) ^ m * z ^ m‖ ^ 2) := by
    intro N
    have h := s02_vd_poly (fun n => c n * (r : ℂ) ^ n) N
    have e : ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 3 * ‖∑ m ∈ Finset.range N,
        ((m + 1 : ℕ) : ℂ) * (c (m + 1) * (r : ℂ) ^ (m + 1)) * z ^ m‖ ^ 2 =
        r ^ 2 * ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 3 *
          ‖∑ m ∈ Finset.range N, c (m + 1) * ((m + 1 : ℕ) : ℂ) * (r : ℂ) ^ m * z ^ m‖ ^ 2 := by
      rw [← integral_const_mul]
      congr 1
      funext z
      rw [hQ]
      ring
    rw [e, pow_zero, mul_one, hc0] at h
    exact h
  have hR : ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 3 * ‖(r : ℂ) * deriv F ((r : ℂ) * z)‖ ^ 2 =
      r ^ 2 * ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 3 * ‖deriv F ((r : ℂ) * z)‖ ^ 2 := by
    rw [← integral_const_mul]
    congr 1
    funext z
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    ring
  rw [hR]
  exact le_of_tendsto_of_tendsto' hL1 (((hL2.const_mul (r ^ 2)).const_mul (2 / 3)).const_add _) hpN

/-- Shen–Wei V_bwd helper (V-d, scaling): for `0 < r ≤ 1`, `u = rz` (`dA(z) = r⁻² dA(u)`,
`Measure.map_addHaar_smul`) and `1 − |u|²/r² ≤ 1 − |u|²` give
`∫_𝔻 (1 − |z|²)³ |r G(rz)|² dA ≤ ∫_𝔻 (1 − |u|²)³ |G(u)|² dA`. -/
theorem s02_vd_scale {G : ℂ → ℂ} (hG : Measurable G) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 * ‖(r : ℂ) * G ((r : ℂ) * z)‖ ^ 2) ≤
      ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 * ‖G z‖ ^ 2) := by
  have hr' : r ≠ 0 := hr0.ne'
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ → ℝ≥0∞, ψ = (ball (0 : ℂ) r).indicator fun u =>
      ENNReal.ofReal (r ^ 2 * ((1 - ‖u‖ ^ 2 / r ^ 2) ^ 3 * ‖G u‖ ^ 2)) := ⟨_, rfl⟩
  have hψm : Measurable ψ := by
    rw [hψ]
    exact (ENNReal.measurable_ofReal.comp (by fun_prop)).indicator measurableSet_ball
  have hpt : ∀ z : ℂ, unitDisc.indicator (fun z => ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 *
      ‖(r : ℂ) * G ((r : ℂ) * z)‖ ^ 2)) z = ψ (r • z) := by
    intro z
    have hn : ‖r • z‖ = r * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg hr0.le]
    rw [hψ]
    by_cases hz : z ∈ unitDisc
    · have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      rw [Set.indicator_of_mem hz,
        Set.indicator_of_mem (mem_ball_zero_iff.mpr (by rw [hn]; nlinarith))]
      congr 1
      rw [hn, Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
      field_simp
    · have hz1 : ¬ ‖z‖ < 1 := fun h => hz (mem_ball_zero_iff.mpr h)
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h => hz1 (by
        have := mem_ball_zero_iff.mp h
        rw [hn] at this
        nlinarith))]
  have hmap := Measure.map_addHaar_smul (volume : Measure ℂ) hr'
  rw [Complex.finrank_real_complex] at hmap
  calc ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 * ‖(r : ℂ) * G ((r : ℂ) * z)‖ ^ 2)
      = ∫⁻ z, ψ (r • z) := by
        rw [← lintegral_indicator (s := unitDisc) measurableSet_ball]
        exact lintegral_congr hpt
    _ = ∫⁻ u, ψ u ∂(Measure.map (fun z : ℂ => r • z) volume) :=
        (lintegral_map hψm (measurable_const_smul r)).symm
    _ = ENNReal.ofReal |(r ^ 2)⁻¹| * ∫⁻ u, ψ u := by rw [hmap, lintegral_smul_measure, smul_eq_mul]
    _ = ∫⁻ u in ball (0 : ℂ) r, ENNReal.ofReal ((1 - ‖u‖ ^ 2 / r ^ 2) ^ 3 * ‖G u‖ ^ 2) := by
        rw [hψ, lintegral_indicator measurableSet_ball,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun u => ?_
        rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (inv_pos.mpr (pow_pos hr0 2))]
        congr 1
        field_simp
    _ ≤ ∫⁻ u in unitDisc, ENNReal.ofReal ((1 - ‖u‖ ^ 2) ^ 3 * ‖G u‖ ^ 2) := by
        refine (setLIntegral_mono' measurableSet_ball fun u hu => ?_).trans
          (lintegral_mono_set (ball_subset_ball hr1))
        apply ENNReal.ofReal_le_ofReal
        have hu1 : ‖u‖ < r := mem_ball_zero_iff.mp hu
        have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hr0.le hr1
        have hrp : 0 < r ^ 2 := pow_pos hr0 2
        have h1 : 0 ≤ 1 - ‖u‖ ^ 2 / r ^ 2 := by
          rw [sub_nonneg, div_le_one hrp]
          nlinarith [norm_nonneg u]
        have h2 : 1 - ‖u‖ ^ 2 / r ^ 2 ≤ 1 - ‖u‖ ^ 2 := by
          have : ‖u‖ ^ 2 ≤ ‖u‖ ^ 2 / r ^ 2 := by
            rw [le_div_iff₀ hrp]
            nlinarith [mul_le_mul_of_nonneg_left hr2 (sq_nonneg ‖u‖)]
          linarith
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h1 h2 3) (sq_nonneg _)

/-- Shen–Wei V_bwd helper (V-d = [SW] Littlewood–Paley, l. 371–373): for `F` holomorphic on `𝔻`,
`∫_𝔻 (1 − |z|²)|F|² dA ≤ (π/2)|F(0)|² + (2/3) ∫_𝔻 (1 − |z|²)³ |F'|² dA` (both sides may be `∞`).
Fatou along `r_k → 1` on the left (`s02_vd_dilate`, converted to `∫⁻`), `s02_vd_scale` with
`G = F'` on the right. -/
theorem s02_vd_lp {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F unitDisc) :
    ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) * ‖F z‖ ^ 2) ≤
      ENNReal.ofReal (π / 2 * ‖F 0‖ ^ 2) + ENNReal.ofReal (2 / 3) *
        ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 * ‖deriv F z‖ ^ 2) := by
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
  have hnn : ∀ g : ℂ → ℝ, (∀ z ∈ unitDisc, 0 ≤ g z) → 0 ≤ᵐ[volume.restrict unitDisc] g :=
    fun g hg => (ae_restrict_iff' (measurableSet_ball : MeasurableSet unitDisc)).mpr
      (ae_of_all _ hg)
  have hw : ∀ z ∈ unitDisc, 0 ≤ 1 - ‖z‖ ^ 2 := fun z hz => by
    have := mem_ball_zero_iff.mp hz
    nlinarith [norm_nonneg z]
  have hmaps : ∀ k, MapsTo (fun z : ℂ => (rs k : ℂ) * z) (closedBall 0 1) unitDisc := by
    intro k z hz
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hr0 k).le]
    exact (mul_le_of_le_one_right (hr0 k).le (mem_closedBall_zero_iff.mp hz)).trans_lt (hr1 k)
  have hc1 : ∀ k, ContinuousOn (fun z => (1 - ‖z‖ ^ 2) * ‖F ((rs k : ℂ) * z)‖ ^ 2)
      (closedBall 0 1) := fun k =>
    (by fun_prop : Continuous fun z : ℂ => 1 - ‖z‖ ^ 2).continuousOn.mul
      ((hF.continuousOn.comp (by fun_prop) (hmaps k)).norm.pow 2)
  -- the dilated bound
  have hk : ∀ k, ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) * ‖F ((rs k : ℂ) * z)‖ ^ 2) ≤
      ENNReal.ofReal (π / 2 * ‖F 0‖ ^ 2) + ENNReal.ofReal (2 / 3) *
        ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 * ‖deriv F z‖ ^ 2) := by
    intro k
    have hc2 : ContinuousOn (fun z => (1 - ‖z‖ ^ 2) ^ 3 *
        ‖(rs k : ℂ) * deriv F ((rs k : ℂ) * z)‖ ^ 2) (closedBall 0 1) :=
      (by fun_prop : Continuous fun z : ℂ => (1 - ‖z‖ ^ 2) ^ 3).continuousOn.mul
        ((continuousOn_const.mul
          ((hF.deriv isOpen_ball).continuousOn.comp (by fun_prop) (hmaps k))).norm.pow 2)
    have hn2 := hnn _ fun z hz => mul_nonneg (pow_nonneg (hw z hz) 3)
      (sq_nonneg ‖(rs k : ℂ) * deriv F ((rs k : ℂ) * z)‖)
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((hc1 k).integrableOn_compact (isCompact_closedBall 0 1) |>.mono_set hsub)
      (hnn _ fun z hz => mul_nonneg (hw z hz) (sq_nonneg _))]
    refine (ENNReal.ofReal_le_ofReal (s02_vd_dilate hF (hr0 k) (hr1 k))).trans ?_
    rw [ENNReal.ofReal_add (by positivity) (mul_nonneg (by norm_num) (integral_nonneg_of_ae hn2)),
      ENNReal.ofReal_mul (p := 2 / 3) (by norm_num), ofReal_integral_eq_lintegral_ofReal
        (hc2.integrableOn_compact (isCompact_closedBall 0 1) |>.mono_set hsub) hn2]
    exact add_le_add le_rfl
      (mul_le_mul_right (s02_vd_scale (measurable_deriv F) (hr0 k) (hr1 k).le) _)
  -- pointwise convergence and Fatou
  have hpt : ∀ z ∈ unitDisc, Tendsto (fun k => ENNReal.ofReal ((1 - ‖z‖ ^ 2) *
      ‖F ((rs k : ℂ) * z)‖ ^ 2)) atTop (𝓝 (ENNReal.ofReal ((1 - ‖z‖ ^ 2) * ‖F z‖ ^ 2))) := by
    intro z hz
    have h1 : Tendsto (fun k => (rs k : ℂ) * z) atTop (𝓝 z) := by
      have := ((Complex.continuous_ofReal.tendsto 1).comp hlim).mul_const z
      simpa using this
    have hFz : ContinuousAt F z := hF.continuousOn.continuousAt (isOpen_ball.mem_nhds hz)
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (((hFz.tendsto.comp h1).norm.pow 2).const_mul _)
  have hmeas : ∀ k, AEMeasurable (fun z => ENNReal.ofReal ((1 - ‖z‖ ^ 2) *
      ‖F ((rs k : ℂ) * z)‖ ^ 2)) (volume.restrict unitDisc) := fun k =>
    (ENNReal.continuous_ofReal.comp_continuousOn ((hc1 k).mono hsub)).aemeasurable
      (measurableSet_ball : MeasurableSet unitDisc)
  calc ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) * ‖F z‖ ^ 2)
      = ∫⁻ z in unitDisc, liminf (fun k => ENNReal.ofReal ((1 - ‖z‖ ^ 2) *
          ‖F ((rs k : ℂ) * z)‖ ^ 2)) atTop := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet unitDisc)] with z hz
        exact (hpt z hz).liminf_eq.symm
    _ ≤ liminf (fun k => ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) *
          ‖F ((rs k : ℂ) * z)‖ ^ 2)) atTop := lintegral_liminf_le' hmeas
    _ ≤ _ := liminf_le_of_frequently_le' (Frequently.of_forall hk)

-- Moved byte-identically from below `s02_sw_V_bwd` (Carleson helpers) for V-e (leader decision 2026-11-04).
/-- Carleson helper (change of variables): for `φ = c·M_a` and measurable `E ⊆ 𝔻`,
`∫_{φ(E)} h dA = ∫_E |φ'|² (h ∘ φ) dA` with `|φ'(z)| = (1-|a|²)/|1-āz|²`. -/
theorem s02_cm_lintegral_blaschke {a c : ℂ} (ha : ‖a‖ < 1) (hc : ‖c‖ = 1) {E : Set ℂ}
    (hE : MeasurableSet E) (hE1 : E ⊆ unitDisc) (h : ℂ → ℝ≥0∞) :
    ∫⁻ w in (fun z => c * blaschke a z) '' E, h w =
      ∫⁻ z in E, ENNReal.ofReal (((1 - ‖a‖ ^ 2) / ‖1 - conj a * z‖ ^ 2) ^ 2) *
        h (c * blaschke a z) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have hd : ∀ z ∈ E, HasDerivAt (fun z => c * blaschke a z)
      (c * ((1 - a * conj a) / (1 - conj a * z) ^ 2)) z := fun z hz =>
    (hasDerivAt_blaschke ha (mem_ball_zero_iff.mp (hE1 hz))).const_mul c
  have hinj : InjOn (fun z => c * blaschke a z) E := fun x hx y hy hxy =>
    (isConformalOnto_blaschke ha).2.1 (hE1 hx) (hE1 hy) (mul_left_cancel₀ hc0 hxy)
  have hdet : ∀ d : ℂ,
      ((ContinuousLinearMap.toSpanSingleton ℂ d).restrictScalars ℝ).det = Complex.normSq d := by
    intro d
    simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]
  have hn : ‖1 - a * conj a‖ = 1 - ‖a‖ ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
    rw [Real.norm_of_nonneg (by nlinarith [norm_nonneg a])]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hE
    (fun z hz => ((hd z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hinj]
  refine setLIntegral_congr_fun hE fun z hz => ?_
  rw [hdet, Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _), norm_mul, hc, one_mul,
    norm_div, norm_pow, hn]

/-- Shen–Wei V_bwd helper (V-e, `G` has the derivative of `s02_ve_deriv` at every point of `𝔻`). -/
theorem s02_ve_hasDeriv {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) {ζ : ℂ} (hζ : ‖ζ‖ < 1)
    {w : ℂ} (hw : w ∈ unitDisc) :
    HasDerivAt (fun w => g (blaschke (-ζ) w) * deriv (blaschke (-ζ)) w)
      (deriv (blaschke (-ζ)) w ^ 2 * (deriv g (blaschke (-ζ) w) -
        2 * conj ζ / (1 - conj ζ * blaschke (-ζ) w) * g (blaschke (-ζ) w))) w := by
  have hζ' : ‖-ζ‖ < 1 := by rwa [norm_neg]
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hb : ∀ v ∈ unitDisc, deriv (blaschke (-ζ)) v =
      (1 - -ζ * conj (-ζ)) / (1 - conj (-ζ) * v) ^ 2 := fun v hv =>
    (hasDerivAt_blaschke hζ' (mem_ball_zero_iff.mp hv)).deriv
  have hden : (1 : ℂ) - conj (-ζ) * w ≠ 0 := blaschke_den_ne_zero hζ' hw1
  have hc0 : (1 : ℂ) - -ζ * conj (-ζ) ≠ 0 := one_sub_mul_conj_ne_zero hζ'
  have hbw : blaschke (-ζ) w ∈ unitDisc :=
    mem_ball_zero_iff.mpr (blaschke_mem_unitDisc hζ' hw1)
  have hgb : HasDerivAt (fun v => g (blaschke (-ζ) v))
      (deriv g (blaschke (-ζ) w) * ((1 - -ζ * conj (-ζ)) / (1 - conj (-ζ) * w) ^ 2)) w :=
    (hg.differentiableAt (isOpen_ball.mem_nhds hbw)).hasDerivAt.comp w
      (hasDerivAt_blaschke hζ' hw1)
  have hq : HasDerivAt (fun v : ℂ => 1 - conj (-ζ) * v) (-(conj (-ζ) * 1)) w :=
    ((hasDerivAt_id w).const_mul (conj (-ζ))).const_sub 1
  have hprod := hgb.mul ((hasDerivAt_const w (1 - -ζ * conj (-ζ))).div (hq.pow 2)
    (pow_ne_zero 2 hden))
  have hev : (fun v => g (blaschke (-ζ) v) * deriv (blaschke (-ζ)) v) =ᶠ[𝓝 w]
      fun v => g (blaschke (-ζ) v) * ((1 - -ζ * conj (-ζ)) / (1 - conj (-ζ) * v) ^ 2) := by
    filter_upwards [isOpen_ball.mem_nhds hw] with v hv
    rw [hb v hv]
  have e3 : 1 - conj ζ * blaschke (-ζ) w = (1 - -ζ * conj (-ζ)) / (1 - conj (-ζ) * w) := by
    rw [blaschke, eq_div_iff hden, sub_mul, mul_assoc, div_mul_cancel₀ _ hden]
    simp only [map_neg]
    ring
  convert hprod.congr_of_eventuallyEq hev using 1
  simp only [Pi.div_apply, Pi.pow_apply]
  rw [hb w hw, e3]
  rw [map_neg] at hden hc0 ⊢
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize (1 : ℂ) - -ζ * -conj ζ = c at hc0 ⊢
  generalize (1 : ℂ) - -conj ζ * w = q at hden ⊢
  field_simp
  ring

/-- Shen–Wei V_bwd helper (V-e, the pulled-back function): for `g` holomorphic on `𝔻` and
`φ = M_{-ζ}` (`φ = γ_ζ⁻¹` of [SW] (4.1)), `G = (g ∘ φ) φ'` is holomorphic on `𝔻`. -/
theorem s02_ve_diff {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    DifferentiableOn ℂ (fun w => g (blaschke (-ζ) w) * deriv (blaschke (-ζ)) w) unitDisc := by
  exact fun w hw => (s02_ve_hasDeriv hg hζ hw).differentiableAt.differentiableWithinAt

/-- Shen–Wei V_bwd helper (V-e, derivative of `G`; [SW] (4.3) without `f_ζ`):
`G' = φ'² · (g' − N_{γ_ζ} g) ∘ φ` with `N_{γ_ζ}(z) = 2ζ̄/(1 − ζ̄z)` ([SW] (4.2)), since
`φ''/φ' = −(N_{γ_ζ} ∘ φ) φ'`. -/
theorem s02_ve_deriv {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) {ζ : ℂ} (hζ : ‖ζ‖ < 1)
    {w : ℂ} (hw : w ∈ unitDisc) :
    deriv (fun w => g (blaschke (-ζ) w) * deriv (blaschke (-ζ)) w) w =
      deriv (blaschke (-ζ)) w ^ 2 * (deriv g (blaschke (-ζ) w) -
        2 * conj ζ / (1 - conj ζ * blaschke (-ζ) w) * g (blaschke (-ζ) w)) := by
  exact (s02_ve_hasDeriv hg hζ hw).deriv

/-- Shen–Wei V_bwd helper (V-e, value at the origin): `G(0) = g(ζ)(1 − |ζ|²)`. -/
theorem s02_ve_origin {g : ℂ → ℂ} {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ‖g (blaschke (-ζ) 0) * deriv (blaschke (-ζ)) 0‖ ^ 2 = ‖g ζ‖ ^ 2 * (1 - ‖ζ‖ ^ 2) ^ 2 := by
  have hζ' : ‖-ζ‖ < 1 := by rwa [norm_neg]
  rw [(hasDerivAt_blaschke hζ' (by simp : ‖(0 : ℂ)‖ < 1)).deriv]
  have e : blaschke (-ζ) 0 = ζ := by simp [blaschke]
  have h1 : (1 - -ζ * conj (-ζ)) / (1 - conj (-ζ) * 0) ^ 2 = 1 - ζ * conj ζ := by simp
  have hn : ‖(1 : ℂ) - ζ * conj ζ‖ = 1 - ‖ζ‖ ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
    rw [Real.norm_of_nonneg (by nlinarith [norm_nonneg ζ])]
  rw [e, h1, norm_mul, mul_pow, hn]

/-- Shen–Wei V_bwd helper (V-e, pointwise Möbius identities): for `z ∈ 𝔻` and `w = γ_ζ(z)`,
with `k = |γ_ζ'(z)| = (1 − |ζ|²)/|1 − ζ̄z|²`: `w ∈ 𝔻`, `φ(w) = z`, `1 − |w|² = k(1 − |z|²)` and
`|φ'(w)| k = 1` (`LiZhongQC.one_sub_normSq_blaschke`, `LiZhongQC.hasDerivAt_blaschke`). -/
theorem s02_ve_point {ζ z : ℂ} (hζ : ‖ζ‖ < 1) (hz : z ∈ unitDisc) :
    blaschke ζ z ∈ unitDisc ∧ blaschke (-ζ) (blaschke ζ z) = z ∧
      1 - ‖blaschke ζ z‖ ^ 2 = (1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 * (1 - ‖z‖ ^ 2) ∧
      ‖deriv (blaschke (-ζ)) (blaschke ζ z)‖ * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2) = 1 := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hden : (1 : ℂ) - conj ζ * z ≠ 0 := blaschke_den_ne_zero hζ hz1
  have hw1 : ‖blaschke ζ z‖ < 1 := blaschke_mem_unitDisc hζ hz1
  refine ⟨mem_ball_zero_iff.mpr hw1, blaschke_neg_blaschke hζ hz1, ?_, ?_⟩
  · have h := one_sub_normSq_blaschke hζ hz1
    simp only [Complex.normSq_eq_norm_sq] at h
    rw [h]
    ring
  · have hζ' : ‖-ζ‖ < 1 := by rwa [norm_neg]
    rw [(hasDerivAt_blaschke hζ' hw1).deriv]
    have hc0 : (1 : ℂ) - ζ * conj ζ ≠ 0 := one_sub_mul_conj_ne_zero hζ
    have e : (1 : ℂ) - conj (-ζ) * blaschke ζ z = (1 - ζ * conj ζ) / (1 - conj ζ * z) := by
      rw [blaschke, eq_div_iff hden, sub_mul, mul_assoc, div_mul_cancel₀ _ hden]
      simp only [map_neg]
      ring
    have e2 : (1 : ℂ) - -ζ * conj (-ζ) = 1 - ζ * conj ζ := by
      simp only [map_neg]
      ring
    have hn : ‖(1 : ℂ) - ζ * conj ζ‖ = 1 - ‖ζ‖ ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      norm_cast
      rw [Real.norm_of_nonneg (by nlinarith [norm_nonneg ζ])]
    have hpos : 1 - ‖ζ‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg ζ]
    have hd : ‖1 - conj ζ * z‖ ≠ 0 := norm_ne_zero_iff.mpr hden
    rw [e, e2, norm_div, norm_pow, norm_div, hn]
    field_simp

/-- Shen–Wei V_bwd helper (V-e, Möbius change of variables on `𝔻`): `w = γ_ζ(z)`,
`dA(w) = |γ_ζ'(z)|² dA(z)` (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`, as in
`s02_cm_lintegral_blaschke` with `c = 1`, `E = 𝔻`). -/
theorem s02_ve_cov {ζ : ℂ} (hζ : ‖ζ‖ < 1) (h : ℂ → ℝ≥0∞) :
    ∫⁻ w in unitDisc, h w = ∫⁻ z in unitDisc,
      ENNReal.ofReal (((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2) ^ 2) * h (blaschke ζ z) := by
  have himg : (fun z => (1 : ℂ) * blaschke ζ z) '' unitDisc = unitDisc := by
    simpa only [one_mul] using (isConformalOnto_blaschke hζ).2.2
  have hcv := s02_cm_lintegral_blaschke (c := 1) (E := unitDisc) hζ norm_one
    measurableSet_ball subset_rfl h
  rw [himg] at hcv
  simpa only [one_mul] using hcv

/-- Shen–Wei V_bwd helper (V-e = [SW] proof of Thm 4.1, chain (4.4) up to the `C₂` line): for `g`
holomorphic on `𝔻` (later `g = N_f`, `g' − ½g² = S_f` by `s02_sw_logDeriv`) and `ζ ∈ 𝔻`,
`∫_𝔻 |γ_ζ'| |g|²(1 − |z|²) ≤ (π/2)|g(ζ)|²(1 − |ζ|²)² + (2/3) ∫_𝔻 |γ_ζ'| |g' − N_{γ_ζ} g|²(1 − |z|²)³`.
Proof: `s02_vd_lp` for `G = (g ∘ φ)φ'` (`s02_ve_diff`, `s02_ve_deriv`, `s02_ve_origin`), then
`s02_ve_cov` and `s02_ve_point` on both integrals. -/
theorem s02_ve_key {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
        (‖g z‖ ^ 2 * (1 - ‖z‖ ^ 2))) ≤
      ENNReal.ofReal (π / 2 * (‖g ζ‖ ^ 2 * (1 - ‖ζ‖ ^ 2) ^ 2)) + ENNReal.ofReal (2 / 3) *
        ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
          (‖deriv g z - 2 * conj ζ / (1 - conj ζ * z) * g z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3)) := by
  have hL : ∫⁻ w in unitDisc, ENNReal.ofReal ((1 - ‖w‖ ^ 2) *
      ‖g (blaschke (-ζ) w) * deriv (blaschke (-ζ)) w‖ ^ 2) =
      ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
        (‖g z‖ ^ 2 * (1 - ‖z‖ ^ 2))) := by
    rw [s02_ve_cov hζ]
    refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
    obtain ⟨_, hinv, h1, h2⟩ := s02_ve_point hζ hz
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    rw [h1, hinv, norm_mul, mul_pow]
    linear_combination ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 * (1 - ‖z‖ ^ 2) * ‖g z‖ ^ 2 *
      (‖deriv (blaschke (-ζ)) (blaschke ζ z)‖ * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2) + 1)) * h2
  have hR : ∫⁻ w in unitDisc, ENNReal.ofReal ((1 - ‖w‖ ^ 2) ^ 3 *
      ‖deriv (fun w => g (blaschke (-ζ) w) * deriv (blaschke (-ζ)) w) w‖ ^ 2) =
      ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
        (‖deriv g z - 2 * conj ζ / (1 - conj ζ * z) * g z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3)) := by
    rw [s02_ve_cov hζ]
    refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
    obtain ⟨hw, hinv, h1, h2⟩ := s02_ve_point hζ hz
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    rw [h1, s02_ve_deriv hg hζ hw, hinv, norm_mul, norm_pow, mul_pow]
    linear_combination ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3 *
      ‖deriv g z - 2 * conj ζ / (1 - conj ζ * z) * g z‖ ^ 2 *
      (‖deriv (blaschke (-ζ)) (blaschke ζ z)‖ * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2) + 1) *
      (‖deriv (blaschke (-ζ)) (blaschke ζ z)‖ ^ 2 *
        ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2) ^ 2 + 1)) * h2
  refine hL.symm.trans_le ((s02_vd_lp (s02_ve_diff hg hζ)).trans (le_of_eq ?_))
  rw [hR, s02_ve_origin hζ]

/-- Shen–Wei V_bwd helper (V-f, denominator): `1 − |ζ||z| ≤ |1 − ζ̄z|`. -/
theorem s02_vf_den {ζ z : ℂ} : 1 - ‖ζ‖ * ‖z‖ ≤ ‖1 - conj ζ * z‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (conj ζ * z)
  rwa [norm_one, norm_mul, Complex.norm_conj] at h

/-- Shen–Wei V_bwd helper (V-f, denominator): for `|ζ| < 1`, `|z| ≤ 1`,
`|1 − ζ̄z| ≥ 1 − |ζ|` and `|1 − ζ̄z| ≥ 1 − |z|`. -/
theorem s02_vf_den_pos {ζ z : ℂ} (hζ : ‖ζ‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - ‖ζ‖ ≤ ‖1 - conj ζ * z‖ ∧ 1 - ‖z‖ ≤ ‖1 - conj ζ * z‖ := by
  have h0 := s02_vf_den (ζ := ζ) (z := z)
  have h1 : ‖ζ‖ * ‖z‖ ≤ ‖ζ‖ := mul_le_of_le_one_right (norm_nonneg _) hz
  have h2 : ‖ζ‖ * ‖z‖ ≤ ‖z‖ := mul_le_of_le_one_left (norm_nonneg _) hζ.le
  constructor <;> linarith

/-- Shen–Wei V_bwd helper (V-f, kernel bound): `0 ≤ |γ_ζ'(z)| ≤ (1 + |ζ|)/(1 − |ζ|)` for `|z| ≤ 1`. -/
theorem s02_vf_kle {ζ z : ℂ} (hζ : ‖ζ‖ < 1) (hz : ‖z‖ ≤ 1) :
    0 ≤ (1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 ∧
      (1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 ≤ (1 + ‖ζ‖) / (1 - ‖ζ‖) := by
  have hD := (s02_vf_den_pos hζ hz).1
  have hp : 0 < 1 - ‖ζ‖ := by linarith
  have hζ0 := norm_nonneg ζ
  refine ⟨div_nonneg (by nlinarith) (sq_nonneg _), ?_⟩
  rw [div_le_div_iff₀ (pow_pos (by linarith) 2) hp]
  have h2 : (1 - ‖ζ‖) ^ 2 ≤ ‖1 - conj ζ * z‖ ^ 2 := pow_le_pow_left₀ hp.le hD 2
  nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 + ‖ζ‖)]

/-- Shen–Wei V_bwd helper (V-f): `z ↦ |γ_ζ'(z)|` is continuous on `𝔻`. -/
theorem s02_vf_kcont {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ContinuousOn (fun z => (1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2) unitDisc :=
  continuousOn_const.div (by fun_prop) fun z hz =>
    pow_ne_zero 2 (ne_of_gt (by
      have := (s02_vf_den_pos hζ (mem_ball_zero_iff.mp hz).le).1
      linarith))

/-- Shen–Wei V_bwd helper (V-f): `ofReal ∘ F` is a.e.-measurable on `𝔻` for `F` continuous on `𝔻`. -/
theorem s02_vf_aem {F : ℂ → ℝ} (hF : ContinuousOn F unitDisc) :
    AEMeasurable (fun z => ENNReal.ofReal (F z)) (volume.restrict unitDisc) :=
  (ENNReal.continuous_ofReal.comp_continuousOn hF).aemeasurable
    (measurableSet_ball : MeasurableSet unitDisc)

/-- Shen–Wei V_bwd helper (V-f): the kernel integral against `F dA` on `𝔻`, for measurable `F`. -/
theorem s02_vf_kernel_wd {F : ℂ → ℝ} (hF : Measurable F) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2)
        ∂((volume.restrict unitDisc).withDensity fun z => ENNReal.ofReal (F z)) =
      ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 * F z) := by
  have hk : Measurable fun z : ℂ => ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.div (by fun_prop : Continuous fun z : ℂ => ‖1 - conj ζ * z‖ ^ 2).measurable)
  rw [restrict_withDensity (s := unitDisc) measurableSet_ball,
    Measure.restrict_restrict (s := unitDisc) measurableSet_ball, inter_self,
    lintegral_withDensity_eq_lintegral_mul _ (f := fun z => ENNReal.ofReal (F z))
      (ENNReal.measurable_ofReal.comp hF) hk]
  refine lintegral_congr fun z => ?_
  have hζ0 := norm_nonneg ζ
  simp only [Pi.mul_apply]
  rw [mul_comm, ← ENNReal.ofReal_mul (div_nonneg (by nlinarith) (sq_nonneg _))]

/-- Shen–Wei V_bwd helper (V-f, the `N_{γ_ζ}` term of [SW] (4.6)): with `n = N_{γ_ζ} = 2ζ̄/(1 − ζ̄z)`,
`∫_𝔻 |γ_ζ'| (1 − |z|²) |n|² dA = 4|ζ|²(1 − |ζ|²) ∫_𝔻 (1 − |z|²)/|1 − ζ̄z|⁴ dA ≤ 4π`, since
`1/(1 − ζ̄z)² = Σ (k + 1) ζ̄^k z^k` and `s02_vd_disc_parseval`, `s02_vd_radial1`, `s02_vd_lim` give
`∫_𝔻 (1 − |z|²)/|1 − ζ̄z|⁴ dA = π Σ (k + 1)/(k + 2) |ζ|^{2k} ≤ π/(1 − |ζ|²)`. -/
theorem s02_vf_kernel_n {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
        ((1 - ‖z‖ ^ 2) * ‖2 * conj ζ / (1 - conj ζ * z)‖ ^ 2)) ≤
      ENNReal.ofReal (4 * π) := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℂ, a = fun n : ℕ => ((n : ℂ) + 1) * conj ζ ^ n := ⟨_, rfl⟩
  have hζ0 := norm_nonneg ζ
  have hnζ : ‖‖ζ‖‖ < 1 := by rwa [norm_norm]
  have hsum : HasSum (fun n : ℕ => ((n : ℝ) + 1) * ‖ζ‖ ^ n)
      (‖ζ‖ / (1 - ‖ζ‖) ^ 2 + (1 - ‖ζ‖)⁻¹) := by
    convert (hasSum_coe_mul_geometric_of_norm_lt_one hnζ).add
      (hasSum_geometric_of_norm_lt_one hnζ) using 1
    ext n
    ring
  have hna : ∀ n : ℕ, ‖a n‖ = ((n : ℝ) + 1) * ‖ζ‖ ^ n := fun n => by
    rw [ha, norm_mul, norm_pow, Complex.norm_conj]
    congr 1
    rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast
    ring
  have hbd : ∀ n z, z ∈ closedBall (0 : ℂ) 1 → ‖a n * z ^ n‖ ≤ ((n : ℝ) + 1) * ‖ζ‖ ^ n := by
    intro n z hz
    rw [norm_mul, norm_pow, hna]
    exact mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (norm_nonneg z) (mem_closedBall_zero_iff.mp hz))
  have hU := tendstoUniformlyOn_tsum_nat hsum.summable hbd
  have hPc : ∀ N, Continuous fun x : ℂ => ∑ n ∈ Finset.range N, a n * x ^ n := fun N =>
    continuous_finsetSum _ fun n _ => by fun_prop
  have hfc : ContinuousOn (fun x : ℂ => ∑' n, a n * x ^ n) (closedBall 0 1) :=
    hU.continuousOn (Frequently.of_forall fun N => (hPc N).continuousOn)
  have hlim := s02_vd_lim (fun r => 1 - r ^ 2) (by fun_prop) hPc hfc hU
  have hgeom : ∀ N : ℕ, ∑ n ∈ Finset.range N, (‖ζ‖ ^ 2) ^ n ≤ 1 / (1 - ‖ζ‖ ^ 2) := fun N => by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := N) (sq_nonneg ‖ζ‖) (by nlinarith)
    rwa [pow_zero, ← Finset.range_eq_Ico] at this
  have hbound : ∀ N, ∫ z in unitDisc, (fun r : ℝ => 1 - r ^ 2) ‖z‖ *
      ‖∑ n ∈ Finset.range N, a n * z ^ n‖ ^ 2 ≤ π / (1 - ‖ζ‖ ^ 2) := by
    intro N
    have hr : ∀ n : ℕ, ∫ r in (0 : ℝ)..1, r * (fun r : ℝ => 1 - r ^ 2) r * r ^ (2 * n) =
        1 / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := fun n => s02_vd_radial1 n
    rw [s02_vd_disc_parseval (fun r : ℝ => 1 - r ^ 2) (by fun_prop) a N]
    simp only [hr]
    have hterm : ∀ n ∈ Finset.range N, ‖a n‖ ^ 2 * (1 / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2))) ≤
        1 / 2 * (‖ζ‖ ^ 2) ^ n := by
      intro n _
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have e : ‖a n‖ ^ 2 * (1 / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2))) =
          ((n : ℝ) + 1) / ((n : ℝ) + 2) * (1 / 2 * (‖ζ‖ ^ 2) ^ n) := by
        rw [hna]
        field_simp
        ring
      rw [e]
      exact mul_le_of_le_one_left (by positivity) (by rw [div_le_one (by positivity)]; linarith)
    calc 2 * π * ∑ n ∈ Finset.range N,
          ‖a n‖ ^ 2 * (1 / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2)))
        ≤ 2 * π * ∑ n ∈ Finset.range N, 1 / 2 * (‖ζ‖ ^ 2) ^ n :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
      _ = π * ∑ n ∈ Finset.range N, (‖ζ‖ ^ 2) ^ n := by
          rw [← Finset.mul_sum]
          ring
      _ ≤ π * (1 / (1 - ‖ζ‖ ^ 2)) := mul_le_mul_of_nonneg_left (hgeom N) Real.pi_pos.le
      _ = π / (1 - ‖ζ‖ ^ 2) := by ring
  have hI : ∫ z in unitDisc, (fun r : ℝ => 1 - r ^ 2) ‖z‖ * ‖∑' n, a n * z ^ n‖ ^ 2 ≤
      π / (1 - ‖ζ‖ ^ 2) := le_of_tendsto' hlim hbound
  have hts : ∀ z ∈ unitDisc, ∑' n, a n * z ^ n = 1 / (1 - conj ζ * z) ^ 2 := by
    intro z hz
    have hw : ‖conj ζ * z‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      exact (mul_le_of_le_one_right hζ0 (mem_ball_zero_iff.mp hz).le).trans_lt hζ
    have hne : (1 : ℂ) - conj ζ * z ≠ 0 := by
      intro h
      have h1 : conj ζ * z = 1 := by linear_combination -h
      rw [h1, norm_one] at hw
      exact lt_irrefl _ hw
    have hs : HasSum (fun n => a n * z ^ n) (1 / (1 - conj ζ * z) ^ 2) := by
      convert (hasSum_coe_mul_geometric_of_norm_lt_one hw).add
        (hasSum_geometric_of_norm_lt_one hw) using 1
      · ext n
        rw [ha, mul_pow]
        ring
      · field_simp
        ring
    exact hs.tsum_eq
  have hsub : unitDisc ⊆ closedBall (0 : ℂ) 1 := ball_subset_closedBall
  have hint : IntegrableOn (fun z => (fun r : ℝ => 1 - r ^ 2) ‖z‖ * ‖∑' n, a n * z ^ n‖ ^ 2)
      unitDisc := by
    have hc : ContinuousOn (fun z => (fun r : ℝ => 1 - r ^ 2) ‖z‖ * ‖∑' n, a n * z ^ n‖ ^ 2)
        (closedBall 0 1) :=
      (by fun_prop : Continuous fun z : ℂ => 1 - ‖z‖ ^ 2).continuousOn.mul (hfc.norm.pow 2)
    exact (hc.integrableOn_compact (isCompact_closedBall 0 1)).mono_set hsub
  have hnn : 0 ≤ᵐ[volume.restrict unitDisc]
      fun z => (fun r : ℝ => 1 - r ^ 2) ‖z‖ * ‖∑' n, a n * z ^ n‖ ^ 2 :=
    (ae_restrict_iff' (measurableSet_ball : MeasurableSet unitDisc)).mpr
      (ae_of_all _ fun z hz => mul_nonneg (by
        have := mem_ball_zero_iff.mp hz
        nlinarith [norm_nonneg z]) (sq_nonneg _))
  have h1ζ : 0 ≤ 1 - ‖ζ‖ ^ 2 := by nlinarith
  have hc0 : 0 ≤ 4 * ‖ζ‖ ^ 2 * (1 - ‖ζ‖ ^ 2) := mul_nonneg (by positivity) h1ζ
  calc ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
          ((1 - ‖z‖ ^ 2) * ‖2 * conj ζ / (1 - conj ζ * z)‖ ^ 2))
      = ∫⁻ z in unitDisc, ENNReal.ofReal (4 * ‖ζ‖ ^ 2 * (1 - ‖ζ‖ ^ 2)) *
          ENNReal.ofReal ((fun r : ℝ => 1 - r ^ 2) ‖z‖ * ‖∑' n, a n * z ^ n‖ ^ 2) := by
        refine setLIntegral_congr_fun (measurableSet_ball : MeasurableSet unitDisc)
          fun z hz => ?_
        rw [← ENNReal.ofReal_mul hc0, hts z hz]
        congr 1
        have hD : ‖1 - conj ζ * z‖ ≠ 0 := by
          have := (s02_vf_den_pos hζ (mem_ball_zero_iff.mp hz).le).1
          exact ne_of_gt (by linarith)
        simp only [norm_div, norm_mul, norm_pow, norm_one, Complex.norm_conj, Complex.norm_two]
        field_simp
        ring
    _ = ENNReal.ofReal (4 * ‖ζ‖ ^ 2 * (1 - ‖ζ‖ ^ 2)) *
          ENNReal.ofReal (∫ z in unitDisc, (fun r : ℝ => 1 - r ^ 2) ‖z‖ *
            ‖∑' n, a n * z ^ n‖ ^ 2) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ofReal_integral_eq_lintegral_ofReal hint hnn]
    _ ≤ ENNReal.ofReal (4 * ‖ζ‖ ^ 2 * (1 - ‖ζ‖ ^ 2)) * ENNReal.ofReal (π / (1 - ‖ζ‖ ^ 2)) :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal hI) _
    _ ≤ ENNReal.ofReal (4 * π) := by
        rw [← ENNReal.ofReal_mul hc0]
        apply ENNReal.ofReal_le_ofReal
        have h1 : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith
        rw [show 4 * ‖ζ‖ ^ 2 * (1 - ‖ζ‖ ^ 2) * (π / (1 - ‖ζ‖ ^ 2)) = 4 * π * ‖ζ‖ ^ 2 by
          field_simp]
        nlinarith [Real.pi_pos]

/-- Shen–Wei V_bwd helper (V-f = [SW] (4.6)–(4.7), the quartic term): for `g` holomorphic on `𝔻` with
the Bloch bound `(1 − |z|²)|g| ≤ 6` (`s02_sw_bloch` for `g = N_f`) and `(1 − |z|²)|g| ≤ ε` on
`r < |z| < 1`: on `r < |z|` the integrand is `≤ ε² |γ_ζ'| (1 − |z|²)(|g|² + 4|n|²)` (then
`s02_vf_kernel_n`); on `|z| ≤ r` it is `≤ 3600 |γ_ζ'|/(1 − |z|²) ≤ 3600 (1 − |ζ|²)/(1 − r)³`
(`(1 − |z|²)|n| ≤ 4`, `|1 − ζ̄z| ≥ 1 − r`). -/
theorem s02_vf_quartic {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc)
    (hB : ∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) * ‖g z‖ ≤ 6) {ε r : ℝ} (hε : 0 ≤ ε) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hsm : ∀ z : ℂ, r < ‖z‖ → ‖z‖ < 1 → (1 - ‖z‖ ^ 2) * ‖g z‖ ≤ ε) {ζ : ℂ}
    (hζ : ‖ζ‖ < 1) :
    ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
        (‖g z‖ ^ 2 * (‖g z‖ ^ 2 + 4 * ‖2 * conj ζ / (1 - conj ζ * z)‖ ^ 2) * (1 - ‖z‖ ^ 2) ^ 3)) ≤
      ENNReal.ofReal (ε ^ 2) * (∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) /
        ‖1 - conj ζ * z‖ ^ 2 * (‖g z‖ ^ 2 * (1 - ‖z‖ ^ 2)))) +
      ENNReal.ofReal (16 * π * ε ^ 2 + 3600 * π / (1 - r) ^ 3 * (1 - ‖ζ‖ ^ 2)) := by
  -- `0 ≤ ε` and `0 ≤ r` are not needed: the bound holds for any `ε` and any `r < 1`.
  have _hε := hε
  have _hr0 := hr0
  have hζ0 := norm_nonneg ζ
  have h1ζ : 0 ≤ 1 - ‖ζ‖ ^ 2 := by nlinarith
  have hr1' : 0 < 1 - r := by linarith
  have hc0 : 0 ≤ 3600 / (1 - r) ^ 3 * (1 - ‖ζ‖ ^ 2) :=
    mul_nonneg (div_nonneg (by norm_num) (pow_nonneg hr1'.le 3)) h1ζ
  have hpt : ∀ z ∈ unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
      (‖g z‖ ^ 2 * (‖g z‖ ^ 2 + 4 * ‖2 * conj ζ / (1 - conj ζ * z)‖ ^ 2) *
        (1 - ‖z‖ ^ 2) ^ 3)) ≤
      ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
        (‖g z‖ ^ 2 * (1 - ‖z‖ ^ 2))) +
      ENNReal.ofReal (4 * ε ^ 2) * ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
        ((1 - ‖z‖ ^ 2) * ‖2 * conj ζ / (1 - conj ζ * z)‖ ^ 2)) +
      ENNReal.ofReal (3600 / (1 - r) ^ 3 * (1 - ‖ζ‖ ^ 2)) := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have ht0 := norm_nonneg z
    have hu : 0 < 1 - ‖z‖ ^ 2 := by nlinarith
    obtain ⟨hk0, -⟩ := s02_vf_kle hζ hz1.le
    have hDt := (s02_vf_den_pos hζ hz1.le).2
    have hDp : 0 < ‖1 - conj ζ * z‖ := by linarith
    have hNe : ‖2 * conj ζ / (1 - conj ζ * z)‖ = 2 * ‖ζ‖ / ‖1 - conj ζ * z‖ := by
      rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_two]
    have hN0 : 0 ≤ ‖2 * conj ζ / (1 - conj ζ * z)‖ := norm_nonneg _
    have hN4 : ‖2 * conj ζ / (1 - conj ζ * z)‖ * (1 - ‖z‖ ^ 2) ≤ 4 := by
      rw [hNe, div_mul_eq_mul_div, div_le_iff₀ hDp]
      nlinarith [mul_le_mul_of_nonneg_right hζ.le hu.le, sq_nonneg (1 - ‖z‖)]
    have hkt : (1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 * (1 - ‖z‖) ^ 2 ≤ 1 - ‖ζ‖ ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hDt 2) h1ζ
    have hBz := hB z hz
    have hsmz : r < ‖z‖ → (1 - ‖z‖ ^ 2) * ‖g z‖ ≤ ε := fun h => hsm z h hz1
    have hA0 : 0 ≤ (1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 * (‖g z‖ ^ 2 * (1 - ‖z‖ ^ 2)) :=
      mul_nonneg hk0 (mul_nonneg (sq_nonneg _) hu.le)
    have hB0 : 0 ≤ (1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
        ((1 - ‖z‖ ^ 2) * ‖2 * conj ζ / (1 - conj ζ * z)‖ ^ 2) :=
      mul_nonneg hk0 (mul_nonneg hu.le (sq_nonneg _))
    have h4ε : (0 : ℝ) ≤ 4 * ε ^ 2 := by positivity
    rw [← ENNReal.ofReal_mul (sq_nonneg ε), ← ENNReal.ofReal_mul h4ε,
      ← ENNReal.ofReal_add (mul_nonneg (sq_nonneg ε) hA0) (mul_nonneg h4ε hB0),
      ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (sq_nonneg ε) hA0) (mul_nonneg h4ε hB0)) hc0]
    apply ENNReal.ofReal_le_ofReal
    have hG0 := norm_nonneg (g z)
    generalize ‖g z‖ = G at *
    generalize ‖2 * conj ζ / (1 - conj ζ * z)‖ = N at *
    generalize (1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 = k at *
    generalize ‖z‖ = t at *
    rcases le_or_gt t r with htr | htr
    · have hX2 : ((1 - t ^ 2) * G) ^ 2 ≤ 36 := by
        have := pow_le_pow_left₀ (mul_nonneg hu.le hG0) hBz 2
        linarith
      have hY2 : (N * (1 - t ^ 2)) ^ 2 ≤ 16 := by
        have := pow_le_pow_left₀ (mul_nonneg hN0 hu.le) hN4 2
        linarith
      have h1 : k * (G ^ 2 * (G ^ 2 + 4 * N ^ 2) * (1 - t ^ 2) ^ 3) * (1 - t ^ 2) ≤ k * 3600 := by
        have e : k * (G ^ 2 * (G ^ 2 + 4 * N ^ 2) * (1 - t ^ 2) ^ 3) * (1 - t ^ 2) =
            k * (((1 - t ^ 2) * G) ^ 2 * (((1 - t ^ 2) * G) ^ 2 + 4 * (N * (1 - t ^ 2)) ^ 2)) := by
          ring
        rw [e]
        apply mul_le_mul_of_nonneg_left _ hk0
        have := mul_le_mul hX2 (by linarith : ((1 - t ^ 2) * G) ^ 2 + 4 * (N * (1 - t ^ 2)) ^ 2 ≤
          100) (by positivity) (by norm_num)
        linarith
      have hL0 : 0 ≤ k * (G ^ 2 * (G ^ 2 + 4 * N ^ 2) * (1 - t ^ 2) ^ 3) :=
        mul_nonneg hk0 (mul_nonneg (by positivity) (pow_nonneg hu.le 3))
      have h2 : k * (G ^ 2 * (G ^ 2 + 4 * N ^ 2) * (1 - t ^ 2) ^ 3) * ((1 - t ^ 2) * (1 - t) ^ 2) ≤
          3600 * (1 - ‖ζ‖ ^ 2) := by
        calc k * (G ^ 2 * (G ^ 2 + 4 * N ^ 2) * (1 - t ^ 2) ^ 3) * ((1 - t ^ 2) * (1 - t) ^ 2)
            = k * (G ^ 2 * (G ^ 2 + 4 * N ^ 2) * (1 - t ^ 2) ^ 3) * (1 - t ^ 2) * (1 - t) ^ 2 := by
              ring
          _ ≤ k * 3600 * (1 - t) ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
          _ = 3600 * (k * (1 - t) ^ 2) := by ring
          _ ≤ 3600 * (1 - ‖ζ‖ ^ 2) := by linarith
      have h3 : (1 - r) ^ 3 ≤ (1 - t ^ 2) * (1 - t) ^ 2 := by
        have ha : 1 - r ≤ 1 - t ^ 2 := by nlinarith
        have hb : (1 - r) ^ 2 ≤ (1 - t) ^ 2 := pow_le_pow_left₀ hr1'.le (by linarith) 2
        calc (1 - r) ^ 3 = (1 - r) * (1 - r) ^ 2 := by ring
          _ ≤ (1 - t ^ 2) * (1 - t) ^ 2 := mul_le_mul ha hb (sq_nonneg _) hu.le
      have h4 : k * (G ^ 2 * (G ^ 2 + 4 * N ^ 2) * (1 - t ^ 2) ^ 3) ≤
          3600 / (1 - r) ^ 3 * (1 - ‖ζ‖ ^ 2) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hr1' 3)]
        linarith [mul_le_mul_of_nonneg_left h3 hL0]
      linarith [mul_nonneg (sq_nonneg ε) hA0, mul_nonneg h4ε hB0]
    · have hX2 : ((1 - t ^ 2) * G) ^ 2 ≤ ε ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hu.le hG0) (hsmz htr) 2
      have e : k * (G ^ 2 * (G ^ 2 + 4 * N ^ 2) * (1 - t ^ 2) ^ 3) =
          k * (G ^ 2 * (1 - t ^ 2)) * ((1 - t ^ 2) * G) ^ 2 +
            4 * (k * ((1 - t ^ 2) * N ^ 2)) * ((1 - t ^ 2) * G) ^ 2 := by ring
      have h1 := mul_le_mul_of_nonneg_left hX2 hA0
      have h2 := mul_le_mul_of_nonneg_left hX2 hB0
      have e2 : k * (G ^ 2 * (1 - t ^ 2)) * ε ^ 2 + 4 * (k * ((1 - t ^ 2) * N ^ 2) * ε ^ 2) =
          ε ^ 2 * (k * (G ^ 2 * (1 - t ^ 2))) + 4 * ε ^ 2 * (k * ((1 - t ^ 2) * N ^ 2)) := by ring
      rw [e]
      linarith
  have hk := s02_vf_kcont hζ
  have hA : AEMeasurable (fun z => ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
      (‖g z‖ ^ 2 * (1 - ‖z‖ ^ 2)))) (volume.restrict unitDisc) :=
    s02_vf_aem (hk.mul ((hg.continuousOn.norm.pow 2).mul
      (by fun_prop : Continuous fun z : ℂ => 1 - ‖z‖ ^ 2).continuousOn))
  have hvol : volume unitDisc = ENNReal.ofReal π := by
    rw [show unitDisc = ball (0 : ℂ) 1 from rfl, Complex.volume_ball, ENNReal.ofReal_one,
      one_pow, one_mul, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
  calc _ ≤ ∫⁻ z in unitDisc, (ENNReal.ofReal (ε ^ 2) *
          ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 * (‖g z‖ ^ 2 * (1 - ‖z‖ ^ 2))) +
        ENNReal.ofReal (4 * ε ^ 2) * ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
          ((1 - ‖z‖ ^ 2) * ‖2 * conj ζ / (1 - conj ζ * z)‖ ^ 2)) +
        ENNReal.ofReal (3600 / (1 - r) ^ 3 * (1 - ‖ζ‖ ^ 2))) :=
      lintegral_mono_ae ((ae_restrict_iff' (measurableSet_ball : MeasurableSet unitDisc)).mpr
        (ae_of_all _ hpt))
    _ = ENNReal.ofReal (ε ^ 2) * (∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) /
          ‖1 - conj ζ * z‖ ^ 2 * (‖g z‖ ^ 2 * (1 - ‖z‖ ^ 2)))) +
        ENNReal.ofReal (4 * ε ^ 2) * (∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) /
          ‖1 - conj ζ * z‖ ^ 2 * ((1 - ‖z‖ ^ 2) * ‖2 * conj ζ / (1 - conj ζ * z)‖ ^ 2))) +
        ENNReal.ofReal (3600 / (1 - r) ^ 3 * (1 - ‖ζ‖ ^ 2)) * volume unitDisc := by
      rw [lintegral_add_right' _ aemeasurable_const, lintegral_add_left' (hA.const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, setLIntegral_const]
    _ ≤ ENNReal.ofReal (ε ^ 2) * (∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) /
          ‖1 - conj ζ * z‖ ^ 2 * (‖g z‖ ^ 2 * (1 - ‖z‖ ^ 2)))) +
        ENNReal.ofReal (4 * ε ^ 2) * ENNReal.ofReal (4 * π) +
        ENNReal.ofReal (3600 / (1 - r) ^ 3 * (1 - ‖ζ‖ ^ 2)) * ENNReal.ofReal π := by
      rw [hvol]
      exact add_le_add (add_le_add le_rfl (mul_le_mul_right (s02_vf_kernel_n hζ) _)) le_rfl
    _ = _ := by
      rw [add_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hc0,
        ← ENNReal.ofReal_add (by positivity) (mul_nonneg hc0 Real.pi_pos.le)]
      congr 2
      ring

/-- Shen–Wei V_bwd helper (V-f = [SW] (4.4)–(4.7) with absorption): with `S = g' − ½g²`
(`= S_f` for `g = N_f`, `s02_sw_logDeriv`), `|g' − ng|² ≤ 2|S|² + |g|²(|g|² + 4|n|²)`, so
`s02_ve_key` and `s02_vf_quartic` give `I ≤ A + (4/3)B + (2/3)(ε² I + c)`; since `(2/3)ε² ≤ 1/2` and
`I < ∞`, `I ≤ 2A + (8/3)B + (4/3)c`. -/
theorem s02_vf_absorb {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc)
    (hB : ∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) * ‖g z‖ ≤ 6) {ε r : ℝ} (hε : 0 ≤ ε) (hε1 : ε ^ 2 ≤ 3 / 4)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hsm : ∀ z : ℂ, r < ‖z‖ → ‖z‖ < 1 → (1 - ‖z‖ ^ 2) * ‖g z‖ ≤ ε) {ζ : ℂ} (hζ : ‖ζ‖ < 1)
    (hfin : ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
      (‖g z‖ ^ 2 * (1 - ‖z‖ ^ 2))) ≠ ⊤) :
    ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
        (‖g z‖ ^ 2 * (1 - ‖z‖ ^ 2))) ≤
      ENNReal.ofReal (π * (‖g ζ‖ ^ 2 * (1 - ‖ζ‖ ^ 2) ^ 2)) +
      ENNReal.ofReal (8 / 3) * (∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) /
        ‖1 - conj ζ * z‖ ^ 2 * (‖deriv g z - 1 / 2 * g z ^ 2‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3))) +
      ENNReal.ofReal (64 * π / 3 * ε ^ 2 + 4800 * π / (1 - r) ^ 3 * (1 - ‖ζ‖ ^ 2)) := by
  have hζ0 := norm_nonneg ζ
  have h1ζ : 0 ≤ 1 - ‖ζ‖ ^ 2 := by nlinarith
  have hr1' : 0 < 1 - r := by linarith
  have hk := s02_vf_kcont hζ
  have hgd : ContinuousOn (deriv g) unitDisc := (hg.analyticOnNhd isOpen_ball).deriv.continuousOn
  have hbS : AEMeasurable (fun z => ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
      (‖deriv g z - 1 / 2 * g z ^ 2‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3))) (volume.restrict unitDisc) :=
    s02_vf_aem (hk.mul (((hgd.sub (continuousOn_const.mul (hg.continuousOn.pow 2))).norm.pow 2).mul
      (by fun_prop : Continuous fun z : ℂ => (1 - ‖z‖ ^ 2) ^ 3).continuousOn))
  have hY : ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
        (‖deriv g z - 2 * conj ζ / (1 - conj ζ * z) * g z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3)) ≤
      ENNReal.ofReal 2 * (∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) /
        ‖1 - conj ζ * z‖ ^ 2 * (‖deriv g z - 1 / 2 * g z ^ 2‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3))) +
      ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
        (‖g z‖ ^ 2 * (‖g z‖ ^ 2 + 4 * ‖2 * conj ζ / (1 - conj ζ * z)‖ ^ 2) *
          (1 - ‖z‖ ^ 2) ^ 3)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left' (hbS.const_mul _)]
    refine lintegral_mono_ae ((ae_restrict_iff' (measurableSet_ball : MeasurableSet unitDisc)).mpr
      (ae_of_all _ fun z hz => ?_))
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    obtain ⟨hk0, -⟩ := s02_vf_kle hζ hz1.le
    have hw : 0 ≤ (1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3 :=
      mul_nonneg hk0 (pow_nonneg (by nlinarith [norm_nonneg z]) 3)
    have hnorm : ‖deriv g z - 2 * conj ζ / (1 - conj ζ * z) * g z‖ ^ 2 ≤
        2 * ‖deriv g z - 1 / 2 * g z ^ 2‖ ^ 2 +
          ‖g z‖ ^ 2 * (‖g z‖ ^ 2 + 4 * ‖2 * conj ζ / (1 - conj ζ * z)‖ ^ 2) := by
      have e : deriv g z - 2 * conj ζ / (1 - conj ζ * z) * g z = (deriv g z - 1 / 2 * g z ^ 2) +
          g z * (1 / 2 * g z - 2 * conj ζ / (1 - conj ζ * z)) := by ring
      have h1 : ‖deriv g z - 2 * conj ζ / (1 - conj ζ * z) * g z‖ ≤
          ‖deriv g z - 1 / 2 * g z ^ 2‖ +
            ‖g z‖ * (1 / 2 * ‖g z‖ + ‖2 * conj ζ / (1 - conj ζ * z)‖) := by
        rw [e]
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (le_of_eq ?_)) (norm_nonneg _)
        rw [norm_mul]
        norm_num
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have hG0 := norm_nonneg (g z)
      have hN0 := norm_nonneg (2 * conj ζ / (1 - conj ζ * z))
      have hS0 := norm_nonneg (deriv g z - 1 / 2 * g z ^ 2)
      generalize ‖g z‖ = G at *
      generalize ‖2 * conj ζ / (1 - conj ζ * z)‖ = N at *
      generalize ‖deriv g z - 1 / 2 * g z ^ 2‖ = S at *
      nlinarith [sq_nonneg (S - G * (1 / 2 * G + N)), mul_nonneg (sq_nonneg G) (sq_nonneg (G - 2 * N))]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.ofReal_add
      (mul_nonneg (by norm_num) (mul_nonneg hk0 (mul_nonneg (sq_nonneg _)
        (pow_nonneg (by nlinarith [norm_nonneg z]) 3))))
      (mul_nonneg hk0 (mul_nonneg (by positivity) (pow_nonneg (by nlinarith [norm_nonneg z]) 3)))]
    apply ENNReal.ofReal_le_ofReal
    calc (1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
          (‖deriv g z - 2 * conj ζ / (1 - conj ζ * z) * g z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3)
        = (1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3 *
          ‖deriv g z - 2 * conj ζ / (1 - conj ζ * z) * g z‖ ^ 2 := by ring
      _ ≤ (1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3 *
          (2 * ‖deriv g z - 1 / 2 * g z ^ 2‖ ^ 2 +
            ‖g z‖ ^ 2 * (‖g z‖ ^ 2 + 4 * ‖2 * conj ζ / (1 - conj ζ * z)‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hnorm hw
      _ = _ := by ring
  have hQ := s02_vf_quartic hg hB hε hr0 hr1 hsm hζ
  have h := (s02_ve_key hg hζ).trans
    (add_le_add le_rfl (mul_le_mul_right (hY.trans (add_le_add le_rfl hQ)) _))
  have hc0 : 0 ≤ 16 * π * ε ^ 2 + 3600 * π / (1 - r) ^ 3 * (1 - ‖ζ‖ ^ 2) :=
    add_nonneg (by positivity) (mul_nonneg (div_nonneg (by positivity) (pow_nonneg hr1'.le 3)) h1ζ)
  have hc0' : 0 ≤ 64 * π / 3 * ε ^ 2 + 4800 * π / (1 - r) ^ 3 * (1 - ‖ζ‖ ^ 2) :=
    add_nonneg (by positivity) (mul_nonneg (div_nonneg (by positivity) (pow_nonneg hr1'.le 3)) h1ζ)
  have hA0 : 0 ≤ ‖g ζ‖ ^ 2 * (1 - ‖ζ‖ ^ 2) ^ 2 := by positivity
  generalize ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) /
    ‖1 - conj ζ * z‖ ^ 2 * (‖deriv g z - 1 / 2 * g z ^ 2‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3)) = B at h ⊢
  generalize ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
    (‖g z‖ ^ 2 * (1 - ‖z‖ ^ 2))) = I at h hfin ⊢
  rcases eq_or_ne B ⊤ with hBt | hBt
  · rw [hBt, ENNReal.mul_top (by simp : ENNReal.ofReal (8 / 3) ≠ 0)]
    simp
  obtain ⟨i, hi0, rfl⟩ : ∃ i : ℝ, 0 ≤ i ∧ I = ENNReal.ofReal i :=
    ⟨I.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hfin).symm⟩
  obtain ⟨b, hb0, rfl⟩ : ∃ b : ℝ, 0 ≤ b ∧ B = ENNReal.ofReal b :=
    ⟨B.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hBt).symm⟩
  have t1 : (0 : ℝ) ≤ 2 * b := by linarith
  have t2 : 0 ≤ ε ^ 2 * i := mul_nonneg (sq_nonneg ε) hi0
  have t3 : 0 ≤ ε ^ 2 * i + (16 * π * ε ^ 2 + 3600 * π / (1 - r) ^ 3 * (1 - ‖ζ‖ ^ 2)) := by
    linarith
  have t4 : 0 ≤ 2 * b + (ε ^ 2 * i + (16 * π * ε ^ 2 + 3600 * π / (1 - r) ^ 3 *
      (1 - ‖ζ‖ ^ 2))) := by linarith
  have tA : 0 ≤ π / 2 * (‖g ζ‖ ^ 2 * (1 - ‖ζ‖ ^ 2) ^ 2) := by positivity
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.ofReal_mul (sq_nonneg ε),
    ← ENNReal.ofReal_add t2 hc0, ← ENNReal.ofReal_add t1 t3,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2 / 3),
    ← ENNReal.ofReal_add tA (mul_nonneg (by norm_num) t4),
    ENNReal.ofReal_le_ofReal_iff (add_nonneg tA (mul_nonneg (by norm_num) t4))] at h
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8 / 3),
    ← ENNReal.ofReal_add (by positivity) (by linarith),
    ← ENNReal.ofReal_add (by nlinarith [Real.pi_pos]) hc0']
  apply ENNReal.ofReal_le_ofReal
  have he : ε ^ 2 * i ≤ 3 / 4 * i := mul_le_mul_of_nonneg_right hε1 hi0
  have hc' : 64 * π / 3 * ε ^ 2 + 4800 * π / (1 - r) ^ 3 * (1 - ‖ζ‖ ^ 2) =
      4 / 3 * (16 * π * ε ^ 2 + 3600 * π / (1 - r) ^ 3 * (1 - ‖ζ‖ ^ 2)) := by ring
  rw [hc']
  nlinarith

/-- Shen–Wei V_bwd helper (V-f, dilation): for `0 < s ≤ 1`, `g_s(z) = s g(sz)` (`= N_{f_s}` for
`f_s(z) = f(sz)`) is holomorphic on `𝔻` and `g_s' − ½g_s² = s² (g' − ½g²)(sz)`. -/
theorem s02_vf_dil {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s ≤ 1) :
    DifferentiableOn ℂ (fun z => (s : ℂ) * g ((s : ℂ) * z)) unitDisc ∧
      ∀ z ∈ unitDisc, deriv (fun z => (s : ℂ) * g ((s : ℂ) * z)) z -
          1 / 2 * ((s : ℂ) * g ((s : ℂ) * z)) ^ 2 =
        (s : ℂ) ^ 2 * (deriv g ((s : ℂ) * z) - 1 / 2 * g ((s : ℂ) * z) ^ 2) := by
  have hmaps : MapsTo (fun z : ℂ => (s : ℂ) * z) unitDisc unitDisc := by
    intro z hz
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    exact (mul_le_of_le_one_left (norm_nonneg z) hs1).trans_lt (mem_ball_zero_iff.mp hz)
  refine ⟨(differentiableOn_const _).mul
    (hg.comp (by fun_prop : Differentiable ℂ fun z : ℂ => (s : ℂ) * z).differentiableOn hmaps),
    fun z hz => ?_⟩
  have hgz : DifferentiableAt ℂ g ((s : ℂ) * z) :=
    hg.differentiableAt (isOpen_ball.mem_nhds (hmaps hz))
  have hl : HasDerivAt (fun z : ℂ => (s : ℂ) * z) (s : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (s : ℂ)
  have hd : HasDerivAt (fun z => (s : ℂ) * g ((s : ℂ) * z))
      ((s : ℂ) * (deriv g ((s : ℂ) * z) * (s : ℂ))) z :=
    (hgz.hasDerivAt.comp z hl).const_mul (s : ℂ)
  rw [hd.deriv]
  ring

/-- Shen–Wei V_bwd helper (V-f, dilation keeps the Bloch bound): `(1 − |z|²) s ≤ 1 − |sz|²`. -/
theorem s02_vf_dil_bloch {g : ℂ → ℂ} (hB : ∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) * ‖g z‖ ≤ 6) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) * ‖(s : ℂ) * g ((s : ℂ) * z)‖ ≤ 6 := by
  intro z hz
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hn : ‖(s : ℂ) * z‖ = s * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
  have hsz : (s : ℂ) * z ∈ unitDisc := mem_ball_zero_iff.mpr (by
    rw [hn]
    exact (mul_le_of_le_one_left (norm_nonneg z) hs1).trans_lt hz1)
  have h := hB _ hsz
  rw [hn] at h
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
  have e : (1 - ‖z‖ ^ 2) * (s * ‖g ((s : ℂ) * z)‖) = (1 - (s * ‖z‖) ^ 2) * ‖g ((s : ℂ) * z)‖ -
      (1 - s) * (1 + s * ‖z‖ ^ 2) * ‖g ((s : ℂ) * z)‖ := by ring
  rw [e]
  have : 0 ≤ (1 - s) * (1 + s * ‖z‖ ^ 2) * ‖g ((s : ℂ) * z)‖ :=
    mul_nonneg (mul_nonneg (by linarith) (by positivity)) (norm_nonneg _)
  linarith

/-- Shen–Wei V_bwd helper (V-f, little Bloch uniformly in `s`): if `(1 − |z|²)|g| ≤ ε` on
`r < |z| < 1`, then for some `r' < 1` and every `0 < s ≤ 1`, `(1 − |z|²)|g_s| ≤ ε` on `r' < |z| < 1`
(`|sz| > r`: as above; `|sz| ≤ r`: `(1 − r'²) sup_{|w| ≤ r} |g| ≤ ε`). -/
theorem s02_vf_dil_small {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) {ε r : ℝ} (hε : 0 < ε)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hsm : ∀ z : ℂ, r < ‖z‖ → ‖z‖ < 1 → (1 - ‖z‖ ^ 2) * ‖g z‖ ≤ ε) :
    ∃ r' : ℝ, 0 ≤ r' ∧ r' < 1 ∧ ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ z : ℂ, r' < ‖z‖ → ‖z‖ < 1 →
      (1 - ‖z‖ ^ 2) * ‖(s : ℂ) * g ((s : ℂ) * z)‖ ≤ ε := by
  have hcb : closedBall (0 : ℂ) r ⊆ unitDisc := fun w hw =>
    mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hw).trans_lt hr1)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    (hg.continuousOn.mono hcb)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max C 0 + 1 := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; linarith [le_max_right C 0]
  have hCM : ∀ x ∈ closedBall (0 : ℂ) r, ‖g x‖ ≤ M := fun x hx => by
    rw [hM]
    linarith [hC x hx, le_max_left C 0]
  have hδ : 0 < ε / (2 * M) := by positivity
  refine ⟨max r (1 - ε / (2 * M)), le_max_of_le_left hr0, max_lt hr1 (by linarith),
    fun s hs0 hs1 z hz hz1 => ?_⟩
  have ht0 := norm_nonneg z
  have hn : ‖(s : ℂ) * z‖ = s * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
  have hsz1 : s * ‖z‖ < 1 := (mul_le_of_le_one_left ht0 hs1).trans_lt hz1
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
  have hG0 := norm_nonneg (g ((s : ℂ) * z))
  rcases lt_or_ge r (s * ‖z‖) with hr | hr
  · have h := hsm ((s : ℂ) * z) (by rw [hn]; exact hr) (by rw [hn]; exact hsz1)
    rw [hn] at h
    have e : (1 - ‖z‖ ^ 2) * (s * ‖g ((s : ℂ) * z)‖) =
        (1 - (s * ‖z‖) ^ 2) * ‖g ((s : ℂ) * z)‖ -
          (1 - s) * (1 + s * ‖z‖ ^ 2) * ‖g ((s : ℂ) * z)‖ := by ring
    rw [e]
    have : 0 ≤ (1 - s) * (1 + s * ‖z‖ ^ 2) * ‖g ((s : ℂ) * z)‖ :=
      mul_nonneg (mul_nonneg (by linarith) (by positivity)) hG0
    linarith
  · have hgM := hCM _ (mem_closedBall_zero_iff.mpr (by rw [hn]; exact hr))
    have hz' : 1 - ε / (2 * M) < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hz
    have h1 : (1 - ‖z‖) * (2 * M) < ε := by
      have : 1 - ‖z‖ < ε / (2 * M) := by linarith
      rwa [lt_div_iff₀ (by positivity)] at this
    have hu : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith
    calc (1 - ‖z‖ ^ 2) * (s * ‖g ((s : ℂ) * z)‖) ≤ (1 - ‖z‖ ^ 2) * M :=
          mul_le_mul_of_nonneg_left ((mul_le_of_le_one_left hG0 hs1).trans hgM) hu
      _ ≤ (1 - ‖z‖) * (2 * M) := by nlinarith [mul_nonneg (sq_nonneg (1 - ‖z‖)) hM0.le]
      _ ≤ ε := h1.le

/-- Shen–Wei V_bwd helper (V-f, finiteness for the dilations): for `s < 1`, `g_s` is bounded on `𝔻`
(`g` is continuous on `D̄(0, s)`) and `|γ_ζ'| ≤ (1 + |ζ|)/(1 − |ζ|)`, so `I_{g_s}(ζ) < ∞`. -/
theorem s02_vf_dil_fin {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
      (‖(s : ℂ) * g ((s : ℂ) * z)‖ ^ 2 * (1 - ‖z‖ ^ 2))) ≠ ⊤ := by
  have hcb : closedBall (0 : ℂ) s ⊆ unitDisc := fun w hw =>
    mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hw).trans_lt hs1)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) s).exists_bound_of_continuousOn
    (hg.continuousOn.mono hcb)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (mem_closedBall_self hs0.le))
  refine ne_top_of_le_ne_top (b := ∫⁻ _ in unitDisc,
      ENNReal.ofReal ((1 + ‖ζ‖) / (1 - ‖ζ‖) * C ^ 2)) ?_ ?_
  · rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  refine lintegral_mono_ae ((ae_restrict_iff' (measurableSet_ball : MeasurableSet unitDisc)).mpr
    (ae_of_all _ fun z hz => ENNReal.ofReal_le_ofReal ?_))
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  obtain ⟨hk0, hkK⟩ := s02_vf_kle hζ hz1.le
  have hn : ‖(s : ℂ) * z‖ = s * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
  have hgC : ‖(s : ℂ) * g ((s : ℂ) * z)‖ ≤ C := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    refine (mul_le_of_le_one_left (norm_nonneg _) hs1.le).trans (hC _ ?_)
    rw [mem_closedBall_zero_iff, hn]
    exact mul_le_of_le_one_right hs0.le hz1.le
  have hg2 : ‖(s : ℂ) * g ((s : ℂ) * z)‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgC 2
  have hu0 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hu1 : 1 - ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  calc (1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 * (‖(s : ℂ) * g ((s : ℂ) * z)‖ ^ 2 * (1 - ‖z‖ ^ 2))
      ≤ (1 + ‖ζ‖) / (1 - ‖ζ‖) * (C ^ 2 * 1) :=
        mul_le_mul hkK (mul_le_mul hg2 hu1 hu0 (sq_nonneg _)) (by positivity)
          (hk0.trans hkK)
    _ = (1 + ‖ζ‖) / (1 - ‖ζ‖) * C ^ 2 := by ring

/-- Shen–Wei V_bwd helper (V-f, the Schwarzian term of the dilations, for fixed `ζ`):
`|γ_ζ'| ≤ (1 + |ζ|)/(1 − |ζ|)`, `s02_vf_dil`, `s⁴ ≤ s²` and `s02_vd_scale` with `G = g' − ½g²`. -/
theorem s02_vf_dil_B {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) (hgm : Measurable g) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
        (‖deriv (fun z => (s : ℂ) * g ((s : ℂ) * z)) z -
          1 / 2 * ((s : ℂ) * g ((s : ℂ) * z)) ^ 2‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3)) ≤
      ENNReal.ofReal ((1 + ‖ζ‖) / (1 - ‖ζ‖)) * ∫⁻ z in unitDisc,
        ENNReal.ofReal (‖deriv g z - 1 / 2 * g z ^ 2‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) := by
  have hGm : Measurable fun u => deriv g u - 1 / 2 * g u ^ 2 :=
    (measurable_deriv g).sub (measurable_const.mul (hgm.pow_const 2))
  have hsc := s02_vd_scale hGm hs0 hs1
  have hζ1 : 0 < 1 - ‖ζ‖ := by linarith
  calc _ ≤ ∫⁻ z in unitDisc, ENNReal.ofReal ((1 + ‖ζ‖) / (1 - ‖ζ‖)) *
          ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 *
            ‖(s : ℂ) * (deriv g ((s : ℂ) * z) - 1 / 2 * g ((s : ℂ) * z) ^ 2)‖ ^ 2) := by
        refine lintegral_mono_ae ((ae_restrict_iff' (measurableSet_ball :
          MeasurableSet unitDisc)).mpr (ae_of_all _ fun z hz => ?_))
        have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
        obtain ⟨hk0, hkK⟩ := s02_vf_kle hζ hz1.le
        have hu0 : 0 ≤ (1 - ‖z‖ ^ 2) ^ 3 := pow_nonneg (by nlinarith [norm_nonneg z]) 3
        rw [(s02_vf_dil hg hs0 hs1).2 z hz, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hX := norm_nonneg (deriv g ((s : ℂ) * z) - 1 / 2 * g ((s : ℂ) * z) ^ 2)
        rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs0.le]
        generalize ‖deriv g ((s : ℂ) * z) - 1 / 2 * g ((s : ℂ) * z) ^ 2‖ = X at *
        have hs4 : (s ^ 2 * X) ^ 2 ≤ (s * X) ^ 2 := by
          have hss : s ^ 2 ≤ s := by nlinarith
          have : s ^ 2 * X ≤ s * X := mul_le_mul_of_nonneg_right hss hX
          exact pow_le_pow_left₀ (by positivity) this 2
        calc (1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 * ((s ^ 2 * X) ^ 2 * (1 - ‖z‖ ^ 2) ^ 3)
            ≤ (1 + ‖ζ‖) / (1 - ‖ζ‖) * ((s * X) ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) :=
              mul_le_mul hkK (mul_le_mul_of_nonneg_right hs4 hu0) (by positivity)
                (hk0.trans hkK)
          _ = (1 + ‖ζ‖) / (1 - ‖ζ‖) * ((1 - ‖z‖ ^ 2) ^ 3 * (s * X) ^ 2) := by ring
    _ = ENNReal.ofReal ((1 + ‖ζ‖) / (1 - ‖ζ‖)) * ∫⁻ z in unitDisc,
          ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 *
            ‖(s : ℂ) * (deriv g ((s : ℂ) * z) - 1 / 2 * g ((s : ℂ) * z) ^ 2)‖ ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((1 + ‖ζ‖) / (1 - ‖ζ‖)) * ∫⁻ z in unitDisc,
          ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 * ‖deriv g z - 1 / 2 * g z ^ 2‖ ^ 2) :=
        mul_le_mul_right hsc _
    _ = _ := by
        congr 1
        refine lintegral_congr fun z => ?_
        rw [mul_comm]

/-- Shen–Wei V_bwd helper (V-f, Fatou as `s → 1`): a bound on `I_{g_s}(ζ)` for all `0 < s < 1` bounds
`I_g(ζ)` (`lintegral_liminf_le` along `s_n = 1 − 1/(n + 2)`; `g_{s_n} → g` pointwise on `𝔻`). -/
theorem s02_vf_fatou {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) {ζ : ℂ} (hζ : ‖ζ‖ < 1)
    {M : ℝ≥0∞}
    (hM : ∀ s : ℝ, 0 < s → s < 1 → ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) /
      ‖1 - conj ζ * z‖ ^ 2 * (‖(s : ℂ) * g ((s : ℂ) * z)‖ ^ 2 * (1 - ‖z‖ ^ 2))) ≤ M) :
    ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
      (‖g z‖ ^ 2 * (1 - ‖z‖ ^ 2))) ≤ M := by
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
  have hk := s02_vf_kcont hζ
  have hpt : ∀ z ∈ unitDisc, Tendsto (fun k => ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) /
      ‖1 - conj ζ * z‖ ^ 2 * (‖(rs k : ℂ) * g ((rs k : ℂ) * z)‖ ^ 2 * (1 - ‖z‖ ^ 2)))) atTop
      (𝓝 (ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
        (‖g z‖ ^ 2 * (1 - ‖z‖ ^ 2))))) := by
    intro z hz
    have hsC : Tendsto (fun k => (rs k : ℂ)) atTop (𝓝 1) := by
      have := (Complex.continuous_ofReal.tendsto 1).comp hlim
      rw [Complex.ofReal_one] at this
      exact this
    have h1 : Tendsto (fun k => (rs k : ℂ) * z) atTop (𝓝 z) := by
      simpa using hsC.mul_const z
    have hgz : ContinuousAt g z := hg.continuousOn.continuousAt (isOpen_ball.mem_nhds hz)
    have h2 : Tendsto (fun k => (rs k : ℂ) * g ((rs k : ℂ) * z)) atTop (𝓝 (g z)) := by
      simpa using hsC.mul (hgz.tendsto.comp h1)
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (((h2.norm.pow 2).mul_const _).const_mul _)
  have hmeas : ∀ k, AEMeasurable (fun z => ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) /
      ‖1 - conj ζ * z‖ ^ 2 * (‖(rs k : ℂ) * g ((rs k : ℂ) * z)‖ ^ 2 * (1 - ‖z‖ ^ 2))))
      (volume.restrict unitDisc) := fun k =>
    s02_vf_aem (hk.mul ((((s02_vf_dil hg (hr0 k) (hr1 k).le).1.continuousOn.norm.pow 2).mul
      (by fun_prop : Continuous fun z : ℂ => 1 - ‖z‖ ^ 2).continuousOn)))
  calc _ = ∫⁻ z in unitDisc, liminf (fun k => ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) /
          ‖1 - conj ζ * z‖ ^ 2 * (‖(rs k : ℂ) * g ((rs k : ℂ) * z)‖ ^ 2 * (1 - ‖z‖ ^ 2))))
          atTop := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet unitDisc)] with z hz
        exact (hpt z hz).liminf_eq.symm
    _ ≤ liminf (fun k => ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) /
          ‖1 - conj ζ * z‖ ^ 2 * (‖(rs k : ℂ) * g ((rs k : ℂ) * z)‖ ^ 2 * (1 - ‖z‖ ^ 2))))
          atTop := lintegral_liminf_le' hmeas
    _ ≤ M := liminf_le_of_frequently_le' (Frequently.of_forall fun k => hM _ (hr0 k) (hr1 k))

/-- Shen–Wei V_bwd helper (V-f, finiteness of the kernel integral; replaces [SW]'s use of B2 in
(4.6)): `s02_vf_absorb` for `g_s` (`ε = 1/2`, `r'` from `s02_vf_dil_small`; `s02_vf_dil`,
`s02_vf_dil_bloch`, `s02_vf_dil_fin`, `s02_vf_dil_B`) bounds `I_{g_s}(ζ)` uniformly in `s`;
then `s02_vf_fatou`. -/
theorem s02_vf_finite {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) (hgm : Measurable g)
    (hB : ∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) * ‖g z‖ ≤ 6)
    (hlb : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, r < 1 ∧ ∀ z : ℂ, r < ‖z‖ → ‖z‖ < 1 →
      (1 - ‖z‖ ^ 2) * ‖g z‖ < ε)
    (hS : ∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv g z - 1 / 2 * g z ^ 2‖ ^ 2 *
      (1 - ‖z‖ ^ 2) ^ 3) ≠ ⊤) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
      (‖g z‖ ^ 2 * (1 - ‖z‖ ^ 2))) ≠ ⊤ := by
  obtain ⟨r0, hr01, hr0s⟩ := hlb (1 / 2) (by norm_num)
  have hsm : ∀ z : ℂ, max r0 0 < ‖z‖ → ‖z‖ < 1 → (1 - ‖z‖ ^ 2) * ‖g z‖ ≤ 1 / 2 :=
    fun z h1 h2 => (hr0s z (lt_of_le_of_lt (le_max_left _ _) h1) h2).le
  obtain ⟨r', hr'0, hr'1, hr's⟩ := s02_vf_dil_small hg (by norm_num : (0 : ℝ) < 1 / 2)
    (le_max_right _ _) (max_lt hr01 one_pos) hsm
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (π * 36) + ENNReal.ofReal (8 / 3) *
      (ENNReal.ofReal ((1 + ‖ζ‖) / (1 - ‖ζ‖)) * ∫⁻ z in unitDisc,
        ENNReal.ofReal (‖deriv g z - 1 / 2 * g z ^ 2‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3)) +
      ENNReal.ofReal (64 * π / 3 * (1 / 2) ^ 2 + 4800 * π / (1 - r') ^ 3 * (1 - ‖ζ‖ ^ 2)))
    (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS)⟩,
      ENNReal.ofReal_ne_top⟩)
    (s02_vf_fatou hg hζ fun s hs0 hs1 => ?_)
  have hd := (s02_vf_dil hg hs0 hs1.le).1
  have hbl := s02_vf_dil_bloch hB hs0 hs1.le
  have h := s02_vf_absorb hd hbl (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hr'0 hr'1
    (hr's s hs0 hs1.le) hζ (s02_vf_dil_fin hg hs0 hs1 hζ)
  refine h.trans (add_le_add (add_le_add (ENNReal.ofReal_le_ofReal ?_)
    (mul_le_mul_right (s02_vf_dil_B hg hgm hs0 hs1.le hζ) _)) le_rfl)
  have hb := hbl ζ (mem_ball_zero_iff.mpr hζ)
  have hb0 : 0 ≤ (1 - ‖ζ‖ ^ 2) * ‖(s : ℂ) * g ((s : ℂ) * ζ)‖ :=
    mul_nonneg (by nlinarith [norm_nonneg ζ]) (norm_nonneg _)
  have h36 := pow_le_pow_left₀ hb0 hb 2
  have e : ‖(s : ℂ) * g ((s : ℂ) * ζ)‖ ^ 2 * (1 - ‖ζ‖ ^ 2) ^ 2 =
      ((1 - ‖ζ‖ ^ 2) * ‖(s : ℂ) * g ((s : ℂ) * ζ)‖) ^ 2 := by ring
  show π * (‖(s : ℂ) * g ((s : ℂ) * ζ)‖ ^ 2 * (1 - ‖ζ‖ ^ 2) ^ 2) ≤ π * 36
  rw [e]
  nlinarith [Real.pi_pos]

/-- Shen–Wei V_bwd helper (V-f = [SW] (V3) ⇒ (V2) given little Bloch): for `f` conformal on `𝔻` with
`(1 − |z|²)|N_f| → 0` and `|S_f|²(1 − |z|²)³ ∈ CM₀`, `log f' ∈ VMOA`. With `g = N_f`
(`s02_sw_logDeriv`, `s02_sw_bloch`): `s02_vf_finite`, then `s02_vf_absorb` bounds the kernel integral
of `|N_f|²(1 − |z|²) dA` by `π|N_f(ζ)|²(1 − |ζ|²)² + (8/3)·[kernel integral of λ_f] + c(ε, r)`;
`s02_vc_kernel_bound`/`s02_vc_of_kernel` give CM, `s02_vc_kernel_vanish`/`s02_vc_vanishing_of_kernel`
give CM₀. -/
theorem s02_vf_V2 {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (hlb : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, r < 1 ∧ ∀ z : ℂ, r < ‖z‖ → ‖z‖ < 1 →
      (1 - ‖z‖ ^ 2) * ‖deriv (deriv f) z / deriv f z‖ < ε)
    (hv : IsVanishingCarlesonDisk (schwarzCarlesonMeasure f)) :
    LogDerivVMOA f := by
  obtain ⟨hg, hSf⟩ := s02_sw_logDeriv hf
  have hgm : Measurable fun z => deriv (deriv f) z / deriv f z :=
    (measurable_deriv _).div (measurable_deriv _)
  have hB : ∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) * ‖deriv (deriv f) z / deriv f z‖ ≤ 6 :=
    fun z hz => s02_sw_bloch hf hz
  -- `λ_f` as a measure with a measurable density
  have hSm : Measurable fun z => ‖deriv (fun w => deriv (deriv f) w / deriv f w) z -
      1 / 2 * (deriv (deriv f) z / deriv f z) ^ 2‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3 :=
    (((measurable_deriv _).sub (measurable_const.mul (hgm.pow_const 2))).norm.pow_const 2).mul
      (by fun_prop : Continuous fun z : ℂ => (1 - ‖z‖ ^ 2) ^ 3).measurable
  have hlam : schwarzCarlesonMeasure f = (volume.restrict unitDisc).withDensity fun z =>
      ENNReal.ofReal (‖deriv (fun w => deriv (deriv f) w / deriv f w) z -
        1 / 2 * (deriv (deriv f) z / deriv f z) ^ 2‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) := by
    unfold schwarzCarlesonMeasure
    refine withDensity_congr_ae ((ae_restrict_iff' (measurableSet_ball :
      MeasurableSet unitDisc)).mpr (ae_of_all _ fun z hz => ?_))
    dsimp only
    rw [hSf z hz]
  have hS : ∫⁻ z in unitDisc, ENNReal.ofReal (‖deriv (fun w => deriv (deriv f) w / deriv f w) z -
      1 / 2 * (deriv (deriv f) z / deriv f z) ^ 2‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) ≠ ⊤ := by
    have h := s02_cm_total hv.1
    rwa [hlam, withDensity_apply (s := unitDisc) _ measurableSet_ball,
      Measure.restrict_restrict (s := unitDisc) measurableSet_ball, inter_self] at h
  have hdm : Measurable fun z => ‖deriv (deriv f) z / deriv f z‖ ^ 2 * (1 - ‖z‖ ^ 2) :=
    (hgm.norm.pow_const 2).mul (by fun_prop : Continuous fun z : ℂ => 1 - ‖z‖ ^ 2).measurable
  obtain ⟨C, hC0, hC⟩ := s02_vc_real hv.1
  have hBb : ∀ ζ : ℂ, ‖ζ‖ < 1 → ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) /
      ‖1 - conj ζ * z‖ ^ 2 * (‖deriv (fun w => deriv (deriv f) w / deriv f w) z -
        1 / 2 * (deriv (deriv f) z / deriv f z) ^ 2‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3)) ≤
      ENNReal.ofReal (108 * C) := fun ζ hζ => by
    have h := s02_vc_kernel_bound hC0 hC hζ
    rwa [hlam, s02_vf_kernel_wd hSm hζ] at h
  have hlb' : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ z : ℂ, r < ‖z‖ → ‖z‖ < 1 →
      (1 - ‖z‖ ^ 2) * ‖deriv (deriv f) z / deriv f z‖ ≤ ε := fun ε hε => by
    obtain ⟨r, hr1, hr⟩ := hlb ε hε
    exact ⟨max r 0, le_max_right _ _, max_lt hr1 one_pos,
      fun z h1 h2 => (hr z (lt_of_le_of_lt (le_max_left _ _) h1) h2).le⟩
  have hfin := fun ζ (hζ : ‖ζ‖ < 1) => s02_vf_finite hg hgm hB hlb hS hζ
  have hpi4 := Real.pi_le_four
  have hpi0 := Real.pi_pos
  show IsVanishingCarlesonDisk ((volume.restrict unitDisc).withDensity fun z =>
    ENNReal.ofReal (‖deriv (deriv f) z / deriv f z‖ ^ 2 * (1 - ‖z‖ ^ 2)))
  obtain ⟨r, hr0, hr1, hr⟩ := hlb' (1 / 2) (by norm_num)
  have hr1' : 0 < 1 - r := by linarith
  refine s02_vc_vanishing_of_kernel (s02_vc_of_kernel (M := π * 36 + 8 / 3 * (108 * C) +
      (64 * π / 3 * (1 / 2) ^ 2 + 4800 * π / (1 - r) ^ 3 * 1)) fun ζ hζ => ?_) fun η hη => ?_
  · rw [s02_vf_kernel_wd hdm hζ]
    have h := s02_vf_absorb hg hB (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hr0 hr1 hr hζ
      (hfin ζ hζ)
    have hζ0 := norm_nonneg ζ
    have h1ζ : 0 ≤ 1 - ‖ζ‖ ^ 2 := by nlinarith
    have hb := hB ζ (mem_ball_zero_iff.mpr hζ)
    have h36 := pow_le_pow_left₀ (mul_nonneg h1ζ (norm_nonneg _)) hb 2
    refine h.trans ?_
    calc _ ≤ ENNReal.ofReal (π * 36) + ENNReal.ofReal (8 / 3) * ENNReal.ofReal (108 * C) +
          ENNReal.ofReal (64 * π / 3 * (1 / 2) ^ 2 + 4800 * π / (1 - r) ^ 3 * 1) := by
          refine add_le_add (add_le_add (ENNReal.ofReal_le_ofReal ?_)
            (mul_le_mul_right (hBb ζ hζ) _)) (ENNReal.ofReal_le_ofReal ?_)
          · nlinarith
          · have : 0 ≤ 4800 * π / (1 - r) ^ 3 := by positivity
            nlinarith
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8 / 3),
            ← ENNReal.ofReal_add (by positivity) (by nlinarith),
            ← ENNReal.ofReal_add (by nlinarith) (by positivity)]
  · -- vanishing
    obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (1 / 2) (η / 200) := ⟨_, rfl⟩
    have hε0 : 0 < ε := by rw [hεdef]; positivity
    have hε1 : ε ≤ 1 / 2 := by rw [hεdef]; exact min_le_left _ _
    have hε2 : ε ≤ η / 200 := by rw [hεdef]; exact min_le_right _ _
    have hεε : ε ^ 2 ≤ 1 / 2 * (η / 200) := by nlinarith
    obtain ⟨r, hr0, hr1, hr⟩ := hlb' ε hε0
    have hr1' : 0 < 1 - r := by linarith
    obtain ⟨r2, hr21, H2⟩ := s02_vc_kernel_vanish hv (3 * η / 32) (by positivity)
    obtain ⟨c0, hc0def⟩ : ∃ c0 : ℝ, c0 = 4800 * π / (1 - r) ^ 3 := ⟨_, rfl⟩
    have hc0 : 0 < c0 := by rw [hc0def]; positivity
    refine ⟨max (max r r2) (1 - η / (16 * c0)), max_lt (max_lt hr1 hr21)
      (by have : 0 < η / (16 * c0) := by positivity
          linarith), fun ζ hζr hζ => ?_⟩
    have hζr1 : r < ‖ζ‖ := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hζr
    have hζr2 : r2 < ‖ζ‖ := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hζr
    have hζr3 : 1 - η / (16 * c0) < ‖ζ‖ := lt_of_le_of_lt (le_max_right _ _) hζr
    rw [s02_vf_kernel_wd hdm hζ]
    have h := s02_vf_absorb hg hB hε0.le (by nlinarith) hr0 hr1 hr hζ (hfin ζ hζ)
    have hBv : ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) /
        ‖1 - conj ζ * z‖ ^ 2 * (‖deriv (fun w => deriv (deriv f) w / deriv f w) z -
          1 / 2 * (deriv (deriv f) z / deriv f z) ^ 2‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3)) ≤
        ENNReal.ofReal (3 * η / 32) := by
      have h2 := H2 ζ hζr2 hζ
      rwa [hlam, s02_vf_kernel_wd hSm hζ] at h2
    have hζ0 := norm_nonneg ζ
    have h1ζ : 0 ≤ 1 - ‖ζ‖ ^ 2 := by nlinarith
    have hsmζ := hr ζ hζr1 hζ
    have hA : ‖deriv (deriv f) ζ / deriv f ζ‖ ^ 2 * (1 - ‖ζ‖ ^ 2) ^ 2 ≤ ε ^ 2 := by
      have := pow_le_pow_left₀ (mul_nonneg h1ζ (norm_nonneg _)) hsmζ 2
      nlinarith
    have hc : c0 * (1 - ‖ζ‖ ^ 2) ≤ η / 8 := by
      have h3 : 1 - ‖ζ‖ < η / (16 * c0) := by linarith
      have h4 : 1 - ‖ζ‖ ^ 2 ≤ 2 * (1 - ‖ζ‖) := by nlinarith
      have h5 : (1 - ‖ζ‖) * (16 * c0) < η := by rwa [lt_div_iff₀ (by positivity)] at h3
      nlinarith
    refine h.trans ?_
    rw [← hc0def]
    calc _ ≤ ENNReal.ofReal (η / 4) + ENNReal.ofReal (8 / 3) * ENNReal.ofReal (3 * η / 32) +
          ENNReal.ofReal (3 * η / 8) := by
          refine add_le_add (add_le_add (ENNReal.ofReal_le_ofReal ?_)
            (mul_le_mul_right hBv _)) (ENNReal.ofReal_le_ofReal ?_)
          · nlinarith
          · nlinarith
      _ = ENNReal.ofReal (7 * η / 8) := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8 / 3),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
      _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal (by linarith)

/-- Shen–Wei V_bwd helper (W-BP B1, boundedness): the bounded component of a bounded quasicircle is
bounded (`F` is continuous, `Ω = F(𝔻) ⊆ F(D̄)`, as in `s07_disk_preimage_tendsto`). -/
theorem s02_bp_bounded {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K) :
    ∃ R : ℝ, 0 < R ∧ ∀ w ∈ Ω, ‖w‖ ≤ R := by
  obtain ⟨F, hFq, -, hF1, -⟩ := hq
  have hK : IsCompact (F '' closedBall 0 1) :=
    (isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn (hFq.2.2.1.1.mono (subset_univ _))
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨max R 1, lt_max_of_lt_right one_pos, fun w hw => ?_⟩
  rw [← hF1] at hw
  have h := hR (image_mono ball_subset_closedBall hw)
  rw [mem_closedBall_zero_iff] at h
  exact h.trans (le_max_left _ _)

/-- Shen–Wei V_bwd helper (W-BP B1, upper bound for `e`): if `Ω ⊆ D̄(0, R)` then
`(1 − |z|)|f'(z)| ≤ (1 − |z|²)|f'(z)| ≤ 4 dist(f(z), ∂Ω) ≤ 4(2R + 1)` (`lem_koebe_a`; `R + 1 ∉ Ω`). -/
theorem s02_bp_upper {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {R : ℝ}
    (hR : ∀ w ∈ Ω, ‖w‖ ≤ R) {z : ℂ} (hz : z ∈ unitDisc) :
    (1 - ‖z‖) ^ 2 * ‖deriv f z‖ ^ 2 ≤ (4 * (2 * R + 1)) ^ 2 := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hfz : f z ∈ Ω := hf.2.2 ▸ mem_image_of_mem f hz
  have hfzR := hR _ hfz
  have hp : ((R + 1 : ℝ) : ℂ) ∉ Ω := fun h => by
    have := hR _ h
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    linarith [le_abs_self (R + 1)]
  have hinf : infDist (f z) Ωᶜ ≤ 2 * R + 1 := by
    refine (infDist_le_dist_of_mem (mem_compl hp)).trans ?_
    rw [dist_eq_norm]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [norm_nonneg (f z)])]
    linarith
  have hk := (lem_koebe_a hf hz).2.1
  have h1 : (1 - ‖z‖) * ‖deriv f z‖ ≤ 4 * (2 * R + 1) := by
    have h2 : (1 - ‖z‖) * ‖deriv f z‖ ≤ (1 - ‖z‖ ^ 2) * ‖deriv f z‖ := by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      nlinarith [norm_nonneg z]
    linarith
  have h0 : 0 ≤ (1 - ‖z‖) * ‖deriv f z‖ := mul_nonneg (by linarith) (norm_nonneg _)
  calc (1 - ‖z‖) ^ 2 * ‖deriv f z‖ ^ 2 = ((1 - ‖z‖) * ‖deriv f z‖) ^ 2 := by ring
    _ ≤ (4 * (2 * R + 1)) ^ 2 := pow_le_pow_left₀ h0 h1 2

/-- Shen–Wei V_bwd helper (W-BP B1, lower bound for `e` on a circle): `f'` is continuous and nonvanishing on
`𝔻` (`deriv_ne_zero_of_injOn`), so it has a positive minimum on the compact circle `|z| = ρ₀`. -/
theorem s02_bp_lower {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {ρ₀ : ℝ}
    (hρ₀ : 0 ≤ ρ₀) (hρ₀1 : ρ₀ < 1) :
    ∃ m : ℝ, 0 < m ∧ ∀ ζ : ℂ, ‖ζ‖ = 1 → m ≤ (1 - ρ₀) ^ 2 * ‖deriv f ((ρ₀ : ℂ) * ζ)‖ ^ 2 := by
  have han : AnalyticOnNhd ℂ f unitDisc := hf.1.analyticOnNhd isOpen_ball
  have hmaps : MapsTo (fun ζ : ℂ => (ρ₀ : ℂ) * ζ) (sphere (0 : ℂ) 1) unitDisc := fun ζ hζ => by
    rw [mem_sphere_zero_iff_norm] at hζ
    have h : ‖(ρ₀ : ℂ) * ζ‖ < 1 := by
      rw [norm_mul, hζ, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ₀]
      exact hρ₀1
    exact mem_ball_zero_iff.mpr h
  have hcont : ContinuousOn (fun ζ : ℂ => (1 - ρ₀) ^ 2 * ‖deriv f ((ρ₀ : ℂ) * ζ)‖ ^ 2)
      (sphere (0 : ℂ) 1) := by
    refine continuousOn_const.mul ((ContinuousOn.norm ?_).pow 2)
    exact han.deriv.continuousOn.comp (continuous_const.mul continuous_id).continuousOn hmaps
  obtain ⟨ζ₀, hζ₀, hmin⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont
  refine ⟨(1 - ρ₀) ^ 2 * ‖deriv f ((ρ₀ : ℂ) * ζ₀)‖ ^ 2, ?_, fun ζ hζ => ?_⟩
  · have hd := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 (hmaps hζ₀)
    have : 0 < 1 - ρ₀ := by linarith
    positivity
  · exact hmin (mem_sphere_zero_iff_norm.mpr hζ)

/-- Shen–Wei V_bwd helper (W-BP B2, the ray stays in `𝔻`): `ρζ ∈ 𝔻` for `|ζ| = 1`, `0 ≤ ρ < 1`. -/
theorem s02_bp_ray {ζ : ℂ} (hζ : ‖ζ‖ = 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (ρ : ℂ) * ζ ∈ unitDisc := by
  have h : ‖(ρ : ℂ) * ζ‖ < 1 := by
    rw [norm_mul, hζ, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0]
    exact hρ1
  exact mem_ball_zero_iff.mpr h

/-- Shen–Wei V_bwd helper (W-BP B2, the ray as a real path): `t ↦ tζ` has derivative `ζ`. -/
theorem s02_bp_path (ζ : ℂ) (ρ : ℝ) : HasDerivAt (fun t : ℝ => (t : ℂ) * ζ) ζ ρ := by
  simpa using ((hasDerivAt_id ρ).ofReal_comp).mul_const ζ

/-- Shen–Wei V_bwd helper (W-BP B2, radial Riccati equation): with `N = f''/f'`,
`w(t) = −((1 − t)/2) ζ N(tζ)` satisfies `(1 − ρ) w'(ρ) = −w − w² − ((1 − ρ)²/2) ζ² S_f(ρζ)`
(`s02_sw_logDeriv`: `N' = S_f + ½N²`; chain rule along `t ↦ tζ`). -/
theorem s02_bp_w_deriv {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {ζ : ℂ}
    (hζ : ‖ζ‖ = 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    HasDerivAt (fun t : ℝ => -(((1 - t) / 2 : ℝ) : ℂ) * ζ *
        (deriv (deriv f) ((t : ℂ) * ζ) / deriv f ((t : ℂ) * ζ)))
      ((-(-(((1 - ρ) / 2 : ℝ) : ℂ) * ζ * (deriv (deriv f) ((ρ : ℂ) * ζ) / deriv f ((ρ : ℂ) * ζ))) -
          (-(((1 - ρ) / 2 : ℝ) : ℂ) * ζ *
            (deriv (deriv f) ((ρ : ℂ) * ζ) / deriv f ((ρ : ℂ) * ζ))) ^ 2 +
          -(((1 - ρ) ^ 2 / 2 : ℝ) : ℂ) * ζ ^ 2 * schwarzian f ((ρ : ℂ) * ζ)) /
        ((1 - ρ : ℝ) : ℂ)) ρ := by
  obtain ⟨hNd, hSN⟩ := s02_sw_logDeriv hf
  have hp : (ρ : ℂ) * ζ ∈ unitDisc := s02_bp_ray hζ hρ0 hρ1
  have hNp := (hNd.differentiableAt (isOpen_ball.mem_nhds hp)).hasDerivAt
  have hcomp := hNp.comp ρ (s02_bp_path ζ ρ)
  have hc : HasDerivAt (fun t : ℝ => -(((1 - t) / 2 : ℝ) : ℂ)) ((1 / 2 : ℝ) : ℂ) ρ := by
    have h1 : HasDerivAt (fun t : ℝ => (1 - t) / 2) (-1 / 2) ρ := by
      refine (((hasDerivAt_id ρ).const_sub 1).div_const 2).congr_deriv ?_
      norm_num
    refine h1.ofReal_comp.neg.congr_deriv ?_
    push_cast
    ring
  have hprod := (hc.mul_const ζ).mul hcomp
  refine hprod.congr_deriv ?_
  simp only [Function.comp_apply]
  rw [hSN _ hp]
  have h1 : ((1 - ρ : ℝ) : ℂ) ≠ 0 := by
    have : (1 - ρ) ≠ 0 := by linarith
    exact_mod_cast this
  rw [eq_div_iff h1]
  push_cast
  ring

/-- Shen–Wei V_bwd helper (W-BP B2, growth of `e`): `e(t) = (1 − t)²|f'(tζ)|²` satisfies
`(1 − ρ) e'(ρ) = e (−2 − 4 Re w)` with `w` as in `s02_bp_w_deriv`, since `(|f'(tζ)|²)' = 2|f'|² Re(ζN)` and
`ζN = −2w/(1 − ρ)` (`HasDerivAt.norm_sq`). -/
theorem s02_bp_e_deriv {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {ζ : ℂ}
    (hζ : ‖ζ‖ = 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    HasDerivAt (fun t : ℝ => (1 - t) ^ 2 * ‖deriv f ((t : ℂ) * ζ)‖ ^ 2)
      ((1 - ρ) ^ 2 * ‖deriv f ((ρ : ℂ) * ζ)‖ ^ 2 *
          (-2 - 4 * (-(((1 - ρ) / 2 : ℝ) : ℂ) * ζ *
            (deriv (deriv f) ((ρ : ℂ) * ζ) / deriv f ((ρ : ℂ) * ζ))).re) / (1 - ρ)) ρ := by
  have han : AnalyticOnNhd ℂ f unitDisc := hf.1.analyticOnNhd isOpen_ball
  have hp : (ρ : ℂ) * ζ ∈ unitDisc := s02_bp_ray hζ hρ0 hρ1
  have ha := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hp
  have hf'p := (han.deriv _ hp).differentiableAt.hasDerivAt
  have hn := (hf'p.comp ρ (s02_bp_path ζ ρ)).norm_sq
  have hq : HasDerivAt (fun t : ℝ => (1 - t) ^ 2) (-(2 * (1 - ρ))) ρ := by
    refine (((hasDerivAt_id ρ).const_sub 1).pow 2).congr_deriv ?_
    simp
  have hprod := hq.mul hn
  refine hprod.congr_deriv ?_
  simp only [Function.comp_apply]
  rw [Complex.inner]
  set a := deriv f ((ρ : ℂ) * ζ)
  set b := deriv (deriv f) ((ρ : ℂ) * ζ)
  have hW : -(((1 - ρ) / 2 : ℝ) : ℂ) * ζ * (b / a) = ((-((1 - ρ) / 2) : ℝ) : ℂ) * (ζ * (b / a)) := by
    push_cast
    ring
  have hkey : ‖a‖ ^ 2 * (ζ * (b / a)).re = (b * ζ * conj a).re := by
    have h : b * ζ * conj a = ((‖a‖ ^ 2 : ℝ) : ℂ) * (ζ * (b / a)) := by
      have hm := Complex.mul_conj a
      rw [Complex.normSq_eq_norm_sq] at hm
      rw [← hm]
      field_simp
    rw [h, Complex.re_ofReal_mul]
  have h1 : (1 - ρ) ≠ 0 := by linarith
  rw [hW, Complex.re_ofReal_mul, ← hkey]
  field_simp
  ring

/-- Shen–Wei V_bwd helper (W-BP B3, bad phase): while `|w + 1| ≤ c|w|` (`c ≤ 1/5`, so `Re w ≤ −3/4`),
`e(t)(1 − t)` is nondecreasing; with `e ≤ M` this bounds `1 − ρ` from below. -/
theorem s02_bp_bad {ρ₀ c m M : ℝ} {w : ℝ → ℂ} {e : ℝ → ℝ} (hc1 : c ≤ 1 / 5)
    (he : ∀ ρ ∈ Ico ρ₀ 1, HasDerivAt e (e ρ * (-2 - 4 * (w ρ).re) / (1 - ρ)) ρ)
    (he0 : ∀ ρ ∈ Ico ρ₀ 1, 0 < e ρ) (heM : ∀ ρ ∈ Ico ρ₀ 1, e ρ ≤ M) (hm : m ≤ e ρ₀) {ρ : ℝ}
    (hρ : ρ ∈ Ico ρ₀ 1) (hbad : ∀ t ∈ Icc ρ₀ ρ, ‖w t + 1‖ ≤ c * ‖w t‖) :
    m * (1 - ρ₀) ≤ M * (1 - ρ) := by
  have hsub : Icc ρ₀ ρ ⊆ Ico ρ₀ 1 := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hρ.2⟩
  have hg' : ∀ t ∈ Icc ρ₀ ρ,
      HasDerivAt (fun t => e t * (1 - t)) (e t * (-3 - 4 * (w t).re)) t := by
    intro t ht
    have h := (he t (hsub ht)).mul ((hasDerivAt_id t).const_sub 1)
    refine h.congr_deriv ?_
    have : 1 - t ≠ 0 := by linarith [(hsub ht).2]
    simp only [id]
    field_simp
    ring
  have hpos : ∀ t ∈ Icc ρ₀ ρ, 0 ≤ e t * (-3 - 4 * (w t).re) := by
    intro t ht
    have h1 := hbad t ht
    have hn : ‖w t‖ ≤ 5 / 4 := by
      have h2 : ‖w t‖ ≤ ‖w t + 1‖ + 1 := by
        have := norm_sub_le (w t + 1) 1
        simpa using this
      nlinarith [norm_nonneg (w t)]
    have hre : (w t).re + 1 ≤ ‖w t + 1‖ := by
      have := Complex.re_le_norm (w t + 1)
      simpa using this
    have hc0 : (w t).re ≤ -3 / 4 := by nlinarith [norm_nonneg (w t)]
    exact mul_nonneg (he0 t (hsub ht)).le (by linarith)
  have hmono : MonotoneOn (fun t => e t * (1 - t)) (Icc ρ₀ ρ) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t ht => (hg' t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hg' t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hpos t (interior_subset ht))
  have h := hmono ⟨le_rfl, hρ.1⟩ ⟨hρ.1, le_rfl⟩ hρ.1
  simp only at h
  calc m * (1 - ρ₀) ≤ e ρ₀ * (1 - ρ₀) := mul_le_mul_of_nonneg_right hm (by linarith [hρ.1, hρ.2])
    _ ≤ e ρ * (1 - ρ) := h
    _ ≤ M * (1 - ρ) := mul_le_mul_of_nonneg_right (heM ρ hρ) (by linarith [hρ.2])

/-- Shen–Wei V_bwd helper (W-BP B3, the Riccati equation for `z = 1 + 1/w`): where `w ≠ 0`,
`(1 − t) z' = z − Q/w²`. -/
theorem s02_bp_zid {w w' Q : ℂ} {t : ℝ} (hw : w ≠ 0) (ht : t < 1)
    (hw' : w' = (-w - w ^ 2 + Q) / ((1 - t : ℝ) : ℂ)) :
    (-(w ^ 2)⁻¹ * w') * ((1 - t : ℝ) : ℂ) = (1 + w⁻¹) - Q / w ^ 2 := by
  have h1 : ((1 - t : ℝ) : ℂ) ≠ 0 := by
    have : (1 - t) ≠ 0 := by linarith
    exact_mod_cast this
  rw [hw']
  field_simp
  ring

/-- Shen–Wei V_bwd helper (W-BP B3, escape phase): with `c = 128ε`, if `|w(σ) + 1| > c|w(σ)|` then `|w|`
drops to `≤ 1/8` before `1 − c²(1 − σ)/81`: while `|w| > 1/8`, `|z|²(1 − t)` (`z = 1 + 1/w`) stays
`≥ c²(1 − σ)` (barrier `image_le_of_deriv_right_lt_deriv_boundary'`, since
`(|z|²(1 − t))' ≥ |z|(|z| − c) > 0` there), which forces `|z| ≥ 9` at the end. -/
theorem s02_bp_escape {ρ₀ ε σ : ℝ} {w Q : ℝ → ℂ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 1000)
    (hw : ∀ ρ ∈ Ico ρ₀ 1, HasDerivAt w ((-w ρ - w ρ ^ 2 + Q ρ) / ((1 - ρ : ℝ) : ℂ)) ρ)
    (hQ : ∀ ρ ∈ Ico ρ₀ 1, ‖Q ρ‖ ≤ ε) (hσ : σ ∈ Ico ρ₀ 1)
    (hgood : 128 * ε * ‖w σ‖ < ‖w σ + 1‖) :
    ∃ τ ∈ Icc σ (1 - (128 * ε) ^ 2 * (1 - σ) / 81), ‖w τ‖ ≤ 1 / 8 := by
  by_contra hcon
  push Not at hcon
  set c : ℝ := 128 * ε with hcdef
  set ρc : ℝ := 1 - c ^ 2 * (1 - σ) / 81 with hρcdef
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 / 5 := by rw [hcdef]; linarith
  have hσ1 : 0 < 1 - σ := by linarith [hσ.2]
  have hρc1 : ρc < 1 := by
    rw [hρcdef]
    have : 0 < c ^ 2 * (1 - σ) / 81 := by positivity
    linarith
  have hσρc : σ ≤ ρc := by
    rw [hρcdef]
    have : c ^ 2 * (1 - σ) / 81 ≤ 1 - σ := by
      have : c ^ 2 ≤ 81 := by nlinarith
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 81)]
      nlinarith
    linarith
  have hsub : Icc σ ρc ⊆ Ico ρ₀ 1 := fun t ht => ⟨hσ.1.trans ht.1, lt_of_le_of_lt ht.2 hρc1⟩
  have hw8 : ∀ t ∈ Icc σ ρc, 1 / 8 < ‖w t‖ := fun t ht => hcon t ht
  have hw0 : ∀ t ∈ Icc σ ρc, w t ≠ 0 := fun t ht h => by
    have := hw8 t ht
    rw [h, norm_zero] at this
    linarith
  -- `z = 1 + 1/w` and `F = |z|²(1 − t)`
  have hz' : ∀ t ∈ Icc σ ρc, HasDerivAt (fun t => 1 + (w t)⁻¹)
      (-(w t ^ 2)⁻¹ * ((-w t - w t ^ 2 + Q t) / ((1 - t : ℝ) : ℂ))) t := fun t ht =>
    ((hasDerivAt_inv (hw0 t ht)).comp t (hw t (hsub ht))).const_add 1
  have hF' : ∀ t ∈ Icc σ ρc, HasDerivAt (fun t => ‖1 + (w t)⁻¹‖ ^ 2 * (1 - t))
      (2 * inner ℝ (1 + (w t)⁻¹) (-(w t ^ 2)⁻¹ * ((-w t - w t ^ 2 + Q t) / ((1 - t : ℝ) : ℂ))) *
        (1 - t) + ‖1 + (w t)⁻¹‖ ^ 2 * (-1)) t := fun t ht =>
    ((hz' t ht).norm_sq).mul ((hasDerivAt_id t).const_sub 1)
  -- the derivative is positive where `|z| > c`
  have hpos : ∀ t ∈ Icc σ ρc, c < ‖1 + (w t)⁻¹‖ →
      0 < 2 * inner ℝ (1 + (w t)⁻¹)
        (-(w t ^ 2)⁻¹ * ((-w t - w t ^ 2 + Q t) / ((1 - t : ℝ) : ℂ))) * (1 - t) +
        ‖1 + (w t)⁻¹‖ ^ 2 * (-1) := by
    intro t ht hzc
    set z := 1 + (w t)⁻¹ with hz
    have hid := s02_bp_zid (hw0 t ht) (hsub ht).2 rfl (Q := Q t)
    rw [Complex.inner]
    have h1 : ((-(w t ^ 2)⁻¹ * ((-w t - w t ^ 2 + Q t) / ((1 - t : ℝ) : ℂ))) * conj z).re * (1 - t) =
        ((z - Q t / w t ^ 2) * conj z).re := by
      rw [← hid]
      rw [show (-(w t ^ 2)⁻¹ * ((-w t - w t ^ 2 + Q t) / ((1 - t : ℝ) : ℂ)) * ((1 - t : ℝ) : ℂ) *
          conj z) = ((1 - t : ℝ) : ℂ) * ((-(w t ^ 2)⁻¹ *
            ((-w t - w t ^ 2 + Q t) / ((1 - t : ℝ) : ℂ))) * conj z) by ring]
      rw [Complex.re_ofReal_mul]
      ring
    have h2 : ((z - Q t / w t ^ 2) * conj z).re = ‖z‖ ^ 2 - (Q t / w t ^ 2 * conj z).re := by
      rw [sub_mul, Complex.sub_re, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.ofReal_re]
    have h3 : (Q t / w t ^ 2 * conj z).re ≤ 64 * ε * ‖z‖ := by
      refine (Complex.re_le_norm _).trans ?_
      rw [norm_mul, norm_div, norm_pow, Complex.norm_conj]
      have hw2 : 1 / 64 < ‖w t‖ ^ 2 := by nlinarith [hw8 t ht]
      have hQt := hQ t (hsub ht)
      have : ‖Q t‖ / ‖w t‖ ^ 2 ≤ 64 * ε := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have h4 : 2 * ((-(w t ^ 2)⁻¹ * ((-w t - w t ^ 2 + Q t) / ((1 - t : ℝ) : ℂ))) * conj z).re *
        (1 - t) = 2 * (((-(w t ^ 2)⁻¹ * ((-w t - w t ^ 2 + Q t) / ((1 - t : ℝ) : ℂ))) *
          conj z).re * (1 - t)) := by ring
    rw [h4, h1, h2]
    have : c * ‖z‖ < ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    rw [hcdef] at this
    nlinarith [norm_nonneg z]
  -- barrier: `F ≥ c²(1 − σ)` on `[σ, ρc]`
  have hzσ : c < ‖1 + (w σ)⁻¹‖ := by
    have hwσ := hw0 σ ⟨le_rfl, hσρc⟩
    have : 1 + (w σ)⁻¹ = (w σ + 1) / w σ := by field_simp
    rw [this, norm_div, lt_div_iff₀ (norm_pos_iff.mpr hwσ)]
    exact hgood
  have hbar := image_le_of_deriv_right_lt_deriv_boundary'
    (f := fun t => -(‖1 + (w t)⁻¹‖ ^ 2 * (1 - t))) (a := σ) (b := ρc)
    (B := fun _ => -(c ^ 2 * (1 - σ))) (B' := fun _ => 0)
    (fun t ht => (hF' t ht).continuousAt.neg.continuousWithinAt)
    (fun t ht => ((hF' t (Ico_subset_Icc_self ht)).neg).hasDerivWithinAt)
    (by
      simp only [neg_le_neg_iff]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0.le hzσ.le 2) hσ1.le)
    continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _)
    (by
      intro t ht hft
      simp only [neg_inj] at hft
      have hzc : c < ‖1 + (w t)⁻¹‖ := by
        rcases eq_or_lt_of_le ht.1 with h | h
        · rw [← h]; exact hzσ
        · have h1t : 0 < 1 - t := by linarith [ht.2, hρc1]
          have : c ^ 2 < ‖1 + (w t)⁻¹‖ ^ 2 := by
            have h5 : c ^ 2 * (1 - t) < c ^ 2 * (1 - σ) := by
              have : 0 < c ^ 2 := by positivity
              nlinarith
            rw [← hft] at h5
            exact lt_of_mul_lt_mul_right h5 h1t.le
          exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this
      have := hpos t (Ico_subset_Icc_self ht) hzc
      linarith)
  have hend := hbar ⟨hσρc, le_rfl⟩
  simp only [neg_le_neg_iff] at hend
  have h81 : (81 : ℝ) ≤ ‖1 + (w ρc)⁻¹‖ ^ 2 := by
    have h1 : 1 - ρc = c ^ 2 * (1 - σ) / 81 := by rw [hρcdef]; ring
    rw [h1] at hend
    have hpos' : 0 < c ^ 2 * (1 - σ) := by positivity
    nlinarith
  have h9 : 9 ≤ ‖1 + (w ρc)⁻¹‖ := by nlinarith [norm_nonneg (1 + (w ρc)⁻¹)]
  have h8 : 8 ≤ ‖w ρc‖⁻¹ := by
    have := norm_add_le 1 (w ρc)⁻¹
    rw [norm_one, norm_inv] at this
    linarith
  have hwpos : 0 < ‖w ρc‖ := norm_pos_iff.mpr (hw0 ρc ⟨hσρc, le_rfl⟩)
  have := hw8 ρc ⟨hσρc, le_rfl⟩
  have : ‖w ρc‖ ≤ 1 / 8 := by
    rw [le_inv_comm₀ (by norm_num) hwpos] at h8
    linarith
  linarith

/-- Shen–Wei V_bwd helper (W-BP B3, trap phase): once `|w(τ)| ≤ 1/8`,
`|w(ρ)|² ≤ 9ε² + (1 − ρ)/(64(1 − τ))` for `ρ ≥ τ` (barrier
`image_le_of_deriv_right_lt_deriv_boundary'`: on the barrier `|w| = a ∈ [3ε, 0.1251]`, so
`(1 − t)(|w|²)' ≤ −2a² + 2a³ + 2εa < −a²`). -/
theorem s02_bp_trap {ρ₀ ε τ : ℝ} {w Q : ℝ → ℂ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 1000)
    (hw : ∀ ρ ∈ Ico ρ₀ 1, HasDerivAt w ((-w ρ - w ρ ^ 2 + Q ρ) / ((1 - ρ : ℝ) : ℂ)) ρ)
    (hQ : ∀ ρ ∈ Ico ρ₀ 1, ‖Q ρ‖ ≤ ε) (hτ : τ ∈ Ico ρ₀ 1) (htrap : ‖w τ‖ ≤ 1 / 8) :
    ∀ ρ ∈ Ico τ 1, ‖w ρ‖ ^ 2 ≤ 9 * ε ^ 2 + (1 - ρ) / (64 * (1 - τ)) := by
  intro ρ hρ
  have hτ1 : 0 < 1 - τ := by linarith [hτ.2]
  have hsub : Icc τ ρ ⊆ Ico ρ₀ 1 := fun t ht => ⟨hτ.1.trans ht.1, lt_of_le_of_lt ht.2 hρ.2⟩
  have hV' : ∀ t ∈ Icc τ ρ, HasDerivAt (fun t => ‖w t‖ ^ 2)
      (2 * inner ℝ (w t) ((-w t - w t ^ 2 + Q t) / ((1 - t : ℝ) : ℂ))) t :=
    fun t ht => (hw t (hsub ht)).norm_sq
  have hB' : ∀ t, HasDerivAt (fun t => 9 * ε ^ 2 + (1 - t) / (64 * (1 - τ)))
      (-1 / (64 * (1 - τ))) t := fun t => by
    have h := (((hasDerivAt_id t).const_sub 1).div_const (64 * (1 - τ))).const_add (9 * ε ^ 2)
    refine h.congr_deriv ?_
    ring
  have hbar := image_le_of_deriv_right_lt_deriv_boundary'
    (f := fun t => ‖w t‖ ^ 2) (a := τ) (b := ρ)
    (fun t ht => (hV' t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hV' t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by
      rw [show (1 - τ) / (64 * (1 - τ)) = 1 / 64 by field_simp]
      have : ‖w τ‖ ^ 2 ≤ 1 / 64 := by nlinarith [norm_nonneg (w τ)]
      nlinarith)
    (fun t _ => (hB' t).continuousAt.continuousWithinAt)
    (fun t _ => (hB' t).hasDerivWithinAt)
    (by
      intro t ht hft
      have ht' := hsub (Ico_subset_Icc_self ht)
      have h1t : 0 < 1 - t := by linarith [ht'.2]
      set a := ‖w t‖ with ha
      have hrat : (1 - t) / (1 - τ) ≤ 1 := by
        rw [div_le_one hτ1]
        linarith [ht.1]
      have hrat0 : 0 ≤ (1 - t) / (1 - τ) := by positivity
      have hft' : a ^ 2 = 9 * ε ^ 2 + (1 - t) / (1 - τ) / 64 := by
        rw [hft]
        field_simp
      have hε2 : ε ^ 2 ≤ 1 / 1000000 := by nlinarith
      have ha0 : 0 ≤ a := norm_nonneg _
      have ha3 : 3 * ε ≤ a := by nlinarith
      have hab : a ≤ 1251 / 10000 := by nlinarith
      have hapos : 0 < a := by linarith
      rw [Complex.inner]
      set X := ((-w t - w t ^ 2 + Q t) / ((1 - t : ℝ) : ℂ)) * conj (w t) with hX
      have hre : X.re * (1 - t) = -a ^ 2 - (w t ^ 2 * conj (w t)).re + (Q t * conj (w t)).re := by
        have hne : ((1 - t : ℝ) : ℂ) ≠ 0 := by
          have : (1 - t) ≠ 0 := by linarith
          exact_mod_cast this
        have h1 : X = ((1 / (1 - t) : ℝ) : ℂ) * ((-w t - w t ^ 2 + Q t) * conj (w t)) := by
          rw [hX]
          push_cast
          field_simp
        have h2 : ((-w t - w t ^ 2 + Q t) * conj (w t)).re =
            -a ^ 2 - (w t ^ 2 * conj (w t)).re + (Q t * conj (w t)).re := by
          have h3 : (-w t - w t ^ 2 + Q t) * conj (w t) =
              -(w t * conj (w t)) - w t ^ 2 * conj (w t) + Q t * conj (w t) := by ring
          rw [h3, Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_conj,
            Complex.normSq_eq_norm_sq, Complex.ofReal_re]
        rw [h1, Complex.re_ofReal_mul, h2]
        field_simp
      have hc1 : -(w t ^ 2 * conj (w t)).re ≤ a ^ 3 := by
        have h1 := Complex.abs_re_le_norm (w t ^ 2 * conj (w t))
        rw [norm_mul, norm_pow, Complex.norm_conj] at h1
        have h2 := neg_abs_le (w t ^ 2 * conj (w t)).re
        nlinarith
      have hc2 : (Q t * conj (w t)).re ≤ ε * a := by
        refine (Complex.re_le_norm _).trans ?_
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_right (hQ t ht') ha0
      have hkey : (1 - t) * (2 * X.re) < (1 - t) * (-1 / (64 * (1 - τ))) := by
        have e1 : (1 - t) * (-1 / (64 * (1 - τ))) = -((1 - t) / (1 - τ) / 64) := by
          field_simp
        rw [e1]
        have e2 : (1 - t) * (2 * X.re) = 2 * (X.re * (1 - t)) := by ring
        rw [e2, hre]
        nlinarith
      exact lt_of_mul_lt_mul_left hkey h1t.le)
  exact hbar ⟨hρ.1, le_rfl⟩

/-- Shen–Wei V_bwd helper (W-BP B3, the ODE lemma; pure real analysis): let `(1 − ρ) w' = −w − w² + Q`,
`(1 − ρ) e' = e (−2 − 4 Re w)` on `[ρ₀, 1)` with `|Q| ≤ ε ≤ 1/1000`, `0 < e ≤ M` and `e(ρ₀) ≥ m > 0`.
Then `|w| ≤ 4ε` on `[ρ₁, 1)` for a `ρ₁ < 1` depending only on `ρ₀, ε, m, M`. Three phases, with
`c = 32ε` and `P = |w + 1|² − c²|w|²` (planned helpers, each by `image_le_of_deriv_right_lt_deriv_boundary'`
or a monotone product):
* bad phase `P ≤ 0` (`w` near `−1`): `Re w ≤ −1 + 64ε`, so `e (1 − ρ)` is nondecreasing; with `e ≤ M` it ends
  before `1 − ρ = m(1 − ρ₀)/M`. `{P > 0}` is forward invariant (`(1 − ρ)P' = 2c²|w|² + O(ε|w|) > 0` on `P = 0`);
* escape `P > 0`, `|w| > 1/4`: `z = 1 + 1/w` has `(1 − ρ)z' = z − Q/w²`, so `|z|²(1 − ρ)` is nondecreasing
  while `|z| ≥ c`, and `|z| < 5` there;
* trap `|w| ≤ 1/4` (forward invariant): `V = |w|²` has `(1 − ρ)V' ≤ −V/2` while `V ≥ 4ε²`, so `V²/(1 − ρ)` is
  nonincreasing, then `{V ≤ 4ε²}` is forward invariant. -/
theorem s02_bp_ode {ρ₀ ε m M : ℝ} (hρ₀ : 0 ≤ ρ₀) (hρ₀1 : ρ₀ < 1) (hε : 0 < ε) (hε1 : ε ≤ 1 / 1000)
    (hm : 0 < m) :
    ∃ ρ₁ : ℝ, ρ₁ < 1 ∧ ∀ (w : ℝ → ℂ) (e : ℝ → ℝ) (Q : ℝ → ℂ),
      (∀ ρ ∈ Ico ρ₀ 1, HasDerivAt w ((-w ρ - w ρ ^ 2 + Q ρ) / ((1 - ρ : ℝ) : ℂ)) ρ) →
      (∀ ρ ∈ Ico ρ₀ 1, HasDerivAt e (e ρ * (-2 - 4 * (w ρ).re) / (1 - ρ)) ρ) →
      (∀ ρ ∈ Ico ρ₀ 1, ‖Q ρ‖ ≤ ε) → (∀ ρ ∈ Ico ρ₀ 1, 0 < e ρ) → (∀ ρ ∈ Ico ρ₀ 1, e ρ ≤ M) →
      m ≤ e ρ₀ → ∀ ρ ∈ Ico ρ₁ 1, ‖w ρ‖ ≤ 4 * ε := by
  -- `hρ₀ : 0 ≤ ρ₀` is not needed (the statement stays true without it); it matches the ray setting.
  have _hρ₀ := hρ₀
  have h1ρ₀ : 0 < 1 - ρ₀ := by linarith
  set L : ℝ := m * (1 - ρ₀) / max M m with hL
  have hmax : 0 < max M m := lt_max_of_lt_right hm
  have hL0 : 0 < L := by positivity
  have hc0 : 0 < 128 * ε := by positivity
  refine ⟨1 - 448 * ε ^ 2 * (128 * ε) ^ 2 * L / 162, ?_, ?_⟩
  · have : 0 < 448 * ε ^ 2 * (128 * ε) ^ 2 * L / 162 := by positivity
    linarith
  intro w e Q hw he hQ he0 heM hm0 ρ hρ
  have hρ₀mem : ρ₀ ∈ Ico ρ₀ 1 := ⟨le_rfl, hρ₀1⟩
  have hmM : m ≤ M := hm0.trans (heM ρ₀ hρ₀mem)
  have hmaxM : max M m = M := max_eq_left hmM
  have hMpos : 0 < M := hm.trans_le hmM
  have hLle : L ≤ 1 - ρ₀ := by
    rw [hL, hmaxM, div_le_iff₀ hMpos]
    nlinarith
  have hρb : 1 - L / 2 ∈ Ico ρ₀ 1 := ⟨by linarith, by linarith⟩
  obtain ⟨σ, hσ, hgood⟩ : ∃ σ ∈ Icc ρ₀ (1 - L / 2), 128 * ε * ‖w σ‖ < ‖w σ + 1‖ := by
    by_contra hcon
    push Not at hcon
    have hb := s02_bp_bad (c := 128 * ε) (by linarith) he he0 heM hm0 hρb hcon
    have h1 : M * (1 - (1 - L / 2)) = m * (1 - ρ₀) / 2 := by
      rw [hL, hmaxM]
      field_simp
      ring
    have : 0 < m * (1 - ρ₀) := by positivity
    linarith
  have hσ' : σ ∈ Ico ρ₀ 1 := ⟨hσ.1, by linarith [hσ.2, hρb.2]⟩
  obtain ⟨τ, hτ, hτw⟩ := s02_bp_escape hε hε1 hw hQ hσ' hgood
  have hσb : L / 2 ≤ 1 - σ := by linarith [hσ.2]
  have hcL : (128 * ε) ^ 2 * L / 162 ≤ 1 - τ := by
    have h2 := hτ.2
    have h3 : (128 * ε) ^ 2 * (L / 2) ≤ (128 * ε) ^ 2 * (1 - σ) :=
      mul_le_mul_of_nonneg_left hσb (by positivity)
    linarith
  have hcLpos : 0 < (128 * ε) ^ 2 * L / 162 := by positivity
  have hτmem : τ ∈ Ico ρ₀ 1 := ⟨hσ.1.trans hτ.1, by linarith⟩
  have hε2 : 448 * ε ^ 2 ≤ 1 := by nlinarith
  have h1ρ : 1 - ρ ≤ 448 * ε ^ 2 * ((128 * ε) ^ 2 * L / 162) := by
    have := hρ.1
    have e1 : 448 * ε ^ 2 * (128 * ε) ^ 2 * L / 162 =
        448 * ε ^ 2 * ((128 * ε) ^ 2 * L / 162) := by ring
    linarith
  have hρτ : τ ≤ ρ := by nlinarith
  have htr := s02_bp_trap hε hε1 hw hQ hτmem hτw ρ ⟨hρτ, hρ.2⟩
  have h1τ : 0 < 1 - τ := by linarith
  have h7 : (1 - ρ) / (64 * (1 - τ)) ≤ 7 * ε ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : 448 * ε ^ 2 * ((128 * ε) ^ 2 * L / 162) ≤ 448 * ε ^ 2 * (1 - τ) :=
      mul_le_mul_of_nonneg_left hcL (by positivity)
    nlinarith
  have hsq : ‖w ρ‖ ^ 2 ≤ (4 * ε) ^ 2 := by nlinarith
  nlinarith [norm_nonneg (w ρ)]

/-- Shen–Wei V_bwd helper (W-BP, Becker–Pommerenke; FROZEN STUB, proved later in B1–B4, not part of
the V-f delivery): for `f` conformal onto a bounded quasidisk, `(1 − |z|²)²|S_f| → 0` implies
`(1 − |z|²)|f''/f'| → 0`. This is (iv) ⇒ (ii) of Pommerenke 1992 Thm 11.1
(`References/Pommerenke1992/Ch11/S02_AsymptoticallyConformalCurvesAndB0.lean` `thm11_1`, sorry,
outside the S02 closure), for the Jordan domain `Ω = F(𝔻)`. -/
theorem s02_vf_bp {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω)
    (hS : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, r < 1 ∧ ∀ z : ℂ, r < ‖z‖ → ‖z‖ < 1 →
      (1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzian f z‖ < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, r < 1 ∧ ∀ z : ℂ, r < ‖z‖ → ‖z‖ < 1 →
      (1 - ‖z‖ ^ 2) * ‖deriv (deriv f) z / deriv f z‖ < ε := by
  intro ε hε
  obtain ⟨R, -, hR⟩ := s02_bp_bounded hq
  set η : ℝ := min (ε / 32) (1 / 1000) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  have hη1 : η ≤ 1 / 1000 := min_le_right _ _
  have hηε : η ≤ ε / 32 := min_le_left _ _
  obtain ⟨r, hr1, hr⟩ := hS η hη0
  have hmr : max r 0 < 1 := max_lt hr1 one_pos
  set ρ₀ : ℝ := (max r 0 + 1) / 2 with hρ₀
  have hρ₀0 : 0 ≤ ρ₀ := by have := le_max_right r 0; rw [hρ₀]; linarith
  have hρ₀1 : ρ₀ < 1 := by rw [hρ₀]; linarith
  have hrρ₀ : r < ρ₀ := by have := le_max_left r 0; rw [hρ₀]; linarith
  obtain ⟨m, hm0, hm⟩ := s02_bp_lower hf hρ₀0 hρ₀1
  obtain ⟨ρ₁, hρ₁1, hode⟩ :=
    s02_bp_ode (M := (4 * (2 * R + 1)) ^ 2) hρ₀0 hρ₀1 hη0 hη1 hm0
  refine ⟨max ρ₁ ρ₀, max_lt hρ₁1 hρ₀1, fun z hz1 hz2 => ?_⟩
  have hρpos : 0 < ‖z‖ := lt_of_le_of_lt (hρ₀0.trans (le_max_right _ _)) hz1
  have hρ₁z : ρ₁ ≤ ‖z‖ := (le_max_left _ _).trans hz1.le
  have hρ₀z : ρ₀ ≤ ‖z‖ := (le_max_right _ _).trans hz1.le
  set ζ : ℂ := z / (‖z‖ : ℂ) with hζdef
  have hζ : ‖ζ‖ = 1 := by
    rw [hζdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos,
      div_self hρpos.ne']
  have hzζ : ((‖z‖ : ℝ) : ℂ) * ζ = z := by
    rw [hζdef]
    have : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hρpos.ne'
    field_simp
  have hray : ∀ t : ℝ, 0 ≤ t → ‖(t : ℂ) * ζ‖ = t := fun t ht => by
    rw [norm_mul, hζ, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  have hmem : ∀ t ∈ Ico ρ₀ 1, (t : ℂ) * ζ ∈ unitDisc := fun t ht => by
    have h : ‖(t : ℂ) * ζ‖ < 1 := by rw [hray t (hρ₀0.trans ht.1)]; exact ht.2
    exact mem_ball_zero_iff.mpr h
  have key := hode
    (fun t : ℝ => -(((1 - t) / 2 : ℝ) : ℂ) * ζ *
      (deriv (deriv f) ((t : ℂ) * ζ) / deriv f ((t : ℂ) * ζ)))
    (fun t : ℝ => (1 - t) ^ 2 * ‖deriv f ((t : ℂ) * ζ)‖ ^ 2)
    (fun t : ℝ => -(((1 - t) ^ 2 / 2 : ℝ) : ℂ) * ζ ^ 2 * schwarzian f ((t : ℂ) * ζ))
    (fun t ht => s02_bp_w_deriv hf hζ (hρ₀0.trans ht.1) ht.2)
    (fun t ht => s02_bp_e_deriv hf hζ (hρ₀0.trans ht.1) ht.2)
    (fun t ht => by
      have ht0 : 0 ≤ t := hρ₀0.trans ht.1
      have hS' := hr ((t : ℂ) * ζ) (by rw [hray t ht0]; linarith [ht.1])
        (by rw [hray t ht0]; exact ht.2)
      rw [hray t ht0] at hS'
      have h1 : (1 - t) ^ 2 ≤ (1 - t ^ 2) ^ 2 := by
        have h2 : 0 ≤ 1 - t := by linarith [ht.2]
        have h3 : 1 - t ≤ 1 - t ^ 2 := by nlinarith [ht.2]
        exact pow_le_pow_left₀ h2 h3 2
      rw [norm_mul, norm_mul, norm_neg, norm_pow, hζ, one_pow, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h4 : (1 - t) ^ 2 * ‖schwarzian f ((t : ℂ) * ζ)‖ ≤
          (1 - t ^ 2) ^ 2 * ‖schwarzian f ((t : ℂ) * ζ)‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      linarith)
    (fun t ht => by
      have hd := deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 (hmem t ht)
      have : 0 < 1 - t := by linarith [ht.2]
      positivity)
    (fun t ht => by
      have := s02_bp_upper hf hR (hmem t ht)
      rwa [hray t (hρ₀0.trans ht.1)] at this)
    (hm ζ hζ) ‖z‖ ⟨hρ₁z, hz2⟩
  simp only [hzζ] at key
  have hN : (1 - ‖z‖ ^ 2) * ‖deriv (deriv f) z / deriv f z‖ =
      2 * (1 + ‖z‖) * ‖-(((1 - ‖z‖) / 2 : ℝ) : ℂ) * ζ * (deriv (deriv f) z / deriv f z)‖ := by
    rw [norm_mul, norm_mul, norm_neg, hζ, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    ring
  rw [hN]
  have : 2 * (1 + ‖z‖) ≤ 4 := by linarith
  nlinarith [norm_nonneg (-(((1 - ‖z‖) / 2 : ℝ) : ℂ) * ζ * (deriv (deriv f) z / deriv f z))]

/-- Shen–Wei (V3) ⇒ (V2) for bounded quasidisks: the backward half of `thm_shen_wei_V`
(Shen–Wei, Thm 4.1; wall W-AZ in `collaboration/SW_PLAN.md`). -/
theorem s02_sw_V_bwd {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) :
    IsVanishingCarlesonDisk (schwarzCarlesonMeasure f) → LogDerivVMOA f := by
  exact fun hv => s02_vf_V2 hf (s02_vf_bp hq hf (s02_va_decay hf hv)) hv

/-- Shen–Wei B_bwd helper (W-AZ A1, Koebe frame): for `F` conformal and `φ = M_{−z}` (`φ(0) = z`),
`G = F ∘ φ` is conformal onto the same domain, `N_G = (N_F ∘ φ) φ' − (N_{γ_z} ∘ φ) φ'` with
`N_{γ_z}(u) = 2z̄/(1 − z̄u)` (`φ''/φ' = −(N_{γ_z} ∘ φ) φ'`, as in `s02_ve_deriv`), so
`N_G(0) = (1 − |z|²) N_F(z) − 2z̄`, and `S_G = (S_F ∘ φ) φ'²` (`eq19_1_chain_rule`, `schwarzianHol_mobius`). -/
theorem s02_az_frame {Ω : Set ℂ} {F : ℂ → ℂ} (hF : IsConformalOnto F unitDisc Ω) {z : ℂ}
    (hz : ‖z‖ < 1) :
    IsConformalOnto (fun w => F (blaschke (-z) w)) unitDisc Ω ∧
      (∀ w ∈ unitDisc, deriv (deriv fun w => F (blaschke (-z) w)) w /
          deriv (fun w => F (blaschke (-z) w)) w =
        deriv (deriv F) (blaschke (-z) w) / deriv F (blaschke (-z) w) * deriv (blaschke (-z)) w -
          2 * conj z / (1 - conj z * blaschke (-z) w) * deriv (blaschke (-z)) w) ∧
      ∀ w ∈ unitDisc, schwarzian (fun w => F (blaschke (-z) w)) w =
        schwarzian F (blaschke (-z) w) * deriv (blaschke (-z)) w ^ 2 := by
  have hz' : ‖-z‖ < 1 := by rwa [norm_neg]
  have hB := isConformalOnto_blaschke hz'
  have hmaps : ∀ w ∈ unitDisc, blaschke (-z) w ∈ unitDisc := fun w hw =>
    mem_ball_zero_iff.mpr (blaschke_mem_unitDisc hz' (mem_ball_zero_iff.mp hw))
  have hFd : ∀ v ∈ unitDisc, DifferentiableAt ℂ F v := fun v hv =>
    hF.1.differentiableAt (isOpen_ball.mem_nhds hv)
  have hBd : ∀ v ∈ unitDisc, DifferentiableAt ℂ (blaschke (-z)) v := fun v hv =>
    hB.1.differentiableAt (isOpen_ball.mem_nhds hv)
  have hd1 : ∀ v ∈ unitDisc, deriv (fun w => F (blaschke (-z) w)) v =
      deriv F (blaschke (-z) v) * deriv (blaschke (-z)) v := fun v hv =>
    ((hFd _ (hmaps v hv)).hasDerivAt.comp v (hBd v hv).hasDerivAt).deriv
  refine ⟨⟨hF.1.comp hB.1 hmaps, hF.2.1.comp hB.2.1 hmaps, ?_⟩, fun w hw => ?_, fun w hw => ?_⟩
  · calc (fun w => F (blaschke (-z) w)) '' unitDisc = F '' (blaschke (-z) '' unitDisc) :=
          (Set.image_image _ _ _).symm
      _ = Ω := by rw [hB.2.2, hF.2.2]
  · have hev : deriv (fun w => F (blaschke (-z) w)) =ᶠ[𝓝 w]
        fun v => deriv F (blaschke (-z) v) * deriv (blaschke (-z)) v :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hw) hd1
    rw [hev.deriv_eq, s02_ve_deriv (hF.1.deriv isOpen_ball) hz hw, hd1 w hw]
    have h1 := deriv_ne_zero_of_injOn isOpen_ball hF.1 hF.2.1 (hmaps w hw)
    have h2 := deriv_ne_zero_of_injOn isOpen_ball hB.1 hB.2.1 hw
    field_simp
  · have h1 := deriv_ne_zero_of_injOn isOpen_ball hF.1 hF.2.1 (hmaps w hw)
    have h2 := deriv_ne_zero_of_injOn isOpen_ball hB.1 hB.2.1 hw
    have hφA : AnalyticAt ℂ (blaschke (-z)) w := hB.1.analyticAt (isOpen_ball.mem_nhds hw)
    have hFA : AnalyticAt ℂ F (blaschke (-z) w) :=
      hF.1.analyticAt (isOpen_ball.mem_nhds (hmaps w hw))
    have h := eq19_1_chain_rule hφA h2 hFA h1
    have hS0 : schwarzian (blaschke (-z)) w = 0 := by
      rw [schwarzian_of_analyticAt hφA]
      have hform : blaschke (-z) = fun v => (1 * v + z) / (-conj (-z) * v + 1) := by
        funext v
        show (v - -z) / (1 - conj (-z) * v) = _
        ring
      have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
      have hden := blaschke_den_ne_zero hz' hw1
      rw [hform]
      refine schwarzianHol_mobius ?_ ?_
      · have hc : (1 : ℂ) * 1 - z * -conj (-z) = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
          rw [map_neg, neg_neg, Complex.mul_conj']
          push_cast
          ring
        rw [hc, Complex.ofReal_ne_zero]
        have : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
        linarith
      · intro hc
        exact hden (by linear_combination hc)
    rw [hS0, add_zero] at h
    exact h

/-- Shen–Wei B_bwd helper (W-AZ A1, Möbius pull-back of the weight `1 − |z|²`, for any `g`): with
`φ = M_{−ζ}`, `∫_𝔻 (1 − |w|²)|(g ∘ φ)φ'|² = ∫_𝔻 k_ζ |g|²(1 − |z|²)` (the identity `hL` in the proof of
`s02_ve_key`; `s02_ve_cov`, `s02_ve_point`). -/
theorem s02_az_cv1 {g : ℂ → ℂ} {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ∫⁻ w in unitDisc, ENNReal.ofReal ((1 - ‖w‖ ^ 2) *
      ‖g (blaschke (-ζ) w) * deriv (blaschke (-ζ)) w‖ ^ 2) =
      ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
        (‖g z‖ ^ 2 * (1 - ‖z‖ ^ 2))) := by
  rw [s02_ve_cov hζ]
  refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
  obtain ⟨_, hinv, h1, h2⟩ := s02_ve_point hζ hz
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  rw [h1, hinv, norm_mul, mul_pow]
  linear_combination ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 * (1 - ‖z‖ ^ 2) * ‖g z‖ ^ 2 *
    (‖deriv (blaschke (-ζ)) (blaschke ζ z)‖ * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2) + 1)) * h2

/-- Shen–Wei B_bwd helper (W-AZ A1, pull-back): for `G = F ∘ φ`, `φ = M_{−ζ}`:
(i) `∫_𝔻 k_ζ |N_F|²(1 − |z|²) ≤ 2∫_𝔻 (1 − |w|²)|N_G|² + 8π`: by `s02_ve_cov`, `s02_ve_point` the left side is
`∫_𝔻 (1 − |w|²)|(N_F ∘ φ)φ'|²`; `s02_az_frame` and `|a + b|² ≤ 2|a|² + 2|b|²`, and the `N_{γ_ζ}` term is
`∫_𝔻 k_ζ (1 − |z|²)|N_{γ_ζ}|² ≤ 4π` (`s02_vf_kernel_n`);
(ii) `∫_𝔻 (1 − |w|²)³|S_G|² = ∫_𝔻 k_ζ |S_F|²(1 − |z|²)³` (`S_G = (S_F ∘ φ)φ'²`, `1 − |φ|² = |φ'|(1 − |w|²)`). -/
theorem s02_az_pull {Ω : Set ℂ} {F : ℂ → ℂ} (hF : IsConformalOnto F unitDisc Ω) {ζ : ℂ}
    (hζ : ‖ζ‖ < 1) :
    ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
        (‖deriv (deriv F) z / deriv F z‖ ^ 2 * (1 - ‖z‖ ^ 2))) ≤
      2 * (∫⁻ w in unitDisc, ENNReal.ofReal ((1 - ‖w‖ ^ 2) *
        ‖deriv (deriv fun w => F (blaschke (-ζ) w)) w /
          deriv (fun w => F (blaschke (-ζ) w)) w‖ ^ 2)) + ENNReal.ofReal (8 * π) ∧
    ∫⁻ w in unitDisc, ENNReal.ofReal ((1 - ‖w‖ ^ 2) ^ 3 *
        ‖schwarzian (fun w => F (blaschke (-ζ) w)) w‖ ^ 2) =
      ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
        (‖schwarzian F z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3)) := by
  obtain ⟨_, hN, hS⟩ := s02_az_frame hF hζ
  refine ⟨?_, ?_⟩
  · have hcv := s02_az_cv1 (g := fun z => deriv (deriv F) z / deriv F z) hζ
    have hcvn := s02_az_cv1 (g := fun z => 2 * conj ζ / (1 - conj ζ * z)) hζ
    beta_reduce at hcv hcvn
    rw [← hcv]
    have hn4 : ∫⁻ w in unitDisc, ENNReal.ofReal ((1 - ‖w‖ ^ 2) *
        ‖2 * conj ζ / (1 - conj ζ * blaschke (-ζ) w) * deriv (blaschke (-ζ)) w‖ ^ 2) ≤
        ENNReal.ofReal (4 * π) := by
      rw [hcvn]
      refine le_trans (le_of_eq (lintegral_congr fun z => ?_)) (s02_vf_kernel_n hζ)
      congr 1
      ring
    have hmeas : Measurable fun w => 2 * ENNReal.ofReal ((1 - ‖w‖ ^ 2) *
        ‖deriv (deriv fun w => F (blaschke (-ζ) w)) w /
          deriv (fun w => F (blaschke (-ζ) w)) w‖ ^ 2) :=
      (ENNReal.measurable_ofReal.comp
        ((by fun_prop : Continuous fun w : ℂ => 1 - ‖w‖ ^ 2).measurable.mul
          (((measurable_deriv _).div (measurable_deriv _)).norm.pow_const 2))).const_mul 2
    have hpt : ∀ w ∈ unitDisc, ENNReal.ofReal ((1 - ‖w‖ ^ 2) *
        ‖deriv (deriv F) (blaschke (-ζ) w) / deriv F (blaschke (-ζ) w) *
          deriv (blaschke (-ζ)) w‖ ^ 2) ≤
        2 * ENNReal.ofReal ((1 - ‖w‖ ^ 2) *
          ‖deriv (deriv fun w => F (blaschke (-ζ) w)) w /
            deriv (fun w => F (blaschke (-ζ) w)) w‖ ^ 2) +
        2 * ENNReal.ofReal ((1 - ‖w‖ ^ 2) *
          ‖2 * conj ζ / (1 - conj ζ * blaschke (-ζ) w) * deriv (blaschke (-ζ)) w‖ ^ 2) := by
      intro w hw
      have hw1 : 0 ≤ 1 - ‖w‖ ^ 2 := by
        have := mem_ball_zero_iff.mp hw
        nlinarith [norm_nonneg w]
      have he : deriv (deriv F) (blaschke (-ζ) w) / deriv F (blaschke (-ζ) w) *
          deriv (blaschke (-ζ)) w =
          deriv (deriv fun w => F (blaschke (-ζ) w)) w / deriv (fun w => F (blaschke (-ζ) w)) w +
            2 * conj ζ / (1 - conj ζ * blaschke (-ζ) w) * deriv (blaschke (-ζ)) w := by
        rw [hN w hw]
        ring
      rw [he]
      have h := norm_add_le (deriv (deriv fun w => F (blaschke (-ζ) w)) w /
          deriv (fun w => F (blaschke (-ζ) w)) w)
        (2 * conj ζ / (1 - conj ζ * blaschke (-ζ) w) * deriv (blaschke (-ζ)) w)
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith [mul_le_mul_of_nonneg_left h2 hw1,
        mul_nonneg hw1 (sq_nonneg (‖deriv (deriv fun w => F (blaschke (-ζ) w)) w /
          deriv (fun w => F (blaschke (-ζ) w)) w‖ -
          ‖2 * conj ζ / (1 - conj ζ * blaschke (-ζ) w) * deriv (blaschke (-ζ)) w‖))]
    calc _ ≤ ∫⁻ w in unitDisc, (2 * ENNReal.ofReal ((1 - ‖w‖ ^ 2) *
            ‖deriv (deriv fun w => F (blaschke (-ζ) w)) w /
              deriv (fun w => F (blaschke (-ζ) w)) w‖ ^ 2) +
          2 * ENNReal.ofReal ((1 - ‖w‖ ^ 2) *
            ‖2 * conj ζ / (1 - conj ζ * blaschke (-ζ) w) * deriv (blaschke (-ζ)) w‖ ^ 2)) :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = 2 * (∫⁻ w in unitDisc, ENNReal.ofReal ((1 - ‖w‖ ^ 2) *
            ‖deriv (deriv fun w => F (blaschke (-ζ) w)) w /
              deriv (fun w => F (blaschke (-ζ) w)) w‖ ^ 2)) +
          2 * ∫⁻ w in unitDisc, ENNReal.ofReal ((1 - ‖w‖ ^ 2) *
            ‖2 * conj ζ / (1 - conj ζ * blaschke (-ζ) w) * deriv (blaschke (-ζ)) w‖ ^ 2) := by
          rw [lintegral_add_left hmeas, lintegral_const_mul' _ _ (by norm_num),
            lintegral_const_mul' _ _ (by norm_num)]
      _ ≤ _ := by
          refine add_le_add le_rfl ?_
          rw [show (8 : ℝ) * π = 2 * (4 * π) by ring, ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_ofNat]
          exact mul_le_mul' le_rfl hn4
  · rw [s02_ve_cov hζ]
    refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
    obtain ⟨hw, hinv, h1, h2⟩ := s02_ve_point hζ hz
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    rw [h1, hS _ hw, hinv, norm_mul, norm_pow, mul_pow]
    linear_combination ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3 *
      ‖schwarzian F z‖ ^ 2 *
      (‖deriv (blaschke (-ζ)) (blaschke ζ z)‖ * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2) + 1) *
      (‖deriv (blaschke (-ζ)) (blaschke ζ z)‖ ^ 2 *
        ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2) ^ 2 + 1)) * h2

/-- Shen–Wei B_bwd helper (W-AZ A2a, polynomial case): for `P = Σ_{n≤N} a_n z^n` and
`Q = Σ_{m<N} (m + 1) a_{m+1} z^m` (`= P'`), coefficientwise (`s02_vd_disc_parseval`, `s02_vd_radial1/3`):
the `n`-th term `T_n = π|a_n|²/((n+1)(n+2))` of the left side is kept for `n < K`, and for `n ≥ K` it is at
most `((K + 3)/(6K)) · (6n/(n + 3)) T_n`, the `n`-th term of the `Q` side. -/
theorem s02_az_lpt_poly (a : ℕ → ℂ) (N : ℕ) {K : ℕ} (hK : 1 ≤ K) :
    ∫ z in unitDisc, (1 - ‖z‖ ^ 2) * ‖∑ n ∈ Finset.range (N + 1), a n * z ^ n‖ ^ 2 ≤
      π * ∑ n ∈ Finset.range K, ‖a n‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) +
        ((K : ℝ) + 3) / (6 * K) * ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 3 *
          ‖∑ m ∈ Finset.range N, ((m + 1 : ℕ) : ℂ) * a (m + 1) * z ^ m‖ ^ 2 := by
  have h1 := s02_vd_disc_parseval (fun t => 1 - t ^ 2) (by fun_prop) a (N + 1)
  have h2 := s02_vd_disc_parseval (fun t => (1 - t ^ 2) ^ 3) (by fun_prop)
    (fun m => ((m + 1 : ℕ) : ℂ) * a (m + 1)) N
  simp only [s02_vd_radial1, s02_vd_radial3] at h1 h2
  rw [h1, h2]
  have hKp : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hπ := Real.pi_pos
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℝ,
      T = fun n => π * (‖a n‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ → ℝ,
      B = fun n => T n * ((n : ℝ) / ((n : ℝ) + 3) * (((K : ℝ) + 3) / K)) := ⟨_, rfl⟩
  have hT0 : ∀ n, 0 ≤ T n := fun n => by
    rw [hT]
    positivity
  have hB0 : ∀ n, 0 ≤ B n := fun n => by
    rw [hB]
    exact mul_nonneg (hT0 n) (by positivity)
  have hpt : ∀ n, T n ≤ (if n < K then T n else 0) + B n := by
    intro n
    split_ifs with hn
    · linarith [hB0 n]
    · have hKn : (K : ℝ) ≤ n := Nat.cast_le.mpr (not_lt.mp hn)
      rw [zero_add, hB]
      refine le_mul_of_one_le_right (hT0 n) ?_
      rw [div_mul_div_comm, one_le_div (by positivity)]
      nlinarith
  calc _ = ∑ n ∈ Finset.range (N + 1), T n := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [hT]
        field_simp
    _ ≤ ∑ n ∈ Finset.range (N + 1), ((if n < K then T n else 0) + B n) :=
        Finset.sum_le_sum fun n _ => hpt n
    _ = ∑ n ∈ Finset.range (N + 1), (if n < K then T n else 0) +
          ∑ n ∈ Finset.range (N + 1), B n := Finset.sum_add_distrib
    _ ≤ ∑ n ∈ Finset.range K, T n + ∑ m ∈ Finset.range N, B (m + 1) := by
        refine add_le_add ?_ (le_of_eq ?_)
        · rw [← Finset.sum_filter]
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => hT0 n
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
        · rw [Finset.sum_range_succ', hB]
          simp
    _ = _ := by
        congr 1
        · simp only [hT, Finset.mul_sum]
        · rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [hB, hT, norm_mul, Complex.norm_natCast, mul_pow]
          push_cast
          field_simp
          ring

/-- Shen–Wei B_bwd helper (W-AZ A2a, dilations): for `g` holomorphic on `𝔻` and `0 < r < 1`, the cut
inequality holds for `g_r(z) = g(rz)` (Taylor coefficients `c_n rⁿ`, `|c_n rⁿ| ≤ |c_n|`); proof as
`s02_vd_dilate`, with `s02_az_lpt_poly` in place of `s02_vd_poly`. -/
theorem s02_az_lpt_dilate {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) {K : ℕ} (hK : 1 ≤ K)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∫ z in unitDisc, (1 - ‖z‖ ^ 2) * ‖g ((r : ℂ) * z)‖ ^ 2 ≤
      π * ∑ n ∈ Finset.range K,
          ‖((n.factorial : ℂ))⁻¹ * iteratedDeriv n g 0‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) +
        ((K : ℝ) + 3) / (6 * K) * ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 3 *
          ‖(r : ℂ) * deriv g ((r : ℂ) * z)‖ ^ 2 := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, c = fun n => ((n.factorial : ℂ))⁻¹ * iteratedDeriv n g 0 :=
    ⟨_, rfl⟩
  have hs : ∀ z ∈ unitDisc, HasSum (fun n => c n * z ^ n) (g z) := by
    intro z hz
    have h := hasSum_taylorSeries_on_ball hg hz
    simp only [sub_zero, smul_eq_mul] at h
    convert h using 2 with n
    simp only [hc]
    ring
  have hs' : ∀ z ∈ unitDisc,
      HasSum (fun n => c (n + 1) * ((n + 1 : ℕ) : ℂ) * z ^ n) (deriv g z) :=
    fun z hz => TakhtajanTeo.Ch2.faber_powerSeries_deriv hs hz
  have hU1 := TakhtajanTeo.Ch2.bergmanTaylorPoly_dilate_uniform hs hr0 hr1
  have hU2 := TakhtajanTeo.Ch2.bergmanTaylorPoly_dilate_uniform
    (f := deriv g) (c := fun n => c (n + 1) * ((n + 1 : ℕ) : ℂ)) hs' hr0 hr1
  simp only [TakhtajanTeo.Ch2.bergmanTaylorPoly_eval] at hU1 hU2
  have hmaps : MapsTo (fun z : ℂ => (r : ℂ) * z) (closedBall 0 1) unitDisc := by
    intro z hz
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    exact (mul_le_of_le_one_right hr0.le (mem_closedBall_zero_iff.mp hz)).trans_lt hr1
  have hc1 : ContinuousOn (fun z => g ((r : ℂ) * z)) (closedBall 0 1) :=
    hg.continuousOn.comp (by fun_prop) hmaps
  have hc2 : ContinuousOn (fun z => deriv g ((r : ℂ) * z)) (closedBall 0 1) :=
    (hg.deriv isOpen_ball).continuousOn.comp (by fun_prop) hmaps
  have hL1 := (s02_vd_lim (fun t => 1 - t ^ 2) (by fun_prop)
    (fun N => continuous_finsetSum _ fun n _ => by fun_prop) hc1 hU1).comp
    (tendsto_add_atTop_nat 1)
  have hL2 := s02_vd_lim (fun t => (1 - t ^ 2) ^ 3) (by fun_prop)
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
  have hpN : ∀ N : ℕ, ∫ z in unitDisc, (1 - ‖z‖ ^ 2) *
      ‖∑ n ∈ Finset.range (N + 1), c n * (r : ℂ) ^ n * z ^ n‖ ^ 2 ≤
      π * ∑ n ∈ Finset.range K,
          ‖((n.factorial : ℂ))⁻¹ * iteratedDeriv n g 0‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) +
        ((K : ℝ) + 3) / (6 * K) * (r ^ 2 * ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 3 *
          ‖∑ m ∈ Finset.range N, c (m + 1) * ((m + 1 : ℕ) : ℂ) * (r : ℂ) ^ m * z ^ m‖ ^ 2) := by
    intro N
    have h := s02_az_lpt_poly (fun n => c n * (r : ℂ) ^ n) N hK
    have e : ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 3 * ‖∑ m ∈ Finset.range N,
        ((m + 1 : ℕ) : ℂ) * (c (m + 1) * (r : ℂ) ^ (m + 1)) * z ^ m‖ ^ 2 =
        r ^ 2 * ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 3 *
          ‖∑ m ∈ Finset.range N, c (m + 1) * ((m + 1 : ℕ) : ℂ) * (r : ℂ) ^ m * z ^ m‖ ^ 2 := by
      rw [← integral_const_mul]
      congr 1
      funext z
      rw [hQ]
      ring
    rw [e] at h
    refine h.trans (add_le_add ?_ le_rfl)
    gcongr with n hn
    simp only [hc]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hr0.le hr1.le)
  have hR : ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 3 * ‖(r : ℂ) * deriv g ((r : ℂ) * z)‖ ^ 2 =
      r ^ 2 * ∫ z in unitDisc, (1 - ‖z‖ ^ 2) ^ 3 * ‖deriv g ((r : ℂ) * z)‖ ^ 2 := by
    rw [← integral_const_mul]
    congr 1
    funext z
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    ring
  rw [hR]
  exact le_of_tendsto_of_tendsto' hL1
    (((hL2.const_mul (r ^ 2)).const_mul (((K : ℝ) + 3) / (6 * K))).const_add _) hpN

/-- Shen–Wei B_bwd helper (W-AZ A2a, Littlewood–Paley with a coefficient cut, AZ (6)): for `g` holomorphic on
`𝔻` with Taylor coefficients `c_n = g⁽ⁿ⁾(0)/n!`,
`∫_𝔻 (1 − |z|²)|g|² = π Σ |c_n|²/((n+1)(n+2))` and
`∫_𝔻 (1 − |z|²)³|g'|² = 6π Σ n|c_n|²/((n+1)(n+2)(n+3))`; the ratio of the `n`-th terms is `6n/(n + 3)`,
which is `≥ 6K/(K + 3)` for `n ≥ K`. Same scheme as V-d (`s02_vd_disc_parseval`, `s02_vd_radial1/3`, then
`s02_vd_lim`, dilation, Fatou and `s02_vd_scale`). Both sides may be `∞`. -/
theorem s02_az_lp_tail {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) {K : ℕ} (hK : 1 ≤ K) :
    ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) * ‖g z‖ ^ 2) ≤
      ENNReal.ofReal (π * ∑ n ∈ Finset.range K,
          ‖((n.factorial : ℂ))⁻¹ * iteratedDeriv n g 0‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) +
        ENNReal.ofReal (((K : ℝ) + 3) / (6 * K)) *
          ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 * ‖deriv g z‖ ^ 2) := by
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
  have hKc : (0 : ℝ) ≤ ((K : ℝ) + 3) / (6 * K) := by positivity
  have hsub : unitDisc ⊆ closedBall (0 : ℂ) 1 := ball_subset_closedBall
  have hnn : ∀ g : ℂ → ℝ, (∀ z ∈ unitDisc, 0 ≤ g z) → 0 ≤ᵐ[volume.restrict unitDisc] g :=
    fun g hg => (ae_restrict_iff' (measurableSet_ball : MeasurableSet unitDisc)).mpr
      (ae_of_all _ hg)
  have hw : ∀ z ∈ unitDisc, 0 ≤ 1 - ‖z‖ ^ 2 := fun z hz => by
    have := mem_ball_zero_iff.mp hz
    nlinarith [norm_nonneg z]
  have hmaps : ∀ k, MapsTo (fun z : ℂ => (rs k : ℂ) * z) (closedBall 0 1) unitDisc := by
    intro k z hz
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hr0 k).le]
    exact (mul_le_of_le_one_right (hr0 k).le (mem_closedBall_zero_iff.mp hz)).trans_lt (hr1 k)
  have hc1 : ∀ k, ContinuousOn (fun z => (1 - ‖z‖ ^ 2) * ‖g ((rs k : ℂ) * z)‖ ^ 2)
      (closedBall 0 1) := fun k =>
    (by fun_prop : Continuous fun z : ℂ => 1 - ‖z‖ ^ 2).continuousOn.mul
      ((hg.continuousOn.comp (by fun_prop) (hmaps k)).norm.pow 2)
  -- the dilated bound
  have hk : ∀ k, ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) * ‖g ((rs k : ℂ) * z)‖ ^ 2) ≤
      ENNReal.ofReal (π * ∑ n ∈ Finset.range K,
          ‖((n.factorial : ℂ))⁻¹ * iteratedDeriv n g 0‖ ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) +
        ENNReal.ofReal (((K : ℝ) + 3) / (6 * K)) *
          ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 * ‖deriv g z‖ ^ 2) := by
    intro k
    have hc2 : ContinuousOn (fun z => (1 - ‖z‖ ^ 2) ^ 3 *
        ‖(rs k : ℂ) * deriv g ((rs k : ℂ) * z)‖ ^ 2) (closedBall 0 1) :=
      (by fun_prop : Continuous fun z : ℂ => (1 - ‖z‖ ^ 2) ^ 3).continuousOn.mul
        ((continuousOn_const.mul
          ((hg.deriv isOpen_ball).continuousOn.comp (by fun_prop) (hmaps k))).norm.pow 2)
    have hn2 := hnn _ fun z hz => mul_nonneg (pow_nonneg (hw z hz) 3)
      (sq_nonneg ‖(rs k : ℂ) * deriv g ((rs k : ℂ) * z)‖)
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((hc1 k).integrableOn_compact (isCompact_closedBall 0 1) |>.mono_set hsub)
      (hnn _ fun z hz => mul_nonneg (hw z hz) (sq_nonneg _))]
    refine (ENNReal.ofReal_le_ofReal (s02_az_lpt_dilate hg hK (hr0 k) (hr1 k))).trans ?_
    rw [ENNReal.ofReal_add (by positivity) (mul_nonneg hKc (integral_nonneg_of_ae hn2)),
      ENNReal.ofReal_mul hKc, ofReal_integral_eq_lintegral_ofReal
        (hc2.integrableOn_compact (isCompact_closedBall 0 1) |>.mono_set hsub) hn2]
    exact add_le_add le_rfl
      (mul_le_mul_right (s02_vd_scale (measurable_deriv g) (hr0 k) (hr1 k).le) _)
  -- pointwise convergence and Fatou
  have hpt : ∀ z ∈ unitDisc, Tendsto (fun k => ENNReal.ofReal ((1 - ‖z‖ ^ 2) *
      ‖g ((rs k : ℂ) * z)‖ ^ 2)) atTop (𝓝 (ENNReal.ofReal ((1 - ‖z‖ ^ 2) * ‖g z‖ ^ 2))) := by
    intro z hz
    have h1 : Tendsto (fun k => (rs k : ℂ) * z) atTop (𝓝 z) := by
      have := ((Complex.continuous_ofReal.tendsto 1).comp hlim).mul_const z
      simpa using this
    have hgz : ContinuousAt g z := hg.continuousOn.continuousAt (isOpen_ball.mem_nhds hz)
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (((hgz.tendsto.comp h1).norm.pow 2).const_mul _)
  have hmeas : ∀ k, AEMeasurable (fun z => ENNReal.ofReal ((1 - ‖z‖ ^ 2) *
      ‖g ((rs k : ℂ) * z)‖ ^ 2)) (volume.restrict unitDisc) := fun k =>
    (ENNReal.continuous_ofReal.comp_continuousOn ((hc1 k).mono hsub)).aemeasurable
      (measurableSet_ball : MeasurableSet unitDisc)
  calc ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) * ‖g z‖ ^ 2)
      = ∫⁻ z in unitDisc, liminf (fun k => ENNReal.ofReal ((1 - ‖z‖ ^ 2) *
          ‖g ((rs k : ℂ) * z)‖ ^ 2)) atTop := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet unitDisc)] with z hz
        exact (hpt z hz).liminf_eq.symm
    _ ≤ liminf (fun k => ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) *
          ‖g ((rs k : ℂ) * z)‖ ^ 2)) atTop := lintegral_liminf_le' hmeas
    _ ≤ _ := liminf_le_of_frequently_le' (Frequently.of_forall hk)

/-- Shen–Wei B_bwd helper (W-AZ A2b, low coefficients): a Bloch bound `(1 − |z|²)|g| ≤ 6` gives
`|g| ≤ 8` on `|z| = 1/2`, so `|g⁽ⁿ⁾(0)/n!| ≤ 8·2ⁿ` (Cauchy, `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`). -/
theorem s02_az_coeff {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc)
    (hB : ∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) * ‖g z‖ ≤ 6) (n : ℕ) :
    ‖((n.factorial : ℂ))⁻¹ * iteratedDeriv n g 0‖ ≤ 8 * 2 ^ n := by
  have hsub : closedBall (0 : ℂ) (1 / 2) ⊆ unitDisc := closedBall_subset_ball (by norm_num)
  have hd : DiffContOnCl ℂ g (ball (0 : ℂ) (1 / 2)) := (hg.mono hsub).diffContOnCl_ball subset_rfl
  have hC : ∀ z ∈ sphere (0 : ℂ) (1 / 2), ‖g z‖ ≤ 8 := fun z hz => by
    have hz1 : ‖z‖ = 1 / 2 := mem_sphere_zero_iff_norm.mp hz
    have h := hB z (hsub (sphere_subset_closedBall hz))
    rw [hz1] at h
    linarith
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num) hd hC
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (n.factorial : ℝ)⁻¹ * ‖iteratedDeriv n g 0‖ ≤
        (n.factorial : ℝ)⁻¹ * (n.factorial * 8 / (1 / 2) ^ n) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 8 * 2 ^ n := by
        rw [one_div, inv_pow, div_inv_eq_mul]
        field_simp

/-- Shen–Wei B_bwd helper (W-AZ A2c, pointwise split, AZ l. 276–299 with `ε² = 1/100`, threshold `T = 24/5`):
for `x = 1 − |z|² > 0`, `a = N(z)`, `b = N'(z)` with the Bloch bound `x|a| ≤ 6`, and `S = b − ½a²`:
`|b|² ≤ 51|S|² + (51/200)|a|⁴` (`|u + v|² ≤ (1 + 1/t)|u|² + (1 + t)|v|²`, `t = 1/50`); then
`x³|a|⁴ ≤ T² x|a|²` if `x|a| ≤ T`, and `x³|a|⁴ = (x|a|)⁴/x ≤ 6⁴/x` otherwise;
`(51/200)·(24/5)² = 3672/625 ≈ 5.875 < 6`, `(51/200)·6⁴ = 8262/25`. -/
theorem s02_az_point {x : ℝ} (hx : 0 < x) {a b : ℂ} (hB : x * ‖a‖ ≤ 6) :
    x ^ 3 * ‖b‖ ^ 2 ≤ 51 * (x ^ 3 * ‖b - 1 / 2 * a ^ 2‖ ^ 2) + 3672 / 625 * (x * ‖a‖ ^ 2) +
      8262 / 25 * (if 24 / 5 < x * ‖a‖ then x⁻¹ else 0) := by
  have hn := norm_nonneg a
  have hs := norm_nonneg (b - 1 / 2 * a ^ 2)
  have hm := norm_nonneg b
  have hxn : 0 ≤ x * ‖a‖ := mul_nonneg hx.le hn
  have hb : ‖b‖ ≤ ‖b - 1 / 2 * a ^ 2‖ + 1 / 2 * ‖a‖ ^ 2 := by
    have h1 : b = (b - 1 / 2 * a ^ 2) + 1 / 2 * a ^ 2 := by ring
    have h2 : ‖(1 / 2 : ℂ) * a ^ 2‖ = 1 / 2 * ‖a‖ ^ 2 := by
      rw [norm_mul, norm_pow]
      norm_num
    calc ‖b‖ = ‖(b - 1 / 2 * a ^ 2) + 1 / 2 * a ^ 2‖ := by rw [← h1]
      _ ≤ _ := norm_add_le _ _
      _ = _ := by rw [h2]
  have hm2 : ‖b‖ ^ 2 ≤ 51 * ‖b - 1 / 2 * a ^ 2‖ ^ 2 + 51 / 200 * ‖a‖ ^ 4 := by
    have h3 := pow_le_pow_left₀ hm hb 2
    nlinarith [sq_nonneg (50 * ‖b - 1 / 2 * a ^ 2‖ - 1 / 2 * ‖a‖ ^ 2)]
  have hx3 : 0 ≤ x ^ 3 := by positivity
  have hmain : x ^ 3 * ‖b‖ ^ 2 ≤
      51 * (x ^ 3 * ‖b - 1 / 2 * a ^ 2‖ ^ 2) + 51 / 200 * (x ^ 3 * ‖a‖ ^ 4) := by
    nlinarith [mul_le_mul_of_nonneg_left hm2 hx3]
  have hxa2 : 0 ≤ x * ‖a‖ ^ 2 := by positivity
  split_ifs with h
  · have h4 : x ^ 3 * ‖a‖ ^ 4 = (x * ‖a‖) ^ 4 * x⁻¹ := by
      field_simp
    have h5 : (x * ‖a‖) ^ 4 ≤ 1296 := by
      have := pow_le_pow_left₀ hxn hB 4
      norm_num at this
      exact this
    have h6 : x ^ 3 * ‖a‖ ^ 4 ≤ 1296 * x⁻¹ := by
      rw [h4]
      exact mul_le_mul_of_nonneg_right h5 (inv_nonneg.mpr hx.le)
    nlinarith
  · replace h : x * ‖a‖ ≤ 24 / 5 := le_of_not_gt h
    have h4 : x ^ 3 * ‖a‖ ^ 4 = (x * ‖a‖) ^ 2 * (x * ‖a‖ ^ 2) := by ring
    have h5 : (x * ‖a‖) ^ 2 ≤ 576 / 25 := by
      have := pow_le_pow_left₀ hxn h 2
      norm_num at this
      exact this
    have h6 : x ^ 3 * ‖a‖ ^ 4 ≤ 576 / 25 * (x * ‖a‖ ^ 2) := by
      rw [h4]
      exact mul_le_mul_of_nonneg_right h5 hxa2
    nlinarith

/-- Shen–Wei B_bwd helper (W-AZ A2e, Riccati–Gronwall comparison; explicit error constant `2`):
let `14/5 ≤ a ≤ 4`, `t₁ = 2/a − 11/35 ∈ [0.186, 2/5]` (`t₁ = 2/5` exactly for `a = 14/5`), and let
`y' = ½y² + q` on `[0, t₁]` with `y(0) = a`, `|q| ≤ Q` and `|y| ≤ 40/7`. Then `|y(t₁) − 70/11| ≤ 2Q`.

Numeric chain: `Y(t) = a/(1 − at/2)` solves `Y' = ½Y²`, `Y(0) = a`, is increasing, and `Y(t₁) = 70/11 ≈ 6.364`
(`1 − at₁/2 = 11a/70`); in particular `Y(2/5) = (14/5)/(11/25) = 70/11` for `a = 14/5`. The error `e = y − Y`
has `e(0) = 0`, `e' = ½(y + Y)e + q`, so `|e'| ≤ K|e| + Q` with `K = ½(40/7 + 70/11) = 465/77 ≈ 6.039`, and
Gronwall (`norm_le_gronwallBound_of_norm_deriv_right_le`) gives
`|e(t₁)| ≤ (Q/K)(e^{K t₁} − 1) ≤ (77/465)(e^{186/77} − 1) Q ≈ 1.689 Q ≤ 2Q`
(`K t₁ ≤ 186/77 < 5/2`, `e^{5/2} ≤ 12.19`, `(77/465)·11.19 ≈ 1.853 ≤ 2`). -/
theorem s02_az_riccati {y q : ℝ → ℂ} {a Q : ℝ} (ha1 : 14 / 5 ≤ a) (ha2 : a ≤ 4)
    (hy0 : y 0 = a)
    (hy : ∀ t ∈ Icc (0 : ℝ) (2 / a - 11 / 35), HasDerivAt y (1 / 2 * y t ^ 2 + q t) t)
    (hq : ∀ t ∈ Icc (0 : ℝ) (2 / a - 11 / 35), ‖q t‖ ≤ Q)
    (hyb : ∀ t ∈ Icc (0 : ℝ) (2 / a - 11 / 35), ‖y t‖ ≤ 40 / 7) :
    ‖y (2 / a - 11 / 35) - 70 / 11‖ ≤ 2 * Q := by
  have ha0 : 0 < a := by linarith
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : ℝ, t₁ = 2 / a - 11 / 35 := ⟨_, rfl⟩
  rw [← ht₁] at hy hq hyb ⊢
  have hat : a * t₁ = 2 - 11 * a / 35 := by
    rw [ht₁]
    field_simp
  have ht0 : 0 ≤ t₁ := by
    rw [ht₁, sub_nonneg, le_div_iff₀ ha0]
    linarith
  have ht25 : t₁ ≤ 2 / 5 := by
    rw [ht₁, sub_le_iff_le_add, div_le_iff₀ ha0]
    linarith
  have hQ : 0 ≤ Q := (norm_nonneg _).trans (hq 0 ⟨le_rfl, ht0⟩)
  have hden : ∀ t ∈ Icc 0 t₁, 11 * a / 70 ≤ 1 - a * t / 2 := fun t ht => by
    have := mul_le_mul_of_nonneg_left ht.2 ha0.le
    linarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ → ℝ, Y = fun t => a / (1 - a * t / 2) := ⟨_, rfl⟩
  have hYd : ∀ t ∈ Icc 0 t₁, HasDerivAt Y (1 / 2 * Y t ^ 2) t := fun t ht => by
    have hd : 1 - a * t / 2 ≠ 0 := by
      have := hden t ht
      have : 0 < 11 * a / 70 := by positivity
      linarith
    have h1 : HasDerivAt (fun t => 1 - a * t / 2) (-(a * 1 / 2)) t :=
      (((hasDerivAt_id' t).const_mul a).div_const 2).const_sub 1
    have h2 := (hasDerivAt_const t a).div h1 hd
    rw [hY]
    refine h2.congr_deriv ?_
    field_simp
    ring
  have hYb : ∀ t ∈ Icc 0 t₁, 0 ≤ Y t ∧ Y t ≤ 70 / 11 := fun t ht => by
    have h1 := hden t ht
    have h2 : 0 < 1 - a * t / 2 := by
      have : 0 < 11 * a / 70 := by positivity
      linarith
    rw [hY]
    refine ⟨div_nonneg ha0.le h2.le, ?_⟩
    rw [div_le_iff₀ h2]
    linarith
  obtain ⟨e, he⟩ : ∃ e : ℝ → ℂ, e = fun t => y t - (Y t : ℂ) := ⟨_, rfl⟩
  have hed : ∀ t ∈ Icc 0 t₁, HasDerivAt e (1 / 2 * (y t + Y t) * e t + q t) t := fun t ht => by
    have h := (hy t ht).sub (hYd t ht).ofReal_comp
    rw [he]
    refine h.congr_deriv ?_
    beta_reduce
    push_cast
    ring
  have hcont : ContinuousOn e (Icc 0 t₁) := fun t ht =>
    (hed t ht).continuousAt.continuousWithinAt
  have he0 : ‖e 0‖ ≤ 0 := by
    rw [he, hY]
    simp [hy0]
  have key := norm_le_gronwallBound_of_norm_deriv_right_le
    (f' := fun t => 1 / 2 * (y t + Y t) * e t + q t) (K := 465 / 77) hcont
    (fun t ht => (hed t (Ico_subset_Icc_self ht)).hasDerivWithinAt) he0
    (fun t ht => by
      have ht' := Ico_subset_Icc_self ht
      obtain ⟨h0, h1⟩ := hYb t ht'
      have hn : ‖(1 / 2 : ℂ) * (y t + Y t)‖ ≤ 465 / 77 := by
        have h2 := norm_add_le (y t) (Y t : ℂ)
        rw [Complex.norm_real, Real.norm_of_nonneg h0] at h2
        rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
        linarith [hyb t ht']
      calc ‖1 / 2 * (y t + Y t) * e t + q t‖ ≤ ‖1 / 2 * (y t + Y t) * e t‖ + ‖q t‖ :=
            norm_add_le _ _
        _ ≤ 465 / 77 * ‖e t‖ + Q := by
            rw [norm_mul]
            exact add_le_add (mul_le_mul_of_nonneg_right hn (norm_nonneg _)) (hq t ht'))
    t₁ ⟨ht0, le_rfl⟩
  rw [gronwallBound_of_K_ne_0 (by norm_num)] at key
  beta_reduce at key
  simp only [sub_zero, zero_mul, zero_add] at key
  have hYt : Y t₁ = 70 / 11 := by
    rw [hY]
    dsimp only
    rw [div_eq_iff (by nlinarith)]
    linarith
  have hyt : y t₁ - 70 / 11 = e t₁ := by
    rw [he]
    dsimp only
    rw [hYt]
    push_cast
    ring
  have hE5 : Real.exp (5 / 2) < 1007 / 77 := by
    have h1 : Real.exp (5 / 2) ^ 2 = Real.exp 1 ^ 5 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      norm_num
    have h2 : Real.exp 1 ^ 5 < 2.7182818286 ^ 5 :=
      pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
    have h3 := Real.exp_pos (5 / 2)
    nlinarith
  have hE : Real.exp (465 / 77 * t₁) ≤ 1 + 2 * (465 / 77) := by
    have : Real.exp (465 / 77 * t₁) ≤ Real.exp (5 / 2) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  rw [hyt]
  refine key.trans ?_
  have h1 : 0 ≤ Q / (465 / 77) := by positivity
  calc Q / (465 / 77) * (Real.exp (465 / 77 * t₁) - 1) ≤ Q / (465 / 77) * (2 * (465 / 77)) :=
        mul_le_mul_of_nonneg_left (by linarith) h1
    _ = 2 * Q := by field_simp

/-- Shen–Wei B_bwd helper (W-AZ A2e, AZ Lemma 2 in the Koebe frame, `δ = 1/8`, `t = 2/5`): if `G` is conformal on
`𝔻` and `a = |N_G(0)| ≥ 14/5`, then `(1 − |v|²)²|S_G(v)| > 1/8` for some `|v| ≤ 2/5`.

Proof (no normal families): otherwise, with `|η| = 1`, `ηN_G(0) = a`, `y(t) = ηN_G(tη)` solves
`y' = ½y² + q`, `q(t) = η²S_G(tη)` (`s02_sw_logDeriv`). Numeric chain:
* `a ≤ 4` (`lem_koebe_b` at `0`), so `s02_az_riccati` applies up to `t₁ = 2/a − 11/35 ≤ 2/5`;
* `|q(t)| ≤ δ/(1 − t²)² ≤ Q = (1/8)/(21/25)² = 625/3528 ≈ 0.177` for `t ≤ 2/5`;
* Koebe (`lem_koebe_b`): `|N_G(u)| ≤ (4 + 2|u|)/(1 − |u|²) ≤ (4 + 0.8)/0.84 = 40/7 ≈ 5.714` for `|u| ≤ 2/5`;
* `s02_az_riccati`: `|y(t₁)| ≥ 70/11 − 2Q = 70/11 − 625/1764 ≈ 6.364 − 0.354 = 6.009 > 40/7`, a contradiction
  (margin `≈ 0.295`; all comparisons by `norm_num`).
`δ = 1/8` rather than `1/4`: with the frozen error constant `2` the choice `δ = 1/4` gives error
`2·(1/4)/0.7056 ≈ 0.709 > 70/11 − 40/7 ≈ 0.649`; the sharp factor `1.689/0.7056 ≈ 2.39` would leave only `0.05`. -/
theorem s02_az_lemma2 {Ω : Set ℂ} {G : ℂ → ℂ} (hG : IsConformalOnto G unitDisc Ω)
    (ha : 14 / 5 ≤ ‖deriv (deriv G) 0 / deriv G 0‖) :
    ∃ v : ℂ, ‖v‖ ≤ 2 / 5 ∧ 1 / 8 < (1 - ‖v‖ ^ 2) ^ 2 * ‖schwarzian G v‖ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hNd, hSN⟩ := s02_sw_logDeriv hG
  -- Koebe (`lem_koebe_b`): `|N_G(u)| ≤ (4 + 2|u|)/(1 − |u|²) ≤ 40/7` for `|u| ≤ 2/5`
  have hK : ∀ u : ℂ, ‖u‖ ≤ 2 / 5 → ‖deriv (deriv G) u / deriv G u‖ ≤ 40 / 7 := fun u hu => by
    have hu0 := norm_nonneg u
    have hu1 : u ∈ unitDisc := mem_ball_zero_iff.mpr (by linarith)
    have h := (lem_koebe_b hG hu1).1
    have h1 := norm_sub_norm_le ((1 - ‖u‖ ^ 2 : ℂ) * deriv (deriv G) u / deriv G u) (2 * conj u)
    have h2 : ‖(1 - ‖u‖ ^ 2 : ℂ) * deriv (deriv G) u / deriv G u‖ =
        (1 - ‖u‖ ^ 2) * ‖deriv (deriv G) u / deriv G u‖ := by
      rw [mul_div_assoc, norm_mul,
        show (1 - ‖u‖ ^ 2 : ℂ) = ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by nlinarith)]
    have h3 : ‖(2 : ℂ) * conj u‖ = 2 * ‖u‖ := by simp
    rw [h2, h3] at h1
    have h4 : 0 < 1 - ‖u‖ ^ 2 := by nlinarith
    by_contra hc
    push Not at hc
    have h5 := mul_lt_mul_of_pos_left hc h4
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 / 5 - ‖u‖) (by linarith : (0 : ℝ) ≤ ‖u‖ + 3 / 4)]
  obtain ⟨A, hA⟩ : ∃ A : ℂ, A = deriv (deriv G) 0 / deriv G 0 := ⟨_, rfl⟩
  rw [← hA] at ha
  have ha4 : ‖A‖ ≤ 4 := by
    have h := (lem_koebe_b (z := 0) hG (mem_ball_zero_iff.mpr (by simp))).1
    rw [hA]
    simpa using h
  have ha0 : 0 < ‖A‖ := by linarith
  obtain ⟨η, hη⟩ : ∃ η : ℂ, η = conj A / (‖A‖ : ℂ) := ⟨_, rfl⟩
  have hη1 : ‖η‖ = 1 := by
    rw [hη, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self ha0.ne']
  have hηA : η * A = (‖A‖ : ℂ) := by
    rw [hη, div_mul_eq_mul_div, Complex.conj_mul',
      div_eq_iff (Complex.ofReal_ne_zero.mpr ha0.ne')]
    ring
  have hnt : ∀ t : ℝ, 0 ≤ t → ‖(t : ℂ) * η‖ = t := fun t ht => by
    rw [norm_mul, hη1, mul_one, Complex.norm_real, Real.norm_of_nonneg ht]
  have ht1 : 2 / ‖A‖ - 11 / 35 ≤ 2 / 5 := by
    rw [sub_le_iff_le_add, div_le_iff₀ ha0]
    linarith
  have ht0 : 0 ≤ 2 / ‖A‖ - 11 / 35 := by
    rw [sub_nonneg, le_div_iff₀ ha0]
    linarith
  have hsub : ∀ t ∈ Icc (0 : ℝ) (2 / ‖A‖ - 11 / 35), 0 ≤ t ∧ t ≤ 2 / 5 := fun t ht =>
    ⟨ht.1, ht.2.trans ht1⟩
  have key := s02_az_riccati
    (y := fun t : ℝ => η * (deriv (deriv G) ((t : ℂ) * η) / deriv G ((t : ℂ) * η)))
    (q := fun t : ℝ => η ^ 2 * schwarzian G ((t : ℂ) * η)) (Q := 625 / 3528) ha ha4
    (by
      rw [Complex.ofReal_zero, zero_mul, ← hA, hηA])
    (fun t ht => by
      obtain ⟨h0, h25⟩ := hsub t ht
      have hu : (t : ℂ) * η ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hnt t h0]; linarith)
      have hNda : HasDerivAt (fun z => deriv (deriv G) z / deriv G z)
          (deriv (fun z => deriv (deriv G) z / deriv G z) ((t : ℂ) * η)) ((t : ℂ) * η) :=
        (hNd.differentiableAt (isOpen_ball.mem_nhds hu)).hasDerivAt
      have hlin : HasDerivAt (fun u : ℂ => u * η) η (t : ℂ) := by
        simpa using (hasDerivAt_id (t : ℂ)).mul_const η
      have hc := ((hNda.comp (t : ℂ) hlin).comp_ofReal).const_mul η
      refine hc.congr_deriv ?_
      rw [hSN _ hu]
      ring)
    (fun t ht => by
      obtain ⟨h0, h25⟩ := hsub t ht
      rw [norm_mul, norm_pow, hη1, one_pow, one_mul]
      have h := hcon _ (by rw [hnt t h0]; exact h25)
      rw [hnt t h0] at h
      have h1 : 21 / 25 ≤ 1 - t ^ 2 := by nlinarith
      have h2 : (21 / 25 : ℝ) ^ 2 ≤ (1 - t ^ 2) ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
      nlinarith [mul_le_mul_of_nonneg_right h2 (norm_nonneg (schwarzian G ((t : ℂ) * η)))])
    (fun t ht => by
      obtain ⟨h0, h25⟩ := hsub t ht
      rw [norm_mul, hη1, one_mul]
      exact hK _ (by rw [hnt t h0]; exact h25))
  beta_reduce at key
  have hy1 : ‖η * (deriv (deriv G) (((2 / ‖A‖ - 11 / 35 : ℝ) : ℂ) * η) /
      deriv G (((2 / ‖A‖ - 11 / 35 : ℝ) : ℂ) * η))‖ ≤ 40 / 7 := by
    rw [norm_mul, hη1, one_mul]
    exact hK _ (by rw [hnt _ ht0]; exact ht1)
  have h70 := norm_sub_le (η * (deriv (deriv G) (((2 / ‖A‖ - 11 / 35 : ℝ) : ℂ) * η) /
      deriv G (((2 / ‖A‖ - 11 / 35 : ℝ) : ℂ) * η)))
    (η * (deriv (deriv G) (((2 / ‖A‖ - 11 / 35 : ℝ) : ℂ) * η) /
      deriv G (((2 / ‖A‖ - 11 / 35 : ℝ) : ℂ) * η)) - 70 / 11)
  rw [sub_sub_cancel, show ‖(70 / 11 : ℂ)‖ = 70 / 11 by norm_num] at h70
  norm_num at key h70 hy1
  linarith

/-- Shen–Wei B_bwd helper (W-AZ A2f, one point of `E`): if `(1 − |z|²)|N_F(z)| > 24/5` then the pseudo-hyperbolic
disc `Δ(z, 3/5) = {v : |M_z(v)| < 3/5}` carries `∫_Δ (1 − |v|²)³|S_F|² ≥ (π/15625)(1 − |z|²)`.
In the frame `G = F ∘ φ` (`s02_az_frame`): `|N_G(0)| ≥ 24/5 − 2|z| > 14/5`, so `s02_az_lemma2` gives `|v₀| ≤ 2/5`
with `|S_G(v₀)| > 1/8`; `s02_sw_meanValue` on `D(v₀, 1/5) ⊆ D(0, 3/5)` gives `∫ |S_G|² ≥ π/25 · 1/64`; and
`(1 − |v|²)³|S_F|² dA(v) = |φ'(w)|(1 − |w|²)³|S_G(w)|² dA(w)` (`s02_ve_cov` at `−z`) with
`|φ'(w)| ≥ (25/64)(1 − |z|²)`, `(1 − |w|²)³ ≥ (16/25)³` on `D(0, 3/5)`:
`(25/64)(4096/15625)(π/25)(1/64) = π/15625`. -/
theorem s02_az_epoint {Ω : Set ℂ} {F : ℂ → ℂ} (hF : IsConformalOnto F unitDisc Ω) {z : ℂ}
    (hz : ‖z‖ < 1) (hE : 24 / 5 < (1 - ‖z‖ ^ 2) * ‖deriv (deriv F) z / deriv F z‖) :
    ENNReal.ofReal (π / 15625 * (1 - ‖z‖ ^ 2)) ≤
      ∫⁻ v in unitDisc ∩ {v | ‖blaschke z v‖ < 3 / 5},
        ENNReal.ofReal ((1 - ‖v‖ ^ 2) ^ 3 * ‖schwarzian F v‖ ^ 2) := by
  have hz' : ‖-z‖ < 1 := by rwa [norm_neg]
  have hz0 := norm_nonneg z
  have h1z : 0 < 1 - ‖z‖ ^ 2 := by nlinarith
  obtain ⟨hG, hN, hS⟩ := s02_az_frame hF hz
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_zero_iff.mpr (by simp)
  have hφ0 : blaschke (-z) 0 = z := by
    show (0 - -z) / (1 - conj (-z) * 0) = z
    simp
  have hφ'0 : deriv (blaschke (-z)) 0 = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [(hasDerivAt_blaschke hz' (by simp)).deriv, map_neg, neg_mul_neg, Complex.mul_conj',
      mul_zero, sub_zero, one_pow, div_one]
    push_cast
    ring
  -- the Koebe transform: `N_G(0) = (1 − |z|²) N_F(z) − 2z̄`, so `|N_G(0)| > 24/5 − 2 = 14/5`
  have hc : (1 : ℂ) - conj z * z = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']
    push_cast
    ring
  have hne : ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h1z.ne'
  have hNG0 : deriv (deriv fun w => F (blaschke (-z) w)) 0 /
      deriv (fun w => F (blaschke (-z) w)) 0 =
      ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * (deriv (deriv F) z / deriv F z) - 2 * conj z := by
    rw [hN 0 h0D, hφ0, hφ'0, hc]
    field_simp
  have ha : 14 / 5 ≤ ‖deriv (deriv fun w => F (blaschke (-z) w)) 0 /
      deriv (fun w => F (blaschke (-z) w)) 0‖ := by
    rw [hNG0]
    have h := norm_sub_norm_le (((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * (deriv (deriv F) z / deriv F z))
      (2 * conj z)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h1z.le,
      show ‖(2 : ℂ) * conj z‖ = 2 * ‖z‖ by simp] at h
    linarith
  obtain ⟨v₀, hv₀, hv₀S⟩ := s02_az_lemma2 hG ha
  obtain ⟨hNd, hSN⟩ := s02_sw_logDeriv hG
  have hŜd : DifferentiableOn ℂ (fun w => deriv (fun w => deriv (deriv fun w => F (blaschke (-z) w)) w /
      deriv (fun w => F (blaschke (-z) w)) w) w - 1 / 2 * (deriv (deriv fun w => F (blaschke (-z) w)) w /
      deriv (fun w => F (blaschke (-z) w)) w) ^ 2) unitDisc :=
    (hNd.deriv isOpen_ball).sub ((hNd.pow 2).const_mul _)
  have hv₀D : v₀ ∈ unitDisc := mem_ball_zero_iff.mpr (by linarith)
  have hv₀1 : (1 - ‖v₀‖ ^ 2) ^ 2 ≤ 1 := by
    have := norm_nonneg v₀
    have h1 : 0 ≤ 1 - ‖v₀‖ ^ 2 := by nlinarith
    have h2 : 1 - ‖v₀‖ ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hSv₀ : 1 / 8 < ‖deriv (fun w => deriv (deriv fun w => F (blaschke (-z) w)) w /
      deriv (fun w => F (blaschke (-z) w)) w) v₀ - 1 / 2 * (deriv (deriv fun w => F (blaschke (-z) w)) v₀ /
      deriv (fun w => F (blaschke (-z) w)) v₀) ^ 2‖ := by
    rw [← hSN v₀ hv₀D]
    nlinarith [norm_nonneg (schwarzian (fun w => F (blaschke (-z) w)) v₀)]
  have hcb : closedBall v₀ (1 / 5) ⊆ unitDisc := fun w hw => by
    have h1 := mem_closedBall.mp hw
    rw [dist_eq_norm] at h1
    have h2 := norm_sub_norm_le w v₀
    exact mem_ball_zero_iff.mpr (by linarith)
  have hmv := s02_sw_meanValue (by norm_num : (0 : ℝ) < 1 / 5) (hŜd.mono hcb)
  -- the region `Δ(z, 3/5)` and the change of variables `v = φ(w)` (`s02_ve_cov` at `−z`)
  have hAm : MeasurableSet {v : ℂ | ‖blaschke z v‖ < 3 / 5} := by
    refine measurableSet_lt ?_ measurable_const
    show Measurable fun v : ℂ => ‖(v - z) / (1 - conj z * v)‖
    fun_prop
  have hR : ∫⁻ v in unitDisc ∩ {v | ‖blaschke z v‖ < 3 / 5},
      ENNReal.ofReal ((1 - ‖v‖ ^ 2) ^ 3 * ‖schwarzian F v‖ ^ 2) =
      ∫⁻ v in unitDisc, {v | ‖blaschke z v‖ < 3 / 5}.indicator
        (fun v => ENNReal.ofReal ((1 - ‖v‖ ^ 2) ^ 3 * ‖schwarzian F v‖ ^ 2)) v := by
    rw [lintegral_indicator hAm, Measure.restrict_restrict hAm, Set.inter_comm]
  rw [hR, s02_ve_cov hz']
  have hpt : ∀ w ∈ ball v₀ (1 / 5), ENNReal.ofReal (64 / 625 * (1 - ‖z‖ ^ 2)) *
      ENNReal.ofReal (‖deriv (fun w => deriv (deriv fun w => F (blaschke (-z) w)) w /
        deriv (fun w => F (blaschke (-z) w)) w) w - 1 / 2 *
          (deriv (deriv fun w => F (blaschke (-z) w)) w /
            deriv (fun w => F (blaschke (-z) w)) w) ^ 2‖ ^ 2) ≤
      ENNReal.ofReal (((1 - ‖-z‖ ^ 2) / ‖1 - conj (-z) * w‖ ^ 2) ^ 2) *
        {v | ‖blaschke z v‖ < 3 / 5}.indicator
          (fun v => ENNReal.ofReal ((1 - ‖v‖ ^ 2) ^ 3 * ‖schwarzian F v‖ ^ 2))
          (blaschke (-z) w) := by
    intro w hw
    have hwv := mem_ball.mp hw
    rw [dist_eq_norm] at hwv
    have hw35 : ‖w‖ < 3 / 5 := by
      have := norm_sub_norm_le w v₀
      linarith
    have hw0 := norm_nonneg w
    have hwD : w ∈ unitDisc := mem_ball_zero_iff.mpr (by linarith)
    have hw1 : ‖w‖ < 1 := by linarith
    obtain ⟨_, hinv, h1, _⟩ := s02_ve_point hz' hwD
    rw [neg_neg] at hinv
    rw [Set.indicator_of_mem (show blaschke (-z) w ∈ {v | ‖blaschke z v‖ < 3 / 5} by
      show ‖blaschke z (blaschke (-z) w)‖ < 3 / 5
      rw [hinv]
      exact hw35)]
    have hden := blaschke_den_ne_zero hz' hw1
    have hdpos : 0 < ‖1 - conj (-z) * w‖ := norm_pos_iff.mpr hden
    have hdle : ‖1 - conj (-z) * w‖ ≤ 8 / 5 := by
      have h := norm_sub_le (1 : ℂ) (conj (-z) * w)
      rw [norm_one, norm_mul, Complex.norm_conj, norm_neg] at h
      nlinarith
    have hφ' : ‖deriv (blaschke (-z)) w‖ = (1 - ‖-z‖ ^ 2) / ‖1 - conj (-z) * w‖ ^ 2 := by
      rw [(hasDerivAt_blaschke hz' hw1).deriv, norm_div, norm_pow, Complex.mul_conj',
        show (1 : ℂ) - ((‖-z‖ : ℝ) : ℂ) ^ 2 = ((1 - ‖-z‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by rw [norm_neg]; linarith)]
    rw [norm_neg] at hφ' h1 ⊢
    set k := (1 - ‖z‖ ^ 2) / ‖1 - conj (-z) * w‖ ^ 2 with hk
    have hk0 : 0 ≤ k := by positivity
    have hkb : 25 / 64 * (1 - ‖z‖ ^ 2) ≤ k := by
      rw [hk, le_div_iff₀ (by positivity)]
      have : ‖1 - conj (-z) * w‖ ^ 2 ≤ 64 / 25 := by nlinarith
      nlinarith
    have hw3 : 4096 / 15625 ≤ (1 - ‖w‖ ^ 2) ^ 3 := by
      have h2 : 16 / 25 ≤ 1 - ‖w‖ ^ 2 := by nlinarith
      have := pow_le_pow_left₀ (by norm_num) h2 3
      norm_num at this
      exact this
    have hkw : 64 / 625 * (1 - ‖z‖ ^ 2) ≤ k * (1 - ‖w‖ ^ 2) ^ 3 := by
      nlinarith [mul_le_mul hkb hw3 (by norm_num) hk0]
    have hSw : ‖deriv (fun w => deriv (deriv fun w => F (blaschke (-z) w)) w /
        deriv (fun w => F (blaschke (-z) w)) w) w - 1 / 2 *
          (deriv (deriv fun w => F (blaschke (-z) w)) w /
            deriv (fun w => F (blaschke (-z) w)) w) ^ 2‖ =
        ‖schwarzian F (blaschke (-z) w)‖ * k ^ 2 := by
      rw [← hSN w hwD, hS w hwD, norm_mul, norm_pow, hφ']
    rw [hSw, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), h1]
    refine ENNReal.ofReal_le_ofReal ?_
    calc 64 / 625 * (1 - ‖z‖ ^ 2) * (‖schwarzian F (blaschke (-z) w)‖ * k ^ 2) ^ 2
        = 64 / 625 * (1 - ‖z‖ ^ 2) * (‖schwarzian F (blaschke (-z) w)‖ ^ 2 * k ^ 4) := by ring
      _ ≤ k * (1 - ‖w‖ ^ 2) ^ 3 * (‖schwarzian F (blaschke (-z) w)‖ ^ 2 * k ^ 4) :=
          mul_le_mul_of_nonneg_right hkw (by positivity)
      _ = k ^ 2 * ((k * (1 - ‖w‖ ^ 2)) ^ 3 * ‖schwarzian F (blaschke (-z) w)‖ ^ 2) := by ring
  have hball : ball v₀ (1 / 5) ⊆ unitDisc := ball_subset_closedBall.trans hcb
  calc ENNReal.ofReal (π / 15625 * (1 - ‖z‖ ^ 2))
      ≤ ENNReal.ofReal (64 / 625 * (1 - ‖z‖ ^ 2)) *
          (ENNReal.ofReal (‖deriv (fun w => deriv (deriv fun w => F (blaschke (-z) w)) w /
            deriv (fun w => F (blaschke (-z) w)) w) v₀ - 1 / 2 *
              (deriv (deriv fun w => F (blaschke (-z) w)) v₀ /
                deriv (fun w => F (blaschke (-z) w)) v₀) ^ 2‖ ^ 2) *
            ENNReal.ofReal (π * (1 / 5) ^ 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h64 : (1 / 8 : ℝ) ^ 2 ≤ ‖deriv (fun w => deriv (deriv fun w => F (blaschke (-z) w)) w /
            deriv (fun w => F (blaschke (-z) w)) w) v₀ - 1 / 2 *
              (deriv (deriv fun w => F (blaschke (-z) w)) v₀ /
                deriv (fun w => F (blaschke (-z) w)) v₀) ^ 2‖ ^ 2 :=
          pow_le_pow_left₀ (by norm_num) hSv₀.le 2
        have hπ := Real.pi_pos
        nlinarith [mul_le_mul_of_nonneg_left h64 (by positivity : (0 : ℝ) ≤
          64 / 625 * (1 - ‖z‖ ^ 2) * (π * (1 / 5) ^ 2))]
    _ ≤ ENNReal.ofReal (64 / 625 * (1 - ‖z‖ ^ 2)) *
          ∫⁻ w in ball v₀ (1 / 5), ENNReal.ofReal (‖deriv (fun w =>
            deriv (deriv fun w => F (blaschke (-z) w)) w /
              deriv (fun w => F (blaschke (-z) w)) w) w - 1 / 2 *
                (deriv (deriv fun w => F (blaschke (-z) w)) w /
                  deriv (fun w => F (blaschke (-z) w)) w) ^ 2‖ ^ 2) :=
        mul_le_mul' le_rfl hmv
    _ = ∫⁻ w in ball v₀ (1 / 5), ENNReal.ofReal (64 / 625 * (1 - ‖z‖ ^ 2)) *
          ENNReal.ofReal (‖deriv (fun w => deriv (deriv fun w => F (blaschke (-z) w)) w /
            deriv (fun w => F (blaschke (-z) w)) w) w - 1 / 2 *
              (deriv (deriv fun w => F (blaschke (-z) w)) w /
                deriv (fun w => F (blaschke (-z) w)) w) ^ 2‖ ^ 2) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ w in ball v₀ (1 / 5), ENNReal.ofReal (((1 - ‖-z‖ ^ 2) / ‖1 - conj (-z) * w‖ ^ 2) ^ 2) *
          {v | ‖blaschke z v‖ < 3 / 5}.indicator
            (fun v => ENNReal.ofReal ((1 - ‖v‖ ^ 2) ^ 3 * ‖schwarzian F v‖ ^ 2))
            (blaschke (-z) w) :=
        setLIntegral_mono' measurableSet_ball hpt
    _ ≤ _ := lintegral_mono_set hball

/-- Shen–Wei B_bwd helper (W-AZ A2f, pseudo-hyperbolic Whitney–Tonelli): Tonelli and `|M_z(v)| = |M_v(z)|`, then
for fixed `v` the hyperbolic area `∫_{Δ(v, 3/5)} (1 − |z|²)⁻² dA(z) = ∫_{D(0, 3/5)} (1 − |w|²)⁻² dA(w)`
(`s02_ve_cov`, `s02_ve_point`) `≤ π(9/25)(25/16)² = 225π/256 ≤ 3`. -/
theorem s02_az_swap {H : ℂ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ z in unitDisc, ENNReal.ofReal (((1 - ‖z‖ ^ 2) ^ 2)⁻¹) *
        ∫⁻ v in unitDisc ∩ {v | ‖blaschke z v‖ < 3 / 5}, H v) ≤
      ENNReal.ofReal 3 * ∫⁻ v in unitDisc, H v := by
  obtain ⟨S, hS⟩ : ∃ S : Set (ℂ × ℂ), S = {p | p.2 ∈ unitDisc ∧ ‖blaschke p.1 p.2‖ < 3 / 5} :=
    ⟨_, rfl⟩
  have hmemS : ∀ z v, (z, v) ∈ S ↔ v ∈ unitDisc ∧ ‖blaschke z v‖ < 3 / 5 := by
    intro z v
    rw [hS]
    rfl
  have hb : Measurable fun p : ℂ × ℂ => ‖blaschke p.1 p.2‖ := by
    show Measurable fun p : ℂ × ℂ => ‖(p.2 - p.1) / (1 - conj p.1 * p.2)‖
    fun_prop
  have hSm : MeasurableSet S := by
    rw [hS]
    exact (measurableSet_ball.preimage measurable_snd).inter (measurableSet_lt hb measurable_const)
  have hsym : ∀ z v : ℂ, ‖blaschke z v‖ = ‖blaschke v z‖ := by
    intro z v
    show ‖(v - z) / (1 - conj z * v)‖ = ‖(z - v) / (1 - conj v * z)‖
    rw [norm_div, norm_div, norm_sub_rev v z, ← Complex.norm_conj (1 - conj v * z)]
    congr 2
    simp [mul_comm]
  have ham : Measurable fun z : ℂ => ENNReal.ofReal (((1 - ‖z‖ ^ 2) ^ 2)⁻¹) :=
    Measurable.ennreal_ofReal (by fun_prop)
  have hG : Measurable fun p : ℂ × ℂ =>
      ENNReal.ofReal (((1 - ‖p.1‖ ^ 2) ^ 2)⁻¹) * S.indicator (fun q => H q.2) p :=
    (ham.comp measurable_fst).mul ((hH.comp measurable_snd).indicator hSm)
  have heq : ∀ z, ENNReal.ofReal (((1 - ‖z‖ ^ 2) ^ 2)⁻¹) *
      ∫⁻ v in unitDisc ∩ {v | ‖blaschke z v‖ < 3 / 5}, H v =
      ∫⁻ v, ENNReal.ofReal (((1 - ‖z‖ ^ 2) ^ 2)⁻¹) * S.indicator (fun q => H q.2) (z, v) := by
    intro z
    have hm : MeasurableSet (unitDisc ∩ {v | ‖blaschke z v‖ < 3 / 5}) :=
      measurableSet_ball.inter (measurableSet_lt (hb.comp measurable_prodMk_left) measurable_const)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator hm]
    refine lintegral_congr fun v => ?_
    by_cases hv : (z, v) ∈ S
    · rw [Set.indicator_of_mem hv,
        Set.indicator_of_mem (show v ∈ unitDisc ∩ {v | ‖blaschke z v‖ < 3 / 5} from
          (hmemS z v).1 hv)]
    · rw [Set.indicator_of_notMem hv, mul_zero,
        Set.indicator_of_notMem (show v ∉ unitDisc ∩ {v | ‖blaschke z v‖ < 3 / 5} from
          fun h => hv ((hmemS z v).2 h))]
  -- the hyperbolic area of `Δ(v, 3/5)` is at most `3`
  have harea : ∀ v ∈ unitDisc, ∫⁻ z in unitDisc, {z | ‖blaschke v z‖ < 3 / 5}.indicator
      (fun z => ENNReal.ofReal (((1 - ‖z‖ ^ 2) ^ 2)⁻¹)) z ≤ ENNReal.ofReal 3 := by
    intro v hv
    have hv1 : ‖v‖ < 1 := mem_ball_zero_iff.mp hv
    have hcov := s02_ve_cov hv1
      ((ball (0 : ℂ) (3 / 5)).indicator fun w => ENNReal.ofReal (((1 - ‖w‖ ^ 2) ^ 2)⁻¹))
    have hvol : volume (ball (0 : ℂ) (3 / 5)) = ENNReal.ofReal ((3 / 5) ^ 2 * π) := by
      rw [Complex.volume_ball, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow (by norm_num), ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
    calc ∫⁻ z in unitDisc, {z | ‖blaschke v z‖ < 3 / 5}.indicator
          (fun z => ENNReal.ofReal (((1 - ‖z‖ ^ 2) ^ 2)⁻¹)) z
        = ∫⁻ z in unitDisc, ENNReal.ofReal (((1 - ‖v‖ ^ 2) / ‖1 - conj v * z‖ ^ 2) ^ 2) *
            (ball (0 : ℂ) (3 / 5)).indicator
              (fun w => ENNReal.ofReal (((1 - ‖w‖ ^ 2) ^ 2)⁻¹)) (blaschke v z) := by
          refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
          obtain ⟨_, _, h1, _⟩ := s02_ve_point hv1 hz
          have hz1 : 0 < 1 - ‖z‖ ^ 2 := by
            have := mem_ball_zero_iff.mp hz
            nlinarith [norm_nonneg z]
          have hden : (0 : ℝ) < ‖1 - conj v * z‖ :=
            norm_pos_iff.mpr (blaschke_den_ne_zero hv1 (mem_ball_zero_iff.mp hz))
          have hk : 0 < 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
          by_cases hzT : ‖blaschke v z‖ < 3 / 5
          · rw [Set.indicator_of_mem (show z ∈ {z | ‖blaschke v z‖ < 3 / 5} from hzT),
              Set.indicator_of_mem (show blaschke v z ∈ ball (0 : ℂ) (3 / 5) from
                mem_ball_zero_iff.mpr hzT),
              ← ENNReal.ofReal_mul (by positivity), h1]
            congr 1
            field_simp
          · rw [Set.indicator_of_notMem (show z ∉ {z | ‖blaschke v z‖ < 3 / 5} from hzT),
              Set.indicator_of_notMem (show blaschke v z ∉ ball (0 : ℂ) (3 / 5) from
                fun h => hzT (mem_ball_zero_iff.mp h)), mul_zero]
      _ = ∫⁻ w in unitDisc, (ball (0 : ℂ) (3 / 5)).indicator
            (fun w => ENNReal.ofReal (((1 - ‖w‖ ^ 2) ^ 2)⁻¹)) w := hcov.symm
      _ ≤ ∫⁻ w, (ball (0 : ℂ) (3 / 5)).indicator (fun _ => ENNReal.ofReal (625 / 256)) w := by
          refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun w => ?_)
          by_cases hw : w ∈ ball (0 : ℂ) (3 / 5)
          · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
            refine ENNReal.ofReal_le_ofReal ?_
            have hw1 : ‖w‖ < 3 / 5 := mem_ball_zero_iff.mp hw
            have h2 : 16 / 25 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
            have h3 : (16 / 25 : ℝ) ^ 2 ≤ (1 - ‖w‖ ^ 2) ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
            calc ((1 - ‖w‖ ^ 2) ^ 2)⁻¹ ≤ ((16 / 25 : ℝ) ^ 2)⁻¹ := inv_anti₀ (by norm_num) h3
              _ = 625 / 256 := by norm_num
          · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]
      _ = ENNReal.ofReal (625 / 256) * volume (ball (0 : ℂ) (3 / 5)) :=
          lintegral_indicator_const measurableSet_ball _
      _ ≤ ENNReal.ofReal 3 := by
          rw [hvol, ← ENNReal.ofReal_mul (by norm_num)]
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith [Real.pi_lt_d2]
  have hpw : ∀ v, (∫⁻ z in unitDisc,
      ENNReal.ofReal (((1 - ‖z‖ ^ 2) ^ 2)⁻¹) * S.indicator (fun q => H q.2) (z, v)) ≤
        unitDisc.indicator (fun v => ENNReal.ofReal 3 * H v) v := by
    intro v
    by_cases hv : v ∈ unitDisc
    · rw [Set.indicator_of_mem hv]
      have hT : MeasurableSet {z : ℂ | ‖blaschke v z‖ < 3 / 5} :=
        measurableSet_lt (hb.comp measurable_prodMk_left) measurable_const
      calc (∫⁻ z in unitDisc,
            ENNReal.ofReal (((1 - ‖z‖ ^ 2) ^ 2)⁻¹) * S.indicator (fun q => H q.2) (z, v))
          = ∫⁻ z in unitDisc, {z | ‖blaschke v z‖ < 3 / 5}.indicator
              (fun z => ENNReal.ofReal (((1 - ‖z‖ ^ 2) ^ 2)⁻¹)) z * H v := by
            refine lintegral_congr fun z => ?_
            by_cases hz : ‖blaschke v z‖ < 3 / 5
            · have hzv : (z, v) ∈ S := (hmemS z v).2 ⟨hv, by rwa [hsym]⟩
              rw [Set.indicator_of_mem hzv,
                Set.indicator_of_mem (show z ∈ {z | ‖blaschke v z‖ < 3 / 5} from hz)]
            · have hzv : (z, v) ∉ S := fun h => hz (by rw [← hsym]; exact ((hmemS z v).1 h).2)
              rw [Set.indicator_of_notMem hzv,
                Set.indicator_of_notMem (show z ∉ {z | ‖blaschke v z‖ < 3 / 5} from hz),
                mul_zero, zero_mul]
        _ = (∫⁻ z in unitDisc, {z | ‖blaschke v z‖ < 3 / 5}.indicator
              (fun z => ENNReal.ofReal (((1 - ‖z‖ ^ 2) ^ 2)⁻¹)) z) * H v :=
            lintegral_mul_const _ (ham.indicator hT)
        _ ≤ ENNReal.ofReal 3 * H v := mul_le_mul' (harea v hv) le_rfl
    · rw [Set.indicator_of_notMem hv]
      refine le_of_eq ((lintegral_congr (g := fun _ => 0) fun z => ?_).trans lintegral_zero)
      rw [Set.indicator_of_notMem (fun h => hv ((hmemS z v).1 h).1), mul_zero]
  calc (∫⁻ z in unitDisc, ENNReal.ofReal (((1 - ‖z‖ ^ 2) ^ 2)⁻¹) *
        ∫⁻ v in unitDisc ∩ {v | ‖blaschke z v‖ < 3 / 5}, H v)
      = ∫⁻ z in unitDisc, ∫⁻ v,
          ENNReal.ofReal (((1 - ‖z‖ ^ 2) ^ 2)⁻¹) * S.indicator (fun q => H q.2) (z, v) :=
        lintegral_congr fun z => heq z
    _ = ∫⁻ v, ∫⁻ z in unitDisc,
          ENNReal.ofReal (((1 - ‖z‖ ^ 2) ^ 2)⁻¹) * S.indicator (fun q => H q.2) (z, v) :=
        lintegral_lintegral_swap hG.aemeasurable
    _ ≤ ∫⁻ v, unitDisc.indicator (fun v => ENNReal.ofReal 3 * H v) v := lintegral_mono hpw
    _ = ∫⁻ v in unitDisc, ENNReal.ofReal 3 * H v := lintegral_indicator measurableSet_ball _
    _ = ENNReal.ofReal 3 * ∫⁻ v in unitDisc, H v := lintegral_const_mul _ hH

/-- Shen–Wei B_bwd helper (W-AZ A2f, the part on `E = {(1 − |z|²)|N_F| > 24/5}`, AZ l. 319–341):
`∫_E (1 − |z|²)⁻¹ ≤ 15000 ∫_𝔻 (1 − |v|²)³|S_F|²`: on `E`, `(1 − |z|²)⁻¹ ≤ (15625/π)(1 − |z|²)⁻² ∫_Δ …`
(`s02_az_epoint`), then `s02_az_swap`; `3·15625/π ≤ 15000`. -/
theorem s02_az_epart {Ω : Set ℂ} {F : ℂ → ℂ} (hF : IsConformalOnto F unitDisc Ω) :
    ∫⁻ z in unitDisc, ENNReal.ofReal
        (if 24 / 5 < (1 - ‖z‖ ^ 2) * ‖deriv (deriv F) z / deriv F z‖ then (1 - ‖z‖ ^ 2)⁻¹ else 0) ≤
      ENNReal.ofReal 15000 *
        ∫⁻ v in unitDisc, ENNReal.ofReal ((1 - ‖v‖ ^ 2) ^ 3 * ‖schwarzian F v‖ ^ 2) := by
  obtain ⟨_, hSN⟩ := s02_sw_logDeriv hF
  have hNm : Measurable fun w => deriv (deriv F) w / deriv F w :=
    (measurable_deriv _).div (measurable_deriv _)
  -- a measurable version of the integrand, equal to it on `𝔻`
  have hHm : Measurable fun v => ENNReal.ofReal ((1 - ‖v‖ ^ 2) ^ 3 *
      ‖deriv (fun w => deriv (deriv F) w / deriv F w) v -
        1 / 2 * (deriv (deriv F) v / deriv F v) ^ 2‖ ^ 2) :=
    Measurable.ennreal_ofReal
      ((by fun_prop : Continuous fun v : ℂ => (1 - ‖v‖ ^ 2) ^ 3).measurable.mul
        (((measurable_deriv _).sub (measurable_const.mul (hNm.pow_const 2))).norm.pow_const 2))
  have hHH : ∀ v ∈ unitDisc, ENNReal.ofReal ((1 - ‖v‖ ^ 2) ^ 3 * ‖schwarzian F v‖ ^ 2) =
      ENNReal.ofReal ((1 - ‖v‖ ^ 2) ^ 3 *
        ‖deriv (fun w => deriv (deriv F) w / deriv F w) v -
          1 / 2 * (deriv (deriv F) v / deriv F v) ^ 2‖ ^ 2) := fun v hv => by
    rw [hSN v hv]
  have hsw := s02_az_swap hHm
  have hpt : ∀ z ∈ unitDisc, ENNReal.ofReal
      (if 24 / 5 < (1 - ‖z‖ ^ 2) * ‖deriv (deriv F) z / deriv F z‖ then (1 - ‖z‖ ^ 2)⁻¹ else 0) ≤
      ENNReal.ofReal (15625 / π) * (ENNReal.ofReal (((1 - ‖z‖ ^ 2) ^ 2)⁻¹) *
        ∫⁻ v in unitDisc ∩ {v | ‖blaschke z v‖ < 3 / 5}, ENNReal.ofReal ((1 - ‖v‖ ^ 2) ^ 3 *
          ‖deriv (fun w => deriv (deriv F) w / deriv F w) v -
            1 / 2 * (deriv (deriv F) v / deriv F v) ^ 2‖ ^ 2)) := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    split_ifs with hE
    · have hAm : MeasurableSet {v : ℂ | ‖blaschke z v‖ < 3 / 5} := by
        refine measurableSet_lt ?_ measurable_const
        show Measurable fun v : ℂ => ‖(v - z) / (1 - conj z * v)‖
        fun_prop
      have he := s02_az_epoint hF hz1 hE
      replace he := he.trans (le_of_eq (setLIntegral_congr_fun (measurableSet_ball.inter hAm)
        fun v hv => hHH v hv.1))
      have hx : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      have hπ := Real.pi_pos
      calc ENNReal.ofReal (1 - ‖z‖ ^ 2)⁻¹ = ENNReal.ofReal (15625 / π) *
            (ENNReal.ofReal (((1 - ‖z‖ ^ 2) ^ 2)⁻¹) *
              ENNReal.ofReal (π / 15625 * (1 - ‖z‖ ^ 2))) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            field_simp
        _ ≤ _ := mul_le_mul' le_rfl (mul_le_mul' le_rfl he)
    · rw [ENNReal.ofReal_zero]
      exact bot_le
  have hπ := Real.pi_gt_d2
  calc _ ≤ ∫⁻ z in unitDisc, ENNReal.ofReal (15625 / π) *
        (ENNReal.ofReal (((1 - ‖z‖ ^ 2) ^ 2)⁻¹) *
          ∫⁻ v in unitDisc ∩ {v | ‖blaschke z v‖ < 3 / 5}, ENNReal.ofReal ((1 - ‖v‖ ^ 2) ^ 3 *
            ‖deriv (fun w => deriv (deriv F) w / deriv F w) v -
              1 / 2 * (deriv (deriv F) v / deriv F v) ^ 2‖ ^ 2)) :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = ENNReal.ofReal (15625 / π) * ∫⁻ z in unitDisc,
          ENNReal.ofReal (((1 - ‖z‖ ^ 2) ^ 2)⁻¹) *
            ∫⁻ v in unitDisc ∩ {v | ‖blaschke z v‖ < 3 / 5}, ENNReal.ofReal ((1 - ‖v‖ ^ 2) ^ 3 *
              ‖deriv (fun w => deriv (deriv F) w / deriv F w) v -
                1 / 2 * (deriv (deriv F) v / deriv F v) ^ 2‖ ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (15625 / π) * (ENNReal.ofReal 3 * ∫⁻ v in unitDisc,
          ENNReal.ofReal ((1 - ‖v‖ ^ 2) ^ 3 *
            ‖deriv (fun w => deriv (deriv F) w / deriv F w) v -
              1 / 2 * (deriv (deriv F) v / deriv F v) ^ 2‖ ^ 2)) := mul_le_mul' le_rfl hsw
    _ = ENNReal.ofReal (15625 / π) * (ENNReal.ofReal 3 * ∫⁻ v in unitDisc,
          ENNReal.ofReal ((1 - ‖v‖ ^ 2) ^ 3 * ‖schwarzian F v‖ ^ 2)) := by
        congr 2
        exact setLIntegral_congr_fun measurableSet_ball fun v hv => (hHH v hv).symm
    _ ≤ _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith

/-- Shen–Wei B_bwd helper (W-AZ A2d, dilations of a conformal map): for `0 < s ≤ 1`, `G_s(w) = G(sw)` is
conformal on `𝔻` and `N_{G_s}(w) = s N_G(sw)` for every `w` (`deriv_comp_mul_left`). -/
theorem s02_az_cdil {Ω : Set ℂ} {G : ℂ → ℂ} (hG : IsConformalOnto G unitDisc Ω) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s ≤ 1) :
    IsConformalOnto (fun w => G ((s : ℂ) * w)) unitDisc ((fun w => G ((s : ℂ) * w)) '' unitDisc) ∧
      ∀ w, deriv (deriv fun w => G ((s : ℂ) * w)) w / deriv (fun w => G ((s : ℂ) * w)) w =
        (s : ℂ) * (deriv (deriv G) ((s : ℂ) * w) / deriv G ((s : ℂ) * w)) := by
  have hmaps : MapsTo (fun z : ℂ => (s : ℂ) * z) unitDisc unitDisc := by
    intro z hz
    apply mem_ball_zero_iff.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    exact (mul_le_of_le_one_left (norm_nonneg z) hs1).trans_lt (mem_ball_zero_iff.mp hz)
  have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0.ne'
  have hd1 : deriv (fun w => G ((s : ℂ) * w)) = fun w => (s : ℂ) * deriv G ((s : ℂ) * w) :=
    funext fun w => by rw [deriv_comp_mul_left, smul_eq_mul]
  have hd2 : deriv (deriv fun w => G ((s : ℂ) * w)) =
      fun w => (s : ℂ) * ((s : ℂ) * deriv (deriv G) ((s : ℂ) * w)) :=
    funext fun w => by rw [hd1, deriv_const_mul_field, deriv_comp_mul_left, smul_eq_mul]
  refine ⟨⟨hG.1.comp (by fun_prop : Differentiable ℂ fun z : ℂ => (s : ℂ) * z).differentiableOn hmaps,
    hG.2.1.comp (fun x _ y _ h => mul_left_cancel₀ hs' h) hmaps, rfl⟩, fun w => ?_⟩
  rw [hd2, hd1, mul_div_mul_left _ _ hs', mul_div_assoc]

/-- Shen–Wei B_bwd helper (W-AZ A2d, AZ Lemma 1 at the centre `0`): there are constants with
`∫_𝔻 (1 − |w|²)|N_G|² ≤ C₀ + C₁ ∫_𝔻 (1 − |w|²)³|S_G|²` for every conformal `G`.
For `0 < s < 1`, `G_s(w) = G(sw)` is conformal with `N_{G_s}(w) = sN_G(sw)` (bounded, so `A_s < ∞` as in
`s02_vf_dil_fin`) and `∫(1 − |w|²)³|S_{G_s}|² ≤ ∫(1 − |w|²)³|S_G|²` (`s02_vd_scale`). With `K = 200`:
`A_s ≤ L + ρB_s` (`s02_az_lp_tail`, `ρ = 203/1200`, `L ≤ 64π·4²⁰⁰` by `s02_az_coeff` and `s02_sw_bloch`),
`B_s ≤ 51 S_s + (3672/625)A_s + (8262/25)E_s` (`s02_az_point`), `E_s ≤ 15000 S_s` (`s02_az_epart`);
`1 − ρ·3672/625 = 573/93750 > 0` absorbs `A_s`, and `s02_vf_fatou` (at `ζ = 0`) lets `s → 1`. -/
theorem s02_az_center : ∃ C₀ C₁ : ℝ, ∀ {Ω : Set ℂ} {G : ℂ → ℂ}, IsConformalOnto G unitDisc Ω →
    ∫⁻ w in unitDisc, ENNReal.ofReal ((1 - ‖w‖ ^ 2) * ‖deriv (deriv G) w / deriv G w‖ ^ 2) ≤
      ENNReal.ofReal C₀ + ENNReal.ofReal C₁ *
        ∫⁻ w in unitDisc, ENNReal.ofReal ((1 - ‖w‖ ^ 2) ^ 3 * ‖schwarzian G w‖ ^ 2) := by
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℝ, L₀ = π * (200 * (8 * 2 ^ 200) ^ 2) := ⟨_, rfl⟩
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = 203 / 1200 * 4957251 * (93750 / 573) := ⟨_, rfl⟩
  refine ⟨L₀ * (93750 / 573), C₁, ?_⟩
  intro Ω G hG
  obtain ⟨hgd, hSN⟩ := s02_sw_logDeriv hG
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, g = fun w => deriv (deriv G) w / deriv G w := ⟨_, rfl⟩
  rw [← hg] at hgd hSN
  have hgm : Measurable g := by
    rw [hg]
    exact (measurable_deriv _).div (measurable_deriv _)
  have hH : ∀ z ∈ unitDisc, schwarzian G z = deriv g z - 1 / 2 * g z ^ 2 := fun z hz => by
    rw [hSN z hz, hg]
  have hHm : Measurable fun z => deriv g z - 1 / 2 * g z ^ 2 :=
    (measurable_deriv _).sub (measurable_const.mul (hgm.pow_const 2))
  have hL0 : 0 ≤ L₀ := by
    rw [hL₀]
    positivity
  have hC10 : 0 ≤ C₁ := by
    rw [hC₁]
    norm_num
  by_cases hS : ∫⁻ w in unitDisc, ENNReal.ofReal ((1 - ‖w‖ ^ 2) ^ 3 * ‖schwarzian G w‖ ^ 2) = ⊤
  · rw [hS, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by rw [hC₁]; norm_num)).ne', add_top]
    exact le_top
  obtain ⟨σ, hσ0, hσ⟩ : ∃ σ : ℝ, 0 ≤ σ ∧
      ∫⁻ w in unitDisc, ENNReal.ofReal ((1 - ‖w‖ ^ 2) ^ 3 * ‖schwarzian G w‖ ^ 2) =
        ENNReal.ofReal σ := ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hS).symm⟩
  rw [hσ]
  have e0 : ∀ (z : ℂ) (X : ℝ), (1 - ‖(0 : ℂ)‖ ^ 2) / ‖1 - conj (0 : ℂ) * z‖ ^ 2 * X = X := by
    intro z X
    simp
  have h0 : ‖(0 : ℂ)‖ < 1 := by simp
  have hfat := s02_vf_fatou hgd h0
    (M := ENNReal.ofReal (L₀ * (93750 / 573)) + ENNReal.ofReal C₁ * ENNReal.ofReal σ) ?_
  · simp only [e0] at hfat
    refine le_trans (le_of_eq (lintegral_congr fun z => ?_)) hfat
    rw [hg]
    congr 1
    ring
  intro s hs0 hs1
  simp only [e0]
  obtain ⟨hgsd, hgs2⟩ := s02_vf_dil hgd hs0 hs1.le
  obtain ⟨hconf, hNs⟩ := s02_az_cdil hG hs0 hs1.le
  have hNs' : ∀ w, deriv (deriv fun w => G ((s : ℂ) * w)) w / deriv (fun w => G ((s : ℂ) * w)) w =
      (s : ℂ) * g ((s : ℂ) * w) := fun w => by rw [hNs, hg]
  have hNf : (fun w => deriv (deriv fun w => G ((s : ℂ) * w)) w /
      deriv (fun w => G ((s : ℂ) * w)) w) = fun w => (s : ℂ) * g ((s : ℂ) * w) := funext hNs'
  have hB : ∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) * ‖(s : ℂ) * g ((s : ℂ) * z)‖ ≤ 6 := fun z hz => by
    have h := s02_sw_bloch hconf hz
    rwa [hNs'] at h
  have hgsm : Measurable fun w => (s : ℂ) * g ((s : ℂ) * w) :=
    measurable_const.mul (hgm.comp (measurable_const.mul measurable_id))
  -- finiteness of `A_s`
  have hfin := s02_vf_dil_fin hgd hs0 hs1 h0
  simp only [e0] at hfin
  have hAeq : ∫⁻ z in unitDisc, ENNReal.ofReal (‖(s : ℂ) * g ((s : ℂ) * z)‖ ^ 2 * (1 - ‖z‖ ^ 2)) =
      ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) * ‖(s : ℂ) * g ((s : ℂ) * z)‖ ^ 2) :=
    lintegral_congr fun z => by
      congr 1
      ring
  rw [hAeq] at hfin ⊢
  obtain ⟨α, hα0, hα⟩ : ∃ α : ℝ, 0 ≤ α ∧
      ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) * ‖(s : ℂ) * g ((s : ℂ) * z)‖ ^ 2) =
        ENNReal.ofReal α := ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hfin).symm⟩
  -- A2a with `K = 200`, and the low coefficients (A2b)
  have hlp := s02_az_lp_tail hgsd (K := 200) (by norm_num)
  have hρ : (((200 : ℕ) : ℝ) + 3) / (6 * ((200 : ℕ) : ℝ)) = 203 / 1200 := by norm_num
  rw [hρ] at hlp
  have hL : ENNReal.ofReal (π * ∑ n ∈ Finset.range 200,
      ‖((n.factorial : ℂ))⁻¹ * iteratedDeriv n (fun w => (s : ℂ) * g ((s : ℂ) * w)) 0‖ ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) + 2))) ≤ ENNReal.ofReal L₀ := by
    rw [hL₀]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le)
    calc _ ≤ ∑ n ∈ Finset.range 200, ((8 : ℝ) * 2 ^ 200) ^ 2 := Finset.sum_le_sum fun n hn => by
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          refine (div_le_self (sq_nonneg _) (by nlinarith)).trans
            ((pow_le_pow_left₀ (norm_nonneg _) (s02_az_coeff hgsd hB n) 2).trans
              (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left
                (pow_le_pow_right₀ (by norm_num) (Finset.mem_range.mp hn).le) (by norm_num)) 2))
      _ = 200 * ((8 : ℝ) * 2 ^ 200) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat]
  -- A2c pointwise, integrated
  have hBb : ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 *
      ‖deriv (fun w => (s : ℂ) * g ((s : ℂ) * w)) z‖ ^ 2) ≤
      ENNReal.ofReal 51 * (∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 *
        ‖deriv (fun w => (s : ℂ) * g ((s : ℂ) * w)) z - 1 / 2 * ((s : ℂ) * g ((s : ℂ) * z)) ^ 2‖ ^ 2)) +
      ENNReal.ofReal (3672 / 625) * (∫⁻ z in unitDisc,
        ENNReal.ofReal ((1 - ‖z‖ ^ 2) * ‖(s : ℂ) * g ((s : ℂ) * z)‖ ^ 2)) +
      ENNReal.ofReal (8262 / 25) * ∫⁻ z in unitDisc, ENNReal.ofReal
        (if 24 / 5 < (1 - ‖z‖ ^ 2) * ‖(s : ℂ) * g ((s : ℂ) * z)‖ then (1 - ‖z‖ ^ 2)⁻¹ else 0) := by
    have hm1 : Measurable fun z => ENNReal.ofReal 51 * ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 *
        ‖deriv (fun w => (s : ℂ) * g ((s : ℂ) * w)) z -
          1 / 2 * ((s : ℂ) * g ((s : ℂ) * z)) ^ 2‖ ^ 2) :=
      (Measurable.ennreal_ofReal
        ((by fun_prop : Continuous fun z : ℂ => (1 - ‖z‖ ^ 2) ^ 3).measurable.mul
          (((measurable_deriv _).sub (measurable_const.mul (hgsm.pow_const 2))).norm.pow_const
            2))).const_mul _
    have hm2 : Measurable fun z => ENNReal.ofReal (3672 / 625) *
        ENNReal.ofReal ((1 - ‖z‖ ^ 2) * ‖(s : ℂ) * g ((s : ℂ) * z)‖ ^ 2) :=
      (Measurable.ennreal_ofReal
        ((by fun_prop : Continuous fun z : ℂ => 1 - ‖z‖ ^ 2).measurable.mul
          (hgsm.norm.pow_const 2))).const_mul _
    have hm12 : Measurable fun z => ENNReal.ofReal 51 * ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 *
        ‖deriv (fun w => (s : ℂ) * g ((s : ℂ) * w)) z -
          1 / 2 * ((s : ℂ) * g ((s : ℂ) * z)) ^ 2‖ ^ 2) + ENNReal.ofReal (3672 / 625) *
        ENNReal.ofReal ((1 - ‖z‖ ^ 2) * ‖(s : ℂ) * g ((s : ℂ) * z)‖ ^ 2) := hm1.add hm2
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left hm1,
      ← lintegral_add_left hm12]
    refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
    have hx : 0 < 1 - ‖z‖ ^ 2 := by
      have := mem_ball_zero_iff.mp hz
      nlinarith [norm_nonneg z]
    have hp := s02_az_point hx (hB z hz)
      (b := deriv (fun w => (s : ℂ) * g ((s : ℂ) * w)) z)
    have hite : 0 ≤ (if 24 / 5 < (1 - ‖z‖ ^ 2) * ‖(s : ℂ) * g ((s : ℂ) * z)‖ then
        (1 - ‖z‖ ^ 2)⁻¹ else 0) := by
      split_ifs
      · exact (inv_pos.mpr hx).le
      · exact le_rfl
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg hx.le 3)
        (sq_nonneg _))) (mul_nonneg (by norm_num) (mul_nonneg hx.le (sq_nonneg _))),
      ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg hx.le 3)
        (sq_nonneg _))) (mul_nonneg (by norm_num) (mul_nonneg hx.le (sq_nonneg _))))
        (mul_nonneg (by norm_num) hite)]
    exact ENNReal.ofReal_le_ofReal hp
  -- the Schwarzian side: `S_{G_s}` and `g_s' − ½g_s²` both reduce to `s²(g' − ½g²)(sw)`
  have hSs : ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 *
      ‖deriv (fun w => (s : ℂ) * g ((s : ℂ) * w)) z - 1 / 2 * ((s : ℂ) * g ((s : ℂ) * z)) ^ 2‖ ^ 2) ≤
      ENNReal.ofReal σ := by
    rw [← hσ]
    calc _ ≤ ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 *
          ‖(s : ℂ) * (deriv g ((s : ℂ) * z) - 1 / 2 * g ((s : ℂ) * z) ^ 2)‖ ^ 2) := by
          refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
          refine ENNReal.ofReal_le_ofReal ?_
          have hx : 0 ≤ 1 - ‖z‖ ^ 2 := by
            have := mem_ball_zero_iff.mp hz
            nlinarith [norm_nonneg z]
          rw [hgs2 z hz, pow_two (s : ℂ), mul_assoc, norm_mul _ ((s : ℂ) * _)]
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
            (mul_le_of_le_one_left (norm_nonneg _) ?_) 2) (pow_nonneg hx 3)
          rw [Complex.norm_real, Real.norm_of_nonneg hs0.le]
          exact hs1.le
      _ ≤ ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 *
          ‖deriv g z - 1 / 2 * g z ^ 2‖ ^ 2) := s02_vd_scale hHm hs0 hs1.le
      _ = _ := setLIntegral_congr_fun measurableSet_ball fun z hz => by rw [hH z hz]
  have hSG : ∫⁻ v in unitDisc, ENNReal.ofReal ((1 - ‖v‖ ^ 2) ^ 3 *
      ‖schwarzian (fun w => G ((s : ℂ) * w)) v‖ ^ 2) =
      ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ 3 *
        ‖deriv (fun w => (s : ℂ) * g ((s : ℂ) * w)) z - 1 / 2 * ((s : ℂ) * g ((s : ℂ) * z)) ^ 2‖ ^ 2) := by
    obtain ⟨_, hSNs⟩ := s02_sw_logDeriv hconf
    refine setLIntegral_congr_fun measurableSet_ball fun v hv => ?_
    rw [hSNs v hv, hNf, hNs']
  -- A2f for `G_s`
  have he := s02_az_epart hconf
  simp only [hNs'] at he
  rw [hSG] at he
  have hE := he.trans (mul_le_mul' le_rfl hSs)
  rw [← ENNReal.ofReal_mul (by norm_num)] at hE
  -- absorption
  have hBr := hBb.trans (add_le_add (add_le_add (mul_le_mul' le_rfl hSs) le_rfl)
    (mul_le_mul' le_rfl hE))
  rw [hα, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (mul_nonneg (by norm_num) hσ0) (mul_nonneg (by norm_num) hα0),
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (by norm_num) hσ0) (mul_nonneg (by norm_num) hα0))
      (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hσ0))] at hBr
  rw [hα] at hlp ⊢
  have hA := hlp.trans (add_le_add hL (mul_le_mul' le_rfl hBr))
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add hL0 (mul_nonneg (by norm_num)
    (add_nonneg (add_nonneg (mul_nonneg (by norm_num) hσ0) (mul_nonneg (by norm_num) hα0))
      (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hσ0))))] at hA
  have ha := (ENNReal.ofReal_le_ofReal_iff (add_nonneg hL0 (mul_nonneg (by norm_num)
    (add_nonneg (add_nonneg (mul_nonneg (by norm_num) hσ0) (mul_nonneg (by norm_num) hα0))
      (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hσ0)))))).mp hA
  rw [← ENNReal.ofReal_mul hC10, ← ENNReal.ofReal_add (by positivity) (mul_nonneg hC10 hσ0)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hC₁]
  linarith

/-- Shen–Wei (B3) ⇒ (B2) for quasidisks: the backward half of `thm_shen_wei_B` (Shen–Wei,
Thm A; wall W-AZ in `collaboration/SW_PLAN.md`). -/
theorem s02_sw_B_bwd {Ω Ωs : Set ℂ} {K : ℝ}
    (hq : IsBoundedKQuasicircle Ω Ωs K ∨ IsKQuasiPair Ω Ωs K) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) :
    IsCarlesonDisk (schwarzCarlesonMeasure f) → LogDerivBMOA f := by
  -- `hq` is not needed: Astala–Zinsmeister's Lemma 1 holds for every conformal `f` of `𝔻`.
  have _hq := hq
  intro hS
  obtain ⟨C₀, C₁, hcen⟩ := s02_az_center
  obtain ⟨C, hC0, hC⟩ := s02_vc_real hS
  obtain ⟨_, hSf⟩ := s02_sw_logDeriv hf
  have hgm : Measurable fun z => deriv (deriv f) z / deriv f z :=
    (measurable_deriv _).div (measurable_deriv _)
  have hSm : Measurable fun z => ‖deriv (fun w => deriv (deriv f) w / deriv f w) z -
      1 / 2 * (deriv (deriv f) z / deriv f z) ^ 2‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3 :=
    (((measurable_deriv _).sub (measurable_const.mul (hgm.pow_const 2))).norm.pow_const 2).mul
      (by fun_prop : Continuous fun z : ℂ => (1 - ‖z‖ ^ 2) ^ 3).measurable
  have hlam : schwarzCarlesonMeasure f = (volume.restrict unitDisc).withDensity fun z =>
      ENNReal.ofReal (‖deriv (fun w => deriv (deriv f) w / deriv f w) z -
        1 / 2 * (deriv (deriv f) z / deriv f z) ^ 2‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) := by
    unfold schwarzCarlesonMeasure
    refine withDensity_congr_ae ((ae_restrict_iff' (measurableSet_ball :
      MeasurableSet unitDisc)).mpr (ae_of_all _ fun z hz => ?_))
    dsimp only
    rw [hSf z hz]
  have hdm : Measurable fun z => ‖deriv (deriv f) z / deriv f z‖ ^ 2 * (1 - ‖z‖ ^ 2) :=
    (hgm.norm.pow_const 2).mul (by fun_prop : Continuous fun z : ℂ => 1 - ‖z‖ ^ 2).measurable
  show IsCarlesonDisk ((volume.restrict unitDisc).withDensity fun z =>
    ENNReal.ofReal (‖deriv (deriv f) z / deriv f z‖ ^ 2 * (1 - ‖z‖ ^ 2)))
  refine s02_vc_of_kernel (M := 2 * (max C₀ 0 + max C₁ 0 * (108 * C)) + 8 * π) fun ζ hζ => ?_
  rw [s02_vf_kernel_wd hdm hζ]
  obtain ⟨hp1, hp2⟩ := s02_az_pull hf hζ
  have hk : ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ ^ 2 *
      (‖schwarzian f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3)) ≤ ENNReal.ofReal (108 * C) := by
    have h := s02_vc_kernel_bound hC0 hC hζ
    rw [hlam, s02_vf_kernel_wd hSm hζ] at h
    refine le_of_eq_of_le (setLIntegral_congr_fun measurableSet_ball fun z hz => ?_) h
    rw [hSf z hz]
  have hc := hcen (s02_az_frame hf hζ).1
  rw [hp2] at hc
  have hπ := Real.pi_pos
  refine hp1.trans ?_
  calc _ ≤ 2 * (ENNReal.ofReal (max C₀ 0) + ENNReal.ofReal (max C₁ 0) *
          ENNReal.ofReal (108 * C)) + ENNReal.ofReal (8 * π) := by
        gcongr
        refine hc.trans (add_le_add (ENNReal.ofReal_le_ofReal (le_max_left _ _))
          (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hk))
    _ = _ := by
        rw [← ENNReal.ofReal_mul (le_max_right _ _),
          ← ENNReal.ofReal_add (le_max_right _ _) (by positivity),
          ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- Theorem 2.13 `thm:shen-wei`, (B2) ⇔ (B3), `sec02-prelim.tex:592` (Shen–Wei, Thm A):
for `f : 𝔻 → Ω` conformal onto a quasidisk (bounded, or with `∞` on its boundary),
`log f' ∈ BMOA ⇔ |S f|²(1-|z|²)³ dA ∈ CM(𝔻)`. -/
theorem thm_shen_wei_B {Ω Ωs : Set ℂ} {K : ℝ}
    (hq : IsBoundedKQuasicircle Ω Ωs K ∨ IsKQuasiPair Ω Ωs K) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) :
    LogDerivBMOA f ↔ IsCarlesonDisk (schwarzCarlesonMeasure f) := by
  exact ⟨s02_sw_B_fwd hf, s02_sw_B_bwd hq hf⟩

/-- Theorem 2.13 `thm:shen-wei`, (V2) ⇔ (V3), `sec02-prelim.tex:600` (Shen–Wei, Thm 4.1): for
bounded `f`, `log f' ∈ VMOA ⇔ |S f|²(1-|z|²)³ dA ∈ CM₀(𝔻)`. -/
theorem thm_shen_wei_V {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K)
    {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) :
    LogDerivVMOA f ↔ IsVanishingCarlesonDisk (schwarzCarlesonMeasure f) := by
  exact ⟨s02_sw_V_fwd hf, s02_sw_V_bwd hq hf⟩

/-- The inverse Cayley transform maps `Δ` conformally onto `ℍ`. -/
theorem s02_cayleyInv_conformal : IsConformalOnto cayleyInv unitDisc upperHalf := by
  refine ⟨fun w hw => ?_, fun a ha b hb hab => ?_, ?_⟩
  · have hw' : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have hd : DifferentiableAt ℂ (fun w : ℂ => I * (1 + w) / (1 - w)) w :=
      ((differentiableAt_const _).mul ((differentiableAt_const _).add differentiableAt_id)).div
        ((differentiableAt_const _).sub differentiableAt_id) (cayleyInv_den_ne_zero hw')
    exact hd.differentiableWithinAt
  · have h := congrArg cayley hab
    rwa [cayley_cayleyInv (mem_ball_zero_iff.mp ha), cayley_cayleyInv (mem_ball_zero_iff.mp hb)] at h
  · ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp hw)
    · intro hz
      exact ⟨cayley z, cayley_mem_unitDisc hz, cayleyInv_cayley hz⟩

/-- `(log f')' = f''/f' = 2/(1-z)` for the inverse Cayley transform `f(z) = i(1+z)/(1-z)`. -/
theorem s02_cayleyInv_logDeriv {z : ℂ} (hz : z ≠ 1) :
    deriv (deriv cayleyInv) z / deriv cayleyInv z = 2 / (1 - z) := by
  have hI : I ≠ 0 := I_ne_zero
  have hd1 : ∀ w : ℂ, w ≠ 1 → HasDerivAt cayleyInv (2 * I / (1 - w) ^ 2) w := by
    intro w hw
    have hw' : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
    have h1 : HasDerivAt (fun x : ℂ => I * (1 + x)) (I * 1) w :=
      ((hasDerivAt_id w).const_add 1).const_mul I
    have h2 : HasDerivAt (fun x : ℂ => 1 - x) (-1) w := (hasDerivAt_id w).const_sub 1
    have h := h1.div h2 hw'
    have e : (I * 1 * (1 - w) - I * (1 + w) * (-1)) / (1 - w) ^ 2 = 2 * I / (1 - w) ^ 2 := by
      ring
    rw [e] at h
    exact h
  have hz' : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hev : deriv cayleyInv =ᶠ[𝓝 z] fun w => 2 * I / (1 - w) ^ 2 := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show z ∈ ({1}ᶜ : Set ℂ) from hz)] with w hw
    exact (hd1 w hw).deriv
  have h3 : HasDerivAt (fun w : ℂ => 2 * I / (1 - w) ^ 2) (4 * I / (1 - z) ^ 3) z := by
    have h2 : HasDerivAt (fun x : ℂ => (1 - x) ^ 2) (2 * (1 - z) * (-1)) z := by
      have := ((hasDerivAt_id z).const_sub 1).fun_pow 2
      simpa using this
    have h := (hasDerivAt_const z (2 * I)).div h2 (pow_ne_zero 2 hz')
    have e : (0 * (1 - z) ^ 2 - 2 * I * (2 * (1 - z) * (-1))) / ((1 - z) ^ 2) ^ 2 =
        4 * I / (1 - z) ^ 3 := by
      field_simp
      ring
    rw [e] at h
    exact h
  rw [hev.deriv_eq, h3.deriv, (hd1 z hz).deriv]
  field_simp
  ring

/-- §2.9, `sec02-prelim.tex:608` (Shen–Wei, Remark 4.1): the boundedness hypothesis of the second
half is necessary; e.g. `f(z) = (1+z)/(1-z)` onto a half-plane has `S f = 0` but
`log f' = log 2 - 2 log(1-z) ∉ VMOA`. -/
theorem thm_shen_wei_bounded_necessary :
    ∃ (Ω Ωs : Set ℂ) (K : ℝ) (f : ℂ → ℂ), IsKQuasiPair Ω Ωs K ∧
      IsConformalOnto f unitDisc Ω ∧ IsVanishingCarlesonDisk (schwarzCarlesonMeasure f) ∧
      ¬ LogDerivVMOA f := by
  have hS : ∀ z, schwarzian cayleyInv z = 0 := by
    intro z
    have hfun : cayleyInv = fun w => (I * w + I) / (-1 * w + 1) := by
      funext w
      unfold cayleyInv
      ring
    rw [hfun]
    exact schwarzian_mobius cayley_det z
  have hid : IsConformalOnto (id : ℂ → ℂ) univ univ :=
    ⟨differentiableOn_id, injOn_id _, image_id _⟩
  refine ⟨upperHalf, lowerHalf, 1, cayleyInv,
    ⟨id, isKQC_one_of_conformal isOpen_univ hid, image_id _, image_id _, image_id _⟩,
    s02_cayleyInv_conformal, ?_, ?_⟩
  · -- `S f ≡ 0`: the Schwarzian measure vanishes
    have h0 : schwarzCarlesonMeasure cayleyInv = 0 := by
      unfold schwarzCarlesonMeasure
      have : (fun z => ENNReal.ofReal (‖schwarzian cayleyInv z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3)) = 0 := by
        funext z
        simp [hS z]
      rw [this, withDensity_zero]
    rw [h0]
    exact ⟨⟨0, ENNReal.zero_ne_top, fun _ _ _ _ _ => by simp⟩,
      fun _ _ => ⟨1, one_pos, fun _ _ _ _ _ => by simp⟩⟩
  · -- `μ(𝔻 ∩ D(1, r)) ≥ π r / 16`, so `log f' ∉ VMOA`
    rintro ⟨-, hvan⟩
    obtain ⟨δ, hδ, hδb⟩ := hvan (1 / 10) (by norm_num)
    set r := min (δ / 2) (1 / 2) with hr
    have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
    have hrδ : r < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hr1 : r ≤ 1 / 2 := min_le_right _ _
    have h1 : (1 : ℂ) ∈ sphere (0 : ℂ) 1 := by simp
    have hb := hδb 1 h1 r hr0 hrδ
    set c0 : ℂ := ((1 - r / 2 : ℝ) : ℂ) with hc0
    have hc0n : ‖c0‖ = 1 - r / 2 := by
      rw [hc0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hc01 : ‖1 - c0‖ = r / 2 := by
      rw [hc0, show (1 : ℂ) - ((1 - r / 2 : ℝ) : ℂ) = ((r / 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hzc : ∀ z ∈ ball c0 (r / 4), ‖z‖ < 1 - r / 4 := by
      intro z hz
      have hz' : ‖z - c0‖ < r / 4 := by
        rw [← dist_eq_norm]
        exact hz
      calc ‖z‖ = ‖c0 + (z - c0)‖ := by ring_nf
        _ ≤ ‖c0‖ + ‖z - c0‖ := norm_add_le _ _
        _ < 1 - r / 4 := by rw [hc0n]; linarith
    have hsub : ball c0 (r / 4) ⊆ unitDisc ∩ ball 1 r := by
      intro z hz
      have hz' : ‖z - c0‖ < r / 4 := by
        rw [← dist_eq_norm]
        exact hz
      refine ⟨mem_ball_zero_iff.mpr (by linarith [hzc z hz]), ?_⟩
      show dist z 1 < r
      rw [dist_eq_norm]
      calc ‖z - 1‖ = ‖(z - c0) - (1 - c0)‖ := by ring_nf
        _ ≤ ‖z - c0‖ + ‖1 - c0‖ := norm_sub_le _ _
        _ < r := by rw [hc01]; linarith
    have hdens : ∀ z ∈ ball c0 (r / 4), ENNReal.ofReal (1 / r) ≤
        ENNReal.ofReal (‖deriv (deriv cayleyInv) z / deriv cayleyInv z‖ ^ 2 * (1 - ‖z‖ ^ 2)) := by
      intro z hz
      obtain ⟨hzD, hz1⟩ := hsub hz
      have hzn : ‖z‖ < 1 - r / 4 := hzc z hz
      have hzne : z ≠ 1 := by
        intro h
        rw [h, norm_one] at hzn
        linarith
      have hb1 : ‖1 - z‖ < r := by
        have : dist 1 z < r := by
          rw [dist_comm]
          exact hz1
        rwa [dist_eq_norm] at this
      have hb0 : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hzne))
      apply ENNReal.ofReal_le_ofReal
      rw [s02_cayleyInv_logDeriv hzne, norm_div, Complex.norm_two, div_pow, div_mul_eq_mul_div,
        le_div_iff₀ (by positivity)]
      have h4 : 1 / r * ‖1 - z‖ ^ 2 ≤ r := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hr0]
        nlinarith
      have h5 : r ≤ 2 ^ 2 * (1 - ‖z‖ ^ 2) := by
        nlinarith [norm_nonneg z]
      linarith
    have hmeas : ENNReal.ofReal (1 / r) * volume (ball c0 (r / 4)) ≤
        derivCarlesonMeasure (fun z => deriv (deriv cayleyInv) z / deriv cayleyInv z)
          (unitDisc ∩ ball 1 r) := by
      calc ENNReal.ofReal (1 / r) * volume (ball c0 (r / 4)) =
          ∫⁻ _ in ball c0 (r / 4), ENNReal.ofReal (1 / r) := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ z in ball c0 (r / 4),
            ENNReal.ofReal (‖deriv (deriv cayleyInv) z / deriv cayleyInv z‖ ^ 2 * (1 - ‖z‖ ^ 2)) :=
          setLIntegral_mono' measurableSet_ball hdens
        _ = derivCarlesonMeasure (fun z => deriv (deriv cayleyInv) z / deriv cayleyInv z)
            (ball c0 (r / 4)) := by
          unfold derivCarlesonMeasure
          rw [withDensity_apply _ measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
            inter_eq_left.mpr (fun z hz => (hsub hz).1)]
        _ ≤ _ := measure_mono hsub
    have hle := hmeas.trans hb
    rw [Complex.volume_ball, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
      ← ENNReal.ofReal_pow (p := r / 4) (by positivity),
      ← ENNReal.ofReal_mul (p := (r / 4) ^ 2) (by positivity),
      ← ENNReal.ofReal_mul (p := 1 / r) (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
    have e : 1 / r * ((r / 4) ^ 2 * π) = π * r / 16 := by
      field_simp
      ring
    rw [e] at hle
    nlinarith [Real.pi_gt_three]

/-- Carleson helper (density identity): on `𝔻`,
`(1-|z|²) s(fz)² λ(fz)² |f'(z)|² = |Sf(z)|² (1-|z|²)³ / 4` (from (2.17) and `eq_lambda_f`). -/
theorem s02_cm_density {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {z : ℂ}
    (hz : z ∈ unitDisc) :
    (1 - ‖z‖ ^ 2) * (schwarzNorm Ω (f z) ^ 2 * poincareDensity Ω (f z) ^ 2 * ‖deriv f z‖ ^ 2) =
      ‖schwarzian f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3 / 4 := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hr : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  rw [eq_s_disk hf hz, mul_assoc (_ ^ 2), ← mul_pow, eq_lambda_f hf hz]
  field_simp
  ring

/-- Carleson helper: the measure of §2.9 is `¼` of the Schwarzian Carleson measure. -/
theorem s02_cm_measure_eq {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) :
    ((volume.restrict unitDisc).withDensity fun z =>
      ENNReal.ofReal ((1 - ‖z‖ ^ 2) * (schwarzNorm Ω (f z) ^ 2 *
        poincareDensity Ω (f z) ^ 2 * ‖deriv f z‖ ^ 2))) =
      ENNReal.ofReal (1 / 4) • schwarzCarlesonMeasure f := by
  unfold schwarzCarlesonMeasure
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet unitDisc)] with z hz
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [s02_cm_density hf hz, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-- Carleson helper: `CM(𝔻)` and `CM₀(𝔻)` are invariant under multiplication by a constant
`0 < c < ∞`. -/
theorem s02_cm_smul {μ : Measure ℂ} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) :
    (IsCarlesonDisk (c • μ) ↔ IsCarlesonDisk μ) ∧
      (IsVanishingCarlesonDisk (c • μ) ↔ IsVanishingCarlesonDisk μ) := by
  have hct : 0 < c.toReal := ENNReal.toReal_pos hc0 hc
  have hmul : ∀ x : ℝ, c * ENNReal.ofReal x = ENNReal.ofReal (c.toReal * x) := fun x => by
    rw [ENNReal.ofReal_mul hct.le, ENNReal.ofReal_toReal hc]
  have hC : IsCarlesonDisk (c • μ) ↔ IsCarlesonDisk μ := by
    constructor
    · rintro ⟨C, hC, h⟩
      refine ⟨C / c, ENNReal.div_ne_top hC hc0, fun ζ hζ r hr hr2 => ?_⟩
      have h1 := h ζ hζ r hr hr2
      rw [Measure.smul_apply, smul_eq_mul, mul_comm,
        ← ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hc)] at h1
      rwa [← ENNReal.mul_div_right_comm]
    · rintro ⟨C, hC, h⟩
      refine ⟨c * C, ENNReal.mul_ne_top hc hC, fun ζ hζ r hr hr2 => ?_⟩
      rw [Measure.smul_apply, smul_eq_mul, mul_assoc]
      exact mul_le_mul_right (h ζ hζ r hr hr2) c
  refine ⟨hC, ?_⟩
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hC.1 h1, fun ε hε => ?_⟩
    obtain ⟨δ, hδ, h⟩ := h2 (ε * c.toReal) (by positivity)
    refine ⟨δ, hδ, fun ζ hζ r hr hrδ => ?_⟩
    have h3 := h ζ hζ r hr hrδ
    rw [Measure.smul_apply, smul_eq_mul, show ε * c.toReal * r = c.toReal * (ε * r) by ring,
      ← hmul] at h3
    exact (ENNReal.mul_le_mul_iff_right hc0 hc).1 h3
  · rintro ⟨h1, h2⟩
    refine ⟨hC.2 h1, fun ε hε => ?_⟩
    obtain ⟨δ, hδ, h⟩ := h2 (ε / c.toReal) (by positivity)
    refine ⟨δ, hδ, fun ζ hζ r hr hrδ => ?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    calc c * μ (unitDisc ∩ ball ζ r) ≤ c * ENNReal.ofReal (ε / c.toReal * r) :=
          mul_le_mul_right (h ζ hζ r hr hrδ) c
      _ = ENNReal.ofReal (ε * r) := by
          rw [hmul]
          congr 1
          field_simp

/-- Carleson helper: a disc automorphism `φ = c·M_a` is `L`-Lipschitz on the closed disc,
`L = (1+|a|)/(1-|a|)`, and maps the unit circle to itself. -/
theorem s02_cm_blaschke_lip {a c z ζ : ℂ} (ha : ‖a‖ < 1) (hc : ‖c‖ = 1) (hz : ‖z‖ ≤ 1)
    (hζ : ‖ζ‖ ≤ 1) :
    ‖c * blaschke a z - c * blaschke a ζ‖ ≤ (1 + ‖a‖) / (1 - ‖a‖) * ‖z - ζ‖ ∧
      (‖ζ‖ = 1 → ‖c * blaschke a ζ‖ = 1) := by
  have ha1 : 0 < 1 - ‖a‖ := by linarith
  have hd : ∀ w : ℂ, ‖w‖ ≤ 1 → 1 - ‖a‖ ≤ ‖1 - conj a * w‖ := fun w hw => by
    have h1 := norm_sub_norm_le (1 : ℂ) (conj a * w)
    rw [norm_one, norm_mul, Complex.norm_conj] at h1
    nlinarith [norm_nonneg a, norm_nonneg w]
  have hz0 : 1 - conj a * z ≠ 0 := norm_ne_zero_iff.mp (lt_of_lt_of_le ha1 (hd z hz)).ne'
  have hζ0 : 1 - conj a * ζ ≠ 0 := norm_ne_zero_iff.mp (lt_of_lt_of_le ha1 (hd ζ hζ)).ne'
  constructor
  · have key : c * blaschke a z - c * blaschke a ζ =
        c * ((1 - a * conj a) * (z - ζ) / ((1 - conj a * z) * (1 - conj a * ζ))) := by
      unfold blaschke
      rw [← mul_sub, div_sub_div _ _ hz0 hζ0]
      congr 2
      ring
    have hn : ‖1 - a * conj a‖ = 1 - ‖a‖ ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      norm_cast
      rw [Real.norm_of_nonneg (by nlinarith [norm_nonneg a])]
    have hden : (1 - ‖a‖) ^ 2 ≤ ‖1 - conj a * z‖ * ‖1 - conj a * ζ‖ := by
      rw [sq]
      exact mul_le_mul (hd z hz) (hd ζ hζ) ha1.le (norm_nonneg _)
    rw [key, norm_mul, hc, one_mul, norm_div, norm_mul, norm_mul, hn,
      div_le_iff₀ (lt_of_lt_of_le (by positivity) hden)]
    calc (1 - ‖a‖ ^ 2) * ‖z - ζ‖ = (1 + ‖a‖) / (1 - ‖a‖) * ‖z - ζ‖ * (1 - ‖a‖) ^ 2 := by
          field_simp
          ring
      _ ≤ (1 + ‖a‖) / (1 - ‖a‖) * ‖z - ζ‖ * (‖1 - conj a * z‖ * ‖1 - conj a * ζ‖) :=
          mul_le_mul_of_nonneg_left hden (by positivity)
  · intro h1
    have hζa : ζ - a ≠ 0 := by
      intro h0
      rw [sub_eq_zero] at h0
      rw [h0] at h1
      linarith
    have e : 1 - conj a * ζ = ζ * conj (ζ - a) := by
      have hζζ : ζ * conj ζ = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
        norm_num
      rw [map_sub, mul_sub, hζζ]
      ring
    rw [norm_mul, hc, one_mul, blaschke, norm_div, e, norm_mul, h1, one_mul, Complex.norm_conj,
      div_self (norm_ne_zero_iff.mpr hζa)]

/-- Carleson helper (Möbius transfer at one box): if `F, f` are conformal maps of `𝔻` onto the
same `Ω` (so `F = f ∘ φ`, `φ ∈ Aut 𝔻`), each box of `F` is controlled by a box of `f`, with a
constant `L ≥ 1` depending only on `φ`. -/
theorem s02_cm_box {Ω : Set ℂ} {f F : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (hF : IsConformalOnto F unitDisc Ω) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → ∃ ζ' ∈ sphere (0 : ℂ) 1,
      schwarzCarlesonMeasure F (unitDisc ∩ ball ζ r) ≤
        ENNReal.ofReal L * schwarzCarlesonMeasure f (unitDisc ∩ ball ζ' (L * r)) := by
  obtain ⟨c, b, hc, hb, hcb⟩ := s02_riemannMap_factor hf hF
  have hb1 : 0 < 1 - ‖b‖ := by linarith
  refine ⟨(1 + ‖b‖) / (1 - ‖b‖), by rw [le_div_iff₀ hb1]; linarith [norm_nonneg b],
    fun ζ hζ r hr => ?_⟩
  set L := (1 + ‖b‖) / (1 - ‖b‖) with hL
  have hL0 : 0 < L := by positivity
  have hζ1 : ‖ζ‖ = 1 := by simpa using hζ
  refine ⟨c * blaschke b ζ, by simpa using (s02_cm_blaschke_lip hb hc hζ1.le hζ1.le).2 hζ1, ?_⟩
  have hEm : MeasurableSet (unitDisc ∩ ball ζ r) := measurableSet_ball.inter measurableSet_ball
  have hE1 : unitDisc ∩ ball ζ r ⊆ unitDisc := inter_subset_left
  have hμ : ∀ (g : ℂ → ℂ) (S : Set ℂ), MeasurableSet S → S ⊆ unitDisc →
      schwarzCarlesonMeasure g S =
        ∫⁻ z in S, ENNReal.ofReal (‖schwarzian g z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) := by
    intro g S hS hS1
    unfold schwarzCarlesonMeasure
    rw [withDensity_apply _ hS, Measure.restrict_restrict hS, inter_eq_left.mpr hS1]
  rw [hμ F _ hEm hE1, hμ f (unitDisc ∩ ball (c * blaschke b ζ) (L * r))
    (measurableSet_ball.inter measurableSet_ball) inter_subset_left]
  set H : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (‖schwarzian f w‖ ^ 2 * (1 - ‖w‖ ^ 2) ^ 3)
    with hH
  -- `|SF|²(1-|z|²)³ = |Sf(φz)|²(1-|φz|²)³ |φ'(z)| ≤ L |φ'(z)|² |Sf(φz)|²(1-|φz|²)³`
  have hpt : ∀ z ∈ unitDisc ∩ ball ζ r,
      ENNReal.ofReal (‖schwarzian F z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) ≤
        ENNReal.ofReal L * (ENNReal.ofReal (((1 - ‖b‖ ^ 2) / ‖1 - conj b * z‖ ^ 2) ^ 2) *
          H (c * blaschke b z)) := by
    intro z hz
    have hzD := hE1 hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hzD
    have hu : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have hφD : c * blaschke b z ∈ unitDisc := by
      refine mem_ball_zero_iff.mpr ?_
      rw [norm_mul, hc, one_mul]
      exact blaschke_mem_unitDisc hb hz1
    have hfac := s02_schwarzian_factor hf hF hφD hzD (hcb z hzD).2
    have hden : 0 < ‖1 - conj b * z‖ := norm_pos_iff.mpr (blaschke_den_ne_zero hb hz1)
    have hv : 1 - ‖c * blaschke b z‖ ^ 2 =
        (1 - ‖b‖ ^ 2) / ‖1 - conj b * z‖ ^ 2 * (1 - ‖z‖ ^ 2) := by
      have h1 := one_sub_normSq_blaschke hb hz1
      simp only [Complex.normSq_eq_norm_sq] at h1
      rw [norm_mul, hc, one_mul, h1]
      ring
    set p := (1 - ‖b‖ ^ 2) / ‖1 - conj b * z‖ ^ 2 with hp
    have hp0 : 0 ≤ p := div_nonneg (by nlinarith [norm_nonneg b]) (sq_nonneg _)
    have hLp : 1 ≤ L * p := by
      have hn : ‖1 - conj b * z‖ ≤ 1 + ‖b‖ := by
        calc ‖1 - conj b * z‖ ≤ ‖(1 : ℂ)‖ + ‖conj b * z‖ := norm_sub_le _ _
          _ ≤ 1 + ‖b‖ := by
            rw [norm_one, norm_mul, Complex.norm_conj]
            nlinarith [norm_nonneg b, norm_nonneg z]
      have e : L * p = (1 + ‖b‖) ^ 2 / ‖1 - conj b * z‖ ^ 2 := by
        rw [hL, hp]
        field_simp
        ring
      rw [e, one_le_div (by positivity)]
      exact pow_le_pow_left₀ hden.le hn 2
    rw [hv] at hfac
    have hX : ‖schwarzian F z‖ = ‖schwarzian f (c * blaschke b z)‖ * p ^ 2 := by
      apply mul_right_cancel₀ (pow_pos hu 2).ne'
      rw [hfac]
      ring
    rw [hH]
    dsimp only
    rw [hX, hv, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hL0.le]
    apply ENNReal.ofReal_le_ofReal
    have hY : 0 ≤ ‖schwarzian f (c * blaschke b z)‖ ^ 2 * p ^ 4 * (1 - ‖z‖ ^ 2) ^ 3 := by
      positivity
    calc (‖schwarzian f (c * blaschke b z)‖ * p ^ 2) ^ 2 * (1 - ‖z‖ ^ 2) ^ 3 =
          1 * (‖schwarzian f (c * blaschke b z)‖ ^ 2 * p ^ 4 * (1 - ‖z‖ ^ 2) ^ 3) := by ring
      _ ≤ (L * p) * (‖schwarzian f (c * blaschke b z)‖ ^ 2 * p ^ 4 * (1 - ‖z‖ ^ 2) ^ 3) :=
          mul_le_mul_of_nonneg_right hLp hY
      _ = _ := by ring
  calc ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal (‖schwarzian F z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3)
        ≤ ∫⁻ z in unitDisc ∩ ball ζ r, ENNReal.ofReal L *
          (ENNReal.ofReal (((1 - ‖b‖ ^ 2) / ‖1 - conj b * z‖ ^ 2) ^ 2) * H (c * blaschke b z)) :=
        setLIntegral_mono' hEm hpt
    _ = ENNReal.ofReal L * ∫⁻ z in unitDisc ∩ ball ζ r,
          ENNReal.ofReal (((1 - ‖b‖ ^ 2) / ‖1 - conj b * z‖ ^ 2) ^ 2) * H (c * blaschke b z) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal L * ∫⁻ w in (fun z => c * blaschke b z) '' (unitDisc ∩ ball ζ r), H w := by
        rw [s02_cm_lintegral_blaschke hb hc hEm hE1 H]
    _ ≤ ENNReal.ofReal L * ∫⁻ w in unitDisc ∩ ball (c * blaschke b ζ) (L * r), H w := by
        refine mul_le_mul_right (lintegral_mono_set ?_) _
        rintro _ ⟨z, hz, rfl⟩
        have hzD := hE1 hz
        have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hzD
        refine ⟨?_, ?_⟩
        · refine mem_ball_zero_iff.mpr ?_
          rw [norm_mul, hc, one_mul]
          exact blaschke_mem_unitDisc hb hz1
        · rw [mem_ball, dist_eq_norm]
          have hzr : ‖z - ζ‖ < r := by
            have := hz.2
            rwa [mem_ball, dist_eq_norm] at this
          calc ‖c * blaschke b z - c * blaschke b ζ‖ ≤ L * ‖z - ζ‖ :=
                (s02_cm_blaschke_lip hb hc hz1.le hζ1.le).1
            _ < L * r := mul_lt_mul_of_pos_left hzr hL0

/-- Carleson helper: the Schwarzian Carleson condition (and its vanishing version) does not depend
on the choice of the Riemann map of `Ω`. -/
theorem s02_cm_transfer {Ω : Set ℂ} {f F : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (hF : IsConformalOnto F unitDisc Ω) :
    (IsCarlesonDisk (schwarzCarlesonMeasure f) → IsCarlesonDisk (schwarzCarlesonMeasure F)) ∧
      (IsVanishingCarlesonDisk (schwarzCarlesonMeasure f) →
        IsVanishingCarlesonDisk (schwarzCarlesonMeasure F)) := by
  obtain ⟨L, hL, hbox⟩ := s02_cm_box hf hF
  have hL0 : 0 < L := by linarith
  have hCar : IsCarlesonDisk (schwarzCarlesonMeasure f) →
      IsCarlesonDisk (schwarzCarlesonMeasure F) := by
    rintro ⟨C, hC, h⟩
    have hM := s02_cm_total ⟨C, hC, h⟩
    refine ⟨ENNReal.ofReal L * C * ENNReal.ofReal L +
        ENNReal.ofReal L * schwarzCarlesonMeasure f unitDisc * ENNReal.ofReal (L / 2),
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC)
        ENNReal.ofReal_ne_top, ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM)
        ENNReal.ofReal_ne_top⟩, fun ζ hζ r hr hr2 => ?_⟩
    obtain ⟨ζ', hζ', hle⟩ := hbox ζ hζ r hr
    refine hle.trans ?_
    rcases lt_or_ge (L * r) 2 with h2 | h2
    · calc ENNReal.ofReal L * schwarzCarlesonMeasure f (unitDisc ∩ ball ζ' (L * r))
          ≤ ENNReal.ofReal L * (C * ENNReal.ofReal (L * r)) :=
            mul_le_mul_right (h ζ' hζ' (L * r) (by positivity) h2) _
        _ = ENNReal.ofReal L * C * ENNReal.ofReal L * ENNReal.ofReal r := by
            rw [ENNReal.ofReal_mul hL0.le]
            ring
        _ ≤ _ := mul_le_mul_left le_self_add _
    · calc ENNReal.ofReal L * schwarzCarlesonMeasure f (unitDisc ∩ ball ζ' (L * r))
          ≤ ENNReal.ofReal L * schwarzCarlesonMeasure f unitDisc * 1 := by
            rw [mul_one]
            exact mul_le_mul_right (measure_mono inter_subset_left) _
        _ ≤ ENNReal.ofReal L * schwarzCarlesonMeasure f unitDisc *
            (ENNReal.ofReal (L / 2) * ENNReal.ofReal r) := by
            refine mul_le_mul_right ?_ _
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (by linarith)
        _ = ENNReal.ofReal L * schwarzCarlesonMeasure f unitDisc * ENNReal.ofReal (L / 2) *
            ENNReal.ofReal r := by ring
        _ ≤ _ := mul_le_mul_left le_add_self _
  refine ⟨hCar, fun hV => ⟨hCar hV.1, fun ε hε => ?_⟩⟩
  obtain ⟨δ, hδ, h⟩ := hV.2 (ε / L ^ 2) (by positivity)
  refine ⟨δ / L, by positivity, fun ζ hζ r hr hrδ => ?_⟩
  obtain ⟨ζ', hζ', hle⟩ := hbox ζ hζ r hr
  have hLr : L * r < δ := by
    rw [lt_div_iff₀ hL0] at hrδ
    linarith
  calc schwarzCarlesonMeasure F (unitDisc ∩ ball ζ r)
      ≤ ENNReal.ofReal L * schwarzCarlesonMeasure f (unitDisc ∩ ball ζ' (L * r)) := hle
    _ ≤ ENNReal.ofReal L * ENNReal.ofReal (ε / L ^ 2 * (L * r)) :=
        mul_le_mul_right (h ζ' hζ' (L * r) (by positivity) hLr) _
    _ = ENNReal.ofReal (ε * r) := by
        rw [← ENNReal.ofReal_mul hL0.le]
        congr 1
        field_simp

/-- §2.9, `sec02-prelim.tex:612`: a bounded quasicircle is a BMO quasicircle iff the measure
`(1-|z|²) f^* dm_Ω = (1-|z|²) s(f z)² λ(f z)² |f'(z)|² dA` belongs to `CM(𝔻)`. -/
theorem subsec_carleson_bmo_iff {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K)
    {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) :
    IsBMOQuasicircle Ω Ωs ↔ IsCarlesonDisk ((volume.restrict unitDisc).withDensity fun z =>
      ENNReal.ofReal ((1 - ‖z‖ ^ 2) * (schwarzNorm Ω (f z) ^ 2 *
        poincareDensity Ω (f z) ^ 2 * ‖deriv f z‖ ^ 2))) := by
  rw [s02_cm_measure_eq hf, (s02_cm_smul (ENNReal.ofReal_pos.2 (by norm_num)).ne'
    ENNReal.ofReal_ne_top).1]
  constructor
  · rintro ⟨-, g, hg, hB⟩
    exact (s02_cm_transfer hg hf).1 ((thm_shen_wei_B (Or.inl hq) hg).1 hB)
  · intro h
    exact ⟨⟨K, hq⟩, f, hf, (thm_shen_wei_B (Or.inl hq) hf).2 h⟩

/-- §2.9, `sec02-prelim.tex:612`: a bounded quasicircle is a VMO quasicircle iff
`(1-|z|²) f^* dm_Ω ∈ CM₀(𝔻)`. -/
theorem subsec_carleson_vmo_iff {Ω Ωs : Set ℂ} {K : ℝ} (hq : IsBoundedKQuasicircle Ω Ωs K)
    {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) :
    IsVMOQuasicircle Ω Ωs ↔ IsVanishingCarlesonDisk ((volume.restrict unitDisc).withDensity
      fun z => ENNReal.ofReal ((1 - ‖z‖ ^ 2) * (schwarzNorm Ω (f z) ^ 2 *
        poincareDensity Ω (f z) ^ 2 * ‖deriv f z‖ ^ 2))) := by
  rw [s02_cm_measure_eq hf, (s02_cm_smul (ENNReal.ofReal_pos.2 (by norm_num)).ne'
    ENNReal.ofReal_ne_top).2]
  constructor
  · rintro ⟨-, g, hg, hV⟩
    exact (s02_cm_transfer hg hf).2 ((thm_shen_wei_V hq hg).1 hV)
  · intro h
    exact ⟨⟨K, hq⟩, f, hf, (thm_shen_wei_V hq hf).2 h⟩

end EpsteinVMO
