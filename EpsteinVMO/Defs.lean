import Mathlib
import LiZhongQC.Ch04.S16_Quasicircles
import LiZhongQC.Ch05.S19_Schwarzian

/-!
# Horoball gaps of quasicircles — core definitions

Source: the paper *Horoball gaps of quasicircles: curvature, volume, and BMO and VMO
characterizations* (`D:\study\study\ocr\专题-horofunction边界与Gromov紧化\正式稿-Epstein-VMO`),
§1–§2.  This file fixes the objects shared by all sections; section files add their own.

## Modelling conventions (read before stating anything)

* **Hyperbolic space.** `ℍ³` is the upper half-space; we work in the ambient type `ℂ × ℝ` and
  restrict to `UHS = {q | 0 < q.2}`.  A point is `q = (W, ξ)`.  `hdist` is (2.1), `hvol` is the
  hyperbolic volume `ξ⁻³ dA dξ` (restricted to `UHS`).
* **Position of the curve (Convention 2.1).** All Möbius-invariant statements (Theorems A, C,
  D, E and everything they rest on) are stated for Jordan curves **through `∞`**, i.e. for a pair
  `(Ω, Ωs)` of complementary domains in `ℂ`.  A Jordan curve through `∞` is given in Schoenflies
  form `IsJordanPair Ω Ωs`: `Ω = F(ℍ)`, `Ωs = F(𝕃)` for a homeomorphism `F` of `ℂ`; the curve is
  `curveOf Ω Ωs = (Ω ∪ Ωs)ᶜ = F(ℝ)`.  A `K`-quasicircle through `∞` is `IsKQuasiPair Ω Ωs K`
  (`F` a `K`-q.c. homeomorphism of `ℂ`, Li Zhong's geometric definition `IsKQC`).  Every
  `K`-quasicircle of `ℂ̂` is Möbius equivalent to one through `∞` (precompose the `K`-q.c. map of
  `ℂ̂` with a Möbius map sending `∞` to a preimage of a point of `Γ`), and every quantity below is
  Möbius natural (paper, §2.1), so this loses no generality.  "`Γ` is a circle" becomes
  `IsLinePair Ω Ωs` (`Ω` is an open half-plane).
* **Bounded curves (Theorem B, §7–§9, §12).** A bounded curve is given by
  `IsBoundedKQuasicircle Ω Ωs K` (`Ω = F(𝔻)` bounded, `Ωs = F(𝔻*)` the unbounded component, as
  subsets of `ℂ`).  Its horoball quantities are *defined by transport* through the inversion
  `invAt x₀ z = (z - x₀)⁻¹` at a point `x₀ ∈ Γ`, which sends the curve to a curve through `∞`
  (the point `∞ ∈ Ωs` becomes `0`); see `invPairΩ`, `invPairΩs`, `invExt`.  By naturality the
  transported quantities do not depend on `x₀`; statements quantify over `x₀`.
* **Integrals (Convention 2.2).** All kernel quantities are lower Lebesgue integrals `∫⁻` with
  values in `ℝ≥0∞`; an inequality `A ≤ C * B` in `ℝ≥0∞` holds automatically when `B = ∞`, as in
  the paper.  For a circle (line) the gap is empty and `s ≡ 0`, so all kernel quantities vanish
  without a special case (the paper's Definition 2.9 sets them to `0`).
* **Poincaré density.** `poincareDensity Ω w = λ(w) = 2 / sup |g'(0)|` over holomorphic
  `g : 𝔻 → Ω` with `g 0 = w`; for a simply connected proper subdomain the sup is attained by the
  Riemann map, giving (2.2) `λ(f z) |f' z| = 2/(1-|z|²)`.  (Junk `0` off `Ω` and for `Ω = ℂ`.)
* **Schwarzian norm.** `schwarzNorm Ω w = s(w) = ¼ |S f(z)| (1-|z|²)²` for any conformal
  `f : 𝔻 → Ω` with `f z = w` (2.5), written as a `sSup` over all such `(f, z)` (all values agree).
  `schwarzian` is Li Zhong's (`LiZhongQC.schwarzian`).
* **BMOA / VMOA.** `g ∈ BMOA(𝔻)` iff `|g'|²(1-|z|²) dA` is a Carleson measure, `g ∈ VMOA` iff it is
  a vanishing Carleson measure (Garnett, *Bounded analytic functions*, Ch. VI, Thm 3.4 and
  Ch. X); we take these as the definitions.  For `g = log f'` we have `g' = f''/f'`, so no branch
  of the logarithm is needed.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace EpsteinVMO

open LiZhongQC

/-! ## Hyperbolic space `ℍ³` -/

/-- The upper half-space `ℍ³ = {(W, ξ) : ξ > 0}` inside `ℂ × ℝ`. -/
def UHS : Set (ℂ × ℝ) := {q | 0 < q.2}

/-- `cosh d(q, q')` for the hyperbolic distance of `ℍ³`, formula (2.1). -/
def coshDist (q q' : ℂ × ℝ) : ℝ :=
  1 + (‖q.1 - q'.1‖ ^ 2 + (q.2 - q'.2) ^ 2) / (2 * q.2 * q'.2)

/-- The hyperbolic distance of `ℍ³` (2.1). -/
def hdist (q q' : ℂ × ℝ) : ℝ := Real.arcosh (coshDist q q')

/-- The base point `j = (0, 1)`. -/
def jPt : ℂ × ℝ := (0, 1)

/-- The closed hyperbolic ball `B(P, r)`. -/
def hball (P : ℂ × ℝ) (r : ℝ) : Set (ℂ × ℝ) := {Q | Q ∈ UHS ∧ hdist P Q ≤ r}

/-- The hyperbolic volume `ξ⁻³ dA(W) dξ` on `ℍ³` (a measure on `ℂ × ℝ` carried by `UHS`). -/
def hvol : Measure (ℂ × ℝ) :=
  (volume.restrict UHS).withDensity fun q => ENNReal.ofReal ((q.2 ^ 3)⁻¹)

/-- The ambient kernel `k_P(Q) = sech²(d(P,Q)/2)`. -/
def ambKernel (P Q : ℂ × ℝ) : ℝ := ((Real.cosh (hdist P Q / 2))⁻¹) ^ 2

/-! ## The Poincaré metric, the hyperbolic distance and the Schwarzian norm of a domain -/

/-- The density `λ_Ω` of the complete conformal metric of curvature `-1` on `Ω`
(`λ_𝔻(z) = 2/(1-|z|²)`): `λ_Ω(w) = 2 / sup |g'(0)|`, the sup over holomorphic `g : 𝔻 → Ω` with
`g 0 = w`. -/
def poincareDensity (Ω : Set ℂ) (w : ℂ) : ℝ :=
  2 / sSup {r : ℝ | ∃ g : ℂ → ℂ, DifferentiableOn ℂ g unitDisc ∧ MapsTo g unitDisc Ω ∧
    g 0 = w ∧ r = ‖deriv g 0‖}

/-- `cosh` of the Poincaré distance of `𝔻`: `1 + 2|a-z|²/((1-|a|²)(1-|z|²))`. -/
def diskCoshDist (a z : ℂ) : ℝ :=
  1 + 2 * ‖a - z‖ ^ 2 / ((1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2))

/-- The Poincaré distance of `𝔻` (curvature `-1`). -/
def diskDist (a z : ℂ) : ℝ := Real.arcosh (diskCoshDist a z)

/-- The hyperbolic distance `d_ρ` of a simply connected domain `Ω`: `d_𝔻(a, z)` for any conformal
`f : 𝔻 → Ω` with `f a = p`, `f z = w` (independent of `f`). -/
def poincareDist (Ω : Set ℂ) (p w : ℂ) : ℝ :=
  sInf {d : ℝ | ∃ (f : ℂ → ℂ) (a z : ℂ), IsConformalOnto f unitDisc Ω ∧ a ∈ unitDisc ∧
    z ∈ unitDisc ∧ f a = p ∧ f z = w ∧ d = diskDist a z}

/-- The intrinsic kernel `k_p(w) = sech²(d_ρ(p,w)/2)` of `Ω`. -/
def intrKernel (Ω : Set ℂ) (p w : ℂ) : ℝ := ((Real.cosh (poincareDist Ω p w / 2))⁻¹) ^ 2

/-- The pointwise hyperbolic norm `s = |S(f⁻¹)|/λ²` of the Schwarzian on `Ω` (2.4), computed by
(2.5): `s(f z) = ¼ |S f(z)| (1-|z|²)²` for a conformal `f : 𝔻 → Ω`. -/
def schwarzNorm (Ω : Set ℂ) (w : ℂ) : ℝ :=
  sSup {r : ℝ | ∃ (f : ℂ → ℂ) (z : ℂ), IsConformalOnto f unitDisc Ω ∧ z ∈ unitDisc ∧
    f z = w ∧ r = ‖schwarzian f z‖ * (1 - ‖z‖ ^ 2) ^ 2 / 4}

/-- The hyperbolic area `dâ = λ² dA` on `Ω`. -/
def hypArea (Ω : Set ℂ) : Measure ℂ :=
  (volume.restrict Ω).withDensity fun w => ENNReal.ofReal (poincareDensity Ω w ^ 2)

/-- The curvature mass `dm_Ω = s² dâ` on `Ω`. -/
def curvMass (Ω : Set ℂ) : Measure ℂ :=
  (volume.restrict Ω).withDensity fun w =>
    ENNReal.ofReal (schwarzNorm Ω w ^ 2 * poincareDensity Ω w ^ 2)

/-- The Wirtinger derivative `∂_w φ = ½(∂_x φ - i ∂_y φ)` of a real function. -/
def wirtingerDz (φ : ℂ → ℝ) (w : ℂ) : ℂ :=
  ((fderiv ℝ φ w 1 : ℂ) - I * (fderiv ℝ φ w I : ℂ)) / 2

/-- `A = ∂_w log λ`. -/
def logDensityDz (Ω : Set ℂ) (w : ℂ) : ℂ :=
  wirtingerDz (fun x => Real.log (poincareDensity Ω x)) w

/-! ## Horoballs, the horoball gap and the Epstein–Poincaré map -/

/-- `Φ_q(w) = λ(w)(|W-w|² + ξ²)/(2ξ)` (2.7). -/
def horoPhi (Ω : Set ℂ) (q : ℂ × ℝ) (w : ℂ) : ℝ :=
  poincareDensity Ω w * (‖q.1 - w‖ ^ 2 + q.2 ^ 2) / (2 * q.2)

/-- The horoball `B_w = {Φ_q(w) ≤ 1}`: the closed Euclidean ball tangent to `ℂ` at `w` of
diameter `2/λ(w)`. -/
def horoball (Ω : Set ℂ) (w : ℂ) : Set (ℂ × ℝ) := {q | q ∈ UHS ∧ horoPhi Ω q w ≤ 1}

/-- `U = ⋃_{w ∈ Ω} B_w`. -/
def horoUnion (Ω : Set ℂ) : Set (ℂ × ℝ) := ⋃ w ∈ Ω, horoball Ω w

/-- The horoball gap `𝒩 = ℍ³ ∖ (U ∪ U*)`. -/
def gap (Ω Ωs : Set ℂ) : Set (ℂ × ℝ) := UHS \ (horoUnion Ω ∪ horoUnion Ωs)

/-- The Epstein–Poincaré map `X = Ep_Ω`, explicit formula (2.9):
`X(w) = (w + 4Ā/(λ² + 4|A|²), 2λ/(λ² + 4|A|²))` with `A = ∂_w log λ`. -/
def epstein (Ω : Set ℂ) (w : ℂ) : ℂ × ℝ :=
  (w + 4 * conj (logDensityDz Ω w) /
      ((poincareDensity Ω w ^ 2 + 4 * ‖logDensityDz Ω w‖ ^ 2 : ℝ) : ℂ),
    2 * poincareDensity Ω w / (poincareDensity Ω w ^ 2 + 4 * ‖logDensityDz Ω w‖ ^ 2))

/-- The normal geodesic `γ_w` (Lemma 2.4), parametrized by arclength `τ ↦ E(w, τ)` with
`E(w, 0) = X(w)` and `τ` increasing away from `w`: the geodesic from `w` to `w + 1/A`, written as
the image under the Poincaré extension of `z ↦ w + 1/z` of the vertical point `(A, h)`,
`h = λ(w) e^{-τ}/2`; thus `log Φ_{E(w,τ)}(w) = τ`. -/
def normalGeod (Ω : Set ℂ) (w : ℂ) (τ : ℝ) : ℂ × ℝ :=
  (w + conj (logDensityDz Ω w) /
      ((‖logDensityDz Ω w‖ ^ 2 + (poincareDensity Ω w * Real.exp (-τ) / 2) ^ 2 : ℝ) : ℂ),
    (poincareDensity Ω w * Real.exp (-τ) / 2) /
      (‖logDensityDz Ω w‖ ^ 2 + (poincareDensity Ω w * Real.exp (-τ) / 2) ^ 2))

/-! ## Labels and the intrinsic kernel quantities (Definition 2.9) -/

/-- A label: a Borel map selecting, for `q ∈ ℍ³ ∖ U`, a base point `w(q) ∈ Ω` of a nearest
horoball, i.e. a minimizer of `Φ_q` on `Ω`. -/
def IsLabel (Ω : Set ℂ) (lab : ℂ × ℝ → ℂ) : Prop :=
  Measurable lab ∧ ∀ q ∈ UHS \ horoUnion Ω,
    lab q ∈ Ω ∧ ∀ w ∈ Ω, horoPhi Ω q (lab q) ≤ horoPhi Ω q w

/-- `K_H(p) = ∫_Ω k_p s² dâ`. -/
def KH (Ω : Set ℂ) (p : ℂ) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal (intrKernel Ω p w) ∂curvMass Ω

/-- `K_*(p) = ∫_{Ω*} k_p(R z*) s*(z*)² dâ*(z*)` with `R = w ∘ X*`. -/
def Kst (Ω Ωs : Set ℂ) (lab : ℂ × ℝ → ℂ) (p : ℂ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (intrKernel Ω p (lab (epstein Ωs z))) ∂curvMass Ωs

/-- `K_{H,2} = K_H + K_*`. -/
def KH2 (Ω Ωs : Set ℂ) (lab : ℂ × ℝ → ℂ) (p : ℂ) : ℝ≥0∞ := KH Ω p + Kst Ω Ωs lab p

/-- `K_V(p) = ∫_𝒩 k_p(w(q)) dvol(q)`. -/
def KV (Ω Ωs : Set ℂ) (lab : ℂ × ℝ → ℂ) (p : ℂ) : ℝ≥0∞ :=
  ∫⁻ q in gap Ω Ωs, ENNReal.ofReal (intrKernel Ω p (lab q)) ∂hvol

/-! ## Ambient quantities (2.13) -/

/-- `V(P) = ∫_𝒩 k_P dvol`. -/
def ambV (Ω Ωs : Set ℂ) (P : ℂ × ℝ) : ℝ≥0∞ :=
  ∫⁻ q in gap Ω Ωs, ENNReal.ofReal (ambKernel P q) ∂hvol

/-- `H(P) = ∫ k_P dμ_H = ∫_Ω k_P(X w) s² dâ + ∫_{Ω*} k_P(X* z*) s*² dâ*`. -/
def ambH (Ω Ωs : Set ℂ) (P : ℂ × ℝ) : ℝ≥0∞ :=
  (∫⁻ w, ENNReal.ofReal (ambKernel P (epstein Ω w)) ∂curvMass Ω) +
    ∫⁻ z, ENNReal.ofReal (ambKernel P (epstein Ωs z)) ∂curvMass Ωs

/-- The kernel-renormalized volume `Ren(P) = V(P) - ½ H(P)` (meaningful when `H(P) < ∞`), with
values in `EReal`. -/
def ren (Ω Ωs : Set ℂ) (P : ℂ × ℝ) : EReal :=
  (ambV Ω Ωs P : EReal) - ((ambH Ω Ωs P / 2 : ℝ≥0∞) : EReal)

/-! ## Jordan curves and quasicircles -/

/-- The curve `Γ = ℂ ∖ (Ω ∪ Ω*)` (its finite part). -/
def curveOf (Ω Ωs : Set ℂ) : Set ℂ := (Ω ∪ Ωs)ᶜ

/-- `(Ω, Ωs)` are the two complementary components of a Jordan curve through `∞`
(Schoenflies form). -/
def IsJordanPair (Ω Ωs : Set ℂ) : Prop :=
  ∃ F : ℂ ≃ₜ ℂ, F '' upperHalf = Ω ∧ F '' lowerHalf = Ωs

/-- `(Ω, Ωs)` are the two complementary components of a `K`-quasicircle through `∞`. -/
def IsKQuasiPair (Ω Ωs : Set ℂ) (K : ℝ) : Prop :=
  ∃ F : ℂ → ℂ, IsKQC F univ K ∧ F '' univ = univ ∧ F '' upperHalf = Ω ∧ F '' lowerHalf = Ωs

/-- The curve through `∞` is a circle, i.e. a straight line: `Ω` is an open half-plane. -/
def IsLinePair (Ω Ωs : Set ℂ) : Prop :=
  ∃ a b : ℂ, a ≠ 0 ∧ Ω = {z | 0 < (a * z + b).im} ∧ Ωs = {z | (a * z + b).im < 0}

/-- A bounded `K`-quasicircle with bounded component `Ω` and unbounded component `Ωs`
(finite points). -/
def IsBoundedKQuasicircle (Ω Ωs : Set ℂ) (K : ℝ) : Prop :=
  ∃ F : ℂ → ℂ, IsKQC F univ K ∧ F '' univ = univ ∧ F '' unitDisc = Ω ∧
    F '' unitDiscExterior = Ωs

/-- The inversion `z ↦ 1/(z - x₀)`. -/
def invAt (x₀ z : ℂ) : ℂ := (z - x₀)⁻¹

/-- The image of the bounded component under `invAt x₀`. -/
def invPairΩ (Ω : Set ℂ) (x₀ : ℂ) : Set ℂ := invAt x₀ '' Ω

/-- The image of the unbounded component (with its point `∞ ↦ 0`) under `invAt x₀`. -/
def invPairΩs (Ωs : Set ℂ) (x₀ : ℂ) : Set ℂ := invAt x₀ '' Ωs ∪ {0}

/-- The Poincaré extension of `z ↦ 1/(z - x₀)` to `ℍ³`:
`(W, ξ) ↦ (conj (W - x₀), ξ)/(|W - x₀|² + ξ²)`. -/
def invExt (x₀ : ℂ) (q : ℂ × ℝ) : ℂ × ℝ :=
  (conj (q.1 - x₀) / ((‖q.1 - x₀‖ ^ 2 + q.2 ^ 2 : ℝ) : ℂ), q.2 / (‖q.1 - x₀‖ ^ 2 + q.2 ^ 2))

/-! ## Carleson measures, BMOA, VMOA -/

/-- `μ ∈ CM(𝔻)`: `μ(𝔻 ∩ D(ζ, r)) ≤ C r` for `ζ ∈ ∂𝔻`, `0 < r < 2`. -/
def IsCarlesonDisk (μ : Measure ℂ) : Prop :=
  ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 2 →
    μ (unitDisc ∩ ball ζ r) ≤ C * ENNReal.ofReal r

/-- `μ ∈ CM₀(𝔻)`: a Carleson measure with `μ(𝔻 ∩ D(ζ, r))/r → 0` uniformly as `r → 0`. -/
def IsVanishingCarlesonDisk (μ : Measure ℂ) : Prop :=
  IsCarlesonDisk μ ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r : ℝ,
    0 < r → r < δ → μ (unitDisc ∩ ball ζ r) ≤ ENNReal.ofReal (ε * r)

/-- The measure `|g'(z)|²(1-|z|²) dA` on `𝔻`, given `g'`. -/
def derivCarlesonMeasure (g' : ℂ → ℂ) : Measure ℂ :=
  (volume.restrict unitDisc).withDensity fun z => ENNReal.ofReal (‖g' z‖ ^ 2 * (1 - ‖z‖ ^ 2))

/-- `log f' ∈ BMOA(𝔻)`, for `f` locally univalent on `𝔻`: `(log f')' = f''/f'`. -/
def LogDerivBMOA (f : ℂ → ℂ) : Prop :=
  IsCarlesonDisk (derivCarlesonMeasure fun z => deriv (deriv f) z / deriv f z)

/-- `log f' ∈ VMOA(𝔻)`. -/
def LogDerivVMOA (f : ℂ → ℂ) : Prop :=
  IsVanishingCarlesonDisk (derivCarlesonMeasure fun z => deriv (deriv f) z / deriv f z)

/-- The Schwarzian Carleson measure `|S f(z)|²(1-|z|²)³ dA` on `𝔻`. -/
def schwarzCarlesonMeasure (f : ℂ → ℂ) : Measure ℂ :=
  (volume.restrict unitDisc).withDensity fun z =>
    ENNReal.ofReal (‖schwarzian f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3)

/-- A BMO quasicircle: a bounded quasicircle with `log f' ∈ BMOA` for a conformal map `f` of `𝔻`
onto the bounded component. -/
def IsBMOQuasicircle (Ω Ωs : Set ℂ) : Prop :=
  (∃ K, IsBoundedKQuasicircle Ω Ωs K) ∧
    ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω ∧ LogDerivBMOA f

/-- A VMO quasicircle. -/
def IsVMOQuasicircle (Ω Ωs : Set ℂ) : Prop :=
  (∃ K, IsBoundedKQuasicircle Ω Ωs K) ∧
    ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω ∧ LogDerivVMOA f

end EpsteinVMO
