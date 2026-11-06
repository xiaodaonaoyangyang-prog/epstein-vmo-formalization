import LiZhongQC.Ch08.S30_ModularGroupDiscontinuity
import EpsteinVMO.Defs
import EpsteinVMO.S02_Prelim
import EpsteinVMO.S07_Transfer
import EpsteinVMO.S03_Coarse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import VanishingCarleson.Basic

/-!
# §11 Quasicircles through `∞`: small-scale vanishing and transfer

Source: `sec11-halfplane.tex`.

## Section-local conventions

* Measures "on `ℍ`" are measures on `ℂ`; every quantity below only sees their restriction to
  `upperHalf` (boxes lie in `ℍ`, kernel integrals are over `upperHalf`).
* An interval `I` is encoded by its center `c` and its length `ℓ > 0`, so `I = [c - ℓ/2, c + ℓ/2]`,
  `β I` has center `c` and length `β ℓ`, and the Carleson box is `Q_I = hpBox c ℓ`.
* `hpWeight m = y m` is the measure `λ` attached to `m`; `hpPushWeight F m = Im w d(F_* m)(w)` is
  `λ_F` (Definition 11.?/`def:hp-admissible`).  The push-forward `hpPush F m` is a `Measure.map` of
  `m.restrict upperHalf`; it is used only for maps `F` continuous on `upperHalf` (admissible maps),
  for which `F` is a.e.-measurable for `m.restrict upperHalf`, so the push-forward is genuine.
* Kernel quantities against a push-forward are written as explicit integrals: `hpPOf A m a` is
  `𝒫_{A_* m}(a) = ∫ k_a(A z) dm(z)`, so no measurability of `A` is needed.
* Strongly quasisymmetric maps are given together with a density `ω` of `h` (`h` is the indefinite
  integral of `ω`); this is local absolute continuity, and `ω = h'` a.e.
* A boundary map is an increasing homeomorphism `h : ℝ ≃ₜ ℝ`; the inverse is `h.symm`.
* The welding setting (Convention `set:hp`) is the predicate `IsHPSetting`.  Conformal maps are
  functions `ℂ → ℂ`; their values on `ℝ` are required to be the continuous boundary extension.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace EpsteinVMO

open LiZhongQC

/-! ## Half-plane hyperbolic geometry -/

/-- The closed upper half-plane `ℍ ∪ ℝ`. -/
def closedUpperHalf : Set ℂ := {z | 0 ≤ z.im}

/-- The closed lower half-plane `𝕃 ∪ ℝ`. -/
def closedLowerHalf : Set ℂ := {z | z.im ≤ 0}

/-! The hyperbolic distance `hpDist` of `ℍ` (`cosh d_ρ(a,z) = 1 + |z-a|²/(2 Im a Im z)`, (11.1)
`eq:hp-distance`) and the kernel `hpKernel a z = sech²(d_ρ(a,z)/2)` are those of
`EpsteinVMO.S07_Transfer` (w3). -/

/-- The hyperbolic area `dA_ρ = dx dy / y²` on `ℍ`. -/
def hpArea : Measure ℂ :=
  (volume.restrict upperHalf).withDensity fun z => ENNReal.ofReal ((z.im ^ 2)⁻¹)

/-- The band measure `1_{a<y<b} dA_ρ`. -/
def hpBandMeasure (a b : ℝ) : Measure ℂ := hpArea.restrict {z | a < z.im ∧ z.im < b}

/-! ## Carleson measures on the half-plane -/

/-- The Carleson box `Q_I = I × (0, |I|]` of the interval `I` with center `c` and length `ℓ`. -/
def hpBox (c ℓ : ℝ) : Set ℂ := {z | |z.re - c| ≤ ℓ / 2 ∧ 0 < z.im ∧ z.im ≤ ℓ}

/-- `‖λ‖_CM = sup_I λ(Q_I)/|I|` (11.?) `eq:hp-CM`. -/
def hpCMNorm (μ : Measure ℂ) : ℝ≥0∞ :=
  ⨆ (c : ℝ) (ℓ : ℝ) (_ : 0 < ℓ), μ (hpBox c ℓ) / ENNReal.ofReal ℓ

/-- `ε_λ(r) = sup_{|I| ≤ r} λ(Q_I)/|I|` `eq:hp-CM`. -/
def hpEps (μ : Measure ℂ) (r : ℝ) : ℝ≥0∞ :=
  ⨆ (c : ℝ) (ℓ : ℝ) (_ : 0 < ℓ) (_ : ℓ ≤ r), μ (hpBox c ℓ) / ENNReal.ofReal ℓ

/-- `λ ∈ CM(ℍ)`. -/
def IsHPCarleson (μ : Measure ℂ) : Prop := hpCMNorm μ ≠ ⊤

/-- `λ ∈ CM₀(ℍ)`: Carleson, and `ε_λ(r) → 0` as `r → 0`. -/
def IsHPVanishingCarleson (μ : Measure ℂ) : Prop :=
  IsHPCarleson μ ∧ Tendsto (hpEps μ) (𝓝[>] 0) (𝓝 0)

/-- `dλ = y dm`. -/
def hpWeight (m : Measure ℂ) : Measure ℂ := m.withDensity fun z => ENNReal.ofReal z.im

/-- Shen's quantity `N_δ(λ) = sup {λ(Q(x,h))/h : 0 < h < δ}` with the open boxes
`Q(x,h) = (x - h/2, x + h/2) × (0, h)` (Remark `rem:hp-boxes`). -/
def hpShenN (μ : Measure ℂ) (δ : ℝ) : ℝ≥0∞ :=
  ⨆ (x : ℝ) (h : ℝ) (_ : 0 < h) (_ : h < δ),
    μ {z : ℂ | |z.re - x| < h / 2 ∧ 0 < z.im ∧ z.im < h} / ENNReal.ofReal h

/-! ## The kernel quantities -/

/-- `𝒫_m(a) = ∫_ℍ k_a dm`. -/
def hpP (m : Measure ℂ) (a : ℂ) : ℝ≥0∞ :=
  ∫⁻ z in upperHalf, ENNReal.ofReal (hpKernel a z) ∂m

/-- `𝒫_{A_* m}(a) = ∫_ℍ k_a(A z) dm(z)`, written without a push-forward. -/
def hpPOf (A : ℂ → ℂ) (m : Measure ℂ) (a : ℂ) : ℝ≥0∞ :=
  ∫⁻ z in upperHalf, ENNReal.ofReal (hpKernel a (A z)) ∂m

/-- `sup_{a ∈ ℍ, Im a ≤ r} P(a)`. -/
def hpSupLow (P : ℂ → ℝ≥0∞) (r : ℝ) : ℝ≥0∞ :=
  ⨆ (a : ℂ) (_ : a ∈ upperHalf) (_ : a.im ≤ r), P a

/-- The push-forward `F_* m` of `m|_ℍ` (used for maps continuous on `ℍ`). -/
def hpPush (F : ℂ → ℂ) (m : Measure ℂ) : Measure ℂ := (m.restrict upperHalf).map F

/-- `dλ_F(w) = Im w d(F_* m)(w)` (`def:hp-admissible`). -/
def hpPushWeight (F : ℂ → ℂ) (m : Measure ℂ) : Measure ℂ := hpWeight (hpPush F m)

/-! ## Schwarzian measures and `VMOA(ℍ)` -/

/-- `dm_f = y² |S f(z)|² dx dy` on `ℍ` (11.?) `eq:hp-mf`. -/
def hpSchwarzMass (f : ℂ → ℂ) : Measure ℂ :=
  (volume.restrict upperHalf).withDensity fun z =>
    ENNReal.ofReal (z.im ^ 2 * ‖schwarzian f z‖ ^ 2)

/-- `dλ_f = y dm_f = y³ |S f|² dx dy` `eq:hp-mf`. -/
def hpSchwarzCarleson (f : ℂ → ℂ) : Measure ℂ := hpWeight (hpSchwarzMass f)

/-- `dm_-(z) = y² |S g(z̄)|² dx dy` on `ℍ`, for `g` conformal on `𝕃` (Convention `set:hp`). -/
def hpSchwarzMassLower (g : ℂ → ℂ) : Measure ℂ :=
  (volume.restrict upperHalf).withDensity fun z =>
    ENNReal.ofReal (z.im ^ 2 * ‖schwarzian g (conj z)‖ ^ 2)

/-- `dλ_- = y dm_-`. -/
def hpSchwarzCarlesonLower (g : ℂ → ℂ) : Measure ℂ := hpWeight (hpSchwarzMassLower g)

/-- The measure `|φ'(z)|² y dx dy` on `ℍ`, given `φ'`. -/
def hpVMOAMeasure (φ' : ℂ → ℂ) : Measure ℂ :=
  (volume.restrict upperHalf).withDensity fun z => ENNReal.ofReal (‖φ' z‖ ^ 2 * z.im)

/-- `log f' ∈ VMOA(ℍ)`: `|(log f')'|² y dx dy ∈ CM₀(ℍ)`, with `(log f')' = f''/f'`. -/
def HPLogDerivVMOA (f : ℂ → ℂ) : Prop :=
  IsHPVanishingCarleson (hpVMOAMeasure fun z => deriv (deriv f) z / deriv f z)

/-! ## Complex dilatation (pointwise, from the real derivative) -/

/-- `φ_z = ½(φ_x - i φ_y)` for a complex-valued `φ`. -/
def cWirtDz (φ : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ φ z 1 - I * fderiv ℝ φ z I) / 2

/-- `φ_z̄ = ½(φ_x + i φ_y)`. -/
def cWirtDzbar (φ : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ φ z 1 + I * fderiv ℝ φ z I) / 2

/-- The complex dilatation `μ_φ = φ_z̄/φ_z`. -/
def cDilatation (φ : ℂ → ℂ) (z : ℂ) : ℂ := cWirtDzbar φ z / cWirtDz φ z

/-! ## Strongly quasisymmetric homeomorphisms of the line -/

/-- An `A_∞` weight on `ℝ`: `∫_E ω ≤ C (|E|/|I|)^δ ∫_I ω` for all intervals `I` and measurable
`E ⊆ I`. -/
def IsAInftyWeight (ω : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ ω x) ∧ LocallyIntegrable ω ∧
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ a b : ℝ, a < b → ∀ E ⊆ Icc a b, MeasurableSet E →
      ∫ x in E, ω x ≤ C * ((volume E).toReal / (b - a)) ^ δ * ∫ x in Icc a b, ω x

/-- `h` is an increasing homeomorphism of `ℝ`, locally absolutely continuous with density `ω`
(`h(x) = h(0) + ∫₀ˣ ω`), and `ω` is an `A_∞` weight. -/
def IsSQSWith (h : ℝ → ℝ) (ω : ℝ → ℝ) : Prop :=
  StrictMono h ∧ Continuous h ∧ Function.Surjective h ∧ IsAInftyWeight ω ∧
    ∀ x, h x = h 0 + ∫ t in (0 : ℝ)..x, ω t

/-- `h ∈ SQS(ℝ)`, strongly quasisymmetric. -/
def IsSQS (h : ℝ → ℝ) : Prop := ∃ ω, IsSQSWith h ω

/-- The mean `u_I` of `u` over `[a, b]`. -/
def intervalMean (u : ℝ → ℝ) (a b : ℝ) : ℝ := (b - a)⁻¹ * ∫ x in a..b, u x

/-- The mean oscillation `|I|⁻¹ ∫_I |u - u_I|` of `u` over `I = [a, b]`. -/
def realMeanOsc (u : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (b - a)⁻¹ * ∫ x in a..b, |u x - intervalMean u a b|

/-- `u ∈ BMO(ℝ)`. -/
def IsBMOReal (u : ℝ → ℝ) : Prop :=
  LocallyIntegrable u ∧ ∃ C : ℝ, ∀ a b : ℝ, a < b → realMeanOsc u a b ≤ C

/-- `u ∈ VMO(ℝ)`: `u ∈ BMO` and the mean oscillation tends to `0` as `|I| → 0`. -/
def IsVMOReal (u : ℝ → ℝ) : Prop :=
  IsBMOReal u ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a < b → b - a < δ → realMeanOsc u a b ≤ ε

/-- `h ∈ SS(ℝ)`, strongly symmetric: `h ∈ SQS(ℝ)` and `log h' ∈ VMO(ℝ)` (with `h' > 0` a.e., so
that `Real.log 0 = 0` hides nothing; this is automatic for an `A_∞` density of a homeomorphism). -/
def IsSS (h : ℝ → ℝ) : Prop :=
  ∃ ω, IsSQSWith h ω ∧ (∀ᵐ t, 0 < ω t) ∧ IsVMOReal fun x => Real.log (ω x)

/-- The center of `h(I)`, `I = [c - ℓ/2, c + ℓ/2]`, for increasing `h`. -/
def imgCenter (h : ℝ → ℝ) (c ℓ : ℝ) : ℝ := (h (c - ℓ / 2) + h (c + ℓ / 2)) / 2

/-- The length `|h(I)|`, `I = [c - ℓ/2, c + ℓ/2]`, for increasing `h`. -/
def imgLength (h : ℝ → ℝ) (c ℓ : ℝ) : ℝ := h (c + ℓ / 2) - h (c - ℓ / 2)

/-- Strong quasisymmetry data `(D_h, p_h, C_h)`: the doubling bound `|h(2I)| ≤ D |h(I)|` and the
reverse Hölder inequality (11.?) `eq:hp-RH` with exponent `p > 1` and constant `C_h`. -/
def IsSQSData (h : ℝ → ℝ) (D p Ch : ℝ) : Prop :=
  ∃ ω, IsSQSWith h ω ∧
    (∀ c ℓ : ℝ, 0 < ℓ → imgLength h c (2 * ℓ) ≤ D * imgLength h c ℓ) ∧ 1 < p ∧
    ∀ a b : ℝ, a < b →
      ((∫⁻ x in Icc a b, ENNReal.ofReal (ω x ^ p)) / ENNReal.ofReal (b - a)) ^ (1 / p) ≤
        ENNReal.ofReal Ch * ((∫⁻ x in Icc a b, ENNReal.ofReal (ω x)) / ENNReal.ofReal (b - a))

/-- The uncentered maximal function `M_u φ(t) = sup_{K ∋ t} |K|⁻¹ ∫_K |φ|`. -/
def maxFnU (φ : ℝ → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (a : ℝ) (b : ℝ) (_ : a ≤ t) (_ : t ≤ b) (_ : a < b),
    (∫⁻ x in Icc a b, ENNReal.ofReal |φ x|) / ENNReal.ofReal (b - a)

/-- `A` is a family of constants for the maximal theorem (11.?) `eq:hp-maximal`:
`‖M_u φ‖_p ≤ A_p ‖φ‖_p` for `1 < p < ∞`. -/
def IsMaximalConst (A : ℝ → ℝ) : Prop :=
  ∀ p : ℝ, 1 < p → ∀ φ : ℝ → ℝ, Measurable φ →
    (∫⁻ t, maxFnU φ t ^ p) ^ (1 / p) ≤ ENNReal.ofReal (A p) * (∫⁻ t, ENNReal.ofReal |φ t| ^ p) ^ (1 / p)

/-- The modulus of continuity `ω_φ(r) = sup {|φ b - φ a| : |b - a| ≤ r}` (meaningful for uniformly
continuous `φ`, the only case in which it is used). -/
def modCont (φ : ℝ → ℝ) (r : ℝ) : ℝ :=
  sSup {d : ℝ | ∃ a b : ℝ, |b - a| ≤ r ∧ d = |φ b - φ a|}

/-! ## Admissible maps -/

/-- `F : ℍ → ℍ` is admissible with constant `L` and boundary map `h` (`def:hp-admissible`): a
quasiconformal homeomorphism of `ℍ` onto itself, `L`-bi-Lipschitz for `d_ρ`, extending to a
homeomorphism of `ℍ ∪ ℝ ∪ {∞}` with `F(∞) = ∞` (a continuous proper bijection of the closed
half-plane), with `F|_ℝ = h ∈ SQS(ℝ)`. -/
def IsHPAdmissible (F : ℂ → ℂ) (h : ℝ ≃ₜ ℝ) (L : ℝ) : Prop :=
  1 ≤ L ∧ IsQuasiconformal F upperHalf ∧ F '' upperHalf = upperHalf ∧
    (∀ z ∈ upperHalf, ∀ z' ∈ upperHalf,
      hpDist (F z) (F z') ≤ L * hpDist z z' ∧ hpDist z z' ≤ L * hpDist (F z) (F z')) ∧
    ContinuousOn F closedUpperHalf ∧ BijOn F closedUpperHalf closedUpperHalf ∧
    Tendsto F (cocompact ℂ ⊓ 𝓟 closedUpperHalf) (cocompact ℂ) ∧
    (∀ x : ℝ, F (x : ℂ) = ((h x : ℝ) : ℂ)) ∧ IsSQS h

/-- The conclusion of Lemma `lem:hp-wm` for the constants `C₁, α` and the bi-Lipschitz
constant `L`: the height comparison (11.?) `eq:hp-wm-height` with `I_z = [x - y, x + y]`, the box
inclusion `F(Q_I) ⊆ Q_{α h(I)}`, and its inverse form (11.?) `eq:hp-wm-box`. -/
def HPWMConstants (L C₁ α : ℝ) : Prop :=
  1 ≤ C₁ ∧ 1 ≤ α ∧ ∀ (F : ℂ → ℂ) (h : ℝ ≃ₜ ℝ), IsHPAdmissible F h L →
    (∀ z ∈ upperHalf,
      C₁⁻¹ * (imgLength h z.re (2 * z.im) / (2 * z.im)) ≤ (F z).im / z.im ∧
        (F z).im / z.im ≤ C₁ * (imgLength h z.re (2 * z.im) / (2 * z.im))) ∧
    (∀ c ℓ : ℝ, 0 < ℓ → F '' hpBox c ℓ ⊆ hpBox (imgCenter h c ℓ) (α * imgLength h c ℓ)) ∧
    (∀ c ℓ : ℝ, 0 < ℓ → ∀ z ∈ upperHalf, F z ∈ hpBox c ℓ →
      z ∈ hpBox (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ))

/-- The transfer constant `C = C₁ A_{p_h} C_h D_h^k`, `k = ⌈log₂(3α)⌉` (`thm:hp-transfer`). -/
def hpTransferConst (C₁ α : ℝ) (A : ℝ → ℝ) (D p Ch : ℝ) : ℝ :=
  C₁ * A p * Ch * D ^ ⌈Real.logb 2 (3 * α)⌉₊

/-! ## The welding setting -/

/-- Convention `set:hp`: `Γ` is a `K`-quasicircle through `∞` that is not a line, with components
`Ω, Ωs`; `f : ℍ → Ω` and `g : 𝕃 → Ωs` are conformal with `f(∞) = ∞ = g(∞)`, continuous up to
`ℝ`; and `w = g⁻¹ ∘ f|_ℝ` is the welding (`f x = g (w x)` on `ℝ`). -/
def IsHPSetting (Ω Ωs : Set ℂ) (K : ℝ) (f g : ℂ → ℂ) (w : ℝ ≃ₜ ℝ) : Prop :=
  IsKQuasiPair Ω Ωs K ∧ ¬ IsLinePair Ω Ωs ∧
    IsConformalOnto f upperHalf Ω ∧ IsConformalOnto g lowerHalf Ωs ∧
    ContinuousOn f closedUpperHalf ∧ ContinuousOn g closedLowerHalf ∧
    Tendsto f (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ) ∧
    Tendsto g (cocompact ℂ ⊓ 𝓟 lowerHalf) (cocompact ℂ) ∧
    ∀ x : ℝ, f (x : ℂ) = g ((w x : ℝ) : ℂ)

/-- `R̃ = f⁻¹ ∘ R ∘ g ∘ J`, `R = lab ∘ X*` (Lemma `lem:hp-label`). -/
def hpLabelMap (Ωs : Set ℂ) (f g : ℂ → ℂ) (lab : ℂ × ℝ → ℂ) (z : ℂ) : ℂ :=
  Function.invFunOn f upperHalf (lab (epstein Ωs (g (conj z))))

/-! ## Basic facts -/

/-- (11.2) `eq:hp-height`, `sec11-halfplane.tex:43`: `|log(Im z / Im a)| ≤ d_ρ(a, z)`. -/
theorem eq_hp_height {a z : ℂ} (ha : a ∈ upperHalf) (hz : z ∈ upperHalf) :
    |Real.log (z.im / a.im)| ≤ hpDist a z := by
  have ht : 0 < a.im := ha
  have hy : 0 < z.im := hz
  have hq : 0 < z.im / a.im := div_pos hy ht
  have hX : 0 ≤ ‖a - z‖ ^ 2 / (2 * a.im * z.im) := by positivity
  rw [← Real.arcosh_cosh (abs_nonneg (Real.log (z.im / a.im))), Real.cosh_abs]
  unfold hpDist
  rw [Real.arcosh_le_arcosh (Real.cosh_pos _) (by linarith)]
  rw [Real.cosh_eq, Real.exp_neg, Real.exp_log hq]
  have hsq : (z.im - a.im) ^ 2 ≤ ‖a - z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    nlinarith [sq_nonneg (a.re - z.re)]
  have e : (z.im / a.im + (z.im / a.im)⁻¹) / 2 = 1 + (z.im - a.im) ^ 2 / (2 * a.im * z.im) := by
    field_simp
    ring
  rw [e]
  gcongr

/-- (11.3) `eq:hp-reflection`, `sec11-halfplane.tex:64`, maximal dilatation part: `J ∘ φ ∘ J`
is `K`-quasiconformal on `J(A)` when `φ` is `K`-quasiconformal on `A`. -/
theorem eq_hp_reflection_qc {φ : ℂ → ℂ} {A : Set ℂ} {K : ℝ} (hφ : IsKQC φ A K) :
    IsKQC (fun z => conj (φ (conj z))) (conj '' A) K := by
  -- `conj` is an involution, so `conj '' A = conj ⁻¹' A` (`abR_x_isKQC_conj`)
  have h : (conj '' A : Set ℂ) = conj ⁻¹' A :=
    congrFun (Set.image_eq_preimage_of_inverse (fun z => Complex.conj_conj z)
      (fun z => Complex.conj_conj z)) A
  rw [h]
  exact abR_x_isKQC_conj hφ

/-- (11.3) `eq:hp-reflection`, `sec11-halfplane.tex:64`: `μ_{J∘φ∘J}(z) = conj (μ_φ(z̄))` at every
point where `φ` is real-differentiable at `z̄`. -/
theorem eq_hp_reflection {φ : ℂ → ℂ} {z : ℂ} (hφ : DifferentiableAt ℝ φ (conj z)) :
    cDilatation (fun w => conj (φ (conj w))) z = conj (cDilatation φ (conj z)) := by
  have hd : HasFDerivAt (fun w => conj (φ (conj w)))
      ((conjCLE : ℂ →L[ℝ] ℂ).comp ((fderiv ℝ φ (conj z)).comp (conjCLE : ℂ →L[ℝ] ℂ))) z := by
    have h1 : HasFDerivAt (fun w : ℂ => conj w) (conjCLE : ℂ →L[ℝ] ℂ) z :=
      (conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt
    have h2 := hφ.hasFDerivAt.comp z h1
    exact (conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z h2
  unfold cDilatation cWirtDzbar cWirtDz
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, conjCLE_apply,
    map_one, Complex.conj_I]
  have hneg : fderiv ℝ φ (conj z) (-I) = -fderiv ℝ φ (conj z) I := map_neg _ _
  rw [hneg]
  simp only [map_div₀, map_add, map_sub, map_mul, map_neg, Complex.conj_I, map_ofNat]
  congr 1 <;> ring

/-- Lemma 11.1 `lem:hp-gluing`, `sec11-halfplane.tex:72`: a homeomorphism of `ℂ` that is
`K`-quasiconformal on `ℍ` and on `𝕃` is `K`-quasiconformal on `ℂ`. -/
theorem lem_hp_gluing (T : ℂ ≃ₜ ℂ) {K : ℝ} (h₁ : IsKQC T upperHalf K)
    (h₂ : IsKQC T lowerHalf K) : IsKQC T univ K := by
  -- `ℝ` is removable (`s13x_removable`): null, met by each vertical line in one point and by
  -- almost every horizontal line in no point
  have hhom : IsHomeomorphOnto T univ (T '' univ) := by
    rw [image_univ, T.range_coe]
    exact nxI1_isHomeomorphOnto_of_homeomorph T
  refine s13x_removable (L := {z : ℂ | z.im = 0}) isOpen_univ h₁.2.1 hhom gzE_volume_im_eq_zero
    (Eventually.of_forall fun x => (Set.countable_singleton (0 : ℝ)).mono fun y hy => by
      simpa using hy) ?_ ?_
  · filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with y hy
    exact Set.countable_empty.mono fun x hx => hy (by simpa using hx)
  · intro z hz
    have him : z.im ≠ 0 := hz.2
    rcases lt_or_gt_of_ne him with h | h
    · exact ⟨lowerHalf, h₂.1, h, subset_univ _, h₂⟩
    · exact ⟨upperHalf, h₁.1, h, subset_univ _, h₁⟩

/-- `sec11-halfplane.tex:129`: `ε_λ` is nondecreasing and bounded by `‖λ‖_CM`. -/
theorem hp_eps_mono_le (μ : Measure ℂ) :
    Monotone (hpEps μ) ∧ ∀ r, hpEps μ r ≤ hpCMNorm μ := by
  refine ⟨fun r s hrs => ?_, fun r => ?_⟩
  · unfold hpEps
    refine iSup₂_le fun c ℓ => iSup₂_le fun hℓ hℓr => ?_
    exact le_iSup₂_of_le c ℓ (le_iSup₂_of_le hℓ (hℓr.trans hrs) le_rfl)
  · unfold hpEps hpCMNorm
    refine iSup₂_le fun c ℓ => iSup₂_le fun hℓ _ => ?_
    exact le_iSup₂_of_le c ℓ (le_iSup_of_le hℓ le_rfl)

/-- Remark `rem:hp-boxes`, `sec11-halfplane.tex:137`: `N_δ(λ) ≤ ε_λ(δ)` and
`ε_λ(r) ≤ 2 N_{3r}(λ)`. -/
theorem rem_hp_boxes (μ : Measure ℂ) :
    (∀ δ : ℝ, 0 < δ → hpShenN μ δ ≤ hpEps μ δ) ∧
      ∀ r : ℝ, 0 < r → hpEps μ r ≤ 2 * hpShenN μ (3 * r) := by
  refine ⟨fun δ _ => ?_, fun r hr => ?_⟩
  · unfold hpShenN
    refine iSup₂_le fun x h => iSup₂_le fun hh hhδ => ?_
    have hsub : {z : ℂ | |z.re - x| < h / 2 ∧ 0 < z.im ∧ z.im < h} ⊆ hpBox x h :=
      fun z hz => ⟨hz.1.le, hz.2.1, hz.2.2.le⟩
    calc μ {z : ℂ | |z.re - x| < h / 2 ∧ 0 < z.im ∧ z.im < h} / ENNReal.ofReal h
        ≤ μ (hpBox x h) / ENNReal.ofReal h := by gcongr
      _ ≤ hpEps μ δ := le_iSup₂_of_le x h (le_iSup₂_of_le hh hhδ.le le_rfl)
  · unfold hpEps
    refine iSup₂_le fun c ℓ => iSup₂_le fun hℓ hℓr => ?_
    have hsub : hpBox c ℓ ⊆ {z : ℂ | |z.re - c| < 2 * ℓ / 2 ∧ 0 < z.im ∧ z.im < 2 * ℓ} :=
      fun z hz => ⟨by linarith [hz.1], hz.2.1, by linarith [hz.2.2]⟩
    calc μ (hpBox c ℓ) / ENNReal.ofReal ℓ
        ≤ μ {z : ℂ | |z.re - c| < 2 * ℓ / 2 ∧ 0 < z.im ∧ z.im < 2 * ℓ} / ENNReal.ofReal ℓ := by
          gcongr
      _ = 2 * (μ {z : ℂ | |z.re - c| < 2 * ℓ / 2 ∧ 0 < z.im ∧ z.im < 2 * ℓ} /
            ENNReal.ofReal (2 * ℓ)) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ← mul_div_assoc,
            ENNReal.mul_div_mul_left _ _ two_ne_zero ENNReal.ofNat_ne_top]
      _ ≤ 2 * hpShenN μ (3 * r) := by
          gcongr
          exact le_iSup₂_of_le c (2 * ℓ) (le_iSup₂_of_le (by positivity) (by linarith) le_rfl)

/-- Helper for `hp_sqs_comp`: the density of an `SQS` map can be taken measurable. -/
theorem s11_comp_meas {h ω : ℝ → ℝ} (hω : IsSQSWith h ω) :
    ∃ ω' : ℝ → ℝ, Measurable ω' ∧ IsSQSWith h ω' := by
  obtain ⟨hmono, hcont, hsurj, ⟨hpos, hli, C, δ, hC, hδ, hA⟩, hF⟩ := hω
  obtain ⟨g, hgm, hg⟩ := hli.aestronglyMeasurable.aemeasurable
  obtain ⟨f, hfm, hf0, hfeq⟩ : ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ ω =ᵐ[volume] f :=
    ⟨fun x => max (g x) 0, hgm.max measurable_const, fun x => le_max_right _ _,
      hg.mono fun x hx => by
        show ω x = max (g x) 0
        rw [← hx, max_eq_left (hpos x)]⟩
  have hsi : ∀ s : Set ℝ, ∫ x in s, ω x = ∫ x in s, f x := fun s =>
    integral_congr_ae (ae_restrict_of_ae hfeq)
  refine ⟨f, hfm, hmono, hcont, hsurj, ⟨hf0, hli.congr hfeq, C, δ, hC, hδ,
    fun a b hab E hE hEm => ?_⟩, fun x => ?_⟩
  · rw [← hsi E, ← hsi (Icc a b)]
    exact hA a b hab E hE hEm
  · rw [hF x, intervalIntegral.integral_congr_ae (hfeq.mono fun t ht _ => ht)]

/-- Helper for `hp_sqs_comp` (H-IMG): an `SQS` map `h` pushes `ω dx` forward to Lebesgue
measure. -/
theorem s11_comp_map {h ω : ℝ → ℝ} (hω : IsSQSWith h ω) (hm : Measurable ω) :
    Measure.map h (volume.withDensity fun x => ENNReal.ofReal (ω x)) = volume := by
  -- `hm` is not needed here (`withDensity_apply` holds for any density); the statement keeps it
  -- because every caller has a measurable density anyway
  have _hm := hm
  obtain ⟨hmono, hcont, hsurj, ⟨hpos, hli, -⟩, hF⟩ := hω
  have hii : ∀ u v : ℝ, IntervalIntegrable ω volume u v := fun u v =>
    (hli.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  refine (Measure.ext_of_Ioc volume _ fun u v huv => ?_).symm
  obtain ⟨a, rfl⟩ := hsurj u
  obtain ⟨b, rfl⟩ := hsurj v
  have hab : a < b := hmono.lt_iff_lt.mp huv
  have hpre : h ⁻¹' Ioc (h a) (h b) = Ioc a b := by
    ext x
    simp only [mem_preimage, mem_Ioc, hmono.lt_iff_lt, hmono.le_iff_le]
  rw [Measure.map_apply hcont.measurable measurableSet_Ioc, hpre,
    withDensity_apply _ measurableSet_Ioc, Real.volume_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal (hii a b).1 (Eventually.of_forall fun x => hpos x),
    ← intervalIntegral.integral_of_le hab.le, hF b, hF a, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _)]

/-- Helper for `hp_sqs_comp`: the change of variables `∫_{h(E)} g = ∫_E (g ∘ h) ω`. -/
theorem s11_comp_lchange {h ω : ℝ → ℝ} (hω : IsSQSWith h ω) (hm : Measurable ω)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) {E : Set ℝ} (hE : MeasurableSet E) :
    ∫⁻ y in h '' E, g y = ∫⁻ x in E, g (h x) * ENNReal.ofReal (ω x) := by
  have hmap := s11_comp_map hω hm
  obtain ⟨hmono, hcont, -, -, -⟩ := hω
  have hemb : MeasurableEmbedding h := hcont.measurableEmbedding hmono.injective
  have hhE : MeasurableSet (h '' E) := hemb.measurableSet_image.mpr hE
  have hind : ∀ x, (h '' E).indicator g (h x) = E.indicator (fun x => g (h x)) x := by
    intro x
    by_cases hx : x ∈ E
    · rw [indicator_of_mem (mem_image_of_mem h hx), indicator_of_mem hx]
    · rw [indicator_of_notMem (fun h' => hx (hmono.injective.mem_set_image.mp h')),
        indicator_of_notMem hx]
  have hmw : Measurable fun x => ENNReal.ofReal (ω x) := ENNReal.measurable_ofReal.comp hm
  calc ∫⁻ y in h '' E, g y = ∫⁻ y, (h '' E).indicator g y
        ∂(Measure.map h (volume.withDensity fun x => ENNReal.ofReal (ω x))) := by
        rw [hmap, lintegral_indicator hhE]
    _ = ∫⁻ x, (h '' E).indicator g (h x) ∂(volume.withDensity fun x => ENNReal.ofReal (ω x)) :=
        lintegral_map (hg.indicator hhE) hcont.measurable
    _ = ∫⁻ x, E.indicator (fun x => g (h x)) x
        ∂(volume.withDensity fun x => ENNReal.ofReal (ω x)) := by simp only [hind]
    _ = ∫⁻ x in E, g (h x) ∂(volume.withDensity fun x => ENNReal.ofReal (ω x)) := by
        rw [lintegral_indicator hE]
    _ = _ := by
        have hgh : Measurable fun x => g (h x) := hg.comp hcont.measurable
        rw [restrict_withDensity hE, lintegral_withDensity_eq_lintegral_mul _ hmw hgh]
        exact lintegral_congr fun x => mul_comm _ _

/-- Helper for `hp_sqs_comp`: `(ω₂ ∘ h₁) ω₁` is an `A_∞` weight
(`ω(E) = ω₂(h₁E) ≤ C₂ (|h₁E|/|h₁I|)^{δ₂} ω₂(h₁I)` and `|h₁E| = ω₁(E) ≤ C₁ (|E|/|I|)^{δ₁} |h₁I|`). -/
theorem s11_comp_ainfty {h₁ ω₁ ω₂ : ℝ → ℝ} (hω₁ : IsSQSWith h₁ ω₁) (hm₁ : Measurable ω₁)
    (hA₂ : IsAInftyWeight ω₂) (hm₂ : Measurable ω₂) :
    IsAInftyWeight fun x => ω₂ (h₁ x) * ω₁ x := by
  have hω₁' := hω₁
  obtain ⟨hmono, hcont, hsurj, ⟨hpos₁, -, C₁, δ₁, hC₁, hδ₁, hA₁⟩, -⟩ := hω₁'
  obtain ⟨hpos₂, hli₂, C₂, δ₂, hC₂, hδ₂, hA₂'⟩ := hA₂
  have hm : Measurable fun x => ω₂ (h₁ x) * ω₁ x := (hm₂.comp hcont.measurable).mul hm₁
  have hpos : ∀ x, 0 ≤ ω₂ (h₁ x) * ω₁ x := fun x => mul_nonneg (hpos₂ _) (hpos₁ x)
  have hL : ∀ E : Set ℝ, MeasurableSet E → ∫⁻ x in E, ENNReal.ofReal (ω₂ (h₁ x) * ω₁ x) =
      ∫⁻ y in h₁ '' E, ENNReal.ofReal (ω₂ y) := by
    intro E hE
    have hm₂' : Measurable fun y => ENNReal.ofReal (ω₂ y) := ENNReal.measurable_ofReal.comp hm₂
    rw [s11_comp_lchange hω₁ hm₁ hm₂' hE]
    exact setLIntegral_congr_fun hE fun x _ => ENNReal.ofReal_mul (hpos₂ _)
  have hB : ∀ E : Set ℝ, MeasurableSet E →
      ∫ x in E, ω₂ (h₁ x) * ω₁ x = ∫ y in h₁ '' E, ω₂ y := by
    intro E hE
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => hpos x)
        hm.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y => hpos₂ y)
        hm₂.aestronglyMeasurable, hL E hE]
  have hBV : ∀ E : Set ℝ, MeasurableSet E → (volume (h₁ '' E)).toReal = ∫ x in E, ω₁ x := by
    intro E hE
    have h1 := s11_comp_lchange hω₁ hm₁ (g := fun _ => (1 : ℝ≥0∞)) measurable_const hE
    simp only [setLIntegral_const, one_mul] at h1
    rw [h1, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => hpos₁ x)
      hm₁.aestronglyMeasurable]
  have himg : ∀ a b : ℝ, h₁ '' Icc a b = Icc (h₁ a) (h₁ b) := by
    intro a b
    ext y
    constructor
    · rintro ⟨x, ⟨hax, hxb⟩, rfl⟩
      exact ⟨hmono.monotone hax, hmono.monotone hxb⟩
    · rintro ⟨hy1, hy2⟩
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨x, ⟨hmono.le_iff_le.mp hy1, hmono.le_iff_le.mp hy2⟩, rfl⟩
  have hli : LocallyIntegrable (fun x => ω₂ (h₁ x) * ω₁ x) := by
    rw [locallyIntegrable_iff]
    intro K hK
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => hpos x), hL K hK.measurableSet]
    exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => hpos₂ y)).mp
      (hli₂.integrableOn_isCompact (hK.image hcont)).hasFiniteIntegral
  refine ⟨hpos, hli, C₂ * C₁ ^ δ₂, δ₁ * δ₂, by positivity, mul_pos hδ₁ hδ₂, ?_⟩
  intro a b hab E hEsub hEm
  show ∫ x in E, ω₂ (h₁ x) * ω₁ x ≤ C₂ * C₁ ^ δ₂ * ((volume E).toReal / (b - a)) ^ (δ₁ * δ₂) *
    ∫ x in Icc a b, ω₂ (h₁ x) * ω₁ x
  have hab' : h₁ a < h₁ b := hmono hab
  have hsub' : h₁ '' E ⊆ Icc (h₁ a) (h₁ b) := by
    rw [← himg a b]
    exact image_mono hEsub
  have hEm' : MeasurableSet (h₁ '' E) :=
    (hcont.measurableEmbedding hmono.injective).measurableSet_image.mpr hEm
  have h2 := hA₂' (h₁ a) (h₁ b) hab' (h₁ '' E) hsub' hEm'
  have h1 := hA₁ a b hab E hEsub hEm
  have hIcc : ∫ x in Icc a b, ω₂ (h₁ x) * ω₁ x = ∫ y in Icc (h₁ a) (h₁ b), ω₂ y := by
    rw [hB _ measurableSet_Icc, himg]
  have hW1 : ∫ x in Icc a b, ω₁ x = h₁ b - h₁ a := by
    rw [← hBV _ measurableSet_Icc, himg, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  rw [← hB E hEm, hBV E hEm, ← hIcc] at h2
  rw [hW1] at h1
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = (volume E).toReal / (b - a) := ⟨_, rfl⟩
  rw [← hxdef] at h1 ⊢
  have hx0 : 0 ≤ x := by rw [hxdef]; exact div_nonneg ENNReal.toReal_nonneg (by linarith)
  have hy0 : 0 ≤ (∫ x in E, ω₁ x) / (h₁ b - h₁ a) :=
    div_nonneg (setIntegral_nonneg hEm fun x _ => hpos₁ x) (by linarith)
  have hy : (∫ x in E, ω₁ x) / (h₁ b - h₁ a) ≤ C₁ * x ^ δ₁ := by
    rw [div_le_iff₀ (by linarith)]
    exact h1
  have hyδ : ((∫ x in E, ω₁ x) / (h₁ b - h₁ a)) ^ δ₂ ≤ C₁ ^ δ₂ * x ^ (δ₁ * δ₂) := by
    calc _ ≤ (C₁ * x ^ δ₁) ^ δ₂ := Real.rpow_le_rpow hy0 hy hδ₂.le
      _ = _ := by rw [Real.mul_rpow hC₁.le (Real.rpow_nonneg hx0 _), ← Real.rpow_mul hx0]
  have hW0 : 0 ≤ ∫ x in Icc a b, ω₂ (h₁ x) * ω₁ x :=
    setIntegral_nonneg measurableSet_Icc fun x _ => hpos x
  calc _ ≤ _ := h2
    _ ≤ C₂ * (C₁ ^ δ₂ * x ^ (δ₁ * δ₂)) * ∫ x in Icc a b, ω₂ (h₁ x) * ω₁ x := by gcongr
    _ = _ := by ring

/-- Helper for `hp_sqs_comp`: `h₂ ∘ h₁` is the integral of `(ω₂ ∘ h₁) ω₁`. -/
theorem s11_comp_formula {h₁ h₂ ω₁ ω₂ : ℝ → ℝ} (hω₁ : IsSQSWith h₁ ω₁) (hω₂ : IsSQSWith h₂ ω₂)
    (hm₁ : Measurable ω₁) (hm₂ : Measurable ω₂) :
    ∀ x, h₂ (h₁ x) = h₂ (h₁ 0) + ∫ t in (0 : ℝ)..x, ω₂ (h₁ t) * ω₁ t := by
  have hmono := hω₁.1
  have hcont := hω₁.2.1
  have hsurj := hω₁.2.2.1
  have hpos₁ := hω₁.2.2.2.1.1
  have hpos₂ := hω₂.2.2.2.1.1
  have hli₂ := hω₂.2.2.2.1.2.1
  have hF₂ := hω₂.2.2.2.2
  have hm : Measurable fun x => ω₂ (h₁ x) * ω₁ x := (hm₂.comp hcont.measurable).mul hm₁
  have hpos : ∀ x, 0 ≤ ω₂ (h₁ x) * ω₁ x := fun x => mul_nonneg (hpos₂ _) (hpos₁ x)
  have hB : ∀ E : Set ℝ, MeasurableSet E →
      ∫ x in E, ω₂ (h₁ x) * ω₁ x = ∫ y in h₁ '' E, ω₂ y := by
    intro E hE
    have hm₂' : Measurable fun y => ENNReal.ofReal (ω₂ y) := ENNReal.measurable_ofReal.comp hm₂
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => hpos x)
        hm.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y => hpos₂ y)
        hm₂.aestronglyMeasurable, s11_comp_lchange hω₁ hm₁ hm₂' hE]
    congr 1
    exact setLIntegral_congr_fun hE fun x _ => ENNReal.ofReal_mul (hpos₂ _)
  have himg : ∀ u v : ℝ, h₁ '' Ioc u v = Ioc (h₁ u) (h₁ v) := by
    intro u v
    ext y
    constructor
    · rintro ⟨x, ⟨hux, hxv⟩, rfl⟩
      exact ⟨hmono hux, hmono.monotone hxv⟩
    · rintro ⟨hy1, hy2⟩
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨x, ⟨hmono.lt_iff_lt.mp hy1, hmono.le_iff_le.mp hy2⟩, rfl⟩
  have hii₂ : ∀ u v : ℝ, IntervalIntegrable ω₂ volume u v := fun u v =>
    (hli₂.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hle : ∀ u v : ℝ, u ≤ v →
      ∫ t in u..v, ω₂ (h₁ t) * ω₁ t = ∫ y in h₁ u..h₁ v, ω₂ y := by
    intro u v huv
    rw [intervalIntegral.integral_of_le huv, intervalIntegral.integral_of_le (hmono.monotone huv),
      hB _ measurableSet_Ioc, himg]
  have hall : ∀ x : ℝ, ∫ t in (0 : ℝ)..x, ω₂ (h₁ t) * ω₁ t = ∫ y in h₁ 0..h₁ x, ω₂ y := by
    intro x
    rcases le_total 0 x with hx | hx
    · exact hle 0 x hx
    · rw [intervalIntegral.integral_symm, hle x 0 hx, ← intervalIntegral.integral_symm]
  intro x
  rw [hall x, hF₂ (h₁ x), hF₂ (h₁ 0),
    ← intervalIntegral.integral_interval_sub_left (hii₂ 0 (h₁ x)) (hii₂ 0 (h₁ 0))]
  ring

/-- `sec11-halfplane.tex:165` (cited from [WMUC, §2.4]): `SQS(ℝ)` is closed under composition. -/
theorem hp_sqs_comp {h₁ h₂ : ℝ ≃ₜ ℝ} (h₁s : IsSQS h₁) (h₂s : IsSQS h₂) :
    IsSQS (h₁.trans h₂) := by
  obtain ⟨ω₁, hω₁⟩ := h₁s
  obtain ⟨ω₂, hω₂⟩ := h₂s
  obtain ⟨v₁, hv₁m, hv₁⟩ := s11_comp_meas hω₁
  obtain ⟨v₂, hv₂m, hv₂⟩ := s11_comp_meas hω₂
  exact ⟨fun x => v₂ (h₁ x) * v₁ x, hv₂.1.comp hv₁.1, (h₁.trans h₂).continuous,
    (h₁.trans h₂).surjective, s11_comp_ainfty hv₁ hv₁m hv₂.2.2.2.1 hv₂m,
    s11_comp_formula (h₁ := h₁) (h₂ := h₂) hv₁ hv₂ hv₁m hv₂m⟩

/-- Helper: an `A_∞` density of an increasing homeomorphism is positive a.e. (at a density
point of `{ω = 0}` the `A_∞` bound would force `∫_I ω = 0`, contradicting strict monotonicity). -/
theorem hp_sqs_pos_ae {h ω : ℝ → ℝ} (hω : IsSQSWith h ω) : ∀ᵐ t, 0 < ω t := by
  obtain ⟨hmono, -, -, ⟨hω0, hωloc, C, δ, hC, hδ, hA⟩, hrep⟩ := hω
  have hωm := hωloc.aestronglyMeasurable
  set ω' := hωm.mk ω with hω'def
  have hω'm : Measurable ω' := hωm.stronglyMeasurable_mk.measurable
  have hωe : ω =ᵐ[volume] ω' := hωm.ae_eq_mk
  set Z := {t | ω' t ≤ 0} with hZdef
  have hZm : MeasurableSet Z := measurableSet_le hω'm measurable_const
  suffices hZ : volume Z = 0 by
    filter_upwards [compl_mem_ae_iff.mpr hZ, hωe] with t ht he
    rw [he]
    exact not_le.mp ht
  by_contra hZ
  set η : ℝ := ((2 * C)⁻¹) ^ δ⁻¹ with hηdef
  have hη0 : 0 < η := by positivity
  have hηδ : η ^ δ = (2 * C)⁻¹ := Real.rpow_inv_rpow (by positivity) hδ.ne'
  haveI : (ae (volume.restrict Z)).NeBot := ae_neBot.mpr (mt Measure.restrict_eq_zero.mp hZ)
  obtain ⟨x, hx⟩ := (Besicovitch.ae_tendsto_measure_inter_div (volume : Measure ℝ) Z).exists
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), ENNReal.ofReal (1 - η) <
      volume (Z ∩ closedBall x r) / volume (closedBall x r) :=
    hx.eventually (lt_mem_nhds (ENNReal.ofReal_lt_one.mpr (by linarith)))
  obtain ⟨r, hr, hr0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hr0' : 0 < r := hr0
  rw [Real.closedBall_eq_Icc, Real.volume_Icc, inter_comm,
    show x + r - (x - r) = 2 * r by ring] at hr
  set B := Icc (x - r) (x + r) with hBdef
  have hBi : IntegrableOn ω B := hωloc.integrableOn_isCompact isCompact_Icc
  have hfin : volume (B ∩ Z) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hBdef, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (measure_mono inter_subset_left)
  have hfinE : volume (B \ Z) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hBdef, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (measure_mono sdiff_subset)
  -- the mass of `ω` sits on `B \ Z`
  have hZ0 : ∫ t in B ∩ Z, ω t = 0 := by
    apply integral_eq_zero_of_ae
    rw [EventuallyEq, ae_restrict_iff' (measurableSet_Icc.inter hZm)]
    filter_upwards [hωe] with t he ht
    exact le_antisymm (he ▸ ht.2) (hω0 t)
  have hmass : ∫ t in B \ Z, ω t = ∫ t in B, ω t := by
    rw [← integral_inter_add_sdiff hZm hBi, hZ0, zero_add]
  -- `|B \ Z| ≤ η |B|`
  have hsplit : (volume (B ∩ Z)).toReal + (volume (B \ Z)).toReal = 2 * r := by
    rw [← ENNReal.toReal_add hfin hfinE, measure_inter_add_sdiff B hZm, hBdef, Real.volume_Icc,
      show x + r - (x - r) = 2 * r by ring, ENNReal.toReal_ofReal (by linarith)]
  have hE : (volume (B \ Z)).toReal ≤ η * (2 * r) := by
    by_cases hη1 : 1 ≤ η
    · nlinarith [ENNReal.toReal_nonneg (a := volume (B ∩ Z))]
    · push_neg at hη1
      rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by simp; linarith)) (Or.inl ENNReal.ofReal_ne_top),
        ← ENNReal.ofReal_mul (by linarith),
        ENNReal.ofReal_lt_iff_lt_toReal (by nlinarith) hfin] at hr
      nlinarith
  have hint0 : 0 ≤ ∫ t in B, ω t := setIntegral_nonneg measurableSet_Icc fun t _ => hω0 t
  have hAi := hA (x - r) (x + r) (by linarith) (B \ Z) sdiff_subset (measurableSet_Icc.diff hZm)
  rw [hmass, show x + r - (x - r) = 2 * r by ring] at hAi
  have hq : ((volume (B \ Z)).toReal / (2 * r)) ^ δ ≤ (2 * C)⁻¹ := by
    rw [← hηδ]
    exact Real.rpow_le_rpow (by positivity) ((div_le_iff₀ (by linarith)).mpr hE) hδ.le
  have hB0 : ∫ t in B, ω t = 0 := by
    have : C * ((volume (B \ Z)).toReal / (2 * r)) ^ δ ≤ 1 / 2 := by
      calc C * ((volume (B \ Z)).toReal / (2 * r)) ^ δ ≤ C * (2 * C)⁻¹ :=
            mul_le_mul_of_nonneg_left hq hC.le
        _ = 1 / 2 := by field_simp
    nlinarith
  -- but `h` is strictly increasing
  have hlt := hmono (show x - r < x + r by linarith)
  have hii : ∀ u v : ℝ, IntervalIntegrable ω volume u v := fun u v =>
    (hωloc.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hdiff : h (x + r) - h (x - r) = ∫ t in (x - r)..(x + r), ω t := by
    rw [hrep (x + r), hrep (x - r), add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (hii 0 (x + r)) (hii 0 (x - r))]
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc, ← hBdef,
    hB0] at hdiff
  linarith

/-- Helper for `hp_sqs_symm`: the change of variables for the inverse map,
`∫_F (ω ∘ h⁻¹)⁻¹ = |h⁻¹(F)|` (`s11_comp_lchange` on `h⁻¹(F)`, with `ω > 0` a.e.). -/
theorem s11_symm_change {h : ℝ ≃ₜ ℝ} {ω : ℝ → ℝ} (hω : IsSQSWith h ω) (hm : Measurable ω)
    (hpos : ∀ᵐ x, 0 < ω x) {F : Set ℝ} (hF : MeasurableSet F) :
    ∫⁻ y in F, ENNReal.ofReal ((ω (h.symm y))⁻¹) = volume (h.symm '' F) := by
  have hE : MeasurableSet (h.symm '' F) := h.symm.measurableEmbedding.measurableSet_image.mpr hF
  have hg : Measurable fun y => ENNReal.ofReal ((ω (h.symm y))⁻¹) :=
    ENNReal.measurable_ofReal.comp (hm.comp h.symm.continuous.measurable).inv
  have himg : ⇑h '' (⇑h.symm '' F) = F := by
    rw [image_image]
    simp
  have key := s11_comp_lchange hω hm hg hE
  rw [himg] at key
  rw [key, ← setLIntegral_one (μ := volume) (h.symm '' F)]
  refine lintegral_congr_ae ((ae_restrict_of_ae hpos).mono fun x hx => ?_)
  simp only [Homeomorph.symm_apply_apply]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hx.le), inv_mul_cancel₀ hx.ne', ENNReal.ofReal_one]

/-- Helper for `hp_sqs_symm`: the dual threshold property `|F| ≤ ½|J| ⇒ |h⁻¹F| ≤ θ |h⁻¹J|`
(`A_∞` of `ω` applied to the complement `h⁻¹J ∖ h⁻¹F`). -/
theorem s11_symm_dual {h : ℝ ≃ₜ ℝ} {ω : ℝ → ℝ} (hω : IsSQSWith h ω) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ a b : ℝ, a < b → ∀ F ⊆ Icc a b, MeasurableSet F →
      volume F ≤ ENNReal.ofReal (1 / 2 * (b - a)) →
        volume (h.symm '' F) ≤ ENNReal.ofReal θ * volume (h.symm '' Icc a b) := by
  obtain ⟨ω', hm, hω'⟩ := s11_comp_meas hω
  have hω'' := hω'
  obtain ⟨hmono, -, -, ⟨hpos, -, C, δ, hC, hδ, hA⟩, -⟩ := hω''
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = min (1 / 2) ((1 / (4 * C)) ^ δ⁻¹) := ⟨_, rfl⟩
  have hα0 : 0 < α := by
    rw [hα]
    exact lt_min (by norm_num) (Real.rpow_pos_of_pos (by positivity) _)
  have hα1 : α ≤ 1 / 2 := by
    rw [hα]
    exact min_le_left _ _
  have hαδ : C * α ^ δ ≤ 1 / 4 := by
    have h1 : α ^ δ ≤ ((1 / (4 * C)) ^ δ⁻¹) ^ δ :=
      Real.rpow_le_rpow hα0.le (by rw [hα]; exact min_le_right _ _) hδ.le
    rw [← Real.rpow_mul (by positivity), inv_mul_cancel₀ hδ.ne', Real.rpow_one] at h1
    calc C * α ^ δ ≤ C * (1 / (4 * C)) := mul_le_mul_of_nonneg_left h1 hC.le
      _ = 1 / 4 := by field_simp
  refine ⟨1 - α, by linarith, by linarith, ?_⟩
  intro a b hab F hFJ hF hFs
  have hsm : StrictMono h.symm := fun x y hxy => hmono.lt_iff_lt.mp (by simpa using hxy)
  have himgI : ⇑h.symm '' Icc a b = Icc (h.symm a) (h.symm b) := by
    ext y
    constructor
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
      exact ⟨hsm.monotone h1, hsm.monotone h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h y, ⟨?_, ?_⟩, h.symm_apply_apply y⟩
      · have h3 := hmono.monotone h1
        simpa using h3
      · have h3 := hmono.monotone h2
        simpa using h3
  have hhh : ∀ X : Set ℝ, ⇑h '' (⇑h.symm '' X) = X := fun X => by
    rw [image_image]
    simp
  have hBV : ∀ X : Set ℝ, MeasurableSet X → volume.real (⇑h '' X) = ∫ x in X, ω' x := by
    intro X hX
    have h1 := s11_comp_lchange hω' hm (g := fun _ => (1 : ℝ≥0∞)) measurable_const hX
    simp only [setLIntegral_const, one_mul] at h1
    rw [measureReal_def, h1, integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun x => hpos x) hm.aestronglyMeasurable]
  have hl0 : 0 < h.symm b - h.symm a := sub_pos.mpr (hsm hab)
  have hEm : MeasurableSet (⇑h.symm '' F) := h.symm.measurableEmbedding.measurableSet_image.mpr hF
  have hEsub : ⇑h.symm '' F ⊆ Icc (h.symm a) (h.symm b) := himgI ▸ image_mono hFJ
  obtain ⟨Ec, hEc⟩ : ∃ Ec, Ec = Icc (h.symm a) (h.symm b) \ ⇑h.symm '' F := ⟨_, rfl⟩
  have hEcm : MeasurableSet Ec := hEc ▸ measurableSet_Icc.diff hEm
  have hEcsub : Ec ⊆ Icc (h.symm a) (h.symm b) := hEc ▸ fun y hy => hy.1
  have hvI : volume.real (Icc (h.symm a) (h.symm b)) = h.symm b - h.symm a := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal hl0.le]
  have hsplit : volume.real (⇑h.symm '' F) + volume.real Ec = h.symm b - h.symm a := by
    rw [hEc, measureReal_sdiff hEsub hEm measure_Icc_lt_top.ne, hvI]
    ring
  have hhEc : ⇑h '' Ec = Icc a b \ F := by
    rw [hEc, image_sdiff h.injective, ← himgI, hhh, hhh]
  have hωEc : volume.real (Icc a b \ F) = ∫ x in Ec, ω' x := by
    rw [← hhEc]
    exact hBV Ec hEcm
  have hωI : ∫ x in Icc (h.symm a) (h.symm b), ω' x = b - a := by
    rw [← hBV _ measurableSet_Icc, ← himgI, hhh, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)]
  have hFr : volume.real F ≤ 1 / 2 * (b - a) := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by linarith) hFs
  have hdiff : volume.real (Icc a b \ F) = (b - a) - volume.real F := by
    rw [measureReal_sdiff hFJ hF measure_Icc_lt_top.ne, measureReal_def volume (Icc a b),
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  have hFfin : volume (⇑h.symm '' F) ≠ ∞ :=
    ((measure_mono hEsub).trans_lt measure_Icc_lt_top).ne
  rw [himgI, Real.volume_Icc, ← ENNReal.ofReal_mul (by linarith),
    ENNReal.le_ofReal_iff_toReal_le hFfin (mul_nonneg (by linarith) hl0.le), ← measureReal_def]
  by_contra hcon
  rw [not_le] at hcon
  have hEcs : volume.real Ec / (h.symm b - h.symm a) ≤ α := by
    rw [div_le_iff₀ hl0]
    nlinarith
  have hAc := hA (h.symm a) (h.symm b) (hsm hab) Ec hEcsub hEcm
  rw [← measureReal_def, hωI, ← hωEc, hdiff] at hAc
  have hr : (volume.real Ec / (h.symm b - h.symm a)) ^ δ ≤ α ^ δ :=
    Real.rpow_le_rpow (div_nonneg measureReal_nonneg hl0.le) hEcs hδ.le
  have hfin : C * (volume.real Ec / (h.symm b - h.symm a)) ^ δ * (b - a) ≤ 1 / 4 * (b - a) := by
    have h4 := mul_le_mul_of_nonneg_left hr hC.le
    have h5 := mul_le_mul_of_nonneg_right (h4.trans hαδ) (by linarith : (0 : ℝ) ≤ b - a)
    linarith
  linarith

/-- Helper for `hp_sqs_symm`: `h⁻¹(y) = h⁻¹(0) + ∫₀ʸ (ω ∘ h⁻¹)⁻¹`. -/
theorem s11_symm_formula {h : ℝ ≃ₜ ℝ} {ω : ℝ → ℝ} (hω : IsSQSWith h ω) (hm : Measurable ω)
    (hpos : ∀ᵐ x, 0 < ω x) :
    ∀ y, h.symm y = h.symm 0 + ∫ t in (0 : ℝ)..y, (ω (h.symm t))⁻¹ := by
  have hmono := hω.1
  have hσm : Measurable fun y => (ω (h.symm y))⁻¹ := (hm.comp h.symm.continuous.measurable).inv
  have hσ0 : ∀ y, 0 ≤ (ω (h.symm y))⁻¹ := fun y => inv_nonneg.mpr (hω.2.2.2.1.1 _)
  have hsm : StrictMono h.symm := fun x y hxy => hmono.lt_iff_lt.mp (by simpa using hxy)
  have himg : ∀ u v : ℝ, ⇑h.symm '' Ioc u v = Ioc (h.symm u) (h.symm v) := by
    intro u v
    ext y
    constructor
    · rintro ⟨x, ⟨hux, hxv⟩, rfl⟩
      exact ⟨hsm hux, hsm.monotone hxv⟩
    · rintro ⟨hy1, hy2⟩
      refine ⟨h y, ⟨?_, ?_⟩, h.symm_apply_apply y⟩
      · have h3 := hmono hy1
        simpa using h3
      · have h3 := hmono.monotone hy2
        simpa using h3
  have hle : ∀ u v : ℝ, u ≤ v → ∫ t in u..v, (ω (h.symm t))⁻¹ = h.symm v - h.symm u := by
    intro u v huv
    rw [intervalIntegral.integral_of_le huv, integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall hσ0) hσm.aestronglyMeasurable,
      s11_symm_change hω hm hpos measurableSet_Ioc, himg, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (hsm.monotone huv))]
  intro y
  rcases le_total 0 y with hy | hy
  · rw [hle 0 y hy]
    ring
  · rw [intervalIntegral.integral_symm, hle y 0 hy]
    ring

/-- Helper for `hp_sqs_symm`: `(ω ∘ h⁻¹)⁻¹` is an `A_∞` weight (`s07_cz_power` for the measure
`F ↦ |h⁻¹F|`, whose fixed-threshold condition is `s11_symm_dual`). -/
theorem s11_symm_ainfty {h : ℝ ≃ₜ ℝ} {ω : ℝ → ℝ} (hω : IsSQSWith h ω) (hm : Measurable ω)
    (hpos : ∀ᵐ x, 0 < ω x) : IsAInftyWeight fun y => (ω (h.symm y))⁻¹ := by
  have hσm : Measurable fun y => (ω (h.symm y))⁻¹ := (hm.comp h.symm.continuous.measurable).inv
  have hσ0 : ∀ y, 0 ≤ (ω (h.symm y))⁻¹ := fun y => inv_nonneg.mpr (hω.2.2.2.1.1 _)
  have hB : ∀ X : Set ℝ, MeasurableSet X →
      ∫ y in X, (ω (h.symm y))⁻¹ = (volume (⇑h.symm '' X)).toReal := by
    intro X hX
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hσ0) hσm.aestronglyMeasurable,
      s11_symm_change hω hm hpos hX]
  have hfinK : ∀ K : Set ℝ, IsCompact K → volume (⇑h.symm '' K) < ∞ := fun K hK =>
    (hK.image h.symm.continuous).measure_lt_top
  have hli : LocallyIntegrable fun y => (ω (h.symm y))⁻¹ := by
    rw [locallyIntegrable_iff]
    intro K hK
    refine ⟨hσm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hσ0),
      s11_symm_change hω hm hpos hK.measurableSet]
    exact hfinK K hK
  obtain ⟨θ, hθ0, hθ1, hdual⟩ := s11_symm_dual hω
  obtain ⟨C, δ, hC, hδ, hcz⟩ := s07_cz_power (β := 1 / 2) (by norm_num) (by norm_num) hθ0 hθ1
  refine ⟨hσ0, hli, C, δ, hC, hδ, ?_⟩
  intro a b hab E hEsub hEm
  have hμ : ∀ X : Set ℝ, MeasurableSet X →
      (volume.withDensity fun y => ENNReal.ofReal ((ω (h.symm y))⁻¹)) X =
        volume (⇑h.symm '' X) := fun X hX => by
    rw [withDensity_apply _ hX, s11_symm_change hω hm hpos hX]
  have key := hcz (volume.withDensity fun y => ENNReal.ofReal ((ω (h.symm y))⁻¹))
    (withDensity_absolutelyContinuous _ _) (b - a)
    (fun a' b' hab' _ F hF hFm hFs => by
      rw [hμ F hFm, hμ _ measurableSet_Icc]
      exact hdual a' b' hab' F hF hFm hFs) a b hab le_rfl E hEsub hEm
  rw [hμ E hEm, hμ _ measurableSet_Icc] at key
  show ∫ y in E, (ω (h.symm y))⁻¹ ≤
    C * ((volume E).toReal / (b - a)) ^ δ * ∫ y in Icc a b, (ω (h.symm y))⁻¹
  rw [hB E hEm, hB _ measurableSet_Icc]
  have hIfin : volume (⇑h.symm '' Icc a b) ≠ ∞ := (hfinK _ isCompact_Icc).ne
  have hc0 : 0 ≤ C * ((volume E).toReal / (b - a)) ^ δ :=
    mul_nonneg hC.le (Real.rpow_nonneg (div_nonneg ENNReal.toReal_nonneg (by linarith)) _)
  calc (volume (⇑h.symm '' E)).toReal
      ≤ (ENNReal.ofReal (C * ((volume E).toReal / (b - a)) ^ δ) *
          volume (⇑h.symm '' Icc a b)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIfin) key
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0]

/-- `sec11-halfplane.tex:165` (cited from [WMUC, §2.4]): `SQS(ℝ)` is closed under inversion. -/
theorem hp_sqs_symm {h : ℝ ≃ₜ ℝ} (hs : IsSQS h) : IsSQS h.symm := by
  obtain ⟨ω₀, hω₀⟩ := hs
  obtain ⟨ω, hm, hω⟩ := s11_comp_meas hω₀
  have hpos := hp_sqs_pos_ae hω
  exact ⟨fun y => (ω (h.symm y))⁻¹,
    fun x y hxy => hω.1.lt_iff_lt.mp (by rw [h.apply_symm_apply, h.apply_symm_apply]; exact hxy),
    h.symm.continuous, h.symm.surjective, s11_symm_ainfty hω hm hpos, s11_symm_formula hω hm hpos⟩

/-- Helper: `IsAInftyWeight` plus a.e. positivity gives `VanishingCarleson.AInfinityWeight`
(constants `max C 1`, `min δ 1`). -/
theorem hp_ainfty_vc {ω : ℝ → ℝ} (hA : IsAInftyWeight ω) (hpos : ∀ᵐ t, 0 < ω t) :
    VanishingCarleson.AInfinityWeight ω := by
  obtain ⟨hω0, -, C, δ, hC, hδ, hA⟩ := hA
  refine ⟨max C 1, min δ 1, le_max_right _ _, lt_min hδ one_pos, min_le_right _ _, hpos, ?_⟩
  intro a b hab E hE hEsub
  have hI := hA a b hab E hEsub hE
  have hba : 0 < b - a := by linarith
  have hr0 : 0 ≤ (volume E).toReal / (b - a) := div_nonneg ENNReal.toReal_nonneg hba.le
  have hr1 : (volume E).toReal / (b - a) ≤ 1 := by
    rw [div_le_one hba]
    have h1 : (volume E).toReal ≤ (volume (Icc a b)).toReal :=
      ENNReal.toReal_mono (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (measure_mono hEsub)
    rwa [Real.volume_Icc, ENNReal.toReal_ofReal hba.le] at h1
  have hrp : ((volume E).toReal / (b - a)) ^ δ ≤ ((volume E).toReal / (b - a)) ^ min δ 1 :=
    Real.rpow_le_rpow_of_exponent_ge' hr0 hr1 (le_min hδ.le zero_le_one) (min_le_left _ _)
  have hS : 0 ≤ ∫ x in Icc a b, ω x := setIntegral_nonneg measurableSet_Icc fun t _ => hω0 t
  rcases hS.eq_or_lt with hS0 | hS0
  · rw [← hS0, div_zero]
    positivity
  rw [div_le_iff₀ hS0]
  calc ∫ x in E, ω x ≤ C * ((volume E).toReal / (b - a)) ^ δ * ∫ x in Icc a b, ω x := hI
    _ ≤ max C 1 * ((volume E).toReal / (b - a)) ^ min δ 1 * ∫ x in Icc a b, ω x := by
      gcongr
      · exact le_max_left _ _

/-- Helper: copy of the private `VanishingCarleson.ps_log_intervalIntegrable_of_A1Pos`
(`VanishingCarleson/ProofSteps.lean:107`): an everywhere-positive `(A1)` weight has a logarithm
integrable on every interval. -/
theorem hp_log_intervalIntegrable_of_A1Pos {v : ℝ → ℝ} {C₁ σ : ℝ} (hC₁ : 1 ≤ C₁)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hA1 : VanishingCarleson.WeightA1Pos v C₁ σ) {a b : ℝ}
    (hab : a < b) (hint : IntervalIntegrable v volume a b) :
    IntervalIntegrable (fun t => Real.log (v t)) volume a b := by
  by_contra hnot
  have hmpos : 0 < VanishingCarleson.weightMean v a b := by
    unfold VanishingCarleson.weightMean VanishingCarleson.intervalAvg
    exact div_pos (intervalIntegral.intervalIntegral_pos_of_pos_on hint
      (fun x _ => hA1.1 x) hab) (sub_pos.mpr hab)
  set M : ℝ := Real.exp (VanishingCarleson.A1A2.Mconst C₁ σ) with hMdef
  set c : ℝ := (M + 1) / VanishingCarleson.weightMean v a b with hcdef
  have hc : 0 < c := div_pos (by positivity) hmpos
  have hA1c : VanishingCarleson.WeightA1Pos (fun t => c * v t) C₁ σ := by
    refine ⟨fun t => mul_pos hc (hA1.1 t), ?_⟩
    intro p q hpq E hE hEsub
    rw [integral_const_mul, integral_const_mul, mul_div_mul_left _ _ hc.ne']
    exact hA1.2 p q hpq E hE hEsub
  have hkey := VanishingCarleson.A1A2.weightMean_le hC₁ hσ hσ1 hA1c hab (hint.const_mul c)
  have hmean : VanishingCarleson.weightMean (fun t => c * v t) a b =
      c * VanishingCarleson.weightMean v a b := by
    unfold VanishingCarleson.weightMean VanishingCarleson.intervalAvg
    rw [intervalIntegral.integral_const_mul]
    ring
  have hgeom : VanishingCarleson.weightGeomMean (fun t => c * v t) a b = 1 := by
    have hnot' : ¬ IntervalIntegrable (fun t => Real.log (c * v t)) volume a b := by
      intro hi
      apply hnot
      have heq : (fun t => Real.log (v t)) = fun t => Real.log (c * v t) - Real.log c := by
        funext t
        rw [Real.log_mul hc.ne' (hA1.1 t).ne']
        ring
      rw [heq]
      exact hi.sub intervalIntegrable_const
    unfold VanishingCarleson.weightGeomMean VanishingCarleson.intervalAvg
    rw [intervalIntegral.integral_undef hnot', zero_div, Real.exp_zero]
  rw [hmean, hgeom, mul_one] at hkey
  have hcm : c * VanishingCarleson.weightMean v a b = M + 1 := by
    rw [hcdef]
    field_simp
  linarith

/-- Helper: an `A_∞` weight (in the form of `VanishingCarleson`) has a logarithm integrable on
every interval (after `VanishingCarleson/ProofSteps.lean:155`). -/
theorem hp_log_intervalIntegrable {ω : ℝ → ℝ} (hA : VanishingCarleson.AInfinityWeight ω)
    (hint : ∀ a b : ℝ, IntervalIntegrable ω volume a b) (a b : ℝ) :
    IntervalIntegrable (fun t => Real.log (ω t)) volume a b := by
  obtain ⟨C₁, σ, hC₁, hσ, hσ1, hA1⟩ := hA
  obtain ⟨g, hgw, hg⟩ := hA1.exists_pos
  have key : ∀ u v : ℝ, u < v → IntervalIntegrable (fun t => Real.log (ω t)) volume u v := by
    intro u v huv
    have hintg : IntervalIntegrable g volume u v :=
      (hint u v).congr_ae (ae_restrict_of_ae hgw.symm)
    have hlogg := hp_log_intervalIntegrable_of_A1Pos hC₁ hσ hσ1 hg huv hintg
    refine hlogg.congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hgw] with t ht
    rw [ht]
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact key a b hab
  · exact IntervalIntegrable.refl
  · exact (key b a hab).symm

/-- Helper: the `(A2)` condition `(ω)_I ≤ A₀ e^{(log ω)_I}` bounds the mean oscillation of
`log ω` by `2 A₀` (`|v| ≤ 2 e^v - v`). -/
theorem hp_A2_osc {ω : ℝ → ℝ} {A₀ : ℝ} (hA2 : VanishingCarleson.WeightA2 ω A₀)
    (hpos : ∀ᵐ t, 0 < ω t) {a b : ℝ} (hab : a < b) (hint : IntervalIntegrable ω volume a b)
    (hlog : IntervalIntegrable (fun t => Real.log (ω t)) volume a b) :
    realMeanOsc (fun x => Real.log (ω x)) a b ≤ 2 * A₀ := by
  have hba : 0 < b - a := by linarith
  set m := intervalMean (fun x => Real.log (ω x)) a b with hmdef
  have hm : (b - a) * m = ∫ x in a..b, Real.log (ω x) := by
    rw [hmdef, intervalMean]
    field_simp
  have hA := hA2 a b hab
  unfold VanishingCarleson.weightMean VanishingCarleson.weightGeomMean
    VanishingCarleson.intervalAvg at hA
  rw [← hm, mul_div_cancel_left₀ _ hba.ne'] at hA
  have hpt : ∀ᵐ x, |Real.log (ω x) - m| ≤ 2 / Real.exp m * ω x - (Real.log (ω x) - m) := by
    filter_upwards [hpos] with x hx
    have h1 : Real.log (ω x) - m ≤ Real.exp (Real.log (ω x) - m) := by
      linarith [Real.add_one_le_exp (Real.log (ω x) - m)]
    have h2 : Real.exp (Real.log (ω x) - m) = ω x / Real.exp m := by
      rw [Real.exp_sub, Real.exp_log hx]
    rw [h2] at h1
    have h3 : 0 ≤ ω x / Real.exp m := by positivity
    rw [show 2 / Real.exp m * ω x = 2 * (ω x / Real.exp m) by ring]
    rcases le_or_gt 0 (Real.log (ω x) - m) with h | h
    · rw [abs_of_nonneg h]
      linarith
    · rw [abs_of_neg h]
      linarith
  have hI := intervalIntegral.integral_mono_ae hab.le ((hlog.sub intervalIntegrable_const).abs)
    ((hint.const_mul (2 / Real.exp m)).sub (hlog.sub intervalIntegrable_const)) hpt
  rw [intervalIntegral.integral_sub (hint.const_mul _) (hlog.sub intervalIntegrable_const),
    intervalIntegral.integral_sub hlog intervalIntegrable_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul, ← hm, sub_self, sub_zero] at hI
  unfold realMeanOsc
  rw [← hmdef]
  have hexp := Real.exp_pos m
  rw [inv_mul_le_iff₀ hba]
  calc ∫ x in a..b, |Real.log (ω x) - m| ≤ 2 / Real.exp m * ∫ x in a..b, ω x := hI
    _ ≤ 2 / Real.exp m * ((b - a) * (A₀ * Real.exp m)) := by
      gcongr
      rwa [div_le_iff₀ hba, mul_comm] at hA
    _ = (b - a) * (2 * A₀) := by field_simp

/-- `sec11-halfplane.tex:166` (cited from [WMUC, §2.4]): `log h' ∈ BMO(ℝ)` for `h ∈ SQS(ℝ)`. -/
theorem hp_sqs_logBMO {h ω : ℝ → ℝ} (hω : IsSQSWith h ω) :
    IsBMOReal fun x => Real.log (ω x) := by
  have hpos := hp_sqs_pos_ae hω
  have hA := hω.2.2.2.1
  have hvc := hp_ainfty_vc hA hpos
  obtain ⟨A₀, -, hA2⟩ := VanishingCarleson.a1_imp_a2 ω hvc
  have hint : ∀ a b : ℝ, IntervalIntegrable ω volume a b := fun a b =>
    (hA.2.1.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hlog := hp_log_intervalIntegrable hvc hint
  refine ⟨?_, 2 * A₀, fun a b hab => hp_A2_osc hA2 hpos hab (hint a b) (hlog a b)⟩
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨a, ha⟩ := hK.bddBelow
  obtain ⟨b, hb⟩ := hK.bddAbove
  refine IntegrableOn.mono_set
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (le_max_left a b)).mp (hlog a (max a b))) ?_
  intro t ht
  exact ⟨ha ht, (hb ht).trans (le_max_right a b)⟩

/-- `sec11-halfplane.tex:167`: if `h ∈ SQS(ℝ)` and `log h'` is Lipschitz, then `h ∈ SS(ℝ)`. -/
theorem hp_ss_of_lipschitz {h ω : ℝ → ℝ} (hω : IsSQSWith h ω) {c : ℝ≥0}
    (hlip : LipschitzWith c fun x => Real.log (ω x)) : IsSS h := by
  refine ⟨ω, hω, hp_sqs_pos_ae hω, hp_sqs_logBMO hω, ?_⟩
  intro ε hε
  refine ⟨ε / (c + 1), by positivity, ?_⟩
  intro a b hab hδ
  have hba : 0 < b - a := by linarith
  set u : ℝ → ℝ := fun x => Real.log (ω x) with hudef
  have hui : ∀ u' v' : ℝ, IntervalIntegrable u volume u' v' := fun _ _ =>
    hlip.continuous.intervalIntegrable _ _
  set m := intervalMean u a b with hmdef
  -- pointwise: `|u x - m| ≤ c (b - a)` on `(a, b]`
  have hpt : ∀ x ∈ Set.uIoc a b, ‖|u x - m|‖ ≤ c * (b - a) := by
    intro x hx
    rw [uIoc_of_le hab.le] at hx
    rw [Real.norm_eq_abs, abs_abs]
    have hsub : ∫ y in a..b, (u x - u y) = (b - a) * (u x - m) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hui a b),
        intervalIntegral.integral_const, smul_eq_mul, hmdef, intervalMean]
      field_simp
    have hb : ‖∫ y in a..b, (u x - u y)‖ ≤ c * (b - a) * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (by
        intro y hy
        rw [uIoc_of_le hab.le] at hy
        have := hlip.dist_le_mul x y
        rw [Real.dist_eq, Real.dist_eq] at this
        rw [Real.norm_eq_abs]
        calc |u x - u y| ≤ c * |x - y| := this
          _ ≤ c * (b - a) := by
            gcongr
            rw [abs_le]
            constructor <;> linarith [hx.1, hx.2, hy.1, hy.2])
    rw [hsub, norm_mul] at hb
    simp only [Real.norm_eq_abs, abs_of_pos hba] at hb
    nlinarith
  have hosc := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_of_pos hba] at hosc
  unfold realMeanOsc
  rw [← hmdef]
  have hle : ∫ x in a..b, |u x - m| ≤ c * (b - a) * (b - a) :=
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hosc)
  rw [inv_mul_le_iff₀ hba]
  have hcδ : (c : ℝ) * (b - a) ≤ ε := by
    have hc0 : (0 : ℝ) ≤ c := c.2
    calc (c : ℝ) * (b - a) ≤ (c + 1) * (ε / (c + 1)) := by
          gcongr
          · linarith
      _ = ε := by field_simp
  nlinarith

/-- Helper for (11.?) `eq:hp-RH`: `|h(I)| = ∫_I ω` for `I = [c - ℓ/2, c + ℓ/2]`. -/
theorem s11_rh_img {h ω : ℝ → ℝ} (hω : IsSQSWith h ω) {c ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    imgLength h c ℓ = ∫ x in Icc (c - ℓ / 2) (c + ℓ / 2), ω x := by
  obtain ⟨-, -, -, hA, hF⟩ := hω
  have hii : ∀ u v : ℝ, IntervalIntegrable ω volume u v := fun u v =>
    (hA.2.1.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  unfold imgLength
  rw [hF (c + ℓ / 2), hF (c - ℓ / 2), add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _),
    intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]

/-- Helper for (11.?) `eq:hp-RH`: a slight enlargement of an interval at most doubles the
`ω`-mass (`A_∞` applied to the small set `I' ∖ I`). -/
theorem s11_rh_dilate {ω : ℝ → ℝ} (hA : IsAInftyWeight ω) :
    ∃ η : ℝ, 0 < η ∧ ∀ a b a' b' : ℝ, a' ≤ a → a < b → b ≤ b' → b' - a' ≤ (1 + η) * (b - a) →
      ∫ x in Icc a' b', ω x ≤ 2 * ∫ x in Icc a b, ω x := by
  obtain ⟨hpos, hli, C, δ, hC, hδ, hA⟩ := hA
  have hC2 : 0 < 1 / (2 * C) := by positivity
  refine ⟨(1 / (2 * C)) ^ δ⁻¹, Real.rpow_pos_of_pos hC2 _, ?_⟩
  intro a b a' b' ha hab hb hlen
  have hη0 : 0 < (1 / (2 * C)) ^ δ⁻¹ := Real.rpow_pos_of_pos hC2 _
  have hηδ : ((1 / (2 * C)) ^ δ⁻¹) ^ δ = 1 / (2 * C) := Real.rpow_inv_rpow hC2.le hδ.ne'
  have hsub : Icc a b ⊆ Icc a' b' := Icc_subset_Icc ha hb
  have hab' : a' < b' := by linarith
  have hint : IntegrableOn ω (Icc a' b') := hli.integrableOn_isCompact isCompact_Icc
  have hvol : (volume (Icc a' b' \ Icc a b)).toReal = (b' - a') - (b - a) := by
    rw [measure_sdiff hsub measurableSet_Icc.nullMeasurableSet measure_Icc_lt_top.ne,
      Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_sub _ (by linarith : (0 : ℝ) ≤ b - a),
      ENNReal.toReal_ofReal (by linarith)]
  have hE := hA a' b' hab' (Icc a' b' \ Icc a b) sdiff_subset
    (measurableSet_Icc.diff measurableSet_Icc)
  rw [hvol, setIntegral_sdiff measurableSet_Icc hint hsub] at hE
  have hx0 : 0 ≤ ((b' - a') - (b - a)) / (b' - a') := div_nonneg (by linarith) (by linarith)
  have hx : ((b' - a') - (b - a)) / (b' - a') ≤ (1 / (2 * C)) ^ δ⁻¹ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hη0.le (by linarith : 0 ≤ (b' - a') - (b - a))]
  have hxδ : (((b' - a') - (b - a)) / (b' - a')) ^ δ ≤ 1 / (2 * C) := by
    rw [← hηδ]
    exact Real.rpow_le_rpow hx0 hx hδ.le
  have hI0 : 0 ≤ ∫ x in Icc a' b', ω x := setIntegral_nonneg measurableSet_Icc fun x _ => hpos x
  have hCx : C * (((b' - a') - (b - a)) / (b' - a')) ^ δ ≤ 1 / 2 := by
    have hC0 : C ≠ 0 := hC.ne'
    calc _ ≤ C * (1 / (2 * C)) := by gcongr
      _ = 1 / 2 := by field_simp
  have := mul_le_mul_of_nonneg_right hCx hI0
  linarith

/-- Helper for (11.?) `eq:hp-RH`: `h′dx` is doubling, `|h(2I)| ≤ D |h(I)|`, by iterating
`s11_rh_dilate`. This closes NOTES gap 3 (doubling of `h′dx` from `A_∞`) in Lean. -/
theorem s11_rh_doubling {h ω : ℝ → ℝ} (hω : IsSQSWith h ω) :
    ∃ D : ℝ, ∀ c ℓ : ℝ, 0 < ℓ → imgLength h c (2 * ℓ) ≤ D * imgLength h c ℓ := by
  have hA := hω.2.2.2.1
  obtain ⟨η, hη, hdil⟩ := s11_rh_dilate hA
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (2 : ℝ) (by linarith : (1 : ℝ) < 1 + η)
  refine ⟨2 ^ N, fun c ℓ hℓ => ?_⟩
  have hit : ∀ n : ℕ, ∀ s : ℝ, 0 < s →
      ∫ x in Icc (c - (1 + η) ^ n * s) (c + (1 + η) ^ n * s), ω x ≤
        2 ^ n * ∫ x in Icc (c - s) (c + s), ω x := by
    intro n
    induction n with
    | zero => intro s _; simp
    | succ n ih =>
      intro s hs
      have hpn : 0 < (1 + η) ^ n * s := by positivity
      have e : (1 + η) ^ (n + 1) * s = (1 + η) * ((1 + η) ^ n * s) := by ring
      have h1 : c - (1 + η) ^ (n + 1) * s ≤ c - (1 + η) ^ n * s := by
        rw [e]; nlinarith
      have h2 : c + (1 + η) ^ n * s ≤ c + (1 + η) ^ (n + 1) * s := by
        rw [e]; nlinarith
      have h3 : c + (1 + η) ^ (n + 1) * s - (c - (1 + η) ^ (n + 1) * s) ≤
          (1 + η) * (c + (1 + η) ^ n * s - (c - (1 + η) ^ n * s)) := by
        rw [e]; linarith
      have hstep := hdil (c - (1 + η) ^ n * s) (c + (1 + η) ^ n * s)
        (c - (1 + η) ^ (n + 1) * s) (c + (1 + η) ^ (n + 1) * s) h1 (by linarith) h2 h3
      calc _ ≤ 2 * ∫ x in Icc (c - (1 + η) ^ n * s) (c + (1 + η) ^ n * s), ω x := hstep
        _ ≤ 2 * (2 ^ n * ∫ x in Icc (c - s) (c + s), ω x) := by gcongr; exact ih s hs
        _ = 2 ^ (n + 1) * ∫ x in Icc (c - s) (c + s), ω x := by ring
  have hint : IntegrableOn ω (Icc (c - (1 + η) ^ N * (ℓ / 2)) (c + (1 + η) ^ N * (ℓ / 2))) :=
    hA.2.1.integrableOn_isCompact isCompact_Icc
  have hNℓ : ℓ ≤ (1 + η) ^ N * (ℓ / 2) := by nlinarith [mul_lt_mul_of_pos_right hN hℓ]
  rw [s11_rh_img hω (by positivity), s11_rh_img hω hℓ.le]
  calc ∫ x in Icc (c - 2 * ℓ / 2) (c + 2 * ℓ / 2), ω x ≤
        ∫ x in Icc (c - (1 + η) ^ N * (ℓ / 2)) (c + (1 + η) ^ N * (ℓ / 2)), ω x := by
        apply setIntegral_mono_set hint (Eventually.of_forall fun x => hA.1 x)
        exact (Icc_subset_Icc (by linarith) (by linarith)).eventuallyLE
    _ ≤ _ := hit N (ℓ / 2) (by positivity)

/-- Helper for (11.?) `eq:hp-RH`: the distribution bound
`ω({ω > t} ∩ I) ≤ K ((ω)_I / t)^κ ω(I)` (Chebyshev plus `A_∞`). -/
theorem s11_rh_level {ω : ℝ → ℝ} (hA : IsAInftyWeight ω) :
    ∃ K κ : ℝ, 0 ≤ K ∧ 0 < κ ∧ ∀ a b : ℝ, a < b → ∀ t : ℝ, 0 < t →
      ∫ x in Icc a b ∩ {x | t < ω x}, ω x ≤
        K * ((∫ x in Icc a b, ω x) / ((b - a) * t)) ^ κ * ∫ x in Icc a b, ω x := by
  obtain ⟨hpos, hli, C, δ, hC, hδ, hA⟩ := hA
  obtain ⟨d, hd0, hd1, hdδ⟩ : ∃ d : ℝ, 0 < d ∧ d < 1 ∧ d ≤ δ :=
    ⟨min δ (1 / 2), lt_min hδ (by norm_num), (min_le_right _ _).trans_lt (by norm_num),
      min_le_left _ _⟩
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 < r ∧ r * (1 - d) = 1 :=
    ⟨(1 - d)⁻¹, inv_pos.mpr (by linarith), inv_mul_cancel₀ (by linarith)⟩
  -- the algebra: `m ≤ C (m/T)^d W` forces `m ≤ C^r (W/T)^{dr} W`, `r = 1/(1-d)`
  have halg : ∀ m W T : ℝ, 0 < m → 0 < W → 0 < T → m ≤ C * (m / T) ^ d * W →
      m ≤ C ^ r * (W / T) ^ (d * r) * W := by
    intro m W T hm hW hT h
    have hmd : 0 < m ^ d := Real.rpow_pos_of_pos hm d
    have h1 : m ^ d * m ^ (1 - d) ≤ m ^ d * (C * W / T ^ d) := by
      rw [← Real.rpow_add hm, show d + (1 - d) = (1 : ℝ) by ring, Real.rpow_one]
      calc m ≤ C * (m / T) ^ d * W := h
        _ = m ^ d * (C * W / T ^ d) := by rw [Real.div_rpow hm.le hT.le]; ring
    have h2 : m ^ (1 - d) ≤ C * W / T ^ d := le_of_mul_le_mul_left h1 hmd
    have h3 : (m ^ (1 - d)) ^ r ≤ (C * W / T ^ d) ^ r :=
      Real.rpow_le_rpow (Real.rpow_nonneg hm.le _) h2 hr0.le
    have h4 : (m ^ (1 - d)) ^ r = m := by
      rw [← Real.rpow_mul hm.le, mul_comm, hr, Real.rpow_one]
    have h5 : (C * W / T ^ d) ^ r = C ^ r * (W / T) ^ (d * r) * W := by
      have hWr : W ^ r = W ^ (d * r) * W := by
        rw [← Real.rpow_add_one hW.ne']
        congr 1
        linarith
      rw [Real.div_rpow (mul_nonneg hC.le hW.le) (Real.rpow_nonneg hT.le d),
        Real.mul_rpow hC.le hW.le, ← Real.rpow_mul hT.le, Real.div_rpow hW.le hT.le, hWr]
      ring
    rw [h4, h5] at h3
    exact h3
  refine ⟨C ^ r, d * r, Real.rpow_nonneg hC.le _, mul_pos hd0 hr0, ?_⟩
  intro a b hab t ht
  obtain ⟨g, hgm, hg⟩ := hli.aestronglyMeasurable.aemeasurable
  have hE'm : MeasurableSet (Icc a b ∩ {x | t < g x}) :=
    measurableSet_Icc.inter (measurableSet_lt measurable_const hgm)
  have hEE : (Icc a b ∩ {x | t < ω x} : Set ℝ) =ᵐ[volume] Icc a b ∩ {x | t < g x} := by
    filter_upwards [hg] with x hx
    change (x ∈ Icc a b ∧ t < ω x) = (x ∈ Icc a b ∧ t < g x)
    rw [hx]
  rw [setIntegral_congr_set hEE]
  have hint : IntegrableOn ω (Icc a b) := hli.integrableOn_isCompact isCompact_Icc
  have hE'sub : Icc a b ∩ {x | t < g x} ⊆ Icc a b := inter_subset_left
  have hL : 0 < b - a := sub_pos.mpr hab
  have hm0 : 0 ≤ ∫ x in Icc a b ∩ {x | t < g x}, ω x :=
    setIntegral_nonneg hE'm fun x _ => hpos x
  have hmW : ∫ x in Icc a b ∩ {x | t < g x}, ω x ≤ ∫ x in Icc a b, ω x :=
    setIntegral_mono_set hint (Eventually.of_forall fun x => hpos x) hE'sub.eventuallyLE
  have hvolfin : volume (Icc a b ∩ {x | t < g x}) ≠ ⊤ :=
    ((measure_mono hE'sub).trans_lt measure_Icc_lt_top).ne
  -- Chebyshev
  have hcheb : t * (volume (Icc a b ∩ {x | t < g x})).toReal ≤
      ∫ x in Icc a b ∩ {x | t < g x}, ω x := by
    have h1 := setIntegral_ge_of_const_le_real hE'm hvolfin (fun x hx => le_of_lt hx.2)
      ((hint.mono_set hE'sub).congr (ae_restrict_of_ae hg))
    rw [measureReal_def] at h1
    refine h1.trans (le_of_eq ?_)
    exact integral_congr_ae (ae_restrict_of_ae hg.symm)
  have hvL : (volume (Icc a b ∩ {x | t < g x})).toReal ≤ b - a := by
    have := ENNReal.toReal_mono (measure_Icc_lt_top (μ := volume) (a := a) (b := b)).ne
      (measure_mono (μ := volume) hE'sub)
    rwa [Real.volume_Icc, ENNReal.toReal_ofReal hL.le] at this
  have hv0 : 0 ≤ (volume (Icc a b ∩ {x | t < g x})).toReal := ENNReal.toReal_nonneg
  have hAI := hA a b hab _ hE'sub hE'm
  have hx0 : 0 ≤ (volume (Icc a b ∩ {x | t < g x})).toReal / (b - a) := div_nonneg hv0 hL.le
  have hx1 : (volume (Icc a b ∩ {x | t < g x})).toReal / (b - a) ≤ 1 :=
    (div_le_one hL).mpr hvL
  have hxm : (volume (Icc a b ∩ {x | t < g x})).toReal / (b - a) ≤
      (∫ x in Icc a b ∩ {x | t < g x}, ω x) / ((b - a) * t) := by
    rw [div_le_div_iff₀ hL (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hcheb hL.le]
  have hW0 : 0 ≤ ∫ x in Icc a b, ω x := setIntegral_nonneg measurableSet_Icc fun x _ => hpos x
  have hmain : ∫ x in Icc a b ∩ {x | t < g x}, ω x ≤
      C * ((∫ x in Icc a b ∩ {x | t < g x}, ω x) / ((b - a) * t)) ^ d * ∫ x in Icc a b, ω x := by
    refine hAI.trans ?_
    gcongr
    calc ((volume (Icc a b ∩ {x | t < g x})).toReal / (b - a)) ^ δ ≤
          ((volume (Icc a b ∩ {x | t < g x})).toReal / (b - a)) ^ d :=
          Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 hd0.le hdδ
      _ ≤ _ := Real.rpow_le_rpow hx0 hxm hd0.le
  rcases hm0.eq_or_lt with hm | hm
  · rw [← hm]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hC.le _)
      (Real.rpow_nonneg (div_nonneg hW0 (by positivity)) _)) hW0
  · exact halg _ _ _ hm (hm.trans_le hmW) (by positivity) hmain

/-- Helper for (11.?) `eq:hp-RH`: the reverse Hölder inequality for an `A_∞` weight (layer cake
for `∫_I ω · ω^{p-1}` against `s11_rh_level`, with `p = 1 + κ/2`). -/
theorem s11_rh_main {ω : ℝ → ℝ} (hA : IsAInftyWeight ω) :
    ∃ p Ch : ℝ, 1 < p ∧ ∀ a b : ℝ, a < b →
      ((∫⁻ x in Icc a b, ENNReal.ofReal (ω x ^ p)) / ENNReal.ofReal (b - a)) ^ (1 / p) ≤
        ENNReal.ofReal Ch * ((∫⁻ x in Icc a b, ENNReal.ofReal (ω x)) / ENNReal.ofReal (b - a)) := by
  obtain ⟨K, κ, hK, hκ, hlev⟩ := s11_rh_level hA
  obtain ⟨hpos, hli, -⟩ := hA
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = 1 + κ / 2 := ⟨_, rfl⟩
  have hp1 : 1 < p := by rw [hpdef]; linarith
  have hp0 : 0 < p := by linarith
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = 1 + 2 * K * p / κ := ⟨_, rfl⟩
  have hM : 0 ≤ M := by rw [hMdef]; positivity
  refine ⟨p, M ^ (1 / p), hp1, ?_⟩
  intro a b hab
  have hFTC : ∀ y : ℝ, 0 ≤ y → ∫ t in (0 : ℝ)..y, p * t ^ (p - 1) = y ^ p := by
    intro y _
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
      show p - 1 + 1 = p by ring, Real.zero_rpow hp0.ne', sub_zero]
    field_simp
  have hL : 0 < b - a := sub_pos.mpr hab
  have hint : IntegrableOn ω (Icc a b) := hli.integrableOn_isCompact isCompact_Icc
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = ∫ x in Icc a b, ω x := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hWdef]; exact setIntegral_nonneg measurableSet_Icc fun x _ => hpos x
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = W / (b - a) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAdef]; exact div_nonneg hW0 hL.le
  obtain ⟨g, hgm, hg⟩ := hli.aestronglyMeasurable.aemeasurable
  obtain ⟨f, hfm, hf0, hfeq⟩ : ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ ω =ᵐ[volume] f :=
    ⟨fun x => max (g x) 0, hgm.max measurable_const, fun x => le_max_right _ _,
      hg.mono fun x hx => by
        show ω x = max (g x) 0
        rw [← hx, max_eq_left (hpos x)]⟩
  have hfint : IntegrableOn f (Icc a b) := hint.congr (ae_restrict_of_ae hfeq)
  have hμle : ∀ t : ℝ, volume.restrict (Icc a b) {x | t < f x} ≤ ENNReal.ofReal (b - a) :=
    fun t => by
      calc volume.restrict (Icc a b) {x | t < f x} ≤ volume.restrict (Icc a b) univ :=
            measure_mono (subset_univ _)
        _ = ENNReal.ofReal (b - a) := by rw [Measure.restrict_apply_univ, Real.volume_Icc]
  -- Chebyshev plus the level bound
  have hcheb : ∀ t : ℝ, 0 < t → t * (volume.restrict (Icc a b) {x | t < f x}).toReal ≤
      K * (W / ((b - a) * t)) ^ κ * W := by
    intro t ht
    have hs : MeasurableSet {x | t < f x} := measurableSet_lt measurable_const hfm
    have hset : (Icc a b ∩ {x | t < ω x} : Set ℝ) =ᵐ[volume] {x | t < f x} ∩ Icc a b := by
      filter_upwards [hfeq] with x hx
      change (x ∈ Icc a b ∧ t < ω x) = (t < f x ∧ x ∈ Icc a b)
      rw [hx, and_comm]
    rw [Measure.restrict_apply hs]
    have h1 := setIntegral_ge_of_const_le_real (hs.inter measurableSet_Icc)
      ((measure_mono inter_subset_right).trans_lt measure_Icc_lt_top).ne
      (fun x hx => le_of_lt hx.1) (hfint.mono_set inter_subset_right)
    rw [measureReal_def] at h1
    calc t * (volume ({x | t < f x} ∩ Icc a b)).toReal ≤
          ∫ x in {x | t < f x} ∩ Icc a b, f x := h1
      _ = ∫ x in Icc a b ∩ {x | t < ω x}, ω x := by
          rw [setIntegral_congr_set hset]
          exact integral_congr_ae (ae_restrict_of_ae hfeq.symm)
      _ ≤ _ := by rw [hWdef]; exact hlev a b hab t ht
  -- the layer cake
  have hX1 : ∫⁻ x in Icc a b, ENNReal.ofReal (ω x ^ p) =
      ∫⁻ x in Icc a b, ENNReal.ofReal (f x ^ p) :=
    lintegral_congr_ae (ae_restrict_of_ae (hfeq.mono fun x hx => by simp only [hx]))
  have hlc := lintegral_comp_eq_lintegral_meas_lt_mul (volume.restrict (Icc a b)) (f := f)
    (g := fun t => p * t ^ (p - 1)) (Eventually.of_forall fun x => hf0 x) hfm.aemeasurable
    (fun t _ => (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul p)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg hp0.le (Real.rpow_nonneg (le_of_lt ht) _))
  have h1 : ∀ x, ENNReal.ofReal (∫ t in (0 : ℝ)..f x, p * t ^ (p - 1)) =
      ENNReal.ofReal (f x ^ p) := fun x => by rw [hFTC _ (hf0 x)]
  simp only [h1] at hlc
  rcases hW0.eq_or_lt with hW | hWpos
  · -- `W = 0`: every level set is null
    have hz : ∀ t ∈ Ioi (0 : ℝ), volume.restrict (Icc a b) {x | t < f x} *
        ENNReal.ofReal (p * t ^ (p - 1)) = 0 := by
      intro t ht
      have h := hcheb t ht
      rw [← hW, mul_zero] at h
      have hv0 := ENNReal.toReal_nonneg (a := volume.restrict (Icc a b) {x | t < f x})
      have ht0 : (0 : ℝ) < t := ht
      have hv : (volume.restrict (Icc a b) {x | t < f x}).toReal = 0 :=
        le_antisymm (by nlinarith) hv0
      have hfin : volume.restrict (Icc a b) {x | t < f x} ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hμle t)
      rw [((ENNReal.toReal_eq_zero_iff _).mp hv).resolve_right hfin, zero_mul]
    have hX0 : ∫⁻ x in Icc a b, ENNReal.ofReal (ω x ^ p) = 0 := by
      rw [hX1, hlc, setLIntegral_congr_fun measurableSet_Ioi hz, lintegral_zero]
    rw [hX0, ENNReal.zero_div, ENNReal.zero_rpow_of_pos (by positivity)]
    exact zero_le
  have hApos : 0 < A := by rw [hAdef]; exact div_pos hWpos hL
  have hL' : b - a ≠ 0 := hL.ne'
  have hκ0 : κ ≠ 0 := hκ.ne'
  -- the part `t ≤ A`
  have hIoc : IntegrableOn (fun t : ℝ => p * t ^ (p - 1)) (Ioc 0 A) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hApos.le).mp
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul p)
  have hP1 : ∫⁻ t in Ioc 0 A, volume.restrict (Icc a b) {x | t < f x} *
      ENNReal.ofReal (p * t ^ (p - 1)) ≤ ENNReal.ofReal ((b - a) * A ^ p) := by
    calc _ ≤ ∫⁻ t in Ioc 0 A, ENNReal.ofReal (b - a) * ENNReal.ofReal (p * t ^ (p - 1)) :=
          setLIntegral_mono' measurableSet_Ioc fun t _ =>
            mul_le_mul_of_nonneg_right (hμle t) zero_le
      _ = ENNReal.ofReal (b - a) * ENNReal.ofReal (A ^ p) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            ← ofReal_integral_eq_lintegral_ofReal hIoc (by
              filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
              exact mul_nonneg hp0.le (Real.rpow_nonneg ht.1.le _)),
            ← intervalIntegral.integral_of_le hApos.le, hFTC A hA0]
      _ = _ := (ENNReal.ofReal_mul hL.le).symm
  -- the part `t > A`
  have hr : -1 - κ / 2 < -1 := by linarith
  have hc : 0 ≤ K * p * W * A ^ κ := by positivity
  have hpt : ∀ t ∈ Ioi A, volume.restrict (Icc a b) {x | t < f x} *
      ENNReal.ofReal (p * t ^ (p - 1)) ≤ ENNReal.ofReal (K * p * W * A ^ κ * t ^ (-1 - κ / 2)) := by
    intro t ht
    have ht0 : 0 < t := hApos.trans ht
    have hfin : volume.restrict (Icc a b) {x | t < f x} ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hμle t)
    have hc1 := hcheb t ht0
    have hv0 := ENNReal.toReal_nonneg (a := volume.restrict (Icc a b) {x | t < f x})
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul hv0]
    apply ENNReal.ofReal_le_ofReal
    generalize (volume.restrict (Icc a b) {x | t < f x}).toReal = v at hc1 hv0 ⊢
    have hu : 0 < t ^ (κ / 2) := Real.rpow_pos_of_pos ht0 _
    have hu' : t ^ (κ / 2) ≠ 0 := hu.ne'
    have ht' : t ≠ 0 := ht0.ne'
    have e1 : W / ((b - a) * t) = A / t := by rw [hAdef]; field_simp
    have e2 : t ^ κ = t ^ (κ / 2) * t ^ (κ / 2) := by
      rw [← Real.rpow_add ht0]; congr 1; ring
    have e3 : t ^ (-1 - κ / 2) = (t * t ^ (κ / 2))⁻¹ := by
      rw [show -1 - κ / 2 = -(1 + κ / 2) by ring, Real.rpow_neg ht0.le, Real.rpow_add ht0,
        Real.rpow_one]
    have e4 : p - 1 = κ / 2 := by rw [hpdef]; ring
    rw [e1, Real.div_rpow hA0 ht0.le, e2] at hc1
    rw [e3, e4]
    have hK2 : v * (p * t ^ (κ / 2)) = (t * v) * (p * t ^ (κ / 2) / t) := by field_simp
    have hR : K * p * W * A ^ κ * (t * t ^ (κ / 2))⁻¹ =
        (K * (A ^ κ / (t ^ (κ / 2) * t ^ (κ / 2))) * W) * (p * t ^ (κ / 2) / t) := by
      field_simp
    rw [hK2, hR]
    exact mul_le_mul_of_nonneg_right hc1 (by positivity)
  have hP2 : ∫⁻ t in Ioi A, volume.restrict (Icc a b) {x | t < f x} *
      ENNReal.ofReal (p * t ^ (p - 1)) ≤
        ENNReal.ofReal (K * p * W * A ^ κ * (2 / κ * A ^ (-(κ / 2)))) := by
    calc _ ≤ ∫⁻ t in Ioi A, ENNReal.ofReal (K * p * W * A ^ κ * t ^ (-1 - κ / 2)) :=
          setLIntegral_mono' measurableSet_Ioi hpt
      _ = _ := by
          rw [← ofReal_integral_eq_lintegral_ofReal
            ((integrableOn_Ioi_rpow_of_lt hr hApos).const_mul _) (by
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              exact mul_nonneg hc (Real.rpow_nonneg (hApos.trans ht).le _)),
            integral_const_mul, integral_Ioi_rpow_of_lt hr hApos]
          congr 2
          rw [show -1 - κ / 2 + 1 = -(κ / 2) by ring]
          field_simp
  have hX : ∫⁻ x in Icc a b, ENNReal.ofReal (ω x ^ p) ≤
      ENNReal.ofReal (M * A ^ p) * ENNReal.ofReal (b - a) := by
    rw [hX1, hlc, ← Ioc_union_Ioi_eq_Ioi hApos.le]
    refine (lintegral_union_le _ _ _).trans ?_
    calc _ ≤ ENNReal.ofReal ((b - a) * A ^ p) +
          ENNReal.ofReal (K * p * W * A ^ κ * (2 / κ * A ^ (-(κ / 2)))) := add_le_add hP1 hP2
      _ = ENNReal.ofReal ((b - a) * A ^ p + K * p * W * A ^ κ * (2 / κ * A ^ (-(κ / 2)))) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ = ENNReal.ofReal (M * A ^ p) * ENNReal.ofReal (b - a) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have eW : W = A * (b - a) := by rw [hAdef]; field_simp
          have eAp : A ^ p = A * A ^ (κ / 2) := by
            rw [hpdef, Real.rpow_add hApos, Real.rpow_one]
          have eAk : A ^ κ * A ^ (-(κ / 2)) = A ^ (κ / 2) := by
            rw [← Real.rpow_add hApos]; congr 1; ring
          rw [eAp, eW, hMdef]
          linear_combination (2 * K * p * A * (b - a) / κ) * eAk
  have hW1 : ∫⁻ x in Icc a b, ENNReal.ofReal (ω x) = ENNReal.ofReal W := by
    rw [hWdef]
    exact (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => hpos x)).symm
  rw [hW1, ← ENNReal.ofReal_div_of_pos hL, ← hAdef]
  have h2 := ENNReal.div_le_of_le_mul hX
  calc _ ≤ ENNReal.ofReal (M * A ^ p) ^ (1 / p) := ENNReal.rpow_le_rpow h2 (by positivity)
    _ = ENNReal.ofReal ((M * A ^ p) ^ (1 / p)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)
    _ = ENNReal.ofReal (M ^ (1 / p) * A) := by
        rw [Real.mul_rpow hM (Real.rpow_nonneg hA0 _), ← Real.rpow_mul hA0,
          mul_one_div_cancel hp0.ne', Real.rpow_one]
    _ = ENNReal.ofReal (M ^ (1 / p)) * ENNReal.ofReal A :=
        ENNReal.ofReal_mul (Real.rpow_nonneg hM _)

/-- (11.?) `eq:hp-RH`, `sec11-halfplane.tex:169–180` (cited from [WMUC, §2.2] and
[GCRF, Thm IV.2.11]): every `h ∈ SQS(ℝ)` has strong quasisymmetry data `(D_h, p_h, C_h)`. -/
theorem eq_hp_RH {h : ℝ → ℝ} (hs : IsSQS h) : ∃ D p Ch : ℝ, IsSQSData h D p Ch := by
  obtain ⟨ω, hω⟩ := hs
  obtain ⟨D, hD⟩ := s11_rh_doubling hω
  obtain ⟨p, Ch, hp, hRH⟩ := s11_rh_main hω.2.2.2.1
  exact ⟨D, p, Ch, ω, hω, hD, hp, hRH⟩

/-- Helper for (11.?) `eq:hp-maximal`: the uncentered maximal function is lower semicontinuous
(an interval `[a, b] ∋ t` with average `> y` can be enlarged to `[a - ε, b + ε]`, a neighbourhood
of `t`, keeping the average `> y`). -/
theorem s11_max_lsc (φ : ℝ → ℝ) : LowerSemicontinuous (maxFnU φ) := by
  intro t y hy
  unfold maxFnU at hy
  obtain ⟨a, ha⟩ := lt_iSup_iff.mp hy
  obtain ⟨b, hb⟩ := lt_iSup_iff.mp ha
  obtain ⟨hat, h3⟩ := lt_iSup_iff.mp hb
  obtain ⟨htb, h4⟩ := lt_iSup_iff.mp h3
  obtain ⟨hab, h5⟩ := lt_iSup_iff.mp h4
  have hL : ENNReal.ofReal (b - a) ≠ 0 := (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have hyX : y * ENNReal.ofReal (b - a) < ∫⁻ x in Icc a b, ENNReal.ofReal |φ x| :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl hL) (Or.inl ENNReal.ofReal_ne_top)).mp h5
  have hyt : y ≠ ⊤ := ne_top_of_lt h5
  have hc : Tendsto (fun ε : ℝ => y * ENNReal.ofReal (b - a + 2 * ε)) (𝓝 0)
      (𝓝 (y * ENNReal.ofReal (b - a))) := by
    have h0 : Tendsto (fun ε : ℝ => b - a + 2 * ε) (𝓝 0) (𝓝 (b - a)) := by
      have hcont : Continuous fun ε : ℝ => b - a + 2 * ε := by fun_prop
      convert hcont.tendsto 0 using 2
      ring
    exact ENNReal.Tendsto.const_mul ((ENNReal.continuous_ofReal.tendsto _).comp h0) (Or.inr hyt)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hc.eventually (gt_mem_nhds hyX))
  have hε : y * ENNReal.ofReal (b - a + 2 * (δ / 2)) < ∫⁻ x in Icc a b, ENNReal.ofReal |φ x| := by
    refine hball ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
    linarith
  filter_upwards [Ioo_mem_nhds (show a - δ / 2 < t by linarith) (show t < b + δ / 2 by linarith)]
    with t' ht'
  unfold maxFnU
  have hmono : ∫⁻ x in Icc a b, ENNReal.ofReal |φ x| ≤
      ∫⁻ x in Icc (a - δ / 2) (b + δ / 2), ENNReal.ofReal |φ x| :=
    lintegral_mono_set (Icc_subset_Icc (by linarith) (by linarith))
  have hlt : y < (∫⁻ x in Icc (a - δ / 2) (b + δ / 2), ENNReal.ofReal |φ x|) /
      ENNReal.ofReal (b + δ / 2 - (a - δ / 2)) := by
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.ofReal_pos.mpr (by linarith)).ne')
      (Or.inl ENNReal.ofReal_ne_top), show b + δ / 2 - (a - δ / 2) = b - a + 2 * (δ / 2) by ring]
    exact lt_of_lt_of_le hε hmono
  exact lt_of_lt_of_le hlt (le_iSup_of_le (a - δ / 2) (le_iSup_of_le (b + δ / 2)
    (le_iSup_of_le ht'.1.le (le_iSup_of_le ht'.2.le (le_iSup_of_le (by linarith) le_rfl)))))

/-- Helper for (11.?) `eq:hp-maximal`: the weak type `(1,1)` covering estimate.  If `g ≥ 0` and
`s > 0`, the set of `t` lying in some `[a, b]` with `s (b - a) < ∫_{[a,b]} g` has measure at most
`(4/s) ∫ g` (Vitali covering, closed balls, dilation factor `4`). -/
theorem s11_max_weak {g : ℝ → ℝ≥0∞} (hg : Measurable g) {s : ℝ} (hs : 0 < s) :
    volume {t : ℝ | ∃ a b : ℝ, a ≤ t ∧ t ≤ b ∧ a < b ∧
      ENNReal.ofReal s * ENNReal.ofReal (b - a) < ∫⁻ x in Icc a b, g x} ≤
      ENNReal.ofReal (4 / s) * ∫⁻ x, g x := by
  -- `hg` is not needed: only monotonicity and countable additivity of `∫⁻` over the disjoint
  -- (measurable) balls are used; the statement stays true without it.
  have _hg := hg
  have h4s : 0 < 4 / s := div_pos (by norm_num) hs
  by_cases hI : ∫⁻ x, g x = ⊤
  · rw [hI, ENNReal.mul_top (ENNReal.ofReal_pos.mpr h4s).ne']
    exact le_top
  -- the covering family: all intervals `[a, b]` with `s (b - a) < ∫_{[a,b]} g`
  set T : Set (ℝ × ℝ) := {q | q.1 < q.2 ∧
    ENNReal.ofReal s * ENNReal.ofReal (q.2 - q.1) < ∫⁻ x in Icc q.1 q.2, g x} with hT
  set c : ℝ × ℝ → ℝ := fun q => (q.1 + q.2) / 2 with hc
  set r : ℝ × ℝ → ℝ := fun q => (q.2 - q.1) / 2 with hr
  have hball : ∀ q : ℝ × ℝ, closedBall (c q) (r q) = Icc q.1 q.2 := by
    intro q
    rw [Real.closedBall_eq_Icc]
    congr 1 <;> simp only [hc, hr] <;> ring
  -- radii are bounded since `∫ g < ∞`
  have hR : ∀ q ∈ T, r q ≤ (∫⁻ x, g x).toReal / s := by
    intro q hq
    have hlen : 0 ≤ s * (q.2 - q.1) := mul_nonneg hs.le (sub_nonneg.mpr hq.1.le)
    have h1 : ENNReal.ofReal (s * (q.2 - q.1)) < ∫⁻ x, g x := by
      rw [ENNReal.ofReal_mul hs.le]
      exact lt_of_lt_of_le hq.2 (setLIntegral_le_lintegral _ _)
    have h2 := (ENNReal.ofReal_lt_iff_lt_toReal hlen hI).mp h1
    rw [le_div_iff₀ hs]
    simp only [hr]
    nlinarith [hq.1]
  obtain ⟨u, hut, hdisj, hcov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall T c r _ hR 4 (by norm_num)
  have hrpos : ∀ q ∈ T, 0 < r q := fun q hq => by
    simp only [hr]
    linarith [hq.1]
  have hcount : u.Countable := hdisj.countable_of_nonempty_interior fun q hq =>
    ⟨c q, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ (hrpos q (hut hq)))⟩
  have hsub : {t : ℝ | ∃ a b : ℝ, a ≤ t ∧ t ≤ b ∧ a < b ∧
      ENNReal.ofReal s * ENNReal.ofReal (b - a) < ∫⁻ x in Icc a b, g x} ⊆
      ⋃ q ∈ u, closedBall (c q) (4 * r q) := by
    rintro t ⟨a, b, hat, htb, hab, hlt⟩
    obtain ⟨q', hq'u, hq'⟩ := hcov (a, b) ⟨hab, hlt⟩
    exact mem_biUnion hq'u (hq' (by rw [hball]; exact ⟨hat, htb⟩))
  calc volume {t : ℝ | ∃ a b : ℝ, a ≤ t ∧ t ≤ b ∧ a < b ∧
        ENNReal.ofReal s * ENNReal.ofReal (b - a) < ∫⁻ x in Icc a b, g x}
      ≤ volume (⋃ q ∈ u, closedBall (c q) (4 * r q)) := measure_mono hsub
    _ ≤ ∑' q : u, volume (closedBall (c q.1) (4 * r q.1)) := measure_biUnion_le _ hcount _
    _ ≤ ∑' q : u, ENNReal.ofReal (4 / s) * ∫⁻ x in closedBall (c q.1) (r q.1), g x := by
        refine tsum_le_tsum fun q => ?_
        have hq := hut q.2
        rw [Real.volume_closedBall, hball]
        calc ENNReal.ofReal (2 * (4 * r q.1))
            = ENNReal.ofReal (4 / s) * (ENNReal.ofReal s * ENNReal.ofReal (q.1.2 - q.1.1)) := by
              rw [← ENNReal.ofReal_mul hs.le, ← ENNReal.ofReal_mul h4s.le]
              congr 1
              simp only [hr]
              field_simp
          _ ≤ ENNReal.ofReal (4 / s) * ∫⁻ x in Icc q.1.1 q.1.2, g x := by
              gcongr
              exact hq.2.le
    _ = ENNReal.ofReal (4 / s) * ∑' q : u, ∫⁻ x in closedBall (c q.1) (r q.1), g x :=
        ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (4 / s) * ∫⁻ x in ⋃ q ∈ u, closedBall (c q) (r q), g x := by
        rw [lintegral_biUnion hcount (fun q _ => measurableSet_closedBall) hdisj]
    _ ≤ ENNReal.ofReal (4 / s) * ∫⁻ x, g x := by
        gcongr _ * ?_
        exact setLIntegral_le_lintegral _ _

/-- Helper for (11.?) `eq:hp-maximal`: the distribution estimate
`|{M_u φ > 2s}| ≤ (4/s) ∫_{|φ| > s} |φ|` (split `φ` at height `s`). -/
theorem s11_max_distrib {φ : ℝ → ℝ} (hφ : Measurable φ) {s : ℝ} (hs : 0 < s) :
    volume {t : ℝ | ENNReal.ofReal (2 * s) < maxFnU φ t} ≤
      ENNReal.ofReal (4 / s) *
        ∫⁻ x, {y : ℝ | s < |φ y|}.indicator (fun y => ENNReal.ofReal |φ y|) x := by
  have hg : Measurable ({y : ℝ | s < |φ y|}.indicator (fun y => ENNReal.ofReal |φ y|)) :=
    (ENNReal.measurable_ofReal.comp hφ.abs).indicator (measurableSet_lt measurable_const hφ.abs)
  refine le_trans (measure_mono ?_) (s11_max_weak hg hs)
  intro t ht
  have ht' : ENNReal.ofReal (2 * s) < maxFnU φ t := ht
  unfold maxFnU at ht'
  obtain ⟨a, ha⟩ := lt_iSup_iff.mp ht'
  obtain ⟨b, hb⟩ := lt_iSup_iff.mp ha
  obtain ⟨hat, h3⟩ := lt_iSup_iff.mp hb
  obtain ⟨htb, h4⟩ := lt_iSup_iff.mp h3
  obtain ⟨hab, h5⟩ := lt_iSup_iff.mp h4
  have hL0 : ENNReal.ofReal (b - a) ≠ 0 := (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have h6 := (ENNReal.lt_div_iff_mul_lt (Or.inl hL0) (Or.inl ENNReal.ofReal_ne_top)).mp h5
  -- `|φ| ≤ |φ| 1_{|φ| > s} + s`
  have hpt : ∀ x, ENNReal.ofReal |φ x| ≤
      {y : ℝ | s < |φ y|}.indicator (fun y => ENNReal.ofReal |φ y|) x + ENNReal.ofReal s := by
    intro x
    by_cases hx : s < |φ x|
    · rw [indicator_of_mem (show x ∈ {y : ℝ | s < |φ y|} from hx)]
      exact le_self_add
    · rw [indicator_of_notMem (show x ∉ {y : ℝ | s < |φ y|} from hx), zero_add]
      exact ENNReal.ofReal_le_ofReal (not_lt.mp hx)
  have h7 : ∫⁻ x in Icc a b, ENNReal.ofReal |φ x| ≤
      (∫⁻ x in Icc a b, {y : ℝ | s < |φ y|}.indicator (fun y => ENNReal.ofReal |φ y|) x) +
        ENNReal.ofReal s * ENNReal.ofReal (b - a) := by
    calc ∫⁻ x in Icc a b, ENNReal.ofReal |φ x|
        ≤ ∫⁻ x in Icc a b,
            ({y : ℝ | s < |φ y|}.indicator (fun y => ENNReal.ofReal |φ y|) x + ENNReal.ofReal s) :=
          lintegral_mono hpt
      _ = _ := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const, Real.volume_Icc]
  have h2s : ENNReal.ofReal (2 * s) * ENNReal.ofReal (b - a) =
      ENNReal.ofReal s * ENNReal.ofReal (b - a) + ENNReal.ofReal s * ENNReal.ofReal (b - a) := by
    rw [← add_mul, ← ENNReal.ofReal_add hs.le hs.le, two_mul]
  have hfin : ENNReal.ofReal s * ENNReal.ofReal (b - a) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have h8 := lt_of_lt_of_le h6 h7
  rw [h2s] at h8
  show ∃ a b : ℝ, a ≤ t ∧ t ≤ b ∧ a < b ∧ ENNReal.ofReal s * ENNReal.ofReal (b - a) <
    ∫⁻ x in Icc a b, {y : ℝ | s < |φ y|}.indicator (fun y => ENNReal.ofReal |φ y|) x
  exact ⟨a, b, hat, htb, hab, (ENNReal.add_lt_add_iff_right hfin).mp h8⟩

/-- Helper for (11.?) `eq:hp-maximal`: the layer-cake formula
`∫ F^p dμ = ∫_0^∞ μ{F > s} p s^{p-1} ds` for a measurable `F : α → [0,∞]` and an arbitrary
measure (from Mathlib's `lintegral_comp_eq_lintegral_meas_lt_mul` by truncation `min F n`). -/
theorem s11_max_layer {α : Type*} [MeasurableSpace α] (μ : Measure α) {F : α → ℝ≥0∞}
    (hF : Measurable F) {p : ℝ} (hp : 0 < p) :
    ∫⁻ a, F a ^ p ∂μ =
      ∫⁻ s in Ioi (0 : ℝ), μ {a | ENNReal.ofReal s < F a} * ENNReal.ofReal (p * s ^ (p - 1)) := by
  have hfin : ∀ (n : ℕ) (a : α), min (F a) n ≠ ⊤ := fun n a =>
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _)
  have hmeas : ∀ n : ℕ, Measurable fun a => min (F a) n := fun n => hF.min measurable_const
  have hint : ∀ x : ℝ, 0 ≤ x → ∫ t in (0 : ℝ)..x, p * t ^ (p - 1) = x ^ p := by
    intro x _
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
      show p - 1 + 1 = p by ring, Real.zero_rpow hp.ne', sub_zero]
    field_simp
  have hw : Measurable fun s : ℝ => ENNReal.ofReal (p * s ^ (p - 1)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_id.pow_const _))
  -- the truncated formula, from Mathlib's layer cake
  have key : ∀ n : ℕ, ∫⁻ a, min (F a) n ^ p ∂μ = ∫⁻ s in Ioi (0 : ℝ),
      μ {a | ENNReal.ofReal s < min (F a) n} * ENNReal.ofReal (p * s ^ (p - 1)) := by
    intro n
    have h := lintegral_comp_eq_lintegral_meas_lt_mul μ (f := fun a => (min (F a) n).toReal)
      (g := fun t => p * t ^ (p - 1)) (Eventually.of_forall fun a => ENNReal.toReal_nonneg)
      (hmeas n).ennreal_toReal.aemeasurable
      (fun t _ => (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul p)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg hp.le (Real.rpow_nonneg (le_of_lt ht) _))
    have h1 : ∀ a, ENNReal.ofReal (∫ t in (0 : ℝ)..(min (F a) n).toReal, p * t ^ (p - 1)) =
        min (F a) n ^ p := fun a => by
      rw [hint _ ENNReal.toReal_nonneg, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le,
        ENNReal.ofReal_toReal (hfin n a)]
    simp only [h1] at h
    rw [h]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hset : {a | u < (min (F a) n).toReal} = {a | ENNReal.ofReal u < min (F a) n} := by
      ext a
      exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hu) (hfin n a)).symm
    rw [hset]
  have hsup : ∀ a, ⨆ n : ℕ, min (F a) n = F a := by
    intro a
    apply le_antisymm (iSup_le fun n => min_le_left _ _)
    refine le_of_forall_lt fun b hb => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_top_of_lt hb)
    exact lt_of_lt_of_le (lt_min hb hn) (le_iSup (fun n : ℕ => min (F a) n) n)
  have hsupp : ∀ a, ⨆ n : ℕ, min (F a) n ^ p = F a ^ p := by
    intro a
    have hmono : Monotone fun n : ℕ => min (F a) n := fun n m hnm =>
      min_le_min le_rfl (Nat.cast_le.mpr hnm)
    calc ⨆ n : ℕ, min (F a) n ^ p = (⨆ n : ℕ, min (F a) n) ^ p :=
          ((ENNReal.monotone_rpow_of_nonneg hp.le).map_iSup_of_continuousAt
            ENNReal.continuous_rpow_const.continuousAt
            (by rw [ENNReal.bot_eq_zero, ENNReal.zero_rpow_of_pos hp])).symm
      _ = F a ^ p := by rw [hsup a]
  have hlev : ∀ u : ℝ, ⨆ n : ℕ, μ {a | ENNReal.ofReal u < min (F a) n} =
      μ {a | ENNReal.ofReal u < F a} := by
    intro u
    have hm : Monotone fun n : ℕ => {a | ENNReal.ofReal u < min (F a) n} := by
      intro n m hnm a ha
      exact (show ENNReal.ofReal u < min (F a) m from
        lt_of_lt_of_le (show ENNReal.ofReal u < min (F a) n from ha)
          (min_le_min le_rfl (Nat.cast_le.mpr hnm)))
    rw [← hm.measure_iUnion]
    congr 1
    ext a
    simp only [mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      exact lt_of_lt_of_le hn (min_le_left _ _)
    · intro ha
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.ofReal_ne_top (r := u))
      exact ⟨n, lt_min ha hn⟩
  have hanti : ∀ n : ℕ, Measurable fun u : ℝ =>
      μ {a | ENNReal.ofReal u < min (F a) n} * ENNReal.ofReal (p * u ^ (p - 1)) := by
    intro n
    refine Measurable.mul (Antitone.measurable fun u v huv => measure_mono fun a ha => ?_) hw
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal huv) ha
  have hmono2 : Monotone fun (n : ℕ) (u : ℝ) =>
      μ {a | ENNReal.ofReal u < min (F a) n} * ENNReal.ofReal (p * u ^ (p - 1)) :=
    fun n m hnm u => by
      show μ {a | ENNReal.ofReal u < min (F a) n} * ENNReal.ofReal (p * u ^ (p - 1)) ≤
        μ {a | ENNReal.ofReal u < min (F a) m} * ENNReal.ofReal (p * u ^ (p - 1))
      gcongr ?_ * _
      exact measure_mono fun a ha =>
        (show ENNReal.ofReal u < min (F a) m from
          lt_of_lt_of_le (show ENNReal.ofReal u < min (F a) n from ha)
            (min_le_min le_rfl (Nat.cast_le.mpr hnm)))
  have hmeasp : ∀ n : ℕ, Measurable fun a => min (F a) n ^ p := fun n =>
    (hmeas n).pow_const p
  have hmonop : Monotone fun (n : ℕ) (a : α) => min (F a) n ^ p := fun n m hnm a =>
    ENNReal.rpow_le_rpow (min_le_min le_rfl (Nat.cast_le.mpr hnm)) hp.le
  calc ∫⁻ a, F a ^ p ∂μ = ∫⁻ a, ⨆ n : ℕ, min (F a) n ^ p ∂μ := by simp only [hsupp]
    _ = ⨆ n : ℕ, ∫⁻ a, min (F a) n ^ p ∂μ := lintegral_iSup hmeasp hmonop
    _ = ⨆ n : ℕ, ∫⁻ s in Ioi (0 : ℝ),
          μ {a | ENNReal.ofReal s < min (F a) n} * ENNReal.ofReal (p * s ^ (p - 1)) := by
        simp only [key]
    _ = ∫⁻ s in Ioi (0 : ℝ), ⨆ n : ℕ,
          μ {a | ENNReal.ofReal s < min (F a) n} * ENNReal.ofReal (p * s ^ (p - 1)) :=
        (lintegral_iSup hanti hmono2).symm
    _ = ∫⁻ s in Ioi (0 : ℝ), μ {a | ENNReal.ofReal s < F a} * ENNReal.ofReal (p * s ^ (p - 1)) := by
        simp only [← ENNReal.iSup_mul, hlev]

/-- Helper for (11.?) `eq:hp-maximal`: integrating the distribution estimate against
`p s^{p-1} ds` (Tonelli; `∫_0^{2|φ|} s^{p-2} ds = (2|φ|)^{p-1}/(p-1)`). -/
theorem s11_max_tonelli {φ : ℝ → ℝ} (hφ : Measurable φ) {p : ℝ} (hp : 1 < p) :
    ∫⁻ s in Ioi (0 : ℝ),
        (ENNReal.ofReal (4 / (s / 2)) *
          ∫⁻ x, {y : ℝ | s / 2 < |φ y|}.indicator (fun y => ENNReal.ofReal |φ y|) x) *
        ENNReal.ofReal (p * s ^ (p - 1)) ≤
      ENNReal.ofReal (4 * p * 2 ^ p / (p - 1)) * ∫⁻ x, ENNReal.ofReal |φ x| ^ p := by
  have hp0 : 0 < p := by linarith
  have hK : 0 ≤ 4 * p * 2 ^ p / (p - 1) := div_nonneg (by positivity) (by linarith)
  have hind : ∀ s : ℝ, Measurable ({y : ℝ | s / 2 < |φ y|}.indicator
      (fun y => ENNReal.ofReal |φ y|)) := fun s =>
    (ENNReal.measurable_ofReal.comp hφ.abs).indicator (measurableSet_lt measurable_const hφ.abs)
  -- Step A: put the `s`-factors inside the `x`-integral
  have hA : ∀ s ∈ Ioi (0 : ℝ),
      (ENNReal.ofReal (4 / (s / 2)) *
          ∫⁻ x, {y : ℝ | s / 2 < |φ y|}.indicator (fun y => ENNReal.ofReal |φ y|) x) *
        ENNReal.ofReal (p * s ^ (p - 1)) =
      ∫⁻ x, {y : ℝ | s / 2 < |φ y|}.indicator (fun y => ENNReal.ofReal |φ y|) x *
        ENNReal.ofReal (8 * p * s ^ (p - 2)) := by
    intro s hs
    have hs0 : 0 < s := hs
    rw [mul_comm (ENNReal.ofReal (4 / (s / 2))), mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), lintegral_mul_const _ (hind s)]
    congr 2
    rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add hs0, Real.rpow_one]
    field_simp
    ring
  -- joint measurability for Tonelli
  have hmeas : Measurable (Function.uncurry fun (s x : ℝ) =>
      {y : ℝ | s / 2 < |φ y|}.indicator (fun y => ENNReal.ofReal |φ y|) x *
        ENNReal.ofReal (8 * p * s ^ (p - 2))) := by
    have he : (fun z : ℝ × ℝ => {y : ℝ | z.1 / 2 < |φ y|}.indicator
        (fun y => ENNReal.ofReal |φ y|) z.2) =
        {z : ℝ × ℝ | z.1 / 2 < |φ z.2|}.indicator (fun z => ENNReal.ofReal |φ z.2|) := by
      funext z
      rfl
    have h1 : Measurable fun z : ℝ × ℝ => {y : ℝ | z.1 / 2 < |φ y|}.indicator
        (fun y => ENNReal.ofReal |φ y|) z.2 := by
      rw [he]
      exact (ENNReal.measurable_ofReal.comp (hφ.comp measurable_snd).abs).indicator
        (measurableSet_lt (measurable_fst.div_const 2) (hφ.comp measurable_snd).abs)
    exact h1.mul (ENNReal.measurable_ofReal.comp
      (measurable_const.mul (measurable_fst.pow_const _)))
  -- the elementary integral `∫_0^c s^{p-2} ds = c^{p-1}/(p-1)`
  have hI : ∀ c : ℝ, 0 < c →
      ∫⁻ s in Ioo 0 c, ENNReal.ofReal (s ^ (p - 2)) = ENNReal.ofReal (c ^ (p - 1) / (p - 1)) := by
    intro c hc
    have hii : IntervalIntegrable (fun s : ℝ => s ^ (p - 2)) volume 0 c :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    rw [← ofReal_integral_eq_lintegral_ofReal
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le hc.le).mp hii).mono_set Ioo_subset_Ioc_self)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact Real.rpow_nonneg hs.1.le _)]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hc.le,
      integral_rpow (Or.inl (by linarith)), show p - 2 + 1 = p - 1 by ring,
      Real.zero_rpow (by linarith : p - 1 ≠ 0), sub_zero]
  -- Step C: the inner `s`-integral for fixed `x`
  have hC : ∀ x : ℝ, ∫⁻ s in Ioi (0 : ℝ),
      {y : ℝ | s / 2 < |φ y|}.indicator (fun y => ENNReal.ofReal |φ y|) x *
        ENNReal.ofReal (8 * p * s ^ (p - 2)) ≤
      ENNReal.ofReal (4 * p * 2 ^ p / (p - 1)) * ENNReal.ofReal |φ x| ^ p := by
    intro x
    have hpt : ∀ s : ℝ, {y : ℝ | s / 2 < |φ y|}.indicator (fun y => ENNReal.ofReal |φ y|) x *
        ENNReal.ofReal (8 * p * s ^ (p - 2)) =
        (Iio (2 * |φ x|)).indicator (fun s => ENNReal.ofReal |φ x| *
          (ENNReal.ofReal (8 * p) * ENNReal.ofReal (s ^ (p - 2)))) s := by
      intro s
      by_cases h : s / 2 < |φ x|
      · rw [indicator_of_mem (show x ∈ {y : ℝ | s / 2 < |φ y|} from h),
          indicator_of_mem (show s ∈ Iio (2 * |φ x|) from mem_Iio.mpr (by linarith)),
          ENNReal.ofReal_mul (by positivity)]
      · rw [indicator_of_notMem (show x ∉ {y : ℝ | s / 2 < |φ y|} from h),
          indicator_of_notMem (show s ∉ Iio (2 * |φ x|) from fun h' => h (by
            have := mem_Iio.mp h'
            linarith)), zero_mul]
    rw [lintegral_congr hpt, lintegral_indicator measurableSet_Iio,
      Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rcases (abs_nonneg (φ x)).eq_or_lt with hv | hv
    · rw [← hv, ENNReal.ofReal_zero, zero_mul]
      exact zero_le
    rw [hI _ (by linarith), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (abs_nonneg _),
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le, ← ENNReal.ofReal_mul hK]
    refine le_of_eq (congrArg ENNReal.ofReal ?_)
    rw [Real.mul_rpow (by norm_num) hv.le, Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0),
      Real.rpow_sub_one hv.ne']
    have hp1 : p - 1 ≠ 0 := by linarith
    field_simp
    ring
  calc ∫⁻ s in Ioi (0 : ℝ),
        (ENNReal.ofReal (4 / (s / 2)) *
          ∫⁻ x, {y : ℝ | s / 2 < |φ y|}.indicator (fun y => ENNReal.ofReal |φ y|) x) *
        ENNReal.ofReal (p * s ^ (p - 1))
      = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ x,
          {y : ℝ | s / 2 < |φ y|}.indicator (fun y => ENNReal.ofReal |φ y|) x *
            ENNReal.ofReal (8 * p * s ^ (p - 2)) := setLIntegral_congr_fun measurableSet_Ioi hA
    _ = ∫⁻ x, ∫⁻ s in Ioi (0 : ℝ),
          {y : ℝ | s / 2 < |φ y|}.indicator (fun y => ENNReal.ofReal |φ y|) x *
            ENNReal.ofReal (8 * p * s ^ (p - 2)) := lintegral_lintegral_swap hmeas.aemeasurable
    _ ≤ ∫⁻ x, ENNReal.ofReal (4 * p * 2 ^ p / (p - 1)) * ENNReal.ofReal |φ x| ^ p :=
        lintegral_mono hC
    _ = ENNReal.ofReal (4 * p * 2 ^ p / (p - 1)) * ∫⁻ x, ENNReal.ofReal |φ x| ^ p :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- (11.?) `eq:hp-maximal`, `sec11-halfplane.tex:187` ([GCRF, Thm IV.2.8]): the maximal theorem
for the uncentered maximal function. -/
theorem eq_hp_maximal : ∃ A : ℝ → ℝ, IsMaximalConst A := by
  refine ⟨fun p => (4 * p * 2 ^ p / (p - 1)) ^ (1 / p), ?_⟩
  intro p hp φ hφ
  beta_reduce
  have hp0 : 0 < p := by linarith
  have hK : 0 ≤ 4 * p * 2 ^ p / (p - 1) := div_nonneg (by positivity) (by linarith)
  have hM : Measurable (maxFnU φ) := (s11_max_lsc φ).measurable
  have key : ∫⁻ t, maxFnU φ t ^ p ≤
      ENNReal.ofReal (4 * p * 2 ^ p / (p - 1)) * ∫⁻ t, ENNReal.ofReal |φ t| ^ p := by
    rw [s11_max_layer volume hM hp0]
    refine le_trans (setLIntegral_mono' measurableSet_Ioi fun s hs => ?_) (s11_max_tonelli hφ hp)
    gcongr
    have h := s11_max_distrib hφ (half_pos (mem_Ioi.mp hs))
    rwa [show 2 * (s / 2) = s by ring] at h
  calc (∫⁻ t, maxFnU φ t ^ p) ^ (1 / p)
      ≤ (ENNReal.ofReal (4 * p * 2 ^ p / (p - 1)) * ∫⁻ t, ENNReal.ofReal |φ t| ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow key (by positivity)
    _ = ENNReal.ofReal (4 * p * 2 ^ p / (p - 1)) ^ (1 / p) *
          (∫⁻ t, ENNReal.ofReal |φ t| ^ p) ^ (1 / p) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = ENNReal.ofReal ((4 * p * 2 ^ p / (p - 1)) ^ (1 / p)) *
          (∫⁻ t, ENNReal.ofReal |φ t| ^ p) ^ (1 / p) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hK (by positivity)]

/-- Helper: `|t|^β` is interval integrable for `β > -1`. -/
theorem hp_abs_rpow_intervalIntegrable {β : ℝ} (hβ : -1 < β) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => |t| ^ β) volume a b := by
  have hpos : ∀ c : ℝ, 0 ≤ c → IntervalIntegrable (fun t : ℝ => |t| ^ β) volume 0 c := by
    intro c hc
    refine (intervalIntegral.intervalIntegrable_rpow' hβ).congr_ae ?_
    refine (ae_restrict_iff' measurableSet_uIoc).mpr (ae_of_all _ fun t ht => ?_)
    rw [uIoc_of_le hc] at ht
    show t ^ β = |t| ^ β
    rw [abs_of_pos ht.1]
  have h0 : ∀ c : ℝ, IntervalIntegrable (fun t : ℝ => |t| ^ β) volume 0 c := by
    intro c
    rcases le_total 0 c with hc | hc
    · exact hpos c hc
    · have := hpos (-c) (by linarith)
      rw [IntervalIntegrable.iff_comp_neg] at this
      simpa [abs_neg] using this
  exact (h0 a).symm.trans (h0 b)

theorem hp_power_pos {α : ℝ} (hα : 0 < α) {x : ℝ} (hx : 0 ≤ x) : x * |x| ^ (α - 1) = x ^ α := by
  rw [abs_of_nonneg hx]
  rcases hx.eq_or_lt with h | h
  · rw [← h, Real.zero_rpow hα.ne', zero_mul]
  · rw [Real.rpow_sub_one h.ne']
    field_simp

theorem hp_power_neg {α : ℝ} (hα : 0 < α) {x : ℝ} (hx : x ≤ 0) :
    x * |x| ^ (α - 1) = -(-x) ^ α := by
  rw [abs_of_nonpos hx]
  rcases hx.eq_or_lt with h | h
  · rw [h, neg_zero, Real.zero_rpow hα.ne', zero_mul, neg_zero]
  · rw [Real.rpow_sub_one (by linarith : -x ≠ 0)]
    have : -x ≠ 0 := by linarith
    have hx0 : x ≠ 0 := h.ne
    field_simp

/-- Helper: `∫₀ˣ α |t|^{α-1} dt = x |x|^{α-1}`. -/
theorem hp_power_integral {α : ℝ} (hα : 0 < α) (x : ℝ) :
    ∫ t in (0 : ℝ)..x, α * |t| ^ (α - 1) = x * |x| ^ (α - 1) := by
  have hβ : -1 < α - 1 := by linarith
  have hpos : ∀ c : ℝ, 0 ≤ c → ∫ t in (0 : ℝ)..c, α * |t| ^ (α - 1) = c ^ α := by
    intro c hc
    rw [intervalIntegral.integral_const_mul]
    have : ∫ t in (0 : ℝ)..c, |t| ^ (α - 1) = ∫ t in (0 : ℝ)..c, t ^ (α - 1) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hc] at ht
      simp only [abs_of_nonneg ht.1]
    rw [this, integral_rpow (Or.inl hβ), sub_add_cancel, Real.zero_rpow hα.ne', sub_zero]
    field_simp
  rcases le_total 0 x with hx | hx
  · rw [hpos x hx, hp_power_pos hα hx]
  · have h1 : ∫ t in (0 : ℝ)..x, α * |t| ^ (α - 1) = -∫ t in (0 : ℝ)..(-x), α * |t| ^ (α - 1) := by
      have := intervalIntegral.integral_comp_neg (a := 0) (b := -x) (fun t => α * |t| ^ (α - 1))
      simp only [abs_neg, neg_neg, neg_zero] at this
      rw [this, intervalIntegral.integral_symm]
    rw [h1, hpos (-x) (by linarith), hp_power_neg hα hx]

theorem hp_power_integrableOn {α : ℝ} (hα : 0 < α) {a b : ℝ} (hab : a ≤ b) :
    IntegrableOn (fun t : ℝ => α * |t| ^ (α - 1)) (Icc a b) :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
    ((hp_abs_rpow_intervalIntegrable (by linarith) a b).const_mul α)

theorem hp_power_setIntegral_le {α : ℝ} (hα : 0 < α) {a b : ℝ} (hab : a ≤ b) {F : Set ℝ}
    (hF : F ⊆ Icc a b) (hFm : MeasurableSet F) {U : ℝ}
    (hU : ∀ t ∈ F, α * |t| ^ (α - 1) ≤ U) :
    ∫ x in F, α * |x| ^ (α - 1) ≤ (volume F).toReal * U := by
  have hfin : volume F ≠ ∞ := ((measure_mono hF).trans_lt measure_Icc_lt_top).ne
  calc ∫ x in F, α * |x| ^ (α - 1) ≤ ∫ _ in F, U :=
        setIntegral_mono_on ((hp_power_integrableOn hα hab).mono_set hF)
          (integrableOn_const hfin) hFm hU
    _ = (volume F).toReal * U := by rw [setIntegral_const, smul_eq_mul, measureReal_def]

theorem hp_power_setIntegral_ge {α : ℝ} (hα : 0 < α) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hsub : Icc c d ⊆ Icc a b) {m : ℝ}
    (hm : ∀ t ∈ Icc c d, t ≠ 0 → m ≤ α * |t| ^ (α - 1)) :
    (d - c) * m ≤ ∫ x in Icc a b, α * |x| ^ (α - 1) := by
  have hnn : ∀ t : ℝ, 0 ≤ α * |t| ^ (α - 1) := fun t =>
    mul_nonneg hα.le (Real.rpow_nonneg (abs_nonneg _) _)
  calc (d - c) * m = ∫ _ in Icc c d, m := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith)]
    _ ≤ ∫ x in Icc c d, α * |x| ^ (α - 1) := by
        refine setIntegral_mono_on_ae (integrableOn_const measure_Icc_lt_top.ne)
          ((hp_power_integrableOn hα hab).mono_set hsub) measurableSet_Icc ?_
        filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht0 ht using hm t ht ht0
    _ ≤ ∫ x in Icc a b, α * |x| ^ (α - 1) :=
        setIntegral_mono_set (hp_power_integrableOn hα hab) (ae_of_all _ hnn) hsub.eventuallyLE

theorem hp_power_integral_symm {α : ℝ} (hα : 0 < α) {s : ℝ} (hs : 0 ≤ s) :
    ∫ x in Icc (-s) s, α * |x| ^ (α - 1) = 2 * s ^ α := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => α * |t| ^ (α - 1)) volume a b :=
    fun a b => (hp_abs_rpow_intervalIntegrable (by linarith) a b).const_mul α
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals (hint (-s) 0) (hint 0 s),
    intervalIntegral.integral_symm, hp_power_integral hα, hp_power_integral hα,
    hp_power_neg hα (by linarith), hp_power_pos hα hs, neg_neg]
  ring

/-- Helper: the power weight `α |t|^{α-1}` is an `A_∞` weight. -/
theorem hp_power_ainfty {α : ℝ} (hα : 0 < α) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ a b : ℝ, a < b → ∀ E ⊆ Icc a b, MeasurableSet E →
      ∫ x in E, α * |x| ^ (α - 1) ≤
        C * ((volume E).toReal / (b - a)) ^ δ * ∫ x in Icc a b, α * |x| ^ (α - 1) := by
  have hnn : ∀ t : ℝ, 0 ≤ α * |t| ^ (α - 1) := fun t =>
    mul_nonneg hα.le (Real.rpow_nonneg (abs_nonneg _) _)
  -- comparability: sup on `E` against inf on a quarter of `[a, b]`
  have core : ∀ a b : ℝ, a < b → ∀ E ⊆ Icc a b, MeasurableSet E → ∀ U m K c d : ℝ,
      0 ≤ K → 0 ≤ m → c ≤ d → Icc c d ⊆ Icc a b → b - a ≤ 4 * (d - c) →
      (∀ t ∈ E, α * |t| ^ (α - 1) ≤ U) →
      (∀ t ∈ Icc c d, t ≠ 0 → m ≤ α * |t| ^ (α - 1)) → U ≤ K * m →
      ∫ x in E, α * |x| ^ (α - 1) ≤
        4 * K * ((volume E).toReal / (b - a)) * ∫ x in Icc a b, α * |x| ^ (α - 1) := by
    intro a b hab E hE hEm U m K c d hK hm0 hcd hsub hL hU hm hUK
    have h1 := hp_power_setIntegral_le hα hab.le hE hEm hU
    have h2 := hp_power_setIntegral_ge hα hab.le hcd hsub hm
    have he : 0 ≤ (volume E).toReal := ENNReal.toReal_nonneg
    have hL0 : 0 < b - a := by linarith
    have hL0' := hL0.ne'
    have h3 : (b - a) * m ≤ 4 * ∫ x in Icc a b, α * |x| ^ (α - 1) := by
      have := mul_le_mul_of_nonneg_right hL hm0
      linarith
    calc ∫ x in E, α * |x| ^ (α - 1) ≤ (volume E).toReal * U := h1
      _ ≤ (volume E).toReal * (K * m) := mul_le_mul_of_nonneg_left hUK he
      _ = K * ((volume E).toReal / (b - a)) * ((b - a) * m) := by field_simp
      _ ≤ K * ((volume E).toReal / (b - a)) * (4 * ∫ x in Icc a b, α * |x| ^ (α - 1)) :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg hK (div_nonneg he hL0.le))
      _ = _ := by ring
  rcases le_or_gt 1 α with h1α | h1α
  · -- `α ≥ 1`: the weight is increasing in `|t|`
    refine ⟨4 * 2 ^ (α - 1), 1, by positivity, one_pos, fun a b hab E hE hEm => ?_⟩
    rw [Real.rpow_one]
    have hβ : 0 ≤ α - 1 := by linarith
    rcases le_or_gt (-a) b with hba | hba
    · have hb : 0 < b := by linarith
      refine core a b hab E hE hEm (α * b ^ (α - 1)) (α * (b / 2) ^ (α - 1)) (2 ^ (α - 1))
        (max a (b / 2)) b (by positivity) (mul_nonneg hα.le (Real.rpow_nonneg (by linarith) _))
        (max_le hab.le (by linarith)) (Icc_subset_Icc (le_max_left _ _) le_rfl) ?_ ?_ ?_ ?_
      · have := max_le (show a ≤ b - (b - a) / 4 by linarith)
          (show b / 2 ≤ b - (b - a) / 4 by linarith)
        linarith
      · intro t ht
        have ht' := hE ht
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg t)
          (abs_le.mpr ⟨by linarith [ht'.1], ht'.2⟩) hβ) hα.le
      · intro t ht _
        have h2 : b / 2 ≤ t := (max_le_iff.mp ht.1).2
        rw [abs_of_pos (by linarith : 0 < t)]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) h2 hβ) hα.le
      · have : (0 : ℝ) < 2 ^ (α - 1) := by positivity
        rw [Real.div_rpow hb.le zero_le_two]
        field_simp
        rfl
    · have ha : 0 < -a := by linarith
      refine core a b hab E hE hEm (α * (-a) ^ (α - 1)) (α * (-a / 2) ^ (α - 1)) (2 ^ (α - 1))
        a (min b (a / 2)) (by positivity) (mul_nonneg hα.le (Real.rpow_nonneg (by linarith) _))
        (le_min hab.le (by linarith)) (Icc_subset_Icc le_rfl (min_le_left _ _)) ?_ ?_ ?_ ?_
      · have := le_min (show a + (b - a) / 4 ≤ b by linarith)
          (show a + (b - a) / 4 ≤ a / 2 by linarith)
        linarith
      · intro t ht
        have ht' := hE ht
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg t)
          (abs_le.mpr ⟨by linarith [ht'.1], by linarith [ht'.2]⟩) hβ) hα.le
      · intro t ht _
        have h2 : t ≤ a / 2 := (le_min_iff.mp ht.2).2
        rw [abs_of_neg (by linarith : t < 0)]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) (by linarith) hβ) hα.le
      · have : (0 : ℝ) < 2 ^ (α - 1) := by positivity
        rw [Real.div_rpow ha.le zero_le_two]
        field_simp
        rfl
  · -- `α < 1`: the weight is decreasing in `|t|`
    refine ⟨8 / α, α, by positivity, hα, fun a b hab E hE hEm => ?_⟩
    have hβ : α - 1 ≤ 0 := by linarith
    have hL0 : 0 < b - a := by linarith
    have hfin : volume E ≠ ∞ := ((measure_mono hE).trans_lt measure_Icc_lt_top).ne
    have he0 : 0 ≤ (volume E).toReal := ENNReal.toReal_nonneg
    have heL : (volume E).toReal ≤ b - a := by
      have := measure_mono (μ := volume) hE
      rw [Real.volume_Icc] at this
      exact ENNReal.toReal_le_of_le_ofReal hL0.le this
    have hr0 : 0 ≤ (volume E).toReal / (b - a) := div_nonneg he0 hL0.le
    have hr1 : (volume E).toReal / (b - a) ≤ 1 := (div_le_one hL0).mpr heL
    have hI0 : 0 ≤ ∫ x in Icc a b, α * |x| ^ (α - 1) :=
      setIntegral_nonneg measurableSet_Icc fun t _ => hnn t
    have far : ∫ x in E, α * |x| ^ (α - 1) ≤
          4 * 2 * ((volume E).toReal / (b - a)) * ∫ x in Icc a b, α * |x| ^ (α - 1) →
        ∫ x in E, α * |x| ^ (α - 1) ≤
          8 / α * ((volume E).toReal / (b - a)) ^ α * ∫ x in Icc a b, α * |x| ^ (α - 1) := by
      intro h
      refine h.trans (mul_le_mul_of_nonneg_right ?_ hI0)
      have h8 : 8 ≤ 8 / α := by rw [le_div_iff₀ hα]; linarith
      have hrr : (volume E).toReal / (b - a) ≤ ((volume E).toReal / (b - a)) ^ α := by
        simpa using Real.rpow_le_rpow_of_exponent_ge' hr0 hr1 hα.le h1α.le
      nlinarith [Real.rpow_nonneg hr0 α]
    have two_le : ∀ x y : ℝ, 0 < x → 0 < y → y ≤ 2 * x →
        α * x ^ (α - 1) ≤ 2 * (α * y ^ (α - 1)) := by
      intro x y hx hy hyx
      have h2a : (2 * x) ^ (α - 1) ≤ y ^ (α - 1) := Real.rpow_le_rpow_of_nonpos hy hyx hβ
      rw [Real.mul_rpow zero_le_two hx.le] at h2a
      have h2 : (2 : ℝ) ^ (-1 : ℝ) ≤ 2 ^ (α - 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      rw [Real.rpow_neg_one] at h2
      have hxpos : 0 ≤ x ^ (α - 1) := Real.rpow_nonneg hx.le _
      have : x ^ (α - 1) ≤ 2 * y ^ (α - 1) := by nlinarith
      nlinarith
    rcases le_or_gt (b - a) a with hfa | hfa
    · -- far to the right of `0`
      have ha : 0 < a := by linarith
      apply far
      refine core a b hab E hE hEm (α * a ^ (α - 1)) (α * b ^ (α - 1)) 2 a b zero_le_two
        (mul_nonneg hα.le (Real.rpow_nonneg (by linarith) _)) hab.le le_rfl (by linarith) ?_ ?_
        (two_le a b ha (by linarith) (by linarith))
      · intro t ht
        have ht' := hE ht
        rw [abs_of_pos (by linarith [ht'.1])]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha ht'.1 hβ) hα.le
      · intro t ht _
        rw [abs_of_pos (by linarith [ht.1])]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by linarith [ht.1]) ht.2 hβ) hα.le
    rcases le_or_gt (b - a) (-b) with hfb | hfb
    · -- far to the left of `0`
      have hb : 0 < -b := by linarith
      apply far
      refine core a b hab E hE hEm (α * (-b) ^ (α - 1)) (α * (-a) ^ (α - 1)) 2 a b zero_le_two
        (mul_nonneg hα.le (Real.rpow_nonneg (by linarith) _)) hab.le le_rfl (by linarith) ?_ ?_
        (two_le (-b) (-a) hb (by linarith) (by linarith))
      · intro t ht
        have ht' := hE ht
        rw [abs_of_neg (by linarith [ht'.2])]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hb (by linarith [ht'.2]) hβ) hα.le
      · intro t ht _
        rw [abs_of_neg (by linarith [ht.2])]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by linarith [ht.2]) (by linarith [ht.1]) hβ) hα.le
    -- near `0`: `|t| < 2 (b - a)` on `[a, b]`
    set e := (volume E).toReal with he_def
    rcases he0.eq_or_lt with he | he
    · have h0 : volume E = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).mp he.symm with h | h
        · exact h
        · exact absurd h hfin
      rw [setIntegral_measure_zero _ h0]
      exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hr0 _)) hI0
    have hs : 0 < e / 2 := by linarith
    set s := e / 2 with hs_def
    have hes : e = 2 * s := by rw [hs_def]; ring
    have hSm : MeasurableSet (Icc (-s) s) := measurableSet_Icc
    have hsplit := integral_inter_add_sdiff hSm ((hp_power_integrableOn hα hab.le).mono_set hE)
    have hA : ∫ x in E ∩ Icc (-s) s, α * |x| ^ (α - 1) ≤ 2 * s ^ α := by
      rw [← hp_power_integral_symm hα hs.le]
      exact setIntegral_mono_set (hp_power_integrableOn hα (by linarith))
        (ae_of_all _ hnn) inter_subset_right.eventuallyLE
    have hB : ∫ x in E \ Icc (-s) s, α * |x| ^ (α - 1) ≤
        (volume (E \ Icc (-s) s)).toReal * (α * s ^ (α - 1)) := by
      refine hp_power_setIntegral_le hα hab.le (sdiff_subset.trans hE) (hEm.diff hSm)
        fun t ht => ?_
      have : s < |t| := by
        by_contra h
        exact ht.2 (abs_le.mp (not_lt.mp h))
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hs this.le hβ) hα.le
    have hvol : (volume (E \ Icc (-s) s)).toReal ≤ e :=
      ENNReal.toReal_mono hfin (measure_mono sdiff_subset)
    have hsa : 0 ≤ s ^ α := Real.rpow_nonneg hs.le _
    have hE_le : ∫ x in E, α * |x| ^ (α - 1) ≤ 4 * s ^ α := by
      have hB' : (volume (E \ Icc (-s) s)).toReal * (α * s ^ (α - 1)) ≤
          e * (α * s ^ (α - 1)) :=
        mul_le_mul_of_nonneg_right hvol (mul_nonneg hα.le (Real.rpow_nonneg hs.le _))
      have he2 : e * (α * s ^ (α - 1)) = 2 * α * s ^ α := by
        have := hs.ne'
        rw [hes, Real.rpow_sub_one hs.ne']
        field_simp
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - α) hsa
      linarith
    have hL2 : 0 < 2 * (b - a) := by linarith
    have hI_ge : (b - a) * (α * (2 * (b - a)) ^ (α - 1)) ≤
        ∫ x in Icc a b, α * |x| ^ (α - 1) := by
      refine hp_power_setIntegral_ge hα hab.le hab.le subset_rfl fun t ht ht0 => ?_
      have h1 : |t| ≤ 2 * (b - a) := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (abs_pos.mpr ht0) h1 hβ) hα.le
    have hI_ge' : α * (2 * (b - a)) ^ α / 2 ≤ ∫ x in Icc a b, α * |x| ^ (α - 1) := by
      refine Eq.trans_le ?_ hI_ge
      have := hL0.ne'
      rw [Real.rpow_sub_one hL2.ne']
      field_simp
    have hkey : 4 * s ^ α ≤ 4 * ((e / (b - a)) ^ α * (2 * (b - a)) ^ α) := by
      rw [← Real.mul_rpow hr0 hL2.le]
      have h2e : e / (b - a) * (2 * (b - a)) = 2 * e := by
        have := hL0.ne'
        field_simp
      rw [h2e]
      have := Real.rpow_le_rpow hs.le (by linarith : s ≤ 2 * e) hα.le
      linarith
    have hα0 := hα.ne'
    calc ∫ x in E, α * |x| ^ (α - 1) ≤ 4 * s ^ α := hE_le
      _ ≤ 4 * ((e / (b - a)) ^ α * (2 * (b - a)) ^ α) := hkey
      _ = 8 / α * (e / (b - a)) ^ α * (α * (2 * (b - a)) ^ α / 2) := by field_simp; ring
      _ ≤ 8 / α * (e / (b - a)) ^ α * ∫ x in Icc a b, α * |x| ^ (α - 1) :=
          mul_le_mul_of_nonneg_left hI_ge' (mul_nonneg (by positivity) (Real.rpow_nonneg hr0 _))

/-- Example 7.12 `ex:power`, `sec07-transfer.tex:566` (stated here at w3's request, since `SQS(ℝ)`
is defined in this file): the boundary map `x ↦ x |x|^{α-1}` of `F_α` (`powerMap` of
`S07_Transfer`) is strongly quasisymmetric, its derivative being a power weight. -/
theorem ex_power_sqs {α : ℝ} (hα : 0 < α) :
    (∀ x : ℝ, powerMap α (x : ℂ) = ((x * |x| ^ (α - 1) : ℝ) : ℂ)) ∧
      IsSQS fun x => x * |x| ^ (α - 1) := by
  have hβ : -1 < α - 1 := by linarith
  refine ⟨fun x => ?_, ?_⟩
  · unfold powerMap
    rw [Complex.norm_real, Real.norm_eq_abs]
    rcases le_or_gt 0 x with hx | hx
    · rw [Complex.arg_ofReal_of_nonneg hx, hp_power_pos hα hx, abs_of_nonneg hx]
      simp
    · rw [Complex.arg_ofReal_of_neg hx, hp_power_neg hα hx.le, abs_of_neg hx,
        Complex.exp_pi_mul_I]
      push_cast
      ring
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => α * |t| ^ (α - 1)) volume a b :=
    fun a b => (hp_abs_rpow_intervalIntegrable hβ a b).const_mul α
  have hrep : (fun x : ℝ => x * |x| ^ (α - 1)) = fun x => ∫ t in (0 : ℝ)..x, α * |t| ^ (α - 1) :=
    funext fun x => (hp_power_integral hα x).symm
  have hcont : Continuous fun x : ℝ => x * |x| ^ (α - 1) := by
    rw [hrep]
    exact intervalIntegral.continuous_primitive hint 0
  have hmono : StrictMono fun x : ℝ => x * |x| ^ (α - 1) := by
    intro x y hxy
    simp only
    rcases le_total 0 x with hx | hx
    · rw [hp_power_pos hα hx, hp_power_pos hα (hx.trans hxy.le)]
      exact Real.rpow_lt_rpow hx hxy hα
    · rcases le_total 0 y with hy | hy
      · rw [hp_power_neg hα hx, hp_power_pos hα hy]
        have h1 : 0 ≤ (-x) ^ α := Real.rpow_nonneg (by linarith) _
        have h2 : 0 ≤ y ^ α := Real.rpow_nonneg hy _
        rcases hx.lt_or_eq with hx' | hx'
        · have : 0 < (-x) ^ α := Real.rpow_pos_of_pos (by linarith) _
          linarith
        · have : 0 < y ^ α := Real.rpow_pos_of_pos (by linarith) _
          linarith
      · rw [hp_power_neg hα hx, hp_power_neg hα hy]
        have := Real.rpow_lt_rpow (by linarith : 0 ≤ -y) (by linarith : -y < -x) hα
        linarith
  have htop : Tendsto (fun x : ℝ => x * |x| ^ (α - 1)) atTop atTop :=
    (tendsto_rpow_atTop hα).congr' ((eventually_ge_atTop 0).mono fun x hx =>
      (hp_power_pos hα hx).symm)
  have hbot : Tendsto (fun x : ℝ => x * |x| ^ (α - 1)) atBot atBot :=
    (tendsto_neg_atTop_atBot.comp ((tendsto_rpow_atTop hα).comp tendsto_neg_atBot_atTop)).congr'
      ((eventually_le_atBot 0).mono fun x hx => (hp_power_neg hα hx).symm)
  have hloc : LocallyIntegrable fun t : ℝ => α * |t| ^ (α - 1) := by
    rw [locallyIntegrable_iff]
    intro K hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hR
    have hR' : K ⊆ Icc (-max R 0) (max R 0) :=
      hR.trans (Icc_subset_Icc (neg_le_neg (le_max_left _ _)) (le_max_left _ _))
    refine IntegrableOn.mono_set ?_ hR'
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by
      linarith [le_max_right R 0])).mp (hint _ _)
  obtain ⟨C, δ, hC, hδ, hA⟩ := hp_power_ainfty hα
  refine ⟨fun t => α * |t| ^ (α - 1), hmono, hcont, hcont.surjective htop hbot,
    ⟨fun t => mul_nonneg hα.le (Real.rpow_nonneg (abs_nonneg _) _), hloc, C, δ, hC, hδ, hA⟩,
    fun x => ?_⟩
  simp only [zero_mul, zero_add]
  exact (hp_power_integral hα x).symm

/-- `sec11-halfplane.tex:190`: for uniformly continuous `φ`, `ω_φ` is finite, nondecreasing and
tends to `0` as `r → 0`. -/
theorem hp_modCont {φ : ℝ → ℝ} (hφ : UniformContinuous φ) :
    (∀ r : ℝ, 0 ≤ r → BddAbove {d : ℝ | ∃ a b : ℝ, |b - a| ≤ r ∧ d = |φ b - φ a|}) ∧
      MonotoneOn (modCont φ) (Ici 0) ∧ Tendsto (modCont φ) (𝓝[>] 0) (𝓝 0) := by
  have hbdd : ∀ r : ℝ, 0 ≤ r → BddAbove {d : ℝ | ∃ a b : ℝ, |b - a| ≤ r ∧ d = |φ b - φ a|} := by
    intro r hr
    obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuous_iff.mp hφ 1 one_pos
    set n : ℕ := ⌈r / δ⌉₊ + 1 with hn
    have hn0 : (0 : ℝ) < n := by positivity
    have hrn : r / n < δ := by
      rw [div_lt_iff₀ hn0]
      have h1 : r / δ ≤ ⌈r / δ⌉₊ := Nat.le_ceil _
      have h2 : r ≤ δ * ⌈r / δ⌉₊ := by rwa [div_le_iff₀ hδ, mul_comm] at h1
      push_cast [hn]
      nlinarith
    refine ⟨n, ?_⟩
    rintro d ⟨a, b, hab, rfl⟩
    set x : ℕ → ℝ := fun k => a + k * ((b - a) / n)
    have hx0 : x 0 = a := by simp [x]
    have hxn : x n = b := by simp only [x]; field_simp; ring
    have hstep : ∀ k, |φ (x (k + 1)) - φ (x k)| ≤ 1 := by
      intro k
      have : dist (x (k + 1)) (x k) < δ := by
        rw [Real.dist_eq]
        simp only [x]
        push_cast
        rw [show a + (k + 1) * ((b - a) / n) - (a + k * ((b - a) / n)) = (b - a) / n by ring,
          abs_div, abs_of_pos hn0]
        calc |b - a| / n ≤ r / n := by gcongr
          _ < δ := hrn
      exact (hU this).le
    calc |φ b - φ a| = |∑ k ∈ Finset.range n, (φ (x (k + 1)) - φ (x k))| := by
          rw [Finset.sum_range_sub (fun k => φ (x k)), hx0, hxn]
      _ ≤ ∑ k ∈ Finset.range n, |φ (x (k + 1)) - φ (x k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun k _ => hstep k
      _ = n := by simp
  have hne : ∀ r : ℝ, 0 ≤ r → (0 : ℝ) ∈ {d : ℝ | ∃ a b : ℝ, |b - a| ≤ r ∧ d = |φ b - φ a|} :=
    fun r hr => ⟨0, 0, by simpa using hr, by simp⟩
  refine ⟨hbdd, fun r hr s hs hrs => ?_, ?_⟩
  · exact csSup_le_csSup (hbdd s hs) ⟨0, hne r hr⟩
      fun d ⟨a, b, hab, hd⟩ => ⟨a, b, hab.trans hrs, hd⟩
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuous_iff.mp hφ (ε / 2) (by positivity)
    refine ⟨δ, hδ, fun r hr hrd => ?_⟩
    have hr0 : 0 < r := hr
    rw [Real.dist_eq, sub_zero] at hrd ⊢
    rw [abs_lt] at hrd
    have hle : modCont φ r ≤ ε / 2 := by
      refine csSup_le ⟨0, hne r hr0.le⟩ ?_
      rintro d ⟨a, b, hab, rfl⟩
      exact (hU (by rw [Real.dist_eq]; linarith)).le
    have hge : 0 ≤ modCont φ r := le_csSup (hbdd r hr0.le) (hne r hr0.le)
    rw [abs_of_nonneg hge]
    linarith

/-- Helper for `hp_wmuc_cor10`: an `SQS` density has a measurable representative that is a.e.
equal to it (`s11_comp_meas`, keeping the a.e. equality). -/
theorem s11_c10_meas {h ω₀ : ℝ → ℝ} (hω : IsSQSWith h ω₀) :
    ∃ ω : ℝ → ℝ, Measurable ω ∧ ω₀ =ᵐ[volume] ω ∧ IsSQSWith h ω := by
  obtain ⟨hmono, hcont, hsurj, ⟨hpos, hli, C, δ, hC, hδ, hA⟩, hF⟩ := hω
  obtain ⟨g, hgm, hg⟩ := hli.aestronglyMeasurable.aemeasurable
  obtain ⟨f, hfm, hf0, hfeq⟩ : ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ ω₀ =ᵐ[volume] f :=
    ⟨fun x => max (g x) 0, hgm.max measurable_const, fun x => le_max_right _ _,
      hg.mono fun x hx => by
        show ω₀ x = max (g x) 0
        rw [← hx, max_eq_left (hpos x)]⟩
  have hsi : ∀ s : Set ℝ, ∫ x in s, ω₀ x = ∫ x in s, f x := fun s =>
    integral_congr_ae (ae_restrict_of_ae hfeq)
  refine ⟨f, hfm, hfeq, hmono, hcont, hsurj, ⟨hf0, hli.congr hfeq, C, δ, hC, hδ,
    fun a b hab E hE hEm => ?_⟩, fun x => ?_⟩
  · rw [← hsi E, ← hsi (Icc a b)]
    exact hA a b hab E hE hEm
  · rw [hF x, intervalIntegral.integral_congr_ae (hfeq.mono fun t ht _ => ht)]

/-- Helper for `hp_wmuc_cor10`: `realMeanOsc` in the form used by `s07_ssi_osc_uc`. -/
theorem s11_c10_osc_eq (u : ℝ → ℝ) (a b : ℝ) :
    realMeanOsc u a b = (∫ t in a..b, |u t - (∫ s in a..b, u s) / (b - a)|) / (b - a) := by
  unfold realMeanOsc intervalMean
  simp only [div_eq_inv_mul]

/-- Helper for `hp_wmuc_cor10`: `VMO(ℝ)` is invariant under a.e. equality. -/
theorem s11_c10_vmo_congr {u v : ℝ → ℝ} (huv : u =ᵐ[volume] v) (hu : IsVMOReal u) :
    IsVMOReal v := by
  have hm : ∀ a b : ℝ, intervalMean u a b = intervalMean v a b := fun a b => by
    unfold intervalMean
    rw [intervalIntegral.integral_congr_ae (huv.mono fun x hx _ => hx)]
  have ho : ∀ a b : ℝ, realMeanOsc u a b = realMeanOsc v a b := fun a b => by
    unfold realMeanOsc
    rw [hm a b, intervalIntegral.integral_congr_ae (huv.mono fun x hx _ => by rw [hx])]
  obtain ⟨⟨hli, C, hC⟩, hv⟩ := hu
  refine ⟨⟨hli.congr huv, C, fun a b hab => ?_⟩, fun ε hε => ?_⟩
  · rw [← ho]
    exact hC a b hab
  · obtain ⟨δ, hδ, hδv⟩ := hv ε hε
    refine ⟨δ, hδ, fun a b hab hba => ?_⟩
    rw [← ho]
    exact hδv a b hab hba

/-- Helper for `hp_wmuc_cor10`: uniform continuity in the one-sided form `hGu` of
`s07_ssi_osc_uc`: `G b - G a ≤ ε` whenever `0 ≤ b - a ≤ δ`. -/
theorem s11_c10_uc {G : ℝ → ℝ} (hG : UniformContinuous G) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a ≤ b → b - a ≤ δ → G b - G a ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuous_iff.mp hG ε hε
  refine ⟨δ / 2, by positivity, fun a b hab hba => ?_⟩
  have h1 := @hδu b a (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
  rw [Real.dist_eq] at h1
  exact (le_abs_self _).trans h1.le

/-- `sec11-halfplane.tex:928` (cited from [WMUC, Corollary 10(1)]): if `h ∈ SS(ℝ)` and `h⁻¹` is
uniformly continuous, then `h⁻¹ ∈ SS(ℝ)`. -/
theorem hp_wmuc_cor10 {h : ℝ ≃ₜ ℝ} (hs : IsSS h) (huc : UniformContinuous h.symm) :
    IsSS h.symm := by
  obtain ⟨ω₀, hω₀, -, hvmo₀⟩ := hs
  obtain ⟨ω, hm, heq, hω⟩ := s11_c10_meas hω₀
  have hpos := hp_sqs_pos_ae hω
  have hvmo : IsVMOReal fun x => Real.log (ω x) := s11_c10_vmo_congr (heq.fun_comp Real.log) hvmo₀
  have hmono : StrictMono h := hω.1
  have hui : ∀ a b : ℝ, IntegrableOn ω (Icc a b) := fun a b =>
    hω.2.2.2.1.2.1.integrableOn_isCompact isCompact_Icc
  have hli : ∀ a b : ℝ, IntegrableOn (fun t => Real.log (ω t)) (Icc a b) := fun a b =>
    hvmo.1.1.integrableOn_isCompact isCompact_Icc
  have hv : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a < b → b - a ≤ δ →
      (∫ t in a..b, |Real.log (ω t) - (∫ s in a..b, Real.log (ω s)) / (b - a)|) / (b - a) ≤ ε :=
    fun ε hε => by
      obtain ⟨δ, hδ, hδv⟩ := hvmo.2 ε hε
      refine ⟨δ / 2, by positivity, fun a b hab hba => ?_⟩
      rw [← s11_c10_osc_eq]
      exact hδv a b hab (by linarith)
  have hGmono : StrictMono h.symm := fun x y hxy =>
    hmono.lt_iff_lt.mp (by rw [h.apply_symm_apply, h.apply_symm_apply]; exact hxy)
  have hosc := s07_ssi_osc_uc hmono h.continuous hui hω.2.2.2.2 hpos hli hv hGmono
    h.symm.continuous h.apply_symm_apply h.symm_apply_apply (s11_c10_uc huc)
  have hω' : IsSQSWith h.symm fun y => (ω (h.symm y))⁻¹ :=
    ⟨hGmono, h.symm.continuous, h.symm.surjective, s11_symm_ainfty hω hm hpos,
      s11_symm_formula hω hm hpos⟩
  refine ⟨fun y => (ω (h.symm y))⁻¹, hω', hp_sqs_pos_ae hω', hp_sqs_logBMO hω', fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hδv⟩ := hosc (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun a b hab hba => ?_⟩
  rw [s11_c10_osc_eq]
  have h1 := hδv a b hab hba.le
  simp only [one_div] at h1
  linarith

/-! ## Schwarzian measures -/

/-- Helper: the inverse Cayley map `ζ ↦ i(1+ζ)/(1-ζ)` is a conformal map of `𝔻` onto `ℍ`. -/
theorem hp_isConformalOnto_cayleyInv : IsConformalOnto cayleyInv unitDisc upperHalf := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    have hd := cayleyInv_den_ne_zero (mem_ball_zero_iff.mp hw)
    exact ((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => I * (1 + v)) w).div
      (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 - v) w) hd).differentiableWithinAt
  · intro a ha b hb hab
    rw [← cayley_cayleyInv (mem_ball_zero_iff.mp ha), ← cayley_cayleyInv (mem_ball_zero_iff.mp hb),
      hab]
  · refine Subset.antisymm ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp hw)
    · intro z hz
      exact ⟨cayley z, cayley_mem_unitDisc hz, cayleyInv_cayley hz⟩

/-- Helper: `cayleyInv` as a fractional linear map, with its derivative `2i/(1-ζ)²`. -/
theorem hp_cayleyInv_eq : cayleyInv = fun v => (I * v + I) / (-1 * v + 1) := by
  funext v; unfold cayleyInv; congr 1 <;> ring

theorem hp_hasDerivAt_cayleyInv {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    HasDerivAt cayleyInv (2 * I / (1 - ζ) ^ 2) ζ := by
  have hd : -1 * ζ + 1 ≠ 0 := by
    rw [show -1 * ζ + 1 = 1 - ζ by ring]; exact cayleyInv_den_ne_zero hζ
  have h := hasDerivAt_mobius (a := I) (b := I) hd
  rw [← hp_cayleyInv_eq] at h
  convert h using 1
  rw [show -1 * ζ + 1 = 1 - ζ by ring]; ring

/-- Helper: `|C'(ζ)| (1 - |ζ|²) = 2 Im C(ζ)` for the inverse Cayley map `C`. -/
theorem hp_cayleyInv_norm_deriv {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ‖2 * I / (1 - ζ) ^ 2‖ * (1 - ‖ζ‖ ^ 2) = 2 * (cayleyInv ζ).im := by
  have hd := cayleyInv_den_ne_zero hζ
  have hpos : 0 < normSq (1 - ζ) := normSq_pos.mpr hd
  have him := s02_cayley_im ζ
  unfold cayleyInv
  rw [him, norm_div, norm_pow, norm_mul, Complex.norm_I, Complex.norm_two, Complex.sq_norm,
    Complex.sq_norm]
  field_simp

/-- Helper: a conformal `f : ℍ → Ω` is an isometry `d_ℍ → d_ρ`. -/
theorem hp_poincareDist_eq {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f upperHalf Ω)
    {a z : ℂ} (ha : a ∈ upperHalf) (hz : z ∈ upperHalf) :
    poincareDist Ω (f a) (f z) = hpDist a z := by
  have hF := hf.comp hp_isConformalOnto_cayleyInv
  have ha' := cayley_mem_unitDisc ha
  have hz' := cayley_mem_unitDisc hz
  have h1 := subsec_poincare_dist hF ha' hz'
  simp only [Function.comp_apply, cayleyInv_cayley ha, cayleyInv_cayley hz] at h1
  rw [h1, s02_diskDist_cayley ha' hz', ← s02_arcosh_uhp]
  have e1 : I * (1 + cayley a) / (1 - cayley a) = a := cayleyInv_cayley ha
  have e2 : I * (1 + cayley z) / (1 - cayley z) = z := cayleyInv_cayley hz
  rw [e1, e2]
  rfl

/-- Helper: `u ↦ -u` maps `ℍ` conformally onto `𝕃`. -/
theorem hp_isConformalOnto_neg : IsConformalOnto (fun u : ℂ => -u) upperHalf lowerHalf := by
  refine ⟨differentiableOn_neg _, fun a _ b _ h => neg_injective h, ?_⟩
  ext w
  simp only [mem_image, upperHalf, lowerHalf, mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, rfl⟩; simp; linarith
  · intro hw; exact ⟨-w, by simp; linarith, by simp⟩

/-- Helper: for a conformal `g : 𝕃 → Ω`, `d_ρ(g(ā), g(z̄)) = d_ℍ(a, z)`. -/
theorem hp_poincareDist_eq_lower {Ω : Set ℂ} {g : ℂ → ℂ} (hg : IsConformalOnto g lowerHalf Ω)
    {a z : ℂ} (ha : a ∈ upperHalf) (hz : z ∈ upperHalf) :
    poincareDist Ω (g (conj a)) (g (conj z)) = hpDist a z := by
  have hG := hg.comp hp_isConformalOnto_neg
  have ha' : -conj a ∈ upperHalf := by
    show 0 < (-conj a).im; simpa using (show 0 < a.im from ha)
  have hz' : -conj z ∈ upperHalf := by
    show 0 < (-conj z).im; simpa using (show 0 < z.im from hz)
  have h := hp_poincareDist_eq hG ha' hz'
  simp only [Function.comp_apply, neg_neg] at h
  rw [h]
  unfold hpDist
  congr 3
  · rw [show -conj a - -conj z = -conj (a - z) by simp; ring, norm_neg, Complex.norm_conj]
  all_goals simp

/-- Helper: the Schwarzian and the density of a conformal `f : ℍ → Ω` read through the Cayley
map. -/
theorem hp_cayley_pull {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f upperHalf Ω) {z : ℂ}
    (hz : z ∈ upperHalf) :
    poincareDensity Ω (f z) * ‖deriv f z‖ = 1 / z.im ∧
      schwarzNorm Ω (f z) = z.im ^ 2 * ‖schwarzian f z‖ := by
  have hF := hf.comp hp_isConformalOnto_cayleyInv
  set ζ := cayley z with hζdef
  have hζ : ζ ∈ unitDisc := cayley_mem_unitDisc hz
  have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
  have hCz : cayleyInv ζ = z := cayleyInv_cayley hz
  have hy : 0 < z.im := hz
  have hr : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
  have hC := hp_hasDerivAt_cayleyInv hζ1
  have hfd : DifferentiableAt ℂ f z := hf.1.differentiableAt (isOpen_upperHalf.mem_nhds hz)
  have hfd' : HasDerivAt f (deriv f (cayleyInv ζ)) (cayleyInv ζ) := by
    rw [hCz]; exact hfd.hasDerivAt
  have hFd : deriv (f ∘ cayleyInv) ζ = deriv f z * (2 * I / (1 - ζ) ^ 2) := by
    rw [(hfd'.comp ζ hC).deriv, hCz]
  have hN := hp_cayleyInv_norm_deriv hζ1
  rw [hCz] at hN
  have hFz : (f ∘ cayleyInv) ζ = f z := by simp [hCz]
  constructor
  · have hl := eq_lambda_f hF hζ
    rw [hFz, hFd, norm_mul] at hl
    have hy : 0 < z.im := hz
    have h2 : poincareDensity Ω (f z) * (‖deriv f z‖ * ‖2 * I / (1 - ζ) ^ 2‖) * (1 - ‖ζ‖ ^ 2) = 2 := by
      rw [hl]; field_simp
    have key : poincareDensity Ω (f z) * ‖deriv f z‖ * (2 * z.im) = 2 := by
      rw [← hN]; linarith [h2]
    rw [eq_div_iff hy.ne']
    linarith [key]
  · have hs := eq_s_disk hF hζ
    rw [hFz] at hs
    rw [hs]
    -- `S(f ∘ C) = (S f ∘ C) C'²`
    have hCA : AnalyticAt ℂ cayleyInv ζ := by
      rw [hp_cayleyInv_eq]
      exact (by fun_prop : AnalyticAt ℂ (fun v : ℂ => I * v + I) ζ).div
        (by fun_prop : AnalyticAt ℂ (fun v : ℂ => -1 * v + 1) ζ)
        (by rw [show -1 * ζ + 1 = 1 - ζ by ring]; exact cayleyInv_den_ne_zero hζ1)
    have hC0 : deriv cayleyInv ζ ≠ 0 := by
      rw [hC.deriv]
      exact div_ne_zero (by simp) (pow_ne_zero _ (cayleyInv_den_ne_zero hζ1))
    have hfA : AnalyticAt ℂ f (cayleyInv ζ) := by
      rw [hCz]; exact hf.1.analyticAt (isOpen_upperHalf.mem_nhds hz)
    have hf0 : deriv f (cayleyInv ζ) ≠ 0 := by
      rw [hCz]; exact deriv_ne_zero_of_injOn isOpen_upperHalf hf.1 hf.2.1 hz
    have hSC : schwarzian cayleyInv ζ = 0 := by
      rw [hp_cayleyInv_eq]
      exact schwarzian_mobius (by simp) ζ
    rw [eq19_1_chain_rule hCA hC0 hfA hf0, hSC, add_zero, hCz, hC.deriv, norm_mul, norm_pow]
    have : (‖2 * I / (1 - ζ) ^ 2‖ * (1 - ‖ζ‖ ^ 2)) ^ 2 = (2 * z.im) ^ 2 := by rw [hN]
    nlinarith [this, norm_nonneg (schwarzian f z)]

/-- (11.?) `eq:hp-s`, `sec11-halfplane.tex:205–212`: for a conformal `f : ℍ → Ω`,
`λ_Ω(f z)|f'(z)| = 1/y`, `s(f(z)) = y² |S f(z)|`, and `f^*(s² dâ) = m_f`. -/
theorem eq_hp_s {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f upperHalf Ω) :
    (∀ z ∈ upperHalf, poincareDensity Ω (f z) * ‖deriv f z‖ = 1 / z.im) ∧
      (∀ z ∈ upperHalf, schwarzNorm Ω (f z) = z.im ^ 2 * ‖schwarzian f z‖) ∧
      ∀ φ : ℂ → ℝ≥0∞, Measurable φ →
        ∫⁻ w, φ w ∂curvMass Ω = ∫⁻ z, φ (f z) ∂hpSchwarzMass f := by
  classical
  refine ⟨fun z hz => (hp_cayley_pull hf hz).1, fun z hz => (hp_cayley_pull hf hz).2,
    fun φ hφ => ?_⟩
  have hD : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  have hDo : IsOpen upperHalf := isOpen_upperHalf
  set F : ℂ → ℂ := upperHalf.piecewise f 0 with hFdef
  have hFm : Measurable F := hf.1.continuousOn.measurable_piecewise continuousOn_const hD
  have hFeq : ∀ z ∈ upperHalf, F z = f z := fun z hz => by simp [hFdef, hz]
  set c : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (z.im ^ 2 * ‖schwarzianHol f z‖ ^ 2) with hcdef
  have hcm : Measurable c := by
    have := s02_pullback_measurable_schwarzianHol f
    simp only [hcdef]
    fun_prop
  have hceq : ∀ z ∈ upperHalf, c z = ENNReal.ofReal (z.im ^ 2 * ‖schwarzian f z‖ ^ 2) := by
    intro z hz
    have hA : AnalyticAt ℂ f z := hf.1.analyticAt (hDo.mem_nhds hz)
    simp only [hcdef, schwarzian_of_analyticAt hA]
  have hmass : hpSchwarzMass f = (volume.restrict upperHalf).withDensity c := by
    unfold hpSchwarzMass
    refine withDensity_congr_ae ((ae_restrict_iff' hD).mpr (Filter.Eventually.of_forall
      fun z hz => (hceq z hz).symm))
  have hdens : ∀ z ∈ upperHalf,
      ‖deriv f z‖ ^ 2 * (schwarzNorm Ω (f z) ^ 2 * poincareDensity Ω (f z) ^ 2) =
        z.im ^ 2 * ‖schwarzian f z‖ ^ 2 := by
    intro z hz
    obtain ⟨hl, hs⟩ := hp_cayley_pull hf hz
    have hy : 0 < z.im := hz
    rw [hs]
    have : ‖deriv f z‖ ^ 2 * poincareDensity Ω (f z) ^ 2 = (1 / z.im) ^ 2 := by rw [← hl]; ring
    calc ‖deriv f z‖ ^ 2 * ((z.im ^ 2 * ‖schwarzian f z‖) ^ 2 * poincareDensity Ω (f z) ^ 2)
        = (‖deriv f z‖ ^ 2 * poincareDensity Ω (f z) ^ 2) * (z.im ^ 2 * ‖schwarzian f z‖) ^ 2 := by
          ring
      _ = z.im ^ 2 * ‖schwarzian f z‖ ^ 2 := by rw [this]; field_simp
  have hset : ∀ t : Set ℂ, t ∩ Ω = f '' (F ⁻¹' t ∩ upperHalf) := by
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
  have hmeas : curvMass Ω = (hpSchwarzMass f).map F := by
    rw [hmass]
    ext t ht
    have hpre : MeasurableSet (F ⁻¹' t ∩ upperHalf) := (hFm ht).inter hD
    rw [Measure.map_apply hFm ht, withDensity_apply _ (hFm ht), Measure.restrict_restrict (hFm ht),
      curvMass, withDensity_apply _ ht, Measure.restrict_restrict ht, hset t]
    have hder : ∀ x ∈ F ⁻¹' t ∩ upperHalf, HasFDerivWithinAt f
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f x)).restrictScalars ℝ)
        (F ⁻¹' t ∩ upperHalf) x := by
      intro x hx
      exact ((hf.1.differentiableAt (hDo.mem_nhds hx.2)).hasDerivAt.hasFDerivAt.restrictScalars
        ℝ).hasFDerivWithinAt
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hpre hder
      (hf.2.1.mono inter_subset_right)]
    refine setLIntegral_congr_fun hpre (fun x hx => ?_)
    rw [s02_pullback_det, abs_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity),
      hdens x hx.2, hceq x hx.2]
  rw [hmeas, lintegral_map hφ hFm]
  refine lintegral_congr_ae ?_
  have h1 : ∀ᵐ z ∂(volume.restrict upperHalf), z ∈ upperHalf := ae_restrict_mem hD
  have h2 : ∀ᵐ z ∂hpSchwarzMass f, z ∈ upperHalf := by
    rw [hmass]; exact (withDensity_absolutelyContinuous _ _).ae_le h1
  filter_upwards [h2] with z hz
  rw [hFeq z hz]


/-- Lemma 11.2 `lem:hp-vmoa`, `sec11-halfplane.tex:218`: if the conformal map `f : ℍ → Ω`
extends to a quasiconformal homeomorphism of `ℂ`, then `λ_f ∈ CM₀(ℍ)` iff `log f' ∈ VMOA(ℍ)`. -/
theorem lem_hp_vmoa {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f upperHalf Ω)
    (hext : ∃ F : ℂ → ℂ, IsQuasiconformal F univ ∧ F '' univ = univ ∧ EqOn F f upperHalf) :
    IsHPVanishingCarleson (hpSchwarzCarleson f) ↔ HPLogDerivVMOA f := by sorry

/-- Helper: an automorphism `G` of `ℍ` with `G(∞) = ∞` is `z ↦ κ z + β`, `κ > 0`, `β ∈ ℝ`. -/
theorem hp_automorphism_affine {G : ℂ → ℂ} (hG : IsConformalOnto G upperHalf upperHalf)
    (hGinf : Tendsto (fun w => ‖G w‖) (Filter.comap norm atTop ⊓ 𝓟 upperHalf) atTop) :
    ∃ κ β : ℝ, 0 < κ ∧ ∀ z ∈ upperHalf, G z = κ * z + β := by
  set H : ℂ → ℂ := stripCayley ∘ G ∘ stripCayleyInv with hHdef
  have hH : IsConformalOnto H unitDisc unitDisc :=
    isConformalOnto_stripCayley.comp (hG.comp isConformalOnto_stripCayleyInv)
  obtain ⟨c, a, hc1, ha1, heqH⟩ := exists_rotation_blaschke_of_isConformalOnto_unitDisc hH
  -- `c * blaschke a` is continuous at `1`
  have hden_one : (1 : ℂ) - conj a ≠ 0 := by
    intro hcon
    have : conj a = 1 := by linear_combination -hcon
    have hna : ‖conj a‖ = 1 := by rw [this]; simp
    rw [Complex.norm_conj] at hna
    linarith [ha1]
  have hcont : ContinuousAt (fun ζ => c * blaschke a ζ) 1 := by
    have h3 : ContinuousAt (blaschke a) 1 := by
      unfold blaschke
      exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simpa using hden_one)
    exact continuousAt_const.mul h3
  -- `H → 1` at `ζ = 1`, from `G(∞) = ∞`
  have hmapsto_one : Tendsto stripCayleyInv (𝓝[unitDisc] (1 : ℂ))
      (Filter.comap norm atTop ⊓ 𝓟 upperHalf) := by
    refine Filter.tendsto_inf.2 ⟨?_, ?_⟩
    · have hsub : unitDisc ⊆ ({1}ᶜ : Set ℂ) := by
        intro z hz hz1
        rw [Set.mem_singleton_iff] at hz1
        rw [hz1] at hz
        simp [unitDisc] at hz
      have h1 : Tendsto stripCayleyInv (𝓝[unitDisc] (1 : ℂ)) (Bornology.cobounded ℂ) :=
        tendsto_stripCayleyInv_cobounded_of_ne_one.mono_left (nhdsWithin_mono _ hsub)
      rw [← tendsto_norm_atTop_iff_cobounded] at h1
      exact tendsto_comap_iff.2 h1
    · apply tendsto_principal.2
      filter_upwards [self_mem_nhdsWithin] with ζ hζ
      exact isConformalOnto_stripCayleyInv.mapsTo hζ
  have hH_one : Tendsto H (𝓝[unitDisc] (1 : ℂ)) (𝓝 (1 : ℂ)) := by
    have h2 : Tendsto (G ∘ stripCayleyInv) (𝓝[unitDisc] (1 : ℂ)) (Bornology.cobounded ℂ) := by
      rw [← tendsto_norm_atTop_iff_cobounded]
      exact hGinf.comp hmapsto_one
    exact tendsto_stripCayley_cobounded.comp h2
  have hH_one' : Tendsto H (𝓝[unitDisc] (1 : ℂ)) (𝓝 (c * blaschke a 1)) := by
    have h2 : H =ᶠ[𝓝[unitDisc] (1 : ℂ)] (fun ζ => c * blaschke a ζ) := by
      filter_upwards [self_mem_nhdsWithin] with ζ hζ
      exact heqH hζ
    exact (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' h2.symm
  have hNeBot : (𝓝[unitDisc] (1 : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, unitDisc, closure_ball (0 : ℂ) one_ne_zero]
    simp
  have heq2 : c * blaschke a 1 = 1 := tendsto_nhds_unique hH_one' hH_one
  have hca : c * (1 - a) = 1 - conj a := by
    have hb : blaschke a 1 = (1 - a) / (1 - conj a) := by
      rw [blaschke]; ring_nf
    rw [hb, mul_div_assoc'] at heq2
    field_simp at heq2
    linear_combination heq2
  -- the affine coefficients
  have hna : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  have hD : (0 : ℝ) < 1 - Complex.normSq a := by linarith
  have ha_ne : (1 : ℂ) - a ≠ 0 := by
    intro h
    have h1 : a = 1 := by linear_combination -h
    apply hden_one
    rw [h1, map_one, sub_self]
  have hnorm1 : 0 < Complex.normSq (1 - a) := Complex.normSq_pos.mpr ha_ne
  refine ⟨Complex.normSq (1 - a) / (1 - Complex.normSq a), 2 * a.im / (1 - Complex.normSq a),
    div_pos hnorm1 hD, fun z hz => ?_⟩
  have hDc : (1 : ℂ) - a * conj a ≠ 0 := by
    rw [Complex.mul_conj]
    exact_mod_cast hD.ne'
  have hκc : ((Complex.normSq (1 - a) / (1 - Complex.normSq a) : ℝ) : ℂ) =
      (1 - a) * (1 - conj a) / (1 - a * conj a) := by
    have h1 : (1 - a) * (1 - conj a) = (Complex.normSq (1 - a) : ℂ) := by
      rw [← Complex.mul_conj, map_sub, map_one]
    rw [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one, Complex.mul_conj, h1]
  have hβc : ((2 * a.im / (1 - Complex.normSq a) : ℝ) : ℂ) = I * (conj a - a) / (1 - a * conj a) := by
    rw [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one, Complex.mul_conj,
      show conj a - a = -(a - conj a) by ring, Complex.sub_conj]
    linear_combination ((2 * a.im : ℝ) : ℂ) / (1 - (Complex.normSq a : ℂ)) * I_sq
  set κ : ℝ := Complex.normSq (1 - a) / (1 - Complex.normSq a) with hκdef
  set β : ℝ := 2 * a.im / (1 - Complex.normSq a) with hβdef
  have hy : 0 < z.im := hz
  set w : ℂ := stripCayley z with hwdef
  have hwmem : w ∈ unitDisc := stripCayley_mem_unitDisc hz
  have hwn : ‖w‖ < 1 := mem_ball_zero_iff.mp hwmem
  have hHw : H w = stripCayley (G z) := by
    rw [hHdef]
    simp only [Function.comp_apply]
    rw [hwdef, stripCayleyInv_cayley hz]
  have hkey : stripCayley (G z) = c * blaschke a w := by rw [← hHw]; exact heqH hwmem
  have hAz_im : 0 < ((κ : ℂ) * z + β).im := by
    simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    exact mul_pos (div_pos hnorm1 hD) hy
  have hzi : z + I ≠ 0 := stripCayley_den_ne_zero hy
  have hAi : (κ : ℂ) * z + β + I ≠ 0 := stripCayley_den_ne_zero hAz_im
  have hden_bl : (1 : ℂ) - conj a * w ≠ 0 := by
    intro hcon
    have h1 : conj a * w = 1 := by linear_combination -hcon
    have h2 : ‖conj a * w‖ = 1 := by rw [h1]; simp
    rw [norm_mul, Complex.norm_conj] at h2
    have h3 : ‖a‖ * ‖w‖ < 1 := by
      calc ‖a‖ * ‖w‖ < 1 * 1 := mul_lt_mul'' ha1 hwn (norm_nonneg _) (norm_nonneg _)
        _ = 1 := by ring
    linarith
  have hcA : stripCayley ((κ : ℂ) * z + β) = c * blaschke a w := by
    have hc : c = (1 - conj a) / (1 - a) := by rw [eq_div_iff ha_ne]; exact hca
    have hwz : w = (z - I) / (z + I) := rfl
    have E1 : (κ : ℂ) * z + β - I = (1 - conj a) * ((1 - a) * z - I * (1 + a)) / (1 - a * conj a) := by
      rw [hκc, hβc, eq_div_iff hDc]
      field_simp
      ring
    have E2 : (κ : ℂ) * z + β + I = (1 - a) * ((1 - conj a) * z + I * (1 + conj a)) / (1 - a * conj a) := by
      rw [hκc, hβc, eq_div_iff hDc]
      field_simp
      ring
    have hD2 : (1 - conj a) * z + I * (1 + conj a) = (z + I) * (1 - conj a * w) := by
      rw [hwz]
      field_simp
      ring
    have hN2 : (1 - a) * z - I * (1 + a) = (z + I) * (w - a) := by
      rw [hwz]
      field_simp
      ring
    have hDne : (1 - conj a) * z + I * (1 + conj a) ≠ 0 := by
      rw [hD2]
      exact mul_ne_zero hzi hden_bl
    have E3 : blaschke a w = ((1 - a) * z - I * (1 + a)) / ((1 - conj a) * z + I * (1 + conj a)) := by
      rw [hN2, hD2, mul_div_mul_left _ _ hzi, blaschke]
    show ((κ : ℂ) * z + β - I) / ((κ : ℂ) * z + β + I) = c * blaschke a w
    rw [E1, E2, E3, hc]
    generalize (1 - a) * z - I * (1 + a) = N
    generalize (1 - conj a) * z + I * (1 + conj a) = Dd at hDne
    have hDc' : (1 : ℂ) - conj a * a ≠ 0 := by rwa [mul_comm]
    field_simp
  have hGz_mem : G z ∈ upperHalf := hG.mapsTo hz
  rw [← stripCayleyInv_cayley hGz_mem, hkey, ← hcA, stripCayleyInv_cayley hAz_im]

/-- Remark `rem:hp-infinity`(i), `sec11-halfplane.tex:251`, first sentence (repaired: the inverse
maps also send `∞` to `∞`; see `collaboration/FALSE_w6.md` §2). -/
theorem rem_hp_infinity_i_affine {Ω : Set ℂ} {f f' : ℂ → ℂ} (hf : IsConformalOnto f upperHalf Ω)
    (hf' : IsConformalOnto f' upperHalf Ω)
    (hinf : Tendsto f (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ))
    (hinf' : Tendsto f' (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ))
    (hinv : Tendsto (Function.invFunOn f upperHalf) (cocompact ℂ ⊓ 𝓟 Ω) (cocompact ℂ))
    (hinv' : Tendsto (Function.invFunOn f' upperHalf) (cocompact ℂ ⊓ 𝓟 Ω) (cocompact ℂ)) :
    ∃ κ β : ℝ, 0 < κ ∧ ∀ z ∈ upperHalf, f' z = f (κ * z + β) := by
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  set G := Function.invFunOn f upperHalf ∘ f' with hGdef
  have hG : IsConformalOnto G upperHalf upperHalf := (hf.symm hU).comp hf'
  have hf'Ω : Tendsto f' (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ ⊓ 𝓟 Ω) :=
    Filter.tendsto_inf.2 ⟨hinf', tendsto_principal.2
      (mem_inf_of_right (fun z hz => hf'.mapsTo hz))⟩
  have hGc : Tendsto G (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ) := hinv.comp hf'Ω
  have hGinf : Tendsto (fun w => ‖G w‖) (Filter.comap norm atTop ⊓ 𝓟 upperHalf) atTop := by
    rw [comap_norm_atTop, Metric.cobounded_eq_cocompact, tendsto_norm_atTop_iff_cobounded,
      Metric.cobounded_eq_cocompact]
    exact hGc
  obtain ⟨κ, β, hκ, hGz⟩ := hp_automorphism_affine hG hGinf
  refine ⟨κ, β, hκ, fun z hz => ?_⟩
  have hfz : f' z ∈ f '' upperHalf := hf.2.2 ▸ hf'.mapsTo hz
  rw [← hGz z hz, hGdef, Function.comp_apply, Function.invFunOn_eq hfz]


/-- Helper: chain rule for `x ↦ F (κ x + β)`. -/
theorem hp_deriv_affine (F : ℂ → ℂ) (κ β w : ℂ) :
    deriv (fun x => F (κ * x + β)) w = κ * deriv F (κ * w + β) := by
  have h1 := deriv_comp_mul_left (f := fun u => F (u + β)) (c := κ) (x := w)
  simp only [smul_eq_mul] at h1
  rw [h1, deriv_comp_add_const]

/-- Helper: `S(f ∘ A) = κ² (S f) ∘ A` for `A(z) = κ z + β` (no hypothesis on `f`). -/
theorem hp_schwarzianHol_affine (f : ℂ → ℂ) {κ : ℂ} (hκ : κ ≠ 0) (β z : ℂ) :
    schwarzianHol (fun x => f (κ * x + β)) z = κ ^ 2 * schwarzianHol f (κ * z + β) := by
  have hd1 : deriv (fun x => f (κ * x + β)) = fun x => κ * deriv f (κ * x + β) := by
    funext x
    exact hp_deriv_affine f κ β x
  have hd2 : ∀ x, deriv (fun x => κ * deriv f (κ * x + β)) x =
      κ * (κ * deriv (deriv f) (κ * x + β)) := by
    intro x
    rw [deriv_const_mul_field, hp_deriv_affine (deriv f)]
  have hR : (fun w => κ * (κ * deriv (deriv f) (κ * w + β)) / (κ * deriv f (κ * w + β))) =
      fun w => κ * (deriv (deriv f) (κ * w + β) / deriv f (κ * w + β)) := by
    funext w
    rw [mul_div_mul_left _ _ hκ, mul_div_assoc]
  have hD := hp_deriv_affine (fun w => deriv (deriv f) w / deriv f w) κ β z
  unfold schwarzianHol
  simp only [hd1, hd2]
  rw [hR, deriv_const_mul_field, hD, mul_div_mul_left _ _ hκ]
  ring

/-- Helper: Lebesgue measure under `z ↦ κ z + β`, `κ > 0` real. -/
theorem hp_map_affine_volume {κ : ℝ} (hκ : 0 < κ) (β : ℂ) :
    Measure.map (fun z : ℂ => (κ : ℂ) * z + β) volume =
      ENNReal.ofReal ((κ ^ 2)⁻¹) • (volume : Measure ℂ) := by
  have hcomp : (fun z : ℂ => (κ : ℂ) * z + β) = (fun z => z + β) ∘ fun z : ℂ => κ • z := by
    funext z
    simp [Complex.real_smul]
  rw [hcomp, ← Measure.map_map (measurable_add_const β) (measurable_const_smul κ),
    Measure.map_addHaar_smul volume hκ.ne', Measure.map_smul, map_add_right_eq_self,
    Complex.finrank_real_complex, abs_of_pos (by positivity)]
  all_goals exact (measurable_add_const β).aemeasurable

/-- Helper: the `ℝ≥0∞` density of `λ_f = y³ |S f|² dx dy` on `ℍ`, through `schwarzianHol`. -/
def hpCarlesonDensity (f : ℂ → ℂ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (z.im ^ 2 * ‖schwarzianHol f z‖ ^ 2) * ENNReal.ofReal z.im

theorem hp_measurable_carlesonDensity (f : ℂ → ℂ) : Measurable (hpCarlesonDensity f) := by
  have hS : Measurable (schwarzianHol f) := by
    unfold schwarzianHol
    exact (measurable_deriv _).sub
      (measurable_const.mul (((measurable_deriv _).div (measurable_deriv f)).pow_const 2))
  unfold hpCarlesonDensity
  exact ((Complex.measurable_im.pow_const 2).mul (hS.norm.pow_const 2)).ennreal_ofReal.mul
    Complex.measurable_im.ennreal_ofReal

/-- Helper: `λ_f(T) = ∫_{T ∩ ℍ} y³ |S f|²` for `f` holomorphic on `ℍ`. -/
theorem hp_schwarzCarleson_apply {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalf) {T : Set ℂ}
    (hT : MeasurableSet T) :
    hpSchwarzCarleson f T = ∫⁻ z, (T ∩ upperHalf).indicator (hpCarlesonDensity f) z := by
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hae : (fun z => ENNReal.ofReal (z.im ^ 2 * ‖schwarzian f z‖ ^ 2)) =ᵐ[volume.restrict upperHalf]
      fun z => ENNReal.ofReal (z.im ^ 2 * ‖schwarzianHol f z‖ ^ 2) := by
    refine (ae_restrict_iff' hU.measurableSet).mpr (Filter.Eventually.of_forall fun z hz => ?_)
    dsimp only
    rw [schwarzian_of_analyticAt (hf.analyticAt (hU.mem_nhds hz))]
  have hmd : Measurable fun z => ENNReal.ofReal (z.im ^ 2 * ‖schwarzianHol f z‖ ^ 2) := by
    have := hp_measurable_carlesonDensity f
    have hS : Measurable (schwarzianHol f) := by
      unfold schwarzianHol
      exact (measurable_deriv _).sub
        (measurable_const.mul (((measurable_deriv _).div (measurable_deriv f)).pow_const 2))
    exact ((Complex.measurable_im.pow_const 2).mul (hS.norm.pow_const 2)).ennreal_ofReal
  unfold hpSchwarzCarleson hpWeight hpSchwarzMass
  rw [withDensity_congr_ae hae, withDensity_apply _ hT, restrict_withDensity hT,
    lintegral_withDensity_eq_lintegral_mul _ hmd Complex.measurable_im.ennreal_ofReal,
    Measure.restrict_restrict hT, ← lintegral_indicator (hT.inter hU.measurableSet)]
  rfl

/-- Helper: `λ_{f∘A}(A⁻¹ T) = κ⁻¹ λ_f(T)` for `A(z) = κ z + β`, `κ > 0`, `β` real. -/
theorem hp_schwarzCarleson_affine {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalf) {κ β : ℝ}
    (hκ : 0 < κ) {T : Set ℂ} (hT : MeasurableSet T) :
    hpSchwarzCarleson (fun z => f (κ * z + β)) ((fun z : ℂ => (κ : ℂ) * z + β) ⁻¹' T) =
      ENNReal.ofReal κ⁻¹ * hpSchwarzCarleson f T := by
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  set A : ℂ → ℂ := fun z => (κ : ℂ) * z + β with hAdef
  have hAm : Measurable A := (measurable_const.mul measurable_id).add_const _
  have hAim : ∀ z : ℂ, (A z).im = κ * z.im := by
    intro z
    simp [hAdef]
  have hAU : ∀ z, A z ∈ upperHalf ↔ z ∈ upperHalf := by
    intro z
    show 0 < (A z).im ↔ 0 < z.im
    rw [hAim]
    exact ⟨fun h => pos_of_mul_pos_right h hκ.le, fun h => mul_pos hκ h⟩
  have hg : DifferentiableOn ℂ (fun z => f (A z)) upperHalf := by
    intro z hz
    have hfz : DifferentiableAt ℂ f (A z) := hf.differentiableAt (hU.mem_nhds ((hAU z).mpr hz))
    exact (hfz.comp z ((differentiableAt_id.const_mul _).add_const _)).differentiableWithinAt
  have hpt : ∀ z, (A ⁻¹' T ∩ upperHalf).indicator (hpCarlesonDensity fun z => f (A z)) z =
      (T ∩ upperHalf).indicator (fun w => ENNReal.ofReal κ * hpCarlesonDensity f w) (A z) := by
    intro z
    by_cases hz : z ∈ A ⁻¹' T ∩ upperHalf
    · have hz' : A z ∈ T ∩ upperHalf := ⟨hz.1, (hAU z).mpr hz.2⟩
      rw [indicator_of_mem hz, indicator_of_mem hz']
      have hy : 0 < z.im := hz.2
      unfold hpCarlesonDensity
      rw [hp_schwarzianHol_affine f (by exact_mod_cast hκ.ne') (β : ℂ) z, hAim, norm_mul,
        norm_pow, Complex.norm_real, Real.norm_of_nonneg hκ.le, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hκ.le]
      congr 1
      ring
    · have hz' : A z ∉ T ∩ upperHalf := fun h => hz ⟨h.1, (hAU z).mp h.2⟩
      rw [indicator_of_notMem hz, indicator_of_notMem hz']
  have hTU := hT.inter hU.measurableSet
  rw [hp_schwarzCarleson_apply hg (hAm hT), hp_schwarzCarleson_apply hf hT]
  simp_rw [hpt]
  rw [← lintegral_map (((hp_measurable_carlesonDensity f).const_mul _).indicator hTU) hAm,
    hp_map_affine_volume hκ, lintegral_smul_measure, lintegral_indicator hTU,
    lintegral_indicator hTU, lintegral_const_mul _ (hp_measurable_carlesonDensity f), smul_eq_mul,
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [pow_two, mul_inv, mul_assoc, inv_mul_cancel₀ hκ.ne', mul_one]

/-- Helper: the box `Q_I` pulls back to `Q_{A⁻¹ I}` under `A(z) = κ z + β`. -/
theorem hp_box_affine {κ β : ℝ} (hκ : 0 < κ) (c ℓ : ℝ) :
    hpBox c ℓ = (fun z : ℂ => (κ : ℂ) * z + β) ⁻¹' hpBox (κ * c + β) (κ * ℓ) := by
  ext z
  simp only [hpBox, mem_ofPred_eq, mem_preimage, add_re, mul_re, ofReal_re, ofReal_im, zero_mul,
    sub_zero, add_im, mul_im, add_zero]
  rw [show κ * z.re + β - (κ * c + β) = κ * (z.re - c) by ring, abs_mul, abs_of_pos hκ]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by nlinarith, by positivity, by nlinarith⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem hp_box_ratio_affine {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalf) {κ β : ℝ}
    (hκ : 0 < κ) (c ℓ : ℝ) :
    hpSchwarzCarleson (fun z => f (κ * z + β)) (hpBox c ℓ) / ENNReal.ofReal ℓ =
      hpSchwarzCarleson f (hpBox (κ * c + β) (κ * ℓ)) / ENNReal.ofReal (κ * ℓ) := by
  have hmeas : MeasurableSet (hpBox (κ * c + β) (κ * ℓ)) := by
    unfold hpBox
    exact (measurableSet_le (f := fun z : ℂ => |z.re - (κ * c + β)|)
      (continuous_abs.comp (Complex.continuous_re.sub continuous_const)).measurable
      measurable_const).inter
      ((measurableSet_lt measurable_const Complex.measurable_im).inter
        (measurableSet_le Complex.measurable_im measurable_const))
  rw [hp_box_affine hκ c ℓ, hp_schwarzCarleson_affine hf hκ hmeas, ENNReal.ofReal_mul hκ.le,
    div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top),
    ENNReal.ofReal_inv_of_pos hκ]
  ring

/-- Remark `rem:hp-infinity`(i), `sec11-halfplane.tex:251–258`: for `A(z) = κ z + β`,
`‖λ_{f∘A}‖_CM = ‖λ_f‖_CM` and `ε_{λ_{f∘A}}(r) = ε_{λ_f}(κ r)`. -/
theorem rem_hp_infinity_i {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalf) {κ β : ℝ}
    (hκ : 0 < κ) :
    hpCMNorm (hpSchwarzCarleson fun z => f (κ * z + β)) = hpCMNorm (hpSchwarzCarleson f) ∧
      ∀ r : ℝ, 0 < r →
        hpEps (hpSchwarzCarleson fun z => f (κ * z + β)) r = hpEps (hpSchwarzCarleson f) (κ * r) := by
  have hc : ∀ c' : ℝ, κ * ((c' - β) / κ) + β = c' := fun c' => by
    rw [mul_div_cancel₀ _ hκ.ne', sub_add_cancel]
  have hl : ∀ ℓ' : ℝ, κ * (ℓ' / κ) = ℓ' := fun ℓ' => mul_div_cancel₀ _ hκ.ne'
  constructor
  · unfold hpCMNorm
    apply le_antisymm
    · refine iSup_le fun c => iSup_le fun ℓ => iSup_le fun hℓ => ?_
      rw [hp_box_ratio_affine hf hκ c ℓ]
      exact le_iSup_of_le (κ * c + β) (le_iSup_of_le (κ * ℓ)
        (le_iSup_of_le (by positivity) le_rfl))
    · refine iSup_le fun c => iSup_le fun ℓ => iSup_le fun hℓ => ?_
      refine le_iSup_of_le ((c - β) / κ) (le_iSup_of_le (ℓ / κ)
        (le_iSup_of_le (by positivity) ?_))
      rw [hp_box_ratio_affine hf hκ, hc, hl]
  · intro r hr
    unfold hpEps
    apply le_antisymm
    · refine iSup_le fun c => iSup_le fun ℓ => iSup_le fun hℓ => iSup_le fun hℓr => ?_
      rw [hp_box_ratio_affine hf hκ c ℓ]
      exact le_iSup_of_le (κ * c + β) (le_iSup_of_le (κ * ℓ)
        (le_iSup_of_le (by positivity) (le_iSup_of_le (by nlinarith) le_rfl)))
    · refine iSup_le fun c => iSup_le fun ℓ => iSup_le fun hℓ => iSup_le fun hℓr => ?_
      refine le_iSup_of_le ((c - β) / κ) (le_iSup_of_le (ℓ / κ)
        (le_iSup_of_le (by positivity) (le_iSup_of_le ?_ ?_)))
      · rw [div_le_iff₀ hκ]
        linarith
      · rw [hp_box_ratio_affine hf hκ, hc, hl]

/-- Helper: Tonelli on `ℂ ≅ ℝ × ℝ`, `y` outside. -/
theorem hp_lintegral_iter {F : ℂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F z = ∫⁻ y : ℝ, ∫⁻ x : ℝ, F ⟨x, y⟩ := by
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp hF, Measure.volume_eq_prod,
    lintegral_prod_symm' (fun p : ℝ × ℝ => F (Complex.measurableEquivRealProd.symm p))
      (hF.comp Complex.measurableEquivRealProd.symm.measurable)]
  rfl

/-- Helper: integrals against `1_S dA_ρ`. -/
theorem hp_lintegral_hpArea_restrict {S : Set ℂ} (hS : MeasurableSet S) (F : ℂ → ℝ≥0∞) :
    ∫⁻ z, F z ∂(hpArea.restrict S) =
      ∫⁻ z, (S ∩ upperHalf).indicator (fun z => ENNReal.ofReal ((z.im ^ 2)⁻¹) * F z) z := by
  have hU : MeasurableSet upperHalf :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  unfold hpArea
  rw [restrict_withDensity hS, Measure.restrict_restrict hS,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (Measurable.ennreal_ofReal (f := fun z : ℂ => (z.im ^ 2)⁻¹)
        (Complex.measurable_im.pow_const 2).inv)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    lintegral_indicator (hS.inter hU)]
  all_goals rfl

/-- Helper: `∫_ℝ C / (b ((x-u)² + s²)) dx = C π / (b s)`. -/
theorem hp_lintegral_lorentz {C b s : ℝ} (hC : 0 ≤ C) (hb : 0 < b) (hs : 0 < s) (u : ℝ) :
    ∫⁻ x : ℝ, ENNReal.ofReal (C / (b * ((x - u) ^ 2 + s ^ 2))) =
      ENNReal.ofReal (C * π / (b * s)) := by
  have h1 := integral_sub_right_eq_self (μ := volume) (fun v : ℝ => (1 + (v / s) ^ 2)⁻¹) u
  have h2 := Measure.integral_comp_div (fun w : ℝ => (1 + w ^ 2)⁻¹) s
  have hI : ∫ x : ℝ, (1 + ((x - u) / s) ^ 2)⁻¹ = s * π := by
    rw [h1, h2, integral_univ_inv_one_add_sq, abs_of_pos hs, smul_eq_mul]
  have hfun : (fun x : ℝ => C / (b * ((x - u) ^ 2 + s ^ 2))) =
      fun x => C / (b * s ^ 2) * (1 + ((x - u) / s) ^ 2)⁻¹ := by
    funext x
    have hq1 : (x - u) ^ 2 + s ^ 2 ≠ 0 := by positivity
    have hq2 : s ^ 2 + (x - u) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  have hint : Integrable (fun x : ℝ => C / (b * ((x - u) ^ 2 + s ^ 2))) := by
    rw [hfun]
    exact ((integrable_inv_one_add_sq.comp_div hs.ne').comp_sub_right u).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun x => show (0 : ℝ) ≤ _ by positivity), hfun, integral_const_mul, hI]
  congr 1
  field_simp

/-- Helper: `∫_1^∞ 4tπ/(y(y+t)) dy = 4π log(1+t)`. -/
theorem hp_lintegral_Ioi_log {t : ℝ} (ht : 0 < t) :
    ∫⁻ y in Ioi (1 : ℝ), ENNReal.ofReal (4 * t * π / (y * (y + t))) =
      ENNReal.ofReal (4 * π * Real.log (1 + t)) := by
  set F : ℝ → ℝ := fun y => 4 * π * (Real.log y - Real.log (y + t)) with hF
  have hderiv : ∀ y ∈ Ici (1 : ℝ), HasDerivAt F (4 * t * π / (y * (y + t))) y := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
    have h1 := Real.hasDerivAt_log hy0.ne'
    have h2 := HasDerivAt.comp_add_const y t (Real.hasDerivAt_log (by linarith : y + t ≠ 0))
    have h3 := (h1.sub h2).const_mul (4 * π)
    have h4 : 4 * π * (y⁻¹ - (y + t)⁻¹) = 4 * t * π / (y * (y + t)) := by
      have : y + t ≠ 0 := by linarith
      field_simp
      ring
    exact h3.congr_deriv h4
  have hnn : ∀ y ∈ Ioi (1 : ℝ), 0 ≤ 4 * t * π / (y * (y + t)) := fun y hy => by
    have : (0 : ℝ) < y := lt_trans one_pos hy
    positivity
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => 1 - t / (y + t)) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := t)).div_atTop (tendsto_atTop_add_const_right _ t tendsto_id)
      have h := (tendsto_const_nhds (x := (1 : ℝ))).sub this
      rwa [sub_zero] at h
    have h2 := ((Real.continuousAt_log one_ne_zero).tendsto.comp h1).const_mul (4 * π)
    rw [Real.log_one, mul_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    simp only [hF, Function.comp_apply]
    rw [← Real.log_div hy.ne' (by linarith), one_sub_div (by linarith : y + t ≠ 0),
      add_sub_cancel_right]
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hnn hlim
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hnn)), hval]
  congr 1
  simp only [hF, Real.log_one]
  ring

/-- Helper: boxes are measurable. -/
theorem hp_measurableSet_box (c ℓ : ℝ) : MeasurableSet (hpBox c ℓ) := by
  unfold hpBox
  exact (measurableSet_le (f := fun z : ℂ => |z.re - c|)
    (continuous_abs.comp (Complex.continuous_re.sub continuous_const)).measurable
    measurable_const).inter
      ((measurableSet_lt measurable_const Complex.measurable_im).inter
        (measurableSet_le Complex.measurable_im measurable_const))

/-- Helper: `arctan u ≥ π u / 4` on `[0, 1]` (concavity). -/
theorem hp_arctan_ge {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : π / 4 * u ≤ Real.arctan u := by
  have hc : ConcaveOn ℝ (Ici 0) Real.arctan := by
    refine AntitoneOn.concaveOn_of_deriv (convex_Ici 0) Real.continuous_arctan.continuousOn
      Real.differentiable_arctan.differentiableOn ?_
    rw [Real.deriv_arctan, interior_Ici]
    intro x hx y hy hxy
    have hx0 : 0 < x := hx
    show 1 / (1 + y ^ 2) ≤ 1 / (1 + x ^ 2)
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have := hc.2 (mem_Ici.mpr le_rfl : (0 : ℝ) ∈ Ici 0) (mem_Ici.mpr zero_le_one)
    (sub_nonneg.mpr h1) h0 (by ring)
  simp only [smul_eq_mul, Real.arctan_zero, Real.arctan_one, mul_zero, zero_add, mul_one] at this
  linarith

/-- Helper: `∫_{|x| > X} dx / (x² + b²) = (2/b) arctan(b/X)`. -/
theorem hp_integral_abs_gt {b X : ℝ} (hb : 0 < b) (hX : 0 < X) :
    ∫ x in {x : ℝ | X < |x|}, 1 / (x ^ 2 + b ^ 2) = 2 / b * Real.arctan (b / X) := by
  have hfun : (fun x : ℝ => 1 / (x ^ 2 + b ^ 2)) = fun x => 1 / b ^ 2 * (1 + (x / b) ^ 2)⁻¹ := by
    funext x
    have hq1 : x ^ 2 + b ^ 2 ≠ 0 := by positivity
    have hq2 : b ^ 2 + x ^ 2 ≠ 0 := by positivity
    field_simp
    all_goals ring
  have hint : Integrable (fun x : ℝ => 1 / (x ^ 2 + b ^ 2)) := by
    rw [hfun]
    exact (integrable_inv_one_add_sq.comp_div hb.ne').const_mul _
  have htot : ∫ x : ℝ, 1 / (x ^ 2 + b ^ 2) = π / b := by
    have h2 := Measure.integral_comp_div (fun w : ℝ => (1 + w ^ 2)⁻¹) b
    rw [hfun, integral_const_mul, h2, integral_univ_inv_one_add_sq, abs_of_pos hb, smul_eq_mul]
    field_simp
  have hS : MeasurableSet {x : ℝ | X < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hcompl : {x : ℝ | X < |x|}ᶜ = Icc (-X) X := by
    ext x
    simp [abs_le, not_lt]
  have hmid : ∫ x in Icc (-X) X, 1 / (x ^ 2 + b ^ 2) = 2 / b * Real.arctan (X / b) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    have hd : ∀ x ∈ uIcc (-X) X,
        HasDerivAt (fun x => Real.arctan (x / b) / b) (1 / (x ^ 2 + b ^ 2)) x := by
      intro x _
      have h := ((hasDerivAt_id' x).div_const b).arctan.div_const b
      convert h using 1
      have hq1 : x ^ 2 + b ^ 2 ≠ 0 := by positivity
      field_simp
      all_goals ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint.intervalIntegrable, neg_div,
      Real.arctan_neg]
    ring
  have h := integral_add_compl hS hint
  rw [hcompl, hmid, htot] at h
  have harc : Real.arctan (b / X) = π / 2 - Real.arctan (X / b) := by
    rw [← Real.arctan_inv_of_pos (div_pos hX hb), inv_div]
  rw [harc]
  linear_combination h

/-- Helper: the `x`-integral of Remark `rem:hp-infinity`(ii). -/
theorem hp_lintegral_abs_gt {y b X : ℝ} (hy : 0 < y) (hb : 0 < b) (hX : 0 < X) :
    ∫⁻ x in {x : ℝ | X < |x|}, ENNReal.ofReal (4 / (y * (x ^ 2 + b ^ 2))) =
      ENNReal.ofReal (4 / y * (2 / b * Real.arctan (b / X))) := by
  have hpt : ∀ x : ℝ, 4 / (y * (x ^ 2 + b ^ 2)) = 4 / y * (1 / (x ^ 2 + b ^ 2)) := fun x => by
    rw [mul_one_div, div_div]
  have hint : Integrable (fun x : ℝ => 1 / (x ^ 2 + b ^ 2)) := by
    have hfun : (fun x : ℝ => 1 / (x ^ 2 + b ^ 2)) = fun x => 1 / b ^ 2 * (1 + (x / b) ^ 2)⁻¹ := by
      funext x
      have hq1 : x ^ 2 + b ^ 2 ≠ 0 := by positivity
      have hq2 : b ^ 2 + x ^ 2 ≠ 0 := by positivity
      field_simp
      all_goals ring
    rw [hfun]
    exact (integrable_inv_one_add_sq.comp_div hb.ne').const_mul _
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul (4 / y)).integrableOn
    (ae_of_all _ fun x => show (0 : ℝ) ≤ _ by positivity), integral_const_mul,
    hp_integral_abs_gt hb hX]

/-- Remark `rem:hp-infinity`(ii), `sec11-halfplane.tex:260–279`: for `m = 1_{1<y<2} dA_ρ`,
`y m ∈ CM₀(ℍ)`, while `ν = (1 - |ζ|²) χ_* m`, `χ(z) = (z - i)/(z + i)`, satisfies
`ν(𝔻 ∩ D(1, r)) ≥ 2π log(4/3) r` for `0 < r < 2/3`; so `ν ∉ CM₀(𝔻)`. -/
theorem rem_hp_infinity_ii :
    IsHPVanishingCarleson (hpWeight (hpBandMeasure 1 2)) ∧
      (∀ r : ℝ, 0 < r → r < 2 / 3 →
        ENNReal.ofReal (2 * π * Real.log (4 / 3) * r) ≤
          (((hpBandMeasure 1 2).restrict upperHalf).map (fun z => (z - I) / (z + I))).withDensity
            (fun ζ => ENNReal.ofReal (1 - ‖ζ‖ ^ 2)) (unitDisc ∩ ball 1 r)) ∧
      ¬ IsVanishingCarlesonDisk
        ((((hpBandMeasure 1 2).restrict upperHalf).map (fun z => (z - I) / (z + I))).withDensity
          (fun ζ => ENNReal.ofReal (1 - ‖ζ‖ ^ 2))) := by
  have hU : MeasurableSet upperHalf :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hB : MeasurableSet {z : ℂ | 1 < z.im ∧ z.im < 2} :=
    (measurableSet_lt measurable_const Complex.measurable_im).inter
      (measurableSet_lt Complex.measurable_im measurable_const)
  -- (a) the boxes
  have hA : ∀ c ℓ : ℝ, 0 < ℓ → hpWeight (hpBandMeasure 1 2) (hpBox c ℓ) ≤ ENNReal.ofReal ℓ ∧
      (ℓ ≤ 1 → hpWeight (hpBandMeasure 1 2) (hpBox c ℓ) = 0) := by
    intro c ℓ hℓ
    have hQ := hp_measurableSet_box c ℓ
    have hval : hpWeight (hpBandMeasure 1 2) (hpBox c ℓ) =
        ∫⁻ z, ({z : ℂ | 1 < z.im ∧ z.im < 2} ∩ upperHalf).indicator (fun z =>
          ENNReal.ofReal ((z.im ^ 2)⁻¹) * (hpBox c ℓ).indicator (fun z => ENNReal.ofReal z.im) z) z := by
      unfold hpWeight hpBandMeasure
      rw [withDensity_apply _ hQ, ← lintegral_indicator hQ, hp_lintegral_hpArea_restrict hB]
    rw [hval]
    constructor
    · set K : ℂ → ℝ≥0∞ := fun z => (Icc (c - ℓ / 2) (c + ℓ / 2)).indicator 1 z.re *
        (Ioo (1 : ℝ) 2).indicator 1 z.im with hKdef
      have hKm : Measurable K :=
        ((measurable_one.indicator measurableSet_Icc).comp Complex.measurable_re).mul
          ((measurable_one.indicator measurableSet_Ioo).comp Complex.measurable_im)
      have hKval : ∫⁻ z, K z = ENNReal.ofReal ℓ := by
        rw [hp_lintegral_iter hKm]
        have hin : ∀ y : ℝ, ∫⁻ x : ℝ, K ⟨x, y⟩ =
            ENNReal.ofReal ℓ * (Ioo (1 : ℝ) 2).indicator 1 y := by
          intro y
          show ∫⁻ x : ℝ, (Icc (c - ℓ / 2) (c + ℓ / 2)).indicator 1 x *
            (Ioo (1 : ℝ) 2).indicator 1 y = _
          rw [lintegral_mul_const _ (measurable_one.indicator measurableSet_Icc),
            lintegral_indicator_one measurableSet_Icc, Real.volume_Icc]
          congr 2
          ring
        simp_rw [hin]
        rw [lintegral_const_mul _ (measurable_one.indicator measurableSet_Ioo),
          lintegral_indicator_one measurableSet_Ioo, Real.volume_Ioo]
        norm_num
      rw [← hKval]
      refine lintegral_mono fun z => ?_
      by_cases h : z ∈ {z : ℂ | 1 < z.im ∧ z.im < 2} ∩ upperHalf ∧ z ∈ hpBox c ℓ
      · obtain ⟨hzS, h4⟩ := h
        obtain ⟨⟨h1, h2⟩, h3⟩ := hzS
        have hx : z.re ∈ Icc (c - ℓ / 2) (c + ℓ / 2) := by
          have := abs_le.mp h4.1
          constructor <;> linarith [this.1, this.2]
        rw [indicator_of_mem (⟨⟨h1, h2⟩, h3⟩ : z ∈ {z : ℂ | 1 < z.im ∧ z.im < 2} ∩ upperHalf),
          indicator_of_mem h4]
        show _ ≤ (Icc (c - ℓ / 2) (c + ℓ / 2)).indicator 1 z.re * (Ioo (1 : ℝ) 2).indicator 1 z.im
        rw [indicator_of_mem hx, indicator_of_mem (show z.im ∈ Ioo (1 : ℝ) 2 from ⟨h1, h2⟩),
          Pi.one_apply, Pi.one_apply, one_mul, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        rw [pow_two, mul_inv, mul_assoc, inv_mul_cancel₀ (by linarith), mul_one]
        exact inv_le_one_of_one_le₀ h1.le
      · by_cases hzS : z ∈ {z : ℂ | 1 < z.im ∧ z.im < 2} ∩ upperHalf
        · rw [indicator_of_mem hzS, indicator_of_notMem (fun hq => h ⟨hzS, hq⟩), mul_zero]
          exact zero_le
        · rw [indicator_of_notMem hzS]
          exact zero_le
    · intro hℓ1
      refine (lintegral_congr fun z => ?_).trans lintegral_zero
      by_cases hzS : z ∈ {z : ℂ | 1 < z.im ∧ z.im < 2} ∩ upperHalf
      · rw [indicator_of_mem hzS, indicator_of_notMem (fun hq : z ∈ hpBox c ℓ => by
          linarith [hq.2.2, hzS.1.1]), mul_zero]
      · rw [indicator_of_notMem hzS]
  have hCM : IsHPVanishingCarleson (hpWeight (hpBandMeasure 1 2)) := by
    refine ⟨?_, ?_⟩
    · unfold IsHPCarleson
      refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
      unfold hpCMNorm
      refine iSup_le fun c => iSup_le fun ℓ => iSup_le fun hℓ => ?_
      exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact (hA c ℓ hℓ).1)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
      unfold hpEps
      symm
      refine le_antisymm (iSup_le fun c => iSup_le fun ℓ => iSup_le fun hℓ => iSup_le fun hℓr => ?_)
        zero_le
      rw [(hA c ℓ hℓ).2 (hℓr.trans hr.2.le), ENNReal.zero_div]
  -- (b) the disc side
  have hB2 : ∀ r : ℝ, 0 < r → r < 2 / 3 →
      ENNReal.ofReal (2 * π * Real.log (4 / 3) * r) ≤
        (((hpBandMeasure 1 2).restrict upperHalf).map (fun z => (z - I) / (z + I))).withDensity
          (fun ζ => ENNReal.ofReal (1 - ‖ζ‖ ^ 2)) (unitDisc ∩ ball 1 r) := by
    intro r hr hr2
    have hχm : Measurable fun z : ℂ => (z - I) / (z + I) :=
      (measurable_id.sub_const _).div (measurable_id.add_const _)
    have hA' : MeasurableSet (unitDisc ∩ ball (1 : ℂ) r) :=
      (show MeasurableSet unitDisc from measurableSet_ball).inter measurableSet_ball
    have hϖm : Measurable fun ζ : ℂ => ENNReal.ofReal (1 - ‖ζ‖ ^ 2) :=
      (measurable_const.sub (measurable_norm.pow_const 2)).ennreal_ofReal
    have hval : (((hpBandMeasure 1 2).restrict upperHalf).map (fun z => (z - I) / (z + I))).withDensity
        (fun ζ => ENNReal.ofReal (1 - ‖ζ‖ ^ 2)) (unitDisc ∩ ball 1 r) =
        ∫⁻ z, (upperHalf ∩ {z : ℂ | 1 < z.im ∧ z.im < 2} ∩ upperHalf).indicator (fun z =>
          ENNReal.ofReal ((z.im ^ 2)⁻¹) * (unitDisc ∩ ball 1 r).indicator
            (fun ζ => ENNReal.ofReal (1 - ‖ζ‖ ^ 2)) ((z - I) / (z + I))) z := by
      rw [withDensity_apply _ hA', ← lintegral_indicator hA', lintegral_map (hϖm.indicator hA') hχm,
        hpBandMeasure, Measure.restrict_restrict hU, hp_lintegral_hpArea_restrict (hU.inter hB)]
    set E : Set ℂ := {z : ℂ | z.im ∈ Ioo (1 : ℝ) 2 ∧ 2 / r < |z.re|} with hEdef
    have hE : MeasurableSet E :=
      show MeasurableSet ({z : ℂ | z.im ∈ Ioo (1 : ℝ) 2} ∩ {z : ℂ | 2 / r < |z.re|}) from
        (Complex.measurable_im measurableSet_Ioo).inter
          (measurableSet_lt measurable_const (continuous_abs.measurable.comp Complex.measurable_re))
    set g : ℂ → ℝ≥0∞ := fun z =>
      ENNReal.ofReal (4 / (z.im * (z.re ^ 2 + (z.im + 1) ^ 2))) with hgdef
    have hgm : Measurable g := by
      apply Measurable.ennreal_ofReal
      exact measurable_const.div (Complex.measurable_im.mul
        ((Complex.measurable_re.pow_const 2).add ((Complex.measurable_im.add_const _).pow_const 2)))
    have hS : MeasurableSet {x : ℝ | 2 / r < |x|} :=
      measurableSet_lt measurable_const continuous_abs.measurable
    have hiter : ∫⁻ z, E.indicator g z = ∫⁻ y in Ioo (1 : ℝ) 2, ∫⁻ x in {x : ℝ | 2 / r < |x|},
        ENNReal.ofReal (4 / (y * (x ^ 2 + (y + 1) ^ 2))) := by
      rw [hp_lintegral_iter (hgm.indicator hE), ← lintegral_indicator measurableSet_Ioo]
      congr 1
      funext y
      by_cases hy : y ∈ Ioo (1 : ℝ) 2
      · rw [indicator_of_mem hy, ← lintegral_indicator hS]
        congr 1
        funext x
        by_cases hx : 2 / r < |x|
        · rw [indicator_of_mem (show (⟨x, y⟩ : ℂ) ∈ E from ⟨hy, hx⟩),
            indicator_of_mem (show x ∈ {x : ℝ | 2 / r < |x|} from hx)]
        · rw [indicator_of_notMem (show (⟨x, y⟩ : ℂ) ∉ E from fun h => hx h.2),
            indicator_of_notMem (show x ∉ {x : ℝ | 2 / r < |x|} from hx)]
      · rw [indicator_of_notMem hy]
        exact (lintegral_congr fun x => indicator_of_notMem
          (show (⟨x, y⟩ : ℂ) ∉ E from fun h => hy h.1) _).trans lintegral_zero
    have hint : IntegrableOn (fun y : ℝ => π * r * y⁻¹) (Ioo 1 2) :=
      IntegrableOn.mono_set (t := Icc (1 : ℝ) 2) (Integrable.const_mul
        ((continuousOn_inv₀.mono fun y (hy : y ∈ Icc (1 : ℝ) 2) =>
          (ne_of_gt (lt_of_lt_of_le one_pos hy.1) : y ≠ 0)).integrableOn_Icc) (π * r))
        Ioo_subset_Icc_self
    have hlog : ∫⁻ y in Ioo (1 : ℝ) 2, ENNReal.ofReal (π * r * y⁻¹) =
        ENNReal.ofReal (π * r * Real.log 2) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        ((ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun y hy =>
          mul_nonneg (by positivity) (inv_pos.mpr (lt_trans one_pos hy.1)).le)),
        ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
        intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos (by norm_num), div_one]
    calc ENNReal.ofReal (2 * π * Real.log (4 / 3) * r)
        ≤ ENNReal.ofReal (π * r * Real.log 2) := by
          apply ENNReal.ofReal_le_ofReal
          have h43 : 2 * Real.log (4 / 3) ≤ Real.log 2 := by
            rw [← Real.log_rpow (by norm_num)]
            exact Real.log_le_log (by positivity) (by norm_num)
          nlinarith [mul_le_mul_of_nonneg_left h43 (le_of_lt (mul_pos Real.pi_pos hr))]
      _ = ∫⁻ y in Ioo (1 : ℝ) 2, ENNReal.ofReal (π * r * y⁻¹) := hlog.symm
      _ ≤ ∫⁻ y in Ioo (1 : ℝ) 2, ∫⁻ x in {x : ℝ | 2 / r < |x|},
          ENNReal.ofReal (4 / (y * (x ^ 2 + (y + 1) ^ 2))) := by
          refine setLIntegral_mono' measurableSet_Ioo fun y hy => ?_
          have hy0 : 0 < y := lt_trans one_pos hy.1
          rw [hp_lintegral_abs_gt hy0 (by linarith [hy.1]) (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have hu0 : 0 ≤ (y + 1) / (2 / r) := by positivity
          have hu1 : (y + 1) / (2 / r) ≤ 1 := by
            rw [div_le_one (by positivity)]
            rw [le_div_iff₀ hr]
            nlinarith [hy.2]
          have harc := hp_arctan_ge hu0 hu1
          calc π * r * y⁻¹ = 4 / y * (2 / (y + 1) * (π / 4 * ((y + 1) / (2 / r)))) := by
                field_simp
            _ ≤ _ := by gcongr
      _ = ∫⁻ z, E.indicator g z := hiter.symm
      _ ≤ _ := by
          rw [hval]
          refine lintegral_mono fun z => ?_
          by_cases h : z ∈ E
          · obtain ⟨⟨h1, h2⟩, h3⟩ := h
            have hy0 : 0 < z.im := lt_trans one_pos h1
            have hzS : z ∈ upperHalf ∩ {z : ℂ | 1 < z.im ∧ z.im < 2} ∩ upperHalf :=
              ⟨⟨hy0, h1, h2⟩, hy0⟩
            have hne : z + I ≠ 0 := stripCayley_den_ne_zero hy0
            have hzI : ‖z + I‖ ^ 2 = z.re ^ 2 + (z.im + 1) ^ 2 := by
              rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
              simp only [add_re, add_im, I_re, I_im, add_zero]
              ring
            have hzmI : ‖z - I‖ ^ 2 = z.re ^ 2 + (z.im - 1) ^ 2 := by
              rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
              simp only [sub_re, sub_im, I_re, I_im, sub_zero]
              ring
            have hnpos : 0 < ‖z + I‖ := norm_pos_iff.mpr hne
            have hχA : (z - I) / (z + I) ∈ unitDisc ∩ ball 1 r := by
              constructor
              · refine mem_ball_zero_iff.mpr ?_
                rw [norm_div, div_lt_one hnpos]
                have : ‖z - I‖ ^ 2 < ‖z + I‖ ^ 2 := by
                  rw [hzI, hzmI]
                  nlinarith
                exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this
              · rw [mem_ball, dist_eq_norm]
                have hsub : (z - I) / (z + I) - 1 = -(2 * I) / (z + I) := by
                  field_simp
                  ring
                have hre : |z.re| ≤ ‖z + I‖ := by
                  have := Complex.abs_re_le_norm (z + I)
                  simpa using this
                rw [hsub, norm_div, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_two,
                  div_lt_iff₀ hnpos]
                rw [div_lt_iff₀ hr] at h3
                nlinarith
            rw [indicator_of_mem (show z ∈ E from ⟨⟨h1, h2⟩, h3⟩), indicator_of_mem hzS,
              indicator_of_mem hχA,
              ← ENNReal.ofReal_mul (by positivity)]
            show ENNReal.ofReal (4 / (z.im * (z.re ^ 2 + (z.im + 1) ^ 2))) ≤
              ENNReal.ofReal ((z.im ^ 2)⁻¹ * (1 - ‖(z - I) / (z + I)‖ ^ 2))
            apply le_of_eq
            congr 1
            have hq : z.re ^ 2 + (z.im + 1) ^ 2 ≠ 0 := by positivity
            rw [norm_div, div_pow, hzI, hzmI]
            field_simp
            ring
          · rw [indicator_of_notMem h]
            exact zero_le
  refine ⟨hCM, hB2, ?_⟩
  rintro ⟨-, hvan⟩
  have hε : 0 < π * Real.log (4 / 3) := mul_pos Real.pi_pos (Real.log_pos (by norm_num))
  obtain ⟨δ, hδ, hδ'⟩ := hvan (π * Real.log (4 / 3)) hε
  have hr : 0 < min (δ / 2) (1 / 3) := lt_min (by linarith) (by norm_num)
  have h1 := hδ' 1 (by simp) (min (δ / 2) (1 / 3)) hr
    (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have h2 := hB2 (min (δ / 2) (1 / 3)) hr (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
  have h3 := h2.trans h1
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
  nlinarith [mul_pos hε hr]

/-- The angle `θ ∈ [0, 2π)` of `z`. -/
def hpAngle (z : ℂ) : ℝ := if 0 ≤ z.arg then z.arg else z.arg + 2 * π

/-- `φ(θ) = α θ` on `[0, π]`, `α π + (2 - α)(θ - π)` on `[π, 2π]`. -/
def hpPowerAngle (α θ : ℝ) : ℝ := if θ ≤ π then α * θ else α * π + (2 - α) * (θ - π)

/-- The map `r e^{iθ} ↦ r^α e^{iφ(θ)}` of Remark `rem:hp-infinity`(iii) (and Proposition
`prop:sector`(a)). -/
def hpPowerExt (α : ℝ) (z : ℂ) : ℂ := ((‖z‖ ^ α : ℝ) : ℂ) * exp ((hpPowerAngle α (hpAngle z) : ℂ) * I)

/-- Helper: `hpAngle z ∈ [0, 2π)`. -/
theorem s11_pow_angle_mem (z : ℂ) : 0 ≤ hpAngle z ∧ hpAngle z < 2 * π := by
  have hpi := Real.pi_pos
  unfold hpAngle
  split_ifs with h
  · exact ⟨h, by linarith [Complex.arg_le_pi z]⟩
  · push_neg at h
    exact ⟨by linarith [Complex.neg_pi_lt_arg z], by linarith⟩

/-- Helper: `exp(a i) = exp(b i)` when `a - b = 2π`. -/
theorem s11_pow_exp_period {a b : ℝ} (h : a - b = 2 * π) :
    exp ((a : ℂ) * I) = exp ((b : ℂ) * I) := by
  have ha : (a : ℂ) = b + 2 * π := by exact_mod_cast (by linarith : a = b + 2 * π)
  rw [ha, add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- Helper: the polar form `z = |z| e^{i hpAngle z}`. -/
theorem s11_pow_polar (z : ℂ) : ((‖z‖ : ℝ) : ℂ) * exp ((hpAngle z : ℂ) * I) = z := by
  unfold hpAngle
  split_ifs
  · exact Complex.norm_mul_exp_arg_mul_I z
  · rw [s11_pow_exp_period (b := arg z) (by ring)]
    exact Complex.norm_mul_exp_arg_mul_I z

/-- Helper: `hpAngle (r e^{iψ}) = ψ` for `r > 0`, `ψ ∈ [0, 2π)`. -/
theorem s11_pow_angle_of {r ψ : ℝ} (hr : 0 < r) (h0 : 0 ≤ ψ) (h2 : ψ < 2 * π) :
    hpAngle ((r : ℂ) * exp ((ψ : ℂ) * I)) = ψ := by
  have hpi := Real.pi_pos
  unfold hpAngle
  rw [Complex.arg_real_mul _ hr]
  by_cases hψ : ψ ≤ π
  · have ha : arg (exp ((ψ : ℂ) * I)) = ψ := by
      rw [Complex.exp_mul_I]
      exact Complex.arg_cos_add_sin_mul_I ⟨by linarith, hψ⟩
    rw [ha, if_pos h0]
  · push_neg at hψ
    have ha : arg (exp ((ψ : ℂ) * I)) = ψ - 2 * π := by
      rw [s11_pow_exp_period (b := ψ - 2 * π) (by ring), Complex.exp_mul_I]
      exact Complex.arg_cos_add_sin_mul_I ⟨by linarith, by linarith⟩
    rw [ha, if_neg (by linarith)]
    ring

/-- Helper: if `-w ∈ slitPlane` (`w` is off `[0, ∞)`), then `hpAngle w = arg(-w) + π`. -/
theorem s11_pow_angle_neg {w : ℂ} (hw : -w ∈ slitPlane) : hpAngle w = arg (-w) + π := by
  have hpi := Real.pi_pos
  unfold hpAngle
  rcases lt_trichotomy w.im 0 with him | him | him
  · rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg him,
      if_neg (not_le.mpr (Complex.arg_neg_iff.mpr him))]
    ring
  · have hre : 0 < (-w).re := by
      rcases hw with h | h
      · exact h
      · exact absurd (show (-w).im = 0 by simp [him]) h
    have hre' : w.re < 0 := by simpa using hre
    rw [Complex.arg_eq_pi_iff.mpr ⟨hre', him⟩,
      Complex.arg_eq_zero_iff.mpr ⟨hre.le, by simp [him]⟩, if_pos hpi.le]
    ring
  · rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos him, if_pos (Complex.arg_nonneg_iff.mpr him.le)]
    ring

/-- Helper: a polar map `z ↦ ρ(|z|) e^{iΦ(hpAngle z)}` is continuous on `ℂ` when `ρ, Φ` are
continuous, `ρ(0) = 0` and `Φ(2π) = Φ(0) + 2π`. -/
theorem s11_pow_polar_cont {ρ Φ : ℝ → ℝ} (hρ : Continuous ρ) (hρ0 : ρ 0 = 0)
    (hΦ : Continuous Φ) (hΦ2 : Φ (2 * π) = Φ 0 + 2 * π) :
    Continuous fun z : ℂ => (ρ ‖z‖ : ℂ) * exp ((Φ (hpAngle z) : ℂ) * I) := by
  have hρc : Continuous fun w : ℂ => (ρ ‖w‖ : ℂ) := continuous_ofReal.comp (hρ.comp continuous_norm)
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz0 : z = 0
  · subst hz0
    have h0 : Tendsto (fun w : ℂ => ‖(ρ ‖w‖ : ℂ)‖) (𝓝 0) (𝓝 0) := by
      have := (hρc.tendsto 0).norm
      simpa [hρ0] using this
    simp only [ContinuousAt, norm_zero, hρ0, ofReal_zero, zero_mul]
    refine squeeze_zero_norm (fun w => le_of_eq ?_) h0
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  · by_cases hpos : 0 < z.re ∧ z.im = 0
    · -- near the positive real axis: `hpAngle w = arg w` or `arg w + 2π`
      set Ψ : ℝ → ℝ := fun t => Φ (max t 0) + Φ (min t 0 + 2 * π) - Φ (2 * π) with hΨ
      have hΨc : Continuous Ψ :=
        ((hΦ.comp (continuous_id.max continuous_const)).add
          (hΦ.comp ((continuous_id.min continuous_const).add continuous_const))).sub continuous_const
      have hz : z ∈ slitPlane := Or.inl hpos.1
      have heq : ∀ w : ℂ, exp ((Φ (hpAngle w) : ℂ) * I) = exp ((Ψ (arg w) : ℂ) * I) := by
        intro w
        unfold hpAngle
        split_ifs with h
        · have hΨw : Ψ (arg w) = Φ (arg w) := by
            simp only [hΨ, max_eq_left h, min_eq_right h, zero_add, add_sub_cancel_right]
          rw [hΨw]
        · push_neg at h
          refine s11_pow_exp_period ?_
          simp only [hΨ, max_eq_right h.le, min_eq_left h.le]
          rw [hΦ2]
          ring
      have hc : ContinuousAt (fun w : ℂ => (ρ ‖w‖ : ℂ) * exp ((Ψ (arg w) : ℂ) * I)) z :=
        hρc.continuousAt.mul (Complex.continuous_exp.continuousAt.comp
          ((continuous_ofReal.continuousAt.comp
            (hΨc.continuousAt.comp (Complex.continuousAt_arg hz))).mul continuousAt_const))
      exact hc.congr (Eventually.of_forall fun w => by simp only [heq])
    · -- otherwise `-z ∈ slitPlane` and `hpAngle w = arg(-w) + π` near `z`
      have hz : -z ∈ slitPlane := by
        by_cases him : z.im = 0
        · left
          have hre : z.re ≠ 0 := fun h => hz0 (Complex.ext h him)
          have hle : ¬ 0 < z.re := fun h => hpos ⟨h, him⟩
          push_neg at hle
          show 0 < (-z).re
          rw [neg_re]
          exact neg_pos.mpr (lt_of_le_of_ne hle hre)
        · right
          show (-z).im ≠ 0
          rw [neg_im]
          exact neg_ne_zero.mpr him
      have hev : ∀ᶠ w in 𝓝 z, hpAngle w = arg (-w) + π :=
        Filter.eventually_of_mem ((Complex.isOpen_slitPlane.preimage continuous_neg).mem_nhds hz)
          fun w hw => s11_pow_angle_neg hw
      have hc : ContinuousAt (fun w : ℂ => (ρ ‖w‖ : ℂ) * exp ((Φ (arg (-w) + π) : ℂ) * I)) z :=
        hρc.continuousAt.mul (Complex.continuous_exp.continuousAt.comp
          ((continuous_ofReal.continuousAt.comp (hΦ.continuousAt.comp
            (((Complex.continuousAt_arg hz).comp continuous_neg.continuousAt).add
              continuousAt_const))).mul continuousAt_const))
      exact hc.congr (hev.mono fun w hw => by dsimp only; rw [hw])

/-- Helper: composing two polar maps whose radial and angular parts are inverse on `(0, ∞)` and
`[0, 2π)` gives the identity. -/
theorem s11_pow_polar_comp {ρ₁ Φ₁ ρ₂ Φ₂ : ℝ → ℝ} (hρ₁ : ∀ r, 0 < r → 0 < ρ₁ r) (hρ₁0 : ρ₁ 0 = 0)
    (hρ₂0 : ρ₂ 0 = 0) (hρ : ∀ r, 0 < r → ρ₂ (ρ₁ r) = r)
    (hΦ₁ : ∀ θ, 0 ≤ θ → θ < 2 * π → 0 ≤ Φ₁ θ ∧ Φ₁ θ < 2 * π)
    (hΦ : ∀ θ, 0 ≤ θ → θ < 2 * π → Φ₂ (Φ₁ θ) = θ) (z : ℂ) :
    (ρ₂ ‖(ρ₁ ‖z‖ : ℂ) * exp ((Φ₁ (hpAngle z) : ℂ) * I)‖ : ℂ) *
        exp ((Φ₂ (hpAngle ((ρ₁ ‖z‖ : ℂ) * exp ((Φ₁ (hpAngle z) : ℂ) * I))) : ℂ) * I) = z := by
  by_cases hz : z = 0
  · subst hz
    simp [hρ₁0, hρ₂0]
  · have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
    obtain ⟨ha0, ha2⟩ := s11_pow_angle_mem z
    obtain ⟨hb0, hb2⟩ := hΦ₁ _ ha0 ha2
    have hn : ‖(ρ₁ ‖z‖ : ℂ) * exp ((Φ₁ (hpAngle z) : ℂ) * I)‖ = ρ₁ ‖z‖ := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hρ₁ _ hr)]
    rw [hn, s11_pow_angle_of (hρ₁ _ hr) hb0 hb2, hρ _ hr, hΦ _ ha0 ha2]
    exact s11_pow_polar z

/-- Helper: `hpPowerAngle α` in min/max form (hence continuous). -/
theorem s11_pow_angle_minmax (α θ : ℝ) :
    hpPowerAngle α θ = α * min θ π + (2 - α) * max (θ - π) 0 := by
  unfold hpPowerAngle
  split_ifs with h
  · rw [min_eq_left h, max_eq_right (by linarith)]
    ring
  · push_neg at h
    rw [min_eq_right h.le, max_eq_left (by linarith)]

/-- Helper: `φ = hpPowerAngle α` and `χ(θ) = min(θ, απ)/α + max(θ - απ, 0)/(2 - α)` are inverse
bijections of `[0, 2π)`. -/
theorem s11_pow_angle_inv {α : ℝ} (h1 : 1 < α) (h2 : α < 2) {θ : ℝ} (h0 : 0 ≤ θ)
    (h2π : θ < 2 * π) :
    (0 ≤ hpPowerAngle α θ ∧ hpPowerAngle α θ < 2 * π ∧
      min (hpPowerAngle α θ) (α * π) / α + max (hpPowerAngle α θ - α * π) 0 / (2 - α) = θ) ∧
    (0 ≤ min θ (α * π) / α + max (θ - α * π) 0 / (2 - α) ∧
      min θ (α * π) / α + max (θ - α * π) 0 / (2 - α) < 2 * π ∧
      hpPowerAngle α (min θ (α * π) / α + max (θ - α * π) 0 / (2 - α)) = θ) := by
  have hpi := Real.pi_pos
  have hα : 0 < α := by linarith
  have hα0 : α ≠ 0 := hα.ne'
  have h2α : 0 < 2 - α := by linarith
  have h2α0 : 2 - α ≠ 0 := h2α.ne'
  have hαπ : α * π < 2 * π := by nlinarith
  have hπαπ : π < α * π := by nlinarith
  constructor
  · unfold hpPowerAngle
    split_ifs with hθ
    · have hle : α * θ ≤ α * π := mul_le_mul_of_nonneg_left hθ hα.le
      refine ⟨mul_nonneg hα.le h0, by linarith, ?_⟩
      rw [min_eq_left hle, max_eq_right (by linarith), zero_div, add_zero]
      field_simp
    · push_neg at hθ
      have hpos : 0 < (2 - α) * (θ - π) := mul_pos h2α (by linarith)
      have hlt : (2 - α) * (θ - π) < (2 - α) * π := mul_lt_mul_of_pos_left (by linarith) h2α
      refine ⟨by linarith, by linarith, ?_⟩
      rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      field_simp
      ring
  · by_cases hθ : θ ≤ α * π
    · rw [min_eq_left hθ, max_eq_right (by linarith), zero_div, add_zero]
      have hq : θ / α ≤ π := (div_le_iff₀ hα).mpr (by linarith)
      refine ⟨div_nonneg h0 hα.le, by linarith, ?_⟩
      unfold hpPowerAngle
      rw [if_pos hq]
      field_simp
    · push_neg at hθ
      rw [min_eq_right hθ.le, max_eq_left (by linarith)]
      have hq : (θ - α * π) / (2 - α) < π := (div_lt_iff₀ h2α).mpr (by linarith)
      have hq0 : 0 < (θ - α * π) / (2 - α) := div_pos (by linarith) h2α
      have hαα : α * π / α = π := by field_simp
      rw [hαα]
      refine ⟨by linarith, by linarith, ?_⟩
      unfold hpPowerAngle
      rw [if_neg (by linarith)]
      field_simp
      ring

/-- Helper: `z^s = |z|^s e^{i s arg z}` for `z ≠ 0`, `s ∈ ℝ`. -/
theorem s11_pow_cpow_polar {z : ℂ} (hz0 : z ≠ 0) (s : ℝ) :
    z ^ (s : ℂ) = ((‖z‖ ^ s : ℝ) : ℂ) * exp (((s * arg z : ℝ) : ℂ) * I) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hlog : Complex.log z = (Real.log ‖z‖ : ℂ) + (arg z : ℂ) * I := by
    apply Complex.ext <;> simp [Complex.log_re, Complex.log_im]
  rw [Complex.cpow_def_of_ne_zero hz0, hlog, Real.rpow_def_of_pos hr, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Helper: `|z^s| = |z|^s` for `z ≠ 0`, `s ∈ ℝ`. -/
theorem s11_pow_norm_cpow {z : ℂ} (hz0 : z ≠ 0) (s : ℝ) : ‖z ^ (s : ℂ)‖ = ‖z‖ ^ s := by
  rw [s11_pow_cpow_polar hz0, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) s)]

/-- Helper: a continuous bijection with continuous inverse is a homeomorphism onto the image of
any set. -/
theorem s11_pow_homeoOnto {T g : ℂ → ℂ} (hT : Continuous T) (hg : Continuous g)
    (hl : Function.LeftInverse g T) (D : Set ℂ) : IsHomeomorphOnto T D (T '' D) := by
  refine ⟨hT.continuousOn, hl.injective.injOn, rfl, ?_⟩
  refine hg.continuousOn.congr fun w hw => ?_
  obtain ⟨z, hz, rfl⟩ := hw
  have hex : ∃ a ∈ D, T a = T z := ⟨z, hz, rfl⟩
  rw [hl z]
  exact hl.injective (Function.invFunOn_eq hex)

theorem s11_pow_lower_eq {α : ℝ} {z : ℂ} (hz : z ∈ lowerHalf) :
    hpPowerExt α z = ((‖z‖ ^ (2 * α - 2) : ℝ) : ℂ) * z ^ ((2 - α : ℝ) : ℂ) := by
  have him : z.im < 0 := hz
  have hz0 : z ≠ 0 := fun h => by rw [h, zero_im] at him; exact lt_irrefl _ him
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have harg : arg z < 0 := Complex.arg_neg_iff.mpr him
  have hpi := Complex.neg_pi_lt_arg z
  have hA : hpAngle z = arg z + 2 * π := by
    unfold hpAngle
    rw [if_neg (not_le.mpr harg)]
  have hP : hpPowerAngle α (hpAngle z) = (2 - α) * arg z + 2 * π := by
    rw [hA]
    unfold hpPowerAngle
    rw [if_neg (by linarith)]
    ring
  rw [s11_pow_cpow_polar hz0, ← mul_assoc, ← ofReal_mul, ← Real.rpow_add hr,
    show 2 * α - 2 + (2 - α) = α by ring]
  unfold hpPowerExt
  rw [hP, s11_pow_exp_period (b := (2 - α) * arg z) (by ring)]

theorem s11_pow_continuous {α : ℝ} (h0 : 0 < α) : Continuous (hpPowerExt α) := by
  have hΦ : Continuous (hpPowerAngle α) := by
    have h : hpPowerAngle α = fun θ => α * min θ π + (2 - α) * max (θ - π) 0 :=
      funext (s11_pow_angle_minmax α)
    rw [h]
    exact (continuous_const.mul (continuous_id.min continuous_const)).add
      (continuous_const.mul ((continuous_id.sub continuous_const).max continuous_const))
  have hΦ2 : hpPowerAngle α (2 * π) = hpPowerAngle α 0 + 2 * π := by
    have hpi := Real.pi_pos
    unfold hpPowerAngle
    rw [if_neg (by linarith), if_pos hpi.le]
    ring
  exact s11_pow_polar_cont (ρ := fun r => r ^ α) (Real.continuous_rpow_const h0.le)
    (Real.zero_rpow h0.ne') hΦ hΦ2

theorem s11_pow_inverse {α : ℝ} (h1 : 1 < α) (h2 : α < 2) :
    ∃ g : ℂ → ℂ, Continuous g ∧ Function.LeftInverse g (hpPowerExt α) ∧
      Function.RightInverse g (hpPowerExt α) := by
  have hpi := Real.pi_pos
  have hα : 0 < α := by linarith
  have h2α : 0 < 2 - α := by linarith
  have hαπ : α * π < 2 * π := by nlinarith
  refine ⟨fun w => ((‖w‖ ^ α⁻¹ : ℝ) : ℂ) *
      exp (((min (hpAngle w) (α * π) / α + max (hpAngle w - α * π) 0 / (2 - α) : ℝ) : ℂ) * I),
    ?_, ?_, ?_⟩
  · refine s11_pow_polar_cont (ρ := fun r => r ^ α⁻¹)
      (Φ := fun θ => min θ (α * π) / α + max (θ - α * π) 0 / (2 - α))
      (Real.continuous_rpow_const (inv_nonneg.mpr hα.le)) (Real.zero_rpow (inv_ne_zero hα.ne'))
      (((continuous_id.min continuous_const).div_const _).add
        (((continuous_id.sub continuous_const).max continuous_const).div_const _)) ?_
    show min (2 * π) (α * π) / α + max (2 * π - α * π) 0 / (2 - α) =
      min 0 (α * π) / α + max (0 - α * π) 0 / (2 - α) + 2 * π
    rw [min_eq_right hαπ.le, max_eq_left (by linarith), min_eq_left (by positivity),
      max_eq_right (by nlinarith)]
    field_simp
    ring
  · intro z
    exact s11_pow_polar_comp (ρ₁ := fun r => r ^ α) (Φ₁ := hpPowerAngle α)
      (ρ₂ := fun r => r ^ α⁻¹)
      (Φ₂ := fun θ => min θ (α * π) / α + max (θ - α * π) 0 / (2 - α))
      (fun r hr => Real.rpow_pos_of_pos hr α) (Real.zero_rpow hα.ne')
      (Real.zero_rpow (inv_ne_zero hα.ne')) (fun r hr => Real.rpow_rpow_inv hr.le hα.ne')
      (fun θ h0 h2π => ⟨(s11_pow_angle_inv h1 h2 h0 h2π).1.1, (s11_pow_angle_inv h1 h2 h0 h2π).1.2.1⟩)
      (fun θ h0 h2π => (s11_pow_angle_inv h1 h2 h0 h2π).1.2.2) z
  · intro w
    exact s11_pow_polar_comp (ρ₁ := fun r => r ^ α⁻¹)
      (Φ₁ := fun θ => min θ (α * π) / α + max (θ - α * π) 0 / (2 - α))
      (ρ₂ := fun r => r ^ α) (Φ₂ := hpPowerAngle α)
      (fun r hr => Real.rpow_pos_of_pos hr _) (Real.zero_rpow (inv_ne_zero hα.ne'))
      (Real.zero_rpow hα.ne') (fun r hr => Real.rpow_inv_rpow hr.le hα.ne')
      (fun θ h0 h2π => ⟨(s11_pow_angle_inv h1 h2 h0 h2π).2.1, (s11_pow_angle_inv h1 h2 h0 h2π).2.2.1⟩)
      (fun θ h0 h2π => (s11_pow_angle_inv h1 h2 h0 h2π).2.2.2) w

theorem s11_pow_upper {α : ℝ} (h1 : 1 < α) (h2 : α < 2) :
    EqOn (hpPowerExt α) (fun z => z ^ (α : ℂ)) upperHalf ∧ IsKQC (hpPowerExt α) upperHalf 1 := by
  have hEq : EqOn (hpPowerExt α) (fun z => z ^ (α : ℂ)) upperHalf := by
    intro z hz
    have him : 0 < z.im := hz
    have hz0 : z ≠ 0 := fun h => by rw [h, zero_im] at him; exact lt_irrefl _ him
    have hA : hpAngle z = arg z := if_pos (Complex.arg_nonneg_iff.mpr him.le)
    have hP : hpPowerAngle α (arg z) = α * arg z := if_pos (Complex.arg_le_pi z)
    show hpPowerExt α z = z ^ (α : ℂ)
    rw [s11_pow_cpow_polar hz0]
    unfold hpPowerExt
    rw [hA, hP]
  obtain ⟨g, -, hl, -⟩ := s11_pow_inverse h1 h2
  have hd : DifferentiableOn ℂ (fun z : ℂ => z ^ (α : ℂ)) upperHalf := fun z hz =>
    (hasStrictDerivAt_cpow_const (c := (α : ℂ)) (Or.inr (show z.im ≠ 0 from (show 0 < z.im from hz).ne'))).hasDerivAt.differentiableAt.differentiableWithinAt
  exact ⟨hEq, isKQC_one_of_conformal isOpen_upperHalf ⟨hd.congr hEq, hl.injective.injOn, rfl⟩⟩

/-- Helper: on `𝕃`, `T z = z · conj(z^{α-1})`. -/
theorem s11_pow_lower_conj {α : ℝ} {z : ℂ} (hz : z ∈ lowerHalf) :
    hpPowerExt α z = z * conj (z ^ ((α - 1 : ℝ) : ℂ)) := by
  have him : z.im < 0 := hz
  have hz0 : z ≠ 0 := fun h => by rw [h, zero_im] at him; exact lt_irrefl _ him
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hL : hpPowerExt α z = ((‖z‖ ^ α : ℝ) : ℂ) * exp ((((2 - α) * arg z : ℝ) : ℂ) * I) := by
    rw [s11_pow_lower_eq hz, s11_pow_cpow_polar hz0, ← mul_assoc, ← ofReal_mul, ← Real.rpow_add hr,
      show 2 * α - 2 + (2 - α) = α by ring]
  have hz' : z = ((‖z‖ : ℝ) : ℂ) * exp ((arg z : ℂ) * I) := (Complex.norm_mul_exp_arg_mul_I z).symm
  have hR : z * conj (z ^ ((α - 1 : ℝ) : ℂ)) =
      ((‖z‖ ^ α : ℝ) : ℂ) * exp ((((2 - α) * arg z : ℝ) : ℂ) * I) := by
    rw [s11_pow_cpow_polar hz0, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    calc z * (((‖z‖ ^ (α - 1) : ℝ) : ℂ) * exp ((((α - 1) * arg z : ℝ) : ℂ) * -I))
        = (((‖z‖ : ℝ) : ℂ) * exp ((arg z : ℂ) * I)) *
            (((‖z‖ ^ (α - 1) : ℝ) : ℂ) * exp ((((α - 1) * arg z : ℝ) : ℂ) * -I)) := by
          rw [← hz']
      _ = ((‖z‖ * ‖z‖ ^ (α - 1) : ℝ) : ℂ) *
            exp ((arg z : ℂ) * I + (((α - 1) * arg z : ℝ) : ℂ) * -I) := by
          rw [Complex.exp_add]
          push_cast
          ring
      _ = _ := by
          rw [show ‖z‖ * ‖z‖ ^ (α - 1) = ‖z‖ ^ α by
            rw [mul_comm, ← Real.rpow_add_one hr.ne', sub_add_cancel]]
          congr 2
          push_cast
          ring
  rw [hL, hR]

theorem s11_pow_lower_qc {α : ℝ} (h1 : 1 < α) (h2 : α < 2) :
    IsC1Quasiconformal (hpPowerExt α) lowerHalf (α / (2 - α)) := by
  obtain ⟨g, hgc, hl, -⟩ := s11_pow_inverse h1 h2
  have hLo : IsOpen lowerHalf := isOpen_lt Complex.continuous_im continuous_const
  have h2α : 0 < 2 - α := by linarith
  have hK : 1 ≤ α / (2 - α) := (le_div_iff₀ h2α).mpr (by linarith)
  set c : ℂ := ((α - 1 : ℝ) : ℂ) with hc
  set F : ℂ → ℂ := fun u => u * conj (u ^ c) with hF
  have hTF : EqOn (hpPowerExt α) F lowerHalf := fun z hz => s11_pow_lower_conj hz
  have hslit : ∀ z ∈ lowerHalf, z ∈ slitPlane := fun z hz =>
    Or.inr (show z.im ≠ 0 from (show z.im < 0 from hz).ne)
  have hcpA : ∀ z ∈ lowerHalf, AnalyticAt ℂ (fun u : ℂ => u ^ c) z := fun z hz =>
    DifferentiableOn.analyticAt (s := slitPlane)
      (fun u hu => (hasStrictDerivAt_cpow_const (c := c) hu).hasDerivAt.differentiableAt.differentiableWithinAt)
      (Complex.isOpen_slitPlane.mem_nhds (hslit z hz))
  have hFc : ContDiffOn ℝ 1 F lowerHalf := fun z hz =>
    (contDiffAt_id.mul (Complex.conjCLE.contDiff.contDiffAt.comp z
      (((hcpA z hz).contDiffAt (n := 1)).restrict_scalars ℝ))).contDiffWithinAt
  refine ⟨hLo, hK, hFc.congr hTF, s11_pow_homeoOnto (s11_pow_continuous (by linarith)) hgc hl _,
    fun z hz => ?_⟩
  have him : z.im < 0 := hz
  have hz0 : z ≠ 0 := fun h => by rw [h, zero_im] at him; exact lt_irrefl _ him
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set d : ℂ := c * z ^ (c - 1) with hd
  have hFd : HasFDerivAt F
      ((z • (Complex.conjCLE.toContinuousLinearMap.comp
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ))) +
        conj (z ^ c) • ContinuousLinearMap.id ℝ ℂ) z :=
    (hasFDerivAt_id z).mul (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z
      ((hasStrictDerivAt_cpow_const (c := c) (hslit z hz)).hasDerivAt.hasFDerivAt.restrictScalars ℝ))
  have hTz : fderiv ℝ (hpPowerExt α) z = fderiv ℝ F z :=
    (show hpPowerExt α =ᶠ[𝓝 z] F from Filter.eventually_of_mem (hLo.mem_nhds hz) hTF).fderiv_eq
  have hv : ∀ v : ℂ, fderiv ℝ (hpPowerExt α) z v = z * conj (v * d) + conj (z ^ c) * v := by
    intro v
    rw [hTz, hFd.fderiv]
    simp [smul_eq_mul]
  have hdz : dz (hpPowerExt α) z = conj (z ^ c) := by
    unfold dz
    rw [hv, hv]
    simp only [map_mul, Complex.conj_I, map_one]
    linear_combination ((z * conj d - conj (z ^ c)) / 2) * Complex.I_sq
  have hdzbar : dzbar (hpPowerExt α) z = z * conj d := by
    unfold dzbar
    rw [hv, hv]
    simp only [map_mul, Complex.conj_I, map_one]
    linear_combination ((conj (z ^ c) - z * conj d) / 2) * Complex.I_sq
  have hN : 0 < ‖z‖ ^ (α - 1) := Real.rpow_pos_of_pos hr _
  have hndz : ‖dz (hpPowerExt α) z‖ = ‖z‖ ^ (α - 1) := by
    rw [hdz, Complex.norm_conj, hc, s11_pow_norm_cpow hz0]
  have hndzbar : ‖dzbar (hpPowerExt α) z‖ = (α - 1) * ‖z‖ ^ (α - 1) := by
    have hc1 : c - 1 = ((α - 2 : ℝ) : ℂ) := by rw [hc]; push_cast; ring
    rw [hdzbar, norm_mul, Complex.norm_conj, hd, norm_mul, hc1, s11_pow_norm_cpow hz0, hc,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [show α - 1 = α - 2 + 1 by ring, Real.rpow_add_one hr.ne']
    ring
  have hμ : ‖complexDilatation (hpPowerExt α) z‖ = α - 1 := by
    unfold complexDilatation
    rw [norm_div, hndz, hndzbar]
    field_simp
  refine ⟨?_, ?_⟩
  · rw [hndz, hndzbar]
    nlinarith
  · unfold dilatationQuotient
    rw [hμ, show 1 + (α - 1) = α by ring, show 1 - (α - 1) = 2 - α by ring]

theorem s11_pow_not_uc {α : ℝ} (h1 : 1 < α) (h2 : α < 2) (R : ℝ) :
    ¬ UniformContinuousOn (fun z : ℂ => z ^ (α : ℂ)) {z | z ∈ upperHalf ∧ R < ‖z‖} := by
  intro hU
  rw [Metric.uniformContinuousOn_iff] at hU
  obtain ⟨δ, hδ, hδU⟩ := hU 1 one_pos
  set h : ℝ := δ / 2 with hh
  have hh0 : 0 < h := by positivity
  obtain ⟨y, hy⟩ := (((tendsto_rpow_atTop (by linarith : (0 : ℝ) < α - 1)).eventually_ge_atTop
    (1 / h)).and ((eventually_gt_atTop R).and (eventually_ge_atTop 1))).exists
  obtain ⟨hyh, hyR, hy1⟩ := hy
  have hy0 : 0 < y := by linarith
  -- the values on the imaginary axis
  have himag : ∀ t : ℝ, 0 < t →
      ((t : ℂ) * I) ^ (α : ℂ) = ((t ^ α : ℝ) : ℂ) * exp (((α * (π / 2) : ℝ) : ℂ) * I) := by
    intro t ht
    have ht0 : (t : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr ht.ne') I_ne_zero
    rw [s11_pow_cpow_polar ht0, Complex.arg_real_mul _ ht, Complex.arg_I, norm_mul, Complex.norm_I,
      mul_one, Complex.norm_real, Real.norm_of_nonneg ht.le]
  have hmem : ∀ t : ℝ, R < t → 0 < t → (t : ℂ) * I ∈ {z : ℂ | z ∈ upperHalf ∧ R < ‖z‖} := by
    intro t htR ht
    refine ⟨show 0 < ((t : ℂ) * I).im by simpa using ht, ?_⟩
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg ht.le]
    exact htR
  have hdist : dist ((y : ℂ) * I) (((y + h : ℝ) : ℂ) * I) < δ := by
    rw [dist_eq_norm, ← sub_mul, norm_mul, Complex.norm_I, mul_one, ← ofReal_sub, Complex.norm_real,
      show y - (y + h) = -h by ring, norm_neg, Real.norm_of_nonneg hh0.le]
    linarith
  have key := hδU _ (hmem y hyR hy0) _ (hmem (y + h) (by linarith) (by linarith)) hdist
  rw [himag y hy0, himag (y + h) (by linarith), dist_eq_norm, ← sub_mul, ← ofReal_sub, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at key
  -- `(y + h)^α - y^α ≥ h y^{α-1} ≥ 1`
  have hmono : y ^ (α - 1) ≤ (y + h) ^ (α - 1) :=
    Real.rpow_le_rpow hy0.le (by linarith) (by linarith)
  have e1 : (y + h) ^ α = (y + h) ^ (α - 1) * (y + h) := by
    rw [← Real.rpow_add_one (by linarith : y + h ≠ 0), sub_add_cancel]
  have e2 : y ^ α = y ^ (α - 1) * y := by
    rw [← Real.rpow_add_one hy0.ne', sub_add_cancel]
  have hge : 1 ≤ (y + h) ^ α - y ^ α := by
    have h3 : 1 ≤ h * y ^ (α - 1) := by
      rw [div_le_iff₀ hh0] at hyh
      linarith [mul_comm h (y ^ (α - 1))]
    rw [e1, e2]
    nlinarith [Real.rpow_nonneg hy0.le (α - 1)]
  rw [abs_sub_comm] at key
  linarith [le_abs_self ((y + h) ^ α - y ^ α)]

/-- Remark `rem:hp-infinity`(iii), `sec11-halfplane.tex:285–291`: for `1 < α < 2` the map
`hpPowerExt α` is a quasiconformal homeomorphism of `ℂ` (with maximal dilatation `α/(2-α)`)
extending `f(z) = z^α` on `ℍ`, and `f` is not uniformly continuous near `∞`. -/
theorem rem_hp_infinity_iii {α : ℝ} (h1 : 1 < α) (h2 : α < 2) :
    IsKQC (hpPowerExt α) univ (α / (2 - α)) ∧ hpPowerExt α '' univ = univ ∧
      EqOn (hpPowerExt α) (fun z => z ^ (α : ℂ)) upperHalf ∧
      ∀ R : ℝ, ¬ UniformContinuousOn (fun z : ℂ => z ^ (α : ℂ)) {z | z ∈ upperHalf ∧ R < ‖z‖} := by
  obtain ⟨g, hgc, hl, hr⟩ := s11_pow_inverse h1 h2
  have hTc := s11_pow_continuous (by linarith : (0 : ℝ) < α)
  have h2α : 0 < 2 - α := by linarith
  have hK : 1 ≤ α / (2 - α) := (le_div_iff₀ h2α).mpr (by linarith)
  let E : ℂ ≃ₜ ℂ := ⟨⟨hpPowerExt α, g, hl, hr⟩, hTc, hgc⟩
  obtain ⟨hEq, hU⟩ := s11_pow_upper h1 h2
  have hG : IsKQC E univ (α / (2 - α)) :=
    lem_hp_gluing E (by exact hU.mono hK) (by exact isKQC_of_isC1Quasiconformal (s11_pow_lower_qc h1 h2))
  refine ⟨hG, ?_, hEq, s11_pow_not_uc h1 h2⟩
  rw [image_univ]
  exact hr.surjective.range_eq

/-! ## The kernel test -/

/-- Helper for `lem_hp_kernel_a`: `k_a(z) = 4 Im a Im z / |z - ā|²`. -/
theorem hpKernel_eq {a z : ℂ} (ha : a ∈ upperHalf) (hz : z ∈ upperHalf) :
    hpKernel a z = 4 * a.im * z.im / ‖z - conj a‖ ^ 2 := by
  have ht : 0 < a.im := ha
  have hy : 0 < z.im := hz
  have hX : Real.cosh (hpDist a z) = 1 + ‖a - z‖ ^ 2 / (2 * a.im * z.im) := by
    unfold hpDist
    rw [Real.cosh_arcosh]
    have : 0 ≤ ‖a - z‖ ^ 2 / (2 * a.im * z.im) := by positivity
    linarith
  have hc : Real.cosh (hpDist a z / 2) ^ 2 = (1 + Real.cosh (hpDist a z)) / 2 := by
    have h1 := Real.cosh_two_mul (hpDist a z / 2)
    rw [show 2 * (hpDist a z / 2) = hpDist a z by ring] at h1
    have h2 := Real.cosh_sq (hpDist a z / 2)
    linarith
  have hn : ‖z - conj a‖ ^ 2 = ‖a - z‖ ^ 2 + 4 * a.im * z.im := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
    ring
  unfold hpKernel
  rw [inv_pow, hc, hX, hn]
  have : 0 ≤ ‖a - z‖ ^ 2 := by positivity
  field_simp
  ring

/-- Lemma 11.3(a) `lem:hp-kernel`, `sec11-halfplane.tex:308`: `k_a(z) = 4 t y / |z - ā|²` and
`𝒫_m(a) = 4t ∫ dλ(x+iy)/((x-u)² + (y+t)²)`. -/
theorem lem_hp_kernel_a (m : Measure ℂ) {a : ℂ} (ha : a ∈ upperHalf) :
    (∀ z ∈ upperHalf, hpKernel a z = 4 * a.im * z.im / ‖z - conj a‖ ^ 2) ∧
      hpP m a = ∫⁻ z in upperHalf,
        ENNReal.ofReal (4 * a.im / ((z.re - a.re) ^ 2 + (z.im + a.im) ^ 2)) ∂hpWeight m := by
  refine ⟨fun z hz => hpKernel_eq ha hz, ?_⟩
  have hU : MeasurableSet upperHalf := measurableSet_lt measurable_const Complex.measurable_im
  unfold hpP hpWeight
  rw [restrict_withDensity hU, lintegral_withDensity_eq_lintegral_mul _
    Complex.measurable_im.ennreal_ofReal (Measurable.ennreal_ofReal (by fun_prop))]
  refine setLIntegral_congr_fun hU fun z hz => ?_
  have ht : 0 < a.im := ha
  have hy : 0 < z.im := hz
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul hy.le, hpKernel_eq ha hz]
  congr 1
  have hn : ‖z - conj a‖ ^ 2 = (z.re - a.re) ^ 2 + (z.im + a.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [hn]
  ring

/-- Lemma 11.3(b) `lem:hp-kernel`, `sec11-halfplane.tex:311`: `λ(Q_I)/|I| ≤ (17/16) 𝒫_m(u + i|I|)`
for `I` centered at `u`. -/
theorem lem_hp_kernel_b (m : Measure ℂ) {c ℓ : ℝ} (hℓ : 0 < ℓ) :
    hpWeight m (hpBox c ℓ) / ENNReal.ofReal ℓ ≤ (17 / 16 : ℝ≥0∞) * hpP m ⟨c, ℓ⟩ := by
  have ha : (⟨c, ℓ⟩ : ℂ) ∈ upperHalf := hℓ
  rw [(lem_hp_kernel_a m ha).2]
  set G : ℂ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (4 * (⟨c, ℓ⟩ : ℂ).im / ((z.re - (⟨c, ℓ⟩ : ℂ).re) ^ 2 + (z.im + (⟨c, ℓ⟩ : ℂ).im) ^ 2))
  have hG : Measurable G := Measurable.ennreal_ofReal (by fun_prop)
  have hQU : hpBox c ℓ ⊆ upperHalf := fun z hz => hz.2.1
  have hlow : ∀ z ∈ hpBox c ℓ, ENNReal.ofReal (16 / (17 * ℓ)) ≤ G z := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hz
    simp only [G]
    apply ENNReal.ofReal_le_ofReal
    have hx : (z.re - c) ^ 2 ≤ ℓ ^ 2 / 4 := by
      have := abs_le.mp h1
      nlinarith
    have hyl : (z.im + ℓ) ^ 2 ≤ 4 * ℓ ^ 2 := by nlinarith
    have hd : 0 < (z.re - c) ^ 2 + (z.im + ℓ) ^ 2 := by positivity
    rw [div_le_div_iff₀ (by positivity) hd]
    nlinarith
  have hint : ENNReal.ofReal (16 / (17 * ℓ)) * hpWeight m (hpBox c ℓ) ≤
      ∫⁻ z in upperHalf, G z ∂hpWeight m := by
    calc ENNReal.ofReal (16 / (17 * ℓ)) * hpWeight m (hpBox c ℓ)
        = ∫⁻ _ in hpBox c ℓ, ENNReal.ofReal (16 / (17 * ℓ)) ∂hpWeight m :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ z in hpBox c ℓ, G z ∂hpWeight m := setLIntegral_mono hG hlow
      _ ≤ ∫⁻ z in upperHalf, G z ∂hpWeight m := lintegral_mono_set hQU
  have e : (17 / 16 : ℝ≥0∞) * ENNReal.ofReal (16 / (17 * ℓ)) = (ENNReal.ofReal ℓ)⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos hℓ,
      show (17 / 16 : ℝ≥0∞) = ENNReal.ofReal (17 / 16) by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    field_simp
  calc hpWeight m (hpBox c ℓ) / ENNReal.ofReal ℓ
      = (17 / 16 : ℝ≥0∞) * (ENNReal.ofReal (16 / (17 * ℓ)) * hpWeight m (hpBox c ℓ)) := by
        rw [← mul_assoc, e, ENNReal.div_eq_inv_mul]
    _ ≤ (17 / 16 : ℝ≥0∞) * ∫⁻ z in upperHalf, G z ∂hpWeight m := by gcongr

/-- (11.?) `eq:hp-shells`, Lemma 11.3(b), `sec11-halfplane.tex:312`:
`𝒫_m(a) ≤ 32 Σ_{n≥0} 2^{-n} ε_λ(2^{n+1} t)`. -/
theorem eq_hp_shells (m : Measure ℂ) {a : ℂ} (ha : a ∈ upperHalf) :
    hpP m a ≤ 32 * ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n * hpEps (hpWeight m) (2 ^ (n + 1) * a.im) := by
  have ht : 0 < a.im := ha
  set G : ℂ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (4 * a.im / ((z.re - a.re) ^ 2 + (z.im + a.im) ^ 2)) with hG
  set B : ℕ → Set ℂ := fun n => hpBox a.re (2 ^ (n + 1) * a.im) with hB
  set D : ℕ → Set ℂ := fun n => {z | z ∈ B n ∧ ∀ k < n, z ∉ B k} with hD
  have hcover : upperHalf ⊆ ⋃ n, D n := by
    intro z hz
    have hy : 0 < z.im := hz
    have hex : ∃ n, z ∈ B n := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((|z.re - a.re| + z.im) / a.im)
        (by norm_num : (1 : ℝ) < 2)
      rw [div_lt_iff₀ ht] at hn
      have hp : 0 < (2 : ℝ) ^ n * a.im := by positivity
      refine ⟨n, ?_, hy, ?_⟩
      · rw [show (2 : ℝ) ^ (n + 1) * a.im / 2 = 2 ^ n * a.im by ring]
        linarith [abs_nonneg (z.re - a.re)]
      · rw [show (2 : ℝ) ^ (n + 1) * a.im = 2 * (2 ^ n * a.im) by ring]
        linarith [abs_nonneg (z.re - a.re)]
    classical
    exact mem_iUnion.mpr ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have key : ∀ n, ∀ z ∈ D n,
      ((2 : ℝ) ^ n * a.im) ^ 2 / 4 ≤ (z.re - a.re) ^ 2 + (z.im + a.im) ^ 2 := by
    intro n z hz
    obtain ⟨hzB, hmin⟩ := hz
    have hy : 0 < z.im := hzB.2.1
    cases n with
    | zero =>
      simp only [pow_zero, one_mul]
      nlinarith [sq_nonneg (z.re - a.re)]
    | succ k =>
      have hk := hmin k (Nat.lt_succ_self k)
      have hk' : ¬ (|z.re - a.re| ≤ 2 ^ k * a.im ∧ z.im ≤ 2 ^ (k + 1) * a.im) := by
        rintro ⟨h1, h2⟩
        exact hk ⟨by rw [show (2 : ℝ) ^ (k + 1) * a.im / 2 = 2 ^ k * a.im by ring]; exact h1,
          hy, h2⟩
      rw [not_and_or, not_le, not_le] at hk'
      have hpk : 0 < (2 : ℝ) ^ k * a.im := by positivity
      have e : (2 : ℝ) ^ (k + 1) * a.im = 2 * (2 ^ k * a.im) := by ring
      rcases hk' with h | h
      · have hx : (2 ^ k * a.im) ^ 2 ≤ (z.re - a.re) ^ 2 := by
          rw [← sq_abs (z.re - a.re)]
          exact pow_le_pow_left₀ hpk.le h.le 2
        rw [e]
        nlinarith [sq_nonneg (z.im + a.im)]
      · rw [e] at h ⊢
        nlinarith [sq_nonneg (z.re - a.re)]
  have hterm : ∀ n, ∫⁻ z in D n, G z ∂hpWeight m ≤
      32 * ((2 : ℝ≥0∞)⁻¹ ^ n * hpEps (hpWeight m) (2 ^ (n + 1) * a.im)) := by
    intro n
    have hq : (0 : ℝ) < 2 ^ n := by positivity
    have hℓ : (0 : ℝ) < 2 ^ (n + 1) * a.im := by positivity
    have hpt : ∀ z ∈ D n, G z ≤ ENNReal.ofReal (16 / ((2 ^ n) ^ 2 * a.im)) := by
      intro z hz
      have hk := key n z hz
      have hy : 0 < z.im := hz.1.2.1
      have hden : 0 < (z.re - a.re) ^ 2 + (z.im + a.im) ^ 2 := by positivity
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_div_iff₀ hden (by positivity)]
      nlinarith
    have hBn : hpWeight m (B n) ≤
        hpEps (hpWeight m) (2 ^ (n + 1) * a.im) * ENNReal.ofReal (2 ^ (n + 1) * a.im) := by
      have h1 : hpWeight m (B n) / ENNReal.ofReal (2 ^ (n + 1) * a.im) ≤
          hpEps (hpWeight m) (2 ^ (n + 1) * a.im) := by
        unfold hpEps
        exact le_iSup₂_of_le a.re (2 ^ (n + 1) * a.im) (le_iSup₂_of_le hℓ le_rfl le_rfl)
      exact (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hℓ).ne' ENNReal.ofReal_ne_top).mp h1
    have h2n : ENNReal.ofReal (2 ^ n) = 2 ^ n := by
      rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    calc ∫⁻ z in D n, G z ∂hpWeight m
        ≤ ∫⁻ _ in D n, ENNReal.ofReal (16 / ((2 ^ n) ^ 2 * a.im)) ∂hpWeight m :=
          setLIntegral_mono measurable_const hpt
      _ = ENNReal.ofReal (16 / ((2 ^ n) ^ 2 * a.im)) * hpWeight m (D n) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (16 / ((2 ^ n) ^ 2 * a.im)) * hpWeight m (B n) := by
          gcongr
          exact fun z hz => hz.1
      _ ≤ ENNReal.ofReal (16 / ((2 ^ n) ^ 2 * a.im)) *
          (hpEps (hpWeight m) (2 ^ (n + 1) * a.im) * ENNReal.ofReal (2 ^ (n + 1) * a.im)) := by
          gcongr
      _ = ENNReal.ofReal (16 / ((2 ^ n) ^ 2 * a.im) * (2 ^ (n + 1) * a.im)) *
          hpEps (hpWeight m) (2 ^ (n + 1) * a.im) := by
          rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 16 / ((2 ^ n) ^ 2 * a.im) by positivity)]
          ring
      _ = 32 * ((2 : ℝ≥0∞)⁻¹ ^ n * hpEps (hpWeight m) (2 ^ (n + 1) * a.im)) := by
          rw [show 16 / (((2 : ℝ) ^ n) ^ 2 * a.im) * (2 ^ (n + 1) * a.im) = 32 / 2 ^ n by
            rw [pow_succ]; field_simp; ring]
          rw [ENNReal.ofReal_div_of_pos hq, ENNReal.ofReal_ofNat, h2n, div_eq_mul_inv,
            ENNReal.inv_pow]
          ring
  calc hpP m a = ∫⁻ z in upperHalf, G z ∂hpWeight m := (lem_hp_kernel_a m ha).2
    _ ≤ ∫⁻ z in ⋃ n, D n, G z ∂hpWeight m := lintegral_mono_set hcover
    _ ≤ ∑' n, ∫⁻ z in D n, G z ∂hpWeight m := lintegral_iUnion_le _ _
    _ ≤ ∑' n, 32 * ((2 : ℝ≥0∞)⁻¹ ^ n * hpEps (hpWeight m) (2 ^ (n + 1) * a.im)) :=
        ENNReal.tsum_le_tsum hterm
    _ = _ := ENNReal.tsum_mul_left

/-- Lemma 11.3(b) `lem:hp-kernel`, `sec11-halfplane.tex:315`:
`‖λ‖_CM ≤ (17/16) sup 𝒫_m` and `sup 𝒫_m ≤ 64 ‖λ‖_CM`. -/
theorem lem_hp_kernel_b_norm (m : Measure ℂ) :
    hpCMNorm (hpWeight m) ≤ (17 / 16 : ℝ≥0∞) * ⨆ (a : ℂ) (_ : a ∈ upperHalf), hpP m a ∧
      ⨆ (a : ℂ) (_ : a ∈ upperHalf), hpP m a ≤ 64 * hpCMNorm (hpWeight m) := by
  constructor
  · unfold hpCMNorm
    refine iSup₂_le fun c ℓ => iSup_le fun hℓ => ?_
    calc hpWeight m (hpBox c ℓ) / ENNReal.ofReal ℓ ≤ (17 / 16 : ℝ≥0∞) * hpP m ⟨c, ℓ⟩ :=
          lem_hp_kernel_b m hℓ
      _ ≤ (17 / 16 : ℝ≥0∞) * ⨆ (a : ℂ) (_ : a ∈ upperHalf), hpP m a := by
          gcongr
          exact le_iSup₂_of_le (⟨c, ℓ⟩ : ℂ) (show (⟨c, ℓ⟩ : ℂ) ∈ upperHalf from hℓ) le_rfl
  · refine iSup₂_le fun a ha => ?_
    calc hpP m a ≤ 32 * ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n * hpEps (hpWeight m) (2 ^ (n + 1) * a.im) :=
          eq_hp_shells m ha
      _ ≤ 32 * ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n * hpCMNorm (hpWeight m) :=
          mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum fun n =>
            mul_le_mul_of_nonneg_left ((hp_eps_mono_le _).2 _) zero_le) zero_le
      _ = 64 * hpCMNorm (hpWeight m) := by
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric_two, ← mul_assoc]
          norm_num

/-- Helper: `lem_hp_kernel_d`, stated before `lem_hp_kernel_c`, which uses it. -/
theorem hp_kernel_d_aux (m : Measure ℂ) (hm : IsHPCarleson (hpWeight m)) {r δ : ℝ} (hr : 0 < r)
    (hrδ : r < δ) :
    hpSupLow (hpP m) r ≤
      64 * hpEps (hpWeight m) δ + 128 * hpCMNorm (hpWeight m) * ENNReal.ofReal (r / δ) := by
  have hδ : 0 < δ := hr.trans hrδ
  unfold hpSupLow
  refine iSup₂_le fun a ha => iSup_le fun har => ?_
  have ht : 0 < a.im := ha
  have hex : ∃ n : ℕ, δ < 2 ^ (n + 1) * a.im := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (δ / a.im) (by norm_num : (1 : ℝ) < 2)
    rw [div_lt_iff₀ ht] at hn
    refine ⟨n, ?_⟩
    have : (0 : ℝ) < 2 ^ n * a.im := by positivity
    nlinarith [pow_succ (2 : ℝ) n]
  classical
  set N := Nat.find hex with hNdef
  have hN : δ < 2 ^ (N + 1) * a.im := Nat.find_spec hex
  have hlt : ∀ n < N, 2 ^ (n + 1) * a.im ≤ δ := fun n hn => not_lt.mp (Nat.find_min hex hn)
  set e := hpEps (hpWeight m) δ
  set c := hpCMNorm (hpWeight m)
  set f : ℕ → ℝ≥0∞ := fun n => (2 : ℝ≥0∞)⁻¹ ^ n * hpEps (hpWeight m) (2 ^ (n + 1) * a.im)
  have hsplit : ∑' n, f n = ∑ n ∈ Finset.range N, f n + ∑' k, f (k + N) :=
    (ENNReal.summable.hasSum.sum_range_add).tsum_eq
  have hhead : ∑ n ∈ Finset.range N, f n ≤ 2 * e := by
    calc ∑ n ∈ Finset.range N, f n ≤ ∑ n ∈ Finset.range N, (2 : ℝ≥0∞)⁻¹ ^ n * e :=
          Finset.sum_le_sum fun n hn =>
            mul_le_mul_of_nonneg_left ((hp_eps_mono_le _).1 (hlt n (Finset.mem_range.mp hn))) zero_le
      _ ≤ ∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * e := ENNReal.sum_le_tsum _
      _ = 2 * e := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric_two]
  have hpowN : (2 : ℝ≥0∞)⁻¹ ^ N ≤ 2 * ENNReal.ofReal (r / δ) := by
    have h2N : ((2 : ℝ≥0∞)⁻¹) ^ N = ENNReal.ofReal (((2 : ℝ) ^ N)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_ofNat, ENNReal.inv_pow]
    rw [h2N, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    have : (2 : ℝ) ^ (N + 1) * a.im ≤ 2 ^ (N + 1) * r := by gcongr
    calc (1 : ℝ) ≤ (2 ^ (N + 1) * r) / δ := by rw [le_div_iff₀ hδ]; linarith
      _ = _ := by rw [pow_succ]; ring
  have htail : ∑' k, f (k + N) ≤ 4 * (ENNReal.ofReal (r / δ) * c) := by
    calc ∑' k, f (k + N) ≤ ∑' k, (2 : ℝ≥0∞)⁻¹ ^ k * ((2 : ℝ≥0∞)⁻¹ ^ N * c) :=
          ENNReal.tsum_le_tsum fun k => by
            simp only [f]
            rw [pow_add, mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left ((hp_eps_mono_le _).2 _) zero_le) zero_le
      _ = 2 * ((2 : ℝ≥0∞)⁻¹ ^ N * c) := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric_two]
      _ ≤ 2 * ((2 * ENNReal.ofReal (r / δ)) * c) := by gcongr
      _ = 4 * (ENNReal.ofReal (r / δ) * c) := by ring
  calc hpP m a ≤ 32 * ∑' n, f n := eq_hp_shells m ha
    _ = 32 * (∑ n ∈ Finset.range N, f n + ∑' k, f (k + N)) := by rw [hsplit]
    _ ≤ 32 * (2 * e + 4 * (ENNReal.ofReal (r / δ) * c)) := by gcongr
    _ = 64 * e + 128 * c * ENNReal.ofReal (r / δ) := by ring

/-- Lemma 11.3(c) `lem:hp-kernel`, `sec11-halfplane.tex:317`: `λ ∈ CM₀(ℍ)` iff `λ ∈ CM(ℍ)` and
`sup_{Im a ≤ r} 𝒫_m(a) → 0`. -/
theorem lem_hp_kernel_c (m : Measure ℂ) :
    IsHPVanishingCarleson (hpWeight m) ↔
      IsHPCarleson (hpWeight m) ∧ Tendsto (hpSupLow (hpP m)) (𝓝[>] 0) (𝓝 0) := by
  constructor
  · rintro ⟨hC, hT⟩
    refine ⟨hC, ?_⟩
    rw [ENNReal.tendsto_nhds_zero] at hT ⊢
    intro ε hε
    have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
    have hε' : 0 < ε / 2 / 64 := ENNReal.div_pos hε2.ne' (by norm_num)
    obtain ⟨δ, hδ, hδpos⟩ := ((hT _ hε').and self_mem_nhdsWithin).exists
    have hδ0 : 0 < δ := hδpos
    have hlim : Tendsto (fun r => 128 * hpCMNorm (hpWeight m) * ENNReal.ofReal (r / δ))
        (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun r : ℝ => ENNReal.ofReal (r / δ)) (𝓝[>] 0) (𝓝 0) := by
        have := (ENNReal.continuous_ofReal.tendsto _).comp
          ((continuous_id.div_const δ).tendsto (0 : ℝ))
        simpa [Function.comp_def] using this.mono_left nhdsWithin_le_nhds
      have h2 := ENNReal.Tendsto.const_mul h1
        (Or.inr (ENNReal.mul_ne_top (by norm_num : (128 : ℝ≥0∞) ≠ ⊤) hC))
      simpa using h2
    filter_upwards [ENNReal.tendsto_nhds_zero.mp hlim _ hε2, Ioo_mem_nhdsGT hδ0] with r hr1 hr2
    calc hpSupLow (hpP m) r
        ≤ 64 * hpEps (hpWeight m) δ + 128 * hpCMNorm (hpWeight m) * ENNReal.ofReal (r / δ) :=
          hp_kernel_d_aux m hC hr2.1 hr2.2
      _ ≤ 64 * (ε / 2 / 64) + ε / 2 := add_le_add (mul_le_mul_of_nonneg_left hδ zero_le) hr1
      _ = ε / 2 + ε / 2 := by rw [ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
      _ = ε := ENNReal.add_halves ε
  · rintro ⟨hC, hT⟩
    refine ⟨hC, ?_⟩
    have hle : ∀ r, hpEps (hpWeight m) r ≤ 17 / 16 * hpSupLow (hpP m) r := by
      intro r
      unfold hpEps
      refine iSup₂_le fun c ℓ => iSup₂_le fun hℓ hℓr => ?_
      refine (lem_hp_kernel_b m hℓ).trans (mul_le_mul_of_nonneg_left ?_ zero_le)
      unfold hpSupLow
      exact le_iSup₂_of_le (⟨c, ℓ⟩ : ℂ) (show (⟨c, ℓ⟩ : ℂ) ∈ upperHalf from hℓ)
        (le_iSup_of_le hℓr le_rfl)
    have hT' := ENNReal.Tendsto.const_mul hT (Or.inr (ENNReal.div_lt_top (by norm_num : (17 : ℝ≥0∞) ≠ ⊤) (by norm_num : (16 : ℝ≥0∞) ≠ 0)).ne)
    rw [mul_zero] at hT'
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT'
      (fun r => zero_le) hle

/-- Lemma 11.3(c) `lem:hp-kernel`, `sec11-halfplane.tex:318, 359–367`: the hypothesis
`λ ∈ CM(ℍ)` cannot be omitted; for `m = 1_{y>1} dA_ρ`, `𝒫_m(u+it) = 4π log(1+t)` tends to `0`
uniformly, but `λ ∉ CM(ℍ)`. -/
theorem lem_hp_kernel_c_sharp :
    (∀ a ∈ upperHalf, hpP (hpArea.restrict {z | 1 < z.im}) a =
      ENNReal.ofReal (4 * π * Real.log (1 + a.im))) ∧
      Tendsto (hpSupLow (hpP (hpArea.restrict {z | 1 < z.im}))) (𝓝[>] 0) (𝓝 0) ∧
      ¬ IsHPCarleson (hpWeight (hpArea.restrict {z | 1 < z.im})) := by
  have hU : MeasurableSet upperHalf :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hS : MeasurableSet {z : ℂ | 1 < z.im} := measurableSet_lt measurable_const Complex.measurable_im
  have hP : ∀ a ∈ upperHalf, hpP (hpArea.restrict {z | 1 < z.im}) a =
      ENNReal.ofReal (4 * π * Real.log (1 + a.im)) := by
    intro a ha
    have ht : 0 < a.im := ha
    have hGm : Measurable fun z : ℂ =>
        ENNReal.ofReal (4 * a.im / (z.im * ((z.re - a.re) ^ 2 + (z.im + a.im) ^ 2))) := by
      apply Measurable.ennreal_ofReal
      exact measurable_const.div (Complex.measurable_im.mul
        (((Complex.measurable_re.sub_const _).pow_const 2).add
          ((Complex.measurable_im.add_const _).pow_const 2)))
    have step1 : hpP (hpArea.restrict {z | 1 < z.im}) a = ∫⁻ z, {z : ℂ | 1 < z.im}.indicator
        (fun z => ENNReal.ofReal (4 * a.im / (z.im * ((z.re - a.re) ^ 2 + (z.im + a.im) ^ 2)))) z := by
      unfold hpP
      rw [← lintegral_indicator hU, hp_lintegral_hpArea_restrict hS]
      congr 1
      funext z
      by_cases hz : 1 < z.im
      · have hzU : z ∈ upperHalf := show 0 < z.im by linarith
        have hy : 0 < z.im := hzU
        rw [indicator_of_mem (⟨hz, hzU⟩ : z ∈ {z : ℂ | 1 < z.im} ∩ upperHalf),
          indicator_of_mem (show z ∈ {z : ℂ | 1 < z.im} from hz)]
        rw [indicator_of_mem hzU]
        have hn : ‖z - conj a‖ ^ 2 = (z.re - a.re) ^ 2 + (z.im + a.im) ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          simp only [sub_re, sub_im, conj_re, conj_im]
          ring
        have hq : (z.re - a.re) ^ 2 + (z.im + a.im) ^ 2 ≠ 0 := by positivity
        rw [hpKernel_eq ha hzU, hn, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
      · rw [indicator_of_notMem (fun h : z ∈ {z : ℂ | 1 < z.im} ∩ upperHalf => hz h.1),
          indicator_of_notMem (show z ∉ {z : ℂ | 1 < z.im} from hz)]
    have step2 : ∫⁻ z, {z : ℂ | 1 < z.im}.indicator
        (fun z => ENNReal.ofReal (4 * a.im / (z.im * ((z.re - a.re) ^ 2 + (z.im + a.im) ^ 2)))) z =
        ∫⁻ y in Ioi (1 : ℝ), ∫⁻ x : ℝ,
          ENNReal.ofReal (4 * a.im / (y * ((x - a.re) ^ 2 + (y + a.im) ^ 2))) := by
      rw [hp_lintegral_iter (hGm.indicator hS), ← lintegral_indicator measurableSet_Ioi]
      congr 1
      funext y
      by_cases hy : 1 < y
      · rw [indicator_of_mem (show y ∈ Ioi (1 : ℝ) from hy)]
        congr 1
        funext x
        exact indicator_of_mem (show (⟨x, y⟩ : ℂ) ∈ {z : ℂ | 1 < z.im} from hy) _
      · rw [indicator_of_notMem (show y ∉ Ioi (1 : ℝ) from hy)]
        simp only [Set.indicator_apply, mem_ofPred_eq, hy, ite_false, lintegral_zero]
    rw [step1, step2]
    have step3 : ∫⁻ y in Ioi (1 : ℝ), ∫⁻ x : ℝ,
        ENNReal.ofReal (4 * a.im / (y * ((x - a.re) ^ 2 + (y + a.im) ^ 2))) =
        ∫⁻ y in Ioi (1 : ℝ), ENNReal.ofReal (4 * a.im * π / (y * (y + a.im))) := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
      have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
      exact hp_lintegral_lorentz (by positivity) hy0 (by positivity) a.re
    rw [step3, hp_lintegral_Ioi_log ht]
  refine ⟨hP, ?_, ?_⟩
  · have h0 : ContinuousAt (fun r : ℝ => 4 * π * Real.log (1 + r)) 0 :=
      continuousAt_const.mul ((continuousAt_const.add continuousAt_id).log (by norm_num))
    have hc : Tendsto (fun r : ℝ => ENNReal.ofReal (4 * π * Real.log (1 + r))) (𝓝[>] 0) (𝓝 0) := by
      have := (ENNReal.tendsto_ofReal h0.tendsto).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    unfold hpSupLow
    refine iSup₂_le fun a ha => iSup_le fun har => ?_
    rw [hP a ha]
    have ht : 0 < a.im := ha
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by linarith) (by linarith)) (by positivity))
  · have hlow : ∀ ℓ : ℝ, 1 < ℓ → ENNReal.ofReal (Real.log ℓ) ≤
        hpCMNorm (hpWeight (hpArea.restrict {z | 1 < z.im})) := by
      intro ℓ hℓ
      have hℓ0 : 0 < ℓ := by linarith
      have hQ := hp_measurableSet_box 0 ℓ
      set K : ℂ → ℝ≥0∞ := fun z => (Icc (-(ℓ / 2)) (ℓ / 2)).indicator 1 z.re *
        (Ioc 1 ℓ).indicator (fun y => ENNReal.ofReal y⁻¹) z.im with hKdef
      have hKm : Measurable K :=
        ((measurable_one.indicator measurableSet_Icc).comp Complex.measurable_re).mul
          ((measurable_inv.ennreal_ofReal.indicator measurableSet_Ioc).comp Complex.measurable_im)
      have hint : IntegrableOn (fun y : ℝ => y⁻¹) (Ioc 1 ℓ) :=
        ((continuousOn_inv₀.mono fun y (hy : y ∈ Icc 1 ℓ) =>
          (ne_of_gt (lt_of_lt_of_le one_pos hy.1) : y ≠ 0)).integrableOn_Icc).mono_set
          Ioc_subset_Icc_self
      have hKval : ∫⁻ z, K z = ENNReal.ofReal ℓ * ENNReal.ofReal (Real.log ℓ) := by
        rw [hp_lintegral_iter hKm]
        have hin : ∀ y : ℝ, ∫⁻ x : ℝ, K ⟨x, y⟩ =
            ENNReal.ofReal ℓ * (Ioc 1 ℓ).indicator (fun y => ENNReal.ofReal y⁻¹) y := by
          intro y
          show ∫⁻ x : ℝ, (Icc (-(ℓ / 2)) (ℓ / 2)).indicator 1 x *
            (Ioc 1 ℓ).indicator (fun y => ENNReal.ofReal y⁻¹) y = _
          rw [lintegral_mul_const _ (measurable_one.indicator measurableSet_Icc),
            lintegral_indicator_one measurableSet_Icc, Real.volume_Icc]
          congr 2
          ring
        simp_rw [hin]
        rw [lintegral_const_mul _ (measurable_inv.ennreal_ofReal.indicator measurableSet_Ioc),
          lintegral_indicator measurableSet_Ioc,
          ← ofReal_integral_eq_lintegral_ofReal hint
            ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun y hy =>
              (inv_pos.mpr (lt_trans one_pos hy.1)).le)),
          ← intervalIntegral.integral_of_le hℓ.le, integral_inv_of_pos one_pos hℓ0, div_one]
      have hmass : ENNReal.ofReal ℓ * ENNReal.ofReal (Real.log ℓ) ≤
          hpWeight (hpArea.restrict {z | 1 < z.im}) (hpBox 0 ℓ) := by
        unfold hpWeight
        rw [withDensity_apply _ hQ, ← lintegral_indicator hQ, hp_lintegral_hpArea_restrict hS,
          ← hKval]
        refine lintegral_mono fun z => ?_
        by_cases h : z.re ∈ Icc (-(ℓ / 2)) (ℓ / 2) ∧ z.im ∈ Ioc 1 ℓ
        · obtain ⟨hx, hy⟩ := h
          have hy0 : 0 < z.im := lt_trans one_pos hy.1
          have hzQ : z ∈ hpBox 0 ℓ := ⟨by rw [sub_zero]; exact abs_le.mpr hx, hy0, hy.2⟩
          have hzS : z ∈ {z : ℂ | 1 < z.im} ∩ upperHalf := ⟨hy.1, hy0⟩
          show (Icc (-(ℓ / 2)) (ℓ / 2)).indicator 1 z.re *
            (Ioc 1 ℓ).indicator (fun y => ENNReal.ofReal y⁻¹) z.im ≤ _
          rw [indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem hzS]
          rw [indicator_of_mem hzQ, Pi.one_apply, one_mul, ← ENNReal.ofReal_mul (by positivity)]
          apply le_of_eq
          congr 1
          rw [pow_two, mul_inv, mul_assoc, inv_mul_cancel₀ hy0.ne', mul_one]
        · have hK0 : K z = 0 := by
            show (Icc (-(ℓ / 2)) (ℓ / 2)).indicator 1 z.re *
              (Ioc 1 ℓ).indicator (fun y => ENNReal.ofReal y⁻¹) z.im = 0
            by_cases hx : z.re ∈ Icc (-(ℓ / 2)) (ℓ / 2)
            · rw [indicator_of_notMem (fun hy => h ⟨hx, hy⟩), mul_zero]
            · rw [indicator_of_notMem hx, zero_mul]
          rw [hK0]
          exact zero_le
      have hℓne : ENNReal.ofReal ℓ ≠ 0 := (ENNReal.ofReal_pos.mpr hℓ0).ne'
      calc ENNReal.ofReal (Real.log ℓ)
          = ENNReal.ofReal ℓ * ENNReal.ofReal (Real.log ℓ) / ENNReal.ofReal ℓ := by
            rw [mul_comm, ENNReal.mul_div_cancel_right hℓne ENNReal.ofReal_ne_top]
        _ ≤ hpWeight (hpArea.restrict {z | 1 < z.im}) (hpBox 0 ℓ) / ENNReal.ofReal ℓ :=
            ENNReal.div_le_div_right hmass _
        _ ≤ _ := by
            unfold hpCMNorm
            exact le_iSup_of_le (0 : ℝ) (le_iSup_of_le ℓ (le_iSup_of_le hℓ0 le_rfl))
    intro hC
    apply hC
    refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
    have hℓ : 1 < Real.exp (r + 1) := Real.one_lt_exp_iff.mpr (by positivity)
    refine le_trans ?_ (hlow _ hℓ)
    rw [Real.log_exp]
    calc (r : ℝ≥0∞) = ENNReal.ofReal r := (ENNReal.ofReal_coe_nnreal).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

/-- Lemma 11.3(d) `lem:hp-kernel`, `sec11-halfplane.tex:320`: if `λ ∈ CM(ℍ)` and `0 < r < δ`, then
`sup_{Im a ≤ r} 𝒫_m(a) ≤ 64 ε_λ(δ) + 128 ‖λ‖_CM r/δ`. -/
theorem lem_hp_kernel_d (m : Measure ℂ) (hm : IsHPCarleson (hpWeight m)) {r δ : ℝ} (hr : 0 < r)
    (hrδ : r < δ) :
    hpSupLow (hpP m) r ≤
      64 * hpEps (hpWeight m) δ + 128 * hpCMNorm (hpWeight m) * ENNReal.ofReal (r / δ) :=
  hp_kernel_d_aux m hm hr hrδ

/-! ## Transfer by bi-Lipschitz maps -/

/-- Helper for `hp_admissible_symm`: the inverse of a continuous proper bijection of the closed
upper half-plane is continuous and proper (a continuous proper map is closed). -/
theorem s11_adm_inv_cont {F : ℂ → ℂ} (hc : ContinuousOn F closedUpperHalf)
    (hb : BijOn F closedUpperHalf closedUpperHalf)
    (ht : Tendsto F (cocompact ℂ ⊓ 𝓟 closedUpperHalf) (cocompact ℂ)) :
    ContinuousOn (Function.invFunOn F closedUpperHalf) closedUpperHalf ∧
      Tendsto (Function.invFunOn F closedUpperHalf) (cocompact ℂ ⊓ 𝓟 closedUpperHalf)
        (cocompact ℂ) := by
  have hinv := hb.invOn_invFunOn
  have hGm : MapsTo (Function.invFunOn F closedUpperHalf) closedUpperHalf closedUpperHalf :=
    hb.surjOn.mapsTo_invFunOn
  have hcl : IsClosed closedUpperHalf := isClosed_le continuous_const Complex.continuous_im
  -- points of `cH` whose image lies in a compact set lie in a compact set
  have hprop : ∀ B : Set ℂ, IsCompact B → ∃ t : Set ℂ, IsCompact t ∧
      ∀ x ∈ closedUpperHalf, F x ∈ B → x ∈ t := by
    intro B hB
    have h1 := ht hB.compl_mem_cocompact
    rw [Filter.mem_map, mem_inf_principal, mem_cocompact] at h1
    obtain ⟨t, htc, hts⟩ := h1
    refine ⟨t, htc, fun x hx hFx => ?_⟩
    by_contra hxt
    exact hts hxt hx hFx
  refine ⟨fun y₀ hy₀ => ?_, ?_⟩
  · obtain ⟨t, htc, hts⟩ := hprop (closedBall y₀ 1) (isCompact_closedBall y₀ 1)
    have hKc : IsCompact (t ∩ (closedUpperHalf ∩ F ⁻¹' closedBall y₀ 1)) :=
      htc.inter_right (hc.preimage_isClosed_of_isClosed hcl isClosed_closedBall)
    have hKsub : t ∩ (closedUpperHalf ∩ F ⁻¹' closedBall y₀ 1) ⊆ closedUpperHalf :=
      fun x hx => hx.2.1
    have himg : F '' (t ∩ (closedUpperHalf ∩ F ⁻¹' closedBall y₀ 1)) =
        closedBall y₀ 1 ∩ closedUpperHalf := by
      ext y
      constructor
      · rintro ⟨x, ⟨-, hx, hxB⟩, rfl⟩
        exact ⟨hxB, hb.mapsTo hx⟩
      · rintro ⟨hyB, hy⟩
        have hFG : F (Function.invFunOn F closedUpperHalf y) = y := hinv.2 hy
        refine ⟨Function.invFunOn F closedUpperHalf y,
          ⟨hts _ (hGm hy) (show F (Function.invFunOn F closedUpperHalf y) ∈ closedBall y₀ 1 by
            rw [hFG]; exact hyB), hGm hy, ?_⟩,
          hFG⟩
        show F (Function.invFunOn F closedUpperHalf y) ∈ closedBall y₀ 1
        rw [hFG]
        exact hyB
    have hloc := continuousOn_invFunOn_image_of_isCompact hKc (hc.mono hKsub)
      (hb.injOn.mono hKsub)
    rw [himg] at hloc
    have heq : EqOn (Function.invFunOn F closedUpperHalf)
        (Function.invFunOn F (t ∩ (closedUpperHalf ∩ F ⁻¹' closedBall y₀ 1)))
        (closedBall y₀ 1 ∩ closedUpperHalf) := by
      intro y hy
      have hex : ∃ x ∈ t ∩ (closedUpperHalf ∩ F ⁻¹' closedBall y₀ 1), F x = y := by
        rw [← himg] at hy
        exact hy
      exact hb.injOn (hGm hy.2) (hKsub (Function.invFunOn_mem hex))
        ((hinv.2 hy.2).trans (Function.invFunOn_eq hex).symm)
    exact ((hloc.congr heq) y₀ ⟨mem_closedBall_self zero_le_one, hy₀⟩).mono_of_mem_nhdsWithin
      (by rw [inter_comm]; exact inter_mem_nhdsWithin _ (closedBall_mem_nhds y₀ one_pos))
  · rw [hasBasis_cocompact.tendsto_right_iff]
    intro K hK
    have hK' : IsCompact (F '' (K ∩ closedUpperHalf)) :=
      (hK.inter_right hcl).image_of_continuousOn (hc.mono inter_subset_right)
    refine mem_inf_of_inter hK'.compl_mem_cocompact (mem_principal_self closedUpperHalf) ?_
    rintro y ⟨hy1, hy2⟩ hyK
    exact hy1 ⟨_, ⟨hyK, hGm hy2⟩, hinv.2 hy2⟩

/-- Helper for `hp_admissible_symm`: on `ℍ` the inverse taken on the closed half-plane agrees with
the inverse taken on `ℍ`, and it maps `ℍ` onto `ℍ`. -/
theorem s11_adm_inv_upper {F : ℂ → ℂ} (hb : BijOn F closedUpperHalf closedUpperHalf)
    (hu : F '' upperHalf = upperHalf) :
    EqOn (Function.invFunOn F closedUpperHalf) (Function.invFunOn F upperHalf) upperHalf ∧
      Function.invFunOn F closedUpperHalf '' upperHalf = upperHalf := by
  have hinv := hb.invOn_invFunOn
  have hsub : upperHalf ⊆ closedUpperHalf := fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt hz
  have heq : EqOn (Function.invFunOn F closedUpperHalf) (Function.invFunOn F upperHalf)
      upperHalf := by
    intro y hy
    have hex : ∃ x ∈ upperHalf, F x = y := by
      rw [← hu] at hy
      exact hy
    exact hb.injOn (hb.surjOn.mapsTo_invFunOn (hsub hy)) (hsub (Function.invFunOn_mem hex))
      ((hinv.2 (hsub hy)).trans (Function.invFunOn_eq hex).symm)
  refine ⟨heq, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [heq hx]
    have hex : ∃ x' ∈ upperHalf, F x' = x := by
      rw [← hu] at hx
      exact hx
    exact Function.invFunOn_mem hex
  · intro hy
    refine ⟨F y, ?_, hinv.1 (hsub hy)⟩
    rw [← hu]
    exact mem_image_of_mem F hy

/-- `sec11-halfplane.tex:398`: the inverse of an admissible map is admissible with the same
constant (and boundary map `h⁻¹`). -/
theorem hp_admissible_symm {F : ℂ → ℂ} {h : ℝ ≃ₜ ℝ} {L : ℝ} (hF : IsHPAdmissible F h L) :
    ∃ G : ℂ → ℂ, IsHPAdmissible G h.symm L ∧ ∀ z ∈ closedUpperHalf, G (F z) = z ∧ F (G z) = z := by
  obtain ⟨hL, ⟨K, hK⟩, hu, hlip, hc, hb, ht, hbd, hs⟩ := hF
  obtain ⟨hGc, hGt⟩ := s11_adm_inv_cont hc hb ht
  obtain ⟨hGeq, hGu⟩ := s11_adm_inv_upper hb hu
  have hinv := hb.invOn_invFunOn
  have hsub : upperHalf ⊆ closedUpperHalf := fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt hz
  have hKG : IsKQC (Function.invFunOn F upperHalf) upperHalf K := by
    have h1 := thm7_2_inv hK
    rwa [hu] at h1
  refine ⟨Function.invFunOn F closedUpperHalf, ⟨hL, ⟨K, ad_isKQC_congr hKG hGeq⟩, hGu, ?_, hGc,
    hinv.symm.bijOn hb.surjOn.mapsTo_invFunOn hb.mapsTo, hGt, ?_, hp_sqs_symm hs⟩,
    fun z hz => ⟨hinv.1 hz, hinv.2 hz⟩⟩
  · intro z hz z' hz'
    have hw : Function.invFunOn F closedUpperHalf z ∈ upperHalf := hGu ▸ mem_image_of_mem _ hz
    have hw' : Function.invFunOn F closedUpperHalf z' ∈ upperHalf := hGu ▸ mem_image_of_mem _ hz'
    obtain ⟨h1, h2⟩ := hlip _ hw _ hw'
    rw [hinv.2 (hsub hz), hinv.2 (hsub hz')] at h1 h2
    exact ⟨h2, h1⟩
  · intro x
    have hx : ((h.symm x : ℝ) : ℂ) ∈ closedUpperHalf := by
      show (0 : ℝ) ≤ ((h.symm x : ℝ) : ℂ).im
      simp
    have hFx : F ((h.symm x : ℝ) : ℂ) = (x : ℂ) := by
      rw [hbd, h.apply_symm_apply]
    rw [← hFx, hinv.1 hx]

/-- Helper: `d_ρ` on `ℍ` is the distance of Mathlib's upper half-plane. -/
theorem s11_wm_hpDist_uhp {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    hpDist z w = dist (UpperHalfPlane.mk z hz) (UpperHalfPlane.mk w hw) := by
  unfold hpDist
  exact s02_arcosh_uhp hz hw

theorem s11_wm_hpDist_comm {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    hpDist z w = hpDist w z := by
  rw [s11_wm_hpDist_uhp hz hw, s11_wm_hpDist_uhp hw hz, dist_comm]

theorem s11_wm_hpDist_tri {z w v : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) (hv : 0 < v.im) :
    hpDist z v ≤ hpDist z w + hpDist w v := by
  rw [s11_wm_hpDist_uhp hz hv, s11_wm_hpDist_uhp hz hw, s11_wm_hpDist_uhp hw hv]
  exact dist_triangle _ _ _

/-- Helper: the denominator of a real Möbius map with positive determinant does not vanish on `ℍ`. -/
theorem s11_wm_mob_den {a b c d : ℝ} (hdet : 0 < a * d - b * c) {z : ℂ} (hz : 0 < z.im) :
    (c : ℂ) * z + d ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  rcases him with hc | hz0
  · subst hc
    simp at hre
    subst hre
    simp at hdet
  · linarith

/-- Helper: `Im ((a z + b)/(c z + d)) = (a d - b c) Im z / |c z + d|²`. -/
theorem s11_wm_mob_im {a b c d : ℝ} (hdet : 0 < a * d - b * c) {z : ℂ} (hz : 0 < z.im) :
    (((a : ℂ) * z + b) / ((c : ℂ) * z + d)).im =
      (a * d - b * c) * z.im / normSq ((c : ℂ) * z + d) := by
  have hN : normSq ((c : ℂ) * z + d) ≠ 0 := (normSq_pos.2 (s11_wm_mob_den hdet hz)).ne'
  rw [Complex.div_im]
  simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im]
  field_simp
  ring

theorem s11_wm_mob_mem {a b c d : ℝ} (hdet : 0 < a * d - b * c) {z : ℂ} (hz : 0 < z.im) :
    0 < (((a : ℂ) * z + b) / ((c : ℂ) * z + d)).im := by
  rw [s11_wm_mob_im hdet hz]
  exact div_pos (mul_pos hdet hz) (normSq_pos.2 (s11_wm_mob_den hdet hz))

/-- Helper: real Möbius maps with positive determinant are isometries of `(ℍ, d_ρ)`. -/
theorem s11_wm_mob_dist {a b c d : ℝ} (hdet : 0 < a * d - b * c) {z w : ℂ} (hz : 0 < z.im)
    (hw : 0 < w.im) :
    hpDist (((a : ℂ) * z + b) / ((c : ℂ) * z + d)) (((a : ℂ) * w + b) / ((c : ℂ) * w + d)) =
      hpDist z w := by
  have hdz := s11_wm_mob_den hdet hz
  have hdw := s11_wm_mob_den hdet hw
  have hNz : normSq ((c : ℂ) * z + d) ≠ 0 := (normSq_pos.2 hdz).ne'
  have hNw : normSq ((c : ℂ) * w + d) ≠ 0 := (normSq_pos.2 hdw).ne'
  have e1 : ((a : ℂ) * z + b) / ((c : ℂ) * z + d) - ((a : ℂ) * w + b) / ((c : ℂ) * w + d) =
      ((a * d - b * c : ℝ) : ℂ) * (z - w) / (((c : ℂ) * z + d) * ((c : ℂ) * w + d)) := by
    rw [div_sub_div _ _ hdz hdw]
    push_cast
    ring
  unfold hpDist
  rw [e1, s11_wm_mob_im hdet hz, s11_wm_mob_im hdet hw, Complex.sq_norm, Complex.sq_norm,
    normSq_div, normSq_mul, normSq_mul, normSq_ofReal]
  congr 2
  have hd : a * d - b * c ≠ 0 := hdet.ne'
  have hNz' : normSq (z * (c : ℂ) + d) ≠ 0 := by rwa [mul_comm]
  have hNw' : normSq (w * (c : ℂ) + d) ≠ 0 := by rwa [mul_comm]
  field_simp

/-- Helper: `|log(Im z / Im w)| ≤ d_ρ(z, w)`. -/
theorem s11_wm_log_im_le {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    |Real.log (z.im / w.im)| ≤ hpDist z w := by
  have ht : 0 < z.im / w.im := div_pos hz hw
  have hc : Real.cosh |Real.log (z.im / w.im)| = (z.im ^ 2 + w.im ^ 2) / (2 * z.im * w.im) := by
    rw [Real.cosh_abs, Real.cosh_eq, Real.exp_neg, Real.exp_log ht]
    field_simp
  unfold hpDist
  rw [← Real.arcosh_cosh (abs_nonneg _), hc]
  refine (Real.arcosh_le_arcosh (by positivity) (by positivity)).2 ?_
  have hn : (z.im - w.im) ^ 2 ≤ ‖z - w‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_im]
    nlinarith [mul_self_nonneg (z - w).re]
  rw [show (z.im ^ 2 + w.im ^ 2) / (2 * z.im * w.im) = 1 + (z.im - w.im) ^ 2 / (2 * z.im * w.im) by
    field_simp; ring]
  gcongr

/-- Helper: `arsinh (|Re w - s| / Im w) ≤ d_ρ(w, s + i q)` (distance to the vertical geodesic). -/
theorem s11_wm_vert_le {w : ℂ} (hw : 0 < w.im) (s : ℝ) {q : ℝ} (hq : 0 < q) :
    Real.arsinh (|w.re - s| / w.im) ≤ hpDist w (s + I * q) := by
  set A := |w.re - s|
  have hA : (w.re - s) ^ 2 = A ^ 2 := (sq_abs _).symm
  have h0 : 0 ≤ Real.arsinh (A / w.im) :=
    Real.arsinh_nonneg_iff.2 (div_nonneg (abs_nonneg _) hw.le)
  have hn : ‖w - (s + I * q)‖ ^ 2 = A ^ 2 + (w.im - q) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    nlinarith [hA]
  have him : (s + I * (q : ℂ)).im = q := by simp
  unfold hpDist
  rw [← Real.arcosh_cosh h0, Real.cosh_arsinh, hn, him]
  refine (Real.arcosh_le_arcosh (by positivity) (by positivity)).2 ?_
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [div_pow, show (1 : ℝ) + A ^ 2 / w.im ^ 2 = (A ^ 2 + w.im ^ 2) / w.im ^ 2 by field_simp; ring,
    show 1 + (A ^ 2 + (w.im - q) ^ 2) / (2 * w.im * q) = (A ^ 2 + w.im ^ 2 + q ^ 2) / (2 * w.im * q) by
      field_simp; ring, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (A ^ 2 + w.im ^ 2 - q ^ 2), sq_nonneg A, sq_nonneg w.im, sq_nonneg q,
    mul_pos hw hq]

/-- Helper: the foot `s + i|w - s|` of `w` on the vertical geodesic at `s` realizes
`arsinh (|Re w - s| / Im w)`. -/
theorem s11_wm_vert_foot {w : ℂ} (hw : 0 < w.im) (s : ℝ) :
    hpDist w (s + I * ‖w - s‖) = Real.arsinh (|w.re - s| / w.im) ∧ 0 < ‖w - s‖ := by
  set A := |w.re - s|
  set R := ‖w - s‖ with hRdef
  have hR2 : R ^ 2 = A ^ 2 + w.im ^ 2 := by
    rw [hRdef, Complex.sq_norm, Complex.normSq_apply, sq_abs]
    simp
    ring
  have hRpos : 0 < R := by
    have : 0 < R ^ 2 := by rw [hR2]; positivity
    exact lt_of_le_of_ne (norm_nonneg _) (fun h => by rw [← h] at this; simp at this)
  refine ⟨?_, hRpos⟩
  have h0 : 0 ≤ Real.arsinh (A / w.im) :=
    Real.arsinh_nonneg_iff.2 (div_nonneg (abs_nonneg _) hw.le)
  unfold hpDist
  rw [← Real.arcosh_cosh h0, Real.cosh_arsinh]
  congr 1
  have hn : ‖w - (s + I * (R : ℂ))‖ ^ 2 = A ^ 2 + (w.im - R) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    rw [sq_abs] at *
    ring
  have him : (s + I * (R : ℂ)).im = R := by simp
  rw [hn, him]
  have hsq : Real.sqrt (1 + (A / w.im) ^ 2) = R / w.im := by
    rw [show 1 + (A / w.im) ^ 2 = (R / w.im) ^ 2 by rw [div_pow, div_pow, hR2]; field_simp; ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsq]
  field_simp
  nlinarith [hR2]

/-- Helper (WM0): `arsinh (|Re w - s| / Im w)` is `1`-Lipschitz for `d_ρ`. -/
theorem s11_wm_vert_transfer {w w' : ℂ} (hw : 0 < w.im) (hw' : 0 < w'.im) (s : ℝ) :
    Real.arsinh (|w.re - s| / w.im) ≤ hpDist w w' + Real.arsinh (|w'.re - s| / w'.im) := by
  obtain ⟨hf, hR⟩ := s11_wm_vert_foot hw' s
  have hfi : 0 < ((s : ℂ) + I * (‖w' - s‖ : ℂ)).im := by simpa using hR
  calc _ ≤ hpDist w (s + I * ‖w' - s‖) := s11_wm_vert_le hw s hR
    _ ≤ hpDist w w' + hpDist w' (s + I * ‖w' - s‖) := s11_wm_hpDist_tri hw hw' hfi
    _ = _ := by rw [hf]

/-- Helper: `(2/(1 - |w|²)) Im w = -Re ζ / Im ζ` for `w = (ζ - i)/(ζ + i)`. -/
theorem s11_wm_B_cayley {ζ : ℂ} (hζ : 0 < ζ.im) :
    ((((2 / (1 - ‖cayley ζ‖ ^ 2) : ℝ) : ℂ) * cayley ζ) * conj I).re = -ζ.re / ζ.im := by
  have hd := cayley_den_ne_zero hζ
  have hN : normSq (ζ + I) ≠ 0 := (normSq_pos.2 hd).ne'
  have hNe : normSq (ζ + I) = ζ.re ^ 2 + (ζ.im + 1) ^ 2 := by
    rw [normSq_apply]; simp; ring
  have hw2 : ‖cayley ζ‖ ^ 2 = (ζ.re ^ 2 + (ζ.im - 1) ^ 2) / normSq (ζ + I) := by
    rw [Complex.sq_norm, cayley, normSq_div, normSq_apply (ζ - I)]
    simp
    ring
  have him : (cayley ζ).im = -2 * ζ.re / normSq (ζ + I) := by
    rw [cayley, Complex.div_im]
    simp
    field_simp
    ring
  have hre : ((((2 / (1 - ‖cayley ζ‖ ^ 2) : ℝ) : ℂ) * cayley ζ) * conj I).re =
      2 / (1 - ‖cayley ζ‖ ^ 2) * (cayley ζ).im := by
    have key : ∀ (c : ℝ) (w : ℂ), (((c : ℂ) * w) * conj I).re = c * w.im := by
      intro c w
      simp [Complex.mul_re]
    exact key _ _
  rw [hre, him, hw2, hNe]
  have hpos : 0 < ζ.re ^ 2 + (ζ.im + 1) ^ 2 := by positivity
  have h1 : 1 - (ζ.re ^ 2 + (ζ.im - 1) ^ 2) / (ζ.re ^ 2 + (ζ.im + 1) ^ 2) =
      4 * ζ.im / (ζ.re ^ 2 + (ζ.im + 1) ^ 2) := by
    field_simp
    ring
  rw [h1]
  field_simp
  ring

/-- Helper: the Cayley inverse `𝔻 → ℍ` tends to `∞` at `1`. -/
theorem s11_wm_ci_one :
    Tendsto cayleyInv (𝓝[unitDisc] 1) (cocompact ℂ ⊓ 𝓟 upperHalf) := by
  refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (eventually_nhdsWithin_of_forall fun ζ hζ =>
    cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp hζ))⟩
  refine tendsto_cocompact_of_tendsto_dist_comp_atTop 0 ?_
  have hnum : Tendsto (fun ζ : ℂ => ‖1 + ζ‖) (𝓝[unitDisc] 1) (𝓝 2) := by
    have : Tendsto (fun ζ : ℂ => ‖1 + ζ‖) (𝓝 1) (𝓝 ‖(1 : ℂ) + 1‖) :=
      ((continuous_const.add continuous_id).norm).tendsto 1
    rw [show ‖(1 : ℂ) + 1‖ = 2 by norm_num] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun ζ : ℂ => ‖1 - ζ‖) (𝓝[unitDisc] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun ζ hζ => ?_⟩
    · have : Tendsto (fun ζ : ℂ => ‖1 - ζ‖) (𝓝 1) (𝓝 ‖(1 : ℂ) - 1‖) :=
        ((continuous_const.sub continuous_id).norm).tendsto 1
      rw [sub_self, norm_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · exact norm_pos_iff.2 (cayleyInv_den_ne_zero (mem_ball_zero_iff.mp hζ))
  have h := Tendsto.pos_mul_atTop (by norm_num : (0 : ℝ) < 2) hnum (tendsto_inv_nhdsGT_zero.comp hden)
  refine h.congr' (Eventually.of_forall fun ζ => ?_)
  simp only [Function.comp, dist_zero_right, cayleyInv, norm_div, norm_mul, norm_I, one_mul]
  rw [div_eq_mul_inv]

/-- Helper: `(z - i)/(z + i) → 1` as `z → ∞`. -/
theorem s11_wm_cayley_inf : Tendsto cayley (cocompact ℂ) (𝓝 1) := by
  have hn : Tendsto (fun w : ℂ => ‖w + I‖) (cocompact ℂ) atTop := by
    refine tendsto_atTop_mono (fun w => ?_)
      (tendsto_atTop_add_const_right _ (-1) (tendsto_norm_cocompact_atTop (E := ℂ)))
    have := norm_sub_norm_le w (-I)
    simp only [norm_neg, norm_I, sub_neg_eq_add] at this
    linarith
  have h0 : Tendsto (fun w : ℂ => 2 * I / (w + I)) (cocompact ℂ) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := (tendsto_const_nhds (x := (2 : ℝ))).div_atTop hn
    refine this.congr (fun w => ?_)
    rw [norm_div, norm_mul, norm_I, mul_one]
    norm_num
  have h1 := (tendsto_const_nhds (x := (1 : ℂ))).sub h0
  rw [sub_zero] at h1
  refine h1.congr' ?_
  filter_upwards [(isCompact_singleton (x := -I)).compl_mem_cocompact] with w hw
  have hw' : w + I ≠ 0 := fun h => hw (by simp [eq_neg_of_add_eq_zero_left h])
  rw [cayley]
  field_simp
  ring

/-- Helper (WM2), Morse normal form: an `L`-bi-Lipschitz self-map `Φ` of `(ℍ, d_ρ)` with
`Φ → 0` at `0` and `Φ → ∞` at `∞` moves `i` at most `M_*(L, 0)` from the imaginary axis:
`|Re Φ(i)| ≤ sinh M_* · Im Φ(i)`.  Via the Cayley transform and `s07_mo_qi_normal_gen`. -/
theorem s11_wm_normal {L : ℝ} (hL : 1 ≤ L) {Φ : ℂ → ℂ} (hmaps : MapsTo Φ upperHalf upperHalf)
    (hlip : ∀ z ∈ upperHalf, ∀ w ∈ upperHalf,
      hpDist (Φ z) (Φ w) ≤ L * hpDist z w ∧ hpDist z w ≤ L * hpDist (Φ z) (Φ w))
    (h0 : Tendsto Φ (𝓝[upperHalf] 0) (𝓝 0))
    (hinf : Tendsto Φ (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ)) :
    |(Φ I).re| ≤ Real.sinh (morseM L 0) * (Φ I).im := by
  set B : ℝ × ℂ → ℝ × ℂ → ℝ := fun X Y => -X.1 * Y.1 + (X.2 * conj Y.2).re with hBdef
  set P : ℂ → ℝ × ℂ := fun p =>
    ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p) with hPdef
  have hB : ∀ X Y, B X Y = -X.1 * Y.1 + (X.2 * conj Y.2).re := fun _ _ => rfl
  have hP : ∀ p, P p =
      ((1 + ‖p‖ ^ 2) / (1 - ‖p‖ ^ 2), ((2 / (1 - ‖p‖ ^ 2) : ℝ) : ℂ) * p) := fun _ => rfl
  set Q : ℂ → ℂ := fun ζ => cayley (Φ (cayleyInv ζ)) with hQdef
  have hci : ∀ ζ ∈ unitDisc, cayleyInv ζ ∈ upperHalf := fun ζ hζ =>
    cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp hζ)
  have hdd : ∀ a ∈ unitDisc, ∀ b ∈ unitDisc,
      diskDist a b = hpDist (cayleyInv a) (cayleyInv b) := by
    intro a ha b hb
    unfold diskDist hpDist
    rw [s02_diskCoshDist_cayley ha hb]
    rfl
  have hQD : ∀ ζ ∈ unitDisc, Q ζ ∈ unitDisc := fun ζ hζ =>
    cayley_mem_unitDisc (hmaps (hci ζ hζ))
  have hQ : IsDiskQI Q L 0 := by
    refine ⟨fun ζ hζ => hQD ζ hζ, fun x hx y hy => ?_⟩
    have hQd : diskDist (Q x) (Q y) = hpDist (Φ (cayleyInv x)) (Φ (cayleyInv y)) := by
      rw [hdd _ (hQD x hx) _ (hQD y hy)]
      simp only [hQdef]
      rw [cayleyInv_cayley (hmaps (hci x hx)), cayleyInv_cayley (hmaps (hci y hy))]
    rw [hQd, hdd x hx y hy]
    obtain ⟨h1, h2⟩ := hlip _ (hci x hx) _ (hci y hy)
    have hL0 : 0 < L := by linarith
    refine ⟨?_, by linarith⟩
    rw [sub_zero, inv_mul_le_iff₀ hL0]
    exact h2
  -- the frame at `0`: the real diameter `C(iℝ₊)` with normal `(0, i)`
  have hP0 : P 0 = ((1 : ℝ), (0 : ℂ)) := by simp [hP]
  set e₁ : ℝ × ℂ := ((0 : ℝ), (1 : ℂ)) with he₁
  set e₂ : ℝ × ℂ := ((0 : ℝ), I) with he₂
  have hon : B (P 0) (P 0) = -1 ∧ B e₁ e₁ = 1 ∧ B e₂ e₂ = 1 ∧ B (P 0) e₁ = 0 ∧ B (P 0) e₂ = 0 ∧
      B e₁ e₂ = 0 := by
    rw [hP0]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hB, he₁, he₂]
  have he₀ : 0 < (P 0).1 := by rw [hP0]; norm_num
  obtain ⟨-, -, -, -, γ, hγD, hγ0, -, hγd, hγtop, hγbot⟩ := s07_mo_line B hB P hP hon he₀
  have hωp : ((P 0).2 + e₁.2) / (((P 0).1 + e₁.1 : ℝ) : ℂ) = 1 := by rw [hP0]; simp [he₁]
  have hωm : ((P 0).2 - e₁.2) / (((P 0).1 - e₁.1 : ℝ) : ℂ) = -1 := by rw [hP0]; simp [he₁]
  rw [hωp] at hγtop
  rw [hωm] at hγbot
  have hγ00 : γ 0 = 0 := s07_mo_P_inj P hP (hγD 0) (mem_ball_self one_pos) hγ0
  -- the two end limits of `Q`
  have hQ1 : Tendsto Q (𝓝[unitDisc] 1) (𝓝 1) :=
    s11_wm_cayley_inf.comp (hinf.comp s11_wm_ci_one)
  have hQm1 : Tendsto Q (𝓝[unitDisc] (-1)) (𝓝 (-1)) := by
    have hc1 : ContinuousAt (fun w : ℂ => I * (1 + w) / (1 - w)) (-1) :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
    have hci0 : Tendsto cayleyInv (𝓝[unitDisc] (-1)) (𝓝[upperHalf] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall hci⟩
      have := hc1.tendsto
      rw [show I * (1 + -1) / (1 - -1) = (0 : ℂ) by norm_num] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hc2 : ContinuousAt (fun w : ℂ => (w - I) / (w + I)) 0 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)
    have h2 := hc2.tendsto
    rw [show ((0 : ℂ) - I) / (0 + I) = -1 by
      rw [zero_sub, zero_add, neg_div, div_self I_ne_zero]] at h2
    exact h2.comp (h0.comp hci0)
  have htop : Tendsto (fun τ => Q (γ τ)) atTop
      (𝓝 (((P 0).2 + e₁.2) / (((P 0).1 + e₁.1 : ℝ) : ℂ))) := by
    rw [hωp]
    exact hQ1.comp (tendsto_nhdsWithin_iff.2 ⟨hγtop, Eventually.of_forall hγD⟩)
  have hbot : Tendsto (fun τ => Q (γ τ)) atBot
      (𝓝 (((P 0).2 - e₁.2) / (((P 0).1 - e₁.1 : ℝ) : ℂ))) := by
    rw [hωm]
    exact hQm1.comp (tendsto_nhdsWithin_iff.2 ⟨hγbot, Eventually.of_forall hγD⟩)
  have hmain := s07_mo_qi_normal_gen L 0 hL le_rfl Q hQ B hB P hP γ hγD hγd hon he₀ htop hbot 0
  have hQ0 : Q (γ 0) = cayley (Φ I) := by
    rw [hγ00]
    simp [hQdef, cayleyInv]
  rw [hQ0] at hmain
  have hζ : 0 < (Φ I).im := hmaps (show (0 : ℝ) < I.im by simp)
  have hval : B (P (cayley (Φ I))) e₂ = -(Φ I).re / (Φ I).im := by
    rw [hB, hP, he₂]
    simp only [mul_zero, neg_zero, zero_add]
    exact s11_wm_B_cayley hζ
  rw [hval, abs_div, abs_neg, abs_of_pos hζ, div_le_iff₀ hζ] at hmain
  exact hmain

/-- Helper: a nonconstant complex affine map is proper. -/
theorem s11_wm_cocompact_affine {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    Tendsto (fun z => a * z + b) (cocompact ℂ) (cocompact ℂ) := by
  refine tendsto_cocompact_of_tendsto_dist_comp_atTop 0 ?_
  have h := (tendsto_norm_cocompact_atTop (E := ℂ)).const_mul_atTop (norm_pos_iff.2 ha)
  refine tendsto_atTop_mono (fun z => ?_) (tendsto_atTop_add_const_right _ (-‖b‖) h)
  rw [dist_zero_right]
  have := norm_sub_norm_le (a * z) (-b)
  rw [norm_mul, norm_neg, sub_neg_eq_add] at this
  linarith

/-- Helper: boundary behaviour of an admissible map: `F → h x` at the real point `x`, `F` maps `ℍ`
to `ℍ`, and `F → ∞` at `∞`. -/
theorem s11_wm_adm_basic {F : ℂ → ℂ} {h : ℝ ≃ₜ ℝ} {L : ℝ} (hF : IsHPAdmissible F h L) :
    MapsTo F upperHalf upperHalf ∧
      (∀ x : ℝ, Tendsto F (𝓝[upperHalf] (x : ℂ)) (𝓝[upperHalf] ((h x : ℝ) : ℂ))) ∧
      Tendsto F (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ) := by
  obtain ⟨-, -, hu, -, hc, -, ht, hbd, -⟩ := hF
  have hmaps : MapsTo F upperHalf upperHalf := fun z hz => hu ▸ mem_image_of_mem F hz
  have hsub : upperHalf ⊆ closedUpperHalf := fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt hz
  refine ⟨hmaps, fun x => ?_, ?_⟩
  · have hx : (x : ℂ) ∈ closedUpperHalf := show (0 : ℝ) ≤ (x : ℂ).im by simp
    have h1 := (hc _ hx).tendsto
    rw [hbd x] at h1
    exact tendsto_nhdsWithin_iff.2 ⟨h1.mono_left (nhdsWithin_mono _ hsub),
      eventually_nhdsWithin_of_forall fun z hz => hmaps hz⟩
  · exact ht.mono_left (inf_le_inf_left _ (principal_mono.2 hsub))

/-- Helper: `d_ρ(s + q z, s + q w) = d_ρ(z, w)` for `q > 0`. -/
theorem s11_wm_affine_dist (s : ℝ) {q : ℝ} (hq : 0 < q) {z w : ℂ} (hz : 0 < z.im)
    (hw : 0 < w.im) : hpDist (s + q * z) (s + q * w) = hpDist z w := by
  have h := s11_wm_mob_dist (a := q) (b := s) (c := 0) (d := 1) (by simp; linarith) hz hw
  simp only [ofReal_zero, zero_mul, zero_add, ofReal_one, div_one] at h
  rw [add_comm (s : ℂ), add_comm (s : ℂ)]
  exact h

/-- Helper (WM3), vertical case: an admissible `F` keeps the vertical geodesic at `s` within
`M_*(L, 0)` of the vertical geodesic at `h s`. -/
theorem s11_wm_morse_vert {F : ℂ → ℂ} {h : ℝ ≃ₜ ℝ} {L : ℝ} (hF : IsHPAdmissible F h L) (s : ℝ)
    {q : ℝ} (hq : 0 < q) :
    |(F (s + I * q)).re - h s| ≤ Real.sinh (morseM L 0) * (F (s + I * q)).im := by
  obtain ⟨hmaps, hbdl, hinfF⟩ := s11_wm_adm_basic hF
  have hlipF := hF.2.2.2.1
  set Φ : ℂ → ℂ := fun ζ => F (s + q * ζ) + (-(h s : ℂ)) with hΦ
  have hM₁ : ∀ ζ ∈ upperHalf, (s : ℂ) + q * ζ ∈ upperHalf := fun ζ hζ => by
    show 0 < ((s : ℂ) + q * ζ).im
    simpa using mul_pos hq hζ
  have hmapsΦ : MapsTo Φ upperHalf upperHalf := fun ζ hζ => by
    have := hmaps (hM₁ ζ hζ)
    show 0 < (F (s + q * ζ) + (-(h s : ℂ))).im
    simp only [add_im, neg_im, ofReal_im, neg_zero, add_zero]
    exact this
  have htr : ∀ z ∈ upperHalf, ∀ w ∈ upperHalf,
      hpDist (z + (-(h s : ℂ))) (w + (-(h s : ℂ))) = hpDist z w := by
    intro z hz w hw
    have := s11_wm_affine_dist (-(h s)) one_pos hz hw
    simp only [ofReal_neg, ofReal_one, one_mul] at this
    rw [add_comm z, add_comm w]
    exact this
  have hlip : ∀ z ∈ upperHalf, ∀ w ∈ upperHalf,
      hpDist (Φ z) (Φ w) ≤ L * hpDist z w ∧ hpDist z w ≤ L * hpDist (Φ z) (Φ w) := by
    intro z hz w hw
    simp only [hΦ]
    rw [htr _ (hmaps (hM₁ z hz)) _ (hmaps (hM₁ w hw)), ← s11_wm_affine_dist s hq hz hw]
    exact hlipF _ (hM₁ z hz) _ (hM₁ w hw)
  have h0 : Tendsto Φ (𝓝[upperHalf] 0) (𝓝 0) := by
    have hm : Tendsto (fun ζ : ℂ => (s : ℂ) + q * ζ) (𝓝[upperHalf] 0) (𝓝[upperHalf] (s : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall hM₁⟩
      have : Tendsto (fun ζ : ℂ => (s : ℂ) + q * ζ) (𝓝 0) (𝓝 ((s : ℂ) + q * 0)) :=
        (continuous_const.add (continuous_const.mul continuous_id)).tendsto 0
      rw [mul_zero, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have := ((hbdl s).mono_right nhdsWithin_le_nhds).comp hm
    have h2 := this.add_const (-(h s : ℂ))
    rw [add_neg_cancel] at h2
    exact h2
  have hinf : Tendsto Φ (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ) := by
    have hm : Tendsto (fun ζ : ℂ => (s : ℂ) + q * ζ) (cocompact ℂ ⊓ 𝓟 upperHalf)
        (cocompact ℂ ⊓ 𝓟 upperHalf) := by
      refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (mem_inf_of_right (mem_principal.2 hM₁))⟩
      have := s11_wm_cocompact_affine (a := (q : ℂ)) (by exact_mod_cast hq.ne') (s : ℂ)
      refine (this.congr fun z => add_comm _ _).mono_left inf_le_left
    have := (s11_wm_cocompact_affine one_ne_zero (-(h s : ℂ))).comp (hinfF.comp hm)
    refine this.congr fun z => ?_
    simp [hΦ]
  have hN := s11_wm_normal hF.1 hmapsΦ hlip h0 hinf
  have hI : (s : ℂ) + q * I = s + I * q := by ring
  simp only [hΦ, hI, add_re, add_im, neg_re, neg_im, ofReal_re, ofReal_im, neg_zero,
    add_zero] at hN
  rwa [← sub_eq_add_neg] at hN

/-- Helper: `c / w → 0` as `w → ∞`. -/
theorem s11_wm_div_inf (c : ℂ) : Tendsto (fun w : ℂ => c / w) (cocompact ℂ) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have := (tendsto_const_nhds (x := ‖c‖)).div_atTop (tendsto_norm_cocompact_atTop (E := ℂ))
  exact this.congr fun w => (norm_div _ _).symm

/-- Helper: `c / x → ∞` as `x → 0`, `x ≠ 0`, for `c ≠ 0`. -/
theorem s11_wm_div_zero {c : ℂ} (hc : c ≠ 0) :
    Tendsto (fun x : ℂ => c / x) (𝓝[≠] 0) (cocompact ℂ) := by
  refine tendsto_cocompact_of_tendsto_dist_comp_atTop 0 ?_
  have h := (tendsto_inv_nhdsGT_zero.comp (tendsto_norm_nhdsNE_zero (E := ℂ))).const_mul_atTop
    (norm_pos_iff.2 hc)
  refine h.congr fun x => ?_
  simp [norm_div, div_eq_mul_inv]

/-- Helper (WM3), semicircle case: an admissible `F` keeps the geodesic `γ_{s,t}` within
`M_*(L, 0)` of `γ_{h s, h t}`; with `u + i v = F p`, `|(u - h s)(h t - u) - v²| ≤ sinh M_* v (h t - h s)`. -/
theorem s11_wm_morse_arc {F : ℂ → ℂ} {h : ℝ ≃ₜ ℝ} {L : ℝ} (hF : IsHPAdmissible F h L) {s t : ℝ}
    (hst : s < t) {p : ℂ} (hp : 0 < p.im) (hpc : ‖p - ((s + t) / 2 : ℝ)‖ = (t - s) / 2) :
    |((F p).re - h s) * (h t - (F p).re) - (F p).im ^ 2| ≤
      Real.sinh (morseM L 0) * (F p).im * (h t - h s) := by
  obtain ⟨hmaps, hbdl, -⟩ := s11_wm_adm_basic hF
  have hlipF := hF.2.2.2.1
  obtain ⟨ω, hω⟩ := hF.2.2.2.2.2.2.2.2
  have hht : h s < h t := hω.1 hst
  -- `p` on the semicircle: `(Re p - s)(t - Re p) = (Im p)²`
  have hsemi : (p.re - s) * (t - p.re) = p.im ^ 2 := by
    have h2 := congrArg (· ^ 2) hpc
    simp only [Complex.sq_norm, normSq_apply, sub_re, sub_im, ofReal_re, ofReal_im, sub_zero] at h2
    nlinarith [h2]
  have htp : (t : ℂ) - p ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hNtp : normSq ((t : ℂ) - p) ≠ 0 := (normSq_pos.2 htp).ne'
  set lam := (((p : ℂ) - s) / ((t : ℂ) - p)).im with hlamdef
  have hNre : (((p : ℂ) - s) / ((t : ℂ) - p)).re = 0 := by
    rw [Complex.div_re]
    simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero, zero_sub]
    rw [← add_div]
    have : (p.re - s) * (t - p.re) + p.im * -p.im = 0 := by nlinarith [hsemi]
    rw [this, zero_div]
  have hlam : 0 < lam := by
    rw [hlamdef, Complex.div_im]
    simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero, zero_sub]
    rw [← sub_div]
    refine div_pos ?_ (normSq_pos.2 htp)
    nlinarith [mul_pos hp (sub_pos.2 hst)]
  have hNp : ((p : ℂ) - s) / ((t : ℂ) - p) = I * lam := by
    refine Complex.ext ?_ ?_
    · simp [hNre]
    · simp [hlamdef]
  -- the Möbius maps `M₁ : 0, i, ∞ ↦ s, p, t` and `M₂ : h s, h t ↦ 0, ∞`
  have hdet₁ : 0 < t * lam * 1 - s * lam := by nlinarith [mul_pos hlam (sub_pos.2 hst)]
  have hdet₂ : 0 < 1 * h t - (-h s) * (-1) := by linarith
  set M₁ : ℂ → ℂ := fun ζ => (((t * lam : ℝ) : ℂ) * ζ + (s : ℂ)) / (((lam : ℝ) : ℂ) * ζ + ((1 : ℝ) : ℂ))
    with hM₁
  set M₂ : ℂ → ℂ := fun w => (((1 : ℝ) : ℂ) * w + ((-h s : ℝ) : ℂ)) /
    (((-1 : ℝ) : ℂ) * w + ((h t : ℝ) : ℂ)) with hM₂
  have hM₁u : ∀ ζ ∈ upperHalf, M₁ ζ ∈ upperHalf := fun ζ hζ => s11_wm_mob_mem hdet₁ hζ
  have hM₂u : ∀ w ∈ upperHalf, M₂ w ∈ upperHalf := fun w hw => s11_wm_mob_mem hdet₂ hw
  have hM₁I : M₁ I = p := by
    have hden : ((lam : ℝ) : ℂ) * I + ((1 : ℝ) : ℂ) ≠ 0 := s11_wm_mob_den hdet₁ (by simp)
    simp only [hM₁]
    rw [div_eq_iff hden]
    have h1 : (p : ℂ) - s = I * lam * ((t : ℂ) - p) := by
      rw [← hNp, div_mul_cancel₀ _ htp]
    push_cast
    linear_combination -h1
  set Φ : ℂ → ℂ := fun ζ => M₂ (F (M₁ ζ)) with hΦ
  have hmapsΦ : MapsTo Φ upperHalf upperHalf := fun ζ hζ => hM₂u _ (hmaps (hM₁u ζ hζ))
  have hlip : ∀ z ∈ upperHalf, ∀ w ∈ upperHalf,
      hpDist (Φ z) (Φ w) ≤ L * hpDist z w ∧ hpDist z w ≤ L * hpDist (Φ z) (Φ w) := by
    intro z hz w hw
    simp only [hΦ, hM₂]
    rw [s11_wm_mob_dist hdet₂ (hmaps (hM₁u z hz)) (hmaps (hM₁u w hw)),
      ← s11_wm_mob_dist hdet₁ hz hw]
    exact hlipF _ (hM₁u z hz) _ (hM₁u w hw)
  -- end limits
  have hM₂c : ContinuousAt M₂ ((h s : ℝ) : ℂ) := by
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    push_cast
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  have h0 : Tendsto Φ (𝓝[upperHalf] 0) (𝓝 0) := by
    have hc : ContinuousAt M₁ 0 := ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)
    have hm : Tendsto M₁ (𝓝[upperHalf] 0) (𝓝[upperHalf] (s : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall hM₁u⟩
      have := hc.tendsto
      rw [show M₁ 0 = (s : ℂ) by simp [hM₁]] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 := hM₂c.tendsto
    rw [show M₂ ((h s : ℝ) : ℂ) = 0 by simp [hM₂]] at h2
    exact h2.comp (((hbdl s).mono_right nhdsWithin_le_nhds).comp hm)
  have hinf : Tendsto Φ (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ) := by
    have hm : Tendsto M₁ (cocompact ℂ ⊓ 𝓟 upperHalf) (𝓝[upperHalf] (t : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, mem_inf_of_right (mem_principal.2 hM₁u)⟩
      have hl := (s11_wm_div_inf ((t : ℂ) - s)).comp
        (s11_wm_cocompact_affine (a := ((lam : ℝ) : ℂ)) (by exact_mod_cast hlam.ne') ((1 : ℝ) : ℂ))
      have h2 := (tendsto_const_nhds (x := (t : ℂ))).sub hl
      rw [sub_zero] at h2
      refine (h2.mono_left inf_le_left).congr' (mem_inf_of_right (mem_principal.2 fun ζ hζ => ?_))
      have hden : ((lam : ℝ) : ℂ) * ζ + ((1 : ℝ) : ℂ) ≠ 0 := s11_wm_mob_den hdet₁ hζ
      show (t : ℂ) - ((t : ℂ) - s) / (((lam : ℝ) : ℂ) * ζ + ((1 : ℝ) : ℂ)) = M₁ ζ
      simp only [hM₁]
      rw [eq_div_iff hden]
      field_simp
      push_cast
      ring
    have hw : Tendsto M₂ (𝓝[upperHalf] ((h t : ℝ) : ℂ)) (cocompact ℂ) := by
      have hd : Tendsto (fun w : ℂ => ((h t : ℝ) : ℂ) - w) (𝓝[upperHalf] ((h t : ℝ) : ℂ))
          (𝓝[≠] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun w hw => ?_⟩
        · have : Tendsto (fun w : ℂ => ((h t : ℝ) : ℂ) - w) (𝓝 ((h t : ℝ) : ℂ))
              (𝓝 (((h t : ℝ) : ℂ) - ((h t : ℝ) : ℂ))) :=
            (continuous_const.sub continuous_id).tendsto _
          rw [sub_self] at this
          exact this.mono_left nhdsWithin_le_nhds
        · intro h0
          have := congrArg Complex.im h0
          have hw' : 0 < w.im := hw
          simp at this
          linarith
      have hne : ((h t : ℝ) : ℂ) - ((h s : ℝ) : ℂ) ≠ 0 := by
        rw [← ofReal_sub]
        exact_mod_cast (sub_pos.2 hht).ne'
      have h2 := (s11_wm_cocompact_affine one_ne_zero (-1)).comp ((s11_wm_div_zero hne).comp hd)
      refine h2.congr' (eventually_nhdsWithin_of_forall fun w hw => ?_)
      have hw' : 0 < w.im := hw
      have hden : ((h t : ℝ) : ℂ) - w ≠ 0 := by
        intro h0
        have := congrArg Complex.im h0
        simp at this
        linarith
      simp only [Function.comp, hM₂]
      push_cast
      rw [show -(1 : ℂ) * w + ((h t : ℝ) : ℂ) = ((h t : ℝ) : ℂ) - w by ring]
      field_simp
      ring
    exact hw.comp ((hbdl t).comp hm)
  -- conclusion
  have hN := s11_wm_normal hF.1 hmapsΦ hlip h0 hinf
  have hFp : 0 < (F p).im := hmaps hp
  have hΦI : Φ I = M₂ (F p) := by simp only [hΦ, hM₁I]
  rw [hΦI] at hN
  have him := s11_wm_mob_im hdet₂ hFp
  have hden : normSq (((-1 : ℝ) : ℂ) * F p + ((h t : ℝ) : ℂ)) ≠ 0 :=
    (normSq_pos.2 (s11_wm_mob_den hdet₂ hFp)).ne'
  have hNe : normSq (((-1 : ℝ) : ℂ) * F p + ((h t : ℝ) : ℂ)) = (h t - (F p).re) ^ 2 + (F p).im ^ 2 := by
    rw [normSq_apply]; simp; ring
  have hre : (M₂ (F p)).re = (((F p).re - h s) * (h t - (F p).re) - (F p).im ^ 2) /
      normSq (((-1 : ℝ) : ℂ) * F p + ((h t : ℝ) : ℂ)) := by
    simp only [hM₂]
    rw [Complex.div_re]
    simp
    ring
  rw [show M₂ (F p) = (((1 : ℝ) : ℂ) * F p + ((-h s : ℝ) : ℂ)) /
    (((-1 : ℝ) : ℂ) * F p + ((h t : ℝ) : ℂ)) from rfl, him] at hN
  rw [hre, abs_div, abs_of_pos (normSq_pos.2 (s11_wm_mob_den hdet₂ hFp))] at hN
  have hNp' := normSq_pos.2 (s11_wm_mob_den hdet₂ hFp)
  rw [div_le_iff₀ hNp'] at hN
  have : Real.sinh (morseM L 0) * ((1 * h t - -h s * -1) * (F p).im /
      normSq (((-1 : ℝ) : ℂ) * F p + ((h t : ℝ) : ℂ))) *
      normSq (((-1 : ℝ) : ℂ) * F p + ((h t : ℝ) : ℂ)) =
      Real.sinh (morseM L 0) * (F p).im * (h t - h s) := by
    field_simp
  linarith

/-- The constant `C₁(L) = 2 (sinh E + 1)`, `E = L arsinh 1 + M_*(L, 0)`, of `lem_hp_wm`. -/
def s11_wm_C₁ (L : ℝ) : ℝ := 2 * (Real.sinh (L * Real.arsinh 1 + morseM L 0) + 1)

/-- The constant `α(L) = 1 + C₁³ 3^L (sinh M_*(L, 0) + 1)` of `lem_hp_wm`. -/
def s11_wm_α (L : ℝ) : ℝ := 1 + s11_wm_C₁ L ^ 3 * (3 : ℝ) ^ L * (Real.sinh (morseM L 0) + 1)

theorem s11_wm_morseM_nonneg {L : ℝ} (hL : 1 ≤ L) : 0 ≤ morseM L 0 := by
  have hS1 : 1 ≤ morseS L 0 := by unfold morseS; linarith
  have ha1 : 1 ≤ morseA1 L 0 := by unfold morseA1; nlinarith [hS1]
  have hb0 : 0 ≤ morseB1 L 0 := by
    unfold morseB1
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hr0 : 0 ≤ morseR L 0 := Real.arcosh_nonneg (by linarith)
  show 0 ≤ (2 * morseA1 L 0 + 1) * morseR L 0 + morseB1 L 0
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * morseA1 L 0 + 1) hr0]

theorem s11_wm_C₁_ge {L : ℝ} (hL : 1 ≤ L) : 1 ≤ s11_wm_C₁ L := by
  have ha0 : 0 ≤ Real.arsinh 1 := Real.arsinh_nonneg_iff.2 zero_le_one
  have hE : 0 ≤ L * Real.arsinh 1 + morseM L 0 :=
    add_nonneg (mul_nonneg (by linarith) ha0) (s11_wm_morseM_nonneg hL)
  have := Real.sinh_nonneg_iff.2 hE
  unfold s11_wm_C₁
  linarith

theorem s11_wm_α_ge {L : ℝ} (hL : 1 ≤ L) : 1 ≤ s11_wm_α L := by
  have hC := s11_wm_C₁_ge hL
  have hσ := Real.sinh_nonneg_iff.2 (s11_wm_morseM_nonneg hL)
  have : 0 ≤ s11_wm_C₁ L ^ 3 * (3 : ℝ) ^ L * (Real.sinh (morseM L 0) + 1) :=
    mul_nonneg (mul_nonneg (pow_nonneg (by linarith) 3) (by positivity)) (by linarith)
  unfold s11_wm_α
  linarith

/-- Helper (WM4): `|Re F z - h s| ≤ sinh (L arsinh r + M_*(L, 0)) Im F z`, `r = |Re z - s| / Im z`
(WM3 at the foot of `z` on the vertical geodesic at `s`, then WM0 transfer). -/
theorem s11_wm_vert_far {F : ℂ → ℂ} {h : ℝ ≃ₜ ℝ} {L : ℝ} (hF : IsHPAdmissible F h L) {z : ℂ}
    (hz : 0 < z.im) (s : ℝ) :
    |(F z).re - h s| ≤
      Real.sinh (L * Real.arsinh (|z.re - s| / z.im) + morseM L 0) * (F z).im := by
  obtain ⟨hmaps, -, -⟩ := s11_wm_adm_basic hF
  obtain ⟨hf, hR⟩ := s11_wm_vert_foot hz s
  have hw'i : 0 < ((s : ℂ) + I * (‖z - s‖ : ℂ)).im := by simpa using hR
  have hFz : 0 < (F z).im := hmaps hz
  have hFw : 0 < (F ((s : ℂ) + I * (‖z - s‖ : ℂ))).im := hmaps hw'i
  have hd : hpDist (F z) (F ((s : ℂ) + I * (‖z - s‖ : ℂ))) ≤
      L * Real.arsinh (|z.re - s| / z.im) := by
    rw [← hf]
    exact (hF.2.2.2.1 z hz _ hw'i).1
  have hv := s11_wm_morse_vert hF s hR
  have h2 : Real.arsinh (|(F ((s : ℂ) + I * (‖z - s‖ : ℂ))).re - h s| /
      (F ((s : ℂ) + I * (‖z - s‖ : ℂ))).im) ≤ morseM L 0 := by
    rw [← Real.arsinh_sinh (morseM L 0)]
    exact Real.arsinh_le_arsinh.2 ((div_le_iff₀ hFw).2 hv)
  have h3 := s11_wm_vert_transfer hFz hFw (h s)
  have h5 := Real.sinh_le_sinh.2 (show Real.arsinh (|(F z).re - h s| / (F z).im) ≤
    L * Real.arsinh (|z.re - s| / z.im) + morseM L 0 by linarith)
  rw [Real.sinh_arsinh] at h5
  exact (div_le_iff₀ hFz).1 h5

/-- Helper (WM4), [WMUC, Lemma 13]: for admissible `F` and `z ∈ ℍ`,
`Im F z / Im z ≍ |h(I_z)| / |I_z|` with `I_z = [Re z - Im z, Re z + Im z]`, constant `C₁(L)`.
Upper bound: `z ∈ γ_{a,b}` and WM3 (arc); lower bound: WM3 (vertical) at `a` and at `b`. -/
theorem s11_wm_height {F : ℂ → ℂ} {h : ℝ ≃ₜ ℝ} {L : ℝ} (hF : IsHPAdmissible F h L) {z : ℂ}
    (hz : z ∈ upperHalf) :
    (s11_wm_C₁ L)⁻¹ * (imgLength h z.re (2 * z.im) / (2 * z.im)) ≤ (F z).im / z.im ∧
      (F z).im / z.im ≤ s11_wm_C₁ L * (imgLength h z.re (2 * z.im) / (2 * z.im)) := by
  have hy : 0 < z.im := hz
  obtain ⟨hmaps, -, -⟩ := s11_wm_adm_basic hF
  obtain ⟨ω, hω⟩ := hF.2.2.2.2.2.2.2.2
  have hv : 0 < (F z).im := hmaps hz
  have ha0 : 0 ≤ Real.arsinh 1 := Real.arsinh_nonneg_iff.2 zero_le_one
  have hσ : 0 ≤ Real.sinh (morseM L 0) := Real.sinh_nonneg_iff.2 (s11_wm_morseM_nonneg hF.1)
  have hσE : Real.sinh (morseM L 0) ≤ Real.sinh (L * Real.arsinh 1 + morseM L 0) :=
    Real.sinh_le_sinh.2 (by nlinarith [hF.1])
  have hlen : imgLength h z.re (2 * z.im) = h (z.re + z.im) - h (z.re - z.im) := by
    simp only [imgLength]
    rw [show 2 * z.im / 2 = z.im by ring]
  have hDp : 0 < h (z.re + z.im) - h (z.re - z.im) := sub_pos.2 (hω.1 (by linarith))
  -- upper bound
  have hpc : ‖z - (((z.re - z.im) + (z.re + z.im)) / 2 : ℝ)‖ =
      ((z.re + z.im) - (z.re - z.im)) / 2 := by
    have e : z - ((((z.re - z.im) + (z.re + z.im)) / 2 : ℝ) : ℂ) = I * z.im :=
      Complex.ext (by simp <;> ring) (by simp)
    rw [e, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
    ring
  have harc := s11_wm_morse_arc hF (by linarith : z.re - z.im < z.re + z.im) hy hpc
  -- lower bound
  have hfa := s11_wm_vert_far hF hy (z.re - z.im)
  have hfb := s11_wm_vert_far hF hy (z.re + z.im)
  rw [show |z.re - (z.re - z.im)| / z.im = 1 by
    rw [show z.re - (z.re - z.im) = z.im by ring, abs_of_pos hy, div_self hy.ne']] at hfa
  rw [show |z.re - (z.re + z.im)| / z.im = 1 by
    rw [show z.re - (z.re + z.im) = -z.im by ring, abs_neg, abs_of_pos hy, div_self hy.ne']] at hfb
  rw [hlen, show s11_wm_C₁ L = 2 * (Real.sinh (L * Real.arsinh 1 + morseM L 0) + 1) from rfl]
  generalize Real.sinh (L * Real.arsinh 1 + morseM L 0) = sE at hfa hfb hσE ⊢
  generalize Real.sinh (morseM L 0) = σ at harc hσ hσE
  generalize h (z.re + z.im) = hb at harc hfb hDp ⊢
  generalize h (z.re - z.im) = ha at harc hfa hDp ⊢
  generalize (F z).re = u at harc hfa hfb
  generalize (F z).im = v at harc hfa hfb hv ⊢
  have hsE : 0 ≤ sE := hσ.trans hσE
  constructor
  · rw [inv_mul_le_iff₀ (by linarith), div_le_iff₀ (by positivity)]
    have e : 2 * (sE + 1) * (v / z.im) * (2 * z.im) = 4 * (sE + 1) * v := by
      field_simp
      ring
    rw [e]
    nlinarith [abs_le.1 hfa, abs_le.1 hfb]
  · have hprod : (u - ha) * (hb - u) ≤ (hb - ha) ^ 2 / 4 := by
      nlinarith [sq_nonneg ((u - ha) - (hb - u))]
    have hup : v ≤ (σ + 1) * (hb - ha) := by
      by_contra hc
      push_neg at hc
      have h1 := (abs_le.1 harc).1
      nlinarith [mul_lt_mul_of_pos_left hc hv, mul_lt_mul_of_pos_left hc hDp,
        mul_nonneg hσ (sq_nonneg (hb - ha))]
    rw [div_le_iff₀ hy]
    have e : 2 * (sE + 1) * ((hb - ha) / (2 * z.im)) * z.im = (sE + 1) * (hb - ha) := by
      field_simp
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right hσE hDp.le]

/-- Helper (WM5): the doubling `|h(3I)| ≤ C₁² 3^L |h(I)|` for the boundary map of an admissible
`F`. This step fills a gap in the source: [WMUC] uses a quasisymmetry constant `M(L)` of `h` that it
does not prove; here doubling is derived from Lemma 13 (`s11_wm_height`) at `c + iℓ/2` and
`c + 3iℓ/2`, two points at distance `log 3` on one vertical geodesic. -/
theorem s11_wm_double {F : ℂ → ℂ} {h : ℝ ≃ₜ ℝ} {L : ℝ} (hF : IsHPAdmissible F h L) (c : ℝ)
    {ℓ : ℝ} (hℓ : 0 < ℓ) :
    imgLength h c (3 * ℓ) ≤ (s11_wm_C₁ L) ^ 2 * (3 : ℝ) ^ L * imgLength h c ℓ := by
  obtain ⟨hmaps, -, -⟩ := s11_wm_adm_basic hF
  have hC := s11_wm_C₁_ge hF.1
  have h1i : ((c : ℂ) + I * ((ℓ / 2 : ℝ) : ℂ)).im = ℓ / 2 := by simp
  have h2i : ((c : ℂ) + I * ((3 * ℓ / 2 : ℝ) : ℂ)).im = 3 * ℓ / 2 := by simp
  have h1r : ((c : ℂ) + I * ((ℓ / 2 : ℝ) : ℂ)).re = c := by simp
  have h2r : ((c : ℂ) + I * ((3 * ℓ / 2 : ℝ) : ℂ)).re = c := by simp
  have hz₁ : 0 < ((c : ℂ) + I * ((ℓ / 2 : ℝ) : ℂ)).im := by rw [h1i]; positivity
  have hz₂ : 0 < ((c : ℂ) + I * ((3 * ℓ / 2 : ℝ) : ℂ)).im := by rw [h2i]; positivity
  have hv₁ : 0 < (F ((c : ℂ) + I * ((ℓ / 2 : ℝ) : ℂ))).im := hmaps hz₁
  have hv₂ : 0 < (F ((c : ℂ) + I * ((3 * ℓ / 2 : ℝ) : ℂ))).im := hmaps hz₂
  have H₁ := (s11_wm_height hF hz₁).2
  have H₂ := (s11_wm_height hF hz₂).1
  rw [h1i, h1r, show 2 * (ℓ / 2) = ℓ by ring] at H₁
  rw [h2i, h2r, show 2 * (3 * ℓ / 2) = 3 * ℓ by ring] at H₂
  have hd : hpDist ((c : ℂ) + I * ((3 * ℓ / 2 : ℝ) : ℂ)) ((c : ℂ) + I * ((ℓ / 2 : ℝ) : ℂ)) =
      Real.log 3 := by
    unfold hpDist
    have hn : ‖((c : ℂ) + I * ((3 * ℓ / 2 : ℝ) : ℂ)) - ((c : ℂ) + I * ((ℓ / 2 : ℝ) : ℂ))‖ ^ 2 =
        ℓ ^ 2 := by
      rw [Complex.sq_norm, normSq_apply]
      simp
      ring
    rw [hn, h1i, h2i, show 1 + ℓ ^ 2 / (2 * (3 * ℓ / 2) * (ℓ / 2)) = Real.cosh (Real.log 3) by
      rw [Real.cosh_eq, Real.exp_neg, Real.exp_log (by norm_num)]
      field_simp
      ring]
    exact Real.arcosh_cosh (Real.log_nonneg (by norm_num))
  have hlog := s11_wm_log_im_le hv₂ hv₁
  have hlipd := (hF.2.2.2.1 _ hz₂ _ hz₁).1
  rw [hd] at hlipd
  have hr : (F ((c : ℂ) + I * ((3 * ℓ / 2 : ℝ) : ℂ))).im /
      (F ((c : ℂ) + I * ((ℓ / 2 : ℝ) : ℂ))).im ≤ (3 : ℝ) ^ L := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← Real.log_le_iff_le_exp (div_pos hv₂ hv₁)]
    have := (abs_le.1 (hlog.trans hlipd)).2
    linarith [mul_comm (Real.log 3) L]
  have h3 : 0 < (3 : ℝ) ^ L := by positivity
  generalize (F ((c : ℂ) + I * ((3 * ℓ / 2 : ℝ) : ℂ))).im = v₂ at hv₂ H₂ hr
  generalize (F ((c : ℂ) + I * ((ℓ / 2 : ℝ) : ℂ))).im = v₁ at hv₁ H₁ hr
  generalize s11_wm_C₁ L = C at hC H₁ H₂ ⊢
  generalize imgLength h c (3 * ℓ) = B at H₂ ⊢
  generalize imgLength h c ℓ = A at H₁ ⊢
  have e2 : B ≤ 2 * C * v₂ := by
    rw [inv_mul_le_iff₀ (by linarith), div_le_iff₀ (by positivity)] at H₂
    have e : C * (v₂ / (3 * ℓ / 2)) * (3 * ℓ) = 2 * C * v₂ := by
      field_simp
    linarith
  have e1 : v₁ ≤ C * A / 2 := by
    rw [div_le_iff₀ (by positivity)] at H₁
    have e : C * (A / ℓ) * (ℓ / 2) = C * A / 2 := by
      field_simp
    linarith
  have e3 : v₂ ≤ (3 : ℝ) ^ L * v₁ := (div_le_iff₀ hv₁).1 hr
  nlinarith [mul_le_mul_of_nonneg_left e3 (by linarith : (0 : ℝ) ≤ 2 * C),
    mul_le_mul_of_nonneg_left e1 (by positivity : (0 : ℝ) ≤ 2 * C * (3 : ℝ) ^ L)]

/-- Helper (WM6), [WMUC, Lemma 14]: `F(Q_I) ⊆ Q_{α h(I)}` for admissible `F`, pointwise from WM4,
WM5 (`I_z ⊆ 3I`) and WM3 (vertical) at `Re z`. -/
theorem s11_wm_box {F : ℂ → ℂ} {h : ℝ ≃ₜ ℝ} {L : ℝ} (hF : IsHPAdmissible F h L) :
    ∀ c ℓ : ℝ, 0 < ℓ → F '' hpBox c ℓ ⊆ hpBox (imgCenter h c ℓ) (s11_wm_α L * imgLength h c ℓ) := by
  rintro c ℓ hℓ _ ⟨z, ⟨hzc, hy, hyl⟩, rfl⟩
  obtain ⟨hmaps, -, -⟩ := s11_wm_adm_basic hF
  obtain ⟨ω, hω⟩ := hF.2.2.2.2.2.2.2.2
  have hmono := hω.1.monotone
  have hv : 0 < (F z).im := hmaps hy
  have hC := s11_wm_C₁_ge hF.1
  have hσ : 0 ≤ Real.sinh (morseM L 0) := Real.sinh_nonneg_iff.2 (s11_wm_morseM_nonneg hF.1)
  have h3 : 0 < (3 : ℝ) ^ L := by positivity
  have hA : 0 < imgLength h c ℓ := sub_pos.2 (hω.1 (by linarith))
  have H := (s11_wm_height hF hy).2
  have hIz : imgLength h z.re (2 * z.im) ≤ imgLength h c (3 * ℓ) := by
    unfold imgLength
    have h1 := hmono (show z.re + 2 * z.im / 2 ≤ c + 3 * ℓ / 2 by linarith [(abs_le.1 hzc).2])
    have h2 := hmono (show c - 3 * ℓ / 2 ≤ z.re - 2 * z.im / 2 by linarith [(abs_le.1 hzc).1])
    linarith
  have hD := s11_wm_double hF c hℓ
  have hzz : (z.re : ℂ) + I * z.im = z := by rw [mul_comm]; exact re_add_im z
  have hvert := s11_wm_morse_vert hF z.re hy
  rw [hzz] at hvert
  have hx1 := hmono (show c - ℓ / 2 ≤ z.re by linarith [(abs_le.1 hzc).1])
  have hx2 := hmono (show z.re ≤ c + ℓ / 2 by linarith [(abs_le.1 hzc).2])
  rw [div_le_iff₀ hy] at H
  have e : s11_wm_C₁ L * (imgLength h z.re (2 * z.im) / (2 * z.im)) * z.im =
      s11_wm_C₁ L * imgLength h z.re (2 * z.im) / 2 := by
    field_simp
  have hvb : (F z).im ≤ s11_wm_C₁ L ^ 3 * (3 : ℝ) ^ L * imgLength h c ℓ / 2 := by
    have := mul_le_mul_of_nonneg_left (hIz.trans hD) (by linarith : (0 : ℝ) ≤ s11_wm_C₁ L)
    have e' : s11_wm_C₁ L * (s11_wm_C₁ L ^ 2 * (3 : ℝ) ^ L * imgLength h c ℓ) =
        s11_wm_C₁ L ^ 3 * (3 : ℝ) ^ L * imgLength h c ℓ := by ring
    linarith
  have hK : 0 ≤ s11_wm_C₁ L ^ 3 * (3 : ℝ) ^ L := mul_nonneg (pow_nonneg (by linarith) 3) h3.le
  have hσv := mul_le_mul_of_nonneg_left hvb hσ
  have hKσ := mul_nonneg (mul_nonneg hK hσ) hA.le
  have hKA := mul_nonneg hK hA.le
  refine ⟨?_, hv, ?_⟩
  · unfold imgCenter s11_wm_α
    unfold imgLength at hA hσv hKσ hKA ⊢
    rw [abs_le] at hvert ⊢
    constructor <;> nlinarith [hvert.1, hvert.2]
  · unfold s11_wm_α
    nlinarith

/-- Helper (WM6), clause 3 of `HPWMConstants`: `F z ∈ Q_I` implies `z ∈ Q_{α h⁻¹(I)}`, from
`s11_wm_box` for the inverse map given by `hp_admissible_symm`. -/
theorem s11_wm_box_inv {F : ℂ → ℂ} {h : ℝ ≃ₜ ℝ} {L : ℝ} (hF : IsHPAdmissible F h L) :
    ∀ c ℓ : ℝ, 0 < ℓ → ∀ z ∈ upperHalf, F z ∈ hpBox c ℓ →
      z ∈ hpBox (imgCenter h.symm c ℓ) (s11_wm_α L * imgLength h.symm c ℓ) := by
  intro c ℓ hℓ z hz hFz
  obtain ⟨G, hG, hGF⟩ := hp_admissible_symm hF
  have := s11_wm_box hG c ℓ hℓ ⟨F z, hFz, rfl⟩
  rwa [(hGF z (show (0 : ℝ) ≤ z.im from le_of_lt hz)).1] at this

/-- Lemma 11.4 `lem:hp-wm`, `sec11-halfplane.tex:401` (cited from [WMUC, Lemmas 13 and 14]): for
every `L ≥ 1` there are `C₁, α ≥ 1` depending only on `L` with (11.?) `eq:hp-wm-height`,
`F(Q_I) ⊆ Q_{α h(I)}` and (11.?) `eq:hp-wm-box`. -/
theorem lem_hp_wm : ∀ L : ℝ, 1 ≤ L → ∃ C₁ α : ℝ, HPWMConstants L C₁ α := by
  intro L hL
  exact ⟨s11_wm_C₁ L, s11_wm_α L, s11_wm_C₁_ge hL, s11_wm_α_ge hL, fun F h hF =>
    ⟨fun z hz => s11_wm_height hF hz, s11_wm_box hF, s11_wm_box_inv hF⟩⟩

/-- Helper for Lemma 11.5: the nontangential maximal function `NG` of any `G` is lower
semicontinuous (its superlevel sets are unions of the open intervals `(x - y, x + y)`). -/
theorem s11_emb_lsc (G : ℂ → ℝ≥0∞) :
    LowerSemicontinuous (fun t : ℝ => ⨆ (z : ℂ) (_ : |z.re - t| < z.im), G z) := by
  intro t y hy
  have hy' : y < ⨆ (z : ℂ) (_ : |z.re - t| < z.im), G z := hy
  obtain ⟨z, hz⟩ := lt_iSup_iff.mp hy'
  obtain ⟨hzt, hyz⟩ := lt_iSup_iff.mp hz
  have hopen : IsOpen {s : ℝ | |z.re - s| < z.im} := isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds hzt] with s hs
  exact lt_of_lt_of_le hyz (le_iSup₂_of_le (f := fun (w : ℂ) (_ : |w.re - s| < w.im) => G w) z hs le_rfl)

/-- Helper for Lemma 11.5: the layer-cake formula for a measurable `f : α → [0,∞]` and an
arbitrary (not necessarily s-finite) measure, obtained from Mathlib's real version
`lintegral_eq_lintegral_meas_lt` by truncation `min f n`. -/
theorem s11_emb_layer {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ a, f a ∂μ = ∫⁻ u in Ioi (0 : ℝ), μ {a | ENNReal.ofReal u < f a} := by
  have hfin : ∀ (n : ℕ) (a : α), min (f a) n ≠ ⊤ := fun n a =>
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _)
  have hmeas : ∀ n : ℕ, Measurable fun a => min (f a) n := fun n => hf.min measurable_const
  -- the truncated layer-cake formula, from the real version
  have key : ∀ n : ℕ, ∫⁻ a, min (f a) n ∂μ =
      ∫⁻ u in Ioi (0 : ℝ), μ {a | ENNReal.ofReal u < min (f a) n} := by
    intro n
    have h := lintegral_eq_lintegral_meas_lt μ (f := fun a => (min (f a) n).toReal)
      (Eventually.of_forall fun a => ENNReal.toReal_nonneg) (hmeas n).ennreal_toReal.aemeasurable
    have h1 : ∀ a, ENNReal.ofReal (min (f a) n).toReal = min (f a) n := fun a =>
      ENNReal.ofReal_toReal (hfin n a)
    simp only [h1] at h
    rw [h]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    congr 1
    ext a
    exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hu) (hfin n a)).symm
  have hmono : Monotone fun (n : ℕ) (a : α) => min (f a) n := fun n m hnm a =>
    min_le_min le_rfl (Nat.cast_le.mpr hnm)
  have hsup : ∀ a, ⨆ n : ℕ, min (f a) n = f a := by
    intro a
    apply le_antisymm (iSup_le fun n => min_le_left _ _)
    refine le_of_forall_lt fun b hb => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_top_of_lt hb)
    exact lt_of_lt_of_le (lt_min hb hn) (le_iSup (fun n : ℕ => min (f a) n) n)
  have hlev : ∀ u : ℝ, ⨆ n : ℕ, μ {a | ENNReal.ofReal u < min (f a) n} =
      μ {a | ENNReal.ofReal u < f a} := by
    intro u
    have hm : Monotone fun n : ℕ => {a | ENNReal.ofReal u < min (f a) n} := by
      intro n m hnm a ha
      exact (show ENNReal.ofReal u < min (f a) m from
        lt_of_lt_of_le (show ENNReal.ofReal u < min (f a) n from ha)
          (min_le_min le_rfl (Nat.cast_le.mpr hnm)))
    rw [← hm.measure_iUnion]
    congr 1
    ext a
    simp only [mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      exact lt_of_lt_of_le hn (min_le_left _ _)
    · intro ha
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.ofReal_ne_top (r := u))
      exact ⟨n, lt_min ha hn⟩
  have hanti : ∀ n : ℕ, Measurable fun u : ℝ => μ {a | ENNReal.ofReal u < min (f a) n} := by
    intro n
    refine Antitone.measurable fun u v huv => measure_mono fun a ha => ?_
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal huv) ha
  have hmono2 : Monotone fun (n : ℕ) (u : ℝ) => μ {a | ENNReal.ofReal u < min (f a) n} :=
    fun n m hnm u => measure_mono fun a ha =>
      (show ENNReal.ofReal u < min (f a) m from
        lt_of_lt_of_le (show ENNReal.ofReal u < min (f a) n from ha)
          (min_le_min le_rfl (Nat.cast_le.mpr hnm)))
  calc ∫⁻ a, f a ∂μ = ∫⁻ a, ⨆ n : ℕ, min (f a) n ∂μ := by simp only [hsup]
    _ = ⨆ n : ℕ, ∫⁻ a, min (f a) n ∂μ := lintegral_iSup hmeas hmono
    _ = ⨆ n : ℕ, ∫⁻ u in Ioi (0 : ℝ), μ {a | ENNReal.ofReal u < min (f a) n} := by
        simp only [key]
    _ = ∫⁻ u in Ioi (0 : ℝ), ⨆ n : ℕ, μ {a | ENNReal.ofReal u < min (f a) n} :=
        (lintegral_iSup hanti hmono2).symm
    _ = ∫⁻ u in Ioi (0 : ℝ), μ {a | ENNReal.ofReal u < f a} := by simp only [hlev]

/-- Helper for Lemma 11.5: a nonempty open order-connected `C ⊆ ℝ` of finite length is an
interval `(a, b)`; with `c = (a + b)/2`, `ℓ = b - a`, every `z ∈ ℍ` with `(x - y, x + y) ⊆ C`
lies in the box `Q_I = hpBox c ℓ`, and `ℓ ≤ |C|`. -/
theorem s11_emb_interval {C : Set ℝ} (hCo : IsOpen C) (hC : C.OrdConnected) (hne : C.Nonempty)
    (hfin : volume C ≠ ⊤) :
    ∃ c ℓ : ℝ, 0 < ℓ ∧ ENNReal.ofReal ℓ ≤ volume C ∧
      ∀ z : ℂ, 0 < z.im → Ioo (z.re - z.im) (z.re + z.im) ⊆ C → z ∈ hpBox c ℓ := by
  obtain ⟨p, hp⟩ := hne
  have hab : BddAbove C := by
    by_contra h
    apply hfin
    refine measure_mono_top (s₁ := Ici p) (fun q hq => ?_) (by simp)
    obtain ⟨r, hr, hqr⟩ := not_bddAbove_iff.mp h q
    exact hC.out hp hr ⟨hq, hqr.le⟩
  have hbb : BddBelow C := by
    by_contra h
    apply hfin
    refine measure_mono_top (s₁ := Iic p) (fun q hq => ?_) (by simp)
    obtain ⟨r, hr, hrq⟩ := not_bddBelow_iff.mp h q
    exact hC.out hr hp ⟨hrq.le, hq⟩
  set a := sInf C with ha
  set b := sSup C with hb
  have hsub : Ioo a b ⊆ C := by
    intro s hs
    obtain ⟨q, hq, hqs⟩ := exists_lt_of_csInf_lt ⟨p, hp⟩ hs.1
    obtain ⟨r, hr, hsr⟩ := exists_lt_of_lt_csSup ⟨p, hp⟩ hs.2
    exact hC.out hq hr ⟨hqs.le, hsr.le⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hCo p hp
  have h1 : p - ε / 2 ∈ C := hball (by
    rw [Real.ball_eq_Ioo]; exact ⟨by linarith, by linarith⟩)
  have h2 : p + ε / 2 ∈ C := hball (by
    rw [Real.ball_eq_Ioo]; exact ⟨by linarith, by linarith⟩)
  have hlt : a < b := by
    have := csInf_le hbb h1
    have := le_csSup hab h2
    linarith
  refine ⟨(a + b) / 2, b - a, by linarith, ?_, ?_⟩
  · rw [← Real.volume_Ioo]
    exact measure_mono hsub
  · intro z hy hz
    have hne' : (Ioo (z.re - z.im) (z.re + z.im)).Nonempty := nonempty_Ioo.mpr (by linarith)
    have hlo : a ≤ z.re - z.im := by
      rw [← csInf_Ioo (show z.re - z.im < z.re + z.im by linarith)]
      exact le_csInf hne' fun s hs => csInf_le hbb (hz hs)
    have hhi : z.re + z.im ≤ b := by
      rw [← csSup_Ioo (show z.re - z.im < z.re + z.im by linarith)]
      exact csSup_le hne' fun s hs => le_csSup hab (hz hs)
    show |z.re - (a + b) / 2| ≤ (b - a) / 2 ∧ 0 < z.im ∧ z.im ≤ b - a
    exact ⟨abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩, hy, by linarith⟩

/-- Helper for Lemma 11.5 (the covering step, finite-length case): if `U ⊆ ℝ` is open of finite
length and every `z ∈ S` lies in `ℍ` with `(x - y, x + y) ⊆ U`, then `ν(S) ≤ ‖ν‖_CM |U|`
(one box per connected component of `U`). -/
theorem s11_emb_cover_fin (ν : Measure ℂ) {U : Set ℝ} (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    {S : Set ℂ} (hS : ∀ z ∈ S, 0 < z.im ∧ Ioo (z.re - z.im) (z.re + z.im) ⊆ U) :
    ν S ≤ hpCMNorm ν * volume U := by
  set 𝒞 : Set (Set ℝ) := {C | ∃ t ∈ U, C = connectedComponentIn U t} with h𝒞
  have hmem : ∀ C ∈ 𝒞, IsOpen C ∧ C.OrdConnected ∧ C.Nonempty ∧ volume C ≠ ⊤ := by
    intro C hC
    obtain ⟨t, ht, rfl⟩ := hC
    exact ⟨hU.connectedComponentIn,
      isPreconnected_iff_ordConnected.mp isPreconnected_connectedComponentIn,
      ⟨t, mem_connectedComponentIn ht⟩,
      ne_top_of_le_ne_top hfin (measure_mono (connectedComponentIn_subset _ _))⟩
  have hdisj : 𝒞.PairwiseDisjoint (fun C : Set ℝ => C) := by
    intro C hC D hD hCD
    obtain ⟨t, ht, rfl⟩ := hC
    obtain ⟨s, hs, rfl⟩ := hD
    rw [Function.onFun, Set.disjoint_iff]
    intro w hw
    exact hCD ((connectedComponentIn_eq hw.1).trans (connectedComponentIn_eq hw.2).symm)
  have hcount : 𝒞.Countable :=
    hdisj.countable_of_isOpen (fun C hC => (hmem C hC).1) (fun C hC => (hmem C hC).2.2.1)
  choose! c ℓ hℓ hvol hbox using fun C (hC : C ∈ 𝒞) =>
    s11_emb_interval (hmem C hC).1 (hmem C hC).2.1 (hmem C hC).2.2.1 (hmem C hC).2.2.2
  have hcov : S ⊆ ⋃ C ∈ 𝒞, hpBox (c C) (ℓ C) := by
    intro z hz
    obtain ⟨hy, hzU⟩ := hS z hz
    have hx : z.re ∈ Ioo (z.re - z.im) (z.re + z.im) := ⟨by linarith, by linarith⟩
    have hC : connectedComponentIn U z.re ∈ 𝒞 := ⟨z.re, hzU hx, rfl⟩
    exact mem_biUnion hC (hbox _ hC z hy (isPreconnected_Ioo.subset_connectedComponentIn hx hzU))
  have hboxν : ∀ C ∈ 𝒞, ν (hpBox (c C) (ℓ C)) ≤ hpCMNorm ν * volume C := by
    intro C hC
    have hle : ν (hpBox (c C) (ℓ C)) / ENNReal.ofReal (ℓ C) ≤ hpCMNorm ν := by
      unfold hpCMNorm
      exact le_iSup_of_le (c C) (le_iSup_of_le (ℓ C) (le_iSup_of_le (hℓ C hC) le_rfl))
    calc ν (hpBox (c C) (ℓ C)) ≤ hpCMNorm ν * ENNReal.ofReal (ℓ C) :=
          (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr (hℓ C hC)).ne' ENNReal.ofReal_ne_top).mp hle
      _ ≤ hpCMNorm ν * volume C := by gcongr; exact hvol C hC
  calc ν S ≤ ν (⋃ C ∈ 𝒞, hpBox (c C) (ℓ C)) := measure_mono hcov
    _ ≤ ∑' C : 𝒞, ν (hpBox (c C) (ℓ C)) := measure_biUnion_le ν hcount _
    _ ≤ ∑' C : 𝒞, hpCMNorm ν * volume (C : Set ℝ) :=
        tsum_le_tsum fun C => hboxν C C.2
    _ = hpCMNorm ν * ∑' C : 𝒞, volume (C : Set ℝ) := ENNReal.tsum_mul_left
    _ = hpCMNorm ν * volume (⋃ C ∈ 𝒞, C) := by
        rw [measure_biUnion hcount hdisj fun C hC => (hmem C hC).1.measurableSet]
    _ ≤ hpCMNorm ν * volume U := by
        gcongr
        exact iUnion₂_subset fun C hC => by
          obtain ⟨t, _, rfl⟩ := hC
          exact connectedComponentIn_subset _ _

/-- Helper for Lemma 11.5 (the covering step): as `s11_emb_cover_fin`, without finiteness of
`|U|` (exhaust `S` by the bounded pieces `S ∩ {|x| < n, y < n}`, whose intervals lie in
`U ∩ (-2n, 2n)`). -/
theorem s11_emb_cover (ν : Measure ℂ) {U : Set ℝ} (hU : IsOpen U) {S : Set ℂ}
    (hS : ∀ z ∈ S, 0 < z.im ∧ Ioo (z.re - z.im) (z.re + z.im) ⊆ U) :
    ν S ≤ hpCMNorm ν * volume U := by
  set T : ℕ → Set ℂ := fun n => S ∩ {z | |z.re| < n ∧ z.im < n} with hT
  have hmono : Monotone T := fun n m hnm z hz =>
    ⟨hz.1, lt_of_lt_of_le hz.2.1 (Nat.cast_le.mpr hnm), lt_of_lt_of_le hz.2.2 (Nat.cast_le.mpr hnm)⟩
  have hST : S = ⋃ n, T n := by
    ext z
    simp only [hT, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_gt (max |z.re| z.im)
      exact ⟨n, hz, lt_of_le_of_lt (le_max_left _ _) hn, lt_of_le_of_lt (le_max_right _ _) hn⟩
    · rintro ⟨n, hz, _⟩
      exact hz
  have hpiece : ∀ n : ℕ, ν (T n) ≤ hpCMNorm ν * volume U := by
    intro n
    have hfin : volume (U ∩ Ioo (-(2 * (n : ℝ))) (2 * n)) ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) (measure_mono inter_subset_right)
    refine (s11_emb_cover_fin ν (hU.inter isOpen_Ioo) hfin fun z hz => ?_).trans
      (by gcongr; exact inter_subset_left)
    obtain ⟨hzS, hzx, hzy⟩ := hz
    obtain ⟨hy, hsub⟩ := hS z hzS
    obtain ⟨hx1, hx2⟩ := abs_lt.mp hzx
    refine ⟨hy, fun t ht => ⟨hsub ht, ?_, ?_⟩⟩
    · linarith [ht.1]
    · linarith [ht.2]
  rw [hST, hmono.measure_iUnion]
  exact iSup_le hpiece

/-- Lemma 11.5 `lem:hp-embedding`, `sec11-halfplane.tex:421` (Carleson embedding): with
`NG(t) = sup {G(x+iy) : |x - t| < y}`, `NG` is lower semicontinuous and
`∫_ℍ G dν ≤ ‖ν‖_CM ∫_ℝ NG`. -/
theorem lem_hp_embedding (ν : Measure ℂ) {G : ℂ → ℝ≥0∞} (hG : Measurable G) :
    LowerSemicontinuous (fun t : ℝ => ⨆ (z : ℂ) (_ : |z.re - t| < z.im), G z) ∧
      ∫⁻ z in upperHalf, G z ∂ν ≤
        hpCMNorm ν * ∫⁻ t : ℝ, ⨆ (z : ℂ) (_ : |z.re - t| < z.im), G z := by
  refine ⟨s11_emb_lsc G, ?_⟩
  set NG : ℝ → ℝ≥0∞ := fun t => ⨆ (z : ℂ) (_ : |z.re - t| < z.im), G z with hNG
  have hlsc : LowerSemicontinuous NG := s11_emb_lsc G
  -- layer cake on both sides, and the covering bound for each level `u > 0`
  have hlev : ∀ u : ℝ, (ν.restrict upperHalf) {z | ENNReal.ofReal u < G z} ≤
      hpCMNorm ν * volume {t | ENNReal.ofReal u < NG t} := by
    intro u
    rw [Measure.restrict_apply (measurableSet_lt measurable_const hG)]
    refine s11_emb_cover ν (hlsc.isOpen_preimage _) ?_
    intro z hz
    refine ⟨hz.2, fun t ht => ?_⟩
    have hzt : |z.re - t| < z.im := abs_sub_lt_iff.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact lt_of_lt_of_le hz.1 (le_iSup₂_of_le (f := fun (w : ℂ) (_ : |w.re - t| < w.im) => G w)
      z hzt le_rfl)
  have hanti : Antitone fun u : ℝ => volume {t | ENNReal.ofReal u < NG t} := by
    intro u v huv
    exact measure_mono fun t ht => lt_of_le_of_lt (ENNReal.ofReal_le_ofReal huv) ht
  calc ∫⁻ z in upperHalf, G z ∂ν
      = ∫⁻ u in Ioi (0 : ℝ), (ν.restrict upperHalf) {z | ENNReal.ofReal u < G z} :=
        s11_emb_layer _ hG
    _ ≤ ∫⁻ u in Ioi (0 : ℝ), hpCMNorm ν * volume {t | ENNReal.ofReal u < NG t} :=
        lintegral_mono fun u => hlev u
    _ = hpCMNorm ν * ∫⁻ u in Ioi (0 : ℝ), volume {t | ENNReal.ofReal u < NG t} :=
        lintegral_const_mul _ hanti.measurable
    _ = hpCMNorm ν * ∫⁻ t : ℝ, NG t := by
        rw [s11_emb_layer volume hlsc.measurable]

/-- Helper (T0) for Theorem 11.6: `ofReal a * ofReal b ≤ ofReal (a b)` for all real `a, b`. -/
theorem s11_tr_ofReal_mul_le (a b : ℝ) :
    ENNReal.ofReal a * ENNReal.ofReal b ≤ ENNReal.ofReal (a * b) := by
  rcases le_or_gt 0 a with ha | ha
  · rw [ENNReal.ofReal_mul ha]
  · rw [ENNReal.ofReal_of_nonpos ha.le, zero_mul]
    exact zero_le

/-- Helper (T0) for Theorem 11.6: `3α ≤ 2^k`, `k = ⌈log₂(3α)⌉`. -/
theorem s11_tr_pow_ge {α : ℝ} (hα : 1 ≤ α) : 3 * α ≤ (2 : ℝ) ^ ⌈Real.logb 2 (3 * α)⌉₊ := by
  have h3 : 0 < 3 * α := by linarith
  calc 3 * α = (2 : ℝ) ^ (Real.logb 2 (3 * α)) :=
        (Real.rpow_logb (by norm_num) (by norm_num) h3).symm
    _ ≤ (2 : ℝ) ^ ((⌈Real.logb 2 (3 * α)⌉₊ : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    _ = _ := Real.rpow_natCast _ _

/-- Helper (T0) for Theorem 11.6: the doubling constant `D_h` is nonnegative. -/
theorem s11_tr_D_nonneg {h : ℝ → ℝ} {D p Ch : ℝ} (hd : IsSQSData h D p Ch) : 0 ≤ D := by
  obtain ⟨ω, hω, hD, -⟩ := hd
  have h1 := hD 0 1 one_pos
  have hp1 : 0 < imgLength h 0 1 := sub_pos.2 (hω.1 (by norm_num))
  have hp2 : 0 < imgLength h 0 (2 * 1) := sub_pos.2 (hω.1 (by norm_num))
  by_contra hc
  push_neg at hc
  nlinarith [mul_neg_of_neg_of_pos hc hp1]

/-- Helper (T0) for Theorem 11.6: for `J = h⁻¹(I)`, `|h(J)| = |I|` and `|J| > 0`. -/
theorem s11_tr_J (h : ℝ ≃ₜ ℝ) (hmono : StrictMono h) (c : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    imgLength h (imgCenter h.symm c ℓ) (imgLength h.symm c ℓ) = ℓ ∧ 0 < imgLength h.symm c ℓ := by
  have e1 : imgCenter h.symm c ℓ + imgLength h.symm c ℓ / 2 = h.symm (c + ℓ / 2) := by
    unfold imgCenter imgLength
    ring
  have e2 : imgCenter h.symm c ℓ - imgLength h.symm c ℓ / 2 = h.symm (c - ℓ / 2) := by
    unfold imgCenter imgLength
    ring
  refine ⟨?_, ?_⟩
  · rw [show imgLength h (imgCenter h.symm c ℓ) (imgLength h.symm c ℓ) =
      h (imgCenter h.symm c ℓ + imgLength h.symm c ℓ / 2) -
        h (imgCenter h.symm c ℓ - imgLength h.symm c ℓ / 2) from rfl, e1, e2,
      h.apply_symm_apply, h.apply_symm_apply]
    ring
  · show 0 < h.symm (c + ℓ / 2) - h.symm (c - ℓ / 2)
    by_contra hc
    push_neg at hc
    have := hmono.monotone (sub_nonpos.1 hc)
    rw [h.apply_symm_apply, h.apply_symm_apply] at this
    linarith

/-- Helper (T4) for Theorem 11.6: iterated doubling `|h(2^k I)| ≤ D^k |h(I)|`. -/
theorem s11_tr_double_iter {h : ℝ → ℝ} {D p Ch : ℝ} (hd : IsSQSData h D p Ch) (c : ℝ) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (k : ℕ) : imgLength h c (2 ^ k * ℓ) ≤ D ^ k * imgLength h c ℓ := by
  have hD0 := s11_tr_D_nonneg hd
  obtain ⟨ω, hω, hD, -⟩ := hd
  induction k with
  | zero => simp
  | succ k ih =>
    calc imgLength h c (2 ^ (k + 1) * ℓ) = imgLength h c (2 * (2 ^ k * ℓ)) := by
          congr 1
          ring
      _ ≤ D * imgLength h c (2 ^ k * ℓ) := hD c _ (by positivity)
      _ ≤ D * (D ^ k * imgLength h c ℓ) := mul_le_mul_of_nonneg_left ih hD0
      _ = D ^ (k + 1) * imgLength h c ℓ := by ring

/-- Helper for Theorem 11.6: the boxes `Q_I` are Borel. -/
theorem s11_tr_box_meas (c ℓ : ℝ) : MeasurableSet (hpBox c ℓ) := by
  have h1 : Measurable fun z : ℂ => |z.re - c| := by fun_prop
  exact (measurableSet_le h1 measurable_const).inter
    ((measurableSet_lt measurable_const Complex.measurable_im).inter
      (measurableSet_le Complex.measurable_im measurable_const))

/-- Helper (T5) for Theorem 11.6, Step 6: `‖λ|_{Q_I}‖_CM ≤ ε_λ(|I|)`. -/
theorem s11_tr_local_norm (μ : Measure ℂ) (c : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    hpCMNorm (μ.restrict (hpBox c ℓ)) ≤ hpEps μ ℓ := by
  unfold hpCMNorm
  refine iSup₂_le fun c' ℓ' => iSup_le fun hℓ' => ?_
  rcases le_or_gt ℓ' ℓ with hle | hlt
  · calc μ.restrict (hpBox c ℓ) (hpBox c' ℓ') / ENNReal.ofReal ℓ'
        ≤ μ (hpBox c' ℓ') / ENNReal.ofReal ℓ' :=
          ENNReal.div_le_div_right (Measure.le_iff'.1 Measure.restrict_le_self _) _
      _ ≤ hpEps μ ℓ := le_iSup₂_of_le c' ℓ' (le_iSup₂_of_le hℓ' hle le_rfl)
  · calc μ.restrict (hpBox c ℓ) (hpBox c' ℓ') / ENNReal.ofReal ℓ'
        ≤ μ (hpBox c ℓ) / ENNReal.ofReal ℓ := by
          refine ENNReal.div_le_div ?_ (ENNReal.ofReal_le_ofReal hlt.le)
          calc μ.restrict (hpBox c ℓ) (hpBox c' ℓ') ≤ μ.restrict (hpBox c ℓ) univ :=
                measure_mono (subset_univ _)
            _ = μ (hpBox c ℓ) := Measure.restrict_apply_univ _
      _ ≤ hpEps μ ℓ := le_iSup₂_of_le c ℓ (le_iSup₂_of_le hℓ le_rfl le_rfl)

/-- Helper (T1) for Theorem 11.6, Step 1: change of variables, the inverse box inclusion and the
height bound of Lemma 11.4 give `λ_F(Q_I) ≤ C₁ ∫ G dλ_J`, `G = ω̃ 1_{Q_{αJ}}`. -/
theorem s11_tr_step1 {L C₁ α : ℝ} (hwm : HPWMConstants L C₁ α) {F : ℂ → ℂ} {h : ℝ ≃ₜ ℝ}
    (hF : IsHPAdmissible F h L) (m : Measure ℂ) (c : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    hpPushWeight F m (hpBox c ℓ) ≤ ENNReal.ofReal C₁ *
      ∫⁻ z in upperHalf, (hpBox (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ)).indicator
        (fun z => ENNReal.ofReal (imgLength h z.re (2 * z.im) / (2 * z.im))) z ∂
        ((hpWeight m).restrict (hpBox (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ))) := by
  obtain ⟨hC1, -, hall⟩ := hwm
  obtain ⟨hht, -, hinv⟩ := hall F h hF
  obtain ⟨ω, hω⟩ := hF.2.2.2.2.2.2.2.2
  have hmono := hω.1.monotone
  have hQm := s11_tr_box_meas (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ)
  have hUm : MeasurableSet upperHalf := measurableSet_lt measurable_const Complex.measurable_im
  have hρ : Measurable fun z : ℂ => ENNReal.ofReal z.im :=
    ENNReal.measurable_ofReal.comp Complex.measurable_im
  have hgm : Measurable fun z : ℂ => ENNReal.ofReal (imgLength h z.re (2 * z.im) / (2 * z.im)) := by
    have hm : Measurable h := h.continuous.measurable
    simp only [imgLength]
    fun_prop
  have hFae : AEMeasurable F (m.restrict upperHalf) :=
    (hF.2.2.2.2.1.mono fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt hz).aemeasurable hUm
  have hL : hpPushWeight F m (hpBox c ℓ) =
      ∫⁻ z in upperHalf, (hpBox c ℓ).indicator (fun w => ENNReal.ofReal w.im) (F z) ∂m := by
    unfold hpPushWeight hpWeight hpPush
    rw [withDensity_apply _ (s11_tr_box_meas c ℓ), ← lintegral_indicator (s11_tr_box_meas c ℓ),
      lintegral_map' ((hρ.indicator (s11_tr_box_meas c ℓ)).aemeasurable) hFae]
  have hR : ∫⁻ z in upperHalf, (hpBox (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ)).indicator
        (fun z => ENNReal.ofReal (imgLength h z.re (2 * z.im) / (2 * z.im))) z ∂
        ((hpWeight m).restrict (hpBox (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ))) =
      ∫⁻ z in hpBox (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ),
        ENNReal.ofReal (imgLength h z.re (2 * z.im) / (2 * z.im)) * ENNReal.ofReal z.im ∂m := by
    have hsub : hpBox (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ) ⊆ upperHalf :=
      fun z hz => hz.2.1
    rw [Measure.restrict_eq_self_of_ae_mem ((ae_restrict_mem hQm).mono fun z hz => hsub hz)]
    unfold hpWeight
    rw [restrict_withDensity hQm, lintegral_withDensity_eq_lintegral_mul _ hρ (hgm.indicator hQm)]
    refine setLIntegral_congr_fun hQm (fun z hz => ?_)
    rw [Pi.mul_apply, Set.indicator_of_mem hz, mul_comm]
  rw [hL, hR, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ∫⁻ z in upperHalf, (hpBox c ℓ).indicator (fun w => ENNReal.ofReal w.im) (F z) ∂m
      ≤ ∫⁻ z in upperHalf, (hpBox (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ)).indicator
          (fun z => ENNReal.ofReal C₁ * (ENNReal.ofReal (imgLength h z.re (2 * z.im) / (2 * z.im)) *
            ENNReal.ofReal z.im)) z ∂m := by
        refine lintegral_mono_ae ((ae_restrict_mem hUm).mono fun z hz => ?_)
        by_cases hFz : F z ∈ hpBox c ℓ
        · have hzQ := hinv c ℓ hℓ z hz hFz
          rw [Set.indicator_of_mem hFz, Set.indicator_of_mem hzQ]
          have hy : 0 < z.im := hz
          have h2 := (hht z hz).2
          have hω0 : 0 ≤ imgLength h z.re (2 * z.im) / (2 * z.im) :=
            div_nonneg (sub_nonneg.2 (hmono (by linarith))) (by linarith)
          rw [div_le_iff₀ hy] at h2
          rw [← ENNReal.ofReal_mul hω0, ← ENNReal.ofReal_mul (by linarith)]
          exact ENNReal.ofReal_le_ofReal (by nlinarith [h2])
        · rw [Set.indicator_of_notMem hFz]
          exact zero_le
    _ ≤ ∫⁻ z, (hpBox (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ)).indicator
          (fun z => ENNReal.ofReal C₁ * (ENNReal.ofReal (imgLength h z.re (2 * z.im) / (2 * z.im)) *
            ENNReal.ofReal z.im)) z ∂m := setLIntegral_le_lintegral _ _
    _ = _ := lintegral_indicator hQm _

/-- Helper (T2) for Theorem 11.6, Step 3: for `G = ω̃ 1_{Q_I}`, `NG ≤ 1_{3I} M_u φ` with
`φ = 1_{3I} |ψ|` and `ψ = ω` a.e. (`ω̃(z)` is the `ω`-average over `I_z ⊆ 3I`). -/
theorem s11_tr_NG_le {h ω : ℝ → ℝ} (hω : IsSQSWith h ω) {ψ : ℝ → ℝ} (hψ : ψ =ᵐ[volume] ω)
    (c : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) :
    (⨆ (z : ℂ) (_ : |z.re - t| < z.im), (hpBox c ℓ).indicator
        (fun z => ENNReal.ofReal (imgLength h z.re (2 * z.im) / (2 * z.im))) z) ≤
      (Icc (c - 3 * ℓ / 2) (c + 3 * ℓ / 2)).indicator
        (maxFnU ((Icc (c - 3 * ℓ / 2) (c + 3 * ℓ / 2)).indicator fun x => |ψ x|)) t := by
  refine iSup₂_le fun z hzt => ?_
  by_cases hzQ : z ∈ hpBox c ℓ
  swap
  · rw [Set.indicator_of_notMem hzQ]
    exact zero_le
  rw [Set.indicator_of_mem hzQ]
  obtain ⟨hzc, hy, hyl⟩ := hzQ
  have hzc' := abs_le.1 hzc
  have hzt' := abs_lt.1 hzt
  have hIK : Icc (z.re - z.im) (z.re + z.im) ⊆ Icc (c - 3 * ℓ / 2) (c + 3 * ℓ / 2) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have htK : t ∈ Icc (c - 3 * ℓ / 2) (c + 3 * ℓ / 2) := hIK ⟨by linarith, by linarith⟩
  rw [Set.indicator_of_mem htK]
  have himg := s11_rh_img hω (c := z.re) (ℓ := 2 * z.im) (by linarith)
  rw [show z.re - 2 * z.im / 2 = z.re - z.im by ring,
    show z.re + 2 * z.im / 2 = z.re + z.im by ring] at himg
  have hint : IntegrableOn ω (Icc (z.re - z.im) (z.re + z.im)) :=
    hω.2.2.2.1.2.1.integrableOn_isCompact isCompact_Icc
  have hlin : ENNReal.ofReal (∫ x in Icc (z.re - z.im) (z.re + z.im), ω x) =
      ∫⁻ x in Icc (z.re - z.im) (z.re + z.im),
        ENNReal.ofReal |(Icc (c - 3 * ℓ / 2) (c + 3 * ℓ / 2)).indicator (fun x => |ψ x|) x| := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => hω.2.2.2.1.1 x)]
    refine lintegral_congr_ae ((ae_restrict_iff' measurableSet_Icc).2 (hψ.mono fun x hx hxI => ?_))
    beta_reduce
    rw [Set.indicator_of_mem (hIK hxI), abs_abs, hx, abs_of_nonneg (hω.2.2.2.1.1 x)]
  rw [ENNReal.ofReal_div_of_pos (by linarith), himg, hlin]
  unfold maxFnU
  refine le_iSup₂_of_le (z.re - z.im) (z.re + z.im)
    (le_iSup₂_of_le (by linarith) (by linarith) (le_iSup_of_le (by linarith) (le_of_eq ?_)))
  rw [show z.re + z.im - (z.re - z.im) = 2 * z.im by ring]

/-- Helper (T3) for Theorem 11.6, Step 4: Hölder on `K = I`, the maximal theorem and the reverse
Hölder inequality give `∫ 1_K M_u φ ≤ A_p C_h |h(K)|` for `φ = 1_K |ψ|`, `ψ = ω` a.e. -/
theorem s11_tr_step4 {A : ℝ → ℝ} (hA : IsMaximalConst A) {h ω : ℝ → ℝ} (hω : IsSQSWith h ω)
    {p Ch : ℝ} (hp : 1 < p)
    (hRH : ∀ a b : ℝ, a < b →
      ((∫⁻ x in Icc a b, ENNReal.ofReal (ω x ^ p)) / ENNReal.ofReal (b - a)) ^ (1 / p) ≤
        ENNReal.ofReal Ch * ((∫⁻ x in Icc a b, ENNReal.ofReal (ω x)) / ENNReal.ofReal (b - a)))
    {ψ : ℝ → ℝ} (hψm : Measurable ψ) (hψ : ψ =ᵐ[volume] ω) (c : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫⁻ t, (Icc (c - ℓ / 2) (c + ℓ / 2)).indicator
        (maxFnU ((Icc (c - ℓ / 2) (c + ℓ / 2)).indicator fun x => |ψ x|)) t ≤
      ENNReal.ofReal (A p) * ENNReal.ofReal Ch * ENNReal.ofReal (imgLength h c ℓ) := by
  have hKm : MeasurableSet (Icc (c - ℓ / 2) (c + ℓ / 2)) := measurableSet_Icc
  have hω0 := hω.2.2.2.1.1
  have hφm : Measurable ((Icc (c - ℓ / 2) (c + ℓ / 2)).indicator fun x => |ψ x|) :=
    (continuous_abs.measurable.comp hψm).indicator hKm
  have hMm := (s11_max_lsc ((Icc (c - ℓ / 2) (c + ℓ / 2)).indicator fun x => |ψ x|)).measurable
  have hvol : volume (Icc (c - ℓ / 2) (c + ℓ / 2)) = ENNReal.ofReal ℓ := by
    rw [Real.volume_Icc]
    congr 1
    ring
  have hp0 : 0 < p := by linarith
  have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp
  have hH : ∫⁻ t in Icc (c - ℓ / 2) (c + ℓ / 2),
        maxFnU ((Icc (c - ℓ / 2) (c + ℓ / 2)).indicator fun x => |ψ x|) t ≤
      (∫⁻ t in Icc (c - ℓ / 2) (c + ℓ / 2),
        maxFnU ((Icc (c - ℓ / 2) (c + ℓ / 2)).indicator fun x => |ψ x|) t ^ p) ^ (1 / p) *
        ENNReal.ofReal ℓ ^ (1 / p.conjExponent) := by
    have := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Icc (c - ℓ / 2) (c + ℓ / 2))) hpq
      hMm.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simpa [hvol] using this
  have hφp : ∫⁻ t, ENNReal.ofReal
        |(Icc (c - ℓ / 2) (c + ℓ / 2)).indicator (fun x => |ψ x|) t| ^ p =
      ∫⁻ t in Icc (c - ℓ / 2) (c + ℓ / 2), ENNReal.ofReal (ω t ^ p) := by
    rw [← lintegral_indicator hKm]
    refine lintegral_congr_ae (hψ.mono fun t ht => ?_)
    by_cases htK : t ∈ Icc (c - ℓ / 2) (c + ℓ / 2)
    · rw [Set.indicator_of_mem htK]
      beta_reduce
      rw [Set.indicator_of_mem htK, abs_abs, ht, abs_of_nonneg (hω0 t),
        ENNReal.ofReal_rpow_of_nonneg (hω0 t) hp0.le]
    · rw [Set.indicator_of_notMem htK]
      beta_reduce
      rw [Set.indicator_of_notMem htK, abs_zero, ENNReal.ofReal_zero,
        ENNReal.zero_rpow_of_pos hp0]
  have hY : ∫⁻ t in Icc (c - ℓ / 2) (c + ℓ / 2), ENNReal.ofReal (ω t) =
      ENNReal.ofReal (imgLength h c ℓ) := by
    rw [s11_rh_img hω hℓ.le, ofReal_integral_eq_lintegral_ofReal
      (hω.2.2.2.1.2.1.integrableOn_isCompact isCompact_Icc) (Eventually.of_forall hω0)]
  have hXY : (∫⁻ t in Icc (c - ℓ / 2) (c + ℓ / 2), ENNReal.ofReal (ω t ^ p)) ^ (1 / p) *
        ENNReal.ofReal ℓ ^ (1 / p.conjExponent) ≤
      ENNReal.ofReal Ch * ∫⁻ t in Icc (c - ℓ / 2) (c + ℓ / 2), ENNReal.ofReal (ω t) := by
    have hR := hRH (c - ℓ / 2) (c + ℓ / 2) (by linarith)
    rw [show c + ℓ / 2 - (c - ℓ / 2) = ℓ by ring] at hR
    have hl0 : ENNReal.ofReal ℓ ≠ 0 := (ENNReal.ofReal_pos.2 hℓ).ne'
    have hlt : ENNReal.ofReal ℓ ≠ ⊤ := ENNReal.ofReal_ne_top
    generalize ∫⁻ t in Icc (c - ℓ / 2) (c + ℓ / 2), ENNReal.ofReal (ω t ^ p) = X at hR ⊢
    generalize ∫⁻ t in Icc (c - ℓ / 2) (c + ℓ / 2), ENNReal.ofReal (ω t) = Y at hR ⊢
    generalize ENNReal.ofReal ℓ = e at hR hl0 hlt ⊢
    have e1 : X ^ (1 / p) = (X / e) ^ (1 / p) * e ^ (1 / p) := by
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.div_mul_cancel hl0 hlt]
    have e2 : e ^ (1 / p) * e ^ (1 / p.conjExponent) = e := by
      rw [← ENNReal.rpow_add _ _ hl0 hlt, one_div, one_div, hpq.inv_add_inv_eq_one, ENNReal.rpow_one]
    calc X ^ (1 / p) * e ^ (1 / p.conjExponent)
        = (X / e) ^ (1 / p) * (e ^ (1 / p) * e ^ (1 / p.conjExponent)) := by rw [e1, mul_assoc]
      _ = (X / e) ^ (1 / p) * e := by rw [e2]
      _ ≤ ENNReal.ofReal Ch * (Y / e) * e := by gcongr ?_ * _
      _ = ENNReal.ofReal Ch * Y := by rw [mul_assoc, ENNReal.div_mul_cancel hl0 hlt]
  rw [lintegral_indicator hKm]
  calc _ ≤ _ := hH
    _ ≤ ENNReal.ofReal (A p) * (∫⁻ t, ENNReal.ofReal
          |(Icc (c - ℓ / 2) (c + ℓ / 2)).indicator (fun x => |ψ x|) t| ^ p) ^ (1 / p) *
          ENNReal.ofReal ℓ ^ (1 / p.conjExponent) := by
        gcongr ?_ * _
        exact (ENNReal.rpow_le_rpow (setLIntegral_le_lintegral _ _) (by positivity)).trans
          (hA p hp _ hφm)
    _ = ENNReal.ofReal (A p) *
          ((∫⁻ t in Icc (c - ℓ / 2) (c + ℓ / 2), ENNReal.ofReal (ω t ^ p)) ^ (1 / p) *
            ENNReal.ofReal ℓ ^ (1 / p.conjExponent)) := by rw [hφp, mul_assoc]
    _ ≤ ENNReal.ofReal (A p) *
          (ENNReal.ofReal Ch * ∫⁻ t in Icc (c - ℓ / 2) (c + ℓ / 2), ENNReal.ofReal (ω t)) :=
        by gcongr ENNReal.ofReal (A p) * ?_
    _ = _ := by rw [hY, mul_assoc]

/-- Helper (T6) for Theorem 11.6: restriction does not increase `‖·‖_CM`. -/
theorem s11_tr_cm_restrict (μ : Measure ℂ) (s : Set ℂ) : hpCMNorm (μ.restrict s) ≤ hpCMNorm μ :=
  iSup₂_le fun c ℓ => iSup_le fun hℓ => le_iSup₂_of_le c ℓ (le_iSup_of_le hℓ
    (ENNReal.div_le_div_right (Measure.le_iff'.1 Measure.restrict_le_self _) _))

/-- Helper (T6) for Theorem 11.6: Steps 1–5 give the first inequality of (11.?) `eq:hp-local`,
`λ_F(Q_I)/|I| ≤ C ‖λ|_{Q_{αJ}}‖_CM`. -/
theorem s11_tr_box {L C₁ α : ℝ} (hwm : HPWMConstants L C₁ α) {A : ℝ → ℝ} (hA : IsMaximalConst A)
    {F : ℂ → ℂ} {h : ℝ ≃ₜ ℝ} (hF : IsHPAdmissible F h L) {D p Ch : ℝ}
    (hdata : IsSQSData h D p Ch) (m : Measure ℂ) (c : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    hpPushWeight F m (hpBox c ℓ) / ENNReal.ofReal ℓ ≤
      ENNReal.ofReal (hpTransferConst C₁ α A D p Ch) *
        hpCMNorm ((hpWeight m).restrict
          (hpBox (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ))) := by
  have hα := hwm.2.1
  have hD0 := s11_tr_D_nonneg hdata
  have hdbl := s11_tr_double_iter hdata
  have h1 := s11_tr_step1 hwm hF m c hℓ
  obtain ⟨ω, hω, -, hp, hRH⟩ := hdata
  have hmono := hω.1
  obtain ⟨hJ, hJpos⟩ := s11_tr_J h hmono c hℓ
  have hαJ : 0 < α * imgLength h.symm c ℓ := mul_pos (by linarith) hJpos
  obtain ⟨ψ, hψm, hψ⟩ : ∃ ψ : ℝ → ℝ, Measurable ψ ∧ ψ =ᵐ[volume] ω :=
    ⟨_, hω.2.2.2.1.2.1.aestronglyMeasurable.aemeasurable.measurable_mk,
      hω.2.2.2.1.2.1.aestronglyMeasurable.aemeasurable.ae_eq_mk.symm⟩
  have hgm : Measurable fun z : ℂ => ENNReal.ofReal (imgLength h z.re (2 * z.im) / (2 * z.im)) := by
    have hm : Measurable h := h.continuous.measurable
    simp only [imgLength]
    fun_prop
  have hGm := hgm.indicator (s11_tr_box_meas (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ))
  have h2 := (lem_hp_embedding ((hpWeight m).restrict
    (hpBox (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ))) hGm).2
  have h3 := (lintegral_mono fun t => s11_tr_NG_le hω hψ (imgCenter h.symm c ℓ) hαJ t).trans
    (s11_tr_step4 hA hω hp hRH hψm hψ (imgCenter h.symm c ℓ) (by positivity : 0 < 3 * (α * imgLength h.symm c ℓ)))
  have hk := s11_tr_pow_ge hα
  have h4 : imgLength h (imgCenter h.symm c ℓ) (3 * (α * imgLength h.symm c ℓ)) ≤
      D ^ ⌈Real.logb 2 (3 * α)⌉₊ * ℓ := by
    have hle : 3 * (α * imgLength h.symm c ℓ) ≤
        (2 : ℝ) ^ ⌈Real.logb 2 (3 * α)⌉₊ * imgLength h.symm c ℓ := by nlinarith
    have hm1 := hmono.monotone (show imgCenter h.symm c ℓ - (2 : ℝ) ^ ⌈Real.logb 2 (3 * α)⌉₊ *
      imgLength h.symm c ℓ / 2 ≤ imgCenter h.symm c ℓ - 3 * (α * imgLength h.symm c ℓ) / 2 by linarith)
    have hm2 := hmono.monotone (show imgCenter h.symm c ℓ + 3 * (α * imgLength h.symm c ℓ) / 2 ≤
      imgCenter h.symm c ℓ + (2 : ℝ) ^ ⌈Real.logb 2 (3 * α)⌉₊ * imgLength h.symm c ℓ / 2 by linarith)
    have hd := hdbl (imgCenter h.symm c ℓ) hJpos ⌈Real.logb 2 (3 * α)⌉₊
    rw [hJ] at hd
    refine le_trans ?_ hd
    show h (imgCenter h.symm c ℓ + 3 * (α * imgLength h.symm c ℓ) / 2) -
        h (imgCenter h.symm c ℓ - 3 * (α * imgLength h.symm c ℓ) / 2) ≤
      h (imgCenter h.symm c ℓ + (2 : ℝ) ^ ⌈Real.logb 2 (3 * α)⌉₊ * imgLength h.symm c ℓ / 2) -
        h (imgCenter h.symm c ℓ - (2 : ℝ) ^ ⌈Real.logb 2 (3 * α)⌉₊ * imgLength h.symm c ℓ / 2)
    linarith
  have hmain : hpPushWeight F m (hpBox c ℓ) ≤ ENNReal.ofReal C₁ *
      (hpCMNorm ((hpWeight m).restrict (hpBox (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ))) *
        (ENNReal.ofReal (A p) * ENNReal.ofReal Ch * ENNReal.ofReal (D ^ ⌈Real.logb 2 (3 * α)⌉₊ * ℓ))) :=
    h1.trans (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left (h3.trans
      (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal h4) zero_le)) zero_le)) zero_le)
  rw [ENNReal.ofReal_mul (pow_nonneg hD0 _)] at hmain
  have hK : ENNReal.ofReal C₁ * ENNReal.ofReal (A p) * ENNReal.ofReal Ch *
      ENNReal.ofReal (D ^ ⌈Real.logb 2 (3 * α)⌉₊) ≤ ENNReal.ofReal (hpTransferConst C₁ α A D p Ch) := by
    unfold hpTransferConst
    refine le_trans (mul_le_mul_of_nonneg_right ?_ zero_le) (s11_tr_ofReal_mul_le _ _)
    refine le_trans (mul_le_mul_of_nonneg_right ?_ zero_le) (s11_tr_ofReal_mul_le _ _)
    exact s11_tr_ofReal_mul_le _ _
  refine ENNReal.div_le_of_le_mul (hmain.trans ?_)
  calc ENNReal.ofReal C₁ *
        (hpCMNorm ((hpWeight m).restrict (hpBox (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ))) *
          (ENNReal.ofReal (A p) * ENNReal.ofReal Ch *
            (ENNReal.ofReal (D ^ ⌈Real.logb 2 (3 * α)⌉₊) * ENNReal.ofReal ℓ)))
      = ENNReal.ofReal C₁ * ENNReal.ofReal (A p) * ENNReal.ofReal Ch *
          ENNReal.ofReal (D ^ ⌈Real.logb 2 (3 * α)⌉₊) *
          hpCMNorm ((hpWeight m).restrict (hpBox (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ))) *
          ENNReal.ofReal ℓ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK zero_le) zero_le

/-- Theorem 11.6 `thm:hp-transfer`, `sec11-halfplane.tex:451`: with `C₁, α` as in Lemma
`lem:hp-wm`, `A` the constants of the maximal theorem and `C = C₁ A_{p_h} C_h D_h^k`, for every
`m` and every interval `I` (`J = h⁻¹(I)`) the local bound (11.?) `eq:hp-local` holds, hence
`‖λ_F‖_CM ≤ C ‖λ‖_CM`; and if `h⁻¹` is uniformly continuous, (11.?) `eq:hp-uc` holds and
`λ ∈ CM₀ ⇒ λ_F ∈ CM₀`.

NOTES gap 2 is closed here: `lem_hp_wm` gives `C₁ = s11_wm_C₁ L` and `α = s11_wm_α L`, functions of `L`
alone, so `C = hpTransferConst C₁ α A D p Ch` depends only on `L`, the universal `A` of
`eq_hp_maximal` and the SQS data `(D, p, Ch)` of `h`. NOTES gap 11 (no explicit `(p_h, C_h)`) is not
a correctness gap: the theorem holds for every `IsSQSData h D p Ch`, which exists by `eq_hp_RH`. -/
theorem thm_hp_transfer {L C₁ α : ℝ} (hwm : HPWMConstants L C₁ α) {A : ℝ → ℝ}
    (hA : IsMaximalConst A) {F : ℂ → ℂ} {h : ℝ ≃ₜ ℝ} (hF : IsHPAdmissible F h L) {D p Ch : ℝ}
    (hdata : IsSQSData h D p Ch) (m : Measure ℂ) :
    (∀ c ℓ : ℝ, 0 < ℓ →
      hpPushWeight F m (hpBox c ℓ) / ENNReal.ofReal ℓ ≤
          ENNReal.ofReal (hpTransferConst C₁ α A D p Ch) *
            hpCMNorm ((hpWeight m).restrict
              (hpBox (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ))) ∧
        hpCMNorm ((hpWeight m).restrict (hpBox (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ))) ≤
          hpEps (hpWeight m) (α * imgLength h.symm c ℓ)) ∧
      hpCMNorm (hpPushWeight F m) ≤
        ENNReal.ofReal (hpTransferConst C₁ α A D p Ch) * hpCMNorm (hpWeight m) ∧
      (UniformContinuous h.symm →
        (∀ r : ℝ, 0 < r → hpEps (hpPushWeight F m) r ≤
          ENNReal.ofReal (hpTransferConst C₁ α A D p Ch) *
            hpEps (hpWeight m) (α * modCont h.symm r)) ∧
        (IsHPVanishingCarleson (hpWeight m) → IsHPVanishingCarleson (hpPushWeight F m))) := by
  have hα := hwm.2.1
  have hmono : StrictMono h := by
    obtain ⟨ω, hω, -⟩ := hdata
    exact hω.1
  have hbox := fun c ℓ (hℓ : 0 < ℓ) => s11_tr_box hwm hA hF hdata m c hℓ
  have hloc : ∀ c ℓ : ℝ, 0 < ℓ → hpCMNorm ((hpWeight m).restrict
      (hpBox (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ))) ≤
        hpEps (hpWeight m) (α * imgLength h.symm c ℓ) := fun c ℓ hℓ =>
    s11_tr_local_norm _ _ (mul_pos (by linarith) (s11_tr_J h hmono c hℓ).2)
  have hcm : hpCMNorm (hpPushWeight F m) ≤
      ENNReal.ofReal (hpTransferConst C₁ α A D p Ch) * hpCMNorm (hpWeight m) := by
    show (⨆ (c : ℝ) (ℓ : ℝ) (_ : 0 < ℓ), hpPushWeight F m (hpBox c ℓ) / ENNReal.ofReal ℓ) ≤ _
    exact iSup₂_le fun c ℓ => iSup_le fun hℓ => (hbox c ℓ hℓ).trans
      (mul_le_mul_of_nonneg_left (s11_tr_cm_restrict _ _) zero_le)
  refine ⟨fun c ℓ hℓ => ⟨hbox c ℓ hℓ, hloc c ℓ hℓ⟩, hcm, fun hUC => ?_⟩
  obtain ⟨hbdd, hmonoC, hlimC⟩ := hp_modCont hUC
  have hJle : ∀ c ℓ : ℝ, 0 < ℓ → ∀ r, ℓ ≤ r → imgLength h.symm c ℓ ≤ modCont h.symm r := by
    intro c ℓ hℓ r hr
    have h1 : imgLength h.symm c ℓ ≤ modCont h.symm ℓ :=
      le_csSup (hbdd ℓ hℓ.le) ⟨c - ℓ / 2, c + ℓ / 2,
        by rw [show c + ℓ / 2 - (c - ℓ / 2) = ℓ by ring, abs_of_pos hℓ],
        (abs_of_pos (s11_tr_J h hmono c hℓ).2).symm⟩
    exact h1.trans (hmonoC (mem_Ici.2 hℓ.le) (mem_Ici.2 (hℓ.le.trans hr)) hr)
  have heps : ∀ r : ℝ, 0 < r → hpEps (hpPushWeight F m) r ≤
      ENNReal.ofReal (hpTransferConst C₁ α A D p Ch) *
        hpEps (hpWeight m) (α * modCont h.symm r) := by
    intro r hr
    show (⨆ (c : ℝ) (ℓ : ℝ) (_ : 0 < ℓ) (_ : ℓ ≤ r),
      hpPushWeight F m (hpBox c ℓ) / ENNReal.ofReal ℓ) ≤ _
    refine iSup₂_le fun c ℓ => iSup₂_le fun hℓ hℓr => ?_
    refine (hbox c ℓ hℓ).trans (mul_le_mul_of_nonneg_left ((hloc c ℓ hℓ).trans
      ((hp_eps_mono_le _).1 ?_)) zero_le)
    exact mul_le_mul_of_nonneg_left (hJle c ℓ hℓ r hℓr) (by linarith)
  refine ⟨heps, fun hvan => ⟨?_, ?_⟩⟩
  · exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvan.1) hcm
  · have hg : Tendsto (fun r => hpEps (hpWeight m) (α * modCont h.symm r)) (𝓝[>] 0) (𝓝 0) := by
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      obtain ⟨s₀, hs₀ε, hs₀⟩ :=
        ((ENNReal.tendsto_nhds_zero.1 hvan.2 ε hε).and self_mem_nhdsWithin).exists
      have hlim2 : Tendsto (fun r => α * modCont h.symm r) (𝓝[>] 0) (𝓝 0) := by
        simpa using hlimC.const_mul α
      filter_upwards [hlim2.eventually (gt_mem_nhds (show (0 : ℝ) < s₀ from hs₀))] with r hr
      exact ((hp_eps_mono_le _).1 hr.le).trans hs₀ε
    have hC := ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal (hpTransferConst C₁ α A D p Ch)) hg (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at hC
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact heps r hr

/-- Remark `rem:hp-compatible`, `sec11-halfplane.tex:524–528`, **repaired** (see
`collaboration/FALSE_w6.md`, item 1): for a fixed measure with `λ ∈ CM(ℍ)`, `λ_F ∈ CM₀(ℍ)` under
`lim_{r→0} sup_{|I| ≤ r} ‖λ|_{Q_{α h⁻¹(I)}}‖_CM = 0`.  The hypothesis `λ ∈ CM(ℍ)` is not in the
paper; without it the claim fails already for `F = id`. -/
theorem rem_hp_compatible {L C₁ α : ℝ} (hwm : HPWMConstants L C₁ α) {F : ℂ → ℂ} {h : ℝ ≃ₜ ℝ}
    (hF : IsHPAdmissible F h L) (m : Measure ℂ) (hm : IsHPCarleson (hpWeight m))
    (hcond : Tendsto (fun r => ⨆ (c : ℝ) (ℓ : ℝ) (_ : 0 < ℓ) (_ : ℓ ≤ r),
      hpCMNorm ((hpWeight m).restrict (hpBox (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ))))
      (𝓝[>] 0) (𝓝 0)) :
    IsHPVanishingCarleson (hpPushWeight F m) := by
  obtain ⟨A, hA⟩ := eq_hp_maximal
  obtain ⟨D, p, Ch, hdata⟩ := eq_hp_RH hF.2.2.2.2.2.2.2.2
  obtain ⟨hloc, hcm, -⟩ := thm_hp_transfer hwm hA hF hdata m
  refine ⟨ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm) hcm, ?_⟩
  have hC := ENNReal.Tendsto.const_mul
    (a := ENNReal.ofReal (hpTransferConst C₁ α A D p Ch)) hcond (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hC
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hC (fun _ => zero_le)
    fun r => ?_
  show (⨆ (c : ℝ) (ℓ : ℝ) (_ : 0 < ℓ) (_ : ℓ ≤ r),
    hpPushWeight F m (hpBox c ℓ) / ENNReal.ofReal ℓ) ≤ _
  refine iSup₂_le fun c ℓ => iSup₂_le fun hℓ hℓr => (hloc c ℓ hℓ).1.trans ?_
  exact mul_le_mul_of_nonneg_left (le_iSup₂_of_le (f := fun (c : ℝ) (ℓ : ℝ) =>
    ⨆ (_ : 0 < ℓ) (_ : ℓ ≤ r), hpCMNorm ((hpWeight m).restrict
      (hpBox (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ)))) c ℓ
    (le_iSup₂_of_le (f := fun (_ : 0 < ℓ) (_ : ℓ ≤ r) => hpCMNorm ((hpWeight m).restrict
      (hpBox (imgCenter h.symm c ℓ) (α * imgLength h.symm c ℓ)))) hℓ hℓr le_rfl)) zero_le

/-- Helper: a box bound for a density dominated by a function of `Im z`. -/
theorem s11_sch_box_le {D : ℂ → ℝ≥0∞} {g : ℝ → ℝ≥0∞} (hg : Measurable g)
    (hD : ∀ z ∈ upperHalf, D z ≤ g z.im) (c ℓ : ℝ) :
    (volume.restrict upperHalf).withDensity D (hpBox c ℓ) ≤
      ENNReal.ofReal ℓ * ∫⁻ y in Ioc 0 ℓ, g y := by
  have hQ := hp_measurableSet_box c ℓ
  have hU : MeasurableSet upperHalf :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  set K : ℂ → ℝ≥0∞ := fun z => (Icc (c - ℓ / 2) (c + ℓ / 2)).indicator 1 z.re *
    (Ioc 0 ℓ).indicator g z.im with hKdef
  have hKm : Measurable K :=
    ((measurable_one.indicator measurableSet_Icc).comp Complex.measurable_re).mul
      ((hg.indicator measurableSet_Ioc).comp Complex.measurable_im)
  rw [withDensity_apply _ hQ, Measure.restrict_restrict hQ, ← lintegral_indicator (hQ.inter hU)]
  calc ∫⁻ z, (hpBox c ℓ ∩ upperHalf).indicator D z ≤ ∫⁻ z, K z := by
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ hpBox c ℓ ∩ upperHalf
        · rw [Set.indicator_of_mem hz]
          obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hz
          obtain ⟨h1a, h1b⟩ := abs_le.mp h1
          simp only [hKdef]
          rw [Set.indicator_of_mem (show z.re ∈ Icc (c - ℓ / 2) (c + ℓ / 2) from
            ⟨by linarith, by linarith⟩), Set.indicator_of_mem (show z.im ∈ Ioc 0 ℓ from ⟨h2, h3⟩),
            Pi.one_apply, one_mul]
          exact hD z h4
        · rw [Set.indicator_of_notMem hz]
          exact bot_le
    _ = ENNReal.ofReal ℓ * ∫⁻ y in Ioc 0 ℓ, g y := by
        rw [hp_lintegral_iter hKm]
        have hin : ∀ y : ℝ, ∫⁻ x : ℝ, K ⟨x, y⟩ = ENNReal.ofReal ℓ * (Ioc 0 ℓ).indicator g y := by
          intro y
          show ∫⁻ x : ℝ, (Icc (c - ℓ / 2) (c + ℓ / 2)).indicator 1 x *
            (Ioc 0 ℓ).indicator g y = _
          rw [lintegral_mul_const _ (measurable_one.indicator measurableSet_Icc),
            lintegral_indicator_one measurableSet_Icc, Real.volume_Icc]
          congr 2
          ring
        simp_rw [hin]
        rw [lintegral_const_mul _ (hg.indicator measurableSet_Ioc),
          lintegral_indicator measurableSet_Ioc]

/-- Helper (N0) for Theorem 11.7, (ii)⇒(iii): `y m ∈ CM₀(ℍ)` for every band measure
`m = 1_{a<y<b} dA_ρ`, `0 < a < b`: `λ(Q_I) ≤ |I| (b - a)/a`, and `λ(Q_I) = 0` when `|I| ≤ a`. -/
theorem s11_nec_band_cm0 {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IsHPVanishingCarleson (hpWeight (hpBandMeasure a b)) := by
  have hB : MeasurableSet {z : ℂ | a < z.im ∧ z.im < b} :=
    (measurableSet_lt measurable_const Complex.measurable_im).inter
      (measurableSet_lt Complex.measurable_im measurable_const)
  have hfm : Measurable fun z : ℂ => ENNReal.ofReal ((z.im ^ 2)⁻¹) := by fun_prop
  have hkm : Measurable fun z : ℂ => ENNReal.ofReal z.im := by fun_prop
  set g : ℝ → ℝ≥0∞ := (Ioo a b).indicator fun y => ENNReal.ofReal ((y ^ 2)⁻¹) * ENNReal.ofReal y
    with hg
  have hgm : Measurable g :=
    (by fun_prop : Measurable fun y : ℝ => ENNReal.ofReal ((y ^ 2)⁻¹) * ENNReal.ofReal y).indicator
      measurableSet_Ioo
  have hbox : ∀ c ℓ : ℝ, hpWeight (hpBandMeasure a b) (hpBox c ℓ) ≤
      ENNReal.ofReal ℓ * ∫⁻ y in Ioc 0 ℓ, g y := by
    intro c ℓ
    have hQ := hp_measurableSet_box c ℓ
    refine le_trans (le_of_eq ?_) (s11_sch_box_le (D := fun z => g z.im) hgm (fun z _ => le_rfl) c ℓ)
    unfold hpWeight hpBandMeasure hpArea
    rw [withDensity_apply _ hQ, withDensity_apply _ hQ, Measure.restrict_restrict hQ,
      setLIntegral_withDensity_eq_setLIntegral_mul _ hfm hkm (hQ.inter hB),
      ← lintegral_indicator (hQ.inter hB), ← lintegral_indicator hQ]
    refine lintegral_congr fun z => ?_
    simp only [Set.indicator_apply, hg, mem_inter_iff, mem_Ioo, Pi.mul_apply, mem_setOf_eq]
    by_cases h1 : z ∈ hpBox c ℓ <;> by_cases h2 : a < z.im ∧ z.im < b <;> simp_all
  have hgI : ∀ ℓ : ℝ, ∫⁻ y in Ioc 0 ℓ, g y ≤ ENNReal.ofReal a⁻¹ * ENNReal.ofReal (b - a) := by
    intro ℓ
    calc ∫⁻ y in Ioc 0 ℓ, g y ≤ ∫⁻ y, (Ioo a b).indicator (fun _ => ENNReal.ofReal a⁻¹) y := by
          refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun y => ?_)
          by_cases hy : y ∈ Ioo a b
          · rw [hg, indicator_of_mem hy, indicator_of_mem hy, ← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            have hy0 : 0 < y := ha.trans hy.1
            rw [show (y ^ 2)⁻¹ * y = y⁻¹ by field_simp]
            exact inv_anti₀ ha hy.1.le
          · rw [hg, indicator_of_notMem hy, indicator_of_notMem hy]
      _ = ENNReal.ofReal a⁻¹ * ENNReal.ofReal (b - a) := by
          rw [lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo]
  have hg0 : ∀ ℓ : ℝ, ℓ ≤ a → ∫⁻ y in Ioc 0 ℓ, g y = 0 := by
    intro ℓ hℓ
    refine le_antisymm ((setLIntegral_mono' measurableSet_Ioc fun y hy => ?_).trans
      (le_of_eq (lintegral_zero))) zero_le
    rw [hg]
    exact le_of_eq (indicator_of_notMem (fun h => by linarith [h.1, hy.2]) _)
  have hratio : ∀ c ℓ : ℝ, 0 < ℓ → hpWeight (hpBandMeasure a b) (hpBox c ℓ) / ENNReal.ofReal ℓ ≤
      ENNReal.ofReal a⁻¹ * ENNReal.ofReal (b - a) := by
    intro c ℓ _
    refine ENNReal.div_le_of_le_mul ?_
    calc hpWeight (hpBandMeasure a b) (hpBox c ℓ) ≤ ENNReal.ofReal ℓ * ∫⁻ y in Ioc 0 ℓ, g y :=
          hbox c ℓ
      _ ≤ ENNReal.ofReal ℓ * (ENNReal.ofReal a⁻¹ * ENNReal.ofReal (b - a)) := by gcongr; exact hgI ℓ
      _ = ENNReal.ofReal a⁻¹ * ENNReal.ofReal (b - a) * ENNReal.ofReal ℓ := by rw [mul_comm]
  have hzero : ∀ c ℓ : ℝ, ℓ ≤ a →
      hpWeight (hpBandMeasure a b) (hpBox c ℓ) / ENNReal.ofReal ℓ = 0 := by
    intro c ℓ hℓ
    have h0 : hpWeight (hpBandMeasure a b) (hpBox c ℓ) = 0 :=
      le_antisymm ((hbox c ℓ).trans (by rw [hg0 ℓ hℓ, mul_zero])) zero_le
    rw [h0, ENNReal.zero_div]
  refine ⟨ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (iSup_le fun c => iSup_le fun ℓ => iSup_le fun hℓ => hratio c ℓ hℓ), ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ha)] with r hr
  exact (le_antisymm (iSup_le fun c => iSup_le fun ℓ => iSup_le fun _ => iSup_le fun hℓr =>
    (hzero c ℓ (hℓr.trans (le_of_lt hr))).le) zero_le).symm

/-- Helper (N1) for Theorem 11.7, (iii)⇒(i): if `h⁻¹` is not uniformly continuous, there are
`ε > 0` and intervals `[x_n - ε/2, x_n + ε/2]` with `|h(·)| ≤ 1/(n+1)`. -/
theorem s11_nec_not_uc {h : ℝ ≃ₜ ℝ} (hmono : StrictMono h) (hnuc : ¬ UniformContinuous h.symm) :
    ∃ ε > 0, ∀ n : ℕ, ∃ x : ℝ, imgLength h x ε ≤ 1 / ((n : ℝ) + 1) := by
  rw [Metric.uniformContinuous_iff] at hnuc
  push_neg at hnuc
  obtain ⟨ε, hε, hall⟩ := hnuc
  have hsm : ∀ s t : ℝ, s ≤ t → h.symm s ≤ h.symm t := fun s t hst => by
    by_contra hc
    push_neg at hc
    have := hmono hc
    rw [h.apply_symm_apply, h.apply_symm_apply] at this
    linarith
  refine ⟨ε, hε, fun n => ?_⟩
  have key : ∀ u v : ℝ, v - u < 1 / ((n : ℝ) + 1) → ε ≤ h.symm v - h.symm u →
      ∃ x : ℝ, imgLength h x ε ≤ 1 / ((n : ℝ) + 1) := by
    intro u v hd he
    refine ⟨h.symm u + ε / 2, ?_⟩
    show h (h.symm u + ε / 2 + ε / 2) - h (h.symm u + ε / 2 - ε / 2) ≤ _
    rw [show h.symm u + ε / 2 - ε / 2 = h.symm u by ring, h.apply_symm_apply]
    have h1 := hmono.monotone (show h.symm u + ε / 2 + ε / 2 ≤ h.symm v by linarith)
    rw [h.apply_symm_apply] at h1
    linarith
  obtain ⟨u, v, huv, hε'⟩ := hall (1 / ((n : ℝ) + 1)) (by positivity)
  rw [Real.dist_eq] at huv hε'
  have huv' := abs_lt.1 huv
  rcases le_total u v with h1 | h1
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hsm u v h1))] at hε'
    exact key u v (by linarith) hε'
  · rw [abs_of_nonneg (sub_nonneg.2 (hsm v u h1))] at hε'
    exact key v u (by linarith) hε'

/-- Helper (N2) for Theorem 11.7: at `z = x + iε/2` (so `I_z = [x - ε/2, x + ε/2]`), the height
bound of Lemma 11.4 gives `Im F z ≤ (C₁/2) |h(I_z)|`. -/
theorem s11_nec_height {L C₁ α : ℝ} (hwm : HPWMConstants L C₁ α) {F : ℂ → ℂ} {h : ℝ ≃ₜ ℝ}
    (hF : IsHPAdmissible F h L) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (F (x + I * (ε / 2 : ℝ))).im ≤ C₁ / 2 * imgLength h x ε := by
  have him : ((x : ℂ) + I * ((ε / 2 : ℝ) : ℂ)).im = ε / 2 := by simp
  have hre : ((x : ℂ) + I * ((ε / 2 : ℝ) : ℂ)).re = x := by simp
  have hz : ((x : ℂ) + I * ((ε / 2 : ℝ) : ℂ)) ∈ upperHalf := by
    show 0 < ((x : ℂ) + I * ((ε / 2 : ℝ) : ℂ)).im
    rw [him]
    linarith
  have H := ((hwm.2.2 F h hF).1 _ hz).2
  rw [him, hre, show 2 * (ε / 2) = ε by ring, div_le_iff₀ (by linarith)] at H
  have e : C₁ * (imgLength h x ε / ε) * (ε / 2) = C₁ / 2 * imgLength h x ε := by
    field_simp
  linarith

/-- Helper (N3) for Theorem 11.7, (iii)⇒(i): a uniform lower bound `𝒫_{F_* m}(F(x + i y₀)) ≥ κ > 0`
for the band measure `m = 1_{y₀/2 < y < 2y₀} dA_ρ`. In place of the hyperbolic disk
`B_ρ(z, 1)` of `sec11-halfplane.tex:560` we use the Euclidean rectangle
`R = (x - y₀/4, x + y₀/4) × (3y₀/4, 5y₀/4)` inside the band: for `ζ ∈ R`,
`cosh d_ρ(z, ζ) = 1 + |z - ζ|²/(2 y₀ Im ζ) ≤ 1 + (y₀²/8)/(3y₀²/2) = 13/12` (by `hpDist`, (11.1)),
so `k_{F z}(F ζ) ≥ sech²(L arcosh(13/12)/2)` by the `L`-Lipschitz bound; and
`A_ρ(R) ≥ |R| / (5y₀/4)² = (y₀/2)²/(5y₀/4)² = 4/25` (density `1/y²` of `dA_ρ`). -/
theorem s11_nec_P_lower {F : ℂ → ℂ} {h : ℝ ≃ₜ ℝ} {L : ℝ} (hF : IsHPAdmissible F h L) {y₀ : ℝ}
    (hy₀ : 0 < y₀) :
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ ∀ x : ℝ,
      κ ≤ hpP (hpPush F (hpBandMeasure (y₀ / 2) (2 * y₀))) (F (x + I * y₀)) := by
  obtain ⟨hmaps, -, -⟩ := s11_wm_adm_basic hF
  have hlipF := hF.2.2.2.1
  have hL : 0 ≤ L := by linarith [hF.1]
  set D₀ := L * Real.arcosh (13 / 12) with hD₀
  set k₀ := ((Real.cosh (D₀ / 2))⁻¹) ^ 2 with hk₀
  have hk₀p : 0 < k₀ := by positivity
  set c₀ := ((5 / 4 * y₀) ^ 2)⁻¹ with hc₀
  refine ⟨ENNReal.ofReal k₀ * (ENNReal.ofReal c₀ * (ENNReal.ofReal (y₀ / 2) *
    ENNReal.ofReal (y₀ / 2))), ?_, fun x => ?_⟩
  · simp only [ne_eq, mul_eq_zero, ENNReal.ofReal_eq_zero, not_or, not_le]
    exact ⟨hk₀p, by positivity, by positivity, by positivity⟩
  have hU : MeasurableSet upperHalf :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  set z₀ : ℂ := (x : ℂ) + I * (y₀ : ℂ) with hz₀
  have hz₀re : z₀.re = x := by simp [hz₀]
  have hz₀im : z₀.im = y₀ := by simp [hz₀]
  have hz₀U : z₀ ∈ upperHalf := show 0 < z₀.im by rw [hz₀im]; exact hy₀
  have haU : F z₀ ∈ upperHalf := hmaps hz₀U
  set R : Set ℂ := Complex.measurableEquivRealProd ⁻¹'
    (Ioo (x - y₀ / 4) (x + y₀ / 4) ×ˢ Ioo (3 * y₀ / 4) (5 * y₀ / 4)) with hR
  have hRm : MeasurableSet R :=
    Complex.measurableEquivRealProd.measurable (measurableSet_Ioo.prod measurableSet_Ioo)
  have hRvol : volume R = ENNReal.ofReal (y₀ / 2) * ENNReal.ofReal (y₀ / 2) := by
    rw [hR, Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet, Measure.volume_eq_prod,
      Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
    congr 2 <;> ring
  have hRmem : ∀ ζ ∈ R, (x - y₀ / 4 < ζ.re ∧ ζ.re < x + y₀ / 4) ∧
      3 * y₀ / 4 < ζ.im ∧ ζ.im < 5 * y₀ / 4 := fun ζ hζ => ⟨hζ.1, hζ.2⟩
  have hRU : R ⊆ upperHalf := fun ζ hζ => show 0 < ζ.im by linarith [(hRmem ζ hζ).2.1]
  have hRB : R ⊆ {z : ℂ | y₀ / 2 < z.im ∧ z.im < 2 * y₀} := fun ζ hζ =>
    ⟨by linarith [(hRmem ζ hζ).2.1], by linarith [(hRmem ζ hζ).2.2]⟩
  have hkm : Measurable fun z => ENNReal.ofReal (hpKernel (F z₀) z) := by
    unfold hpKernel hpDist Real.arcosh
    fun_prop
  set G : ℂ → ℝ≥0∞ := upperHalf.indicator fun z => ENNReal.ofReal (hpKernel (F z₀) z) with hG
  -- the kernel on `F(R)`
  have hpt : ∀ ζ ∈ R, ENNReal.ofReal k₀ ≤ G (F ζ) := by
    intro ζ hζ
    obtain ⟨⟨h1a, h1b⟩, h2, h3⟩ := hRmem ζ hζ
    have hζU := hRU hζ
    have hy : 0 < ζ.im := hζU
    rw [hG, Set.indicator_of_mem (hmaps hζU)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hd : hpDist z₀ ζ ≤ Real.arcosh (13 / 12) := by
      unfold hpDist
      have hn : ‖z₀ - ζ‖ ^ 2 = (x - ζ.re) ^ 2 + (y₀ - ζ.im) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, hz₀re, hz₀im]
        ring
      rw [hn, hz₀im]
      refine (Real.arcosh_le_arcosh (by positivity) (by norm_num)).2 ?_
      have hq : ((x - ζ.re) ^ 2 + (y₀ - ζ.im) ^ 2) / (2 * y₀ * ζ.im) ≤ 1 / 12 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (x - ζ.re), sq_nonneg (y₀ - ζ.im)]
      linarith
    have hdF : hpDist (F z₀) (F ζ) ≤ D₀ :=
      (hlipF z₀ hz₀U ζ hζU).1.trans (mul_le_mul_of_nonneg_left hd hL)
    have hd0 : 0 ≤ hpDist (F z₀) (F ζ) := by
      unfold hpDist
      have h1 : 0 < (F z₀).im := haU
      have h2 : 0 < (F ζ).im := hmaps hζU
      exact Real.arcosh_nonneg (le_add_of_nonneg_right (div_nonneg (sq_nonneg _)
        (mul_nonneg (mul_nonneg zero_le_two h1.le) h2.le)))
    unfold hpKernel
    rw [hk₀]
    refine pow_le_pow_left₀ (by positivity) (inv_anti₀ (Real.cosh_pos _) ?_) 2
    rw [Real.cosh_le_cosh, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  -- the integral
  have hFae : AEMeasurable F ((hpBandMeasure (y₀ / 2) (2 * y₀)).restrict upperHalf) :=
    (hF.2.2.2.2.1.mono fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt hz).aemeasurable hU
  have hP : hpP (hpPush F (hpBandMeasure (y₀ / 2) (2 * y₀))) (F z₀) =
      ∫⁻ ζ, G (F ζ) ∂((hpBandMeasure (y₀ / 2) (2 * y₀)).restrict upperHalf) := by
    unfold hpP hpPush
    rw [← lintegral_indicator hU, lintegral_map' ((hkm.indicator hU).aemeasurable) hFae]
  have hmR : (hpBandMeasure (y₀ / 2) (2 * y₀)).restrict upperHalf R = hpArea R := by
    unfold hpBandMeasure
    rw [Measure.restrict_apply hRm, Measure.restrict_apply (hRm.inter hU),
      inter_eq_left.2 hRU, inter_eq_left.2 hRB]
  have hA : ENNReal.ofReal c₀ * (ENNReal.ofReal (y₀ / 2) * ENNReal.ofReal (y₀ / 2)) ≤ hpArea R := by
    unfold hpArea
    rw [withDensity_apply _ hRm, Measure.restrict_restrict hRm, inter_eq_left.2 hRU, ← hRvol,
      ← setLIntegral_const]
    refine setLIntegral_mono' hRm fun ζ hζ => ENNReal.ofReal_le_ofReal ?_
    obtain ⟨-, h2, h3⟩ := hRmem ζ hζ
    rw [hc₀]
    exact inv_anti₀ (pow_pos (by linarith) 2) (pow_le_pow_left₀ (by linarith) (by linarith) 2)
  rw [hP]
  calc ENNReal.ofReal k₀ * (ENNReal.ofReal c₀ * (ENNReal.ofReal (y₀ / 2) * ENNReal.ofReal (y₀ / 2)))
      ≤ ENNReal.ofReal k₀ * (hpBandMeasure (y₀ / 2) (2 * y₀)).restrict upperHalf R := by
        rw [hmR]
        exact mul_le_mul_of_nonneg_left hA zero_le
    _ = ∫⁻ ζ, ENNReal.ofReal k₀ ∂(((hpBandMeasure (y₀ / 2) (2 * y₀)).restrict upperHalf).restrict R) := by
        rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ∫⁻ ζ, G (F ζ) ∂(((hpBandMeasure (y₀ / 2) (2 * y₀)).restrict upperHalf).restrict R) :=
        lintegral_mono_ae ((ae_restrict_mem hRm).mono fun ζ hζ => hpt ζ hζ)
    _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl

/-- Helper (N4) for Theorem 11.7, (iii)⇒(i): `sec11-halfplane.tex:551–572`. If `h⁻¹` is not
uniformly continuous, `Im F z_n → 0` (N1, N2) while `𝒫_{F_* m}(F z_n) ≥ κ > 0` (N3), so
Lemma 11.3(c) excludes `λ_F ∈ CM₀(ℍ)` for the band measure `m`. -/
theorem s11_nec_iii_i {F : ℂ → ℂ} {h : ℝ ≃ₜ ℝ} {L : ℝ} (hF : IsHPAdmissible F h L)
    (hband : ∀ a b : ℝ, 0 < a → a < b →
      IsHPVanishingCarleson (hpPushWeight F (hpBandMeasure a b))) :
    UniformContinuous h.symm := by
  by_contra hnuc
  obtain ⟨C₁, α, hwm⟩ := lem_hp_wm L hF.1
  obtain ⟨ω, hω⟩ := hF.2.2.2.2.2.2.2.2
  obtain ⟨ε, hε, hseq⟩ := s11_nec_not_uc hω.1 hnuc
  obtain ⟨κ, hκ, hP⟩ := s11_nec_P_lower hF (y₀ := ε / 2) (by positivity)
  have hv := hband (ε / 2 / 2) (2 * (ε / 2)) (by positivity) (by linarith)
  have hT := ((lem_hp_kernel_c (hpPush F (hpBandMeasure (ε / 2 / 2) (2 * (ε / 2))))).1 hv).2
  have hge : ∀ r : ℝ, 0 < r →
      κ ≤ hpSupLow (hpP (hpPush F (hpBandMeasure (ε / 2 / 2) (2 * (ε / 2))))) r := by
    intro r hr
    obtain ⟨n, hn⟩ := exists_nat_gt (C₁ / 2 / r)
    obtain ⟨x, hx⟩ := hseq n
    have hh := s11_nec_height hwm hF x hε
    have hz : ((x : ℂ) + I * ((ε / 2 : ℝ) : ℂ)) ∈ upperHalf := by
      show 0 < ((x : ℂ) + I * ((ε / 2 : ℝ) : ℂ)).im
      simp only [add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, zero_mul, one_mul, zero_add]
      linarith
    have hmem := (s11_wm_adm_basic hF).1 hz
    have hn1 : C₁ / 2 * (1 / ((n : ℝ) + 1)) ≤ r := by
      have := (div_lt_iff₀ hr).1 hn
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      nlinarith
    have him : (F ((x : ℂ) + I * ((ε / 2 : ℝ) : ℂ))).im ≤ r :=
      hh.trans ((mul_le_mul_of_nonneg_left hx (by linarith [hwm.1])).trans hn1)
    exact (hP x).trans (le_iSup₂_of_le (f := fun (a : ℂ) (_ : a ∈ upperHalf) =>
      ⨆ (_ : a.im ≤ r), hpP (hpPush F (hpBandMeasure (ε / 2 / 2) (2 * (ε / 2)))) a) _ hmem
      (le_iSup_of_le him le_rfl))
  exact hκ (le_antisymm (ge_of_tendsto hT (eventually_nhdsWithin_of_forall hge)) zero_le)

/-- Theorem 11.7 `thm:hp-necessity`, `sec11-halfplane.tex:534`: for admissible `F`, (i) `h⁻¹`
uniformly continuous ⇔ (ii) `λ_F ∈ CM₀(ℍ)` whenever `y m ∈ CM₀(ℍ)` ⇔ (iii) `λ_F ∈ CM₀(ℍ)` for
every band measure `1_{a<y<b} dA_ρ`. -/
theorem thm_hp_necessity {F : ℂ → ℂ} {h : ℝ ≃ₜ ℝ} {L : ℝ} (hF : IsHPAdmissible F h L) :
    (UniformContinuous h.symm ↔ ∀ m : Measure ℂ,
      IsHPVanishingCarleson (hpWeight m) → IsHPVanishingCarleson (hpPushWeight F m)) ∧
    (UniformContinuous h.symm ↔ ∀ a b : ℝ, 0 < a → a < b →
      IsHPVanishingCarleson (hpPushWeight F (hpBandMeasure a b))) := by
  have hii : UniformContinuous h.symm → ∀ m : Measure ℂ,
      IsHPVanishingCarleson (hpWeight m) → IsHPVanishingCarleson (hpPushWeight F m) := by
    intro hUC m hm
    obtain ⟨C₁, α, hwm⟩ := lem_hp_wm L hF.1
    obtain ⟨A, hA⟩ := eq_hp_maximal
    obtain ⟨D, p, Ch, hdata⟩ := eq_hp_RH hF.2.2.2.2.2.2.2.2
    exact ((thm_hp_transfer hwm hA hF hdata m).2.2 hUC).2 hm
  have hband : (∀ m : Measure ℂ,
      IsHPVanishingCarleson (hpWeight m) → IsHPVanishingCarleson (hpPushWeight F m)) →
      ∀ a b : ℝ, 0 < a → a < b → IsHPVanishingCarleson (hpPushWeight F (hpBandMeasure a b)) :=
    fun H a b ha hab => H _ (s11_nec_band_cm0 ha hab)
  exact ⟨⟨hii, fun H => s11_nec_iii_i hF (hband H)⟩, ⟨fun hUC => hband (hii hUC), s11_nec_iii_i hF⟩⟩

/-! ## Two counterexamples -/

/-- The polynomial map `H(x+iy) = x + x³ + x y² + i y (1 + 3x² + y²/2)` (11.?) `eq:hp-H`. -/
def hpPolyH (z : ℂ) : ℂ :=
  ⟨z.re + z.re ^ 3 + z.re * z.im ^ 2, z.im * (1 + 3 * z.re ^ 2 + z.im ^ 2 / 2)⟩

/-- Helper: `Re H(z) = x + x³ + x y²`. -/
theorem s11_poly_re (z : ℂ) : (hpPolyH z).re = z.re + z.re ^ 3 + z.re * z.im ^ 2 := rfl

/-- Helper: `Im H(z) = y (1 + 3x² + y²/2)`. -/
theorem s11_poly_im (z : ℂ) : (hpPolyH z).im = z.im * (1 + 3 * z.re ^ 2 + z.im ^ 2 / 2) := rfl

/-- Helper: the quadratic-form inequality `⟨P (H z - H w), z - w⟩ ≥ |z - w|²/3`, `P = diag(1, 1/3)`.
It is `∫₀¹ ⟨P DH(w + t(z-w)) d, d⟩ dt` with
`⟨P DH d, d⟩ - |d|²/3 = (2/3) a² + 3(x a + y b/3)² + (y b)²/6 + (y a + x b)²`, integrated exactly. -/
theorem s11_poly_quad (z w : ℂ) :
    ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) / 3 ≤
      (hpPolyH z - hpPolyH w).re * (z.re - w.re) + (hpPolyH z - hpPolyH w).im * (z.im - w.im) / 3 := by
  have key : (hpPolyH z - hpPolyH w).re * (z.re - w.re) +
      (hpPolyH z - hpPolyH w).im * (z.im - w.im) / 3 - ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) / 3 =
      2 / 3 * (z.re - w.re) ^ 2 +
      3 * ((w.re * (z.re - w.re) + w.im * (z.im - w.im) / 3 +
          ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 / 3) / 2) ^ 2 +
        ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 / 3) ^ 2 / 12) +
      ((w.im * (z.im - w.im) + (z.im - w.im) ^ 2 / 2) ^ 2 + ((z.im - w.im) ^ 2) ^ 2 / 12) / 6 +
      ((w.im * (z.re - w.re) + w.re * (z.im - w.im) + (z.re - w.re) * (z.im - w.im)) ^ 2 +
        (2 * (z.re - w.re) * (z.im - w.im)) ^ 2 / 12) := by
    simp only [sub_re, sub_im, s11_poly_re, s11_poly_im]
    ring
  have hpos : 0 ≤ 2 / 3 * (z.re - w.re) ^ 2 +
      3 * ((w.re * (z.re - w.re) + w.im * (z.im - w.im) / 3 +
          ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 / 3) / 2) ^ 2 +
        ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 / 3) ^ 2 / 12) +
      ((w.im * (z.im - w.im) + (z.im - w.im) ^ 2 / 2) ^ 2 + ((z.im - w.im) ^ 2) ^ 2 / 12) / 6 +
      ((w.im * (z.re - w.re) + w.re * (z.im - w.im) + (z.re - w.re) * (z.im - w.im)) ^ 2 +
        (2 * (z.re - w.re) * (z.im - w.im)) ^ 2 / 12) := by positivity
  linarith

theorem s11_poly_lower_lip (z w : ℂ) : ‖z - w‖ ≤ 3 * ‖hpPolyH z - hpPolyH w‖ := by
  have hq := s11_poly_quad z w
  set p := hpPolyH z - hpPolyH w with hp
  set a := z.re - w.re with ha
  set b := z.im - w.im with hb
  have hN : ‖z - w‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im]
    ring
  have hM : ‖p‖ ^ 2 = p.re ^ 2 + p.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hN0 := norm_nonneg (z - w)
  have hM0 := norm_nonneg p
  have hcs : (p.re * a + p.im * b / 3) ^ 2 ≤ (‖p‖ * ‖z - w‖) ^ 2 := by
    rw [mul_pow, hN, hM]
    nlinarith [sq_nonneg (p.re * (b / 3) - p.im * a),
      mul_nonneg (add_nonneg (sq_nonneg p.re) (sq_nonneg p.im)) (sq_nonneg b)]
  have hX : p.re * a + p.im * b / 3 ≤ ‖p‖ * ‖z - w‖ := by
    by_contra h
    push_neg at h
    nlinarith [mul_nonneg hM0 hN0]
  have h2 : ‖z - w‖ ^ 2 ≤ 3 * (‖p‖ * ‖z - w‖) := by
    rw [hN]
    linarith
  by_contra h
  push_neg at h
  nlinarith

/-- Helper: `H` is smooth. -/
theorem s11_poly_contDiff : ContDiff ℝ ⊤ hpPolyH := by
  have hre : ContDiff ℝ ⊤ (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ ⊤ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  have h : hpPolyH = fun z => Complex.equivRealProdCLM.symm
      (z.re + z.re ^ 3 + z.re * z.im ^ 2, z.im * (1 + 3 * z.re ^ 2 + z.im ^ 2 / 2)) := by
    funext z
    apply Complex.ext <;> simp [hpPolyH]
  rw [h]
  exact Complex.equivRealProdCLM.symm.contDiff.comp
    (((hre.add (hre.pow 3)).add (hre.mul (him.pow 2))).prodMk
      (him.mul ((contDiff_const.add (contDiff_const.mul (hre.pow 2))).add ((him.pow 2).div_const 2))))

/-- Helper: `H(ℂ)` is open (inverse function theorem; the differential is injective by
`s11_poly_lower_lip`). -/
theorem s11_poly_isOpen_range : IsOpen (range hpPolyH) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, rfl⟩
  have hd : HasStrictFDerivAt hpPolyH (fderiv ℝ hpPolyH z) z :=
    s11_poly_contDiff.contDiffAt.hasStrictFDerivAt (by simp)
  have hinj : Function.Injective (fderiv ℝ hpPolyH z) := by
    rw [injective_iff_map_eq_zero]
    intro d hd0
    by_contra hne
    have h1 : HasDerivAt (fun t : ℝ => z + t • d) d 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add z
    have h2 : HasFDerivAt hpPolyH (fderiv ℝ hpPolyH z) (z + (0 : ℝ) • d) := by
      rw [zero_smul, add_zero]
      exact hd.hasFDerivAt
    have hD := h2.comp_hasDerivAt (0 : ℝ) h1
    rw [Function.comp_def, hd0] at hD
    have hT := (hD.tendsto_slope_zero).norm
    simp only [zero_add, zero_smul, add_zero, norm_zero] at hT
    have hlow : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        ‖d‖ / 3 ≤ ‖t⁻¹ • (hpPolyH (z + t • d) - hpPolyH z)‖ := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : 0 < |t| := abs_pos.mpr ht
      have hl := s11_poly_lower_lip (z + t • d) z
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at hl
      rw [norm_smul, norm_inv, Real.norm_eq_abs, le_inv_mul_iff₀ ht0]
      linarith
    have := ge_of_tendsto hT hlow
    have : 0 < ‖d‖ := norm_pos_iff.mpr hne
    linarith
  have hsurj : (fderiv ℝ hpPolyH z : ℂ →ₗ[ℝ] ℂ).range = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hinj)
  rw [← hd.map_nhds_eq_of_surj hsurj]
  exact range_mem_map

/-- Helper: `H(ℂ)` is closed (`H⁻¹` is `3`-Lipschitz on the range). -/
theorem s11_poly_isClosed_range : IsClosed (range hpPolyH) := by
  rw [← closure_subset_iff_isClosed]
  intro w hw
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hw
  choose z hz using hu
  have hc : CauchySeq z := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq (ε / 3) (by positivity)
    refine ⟨N, fun k hk l hl => ?_⟩
    have h1 := hN k hk l hl
    have h3 := s11_poly_lower_lip (z k) (z l)
    rw [hz k, hz l] at h3
    rw [dist_eq_norm] at h1 ⊢
    linarith
  obtain ⟨z₀, hz₀⟩ := cauchySeq_tendsto_of_complete hc
  have h := (s11_poly_contDiff.continuous.tendsto z₀).comp hz₀
  simp only [Function.comp_def, hz] at h
  exact ⟨z₀, tendsto_nhds_unique h hlim⟩

theorem s11_poly_homeo : ∃ G : ℂ ≃ₜ ℂ, ⇑G = hpPolyH := by
  have hinj : Function.Injective hpPolyH := fun z w h => by
    have := s11_poly_lower_lip z w
    rw [h, sub_self, norm_zero, mul_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hsurj : Function.Surjective hpPolyH := by
    have hc : IsClopen (range hpPolyH) := ⟨s11_poly_isClosed_range, s11_poly_isOpen_range⟩
    exact range_eq_univ.mp (hc.eq_univ (range_nonempty _))
  let e := Equiv.ofBijective hpPolyH ⟨hinj, hsurj⟩
  have hcont : Continuous e.symm := by
    refine (LipschitzWith.of_dist_le_mul (K := 3) fun a b => ?_).continuous
    have hl := s11_poly_lower_lip (e.symm a) (e.symm b)
    have ha : hpPolyH (e.symm a) = a := e.apply_symm_apply a
    have hb : hpPolyH (e.symm b) = b := e.apply_symm_apply b
    rw [ha, hb] at hl
    rw [dist_eq_norm, dist_eq_norm]
    push_cast
    linarith
  exact ⟨⟨e, s11_poly_contDiff.continuous, hcont⟩, rfl⟩

/-- Helper: `Im H(z) ≥ 0 ↔ Im z ≥ 0`. -/
theorem s11_poly_im_nonneg_iff (z : ℂ) : 0 ≤ (hpPolyH z).im ↔ 0 ≤ z.im := by
  rw [s11_poly_im]
  have h : 0 < 1 + 3 * z.re ^ 2 + z.im ^ 2 / 2 := by positivity
  constructor
  · intro h'
    by_contra h''
    push_neg at h''
    nlinarith
  · intro h'
    exact mul_nonneg h' h.le

theorem s11_poly_inv_spec {w : ℂ} (hw : w ∈ closedUpperHalf) :
    hpPolyH (Function.invFunOn hpPolyH closedUpperHalf w) = w ∧
      Function.invFunOn hpPolyH closedUpperHalf w ∈ closedUpperHalf := by
  obtain ⟨G, hG⟩ := s11_poly_homeo
  have hGw : hpPolyH (G.symm w) = w := by rw [← hG, G.apply_symm_apply]
  have hex : ∃ a ∈ closedUpperHalf, hpPolyH a = w :=
    ⟨G.symm w, (s11_poly_im_nonneg_iff _).mp (by rw [hGw]; exact hw), hGw⟩
  exact ⟨Function.invFunOn_eq hex, Function.invFunOn_mem hex⟩

open Classical in
theorem s11_poly_inv_measurable : Measurable (Function.invFunOn hpPolyH closedUpperHalf) := by
  obtain ⟨G, hG⟩ := s11_poly_homeo
  have hC : MeasurableSet closedUpperHalf :=
    (isClosed_le continuous_const Complex.continuous_im).measurableSet
  have heq : Function.invFunOn hpPolyH closedUpperHalf = closedUpperHalf.piecewise G.symm
      (fun _ => Function.invFunOn hpPolyH closedUpperHalf (-I)) := by
    funext w
    by_cases hw : w ∈ closedUpperHalf
    · rw [Set.piecewise_eq_of_mem _ _ _ hw]
      apply G.injective
      rw [G.apply_symm_apply, hG]
      exact (s11_poly_inv_spec hw).1
    · rw [Set.piecewise_eq_of_notMem _ _ _ hw]
      have h1 : ¬ ∃ a ∈ closedUpperHalf, hpPolyH a = w := fun ⟨a, ha, h⟩ =>
        hw (by rw [← h]; exact (s11_poly_im_nonneg_iff a).mpr ha)
      have h2 : ¬ ∃ a ∈ closedUpperHalf, hpPolyH a = -I := fun ⟨a, ha, h⟩ => by
        have := (s11_poly_im_nonneg_iff a).mpr ha
        rw [h] at this
        norm_num at this
      rw [Function.invFunOn_neg h1, Function.invFunOn_neg h2]
  rw [heq]
  exact G.symm.continuous.measurable.piecewise hC measurable_const

/-- Helper: estimates for a preimage `x + iy` of a point of
`R_n = {|Re ζ - (n + n³)| < 1/2, 5/4 < Im ζ < 7/4}`: `|x - n| ≤ n⁻²`, `n⁻²/11 ≤ y ≤ 3 n⁻²`. -/
theorem s11_poly_est {n x y : ℝ} (hn : 3 ≤ n) (hy : 0 ≤ y)
    (hre : |x + x ^ 3 + x * y ^ 2 - (n + n ^ 3)| < 1 / 2)
    (him1 : 5 / 4 < y * (1 + 3 * x ^ 2 + y ^ 2 / 2)) (him2 : y * (1 + 3 * x ^ 2 + y ^ 2 / 2) < 7 / 4) :
    |x - n| ≤ 1 / n ^ 2 ∧ 1 / n ^ 2 / 11 ≤ y ∧ y ≤ 3 * (1 / n ^ 2) := by
  have hn0 : 0 < n := by linarith
  obtain ⟨hre1, hre2⟩ := abs_lt.mp hre
  have hy2 : y < 2 := by nlinarith [mul_nonneg hy (by positivity : (0 : ℝ) ≤ 3 * x ^ 2 + y ^ 2 / 2)]
  have hn3 : 27 ≤ n ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hn 3]
  -- `x ≥ n/2`
  have hx0 : n / 2 ≤ x := by
    by_contra h
    push_neg at h
    rcases le_or_gt x 0 with hx | hx
    · nlinarith [mul_nonneg (neg_nonneg.mpr hx) (by positivity : (0 : ℝ) ≤ 1 + x ^ 2 + y ^ 2)]
    · have h3 : x ^ 3 < (n / 2) ^ 3 := pow_lt_pow_left₀ h hx.le (by norm_num)
      have h4 : x * y ^ 2 ≤ x * 4 := mul_le_mul_of_nonneg_left (by nlinarith) hx.le
      nlinarith
  have hxpos : 0 < x := by linarith
  -- `x ≤ n + 1`
  have hxu : x ≤ n + 1 := by
    by_contra h
    push_neg at h
    have h3 : (n + 1) ^ 3 < x ^ 3 := pow_lt_pow_left₀ h (by linarith) (by norm_num)
    nlinarith [mul_nonneg hxpos.le (sq_nonneg y)]
  -- `y n² ≤ 8/3`
  have hyn : y * n ^ 2 ≤ 8 / 3 := by
    have hx2 : n ^ 2 / 4 ≤ x ^ 2 := by nlinarith
    nlinarith [mul_nonneg hy (sq_nonneg y), mul_le_mul_of_nonneg_left hx2 hy]
  -- `x y² ≤ 1/2`
  have hxy : x * y ^ 2 ≤ 1 / 2 := by
    have hsq : (y * n ^ 2) ^ 2 ≤ (8 / 3) ^ 2 := pow_le_pow_left₀ (by positivity) hyn 2
    have h1 : x * (y * n ^ 2) ^ 2 ≤ (n + 1) * (8 / 3) ^ 2 :=
      mul_le_mul hxu hsq (sq_nonneg _) (by linarith)
    have hn4 : 27 * n ≤ n ^ 4 := by nlinarith
    have h4 : 0 < n ^ 4 := by positivity
    have h2 : x * y ^ 2 * n ^ 4 ≤ 1 / 2 * n ^ 4 := by nlinarith
    exact le_of_mul_le_mul_right h2 h4
  have hxy0 : 0 ≤ x * y ^ 2 := mul_nonneg hxpos.le (sq_nonneg y)
  -- `|x - n| n² ≤ 1`
  have hfac : x + x ^ 3 - (n + n ^ 3) = (x - n) * (1 + x ^ 2 + x * n + n ^ 2) := by ring
  have hF : n ^ 2 ≤ 1 + x ^ 2 + x * n + n ^ 2 := by nlinarith
  have habs : |x - n| * (1 + x ^ 2 + x * n + n ^ 2) ≤ 1 := by
    rw [← abs_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2 + x * n + n ^ 2), ← abs_mul, ← hfac]
    rw [abs_le]
    constructor <;> linarith
  have hn2 : 0 < n ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hn2]
    nlinarith [abs_nonneg (x - n)]
  · have hy1 : y ≤ 1 := by
      have : y * 9 ≤ y * n ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hy
      linarith
    have hG : 1 + 3 * x ^ 2 + y ^ 2 / 2 ≤ 27 / 2 * n ^ 2 := by nlinarith
    have h5 : 5 / 4 < y * (27 / 2 * n ^ 2) := lt_of_lt_of_le him1 (mul_le_mul_of_nonneg_left hG hy)
    rw [div_div, div_le_iff₀ (by positivity)]
    nlinarith
  · rw [mul_one_div, le_div_iff₀ hn2]
    linarith

theorem s11_poly_not_cm0 {m : Measure ℂ} {c : ℝ≥0∞} (hc : c ≠ 0) (hm : c • hpBandMeasure 1 2 ≤ m) :
    ¬ IsHPVanishingCarleson (hpPushWeight (Function.invFunOn hpPolyH closedUpperHalf) m) := by
  set F := Function.invFunOn hpPolyH closedUpperHalf with hFdef
  have hFm : Measurable F := s11_poly_inv_measurable
  have hU : MeasurableSet upperHalf :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hB : MeasurableSet {z : ℂ | 1 < z.im ∧ z.im < 2} :=
    (measurableSet_lt measurable_const Complex.measurable_im).inter
      (measurableSet_lt Complex.measurable_im measurable_const)
  set c' : ℝ≥0∞ := min c 1 with hc'
  have hc'0 : c' ≠ 0 := by simp [hc', hc]
  have hc'top : c' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  set κ : ℝ≥0∞ := c' * (ENNReal.ofReal (16 / 49) * ENNReal.ofReal (4 / 187) *
    (ENNReal.ofReal 1 * ENNReal.ofReal (1 / 2))) with hκ
  have hκ0 : κ ≠ 0 := by
    refine mul_ne_zero hc'0 ?_
    simp only [ne_eq, mul_eq_zero, ENNReal.ofReal_eq_zero, not_or, not_le]
    norm_num
  have hκtop : κ ≠ ⊤ := ENNReal.mul_ne_top hc'top (by simp [ENNReal.mul_eq_top])
  -- the lower bound `𝒫_{F_* m}(n + i n⁻²) ≥ κ`
  have hkey : ∀ n : ℕ, (3 : ℝ) ≤ n →
      κ ≤ hpP (hpPush F m) ((n : ℂ) + ((1 / (n : ℝ) ^ 2 : ℝ) : ℂ) * I) := by
    intro n hn
    have hn0 : 0 < (n : ℝ) := by linarith
    have ht : 0 < 1 / (n : ℝ) ^ 2 := by positivity
    set a : ℂ := (n : ℂ) + ((1 / (n : ℝ) ^ 2 : ℝ) : ℂ) * I with ha_def
    have hare : a.re = n := by simp only [ha_def, Complex.add_re, Complex.natCast_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.natCast_im, Complex.mul_im, zero_mul, zero_add]
    have haim : a.im = 1 / (n : ℝ) ^ 2 := by simp only [ha_def, Complex.add_re, Complex.natCast_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.natCast_im, Complex.mul_im, zero_mul, zero_add]
    have ha : a ∈ upperHalf := show 0 < a.im by rw [haim]; exact ht
    set R : Set ℂ := Complex.measurableEquivRealProd ⁻¹'
      (Ioo ((n : ℝ) + n ^ 3 - 1 / 2) ((n : ℝ) + n ^ 3 + 1 / 2) ×ˢ Ioo (5 / 4) (7 / 4)) with hR
    have hRm : MeasurableSet R :=
      Complex.measurableEquivRealProd.measurable (measurableSet_Ioo.prod measurableSet_Ioo)
    have hRvol : volume R = ENNReal.ofReal 1 * ENNReal.ofReal (1 / 2) := by
      rw [hR, Complex.volume_preserving_equiv_real_prod.measure_preimage
        (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet, Measure.volume_eq_prod,
        Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
      congr 2 <;> ring
    have hRmem : ∀ ζ ∈ R, ((n : ℝ) + n ^ 3 - 1 / 2 < ζ.re ∧ ζ.re < (n : ℝ) + n ^ 3 + 1 / 2) ∧
        5 / 4 < ζ.im ∧ ζ.im < 7 / 4 := fun ζ hζ => ⟨hζ.1, hζ.2⟩
    have hRU : R ⊆ upperHalf := fun ζ hζ => show 0 < ζ.im by linarith [(hRmem ζ hζ).2.1]
    have hRB : R ⊆ {z : ℂ | 1 < z.im ∧ z.im < 2} := fun ζ hζ =>
      ⟨by linarith [(hRmem ζ hζ).2.1], by linarith [(hRmem ζ hζ).2.2]⟩
    have hkm : Measurable fun z => ENNReal.ofReal (hpKernel a z) := by
      unfold hpKernel hpDist Real.arcosh; fun_prop
    set G : ℂ → ℝ≥0∞ := upperHalf.indicator fun z => ENNReal.ofReal (hpKernel a z) with hG
    -- pointwise: `k_a(F ζ) ≥ 4/187` on `R`
    have hpt : ∀ ζ ∈ R, ENNReal.ofReal (4 / 187) ≤ G (F ζ) := by
      intro ζ hζ
      obtain ⟨⟨h1a, h1b⟩, h2, h3⟩ := hRmem ζ hζ
      have hζ' : ζ ∈ closedUpperHalf := show 0 ≤ ζ.im by linarith
      obtain ⟨hHF, hFmem⟩ := s11_poly_inv_spec hζ'
      rw [← hFdef] at hHF hFmem
      have hre : (hpPolyH (F ζ)).re = ζ.re := by rw [hHF]
      have him : (hpPolyH (F ζ)).im = ζ.im := by rw [hHF]
      rw [s11_poly_re] at hre
      rw [s11_poly_im] at him
      obtain ⟨hx, hy1, hy2⟩ := s11_poly_est (x := (F ζ).re) (y := (F ζ).im) hn hFmem
        (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩) (by linarith) (by linarith)
      have hy : 0 < (F ζ).im := lt_of_lt_of_le (by positivity) hy1
      have hp : F ζ ∈ upperHalf := hy
      rw [hG, Set.indicator_of_mem hp, hpKernel_eq ha hp]
      apply ENNReal.ofReal_le_ofReal
      have hnorm : ‖F ζ - conj a‖ ^ 2 = ((F ζ).re - n) ^ 2 + ((F ζ).im + 1 / (n : ℝ) ^ 2) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, Complex.conj_re,
          Complex.conj_im, hare, haim]
        ring
      have hxn : ((F ζ).re - n) ^ 2 ≤ (1 / (n : ℝ) ^ 2) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hx 2
      have hyt : ((F ζ).im + 1 / (n : ℝ) ^ 2) ^ 2 ≤ (4 * (1 / (n : ℝ) ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      have hty : 1 / (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ 2 / 11) ≤ 1 / (n : ℝ) ^ 2 * (F ζ).im :=
        mul_le_mul_of_nonneg_left hy1 ht.le
      rw [hnorm, haim, le_div_iff₀ (by positivity)]
      nlinarith
    -- the integral
    have hP : hpP (hpPush F m) a = ∫⁻ ζ, G (F ζ) ∂(m.restrict upperHalf) := by
      unfold hpP hpPush
      rw [← lintegral_indicator hU, lintegral_map (hkm.indicator hU) hFm]
    have hcm : c' • hpBandMeasure 1 2 ≤ c • hpBandMeasure 1 2 := Measure.le_iff'.mpr fun s => by
      simp only [Measure.smul_apply, smul_eq_mul]
      gcongr
      exact min_le_left c 1
    have hle1 : ∫⁻ ζ, G (F ζ) ∂((c' • hpBandMeasure 1 2).restrict upperHalf) ≤
        ∫⁻ ζ, G (F ζ) ∂(m.restrict upperHalf) :=
      lintegral_mono' (Measure.restrict_mono subset_rfl
        (hcm.trans hm)) le_rfl
    have hle2 : ∫⁻ ζ, G (F ζ) ∂((hpBandMeasure 1 2).restrict R) ≤
        ∫⁻ ζ, G (F ζ) ∂((hpBandMeasure 1 2).restrict upperHalf) :=
      lintegral_mono' (Measure.restrict_mono_set _ hRU) le_rfl
    have hbandR : (hpBandMeasure 1 2).restrict R = hpArea.restrict R := by
      unfold hpBandMeasure
      rw [Measure.restrict_restrict hRm, inter_eq_left.mpr hRB]
    have hle3 : ENNReal.ofReal (16 / 49) * ENNReal.ofReal (4 / 187) * volume R ≤
        ∫⁻ ζ, G (F ζ) ∂(hpArea.restrict R) := by
      rw [hp_lintegral_hpArea_restrict hRm, ← lintegral_indicator_const hRm]
      refine lintegral_mono fun ζ => ?_
      by_cases hζ : ζ ∈ R
      · rw [Set.indicator_of_mem hζ, Set.indicator_of_mem (show ζ ∈ R ∩ upperHalf from ⟨hζ, hRU hζ⟩)]
        have hh := (hRmem ζ hζ).2
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) (hpt ζ hζ)
        rw [le_inv_comm₀ (by norm_num) (by nlinarith)]
        nlinarith
      · rw [Set.indicator_of_notMem hζ]
        exact bot_le
    calc κ = c' * (ENNReal.ofReal (16 / 49) * ENNReal.ofReal (4 / 187) * volume R) := by
          rw [hκ, hRvol]
      _ ≤ c' * ∫⁻ ζ, G (F ζ) ∂(hpArea.restrict R) := by gcongr
      _ = ∫⁻ ζ, G (F ζ) ∂((c' • hpBandMeasure 1 2).restrict R) := by
          rw [Measure.restrict_smul, lintegral_smul_measure, hbandR]
          try rfl
      _ ≤ ∫⁻ ζ, G (F ζ) ∂((c' • hpBandMeasure 1 2).restrict upperHalf) :=
          lintegral_mono' (Measure.restrict_mono_set _ hRU) le_rfl
      _ ≤ _ := hle1
      _ = _ := hP.symm
  unfold hpPushWeight
  rw [lem_hp_kernel_c]
  rintro ⟨-, hT⟩
  rw [ENNReal.tendsto_nhds_zero] at hT
  obtain ⟨r, hr, hr0⟩ := ((hT (κ / 2) (ENNReal.half_pos hκ0)).and self_mem_nhdsWithin).exists
  have hr0' : 0 < r := hr0
  obtain ⟨n, hn⟩ := exists_nat_ge (max 3 (1 / r))
  have hn3 : (3 : ℝ) ≤ n := le_trans (le_max_left _ _) hn
  have hnr : 1 / r ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : 0 < (n : ℝ) := by linarith
  set a : ℂ := (n : ℂ) + ((1 / (n : ℝ) ^ 2 : ℝ) : ℂ) * I with ha_def
  have haim : a.im = 1 / (n : ℝ) ^ 2 := by simp only [ha_def, Complex.add_re, Complex.natCast_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.natCast_im, Complex.mul_im, zero_mul, zero_add]
  have ha : a ∈ upperHalf := show 0 < a.im by rw [haim]; positivity
  have har : a.im ≤ r := by
    rw [haim, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hr0'] at hnr
    nlinarith
  have h1 : κ ≤ hpSupLow (hpP (hpPush F m)) r :=
    (hkey n hn3).trans (le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le har le_rfl)))
  exact absurd (h1.trans hr) (not_le.mpr (ENNReal.half_lt_self hκ0 hκtop))


/-- Helper: `Im H(z) > 0 ↔ Im z > 0`. -/
theorem s11_ex_im_pos_iff (z : ℂ) : 0 < (hpPolyH z).im ↔ 0 < z.im := by
  rw [s11_poly_im]
  have h : 0 < 1 + 3 * z.re ^ 2 + z.im ^ 2 / 2 := by positivity
  exact ⟨fun h' => pos_of_mul_pos_left h' h.le, fun h' => mul_pos h' h⟩

/-- Helper: `H` is a bijection of `ℍ` and of `ℍ ∪ ℝ`, continuous and proper there. -/
theorem s11_ex_bij :
    BijOn hpPolyH upperHalf upperHalf ∧ BijOn hpPolyH closedUpperHalf closedUpperHalf ∧
      ContinuousOn hpPolyH closedUpperHalf ∧
      Tendsto hpPolyH (cocompact ℂ ⊓ 𝓟 closedUpperHalf) (cocompact ℂ) := by
  obtain ⟨G, hG⟩ := s11_poly_homeo
  have hGs : ∀ w, hpPolyH (G.symm w) = w := fun w => by rw [← hG, G.apply_symm_apply]
  have key : ∀ {S : Set ℂ}, (∀ z, hpPolyH z ∈ S ↔ z ∈ S) → BijOn hpPolyH S S := by
    intro S hS
    refine ⟨fun z hz => (hS z).mpr hz, ?_, fun w hw => ⟨G.symm w, (hS _).mp (by rw [hGs]; exact hw),
      hGs w⟩⟩
    rw [← hG]
    exact G.injective.injOn
  refine ⟨key fun z => s11_ex_im_pos_iff z, key fun z => s11_poly_im_nonneg_iff z, ?_, ?_⟩
  · rw [← hG]
    exact G.continuous.continuousOn
  · rw [← hG]
    exact G.isClosedEmbedding.tendsto_cocompact.mono_left inf_le_left

/-- Helper: the differential of `H`, `DH = [[1+3x²+y², 2xy], [6xy, 1+3x²+3y²/2]]`. -/
theorem s11_ex_fderiv (z v : ℂ) : fderiv ℝ hpPolyH z v =
    ⟨(1 + 3 * z.re ^ 2 + z.im ^ 2) * v.re + 2 * z.re * z.im * v.im,
      6 * z.re * z.im * v.re + (1 + 3 * z.re ^ 2 + 3 / 2 * z.im ^ 2) * v.im⟩ := by
  have hd : HasFDerivAt hpPolyH (fderiv ℝ hpPolyH z) z :=
    ((s11_poly_contDiff.differentiable (by simp)) z).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => z + t • v) ((1 : ℝ) • v) 0 :=
    ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h1 := hd.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hl (by simp)
  have hx : HasDerivAt (fun t : ℝ => z.re + t * v.re) v.re 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v.re).const_add z.re
  have hy : HasDerivAt (fun t : ℝ => z.im + t * v.im) v.im 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v.im).const_add z.im
  have hP : HasDerivAt (fun t : ℝ => (z.re + t * v.re) + (z.re + t * v.re) ^ 3 +
      (z.re + t * v.re) * (z.im + t * v.im) ^ 2)
      ((1 + 3 * z.re ^ 2 + z.im ^ 2) * v.re + 2 * z.re * z.im * v.im) 0 := by
    have := (hx.add (hx.pow 3)).add (hx.mul (hy.pow 2))
    convert this using 1
    norm_num
    ring
  have hQ : HasDerivAt (fun t : ℝ => (z.im + t * v.im) *
      (1 + 3 * (z.re + t * v.re) ^ 2 + (z.im + t * v.im) ^ 2 / 2))
      (6 * z.re * z.im * v.re + (1 + 3 * z.re ^ 2 + 3 / 2 * z.im ^ 2) * v.im) 0 := by
    have := hy.mul ((((hx.pow 2).const_mul 3).const_add 1).add ((hy.pow 2).div_const 2))
    convert this using 1
    norm_num <;> ring
  have h2 : HasDerivAt (fun t : ℝ => hpPolyH (z + t • v))
      ((Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)
        ((1 + 3 * z.re ^ 2 + z.im ^ 2) * v.re + 2 * z.re * z.im * v.im,
          6 * z.re * z.im * v.re + (1 + 3 * z.re ^ 2 + 3 / 2 * z.im ^ 2) * v.im)) 0 := by
    have := Complex.equivRealProdCLM.symm.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hP.prodMk hQ)
    convert this using 1
    funext t
    apply Complex.ext <;> simp [hpPolyH]
  rw [one_smul] at h1
  rw [h1.unique h2]
  apply Complex.ext <;> simp

/-- Helper: `det DH = (1+3x²+y²)(1+3x²+3y²/2) - 12x²y²`. -/
theorem s11_ex_det (z : ℂ) : LinearMap.det (fderiv ℝ hpPolyH z : ℂ →ₗ[ℝ] ℂ) =
    (1 + 3 * z.re ^ 2 + z.im ^ 2) * (1 + 3 * z.re ^ 2 + 3 / 2 * z.im ^ 2) -
      2 * z.re * z.im * (6 * z.re * z.im) := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, s11_ex_fderiv]

/-- Helper: `det DH ≥ A²/2`, `A = 1 + x² + y²` (`eq:hp-det`). -/
theorem s11_ex_det_ge (z : ℂ) : (1 + z.re ^ 2 + z.im ^ 2) ^ 2 / 2 ≤
    (1 + 3 * z.re ^ 2 + z.im ^ 2) * (1 + 3 * z.re ^ 2 + 3 / 2 * z.im ^ 2) -
      2 * z.re * z.im * (6 * z.re * z.im) := by
  nlinarith [sq_nonneg (z.im ^ 2 - 11 / 4 * z.re ^ 2), sq_nonneg z.re, sq_nonneg z.im,
    sq_nonneg (z.re ^ 2)]

/-- Helper: the Frobenius bound `|DH|² ≤ 28 A²`. -/
theorem s11_ex_frob (z : ℂ) : (1 + 3 * z.re ^ 2 + z.im ^ 2) ^ 2 + (2 * z.re * z.im) ^ 2 +
    (6 * z.re * z.im) ^ 2 + (1 + 3 * z.re ^ 2 + 3 / 2 * z.im ^ 2) ^ 2 ≤
      28 * (1 + z.re ^ 2 + z.im ^ 2) ^ 2 := by
  have hA : 0 ≤ 1 + z.re ^ 2 + z.im ^ 2 := by positivity
  have ha0 : 0 ≤ 1 + 3 * z.re ^ 2 + z.im ^ 2 := by positivity
  have hd0 : 0 ≤ 1 + 3 * z.re ^ 2 + 3 / 2 * z.im ^ 2 := by positivity
  have ha : 1 + 3 * z.re ^ 2 + z.im ^ 2 ≤ 3 * (1 + z.re ^ 2 + z.im ^ 2) := by nlinarith [sq_nonneg z.im]
  have hd : 1 + 3 * z.re ^ 2 + 3 / 2 * z.im ^ 2 ≤ 3 * (1 + z.re ^ 2 + z.im ^ 2) := by
    nlinarith [sq_nonneg z.im]
  nlinarith [mul_le_mul ha ha ha0 (by positivity), mul_le_mul hd hd hd0 (by positivity),
    sq_nonneg (z.re ^ 2 - z.im ^ 2), sq_nonneg z.re, sq_nonneg z.im, mul_nonneg (sq_nonneg z.re) (sq_nonneg z.im)]

/-- Helper: singular-value bounds for a `2 × 2` matrix with `|M|² ≤ 28 A²`, `det M ≥ A²/2`:
`|Mv|² ≤ 36 A²|v|²` and `A²|v|² ≤ 144 |Mv|²` (adjugate and Cauchy–Schwarz). -/
theorem s11_ex_mat_bounds {a b c d A : ℝ} (hA : 0 < A) (hF : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≤ 28 * A ^ 2)
    (hdet : A ^ 2 / 2 ≤ a * d - b * c) (v1 v2 : ℝ) :
    (a * v1 + b * v2) * (a * v1 + b * v2) + (c * v1 + d * v2) * (c * v1 + d * v2) ≤
        36 * A ^ 2 * (v1 * v1 + v2 * v2) ∧
      A ^ 2 * (v1 * v1 + v2 * v2) ≤
        144 * ((a * v1 + b * v2) * (a * v1 + b * v2) + (c * v1 + d * v2) * (c * v1 + d * v2)) := by
  set P := (a * v1 + b * v2) * (a * v1 + b * v2) + (c * v1 + d * v2) * (c * v1 + d * v2) with hP
  set V := v1 * v1 + v2 * v2 with hV
  have hV0 : 0 ≤ V := by nlinarith [mul_self_nonneg v1, mul_self_nonneg v2]
  have hP0 : 0 ≤ P := by nlinarith [mul_self_nonneg (a * v1 + b * v2), mul_self_nonneg (c * v1 + d * v2)]
  have hCS : P ≤ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * V := by
    nlinarith [sq_nonneg (a * v2 - b * v1), sq_nonneg (c * v2 - d * v1)]
  have hadj : (a * d - b * c) ^ 2 * V ≤ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * P := by
    nlinarith [sq_nonneg (b * (a * v1 + b * v2) + d * (c * v1 + d * v2)),
      sq_nonneg (a * (a * v1 + b * v2) + c * (c * v1 + d * v2))]
  have hd2 : (A ^ 2 / 2) ^ 2 ≤ (a * d - b * c) ^ 2 := pow_le_pow_left₀ (by positivity) hdet 2
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hF hV0, mul_nonneg (sq_nonneg A) hV0]
  · have h3 : A ^ 2 * (A ^ 2 * V) ≤ A ^ 2 * (112 * P) := by
      nlinarith [mul_le_mul_of_nonneg_right hd2 hV0, mul_le_mul_of_nonneg_right hF hP0]
    have h4 := le_of_mul_le_mul_left h3 (by positivity)
    linarith

/-- Helper: `|DH v|² ≤ 36 A² |v|²` and `A² |v|² ≤ 144 |DH v|²`. -/
theorem s11_ex_sq_bounds (z v : ℂ) :
    ‖fderiv ℝ hpPolyH z v‖ ^ 2 ≤ 36 * (1 + z.re ^ 2 + z.im ^ 2) ^ 2 * ‖v‖ ^ 2 ∧
      (1 + z.re ^ 2 + z.im ^ 2) ^ 2 * ‖v‖ ^ 2 ≤ 144 * ‖fderiv ℝ hpPolyH z v‖ ^ 2 := by
  have hA : 0 < 1 + z.re ^ 2 + z.im ^ 2 := by positivity
  have h := s11_ex_mat_bounds hA (s11_ex_frob z) (s11_ex_det_ge z) v.re v.im
  rw [s11_ex_fderiv, Complex.sq_norm, Complex.sq_norm, Complex.normSq_mk, Complex.normSq_apply]
  exact h

/-- Helper: the hyperbolic expansion of `H` lies in `[1/36, 12]`. -/
theorem s11_ex_hyp {z : ℂ} (hz : 0 < z.im) (v : ℂ) :
    ‖fderiv ℝ hpPolyH z v‖ / (hpPolyH z).im ≤ 12 * (‖v‖ / z.im) ∧
      ‖v‖ / z.im ≤ 36 * (‖fderiv ℝ hpPolyH z v‖ / (hpPolyH z).im) := by
  set A := 1 + z.re ^ 2 + z.im ^ 2 with hA
  set m := 1 + 3 * z.re ^ 2 + z.im ^ 2 / 2 with hm
  have hA0 : 0 < A := by positivity
  have hm1 : A / 2 ≤ m := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  have hm2 : m ≤ 3 * A := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  have hm0 : 0 < m := by linarith
  have hIm : (hpPolyH z).im = z.im * m := s11_poly_im z
  obtain ⟨h1, h2⟩ := s11_ex_sq_bounds z v
  have hn := norm_nonneg (fderiv ℝ hpPolyH z v)
  have hv := norm_nonneg v
  have hu : ‖fderiv ℝ hpPolyH z v‖ ≤ 6 * A * ‖v‖ :=
    (pow_le_pow_iff_left₀ hn (by positivity) two_ne_zero).mp (by nlinarith)
  have hl : A * ‖v‖ ≤ 12 * ‖fderiv ℝ hpPolyH z v‖ :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp (by nlinarith)
  rw [hIm]
  constructor
  · rw [div_le_iff₀ (by positivity), show 12 * (‖v‖ / z.im) * (z.im * m) = 12 * ‖v‖ * m by
      field_simp]
    nlinarith [mul_le_mul_of_nonneg_left hm1 hv]
  · rw [div_le_iff₀ hz, show 36 * (‖fderiv ℝ hpPolyH z v‖ / (z.im * m)) * z.im =
      36 * ‖fderiv ℝ hpPolyH z v‖ / m by field_simp, le_div_iff₀ hm0]
    nlinarith [mul_le_mul_of_nonneg_left hm2 hv]

/-- Helper: `(1 + q/p)/(1 - q/p) ≤ 72` when `(p+q)² ≤ 56(p² - q²)`. -/
theorem s11_ex_dil {P Q : ℝ} (hQ : 0 ≤ Q) (hQP : Q < P) (h : (P + Q) ^ 2 ≤ 56 * (P ^ 2 - Q ^ 2)) :
    (1 + Q / P) / (1 - Q / P) ≤ 72 := by
  have hP : 0 < P := by linarith
  have e1 : 1 + Q / P = (P + Q) / P := by field_simp
  have e2 : 1 - Q / P = (P - Q) / P := by field_simp
  rw [e1, e2, div_div_div_cancel_right₀ hP.ne', div_le_iff₀ (sub_pos.mpr hQP)]
  have h1 : (P + Q) * (P + Q) ≤ (P + Q) * (56 * (P - Q)) := by nlinarith
  have h2 := le_of_mul_le_mul_left h1 (by linarith)
  linarith

/-- Helper: `∂H = ((a+d) + i(c-b))/2`, `∂̄H = ((a-d) + i(c+b))/2` for `DH = [[a, b], [c, d]]`. -/
theorem s11_ex_dz (z : ℂ) :
    dz hpPolyH z = ⟨((1 + 3 * z.re ^ 2 + z.im ^ 2) + (1 + 3 * z.re ^ 2 + 3 / 2 * z.im ^ 2)) / 2,
        (6 * z.re * z.im - 2 * z.re * z.im) / 2⟩ ∧
      dzbar hpPolyH z = ⟨((1 + 3 * z.re ^ 2 + z.im ^ 2) - (1 + 3 * z.re ^ 2 + 3 / 2 * z.im ^ 2)) / 2,
        (6 * z.re * z.im + 2 * z.re * z.im) / 2⟩ := by
  constructor <;> apply Complex.ext <;> simp [dz, dzbar, s11_ex_fderiv] <;> ring

/-- Helper: the pointwise dilatation bound `|∂̄H| < |∂H|`, `D_H ≤ 72`. -/
theorem s11_ex_dil_pt (z : ℂ) :
    ‖dzbar hpPolyH z‖ < ‖dz hpPolyH z‖ ∧ dilatationQuotient hpPolyH z ≤ 72 := by
  obtain ⟨hdz, hdzb⟩ := s11_ex_dz z
  have hdet := s11_ex_det_ge z
  have hF := s11_ex_frob z
  generalize ha : 1 + 3 * z.re ^ 2 + z.im ^ 2 = a at hdz hdzb hdet hF
  generalize hb : 2 * z.re * z.im = b at hdz hdzb hdet hF
  generalize hc : 6 * z.re * z.im = c at hdz hdzb hdet hF
  generalize hd : 1 + 3 * z.re ^ 2 + 3 / 2 * z.im ^ 2 = d at hdz hdzb hdet hF
  have hA0 : 0 < (1 + z.re ^ 2 + z.im ^ 2) ^ 2 / 2 := by positivity
  generalize (1 + z.re ^ 2 + z.im ^ 2) = A at hdet hF hA0
  have hP2 : ‖dz hpPolyH z‖ ^ 2 = ((a + d) / 2) * ((a + d) / 2) + ((c - b) / 2) * ((c - b) / 2) := by
    rw [hdz, Complex.sq_norm, Complex.normSq_mk]
  have hQ2 : ‖dzbar hpPolyH z‖ ^ 2 =
      ((a - d) / 2) * ((a - d) / 2) + ((c + b) / 2) * ((c + b) / 2) := by
    rw [hdzb, Complex.sq_norm, Complex.normSq_mk]
  have hP0 := norm_nonneg (dz hpPolyH z)
  have hQ0 := norm_nonneg (dzbar hpPolyH z)
  unfold dilatationQuotient complexDilatation
  rw [norm_div]
  generalize ‖dz hpPolyH z‖ = P at hP2 hP0 ⊢
  generalize ‖dzbar hpPolyH z‖ = Q at hQ2 hQ0 ⊢
  have hdiff : P ^ 2 - Q ^ 2 = a * d - b * c := by rw [hP2, hQ2]; ring
  have hsum : 2 * (P ^ 2 + Q ^ 2) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by rw [hP2, hQ2]; ring
  have hpos : 0 < a * d - b * c := by linarith
  have hlt : Q < P := by
    by_contra hle
    push_neg at hle
    nlinarith [mul_le_mul hle hle hP0 hQ0]
  refine ⟨hlt, s11_ex_dil hQ0 hlt ?_⟩
  nlinarith [sq_nonneg (P - Q)]

/-- Helper: `H` is `C¹`-quasiconformal on `ℍ` with `K = 72` (in fact `D_H ≤ 56`). -/
theorem s11_ex_c1qc : IsC1Quasiconformal hpPolyH upperHalf 72 := by
  obtain ⟨G, hG⟩ := s11_poly_homeo
  have hho : IsHomeomorphOnto hpPolyH upperHalf (hpPolyH '' upperHalf) := by
    rw [← hG]
    exact s11_pow_homeoOnto G.continuous G.symm.continuous (fun z => G.symm_apply_apply z) _
  exact ⟨isOpen_upperHalf, by norm_num, (s11_poly_contDiff.of_le le_top).contDiffOn, hho,
    fun z _ => s11_ex_dil_pt z⟩

/-- Helper: `H` is `72`-quasiconformal on `ℍ`. -/
theorem s11_ex_qc : IsKQC hpPolyH upperHalf 72 := isKQC_of_isC1Quasiconformal s11_ex_c1qc

/-- Helper: `F = H⁻¹` (inverse on `ℍ ∪ ℝ`) is `72`-quasiconformal on `ℍ`. -/
theorem s11_ex_inv_qc : IsKQC (Function.invFunOn hpPolyH closedUpperHalf) upperHalf 72 := by
  obtain ⟨hB, -, -, -⟩ := s11_ex_bij
  have h := thm7_2_inv s11_ex_qc
  rw [hB.image_eq] at h
  refine ad_isKQC_congr h fun w hw => ?_
  obtain ⟨G, hG⟩ := s11_poly_homeo
  have hinj : Function.Injective hpPolyH := by rw [← hG]; exact G.injective
  have h1 := (s11_poly_inv_spec (show (0 : ℝ) ≤ w.im from le_of_lt (show (0 : ℝ) < w.im from hw))).1
  have h2 : hpPolyH (Function.invFunOn hpPolyH upperHalf w) = w :=
    Function.invFunOn_eq (hB.surjOn hw)
  exact hinj (h1.trans h2.symm)

/-- Helper: `d_ρ` is the Mathlib distance of `UpperHalfPlane`. -/
theorem s11_ex_dist {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    hpDist z w = dist (UpperHalfPlane.mk z hz) (UpperHalfPlane.mk w hw) := by
  rw [UpperHalfPlane.dist_eq]
  obtain ⟨h0, hs⟩ := s07_hpDist_sinh_sq hz hw
  have hr : dist ((UpperHalfPlane.mk z hz : UpperHalfPlane) : ℂ) (UpperHalfPlane.mk w hw) =
      ‖z - w‖ := by rw [Complex.dist_eq]
  have hi1 : (UpperHalfPlane.mk z hz).im = z.im := rfl
  have hi2 : (UpperHalfPlane.mk w hw).im = w.im := rfl
  rw [hr, hi1, hi2]
  have hs0 : 0 ≤ ‖z - w‖ / (2 * √(z.im * w.im)) := by positivity
  have hsq : (‖z - w‖ / (2 * √(z.im * w.im))) ^ 2 = ‖z - w‖ ^ 2 / (2 * z.im * w.im) / 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have hsh : 0 ≤ Real.sinh (hpDist z w / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
  have heq : Real.sinh (hpDist z w / 2) = ‖z - w‖ / (2 * √(z.im * w.im)) :=
    (pow_left_inj₀ hsh hs0 two_ne_zero).mp (hs.trans hsq.symm)
  rw [← heq, Real.arsinh_sinh]
  ring


/-- Helper: `H` multiplies hyperbolic lengths of Lipschitz curves by at most `12` and at least
`1/36` (`s11_ex_hyp` at every point where the curve is differentiable, i.e. a.e. by Rademacher). -/
theorem s11_ex_len {γ : ℝ → ℂ} (hγ : ∃ K : ℝ≥0, LipschitzOnWith K γ (Icc 0 1))
    (him : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (γ t).im) :
    hypLength (hpPolyH ∘ γ) ≤ ENNReal.ofReal 12 * hypLength γ ∧
      hypLength γ ≤ ENNReal.ofReal 36 * hypLength (hpPolyH ∘ γ) := by
  obtain ⟨K, hK⟩ := hγ
  have hae : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      t ∈ Ioo (0 : ℝ) 1 ∧ DifferentiableAt ℝ γ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae hK.ae_differentiableWithinAt_of_mem_real] with t ht h2
    exact ⟨ht, (h2 (Ioo_subset_Icc_self ht)).differentiableAt (Icc_mem_nhds ht.1 ht.2)⟩
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ γ t →
      ‖deriv (hpPolyH ∘ γ) t‖ₑ / ENNReal.ofReal ((hpPolyH ∘ γ) t).im ≤
          ENNReal.ofReal 12 * (‖deriv γ t‖ₑ / ENNReal.ofReal (γ t).im) ∧
        ‖deriv γ t‖ₑ / ENNReal.ofReal (γ t).im ≤
          ENNReal.ofReal 36 * (‖deriv (hpPolyH ∘ γ) t‖ₑ / ENNReal.ofReal ((hpPolyH ∘ γ) t).im) := by
    intro t ht hd
    have hy : 0 < (γ t).im := him t (Ioo_subset_Icc_self ht)
    have hHy : 0 < (hpPolyH (γ t)).im := (s11_ex_im_pos_iff _).mpr hy
    have hHd : DifferentiableAt ℝ hpPolyH (γ t) := (s11_poly_contDiff.differentiable (by simp)) _
    rw [fderiv_comp_deriv t hHd hd, Function.comp_apply]
    obtain ⟨h1, h2⟩ := s11_ex_hyp hy (deriv γ t)
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_div_of_pos hHy,
      ← ENNReal.ofReal_div_of_pos hy, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 36)]
    exact ⟨ENNReal.ofReal_le_ofReal h1, ENNReal.ofReal_le_ofReal h2⟩
  unfold hypLength
  constructor
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with t ht
    exact (hpt t ht.1 ht.2).1
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with t ht
    exact (hpt t ht.1 ht.2).2

/-- Helper: `H` is `12`-Lipschitz and `H⁻¹` is `36`-Lipschitz for `d_ρ` (geodesics of `S30`). -/
theorem s11_ex_dist_lip {z z' : ℂ} (hz : z ∈ upperHalf) (hz' : z' ∈ upperHalf) :
    hpDist (hpPolyH z) (hpPolyH z') ≤ 12 * hpDist z z' ∧
      hpDist z z' ≤ 36 * hpDist (hpPolyH z) (hpPolyH z') := by
  have hy : 0 < z.im := hz
  have hy' : 0 < z'.im := hz'
  have hHy := (s11_ex_im_pos_iff z).mpr hy
  have hHy' := (s11_ex_im_pos_iff z').mpr hy'
  have hd0 := (s07_hpDist_sinh_sq hy hy').1
  have hHd0 := (s07_hpDist_sinh_sq hHy hHy').1
  constructor
  · obtain ⟨c, ⟨K, hK⟩, hcim, hc0, hc1, hcl⟩ :=
      s30a_geodesic (UpperHalfPlane.mk z hy) (UpperHalfPlane.mk z' hy')
    obtain ⟨R, hR⟩ :=
      (isCompact_Icc.image_of_continuousOn hK.continuousOn).isBounded.subset_closedBall 0
    obtain ⟨K', hK'⟩ := (s11_poly_contDiff.contDiffOn (s := closedBall 0 R)).exists_lipschitzOnWith
      (by simp) (convex_closedBall 0 R) (isCompact_closedBall 0 R)
    have hHc : ∃ K : ℝ≥0, LipschitzOnWith K (hpPolyH ∘ c) (Icc 0 1) :=
      ⟨K' * K, hK'.comp hK fun t ht => hR (mem_image_of_mem c ht)⟩
    have hHim : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ((hpPolyH ∘ c) t).im := fun t ht =>
      (s11_ex_im_pos_iff _).mpr (hcim t ht)
    have h1 := s30a_dist_le_hypLength (hpPolyH ∘ c) hHc hHim
    have h2 := (s11_ex_len ⟨K, hK⟩ hcim).1
    rw [hcl, ← s11_ex_dist hy hy'] at h2
    rw [← s11_ex_dist] at h1
    simp only [Function.comp_apply, hc0, hc1, UpperHalfPlane.coe_mk] at h1
    have h3 := h1.trans h2
    rwa [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
  · obtain ⟨G, hG⟩ := s11_poly_homeo
    obtain ⟨c, ⟨K, hK⟩, hcim, hc0, hc1, hcl⟩ :=
      s30a_geodesic (UpperHalfPlane.mk (hpPolyH z) hHy) (UpperHalfPlane.mk (hpPolyH z') hHy')
    have hGl : LipschitzWith 3 G.symm := LipschitzWith.of_dist_le_mul fun u v => by
      have := s11_poly_lower_lip (G.symm u) (G.symm v)
      rw [← hG, G.apply_symm_apply, G.apply_symm_apply] at this
      rw [dist_eq_norm, dist_eq_norm]
      exact_mod_cast this
    have hHγ : ∀ t, hpPolyH ((G.symm ∘ c) t) = c t := fun t => by
      rw [← hG, Function.comp_apply, G.apply_symm_apply]
    have hHγ' : hpPolyH ∘ (G.symm ∘ c) = c := funext hHγ
    have hγim : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ((G.symm ∘ c) t).im := fun t ht =>
      (s11_ex_im_pos_iff _).mp (by rw [hHγ]; exact hcim t ht)
    have hγL : ∃ K : ℝ≥0, LipschitzOnWith K (G.symm ∘ c) (Icc 0 1) :=
      ⟨3 * K, hGl.comp_lipschitzOnWith hK⟩
    have h1 := s30a_dist_le_hypLength (G.symm ∘ c) hγL hγim
    have h2 := (s11_ex_len hγL hγim).2
    rw [hHγ', hcl, ← s11_ex_dist hHy hHy'] at h2
    rw [← s11_ex_dist] at h1
    have hz0 : (G.symm ∘ c) 0 = z := by
      rw [Function.comp_apply, hc0, UpperHalfPlane.coe_mk, ← hG, G.symm_apply_apply]
    have hz1 : (G.symm ∘ c) 1 = z' := by
      rw [Function.comp_apply, hc1, UpperHalfPlane.coe_mk, ← hG, G.symm_apply_apply]
    rw [hz0, hz1] at h1
    have h3 := h1.trans h2
    rwa [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 36),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3

/-- Helper: `h(x) = x + x³` is strictly increasing. -/
theorem s11_ex_h_mono : StrictMono fun x : ℝ => x + x ^ 3 := fun x y hxy => by
  nlinarith [mul_pos (sub_pos.mpr hxy)
    (by positivity : (0 : ℝ) < 1 + (x + y) ^ 2 / 2 + x ^ 2 / 2 + y ^ 2 / 2)]

/-- Helper: `h(x) = x + x³` is a homeomorphism of `ℝ`. -/
theorem s11_ex_h_exists : ∃ h : ℝ ≃ₜ ℝ, ∀ x, h x = x + x ^ 3 := by
  have hc : Continuous fun x : ℝ => x + x ^ 3 := by fun_prop
  have hs : Function.Surjective fun x : ℝ => x + x ^ 3 := by
    refine hc.surjective ?_ ?_
    · exact tendsto_atTop_mono' atTop ((eventually_ge_atTop 0).mono fun x hx => by
        show x ≤ x + x ^ 3
        nlinarith [pow_nonneg hx 3]) tendsto_id
    · exact tendsto_atBot_mono' atBot ((eventually_le_atBot 0).mono fun x hx => by
        show x + x ^ 3 ≤ x
        nlinarith [mul_nonneg (neg_nonneg.mpr hx) (sq_nonneg x)]) tendsto_id
  exact ⟨(s11_ex_h_mono.orderIsoOfSurjective _ hs).toHomeomorph, fun x => rfl⟩

/-- Helper: `h ∈ SQS(ℝ)` with density `h′ = 1 + 3x²` (`A_∞` with `C = 6`, `δ = 1`). -/
theorem s11_ex_h_sqs {h : ℝ ≃ₜ ℝ} (hh : ∀ x, h x = x + x ^ 3) :
    IsSQSWith h fun x => 1 + 3 * x ^ 2 := by
  have hf : (⇑h) = fun x => x + x ^ 3 := funext hh
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => x + x ^ 3) (1 + 3 * x ^ 2) x := fun x => by
    have := (hasDerivAt_id x).add (hasDerivAt_pow 3 x)
    convert this using 1
    all_goals first | rfl | norm_num
  have hcont : Continuous fun x : ℝ => 1 + 3 * x ^ 2 := by fun_prop
  have hint : ∀ a b : ℝ, ∫ x in a..b, (1 + 3 * x ^ 2) = (b + b ^ 3) - (a + a ^ 3) := fun a b =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hcont.intervalIntegrable a b)
  have hsurj := h.surjective
  rw [hf] at hsurj ⊢
  refine ⟨s11_ex_h_mono, by fun_prop, hsurj,
    ⟨fun x => by positivity, hcont.locallyIntegrable, 6, 1, by norm_num, one_pos, ?_⟩, fun x => ?_⟩
  · intro a b hab E hE hEm
    have hIcc : ∫ x in Icc a b, (1 + 3 * x ^ 2) = (b - a) * (1 + a ^ 2 + a * b + b ^ 2) := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le, hint]
      ring
    have hbd : ∀ x ∈ E, 1 + 3 * x ^ 2 ≤ 1 + 3 * (a ^ 2 + b ^ 2) := fun x hx => by
      obtain ⟨h1, h2⟩ := hE hx
      rcases le_total 0 x with h0 | h0
      · nlinarith [pow_le_pow_left₀ h0 h2 2, sq_nonneg a]
      · nlinarith [pow_le_pow_left₀ (neg_nonneg.mpr h0) (neg_le_neg h1) 2, sq_nonneg b]
    have hV0 : 0 ≤ (volume E).toReal := ENNReal.toReal_nonneg
    have hba : 0 < b - a := sub_pos.mpr hab
    calc ∫ x in E, (1 + 3 * x ^ 2) ≤ ∫ x in E, (1 + 3 * (a ^ 2 + b ^ 2)) :=
          setIntegral_mono_on (hcont.integrableOn_Icc.mono_set hE)
            (continuous_const.integrableOn_Icc.mono_set hE) hEm hbd
      _ = (volume E).toReal * (1 + 3 * (a ^ 2 + b ^ 2)) := by
          rw [setIntegral_const, smul_eq_mul]
          rfl
      _ ≤ 6 * ((volume E).toReal / (b - a)) ^ (1 : ℝ) * ∫ x in Icc a b, (1 + 3 * x ^ 2) := by
          rw [Real.rpow_one, hIcc, show 6 * ((volume E).toReal / (b - a)) *
            ((b - a) * (1 + a ^ 2 + a * b + b ^ 2)) = 6 * (volume E).toReal *
              (1 + a ^ 2 + a * b + b ^ 2) * ((b - a) / (b - a)) by ring, div_self hba.ne', mul_one]
          nlinarith [mul_nonneg hV0 (sq_nonneg (a + b))]
  · beta_reduce
    rw [hint]
    ring

/-- Helper: `x ↦ log (1 + 3x²)` is `2`-Lipschitz. -/
theorem s11_ex_log_lip : LipschitzWith 2 fun x : ℝ => Real.log (1 + 3 * x ^ 2) := by
  have hpos : ∀ x : ℝ, 0 < 1 + 3 * x ^ 2 := fun x => by positivity
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Real.log (1 + 3 * x ^ 2))
      (6 * x / (1 + 3 * x ^ 2)) x := fun x => by
    have h1 : HasDerivAt (fun x : ℝ => 1 + 3 * x ^ 2) (6 * x) x := by
      have := ((hasDerivAt_pow 2 x).const_mul 3).const_add 1
      convert this using 1
      norm_num <;> ring
    exact h1.log (hpos x).ne'
  refine lipschitzWith_of_nnnorm_deriv_le (fun x => (hd x).differentiableAt) fun x => ?_
  rw [(hd x).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_div,
    abs_of_pos (hpos x), div_le_iff₀ (hpos x)]
  have : |6 * x| ≤ 2 * (1 + 3 * x ^ 2) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (x - 1 / 2)]
  exact_mod_cast this

/-- Helper: `h ∈ SS(ℝ)`. -/
theorem s11_ex_h_ss {h : ℝ ≃ₜ ℝ} (hh : ∀ x, h x = x + x ^ 3) : IsSS h :=
  hp_ss_of_lipschitz (s11_ex_h_sqs hh) s11_ex_log_lip

/-- Helper: `h⁻¹ ∈ SQS(ℝ)` with density `(h′ ∘ h⁻¹)⁻¹` (`s11_symm_ainfty`, `s11_symm_formula`). -/
theorem s11_ex_hsymm_sqs {h : ℝ ≃ₜ ℝ} (hh : ∀ x, h x = x + x ^ 3) :
    IsSQSWith h.symm fun y => (1 + 3 * (h.symm y) ^ 2)⁻¹ := by
  have hω := s11_ex_h_sqs hh
  have hm : Measurable fun x : ℝ => 1 + 3 * x ^ 2 := by fun_prop
  have hpos : ∀ᵐ x : ℝ, 0 < 1 + 3 * x ^ 2 := ae_of_all _ fun x => by positivity
  exact ⟨fun x y hxy => hω.1.lt_iff_lt.mp (by rw [h.apply_symm_apply, h.apply_symm_apply]; exact hxy),
    h.symm.continuous, h.symm.surjective, s11_symm_ainfty hω hm hpos, s11_symm_formula hω hm hpos⟩

/-- Helper: `h⁻¹` is `1`-Lipschitz (`h′ ≥ 1`). -/
theorem s11_ex_hsymm_lip {h : ℝ ≃ₜ ℝ} (hh : ∀ x, h x = x + x ^ 3) : LipschitzWith 1 h.symm :=
  LipschitzWith.of_dist_le_mul fun u v => by
    rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq]
    have hu : h (h.symm u) = u := h.apply_symm_apply u
    have hv : h (h.symm v) = v := h.apply_symm_apply v
    rw [hh] at hu hv
    generalize h.symm u = x at hu ⊢
    generalize h.symm v = y at hv ⊢
    have hq1 : 1 ≤ 1 + x ^ 2 + x * y + y ^ 2 := by
      nlinarith [sq_nonneg (x + y), sq_nonneg x, sq_nonneg y]
    have hq : 0 < 1 + x ^ 2 + x * y + y ^ 2 := by linarith
    rw [← hu, ← hv, show x + x ^ 3 - (y + y ^ 3) = (x - y) * (1 + x ^ 2 + x * y + y ^ 2) by ring,
      abs_mul, abs_of_pos hq]
    exact le_mul_of_one_le_right (abs_nonneg _) hq1

/-- Helper: `h⁻¹ ∈ SS(ℝ)` (`log (h⁻¹)′ = -log (1 + 3 (h⁻¹)²)` is `2`-Lipschitz). -/
theorem s11_ex_hsymm_ss {h : ℝ ≃ₜ ℝ} (hh : ∀ x, h x = x + x ^ 3) : IsSS h.symm := by
  refine hp_ss_of_lipschitz (s11_ex_hsymm_sqs hh) (c := 2) (LipschitzWith.of_dist_le_mul fun u v => ?_)
  have h2 := (s11_ex_log_lip.comp (s11_ex_hsymm_lip hh)).dist_le_mul u v
  simp only [Function.comp_apply, mul_one] at h2
  rw [Real.log_inv, Real.log_inv, dist_neg_neg]
  exact h2

/-- Helper: `h` is not uniformly continuous (`h(x + δ/2) - h(x) ≥ 3x²δ/2 ≥ 1` for `x = 1/δ + 1`). -/
theorem s11_ex_not_uc {h : ℝ ≃ₜ ℝ} (hh : ∀ x, h x = x + x ^ 3) : ¬ UniformContinuous h := by
  rw [Metric.uniformContinuous_iff]
  intro H
  obtain ⟨δ, hδ, hδ'⟩ := H 1 one_pos
  have hx1 : 1 ≤ 1 / δ + 1 := by have := one_div_pos.mpr hδ; linarith
  have hxδ : (1 / δ + 1) * δ = 1 + δ := by field_simp
  have hd : dist (1 / δ + 1 + δ / 2) (1 / δ + 1) < δ := by
    rw [Real.dist_eq, show 1 / δ + 1 + δ / 2 - (1 / δ + 1) = δ / 2 by ring,
      abs_of_pos (by positivity)]
    linarith
  have h1 := hδ' hd
  rw [Real.dist_eq, hh, hh, abs_lt] at h1
  generalize 1 / δ + 1 = x at hx1 hxδ h1
  have h3 : 1 ≤ x * (x * δ) := by nlinarith
  have ht := half_pos hδ
  nlinarith [mul_pos (mul_pos (by linarith : (0 : ℝ) < x) ht) ht, pow_pos ht 3]

/-- Helper: `y m ∈ CM₀(ℍ)` for the band measure `m = 1_{1<y<2} dA_ρ` (boxes of size `≤ 1` miss it). -/
theorem s11_ex_band_cm0 : IsHPVanishingCarleson (hpWeight (hpBandMeasure 1 2)) :=
  s11_nec_band_cm0 one_pos one_lt_two

/-- Example 11.8 `ex:hp-polynomial`, `sec11-halfplane.tex:580`: `H` is a diffeomorphism of `ℍ`
extending to a homeomorphism of `ℍ ∪ ℝ ∪ {∞}` with `H|_ℝ = h`, `h(x) = x + x³`; `H` is
`12`-Lipschitz and `H⁻¹` is `36`-Lipschitz for `d_ρ`; both are `72`-quasiconformal; `h, h⁻¹` are
strongly symmetric, `h` is not uniformly continuous; `F = H⁻¹` is admissible with constant `36` and
boundary map `h⁻¹`; and for `m = 1_{1<y<2} dA_ρ`, `y m ∈ CM₀(ℍ)` but `λ_F ∉ CM₀(ℍ)`. -/
theorem ex_hp_polynomial :
    BijOn hpPolyH upperHalf upperHalf ∧ ContDiff ℝ ⊤ hpPolyH ∧
      (∀ z ∈ upperHalf, 0 < LinearMap.det (fderiv ℝ hpPolyH z : ℂ →ₗ[ℝ] ℂ)) ∧
      ContinuousOn hpPolyH closedUpperHalf ∧ BijOn hpPolyH closedUpperHalf closedUpperHalf ∧
      Tendsto hpPolyH (cocompact ℂ ⊓ 𝓟 closedUpperHalf) (cocompact ℂ) ∧
      (∀ z ∈ upperHalf, ∀ z' ∈ upperHalf,
        hpDist (hpPolyH z) (hpPolyH z') ≤ 12 * hpDist z z' ∧
          hpDist z z' ≤ 36 * hpDist (hpPolyH z) (hpPolyH z')) ∧
      IsKQC hpPolyH upperHalf 72 ∧
      IsKQC (Function.invFunOn hpPolyH closedUpperHalf) upperHalf 72 ∧
      ∃ h : ℝ ≃ₜ ℝ, (∀ x, h x = x + x ^ 3) ∧ (∀ x : ℝ, hpPolyH (x : ℂ) = ((h x : ℝ) : ℂ)) ∧
        IsSS h ∧ IsSS h.symm ∧ ¬ UniformContinuous h ∧
        IsHPAdmissible (Function.invFunOn hpPolyH closedUpperHalf) h.symm 36 ∧
        IsHPVanishingCarleson (hpWeight (hpBandMeasure 1 2)) ∧
        ¬ IsHPVanishingCarleson
          (hpPushWeight (Function.invFunOn hpPolyH closedUpperHalf) (hpBandMeasure 1 2)) := by
  -- `H` is a homeomorphism of `ℂ` preserving `ℍ` and `ℝ` (`s11_poly_homeo`); metric bounds by
  -- hyperbolic length (`s11_ex_len`), QC by `D_H ≤ 56`; boundary map `h(x) = x + x³`
  obtain ⟨hBU, hBC, hcont, htend⟩ := s11_ex_bij
  obtain ⟨h, hh⟩ := s11_ex_h_exists
  have hsub : upperHalf ⊆ closedUpperHalf := fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt hz
  have hinv := hBC.invOn_invFunOn
  have hFU := (s11_adm_inv_upper hBC hBU.image_eq).2
  have hFc := s11_adm_inv_cont hcont hBC htend
  have hHx : ∀ x : ℝ, hpPolyH (x : ℂ) = ((h x : ℝ) : ℂ) := fun x => by
    rw [hh]
    apply Complex.ext <;> simp [hpPolyH, ← Complex.ofReal_pow]
  refine ⟨hBU, s11_poly_contDiff, fun z _ => ?_, hcont, hBC, htend,
    fun z hz z' hz' => s11_ex_dist_lip hz hz', s11_ex_qc, s11_ex_inv_qc, h, hh, hHx, s11_ex_h_ss hh,
    s11_ex_hsymm_ss hh, s11_ex_not_uc hh, ⟨by norm_num, ⟨72, s11_ex_inv_qc⟩, hFU, ?_, hFc.1,
      hinv.symm.bijOn hBC.surjOn.mapsTo_invFunOn hBC.mapsTo, hFc.2, ?_, ⟨_, s11_ex_hsymm_sqs hh⟩⟩,
    s11_ex_band_cm0, s11_poly_not_cm0 one_ne_zero (one_smul ℝ≥0∞ _).le⟩
  · rw [s11_ex_det]
    have := s11_ex_det_ge z
    have : 0 < (1 + z.re ^ 2 + z.im ^ 2) ^ 2 / 2 := by positivity
    linarith
  · intro z hz z' hz'
    have hw : Function.invFunOn hpPolyH closedUpperHalf z ∈ upperHalf := hFU ▸ mem_image_of_mem _ hz
    have hw' : Function.invFunOn hpPolyH closedUpperHalf z' ∈ upperHalf :=
      hFU ▸ mem_image_of_mem _ hz'
    obtain ⟨h1, h2⟩ := s11_ex_dist_lip hw hw'
    rw [hinv.2 (hsub hz), hinv.2 (hsub hz')] at h1 h2
    have h0 := (s07_hpDist_sinh_sq (show 0 < (Function.invFunOn hpPolyH closedUpperHalf z).im from hw)
      (show 0 < (Function.invFunOn hpPolyH closedUpperHalf z').im from hw')).1
    exact ⟨h2, by linarith⟩
  · intro x
    have hx : ((h.symm x : ℝ) : ℂ) ∈ closedUpperHalf := by
      show (0 : ℝ) ≤ ((h.symm x : ℝ) : ℂ).im
      simp
    have hFx : hpPolyH ((h.symm x : ℝ) : ℂ) = (x : ℂ) := by
      rw [hHx, h.apply_symm_apply]
    rw [← hFx, hinv.1 hx]

/-- (11.?) `eq:hp-Sf`, `sec11-halfplane.tex:708`: for `f(z) = z + τ e^{iz}`,
`S f(z) = -iτ e^{iz}(1 - (i/2) τ e^{iz})/(1 + iτ e^{iz})²` on `ℍ` (`0 < τ ≤ 1/4`). -/
theorem eq_hp_Sf {τ : ℝ} (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4) {z : ℂ} (hz : z ∈ upperHalf) :
    schwarzian (fun w => w + τ * exp (I * w)) z =
      -I * τ * exp (I * z) * (1 - I / 2 * τ * exp (I * z)) / (1 + I * τ * exp (I * z)) ^ 2 := by
  have hE : ∀ w : ℂ, HasDerivAt (fun w => exp (I * w)) (I * exp (I * w)) w := fun w => by
    simpa [mul_comm] using ((hasDerivAt_id w).const_mul I).cexp
  have hd1 : deriv (fun w => w + τ * exp (I * w)) = fun w => 1 + I * τ * exp (I * w) := by
    funext w
    have h : HasDerivAt (fun w => w + τ * exp (I * w)) (1 + τ * (I * exp (I * w))) w :=
      (hasDerivAt_id' w).add ((hE w).const_mul (τ : ℂ))
    rw [h.deriv]
    ring
  have hd2 : deriv (deriv (fun w => w + τ * exp (I * w))) = fun w => -τ * exp (I * w) := by
    rw [hd1]
    funext w
    rw [(((hE w).const_mul (I * τ)).const_add 1).deriv]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hy : 0 < z.im := hz
  have hne : ∀ w : ℂ, 0 < w.im → 1 + I * τ * exp (I * w) ≠ 0 := by
    intro w hw h
    have h' : I * τ * exp (I * w) = -1 := by linear_combination h
    have h1 : ‖I * τ * exp (I * w)‖ = ‖(-1 : ℂ)‖ := by rw [h']
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_exp] at h1
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
      norm_neg, norm_one, Real.norm_eq_abs, abs_of_pos hτ] at h1
    have : Real.exp (-w.im) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    nlinarith [Real.exp_pos (-w.im)]
  rw [schwarzian_of_analyticAt ((by fun_prop :
    Differentiable ℂ fun w : ℂ => w + τ * exp (I * w)).analyticAt z)]
  unfold schwarzianHol
  rw [hd2, hd1]
  have hnum : HasDerivAt (fun w => -(τ : ℂ) * exp (I * w)) (-τ * (I * exp (I * z))) z :=
    (hE z).const_mul _
  have hden : HasDerivAt (fun w => 1 + I * τ * exp (I * w)) (I * τ * (I * exp (I * z))) z :=
    ((hE z).const_mul (I * τ)).const_add 1
  have hq : HasDerivAt (fun w => -(τ : ℂ) * exp (I * w) / (1 + I * τ * exp (I * w))) _ z :=
    hnum.div hden (hne z hy)
  beta_reduce
  rw [hq.deriv]
  have h0 := hne z hy
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Helper: `exp` is `1`-Lipschitz on `(-∞, 0]`. -/
theorem s11_sch_exp_lip {u v : ℝ} (hu : u ≤ 0) (hv : v ≤ 0) :
    |Real.exp u - Real.exp v| ≤ |u - v| := by
  wlog h : v ≤ u generalizing u v
  · rw [abs_sub_comm, abs_sub_comm u]
    exact this hv hu (le_of_not_ge h)
  have h1 : Real.exp v = Real.exp u * Real.exp (v - u) := by rw [← Real.exp_add]; ring_nf
  have h2 := Real.add_one_le_exp (v - u)
  have h3 : Real.exp u ≤ 1 := Real.exp_le_one_iff.mpr hu
  have h4 := Real.exp_pos u
  have h5 : Real.exp (v - u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h6 : 1 - Real.exp (v - u) ≤ u - v := by linarith
  have h7 : 0 ≤ 1 - Real.exp (v - u) := by linarith
  rw [h1, abs_of_nonneg (by nlinarith [mul_nonneg h4.le h7]), abs_of_nonneg (by linarith)]
  nlinarith [mul_le_mul h3 h6 h7 zero_le_one]

theorem s11_sch_phi_lip {τ : ℝ} (hτ : 0 ≤ τ) (z w : ℂ) :
    ‖(τ : ℂ) * exp (I * z.re) * (Real.exp (-|z.im|) : ℂ) -
        (τ : ℂ) * exp (I * w.re) * (Real.exp (-|w.im|) : ℂ)‖ ≤ 2 * τ * ‖z - w‖ := by
  have he : exp (I * z.re) = exp (I * w.re) * exp (I * ((z.re - w.re : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    push_cast
    ring_nf
  have hsplit : (τ : ℂ) * exp (I * z.re) * (Real.exp (-|z.im|) : ℂ) -
      (τ : ℂ) * exp (I * w.re) * (Real.exp (-|w.im|) : ℂ) =
      (τ : ℂ) * (exp (I * w.re) * ((exp (I * ((z.re - w.re : ℝ) : ℂ)) - 1) *
        (Real.exp (-|z.im|) : ℂ) + ((Real.exp (-|z.im|) - Real.exp (-|w.im|) : ℝ) : ℂ))) := by
    rw [he]
    push_cast
    ring
  have hu : ‖exp (I * (w.re : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hA : ‖exp (I * ((z.re - w.re : ℝ) : ℂ)) - 1‖ ≤ |z.re - w.re| := by
    simpa [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := z.re - w.re)
  have hE : ‖((Real.exp (-|z.im|) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))
  have hD : ‖(((Real.exp (-|z.im|) - Real.exp (-|w.im|)) : ℝ) : ℂ)‖ ≤ |z.im - w.im| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine (s11_sch_exp_lip (neg_nonpos.mpr (abs_nonneg _)) (neg_nonpos.mpr (abs_nonneg _))).trans ?_
    rw [show -|z.im| - -|w.im| = |w.im| - |z.im| by ring, abs_sub_comm z.im]
    exact abs_abs_sub_abs_le_abs_sub _ _
  have hre : |z.re - w.re| ≤ ‖z - w‖ := by simpa using Complex.abs_re_le_norm (z - w)
  have him : |z.im - w.im| ≤ ‖z - w‖ := by simpa using Complex.abs_im_le_norm (z - w)
  have hX : ‖(exp (I * ((z.re - w.re : ℝ) : ℂ)) - 1) * (Real.exp (-|z.im|) : ℂ) +
      ((Real.exp (-|z.im|) - Real.exp (-|w.im|) : ℝ) : ℂ)‖ ≤ 2 * ‖z - w‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have := mul_le_mul hA hE (norm_nonneg _) (abs_nonneg _)
    linarith
  rw [hsplit, norm_mul, norm_mul, hu, one_mul, Complex.norm_real, Real.norm_of_nonneg hτ]
  nlinarith

theorem s11_sch_homeo {τ : ℝ} (hτ : 0 ≤ τ) (hτ' : τ < 1 / 2) :
    ∃ T : ℂ ≃ₜ ℂ, ∀ z, T z = z + (τ : ℂ) * exp (I * z.re) * (Real.exp (-|z.im|) : ℂ) := by
  set f : ℂ → ℂ := fun z => z + (τ : ℂ) * exp (I * z.re) * (Real.exp (-|z.im|) : ℂ) with hf
  have hA : ApproximatesLinearOn f ((ContinuousLinearEquiv.refl ℝ ℂ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) univ
      (Real.toNNReal (2 * τ)) := by
    intro x _ y _
    have h := s11_sch_phi_lip hτ x y
    simp only [hf, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_refl', id]
    rw [Real.coe_toNNReal _ (by linarith)]
    calc ‖x + (τ : ℂ) * exp (I * x.re) * (Real.exp (-|x.im|) : ℂ) -
          (y + (τ : ℂ) * exp (I * y.re) * (Real.exp (-|y.im|) : ℂ)) - (x - y)‖
        = ‖(τ : ℂ) * exp (I * x.re) * (Real.exp (-|x.im|) : ℂ) -
          (τ : ℂ) * exp (I * y.re) * (Real.exp (-|y.im|) : ℂ)‖ := by congr 1; ring
      _ ≤ 2 * τ * ‖x - y‖ := h
  have hc : Subsingleton ℂ ∨ Real.toNNReal (2 * τ) <
      ‖((ContinuousLinearEquiv.refl ℝ ℂ).symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
    right
    have h1 : ‖((ContinuousLinearEquiv.refl ℝ ℂ).symm : ℂ →L[ℝ] ℂ)‖₊ = 1 := by
      rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl]
      exact ContinuousLinearMap.nnnorm_id
    rw [h1, inv_one, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ (by linarith), NNReal.coe_one]
    linarith
  exact ⟨hA.toHomeomorph f hc, fun z => rfl⟩

theorem s11_sch_upper_eq (τ : ℝ) :
    EqOn (fun z => z + (τ : ℂ) * exp (I * z.re) * (Real.exp (-|z.im|) : ℂ))
      (fun z => z + τ * exp (I * z)) upperHalf := by
  intro z hz
  have hy : 0 < z.im := hz
  simp only
  rw [abs_of_pos hy, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
  congr 3
  apply Complex.ext <;> simp

/-- Helper: on `𝕃`, the extension is `z + τ e^{i z̄}`. -/
theorem s11_sch_lower_eq (τ : ℝ) :
    EqOn (fun z => z + (τ : ℂ) * exp (I * z.re) * (Real.exp (-|z.im|) : ℂ))
      (fun z => z + τ * exp (I * conj z)) lowerHalf := by
  intro z hz
  have hy : z.im < 0 := hz
  simp only
  rw [abs_of_neg hy, neg_neg, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
  congr 3
  apply Complex.ext <;> simp

theorem s11_sch_lower_qc {τ : ℝ} (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4) :
    IsC1Quasiconformal (fun z => z + (τ : ℂ) * exp (I * z.re) * (Real.exp (-|z.im|) : ℂ)) lowerHalf
      ((1 + τ) / (1 - τ)) := by
  obtain ⟨T, hT⟩ := s11_sch_homeo hτ.le (by linarith)
  have hTf : (⇑T) = fun z => z + (τ : ℂ) * exp (I * z.re) * (Real.exp (-|z.im|) : ℂ) := funext hT
  rw [← hTf]
  have hLo : IsOpen lowerHalf := isOpen_lt Complex.continuous_im continuous_const
  have h1τ : 0 < 1 - τ := by linarith
  have hK : 1 ≤ (1 + τ) / (1 - τ) := (le_div_iff₀ h1τ).mpr (by linarith)
  set F : ℂ → ℂ := fun u => u + τ * exp (I * conj u) with hF
  have hTF : EqOn T F lowerHalf := by
    intro z hz
    rw [hTf]
    exact s11_sch_lower_eq τ hz
  have hFc : ContDiff ℝ 1 F :=
    contDiff_id.add (contDiff_const.mul (Complex.contDiff_exp.comp
      (contDiff_const.mul Complex.conjCLE.contDiff)))
  have hl : Function.LeftInverse T.symm T := T.symm_apply_apply
  refine ⟨hLo, hK, hFc.contDiffOn.congr hTF,
    s11_pow_homeoOnto T.continuous T.symm.continuous hl _, fun z hz => ?_⟩
  have hy : z.im < 0 := hz
  set e : ℂ := exp (I * conj z) with he
  have hc : HasFDerivAt (fun u : ℂ => I * conj u) (I • Complex.conjCLE.toContinuousLinearMap) z :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.const_mul I
  have hFd : HasFDerivAt F (ContinuousLinearMap.id ℝ ℂ +
      (τ : ℂ) • (e • (I • Complex.conjCLE.toContinuousLinearMap))) z :=
    (hasFDerivAt_id z).add (hc.cexp.const_mul (τ : ℂ))
  have hTz : fderiv ℝ T z = fderiv ℝ F z :=
    (show (⇑T) =ᶠ[𝓝 z] F from Filter.eventually_of_mem (hLo.mem_nhds hz) hTF).fderiv_eq
  have hv : ∀ v : ℂ, fderiv ℝ T z v = v + τ * e * (I * conj v) := by
    intro v
    rw [hTz, hFd.fderiv]
    simp [smul_eq_mul]
    ring
  have hdz : dz T z = 1 := by
    unfold dz
    rw [hv, hv]
    simp only [map_one, Complex.conj_I]
    linear_combination ((-1 + (τ : ℂ) * e * I) / 2) * Complex.I_sq
  have hdzbar : dzbar T z = I * τ * e := by
    unfold dzbar
    rw [hv, hv]
    simp only [map_one, Complex.conj_I]
    linear_combination ((1 - (τ : ℂ) * e * I) / 2) * Complex.I_sq
  have hne : ‖e‖ = Real.exp z.im := by
    rw [he, Complex.norm_exp]
    simp
  have hq : Real.exp z.im < 1 := Real.exp_lt_one_iff.mpr hy
  have hq0 := Real.exp_pos z.im
  have hndzbar : ‖dzbar T z‖ = τ * Real.exp z.im := by
    rw [hdzbar, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg hτ.le, hne]
  have hμ : ‖complexDilatation T z‖ = τ * Real.exp z.im := by
    unfold complexDilatation
    rw [norm_div, hndzbar, hdz, norm_one, div_one]
  refine ⟨?_, ?_⟩
  · rw [hdz, norm_one, hndzbar]
    nlinarith
  · unfold dilatationQuotient
    rw [hμ, div_le_div_iff₀ (by nlinarith) h1τ]
    nlinarith

theorem s11_sch_Sf_bound {τ : ℝ} (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4) {z : ℂ} (hz : z ∈ upperHalf) :
    ‖schwarzian (fun w => w + τ * exp (I * w)) z‖ ≤ 2 * τ * Real.exp (-z.im) ∧
      (1 < z.im → z.im < 2 →
        τ * Real.exp (-2) / 2 ≤ ‖schwarzian (fun w => w + τ * exp (I * w)) z‖) := by
  have hy : 0 < z.im := hz
  rw [eq_hp_Sf hτ hτ' hz]
  set e : ℂ := exp (I * z) with he
  set q : ℝ := Real.exp (-z.im) with hq
  have hne : ‖e‖ = q := by
    rw [he, Complex.norm_exp]
    simp [hq]
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hq0 : 0 < q := Real.exp_pos _
  have hτq : τ * q ≤ 1 / 4 := by nlinarith
  have hw : ‖I * τ * e‖ = τ * q := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hτ.le,
      hne]
  have hw2 : ‖I / 2 * τ * e‖ = τ * q / 2 := by
    rw [norm_mul, norm_mul, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hτ.le,
      hne]
    norm_num
    ring
  have hnum : ‖-I * τ * e‖ = τ * q := by
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg hτ.le, hne]
  have hN1 : ‖1 - I / 2 * τ * e‖ ≤ 1 + τ * q / 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, hw2]
  have hN2 : 1 - τ * q / 2 ≤ ‖1 - I / 2 * τ * e‖ := by
    have := norm_sub_norm_le (1 : ℂ) (I / 2 * τ * e)
    rw [norm_one, hw2] at this
    linarith
  have hD1 : 1 - τ * q ≤ ‖1 + I * τ * e‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(I * τ * e))
    rw [norm_one, norm_neg, hw, sub_neg_eq_add] at this
    linarith
  have hD2 : ‖1 + I * τ * e‖ ≤ 1 + τ * q := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, hw]
  have hD0 : 0 < ‖1 + I * τ * e‖ := by linarith
  rw [norm_div, norm_mul, norm_pow, hnum]
  constructor
  · rw [div_le_iff₀ (by positivity)]
    have h1 : (3 / 4 : ℝ) ^ 2 ≤ ‖1 + I * τ * e‖ ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have h2 : τ * q * ‖1 - I / 2 * τ * e‖ ≤ τ * q * (9 / 8) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * τ * q)]
  · intro h1 h2
    have hqe : Real.exp (-2) < q := Real.exp_lt_exp.mpr (by linarith)
    rw [le_div_iff₀ (by positivity)]
    have h3 : ‖1 + I * τ * e‖ ^ 2 ≤ (5 / 4 : ℝ) ^ 2 := pow_le_pow_left₀ hD0.le (by linarith) 2
    have h4 : τ * q * (7 / 8) ≤ τ * q * ‖1 - I / 2 * τ * e‖ :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h5 : τ * Real.exp (-2) ≤ τ * q := mul_le_mul_of_nonneg_left hqe.le hτ.le
    have h6 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ τ * Real.exp (-2) / 2)
    nlinarith [Real.exp_pos (-2)]

theorem s11_sch_cm0 {τ : ℝ} (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4) :
    IsHPVanishingCarleson (hpSchwarzCarleson fun z => z + τ * exp (I * z)) := by
  have hU : MeasurableSet upperHalf :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  set D₁ : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (4 * τ ^ 2 * (z.im ^ 2 * Real.exp (-(2 * z.im))))
    with hD₁
  set g : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (4 * τ ^ 2 * (y ^ 2 * Real.exp (-(2 * y)))) *
    ENNReal.ofReal y with hg
  have hD₁m : Measurable D₁ := by rw [hD₁]; fun_prop
  have hgm : Measurable g := by rw [hg]; fun_prop
  have hImm : Measurable fun z : ℂ => ENNReal.ofReal z.im := by fun_prop
  -- `λ_f ≤ 4τ² y² e^{-2y} dx dy`
  have hmass : hpSchwarzMass (fun z => z + τ * exp (I * z)) ≤
      (volume.restrict upperHalf).withDensity D₁ := by
    unfold hpSchwarzMass
    refine withDensity_mono ((ae_restrict_iff' hU).mpr (Eventually.of_forall fun z hz => ?_))
    have hb := (s11_sch_Sf_bound hτ hτ' hz).1
    apply ENNReal.ofReal_le_ofReal
    have hs : ‖schwarzian (fun w => w + τ * exp (I * w)) z‖ ^ 2 ≤
        (2 * τ * Real.exp (-z.im)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hexp : Real.exp (-z.im) ^ 2 = Real.exp (-(2 * z.im)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have := mul_le_mul_of_nonneg_left hs (sq_nonneg z.im)
    rw [mul_pow, mul_pow, hexp] at this
    linarith
  have hbox : ∀ c ℓ : ℝ, hpSchwarzCarleson (fun z => z + τ * exp (I * z)) (hpBox c ℓ) ≤
      ENNReal.ofReal ℓ * ∫⁻ y in Ioc 0 ℓ, g y := by
    intro c ℓ
    have hQ := hp_measurableSet_box c ℓ
    calc hpSchwarzCarleson (fun z => z + τ * exp (I * z)) (hpBox c ℓ)
        ≤ ((volume.restrict upperHalf).withDensity D₁).withDensity
            (fun z => ENNReal.ofReal z.im) (hpBox c ℓ) := by
          unfold hpSchwarzCarleson hpWeight
          rw [withDensity_apply _ hQ, withDensity_apply _ hQ]
          exact lintegral_mono' (Measure.restrict_mono subset_rfl hmass) le_rfl
      _ = (volume.restrict upperHalf).withDensity (D₁ * fun z => ENNReal.ofReal z.im)
            (hpBox c ℓ) := by rw [withDensity_mul _ hD₁m hImm]
      _ ≤ _ := s11_sch_box_le hgm (fun z _ => le_rfl) c ℓ
  -- the `y`-integrals
  have hexpI : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-y)) = ENNReal.ofReal 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal, integral_exp_neg_Ioi_zero]
    · exact (by simpa using exp_neg_integrableOn_Ioi 0 (one_pos : (0 : ℝ) < 1) :
        IntegrableOn (fun y : ℝ => Real.exp (-y)) (Ioi 0))
    · exact ae_of_all _ fun y => (Real.exp_pos _).le
  have hcube : ∀ y : ℝ, 0 ≤ y → y ^ 3 * Real.exp (-y) ≤ 27 := by
    intro y hy
    have h1 := Real.add_one_le_exp (y / 3)
    have h2 : (y / 3 + 1) ^ 3 ≤ Real.exp (y / 3) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
    rw [← Real.exp_nat_mul] at h2
    have h3 : ((3 : ℕ) : ℝ) * (y / 3) = y := by push_cast; ring
    rw [h3] at h2
    have h4 : y ^ 3 ≤ 27 * Real.exp y := by nlinarith [sq_nonneg y, mul_nonneg hy (sq_nonneg y)]
    have h5 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-y)]
  have hgU : ∀ ℓ : ℝ, ∫⁻ y in Ioc 0 ℓ, g y ≤ ENNReal.ofReal (108 * τ ^ 2) := by
    intro ℓ
    calc ∫⁻ y in Ioc 0 ℓ, g y ≤ ∫⁻ y in Ioc 0 ℓ,
          ENNReal.ofReal (108 * τ ^ 2) * ENNReal.ofReal (Real.exp (-y)) := by
          refine setLIntegral_mono' measurableSet_Ioc fun y hy => ?_
          simp only [hg]
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have h := hcube y hy.1.le
          have he : Real.exp (-(2 * y)) = Real.exp (-y) * Real.exp (-y) := by
            rw [← Real.exp_add]; ring_nf
          rw [he]
          have h0 := Real.exp_pos (-y)
          nlinarith [mul_le_mul_of_nonneg_left h
            (by positivity : (0 : ℝ) ≤ 4 * τ ^ 2 * Real.exp (-y))]
      _ ≤ ∫⁻ y in Ioi 0, ENNReal.ofReal (108 * τ ^ 2) * ENNReal.ofReal (Real.exp (-y)) :=
          lintegral_mono_set Ioc_subset_Ioi_self
      _ = ENNReal.ofReal (108 * τ ^ 2) := by
          rw [lintegral_const_mul _ (by fun_prop), hexpI, ENNReal.ofReal_one, mul_one]
  have hgS : ∀ ℓ : ℝ, 0 < ℓ → ∫⁻ y in Ioc 0 ℓ, g y ≤ ENNReal.ofReal (4 * τ ^ 2 * ℓ ^ 3 * ℓ) := by
    intro ℓ hℓ
    calc ∫⁻ y in Ioc 0 ℓ, g y ≤ ∫⁻ y in Ioc 0 ℓ, ENNReal.ofReal (4 * τ ^ 2 * ℓ ^ 3) := by
          refine setLIntegral_mono' measurableSet_Ioc fun y hy => ?_
          simp only [hg]
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have h1 : Real.exp (-(2 * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hy.1])
          have h2 : y ^ 3 ≤ ℓ ^ 3 := pow_le_pow_left₀ hy.1.le hy.2 3
          have h3 : y ^ 2 * Real.exp (-(2 * y)) * y ≤ y ^ 3 := by
            nlinarith [mul_le_mul_of_nonneg_left h1 (pow_nonneg hy.1.le 3)]
          nlinarith [mul_le_mul_of_nonneg_left (h3.trans h2) (by positivity : (0 : ℝ) ≤ 4 * τ ^ 2)]
      _ = ENNReal.ofReal (4 * τ ^ 2 * ℓ ^ 3 * ℓ) := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
  have hratio : ∀ c ℓ : ℝ, 0 < ℓ →
      hpSchwarzCarleson (fun z => z + τ * exp (I * z)) (hpBox c ℓ) / ENNReal.ofReal ℓ ≤
        min (ENNReal.ofReal (108 * τ ^ 2)) (ENNReal.ofReal (4 * τ ^ 2 * ℓ ^ 3 * ℓ)) := by
    intro c ℓ hℓ
    refine ENNReal.div_le_of_le_mul ?_
    rw [mul_comm]
    refine (hbox c ℓ).trans ?_
    gcongr
    exact le_min (hgU ℓ) (hgS ℓ hℓ)
  refine ⟨?_, ?_⟩
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le fun c => iSup_le fun ℓ => iSup_le
      fun hℓ => (hratio c ℓ hℓ).trans (min_le_left _ _))
  · have h0 : Tendsto (fun r : ℝ => ENNReal.ofReal (4 * τ ^ 2 * r ^ 3 * r)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun r : ℝ => 4 * τ ^ 2 * r ^ 3 * r) (𝓝 0) (𝓝 (4 * τ ^ 2 * 0 ^ 3 * 0)) :=
        ((continuous_const.mul (continuous_pow 3)).mul continuous_id).tendsto 0
      simpa using (ENNReal.tendsto_ofReal this).mono_left nhdsWithin_le_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
      (Eventually.of_forall fun _ => zero_le') ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : 0 < r := hr
    refine iSup_le fun c => iSup_le fun ℓ => iSup_le fun hℓ => iSup_le fun hℓr => ?_
    refine (hratio c ℓ hℓ).trans ((min_le_right _ _).trans (ENNReal.ofReal_le_ofReal ?_))
    have h3 := pow_le_pow_left₀ hℓ.le hℓr 3
    have hτ2 : 0 ≤ 4 * τ ^ 2 := by positivity
    have := mul_le_mul (mul_le_mul_of_nonneg_left h3 hτ2) hℓr hℓ.le (by positivity)
    linarith

theorem s11_sch_band_le {τ : ℝ} (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4) :
    ENNReal.ofReal (τ ^ 2 * Real.exp (-4) / 4) • hpBandMeasure 1 2 ≤
      hpSchwarzMass fun z => z + τ * exp (I * z) := by
  have hU : MeasurableSet upperHalf :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hB : MeasurableSet {z : ℂ | 1 < z.im ∧ z.im < 2} :=
    (measurableSet_lt measurable_const Complex.measurable_im).inter
      (measurableSet_lt Complex.measurable_im measurable_const)
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [Measure.smul_apply, smul_eq_mul]
  unfold hpBandMeasure hpArea hpSchwarzMass
  rw [Measure.restrict_apply hs, withDensity_apply _ (hs.inter hB), withDensity_apply _ hs,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ∫⁻ z in s ∩ {z : ℂ | 1 < z.im ∧ z.im < 2}, ENNReal.ofReal (τ ^ 2 * Real.exp (-4) / 4) *
        ENNReal.ofReal ((z.im ^ 2)⁻¹) ∂(volume.restrict upperHalf)
      ≤ ∫⁻ z in s ∩ {z : ℂ | 1 < z.im ∧ z.im < 2},
          ENNReal.ofReal (z.im ^ 2 * ‖schwarzian (fun z => z + τ * exp (I * z)) z‖ ^ 2)
          ∂(volume.restrict upperHalf) := by
        rw [Measure.restrict_restrict (hs.inter hB)]
        refine setLIntegral_mono' ((hs.inter hB).inter hU) fun z hz => ?_
        obtain ⟨⟨-, h1, h2⟩, hzU⟩ := hz
        have hb := (s11_sch_Sf_bound hτ hτ' hzU).2 h1 h2
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hy2 : 1 < z.im ^ 2 := by nlinarith
        have hinv : (z.im ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hy2.le
        have hsq : (τ * Real.exp (-2) / 2) ^ 2 ≤
            ‖schwarzian (fun z => z + τ * exp (I * z)) z‖ ^ 2 :=
          pow_le_pow_left₀ (by positivity) hb 2
        have he : (τ * Real.exp (-2) / 2) ^ 2 = τ ^ 2 * Real.exp (-4) / 4 := by
          rw [div_pow, mul_pow, ← Real.exp_nat_mul]; norm_num
        rw [he] at hsq
        have hpos : 0 ≤ τ ^ 2 * Real.exp (-4) / 4 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hinv hpos,
          mul_le_mul_of_nonneg_right hy2.le
            (sq_nonneg ‖schwarzian (fun z => z + τ * exp (I * z)) z‖)]
    _ ≤ _ := lintegral_mono_set inter_subset_left

/-- Proposition 11.9 `prop:hp-schwarzian`, `sec11-halfplane.tex:679`: for `0 < τ ≤ 1/4`,
`f(z) = z + τ e^{iz}` maps `ℍ` conformally onto a quasidisk `Ω` with `∞ ∈ ∂Ω`, extends to a
`(1+τ)/(1-τ)`-quasiconformal homeomorphism of `ℂ`; `λ_f ∈ CM₀(ℍ)`, but for `F = H⁻¹`,
`Im w d(F_* m_f)(w) ∉ CM₀(ℍ)`. -/
theorem prop_hp_schwarzian {τ : ℝ} (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4) :
    IsConformalOnto (fun z => z + τ * exp (I * z)) upperHalf
        ((fun z => z + τ * exp (I * z)) '' upperHalf) ∧
      (∃ T : ℂ → ℂ, IsKQC T univ ((1 + τ) / (1 - τ)) ∧ T '' univ = univ ∧
        EqOn T (fun z => z + τ * exp (I * z)) upperHalf ∧
        IsKQuasiPair ((fun z => z + τ * exp (I * z)) '' upperHalf) (T '' lowerHalf)
          ((1 + τ) / (1 - τ))) ∧
      Tendsto (fun z => z + τ * exp (I * z)) (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ) ∧
      IsHPVanishingCarleson (hpSchwarzCarleson fun z => z + τ * exp (I * z)) ∧
      ¬ IsHPVanishingCarleson (hpPushWeight (Function.invFunOn hpPolyH closedUpperHalf)
        (hpSchwarzMass fun z => z + τ * exp (I * z))) := by
  -- the extension `T = z + τ e^{ix-|y|}` (`s11_sch_homeo`): conformal on `ℍ`, QC on `𝕃`
  obtain ⟨T, hT⟩ := s11_sch_homeo hτ.le (by linarith)
  have hTfun : (⇑T) = fun z => z + (τ : ℂ) * exp (I * z.re) * (Real.exp (-|z.im|) : ℂ) :=
    funext hT
  have hTf : EqOn T (fun z => z + τ * exp (I * z)) upperHalf := by
    rw [hTfun]
    exact s11_sch_upper_eq τ
  have h1τ : 0 < 1 - τ := by linarith
  have hK : 1 ≤ (1 + τ) / (1 - τ) := (le_div_iff₀ h1τ).mpr (by linarith)
  have hd : DifferentiableOn ℂ (fun z => z + τ * exp (I * z)) upperHalf :=
    (by fun_prop : Differentiable ℂ fun z : ℂ => z + τ * exp (I * z)).differentiableOn
  have hconf : IsConformalOnto (fun z => z + τ * exp (I * z)) upperHalf
      ((fun z => z + τ * exp (I * z)) '' upperHalf) :=
    ⟨hd, T.injective.injOn.congr hTf, rfl⟩
  have hU : IsKQC T upperHalf 1 :=
    isKQC_one_of_conformal isOpen_upperHalf ⟨hd.congr hTf, T.injective.injOn, rfl⟩
  have hL : IsKQC T lowerHalf ((1 + τ) / (1 - τ)) := by
    have := isKQC_of_isC1Quasiconformal (s11_sch_lower_qc hτ hτ')
    rwa [← hTfun] at this
  have hG : IsKQC T univ ((1 + τ) / (1 - τ)) := lem_hp_gluing T (hU.mono hK) hL
  have hTuniv : (⇑T) '' univ = univ := by rw [image_univ]; exact T.surjective.range_eq
  have hTU : (⇑T) '' upperHalf = (fun z => z + τ * exp (I * z)) '' upperHalf := hTf.image_eq
  refine ⟨hconf, ⟨T, hG, hTuniv, hTf, T, hG, hTuniv, hTU, rfl⟩, ?_, s11_sch_cm0 hτ hτ', ?_⟩
  · -- `|f z| ≥ |z| - τ` on `ℍ`
    have h0 : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ ⊓ 𝓟 upperHalf) atTop :=
      tendsto_norm_cocompact_atTop.mono_left inf_le_left
    have key : Tendsto (fun z => z + τ * exp (I * z)) (cocompact ℂ ⊓ 𝓟 upperHalf)
        (comap norm atTop) := by
      refine tendsto_comap_iff.mpr (tendsto_atTop_mono' _ ?_
        (tendsto_atTop_add_const_right _ (-τ) h0))
      filter_upwards [mem_inf_of_right (mem_principal_self upperHalf)] with z hz
      show ‖z‖ + -τ ≤ ‖z + (τ : ℂ) * exp (I * z)‖
      have hy : 0 < z.im := hz
      have he : ‖(τ : ℂ) * exp (I * z)‖ ≤ τ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ.le, Complex.norm_exp]
        have : (I * z).re = -z.im := by simp
        rw [this]
        exact mul_le_of_le_one_right hτ.le (Real.exp_le_one_iff.mpr (by linarith))
      have := norm_sub_norm_le z (-((τ : ℂ) * exp (I * z)))
      rw [norm_neg, sub_neg_eq_add] at this
      linarith
    rwa [comap_norm_atTop, Metric.cobounded_eq_cocompact] at key
  · exact s11_poly_not_cm0 (ENNReal.ofReal_pos.mpr (by positivity)).ne' (s11_sch_band_le hτ hτ')

/-! ## The welding and the two Schwarzian measures -/

/-- Helper (W0) for `set_hp_welding`: `hp_ext_transfer` without the boundary-continuity hypothesis
and with the conclusion on `ℍ` only: `F₁ = F₀ ∘ (κ z + β)`. -/
theorem s11_sw_ext {Ω : Set ℂ} {Q : ℝ} {f₀ F₀ f : ℂ → ℂ}
    (hf₀ : IsConformalOnto f₀ upperHalf Ω) (hF₀ : IsKQC F₀ univ Q) (hF₀s : F₀ '' univ = univ)
    (hE : EqOn F₀ f₀ upperHalf) (hf : IsConformalOnto f upperHalf Ω)
    (hfi : Tendsto f (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ)) :
    ∃ F₁ : ℂ → ℂ, IsKQC F₁ univ Q ∧ F₁ '' univ = univ ∧ EqOn F₁ f upperHalf := by
  have hU : IsOpen upperHalf := isOpen_upperHalf
  set A : ℂ → ℂ := Function.invFunOn f₀ upperHalf ∘ f with hAdef
  have hA : IsConformalOnto A upperHalf upperHalf := (hf₀.symm hU).comp hf
  -- `f₀ (A w) = f w` and `A w ∈ ℍ`
  have hAw : ∀ w ∈ upperHalf, A w ∈ upperHalf ∧ F₀ (A w) = f w := by
    intro w hw
    have hfw : f w ∈ f₀ '' upperHalf := by rw [hf₀.2.2]; exact hf.2.2 ▸ mem_image_of_mem f hw
    have hm : A w ∈ upperHalf := Function.invFunOn_mem hfw
    exact ⟨hm, by rw [hE hm]; exact Function.invFunOn_eq hfw⟩
  have hF₀c : Continuous F₀ := continuousOn_univ.mp hF₀.2.2.1.1
  have hAinf : Tendsto A (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ) := by
    refine (Filter.hasBasis_cocompact.tendsto_right_iff).mpr fun C hC => ?_
    have hC' : IsCompact (F₀ '' C) := hC.image hF₀c
    have h1 : ∀ᶠ w in cocompact ℂ ⊓ 𝓟 upperHalf, f w ∈ (F₀ '' C)ᶜ :=
      (Filter.hasBasis_cocompact.tendsto_right_iff).mp hfi _ hC'
    have h2 : ∀ᶠ w in cocompact ℂ ⊓ 𝓟 upperHalf, w ∈ upperHalf :=
      inf_le_right (a := cocompact ℂ) (mem_principal_self upperHalf)
    filter_upwards [h1, h2] with w hw1 hw2 hwC
    exact hw1 ⟨A w, hwC, (hAw w hw2).2⟩
  have hAn : Tendsto (fun w => ‖A w‖) (comap norm atTop ⊓ 𝓟 upperHalf) atTop := by
    rw [comap_norm_atTop, Metric.cobounded_eq_cocompact]
    exact tendsto_norm_cocompact_atTop.comp hAinf
  obtain ⟨κ, β, hκ, hAff⟩ := hp_automorphism_affine hA hAn
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  obtain ⟨hq, hs⟩ := td_affine_comp hF₀ hF₀s (β : ℂ) (0 : ℂ) hκ0 one_ne_zero
  simp only [one_mul, add_zero] at hq hs
  refine ⟨fun z => F₀ (κ * z + β), hq, hs, ?_⟩
  have hon : EqOn (fun z => F₀ (κ * z + β)) f upperHalf := by
    intro z hz
    simp only
    rw [← hAff z hz]
    exact (hAw z hz).2
  exact hon

/-- Helper (W1) for `set_hp_welding`: both sides of a `K`-quasi pair, as in `set_hp_extension`
but without continuity of `f, g` up to `ℝ`: q.c. homeomorphisms `F₁ = f` on `ℍ`, `G₁ = g` on `𝕃`. -/
theorem s11_sw_extend {Ω Ωs : Set ℂ} {K : ℝ} (hΓ : IsKQuasiPair Ω Ωs K) {f g : ℂ → ℂ}
    (hf : IsConformalOnto f upperHalf Ω) (hg : IsConformalOnto g lowerHalf Ωs)
    (hfinf : Tendsto f (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ))
    (hginf : Tendsto g (cocompact ℂ ⊓ 𝓟 lowerHalf) (cocompact ℂ)) :
    ∃ Q : ℝ, ∃ F₁ G₁ : ℂ → ℂ, IsKQC F₁ univ Q ∧ F₁ '' univ = univ ∧ EqOn F₁ f upperHalf ∧
      IsKQC G₁ univ Q ∧ G₁ '' univ = univ ∧ EqOn G₁ g lowerHalf := by
  obtain ⟨f₀, hf₀, F₀, hF₀, hF₀s, hE⟩ := s03_qce_partC hΓ
  obtain ⟨F₁, hF₁, hF₁s, hF₁e⟩ := s11_sw_ext hf₀ hF₀ hF₀s hE hf hfinf
  -- the lower side, through `g ∘ (-·) : ℍ → Ωs`
  obtain ⟨g₀, hg₀, G₀, hG₀, hG₀s, hEg⟩ := s03_qce_partC (s03_qce_swap hΓ)
  have hgn : IsConformalOnto (g ∘ fun u : ℂ => -u) upperHalf Ωs := hg.comp hp_isConformalOnto_neg
  have hneg : Tendsto (fun u : ℂ => -u) (cocompact ℂ ⊓ 𝓟 upperHalf)
      (cocompact ℂ ⊓ 𝓟 lowerHalf) := by
    refine tendsto_inf.mpr ⟨?_, tendsto_principal.mpr ?_⟩
    · exact (Homeomorph.neg ℂ).isClosedEmbedding.tendsto_cocompact.comp (tendsto_inf_left tendsto_id)
    · filter_upwards [inf_le_right (a := cocompact ℂ) (mem_principal_self upperHalf)] with u hu
      show (-u).im < 0
      have : (0 : ℝ) < u.im := hu
      simp; linarith
  obtain ⟨G₁, hG₁, hG₁s, hG₁e⟩ := s11_sw_ext hg₀ hG₀ hG₀s hEg hgn (hginf.comp hneg)
  obtain ⟨hq', hs'⟩ := td_affine_comp hG₁ hG₁s (0 : ℂ) (0 : ℂ) (neg_ne_zero.mpr one_ne_zero)
    one_ne_zero
  simp only [one_mul, add_zero, neg_one_mul] at hq' hs'
  refine ⟨K * K, F₁, fun z => G₁ (-z), hF₁, hF₁s, hF₁e, hq', hs', fun z hz => ?_⟩
  have hz' : -z ∈ upperHalf := by
    show 0 < (-z).im
    have : z.im < 0 := hz
    simp; linarith
  have := hG₁e hz'
  simp only [Function.comp_apply, neg_neg] at this
  exact this

/-- Helper (W2) for `set_hp_welding`: `∂ℍ = ℝ`. -/
theorem s11_sw_frontier_upper : frontier upperHalf = {z : ℂ | z.im = 0} := by
  exact Complex.frontier_setOfPred_lt_im 0

/-- Helper (W2) for `set_hp_welding`: `∂𝕃 = ℝ`. -/
theorem s11_sw_frontier_lower : frontier lowerHalf = {z : ℂ | z.im = 0} := by
  exact Complex.frontier_setOfPred_im_lt 0

/-- Helper (W2) for `set_hp_welding`: q.c. homeomorphisms `F₁ : ℍ → Ω`, `G₁ : 𝕃 → Ω*` of `ℂ` both
map `ℝ` onto `Φ(ℝ) = ∂Ω = ∂Ω*` (`Homeomorph.image_frontier`). -/
theorem s11_sw_real {Ω Ωs : Set ℂ} {K Q : ℝ} (hΓ : IsKQuasiPair Ω Ωs K) {F₁ G₁ : ℂ → ℂ}
    (hF₁ : IsKQC F₁ univ Q) (hF₁s : F₁ '' univ = univ) (hF₁Ω : F₁ '' upperHalf = Ω)
    (hG₁ : IsKQC G₁ univ Q) (hG₁s : G₁ '' univ = univ) (hG₁Ω : G₁ '' lowerHalf = Ωs) :
    F₁ '' {z : ℂ | z.im = 0} = G₁ '' {z : ℂ | z.im = 0} := by
  obtain ⟨Φ, hΦ, hΦs, hΦU, hΦL⟩ := hΓ
  obtain ⟨eΦ, heΦ⟩ := t1_homeomorph hΦ hΦs
  obtain ⟨eF, heF⟩ := t1_homeomorph hF₁ hF₁s
  obtain ⟨eG, heG⟩ := t1_homeomorph hG₁ hG₁s
  have h1 : F₁ '' {z : ℂ | z.im = 0} = Φ '' {z : ℂ | z.im = 0} := by
    rw [← s11_sw_frontier_upper, ← heF, ← heΦ, eF.image_frontier, eΦ.image_frontier, heF, heΦ,
      hF₁Ω, hΦU]
  have h2 : G₁ '' {z : ℂ | z.im = 0} = Φ '' {z : ℂ | z.im = 0} := by
    rw [← s11_sw_frontier_lower, ← heG, ← heΦ, eG.image_frontier, eΦ.image_frontier, heG, heΦ,
      hG₁Ω, hΦL]
  rw [h1, h2]

/-- Helper (W3) for `set_hp_welding`: if two q.c. homeomorphisms of `ℂ` have the same image of
`ℝ`, then `G₁⁻¹ ∘ F₁` restricts to a homeomorphism `w` of `ℝ` with `F₁ = G₁ ∘ w` on `ℝ`. -/
theorem s11_sw_weld {F₁ G₁ : ℂ → ℂ} {Q : ℝ} (hF₁ : IsKQC F₁ univ Q) (hF₁s : F₁ '' univ = univ)
    (hG₁ : IsKQC G₁ univ Q) (hG₁s : G₁ '' univ = univ)
    (hR : F₁ '' {z : ℂ | z.im = 0} = G₁ '' {z : ℂ | z.im = 0}) :
    ∃ w : ℝ ≃ₜ ℝ, ∀ x : ℝ, F₁ (x : ℂ) = G₁ ((w x : ℝ) : ℂ) := by
  obtain ⟨eF, heF⟩ := t1_homeomorph hF₁ hF₁s
  obtain ⟨eG, heG⟩ := t1_homeomorph hG₁ hG₁s
  have hre : ∀ z : ℂ, z.im = 0 → ((z.re : ℝ) : ℂ) = z := fun z hz =>
    Complex.ext (by simp) (by simp [hz])
  have hreal : ∀ x : ℝ, (eG.symm (eF (x : ℂ))).im = 0 := by
    intro x
    have hm : F₁ (x : ℂ) ∈ G₁ '' {z : ℂ | z.im = 0} :=
      hR ▸ mem_image_of_mem F₁ (show ((x : ℂ)).im = 0 by simp)
    obtain ⟨y, hy, hyx⟩ := hm
    rw [heF, ← hyx, ← heG, eG.symm_apply_apply]
    exact hy
  have hreal' : ∀ y : ℝ, (eF.symm (eG (y : ℂ))).im = 0 := by
    intro y
    have hm : G₁ (y : ℂ) ∈ F₁ '' {z : ℂ | z.im = 0} :=
      hR.symm ▸ mem_image_of_mem G₁ (show ((y : ℂ)).im = 0 by simp)
    obtain ⟨x, hx, hxy⟩ := hm
    rw [heG, ← hxy, ← heF, eF.symm_apply_apply]
    exact hx
  let w : ℝ ≃ₜ ℝ :=
    { toFun := fun x => (eG.symm (eF (x : ℂ))).re
      invFun := fun y => (eF.symm (eG (y : ℂ))).re
      left_inv := fun x => by
        simp only
        rw [hre _ (hreal x), Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply]
        simp
      right_inv := fun y => by
        simp only
        rw [hre _ (hreal' y), Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply]
        simp
      continuous_toFun := Complex.continuous_re.comp
        (eG.symm.continuous.comp (eF.continuous.comp Complex.continuous_ofReal))
      continuous_invFun := Complex.continuous_re.comp
        (eF.symm.continuous.comp (eG.continuous.comp Complex.continuous_ofReal)) }
  refine ⟨w, fun x => ?_⟩
  show F₁ (x : ℂ) = G₁ (((eG.symm (eF (x : ℂ))).re : ℝ) : ℂ)
  rw [hre _ (hreal x), ← heG, Homeomorph.apply_symm_apply, heF]

/-- Helper: if one conformal `f₀ : ℍ → Ω` has a `Q`-q.c. extension `F₀` to `ℂ`, then every
conformal `f : ℍ → Ω` with `f(∞) = ∞`, continuous on `ℍ ∪ ℝ`, has one (`F₀ ∘ (κ z + β)`). -/
theorem hp_ext_transfer {Ω : Set ℂ} {Q : ℝ} {f₀ F₀ f : ℂ → ℂ}
    (hf₀ : IsConformalOnto f₀ upperHalf Ω) (hF₀ : IsKQC F₀ univ Q) (hF₀s : F₀ '' univ = univ)
    (hE : EqOn F₀ f₀ upperHalf) (hf : IsConformalOnto f upperHalf Ω)
    (hfc : ContinuousOn f closedUpperHalf)
    (hfi : Tendsto f (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ)) :
    ∃ F₁ : ℂ → ℂ, IsKQC F₁ univ Q ∧ F₁ '' univ = univ ∧ EqOn F₁ f closedUpperHalf := by
  obtain ⟨F₁, hq, hs, hon⟩ := s11_sw_ext hf₀ hF₀ hF₀s hE hf hfi
  refine ⟨F₁, hq, hs, ?_⟩
  have hcl : closedUpperHalf ⊆ closure upperHalf := by
    rw [show upperHalf = {z : ℂ | 0 < z.im} from rfl, Complex.closure_setOfPred_lt_im]
    intro z hz; exact hz
  refine hon.of_subset_closure ?_ hfc (fun z (hz : 0 < z.im) => show 0 ≤ z.im from le_of_lt hz) hcl
  exact (continuousOn_univ.mp hq.2.2.1.1).continuousOn

/-- Convention `set:hp`, `sec11-halfplane.tex:742–749` (via Lemma `lem:qc-extension`): `f` and `g`
extend to `Q(K)`-quasiconformal homeomorphisms of `ℂ`, with `Q` depending only on `K`. -/
theorem set_hp_extension : ∀ K : ℝ, 1 ≤ K → ∃ Q : ℝ, 1 ≤ Q ∧
    ∀ (Ω Ωs : Set ℂ) (f g : ℂ → ℂ) (w : ℝ ≃ₜ ℝ), IsHPSetting Ω Ωs K f g w →
      ∃ F₁ G₁ : ℂ → ℂ, IsKQC F₁ univ Q ∧ F₁ '' univ = univ ∧ EqOn F₁ f closedUpperHalf ∧
        IsKQC G₁ univ Q ∧ G₁ '' univ = univ ∧ EqOn G₁ g closedLowerHalf := by
  intro K hK
  refine ⟨K * K, by nlinarith, fun Ω Ωs f g w hs => ?_⟩
  obtain ⟨hq, -, hf, hg, hfc, hgc, hfi, hgi, -⟩ := hs
  -- the upper side
  obtain ⟨f₀, hf₀, F₀, hF₀, hF₀s, hE⟩ := s03_qce_partC hq
  obtain ⟨F₁, hF₁, hF₁s, hF₁e⟩ := hp_ext_transfer hf₀ hF₀ hF₀s hE hf hfc hfi
  -- the lower side, through `g ∘ (-·) : ℍ → Ωs`
  obtain ⟨g₀, hg₀, G₀, hG₀, hG₀s, hEg⟩ := s03_qce_partC (s03_qce_swap hq)
  have hgn : IsConformalOnto (g ∘ fun u : ℂ => -u) upperHalf Ωs := hg.comp hp_isConformalOnto_neg
  have hgnc : ContinuousOn (g ∘ fun u : ℂ => -u) closedUpperHalf :=
    hgc.comp (by fun_prop) fun z (hz : 0 ≤ z.im) => show (-z).im ≤ 0 by simp; exact hz
  have hneg : Tendsto (fun u : ℂ => -u) (cocompact ℂ ⊓ 𝓟 upperHalf)
      (cocompact ℂ ⊓ 𝓟 lowerHalf) := by
    refine tendsto_inf.mpr ⟨?_, tendsto_principal.mpr ?_⟩
    · exact (Homeomorph.neg ℂ).isClosedEmbedding.tendsto_cocompact.comp (tendsto_inf_left tendsto_id)
    · filter_upwards [inf_le_right (a := cocompact ℂ) (mem_principal_self upperHalf)] with u hu
      show (-u).im < 0
      have : (0 : ℝ) < u.im := hu
      simp; linarith
  obtain ⟨G₁, hG₁, hG₁s, hG₁e⟩ := hp_ext_transfer hg₀ hG₀ hG₀s hEg hgn hgnc (hgi.comp hneg)
  obtain ⟨hq', hs'⟩ := td_affine_comp hG₁ hG₁s (0 : ℂ) (0 : ℂ) (neg_ne_zero.mpr one_ne_zero)
    one_ne_zero
  simp only [one_mul, add_zero, neg_one_mul] at hq' hs'
  refine ⟨F₁, fun z => G₁ (-z), hF₁, hF₁s, hF₁e, hq', hs', fun z hz => ?_⟩
  have hz' : -z ∈ closedUpperHalf := by
    show 0 ≤ (-z).im
    have : z.im ≤ 0 := hz
    simp; linarith
  have := hG₁e hz'
  simp only [Function.comp_apply, neg_neg] at this
  exact this

/-- Helper for `set_hp_invariance` (W-AUT): two conformal maps `ℍ → Ω` differ by an increasing real
affine map when one has a continuous extension `F` to `ℂ` and the other sends `∞` to `∞`
(`hp_automorphism_affine` applied to `f⁻¹ ∘ f'`, as in `hp_ext_transfer`). -/
theorem hpv_aut_upper {Ω : Set ℂ} {f f' F : ℂ → ℂ} (hf : IsConformalOnto f upperHalf Ω)
    (hf' : IsConformalOnto f' upperHalf Ω) (hF : Continuous F) (hFf : EqOn F f upperHalf)
    (hf'i : Tendsto f' (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ)) :
    ∃ a b : ℝ, 0 < a ∧ ∀ z ∈ upperHalf, f' z = f ((a : ℂ) * z + b) := by
  have hU : IsOpen upperHalf := isOpen_upperHalf
  set A : ℂ → ℂ := Function.invFunOn f upperHalf ∘ f' with hAdef
  have hA : IsConformalOnto A upperHalf upperHalf := (hf.symm hU).comp hf'
  -- `A w ∈ ℍ` and `f (A w) = f' w`
  have hAw : ∀ w ∈ upperHalf, A w ∈ upperHalf ∧ f (A w) = f' w := by
    intro w hw
    have hfw : f' w ∈ f '' upperHalf := by rw [hf.2.2]; exact hf'.2.2 ▸ mem_image_of_mem f' hw
    exact ⟨Function.invFunOn_mem hfw, Function.invFunOn_eq hfw⟩
  have hAinf : Tendsto A (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ) := by
    refine (Filter.hasBasis_cocompact.tendsto_right_iff).mpr fun C hC => ?_
    have hC' : IsCompact (F '' C) := hC.image hF
    have h1 : ∀ᶠ w in cocompact ℂ ⊓ 𝓟 upperHalf, f' w ∈ (F '' C)ᶜ :=
      (Filter.hasBasis_cocompact.tendsto_right_iff).mp hf'i _ hC'
    have h2 : ∀ᶠ w in cocompact ℂ ⊓ 𝓟 upperHalf, w ∈ upperHalf :=
      inf_le_right (a := cocompact ℂ) (mem_principal_self upperHalf)
    filter_upwards [h1, h2] with w hw1 hw2 hwC
    exact hw1 ⟨A w, hwC, by rw [hFf (hAw w hw2).1]; exact (hAw w hw2).2⟩
  have hAn : Tendsto (fun w => ‖A w‖) (comap norm atTop ⊓ 𝓟 upperHalf) atTop := by
    rw [comap_norm_atTop, Metric.cobounded_eq_cocompact]
    exact tendsto_norm_cocompact_atTop.comp hAinf
  obtain ⟨κ, β, hκ, hAff⟩ := hp_automorphism_affine hA hAn
  refine ⟨κ, β, hκ, fun z hz => ?_⟩
  rw [← hAff z hz]
  exact (hAw z hz).2.symm

/-- Helper for `set_hp_invariance` (conjunct 1): two settings with the same `(Ω, Ωs)` differ by
increasing real affine maps, `f' = f ∘ A₁` on `ℍ`, `g' = g ∘ A₂` on `𝕃`, and then
`A₂ ∘ w' = w ∘ A₁` on `ℝ`. The upper map comes from `hpv_aut_upper` with the extension of
`hp_ext_transfer`, and the lower one from `hpv_aut_upper` for `g ∘ (-·)`. The relation for `w`
follows by continuity up to `ℝ` and injectivity of the extension of `g`. -/
theorem hpv_welding_affine {Ω Ωs : Set ℂ} {K K' : ℝ} {f g f' g' : ℂ → ℂ} {w w' : ℝ ≃ₜ ℝ}
    (hs : IsHPSetting Ω Ωs K f g w) (hs' : IsHPSetting Ω Ωs K' f' g' w') :
    ∃ a₁ b₁ a₂ b₂ : ℝ, 0 < a₁ ∧ 0 < a₂ ∧
      (∀ z ∈ upperHalf, f' z = f ((a₁ : ℂ) * z + b₁)) ∧
      (∀ z ∈ lowerHalf, g' z = g ((a₂ : ℂ) * z + b₂)) ∧
      ∀ x, a₂ * w' x + b₂ = w (a₁ * x + b₁) := by
  obtain ⟨hq, -, hf, hg, hfc, hgc, hfi, hgi, hw⟩ := hs
  obtain ⟨-, -, hf', hg', hfc', hgc', hfi', hgi', hw'⟩ := hs'
  have hUc : upperHalf ⊆ closedUpperHalf := fun z (hz : 0 < z.im) => show 0 ≤ z.im from hz.le
  have hLc : lowerHalf ⊆ closedLowerHalf := fun z (hz : z.im < 0) => show z.im ≤ 0 from hz.le
  have hcl : closedUpperHalf ⊆ closure upperHalf := by
    rw [show upperHalf = {z : ℂ | 0 < z.im} from rfl, Complex.closure_setOfPred_lt_im]
    intro z hz; exact hz
  have hclL : closedLowerHalf ⊆ closure lowerHalf := by
    rw [show lowerHalf = {z : ℂ | z.im < 0} from rfl, Complex.closure_setOfPred_im_lt]
    intro z hz; exact hz
  -- the upper side: `f' = f ∘ A₁` through the extension `F₁` of `f`
  obtain ⟨f₀, hf₀, F₀, hF₀, hF₀s, hE⟩ := s03_qce_partC hq
  obtain ⟨F₁, hF₁, -, hF₁e⟩ := hp_ext_transfer hf₀ hF₀ hF₀s hE hf hfc hfi
  have hF₁c : Continuous F₁ := continuousOn_univ.mp hF₁.2.2.1.1
  obtain ⟨a₁, b₁, ha₁, hff⟩ := hpv_aut_upper hf hf' hF₁c (hF₁e.mono hUc) hfi'
  -- the lower side, through `g ∘ (-·)` and the extension `G₁` of it
  obtain ⟨g₀, hg₀, G₀, hG₀, hG₀s, hEg⟩ := s03_qce_partC (s03_qce_swap hq)
  have hgn : IsConformalOnto (g ∘ fun u : ℂ => -u) upperHalf Ωs := hg.comp hp_isConformalOnto_neg
  have hgn' : IsConformalOnto (g' ∘ fun u : ℂ => -u) upperHalf Ωs :=
    hg'.comp hp_isConformalOnto_neg
  have hgnc : ContinuousOn (g ∘ fun u : ℂ => -u) closedUpperHalf :=
    hgc.comp (by fun_prop) fun z (hz : 0 ≤ z.im) => show (-z).im ≤ 0 by simp; exact hz
  have hneg : Tendsto (fun u : ℂ => -u) (cocompact ℂ ⊓ 𝓟 upperHalf)
      (cocompact ℂ ⊓ 𝓟 lowerHalf) := by
    refine tendsto_inf.mpr ⟨?_, tendsto_principal.mpr ?_⟩
    · exact (Homeomorph.neg ℂ).isClosedEmbedding.tendsto_cocompact.comp (tendsto_inf_left tendsto_id)
    · filter_upwards [inf_le_right (a := cocompact ℂ) (mem_principal_self upperHalf)] with u hu
      show (-u).im < 0
      have : (0 : ℝ) < u.im := hu
      simp; linarith
  obtain ⟨G₁, hG₁, -, hG₁e⟩ := hp_ext_transfer hg₀ hG₀ hG₀s hEg hgn hgnc (hgi.comp hneg)
  have hG₁c : Continuous G₁ := continuousOn_univ.mp hG₁.2.2.1.1
  obtain ⟨a₂, β, ha₂, hgg0⟩ := hpv_aut_upper hgn hgn' hG₁c (hG₁e.mono hUc) (hgi'.comp hneg)
  -- `g = G₁ ∘ (-·)` on `𝕃 ∪ ℝ`
  have hgG : ∀ v ∈ closedLowerHalf, g v = G₁ (-v) := by
    intro v hv
    have hv' : -v ∈ closedUpperHalf := by
      show 0 ≤ (-v).im
      have : v.im ≤ 0 := hv
      simp; linarith
    have := hG₁e hv'
    simp only [Function.comp_apply, neg_neg] at this
    exact this.symm
  have hgg : ∀ z ∈ lowerHalf, g' z = g ((a₂ : ℂ) * z + ((-β : ℝ) : ℂ)) := by
    intro z hz
    have hz' : -z ∈ upperHalf := by
      show 0 < (-z).im
      have : z.im < 0 := hz
      simp; linarith
    have := hgg0 (-z) hz'
    simp only [Function.comp_apply, neg_neg] at this
    rw [this]
    congr 1
    push_cast
    ring
  -- both relations extend to the boundary by continuity
  have hfcl : ∀ z ∈ closedUpperHalf, f' z = F₁ ((a₁ : ℂ) * z + b₁) := by
    have hon : EqOn (fun z => F₁ ((a₁ : ℂ) * z + b₁)) f' upperHalf := by
      intro z hz
      have hAz : (a₁ : ℂ) * z + b₁ ∈ closedUpperHalf := by
        show 0 ≤ ((a₁ : ℂ) * z + b₁).im
        rw [show ((a₁ : ℂ) * z + b₁).im = a₁ * z.im by simp]
        exact mul_nonneg ha₁.le (le_of_lt hz)
      simp only
      rw [hF₁e hAz, hff z hz]
    exact fun z hz =>
      (hon.of_subset_closure (hF₁c.comp (by fun_prop)).continuousOn hfc' hUc hcl hz).symm
  have hgcl : ∀ z ∈ closedLowerHalf, g' z = G₁ (-((a₂ : ℂ) * z + ((-β : ℝ) : ℂ))) := by
    have hon : EqOn (fun z => G₁ (-((a₂ : ℂ) * z + ((-β : ℝ) : ℂ)))) g' lowerHalf := by
      intro z hz
      have hAz : (a₂ : ℂ) * z + ((-β : ℝ) : ℂ) ∈ closedLowerHalf := by
        show ((a₂ : ℂ) * z + ((-β : ℝ) : ℂ)).im ≤ 0
        rw [show ((a₂ : ℂ) * z + ((-β : ℝ) : ℂ)).im = a₂ * z.im by simp]
        have : z.im < 0 := hz
        exact mul_nonpos_of_nonneg_of_nonpos ha₂.le this.le
      simp only
      rw [← hgG _ hAz, hgg z hz]
    exact fun z hz =>
      (hon.of_subset_closure (hG₁c.comp (by fun_prop)).continuousOn hgc' hLc hclL hz).symm
  refine ⟨a₁, b₁, a₂, -β, ha₁, ha₂, hff, hgg, fun x => ?_⟩
  have hx0 : ∀ t : ℝ, (t : ℂ) ∈ closedUpperHalf := fun t => show 0 ≤ (t : ℂ).im by simp
  have hx1 : ∀ t : ℝ, (t : ℂ) ∈ closedLowerHalf := fun t => show (t : ℂ).im ≤ 0 by simp
  -- `f' x = g (w (A₁ x)) = g' (w' x) = g (A₂ (w' x))`, and `G₁` is injective
  have e1 : f' x = G₁ (-((w (a₁ * x + b₁) : ℝ) : ℂ)) := by
    rw [hfcl _ (hx0 x), show (a₁ : ℂ) * x + b₁ = ((a₁ * x + b₁ : ℝ) : ℂ) by push_cast; ring,
      hF₁e (hx0 _), hw, hgG _ (hx1 _)]
  have e2 : f' x = G₁ (-((a₂ * w' x + -β : ℝ) : ℂ)) := by
    rw [hw', hgcl _ (hx1 _)]
    congr 2
    push_cast
    ring
  have h := hG₁.2.2.1.2.1 (mem_univ _) (mem_univ _) (e2.symm.trans e1)
  exact_mod_cast neg_injective h

/-- Helper for `set_hp_invariance`: `SQS` survives increasing affine changes of variable on both
sides. `h' = B⁻¹ ∘ h ∘ A` with `A x = a x + b`, `B y = c y + d`, and density `(a/c)·ω ∘ A`. -/
theorem hpv_sqsWith_affine {h ω : ℝ → ℝ} {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hh : IsSQSWith h ω) :
    IsSQSWith (fun x => (h (a * x + b) - d) / c) (fun x => a / c * ω (a * x + b)) := by
  obtain ⟨hmono, hcont, hsurj, ⟨hnn, hloc, C, δ, hC, hδ, hAI⟩, hF⟩ := hh
  have hd : ∀ x, HasDerivAt (fun x => a * x + b) a x := fun x => by
    have := ((hasDerivAt_id' x).const_mul a).add_const b
    rwa [mul_one] at this
  have hinj : Function.Injective fun x => a * x + b := fun x y hxy =>
    mul_left_cancel₀ ha.ne' (add_right_cancel hxy)
  -- `∫_s (a/c) ω ∘ A = c⁻¹ ∫_{A s} ω` and `|A s| = a |s|`
  have hcv : ∀ s, MeasurableSet s →
      ∫ x in s, a / c * ω (a * x + b) = c⁻¹ * ∫ y in (fun x => a * x + b) '' s, ω y := by
    intro s hs
    rw [integral_image_eq_integral_abs_deriv_smul hs (fun x _ => (hd x).hasDerivWithinAt)
      hinj.injOn, integral_const_mul]
    simp only [smul_eq_mul]
    rw [integral_const_mul, abs_of_pos ha]
    field_simp
  have hvol : ∀ s, MeasurableSet s →
      volume ((fun x => a * x + b) '' s) = ENNReal.ofReal a * volume s := by
    intro s hs
    have := lintegral_image_eq_lintegral_abs_deriv_mul hs (fun x _ => (hd x).hasDerivWithinAt)
      hinj.injOn (fun _ => (1 : ℝ≥0∞))
    simp only [setLIntegral_one, mul_one, setLIntegral_const] at this
    rw [this, abs_of_pos ha]
  have hli : LocallyIntegrable fun x => ω (a * x + b) := by
    rw [locallyIntegrable_iff] at hloc ⊢
    intro k hk
    have h1 := (integrableOn_image_iff_integrableOn_abs_deriv_smul hk.measurableSet
      (fun x _ => (hd x).hasDerivWithinAt) hinj.injOn ω).mp (hloc _ (hk.image (by fun_prop)))
    refine IntegrableOn.congr_fun (Integrable.const_mul h1 |a|⁻¹) (fun x _ => ?_) hk.measurableSet
    simp only [smul_eq_mul]
    rw [inv_mul_cancel_left₀ (abs_pos.2 ha.ne').ne']
  have hii : ∀ u v : ℝ, IntervalIntegrable ω volume u v := fun u v =>
    (hloc.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  refine ⟨fun x y hxy => ?_, ?_, fun y => ?_, ⟨fun x => ?_, ?_, C, δ, hC, hδ, ?_⟩, fun x => ?_⟩
  · show (h (a * x + b) - d) / c < (h (a * y + b) - d) / c
    exact div_lt_div_of_pos_right (sub_lt_sub_right (hmono (by nlinarith)) d) hc
  · exact ((hcont.comp (by fun_prop : Continuous fun x : ℝ => a * x + b)).sub
      continuous_const).div_const c
  · obtain ⟨x0, hx0⟩ := hsurj (c * y + d)
    refine ⟨(x0 - b) / a, ?_⟩
    show (h (a * ((x0 - b) / a) + b) - d) / c = y
    rw [mul_div_cancel₀ _ ha.ne', sub_add_cancel, hx0, add_sub_cancel_right,
      mul_div_cancel_left₀ _ hc.ne']
  · exact mul_nonneg (div_nonneg ha.le hc.le) (hnn _)
  · exact LocallyIntegrable.smul hli (a / c)
  · intro α β hαβ E hE hEm
    have hAαβ : a * α + b < a * β + b := by nlinarith
    have hE' : (fun x => a * x + b) '' E ⊆ Icc (a * α + b) (a * β + b) := by
      rw [← image_affine_Icc' ha]
      exact image_mono hE
    have key := hAI _ _ hAαβ _ hE'
      (hEm.image_of_continuousOn_injOn (by fun_prop) hinj.injOn)
    rw [hvol E hEm, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le,
      show a * β + b - (a * α + b) = a * (β - α) by ring, mul_div_mul_left _ _ ha.ne'] at key
    rw [hcv E hEm, hcv _ measurableSet_Icc, image_affine_Icc' ha]
    calc c⁻¹ * ∫ y in (fun x => a * x + b) '' E, ω y
        ≤ c⁻¹ * (C * ((volume E).toReal / (β - α)) ^ δ *
          ∫ y in Icc (a * α + b) (a * β + b), ω y) :=
          mul_le_mul_of_nonneg_left key (inv_nonneg.2 hc.le)
      _ = _ := by ring
  · show (h (a * x + b) - d) / c = (h (a * 0 + b) - d) / c + ∫ t in (0 : ℝ)..x, a / c * ω (a * t + b)
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_add (fun t => ω t) ha.ne',
      ← intervalIntegral.integral_interval_sub_left (hii 0 _) (hii 0 _), hF (a * x + b),
      hF (a * 0 + b), smul_eq_mul]
    field_simp
    ring

/-- Helper for `set_hp_invariance`: `VMO(ℝ)` survives an increasing affine change of variable plus
a constant (`realMeanOsc (u ∘ A + k) α β = realMeanOsc u (A α) (A β)`). -/
theorem hpv_vmo_affine {u : ℝ → ℝ} {a b k : ℝ} (ha : 0 < a) (hu : IsVMOReal u) :
    IsVMOReal fun x => u (a * x + b) + k := by
  obtain ⟨⟨hloc, C, hC⟩, hv⟩ := hu
  have hd : ∀ x, HasDerivAt (fun x => a * x + b) a x := fun x => by
    have := ((hasDerivAt_id' x).const_mul a).add_const b
    rwa [mul_one] at this
  have hinj : Function.Injective fun x => a * x + b := fun x y hxy =>
    mul_left_cancel₀ ha.ne' (add_right_cancel hxy)
  have hli : LocallyIntegrable fun x => u (a * x + b) := by
    rw [locallyIntegrable_iff] at hloc ⊢
    intro k hk
    have h1 := (integrableOn_image_iff_integrableOn_abs_deriv_smul hk.measurableSet
      (fun x _ => (hd x).hasDerivWithinAt) hinj.injOn u).mp (hloc _ (hk.image (by fun_prop)))
    refine IntegrableOn.congr_fun (Integrable.const_mul h1 |a|⁻¹) (fun x _ => ?_) hk.measurableSet
    simp only [smul_eq_mul]
    rw [inv_mul_cancel_left₀ (abs_pos.2 ha.ne').ne']
  have hii : ∀ α β, IntervalIntegrable (fun x => u (a * x + b)) volume α β := fun α β =>
    (hli.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  -- the mean oscillation is invariant
  have hosc : ∀ α β, α < β →
      realMeanOsc (fun x => u (a * x + b) + k) α β = realMeanOsc u (a * α + b) (a * β + b) := by
    intro α β hαβ
    have hne : β - α ≠ 0 := sub_ne_zero.2 hαβ.ne'
    have hlen : a * β + b - (a * α + b) = a * (β - α) := by ring
    have hmean : intervalMean (fun x => u (a * x + b) + k) α β =
        intervalMean u (a * α + b) (a * β + b) + k := by
      simp only [intervalMean]
      rw [intervalIntegral.integral_add (hii α β) intervalIntegrable_const,
        intervalIntegral.integral_comp_mul_add (fun x => u x) ha.ne',
        intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul, hlen, mul_add,
        ← mul_assoc _ (β - α), inv_mul_cancel₀ hne, one_mul, mul_inv]
      ring
    have h2 : ∫ x in α..β, |u (a * x + b) + k - (intervalMean u (a * α + b) (a * β + b) + k)| =
        a⁻¹ * ∫ y in (a * α + b)..(a * β + b), |u y - intervalMean u (a * α + b) (a * β + b)| := by
      simp_rw [add_sub_add_right_eq_sub]
      rw [intervalIntegral.integral_comp_mul_add
        (fun y => |u y - intervalMean u (a * α + b) (a * β + b)|) ha.ne', smul_eq_mul]
    simp only [realMeanOsc]
    rw [hmean, h2, hlen, mul_inv]
    ring
  refine ⟨⟨hli.add (locallyIntegrable_const k), C, fun α β h => ?_⟩, fun ε hε => ?_⟩
  · rw [hosc α β h]
    exact hC _ _ (by nlinarith)
  · obtain ⟨δ, hδ, H⟩ := hv ε hε
    refine ⟨δ / a, div_pos hδ ha, fun α β h hl => ?_⟩
    rw [hosc α β h]
    have := (lt_div_iff₀ ha).1 hl
    exact H _ _ (by nlinarith) (by nlinarith)

/-- Helper for `set_hp_invariance`: `VMO(ℝ)` only sees `u` almost everywhere. -/
theorem hpv_vmo_congr {u v : ℝ → ℝ} (hu : IsVMOReal u) (huv : u =ᵐ[volume] v) : IsVMOReal v := by
  obtain ⟨⟨hloc, C, hC⟩, hv⟩ := hu
  have hI : ∀ α β, ∫ x in α..β, u x = ∫ x in α..β, v x := fun α β =>
    intervalIntegral.integral_congr_ae (huv.mono fun x hx _ => hx)
  have hO : ∀ α β, realMeanOsc u α β = realMeanOsc v α β := by
    intro α β
    simp only [realMeanOsc, intervalMean]
    rw [hI α β]
    congr 1
    exact intervalIntegral.integral_congr_ae (huv.mono fun x hx _ => by rw [hx])
  refine ⟨⟨hloc.congr huv, C, fun α β h => ?_⟩, fun ε hε => ?_⟩
  · rw [← hO]
    exact hC α β h
  · obtain ⟨δ, hδ, H⟩ := hv ε hε
    exact ⟨δ, hδ, fun α β h hl => by rw [← hO]; exact H α β h hl⟩

/-- Helper for `set_hp_invariance` (conjuncts 2–6): `SQS`, `SS` and uniform continuity survive
`h ↦ B⁻¹ ∘ h ∘ A` for increasing real affine `A x = a x + b`, `B y = c y + d`. -/
theorem hpv_real_affine {h : ℝ → ℝ} {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) :
    (IsSQS h → IsSQS fun x => (h (a * x + b) - d) / c) ∧
      (IsSS h → IsSS fun x => (h (a * x + b) - d) / c) ∧
      (UniformContinuous h → UniformContinuous fun x => (h (a * x + b) - d) / c) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨ω, hω⟩
    exact ⟨_, hpv_sqsWith_affine ha hc hω⟩
  · rintro ⟨ω, hω, hpos, hlog⟩
    -- `ω ∘ A > 0` a.e., since `A` is quasi-measure-preserving
    have hq : QuasiMeasurePreserving (fun t : ℝ => a * t + b) volume volume :=
      (measurePreserving_add_right (volume : Measure ℝ) b).quasiMeasurePreserving.comp
        (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ)) ha.ne')
    have hposA : ∀ᵐ t, 0 < ω (a * t + b) := by
      filter_upwards [hq.ae hpos] with t ht
      exact ht
    refine ⟨_, hpv_sqsWith_affine ha hc hω, ?_, ?_⟩
    · filter_upwards [hposA] with t ht
      exact mul_pos (div_pos ha hc) ht
    · refine hpv_vmo_congr (hpv_vmo_affine (b := b) (k := Real.log (a / c)) ha hlog) ?_
      filter_upwards [hposA] with t ht
      rw [Real.log_mul (div_pos ha hc).ne' ht.ne', add_comm]
  · intro hu
    rw [Metric.uniformContinuous_iff] at hu ⊢
    intro ε hε
    obtain ⟨δ, hδ, H⟩ := hu (c * ε) (mul_pos hc hε)
    refine ⟨δ / a, div_pos hδ ha, ?_⟩
    intro x y hxy
    have h1 : dist (a * x + b) (a * y + b) < δ := by
      rw [Real.dist_eq] at hxy ⊢
      rw [show a * x + b - (a * y + b) = a * (x - y) by ring, abs_mul, abs_of_pos ha]
      have := (lt_div_iff₀ ha).1 hxy
      linarith
    have h2 := H h1
    rw [Real.dist_eq] at h2 ⊢
    show |(h (a * x + b) - d) / c - (h (a * y + b) - d) / c| < ε
    rw [show (h (a * x + b) - d) / c - (h (a * y + b) - d) / c =
      (h (a * x + b) - h (a * y + b)) / c by ring, abs_div, abs_of_pos hc, div_lt_iff₀ hc]
    linarith

/-- Helper for `set_hp_invariance`: if `f' = f ∘ A` on an open set `U`, `A z = a z + b`, then
`S_hol f' = a² (S_hol f) ∘ A` on `U` (`hp_schwarzianHol_affine` and locality of `deriv`). -/
theorem hpv_schwarzianHol_congr {U : Set ℂ} (hU : IsOpen U) {f f' : ℂ → ℂ} {a b : ℂ} (ha : a ≠ 0)
    (h : ∀ z ∈ U, f' z = f (a * z + b)) {z : ℂ} (hz : z ∈ U) :
    schwarzianHol f' z = a ^ 2 * schwarzianHol f (a * z + b) := by
  have hev : f' =ᶠ[𝓝 z] fun x => f (a * x + b) := Filter.eventually_of_mem (hU.mem_nhds hz) h
  have h1 := hev.deriv
  have h2 := h1.deriv
  have h3 : (fun w => deriv (deriv f') w / deriv f' w) =ᶠ[𝓝 z]
      fun w => deriv (deriv fun x => f (a * x + b)) w / deriv (fun x => f (a * x + b)) w := by
    filter_upwards [h1, h2] with w hw1 hw2
    rw [hw1, hw2]
  rw [← hp_schwarzianHol_affine f ha b z]
  unfold schwarzianHol
  rw [h3.deriv_eq, h2.eq_of_nhds, h1.eq_of_nhds]

/-- Helper for `set_hp_invariance`: for `f` conformal on `ℍ`, `λ_f` is the measure with the
measurable density `y³ |S_hol f|²` (`schwarzian = schwarzianHol` on `ℍ`). -/
theorem hpv_mass_upper {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f upperHalf Ω) :
    hpSchwarzCarleson f = hpWeight ((volume.restrict upperHalf).withDensity
      fun z => ENNReal.ofReal (z.im ^ 2 * ‖schwarzianHol f z‖ ^ 2)) := by
  have hU : IsOpen upperHalf := isOpen_upperHalf
  unfold hpSchwarzCarleson hpSchwarzMass
  congr 1
  refine withDensity_congr_ae ((ae_restrict_iff' hU.measurableSet).mpr
    (Filter.Eventually.of_forall fun z hz => ?_))
  dsimp only
  rw [schwarzian_of_analyticAt (hf.1.analyticAt (hU.mem_nhds hz))]

/-- Helper for `set_hp_invariance`: for `g` conformal on `𝕃`, `λ_-` is the measure with the
measurable density `y³ |S_hol g(z̄)|²`. -/
theorem hpv_mass_lower {Ω : Set ℂ} {g : ℂ → ℂ} (hg : IsConformalOnto g lowerHalf Ω) :
    hpSchwarzCarlesonLower g = hpWeight ((volume.restrict upperHalf).withDensity
      fun z => ENNReal.ofReal (z.im ^ 2 * ‖schwarzianHol g (conj z)‖ ^ 2)) := by
  have hU : IsOpen upperHalf := isOpen_upperHalf
  have hlow : IsOpen lowerHalf := isOpen_lt Complex.continuous_im continuous_const
  unfold hpSchwarzCarlesonLower hpSchwarzMassLower
  congr 1
  refine withDensity_congr_ae ((ae_restrict_iff' hU.measurableSet).mpr
    (Filter.Eventually.of_forall fun z hz => ?_))
  have hzc : conj z ∈ lowerHalf := by
    show (conj z).im < 0
    have : 0 < z.im := hz
    simp only [Complex.conj_im]
    linarith
  dsimp only
  rw [schwarzian_of_analyticAt (hg.1.analyticAt (hlow.mem_nhds hzc))]

/-- Helper for `set_hp_invariance`: if `Ψ = a⁴ Φ ∘ A` on `ℍ`, `A z = a z + b` (`a > 0`, `b` real),
then `y³Ψ dA (Q(c, ℓ)) = a⁻¹ · y³Φ dA (Q(a c + b, a ℓ))` (change of variables `w = A z`,
`Im w = a Im z`, `dA(w) = a² dA(z)`, `A(Q(c, ℓ)) = Q(a c + b, a ℓ)`). -/
theorem hpv_box_affine {Φ Ψ : ℂ → ℝ} (hΦ : Measurable Φ) (hΨm : Measurable Ψ) {a b : ℝ}
    (ha : 0 < a) (hΨ : ∀ z ∈ upperHalf, Ψ z = a ^ 4 * Φ ((a : ℂ) * z + b)) (c ℓ : ℝ) :
    hpWeight ((volume.restrict upperHalf).withDensity
        fun z => ENNReal.ofReal (z.im ^ 2 * Ψ z)) (hpBox c ℓ) =
      ENNReal.ofReal a⁻¹ * hpWeight ((volume.restrict upperHalf).withDensity
        fun z => ENNReal.ofReal (z.im ^ 2 * Φ z)) (hpBox (a * c + b) (a * ℓ)) := by
  have hU : IsOpen upperHalf := isOpen_upperHalf
  have hAm : Measurable fun z : ℂ => (a : ℂ) * z + b := (measurable_const.mul measurable_id).add_const _
  have hAim : ∀ z : ℂ, ((a : ℂ) * z + b).im = a * z.im := fun z => by simp
  have hAU : ∀ z : ℂ, (a : ℂ) * z + b ∈ upperHalf ↔ z ∈ upperHalf := by
    intro z
    show 0 < ((a : ℂ) * z + b).im ↔ 0 < z.im
    rw [hAim]
    exact ⟨fun h => pos_of_mul_pos_right h ha.le, fun h => mul_pos ha h⟩
  -- `λ(T) = ∫_{T ∩ ℍ} y³ G` for a measurable density `G`
  have happ : ∀ G : ℂ → ℝ, Measurable G → ∀ T : Set ℂ, MeasurableSet T →
      hpWeight ((volume.restrict upperHalf).withDensity
        fun z => ENNReal.ofReal (z.im ^ 2 * G z)) T =
      ∫⁻ z, (T ∩ upperHalf).indicator
        (fun z => ENNReal.ofReal (z.im ^ 2 * G z) * ENNReal.ofReal z.im) z := by
    intro G hG T hT
    unfold hpWeight
    rw [withDensity_apply _ hT, restrict_withDensity hT,
      lintegral_withDensity_eq_lintegral_mul _
        (show Measurable fun z : ℂ => ENNReal.ofReal (z.im ^ 2 * G z) from
          ((Complex.measurable_im.pow_const 2).mul hG).ennreal_ofReal)
        Complex.measurable_im.ennreal_ofReal,
      Measure.restrict_restrict hT, ← lintegral_indicator (hT.inter hU.measurableSet)]
    rfl
  have hB := hp_measurableSet_box (a * c + b) (a * ℓ)
  have hTU := hB.inter hU.measurableSet
  have hmΦ : Measurable fun w : ℂ => ENNReal.ofReal (w.im ^ 2 * Φ w) * ENNReal.ofReal w.im :=
    ((Complex.measurable_im.pow_const 2).mul hΦ).ennreal_ofReal.mul
      Complex.measurable_im.ennreal_ofReal
  have hpt : ∀ z, ((fun z : ℂ => (a : ℂ) * z + b) ⁻¹' hpBox (a * c + b) (a * ℓ) ∩ upperHalf).indicator
      (fun z => ENNReal.ofReal (z.im ^ 2 * Ψ z) * ENNReal.ofReal z.im) z =
      (hpBox (a * c + b) (a * ℓ) ∩ upperHalf).indicator
        (fun w => ENNReal.ofReal a * (ENNReal.ofReal (w.im ^ 2 * Φ w) * ENNReal.ofReal w.im))
        ((a : ℂ) * z + b) := by
    intro z
    by_cases hz : z ∈ (fun z : ℂ => (a : ℂ) * z + b) ⁻¹' hpBox (a * c + b) (a * ℓ) ∩ upperHalf
    · have hz' : (a : ℂ) * z + b ∈ hpBox (a * c + b) (a * ℓ) ∩ upperHalf :=
        ⟨hz.1, (hAU z).mpr hz.2⟩
      rw [indicator_of_mem hz, indicator_of_mem hz']
      have hy : 0 < z.im := hz.2
      show ENNReal.ofReal (z.im ^ 2 * Ψ z) * ENNReal.ofReal z.im =
        ENNReal.ofReal a * (ENNReal.ofReal (((a : ℂ) * z + b).im ^ 2 * Φ ((a : ℂ) * z + b)) *
          ENNReal.ofReal ((a : ℂ) * z + b).im)
      rw [hAim, hΨ z hz.2, ← ENNReal.ofReal_mul' hy.le, ← ENNReal.ofReal_mul' (mul_pos ha hy).le,
        ← ENNReal.ofReal_mul ha.le]
      congr 1
      ring
    · have hz' : (a : ℂ) * z + b ∉ hpBox (a * c + b) (a * ℓ) ∩ upperHalf :=
        fun h => hz ⟨h.1, (hAU z).mp h.2⟩
      rw [indicator_of_notMem hz, indicator_of_notMem hz']
  rw [hp_box_affine (β := b) ha c ℓ, happ Ψ hΨm _ (hAm hB), happ Φ hΦ _ hB]
  simp_rw [hpt]
  rw [← lintegral_map ((hmΦ.const_mul _).indicator hTU) hAm, hp_map_affine_volume ha,
    lintegral_smul_measure, lintegral_indicator hTU, lintegral_indicator hTU,
    lintegral_const_mul _ hmΦ, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [pow_two, mul_inv, mul_assoc, inv_mul_cancel₀ ha.ne', mul_one]

/-- Helper for `set_hp_invariance` (conjuncts 7–8): under `Ψ = a⁴ Φ ∘ A` on `ℍ`, `ε_Ψ(r) = ε_Φ(a r)`
and the Carleson norms agree (`hpv_box_affine`), so `CM₀(ℍ)` holds for both or for neither. -/
theorem hpv_vc_affine {Φ Ψ : ℂ → ℝ} (hΦ : Measurable Φ) (hΨm : Measurable Ψ) {a b : ℝ}
    (ha : 0 < a) (hΨ : ∀ z ∈ upperHalf, Ψ z = a ^ 4 * Φ ((a : ℂ) * z + b)) :
    IsHPVanishingCarleson (hpWeight ((volume.restrict upperHalf).withDensity
        fun z => ENNReal.ofReal (z.im ^ 2 * Φ z))) ↔
      IsHPVanishingCarleson (hpWeight ((volume.restrict upperHalf).withDensity
        fun z => ENNReal.ofReal (z.im ^ 2 * Ψ z))) := by
  -- the statement only depends on the box identity of `hpv_box_affine`
  have key : ∀ μ ν : Measure ℂ,
      (∀ c ℓ : ℝ, ν (hpBox c ℓ) = ENNReal.ofReal a⁻¹ * μ (hpBox (a * c + b) (a * ℓ))) →
      (IsHPVanishingCarleson μ ↔ IsHPVanishingCarleson ν) := by
    intro μ ν hbox
    have hratio : ∀ c ℓ : ℝ, ν (hpBox c ℓ) / ENNReal.ofReal ℓ =
        μ (hpBox (a * c + b) (a * ℓ)) / ENNReal.ofReal (a * ℓ) := by
      intro c ℓ
      rw [hbox, ENNReal.ofReal_mul ha.le, div_eq_mul_inv, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top),
        ENNReal.ofReal_inv_of_pos ha]
      ring
    have hc : ∀ c' : ℝ, a * ((c' - b) / a) + b = c' := fun c' => by
      rw [mul_div_cancel₀ _ ha.ne', sub_add_cancel]
    have hl : ∀ ℓ' : ℝ, a * (ℓ' / a) = ℓ' := fun ℓ' => mul_div_cancel₀ _ ha.ne'
    have hCM : hpCMNorm ν = hpCMNorm μ := by
      unfold hpCMNorm
      apply le_antisymm
      · refine iSup_le fun c => iSup_le fun ℓ => iSup_le fun hℓ => ?_
        rw [hratio c ℓ]
        exact le_iSup_of_le (a * c + b) (le_iSup_of_le (a * ℓ)
          (le_iSup_of_le (by positivity) le_rfl))
      · refine iSup_le fun c => iSup_le fun ℓ => iSup_le fun hℓ => ?_
        refine le_iSup_of_le ((c - b) / a) (le_iSup_of_le (ℓ / a)
          (le_iSup_of_le (by positivity) ?_))
        rw [hratio, hc, hl]
    have hEps : ∀ r : ℝ, 0 < r → hpEps ν r = hpEps μ (a * r) := by
      intro r hr
      unfold hpEps
      apply le_antisymm
      · refine iSup_le fun c => iSup_le fun ℓ => iSup_le fun hℓ => iSup_le fun hℓr => ?_
        rw [hratio c ℓ]
        exact le_iSup_of_le (a * c + b) (le_iSup_of_le (a * ℓ)
          (le_iSup_of_le (by positivity) (le_iSup_of_le (by nlinarith) le_rfl)))
      · refine iSup_le fun c => iSup_le fun ℓ => iSup_le fun hℓ => iSup_le fun hℓr => ?_
        refine le_iSup_of_le ((c - b) / a) (le_iSup_of_le (ℓ / a)
          (le_iSup_of_le (by positivity) (le_iSup_of_le ?_ ?_)))
        · rw [div_le_iff₀ ha]
          linarith
        · rw [hratio, hc, hl]
    have hlim : ∀ k : ℝ, 0 < k → Tendsto (fun r : ℝ => k * r) (𝓝[>] 0) (𝓝[>] 0) := by
      intro k hk
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun r : ℝ => k * r) (𝓝 0) (𝓝 (k * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rw [mul_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact mul_pos hk hr
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by show hpCMNorm _ ≠ ⊤; rw [hCM]; exact h1, ?_⟩
      refine (h2.comp (hlim a ha)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (hEps r hr).symm
    · rintro ⟨h1, h2⟩
      refine ⟨by show hpCMNorm _ ≠ ⊤; rw [← hCM]; exact h1, ?_⟩
      refine (h2.comp (hlim a⁻¹ (inv_pos.2 ha))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      show hpEps ν (a⁻¹ * r) = hpEps μ r
      rw [hEps _ (mul_pos (inv_pos.2 ha) hr), mul_inv_cancel_left₀ ha.ne']
  exact key _ _ (hpv_box_affine hΦ hΨm ha hΨ)

/-- Convention `set:hp`, `sec11-halfplane.tex:758–768`: another choice of `f, g` replaces `w` by
`B₁⁻¹ ∘ w ∘ A₁` with increasing real affine `A₁, B₁`; this does not affect `SQS`, `SS`, uniform
continuity of `w` and `w⁻¹`, nor the conditions `λ_f ∈ CM₀(ℍ)`, `λ_- ∈ CM₀(ℍ)`. -/
theorem set_hp_invariance {Ω Ωs : Set ℂ} {K K' : ℝ} {f g f' g' : ℂ → ℂ} {w w' : ℝ ≃ₜ ℝ}
    (hs : IsHPSetting Ω Ωs K f g w) (hs' : IsHPSetting Ω Ωs K' f' g' w') :
    (∃ a₁ b₁ a₂ b₂ : ℝ, 0 < a₁ ∧ 0 < a₂ ∧ ∀ x, a₂ * w' x + b₂ = w (a₁ * x + b₁)) ∧
      (IsSQS w ↔ IsSQS w') ∧ (IsSS w ↔ IsSS w') ∧ (IsSS w.symm ↔ IsSS w'.symm) ∧
      (UniformContinuous w ↔ UniformContinuous w') ∧
      (UniformContinuous w.symm ↔ UniformContinuous w'.symm) ∧
      (IsHPVanishingCarleson (hpSchwarzCarleson f) ↔ IsHPVanishingCarleson (hpSchwarzCarleson f')) ∧
      (IsHPVanishingCarleson (hpSchwarzCarlesonLower g) ↔
        IsHPVanishingCarleson (hpSchwarzCarlesonLower g')) := by
  obtain ⟨a₁, b₁, a₂, b₂, ha₁, ha₂, hff, hgg, hw⟩ := hpv_welding_affine hs hs'
  have e1 : (⇑w' : ℝ → ℝ) = fun x => (w (a₁ * x + b₁) - b₂) / a₂ := by
    funext x
    rw [← hw x]
    field_simp
    ring
  have e2 : (⇑w : ℝ → ℝ) = fun y => (w' (a₁⁻¹ * y + -b₁ / a₁) - -b₂ / a₂) / a₂⁻¹ := by
    funext y
    have h1 := hw (a₁⁻¹ * y + -b₁ / a₁)
    rw [show a₁ * (a₁⁻¹ * y + -b₁ / a₁) + b₁ = y by field_simp; ring] at h1
    rw [← h1]
    field_simp
    ring
  have e3 : (⇑w'.symm : ℝ → ℝ) = fun y => (w.symm (a₂ * y + b₂) - b₁) / a₁ := by
    funext y
    have h1 := hw (w'.symm y)
    rw [Homeomorph.apply_symm_apply] at h1
    rw [h1, Homeomorph.symm_apply_apply]
    field_simp
    ring
  have e4 : (⇑w.symm : ℝ → ℝ) =
      fun x => (w'.symm (a₂⁻¹ * x + -b₂ / a₂) - -b₁ / a₁) / a₁⁻¹ := by
    funext x
    have h1 := congrFun e3 (a₂⁻¹ * x + -b₂ / a₂)
    rw [show a₂ * (a₂⁻¹ * x + -b₂ / a₂) + b₂ = x by field_simp; ring] at h1
    rw [h1]
    field_simp
    ring
  have P := hpv_real_affine (h := w) (b := b₁) (d := b₂) ha₁ ha₂
  have Q := hpv_real_affine (h := w') (b := -b₁ / a₁) (d := -b₂ / a₂) (inv_pos.2 ha₁)
    (inv_pos.2 ha₂)
  have P' := hpv_real_affine (h := w.symm) (b := b₂) (d := b₁) ha₂ ha₁
  have Q' := hpv_real_affine (h := w'.symm) (b := -b₂ / a₂) (d := -b₁ / a₁) (inv_pos.2 ha₂)
    (inv_pos.2 ha₁)
  have hmU : ∀ F : ℂ → ℂ, Measurable fun z => ‖schwarzianHol F z‖ ^ 2 := fun F =>
    (s02_pullback_measurable_schwarzianHol F).norm.pow_const 2
  have hmL : ∀ F : ℂ → ℂ, Measurable fun z => ‖schwarzianHol F (conj z)‖ ^ 2 := fun F =>
    ((s02_pullback_measurable_schwarzianHol F).comp Complex.continuous_conj.measurable).norm.pow_const 2
  have hsq : ∀ (a : ℝ) (s : ℂ), 0 < a → ‖(a : ℂ) ^ 2 * s‖ ^ 2 = a ^ 4 * ‖s‖ ^ 2 := by
    intro a s ha
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ha.le]
    ring
  refine ⟨⟨a₁, b₁, a₂, b₂, ha₁, ha₂, hw⟩, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩,
    ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
  · rw [e1]; exact P.1 h
  · rw [e2]; exact Q.1 h
  · rw [e1]; exact P.2.1 h
  · rw [e2]; exact Q.2.1 h
  · rw [e3]; exact P'.2.1 h
  · rw [e4]; exact Q'.2.1 h
  · rw [e1]; exact P.2.2 h
  · rw [e2]; exact Q.2.2 h
  · rw [e3]; exact P'.2.2 h
  · rw [e4]; exact Q'.2.2 h
  · rw [hpv_mass_upper hs.2.2.1, hpv_mass_upper hs'.2.2.1]
    refine hpv_vc_affine (hmU f) (hmU f') (b := b₁) ha₁ fun z hz => ?_
    rw [hpv_schwarzianHol_congr isOpen_upperHalf (by exact_mod_cast ha₁.ne') hff hz, hsq _ _ ha₁]
  · rw [hpv_mass_lower hs.2.2.2.1, hpv_mass_lower hs'.2.2.2.1]
    refine hpv_vc_affine (hmL g) (hmL g') (b := b₂) ha₂ fun z hz => ?_
    have hzc : conj z ∈ lowerHalf := by
      show (conj z).im < 0
      have : 0 < z.im := hz
      simp only [Complex.conj_im]
      linarith
    have hU : IsOpen lowerHalf := isOpen_lt Complex.continuous_im continuous_const
    rw [hpv_schwarzianHol_congr hU (by exact_mod_cast ha₂.ne') hgg hzc, hsq _ _ ha₂]
    congr 3
    simp [map_add, map_mul, Complex.conj_ofReal]

/-- Convention `set:hp`, `sec11-halfplane.tex:765`: for `g♯ = J ∘ g ∘ J`,
`S g♯(z) = conj (S g(z̄))`, so `m_- = m_{g♯}` and `λ_- = λ_{g♯}`. -/
theorem set_hp_gsharp {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g lowerHalf) :
    (∀ z ∈ upperHalf, schwarzian (fun w => conj (g (conj w))) z = conj (schwarzian g (conj z))) ∧
      hpSchwarzMassLower g = hpSchwarzMass (fun w => conj (g (conj w))) := by
  have hd1 : deriv (conj ∘ g ∘ conj) = conj ∘ deriv g ∘ conj := deriv_conj_conj
  have hd2 : deriv (deriv (conj ∘ g ∘ conj)) = conj ∘ deriv (deriv g) ∘ conj := by
    rw [hd1, deriv_conj_conj]
  have hq : (fun w => deriv (deriv (conj ∘ g ∘ conj)) w / deriv (conj ∘ g ∘ conj) w) =
      conj ∘ (fun w => deriv (deriv g) w / deriv g w) ∘ conj := by
    rw [hd2, hd1]
    funext w
    simp [map_div₀]
  have hSH : ∀ z, schwarzianHol (conj ∘ g ∘ conj) z = conj (schwarzianHol g (conj z)) := by
    intro z
    unfold schwarzianHol
    rw [hq, deriv_conj_conj, hd2, hd1]
    simp [map_sub, map_mul, map_div₀, map_pow, map_ofNat]
  have hlow : IsOpen lowerHalf := isOpen_lt Complex.continuous_im continuous_const
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hconj : ∀ w ∈ upperHalf, conj w ∈ lowerHalf := fun w hw => by
    show (conj w).im < 0
    have : 0 < w.im := hw
    simp only [Complex.conj_im]
    linarith
  have part1 : ∀ z ∈ upperHalf,
      schwarzian (fun w => conj (g (conj w))) z = conj (schwarzian g (conj z)) := by
    intro z hz
    have hga : AnalyticAt ℂ g (conj z) := hg.analyticAt (hlow.mem_nhds (hconj z hz))
    have hsharpD : DifferentiableOn ℂ (conj ∘ g ∘ conj) upperHalf := fun w hw => by
      have h := ((hg _ (hconj w hw)).differentiableAt (hlow.mem_nhds (hconj w hw))).conj_conj
      rw [Complex.conj_conj] at h
      exact h.differentiableWithinAt
    have hsa : AnalyticAt ℂ (conj ∘ g ∘ conj) z := hsharpD.analyticAt (hU.mem_nhds hz)
    rw [show (fun w => conj (g (conj w))) = conj ∘ g ∘ conj from rfl,
      schwarzian_of_analyticAt hsa, schwarzian_of_analyticAt hga, hSH]
  refine ⟨part1, ?_⟩
  unfold hpSchwarzMassLower hpSchwarzMass
  refine withDensity_congr_ae ((ae_restrict_iff' hU.measurableSet).mpr
    (Filter.Eventually.of_forall fun z hz => ?_))
  simp only [part1 z hz, Complex.norm_conj]

/-- Lemma 11.10 `lem:hp-welding`, `sec11-halfplane.tex:771`: `λ_f ∈ CM₀(ℍ) ⇔ w ∈ SS(ℝ)` and
`λ_- ∈ CM₀(ℍ) ⇔ w⁻¹ ∈ SS(ℝ)`. -/
theorem lem_hp_welding {Ω Ωs : Set ℂ} {K : ℝ} {f g : ℂ → ℂ} {w : ℝ ≃ₜ ℝ}
    (hs : IsHPSetting Ω Ωs K f g w) :
    (IsHPVanishingCarleson (hpSchwarzCarleson f) ↔ IsSS w) ∧
      (IsHPVanishingCarleson (hpSchwarzCarlesonLower g) ↔ IsSS w.symm) := by sorry

/-- `a_n = 12 n² + 10 n` (Proposition `prop:hp-w0`). -/
def hpW0a (n : ℕ) : ℝ := 12 * (n : ℝ) ^ 2 + 10 * n

/-- `c_n = (a_{n-1} + a_n)/2`. -/
def hpW0c (n : ℕ) : ℝ := (hpW0a (n - 1) + hpW0a n) / 2

/-- The block index of `y ≥ 0`: the least `n ≥ 1` with `y ≤ a_n`. -/
def hpW0Block (y : ℝ) : ℕ := sInf {n : ℕ | 1 ≤ n ∧ y ≤ hpW0a n}

/-- The even weight `ω₀(x) = (1 + |x - c_n|)/(12 n)` on `a_{n-1} ≤ |x| ≤ a_n` (11.?)
`eq:hp-omega0`. -/
def hpOmega0 (x : ℝ) : ℝ :=
  (1 + |(|x|) - hpW0c (hpW0Block |x|)|) / (12 * (hpW0Block |x| : ℝ))

/-- `w₀(x) = ∫₀ˣ ω₀`. -/
def hpW0 (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, hpOmega0 t

/-- Helper: `a_{n+1} - a_n = 24 n + 22`. -/
theorem hp_w0a_succ_sub (n : ℕ) : hpW0a (n + 1) - hpW0a n = 24 * n + 22 := by
  unfold hpW0a; push_cast; ring

theorem hp_w0a_strictMono : StrictMono hpW0a :=
  strictMono_nat_of_lt_succ fun n => by
    linarith [hp_w0a_succ_sub n, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem hp_w0a_nonneg (n : ℕ) : 0 ≤ hpW0a n := by unfold hpW0a; positivity

theorem hp_w0a_ge (m : ℕ) : (m : ℝ) ≤ hpW0a m := by
  unfold hpW0a; nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

theorem hp_w0c_succ (n : ℕ) : hpW0c (n + 1) = (hpW0a n + hpW0a (n + 1)) / 2 := by
  simp [hpW0c]

/-- Helper: the defining properties of the block index. -/
theorem hp_w0Block_spec (t : ℝ) :
    1 ≤ hpW0Block t ∧ t ≤ hpW0a (hpW0Block t) ∧
      ∀ k, 1 ≤ k → t ≤ hpW0a k → hpW0Block t ≤ k := by
  have hne : {n : ℕ | 1 ≤ n ∧ t ≤ hpW0a n}.Nonempty := by
    refine ⟨⌈t⌉₊ + 1, by omega, ?_⟩
    have h1 := Nat.le_ceil t
    have h2 := hp_w0a_ge (⌈t⌉₊ + 1)
    push_cast at h2
    linarith
  have hm := Nat.sInf_mem hne
  exact ⟨hm.1, hm.2, fun k hk1 hk2 => Nat.sInf_le ⟨hk1, hk2⟩⟩

theorem hp_w0_block_exists {t : ℝ} (ht : 0 ≤ t) :
    ∃ n : ℕ, hpW0a n ≤ t ∧ t ≤ hpW0a (n + 1) := by
  obtain ⟨h1, h2, h3⟩ := hp_w0Block_spec t
  obtain ⟨n, hn⟩ : ∃ n, hpW0Block t = n + 1 := ⟨hpW0Block t - 1, by omega⟩
  refine ⟨n, ?_, by rw [← hn]; exact h2⟩
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simpa [hpW0a] using ht
  · by_contra hlt
    have := h3 n hpos (not_le.mp hlt).le
    omega

/-- Helper: on the block `[a_n, a_{n+1}]`, `ω₀ t = (1 + |t - c_{n+1}|)/(12(n+1))`. -/
theorem hp_omega0_block {n : ℕ} {t : ℝ} (h1 : hpW0a n ≤ t) (h2 : t ≤ hpW0a (n + 1)) :
    hpOmega0 t = (1 + |t - hpW0c (n + 1)|) / (12 * ((n : ℝ) + 1)) := by
  have ht : 0 ≤ t := (hp_w0a_nonneg n).trans h1
  obtain ⟨b1, b2, b3⟩ := hp_w0Block_spec t
  have hle := b3 (n + 1) (by omega) h2
  unfold hpOmega0
  rw [abs_of_nonneg ht]
  rcases Nat.lt_or_ge (hpW0Block t) (n + 1) with hlt | hge
  · have hm : hpW0a (hpW0Block t) ≤ hpW0a n := hp_w0a_strictMono.monotone (by omega)
    have heq : hpW0a (hpW0Block t) = hpW0a n := le_antisymm hm (h1.trans b2)
    have hB : hpW0Block t = n := hp_w0a_strictMono.injective heq
    have htn : t = hpW0a n := le_antisymm (hB ▸ b2) h1
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [hB, htn, hp_w0c_succ, hp_w0c_succ]
    have e1 : hpW0a (j + 1) - (hpW0a j + hpW0a (j + 1)) / 2 = 12 * j + 11 := by
      unfold hpW0a; push_cast; ring
    have e2 : hpW0a (j + 1) - (hpW0a (j + 1) + hpW0a (j + 1 + 1)) / 2 = -(12 * j + 23) := by
      unfold hpW0a; push_cast; ring
    rw [e1, e2, abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    push_cast
    field_simp
    ring
  · rw [show hpW0Block t = n + 1 by omega]
    push_cast
    ring

theorem hp_omega0_neg (x : ℝ) : hpOmega0 (-x) = hpOmega0 x := by simp [hpOmega0, abs_neg]

theorem hp_omega0_abs (x : ℝ) : hpOmega0 |x| = hpOmega0 x := by simp [hpOmega0, abs_abs]

theorem hp_omega0_le_one (x : ℝ) : hpOmega0 x ≤ 1 := by
  rw [← hp_omega0_abs]
  obtain ⟨n, h1, h2⟩ := hp_w0_block_exists (abs_nonneg x)
  rw [hp_omega0_block h1 h2, div_le_one (by positivity)]
  have hd := hp_w0a_succ_sub n
  have hc := hp_w0c_succ n
  have : |(|x|) - hpW0c (n + 1)| ≤ 12 * (n : ℝ) + 11 := by
    rw [abs_le]; constructor <;> linarith
  linarith

theorem hp_omega0_zero : hpOmega0 0 = 1 := by
  rw [hp_omega0_block (n := 0) (by simp [hpW0a]) (hp_w0a_nonneg 1), hp_w0c_succ]
  norm_num [hpW0a]

/-- Helper: `(y |y|)' = 2 |y|`. -/
theorem hp_hasDerivAt_mul_abs (x : ℝ) : HasDerivAt (fun y : ℝ => y * |y|) (2 * |x|) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have : (fun y : ℝ => y * |y|) =ᶠ[𝓝 x] fun y => -(y ^ 2) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      rw [abs_of_neg hy]; ring
    rw [abs_of_neg hx]
    convert ((hasDerivAt_pow 2 x).neg).congr_of_eventuallyEq this using 1
    ring
  · rw [hasDerivAt_iff_isLittleO_nhds_zero]
    have ht : Tendsto (fun h : ℝ => |h|) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ))
    have h1 : (fun h : ℝ => |h|) =o[𝓝 0] fun _ => (1 : ℝ) := (Asymptotics.isLittleO_one_iff ℝ).mpr ht
    have := (Asymptotics.isBigO_refl (fun h : ℝ => h) (𝓝 0)).mul_isLittleO h1
    simpa using this
  · have : (fun y : ℝ => y * |y|) =ᶠ[𝓝 x] fun y => y ^ 2 := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      rw [abs_of_pos hy]; ring
    rw [abs_of_pos hx]
    convert (hasDerivAt_pow 2 x).congr_of_eventuallyEq this using 1
    ring

/-- Helper: integral of `ω₀` over a subinterval of the block `[a_n, a_{n+1}]`. -/
theorem hp_omega0_integral_block {n : ℕ} {p q : ℝ} (hp : hpW0a n ≤ p) (hpq : p ≤ q)
    (hq : q ≤ hpW0a (n + 1)) :
    IntervalIntegrable hpOmega0 volume p q ∧
      ∫ y in p..q, hpOmega0 y =
        ((q - hpW0c (n + 1)) + (q - hpW0c (n + 1)) * |q - hpW0c (n + 1)| / 2) /
            (12 * ((n : ℝ) + 1)) -
          ((p - hpW0c (n + 1)) + (p - hpW0c (n + 1)) * |p - hpW0c (n + 1)| / 2) /
            (12 * ((n : ℝ) + 1)) := by
  set c := hpW0c (n + 1)
  set D : ℝ := 12 * ((n : ℝ) + 1)
  have heq : EqOn hpOmega0 (fun y => (1 + |y - c|) / D) (uIcc p q) := by
    intro y hy
    rw [uIcc_of_le hpq] at hy
    exact hp_omega0_block (hp.trans hy.1) (hy.2.trans hq)
  have hcont : Continuous fun y => (1 + |y - c|) / D := by fun_prop
  have hderiv : ∀ x ∈ uIcc p q, HasDerivAt (fun y => ((y - c) + (y - c) * |y - c| / 2) / D)
      ((1 + |x - c|) / D) x := by
    intro x _
    have h1 := (hp_hasDerivAt_mul_abs (x - c)).comp x ((hasDerivAt_id x).sub_const c)
    have h2 := (((hasDerivAt_id x).sub_const c).add (h1.div_const 2)).div_const D
    convert h2 using 1
    · funext y; simp [Function.comp]
    · ring
  refine ⟨((hcont.integrableOn_uIcc (μ := volume)).congr_fun heq.symm measurableSet_uIcc).intervalIntegrable,
    ?_⟩
  rw [intervalIntegral.integral_congr heq]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable p q)

theorem hp_w0_alg_sb {u v w : ℝ} (huw : u ≤ w) (hwv : w ≤ v) :
    (1 + |w|) * (v - u) ≤ 4 * ((v + v * |v| / 2) - (u + u * |u| / 2)) := by
  rcases le_total 0 u with hu | hu <;> rcases le_total 0 v with hv | hv <;>
    rcases le_total 0 w with hw | hw
  all_goals
    first | rw [abs_of_nonneg hu] | rw [abs_of_nonpos hu]
    first | rw [abs_of_nonneg hv] | rw [abs_of_nonpos hv]
    first | rw [abs_of_nonneg hw] | rw [abs_of_nonpos hw]
    nlinarith [mul_nonneg (sub_nonneg.2 hwv) (sub_nonneg.2 (huw.trans hwv)),
      mul_nonneg (sub_nonneg.2 huw) (sub_nonneg.2 (huw.trans hwv)), sq_nonneg (u + v),
      sq_nonneg (u - v), sq_nonneg u, sq_nonneg v]

theorem hp_w0_alg_left {L u v : ℝ} (hL : 0 ≤ L) (hu : u = -L) (h1 : u ≤ v) (h2 : v ≤ L) :
    (v - u) * (L + 1) ≤ 4 * ((v + v * |v| / 2) - (u + u * |u| / 2)) := by
  subst hu
  rw [abs_neg, abs_of_nonneg hL]
  rcases le_total 0 v with hv | hv
  · rw [abs_of_nonneg hv]
    nlinarith [sq_nonneg (L - v), mul_nonneg hv hL, sq_nonneg v, sq_nonneg L]
  · rw [abs_of_nonpos hv]
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (by linarith : (0 : ℝ) ≤ L - 2 * v)]

theorem hp_w0_alg_right {L u v : ℝ} (hL : 0 ≤ L) (hv : v = L) (h1 : -L ≤ u) (h2 : u ≤ v) :
    (v - u) * (L + 1) ≤ 4 * ((v + v * |v| / 2) - (u + u * |u| / 2)) := by
  subst hv
  rw [abs_of_nonneg hL]
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (by linarith : (0 : ℝ) ≤ v + 2 * u)]
  · rw [abs_of_nonpos hu]
    nlinarith [sq_nonneg (v + u), sq_nonneg u, sq_nonneg v]

/-- Helper: `ω₀` on a piece of a block starting at its left end has mean `≥ 1/4`. -/
theorem hp_omega0_left {n : ℕ} {β : ℝ} (h1 : hpW0a n ≤ β) (h2 : β ≤ hpW0a (n + 1)) :
    IntervalIntegrable hpOmega0 volume (hpW0a n) β ∧
      (β - hpW0a n) / 4 ≤ ∫ y in hpW0a n..β, hpOmega0 y := by
  obtain ⟨hI, hv⟩ := hp_omega0_integral_block le_rfl h1 h2
  refine ⟨hI, ?_⟩
  have hd := hp_w0a_succ_sub n
  have hc := hp_w0c_succ n
  have := hp_w0_alg_left (L := 12 * n + 11) (u := hpW0a n - hpW0c (n + 1))
    (v := β - hpW0c (n + 1)) (by positivity) (by linarith) (by linarith) (by linarith)
  rw [hv, ← sub_div, le_div_iff₀ (by positivity)]
  linarith

/-- Helper: `ω₀` on a piece of a block ending at its right end has mean `≥ 1/4`. -/
theorem hp_omega0_right {n : ℕ} {α : ℝ} (h1 : hpW0a n ≤ α) (h2 : α ≤ hpW0a (n + 1)) :
    IntervalIntegrable hpOmega0 volume α (hpW0a (n + 1)) ∧
      (hpW0a (n + 1) - α) / 4 ≤ ∫ y in α..hpW0a (n + 1), hpOmega0 y := by
  obtain ⟨hI, hv⟩ := hp_omega0_integral_block h1 h2 le_rfl
  refine ⟨hI, ?_⟩
  have hd := hp_w0a_succ_sub n
  have hc := hp_w0c_succ n
  have := hp_w0_alg_right (L := 12 * n + 11) (u := α - hpW0c (n + 1))
    (v := hpW0a (n + 1) - hpW0c (n + 1)) (by positivity) (by linarith) (by linarith)
    (by linarith)
  rw [hv, ← sub_div, le_div_iff₀ (by positivity)]
  linarith

/-- Helper: the `A_∞` bound inside one block. -/
theorem hp_omega0_sb {n : ℕ} {α x β : ℝ} (h1 : hpW0a n ≤ α) (hαx : α ≤ x) (hxβ : x ≤ β)
    (h2 : β ≤ hpW0a (n + 1)) :
    IntervalIntegrable hpOmega0 volume α β ∧
      (β - α) * hpOmega0 x ≤ 4 * ∫ y in α..β, hpOmega0 y := by
  obtain ⟨hI, hv⟩ := hp_omega0_integral_block h1 (hαx.trans hxβ) h2
  refine ⟨hI, ?_⟩
  have := hp_w0_alg_sb (u := α - hpW0c (n + 1)) (v := β - hpW0c (n + 1))
    (w := x - hpW0c (n + 1)) (by linarith) (by linarith)
  rw [hv, hp_omega0_block (h1.trans hαx) (hxβ.trans h2), ← sub_div, mul_div_assoc',
    mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
  linarith

theorem hp_omega0_fwd (N : ℕ) : ∀ k : ℕ, ∀ β : ℝ, hpW0a k ≤ β → β ≤ hpW0a (k + N + 1) →
    IntervalIntegrable hpOmega0 volume (hpW0a k) β ∧
      (β - hpW0a k) / 4 ≤ ∫ y in hpW0a k..β, hpOmega0 y := by
  induction N with
  | zero => exact fun k β h1 h2 => hp_omega0_left h1 h2
  | succ N ih =>
    intro k β h1 h2
    rcases le_total β (hpW0a (k + 1)) with hb | hb
    · exact hp_omega0_left h1 hb
    · obtain ⟨i1, j1⟩ :=
        hp_omega0_left (n := k) (hp_w0a_strictMono.monotone (Nat.le_succ k)) le_rfl
      obtain ⟨i2, j2⟩ :=
        ih (k + 1) β hb (by rwa [show k + 1 + N + 1 = k + (N + 1) + 1 by omega])
      refine ⟨i1.trans i2, ?_⟩
      rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
      linarith

theorem hp_omega0_fwd_all (k : ℕ) {β : ℝ} (h1 : hpW0a k ≤ β) :
    IntervalIntegrable hpOmega0 volume (hpW0a k) β ∧
      (β - hpW0a k) / 4 ≤ ∫ y in hpW0a k..β, hpOmega0 y := by
  refine hp_omega0_fwd ⌈β⌉₊ k β h1 ?_
  have h2 := hp_w0a_ge (k + ⌈β⌉₊ + 1)
  have h3 := Nat.le_ceil β
  push_cast at h2
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- Helper: the `A_∞` bound for intervals in `[0, ∞)`. -/
theorem hp_omega0_nonneg_interval {α x β : ℝ} (hα : 0 ≤ α) (hαx : α ≤ x) (hxβ : x ≤ β) :
    IntervalIntegrable hpOmega0 volume α β ∧
      (β - α) * hpOmega0 x ≤ 4 * ∫ y in α..β, hpOmega0 y := by
  obtain ⟨n, h1, h2⟩ := hp_w0_block_exists hα
  rcases le_total β (hpW0a (n + 1)) with hβ | hβ
  · exact hp_omega0_sb h1 hαx hxβ hβ
  · obtain ⟨i1, j1⟩ := hp_omega0_right h1 h2
    obtain ⟨i2, j2⟩ := hp_omega0_fwd_all (n + 1) hβ
    refine ⟨i1.trans i2, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
    nlinarith [mul_le_mul_of_nonneg_left (hp_omega0_le_one x) (sub_nonneg.2 (hαx.trans hxβ))]

/-- (11.?) `eq:hp-A-infty`, `sec11-halfplane.tex:859`: `sup_I ω₀ ≤ 4 |I|⁻¹ ∫_I ω₀`. -/
theorem eq_hp_A_infty {a b : ℝ} (hab : a < b) {x : ℝ} (hx : x ∈ Icc a b) :
    hpOmega0 x ≤ 4 * intervalMean hpOmega0 a b := by
  suffices h : (b - a) * hpOmega0 x ≤ 4 * ∫ y in a..b, hpOmega0 y by
    have hba : 0 < b - a := sub_pos.2 hab
    unfold intervalMean
    rw [show 4 * ((b - a)⁻¹ * ∫ y in a..b, hpOmega0 y) = (4 * ∫ y in a..b, hpOmega0 y) / (b - a)
      by ring, le_div_iff₀ hba]
    linarith
  have hrefl : ∀ p q : ℝ, ∫ y in p..q, hpOmega0 y = ∫ y in -q..-p, hpOmega0 y := fun p q => by
    rw [← intervalIntegral.integral_comp_neg]; simp_rw [hp_omega0_neg]
  rcases le_total 0 a with ha | ha
  · exact (hp_omega0_nonneg_interval ha hx.1 hx.2).2
  rcases le_total b 0 with hb | hb
  · rw [hrefl, ← hp_omega0_neg x]
    have := (hp_omega0_nonneg_interval (neg_nonneg.2 hb) (neg_le_neg hx.2) (neg_le_neg hx.1)).2
    linarith
  obtain ⟨i1, j1⟩ := hp_omega0_nonneg_interval (le_refl 0) (le_refl 0) (neg_nonneg.2 ha)
  obtain ⟨i2, j2⟩ := hp_omega0_nonneg_interval (le_refl 0) (le_refl 0) hb
  have i1' : IntervalIntegrable hpOmega0 volume a 0 := by
    have := i1.comp_sub_left 0
    simpa [hp_omega0_neg] using this.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals i1' i2, hrefl a 0, neg_zero]
  rw [hp_omega0_zero] at j1 j2
  rcases le_total 0 x with hx0 | hx0
  · have j3 := (hp_omega0_nonneg_interval le_rfl hx0 hx.2).2
    nlinarith [mul_le_mul_of_nonneg_left (hp_omega0_le_one x) (neg_nonneg.2 ha)]
  · have j3 := (hp_omega0_nonneg_interval le_rfl (neg_nonneg.2 hx0) (neg_le_neg hx.1)).2
    rw [hp_omega0_neg] at j3
    nlinarith [mul_le_mul_of_nonneg_left (hp_omega0_le_one x) hb]


/-- Helper: `ω₀ > 0`. -/
theorem s11_w0_pos (x : ℝ) : 0 < hpOmega0 x := by
  rw [← hp_omega0_abs]
  obtain ⟨n, h1, h2⟩ := hp_w0_block_exists (abs_nonneg x)
  rw [hp_omega0_block h1 h2]
  positivity

/-- Helper: `ω₀` is interval integrable on every interval. -/
theorem s11_w0_ii (a b : ℝ) : IntervalIntegrable hpOmega0 volume a b := by
  set R := |a| + |b| with hR
  have hR0 : 0 ≤ R := by positivity
  have i2 : IntervalIntegrable hpOmega0 volume 0 R :=
    (hp_omega0_nonneg_interval le_rfl le_rfl hR0).1
  have i1 : IntervalIntegrable hpOmega0 volume (-R) 0 := by
    have := i2.comp_sub_left 0
    simpa [hp_omega0_neg] using this.symm
  have ha : a ∈ uIcc (-R) R := by
    rw [uIcc_of_le (by linarith)]
    exact abs_le.1 (by linarith [abs_nonneg b])
  have hb : b ∈ uIcc (-R) R := by
    rw [uIcc_of_le (by linarith)]
    exact abs_le.1 (by linarith [abs_nonneg a])
  exact (i1.trans i2).mono_set (uIcc_subset_uIcc ha hb)

/-- Helper: `ω₀` is locally integrable. -/
theorem s11_w0_locInt : LocallyIntegrable hpOmega0 volume := fun x =>
  ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith),
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).1 (s11_w0_ii _ _)⟩

/-- Helper: `w₀(y) - w₀(x) = ∫_x^y ω₀`. -/
theorem s11_w0_sub (x y : ℝ) : hpW0 y - hpW0 x = ∫ t in x..y, hpOmega0 t := by
  unfold hpW0
  exact intervalIntegral.integral_interval_sub_left (s11_w0_ii 0 y) (s11_w0_ii 0 x)

/-- Helper: `w₀` is odd. -/
theorem s11_w0_odd (x : ℝ) : hpW0 (-x) = -hpW0 x := by
  unfold hpW0
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := x) hpOmega0
  simp only [hp_omega0_neg, neg_zero] at h
  rw [intervalIntegral.integral_symm, ← h]

theorem s11_w0_strictMono : StrictMono hpW0 := fun x y hxy => by
  have h := s11_w0_sub x y
  have hpos : 0 < ∫ t in x..y, hpOmega0 t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (s11_w0_ii x y) (fun t _ => s11_w0_pos t) hxy
  linarith

theorem s11_w0_continuous : Continuous hpW0 :=
  intervalIntegral.continuous_primitive s11_w0_ii 0

/-- Helper: `w₀(x) ≥ x/4` for `x ≥ 0`. -/
theorem s11_w0_ge {x : ℝ} (hx : 0 ≤ x) : x / 4 ≤ hpW0 x := by
  have := (hp_omega0_fwd_all 0 (show hpW0a 0 ≤ x by simpa [hpW0a] using hx)).2
  simpa [hpW0a, hpW0] using this

/-- Helper (W1): `w₀` is a homeomorphism of `ℝ`. -/
theorem s11_w0_homeo : ∃ w₀ : ℝ ≃ₜ ℝ, ∀ x, w₀ x = hpW0 x := by
  have hs : Function.Surjective hpW0 := by
    refine s11_w0_continuous.surjective ?_ ?_
    · exact tendsto_atTop_mono' atTop ((eventually_ge_atTop 0).mono fun x hx => s11_w0_ge hx)
        (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 4))
    · refine tendsto_atBot_mono' atBot ((eventually_le_atBot 0).mono fun x hx => ?_)
        (tendsto_id.atBot_div_const (by norm_num : (0 : ℝ) < 4))
      have := s11_w0_ge (neg_nonneg.2 hx)
      rw [s11_w0_odd] at this
      show hpW0 x ≤ x / 4
      linarith
  exact ⟨(s11_w0_strictMono.orderIsoOfSurjective _ hs).toHomeomorph, fun x => rfl⟩

/-- Helper: `w₀` is `1`-Lipschitz (`ω₀ ≤ 1`). -/
theorem s11_w0_lip : LipschitzWith 1 hpW0 := LipschitzWith.of_dist_le_mul fun x y => by
  rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq, s11_w0_sub y x]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := x) (C := 1)
    (f := hpOmega0) fun t _ => by
      rw [Real.norm_eq_abs, abs_of_pos (s11_w0_pos t)]
      exact hp_omega0_le_one t
  rwa [Real.norm_eq_abs, one_mul] at this

/-- Helper (W2): `w₀` is uniformly continuous. -/
theorem s11_w0_uc {w₀ : ℝ ≃ₜ ℝ} (hw : ∀ x, w₀ x = hpW0 x) : UniformContinuous w₀ := by
  rw [show ⇑w₀ = hpW0 from funext hw]
  exact s11_w0_lip.uniformContinuous

/-- Helper (W3): `w₀ ∈ SQS(ℝ)` with density `ω₀` (`A_∞` with `C = 4`, `δ = 1`, by `eq_hp_A_infty`). -/
theorem s11_w0_sqs {w₀ : ℝ ≃ₜ ℝ} (hw : ∀ x, w₀ x = hpW0 x) : IsSQSWith w₀ hpOmega0 := by
  have hf : ⇑w₀ = hpW0 := funext hw
  have hsurj := w₀.surjective
  rw [hf] at hsurj ⊢
  refine ⟨s11_w0_strictMono, s11_w0_continuous, hsurj,
    ⟨fun x => (s11_w0_pos x).le, s11_w0_locInt, 4, 1, by norm_num, one_pos, ?_⟩, fun x => ?_⟩
  · intro a b hab E hE hEm
    have hIcc : IntegrableOn hpOmega0 (Icc a b) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).1 (s11_w0_ii a b)
    have hba : 0 < b - a := sub_pos.2 hab
    calc ∫ x in E, hpOmega0 x ≤ ∫ x in E, 4 * intervalMean hpOmega0 a b :=
          setIntegral_mono_on (hIcc.mono_set hE)
            ((continuous_const.integrableOn_Icc (μ := volume)).mono_set hE) hEm
            fun x hx => eq_hp_A_infty hab (hE hx)
      _ = (volume E).toReal * (4 * intervalMean hpOmega0 a b) := by
          rw [setIntegral_const, smul_eq_mul]
          rfl
      _ = 4 * ((volume E).toReal / (b - a)) ^ (1 : ℝ) * ∫ x in Icc a b, hpOmega0 x := by
          rw [Real.rpow_one, intervalMean, intervalIntegral.integral_of_le hab.le,
            integral_Icc_eq_integral_Ioc]
          field_simp
  · simp [hpW0]

/-- Helper: `|log(1+s) - log(1+t)| ≤ |s - t|` for `s, t ≥ 0`. -/
theorem s11_w0_log1 {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |Real.log (1 + s) - Real.log (1 + t)| ≤ |s - t| := by
  wlog hst : t ≤ s generalizing s t
  · rw [abs_sub_comm, abs_sub_comm s t]
    exact this ht hs (not_le.1 hst).le
  have h1 : 0 < 1 + t := by linarith
  have h2 : 0 < 1 + s := by linarith
  rw [← Real.log_div h2.ne' h1.ne', abs_of_nonneg (Real.log_nonneg ((one_le_div h1).2 (by linarith))),
    abs_of_nonneg (by linarith : 0 ≤ s - t)]
  have h3 := Real.log_le_sub_one_of_pos (div_pos h2 h1)
  have h4 : (1 + s) / (1 + t) - 1 ≤ s - t := by
    rw [div_sub_one h1.ne', div_le_iff₀ h1]
    nlinarith
  linarith

/-- Helper: `log ω₀` is `1`-Lipschitz on a block. -/
theorem s11_w0_log_block {n : ℕ} {x y : ℝ} (hx1 : hpW0a n ≤ x) (hx2 : x ≤ hpW0a (n + 1))
    (hy1 : hpW0a n ≤ y) (hy2 : y ≤ hpW0a (n + 1)) :
    |Real.log (hpOmega0 x) - Real.log (hpOmega0 y)| ≤ |x - y| := by
  rw [hp_omega0_block hx1 hx2, hp_omega0_block hy1 hy2]
  have hD : (0 : ℝ) < 12 * ((n : ℝ) + 1) := by positivity
  rw [Real.log_div (by positivity) hD.ne', Real.log_div (by positivity) hD.ne',
    sub_sub_sub_cancel_right]
  calc _ ≤ abs (|x - hpW0c (n + 1)| - |y - hpW0c (n + 1)|) :=
        s11_w0_log1 (abs_nonneg _) (abs_nonneg _)
    _ ≤ |(x - hpW0c (n + 1)) - (y - hpW0c (n + 1))| := abs_abs_sub_abs_le_abs_sub _ _
    _ = |x - y| := by rw [sub_sub_sub_cancel_right]

theorem s11_w0_log_fwd (N : ℕ) : ∀ k : ℕ, ∀ x y : ℝ, hpW0a k ≤ x → x ≤ y →
    y ≤ hpW0a (k + N + 1) → |Real.log (hpOmega0 x) - Real.log (hpOmega0 y)| ≤ y - x := by
  induction N with
  | zero =>
    intro k x y h1 h2 h3
    have := s11_w0_log_block h1 (h2.trans h3) (h1.trans h2) h3
    rw [abs_of_nonpos (sub_nonpos.2 h2)] at this
    linarith
  | succ N ih =>
    intro k x y h1 h2 h3
    rcases le_total y (hpW0a (k + 1)) with hy | hy
    · have := s11_w0_log_block h1 (h2.trans hy) (h1.trans h2) hy
      rw [abs_of_nonpos (sub_nonpos.2 h2)] at this
      linarith
    rcases le_total (hpW0a (k + 1)) x with hx | hx
    · exact ih (k + 1) x y hx h2 (by rwa [show k + 1 + N + 1 = k + (N + 1) + 1 by omega])
    · have e1 := s11_w0_log_block h1 hx (hp_w0a_strictMono.monotone (Nat.le_succ k)) le_rfl
      have e2 := ih (k + 1) _ y le_rfl hy (by rwa [show k + 1 + N + 1 = k + (N + 1) + 1 by omega])
      rw [abs_of_nonpos (sub_nonpos.2 hx)] at e1
      calc _ ≤ |Real.log (hpOmega0 x) - Real.log (hpOmega0 (hpW0a (k + 1)))| +
            |Real.log (hpOmega0 (hpW0a (k + 1))) - Real.log (hpOmega0 y)| := abs_sub_le _ _ _
        _ ≤ _ := by linarith

theorem s11_w0_log_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    |Real.log (hpOmega0 x) - Real.log (hpOmega0 y)| ≤ y - x := by
  obtain ⟨k, h1, -⟩ := hp_w0_block_exists hx
  refine s11_w0_log_fwd ⌈y⌉₊ k x y h1 hxy ?_
  have h2 := hp_w0a_ge (k + ⌈y⌉₊ + 1)
  have h3 := Nat.le_ceil y
  push_cast at h2
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- Helper: `log ω₀` is `1`-Lipschitz on `ℝ` (`sec11-halfplane.tex`, Step 1). -/
theorem s11_w0_log_lip : LipschitzWith 1 fun x => Real.log (hpOmega0 x) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq, ← hp_omega0_abs x, ← hp_omega0_abs y]
    refine le_trans ?_ (abs_abs_sub_abs_le_abs_sub x y)
    rcases le_total |x| |y| with h | h
    · rw [abs_sub_comm |x| |y|, abs_of_nonneg (sub_nonneg.2 h)]
      exact s11_w0_log_nonneg (abs_nonneg x) h
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
      exact s11_w0_log_nonneg (abs_nonneg y) h

/-- Helper (W4): `w₀ ∈ SS(ℝ)`. -/
theorem s11_w0_ss {w₀ : ℝ ≃ₜ ℝ} (hw : ∀ x, w₀ x = hpW0 x) : IsSS w₀ :=
  hp_ss_of_lipschitz (s11_w0_sqs hw) s11_w0_log_lip

/-- Helper (W5): `w₀⁻¹ ∈ SQS(ℝ)`. -/
theorem s11_w0_symm_sqs {w₀ : ℝ ≃ₜ ℝ} (hw : ∀ x, w₀ x = hpW0 x) : IsSQS w₀.symm :=
  hp_sqs_symm ⟨_, s11_w0_sqs hw⟩

/-- Helper: `w₀(c_{n+1} + t) = w₀(c_{n+1}) + (t + t²/2)/(12(n+1))` for `0 ≤ t ≤ 6`. -/
theorem s11_w0_near_c (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht6 : t ≤ 6) :
    hpW0 (hpW0c (n + 1) + t) =
      hpW0 (hpW0c (n + 1)) + (t + t ^ 2 / 2) / (12 * ((n : ℝ) + 1)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hc1 : hpW0a n ≤ hpW0c (n + 1) := by
    rw [hp_w0c_succ]; linarith [hp_w0a_succ_sub n]
  have hc2 : hpW0c (n + 1) + t ≤ hpW0a (n + 1) := by
    rw [hp_w0c_succ]; linarith [hp_w0a_succ_sub n]
  obtain ⟨-, h⟩ := hp_omega0_integral_block hc1 (le_add_of_nonneg_right ht0) hc2
  have key : hpW0 (hpW0c (n + 1) + t) - hpW0 (hpW0c (n + 1)) =
      (t + t ^ 2 / 2) / (12 * ((n : ℝ) + 1)) := by
    rw [s11_w0_sub, h]
    simp only [add_sub_cancel_left, sub_self, abs_zero, abs_of_nonneg ht0]
    ring
  linarith

/-- Helper: `|I_n| = w₀(c_{n+1} + 6) - w₀(c_{n+1}) = 2/(n+1)`. -/
theorem s11_w0_len (n : ℕ) :
    hpW0 (hpW0c (n + 1) + 6) - hpW0 (hpW0c (n + 1)) = 2 / ((n : ℝ) + 1) := by
  rw [s11_w0_near_c n (by norm_num) le_rfl]
  field_simp
  ring

/-- Helper (W6): `w₀⁻¹` is not uniformly continuous (`w₀(c+6) - w₀(c+4) = 1/(n+1)`). -/
theorem s11_w0_symm_not_uc {w₀ : ℝ ≃ₜ ℝ} (hw : ∀ x, w₀ x = hpW0 x) :
    ¬ UniformContinuous w₀.symm := by
  rw [Metric.uniformContinuous_iff]
  intro H
  obtain ⟨δ, hδ, hδ'⟩ := H 1 one_pos
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  have h4 := s11_w0_near_c n (t := 4) (by norm_num) (by norm_num)
  have h6 := s11_w0_near_c n (t := 6) (by norm_num) (by norm_num)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hdiff : hpW0 (hpW0c (n + 1) + 6) - hpW0 (hpW0c (n + 1) + 4) = 1 / ((n : ℝ) + 1) := by
    rw [h4, h6]
    field_simp
    ring
  have hlt : dist (w₀ (hpW0c (n + 1) + 6)) (w₀ (hpW0c (n + 1) + 4)) < δ := by
    rw [hw, hw, Real.dist_eq, hdiff, abs_of_pos (by positivity), div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hn
    nlinarith
  have := hδ' hlt
  rw [w₀.symm_apply_apply, w₀.symm_apply_apply, Real.dist_eq,
    show hpW0c (n + 1) + 6 - (hpW0c (n + 1) + 4) = 2 by ring] at this
  norm_num at this

/-- Helper: the mean oscillation is invariant under increasing affine changes of variable. -/
theorem s11_w0_osc_affine (G : ℝ → ℝ) {α : ℝ} (hα : 0 < α) (β a b : ℝ) :
    realMeanOsc (fun u => G (α * u + β)) a b = realMeanOsc G (α * a + β) (α * b + β) := by
  have hmean : intervalMean (fun u => G (α * u + β)) a b =
      intervalMean G (α * a + β) (α * b + β) := by
    simp only [intervalMean]
    rw [intervalIntegral.integral_comp_mul_add G hα.ne' β, smul_eq_mul,
      show α * b + β - (α * a + β) = α * (b - a) by ring, mul_inv]
    ring
  simp only [realMeanOsc]
  rw [hmean]
  have e := intervalIntegral.integral_comp_mul_add
    (fun s => |G s - intervalMean G (α * a + β) (α * b + β)|) hα.ne' β (a := a) (b := b)
  beta_reduce at e
  rw [e, smul_eq_mul, show α * b + β - (α * a + β) = α * (b - a) by ring, mul_inv]
  ring

/-- Helper: the mean oscillation only sees `u` almost everywhere on `(a, b)`. -/
theorem s11_w0_osc_congr {u v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ᵐ x, x ∈ Ioo a b → u x = v x) : realMeanOsc u a b = realMeanOsc v a b := by
  have h' : ∀ᵐ x, x ∈ Set.uIoc a b → u x = v x := by
    have hb : ∀ᵐ x : ℝ, x ≠ b := by simp [ae_iff, measure_singleton]
    filter_upwards [h, hb] with x hx hxb hxI
    rw [uIoc_of_le hab] at hxI
    exact hx ⟨hxI.1, lt_of_le_of_ne hxI.2 hxb⟩
  have hm : intervalMean u a b = intervalMean v a b := by
    unfold intervalMean
    rw [intervalIntegral.integral_congr_ae h']
  unfold realMeanOsc
  rw [hm]
  congr 1
  exact intervalIntegral.integral_congr_ae (h'.mono fun x hx hxI => by rw [hx hxI])

/-- Helper: the mean oscillation of `K - (log s)/2` over `[1, 49]` is at least `log 18 / 192`
(`log s ≤ log 2` on `[1, 2]`, `log s ≥ log 36` on `[36, 49]`). -/
theorem s11_w0_osc_lower (K : ℝ) :
    Real.log 18 / 192 ≤ realMeanOsc (fun s => K - Real.log s / 2) 1 49 := by
  have hl18 : 0 < Real.log 18 := Real.log_pos (by norm_num)
  have h18 : Real.log 18 = Real.log 36 - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  simp only [realMeanOsc]
  set m := intervalMean (fun s => K - Real.log s / 2) 1 49 with hm
  have hsub : uIcc (1 : ℝ) 49 ⊆ {0}ᶜ := by
    intro s hs
    rw [uIcc_of_le (by norm_num)] at hs
    exact (by linarith [hs.1] : (0 : ℝ) < s).ne'
  have hc : ContinuousOn (fun s => |K - Real.log s / 2 - m|) (uIcc 1 49) :=
    ((continuousOn_const.sub ((Real.continuousOn_log.mono hsub).div_const 2)).sub
      continuousOn_const).abs
  have hi : IntervalIntegrable (fun s => |K - Real.log s / 2 - m|) volume 1 49 :=
    hc.intervalIntegrable
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 1 49)] fun s => |K - Real.log s / 2 - m| :=
    ae_of_all _ fun s => abs_nonneg _
  have key : Real.log 18 / 4 ≤ ∫ s in (1 : ℝ)..49, |K - Real.log s / 2 - m| := by
    rcases le_total (K - (Real.log 2 + Real.log 36) / 4) m with hmid | hmid
    · calc Real.log 18 / 4 ≤ ∫ _ in (36 : ℝ)..49, Real.log 18 / 4 := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
            linarith
        _ ≤ ∫ s in (36 : ℝ)..49, |K - Real.log s / 2 - m| := by
            refine intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
              (hi.mono_set ?_) fun s hs => ?_
            · rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
              exact Icc_subset_Icc (by norm_num) le_rfl
            · have := Real.log_le_log (by norm_num) hs.1
              exact le_abs.2 (Or.inr (by linarith))
        _ ≤ _ := intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) le_rfl hnn hi
    · calc Real.log 18 / 4 = ∫ _ in (1 : ℝ)..2, Real.log 18 / 4 := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
            ring
        _ ≤ ∫ s in (1 : ℝ)..2, |K - Real.log s / 2 - m| := by
            refine intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
              (hi.mono_set ?_) fun s hs => ?_
            · rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]
              exact Icc_subset_Icc le_rfl (by norm_num)
            · have := Real.log_le_log (by linarith [hs.1]) hs.2
              exact le_abs.2 (Or.inl (by linarith))
        _ ≤ _ := intervalIntegral.integral_mono_interval le_rfl (by norm_num) (by norm_num) hnn hi
  rw [show ((49 : ℝ) - 1)⁻¹ = 1 / 48 by norm_num]
  linarith

/-- Helper: on `I_n = [w₀(c_{n+1}), w₀(c_{n+1} + 6)]` any density `ω` of `w₀⁻¹` has
`log ω = log D - log(1 + 2D(u - u₀))/2` a.e. (`D = 12(n+1)`), so its mean oscillation over `I_n`
is that of `K - (log s)/2` over `[1, 49]`. -/
theorem s11_w0_osc_block {w₀ : ℝ ≃ₜ ℝ} (hw : ∀ x, w₀ x = hpW0 x) {ω : ℝ → ℝ}
    (hω : IsSQSWith w₀.symm ω) (n : ℕ) :
    Real.log 18 / 192 ≤ realMeanOsc (fun x => Real.log (ω x)) (hpW0 (hpW0c (n + 1)))
      (hpW0 (hpW0c (n + 1) + 6)) := by
  have hD : (0 : ℝ) < 12 * ((n : ℝ) + 1) := by positivity
  have hnear : ∀ t : ℝ, 0 ≤ t → t ≤ 6 → hpW0 (hpW0c (n + 1) + t) =
      hpW0 (hpW0c (n + 1)) + (t + t ^ 2 / 2) / (12 * ((n : ℝ) + 1)) :=
    fun t h0 h6 => s11_w0_near_c n h0 h6
  rw [hnear 6 (by norm_num) le_rfl, show (6 : ℝ) + 6 ^ 2 / 2 = 24 by norm_num]
  generalize hDe : 12 * ((n : ℝ) + 1) = D at hD hnear ⊢
  generalize hu0 : hpW0 (hpW0c (n + 1)) = u₀ at hnear ⊢
  generalize hc : hpW0c (n + 1) = c at hnear
  have hD0 : D ≠ 0 := hD.ne'
  -- (A) `w₀⁻¹` is explicit on `I_n`
  have hA : ∀ u ∈ Icc u₀ (u₀ + 24 / D),
      w₀.symm u = c - 1 + Real.sqrt (1 + 2 * D * (u - u₀)) := by
    intro u hu
    have hx0 : 0 ≤ u - u₀ := sub_nonneg.2 hu.1
    have hx1 : (u - u₀) * D ≤ 24 := (le_div_iff₀ hD).1 (sub_le_iff_le_add'.2 hu.2)
    have hpos : 0 ≤ 1 + 2 * D * (u - u₀) := by nlinarith [mul_nonneg hD.le hx0]
    have hS2 : Real.sqrt (1 + 2 * D * (u - u₀)) ^ 2 = 1 + 2 * D * (u - u₀) := Real.sq_sqrt hpos
    have hS1 : 1 ≤ Real.sqrt (1 + 2 * D * (u - u₀)) := by
      have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + 2 * D * (u - u₀) by nlinarith [mul_nonneg hD.le hx0])
      rwa [Real.sqrt_one] at this
    have hS7 : Real.sqrt (1 + 2 * D * (u - u₀)) ≤ 7 := by
      have := Real.sqrt_le_sqrt (show 1 + 2 * D * (u - u₀) ≤ 49 by nlinarith)
      rwa [show (49 : ℝ) = 7 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    generalize hS : Real.sqrt (1 + 2 * D * (u - u₀)) = S at hS2 hS1 hS7 ⊢
    have h := hnear (S - 1) (by linarith) (by linarith)
    have hval : u₀ + ((S - 1) + (S - 1) ^ 2 / 2) / D = u := by
      rw [show (S - 1) + (S - 1) ^ 2 / 2 = (S ^ 2 - 1) / 2 by ring, hS2]
      field_simp
      ring
    rw [hval, ← hw] at h
    rw [Homeomorph.symm_apply_eq, show c - 1 + S = c + (S - 1) by ring, h]
  -- (B) its derivative on the interior
  have hB : ∀ u ∈ Ioo u₀ (u₀ + 24 / D),
      HasDerivAt w₀.symm (2 * D / (2 * Real.sqrt (1 + 2 * D * (u - u₀)))) u := by
    intro u hu
    have hpos : 0 < 1 + 2 * D * (u - u₀) := by nlinarith [sub_pos.2 hu.1]
    have hg : HasDerivAt (fun v => 1 + 2 * D * (v - u₀)) (2 * D) u := by
      have := (((hasDerivAt_id u).sub_const u₀).const_mul (2 * D)).const_add 1
      convert this using 1 <;> first | rfl | ring
    have hφ := (hg.sqrt hpos.ne').const_add (c - 1)
    refine hφ.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
    exact hA v (Ioo_subset_Icc_self hv)
  -- (C) Lebesgue differentiation identifies `ω` a.e. on `I_n`
  have hC : ∀ᵐ u, u ∈ Ioo u₀ (u₀ + 24 / D) → Real.log (ω u) =
      (fun s => Real.log D - Real.log s / 2) (2 * D * u + (1 - 2 * D * u₀)) := by
    filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hω.2.2.2.1.2.1] with u hu hmem
    have h1 : HasDerivAt w₀.symm (ω u) u := by
      have := (hu 0).const_add (w₀.symm 0)
      convert this using 1
      exact funext hω.2.2.2.2
    have h2 := h1.unique (hB u hmem)
    have hpos : 0 < 1 + 2 * D * (u - u₀) := by nlinarith [sub_pos.2 hmem.1]
    rw [h2, show 2 * D * u + (1 - 2 * D * u₀) = 1 + 2 * D * (u - u₀) by ring,
      mul_div_mul_left _ _ (two_ne_zero' ℝ), Real.log_div hD0 (Real.sqrt_pos.2 hpos).ne',
      Real.log_sqrt hpos.le]
  have hu1 : u₀ < u₀ + 24 / D := by
    have : 0 < 24 / D := div_pos (by norm_num) hD
    linarith
  calc Real.log 18 / 192 ≤ realMeanOsc (fun s => Real.log D - Real.log s / 2) 1 49 :=
        s11_w0_osc_lower _
    _ = realMeanOsc (fun s => Real.log D - Real.log s / 2) (2 * D * u₀ + (1 - 2 * D * u₀))
          (2 * D * (u₀ + 24 / D) + (1 - 2 * D * u₀)) := by
        rw [show 2 * D * u₀ + (1 - 2 * D * u₀) = 1 by ring,
          show 2 * D * (u₀ + 24 / D) + (1 - 2 * D * u₀) = 49 by field_simp; ring]
    _ = realMeanOsc (fun u => (fun s => Real.log D - Real.log s / 2) (2 * D * u + (1 - 2 * D * u₀)))
          u₀ (u₀ + 24 / D) := (s11_w0_osc_affine _ (by linarith) _ _ _).symm
    _ = realMeanOsc (fun x => Real.log (ω x)) u₀ (u₀ + 24 / D) :=
        (s11_w0_osc_congr hu1.le hC).symm

/-- Helper (W7): `w₀⁻¹ ∉ SS(ℝ)`: the mean oscillation of `log (w₀⁻¹)'` over `I_n` stays
`≥ log 18 / 192` while `|I_n| = 2/(n+1) → 0`. -/
theorem s11_w0_symm_not_ss {w₀ : ℝ ≃ₜ ℝ} (hw : ∀ x, w₀ x = hpW0 x) : ¬ IsSS w₀.symm := by
  rintro ⟨ω, hω, -, hvmo⟩
  have hl : 0 < Real.log 18 := Real.log_pos (by norm_num)
  obtain ⟨δ, hδ, hδ'⟩ := hvmo.2 (Real.log 18 / 384) (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / δ)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlen := s11_w0_len n
  have hab : hpW0 (hpW0c (n + 1)) < hpW0 (hpW0c (n + 1) + 6) := by
    rw [← sub_pos, hlen]
    positivity
  have hsmall : hpW0 (hpW0c (n + 1) + 6) - hpW0 (hpW0c (n + 1)) < δ := by
    rw [hlen, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hn
    nlinarith
  have h1 := hδ' _ _ hab hsmall
  have h2 := s11_w0_osc_block hw hω n
  linarith

/-- Helper (W8a) for `prop_hp_w0`: a strongly quasisymmetric `h` is `ρ`-quasisymmetric for some `ρ`
(`s11_rh_doubling` twice: `|h[x, x+t]| ≤ |h(4I)| ≤ D² |h(I)|` for `I = [x-t, x]`, and symmetrically). -/
theorem s11_w8_qs {h ω : ℝ → ℝ} (hω : IsSQSWith h ω) : ∃ ρ : ℝ, IsQuasisymmetric h ρ := by
  obtain ⟨D, hD⟩ := s11_rh_doubling hω
  obtain ⟨hmono, hcont, hsurj, -, -⟩ := hω
  obtain ⟨D', hD'⟩ : ∃ D' : ℝ, D' = max D 1 := ⟨_, rfl⟩
  have hD'1 : 1 ≤ D' := hD' ▸ le_max_right _ _
  have hlen0 : ∀ c ℓ : ℝ, 0 < ℓ → 0 < imgLength h c ℓ := fun c ℓ hℓ => by
    unfold imgLength
    exact sub_pos.mpr (hmono (by linarith))
  have hdbl : ∀ c ℓ : ℝ, 0 < ℓ → imgLength h c (2 * ℓ) ≤ D' * imgLength h c ℓ := fun c ℓ hℓ =>
    (hD c ℓ hℓ).trans (mul_le_mul_of_nonneg_right (hD' ▸ le_max_left _ _) (hlen0 c ℓ hℓ).le)
  have h4 : ∀ c ℓ : ℝ, 0 < ℓ → imgLength h c (2 * (2 * ℓ)) ≤ D' ^ 2 * imgLength h c ℓ :=
    fun c ℓ hℓ => by
      calc imgLength h c (2 * (2 * ℓ)) ≤ D' * imgLength h c (2 * ℓ) := hdbl c _ (by linarith)
        _ ≤ D' * (D' * imgLength h c ℓ) :=
          mul_le_mul_of_nonneg_left (hdbl c ℓ hℓ) (by linarith)
        _ = D' ^ 2 * imgLength h c ℓ := by ring
  refine ⟨D' ^ 2, hmono, hcont, hmono.monotone.tendsto_atTop_atTop fun b => ?_,
    hmono.monotone.tendsto_atBot_atBot fun b => ?_, fun x t ht => ?_⟩
  · obtain ⟨a, ha⟩ := hsurj b
    exact ⟨a, ha.ge⟩
  · obtain ⟨a, ha⟩ := hsurj b
    exact ⟨a, ha.le⟩
  have hb : 0 < h x - h (x - t) := sub_pos.mpr (hmono (by linarith))
  have hρ : 0 < D' ^ 2 := by positivity
  have hab : h (x + t) - h x ≤ D' ^ 2 * (h x - h (x - t)) := by
    have e := h4 (x - t / 2) t ht
    have e1 : imgLength h (x - t / 2) t = h x - h (x - t) := by
      unfold imgLength
      rw [show x - t / 2 + t / 2 = x by ring, show x - t / 2 - t / 2 = x - t by ring]
    have e2 : imgLength h (x - t / 2) (2 * (2 * t)) = h (x + 3 * t / 2) - h (x - 5 * t / 2) := by
      unfold imgLength
      rw [show x - t / 2 + 2 * (2 * t) / 2 = x + 3 * t / 2 by ring,
        show x - t / 2 - 2 * (2 * t) / 2 = x - 5 * t / 2 by ring]
    rw [e1, e2] at e
    have m1 : h (x + t) ≤ h (x + 3 * t / 2) := hmono.monotone (by linarith)
    have m2 : h (x - 5 * t / 2) ≤ h x := hmono.monotone (by linarith)
    linarith
  have hba : h x - h (x - t) ≤ D' ^ 2 * (h (x + t) - h x) := by
    have e := h4 (x + t / 2) t ht
    have e1 : imgLength h (x + t / 2) t = h (x + t) - h x := by
      unfold imgLength
      rw [show x + t / 2 + t / 2 = x + t by ring, show x + t / 2 - t / 2 = x by ring]
    have e2 : imgLength h (x + t / 2) (2 * (2 * t)) = h (x + 5 * t / 2) - h (x - 3 * t / 2) := by
      unfold imgLength
      rw [show x + t / 2 + 2 * (2 * t) / 2 = x + 5 * t / 2 by ring,
        show x + t / 2 - 2 * (2 * t) / 2 = x - 3 * t / 2 by ring]
    rw [e1, e2] at e
    have m1 : h (x - 3 * t / 2) ≤ h (x - t) := hmono.monotone (by linarith)
    have m2 : h x ≤ h (x + 5 * t / 2) := hmono.monotone (by linarith)
    linarith
  show (D' ^ 2)⁻¹ ≤ (h (x + t) - h x) / (h x - h (x - t)) ∧
    (h (x + t) - h x) / (h x - h (x - t)) ≤ D' ^ 2
  constructor
  · rw [le_div_iff₀ hb, inv_mul_le_iff₀ hρ]
    exact hba
  · rw [div_le_iff₀ hb]
    exact hab

/-- Helper (W8b) for `prop_hp_w0`: for a `K`-q.c. map `V` of `ℍ`, `μ = 1_ℍ μ_V` is a Beltrami
coefficient on `ℂ` with `‖μ‖_∞ ≤ (K-1)/(K+1) < 1`, vanishing on `{Im z ≤ 0}`. -/
theorem s11_w8_mu {V : ℂ → ℂ} {K : ℝ} (hV : IsKQC V upperHalf K) :
    0 ≤ (K - 1) / (K + 1) ∧ (K - 1) / (K + 1) < 1 ∧
      IsBeltramiCoeff (upperHalf.indicator (complexDilatation V)) univ ((K - 1) / (K + 1)) ∧
      ∀ z : ℂ, z.im ≤ 0 → upperHalf.indicator (complexDilatation V) z = 0 := by
  have hK1 : 1 ≤ K := hV.2.1
  have hUm : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  have hk0 : 0 ≤ (K - 1) / (K + 1) := div_nonneg (by linarith) (by linarith)
  have hm : Measurable (complexDilatation V) := (measurable_dzbar V).div (measurable_dz V)
  obtain ⟨⟨-, hb⟩, -⟩ := thm10_2_genHomeoSolution_of_isKQC hV
  have hb' := (ae_restrict_iff' hUm).mp hb
  refine ⟨hk0, ?_, ⟨(hm.indicator hUm).aestronglyMeasurable, ?_⟩, fun z hz => ?_⟩
  · rw [div_lt_one (by linarith)]
    linarith
  · rw [Measure.restrict_univ]
    filter_upwards [hb'] with z hz
    by_cases hzU : z ∈ upperHalf
    · rw [Set.indicator_of_mem hzU]
      exact hz hzU
    · rw [Set.indicator_of_notMem hzU, norm_zero]
      exact hk0
  · have hzU : z ∉ upperHalf := fun h' => by
      have h'' : 0 < z.im := h'
      linarith
    exact Set.indicator_of_notMem hzU _

/-- Helper (W8c) for `prop_hp_w0`: for a q.c. self-map `B` of `ℍ` with boundary values `h`
(`HasQCExtensionH`), the map `B̄ = B` on `ℍ`, `B̄ z = h (Re z)` off `ℍ`, is continuous on `ℍ ∪ ℝ`
(the extension `G` is continuous on `closure ℍ ⊆ ℂ̄`, and `ℂ → ℂ̄` is an embedding). -/
theorem s11_w8_bext {h : ℝ → ℝ} {B : ℂ → ℂ} {K : ℝ} (hB : HasQCExtensionH h B K) :
    ContinuousOn (fun z : ℂ => if 0 < z.im then B z else ((h z.re : ℝ) : ℂ)) closedUpperHalf := by
  obtain ⟨-, -, G, hG, -, hGx⟩ := hB
  obtain ⟨heq, hGc, -⟩ := hG
  have hcl : closure upperHalf = closedUpperHalf := Complex.closure_setOfPred_lt_im 0
  have hmaps : MapsTo ((↑) : ℂ → ExtPlane) closedUpperHalf (closure (toExt upperHalf)) := by
    intro z hz
    rw [← hcl] at hz
    exact image_closure_subset_closure_image OnePoint.continuous_coe ⟨z, hz, rfl⟩
  rw [OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_iff]
  refine (hGc.comp OnePoint.continuous_coe.continuousOn hmaps).congr fun z hz => ?_
  by_cases hpos : 0 < z.im
  · simp only [Function.comp_apply, ite_eq_left hpos]
    exact (heq z hpos).symm
  · simp only [Function.comp_apply, ite_eq_right hpos]
    have hz0 : z.im = 0 := le_antisymm (not_lt.mp hpos) hz
    have hz' : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hz0])
    conv_rhs => rw [← hz']
    exact (hGx z.re).symm

/-- Helper (W8d) for `prop_hp_w0`: if `B` is a `K`-q.c. self-map of `ℍ` and `F` is a normalized
solution for a `μ` equal to `μ_{B⁻¹}` on `ℍ`, then `F ∘ B` is conformal on `ℍ`
(`F = φ ∘ B⁻¹` on `ℍ` with `φ` conformal, by `same_dilatation_conformal`). -/
theorem s11_w8_conf {B F μ : ℂ → ℂ} {K : ℝ} (hB : IsKQC B upperHalf K)
    (hBs : B '' upperHalf = upperHalf)
    (hμ : EqOn μ (complexDilatation (Function.invFunOn B upperHalf)) upperHalf)
    (hF : IsNormalizedSolution F μ) :
    IsConformalOnto (F ∘ B) upperHalf (F '' upperHalf) := by
  have hU : IsOpen upperHalf := isOpen_upperHalf
  have hUm : MeasurableSet upperHalf := hU.measurableSet
  have hV : IsKQC (Function.invFunOn B upperHalf) upperHalf K := by
    have h := thm7_2_inv hB
    rwa [hBs] at h
  obtain ⟨⟨hVm, hVb⟩, hVsol⟩ := thm10_2_genHomeoSolution_of_isKQC hV
  have hμae : μ =ᵐ[volume.restrict upperHalf] complexDilatation (Function.invFunOn B upperHalf) :=
    (ae_restrict_iff' hUm).mpr (Filter.Eventually.of_forall fun z hz => hμ hz)
  have hμB : IsBeltramiCoeff μ upperHalf ((K - 1) / (K + 1)) := by
    refine ⟨hVm.congr hμae.symm, ?_⟩
    filter_upwards [hVb, hμae] with z hz hz'
    rw [hz']
    exact hz
  have hVμ : IsGenHomeoSolution (Function.invFunOn B upperHalf) μ upperHalf 2 := by
    obtain ⟨hhom, g, h, hp, hae⟩ := hVsol
    refine ⟨hhom, g, h, hp, ?_⟩
    filter_upwards [hae, hμae] with z hz hz'
    rw [hz']
    exact hz
  obtain ⟨⟨KF, hKF⟩, -, -, -, hFd⟩ := hF
  have hFU : IsKQC F upperHalf KF := nx_isKQC_restrict hKF hU (subset_univ _)
  obtain ⟨-, hFsol⟩ := thm10_2_genHomeoSolution_of_isKQC hFU
  have hFμ : IsGenHomeoSolution F μ upperHalf 2 := by
    obtain ⟨hhom, g, h, hp, hae⟩ := hFsol
    refine ⟨hhom, g, h, hp, ?_⟩
    filter_upwards [hae, ae_restrict_of_ae hFd] with z hz hz'
    rw [← hz']
    exact hz
  have hk1 : (K - 1) / (K + 1) < 1 := by
    have hK1 : 1 ≤ K := hB.2.1
    rw [div_lt_one (by linarith)]
    linarith
  obtain ⟨φ, hφ, hFφ⟩ := same_dilatation_conformal hU hk1 hμB hVμ hFμ
  have hinj : InjOn B upperHalf := hB.2.2.1.2.1
  have hVB : ∀ z ∈ upperHalf, Function.invFunOn B upperHalf (B z) = z := fun z hz =>
    hinj.leftInvOn_invFunOn hz
  have hBU : ∀ z ∈ upperHalf, B z ∈ upperHalf := fun z hz => hBs ▸ mem_image_of_mem B hz
  have hVU : Function.invFunOn B upperHalf '' upperHalf = upperHalf := by
    refine Subset.antisymm ?_ fun z hz => ⟨B z, hBU z hz, hVB z hz⟩
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w ∈ B '' upperHalf := by
      rw [hBs]
      exact hw
    obtain ⟨a, ha, hab⟩ := hw'
    exact Function.invFunOn_mem ⟨a, ha, hab⟩
  rw [hVU] at hφ
  have heq : EqOn (F ∘ B) φ upperHalf := fun z hz => by
    show F (B z) = φ z
    rw [hFφ (B z) (hBU z hz), hVB z hz]
  refine ⟨hφ.1.congr heq, hFU.2.2.1.2.1.comp hinj fun z hz => hBU z hz, ?_⟩
  rw [image_comp, hBs]

/-- Helper for `s11_w8_not_line`: `z ↦ (z - b)/a` maps `S` conformally onto `{w | a w + b ∈ S}`. -/
theorem s11_w8_aff_conf {a b : ℂ} (ha : a ≠ 0) (S : Set ℂ) :
    IsConformalOnto (fun z => (z - b) / a) S {w | a * w + b ∈ S} := by
  refine ⟨((differentiable_id.sub_const b).div_const a).differentiableOn, fun x _ y _ hxy => ?_, ?_⟩
  · have h' : (x - b) / a * a = (y - b) / a * a := by
      rw [show (x - b) / a = (y - b) / a from hxy]
    rwa [div_mul_cancel₀ _ ha, div_mul_cancel₀ _ ha, sub_left_inj] at h'
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      show a * ((z - b) / a) + b ∈ S
      rwa [mul_div_cancel₀ _ ha, sub_add_cancel]
    · intro hw
      refine ⟨a * w + b, hw, ?_⟩
      show (a * w + b - b) / a = w
      field_simp
      ring

/-- Helper for `s11_w8_not_line`: if `g : 𝕃 → S` is conformal, then `z ↦ conj (g (conj z))` maps
`ℍ` conformally onto `conj(S)`. -/
theorem s11_w8_conj_conf {g : ℂ → ℂ} {S : Set ℂ} (hg : IsConformalOnto g lowerHalf S) :
    IsConformalOnto (fun z => conj (g (conj z))) upperHalf (conj '' S) := by
  have hL : IsOpen lowerHalf := isOpen_lt Complex.continuous_im continuous_const
  have hmem : ∀ z ∈ upperHalf, conj z ∈ lowerHalf := fun z hz => by
    have h' : 0 < z.im := hz
    show (conj z).im < 0
    rw [conj_im]
    linarith
  refine ⟨fun z hz => ?_, fun x hx y hy hxy => ?_, ?_⟩
  · have hd := (hg.1.differentiableAt (hL.mem_nhds (hmem z hz))).conj_conj
    rw [conj_conj] at hd
    exact hd.differentiableWithinAt
  · have h1 : g (conj x) = g (conj y) := star_injective hxy
    have h2 := hg.2.1 (hmem x hx) (hmem y hy) h1
    exact star_injective h2
  · rw [← hg.2.2]
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨g (conj z), ⟨conj z, hmem z hz, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      have hu' : u.im < 0 := hu
      refine ⟨conj u, ?_, ?_⟩
      · show 0 < (conj u).im
        rw [conj_im]
        linarith
      · show conj (g (conj (conj u))) = conj (g u)
        rw [conj_conj]

/-- Helper for `s11_w8_not_line`: `g → ∞` at `∞` in `𝕃` gives `conj ∘ g ∘ conj → ∞` at `∞` in `ℍ`. -/
theorem s11_w8_conj_tendsto {g : ℂ → ℂ}
    (hgi : Tendsto g (cocompact ℂ ⊓ 𝓟 lowerHalf) (cocompact ℂ)) :
    Tendsto (fun z => conj (g (conj z))) (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ) := by
  have hcc : Tendsto (fun z : ℂ => conj z) (cocompact ℂ) (cocompact ℂ) :=
    Complex.conjLIE.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  have hp : Tendsto (fun z : ℂ => conj z) (𝓟 upperHalf) (𝓟 lowerHalf) :=
    tendsto_principal_principal.mpr fun z hz => by
      have h' : 0 < z.im := hz
      show (conj z).im < 0
      rw [conj_im]
      linarith
  exact hcc.comp (hgi.comp (hcc.inf hp))

/-- Helper (W8e) for `prop_hp_w0`: conformal maps `f : ℍ → Ω`, `g : 𝕃 → Ωs` sending `∞` to `∞`,
continuous up to `ℝ`, with welding `w` such that `w⁻¹` is not uniformly continuous, do not map onto
two complementary half-planes: otherwise, with `A z = a z + b`, `A ∘ f` and `A ∘ g` are increasing
real affine maps (`hpv_aut_upper`, and its reflection for `𝕃`), so `w` is real affine. -/
theorem s11_w8_not_line {Ω Ωs : Set ℂ} {f g : ℂ → ℂ} {w : ℝ ≃ₜ ℝ}
    (hw : ¬ UniformContinuous w.symm) (hf : IsConformalOnto f upperHalf Ω)
    (hg : IsConformalOnto g lowerHalf Ωs) (hfc : ContinuousOn f closedUpperHalf)
    (hgc : ContinuousOn g closedLowerHalf)
    (hfi : Tendsto f (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ))
    (hgi : Tendsto g (cocompact ℂ ⊓ 𝓟 lowerHalf) (cocompact ℂ))
    (hweld : ∀ x : ℝ, f (x : ℂ) = g ((w x : ℝ) : ℂ)) : ¬ IsLinePair Ω Ωs := by
  rintro ⟨a, b, ha, hΩ, hΩs⟩
  have hRU : IsConformalOnto (fun z => (z - b) / a) upperHalf Ω := by
    rw [hΩ]
    exact s11_w8_aff_conf ha upperHalf
  have hRL : IsConformalOnto (fun z => (z - b) / a) lowerHalf Ωs := by
    rw [hΩs]
    exact s11_w8_aff_conf ha lowerHalf
  have hRc : Continuous fun z : ℂ => (z - b) / a := (continuous_id.sub continuous_const).div_const a
  have hRc' : Continuous fun z : ℂ => conj ((conj z - b) / a) :=
    Complex.continuous_conj.comp (hRc.comp Complex.continuous_conj)
  obtain ⟨α, β, hα, hfU⟩ := hpv_aut_upper hRU hf hRc (fun _ _ => rfl) hfi
  obtain ⟨α', β', hα', hgU⟩ := hpv_aut_upper (s11_w8_conj_conf hRL) (s11_w8_conj_conf hg) hRc'
    (fun _ _ => rfl) (s11_w8_conj_tendsto hgi)
  have hfA : ∀ z ∈ upperHalf, a * f z + b = (α : ℂ) * z + β := fun z hz => by
    rw [hfU z hz]
    field_simp
    ring
  have hgA : ∀ u ∈ lowerHalf, a * g u + b = (α' : ℂ) * u + β' := fun u hu => by
    have hu' : u.im < 0 := hu
    have hcu : conj u ∈ upperHalf := by
      show 0 < (conj u).im
      rw [conj_im]
      linarith
    have h1 := congrArg conj (hgU (conj u) hcu)
    simp only [conj_conj, map_add, map_mul, conj_ofReal] at h1
    rw [h1]
    field_simp
    ring
  have hcU : closure upperHalf = closedUpperHalf := Complex.closure_setOfPred_lt_im 0
  have hcL : closure lowerHalf = closedLowerHalf := Complex.closure_setOfPred_im_lt 0
  have hfR : ∀ x : ℝ, a * f x + b = (α : ℂ) * x + β := fun x => by
    have hE : EqOn (fun z => a * f z + b) (fun z => (α : ℂ) * z + β) closedUpperHalf :=
      Set.EqOn.of_subset_closure (fun z hz => hfA z hz)
        ((continuousOn_const.mul hfc).add continuousOn_const)
        ((continuous_const.mul continuous_id).add continuous_const).continuousOn
        (fun z hz => (show (0 : ℝ) < z.im from hz).le) hcU.ge
    exact hE (show (0 : ℝ) ≤ (x : ℂ).im by simp)
  have hgR : ∀ x : ℝ, a * g x + b = (α' : ℂ) * x + β' := fun x => by
    have hE : EqOn (fun z => a * g z + b) (fun z => (α' : ℂ) * z + β') closedLowerHalf :=
      Set.EqOn.of_subset_closure (fun z hz => hgA z hz)
        ((continuousOn_const.mul hgc).add continuousOn_const)
        ((continuous_const.mul continuous_id).add continuous_const).continuousOn
        (fun z hz => (show z.im < 0 from hz).le) hcL.ge
    exact hE (show (x : ℂ).im ≤ 0 by simp)
  have hkey : ∀ x : ℝ, α * x + β = α' * w x + β' := fun x => by
    have h1 : (α : ℂ) * x + β = (α' : ℂ) * (w x : ℝ) + β' := by
      rw [← hfR x, ← hgR (w x), hweld x]
    have h2 := congrArg Complex.re h1
    simpa using h2
  have hsymm : ∀ y : ℝ, w.symm y = α' / α * y + (β' - β) / α := fun y => by
    have h1 := hkey (w.symm y)
    rw [w.apply_symm_apply] at h1
    field_simp
    linarith
  apply hw
  have hfun : (w.symm : ℝ → ℝ) = fun y => α' / α * y + (β' - β) / α := funext hsymm
  rw [hfun]
  exact (uniformContinuous_id.const_mul' (α' / α)).add uniformContinuous_const

/-- Helper for `s11_w8_setting`: conformality onto `V` is invariant under changing the map off `U`. -/
theorem s11_w8_conf_congr {f g : ℂ → ℂ} {U V : Set ℂ} (hf : IsConformalOnto f U V)
    (heq : EqOn g f U) : IsConformalOnto g U V :=
  ⟨hf.1.congr heq, hf.2.1.congr heq.symm, heq.image_eq.trans hf.2.2⟩

/-- Helper (W8) for `prop_hp_w0`: some quasicircle through `∞` has welding `w₀`. With `B` the
Beurling–Ahlfors extension of `w₀` (`s11_w8_qs`, `thm17_2_beurling_ahlfors`), `μ = 1_ℍ μ_{B⁻¹}`
(`s11_w8_mu`) and `F = f_μ` (`normalizedSolution`, conformal on `𝕃` by `ut_conformal_lowerHalf`):
`Ω = F(ℍ)`, `Ωs = F(𝕃)`, `f = F ∘ B̄` (`s11_w8_bext`, `s11_w8_conf`), `g = F`; `¬ IsLinePair` by
`s11_w8_not_line` and `s11_w0_symm_not_uc`. -/
theorem s11_w8_setting {w₀ : ℝ ≃ₜ ℝ} (hw : ∀ x, w₀ x = hpW0 x) :
    ∃ (Ω Ωs : Set ℂ) (K : ℝ) (f g : ℂ → ℂ), IsHPSetting Ω Ωs K f g w₀ := by
  obtain ⟨ρ, hρ⟩ := s11_w8_qs (s11_w0_sqs hw)
  obtain ⟨-, hBA⟩ := thm17_2_beurling_ahlfors hρ
  generalize beurlingAhlfors (⇑w₀) 1 = B at hBA
  generalize 8 * ρ * (ρ + 1) = KB at hBA
  have hBK : IsKQC B upperHalf KB := hBA.1
  have hBs : B '' upperHalf = upperHalf := hBA.2.1
  obtain ⟨G, hG, hGinf, -⟩ := hBA.2.2
  have hKB1 : 1 ≤ KB := hBK.2.1
  have hV : IsKQC (Function.invFunOn B upperHalf) upperHalf KB := by
    have h := thm7_2_inv hBK
    rwa [hBs] at h
  obtain ⟨hk0, hk1, hμ, hμ0⟩ := s11_w8_mu hV
  obtain ⟨F₀, -, hF₀K, huniq⟩ := thm13_7_normalized_existence hk0 hk1 hμ
  have hKk : (1 + (KB - 1) / (KB + 1)) / (1 - (KB - 1) / (KB + 1)) = KB := by
    have h1 : KB + 1 ≠ 0 := by linarith
    rw [show 1 + (KB - 1) / (KB + 1) = 2 * KB / (KB + 1) by field_simp; ring,
      show 1 - (KB - 1) / (KB + 1) = 2 / (KB + 1) by field_simp; ring]
    field_simp
  rw [hKk] at hF₀K
  have hFspec := ut_spec ⟨_, ⟨_, hk0, hk1, hμ⟩, hμ0⟩
  have hFL := ut_conformal_lowerHalf ⟨_, ⟨_, hk0, hk1, hμ⟩, hμ0⟩
  generalize normalizedSolution (upperHalf.indicator (complexDilatation
    (Function.invFunOn B upperHalf))) = F at hFspec hFL
  have hFK : IsKQC F univ KB := by
    rw [huniq F hFspec]
    exact hF₀K
  have hFs : F '' univ = univ := hFspec.2.1
  obtain ⟨e, he⟩ := t1_homeomorph hFK hFs
  have hFc : Continuous F := he ▸ e.continuous
  have hFt : Tendsto F (cocompact ℂ) (cocompact ℂ) := he ▸ e.isClosedEmbedding.tendsto_cocompact
  have hfU : IsConformalOnto (fun z => F (if 0 < z.im then B z else ((w₀ z.re : ℝ) : ℂ)))
      upperHalf (F '' upperHalf) :=
    s11_w8_conf_congr (s11_w8_conf hBK hBs (fun z hz => Set.indicator_of_mem hz _) hFspec)
      fun z hz => by
        have hz' : 0 < z.im := hz
        show F (if 0 < z.im then B z else ((w₀ z.re : ℝ) : ℂ)) = F (B z)
        rw [ite_eq_left hz']
  have hfc : ContinuousOn (fun z => F (if 0 < z.im then B z else ((w₀ z.re : ℝ) : ℂ)))
      closedUpperHalf := hFc.comp_continuousOn (s11_w8_bext hBA)
  have hfi : Tendsto (fun z => F (if 0 < z.im then B z else ((w₀ z.re : ℝ) : ℂ)))
      (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ) := by
    refine (hFt.comp (b4_ext_tendsto_cocompact hG hGinf)).congr' ?_
    refine eventually_inf_principal.mpr (Filter.Eventually.of_forall fun z hz => ?_)
    have hz' : 0 < z.im := hz
    show F (B z) = F (if 0 < z.im then B z else ((w₀ z.re : ℝ) : ℂ))
    rw [ite_eq_left hz']
  have hgi : Tendsto F (cocompact ℂ ⊓ 𝓟 lowerHalf) (cocompact ℂ) := hFt.mono_left inf_le_left
  have hweld : ∀ x : ℝ, (fun z => F (if 0 < z.im then B z else ((w₀ z.re : ℝ) : ℂ))) (x : ℂ) =
      F ((w₀ x : ℝ) : ℂ) := fun x => by
    show F (if 0 < (x : ℂ).im then B x else ((w₀ (x : ℂ).re : ℝ) : ℂ)) = F ((w₀ x : ℝ) : ℂ)
    rw [ite_eq_right (by simp), Complex.ofReal_re]
  exact ⟨F '' upperHalf, F '' lowerHalf, KB, _, F, ⟨F, hFK, hFs, rfl, rfl⟩,
    s11_w8_not_line (s11_w0_symm_not_uc hw) hfU hFL hfc hFc.continuousOn hfi hgi hweld,
    hfU, hFL, hfc, hFc.continuousOn, hfi, hgi, hweld⟩

/-- Proposition 11.11 `prop:hp-w0`, `sec11-halfplane.tex:834`: `w₀` is a homeomorphism of `ℝ`,
uniformly continuous and strongly symmetric, while `w₀⁻¹` is strongly quasisymmetric but neither
strongly symmetric nor uniformly continuous; some quasicircle through `∞` has welding `w₀`; and for
every such quasicircle `λ_f ∈ CM₀(ℍ)` and `λ_- ∉ CM₀(ℍ)`. -/
theorem prop_hp_w0 :
    ∃ w₀ : ℝ ≃ₜ ℝ, (∀ x, w₀ x = hpW0 x) ∧ UniformContinuous w₀ ∧ IsSS w₀ ∧ IsSQS w₀.symm ∧
      ¬ IsSS w₀.symm ∧ ¬ UniformContinuous w₀.symm ∧
      (∃ (Ω Ωs : Set ℂ) (K : ℝ) (f g : ℂ → ℂ), IsHPSetting Ω Ωs K f g w₀) ∧
      ∀ (Ω Ωs : Set ℂ) (K : ℝ) (f g : ℂ → ℂ), IsHPSetting Ω Ωs K f g w₀ →
        IsHPVanishingCarleson (hpSchwarzCarleson f) ∧
          ¬ IsHPVanishingCarleson (hpSchwarzCarlesonLower g) := by sorry

/-! ## Vanishing under uniform continuity -/

/-- `d_ρ ≥ 0` on `ℍ`. -/
theorem hp_la_hpDist_nonneg {z z' : ℂ} (hz : z ∈ upperHalf) (hz' : z' ∈ upperHalf) :
    0 ≤ hpDist z z' := by
  have h1 : (0 : ℝ) < z.im := hz
  have h2 : (0 : ℝ) < z'.im := hz'
  unfold hpDist
  exact Real.arcosh_nonneg (le_add_of_nonneg_right (by positivity))

/-- `R̃ = f⁻¹ ∘ R ∘ g ∘ J` in the half-plane setting: `g(z̄) ∈ Ω*`, `R(g(z̄)) ∈ Ω`,
`f(R̃ z) = R(g(z̄))` and `R̃ z ∈ ℍ`. -/
theorem hp_la_mem {Ω Ωs : Set ℂ} {K : ℝ} {f g : ℂ → ℂ} {w : ℝ ≃ₜ ℝ} {lab : ℂ × ℝ → ℂ}
    (hs : IsHPSetting Ω Ωs K f g w) (hlab : IsLabel Ω lab) {z : ℂ} (hz : z ∈ upperHalf) :
    conj z ∈ lowerHalf ∧ g (conj z) ∈ Ωs ∧ lab (epstein Ωs (g (conj z))) ∈ Ω ∧
      f (hpLabelMap Ωs f g lab z) = lab (epstein Ωs (g (conj z))) ∧
      hpLabelMap Ωs f g lab z ∈ upperHalf := by
  obtain ⟨hq, hnl, hf, hg, -⟩ := hs
  have hc : conj z ∈ lowerHalf := by
    have : (0 : ℝ) < z.im := hz
    show (conj z).im < 0
    rw [Complex.conj_im]
    linarith
  have hgz : g (conj z) ∈ Ωs := hg.2.2 ▸ mem_image_of_mem g hc
  obtain ⟨A, B, E, hR⟩ := cor_R_qi K
  have hRz := (hR Ω Ωs hq hnl lab hlab).1 _ hgz
  have hex : ∃ a ∈ upperHalf, f a = lab (epstein Ωs (g (conj z))) := by
    rw [← hf.2.2] at hRz
    obtain ⟨a, ha, hfa⟩ := hRz
    exact ⟨a, ha, hfa⟩
  exact ⟨hc, hgz, hRz, Function.invFunOn_eq hex, Function.invFunOn_mem hex⟩

/-- `R̃ ∘ val` is Borel: `z ↦ X*(g(z̄))` is continuous on `ℍ`, `lab` is Borel, and `f⁻¹` is
continuous on `Ω`. -/
theorem hp_la_measurable {Ω Ωs : Set ℂ} {K : ℝ} {f g : ℂ → ℂ} {w : ℝ ≃ₜ ℝ}
    {lab : ℂ × ℝ → ℂ} (hs : IsHPSetting Ω Ωs K f g w) (hlab : IsLabel Ω lab) :
    Measurable (hpLabelMap Ωs f g lab ∘ (Subtype.val : upperHalf → ℂ)) := by
  have hmem := fun z : upperHalf => hp_la_mem hs hlab z.2
  obtain ⟨hq, -, hf, hg, -⟩ := hs
  have hU : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im
  have hΩs : ∃ F : ℂ → ℂ, IsConformalOnto F unitDisc Ωs := (s03_b0_basic (s03_qce_swap hq)).2.2.2
  have hX : ContinuousOn (epstein Ωs) Ωs := fun x hx =>
    (s02_epstein_differentiableAt hΩs hx).continuousAt.continuousWithinAt
  have hgc : Continuous fun z : upperHalf => g (conj z.1) :=
    hg.1.continuousOn.comp_continuous (Complex.continuous_conj.comp continuous_subtype_val)
      fun z => (hmem z).1
  have hXc : Continuous fun z : upperHalf => epstein Ωs (g (conj z.1)) :=
    hX.comp_continuous hgc fun z => (hmem z).2.1
  have hT : Measurable fun z : upperHalf =>
      (⟨lab (epstein Ωs (g (conj z.1))), (hmem z).2.2.1⟩ : Ω) :=
    (hlab.1.comp hXc.measurable).subtype_mk
  have hψ : Continuous (Ω.domRestrict (Function.invFunOn f upperHalf)) :=
    (hf.symm hU).1.continuousOn.domRestrict
  exact hψ.measurable.comp hT

/-- Lemma 11.12(a) `lem:hp-label`, `sec11-halfplane.tex:944`: `R̃` is a Borel
`(L_A, c_A)`-quasi-isometry of `(ℍ, d_ρ)`, with constants depending only on `K`. -/
theorem lem_hp_label_a : ∀ K : ℝ, 1 ≤ K → ∃ LA cA : ℝ, 1 ≤ LA ∧ 0 ≤ cA ∧
    ∀ (Ω Ωs : Set ℂ) (f g : ℂ → ℂ) (w : ℝ ≃ₜ ℝ) (lab : ℂ × ℝ → ℂ),
      IsHPSetting Ω Ωs K f g w → IsLabel Ω lab →
        MapsTo (hpLabelMap Ωs f g lab) upperHalf upperHalf ∧
        Measurable (hpLabelMap Ωs f g lab ∘ (Subtype.val : upperHalf → ℂ)) ∧
        ∀ z ∈ upperHalf, ∀ z' ∈ upperHalf,
          LA⁻¹ * hpDist z z' - cA ≤ hpDist (hpLabelMap Ωs f g lab z) (hpLabelMap Ωs f g lab z') ∧
          hpDist (hpLabelMap Ωs f g lab z) (hpLabelMap Ωs f g lab z') ≤ LA * hpDist z z' + cA := by
  -- The constants come from Corollary 3.7 (`cor_R_qi`), which holds for every `K`; the
  -- hypothesis `1 ≤ K` is not needed (the statement stays true without it).
  intro K _hK
  obtain ⟨A, B, E, hR⟩ := cor_R_qi K
  refine ⟨max A 1, max B 0, le_max_right _ _, le_max_right _ _,
    fun Ω Ωs f g w lab hs hlab => ⟨fun z hz => (hp_la_mem hs hlab hz).2.2.2.2,
      hp_la_measurable hs hlab, fun z hz z' hz' => ?_⟩⟩
  obtain ⟨-, hu, -, hfz, hRz⟩ := hp_la_mem hs hlab hz
  obtain ⟨-, hu', -, hfz', hRz'⟩ := hp_la_mem hs hlab hz'
  obtain ⟨hq, hnl, hf, hg, -⟩ := hs
  obtain ⟨hup, hlo⟩ := (hR Ω Ωs hq hnl lab hlab).2.1 _ hu _ hu'
  -- `d_ρ(R̃ z, R̃ z') = d_Ω(R(g z̄), R(g z̄'))` and `d_ρ(z, z') = d_{Ω*}(g z̄, g z̄')`
  have e : hpDist (hpLabelMap Ωs f g lab z) (hpLabelMap Ωs f g lab z') =
      poincareDist Ω (lab (epstein Ωs (g (conj z)))) (lab (epstein Ωs (g (conj z')))) := by
    rw [← hp_poincareDist_eq hf hRz hRz', hfz, hfz']
  have hd0 := hp_la_hpDist_nonneg hz hz'
  have hd0' := hp_la_hpDist_nonneg hRz hRz'
  rw [hp_poincareDist_eq_lower hg hz hz'] at hup hlo
  rw [e] at hd0' ⊢
  set d := hpDist z z'
  set d' := poincareDist Ω (lab (epstein Ωs (g (conj z)))) (lab (epstein Ωs (g (conj z'))))
  have hLA : (1 : ℝ) ≤ max A 1 := le_max_right _ _
  have hA : A ≤ max A 1 := le_max_left _ _
  have hB : B ≤ max B 0 := le_max_left _ _
  have hB0 : (0 : ℝ) ≤ max B 0 := le_max_right _ _
  constructor
  · have key : d ≤ max A 1 * (d' + max B 0) := by
      nlinarith [mul_le_mul_of_nonneg_right hA hd0']
    have := (inv_mul_le_iff₀ (by linarith : (0 : ℝ) < max A 1)).mpr key
    linarith
  · nlinarith [mul_le_mul_of_nonneg_right hA hd0]

/-- Helper: under Convention 11.? (`IsHPSetting`), `f` has a homeomorphic extension to the
closure of `ℍ` in `ℂ̄` (`Ω` is a Jordan domain, `s03_qce_jordan`; LZ boundary correspondence). -/
theorem s11_lb_ext {Ω Ωs : Set ℂ} {K : ℝ} {f g : ℂ → ℂ} {w : ℝ ≃ₜ ℝ}
    (hs : IsHPSetting Ω Ωs K f g w) :
    ∃ Fx : ExtPlane → ExtPlane, IsHomeoExtension f upperHalf Ω Fx :=
  thm13_3_boundary_correspondence isJordanDomain_upperHalf (s03_qce_jordan hs.1).1
    ⟨1, isKQC_one_of_conformal isOpen_upperHalf hs.2.2.1⟩ hs.2.2.1.2.2

/-- Helper: `coe` maps `𝓝[U] z` onto `𝓝[toExt U] z` in `ℂ̄`. -/
theorem s11_lb_map_nhds (U : Set ℂ) (z : ℂ) :
    map ((↑) : ℂ → ExtPlane) (𝓝[U] z) = 𝓝[toExt U] (z : ExtPlane) :=
  OnePoint.isOpenEmbedding_coe.isInducing.map_nhdsWithin_eq U z

/-- Helper (L1): the extension agrees with `f` on `ℍ ∪ ℝ` (continuity of `f` on `closedUpperHalf`). -/
theorem s11_lb_fx_real {Ω Ωs : Set ℂ} {K : ℝ} {f g : ℂ → ℂ} {w : ℝ ≃ₜ ℝ}
    (hs : IsHPSetting Ω Ωs K f g w) {Fx : ExtPlane → ExtPlane}
    (hFx : IsHomeoExtension f upperHalf Ω Fx) {z : ℂ} (hz : z ∈ closedUpperHalf) :
    Fx (z : ExtPlane) = ((f z : ℂ) : ExtPlane) ∧ (z : ExtPlane) ∈ closure (toExt upperHalf) := by
  have hcl : closure upperHalf = closedUpperHalf := closure_setOfPred_lt_im 0
  have hzc : z ∈ closure upperHalf := hcl ▸ hz
  have hmem : (z : ExtPlane) ∈ closure (toExt upperHalf) :=
    image_closure_subset_closure_image OnePoint.continuous_coe (mem_image_of_mem _ hzc)
  refine ⟨?_, hmem⟩
  haveI : (𝓝[upperHalf] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hzc
  have h1 : Tendsto (Fx ∘ ((↑) : ℂ → ExtPlane)) (𝓝[upperHalf] z) (𝓝 (Fx (z : ExtPlane))) := by
    refine ((hFx.2.1 _ hmem).tendsto.mono_left (nhdsWithin_mono _ subset_closure)).comp ?_
    rw [← s11_lb_map_nhds]
    exact tendsto_map
  have h2 : Tendsto (Fx ∘ ((↑) : ℂ → ExtPlane)) (𝓝[upperHalf] z) (𝓝 ((f z : ℂ) : ExtPlane)) := by
    have hf : Tendsto f (𝓝[upperHalf] z) (𝓝 (f z)) :=
      (hs.2.2.2.2.1 z hz).tendsto.mono_left (nhdsWithin_mono _ fun u hu => show (0 : ℝ) ≤ u.im from le_of_lt hu)
    exact ((OnePoint.continuous_coe.tendsto _).comp hf).congr'
      (eventually_nhdsWithin_of_forall fun u hu => (hFx.1 u hu).symm)
  exact tendsto_nhds_unique h1 h2

/-- Helper (L2): `g(x) = f(w⁻¹ x)` lies on the curve `Γ = (Ω ∪ Ω*)ᶜ` (injectivity of the
extension `Fx` on the closure; `Ω*` is open and disjoint from `Ω`). -/
theorem s11_lb_curve {Ω Ωs : Set ℂ} {K : ℝ} {f g : ℂ → ℂ} {w : ℝ ≃ₜ ℝ}
    (hs : IsHPSetting Ω Ωs K f g w) (x : ℝ) : g x ∈ curveOf Ω Ωs := by
  obtain ⟨hq, -, hf, hg, hfc, -⟩ := id hs
  obtain ⟨Fx, hFx⟩ := s11_lb_ext hs
  set x' : ℝ := w.symm x with hx'
  have hgx : g x = f (x' : ℂ) := by rw [hs.2.2.2.2.2.2.2.2, hx', w.apply_symm_apply]
  have hx'm : ((x' : ℝ) : ℂ) ∈ closedUpperHalf := by
    show (0 : ℝ) ≤ ((x' : ℝ) : ℂ).im
    simp
  obtain ⟨hFx', hmem⟩ := s11_lb_fx_real hs hFx hx'm
  rw [hgx]
  rintro (hΩ | hΩs)
  · rw [← hf.2.2] at hΩ
    obtain ⟨z₀, hz₀, hfz⟩ := hΩ
    have h1 : Fx ((x' : ℂ) : ExtPlane) = Fx (z₀ : ExtPlane) := by
      rw [hFx', hFx.1 z₀ hz₀, hfz]
    have h2 := OnePoint.coe_injective
      (hFx.2.2.1 hmem (subset_closure (mem_image_of_mem _ hz₀)) h1)
    have h3 : (0 : ℝ) < z₀.im := hz₀
    rw [← h2] at h3
    simp at h3
  · have hd : Disjoint Ω Ωs := s02_jordanPair_disjoint (s03_b0_jordanPair hq)
    have hΩso : IsOpen Ωs :=
      hg.isOpen (isOpen_lt Complex.continuous_im continuous_const)
    have hcl : closure upperHalf = closedUpperHalf := closure_setOfPred_lt_im 0
    have hfx : f (x' : ℂ) ∈ closure Ω := by
      rw [← hf.2.2]
      refine (hcl ▸ hfc : ContinuousOn f (closure upperHalf)).image_closure ?_
      exact mem_image_of_mem _ (hcl ▸ hx'm)
    exact disjoint_left.1 (hd.closure_left hΩso) hfx hΩs

/-- Helper (L3): `f⁻¹` is continuous at the boundary point `f(x')` (the homeomorphic extension of
`f⁻¹` given by `isHomeoExtension_invFunOn`). -/
theorem s11_lb_inv_tendsto {Ω Ωs : Set ℂ} {K : ℝ} {f g : ℂ → ℂ} {w : ℝ ≃ₜ ℝ}
    (hs : IsHPSetting Ω Ωs K f g w) (x' : ℝ) :
    Tendsto (Function.invFunOn f upperHalf) (𝓝[Ω] (f x')) (𝓝 (x' : ℂ)) := by
  have hf := hs.2.2.1
  obtain ⟨Fx, hFx⟩ := s11_lb_ext hs
  have hΨ := isHomeoExtension_invFunOn hf hFx
  set Ψ := Function.invFunOn Fx (closure (toExt upperHalf)) with hΨdef
  have hx'm : ((x' : ℝ) : ℂ) ∈ closedUpperHalf := by
    show (0 : ℝ) ≤ ((x' : ℝ) : ℂ).im
    simp
  obtain ⟨hFx', hmem⟩ := s11_lb_fx_real hs hFx hx'm
  have hpm : ((f x' : ℂ) : ExtPlane) ∈ closure (toExt Ω) := by
    rw [← hFx.2.2.2, ← hFx']
    exact mem_image_of_mem _ hmem
  have hΨp : Ψ ((f x' : ℂ) : ExtPlane) = ((x' : ℂ) : ExtPlane) := by
    rw [← hFx']
    exact hFx.2.2.1.leftInvOn_invFunOn hmem
  have h1 : Tendsto (Ψ ∘ ((↑) : ℂ → ExtPlane)) (𝓝[Ω] (f x')) (𝓝 ((x' : ℂ) : ExtPlane)) := by
    rw [← hΨp]
    refine ((hΨ.2.1 _ hpm).tendsto.mono_left (nhdsWithin_mono _ subset_closure)).comp ?_
    rw [← s11_lb_map_nhds]
    exact tendsto_map
  rw [OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff]
  exact h1.congr' (eventually_nhdsWithin_of_forall fun u hu => hΨ.1 u hu)

/-- Helper (L4): `f⁻¹ → ∞` as `u → ∞` in `Ω` (`f` maps compact parts of `ℍ ∪ ℝ` to compact sets). -/
theorem s11_lb_inv_cocompact {Ω Ωs : Set ℂ} {K : ℝ} {f g : ℂ → ℂ} {w : ℝ ≃ₜ ℝ}
    (hs : IsHPSetting Ω Ωs K f g w) :
    Tendsto (Function.invFunOn f upperHalf) (cocompact ℂ ⊓ 𝓟 Ω) (cocompact ℂ) := by
  obtain ⟨-, -, hf, -, hfc, -⟩ := id hs
  refine (hasBasis_cocompact.tendsto_right_iff).2 fun C hC => ?_
  have hcl : IsClosed closedUpperHalf := isClosed_le continuous_const Complex.continuous_im
  have hC' : IsCompact (f '' (C ∩ closedUpperHalf)) :=
    (hC.inter_right hcl).image_of_continuousOn (hfc.mono inter_subset_right)
  filter_upwards [mem_inf_of_left hC'.compl_mem_cocompact, mem_inf_of_right (mem_principal_self Ω)]
    with u hu huΩ
  intro hinC
  have hex : ∃ a ∈ upperHalf, f a = u := by
    rw [← hf.2.2] at huΩ
    exact huΩ
  have hm : Function.invFunOn f upperHalf u ∈ upperHalf := Function.invFunOn_mem hex
  exact hu ⟨_, ⟨hinC, le_of_lt (show (0 : ℝ) < _ from hm)⟩, Function.invFunOn_eq hex⟩

/-- Helper (L5): `R(z*) → ∞` as `z* → ∞` in `Ω*` (`s07_label_norm_growth`). -/
theorem s11_lb_lab_cocompact {Ω Ωs : Set ℂ} {K : ℝ} {f g : ℂ → ℂ} {w : ℝ ≃ₜ ℝ}
    {lab : ℂ × ℝ → ℂ} (hs : IsHPSetting Ω Ωs K f g w) (hlab : IsLabel Ω lab) :
    Tendsto (fun z => lab (epstein Ωs z)) (cocompact ℂ ⊓ 𝓟 Ωs) (cocompact ℂ) := by
  obtain ⟨C, hC⟩ := s07_label_norm_growth hs.1 hs.2.1 hlab
  set C' := max C 1 with hC'def
  have hC'0 : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hn : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ ⊓ 𝓟 Ωs) atTop :=
    tendsto_norm_cocompact_atTop.mono_left inf_le_left
  have hn' : Tendsto (fun z : ℂ => ‖z‖ / C' - 1) (cocompact ℂ ⊓ 𝓟 Ωs) atTop :=
    tendsto_atTop_add_const_right _ _ (hn.atTop_div_const hC'0)
  have hR : Tendsto (fun z => ‖lab (epstein Ωs z)‖) (cocompact ℂ ⊓ 𝓟 Ωs) atTop := by
    refine tendsto_atTop_mono' _ ?_ hn'
    filter_upwards [mem_inf_of_right (mem_principal_self Ωs)] with z hz
    have h1 := hC z hz
    have h2 : C * (‖lab (epstein Ωs z)‖ + 1) ≤ C' * (‖lab (epstein Ωs z)‖ + 1) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    rw [div_sub_one hC'0.ne', div_le_iff₀ hC'0]
    nlinarith
  have key : Tendsto (fun z => lab (epstein Ωs z)) (cocompact ℂ ⊓ 𝓟 Ωs) (comap norm atTop) :=
    tendsto_comap_iff.2 hR
  rwa [comap_norm_atTop, Metric.cobounded_eq_cocompact] at key

/-- Lemma 11.12(b) `lem:hp-label`, `sec11-halfplane.tex:946`: `R̃(z) → h(x) = w⁻¹(x)` as
`z → x ∈ ℝ`, and `R̃(z) → ∞` as `z → ∞`. -/
theorem lem_hp_label_b {Ω Ωs : Set ℂ} {K : ℝ} {f g : ℂ → ℂ} {w : ℝ ≃ₜ ℝ} {lab : ℂ × ℝ → ℂ}
    (hs : IsHPSetting Ω Ωs K f g w) (hlab : IsLabel Ω lab) :
    (∀ x : ℝ, Tendsto (hpLabelMap Ωs f g lab) (𝓝[upperHalf] (x : ℂ)) (𝓝 ((w.symm x : ℝ) : ℂ))) ∧
      Tendsto (hpLabelMap Ωs f g lab) (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ) := by
  -- `R̃ = f⁻¹ ∘ R ∘ g ∘ J`: `J z → x`, `g → g x ∈ Γ`, `R → g x` (`cor_R_qi`), `f⁻¹ → w⁻¹ x`
  -- (homeomorphic extension of `f⁻¹`); at `∞` the same chain with `s07_label_norm_growth`
  obtain ⟨hq, hnl, hf, hg, hfc, hgc, hfi, hgi, hfg⟩ := id hs
  obtain ⟨A, B, E, hAB⟩ := cor_R_qi K
  obtain ⟨hRΩ, -, -, hRb⟩ := hAB Ω Ωs hq hnl lab hlab
  have hJl : ∀ z ∈ upperHalf, conj z ∈ lowerHalf := fun z hz => by
    show (conj z).im < 0
    rw [Complex.conj_im]
    linarith [show (0 : ℝ) < z.im from hz]
  have hgΩs : ∀ z ∈ lowerHalf, g z ∈ Ωs := fun z hz => hg.2.2 ▸ mem_image_of_mem g hz
  constructor
  · intro x
    have hgx : f ((w.symm x : ℝ) : ℂ) = g x := by rw [hfg, w.apply_symm_apply]
    have h1 : Tendsto (fun z => conj z) (𝓝[upperHalf] (x : ℂ)) (𝓝[closedLowerHalf] (x : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨(Complex.continuous_conj.tendsto' _ _ (Complex.conj_ofReal x)).mono_left
        nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun z hz =>
          show (conj z).im ≤ 0 from le_of_lt (hJl z hz)⟩
    have hxl : ((x : ℝ) : ℂ) ∈ closedLowerHalf := by
      show ((x : ℝ) : ℂ).im ≤ 0
      simp
    have h2 : Tendsto (fun z => g (conj z)) (𝓝[upperHalf] (x : ℂ)) (𝓝[Ωs] (g x)) :=
      tendsto_nhdsWithin_iff.2 ⟨(hgc _ hxl).tendsto.comp h1,
        eventually_nhdsWithin_of_forall fun z hz => hgΩs _ (hJl z hz)⟩
    have h3 : Tendsto (fun z => lab (epstein Ωs (g (conj z)))) (𝓝[upperHalf] (x : ℂ))
        (𝓝[Ω] (g x)) :=
      tendsto_nhdsWithin_iff.2 ⟨(hRb _ (s11_lb_curve hs x)).comp h2,
        eventually_nhdsWithin_of_forall fun z hz => hRΩ _ (hgΩs _ (hJl z hz))⟩
    rw [← hgx] at h3
    exact (s11_lb_inv_tendsto hs _).comp h3
  · have hc : Tendsto (fun z => conj z) (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ ⊓ 𝓟 lowerHalf) :=
      tendsto_inf.2 ⟨(Complex.conjLIE.toHomeomorph.isClosedEmbedding.tendsto_cocompact).mono_left
        inf_le_left, tendsto_principal.2 (mem_inf_of_right (mem_principal.2 hJl))⟩
    have hg' : Tendsto g (cocompact ℂ ⊓ 𝓟 lowerHalf) (cocompact ℂ ⊓ 𝓟 Ωs) :=
      tendsto_inf.2 ⟨hgi, tendsto_principal.2 (mem_inf_of_right (mem_principal.2 hgΩs))⟩
    have hR : Tendsto (fun z => lab (epstein Ωs z)) (cocompact ℂ ⊓ 𝓟 Ωs) (cocompact ℂ ⊓ 𝓟 Ω) :=
      tendsto_inf.2 ⟨s11_lb_lab_cocompact hs hlab,
        tendsto_principal.2 (mem_inf_of_right (mem_principal.2 hRΩ))⟩
    exact (s11_lb_inv_cocompact hs).comp (hR.comp (hg'.comp hc))

/-- Helper: `S(g ∘ (-·))(z) = S g(-z)` for a conformal `g` on `𝕃` and `z ∈ ℍ`. -/
theorem hp_schwarzian_comp_neg {Ω : Set ℂ} {g : ℂ → ℂ} (hg : IsConformalOnto g lowerHalf Ω)
    {z : ℂ} (hz : z ∈ upperHalf) :
    schwarzian (g ∘ fun u : ℂ => -u) z = schwarzian g (-z) := by
  have hy : (0 : ℝ) < z.im := hz
  have hzl : -z ∈ lowerHalf := by
    show (-z).im < 0
    rw [Complex.neg_im]; linarith
  have hLo : IsOpen lowerHalf := isOpen_lt Complex.continuous_im continuous_const
  have hnA : AnalyticAt ℂ (fun u : ℂ => -u) z := by fun_prop
  have hn' : deriv (fun u : ℂ => -u) z ≠ 0 := by simp
  have hgA : AnalyticAt ℂ g (-z) := hg.1.analyticAt (hLo.mem_nhds hzl)
  have hg0 : deriv g (-z) ≠ 0 := deriv_ne_zero_of_injOn hLo hg.1 hg.2.1 hzl
  have hS : schwarzian (fun u : ℂ => -u) z = 0 := by
    have := schwarzian_mobius (a := -1) (b := 0) (c := 0) (d := 1) (by norm_num) z
    simpa using this
  rw [eq19_1_chain_rule hnA hn' hgA hg0, hS]
  simp

/-- Helper: the lower-half-plane twin of the mass part of `eq:hp-s`: for a conformal
`g : 𝕃 → Ω`, `∫ φ dm_Ω = ∫_ℍ φ(g(z̄)) dm_-(z)`. -/
theorem hp_lower_pull {Ω : Set ℂ} {g : ℂ → ℂ} (hg : IsConformalOnto g lowerHalf Ω)
    {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ w, φ w ∂curvMass Ω = ∫⁻ z, φ (g (conj z)) ∂hpSchwarzMassLower g := by
  set e : ℂ ≃ₗᵢ[ℝ] ℂ := Complex.conjLIE.trans (LinearIsometryEquiv.neg ℝ) with hedef
  have he : ∀ u, e u = -conj u := fun u => rfl
  have hmp : MeasurePreserving e volume volume := e.measurePreserving
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hD : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  have hpre : e ⁻¹' upperHalf = upperHalf := by
    ext u; simp [he, upperHalf]
  have hG := hg.comp hp_isConformalOnto_neg
  have hmap : hpSchwarzMassLower g = (hpSchwarzMass (g ∘ fun u : ℂ => -u)).map e := by
    ext t ht
    have hte : MeasurableSet (e ⁻¹' t) := hme.measurable ht
    rw [Measure.map_apply hme.measurable ht, hpSchwarzMass, hpSchwarzMassLower,
      withDensity_apply _ ht, withDensity_apply _ hte, Measure.restrict_restrict ht,
      Measure.restrict_restrict hte]
    have h := hmp.setLIntegral_comp_preimage_emb hme
      (fun u => ENNReal.ofReal (u.im ^ 2 * ‖schwarzian g (conj u)‖ ^ 2)) (t ∩ upperHalf)
    rw [← h, preimage_inter, hpre]
    refine setLIntegral_congr_fun (hte.inter hD) (fun z hz => ?_)
    rw [hp_schwarzian_comp_neg hg hz.2]
    simp [he]
  rw [(eq_hp_s hG).2.2 φ hφ, hmap, hme.lintegral_map]
  simp [he]

/-- Lemma 11.12(c) `lem:hp-label`, `sec11-halfplane.tex:947`: `K_H(f(a)) = 𝒫_{m_f}(a)` and
`K_*(f(a)) = 𝒫_{R̃_* m_-}(a)`. -/
theorem lem_hp_label_c {Ω Ωs : Set ℂ} {K : ℝ} {f g : ℂ → ℂ} {w : ℝ ≃ₜ ℝ} {lab : ℂ × ℝ → ℂ}
    (hs : IsHPSetting Ω Ωs K f g w) (hlab : IsLabel Ω lab) {a : ℂ} (ha : a ∈ upperHalf) :
    KH Ω (f a) = hpP (hpSchwarzMass f) a ∧
      Kst Ω Ωs lab (f a) = hpPOf (hpLabelMap Ωs f g lab) (hpSchwarzMassLower g) a := by
  classical
  obtain ⟨hq, hnl, hf, hg, -⟩ := id hs
  have hU : IsOpen upperHalf := isOpen_upperHalf
  have hD : MeasurableSet upperHalf := hU.measurableSet
  have hΩm : MeasurableSet Ω := by
    rw [← hf.2.2]; exact hD.image_of_continuousOn_injOn hf.1.continuousOn hf.2.1
  -- a Borel inverse of `f` on `Ω`
  set G : ℂ → ℂ := Ω.piecewise (Function.invFunOn f upperHalf) 0 with hGdef
  have hGm : Measurable G :=
    ContinuousOn.measurable_piecewise (hf.symm hU).1.continuousOn continuousOn_const hΩm
  have hleft : ∀ z ∈ upperHalf, G (f z) = z := by
    intro z hz
    have hfz : f z ∈ Ω := hf.2.2 ▸ mem_image_of_mem f hz
    simp only [hGdef, Set.piecewise_eq_of_mem _ _ _ hfz]
    exact hf.2.1.leftInvOn_invFunOn hz
  have hkm : Measurable fun z => ENNReal.ofReal (hpKernel a z) := by
    unfold hpKernel hpDist Real.arcosh; fun_prop
  set ψ : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (hpKernel a (G w)) with hψdef
  have hψm : Measurable ψ := hkm.comp hGm
  have hkern : ∀ z ∈ upperHalf, intrKernel Ω (f a) (f z) = hpKernel a z := by
    intro z hz; unfold intrKernel hpKernel; rw [hp_poincareDist_eq hf ha hz]
  have hψf : ∀ z ∈ upperHalf, ψ (f z) = ENNReal.ofReal (hpKernel a z) := by
    intro z hz; simp only [hψdef, hleft z hz]
  have hψΩ : ∀ v ∈ Ω, ENNReal.ofReal (intrKernel Ω (f a) v) = ψ v := by
    intro v hv
    rw [← hf.2.2] at hv
    obtain ⟨z, hz, rfl⟩ := hv
    rw [hψf z hz, hkern z hz]
  have hmf : ∀ᵐ z ∂hpSchwarzMass f, z ∈ upperHalf :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hD)
  have hmg : ∀ᵐ z ∂hpSchwarzMassLower g, z ∈ upperHalf :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hD)
  constructor
  · have hae : ∀ᵐ v ∂curvMass Ω, ENNReal.ofReal (intrKernel Ω (f a) v) = ψ v := by
      filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩm)]
        with v hv
      exact hψΩ v hv
    rw [KH, lintegral_congr_ae hae, (eq_hp_s hf).2.2 ψ hψm, hpP,
      Measure.restrict_eq_self_of_ae_mem hmf]
    refine lintegral_congr_ae ?_
    filter_upwards [hmf] with z hz
    exact hψf z hz
  · have hLo : IsOpen lowerHalf := isOpen_lt Complex.continuous_im continuous_const
    have hΩsm : MeasurableSet Ωs := by
      rw [← hg.2.2]
      exact hLo.measurableSet.image_of_continuousOn_injOn hg.1.continuousOn hg.2.1
    have hΩs : ∃ F : ℂ → ℂ, IsConformalOnto F unitDisc Ωs :=
      (s03_b0_basic (s03_qce_swap hq)).2.2.2
    have hX : ContinuousOn (epstein Ωs) Ωs := fun x hx =>
      (s02_epstein_differentiableAt hΩs hx).continuousAt.continuousWithinAt
    set E : ℂ → ℂ × ℝ := Ωs.piecewise (epstein Ωs) (fun _ => 0) with hEdef
    have hEm : Measurable E := hX.measurable_piecewise continuousOn_const hΩsm
    set χ : ℂ → ℝ≥0∞ := fun v => ψ (lab (E v)) with hχdef
    have hχm : Measurable χ := hψm.comp (hlab.1.comp hEm)
    obtain ⟨A, B, E', hR⟩ := cor_R_qi K
    have hae : ∀ᵐ v ∂curvMass Ωs,
        ENNReal.ofReal (intrKernel Ω (f a) (lab (epstein Ωs v))) = χ v := by
      filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩsm)]
        with v hv
      simp only [hχdef, hEdef, Set.piecewise_eq_of_mem _ _ _ hv]
      exact hψΩ _ ((hR Ω Ωs hq hnl lab hlab).1 _ hv)
    rw [Kst, lintegral_congr_ae hae, hp_lower_pull hg hχm, hpPOf,
      Measure.restrict_eq_self_of_ae_mem hmg]
    refine lintegral_congr_ae ?_
    filter_upwards [hmg] with z hz
    obtain ⟨-, hgz, -, hfR, hRz⟩ := hp_la_mem hs hlab hz
    simp only [hχdef, hEdef, Set.piecewise_eq_of_mem _ _ _ hgz]
    rw [← hfR, hψf _ hRz]

/-! ### D0: the Cayley toolkit for `lem_hp_label_d` -/

/-- Helper (D0) for `lem_hp_label_d`: the Cayley map is an isometry `(ℍ, d_ρ) → (𝔻, d_𝔻)`. -/
theorem s11_ld_hpDist_cayley {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    hpDist z w = diskDist (cayley z) (cayley w) := by
  rw [s02_diskDist_cayley (cayley_mem_unitDisc hz) (cayley_mem_unitDisc hw),
    s11_wm_hpDist_uhp hz hw]
  congr 1 <;> exact UpperHalfPlane.ext (by
    first
    | exact (cayleyInv_cayley hz).symm
    | exact (cayleyInv_cayley hw).symm)

/-- Helper (D0) for `lem_hp_label_d`: `k_a(z) = k_{C a}(C z)` for the Cayley map `C`. -/
theorem s11_ld_hpKernel_cayley {a z : ℂ} (ha : 0 < a.im) (hz : 0 < z.im) :
    hpKernel a z = diskKernel (cayley a) (cayley z) := by
  rw [sec07_kernel_formula _ _ (cayley_mem_unitDisc ha) (cayley_mem_unitDisc hz),
    ← s11_ld_hpDist_cayley ha hz]
  rfl

/-- Helper (D0) for `lem_hp_label_d`: the Cayley map on the closed half-plane `ℍ ∪ ℝ`. -/
theorem s11_ld_cayley_closed {z : ℂ} (hz : 0 ≤ z.im) :
    z + I ≠ 0 ∧ cayley z ≠ 1 ∧ cayley z ∈ closedBall (0 : ℂ) 1 ∧ cayleyInv (cayley z) = z := by
  have hden : z + I ≠ 0 := by
    intro hcon
    have him := congrArg Complex.im hcon
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at him
    linarith
  have hpos : 0 < normSq (z + I) := normSq_pos.mpr hden
  refine ⟨hden, fun h1 => ?_, ?_, ?_⟩
  · rw [cayley, div_eq_one_iff_eq hden] at h1
    have him := congrArg Complex.im h1
    simp only [Complex.sub_im, Complex.add_im, Complex.I_im] at him
    linarith
  · have hle : normSq (z - I) ≤ normSq (z + I) := by
      have h := normSq_cayley_key z
      linarith
    rw [mem_closedBall_zero_iff, cayley, norm_div, div_le_one (norm_pos_iff.mpr hden)]
    have h1 : ‖z - I‖ ^ 2 ≤ ‖z + I‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]; exact hle
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1
  · have h1 : (1 : ℂ) + cayley z = 2 * z / (z + I) := by
      rw [cayley]; field_simp; ring
    have h2 : (1 : ℂ) - cayley z = 2 * I / (z + I) := by
      rw [cayley]; field_simp; ring
    have h2ne : (1 : ℂ) - cayley z ≠ 0 := by
      rw [h2]
      exact div_ne_zero (by simp) hden
    rw [cayleyInv, div_eq_iff h2ne, h1, h2]
    field_simp

/-- Helper (D0) for `lem_hp_label_d`: the inverse Cayley map off its pole `1`. -/
theorem s11_ld_cayleyInv_ne {u : ℂ} (hu : u ≠ 1) :
    cayley (cayleyInv u) = u ∧
      (cayleyInv u).im = (1 - normSq u) / normSq (1 - u) := by
  have hden : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  refine ⟨?_, s02_cayley_im u⟩
  have h1 : cayleyInv u - I = I * (2 * u) / (1 - u) := by
    rw [cayleyInv]; field_simp; ring
  have h2 : cayleyInv u + I = I * 2 / (1 - u) := by
    rw [cayleyInv]; field_simp; ring
  have h2ne : cayleyInv u + I ≠ 0 := by
    rw [h2]
    exact div_ne_zero (by simp) hden
  rw [cayley, div_eq_iff h2ne, h1, h2]
  field_simp

/-- Helper (D0) for `lem_hp_label_d`: `C⁻¹` maps `𝔻̄ ∖ {1}` into `ℍ ∪ ℝ` and `∂𝔻 ∖ {1}` into `ℝ`. -/
theorem s11_ld_cayleyInv_closed {u : ℂ} (hu : u ∈ closedBall (0 : ℂ) 1) (hu1 : u ≠ 1) :
    0 ≤ (cayleyInv u).im ∧ (‖u‖ = 1 → (cayleyInv u).im = 0) := by
  have hden : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have hpos : 0 < normSq (1 - u) := normSq_pos.mpr hden
  have hn : normSq u ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have := mem_closedBall_zero_iff.mp hu
    nlinarith [norm_nonneg u]
  rw [(s11_ld_cayleyInv_ne hu1).2]
  refine ⟨div_nonneg (by linarith) hpos.le, fun h => ?_⟩
  rw [Complex.normSq_eq_norm_sq, h]
  simp

/-- Helper (D0) for `lem_hp_label_d`: the Cayley map is a bijection `ℍ ∪ ℝ → 𝔻̄ ∖ {1}`. -/
theorem s11_ld_cayley_bijOn :
    BijOn cayley closedUpperHalf (closedBall (0 : ℂ) 1 \ {1}) ∧ BijOn cayley upperHalf unitDisc := by
  refine ⟨⟨fun z hz => ⟨(s11_ld_cayley_closed hz).2.2.1, (s11_ld_cayley_closed hz).2.1⟩,
    fun z hz z' hz' h => ?_, fun u hu => ?_⟩, ⟨fun z hz => cayley_mem_unitDisc hz,
    isConformalOnto_cayley.2.1, fun u hu => ?_⟩⟩
  · rw [← (s11_ld_cayley_closed hz).2.2.2, h, (s11_ld_cayley_closed hz').2.2.2]
  · exact ⟨cayleyInv u, (s11_ld_cayleyInv_closed hu.1 hu.2).1, (s11_ld_cayleyInv_ne hu.2).1⟩
  · exact ⟨cayleyInv u, cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp hu),
      cayley_cayleyInv (mem_ball_zero_iff.mp hu)⟩

/-- Helper (D0) for `lem_hp_label_d`: continuity of `C` on `ℍ ∪ ℝ` and of `C⁻¹` off `1`. -/
theorem s11_ld_cayley_cont :
    ContinuousOn cayley closedUpperHalf ∧ ContinuousOn cayleyInv {u | u ≠ 1} := by
  constructor
  · intro z hz
    exact ((continuous_id.sub continuous_const).continuousAt.div
      (continuous_id.add continuous_const).continuousAt
      (s11_ld_cayley_closed hz).1).continuousWithinAt
  · intro u hu
    exact ((continuous_const.mul (continuous_const.add continuous_id)).continuousAt.div
      (continuous_const.sub continuous_id).continuousAt
      (sub_ne_zero.mpr (Ne.symm hu))).continuousWithinAt

/-- Helper (D0) for `lem_hp_label_d`: `C⁻¹(u) → ∞` as `u → 1`. -/
theorem s11_ld_cayleyInv_inf : Tendsto cayleyInv (𝓝[≠] (1 : ℂ)) (cocompact ℂ) := by
  have hn : Tendsto (fun u : ℂ => ‖1 - u‖) (𝓝[≠] (1 : ℂ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun u : ℂ => ‖1 - u‖) (𝓝 (1 : ℂ)) (𝓝 ‖(1 : ℂ) - 1‖) :=
        (continuous_const.sub continuous_id).norm.tendsto 1
      rw [sub_self, norm_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hu))
  have h2 : Tendsto (fun u : ℂ => 2 * ‖1 - u‖⁻¹ - 1) (𝓝[≠] (1 : ℂ)) atTop :=
    tendsto_atTop_add_const_right _ (-1)
      ((tendsto_inv_nhdsGT_zero.comp hn).const_mul_atTop two_pos)
  refine tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℂ) (tendsto_atTop_mono' _ ?_ h2)
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hden : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have he : cayleyInv u = 2 * I / (1 - u) - I := by
    rw [cayleyInv]; field_simp; ring
  rw [dist_zero_right, he]
  have h := norm_sub_norm_le (2 * I / (1 - u)) I
  rw [norm_div, norm_mul, norm_I, mul_one, Complex.norm_two] at h
  rw [div_eq_mul_inv] at h
  linarith


/-! ### D3: bi-Lipschitz disk diffeomorphisms are quasiconformal -/

/-- Helper (D3) for `lem_hp_label_d`: `|D(e^{iθ})| = |∂f + ∂̄f e^{-2iθ}|`. -/
theorem s11_ld_fderiv_exp {f : ℂ → ℂ} {z : ℂ} (hd : DifferentiableAt ℝ f z) (θ : ℝ) :
    ‖fderiv ℝ f z (exp (θ * I))‖ = ‖dz f z + dzbar f z * exp (-(2 * θ) * I)‖ := by
  rw [fderiv_eq_dz_dzbar hd, ← Complex.exp_conj]
  have hc : conj ((θ : ℂ) * I) = -(θ : ℂ) * I := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  have he : dz f z * exp (θ * I) + dzbar f z * exp (conj ((θ : ℂ) * I)) =
      exp (θ * I) * (dz f z + dzbar f z * exp (-(2 * θ) * I)) := by
    rw [hc, mul_add, ← mul_assoc, mul_comm (exp _) (dzbar f z), mul_assoc, ← Complex.exp_add]
    ring_nf
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Helper (D3) for `lem_hp_label_d`: an `L`-bi-Lipschitz disk diffeomorphism is
`L²`-quasiconformal on `𝔻` (the infinitesimal bounds `s07_tw_inf` give axis ratio `≤ L²`). -/
theorem s11_ld_bilip_qc {F : ℂ → ℂ} {L : ℝ} (hF : IsBiLipDiskDiffeo F L) (hL : 1 ≤ L) :
    IsKQC F unitDisc (L ^ 2) := by
  obtain ⟨G, hGD, hFG, hGF, -, -, hGc, -⟩ := s07_tw_inv hF
  obtain ⟨hFh, hFc1, hdet, hFL⟩ := hF
  obtain ⟨hFD, -⟩ := s07_sb_maps hFh hFL
  have hDo : IsOpen unitDisc := isOpen_ball
  apply isKQC_of_isC1Quasiconformal
  refine ⟨hDo, by nlinarith, hFc1, ?_, fun z hz => ?_⟩
  · have himg : F '' unitDisc = unitDisc :=
      Subset.antisymm (image_subset_iff.mpr hFD) fun w hw => ⟨G w, hGD hw, hFG w hw⟩
    have hinj : InjOn F unitDisc := fun a ha b hb h => by rw [← hGF a ha, h, hGF b hb]
    refine ⟨hFc1.continuousOn, hinj, rfl, ?_⟩
    rw [himg]
    refine hGc.congr fun w hw => ?_
    have hex : ∃ a ∈ unitDisc, F a = w := ⟨G w, hGD hw, hFG w hw⟩
    exact hinj (Function.invFunOn_mem hex) (hGD hw)
      ((Function.invFunOn_eq hex).trans (hFG w hw).symm)
  · have hd : DifferentiableAt ℝ F z :=
      (hFc1.contDiffAt (hDo.mem_nhds hz)).differentiableAt (by norm_num)
    have hdt := s07_tw_jac_det (fderiv ℝ F z)
    have hab : ‖dzbar F z‖ < ‖dz F z‖ := by
      have h0 := hdet z hz
      rw [hdt] at h0
      have e1 : Complex.normSq ((fderiv ℝ F z 1 - I * fderiv ℝ F z I) / 2) = ‖dz F z‖ ^ 2 :=
        Complex.normSq_eq_norm_sq _
      have e2 : Complex.normSq ((fderiv ℝ F z 1 + I * fderiv ℝ F z I) / 2) = ‖dzbar F z‖ ^ 2 :=
        Complex.normSq_eq_norm_sq _
      rw [e1, e2] at h0
      nlinarith [norm_nonneg (dz F z), norm_nonneg (dzbar F z)]
    refine ⟨hab, ?_⟩
    obtain ⟨-, hmax, hq⟩ := ellipse_axes hab
    set a := dz F z with ha
    set b := dzbar F z with hb
    set θ₀ : ℝ := arg (b / a) / 2 with hθ₀
    set c := b * exp (-(2 * θ₀) * I) with hc
    have hcn : ‖c‖ = ‖b‖ := by
      rw [hc, norm_mul, show -(2 * (θ₀ : ℂ)) * I = ((-(2 * θ₀) : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have hmax' : ‖a + c‖ = ‖a‖ + ‖b‖ := hmax
    -- the minimal stretch `|a| - |b|` is attained at `θ₀ + π/2`
    have hmin : ‖a - c‖ = ‖a‖ - ‖b‖ := by
      have hpar : ‖a + c‖ ^ 2 + ‖a - c‖ ^ 2 = 2 * ‖a‖ ^ 2 + 2 * ‖c‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
          ← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_sub]
        ring
      rw [hmax', hcn] at hpar
      have hsq : ‖a - c‖ ^ 2 = (‖a‖ - ‖b‖) ^ 2 := by linarith
      have hnn : 0 ≤ ‖a‖ - ‖b‖ := by linarith
      exact (pow_left_inj₀ (norm_nonneg _) hnn two_ne_zero).mp hsq
    have hθ₁ : b * exp (-(2 * ((θ₀ + π / 2 : ℝ) : ℂ)) * I) = -c := by
      rw [hc, show -(2 * ((θ₀ + π / 2 : ℝ) : ℂ)) * I = -(2 * (θ₀ : ℂ)) * I + -(π * I) by
        push_cast; ring, Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
      ring
    have hv : ∀ θ : ℝ, ‖exp ((θ : ℂ) * I)‖ = 1 := fun θ => Complex.norm_exp_ofReal_mul_I θ
    have hup := (s07_tw_inf hFD hFL hz hd (exp ((θ₀ : ℂ) * I))).2
    have hlo := (s07_tw_inf hFD hFL hz hd (exp (((θ₀ + π / 2 : ℝ) : ℂ) * I))).1
    rw [s11_ld_fderiv_exp hd, hv] at hup hlo
    rw [← ha, ← hb] at hup hlo
    rw [hθ₁, ← sub_eq_add_neg, hmin] at hlo
    rw [← hc, hmax'] at hup
    have hvz := s07_varpi_pos hz
    have hvF := s07_varpi_pos (hFD hz)
    have hpos : 0 < ‖a‖ - ‖b‖ := by linarith
    rw [← hq, div_le_iff₀ hpos]
    have h1 : varpi z * (‖a‖ + ‖b‖) ≤ L * (L * varpi z * (‖a‖ - ‖b‖)) := by
      calc varpi z * (‖a‖ + ‖b‖) ≤ L * varpi (F z) * 1 := hup
        _ = L * (varpi (F z) * 1) := by ring
        _ ≤ L * (L * varpi z * (‖a‖ - ‖b‖)) :=
          mul_le_mul_of_nonneg_left hlo (by linarith)
    have h2 : varpi z * (‖a‖ + ‖b‖) ≤ varpi z * (L ^ 2 * (‖a‖ - ‖b‖)) := by
      nlinarith
    exact le_of_mul_le_mul_left h2 hvz


/-! ### D1: the welding extension `H = J ∘ F₁⁻¹ ∘ G₁ ∘ J` -/

/-- Helper (D1) for `lem_hp_label_d`: a quasiconformal map of `ℂ` onto `ℂ` is a homeomorphism,
with inverse `invFunOn F univ`. -/
theorem s11_ld_homeo {F : ℂ → ℂ} {K : ℝ} (hF : IsKQC F univ K) (hFs : F '' univ = univ) :
    ∃ e : ℂ ≃ₜ ℂ, ⇑e = F ∧ ⇑e.symm = Function.invFunOn F univ := by
  obtain ⟨-, -, ⟨hc, hi, -, hinv⟩, -⟩ := hF
  have hinj : Function.Injective F := injOn_univ.mp hi
  have hsurj : Function.Surjective F := fun y => by
    have : y ∈ F '' univ := by rw [hFs]; exact mem_univ y
    obtain ⟨x, -, hx⟩ := this
    exact ⟨x, hx⟩
  set E := Equiv.ofBijective F ⟨hinj, hsurj⟩ with hE
  have hsymm : ⇑E.symm = Function.invFunOn F univ := by
    funext y
    have hex : ∃ x ∈ (univ : Set ℂ), F x = y := ⟨E.symm y, mem_univ _, E.apply_symm_apply y⟩
    apply hinj
    rw [Function.invFunOn_eq hex]
    exact E.apply_symm_apply y
  refine ⟨⟨E, continuousOn_univ.mp hc, ?_⟩, rfl, hsymm⟩
  rw [hFs] at hinv
  change Continuous (⇑E.symm)
  rw [hsymm]
  exact continuousOn_univ.mp hinv

/-- Helper (D1) for `lem_hp_label_d`: the welding extension.  With `F₁, G₁` the `Q`-q.c.
extensions of `f, g` (`set_hp_extension`), `H = J ∘ F₁⁻¹ ∘ G₁ ∘ J` is a homeomorphism of `ℂ`,
`Q²`-q.c. on `ℍ`, mapping `ℍ` onto `ℍ`, with `H = w⁻¹` on `ℝ`. -/
theorem s11_ld_weld {Ω Ωs : Set ℂ} {K Q : ℝ} {f g : ℂ → ℂ} {w : ℝ ≃ₜ ℝ}
    (hs : IsHPSetting Ω Ωs K f g w) {F₁ G₁ : ℂ → ℂ} (hF₁ : IsKQC F₁ univ Q)
    (hF₁s : F₁ '' univ = univ) (hF₁e : EqOn F₁ f closedUpperHalf) (hG₁ : IsKQC G₁ univ Q)
    (hG₁s : G₁ '' univ = univ) (hG₁e : EqOn G₁ g closedLowerHalf) :
    ∃ H : ℂ ≃ₜ ℂ, IsKQC H upperHalf (Q * Q) ∧ H '' upperHalf = upperHalf ∧
      ∀ x : ℝ, H (x : ℂ) = ((w.symm x : ℝ) : ℂ) := by
  have hcurve : ∀ x : ℝ, g (x : ℂ) ∉ Ω ∧ g (x : ℂ) ∉ Ωs := fun x => by
    have h := s11_lb_curve hs x
    simp only [curveOf, mem_compl_iff, mem_union, not_or] at h
    exact h
  obtain ⟨⟨Fq, hFq, -, hFqU, hFqL⟩, -, hf, hg, -, -, -, -, hw⟩ := hs
  obtain ⟨eF, heF, heFs⟩ := s11_ld_homeo hF₁ hF₁s
  obtain ⟨eG, heG, -⟩ := s11_ld_homeo hG₁ hG₁s
  have hUo : IsOpen upperHalf := isOpen_upperHalf
  have hLo : IsOpen lowerHalf := isOpen_lt continuous_im continuous_const
  -- `Ω` and `Ωs` are disjoint
  have hFqi : InjOn Fq univ := hFq.2.2.1.2.1
  have hdisj : ∀ y, y ∈ Ω → y ∉ Ωs := by
    rintro y hy hy'
    rw [← hFqU] at hy
    rw [← hFqL] at hy'
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨b, hb, hab⟩ := hy'
    have := hFqi (mem_univ b) (mem_univ a) hab
    subst this
    have h1 : 0 < b.im := ha
    have h2 : b.im < 0 := hb
    linarith
  have hgf : ∀ x : ℝ, g (x : ℂ) = f ((w.symm x : ℝ) : ℂ) := fun x => by
    rw [hw, w.apply_symm_apply]
  have hcU : ∀ x : ℝ, (x : ℂ) ∈ closedUpperHalf := fun x => show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hcL : ∀ x : ℝ, (x : ℂ) ∈ closedLowerHalf := fun x => show (x : ℂ).im ≤ 0 by simp
  have hre : ∀ z : ℂ, z.im = 0 → z = (z.re : ℂ) := fun z h => Complex.ext (by simp) (by simp [h])
  -- `Ωs ⊆ F₁(𝕃)` and `Ω ⊆ G₁(ℍ)`
  have hα : ∀ y ∈ Ωs, ∃ u, u.im < 0 ∧ F₁ u = y := by
    intro y hy
    obtain ⟨z, hz⟩ := eF.surjective y
    rw [heF] at hz
    rcases lt_trichotomy z.im 0 with h | h | h
    · exact ⟨z, h, hz⟩
    · exfalso
      rw [hre z h, hF₁e (hcU _), hw] at hz
      exact (hcurve _).2 (hz ▸ hy)
    · exfalso
      have : F₁ z ∈ Ω := by rw [hF₁e (le_of_lt h)]; exact hf.2.2 ▸ mem_image_of_mem f h
      exact hdisj y (hz ▸ this) hy
  have hβ : ∀ y ∈ Ω, ∃ u, 0 < u.im ∧ G₁ u = y := by
    intro y hy
    obtain ⟨z, hz⟩ := eG.surjective y
    rw [heG] at hz
    rcases lt_trichotomy z.im 0 with h | h | h
    · exfalso
      have : G₁ z ∈ Ωs := by rw [hG₁e (le_of_lt h)]; exact hg.2.2 ▸ mem_image_of_mem g h
      exact hdisj y hy (hz ▸ this)
    · exfalso
      rw [hre z h, hG₁e (hcL _)] at hz
      exact (hcurve _).1 (hz ▸ hy)
    · exact ⟨z, h, hz⟩
  -- `φ = F₁⁻¹ ∘ G₁`
  set φ : ℂ ≃ₜ ℂ := eG.trans eF.symm with hφ
  have hφa : ∀ z, φ z = eF.symm (G₁ z) := fun z => by rw [← heG]; rfl
  have hφL : ∀ z : ℂ, z.im < 0 → (φ z).im < 0 := by
    intro z hz
    have hgz : G₁ z ∈ Ωs := by rw [hG₁e (le_of_lt hz)]; exact hg.2.2 ▸ mem_image_of_mem g hz
    obtain ⟨u, hu, hFu⟩ := hα _ hgz
    rw [hφa, ← hFu, ← heF, eF.symm_apply_apply]
    exact hu
  have hφR : ∀ x : ℝ, φ (x : ℂ) = ((w.symm x : ℝ) : ℂ) := by
    intro x
    rw [hφa, hG₁e (hcL x), hgf, ← hF₁e (hcU _), ← heF, eF.symm_apply_apply]
  have hφU' : ∀ z : ℂ, 0 < (φ z).im → 0 < z.im := by
    intro z hz
    have h1 : G₁ z = F₁ (φ z) := by rw [hφa, ← heF, eF.apply_symm_apply]
    have h2 : F₁ (φ z) ∈ Ω := by
      rw [hF₁e (le_of_lt hz)]; exact hf.2.2 ▸ mem_image_of_mem f hz
    obtain ⟨u, hu, hGu⟩ := hβ _ h2
    have : u = z := eG.injective (by rw [heG, hGu, h1])
    exact this ▸ hu
  have hφreal : ∀ z : ℂ, (φ z).im = 0 → z.im = 0 := by
    intro z hz
    have h := hφR (w (φ z).re)
    rw [w.symm_apply_apply, ← hre _ hz] at h
    have := φ.injective h
    rw [← this]
    simp
  -- `φ(ℍ) ⊆ ℍ` by connectedness
  have hφU : ∀ z : ℂ, 0 < z.im → 0 < (φ z).im := by
    have hconv : Convex ℝ upperHalf := by
      intro x hx y hy a b ha hb hab
      show 0 < (a • x + b • y).im
      have hx' : 0 < x.im := hx
      have hy' : 0 < y.im := hy
      simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
      rcases ha.lt_or_eq with ha' | ha'
      · nlinarith
      · rw [← ha'] at hab ⊢
        simp only [zero_add] at hab
        rw [hab]; simp [hy']
    have hpre : IsPreconnected (φ '' upperHalf) :=
      hconv.isPreconnected.image φ φ.continuous.continuousOn
    have hsub : φ '' upperHalf ⊆ upperHalf ∪ lowerHalf := by
      rintro _ ⟨z, hz, rfl⟩
      rcases lt_trichotomy (φ z).im 0 with h | h | h
      · exact Or.inr h
      · exfalso
        have := hφreal z h
        have hz' : 0 < z.im := hz
        linarith
      · exact Or.inl h
    have hne : (φ '' upperHalf ∩ upperHalf).Nonempty := by
      refine ⟨I, ⟨φ.symm I, hφU' _ ?_, φ.apply_symm_apply I⟩, show (0 : ℝ) < I.im by simp⟩
      rw [φ.apply_symm_apply]; simp
    have hdj : Disjoint upperHalf lowerHalf := Set.disjoint_left.mpr fun z h1 h2 => by
      have a1 : 0 < z.im := h1
      have a2 : z.im < 0 := h2
      linarith
    have key := hpre.subset_left_of_subset_union hUo hLo hdj hsub hne
    exact fun z hz => key ⟨z, hz, rfl⟩
  -- `H = J ∘ φ ∘ J`
  set J : ℂ ≃ₜ ℂ := Complex.conjLIE.toHomeomorph with hJ
  set H : ℂ ≃ₜ ℂ := J.trans (φ.trans J) with hHdef
  have hH : ∀ z, H z = conj (φ (conj z)) := fun z => rfl
  have hqcL : IsKQC φ lowerHalf (Q * Q) := by
    have h1 : IsKQC G₁ lowerHalf Q := ac_t_isKQC_restrict hG₁ hLo (subset_univ _)
    have h2 : IsKQC (Function.invFunOn F₁ univ) univ Q := by
      have := thm7_2_inv hF₁
      rwa [hF₁s] at this
    have h3 := thm7_1_comp h1 h2 (subset_univ _)
    exact ad_isKQC_congr h3 fun z _ => by rw [hφa, heFs]; rfl
  have hcl : (conj '' lowerHalf : Set ℂ) = upperHalf := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' : u.im < 0 := hu
      show 0 < (conj u).im
      rw [Complex.conj_im]
      linarith
    · intro hz
      have hz' : 0 < z.im := hz
      refine ⟨conj z, ?_, Complex.conj_conj z⟩
      show (conj z).im < 0
      rw [Complex.conj_im]
      linarith
  have hqc : IsKQC H upperHalf (Q * Q) := by
    have := eq_hp_reflection_qc hqcL
    rw [hcl] at this
    exact ad_isKQC_congr this fun z _ => hH z
  refine ⟨H, hqc, ?_, fun x => ?_⟩
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : 0 < z.im := hz
      have h1 : (conj z).im < 0 := by rw [Complex.conj_im]; linarith
      have h2 := hφL _ h1
      show 0 < (H z).im
      rw [hH, Complex.conj_im]
      linarith
    · intro hy
      have hy' : 0 < y.im := hy
      set v := φ.symm (conj y) with hv
      have hφv : φ v = conj y := φ.apply_symm_apply _
      have hvL : v.im < 0 := by
        rcases lt_trichotomy v.im 0 with h | h | h
        · exact h
        · exfalso
          rw [hre v h, hφR] at hφv
          have := congrArg Complex.im hφv
          simp only [Complex.ofReal_im, Complex.conj_im] at this
          linarith
        · exfalso
          have := hφU v h
          rw [hφv, Complex.conj_im] at this
          linarith
      refine ⟨conj v, show 0 < (conj v).im by rw [Complex.conj_im]; linarith, ?_⟩
      rw [hH, Complex.conj_conj, hφv, Complex.conj_conj]
  · rw [hH, Complex.conj_ofReal, hφR, Complex.conj_ofReal]


/-! ### D2: the disk extension and the Douady–Earle map -/

/-- Helper (D2) for `lem_hp_label_d`: conjugating a `K₀`-q.c. homeomorphism `H` of `ℂ` with
`H(ℍ) = ℍ`, `H(ℝ) ⊆ ℝ` by the Cayley map gives a `K₀`-q.c. extension to `𝔻` of the circle map
`h_𝔻 = C ∘ H ∘ C⁻¹` (`h_𝔻(1) = 1`), which is therefore a circle homeomorphism. -/
theorem s11_ld_disk {H : ℂ ≃ₜ ℂ} {K₀ : ℝ} (hHq : IsKQC H upperHalf K₀)
    (hHs : H '' upperHalf = upperHalf) (hHR : ∀ x : ℝ, (H (x : ℂ)).im = 0) :
    ∃ hD : ℂ → ℂ, hD 1 = 1 ∧ (∀ ζ, ζ ≠ 1 → hD ζ = cayley (H (cayleyInv ζ))) ∧
      AdmitsQCDiskExt hD K₀ ∧ IsCircleHomeo hD := by
  obtain ⟨HD, hHD⟩ : ∃ HD : ℂ → ℂ, HD = cayley ∘ (⇑H ∘ cayleyInv) := ⟨_, rfl⟩
  have hHDa : ∀ u, HD u = cayley (H (cayleyInv u)) := fun u => by rw [hHD]; rfl
  have hq : IsKQC HD unitDisc K₀ := by
    have h1 := isKQC_one_of_conformal isOpen_ball hp_isConformalOnto_cayleyInv
    have h2 := thm7_1_comp h1 hHq hp_isConformalOnto_cayleyInv.2.2.le
    have h3 := thm7_1_comp h2 (isKQC_one_of_conformal isOpen_upperHalf isConformalOnto_cayley)
      (by rw [image_comp]; exact (image_mono hp_isConformalOnto_cayleyInv.2.2.le).trans hHs.le)
    rw [show (1 : ℝ) * K₀ * 1 = K₀ by ring] at h3
    rw [hHD]
    exact h3
  have himg : HD '' unitDisc = unitDisc := by
    rw [hHD, image_comp, image_comp, hp_isConformalOnto_cayleyInv.2.2, hHs,
      isConformalOnto_cayley.2.2]
  obtain ⟨hD, hhD⟩ : ∃ hD : ℂ → ℂ, hD = fun ζ => if ζ = 1 then 1 else HD ζ := ⟨_, rfl⟩
  have hD1 : hD 1 = 1 := by rw [hhD]; simp
  have hDne : ∀ ζ, ζ ≠ 1 → hD ζ = cayley (H (cayleyInv ζ)) := fun ζ hζ => by
    rw [hhD]; simp only [hζ, if_false]; exact hHDa ζ
  have hbd : HasDiskBoundaryValues HD hD := by
    intro ζ hζ
    by_cases h1 : ζ = 1
    · subst h1
      rw [hD1]
      have hci : Tendsto cayleyInv (𝓝[unitDisc] (1 : ℂ)) (cocompact ℂ) :=
        s11_ld_cayleyInv_inf.mono_left (nhdsWithin_mono _ fun u hu h => by
          rw [h, unitDisc, mem_ball_zero_iff, norm_one] at hu
          exact lt_irrefl _ hu)
      have hH' : Tendsto H (cocompact ℂ) (cocompact ℂ) := H.map_cocompact.le
      have := s11_wm_cayley_inf.comp (hH'.comp hci)
      exact this.congr fun u => (hHDa u).symm
    · rw [hDne ζ h1]
      have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
      have him := (s11_ld_cayleyInv_closed (sphere_subset_closedBall hζ) h1).2 hζ1
      have hre : cayleyInv ζ = ((cayleyInv ζ).re : ℂ) :=
        Complex.ext (by simp) (by simp [him])
      have hHim : (H (cayleyInv ζ)).im = 0 := by rw [hre]; exact hHR _
      have hden : H (cayleyInv ζ) + I ≠ 0 := (s11_ld_cayley_closed (le_of_eq hHim.symm)).1
      have hc1 : ContinuousAt cayleyInv ζ :=
        s11_ld_cayley_cont.2.continuousAt (isOpen_ne.mem_nhds h1)
      have hc2 : ContinuousAt cayley (H (cayleyInv ζ)) :=
        (continuous_id.sub continuous_const).continuousAt.div
          (continuous_id.add continuous_const).continuousAt hden
      have hc : ContinuousAt HD ζ := by
        rw [hHD]
        exact ContinuousAt.comp (g := cayley) (f := ⇑H ∘ cayleyInv) hc2
          ((H.continuous.continuousAt (x := cayleyInv ζ)).comp hc1)
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := unitDisc))
      rwa [hHDa] at this
  exact ⟨hD, hD1, hDne, ⟨HD, hq, himg, hbd⟩, s07_circleHomeo_of_qcExt hq himg hbd⟩

/-- Helper (D2) for `lem_hp_label_d`: the Douady–Earle map `F_𝔻 = E(h_𝔻)` of `thm_DE`, an
`L(K₀)`-bi-Lipschitz analytic disk diffeomorphism fixing `1`, with `F_𝔻 = C ∘ H ∘ C⁻¹` on `∂𝔻`. -/
theorem s11_ld_DE (K₀ : ℝ) (hK₀ : 1 ≤ K₀) : ∃ L : ℝ, 1 ≤ L ∧
    ∀ H : ℂ ≃ₜ ℂ, IsKQC H upperHalf K₀ → H '' upperHalf = upperHalf →
      (∀ x : ℝ, (H (x : ℂ)).im = 0) →
      ∃ FD : ℂ → ℂ, IsBiLipDiskDiffeo FD L ∧ AnalyticOnNhd ℝ FD unitDisc ∧ FD 1 = 1 ∧
        ∀ ζ ∈ sphere (0 : ℂ) 1, ζ ≠ 1 → FD ζ = cayley (H (cayleyInv ζ)) := by
  obtain ⟨L, hL, hDE⟩ := thm_DE K₀ hK₀
  refine ⟨L, hL, fun H hHq hHs hHR => ?_⟩
  obtain ⟨hD, hD1, hDne, hadm, hcirc⟩ := s11_ld_disk hHq hHs hHR
  obtain ⟨FD, hFh, hEq, hAn, hdet, hbl⟩ := hDE hD hcirc
  have h1 : (1 : ℂ) ∈ sphere (0 : ℂ) 1 := by simp
  refine ⟨FD, ⟨hFh, hAn.contDiffOn isOpen_ball.uniqueDiffOn, hdet, hbl hadm⟩, hAn, by rw [hEq h1, hD1],
    fun ζ hζ hζ1 => by rw [hEq hζ, hDne ζ hζ1]⟩


/-! ### D4: the map `F = C⁻¹ ∘ F_𝔻 ∘ C` -/

/-- Helper (D4) for `lem_hp_label_d`: the real derivative of a holomorphic map is
multiplication by `f'`, with Jacobian `|f'|²`. -/
theorem s11_ld_cderiv {g : ℂ → ℂ} {d p : ℂ} (h : HasDerivAt g d p) :
    HasFDerivAt g ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ) p ∧
      LinearMap.det (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ :
        ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = Complex.normSq d := by
  refine ⟨h.hasFDerivAt.restrictScalars ℝ, ?_⟩
  set D : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ
  have hD1 : D 1 = d := by simp [D]
  have hDI : D I = I * d := by simp [D]
  have := s07_tw_jac_det D
  rw [hD1, hDI, show (d - I * (I * d)) / 2 = d by linear_combination (-d / 2) * I_sq,
    show (d + I * (I * d)) / 2 = 0 by linear_combination (d / 2) * I_sq, map_zero, sub_zero] at this
  exact this

/-- Helper (D4) for `lem_hp_label_d`: the properties of `F = C⁻¹ ∘ F_𝔻 ∘ C` on `ℍ ∪ ℝ` for the
Douady–Earle map `F_𝔻` of `s11_ld_DE` (everything in the conclusion except the kernel bounds). -/
theorem s11_ld_F {FD : ℂ → ℂ} {L : ℝ} (hFD : IsBiLipDiskDiffeo FD L)
    (hAn : AnalyticOnNhd ℝ FD unitDisc) (hF1 : FD 1 = 1) {H : ℂ → ℂ}
    (hHR : ∀ x : ℝ, (H (x : ℂ)).im = 0)
    (hb : ∀ ζ ∈ sphere (0 : ℂ) 1, ζ ≠ 1 → FD ζ = cayley (H (cayleyInv ζ))) :
    ContinuousOn (cayleyInv ∘ FD ∘ cayley) closedUpperHalf ∧
      BijOn (cayleyInv ∘ FD ∘ cayley) closedUpperHalf closedUpperHalf ∧
      Tendsto (cayleyInv ∘ FD ∘ cayley) (cocompact ℂ ⊓ 𝓟 closedUpperHalf) (cocompact ℂ) ∧
      (∀ x : ℝ, (cayleyInv ∘ FD ∘ cayley) (x : ℂ) = H x) ∧
      BijOn (cayleyInv ∘ FD ∘ cayley) upperHalf upperHalf ∧
      AnalyticOnNhd ℝ (cayleyInv ∘ FD ∘ cayley) upperHalf ∧
      (∀ z ∈ upperHalf,
        0 < LinearMap.det (fderiv ℝ (cayleyInv ∘ FD ∘ cayley) z : ℂ →ₗ[ℝ] ℂ)) ∧
      (∀ z ∈ upperHalf, ∀ z' ∈ upperHalf,
        hpDist ((cayleyInv ∘ FD ∘ cayley) z) ((cayleyInv ∘ FD ∘ cayley) z') ≤ L * hpDist z z' ∧
          hpDist z z' ≤ L * hpDist ((cayleyInv ∘ FD ∘ cayley) z) ((cayleyInv ∘ FD ∘ cayley) z')) ∧
      IsKQC (cayleyInv ∘ FD ∘ cayley) upperHalf (L ^ 2) := by
  obtain ⟨G, hGD, hFG, -, -, -, -, -⟩ := s07_tw_inv hFD
  have hqcD := s11_ld_bilip_qc hFD (s07_sb_maps hFD.1 hFD.2.2.2).2
  obtain ⟨⟨hFb, hFc⟩, hFc1, hdet, hFL⟩ := hFD
  obtain ⟨hFD, hL⟩ := s07_sb_maps ⟨hFb, hFc⟩ hFL
  have hDo : IsOpen unitDisc := isOpen_ball
  set S : Set ℂ := closedBall (0 : ℂ) 1 \ {1} with hS
  have h1cb : (1 : ℂ) ∈ closedBall (0 : ℂ) 1 := by simp
  obtain ⟨hcb, hcbo⟩ := s11_ld_cayley_bijOn
  -- `F_𝔻` on `𝔻̄ ∖ {1}` and on `𝔻`
  have hFS : BijOn FD S S := by
    refine ⟨fun u hu => ⟨hFb.mapsTo hu.1, fun h => hu.2 ?_⟩, hFb.injOn.mono diff_subset,
      fun v hv => ?_⟩
    · exact hFb.injOn hu.1 h1cb (h.trans hF1.symm)
    · obtain ⟨u, hu, rfl⟩ := hFb.surjOn hv.1
      exact ⟨u, ⟨hu, fun h => hv.2 (by rw [h, hF1]; rfl)⟩, rfl⟩
  have hFDb : BijOn FD unitDisc unitDisc :=
    ⟨hFD, hFb.injOn.mono ball_subset_closedBall, fun v hv => ⟨G v, hGD hv, hFG v hv⟩⟩
  -- `C⁻¹` on `𝔻̄ ∖ {1}` and on `𝔻`
  have hciS : BijOn cayleyInv S closedUpperHalf :=
    InvOn.bijOn ⟨fun u hu => (s11_ld_cayleyInv_ne hu.2).1,
      fun z hz => (s11_ld_cayley_closed hz).2.2.2⟩
      (fun u hu => (s11_ld_cayleyInv_closed hu.1 hu.2).1) hcb.mapsTo
  have hciD : BijOn cayleyInv unitDisc upperHalf :=
    InvOn.bijOn ⟨fun u hu => cayley_cayleyInv (mem_ball_zero_iff.mp hu),
      fun z hz => cayleyInv_cayley hz⟩
      (fun u hu => cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp hu)) hcbo.mapsTo
  have hbij := hciS.comp (hFS.comp hcb)
  have hbijo := hciD.comp (hFDb.comp hcbo)
  have hSne : ∀ u ∈ S, u ≠ 1 := fun u hu => hu.2
  -- the boundary values
  have hreal : ∀ x : ℝ, (cayleyInv ∘ FD ∘ cayley) (x : ℂ) = H x := by
    intro x
    have hx : (0 : ℝ) ≤ (x : ℂ).im := by simp
    obtain ⟨-, hne, -, hinv⟩ := s11_ld_cayley_closed hx
    have hsph : cayley (x : ℂ) ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, cayley, norm_div,
        div_eq_one_iff_eq (norm_ne_zero_iff.mpr (s11_ld_cayley_closed hx).1)]
      have h := normSq_cayley_key (x : ℂ)
      simp only [Complex.ofReal_im, mul_zero, sub_eq_zero] at h
      have h2 : ‖(x : ℂ) - I‖ ^ 2 = ‖(x : ℂ) + I‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, h]
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
    show cayleyInv (FD (cayley x)) = H x
    rw [hb _ hsph hne, hinv]
    exact (s11_ld_cayley_closed (le_of_eq (hHR x).symm)).2.2.2
  refine ⟨?_, hbij, ?_, hreal, hbijo, ?_, ?_, ?_, ?_⟩
  · -- continuity on `ℍ ∪ ℝ`
    refine s11_ld_cayley_cont.2.comp (hFc.comp s11_ld_cayley_cont.1
      (fun z hz => (hcb.mapsTo hz).1)) ?_
    intro z hz
    exact hSne _ ((hFS.comp hcb).mapsTo hz)
  · -- `∞ ↦ ∞`
    have h1 : Tendsto cayley (cocompact ℂ ⊓ 𝓟 closedUpperHalf) (𝓝[S] 1) :=
      tendsto_nhdsWithin_iff.mpr ⟨s11_wm_cayley_inf.mono_left inf_le_left,
        mem_inf_of_right (mem_principal.mpr fun z hz => hcb.mapsTo hz)⟩
    have h2 : Tendsto FD (𝓝[S] 1) (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have := (hFc 1 h1cb).tendsto.mono_left
          (nhdsWithin_mono _ (diff_subset : S ⊆ closedBall 0 1))
        rwa [hF1] at this
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact hSne _ (hFS.mapsTo hu)
    exact s11_ld_cayleyInv_inf.comp (h2.comp h1)
  · -- analyticity
    intro z hz
    have hcz := cayley_mem_unitDisc hz
    have h1 : AnalyticAt ℝ cayley z :=
      (isConformalOnto_cayley.1.analyticAt (isOpen_upperHalf.mem_nhds hz)).restrictScalars
    have h3 : AnalyticAt ℝ cayleyInv (FD (cayley z)) :=
      (hp_isConformalOnto_cayleyInv.1.analyticAt (hDo.mem_nhds (hFD hcz))).restrictScalars
    exact AnalyticAt.comp (g := cayleyInv) (f := FD ∘ cayley) h3 ((hAn _ hcz).comp h1)
  · -- the Jacobian
    intro z hz
    have hcz := cayley_mem_unitDisc hz
    have hden := cayley_den_ne_zero hz
    have hc : HasDerivAt cayley ((1 * (z + I) - (z - I) * 1) / (z + I) ^ 2) z := by
      unfold cayley
      exact ((hasDerivAt_id' z).sub_const I).div ((hasDerivAt_id' z).add_const I) hden
    have hcne : (1 * (z + I) - (z - I) * 1) / (z + I) ^ 2 ≠ 0 := by
      rw [show 1 * (z + I) - (z - I) * 1 = 2 * I by ring]
      exact div_ne_zero (by simp) (pow_ne_zero 2 hden)
    have hw : ‖FD (cayley z)‖ < 1 := mem_ball_zero_iff.mp (hFD hcz)
    have hi := hp_hasDerivAt_cayleyInv hw
    have hine : 2 * I / (1 - FD (cayley z)) ^ 2 ≠ 0 :=
      div_ne_zero (by simp) (pow_ne_zero 2 (cayleyInv_den_ne_zero hw))
    have hFd : HasFDerivAt FD (fderiv ℝ FD (cayley z)) (cayley z) :=
      ((hFc1.contDiffAt (hDo.mem_nhds hcz)).differentiableAt (by norm_num)).hasFDerivAt
    obtain ⟨hc1, hc2⟩ := s11_ld_cderiv hc
    obtain ⟨hi1, hi2⟩ := s11_ld_cderiv hi
    have hall := hi1.comp z (hFd.comp z hc1)
    have hcomp : ∀ A B C : ℂ →L[ℝ] ℂ, ((A.comp (B.comp C) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) =
        (A : ℂ →ₗ[ℝ] ℂ).comp ((B : ℂ →ₗ[ℝ] ℂ).comp (C : ℂ →ₗ[ℝ] ℂ)) := fun _ _ _ => rfl
    rw [hall.fderiv, hcomp, LinearMap.det_comp, LinearMap.det_comp, hc2, hi2]
    have := hdet _ hcz
    exact mul_pos (Complex.normSq_pos.mpr hine) (mul_pos this (Complex.normSq_pos.mpr hcne))
  · -- bi-Lipschitz for `d_ρ`
    intro z hz z' hz'
    have hcz := cayley_mem_unitDisc hz
    have hcz' := cayley_mem_unitDisc hz'
    have hm : ∀ u, u ∈ upperHalf → (cayleyInv ∘ FD ∘ cayley) u ∈ upperHalf :=
      fun u hu => hbijo.mapsTo hu
    have e : ∀ u, u ∈ upperHalf →
        cayley ((cayleyInv ∘ FD ∘ cayley) u) = FD (cayley u) := fun u hu =>
      cayley_cayleyInv (mem_ball_zero_iff.mp (hFD (cayley_mem_unitDisc hu)))
    rw [s11_ld_hpDist_cayley (hm z hz) (hm z' hz'), s11_ld_hpDist_cayley hz hz', e z hz, e z' hz']
    exact hFL _ hcz _ hcz'
  · -- quasiconformality
    have h1 := thm7_1_comp (isKQC_one_of_conformal isOpen_upperHalf isConformalOnto_cayley) hqcD
      isConformalOnto_cayley.2.2.le
    have h2 := thm7_1_comp h1 (isKQC_one_of_conformal hDo hp_isConformalOnto_cayleyInv)
      (by rw [image_comp, isConformalOnto_cayley.2.2]; exact image_subset_iff.mpr hFD)
    rw [show (1 : ℝ) * L ^ 2 * 1 = L ^ 2 by ring] at h2
    exact h2


/-! ### D5: the label map stays close to `F`, and the kernel bounds -/

/-- Helper (D5) for `lem_hp_label_d`: `R̃ = hpLabelMap` stays within `L D_*(L L_A, L c_A)` of
`F = C⁻¹ ∘ F_𝔻 ∘ C` (`lem_same_boundary` for `C ∘ R̃ ∘ C⁻¹`, whose boundary values are those of
`F_𝔻` by `lem_hp_label_b`). -/
theorem s11_ld_close {Ω Ωs : Set ℂ} {K : ℝ} {f g : ℂ → ℂ} {w : ℝ ≃ₜ ℝ} {lab : ℂ × ℝ → ℂ}
    (hs : IsHPSetting Ω Ωs K f g w) (hlab : IsLabel Ω lab) {LA cA : ℝ}
    (hRm : MapsTo (hpLabelMap Ωs f g lab) upperHalf upperHalf)
    (hRq : ∀ z ∈ upperHalf, ∀ z' ∈ upperHalf,
      LA⁻¹ * hpDist z z' - cA ≤ hpDist (hpLabelMap Ωs f g lab z) (hpLabelMap Ωs f g lab z') ∧
      hpDist (hpLabelMap Ωs f g lab z) (hpLabelMap Ωs f g lab z') ≤ LA * hpDist z z' + cA)
    {FD : ℂ → ℂ} {L : ℝ} (hFD : IsBiLipDiskDiffeo FD L) (hF1 : FD 1 = 1) {H : ℂ → ℂ}
    (hHw : ∀ x : ℝ, H (x : ℂ) = ((w.symm x : ℝ) : ℂ))
    (hb : ∀ ζ ∈ sphere (0 : ℂ) 1, ζ ≠ 1 → FD ζ = cayley (H (cayleyInv ζ))) :
    ∀ z ∈ upperHalf, hpDist (hpLabelMap Ωs f g lab z) ((cayleyInv ∘ FD ∘ cayley) z) ≤
      L * morseD (L * LA) (L * cA) := by
  set R := hpLabelMap Ωs f g lab with hRdef
  obtain ⟨hRb, hRinf⟩ := lem_hp_label_b hs hlab
  obtain ⟨hFDm, -⟩ := s07_sb_maps hFD.1 hFD.2.2.2
  obtain ⟨A, hA⟩ : ∃ A : ℂ → ℂ, A = fun u => cayley (R (cayleyInv u)) := ⟨_, rfl⟩
  have hciU : ∀ u ∈ unitDisc, cayleyInv u ∈ upperHalf := fun u hu =>
    cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp hu)
  have hAq : IsDiskQI A LA cA := by
    refine ⟨fun u hu => ?_, fun x hx y hy => ?_⟩
    · rw [hA]; exact cayley_mem_unitDisc (hRm (hciU u hu))
    · have e1 : diskDist (A x) (A y) = hpDist (R (cayleyInv x)) (R (cayleyInv y)) := by
        rw [hA, s11_ld_hpDist_cayley (hRm (hciU x hx)) (hRm (hciU y hy))]
      have e2 : diskDist x y = hpDist (cayleyInv x) (cayleyInv y) := by
        rw [s11_ld_hpDist_cayley (hciU x hx) (hciU y hy),
          cayley_cayleyInv (mem_ball_zero_iff.mp hx), cayley_cayleyInv (mem_ball_zero_iff.mp hy)]
      rw [e1, e2]
      exact hRq _ (hciU x hx) _ (hciU y hy)
  have hcont : ∀ y : ℂ, 0 ≤ y.im → ContinuousAt cayley y := fun y hy =>
    (continuous_id.sub continuous_const).continuousAt.div
      (continuous_id.add continuous_const).continuousAt (s11_ld_cayley_closed hy).1
  have hbd : HasDiskBoundaryValues A FD := by
    intro ζ hζ
    have hci : Tendsto cayleyInv (𝓝[unitDisc] ζ) (𝓟 upperHalf) :=
      tendsto_principal.mpr (by filter_upwards [self_mem_nhdsWithin] with u hu using hciU u hu)
    by_cases h1 : ζ = 1
    · subst h1
      rw [hF1]
      have h2 : Tendsto cayleyInv (𝓝[unitDisc] (1 : ℂ)) (cocompact ℂ) :=
        s11_ld_cayleyInv_inf.mono_left (nhdsWithin_mono _ fun u hu h => by
          rw [h, unitDisc, mem_ball_zero_iff, norm_one] at hu
          exact lt_irrefl _ hu)
      have := s11_wm_cayley_inf.comp (hRinf.comp (tendsto_inf.mpr ⟨h2, hci⟩))
      rw [hA]
      exact this
    · have hζ1 : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
      have him := (s11_ld_cayleyInv_closed (sphere_subset_closedBall hζ) h1).2 hζ1
      set x : ℝ := (cayleyInv ζ).re with hx
      have hre : cayleyInv ζ = (x : ℂ) := Complex.ext (by simp [hx]) (by simp [him])
      have hc1 : Tendsto cayleyInv (𝓝[unitDisc] ζ) (𝓝[upperHalf] (x : ℂ)) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · rw [← hre]
          exact (s11_ld_cayley_cont.2.continuousAt (isOpen_ne.mem_nhds h1)).tendsto.mono_left
            nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with u hu using hciU u hu
      have hwim : (0 : ℝ) ≤ (((w.symm x : ℝ) : ℂ)).im := by simp
      have := ((hcont _ hwim).tendsto.comp (hRb x)).comp hc1
      rw [hb ζ hζ h1, hre, hHw, hA]
      exact this
  have hsb := lem_same_boundary A FD LA cA L hAq hFD.1 hFD.2.2.2 hbd
  intro z hz
  have hcz := cayley_mem_unitDisc hz
  have h := hsb _ hcz
  have eA : A (cayley z) = cayley (R z) := by rw [hA]; simp only [cayleyInv_cayley hz]
  have eF : FD (cayley z) = cayley ((cayleyInv ∘ FD ∘ cayley) z) :=
    (cayley_cayleyInv (mem_ball_zero_iff.mp (hFDm hcz))).symm
  have hFz : (cayleyInv ∘ FD ∘ cayley) z ∈ upperHalf :=
    cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp (hFDm hcz))
  rw [eA, eF, ← s11_ld_hpDist_cayley (hRm hz) hFz] at h
  exact h

/-- Helper (D5) for `lem_hp_label_d`: if `d_ρ(A z, B z) ≤ M` on `ℍ`, then
`e^{-M} 𝒫_B ≤ 𝒫_A ≤ e^{M} 𝒫_B` (pointwise `k_a(p) ≤ e^{d(p,q)} k_a(q)`, Lemma 7.2 via Cayley). -/
theorem s11_ld_kernel {A B : ℂ → ℂ} (hA : MapsTo A upperHalf upperHalf)
    (hB : MapsTo B upperHalf upperHalf) {M : ℝ} (hM : ∀ z ∈ upperHalf, hpDist (A z) (B z) ≤ M)
    (m : Measure ℂ) {a : ℂ} (ha : a ∈ upperHalf) :
    ENNReal.ofReal (Real.exp (-M)) * hpPOf B m a ≤ hpPOf A m a ∧
      hpPOf A m a ≤ ENNReal.ofReal (Real.exp M) * hpPOf B m a := by
  have hk : ∀ p ∈ upperHalf, ∀ q ∈ upperHalf, hpKernel a p ≤ Real.exp (hpDist p q) * hpKernel a q := by
    intro p hp q hq
    rw [s11_ld_hpKernel_cayley ha hp, s11_ld_hpKernel_cayley ha hq, s11_ld_hpDist_cayley hp hq]
    exact s07_diskKernel_le_exp _ _ _ (cayley_mem_unitDisc ha) (cayley_mem_unitDisc hp)
      (cayley_mem_unitDisc hq)
  have hk0 : ∀ p ∈ upperHalf, 0 ≤ hpKernel a p := fun p _ => by unfold hpKernel; positivity
  have hU : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  unfold hpPOf
  constructor
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' hU fun z hz => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hk _ (hB hz) _ (hA hz)
    rw [s11_wm_hpDist_comm (hB hz) (hA hz)] at h1
    have h2 : Real.exp (hpDist (A z) (B z)) * hpKernel a (A z) ≤ Real.exp M * hpKernel a (A z) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hM z hz)) (hk0 _ (hA hz))
    have h3 : Real.exp (-M) * Real.exp M = 1 := by rw [← Real.exp_add]; simp
    have h4 := mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos (-M)).le
    rw [← mul_assoc, h3, one_mul] at h4
    exact h4
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' hU fun z hz => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ((hk _ (hA hz) _ (hB hz)).trans ?_)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hM z hz)) (hk0 _ (hB hz))

/-- Helper (W4) for `set_hp_welding`: the Cayley map on `ℝ`, `C(x) = exp(i(π + 2 arctan x))`. -/
theorem s11_sw_cayley_real (x : ℝ) :
    cayley (x : ℂ) = exp (((π + 2 * Real.arctan x : ℝ) : ℂ) * I) := by
  set t := Real.arctan x with ht
  have hcpos : 0 < Real.cos t := Real.cos_arctan_pos x
  have hxr : Real.sin t = x * Real.cos t := by
    have h := Real.tan_arctan x
    rw [← ht, Real.tan_eq_sin_div_cos, div_eq_iff hcpos.ne'] at h
    exact h
  have hx : (x : ℂ) * Complex.cos t = Complex.sin t := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_mul, hxr]
  have hpy : Complex.cos t ^ 2 + Complex.sin t ^ 2 = 1 := Complex.cos_sq_add_sin_sq _
  have he : exp (((π + 2 * t : ℝ) : ℂ) * I) = -((Complex.cos t + Complex.sin t * I) ^ 2) := by
    rw [show (((π + 2 * t : ℝ)) : ℂ) * I = π * I + ((t : ℂ) * I + (t : ℂ) * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_mul_I]
    ring
  have hden : (x : ℂ) + I ≠ 0 := (s11_ld_cayley_closed (show (0 : ℝ) ≤ (x : ℂ).im by simp)).1
  unfold cayley
  rw [he, div_eq_iff hden]
  linear_combination (2 * Complex.cos t + 2 * Complex.sin t * I) * hx +
    (I - x) * hpy + (2 * Complex.cos t * Complex.sin t + Complex.sin t ^ 2 * x +
      Complex.sin t ^ 2 * I) * Complex.I_sq

/-- Helper (W4) for `set_hp_welding`: a homeomorphism `φ` of `ℝ` whose Cayley conjugate is (the
restriction of) a circle homeomorphism with a strictly increasing lift is increasing: the lift `L`
satisfies `L(τ x) − τ(φ x) ∈ 2πℤ` with `τ = π + 2 arctan`, which is constant by continuity and the
intermediate value theorem. -/
theorem s11_sw_mono {hD : ℂ → ℂ} (hc : IsCircleHomeo hD) {φ : ℝ ≃ₜ ℝ}
    (hφ : ∀ x : ℝ, hD (cayley (x : ℂ)) = cayley ((φ x : ℝ) : ℂ)) : StrictMono φ := by
  obtain ⟨L, hLm, hLc, -, hLe⟩ := hc
  set τ : ℝ → ℝ := fun x => π + 2 * Real.arctan x with hτ
  have hτm : StrictMono τ := fun a b hab => by
    simp only [hτ]
    linarith [Real.arctan_strictMono hab]
  have key : ∀ x : ℝ, ∃ n : ℤ, L (τ x) - τ (φ x) = n * (2 * π) := by
    intro x
    have h := hLe (τ x)
    rw [← s11_sw_cayley_real, hφ, s11_sw_cayley_real] at h
    generalize hA : π + 2 * Real.arctan (φ x) = A at h
    generalize hB : L (τ x) = B at h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
    refine ⟨-n, ?_⟩
    have := congrArg Complex.im hn
    simp at this
    show B - (π + 2 * Real.arctan (φ x)) = _
    rw [hA]
    push_cast
    linarith
  choose n hn using key
  set g : ℝ → ℝ := fun x => L (τ x) - τ (φ x) with hg
  have hgc : Continuous g := by
    have hτc : Continuous τ := continuous_const.add (continuous_const.mul Real.continuous_arctan)
    exact (hLc.comp hτc).sub (hτc.comp φ.continuous)
  have hπ : 0 < π := Real.pi_pos
  -- `g` cannot jump: two values differ by `≥ 2π`, so `g a + π` would be attained, off `2πℤ`
  have hno : ∀ a b : ℝ, g a < g b → False := by
    intro a b hab
    have h1 := hn a
    have h2 := hn b
    have hab' : (n a : ℝ) < n b := by
      have : (n a : ℝ) * (2 * π) < n b * (2 * π) := by
        simp only [hg] at hab; linarith
      exact lt_of_mul_lt_mul_right this (by positivity)
    have hab'' : (n a : ℝ) + 1 ≤ n b := by
      have : n a + 1 ≤ n b := Int.add_one_le_of_lt (by exact_mod_cast hab')
      exact_mod_cast this
    have hmem : g a + π ∈ uIcc (g a) (g b) := by
      rw [uIcc_of_le hab.le]
      refine ⟨by linarith, ?_⟩
      simp only [hg] at h1 h2 ⊢
      nlinarith
    obtain ⟨z, -, hz⟩ := intermediate_value_uIcc hgc.continuousOn hmem
    have h3 := hn z
    simp only [hg] at h1 h3 hz
    have hr : (2 * n z : ℝ) = 2 * n a + 1 := by
      have h' : ((2 * n z : ℝ) - (2 * n a + 1)) * π = 0 := by linarith
      have := (mul_eq_zero.mp h').resolve_right hπ.ne'
      linarith
    have : (2 * n z : ℤ) = 2 * n a + 1 := by exact_mod_cast hr
    omega
  have hconst : ∀ x, g x = g 0 := fun x => by
    rcases lt_trichotomy (g x) (g 0) with h | h | h
    · exact (hno _ _ h).elim
    · exact h
    · exact (hno _ _ h).elim
  intro a b hab
  have ha := hconst a
  have hb := hconst b
  simp only [hg] at ha hb
  have hL := hLm (hτm hab)
  have : τ (φ a) < τ (φ b) := by linarith
  simp only [hτ] at this
  exact Real.arctan_strictMono.lt_iff_lt.mp (by linarith)

/-- Convention `set:hp`, `sec11-halfplane.tex:742–760`: conformal maps `f : ℍ → Ω`, `g : 𝕃 → Ωs`
fixing `∞` have continuous boundary extensions, and the welding `g⁻¹ ∘ f|_ℝ` is an increasing
homeomorphism of `ℝ`. -/
theorem set_hp_welding {Ω Ωs : Set ℂ} {K : ℝ} (hΓ : IsKQuasiPair Ω Ωs K)
    (hline : ¬ IsLinePair Ω Ωs) {f g : ℂ → ℂ} (hf : IsConformalOnto f upperHalf Ω)
    (hg : IsConformalOnto g lowerHalf Ωs) (hfinf : Tendsto f (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ))
    (hginf : Tendsto g (cocompact ℂ ⊓ 𝓟 lowerHalf) (cocompact ℂ)) :
    ∃ (f₁ g₁ : ℂ → ℂ) (w : ℝ ≃ₜ ℝ), EqOn f₁ f upperHalf ∧ EqOn g₁ g lowerHalf ∧
      IsHPSetting Ω Ωs K f₁ g₁ w ∧ StrictMono w := by
  obtain ⟨Q, F₁, G₁, hF₁, hF₁s, hF₁e, hG₁, hG₁s, hG₁e⟩ := s11_sw_extend hΓ hf hg hfinf hginf
  have hF₁Ω : F₁ '' upperHalf = Ω := hF₁e.image_eq.trans hf.2.2
  have hG₁Ω : G₁ '' lowerHalf = Ωs := hG₁e.image_eq.trans hg.2.2
  obtain ⟨w, hw⟩ := s11_sw_weld hF₁ hF₁s hG₁ hG₁s (s11_sw_real hΓ hF₁ hF₁s hF₁Ω hG₁ hG₁s hG₁Ω)
  have hFc : Continuous F₁ := continuousOn_univ.mp hF₁.2.2.1.1
  have hGc : Continuous G₁ := continuousOn_univ.mp hG₁.2.2.1.1
  have hs : IsHPSetting Ω Ωs K F₁ G₁ w :=
    ⟨hΓ, hline, ⟨hf.1.congr hF₁e, hf.2.1.congr hF₁e.symm, hF₁Ω⟩,
      ⟨hg.1.congr hG₁e, hg.2.1.congr hG₁e.symm, hG₁Ω⟩, hFc.continuousOn, hGc.continuousOn,
      hfinf.congr' (eventually_inf_principal.mpr (Eventually.of_forall fun z hz => (hF₁e hz).symm)),
      hginf.congr' (eventually_inf_principal.mpr (Eventually.of_forall fun z hz => (hG₁e hz).symm)),
      hw⟩
  obtain ⟨H, hHq, hHs, hHw⟩ := s11_ld_weld hs hF₁ hF₁s (fun _ _ => rfl) hG₁ hG₁s (fun _ _ => rfl)
  obtain ⟨hD, -, hDe, -, hDc⟩ := s11_ld_disk hHq hHs (fun x => by rw [hHw]; simp)
  have hmono : StrictMono w.symm := s11_sw_mono hDc fun x => by
    have hc := s11_ld_cayley_closed (show (0 : ℝ) ≤ (x : ℂ).im by simp)
    rw [hDe _ hc.2.1, hc.2.2.2, hHw]
  refine ⟨F₁, G₁, w, hF₁e, hG₁e, hs, fun a b hab => ?_⟩
  have := hmono.lt_iff_lt (a := w a) (b := w b)
  rw [w.symm_apply_apply, w.symm_apply_apply] at this
  exact this.mp hab

/-- Lemma 11.12(d) `lem:hp-label`, `sec11-halfplane.tex:949`: there is a homeomorphism `F` of
`ℍ ∪ ℝ ∪ {∞}` with `F|_ℝ = h = w⁻¹`, `F(∞) = ∞`, real-analytic diffeomorphism of `ℍ`,
`L_F`-bi-Lipschitz for `d_ρ` and `L_F²`-quasiconformal, with `L_F` depending only on `K`;
admissible with constant `L_F` if `h ∈ SQS(ℝ)`; and (11.?) `eq:hp-far` holds with `M` depending
only on `K` (`M = L_F D_*(L_F L_A, L_F c_A)` of `eq:morse-constants`). -/
theorem lem_hp_label_d : ∀ K : ℝ, 1 ≤ K → ∃ LF M : ℝ, 1 ≤ LF ∧ 0 ≤ M ∧
    ∀ (Ω Ωs : Set ℂ) (f g : ℂ → ℂ) (w : ℝ ≃ₜ ℝ) (lab : ℂ × ℝ → ℂ),
      IsHPSetting Ω Ωs K f g w → IsLabel Ω lab →
        ∃ F : ℂ → ℂ, ContinuousOn F closedUpperHalf ∧ BijOn F closedUpperHalf closedUpperHalf ∧
          Tendsto F (cocompact ℂ ⊓ 𝓟 closedUpperHalf) (cocompact ℂ) ∧
          (∀ x : ℝ, F (x : ℂ) = ((w.symm x : ℝ) : ℂ)) ∧
          BijOn F upperHalf upperHalf ∧ AnalyticOnNhd ℝ F upperHalf ∧
          (∀ z ∈ upperHalf, LinearMap.det (fderiv ℝ F z : ℂ →ₗ[ℝ] ℂ) ≠ 0) ∧
          (∀ z ∈ upperHalf, ∀ z' ∈ upperHalf,
            hpDist (F z) (F z') ≤ LF * hpDist z z' ∧ hpDist z z' ≤ LF * hpDist (F z) (F z')) ∧
          IsKQC F upperHalf (LF ^ 2) ∧
          (IsSQS w.symm → IsHPAdmissible F w.symm LF) ∧
          ∀ a ∈ upperHalf,
            ENNReal.ofReal (Real.exp (-M)) * hpPOf F (hpSchwarzMassLower g) a ≤ Kst Ω Ωs lab (f a) ∧
            Kst Ω Ωs lab (f a) ≤ ENNReal.ofReal (Real.exp M) * hpPOf F (hpSchwarzMassLower g) a := by
  intro K hK
  obtain ⟨Q, hQ, hext⟩ := set_hp_extension K hK
  obtain ⟨L, hL, hDE⟩ := s11_ld_DE (Q * Q) (by nlinarith)
  obtain ⟨LA, cA, -, -, hlabA⟩ := lem_hp_label_a K hK
  refine ⟨L, max 0 (L * morseD (L * LA) (L * cA)), hL, le_max_left _ _,
    fun Ω Ωs f g w lab hs hlab => ?_⟩
  obtain ⟨F₁, G₁, hF₁, hF₁s, hF₁e, hG₁, hG₁s, hG₁e⟩ := hext Ω Ωs f g w hs
  obtain ⟨H, hHq, hHs, hHw⟩ := s11_ld_weld hs hF₁ hF₁s hF₁e hG₁ hG₁s hG₁e
  have hHR : ∀ x : ℝ, (H (x : ℂ)).im = 0 := fun x => by rw [hHw]; simp
  obtain ⟨FD, hFD, hAn, hF1, hb⟩ := hDE H hHq hHs hHR
  obtain ⟨hFc, hFbij, hFinf, hFreal, hFbijo, hFan, hFdet, hFbl, hFqc⟩ :=
    s11_ld_F hFD hAn hF1 hHR hb
  obtain ⟨hRm, -, hRq⟩ := hlabA Ω Ωs f g w lab hs hlab
  have hclose := s11_ld_close hs hlab hRm hRq hFD hF1 hHw hb
  have hFw : ∀ x : ℝ, (cayleyInv ∘ FD ∘ cayley) (x : ℂ) = ((w.symm x : ℝ) : ℂ) := fun x => by
    rw [hFreal, hHw]
  refine ⟨cayleyInv ∘ FD ∘ cayley, hFc, hFbij, hFinf, hFw, hFbijo, hFan,
    fun z hz => (hFdet z hz).ne', hFbl, hFqc, fun hsqs => ?_, fun a ha => ?_⟩
  · exact ⟨hL, ⟨L ^ 2, hFqc⟩, hFbijo.image_eq, hFbl, hFc, hFbij, hFinf, hFw, hsqs⟩
  · rw [(lem_hp_label_c hs hlab ha).2]
    exact s11_ld_kernel hRm hFbijo.mapsTo
      (fun z hz => (hclose z hz).trans (le_max_right _ _)) (hpSchwarzMassLower g) ha

/-- Helper for Theorem 11.13: for `F` continuous on `ℍ ∪ ℝ` with `F(ℍ) ⊆ ℍ`, the explicit integral
`hpPOf F m a = ∫_ℍ k_a(F z) dm(z)` equals `𝒫_{F_* m}(a)`. -/
theorem s11_ts_pOf_eq {F : ℂ → ℂ} (hFc : ContinuousOn F closedUpperHalf)
    (hFm : MapsTo F upperHalf upperHalf) (m : Measure ℂ) (a : ℂ) :
    hpPOf F m a = hpP (hpPush F m) a := by
  have hU : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  have hkm : Measurable fun z => ENNReal.ofReal (hpKernel a z) := by
    unfold hpKernel hpDist Real.arcosh; fun_prop
  have hFa : AEMeasurable F (m.restrict upperHalf) :=
    (hFc.mono (t := upperHalf) fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt hz).aemeasurable hU
  unfold hpP hpPush hpPOf
  symm
  rw [← lintegral_indicator hU, lintegral_map' (hkm.indicator hU).aemeasurable hFa]
  refine lintegral_congr_ae ((ae_restrict_iff' hU).mpr (Eventually.of_forall fun z hz => ?_))
  exact indicator_of_mem (hFm hz) _

/-- Helper for Theorem 11.13: for `λ ∈ CM₀(ℍ)`, `Σ_{n≥0} 2^{-n} ε_λ(2^{n+1} r) → 0` as `r → 0⁺`
(dominated convergence for the counting measure, with the summable bound `2^{-n} ‖λ‖_CM`). -/
theorem s11_ts_series {μ : Measure ℂ} (hμ : IsHPVanishingCarleson μ) :
    Tendsto (fun r : ℝ => ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n * hpEps μ (2 ^ (n + 1) * r)) (𝓝[>] 0)
      (𝓝 0) := by
  have hpow : ∀ n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n ≠ ⊤ := fun n =>
    ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr two_ne_zero)
  have key := tendsto_lintegral_filter_of_dominated_convergence (μ := Measure.count)
    (l := 𝓝[>] (0 : ℝ)) (F := fun r n => (2 : ℝ≥0∞)⁻¹ ^ n * hpEps μ (2 ^ (n + 1) * r))
    (f := fun _ : ℕ => (0 : ℝ≥0∞)) (fun n => (2 : ℝ≥0∞)⁻¹ ^ n * hpCMNorm μ)
    (Eventually.of_forall fun _ => measurable_from_nat)
    (Eventually.of_forall fun r => Eventually.of_forall fun n => by
      gcongr; exact (hp_eps_mono_le μ).2 _) ?_ ?_
  · simpa [lintegral_count] using key
  · rw [lintegral_count, ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two,
      inv_inv]
    exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top hμ.1
  · refine Eventually.of_forall fun n => ?_
    have hs : Tendsto (fun r : ℝ => (2 : ℝ) ^ (n + 1) * r) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun r (hr : (0 : ℝ) < r) =>
        show (2 : ℝ) ^ (n + 1) * r ∈ Ioi (0 : ℝ) from mul_pos (by positivity) hr⟩
      have : Tendsto (fun r : ℝ => (2 : ℝ) ^ (n + 1) * r) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul ((2 : ℝ) ^ (n + 1))
      exact this.mono_left nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)⁻¹ ^ n) (hμ.2.comp hs) (Or.inr (hpow n))

/-- Helper for Theorem 11.13 `thm:hp-two-sided`: the limit form under the extra hypothesis
`w⁻¹ ∈ SQS(ℝ)` (which the paper derives from `λ_- ∈ CM₀` via Lemma `lem:hp-welding`). With `F, M`
from Lemma `lem:hp-label`(d), `K_H(f(a)) + K_*(f(a)) ≤ 32 S_{λ_f}(r) + e^M · 32 S_{λ_F}(r)` for
`Im a ≤ r`, where `S_λ(r) = Σ 2^{-n} ε_λ(2^{n+1} r)`; `λ_F ∈ CM₀` by Theorem `thm:hp-transfer`. -/
theorem s11_ts_limit {Ω Ωs : Set ℂ} {K : ℝ} {f g : ℂ → ℂ} {w : ℝ ≃ₜ ℝ} {lab : ℂ × ℝ → ℂ}
    (hs : IsHPSetting Ω Ωs K f g w) (hlab : IsLabel Ω lab)
    (hf : IsHPVanishingCarleson (hpSchwarzCarleson f))
    (hg : IsHPVanishingCarleson (hpSchwarzCarlesonLower g)) (hw : UniformContinuous w)
    (hsq : IsSQS w.symm) :
    Tendsto (hpSupLow fun a => KH Ω (f a) + Kst Ω Ωs lab (f a)) (𝓝[>] 0) (𝓝 0) := by
  have hK : 1 ≤ K := by
    obtain ⟨Φ, hΦ, -⟩ := hs.1
    exact hΦ.2.1
  obtain ⟨D, p, Ch, hdata⟩ := eq_hp_RH hsq
  obtain ⟨A, hA⟩ := eq_hp_maximal
  obtain ⟨L, M, hL, -, hLD⟩ := lem_hp_label_d K hK
  obtain ⟨C₁, α, hwm⟩ := lem_hp_wm L hL
  obtain ⟨F, hFc, -, -, -, hFbijo, -, -, -, -, hadm, hker⟩ := hLD Ω Ωs f g w lab hs hlab
  set m := hpSchwarzMassLower g
  have hFv : IsHPVanishingCarleson (hpPushWeight F m) :=
    ((thm_hp_transfer hwm hA (hadm hsq) hdata m).2.2 (by simpa using hw)).2 hg
  set E := ENNReal.ofReal (Real.exp M)
  have hmono := fun μ : Measure ℂ => (hp_eps_mono_le μ).1
  have hbd : ∀ r : ℝ, hpSupLow (fun a => KH Ω (f a) + Kst Ω Ωs lab (f a)) r ≤
      32 * ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n * hpEps (hpSchwarzCarleson f) (2 ^ (n + 1) * r) +
        E * (32 * ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n * hpEps (hpPushWeight F m) (2 ^ (n + 1) * r)) := by
    intro r
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun har => ?_
    have hsc : ∀ n : ℕ, (2 : ℝ) ^ (n + 1) * a.im ≤ 2 ^ (n + 1) * r := fun n =>
      mul_le_mul_of_nonneg_left har (by positivity)
    have h1 : hpP (hpSchwarzMass f) a ≤
        32 * ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n * hpEps (hpSchwarzCarleson f) (2 ^ (n + 1) * a.im) :=
      eq_hp_shells _ ha
    have h2 : hpP (hpPush F m) a ≤
        32 * ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n * hpEps (hpPushWeight F m) (2 ^ (n + 1) * a.im) :=
      eq_hp_shells _ ha
    show KH Ω (f a) + Kst Ω Ωs lab (f a) ≤ _
    refine add_le_add ?_ ?_
    · rw [(lem_hp_label_c hs hlab ha).1]
      refine h1.trans ?_
      gcongr 32 * ?_
      exact ENNReal.tsum_le_tsum fun n => by gcongr; exact hmono _ (hsc n)
    · refine (hker a ha).2.trans ?_
      rw [s11_ts_pOf_eq hFc hFbijo.mapsTo]
      gcongr E * ?_
      refine h2.trans ?_
      gcongr 32 * ?_
      exact ENNReal.tsum_le_tsum fun n => by gcongr; exact hmono _ (hsc n)
  have h32 : (32 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hlim := (ENNReal.Tendsto.const_mul (s11_ts_series hf) (Or.inr h32)).add
    (ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul (s11_ts_series hFv) (Or.inr h32))
      (Or.inr ENNReal.ofReal_ne_top : (32 * 0 : ℝ≥0∞) ≠ 0 ∨ E ≠ ⊤))
  simp only [mul_zero, add_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hbd

/-- Theorem 11.13 `thm:hp-two-sided`, `sec11-halfplane.tex:1029`, limit form: if
`λ_f, λ_- ∈ CM₀(ℍ)` and `w` is uniformly continuous, then
`sup_{Im a ≤ r} (K_H(f(a)) + K_*(f(a))) → 0` as `r → 0`. -/
theorem thm_hp_two_sided {Ω Ωs : Set ℂ} {K : ℝ} {f g : ℂ → ℂ} {w : ℝ ≃ₜ ℝ} {lab : ℂ × ℝ → ℂ}
    (hs : IsHPSetting Ω Ωs K f g w) (hlab : IsLabel Ω lab)
    (hf : IsHPVanishingCarleson (hpSchwarzCarleson f))
    (hg : IsHPVanishingCarleson (hpSchwarzCarlesonLower g)) (hw : UniformContinuous w) :
    Tendsto (hpSupLow fun a => KH Ω (f a) + Kst Ω Ωs lab (f a)) (𝓝[>] 0) (𝓝 0) := by sorry

/-- Theorem 11.13 `thm:hp-two-sided`, (11.?) `eq:hp-two-sided`, `sec11-halfplane.tex:1038`: the
quantitative bounds, with `M, α` depending only on `K` and `C` depending on `K` and the strong
quasisymmetry data `(D, p, C_h)` of `w⁻¹` (through the maximal constants `A`). -/
theorem eq_hp_two_sided : ∀ K : ℝ, 1 ≤ K → ∃ M α : ℝ, 0 ≤ M ∧ 1 ≤ α ∧
    ∃ Cf : (ℝ → ℝ) → ℝ → ℝ → ℝ → ℝ, ∀ A : ℝ → ℝ, IsMaximalConst A →
    ∀ (Ω Ωs : Set ℂ) (f g : ℂ → ℂ) (w : ℝ ≃ₜ ℝ) (lab : ℂ × ℝ → ℂ),
      IsHPSetting Ω Ωs K f g w → IsLabel Ω lab →
      IsHPVanishingCarleson (hpSchwarzCarleson f) →
      IsHPVanishingCarleson (hpSchwarzCarlesonLower g) → UniformContinuous w →
      ∀ D p Ch : ℝ, IsSQSData w.symm D p Ch → ∀ r : ℝ, 0 < r → ∀ a ∈ upperHalf, a.im ≤ r →
        KH Ω (f a) ≤ 32 * ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n *
          hpEps (hpSchwarzCarleson f) (2 ^ (n + 1) * r) ∧
        Kst Ω Ωs lab (f a) ≤ 32 * ENNReal.ofReal (Cf A D p Ch) * ENNReal.ofReal (Real.exp M) *
          ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n *
            hpEps (hpSchwarzCarlesonLower g) (α * modCont w (2 ^ (n + 1) * r)) := by
  intro K hK
  obtain ⟨L, M, hL, hM, hLD⟩ := lem_hp_label_d K hK
  obtain ⟨C₁, α, hwm⟩ := lem_hp_wm L hL
  refine ⟨M, α, hM, hwm.2.1, fun A D p Ch => hpTransferConst C₁ α A D p Ch,
    fun A hA Ω Ωs f g w lab hs hlab hf hg hw D p Ch hdata r hr a ha har => ?_⟩
  -- `λ_f, λ_- ∈ CM₀` are not needed for the quantitative bounds (the statement holds without them)
  have _hf := hf
  have _hg := hg
  obtain ⟨F, hFc, -, -, -, hFbijo, -, -, -, -, hadm, hker⟩ := hLD Ω Ωs f g w lab hs hlab
  have hsq : IsSQS w.symm := hdata.elim fun ω h => ⟨ω, h.1⟩
  have hUC := ((thm_hp_transfer hwm hA (hadm hsq) hdata (hpSchwarzMassLower g)).2.2
    (by simpa using hw)).1
  simp only [Homeomorph.symm_symm] at hUC
  have hmono := fun μ : Measure ℂ => (hp_eps_mono_le μ).1
  have hsc : ∀ n : ℕ, (2 : ℝ) ^ (n + 1) * a.im ≤ 2 ^ (n + 1) * r := fun n =>
    mul_le_mul_of_nonneg_left har (by positivity)
  refine ⟨?_, ?_⟩
  · rw [(lem_hp_label_c hs hlab ha).1]
    refine (eq_hp_shells _ ha).trans ?_
    gcongr 32 * ?_
    exact ENNReal.tsum_le_tsum fun n => by gcongr; exact hmono _ (hsc n)
  · refine ((hker a ha).2.trans ?_)
    rw [s11_ts_pOf_eq hFc hFbijo.mapsTo]
    set C := ENNReal.ofReal (hpTransferConst C₁ α A D p Ch)
    set E := ENNReal.ofReal (Real.exp M)
    have hstep : ∀ n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n * hpEps (hpPushWeight F (hpSchwarzMassLower g))
        (2 ^ (n + 1) * a.im) ≤ C * ((2 : ℝ≥0∞)⁻¹ ^ n *
          hpEps (hpSchwarzCarlesonLower g) (α * modCont w (2 ^ (n + 1) * r))) := fun n => by
      rw [mul_left_comm]
      gcongr
      exact (hmono _ (hsc n)).trans (hUC _ (by positivity))
    calc E * hpP (hpPush F (hpSchwarzMassLower g)) a
        ≤ E * (32 * ∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ n *
            hpEps (hpPushWeight F (hpSchwarzMassLower g)) (2 ^ (n + 1) * a.im)) := by
          gcongr; exact eq_hp_shells _ ha
      _ ≤ E * (32 * ∑' n : ℕ, C * ((2 : ℝ≥0∞)⁻¹ ^ n *
            hpEps (hpSchwarzCarlesonLower g) (α * modCont w (2 ^ (n + 1) * r)))) := by
          gcongr E * (32 * ?_); exact ENNReal.tsum_le_tsum hstep
      _ = _ := by rw [ENNReal.tsum_mul_left]; ring

/-- Theorem 11.14 `thm:hp-one-sided`, `sec11-halfplane.tex:1065`: if `λ_f ∈ CM₀(ℍ)` and `w, w⁻¹`
are uniformly continuous, then `λ_- ∈ CM₀(ℍ)` and the conclusions of Theorem `thm:hp-two-sided`
hold. -/
theorem thm_hp_one_sided {Ω Ωs : Set ℂ} {K : ℝ} {f g : ℂ → ℂ} {w : ℝ ≃ₜ ℝ} {lab : ℂ × ℝ → ℂ}
    (hs : IsHPSetting Ω Ωs K f g w) (hlab : IsLabel Ω lab)
    (hf : IsHPVanishingCarleson (hpSchwarzCarleson f)) (hw : UniformContinuous w)
    (hw' : UniformContinuous w.symm) :
    IsHPVanishingCarleson (hpSchwarzCarlesonLower g) ∧
      Tendsto (hpSupLow fun a => KH Ω (f a) + Kst Ω Ωs lab (f a)) (𝓝[>] 0) (𝓝 0) := by sorry

/-- Corollary 11.15(a) `cor:hp-volume`, `sec11-halfplane.tex:1086`, under the hypotheses of
Theorem `thm:hp-two-sided`: `sup_{Im a ≤ r} K_V(f(a)) → 0`. -/
theorem cor_hp_volume_a_two {Ω Ωs : Set ℂ} {K : ℝ} {f g : ℂ → ℂ} {w : ℝ ≃ₜ ℝ} {lab : ℂ × ℝ → ℂ}
    (hs : IsHPSetting Ω Ωs K f g w) (hlab : IsLabel Ω lab)
    (hf : IsHPVanishingCarleson (hpSchwarzCarleson f))
    (hg : IsHPVanishingCarleson (hpSchwarzCarlesonLower g)) (hw : UniformContinuous w) :
    Tendsto (hpSupLow fun a => KV Ω Ωs lab (f a)) (𝓝[>] 0) (𝓝 0) := by sorry

/-- Corollary 11.15(a) `cor:hp-volume`, `sec11-halfplane.tex:1086`, under the hypotheses of
Theorem `thm:hp-one-sided`: `sup_{Im a ≤ r} K_V(f(a)) → 0`. -/
theorem cor_hp_volume_a_one {Ω Ωs : Set ℂ} {K : ℝ} {f g : ℂ → ℂ} {w : ℝ ≃ₜ ℝ} {lab : ℂ × ℝ → ℂ}
    (hs : IsHPSetting Ω Ωs K f g w) (hlab : IsLabel Ω lab)
    (hf : IsHPVanishingCarleson (hpSchwarzCarleson f)) (hw : UniformContinuous w)
    (hw' : UniformContinuous w.symm) :
    Tendsto (hpSupLow fun a => KV Ω Ωs lab (f a)) (𝓝[>] 0) (𝓝 0) := by sorry

/-- Corollary 11.15(b) `cor:hp-volume`, `sec11-halfplane.tex:1091`: if `λ_f ∈ CM(ℍ)` and
`sup_{Im a ≤ r} K_V(f(a)) → 0`, then `λ_f ∈ CM₀(ℍ)`, hence `w ∈ SS(ℝ)`. -/
theorem cor_hp_volume_b {Ω Ωs : Set ℂ} {K : ℝ} {f g : ℂ → ℂ} {w : ℝ ≃ₜ ℝ} {lab : ℂ × ℝ → ℂ}
    (hs : IsHPSetting Ω Ωs K f g w) (hlab : IsLabel Ω lab)
    (hf : IsHPCarleson (hpSchwarzCarleson f))
    (hV : Tendsto (hpSupLow fun a => KV Ω Ωs lab (f a)) (𝓝[>] 0) (𝓝 0)) :
    IsHPVanishingCarleson (hpSchwarzCarleson f) ∧ IsSS w := by sorry

end EpsteinVMO
