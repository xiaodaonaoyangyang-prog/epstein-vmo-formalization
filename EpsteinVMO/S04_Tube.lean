import EpsteinVMO.Defs
import EpsteinVMO.S02_Prelim
import EpsteinVMO.S03_Coarse

/-!
# §4 The finite normal tube lemma (`sec04-tube.tex`)

Statements of §4: Lemma 4.1 (`lem:Cj`), Lemma 4.2 (`lem:tube`), Corollary 4.4 (`cor:coverage`),
the smooth gluing (4.3) (`eq:def-N`), Proposition 4.5 (`prop:RN`), Lemma 4.6 (`lem:jacobian`) and
Lemma 4.7 (`lem:source`).

## Section-local definitions (also used by §5, §9, §10, §12)

* **ρ-balls.** `rhoBall Ω w r`, `rhoClosedBall Ω w r` (for the hyperbolic distance `poincareDist`),
  `rhoNbhd Ω S r`.
* **Smoothness.** `SmoothNear f S` (`f` is `C^∞` on an open neighbourhood of `S`), and
  `IsSmoothEmbeddingOn f S` (smooth near `S`, injective on `S`, injective differential at every
  point of `S`, and a topological embedding of `S`).
* **Tensors on `(Ω, ρ)`.** A covariant `k`-tensor field is written in the global coordinate `w` of
  `Ω ⊂ ℂ` as `TensorField k = ℂ → (Fin k → ℂ) → ℝ` (only its values on multilinear fields matter).
  `rhoCovDeriv` is the Levi-Civita covariant derivative of `ρ = λ² |dw|²`
  (Christoffel map `rhoChristoffel`, `Γ(X,Y) = (Xφ)Y + (Yφ)X - ⟨X,Y⟩ ∇φ`, `φ = log λ`), the new
  slot (the direction of differentiation) being slot `0`.  `rhoTensorNorm` is the pointwise
  Hilbert–Schmidt `ρ`-norm and `rhoCjNorm Ω j T E ∈ ℝ≥0∞` is the paper's `‖T‖_{C^j(E)}`: the
  supremum over orders `≤ j` and points of `E` of the `ρ`-norms of the covariant derivatives.
  Tensors of type `(1,1)` or `(2,0)` are measured after lowering the indices with `ρ` (this is
  isometric and commutes with `∇`).
* **The surfaces.** `fffT Ω` is `I = X^* g_{ℍ³}`, `rhoMetricT Ω` is `ρ`; `normalVec Ω w = ∂_τ E(w,0)`
  is the marked unit normal `ν`; `secondFF` is `II(v,v') = ⟨-∇_{dX v} ν, dX v'⟩ = I(Bv, v')`
  (with `hypChristoffel` the Levi-Civita connection of `ℍ³`; `hypInner` is §2's), `shapeMat Ω w` the matrix of the
  shape operator `B = I⁻¹ II` in the basis `(1, i)`, `shapeT Ω = ρ(B ·, ·)` (`B` with the index
  lowered by `ρ`), `meanCurv Ω w = ½ tr B`.
* **Good parameters (§4, used in §5, §9, §10).** `varsigma Ω Ωs x R` is `ς(x, R)`
  (with `sup ∅ = 0`), `IsGoodParam Ω Ωs η R w` is "`w ∈ Ω` is `(η,R)`-good", and
  `goodSet Ω Ωs η R` is the set `G₀` of good parameters.
* **The slab (4.3).** `slabTop Ω Ωs w` is the first time `τ > 0` at which the normal ray
  `τ ↦ E(w,τ)` meets `Σ* = X*(Ω*)`, and `slabMap Ω Ωs w` a point `z* ∈ Ω*` with
  `X*(z*) = E(w, slabTop w)`.  On `G₀` these are the paper's `t` and `N` (by the uniqueness in
  Lemma 4.2 (iii)); off `G₀` they are junk and never used.
* `sigmaSrc Ω Ωs w = σ(w) = H(w) + H*(N w)` with `H = s²/(1-s²)` (4.4), and `jacN Ω Ωs w` the area
  Jacobian `J_N` of `N` with respect to `dâ`, `dâ*`.

`E(w,τ)` is `normalGeod Ω w τ` (`Defs`), and `normalMap Ω (v, τ) = E(v, τ)`.

## Modelling remarks
* Remark 4.3 (`rem:tube-quantifiers`) states the quantifier order, which the statements below
  follow (`ε` first, then `η, R`); it contains no further formal claim.
* In Lemma 4.2 (v) the paper's constant `R₀ = R₀(K)` (Lemma 3.x of §3) is replaced by an arbitrary
  `R₀ ≥ 0`, with `η, R` allowed to depend on it.  This is stronger than the paper's statement
  (which uses one particular `R₀(K)`), and the paper's proof gives it verbatim (the enlargement of
  `R` by `5/2 (L + R₀ + 4) + T + 4` works for every `R₀`).
* "`(η, R)` as in Lemma 4.2" is rendered as `∃ η R` in each statement.  All properties stated on
  `G₀` are inherited by smaller `η` and larger `R` (`G₀` shrinks), so the existential constants
  of different statements can be taken common.
-/

open Complex Set Metric Filter Topology MeasureTheory Matrix
open scoped ENNReal NNReal Real ComplexConjugate ContDiff

noncomputable section

namespace EpsteinVMO

open LiZhongQC

/-! ## ρ-balls and smoothness -/

/-- The open ball `B_ρ(w, r)` of the hyperbolic distance of `Ω`. -/
def rhoBall (Ω : Set ℂ) (w : ℂ) (r : ℝ) : Set ℂ := {w' | w' ∈ Ω ∧ poincareDist Ω w w' < r}

/-- The closed ball `\overline{B_ρ(w, r)}` of the hyperbolic distance of `Ω`. -/
def rhoClosedBall (Ω : Set ℂ) (w : ℂ) (r : ℝ) : Set ℂ :=
  {w' | w' ∈ Ω ∧ poincareDist Ω w w' ≤ r}

/-- The open `ρ`-neighbourhood of radius `r` of a set `S ⊆ Ω`. -/
def rhoNbhd (Ω : Set ℂ) (S : Set ℂ) (r : ℝ) : Set ℂ :=
  {w' | w' ∈ Ω ∧ ∃ y ∈ S, poincareDist Ω y w' < r}

/-- `f` is smooth (`C^∞`) on an open neighbourhood of `S`. -/
def SmoothNear {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E → F) (S : Set E) : Prop :=
  ∃ V : Set E, IsOpen V ∧ S ⊆ V ∧ ContDiffOn ℝ ∞ f V

/-- `f` is a smooth embedding of `S`: smooth near `S`, injective on `S`, an immersion at every
point of `S`, and a homeomorphism of `S` onto its image. -/
def IsSmoothEmbeddingOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (S : Set E) : Prop :=
  SmoothNear f S ∧ InjOn f S ∧ (∀ x ∈ S, Function.Injective (fderiv ℝ f x)) ∧
    Topology.IsEmbedding (fun x : S => f x)

/-! ## Tensor fields on `(Ω, ρ)` and their `C^j` norms -/

/-- A covariant `k`-tensor field on a plane domain, in the global coordinate `w`. -/
abbrev TensorField (k : ℕ) : Type := ℂ → (Fin k → ℂ) → ℝ

/-- The Euclidean frame `(1, i)` of `T_wΩ = ℂ`. -/
def frameVec (i : Fin 2) : ℂ := ![(1 : ℂ), I] i

/-- Coordinates of `v ∈ ℂ` in the frame `(1, i)`. -/
def cvec (v : ℂ) : Fin 2 → ℝ := ![v.re, v.im]

/-- The vector with coordinates `x` in the frame `(1, i)`. -/
def ofCvec (x : Fin 2 → ℝ) : ℂ := ⟨x 0, x 1⟩

/-- A function as a `0`-tensor field. -/
def scalarField (u : ℂ → ℝ) : TensorField 0 := fun w _ => u w

/-- The Euclidean gradient `φ_x + i φ_y` of `φ = log λ`. -/
def logDensityGrad (Ω : Set ℂ) (w : ℂ) : ℂ :=
  ((fderiv ℝ (fun x => Real.log (poincareDensity Ω x)) w 1 : ℝ) : ℂ) +
    ((fderiv ℝ (fun x => Real.log (poincareDensity Ω x)) w I : ℝ) : ℂ) * I

/-- The Levi-Civita connection of `ρ = e^{2φ} |dw|²`, `φ = log λ`, on coordinate fields:
`Γ_w(X, Y) = (Xφ) Y + (Yφ) X - ⟨X, Y⟩ ∇φ`. -/
def rhoChristoffel (Ω : Set ℂ) (w X Y : ℂ) : ℂ :=
  (((conj (logDensityGrad Ω w) * X).re : ℝ) : ℂ) * Y +
    (((conj (logDensityGrad Ω w) * Y).re : ℝ) : ℂ) * X -
      (((conj X * Y).re : ℝ) : ℂ) * logDensityGrad Ω w

/-- The covariant derivative `∇T` of a covariant tensor field for the metric `ρ`;
`(∇T)(X, v₁, …, v_k) = (∇_X T)(v₁, …, v_k)`. -/
def rhoCovDeriv (Ω : Set ℂ) {k : ℕ} (T : TensorField k) : TensorField (k + 1) := fun w v =>
  fderiv ℝ (fun x => T x (Fin.tail v)) w (v 0) -
    ∑ i : Fin k, T w (Function.update (Fin.tail v) i (rhoChristoffel Ω w (v 0) (Fin.tail v i)))

/-- The iterated covariant derivative `∇^j T`. -/
def rhoIterCovDeriv (Ω : Set ℂ) : (j : ℕ) → {k : ℕ} → TensorField k → TensorField (k + j)
  | 0, _, T => T
  | j + 1, k, T => fun w v =>
      rhoIterCovDeriv Ω j (rhoCovDeriv Ω T) w (v ∘ Fin.cast (by omega))

/-- The pointwise Hilbert–Schmidt `ρ`-norm of a covariant `k`-tensor at `w`. -/
def rhoTensorNorm (Ω : Set ℂ) {k : ℕ} (T : TensorField k) (w : ℂ) : ℝ :=
  Real.sqrt (∑ idx : Fin k → Fin 2, (T w fun i => frameVec (idx i)) ^ 2) /
    poincareDensity Ω w ^ k

/-- `‖T‖_{C^j(E)}`: the supremum over orders `i ≤ j` and points of `E` of the pointwise
`ρ`-norms of `∇^i T` (with values in `ℝ≥0∞`, so that no boundedness is presupposed). -/
def rhoCjNorm (Ω : Set ℂ) {k : ℕ} (j : ℕ) (T : TensorField k) (E : Set ℂ) : ℝ≥0∞ :=
  ⨆ (i : ℕ) (_ : i ≤ j) (w : ℂ) (_ : w ∈ E),
    ENNReal.ofReal (rhoTensorNorm Ω (rhoIterCovDeriv Ω i T) w)

/-! ## The first and second fundamental forms of `Σ = X(Ω)` -/

/-- The Levi-Civita connection of `ℍ³` (metric `ξ⁻² (|dW|² + dξ²)`) at `q`:
`Γ_q(U, V) = -(U₂ V + V₂ U)/ξ + ⟨U, V⟩/ξ · e₃`. -/
def hypChristoffel (q U V : ℂ × ℝ) : ℂ × ℝ :=
  (-(U.2 / q.2)) • V + (-(V.2 / q.2)) • U +
    (((conj U.1 * V.1).re + U.2 * V.2) / q.2) • ((0 : ℂ), (1 : ℝ))

/-- The metric `ρ = λ² |dw|²` as a `2`-tensor. -/
def rhoMetricT (Ω : Set ℂ) : TensorField 2 := fun w v =>
  poincareDensity Ω w ^ 2 * (conj (v 0) * v 1).re

/-- The first fundamental form `I = X^* g_{ℍ³}` of the Epstein–Poincaré map. -/
def fffT (Ω : Set ℂ) : TensorField 2 := fun w v =>
  hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w (v 0)) (fderiv ℝ (epstein Ω) w (v 1))

/-- The normal map `E(v, τ)` as a map of `ℂ × ℝ`. -/
def normalMap (Ω : Set ℂ) (p : ℂ × ℝ) : ℂ × ℝ := normalGeod Ω p.1 p.2

/-- The marked unit normal `ν(w) = ∂_τ E(w, τ)|_{τ=0}` of `Σ` at `X(w)`. -/
def normalVec (Ω : Set ℂ) (w : ℂ) : ℂ × ℝ := deriv (fun τ => normalGeod Ω w τ) 0

/-- The second fundamental form `II(v, v') = ⟨-∇_{dX v} ν, dX v'⟩ = I(Bv, v')`, `B = -∇ν`. -/
def secondFF (Ω : Set ℂ) (w v v' : ℂ) : ℝ :=
  hypInner (epstein Ω w)
    (-(fderiv ℝ (normalVec Ω) w v +
      hypChristoffel (epstein Ω w) (fderiv ℝ (epstein Ω) w v) (normalVec Ω w)))
    (fderiv ℝ (epstein Ω) w v')

/-- The matrix of `I` in the frame `(1, i)`. -/
def fffMat (Ω : Set ℂ) (w : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => fffT Ω w ![frameVec i, frameVec j]

/-- The matrix of `II` in the frame `(1, i)`. -/
def secondFFMat (Ω : Set ℂ) (w : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => secondFF Ω w (frameVec i) (frameVec j)

/-- The matrix of the shape operator `B` (transported to `T_wΩ` by `dX`) in the frame `(1, i)`:
`I(Bv, v') = II(v, v')`, i.e. `B = I⁻¹ IIᵀ`.  (Meaningful where `X` is an immersion.) -/
def shapeMat (Ω : Set ℂ) (w : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (fffMat Ω w)⁻¹ * (secondFFMat Ω w)ᵀ

/-- `B v`. -/
def shapeApply (Ω : Set ℂ) (w v : ℂ) : ℂ := ofCvec (shapeMat Ω w *ᵥ cvec v)

/-- The shape operator with its upper index lowered by `ρ`: `(v, v') ↦ ρ(Bv, v')`. -/
def shapeT (Ω : Set ℂ) : TensorField 2 := fun w v =>
  poincareDensity Ω w ^ 2 * ((shapeMat Ω w *ᵥ cvec (v 0)) ⬝ᵥ cvec (v 1))

/-- The mean curvature `H = ½ tr B` of `Σ` with respect to `ν`. -/
def meanCurv (Ω : Set ℂ) (w : ℂ) : ℝ := (shapeMat Ω w).trace / 2

/-! ## Good parameters -/

/-- `ς(x, R) = sup ({s(w') : X(w') ∈ B(x,R)} ∪ {s*(z*) : X*(z*) ∈ B(x,R)})`, `sup ∅ = 0`. -/
def varsigma (Ω Ωs : Set ℂ) (x : ℂ × ℝ) (R : ℝ) : ℝ :=
  sSup ({r | ∃ w ∈ Ω, epstein Ω w ∈ hball x R ∧ r = schwarzNorm Ω w} ∪
    {r | ∃ z ∈ Ωs, epstein Ωs z ∈ hball x R ∧ r = schwarzNorm Ωs z})

/-- `w ∈ Ω` is `(η, R)`-good: `ς(X(w), R) < η`. -/
def IsGoodParam (Ω Ωs : Set ℂ) (η R : ℝ) (w : ℂ) : Prop :=
  w ∈ Ω ∧ varsigma Ω Ωs (epstein Ω w) R < η

/-- The set `G₀` of `(η, R)`-good parameters. -/
def goodSet (Ω Ωs : Set ℂ) (η R : ℝ) : Set ℂ := {w | IsGoodParam Ω Ωs η R w}

/-! ## The slab: `t`, `N`, `σ`, `J_N` -/

/-- The thickness `t(w)`: the first time `τ > 0` at which `E(w, τ) ∈ Σ*`. -/
def slabTop (Ω Ωs : Set ℂ) (w : ℂ) : ℝ :=
  sInf {τ | 0 < τ ∧ ∃ z ∈ Ωs, epstein Ωs z = normalGeod Ω w τ}

open Classical in
/-- The map `N`: a point `z* ∈ Ω*` with `X*(z*) = E(w, t(w))` (unique on `G₀`). -/
def slabMap (Ω Ωs : Set ℂ) (w : ℂ) : ℂ :=
  if h : ∃ z ∈ Ωs, epstein Ωs z = normalGeod Ω w (slabTop Ω Ωs w) then h.choose else w

/-- The source `σ(w) = H(w) + H*(N(w))`, with `H = s²/(1-s²)` and `H* = s*²/(1-s*²)` (4.4). -/
def sigmaSrc (Ω Ωs : Set ℂ) (w : ℂ) : ℝ :=
  schwarzNorm Ω w ^ 2 / (1 - schwarzNorm Ω w ^ 2) +
    schwarzNorm Ωs (slabMap Ω Ωs w) ^ 2 / (1 - schwarzNorm Ωs (slabMap Ω Ωs w) ^ 2)

/-- The area Jacobian `J_N` of `N`, defined by `N^*(dâ*) = J_N dâ`. -/
def jacN (Ω Ωs : Set ℂ) (w : ℂ) : ℝ :=
  |LinearMap.det ((fderiv ℝ (slabMap Ω Ωs) w : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)| *
    poincareDensity Ωs (slabMap Ω Ωs w) ^ 2 / poincareDensity Ω w ^ 2

/-! ## §4.2 Tube lemma, stage 1: deterministic helpers (interface T40)

`s04_tb_*`: the subsequence principle and the reduction of `lem_tube` to sequences, monotonicity
of `rhoCjNorm`, goodness facts, and the deterministic stages (i) embedding (`s04_tb_X_embed`),
(ii) (`s04_tb_E_embed`) and (iv) (`s04_tb_sides`). -/

/-- T40 helper (subsequence principle): if every subsequence has a further subsequence along which
`P` holds eventually, then `P` holds eventually. -/
theorem s04_tb_subseq {P : ℕ → Prop}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ n in atTop, P (φ (ψ n))) :
    ∀ᶠ n in atTop, P n := by
  by_contra hne
  obtain ⟨φ, hφ, hP⟩ := Filter.extraction_of_frequently_atTop (Filter.not_eventually.mp hne)
  obtain ⟨ψ, -, hψ⟩ := h φ hφ
  obtain ⟨n, hn⟩ := hψ.exists
  exact hP (ψ n) hn

/-- T40 helper (reduction to sequences): a property `C` of good parameters holds for some
`(η, R)` as soon as it holds eventually along every sequence of `(η n, R n)`-good parameters
with `η n → 0` and `R n → ∞`. -/
theorem s04_tb_contra {K : ℝ} {C : Set ℂ → Set ℂ → ℂ → Prop}
    (hseq : ∀ (Ω Ωs : ℕ → Set ℂ) (w : ℕ → ℂ) (η R : ℕ → ℝ),
      (∀ n, IsKQuasiPair (Ω n) (Ωs n) K) → (∀ n, ¬ IsLinePair (Ω n) (Ωs n)) →
      (∀ n, IsGoodParam (Ω n) (Ωs n) (η n) (R n) (w n)) → Tendsto η atTop (𝓝 0) →
      Tendsto R atTop atTop → ∀ᶠ n in atTop, C (Ω n) (Ωs n) (w n)) :
    ∃ η : ℝ, 0 < η ∧ ∃ R : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ w : ℂ, IsGoodParam Ω Ωs η R w → C Ω Ωs w := by
  by_contra hne
  have hex : ∀ n : ℕ, ∃ Ω Ωs : Set ℂ, ∃ w : ℂ, IsKQuasiPair Ω Ωs K ∧ ¬ IsLinePair Ω Ωs ∧
      IsGoodParam Ω Ωs (1 / ((n : ℝ) + 1)) (n : ℝ) w ∧ ¬ C Ω Ωs w := by
    intro n
    by_contra hn
    apply hne
    refine ⟨1 / ((n : ℝ) + 1), by positivity, (n : ℝ), fun Ω Ωs hp hnl w hg => ?_⟩
    by_contra hc
    exact hn ⟨Ω, Ωs, w, hp, hnl, hg, hc⟩
  choose Ω Ωs w hp hnl hg hc using hex
  obtain ⟨n, hn⟩ := (hseq Ω Ωs w _ _ hp hnl hg tendsto_one_div_add_atTop_nhds_zero_nat
    tendsto_natCast_atTop_atTop).exists
  exact hc n hn

/-- T40 helper: `‖T‖_{C^i(E)} ≤ ‖T‖_{C^j(E')}` for `i ≤ j`, `E ⊆ E'`. -/
theorem s04_tb_cj_mono (Ω : Set ℂ) {k : ℕ} (T : TensorField k) {i j : ℕ} (hij : i ≤ j)
    {E E' : Set ℂ} (hE : E ⊆ E') : rhoCjNorm Ω i T E ≤ rhoCjNorm Ω j T E' := by
  unfold rhoCjNorm
  refine iSup_le fun l => iSup_le fun hl => iSup_le fun w => iSup_le fun hw => ?_
  exact le_iSup_of_le l (le_iSup_of_le (hl.trans hij) (le_iSup_of_le w
    (le_iSup_of_le (hE hw) le_rfl)))

/-- T40 helper: `d_ρ(w, w) = 0`. -/
theorem s04_tb_dist_self {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) : poincareDist Ω w w = 0 := by
  obtain ⟨f, hf⟩ := hΩ
  obtain ⟨a, ha, rfl⟩ : w ∈ f '' unitDisc := by rw [hf.2.2]; exact hw
  rw [subsec_poincare_dist hf ha ha, s02_diskDist_cayley ha ha, dist_self]

/-- T40 helper: being a line pair is symmetric. -/
theorem s04_tb_swap_nl {Ω Ωs : Set ℂ} (h : ¬ IsLinePair Ω Ωs) : ¬ IsLinePair Ωs Ω := by
  rintro ⟨a, b, ha, h1, h2⟩
  have e : ∀ z : ℂ, (-a * z + -b).im = -(a * z + b).im := fun z => by
    simp only [neg_mul, Complex.add_im, Complex.neg_im]
    ring
  refine h ⟨-a, -b, neg_ne_zero.mpr ha, ?_, ?_⟩
  · rw [h2]
    ext z
    show (a * z + b).im < 0 ↔ 0 < (-a * z + -b).im
    rw [e]
    constructor <;> intro hz <;> linarith
  · rw [h1]
    ext z
    show 0 < (a * z + b).im ↔ (-a * z + -b).im < 0
    rw [e]
    constructor <;> intro hz <;> linarith

/-- T40 helper: `X(w) ∈ ℍ³`. -/
theorem s04_tb_ep_uhs {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) : epstein Ω w ∈ UHS := by
  rw [← (lem_normal_b hΩ hw).2.2]
  exact (lem_normal_b hΩ hw).1 0

/-- T40 helper: the set whose supremum is `ς(x, R)` is bounded above (by `3/2`, Nehari) and
consists of nonnegative numbers. -/
theorem s04_tb_vs_bdd {Ω Ωs : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    (hΩs : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ωs) (x : ℂ × ℝ) (R : ℝ) :
    BddAbove ({r | ∃ w ∈ Ω, epstein Ω w ∈ hball x R ∧ r = schwarzNorm Ω w} ∪
      {r | ∃ z ∈ Ωs, epstein Ωs z ∈ hball x R ∧ r = schwarzNorm Ωs z}) ∧
    ∀ r ∈ ({r | ∃ w ∈ Ω, epstein Ω w ∈ hball x R ∧ r = schwarzNorm Ω w} ∪
      {r | ∃ z ∈ Ωs, epstein Ωs z ∈ hball x R ∧ r = schwarzNorm Ωs z}), 0 ≤ r := by
  refine ⟨⟨3 / 2, ?_⟩, ?_⟩
  · rintro r (⟨w, hw, -, rfl⟩ | ⟨z, hz, -, rfl⟩)
    · exact (eq_nehari hΩ hw).2
    · exact (eq_nehari hΩs hz).2
  · rintro r (⟨w, hw, -, rfl⟩ | ⟨z, hz, -, rfl⟩)
    · exact (eq_nehari hΩ hw).1
    · exact (eq_nehari hΩs hz).1

/-- T40 helper: at an `(η, R)`-good `w`, `s < η` at every parameter of either side whose Epstein
point lies within `R` of `X(w)`. -/
theorem s04_tb_good_s {K : ℝ} {Ω Ωs : Set ℂ} (hpair : IsKQuasiPair Ω Ωs K) {η R : ℝ} {w : ℂ}
    (hg : IsGoodParam Ω Ωs η R w) :
    (∀ w' ∈ Ω, hdist (epstein Ω w) (epstein Ω w') ≤ R → schwarzNorm Ω w' < η) ∧
      ∀ z ∈ Ωs, hdist (epstein Ω w) (epstein Ωs z) ≤ R → schwarzNorm Ωs z < η := by
  obtain ⟨-, hlt⟩ := hg
  have hΩ := s02_jordanPair_riemannMap (s03_b0_jordanPair hpair)
  have hΩs := s02_jordanPair_riemannMap (s03_b0_jordanPair (s03_qce_swap hpair))
  have hb := (s04_tb_vs_bdd hΩ hΩs (epstein Ω w) R).1
  unfold varsigma at hlt
  refine ⟨fun w' hw' hd => ?_, fun z hz hd => ?_⟩
  · exact lt_of_le_of_lt (le_csSup hb (Or.inl ⟨w', hw', ⟨s04_tb_ep_uhs hΩ hw', hd⟩, rfl⟩)) hlt
  · exact lt_of_le_of_lt (le_csSup hb (Or.inr ⟨z, hz, ⟨s04_tb_ep_uhs hΩs hz, hd⟩, rfl⟩)) hlt

/-- T40 helper: goodness passes to the other side: if `d(X(w), X*(z)) ≤ c`, then `z` is
`(η, R - c)`-good for the swapped pair `(Ω*, Ω)`. -/
theorem s04_tb_good_swap {K : ℝ} {Ω Ωs : Set ℂ} (hpair : IsKQuasiPair Ω Ωs K) {η R c : ℝ}
    {w z : ℂ} (hg : IsGoodParam Ω Ωs η R w) (hz : z ∈ Ωs)
    (hc : hdist (epstein Ω w) (epstein Ωs z) ≤ c) : IsGoodParam Ωs Ω η (R - c) z := by
  obtain ⟨hw, hlt⟩ := hg
  have hΩ := s02_jordanPair_riemannMap (s03_b0_jordanPair hpair)
  have hΩs := s02_jordanPair_riemannMap (s03_b0_jordanPair (s03_qce_swap hpair))
  obtain ⟨hb, -⟩ := s04_tb_vs_bdd hΩ hΩs (epstein Ω w) R
  obtain ⟨-, hnn⟩ := s04_tb_vs_bdd hΩ hΩs (epstein Ω w) R
  have hXw := s04_tb_ep_uhs hΩ hw
  have hXz := s04_tb_ep_uhs hΩs hz
  have htri : ∀ Q ∈ hball (epstein Ωs z) (R - c), Q ∈ hball (epstein Ω w) R := by
    rintro Q ⟨hQ, hd⟩
    refine ⟨hQ, (s02_hdist_triangle hXw hXz hQ).trans ?_⟩
    linarith
  refine ⟨hz, lt_of_le_of_lt ?_ hlt⟩
  unfold varsigma
  refine Real.sSup_le (fun r hr => le_csSup hb ?_) (Real.sSup_nonneg hnn)
  rcases hr with ⟨z', hz', hQ, rfl⟩ | ⟨w', hw', hQ, rfl⟩
  · exact Or.inr ⟨z', hz', htri _ hQ, rfl⟩
  · exact Or.inl ⟨w', hw', htri _ hQ, rfl⟩

/-- T40 helper: for `0 ≤ r`, the disk set `{z ∈ 𝔻 | d_𝔻(0, z) ≤ r}` is the closed Euclidean
ball of radius `√((cosh r - 1)/(cosh r + 1)) < 1`. -/
theorem s04_tb_disk_ball {r : ℝ} (hr : 0 ≤ r) :
    {z | z ∈ unitDisc ∧ diskDist 0 z ≤ r} =
      closedBall 0 (√((Real.cosh r - 1) / (Real.cosh r + 1))) := by
  set C := Real.cosh r with hCdef
  have hC1 : 1 ≤ C := Real.one_le_cosh r
  have hq0 : 0 ≤ (C - 1) / (C + 1) := div_nonneg (by linarith) (by linarith)
  have hq1 : (C - 1) / (C + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hcd : ∀ z : ℂ, ‖z‖ < 1 → diskCoshDist 0 z = 1 + 2 * ‖z‖ ^ 2 / (1 - ‖z‖ ^ 2) := by
    intro z _
    unfold diskCoshDist
    rw [zero_sub, norm_neg, norm_zero]
    ring_nf
  ext z
  simp only [mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨hz, hd⟩
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hz2 : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have hcge : 1 ≤ diskCoshDist 0 z := by
      rw [hcd z hz1]
      have : 0 ≤ 2 * ‖z‖ ^ 2 / (1 - ‖z‖ ^ 2) := by positivity
      linarith
    have hle : diskCoshDist 0 z ≤ C := by
      have h1 : diskDist 0 z ≤ Real.arcosh C := by rw [hCdef, Real.arcosh_cosh hr]; exact hd
      exact (Real.arcosh_le_arcosh (by linarith) (by linarith)).mp h1
    rw [hcd z hz1] at hle
    have h2 : 2 * ‖z‖ ^ 2 ≤ (C - 1) * (1 - ‖z‖ ^ 2) := by
      have := (div_le_iff₀ hz2).mp (by linarith : 2 * ‖z‖ ^ 2 / (1 - ‖z‖ ^ 2) ≤ C - 1)
      linarith
    rw [← Real.sqrt_sq (norm_nonneg z)]
    refine Real.sqrt_le_sqrt ?_
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  · intro hz
    have hz2 : ‖z‖ ^ 2 ≤ (C - 1) / (C + 1) := by
      have := Real.sq_sqrt hq0
      nlinarith [norm_nonneg z, Real.sqrt_nonneg ((C - 1) / (C + 1))]
    have hz1 : ‖z‖ < 1 := by nlinarith [norm_nonneg z]
    have hz2' : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    refine ⟨mem_ball_zero_iff.mpr hz1, ?_⟩
    have hcge : 1 ≤ diskCoshDist 0 z := by
      rw [hcd z hz1]
      have : 0 ≤ 2 * ‖z‖ ^ 2 / (1 - ‖z‖ ^ 2) := by positivity
      linarith
    have hle : diskCoshDist 0 z ≤ C := by
      rw [hcd z hz1]
      have h3 : ‖z‖ ^ 2 * (C + 1) ≤ C - 1 := (le_div_iff₀ (by linarith)).mp hz2
      have h4 : 2 * ‖z‖ ^ 2 / (1 - ‖z‖ ^ 2) ≤ C - 1 := by
        rw [div_le_iff₀ hz2']
        nlinarith
      linarith
    have := (Real.arcosh_le_arcosh (by linarith) (by linarith)).mpr hle
    rw [hCdef, Real.arcosh_cosh hr] at this
    exact this

/-- T40 helper: closed `ρ`-balls are compact. -/
theorem s04_tb_ball_compact {Ω Ωs : Set ℂ} (hΓ : IsJordanPair Ω Ωs) {w : ℂ} (hw : w ∈ Ω)
    (r : ℝ) : IsCompact (rhoClosedBall Ω w r) := by
  obtain ⟨f, hf, hf0⟩ := s02_riemannMap_at hΓ hw
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hS : rhoClosedBall Ω w r = f '' {z | z ∈ unitDisc ∧ diskDist 0 z ≤ r} := by
    ext v
    constructor
    · rintro ⟨hv, hd⟩
      obtain ⟨z, hz, rfl⟩ : v ∈ f '' unitDisc := by rw [hf.2.2]; exact hv
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [← subsec_poincare_dist hf h0 hz, hf0]
      exact hd
    · rintro ⟨z, ⟨hz, hd⟩, rfl⟩
      refine ⟨by rw [← hf.2.2]; exact mem_image_of_mem f hz, ?_⟩
      show poincareDist Ω w (f z) ≤ r
      rw [← hf0, subsec_poincare_dist hf h0 hz]
      exact hd
  rw [hS]
  by_cases hr : 0 ≤ r
  · rw [s04_tb_disk_ball hr]
    refine (isCompact_closedBall 0 _).image_of_continuousOn
      (hf.1.continuousOn.mono ?_)
    intro z hz
    rw [← s04_tb_disk_ball hr] at hz
    exact hz.1
  · have he : {z | z ∈ unitDisc ∧ diskDist 0 z ≤ r} = ∅ := by
      ext z
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨hz, hd⟩
      exact hr ((s02_diskDist_nonneg h0 hz).trans hd)
    rw [he, image_empty]
    exact isCompact_empty

/-- T40 helper: a map continuous and injective on a compact `K ⊇ S` is a topological embedding
of `S`. -/
theorem s04_tb_embed_of_compact {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [T2Space F] {f : E → F} {S K : Set E} (hK : IsCompact K) (hSK : S ⊆ K)
    (hc : ContinuousOn f K) (hinj : InjOn f K) : Topology.IsEmbedding (fun x : S => f x) := by
  have := isCompact_iff_compactSpace.mp hK
  have hg : Topology.IsEmbedding (fun x : K => f x) :=
    (Continuous.isClosedEmbedding (continuousOn_iff_continuous_domRestrict.mp hc)
      fun a b h => Subtype.ext (hinj a.2 b.2 h)).isEmbedding
  exact hg.comp (Topology.IsEmbedding.inclusion hSK)

/-- T40 helper (injectivity of `E`): if `s < 1/2` on `\overline{B_ρ(w, 3r)}`, then `E` is
injective on `\overline{B_ρ(w, r)} × ℝ` (`s03_ul_near` at both base points). -/
theorem s04_tb_E_inj {K : ℝ} {Ω Ωs : Set ℂ} (hpair : IsKQuasiPair Ω Ωs K)
    (hnl : ¬ IsLinePair Ω Ωs) {w : ℂ} (hw : w ∈ Ω) {r : ℝ}
    (hs : ∀ w' ∈ Ω, poincareDist Ω w w' ≤ 3 * r → schwarzNorm Ω w' < 1 / 2) :
    InjOn (normalMap Ω) (rhoClosedBall Ω w r ×ˢ univ) := by
  have hΩ := s02_jordanPair_riemannMap (s03_b0_jordanPair hpair)
  have hnear : ∀ v ∈ rhoClosedBall Ω w r, ∀ w' ∈ Ω, poincareDist Ω v w' ≤ 2 * r →
      schwarzNorm Ω w' < 1 / 2 := by
    rintro v ⟨hv, hdv⟩ w' hw' hd
    refine hs w' hw' ?_
    have := s02_poincareDist_triangle hΩ hw hv hw'
    linarith
  have hd12 : ∀ v₁ ∈ rhoClosedBall Ω w r, ∀ v₂ ∈ rhoClosedBall Ω w r,
      poincareDist Ω v₁ v₂ ≤ 2 * r := by
    rintro v₁ ⟨hv₁, hd₁⟩ v₂ ⟨hv₂, hd₂⟩
    have := s02_poincareDist_triangle hΩ hv₁ hw hv₂
    rw [s02_poincareDist_comm hΩ hv₁ hw] at this
    linarith
  rintro ⟨v₁, τ₁⟩ ⟨h₁, -⟩ ⟨v₂, τ₂⟩ ⟨h₂, -⟩ heq
  change normalGeod Ω v₁ τ₁ = normalGeod Ω v₂ τ₂ at heq
  by_cases hne : v₂ = v₁
  · subst hne
    have hl := s02_poincareDensity_pos hΩ h₁.1
    have e1 := s02_horoPhi_normalGeod Ω v₂ hl τ₁
    rw [heq, s02_horoPhi_normalGeod Ω v₂ hl τ₂] at e1
    rw [Real.exp_injective e1]
  · have a1 := s03_ul_near hpair hnl h₁.1 (hnear v₁ h₁) τ₁ h₂.1 hne (hd12 v₁ h₁ v₂ h₂)
    have a2 := s03_ul_near hpair hnl h₂.1 (hnear v₂ h₂) τ₂ h₁.1 (Ne.symm hne)
      (hd12 v₂ h₂ v₁ h₁)
    rw [heq] at a1
    exact absurd (a1.trans a2) (lt_irrefl _)

/-- T40 stage (i), embedding part (deterministic): if `s < 1/2` on `B_ρ(w, 3r)`, then `X` is a
smooth embedding of `B_ρ(w, r)` (injectivity: `v` is the strict minimizer of `Φ_{X(v)}` on
`B_ρ(v, 2r)` by `s03_ul_near`; immersion: `s ≠ 1`; embedding: compactness of the closed ball). -/
theorem s04_tb_X_embed {K : ℝ} {Ω Ωs : Set ℂ} (hpair : IsKQuasiPair Ω Ωs K)
    (hnl : ¬ IsLinePair Ω Ωs) {w : ℂ} (hw : w ∈ Ω) {r : ℝ}
    (hs : ∀ w' ∈ Ω, poincareDist Ω w w' ≤ 3 * r → schwarzNorm Ω w' < 1 / 2) :
    IsSmoothEmbeddingOn (epstein Ω) (rhoBall Ω w r) := by
  have hΓ := s03_b0_jordanPair hpair
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hΓ
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hsm := lem_fff_smooth ⟨f, hf⟩
  have hsub : rhoBall Ω w r ⊆ rhoClosedBall Ω w r := fun v hv => ⟨hv.1, hv.2.le⟩
  have hcl : rhoClosedBall Ω w r ⊆ Ω := fun v hv => hv.1
  have hinj : InjOn (epstein Ω) (rhoClosedBall Ω w r) := by
    intro v₁ h₁ v₂ h₂ heq
    have e : normalMap Ω (v₁, 0) = normalMap Ω (v₂, 0) := by
      show normalGeod Ω v₁ 0 = normalGeod Ω v₂ 0
      rw [s02_normalGeod_zero Ω v₁ (s02_poincareDensity_pos ⟨f, hf⟩ h₁.1),
        s02_normalGeod_zero Ω v₂ (s02_poincareDensity_pos ⟨f, hf⟩ h₂.1)]
      exact heq
    exact congrArg Prod.fst (s04_tb_E_inj hpair hnl hw hs ⟨h₁, mem_univ _⟩ ⟨h₂, mem_univ _⟩ e)
  refine ⟨⟨Ω, hΩo, hsub.trans hcl, hsm⟩, hinj.mono hsub, fun v hv => ?_,
    s04_tb_embed_of_compact (s04_tb_ball_compact hΓ hw r) hsub (hsm.continuousOn.mono hcl)
      hinj⟩
  have hv0 := s02_poincareDist_nonneg ⟨f, hf⟩ hw hv.1
  have hlt : poincareDist Ω w v < r := hv.2
  refine (lem_fff_immersion ⟨f, hf⟩ hv.1).mpr (ne_of_lt ?_)
  have := hs v hv.1 (by linarith)
  linarith

/-- T40 helper: `E` is smooth on `Ω × ℝ`. -/
theorem s04_tb_nm_smooth {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) :
    ContDiffOn ℝ ∞ (normalMap Ω) (Ω ×ˢ univ) := by
  have hmap : MapsTo Prod.fst (Ω ×ˢ (univ : Set ℝ)) Ω := fun p hp => hp.1
  have hl := (s02_contDiffOn_poincareDensity hf).comp contDiff_fst.contDiffOn hmap
  have hA := (s02_contDiffOn_logDensityDz hf).comp contDiff_fst.contDiffOn hmap
  have hk : ContDiffOn ℝ ∞
      (fun p : ℂ × ℝ => poincareDensity Ω p.1 * Real.exp (-p.2) / 2) (Ω ×ˢ univ) :=
    (hl.mul (Real.contDiff_exp.comp contDiff_snd.neg).contDiffOn).div_const 2
  have hD : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => ‖logDensityDz Ω p.1‖ ^ 2 +
      (poincareDensity Ω p.1 * Real.exp (-p.2) / 2) ^ 2) (Ω ×ˢ univ) :=
    (hA.norm_sq ℝ).add (hk.pow 2)
  have hDpos : ∀ p ∈ Ω ×ˢ (univ : Set ℝ), 0 < ‖logDensityDz Ω p.1‖ ^ 2 +
      (poincareDensity Ω p.1 * Real.exp (-p.2) / 2) ^ 2 := fun p hp => by
    have := s02_poincareDensity_pos ⟨f, hf⟩ hp.1
    positivity
  have hDc : ∀ p ∈ Ω ×ˢ (univ : Set ℝ), ((‖logDensityDz Ω p.1‖ ^ 2 +
      (poincareDensity Ω p.1 * Real.exp (-p.2) / 2) ^ 2 : ℝ) : ℂ) ≠ 0 := fun p hp => by
    exact_mod_cast (hDpos p hp).ne'
  have hc := Complex.conjCLE.contDiff.comp_contDiffOn hA
  have hDC := Complex.ofRealCLM.contDiff.comp_contDiffOn hD
  have h1 := contDiff_fst.contDiffOn.add (hc.mul (hDC.inv hDc))
  have h2 := hk.div hD fun p hp => (hDpos p hp).ne'
  refine (h1.prodMk h2).congr fun p hp => ?_
  simp only [normalMap, normalGeod, Pi.inv_apply, div_eq_mul_inv, Function.comp]
  rfl

/-- T40 helper: the explicit offset and height of `E(w, τ)`: with `D = |A|² + k²`,
`k = λ e^{-τ}/2`, `E(w,τ) - w = (Ā/D, k/D)` and `|W - w|² + ξ² = 1/D`. -/
theorem s04_tb_ng_alg (Ω : Set ℂ) (w : ℂ) (τ : ℝ) (hl : 0 < poincareDensity Ω w) :
    (normalGeod Ω w τ).1 - w = conj (logDensityDz Ω w) /
        ((‖logDensityDz Ω w‖ ^ 2 + (poincareDensity Ω w * Real.exp (-τ) / 2) ^ 2 : ℝ) : ℂ) ∧
      (normalGeod Ω w τ).2 = (poincareDensity Ω w * Real.exp (-τ) / 2) /
        (‖logDensityDz Ω w‖ ^ 2 + (poincareDensity Ω w * Real.exp (-τ) / 2) ^ 2) ∧
      ‖(normalGeod Ω w τ).1 - w‖ ^ 2 + (normalGeod Ω w τ).2 ^ 2 =
        1 / (‖logDensityDz Ω w‖ ^ 2 + (poincareDensity Ω w * Real.exp (-τ) / 2) ^ 2) := by
  have h1 : (normalGeod Ω w τ).1 - w = conj (logDensityDz Ω w) /
      ((‖logDensityDz Ω w‖ ^ 2 + (poincareDensity Ω w * Real.exp (-τ) / 2) ^ 2 : ℝ) : ℂ) := by
    unfold normalGeod
    exact add_sub_cancel_left _ _
  have h2 : (normalGeod Ω w τ).2 = (poincareDensity Ω w * Real.exp (-τ) / 2) /
      (‖logDensityDz Ω w‖ ^ 2 + (poincareDensity Ω w * Real.exp (-τ) / 2) ^ 2) := rfl
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  have hk : 0 < poincareDensity Ω w * Real.exp (-τ) / 2 := by positivity
  generalize logDensityDz Ω w = A
  generalize poincareDensity Ω w * Real.exp (-τ) / 2 = k at hk ⊢
  have hD : 0 < ‖A‖ ^ 2 + k ^ 2 := by positivity
  rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hD.le]
  field_simp

/-- T40 helper (algebra of the immersion of `E`): if
`-2A Re(hA) + (A² + S/2) h + (λ²/4) h̄ + (|A|² + k²) h̄ = 0` and `|S| < λ²/2`, then `h = 0`
(the left side is `(S/2) h + (λ²/4 + k²) h̄`). -/
theorem s04_tb_imm_alg {A S h : ℂ} {l k : ℝ} (hS : ‖S‖ < l ^ 2 / 2)
    (hM : A * (((-2 * (h * A).re : ℝ)) : ℂ) +
        ((A ^ 2 + S / 2) * h + ((l ^ 2 / 4 : ℝ) : ℂ) * conj h) +
      ((‖A‖ ^ 2 + k ^ 2 : ℝ) : ℂ) * conj h = 0) : h = 0 := by
  have hre : (((h * A).re : ℝ) : ℂ) = (h * A + conj h * conj A) / 2 := by
    rw [Complex.re_eq_add_conj, map_mul]
  have hn : ((‖A‖ : ℝ) : ℂ) ^ 2 = A * conj A := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  push_cast at hM
  rw [hre, hn] at hM
  have key : S * h = -(((l ^ 2 / 2 + 2 * k ^ 2 : ℝ)) : ℂ) * conj h := by
    push_cast
    linear_combination 2 * hM
  have hnk := congrArg norm key
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_conj, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)] at hnk
  by_contra hh
  have hpos : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have := mul_right_cancel₀ hpos.ne' hnk
  nlinarith [sq_nonneg k]

/-- T40 helper (immersion of `E`): if `s(v) < 1/2`, then `dE` is injective at `(v, τ)`.
Differentiate the critical-point identity `A(v)(|W - v|² + ξ²) = conj(W - v)` at
`(W, ξ) = E(v, τ)` along a kernel vector `(h, s)`: its `v`-derivative is
`D⁻¹((S/2) h + (λ²/4 + k²) h̄)`, so `h = 0`; and `Φ_{E(v,τ)}(v) = e^τ` gives `s = 0`. -/
theorem s04_tb_E_imm {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {v : ℂ}
    (hv : v ∈ Ω) (hs : schwarzNorm Ω v < 1 / 2) (τ : ℝ) :
    Function.Injective (fderiv ℝ (normalMap Ω) (v, τ)) := by
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hv
  have hU : IsOpen (Ω ×ˢ (univ : Set ℝ)) := hΩo.prod isOpen_univ
  have hp0 : (v, τ) ∈ Ω ×ˢ (univ : Set ℝ) := ⟨hv, mem_univ τ⟩
  have hL : HasFDerivAt (normalMap Ω) (fderiv ℝ (normalMap Ω) (v, τ)) (v, τ) :=
    (((s04_tb_nm_smooth hf).contDiffAt (hU.mem_nhds hp0)).differentiableAt
      (by simp)).hasFDerivAt
  set L := fderiv ℝ (normalMap Ω) (v, τ) with hLdef
  obtain ⟨LA, hLA, hLAv⟩ := s02_fff_hasFDerivAt_A hf hv
  -- `Φ_{E(v,τ)}(v) = e^τ`: the `τ`-derivative `L (0, 1)` is not `0`
  have hL01 : L ((0 : ℂ), (1 : ℝ)) ≠ 0 := by
    intro h0
    have hq0 : 0 < (normalMap Ω (v, τ)).2 := s02_normalGeod_pos Ω v hl τ
    have hφ : DifferentiableAt ℝ (fun q : ℂ × ℝ => horoPhi Ω q v) (normalMap Ω (v, τ)) := by
      have h1 : DifferentiableAt ℝ (fun q : ℂ × ℝ =>
          poincareDensity Ω v * (‖q.1 - v‖ ^ 2 + q.2 ^ 2)) (normalMap Ω (v, τ)) :=
        (((differentiableAt_fst.sub (differentiableAt_const v)).norm_sq ℝ).add
          (differentiableAt_snd.pow 2)).const_mul _
      have h2 : DifferentiableAt ℝ (fun q : ℂ × ℝ => 2 * q.2) (normalMap Ω (v, τ)) :=
        differentiableAt_snd.const_mul 2
      exact (h1.mul (h2.inv (mul_pos two_pos hq0).ne')).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun q => div_eq_mul_inv _ _)
    have hι2 : HasFDerivAt (fun t : ℝ => (v, t))
        ((0 : ℝ →L[ℝ] ℂ).prod (ContinuousLinearMap.id ℝ ℝ)) τ :=
      (hasFDerivAt_const v τ).prodMk (hasFDerivAt_id τ)
    have hc := hφ.hasFDerivAt.comp τ (hL.comp τ hι2)
    have hc' : HasFDerivAt Real.exp ((fderiv ℝ (fun q : ℂ × ℝ => horoPhi Ω q v)
        (normalMap Ω (v, τ))).comp
          (L.comp ((0 : ℝ →L[ℝ] ℂ).prod (ContinuousLinearMap.id ℝ ℝ)))) τ :=
      hc.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => (s02_horoPhi_normalGeod Ω v hl t).symm)
    have hu := congrArg (fun T => T 1) (hc'.unique (Real.hasDerivAt_exp τ).hasFDerivAt)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      zero_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul] at hu
    rw [h0, map_zero] at hu
    exact (Real.exp_pos τ).ne' hu.symm
  -- the critical-point function `F₁(q, w) = A(w)(|W - w|² + ξ²) - conj(W - w)`
  set q0 := normalMap Ω (v, τ) with hq0def
  have hF1z : ∀ p ∈ Ω ×ˢ (univ : Set ℝ),
      logDensityDz Ω p.1 * ((‖(normalMap Ω p).1 - p.1‖ ^ 2 + (normalMap Ω p).2 ^ 2 : ℝ) : ℂ) -
        conj ((normalMap Ω p).1 - p.1) = 0 := by
    rintro ⟨v', τ'⟩ ⟨hv', -⟩
    obtain ⟨e1, -, e3⟩ := s04_tb_ng_alg Ω v' τ' (s02_poincareDensity_pos ⟨f, hf⟩ hv')
    show logDensityDz Ω v' * ((‖(normalGeod Ω v' τ').1 - v'‖ ^ 2 +
      (normalGeod Ω v' τ').2 ^ 2 : ℝ) : ℂ) - conj ((normalGeod Ω v' τ').1 - v') = 0
    rw [e3, e1, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
    push_cast
    ring
  have hF1d : DifferentiableAt ℝ (fun P : (ℂ × ℝ) × ℂ => logDensityDz Ω P.2 *
      ((‖P.1.1 - P.2‖ ^ 2 + P.1.2 ^ 2 : ℝ) : ℂ) - conj (P.1.1 - P.2)) (q0, v) := by
    have hAd : DifferentiableAt ℝ (fun P : (ℂ × ℝ) × ℂ => logDensityDz Ω P.2) (q0, v) :=
      hLA.differentiableAt.comp (q0, v) differentiableAt_snd
    refine (hAd.mul ?_).sub ?_
    · exact Complex.ofRealCLM.differentiableAt.comp _
        (((differentiableAt_fst.fst.sub differentiableAt_snd).norm_sq ℝ).add
          (differentiableAt_fst.snd.pow 2))
    · exact Complex.conjCLE.differentiableAt.comp _
        (differentiableAt_fst.fst.sub differentiableAt_snd)
  set D := fderiv ℝ (fun P : (ℂ × ℝ) × ℂ => logDensityDz Ω P.2 *
      ((‖P.1.1 - P.2‖ ^ 2 + P.1.2 ^ 2 : ℝ) : ℂ) - conj (P.1.1 - P.2)) (q0, v) with hDdef
  have hD := hF1d.hasFDerivAt
  have hG := hD.comp (v, τ) (hL.prodMk (hasFDerivAt_fst (p := (v, τ))))
  have hG0 : HasFDerivAt (fun p : ℂ × ℝ => logDensityDz Ω p.1 *
      ((‖(normalMap Ω p).1 - p.1‖ ^ 2 + (normalMap Ω p).2 ^ 2 : ℝ) : ℂ) -
        conj ((normalMap Ω p).1 - p.1)) (0 : ℂ × ℝ →L[ℝ] ℂ) (v, τ) :=
    (hasFDerivAt_const (0 : ℂ) (v, τ)).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hU.mem_nhds hp0) fun p hp => hF1z p hp)
  have hDL := hG.unique hG0
  -- the `w`-derivative of `F₁(q0, ·)`
  have hι : HasFDerivAt (fun w : ℂ => (q0, w))
      ((0 : ℂ →L[ℝ] ℂ × ℝ).prod (ContinuousLinearMap.id ℝ ℂ)) v :=
    (hasFDerivAt_const q0 v).prodMk (hasFDerivAt_id v)
  have hW1 := hD.comp v hι
  have hsub : HasFDerivAt (fun w : ℂ => q0.1 - w) (0 - ContinuousLinearMap.id ℝ ℂ) v :=
    (hasFDerivAt_const q0.1 v).sub (hasFDerivAt_id v)
  have hNc := Complex.ofRealCLM.hasFDerivAt.comp v (hsub.norm_sq.add_const (q0.2 ^ 2))
  have hM := (hLA.mul hNc).sub ((Complex.conjCLE.hasFDerivAt).comp v hsub)
  have hWW := hW1.unique hM
  rw [injective_iff_map_eq_zero]
  rintro ⟨h, s⟩ hx
  have e1 := congrArg (fun T => T (h, s)) hDL
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', zero_apply] at e1
  rw [hx] at e1
  have e2 := congrArg (fun T => T h) hWW
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply] at e2
  rw [e1] at e2
  have e3 := e2.symm
  simp [Complex.inner] at e3
  -- substitute `E(v, τ) - v = (Ā/D, k/D)`
  obtain ⟨g1, -, g3⟩ := s04_tb_ng_alg Ω v τ hl
  set A0 := logDensityDz Ω v with hA0
  set k := poincareDensity Ω v * Real.exp (-τ) / 2 with hkdef
  have hkp : 0 < k := by rw [hkdef]; positivity
  set D0 := ‖A0‖ ^ 2 + k ^ 2 with hD0
  have hD0p : 0 < D0 := add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hkp 2)
  have g1' : q0.1 - v = conj A0 / (D0 : ℂ) := g1
  have g3' : ‖q0.1 - v‖ ^ 2 + q0.2 ^ 2 = 1 / D0 := g3
  have hr : q0.1.re - v.re = A0.re / D0 := by
    have := congrArg Complex.re g1'
    simpa [Complex.div_ofReal_re] using this
  have hi : q0.1.im - v.im = -A0.im / D0 := by
    have := congrArg Complex.im g1'
    simpa [Complex.div_ofReal_im, neg_div] using this
  have hur : D0 * (q0.1.re - v.re) = A0.re := by rw [hr]; field_simp
  have hui : D0 * (q0.1.im - v.im) = -A0.im := by rw [hi]; field_simp
  have hN : D0 * (‖q0.1 - v‖ ^ 2 + q0.2 ^ 2) = 1 := by rw [g3']; field_simp
  have hurc : (D0 : ℂ) * ((q0.1.re : ℂ) - v.re) = A0.re := by exact_mod_cast hur
  have huic : (D0 : ℂ) * ((q0.1.im : ℂ) - v.im) = -A0.im := by exact_mod_cast hui
  have hNc : (D0 : ℂ) * (((‖q0.1 - v‖ : ℝ) : ℂ) ^ 2 + ((q0.2 : ℝ) : ℂ) ^ 2) = 1 := by
    exact_mod_cast hN
  have hfin : A0 * (((-2 * (h * A0).re : ℝ)) : ℂ) + LA h + (D0 : ℂ) * conj h = 0 := by
    rw [Complex.mul_re]
    push_cast
    linear_combination (D0 : ℂ) * e3 + 2 * A0 * (h.re : ℂ) * hurc +
      2 * A0 * (h.im : ℂ) * huic - LA h * hNc
  rw [hLAv h] at hfin
  have hSb : ‖schwarzian (Function.invFunOn f unitDisc) v‖ < poincareDensity Ω v ^ 2 / 2 := by
    rw [eq_def_s hf hv, div_lt_iff₀ (by positivity)] at hs
    linarith
  have hh : h = 0 := s04_tb_imm_alg (l := poincareDensity Ω v) (k := k) hSb hfin
  subst hh
  have hx' : L ((0 : ℂ), s) = s • L ((0 : ℂ), (1 : ℝ)) := by
    rw [← map_smul]
    simp
  rw [hx'] at hx
  rcases smul_eq_zero.mp hx with h0 | h0
  · subst h0
    rfl
  · exact absurd h0 hL01

/-- T40 stage (ii) (deterministic): if `s < 1/2` on `B_ρ(w, 3r)`, then `E` is a smooth embedding
of `\overline{B_ρ(w, r)} × [a, b]` (injectivity: `E(v₁,τ₁) = E(v₂,τ₂)` makes `v₁`, `v₂` both strict
minimizers by `s03_ul_near`; immersion: differentiate `log Φ_{E(v,τ)}(v) = τ` and the critical
point equation, and use `lem_convexity_lower`). -/
theorem s04_tb_E_embed {K : ℝ} {Ω Ωs : Set ℂ} (hpair : IsKQuasiPair Ω Ωs K)
    (hnl : ¬ IsLinePair Ω Ωs) {w : ℂ} (hw : w ∈ Ω) {r : ℝ}
    (hs : ∀ w' ∈ Ω, poincareDist Ω w w' ≤ 3 * r → schwarzNorm Ω w' < 1 / 2) (a b : ℝ) :
    IsSmoothEmbeddingOn (normalMap Ω) (rhoClosedBall Ω w r ×ˢ Icc a b) := by
  -- The immersion is proved from the critical-point identity (`s04_tb_E_imm`), which needs only
  -- `s < 1/2` at the base point; `lem_convexity_lower` is not used.
  have hΓ := s03_b0_jordanPair hpair
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hΓ
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hsm := s04_tb_nm_smooth hf
  have hS : rhoClosedBall Ω w r ×ˢ Icc a b ⊆ Ω ×ˢ univ := fun p hp => ⟨hp.1.1, mem_univ _⟩
  have hinj : InjOn (normalMap Ω) (rhoClosedBall Ω w r ×ˢ Icc a b) :=
    (s04_tb_E_inj hpair hnl hw hs).mono (prod_mono subset_rfl (subset_univ _))
  refine ⟨⟨Ω ×ˢ univ, hΩo.prod isOpen_univ, hS, hsm⟩, hinj, fun p hp => ?_,
    s04_tb_embed_of_compact ((s04_tb_ball_compact hΓ hw r).prod isCompact_Icc) subset_rfl
      (hsm.continuousOn.mono hS) hinj⟩
  obtain ⟨v, τ⟩ := p
  obtain ⟨⟨hv, hd⟩, -⟩ := hp
  have hd0 := s02_poincareDist_nonneg ⟨f, hf⟩ hw hv
  exact s04_tb_E_imm hf hv (hs v hv (by linarith)) τ

/-- T40 helper (`∂U ⊆ Σ`): a point of `U = horoUnion Ω'` that is not interior to `U` is an
Epstein point `X(z)` (the minimum of `Φ_q` is `1` there, attained at a critical point, and
`lem_normal_a` puts `q` on the normal geodesic of the minimizer at time `0`). -/
theorem s04_tb_bdry {Ω' Ωo : Set ℂ} (hΓ : IsJordanPair Ω' Ωo) {q : ℂ × ℝ} (hq : q ∈ UHS)
    (hU : q ∈ horoUnion Ω') (hni : q ∉ interior (horoUnion Ω')) :
    ∃ z ∈ Ω', epstein Ω' z = q := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hΓ
  have hΩo : IsOpen Ω' := hf.isOpen isOpen_ball
  have hUHS : IsOpen UHS := isOpen_lt continuous_const continuous_snd
  obtain ⟨z, hz, hmin⟩ := lem_proper_min hΓ hq
  have hle1 : horoPhi Ω' q z ≤ 1 := by
    simp only [horoUnion, mem_iUnion] at hU
    obtain ⟨w, hw, hqw⟩ := hU
    exact (hmin w hw).trans hqw.2
  have hge1 : 1 ≤ horoPhi Ω' q z := by
    by_contra hlt
    rw [not_le] at hlt
    apply hni
    have hcont : ContinuousAt (fun q' : ℂ × ℝ => horoPhi Ω' q' z) q :=
      ((s02_horoPhi_continuousOn hΓ).continuousAt
        ((hUHS.prod hΩo).mem_nhds ⟨hq, hz⟩)).comp (continuousAt_id.prodMk continuousAt_const)
    refine mem_interior_iff_mem_nhds.mpr ?_
    filter_upwards [hcont.eventually (Iio_mem_nhds hlt), hUHS.mem_nhds hq] with q' h1 h2
    exact mem_iUnion₂.mpr ⟨z, hz, h2, (show horoPhi Ω' q' z < 1 from h1).le⟩
  have h1 : horoPhi Ω' q z = 1 := le_antisymm hle1 hge1
  obtain ⟨Ll, hLl, -⟩ := s02_fff_hasFDerivAt_lambda hf hz
  have hq2 : 0 < q.2 := hq
  have hd : DifferentiableAt ℝ (fun w' : ℂ => horoPhi Ω' q w') z := by
    have h1 : DifferentiableAt ℝ (fun w' : ℂ =>
        poincareDensity Ω' w' * (‖q.1 - w'‖ ^ 2 + q.2 ^ 2)) z :=
      hLl.differentiableAt.mul
        ((((differentiableAt_const q.1).sub differentiableAt_id).norm_sq ℝ).add_const _)
    exact (h1.mul_const (2 * q.2)⁻¹).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun w' => div_eq_mul_inv _ _)
  have hloc : IsLocalMin (fun w' : ℂ => horoPhi Ω' q w') z :=
    Filter.eventually_of_mem (hΩo.mem_nhds hz) fun w' hw' => hmin w' hw'
  have h0 := hloc.hasFDerivAt_eq_zero hd.hasFDerivAt
  have hcrit : q ∈ {q | q ∈ UHS ∧ HasFDerivAt (fun w' => horoPhi Ω' q w') (0 : ℂ →L[ℝ] ℝ) z} :=
    ⟨hq, h0 ▸ hd.hasFDerivAt⟩
  rw [lem_normal_a ⟨f, hf⟩ hz] at hcrit
  obtain ⟨τ0, hτ0⟩ := hcrit
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hz
  have he := s02_horoPhi_normalGeod Ω' z hl τ0
  rw [hτ0, h1] at he
  have hτ : τ0 = 0 := by
    have := Real.exp_eq_one_iff τ0
    exact this.mp he.symm
  refine ⟨z, hz, ?_⟩
  rw [← s02_normalGeod_zero Ω' z hl, ← hτ, hτ0]

/-- T40 stage (iv) (deterministic): if the ray `τ ↦ E(v, τ)`, `0 ≤ τ ≤ T'`, meets `Σ*` only at
`τ = t ∈ (0, T')`, and `E(v, T') ∈ int U*`, then it lies outside `U*` before `t` and in `int U*`
after `t` (`∂U* ⊆ Σ*` by `lem_proper_min` and `lem_normal_a`; `X(v) ∉ U*` by
`prop_separation_b`; connectedness of the two intervals). -/
theorem s04_tb_sides {K : ℝ} {Ω Ωs : Set ℂ} (hpair : IsKQuasiPair Ω Ωs K)
    (hnl : ¬ IsLinePair Ω Ωs) {v : ℂ} (hv : v ∈ Ω) {t T' : ℝ} (ht : 0 < t) (htT : t < T')
    (huniq : ∀ τ ∈ Icc 0 T', ∀ z ∈ Ωs, epstein Ωs z = normalGeod Ω v τ → τ = t)
    (hT' : normalGeod Ω v T' ∈ interior (horoUnion Ωs)) :
    (∀ τ ∈ Ico 0 t, normalGeod Ω v τ ∉ horoUnion Ωs) ∧
      ∀ τ ∈ Ioc t T', normalGeod Ω v τ ∈ interior (horoUnion Ωs) := by
  have hΓ := s03_b0_jordanPair hpair
  have hΓs := s03_b0_jordanPair (s03_qce_swap hpair)
  have hΩ := s02_jordanPair_riemannMap hΓ
  have hl := s02_poincareDensity_pos hΩ hv
  have hγc : Continuous (normalGeod Ω v) := s03_ul_normalGeod_cont hl
  have hγU : ∀ τ, normalGeod Ω v τ ∈ UHS := (lem_normal_b hΩ hv).1
  have hclo : closure (horoUnion Ωs) ∩ UHS = horoUnion Ωs := lem_proper_closed hΓs
  have hu : IsOpen (normalGeod Ω v ⁻¹' (closure (horoUnion Ωs))ᶜ) :=
    isClosed_closure.isOpen_compl.preimage hγc
  have hV : IsOpen (normalGeod Ω v ⁻¹' interior (horoUnion Ωs)) :=
    isOpen_interior.preimage hγc
  have hdisj : Disjoint (normalGeod Ω v ⁻¹' (closure (horoUnion Ωs))ᶜ)
      (normalGeod Ω v ⁻¹' interior (horoUnion Ωs)) :=
    Set.disjoint_left.mpr fun τ h1 h2 => h1 (interior_subset_closure h2)
  have hcover : ∀ τ ∈ Icc 0 T', τ ≠ t → τ ∈ normalGeod Ω v ⁻¹' (closure (horoUnion Ωs))ᶜ ∪
      normalGeod Ω v ⁻¹' interior (horoUnion Ωs) := by
    intro τ hτ hne
    by_cases hc : normalGeod Ω v τ ∈ closure (horoUnion Ωs)
    · right
      have hU : normalGeod Ω v τ ∈ horoUnion Ωs := by rw [← hclo]; exact ⟨hc, hγU τ⟩
      by_contra hni
      obtain ⟨z, hz, hzq⟩ := s04_tb_bdry hΓs (hγU τ) hU hni
      exact hne (huniq τ hτ z hz hzq)
    · left
      exact hc
  have h0 : (0 : ℝ) ∈ normalGeod Ω v ⁻¹' (closure (horoUnion Ωs))ᶜ := by
    intro hc
    have hU : normalGeod Ω v 0 ∈ horoUnion Ωs := by rw [← hclo]; exact ⟨hc, hγU 0⟩
    have hX : normalGeod Ω v 0 ∈ horoUnion Ω := mem_iUnion₂.mpr ⟨v, hv, hγU 0,
      by rw [s02_horoPhi_normalGeod Ω v hl 0, Real.exp_zero]⟩
    have hint : normalGeod Ω v 0 ∈ horoUnion Ω ∩ horoUnion Ωs := ⟨hX, hU⟩
    rw [(prop_separation_b hΓ hnl).2] at hint
    exact hint
  refine ⟨fun τ hτ => ?_, fun τ hτ => ?_⟩
  · have hsub : Ico 0 t ⊆ normalGeod Ω v ⁻¹' (closure (horoUnion Ωs))ᶜ :=
      isPreconnected_Ico.subset_left_of_subset_union hu hV hdisj
        (fun τ' hτ' => hcover τ' ⟨hτ'.1, by linarith [hτ'.2]⟩ (ne_of_lt hτ'.2))
        ⟨0, ⟨le_rfl, ht⟩, h0⟩
    intro hU
    exact hsub hτ (subset_closure hU)
  · have hsub : Ioc t T' ⊆ normalGeod Ω v ⁻¹' interior (horoUnion Ωs) :=
      isPreconnected_Ioc.subset_right_of_subset_union hu hV hdisj
        (fun τ' hτ' => hcover τ' ⟨by linarith [hτ'.1], hτ'.2⟩ (ne_of_gt hτ'.1))
        ⟨T', ⟨htT, le_rfl⟩, hT'⟩
    exact hsub hτ

-- Relocated byte-identically from `S05_Upper` (w2, lines 461-593; approved 2026-11-04).
/-- Shape helper (SA6): `II(u, v) = -s²λ² Re(u v̄) - Re(S(f⁻¹) u v)` (the identity
`II = λ² Re(u v̄) + Re(S u v) - I` of the proof of `prop_curvature`, with Lemma 2.5). -/
theorem s05_sa_secondFF {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) (u v : ℂ) :
    secondFF Ω w u v =
      -(schwarzNorm Ω w ^ 2 * poincareDensity Ω w ^ 2 * (u * conj v).re) -
        (schwarzian (Function.invFunOn f unitDisc) w * u * v).re := by
  have hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω := ⟨f, hf⟩
  have hl := s02_poincareDensity_pos hΩ hw
  obtain ⟨Ll, hLl, hLlv⟩ := s02_fff_hasFDerivAt_lambda hf hw
  obtain ⟨LA, hLA, hLAv⟩ := s02_fff_hasFDerivAt_A hf hw
  obtain ⟨L, hL, hLv⟩ := s02_fff_hasFDerivAt_ep hLl hLA hl
  have hX : fderiv ℝ (epstein Ω) w = L := hL.fderiv
  obtain ⟨Ln, hLn, hLnv⟩ := s02_curv_hasFDerivAt_normal hf hw
  have hnd : fderiv ℝ (fun w' => deriv (fun τ : ℝ => normalGeod Ω w' τ) 0) w = Ln := hLn.fderiv
  have hnw := s02_curv_normal_eq hl
  have hfI := s02_curv_fI hf hw u v
  -- `II` unfolded (the Levi-Civita term written out, as in `lem_shape_b`)
  have hII : secondFF Ω w u v =
      hypInner (epstein Ω w)
        (-(fderiv ℝ (fun w' => deriv (fun τ : ℝ => normalGeod Ω w' τ) 0) w u -
          ((fderiv ℝ (epstein Ω) w u).2 / (epstein Ω w).2) •
            deriv (fun τ : ℝ => normalGeod Ω w τ) 0 -
          ((deriv (fun τ : ℝ => normalGeod Ω w τ) 0).2 / (epstein Ω w).2) •
            fderiv ℝ (epstein Ω) w u +
          ((((fderiv ℝ (epstein Ω) w u).1 *
              conj (deriv (fun τ : ℝ => normalGeod Ω w τ) 0).1).re +
            (fderiv ℝ (epstein Ω) w u).2 * (deriv (fun τ : ℝ => normalGeod Ω w τ) 0).2) /
              (epstein Ω w).2) • ((0 : ℂ), (1 : ℝ))))
        (fderiv ℝ (epstein Ω) w v) := by
    unfold secondFF hypChristoffel normalVec
    congr 2
    ext <;> simp [Complex.mul_re] <;> ring
  set q := epstein Ω w with hq
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
  have horth : ∀ v, ((q.1 - w) * conj (fderiv ℝ (epstein Ω) w v).1).re +
      (q.2 - 1 / l) * (fderiv ℝ (epstein Ω) w v).2 = 0 := by
    intro v
    rw [hX, hLv v, hP, hξ]
    exact s02_curv_orth_alg hl (hLlv v) rfl
  have h1 := s02_curv_shape_alg (q := q) (a := fderiv ℝ (epstein Ω) w u)
    (b := fderiv ℝ (epstein Ω) w v) (n := deriv (fun τ : ℝ => normalGeod Ω w τ) 0)
    (Dn := fderiv ℝ (fun w' => deriv (fun τ : ℝ => normalGeod Ω w' τ) 0) w u) (u := u)
    (dl := Ll u) (P := q.1 - w) hl hξ0 rfl hnw (by rw [hnd, hLnv u, hLlv u]) (horth u) (horth v)
  have h2 : l / q.2 * ((u * conj (fderiv ℝ (epstein Ω) w v).1).re -
      Ll u * (fderiv ℝ (epstein Ω) w v).2 / l ^ 2) = l ^ 2 * (u * conj v).re + (S * u * v).re := by
    rw [hX, hLv v, hξ]
    exact s02_curv_M_alg hl (hLlv v) (hLlv u) (hLAv v) rfl
  rw [hII, h1, h2, hfI]
  ring

/-- Shape helper (SA7): `B v = (s² v - \overline{S(f⁻¹)} v̄/λ²)/(1 - s²)` for `s ≠ 1`
(`I(Bv, v') = II(v, v')`, inverting `I = (1+s²)λ² Re(· \bar{·}) + 2 Re(S · ·)`). -/
theorem s05_sa_shapeApply {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) (hs : schwarzNorm Ω w ≠ 1) (v : ℂ) :
    shapeApply Ω w v =
      (((schwarzNorm Ω w ^ 2 : ℝ) : ℂ) * v -
          conj (schwarzian (Function.invFunOn f unitDisc) w) * conj v /
            ((poincareDensity Ω w ^ 2 : ℝ) : ℂ)) /
        ((1 - schwarzNorm Ω w ^ 2 : ℝ) : ℂ) := by
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hw
  have hS : ‖schwarzian (Function.invFunOn f unitDisc) w‖ =
      schwarzNorm Ω w * poincareDensity Ω w ^ 2 := by
    rw [eq_def_s hf hw]
    field_simp
  have hs0 : 0 ≤ schwarzNorm Ω w := by
    rw [eq_def_s hf hw]
    positivity
  have hM : ∀ i j, fffMat Ω w i j =
      (1 + schwarzNorm Ω w ^ 2) * poincareDensity Ω w ^ 2 * (frameVec i * conj (frameVec j)).re +
        2 * (schwarzian (Function.invFunOn f unitDisc) w * frameVec i * frameVec j).re :=
    fun i j => s02_curv_fI hf hw (frameVec i) (frameVec j)
  have hT : ∀ i j, secondFFMat Ω w i j =
      -(schwarzNorm Ω w ^ 2 * poincareDensity Ω w ^ 2 * (frameVec i * conj (frameVec j)).re) -
        (schwarzian (Function.invFunOn f unitDisc) w * frameVec i * frameVec j).re :=
    fun i j => s05_sa_secondFF hf hw (frameVec i) (frameVec j)
  unfold shapeApply shapeMat
  generalize fffMat Ω w = M at hM ⊢
  generalize secondFFMat Ω w = T at hT ⊢
  generalize schwarzNorm Ω w = s at hS hs0 hs hM hT ⊢
  generalize poincareDensity Ω w = l at hl hS hM hT ⊢
  generalize schwarzian (Function.invFunOn f unitDisc) w = S at hS hM hT ⊢
  have hab : S.re ^ 2 + S.im ^ 2 = (s * l ^ 2) ^ 2 := by
    rw [← hS, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hl0 : l ≠ 0 := hl.ne'
  have hk : 1 - s ^ 2 ≠ 0 := by
    have e : 1 - s ^ 2 = (1 - s) * (1 + s) := by ring
    rw [e]
    exact mul_ne_zero (sub_ne_zero.2 (Ne.symm hs)) (by positivity)
  have hdet : M.det = ((1 - s ^ 2) * l ^ 2) ^ 2 := by
    rw [Matrix.det_fin_two, hM, hM, hM, hM]
    simp [frameVec, Complex.mul_re, Complex.mul_im]
    linear_combination (-4) * hab
  have hu : IsUnit M.det := by
    rw [hdet]
    exact isUnit_iff_ne_zero.2 (pow_ne_zero 2 (mul_ne_zero hk (pow_ne_zero 2 hl0)))
  have key : Tᵀ *ᵥ cvec v = M *ᵥ cvec ((((s ^ 2 : ℝ) : ℂ) * v - conj S * conj v /
      ((l ^ 2 : ℝ) : ℂ)) / ((1 - s ^ 2 : ℝ) : ℂ)) := by
    ext i
    fin_cases i
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply, hM, hT,
        cvec, frameVec, Fin.isValue, Fin.zero_eta, Complex.ofReal_re,
        Complex.ofReal_im, Matrix.cons_val_zero, Matrix.cons_val_one,
        Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im, Complex.I_re,
        Complex.I_im, map_one]
      linear_combination (norm := skip) (2 * v.re / ((1 - s ^ 2) * l ^ 2)) * hab
      field_simp
      ring
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply, hM, hT,
        cvec, frameVec, Fin.isValue, Fin.mk_one, Complex.ofReal_re,
        Complex.ofReal_im, Matrix.cons_val_zero, Matrix.cons_val_one,
        Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im, Complex.I_re,
        Complex.I_im, Complex.conj_I, Complex.neg_re, Complex.neg_im]
      linear_combination (norm := skip) (2 * v.im / ((1 - s ^ 2) * l ^ 2)) * hab
      field_simp
      ring
  rw [← Matrix.mulVec_mulVec, key, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hu,
    Matrix.one_mulVec]
  rfl

/-- Shape helper (SA1): the velocity of the normal geodesic at time `τ`.  With `h = λe^{-τ}/2`
and `D = |A|² + h²`: `∂_τE(w, τ) = (Ā · 2h²/D², h(h² - |A|²)/D²)`. -/
theorem s05_sa_hasDerivAt_tau (Ω : Set ℂ) (w : ℂ) (hl : 0 < poincareDensity Ω w) (τ : ℝ) :
    HasDerivAt (fun τ' : ℝ => normalGeod Ω w τ')
      (conj (logDensityDz Ω w) *
          (((2 * (poincareDensity Ω w * Real.exp (-τ) / 2) ^ 2) /
            (‖logDensityDz Ω w‖ ^ 2 + (poincareDensity Ω w * Real.exp (-τ) / 2) ^ 2) ^ 2 : ℝ) : ℂ),
        (poincareDensity Ω w * Real.exp (-τ) / 2) *
            ((poincareDensity Ω w * Real.exp (-τ) / 2) ^ 2 - ‖logDensityDz Ω w‖ ^ 2) /
          (‖logDensityDz Ω w‖ ^ 2 + (poincareDensity Ω w * Real.exp (-τ) / 2) ^ 2) ^ 2) τ := by
  unfold normalGeod
  generalize poincareDensity Ω w = l at hl ⊢
  generalize logDensityDz Ω w = A
  have hh : HasDerivAt (fun τ : ℝ => l * Real.exp (-τ) / 2) (-(l * Real.exp (-τ) / 2)) τ := by
    have := (((hasDerivAt_neg τ).exp).const_mul l).div_const 2
    convert this using 1
    ring
  have hD : HasDerivAt (fun τ : ℝ => ‖A‖ ^ 2 + (l * Real.exp (-τ) / 2) ^ 2)
      (2 * (l * Real.exp (-τ) / 2) * (-(l * Real.exp (-τ) / 2))) τ := by
    have := (hh.pow 2).const_add (‖A‖ ^ 2)
    convert this using 1
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  have hD0 : ‖A‖ ^ 2 + (l * Real.exp (-τ) / 2) ^ 2 ≠ 0 := by positivity
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
  refine Prod.ext ?_ ?_
  · dsimp only
    congr 1
    norm_cast
    ring
  · dsimp only
    ring

/-- Shape helper (SA2): `|∂_τE| = 1` (first claim of Lemma 5.2 (a)). -/
theorem s05_sa_unit (Ω : Set ℂ) (w : ℂ) (hl : 0 < poincareDensity Ω w) (τ : ℝ) :
    hypInner (normalGeod Ω w τ) (deriv (fun τ' => normalGeod Ω w τ') τ)
      (deriv (fun τ' => normalGeod Ω w τ') τ) = 1 := by
  rw [(s05_sa_hasDerivAt_tau Ω w hl τ).deriv]
  unfold hypInner normalGeod
  have hh : 0 < poincareDensity Ω w * Real.exp (-τ) / 2 := by positivity
  generalize poincareDensity Ω w * Real.exp (-τ) / 2 = h at hh ⊢
  generalize logDensityDz Ω w = A
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hD0 : A.re * A.re + A.im * A.im + h ^ 2 ≠ 0 :=
    (by nlinarith [mul_self_nonneg A.re, mul_self_nonneg A.im, pow_pos hh 2] :
      (0 : ℝ) < A.re * A.re + A.im * A.im + h ^ 2).ne'
  field_simp
  ring

/-- Shape helper (SA3): the derivative of `w ↦ E(w, τ)` from those of `λ` and `A`.  With
`h = λe^{-τ}/2`, `D = |A|² + h²`, `dh = dλ(v) e^{-τ}/2`, `dD = 2 Re(Ā dA(v)) + 2h dh`:
`d_wE(v) = (v + \overline{dA(v)}/D - Ā dD/D², dh/D - h dD/D²)`. -/
theorem s05_sa_hasFDerivAt_w {Ω : Set ℂ} {w : ℂ} {Ll : ℂ →L[ℝ] ℝ} {LA : ℂ →L[ℝ] ℂ}
    (hLl : HasFDerivAt (poincareDensity Ω) Ll w) (hLA : HasFDerivAt (logDensityDz Ω) LA w)
    (hl : 0 < poincareDensity Ω w) (τ : ℝ) :
    ∃ L : ℂ →L[ℝ] ℂ × ℝ, HasFDerivAt (fun x => normalGeod Ω x τ) L w ∧
      ∀ (v : ℂ) (h D dh dD : ℝ), h = poincareDensity Ω w * Real.exp (-τ) / 2 →
        D = ‖logDensityDz Ω w‖ ^ 2 + h ^ 2 → dh = Ll v * Real.exp (-τ) / 2 →
        dD = 2 * (conj (logDensityDz Ω w) * LA v).re + 2 * h * dh →
        L v = (v + conj (LA v) / (D : ℂ) - conj (logDensityDz Ω w) * ((dD / D ^ 2 : ℝ) : ℂ),
          dh / D - h * dD / D ^ 2) := by
  have hh := hLl.const_mul (Real.exp (-τ) / 2)
  have hD := (hLA.norm_sq).add (hh.pow 2)
  have hD0 : ‖logDensityDz Ω w‖ ^ 2 + (Real.exp (-τ) / 2 * poincareDensity Ω w) ^ 2 ≠ 0 := by
    positivity
  have hDi := (hasDerivAt_inv hD0).comp_hasFDerivAt w hD
  have hDic := (Complex.ofRealCLM.hasFDerivAt).comp w hDi
  have hcA := ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt).comp w hLA
  have hW := (hasFDerivAt_id w).add (hcA.mul hDic)
  have hξ := hh.mul hDi
  refine ⟨_, (hW.prodMk hξ).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_),
    fun v h D dh dD hh' hD' hdh hdD => ?_⟩
  · beta_reduce
    unfold normalGeod
    rw [show poincareDensity Ω x * Real.exp (-τ) / 2 = Real.exp (-τ) / 2 * poincareDensity Ω x
      by ring]
    refine Prod.ext ?_ ?_
    · simp [div_eq_mul_inv]
    · simp [div_eq_mul_inv]
  · subst hh' hD' hdh hdD
    refine Prod.ext ?_ ?_
    · simp [Complex.inner, div_eq_mul_inv]
      ring
    · simp [Complex.inner, div_eq_mul_inv]
      ring

/-- Shape helper (SA4, algebra): `∂_τE ⊥ d_wE(v)` (Euclidean numerator of `hypInner`), for any
value `dA` of the derivative of `A`. -/
theorem s05_sa_orth_alg {h D dh dD : ℝ} {A dA v : ℂ} (hh : 0 < h) (hD : D = ‖A‖ ^ 2 + h ^ 2)
    (hdh : dh = h * (2 * (A * v).re)) (hdD : dD = 2 * (conj A * dA).re + 2 * h * dh) :
    ((conj A * ((2 * h ^ 2 / D ^ 2 : ℝ) : ℂ)) *
        conj (v + conj dA / (D : ℂ) - conj A * ((dD / D ^ 2 : ℝ) : ℂ))).re +
      h * (h ^ 2 - ‖A‖ ^ 2) / D ^ 2 * (dh / D - h * dD / D ^ 2) = 0 := by
  subst hdD
  subst hdh
  rw [Complex.sq_norm, Complex.normSq_apply] at hD ⊢
  subst hD
  simp only [map_sub, map_add, map_mul, map_div₀, Complex.conj_conj, Complex.conj_ofReal,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.add_re, Complex.sub_im,
    Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.div_ofReal_re, Complex.div_ofReal_im]
  have hD0 : A.re * A.re + A.im * A.im + h ^ 2 ≠ 0 :=
    (by nlinarith [mul_self_nonneg A.re, mul_self_nonneg A.im, pow_pos hh 2] :
      (0 : ℝ) < A.re * A.re + A.im * A.im + h ^ 2).ne'
  field_simp
  ring

/-- Shape helper (SA5, algebra): the metric of the equidistant surface,
`⟨d_wE v, d_wE v'⟩ = (cosh²τ + s²e^{2τ}) λ² Re(v v̄') + 2 cosh τ e^τ Re(S v v')`, from
`dλ(v) = 2λ Re(Av)`, `dA(v) = (A² + S/2)v + (λ²/4)v̄` and `|S| = sλ²`. -/
theorem s05_sa_gram_alg {l s τ h D dh dh' dD dD' : ℝ} {A S v v' dA dA' z0 : ℂ} (hl : 0 < l)
    (hh : h = l * Real.exp (-τ) / 2) (hD : D = ‖A‖ ^ 2 + h ^ 2)
    (hdh : dh = h * (2 * (A * v).re)) (hdh' : dh' = h * (2 * (A * v').re))
    (hdA : dA = (A ^ 2 + S / 2) * v + ((l ^ 2 / 4 : ℝ) : ℂ) * conj v)
    (hdA' : dA' = (A ^ 2 + S / 2) * v' + ((l ^ 2 / 4 : ℝ) : ℂ) * conj v')
    (hdD : dD = 2 * (conj A * dA).re + 2 * h * dh)
    (hdD' : dD' = 2 * (conj A * dA').re + 2 * h * dh') (hS : ‖S‖ = s * l ^ 2) :
    hypInner (z0, h / D)
        (v + conj dA / (D : ℂ) - conj A * ((dD / D ^ 2 : ℝ) : ℂ), dh / D - h * dD / D ^ 2)
        (v' + conj dA' / (D : ℂ) - conj A * ((dD' / D ^ 2 : ℝ) : ℂ), dh' / D - h * dD' / D ^ 2) =
      (Real.cosh τ ^ 2 + s ^ 2 * Real.exp τ ^ 2) * l ^ 2 * (v * conj v').re +
        2 * Real.cosh τ * Real.exp τ * (S * v * v').re := by
  have hab : S.re ^ 2 + S.im ^ 2 = (s * l ^ 2) ^ 2 := by
    rw [← hS, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hh0 : 0 < h := by rw [hh]; exact div_pos (mul_pos hl (Real.exp_pos _)) two_pos
  have hD0 : 0 < D := by rw [hD]; exact add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hh0 2)
  have hl2 : l = 2 * h * Real.exp τ := by
    rw [hh, Real.exp_neg]
    field_simp
  have hc : Real.cosh τ * Real.exp τ = (Real.exp τ ^ 2 + 1) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg]
    field_simp
  -- clear the denominators `D²` of `d_wE` by hand
  have hDc : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hD0.ne'
  have e1 : ∀ (dA : ℂ) (dD : ℝ), v + conj dA / (D : ℂ) - conj A * ((dD / D ^ 2 : ℝ) : ℂ) =
      (v * ((D ^ 2 : ℝ) : ℂ) + conj dA * (D : ℂ) - conj A * (dD : ℂ)) / ((D ^ 2 : ℝ) : ℂ) := by
    intro dA dD
    push_cast
    field_simp
  have e1' : ∀ (dA : ℂ) (dD : ℝ), v' + conj dA / (D : ℂ) - conj A * ((dD / D ^ 2 : ℝ) : ℂ) =
      (v' * ((D ^ 2 : ℝ) : ℂ) + conj dA * (D : ℂ) - conj A * (dD : ℂ)) / ((D ^ 2 : ℝ) : ℂ) := by
    intro dA dD
    push_cast
    field_simp
  have e2 : ∀ dh dD : ℝ, dh / D - h * dD / D ^ 2 = (dh * D - h * dD) / D ^ 2 := by
    intro dh dD
    field_simp
  have key : ∀ (X Y : ℂ) (x y : ℝ), hypInner (z0, h / D) (X / ((D ^ 2 : ℝ) : ℂ), x / D ^ 2)
      (Y / ((D ^ 2 : ℝ) : ℂ), y / D ^ 2) = ((X * conj Y).re + x * y) / (D ^ 2 * h ^ 2) := by
    intro X Y x y
    unfold hypInner
    dsimp only
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, ← Complex.ofReal_mul,
      Complex.div_ofReal_re]
    have hh2 : h ≠ 0 := hh0.ne'
    have hD2 : D ≠ 0 := hD0.ne'
    field_simp
  rw [e1, e1', e2, e2, key, div_eq_iff (mul_pos (pow_pos hD0 2) (pow_pos hh0 2)).ne']
  clear e1 e1' e2 key hDc
  clear hh
  subst hl2
  subst hdD hdD'
  subst hdA hdA' hdh hdh'
  -- `(cosh τ e^τ)` and `|S|² = s²λ⁴` are the only relations used
  linear_combination (norm := skip) (D ^ 2 * (v * conj v').re / 4) * hab +
    (-2 * D ^ 2 * (h ^ 4 * (v * conj v').re * (Real.exp τ ^ 2 + 1 + 2 * Real.cosh τ * Real.exp τ) +
      h ^ 2 * (S * v * v').re)) * hc
  simp only [map_sub, map_add, map_mul, Complex.conj_conj, Complex.conj_ofReal,
    pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.add_re, Complex.sub_im,
    Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im]
  rw [Complex.sq_norm, Complex.normSq_apply] at hD
  subst hD
  ring

/-- Shape helper (SA8): the right side of Lemma 5.2 (a),
`I((cosh τ - sinh τ B)v, (cosh τ - sinh τ B)v') = (cosh²τ + s²e^{2τ}) λ² Re(v v̄') +
2 cosh τ e^τ Re(S v v')`. -/
theorem s05_sa_rhs {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) (hs : schwarzNorm Ω w ≠ 1) (τ : ℝ) (v v' : ℂ) :
    fffT Ω w ![(Real.cosh τ : ℂ) * v - (Real.sinh τ : ℂ) * shapeApply Ω w v,
        (Real.cosh τ : ℂ) * v' - (Real.sinh τ : ℂ) * shapeApply Ω w v'] =
      (Real.cosh τ ^ 2 + schwarzNorm Ω w ^ 2 * Real.exp τ ^ 2) * poincareDensity Ω w ^ 2 *
          (v * conj v').re +
        2 * Real.cosh τ * Real.exp τ * (schwarzian (Function.invFunOn f unitDisc) w * v * v').re := by
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hw
  have hS : ‖schwarzian (Function.invFunOn f unitDisc) w‖ =
      schwarzNorm Ω w * poincareDensity Ω w ^ 2 := by
    rw [eq_def_s hf hw]
    field_simp
  have hs0 : 0 ≤ schwarzNorm Ω w := by
    rw [eq_def_s hf hw]
    positivity
  have hI := s02_curv_fI hf hw ((Real.cosh τ : ℂ) * v - (Real.sinh τ : ℂ) * shapeApply Ω w v)
    ((Real.cosh τ : ℂ) * v' - (Real.sinh τ : ℂ) * shapeApply Ω w v')
  refine hI.trans ?_
  rw [s05_sa_shapeApply hf hw hs v, s05_sa_shapeApply hf hw hs v', ← Real.cosh_add_sinh τ]
  generalize Real.cosh τ = c
  generalize Real.sinh τ = σ
  generalize schwarzNorm Ω w = s at hS hs0 hs ⊢
  generalize poincareDensity Ω w = l at hl hS ⊢
  generalize schwarzian (Function.invFunOn f unitDisc) w = S at hS ⊢
  have hab : S.re ^ 2 + S.im ^ 2 = (s * l ^ 2) ^ 2 := by
    rw [← hS, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hl0 : l ≠ 0 := hl.ne'
  have hk : 1 - s ^ 2 ≠ 0 := by
    have e : 1 - s ^ 2 = (1 - s) * (1 + s) := by ring
    rw [e]
    exact mul_ne_zero (sub_ne_zero.2 (Ne.symm hs)) (by positivity)
  simp only [map_sub, map_mul, map_div₀, Complex.conj_conj, Complex.conj_ofReal,
    Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  linear_combination (norm := skip)
    (σ ^ 2 * ((1 + s ^ 2) * (v.re * v'.re + v.im * v'.im) / (l ^ 2 * (1 - s ^ 2) ^ 2) +
      2 * ((S.re * (v.re * v'.re - v.im * v'.im) - S.im * (v.re * v'.im + v.im * v'.re)) /
          l ^ 4 - 2 * s ^ 2 * (v.re * v'.re + v.im * v'.im) / l ^ 2) / (1 - s ^ 2) ^ 2) +
      4 * c * σ * (v.re * v'.re + v.im * v'.im) / (l ^ 2 * (1 - s ^ 2))) * hab
  field_simp
  ring

/-- **Lemma 5.2 (a)** (`lem:shape`, sec05-upper.tex:37), isometric form of (5.2)–(5.3).  Let
`w ∈ Ω` with `s(w) ≠ 1`.  The Jacobi field formula
`d_wE(·,τ)(v) = P_τ(cosh τ dX(v) - sinh τ dX(Bv))` with `P_τ` the parallel transport along `γ_w` is
recorded through its metric content: `|∂_τ E| = 1`, `∂_τE ⊥ d_wE(·,τ)(v)`, and
`⟨d_wE(·,τ)v, d_wE(·,τ)v'⟩ = I((cosh τ - sinh τ B)v, (cosh τ - sinh τ B)v')`, i.e.
`E^* g_{ℍ³} = dτ² + g_τ` (`eq:fermi`).  (The parallel transport `P_τ` itself is not
formalized.) -/
theorem lem_shape_a : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ w ∈ Ω, schwarzNorm Ω w ≠ 1 →
    ∀ τ : ℝ,
      hypInner (normalGeod Ω w τ) (deriv (fun τ' => normalGeod Ω w τ') τ)
          (deriv (fun τ' => normalGeod Ω w τ') τ) = 1 ∧
      (∀ v : ℂ, hypInner (normalGeod Ω w τ) (deriv (fun τ' => normalGeod Ω w τ') τ)
          (fderiv ℝ (fun x => normalGeod Ω x τ) w v) = 0) ∧
      ∀ v v' : ℂ, hypInner (normalGeod Ω w τ) (fderiv ℝ (fun x => normalGeod Ω x τ) w v)
          (fderiv ℝ (fun x => normalGeod Ω x τ) w v') =
        fffT Ω w ![(Real.cosh τ : ℂ) * v - (Real.sinh τ : ℂ) * shapeApply Ω w v,
          (Real.cosh τ : ℂ) * v' - (Real.sinh τ : ℂ) * shapeApply Ω w v'] := by
  intro Ω Ωs hJ w hw hs1 τ
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hw
  obtain ⟨Ll, hLl, hLlv⟩ := s02_fff_hasFDerivAt_lambda hf hw
  obtain ⟨LA, hLA, hLAv⟩ := s02_fff_hasFDerivAt_A hf hw
  obtain ⟨L, hL, hLv⟩ := s05_sa_hasFDerivAt_w hLl hLA hl τ
  have hfd : ∀ v, fderiv ℝ (fun x => normalGeod Ω x τ) w v = L v := fun v => by rw [hL.fderiv]
  have hdt := (s05_sa_hasDerivAt_tau Ω w hl τ).deriv
  have hS : ‖schwarzian (Function.invFunOn f unitDisc) w‖ =
      schwarzNorm Ω w * poincareDensity Ω w ^ 2 := by
    rw [eq_def_s hf hw]
    field_simp
  set h := poincareDensity Ω w * Real.exp (-τ) / 2 with hh
  set D := ‖logDensityDz Ω w‖ ^ 2 + h ^ 2 with hD
  have hh0 : 0 < h := by positivity
  have hdh : ∀ v, Ll v * Real.exp (-τ) / 2 = h * (2 * (logDensityDz Ω w * v).re) := by
    intro v
    rw [hLlv, hh]
    ring
  refine ⟨s05_sa_unit Ω w hl τ, fun v => ?_, fun v v' => ?_⟩
  · rw [hdt, hfd v, hLv v h D _ _ rfl rfl rfl rfl]
    unfold hypInner
    rw [s05_sa_orth_alg hh0 rfl (hdh v) rfl, zero_div]
  · rw [hfd v, hfd v', hLv v h D _ _ rfl rfl rfl rfl, hLv v' h D _ _ rfl rfl rfl rfl,
      s05_sa_rhs hf hw hs1 τ v v']
    exact s05_sa_gram_alg hl rfl rfl (hdh v) (hdh v') (hLAv v) (hLAv v') rfl rfl hS

/-! ## §4.2 Tube lemma, stage 2 (interfaces T42, T43, w5)

The `C^∞_loc` toolkit (C), naturality under real similarities (N), normalization and
compactness (P), convergence of the data (D), W-CJ (W) and the slab graph (G), assembled
into `s04_tb_X_norm` and `s04_tb_graph`. -/

universe u

/-! ## C: the `C^∞_loc` convergence toolkit -/

/-- T42 C helper: for a limit continuous on `U`, locally uniform convergence on `U` is
convergence of `(n, y) ↦ F n y` along `atTop ×ˢ 𝓝[U] x` for every `x ∈ U`. -/
theorem s04_tc_cc {α β : Type*} [TopologicalSpace α] [PseudoMetricSpace β] {U : Set α}
    {F : ℕ → α → β} {f : α → β} (hf : ContinuousOn f U) :
    TendstoLocallyUniformlyOn F f atTop U ↔
      ∀ x ∈ U, Tendsto (fun q : ℕ × α => F q.1 q.2) (atTop ×ˢ 𝓝[U] x) (𝓝 (f x)) := by
  constructor
  · intro h x hx
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨t, ht, hev⟩ := Metric.tendstoLocallyUniformlyOn_iff.1 h (ε / 2) (half_pos hε) x hx
    have hc : ∀ᶠ y in 𝓝[U] x, dist (f y) (f x) < ε / 2 :=
      Metric.tendsto_nhds.1 (hf x hx) _ (half_pos hε)
    have h2 : ∀ᶠ y in 𝓝[U] x, y ∈ t ∧ dist (f y) (f x) < ε / 2 :=
      (Filter.eventually_mem_set.2 ht).and hc
    filter_upwards [hev.prod_mk h2] with q hq
    have h3 := hq.1 q.2 hq.2.1
    have h4 := hq.2.2
    have h5 := dist_triangle (F q.1 q.2) (f q.2) (f x)
    have h6 := dist_comm (F q.1 q.2) (f q.2)
    linarith
  · intro h
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε x hx
    have h1 := Metric.tendsto_nhds.1 (h x hx) (ε / 2) (half_pos hε)
    obtain ⟨pa, hpa, pb, hpb, hp⟩ := eventually_prod_iff.1 h1
    have hc : ∀ᶠ y in 𝓝[U] x, dist (f y) (f x) < ε / 2 :=
      Metric.tendsto_nhds.1 (hf x hx) _ (half_pos hε)
    refine ⟨{y | pb y ∧ dist (f y) (f x) < ε / 2}, hpb.and hc, ?_⟩
    filter_upwards [hpa] with n hn y hy
    have h2 : dist (F n y) (f x) < ε / 2 := hp hn hy.1
    have h3 := dist_triangle (f y) (f x) (F n y)
    have h4 := hy.2
    rw [dist_comm (f x) (F n y)] at h3
    linarith

/-- T42 C helper: locally uniform convergence is unchanged by eventual equality on `U`. -/
theorem s04_tc_evcongr {α β : Type*} [TopologicalSpace α] [PseudoMetricSpace β] {U : Set α}
    {F G : ℕ → α → β} {f g : α → β} (hF : TendstoLocallyUniformlyOn F f atTop U)
    (hFG : ∀ᶠ n in atTop, EqOn (F n) (G n) U) (hfg : EqOn f g U) :
    TendstoLocallyUniformlyOn G g atTop U := by
  rw [Metric.tendstoLocallyUniformlyOn_iff] at hF ⊢
  intro ε hε x hx
  obtain ⟨t, ht, hev⟩ := hF ε hε x hx
  refine ⟨t ∩ U, inter_mem ht self_mem_nhdsWithin, ?_⟩
  filter_upwards [hev, hFG] with n hn hn' y hy
  rw [← hfg hy.2, ← hn' hy.2]
  exact hn y hy.1

/-- T42 C helper: functions equal on an open set have equal iterated derivatives there. -/
theorem s04_tc_eqOn {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f g : E → F}
    (h : EqOn f g U) (i : ℕ) : EqOn (iteratedFDeriv ℝ i f) (iteratedFDeriv ℝ i g) U :=
  fun _ hy => ((Filter.eventuallyEq_of_mem (hU.mem_nhds hy) h).iteratedFDeriv ℝ i).eq_of_nhds

/-- T42 C helper: iterated derivatives of a smooth map are continuous on an open set. -/
theorem s04_tc_cont {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (i : ℕ) : ContinuousOn (iteratedFDeriv ℝ i f) U :=
  (hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hU.uniqueDiffOn).congr
    fun _ hy => (iteratedFDerivWithin_of_isOpen i hU hy).symm

/-- T42 C helper: a smooth map on an open set is `C^m` at each of its points. -/
theorem s04_tc_at {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) {y : E} (hy : y ∈ U) (m : ℕ) : ContDiffAt ℝ m f y :=
  (hf.contDiffAt (hU.mem_nhds hy)).of_le (by exact_mod_cast le_top)

/-- T42 C: a constant sequence of smooth maps converges in `C^∞_loc`. -/
theorem s04_tc_const {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞ ((fun _ : ℕ => f) n) U) ∧ ContDiffOn ℝ ∞ f U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i ((fun _ : ℕ => f) n))
        (iteratedFDeriv ℝ i f) atTop U := by
  refine ⟨Eventually.of_forall fun _ => hf, hf, fun i => ?_⟩
  exact Metric.tendstoLocallyUniformlyOn_iff.2 fun ε hε x _ =>
    ⟨univ, univ_mem, Eventually.of_forall fun n y _ => by simp [hε]⟩

/-- T42 C: `C^∞_loc` convergence only depends on the values on the open set. -/
theorem s04_tc_congr {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U)
    {f f' : ℕ → E → F} {fL fL' : E → F}
    (h : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f' n) U) ∧ ContDiffOn ℝ ∞ fL' U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (f' n))
        (iteratedFDeriv ℝ i fL') atTop U)
    (he : ∀ᶠ n in atTop, EqOn (f n) (f' n) U) (heL : EqOn fL fL' U) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) U) ∧ ContDiffOn ℝ ∞ fL U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (f n))
        (iteratedFDeriv ℝ i fL) atTop U := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨(h1.and he).mono fun n hn => hn.1.congr hn.2, h2.congr heL, fun i => ?_⟩
  exact s04_tc_evcongr (h3 i) (he.mono fun n hn => (s04_tc_eqOn hU hn i).symm)
    (s04_tc_eqOn hU heL i).symm

/-- T42 C: sums. -/
theorem s04_tc_add {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U)
    {f g : ℕ → E → F} {fL gL : E → F}
    (hf : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) U) ∧ ContDiffOn ℝ ∞ fL U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (f n))
        (iteratedFDeriv ℝ i fL) atTop U)
    (hg : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (g n) U) ∧ ContDiffOn ℝ ∞ gL U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (g n))
        (iteratedFDeriv ℝ i gL) atTop U) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fun x => f n x + g n x) U) ∧
      ContDiffOn ℝ ∞ (fun x => fL x + gL x) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (fun x => f n x + g n x))
        (iteratedFDeriv ℝ i (fun x => fL x + gL x)) atTop U := by
  obtain ⟨hf1, hf2, hf3⟩ := hf
  obtain ⟨hg1, hg2, hg3⟩ := hg
  refine ⟨(hf1.and hg1).mono fun n hn => hn.1.add hn.2, hf2.add hg2, fun i => ?_⟩
  have hT := uniformContinuous_add.comp_tendstoLocallyUniformlyOn ((hf3 i).prodMk (hg3 i))
  refine s04_tc_evcongr hT ((hf1.and hg1).mono fun n hn y hy => ?_) (fun y hy => ?_)
  · exact (iteratedFDeriv_add_apply (s04_tc_at hU hn.1 hy i) (s04_tc_at hU hn.2 hy i)).symm
  · exact (iteratedFDeriv_add_apply (s04_tc_at hU hf2 hy i) (s04_tc_at hU hg2 hy i)).symm

/-- T42 C helper: post-composition with a continuous linear map, at one order. -/
theorem s04_tc_clm_ord {E F G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {U : Set E} (hU : IsOpen U) (L : F →L[ℝ] G) {f : ℕ → E → F} {fL : E → F}
    (hf1 : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) U) (hf2 : ContDiffOn ℝ ∞ fL U) (i : ℕ)
    (hf3 : TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (f n))
      (iteratedFDeriv ℝ i fL) atTop U) :
    TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (fun x => L (f n x)))
      (iteratedFDeriv ℝ i (fun x => L (fL x))) atTop U := by
  have hT := (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin i => E) F G
    L).uniformContinuous.comp_tendstoLocallyUniformlyOn hf3
  refine s04_tc_evcongr hT (hf1.mono fun n hn y hy => ?_) (fun y hy => ?_)
  · exact (L.iteratedFDeriv_comp_left (s04_tc_at hU hn hy i) le_rfl).symm
  · exact (L.iteratedFDeriv_comp_left (s04_tc_at hU hf2 hy i) le_rfl).symm

/-- T42 C: post-composition with a continuous linear map. -/
theorem s04_tc_clm {E F G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {U : Set E} (hU : IsOpen U) (L : F →L[ℝ] G) {f : ℕ → E → F} {fL : E → F}
    (hf : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) U) ∧ ContDiffOn ℝ ∞ fL U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (f n))
        (iteratedFDeriv ℝ i fL) atTop U) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fun x => L (f n x)) U) ∧
      ContDiffOn ℝ ∞ (fun x => L (fL x)) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (fun x => L (f n x)))
        (iteratedFDeriv ℝ i (fun x => L (fL x))) atTop U := by
  obtain ⟨hf1, hf2, hf3⟩ := hf
  exact ⟨hf1.mono fun n hn => L.contDiff.comp_contDiffOn hn, L.contDiff.comp_contDiffOn hf2,
    fun i => s04_tc_clm_ord hU L hf1 hf2 i (hf3 i)⟩

/-- T42 C helper: order `0` convergence is convergence of the maps. -/
theorem s04_tc_zero {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} {f : ℕ → E → F} {fL : E → F}
    (h : TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ 0 (f n))
      (iteratedFDeriv ℝ 0 fL) atTop U) :
    TendstoLocallyUniformlyOn f fL atTop U := by
  have hT := (continuousMultilinearCurryFin0 ℝ E F).isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn h
  refine (hT.congr fun n y _ => ?_).congr_right fun y _ => ?_
  · simp [iteratedFDeriv_zero_eq_comp]
  · simp [iteratedFDeriv_zero_eq_comp]

/-- T42 C helper: Leibniz bound for a bilinear expression, global derivatives on an open set. -/
theorem s04_tc_bilin_bd {E F G H : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {U : Set E} (hU : IsOpen U)
    (B : F →L[ℝ] G →L[ℝ] H) {u : E → F} {v : E → G} (hu : ContDiffOn ℝ ∞ u U)
    (hv : ContDiffOn ℝ ∞ v U) {y : E} (hy : y ∈ U) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun x => B (u x) (v x)) y‖ ≤
      ‖B‖ * ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * ‖iteratedFDeriv ℝ k u y‖ *
        ‖iteratedFDeriv ℝ (i - k) v y‖ := by
  rw [← iteratedFDerivWithin_of_isOpen (f := fun x => B (u x) (v x)) i hU hy]
  refine (B.norm_iteratedFDerivWithin_le_of_bilinear hu hv hU.uniqueDiffOn hy
    (by exact_mod_cast le_top)).trans_eq ?_
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iteratedFDerivWithin_of_isOpen k hU hy, iteratedFDerivWithin_of_isOpen (i - k) hU hy]

/-- T42 C helper: the difference of two bilinear expressions, bounded by Leibniz. -/
theorem s04_tc_bilin_step {E F G H : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {U : Set E} (hU : IsOpen U)
    (B : F →L[ℝ] G →L[ℝ] H) {u uL : E → F} {v vL : E → G} (hu : ContDiffOn ℝ ∞ u U)
    (huL : ContDiffOn ℝ ∞ uL U) (hv : ContDiffOn ℝ ∞ v U) (hvL : ContDiffOn ℝ ∞ vL U)
    {y : E} (hy : y ∈ U) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun x => B (u x) (v x)) y -
        iteratedFDeriv ℝ i (fun x => B (uL x) (vL x)) y‖ ≤
      ‖B‖ * ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
          ‖iteratedFDeriv ℝ k u y - iteratedFDeriv ℝ k uL y‖ * ‖iteratedFDeriv ℝ (i - k) v y‖ +
        ‖B‖ * ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * ‖iteratedFDeriv ℝ k uL y‖ *
          ‖iteratedFDeriv ℝ (i - k) v y - iteratedFDeriv ℝ (i - k) vL y‖ := by
  have hdu : ContDiffOn ℝ ∞ (fun x => u x - uL x) U := hu.sub huL
  have hdv : ContDiffOn ℝ ∞ (fun x => v x - vL x) U := hv.sub hvL
  have h1 : ContDiffOn ℝ ∞ (fun x => B (u x - uL x) (v x)) U :=
    (B.contDiff.comp_contDiffOn hdu).clm_apply hv
  have h2 : ContDiffOn ℝ ∞ (fun x => B (uL x) (v x - vL x)) U :=
    (B.contDiff.comp_contDiffOn huL).clm_apply hdv
  have h3 : ContDiffOn ℝ ∞ (fun x => B (uL x) (vL x)) U :=
    (B.contDiff.comp_contDiffOn huL).clm_apply hvL
  have he : (fun x => B (u x) (v x)) =
      fun x => (B (u x - uL x) (v x) + B (uL x) (v x - vL x)) + B (uL x) (vL x) := by
    funext x
    simp only [map_sub, sub_apply]
    abel
  have hsplit : iteratedFDeriv ℝ i (fun x => B (u x) (v x)) y =
      (iteratedFDeriv ℝ i (fun x => B (u x - uL x) (v x)) y +
        iteratedFDeriv ℝ i (fun x => B (uL x) (v x - vL x)) y) +
        iteratedFDeriv ℝ i (fun x => B (uL x) (vL x)) y := by
    rw [he]
    exact (iteratedFDeriv_add_apply (s04_tc_at hU (h1.add h2) hy i) (s04_tc_at hU h3 hy i)).trans
      (congrArg (· + _) (iteratedFDeriv_add_apply (s04_tc_at hU h1 hy i) (s04_tc_at hU h2 hy i)))
  have hsu : ∀ k, iteratedFDeriv ℝ k (fun x => u x - uL x) y =
      iteratedFDeriv ℝ k u y - iteratedFDeriv ℝ k uL y := fun k =>
    iteratedFDeriv_sub_apply (s04_tc_at hU hu hy k) (s04_tc_at hU huL hy k)
  have hsv : ∀ k, iteratedFDeriv ℝ k (fun x => v x - vL x) y =
      iteratedFDeriv ℝ k v y - iteratedFDeriv ℝ k vL y := fun k =>
    iteratedFDeriv_sub_apply (s04_tc_at hU hv hy k) (s04_tc_at hU hvL hy k)
  have hb1 := s04_tc_bilin_bd hU B hdu hv hy i
  have hb2 := s04_tc_bilin_bd hU B huL hdv hy i
  simp only [hsu, hsv] at hb1 hb2
  rw [hsplit, add_sub_cancel_right]
  exact (norm_add_le _ _).trans (add_le_add hb1 hb2)

/-- T42 C helper: a continuous bilinear map applied to two convergent sequences, at one order
(only the orders `≤ i` of the factors are used). -/
theorem s04_tc_bilin_ord {E F G H : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {U : Set E} (hU : IsOpen U)
    (B : F →L[ℝ] G →L[ℝ] H) {f : ℕ → E → F} {fL : E → F} {g : ℕ → E → G} {gL : E → G}
    (hf1 : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) U) (hf2 : ContDiffOn ℝ ∞ fL U)
    (hg1 : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (g n) U) (hg2 : ContDiffOn ℝ ∞ gL U) (i : ℕ)
    (hf3 : ∀ k ≤ i, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ k (f n))
      (iteratedFDeriv ℝ k fL) atTop U)
    (hg3 : ∀ k ≤ i, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ k (g n))
      (iteratedFDeriv ℝ k gL) atTop U) :
    TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (fun x => B (f n x) (g n x)))
      (iteratedFDeriv ℝ i (fun x => B (fL x) (gL x))) atTop U := by
  have hBL : ContDiffOn ℝ ∞ (fun x => B (fL x) (gL x)) U :=
    (B.contDiff.comp_contDiffOn hf2).clm_apply hg2
  rw [s04_tc_cc (s04_tc_cont hU hBL i)]
  intro x hx
  have hcf : ∀ k ≤ i, Tendsto (fun q : ℕ × E => iteratedFDeriv ℝ k (f q.1) q.2)
      (atTop ×ˢ 𝓝[U] x) (𝓝 (iteratedFDeriv ℝ k fL x)) := fun k hk =>
    (s04_tc_cc (s04_tc_cont hU hf2 k)).1 (hf3 k hk) x hx
  have hcg : ∀ k ≤ i, Tendsto (fun q : ℕ × E => iteratedFDeriv ℝ k (g q.1) q.2)
      (atTop ×ˢ 𝓝[U] x) (𝓝 (iteratedFDeriv ℝ k gL x)) := fun k hk =>
    (s04_tc_cc (s04_tc_cont hU hg2 k)).1 (hg3 k hk) x hx
  have hlf : ∀ k, Tendsto (fun q : ℕ × E => iteratedFDeriv ℝ k fL q.2)
      (atTop ×ˢ 𝓝[U] x) (𝓝 (iteratedFDeriv ℝ k fL x)) := fun k =>
    ((s04_tc_cont hU hf2 k) x hx).tendsto.comp tendsto_snd
  have hlg : ∀ k, Tendsto (fun q : ℕ × E => iteratedFDeriv ℝ k gL q.2)
      (atTop ×ˢ 𝓝[U] x) (𝓝 (iteratedFDeriv ℝ k gL x)) := fun k =>
    ((s04_tc_cont hU hg2 k) x hx).tendsto.comp tendsto_snd
  have hlB : Tendsto (fun q : ℕ × E => iteratedFDeriv ℝ i (fun x => B (fL x) (gL x)) q.2)
      (atTop ×ˢ 𝓝[U] x) (𝓝 (iteratedFDeriv ℝ i (fun x => B (fL x) (gL x)) x)) :=
    ((s04_tc_cont hU hBL i) x hx).tendsto.comp tendsto_snd
  have hbd : Tendsto (fun q : ℕ × E =>
      ‖B‖ * ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
          ‖iteratedFDeriv ℝ k (f q.1) q.2 - iteratedFDeriv ℝ k fL q.2‖ *
          ‖iteratedFDeriv ℝ (i - k) (g q.1) q.2‖ +
        ‖B‖ * ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * ‖iteratedFDeriv ℝ k fL q.2‖ *
          ‖iteratedFDeriv ℝ (i - k) (g q.1) q.2 - iteratedFDeriv ℝ (i - k) gL q.2‖)
      (atTop ×ˢ 𝓝[U] x) (𝓝 0) := by
    have h := ((tendsto_finsetSum (Finset.range (i + 1)) fun k hk =>
        ((((hcf k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))).sub (hlf k)).norm.const_mul
          (i.choose k : ℝ)).mul (hcg (i - k) (Nat.sub_le i k)).norm)).const_mul ‖B‖).add
      ((tendsto_finsetSum (Finset.range (i + 1)) fun k _ =>
        ((((hlf k).norm.const_mul (i.choose k : ℝ))).mul
          ((hcg (i - k) (Nat.sub_le i k)).sub (hlg (i - k))).norm)).const_mul ‖B‖)
    simpa using h
  have hdiff : Tendsto (fun q : ℕ × E =>
      iteratedFDeriv ℝ i (fun x => B (f q.1 x) (g q.1 x)) q.2 -
        iteratedFDeriv ℝ i (fun x => B (fL x) (gL x)) q.2) (atTop ×ˢ 𝓝[U] x) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbd
    filter_upwards [(hf1.and hg1).prod_mk (eventually_mem_nhdsWithin (s := U) (a := x))]
      with q hq
    exact s04_tc_bilin_step hU B hq.1.1 hf2 hq.1.2 hg2 hq.2 i
  have h := hdiff.add hlB
  simp only [sub_add_cancel, zero_add] at h
  exact h

/-- T42 C: a continuous bilinear map applied to two convergent sequences (Leibniz bound
`ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear` on the differences). -/
theorem s04_tc_bilin {E F G H : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {U : Set E} (hU : IsOpen U)
    (B : F →L[ℝ] G →L[ℝ] H) {f : ℕ → E → F} {fL : E → F} {g : ℕ → E → G} {gL : E → G}
    (hf : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) U) ∧ ContDiffOn ℝ ∞ fL U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (f n))
        (iteratedFDeriv ℝ i fL) atTop U)
    (hg : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (g n) U) ∧ ContDiffOn ℝ ∞ gL U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (g n))
        (iteratedFDeriv ℝ i gL) atTop U) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fun x => B (f n x) (g n x)) U) ∧
      ContDiffOn ℝ ∞ (fun x => B (fL x) (gL x)) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ i (fun x => B (f n x) (g n x)))
        (iteratedFDeriv ℝ i (fun x => B (fL x) (gL x))) atTop U := by
  obtain ⟨hf1, hf2, hf3⟩ := hf
  obtain ⟨hg1, hg2, hg3⟩ := hg
  exact ⟨(hf1.and hg1).mono fun n hn => (B.contDiff.comp_contDiffOn hn.1).clm_apply hn.2,
    (B.contDiff.comp_contDiffOn hf2).clm_apply hg2,
    fun i => s04_tc_bilin_ord hU B hf1 hf2 hg1 hg2 i (fun k _ => hf3 k) (fun k _ => hg3 k)⟩

/-- T42 C: pairing. -/
theorem s04_tc_pair {E F G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {U : Set E} (hU : IsOpen U) {f : ℕ → E → F} {fL : E → F} {g : ℕ → E → G} {gL : E → G}
    (hf : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) U) ∧ ContDiffOn ℝ ∞ fL U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (f n))
        (iteratedFDeriv ℝ i fL) atTop U)
    (hg : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (g n) U) ∧ ContDiffOn ℝ ∞ gL U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (g n))
        (iteratedFDeriv ℝ i gL) atTop U) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fun x => (f n x, g n x)) U) ∧
      ContDiffOn ℝ ∞ (fun x => (fL x, gL x)) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (fun x => (f n x, g n x)))
        (iteratedFDeriv ℝ i (fun x => (fL x, gL x))) atTop U := by
  have h := s04_tc_add hU (s04_tc_clm hU (ContinuousLinearMap.inl ℝ F G) hf)
    (s04_tc_clm hU (ContinuousLinearMap.inr ℝ F G) hg)
  exact s04_tc_congr hU h (Eventually.of_forall fun n y _ => by simp) (fun y _ => by simp)

/-- T42 C: differentiation (`iteratedFDeriv (i+1) f` is `iteratedFDeriv i (fderiv f)` up to a
linear isometry). -/
theorem s04_tc_fderiv {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U)
    {f : ℕ → E → F} {fL : E → F}
    (hf : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) U) ∧ ContDiffOn ℝ ∞ fL U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (f n))
        (iteratedFDeriv ℝ i fL) atTop U) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fderiv ℝ (f n)) U) ∧ ContDiffOn ℝ ∞ (fderiv ℝ fL) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (fderiv ℝ (f n)))
        (iteratedFDeriv ℝ i (fderiv ℝ fL)) atTop U := by
  obtain ⟨hf1, hf2, hf3⟩ := hf
  refine ⟨hf1.mono fun n hn => hn.fderiv_of_isOpen hU (by simp),
    hf2.fderiv_of_isOpen hU (by simp), fun i => ?_⟩
  have hT := (continuousMultilinearCurryRightEquiv' ℝ i E F).isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn (hf3 (i + 1))
  refine (hT.congr fun n y _ => ?_).congr_right fun y _ => ?_
  · simp [iteratedFDeriv_succ_eq_comp_right]
  · simp [iteratedFDeriv_succ_eq_comp_right]

/-- T42 C helper: composition, both factors varying, orders `≤ i`, for every target space. -/
theorem s04_tc_comp_ord {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} {V : Set F} (hU : IsOpen U)
    (hV : IsOpen V) {Gn : ℕ → E → F} {Gl : E → F}
    (hG : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (Gn n) U) ∧ ContDiffOn ℝ ∞ Gl U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (Gn n))
        (iteratedFDeriv ℝ i Gl) atTop U)
    (hmaps : ∀ᶠ n in atTop, MapsTo (Gn n) U V) (hmapsL : MapsTo Gl U V) (i : ℕ) :
    ∀ (H : Type u) [NormedAddCommGroup H] [NormedSpace ℝ H] (Fn : ℕ → F → H) (Fl : F → H),
      ((∀ᶠ n in atTop, ContDiffOn ℝ ∞ (Fn n) V) ∧ ContDiffOn ℝ ∞ Fl V ∧
        ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (Fn n))
          (iteratedFDeriv ℝ i Fl) atTop V) →
      ∀ k ≤ i, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ k (fun x => Fn n (Gn n x)))
        (iteratedFDeriv ℝ k (fun x => Fl (Gl x))) atTop U := by
  induction i with
  | zero =>
    intro H _ _ Fn Fl hF k hk
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    have h0 : TendstoLocallyUniformlyOn (fun n x => Fn n (Gn n x)) (fun x => Fl (Gl x))
        atTop U := by
      refine (s04_tc_cc (f := fun x => Fl (Gl x))
        (hF.2.1.continuousOn.comp hG.2.1.continuousOn hmapsL)).2 fun x hx => ?_
      have hFc := (s04_tc_cc hF.2.1.continuousOn).1 (s04_tc_zero (hF.2.2 0)) (Gl x) (hmapsL hx)
      have hGc := (s04_tc_cc hG.2.1.continuousOn).1 (s04_tc_zero (hG.2.2 0)) x hx
      have hGV : Tendsto (fun q : ℕ × E => Gn q.1 q.2) (atTop ×ˢ 𝓝[U] x) (𝓝[V] (Gl x)) :=
        tendsto_nhdsWithin_iff.2 ⟨hGc,
          (hmaps.prod_mk (eventually_mem_nhdsWithin (s := U) (a := x))).mono
            fun q hq => hq.1 hq.2⟩
      exact hFc.comp (tendsto_fst.prodMk hGV)
    have hT := (continuousMultilinearCurryFin0 ℝ E H).symm.isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn h0
    refine (hT.congr fun n y _ => ?_).congr_right fun y _ => ?_
    · rw [iteratedFDeriv_zero_eq_comp]
    · rw [iteratedFDeriv_zero_eq_comp]
  | succ i ih =>
    intro H _ _ Fn Fl hF k hk
    rcases Nat.lt_or_ge k (i + 1) with hlt | hge
    · exact ih H Fn Fl hF k (Nat.lt_succ_iff.1 hlt)
    obtain rfl : k = i + 1 := le_antisymm hk hge
    have hDF := s04_tc_fderiv hV hF
    have hDG := s04_tc_fderiv hU hG
    have hih := ih (F →L[ℝ] H) (fun n => fderiv ℝ (Fn n)) (fderiv ℝ Fl) hDF
    have hev := (hF.1.and hG.1).and hmaps
    have hu1 : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fun x => fderiv ℝ (Fn n) (Gn n x)) U :=
      ((hDF.1.and hG.1).and hmaps).mono fun n hn => hn.1.1.comp hn.1.2 hn.2
    have hu2 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ Fl (Gl x)) U :=
      hDF.2.1.comp hG.2.1 hmapsL
    have hord := s04_tc_bilin_ord hU (ContinuousLinearMap.compL ℝ E F H) hu1 hu2 hDG.1 hDG.2.1 i
      hih (fun k _ => hDG.2.2 k)
    have hT := (continuousMultilinearCurryRightEquiv' ℝ i E H).symm.isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn hord
    have hEq : ∀ {Fa : F → H} {Ga : E → F}, ContDiffOn ℝ ∞ Fa V → ContDiffOn ℝ ∞ Ga U →
        MapsTo Ga U V → EqOn (fderiv ℝ (fun x => Fa (Ga x)))
          (fun z => ContinuousLinearMap.compL ℝ E F H (fderiv ℝ Fa (Ga z)) (fderiv ℝ Ga z)) U := by
      intro Fa Ga hFa hGa hm z hz
      show fderiv ℝ (Fa ∘ Ga) z = (fderiv ℝ Fa (Ga z)).comp (fderiv ℝ Ga z)
      exact fderiv_comp z ((s04_tc_at hV hFa (hm hz) 1).differentiableAt (by simp))
        ((s04_tc_at hU hGa hz 1).differentiableAt (by simp))
    refine s04_tc_evcongr hT (hev.mono fun n hn y hy => ?_) (fun y hy => ?_)
    · rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, Function.comp_apply]
      exact congrArg _ (s04_tc_eqOn hU (hEq hn.1.1 hn.1.2 hn.2) i hy).symm
    · rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, Function.comp_apply]
      exact congrArg _ (s04_tc_eqOn hU (hEq hF.2.1 hG.2.1 hmapsL) i hy).symm

/-- T42 C: composition, both factors varying (induction on the order:
`D(F_n ∘ G_n) = (DF_n ∘ G_n) ∘L DG_n`, then `s04_tc_bilin`, `s04_tc_fderiv`). -/
theorem s04_tc_comp {E F G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {Fn : ℕ → F → G} {Fl : F → G} {Gn : ℕ → E → F} {Gl : E → F}
    (hF : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (Fn n) V) ∧ ContDiffOn ℝ ∞ Fl V ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (Fn n))
        (iteratedFDeriv ℝ i Fl) atTop V)
    (hG : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (Gn n) U) ∧ ContDiffOn ℝ ∞ Gl U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (Gn n))
        (iteratedFDeriv ℝ i Gl) atTop U)
    (hmaps : ∀ᶠ n in atTop, MapsTo (Gn n) U V) (hmapsL : MapsTo Gl U V) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fun x => Fn n (Gn n x)) U) ∧
      ContDiffOn ℝ ∞ (fun x => Fl (Gl x)) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (fun x => Fn n (Gn n x)))
        (iteratedFDeriv ℝ i (fun x => Fl (Gl x))) atTop U := by
  exact ⟨((hF.1.and hG.1).and hmaps).mono fun n hn => hn.1.1.comp hn.1.2 hn.2,
    hF.2.1.comp hG.2.1 hmapsL,
    fun i => s04_tc_comp_ord hU hV hG hmaps hmapsL i G Fn Fl hF i le_rfl⟩

/-- T42 C helper: real iterated derivatives of locally uniformly convergent holomorphic maps,
one order at a time. -/
theorem s04_tc_holo_ord {U : Set ℂ} (hU : IsOpen U) (i : ℕ) :
    ∀ (f : ℕ → ℂ → ℂ) (fL : ℂ → ℂ), (∀ᶠ n in atTop, DifferentiableOn ℂ (f n) U) →
      TendstoLocallyUniformlyOn f fL atTop U →
      TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (f n)) (iteratedFDeriv ℝ i fL)
        atTop U := by
  induction i with
  | zero =>
    intro f fL _ hconv
    have hT := (continuousMultilinearCurryFin0 ℝ ℂ ℂ).symm.isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn hconv
    refine (hT.congr fun n y _ => ?_).congr_right fun y _ => ?_
    · rw [iteratedFDeriv_zero_eq_comp]
    · rw [iteratedFDeriv_zero_eq_comp]
  | succ i ih =>
    intro f fL hd hconv
    have hdL : DifferentiableOn ℂ fL U := hconv.differentiableOn hd hU
    have hD := ih (fun n => deriv (f n)) (deriv fL) (hd.mono fun n hn => hn.deriv hU)
      (hconv.deriv hd hU)
    have hfd : ∀ {h : ℂ → ℂ}, DifferentiableOn ℂ h U →
        EqOn (fderiv ℝ h) (fun z => ContinuousLinearMap.lsmul ℝ ℂ (deriv h z)) U := by
      intro h hh z hz
      have hd' : DifferentiableAt ℂ h z := hh.differentiableAt (hU.mem_nhds hz)
      refine ContinuousLinearMap.ext fun v => ?_
      rw [hd'.fderiv_restrictScalars ℝ]
      simp [fderiv_eq_smul_deriv, mul_comm]
    have hsm : ∀ {h : ℂ → ℂ}, DifferentiableOn ℂ h U → ContDiffOn ℝ ∞ (deriv h) U :=
      fun hh => ((hh.deriv hU).contDiffOn hU).restrict_scalars ℝ
    have hc := s04_tc_clm_ord hU (ContinuousLinearMap.lsmul (E := ℂ) ℝ ℂ) (hd.mono fun n hn => hsm hn)
      (hsm hdL) i hD
    have hT := (continuousMultilinearCurryRightEquiv' ℝ i ℂ ℂ).symm.isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn hc
    refine s04_tc_evcongr hT (hd.mono fun n hn y hy => ?_) (fun y hy => ?_)
    · rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, Function.comp_apply]
      exact congrArg _ (s04_tc_eqOn hU (hfd hn) i hy).symm
    · rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, Function.comp_apply]
      exact congrArg _ (s04_tc_eqOn hU (hfd hdL) i hy).symm

/-- T42 C: holomorphic maps converging locally uniformly converge in `C^∞_loc` (real
derivatives; Weierstrass + `iteratedFDeriv ℂ` restricted to `ℝ`). -/
theorem s04_tc_holo {U : Set ℂ} (hU : IsOpen U) {f : ℕ → ℂ → ℂ} {fL : ℂ → ℂ}
    (hd : ∀ᶠ n in atTop, DifferentiableOn ℂ (f n) U)
    (hconv : TendstoLocallyUniformlyOn f fL atTop U) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) U) ∧ ContDiffOn ℝ ∞ fL U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (f n))
        (iteratedFDeriv ℝ i fL) atTop U := by
  have hdL : DifferentiableOn ℂ fL U := hconv.differentiableOn hd hU
  exact ⟨hd.mono fun n hn => (hn.contDiffOn hU).restrict_scalars ℝ,
    (hdL.contDiffOn hU).restrict_scalars ℝ, fun i => s04_tc_holo_ord hU i f fL hd hconv⟩

/-- T42 C: order `0` on a compact subset. -/
theorem s04_tc_unif {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U)
    {f : ℕ → E → F} {fL : E → F}
    (hf : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) U) ∧ ContDiffOn ℝ ∞ fL U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (f n))
        (iteratedFDeriv ℝ i fL) atTop U)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) : TendstoUniformlyOn f fL atTop K := by
  have _h := hU
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1
    ((s04_tc_zero (hf.2.2 0)).mono hKU)

/-! ## N: naturality under real similarities `A z = c z + b`, `c > 0` -/

/-- T42 N helper: post-composition of a conformal map with a similarity. -/
theorem s04_tn_conf {f : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω) {a : ℂ}
    (ha : a ≠ 0) (b : ℂ) :
    IsConformalOnto (fun ζ => a * f ζ + b) unitDisc ((fun z => a * z + b) '' Ω) := by
  refine ⟨(hf.1.const_mul a).add_const b, fun x hx y hy hxy => hf.2.1 hx hy ?_, ?_⟩
  · have h : a * f x + b = a * f y + b := hxy
    exact mul_left_cancel₀ ha (add_right_cancel h)
  · rw [← hf.2.2, image_image]

/-- T42 N helper: the hyperbolic distance is invariant under a similarity. -/
theorem s04_tn_dist (Ω : Set ℂ) {a : ℂ} (ha : a ≠ 0) (b p w : ℂ) :
    poincareDist ((fun z => a * z + b) '' Ω) (a * p + b) (a * w + b) = poincareDist Ω p w := by
  have hinv : ∀ z : ℂ, a⁻¹ * (a * z + b) + -(a⁻¹ * b) = z := fun z => by
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ ha, one_mul, add_neg_cancel_right]
  have himg : (fun z => a⁻¹ * z + -(a⁻¹ * b)) '' ((fun z => a * z + b) '' Ω) = Ω := by
    rw [image_image]
    simp only [hinv, image_id']
  show sInf _ = sInf _
  congr 1
  ext d
  constructor
  · rintro ⟨g, x, z, hg, hx, hz, hgx, hgz, rfl⟩
    have h := s04_tn_conf hg (inv_ne_zero ha) (-(a⁻¹ * b))
    rw [himg] at h
    exact ⟨_, x, z, h, hx, hz, by simp only [hgx, hinv], by simp only [hgz, hinv], rfl⟩
  · rintro ⟨f, x, z, hf, hx, hz, hfx, hfz, rfl⟩
    exact ⟨_, x, z, s04_tn_conf hf ha b, hx, hz, by simp only [hfx], by simp only [hfz], rfl⟩

/-- T42 N helper: the image of an open set under a similarity is open. -/
theorem s04_tn_open {Ω : Set ℂ} (hΩ : IsOpen Ω) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsOpen ((fun z => a * z + b) '' Ω) := by
  have he : (fun z => a * z + b) '' Ω = (fun y => a⁻¹ * (y - b)) ⁻¹' Ω := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show a⁻¹ * (a * x + b - b) ∈ Ω
      rwa [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    · intro hy
      refine ⟨_, hy, ?_⟩
      show a * (a⁻¹ * (y - b)) + b = y
      rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul, sub_add_cancel]
  rw [he]
  exact hΩ.preimage (by fun_prop)

/-- T42 N: `A(B_ρ(w, r)) = B_{ρ'}(A w, r)` for `Ω' = A(Ω)`. -/
theorem s04_tn_ball {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {c : ℝ}
    (hc : 0 < c) (b : ℂ) {w : ℂ} (hw : w ∈ Ω) (r : ℝ) :
    rhoBall ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * w + b) r =
      (fun z => (c : ℂ) * z + b) '' rhoBall Ω w r := by
  have _h := hΩ
  have _h' := hw
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  ext w'
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hd⟩
    have hd' : poincareDist ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * w + b)
        ((c : ℂ) * y + b) < r := hd
    rw [s04_tn_dist Ω hc' b w y] at hd'
    exact ⟨y, ⟨hy, hd'⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hd⟩, rfl⟩
    refine ⟨mem_image_of_mem _ hy, ?_⟩
    show poincareDist ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * w + b)
        ((c : ℂ) * y + b) < r
    rw [s04_tn_dist Ω hc' b w y]
    exact hd

/-- T42 N helper: `D(g ∘ A⁻¹)(A x)(c v) = D g(x)(v)` (no differentiability needed). -/
theorem s04_tn_fd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {c : ℝ} (hc : 0 < c)
    (b : ℂ) (g : ℂ → F) (x v : ℂ) :
    fderiv ℝ (fun y => g ((c : ℂ)⁻¹ * (y - b))) ((c : ℂ) * x + b) ((c : ℂ) * v) =
      fderiv ℝ g x v := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  set e : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 (c⁻¹ : ℝ) (inv_ne_zero hc.ne'))
    with he
  have hev : ∀ y : ℂ, e y = (c : ℂ)⁻¹ * y := fun y => by
    simp [he, Units.smul_def, Complex.real_smul]
  have e1 : (fun y => g ((c : ℂ)⁻¹ * (y - b))) = (fun z => g (z + -((c : ℂ)⁻¹ * b))) ∘ e := by
    funext y
    show g ((c : ℂ)⁻¹ * (y - b)) = g (e y + -((c : ℂ)⁻¹ * b))
    rw [hev]
    congr 1
    ring
  have hx : (c : ℂ)⁻¹ * ((c : ℂ) * x + b) + -((c : ℂ)⁻¹ * b) = x := by
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hc', one_mul, add_neg_cancel_right]
  have hv : (c : ℂ)⁻¹ * ((c : ℂ) * v) = v := by
    rw [← mul_assoc, inv_mul_cancel₀ hc', one_mul]
  rw [e1, e.comp_right_fderiv, fderiv_comp_add_right, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, hev, hev, hx, hv]

/-- T42 N: `λ'(A w) c = λ(w)` and `∇φ'(A w) = ∇φ(w)/c`. -/
theorem s04_tn_lambda {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {c : ℝ}
    (hc : 0 < c) (b : ℂ) {w : ℂ} (hw : w ∈ Ω) :
    poincareDensity ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * w + b) * c =
        poincareDensity Ω w ∧
      logDensityGrad ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * w + b) =
        logDensityGrad Ω w / c := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hnc : ‖(c : ℂ)‖ = c := by rw [Complex.norm_real, Real.norm_of_nonneg hc.le]
  have hlam : ∀ x ∈ Ω, poincareDensity ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * x + b) *
      c = poincareDensity Ω x := fun x hx => by
    have h := (subsec_poincare_natural_affine hΩ (b := b) hc' hx).1
    rwa [hnc] at h
  refine ⟨hlam w hw, ?_⟩
  obtain ⟨f, hf⟩ := hΩ
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hAo := s04_tn_open hΩo hc' b
  have hev : (fun y => Real.log (poincareDensity ((fun z => (c : ℂ) * z + b) '' Ω) y)) =ᶠ[𝓝 ((c : ℂ) * w + b)]
      fun y => (fun x => Real.log (poincareDensity Ω x)) ((c : ℂ)⁻¹ * (y - b)) - Real.log c := by
    filter_upwards [hAo.mem_nhds (mem_image_of_mem _ hw)] with y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hpos := s02_poincareDensity_pos ⟨f, hf⟩ hx
    have hne : poincareDensity ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * x + b) ≠ 0 := by
      intro h0
      have h := hlam x hx
      rw [h0, zero_mul] at h
      linarith
    have h1 : (c : ℂ)⁻¹ * ((c : ℂ) * x + b - b) = x := by
      rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ hc', one_mul]
    show Real.log (poincareDensity ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * x + b)) =
      Real.log (poincareDensity Ω ((c : ℂ)⁻¹ * ((c : ℂ) * x + b - b))) - Real.log c
    rw [h1, ← hlam x hx, Real.log_mul hne hc.ne', add_sub_cancel_right]
  have hfd : ∀ v : ℂ, fderiv ℝ (fun y => Real.log (poincareDensity
      ((fun z => (c : ℂ) * z + b) '' Ω) y)) ((c : ℂ) * w + b) v =
        c⁻¹ * fderiv ℝ (fun x => Real.log (poincareDensity Ω x)) w v := by
    intro v
    rw [hev.fderiv_eq, fderiv_sub_const]
    have h := s04_tn_fd hc b (fun x => Real.log (poincareDensity Ω x)) w ((c⁻¹ : ℝ) • v)
    rw [show (c : ℂ) * ((c⁻¹ : ℝ) • v) = v by
      rw [Complex.real_smul, ← mul_assoc]; push_cast; rw [mul_inv_cancel₀ hc', one_mul],
      map_smul, smul_eq_mul] at h
    exact h
  simp only [logDensityGrad, hfd]
  rw [div_eq_mul_inv]
  push_cast
  ring

/-- T42 N helper: the Christoffel symbol under `A`, `Γ'_{Ax}(cX, cY) = c Γ_x(X, Y)`. -/
theorem s04_tn_christ {Ω Ω' : Set ℂ} {c : ℝ} (hc : 0 < c) {x x' : ℂ}
    (hg : logDensityGrad Ω' x' = logDensityGrad Ω x / c) (X Y : ℂ) :
    rhoChristoffel Ω' x' ((c : ℂ) * X) ((c : ℂ) * Y) = (c : ℂ) * rhoChristoffel Ω x X Y := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  simp only [rhoChristoffel, hg]
  have h1 : ∀ Z : ℂ, conj (logDensityGrad Ω x / (c : ℂ)) * ((c : ℂ) * Z) =
      conj (logDensityGrad Ω x) * Z := by
    intro Z
    rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, mul_left_comm,
      mul_div_cancel_left₀ _ hc']
  have h3 : conj ((c : ℂ) * X) * ((c : ℂ) * Y) = ((c ^ 2 : ℝ) : ℂ) * (conj X * Y) := by
    rw [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  rw [h1, h1, h3, Complex.re_ofReal_mul]
  push_cast
  field_simp

/-- T42 N helper: `Γ` is real-homogeneous in its first vector. -/
theorem s04_tn_christ_l (Ω : Set ℂ) (w X Y : ℂ) (a : ℝ) :
    rhoChristoffel Ω w ((a : ℂ) * X) Y = (a : ℂ) * rhoChristoffel Ω w X Y := by
  simp only [rhoChristoffel]
  rw [show conj (logDensityGrad Ω w) * ((a : ℂ) * X) =
      (a : ℂ) * (conj (logDensityGrad Ω w) * X) by ring,
    show conj ((a : ℂ) * X) * Y = (a : ℂ) * (conj X * Y) by
      rw [map_mul, Complex.conj_ofReal]; ring,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  push_cast
  ring

/-- T42 N helper: `Γ` is real-homogeneous in its second vector. -/
theorem s04_tn_christ_r (Ω : Set ℂ) (w X Y : ℂ) (a : ℝ) :
    rhoChristoffel Ω w X ((a : ℂ) * Y) = (a : ℂ) * rhoChristoffel Ω w X Y := by
  simp only [rhoChristoffel]
  rw [show conj (logDensityGrad Ω w) * ((a : ℂ) * Y) =
      (a : ℂ) * (conj (logDensityGrad Ω w) * Y) by ring,
    show conj X * ((a : ℂ) * Y) = (a : ℂ) * (conj X * Y) by ring,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  push_cast
  ring

/-- T42 N: `∇` commutes with the push-forward by `A` (no homogeneity needed:
`Γ'_{Ax}(cX, cY) = c Γ_x(X, Y)`). -/
theorem s04_tn_cov {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω) {c : ℝ} (hc : 0 < c) {b : ℂ} {k : ℕ}
    {T T' : TensorField k}
    (hrel : ∀ x ∈ Ω, ∀ u : Fin k → ℂ, T' ((c : ℂ) * x + b) (fun i => (c : ℂ) * u i) = T x u)
    (hgrad : ∀ x ∈ Ω, logDensityGrad Ω' ((c : ℂ) * x + b) = logDensityGrad Ω x / c) :
    ∀ x ∈ Ω, ∀ v : Fin (k + 1) → ℂ,
      rhoCovDeriv Ω' T' ((c : ℂ) * x + b) (fun i => (c : ℂ) * v i) = rhoCovDeriv Ω T x v := by
  intro x hx v
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hAo := s04_tn_open hΩ hc' b
  have h1 : fderiv ℝ (fun y => T' y (fun i => (c : ℂ) * Fin.tail v i)) ((c : ℂ) * x + b)
      ((c : ℂ) * v 0) = fderiv ℝ (fun y => T y (Fin.tail v)) x (v 0) := by
    have hev : (fun y => T' y (fun i => (c : ℂ) * Fin.tail v i)) =ᶠ[𝓝 ((c : ℂ) * x + b)]
        fun y => (fun x => T x (Fin.tail v)) ((c : ℂ)⁻¹ * (y - b)) := by
      filter_upwards [hAo.mem_nhds (mem_image_of_mem _ hx)] with y hy
      obtain ⟨x', hx', rfl⟩ := hy
      have h1 : (c : ℂ)⁻¹ * ((c : ℂ) * x' + b - b) = x' := by
        rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ hc', one_mul]
      show T' ((c : ℂ) * x' + b) (fun i => (c : ℂ) * Fin.tail v i) =
        T ((c : ℂ)⁻¹ * ((c : ℂ) * x' + b - b)) (Fin.tail v)
      rw [h1]
      exact hrel x' hx' (Fin.tail v)
    rw [hev.fderiv_eq]
    exact s04_tn_fd hc b (fun x => T x (Fin.tail v)) x (v 0)
  have h2 : ∀ i : Fin k, T' ((c : ℂ) * x + b) (Function.update (fun i => (c : ℂ) * Fin.tail v i) i
      (rhoChristoffel Ω' ((c : ℂ) * x + b) ((c : ℂ) * v 0) ((c : ℂ) * Fin.tail v i))) =
      T x (Function.update (Fin.tail v) i (rhoChristoffel Ω x (v 0) (Fin.tail v i))) := by
    intro i
    have hupd : Function.update (fun i => (c : ℂ) * Fin.tail v i) i
        (rhoChristoffel Ω' ((c : ℂ) * x + b) ((c : ℂ) * v 0) ((c : ℂ) * Fin.tail v i)) =
        fun j => (c : ℂ) *
          Function.update (Fin.tail v) i (rhoChristoffel Ω x (v 0) (Fin.tail v i)) j := by
      rw [s04_tn_christ hc (hgrad x hx) (v 0) (Fin.tail v i)]
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Function.update_of_ne hj]
    rw [hupd]
    exact hrel x hx _
  have key : rhoCovDeriv Ω' T' ((c : ℂ) * x + b) (fun i => (c : ℂ) * v i) =
      fderiv ℝ (fun y => T' y (fun i => (c : ℂ) * Fin.tail v i)) ((c : ℂ) * x + b)
        ((c : ℂ) * v 0) -
      ∑ i : Fin k, T' ((c : ℂ) * x + b) (Function.update (fun i => (c : ℂ) * Fin.tail v i) i
        (rhoChristoffel Ω' ((c : ℂ) * x + b) ((c : ℂ) * v 0) ((c : ℂ) * Fin.tail v i))) := rfl
  rw [key, h1, Finset.sum_congr rfl fun i _ => h2 i]
  rfl

/-- T42 N: `∇^j` commutes with the push-forward by `A`. -/
theorem s04_tn_iter {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω) {c : ℝ} (hc : 0 < c) {b : ℂ} {k : ℕ}
    {T T' : TensorField k}
    (hrel : ∀ x ∈ Ω, ∀ u : Fin k → ℂ, T' ((c : ℂ) * x + b) (fun i => (c : ℂ) * u i) = T x u)
    (hgrad : ∀ x ∈ Ω, logDensityGrad Ω' ((c : ℂ) * x + b) = logDensityGrad Ω x / c) (j : ℕ) :
    ∀ x ∈ Ω, ∀ v : Fin (k + j) → ℂ,
      rhoIterCovDeriv Ω' j T' ((c : ℂ) * x + b) (fun i => (c : ℂ) * v i) =
        rhoIterCovDeriv Ω j T x v := by
  induction j generalizing k T T' with
  | zero => exact hrel
  | succ j ih =>
    intro x hx v
    exact ih (s04_tn_cov hΩ hc hrel hgrad) x hx (v ∘ Fin.cast (by omega))

/-- T42 N helper: `fderiv` of a constant multiple, without differentiability. -/
theorem s04_tn_fdmul (h : ℂ → ℝ) (a : ℝ) (x v : ℂ) :
    fderiv ℝ (fun y => a * h y) x v = a * fderiv ℝ h x v := by
  have h1 := fderivWithin_const_smul_field (𝕜 := ℝ) (f := h) (s := univ) (x := x) a
    uniqueDiffWithinAt_univ
  rw [fderivWithin_univ, fderivWithin_univ] at h1
  have e : (fun y => a * h y) = a • h := by
    funext y
    simp [smul_eq_mul]
  rw [e, h1]
  rfl

/-- T42 N helper: `∇` preserves real homogeneity in each slot. -/
theorem s04_tn_cov_hom (Ω : Set ℂ) {k : ℕ} {T : TensorField k}
    (hT : ∀ (x : ℂ) (u : Fin k → ℂ) (i : Fin k) (a : ℝ),
      T x (Function.update u i ((a : ℂ) * u i)) = a * T x u)
    (x : ℂ) (v : Fin (k + 1) → ℂ) (i : Fin (k + 1)) (a : ℝ) :
    rhoCovDeriv Ω T x (Function.update v i ((a : ℂ) * v i)) = a * rhoCovDeriv Ω T x v := by
  refine Fin.cases ?_ (fun j => ?_) i
  · show fderiv ℝ (fun y => T y (Fin.tail (Function.update v 0 ((a : ℂ) * v 0)))) x
        (Function.update v 0 ((a : ℂ) * v 0) 0) -
      ∑ m : Fin k, T x (Function.update (Fin.tail (Function.update v 0 ((a : ℂ) * v 0))) m
        (rhoChristoffel Ω x (Function.update v 0 ((a : ℂ) * v 0) 0)
          (Fin.tail (Function.update v 0 ((a : ℂ) * v 0)) m))) =
      a * (fderiv ℝ (fun y => T y (Fin.tail v)) x (v 0) -
        ∑ m : Fin k, T x (Function.update (Fin.tail v) m
          (rhoChristoffel Ω x (v 0) (Fin.tail v m))))
    rw [Fin.tail_update_zero, Function.update_self]
    have hfd : fderiv ℝ (fun y => T y (Fin.tail v)) x ((a : ℂ) * v 0) =
        a * fderiv ℝ (fun y => T y (Fin.tail v)) x (v 0) := by
      rw [show (a : ℂ) * v 0 = a • v 0 from (Complex.real_smul).symm, map_smul, smul_eq_mul]
    have hs : ∀ m : Fin k, T x (Function.update (Fin.tail v) m
        (rhoChristoffel Ω x ((a : ℂ) * v 0) (Fin.tail v m))) =
        a * T x (Function.update (Fin.tail v) m (rhoChristoffel Ω x (v 0) (Fin.tail v m))) := by
      intro m
      rw [s04_tn_christ_l, ← hT x _ m a, Function.update_idem, Function.update_self]
    rw [hfd, Finset.sum_congr rfl fun m _ => hs m, ← Finset.mul_sum, mul_sub]
  · have h0 : Function.update v j.succ ((a : ℂ) * v j.succ) 0 = v 0 :=
      Function.update_of_ne (Fin.succ_ne_zero j).symm _ _
    show fderiv ℝ (fun y => T y (Fin.tail (Function.update v j.succ ((a : ℂ) * v j.succ)))) x
        (Function.update v j.succ ((a : ℂ) * v j.succ) 0) -
      ∑ m : Fin k, T x (Function.update (Fin.tail (Function.update v j.succ ((a : ℂ) * v j.succ)))
        m (rhoChristoffel Ω x (Function.update v j.succ ((a : ℂ) * v j.succ) 0)
          (Fin.tail (Function.update v j.succ ((a : ℂ) * v j.succ)) m))) =
      a * (fderiv ℝ (fun y => T y (Fin.tail v)) x (v 0) -
        ∑ m : Fin k, T x (Function.update (Fin.tail v) m
          (rhoChristoffel Ω x (v 0) (Fin.tail v m))))
    rw [Fin.tail_update_succ, h0]
    have ht : v j.succ = Fin.tail v j := rfl
    have hfd : fderiv ℝ (fun y => T y (Function.update (Fin.tail v) j ((a : ℂ) * Fin.tail v j)))
        x (v 0) = a * fderiv ℝ (fun y => T y (Fin.tail v)) x (v 0) := by
      have e : (fun y => T y (Function.update (Fin.tail v) j ((a : ℂ) * Fin.tail v j))) =
          fun y => a * T y (Fin.tail v) := funext fun y => hT y _ j a
      rw [e, s04_tn_fdmul]
    have hs : ∀ m : Fin k, T x (Function.update
        (Function.update (Fin.tail v) j ((a : ℂ) * Fin.tail v j)) m
        (rhoChristoffel Ω x (v 0)
          (Function.update (Fin.tail v) j ((a : ℂ) * Fin.tail v j) m))) =
        a * T x (Function.update (Fin.tail v) m (rhoChristoffel Ω x (v 0) (Fin.tail v m))) := by
      intro m
      by_cases hm : m = j
      · subst hm
        rw [Function.update_self, Function.update_idem, s04_tn_christ_r, ← hT x _ m a,
          Function.update_idem, Function.update_self]
      · rw [Function.update_of_ne hm, Function.update_comm (Ne.symm hm), ← hT x _ j a,
          Function.update_of_ne (Ne.symm hm)]
    rw [ht, hfd, Finset.sum_congr rfl fun m _ => hs m, ← Finset.mul_sum, mul_sub]

/-- T42 N: `∇^j` preserves real homogeneity in each slot. -/
theorem s04_tn_hom (Ω : Set ℂ) {k : ℕ} {T : TensorField k}
    (hT : ∀ (x : ℂ) (u : Fin k → ℂ) (i : Fin k) (a : ℝ),
      T x (Function.update u i ((a : ℂ) * u i)) = a * T x u)
    (j : ℕ) (x : ℂ) (u : Fin (k + j) → ℂ) (i : Fin (k + j)) (a : ℝ) :
    rhoIterCovDeriv Ω j T x (Function.update u i ((a : ℂ) * u i)) =
      a * rhoIterCovDeriv Ω j T x u := by
  revert x u i a
  induction j generalizing k T with
  | zero => exact hT
  | succ j ih =>
    intro x u i a
    have hc : k + 1 + j = k + (j + 1) := by omega
    have hcomp : Function.update u i ((a : ℂ) * u i) ∘ Fin.cast hc =
        Function.update (u ∘ Fin.cast hc) (Fin.cast hc.symm i)
          ((a : ℂ) * (u ∘ Fin.cast hc) (Fin.cast hc.symm i)) := by
      rw [← Function.update_comp_eq_of_injective _ (Fin.cast_injective hc)]
      rfl
    show rhoIterCovDeriv Ω j (rhoCovDeriv Ω T) x (Function.update u i ((a : ℂ) * u i) ∘
        Fin.cast hc) = a * rhoIterCovDeriv Ω j (rhoCovDeriv Ω T) x (u ∘ Fin.cast hc)
    rw [hcomp]
    exact ih (s04_tn_cov_hom Ω hT) x _ _ a

/-- T42 N helper: slot-wise homogeneity at `x` gives `T x (a u) = a ^ k T x u`. -/
theorem s04_tn_allslot {k : ℕ} {T : TensorField k} {x : ℂ}
    (hhom : ∀ (u : Fin k → ℂ) (i : Fin k) (a : ℝ),
      T x (Function.update u i ((a : ℂ) * u i)) = a * T x u) (a : ℝ) (u : Fin k → ℂ) :
    T x (fun i => (a : ℂ) * u i) = a ^ k * T x u := by
  have key : ∀ s : Finset (Fin k),
      T x (fun i => if i ∈ s then (a : ℂ) * u i else u i) = a ^ s.card * T x u := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert m s hm ih =>
      have e : (fun i => if i ∈ insert m s then (a : ℂ) * u i else u i) =
          Function.update (fun i => if i ∈ s then (a : ℂ) * u i else u i) m
            ((a : ℂ) * (fun i => if i ∈ s then (a : ℂ) * u i else u i) m) := by
        funext i
        by_cases hi : i = m
        · subst hi
          simp [hm]
        · simp [hi]
      rw [e, hhom, ih, Finset.card_insert_of_notMem hm, pow_succ]
      ring
  have := key Finset.univ
  simpa using this

/-- T42 N: the pointwise `ρ`-norm is invariant under the push-forward by `A`. -/
theorem s04_tn_norm {Ω Ω' : Set ℂ} {c : ℝ} (hc : 0 < c) {b : ℂ} {k : ℕ} {T T' : TensorField k}
    {x : ℂ} (hrel : ∀ u : Fin k → ℂ, T' ((c : ℂ) * x + b) (fun i => (c : ℂ) * u i) = T x u)
    (hhom : ∀ (u : Fin k → ℂ) (i : Fin k) (a : ℝ),
      T x (Function.update u i ((a : ℂ) * u i)) = a * T x u)
    (hlam_ : poincareDensity Ω' ((c : ℂ) * x + b) * c = poincareDensity Ω x) :
    rhoTensorNorm Ω' T' ((c : ℂ) * x + b) = rhoTensorNorm Ω T x := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hsc : ∀ u : Fin k → ℂ, T' ((c : ℂ) * x + b) u = (c⁻¹) ^ k * T x u := by
    intro u
    have e : u = fun i => (c : ℂ) * (((c⁻¹ : ℝ) : ℂ) * u i) := by
      funext i
      rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hc', one_mul]
    rw [congrArg (T' ((c : ℂ) * x + b)) e, hrel, s04_tn_allslot hhom]
  have hl : poincareDensity Ω' ((c : ℂ) * x + b) = poincareDensity Ω x / c :=
    eq_div_of_mul_eq hc.ne' hlam_
  show Real.sqrt (∑ idx : Fin k → Fin 2, (T' ((c : ℂ) * x + b) fun i => frameVec (idx i)) ^ 2) /
      poincareDensity Ω' ((c : ℂ) * x + b) ^ k =
    Real.sqrt (∑ idx : Fin k → Fin 2, (T x fun i => frameVec (idx i)) ^ 2) /
      poincareDensity Ω x ^ k
  simp only [hsc, hl, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), div_pow,
    inv_pow]
  have hck : c ^ k ≠ 0 := pow_ne_zero _ hc.ne'
  rw [div_div_eq_mul_div, mul_comm _ (c ^ k), ← mul_assoc, mul_inv_cancel₀ hck, one_mul]

/-- T42 N: `‖T'‖_{C^j(A E)} = ‖T‖_{C^j(E)}` (from `s04_tn_iter`, `s04_tn_hom`,
`s04_tn_norm`). -/
theorem s04_tn_cj {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω) {c : ℝ} (hc : 0 < c) {b : ℂ} {k : ℕ}
    {T T' : TensorField k}
    (hrel : ∀ x ∈ Ω, ∀ u : Fin k → ℂ, T' ((c : ℂ) * x + b) (fun i => (c : ℂ) * u i) = T x u)
    (hgrad : ∀ x ∈ Ω, logDensityGrad Ω' ((c : ℂ) * x + b) = logDensityGrad Ω x / c)
    (hlam_ : ∀ x ∈ Ω, poincareDensity Ω' ((c : ℂ) * x + b) * c = poincareDensity Ω x)
    (hhom : ∀ (x : ℂ) (u : Fin k → ℂ) (i : Fin k) (a : ℝ),
      T x (Function.update u i ((a : ℂ) * u i)) = a * T x u)
    (j : ℕ) {E : Set ℂ} (hE : E ⊆ Ω) :
    rhoCjNorm Ω' j T' ((fun z => (c : ℂ) * z + b) '' E) = rhoCjNorm Ω j T E := by
  show (⨆ (i : ℕ) (_ : i ≤ j) (w : ℂ) (_ : w ∈ (fun z => (c : ℂ) * z + b) '' E),
      ENNReal.ofReal (rhoTensorNorm Ω' (rhoIterCovDeriv Ω' i T') w)) =
    ⨆ (i : ℕ) (_ : i ≤ j) (w : ℂ) (_ : w ∈ E),
      ENNReal.ofReal (rhoTensorNorm Ω (rhoIterCovDeriv Ω i T) w)
  refine iSup_congr fun i => iSup_congr fun _ => ?_
  rw [iSup_image]
  refine iSup_congr fun x => iSup_congr fun hx => ?_
  rw [s04_tn_norm hc (s04_tn_iter hΩ hc hrel hgrad i x (hE hx)) (s04_tn_hom Ω hhom i x)
    (hlam_ x (hE hx))]

/-- T42 N helper: `hypInner` under `(W, ξ) ↦ (W', c ξ)` (the first coordinate is irrelevant). -/
theorem s04_tn_hypInner (p : ℂ) (c : ℝ) (q a b : ℂ × ℝ) :
    hypInner (p, c * q.2) a b = hypInner q a b / c ^ 2 := by
  show _ / (c * q.2) ^ 2 = _ / q.2 ^ 2 / c ^ 2
  rw [mul_pow, div_div, mul_comm (q.2 ^ 2)]

/-- T42 N helper: `hypInner` is real-homogeneous in its first vector. -/
theorem s04_tn_hypInner_l (q a b : ℂ × ℝ) (t : ℝ) :
    hypInner q (t • a) b = t * hypInner q a b := by
  show (((t • a).1 * conj b.1).re + (t • a).2 * b.2) / q.2 ^ 2 =
    t * (((a.1 * conj b.1).re + a.2 * b.2) / q.2 ^ 2)
  rw [Prod.smul_fst, Prod.smul_snd, Complex.real_smul, smul_eq_mul, mul_assoc,
    Complex.re_ofReal_mul]
  ring

/-- T42 N helper: `hypInner` is real-homogeneous in its second vector. -/
theorem s04_tn_hypInner_r (q a b : ℂ × ℝ) (t : ℝ) :
    hypInner q a (t • b) = t * hypInner q a b := by
  show ((a.1 * conj (t • b).1).re + a.2 * (t • b).2) / q.2 ^ 2 =
    t * (((a.1 * conj b.1).re + a.2 * b.2) / q.2 ^ 2)
  rw [Prod.smul_fst, Prod.smul_snd, Complex.real_smul, smul_eq_mul, map_mul,
    Complex.conj_ofReal, mul_left_comm, Complex.re_ofReal_mul]
  ring

/-- T42 N helper: `cvec (a v) = a • cvec v`. -/
theorem s04_tn_cvec (a : ℝ) (v : ℂ) : cvec ((a : ℂ) * v) = a • cvec v := by
  funext i
  fin_cases i <;> simp [cvec]

/-- T42 N helper: `dX'(A x) = dX(x)` for the Epstein–Poincaré map of `Ω' = A Ω`. -/
theorem s04_tn_dX {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {c : ℝ}
    (hc : 0 < c) (b : ℂ) {x : ℂ} (hx : x ∈ Ω) (v : ℂ) :
    fderiv ℝ (epstein ((fun z => (c : ℂ) * z + b) '' Ω)) ((c : ℂ) * x + b) v =
      fderiv ℝ (epstein Ω) x v := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hnc : ‖(c : ℂ)‖ = c := by rw [Complex.norm_real, Real.norm_of_nonneg hc.le]
  obtain ⟨f, hf⟩ := hΩ
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hAo := s04_tn_open hΩo hc' b
  have hev : epstein ((fun z => (c : ℂ) * z + b) '' Ω) =ᶠ[𝓝 ((c : ℂ) * x + b)]
      fun y => (fun z => c • epstein Ω z + ((b : ℂ), (0 : ℝ))) ((c : ℂ)⁻¹ * (y - b)) := by
    filter_upwards [hAo.mem_nhds (mem_image_of_mem _ hx)] with y hy
    obtain ⟨x', hx', rfl⟩ := hy
    have h1 : (c : ℂ)⁻¹ * ((c : ℂ) * x' + b - b) = x' := by
      rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ hc', one_mul]
    show epstein ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * x' + b) =
      c • epstein Ω ((c : ℂ)⁻¹ * ((c : ℂ) * x' + b - b)) + ((b : ℂ), (0 : ℝ))
    rw [h1, subsec_epstein_natural_affine ⟨f, hf⟩ hc' hx', hnc]
    ext
    · simp [Complex.real_smul]
    · simp
  rw [hev.fderiv_eq]
  have h := s04_tn_fd hc b (fun z => c • epstein Ω z + ((b : ℂ), (0 : ℝ))) x ((c : ℂ)⁻¹ * v)
  rw [mul_inv_cancel_left₀ hc'] at h
  rw [h, fderiv_add_const]
  have h1 := fderivWithin_const_smul_field (𝕜 := ℝ) (f := epstein Ω) (s := univ) (x := x) c
    uniqueDiffWithinAt_univ
  rw [fderivWithin_univ, fderivWithin_univ] at h1
  have h2 : fderiv ℝ (fun z => c • epstein Ω z) x = c • fderiv ℝ (epstein Ω) x := h1
  rw [h2, smul_apply,
    show (c : ℂ)⁻¹ * v = (c⁻¹ : ℝ) • v by rw [Complex.real_smul, Complex.ofReal_inv],
    map_smul, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

/-- T42 N helper: `I'(A x) = I(x) / c²` on `Ω' = A Ω`. -/
theorem s04_tn_fff {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {c : ℝ}
    (hc : 0 < c) (b : ℂ) {x : ℂ} (hx : x ∈ Ω) (u : Fin 2 → ℂ) :
    fffT ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * x + b) u = fffT Ω x u / c ^ 2 := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hnc : ‖(c : ℂ)‖ = c := by rw [Complex.norm_real, Real.norm_of_nonneg hc.le]
  show hypInner (epstein ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * x + b))
      (fderiv ℝ (epstein ((fun z => (c : ℂ) * z + b) '' Ω)) ((c : ℂ) * x + b) (u 0))
      (fderiv ℝ (epstein ((fun z => (c : ℂ) * z + b) '' Ω)) ((c : ℂ) * x + b) (u 1)) =
    hypInner (epstein Ω x) (fderiv ℝ (epstein Ω) x (u 0)) (fderiv ℝ (epstein Ω) x (u 1)) / c ^ 2
  rw [s04_tn_dX hΩ hc b hx, s04_tn_dX hΩ hc b hx, subsec_epstein_natural_affine hΩ hc' hx, hnc]
  exact s04_tn_hypInner _ _ _ _ _

/-- T42 N helper: `ρ'(A x) = ρ(x) / c²` on `Ω' = A Ω`. -/
theorem s04_tn_rho {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {c : ℝ}
    (hc : 0 < c) (b : ℂ) {x : ℂ} (hx : x ∈ Ω) (u : Fin 2 → ℂ) :
    rhoMetricT ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * x + b) u =
      rhoMetricT Ω x u / c ^ 2 := by
  show poincareDensity ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * x + b) ^ 2 *
      (conj (u 0) * u 1).re = poincareDensity Ω x ^ 2 * (conj (u 0) * u 1).re / c ^ 2
  rw [eq_div_of_mul_eq hc.ne' (s04_tn_lambda hΩ hc b hx).1]
  ring

/-- T42 N helper: `I` is real-homogeneous in each slot. -/
theorem s04_tn_fff_hom (Ω : Set ℂ) (x : ℂ) (u : Fin 2 → ℂ) (i : Fin 2) (a : ℝ) :
    fffT Ω x (Function.update u i ((a : ℂ) * u i)) = a * fffT Ω x u := by
  have hd : ∀ v : ℂ, fderiv ℝ (epstein Ω) x ((a : ℂ) * v) = a • fderiv ℝ (epstein Ω) x v :=
    fun v => by rw [← Complex.real_smul, map_smul]
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · show hypInner (epstein Ω x)
        (fderiv ℝ (epstein Ω) x (Function.update u 0 ((a : ℂ) * u 0) 0))
        (fderiv ℝ (epstein Ω) x (Function.update u 0 ((a : ℂ) * u 0) 1)) =
      a * hypInner (epstein Ω x) (fderiv ℝ (epstein Ω) x (u 0)) (fderiv ℝ (epstein Ω) x (u 1))
    rw [Function.update_self, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), hd,
      s04_tn_hypInner_l]
  · show hypInner (epstein Ω x)
        (fderiv ℝ (epstein Ω) x (Function.update u 1 ((a : ℂ) * u 1) 0))
        (fderiv ℝ (epstein Ω) x (Function.update u 1 ((a : ℂ) * u 1) 1)) =
      a * hypInner (epstein Ω x) (fderiv ℝ (epstein Ω) x (u 0)) (fderiv ℝ (epstein Ω) x (u 1))
    rw [Function.update_self, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1), hd,
      s04_tn_hypInner_r]

/-- T42 N helper: `ρ` is real-homogeneous in each slot. -/
theorem s04_tn_rho_hom (Ω : Set ℂ) (x : ℂ) (u : Fin 2 → ℂ) (i : Fin 2) (a : ℝ) :
    rhoMetricT Ω x (Function.update u i ((a : ℂ) * u i)) = a * rhoMetricT Ω x u := by
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · show poincareDensity Ω x ^ 2 * (conj (Function.update u 0 ((a : ℂ) * u 0) 0) *
        Function.update u 0 ((a : ℂ) * u 0) 1).re = a * (poincareDensity Ω x ^ 2 *
        (conj (u 0) * u 1).re)
    rw [Function.update_self, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), map_mul,
      Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
    ring
  · show poincareDensity Ω x ^ 2 * (conj (Function.update u 1 ((a : ℂ) * u 1) 0) *
        Function.update u 1 ((a : ℂ) * u 1) 1).re = a * (poincareDensity Ω x ^ 2 *
        (conj (u 0) * u 1).re)
    rw [Function.update_self, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
      mul_left_comm, Complex.re_ofReal_mul]
    ring

/-- T42 N helper: `ρ(B·,·)` is real-homogeneous in each slot. -/
theorem s04_tn_shape_hom (Ω : Set ℂ) (x : ℂ) (u : Fin 2 → ℂ) (i : Fin 2) (a : ℝ) :
    shapeT Ω x (Function.update u i ((a : ℂ) * u i)) = a * shapeT Ω x u := by
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · show poincareDensity Ω x ^ 2 * ((shapeMat Ω x *ᵥ cvec (Function.update u 0 ((a : ℂ) * u 0) 0))
        ⬝ᵥ cvec (Function.update u 0 ((a : ℂ) * u 0) 1)) =
      a * (poincareDensity Ω x ^ 2 * ((shapeMat Ω x *ᵥ cvec (u 0)) ⬝ᵥ cvec (u 1)))
    rw [Function.update_self, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), s04_tn_cvec,
      Matrix.mulVec_smul, smul_dotProduct, smul_eq_mul]
    ring
  · show poincareDensity Ω x ^ 2 * ((shapeMat Ω x *ᵥ cvec (Function.update u 1 ((a : ℂ) * u 1) 0))
        ⬝ᵥ cvec (Function.update u 1 ((a : ℂ) * u 1) 1)) =
      a * (poincareDensity Ω x ^ 2 * ((shapeMat Ω x *ᵥ cvec (u 0)) ⬝ᵥ cvec (u 1)))
    rw [Function.update_self, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1), s04_tn_cvec,
      dotProduct_smul, smul_eq_mul]
    ring

/-- T42 N helper: `II = ((1 - s²) ρ - I)/2` (from `s02_curv_fI` and `s05_sa_secondFF`). -/
theorem s04_tn_II {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) (u v : ℂ) :
    secondFF Ω w u v = ((1 - schwarzNorm Ω w ^ 2) * poincareDensity Ω w ^ 2 * (u * conj v).re -
      fffT Ω w ![u, v]) / 2 := by
  have h3 : fffT Ω w ![u, v] =
      hypInner (epstein Ω w) (fderiv ℝ (epstein Ω) w u) (fderiv ℝ (epstein Ω) w v) := rfl
  rw [h3, s02_curv_fI hf hw u v, s05_sa_secondFF hf hw u v]
  ring

/-- T42 N helper: `II'(A x) = II(x) / c²` on `Ω' = A Ω`. -/
theorem s04_tn_sff {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {c : ℝ}
    (hc : 0 < c) (b : ℂ) {x : ℂ} (hx : x ∈ Ω) (u v : ℂ) :
    secondFF ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * x + b) u v =
      secondFF Ω x u v / c ^ 2 := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  obtain ⟨f, hf⟩ := hΩ
  have hf' := s04_tn_conf hf hc' b
  have hAx : (c : ℂ) * x + b ∈ (fun z => (c : ℂ) * z + b) '' Ω := mem_image_of_mem _ hx
  rw [s04_tn_II hf' hAx, s04_tn_II hf hx, s04_tn_fff ⟨f, hf⟩ hc b hx,
    (subsec_poincare_natural_affine ⟨f, hf⟩ (b := b) hc' hx).2,
    eq_div_of_mul_eq hc.ne' (s04_tn_lambda ⟨f, hf⟩ hc b hx).1]
  ring

/-- T42 N helper: `(k F)⁻¹ (k S)ᵀ = F⁻¹ Sᵀ` for `k ≠ 0` (also when `F` is singular). -/
theorem s04_tn_matscale (F S : Matrix (Fin 2) (Fin 2) ℝ) {k : ℝ} (hk : k ≠ 0) :
    (k • F)⁻¹ * (k • S)ᵀ = F⁻¹ * Sᵀ := by
  by_cases hF : IsUnit F.det
  · have := invertibleOfNonzero hk
    rw [Matrix.inv_smul F k hF, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      invOf_mul_self, one_smul]
  · have hF' : ¬ IsUnit (k • F).det := by
      rw [Matrix.det_smul]
      intro h
      exact hF (IsUnit.mul_iff.mp h).2
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hF, Matrix.nonsing_inv_apply_not_isUnit _ hF',
      Matrix.zero_mul, Matrix.zero_mul]

/-- T42 N helper: `B'(A x) = B(x)` (as matrices in the frame `(1, i)`). -/
theorem s04_tn_shapeMat {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {c : ℝ}
    (hc : 0 < c) (b : ℂ) {x : ℂ} (hx : x ∈ Ω) :
    shapeMat ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * x + b) = shapeMat Ω x := by
  have h1 : fffMat ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * x + b) =
      (c ^ 2)⁻¹ • fffMat Ω x := by
    ext i j
    show fffT ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * x + b) ![frameVec i, frameVec j] =
      (c ^ 2)⁻¹ * fffT Ω x ![frameVec i, frameVec j]
    rw [s04_tn_fff hΩ hc b hx, div_eq_inv_mul]
  have h2 : secondFFMat ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * x + b) =
      (c ^ 2)⁻¹ • secondFFMat Ω x := by
    ext i j
    show secondFF ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * x + b) (frameVec i) (frameVec j) =
      (c ^ 2)⁻¹ * secondFF Ω x (frameVec i) (frameVec j)
    rw [s04_tn_sff hΩ hc b hx, div_eq_inv_mul]
  show (fffMat ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * x + b))⁻¹ *
      (secondFFMat ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * x + b))ᵀ =
    (fffMat Ω x)⁻¹ * (secondFFMat Ω x)ᵀ
  rw [h1, h2, s04_tn_matscale _ _ (inv_ne_zero (pow_ne_zero 2 hc.ne'))]

/-- T42 N: `I - ρ` and `ρ(B·,·)` are natural under `A` and real-homogeneous in each slot
(from `s02_curv_fI` and `s05_sa_secondFF`; `S(ψ ∘ A⁻¹)(A x) = S ψ(x)/c²`). -/
theorem s04_tn_fields {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {c : ℝ}
    (hc : 0 < c) (b : ℂ) :
    (∀ x ∈ Ω, ∀ u : Fin 2 → ℂ,
      (fffT ((fun z => (c : ℂ) * z + b) '' Ω) - rhoMetricT ((fun z => (c : ℂ) * z + b) '' Ω))
          ((c : ℂ) * x + b) (fun i => (c : ℂ) * u i) = (fffT Ω - rhoMetricT Ω) x u) ∧
    (∀ x ∈ Ω, ∀ u : Fin 2 → ℂ,
      shapeT ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * x + b) (fun i => (c : ℂ) * u i) =
        shapeT Ω x u) ∧
    (∀ (x : ℂ) (u : Fin 2 → ℂ) (i : Fin 2) (a : ℝ),
      (fffT Ω - rhoMetricT Ω) x (Function.update u i ((a : ℂ) * u i)) =
        a * (fffT Ω - rhoMetricT Ω) x u) ∧
    (∀ (x : ℂ) (u : Fin 2 → ℂ) (i : Fin 2) (a : ℝ),
      shapeT Ω x (Function.update u i ((a : ℂ) * u i)) = a * shapeT Ω x u) := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc.ne'
  refine ⟨fun x hx u => ?_, fun x hx u => ?_, fun x u i a => ?_, s04_tn_shape_hom Ω⟩
  · simp only [Pi.sub_apply]
    rw [s04_tn_fff hΩ hc b hx, s04_tn_rho hΩ hc b hx, s04_tn_allslot (s04_tn_fff_hom Ω x) c u,
      s04_tn_allslot (s04_tn_rho_hom Ω x) c u]
    field_simp
  · show poincareDensity ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * x + b) ^ 2 *
        ((shapeMat ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * x + b) *ᵥ cvec ((c : ℂ) * u 0))
          ⬝ᵥ cvec ((c : ℂ) * u 1)) =
      poincareDensity Ω x ^ 2 * ((shapeMat Ω x *ᵥ cvec (u 0)) ⬝ᵥ cvec (u 1))
    rw [s04_tn_shapeMat hΩ hc b hx, s04_tn_cvec, s04_tn_cvec, Matrix.mulVec_smul,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      eq_div_of_mul_eq hc.ne' (s04_tn_lambda hΩ hc b hx).1]
    field_simp
  · simp only [Pi.sub_apply]
    rw [s04_tn_fff_hom, s04_tn_rho_hom, mul_sub]

/-! ## P: normalization and compactness -/

/-- T42 P helper: locally uniform convergence passes to `n ↦ g (m n)` for `m → ∞`. -/
theorem s04_tp_reidx {g : ℕ → ℂ → ℂ} {gL : ℂ → ℂ} {U : Set ℂ}
    (hconv : TendstoLocallyUniformlyOn g gL atTop U) {m : ℕ → ℕ} (hm : Tendsto m atTop atTop) :
    TendstoLocallyUniformlyOn (fun n => g (m n)) gL atTop U := by
  intro u hu x hx
  obtain ⟨t, ht, h⟩ := hconv u hu x hx
  exact ⟨t, ht, hm.eventually h⟩

/-- T42 P helper: `‖α‖ z + b/(α/‖α‖) = (α/‖α‖)⁻¹ (α z + b)` (removing the rotation). -/
theorem s04_tp_rot {α : ℂ} (hα : α ≠ 0) (b z : ℂ) :
    (‖α‖ : ℂ) * z + b / (α / (‖α‖ : ℂ)) = (α / (‖α‖ : ℂ))⁻¹ * (α * z + b) := by
  have hn : (‖α‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hα)
  rw [inv_div, div_div_eq_mul_div]
  field_simp

/-- T42 P helper: `κ n F n → κ₀ f` locally uniformly when `κ n → κ₀`, `F n → f` locally
uniformly and `f` is continuous. -/
theorem s04_tp_mulconv {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : TendstoLocallyUniformlyOn F f atTop U) (hf : ContinuousOn f U) {κ : ℕ → ℂ} {κ₀ : ℂ}
    (hκ : Tendsto κ atTop (𝓝 κ₀)) :
    TendstoLocallyUniformlyOn (fun n ζ => κ n * F n ζ + 0) (fun ζ => κ₀ * f ζ + 0) atTop U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU] at hF ⊢
  intro K hKU hK
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hf.mono hKU)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hM0 : 0 ≤ |M| := abs_nonneg M
  have h1 := Metric.tendstoUniformlyOn_iff.1 (hF K hKU hK) (ε / 2 / (‖κ₀‖ + 1)) (by positivity)
  have h2 : ∀ᶠ n in atTop, dist (κ n) κ₀ < ε / 2 / (|M| + 1) :=
    Metric.tendsto_nhds.1 hκ _ (by positivity)
  have h3 : ∀ᶠ n in atTop, dist (κ n) κ₀ < 1 := Metric.tendsto_nhds.1 hκ 1 one_pos
  filter_upwards [h1, h2, h3] with n hn1 hn2 hn3 x hx
  have hfx : ‖f x‖ ≤ |M| := (hM x hx).trans (le_abs_self M)
  have hkn : ‖κ n‖ ≤ ‖κ₀‖ + 1 := by
    have h := norm_sub_norm_le (κ n) κ₀
    rw [← dist_eq_norm] at h
    linarith
  have e1 : ‖κ₀ - κ n‖ * ‖f x‖ ≤ ε / 2 := by
    have ha : ‖κ₀ - κ n‖ ≤ ε / 2 / (|M| + 1) := by
      rw [← dist_eq_norm, dist_comm]
      exact hn2.le
    calc ‖κ₀ - κ n‖ * ‖f x‖ ≤ ε / 2 / (|M| + 1) * |M| :=
          mul_le_mul ha hfx (norm_nonneg _) (by positivity)
      _ ≤ ε / 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  have e2 : ‖κ n‖ * ‖f x - F n x‖ < ε / 2 := by
    have hb : ‖f x - F n x‖ < ε / 2 / (‖κ₀‖ + 1) := by
      rw [← dist_eq_norm]
      exact hn1 x hx
    calc ‖κ n‖ * ‖f x - F n x‖ ≤ (‖κ₀‖ + 1) * ‖f x - F n x‖ :=
          mul_le_mul_of_nonneg_right hkn (norm_nonneg _)
      _ < (‖κ₀‖ + 1) * (ε / 2 / (‖κ₀‖ + 1)) := mul_lt_mul_of_pos_left hb (by positivity)
      _ = ε / 2 := by field_simp
  have hsplit : κ₀ * f x + 0 - (κ n * F n x + 0) = (κ₀ - κ n) * f x + κ n * (f x - F n x) := by
    ring
  rw [dist_eq_norm, hsplit]
  calc ‖(κ₀ - κ n) * f x + κ n * (f x - F n x)‖
      ≤ ‖(κ₀ - κ n) * f x‖ + ‖κ n * (f x - F n x)‖ := norm_add_le _ _
    _ = ‖κ₀ - κ n‖ * ‖f x‖ + ‖κ n‖ * ‖f x - F n x‖ := by rw [norm_mul, norm_mul]
    _ < ε := by linarith

/-- T42 P: normalized subsequence (from `s03_wc_pairs`, `s03_wc_riemann` with anchor
`P i = 0`, `s03_wc_kernel`, then a convergent subsequence of the rotations `a_n/|a_n|`):
real similarities `A_n` with `A_n (w n) = 0`, Riemann maps `g_n` of `A_n(Ω n)` with `g_n 0 = 0`
converging to a Riemann map `g_L` of `D = g_L(𝔻)`, and kernel convergence to `D`. -/
theorem s04_tp_seq {K : ℝ} (hK : 1 ≤ K) (Ω Ωs : ℕ → Set ℂ)
    (hpair : ∀ n, IsKQuasiPair (Ω n) (Ωs n) K) (w : ℕ → ℂ) (hw : ∀ n, w n ∈ Ω n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (c : ℕ → ℝ) (b : ℕ → ℂ) (g : ℕ → ℂ → ℂ) (gL : ℂ → ℂ),
      (∀ n, 0 < c n ∧ (c n : ℂ) * w (φ n) + b n = 0) ∧
      (∀ n, IsConformalOnto (g n) unitDisc ((fun z => (c n : ℂ) * z + b n) '' Ω (φ n)) ∧
        g n 0 = 0) ∧
      IsConformalOnto gL unitDisc (gL '' unitDisc) ∧ gL 0 = 0 ∧
      TendstoLocallyUniformlyOn g gL atTop unitDisc ∧
      ∀ S : Set ℂ, IsCompact S → S ⊆ gL '' unitDisc →
        ∀ᶠ n in atTop, S ⊆ (fun z => (c n : ℂ) * z + b n) '' Ω (φ n) := by
  obtain ⟨φ1, hφ1, a, b, P, PL, HL, hab, hP, hPL, hPLs, hPL0, hHL, -, hinv⟩ :=
    s03_wc_pairs hK Ω Ωs hpair w hw
  have hy : (0 : ℂ) ∈ PL '' upperHalf := ⟨I, by show (0 : ℝ) < I.im; simp, hPL0⟩
  obtain ⟨φ2, hφ2, g', g'L, hg', hg'L, hg'L0, hconv⟩ :=
    s03_wc_riemann hK (fun n => (hP n).1) (fun n => (hP n).2.1) hPL hPLs hHL hinv hy
  have hker := (s03_wc_kernel (fun n => (hP n).1) (fun n => (hP n).2.1) hPL hPLs hHL hinv).1
  have ha0 : ∀ n, a n ≠ 0 := fun n => (hab n).1
  have hna : ∀ n, (‖a n‖ : ℂ) ≠ 0 := fun n =>
    Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (ha0 n))
  have hεn : ∀ n, a n / (‖a n‖ : ℂ) ≠ 0 := fun n => div_ne_zero (ha0 n) (hna n)
  have hen : ∀ n, ‖a n / (‖a n‖ : ℂ)‖ = 1 := fun n => by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 (ha0 n))]
  obtain ⟨e₀, he₀, φ3, hφ3, he⟩ := (isCompact_sphere (0 : ℂ) 1).tendsto_subseq
    (x := fun n => a (φ2 n) / (‖a (φ2 n)‖ : ℂ)) (fun n => mem_sphere_zero_iff_norm.2 (hen _))
  have he₀1 : ‖e₀‖ = 1 := mem_sphere_zero_iff_norm.1 he₀
  have he₀0 : e₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at he₀1
    exact zero_ne_one he₀1
  have hm : StrictMono (fun n => φ2 (φ3 n)) := hφ2.comp hφ3
  have himg : ∀ n, (fun z => ((‖a (φ2 (φ3 n))‖ : ℝ) : ℂ) * z +
      b (φ2 (φ3 n)) / (a (φ2 (φ3 n)) / (‖a (φ2 (φ3 n))‖ : ℂ))) '' Ω (φ1 (φ2 (φ3 n))) =
      (fun y => (a (φ2 (φ3 n)) / (‖a (φ2 (φ3 n))‖ : ℂ))⁻¹ * y + 0) ''
        (P (φ2 (φ3 n)) '' upperHalf) := by
    intro n
    rw [(hP _).2.2.2.1, image_image]
    congr 1
    funext z
    rw [add_zero]
    exact s04_tp_rot (ha0 _) _ z
  refine ⟨fun n => φ1 (φ2 (φ3 n)), hφ1.comp hm, fun n => ‖a (φ2 (φ3 n))‖,
    fun n => b (φ2 (φ3 n)) / (a (φ2 (φ3 n)) / (‖a (φ2 (φ3 n))‖ : ℂ)),
    fun n ζ => (a (φ2 (φ3 n)) / (‖a (φ2 (φ3 n))‖ : ℂ))⁻¹ * g' (φ3 n) ζ + 0,
    fun ζ => e₀⁻¹ * g'L ζ + 0, fun n => ?_, fun n => ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨norm_pos_iff.2 (ha0 _), ?_⟩
    rw [s04_tp_rot (ha0 _), (hab _).2, mul_zero]
  · refine ⟨?_, ?_⟩
    · rw [himg n]
      exact s04_tn_conf (hg' (φ3 n)).1 (inv_ne_zero (hεn (φ2 (φ3 n)))) 0
    · show (a (φ2 (φ3 n)) / (‖a (φ2 (φ3 n))‖ : ℂ))⁻¹ * g' (φ3 n) 0 + 0 = 0
      rw [(hg' (φ3 n)).2, mul_zero, add_zero]
  · have h := s04_tn_conf hg'L (inv_ne_zero he₀0) 0
    exact ⟨h.1, h.2.1, rfl⟩
  · show e₀⁻¹ * g'L 0 + 0 = 0
    rw [hg'L0, mul_zero, add_zero]
  · exact s04_tp_mulconv isOpen_ball (s04_tp_reidx hconv hφ3.tendsto_atTop)
      hg'L.1.continuousOn (he.inv₀ he₀0)
  · intro S hS hSD
    have hV : IsOpen (PL '' upperHalf) := hg'L.isOpen isOpen_ball
    have hC₀ : IsCompact ((fun s => e₀ * s) '' S) := hS.image (continuous_const.mul continuous_id)
    have hC₀V : (fun s => e₀ * s) '' S ⊆ PL '' upperHalf := by
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨ζ, hζ, hζs⟩ := hSD hs
      have h1 : e₀ * s = g'L ζ := by
        rw [← hζs]
        show e₀ * (e₀⁻¹ * g'L ζ + 0) = g'L ζ
        rw [add_zero, ← mul_assoc, mul_inv_cancel₀ he₀0, one_mul]
      show e₀ * s ∈ PL '' upperHalf
      rw [h1, ← hg'L.2.2]
      exact mem_image_of_mem _ hζ
    obtain ⟨δ, hδ, hδV⟩ := hC₀.exists_thickening_subset_open hV hC₀V
    have hCc : IsCompact (cthickening (δ / 2) ((fun s => e₀ * s) '' S)) := hC₀.cthickening
    have hCV : cthickening (δ / 2) ((fun s => e₀ * s) '' S) ⊆ PL '' upperHalf :=
      (cthickening_subset_thickening' hδ (half_lt_self hδ) _).trans hδV
    obtain ⟨M, hM⟩ := hS.isBounded.exists_norm_le
    have hev1 := hm.tendsto_atTop.eventually (hker _ hCc hCV)
    have hev2 : ∀ᶠ n in atTop,
        dist (a (φ2 (φ3 n)) / (‖a (φ2 (φ3 n))‖ : ℂ)) e₀ < δ / 2 / (|M| + 1) :=
      Metric.tendsto_nhds.1 he _ (by positivity)
    filter_upwards [hev1, hev2] with n hn1 hn2
    intro s hs
    have hεs : a (φ2 (φ3 n)) / (‖a (φ2 (φ3 n))‖ : ℂ) * s ∈
        cthickening (δ / 2) ((fun s => e₀ * s) '' S) := by
      refine Metric.mem_cthickening_of_dist_le _ (e₀ * s) _ _ (mem_image_of_mem _ hs) ?_
      rw [dist_eq_norm, ← sub_mul, norm_mul]
      have h1 : ‖a (φ2 (φ3 n)) / (‖a (φ2 (φ3 n))‖ : ℂ) - e₀‖ ≤ δ / 2 / (|M| + 1) := by
        rw [← dist_eq_norm]
        exact hn2.le
      have h2 : ‖s‖ ≤ |M| := (hM s hs).trans (le_abs_self M)
      have hM0 : 0 ≤ |M| := abs_nonneg M
      calc ‖a (φ2 (φ3 n)) / (‖a (φ2 (φ3 n))‖ : ℂ) - e₀‖ * ‖s‖ ≤ δ / 2 / (|M| + 1) * |M| :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ ≤ δ / 2 := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith
    have hmem := hn1 hεs
    rw [(hP _).2.2.2.1] at hmem
    obtain ⟨z, hz, hzeq⟩ := hmem
    have hzeq' : a (φ2 (φ3 n)) * z + b (φ2 (φ3 n)) =
        a (φ2 (φ3 n)) / (‖a (φ2 (φ3 n))‖ : ℂ) * s := hzeq
    refine ⟨z, hz, ?_⟩
    show (‖a (φ2 (φ3 n))‖ : ℂ) * z + b (φ2 (φ3 n)) / (a (φ2 (φ3 n)) / (‖a (φ2 (φ3 n))‖ : ℂ)) = s
    rw [s04_tp_rot (ha0 _), hzeq', ← mul_assoc, inv_mul_cancel₀ (hεn _), one_mul]

/-- T42 P: the inverse maps converge uniformly on compact subsets of `D` (Schwarz lemma for
`ψ_n ∘ g_L(r₁ ·)` bounds `|ψ_n| ≤ r₀/r₁` on `S ⊆ g_L(B(0,r₀))`; limit points are identified
through `g_n → g_L`). -/
theorem s04_tp_inv {Ω' : ℕ → Set ℂ} {g : ℕ → ℂ → ℂ} {gL : ℂ → ℂ}
    (hg : ∀ n, IsConformalOnto (g n) unitDisc (Ω' n) ∧ g n 0 = 0)
    (hgL : IsConformalOnto gL unitDisc (gL '' unitDisc)) (hgL0 : gL 0 = 0)
    (hconv : TendstoLocallyUniformlyOn g gL atTop unitDisc)
    (hker : ∀ S : Set ℂ, IsCompact S → S ⊆ gL '' unitDisc → ∀ᶠ n in atTop, S ⊆ Ω' n)
    {S : Set ℂ} (hS : IsCompact S) (hSD : S ⊆ gL '' unitDisc) :
    TendstoUniformlyOn (fun n => Function.invFunOn (g n) unitDisc)
      (Function.invFunOn gL unitDisc) atTop S := by
  have hψL := hgL.symm isOpen_ball
  have hD1 : Function.invFunOn gL unitDisc '' S ⊆ ball (0 : ℂ) 1 := by
    have h := image_mono (f := Function.invFunOn gL unitDisc) hSD
    have h2 : Function.invFunOn gL unitDisc '' (gL '' unitDisc) = unitDisc := hψL.2.2
    rw [h2] at h
    exact h
  have hK1 : IsCompact (Function.invFunOn gL unitDisc '' S) :=
    hS.image_of_continuousOn (hψL.1.continuousOn.mono hSD)
  obtain ⟨r₀', hr₀'1, hr₀'⟩ := exists_lt_subset_ball hK1.isClosed hD1
  set r₀ := max r₀' 0 with hr₀def
  have hr₀1 : r₀ < 1 := max_lt hr₀'1 one_pos
  have hr₀0 : 0 ≤ r₀ := le_max_right _ _
  set r₁ := (r₀ + 1) / 2 with hr₁def
  have hr01 : r₀ < r₁ := by rw [hr₁def]; linarith
  have hr11 : r₁ < 1 := by rw [hr₁def]; linarith
  have hr1 : 0 < r₁ := by linarith
  have hρ1 : r₀ / r₁ < 1 := (div_lt_one hr1).2 hr01
  have hSr : ∀ x ∈ S, Function.invFunOn gL unitDisc x ∈ ball (0 : ℂ) r₀ ∧
      gL (Function.invFunOn gL unitDisc x) = x := fun x hx =>
    ⟨ball_subset_ball (le_max_left _ _) (hr₀' (mem_image_of_mem _ hx)),
      Function.invFunOn_eq (hSD hx)⟩
  have hcb1 : closedBall (0 : ℂ) r₁ ⊆ unitDisc := closedBall_subset_ball hr11
  have hB1 : IsCompact (gL '' closedBall 0 r₁) :=
    (isCompact_closedBall 0 r₁).image_of_continuousOn (hgL.1.continuousOn.mono hcb1)
  have hbd : ∀ᶠ n in atTop, ∀ x ∈ S, x ∈ Ω' n ∧
      ‖Function.invFunOn (g n) unitDisc x‖ ≤ r₀ / r₁ := by
    filter_upwards [hker _ hB1 (image_mono hcb1)] with n hn
    intro x hx
    obtain ⟨hz0, hgz⟩ := hSr x hx
    have hxn : x ∈ Ω' n :=
      hn ⟨_, ball_subset_closedBall (ball_subset_ball hr01.le hz0), hgz⟩
    refine ⟨hxn, ?_⟩
    have hψn := (hg n).1.symm isOpen_ball
    have hm1 : MapsTo (fun ζ : ℂ => (r₁ : ℂ) * ζ) (ball 0 1) (closedBall 0 r₁) := by
      intro ζ hζ
      rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr1.le]
      have := mem_ball_zero_iff.1 hζ
      nlinarith [norm_nonneg ζ]
    have hm2 : MapsTo (fun ζ : ℂ => gL ((r₁ : ℂ) * ζ)) (ball 0 1) (Ω' n) :=
      fun ζ hζ => hn (mem_image_of_mem _ (hm1 hζ))
    have hFd : DifferentiableOn ℂ
        (fun ζ => Function.invFunOn (g n) unitDisc (gL ((r₁ : ℂ) * ζ))) (ball 0 1) :=
      hψn.1.comp (hgL.1.comp ((differentiable_id.const_mul _).differentiableOn)
        (hm1.mono_right hcb1)) hm2
    have hFm : MapsTo (fun ζ => Function.invFunOn (g n) unitDisc (gL ((r₁ : ℂ) * ζ)))
        (ball 0 1) (closedBall 0 1) := by
      intro ζ hζ
      have h := mem_image_of_mem (Function.invFunOn (g n) unitDisc) (hm2 hζ)
      have h2 : Function.invFunOn (g n) unitDisc '' Ω' n = unitDisc := hψn.2.2
      rw [h2] at h
      exact ball_subset_closedBall h
    have hF0 : (fun ζ => Function.invFunOn (g n) unitDisc (gL ((r₁ : ℂ) * ζ))) 0 = 0 := by
      show Function.invFunOn (g n) unitDisc (gL ((r₁ : ℂ) * 0)) = 0
      have h := (hg n).1.2.1.leftInvOn_invFunOn (mem_ball_self one_pos : (0 : ℂ) ∈ unitDisc)
      rw [(hg n).2] at h
      rw [mul_zero, hgL0]
      exact h
    set z := Function.invFunOn gL unitDisc x with hz
    have hr1' : (r₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr1.ne'
    have hzn : ‖z / (r₁ : ℂ)‖ = ‖z‖ / r₁ := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr1.le]
    have hz0' := mem_ball_zero_iff.1 hz0
    have hzl : ‖z / (r₁ : ℂ)‖ < 1 := by
      rw [hzn]
      exact lt_of_lt_of_le ((div_lt_div_iff_of_pos_right hr1).2 hz0') hρ1.le
    have h := Complex.norm_le_norm_of_mapsTo_ball hFd hFm hF0 hzl
    have he : (r₁ : ℂ) * (z / (r₁ : ℂ)) = z := mul_div_cancel₀ z hr1'
    simp only [he, hgz] at h
    rw [hzn] at h
    exact h.trans ((div_le_div_iff_of_pos_right hr1).2 hz0'.le)
  have key : TendstoUniformlyOn
      (fun n x => dist (Function.invFunOn gL unitDisc x) (Function.invFunOn (g n) unitDisc x))
      (fun _ => (0 : ℝ)) atTop S := by
    refine s03_wc_unif_of_seq hS fun x hx ζ hζS hζ => ?_
    have hL : Tendsto (fun n => Function.invFunOn gL unitDisc (ζ n)) atTop
        (𝓝 (Function.invFunOn gL unitDisc x)) :=
      (hψL.1.continuousOn x (hSD hx)).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hζ, Eventually.of_forall fun n => hSD (hζS n)⟩)
    have hM : Tendsto (fun n => Function.invFunOn (g n) unitDisc (ζ n)) atTop
        (𝓝 (Function.invFunOn gL unitDisc x)) := by
      refine tendsto_of_subseq_tendsto fun ns hns => ?_
      have hbd' := hns.eventually hbd
      have hfreq : ∃ᶠ k in atTop,
          Function.invFunOn (g (ns k)) unitDisc (ζ (ns k)) ∈ closedBall (0 : ℂ) (r₀ / r₁) :=
        (hbd'.mono fun k hk => mem_closedBall_zero_iff.2 (hk _ (hζS _)).2).frequently
      obtain ⟨z, hzρ, ms, hms, hlim⟩ := (isCompact_closedBall _ _).tendsto_subseq' hfreq
      refine ⟨ms, ?_⟩
      have hz1 : z ∈ unitDisc := closedBall_subset_ball hρ1 hzρ
      have hmm : Tendsto (fun k => ns (ms k)) atTop atTop := hns.comp hms.tendsto_atTop
      have hbd'' := hmm.eventually hbd
      have hyD : ∀ᶠ k in atTop,
          Function.invFunOn (g (ns (ms k))) unitDisc (ζ (ns (ms k))) ∈ unitDisc :=
        hbd''.mono fun k hk => mem_ball_zero_iff.2 (lt_of_le_of_lt (hk _ (hζS _)).2 hρ1)
      have h1 : Tendsto (fun k => g (ns (ms k))
          (Function.invFunOn (g (ns (ms k))) unitDisc (ζ (ns (ms k))))) atTop (𝓝 (gL z)) :=
        (s04_tp_reidx hconv hmm).tendsto_comp (hgL.1.continuousOn.continuousWithinAt hz1) hz1
          (tendsto_nhdsWithin_iff.2 ⟨hlim, hyD⟩)
      have h2 : ∀ᶠ k in atTop, g (ns (ms k))
          (Function.invFunOn (g (ns (ms k))) unitDisc (ζ (ns (ms k)))) = ζ (ns (ms k)) := by
        refine hbd''.mono fun k hk => ?_
        have hx' := (hk (ζ (ns (ms k))) (hζS (ns (ms k)))).1
        rw [← (hg (ns (ms k))).1.2.2] at hx'
        exact Function.invFunOn_eq hx'
      have hgz : gL z = x := tendsto_nhds_unique (h1.congr' h2) (hζ.comp hmm)
      have hψx : Function.invFunOn gL unitDisc x = z := by
        rw [← hgz]
        exact hgL.2.1.leftInvOn_invFunOn hz1
      rw [hψx]
      exact hlim
    have h := hL.dist hM
    rw [dist_self] at h
    exact h
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 key ε hε] with n hn x hx
  have h := hn x hx
  rw [dist_comm, Real.dist_0_eq_abs, abs_of_nonneg dist_nonneg] at h
  exact h

/-- T42 P: the closed `ρ`-balls of radius `r` about `0` eventually lie in one compact subset
of `D` (`s04_tb_disk_ball`, `subsec_poincare_dist`, uniform convergence on a closed disc). -/
theorem s04_tp_ball {Ω' : ℕ → Set ℂ} {g : ℕ → ℂ → ℂ} {gL : ℂ → ℂ}
    (hg : ∀ n, IsConformalOnto (g n) unitDisc (Ω' n) ∧ g n 0 = 0)
    (hgL : IsConformalOnto gL unitDisc (gL '' unitDisc)) (hgL0 : gL 0 = 0)
    (hconv : TendstoLocallyUniformlyOn g gL atTop unitDisc) (r : ℝ) :
    ∃ Kb : Set ℂ, IsCompact Kb ∧ Kb ⊆ gL '' unitDisc ∧
      ∀ᶠ n in atTop, rhoClosedBall (Ω' n) 0 r ⊆ Kb := by
  -- `gL 0 = 0` is not needed: the balls are centred at `g n 0 = 0`.
  have _h0 := hgL0
  set r' := max r 0 with hr'
  set t := √((Real.cosh r' - 1) / (Real.cosh r' + 1)) with htdef
  have hC1 : 1 ≤ Real.cosh r' := Real.one_le_cosh r'
  have ht1 : t < 1 := by
    rw [htdef, Real.sqrt_lt' one_pos, one_pow, div_lt_one (by linarith)]
    linarith
  set t' := (t + 1) / 2 with ht'def
  have htt' : t < t' := by rw [ht'def]; linarith
  have ht'1 : t' < 1 := by rw [ht'def]; linarith
  have hsub' : closedBall (0 : ℂ) t' ⊆ unitDisc := closedBall_subset_ball ht'1
  have hsubt : closedBall (0 : ℂ) t ⊆ unitDisc := closedBall_subset_ball (htt'.trans ht'1)
  have hbsub : ball (0 : ℂ) t' ⊆ unitDisc := ball_subset_ball ht'1.le
  refine ⟨gL '' closedBall 0 t',
    (isCompact_closedBall 0 t').image_of_continuousOn (hgL.1.continuousOn.mono hsub'),
    image_mono hsub', ?_⟩
  have hV : IsOpen (gL '' ball 0 t') :=
    IsConformalOnto.isOpen isOpen_ball ⟨hgL.1.mono hbsub, hgL.2.1.mono hbsub, rfl⟩
  have hCc : IsCompact (gL '' closedBall 0 t) :=
    (isCompact_closedBall 0 t).image_of_continuousOn (hgL.1.continuousOn.mono hsubt)
  obtain ⟨δ, hδ, hδV⟩ :=
    hCc.exists_thickening_subset_open hV (image_mono (closedBall_subset_ball htt'))
  have hU := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).1 hconv
    (closedBall 0 t) hsubt (isCompact_closedBall 0 t)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hU δ hδ] with n hn
  rintro v ⟨hv, hd⟩
  rw [← (hg n).1.2.2] at hv
  obtain ⟨z, hz, rfl⟩ := hv
  have hdz : diskDist 0 z ≤ r' := by
    have h := subsec_poincare_dist (hg n).1 (mem_ball_self one_pos) hz
    rw [(hg n).2] at h
    rw [← h]
    exact hd.trans (le_max_left _ _)
  have hzt : z ∈ closedBall (0 : ℂ) t := by
    rw [htdef, ← s04_tb_disk_ball (le_max_right r 0)]
    exact ⟨hz, hdz⟩
  have hmem : g n z ∈ thickening δ (gL '' closedBall 0 t) :=
    Metric.mem_thickening_iff.2 ⟨gL z, mem_image_of_mem _ hzt, by
      rw [dist_comm]; exact hn z hzt⟩
  exact image_mono ball_subset_closedBall (hδV hmem)

/-- T42 P: goodness with `η n → 0`, `R n → ∞` makes the limit domain flat: `S ψ_L = 0` on `D`
(`s03_wc_jets` for `s`, `subsec_poincare_natural_affine`, the upper bound of `prop_qi`,
`eq_def_s`). -/
theorem s04_tp_flat {K : ℝ} (hK : 1 ≤ K) {Ω Ωs : ℕ → Set ℂ} {w : ℕ → ℂ} {η R : ℕ → ℝ}
    (hpair : ∀ n, IsKQuasiPair (Ω n) (Ωs n) K) (hnl : ∀ n, ¬ IsLinePair (Ω n) (Ωs n))
    (hgood : ∀ n, IsGoodParam (Ω n) (Ωs n) (η n) (R n) (w n))
    (hη : Tendsto η atTop (𝓝 0)) (hR : Tendsto R atTop atTop) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {c : ℕ → ℝ} {b : ℕ → ℂ} {g : ℕ → ℂ → ℂ} {gL : ℂ → ℂ}
    (hcb : ∀ n, 0 < c n ∧ (c n : ℂ) * w (φ n) + b n = 0)
    (hg : ∀ n, IsConformalOnto (g n) unitDisc ((fun z => (c n : ℂ) * z + b n) '' Ω (φ n)) ∧
      g n 0 = 0)
    (hgL : IsConformalOnto gL unitDisc (gL '' unitDisc))
    (hconv : TendstoLocallyUniformlyOn g gL atTop unitDisc) :
    ∀ x ∈ gL '' unitDisc, schwarzian (Function.invFunOn gL unitDisc) x = 0 := by
  -- `1 ≤ K` is not needed here (the constants of `prop_qi` exist for every `K`).
  have _hK := hK
  obtain ⟨Aq, Bq, hqi⟩ := prop_qi K
  rintro x ⟨ζ, hζ, rfl⟩
  have hjet := (s03_wc_jets (fun n => (hg n).1) hgL hconv hζ (fun _ => hζ)
    tendsto_const_nhds).2.2.2.1
  have hev : ∀ᶠ n in atTop,
      schwarzNorm ((fun z => (c n : ℂ) * z + b n) '' Ω (φ n)) (g n ζ) < η (φ n) := by
    filter_upwards [(hR.comp hφ.tendsto_atTop).eventually_ge_atTop (5 / 2 * diskDist 0 ζ)]
      with n hn
    obtain ⟨hcn, hbn⟩ := hcb n
    have hcn' : (c n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hcn.ne'
    have hgz : g n ζ ∈ (fun z => (c n : ℂ) * z + b n) '' Ω (φ n) := by
      rw [← (hg n).1.2.2]
      exact mem_image_of_mem _ hζ
    obtain ⟨w', hw', hw'eq⟩ := hgz
    have hw'' : (c n : ℂ) * w' + b n = g n ζ := hw'eq
    have hΩn := s02_jordanPair_riemannMap (s03_b0_jordanPair (hpair (φ n)))
    have hwn : w (φ n) ∈ Ω (φ n) := (hgood (φ n)).1
    have hd : poincareDist (Ω (φ n)) (w (φ n)) w' = diskDist 0 ζ := by
      have h1 := subsec_poincare_dist (hg n).1 (mem_ball_self one_pos) hζ
      rw [(hg n).2, ← hw''] at h1
      rw [← s04_tn_dist (Ω (φ n)) hcn' (b n), hbn]
      exact h1
    rw [← hw'', (subsec_poincare_natural_affine hΩn hcn' hw').2]
    exact (s04_tb_good_s (hpair (φ n)) (hgood (φ n))).1 w' hw'
      (((hqi _ _ (hpair (φ n)) (hnl (φ n))).1 _ hwn _ hw').2.trans (by rw [hd]; exact hn))
  have hle : schwarzNorm (gL '' unitDisc) (gL ζ) ≤ 0 :=
    le_of_tendsto_of_tendsto hjet (hη.comp hφ.tendsto_atTop) (hev.mono fun n h => h.le)
  have hx : gL ζ ∈ gL '' unitDisc := mem_image_of_mem _ hζ
  have hpos := s02_poincareDensity_pos ⟨gL, hgL⟩ hx
  rw [eq_def_s hgL hx, div_le_iff₀ (by positivity), zero_mul] at hle
  exact norm_le_zero_iff.1 hle

/-! ## D: convergence of the data on `U ⋐ D` -/

/-- T42 D helper: `iteratedDeriv 2 f = f''`. -/
theorem s04_td_id2 (f : ℂ → ℂ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- T42 D helper: `iteratedDeriv 3 f = f'''`. -/
theorem s04_td_id3 (f : ℂ → ℂ) : iteratedDeriv 3 f = deriv (deriv (deriv f)) := by
  rw [iteratedDeriv_succ, s04_td_id2]

/-- T42 D helper: an injective holomorphic map on an open set has nonvanishing derivative. -/
theorem s04_td_derivne {ψ : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V) (hd : DifferentiableOn ℂ ψ V)
    (hinj : InjOn ψ V) : ∀ z ∈ V, deriv ψ z ≠ 0 := by
  have hc : TendstoLocallyUniformlyOn (fun _ : ℕ => ψ) ψ atTop V := fun u hu x _ =>
    ⟨univ, univ_mem, Eventually.of_forall fun _ y _ => refl_mem_uniformity hu⟩
  exact (s03_wc_weierstrass hV hc (fun _ => hd) hinj).2.1

/-- T42 D helper: holomorphic maps converging locally uniformly: so do all their derivatives. -/
theorem s04_td_holiter {U : Set ℂ} (hU : IsOpen U) (m : ℕ) :
    ∀ {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}, (∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U) →
      DifferentiableOn ℂ f U → TendstoLocallyUniformlyOn F f atTop U →
      (∀ᶠ n in atTop, DifferentiableOn ℂ (iteratedDeriv m (F n)) U) ∧
        DifferentiableOn ℂ (iteratedDeriv m f) U ∧
        TendstoLocallyUniformlyOn (fun n => iteratedDeriv m (F n)) (iteratedDeriv m f) atTop U := by
  induction m with
  | zero =>
    intro F f hF hf hc
    simp only [iteratedDeriv_zero]
    exact ⟨hF, hf, hc⟩
  | succ m ih =>
    intro F f hF hf hc
    simp only [iteratedDeriv_succ']
    exact ih (hF.mono fun n h => h.deriv hU) (hf.deriv hU) (hc.deriv hF hU)

/-- T42 D helper: `U ⊆ Ω' n` eventually, and `ψ_n → ψ_L` locally uniformly on `U`. -/
theorem s04_td_conv {Ω' : ℕ → Set ℂ} {g : ℕ → ℂ → ℂ} {gL : ℂ → ℂ}
    (hg : ∀ n, IsConformalOnto (g n) unitDisc (Ω' n) ∧ g n 0 = 0)
    (hgL : IsConformalOnto gL unitDisc (gL '' unitDisc)) (hgL0 : gL 0 = 0)
    (hconv : TendstoLocallyUniformlyOn g gL atTop unitDisc)
    (hker : ∀ S : Set ℂ, IsCompact S → S ⊆ gL '' unitDisc → ∀ᶠ n in atTop, S ⊆ Ω' n)
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsCompact (closure U))
    (hUD : closure U ⊆ gL '' unitDisc) :
    (∀ᶠ n in atTop, U ⊆ Ω' n) ∧
      TendstoLocallyUniformlyOn (fun n => Function.invFunOn (g n) unitDisc)
        (Function.invFunOn gL unitDisc) atTop U := by
  refine ⟨(hker _ hUc hUD).mono fun n hn => subset_closure.trans hn, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  exact s04_tp_inv hg hgL hgL0 hconv hker hK (hKU.trans (subset_closure.trans hUD))

/-- T42 D helper: holomorphy and locally uniform convergence of `ψ_n^{(m)}` on `U`. -/
theorem s04_td_psiD {Ω' : ℕ → Set ℂ} {g : ℕ → ℂ → ℂ} {gL : ℂ → ℂ}
    (hg : ∀ n, IsConformalOnto (g n) unitDisc (Ω' n) ∧ g n 0 = 0)
    (hgL : IsConformalOnto gL unitDisc (gL '' unitDisc)) (hgL0 : gL 0 = 0)
    (hconv : TendstoLocallyUniformlyOn g gL atTop unitDisc)
    (hker : ∀ S : Set ℂ, IsCompact S → S ⊆ gL '' unitDisc → ∀ᶠ n in atTop, S ⊆ Ω' n)
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsCompact (closure U))
    (hUD : closure U ⊆ gL '' unitDisc) (m : ℕ) :
    (∀ᶠ n in atTop, DifferentiableOn ℂ (iteratedDeriv m (Function.invFunOn (g n) unitDisc)) U) ∧
      DifferentiableOn ℂ (iteratedDeriv m (Function.invFunOn gL unitDisc)) U ∧
      TendstoLocallyUniformlyOn (fun n => iteratedDeriv m (Function.invFunOn (g n) unitDisc))
        (iteratedDeriv m (Function.invFunOn gL unitDisc)) atTop U := by
  obtain ⟨hsub, hc⟩ := s04_td_conv hg hgL hgL0 hconv hker hU hUc hUD
  exact s04_td_holiter hU m (hsub.mono fun n hn => ((hg n).1.symm isOpen_ball).1.mono hn)
    ((hgL.symm isOpen_ball).1.mono (subset_closure.trans hUD)) hc

/-- T42 D helper: `ψ_n' ≠ 0` and `ψ_n ∈ 𝔻` on `U` eventually; the same for `ψ_L`. -/
theorem s04_td_maps {Ω' : ℕ → Set ℂ} {g : ℕ → ℂ → ℂ} {gL : ℂ → ℂ}
    (hg : ∀ n, IsConformalOnto (g n) unitDisc (Ω' n) ∧ g n 0 = 0)
    (hgL : IsConformalOnto gL unitDisc (gL '' unitDisc))
    (hker : ∀ S : Set ℂ, IsCompact S → S ⊆ gL '' unitDisc → ∀ᶠ n in atTop, S ⊆ Ω' n)
    {U : Set ℂ} (hUc : IsCompact (closure U)) (hUD : closure U ⊆ gL '' unitDisc) :
    (∀ᶠ n in atTop, ∀ x ∈ U, x ∈ Ω' n ∧ deriv (Function.invFunOn (g n) unitDisc) x ≠ 0 ∧
      ‖Function.invFunOn (g n) unitDisc x‖ < 1) ∧
    ∀ x ∈ U, deriv (Function.invFunOn gL unitDisc) x ≠ 0 ∧
      ‖Function.invFunOn gL unitDisc x‖ < 1 := by
  refine ⟨(hker _ hUc hUD).mono fun n hn x hx => ?_, fun x hx => ?_⟩
  · have hxn : x ∈ Ω' n := hn (subset_closure hx)
    have hψn := (hg n).1.symm isOpen_ball
    refine ⟨hxn, s04_td_derivne ((hg n).1.isOpen isOpen_ball) hψn.1 hψn.2.1 x hxn, ?_⟩
    have h := mem_image_of_mem (Function.invFunOn (g n) unitDisc) hxn
    have h2 : Function.invFunOn (g n) unitDisc '' Ω' n = unitDisc := hψn.2.2
    rw [h2] at h
    exact mem_ball_zero_iff.1 h
  · have hxD : x ∈ gL '' unitDisc := hUD (subset_closure hx)
    have hψL := hgL.symm isOpen_ball
    refine ⟨s04_td_derivne (hgL.isOpen isOpen_ball) hψL.1 hψL.2.1 x hxD, ?_⟩
    have h := mem_image_of_mem (Function.invFunOn gL unitDisc) hxD
    have h2 : Function.invFunOn gL unitDisc '' (gL '' unitDisc) = unitDisc := hψL.2.2
    rw [h2] at h
    exact mem_ball_zero_iff.1 h

/-- T42 D: all complex derivatives of `ψ_n = g_n⁻¹` converge in `C^∞_loc(U)`. -/
theorem s04_td_psi {Ω' : ℕ → Set ℂ} {g : ℕ → ℂ → ℂ} {gL : ℂ → ℂ}
    (hg : ∀ n, IsConformalOnto (g n) unitDisc (Ω' n) ∧ g n 0 = 0)
    (hgL : IsConformalOnto gL unitDisc (gL '' unitDisc)) (hgL0 : gL 0 = 0)
    (hconv : TendstoLocallyUniformlyOn g gL atTop unitDisc)
    (hker : ∀ S : Set ℂ, IsCompact S → S ⊆ gL '' unitDisc → ∀ᶠ n in atTop, S ⊆ Ω' n)
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsCompact (closure U)) (hUD : closure U ⊆ gL '' unitDisc)
    (m : ℕ) :
    (∀ᶠ n in atTop,
      ContDiffOn ℝ ∞ (iteratedDeriv m (Function.invFunOn (g n) unitDisc)) U) ∧
      ContDiffOn ℝ ∞ (iteratedDeriv m (Function.invFunOn gL unitDisc)) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ i (iteratedDeriv m (Function.invFunOn (g n) unitDisc)))
        (iteratedFDeriv ℝ i (iteratedDeriv m (Function.invFunOn gL unitDisc))) atTop U := by
  obtain ⟨h1, -, h3⟩ := s04_td_psiD hg hgL hgL0 hconv hker hU hUc hUD m
  exact s04_tc_holo hU h1 h3

/-- T42 D: `λ_n → λ_D` in `C^∞_loc(U)` (`s02_poincareDensity_eq_inv`, `s04_td_psi`,
composition with `(a, z) ↦ 2|a|/(1-|z|²)` on `{a ≠ 0, |z| < 1}`). -/
theorem s04_td_lambda {Ω' : ℕ → Set ℂ} {g : ℕ → ℂ → ℂ} {gL : ℂ → ℂ}
    (hg : ∀ n, IsConformalOnto (g n) unitDisc (Ω' n) ∧ g n 0 = 0)
    (hgL : IsConformalOnto gL unitDisc (gL '' unitDisc)) (hgL0 : gL 0 = 0)
    (hconv : TendstoLocallyUniformlyOn g gL atTop unitDisc)
    (hker : ∀ S : Set ℂ, IsCompact S → S ⊆ gL '' unitDisc → ∀ᶠ n in atTop, S ⊆ Ω' n)
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsCompact (closure U))
    (hUD : closure U ⊆ gL '' unitDisc) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (poincareDensity (Ω' n)) U) ∧
      ContDiffOn ℝ ∞ (poincareDensity (gL '' unitDisc)) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (poincareDensity (Ω' n)))
        (iteratedFDeriv ℝ i (poincareDensity (gL '' unitDisc))) atTop U := by
  have hC1 := s04_td_psi hg hgL hgL0 hconv hker hU hUc hUD 1
  have hC0 := s04_td_psi hg hgL hgL0 hconv hker hU hUc hUD 0
  simp only [iteratedDeriv_one] at hC1
  simp only [iteratedDeriv_zero] at hC0
  have hG := s04_tc_pair hU hC1 hC0
  have hV : IsOpen {p : ℂ × ℂ | p.1 ≠ 0 ∧ ‖p.2‖ < 1} :=
    (isOpen_ne_fun continuous_fst continuous_const).inter
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const)
  have hΦ : ContDiffOn ℝ ∞ (fun p : ℂ × ℂ => 2 * ‖p.1‖ / (1 - ‖p.2‖ ^ 2))
      {p : ℂ × ℂ | p.1 ≠ 0 ∧ ‖p.2‖ < 1} := by
    intro p hp
    have h1 : ContDiffAt ℝ ∞ (fun p : ℂ × ℂ => ‖p.1‖) p :=
      (contDiffAt_norm ℝ hp.1).comp p contDiffAt_fst
    have h2 : ContDiffAt ℝ ∞ (fun p : ℂ × ℂ => 1 - ‖p.2‖ ^ 2) p :=
      contDiffAt_const.sub ((contDiff_norm_sq ℝ).contDiffAt.comp p contDiffAt_snd)
    have hne : 1 - ‖p.2‖ ^ 2 ≠ 0 := by
      have := hp.2
      nlinarith [norm_nonneg p.2]
    exact ((contDiffAt_const.mul h1).div h2 hne).contDiffWithinAt
  obtain ⟨hmn, hmL⟩ := s04_td_maps hg hgL hker hUc hUD
  have hcomp := s04_tc_comp hU hV (s04_tc_const hΦ) hG
    (hmn.mono fun n hn x hx => ⟨(hn x hx).2.1, (hn x hx).2.2⟩) fun x hx => hmL x hx
  exact s04_tc_congr hU hcomp
    (hmn.mono fun n hn x hx => s02_poincareDensity_eq_inv (hg n).1 (hn x hx).1)
    fun x hx => s02_poincareDensity_eq_inv hgL (hUD (subset_closure hx))

/-- T42 D: `∇φ_n → ∇φ_D` in `C^∞_loc(U)` (log, `s04_tc_fderiv`, evaluation at `1, i`). -/
theorem s04_td_grad {Ω' : ℕ → Set ℂ} {g : ℕ → ℂ → ℂ} {gL : ℂ → ℂ}
    (hg : ∀ n, IsConformalOnto (g n) unitDisc (Ω' n) ∧ g n 0 = 0)
    (hgL : IsConformalOnto gL unitDisc (gL '' unitDisc)) (hgL0 : gL 0 = 0)
    (hconv : TendstoLocallyUniformlyOn g gL atTop unitDisc)
    (hker : ∀ S : Set ℂ, IsCompact S → S ⊆ gL '' unitDisc → ∀ᶠ n in atTop, S ⊆ Ω' n)
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsCompact (closure U))
    (hUD : closure U ⊆ gL '' unitDisc) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (logDensityGrad (Ω' n)) U) ∧
      ContDiffOn ℝ ∞ (logDensityGrad (gL '' unitDisc)) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (logDensityGrad (Ω' n)))
        (iteratedFDeriv ℝ i (logDensityGrad (gL '' unitDisc))) atTop U := by
  have hl := s04_td_lambda hg hgL hgL0 hconv hker hU hUc hUD
  obtain ⟨hmn, -⟩ := s04_td_maps hg hgL hker hUc hUD
  have hlog := s04_tc_comp hU isOpen_compl_singleton (s04_tc_const Real.contDiffOn_log) hl
    (hmn.mono fun n hn x hx =>
      (s02_poincareDensity_pos ⟨g n, (hg n).1⟩ (hn x hx).1).ne')
    fun x hx => (s02_poincareDensity_pos ⟨gL, hgL⟩ (hUD (subset_closure hx))).ne'
  have hfd := s04_tc_fderiv hU hlog
  set L : (ℂ →L[ℝ] ℝ) →L[ℝ] ℂ := (ContinuousLinearMap.apply ℝ ℝ (1 : ℂ)).smulRight (1 : ℂ) +
    (ContinuousLinearMap.apply ℝ ℝ I).smulRight I with hL
  have hLv : ∀ φ : ℂ →L[ℝ] ℝ, L φ = ((φ 1 : ℝ) : ℂ) + ((φ I : ℝ) : ℂ) * I := fun φ => by
    simp [hL, Complex.real_smul]
  have hcl := s04_tc_clm hU L hfd
  refine s04_tc_congr hU hcl (Eventually.of_forall fun n x _ => ?_) fun x _ => ?_
  · show logDensityGrad (Ω' n) x = L (fderiv ℝ (fun x => Real.log (poincareDensity (Ω' n) x)) x)
    rw [hLv]
    rfl
  · show logDensityGrad (gL '' unitDisc) x =
      L (fderiv ℝ (fun x => Real.log (poincareDensity (gL '' unitDisc) x)) x)
    rw [hLv]
    rfl

/-- T42 D: `S ψ_n → S ψ_L` in `C^∞_loc(U)` (holomorphic, `s04_tc_holo`). -/
theorem s04_td_q {Ω' : ℕ → Set ℂ} {g : ℕ → ℂ → ℂ} {gL : ℂ → ℂ}
    (hg : ∀ n, IsConformalOnto (g n) unitDisc (Ω' n) ∧ g n 0 = 0)
    (hgL : IsConformalOnto gL unitDisc (gL '' unitDisc)) (hgL0 : gL 0 = 0)
    (hconv : TendstoLocallyUniformlyOn g gL atTop unitDisc)
    (hker : ∀ S : Set ℂ, IsCompact S → S ⊆ gL '' unitDisc → ∀ᶠ n in atTop, S ⊆ Ω' n)
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsCompact (closure U))
    (hUD : closure U ⊆ gL '' unitDisc) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (schwarzian (Function.invFunOn (g n) unitDisc)) U) ∧
      ContDiffOn ℝ ∞ (schwarzian (Function.invFunOn gL unitDisc)) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ i (schwarzian (Function.invFunOn (g n) unitDisc)))
        (iteratedFDeriv ℝ i (schwarzian (Function.invFunOn gL unitDisc))) atTop U := by
  have hC1 := s04_td_psi hg hgL hgL0 hconv hker hU hUc hUD 1
  have hC2 := s04_td_psi hg hgL hgL0 hconv hker hU hUc hUD 2
  have hC3 := s04_td_psi hg hgL hgL0 hconv hker hU hUc hUD 3
  simp only [iteratedDeriv_one] at hC1
  simp only [s04_td_id2] at hC2
  simp only [s04_td_id3] at hC3
  have hG := s04_tc_pair hU hC1 (s04_tc_pair hU hC2 hC3)
  have hV : IsOpen {p : ℂ × ℂ × ℂ | p.1 ≠ 0} := isOpen_ne_fun continuous_fst continuous_const
  have hΦ : ContDiffOn ℝ ∞ (fun p : ℂ × ℂ × ℂ =>
      (p.2.2 * p.1 - p.2.1 * p.2.1) / p.1 ^ 2 - 1 / 2 * (p.2.1 / p.1) ^ 2)
      {p : ℂ × ℂ × ℂ | p.1 ≠ 0} := by
    intro p hp
    have hp' : p.1 ≠ 0 := hp
    have h1 : ContDiffAt ℂ ∞ (fun p : ℂ × ℂ × ℂ =>
        (p.2.2 * p.1 - p.2.1 * p.2.1) / p.1 ^ 2 - 1 / 2 * (p.2.1 / p.1) ^ 2) p := by
      have ha : ContDiffAt ℂ ∞ (fun p : ℂ × ℂ × ℂ => p.1) p := contDiffAt_fst
      have hb : ContDiffAt ℂ ∞ (fun p : ℂ × ℂ × ℂ => p.2.1) p := contDiffAt_snd.fst
      have hc : ContDiffAt ℂ ∞ (fun p : ℂ × ℂ × ℂ => p.2.2) p := contDiffAt_snd.snd
      exact (((hc.mul ha).sub (hb.mul hb)).div (ha.pow 2) (pow_ne_zero 2 hp')).sub
        (contDiffAt_const.mul ((hb.div ha hp').pow 2))
    exact (h1.restrict_scalars ℝ).contDiffWithinAt
  obtain ⟨hmn, hmL⟩ := s04_td_maps hg hgL hker hUc hUD
  have hcomp := s04_tc_comp hU hV (s04_tc_const hΦ) hG
    (hmn.mono fun n hn x hx => (hn x hx).2.1) fun x hx => (hmL x hx).1
  refine s04_tc_congr hU hcomp (hmn.mono fun n hn x hx => ?_) fun x hx => ?_
  · have hψn := (hg n).1.symm isOpen_ball
    exact s03_wc_schwarzian_eq ((hg n).1.isOpen isOpen_ball) hψn.1 (hn x hx).1 (hn x hx).2.1
  · have hψL := hgL.symm isOpen_ball
    exact s03_wc_schwarzian_eq (hgL.isOpen isOpen_ball) hψL.1 (hUD (subset_closure hx))
      (hmL x hx).1

/-- T42 D helper: `cvec ∘ ofCvec = id`. -/
theorem s04_td_cvec_of (y : Fin 2 → ℝ) : cvec (ofCvec y) = y := by
  funext i
  fin_cases i <;> rfl

/-- T42 D helper: `cvec a ⬝ cvec b = Re(ā b)`. -/
theorem s04_td_dot (a b : ℂ) : cvec a ⬝ᵥ cvec b = (conj a * b).re := by
  simp only [cvec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- T42 D helper: the real part needed for `ρ(B·,·)`. -/
theorem s04_td_alg (a l d : ℝ) (S v w : ℂ) :
    (conj (((a : ℂ) * v - conj S * conj v / (l : ℂ)) / (d : ℂ)) * w).re =
      (a * (conj v * w).re - (S * v * w).re / l) / d := by
  rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, Complex.div_ofReal_re, map_sub,
    map_mul, Complex.conj_ofReal, map_div₀, Complex.conj_ofReal, map_mul, Complex.conj_conj,
    Complex.conj_conj, sub_mul, Complex.sub_re, mul_assoc, Complex.re_ofReal_mul,
    div_mul_eq_mul_div, Complex.div_ofReal_re]

/-- T42 D helper: `(I - ρ)(u) = (|S|²/λ²) Re(ū₀u₁) + 2 Re(S u₀ u₁)` (from `s02_curv_fI`). -/
theorem s04_td_fffeq {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {x : ℂ}
    (hx : x ∈ Ω) (u : Fin 2 → ℂ) :
    (fffT Ω - rhoMetricT Ω) x u =
      ‖schwarzian (Function.invFunOn f unitDisc) x‖ ^ 2 / poincareDensity Ω x ^ 2 *
          (conj (u 0) * u 1).re +
        2 * (schwarzian (Function.invFunOn f unitDisc) x * u 0 * u 1).re := by
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hx
  show hypInner (epstein Ω x) (fderiv ℝ (epstein Ω) x (u 0)) (fderiv ℝ (epstein Ω) x (u 1)) -
      poincareDensity Ω x ^ 2 * (conj (u 0) * u 1).re = _
  have hre : (u 0 * conj (u 1)).re = (conj (u 0) * u 1).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [s02_curv_fI hf hx, eq_def_s hf hx, hre]
  field_simp
  ring

/-- T42 D helper: `ρ(B u₀, u₁)` in terms of `λ` and `S` where `|S| < λ²` (`s05_sa_shapeApply`). -/
theorem s04_td_shapeeq {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {x : ℂ}
    (hx : x ∈ Ω)
    (hs : ‖schwarzian (Function.invFunOn f unitDisc) x‖ ^ 2 < poincareDensity Ω x ^ 4)
    (u : Fin 2 → ℂ) :
    shapeT Ω x u =
      (‖schwarzian (Function.invFunOn f unitDisc) x‖ ^ 2 / poincareDensity Ω x ^ 2 *
          (conj (u 0) * u 1).re -
        (schwarzian (Function.invFunOn f unitDisc) x * u 0 * u 1).re) /
        (1 - ‖schwarzian (Function.invFunOn f unitDisc) x‖ ^ 2 / poincareDensity Ω x ^ 4) := by
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hx
  have hsdef := eq_def_s hf hx
  have hlt : ‖schwarzian (Function.invFunOn f unitDisc) x‖ < poincareDensity Ω x ^ 2 := by
    by_contra h
    have h2 := pow_le_pow_left₀ (by positivity) (not_lt.1 h) 2
    have h4 : (poincareDensity Ω x ^ 2) ^ 2 = poincareDensity Ω x ^ 4 := by ring
    linarith
  have hsl : schwarzNorm Ω x < 1 := by
    rw [hsdef]
    exact (div_lt_one (by positivity)).2 hlt
  have hs0 : 0 ≤ schwarzNorm Ω x := by
    rw [hsdef]
    positivity
  have hs1 : schwarzNorm Ω x ≠ 1 := hsl.ne
  have hB : shapeMat Ω x *ᵥ cvec (u 0) = cvec (shapeApply Ω x (u 0)) := by
    show _ = cvec (ofCvec (shapeMat Ω x *ᵥ cvec (u 0)))
    rw [s04_td_cvec_of]
  have hd : (1 : ℝ) - schwarzNorm Ω x ^ 2 ≠ 0 := by
    have : schwarzNorm Ω x ^ 2 < 1 := by nlinarith
    linarith
  show poincareDensity Ω x ^ 2 * ((shapeMat Ω x *ᵥ cvec (u 0)) ⬝ᵥ cvec (u 1)) = _
  rw [hB, s04_td_dot, s05_sa_shapeApply hf hx hs1, s04_td_alg]
  rw [hsdef] at hd ⊢
  field_simp

/-- T42 D helper: on a flat limit, eventually `|S ψ_n| < λ_n²` on `U` (uniform convergence on
`closure U`, through a thickening `U'` of `closure U` inside `D`). -/
theorem s04_td_small {Ω' : ℕ → Set ℂ} {g : ℕ → ℂ → ℂ} {gL : ℂ → ℂ}
    (hg : ∀ n, IsConformalOnto (g n) unitDisc (Ω' n) ∧ g n 0 = 0)
    (hgL : IsConformalOnto gL unitDisc (gL '' unitDisc)) (hgL0 : gL 0 = 0)
    (hconv : TendstoLocallyUniformlyOn g gL atTop unitDisc)
    (hker : ∀ S : Set ℂ, IsCompact S → S ⊆ gL '' unitDisc → ∀ᶠ n in atTop, S ⊆ Ω' n)
    {U : Set ℂ} (hUc : IsCompact (closure U)) (hUD : closure U ⊆ gL '' unitDisc)
    (hflat : ∀ x ∈ gL '' unitDisc, schwarzian (Function.invFunOn gL unitDisc) x = 0) :
    ∀ᶠ n in atTop, ∀ x ∈ U, ‖schwarzian (Function.invFunOn (g n) unitDisc) x‖ ^ 2 <
      poincareDensity (Ω' n) x ^ 4 := by
  have hD : IsOpen (gL '' unitDisc) := hgL.isOpen isOpen_ball
  obtain ⟨δ, hδ, hδD⟩ := hUc.exists_thickening_subset_open hD hUD
  have hU' : IsOpen (thickening (δ / 2) (closure U)) := isOpen_thickening
  have hcl : closure (thickening (δ / 2) (closure U)) ⊆ cthickening (δ / 2) (closure U) :=
    closure_thickening_subset_cthickening _ _
  have hcc : IsCompact (closure (thickening (δ / 2) (closure U))) :=
    hUc.cthickening.of_isClosed_subset isClosed_closure hcl
  have hU'D : closure (thickening (δ / 2) (closure U)) ⊆ gL '' unitDisc :=
    hcl.trans ((cthickening_subset_thickening' hδ (half_lt_self hδ) _).trans hδD)
  have hUU' : closure U ⊆ thickening (δ / 2) (closure U) := self_subset_thickening (half_pos hδ) _
  have hl := s04_td_lambda hg hgL hgL0 hconv hker hU' hcc hU'D
  have hq := s04_td_q hg hgL hgL0 hconv hker hU' hcc hU'D
  have hlu := s04_tc_unif hU' hl hUc hUU'
  have hqu := s04_tc_unif hU' hq hUc hUU'
  obtain ⟨m₀, hm₀, hmin⟩ := hUc.exists_forall_le' (hl.2.1.continuousOn.mono hUU')
    (fun x hx => s02_poincareDensity_pos ⟨gL, hgL⟩ (hUD hx))
  have ha : 0 < m₀ / 2 := half_pos hm₀
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hlu (m₀ / 2) ha,
    Metric.tendstoUniformlyOn_iff.1 hqu ((m₀ / 2) ^ 2) (by positivity)] with n h1 h2 x hx
  have hxc := subset_closure hx
  have e1 := h1 x hxc
  rw [Real.dist_eq, abs_lt] at e1
  have e2 := h2 x hxc
  rw [hflat x (hUD hxc), dist_zero_left] at e2
  have hlam : m₀ / 2 < poincareDensity (Ω' n) x := by linarith [hmin x hxc, e1.2]
  have h4 : (m₀ / 2) ^ 4 < poincareDensity (Ω' n) x ^ 4 :=
    pow_lt_pow_left₀ hlam ha.le (by norm_num)
  have h5 : ‖schwarzian (Function.invFunOn (g n) unitDisc) x‖ ^ 2 < ((m₀ / 2) ^ 2) ^ 2 :=
    pow_lt_pow_left₀ e2 (norm_nonneg _) two_ne_zero
  calc ‖schwarzian (Function.invFunOn (g n) unitDisc) x‖ ^ 2 < ((m₀ / 2) ^ 2) ^ 2 := h5
    _ = (m₀ / 2) ^ 4 := by ring
    _ < _ := h4

/-- T42 D: on a flat limit, the tensors `I - ρ` and `ρ(B·,·)` of `Ω' n`, as functions of
`(x, u)`, converge to `0` in `C^∞_loc(U × ℂ²)` (explicit formulas in `λ_n`, `S ψ_n`). -/
theorem s04_td_tensors {Ω' : ℕ → Set ℂ} {g : ℕ → ℂ → ℂ} {gL : ℂ → ℂ}
    (hg : ∀ n, IsConformalOnto (g n) unitDisc (Ω' n) ∧ g n 0 = 0)
    (hgL : IsConformalOnto gL unitDisc (gL '' unitDisc)) (hgL0 : gL 0 = 0)
    (hconv : TendstoLocallyUniformlyOn g gL atTop unitDisc)
    (hker : ∀ S : Set ℂ, IsCompact S → S ⊆ gL '' unitDisc → ∀ᶠ n in atTop, S ⊆ Ω' n)
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsCompact (closure U))
    (hUD : closure U ⊆ gL '' unitDisc)
    (hflat : ∀ x ∈ gL '' unitDisc, schwarzian (Function.invFunOn gL unitDisc) x = 0) :
    ((∀ᶠ n in atTop, ContDiffOn ℝ ∞
        (fun p : ℂ × (Fin 2 → ℂ) => (fffT (Ω' n) - rhoMetricT (Ω' n)) p.1 p.2) (U ×ˢ univ)) ∧
      ContDiffOn ℝ ∞ (fun p : ℂ × (Fin 2 → ℂ) => (0 : TensorField 2) p.1 p.2) (U ×ˢ univ) ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ i
          (fun p : ℂ × (Fin 2 → ℂ) => (fffT (Ω' n) - rhoMetricT (Ω' n)) p.1 p.2))
        (iteratedFDeriv ℝ i (fun p : ℂ × (Fin 2 → ℂ) => (0 : TensorField 2) p.1 p.2))
        atTop (U ×ˢ univ)) ∧
    ((∀ᶠ n in atTop, ContDiffOn ℝ ∞
        (fun p : ℂ × (Fin 2 → ℂ) => shapeT (Ω' n) p.1 p.2) (U ×ˢ univ)) ∧
      ContDiffOn ℝ ∞ (fun p : ℂ × (Fin 2 → ℂ) => (0 : TensorField 2) p.1 p.2) (U ×ˢ univ) ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ i (fun p : ℂ × (Fin 2 → ℂ) => shapeT (Ω' n) p.1 p.2))
        (iteratedFDeriv ℝ i (fun p : ℂ × (Fin 2 → ℂ) => (0 : TensorField 2) p.1 p.2))
        atTop (U ×ˢ univ)) := by
  have hUU : IsOpen (U ×ˢ (univ : Set (Fin 2 → ℂ))) := hU.prod isOpen_univ
  have hl := s04_td_lambda hg hgL hgL0 hconv hker hU hUc hUD
  have hq := s04_td_q hg hgL hgL0 hconv hker hU hUc hUD
  have hfst : MapsTo (fun p : ℂ × (Fin 2 → ℂ) => p.1) (U ×ˢ univ) U := fun p hp => hp.1
  have hLm := s04_tc_comp hUU hU hl (s04_tc_const contDiff_fst.contDiffOn)
    (Eventually.of_forall fun _ => hfst) hfst
  have hSg := s04_tc_comp hUU hU hq (s04_tc_const contDiff_fst.contDiffOn)
    (Eventually.of_forall fun _ => hfst) hfst
  have hu := s04_tc_const (f := fun p : ℂ × (Fin 2 → ℂ) => p.2) (U := U ×ˢ univ)
    contDiff_snd.contDiffOn
  have hG := s04_tc_pair hUU hLm (s04_tc_pair hUU hSg hu)
  obtain ⟨hmn, -⟩ := s04_td_maps hg hgL hker hUc hUD
  have hsm := s04_td_small hg hgL hgL0 hconv hker hUc hUD hflat
  -- smooth building blocks on `ℝ × ℂ × ℂ²`
  have cS : ContDiff ℝ ∞ (fun q : ℝ × ℂ × (Fin 2 → ℂ) => ‖q.2.1‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp contDiff_snd.fst
  have cl : ContDiff ℝ ∞ (fun q : ℝ × ℂ × (Fin 2 → ℂ) => q.1) := contDiff_fst
  have cu0 : ContDiff ℝ ∞ (fun q : ℝ × ℂ × (Fin 2 → ℂ) => q.2.2 0) :=
    (contDiff_apply ℝ (fun _ : Fin 2 => ℂ) 0).comp contDiff_snd.snd
  have cu1 : ContDiff ℝ ∞ (fun q : ℝ × ℂ × (Fin 2 → ℂ) => q.2.2 1) :=
    (contDiff_apply ℝ (fun _ : Fin 2 => ℂ) 1).comp contDiff_snd.snd
  have cR1 : ContDiff ℝ ∞ (fun q : ℝ × ℂ × (Fin 2 → ℂ) => (conj (q.2.2 0) * q.2.2 1).re) :=
    Complex.reCLM.contDiff.comp ((Complex.conjCLE.contDiff.comp cu0).mul cu1)
  have cR2 : ContDiff ℝ ∞ (fun q : ℝ × ℂ × (Fin 2 → ℂ) => (q.2.1 * q.2.2 0 * q.2.2 1).re) :=
    Complex.reCLM.contDiff.comp ((contDiff_snd.fst.mul cu0).mul cu1)
  have hV1 : IsOpen {q : ℝ × ℂ × (Fin 2 → ℂ) | q.1 ≠ 0} :=
    isOpen_ne_fun continuous_fst continuous_const
  have hV2 : IsOpen {q : ℝ × ℂ × (Fin 2 → ℂ) | q.1 ≠ 0 ∧ ‖q.2.1‖ ^ 2 < q.1 ^ 4} :=
    (isOpen_ne_fun continuous_fst continuous_const).inter
      (isOpen_lt ((continuous_norm.comp continuous_snd.fst).pow 2) (continuous_fst.pow 4))
  have hF1 : ContDiffOn ℝ ∞ (fun q : ℝ × ℂ × (Fin 2 → ℂ) =>
      ‖q.2.1‖ ^ 2 / q.1 ^ 2 * (conj (q.2.2 0) * q.2.2 1).re + 2 * (q.2.1 * q.2.2 0 * q.2.2 1).re)
      {q : ℝ × ℂ × (Fin 2 → ℂ) | q.1 ≠ 0} := by
    intro q hq
    have hq' : q.1 ≠ 0 := hq
    exact (((cS.contDiffAt.div (cl.pow 2).contDiffAt (pow_ne_zero 2 hq')).mul
      cR1.contDiffAt).add (contDiffAt_const.mul cR2.contDiffAt)).contDiffWithinAt
  have hF2 : ContDiffOn ℝ ∞ (fun q : ℝ × ℂ × (Fin 2 → ℂ) =>
      (‖q.2.1‖ ^ 2 / q.1 ^ 2 * (conj (q.2.2 0) * q.2.2 1).re - (q.2.1 * q.2.2 0 * q.2.2 1).re) /
        (1 - ‖q.2.1‖ ^ 2 / q.1 ^ 4))
      {q : ℝ × ℂ × (Fin 2 → ℂ) | q.1 ≠ 0 ∧ ‖q.2.1‖ ^ 2 < q.1 ^ 4} := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := hq
    have hden : 1 - ‖q.2.1‖ ^ 2 / q.1 ^ 4 ≠ 0 := by
      have : ‖q.2.1‖ ^ 2 / q.1 ^ 4 < 1 := (div_lt_one (by positivity)).2 hq2
      linarith
    exact ((((cS.contDiffAt.div (cl.pow 2).contDiffAt (pow_ne_zero 2 hq1)).mul
      cR1.contDiffAt).sub cR2.contDiffAt).div
      (contDiffAt_const.sub (cS.contDiffAt.div (cl.pow 4).contDiffAt (pow_ne_zero 4 hq1)))
      hden).contDiffWithinAt
  have hlamL : ∀ p ∈ U ×ˢ (univ : Set (Fin 2 → ℂ)),
      0 < poincareDensity (gL '' unitDisc) p.1 := fun p hp =>
    s02_poincareDensity_pos ⟨gL, hgL⟩ (hUD (subset_closure hp.1))
  have hSL : ∀ p ∈ U ×ˢ (univ : Set (Fin 2 → ℂ)),
      schwarzian (Function.invFunOn gL unitDisc) p.1 = 0 := fun p hp =>
    hflat _ (hUD (subset_closure hp.1))
  refine ⟨?_, ?_⟩
  · have hc := s04_tc_comp hUU hV1 (s04_tc_const hF1) hG
      (hmn.mono fun n hn p hp => (s02_poincareDensity_pos ⟨g n, (hg n).1⟩ (hn p.1 hp.1).1).ne')
      fun p hp => (hlamL p hp).ne'
    refine s04_tc_congr hUU hc (hmn.mono fun n hn p hp => ?_) fun p hp => ?_
    · exact s04_td_fffeq (hg n).1 (hn p.1 hp.1).1 p.2
    · show (0 : ℝ) = _
      rw [hSL p hp]
      simp
  · have hc := s04_tc_comp hUU hV2 (s04_tc_const hF2) hG
      ((hmn.and hsm).mono fun n hn p hp =>
        ⟨(s02_poincareDensity_pos ⟨g n, (hg n).1⟩ (hn.1 p.1 hp.1).1).ne', hn.2 p.1 hp.1⟩)
      fun p hp => ⟨(hlamL p hp).ne', by rw [hSL p hp, norm_zero, zero_pow two_ne_zero]; exact pow_pos (hlamL p hp) 4⟩
    refine s04_tc_congr hUU hc ((hmn.and hsm).mono fun n hn p hp => ?_) fun p hp => ?_
    · exact s04_td_shapeeq (hg n).1 (hn.1 p.1 hp.1).1 (hn.2 p.1 hp.1) p.2
    · show (0 : ℝ) = _
      rw [hSL p hp]
      simp

/-! ## W: W-CJ by compactness -/

/-- T42 W helper: finite sums preserve joint `C^∞_loc` convergence. -/
theorem s04_tw_sum {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {ι : Type*}
    (s : Finset ι) {f : ι → ℕ → E → F} {fL : ι → E → F}
    (hf : ∀ i ∈ s, (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f i n) U) ∧ ContDiffOn ℝ ∞ (fL i) U ∧
      ∀ l : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ l (f i n))
        (iteratedFDeriv ℝ l (fL i)) atTop U) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fun x => ∑ i ∈ s, f i n x) U) ∧
      ContDiffOn ℝ ∞ (fun x => ∑ i ∈ s, fL i x) U ∧
      ∀ l : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ l (fun x => ∑ i ∈ s, f i n x))
        (iteratedFDeriv ℝ l (fun x => ∑ i ∈ s, fL i x)) atTop U := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact s04_tc_congr hU (s04_tc_const (f := fun _ : E => (0 : F)) contDiffOn_const)
      (Eventually.of_forall fun n x _ => by simp) fun x _ => by simp
  | @insert a s ha ih =>
    intro hf
    have h1 := s04_tc_add hU (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    exact s04_tc_congr hU h1 (Eventually.of_forall fun n x _ => by simp [Finset.sum_insert ha])
      fun x _ => by simp [Finset.sum_insert ha]

/-- T42 W helper: a partial derivative in the first factor, as the full derivative applied to
`(v, 0)`. -/
theorem s04_tw_pfd {k : ℕ} {F : ℂ × (Fin k → ℂ) → ℝ} {x : ℂ} {c : Fin k → ℂ}
    (h : DifferentiableAt ℝ F (x, c)) (v : ℂ) :
    fderiv ℝ (fun y => F (y, c)) x v = fderiv ℝ F (x, c) (v, 0) := by
  have h3 : HasFDerivAt (fun y => F (y, c))
      ((fderiv ℝ F (x, c)).comp (ContinuousLinearMap.inl ℝ ℂ (Fin k → ℂ))) x :=
    h.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x c)
  rw [h3.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inl_apply]

/-- T42 W helper: the Christoffel substitution `v ↦ (v₁, …, Γ(v₀, v_{i+1}), …, v_k)` is smooth
jointly in the gradient `g` and `v`. -/
theorem s04_tw_updsmooth {k : ℕ} (i : Fin k) :
    ContDiff ℝ ∞ (fun q : ℂ × (Fin (k + 1) → ℂ) => Function.update (Fin.tail q.2) i
      ((((conj q.1 * q.2 0).re : ℝ) : ℂ) * Fin.tail q.2 i +
        (((conj q.1 * Fin.tail q.2 i).re : ℝ) : ℂ) * q.2 0 -
          (((conj (q.2 0) * Fin.tail q.2 i).re : ℝ) : ℂ) * q.1)) := by
  have cg : ContDiff ℝ ∞ (fun q : ℂ × (Fin (k + 1) → ℂ) => q.1) := contDiff_fst
  have cX : ContDiff ℝ ∞ (fun q : ℂ × (Fin (k + 1) → ℂ) => q.2 0) :=
    (contDiff_apply ℝ (fun _ : Fin (k + 1) => ℂ) 0).comp contDiff_snd
  have cY : ∀ t : Fin k, ContDiff ℝ ∞ (fun q : ℂ × (Fin (k + 1) → ℂ) => Fin.tail q.2 t) :=
    fun t => (contDiff_apply ℝ (fun _ : Fin (k + 1) => ℂ) t.succ).comp contDiff_snd
  have cre : ∀ {a b : ℂ × (Fin (k + 1) → ℂ) → ℂ}, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      ContDiff ℝ ∞ (fun q => (((conj (a q) * b q).re : ℝ) : ℂ)) := fun ha hb =>
    Complex.ofRealCLM.contDiff.comp
      (Complex.reCLM.contDiff.comp ((Complex.conjCLE.contDiff.comp ha).mul hb))
  have cΓ := (((cre cg cX).mul (cY i)).add ((cre cg (cY i)).mul cX)).sub
    ((cre cX (cY i)).mul cg)
  refine contDiff_pi.2 fun t => ?_
  by_cases ht : t = i
  · subst ht
    simp only [Function.update_self]
    exact cΓ
  · simp only [Function.update_of_ne ht]
    exact cY t

/-- T42 W: one covariant derivative preserves joint `C^∞_loc` convergence (general limit, so
that `lem_Cj` can reuse it). -/
theorem s04_tw_step {Ω' : ℕ → Set ℂ} {ΩL : Set ℂ} {U : Set ℂ} (hU : IsOpen U) {k : ℕ}
    {T : ℕ → TensorField k} {TL : TensorField k}
    (hT : (∀ᶠ n in atTop, ContDiffOn ℝ ∞
        (fun p : ℂ × (Fin k → ℂ) => T n p.1 p.2) (U ×ˢ univ)) ∧
      ContDiffOn ℝ ∞ (fun p : ℂ × (Fin k → ℂ) => TL p.1 p.2) (U ×ˢ univ) ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ i (fun p : ℂ × (Fin k → ℂ) => T n p.1 p.2))
        (iteratedFDeriv ℝ i (fun p : ℂ × (Fin k → ℂ) => TL p.1 p.2)) atTop (U ×ˢ univ))
    (hG : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (logDensityGrad (Ω' n)) U) ∧
      ContDiffOn ℝ ∞ (logDensityGrad ΩL) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (logDensityGrad (Ω' n)))
        (iteratedFDeriv ℝ i (logDensityGrad ΩL)) atTop U) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞
        (fun p : ℂ × (Fin (k + 1) → ℂ) => rhoCovDeriv (Ω' n) (T n) p.1 p.2) (U ×ˢ univ)) ∧
      ContDiffOn ℝ ∞ (fun p : ℂ × (Fin (k + 1) → ℂ) => rhoCovDeriv ΩL TL p.1 p.2)
        (U ×ˢ univ) ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ i
          (fun p : ℂ × (Fin (k + 1) → ℂ) => rhoCovDeriv (Ω' n) (T n) p.1 p.2))
        (iteratedFDeriv ℝ i (fun p : ℂ × (Fin (k + 1) → ℂ) => rhoCovDeriv ΩL TL p.1 p.2))
        atTop (U ×ˢ univ) := by
  have hW : IsOpen (U ×ˢ (univ : Set (Fin k → ℂ))) := hU.prod isOpen_univ
  have hW' : IsOpen (U ×ˢ (univ : Set (Fin (k + 1) → ℂ))) := hU.prod isOpen_univ
  have hfst : MapsTo (fun p : ℂ × (Fin (k + 1) → ℂ) => p.1) (U ×ˢ univ) U := fun p hp => hp.1
  -- the Christoffel sum
  have hGf := s04_tc_comp hW' hU hG (s04_tc_const contDiff_fst.contDiffOn)
    (Eventually.of_forall fun _ => hfst) hfst
  have hq := s04_tc_pair hW' hGf
    (s04_tc_const (f := fun p : ℂ × (Fin (k + 1) → ℂ) => p.2) contDiff_snd.contDiffOn)
  have hχ := fun i : Fin k => s04_tc_pair hW'
    (s04_tc_const (f := fun p : ℂ × (Fin (k + 1) → ℂ) => p.1) contDiff_fst.contDiffOn)
    (s04_tc_comp hW' isOpen_univ (s04_tc_const (s04_tw_updsmooth i).contDiffOn) hq
      (Eventually.of_forall fun _ => mapsTo_univ _ _) (mapsTo_univ _ _))
  have hχm : ∀ (h : ℂ × (Fin (k + 1) → ℂ) → Fin k → ℂ),
      MapsTo (fun p : ℂ × (Fin (k + 1) → ℂ) => (p.1, h p)) (U ×ˢ univ) (U ×ˢ univ) :=
    fun _ p hp => ⟨hp.1, mem_univ _⟩
  have hS := s04_tw_sum hW' Finset.univ fun i _ =>
    s04_tc_comp hW' hW hT (hχ i) (Eventually.of_forall fun _ => hχm _) (hχm _)
  -- the derivative term
  have hD := s04_tc_fderiv hW hT
  have hφ : ContDiff ℝ ∞ (fun p : ℂ × (Fin (k + 1) → ℂ) => (p.1, Fin.tail p.2)) :=
    contDiff_fst.prodMk (contDiff_pi.2 fun t =>
      (contDiff_apply ℝ (fun _ : Fin (k + 1) => ℂ) t.succ).comp contDiff_snd)
  have hDφ := s04_tc_comp hW' hW hD (s04_tc_const hφ.contDiffOn)
    (Eventually.of_forall fun _ => hχm _) (hχm _)
  have hψ : ContDiff ℝ ∞
      (fun p : ℂ × (Fin (k + 1) → ℂ) => ((p.2 0, (0 : Fin k → ℂ)) : ℂ × (Fin k → ℂ))) :=
    ((contDiff_apply ℝ (fun _ : Fin (k + 1) => ℂ) 0).comp contDiff_snd).prodMk contDiff_const
  have ht1 := s04_tc_bilin hW' (ContinuousLinearMap.apply ℝ ℝ) (s04_tc_const hψ.contDiffOn) hDφ
  have hfin := s04_tc_comp hW' isOpen_univ
    (s04_tc_const (f := fun q : ℝ × ℝ => q.1 - q.2) (contDiff_fst.sub contDiff_snd).contDiffOn)
    (s04_tc_pair hW' ht1 hS) (Eventually.of_forall fun _ => mapsTo_univ _ _) (mapsTo_univ _ _)
  refine s04_tc_congr hW' hfin (hT.1.mono fun n hn p hp => ?_) fun p hp => ?_
  · have hd : DifferentiableAt ℝ (fun q : ℂ × (Fin k → ℂ) => T n q.1 q.2) (p.1, Fin.tail p.2) :=
      (s04_tc_at hW hn (hχm (fun p => Fin.tail p.2) hp) 1).differentiableAt (by simp)
    unfold rhoCovDeriv rhoChristoffel
    dsimp only
    rw [ContinuousLinearMap.apply_apply, ← s04_tw_pfd hd]
  · have hd : DifferentiableAt ℝ (fun q : ℂ × (Fin k → ℂ) => TL q.1 q.2) (p.1, Fin.tail p.2) :=
      (s04_tc_at hW hT.2.1 (hχm (fun p => Fin.tail p.2) hp) 1).differentiableAt (by simp)
    unfold rhoCovDeriv rhoChristoffel
    dsimp only
    rw [ContinuousLinearMap.apply_apply, ← s04_tw_pfd hd]

/-- T42 W: all iterated covariant derivatives converge (induction on `j`, `s04_tw_step`). -/
theorem s04_tw_iter {Ω' : ℕ → Set ℂ} {ΩL : Set ℂ} {U : Set ℂ} (hU : IsOpen U) {k : ℕ}
    {T : ℕ → TensorField k} {TL : TensorField k}
    (hT : (∀ᶠ n in atTop, ContDiffOn ℝ ∞
        (fun p : ℂ × (Fin k → ℂ) => T n p.1 p.2) (U ×ˢ univ)) ∧
      ContDiffOn ℝ ∞ (fun p : ℂ × (Fin k → ℂ) => TL p.1 p.2) (U ×ˢ univ) ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ i (fun p : ℂ × (Fin k → ℂ) => T n p.1 p.2))
        (iteratedFDeriv ℝ i (fun p : ℂ × (Fin k → ℂ) => TL p.1 p.2)) atTop (U ×ˢ univ))
    (hG : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (logDensityGrad (Ω' n)) U) ∧
      ContDiffOn ℝ ∞ (logDensityGrad ΩL) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (logDensityGrad (Ω' n)))
        (iteratedFDeriv ℝ i (logDensityGrad ΩL)) atTop U) (j : ℕ) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞
        (fun p : ℂ × (Fin (k + j) → ℂ) => rhoIterCovDeriv (Ω' n) j (T n) p.1 p.2)
        (U ×ˢ univ)) ∧
      ContDiffOn ℝ ∞ (fun p : ℂ × (Fin (k + j) → ℂ) => rhoIterCovDeriv ΩL j TL p.1 p.2)
        (U ×ˢ univ) ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ i
          (fun p : ℂ × (Fin (k + j) → ℂ) => rhoIterCovDeriv (Ω' n) j (T n) p.1 p.2))
        (iteratedFDeriv ℝ i
          (fun p : ℂ × (Fin (k + j) → ℂ) => rhoIterCovDeriv ΩL j TL p.1 p.2))
        atTop (U ×ˢ univ) := by
  induction j generalizing k with
  | zero => exact hT
  | succ j ih =>
    have h1 := ih (s04_tw_step hU hT hG)
    have hc : k + 1 + j = k + (j + 1) := by omega
    have hW1 : IsOpen (U ×ˢ (univ : Set (Fin (k + 1 + j) → ℂ))) := hU.prod isOpen_univ
    have hW' : IsOpen (U ×ˢ (univ : Set (Fin (k + (j + 1)) → ℂ))) := hU.prod isOpen_univ
    have hι : ContDiff ℝ ∞
        (fun p : ℂ × (Fin (k + (j + 1)) → ℂ) => (p.1, p.2 ∘ Fin.cast hc)) :=
      contDiff_fst.prodMk (contDiff_pi.2 fun t =>
        (contDiff_apply ℝ (fun _ : Fin (k + (j + 1)) => ℂ) (Fin.cast hc t)).comp contDiff_snd)
    have hm : MapsTo (fun p : ℂ × (Fin (k + (j + 1)) → ℂ) => (p.1, p.2 ∘ Fin.cast hc))
        (U ×ˢ univ) (U ×ˢ univ) := fun p hp => ⟨hp.1, mem_univ _⟩
    have h2 := s04_tc_comp hW' hW1 h1 (s04_tc_const hι.contDiffOn)
      (Eventually.of_forall fun _ => hm) hm
    exact s04_tc_congr hW' h2 (Eventually.of_forall fun n p _ => rfl) fun p _ => rfl

/-- T42 W: `∇^j 0 = 0`. -/
theorem s04_tw_zero (Ω : Set ℂ) (j : ℕ) {k : ℕ} (x : ℂ) (v : Fin (k + j) → ℂ) :
    rhoIterCovDeriv Ω j (0 : TensorField k) x v = 0 := by
  induction j generalizing k with
  | zero => rfl
  | succ j ih =>
    have h0 : rhoCovDeriv Ω (0 : TensorField k) = 0 := by
      funext w u
      show fderiv ℝ (fun _ : ℂ => (0 : ℝ)) w (u 0) - ∑ _i : Fin k, (0 : ℝ) = 0
      simp
    show rhoIterCovDeriv Ω j (rhoCovDeriv Ω (0 : TensorField k)) x (v ∘ Fin.cast (by omega)) = 0
    rw [h0]
    exact ih _

/-- T42 W helper: the `C^0` part of W-CJ for one tensor: joint convergence and `λ_n → λ_L` give
eventually `‖A_n‖_ρ ≤ δ` on a compact `K` where `‖A_L‖_ρ < δ` (compare
`δ² λ^{2m} - Σ A(e_idx)²`, which converges uniformly on `K` and is positive in the limit). -/
theorem s04_tw_cj1 {Ω' : ℕ → Set ℂ} {ΩL : Set ℂ} {U K : Set ℂ} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {m : ℕ} {A : ℕ → TensorField m} {AL : TensorField m}
    (hA : (∀ᶠ n in atTop, ContDiffOn ℝ ∞
        (fun p : ℂ × (Fin m → ℂ) => A n p.1 p.2) (U ×ˢ univ)) ∧
      ContDiffOn ℝ ∞ (fun p : ℂ × (Fin m → ℂ) => AL p.1 p.2) (U ×ˢ univ) ∧
      ∀ l : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ l (fun p : ℂ × (Fin m → ℂ) => A n p.1 p.2))
        (iteratedFDeriv ℝ l (fun p : ℂ × (Fin m → ℂ) => AL p.1 p.2)) atTop (U ×ˢ univ))
    (hlam_ : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (poincareDensity (Ω' n)) U) ∧
      ContDiffOn ℝ ∞ (poincareDensity ΩL) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (poincareDensity (Ω' n)))
        (iteratedFDeriv ℝ i (poincareDensity ΩL)) atTop U)
    (hlampos : ∀ x ∈ U, 0 < poincareDensity ΩL x) {δ : ℝ}
    (hδ : ∀ x ∈ K, rhoTensorNorm ΩL AL x < δ) :
    ∀ᶠ n in atTop, ∀ x ∈ K, rhoTensorNorm (Ω' n) (A n) x ≤ δ := by
  have hUU : IsOpen (U ×ˢ (univ : Set (Fin m → ℂ))) := hU.prod isOpen_univ
  have ha : ∀ idx : Fin m → Fin 2,
      (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fun x => (A n x fun t => frameVec (idx t)) ^ 2) U) ∧
      ContDiffOn ℝ ∞ (fun x => (AL x fun t => frameVec (idx t)) ^ 2) U ∧
      ∀ l : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ l (fun x => (A n x fun t => frameVec (idx t)) ^ 2))
        (iteratedFDeriv ℝ l (fun x => (AL x fun t => frameVec (idx t)) ^ 2)) atTop U := by
    intro idx
    have hmap : MapsTo (fun x : ℂ => (x, fun t => frameVec (idx t))) U (U ×ˢ univ) :=
      fun x hx => ⟨hx, mem_univ _⟩
    have h1 := s04_tc_comp hU hUU hA
      (s04_tc_const (contDiff_id.prodMk contDiff_const).contDiffOn)
      (Eventually.of_forall fun _ => hmap) hmap
    exact s04_tc_comp hU isOpen_univ
      (s04_tc_const (f := fun y : ℝ => y ^ 2) (contDiff_id.pow 2).contDiffOn) h1
      (Eventually.of_forall fun _ => mapsTo_univ _ _) (mapsTo_univ _ _)
  have hS := s04_tw_sum hU Finset.univ fun idx _ => ha idx
  have hP := s04_tc_comp hU isOpen_univ
    (s04_tc_const (f := fun y : ℝ => δ ^ 2 * y ^ (2 * m))
      (contDiff_const.mul (contDiff_id.pow _)).contDiffOn) hlam_
    (Eventually.of_forall fun _ => mapsTo_univ _ _) (mapsTo_univ _ _)
  have hQ := s04_tc_comp hU isOpen_univ
    (s04_tc_const (f := fun q : ℝ × ℝ => q.1 - q.2) (contDiff_fst.sub contDiff_snd).contDiffOn)
    (s04_tc_pair hU hP hS) (Eventually.of_forall fun _ => mapsTo_univ _ _) (mapsTo_univ _ _)
  have hpos : ∀ x ∈ K, 0 < δ ^ 2 * poincareDensity ΩL x ^ (2 * m) -
      ∑ idx : Fin m → Fin 2, (AL x fun t => frameVec (idx t)) ^ 2 := by
    intro x hx
    have hl := hlampos x (hKU hx)
    have h := hδ x hx
    have hsum : 0 ≤ ∑ idx : Fin m → Fin 2, (AL x fun t => frameVec (idx t)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h1 : √(∑ idx : Fin m → Fin 2, (AL x fun t => frameVec (idx t)) ^ 2) <
        δ * poincareDensity ΩL x ^ m := (div_lt_iff₀ (pow_pos hl m)).1 h
    have h2 := pow_lt_pow_left₀ h1 (Real.sqrt_nonneg _) two_ne_zero
    rw [Real.sq_sqrt hsum] at h2
    have h3 : (δ * poincareDensity ΩL x ^ m) ^ 2 = δ ^ 2 * poincareDensity ΩL x ^ (2 * m) := by
      ring
    linarith
  obtain ⟨c, hc, hcK⟩ := hK.exists_forall_le' (hQ.2.1.continuousOn.mono hKU) hpos
  obtain ⟨c2, hc2, hc2K⟩ := hK.exists_forall_le' (hlam_.2.1.continuousOn.mono hKU)
    fun x hx => hlampos x (hKU hx)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 (s04_tc_unif hU hQ hK hKU) c hc,
    Metric.tendstoUniformlyOn_iff.1 (s04_tc_unif hU hlam_ hK hKU) c2 hc2] with n h1 h2 x hx
  have e1 := h1 x hx
  have e2 := h2 x hx
  have e3 := hcK x hx
  have e4 := hc2K x hx
  rw [Real.dist_eq, abs_lt] at e1 e2
  dsimp only at e1 e3
  have hl : 0 < poincareDensity (Ω' n) x := by linarith
  have hlL := hlampos x (hKU hx)
  have hδ0 : 0 ≤ δ := by
    have h := hδ x hx
    have : 0 ≤ rhoTensorNorm ΩL AL x := div_nonneg (Real.sqrt_nonneg _) (pow_nonneg hlL.le _)
    linarith
  have hq : ∑ idx : Fin m → Fin 2, (A n x fun t => frameVec (idx t)) ^ 2 <
      δ ^ 2 * poincareDensity (Ω' n) x ^ (2 * m) := by linarith
  show √(∑ idx : Fin m → Fin 2, (A n x fun i => frameVec (idx i)) ^ 2) /
      poincareDensity (Ω' n) x ^ m ≤ δ
  rw [div_le_iff₀ (pow_pos hl m)]
  have h3 : (δ * poincareDensity (Ω' n) x ^ m) ^ 2 =
      δ ^ 2 * poincareDensity (Ω' n) x ^ (2 * m) := by ring
  calc √(∑ idx : Fin m → Fin 2, (A n x fun i => frameVec (idx i)) ^ 2)
      ≤ √((δ * poincareDensity (Ω' n) x ^ m) ^ 2) := Real.sqrt_le_sqrt (by linarith)
    _ = δ * poincareDensity (Ω' n) x ^ m := Real.sqrt_sq (mul_nonneg hδ0 (pow_nonneg hl.le _))

/-- T42 W: from joint convergence of `∇^i T_n` (`i ≤ j`) and `λ_n → λ_L`, the `C^j` norms on a
compact `K ⊆ U` are eventually below any `δ` exceeding the limit's pointwise norms on `K`. -/
theorem s04_tw_cj {Ω' : ℕ → Set ℂ} {ΩL : Set ℂ} {U K : Set ℂ} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {k : ℕ} {T : ℕ → TensorField k} {TL : TensorField k}
    (hT : ∀ i : ℕ, (∀ᶠ n in atTop, ContDiffOn ℝ ∞
        (fun p : ℂ × (Fin (k + i) → ℂ) => rhoIterCovDeriv (Ω' n) i (T n) p.1 p.2)
        (U ×ˢ univ)) ∧
      ContDiffOn ℝ ∞ (fun p : ℂ × (Fin (k + i) → ℂ) => rhoIterCovDeriv ΩL i TL p.1 p.2)
        (U ×ˢ univ) ∧
      ∀ l : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ l
          (fun p : ℂ × (Fin (k + i) → ℂ) => rhoIterCovDeriv (Ω' n) i (T n) p.1 p.2))
        (iteratedFDeriv ℝ l
          (fun p : ℂ × (Fin (k + i) → ℂ) => rhoIterCovDeriv ΩL i TL p.1 p.2))
        atTop (U ×ˢ univ))
    (hlam_ : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (poincareDensity (Ω' n)) U) ∧
      ContDiffOn ℝ ∞ (poincareDensity ΩL) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (poincareDensity (Ω' n)))
        (iteratedFDeriv ℝ i (poincareDensity ΩL)) atTop U)
    (hlampos : ∀ x ∈ U, 0 < poincareDensity ΩL x) (j : ℕ) {δ : ℝ}
    (hδ : ∀ i ≤ j, ∀ x ∈ K, rhoTensorNorm ΩL (rhoIterCovDeriv ΩL i TL) x < δ) :
    ∀ᶠ n in atTop, rhoCjNorm (Ω' n) j (T n) K ≤ ENNReal.ofReal δ := by
  have h := (Filter.eventually_all_finite (Set.finite_Iic j)).2 fun i (hi : i ∈ Set.Iic j) =>
    s04_tw_cj1 hU hK hKU (hT i) hlam_ hlampos (hδ i hi)
  filter_upwards [h] with n hn
  show (⨆ (i : ℕ) (_ : i ≤ j) (w : ℂ) (_ : w ∈ K),
    ENNReal.ofReal (rhoTensorNorm (Ω' n) (rhoIterCovDeriv (Ω' n) i (T n)) w)) ≤ _
  exact iSup₂_le fun i hi => iSup₂_le fun w hw => ENNReal.ofReal_le_ofReal (hn i hi w hw)

/-! ## G: the slab graph (sub-interface T43)

Route: the normalized package of T42/P is extended by the star side (`s03_wc_riemann_lower`,
translated to centre `0` so that stage D applies verbatim) and by the identification of the limit
pair as complementary half-planes `{0 < Im(αz+β)}`, `{Im(αz+β) < 0}` (`s04_tg_line`: `S ψ_L = 0`
and LiZhongQC's local Möbius uniqueness, `∂D = P_L(ℝ)` unbounded).  In the limit everything is
explicit (`s02_halfplane`): `E_L(v, τ)` meets `Σ*_L` exactly at `τ = 0`, `z = v̄` (the reflection of
`v` in the line), transversally, and `Φ*_{E_L(v,τ)}(v̄) = e^{-τ}`.  A parametric implicit function
theorem with `C^∞_loc` convergence (`s04_tg_ift`) solves `E_n(v, τ) = X*_n(z)` near `(0, v̄)`; the
no-return lemma (`prop_qi` + compactness) shows these are the only solutions in the tube; then
`slabTop`/`slabMap` are identified by uniqueness (`slabMap` is a `choose`, so it is not
transported by naturality) and everything is pulled back to the original coordinates
(`s04_tg_pull`, deterministic).  `‖t‖_{C^j}` is stage W with `k = 0`. -/

/-! ### G0: naturality and deterministic helpers -/

/-- T43 G2 helper: `A = ∂_w log λ = conj(∇ log λ)/2`. -/
theorem s04_tg_dz_grad (Ω : Set ℂ) (w : ℂ) :
    logDensityDz Ω w = conj (logDensityGrad Ω w) / 2 := by
  show (((fderiv ℝ (fun x => Real.log (poincareDensity Ω x)) w 1 : ℝ) : ℂ) -
      I * ((fderiv ℝ (fun x => Real.log (poincareDensity Ω x)) w I : ℝ) : ℂ)) / 2 =
    conj (((fderiv ℝ (fun x => Real.log (poincareDensity Ω x)) w 1 : ℝ) : ℂ) +
      ((fderiv ℝ (fun x => Real.log (poincareDensity Ω x)) w I : ℝ) : ℂ) * I) / 2
  rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- T43 G2 helper: `‖conj G / 2‖² = ‖G‖²/4`. -/
theorem s04_tg_normconj (G : ℂ) : ‖conj G / 2‖ ^ 2 = ‖G‖ ^ 2 / 4 := by
  rw [norm_div, Complex.norm_conj, Complex.norm_two]
  ring

/-- T43 G2 helper: the Epstein map in terms of `λ` and `G = ∇ log λ`. -/
theorem s04_tg_ep_eq (Ω : Set ℂ) (x : ℂ) :
    epstein Ω x = (x + (2 / (poincareDensity Ω x ^ 2 + ‖logDensityGrad Ω x‖ ^ 2)) •
        logDensityGrad Ω x,
      2 * poincareDensity Ω x / (poincareDensity Ω x ^ 2 + ‖logDensityGrad Ω x‖ ^ 2)) := by
  unfold epstein
  rw [s04_tg_dz_grad, map_div₀, Complex.conj_conj, map_ofNat, s04_tg_normconj,
    show (4 : ℝ) * (‖logDensityGrad Ω x‖ ^ 2 / 4) = ‖logDensityGrad Ω x‖ ^ 2 by ring]
  refine Prod.ext ?_ ?_
  · simp only
    rw [Complex.real_smul]
    push_cast
    ring
  · rfl

/-- T43 G2 helper: the normal geodesics in terms of `λ` and `G = ∇ log λ`. -/
theorem s04_tg_ng_eq (Ω : Set ℂ) (x : ℂ) (τ : ℝ) :
    normalGeod Ω x τ = (x + (1 / (2 * (‖logDensityGrad Ω x‖ ^ 2 / 4 +
        (poincareDensity Ω x * Real.exp (-τ) / 2) ^ 2))) • logDensityGrad Ω x,
      (poincareDensity Ω x * Real.exp (-τ) / 2) /
        (‖logDensityGrad Ω x‖ ^ 2 / 4 + (poincareDensity Ω x * Real.exp (-τ) / 2) ^ 2)) := by
  unfold normalGeod
  rw [s04_tg_dz_grad, map_div₀, Complex.conj_conj, map_ofNat, s04_tg_normconj]
  refine Prod.ext ?_ ?_
  · simp only
    rw [Complex.real_smul, one_div, mul_inv]
    push_cast
    ring
  · rfl

/-- T43 G0 helper: `Φ_q(w)` is invariant under a real similarity. -/
theorem s04_tg_horophi {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {c : ℝ}
    (hc : 0 < c) (b : ℂ) {w : ℂ} (hw : w ∈ Ω) (q : ℂ × ℝ) :
    horoPhi ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * q.1 + b, c * q.2) ((c : ℂ) * w + b) =
      horoPhi Ω q w := by
  have hl := (s04_tn_lambda hΩ hc b hw).1
  unfold horoPhi
  simp only
  rw [show (c : ℂ) * q.1 + b - ((c : ℂ) * w + b) = (c : ℂ) * (q.1 - w) by ring, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hc.le, ← hl]
  generalize poincareDensity ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * w + b) = l
  rcases eq_or_ne q.2 0 with h | h
  · simp [h]
  · field_simp

/-- T43 G0 helper: `∇^j T` at points of an open `V` only depends on `T` on `V`. -/
theorem s04_tg_covloc (Ω : Set ℂ) {V : Set ℂ} (hV : IsOpen V) (j : ℕ) :
    ∀ {k : ℕ} {T T' : TensorField k}, (∀ w ∈ V, ∀ u : Fin k → ℂ, T w u = T' w u) →
      ∀ w ∈ V, ∀ u : Fin (k + j) → ℂ,
        rhoIterCovDeriv Ω j T w u = rhoIterCovDeriv Ω j T' w u := by
  induction j with
  | zero =>
    intro k T T' h w hw u
    exact h w hw u
  | succ j ih =>
    intro k T T' h w hw u
    have hcov : ∀ x ∈ V, ∀ v : Fin (k + 1) → ℂ,
        rhoCovDeriv Ω T x v = rhoCovDeriv Ω T' x v := by
      intro x hx v
      have hev : (fun y => T y (Fin.tail v)) =ᶠ[𝓝 x] fun y => T' y (Fin.tail v) := by
        filter_upwards [hV.mem_nhds hx] with y hy
        exact h y hy _
      show fderiv ℝ (fun y => T y (Fin.tail v)) x (v 0) -
          ∑ i : Fin k, T x (Function.update (Fin.tail v) i
            (rhoChristoffel Ω x (v 0) (Fin.tail v i))) =
        fderiv ℝ (fun y => T' y (Fin.tail v)) x (v 0) -
          ∑ i : Fin k, T' x (Function.update (Fin.tail v) i
            (rhoChristoffel Ω x (v 0) (Fin.tail v i)))
      rw [hev.fderiv_eq]
      congr 1
      exact Finset.sum_congr rfl fun i _ => h x hx _
    exact ih hcov w hw _

/-- T43 G0: the normal geodesic under a real similarity `A z = c z + b`. -/
theorem s04_tg_geod {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {c : ℝ}
    (hc : 0 < c) (b : ℂ) {w : ℂ} (hw : w ∈ Ω) (τ : ℝ) :
    normalGeod ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * w + b) τ =
      ((c : ℂ) * (normalGeod Ω w τ).1 + b, c * (normalGeod Ω w τ).2) := by
  obtain ⟨hl, hG⟩ := s04_tn_lambda hΩ hc b hw
  have hlp : 0 < poincareDensity Ω w := s02_poincareDensity_pos hΩ hw
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hl' : poincareDensity ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * w + b) =
      poincareDensity Ω w / c := by
    rw [← hl]
    field_simp
  rw [s04_tg_ng_eq, s04_tg_ng_eq, hl', hG, norm_div, Complex.norm_real,
    Real.norm_of_nonneg hc.le]
  have he := Real.exp_pos (-τ)
  generalize logDensityGrad Ω w = G
  generalize poincareDensity Ω w = l at hlp ⊢
  generalize Real.exp (-τ) = e at he ⊢
  have hD : 0 < ‖G‖ ^ 2 / 4 + (l * e / 2) ^ 2 :=
    add_pos_of_nonneg_of_pos (by positivity) (pow_pos (div_pos (mul_pos hlp he) two_pos) 2)
  have hD' : (‖G‖ / c) ^ 2 / 4 + (l / c * e / 2) ^ 2 =
      (‖G‖ ^ 2 / 4 + (l * e / 2) ^ 2) / c ^ 2 := by
    field_simp
  rw [hD']
  generalize ‖G‖ ^ 2 / 4 + (l * e / 2) ^ 2 = D at hD ⊢
  have hDc : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hD.ne'
  refine Prod.ext ?_ ?_
  · simp only
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    field_simp
    ring
  · simp only
    field_simp

/-- T43 G0: `int U` under a real similarity. -/
theorem s04_tg_horo {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {c : ℝ}
    (hc : 0 < c) (b : ℂ) (q : ℂ × ℝ) :
    ((c : ℂ) * q.1 + b, c * q.2) ∈ interior (horoUnion ((fun z => (c : ℂ) * z + b) '' Ω)) ↔
      q ∈ interior (horoUnion Ω) := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  set A : ℂ × ℝ ≃ₜ ℂ × ℝ := ((Homeomorph.mulLeft₀ (c : ℂ) hc').trans
    (Homeomorph.addRight b)).prodCongr (Homeomorph.mulLeft₀ c hc.ne') with hA
  have hAq : ∀ q : ℂ × ℝ, A q = ((c : ℂ) * q.1 + b, c * q.2) := fun q => rfl
  have hS : horoUnion Ω = A ⁻¹' horoUnion ((fun z => (c : ℂ) * z + b) '' Ω) := by
    ext q
    rw [mem_preimage, hAq]
    constructor
    · intro hq
      obtain ⟨hq1, w, hw, hq2⟩ : 0 < q.2 ∧ ∃ w ∈ Ω, horoPhi Ω q w ≤ 1 := by
        simpa [horoUnion, horoball, UHS] using hq
      have h : ((c : ℂ) * q.1 + b, c * q.2) ∈
          horoball ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * w + b) := by
        refine ⟨mul_pos hc hq1, ?_⟩
        rw [s04_tg_horophi hΩ hc b hw q]
        exact hq2
      exact mem_biUnion (mem_image_of_mem _ hw) h
    · intro hq
      obtain ⟨hq1, w, hw, hq2⟩ : 0 < c * q.2 ∧ ∃ w ∈ Ω,
          horoPhi ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * q.1 + b, c * q.2)
            ((c : ℂ) * w + b) ≤ 1 := by
        simpa [horoUnion, horoball, UHS] using hq
      rw [s04_tg_horophi hΩ hc b hw q] at hq2
      exact mem_biUnion hw ⟨(mul_pos_iff_of_pos_left hc).1 hq1, hq2⟩
  rw [hS, ← Homeomorph.preimage_interior]
  exact Iff.rfl

/-- T43 G0: closed `ρ`-balls under a real similarity. -/
theorem s04_tg_cball {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {c : ℝ}
    (hc : 0 < c) (b : ℂ) {w : ℂ} (hw : w ∈ Ω) (r : ℝ) :
    rhoClosedBall ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * w + b) r =
      (fun z => (c : ℂ) * z + b) '' rhoClosedBall Ω w r := by
  have _h := hΩ
  have _h' := hw
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  ext w'
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hd⟩
    have hd' : poincareDist ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * w + b)
        ((c : ℂ) * y + b) ≤ r := hd
    rw [s04_tn_dist Ω hc' b w y] at hd'
    exact ⟨y, ⟨hy, hd'⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hd⟩, rfl⟩
    refine ⟨mem_image_of_mem _ hy, ?_⟩
    show poincareDist ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * w + b)
        ((c : ℂ) * y + b) ≤ r
    rw [s04_tn_dist Ω hc' b w y]
    exact hd

/-- T43 G0: `slabTop` under a real similarity (it is an `sInf`, no `choose`). -/
theorem s04_tg_slabnat {K : ℝ} {Ω Ωs : Set ℂ} (hpair : IsKQuasiPair Ω Ωs K) {c : ℝ}
    (hc : 0 < c) (b : ℂ) {w : ℂ} (hw : w ∈ Ω) :
    slabTop ((fun z => (c : ℂ) * z + b) '' Ω) ((fun z => (c : ℂ) * z + b) '' Ωs)
      ((c : ℂ) * w + b) = slabTop Ω Ωs w := by
  have hΩ := s02_jordanPair_riemannMap (s03_b0_jordanPair hpair)
  have hΩs := s02_jordanPair_riemannMap (s03_b0_jordanPair (s03_qce_swap hpair))
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hnc : ‖(c : ℂ)‖ = c := by rw [Complex.norm_real, Real.norm_of_nonneg hc.le]
  show sInf _ = sInf _
  congr 1
  ext τ
  refine and_congr_right fun _ => ?_
  rw [s04_tg_geod hΩ hc b hw τ]
  constructor
  · rintro ⟨z', ⟨z, hz, rfl⟩, he⟩
    refine ⟨z, hz, ?_⟩
    beta_reduce at he
    rw [subsec_epstein_natural_affine hΩs hc' hz, hnc] at he
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 he
    exact Prod.ext (mul_left_cancel₀ hc' (add_right_cancel h1)) (mul_left_cancel₀ hc.ne' h2)
  · rintro ⟨z, hz, he⟩
    refine ⟨(c : ℂ) * z + b, mem_image_of_mem _ hz, ?_⟩
    rw [subsec_epstein_natural_affine hΩs hc' hz, hnc, he]

/-- T43 G0: `‖T‖_{C^j(E)}` only depends on `T` near `E`. -/
theorem s04_tg_cjlocal (Ω : Set ℂ) {k : ℕ} {T T' : TensorField k} {V E : Set ℂ} (hV : IsOpen V)
    (hEV : E ⊆ V) (h : ∀ w ∈ V, ∀ u : Fin k → ℂ, T w u = T' w u) (j : ℕ) :
    rhoCjNorm Ω j T E = rhoCjNorm Ω j T' E := by
  unfold rhoCjNorm
  refine iSup_congr fun i => iSup_congr fun _ => iSup_congr fun w => iSup_congr fun hw => ?_
  unfold rhoTensorNorm
  simp only [s04_tg_covloc Ω hV i h w (hEV hw)]

/-- T43 G0: `E(v, τ) ∉ Σ*` for `τ ≤ 0` (`E(v, τ) ∈ B_v ⊆ U`, `X*(z) ∈ B*_z ⊆ U*`,
`U ∩ U* = ∅` by `prop_separation_b`). -/
theorem s04_tg_pos {K : ℝ} {Ω Ωs : Set ℂ} (hpair : IsKQuasiPair Ω Ωs K)
    (hnl : ¬ IsLinePair Ω Ωs) {v : ℂ} (hv : v ∈ Ω) {τ : ℝ} (hτ : τ ≤ 0) {z : ℂ} (hz : z ∈ Ωs) :
    epstein Ωs z ≠ normalGeod Ω v τ := by
  have hΓ := s03_b0_jordanPair hpair
  have hΩ := s02_jordanPair_riemannMap hΓ
  have hΩs := s02_jordanPair_riemannMap (s03_b0_jordanPair (s03_qce_swap hpair))
  have hl := s02_poincareDensity_pos hΩ hv
  have hls := s02_poincareDensity_pos hΩs hz
  intro he
  have hB : normalGeod Ω v τ ∈ horoball Ω v := by
    show normalGeod Ω v τ ∈ UHS ∧ horoPhi Ω (normalGeod Ω v τ) v ≤ 1
    refine ⟨s02_normalGeod_pos Ω v hl τ, ?_⟩
    rw [s02_horoPhi_normalGeod Ω v hl τ]
    exact Real.exp_le_one_iff.2 hτ
  have hBs : normalGeod Ω v τ ∈ horoball Ωs z := by
    rw [← he, ← s02_normalGeod_zero Ωs z hls]
    show normalGeod Ωs z 0 ∈ UHS ∧ horoPhi Ωs (normalGeod Ωs z 0) z ≤ 1
    refine ⟨s02_normalGeod_pos Ωs z hls 0, ?_⟩
    rw [s02_horoPhi_normalGeod Ωs z hls 0, Real.exp_zero]
  have h := ((prop_separation_b hΓ hnl).1 v hv z hz).1
  have hm : normalGeod Ω v τ ∈ horoball Ω v ∩ horoball Ωs z := ⟨hB, hBs⟩
  rw [h] at hm
  exact hm

/-- T43 G0: identification of `slabTop`/`slabMap` from a unique hit of `Σ*` in `τ ∈ [0, a]`. -/
theorem s04_tg_ident {Ω Ωs : Set ℂ} {v : ℂ} {t a : ℝ} (ht : 0 < t) (hta : t ≤ a) {z : ℂ}
    (hz : z ∈ Ωs) (heq : epstein Ωs z = normalGeod Ω v t)
    (huniq : ∀ τ ∈ Icc 0 a, ∀ z' ∈ Ωs, epstein Ωs z' = normalGeod Ω v τ → τ = t ∧ z' = z) :
    slabTop Ω Ωs v = t ∧ slabMap Ω Ωs v = z := by
  have hS : IsLeast {τ | 0 < τ ∧ ∃ z ∈ Ωs, epstein Ωs z = normalGeod Ω v τ} t := by
    refine ⟨⟨ht, z, hz, heq⟩, ?_⟩
    rintro τ ⟨hτ, z', hz', he⟩
    rcases le_or_gt t τ with hle | hlt
    · exact hle
    · exact absurd (huniq τ ⟨hτ.le, hlt.le.trans hta⟩ z' hz' he).1 hlt.ne
  have hT : slabTop Ω Ωs v = t := hS.csInf_eq
  refine ⟨hT, ?_⟩
  have hex : ∃ z ∈ Ωs, epstein Ωs z = normalGeod Ω v (slabTop Ω Ωs v) := ⟨z, hz, hT ▸ heq⟩
  unfold slabMap
  simp only [hex, ↓reduceDIte]
  exact (huniq t ⟨ht.le, hta⟩ _ hex.choose_spec.1 (hex.choose_spec.2.trans (by rw [hT]))).2

/-- T43 G0: `N` is an immersion where `X* ∘ N = E ∘ (id, t)` and `E` is one. -/
theorem s04_tg_imm {Ω Ωs : Set ℂ} {N : ℂ → ℂ} {t : ℂ → ℝ} {v : ℂ}
    (hN : DifferentiableAt ℝ N v) (ht : DifferentiableAt ℝ t v)
    (hX : DifferentiableAt ℝ (epstein Ωs) (N v))
    (hEd : DifferentiableAt ℝ (normalMap Ω) (v, t v))
    (heq : (fun x => epstein Ωs (N x)) =ᶠ[𝓝 v] fun x => normalMap Ω (x, t x))
    (hE : Function.Injective (fderiv ℝ (normalMap Ω) (v, t v))) :
    Function.Injective (fderiv ℝ N v) := by
  have h1 : fderiv ℝ (fun x => epstein Ωs (N x)) v =
      (fderiv ℝ (epstein Ωs) (N v)).comp (fderiv ℝ N v) :=
    (hX.hasFDerivAt.comp v hN.hasFDerivAt).fderiv
  have hp : HasFDerivAt (fun x => (x, t x))
      ((ContinuousLinearMap.id ℝ ℂ).prod (fderiv ℝ t v)) v :=
    (hasFDerivAt_id v).prodMk ht.hasFDerivAt
  have h2 : fderiv ℝ (fun x => normalMap Ω (x, t x)) v =
      (fderiv ℝ (normalMap Ω) (v, t v)).comp
        ((ContinuousLinearMap.id ℝ ℂ).prod (fderiv ℝ t v)) := by
    have h2' := hEd.hasFDerivAt.comp v hp
    exact h2'.fderiv
  rw [heq.fderiv_eq, h2] at h1
  rw [injective_iff_map_eq_zero]
  intro h hh
  have h3 := congrArg (fun L => L h) h1
  simp only [ContinuousLinearMap.comp_apply, hh, map_zero, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply] at h3
  have h4 := hE (h3.trans (map_zero _).symm)
  exact congrArg Prod.fst h4

/-- T43 G0: along good parameters, eventually `s < 1/2` on `B_ρ(w n, 3r)` (`s04_tb_good_s`,
`prop_qi`). -/
theorem s04_tg_hs {K : ℝ} {Ω Ωs : ℕ → Set ℂ} {w : ℕ → ℂ} {η R : ℕ → ℝ}
    (hpair : ∀ n, IsKQuasiPair (Ω n) (Ωs n) K) (hnl : ∀ n, ¬ IsLinePair (Ω n) (Ωs n))
    (hgood : ∀ n, IsGoodParam (Ω n) (Ωs n) (η n) (R n) (w n))
    (hη : Tendsto η atTop (𝓝 0)) (hR : Tendsto R atTop atTop) (r : ℝ) :
    ∀ᶠ n in atTop, ∀ w' ∈ Ω n, poincareDist (Ω n) (w n) w' ≤ 3 * r →
      schwarzNorm (Ω n) w' < 1 / 2 := by
  obtain ⟨A, B, hqi⟩ := prop_qi K
  have h1 : ∀ᶠ n in atTop, η n < 1 / 2 := hη.eventually (gt_mem_nhds (by norm_num))
  have h2 : ∀ᶠ n in atTop, 5 / 2 * (3 * r) ≤ R n := hR.eventually (eventually_ge_atTop _)
  filter_upwards [h1, h2] with n hn1 hn2 w' hw' hd
  have hq := ((hqi (Ω n) (Ωs n) (hpair n) (hnl n)).1 (w n) (hgood n).1 w' hw').2
  exact lt_trans ((s04_tb_good_s (hpair n) (hgood n)).1 w' hw'
    (hq.trans ((mul_le_mul_of_nonneg_left hd (by norm_num)).trans hn2))) hn1

/-! ### G1: the two-sided normalized package and the half-plane limit -/

/-- T43 G1 helper: a conformal map onto `𝔻` with vanishing Schwarzian on a domain is the
restriction of a Möbius map whose pole lies off the domain (Theorem 19.1; `ψ` is finite). -/
theorem s04_tg_line_mob {ψ : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D)
    (hψ : IsConformalOnto ψ D unitDisc) (hS : ∀ z ∈ D, schwarzian ψ z = 0) :
    ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧
      ∀ z ∈ D, c * z + d ≠ 0 ∧ ψ z = (a * z + b) / (c * z + d) := by
  have hg : IsConformalOnto (fun w : ℂ => w) D D :=
    ⟨differentiableOn_id, fun x _ y _ h => h, image_id' D⟩
  have hsid : ∀ z, schwarzian (fun w : ℂ => w) z = 0 := fun z => by
    rw [show (fun w : ℂ => w) = fun w => (1 * w + 0) / (0 * w + 1) by funext w; simp]
    exact schwarzian_mobius (by norm_num) z
  have hψa : ∀ z ∈ D, AnalyticAt ℂ ψ z := fun z hz => hψ.1.analyticAt (hD.mem_nhds hz)
  obtain ⟨a, b, c, d, hdet, hfg⟩ := thm19_1_unique hD hDc (isLocUnivMero_of_isConformalOnto hD hψ)
    (isLocUnivMero_of_isConformalOnto hD hg) fun z hz => by rw [hS z hz, hsid z]
  have hfg' : ∀ z ∈ D, c * z + d ≠ 0 → ψ z = (a * z + b) / (c * z + d) := fun z hz hne =>
    hfg z hz (hψa z hz) analyticAt_id hne
  refine ⟨a, b, c, d, hdet, fun z hz => ?_⟩
  by_cases hden : c * z + d = 0
  · -- impossible: `ψ` is continuous at `z`, while the Möbius map has its pole there
    exfalso
    have hc : c ≠ 0 := by
      rintro rfl
      apply hdet
      have hd : d = 0 := by simpa using hden
      rw [hd]
      ring
    have hab : a * z + b ≠ 0 := by
      intro h
      apply hdet
      linear_combination a * hden - c * h
    have hev : ψ =ᶠ[𝓝[≠] z] fun w => (a * w + b) / (c * w + d) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hD.mem_nhds hz)] with y hy hyD
      have hne : c * y + d ≠ 0 := by
        intro h0
        apply hy
        have h3 : c * (y - z) = 0 := by linear_combination h0 - hden
        exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hc)
      exact hfg' y hyD hne
    exact not_continuousAt_mobius_pole hc hden hab hev (hψa z hz).continuousAt
  · exact ⟨hden, hfg' z hz hden⟩

/-- T43 G1 helper: the domain of `s04_tg_line_mob` is `{|az+b| < |cz+d|}`. -/
theorem s04_tg_line_set {ψ : ℂ → ℂ} {D : Set ℂ} (hψ : IsConformalOnto ψ D unitDisc)
    {a b c d : ℂ} (hdet : a * d - b * c ≠ 0)
    (hM : ∀ z ∈ D, c * z + d ≠ 0 ∧ ψ z = (a * z + b) / (c * z + d)) :
    D = {z | ‖a * z + b‖ < ‖c * z + d‖} := by
  ext z
  constructor
  · intro hz
    obtain ⟨hne, he⟩ := hM z hz
    have h1 : ψ z ∈ unitDisc := hψ.2.2 ▸ mem_image_of_mem ψ hz
    rw [he] at h1
    have h1' := mem_ball_zero_iff.1 h1
    rw [norm_div, div_lt_one (norm_pos_iff.2 hne)] at h1'
    exact h1'
  · intro hz
    have hz' : ‖a * z + b‖ < ‖c * z + d‖ := hz
    have hne : c * z + d ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz'
      exact (norm_nonneg _).not_gt hz'
    have hw : (a * z + b) / (c * z + d) ∈ unitDisc := by
      refine mem_ball_zero_iff.2 ?_
      rw [norm_div, div_lt_one (norm_pos_iff.2 hne)]
      exact hz'
    rw [← hψ.2.2] at hw
    obtain ⟨z', hz'D, hψz'⟩ := hw
    obtain ⟨hne', he'⟩ := hM z' hz'D
    rw [he', div_eq_div_iff hne' hne] at hψz'
    have h3 : (a * d - b * c) * (z' - z) = 0 := by linear_combination hψz'
    have hzz : z' = z := sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hdet)
    rw [← hzz]
    exact hz'D

/-- T43 G1 helper: `|az+b|² - |cz+d|²` as a real quadratic polynomial in `z`. -/
theorem s04_tg_line_quad (a b c d z : ℂ) :
    ‖a * z + b‖ ^ 2 - ‖c * z + d‖ ^ 2 = (‖a‖ ^ 2 - ‖c‖ ^ 2) * ‖z‖ ^ 2 +
      2 * ((a * conj b - c * conj d) * z).re + (‖b‖ ^ 2 - ‖d‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re,
    Complex.sub_im]
  ring

/-- T43 G1: a flat limit of the upper side of a `Q`-qc pair through `∞` is a half-plane pair. -/
theorem s04_tg_line {Q : ℝ} {PL HL : ℂ → ℂ} (hPL : IsKQC PL univ Q) (hPLs : PL '' univ = univ)
    (hHL : ∀ z, HL (PL z) = z ∧ PL (HL z) = z) {gL : ℂ → ℂ}
    (hgL : IsConformalOnto gL unitDisc (PL '' upperHalf))
    (hflat : ∀ x ∈ PL '' upperHalf, schwarzian (Function.invFunOn gL unitDisc) x = 0) :
    ∃ α β : ℂ, α ≠ 0 ∧ PL '' upperHalf = {z | 0 < (α * z + β).im} ∧
      PL '' lowerHalf = {z | (α * z + β).im < 0} := by
  have hpair : IsKQuasiPair (PL '' upperHalf) (PL '' lowerHalf) Q := ⟨PL, hPL, hPLs, rfl, rfl⟩
  have _h := hHL
  have hΓ := s03_b0_jordanPair hpair
  have hdisj := s02_jordanPair_disjoint hΓ
  obtain ⟨hunb, hunbs⟩ := s02_jordanPair_unbounded hΓ
  have hDo : IsOpen (PL '' upperHalf) := hgL.isOpen isOpen_ball
  have hDc : IsConnected (PL '' upperHalf) := by
    rw [← hgL.2.2]
    exact ((convex_ball (0 : ℂ) 1).isConnected ⟨0, mem_ball_self one_pos⟩).image _
      hgL.1.continuousOn
  obtain ⟨fs, hfs⟩ := s02_jordanPair_riemannMap (s02_jordanPair_symm hΓ)
  have hDso : IsOpen (PL '' lowerHalf) := hfs.isOpen isOpen_ball
  obtain ⟨a, b, c, d, hdet, hM⟩ := s04_tg_line_mob hDo hDc (hgL.symm isOpen_ball) hflat
  have hDset := s04_tg_line_set (hgL.symm isOpen_ball) hdet hM
  -- `D = {E < 0}` for the real quadratic `E(z) = A|z|² + 2 Re(γ z) + C`
  obtain ⟨A, γ, C, hE⟩ : ∃ (A : ℝ) (γ : ℂ) (C : ℝ), ∀ z, z ∈ PL '' upperHalf ↔
      A * ‖z‖ ^ 2 + 2 * (γ * z).re + C < 0 := by
    refine ⟨‖a‖ ^ 2 - ‖c‖ ^ 2, a * conj b - c * conj d, ‖b‖ ^ 2 - ‖d‖ ^ 2, fun z => ?_⟩
    rw [hDset, ← s04_tg_line_quad, sub_neg]
    show ‖a * z + b‖ < ‖c * z + d‖ ↔ _
    constructor
    · intro h
      nlinarith [norm_nonneg (a * z + b)]
    · intro h
      by_contra hh
      have h' := not_lt.1 hh
      nlinarith [norm_nonneg (c * z + d)]
  have hre : ∀ z : ℂ, |(γ * z).re| ≤ ‖γ‖ * ‖z‖ := fun z => by
    rw [← norm_mul]
    exact Complex.abs_re_le_norm _
  have hD0 : (gL 0) ∈ PL '' upperHalf := hgL.2.2 ▸ mem_image_of_mem gL (mem_ball_self one_pos)
  have hDs0 : PL (-I) ∈ PL '' lowerHalf := mem_image_of_mem PL (by
    show (-I).im < 0
    simp)
  -- `A = 0`: a disc (`A > 0`) is bounded, and the outside of a disc (`A < 0`) has bounded
  -- complement, which cannot contain the unbounded `PL(ℍ⁻)`
  have hA : A = 0 := by
    rcases lt_trichotomy A 0 with hA | hA | hA
    · exfalso
      set R := (2 * ‖γ‖ + |C|) / (-A) + 1 with hR
      obtain ⟨w, hw, hwR⟩ := hunbs 0 R
      rw [sub_zero] at hwR
      have hR1 : 1 ≤ R := by
        rw [hR]
        have : 0 ≤ (2 * ‖γ‖ + |C|) / (-A) := div_nonneg (by positivity) (by linarith)
        linarith
      have hr1 : 1 ≤ ‖w‖ := hR1.trans hwR.le
      have hAR : A * ‖w‖ ≤ -(2 * ‖γ‖ + |C|) + A := by
        have h1 : A * ‖w‖ ≤ A * R := mul_le_mul_of_nonpos_left hwR.le hA.le
        have h2 : A * R = -(2 * ‖γ‖ + |C|) + A := by
          have hA0 : A ≠ 0 := hA.ne
          rw [hR]
          field_simp
        linarith
      have P1 : A * ‖w‖ ^ 2 ≤ ‖w‖ * (-(2 * ‖γ‖ + |C|) + A) := by
        nlinarith [mul_le_mul_of_nonneg_left hAR (norm_nonneg w)]
      have P2 : |C| * 1 ≤ |C| * ‖w‖ := mul_le_mul_of_nonneg_left hr1 (abs_nonneg C)
      have h3 := hre w
      have h4 := le_abs_self C
      have h5 := le_abs_self (γ * w).re
      have hneg : A * ‖w‖ ^ 2 + 2 * (γ * w).re + C < 0 := by
        nlinarith [mul_pos_of_neg_of_neg hA (show -‖w‖ < 0 by linarith)]
      exact Set.disjoint_left.1 hdisj ((hE w).2 hneg) hw
    · exact hA
    · exfalso
      set R := (2 * ‖γ‖ + |C|) / A + 1 with hR
      obtain ⟨w, hw, hwR⟩ := hunb 0 R
      rw [sub_zero] at hwR
      have hR1 : 1 ≤ R := by
        rw [hR]
        have : 0 ≤ (2 * ‖γ‖ + |C|) / A := div_nonneg (by positivity) hA.le
        linarith
      have hr1 : 1 ≤ ‖w‖ := hR1.trans hwR.le
      have hAR : 2 * ‖γ‖ + |C| + A ≤ A * ‖w‖ := by
        have h1 : A * R ≤ A * ‖w‖ := mul_le_mul_of_nonneg_left hwR.le hA.le
        have h2 : A * R = 2 * ‖γ‖ + |C| + A := by
          have hA0 : A ≠ 0 := hA.ne'
          rw [hR]
          field_simp
        linarith
      have P1 : ‖w‖ * (2 * ‖γ‖ + |C| + A) ≤ A * ‖w‖ ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hAR (norm_nonneg w)]
      have P2 : |C| * 1 ≤ |C| * ‖w‖ := mul_le_mul_of_nonneg_left hr1 (abs_nonneg C)
      have h3 := hre w
      have h4 := neg_abs_le C
      have h5 := neg_abs_le (γ * w).re
      have hpos : 0 < A * ‖w‖ ^ 2 + 2 * (γ * w).re + C := by
        nlinarith [mul_pos hA (show (0 : ℝ) < ‖w‖ by linarith)]
      exact absurd ((hE w).1 hw) (not_lt.2 hpos.le)
  -- `γ ≠ 0`: otherwise `D` is empty or everything
  have hγ : γ ≠ 0 := by
    rintro rfl
    have h1 := (hE _).1 hD0
    rw [hA, zero_mul, zero_mul, Complex.zero_re, mul_zero, zero_add, zero_add] at h1
    have h2 : PL (-I) ∈ PL '' upperHalf := by
      rw [hE, hA, zero_mul, zero_mul, Complex.zero_re, mul_zero, zero_add, zero_add]
      exact h1
    exact Set.disjoint_left.1 hdisj h2 hDs0
  have him : ∀ z : ℂ, ((-2 * I * γ) * z + -(I * (C : ℂ))).im = -(2 * (γ * z).re + C) := by
    intro z
    rw [show (-2 * I * γ) * z + -(I * (C : ℂ)) = -(I * (2 * (γ * z) + (C : ℂ))) by ring,
      Complex.neg_im, Complex.I_mul_im, Complex.add_re, Complex.ofReal_re, Complex.mul_re]
    simp
  have hDeq : PL '' upperHalf = {z | 0 < ((-2 * I * γ) * z + -(I * (C : ℂ))).im} := by
    ext z
    rw [hE, hA, zero_mul, zero_add, Set.mem_ofPred_eq, him]
    constructor <;> intro h <;> linarith
  refine ⟨-2 * I * γ, -(I * (C : ℂ)), by simp [hγ], hDeq, ?_⟩
  set α := -2 * I * γ with hα
  set β := -(I * (C : ℂ)) with hβ
  have hα0 : α ≠ 0 := by simp [hα, hγ]
  ext z
  show z ∈ PL '' lowerHalf ↔ (α * z + β).im < 0
  constructor
  · intro hz
    by_contra hz'
    have h0 := not_lt.1 hz'
    rcases h0.lt_or_eq with hlt | heq0
    · exact Set.disjoint_left.1 hdisj (hDeq ▸ hlt) hz
    · -- a point of the line in the open `PL(ℍ⁻)` has points of `D` nearby
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hDso z hz
      have hN : 0 < ‖α‖ := norm_pos_iff.2 hα0
      set s : ℝ := ε / 2 / ‖α‖ with hs
      have hs0 : 0 < s := div_pos (half_pos hε) hN
      have hac : α * conj α = ((‖α‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj']
        push_cast
        ring
      have hz1 : α * (z + (s : ℂ) * (I * conj α)) + β =
          α * z + β + ((s * ‖α‖ ^ 2 : ℝ) : ℂ) * I := by
        rw [show α * (z + (s : ℂ) * (I * conj α)) + β = α * z + β + (s : ℂ) * I * (α * conj α)
          by ring, hac]
        push_cast
        ring
      have hmem : z + (s : ℂ) * (I * conj α) ∈ PL '' upperHalf := by
        rw [hDeq, Set.mem_ofPred_eq, hz1, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, ← heq0]
        simp only [mul_one, zero_mul, add_zero, zero_add]
        positivity
      have hdist : z + (s : ℂ) * (I * conj α) ∈ ball z ε := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_I,
          Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hs0.le, one_mul, hs,
          div_mul_cancel₀ _ hN.ne']
        linarith
      exact Set.disjoint_left.1 hdisj hmem (hball hdist)
  · intro hz
    by_contra hz'
    have hnD : z ∉ PL '' upperHalf := by
      rw [hDeq]
      intro h
      have h' : 0 < (α * z + β).im := h
      linarith
    have hcl := s02_jordanPair_closure hΓ hnD hz'
    have hsub : closure (PL '' upperHalf) ⊆ {z | 0 ≤ (α * z + β).im} := by
      refine closure_minimal (fun x hx => ?_) (isClosed_le continuous_const
        (Complex.continuous_im.comp ((continuous_const.mul continuous_id).add continuous_const)))
      rw [hDeq] at hx
      have hx' : 0 < (α * x + β).im := hx
      exact le_of_lt hx'
    have h1 : 0 ≤ (α * z + β).im := hsub hcl
    linarith

/-- T43 G1 helper: rotating a `K`-q.c. homeomorphism of `ℂ` by `γ⁻¹` keeps it one, and its
inverse is the old inverse after `z ↦ γ z`. -/
theorem s04_tg_seq_rot {F : ℂ → ℂ} {K : ℝ} (hF : IsKQC F univ K) (hs : F '' univ = univ)
    {γ : ℂ} (hγ : γ ≠ 0) :
    IsKQC (fun z => γ⁻¹ * F z) univ K ∧ (fun z => γ⁻¹ * F z) '' univ = univ ∧
      ∀ z, Function.invFunOn (fun z => γ⁻¹ * F z) univ z = Function.invFunOn F univ (γ * z) := by
  have h := td_affine_comp hF hs 0 0 one_ne_zero (inv_ne_zero hγ)
  simp only [one_mul, add_zero] at h
  refine ⟨h.1, h.2, fun z => ?_⟩
  have hinj : Function.Injective (fun z => γ⁻¹ * F z) := fun x y hxy =>
    h.1.2.2.1.2.1 (mem_univ x) (mem_univ y) hxy
  have hz : z ∈ (fun z => γ⁻¹ * F z) '' univ := by rw [h.2]; exact mem_univ z
  have hz' : γ * z ∈ F '' univ := by rw [hs]; exact mem_univ _
  refine hinj ((Function.invFunOn_eq hz).trans ?_)
  show z = γ⁻¹ * F (Function.invFunOn F univ (γ * z))
  rw [Function.invFunOn_eq hz', ← mul_assoc, inv_mul_cancel₀ hγ, one_mul]

/-- T43 G1 helper: `H n (ε n z) → H_L (e z)` locally uniformly when `H n → H_L` locally
uniformly, `H_L` is continuous and `ε n → e`. -/
theorem s04_tg_seq_rinv {H : ℕ → ℂ → ℂ} {HL : ℂ → ℂ} (h : TendstoLocallyUniformly H HL atTop)
    (hc : Continuous HL) {ε : ℕ → ℂ} {e : ℂ} (hε : Tendsto ε atTop (𝓝 e)) :
    TendstoLocallyUniformly (fun n z => H n (ε n * z)) (fun z => HL (e * z)) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto] at h ⊢
  intro x
  have hm : Tendsto (fun y : ℕ × ℂ => (y.1, ε y.1 * y.2)) (atTop ×ˢ 𝓝 x)
      (atTop ×ˢ 𝓝 (e * x)) :=
    tendsto_fst.prodMk ((hε.comp tendsto_fst).mul tendsto_snd)
  have hA : Tendsto (fun y : ℕ × ℂ => (HL (ε y.1 * y.2), H y.1 (ε y.1 * y.2)))
      (atTop ×ˢ 𝓝 x) (uniformity ℂ) := (h (e * x)).comp hm
  have h1 : Tendsto (fun y : ℕ × ℂ => HL (e * y.2)) (atTop ×ˢ 𝓝 x) (𝓝 (HL (e * x))) :=
    (hc.tendsto _).comp (tendsto_const_nhds.mul tendsto_snd)
  have h2 : Tendsto (fun y : ℕ × ℂ => HL (ε y.1 * y.2)) (atTop ×ˢ 𝓝 x) (𝓝 (HL (e * x))) :=
    (hc.tendsto _).comp ((hε.comp tendsto_fst).mul tendsto_snd)
  exact ((h1.prodMk_nhds h2).mono_right (nhds_le_uniformity _)).uniformity_trans hA

/-- T43 G1: the normalized package of `s04_tp_seq`, with the star side (Riemann maps centred
at `0` after the translation by `y₁`) and the half-plane limit pair. -/
theorem s04_tg_seq {K : ℝ} (hK : 1 ≤ K) {Ω Ωs : ℕ → Set ℂ} {w : ℕ → ℂ} {η R : ℕ → ℝ}
    (hpair : ∀ n, IsKQuasiPair (Ω n) (Ωs n) K) (hnl : ∀ n, ¬ IsLinePair (Ω n) (Ωs n))
    (hgood : ∀ n, IsGoodParam (Ω n) (Ωs n) (η n) (R n) (w n))
    (hη : Tendsto η atTop (𝓝 0)) (hR : Tendsto R atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (c : ℕ → ℝ) (b : ℕ → ℂ) (y₁ : ℂ) (g gs : ℕ → ℂ → ℂ)
      (gL gsL : ℂ → ℂ) (α β : ℂ),
      (∀ n, 0 < c n ∧ (c n : ℂ) * w (φ n) + b n = 0) ∧
      (∀ n, IsConformalOnto (g n) unitDisc ((fun z => (c n : ℂ) * z + b n) '' Ω (φ n)) ∧
        g n 0 = 0) ∧
      IsConformalOnto gL unitDisc (gL '' unitDisc) ∧ gL 0 = 0 ∧
      TendstoLocallyUniformlyOn g gL atTop unitDisc ∧
      (∀ S : Set ℂ, IsCompact S → S ⊆ gL '' unitDisc →
        ∀ᶠ n in atTop, S ⊆ (fun z => (c n : ℂ) * z + b n) '' Ω (φ n)) ∧
      (∀ n, IsConformalOnto (gs n) unitDisc
        ((fun z => (c n : ℂ) * z + (b n - y₁)) '' Ωs (φ n)) ∧ gs n 0 = 0) ∧
      IsConformalOnto gsL unitDisc (gsL '' unitDisc) ∧ gsL 0 = 0 ∧
      TendstoLocallyUniformlyOn gs gsL atTop unitDisc ∧
      (∀ S : Set ℂ, IsCompact S → S ⊆ gsL '' unitDisc →
        ∀ᶠ n in atTop, S ⊆ (fun z => (c n : ℂ) * z + (b n - y₁)) '' Ωs (φ n)) ∧
      α ≠ 0 ∧ gL '' unitDisc = {z | 0 < (α * z + β).im} ∧
      gsL '' unitDisc = {z | (α * (z + y₁) + β).im < 0} := by
  obtain ⟨φ1, hφ1, a, b, P, PL, HL, hab, hP, hPL, hPLs, hPL0, hHL, -, hinv⟩ :=
    s03_wc_pairs hK Ω Ωs hpair w fun n => (hgood n).1
  have ha0 : ∀ n, a n ≠ 0 := fun n => (hab n).1
  have hna : ∀ n, (‖a n‖ : ℂ) ≠ 0 := fun n =>
    Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (ha0 n))
  have hεn : ∀ n, a n / (‖a n‖ : ℂ) ≠ 0 := fun n => div_ne_zero (ha0 n) (hna n)
  have hen : ∀ n, ‖a n / (‖a n‖ : ℂ)‖ = 1 := fun n => by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 (ha0 n))]
  obtain ⟨e₀, he₀, φ2, hφ2, he⟩ := (isCompact_sphere (0 : ℂ) 1).tendsto_subseq
    (x := fun n => a n / (‖a n‖ : ℂ)) (fun n => mem_sphere_zero_iff_norm.2 (hen _))
  have he₀1 : ‖e₀‖ = 1 := mem_sphere_zero_iff_norm.1 he₀
  have he₀0 : e₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at he₀1
    exact zero_ne_one he₀1
  have hcont : ∀ n, Continuous (Function.invFunOn (P n) univ) := fun n => by
    have h := (thm7_2_inv (hP n).1).2.2.1.1
    rw [(hP n).2.1] at h
    exact continuousOn_univ.mp h
  have hHLc : Continuous HL := hinv.continuous (Frequently.of_forall hcont)
  -- rotate first, so that both sides are normalized by the same similarity
  have hrot := fun n => s04_tg_seq_rot (hP (φ2 n)).1 (hP (φ2 n)).2.1 (hεn (φ2 n))
  have hrotL := s04_tg_seq_rot hPL hPLs he₀0
  obtain ⟨P', PL', HL', hP'K, hP's, hPL'K, hPL's, hPL'0, hHL', hinv', hP'U, hP'L⟩ :
      ∃ (P' : ℕ → ℂ → ℂ) (PL' HL' : ℂ → ℂ), (∀ n, IsKQC (P' n) univ K) ∧
        (∀ n, P' n '' univ = univ) ∧ IsKQC PL' univ K ∧ PL' '' univ = univ ∧ PL' I = 0 ∧
        (∀ z, HL' (PL' z) = z ∧ PL' (HL' z) = z) ∧
        TendstoLocallyUniformly (fun n => Function.invFunOn (P' n) univ) HL' atTop ∧
        (∀ n, P' n '' upperHalf = (fun z => ((‖a (φ2 n)‖ : ℝ) : ℂ) * z +
          b (φ2 n) / (a (φ2 n) / (‖a (φ2 n)‖ : ℂ))) '' Ω (φ1 (φ2 n))) ∧
        (∀ n, P' n '' lowerHalf = (fun z => ((‖a (φ2 n)‖ : ℝ) : ℂ) * z +
          b (φ2 n) / (a (φ2 n) / (‖a (φ2 n)‖ : ℂ))) '' Ωs (φ1 (φ2 n))) := by
    refine ⟨fun n z => (a (φ2 n) / (‖a (φ2 n)‖ : ℂ))⁻¹ * P (φ2 n) z, fun z => e₀⁻¹ * PL z,
      fun z => HL (e₀ * z), fun n => (hrot n).1, fun n => (hrot n).2.1, hrotL.1, hrotL.2.1, ?_,
      fun z => ⟨?_, ?_⟩, ?_, fun n => ?_, fun n => ?_⟩
    · show e₀⁻¹ * PL I = 0
      rw [hPL0, mul_zero]
    · show HL (e₀ * (e₀⁻¹ * PL z)) = z
      rw [← mul_assoc, mul_inv_cancel₀ he₀0, one_mul, (hHL z).1]
    · show e₀⁻¹ * PL (HL (e₀ * z)) = z
      rw [(hHL _).2, ← mul_assoc, inv_mul_cancel₀ he₀0, one_mul]
    · rw [show (fun n => Function.invFunOn
          (fun z => (a (φ2 n) / (‖a (φ2 n)‖ : ℂ))⁻¹ * P (φ2 n) z) univ) =
          fun n z => Function.invFunOn (P (φ2 n)) univ (a (φ2 n) / (‖a (φ2 n)‖ : ℂ) * z) from
        funext fun n => funext ((hrot n).2.2)]
      exact s04_tg_seq_rinv (s03_wc_tlu_subseq hinv hφ2) hHLc he
    · show (fun z => (a (φ2 n) / (‖a (φ2 n)‖ : ℂ))⁻¹ * P (φ2 n) z) '' upperHalf = _
      rw [show (fun z => (a (φ2 n) / (‖a (φ2 n)‖ : ℂ))⁻¹ * P (φ2 n) z) '' upperHalf =
        (fun y => (a (φ2 n) / (‖a (φ2 n)‖ : ℂ))⁻¹ * y) '' (P (φ2 n) '' upperHalf) by
          rw [image_image], (hP _).2.2.2.1, image_image]
      congr 1
      funext z
      exact (s04_tp_rot (ha0 _) _ z).symm
    · show (fun z => (a (φ2 n) / (‖a (φ2 n)‖ : ℂ))⁻¹ * P (φ2 n) z) '' lowerHalf = _
      rw [show (fun z => (a (φ2 n) / (‖a (φ2 n)‖ : ℂ))⁻¹ * P (φ2 n) z) '' lowerHalf =
        (fun y => (a (φ2 n) / (‖a (φ2 n)‖ : ℂ))⁻¹ * y) '' (P (φ2 n) '' lowerHalf) by
          rw [image_image], (hP _).2.2.2.2, image_image]
      congr 1
      funext z
      exact (s04_tp_rot (ha0 _) _ z).symm
  have hy0 : (0 : ℂ) ∈ PL' '' upperHalf := ⟨I, by show (0 : ℝ) < I.im; simp, hPL'0⟩
  have hy1 : PL' (-I) ∈ PL' '' lowerHalf := mem_image_of_mem _ (show (-I).im < 0 by simp)
  obtain ⟨φ3, hφ3, gs', gsL', hgs', hgsL', hgsL0, hconvs⟩ :=
    s03_wc_riemann_lower hK hP'K hP's hPL'K hPL's hHL' hinv' hy1
  obtain ⟨φ4, hφ4, g', g'L, hg', hg'L, hg'L0, hconv⟩ :=
    s03_wc_riemann hK (fun n => hP'K (φ3 n)) (fun n => hP's (φ3 n)) hPL'K hPL's hHL'
      (s03_wc_tlu_subseq hinv' hφ3) hy0
  obtain ⟨kU, kL, -, -⟩ := s03_wc_kernel hP'K hP's hPL'K hPL's hHL' hinv'
  have hm : StrictMono (fun n => φ3 (φ4 n)) := hφ3.comp hφ4
  have hφ : StrictMono (fun n => φ1 (φ2 (φ3 (φ4 n)))) := hφ1.comp (hφ2.comp hm)
  have hcb : ∀ n, 0 < ‖a (φ2 (φ3 (φ4 n)))‖ ∧
      ((‖a (φ2 (φ3 (φ4 n)))‖ : ℝ) : ℂ) * w (φ1 (φ2 (φ3 (φ4 n)))) +
        b (φ2 (φ3 (φ4 n))) / (a (φ2 (φ3 (φ4 n))) / (‖a (φ2 (φ3 (φ4 n)))‖ : ℂ)) = 0 :=
    fun n => ⟨norm_pos_iff.2 (ha0 _), by rw [s04_tp_rot (ha0 _), (hab _).2, mul_zero]⟩
  have hg : ∀ n, IsConformalOnto (g' n) unitDisc
      ((fun z => ((‖a (φ2 (φ3 (φ4 n)))‖ : ℝ) : ℂ) * z +
        b (φ2 (φ3 (φ4 n))) / (a (φ2 (φ3 (φ4 n))) / (‖a (φ2 (φ3 (φ4 n)))‖ : ℂ))) ''
          Ω (φ1 (φ2 (φ3 (φ4 n))))) ∧ g' n 0 = 0 := fun n => by
    have h := hg' n
    rw [hP'U] at h
    exact h
  have hgL : IsConformalOnto g'L unitDisc (g'L '' unitDisc) := ⟨hg'L.1, hg'L.2.1, rfl⟩
  have hflat := s04_tp_flat hK hpair hnl hgood hη hR hφ hcb hg hgL hconv
  obtain ⟨α, β, hα, hU, hL⟩ := s04_tg_line hPL'K hPL's hHL' hg'L fun x hx =>
    hflat x (by rw [hg'L.2.2]; exact hx)
  have hsL := s04_tn_conf hgsL' one_ne_zero (-PL' (-I))
  simp only [one_mul] at hsL
  refine ⟨fun n => φ1 (φ2 (φ3 (φ4 n))), hφ, fun n => ‖a (φ2 (φ3 (φ4 n)))‖,
    fun n => b (φ2 (φ3 (φ4 n))) / (a (φ2 (φ3 (φ4 n))) / (‖a (φ2 (φ3 (φ4 n)))‖ : ℂ)), PL' (-I),
    g', fun n ζ => gs' (φ4 n) ζ + -PL' (-I), g'L, fun ζ => gsL' ζ + -PL' (-I), α, β, hcb, hg,
    hgL, hg'L0, hconv, ?_, fun n => ?_, ⟨hsL.1, hsL.2.1, rfl⟩, ?_, ?_, ?_, hα, ?_, ?_⟩
  · intro S hS hSD
    have hSV : S ⊆ PL' '' upperHalf := by
      rw [← hg'L.2.2]
      exact hSD
    filter_upwards [hm.tendsto_atTop.eventually (kU S hS hSV)] with n hn
    have h := hn
    rw [hP'U] at h
    exact h
  · have h := s04_tn_conf (hgs' (φ4 n)).1 one_ne_zero (-PL' (-I))
    simp only [one_mul] at h
    have himg : (fun z => ((‖a (φ2 (φ3 (φ4 n)))‖ : ℝ) : ℂ) * z +
        (b (φ2 (φ3 (φ4 n))) / (a (φ2 (φ3 (φ4 n))) / (‖a (φ2 (φ3 (φ4 n)))‖ : ℂ)) - PL' (-I))) ''
          Ωs (φ1 (φ2 (φ3 (φ4 n)))) =
        (fun y => y + -PL' (-I)) '' (P' (φ3 (φ4 n)) '' lowerHalf) := by
      rw [hP'L, image_image]
      congr 1
      funext z
      ring
    refine ⟨?_, ?_⟩
    · rw [himg]
      exact h
    · show gs' (φ4 n) 0 + -PL' (-I) = 0
      rw [(hgs' _).2, add_neg_cancel]
  · show gsL' 0 + -PL' (-I) = 0
    rw [hgsL0, add_neg_cancel]
  · have hu : UniformContinuous (fun y : ℂ => y + -PL' (-I)) :=
      uniformContinuous_id.add uniformContinuous_const
    exact hu.comp_tendstoLocallyUniformlyOn (s04_tp_reidx hconvs hφ4.tendsto_atTop)
  · intro S hS hSD
    have hC : IsCompact ((fun s => s + PL' (-I)) '' S) :=
      hS.image (continuous_id.add continuous_const)
    have hCV : (fun s => s + PL' (-I)) '' S ⊆ PL' '' lowerHalf := by
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨ζ, hζ, hζs⟩ := hSD hs
      rw [← hgsL'.2.2]
      refine ⟨ζ, hζ, ?_⟩
      rw [← hζs]
      show gsL' ζ = gsL' ζ + -PL' (-I) + PL' (-I)
      ring
    filter_upwards [hm.tendsto_atTop.eventually (kL _ hC hCV)] with n hn
    intro s hs
    have hmem := hn (mem_image_of_mem (fun s => s + PL' (-I)) hs)
    rw [hP'L] at hmem
    obtain ⟨z, hz, hzeq⟩ := hmem
    refine ⟨z, hz, ?_⟩
    have hzeq' : ((‖a (φ2 (φ3 (φ4 n)))‖ : ℝ) : ℂ) * z +
        b (φ2 (φ3 (φ4 n))) / (a (φ2 (φ3 (φ4 n))) / (‖a (φ2 (φ3 (φ4 n)))‖ : ℂ)) =
          s + PL' (-I) := hzeq
    show ((‖a (φ2 (φ3 (φ4 n)))‖ : ℝ) : ℂ) * z +
        (b (φ2 (φ3 (φ4 n))) / (a (φ2 (φ3 (φ4 n))) / (‖a (φ2 (φ3 (φ4 n)))‖ : ℂ)) - PL' (-I)) = s
    linear_combination hzeq'
  · rw [← hg'L.2.2] at hU
    exact hU
  · ext z
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      have h : gsL' ζ ∈ PL' '' lowerHalf := by
        rw [← hgsL'.2.2]
        exact mem_image_of_mem _ hζ
      rw [hL] at h
      show (α * (gsL' ζ + -PL' (-I) + PL' (-I)) + β).im < 0
      rw [neg_add_cancel_right]
      exact h
    · intro hz
      have hz' : z + PL' (-I) ∈ PL' '' lowerHalf := by
        rw [hL]
        exact hz
      rw [← hgsL'.2.2] at hz'
      obtain ⟨ζ, hζ, hζe⟩ := hz'
      refine ⟨ζ, hζ, ?_⟩
      show gsL' ζ + -PL' (-I) = z
      rw [hζe, add_neg_cancel_right]

/-! ### G2: convergence of `X` and `E`, and the explicit limit -/

/-- T43 G2: on `U ⋐ D`, `X_n → X_L` and `E_n → E_L` in `C^∞_loc` (stage D data, explicit
smooth formulas in `λ`, `A = conj(∇ log λ)/2`). -/
theorem s04_tg_conv {Ω' : ℕ → Set ℂ} {g : ℕ → ℂ → ℂ} {gL : ℂ → ℂ}
    (hg : ∀ n, IsConformalOnto (g n) unitDisc (Ω' n) ∧ g n 0 = 0)
    (hgL : IsConformalOnto gL unitDisc (gL '' unitDisc)) (hgL0 : gL 0 = 0)
    (hconv : TendstoLocallyUniformlyOn g gL atTop unitDisc)
    (hker : ∀ S : Set ℂ, IsCompact S → S ⊆ gL '' unitDisc → ∀ᶠ n in atTop, S ⊆ Ω' n)
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsCompact (closure U))
    (hUD : closure U ⊆ gL '' unitDisc) :
    ((∀ᶠ n in atTop, ContDiffOn ℝ ∞ (epstein (Ω' n)) U) ∧
      ContDiffOn ℝ ∞ (epstein (gL '' unitDisc)) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (epstein (Ω' n)))
        (iteratedFDeriv ℝ i (epstein (gL '' unitDisc))) atTop U) ∧
    ((∀ᶠ n in atTop, ContDiffOn ℝ ∞
        (fun p : ℂ × ℝ => normalGeod (Ω' n) p.1 p.2) (U ×ˢ univ)) ∧
      ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => normalGeod (gL '' unitDisc) p.1 p.2) (U ×ˢ univ) ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ i (fun p : ℂ × ℝ => normalGeod (Ω' n) p.1 p.2))
        (iteratedFDeriv ℝ i (fun p : ℂ × ℝ => normalGeod (gL '' unitDisc) p.1 p.2))
        atTop (U ×ˢ univ)) := by
  obtain ⟨hmn, -⟩ := s04_td_maps hg hgL hker hUc hUD
  have hl := s04_td_lambda hg hgL hgL0 hconv hker hU hUc hUD
  have hG := s04_td_grad hg hgL hgL0 hconv hker hU hUc hUD
  have hposn : ∀ᶠ n in atTop, ∀ x ∈ U, 0 < poincareDensity (Ω' n) x :=
    hmn.mono fun n hn x hx => s02_poincareDensity_pos ⟨g n, (hg n).1⟩ (hn x hx).1
  have hposL : ∀ x ∈ U, 0 < poincareDensity (gL '' unitDisc) x := fun x hx =>
    s02_poincareDensity_pos ⟨gL, hgL⟩ (hUD (subset_closure hx))
  refine ⟨?_, ?_⟩
  · have hid := s04_tc_const (U := U) (contDiffOn_id (𝕜 := ℝ) (E := ℂ))
    have hP := s04_tc_pair hU hid (s04_tc_pair hU hl hG)
    have hV : IsOpen {p : ℂ × ℝ × ℂ | 0 < p.2.1} :=
      isOpen_lt continuous_const (continuous_fst.comp continuous_snd)
    have hΦ : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ × ℂ =>
        (p.1 + (2 / (p.2.1 ^ 2 + ‖p.2.2‖ ^ 2)) • p.2.2, 2 * p.2.1 / (p.2.1 ^ 2 + ‖p.2.2‖ ^ 2)))
        {p : ℂ × ℝ × ℂ | 0 < p.2.1} := by
      intro p hp
      have hp' : 0 < p.2.1 := hp
      have ha : ContDiffAt ℝ ∞ (fun p : ℂ × ℝ × ℂ => p.1) p := contDiffAt_fst
      have hb : ContDiffAt ℝ ∞ (fun p : ℂ × ℝ × ℂ => p.2.1) p := contDiffAt_snd.fst
      have hc : ContDiffAt ℝ ∞ (fun p : ℂ × ℝ × ℂ => p.2.2) p := contDiffAt_snd.snd
      have hd : ContDiffAt ℝ ∞ (fun p : ℂ × ℝ × ℂ => p.2.1 ^ 2 + ‖p.2.2‖ ^ 2) p :=
        (hb.pow 2).add ((contDiff_norm_sq ℝ).contDiffAt.comp p hc)
      have hne : p.2.1 ^ 2 + ‖p.2.2‖ ^ 2 ≠ 0 :=
        (add_pos_of_pos_of_nonneg (pow_pos hp' 2) (sq_nonneg _)).ne'
      exact ((ha.add ((contDiffAt_const.div hd hne).smul hc)).prodMk
        ((contDiffAt_const.mul hb).div hd hne)).contDiffWithinAt
    have hcomp := s04_tc_comp hU hV (s04_tc_const hΦ) hP
      (hposn.mono fun n hn x hx => hn x hx) fun x hx => hposL x hx
    refine s04_tc_congr hU hcomp (Eventually.of_forall fun n x _ => ?_) fun x _ => ?_
    · exact s04_tg_ep_eq _ x
    · exact s04_tg_ep_eq _ x
  · have hUU : IsOpen (U ×ˢ (univ : Set ℝ)) := hU.prod isOpen_univ
    have hfst := s04_tc_const (U := U ×ˢ (univ : Set ℝ))
      (contDiffOn_fst (s := U ×ˢ (univ : Set ℝ)) (𝕜 := ℝ))
    have hl2 := s04_tc_comp hUU hU hl hfst (Eventually.of_forall fun n p hp => hp.1)
      (fun p hp => hp.1)
    have hG2 := s04_tc_comp hUU hU hG hfst (Eventually.of_forall fun n p hp => hp.1)
      (fun p hp => hp.1)
    have hid := s04_tc_const (U := U ×ˢ (univ : Set ℝ)) (contDiffOn_id (𝕜 := ℝ) (E := ℂ × ℝ))
    have hP := s04_tc_pair hUU hid (s04_tc_pair hUU hl2 hG2)
    have hV : IsOpen {q : (ℂ × ℝ) × ℝ × ℂ | 0 < q.2.1} :=
      isOpen_lt continuous_const (continuous_fst.comp continuous_snd)
    have hΨ : ContDiffOn ℝ ∞ (fun q : (ℂ × ℝ) × ℝ × ℂ =>
        (q.1.1 + (1 / (2 * (‖q.2.2‖ ^ 2 / 4 + (q.2.1 * Real.exp (-q.1.2) / 2) ^ 2))) • q.2.2,
          (q.2.1 * Real.exp (-q.1.2) / 2) /
            (‖q.2.2‖ ^ 2 / 4 + (q.2.1 * Real.exp (-q.1.2) / 2) ^ 2)))
        {q : (ℂ × ℝ) × ℝ × ℂ | 0 < q.2.1} := by
      intro q hq
      have hq' : 0 < q.2.1 := hq
      have hw : ContDiffAt ℝ ∞ (fun q : (ℂ × ℝ) × ℝ × ℂ => q.1.1) q := contDiffAt_fst.fst
      have hτ : ContDiffAt ℝ ∞ (fun q : (ℂ × ℝ) × ℝ × ℂ => q.1.2) q := contDiffAt_fst.snd
      have hb : ContDiffAt ℝ ∞ (fun q : (ℂ × ℝ) × ℝ × ℂ => q.2.1) q := contDiffAt_snd.fst
      have hc : ContDiffAt ℝ ∞ (fun q : (ℂ × ℝ) × ℝ × ℂ => q.2.2) q := contDiffAt_snd.snd
      have he : ContDiffAt ℝ ∞ (fun q : (ℂ × ℝ) × ℝ × ℂ => Real.exp (-q.1.2)) q :=
        Real.contDiff_exp.contDiffAt.comp q hτ.neg
      have hh : ContDiffAt ℝ ∞ (fun q : (ℂ × ℝ) × ℝ × ℂ => q.2.1 * Real.exp (-q.1.2) / 2) q :=
        (hb.mul he).div_const 2
      have hD : ContDiffAt ℝ ∞ (fun q : (ℂ × ℝ) × ℝ × ℂ =>
          ‖q.2.2‖ ^ 2 / 4 + (q.2.1 * Real.exp (-q.1.2) / 2) ^ 2) q :=
        (((contDiff_norm_sq ℝ).contDiffAt.comp q hc).div_const 4).add (hh.pow 2)
      have hh0 : 0 < q.2.1 * Real.exp (-q.1.2) / 2 :=
        div_pos (mul_pos hq' (Real.exp_pos _)) two_pos
      have hDp : 0 < ‖q.2.2‖ ^ 2 / 4 + (q.2.1 * Real.exp (-q.1.2) / 2) ^ 2 :=
        add_pos_of_nonneg_of_pos (by positivity) (pow_pos hh0 2)
      exact ((hw.add ((contDiffAt_const.div (contDiffAt_const.mul hD)
        (mul_pos two_pos hDp).ne').smul hc)).prodMk (hh.div hD hDp.ne')).contDiffWithinAt
    have hcomp := s04_tc_comp hUU hV (s04_tc_const hΨ) hP
      (hposn.mono fun n hn p hp => hn p.1 hp.1) fun p hp => hposL p.1 hp.1
    refine s04_tc_congr hUU hcomp (Eventually.of_forall fun n p _ => ?_) fun p _ => ?_
    · exact s04_tg_ng_eq _ p.1 p.2
    · exact s04_tg_ng_eq _ p.1 p.2

/-- T43 G2: `A = ∂_w log λ` of a half-plane `{0 < σ Im(αz+β)}`. -/
theorem s04_tg_hp_dz (a b : ℂ) (ha : a ≠ 0) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (Ω : Set ℂ)
    (hΩ : ∀ z, z ∈ Ω ↔ 0 < σ * (a * z + b).im) {z : ℂ} (hz : z ∈ Ω) :
    logDensityDz Ω z = I * a / (2 * (((a * z + b).im : ℝ) : ℂ)) := by
  have hΩe : Ω = {z | 0 < σ * (a * z + b).im} := Set.ext hΩ
  have hΩo : IsOpen Ω := by
    rw [hΩe]
    exact isOpen_lt continuous_const (continuous_const.mul
      (Complex.continuous_im.comp ((continuous_const.mul continuous_id).add continuous_const)))
  have hlam := (s02_halfplane a b ha σ hσ Ω hΩ).2
  have hu : 0 < σ * (a * z + b).im := (hΩ z).1 hz
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have ht0 : (a * z + b).im ≠ 0 := by
    intro h
    rw [h, mul_zero] at hu
    exact lt_irrefl _ hu
  have hev : (fun x => Real.log (poincareDensity Ω x)) =ᶠ[𝓝 z]
      fun x => Real.log ‖a‖ - Real.log (σ * (a * x + b).im) := by
    filter_upwards [hΩo.mem_nhds hz] with x hx
    have h1 := hlam x hx
    have h2 : 0 < σ * (a * x + b).im := (hΩ x).1 hx
    have h3 : poincareDensity Ω x = ‖a‖ / (σ * (a * x + b).im) := by
      rw [eq_div_iff h2.ne']
      exact h1
    rw [h3, Real.log_div (norm_ne_zero_iff.2 ha) h2.ne']
  have hA : HasFDerivAt (fun x : ℂ => a * x + b) (a • ContinuousLinearMap.id ℝ ℂ) z :=
    ((hasFDerivAt_id z).const_mul a).add_const b
  have him := (Complex.imCLM.hasFDerivAt).comp z hA
  have hlog := ((him.const_mul σ).log hu.ne').const_sub (Real.log ‖a‖)
  have hφ := hlog.congr_of_eventuallyEq hev
  show wirtingerDz _ z = _
  rw [s02_wirtingerDz_eq hφ (c := I * a / (((a * z + b).im : ℝ) : ℂ)) (fun v => ?_)]
  · field_simp
  · simp only [neg_apply, smul_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, Complex.imCLM_apply,
      FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq,
      smul_eq_mul]
    rw [show I * a / (((a * z + b).im : ℝ) : ℂ) * v =
        (((a * z + b).im)⁻¹ : ℝ) * (I * (a * v)) by push_cast; ring, Complex.re_ofReal_mul,
      Complex.I_mul_re]
    field_simp

/-- T43 G2 helper: `λ = |a| / (σ Im(az+b))` on a half-plane (`s02_halfplane`). -/
theorem s04_tg_hp_lam (a b : ℂ) (ha : a ≠ 0) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (Ω : Set ℂ)
    (hΩ : ∀ z, z ∈ Ω ↔ 0 < σ * (a * z + b).im) {z : ℂ} (hz : z ∈ Ω) :
    poincareDensity Ω z = ‖a‖ / (σ * (a * z + b).im) := by
  rw [eq_div_iff ((hΩ z).1 hz).ne']
  exact (s02_halfplane a b ha σ hσ Ω hΩ).2 z hz

/-- T43 G2 helper: `‖A‖² = |a|²/(4 Im²)` for `A = I a/(2 Im)`. -/
theorem s04_tg_hp_normA (a : ℂ) (t : ℝ) :
    ‖I * a / (2 * (t : ℂ))‖ ^ 2 = ‖a‖ ^ 2 / (4 * t ^ 2) := by
  rw [norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_two, one_mul, div_pow, mul_pow, sq_abs]
  norm_num

/-- T43 G2 helper: `conj (I a / (2t)) = -I |a|² / (2 t a)`. -/
theorem s04_tg_hp_conjA {a : ℂ} (ha : a ≠ 0) (t : ℝ) :
    conj (I * a / (2 * (t : ℂ))) = -I * ((‖a‖ ^ 2 : ℝ) : ℂ) / (2 * (t : ℂ) * a) := by
  have hca : conj a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']
    push_cast
    ring
  rw [map_div₀, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat, ← hca]
  field_simp

/-- T43 G2 helper: the Epstein map of a half-plane, `X(z) = (z - I t/a, σ t/|a|)`,
`t = Im(az+b)`. -/
theorem s04_tg_hp_X (a b : ℂ) (ha : a ≠ 0) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (Ω : Set ℂ)
    (hΩ : ∀ z, z ∈ Ω ↔ 0 < σ * (a * z + b).im) {z : ℂ} (hz : z ∈ Ω) :
    epstein Ω z = (z - I * (((a * z + b).im : ℝ) : ℂ) / a, σ * (a * z + b).im / ‖a‖) := by
  have hu : 0 < σ * (a * z + b).im := (hΩ z).1 hz
  have ht0 : (a * z + b).im ≠ 0 := by
    intro h
    rw [h, mul_zero] at hu
    exact lt_irrefl _ hu
  have hN : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hNc : ((‖a‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hN.ne'
  unfold epstein
  rw [s04_tg_hp_dz a b ha σ hσ Ω hΩ hz, s04_tg_hp_lam a b ha σ hσ Ω hΩ hz,
    s04_tg_hp_normA a _, s04_tg_hp_conjA ha]
  generalize (a * z + b).im = t at ht0 hu ⊢
  rcases hσ with rfl | rfl
  · refine Prod.ext ?_ ?_
    · simp only
      push_cast
      field_simp
      ring
    · simp only
      field_simp
      ring
  · refine Prod.ext ?_ ?_
    · simp only
      push_cast
      field_simp
      ring
    · simp only
      field_simp
      ring

/-- T43 G2 helper: the normal geodesics of a half-plane,
`E(z, τ) = (z - 2 I t/(a(1+e^{-2τ})), 2σ t e^{-τ}/(|a|(1+e^{-2τ})))`. -/
theorem s04_tg_hp_E (a b : ℂ) (ha : a ≠ 0) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (Ω : Set ℂ)
    (hΩ : ∀ z, z ∈ Ω ↔ 0 < σ * (a * z + b).im) {z : ℂ} (hz : z ∈ Ω) (τ : ℝ) :
    normalGeod Ω z τ = (z - 2 * I * (((a * z + b).im : ℝ) : ℂ) /
        (a * (((1 + Real.exp (-τ) ^ 2 : ℝ)) : ℂ)),
      2 * σ * (a * z + b).im * Real.exp (-τ) / (‖a‖ * (1 + Real.exp (-τ) ^ 2))) := by
  have hu : 0 < σ * (a * z + b).im := (hΩ z).1 hz
  have ht0 : (a * z + b).im ≠ 0 := by
    intro h
    rw [h, mul_zero] at hu
    exact lt_irrefl _ hu
  have hN : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hNc : ((‖a‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hN.ne'
  have he : 0 < Real.exp (-τ) := Real.exp_pos _
  unfold normalGeod
  rw [s04_tg_hp_dz a b ha σ hσ Ω hΩ hz, s04_tg_hp_lam a b ha σ hσ Ω hΩ hz,
    s04_tg_hp_normA a _, s04_tg_hp_conjA ha]
  generalize (a * z + b).im = t at ht0 hu ⊢
  generalize Real.exp (-τ) = e at he ⊢
  have hq : (0 : ℝ) < 1 + e ^ 2 := by positivity
  have hqc : (1 + (e : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hq.ne'
  have hq4 : (4 + (e : ℂ) ^ 2 * 4) ≠ 0 := by
    rw [show (4 + (e : ℂ) ^ 2 * 4) = 4 * (1 + (e : ℂ) ^ 2) by ring]
    exact mul_ne_zero (by norm_num) hqc
  rcases hσ with rfl | rfl
  · refine Prod.ext ?_ ?_
    · simp only
      push_cast
      field_simp
      ring_nf
      field_simp
      ring
    · simp only
      field_simp
      ring
  · refine Prod.ext ?_ ?_
    · simp only
      push_cast
      field_simp
      ring_nf
      field_simp
      ring
    · simp only
      field_simp
      ring

/-- T43 G2 helper: the upper side `{0 < Im(αz+β)}` in the form of `s02_halfplane` (`σ = 1`). -/
theorem s04_tg_hp_up (α β : ℂ) :
    ∀ x, x ∈ {z | 0 < (α * z + β).im} ↔ 0 < (1 : ℝ) * (α * x + β).im := fun x => by
  rw [one_mul]
  rfl

/-- T43 G2 helper: the lower side `{Im(αz+β) < 0}` in the form of `s02_halfplane` (`σ = -1`). -/
theorem s04_tg_hp_low (α β : ℂ) :
    ∀ x, x ∈ {z | (α * z + β).im < 0} ↔ 0 < (-1 : ℝ) * (α * x + β).im := fun x => by
  rw [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

/-- T43 G2: the limit equation: `E_L(v, τ) = X*_L(z)` iff `τ = 0` and `z = v̄`. -/
theorem s04_tg_lim_eq {α β : ℂ} (hα : α ≠ 0) {v : ℂ} (hv : 0 < (α * v + β).im) (τ : ℝ) {z : ℂ}
    (hz : (α * z + β).im < 0) :
    normalGeod {z | 0 < (α * z + β).im} v τ = epstein {z | (α * z + β).im < 0} z ↔
      τ = 0 ∧ z = v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α := by
  rw [s04_tg_hp_E α β hα 1 (Or.inl rfl) _ (s04_tg_hp_up α β) hv τ,
    s04_tg_hp_X α β hα (-1) (Or.inr rfl) _ (s04_tg_hp_low α β) hz]
  have hN : 0 < ‖α‖ := norm_pos_iff.2 hα
  have he : 0 < Real.exp (-τ) := Real.exp_pos _
  have hq : 0 < 1 + Real.exp (-τ) ^ 2 := by positivity
  have hqc : (1 + (Real.exp (-τ) : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hq.ne'
  constructor
  · intro h
    rw [Prod.ext_iff] at h
    obtain ⟨h1, h2⟩ := h
    simp only at h1 h2
    generalize hs : (α * z + β).im = s at h1 h2
    generalize ht : (α * v + β).im = t at hv h1 h2 ⊢
    have h1z : z = v - 2 * I * (t : ℂ) / (α * ((1 + Real.exp (-τ) ^ 2 : ℝ) : ℂ)) +
        I * (s : ℂ) / α := by
      linear_combination -h1
    have h5 : α * z + β = (α * v + β) + (((s - 2 * t / (1 + Real.exp (-τ) ^ 2) : ℝ)) : ℂ) * I := by
      rw [h1z]
      push_cast
      field_simp
      ring
    have h4 : (α * z + β).im = t - 2 * t / (1 + Real.exp (-τ) ^ 2) + s := by
      rw [h5, Complex.add_im, ht, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    rw [hs] at h4
    have h6 : t * (1 + Real.exp (-τ) ^ 2) = t * 2 := by
      have h7 : 2 * t / (1 + Real.exp (-τ) ^ 2) = t := by linarith
      rw [div_eq_iff hq.ne'] at h7
      linarith
    have hq2 : 1 + Real.exp (-τ) ^ 2 = 2 := mul_left_cancel₀ hv.ne' h6
    have he1 : Real.exp (-τ) = 1 := by nlinarith
    have hτ : τ = 0 := neg_eq_zero.1 ((Real.exp_eq_one_iff _).1 he1)
    refine ⟨hτ, ?_⟩
    rw [he1] at h2
    have hs' : s = -t := by
      field_simp at h2
      linarith
    rw [h1z, hs', he1]
    push_cast
    field_simp
    ring
  · rintro ⟨rfl, rfl⟩
    have hrefl : (α * (v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α) + β).im = -(α * v + β).im := by
      have h : α * (v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α) + β =
          α * v + β - (((2 * (α * v + β).im : ℝ) : ℂ)) * I := by
        push_cast
        field_simp
        ring
      rw [h, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im]
      ring
    rw [hrefl]
    generalize (α * v + β).im = t at hv ⊢
    simp only [neg_zero, Real.exp_zero]
    have hNc : ((‖α‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hN.ne'
    refine Prod.ext ?_ ?_
    · simp only
      push_cast
      field_simp
      ring
    · simp only
      field_simp
      ring

/-- T43 G2: the reflection `v̄` lies on the other side. -/
theorem s04_tg_lim_refl {α β : ℂ} (hα : α ≠ 0) (v : ℂ) :
    (α * (v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α) + β).im = -(α * v + β).im := by
  have h : α * (v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α) + β =
      α * v + β - (((2 * (α * v + β).im : ℝ) : ℂ)) * I := by
    push_cast
    field_simp
    ring
  rw [h, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

/-- T43 G2: transversality in the limit: the derivative of `(τ, z) ↦ E_L(v, τ) - X*_L(z)` at
`(0, v̄)` is invertible. -/
theorem s04_tg_lim_inv {α β : ℂ} (hα : α ≠ 0) {v : ℂ} (hv : 0 < (α * v + β).im) :
    ∃ e : (ℝ × ℂ) ≃L[ℝ] (ℂ × ℝ), (e : ℝ × ℂ →L[ℝ] ℂ × ℝ) =
      fderiv ℝ (fun y : ℝ × ℂ => normalGeod {z | 0 < (α * z + β).im} v y.1 -
        epstein {z | (α * z + β).im < 0} y.2) (0, v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α) := by
  have hN : 0 < ‖α‖ := norm_pos_iff.2 hα
  have hl := s04_tg_hp_lam α β hα 1 (Or.inl rfl) _ (s04_tg_hp_up α β) hv
  have hlpos : 0 < poincareDensity {z | 0 < (α * z + β).im} v := by
    rw [hl, one_mul]
    exact div_pos hN hv
  -- `∂_τ E_L(v, 0) = (-I t/α, 0)`
  have hτ : HasDerivAt (fun τ : ℝ => normalGeod {z | 0 < (α * z + β).im} v τ)
      (-I * (((α * v + β).im : ℝ) : ℂ) / α, (0 : ℝ)) 0 := by
    refine (s02_hasDerivAt_normalGeod _ v hlpos).congr_deriv ?_
    rw [hl, s04_tg_hp_dz α β hα 1 (Or.inl rfl) _ (s04_tg_hp_up α β) hv,
      s04_tg_hp_normA α _, s04_tg_hp_conjA hα]
    generalize (α * v + β).im = t at hv ⊢
    have hNc : ((‖α‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hN.ne'
    refine Prod.ext ?_ ?_
    · simp only
      push_cast
      field_simp
      ring
    · simp only
      field_simp
      ring
  -- `X*_L` near `v̄` is affine
  have hw := s04_tg_lim_refl (β := β) hα v
  have hwl : v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α ∈ {z | (α * z + β).im < 0} := by
    rw [Set.mem_ofPred_eq, hw]
    linarith
  have hlo : IsOpen {z : ℂ | (α * z + β).im < 0} :=
    isOpen_lt (Complex.continuous_im.comp ((continuous_const.mul continuous_id).add
      continuous_const)) continuous_const
  have heq : epstein {z | (α * z + β).im < 0} =ᶠ[𝓝 (v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α)]
      fun x => (x - I / α * (((α * x + β).im : ℝ) : ℂ), -1 / ‖α‖ * (α * x + β).im) := by
    filter_upwards [hlo.mem_nhds hwl] with x hx
    rw [s04_tg_hp_X α β hα (-1) (Or.inr rfl) _ (s04_tg_hp_low α β) hx]
    refine Prod.ext ?_ ?_
    · simp only
      ring
    · simp only
      ring
  have hA : ∀ x : ℂ, HasFDerivAt (fun x : ℂ => α * x + β) (α • ContinuousLinearMap.id ℝ ℂ) x :=
    fun x => ((hasFDerivAt_id x).const_mul α).add_const β
  have him := fun x => (Complex.imCLM.hasFDerivAt).comp x (hA x)
  have hX := (((hasFDerivAt_id (v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α)).sub
    ((Complex.ofRealCLM.hasFDerivAt.comp _ (him _)).const_mul (I / α))).prodMk
    ((him _).const_mul (-1 / ‖α‖))).congr_of_eventuallyEq heq
  have hF0 := (hτ.hasFDerivAt.comp ((0 : ℝ), v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α)
    hasFDerivAt_fst).sub (hX.comp (f := Prod.snd) ((0 : ℝ),
      v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α) hasFDerivAt_snd)
  have hF : HasFDerivAt (fun y : ℝ × ℂ =>
      normalGeod {z | 0 < (α * z + β).im} v y.1 - epstein {z | (α * z + β).im < 0} y.2) _
      ((0 : ℝ), v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α) := hF0
  have hinj : Function.Injective (fderiv ℝ (fun y : ℝ × ℂ =>
      normalGeod {z | 0 < (α * z + β).im} v y.1 - epstein {z | (α * z + β).im < 0} y.2)
      (0, v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α)) := by
    rw [hF.fderiv, injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨δ, h⟩ := x
    have h2 : (α * h).im = 0 := by
      have h3 := congrArg Prod.snd hx
      simp at h3
      rw [Complex.mul_im]
      exact h3.resolve_left hα
    have h1 : (δ : ℂ) * (-I * (((α * v + β).im : ℝ) : ℂ) / α) -
        (h - I / α * (((α * h).im : ℝ) : ℂ)) = 0 := by
      simpa using congrArg Prod.fst hx
    rw [h2, Complex.ofReal_zero, mul_zero, sub_zero] at h1
    have hh : h = (δ : ℂ) * (-I * (((α * v + β).im : ℝ) : ℂ) / α) := by
      linear_combination -h1
    have hah : α * h = (((-(δ * (α * v + β).im)) : ℝ) : ℂ) * I := by
      rw [hh]
      push_cast
      field_simp
    rw [hah, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im] at h2
    have hδ : δ = 0 := by
      have h4 : δ * (α * v + β).im = 0 := by linarith
      rcases mul_eq_zero.1 h4 with h5 | h5
      · exact h5
      · exact absurd h5 hv.ne'
    rw [hh, hδ]
    simp
  have hdim : Module.finrank ℝ (ℝ × ℂ) = Module.finrank ℝ (ℂ × ℝ) := by
    rw [Module.finrank_prod, Module.finrank_prod, add_comm]
  refine ⟨(LinearMap.linearEquivOfInjective _ hinj hdim).toContinuousLinearEquiv, ?_⟩
  exact ContinuousLinearMap.ext fun x => rfl

/-- T43 G2: `Φ*_{E_L(v, τ)}(v̄) = e^{-τ}`. -/
theorem s04_tg_lim_horo {α β : ℂ} (hα : α ≠ 0) {v : ℂ} (hv : 0 < (α * v + β).im) (τ : ℝ) :
    horoPhi {z | (α * z + β).im < 0} (normalGeod {z | 0 < (α * z + β).im} v τ)
      (v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α) = Real.exp (-τ) := by
  have hw := s04_tg_lim_refl (β := β) hα v
  have hwl : v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α ∈ {z | (α * z + β).im < 0} := by
    rw [Set.mem_ofPred_eq]
    rw [hw]
    linarith
  show poincareDensity _ _ * _ / _ = _
  rw [s04_tg_hp_E α β hα 1 (Or.inl rfl) _ (s04_tg_hp_up α β) hv τ,
    s04_tg_hp_lam α β hα (-1) (Or.inr rfl) _ (s04_tg_hp_low α β) hwl, hw]
  simp only
  generalize (α * v + β).im = t at hv ⊢
  have he := Real.exp_pos (-τ)
  generalize Real.exp (-τ) = e at he ⊢
  have hN : 0 < ‖α‖ := norm_pos_iff.2 hα
  have hq : 0 < 1 + e ^ 2 := by positivity
  have hqc : (1 + (e : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hq.ne'
  have hdiff : v - 2 * I * (t : ℂ) / (α * ((1 + e ^ 2 : ℝ) : ℂ)) - (v - 2 * I * (t : ℂ) / α) =
      ((2 * t * e ^ 2 / (1 + e ^ 2) : ℝ) : ℂ) * (I / α) := by
    push_cast
    field_simp
    ring
  rw [hdiff, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_div,
    Complex.norm_I]
  field_simp
  ring

/-! ### G3: the parametric implicit function theorem with `C^∞_loc` convergence -/

/-- T43 G3 helper: restriction of a `C^∞_loc` convergence triple to a smaller set. -/
theorem s04_tg_ift_mono {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U U' : Set E} {f : ℕ → E → F} {fL : E → F}
    (hf : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) U) ∧ ContDiffOn ℝ ∞ fL U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (f n))
        (iteratedFDeriv ℝ i fL) atTop U) (h : U' ⊆ U) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) U') ∧ ContDiffOn ℝ ∞ fL U' ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (f n))
        (iteratedFDeriv ℝ i fL) atTop U' :=
  ⟨hf.1.mono fun _ hn => hn.mono h, hf.2.1.mono h, fun i => (hf.2.2 i).mono h⟩

/-- T43 G3 helper: order `0` from convergence of the maps. -/
theorem s04_tg_ift_zero {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} {f : ℕ → E → F} {fL : E → F}
    (h : TendstoLocallyUniformlyOn f fL atTop U) :
    TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ 0 (f n))
      (iteratedFDeriv ℝ 0 fL) atTop U := by
  have hT := (continuousMultilinearCurryFin0 ℝ E F).symm.isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn h
  refine (hT.congr fun n y _ => ?_).congr_right fun y _ => ?_
  · rw [iteratedFDeriv_zero_eq_comp]
  · rw [iteratedFDeriv_zero_eq_comp]

/-- T43 G3 helper: order `k` of `fderiv f` is order `k + 1` of `f` (a linear isometry). -/
theorem s04_tg_ift_succ {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} {f : ℕ → E → F} {fL : E → F} (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ k (fderiv ℝ (f n)))
        (iteratedFDeriv ℝ k (fderiv ℝ fL)) atTop U ↔
      TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ (k + 1) (f n))
        (iteratedFDeriv ℝ (k + 1) fL) atTop U := by
  constructor
  · intro h
    have hT := (continuousMultilinearCurryRightEquiv' ℝ k E F).symm.isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn h
    refine (hT.congr fun n y _ => ?_).congr_right fun y _ => ?_
    · simp [iteratedFDeriv_succ_eq_comp_right]
    · simp [iteratedFDeriv_succ_eq_comp_right]
  · intro h
    have hT := (continuousMultilinearCurryRightEquiv' ℝ k E F).isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn h
    refine (hT.congr fun n y _ => ?_).congr_right fun y _ => ?_
    · simp [iteratedFDeriv_succ_eq_comp_right]
    · simp [iteratedFDeriv_succ_eq_comp_right]

/-- T43 G3 helper: the graph map `v ↦ (v, y v)`, orders `≤ i`. -/
theorem s04_tg_ift_graph {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {y : ℕ → E → F}
    {yL : E → F} (hy1 : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (y n) U) (hy2 : ContDiffOn ℝ ∞ yL U)
    (i : ℕ) (hy3 : ∀ k ≤ i, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ k (y n))
      (iteratedFDeriv ℝ k yL) atTop U) :
    ∀ k ≤ i, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ k (fun x => (x, y n x)))
      (iteratedFDeriv ℝ k (fun x => (x, yL x))) atTop U := by
  intro k hk
  have hid : ContDiffOn ℝ ∞ (fun x : E => ContinuousLinearMap.inl ℝ E F x) U :=
    (ContinuousLinearMap.inl ℝ E F).contDiff.contDiffOn
  have h1 := s04_tc_clm_ord hU (ContinuousLinearMap.inr ℝ E F) hy1 hy2 k (hy3 k hk)
  have h0 := (s04_tc_const (U := U) hid).2.2 k
  have hT := uniformContinuous_add.comp_tendstoLocallyUniformlyOn (h0.prodMk h1)
  refine s04_tc_evcongr hT (hy1.mono fun n hn x hx => ?_) (fun x hx => ?_)
  · have hc : ContDiffOn ℝ ∞ (fun x => ContinuousLinearMap.inr ℝ E F (y n x)) U :=
      (ContinuousLinearMap.inr ℝ E F).contDiff.comp_contDiffOn hn
    have hfun : (fun x => (x, y n x)) = (fun x => ContinuousLinearMap.inl ℝ E F x) +
        (fun x => ContinuousLinearMap.inr ℝ E F (y n x)) := by
      funext z
      simp
    show _ = iteratedFDeriv ℝ k (fun x => (x, y n x)) x
    rw [hfun, iteratedFDeriv_add_apply (s04_tc_at hU hid hx k) (s04_tc_at hU hc hx k)]
    rfl
  · have hc : ContDiffOn ℝ ∞ (fun x => ContinuousLinearMap.inr ℝ E F (yL x)) U :=
      (ContinuousLinearMap.inr ℝ E F).contDiff.comp_contDiffOn hy2
    have hfun : (fun x => (x, yL x)) = (fun x => ContinuousLinearMap.inl ℝ E F x) +
        (fun x => ContinuousLinearMap.inr ℝ E F (yL x)) := by
      funext z
      simp
    show _ = iteratedFDeriv ℝ k (fun x => (x, yL x)) x
    rw [hfun, iteratedFDeriv_add_apply (s04_tc_at hU hid hx k) (s04_tc_at hU hc hx k)]
    rfl

/-- T43 G3 helper: composition when the inner maps converge only up to order `i`. -/
theorem s04_tg_ift_comp {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} {V : Set F} (hU : IsOpen U)
    (hV : IsOpen V) {Gn : ℕ → E → F} {Gl : E → F}
    (hG1 : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (Gn n) U) (hG2 : ContDiffOn ℝ ∞ Gl U)
    (hmaps : ∀ᶠ n in atTop, MapsTo (Gn n) U V) (hmapsL : MapsTo Gl U V) (i : ℕ) :
    ∀ (H : Type u) [NormedAddCommGroup H] [NormedSpace ℝ H] (Fn : ℕ → F → H) (Fl : F → H),
      ((∀ᶠ n in atTop, ContDiffOn ℝ ∞ (Fn n) V) ∧ ContDiffOn ℝ ∞ Fl V ∧
        ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (Fn n))
          (iteratedFDeriv ℝ i Fl) atTop V) →
      (∀ k ≤ i, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ k (Gn n))
        (iteratedFDeriv ℝ k Gl) atTop U) →
      ∀ k ≤ i, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ k (fun x => Fn n (Gn n x)))
        (iteratedFDeriv ℝ k (fun x => Fl (Gl x))) atTop U := by
  induction i with
  | zero =>
    intro H _ _ Fn Fl hF hG k hk
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    have h0 : TendstoLocallyUniformlyOn (fun n x => Fn n (Gn n x)) (fun x => Fl (Gl x))
        atTop U := by
      refine (s04_tc_cc (f := fun x => Fl (Gl x))
        (hF.2.1.continuousOn.comp hG2.continuousOn hmapsL)).2 fun x hx => ?_
      have hFc := (s04_tc_cc hF.2.1.continuousOn).1 (s04_tc_zero (hF.2.2 0)) (Gl x) (hmapsL hx)
      have hGc := (s04_tc_cc hG2.continuousOn).1 (s04_tc_zero (hG 0 le_rfl)) x hx
      have hGV : Tendsto (fun q : ℕ × E => Gn q.1 q.2) (atTop ×ˢ 𝓝[U] x) (𝓝[V] (Gl x)) :=
        tendsto_nhdsWithin_iff.2 ⟨hGc,
          (hmaps.prod_mk (eventually_mem_nhdsWithin (s := U) (a := x))).mono
            fun q hq => hq.1 hq.2⟩
      exact hFc.comp (tendsto_fst.prodMk hGV)
    exact s04_tg_ift_zero h0
  | succ i ih =>
    intro H _ _ Fn Fl hF hG k hk
    rcases Nat.lt_or_ge k (i + 1) with hlt | hge
    · exact ih H Fn Fl hF (fun k hk => hG k (hk.trans (Nat.le_succ i))) k
        (Nat.lt_succ_iff.1 hlt)
    obtain rfl : k = i + 1 := le_antisymm hk hge
    have hDF := s04_tc_fderiv hV hF
    have hDG1 : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fderiv ℝ (Gn n)) U :=
      hG1.mono fun n hn => hn.fderiv_of_isOpen hU (by simp)
    have hDG2 : ContDiffOn ℝ ∞ (fderiv ℝ Gl) U := hG2.fderiv_of_isOpen hU (by simp)
    have hDG3 : ∀ k ≤ i, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ k (fderiv ℝ (Gn n)))
        (iteratedFDeriv ℝ k (fderiv ℝ Gl)) atTop U := fun k hk =>
      (s04_tg_ift_succ k).2 (hG (k + 1) (Nat.succ_le_succ hk))
    have hih := ih (F →L[ℝ] H) (fun n => fderiv ℝ (Fn n)) (fderiv ℝ Fl) hDF
      (fun k hk => hG k (hk.trans (Nat.le_succ i)))
    have hev := (hF.1.and hG1).and hmaps
    have hu1 : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fun x => fderiv ℝ (Fn n) (Gn n x)) U :=
      ((hDF.1.and hG1).and hmaps).mono fun n hn => hn.1.1.comp hn.1.2 hn.2
    have hu2 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ Fl (Gl x)) U :=
      hDF.2.1.comp hG2 hmapsL
    have hord := s04_tc_bilin_ord hU (ContinuousLinearMap.compL ℝ E F H) hu1 hu2 hDG1 hDG2 i
      hih hDG3
    have hT := (continuousMultilinearCurryRightEquiv' ℝ i E H).symm.isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn hord
    have hEq : ∀ {Fa : F → H} {Ga : E → F}, ContDiffOn ℝ ∞ Fa V → ContDiffOn ℝ ∞ Ga U →
        MapsTo Ga U V → EqOn (fderiv ℝ (fun x => Fa (Ga x)))
          (fun z => ContinuousLinearMap.compL ℝ E F H (fderiv ℝ Fa (Ga z)) (fderiv ℝ Ga z)) U := by
      intro Fa Ga hFa hGa hm z hz
      show fderiv ℝ (Fa ∘ Ga) z = (fderiv ℝ Fa (Ga z)).comp (fderiv ℝ Ga z)
      exact fderiv_comp z ((s04_tc_at hV hFa (hm hz) 1).differentiableAt (by simp))
        ((s04_tc_at hU hGa hz 1).differentiableAt (by simp))
    refine s04_tc_evcongr hT (hev.mono fun n hn y hy => ?_) (fun y hy => ?_)
    · rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, Function.comp_apply]
      exact congrArg _ (s04_tc_eqOn hU (hEq hn.1.1 hn.1.2 hn.2) i hy).symm
    · rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, Function.comp_apply]
      exact congrArg _ (s04_tc_eqOn hU (hEq hF.2.1 hG2 hmapsL) i hy).symm

/-- T43 G3 helper: the partial derivative in the second variable. -/
theorem s04_tg_ift_slice {P Y Z : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {G : P × Y → Z} {v : P} {y : Y} (hG : DifferentiableAt ℝ G (v, y)) :
    fderiv ℝ (fun y' => G (v, y')) y = fderiv ℝ G (v, y) ∘L ContinuousLinearMap.inr ℝ P Y :=
  (hG.hasFDerivAt.comp y (hasFDerivAt_prodMk_right v y)).fderiv

/-- T43 G3 helper: the derivative of an implicit solution. -/
theorem s04_tg_ift_deriv {P Y Z : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {G : P × Y → Z} {φ : P → Y} {v : P} (hφ : DifferentiableAt ℝ φ v)
    (hG : DifferentiableAt ℝ G (v, φ v)) (h0 : ∀ᶠ x in 𝓝 v, G (x, φ x) = 0)
    (hinv : (fderiv ℝ G (v, φ v) ∘L ContinuousLinearMap.inr ℝ P Y).IsInvertible) :
    fderiv ℝ φ v = -(fderiv ℝ G (v, φ v) ∘L ContinuousLinearMap.inr ℝ P Y).inverse ∘L
      (fderiv ℝ G (v, φ v) ∘L ContinuousLinearMap.inl ℝ P Y) := by
  have hc : HasFDerivAt (fun x => G (x, φ x))
      (fderiv ℝ G (v, φ v) ∘L ((ContinuousLinearMap.id ℝ P).prod (fderiv ℝ φ v))) v :=
    hG.hasFDerivAt.comp v ((hasFDerivAt_id v).prodMk hφ.hasFDerivAt)
  have hz : HasFDerivAt (fun x => G (x, φ x)) (0 : P →L[ℝ] Z) v :=
    (hasFDerivAt_const (0 : Z) v).congr_of_eventuallyEq h0
  have he := hc.unique hz
  obtain ⟨e, hee⟩ := hinv
  rw [← hee, ContinuousLinearMap.inverse_equiv]
  ext h
  have h1 := congrArg (fun T : P →L[ℝ] Z => T h) he
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_id', id_eq, zero_apply] at h1
  have h2 : fderiv ℝ G (v, φ v) (h, fderiv ℝ φ v h) =
      fderiv ℝ G (v, φ v) (ContinuousLinearMap.inl ℝ P Y h) +
        fderiv ℝ G (v, φ v) (ContinuousLinearMap.inr ℝ P Y (fderiv ℝ φ v h)) := by
    rw [← map_add]
    simp
  have h3 : e (fderiv ℝ φ v h) = -(fderiv ℝ G (v, φ v) (ContinuousLinearMap.inl ℝ P Y h)) := by
    have h4 : (e : Y →L[ℝ] Z) (fderiv ℝ φ v h) =
        fderiv ℝ G (v, φ v) (ContinuousLinearMap.inr ℝ P Y (fderiv ℝ φ v h)) := by
      rw [hee]
      rfl
    rw [ContinuousLinearEquiv.coe_coe] at h4
    rw [h4]
    rw [h2] at h1
    exact eq_neg_of_add_eq_zero_right h1
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, neg_apply,
    ContinuousLinearEquiv.coe_coe]
  rw [← map_neg, ← h3, ContinuousLinearEquiv.symm_apply_apply]

/-- T43 G3 helper: a small perturbation of an isomorphism of finite-dimensional spaces is an
isomorphism. -/
theorem s04_tg_ift_inv {Y Z : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (e : Y ≃L[ℝ] Z) {A : Y →L[ℝ] Z} {M c : ℝ} (hM : ‖(e.symm : Z →L[ℝ] Y)‖ ≤ M)
    (hc : ‖A - (e : Y →L[ℝ] Z)‖ ≤ c) (hMc : M * c < 1) : A.IsInvertible := by
  have hinj : Function.Injective A := by
    intro a b hab
    have hd : ‖a - b‖ ≤ M * c * ‖a - b‖ := by
      have h1 : ‖a - b‖ ≤ M * ‖e (a - b)‖ := by
        calc ‖a - b‖ = ‖(e.symm : Z →L[ℝ] Y) (e (a - b))‖ := by simp
          _ ≤ ‖(e.symm : Z →L[ℝ] Y)‖ * ‖e (a - b)‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ M * ‖e (a - b)‖ := by gcongr
      have h2 : ‖e (a - b)‖ ≤ c * ‖a - b‖ := by
        have h3 : e (a - b) = -((A - (e : Y →L[ℝ] Z)) (a - b)) := by
          simp [map_sub, hab]
        rw [h3, norm_neg]
        exact ((A - (e : Y →L[ℝ] Z)).le_opNorm _).trans (by gcongr)
      have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
      calc ‖a - b‖ ≤ M * ‖e (a - b)‖ := h1
        _ ≤ M * (c * ‖a - b‖) := by gcongr
        _ = M * c * ‖a - b‖ := by ring
    have h0 : ‖a - b‖ = 0 := by
      have := norm_nonneg (a - b)
      nlinarith
    exact sub_eq_zero.1 (norm_eq_zero.1 h0)
  have hdim : Module.finrank ℝ Y = Module.finrank ℝ Z := e.toLinearEquiv.finrank_eq
  exact ⟨(LinearMap.linearEquivOfInjective (A : Y →ₗ[ℝ] Z) hinj hdim).toContinuousLinearEquiv,
    by ext x; rfl⟩

/-- T43 G3 helper: `Ψ(A) = -(A ∘ inr)⁻¹ ∘ (A ∘ inl)` is smooth on the open set where `A ∘ inr`
is invertible. -/
theorem s04_tg_ift_psi (P Y Z : Type u) [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] :
    IsOpen {A : P × Y →L[ℝ] Z | (A ∘L ContinuousLinearMap.inr ℝ P Y).IsInvertible} ∧
      ContDiffOn ℝ ∞ (fun A : P × Y →L[ℝ] Z =>
        -(A ∘L ContinuousLinearMap.inr ℝ P Y).inverse ∘L (A ∘L ContinuousLinearMap.inl ℝ P Y))
        {A : P × Y →L[ℝ] Z | (A ∘L ContinuousLinearMap.inr ℝ P Y).IsInvertible} := by
  have hR : ContDiff ℝ ∞ (fun A : P × Y →L[ℝ] Z => A ∘L ContinuousLinearMap.inr ℝ P Y) :=
    contDiff_id.clm_comp contDiff_const
  have hL : ContDiff ℝ ∞ (fun A : P × Y →L[ℝ] Z => A ∘L ContinuousLinearMap.inl ℝ P Y) :=
    contDiff_id.clm_comp contDiff_const
  refine ⟨?_, fun A hA => ?_⟩
  · exact ContinuousLinearEquiv.isOpen.preimage hR.continuous
  · have h1 : ContDiffAt ℝ ∞ (ContinuousLinearMap.inverse ∘ fun A : P × Y →L[ℝ] Z =>
        A ∘L ContinuousLinearMap.inr ℝ P Y) A :=
      (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse hA).comp A hR.contDiffAt
    exact ((h1.clm_comp hL.contDiffAt).neg.congr_of_eventuallyEq
      (Eventually.of_forall fun B => by simp)).contDiffWithinAt

/-- T43 G3 helper: the quantitative one-map solving step (mean value + `ApproximatesLinearOn`). -/
theorem s04_tg_ift_pt {Y Z : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (e : Y ≃L[ℝ] Z) {M : ℝ} (hM0 : 0 < M)
    (hM : ‖(e.symm : Z →L[ℝ] Y)‖ ≤ M) {f : Y → Z} {y0 : Y} {r : ℝ} (hr : 0 < r)
    (hd : ∀ y ∈ closedBall y0 r, DifferentiableAt ℝ f y)
    (hD : ∀ y ∈ closedBall y0 r, ‖fderiv ℝ f y - (e : Y →L[ℝ] Z)‖ ≤ 1 / (2 * M))
    (h0 : ‖f y0‖ ≤ r / (2 * M)) :
    (∃ y ∈ closedBall y0 r, f y = 0) ∧
      (∀ y ∈ closedBall y0 r, f y = 0 → ‖y - y0‖ ≤ 2 * M * ‖f y0‖) ∧
      ∀ y ∈ closedBall y0 r, ∀ y' ∈ closedBall y0 r, f y = 0 → f y' = 0 → y = y' := by
  set c : ℝ≥0 := ⟨1 / (2 * M), by positivity⟩ with hcdef
  have hcc : (c : ℝ) = 1 / (2 * M) := rfl
  -- `f` approximates `e` on the ball with constant `c`
  have happ : ApproximatesLinearOn f (e : Y →L[ℝ] Z) (closedBall y0 r) c := by
    intro a ha b hb
    have hmv := (convex_closedBall y0 r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun y => f y - (e : Y →L[ℝ] Z) y)
      (f' := fun y => fderiv ℝ f y - (e : Y →L[ℝ] Z))
      (fun y hy => ((hd y hy).hasFDerivAt.sub (e : Y →L[ℝ] Z).hasFDerivAt).hasFDerivWithinAt)
      (fun y hy => (hD y hy).trans_eq hcc.symm) hb ha
    have hx : f a - (e : Y →L[ℝ] Z) a - (f b - (e : Y →L[ℝ] Z) b) =
        f a - f b - (e : Y →L[ℝ] Z) (a - b) := by
      rw [map_sub]
      abel
    rw [hx] at hmv
    exact hmv
  have hkey : ∀ a ∈ closedBall y0 r, ∀ b ∈ closedBall y0 r,
      ‖a - b‖ ≤ 2 * M * ‖f a - f b‖ := by
    intro a ha b hb
    have h1 := happ a ha b hb
    have h2 : ‖a - b‖ ≤ M * ‖(e : Y →L[ℝ] Z) (a - b)‖ := by
      calc ‖a - b‖ = ‖(e.symm : Z →L[ℝ] Y) ((e : Y →L[ℝ] Z) (a - b))‖ := by simp
        _ ≤ ‖(e.symm : Z →L[ℝ] Y)‖ * ‖(e : Y →L[ℝ] Z) (a - b)‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ M * ‖(e : Y →L[ℝ] Z) (a - b)‖ := by gcongr
    have h3 : ‖(e : Y →L[ℝ] Z) (a - b)‖ ≤ ‖f a - f b‖ + c * ‖a - b‖ := by
      have := norm_sub_le (f a - f b) (f a - f b - (e : Y →L[ℝ] Z) (a - b))
      simp only [sub_sub_cancel] at this
      linarith
    rw [hcc] at h3
    have h4 : M * (1 / (2 * M) * ‖a - b‖) = ‖a - b‖ / 2 := by
      field_simp
    nlinarith [norm_nonneg (f a - f b)]
  refine ⟨?_, fun y hy hy0 => ?_, fun y hy y' hy' h1 h2 => ?_⟩
  · rcases e.subsingleton_or_nnnorm_symm_pos with hs | hpos
    · refine ⟨y0, mem_closedBall_self hr.le, ?_⟩
      have : Subsingleton Z := e.symm.toEquiv.subsingleton
      exact Subsingleton.elim _ _
    · have hsurj := happ.surjOn_closedBall_of_nonlinearRightInverse e.toNonlinearRightInverse
        hr.le subset_rfl
      have hN : (e.toNonlinearRightInverse.nnnorm : ℝ) = ‖(e.symm : Z →L[ℝ] Y)‖ := rfl
      have hpos' : 0 < ‖(e.symm : Z →L[ℝ] Y)‖ := hpos
      have hinv : 1 / M ≤ (e.toNonlinearRightInverse.nnnorm : ℝ)⁻¹ := by
        rw [hN, one_div]
        exact inv_anti₀ hpos' hM
      have hrad : ‖f y0‖ ≤ ((e.toNonlinearRightInverse.nnnorm : ℝ)⁻¹ - c) * r := by
        rw [hcc]
        have : r / (2 * M) = (1 / M - 1 / (2 * M)) * r := by
          field_simp
          ring
        rw [this] at h0
        exact h0.trans (by gcongr)
      obtain ⟨y, hy, hfy⟩ := hsurj (show (0 : Z) ∈ _ from by
        rw [mem_closedBall, dist_comm, dist_eq_norm, sub_zero]
        exact hrad)
      exact ⟨y, hy, hfy⟩
  · have := hkey y hy y0 (mem_closedBall_self hr.le)
    rwa [hy0, zero_sub, norm_neg] at this
  · have := hkey y hy y' hy'
    rw [h1, h2, sub_self, norm_zero, mul_zero] at this
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/-- T43 G3: if `F_n → F_L` in `C^∞_loc(V × W)`, `F_L(v, y_L v) = 0` with `∂_y F_L` invertible
along `y_L`, then near a compact `K ⊆ V` there are smooth `y_n → y_L` in `C^∞_loc` solving
`F_n(v, y_n v) = 0`, unique in a uniform `ε`-ball (uniform contraction for existence and
uniqueness; smoothness from the local implicit function theorem; `C^∞` convergence by
bootstrapping `D y_n = -(∂_y F_n)⁻¹ ∂_v F_n`). -/
theorem s04_tg_ift {P Y Z : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {V : Set P} {W : Set Y} (hV : IsOpen V) (hW : IsOpen W) {F : ℕ → P × Y → Z} {FL : P × Y → Z}
    (hF : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (F n) (V ×ˢ W)) ∧ ContDiffOn ℝ ∞ FL (V ×ˢ W) ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (F n))
        (iteratedFDeriv ℝ i FL) atTop (V ×ˢ W))
    {yL : P → Y} (hyL : ContDiffOn ℝ ∞ yL V) (hyW : MapsTo yL V W)
    (h0 : ∀ v ∈ V, FL (v, yL v) = 0)
    (hinv : ∀ v ∈ V, ∃ e : Y ≃L[ℝ] Z, (e : Y →L[ℝ] Z) = fderiv ℝ (fun y => FL (v, y)) (yL v))
    {Kc : Set P} (hKc : IsCompact Kc) (hKcV : Kc ⊆ V) :
    ∃ V' : Set P, IsOpen V' ∧ Kc ⊆ V' ∧ V' ⊆ V ∧ ∃ ε > 0, ∃ y : ℕ → P → Y,
      ((∀ᶠ n in atTop, ContDiffOn ℝ ∞ (y n) V') ∧ ContDiffOn ℝ ∞ yL V' ∧
        ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (y n))
          (iteratedFDeriv ℝ i yL) atTop V') ∧
      (∀ᶠ n in atTop, ∀ v ∈ V', y n v ∈ W ∧ F n (v, y n v) = 0) ∧
      ∀ᶠ n in atTop, ∀ v ∈ V', ∀ y' : Y, dist y' (yL v) < ε → F n (v, y') = 0 → y' = y n v := by
  obtain ⟨hF1, hF2, hF3⟩ := hF
  have hVW : IsOpen (V ×ˢ W) := hV.prod hW
  choose e he using hinv
  obtain ⟨V0, hV0o, hKV0, hV0V, hV0c⟩ := exists_open_between_and_isCompact_closure hKc hV hKcV
  have hgr : ContinuousOn (fun v => (v, yL v)) V := continuousOn_id.prodMk hyL.continuousOn
  have hG0c : IsCompact ((fun v => (v, yL v)) '' closure V0) :=
    hV0c.image_of_continuousOn (hgr.mono hV0V)
  have hG0sub : (fun v => (v, yL v)) '' closure V0 ⊆ V ×ˢ W := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨hV0V hv, hyW (hV0V hv)⟩
  obtain ⟨r0, hr0, hr0sub⟩ := hG0c.exists_cthickening_subset_open hVW hG0sub
  have hCc : IsCompact (cthickening r0 ((fun v => (v, yL v)) '' closure V0)) := hG0c.cthickening
  have hgC : ∀ v ∈ closure V0, (v, yL v) ∈ cthickening r0 ((fun v => (v, yL v)) '' closure V0) :=
    fun v hv => self_subset_cthickening _ ⟨v, hv, rfl⟩
  have hDLc : ContinuousOn (fderiv ℝ FL) (V ×ˢ W) := hF2.continuousOn_fderiv_of_isOpen hVW (by simp)
  have hFLd : ∀ p ∈ V ×ˢ W, DifferentiableAt ℝ FL p := fun p hp =>
    (s04_tc_at hVW hF2 hp 1).differentiableAt (by simp)
  have hL : ∀ v (hv : v ∈ V),
      (e v hv : Y →L[ℝ] Z) = fderiv ℝ FL (v, yL v) ∘L ContinuousLinearMap.inr ℝ P Y :=
    fun v hv => (he v hv).trans (s04_tg_ift_slice (hFLd _ ⟨hv, hyW hv⟩))
  have hinr : ‖ContinuousLinearMap.inr ℝ P Y‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => le_of_eq (by simp [Prod.norm_def])
  -- a uniform bound for `(∂_y F_L)⁻¹` along the graph
  have hIc : ContinuousOn
      (fun v => (fderiv ℝ FL (v, yL v) ∘L ContinuousLinearMap.inr ℝ P Y).inverse) V := by
    intro v hv
    have h1 : ContinuousWithinAt
        (fun v => fderiv ℝ FL (v, yL v) ∘L ContinuousLinearMap.inr ℝ P Y) V v :=
      ((hDLc.comp hgr fun x hx => ⟨hx, hyW hx⟩) v hv).clm_comp continuousWithinAt_const
    have h2 : ContinuousAt ContinuousLinearMap.inverse
        (fderiv ℝ FL (v, yL v) ∘L ContinuousLinearMap.inr ℝ P Y) := by
      rw [← hL v hv]
      exact (contDiffAt_map_inverse (n := 0) (e v hv)).continuousAt
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun v => fderiv ℝ FL (v, yL v) ∘L ContinuousLinearMap.inr ℝ P Y) h2 h1
  obtain ⟨M0, hM0⟩ := hV0c.exists_bound_of_continuousOn (hIc.mono hV0V)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = max M0 1 := ⟨_, rfl⟩
  have hMpos : 0 < M := hMdef ▸ lt_of_lt_of_le one_pos (le_max_right _ _)
  have hMe : ∀ v (hv : v ∈ closure V0), ‖((e v (hV0V hv)).symm : Z →L[ℝ] Y)‖ ≤ M := by
    intro v hv
    have h : ‖(fderiv ℝ FL (v, yL v) ∘L ContinuousLinearMap.inr ℝ P Y).inverse‖ ≤ M0 := hM0 v hv
    rw [← hL v (hV0V hv), ContinuousLinearMap.inverse_equiv] at h
    exact h.trans (hMdef ▸ le_max_left _ _)
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 1 / (2 * M) := ⟨_, rfl⟩
  have hcpos : 0 < c := hcdef ▸ by positivity
  have hMc : M * c < 1 := by
    rw [hcdef, mul_one_div, div_lt_one (by positivity)]
    linarith
  -- uniform continuity of `D F_L` on the compact tube
  obtain ⟨δ1, hδ1, hδ1u⟩ := Metric.uniformContinuousOn_iff.1
    (hCc.uniformContinuousOn_of_continuous (hDLc.mono hr0sub)) (c / 2) (half_pos hcpos)
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = min r0 (δ1 / 2) := ⟨_, rfl⟩
  have hr : 0 < r := hrdef ▸ lt_min hr0 (half_pos hδ1)
  have hrr0 : r ≤ r0 := hrdef ▸ min_le_left _ _
  have hrδ : r < δ1 := hrdef ▸ (min_le_right _ _).trans_lt (half_lt_self hδ1)
  have hmemC : ∀ v ∈ closure V0, ∀ y, dist y (yL v) ≤ r →
      (v, y) ∈ cthickening r0 ((fun v => (v, yL v)) '' closure V0) := by
    intro v hv y hy
    refine mem_cthickening_of_dist_le (v, y) (v, yL v) r0 _ ⟨v, hv, rfl⟩ ?_
    rw [Prod.dist_eq, dist_self]
    exact max_le hr0.le (hy.trans hrr0)
  have hdistC : ∀ v ∈ closure V0, ∀ y, dist y (yL v) < δ1 → dist (v, y) (v, yL v) < δ1 := by
    intro v hv y hy
    rw [Prod.dist_eq, dist_self]
    exact max_lt hδ1 hy
  -- `‖(A - D F_L(v, y_L v)) ∘ inr‖ < c` near the graph
  have hnear : ∀ v (hv : v ∈ closure V0), ∀ p ∈ cthickening r0 ((fun v => (v, yL v)) '' closure V0),
      dist p (v, yL v) < δ1 → ∀ A : P × Y →L[ℝ] Z, dist (fderiv ℝ FL p) A < c / 2 →
        ‖A ∘L ContinuousLinearMap.inr ℝ P Y - (e v (hV0V hv) : Y →L[ℝ] Z)‖ ≤ c := by
    intro v hv p hp hpd A hA
    rw [hL v (hV0V hv), ← ContinuousLinearMap.sub_comp]
    have h2 := hδ1u p hp (v, yL v) (hgC v hv) hpd
    rw [dist_eq_norm] at h2
    rw [dist_eq_norm, norm_sub_rev] at hA
    have h3 := norm_sub_le_norm_sub_add_norm_sub A (fderiv ℝ FL p) (fderiv ℝ FL (v, yL v))
    calc ‖(A - fderiv ℝ FL (v, yL v)) ∘L ContinuousLinearMap.inr ℝ P Y‖
        ≤ ‖A - fderiv ℝ FL (v, yL v)‖ * ‖ContinuousLinearMap.inr ℝ P Y‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖A - fderiv ℝ FL (v, yL v)‖ := mul_le_of_le_one_right (norm_nonneg _) hinr
      _ ≤ c := by linarith
  -- uniform convergence of `F_n` and `D F_n` on the tube
  have hUF := s04_tc_unif hVW ⟨hF1, hF2, hF3⟩ hCc hr0sub
  have hUD := s04_tc_unif hVW (s04_tc_fderiv hVW ⟨hF1, hF2, hF3⟩) hCc hr0sub
  have E1 := Metric.tendstoUniformlyOn_iff.1 hUD (c / 2) (half_pos hcpos)
  have E2 := Metric.tendstoUniformlyOn_iff.1 hUF (r / (2 * M)) (by positivity)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 ((hF1.and E1).and E2)
  have hDb : ∀ n, N0 ≤ n → ∀ v (hv : v ∈ closure V0), ∀ y, dist y (yL v) ≤ r →
      DifferentiableAt ℝ (F n) (v, y) ∧
        ‖fderiv ℝ (F n) (v, y) ∘L ContinuousLinearMap.inr ℝ P Y -
          (e v (hV0V hv) : Y →L[ℝ] Z)‖ ≤ c := by
    intro n hn v hv y hy
    have hp := hmemC v hv y hy
    refine ⟨(s04_tc_at hVW (hN0 n hn).1.1 (hr0sub hp) 1).differentiableAt (by simp), ?_⟩
    exact hnear v hv _ hp (hdistC v hv y (hy.trans_lt hrδ)) _ ((hN0 n hn).1.2 _ hp)
  have hpt : ∀ n, N0 ≤ n → ∀ v (hv : v ∈ closure V0),
      (∃ y ∈ closedBall (yL v) r, F n (v, y) = 0) ∧
        (∀ y ∈ closedBall (yL v) r, F n (v, y) = 0 → ‖y - yL v‖ ≤ 2 * M * ‖F n (v, yL v)‖) ∧
        ∀ y ∈ closedBall (yL v) r, ∀ y' ∈ closedBall (yL v) r, F n (v, y) = 0 →
          F n (v, y') = 0 → y = y' := by
    intro n hn v hv
    have hd : ∀ y ∈ closedBall (yL v) r, DifferentiableAt ℝ (fun y => F n (v, y)) y :=
      fun y hy => (hDb n hn v hv y (mem_closedBall.1 hy)).1.comp y
        ((differentiableAt_const v).prodMk differentiableAt_id)
    refine s04_tg_ift_pt (e v (hV0V hv)) hMpos (hMe v hv) (f := fun y => F n (v, y)) hr hd
      (fun y hy => ?_) ?_
    · rw [s04_tg_ift_slice (hDb n hn v hv y (mem_closedBall.1 hy)).1, ← hcdef]
      exact (hDb n hn v hv y (mem_closedBall.1 hy)).2
    · have h1 := (hN0 n hn).2 _ (hgC v hv)
      rw [h0 v (hV0V hv), dist_zero_left] at h1
      exact h1.le
  have hex : ∀ n v, ∃ y : Y, N0 ≤ n → v ∈ closure V0 → dist y (yL v) ≤ r ∧ F n (v, y) = 0 := by
    intro n v
    by_cases h : N0 ≤ n ∧ v ∈ closure V0
    · obtain ⟨y, hy, hfy⟩ := (hpt n h.1 v h.2).1
      exact ⟨y, fun _ _ => ⟨hy, hfy⟩⟩
    · exact ⟨yL v, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose y hy using hex
  have hyb : ∀ n, N0 ≤ n → ∀ v ∈ closure V0, ‖y n v - yL v‖ ≤ 2 * M * ‖F n (v, yL v)‖ :=
    fun n hn v hv => (hpt n hn v hv).2.1 _ (hy n v hn hv).1 (hy n v hn hv).2
  have huq : ∀ n, N0 ≤ n → ∀ v ∈ closure V0, ∀ y' : Y, dist y' (yL v) ≤ r →
      F n (v, y') = 0 → y' = y n v :=
    fun n hn v hv y' hy' hF' => (hpt n hn v hv).2.2 y' hy' _ (hy n v hn hv).1 hF' (hy n v hn hv).2
  -- `y_n → y_L` uniformly on `closure V0`
  have hU0 : TendstoUniformlyOn y yL atTop (closure V0) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hUF (ε / (2 * M)) (by positivity),
      eventually_ge_atTop N0] with n hn hnN v hv
    have h1 := hn _ (hgC v hv)
    rw [h0 v (hV0V hv), dist_zero_left] at h1
    rw [dist_comm, dist_eq_norm]
    calc ‖y n v - yL v‖ ≤ 2 * M * ‖F n (v, yL v)‖ := hyb n hnN v hv
      _ < 2 * M * (ε / (2 * M)) := by gcongr
      _ = ε := by field_simp
  have E3 : ∀ᶠ n in atTop, N0 ≤ n ∧ ∀ v ∈ closure V0, dist (y n v) (yL v) < r / 2 := by
    filter_upwards [eventually_ge_atTop N0,
      Metric.tendstoUniformlyOn_iff.1 hU0 (r / 2) (half_pos hr)] with n h1 h2
    exact ⟨h1, fun v hv => by rw [dist_comm]; exact h2 v hv⟩
  -- smoothness of `y_n` (local implicit function theorem + uniqueness)
  have hsm : ∀ᶠ n in atTop, ∀ v0 ∈ V0, ContDiffAt ℝ ∞ (y n) v0 := by
    filter_upwards [E3] with n hn v0 hv0
    obtain ⟨hnN, hclose⟩ := hn
    have hv0K : v0 ∈ closure V0 := subset_closure hv0
    have hyr : dist (y n v0) (yL v0) ≤ r := (hy n v0 hnN hv0K).1
    have hp := hmemC v0 hv0K _ hyr
    have cdf : ContDiffAt ℝ ∞ (F n) (v0, y n v0) :=
      (hN0 n hnN).1.1.contDiffAt (hVW.mem_nhds (hr0sub hp))
    have if₂ : (fderiv ℝ (F n) (v0, y n v0) ∘L ContinuousLinearMap.inr ℝ P Y).IsInvertible :=
      s04_tg_ift_inv (e v0 (hV0V hv0K)) (hMe v0 hv0K) (hDb n hnN v0 hv0K _ hyr).2 hMc
    have pn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
    have hψ0 : cdf.implicitFunction pn if₂ v0 = y n v0 := cdf.implicitFunction_apply_self pn if₂
    have hψeq := cdf.eventually_apply_implicitFunction pn if₂
    have hψc : ContDiffAt ℝ ∞ (cdf.implicitFunction pn if₂) v0 :=
      cdf.contDiffAt_implicitFunction pn if₂
    have hev : ∀ᶠ x in 𝓝 v0, y n x = cdf.implicitFunction pn if₂ x := by
      have c1 := Metric.tendsto_nhds.1 hψc.continuousAt (r / 4) (by positivity)
      have c2 := Metric.tendsto_nhds.1
        ((hyL.contDiffAt (hV.mem_nhds (hV0V hv0K))).continuousAt) (r / 4) (by positivity)
      filter_upwards [c1, c2, hV0o.mem_nhds hv0, hψeq] with x h1 h2 h3 h4
      have hxK : x ∈ closure V0 := subset_closure h3
      have h5 := hclose v0 hv0K
      rw [hψ0] at h1
      have hd : dist (cdf.implicitFunction pn if₂ x) (yL x) ≤ r := by
        have := dist_triangle4 (cdf.implicitFunction pn if₂ x) (y n v0) (yL v0) (yL x)
        rw [dist_comm (yL v0) (yL x)] at this
        linarith
      have h6 : F n (x, cdf.implicitFunction pn if₂ x) = 0 := by
        rw [h4]
        exact (hy n v0 hnN hv0K).2
      exact (huq n hnN x hxK _ hd h6).symm
    exact hψc.congr_of_eventuallyEq hev
  have hsm' : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (y n) V0 :=
    hsm.mono fun n hn v hv => (hn v hv).contDiffWithinAt
  have hyL0 : ContDiffOn ℝ ∞ yL V0 := hyL.mono (subset_closure.trans hV0V)
  -- the derivative formulas `D y = Ψ (D F (·, y))`
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (P × Y →L[ℝ] Z) → (P →L[ℝ] Y), Ψ = fun A =>
      -(A ∘L ContinuousLinearMap.inr ℝ P Y).inverse ∘L (A ∘L ContinuousLinearMap.inl ℝ P Y) :=
    ⟨_, rfl⟩
  have hderiv : ∀ᶠ n in atTop, ∀ v ∈ V0, fderiv ℝ (y n) v = Ψ (fderiv ℝ (F n) (v, y n v)) := by
    filter_upwards [hsm, E3] with n hsn hn v hv
    have hvK : v ∈ closure V0 := subset_closure hv
    have hyr := (hy n v hn.1 hvK).1
    have hdb := hDb n hn.1 v hvK _ hyr
    rw [hΨ]
    exact s04_tg_ift_deriv ((hsn v hv).differentiableAt (by simp)) hdb.1
      (Filter.eventually_of_mem (hV0o.mem_nhds hv) fun x hx => (hy n x hn.1 (subset_closure hx)).2)
      (s04_tg_ift_inv (e v (hV0V hvK)) (hMe v hvK) hdb.2 hMc)
  have hderivL : ∀ v ∈ V0, fderiv ℝ yL v = Ψ (fderiv ℝ FL (v, yL v)) := by
    intro v hv
    have hvV := hV0V (subset_closure hv)
    rw [hΨ]
    exact s04_tg_ift_deriv ((hyL.contDiffAt (hV.mem_nhds hvV)).differentiableAt (by simp))
      (hFLd _ ⟨hvV, hyW hvV⟩)
      (Filter.eventually_of_mem (hV.mem_nhds hvV) fun x hx => h0 x hx) ⟨e v hvV, hL v hvV⟩
  -- `Ψ ∘ D F_n → Ψ ∘ D F_L` in `C^∞_loc` on the open tube `O`
  obtain ⟨hOo, hΨs⟩ := s04_tg_ift_psi P Y Z
  have hOC : thickening r ((fun v => (v, yL v)) '' closure V0) ⊆
      cthickening r0 ((fun v => (v, yL v)) '' closure V0) :=
    (thickening_subset_cthickening r _).trans (cthickening_mono hrr0 _)
  have hinvO : ∀ p ∈ thickening r ((fun v => (v, yL v)) '' closure V0),
      ∀ A : P × Y →L[ℝ] Z, dist (fderiv ℝ FL p) A < c / 2 →
        (A ∘L ContinuousLinearMap.inr ℝ P Y).IsInvertible := by
    intro p hp A hA
    obtain ⟨g, hg, hpg⟩ := mem_thickening_iff.1 hp
    obtain ⟨v, hv, rfl⟩ := hg
    exact s04_tg_ift_inv (e v (hV0V hv)) (hMe v hv)
      (hnear v hv p (hOC hp) (hpg.trans hrδ) A hA) hMc
  have hDF := s04_tg_ift_mono (s04_tc_fderiv hVW ⟨hF1, hF2, hF3⟩) (hOC.trans hr0sub)
  have hmaps : ∀ᶠ n in atTop, MapsTo (fun p => fderiv ℝ (F n) p)
      (thickening r ((fun v => (v, yL v)) '' closure V0))
      {A : P × Y →L[ℝ] Z | (A ∘L ContinuousLinearMap.inr ℝ P Y).IsInvertible} := by
    filter_upwards [eventually_ge_atTop N0] with n hn p hp
    exact hinvO p hp _ ((hN0 n hn).1.2 p (hOC hp))
  have hmapsL : MapsTo (fun p => fderiv ℝ FL p)
      (thickening r ((fun v => (v, yL v)) '' closure V0))
      {A : P × Y →L[ℝ] Z | (A ∘L ContinuousLinearMap.inr ℝ P Y).IsInvertible} :=
    fun p hp => hinvO p hp _ (by rw [dist_self]; exact half_pos hcpos)
  have hH := s04_tc_comp isOpen_thickening hOo (s04_tc_const (hΨ ▸ hΨs)) hDF hmaps hmapsL
  -- the graph maps `V0` into the open tube
  have hGmaps : ∀ᶠ n in atTop, MapsTo (fun x => (x, y n x)) V0
      (thickening r ((fun v => (v, yL v)) '' closure V0)) := by
    filter_upwards [E3] with n hn v hv
    refine mem_thickening_iff.2 ⟨(v, yL v), ⟨v, subset_closure hv, rfl⟩, ?_⟩
    rw [Prod.dist_eq, dist_self]
    exact max_lt hr ((hn.2 v (subset_closure hv)).trans (half_lt_self hr))
  have hGmapsL : MapsTo (fun x => (x, yL x)) V0
      (thickening r ((fun v => (v, yL v)) '' closure V0)) := fun v hv =>
    mem_thickening_iff.2 ⟨(v, yL v), ⟨v, subset_closure hv, rfl⟩, by rw [dist_self]; exact hr⟩
  have hgr1 : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fun x => (x, y n x)) V0 :=
    hsm'.mono fun n hn => contDiffOn_id.prodMk hn
  have hgr2 : ContDiffOn ℝ ∞ (fun x => (x, yL x)) V0 := contDiffOn_id.prodMk hyL0
  -- bootstrap: convergence up to order `i` gives order `i + 1`
  have hboot : ∀ i, ∀ k ≤ i, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ k (y n))
      (iteratedFDeriv ℝ k yL) atTop V0 := by
    intro i
    induction i with
    | zero =>
      intro k hk
      obtain rfl : k = 0 := Nat.le_zero.1 hk
      exact s04_tg_ift_zero (hU0.mono subset_closure).tendstoLocallyUniformlyOn
    | succ i ih =>
      intro k hk
      rcases Nat.lt_or_ge k (i + 1) with hlt | hge
      · exact ih k (Nat.lt_succ_iff.1 hlt)
      obtain rfl : k = i + 1 := le_antisymm hk hge
      have hg := s04_tg_ift_graph hV0o hsm' hyL0 i ih
      have hcomp := s04_tg_ift_comp hV0o isOpen_thickening hgr1 hgr2 hGmaps hGmapsL i
        (P →L[ℝ] Y) _ _ hH hg i le_rfl
      refine (s04_tg_ift_succ i).1 (s04_tc_evcongr hcomp (hderiv.mono fun n hn => ?_) ?_)
      · exact s04_tc_eqOn hV0o (fun v hv => (hn v hv).symm) i
      · exact s04_tc_eqOn hV0o (fun v hv => (hderivL v hv).symm) i
  refine ⟨V0, hV0o, hKV0, subset_closure.trans hV0V, r, hr, y,
    ⟨hsm', hyL0, fun i => hboot i i le_rfl⟩, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop N0] with n hn v hv
    have h := hy n v hn (subset_closure hv)
    exact ⟨(hr0sub (hmemC v (subset_closure hv) _ h.1)).2, h.2⟩
  · filter_upwards [eventually_ge_atTop N0] with n hn v hv y' hy' hF'
    exact huq n hn v (subset_closure hv) y' hy'.le hF'

/-! ### G4: no return, the far end of the tube, and the solution -/

/-- T43 G4 helper: `(x, h)` with `h > 0` and `λ(w)(|x - w|² + h²) < 2h`, `w ∈ Ω`, lies in the
interior of `U` (an open piece of the horoball `B_w`). -/
theorem s04_tg_horoT_int {Ω : Set ℂ} {w : ℂ} (hw : w ∈ Ω) {x : ℂ} {h : ℝ} (hh : 0 < h)
    (hlt : poincareDensity Ω w * (‖x - w‖ ^ 2 + h ^ 2) < 2 * h) :
    (x, h) ∈ interior (horoUnion Ω) := by
  have hO : IsOpen {p : ℂ × ℝ | 0 < p.2 ∧
      poincareDensity Ω w * (‖p.1 - w‖ ^ 2 + p.2 ^ 2) < 2 * p.2} :=
    (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt
      (f := fun p : ℂ × ℝ => poincareDensity Ω w * (‖p.1 - w‖ ^ 2 + p.2 ^ 2))
      (g := fun p : ℂ × ℝ => 2 * p.2) (by fun_prop) (by fun_prop))
  refine mem_interior.2 ⟨_, ?_, hO, ⟨hh, hlt⟩⟩
  rintro p ⟨hp1, hp2⟩
  refine mem_biUnion hw ⟨hp1, ?_⟩
  show poincareDensity Ω w * (‖p.1 - w‖ ^ 2 + p.2 ^ 2) / (2 * p.2) ≤ 1
  rw [div_le_one (by positivity)]
  exact hp2.le

/-- T43 G4 helper: the hyperbolic distance of `ℍ³` is invariant under `(x, h) ↦ (c x + b, c h)`. -/
theorem s04_tg_nr_hd {c : ℝ} (hc : 0 < c) (b : ℂ) (q q' : ℂ × ℝ) :
    hdist ((c : ℂ) * q.1 + b, ‖(c : ℂ)‖ * q.2) ((c : ℂ) * q'.1 + b, ‖(c : ℂ)‖ * q'.2) =
      hdist q q' := by
  show Real.arcosh (1 + (‖(c : ℂ) * q.1 + b - ((c : ℂ) * q'.1 + b)‖ ^ 2 +
      (‖(c : ℂ)‖ * q.2 - ‖(c : ℂ)‖ * q'.2) ^ 2) / (2 * (‖(c : ℂ)‖ * q.2) * (‖(c : ℂ)‖ * q'.2))) =
    Real.arcosh (1 + (‖q.1 - q'.1‖ ^ 2 + (q.2 - q'.2) ^ 2) / (2 * q.2 * q'.2))
  rw [show (c : ℂ) * q.1 + b - ((c : ℂ) * q'.1 + b) = (c : ℂ) * (q.1 - q'.1) by ring, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hc.le, mul_pow, ← mul_sub, mul_pow, ← mul_add,
    show 2 * (c * q.2) * (c * q'.2) = c ^ 2 * (2 * q.2 * q'.2) by ring,
    mul_div_mul_left _ _ (pow_ne_zero 2 hc.ne')]

/-- T43 G4 helper: the lower quasi-isometry bound of `prop_qi` for `X*` survives a real
similarity `A z = c z + b` of the pair. -/
theorem s04_tg_nr_qi {K : ℝ} {Ω Ωs : Set ℂ} (hpair : IsKQuasiPair Ω Ωs K) {A B : ℝ}
    (hl : ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ∀ w ∈ Ω, ∀ w' ∈ Ω,
      poincareDist Ω w w' ≤ A * hdist (epstein Ω w) (epstein Ω w') + B)
    {c : ℝ} (hc : 0 < c) (b : ℂ) {w w' : ℂ} (hw : w ∈ (fun z => (c : ℂ) * z + b) '' Ωs)
    (hw' : w' ∈ (fun z => (c : ℂ) * z + b) '' Ωs) :
    poincareDist ((fun z => (c : ℂ) * z + b) '' Ωs) w w' ≤
      A * hdist (epstein ((fun z => (c : ℂ) * z + b) '' Ωs) w)
        (epstein ((fun z => (c : ℂ) * z + b) '' Ωs) w') + B := by
  have hΩs := s02_jordanPair_riemannMap (s02_jordanPair_symm (s03_b0_jordanPair hpair))
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  obtain ⟨ζ, hζ, rfl⟩ := hw
  obtain ⟨ζ', hζ', rfl⟩ := hw'
  rw [s04_tn_dist Ωs hc' b ζ ζ', subsec_epstein_natural_affine hΩs hc' hζ,
    subsec_epstein_natural_affine hΩs hc' hζ', s04_tg_nr_hd hc b]
  exact hl Ωs Ω (s03_qce_swap hpair) ζ hζ ζ' hζ'

/-- T43 G4 helper: translating the star side by `-y₁` translates `X*` by `-y₁`. -/
theorem s04_tg_nr_tr {Ωs : Set ℂ} (hΩs : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ωs) {c : ℝ}
    (hc : 0 < c) (b y₁ : ℂ) {z : ℂ} (hz : z ∈ (fun z => (c : ℂ) * z + b) '' Ωs) :
    z - y₁ ∈ (fun z => (c : ℂ) * z + (b - y₁)) '' Ωs ∧
      epstein ((fun z => (c : ℂ) * z + (b - y₁)) '' Ωs) (z - y₁) =
        ((epstein ((fun z => (c : ℂ) * z + b) '' Ωs) z).1 - y₁,
          (epstein ((fun z => (c : ℂ) * z + b) '' Ωs) z).2) := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  obtain ⟨ζ, hζ, rfl⟩ := hz
  have e : (c : ℂ) * ζ + b - y₁ = (c : ℂ) * ζ + (b - y₁) := by ring
  refine ⟨⟨ζ, hζ, e.symm⟩, ?_⟩
  show epstein ((fun z => (c : ℂ) * z + (b - y₁)) '' Ωs) ((c : ℂ) * ζ + b - y₁) =
    ((epstein ((fun z => (c : ℂ) * z + b) '' Ωs) ((c : ℂ) * ζ + b)).1 - y₁,
      (epstein ((fun z => (c : ℂ) * z + b) '' Ωs) ((c : ℂ) * ζ + b)).2)
  rw [e, subsec_epstein_natural_affine hΩs hc' hζ, subsec_epstein_natural_affine hΩs hc' hζ]
  refine Prod.ext ?_ rfl
  show (c : ℂ) * (epstein Ωs ζ).1 + (b - y₁) = (c : ℂ) * (epstein Ωs ζ).1 + b - y₁
  ring

/-- T43 G4 helper: `cosh d` is continuous on `ℍ³ × ℍ³` (sequential form). -/
theorem s04_tg_nr_cosh {ι : Type*} {l : Filter ι} {f g : ι → ℂ × ℝ} {q q' : ℂ × ℝ}
    (hf : Tendsto f l (𝓝 q)) (hg : Tendsto g l (𝓝 q')) (hq : 0 < q.2) (hq' : 0 < q'.2) :
    Tendsto (fun x => coshDist (f x) (g x)) l (𝓝 (coshDist q q')) := by
  have hf1 := (continuous_fst.tendsto q).comp hf
  have hf2 := (continuous_snd.tendsto q).comp hf
  have hg1 := (continuous_fst.tendsto q').comp hg
  have hg2 := (continuous_snd.tendsto q').comp hg
  show Tendsto (fun x => 1 + (‖(f x).1 - (g x).1‖ ^ 2 + ((f x).2 - (g x).2) ^ 2) /
    (2 * (f x).2 * (g x).2)) l (𝓝 (1 + (‖q.1 - q'.1‖ ^ 2 + (q.2 - q'.2) ^ 2) / (2 * q.2 * q'.2)))
  exact tendsto_const_nhds.add ((((hf1.sub hg1).norm.pow 2).add ((hf2.sub hg2).pow 2)).div
    ((tendsto_const_nhds.mul hf2).mul hg2) (by positivity))

/-- T43 G4 helper: the limit normal geodesic stays in `ℍ³`. -/
theorem s04_tg_nr_pos {α β : ℂ} (hα : α ≠ 0) {v : ℂ} (hv : 0 < (α * v + β).im) (τ : ℝ) :
    0 < (normalGeod {z | 0 < (α * z + β).im} v τ).2 := by
  have hlam : poincareDensity {z | 0 < (α * z + β).im} v = ‖α‖ / (1 * (α * v + β).im) :=
    s04_tg_hp_lam α β hα 1 (Or.inl rfl) _ (s04_tg_hp_up α β) hv
  have hlp : 0 < poincareDensity {z | 0 < (α * z + β).im} v := by
    rw [hlam]
    exact div_pos (norm_pos_iff.2 hα) (by linarith)
  show 0 < (poincareDensity {z | 0 < (α * z + β).im} v * Real.exp (-τ) / 2) /
    (‖logDensityDz {z | 0 < (α * z + β).im} v‖ ^ 2 +
      (poincareDensity {z | 0 < (α * z + β).im} v * Real.exp (-τ) / 2) ^ 2)
  have h0 : 0 < poincareDensity {z | 0 < (α * z + β).im} v * Real.exp (-τ) / 2 :=
    div_pos (mul_pos hlp (Real.exp_pos _)) two_pos
  exact div_pos h0 (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos h0 2))

/-- T43 G4 helper: the Epstein map of the limit star half-plane after the translation by `y₁`. -/
theorem s04_tg_sv_tr {gsL : ℂ → ℂ} (hgsL : IsConformalOnto gsL unitDisc (gsL '' unitDisc))
    {α β y₁ : ℂ} (hDs : gsL '' unitDisc = {z | (α * (z + y₁) + β).im < 0}) {z : ℂ}
    (hz : z ∈ gsL '' unitDisc) :
    epstein {z | (α * z + β).im < 0} (z + y₁) =
      ((epstein (gsL '' unitDisc) z).1 + y₁, (epstein (gsL '' unitDisc) z).2) := by
  have ht := subsec_epstein_natural_affine ⟨gsL, hgsL⟩ (a := 1) (b := y₁) one_ne_zero hz
  have hset : (fun z => 1 * z + y₁) '' (gsL '' unitDisc) = {z | (α * z + β).im < 0} := by
    ext x
    rw [hDs]
    constructor
    · rintro ⟨y, hy, rfl⟩
      show (α * (1 * y + y₁) + β).im < 0
      rw [one_mul]
      exact hy
    · intro hx
      refine ⟨x - y₁, ?_, by ring⟩
      show (α * (x - y₁ + y₁) + β).im < 0
      rw [sub_add_cancel]
      exact hx
  rw [hset, one_mul] at ht
  rw [ht]
  ext <;> simp

/-- T43 G4 helper: the reflection `v ↦ v̄` across the limit line is smooth. -/
theorem s04_tg_sv_rho (α β : ℂ) :
    ContDiff ℝ ∞ fun v : ℂ => v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α :=
  contDiff_id.sub ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (Complex.imCLM.contDiff.comp ((contDiff_const.mul contDiff_id).add
      contDiff_const)))).div_const α)

/-- T43 G4 (no return): eventually every hit `E_n(v, τ) = X*_n(z)` with `v` in a compact of
`D` and `τ ∈ [-1, T'+1]` is `ε`-close to `(0, v̄)` (`prop_qi` bounds `d_{ρ*}(z, y₁)`, the star
`s04_tp_ball` traps `z` in a compact of `D*`; a limit hit is `(0, v̄)` by `s04_tg_lim_eq`). -/
theorem s04_tg_noreturn {K : ℝ} {Ω Ωs : ℕ → Set ℂ} (hpair : ∀ n, IsKQuasiPair (Ω n) (Ωs n) K)
    (hnl : ∀ n, ¬ IsLinePair (Ω n) (Ωs n)) {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) {b : ℕ → ℂ}
    {y₁ : ℂ} {g gs : ℕ → ℂ → ℂ} {gL gsL : ℂ → ℂ} {α β : ℂ}
    (hg : ∀ n, IsConformalOnto (g n) unitDisc ((fun z => (c n : ℂ) * z + b n) '' Ω n) ∧
      g n 0 = 0)
    (hgL : IsConformalOnto gL unitDisc (gL '' unitDisc)) (hgL0 : gL 0 = 0)
    (hconv : TendstoLocallyUniformlyOn g gL atTop unitDisc)
    (hker : ∀ S : Set ℂ, IsCompact S → S ⊆ gL '' unitDisc →
      ∀ᶠ n in atTop, S ⊆ (fun z => (c n : ℂ) * z + b n) '' Ω n)
    (hgs : ∀ n, IsConformalOnto (gs n) unitDisc
      ((fun z => (c n : ℂ) * z + (b n - y₁)) '' Ωs n) ∧ gs n 0 = 0)
    (hgsL : IsConformalOnto gsL unitDisc (gsL '' unitDisc)) (hgsL0 : gsL 0 = 0)
    (hsconv : TendstoLocallyUniformlyOn gs gsL atTop unitDisc)
    (hsker : ∀ S : Set ℂ, IsCompact S → S ⊆ gsL '' unitDisc →
      ∀ᶠ n in atTop, S ⊆ (fun z => (c n : ℂ) * z + (b n - y₁)) '' Ωs n)
    (hα : α ≠ 0) (hD : gL '' unitDisc = {z | 0 < (α * z + β).im})
    (hDs : gsL '' unitDisc = {z | (α * (z + y₁) + β).im < 0})
    {Kc : Set ℂ} (hKc : IsCompact Kc) (hKcD : Kc ⊆ gL '' unitDisc) (T' : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v ∈ Kc, ∀ τ ∈ Icc (-1) (T' + 1),
      ∀ z ∈ (fun z => (c n : ℂ) * z + b n) '' Ωs n,
        epstein ((fun z => (c n : ℂ) * z + b n) '' Ωs n) z =
            normalGeod ((fun z => (c n : ℂ) * z + b n) '' Ω n) v τ →
          |τ| < ε ∧ dist z (v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α) < ε := by
  have _h := hnl
  obtain ⟨A, B, hA0, hl⟩ := s03_qi_lower K
  have hΩs : ∀ n, ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc (Ωs n) := fun n =>
    s02_jordanPair_riemannMap (s02_jordanPair_symm (s03_b0_jordanPair (hpair n)))
  have hDo : IsOpen (gL '' unitDisc) := hgL.isOpen isOpen_ball
  have hDso : IsOpen (gsL '' unitDisc) := hgsL.isOpen isOpen_ball
  obtain ⟨U, hUo, hKU, hUD, hUc⟩ := exists_open_between_and_isCompact_closure hKc hDo hKcD
  have hE := (s04_tg_conv hg hgL hgL0 hconv hker hUo hUc hUD).2
  have hEL := s04_tc_zero (hE.2.2 0)
  have hEc := hE.2.1.continuousOn
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨φ, hφ, hP⟩ := Filter.extraction_of_frequently_atTop hcon
  have hP' : ∀ k, ∃ v ∈ Kc, ∃ τ ∈ Icc (-1) (T' + 1),
      ∃ z ∈ (fun z => (c (φ k) : ℂ) * z + b (φ k)) '' Ωs (φ k),
        epstein ((fun z => (c (φ k) : ℂ) * z + b (φ k)) '' Ωs (φ k)) z =
          normalGeod ((fun z => (c (φ k) : ℂ) * z + b (φ k)) '' Ω (φ k)) v τ ∧
        ¬ (|τ| < ε ∧ dist z (v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α) < ε) := fun k => by
    have h := hP k
    simp only [not_forall, exists_prop] at h
    exact h
  choose v hv τ hτ z hz heq hne using hP'
  obtain ⟨p, hp, ψ, hψ, hpT⟩ := (hKc.prod isCompact_Icc).tendsto_subseq
    (x := fun k => (v k, τ k)) fun k => ⟨hv k, hτ k⟩
  have hm : StrictMono (fun k => φ (ψ k)) := hφ.comp hψ
  have hET : Tendsto (fun k => normalGeod ((fun z => (c (φ (ψ k)) : ℂ) * z + b (φ (ψ k))) ''
      Ω (φ (ψ k))) (v (ψ k)) (τ (ψ k))) atTop (𝓝 (normalGeod (gL '' unitDisc) p.1 p.2)) :=
    ((s04_tc_cc hEc).1 hEL p ⟨hKU hp.1, mem_univ _⟩).comp (hm.tendsto_atTop.prodMk
      (tendsto_nhdsWithin_iff.2 ⟨hpT, Eventually.of_forall fun k => ⟨hKU (hv _), mem_univ _⟩⟩))
  have hp1D : 0 < (α * p.1 + β).im := by
    have h := hKcD hp.1
    rw [hD] at h
    exact h
  have hQ2 : 0 < (normalGeod (gL '' unitDisc) p.1 p.2).2 := by
    rw [hD]
    exact s04_tg_nr_pos hα hp1D p.2
  have h0D : (0 : ℂ) ∈ gsL '' unitDisc := ⟨0, mem_ball_self one_pos, hgsL0⟩
  have hQ02 : 0 < (epstein (gsL '' unitDisc) 0).2 := s04_tb_ep_uhs ⟨gsL, hgsL⟩ h0D
  obtain ⟨Kb, hKb, hKbD, hball⟩ := s04_tp_ball hgs hgsL hgsL0 hsconv
    (A * Real.arcosh (coshDist (epstein (gsL '' unitDisc) 0)
      ((normalGeod (gL '' unitDisc) p.1 p.2).1 - y₁, (normalGeod (gL '' unitDisc) p.1 p.2).2) + 1)
      + B)
  obtain ⟨Us, hUso, hKUs, hUsD, hUsc⟩ := exists_open_between_and_isCompact_closure
    (hKb.union (isCompact_singleton (x := 0))) hDso (union_subset hKbD (singleton_subset_iff.2 h0D))
  have hX := (s04_tg_conv hgs hgsL hgsL0 hsconv hsker hUso hUsc hUsD).1
  have hXL := s04_tc_zero (hX.2.2 0)
  have hXc := hX.2.1.continuousOn
  have hXT : ∀ {s : ℕ → ℂ} {s0 : ℂ}, Tendsto s atTop (𝓝 s0) → (∀ k, s k ∈ Us) → s0 ∈ Us →
      ∀ {μ : ℕ → ℕ}, StrictMono μ → Tendsto (fun k => epstein
        ((fun z => (c (μ k) : ℂ) * z + (b (μ k) - y₁)) '' Ωs (μ k)) (s k)) atTop
          (𝓝 (epstein (gsL '' unitDisc) s0)) := fun hs hsU hs0 _ hμ =>
    ((s04_tc_cc hXc).1 hXL _ hs0).comp (hμ.tendsto_atTop.prodMk
      (tendsto_nhdsWithin_iff.2 ⟨hs, Eventually.of_forall hsU⟩))
  have h0U : (0 : ℂ) ∈ Us := hKUs (Or.inr rfl)
  have h0T := hXT tendsto_const_nhds (fun _ => h0U) h0U hm
  have hE''T : Tendsto (fun k => ((normalGeod ((fun z => (c (φ (ψ k)) : ℂ) * z + b (φ (ψ k))) ''
      Ω (φ (ψ k))) (v (ψ k)) (τ (ψ k))).1 - y₁,
        (normalGeod ((fun z => (c (φ (ψ k)) : ℂ) * z + b (φ (ψ k))) ''
          Ω (φ (ψ k))) (v (ψ k)) (τ (ψ k))).2)) atTop
      (𝓝 ((normalGeod (gL '' unitDisc) p.1 p.2).1 - y₁, (normalGeod (gL '' unitDisc) p.1 p.2).2)) :=
    (((continuous_fst.tendsto _).comp hET).sub_const y₁).prodMk_nhds
      ((continuous_snd.tendsto _).comp hET)
  have hcT := s04_tg_nr_cosh h0T hE''T hQ02 hQ2
  have heqk : ∀ k, z k - y₁ ∈ (fun z => (c (φ k) : ℂ) * z + (b (φ k) - y₁)) '' Ωs (φ k) ∧
      epstein ((fun z => (c (φ k) : ℂ) * z + (b (φ k) - y₁)) '' Ωs (φ k)) (z k - y₁) =
        ((normalGeod ((fun z => (c (φ k) : ℂ) * z + b (φ k)) '' Ω (φ k)) (v k) (τ k)).1 - y₁,
          (normalGeod ((fun z => (c (φ k) : ℂ) * z + b (φ k)) '' Ω (φ k)) (v k) (τ k)).2) :=
    fun k => by
      obtain ⟨h1, h2⟩ := s04_tg_nr_tr (hΩs _) (hc _) (b (φ k)) y₁ (hz k)
      rw [heq k] at h2
      exact ⟨h1, h2⟩
  have hzK : ∀ᶠ k in atTop, z (ψ k) - y₁ ∈ Kb := by
    filter_upwards [hcT.eventually (gt_mem_nhds (lt_add_one _)),
      ((continuous_snd.tendsto _).comp hET).eventually (lt_mem_nhds hQ2),
      hm.tendsto_atTop.eventually hball] with k h1 h2 h3
    have h0m : (0 : ℂ) ∈ (fun z => (c (φ (ψ k)) : ℂ) * z + (b (φ (ψ k)) - y₁)) '' Ωs (φ (ψ k)) := by
      rw [← (hgs _).1.2.2]
      exact ⟨0, mem_ball_self one_pos, (hgs _).2⟩
    have hX0 := s04_tb_ep_uhs ⟨gs _, (hgs _).1⟩ h0m
    have hX0' : 0 < (epstein ((fun z => (c (φ (ψ k)) : ℂ) * z + (b (φ (ψ k)) - y₁)) ''
      Ωs (φ (ψ k))) 0).2 := hX0
    obtain ⟨hzm, hzeq⟩ := heqk (ψ k)
    refine h3 ⟨hzm, ?_⟩
    have hq := s04_tg_nr_qi (hpair _) hl (hc _) (b (φ (ψ k)) - y₁) h0m hzm
    rw [hzeq] at hq
    have h2' : 0 < (normalGeod ((fun z => (c (φ (ψ k)) : ℂ) * z + b (φ (ψ k))) ''
        Ω (φ (ψ k))) (v (ψ k)) (τ (ψ k))).2 := h2
    have hpos : 0 < coshDist (epstein ((fun z => (c (φ (ψ k)) : ℂ) * z + (b (φ (ψ k)) - y₁)) ''
        Ωs (φ (ψ k))) 0) ((normalGeod ((fun z => (c (φ (ψ k)) : ℂ) * z + b (φ (ψ k))) ''
          Ω (φ (ψ k))) (v (ψ k)) (τ (ψ k))).1 - y₁,
            (normalGeod ((fun z => (c (φ (ψ k)) : ℂ) * z + b (φ (ψ k))) ''
              Ω (φ (ψ k))) (v (ψ k)) (τ (ψ k))).2) := by
      simp only [coshDist]
      positivity
    have hd : hdist (epstein ((fun z => (c (φ (ψ k)) : ℂ) * z + (b (φ (ψ k)) - y₁)) ''
        Ωs (φ (ψ k))) 0) ((normalGeod ((fun z => (c (φ (ψ k)) : ℂ) * z + b (φ (ψ k))) ''
          Ω (φ (ψ k))) (v (ψ k)) (τ (ψ k))).1 - y₁,
            (normalGeod ((fun z => (c (φ (ψ k)) : ℂ) * z + b (φ (ψ k))) ''
              Ω (φ (ψ k))) (v (ψ k)) (τ (ψ k))).2) ≤
        Real.arcosh (coshDist (epstein (gsL '' unitDisc) 0)
          ((normalGeod (gL '' unitDisc) p.1 p.2).1 - y₁, (normalGeod (gL '' unitDisc) p.1 p.2).2)
            + 1) :=
      (Real.arcosh_le_arcosh hpos (hpos.trans h1)).2 h1.le
    calc _ ≤ _ := hq
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hd hA0]
  obtain ⟨N, hN⟩ := eventually_atTop.1 hzK
  obtain ⟨z0, hz0, χ, hχ, hzT⟩ := hKb.tendsto_subseq (x := fun k => z (ψ (k + N)) - y₁)
    fun k => hN _ (Nat.le_add_left N k)
  have hμ : StrictMono fun k => χ k + N := fun a b h => Nat.add_lt_add_right (hχ h) N
  have hXz := hXT hzT (fun k => hKUs (Or.inl (hN _ (Nat.le_add_left N _)))) (hKUs (Or.inl hz0))
    (hm.comp hμ)
  have hlim : epstein (gsL '' unitDisc) z0 =
      ((normalGeod (gL '' unitDisc) p.1 p.2).1 - y₁, (normalGeod (gL '' unitDisc) p.1 p.2).2) :=
    tendsto_nhds_unique hXz ((hE''T.comp hμ.tendsto_atTop).congr fun k => (heqk _).2.symm)
  have hz0D : (α * (z0 + y₁) + β).im < 0 := by
    have h := hKbD hz0
    rw [hDs] at h
    exact h
  have hlim' : normalGeod {z | 0 < (α * z + β).im} p.1 p.2 =
      epstein {z | (α * z + β).im < 0} (z0 + y₁) := by
    rw [s04_tg_sv_tr hgsL hDs (hKbD hz0), hlim, ← hD]
    ext <;> simp
  have hfin := (s04_tg_lim_eq hα hp1D p.2 hz0D).1 hlim'
  have hρc : Continuous fun x : ℂ => x - 2 * I * (((α * x + β).im : ℝ) : ℂ) / α :=
    continuous_id.sub ((continuous_const.mul (Complex.continuous_ofReal.comp
      (Complex.continuous_im.comp ((continuous_const.mul continuous_id).add
        continuous_const)))).div_const α)
  have hpTμ := hpT.comp hμ.tendsto_atTop
  have hτT := (continuous_snd.tendsto _).comp hpTμ
  have hvT := (continuous_fst.tendsto _).comp hpTμ
  have hzT' : Tendsto (fun k => z (ψ (χ k + N))) atTop (𝓝 (z0 + y₁)) :=
    (hzT.add_const y₁).congr fun k => sub_add_cancel _ _
  have hd := hzT'.dist ((hρc.tendsto _).comp hvT)
  rw [hfin.2, dist_self] at hd
  have hτ0 := hτT.abs
  rw [hfin.1, abs_zero] at hτ0
  obtain ⟨k, hk1, hk2⟩ := ((hd.eventually (gt_mem_nhds hε)).and
    (hτ0.eventually (gt_mem_nhds hε))).exists
  exact hne _ ⟨hk2, hk1⟩

/-- T43 G4: the far end of the tube is eventually inside `int U*` (`C^0` limit of
`Φ*_{E_n(v,T')}(v̄) → e^{-T'} < 1`). -/
theorem s04_tg_horoT {Ω Ωs : ℕ → Set ℂ} {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) {b : ℕ → ℂ}
    {y₁ : ℂ} {g gs : ℕ → ℂ → ℂ} {gL gsL : ℂ → ℂ} {α β : ℂ}
    (hg : ∀ n, IsConformalOnto (g n) unitDisc ((fun z => (c n : ℂ) * z + b n) '' Ω n) ∧
      g n 0 = 0)
    (hgL : IsConformalOnto gL unitDisc (gL '' unitDisc)) (hgL0 : gL 0 = 0)
    (hconv : TendstoLocallyUniformlyOn g gL atTop unitDisc)
    (hker : ∀ S : Set ℂ, IsCompact S → S ⊆ gL '' unitDisc →
      ∀ᶠ n in atTop, S ⊆ (fun z => (c n : ℂ) * z + b n) '' Ω n)
    (hgs : ∀ n, IsConformalOnto (gs n) unitDisc
      ((fun z => (c n : ℂ) * z + (b n - y₁)) '' Ωs n) ∧ gs n 0 = 0)
    (hgsL : IsConformalOnto gsL unitDisc (gsL '' unitDisc)) (hgsL0 : gsL 0 = 0)
    (hsconv : TendstoLocallyUniformlyOn gs gsL atTop unitDisc)
    (hsker : ∀ S : Set ℂ, IsCompact S → S ⊆ gsL '' unitDisc →
      ∀ᶠ n in atTop, S ⊆ (fun z => (c n : ℂ) * z + (b n - y₁)) '' Ωs n)
    (hα : α ≠ 0) (hD : gL '' unitDisc = {z | 0 < (α * z + β).im})
    (hDs : gsL '' unitDisc = {z | (α * (z + y₁) + β).im < 0})
    {Kc : Set ℂ} (hKc : IsCompact Kc) (hKcD : Kc ⊆ gL '' unitDisc) {T' : ℝ} (hT' : 0 < T') :
    ∀ᶠ n in atTop, ∀ v ∈ Kc, normalGeod ((fun z => (c n : ℂ) * z + b n) '' Ω n) v T' ∈
      interior (horoUnion ((fun z => (c n : ℂ) * z + b n) '' Ωs n)) := by
  have _hc := hc
  have hDo : IsOpen (gL '' unitDisc) := hgL.isOpen isOpen_ball
  have hDso : IsOpen (gsL '' unitDisc) := hgsL.isOpen isOpen_ball
  obtain ⟨U, hUo, hKU, hUD, hUc⟩ := exists_open_between_and_isCompact_closure hKc hDo hKcD
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℂ → ℂ, ρ = fun v => v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α :=
    ⟨_, rfl⟩
  have hρc : Continuous ρ := by
    rw [hρ]
    exact continuous_id.sub ((continuous_const.mul (Complex.continuous_ofReal.comp
      (Complex.continuous_im.comp ((continuous_const.mul continuous_id).add
        continuous_const)))).div_const α)
  have hρs : Continuous fun v => ρ v - y₁ := hρc.sub continuous_const
  have hρD : ∀ v ∈ gL '' unitDisc, ρ v - y₁ ∈ gsL '' unitDisc := by
    intro v hv
    rw [hD] at hv
    have hv' : 0 < (α * v + β).im := hv
    rw [hDs]
    show (α * (ρ v - y₁ + y₁) + β).im < 0
    rw [sub_add_cancel, hρ, s04_tg_lim_refl hα]
    linarith
  obtain ⟨Us, hUso, hKUs, hUsD, hUsc⟩ := exists_open_between_and_isCompact_closure
    (hUc.image hρs) hDso (by
      rintro _ ⟨v, hv, rfl⟩
      exact hρD v (hUD hv))
  have hUUs : ∀ v ∈ U, ρ v - y₁ ∈ Us := fun v hv =>
    hKUs (mem_image_of_mem _ (subset_closure hv))
  have hE := (s04_tg_conv hg hgL hgL0 hconv hker hUo hUc hUD).2
  have hEL := s04_tc_zero (hE.2.2 0)
  have hEc := hE.2.1.continuousOn
  have hl := s04_td_lambda hgs hgsL hgsL0 hsconv hsker hUso hUsc hUsD
  have hlL := s04_tc_zero (hl.2.2 0)
  have hlc := hl.2.1.continuousOn
  have hq : ContinuousOn (fun v => normalGeod (gL '' unitDisc) v T') U :=
    hEc.comp (continuousOn_id.prodMk continuousOn_const) fun v hv => ⟨hv, mem_univ _⟩
  have hlv : ContinuousOn (fun v => poincareDensity (gsL '' unitDisc) (ρ v - y₁)) U :=
    hlc.comp hρs.continuousOn hUUs
  have hq1 := continuous_fst.comp_continuousOn hq
  have hq2 := continuous_snd.comp_continuousOn hq
  have hHc : ContinuousOn (fun v => ((normalGeod (gL '' unitDisc) v T').2,
      poincareDensity (gsL '' unitDisc) (ρ v - y₁) *
        (‖(normalGeod (gL '' unitDisc) v T').1 - y₁ - (ρ v - y₁)‖ ^ 2 +
          (normalGeod (gL '' unitDisc) v T').2 ^ 2) -
        2 * (normalGeod (gL '' unitDisc) v T').2)) U :=
    hq2.prodMk ((hlv.mul ((((hq1.sub continuousOn_const).sub hρs.continuousOn).norm.pow 2).add
      (hq2.pow 2))).sub (continuousOn_const.mul hq2))
  have hHT : TendstoLocallyUniformlyOn (fun n v =>
      ((normalGeod ((fun z => (c n : ℂ) * z + b n) '' Ω n) v T').2,
        poincareDensity ((fun z => (c n : ℂ) * z + (b n - y₁)) '' Ωs n) (ρ v - y₁) *
          (‖(normalGeod ((fun z => (c n : ℂ) * z + b n) '' Ω n) v T').1 - y₁ - (ρ v - y₁)‖ ^ 2 +
            (normalGeod ((fun z => (c n : ℂ) * z + b n) '' Ω n) v T').2 ^ 2) -
          2 * (normalGeod ((fun z => (c n : ℂ) * z + b n) '' Ω n) v T').2))
      (fun v => ((normalGeod (gL '' unitDisc) v T').2,
        poincareDensity (gsL '' unitDisc) (ρ v - y₁) *
          (‖(normalGeod (gL '' unitDisc) v T').1 - y₁ - (ρ v - y₁)‖ ^ 2 +
            (normalGeod (gL '' unitDisc) v T').2 ^ 2) -
          2 * (normalGeod (gL '' unitDisc) v T').2)) atTop U := by
    refine (s04_tc_cc hHc).2 fun x hx => ?_
    have hsn : Tendsto (fun p : ℕ × ℂ => p.2) (atTop ×ˢ 𝓝[U] x) (𝓝 x) :=
      tendsto_snd.mono_right nhdsWithin_le_nhds
    have hsU : ∀ᶠ p : ℕ × ℂ in atTop ×ˢ 𝓝[U] x, p.2 ∈ U :=
      tendsto_snd.eventually self_mem_nhdsWithin
    have hm : Tendsto (fun p : ℕ × ℂ => (p.1, (p.2, T'))) (atTop ×ˢ 𝓝[U] x)
        (atTop ×ˢ 𝓝[U ×ˢ univ] (x, T')) :=
      tendsto_fst.prodMk (tendsto_nhdsWithin_iff.2 ⟨hsn.prodMk_nhds tendsto_const_nhds,
        hsU.mono fun p hp => ⟨hp, mem_univ _⟩⟩)
    have hm' : Tendsto (fun p : ℕ × ℂ => (p.1, ρ p.2 - y₁)) (atTop ×ˢ 𝓝[U] x)
        (atTop ×ˢ 𝓝[Us] (ρ x - y₁)) :=
      tendsto_fst.prodMk (tendsto_nhdsWithin_iff.2 ⟨(hρs.tendsto x).comp hsn,
        hsU.mono fun p hp => hUUs _ hp⟩)
    have hqT := ((s04_tc_cc hEc).1 hEL (x, T') ⟨hx, mem_univ _⟩).comp hm
    have hlT := ((s04_tc_cc hlc).1 hlL (ρ x - y₁) (hUUs x hx)).comp hm'
    have hT1 := (continuous_fst.tendsto _).comp hqT
    have hT2 := (continuous_snd.tendsto _).comp hqT
    exact hT2.prodMk_nhds ((hlT.mul ((((hT1.sub tendsto_const_nhds).sub
      ((hρs.tendsto x).comp hsn)).norm.pow 2).add (hT2.pow 2))).sub
        (tendsto_const_nhds.mul hT2))
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hUo).1 hHT Kc hKU hKc
  have hWo : IsOpen {p : ℝ × ℝ | 0 < p.1 ∧ p.2 < 0} :=
    (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_snd continuous_const)
  have hW : (fun v => ((normalGeod (gL '' unitDisc) v T').2,
      poincareDensity (gsL '' unitDisc) (ρ v - y₁) *
        (‖(normalGeod (gL '' unitDisc) v T').1 - y₁ - (ρ v - y₁)‖ ^ 2 +
          (normalGeod (gL '' unitDisc) v T').2 ^ 2) -
        2 * (normalGeod (gL '' unitDisc) v T').2)) '' Kc ⊆
      {p : ℝ × ℝ | 0 < p.1 ∧ p.2 < 0} := by
    rintro _ ⟨v, hv, rfl⟩
    have hvD : v ∈ gL '' unitDisc := hKcD hv
    have hv' : 0 < (α * v + β).im := by
      rw [hD] at hvD
      exact hvD
    have hlam : poincareDensity (gL '' unitDisc) v = ‖α‖ / (1 * (α * v + β).im) :=
      s04_tg_hp_lam α β hα 1 (Or.inl rfl) _ (by rw [hD]; exact s04_tg_hp_up α β) hvD
    have hlp : 0 < poincareDensity (gL '' unitDisc) v := by
      rw [hlam]
      exact div_pos (norm_pos_iff.2 hα) (by linarith)
    have hq2 : 0 < (normalGeod (gL '' unitDisc) v T').2 := by
      show 0 < (poincareDensity (gL '' unitDisc) v * Real.exp (-T') / 2) /
        (‖logDensityDz (gL '' unitDisc) v‖ ^ 2 +
          (poincareDensity (gL '' unitDisc) v * Real.exp (-T') / 2) ^ 2)
      have h0 : 0 < poincareDensity (gL '' unitDisc) v * Real.exp (-T') / 2 :=
        div_pos (mul_pos hlp (Real.exp_pos _)) two_pos
      exact div_pos h0 (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos h0 2))
    have hρv : (α * ρ v + β).im < 0 := by
      rw [hρ, s04_tg_lim_refl hα]
      linarith
    have hls : poincareDensity (gsL '' unitDisc) (ρ v - y₁) =
        poincareDensity {z | (α * z + β).im < 0} (ρ v) := by
      have hΩs : ∀ z, z ∈ gsL '' unitDisc ↔ 0 < (-1 : ℝ) * (α * z + (α * y₁ + β)).im := by
        intro z
        rw [hDs, show α * z + (α * y₁ + β) = α * (z + y₁) + β by ring]
        show (α * (z + y₁) + β).im < 0 ↔ _
        constructor <;> intro h <;> linarith
      rw [s04_tg_hp_lam α (α * y₁ + β) hα (-1) (Or.inr rfl) _ hΩs (hρD v hvD),
        s04_tg_hp_lam α β hα (-1) (Or.inr rfl) _ (s04_tg_hp_low α β) hρv,
        show α * (ρ v - y₁) + (α * y₁ + β) = α * ρ v + β by ring]
    have hh := s04_tg_lim_horo hα hv' T'
    rw [← hD, show v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α = ρ v by rw [hρ]] at hh
    have hh' : poincareDensity {z | (α * z + β).im < 0} (ρ v) *
        (‖(normalGeod (gL '' unitDisc) v T').1 - ρ v‖ ^ 2 +
          (normalGeod (gL '' unitDisc) v T').2 ^ 2) =
        Real.exp (-T') * (2 * (normalGeod (gL '' unitDisc) v T').2) := by
      rw [← div_eq_iff (by positivity)]
      exact hh
    have he1 : Real.exp (-T') < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    refine ⟨hq2, ?_⟩
    show poincareDensity (gsL '' unitDisc) (ρ v - y₁) *
        (‖(normalGeod (gL '' unitDisc) v T').1 - y₁ - (ρ v - y₁)‖ ^ 2 +
          (normalGeod (gL '' unitDisc) v T').2 ^ 2) -
        2 * (normalGeod (gL '' unitDisc) v T').2 < 0
    rw [sub_sub_sub_cancel_right, hls, hh']
    nlinarith
  obtain ⟨δ, hδ, hδW⟩ := (hKc.image_of_continuousOn (hHc.mono hKU)).exists_thickening_subset_open
    hWo hW
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif δ hδ, hsker _ hUsc hUsD] with n hn hn2
  intro v hv
  have hmem := hδW (Metric.mem_thickening_iff.2 ⟨_, mem_image_of_mem _ hv, by
    rw [dist_comm]
    exact hn v hv⟩)
  obtain ⟨h1, h2⟩ := hmem
  have hw' : ρ v - y₁ ∈ (fun z => (c n : ℂ) * z + (b n - y₁)) '' Ωs n :=
    hn2 (subset_closure (hUUs v (hKU hv)))
  have hint := s04_tg_horoT_int hw' h1 (by linarith [h2])
  have ht := (s04_tg_horo ⟨gs n, (hgs n).1⟩ one_pos y₁ _).2 hint
  have hset : (fun z => ((1 : ℝ) : ℂ) * z + y₁) ''
      ((fun z => (c n : ℂ) * z + (b n - y₁)) '' Ωs n) = (fun z => (c n : ℂ) * z + b n) '' Ωs n := by
    rw [image_image]
    congr 1
    funext z
    push_cast
    ring
  rw [hset] at ht
  convert ht using 1
  ext <;> simp

/-- T43 G4: the slab in normalized coordinates: near a compact `Kc ⊆ D`, smooth `t_n → 0` in
`C^∞_loc` and smooth `N_n` with `X*_n(N_n v) = E_n(v, t_n v)`, the only hits of `Σ*_n` along
`E_n(v, [-1, T'+1])` (`s04_tg_conv` on both sides, `s04_tg_lim_*`, `s04_tg_ift`,
`s04_tg_noreturn`). -/
theorem s04_tg_solve {K : ℝ} {Ω Ωs : ℕ → Set ℂ} (hpair : ∀ n, IsKQuasiPair (Ω n) (Ωs n) K)
    (hnl : ∀ n, ¬ IsLinePair (Ω n) (Ωs n)) {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) {b : ℕ → ℂ}
    {y₁ : ℂ} {g gs : ℕ → ℂ → ℂ} {gL gsL : ℂ → ℂ} {α β : ℂ}
    (hg : ∀ n, IsConformalOnto (g n) unitDisc ((fun z => (c n : ℂ) * z + b n) '' Ω n) ∧
      g n 0 = 0)
    (hgL : IsConformalOnto gL unitDisc (gL '' unitDisc)) (hgL0 : gL 0 = 0)
    (hconv : TendstoLocallyUniformlyOn g gL atTop unitDisc)
    (hker : ∀ S : Set ℂ, IsCompact S → S ⊆ gL '' unitDisc →
      ∀ᶠ n in atTop, S ⊆ (fun z => (c n : ℂ) * z + b n) '' Ω n)
    (hgs : ∀ n, IsConformalOnto (gs n) unitDisc
      ((fun z => (c n : ℂ) * z + (b n - y₁)) '' Ωs n) ∧ gs n 0 = 0)
    (hgsL : IsConformalOnto gsL unitDisc (gsL '' unitDisc)) (hgsL0 : gsL 0 = 0)
    (hsconv : TendstoLocallyUniformlyOn gs gsL atTop unitDisc)
    (hsker : ∀ S : Set ℂ, IsCompact S → S ⊆ gsL '' unitDisc →
      ∀ᶠ n in atTop, S ⊆ (fun z => (c n : ℂ) * z + (b n - y₁)) '' Ωs n)
    (hα : α ≠ 0) (hD : gL '' unitDisc = {z | 0 < (α * z + β).im})
    (hDs : gsL '' unitDisc = {z | (α * (z + y₁) + β).im < 0})
    {Kc : Set ℂ} (hKc : IsCompact Kc) (hKcD : Kc ⊆ gL '' unitDisc) (T' : ℝ) :
    ∃ V : Set ℂ, IsOpen V ∧ Kc ⊆ V ∧ IsCompact (closure V) ∧ closure V ⊆ gL '' unitDisc ∧
      ∃ (t : ℕ → ℂ → ℝ) (N : ℕ → ℂ → ℂ),
        ((∀ᶠ n in atTop, ContDiffOn ℝ ∞ (t n) V) ∧ ContDiffOn ℝ ∞ (fun _ : ℂ => (0 : ℝ)) V ∧
          ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (t n))
            (iteratedFDeriv ℝ i (fun _ : ℂ => (0 : ℝ))) atTop V) ∧
        (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (N n) V) ∧
        (∀ᶠ n in atTop, ∀ v ∈ V, N n v ∈ (fun z => (c n : ℂ) * z + b n) '' Ωs n ∧
          epstein ((fun z => (c n : ℂ) * z + b n) '' Ωs n) (N n v) =
            normalGeod ((fun z => (c n : ℂ) * z + b n) '' Ω n) v (t n v)) ∧
        ∀ᶠ n in atTop, ∀ v ∈ V, ∀ τ ∈ Icc (-1) (T' + 1),
          ∀ z ∈ (fun z => (c n : ℂ) * z + b n) '' Ωs n,
            epstein ((fun z => (c n : ℂ) * z + b n) '' Ωs n) z =
                normalGeod ((fun z => (c n : ℂ) * z + b n) '' Ω n) v τ →
              τ = t n v ∧ z = N n v := by
  have hΩs : ∀ n, ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc (Ωs n) := fun n =>
    s02_jordanPair_riemannMap (s02_jordanPair_symm (s03_b0_jordanPair (hpair n)))
  have hDo : IsOpen (gL '' unitDisc) := hgL.isOpen isOpen_ball
  have hDso : IsOpen (gsL '' unitDisc) := hgsL.isOpen isOpen_ball
  obtain ⟨U, hUo, hKU, hUD, hUc⟩ := exists_open_between_and_isCompact_closure hKc hDo hKcD
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℂ → ℂ, ρ = fun v => v - 2 * I * (((α * v + β).im : ℝ) : ℂ) / α :=
    ⟨_, rfl⟩
  have hρd : ContDiff ℝ ∞ ρ := hρ ▸ s04_tg_sv_rho α β
  have hρs : Continuous fun v => ρ v - y₁ := hρd.continuous.sub continuous_const
  have hρv : ∀ v ∈ gL '' unitDisc, 0 < (α * v + β).im ∧ (α * ρ v + β).im < 0 := by
    intro v hv
    rw [hD] at hv
    have hv' : 0 < (α * v + β).im := hv
    refine ⟨hv', ?_⟩
    rw [hρ, s04_tg_lim_refl hα]
    linarith
  have hρD : ∀ v ∈ gL '' unitDisc, ρ v - y₁ ∈ gsL '' unitDisc := by
    intro v hv
    rw [hDs]
    show (α * (ρ v - y₁ + y₁) + β).im < 0
    rw [sub_add_cancel]
    exact (hρv v hv).2
  obtain ⟨Us, hUso, hKUs, hUsD, hUsc⟩ := exists_open_between_and_isCompact_closure
    (hUc.image hρs) hDso (by
      rintro _ ⟨v, hv, rfl⟩
      exact hρD v (hUD hv))
  have hUUs : ∀ v ∈ U, ρ v - y₁ ∈ Us := fun v hv =>
    hKUs (mem_image_of_mem _ (subset_closure hv))
  have hE := (s04_tg_conv hg hgL hgL0 hconv hker hUo hUc hUD).2
  have hX := (s04_tg_conv hgs hgsL hgsL0 hsconv hsker hUso hUsc hUsD).1
  have hWo : IsOpen (univ ×ˢ Us : Set (ℝ × ℂ)) := isOpen_univ.prod hUso
  have hVW : IsOpen (U ×ˢ (univ ×ˢ Us : Set (ℝ × ℂ))) := hUo.prod hWo
  have hπ1 : ContDiffOn ℝ ∞ (fun p : ℂ × (ℝ × ℂ) => (p.1, p.2.1)) (U ×ˢ (univ ×ˢ Us)) :=
    (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).contDiffOn
  have hπ2 : ContDiffOn ℝ ∞ (fun p : ℂ × (ℝ × ℂ) => p.2.2) (U ×ˢ (univ ×ˢ Us)) :=
    (contDiff_snd.comp contDiff_snd).contDiffOn
  have hT1 := s04_tc_comp hVW (hUo.prod isOpen_univ) hE (s04_tc_const hπ1)
    (Eventually.of_forall fun _ p hp => ⟨hp.1, mem_univ _⟩) fun p hp => ⟨hp.1, mem_univ _⟩
  have hT2 := s04_tc_clm hVW (-ContinuousLinearMap.id ℝ (ℂ × ℝ))
    (s04_tc_comp hVW hUso hX (s04_tc_const hπ2) (Eventually.of_forall fun _ p hp => hp.2.2)
      fun p hp => hp.2.2)
  have hF := s04_tc_add hVW (s04_tc_add hVW hT1
    (s04_tc_const (U := U ×ˢ (univ ×ˢ Us)) (contDiffOn_const (c := -(y₁, (0 : ℝ)))))) hT2
  have hyL : ContDiffOn ℝ ∞ (fun v : ℂ => ((0 : ℝ), ρ v - y₁)) U :=
    (contDiff_const.prodMk (hρd.sub contDiff_const)).contDiffOn
  have hyW : MapsTo (fun v : ℂ => ((0 : ℝ), ρ v - y₁)) U (univ ×ˢ Us) := fun v hv =>
    ⟨mem_univ _, hUUs v hv⟩
  have hlimv : ∀ v ∈ U, epstein (gsL '' unitDisc) (ρ v - y₁) =
      ((normalGeod (gL '' unitDisc) v 0).1 - y₁, (normalGeod (gL '' unitDisc) v 0).2) := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := hρv v (hUD (subset_closure hv))
    have h1 := (s04_tg_lim_eq hα hv1 0 hv2).2 ⟨rfl, by rw [hρ]⟩
    have h2 := s04_tg_sv_tr hgsL hDs (hρD v (hUD (subset_closure hv)))
    rw [sub_add_cancel, ← h1, ← hD] at h2
    rw [h2]
    ext <;> simp
  have h0 : ∀ v ∈ U, normalGeod (gL '' unitDisc) v ((0 : ℝ), ρ v - y₁).1 + -(y₁, (0 : ℝ)) +
      -epstein (gsL '' unitDisc) ((0 : ℝ), ρ v - y₁).2 = 0 := by
    intro v hv
    show normalGeod (gL '' unitDisc) v 0 + -(y₁, (0 : ℝ)) +
      -epstein (gsL '' unitDisc) (ρ v - y₁) = 0
    rw [hlimv v hv]
    ext <;> simp
    ring
  have hinv : ∀ v ∈ U, ∃ e : (ℝ × ℂ) ≃L[ℝ] (ℂ × ℝ), (e : ℝ × ℂ →L[ℝ] ℂ × ℝ) =
      fderiv ℝ (fun y : ℝ × ℂ => normalGeod (gL '' unitDisc) v y.1 + -(y₁, (0 : ℝ)) +
        -epstein (gsL '' unitDisc) y.2) ((0 : ℝ), ρ v - y₁) := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := hρv v (hUD (subset_closure hv))
    obtain ⟨e, he⟩ := s04_tg_lim_inv hα hv1
    obtain ⟨G, hG⟩ : ∃ G : ℝ × ℂ → ℂ × ℝ, G = fun y => normalGeod {z | 0 < (α * z + β).im} v y.1 -
        epstein {z | (α * z + β).im < 0} y.2 := ⟨_, rfl⟩
    have hev : (fun y : ℝ × ℂ => normalGeod (gL '' unitDisc) v y.1 + -(y₁, (0 : ℝ)) +
        -epstein (gsL '' unitDisc) y.2) =ᶠ[𝓝 ((0 : ℝ), ρ v - y₁)]
          fun y => G (y + ((0 : ℝ), y₁)) := by
      filter_upwards [(continuous_snd.tendsto ((0 : ℝ), ρ v - y₁)).eventually
        (hDso.mem_nhds (hρD v (hUD (subset_closure hv))))] with y hy
      rw [hG]
      show _ = normalGeod {z | 0 < (α * z + β).im} v (y.1 + 0) -
        epstein {z | (α * z + β).im < 0} (y.2 + y₁)
      rw [s04_tg_sv_tr hgsL hDs hy, add_zero, ← hD]
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, Prod.fst_sub,
        Prod.snd_sub] <;> ring
    refine ⟨e, ?_⟩
    rw [he, hev.fderiv_eq, fderiv_comp_add_right, hG]
    congr 1
    ext <;> simp [hρ]
  obtain ⟨V', hV'o, hKV', hV'U, ε, hε, y, ⟨hy1, hy2, hy3⟩, hysol, hyuniq⟩ :=
    s04_tg_ift hUo hWo hF hyL hyW h0 hinv hKc hKU
  have hV'c : IsCompact (closure V') := hUc.of_isClosed_subset isClosed_closure (closure_mono hV'U)
  have hV'D : closure V' ⊆ gL '' unitDisc := (closure_mono hV'U).trans hUD
  have hnr := s04_tg_noreturn hpair hnl hc hg hgL hgL0 hconv hker hgs hgsL hgsL0 hsconv hsker hα
    hD hDs hV'c hV'D T' hε
  refine ⟨V', hV'o, hKV', hV'c, hV'D, fun n v => (y n v).1, fun n v => (y n v).2 + y₁,
    s04_tc_congr hV'o (s04_tc_clm hV'o (ContinuousLinearMap.fst ℝ ℝ ℂ) ⟨hy1, hy2, hy3⟩)
      (Eventually.of_forall fun _ _ _ => rfl) fun _ _ => rfl,
    hy1.mono fun n hn => ((ContinuousLinearMap.snd ℝ ℝ ℂ).contDiff.comp_contDiffOn hn).add
      contDiffOn_const, ?_, ?_⟩
  · filter_upwards [hysol, hsker _ hUsc hUsD] with n hn hn2 v hv
    obtain ⟨hyW', hF0⟩ := hn v hv
    have hF0' : normalGeod ((fun z => (c n : ℂ) * z + b n) '' Ω n) v (y n v).1 + -(y₁, (0 : ℝ)) +
        -epstein ((fun z => (c n : ℂ) * z + (b n - y₁)) '' Ωs n) (y n v).2 = 0 := hF0
    rw [add_neg_eq_zero] at hF0'
    obtain ⟨ζ, hζ, hζe⟩ := hn2 (subset_closure hyW'.2)
    have hN : (y n v).2 + y₁ ∈ (fun z => (c n : ℂ) * z + b n) '' Ωs n := ⟨ζ, hζ, by
      have h : (c n : ℂ) * ζ + (b n - y₁) = (y n v).2 := hζe
      show (c n : ℂ) * ζ + b n = (y n v).2 + y₁
      rw [← h]
      ring⟩
    have htr := (s04_tg_nr_tr (hΩs n) (hc n) (b n) y₁ hN).2
    rw [add_sub_cancel_right, ← hF0'] at htr
    refine ⟨hN, ?_⟩
    show epstein ((fun z => (c n : ℂ) * z + b n) '' Ωs n) ((y n v).2 + y₁) =
      normalGeod ((fun z => (c n : ℂ) * z + b n) '' Ω n) v (y n v).1
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 htr
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, neg_zero, add_zero] at h1 h2
    exact Prod.ext (by linear_combination -h1) h2.symm
  · filter_upwards [hyuniq, hnr] with n hu hnr' v hv τ hτ z hz heqz
    obtain ⟨h1, h2⟩ := hnr' v (subset_closure hv) τ hτ z hz heqz
    have hzeq := (s04_tg_nr_tr (hΩs n) (hc n) (b n) y₁ hz).2
    have hFz : normalGeod ((fun z => (c n : ℂ) * z + b n) '' Ω n) v (τ, z - y₁).1 +
        -(y₁, (0 : ℝ)) + -epstein ((fun z => (c n : ℂ) * z + (b n - y₁)) '' Ωs n) (τ, z - y₁).2 =
          0 := by
      show normalGeod ((fun z => (c n : ℂ) * z + b n) '' Ω n) v τ + -(y₁, (0 : ℝ)) +
        -epstein ((fun z => (c n : ℂ) * z + (b n - y₁)) '' Ωs n) (z - y₁) = 0
      rw [hzeq, heqz]
      ext <;> simp
      ring
    have hd : dist (τ, z - y₁) ((0 : ℝ), ρ v - y₁) < ε := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [Real.dist_eq, sub_zero]
        exact h1
      · rw [dist_sub_right, hρ]
        exact h2
    have heq := hu v hv (τ, z - y₁) hd hFz
    have h4 : z - y₁ = (y n v).2 := congrArg Prod.snd heq
    refine ⟨congrArg Prod.fst heq, ?_⟩
    show z = (y n v).2 + y₁
    rw [← h4]
    ring

/-- T43 G4 helper: `s04_tg_pos` after a real similarity `A z = c z + b` of the pair. -/
theorem s04_tg_sc_pos {K : ℝ} {Ω Ωs : Set ℂ} (hpair : IsKQuasiPair Ω Ωs K)
    (hnl : ¬ IsLinePair Ω Ωs) {c : ℝ} (hc : 0 < c) (b : ℂ) {v : ℂ}
    (hv : v ∈ (fun z => (c : ℂ) * z + b) '' Ω) {τ : ℝ} (hτ : τ ≤ 0) {z : ℂ}
    (hz : z ∈ (fun z => (c : ℂ) * z + b) '' Ωs) :
    epstein ((fun z => (c : ℂ) * z + b) '' Ωs) z ≠
      normalGeod ((fun z => (c : ℂ) * z + b) '' Ω) v τ := by
  have hΩ := s02_jordanPair_riemannMap (s03_b0_jordanPair hpair)
  have hΩs := s02_jordanPair_riemannMap (s03_b0_jordanPair (s03_qce_swap hpair))
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hnc : ‖(c : ℂ)‖ = c := by rw [Complex.norm_real, Real.norm_of_nonneg hc.le]
  obtain ⟨w, hw, rfl⟩ := hv
  obtain ⟨ζ, hζ, rfl⟩ := hz
  show epstein ((fun z => (c : ℂ) * z + b) '' Ωs) ((c : ℂ) * ζ + b) ≠
    normalGeod ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * w + b) τ
  rw [subsec_epstein_natural_affine hΩs hc' hζ, s04_tg_geod hΩ hc b hw τ, hnc]
  intro he
  apply s04_tg_pos hpair hnl hw hτ hζ
  have h1 : (c : ℂ) * (epstein Ωs ζ).1 + b = (c : ℂ) * (normalGeod Ω w τ).1 + b :=
    congrArg Prod.fst he
  have h2 : c * (epstein Ωs ζ).2 = c * (normalGeod Ω w τ).2 := congrArg Prod.snd he
  exact Prod.ext (mul_left_cancel₀ hc' (add_right_cancel h1)) (mul_left_cancel₀ hc.ne' h2)

/-- T43 G4 (public, for `lem_graph_operator_c`): in normalized coordinates the slab thickness
`slabTop` of `(A_n Ω_n, A_n Ω*_n)` tends to `0` in `C^∞_loc` in the coordinate sense
(`iteratedFDeriv`) near every compact of the limit half-plane (`s04_tg_solve`, `s04_tg_ident`,
`s04_tg_pos`). -/
theorem s04_tg_slabconv {K : ℝ} {Ω Ωs : ℕ → Set ℂ} (hpair : ∀ n, IsKQuasiPair (Ω n) (Ωs n) K)
    (hnl : ∀ n, ¬ IsLinePair (Ω n) (Ωs n)) {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) {b : ℕ → ℂ}
    {y₁ : ℂ} {g gs : ℕ → ℂ → ℂ} {gL gsL : ℂ → ℂ} {α β : ℂ}
    (hg : ∀ n, IsConformalOnto (g n) unitDisc ((fun z => (c n : ℂ) * z + b n) '' Ω n) ∧
      g n 0 = 0)
    (hgL : IsConformalOnto gL unitDisc (gL '' unitDisc)) (hgL0 : gL 0 = 0)
    (hconv : TendstoLocallyUniformlyOn g gL atTop unitDisc)
    (hker : ∀ S : Set ℂ, IsCompact S → S ⊆ gL '' unitDisc →
      ∀ᶠ n in atTop, S ⊆ (fun z => (c n : ℂ) * z + b n) '' Ω n)
    (hgs : ∀ n, IsConformalOnto (gs n) unitDisc
      ((fun z => (c n : ℂ) * z + (b n - y₁)) '' Ωs n) ∧ gs n 0 = 0)
    (hgsL : IsConformalOnto gsL unitDisc (gsL '' unitDisc)) (hgsL0 : gsL 0 = 0)
    (hsconv : TendstoLocallyUniformlyOn gs gsL atTop unitDisc)
    (hsker : ∀ S : Set ℂ, IsCompact S → S ⊆ gsL '' unitDisc →
      ∀ᶠ n in atTop, S ⊆ (fun z => (c n : ℂ) * z + (b n - y₁)) '' Ωs n)
    (hα : α ≠ 0) (hD : gL '' unitDisc = {z | 0 < (α * z + β).im})
    (hDs : gsL '' unitDisc = {z | (α * (z + y₁) + β).im < 0})
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsCompact (closure U))
    (hUD : closure U ⊆ gL '' unitDisc) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞
        (slabTop ((fun z => (c n : ℂ) * z + b n) '' Ω n) ((fun z => (c n : ℂ) * z + b n) '' Ωs n)) U) ∧
      ContDiffOn ℝ ∞ (fun _ : ℂ => (0 : ℝ)) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ i (slabTop ((fun z => (c n : ℂ) * z + b n) '' Ω n) ((fun z => (c n : ℂ) * z + b n) '' Ωs n)))
        (iteratedFDeriv ℝ i (fun _ : ℂ => (0 : ℝ))) atTop U := by
  obtain ⟨V, hVo, hUV, -, -, t, N, ht, -, hmem, huniq⟩ := s04_tg_solve hpair hnl hc hg hgL hgL0
    hconv hker hgs hgsL hgsL0 hsconv hsker hα hD hDs hUc hUD 1
  have hUV' : U ⊆ V := subset_closure.trans hUV
  obtain ⟨ht1, ht2, ht3⟩ := ht
  have htU : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (t n) U) ∧ ContDiffOn ℝ ∞ (fun _ : ℂ => (0 : ℝ)) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (t n))
        (iteratedFDeriv ℝ i (fun _ : ℂ => (0 : ℝ))) atTop U :=
    ⟨ht1.mono fun n hn => hn.mono hUV', ht2.mono hUV', fun i => (ht3 i).mono hUV'⟩
  have hun := s04_tc_unif hVo ⟨ht1, ht2, ht3⟩ hUc hUV
  have hsm := Metric.tendstoUniformlyOn_iff.1 hun 1 one_pos
  refine s04_tc_congr hU htU ?_ fun _ _ => rfl
  filter_upwards [hsm, hker (closure U) hUc hUD, hmem, huniq] with n hs hk hm hu v hv
  have hvV : v ∈ V := hUV' hv
  obtain ⟨hN, heq⟩ := hm v hvV
  have htpos : 0 < t n v := by
    by_contra hneg
    exact s04_tg_sc_pos (hpair n) (hnl n) (hc n) (b n) (hk (subset_closure hv))
      (not_lt.1 hneg) hN heq
  have hd := hs v (subset_closure hv)
  rw [Real.dist_eq, zero_sub, abs_neg] at hd
  have htle : t n v ≤ 1 + 1 := by linarith [le_abs_self (t n v)]
  exact (s04_tg_ident htpos htle hN heq fun τ hτ z' hz' he' =>
    hu v hvV τ ⟨by linarith [hτ.1], hτ.2⟩ z' hz' he').1

/-! ### G5: pull-back to the original coordinates (deterministic, one `n`) -/

/-- T43 G5 helper: `X* = E` is invariant under a real similarity `A z = c z + b` of the pair. -/
theorem s04_tg_pl_eq {Ω Ωs : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    (hΩs : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ωs) {c : ℝ} (hc : 0 < c) (b : ℂ) {v ζ : ℂ}
    (hv : v ∈ Ω) (hζ : ζ ∈ Ωs) (τ : ℝ) :
    epstein ((fun z => (c : ℂ) * z + b) '' Ωs) ((c : ℂ) * ζ + b) =
        normalGeod ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * v + b) τ ↔
      epstein Ωs ζ = normalGeod Ω v τ := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hnc : ‖(c : ℂ)‖ = c := by rw [Complex.norm_real, Real.norm_of_nonneg hc.le]
  rw [subsec_epstein_natural_affine hΩs hc' hζ, s04_tg_geod hΩ hc b hv τ, hnc]
  constructor
  · intro he
    have h1 : (c : ℂ) * (epstein Ωs ζ).1 + b = (c : ℂ) * (normalGeod Ω v τ).1 + b :=
      congrArg Prod.fst he
    have h2 : c * (epstein Ωs ζ).2 = c * (normalGeod Ω v τ).2 := congrArg Prod.snd he
    exact Prod.ext (mul_left_cancel₀ hc' (add_right_cancel h1)) (mul_left_cancel₀ hc.ne' h2)
  · intro he
    rw [he]

/-- T43 G5 helper: at one point `v`, `slabTop`/`slabMap` of the original pair from a normalized
solution `(t, N)` of `X* ∘ N = E ∘ (id, t)` at `A v`, unique on `[-1, T' + 1]`. -/
theorem s04_tg_pl_pt {K : ℝ} {Ω Ωs : Set ℂ} (hpair : IsKQuasiPair Ω Ωs K)
    (hnl : ¬ IsLinePair Ω Ωs) {c : ℝ} (hc : 0 < c) (b : ℂ) {T' : ℝ} (hT' : 0 < T') {v : ℂ}
    (hv : v ∈ Ω) {t : ℝ} {N : ℂ} (hsm : t < 1) (hN : N ∈ (fun z => (c : ℂ) * z + b) '' Ωs)
    (heq : epstein ((fun z => (c : ℂ) * z + b) '' Ωs) N =
      normalGeod ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * v + b) t)
    (huniq : ∀ τ ∈ Icc (-1) (T' + 1), ∀ z ∈ (fun z => (c : ℂ) * z + b) '' Ωs,
      epstein ((fun z => (c : ℂ) * z + b) '' Ωs) z =
          normalGeod ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * v + b) τ → τ = t ∧ z = N) :
    0 < t ∧ slabTop Ω Ωs v = t ∧ slabMap Ω Ωs v = (N - b) / c ∧ (N - b) / c ∈ Ωs ∧
      epstein Ωs ((N - b) / c) = normalGeod Ω v t := by
  have hΩ := s02_jordanPair_riemannMap (s03_b0_jordanPair hpair)
  have hΩs := s02_jordanPair_riemannMap (s03_b0_jordanPair (s03_qce_swap hpair))
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  obtain ⟨ζ, hζ, hζN⟩ := hN
  have hζN' : (c : ℂ) * ζ + b = N := hζN
  have hz0 : (N - b) / c = ζ := by
    rw [← hζN', add_sub_cancel_right, mul_div_cancel_left₀ _ hc']
  rw [hz0]
  rw [← hζN'] at heq huniq
  have he := (s04_tg_pl_eq hΩ hΩs hc b hv hζ t).1 heq
  have htpos : 0 < t := by
    by_contra hneg
    exact s04_tg_pos hpair hnl hv (not_lt.1 hneg) hζ he
  have hu : ∀ τ ∈ Icc 0 (T' + 1), ∀ z' ∈ Ωs, epstein Ωs z' = normalGeod Ω v τ →
      τ = t ∧ z' = ζ := by
    intro τ hτ z' hz' he'
    obtain ⟨h1, h2⟩ := huniq τ ⟨by linarith [hτ.1], hτ.2⟩ ((c : ℂ) * z' + b) ⟨z', hz', rfl⟩
      ((s04_tg_pl_eq hΩ hΩs hc b hv hz' τ).2 he')
    exact ⟨h1, mul_left_cancel₀ hc' (add_right_cancel h2)⟩
  obtain ⟨h1, h2⟩ := s04_tg_ident htpos (by linarith) hζ he hu
  exact ⟨htpos, h1, h2, hζ, he⟩

/-- T43 G5: the conclusion of `s04_tb_graph` at one parameter, from the normalized slab data
(`slabTop`, `slabMap` by `s04_tg_ident`; embedding by `s04_tb_E_inj`, `s04_tg_imm`,
`s04_tb_embed_of_compact`; norms by `s04_tn_cj`, `s04_tg_cjlocal`). -/
theorem s04_tg_pull {K : ℝ} {Ω Ωs : Set ℂ} (hpair : IsKQuasiPair Ω Ωs K)
    (hnl : ¬ IsLinePair Ω Ωs) {w : ℂ} (hw : w ∈ Ω) {c : ℝ} (hc : 0 < c) {b : ℂ}
    (hcb : (c : ℂ) * w + b = 0) {r T' δ : ℝ} (hT' : 0 < T') (hδ : 0 < δ) (j : ℕ)
    (hs : ∀ w' ∈ Ω, poincareDist Ω w w' ≤ 3 * r → schwarzNorm Ω w' < 1 / 2)
    {V : Set ℂ} (hV : IsOpen V) (hVΩ : V ⊆ (fun z => (c : ℂ) * z + b) '' Ω)
    (hball : rhoClosedBall ((fun z => (c : ℂ) * z + b) '' Ω) 0 r ⊆ V)
    {t : ℂ → ℝ} {N : ℂ → ℂ} (ht : ContDiffOn ℝ ∞ t V) (hN : ContDiffOn ℝ ∞ N V)
    (hsmall : ∀ v ∈ V, t v < min δ 1)
    (heq : ∀ v ∈ V, N v ∈ (fun z => (c : ℂ) * z + b) '' Ωs ∧
      epstein ((fun z => (c : ℂ) * z + b) '' Ωs) (N v) =
        normalGeod ((fun z => (c : ℂ) * z + b) '' Ω) v (t v))
    (huniq : ∀ v ∈ V, ∀ τ ∈ Icc (-1) (T' + 1), ∀ z ∈ (fun z => (c : ℂ) * z + b) '' Ωs,
      epstein ((fun z => (c : ℂ) * z + b) '' Ωs) z =
          normalGeod ((fun z => (c : ℂ) * z + b) '' Ω) v τ → τ = t v ∧ z = N v)
    (hcj : rhoCjNorm ((fun z => (c : ℂ) * z + b) '' Ω) j (scalarField t)
      (rhoClosedBall ((fun z => (c : ℂ) * z + b) '' Ω) 0 r) ≤ ENNReal.ofReal δ)
    (hhoro : ∀ v ∈ rhoClosedBall ((fun z => (c : ℂ) * z + b) '' Ω) 0 r,
      normalGeod ((fun z => (c : ℂ) * z + b) '' Ω) v T' ∈
        interior (horoUnion ((fun z => (c : ℂ) * z + b) '' Ωs))) :
    SmoothNear (slabTop Ω Ωs) (rhoClosedBall Ω w r) ∧
      IsSmoothEmbeddingOn (slabMap Ω Ωs) (rhoClosedBall Ω w r) ∧
      MapsTo (slabMap Ω Ωs) (rhoClosedBall Ω w r) Ωs ∧
      rhoCjNorm Ω j (scalarField (slabTop Ω Ωs)) (rhoClosedBall Ω w r) ≤ ENNReal.ofReal δ ∧
      (∀ v ∈ rhoClosedBall Ω w r,
        0 < slabTop Ω Ωs v ∧ slabTop Ω Ωs v < δ ∧
          epstein Ωs (slabMap Ω Ωs v) = normalGeod Ω v (slabTop Ω Ωs v)) ∧
      {z | z ∈ Ωs ∧ epstein Ωs z ∈ normalMap Ω '' (rhoClosedBall Ω w r ×ˢ Icc (-1) (T' + 1))} =
        slabMap Ω Ωs '' rhoClosedBall Ω w r ∧
      ∀ v ∈ rhoClosedBall Ω w r, normalGeod Ω v T' ∈ interior (horoUnion Ωs) := by
  have _h := hδ
  have hΩ := s02_jordanPair_riemannMap (s03_b0_jordanPair hpair)
  have hΩs := s02_jordanPair_riemannMap (s03_b0_jordanPair (s03_qce_swap hpair))
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap (s03_b0_jordanPair hpair)
  obtain ⟨fs, hfs⟩ := s02_jordanPair_riemannMap (s03_b0_jordanPair (s03_qce_swap hpair))
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hΩso : IsOpen Ωs := hfs.isOpen isOpen_ball
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hAc : Continuous fun z : ℂ => (c : ℂ) * z + b := by fun_prop
  have hAd : ContDiff ℝ ∞ fun z : ℂ => (c : ℂ) * z + b :=
    (contDiff_const.mul contDiff_id).add contDiff_const
  set V0 := (fun z : ℂ => (c : ℂ) * z + b) ⁻¹' V with hV0
  have hV0o : IsOpen V0 := hV.preimage hAc
  have hV0Ω : V0 ⊆ Ω := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hVΩ hx
    have hxy' : (c : ℂ) * y + b = (c : ℂ) * x + b := hxy
    have hyx : y = x := mul_left_cancel₀ hc' (add_right_cancel hxy')
    exact hyx ▸ hy
  have hballΩ : ∀ x ∈ rhoClosedBall Ω w r,
      (c : ℂ) * x + b ∈ rhoClosedBall ((fun z => (c : ℂ) * z + b) '' Ω) 0 r := by
    intro x hx
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    have hd := s04_tn_dist Ω hc' b w x
    rw [hcb] at hd
    show poincareDist ((fun z => (c : ℂ) * z + b) '' Ω) 0 ((c : ℂ) * x + b) ≤ r
    rw [hd]
    exact hx.2
  have hbV0 : rhoClosedBall Ω w r ⊆ V0 := fun x hx => hball (hballΩ x hx)
  have hpt : ∀ x ∈ V0, 0 < t ((c : ℂ) * x + b) ∧ slabTop Ω Ωs x = t ((c : ℂ) * x + b) ∧
      slabMap Ω Ωs x = (N ((c : ℂ) * x + b) - b) / c ∧ (N ((c : ℂ) * x + b) - b) / c ∈ Ωs ∧
      epstein Ωs ((N ((c : ℂ) * x + b) - b) / c) = normalGeod Ω x (t ((c : ℂ) * x + b)) :=
    fun x hx => s04_tg_pl_pt hpair hnl hc b hT' (hV0Ω hx)
      ((hsmall _ hx).trans_le (min_le_right _ _)) (heq _ hx).1 (heq _ hx).2 (huniq _ hx)
  have hT0 : ContDiffOn ℝ ∞ (fun x => t ((c : ℂ) * x + b)) V0 :=
    ht.comp hAd.contDiffOn fun x hx => hx
  have hM0 : ContDiffOn ℝ ∞ (fun x => (N ((c : ℂ) * x + b) - b) / c) V0 :=
    ((hN.comp hAd.contDiffOn fun x hx => hx).sub contDiffOn_const).div_const _
  have hsT : ContDiffOn ℝ ∞ (slabTop Ω Ωs) V0 := hT0.congr fun x hx => (hpt x hx).2.1
  have hsM : ContDiffOn ℝ ∞ (slabMap Ω Ωs) V0 := hM0.congr fun x hx => (hpt x hx).2.2.1
  have hxs : ∀ x ∈ rhoClosedBall Ω w r, schwarzNorm Ω x < 1 / 2 := by
    intro x hx
    refine hs x hx.1 ?_
    have h0 := s02_poincareDist_nonneg hΩ hw hx.1
    have h1 : poincareDist Ω w x ≤ r := hx.2
    linarith
  have hinj : InjOn (slabMap Ω Ωs) (rhoClosedBall Ω w r) := by
    intro x hx y hy hxy
    have hE := s04_tb_E_inj hpair hnl hw hs
    have hx' := hpt x (hbV0 hx)
    have hy' := hpt y (hbV0 hy)
    have h : normalMap Ω (x, t ((c : ℂ) * x + b)) = normalMap Ω (y, t ((c : ℂ) * y + b)) := by
      show normalGeod Ω x (t ((c : ℂ) * x + b)) = normalGeod Ω y (t ((c : ℂ) * y + b))
      rw [← hx'.2.2.2.2, ← hy'.2.2.2.2, ← hx'.2.2.1, ← hy'.2.2.1, hxy]
    exact congrArg Prod.fst (hE ⟨hx, mem_univ _⟩ ⟨hy, mem_univ _⟩ h)
  have himm : ∀ x ∈ rhoClosedBall Ω w r, Function.Injective (fderiv ℝ (slabMap Ω Ωs) x) := by
    intro x hx
    have hx0 := hbV0 hx
    have hm := (hpt x hx0).2.2.2.1
    rw [← (hpt x hx0).2.2.1] at hm
    refine s04_tg_imm (t := slabTop Ω Ωs)
      ((hsM.contDiffAt (hV0o.mem_nhds hx0)).differentiableAt (by simp))
      ((hsT.contDiffAt (hV0o.mem_nhds hx0)).differentiableAt (by simp))
      (((lem_fff_smooth hΩs).contDiffAt (hΩso.mem_nhds hm)).differentiableAt (by simp))
      (((s04_tb_nm_smooth hf).contDiffAt
        ((hΩo.prod isOpen_univ).mem_nhds ⟨hx.1, mem_univ _⟩)).differentiableAt (by simp))
      (Filter.mem_of_superset (hV0o.mem_nhds hx0) fun y hy => ?_)
      (s04_tb_E_imm hf hx.1 (hxs x hx) _)
    show epstein Ωs (slabMap Ω Ωs y) = normalGeod Ω y (slabTop Ω Ωs y)
    rw [(hpt y hy).2.2.1, (hpt y hy).2.1]
    exact (hpt y hy).2.2.2.2
  have himg : (fun z => (c : ℂ) * z + b) '' rhoClosedBall Ω w r =
      rhoClosedBall ((fun z => (c : ℂ) * z + b) '' Ω) 0 r := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hballΩ x hx
    · rintro ⟨⟨x, hx, rfl⟩, hd⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      have hd' : poincareDist ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * w + b)
          ((c : ℂ) * x + b) ≤ r := by
        rw [hcb]
        exact hd
      rw [s04_tn_dist Ω hc' b w x] at hd'
      exact hd'
  have e1 := s04_tg_cjlocal Ω hV0o hbV0 (T := scalarField (slabTop Ω Ωs))
    (T' := scalarField fun x => t ((c : ℂ) * x + b)) (fun x hx _ => (hpt x hx).2.1) j
  have e2 := s04_tn_cj hΩo hc (b := b) (Ω' := (fun z => (c : ℂ) * z + b) '' Ω)
    (T := scalarField fun x => t ((c : ℂ) * x + b)) (T' := scalarField t) (fun x _ u => rfl)
    (fun x hx => (s04_tn_lambda hΩ hc b hx).2) (fun x hx => (s04_tn_lambda hΩ hc b hx).1)
    (fun x u i a => i.elim0) j (E := rhoClosedBall Ω w r) fun x hx => hx.1
  refine ⟨⟨V0, hV0o, hbV0, hsT⟩, ⟨⟨V0, hV0o, hbV0, hsM⟩, hinj, himm,
    s04_tb_embed_of_compact (s04_tb_ball_compact (s03_b0_jordanPair hpair) hw r) subset_rfl
      (hsM.continuousOn.mono hbV0) hinj⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [(hpt x (hbV0 hx)).2.2.1]
    exact (hpt x (hbV0 hx)).2.2.2.1
  · rw [e1, ← e2, himg]
    exact hcj
  · intro x hx
    obtain ⟨h0, h1, h2, -, h4⟩ := hpt x (hbV0 hx)
    rw [h1, h2]
    exact ⟨h0, (hsmall _ (hbV0 hx)).trans_le (min_le_left _ _), h4⟩
  · ext z
    constructor
    · rintro ⟨hz, ⟨x, τ⟩, ⟨hx, hτ⟩, hE⟩
      have hx0 := hbV0 hx
      have hE' : epstein Ωs z = normalGeod Ω x τ := hE.symm
      obtain ⟨-, h2⟩ := huniq ((c : ℂ) * x + b) hx0 τ hτ ((c : ℂ) * z + b) ⟨z, hz, rfl⟩
        ((s04_tg_pl_eq hΩ hΩs hc b hx.1 hz τ).2 hE')
      refine ⟨x, hx, ?_⟩
      rw [(hpt x hx0).2.2.1, ← h2, add_sub_cancel_right, mul_div_cancel_left₀ _ hc']
    · rintro ⟨x, hx, rfl⟩
      have hx0 := hbV0 hx
      obtain ⟨h0, -, h2, h3, h4⟩ := hpt x hx0
      have hsm := hsmall _ hx0
      have hm1 := min_le_right δ 1
      rw [h2]
      exact ⟨h3, (x, t ((c : ℂ) * x + b)), ⟨hx, by linarith, by linarith⟩, h4.symm⟩
  · intro x hx
    have h := hhoro _ (hballΩ x hx)
    rw [s04_tg_geod hΩ hc b hx.1 T'] at h
    exact (s04_tg_horo hΩs hc b (normalGeod Ω x T')).1 h

/-- T40 stage (i), estimate part (compactness, W-CJ): along `(η n, R n)`-good parameters with
`η n → 0`, `R n → ∞`, for every order `j`, radius `r` and `δ > 0`, eventually
`‖I - ρ‖_{C^j(B_ρ(w n, r))} + ‖B‖_{C^j(B_ρ(w n, r))} ≤ δ`. -/
theorem s04_tb_X_norm {K : ℝ} (hK : 1 ≤ K) {Ω Ωs : ℕ → Set ℂ} {w : ℕ → ℂ} {η R : ℕ → ℝ}
    (hpair : ∀ n, IsKQuasiPair (Ω n) (Ωs n) K) (hnl : ∀ n, ¬ IsLinePair (Ω n) (Ωs n))
    (hgood : ∀ᶠ n in atTop, IsGoodParam (Ω n) (Ωs n) (η n) (R n) (w n))
    (hη : Tendsto η atTop (𝓝 0)) (hR : Tendsto R atTop atTop) (j : ℕ) {r δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      rhoCjNorm (Ω n) j (fffT (Ω n) - rhoMetricT (Ω n)) (rhoBall (Ω n) (w n) r) +
          rhoCjNorm (Ω n) j (shapeT (Ω n)) (rhoBall (Ω n) (w n) r) ≤ ENNReal.ofReal δ := by
  refine s04_tb_subseq fun φ hφ => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.mp hgood
  have hmono : StrictMono fun n => φ (n + N) :=
    hφ.comp fun a b h => Nat.add_lt_add_right h N
  have hgood' : ∀ n, IsGoodParam (Ω (φ (n + N))) (Ωs (φ (n + N))) (η (φ (n + N)))
      (R (φ (n + N))) (w (φ (n + N))) :=
    fun n => hN _ ((Nat.le_add_left N n).trans (hφ.id_le _))
  obtain ⟨χ, hχ, c, b, g, gL, hcb, hg, hgL, hgL0, hconv, hker⟩ :=
    s04_tp_seq hK (fun n => Ω (φ (n + N))) (fun n => Ωs (φ (n + N))) (fun n => hpair _)
      (fun n => w (φ (n + N))) (fun n => (hgood' n).1)
  refine ⟨fun n => χ n + N, fun a b h => Nat.add_lt_add_right (hχ h) N, ?_⟩
  have hflat := s04_tp_flat (Ω := fun n => Ω (φ (n + N))) (Ωs := fun n => Ωs (φ (n + N)))
    (w := fun n => w (φ (n + N))) (η := fun n => η (φ (n + N))) (R := fun n => R (φ (n + N)))
    hK (fun n => hpair _) (fun n => hnl _) hgood' (hη.comp hmono.tendsto_atTop)
    (hR.comp hmono.tendsto_atTop) hχ hcb hg hgL hconv
  obtain ⟨Kb, hKb, hKbD, hball⟩ := s04_tp_ball hg hgL hgL0 hconv r
  have hDo : IsOpen (gL '' unitDisc) := hgL.isOpen isOpen_ball
  obtain ⟨V, hVo, hKV, hVD, hVc⟩ := exists_open_between_and_isCompact_closure hKb hDo hKbD
  have hlam_ := s04_td_lambda hg hgL hgL0 hconv hker hVo hVc hVD
  have hG := s04_td_grad hg hgL hgL0 hconv hker hVo hVc hVD
  obtain ⟨hT1, hT2⟩ := s04_td_tensors hg hgL hgL0 hconv hker hVo hVc hVD hflat
  have hW1 := s04_tw_iter (T := fun n => fffT ((fun z => (c n : ℂ) * z + b n) ''
    Ω (φ (χ n + N))) - rhoMetricT ((fun z => (c n : ℂ) * z + b n) '' Ω (φ (χ n + N))))
    (TL := 0) hVo hT1 hG
  have hW2 := s04_tw_iter (T := fun n => shapeT ((fun z => (c n : ℂ) * z + b n) ''
    Ω (φ (χ n + N)))) (TL := 0) hVo hT2 hG
  have hpos : ∀ x ∈ V, 0 < poincareDensity (gL '' unitDisc) x := fun x hx =>
    s02_poincareDensity_pos ⟨gL, hgL⟩ (hVD (subset_closure hx))
  have hδ2 : ∀ i ≤ j, ∀ x ∈ Kb, rhoTensorNorm (gL '' unitDisc)
      (rhoIterCovDeriv (gL '' unitDisc) i (0 : TensorField 2)) x < δ / 2 := by
    intro i _ x _
    have h0 : rhoIterCovDeriv (gL '' unitDisc) i (0 : TensorField 2) = 0 :=
      funext fun x => funext fun v => s04_tw_zero _ i x v
    rw [h0]
    simp only [rhoTensorNorm, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero, Real.sqrt_zero, zero_div]
    positivity
  have e1 := s04_tw_cj hVo hKb hKV hW1 hlam_ hpos j hδ2
  have e2 := s04_tw_cj hVo hKb hKV hW2 hlam_ hpos j hδ2
  filter_upwards [e1, e2, hball] with n h1 h2 hb
  obtain ⟨hc, hcw⟩ := hcb n
  have hwm : w (φ (χ n + N)) ∈ Ω (φ (χ n + N)) := (hgood' (χ n)).1
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap (s03_b0_jordanPair (hpair (φ (χ n + N))))
  have hΩo : IsOpen (Ω (φ (χ n + N))) := hf.isOpen isOpen_ball
  obtain ⟨hr1, hr2, hh1, hh2⟩ := s04_tn_fields ⟨f, hf⟩ hc (b n)
  have hlam := fun x (hx : x ∈ Ω (φ (χ n + N))) => s04_tn_lambda ⟨f, hf⟩ hc (b n) hx
  have hsub : rhoBall (Ω (φ (χ n + N))) (w (φ (χ n + N))) r ⊆ Ω (φ (χ n + N)) :=
    fun x hx => hx.1
  have k1 := s04_tn_cj hΩo hc hr1 (fun x hx => (hlam x hx).2) (fun x hx => (hlam x hx).1)
    hh1 j hsub
  have k2 := s04_tn_cj hΩo hc hr2 (fun x hx => (hlam x hx).2) (fun x hx => (hlam x hx).1)
    hh2 j hsub
  have hb' : (fun z => (c n : ℂ) * z + b n) ''
      rhoBall (Ω (φ (χ n + N))) (w (φ (χ n + N))) r ⊆ Kb := by
    rw [← s04_tn_ball ⟨f, hf⟩ hc (b n) hwm r, hcw]
    exact fun x hx => hb ⟨hx.1, hx.2.le⟩
  rw [← k1, ← k2]
  calc _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
        add_le_add ((s04_tb_cj_mono _ _ le_rfl hb').trans h1)
          ((s04_tb_cj_mono _ _ le_rfl hb').trans h2)
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

/-- T40 stage (iii) (compactness): along `(η n, R n)`-good parameters with `η n → 0`,
`R n → ∞`, for every radius `r`, length `T' > 0`, order `j` and `δ > 0`, eventually on
`\overline{B_ρ(w n, r)}`: `t = slabTop` is smooth near the ball, `N = slabMap` is a smooth
embedding into `Ω*`, `‖t‖_{C^j} ≤ δ`, `0 < t < δ`, `X*(N v) = E(v, t v)`, the part of `Σ*` in the
tube `E(\overline{B} × [-1, T'+1])` is exactly `N(\overline{B})`, and `E(v, T') ∈ int U*`. -/
theorem s04_tb_graph {K : ℝ} (hK : 1 ≤ K) {Ω Ωs : ℕ → Set ℂ} {w : ℕ → ℂ} {η R : ℕ → ℝ}
    (hpair : ∀ n, IsKQuasiPair (Ω n) (Ωs n) K) (hnl : ∀ n, ¬ IsLinePair (Ω n) (Ωs n))
    (hgood : ∀ᶠ n in atTop, IsGoodParam (Ω n) (Ωs n) (η n) (R n) (w n))
    (hη : Tendsto η atTop (𝓝 0)) (hR : Tendsto R atTop atTop) {r T' δ : ℝ} (hT' : 0 < T')
    (hδ : 0 < δ) (j : ℕ) :
    ∀ᶠ n in atTop,
      SmoothNear (slabTop (Ω n) (Ωs n)) (rhoClosedBall (Ω n) (w n) r) ∧
      IsSmoothEmbeddingOn (slabMap (Ω n) (Ωs n)) (rhoClosedBall (Ω n) (w n) r) ∧
      MapsTo (slabMap (Ω n) (Ωs n)) (rhoClosedBall (Ω n) (w n) r) (Ωs n) ∧
      rhoCjNorm (Ω n) j (scalarField (slabTop (Ω n) (Ωs n))) (rhoClosedBall (Ω n) (w n) r) ≤
        ENNReal.ofReal δ ∧
      (∀ v ∈ rhoClosedBall (Ω n) (w n) r,
        0 < slabTop (Ω n) (Ωs n) v ∧ slabTop (Ω n) (Ωs n) v < δ ∧
          epstein (Ωs n) (slabMap (Ω n) (Ωs n) v) =
            normalGeod (Ω n) v (slabTop (Ω n) (Ωs n) v)) ∧
      {z | z ∈ Ωs n ∧ epstein (Ωs n) z ∈
          normalMap (Ω n) '' (rhoClosedBall (Ω n) (w n) r ×ˢ Icc (-1) (T' + 1))} =
        slabMap (Ω n) (Ωs n) '' rhoClosedBall (Ω n) (w n) r ∧
      ∀ v ∈ rhoClosedBall (Ω n) (w n) r, normalGeod (Ω n) v T' ∈ interior (horoUnion (Ωs n)) := by
  refine s04_tb_subseq fun φ hφ => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.mp hgood
  have hmono : StrictMono fun n => φ (n + N) :=
    hφ.comp fun a b h => Nat.add_lt_add_right h N
  have hgood' : ∀ n, IsGoodParam (Ω (φ (n + N))) (Ωs (φ (n + N))) (η (φ (n + N)))
      (R (φ (n + N))) (w (φ (n + N))) :=
    fun n => hN _ ((Nat.le_add_left N n).trans (hφ.id_le _))
  obtain ⟨χ, hχ, c, b, y₁, g, gs, gL, gsL, α, β, hcb, hg, hgL, hgL0, hconv, hker, hgs, hgsL,
      hgsL0, hsconv, hsker, hα, hD, hDs⟩ :=
    s04_tg_seq (Ω := fun n => Ω (φ (n + N))) (Ωs := fun n => Ωs (φ (n + N)))
      (w := fun n => w (φ (n + N))) (η := fun n => η (φ (n + N))) (R := fun n => R (φ (n + N)))
      hK (fun n => hpair _) (fun n => hnl _) hgood' (hη.comp hmono.tendsto_atTop)
      (hR.comp hmono.tendsto_atTop)
  refine ⟨fun n => χ n + N, fun a b h => Nat.add_lt_add_right (hχ h) N, ?_⟩
  have hc : ∀ n, 0 < c n := fun n => (hcb n).1
  obtain ⟨Kb, hKb, hKbD, hball⟩ := s04_tp_ball hg hgL hgL0 hconv r
  obtain ⟨V, hVo, hKV, hVc, hVD, t, Nm, hCt, hCN, heq, huniq⟩ :=
    s04_tg_solve (Ω := fun n => Ω (φ (χ n + N))) (Ωs := fun n => Ωs (φ (χ n + N)))
      (fun n => hpair _) (fun n => hnl _) hc hg hgL hgL0 hconv hker hgs hgsL hgsL0 hsconv hsker
      hα hD hDs hKb hKbD T'
  obtain ⟨V', hV'o, hKV', hV'V, hV'c⟩ := exists_open_between_and_isCompact_closure hKb hVo hKV
  have hV'sub : V' ⊆ V := subset_closure.trans hV'V
  -- `t n → 0` uniformly on `closure V'`, so eventually `t n < min δ 1` on `V'`
  have hu := Metric.tendstoUniformlyOn_iff.mp (s04_tc_unif hVo hCt hV'c hV'V) (min δ 1)
    (lt_min hδ one_pos)
  have hsmall : ∀ᶠ n in atTop, ∀ v ∈ V', t n v < min δ 1 := by
    filter_upwards [hu] with n hn v hv
    have h1 := hn v (subset_closure hv)
    rw [Real.dist_eq, zero_sub, abs_neg] at h1
    exact (le_abs_self _).trans_lt h1
  have hV'Ω : ∀ᶠ n in atTop, V' ⊆ (fun z => (c n : ℂ) * z + b n) '' Ω (φ (χ n + N)) := by
    filter_upwards [hker (closure V') hV'c (hV'V.trans (subset_closure.trans hVD))] with n hn
    exact subset_closure.trans hn
  -- `‖t n‖_{C^j}` on `Kb`: stage W with `k = 0`
  have hfst := s04_tc_const (U := V ×ˢ (univ : Set (Fin 0 → ℂ)))
    (contDiffOn_fst (s := V ×ˢ (univ : Set (Fin 0 → ℂ))) (𝕜 := ℝ))
  have hT := s04_tc_comp (hVo.prod isOpen_univ) hVo hCt hfst
    (Eventually.of_forall fun n p hp => hp.1) (fun p hp => hp.1)
  have hTs : (∀ᶠ n in atTop, ContDiffOn ℝ ∞
        (fun p : ℂ × (Fin 0 → ℂ) => scalarField (t n) p.1 p.2) (V ×ˢ univ)) ∧
      ContDiffOn ℝ ∞ (fun p : ℂ × (Fin 0 → ℂ) => scalarField (fun _ : ℂ => (0 : ℝ)) p.1 p.2)
        (V ×ˢ univ) ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ i (fun p : ℂ × (Fin 0 → ℂ) => scalarField (t n) p.1 p.2))
        (iteratedFDeriv ℝ i
          (fun p : ℂ × (Fin 0 → ℂ) => scalarField (fun _ : ℂ => (0 : ℝ)) p.1 p.2))
        atTop (V ×ˢ univ) := hT
  have hlam_ := s04_td_lambda hg hgL hgL0 hconv hker hVo hVc hVD
  have hG := s04_td_grad hg hgL hgL0 hconv hker hVo hVc hVD
  have hW := s04_tw_iter (T := fun n => scalarField (t n))
    (TL := scalarField fun _ : ℂ => (0 : ℝ)) hVo hTs hG
  have hpos : ∀ x ∈ V, 0 < poincareDensity (gL '' unitDisc) x := fun x hx =>
    s02_poincareDensity_pos ⟨gL, hgL⟩ (hVD (subset_closure hx))
  have hδ' : ∀ i ≤ j, ∀ x ∈ Kb, rhoTensorNorm (gL '' unitDisc)
      (rhoIterCovDeriv (gL '' unitDisc) i (scalarField fun _ : ℂ => (0 : ℝ))) x < δ := by
    intro i _ x _
    have hz : scalarField (fun _ : ℂ => (0 : ℝ)) = (0 : TensorField 0) := by
      funext y v
      rfl
    have h0 : rhoIterCovDeriv (gL '' unitDisc) i (scalarField fun _ : ℂ => (0 : ℝ)) = 0 := by
      rw [hz]
      exact funext fun x => funext fun v => s04_tw_zero _ i x v
    rw [h0]
    simp only [rhoTensorNorm, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero, Real.sqrt_zero, zero_div]
    exact hδ
  have ecj := s04_tw_cj hVo hKb hKV hW hlam_ hpos j hδ'
  have hhs := hχ.tendsto_atTop.eventually
    (s04_tg_hs (Ω := fun n => Ω (φ (n + N))) (Ωs := fun n => Ωs (φ (n + N)))
      (w := fun n => w (φ (n + N))) (η := fun n => η (φ (n + N))) (R := fun n => R (φ (n + N)))
      (fun n => hpair _) (fun n => hnl _) hgood' (hη.comp hmono.tendsto_atTop)
      (hR.comp hmono.tendsto_atTop) r)
  have hhoro := s04_tg_horoT (Ω := fun n => Ω (φ (χ n + N))) (Ωs := fun n => Ωs (φ (χ n + N)))
    hc hg hgL hgL0 hconv hker hgs hgsL hgsL0 hsconv hsker hα hD hDs hKb hKbD hT'
  filter_upwards [hCt.1, hCN, heq, huniq, hsmall, hV'Ω, ecj, hball, hhs, hhoro] with n ht hNn
    heqn huniqn hsm hVn hcjn hb hsn hhn
  have hwm : w (φ (χ n + N)) ∈ Ω (φ (χ n + N)) := (hgood' (χ n)).1
  exact s04_tg_pull (hpair _) (hnl _) hwm (hc n) (hcb n).2 hT' hδ j hsn hV'o hVn
    (hb.trans hKV') (ht.mono hV'sub) (hNn.mono hV'sub) hsm (fun v hv => heqn v (hV'sub hv))
    (fun v hv => huniqn v (hV'sub hv)) ((s04_tb_cj_mono _ _ le_rfl hb).trans hcjn)
    (fun v hv => hhn v (hb hv))

/-! ## §4.1 Local smoothness -/

/-- **Lemma 4.1** (`lem:Cj`, sec04-tube.tex:29).  For every `j ≥ 1` there are absolute constants
`δ_j > 0`, `C_j` such that if `sup_{B_ρ(w,2)} s ≤ δ ≤ δ_j`, then `X` is an embedding on `B_ρ(w,1)`
and `‖I - ρ‖_{C^j(B_ρ(w,1))} + ‖B‖_{C^{j-1}(B_ρ(w,1))} ≤ C_j δ` (4.1).  (Standing assumption of §4:
`Γ` a `K`-quasicircle that is not a circle; the constants do not depend on `K`.) -/
theorem lem_Cj : ∀ j : ℕ, 1 ≤ j → ∃ δj : ℝ, 0 < δj ∧ ∃ Cj : ℝ, ∀ K : ℝ, 1 ≤ K →
    ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
    ∀ w ∈ Ω, ∀ δ : ℝ, δ ≤ δj → (∀ w' ∈ rhoBall Ω w 2, schwarzNorm Ω w' ≤ δ) →
      IsSmoothEmbeddingOn (epstein Ω) (rhoBall Ω w 1) ∧
        rhoCjNorm Ω j (fffT Ω - rhoMetricT Ω) (rhoBall Ω w 1) +
            rhoCjNorm Ω (j - 1) (shapeT Ω) (rhoBall Ω w 1) ≤ ENNReal.ofReal (Cj * δ) := by
  sorry

/-! ## §4.2 The tube lemma -/

/-- **Lemma 4.2** (Finite tube lemma, `lem:tube`, sec04-tube.tex:71).  Fix `K ≥ 1`, `L > 0`,
`T > 0`, an integer `m ≥ 6` and `ε ∈ (0, 1/4)` (and `R₀ ≥ 0`, see the module docstring).  There
are `η > 0` and `R < ∞`, depending only on these data, such that for every `K`-quasicircle that is
not a circle and every `(η, R)`-good `w ∈ Ω`, with `Z = \overline{B_ρ(w, L+1)} × [-2, T+2]` and
`Z' = \overline{B_ρ(w, L)} × [-1, T+1]`:
(i) `X` is an embedding on `B_ρ(w, L+1)` and `‖I-ρ‖_{C^{m-2}} + ‖B‖_{C^{m-3}} ≤ ε` there;
(ii) `E` is a smooth embedding of `Z` into `ℍ³`;
(iii) there are a smooth `t` and a smooth embedding `N : \overline{B_ρ(w,L)} → Ω*` with
`0 < t < ε`, `‖t‖_{C^{m-2}} ≤ ε`, `X*(N v) = E(v, t v)` (4.2), and `(X*)⁻¹(E(Z')) = N(\overline{B_ρ(w,L)})`;
(iv) `E(v,τ) ∉ U*` for `0 ≤ τ < t(v)` and `E(v,τ) ∈ int U*` for `t(v) < τ ≤ T`;
(v) `s < 1/2` on `B_ρ(v, R₀+2)`, `s* < ε` on `B_{ρ*}(N v, R₀+2)`, and `Σ*` satisfies the
estimates of (i) on the `ρ*`-neighbourhood of radius `1` of `N(\overline{B_ρ(w,L)})`.
Finally, for `0 < τ < t(v)`, `E(v, τ) ∈ 𝒩` and every label takes the value `v` at it. -/
theorem lem_tube (K L T : ℝ) (m : ℕ) (ε R₀ : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hT : 0 < T)
    (hm : 6 ≤ m) (hε : 0 < ε) (hε' : ε < 1 / 4) (hR₀ : 0 ≤ R₀) :
    ∃ η : ℝ, 0 < η ∧ ∃ R : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ w : ℂ, IsGoodParam Ω Ωs η R w →
        -- (i)
        (IsSmoothEmbeddingOn (epstein Ω) (rhoBall Ω w (L + 1)) ∧
          rhoCjNorm Ω (m - 2) (fffT Ω - rhoMetricT Ω) (rhoBall Ω w (L + 1)) +
              rhoCjNorm Ω (m - 3) (shapeT Ω) (rhoBall Ω w (L + 1)) ≤ ENNReal.ofReal ε) ∧
        -- (ii)
        (IsSmoothEmbeddingOn (normalMap Ω) (rhoClosedBall Ω w (L + 1) ×ˢ Icc (-2) (T + 2)) ∧
          MapsTo (normalMap Ω) (rhoClosedBall Ω w (L + 1) ×ˢ Icc (-2) (T + 2)) UHS) ∧
        ∃ t : ℂ → ℝ, ∃ N : ℂ → ℂ,
          -- (iii)
          SmoothNear t (rhoClosedBall Ω w L) ∧ IsSmoothEmbeddingOn N (rhoClosedBall Ω w L) ∧
          MapsTo N (rhoClosedBall Ω w L) Ωs ∧
          rhoCjNorm Ω (m - 2) (scalarField t) (rhoClosedBall Ω w L) ≤ ENNReal.ofReal ε ∧
          (∀ v ∈ rhoClosedBall Ω w L,
            0 < t v ∧ t v < ε ∧ epstein Ωs (N v) = normalGeod Ω v (t v)) ∧
          {z | z ∈ Ωs ∧ epstein Ωs z ∈ normalMap Ω '' (rhoClosedBall Ω w L ×ˢ Icc (-1) (T + 1))} =
            N '' rhoClosedBall Ω w L ∧
          -- (iv)
          (∀ v ∈ rhoClosedBall Ω w L,
            (∀ τ ∈ Ico 0 (t v), normalGeod Ω v τ ∉ horoUnion Ωs) ∧
            ∀ τ ∈ Ioc (t v) T, normalGeod Ω v τ ∈ interior (horoUnion Ωs)) ∧
          -- (v)
          (∀ v ∈ rhoClosedBall Ω w L,
            (∀ w' ∈ rhoBall Ω v (R₀ + 2), schwarzNorm Ω w' < 1 / 2) ∧
            ∀ z ∈ rhoBall Ωs (N v) (R₀ + 2), schwarzNorm Ωs z < ε) ∧
          rhoCjNorm Ωs (m - 2) (fffT Ωs - rhoMetricT Ωs)
                (rhoNbhd Ωs (N '' rhoClosedBall Ω w L) 1) +
              rhoCjNorm Ωs (m - 3) (shapeT Ωs) (rhoNbhd Ωs (N '' rhoClosedBall Ω w L) 1) ≤
            ENNReal.ofReal ε ∧
          -- the final assertion
          ∀ v ∈ rhoClosedBall Ω w L, ∀ τ ∈ Ioo 0 (t v), normalGeod Ω v τ ∈ gap Ω Ωs ∧
            ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab → lab (normalGeod Ω v τ) = v := by
  -- The frozen hypothesis `hR₀` is not needed (the statement stays true without it).
  have _h := hR₀
  have _hm := hm
  obtain ⟨A, B, hqi⟩ := prop_qi K
  obtain ⟨R₁, hul⟩ := prop_unique_label K
  refine s04_tb_contra (K := K) ?_
  intro Ω Ωs w η R hpair hnl hgood hη hR
  have hgoodE : ∀ᶠ n in atTop, IsGoodParam (Ω n) (Ωs n) (η n) (R n) (w n) :=
    Eventually.of_forall hgood
  set δ : ℝ := min ε (T / 2) with hδdef
  have hδ : 0 < δ := lt_min hε (half_pos hT)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδT : δ < T := (min_le_right _ _).trans_lt (half_lt_self hT)
  set M : ℝ := max (max (5 / 2 * (3 * (L + 1))) (5 / 2 * (L + (R₀ + 2))))
    (max (5 / 2 * (L + (R₁ + 2))) (5 / 2 * L + 1 + 5 / 2 * (R₀ + 2))) with hMdef
  have hM1 : 5 / 2 * (3 * (L + 1)) ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hM2 : 5 / 2 * (L + (R₀ + 2)) ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hM3 : 5 / 2 * (L + (R₁ + 2)) ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hM4 : 5 / 2 * L + 1 + 5 / 2 * (R₀ + 2) ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have eR : ∀ᶠ n in atTop, M ≤ R n := hR.eventually_ge_atTop M
  have eη : ∀ᶠ n in atTop, η n < min (1 / 2) ε :=
    hη.eventually (gt_mem_nhds (lt_min (by norm_num) hε))
  have e1 := s04_tb_X_norm hK hpair hnl hgoodE hη hR (m - 2) (r := L + 1) hε
  have e2 := s04_tb_graph hK hpair hnl hgoodE hη hR (r := L) hT hδ (m - 2)
  -- the star side, at the base points `z n = N(w n)`
  set z : ℕ → ℂ := fun n => slabMap (Ω n) (Ωs n) (w n) with hzdef
  set rs : ℝ := |A| * (1 + 5 / 2 * L) + B + 2 with hrsdef
  have hpair' : ∀ n, IsKQuasiPair (Ωs n) (Ω n) K := fun n => s03_qce_swap (hpair n)
  have hnl' : ∀ n, ¬ IsLinePair (Ωs n) (Ω n) := fun n => s04_tb_swap_nl (hnl n)
  have hXU : ∀ n, ∀ u ∈ Ω n, epstein (Ω n) u ∈ UHS := fun n u hu => by
    have h := lem_normal_b (s02_jordanPair_riemannMap (s03_b0_jordanPair (hpair n))) hu
    rw [← h.2.2]
    exact h.1 0
  have hXUs : ∀ n, ∀ u ∈ Ωs n, epstein (Ωs n) u ∈ UHS := fun n u hu => by
    have h := lem_normal_b (s02_jordanPair_riemannMap (s03_b0_jordanPair (hpair' n))) hu
    rw [← h.2.2]
    exact h.1 0
  -- `d(X(v), X*(N v)) = t(v)`
  have hXN : ∀ n, ∀ v ∈ Ω n, ∀ t : ℝ, 0 ≤ t →
      hdist (epstein (Ω n) v) (normalGeod (Ω n) v t) = t := fun n v hv t ht => by
    have h := lem_normal_b (s02_jordanPair_riemannMap (s03_b0_jordanPair (hpair n))) hv
    rw [← h.2.2, h.2.1, zero_sub, abs_neg, abs_of_nonneg ht]
  have hgs : ∀ᶠ n in atTop, IsGoodParam (Ωs n) (Ω n) (η n) (R n - 1) (z n) := by
    filter_upwards [e2, hgoodE] with n h2 hg
    have hΩc := s02_jordanPair_riemannMap (s03_b0_jordanPair (hpair n))
    have hwB : w n ∈ rhoClosedBall (Ω n) (w n) L :=
      ⟨hg.1, by rw [s04_tb_dist_self hΩc hg.1]; exact hL.le⟩
    obtain ⟨ht0, htδ, hX⟩ := h2.2.2.2.2.1 (w n) hwB
    refine s04_tb_good_swap (hpair n) hg (h2.2.2.1 hwB) ?_
    show hdist (epstein (Ω n) (w n)) (epstein (Ωs n) (slabMap (Ω n) (Ωs n) (w n))) ≤ 1
    rw [hX, hXN n (w n) hg.1 _ ht0.le]
    linarith
  have hR' : Tendsto (fun n => R n - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ (-1) hR
  have e3 := s04_tb_X_norm hK hpair' hnl' hgs hη hR' (m - 2) (r := rs) hε
  filter_upwards [e1, e2, e3, eR, eη, hgoodE] with n h1 h2 h3 hRn hηn hg
  -- data at `n`
  have hJ := s03_b0_jordanPair (hpair n)
  have hΩc := s02_jordanPair_riemannMap hJ
  have hΩsc := s02_jordanPair_riemannMap (s03_b0_jordanPair (hpair' n))
  obtain ⟨hgs1, hgs2⟩ := s04_tb_good_s (hpair n) hg
  have hη2 : η n < 1 / 2 := hηn.trans_le (min_le_left _ _)
  have hηε : η n < ε := hηn.trans_le (min_le_right _ _)
  have hqiΩ := (hqi (Ω n) (Ωs n) (hpair n) (hnl n)).1
  have hqiS := (hqi (Ω n) (Ωs n) (hpair n) (hnl n)).2
  have sball : ∀ w' ∈ Ω n, ∀ ρ₀ : ℝ, poincareDist (Ω n) (w n) w' ≤ ρ₀ → 5 / 2 * ρ₀ ≤ R n →
      schwarzNorm (Ω n) w' < η n := fun w' hw' ρ₀ hd hρ =>
    hgs1 w' hw' ((hqiΩ (w n) hg.1 w' hw').2.trans
      ((mul_le_mul_of_nonneg_left hd (by norm_num)).trans hρ))
  have hs3 : ∀ w' ∈ Ω n, poincareDist (Ω n) (w n) w' ≤ 3 * (L + 1) →
      schwarzNorm (Ω n) w' < 1 / 2 := fun w' hw' hd =>
    (sball w' hw' _ hd (hM1.trans hRn)).trans hη2
  have hEemb := s04_tb_E_embed (hpair n) (hnl n) hg.1 hs3 (-2) (T + 2)
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := h2
  have hL1 : ∀ u ∈ rhoClosedBall (Ω n) (w n) L, u ∈ rhoClosedBall (Ω n) (w n) (L + 1) :=
    fun u hu => ⟨hu.1, hu.2.trans (by linarith)⟩
  have hdw : ∀ v ∈ rhoClosedBall (Ω n) (w n) L, ∀ w' ∈ Ω n, ∀ ρ : ℝ,
      poincareDist (Ω n) v w' ≤ ρ → poincareDist (Ω n) (w n) w' ≤ L + ρ :=
    fun v hv w' hw' ρ hρ =>
      (s02_poincareDist_triangle hΩc hg.1 hv.1 hw').trans (add_le_add hv.2 hρ)
  -- uniqueness of the hitting time along a ray
  have huniq : ∀ v ∈ rhoClosedBall (Ω n) (w n) L, ∀ τ ∈ Icc 0 T, ∀ y ∈ Ωs n,
      epstein (Ωs n) y = normalGeod (Ω n) v τ → τ = slabTop (Ω n) (Ωs n) v := by
    intro v hv τ hτ y hy hyE
    have hymem : y ∈ {z | z ∈ Ωs n ∧ epstein (Ωs n) z ∈
        normalMap (Ω n) '' (rhoClosedBall (Ω n) (w n) L ×ˢ Icc (-1) (T + 1))} :=
      ⟨hy, ⟨(v, τ), ⟨hv, ⟨by linarith [hτ.1], by linarith [hτ.2]⟩⟩, hyE.symm⟩⟩
    rw [g6] at hymem
    obtain ⟨v', hv', hv'y⟩ := hymem
    have hE := hEemb.2.1 (x₁ := (v, τ)) (x₂ := (v', slabTop (Ω n) (Ωs n) v'))
      ⟨hL1 v hv, ⟨by linarith [hτ.1], by linarith [hτ.2]⟩⟩
      ⟨hL1 v' hv', ⟨by linarith [(g5 v' hv').1], by linarith [(g5 v' hv').2.1]⟩⟩
      (by
        show normalGeod (Ω n) v τ = normalGeod (Ω n) v' (slabTop (Ω n) (Ωs n) v')
        rw [← hyE, ← hv'y, (g5 v' hv').2.2])
    have e1' := (Prod.mk.inj hE).1
    have e2' := (Prod.mk.inj hE).2
    rw [e2', ← e1']
  have hiv : ∀ v ∈ rhoClosedBall (Ω n) (w n) L,
      (∀ τ ∈ Ico 0 (slabTop (Ω n) (Ωs n) v), normalGeod (Ω n) v τ ∉ horoUnion (Ωs n)) ∧
        ∀ τ ∈ Ioc (slabTop (Ω n) (Ωs n) v) T,
          normalGeod (Ω n) v τ ∈ interior (horoUnion (Ωs n)) := fun v hv =>
    s04_tb_sides (hpair n) (hnl n) hv.1 (g5 v hv).1 ((g5 v hv).2.1.trans hδT)
      (huniq v hv) (g7 v hv)
  refine ⟨⟨s04_tb_X_embed (hpair n) (hnl n) hg.1 hs3,
      (add_le_add le_rfl (s04_tb_cj_mono _ _ (Nat.sub_le_sub_left (by norm_num : 2 ≤ 3) m)
        subset_rfl)).trans h1⟩,
    ⟨hEemb, fun p hp => (lem_normal_b hΩc hp.1.1).1 p.2⟩,
    slabTop (Ω n) (Ωs n), slabMap (Ω n) (Ωs n), g1, g2, g3,
    g4.trans (ENNReal.ofReal_le_ofReal hδε),
    fun v hv => ⟨(g5 v hv).1, (g5 v hv).2.1.trans_le hδε, (g5 v hv).2.2⟩, g6, hiv, ?_, ?_, ?_⟩
  · -- (v)
    intro v hv
    refine ⟨fun w' hw' => ?_, fun y hy => ?_⟩
    · exact (sball w' hw'.1 _ (hdw v hv w' hw'.1 _ hw'.2.le) (hM2.trans hRn)).trans hη2
    · refine (hgs2 y hy.1 ?_).trans hηε
      have hNv := g3 hv
      have ht := g5 v hv
      have h1' : hdist (epstein (Ω n) (w n)) (epstein (Ω n) v) ≤ 5 / 2 * L :=
        (hqiΩ (w n) hg.1 v hv.1).2.trans (mul_le_mul_of_nonneg_left hv.2 (by norm_num))
      have h2' : hdist (epstein (Ω n) v) (epstein (Ωs n) (slabMap (Ω n) (Ωs n) v)) ≤ 1 := by
        rw [ht.2.2, hXN n v hv.1 _ ht.1.le]
        linarith [ht.2.1]
      have h3' : hdist (epstein (Ωs n) (slabMap (Ω n) (Ωs n) v)) (epstein (Ωs n) y) ≤
          5 / 2 * (R₀ + 2) :=
        (hqiS _ hNv y hy.1).2.trans (mul_le_mul_of_nonneg_left hy.2.le (by norm_num))
      calc hdist (epstein (Ω n) (w n)) (epstein (Ωs n) y)
          ≤ hdist (epstein (Ω n) (w n)) (epstein (Ω n) v) +
              hdist (epstein (Ω n) v) (epstein (Ωs n) y) :=
            s02_hdist_triangle (hXU n _ hg.1) (hXU n _ hv.1) (hXUs n _ hy.1)
        _ ≤ hdist (epstein (Ω n) (w n)) (epstein (Ω n) v) +
              (hdist (epstein (Ω n) v) (epstein (Ωs n) (slabMap (Ω n) (Ωs n) v)) +
                hdist (epstein (Ωs n) (slabMap (Ω n) (Ωs n) v)) (epstein (Ωs n) y)) :=
            add_le_add le_rfl (s02_hdist_triangle (hXU n _ hv.1) (hXUs n _ hNv)
              (hXUs n _ hy.1))
        _ ≤ R n := by linarith
  · -- the star estimates of (v), from the swapped stage at `z n`
    have hsub : rhoNbhd (Ωs n) (slabMap (Ω n) (Ωs n) '' rhoClosedBall (Ω n) (w n) L) 1 ⊆
        rhoBall (Ωs n) (z n) rs := by
      rintro y ⟨hyΩ, _, ⟨v, hv, rfl⟩, hvy⟩
      refine ⟨hyΩ, ?_⟩
      have hwB : w n ∈ rhoClosedBall (Ω n) (w n) L :=
        ⟨hg.1, by rw [s04_tb_dist_self hΩc hg.1]; exact hL.le⟩
      have hNv := g3 hv
      have hNw := g3 hwB
      have htv := g5 v hv
      have htw := g5 (w n) hwB
      have hh : hdist (epstein (Ωs n) (z n)) (epstein (Ωs n) (slabMap (Ω n) (Ωs n) v)) ≤
          1 + 5 / 2 * L := by
        have ha : hdist (epstein (Ωs n) (z n)) (epstein (Ω n) (w n)) ≤ 1 / 2 := by
          rw [s02_hdist_comm]
          show hdist (epstein (Ω n) (w n)) (epstein (Ωs n) (slabMap (Ω n) (Ωs n) (w n))) ≤ 1 / 2
          rw [htw.2.2, hXN n (w n) hg.1 _ htw.1.le]
          linarith [htw.2.1]
        have hb : hdist (epstein (Ω n) (w n)) (epstein (Ω n) v) ≤ 5 / 2 * L :=
          (hqiΩ (w n) hg.1 v hv.1).2.trans (mul_le_mul_of_nonneg_left hv.2 (by norm_num))
        have hc : hdist (epstein (Ω n) v) (epstein (Ωs n) (slabMap (Ω n) (Ωs n) v)) ≤
            1 / 2 := by
          rw [htv.2.2, hXN n v hv.1 _ htv.1.le]
          linarith [htv.2.1]
        calc hdist (epstein (Ωs n) (z n)) (epstein (Ωs n) (slabMap (Ω n) (Ωs n) v))
            ≤ hdist (epstein (Ωs n) (z n)) (epstein (Ω n) (w n)) +
                hdist (epstein (Ω n) (w n)) (epstein (Ωs n) (slabMap (Ω n) (Ωs n) v)) :=
              s02_hdist_triangle (hXUs n _ hNw) (hXU n _ hg.1) (hXUs n _ hNv)
          _ ≤ hdist (epstein (Ωs n) (z n)) (epstein (Ω n) (w n)) +
                (hdist (epstein (Ω n) (w n)) (epstein (Ω n) v) +
                  hdist (epstein (Ω n) v) (epstein (Ωs n) (slabMap (Ω n) (Ωs n) v))) :=
              add_le_add le_rfl (s02_hdist_triangle (hXU n _ hg.1) (hXU n _ hv.1)
                (hXUs n _ hNv))
          _ ≤ 1 + 5 / 2 * L := by linarith
      have hd1 : poincareDist (Ωs n) (z n) (slabMap (Ω n) (Ωs n) v) ≤
          |A| * (1 + 5 / 2 * L) + B := by
        refine (hqiS _ hNw _ hNv).1.trans (add_le_add ?_ le_rfl)
        have h0 : 0 ≤ hdist (epstein (Ωs n) (z n)) (epstein (Ωs n) (slabMap (Ω n) (Ωs n) v)) := by
          have hp1 : (0 : ℝ) < (epstein (Ωs n) (z n)).2 := hXUs n _ hNw
          have hp2 : (0 : ℝ) < (epstein (Ωs n) (slabMap (Ω n) (Ωs n) v)).2 := hXUs n _ hNv
          refine Real.arcosh_nonneg ?_
          unfold coshDist
          have : 0 ≤ (‖(epstein (Ωs n) (z n)).1 - (epstein (Ωs n) (slabMap (Ω n) (Ωs n) v)).1‖ ^ 2 +
              ((epstein (Ωs n) (z n)).2 - (epstein (Ωs n) (slabMap (Ω n) (Ωs n) v)).2) ^ 2) /
              (2 * (epstein (Ωs n) (z n)).2 * (epstein (Ωs n) (slabMap (Ω n) (Ωs n) v)).2) := by
            positivity
          linarith
        calc A * hdist (epstein (Ωs n) (z n)) (epstein (Ωs n) (slabMap (Ω n) (Ωs n) v))
            ≤ |A| * hdist (epstein (Ωs n) (z n)) (epstein (Ωs n) (slabMap (Ω n) (Ωs n) v)) :=
              mul_le_mul_of_nonneg_right (le_abs_self A) h0
          _ ≤ |A| * (1 + 5 / 2 * L) := mul_le_mul_of_nonneg_left hh (abs_nonneg A)
      have htri := s02_poincareDist_triangle hΩsc hNw hNv hyΩ
      show poincareDist (Ωs n) (z n) y < rs
      linarith
    exact (add_le_add (s04_tb_cj_mono _ _ le_rfl hsub)
      (s04_tb_cj_mono _ _ (Nat.sub_le_sub_left (by norm_num : 2 ≤ 3) m) hsub)).trans h3
  · -- the final assertion
    intro v hv τ hτ
    have hsul : ∀ w' ∈ Ω n, poincareDist (Ω n) v w' ≤ R₁ + 2 → schwarzNorm (Ω n) w' < 1 / 2 :=
      fun w' hw' hd => (sball w' hw' _ (hdw v hv w' hw' _ hd) (hM3.trans hRn)).trans hη2
    obtain ⟨-, hlab, -⟩ := (hul (Ω n) (Ωs n) (hpair n) (hnl n)).1 v hv.1 hsul
    have hτ1 : τ ∈ Ioc (0 : ℝ) 1 :=
      ⟨hτ.1, by linarith [hτ.2, (g5 v hv).2.1, hδε]⟩
    refine ⟨⟨(lem_normal_b hΩc hv.1).1 τ, ?_⟩, fun lab hl => (hlab lab hl τ hτ1).1⟩
    rintro (hU | hU)
    · obtain ⟨lab, hl, -⟩ := lem_borel_label hJ (hnl n)
      have h0 := (hlab lab hl τ hτ1).2
      have hUH : horoUnion (Ω n) ⊆ UHS := by
        intro p hp
        simp only [horoUnion, mem_iUnion] at hp
        obtain ⟨_, _, hp⟩ := hp
        exact hp.1
      have := s03_wd_self hU hUH
      linarith [hτ.1]
    · exact (hiv v hv).1 τ ⟨hτ.1.le, hτ.2⟩ hU

/-! ## §4.2½ Slab foundation (interface F0, w3)

`s04_sl_*`: monotonicity of goodness, the uniform form of `lem_tube` (all smaller `η` and larger
`R`), openness of `G₀` for every `(η, R)`, and the identification of the `t`, `N` of `lem_tube`
with `slabTop`, `slabMap`.  The items of §4.3–4.4 are proved in uniform form
(`s04_sl_*_unif`, conclusions at every `η ≤ η₀`, `R ≥ R₁`); the frozen statements follow by
taking `η = η₀`, `R = R₁`.  The uniform forms are what downstream proofs combine. -/

/-- F0a: goodness is monotone, `G₀(η', R') ⊆ G₀(η, R)` for `η' ≤ η` and `R ≤ R'` (`ς(x, ·)` is
monotone, its sets being bounded above and nonnegative, `s04_tb_vs_bdd`). -/
theorem s04_sl_good_mono {K : ℝ} {Ω Ωs : Set ℂ} (hpair : IsKQuasiPair Ω Ωs K)
    {η η' R R' : ℝ} {w : ℂ} (hw : IsGoodParam Ω Ωs η' R' w) (hη : η' ≤ η) (hR : R ≤ R') :
    IsGoodParam Ω Ωs η R w := by
  obtain ⟨hwΩ, hlt⟩ := hw
  refine ⟨hwΩ, lt_of_le_of_lt ?_ (lt_of_lt_of_le hlt hη)⟩
  have hΩ := s02_jordanPair_riemannMap (s03_b0_jordanPair hpair)
  have hΩs := s02_jordanPair_riemannMap (s03_b0_jordanPair (s03_qce_swap hpair))
  obtain ⟨hb, hnn⟩ := s04_tb_vs_bdd hΩ hΩs (epstein Ω w) R'
  unfold varsigma
  rcases Set.eq_empty_or_nonempty ({r | ∃ w' ∈ Ω, epstein Ω w' ∈ hball (epstein Ω w) R ∧
      r = schwarzNorm Ω w'} ∪ {r | ∃ z ∈ Ωs, epstein Ωs z ∈ hball (epstein Ω w) R ∧
      r = schwarzNorm Ωs z}) with he | hne
  · rw [he, Real.sSup_empty]
    exact Real.sSup_nonneg hnn
  · refine csSup_le_csSup hb hne ?_
    rintro r (⟨w', hw', hX, rfl⟩ | ⟨z, hz, hX, rfl⟩)
    · exact Or.inl ⟨w', hw', ⟨hX.1, hX.2.trans hR⟩, rfl⟩
    · exact Or.inr ⟨z, hz, ⟨hX.1, hX.2.trans hR⟩, rfl⟩

/-- F0b: uniform form of Lemma 4.2 (`lem_tube`): its conclusions hold at every `(η, R)` with
`η ≤ η₀`, `R ≥ R₁` (from `lem_tube` and F0a). -/
theorem s04_sl_tube_unif (K L T : ℝ) (m : ℕ) (ε R₀ : ℝ) (hK : 1 ≤ K) (hL : 0 < L) (hT : 0 < T)
    (hm : 6 ≤ m) (hε : 0 < ε) (hε' : ε < 1 / 4) (hR₀ : 0 ≤ R₀) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ R₁ : ℝ, ∀ η R : ℝ, 0 < η → η ≤ η₀ → R₁ ≤ R →
      ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ w : ℂ, IsGoodParam Ω Ωs η R w →
        -- (i)
        (IsSmoothEmbeddingOn (epstein Ω) (rhoBall Ω w (L + 1)) ∧
          rhoCjNorm Ω (m - 2) (fffT Ω - rhoMetricT Ω) (rhoBall Ω w (L + 1)) +
              rhoCjNorm Ω (m - 3) (shapeT Ω) (rhoBall Ω w (L + 1)) ≤ ENNReal.ofReal ε) ∧
        -- (ii)
        (IsSmoothEmbeddingOn (normalMap Ω) (rhoClosedBall Ω w (L + 1) ×ˢ Icc (-2) (T + 2)) ∧
          MapsTo (normalMap Ω) (rhoClosedBall Ω w (L + 1) ×ˢ Icc (-2) (T + 2)) UHS) ∧
        ∃ t : ℂ → ℝ, ∃ N : ℂ → ℂ,
          -- (iii)
          SmoothNear t (rhoClosedBall Ω w L) ∧ IsSmoothEmbeddingOn N (rhoClosedBall Ω w L) ∧
          MapsTo N (rhoClosedBall Ω w L) Ωs ∧
          rhoCjNorm Ω (m - 2) (scalarField t) (rhoClosedBall Ω w L) ≤ ENNReal.ofReal ε ∧
          (∀ v ∈ rhoClosedBall Ω w L,
            0 < t v ∧ t v < ε ∧ epstein Ωs (N v) = normalGeod Ω v (t v)) ∧
          {z | z ∈ Ωs ∧ epstein Ωs z ∈ normalMap Ω '' (rhoClosedBall Ω w L ×ˢ Icc (-1) (T + 1))} =
            N '' rhoClosedBall Ω w L ∧
          -- (iv)
          (∀ v ∈ rhoClosedBall Ω w L,
            (∀ τ ∈ Ico 0 (t v), normalGeod Ω v τ ∉ horoUnion Ωs) ∧
            ∀ τ ∈ Ioc (t v) T, normalGeod Ω v τ ∈ interior (horoUnion Ωs)) ∧
          -- (v)
          (∀ v ∈ rhoClosedBall Ω w L,
            (∀ w' ∈ rhoBall Ω v (R₀ + 2), schwarzNorm Ω w' < 1 / 2) ∧
            ∀ z ∈ rhoBall Ωs (N v) (R₀ + 2), schwarzNorm Ωs z < ε) ∧
          rhoCjNorm Ωs (m - 2) (fffT Ωs - rhoMetricT Ωs)
                (rhoNbhd Ωs (N '' rhoClosedBall Ω w L) 1) +
              rhoCjNorm Ωs (m - 3) (shapeT Ωs) (rhoNbhd Ωs (N '' rhoClosedBall Ω w L) 1) ≤
            ENNReal.ofReal ε ∧
          -- the final assertion
          ∀ v ∈ rhoClosedBall Ω w L, ∀ τ ∈ Ioo 0 (t v), normalGeod Ω v τ ∈ gap Ω Ωs ∧
            ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab → lab (normalGeod Ω v τ) = v := by
  obtain ⟨η₀, hη₀, R₁, h⟩ := lem_tube K L T m ε R₀ hK hL hT hm hε hε' hR₀
  exact ⟨η₀, hη₀, R₁, fun η R _ hηle hR Ω Ωs hp hnl w hw =>
    h Ω Ωs hp hnl w (s04_sl_good_mono hp hw hηle hR)⟩

/-- F0c: `G₀ = goodSet Ω Ωs η R` is open for every `(η, R)`.  The preimages of the closed balls
`hball x R` under `X` and `X*` are compact (`s03_qi_lower`, `s04_tb_ball_compact`), so
`w ↦ ς(X(w), R)` is upper semicontinuous on `Ω`. -/
theorem s04_sl_good_open {K : ℝ} {Ω Ωs : Set ℂ} (hpair : IsKQuasiPair Ω Ωs K) (η R : ℝ) :
    IsOpen (goodSet Ω Ωs η R) := by
  have hJ := s03_b0_jordanPair hpair
  have hpairs := s03_qce_swap hpair
  have hJs := s03_b0_jordanPair hpairs
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  obtain ⟨fs, hfs⟩ := s02_jordanPair_riemannMap hJs
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hXC : ContinuousOn (epstein Ω) Ω := (lem_fff_smooth ⟨f, hf⟩).continuousOn
  have hXCs : ContinuousOn (epstein Ωs) Ωs := (lem_fff_smooth ⟨fs, hfs⟩).continuousOn
  have hsC : ContinuousOn (schwarzNorm Ω) Ω :=
    ((s02_contDiffOn_invFun hf).2.2.2.continuousOn.norm.div
      ((s02_contDiffOn_poincareDensity hf).continuousOn.pow 2)
      (fun x hx => pow_ne_zero 2 (s02_poincareDensity_pos ⟨f, hf⟩ hx).ne')).congr
      (fun x hx => eq_def_s hf hx)
  have hsCs : ContinuousOn (schwarzNorm Ωs) Ωs :=
    ((s02_contDiffOn_invFun hfs).2.2.2.continuousOn.norm.div
      ((s02_contDiffOn_poincareDensity hfs).continuousOn.pow 2)
      (fun x hx => pow_ne_zero 2 (s02_poincareDensity_pos ⟨fs, hfs⟩ hx).ne')).congr
      (fun x hx => eq_def_s hfs hx)
  have hXU : ∀ w ∈ Ω, epstein Ω w ∈ UHS := fun w hw => s04_tb_ep_uhs ⟨f, hf⟩ hw
  have hXUs : ∀ z ∈ Ωs, epstein Ωs z ∈ UHS := fun z hz => s04_tb_ep_uhs ⟨fs, hfs⟩ hz
  -- `Q ↦ d(P, Q)` is continuous on `ℍ³`
  have hdC : ∀ P ∈ UHS, ContinuousOn (hdist P) UHS := by
    intro P hP
    have hP2 : (0 : ℝ) < P.2 := hP
    have h1 : ContinuousOn (coshDist P) UHS := by
      show ContinuousOn (fun Q : ℂ × ℝ =>
        1 + (‖P.1 - Q.1‖ ^ 2 + (P.2 - Q.2) ^ 2) / (2 * P.2 * Q.2)) UHS
      refine continuousOn_const.add (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
      intro Q hQ
      have hQ2 : (0 : ℝ) < Q.2 := hQ
      positivity
    refine Real.continuousOn_arcosh.comp h1 (fun Q hQ => mem_Ici.mpr ?_)
    have hQ2 : (0 : ℝ) < Q.2 := hQ
    have : 0 ≤ (‖P.1 - Q.1‖ ^ 2 + (P.2 - Q.2) ^ 2) / (2 * P.2 * Q.2) := by positivity
    show 1 ≤ 1 + (‖P.1 - Q.1‖ ^ 2 + (P.2 - Q.2) ^ 2) / (2 * P.2 * Q.2)
    linarith
  have hself : ∀ P : ℂ × ℝ, hdist P P = 0 := by
    intro P
    have h1 : coshDist P P = 1 := by simp [coshDist]
    simp only [hdist, h1, Real.arcosh_zero]
  obtain ⟨A, B, hA, hqi⟩ := s03_qi_lower K
  rw [isOpen_iff_mem_nhds]
  intro w0 hw0
  obtain ⟨hw0Ω, hlt⟩ := hw0
  set x0 := epstein Ω w0 with hx0def
  have hx0 : x0 ∈ UHS := hXU w0 hw0Ω
  obtain ⟨hbdd, hnn⟩ := s04_tb_vs_bdd ⟨f, hf⟩ ⟨fs, hfs⟩ x0 R
  have hς0 : 0 ≤ varsigma Ω Ωs x0 R := Real.sSup_nonneg hnn
  obtain ⟨η', hη'1, hη'2⟩ := exists_between hlt
  -- `Ω`-side: the compact set `C₁` of parameters with `s ≥ η'` near `w₀` stays at distance `> R`
  set r0 := A * (R + 1) + B with hr0def
  have hB1 := s04_tb_ball_compact hJ hw0Ω r0
  have hC1 : IsCompact (rhoClosedBall Ω w0 r0 ∩ schwarzNorm Ω ⁻¹' Ici η') :=
    hB1.of_isClosed_subset ((hsC.mono (fun _ h => h.1 : rhoClosedBall Ω w0 r0 ⊆ Ω)).preimage_isClosed_of_isClosed
      hB1.isClosed isClosed_Ici) inter_subset_left
  have hC1far : ∀ w' ∈ rhoClosedBall Ω w0 r0 ∩ schwarzNorm Ω ⁻¹' Ici η',
      R < hdist x0 (epstein Ω w') := by
    rintro w' ⟨hw'B, hw's⟩
    by_contra hle
    rw [not_lt] at hle
    have h1 : schwarzNorm Ω w' ≤ varsigma Ω Ωs x0 R :=
      le_csSup hbdd (Or.inl ⟨w', hw'B.1, ⟨hXU w' hw'B.1, hle⟩, rfl⟩)
    have h2 : η' ≤ schwarzNorm Ω w' := hw's
    linarith
  obtain ⟨δ1, hδ1, hδ11, hδ1far⟩ : ∃ δ1 : ℝ, 0 < δ1 ∧ δ1 ≤ 1 ∧
      ∀ w' ∈ rhoClosedBall Ω w0 r0 ∩ schwarzNorm Ω ⁻¹' Ici η',
        R + δ1 ≤ hdist x0 (epstein Ω w') := by
    rcases (rhoClosedBall Ω w0 r0 ∩ schwarzNorm Ω ⁻¹' Ici η').eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, le_rfl, ?_⟩
      rw [he]
      intro w' hw'
      simp at hw'
    · have hgc : ContinuousOn (fun w' => hdist x0 (epstein Ω w'))
          (rhoClosedBall Ω w0 r0 ∩ schwarzNorm Ω ⁻¹' Ici η') :=
        (hdC x0 hx0).comp (hXC.mono fun _ h => h.1.1) (fun w' hw' => hXU w' hw'.1.1)
      obtain ⟨m, hm, hmin⟩ := hC1.exists_isMinOn hne hgc
      have hRm := hC1far m hm
      refine ⟨min 1 (hdist x0 (epstein Ω m) - R), lt_min one_pos (by linarith),
        min_le_left _ _, fun w' hw' => ?_⟩
      have h1 : hdist x0 (epstein Ω m) ≤ hdist x0 (epstein Ω w') := hmin hw'
      have h2 := min_le_right 1 (hdist x0 (epstein Ω m) - R)
      linarith
  -- `Ω*`-side, around a base point `z₀ ∈ Ω*`
  have hz0 : fs 0 ∈ Ωs := hfs.2.2 ▸ mem_image_of_mem fs (mem_ball_self one_pos)
  set r0s := A * (hdist (epstein Ωs (fs 0)) x0 + (R + 1)) + B with hr0sdef
  have hB2 := s04_tb_ball_compact hJs hz0 r0s
  have hC2 : IsCompact (rhoClosedBall Ωs (fs 0) r0s ∩ schwarzNorm Ωs ⁻¹' Ici η') :=
    hB2.of_isClosed_subset ((hsCs.mono (fun _ h => h.1 : rhoClosedBall Ωs (fs 0) r0s ⊆ Ωs)).preimage_isClosed_of_isClosed
      hB2.isClosed isClosed_Ici) inter_subset_left
  have hC2far : ∀ z ∈ rhoClosedBall Ωs (fs 0) r0s ∩ schwarzNorm Ωs ⁻¹' Ici η',
      R < hdist x0 (epstein Ωs z) := by
    rintro z ⟨hzB, hzs⟩
    by_contra hle
    rw [not_lt] at hle
    have h1 : schwarzNorm Ωs z ≤ varsigma Ω Ωs x0 R :=
      le_csSup hbdd (Or.inr ⟨z, hzB.1, ⟨hXUs z hzB.1, hle⟩, rfl⟩)
    have h2 : η' ≤ schwarzNorm Ωs z := hzs
    linarith
  obtain ⟨δ2, hδ2, hδ21, hδ2far⟩ : ∃ δ2 : ℝ, 0 < δ2 ∧ δ2 ≤ 1 ∧
      ∀ z ∈ rhoClosedBall Ωs (fs 0) r0s ∩ schwarzNorm Ωs ⁻¹' Ici η',
        R + δ2 ≤ hdist x0 (epstein Ωs z) := by
    rcases (rhoClosedBall Ωs (fs 0) r0s ∩ schwarzNorm Ωs ⁻¹' Ici η').eq_empty_or_nonempty
      with he | hne
    · refine ⟨1, one_pos, le_rfl, ?_⟩
      rw [he]
      intro z hz
      simp at hz
    · have hgc : ContinuousOn (fun z => hdist x0 (epstein Ωs z))
          (rhoClosedBall Ωs (fs 0) r0s ∩ schwarzNorm Ωs ⁻¹' Ici η') :=
        (hdC x0 hx0).comp (hXCs.mono fun _ h => h.1.1) (fun z hz => hXUs z hz.1.1)
      obtain ⟨m, hm, hmin⟩ := hC2.exists_isMinOn hne hgc
      have hRm := hC2far m hm
      refine ⟨min 1 (hdist x0 (epstein Ωs m) - R), lt_min one_pos (by linarith),
        min_le_left _ _, fun z hz => ?_⟩
      have h1 : hdist x0 (epstein Ωs m) ≤ hdist x0 (epstein Ωs z) := hmin hz
      have h2 := min_le_right 1 (hdist x0 (epstein Ωs m) - R)
      linarith
  -- the neighbourhood `{w ∈ Ω : d(X(w₀), X(w)) < min δ₁ δ₂}`
  have hδ : 0 < min δ1 δ2 := lt_min hδ1 hδ2
  have hg : ContinuousAt (fun w => hdist x0 (epstein Ω w)) w0 :=
    ((hdC x0 hx0).comp hXC (fun w hw => hXU w hw)).continuousAt (hΩo.mem_nhds hw0Ω)
  have hg0 : Iio (min δ1 δ2) ∈ 𝓝 (hdist x0 (epstein Ω w0)) := by
    rw [← hx0def, hself]
    exact Iio_mem_nhds hδ
  filter_upwards [hΩo.mem_nhds hw0Ω, hg.preimage_mem_nhds hg0] with w hwΩ hwd
  have hwd' : hdist x0 (epstein Ω w) < min δ1 δ2 := hwd
  have hd1 : hdist x0 (epstein Ω w) < δ1 := lt_of_lt_of_le hwd' (min_le_left _ _)
  have hd2 : hdist x0 (epstein Ω w) < δ2 := lt_of_lt_of_le hwd' (min_le_right _ _)
  have hXw := hXU w hwΩ
  refine ⟨hwΩ, lt_of_le_of_lt ?_ hη'2⟩
  refine Real.sSup_le ?_ (hς0.trans hη'1.le)
  rintro r (⟨w', hw'Ω, hw'm, rfl⟩ | ⟨z, hzΩ, hzm, rfl⟩)
  · by_contra hcon
    rw [not_le] at hcon
    have htri : hdist x0 (epstein Ω w') ≤ hdist x0 (epstein Ω w) + hdist (epstein Ω w) (epstein Ω w') :=
      s02_hdist_triangle hx0 hXw (hXU w' hw'Ω)
    have hw'R : hdist (epstein Ω w) (epstein Ω w') ≤ R := hw'm.2
    have hq := hqi Ω Ωs hpair w0 hw0Ω w' hw'Ω
    have hin : w' ∈ rhoClosedBall Ω w0 r0 ∩ schwarzNorm Ω ⁻¹' Ici η' := by
      refine ⟨⟨hw'Ω, ?_⟩, hcon.le⟩
      have : A * hdist x0 (epstein Ω w') ≤ A * (R + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hA
      rw [hr0def]
      linarith
    have := hδ1far w' hin
    linarith
  · by_contra hcon
    rw [not_le] at hcon
    have htri : hdist x0 (epstein Ωs z) ≤ hdist x0 (epstein Ω w) + hdist (epstein Ω w) (epstein Ωs z) :=
      s02_hdist_triangle hx0 hXw (hXUs z hzΩ)
    have hzR : hdist (epstein Ω w) (epstein Ωs z) ≤ R := hzm.2
    have htri2 : hdist (epstein Ωs (fs 0)) (epstein Ωs z) ≤
        hdist (epstein Ωs (fs 0)) x0 + hdist x0 (epstein Ωs z) :=
      s02_hdist_triangle (hXUs _ hz0) hx0 (hXUs z hzΩ)
    have hq := hqi Ωs Ω hpairs (fs 0) hz0 z hzΩ
    have hin : z ∈ rhoClosedBall Ωs (fs 0) r0s ∩ schwarzNorm Ωs ⁻¹' Ici η' := by
      refine ⟨⟨hzΩ, ?_⟩, hcon.le⟩
      have : A * hdist (epstein Ωs (fs 0)) (epstein Ωs z) ≤
          A * (hdist (epstein Ωs (fs 0)) x0 + (R + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) hA
      rw [hr0sdef]
      linarith
    have := hδ2far z hin
    linarith

/-- F0d: identification of the slab.  With the data of Lemma 4.2 (ii)–(iv) at a base point `w`,
`slabTop = t` and `slabMap = N` on `\overline{B_ρ(w, L)}`: no `τ ∈ (0, t v)` reaches
`Σ* ⊆ U*` (`s03_qik_mem`), and a point `z*` with `X*(z*) = E(v, t v)` is `N v` by the set identity
of (iii) and the injectivity of `E` on `Z`. -/
theorem s04_sl_slab_id {K : ℝ} {Ω Ωs : Set ℂ} (hpair : IsKQuasiPair Ω Ωs K) {L T ε : ℝ}
    {w : ℂ} {t : ℂ → ℝ} {N : ℂ → ℂ} (hεT : ε ≤ T + 1)
    (hinj : InjOn (normalMap Ω) (rhoClosedBall Ω w (L + 1) ×ˢ Icc (-2) (T + 2)))
    (hN : MapsTo N (rhoClosedBall Ω w L) Ωs)
    (ht : ∀ v ∈ rhoClosedBall Ω w L,
      0 < t v ∧ t v < ε ∧ epstein Ωs (N v) = normalGeod Ω v (t v))
    (hset : {z | z ∈ Ωs ∧ epstein Ωs z ∈ normalMap Ω '' (rhoClosedBall Ω w L ×ˢ Icc (-1) (T + 1))} =
      N '' rhoClosedBall Ω w L)
    (hout : ∀ v ∈ rhoClosedBall Ω w L, ∀ τ ∈ Ico 0 (t v), normalGeod Ω v τ ∉ horoUnion Ωs) :
    ∀ v ∈ rhoClosedBall Ω w L, slabTop Ω Ωs v = t v ∧ slabMap Ω Ωs v = N v := by
  intro v hv
  have hΩs := s02_jordanPair_riemannMap (s03_b0_jordanPair (s03_qce_swap hpair))
  obtain ⟨ht0, htε, hNv⟩ := ht v hv
  -- `slabTop v = t v`: `t v` is in the set, and no smaller `τ > 0` is (`Σ* ⊆ U*`)
  have hTop : slabTop Ω Ωs v = t v := by
    refine IsLeast.csInf_eq ⟨⟨ht0, N v, hN hv, hNv⟩, ?_⟩
    rintro τ ⟨hτ0, z, hz, hzτ⟩
    by_contra hlt
    rw [not_le] at hlt
    exact hout v hv τ ⟨hτ0.le, hlt⟩ (hzτ ▸ s03_qik_mem hΩs hz)
  refine ⟨hTop, ?_⟩
  have hex : ∃ z ∈ Ωs, epstein Ωs z = normalGeod Ω v (slabTop Ω Ωs v) :=
    ⟨N v, hN hv, by rw [hTop]; exact hNv⟩
  have hsm : slabMap Ω Ωs v = hex.choose := by
    unfold slabMap
    split_ifs
    rfl
  obtain ⟨hz, hzE⟩ := hex.choose_spec
  rw [hsm]
  have hball' : ∀ u ∈ rhoClosedBall Ω w L, u ∈ rhoClosedBall Ω w (L + 1) :=
    fun u hu => ⟨hu.1, by linarith [hu.2]⟩
  have hzmem : hex.choose ∈ {z | z ∈ Ωs ∧
      epstein Ωs z ∈ normalMap Ω '' (rhoClosedBall Ω w L ×ˢ Icc (-1) (T + 1))} :=
    ⟨hz, (v, t v), ⟨hv, ⟨by linarith, by linarith⟩⟩, by
      show normalGeod Ω v (t v) = epstein Ωs hex.choose
      rw [hzE, hTop]⟩
  rw [hset] at hzmem
  obtain ⟨v', hv', hv'z⟩ := hzmem
  obtain ⟨ht0', htε', hNv'⟩ := ht v' hv'
  have hE : normalMap Ω (v', t v') = normalMap Ω (v, t v) := by
    show normalGeod Ω v' (t v') = normalGeod Ω v (t v)
    rw [← hNv', hv'z, hzE, hTop]
  have hvv : v' = v := congrArg Prod.fst
    (hinj ⟨hball' v' hv', ⟨by linarith, by linarith⟩⟩ ⟨hball' v hv, ⟨by linarith, by linarith⟩⟩ hE)
  rw [← hv'z, hvv]

/-- Uniform form of Corollary 4.4 (`cor_coverage`): every `η ≤ η₀`, `R ≥ R₁`. -/
theorem s04_sl_cor_coverage_unif : ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ R₁ : ℝ, ∀ η R : ℝ, 0 < η → η ≤ η₀ → R₁ ≤ R →
      ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab →
        (∀ q ∈ gap Ω Ωs, IsGoodParam Ω Ωs η R (lab q) →
          ∃ τ : ℝ, 0 < τ ∧ τ < slabTop Ω Ωs (lab q) ∧ q = normalGeod Ω (lab q) τ) ∧
        ∀ v : ℂ, IsGoodParam Ω Ωs η R v → ∀ τ ∈ Ioo 0 (slabTop Ω Ωs v),
          normalGeod Ω v τ ∈ gap Ω Ωs ∧ lab (normalGeod Ω v τ) = v := by
  intro K hK ε hε hε'
  obtain ⟨D, hD⟩ := lem_width K
  have hT : (0 : ℝ) < max D 0 + 2 := by positivity
  obtain ⟨η₀, hη₀, R₁, htube⟩ :=
    s04_sl_tube_unif K 1 (max D 0 + 2) 6 ε 0 hK one_pos hT le_rfl hε hε' le_rfl
  refine ⟨η₀, hη₀, R₁, fun η R hη hηle hR Ω Ωs hp hnl lab hlab => ?_⟩
  have hJ := s03_b0_jordanPair hp
  have hΩ := s02_jordanPair_riemannMap hJ
  have hΩs := s02_jordanPair_riemannMap (s03_b0_jordanPair (s03_qce_swap hp))
  -- the slab data at a good base point `v` (`lem_tube` with `L = 1`, `T = D_K + 2`)
  have key : ∀ v, IsGoodParam Ω Ωs η R v → ∃ t : ℂ → ℝ, ∃ N : ℂ → ℂ,
      slabTop Ω Ωs v = t v ∧ N v ∈ Ωs ∧ epstein Ωs (N v) = normalGeod Ω v (t v) ∧
      (∀ τ ∈ Ioc (t v) (max D 0 + 2), normalGeod Ω v τ ∈ interior (horoUnion Ωs)) ∧
      ∀ τ ∈ Ioo 0 (t v), normalGeod Ω v τ ∈ gap Ω Ωs ∧
        ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab → lab (normalGeod Ω v τ) = v := by
    intro v hv
    obtain ⟨-, ⟨hEe, -⟩, t, N, -, -, hNm, -, ht, hset, hiv, -, -, hfin⟩ :=
      htube η R hη hηle hR Ω Ωs hp hnl v hv
    have hvB : v ∈ rhoClosedBall Ω v 1 := ⟨hv.1, by rw [s04_tb_dist_self hΩ hv.1]; norm_num⟩
    obtain ⟨hTop, -⟩ := s04_sl_slab_id hp (by linarith [le_max_right D 0]) hEe.2.1 hNm ht hset
      (fun u hu => (hiv u hu).1) v hvB
    exact ⟨t, N, hTop, hNm hvB, (ht v hvB).2.2, (hiv v hvB).2, hfin v hvB⟩
  refine ⟨fun q hq hgood => ?_, fun v hv τ hτ => ?_⟩
  · -- `q = E(w(q), d(q, U))` with `d(q, U) ≤ D_K`; `d(q, U) ≥ t` would put `q` in `U*`
    obtain ⟨t, N, hTop, hNΩ, hNE, hint, -⟩ := key (lab q) hgood
    have hqU : q ∉ horoUnion Ω := fun h => hq.2 (Or.inl h)
    obtain ⟨hlq, hmin⟩ := hlab.2 q ⟨hq.1, hqU⟩
    obtain ⟨hqE, hd0, -, -⟩ := lem_nearest hJ hnl hq.1 hqU hlq hmin
    have hdD := ((hD Ω Ωs hp hnl).1 q hq).1
    refine ⟨hdistSet q (horoUnion Ω), hd0, ?_, hqE⟩
    rw [hTop]
    by_contra hle
    rw [not_lt] at hle
    apply hq.2
    right
    rcases hle.lt_or_eq with hlt | heq
    · rw [hqE]
      exact interior_subset (hint _ ⟨hlt, by linarith [le_max_left D 0]⟩)
    · rw [hqE, ← heq, ← hNE]
      exact s03_qik_mem hΩs hNΩ
  · obtain ⟨t, N, hTop, -, -, -, hfin⟩ := key v hv
    rw [hTop] at hτ
    exact ⟨(hfin τ hτ).1, (hfin τ hτ).2 lab hlab⟩

/-- Uniform form of (4.6) (`eq_def_N`): every `η ≤ η₀`, `R ≥ R₁`. -/
theorem s04_sl_eq_def_N_unif : ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ R₁ : ℝ, ∀ η R : ℝ, 0 < η → η ≤ η₀ → R₁ ≤ R →
      ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      IsOpen (goodSet Ω Ωs η R) ∧ ContDiffOn ℝ ∞ (slabTop Ω Ωs) (goodSet Ω Ωs η R) ∧
        ContDiffOn ℝ ∞ (slabMap Ω Ωs) (goodSet Ω Ωs η R) ∧
        ∀ w ∈ goodSet Ω Ωs η R, slabMap Ω Ωs w ∈ Ωs ∧ 0 < slabTop Ω Ωs w ∧
          slabTop Ω Ωs w < ε ∧
          epstein Ωs (slabMap Ω Ωs w) = normalGeod Ω w (slabTop Ω Ωs w) := by
  intro K hK ε hε hε'
  obtain ⟨η₀, hη₀, R₁, htube⟩ := s04_sl_tube_unif K 1 1 6 ε 0 hK one_pos one_pos le_rfl hε hε' le_rfl
  refine ⟨η₀, hη₀, R₁, fun η R hη hηle hR Ω Ωs hp hnl => ?_⟩
  have hJ := s03_b0_jordanPair hp
  have hΩ := s02_jordanPair_riemannMap hJ
  -- closed `ρ`-balls of radius `1` are neighbourhoods of their centres
  have hnhds : ∀ v ∈ Ω, rhoClosedBall Ω v 1 ∈ 𝓝 v := by
    intro v hvΩ
    obtain ⟨f, hf, hf0⟩ := s02_riemannMap_at hJ hvΩ
    have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
    have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
    have hψc : ContinuousOn (Function.invFunOn f unitDisc) Ω := (s02_contDiffOn_invFun hf).1.continuousOn
    have hvi : v ∈ f '' unitDisc := by rw [hf.2.2]; exact hvΩ
    have hψv : Function.invFunOn f unitDisc v = 0 :=
      hf.2.1 (Function.invFunOn_mem hvi) h0 ((Function.invFunOn_eq hvi).trans hf0.symm)
    have hc : 0 < √((Real.cosh 1 - 1) / (Real.cosh 1 + 1)) :=
      Real.sqrt_pos.mpr (div_pos (by linarith [Real.one_lt_cosh.mpr (one_ne_zero (α := ℝ))])
        (by positivity))
    have hpre := (hψc.continuousAt (hΩo.mem_nhds hvΩ)).preimage_mem_nhds
      (isOpen_ball.mem_nhds (by rw [hψv]; exact mem_ball_self hc))
    filter_upwards [hΩo.mem_nhds hvΩ, hpre] with u huΩ huc
    have hui : u ∈ f '' unitDisc := by rw [hf.2.2]; exact huΩ
    have hd : Function.invFunOn f unitDisc u ∈ {z | z ∈ unitDisc ∧ diskDist 0 z ≤ 1} := by
      rw [s04_tb_disk_ball zero_le_one]
      exact ball_subset_closedBall huc
    refine ⟨huΩ, ?_⟩
    show poincareDist Ω v u ≤ 1
    rw [← hf0, ← Function.invFunOn_eq hui, subsec_poincare_dist hf h0 (Function.invFunOn_mem hui)]
    exact hd.2
  -- the slab data at a good base point `v` (`lem_tube` with `L = T = 1`)
  have key : ∀ v ∈ goodSet Ω Ωs η R, ∃ t : ℂ → ℝ, ∃ N : ℂ → ℂ,
      SmoothNear t (rhoClosedBall Ω v 1) ∧ SmoothNear N (rhoClosedBall Ω v 1) ∧
      (∀ u ∈ rhoClosedBall Ω v 1, slabTop Ω Ωs u = t u ∧ slabMap Ω Ωs u = N u) ∧
      N v ∈ Ωs ∧ 0 < t v ∧ t v < ε ∧ epstein Ωs (N v) = normalGeod Ω v (t v) := by
    intro v hv
    obtain ⟨-, ⟨hEe, -⟩, t, N, htsm, hNe, hNm, -, ht, hset, hiv, -⟩ :=
      htube η R hη hηle hR Ω Ωs hp hnl v hv
    have hvB : v ∈ rhoClosedBall Ω v 1 := mem_of_mem_nhds (hnhds v hv.1)
    have hid := s04_sl_slab_id hp (by linarith) hEe.2.1 hNm ht hset (fun u hu => (hiv u hu).1)
    exact ⟨t, N, htsm, hNe.1, hid, hNm hvB, (ht v hvB).1, (ht v hvB).2.1, (ht v hvB).2.2⟩
  refine ⟨s04_sl_good_open hp η R, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨t, N, ⟨V, hVo, hBV, htV⟩, -, hid, -⟩ := key v hv
    have hvB : v ∈ rhoClosedBall Ω v 1 := mem_of_mem_nhds (hnhds v hv.1)
    refine ((htV.contDiffAt (hVo.mem_nhds (hBV hvB))).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hnhds v hv.1] with u hu using (hid u hu).1
  · obtain ⟨t, N, -, ⟨V, hVo, hBV, hNV⟩, hid, -⟩ := key v hv
    have hvB : v ∈ rhoClosedBall Ω v 1 := mem_of_mem_nhds (hnhds v hv.1)
    refine ((hNV.contDiffAt (hVo.mem_nhds (hBV hvB))).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hnhds v hv.1] with u hu using (hid u hu).2
  · obtain ⟨t, N, -, -, hid, hN, h0, hε1, hE⟩ := key v hv
    have hvB : v ∈ rhoClosedBall Ω v 1 := mem_of_mem_nhds (hnhds v hv.1)
    rw [(hid v hvB).1, (hid v hvB).2]
    exact ⟨hN, h0, hε1, hE⟩

/-- Uniform form of Proposition 4.5 (`prop_RN`): every `η ≤ η₀`, `R ≥ R₁`. -/
theorem s04_sl_prop_RN_unif : ∀ K : ℝ, 1 ≤ K → ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ R₁ : ℝ, ∀ η R : ℝ, 0 < η → η ≤ η₀ → R₁ ≤ R →
      ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab →
        (∀ w ∈ goodSet Ω Ωs η R, lab (epstein Ωs (slabMap Ω Ωs w)) = w) ∧
        InjOn (slabMap Ω Ωs) (goodSet Ω Ωs η R) ∧
        ∀ w ∈ goodSet Ω Ωs η R, ∀ z ∈ Ωs, lab (epstein Ωs z) = w →
          poincareDist Ωs z (slabMap Ω Ωs w) ≤ M := by
  intro K hK
  obtain ⟨R₀', hUL⟩ := prop_unique_label K
  obtain ⟨A, B, hA, hqi⟩ := s03_qi_lower K
  obtain ⟨D, hD⟩ := lem_width K
  refine ⟨A * (max D 0 + 1) + B, fun ε hε hε' => ?_⟩
  obtain ⟨η₀, hη₀, R₁, htube⟩ := s04_sl_tube_unif K 1 1 6 ε (max R₀' 0 + 1) hK one_pos one_pos
    le_rfl hε hε' (by positivity)
  refine ⟨η₀, hη₀, R₁, fun η R hη hηle hR Ω Ωs hp hnl lab hlab => ?_⟩
  have hJ := s03_b0_jordanPair hp
  have hΩ := s02_jordanPair_riemannMap hJ
  have hΩs := s02_jordanPair_riemannMap (s03_b0_jordanPair (s03_qce_swap hp))
  -- the slab data at a good `v` (`lem_tube` with `L = T = 1` and `R₀ = max R₀' 0 + 1`, so that (v)
  -- covers the closed ball of radius `R₀' + 2` of `prop_unique_label`)
  have key : ∀ v ∈ goodSet Ω Ωs η R, slabMap Ω Ωs v ∈ Ωs ∧
      epstein Ωs (slabMap Ω Ωs v) = normalGeod Ω v (slabTop Ω Ωs v) ∧ 0 < slabTop Ω Ωs v ∧
      slabTop Ω Ωs v < ε ∧
      ∀ w' ∈ Ω, poincareDist Ω v w' ≤ R₀' + 2 → schwarzNorm Ω w' < 1 / 2 := by
    intro v hv
    obtain ⟨-, ⟨hEe, -⟩, t, N, -, -, hNm, -, ht, hset, hiv, hv5, -⟩ :=
      htube η R hη hηle hR Ω Ωs hp hnl v hv
    have hvB : v ∈ rhoClosedBall Ω v 1 := ⟨hv.1, by rw [s04_tb_dist_self hΩ hv.1]; norm_num⟩
    obtain ⟨hTop, hMap⟩ := s04_sl_slab_id hp (by linarith) hEe.2.1 hNm ht hset
      (fun u hu => (hiv u hu).1) v hvB
    rw [hTop, hMap]
    exact ⟨hNm hvB, (ht v hvB).2.2, (ht v hvB).1, (ht v hvB).2.1,
      fun w' hw' hd => (hv5 v hvB).1 w' ⟨hw', by linarith [le_max_left R₀' 0]⟩⟩
  -- (4.7): `E(v, t(v))` has the unique label `v` (`prop_unique_label`, `t(v) < ε < 1`)
  have hlabN : ∀ v ∈ goodSet Ω Ωs η R, lab (epstein Ωs (slabMap Ω Ωs v)) = v := by
    intro v hv
    obtain ⟨-, hE, h0, hε1, hs⟩ := key v hv
    rw [hE]
    exact (((hUL Ω Ωs hp hnl).1 v hv.1 hs).2.1 lab hlab (slabTop Ω Ωs v) ⟨h0, by linarith⟩).1
  refine ⟨hlabN, fun v hv v' hv' hvv => ?_, fun v hv z hz hlz => ?_⟩
  · calc v = lab (epstein Ωs (slabMap Ω Ωs v)) := (hlabN v hv).symm
      _ = lab (epstein Ωs (slabMap Ω Ωs v')) := by rw [hvv]
      _ = v' := hlabN v' hv'
  · -- `X(v)` is within `D_K` of `X*(z)` (`s03_qik_pt`), and within `t(v) < 1` of `X*(N v)`
    obtain ⟨hNΩ, hE, h0, hε1, -⟩ := key v hv
    have hsep := (prop_separation_b hJ hnl).2
    obtain ⟨hDg, -, hDs⟩ := hD Ω Ωs hp hnl
    obtain ⟨-, hzU, hdz⟩ := s03_qik_pt hp hnl hsep hlab (le_max_right D 0)
      (fun q hq => (hDg q hq).1.trans (le_max_left D 0))
      (fun ws hws => (hDs ws hws).trans (le_max_left D 0)) (q := epstein Ωs z) (ℓ := v)
      (Or.inr (Or.inl ⟨z, hz, rfl, hlz.symm⟩))
    have hXv : epstein Ω v ∈ UHS := s04_tb_ep_uhs hΩ hv.1
    have hNU : epstein Ωs (slabMap Ω Ωs v) ∈ UHS := s04_tb_ep_uhs hΩs hNΩ
    have hdN : hdist (epstein Ω v) (epstein Ωs (slabMap Ω Ωs v)) ≤ 1 := by
      rw [hE, ← (lem_normal_b hΩ hv.1).2.2, (lem_normal_b hΩ hv.1).2.1, zero_sub, abs_neg,
        abs_of_pos h0]
      linarith
    have htri := s02_hdist_triangle hzU hXv hNU
    have hq := hqi Ωs Ω (s03_qce_swap hp) z hz (slabMap Ω Ωs v) hNΩ
    have hAm : A * hdist (epstein Ωs z) (epstein Ωs (slabMap Ω Ωs v)) ≤ A * (max D 0 + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hA
    linarith

/-- **Corollary 4.4** (Coverage of the good part of the gap, `cor:coverage`,
sec04-tube.tex:283), with `T = D_K + 2` and `(η, R)` as in Lemma 4.2.  If `q ∈ 𝒩` and `w(q)` is
`(η,R)`-good, then `q = E(w(q), τ)` with `0 < τ < t(w(q))` (4.5).  Conversely, if `v` is good and
`0 < τ < t(v)`, then `E(v, τ) ∈ 𝒩` and its label is `v`.  Here `t = slabTop` (on `G₀` it is the
function `t` of Lemma 4.2). -/
theorem cor_coverage : ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ η : ℝ, 0 < η ∧ ∃ R : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab →
        (∀ q ∈ gap Ω Ωs, IsGoodParam Ω Ωs η R (lab q) →
          ∃ τ : ℝ, 0 < τ ∧ τ < slabTop Ω Ωs (lab q) ∧ q = normalGeod Ω (lab q) τ) ∧
        ∀ v : ℂ, IsGoodParam Ω Ωs η R v → ∀ τ ∈ Ioo 0 (slabTop Ω Ωs v),
          normalGeod Ω v τ ∈ gap Ω Ωs ∧ lab (normalGeod Ω v τ) = v := by
  intro K hK ε hε hε'
  obtain ⟨η₀, hη₀, R₁, h⟩ := s04_sl_cor_coverage_unif K hK ε hε hε'
  exact ⟨η₀, hη₀, R₁, h η₀ R₁ hη₀ le_rfl le_rfl⟩

/-! ## §4.3 The projection identity and the Jacobian -/

/-- **(4.6)** (`eq:def-N`, sec04-tube.tex:313).  For `(η, R)` as in Lemma 4.2, the set `G₀` of good
parameters is open, the functions `t` and `N` obtained from different base points agree on
overlaps and define a smooth function `t = slabTop` and a smooth map `N = slabMap` on `G₀`, with
`N(G₀) ⊆ Ω*`, `0 < t < ε` and `X*(N(w)) = E(w, t(w))`. -/
theorem eq_def_N : ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ η : ℝ, 0 < η ∧ ∃ R : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      IsOpen (goodSet Ω Ωs η R) ∧ ContDiffOn ℝ ∞ (slabTop Ω Ωs) (goodSet Ω Ωs η R) ∧
        ContDiffOn ℝ ∞ (slabMap Ω Ωs) (goodSet Ω Ωs η R) ∧
        ∀ w ∈ goodSet Ω Ωs η R, slabMap Ω Ωs w ∈ Ωs ∧ 0 < slabTop Ω Ωs w ∧
          slabTop Ω Ωs w < ε ∧
          epstein Ωs (slabMap Ω Ωs w) = normalGeod Ω w (slabTop Ω Ωs w) := by
  intro K hK ε hε hε'
  obtain ⟨η₀, hη₀, R₁, h⟩ := s04_sl_eq_def_N_unif K hK ε hε hε'
  exact ⟨η₀, hη₀, R₁, h η₀ R₁ hη₀ le_rfl le_rfl⟩

/-- **Proposition 4.5** (`prop:RN`, sec04-tube.tex:317).  For `w ∈ G₀` and every label,
`R(N(w)) = w` (4.7), where `R = w ∘ X*`.  In particular `N` is injective on `G₀`.  Moreover every
`z*` with `R(z*) = w` satisfies `d_{ρ*}(z*, N(w)) ≤ A_K(D_K + 1) + B_K`; the constant
`A_K(D_K+1) + B_K` depends only on `K` and is rendered as `M`. -/
theorem prop_RN : ∀ K : ℝ, 1 ≤ K → ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ η : ℝ, 0 < η ∧ ∃ R : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab →
        (∀ w ∈ goodSet Ω Ωs η R, lab (epstein Ωs (slabMap Ω Ωs w)) = w) ∧
        InjOn (slabMap Ω Ωs) (goodSet Ω Ωs η R) ∧
        ∀ w ∈ goodSet Ω Ωs η R, ∀ z ∈ Ωs, lab (epstein Ωs z) = w →
          poincareDist Ωs z (slabMap Ω Ωs w) ≤ M := by
  intro K hK
  obtain ⟨M, hM⟩ := s04_sl_prop_RN_unif K hK
  refine ⟨M, fun ε hε hε' => ?_⟩
  obtain ⟨η₀, hη₀, R₁, h⟩ := hM ε hε hε'
  exact ⟨η₀, hη₀, R₁, h η₀ R₁ hη₀ le_rfl le_rfl⟩

/-! ## §4.3 The metric comparison (interface JC, w3)

`s04_jc_*`: pointwise reading of the `C^j` bounds of `lem_tube` (HS norm ⇒ operator bound), the
Fermi form of `h(v) = E(v, t v)` (from `lem_shape_a`), the chain rule `dX* ∘ dN = dh`, the scalar
estimates and a `2 × 2` determinant lemma; `s04_jc_unif` is Lemma 4.6 in uniform form (every
`η ≤ η₀`, `R ≥ R₁`) with the explicit constant `C = 10`. -/

/-- JC1: a `C^j` bound gives the pointwise bound of every `∇^i T`, `i ≤ j`, on `E`. -/
theorem s04_jc_cj_point {Ω E : Set ℂ} {k : ℕ} {T : TensorField k} {i j : ℕ} (hij : i ≤ j)
    {w : ℂ} (hw : w ∈ E) {ε : ℝ} (hε : 0 ≤ ε) (h : rhoCjNorm Ω j T E ≤ ENNReal.ofReal ε) :
    rhoTensorNorm Ω (rhoIterCovDeriv Ω i T) w ≤ ε := by
  have h1 : ENNReal.ofReal (rhoTensorNorm Ω (rhoIterCovDeriv Ω i T) w) ≤ rhoCjNorm Ω j T E := by
    unfold rhoCjNorm
    exact le_iSup₂_of_le i hij (le_iSup₂_of_le w hw le_rfl)
  exact (ENNReal.ofReal_le_ofReal_iff hε).mp (h1.trans h)

/-- JC2: the Hilbert–Schmidt `ρ`-norm of a bilinear `2`-tensor bounds it as an operator:
`|T(a, b)| ≤ ‖T‖_ρ λ² |a| |b|`. -/
theorem s04_jc_hs2 {Ω : Set ℂ} {T : TensorField 2} {w : ℂ} (hl : 0 < poincareDensity Ω w)
    (hT : ∀ a b : ℂ, T w ![a, b] = a.re * b.re * T w ![1, 1] + a.re * b.im * T w ![1, I] +
      a.im * b.re * T w ![I, 1] + a.im * b.im * T w ![I, I]) (a b : ℂ) :
    |T w ![a, b]| ≤ rhoTensorNorm Ω T w * poincareDensity Ω w ^ 2 * (‖a‖ * ‖b‖) := by
  set t1 := T w ![1, 1]
  set t2 := T w ![1, I]
  set t3 := T w ![I, 1]
  set t4 := T w ![I, I]
  set Sf := ∑ idx : Fin 2 → Fin 2, (T w fun i => frameVec (idx i)) ^ 2 with hSf
  have hfr : ∀ x y : Fin 2, (fun i => frameVec (![x, y] i)) = ![frameVec x, frameVec y] := by
    intro x y
    funext i
    fin_cases i <;> rfl
  have hsub : t1 ^ 2 + t2 ^ 2 + t3 ^ 2 + t4 ^ 2 ≤ Sf := by
    have hS : (({![0, 0], ![0, 1], ![1, 0], ![1, 1]} : Finset (Fin 2 → Fin 2))) ⊆ Finset.univ :=
      Finset.subset_univ _
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun _ _ _ => sq_nonneg _))
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, hfr, hfr, hfr, hfr]
    simp only [frameVec, Matrix.cons_val_zero, Matrix.cons_val_one, t1, t2, t3, t4]
    ring
  have hN : rhoTensorNorm Ω T w * poincareDensity Ω w ^ 2 = √Sf := by
    unfold rhoTensorNorm
    rw [← hSf]
    field_simp
  rw [hN, hT a b]
  have ha : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hb : ‖b‖ ^ 2 = b.re ^ 2 + b.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hsq : (a.re * b.re * t1 + a.re * b.im * t2 + a.im * b.re * t3 + a.im * b.im * t4) ^ 2 ≤
      (√Sf * (‖a‖ * ‖b‖)) ^ 2 := by
    have hS0 : 0 ≤ Sf := le_trans (by positivity) hsub
    rw [mul_pow, Real.sq_sqrt hS0, mul_pow, ha, hb]
    have hcs : (a.re * b.re * t1 + a.re * b.im * t2 + a.im * b.re * t3 + a.im * b.im * t4) ^ 2 ≤
        ((a.re ^ 2 + a.im ^ 2) * (b.re ^ 2 + b.im ^ 2)) * (t1 ^ 2 + t2 ^ 2 + t3 ^ 2 + t4 ^ 2) := by
      nlinarith [sq_nonneg (a.re * b.re * t2 - a.re * b.im * t1),
        sq_nonneg (a.re * b.re * t3 - a.im * b.re * t1), sq_nonneg (a.re * b.re * t4 - a.im * b.im * t1),
        sq_nonneg (a.re * b.im * t3 - a.im * b.re * t2), sq_nonneg (a.re * b.im * t4 - a.im * b.im * t2),
        sq_nonneg (a.im * b.re * t4 - a.im * b.im * t3)]
    refine hcs.trans ?_
    rw [mul_comm Sf]
    exact mul_le_mul_of_nonneg_left hsub (by positivity)
  have h0 : 0 ≤ √Sf * (‖a‖ * ‖b‖) := by positivity
  calc |a.re * b.re * t1 + a.re * b.im * t2 + a.im * b.re * t3 + a.im * b.im * t4|
      = √((a.re * b.re * t1 + a.re * b.im * t2 + a.im * b.re * t3 + a.im * b.im * t4) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ √((√Sf * (‖a‖ * ‖b‖)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = √Sf * (‖a‖ * ‖b‖) := Real.sqrt_sq h0

/-- JC3: `I - ρ` is bilinear (in the frame `(1, i)`). -/
theorem s04_jc_fff_bil (Ω : Set ℂ) (w a b : ℂ) :
    (fffT Ω - rhoMetricT Ω) w ![a, b] =
      a.re * b.re * (fffT Ω - rhoMetricT Ω) w ![1, 1] +
        a.re * b.im * (fffT Ω - rhoMetricT Ω) w ![1, I] +
        a.im * b.re * (fffT Ω - rhoMetricT Ω) w ![I, 1] +
        a.im * b.im * (fffT Ω - rhoMetricT Ω) w ![I, I] := by
  have key : ∀ z : ℂ, fderiv ℝ (epstein Ω) w z =
      z.re • fderiv ℝ (epstein Ω) w 1 + z.im • fderiv ℝ (epstein Ω) w I := by
    intro z
    conv_lhs => rw [show z = z.re • (1 : ℂ) + z.im • I by
      apply Complex.ext <;> simp]
    rw [map_add, map_smul, map_smul]
  simp only [Pi.sub_apply, fffT, rhoMetricT, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [key a, key b]
  unfold hypInner
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Complex.real_smul, map_add, map_mul, Complex.conj_ofReal, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.add_im,
    Complex.mul_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, map_one,
    Complex.conj_I, Complex.neg_re, Complex.neg_im]
  ring

/-- JC4: the lowered shape operator `ρ(B ·, ·)` is bilinear (in the frame `(1, i)`). -/
theorem s04_jc_shape_bil (Ω : Set ℂ) (w a b : ℂ) :
    shapeT Ω w ![a, b] =
      a.re * b.re * shapeT Ω w ![1, 1] + a.re * b.im * shapeT Ω w ![1, I] +
        a.im * b.re * shapeT Ω w ![I, 1] + a.im * b.im * shapeT Ω w ![I, I] := by
  simp only [shapeT, cvec, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.one_re, Complex.one_im, Complex.I_re,
    Complex.I_im]
  ring

/-- JC5: `ρ(Ba, Ba) = λ² |Ba|²`. -/
theorem s04_jc_shape_self (Ω : Set ℂ) (w a : ℂ) :
    shapeT Ω w ![a, shapeApply Ω w a] = poincareDensity Ω w ^ 2 * ‖shapeApply Ω w a‖ ^ 2 := by
  simp only [shapeT, shapeApply, Matrix.cons_val_zero, Matrix.cons_val_one]
  set y := shapeMat Ω w *ᵥ cvec a
  have hc : cvec (ofCvec y) = y := by
    funext i
    fin_cases i <;> rfl
  rw [hc, Complex.sq_norm, Complex.normSq_apply]
  simp only [dotProduct, Fin.sum_univ_two, ofCvec]

/-- JC6: the first covariant derivative of a function is its differential:
`|dt(v)| ≤ ‖∇t‖_ρ λ |v|`. -/
theorem s04_jc_dt {Ω : Set ℂ} {t : ℂ → ℝ} {w : ℂ} (hl : 0 < poincareDensity Ω w) (v : ℂ) :
    |fderiv ℝ t w v| ≤
      rhoTensorNorm Ω (rhoIterCovDeriv Ω 1 (scalarField t)) w * (poincareDensity Ω w * ‖v‖) := by
  have hT : ∀ u : Fin 1 → ℂ, rhoIterCovDeriv Ω 1 (scalarField t) w u = fderiv ℝ t w (u 0) := by
    intro u
    simp only [rhoIterCovDeriv, rhoCovDeriv, scalarField, Finset.univ_eq_empty, Finset.sum_empty,
      sub_zero]
    rfl
  set d1 := fderiv ℝ t w 1
  set d2 := fderiv ℝ t w I
  set Sf := ∑ idx : Fin 1 → Fin 2,
    (rhoIterCovDeriv Ω 1 (scalarField t) w fun i => frameVec (idx i)) ^ 2 with hSf
  have hsub : d1 ^ 2 + d2 ^ 2 ≤ Sf := by
    have hS : (({![0], ![1]} : Finset (Fin 1 → Fin 2))) ⊆ Finset.univ := Finset.subset_univ _
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun _ _ _ => sq_nonneg _))
    rw [Finset.sum_insert (by decide), Finset.sum_singleton, hT, hT]
    rfl
  have hN : rhoTensorNorm Ω (rhoIterCovDeriv Ω 1 (scalarField t)) w * poincareDensity Ω w = √Sf := by
    unfold rhoTensorNorm
    rw [← hSf, zero_add, pow_one]
    field_simp
  have hv : fderiv ℝ t w v = v.re * d1 + v.im * d2 := by
    conv_lhs => rw [show v = v.re • (1 : ℂ) + v.im • I by apply Complex.ext <;> simp]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [← mul_assoc, hN, hv]
  have hS0 : 0 ≤ Sf := le_trans (by positivity) hsub
  have hnv : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hsq : (v.re * d1 + v.im * d2) ^ 2 ≤ (√Sf * ‖v‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hS0, hnv]
    nlinarith [sq_nonneg (v.re * d2 - v.im * d1), sq_nonneg v.re, sq_nonneg v.im]
  calc |v.re * d1 + v.im * d2| = √((v.re * d1 + v.im * d2) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ √((√Sf * ‖v‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = √Sf * ‖v‖ := Real.sqrt_sq (by positivity)

/-- JC7: closed `ρ`-balls of positive radius are neighbourhoods of their centres. -/
theorem s04_jc_ball_nhds {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {v : ℂ} (hv : v ∈ Ω) {r : ℝ}
    (hr : 0 < r) : rhoClosedBall Ω v r ∈ 𝓝 v := by
  obtain ⟨f, hf, hf0⟩ := s02_riemannMap_at hJ hv
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hψc : ContinuousOn (Function.invFunOn f unitDisc) Ω :=
    (s02_contDiffOn_invFun hf).1.continuousOn
  have hvi : v ∈ f '' unitDisc := by rw [hf.2.2]; exact hv
  have hψv : Function.invFunOn f unitDisc v = 0 :=
    hf.2.1 (Function.invFunOn_mem hvi) h0 ((Function.invFunOn_eq hvi).trans hf0.symm)
  have hc : 0 < √((Real.cosh r - 1) / (Real.cosh r + 1)) :=
    Real.sqrt_pos.mpr (div_pos (by linarith [Real.one_lt_cosh.mpr hr.ne']) (by positivity))
  have hpre := (hψc.continuousAt (hΩo.mem_nhds hv)).preimage_mem_nhds
    (isOpen_ball.mem_nhds (by rw [hψv]; exact mem_ball_self hc))
  filter_upwards [hΩo.mem_nhds hv, hpre] with u huΩ huc
  have hui : u ∈ f '' unitDisc := by rw [hf.2.2]; exact huΩ
  have hd : Function.invFunOn f unitDisc u ∈ {z | z ∈ unitDisc ∧ diskDist 0 z ≤ r} := by
    rw [s04_tb_disk_ball hr.le]
    exact ball_subset_closedBall huc
  refine ⟨huΩ, ?_⟩
  show poincareDist Ω v u ≤ r
  rw [← hf0, ← Function.invFunOn_eq hui, subsec_poincare_dist hf h0 (Function.invFunOn_mem hui)]
  exact hd.2

/-- JC8 (Fermi form): for `h(u) = E(u, t u)` with `t` differentiable at `w`,
`|dh(v)|² = I((cosh t - sinh t B) v, (cosh t - sinh t B) v) + dt(v)²` (`lem_shape_a`). -/
theorem s04_jc_fermi {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {w : ℂ} (hw : w ∈ Ω)
    (hs : schwarzNorm Ω w ≠ 1) {t : ℂ → ℝ} (ht : DifferentiableAt ℝ t w) (v : ℂ) :
    hypInner (normalGeod Ω w (t w)) (fderiv ℝ (fun u => normalGeod Ω u (t u)) w v)
        (fderiv ℝ (fun u => normalGeod Ω u (t u)) w v) =
      fffT Ω w ![(Real.cosh (t w) : ℂ) * v - (Real.sinh (t w) : ℂ) * shapeApply Ω w v,
          (Real.cosh (t w) : ℂ) * v - (Real.sinh (t w) : ℂ) * shapeApply Ω w v] +
        fderiv ℝ t w v ^ 2 := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hnmD : DifferentiableAt ℝ (normalMap Ω) (w, t w) :=
    ((s04_tb_nm_smooth hf).contDiffAt
      ((hΩo.prod isOpen_univ).mem_nhds ⟨hw, mem_univ _⟩)).differentiableAt (by simp)
  have hL := hnmD.hasFDerivAt
  set L := fderiv ℝ (normalMap Ω) (w, t w)
  -- `h = E ∘ (id, t)`, and the two partial derivatives of `E`
  have hh : HasFDerivAt (fun u => normalGeod Ω u (t u))
      (L.comp ((ContinuousLinearMap.id ℝ ℂ).prod (fderiv ℝ t w))) w := by
    have hg : HasFDerivAt (fun u : ℂ => (u, t u))
        ((ContinuousLinearMap.id ℝ ℂ).prod (fderiv ℝ t w)) w :=
      (hasFDerivAt_id w).prodMk ht.hasFDerivAt
    have := hL.comp w hg
    exact this
  have hx : HasFDerivAt (fun x => normalGeod Ω x (t w))
      (L.comp ((ContinuousLinearMap.id ℝ ℂ).prod 0)) w := by
    have hg : HasFDerivAt (fun u : ℂ => (u, t w)) ((ContinuousLinearMap.id ℝ ℂ).prod 0) w :=
      (hasFDerivAt_id w).prodMk (hasFDerivAt_const (t w) w)
    have := hL.comp w hg
    exact this
  have hτ : HasDerivAt (fun τ => normalGeod Ω w τ) (L ((0 : ℂ), (1 : ℝ))) (t w) :=
    hL.comp_hasDerivAt (t w) ((hasDerivAt_const (t w) w).prodMk (hasDerivAt_id (t w)))
  have hdec : fderiv ℝ (fun u => normalGeod Ω u (t u)) w v =
      fderiv ℝ (fun x => normalGeod Ω x (t w)) w v +
        fderiv ℝ t w v • deriv (fun τ => normalGeod Ω w τ) (t w) := by
    rw [hh.fderiv, hx.fderiv, hτ.deriv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, zero_apply]
    rw [← map_smul, ← map_add]
    congr 1
    ext <;> simp
  have hsym : ∀ (q a b : ℂ × ℝ) (c : ℝ), hypInner q a (c • b) = c * hypInner q b a := by
    intro q a b c
    unfold hypInner
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Complex.real_smul, map_mul,
      Complex.conj_ofReal, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im]
    ring
  obtain ⟨h1, h2, h3⟩ := lem_shape_a Ω Ωs hJ w hw hs (t w)
  rw [hdec, s02_hypInner_add, h3 v v, hsym, h2 v, hsym, hsym, h1]
  ring

/-- JC9 (chain rule): if `X* ∘ N = h` near `w`, then `dX*(dN v) = dh(v)`. -/
theorem s04_jc_chain {Ωs : Set ℂ} (hΩs : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ωs)
    {N : ℂ → ℂ} {h : ℂ → ℂ × ℝ} {w : ℂ} (hN : DifferentiableAt ℝ N w) (hNw : N w ∈ Ωs)
    (heq : ∀ᶠ u in 𝓝 w, epstein Ωs (N u) = h u) (v : ℂ) :
    fderiv ℝ (epstein Ωs) (N w) (fderiv ℝ N w v) = fderiv ℝ h w v := by
  have hX := s02_epstein_differentiableAt hΩs hNw
  have heq' : (fun u => epstein Ωs (N u)) =ᶠ[𝓝 w] h := heq
  have h1 : fderiv ℝ (fun u => epstein Ωs (N u)) w = fderiv ℝ h w := heq'.fderiv_eq
  rw [← h1, show (fun u => epstein Ωs (N u)) = epstein Ωs ∘ N from rfl, fderiv_comp w hX hN]
  rfl

/-- JC10: for `0 < t < e < 1/4` and `|b| ≤ e|v|`,
`(1 - e)|v| ≤ |cosh t · v - sinh t · b| ≤ (1 + 2e)|v|`. -/
theorem s04_jc_a_bounds {t e : ℝ} {v b : ℂ} (ht0 : 0 < t) (hte : t < e) (he : e < 1 / 4)
    (hb : ‖b‖ ≤ e * ‖v‖) :
    (1 - e) * ‖v‖ ≤ ‖(Real.cosh t : ℂ) * v - (Real.sinh t : ℂ) * b‖ ∧
      ‖(Real.cosh t : ℂ) * v - (Real.sinh t : ℂ) * b‖ ≤ (1 + 2 * e) * ‖v‖ := by
  have hc1 : 1 ≤ Real.cosh t := Real.one_le_cosh t
  have hs0 : 0 ≤ Real.sinh t := Real.sinh_nonneg_iff.mpr ht0.le
  have hn1 : ‖(Real.cosh t : ℂ) * v‖ = Real.cosh t * ‖v‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hn2 : ‖(Real.sinh t : ℂ) * b‖ = Real.sinh t * ‖b‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0]
  have hcs : Real.cosh t - Real.sinh t = Real.exp (-t) := Real.cosh_sub_sinh t
  have hcs' : Real.cosh t + Real.sinh t = Real.exp t := Real.cosh_add_sinh t
  have hem : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  have hep : Real.exp t * (1 - t) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hem (Real.exp_pos t).le
    rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
  have hsb : Real.sinh t * ‖b‖ ≤ Real.sinh t * (e * ‖v‖) := mul_le_mul_of_nonneg_left hb hs0
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
  have hse : Real.sinh t * e ≤ Real.sinh t := by nlinarith
  constructor
  · have h := norm_sub_norm_le ((Real.cosh t : ℂ) * v) ((Real.sinh t : ℂ) * b)
    rw [hn1, hn2] at h
    have hk : 1 - e ≤ Real.cosh t - Real.sinh t * e := by linarith
    have hk' := mul_le_mul_of_nonneg_right hk hv0
    nlinarith
  · have h := norm_sub_le ((Real.cosh t : ℂ) * v) ((Real.sinh t : ℂ) * b)
    rw [hn1, hn2] at h
    have hexp : Real.exp t ≤ 1 + 2 * e := by nlinarith [Real.exp_pos t]
    have hk : Real.cosh t + Real.sinh t * e ≤ 1 + 2 * e := by linarith
    have hk' := mul_le_mul_of_nonneg_right hk hv0
    nlinarith

/-- JC11 (scalar estimate): with `x = λ*|dN v|`, `y = λ|v|`, `α = λ|a|`, `G = I(a, a)`,
`d = dt(v)` and `F = |dX*(dN v)|² = G + d²`: `(1 - 10e) y ≤ x ≤ (1 + 10e) y`. -/
theorem s04_jc_scalar {e x y F G α d : ℝ} (he : 0 < e) (he' : e < 1 / 4) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hα1 : (1 - e) * y ≤ α) (hα2 : α ≤ (1 + 2 * e) * y) (hG : |G - α ^ 2| ≤ e * α ^ 2)
    (hd : |d| ≤ e * y) (hF : F = G + d ^ 2) (hF1 : (1 - e) ^ 2 * x ^ 2 ≤ F)
    (hF2 : F ≤ (1 + e) ^ 2 * x ^ 2) :
    (1 - 10 * e) * y ≤ x ∧ x ≤ (1 + 10 * e) * y := by
  have hG1 := (abs_le.mp hG).1
  have hG2 := (abs_le.mp hG).2
  have hα0 : 0 ≤ α := le_trans (mul_nonneg (by linarith) hy) hα1
  have hd2 : d ^ 2 ≤ (e * y) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg d) hd 2
  constructor
  · rcases le_or_gt (1 - 10 * e) 0 with h10 | h10
    · nlinarith
    · -- `(1-10e)²(1+e)² ≤ (1-e)³` on `0 < e < 1/10`
      have hp : (1 - 10 * e) ^ 2 * (1 + e) ^ 2 ≤ (1 - e) ^ 3 := by
        have hbr : 0 ≤ 15 - 58 * e - 181 * e ^ 2 - 100 * e ^ 3 := by nlinarith
        nlinarith
      have hαs : ((1 - e) * y) ^ 2 ≤ α ^ 2 := pow_le_pow_left₀ (by nlinarith) hα1 2
      have hF0 : (1 - e) ^ 3 * y ^ 2 ≤ F := by nlinarith [sq_nonneg d]
      have hk : ((1 - 10 * e) * y) ^ 2 * (1 + e) ^ 2 ≤ x ^ 2 * (1 + e) ^ 2 := by
        nlinarith [sq_nonneg y]
      have hk' : ((1 - 10 * e) * y) ^ 2 ≤ x ^ 2 := le_of_mul_le_mul_right hk (by positivity)
      exact (pow_le_pow_iff_left₀ (by positivity) hx two_ne_zero).mp hk'
  · -- `(1+e)(1+2e)² + e² ≤ (1-e)²(1+10e)²` on `0 < e < 1/4`
    have hq : (1 + e) * (1 + 2 * e) ^ 2 + e ^ 2 ≤ (1 - e) ^ 2 * (1 + 10 * e) ^ 2 := by
      have hbr : 0 ≤ 13 + 52 * e - 184 * e ^ 2 + 100 * e ^ 3 := by nlinarith
      nlinarith
    have hαs : α ^ 2 ≤ ((1 + 2 * e) * y) ^ 2 := pow_le_pow_left₀ hα0 hα2 2
    have hFu : F ≤ ((1 + e) * (1 + 2 * e) ^ 2 + e ^ 2) * y ^ 2 := by nlinarith
    have hk : x ^ 2 * (1 - e) ^ 2 ≤ ((1 + 10 * e) * y) ^ 2 * (1 - e) ^ 2 := by
      nlinarith [sq_nonneg y]
    have hk' : x ^ 2 ≤ ((1 + 10 * e) * y) ^ 2 :=
      le_of_mul_le_mul_right hk (by nlinarith)
    exact (pow_le_pow_iff_left₀ hx (by positivity) two_ne_zero).mp hk'

/-- JC12 (`2 × 2` determinant): if `a λ|v| ≤ λ*|Av| ≤ b λ|v|` for all `v` and `a ≥ 0`, then
`a² ≤ |det A| λ*²/λ² ≤ b²`. -/
theorem s04_jc_det2 (A : ℂ →L[ℝ] ℂ) {l ls a b : ℝ} (hl : 0 < l) (hls : 0 < ls) (ha : 0 ≤ a)
    (h1 : ∀ v : ℂ, a * (l * ‖v‖) ≤ ls * ‖A v‖) (h2 : ∀ v : ℂ, ls * ‖A v‖ ≤ b * (l * ‖v‖)) :
    a ^ 2 ≤ |LinearMap.det (A : ℂ →ₗ[ℝ] ℂ)| * ls ^ 2 / l ^ 2 ∧
      |LinearMap.det (A : ℂ →ₗ[ℝ] ℂ)| * ls ^ 2 / l ^ 2 ≤ b ^ 2 := by
  set p := A 1
  set q := A I
  have hdet : LinearMap.det (A : ℂ →ₗ[ℝ] ℂ) = p.re * q.im - q.re * p.im := by
    rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI,
      Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearMap.coe_coe]
    ring
  have hAv : ∀ x y : ℝ, A ⟨x, y⟩ = x • p + y • q := by
    intro x y
    conv_lhs => rw [show (⟨x, y⟩ : ℂ) = x • (1 : ℂ) + y • I by apply Complex.ext <;> simp]
    rw [map_add, map_smul, map_smul]
  set u := ls ^ 2 / l ^ 2 with hu
  have hu0 : 0 < u := by positivity
  set P := u * (p.re ^ 2 + p.im ^ 2)
  set R := u * (q.re ^ 2 + q.im ^ 2)
  set S := u * (p.re * q.re + p.im * q.im)
  -- the quadratic form `u |A(x + iy)|²` and its bounds
  have hQ : ∀ x y : ℝ, a ^ 2 * (x ^ 2 + y ^ 2) ≤ P * x ^ 2 + 2 * S * x * y + R * y ^ 2 ∧
      P * x ^ 2 + 2 * S * x * y + R * y ^ 2 ≤ b ^ 2 * (x ^ 2 + y ^ 2) := by
    intro x y
    have hn : ‖A ⟨x, y⟩‖ ^ 2 = (x * p.re + y * q.re) ^ 2 + (x * p.im + y * q.im) ^ 2 := by
      rw [hAv, Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hv : ‖(⟨x, y⟩ : ℂ)‖ ^ 2 = x ^ 2 + y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hform : P * x ^ 2 + 2 * S * x * y + R * y ^ 2 = u * ‖A ⟨x, y⟩‖ ^ 2 := by
      rw [hn]
      ring
    have e1 := h1 ⟨x, y⟩
    have e2 := h2 ⟨x, y⟩
    have hv0 : 0 ≤ l * ‖(⟨x, y⟩ : ℂ)‖ := by positivity
    have hA0 : 0 ≤ ls * ‖A ⟨x, y⟩‖ := by positivity
    have s1 : (a * (l * ‖(⟨x, y⟩ : ℂ)‖)) ^ 2 ≤ (ls * ‖A ⟨x, y⟩‖) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg ha hv0) e1 2
    have s2 : (ls * ‖A ⟨x, y⟩‖) ^ 2 ≤ (b * (l * ‖(⟨x, y⟩ : ℂ)‖)) ^ 2 :=
      pow_le_pow_left₀ hA0 e2 2
    have hul : u * l ^ 2 = ls ^ 2 := by rw [hu]; field_simp
    rw [hform]
    constructor
    · have : a ^ 2 * (x ^ 2 + y ^ 2) * l ^ 2 ≤ u * ‖A ⟨x, y⟩‖ ^ 2 * l ^ 2 := by
        rw [← hv]
        nlinarith
      exact le_of_mul_le_mul_right this (by positivity)
    · have : u * ‖A ⟨x, y⟩‖ ^ 2 * l ^ 2 ≤ b ^ 2 * (x ^ 2 + y ^ 2) * l ^ 2 := by
        rw [← hv]
        nlinarith
      exact le_of_mul_le_mul_right this (by positivity)
  have hD2 : (|LinearMap.det (A : ℂ →ₗ[ℝ] ℂ)| * u) ^ 2 = P * R - S ^ 2 := by
    rw [mul_pow, sq_abs, hdet]
    ring
  have hPa := (hQ 1 0).1
  have hRa := (hQ 0 1).1
  have hPb := (hQ 1 0).2
  have hRb := (hQ 0 1).2
  simp only [one_pow, zero_pow two_ne_zero, mul_zero, add_zero, zero_add, mul_one]
    at hPa hRa hPb hRb
  -- `S² ≤ (P - a²)(R - a²)`: the form `Q - a²|·|²` is positive semidefinite
  have hpsd : S ^ 2 ≤ (P - a ^ 2) * (R - a ^ 2) := by
    rcases eq_or_lt_of_le hPa with hP | hP
    · -- `P = a²`: then `2 S x + (R - a²) ≥ 0` for every `x`, so `S = 0`
      have hS : S = 0 := by
        by_contra hS
        set x := -(R - a ^ 2 + 1) / (2 * S) with hxdef
        have hx : 2 * S * x = -(R - a ^ 2 + 1) := by
          rw [hxdef]
          field_simp
        have h := (hQ x 1).1
        rw [← hP] at h
        simp only [one_pow, mul_one] at h
        nlinarith [h, hx]
      rw [hS, ← hP]
      simp
    · have h := (hQ (-S / (P - a ^ 2)) 1).1
      have hP' : 0 < P - a ^ 2 := by linarith
      have key : 0 ≤ (P - a ^ 2) * (-S / (P - a ^ 2)) ^ 2 + 2 * S * (-S / (P - a ^ 2)) +
          (R - a ^ 2) := by nlinarith
      have hval : (P - a ^ 2) * (-S / (P - a ^ 2)) ^ 2 + 2 * S * (-S / (P - a ^ 2)) +
          (R - a ^ 2) = ((P - a ^ 2) * (R - a ^ 2) - S ^ 2) / (P - a ^ 2) := by
        field_simp
        ring
      rw [hval] at key
      have := (div_nonneg_iff.mp key)
      rcases this with ⟨h1', -⟩ | ⟨-, h2'⟩
      · linarith
      · linarith
  have hlow : (a ^ 2) ^ 2 ≤ (|LinearMap.det (A : ℂ →ₗ[ℝ] ℂ)| * u) ^ 2 := by
    rw [hD2]
    nlinarith
  have hup : (|LinearMap.det (A : ℂ →ₗ[ℝ] ℂ)| * u) ^ 2 ≤ (b ^ 2) ^ 2 := by
    rw [hD2]
    have hP0 : 0 ≤ P := by positivity
    have hR0 : 0 ≤ R := by positivity
    nlinarith [sq_nonneg S, mul_le_mul hPb hRb hR0 (by positivity)]
  have h0 : 0 ≤ |LinearMap.det (A : ℂ →ₗ[ℝ] ℂ)| * u := by positivity
  rw [mul_div_assoc]
  exact ⟨(pow_le_pow_iff_left₀ (by positivity) h0 two_ne_zero).mp hlow,
    (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).mp hup⟩

/-- Uniform form of Lemma 4.6 (`lem_jacobian`) with `C = 10`: every `η ≤ η₀`, `R ≥ R₁`. -/
theorem s04_jc_unif : ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ R₁ : ℝ, ∀ η R : ℝ, 0 < η → η ≤ η₀ → R₁ ≤ R →
      ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ w ∈ goodSet Ω Ωs η R,
        (∀ v : ℂ, (1 - 10 * ε) * (poincareDensity Ω w * ‖v‖) ≤
            poincareDensity Ωs (slabMap Ω Ωs w) * ‖fderiv ℝ (slabMap Ω Ωs) w v‖ ∧
          poincareDensity Ωs (slabMap Ω Ωs w) * ‖fderiv ℝ (slabMap Ω Ωs) w v‖ ≤
            (1 + 10 * ε) * (poincareDensity Ω w * ‖v‖)) ∧
        (10 * ε ≤ 1 → (1 - 10 * ε) ^ 2 ≤ jacN Ω Ωs w) ∧ jacN Ω Ωs w ≤ (1 + 10 * ε) ^ 2 := by
  intro K hK ε hε hε'
  obtain ⟨η₀, hη₀, R₁, htube⟩ :=
    s04_sl_tube_unif K 1 1 6 ε 0 hK one_pos one_pos le_rfl hε hε' le_rfl
  refine ⟨η₀, hη₀, R₁, fun η R hη hηle hR Ω Ωs hp hnl w hw => ?_⟩
  have hJ := s03_b0_jordanPair hp
  have hΩ := s02_jordanPair_riemannMap hJ
  have hΩs := s02_jordanPair_riemannMap (s03_b0_jordanPair (s03_qce_swap hp))
  obtain ⟨⟨-, hCj⟩, ⟨hEe, -⟩, t, N, ⟨V₁, hV₁o, hBV₁, htV⟩, ⟨⟨V₂, hV₂o, hBV₂, hNV⟩, -⟩, hNm, htC,
    ht, hset, hiv, hv5, -⟩ := htube η R hη hηle hR Ω Ωs hp hnl w hw
  -- `t = slabTop`, `N = slabMap` on the neighbourhood `B̄_ρ(w, 1)` of `w`
  have hB := s04_jc_ball_nhds hJ hw.1 one_pos
  have hwB : w ∈ rhoClosedBall Ω w 1 := mem_of_mem_nhds hB
  have hid := s04_sl_slab_id hp (by linarith) hEe.2.1 hNm ht hset (fun u hu => (hiv u hu).1)
  have hSM : slabMap Ω Ωs =ᶠ[𝓝 w] N := by
    filter_upwards [hB] with u hu using (hid u hu).2
  have hdN : fderiv ℝ (slabMap Ω Ωs) w = fderiv ℝ N w := hSM.fderiv_eq
  have hNw : slabMap Ω Ωs w = N w := (hid w hwB).2
  have hNd : DifferentiableAt ℝ N w :=
    (hNV.contDiffAt (hV₂o.mem_nhds (hBV₂ hwB))).differentiableAt (by simp)
  have htd : DifferentiableAt ℝ t w :=
    (htV.contDiffAt (hV₁o.mem_nhds (hBV₁ hwB))).differentiableAt (by simp)
  have hNΩs : N w ∈ Ωs := hNm hwB
  obtain ⟨ht0, htε, hEN⟩ := ht w hwB
  have hch := s04_jc_chain hΩs hNd hNΩs (by filter_upwards [hB] with u hu using (ht u hu).2.2)
  -- the pointwise bounds at `w` (`lem_tube` (i), (iii), (v))
  have hs12 : schwarzNorm Ω w < 1 / 2 :=
    (hv5 w hwB).1 w ⟨hw.1, by rw [s04_tb_dist_self hΩ hw.1]; norm_num⟩
  have hss : schwarzNorm Ωs (N w) < ε :=
    (hv5 w hwB).2 (N w) ⟨hNΩs, by rw [s04_tb_dist_self hΩs hNΩs]; norm_num⟩
  have hss0 : 0 ≤ schwarzNorm Ωs (N w) := Real.sSup_nonneg (fun r hr => by
    obtain ⟨f, z, -, -, -, rfl⟩ := hr
    positivity)
  have hwB2 : w ∈ rhoBall Ω w (1 + 1) := ⟨hw.1, by rw [s04_tb_dist_self hΩ hw.1]; norm_num⟩
  have hnI : rhoTensorNorm Ω (fffT Ω - rhoMetricT Ω) w ≤ ε :=
    s04_jc_cj_point (i := 0) (Nat.zero_le _) hwB2 hε.le (le_trans le_self_add hCj)
  have hnB : rhoTensorNorm Ω (shapeT Ω) w ≤ ε :=
    s04_jc_cj_point (i := 0) (Nat.zero_le _) hwB2 hε.le (le_trans le_add_self hCj)
  have hnt : rhoTensorNorm Ω (rhoIterCovDeriv Ω 1 (scalarField t)) w ≤ ε :=
    s04_jc_cj_point (by norm_num) hwB hε.le htC
  have hl := s02_poincareDensity_pos hΩ hw.1
  have hls := s02_poincareDensity_pos hΩs hNΩs
  have hl2 : 0 < poincareDensity Ω w ^ 2 := by positivity
  -- the singular values of `dN`
  have hsv : ∀ v : ℂ, (1 - 10 * ε) * (poincareDensity Ω w * ‖v‖) ≤
      poincareDensity Ωs (N w) * ‖fderiv ℝ N w v‖ ∧
      poincareDensity Ωs (N w) * ‖fderiv ℝ N w v‖ ≤
        (1 + 10 * ε) * (poincareDensity Ω w * ‖v‖) := by
    intro v
    have hBv : ‖shapeApply Ω w v‖ ≤ ε * ‖v‖ := by
      have h1 := s04_jc_hs2 hl (s04_jc_shape_bil Ω w) v (shapeApply Ω w v)
      rw [s04_jc_shape_self] at h1
      have h3 : poincareDensity Ω w ^ 2 * ‖shapeApply Ω w v‖ ^ 2 ≤
          poincareDensity Ω w ^ 2 * (ε * (‖v‖ * ‖shapeApply Ω w v‖)) := by
        calc _ ≤ |poincareDensity Ω w ^ 2 * ‖shapeApply Ω w v‖ ^ 2| := le_abs_self _
          _ ≤ _ := h1
          _ ≤ ε * poincareDensity Ω w ^ 2 * (‖v‖ * ‖shapeApply Ω w v‖) := by gcongr
          _ = _ := by ring
      have h2 := le_of_mul_le_mul_left h3 hl2
      rcases (norm_nonneg (shapeApply Ω w v)).eq_or_lt with h0 | h0
      · rw [← h0]
        positivity
      · refine le_of_mul_le_mul_right ?_ h0
        have e1 : ‖shapeApply Ω w v‖ * ‖shapeApply Ω w v‖ = ‖shapeApply Ω w v‖ ^ 2 := by ring
        have e2 : ε * (‖v‖ * ‖shapeApply Ω w v‖) = ε * ‖v‖ * ‖shapeApply Ω w v‖ := by ring
        linarith
    obtain ⟨ha1, ha2⟩ := s04_jc_a_bounds ht0 htε hε' hBv
    set a := (Real.cosh (t w) : ℂ) * v - (Real.sinh (t w) : ℂ) * shapeApply Ω w v with ha
    have hG := s04_jc_hs2 hl (s04_jc_fff_bil Ω w) a a
    have hre : (conj a * a).re = ‖a‖ ^ 2 := by
      rw [Complex.conj_mul']
      norm_cast
    have hGe : (fffT Ω - rhoMetricT Ω) w ![a, a] =
        fffT Ω w ![a, a] - (poincareDensity Ω w * ‖a‖) ^ 2 := by
      simp only [Pi.sub_apply, rhoMetricT, Matrix.cons_val_zero, Matrix.cons_val_one,
        hre]
      ring
    rw [hGe] at hG
    have hd := s04_jc_dt (t := t) hl v
    have hF : hypInner (epstein Ωs (N w)) (fderiv ℝ (epstein Ωs) (N w) (fderiv ℝ N w v))
        (fderiv ℝ (epstein Ωs) (N w) (fderiv ℝ N w v)) = fffT Ω w ![a, a] + fderiv ℝ t w v ^ 2 := by
      rw [hch v, hEN]
      exact s04_jc_fermi hJ hw.1 (ne_of_lt (by linarith)) htd v
    have hFb := s02_fff_bounds hΩs hNΩs (fderiv ℝ N w v)
    have hx0 : 0 ≤ poincareDensity Ωs (N w) * ‖fderiv ℝ N w v‖ := by positivity
    have hy0 : 0 ≤ poincareDensity Ω w * ‖v‖ := by positivity
    have hm1 : (1 - ε) ^ 2 ≤ (1 - schwarzNorm Ωs (N w)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hm2 : (1 + schwarzNorm Ωs (N w)) ^ 2 ≤ (1 + ε) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hV2 : 0 ≤ poincareDensity Ωs (N w) ^ 2 * ‖fderiv ℝ N w v‖ ^ 2 := by positivity
    refine s04_jc_scalar (α := poincareDensity Ω w * ‖a‖) hε hε' hx0 hy0 ?_ ?_ ?_ ?_ hF ?_ ?_
    · have := mul_le_mul_of_nonneg_left ha1 hl.le
      linarith [show poincareDensity Ω w * ((1 - ε) * ‖v‖) = (1 - ε) * (poincareDensity Ω w * ‖v‖)
        by ring]
    · have := mul_le_mul_of_nonneg_left ha2 hl.le
      linarith [show poincareDensity Ω w * ((1 + 2 * ε) * ‖v‖) =
        (1 + 2 * ε) * (poincareDensity Ω w * ‖v‖) by ring]
    · refine hG.trans ?_
      calc rhoTensorNorm Ω (fffT Ω - rhoMetricT Ω) w * poincareDensity Ω w ^ 2 * (‖a‖ * ‖a‖)
          ≤ ε * poincareDensity Ω w ^ 2 * (‖a‖ * ‖a‖) := by gcongr
        _ = ε * (poincareDensity Ω w * ‖a‖) ^ 2 := by ring
    · exact hd.trans (mul_le_mul_of_nonneg_right hnt hy0)
    · calc (1 - ε) ^ 2 * (poincareDensity Ωs (N w) * ‖fderiv ℝ N w v‖) ^ 2
          = (1 - ε) ^ 2 * (poincareDensity Ωs (N w) ^ 2 * ‖fderiv ℝ N w v‖ ^ 2) := by ring
        _ ≤ (1 - schwarzNorm Ωs (N w)) ^ 2 *
            (poincareDensity Ωs (N w) ^ 2 * ‖fderiv ℝ N w v‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hm1 hV2
        _ = _ := by ring
        _ ≤ _ := hFb.1
    · calc _ ≤ (1 + schwarzNorm Ωs (N w)) ^ 2 * poincareDensity Ωs (N w) ^ 2 *
            ‖fderiv ℝ N w v‖ ^ 2 := hFb.2
        _ = (1 + schwarzNorm Ωs (N w)) ^ 2 *
            (poincareDensity Ωs (N w) ^ 2 * ‖fderiv ℝ N w v‖ ^ 2) := by ring
        _ ≤ (1 + ε) ^ 2 * (poincareDensity Ωs (N w) ^ 2 * ‖fderiv ℝ N w v‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hm2 hV2
        _ = _ := by ring
  unfold jacN
  rw [hdN, hNw]
  refine ⟨hsv, fun h10 => ?_, ?_⟩
  · exact (s04_jc_det2 (fderiv ℝ N w) hl hls (by linarith) (fun v => (hsv v).1)
      (fun v => (hsv v).2)).1
  · exact (s04_jc_det2 (fderiv ℝ N w) hl hls le_rfl (fun v => by rw [zero_mul]; positivity)
      (fun v => (hsv v).2)).2

/-- **Lemma 4.6** (Metric comparison, `lem:jacobian`, sec04-tube.tex:346).  There is an absolute
constant `C` such that on `G₀` the singular values of `dN` with respect to `ρ` and `ρ*` lie in
`[1 - Cε, 1 + Cε]`; in particular the area Jacobian satisfies `(1-Cε)² ≤ J_N ≤ (1+Cε)²` (4.8).

The lower bound for `J_N` is stated under `C ε ≤ 1`: without it `(1 - Cε)²` need not be a lower
bound for the product of two singular values that are only known to be `≥ 1 - Cε < 0`
(see `collaboration/FALSE_w2.md`). -/
theorem lem_jacobian : ∃ C : ℝ, ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ η : ℝ, 0 < η ∧ ∃ R : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ w ∈ goodSet Ω Ωs η R,
        (∀ v : ℂ, (1 - C * ε) * (poincareDensity Ω w * ‖v‖) ≤
            poincareDensity Ωs (slabMap Ω Ωs w) * ‖fderiv ℝ (slabMap Ω Ωs) w v‖ ∧
          poincareDensity Ωs (slabMap Ω Ωs w) * ‖fderiv ℝ (slabMap Ω Ωs) w v‖ ≤
            (1 + C * ε) * (poincareDensity Ω w * ‖v‖)) ∧
        (C * ε ≤ 1 → (1 - C * ε) ^ 2 ≤ jacN Ω Ωs w) ∧ jacN Ω Ωs w ≤ (1 + C * ε) ^ 2 := by
  refine ⟨10, fun K hK ε hε hε' => ?_⟩
  obtain ⟨η₀, hη₀, R₁, h⟩ := s04_jc_unif K hK ε hε hε'
  exact ⟨η₀, hη₀, R₁, h η₀ R₁ hη₀ le_rfl le_rfl⟩

/-! ## §4.4 The exact source term -/

/-! ## §4.4 The source term (interface SRC, w3)

`s04_src_*`: `hypArea` with an extra factor `s²` is `curvMass` (densities continuous on `Ω`); the
change of variables through `N` under `J_N ≥ c` (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`);
the scalar bound `σ ≤ 4/3 (s² + s*²)`; `s04_src_unif` is Lemma 4.7 in uniform form with `C = 10`. -/

/-- SRC1: `∫_S g s² dâ = ∫_S g dm_Ω` for `g ≥ 0` (`dm_Ω = s² dâ`). -/
theorem s04_src_dens {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {S : Set ℂ}
    (hS : MeasurableSet S) {g : ℂ → ℝ} (hg : ∀ z, 0 ≤ g z) :
    ∫⁻ z in S, ENNReal.ofReal (g z * schwarzNorm Ω z ^ 2) ∂hypArea Ω =
      ∫⁻ z in S, ENNReal.ofReal (g z) ∂curvMass Ω := by
  -- `hg` is not needed: both sides are `ofReal (λ² · g s²)` pointwise (true for any real `g`)
  have _hg := hg
  obtain ⟨f, hf⟩ := hΩ
  have hΩm : MeasurableSet Ω := (hf.isOpen isOpen_ball).measurableSet
  have hlC : ContinuousOn (poincareDensity Ω) Ω := (s02_contDiffOn_poincareDensity hf).continuousOn
  have hsC : ContinuousOn (schwarzNorm Ω) Ω :=
    ((s02_contDiffOn_invFun hf).2.2.2.continuousOn.norm.div
      ((s02_contDiffOn_poincareDensity hf).continuousOn.pow 2)
      (fun x hx => pow_ne_zero 2 (s02_poincareDensity_pos ⟨f, hf⟩ hx).ne')).congr
      (fun x hx => eq_def_s hf hx)
  have hm1 : AEMeasurable (fun w => ENNReal.ofReal (poincareDensity Ω w ^ 2))
      ((volume.restrict Ω).restrict S) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable ((hlC.pow 2).aemeasurable hΩm)).mono_measure
      Measure.restrict_le_self
  have hm2 : AEMeasurable (fun w => ENNReal.ofReal (schwarzNorm Ω w ^ 2 * poincareDensity Ω w ^ 2))
      ((volume.restrict Ω).restrict S) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (((hsC.pow 2).mul (hlC.pow 2)).aemeasurable hΩm)).mono_measure Measure.restrict_le_self
  unfold hypArea curvMass
  rw [restrict_withDensity hS, restrict_withDensity hS,
    lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hm1
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hm2
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine lintegral_congr fun z => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- SRC2 (change of variables): for `N` injective and differentiable on a Borel `D ⊆ Ω` with
`N(D) ⊆ Ω*` and `J_N = |det dN| λ*(N)²/λ² ≥ c > 0` on `D`,
`∫_D φ(N w) dâ(w) ≤ c⁻¹ ∫_{N(D)} φ dâ*` for `φ ≥ 0`. -/
theorem s04_src_cov {Ω Ωs : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    (hΩs : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ωs) {N : ℂ → ℂ} {D : Set ℂ}
    (hD : MeasurableSet D) (hDΩ : D ⊆ Ω) (hN : ∀ x ∈ D, HasFDerivWithinAt N (fderiv ℝ N x) D x)
    (hinj : InjOn N D) (hND : MapsTo N D Ωs) {c : ℝ} (hc : 0 < c)
    (hjac : ∀ w ∈ D, c ≤ |LinearMap.det ((fderiv ℝ N w : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)| *
      poincareDensity Ωs (N w) ^ 2 / poincareDensity Ω w ^ 2)
    {φ : ℂ → ℝ} (hφ : ∀ z, 0 ≤ φ z) :
    ∫⁻ w in D, ENNReal.ofReal (φ (N w)) ∂hypArea Ω ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ z in N '' D, ENNReal.ofReal (φ z) ∂hypArea Ωs := by
  obtain ⟨f, hf⟩ := hΩ
  obtain ⟨fs, hfs⟩ := hΩs
  have hΩm : MeasurableSet Ω := (hf.isOpen isOpen_ball).measurableSet
  have hΩsm : MeasurableSet Ωs := (hfs.isOpen isOpen_ball).measurableSet
  have hND' : MeasurableSet (N '' D) := measurable_image_of_fderivWithin hD hN hinj
  have hlC : ContinuousOn (poincareDensity Ω) Ω := (s02_contDiffOn_poincareDensity hf).continuousOn
  have hlsC : ContinuousOn (poincareDensity Ωs) Ωs :=
    (s02_contDiffOn_poincareDensity hfs).continuousOn
  have hm1 : AEMeasurable (fun w => ENNReal.ofReal (poincareDensity Ω w ^ 2))
      ((volume.restrict Ω).restrict D) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable ((hlC.pow 2).aemeasurable hΩm)).mono_measure
      Measure.restrict_le_self
  have hm2 : AEMeasurable (fun w => ENNReal.ofReal (poincareDensity Ωs w ^ 2))
      ((volume.restrict Ωs).restrict (N '' D)) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable ((hlsC.pow 2).aemeasurable hΩsm)).mono_measure
      Measure.restrict_le_self
  unfold hypArea
  rw [restrict_withDensity hD, restrict_withDensity hND',
    lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hm1
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hm2
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    Measure.restrict_restrict hD, Measure.restrict_restrict hND', inter_eq_left.2 hDΩ,
    inter_eq_left.2 hND.image_subset,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := volume) hD hN hinj]
  simp only [Pi.mul_apply]
  have hc' : ENNReal.ofReal c⁻¹ * ENNReal.ofReal c = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one]
  rw [← one_mul (∫⁻ a in D, _ ∂volume), ← hc', mul_assoc]
  gcongr ENNReal.ofReal c⁻¹ * ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hD fun w hw => ?_
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ (hDΩ hw)
  have hj : c * poincareDensity Ω w ^ 2 ≤
      |(fderiv ℝ N w).det| * poincareDensity Ωs (N w) ^ 2 := by
    have := hjac w hw
    rwa [le_div_iff₀ (by positivity)] at this
  rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul hc.le,
    ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (abs_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc c * (poincareDensity Ω w ^ 2 * φ (N w))
      = (c * poincareDensity Ω w ^ 2) * φ (N w) := by ring
    _ ≤ (|(fderiv ℝ N w).det| * poincareDensity Ωs (N w) ^ 2) * φ (N w) :=
        mul_le_mul_of_nonneg_right hj (hφ _)
    _ = _ := by ring

/-- SRC3: for `0 ≤ s, s' ≤ 1/2`, `s²/(1-s²) + s'²/(1-s'²) ≤ 4/3 (s² + s'²)`. -/
theorem s04_src_sigma {s s' : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) (h0' : 0 ≤ s') (h1' : s' ≤ 1 / 2) :
    s ^ 2 / (1 - s ^ 2) + s' ^ 2 / (1 - s' ^ 2) ≤ 4 / 3 * (s ^ 2 + s' ^ 2) := by
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 2 → x ^ 2 / (1 - x ^ 2) ≤ 4 / 3 * x ^ 2 := by
    intro x hx0 hx1
    have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg x]
  linarith [key s h0 h1, key s' h0' h1']

/-- Uniform form of Lemma 4.7 (`lem_source`) with `C = 10`: every `η ≤ η₀`, `R ≥ R₁`. -/
theorem s04_src_unif : ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 → 10 * ε < 1 →
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ R₁ : ℝ, ∀ η R : ℝ, 0 < η → η ≤ η₀ → R₁ ≤ R →
      ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab → ∀ D : Set ℂ, D ⊆ goodSet Ω Ωs η R → MeasurableSet D →
        ∀ p ∈ Ω,
          (∫⁻ w in D, ENNReal.ofReal
              (intrKernel Ω p w * schwarzNorm Ωs (slabMap Ω Ωs w) ^ 2) ∂hypArea Ω) ≤
            ENNReal.ofReal (((1 - 10 * ε) ^ 2)⁻¹) *
              ∫⁻ z in slabMap Ω Ωs '' D, ENNReal.ofReal
                (intrKernel Ω p (lab (epstein Ωs z)) * schwarzNorm Ωs z ^ 2) ∂hypArea Ωs ∧
          ENNReal.ofReal (((1 - 10 * ε) ^ 2)⁻¹) *
              (∫⁻ z in slabMap Ω Ωs '' D, ENNReal.ofReal
                (intrKernel Ω p (lab (epstein Ωs z)) * schwarzNorm Ωs z ^ 2) ∂hypArea Ωs) ≤
            ENNReal.ofReal (((1 - 10 * ε) ^ 2)⁻¹) * Kst Ω Ωs lab p ∧
          (∫⁻ w in D, ENNReal.ofReal (intrKernel Ω p w * sigmaSrc Ω Ωs w) ∂hypArea Ω) ≤
            ENNReal.ofReal (4 / 3 * ((1 - 10 * ε) ^ 2)⁻¹) * KH2 Ω Ωs lab p := by
  intro K hK ε hε hε' hε10
  obtain ⟨η₁, hη₁, R₂, hNu⟩ := s04_sl_eq_def_N_unif K hK ε hε hε'
  obtain ⟨M, hRN⟩ := s04_sl_prop_RN_unif K hK
  obtain ⟨η₂, hη₂, R₃, hRNu⟩ := hRN ε hε hε'
  obtain ⟨η₃, hη₃, R₄, hJCu⟩ := s04_jc_unif K hK ε hε hε'
  refine ⟨min (min η₁ η₂) (min η₃ (1 / 2)), lt_min (lt_min hη₁ hη₂) (lt_min hη₃ (by norm_num)),
    max (max R₂ R₃) (max R₄ 1), fun η R hη hηle hR Ω Ωs hp hnl lab hlab D hD hDm p hpΩ => ?_⟩
  have hη1 : η ≤ η₁ := hηle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hη2 : η ≤ η₂ := hηle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hη3 : η ≤ η₃ := hηle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη4 : η ≤ 1 / 2 := hηle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hR2 : R₂ ≤ R := ((le_max_left _ _).trans (le_max_left _ _)).trans hR
  have hR3 : R₃ ≤ R := ((le_max_right _ _).trans (le_max_left _ _)).trans hR
  have hR4 : R₄ ≤ R := ((le_max_left _ _).trans (le_max_right _ _)).trans hR
  have hR1 : 1 ≤ R := ((le_max_right _ _).trans (le_max_right _ _)).trans hR
  have hJ := s03_b0_jordanPair hp
  have hΩ := s02_jordanPair_riemannMap hJ
  have hΩs := s02_jordanPair_riemannMap (s03_b0_jordanPair (s03_qce_swap hp))
  obtain ⟨hGo, -, hNC, hNg⟩ := hNu η R hη hη1 hR2 Ω Ωs hp hnl
  obtain ⟨hlabN, hinj, -⟩ := hRNu η R hη hη2 hR3 Ω Ωs hp hnl lab hlab
  have hc0 : 0 < 1 - 10 * ε := by linarith
  have hc : 0 < (1 - 10 * ε) ^ 2 := by positivity
  have hDΩ : D ⊆ Ω := fun w hw => (hD hw).1
  have hNd : ∀ x ∈ D, HasFDerivWithinAt (slabMap Ω Ωs) (fderiv ℝ (slabMap Ω Ωs) x) D x :=
    fun x hx => ((hNC.contDiffAt (hGo.mem_nhds (hD hx))).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hinjD : InjOn (slabMap Ω Ωs) D := hinj.mono hD
  have hND : MapsTo (slabMap Ω Ωs) D Ωs := fun w hw => (hNg w (hD hw)).1
  have hjac : ∀ w ∈ D, (1 - 10 * ε) ^ 2 ≤
      |LinearMap.det ((fderiv ℝ (slabMap Ω Ωs) w : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)| *
        poincareDensity Ωs (slabMap Ω Ωs w) ^ 2 / poincareDensity Ω w ^ 2 :=
    fun w hw => (hJCu η R hη hη3 hR4 Ω Ωs hp hnl w (hD hw)).2.1 hε10.le
  have hφ : ∀ z, 0 ≤ intrKernel Ω p (lab (epstein Ωs z)) * schwarzNorm Ωs z ^ 2 :=
    fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- (1): `k_p(w) = k_p(R(N w))` on `D`, then the change of variables through `N`
  have h1 : (∫⁻ w in D, ENNReal.ofReal
        (intrKernel Ω p w * schwarzNorm Ωs (slabMap Ω Ωs w) ^ 2) ∂hypArea Ω) ≤
      ENNReal.ofReal (((1 - 10 * ε) ^ 2)⁻¹) *
        ∫⁻ z in slabMap Ω Ωs '' D, ENNReal.ofReal
          (intrKernel Ω p (lab (epstein Ωs z)) * schwarzNorm Ωs z ^ 2) ∂hypArea Ωs := by
    refine le_trans (le_of_eq (setLIntegral_congr_fun hDm ?_))
      (s04_src_cov hΩ hΩs hDm hDΩ hNd hinjD hND hc hjac
        (φ := fun z => intrKernel Ω p (lab (epstein Ωs z)) * schwarzNorm Ωs z ^ 2) hφ)
    intro w hw
    simp only [hlabN w (hD hw)]
  -- (2): `dâ* s*² = dm_{Ω*}` on `N(D)`
  have h2 : ENNReal.ofReal (((1 - 10 * ε) ^ 2)⁻¹) *
        (∫⁻ z in slabMap Ω Ωs '' D, ENNReal.ofReal
          (intrKernel Ω p (lab (epstein Ωs z)) * schwarzNorm Ωs z ^ 2) ∂hypArea Ωs) ≤
      ENNReal.ofReal (((1 - 10 * ε) ^ 2)⁻¹) * Kst Ω Ωs lab p := by
    gcongr ENNReal.ofReal (((1 - 10 * ε) ^ 2)⁻¹) * ?_
    rw [s04_src_dens hΩs (measurable_image_of_fderivWithin hDm hNd hinjD)
      (g := fun z => intrKernel Ω p (lab (epstein Ωs z))) (fun z => sq_nonneg _)]
    exact setLIntegral_le_lintegral _ _
  refine ⟨h1, h2, ?_⟩
  -- (3): `σ ≤ 4/3 (s² + s*(N)²)` on `D` (`s, s*(N) < η ≤ 1/2`)
  obtain ⟨f, hf⟩ := hΩ
  have hΩm : MeasurableSet Ω := (hf.isOpen isOpen_ball).measurableSet
  have hsC : ContinuousOn (schwarzNorm Ω) Ω :=
    ((s02_contDiffOn_invFun hf).2.2.2.continuousOn.norm.div
      ((s02_contDiffOn_poincareDensity hf).continuousOn.pow 2)
      (fun x hx => pow_ne_zero 2 (s02_poincareDensity_pos ⟨f, hf⟩ hx).ne')).congr
      (fun x hx => eq_def_s hf hx)
  have hmS : AEMeasurable (fun w => ENNReal.ofReal (intrKernel Ω p w * schwarzNorm Ω w ^ 2))
      ((hypArea Ω).restrict D) :=
    ((ENNReal.measurable_ofReal.comp_aemeasurable
      ((s03_sc_meas ⟨f, hf⟩ hpΩ).aemeasurable.mul ((hsC.pow 2).aemeasurable hΩm))).mono_ac
      (withDensity_absolutelyContinuous _ _)).mono_measure Measure.restrict_le_self
  have hs0 : ∀ (U : Set ℂ) (z : ℂ), 0 ≤ schwarzNorm U z := fun U z => Real.sSup_nonneg (fun r hr => by
    obtain ⟨f, z, -, -, -, rfl⟩ := hr
    positivity)
  have hpt : ∀ w ∈ D, ENNReal.ofReal (intrKernel Ω p w * sigmaSrc Ω Ωs w) ≤
      ENNReal.ofReal (4 / 3) * (ENNReal.ofReal (intrKernel Ω p w * schwarzNorm Ω w ^ 2) +
        ENNReal.ofReal (intrKernel Ω p w * schwarzNorm Ωs (slabMap Ω Ωs w) ^ 2)) := by
    intro w hw
    have hg := s04_tb_good_s hp (hD hw)
    have hnb := lem_normal_b ⟨f, hf⟩ (hDΩ hw)
    obtain ⟨hNΩs, ht0, htε, hE⟩ := hNg w (hD hw)
    have hsw : schwarzNorm Ω w < η := hg.1 w (hDΩ hw) (by
      rw [← hnb.2.2, hnb.2.1, sub_self, abs_zero]
      linarith)
    have hsN : schwarzNorm Ωs (slabMap Ω Ωs w) < η := hg.2 _ hNΩs (by
      rw [hE, ← hnb.2.2, hnb.2.1, zero_sub, abs_neg, abs_of_pos ht0]
      linarith)
    have hσ : sigmaSrc Ω Ωs w ≤
        4 / 3 * (schwarzNorm Ω w ^ 2 + schwarzNorm Ωs (slabMap Ω Ωs w) ^ 2) :=
      s04_src_sigma (hs0 _ _) (by linarith) (hs0 _ _) (by linarith)
    have hk : 0 ≤ intrKernel Ω p w := sq_nonneg _
    rw [← ENNReal.ofReal_add (mul_nonneg hk (sq_nonneg _)) (mul_nonneg hk (sq_nonneg _)),
      ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc intrKernel Ω p w * sigmaSrc Ω Ωs w
        ≤ intrKernel Ω p w *
          (4 / 3 * (schwarzNorm Ω w ^ 2 + schwarzNorm Ωs (slabMap Ω Ωs w) ^ 2)) :=
          mul_le_mul_of_nonneg_left hσ hk
      _ = _ := by ring
  have hci : (1 : ℝ) ≤ ((1 - 10 * ε) ^ 2)⁻¹ := by
    have hc1 : (1 - 10 * ε) ^ 2 ≤ 1 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hc1 (inv_pos.2 hc).le
    rw [inv_mul_cancel₀ hc.ne'] at hm
    linarith
  have hA : (∫⁻ w in D, ENNReal.ofReal (intrKernel Ω p w * schwarzNorm Ω w ^ 2) ∂hypArea Ω) ≤
      ENNReal.ofReal (((1 - 10 * ε) ^ 2)⁻¹) * KH Ω p := by
    rw [s04_src_dens ⟨f, hf⟩ hDm (g := intrKernel Ω p) (fun z => sq_nonneg _)]
    calc (∫⁻ w in D, ENNReal.ofReal (intrKernel Ω p w) ∂curvMass Ω) ≤ KH Ω p :=
          setLIntegral_le_lintegral _ _
      _ = 1 * KH Ω p := (one_mul _).symm
      _ ≤ _ := by gcongr; exact ENNReal.one_le_ofReal.2 hci
  calc (∫⁻ w in D, ENNReal.ofReal (intrKernel Ω p w * sigmaSrc Ω Ωs w) ∂hypArea Ω)
      ≤ ∫⁻ w in D, ENNReal.ofReal (4 / 3) *
          (ENNReal.ofReal (intrKernel Ω p w * schwarzNorm Ω w ^ 2) +
            ENNReal.ofReal (intrKernel Ω p w * schwarzNorm Ωs (slabMap Ω Ωs w) ^ 2)) ∂hypArea Ω :=
        setLIntegral_mono' hDm hpt
    _ = ENNReal.ofReal (4 / 3) *
          ((∫⁻ w in D, ENNReal.ofReal (intrKernel Ω p w * schwarzNorm Ω w ^ 2) ∂hypArea Ω) +
            ∫⁻ w in D, ENNReal.ofReal
              (intrKernel Ω p w * schwarzNorm Ωs (slabMap Ω Ωs w) ^ 2) ∂hypArea Ω) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hmS]
    _ ≤ ENNReal.ofReal (4 / 3) * (ENNReal.ofReal (((1 - 10 * ε) ^ 2)⁻¹) * KH2 Ω Ωs lab p) := by
        gcongr ENNReal.ofReal (4 / 3) * ?_
        rw [KH2, mul_add]
        exact add_le_add hA (h1.trans h2)
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]

/-- **Lemma 4.7** (Change of variables for the source, `lem:source`, sec04-tube.tex:390).  Let
`D ⊆ G₀` be Borel and `p ∈ Ω`.  Then (4.9)
`∫_D k_p(w) s*(N w)² dâ ≤ (1-Cε)⁻² ∫_{N(D)} k_p(R z*) s*(z*)² dâ* ≤ (1-Cε)⁻² K_*(p)`,
and consequently (4.10) `∫_D k_p σ dâ ≤ C K_{H,2}(p)`; the proof gives the constant
`(4/3)(1-Cε)⁻²`, which is the one stated.  Here `C` is the constant of Lemma 4.6; the statement is
made for `C ε < 1`, where `(1 - Cε)⁻²` is the bound coming from `J_N ≥ (1-Cε)²`. -/
theorem lem_source : ∃ C : ℝ, ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 → C * ε < 1 →
    ∃ η : ℝ, 0 < η ∧ ∃ R : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab → ∀ D : Set ℂ, D ⊆ goodSet Ω Ωs η R → MeasurableSet D →
        ∀ p ∈ Ω,
          (∫⁻ w in D, ENNReal.ofReal
              (intrKernel Ω p w * schwarzNorm Ωs (slabMap Ω Ωs w) ^ 2) ∂hypArea Ω) ≤
            ENNReal.ofReal (((1 - C * ε) ^ 2)⁻¹) *
              ∫⁻ z in slabMap Ω Ωs '' D, ENNReal.ofReal
                (intrKernel Ω p (lab (epstein Ωs z)) * schwarzNorm Ωs z ^ 2) ∂hypArea Ωs ∧
          ENNReal.ofReal (((1 - C * ε) ^ 2)⁻¹) *
              (∫⁻ z in slabMap Ω Ωs '' D, ENNReal.ofReal
                (intrKernel Ω p (lab (epstein Ωs z)) * schwarzNorm Ωs z ^ 2) ∂hypArea Ωs) ≤
            ENNReal.ofReal (((1 - C * ε) ^ 2)⁻¹) * Kst Ω Ωs lab p ∧
          (∫⁻ w in D, ENNReal.ofReal (intrKernel Ω p w * sigmaSrc Ω Ωs w) ∂hypArea Ω) ≤
            ENNReal.ofReal (4 / 3 * ((1 - C * ε) ^ 2)⁻¹) * KH2 Ω Ωs lab p := by
  refine ⟨10, fun K hK ε hε hε' hC => ?_⟩
  obtain ⟨η₀, hη₀, R₁, h⟩ := s04_src_unif K hK ε hε hε' hC
  exact ⟨η₀, hη₀, R₁, h η₀ R₁ hη₀ le_rfl le_rfl⟩

end EpsteinVMO
