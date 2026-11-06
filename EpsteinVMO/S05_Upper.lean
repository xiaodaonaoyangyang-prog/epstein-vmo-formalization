import EpsteinVMO.S04_Tube
import EpsteinVMO.PDE_Dirichlet
import EpsteinVMO.S03_Coarse
import TauCeti.Analysis.Calculus.ParametricIntegral

/-!
# §5 The upper bound (`sec05-upper.tex`)

Statements of §5: Theorem 5.1 (`thm:upper`), Lemma 5.2 (`lem:shape`), the adjoint (5.4)
(`eq:adjoint`) and Green's formula (5.6) (`eq:green-formula`), Lemma 5.3 (`lem:test-functions`),
Lemma 5.4 (`lem:comparison`), Proposition 5.5 (`prop:dirichlet`), Lemma 5.6 (`lem:reproduction`),
Lemma 5.7 (`lem:graph-operator`), the good domain (5.16) (`eq:def-D`), Lemma 5.8
(`lem:good-domain`), Lemma 5.9 (`lem:s-lipschitz`), Lemma 5.10 (`lem:counting`), the slab identity
of §5.6, Lemma 5.11 (`lem:bad-region`), the barrier (5.19)–(5.21) and the bound (5.22)
(`eq:t-bound`).  Equation numbers follow the order of the displays in the section.

## Section-local definitions (also used by §9, §10, §12)

* **Second-order operators (5.2).** An operator `𝓛u = c u - a^{ij} ∇_i∇_j u - b^i ∇_i u` on
  `D ⊆ Ω` is given by its coefficients in the coordinate `w`: `aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ`
  (the contravariant `a^{ij}` in the frame `(1, i)`), `bUp : ℂ → Fin 2 → ℝ` (the vector `b^i`)
  and `c : ℂ → ℝ`; `∇` is the Levi-Civita connection of `ρ` (`rhoHess`).  `ellOp` is `𝓛`,
  `ellOpAdj` its formal adjoint w.r.t. `dâ` (5.4), with coefficients `adjCoeffB` (`b*`) and
  `adjCoeffC` (`c*`).  `lowerA`, `lowerB` lower the indices with `ρ`, so that
  `‖a - ρ⁻¹‖_{C²} = rhoCjNorm Ω 2 (lowerA Ω aUp - rhoMetricT Ω)` etc.
  `IsSmoothOp` (smooth, symmetric coefficients) and `IsAdmissibleOp Ω D ε' aUp bUp c`
  (`ε'`-admissible on `D`, (5.3)).
* **Dirichlet inverse (Prop. 5.5).** `IsSmoothRelCompactIn D' D` (smooth relatively compact open
  subset: a regular sublevel set), `IsSmoothExhaustion D Dn`, `IsDirichletSol` (the Dirichlet
  problem on `D'`), `IsDirichletInverse … D F G` (`G = 𝒢_D F`: a `C²` solution which is the
  increasing limit of the Dirichlet solutions on every smooth exhaustion) and
  `dirichletInv … D F` (a choice of it, `0` if none).
* **The graph operator (§5.4).** `graphMetric Ω w τ` is `g_τ` (the matrix of `E(·,τ)^* g_{ℍ³}`),
  `meanCurvUp Ω u w` is `H_up(u)(w)` (5.11), `graphQ` is `𝒬(u) = 2(H - H_up(u))`,
  `graphQDeriv Ω v u` is `D𝒬(v)[u]`, and `graphOp Ω Ωs u = ∫₀¹ D𝒬(θt)[u] dθ` is `𝓛` (with
  `t = slabTop`).  `RepresentsOp Ω D L aUp bUp c` says that a (possibly nonlinear-looking)
  operator `L` acts on smooth functions on `D` as `ellOp` with these smooth symmetric coefficients;
  `graphCoeffs Ω Ωs D` chooses such coefficients for `graphOp` (they are unique on an open `D`) and
  `graphOpAdj Ω Ωs D` is the adjoint `𝓛*` of `𝓛` on `D`.  `fffLaplacian` is `Δ_I`.
* **The bad set (§5.5).** `hsetDist x S ∈ ℝ≥0∞` (`d(x, ∅) = ∞`), `curvASet` (`A`), `badSet`
  (`𝔅 = (Σ ∪ Σ*) ∩ {d(·, A) ≤ R}`), `IsBadNet … S ℓ` (`S = {Bᵢ}` a maximal `1`-separated subset of
  `𝔅` with reference labels `ℓ(Bᵢ) = ℓᵢ`), `goodDomainD` (`D`, (5.16)), `goodSetG1` (`G₁`),
  `slabRegion` (`𝒮_D`), `barrierFn` (`b`, (5.19)).
-/

open Complex Set Metric Filter Topology MeasureTheory Matrix intervalIntegral
open scoped ENNReal NNReal Real ComplexConjugate ContDiff

noncomputable section

namespace EpsteinVMO

open LiZhongQC

/-! ## Operators on `(Ω, ρ)` -/

/-- The covariant Hessian `∇²u` of a function for `ρ`. -/
def rhoHess (Ω : Set ℂ) (u : ℂ → ℝ) : TensorField (0 + 2) :=
  rhoIterCovDeriv Ω 2 (scalarField u)

/-- The Laplace–Beltrami operator `Δ_ρ u = tr_ρ ∇²u`. -/
def rhoLaplacian (Ω : Set ℂ) (u : ℂ → ℝ) (w : ℂ) : ℝ :=
  (∑ i : Fin 2, rhoHess Ω u w ![frameVec i, frameVec i]) / poincareDensity Ω w ^ 2

/-- The `(0,2)`-tensor `a♭` obtained from the contravariant `a^{ij}` by lowering both indices
with `ρ`. -/
def lowerA (Ω : Set ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) : TensorField 2 := fun w v =>
  poincareDensity Ω w ^ 4 * (cvec (v 0) ⬝ᵥ (aUp w *ᵥ cvec (v 1)))

/-- The `1`-form `b♭` obtained from the vector field `b^i` by lowering the index with `ρ`. -/
def lowerB (Ω : Set ℂ) (bUp : ℂ → Fin 2 → ℝ) : TensorField 1 := fun w v =>
  poincareDensity Ω w ^ 2 * (bUp w ⬝ᵥ cvec (v 0))

/-- The operator `𝓛u = c u - a^{ij} ∇_i∇_j u - b^i ∇_i u` (5.2). -/
def ellOp (Ω : Set ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ)
    (u : ℂ → ℝ) (w : ℂ) : ℝ :=
  c w * u w - ∑ i : Fin 2, ∑ j : Fin 2, aUp w i j * rhoHess Ω u w ![frameVec i, frameVec j] -
    ∑ i : Fin 2, bUp w i * fderiv ℝ u w (frameVec i)

/-- The double divergence `∇_j ∇_i a^{ij}`. -/
def rhoDDiv (Ω : Set ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (w : ℂ) : ℝ :=
  (∑ i : Fin 2, ∑ j : Fin 2,
    rhoIterCovDeriv Ω 2 (lowerA Ω aUp) w ![frameVec j, frameVec i, frameVec i, frameVec j]) /
    poincareDensity Ω w ^ 4

/-- The divergence `∇_i b^i` of a vector field. -/
def rhoDivB (Ω : Set ℂ) (bUp : ℂ → Fin 2 → ℝ) (w : ℂ) : ℝ :=
  (∑ i : Fin 2, rhoCovDeriv Ω (lowerB Ω bUp) w ![frameVec i, frameVec i]) /
    poincareDensity Ω w ^ 2

/-- The vector field `∇_j a^{ij}` (components in the frame `(1, i)`). -/
def rhoDivA (Ω : Set ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (w : ℂ) : Fin 2 → ℝ := fun i =>
  (∑ j : Fin 2, rhoCovDeriv Ω (lowerA Ω aUp) w ![frameVec j, frameVec i, frameVec j]) /
    poincareDensity Ω w ^ 4

/-- `c* = c - ∇_j∇_i a^{ij} + ∇_i b^i`. -/
def adjCoeffC (Ω : Set ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ)
    (c : ℂ → ℝ) (w : ℂ) : ℝ :=
  c w - rhoDDiv Ω aUp w + rhoDivB Ω bUp w

/-- `b*^i = 2 ∇_j a^{ij} - b^i`. -/
def adjCoeffB (Ω : Set ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ)
    (w : ℂ) : Fin 2 → ℝ :=
  2 • rhoDivA Ω aUp w - bUp w

/-- The formal adjoint `𝓛*v = c* v - a^{ij} ∇_i∇_j v - b*^i ∇_i v` w.r.t. `dâ` (5.4). -/
def ellOpAdj (Ω : Set ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ)
    (c : ℂ → ℝ) (u : ℂ → ℝ) (w : ℂ) : ℝ :=
  ellOp Ω aUp (adjCoeffB Ω aUp bUp) (adjCoeffC Ω aUp bUp c) u w

/-- The coefficients are smooth on `D` and `a^{ij} = a^{ji}`. -/
def IsSmoothOp (D : Set ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ)
    (c : ℂ → ℝ) : Prop :=
  (∀ i j, ContDiffOn ℝ ∞ (fun w => aUp w i j) D) ∧ (∀ i, ContDiffOn ℝ ∞ (fun w => bUp w i) D) ∧
    ContDiffOn ℝ ∞ c D ∧ ∀ w ∈ D, (aUp w)ᵀ = aUp w

/-- `𝓛` is `ε'`-admissible on the open set `D ⊆ Ω` (5.3):
`‖a - ρ⁻¹‖_{C²(D)} + ‖b‖_{C¹(D)} + ‖c - 2‖_{C⁰(D)} ≤ ε'`, `ε' ∈ (0, 1/8]`. -/
def IsAdmissibleOp (Ω D : Set ℂ) (ε' : ℝ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ) : Prop :=
  0 < ε' ∧ ε' ≤ 1 / 8 ∧ IsOpen D ∧ D ⊆ Ω ∧ IsSmoothOp D aUp bUp c ∧
    rhoCjNorm Ω 2 (lowerA Ω aUp - rhoMetricT Ω) D + rhoCjNorm Ω 1 (lowerB Ω bUp) D +
        rhoCjNorm Ω 0 (scalarField fun w => c w - 2) D ≤ ENNReal.ofReal ε'

/-! ## Dirichlet problems and the Dirichlet inverse -/

/-- `D'` is a smooth relatively compact open subset of `D`: a regular sublevel set
`{ψ < 0}` of a smooth function, with compact closure contained in `D`. -/
def IsSmoothRelCompactIn (D' D : Set ℂ) : Prop :=
  IsOpen D' ∧ IsCompact (closure D') ∧ closure D' ⊆ D ∧
    ∃ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ ∧ D' = {w | ψ w < 0} ∧ ∀ w, ψ w = 0 → fderiv ℝ ψ w ≠ 0

/-- An exhaustion `D₁ ⋐ D₂ ⋐ ⋯` of `D` by smooth relatively compact open sets. -/
def IsSmoothExhaustion (D : Set ℂ) (Dn : ℕ → Set ℂ) : Prop :=
  (∀ n, IsSmoothRelCompactIn (Dn n) D) ∧ (∀ n, closure (Dn n) ⊆ Dn (n + 1)) ∧ ⋃ n, Dn n = D

/-- `u` solves the Dirichlet problem `𝓛u = F` in `D'`, `u = 0` on `∂D'`, `u ∈ C^∞(\overline{D'})`. -/
def IsDirichletSol (Ω : Set ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ)
    (c : ℂ → ℝ) (D' : Set ℂ) (F u : ℂ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ u (closure D') ∧ (∀ w ∈ D', ellOp Ω aUp bUp c u w = F w) ∧
    ∀ w ∈ frontier D', u w = 0

/-- `G = 𝒢_D F` (Proposition 5.5 (a)): `G ∈ C²(D)`, `𝓛G = F` on `D`, and on every smooth
exhaustion of `D` the Dirichlet solutions (extended by `0`) increase to `G`. -/
def IsDirichletInverse (Ω : Set ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ)
    (c : ℂ → ℝ) (D : Set ℂ) (F G : ℂ → ℝ) : Prop :=
  ContDiffOn ℝ 2 G D ∧ (∀ w ∈ D, ellOp Ω aUp bUp c G w = F w) ∧
    ∀ Dn : ℕ → Set ℂ, IsSmoothExhaustion D Dn →
      ∀ un : ℕ → ℂ → ℝ, (∀ n, IsDirichletSol Ω aUp bUp c (Dn n) F (un n)) →
        ∀ w ∈ D, Monotone (fun n => (Dn n).indicator (un n) w) ∧
          Tendsto (fun n => (Dn n).indicator (un n) w) atTop (𝓝 (G w))

open Classical in
/-- A choice of `𝒢_D F` (`0` if there is none). -/
def dirichletInv (Ω : Set ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ)
    (c : ℂ → ℝ) (D : Set ℂ) (F : ℂ → ℝ) : ℂ → ℝ :=
  if h : ∃ G, IsDirichletInverse Ω aUp bUp c D F G then h.choose else 0

/-! ## The exact graph operator -/

/-- The metric `g_τ` of the equidistant surface, i.e. the matrix of `E(·, τ)^* g_{ℍ³}` at `w` in
the frame `(1, i)`. -/
def graphMetric (Ω : Set ℂ) (w : ℂ) (τ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j =>
    hypInner (normalGeod Ω w τ) (fderiv ℝ (fun x => normalGeod Ω x τ) w (frameVec i))
      (fderiv ℝ (fun x => normalGeod Ω x τ) w (frameVec j))

/-- The coordinate gradient `(u₁, u₂)` of `u`. -/
def gradCoords (u : ℂ → ℝ) (w : ℂ) : Fin 2 → ℝ := fun j => fderiv ℝ u w (frameVec j)

/-- `W = √(1 + g_τ^{ij} u_i u_j)`. -/
def graphW (Ω : Set ℂ) (u : ℂ → ℝ) (w : ℂ) (τ : ℝ) : ℝ :=
  Real.sqrt (1 + gradCoords u w ⬝ᵥ ((graphMetric Ω w τ)⁻¹ *ᵥ gradCoords u w))

/-- `√(det g_τ)`. -/
def graphSdet (Ω : Set ℂ) (w : ℂ) (τ : ℝ) : ℝ := Real.sqrt (graphMetric Ω w τ).det

/-- The flux `√(det g_τ) g_τ^{ij} u_j / W` at fixed `τ`. -/
def graphFlux (Ω : Set ℂ) (u : ℂ → ℝ) (τ : ℝ) (w : ℂ) : Fin 2 → ℝ := fun i =>
  graphSdet Ω w τ * ((graphMetric Ω w τ)⁻¹ *ᵥ gradCoords u w) i / graphW Ω u w τ

/-- `H_up(u)(w)`, the mean curvature of the graph `{τ = u(w)}` in `(G₀ × (-2, T+2), ḡ)` w.r.t.
the upward unit normal (5.11): `2H_up(u) = -[ (1/√det g_τ) ∂_τ(√det g_τ / W)
- (1/√det g_τ) ∂_i(√det g_τ g_τ^{ij} u_j / W) ]_{τ = u(w)}`, `∂_i` at fixed `τ`. -/
def meanCurvUp (Ω : Set ℂ) (u : ℂ → ℝ) (w : ℂ) : ℝ :=
  -(1 / 2) * (deriv (fun τ => graphSdet Ω w τ / graphW Ω u w τ) (u w) / graphSdet Ω w (u w) -
    (∑ i : Fin 2, fderiv ℝ (fun x => graphFlux Ω u (u w) x i) w (frameVec i)) /
      graphSdet Ω w (u w))

/-- `𝒬(u) = 2(H - H_up(u))`, with `H = s²/(1-s²)` the mean curvature of `Σ` w.r.t. `ν`. -/
def graphQ (Ω : Set ℂ) (u : ℂ → ℝ) (w : ℂ) : ℝ :=
  2 * (schwarzNorm Ω w ^ 2 / (1 - schwarzNorm Ω w ^ 2) - meanCurvUp Ω u w)

/-- The Gateaux derivative `D𝒬(v)[u] = d/dθ|₀ 𝒬(v + θu)`. -/
def graphQDeriv (Ω : Set ℂ) (v u : ℂ → ℝ) (w : ℂ) : ℝ :=
  deriv (fun θ : ℝ => graphQ Ω (v + θ • u) w) 0

/-- The graph operator `𝓛u = ∫₀¹ D𝒬(θt)[u] dθ`, `t = slabTop` (Lemma 5.7 (b)). -/
def graphOp (Ω Ωs : Set ℂ) (u : ℂ → ℝ) (w : ℂ) : ℝ :=
  ∫ θ in (0 : ℝ)..1, graphQDeriv Ω (θ • slabTop Ω Ωs) u w

/-- `L` acts on smooth functions on `D` as the operator `ellOp` with smooth symmetric coefficients
`aUp, bUp, c`. -/
def RepresentsOp (Ω D : Set ℂ) (L : (ℂ → ℝ) → ℂ → ℝ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ) : Prop :=
  IsSmoothOp D aUp bUp c ∧
    ∀ u : ℂ → ℝ, ContDiffOn ℝ ∞ u D → ∀ w ∈ D, L u w = ellOp Ω aUp bUp c u w

open Classical in
/-- A choice of coefficients `(a, b, c)` of the graph operator on `D` (`0` if there are none). -/
def graphCoeffs (Ω Ωs D : Set ℂ) :
    (ℂ → Matrix (Fin 2) (Fin 2) ℝ) × (ℂ → Fin 2 → ℝ) × (ℂ → ℝ) :=
  if h : ∃ abc : (ℂ → Matrix (Fin 2) (Fin 2) ℝ) × (ℂ → Fin 2 → ℝ) × (ℂ → ℝ),
      RepresentsOp Ω D (graphOp Ω Ωs) abc.1 abc.2.1 abc.2.2 then h.choose else (0, 0, 0)

/-- The formal adjoint `𝓛*` of the graph operator on `D`. -/
def graphOpAdj (Ω Ωs D : Set ℂ) (u : ℂ → ℝ) (w : ℂ) : ℝ :=
  ellOpAdj Ω (graphCoeffs Ω Ωs D).1 (graphCoeffs Ω Ωs D).2.1 (graphCoeffs Ω Ωs D).2.2 u w

/-- The Laplace–Beltrami operator `Δ_I u = (1/√det I) ∂_i(√det I I^{ij} ∂_j u)` of `I`. -/
def fffLaplacian (Ω : Set ℂ) (u : ℂ → ℝ) (w : ℂ) : ℝ :=
  (∑ i : Fin 2, fderiv ℝ (fun x => Real.sqrt (fffMat Ω x).det *
      ((fffMat Ω x)⁻¹ *ᵥ gradCoords u x) i) w (frameVec i)) / Real.sqrt (fffMat Ω w).det

/-! ## The bad set and the good domain -/

/-- `d(x, S)` in `ℍ³`, with `d(x, ∅) = ∞`. -/
def hsetDist (x : ℂ × ℝ) (S : Set (ℂ × ℝ)) : ℝ≥0∞ := ⨅ y ∈ S, ENNReal.ofReal (hdist x y)

/-- `A = {X(w) : s(w) ≥ η} ∪ {X*(z*) : s*(z*) ≥ η}`. -/
def curvASet (Ω Ωs : Set ℂ) (η : ℝ) : Set (ℂ × ℝ) :=
  {x | ∃ w ∈ Ω, η ≤ schwarzNorm Ω w ∧ x = epstein Ω w} ∪
    {x | ∃ z ∈ Ωs, η ≤ schwarzNorm Ωs z ∧ x = epstein Ωs z}

/-- `𝔅 = (Σ ∪ Σ*) ∩ {x : d(x, A) ≤ R}`. -/
def badSet (Ω Ωs : Set ℂ) (η R : ℝ) : Set (ℂ × ℝ) :=
  (epstein Ω '' Ω ∪ epstein Ωs '' Ωs) ∩ {x | hsetDist x (curvASet Ω Ωs η) ≤ ENNReal.ofReal R}

/-- `S = {Bᵢ}` is a maximal `1`-separated subset of `𝔅`, and `ℓ(Bᵢ) = ℓᵢ ∈ Ω` is a label of `Bᵢ`:
a preimage under `X` if `Bᵢ ∈ Σ`, and `R(z*) = lab(Bᵢ)` for a preimage `z*` under `X*` if
`Bᵢ ∈ Σ*`. -/
def IsBadNet (Ω Ωs : Set ℂ) (lab : ℂ × ℝ → ℂ) (η R : ℝ) (S : Set (ℂ × ℝ)) (ℓ : ℂ × ℝ → ℂ) :
    Prop :=
  S ⊆ badSet Ω Ωs η R ∧ (∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → 1 ≤ hdist b b') ∧
    (∀ x ∈ badSet Ω Ωs η R, ∃ b ∈ S, hdist x b < 1) ∧
    ∀ b ∈ S, (ℓ b ∈ Ω ∧ epstein Ω (ℓ b) = b) ∨ ((∃ z ∈ Ωs, epstein Ωs z = b) ∧ ℓ b = lab b)

/-- The good domain `D = {w ∈ Ω : d(X(w), 𝔅) > 2 and d_ρ(w, ℓᵢ) > 2 for all i}` (5.16). -/
def goodDomainD (Ω Ωs : Set ℂ) (η R : ℝ) (S : Set (ℂ × ℝ)) (ℓ : ℂ × ℝ → ℂ) : Set ℂ :=
  {w | w ∈ Ω ∧ ENNReal.ofReal 2 < hsetDist (epstein Ω w) (badSet Ω Ωs η R) ∧
    ∀ b ∈ S, 2 < poincareDist Ω w (ℓ b)}

/-- `G₁ = {w ∈ Ω : d(X(w), 𝔅) > 1}` (5.16). -/
def goodSetG1 (Ω Ωs : Set ℂ) (η R : ℝ) : Set ℂ :=
  {w | w ∈ Ω ∧ ENNReal.ofReal 1 < hsetDist (epstein Ω w) (badSet Ω Ωs η R)}

/-- The slab region `𝒮_D = {E(w, τ) : w ∈ D, 0 < τ < t(w)}`. -/
def slabRegion (Ω Ωs D : Set ℂ) : Set (ℂ × ℝ) :=
  {q | ∃ w ∈ D, ∃ τ : ℝ, 0 < τ ∧ τ < slabTop Ω Ωs w ∧ q = normalGeod Ω w τ}

/-- The barrier `b(w) = C_b ∑ᵢ e^{-β d_ρ(w, ℓᵢ)}`, `β = 3/2` (5.19). -/
def barrierFn (Ω : Set ℂ) (S : Set (ℂ × ℝ)) (ℓ : ℂ × ℝ → ℂ) (Cb : ℝ) (w : ℂ) : ℝ :=
  Cb * ∑' b : S, Real.exp (-(3 / 2) * poincareDist Ω w (ℓ b))

/-! ## §5.1 Equidistant surfaces -/

/-- **Lemma 5.2 (b)** (`lem:shape`, sec05-upper.tex:51).  For `w ∈ Ω` with `s(w) ≠ 1`, the shape
operator `B` has eigenvalues `s/(1-s)` and `-s/(1+s)`; in particular
`H = ½ tr B = -det B = s²/(1-s²)` (5.4) (`eq:mean-curvature`). -/
theorem lem_shape_b : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ w ∈ Ω, schwarzNorm Ω w ≠ 1 →
    (shapeMat Ω w).charpoly =
        (Polynomial.X - Polynomial.C (schwarzNorm Ω w / (1 - schwarzNorm Ω w))) *
          (Polynomial.X - Polynomial.C (-(schwarzNorm Ω w / (1 + schwarzNorm Ω w)))) ∧
      meanCurv Ω w = schwarzNorm Ω w ^ 2 / (1 - schwarzNorm Ω w ^ 2) ∧
      -(shapeMat Ω w).det = schwarzNorm Ω w ^ 2 / (1 - schwarzNorm Ω w ^ 2) := by
  intro Ω Ωs hJ w hw hs1
  have hΩ := s02_jordanPair_riemannMap hJ
  have hl := s02_poincareDensity_pos hΩ hw
  have hs0 : 0 ≤ schwarzNorm Ω w := by
    obtain ⟨f, hf, hf0⟩ := s02_riemannMap_at hJ hw
    rw [← hf0, eq_s_disk hf (mem_ball_self one_pos)]
    positivity
  have hpc := prop_curvature hΩ hw hs1
  -- `II` of `S04` is the `fII` of `prop_curvature` (`Re(a b̄) = Re(ā b)`)
  have hII : ∀ u v, secondFF Ω w u v =
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
    intro u v
    unfold secondFF hypChristoffel normalVec
    congr 2
    ext <;> simp [Complex.mul_re] <;> ring
  set s := schwarzNorm Ω w with hsdef
  set M := fffMat Ω w with hM
  set T := secondFFMat Ω w with hT
  have hkey : ∀ κ : ℝ, (T 0 0 - κ * M 0 0) * (T 1 1 - κ * M 1 1) -
      (T 0 1 - κ * M 0 1) * (T 1 0 - κ * M 1 0) =
        M.det * ((κ + s / (1 + s)) * (κ - s / (1 - s))) := by
    intro κ
    rw [Matrix.det_fin_two]
    simp only [hM, hT, fffMat, secondFFMat, Matrix.of_apply, frameVec, Matrix.cons_val_zero,
      Matrix.cons_val_one, hII]
    exact hpc κ
  have hsym : M 1 0 = M 0 1 := by
    simp only [hM, fffMat, Matrix.of_apply, frameVec, fffT, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    unfold hypInner
    congr 1
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hD : M.det = ((1 - s ^ 2) * poincareDensity Ω w ^ 2) ^ 2 := by
    rw [Matrix.det_fin_two, hsym, ← lem_fff_area hΩ hw]
    simp only [hM, fffMat, Matrix.of_apply, frameVec, fffT, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  have hs2 : 1 - s ^ 2 ≠ 0 := by
    intro h
    have : (1 - s) * (1 + s) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact hs1 (by linarith)
    · linarith
  have hD0 : M.det ≠ 0 := by rw [hD]; positivity
  have h1s : 1 - s ≠ 0 := fun h => hs1 (by linarith)
  have h1s' : 1 + s ≠ 0 := by positivity
  have hdetT : T.det = -(M.det * (s / (1 + s) * (s / (1 - s)))) := by
    have h0 := hkey 0
    rw [Matrix.det_fin_two]
    linear_combination h0
  have htrT : T 0 0 * M 1 1 + M 0 0 * T 1 1 - T 0 1 * M 1 0 - M 0 1 * T 1 0 =
      M.det * (s / (1 - s) - s / (1 + s)) := by
    linear_combination (-1 / 2) * hkey 1 + (1 / 2) * hkey (-1)
  have htr : (shapeMat Ω w).trace = s / (1 - s) + -(s / (1 + s)) := by
    rw [shapeMat, ← hM, ← hT, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two,
      Matrix.trace_fin_two]
    simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul]
    rw [hsym] at htrT ⊢
    have e : (M.det)⁻¹ * M.det = 1 := inv_mul_cancel₀ hD0
    linear_combination (M.det)⁻¹ * htrT + (s / (1 - s) - s / (1 + s)) * e
  have hdet : (shapeMat Ω w).det = s / (1 - s) * -(s / (1 + s)) := by
    rw [shapeMat, ← hM, ← hT, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
      Matrix.det_transpose, hdetT]
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.charpoly_fin_two, htr, hdet]
    simp only [map_add, map_neg, map_mul]
    ring
  · rw [meanCurv, htr]
    field_simp
    ring
  · rw [hdet]
    field_simp
    ring

/-! ## §5.2 Elliptic tools -/

/-- Helper (P2): the domain `Ω` of a Jordan pair is open. -/
theorem s05_jordan_isOpen {Ω Ωs : Set ℂ} (h : IsJordanPair Ω Ωs) : IsOpen Ω := by
  obtain ⟨F, hF, -⟩ := h
  rw [← hF]
  exact F.isOpenMap _ isOpen_upperHalf

/-- Helper (P2): the domain `Ω` of a Jordan pair has a Riemann map onto `𝔻`. -/
theorem s05_jordan_riemann {Ω Ωs : Set ℂ} (h : IsJordanPair Ω Ωs) :
    ∃ φ : ℂ → ℂ, IsConformalOnto φ Ω unitDisc := by
  have hO := s05_jordan_isOpen h
  obtain ⟨F, hF, -⟩ := h
  have hne : upperHalf.Nonempty := ⟨I, by simp [upperHalf]⟩
  apply lehto_exists_conformal
  refine ⟨hO, ?_, ?_, ?_⟩
  · rw [← hF]
    exact (convex_upperHalf.isConnected hne).image F F.continuous.continuousOn
  · rw [← hF]
    have : ContractibleSpace upperHalf := convex_upperHalf.contractibleSpace hne
    exact ContinuousMap.HomotopyEquiv.simplyConnectedSpace (F.image upperHalf).symm.toHomotopyEquiv
  · intro hu
    have hm : F (-I) ∈ Ω := hu ▸ mem_univ _
    rw [← hF] at hm
    obtain ⟨x, hx, hFx⟩ := hm
    have := F.injective hFx
    subst this
    norm_num [upperHalf] at hx

/-- Helper (P2): `λ_Ω = 2/((1-|φ|²)|f'(φ)|)` on `Ω` for a Riemann map `φ : Ω → 𝔻`, `f = φ⁻¹`. -/
theorem s05_density_eq {Ω : Set ℂ} {φ : ℂ → ℂ} (hΩ : IsOpen Ω)
    (hφ : IsConformalOnto φ Ω unitDisc) {w : ℂ} (hw : w ∈ Ω) :
    poincareDensity Ω w =
      2 / ((1 - ‖φ w‖ ^ 2) * ‖deriv (Function.invFunOn φ Ω) (φ w)‖) := by
  have hf := hφ.symm hΩ
  have hz : φ w ∈ unitDisc := hφ.2.2 ▸ mem_image_of_mem φ hw
  have h1 := eq_lambda_f hf hz
  rw [hφ.2.1.leftInvOn_invFunOn hw] at h1
  have hne : ‖deriv (Function.invFunOn φ Ω) (φ w)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz)
  have hr : (0 : ℝ) < 1 - ‖φ w‖ ^ 2 := by
    have := mem_ball_zero_iff.mp hz
    nlinarith [norm_nonneg (φ w)]
  rw [eq_div_iff (mul_ne_zero hr.ne' hne)]
  calc poincareDensity Ω w * ((1 - ‖φ w‖ ^ 2) * ‖deriv (Function.invFunOn φ Ω) (φ w)‖)
      = (poincareDensity Ω w * ‖deriv (Function.invFunOn φ Ω) (φ w)‖) * (1 - ‖φ w‖ ^ 2) := by
        ring
    _ = 2 := by rw [h1]; field_simp

/-- Helper (P2): on the domain of a Jordan pair, `λ_Ω` is smooth and positive. -/
theorem s05_density_smooth {Ω Ωs : Set ℂ} (h : IsJordanPair Ω Ωs) :
    IsOpen Ω ∧ ContDiffOn ℝ ∞ (poincareDensity Ω) Ω ∧ ∀ w ∈ Ω, 0 < poincareDensity Ω w := by
  have hΩ := s05_jordan_isOpen h
  obtain ⟨φ, hφ⟩ := s05_jordan_riemann h
  have hf := hφ.symm hΩ
  refine ⟨hΩ, ?_, fun w hw => s02_poincareDensity_pos ⟨_, hf⟩ hw⟩
  have hmaps : MapsTo φ Ω unitDisc := fun w hw => hφ.2.2 ▸ mem_image_of_mem φ hw
  have hφs : ContDiffOn ℝ ∞ φ Ω := (hφ.1.contDiffOn hΩ).restrict_scalars ℝ
  have hf's : ContDiffOn ℝ ∞ (deriv (Function.invFunOn φ Ω)) unitDisc :=
    ((hf.1.deriv isOpen_ball).contDiffOn isOpen_ball).restrict_scalars ℝ
  have hcomp := hf's.comp hφs hmaps
  have hd0 : ∀ w ∈ Ω, deriv (Function.invFunOn φ Ω) (φ w) ≠ 0 := fun w hw =>
    deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 (hmaps hw)
  refine ContDiffOn.congr ?_ fun w hw => s05_density_eq hΩ hφ hw
  refine contDiffOn_const.div ((contDiffOn_const.sub (hφs.norm_sq ℝ)).mul (hcomp.norm ℝ hd0)) ?_
  intro w hw
  have := mem_ball_zero_iff.mp (hmaps hw)
  have hr : (0 : ℝ) < 1 - ‖φ w‖ ^ 2 := by nlinarith [norm_nonneg (φ w)]
  exact mul_ne_zero hr.ne' (norm_ne_zero_iff.mpr (hd0 w hw))

/-- Helper (P2): `cvec` is smooth. -/
theorem s05_cvec_contDiff : ContDiff ℝ ∞ cvec := by
  have h0 : ContDiff ℝ ∞ fun x : ℂ => cvec x 0 := by
    rw [show (fun x : ℂ => cvec x 0) = ⇑reCLM from funext fun x => by simp [cvec]]
    exact reCLM.contDiff
  have h1 : ContDiff ℝ ∞ fun x : ℂ => cvec x 1 := by
    rw [show (fun x : ℂ => cvec x 1) = ⇑imCLM from funext fun x => by simp [cvec]]
    exact imCLM.contDiff
  exact contDiff_pi.2 (Fin.forall_fin_two.2 ⟨h0, h1⟩)

/-- Helper (P2): `∇φ = ∇ log λ` is smooth where `λ` is smooth and positive. -/
theorem s05_logDensityGrad_smooth {Ω U : Set ℂ} (hU : IsOpen U)
    (hl : ContDiffOn ℝ ∞ (poincareDensity Ω) U) (hpos : ∀ w ∈ U, 0 < poincareDensity Ω w) :
    ContDiffOn ℝ ∞ (logDensityGrad Ω) U := by
  have hL : ContDiffOn ℝ ∞ (fun x => Real.log (poincareDensity Ω x)) U :=
    hl.log fun x hx => (hpos x hx).ne'
  have hd := hL.fderiv_of_isOpen hU (m := ∞) (le_of_eq ENat.coe_top_add_one)
  have h1 := hd.clm_apply (contDiffOn_const (c := (1 : ℂ)))
  have h2 := hd.clm_apply (contDiffOn_const (c := I))
  exact (ofRealCLM.contDiff.comp_contDiffOn h1).add
    ((ofRealCLM.contDiff.comp_contDiffOn h2).mul contDiffOn_const)

/-- Helper (P2): `Γ_{g}(X, Y)` is smooth in all its arguments where `λ` is smooth and positive. -/
theorem s05_christoffel_smooth {Ω U : Set ℂ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set E} {g X Y : E → ℂ} (hG : ContDiffOn ℝ ∞ (logDensityGrad Ω) U)
    (hg : ContDiffOn ℝ ∞ g s) (hgU : MapsTo g s U) (hX : ContDiffOn ℝ ∞ X s)
    (hY : ContDiffOn ℝ ∞ Y s) :
    ContDiffOn ℝ ∞ (fun p => rhoChristoffel Ω (g p) (X p) (Y p)) s := by
  have hG' := hG.comp hg hgU
  have hc : ∀ {Z W : E → ℂ}, ContDiffOn ℝ ∞ Z s → ContDiffOn ℝ ∞ W s →
      ContDiffOn ℝ ∞ (fun p => (((conj (Z p) * W p).re : ℝ) : ℂ)) s := fun hZ hW =>
    ofRealCLM.contDiff.comp_contDiffOn (reCLM.contDiff.comp_contDiffOn
      ((conjCLE.contDiff.comp_contDiffOn hZ).mul hW))
  unfold rhoChristoffel
  exact (((hc hG' hX).mul hY).add ((hc hG' hY).mul hX)).sub ((hc hX hY).mul hG')

/-- Helper (P2): the covariant derivative of a jointly smooth tensor field is jointly smooth. -/
theorem s05_covDeriv_smooth {Ω U : Set ℂ} (hU : IsOpen U)
    (hl : ContDiffOn ℝ ∞ (poincareDensity Ω) U) (hpos : ∀ w ∈ U, 0 < poincareDensity Ω w)
    {k : ℕ} {T : TensorField k}
    (hT : ContDiffOn ℝ ∞ (fun p : ℂ × (Fin k → ℂ) => T p.1 p.2) (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p : ℂ × (Fin (k + 1) → ℂ) => rhoCovDeriv Ω T p.1 p.2) (U ×ˢ univ) := by
  have hO : IsOpen (U ×ˢ (univ : Set (Fin k → ℂ))) := hU.prod isOpen_univ
  have hG := s05_logDensityGrad_smooth hU hl hpos
  have hfst : ContDiffOn ℝ ∞ (fun p : ℂ × (Fin (k + 1) → ℂ) => p.1) (U ×ˢ univ) :=
    contDiffOn_fst
  have hmaps1 : MapsTo (fun p : ℂ × (Fin (k + 1) → ℂ) => p.1) (U ×ˢ univ) U := fun p hp => hp.1
  have hcoord : ∀ j : Fin (k + 1),
      ContDiffOn ℝ ∞ (fun p : ℂ × (Fin (k + 1) → ℂ) => p.2 j) (U ×ˢ univ) :=
    fun j => ((contDiff_apply ℝ (fun _ => ℂ) j).comp contDiff_snd).contDiffOn
  have htail : ContDiffOn ℝ ∞ (fun p : ℂ × (Fin (k + 1) → ℂ) => Fin.tail p.2) (U ×ˢ univ) :=
    contDiffOn_pi.2 fun i => hcoord i.succ
  have hF1 : ContDiffOn ℝ ∞ (fun p : ℂ × (Fin (k + 1) → ℂ) =>
      fderiv ℝ (fun p' : ℂ × (Fin k → ℂ) => T p'.1 p'.2) (p.1, Fin.tail p.2) (p.2 0, 0))
      (U ×ˢ univ) :=
    ((hT.fderiv_of_isOpen hO (m := ∞) (le_of_eq ENat.coe_top_add_one)).comp
      (hfst.prodMk htail) (fun p hp => ⟨hp.1, mem_univ _⟩)).clm_apply
      ((hcoord 0).prodMk contDiffOn_const)
  have hsum : ContDiffOn ℝ ∞ (fun p : ℂ × (Fin (k + 1) → ℂ) => ∑ i : Fin k,
      T p.1 (Function.update (Fin.tail p.2) i
        (rhoChristoffel Ω p.1 (p.2 0) (Fin.tail p.2 i)))) (U ×ˢ univ) := by
    refine ContDiffOn.sum fun i _ => ?_
    have hΓ := s05_christoffel_smooth hG hfst hmaps1 (hcoord 0) (hcoord i.succ)
    have hupd : ContDiffOn ℝ ∞ (fun p : ℂ × (Fin (k + 1) → ℂ) => Function.update (Fin.tail p.2) i
        (rhoChristoffel Ω p.1 (p.2 0) (Fin.tail p.2 i))) (U ×ˢ univ) := by
      refine contDiffOn_pi.2 fun j => ?_
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self]
        exact hΓ
      · simp only [Function.update_of_ne hj]
        exact hcoord j.succ
    exact hT.comp (hfst.prodMk hupd) (fun p hp => ⟨hp.1, mem_univ _⟩)
  refine (hF1.sub hsum).congr fun p hp => ?_
  have hd : DifferentiableAt ℝ (fun p' : ℂ × (Fin k → ℂ) => T p'.1 p'.2) (p.1, Fin.tail p.2) :=
    (hT.contDiffAt (hO.mem_nhds ⟨hp.1, mem_univ _⟩)).differentiableAt (by simp)
  have hpart : fderiv ℝ (fun x => T x (Fin.tail p.2)) p.1 (p.2 0) =
      fderiv ℝ (fun p' : ℂ × (Fin k → ℂ) => T p'.1 p'.2) (p.1, Fin.tail p.2) (p.2 0, 0) := by
    have := (hd.hasFDerivAt.comp p.1
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 (Fin.tail p.2))).fderiv
    rw [show (fun x => T x (Fin.tail p.2)) = (fun p' : ℂ × (Fin k → ℂ) => T p'.1 p'.2) ∘
      (fun e : ℂ => (e, Fin.tail p.2)) from rfl, this]
    rfl
  show fderiv ℝ (fun x => T x (Fin.tail p.2)) p.1 (p.2 0) - _ = _
  rw [hpart]

/-- Helper (P2): `∇T` at `w` only depends on `T` near `w`. -/
theorem s05_covDeriv_congr {Ω : Set ℂ} {k : ℕ} {T T' : TensorField k} {w : ℂ}
    (h : ∀ᶠ x in 𝓝 w, T x = T' x) : rhoCovDeriv Ω T w = rhoCovDeriv Ω T' w := by
  funext v
  have h1 : (fun x => T x (Fin.tail v)) =ᶠ[𝓝 w] fun x => T' x (Fin.tail v) :=
    h.mono fun x hx => congrFun hx _
  simp only [rhoCovDeriv, h1.fderiv_eq, h.self_of_nhds]

/-- Helper (P2): `∇(T - T') = ∇T - ∇T'`. -/
theorem s05_covDeriv_sub {Ω : Set ℂ} {k : ℕ} {T T' : TensorField k} {w : ℂ}
    (hT : ∀ u, DifferentiableAt ℝ (fun x => T x u) w)
    (hT' : ∀ u, DifferentiableAt ℝ (fun x => T' x u) w) (v : Fin (k + 1) → ℂ) :
    rhoCovDeriv Ω (T - T') w v = rhoCovDeriv Ω T w v - rhoCovDeriv Ω T' w v := by
  simp only [rhoCovDeriv, Pi.sub_apply]
  rw [fderiv_fun_sub (hT _) (hT' _)]
  simp only [sub_apply, Finset.sum_sub_distrib]
  ring

/-- Helper (P2): `∇(T + T') = ∇T + ∇T'`. -/
theorem s05_covDeriv_add {Ω : Set ℂ} {k : ℕ} {T T' : TensorField k} {w : ℂ}
    (hT : ∀ u, DifferentiableAt ℝ (fun x => T x u) w)
    (hT' : ∀ u, DifferentiableAt ℝ (fun x => T' x u) w) (v : Fin (k + 1) → ℂ) :
    rhoCovDeriv Ω (fun x u => T x u + T' x u) w v = rhoCovDeriv Ω T w v + rhoCovDeriv Ω T' w v := by
  simp only [rhoCovDeriv]
  rw [fderiv_fun_add (hT _) (hT' _)]
  simp only [add_apply, Finset.sum_add_distrib]
  ring

/-- Helper (P2): Leibniz rule `∇(s T) = ds ⊗ T + s ∇T`. -/
theorem s05_covDeriv_smul {Ω : Set ℂ} {k : ℕ} {s : ℂ → ℝ} {T : TensorField k} {w : ℂ}
    (hs : DifferentiableAt ℝ s w) (hT : ∀ u, DifferentiableAt ℝ (fun x => T x u) w)
    (v : Fin (k + 1) → ℂ) :
    rhoCovDeriv Ω (fun x u => s x * T x u) w v =
      fderiv ℝ s w (v 0) * T w (Fin.tail v) + s w * rhoCovDeriv Ω T w v := by
  simp only [rhoCovDeriv]
  rw [fderiv_fun_mul hs (hT _)]
  simp only [add_apply, smul_apply, smul_eq_mul, mul_sub,
    Finset.mul_sum]
  ring

/-- Helper (P2): Leibniz rule `∇(S ⊗ T) = ∇S ⊗ T + S ⊗ ∇T` for a `1`-form-like `S`. -/
theorem s05_covDeriv_tmul {Ω : Set ℂ} {k : ℕ} {S : ℂ → ℂ → ℝ} {T : TensorField k} {w : ℂ}
    (hS : ∀ u, DifferentiableAt ℝ (fun x => S x u) w)
    (hT : ∀ u, DifferentiableAt ℝ (fun x => T x u) w) (v : Fin (k + 2) → ℂ) :
    rhoCovDeriv Ω (k := k + 1) (fun x u => S x (u 0) * T x (Fin.tail u)) w v =
      (fderiv ℝ (fun x => S x (v 1)) w (v 0) - S w (rhoChristoffel Ω w (v 0) (v 1))) *
          T w (Fin.tail (Fin.tail v)) +
        S w (v 1) * rhoCovDeriv Ω T w (Fin.cons (v 0) (Fin.tail (Fin.tail v))) := by
  simp only [rhoCovDeriv]
  rw [fderiv_fun_mul (hS _) (hT _), Fin.sum_univ_succ]
  simp only [Fin.tail_update_zero, Fin.tail_update_succ, Fin.cons_zero, Fin.tail_cons,
    Function.update_self, add_apply, smul_apply,
    smul_eq_mul, mul_sub, sub_mul, Finset.mul_sum]
  have h0 : ∀ i : Fin k, ∀ a : ℂ, Function.update (Fin.tail v) i.succ a 0 = v 1 := fun i a => by
    rw [Function.update_of_ne (Fin.succ_ne_zero i).symm]
    rfl
  simp only [h0]
  have h1 : Fin.tail v 0 = v 1 := rfl
  have h2 : ∀ x : Fin k, Fin.tail v x.succ = Fin.tail (Fin.tail v) x := fun _ => rfl
  rw [h1]
  simp only [h2]
  ring

/-- Helper (P2): an `ℝ`-linear functional on `ℂ` in the frame `(1, i)`. -/
theorem s05_clm_apply_eq (ℓ : ℂ →L[ℝ] ℝ) (X : ℂ) : ℓ X = ℓ 1 * X.re + ℓ I * X.im := by
  have h := map_add ℓ (X.re • (1 : ℂ)) (X.im • I)
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    show X.re • (1 : ℂ) + X.im • I = X by apply Complex.ext <;> simp] at h
  rw [h]
  ring

/-- Helper (P2): `dλ(X) = λ ⟨∇φ, X⟩` (`φ = log λ`). -/
theorem s05_fderiv_density {Ω : Set ℂ} {w : ℂ} (hd : DifferentiableAt ℝ (poincareDensity Ω) w)
    (hpos : 0 < poincareDensity Ω w) (X : ℂ) :
    fderiv ℝ (poincareDensity Ω) w X = poincareDensity Ω w *
      ((logDensityGrad Ω w).re * X.re + (logDensityGrad Ω w).im * X.im) := by
  have hL := fderiv.log hd hpos.ne'
  have hre : (logDensityGrad Ω w).re =
      fderiv ℝ (fun x => Real.log (poincareDensity Ω x)) w 1 := by simp [logDensityGrad]
  have him : (logDensityGrad Ω w).im =
      fderiv ℝ (fun x => Real.log (poincareDensity Ω x)) w I := by simp [logDensityGrad]
  rw [hre, him, ← s05_clm_apply_eq, hL]
  simp only [smul_apply, smul_eq_mul]
  field_simp

/-- Helper (P2): `ρ` is parallel, `∇ρ = 0`, where `λ` is differentiable and positive. -/
theorem s05_covDeriv_metric {Ω : Set ℂ} {w : ℂ} (hd : DifferentiableAt ℝ (poincareDensity Ω) w)
    (hpos : 0 < poincareDensity Ω w) (v : Fin 3 → ℂ) : rhoCovDeriv Ω (rhoMetricT Ω) w v = 0 := by
  have h2 : fderiv ℝ (fun x => poincareDensity Ω x ^ 2) w (v 0) =
      2 * poincareDensity Ω w * fderiv ℝ (poincareDensity Ω) w (v 0) := by
    rw [fderiv_fun_pow 2 hd]
    simp only [smul_apply, smul_eq_mul, nsmul_eq_mul]
    ring
  simp only [rhoCovDeriv, rhoMetricT]
  have hd2 : DifferentiableAt ℝ (fun x => poincareDensity Ω x ^ 2) w := hd.pow 2
  rw [fderiv_mul_const hd2, smul_apply, smul_eq_mul, h2,
    s05_fderiv_density hd hpos]
  simp [Fin.sum_univ_two, rhoChristoffel, Fin.tail, Function.update_apply, Complex.mul_re]
  ring

/-- Helper (P2): `∇²T = ∇(∇T)`. -/
theorem s05_iter_two (Ω : Set ℂ) {k : ℕ} (T : TensorField k) (w : ℂ) (v : Fin (k + 2) → ℂ) :
    rhoIterCovDeriv Ω 2 T w v = rhoCovDeriv Ω (rhoCovDeriv Ω T) w v := rfl

/-- Helper (P2): `∇¹T = ∇T`. -/
theorem s05_iter_one (Ω : Set ℂ) {k : ℕ} (T : TensorField k) (w : ℂ) (v : Fin (k + 1) → ℂ) :
    rhoIterCovDeriv Ω 1 T w v = rhoCovDeriv Ω T w v := rfl

/-- Helper (P2): the `ρ`-lowered `a♭` is jointly smooth. -/
theorem s05_lowerA_smooth {Ω D : Set ℂ} {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ}
    (hl : ContDiffOn ℝ ∞ (poincareDensity Ω) D)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun w => aUp w i j) D) :
    ContDiffOn ℝ ∞ (fun p : ℂ × (Fin 2 → ℂ) => lowerA Ω aUp p.1 p.2) (D ×ˢ univ) := by
  have hfst : ContDiffOn ℝ ∞ (fun p : ℂ × (Fin 2 → ℂ) => p.1) (D ×ˢ univ) := contDiffOn_fst
  have hm : MapsTo (fun p : ℂ × (Fin 2 → ℂ) => p.1) (D ×ˢ univ) D := fun p hp => hp.1
  have hc : ∀ m i : Fin 2,
      ContDiffOn ℝ ∞ (fun p : ℂ × (Fin 2 → ℂ) => cvec (p.2 m) i) (D ×ˢ univ) :=
    fun m i => ((contDiff_apply ℝ (fun _ => ℝ) i).comp (s05_cvec_contDiff.comp
      ((contDiff_apply ℝ (fun _ => ℂ) m).comp contDiff_snd))).contDiffOn
  simp only [lowerA, dotProduct, mulVec]
  exact ((hl.comp hfst hm).pow 4).mul (ContDiffOn.sum fun i _ => (hc 0 i).mul
    (ContDiffOn.sum fun j _ => ((ha i j).comp hfst hm).mul (hc 1 j)))

/-- Helper (P2): slices of a jointly smooth tensor field are differentiable on the open set. -/
theorem s05_slice_diff {U : Set ℂ} (hU : IsOpen U) {k : ℕ} {T : TensorField k}
    (hT : ContDiffOn ℝ ∞ (fun p : ℂ × (Fin k → ℂ) => T p.1 p.2) (U ×ˢ univ)) {w : ℂ}
    (hw : w ∈ U) (u : Fin k → ℂ) : DifferentiableAt ℝ (fun x => T x u) w := by
  have h : ContDiffOn ℝ ∞ (fun x => T x u) U :=
    hT.comp (contDiffOn_id.prodMk contDiffOn_const) fun x hx => ⟨hx, mem_univ _⟩
  exact (h.contDiffAt (hU.mem_nhds hw)).differentiableAt (by simp)

/-- Helper (P2): on `D`, `∇(a♭ - ρ) = ∇a♭` and `∇²(a♭ - ρ) = ∇²a♭`. -/
theorem s05_covDeriv_lowerA_sub {Ω D : Set ℂ} {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ}
    (hD : IsOpen D) (hl : ContDiffOn ℝ ∞ (poincareDensity Ω) D)
    (hpos : ∀ w ∈ D, 0 < poincareDensity Ω w)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun w => aUp w i j) D) {w : ℂ} (hw : w ∈ D) :
    rhoCovDeriv Ω (lowerA Ω aUp - rhoMetricT Ω) w = rhoCovDeriv Ω (lowerA Ω aUp) w ∧
      rhoCovDeriv Ω (rhoCovDeriv Ω (lowerA Ω aUp - rhoMetricT Ω)) w =
        rhoCovDeriv Ω (rhoCovDeriv Ω (lowerA Ω aUp)) w := by
  have hA := s05_lowerA_smooth hl ha
  have key : ∀ x ∈ D, rhoCovDeriv Ω (lowerA Ω aUp - rhoMetricT Ω) x =
      rhoCovDeriv Ω (lowerA Ω aUp) x := fun x hx => funext fun v => by
    have hd : DifferentiableAt ℝ (poincareDensity Ω) x :=
      (hl.contDiffAt (hD.mem_nhds hx)).differentiableAt (by simp)
    have hρ : ∀ u, DifferentiableAt ℝ (fun y => rhoMetricT Ω y u) x := fun u =>
      (hd.pow 2).mul_const _
    rw [s05_covDeriv_sub (s05_slice_diff hD hA hx) hρ, s05_covDeriv_metric hd (hpos x hx),
      sub_zero]
  exact ⟨key w hw, s05_covDeriv_congr (Filter.mem_of_superset (hD.mem_nhds hw) key)⟩

/-- Helper (P2): pointwise bound from a `C^j` norm. -/
theorem s05_cj_point {Ω E : Set ℂ} {k j i : ℕ} {T : TensorField k} (hi : i ≤ j) {w : ℂ}
    (hw : w ∈ E) :
    ENNReal.ofReal (rhoTensorNorm Ω (rhoIterCovDeriv Ω i T) w) ≤ rhoCjNorm Ω j T E := by
  unfold rhoCjNorm
  exact le_iSup₂_of_le i hi (le_iSup₂_of_le w hw le_rfl)

/-- Helper (P2): pointwise form of `ε'`-admissibility. -/
theorem s05_adm_point {Ω D : Set ℂ} {ε' : ℝ} {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ}
    {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ} (h : IsAdmissibleOp Ω D ε' aUp bUp c)
    (hpos : ∀ w ∈ D, 0 < poincareDensity Ω w) {i i' : ℕ} (hi : i ≤ 2) (hi' : i' ≤ 1) {w : ℂ}
    (hw : w ∈ D) :
    rhoTensorNorm Ω (rhoIterCovDeriv Ω i (lowerA Ω aUp - rhoMetricT Ω)) w +
      rhoTensorNorm Ω (rhoIterCovDeriv Ω i' (lowerB Ω bUp)) w + |c w - 2| ≤ ε' := by
  obtain ⟨hε, -, -, -, -, hn⟩ := h
  have hnn : ∀ {k : ℕ} (T : TensorField k), 0 ≤ rhoTensorNorm Ω T w := fun T =>
    div_nonneg (Real.sqrt_nonneg _) (pow_nonneg (hpos w hw).le _)
  have h5 : rhoTensorNorm Ω (rhoIterCovDeriv Ω 0 (scalarField fun w => c w - 2)) w =
      |c w - 2| := by
    simp [rhoTensorNorm, rhoIterCovDeriv, scalarField, Real.sqrt_sq_eq_abs]
  have h := (add_le_add (add_le_add (s05_cj_point (T := lowerA Ω aUp - rhoMetricT Ω) hi hw)
    (s05_cj_point (T := lowerB Ω bUp) hi' hw))
    (s05_cj_point (j := 0) (T := scalarField fun w => c w - 2) le_rfl hw)).trans hn
  rw [h5, ← ENNReal.ofReal_add (hnn _) (hnn _),
    ← ENNReal.ofReal_add (add_nonneg (hnn _) (hnn _)) (abs_nonneg _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).1 h

/-- Helper (P2): some squared frame components are bounded by the squared HS norm. -/
theorem s05_sum_sq_le {k : ℕ} {ι : Type*} [Fintype ι] {σ : ι → (Fin k → Fin 2)}
    (hσ : Function.Injective σ) (F : (Fin k → Fin 2) → ℝ) :
    ∑ p, F (σ p) ^ 2 ≤ ∑ idx, F idx ^ 2 := by
  classical
  rw [← Finset.sum_image (f := fun idx => F idx ^ 2) (fun x _ y _ h => hσ h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _

/-- Helper (P2): `|∑ x_p| ≤ 2 √S` for at most four terms with `∑ x_p² ≤ S`. -/
theorem s05_abs_sum_le {ι : Type*} [Fintype ι] (hι : Fintype.card ι ≤ 4) (x : ι → ℝ) {S : ℝ}
    (hS : ∑ p, x p ^ 2 ≤ S) : |∑ p, x p| ≤ 2 * Real.sqrt S := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x)
  have h0 : (0 : ℝ) ≤ ∑ p, x p ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : (∑ p, x p) ^ 2 ≤ 4 * S := by
    refine h1.trans ?_
    rw [Finset.card_univ]
    exact mul_le_mul (by exact_mod_cast hι) hS h0 (by norm_num)
  calc |∑ p, x p| ≤ Real.sqrt (4 * S) := Real.abs_le_sqrt h2
    _ = 2 * Real.sqrt S := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]

/-- Helper (P2): a trace-type sum of frame components is at most `2 λ^k ‖T‖_ρ`. -/
theorem s05_trace_le {Ω : Set ℂ} {k : ℕ} (T : TensorField k) {w : ℂ}
    (hl : 0 < poincareDensity Ω w) {ι : Type*} [Fintype ι] (hι : Fintype.card ι ≤ 4)
    {σ : ι → (Fin k → Fin 2)} (hσ : Function.Injective σ) :
    |∑ p, T w (fun m => frameVec (σ p m))| ≤
      2 * poincareDensity Ω w ^ k * rhoTensorNorm Ω T w := by
  have hb := s05_abs_sum_le hι (fun p => T w (fun m => frameVec (σ p m)))
    (s05_sum_sq_le hσ (fun idx => T w fun m => frameVec (idx m)))
  unfold rhoTensorNorm
  rw [mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (pow_pos hl k).ne']
  exact hb

/-- Helper (P2): the Hilbert–Schmidt sum is `(λ^k ‖T‖_ρ)²`. -/
theorem s05_sqrt_hs {Ω : Set ℂ} {k : ℕ} (T : TensorField k) {w : ℂ}
    (hl : 0 < poincareDensity Ω w) :
    Real.sqrt (∑ idx : Fin k → Fin 2, (T w fun i => frameVec (idx i)) ^ 2) =
      poincareDensity Ω w ^ k * rhoTensorNorm Ω T w := by
  unfold rhoTensorNorm
  rw [mul_div_assoc', mul_div_cancel_left₀ _ (pow_pos hl k).ne']

/-- Helper (P2): the frame components of a lowered vector field. -/
theorem s05_lowerB_hs (Ω : Set ℂ) (β : ℂ → Fin 2 → ℝ) (w : ℂ) :
    ∑ idx : Fin 1 → Fin 2, (lowerB Ω β w fun m => frameVec (idx m)) ^ 2 =
      ∑ m : Fin 2, (poincareDensity Ω w ^ 2 * β w m) ^ 2 := by
  rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp]
  refine Finset.sum_congr rfl fun m _ => ?_
  fin_cases m <;> simp [lowerB, frameVec, cvec, dotProduct, Fin.sum_univ_two]

/-- Helper (P2): the bounds `|c* - 2| ≤ 5ε'`, `|b*|_ρ ≤ 4ε'` of (5.4). -/
theorem s05_adjoint_bounds {Ω D : Set ℂ} {ε' : ℝ} {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ}
    {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ} (h : IsAdmissibleOp Ω D ε' aUp bUp c)
    (hl : ContDiffOn ℝ ∞ (poincareDensity Ω) D) (hpos : ∀ w ∈ D, 0 < poincareDensity Ω w)
    {w : ℂ} (hw : w ∈ D) :
    |adjCoeffC Ω aUp bUp c w - 2| ≤ 5 * ε' ∧
      rhoTensorNorm Ω (lowerB Ω (adjCoeffB Ω aUp bUp)) w ≤ 4 * ε' := by
  have hε := h.1
  have hsub := s05_covDeriv_lowerA_sub h.2.2.1 hl hpos h.2.2.2.2.1.1 hw
  have hL := hpos w hw
  have hnn : ∀ {k : ℕ} (T : TensorField k), 0 ≤ rhoTensorNorm Ω T w := fun T =>
    div_nonneg (Real.sqrt_nonneg _) (pow_nonneg hL.le _)
  constructor
  · -- `c*`
    have hDD : |rhoDDiv Ω aUp w| ≤
        2 * rhoTensorNorm Ω (rhoIterCovDeriv Ω 2 (lowerA Ω aUp - rhoMetricT Ω)) w := by
      have hσ : Function.Injective (fun p : Fin 2 × Fin 2 => ![p.2, p.1, p.1, p.2]) :=
        fun p q hpq => Prod.ext (by simpa using congrFun hpq 1) (by simpa using congrFun hpq 0)
      have ht := s05_trace_le (rhoIterCovDeriv Ω 2 (lowerA Ω aUp - rhoMetricT Ω)) hL
        (by simp) hσ
      have he : (∑ i : Fin 2, ∑ j : Fin 2, rhoIterCovDeriv Ω 2 (lowerA Ω aUp) w
          ![frameVec j, frameVec i, frameVec i, frameVec j]) =
          ∑ p : Fin 2 × Fin 2, rhoIterCovDeriv Ω 2 (lowerA Ω aUp - rhoMetricT Ω) w
            (fun m => frameVec (![p.2, p.1, p.1, p.2] m)) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [s05_iter_two, s05_iter_two, hsub.2]
        congr 1
        ext m
        fin_cases m <;> rfl
      unfold rhoDDiv
      rw [he, abs_div, abs_of_pos (pow_pos hL 4), div_le_iff₀ (pow_pos hL 4)]
      calc _ ≤ _ := ht
        _ = _ := by ring
    have hDB : |rhoDivB Ω bUp w| ≤
        2 * rhoTensorNorm Ω (rhoIterCovDeriv Ω 1 (lowerB Ω bUp)) w := by
      have hσ : Function.Injective (fun i : Fin 2 => ![i, i]) :=
        fun p q hpq => by simpa using congrFun hpq 0
      have ht := s05_trace_le (rhoIterCovDeriv Ω 1 (lowerB Ω bUp)) hL (by simp) hσ
      have he : (∑ i : Fin 2, rhoCovDeriv Ω (lowerB Ω bUp) w ![frameVec i, frameVec i]) =
          ∑ i : Fin 2, rhoIterCovDeriv Ω 1 (lowerB Ω bUp) w
            (fun m => frameVec (![i, i] m)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [s05_iter_one]
        congr 1
        ext m
        fin_cases m <;> rfl
      unfold rhoDivB
      rw [he, abs_div, abs_of_pos (pow_pos hL 2), div_le_iff₀ (pow_pos hL 2)]
      calc _ ≤ _ := ht
        _ = _ := by ring
    have hp := s05_adm_point h hpos (i := 2) (i' := 1) le_rfl le_rfl hw
    have hc : adjCoeffC Ω aUp bUp c w - 2 = (c w - 2) - rhoDDiv Ω aUp w + rhoDivB Ω bUp w := by
      unfold adjCoeffC; ring
    rw [hc]
    have h1 := abs_sub (c w - 2) (rhoDDiv Ω aUp w)
    have h2 := abs_add_le (c w - 2 - rhoDDiv Ω aUp w) (rhoDivB Ω bUp w)
    have h3 := hnn (rhoIterCovDeriv Ω 2 (lowerA Ω aUp - rhoMetricT Ω))
    have h4 := hnn (rhoIterCovDeriv Ω 1 (lowerB Ω bUp))
    linarith [abs_nonneg (c w - 2)]
  · -- `b*`
    have hp := s05_adm_point h hpos (i := 1) (i' := 0) (by norm_num) (by norm_num) hw
    have hnA0 := hnn (rhoIterCovDeriv Ω 1 (lowerA Ω aUp - rhoMetricT Ω))
    have hnB0 := hnn (rhoIterCovDeriv Ω 0 (lowerB Ω bUp))
    set nA := rhoTensorNorm Ω (rhoIterCovDeriv Ω 1 (lowerA Ω aUp - rhoMetricT Ω)) w with hnA
    set nB := rhoTensorNorm Ω (rhoIterCovDeriv Ω 0 (lowerB Ω bUp)) w with hnB
    set L := poincareDensity Ω w with hLdef
    -- the components `s m = ∑_j ∇a♭(e_j, e_m, e_j)`
    set s : Fin 2 → ℝ := fun m => ∑ j : Fin 2,
      rhoCovDeriv Ω (lowerA Ω aUp) w ![frameVec j, frameVec m, frameVec j] with hs
    have hS : s 0 ^ 2 + s 1 ^ 2 ≤ 2 * (L ^ 3 * nA) ^ 2 := by
      have hσ : Function.Injective (fun p : Fin 2 × Fin 2 => ![p.2, p.1, p.2]) :=
        fun p q hpq => Prod.ext (by simpa using congrFun hpq 1) (by simpa using congrFun hpq 0)
      have h1 := s05_sum_sq_le hσ
        (fun idx => rhoIterCovDeriv Ω 1 (lowerA Ω aUp - rhoMetricT Ω) w fun m => frameVec (idx m))
      have h2 : Real.sqrt (∑ idx : Fin 3 → Fin 2, (rhoIterCovDeriv Ω 1
          (lowerA Ω aUp - rhoMetricT Ω) w fun m => frameVec (idx m)) ^ 2) = L ^ 3 * nA :=
        s05_sqrt_hs _ hL
      rw [← h2, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      have hm : ∀ m : Fin 2, s m ^ 2 ≤ 2 * ∑ j : Fin 2,
          (rhoIterCovDeriv Ω 1 (lowerA Ω aUp - rhoMetricT Ω) w
            fun i => frameVec (![j, m, j] i)) ^ 2 := by
        intro m
        have := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun j : Fin 2 => rhoIterCovDeriv Ω 1 (lowerA Ω aUp - rhoMetricT Ω) w
            fun i => frameVec (![j, m, j] i))
        rw [Finset.card_univ, Fintype.card_fin] at this
        convert this using 2
        · rw [hs]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [s05_iter_one, hsub.1]
          congr 1
          ext i
          fin_cases i <;> rfl
      rw [Fintype.sum_prod_type] at h1
      simp only [Fin.sum_univ_two] at h1 hm
      linarith [hm 0, hm 1]
    have hB : (L ^ 2 * bUp w 0) ^ 2 + (L ^ 2 * bUp w 1) ^ 2 = (L * nB) ^ 2 := by
      have h2 : Real.sqrt (∑ m : Fin 2, (L ^ 2 * bUp w m) ^ 2) = L * nB := by
        have := s05_sqrt_hs (lowerB Ω bUp) hL
        rw [s05_lowerB_hs, pow_one] at this
        exact this
      rw [← Fin.sum_univ_two (fun m => (L ^ 2 * bUp w m) ^ 2), ← h2,
        Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    have hy : ∀ m : Fin 2, L ^ 2 * adjCoeffB Ω aUp bUp w m =
        2 * (s m / L ^ 2) - L ^ 2 * bUp w m := by
      intro m
      simp only [adjCoeffB, rhoDivA, Pi.sub_apply, nsmul_eq_mul, Nat.cast_ofNat,
        Pi.mul_apply, Pi.ofNat_apply, hs, ← hLdef]
      field_simp
    unfold rhoTensorNorm
    rw [s05_lowerB_hs, Fin.sum_univ_two, ← hLdef, hy 0, hy 1, pow_one, div_le_iff₀ hL]
    have hS' : (s 0 / L ^ 2) ^ 2 + (s 1 / L ^ 2) ^ 2 ≤ 2 * (L * nA) ^ 2 := by
      have h4 : (0 : ℝ) < L ^ 4 := by positivity
      have : (s 0 / L ^ 2) ^ 2 + (s 1 / L ^ 2) ^ 2 = (s 0 ^ 2 + s 1 ^ 2) / L ^ 4 := by
        field_simp
      rw [this, div_le_iff₀ h4]
      nlinarith [hS]
    set S0 := s 0 / L ^ 2
    set S1 := s 1 / L ^ 2
    have hsq : (2 * S0 - L ^ 2 * bUp w 0) ^ 2 + (2 * S1 - L ^ 2 * bUp w 1) ^ 2 ≤
        (4 * ε' * L) ^ 2 := by
      have e1 : (2 * S0 - L ^ 2 * bUp w 0) ^ 2 ≤ 8 * S0 ^ 2 + 2 * (L ^ 2 * bUp w 0) ^ 2 := by
        nlinarith [sq_nonneg (2 * S0 + L ^ 2 * bUp w 0)]
      have e2 : (2 * S1 - L ^ 2 * bUp w 1) ^ 2 ≤ 8 * S1 ^ 2 + 2 * (L ^ 2 * bUp w 1) ^ 2 := by
        nlinarith [sq_nonneg (2 * S1 + L ^ 2 * bUp w 1)]
      have e3 : 16 * (L * nA) ^ 2 + 2 * (L * nB) ^ 2 ≤ (4 * ε' * L) ^ 2 := by
        have hab : nA + nB ≤ ε' := by linarith [abs_nonneg (c w - 2)]
        have : (nA + nB) ^ 2 ≤ ε' ^ 2 := pow_le_pow_left₀ (by linarith) hab 2
        nlinarith [mul_nonneg hnA0 hnB0, sq_nonneg L, mul_nonneg (mul_nonneg hnA0 hnB0) (sq_nonneg L),
          mul_le_mul_of_nonneg_left this (sq_nonneg L), sq_nonneg nB, mul_nonneg (sq_nonneg nB) (sq_nonneg L)]
      nlinarith [hS', hB]
    calc Real.sqrt _ ≤ Real.sqrt ((4 * ε' * L) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 4 * ε' * L := Real.sqrt_sq (by positivity)

/-- Helper (P2): `∇u = du` for a function. -/
theorem s05_covDeriv_scalar (Ω : Set ℂ) (u : ℂ → ℝ) :
    rhoCovDeriv Ω (scalarField u) = fun x v => fderiv ℝ u x (v 0) := by
  funext x v
  simp [rhoCovDeriv, scalarField]

/-- Helper (P2): `∇²u(X, Y) = X(du(Y)) - du(Γ(X, Y))`. -/
theorem s05_rhoHess_eq (Ω : Set ℂ) (u : ℂ → ℝ) (w X Y : ℂ) :
    rhoHess Ω u w ![X, Y] =
      fderiv ℝ (fun x => fderiv ℝ u x Y) w X - fderiv ℝ u w (rhoChristoffel Ω w X Y) := by
  rw [rhoHess, s05_iter_two, s05_covDeriv_scalar]
  simp [rhoCovDeriv, Fin.tail]

/-- Helper (P2): `a♭(e_i, e_j) = λ⁴ a^{ij}`. -/
theorem s05_lowerA_frame (Ω : Set ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (w : ℂ)
    (i j : Fin 2) :
    lowerA Ω aUp w ![frameVec i, frameVec j] = poincareDensity Ω w ^ 4 * aUp w i j := by
  fin_cases i <;> fin_cases j <;>
    simp [lowerA, cvec, frameVec, dotProduct, mulVec, Fin.sum_univ_two]

/-- Helper (P2): `b♭(e_i) = λ² b^i`. -/
theorem s05_lowerB_frame (Ω : Set ℂ) (bUp : ℂ → Fin 2 → ℝ) (w : ℂ) (i : Fin 2) :
    lowerB Ω bUp w ![frameVec i] = poincareDensity Ω w ^ 2 * bUp w i := by
  fin_cases i <;> simp [lowerB, cvec, frameVec, dotProduct, Fin.sum_univ_two]

/-- Helper (P2): the covariant derivative of a symmetric `2`-tensor is symmetric in its last
two slots. -/
theorem s05_covDeriv_symm {Ω : Set ℂ} {T : TensorField 2} {w : ℂ}
    (h : ∀ᶠ x in 𝓝 w, ∀ U V : ℂ, T x ![U, V] = T x ![V, U]) (X U V : ℂ) :
    rhoCovDeriv Ω T w ![X, U, V] = rhoCovDeriv Ω T w ![X, V, U] := by
  have h1 : (fun x => T x ![U, V]) =ᶠ[𝓝 w] fun x => T x ![V, U] := h.mono fun x hx => hx U V
  have h0 := h.self_of_nhds
  have e0 : ∀ a b c : ℂ, Function.update ![a, b] 0 c = ![c, b] := fun a b c => by
    ext i; fin_cases i <;> rfl
  have e1 : ∀ a b c : ℂ, Function.update ![a, b] 1 c = ![a, c] := fun a b c => by
    ext i; fin_cases i <;> rfl
  show fderiv ℝ (fun x => T x ![U, V]) w X -
      ∑ i : Fin 2, T w (Function.update ![U, V] i (rhoChristoffel Ω w X (![U, V] i))) =
    fderiv ℝ (fun x => T x ![V, U]) w X -
      ∑ i : Fin 2, T w (Function.update ![V, U] i (rhoChristoffel Ω w X (![V, U] i)))
  rw [h1.fderiv_eq, Fin.sum_univ_two, Fin.sum_univ_two, e0, e1, e0, e1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h0 (rhoChristoffel Ω w X V) U, h0 V (rhoChristoffel Ω w X U)]
  ring

/-- Helper (P2): `∇(sT)(X, U) = ds(X) T(U) + s ∇T(X, U)` on a `1`-form. -/
theorem s05_covDeriv_smul_two {Ω : Set ℂ} {s : ℂ → ℝ} {T : TensorField 1} {w : ℂ}
    (hs : DifferentiableAt ℝ s w) (hT : ∀ u, DifferentiableAt ℝ (fun x => T x u) w)
    (X U : ℂ) :
    rhoCovDeriv Ω (fun x u => s x * T x u) w ![X, U] =
      fderiv ℝ s w X * T w ![U] + s w * rhoCovDeriv Ω T w ![X, U] :=
  s05_covDeriv_smul hs hT _

/-- Helper (P2): `∇²(v a♭) = ∇²v ⊗ a♭ + dv ⊗ ∇a♭ + ∇a♭ ⊗ dv + v ∇²a♭` (Leibniz twice). -/
theorem s05_hess_prod {Ω D : Set ℂ} {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ} (hD : IsOpen D)
    (hl : ContDiffOn ℝ ∞ (poincareDensity Ω) D) (hpos : ∀ w ∈ D, 0 < poincareDensity Ω w)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun w => aUp w i j) D) {v : ℂ → ℝ} (hv : ContDiffOn ℝ ∞ v D)
    {w : ℂ} (hw : w ∈ D) (X Y U V : ℂ) :
    rhoCovDeriv Ω (rhoCovDeriv Ω (fun x u => v x * lowerA Ω aUp x u)) w ![X, Y, U, V] =
      rhoHess Ω v w ![X, Y] * lowerA Ω aUp w ![U, V] +
        fderiv ℝ v w Y * rhoCovDeriv Ω (lowerA Ω aUp) w ![X, U, V] +
        fderiv ℝ v w X * rhoCovDeriv Ω (lowerA Ω aUp) w ![Y, U, V] +
        v w * rhoCovDeriv Ω (rhoCovDeriv Ω (lowerA Ω aUp)) w ![X, Y, U, V] := by
  have hA := s05_lowerA_smooth hl ha
  have hdA := s05_covDeriv_smooth hD hl hpos hA
  have hvd : ∀ x ∈ D, DifferentiableAt ℝ v x := fun x hx =>
    (hv.contDiffAt (hD.mem_nhds hx)).differentiableAt (by simp)
  have hdv : ContDiffOn ℝ ∞ (fderiv ℝ v) D :=
    hv.fderiv_of_isOpen hD (m := ∞) (le_of_eq ENat.coe_top_add_one)
  have hdvd : ∀ U' : ℂ, DifferentiableAt ℝ (fun x => fderiv ℝ v x U') w := fun U' =>
    ((hdv.clm_apply contDiffOn_const).contDiffAt (hD.mem_nhds hw)).differentiableAt (by simp)
  have step : ∀ᶠ x in 𝓝 w, rhoCovDeriv Ω (fun x u => v x * lowerA Ω aUp x u) x =
      fun u => fderiv ℝ v x (u 0) * lowerA Ω aUp x (Fin.tail u) +
        v x * rhoCovDeriv Ω (lowerA Ω aUp) x u :=
    Filter.mem_of_superset (hD.mem_nhds hw) fun x hx => funext fun u =>
      s05_covDeriv_smul (hvd x hx) (s05_slice_diff hD hA hx) u
  have hP : ∀ u : Fin 3 → ℂ, DifferentiableAt ℝ
      (fun x => fderiv ℝ v x (u 0) * lowerA Ω aUp x (Fin.tail u)) w := fun u =>
    (hdvd (u 0)).mul (s05_slice_diff hD hA hw _)
  have hQ : ∀ u : Fin 3 → ℂ, DifferentiableAt ℝ
      (fun x => v x * rhoCovDeriv Ω (lowerA Ω aUp) x u) w := fun u =>
    (hvd w hw).mul (s05_slice_diff hD hdA hw u)
  rw [s05_covDeriv_congr step, s05_covDeriv_add hP hQ,
    s05_covDeriv_tmul hdvd (s05_slice_diff hD hA hw),
    s05_covDeriv_smul (hvd w hw) (s05_slice_diff hD hdA hw), s05_rhoHess_eq]
  show (fderiv ℝ (fun x => fderiv ℝ v x Y) w X - fderiv ℝ v w (rhoChristoffel Ω w X Y)) *
        lowerA Ω aUp w ![U, V] + fderiv ℝ v w Y * rhoCovDeriv Ω (lowerA Ω aUp) w ![X, U, V] +
      (fderiv ℝ v w X * rhoCovDeriv Ω (lowerA Ω aUp) w ![Y, U, V] +
        v w * rhoCovDeriv Ω (rhoCovDeriv Ω (lowerA Ω aUp)) w ![X, Y, U, V]) = _
  ring

/-- Helper (P2): the formal adjoint as a divergence form, first part of (5.4). -/
theorem s05_adjoint_formula {Ω D : Set ℂ} {ε' : ℝ} {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ}
    {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ} (h : IsAdmissibleOp Ω D ε' aUp bUp c)
    (hl : ContDiffOn ℝ ∞ (poincareDensity Ω) D) (hpos : ∀ w ∈ D, 0 < poincareDensity Ω w)
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ ∞ v D) {w : ℂ} (hw : w ∈ D) :
    ellOpAdj Ω aUp bUp c v w =
      c w * v w - rhoDDiv Ω (fun x => v x • aUp x) w + rhoDivB Ω (fun x => v x • bUp x) w := by
  obtain ⟨-, -, hD, -, ⟨ha, hb, -, hsym⟩, -⟩ := h
  have hL := hpos w hw
  have hvd : DifferentiableAt ℝ v w :=
    (hv.contDiffAt (hD.mem_nhds hw)).differentiableAt (by simp)
  have hA1 : lowerA Ω (fun x => v x • aUp x) = fun x u => v x * lowerA Ω aUp x u := by
    funext x u
    simp only [lowerA, dotProduct, mulVec, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
    ring
  have hB1 : lowerB Ω (fun x => v x • bUp x) = fun x u => v x * lowerB Ω bUp x u := by
    funext x u
    simp only [lowerB, smul_dotProduct, smul_eq_mul]
    ring
  have hBd : ∀ u, DifferentiableAt ℝ (fun x => lowerB Ω bUp x u) w := by
    intro u
    have hld : DifferentiableAt ℝ (poincareDensity Ω) w :=
      (hl.contDiffAt (hD.mem_nhds hw)).differentiableAt (by simp)
    have hbi : ∀ i, DifferentiableAt ℝ (fun x => bUp x i) w := fun i =>
      ((hb i).contDiffAt (hD.mem_nhds hw)).differentiableAt (by simp)
    simp only [lowerB, dotProduct, Fin.sum_univ_two]
    exact (hld.pow 2).mul (((hbi 0).mul_const _).add ((hbi 1).mul_const _))
  have hsym01 : ∀ x ∈ D, aUp x 0 1 = aUp x 1 0 := fun x hx => by
    have := congrFun (congrFun (hsym x hx) 1) 0
    simpa [Matrix.transpose_apply] using this
  have hsymA : ∀ x ∈ D, ∀ U V : ℂ, lowerA Ω aUp x ![U, V] = lowerA Ω aUp x ![V, U] := by
    intro x hx U V
    simp only [lowerA, dotProduct, mulVec, Fin.sum_univ_two, cvec, Matrix.cons_val_zero,
      Matrix.cons_val_one, hsym01 x hx]
    ring
  have hsA := s05_covDeriv_symm (Ω := Ω) (Filter.mem_of_superset (hD.mem_nhds hw) hsymA)
  have hDD : rhoDDiv Ω (fun x => v x • aUp x) w = (∑ i : Fin 2, ∑ j : Fin 2,
      (rhoHess Ω v w ![frameVec j, frameVec i] * (poincareDensity Ω w ^ 4 * aUp w i j) +
        fderiv ℝ v w (frameVec i) *
          rhoCovDeriv Ω (lowerA Ω aUp) w ![frameVec j, frameVec i, frameVec j] +
        fderiv ℝ v w (frameVec j) *
          rhoCovDeriv Ω (lowerA Ω aUp) w ![frameVec i, frameVec i, frameVec j] +
        v w * rhoCovDeriv Ω (rhoCovDeriv Ω (lowerA Ω aUp)) w
          ![frameVec j, frameVec i, frameVec i, frameVec j])) / poincareDensity Ω w ^ 4 := by
    unfold rhoDDiv
    rw [hA1]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [s05_iter_two, s05_hess_prod hD hl hpos ha hv hw, s05_lowerA_frame]
  have hDB : rhoDivB Ω (fun x => v x • bUp x) w = (∑ i : Fin 2,
      (fderiv ℝ v w (frameVec i) * (poincareDensity Ω w ^ 2 * bUp w i) +
        v w * rhoCovDeriv Ω (lowerB Ω bUp) w ![frameVec i, frameVec i])) /
      poincareDensity Ω w ^ 2 := by
    unfold rhoDivB
    rw [hB1]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [s05_covDeriv_smul_two hvd hBd, s05_lowerB_frame]
  rw [hDD, hDB]
  simp only [ellOpAdj, ellOp, adjCoeffC, adjCoeffB, rhoDivA, rhoDDiv, rhoDivB, s05_iter_two,
    Pi.sub_apply, nsmul_eq_mul, Nat.cast_ofNat, Pi.mul_apply, Pi.ofNat_apply, Fin.sum_univ_two]
  rw [hsA (frameVec 1) (frameVec 1) (frameVec 0), hsA (frameVec 0) (frameVec 0) (frameVec 1),
    hsym01 w hw]
  field_simp
  ring

/-- **(5.6)** (`eq:adjoint`, sec05-upper.tex:134) and the bounds after it.  For an `ε'`-admissible
`𝓛` on `D`: the adjoint is `𝓛*v = c v - ∇_j∇_i(a^{ij} v) + ∇_i(b^i v)` for smooth `v`, and
`|c* - 2| ≤ 5ε'`, `|b*|_ρ ≤ 4ε'` on `D`. -/
theorem eq_adjoint : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (D : Set ℂ) (ε' : ℝ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsAdmissibleOp Ω D ε' aUp bUp c →
      (∀ v : ℂ → ℝ, ContDiffOn ℝ ∞ v D → ∀ w ∈ D,
        ellOpAdj Ω aUp bUp c v w =
          c w * v w - rhoDDiv Ω (fun x => v x • aUp x) w + rhoDivB Ω (fun x => v x • bUp x) w) ∧
      ∀ w ∈ D, |adjCoeffC Ω aUp bUp c w - 2| ≤ 5 * ε' ∧
        rhoTensorNorm Ω (lowerB Ω (adjCoeffB Ω aUp bUp)) w ≤ 4 * ε' := by
  intro Ω Ωs hJ D ε' aUp bUp c h
  obtain ⟨-, hl, hpos⟩ := s05_density_smooth hJ
  have hDΩ := h.2.2.2.1
  have hlD := hl.mono hDΩ
  have hposD : ∀ w ∈ D, 0 < poincareDensity Ω w := fun w hw => hpos w (hDΩ hw)
  exact ⟨fun v hv w hw => s05_adjoint_formula h hlD hposD hv hw,
    fun w hw => s05_adjoint_bounds h hlD hposD hw⟩

/-- Green helper (G1): the divergence `∇_i T^i` in Euclidean form,
`λ² div_ρ T = ∂_i(λ² T^i)` (`Γ^k_{ik} = 2∂_i log λ` for `ρ = λ²|dw|²`). -/
theorem s05_gr_divB_eucl {Ω : Set ℂ} {T : ℂ → Fin 2 → ℝ} {w : ℂ}
    (hT : ∀ i, DifferentiableAt ℝ (fun x => T x i) w)
    (hd : DifferentiableAt ℝ (poincareDensity Ω) w) (hpos : 0 < poincareDensity Ω w) :
    poincareDensity Ω w ^ 2 * rhoDivB Ω T w =
      ∑ i : Fin 2, fderiv ℝ (fun x => poincareDensity Ω x ^ 2 * T x i) w (frameVec i) := by
  -- `hT`, `hd` are not needed: both sides use the same (possibly junk) `fderiv` values, and the
  -- identity holds without them (the statement stays true without these hypotheses).
  have _hT := hT
  have _hd := hd
  have hfr : ∀ i : Fin 2, (fun x => lowerB Ω T x (Fin.tail ![frameVec i, frameVec i])) =
      fun x => poincareDensity Ω x ^ 2 * T x i := by
    intro i
    funext x
    have e : Fin.tail ![frameVec i, frameVec i] = ![frameVec i] := by
      ext j; fin_cases j; rfl
    rw [e, s05_lowerB_frame]
  have hcd : ∀ i : Fin 2, rhoCovDeriv Ω (lowerB Ω T) w ![frameVec i, frameVec i] =
      fderiv ℝ (fun x => poincareDensity Ω x ^ 2 * T x i) w (frameVec i) -
        lowerB Ω T w ![rhoChristoffel Ω w (frameVec i) (frameVec i)] := by
    intro i
    show fderiv ℝ (fun x => lowerB Ω T x (Fin.tail ![frameVec i, frameVec i])) w (frameVec i) -
      ∑ j : Fin 1, lowerB Ω T w (Function.update (Fin.tail ![frameVec i, frameVec i]) j
        (rhoChristoffel Ω w (frameVec i) (Fin.tail ![frameVec i, frameVec i] j))) = _
    rw [hfr i, Fin.sum_univ_one]
    congr 2
    ext j
    fin_cases j
    rfl
  have hΓ : lowerB Ω T w ![rhoChristoffel Ω w (frameVec 0) (frameVec 0)] +
      lowerB Ω T w ![rhoChristoffel Ω w (frameVec 1) (frameVec 1)] = 0 := by
    simp [lowerB, cvec, dotProduct, Fin.sum_univ_two, rhoChristoffel, frameVec, Complex.mul_re]
    ring
  have hρ : poincareDensity Ω w ^ 2 ≠ 0 := by positivity
  unfold rhoDivB
  rw [Fin.sum_univ_two, Fin.sum_univ_two, hcd 0, hcd 1, mul_div_cancel₀ _ hρ]
  linear_combination -hΓ

/-- Green helper (G2): `∇_i(∇_j a^{ij}) = ∇_j∇_i a^{ij}` for smooth symmetric `a`
(`∇` commutes with the metric contraction since `∇ρ = 0`). -/
theorem s05_gr_divB_divA {Ω U : Set ℂ} {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ} (hU : IsOpen U)
    (hl : ContDiffOn ℝ ∞ (poincareDensity Ω) U) (hpos : ∀ w ∈ U, 0 < poincareDensity Ω w)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun w => aUp w i j) U) (hsym : ∀ w ∈ U, (aUp w)ᵀ = aUp w)
    {w : ℂ} (hw : w ∈ U) :
    rhoDivB Ω (rhoDivA Ω aUp) w = rhoDDiv Ω aUp w := by
  have hn : U ∈ 𝓝 w := hU.mem_nhds hw
  have hd : DifferentiableAt ℝ (poincareDensity Ω) w :=
    (hl.contDiffAt hn).differentiableAt (by simp)
  have hp := hpos w hw
  have hρ2 : poincareDensity Ω w ^ 2 ≠ 0 := by positivity
  have had : ∀ i j, DifferentiableAt ℝ (fun x => aUp x i j) w := fun i j =>
    ((ha i j).contDiffAt hn).differentiableAt (by simp)
  have hA := s05_lowerA_smooth hl ha
  have hdA := s05_covDeriv_smooth hU hl hpos hA
  set N := rhoCovDeriv Ω (lowerA Ω aUp) with hNdef
  have hNd : ∀ v : Fin 3 → ℂ, DifferentiableAt ℝ (fun x => N x v) w := s05_slice_diff hU hdA hw
  have hDa : ∀ i, DifferentiableAt ℝ (fun x => rhoDivA Ω aUp x i) w := by
    intro i
    simp only [rhoDivA, Fin.sum_univ_two, div_eq_mul_inv]
    exact ((hNd _).fun_add (hNd _)).fun_mul ((hd.fun_pow 4).fun_inv (by positivity))
  have e1 := s05_gr_divB_eucl hDa hd hp
  -- symmetry of `a♭` near every point of `U`, hence of `∇a♭`
  have hsymA : ∀ x ∈ U, ∀ U' V : ℂ, lowerA Ω aUp x ![U', V] = lowerA Ω aUp x ![V, U'] := by
    intro x hx U' V
    have h01 : aUp x 0 1 = aUp x 1 0 := by
      have := congrFun (congrFun (hsym x hx) 1) 0
      simpa [Matrix.transpose_apply] using this
    simp only [lowerA, dotProduct, mulVec, Fin.sum_univ_two, cvec, Matrix.cons_val_zero,
      Matrix.cons_val_one, h01]
    ring
  have hNsym : ∀ x ∈ U, ∀ X U' V : ℂ, N x ![X, U', V] = N x ![X, V, U'] := fun x hx =>
    s05_covDeriv_symm (Filter.mem_of_superset (hU.mem_nhds hx) (hsymA))
  have hs01 : aUp w 0 1 = aUp w 1 0 := by
    have := congrFun (congrFun (hsym w hw) 1) 0
    simpa [Matrix.transpose_apply] using this
  have ha01 : fderiv ℝ (fun x => aUp x 0 1) w = fderiv ℝ (fun x => aUp x 1 0) w := by
    refine Filter.EventuallyEq.fderiv_eq (Filter.mem_of_superset hn fun x hx => ?_)
    have := congrFun (congrFun (hsym x hx) 1) 0
    simpa [Matrix.transpose_apply] using this
  -- `ρ² ∇_j a^{ij} = ρ⁻² Σ_j ∇a♭(e_j, e_j, e_i)` near `w`
  have hQ : ∀ i : Fin 2, fderiv ℝ (fun x => poincareDensity Ω x ^ 2 * rhoDivA Ω aUp x i) w =
      fderiv ℝ (fun x => (N x ![frameVec 0, frameVec 0, frameVec i] +
        N x ![frameVec 1, frameVec 1, frameVec i]) * (poincareDensity Ω x ^ 2)⁻¹) w := by
    intro i
    refine Filter.EventuallyEq.fderiv_eq (Filter.mem_of_superset hn fun x hx => ?_)
    have hx0 := hpos x hx
    simp only [Set.mem_ofPred_eq, rhoDivA, Fin.sum_univ_two, ← hNdef,
      hNsym x hx (frameVec 0) (frameVec i), hNsym x hx (frameVec 1) (frameVec i)]
    field_simp
  have h2 : HasFDerivAt (fun x => poincareDensity Ω x ^ 2)
      (fderiv ℝ (fun x => poincareDensity Ω x ^ 2) w) w := (hd.fun_pow 2).hasFDerivAt
  have h2v : ∀ X, fderiv ℝ (fun x => poincareDensity Ω x ^ 2) w X =
      2 * poincareDensity Ω w * fderiv ℝ (poincareDensity Ω) w X := by
    intro X
    rw [fderiv_fun_pow 2 hd]
    simp only [smul_apply, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have hinv : HasFDerivAt (fun x => (poincareDensity Ω x ^ 2)⁻¹)
      ((-((poincareDensity Ω w ^ 2) ^ 2)⁻¹) • fderiv ℝ (fun x => poincareDensity Ω x ^ 2) w) w :=
    (hasDerivAt_inv hρ2).comp_hasFDerivAt w h2
  have hQd : ∀ i : Fin 2, ∀ X : ℂ, poincareDensity Ω w ^ 4 *
      fderiv ℝ (fun x => (N x ![frameVec 0, frameVec 0, frameVec i] +
        N x ![frameVec 1, frameVec 1, frameVec i]) * (poincareDensity Ω x ^ 2)⁻¹) w X =
        poincareDensity Ω w ^ 2 * (fderiv ℝ (fun x => N x ![frameVec 0, frameVec 0, frameVec i]) w X +
            fderiv ℝ (fun x => N x ![frameVec 1, frameVec 1, frameVec i]) w X) -
          (N w ![frameVec 0, frameVec 0, frameVec i] + N w ![frameVec 1, frameVec 1, frameVec i]) *
            (2 * poincareDensity Ω w * fderiv ℝ (poincareDensity Ω) w X) := by
    intro i X
    have hS := ((hNd ![frameVec 0, frameVec 0, frameVec i]).hasFDerivAt.add
      (hNd ![frameVec 1, frameVec 1, frameVec i]).hasFDerivAt)
    have hF : HasFDerivAt (fun x => (N x ![frameVec 0, frameVec 0, frameVec i] +
        N x ![frameVec 1, frameVec 1, frameVec i]) * (poincareDensity Ω x ^ 2)⁻¹) _ w :=
      hS.mul hinv
    rw [hF.fderiv]
    simp only [smul_apply, add_apply, Pi.add_apply, smul_eq_mul, h2v]
    field_simp
    ring
  -- `∇a♭` at `w`, fully expanded
  have hP4 : ∀ j k (X : ℂ), fderiv ℝ (fun x => poincareDensity Ω x ^ 4 * aUp x j k) w X =
      4 * poincareDensity Ω w ^ 3 * fderiv ℝ (poincareDensity Ω) w X * aUp w j k +
        poincareDensity Ω w ^ 4 * fderiv ℝ (fun x => aUp x j k) w X := by
    intro j k X
    rw [fderiv_fun_mul (hd.fun_pow 4) (had j k),
      fderiv_fun_pow 4 hd]
    simp only [add_apply, smul_apply, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have hq : ∀ k l, DifferentiableAt ℝ (fun x => poincareDensity Ω x ^ 4 * aUp x k l) w :=
    fun k l => (hd.fun_pow 4).fun_mul (had k l)
  have hN : ∀ X U' V : ℂ, N w ![X, U', V] =
      cvec U' 0 * cvec V 0 * fderiv ℝ (fun x => poincareDensity Ω x ^ 4 * aUp x 0 0) w X +
        cvec U' 0 * cvec V 1 * fderiv ℝ (fun x => poincareDensity Ω x ^ 4 * aUp x 0 1) w X +
        cvec U' 1 * cvec V 0 * fderiv ℝ (fun x => poincareDensity Ω x ^ 4 * aUp x 1 0) w X +
        cvec U' 1 * cvec V 1 * fderiv ℝ (fun x => poincareDensity Ω x ^ 4 * aUp x 1 1) w X -
        lowerA Ω aUp w ![rhoChristoffel Ω w X U', V] -
        lowerA Ω aUp w ![U', rhoChristoffel Ω w X V] := by
    intro X U' V
    have e : (fun x => lowerA Ω aUp x (Fin.tail ![X, U', V])) = fun x =>
        cvec U' 0 * cvec V 0 * (poincareDensity Ω x ^ 4 * aUp x 0 0) +
          cvec U' 0 * cvec V 1 * (poincareDensity Ω x ^ 4 * aUp x 0 1) +
          cvec U' 1 * cvec V 0 * (poincareDensity Ω x ^ 4 * aUp x 1 0) +
          cvec U' 1 * cvec V 1 * (poincareDensity Ω x ^ 4 * aUp x 1 1) := by
      funext x
      have : Fin.tail ![X, U', V] = ![U', V] := by
        ext l; fin_cases l <;> rfl
      rw [this]
      simp only [lowerA, dotProduct, mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      ring
    show fderiv ℝ (fun x => lowerA Ω aUp x (Fin.tail ![X, U', V])) w X -
      ∑ l : Fin 2, lowerA Ω aUp w (Function.update (Fin.tail ![X, U', V]) l
        (rhoChristoffel Ω w X (Fin.tail ![X, U', V] l))) = _
    have u0 : Function.update (Fin.tail ![X, U', V]) 0
        (rhoChristoffel Ω w X (Fin.tail ![X, U', V] 0)) = ![rhoChristoffel Ω w X U', V] := by
      ext l; fin_cases l <;> rfl
    have u1 : Function.update (Fin.tail ![X, U', V]) 1
        (rhoChristoffel Ω w X (Fin.tail ![X, U', V] 1)) = ![U', rhoChristoffel Ω w X V] := by
      ext l; fin_cases l <;> rfl
    rw [e, Fin.sum_univ_two, u0, u1,
      fderiv_fun_add ((((hq 0 0).const_mul _).fun_add ((hq 0 1).const_mul _)).fun_add
        ((hq 1 0).const_mul _)) ((hq 1 1).const_mul _),
      fderiv_fun_add (((hq 0 0).const_mul _).fun_add ((hq 0 1).const_mul _))
        ((hq 1 0).const_mul _),
      fderiv_fun_add ((hq 0 0).const_mul _) ((hq 0 1).const_mul _),
      fderiv_const_mul (hq 0 0), fderiv_const_mul (hq 0 1), fderiv_const_mul (hq 1 0),
      fderiv_const_mul (hq 1 1)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  -- the second covariant derivative in the frame
  have hNN : ∀ i j : Fin 2, rhoIterCovDeriv Ω 2 (lowerA Ω aUp) w
      ![frameVec j, frameVec i, frameVec i, frameVec j] =
        fderiv ℝ (fun x => N x ![frameVec i, frameVec i, frameVec j]) w (frameVec j) -
          (N w ![rhoChristoffel Ω w (frameVec j) (frameVec i), frameVec i, frameVec j] +
            N w ![frameVec i, rhoChristoffel Ω w (frameVec j) (frameVec i), frameVec j] +
            N w ![frameVec i, frameVec i, rhoChristoffel Ω w (frameVec j) (frameVec j)]) := by
    intro i j
    rw [s05_iter_two]
    have t : Fin.tail ![frameVec j, frameVec i, frameVec i, frameVec j] =
        ![frameVec i, frameVec i, frameVec j] := by
      ext l; fin_cases l <;> rfl
    show fderiv ℝ (fun x => N x (Fin.tail ![frameVec j, frameVec i, frameVec i, frameVec j])) w
        (frameVec j) - ∑ l : Fin 3, N w (Function.update
          (Fin.tail ![frameVec j, frameVec i, frameVec i, frameVec j]) l
          (rhoChristoffel Ω w (frameVec j)
            (Fin.tail ![frameVec j, frameVec i, frameVec i, frameVec j] l))) = _
    rw [t, Fin.sum_univ_three]
    have u0 : Function.update ![frameVec i, frameVec i, frameVec j] 0
        (rhoChristoffel Ω w (frameVec j) (![frameVec i, frameVec i, frameVec j] 0)) =
          ![rhoChristoffel Ω w (frameVec j) (frameVec i), frameVec i, frameVec j] := by
      ext l; fin_cases l <;> rfl
    have u1 : Function.update ![frameVec i, frameVec i, frameVec j] 1
        (rhoChristoffel Ω w (frameVec j) (![frameVec i, frameVec i, frameVec j] 1)) =
          ![frameVec i, rhoChristoffel Ω w (frameVec j) (frameVec i), frameVec j] := by
      ext l; fin_cases l <;> rfl
    have u2 : Function.update ![frameVec i, frameVec i, frameVec j] 2
        (rhoChristoffel Ω w (frameVec j) (![frameVec i, frameVec i, frameVec j] 2)) =
          ![frameVec i, frameVec i, rhoChristoffel Ω w (frameVec j) (frameVec j)] := by
      ext l; fin_cases l <;> rfl
    rw [u0, u1, u2]
  have hAlin : ∀ k l (X : ℂ), fderiv ℝ (fun x => aUp x k l) w X =
      fderiv ℝ (fun x => aUp x k l) w 1 * X.re + fderiv ℝ (fun x => aUp x k l) w I * X.im :=
    fun k l X => s05_clm_apply_eq _ X
  -- the identity with denominators cleared (a polynomial identity in the frame data)
  have key : poincareDensity Ω w ^ 4 * ∑ i : Fin 2,
      fderiv ℝ (fun x => poincareDensity Ω x ^ 2 * rhoDivA Ω aUp x i) w (frameVec i) =
        poincareDensity Ω w ^ 2 * ∑ i : Fin 2, ∑ j : Fin 2, rhoIterCovDeriv Ω 2 (lowerA Ω aUp) w
          ![frameVec j, frameVec i, frameVec i, frameVec j] := by
    simp only [Fin.sum_univ_two, mul_add, hQ, hQd, hNN]
    simp only [hN]
    simp only [hP4, s05_fderiv_density hd hp, hAlin _ _ (rhoChristoffel Ω w _ _)]
    simp only [lowerA, cvec, rhoChristoffel, frameVec, dotProduct, mulVec, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im, ha01, hs01]
    ring
  unfold rhoDDiv
  rw [eq_div_iff (by positivity)]
  apply mul_left_cancel₀ hρ2
  linear_combination poincareDensity Ω w ^ 4 * e1 + key

/-- Green helper (G3): `∇_i(a^{ij} ∇_j f) = (∇_i a^{ij}) ∇_j f + a^{ij} ∇_i∇_j f` for smooth
symmetric `a` and `f ∈ C²`. -/
theorem s05_gr_divB_grad {Ω U : Set ℂ} {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ} (hU : IsOpen U)
    (hl : ContDiffOn ℝ ∞ (poincareDensity Ω) U) (hpos : ∀ w ∈ U, 0 < poincareDensity Ω w)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun w => aUp w i j) U) (hsym : ∀ w ∈ U, (aUp w)ᵀ = aUp w)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 2 f U) {w : ℂ} (hw : w ∈ U) :
    rhoDivB Ω (fun x i => ∑ j : Fin 2, aUp x i j * fderiv ℝ f x (frameVec j)) w =
      ∑ j : Fin 2, rhoDivA Ω aUp w j * fderiv ℝ f w (frameVec j) +
        ∑ i : Fin 2, ∑ j : Fin 2, aUp w i j * rhoHess Ω f w ![frameVec i, frameVec j] := by
  have hn : U ∈ 𝓝 w := hU.mem_nhds hw
  have hd : DifferentiableAt ℝ (poincareDensity Ω) w :=
    (hl.contDiffAt hn).differentiableAt (by simp)
  have hp := hpos w hw
  have hρ2 : poincareDensity Ω w ^ 2 ≠ 0 := by positivity
  have had : ∀ i j, DifferentiableAt ℝ (fun x => aUp x i j) w := fun i j =>
    ((ha i j).contDiffAt hn).differentiableAt (by simp)
  have hdf : ∀ e : ℂ, DifferentiableAt ℝ (fun x => fderiv ℝ f x e) w := by
    intro e
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) w :=
      (hf.contDiffAt hn).fderiv_right (m := 1) (by norm_num)
    exact (h1.clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hV : ∀ i, DifferentiableAt ℝ
      (fun x => ∑ j : Fin 2, aUp x i j * fderiv ℝ f x (frameVec j)) w := by
    intro i
    simp only [Fin.sum_univ_two]
    exact ((had i 0).mul (hdf _)).add ((had i 1).mul (hdf _))
  have e1 := s05_gr_divB_eucl hV hd hp
  beta_reduce at e1
  -- symmetry of `a` near `w`, hence of its derivative
  have ha01 : fderiv ℝ (fun x => aUp x 0 1) w = fderiv ℝ (fun x => aUp x 1 0) w := by
    refine Filter.EventuallyEq.fderiv_eq (Filter.mem_of_superset hn fun x hx => ?_)
    have := congrFun (congrFun (hsym x hx) 1) 0
    simpa [Matrix.transpose_apply] using this
  have hs01 : aUp w 0 1 = aUp w 1 0 := by
    have := congrFun (congrFun (hsym w hw) 1) 0
    simpa [Matrix.transpose_apply] using this
  -- product rules
  have hprod : ∀ i (X : ℂ), fderiv ℝ (fun x => poincareDensity Ω x ^ 2 *
      (aUp x i 0 * fderiv ℝ f x (frameVec 0) + aUp x i 1 * fderiv ℝ f x (frameVec 1))) w X =
        2 * poincareDensity Ω w * fderiv ℝ (poincareDensity Ω) w X *
            (aUp w i 0 * fderiv ℝ f w (frameVec 0) + aUp w i 1 * fderiv ℝ f w (frameVec 1)) +
          poincareDensity Ω w ^ 2 * (fderiv ℝ (fun x => aUp x i 0) w X *
            fderiv ℝ f w (frameVec 0) +
              aUp w i 0 * fderiv ℝ (fun x => fderiv ℝ f x (frameVec 0)) w X +
            (fderiv ℝ (fun x => aUp x i 1) w X * fderiv ℝ f w (frameVec 1) +
              aUp w i 1 * fderiv ℝ (fun x => fderiv ℝ f x (frameVec 1)) w X)) := by
    intro i X
    rw [fderiv_fun_mul (hd.fun_pow 2) (((had i 0).fun_mul (hdf _)).fun_add ((had i 1).fun_mul (hdf _))),
      fderiv_fun_add ((had i 0).fun_mul (hdf _)) ((had i 1).fun_mul (hdf _)),
      fderiv_fun_mul (had i 0) (hdf _), fderiv_fun_mul (had i 1) (hdf _), fderiv_fun_pow 2 hd]
    simp only [add_apply, smul_apply, smul_eq_mul,
      nsmul_eq_mul]
    push_cast
    ring
  have hP4 : ∀ j k (X : ℂ), fderiv ℝ (fun x => poincareDensity Ω x ^ 4 * aUp x j k) w X =
      4 * poincareDensity Ω w ^ 3 * fderiv ℝ (poincareDensity Ω) w X * aUp w j k +
        poincareDensity Ω w ^ 4 * fderiv ℝ (fun x => aUp x j k) w X := by
    intro j k X
    rw [fderiv_fun_mul (hd.fun_pow 4) (had j k), fderiv_fun_pow 4 hd]
    simp only [add_apply, smul_apply, smul_eq_mul,
      nsmul_eq_mul]
    push_cast
    ring
  -- `∇a♭` in the frame
  have hcA : ∀ (X : ℂ) (j k : Fin 2), rhoCovDeriv Ω (lowerA Ω aUp) w ![X, frameVec j, frameVec k] =
      fderiv ℝ (fun x => poincareDensity Ω x ^ 4 * aUp x j k) w X -
        lowerA Ω aUp w ![rhoChristoffel Ω w X (frameVec j), frameVec k] -
        lowerA Ω aUp w ![frameVec j, rhoChristoffel Ω w X (frameVec k)] := by
    intro X j k
    have e : (fun x => lowerA Ω aUp x (Fin.tail ![X, frameVec j, frameVec k])) =
        fun x => poincareDensity Ω x ^ 4 * aUp x j k := by
      funext x
      have : Fin.tail ![X, frameVec j, frameVec k] = ![frameVec j, frameVec k] := by
        ext l; fin_cases l <;> rfl
      rw [this, s05_lowerA_frame]
    show fderiv ℝ (fun x => lowerA Ω aUp x (Fin.tail ![X, frameVec j, frameVec k])) w X -
      ∑ l : Fin 2, lowerA Ω aUp w (Function.update (Fin.tail ![X, frameVec j, frameVec k]) l
        (rhoChristoffel Ω w X (Fin.tail ![X, frameVec j, frameVec k] l))) = _
    rw [e, Fin.sum_univ_two]
    have u0 : Function.update (Fin.tail ![X, frameVec j, frameVec k]) 0
        (rhoChristoffel Ω w X (Fin.tail ![X, frameVec j, frameVec k] 0)) =
          ![rhoChristoffel Ω w X (frameVec j), frameVec k] := by
      ext l; fin_cases l <;> rfl
    have u1 : Function.update (Fin.tail ![X, frameVec j, frameVec k]) 1
        (rhoChristoffel Ω w X (Fin.tail ![X, frameVec j, frameVec k] 1)) =
          ![frameVec j, rhoChristoffel Ω w X (frameVec k)] := by
      ext l; fin_cases l <;> rfl
    rw [u0, u1]
    ring
  have hflin : ∀ X : ℂ, fderiv ℝ f w X = fderiv ℝ f w 1 * X.re + fderiv ℝ f w I * X.im :=
    fun X => s05_clm_apply_eq _ X
  apply mul_left_cancel₀ hρ2
  rw [e1]
  simp only [Fin.sum_univ_two, hprod]
  simp only [rhoDivA, Fin.sum_univ_two, hcA, hP4, s05_rhoHess_eq, s05_fderiv_density hd hp]
  simp only [hflin (rhoChristoffel Ω w _ _)]
  simp only [lowerA, cvec, rhoChristoffel, frameVec, dotProduct, mulVec, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    ha01, hs01]
  field_simp
  ring

/-- Green helper (G4): Leibniz rule `∇_i(g T^i) = (∂_i g) T^i + g ∇_i T^i`. -/
theorem s05_gr_divB_smul {Ω : Set ℂ} {g : ℂ → ℝ} {T : ℂ → Fin 2 → ℝ} {w : ℂ}
    (hg : DifferentiableAt ℝ g w) (hT : ∀ i, DifferentiableAt ℝ (fun x => T x i) w)
    (hd : DifferentiableAt ℝ (poincareDensity Ω) w) (hpos : 0 < poincareDensity Ω w) :
    rhoDivB Ω (fun x i => g x * T x i) w =
      ∑ i : Fin 2, fderiv ℝ g w (frameVec i) * T w i + g w * rhoDivB Ω T w := by
  have hB1 : lowerB Ω (fun x i => g x * T x i) = fun x u => g x * lowerB Ω T x u := by
    funext x u
    simp only [lowerB, dotProduct, Fin.sum_univ_two]
    ring
  have hBd : ∀ u, DifferentiableAt ℝ (fun x => lowerB Ω T x u) w := by
    intro u
    simp only [lowerB, dotProduct, Fin.sum_univ_two]
    exact (hd.pow 2).mul (((hT 0).mul_const _).add ((hT 1).mul_const _))
  have hρ : poincareDensity Ω w ^ 2 ≠ 0 := by positivity
  unfold rhoDivB
  rw [hB1, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, s05_covDeriv_smul_two hg hBd,
    s05_covDeriv_smul_two hg hBd, s05_lowerB_frame, s05_lowerB_frame]
  field_simp
  ring

/-- Green helper (G5): the pointwise Green identity
`z 𝓛u - u 𝓛*z = -∇_i V^i`, `V^i = z a^{ij}∇_j u - u a^{ij}∇_j z - u z ∇_j a^{ij} + u z b^i`
(sec05-upper.tex:150, proof of (5.8)). -/
theorem s05_gr_pointwise {Ω U : Set ℂ} {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ}
    {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ} (hU : IsOpen U)
    (hl : ContDiffOn ℝ ∞ (poincareDensity Ω) U) (hpos : ∀ w ∈ U, 0 < poincareDensity Ω w)
    (hop : IsSmoothOp U aUp bUp c) {u z : ℂ → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hz : ContDiffOn ℝ 2 z U) {w : ℂ} (hw : w ∈ U) :
    z w * ellOp Ω aUp bUp c u w - u w * ellOpAdj Ω aUp bUp c z w =
      -rhoDivB Ω (fun x i =>
        z x * ∑ j : Fin 2, aUp x i j * fderiv ℝ u x (frameVec j) -
          u x * ∑ j : Fin 2, aUp x i j * fderiv ℝ z x (frameVec j) -
          u x * z x * rhoDivA Ω aUp x i + u x * z x * bUp x i) w := by
  obtain ⟨ha, hb, -, hsym⟩ := hop
  have hn : ∀ x ∈ U, U ∈ 𝓝 x := fun x hx => hU.mem_nhds hx
  have hd : DifferentiableAt ℝ (poincareDensity Ω) w :=
    (hl.contDiffAt (hn w hw)).differentiableAt (by simp)
  have hp := hpos w hw
  have hud : DifferentiableAt ℝ u w := (hu.contDiffAt (hn w hw)).differentiableAt (by norm_num)
  have hzd : DifferentiableAt ℝ z w := (hz.contDiffAt (hn w hw)).differentiableAt (by norm_num)
  have hfd : ∀ {f : ℂ → ℝ}, ContDiffOn ℝ 2 f U → ∀ e : ℂ,
      DifferentiableAt ℝ (fun x => fderiv ℝ f x e) w := by
    intro f hf e
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) w :=
      (hf.contDiffAt (hn w hw)).fderiv_right (m := 1) (by norm_num)
    exact (h1.clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have had : ∀ i j, DifferentiableAt ℝ (fun x => aUp x i j) w := fun i j =>
    ((ha i j).contDiffAt (hn w hw)).differentiableAt (by simp)
  have hbd : ∀ i, DifferentiableAt ℝ (fun x => bUp x i) w := fun i =>
    ((hb i).contDiffAt (hn w hw)).differentiableAt (by simp)
  have hdA := s05_covDeriv_smooth hU hl hpos (s05_lowerA_smooth hl ha)
  have hDa : ∀ i, DifferentiableAt ℝ (fun x => rhoDivA Ω aUp x i) w := by
    intro i
    simp only [rhoDivA, Fin.sum_univ_two, div_eq_mul_inv]
    exact ((s05_slice_diff hU hdA hw _).fun_add (s05_slice_diff hU hdA hw _)).fun_mul
      ((hd.fun_pow 4).fun_inv (by positivity))
  have hgrad : ∀ {f : ℂ → ℝ}, ContDiffOn ℝ 2 f U → ∀ i, DifferentiableAt ℝ
      (fun x => ∑ j : Fin 2, aUp x i j * fderiv ℝ f x (frameVec j)) w := by
    intro f hf i
    simp only [Fin.sum_univ_two]
    exact ((had i 0).mul (hfd hf _)).add ((had i 1).mul (hfd hf _))
  -- additivity of the divergence
  have hlin : ∀ T T' : ℂ → Fin 2 → ℝ, (∀ i, DifferentiableAt ℝ (fun x => T x i) w) →
      (∀ i, DifferentiableAt ℝ (fun x => T' x i) w) → ∀ α : ℝ,
        rhoDivB Ω (fun x i => T x i + α * T' x i) w = rhoDivB Ω T w + α * rhoDivB Ω T' w := by
    intro T T' hT hT' α
    have hρ : poincareDensity Ω w ^ 2 ≠ 0 := by positivity
    have hS : ∀ i, DifferentiableAt ℝ (fun x => T x i + α * T' x i) w := fun i =>
      (hT i).add ((hT' i).const_mul α)
    have e1 := s05_gr_divB_eucl hS hd hp
    have e2 := s05_gr_divB_eucl hT hd hp
    have e3 := s05_gr_divB_eucl hT' hd hp
    have hsplit : ∀ i, fderiv ℝ (fun x => poincareDensity Ω x ^ 2 * (T x i + α * T' x i)) w
        (frameVec i) = fderiv ℝ (fun x => poincareDensity Ω x ^ 2 * T x i) w (frameVec i) +
          α * fderiv ℝ (fun x => poincareDensity Ω x ^ 2 * T' x i) w (frameVec i) := by
      intro i
      have h1 : (fun x => poincareDensity Ω x ^ 2 * (T x i + α * T' x i)) =
          fun x => poincareDensity Ω x ^ 2 * T x i + α * (poincareDensity Ω x ^ 2 * T' x i) := by
        funext x; ring
      have q1 : DifferentiableAt ℝ (fun x => poincareDensity Ω x ^ 2 * T x i) w :=
        (hd.pow 2).mul (hT i)
      have q2 : DifferentiableAt ℝ (fun x => poincareDensity Ω x ^ 2 * T' x i) w :=
        (hd.pow 2).mul (hT' i)
      rw [h1, fderiv_fun_add q1 (q2.const_mul α), fderiv_const_mul q2]
      simp
    simp only [hsplit, Fin.sum_univ_two] at e1 e2 e3
    apply mul_left_cancel₀ hρ
    linear_combination e1 - e2 - α * e3
  set V1 : ℂ → Fin 2 → ℝ := fun x i => ∑ j : Fin 2, aUp x i j * fderiv ℝ u x (frameVec j)
    with hV1
  set V2 : ℂ → Fin 2 → ℝ := fun x i => ∑ j : Fin 2, aUp x i j * fderiv ℝ z x (frameVec j)
    with hV2
  have hV1d : ∀ i, DifferentiableAt ℝ (fun x => V1 x i) w := hgrad hu
  have hV2d : ∀ i, DifferentiableAt ℝ (fun x => V2 x i) w := hgrad hz
  have huz : DifferentiableAt ℝ (fun x => u x * z x) w := hud.mul hzd
  -- the four pieces
  have k1 := s05_gr_divB_smul hzd hV1d hd hp
  have k2 := s05_gr_divB_smul hud hV2d hd hp
  have k3 := s05_gr_divB_smul huz hDa hd hp
  have k4 := s05_gr_divB_smul huz hbd hd hp
  have g1 : rhoDivB Ω V1 w = _ := s05_gr_divB_grad hU hl hpos ha hsym hu hw
  have g2 : rhoDivB Ω V2 w = _ := s05_gr_divB_grad hU hl hpos ha hsym hz hw
  have g3 := s05_gr_divB_divA hU hl hpos ha hsym hw
  beta_reduce at k3 k4
  have hd1 : ∀ i, DifferentiableAt ℝ (fun x => z x * V1 x i) w := fun i => hzd.mul (hV1d i)
  have hd2 : ∀ i, DifferentiableAt ℝ (fun x => u x * V2 x i) w := fun i => hud.mul (hV2d i)
  have hd3 : ∀ i, DifferentiableAt ℝ (fun x => u x * z x * rhoDivA Ω aUp x i) w := fun i =>
    huz.mul (hDa i)
  have hd4 : ∀ i, DifferentiableAt ℝ (fun x => u x * z x * bUp x i) w := fun i =>
    huz.mul (hbd i)
  have l1 := hlin (fun x i => z x * V1 x i - u x * V2 x i - u x * z x * rhoDivA Ω aUp x i)
    (fun x i => u x * z x * bUp x i)
    (fun i => ((hd1 i).sub (hd2 i)).sub (hd3 i)) hd4 1
  have l2 := hlin (fun x i => z x * V1 x i - u x * V2 x i) (fun x i => u x * z x * rhoDivA Ω aUp x i)
    (fun i => (hd1 i).sub (hd2 i)) hd3 (-1)
  have l3 := hlin (fun x i => z x * V1 x i) (fun x i => u x * V2 x i) hd1 hd2 (-1)
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at l1 l2 l3
  rw [l1, l2, l3, k1, k2, k3, k4, g1, g2, g3]
  have hsym01 : aUp w 0 1 = aUp w 1 0 := by
    have := congrFun (congrFun (hsym w hw) 1) 0
    simpa [Matrix.transpose_apply] using this
  have huz' : ∀ e, fderiv ℝ (fun x => u x * z x) w e = u w * fderiv ℝ z w e + z w * fderiv ℝ u w e := by
    intro e
    rw [fderiv_fun_mul hud hzd]
    simp only [add_apply, smul_apply, smul_eq_mul]
  simp only [ellOpAdj, ellOp, adjCoeffC, adjCoeffB, hV1, hV2, huz', Fin.sum_univ_two,
    Pi.sub_apply, Pi.smul_apply, hsym01]
  ring

/-- Green helper (G6): a function `C^n` on the compact closure of an open set has bounded
derivatives of order `≤ n` on the set (local Taylor series of `ContDiffWithinAt` plus a finite
subcover; no unique differentiability of `closure s` is needed). -/
theorem s05_gr_bdd {s : Set ℂ} (hs : IsOpen s) (hc : IsCompact (closure s)) {f : ℂ → ℝ}
    {n : ℕ} (hf : ContDiffOn ℝ n f (closure s)) {m : ℕ} (hm : m ≤ n) :
    ∃ M, ∀ w ∈ s, ‖iteratedFDeriv ℝ m f w‖ ≤ M := by
  -- local bound near each point of `closure s`, from a local Taylor series
  have hloc : ∀ x ∈ closure s, ∃ N ∈ 𝓝 x, ∃ B : ℝ, ∀ y ∈ N, y ∈ s →
      ‖iteratedFDeriv ℝ m f y‖ ≤ B := by
    intro x hx
    obtain ⟨u, hu, p, hp⟩ := contDiffWithinAt_nat.1 (hf x hx)
    rw [Set.insert_eq_of_mem hx] at hu
    have hxu : x ∈ u := mem_of_mem_nhdsWithin hx hu
    have hcont : ContinuousWithinAt (fun y => p y m) u x :=
      (hp.cont m (by exact_mod_cast hm)).continuousWithinAt hxu
    have h1 : ∀ᶠ y in 𝓝[u] x, ‖p y m‖ < ‖p x m‖ + 1 :=
      hcont.norm.eventually (gt_mem_nhds (lt_add_one _))
    rw [eventually_nhdsWithin_iff] at h1
    obtain ⟨V, hVo, hxV, hVu⟩ := mem_nhdsWithin.1 hu
    obtain ⟨W, hWsub, hWo, hxW⟩ := _root_.mem_nhds_iff.1 h1
    refine ⟨V ∩ W, Filter.inter_mem (hVo.mem_nhds hxV) (hWo.mem_nhds hxW), ‖p x m‖ + 1, ?_⟩
    intro y hyVW hys
    have hO : IsOpen (V ∩ W ∩ s) := (hVo.inter hWo).inter hs
    have hOu : V ∩ W ∩ s ⊆ u := fun z hz => hVu ⟨hz.1.1, subset_closure hz.2⟩
    have hyO : y ∈ V ∩ W ∩ s := ⟨hyVW, hys⟩
    have e1 := (hp.mono hOu).eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast hm)
      hO.uniqueDiffOn hyO
    rw [← iteratedFDerivWithin_of_isOpen m hO hyO, ← e1]
    exact (hWsub hyVW.2 (hOu hyO)).le
  choose! N hN B hB using hloc
  obtain ⟨t, htc, ht⟩ := hc.elim_nhds_subcover N hN
  refine ⟨∑ x ∈ t, |B x|, fun y hy => ?_⟩
  obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (ht (subset_closure hy))
  calc ‖iteratedFDeriv ℝ m f y‖ ≤ B x := hB x (htc x hxt) y hyx hy
    _ ≤ |B x| := le_abs_self _
    _ ≤ ∑ x ∈ t, |B x| := Finset.single_le_sum (fun z _ => abs_nonneg (B z)) hxt

/-- Green helper (G7): a function continuous on `closure D'`, with bounded derivative on
`D' = {ψ < 0}` and vanishing on `∂D'`, is `O(|ψ|)` (mean value along `∇ψ` to the boundary,
`∇ψ ≠ 0` on `{ψ = 0}`, compactness).  This replaces "`Φ = 0` on `∂D'`" in the divergence
theorem: `fderiv` at points of `∂D'` is a junk value (`u` is arbitrary outside `closure D'`), so
fields built from `fderiv u` are not `C¹` up to `∂D'`. -/
theorem s05_gr_vanish_le {D' : Set ℂ} {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hD' : D' = {w | ψ w < 0}) (hnd : ∀ w, ψ w = 0 → fderiv ℝ ψ w ≠ 0)
    (hc : IsCompact (closure D')) {f : ℂ → ℝ} (hf : ContinuousOn f (closure D'))
    (hdf : ∀ w ∈ D', DifferentiableAt ℝ f w) (hM : ∃ M, ∀ w ∈ D', ‖fderiv ℝ f w‖ ≤ M)
    (h0 : ∀ w ∈ frontier D', f w = 0) :
    ∃ C, ∀ w ∈ D', |f w| ≤ C * |ψ w| := by
  obtain ⟨M, hM⟩ := hM
  have hψc : Continuous ψ := hψ.continuous
  have hψd : ∀ x, DifferentiableAt ℝ ψ x := fun x => hψ.differentiable (by simp) x
  have hDo : IsOpen D' := hD' ▸ isOpen_lt hψc continuous_const
  have hS : IsClosed D'ᶜ := hDo.isClosed_compl
  have hne : (D'ᶜ).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
    rw [h, closure_univ] at hc
    exact noncompact_univ ℂ hc
  -- step 1: `|f w| ≤ M dist(w, D'ᶜ)`, mean value theorem towards a nearest point of `D'ᶜ`
  have hstep1 : ∀ w ∈ D', |f w| ≤ M * Metric.infDist w D'ᶜ := by
    intro w hw
    obtain ⟨p, hpS, hdp⟩ := hS.exists_infDist_eq_dist hne w
    have hball : Metric.ball w (Metric.infDist w D'ᶜ) ⊆ D' := fun z hz => by
      by_contra hz'
      exact Metric.notMem_of_dist_lt_infDist (x := w)
        (by rw [dist_comm]; exact Metric.mem_ball.1 hz) hz'
    have hd0 : 0 < Metric.infDist w D'ᶜ := by
      rw [hdp]
      exact dist_pos.2 fun h => hpS (h ▸ hw)
    have hcb : Metric.closedBall w (Metric.infDist w D'ᶜ) ⊆ closure D' := by
      rw [← closure_ball w hd0.ne']
      exact closure_mono hball
    have hpcl : p ∈ closure D' := hcb (Metric.mem_closedBall.2 (by rw [dist_comm, hdp]))
    have hp0 : f p = 0 := h0 p (by rw [hDo.frontier_eq]; exact ⟨hpcl, hpS⟩)
    have hdist : ∀ t : ℝ, 0 ≤ t → dist (w + t • (p - w)) w = t * Metric.infDist w D'ᶜ := by
      intro t ht
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht,
        ← dist_eq_norm, dist_comm, ← hdp]
    have hsegD : ∀ t ∈ Set.Ico (0 : ℝ) 1, w + t • (p - w) ∈ D' := by
      intro t ht
      apply hball
      rw [Metric.mem_ball, hdist t ht.1]
      exact mul_lt_of_lt_one_left hd0 ht.2
    have hgc : ContinuousOn (fun t : ℝ => f (w + t • (p - w))) (Set.Icc 0 1) := by
      refine hf.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
        fun t ht => hcb ?_
      rw [Metric.mem_closedBall, hdist t ht.1]
      exact mul_le_of_le_one_left hd0.le ht.2
    have hgd : ∀ t ∈ Set.Ico (0 : ℝ) 1, HasDerivWithinAt (fun t : ℝ => f (w + t • (p - w)))
        (fderiv ℝ f (w + t • (p - w)) (p - w)) (Set.Ici t) t := by
      intro t ht
      have h1 : HasDerivAt (fun t : ℝ => w + t • (p - w)) (p - w) t := by
        simpa using ((hasDerivAt_id t).smul_const (p - w)).const_add w
      exact ((hdf _ (hsegD t ht)).hasFDerivAt.comp_hasDerivAt t h1).hasDerivWithinAt
    have hgb : ∀ t ∈ Set.Ico (0 : ℝ) 1,
        ‖fderiv ℝ f (w + t • (p - w)) (p - w)‖ ≤ M * Metric.infDist w D'ᶜ := by
      intro t ht
      refine ((fderiv ℝ f _).le_opNorm _).trans ?_
      rw [← dist_eq_norm, dist_comm, ← hdp]
      exact mul_le_mul_of_nonneg_right (hM _ (hsegD t ht)) hd0.le
    have key := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd hgb 1
      (Set.right_mem_Icc.2 zero_le_one)
    have e1 : w + (1 : ℝ) • (p - w) = p := by simp
    have e0 : w + (0 : ℝ) • (p - w) = w := by simp
    beta_reduce at key
    rw [e1, e0, hp0, zero_sub, norm_neg, sub_zero, mul_one, Real.norm_eq_abs] at key
    exact key
  -- step 2: `dist(w, D'ᶜ) = O(|ψ w|)`, locally near each point of `closure D'`
  obtain ⟨q, hq⟩ := hne
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall 0
  have hdR : ∀ w ∈ D', Metric.infDist w D'ᶜ ≤ R + ‖q‖ := fun w hw => by
    refine (Metric.infDist_le_dist_of_mem hq).trans ((dist_le_norm_add_norm w q).trans ?_)
    have := hR (subset_closure hw)
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  have hle : closure D' ⊆ {x | ψ x ≤ 0} :=
    closure_minimal (fun x hx => by
      rw [hD'] at hx
      show ψ x ≤ 0
      exact le_of_lt hx)
      (isClosed_le hψc continuous_const)
  have hloc : ∀ p ∈ closure D', ∃ N ∈ 𝓝 p, ∃ C : ℝ, ∀ w ∈ N, w ∈ D' →
      Metric.infDist w D'ᶜ ≤ C * |ψ w| := by
    intro p hp
    have hp0 : ψ p ≤ 0 := hle hp
    rcases hp0.lt_or_eq with hlt | heq
    · -- an interior point: `|ψ|` is bounded below nearby
      refine ⟨{x | ψ x < ψ p / 2}, (isOpen_lt hψc continuous_const).mem_nhds
        (show ψ p < ψ p / 2 by linarith), 2 * (R + ‖q‖) / (-ψ p), fun w hw hwD => ?_⟩
      have hwn : ψ w < 0 := by rw [hD'] at hwD; exact hwD
      have hw2 : ψ w < ψ p / 2 := hw
      have hd := hdR w hwD
      have hRn : 0 ≤ R + ‖q‖ := Metric.infDist_nonneg.trans hd
      rw [abs_of_neg hwn, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_right hd (by linarith : 0 ≤ -ψ p),
        mul_le_mul_of_nonneg_left (by linarith : -ψ p ≤ -(2 * ψ w)) hRn]
    · -- a boundary point: move along a direction `e` with `dψ(e) > 0`
      have hg := hnd p heq
      obtain ⟨e0, he0⟩ : ∃ e, fderiv ℝ ψ p e ≠ 0 := by
        by_contra h
        exact hg (ContinuousLinearMap.ext fun e => by
          by_contra he
          exact h ⟨e, he⟩)
      obtain ⟨e, hκ⟩ : ∃ e, 0 < fderiv ℝ ψ p e := by
        rcases he0.lt_or_gt with h | h
        · exact ⟨-e0, by rw [map_neg]; linarith⟩
        · exact ⟨e0, h⟩
      have hL : 0 < ‖e‖ := norm_pos_iff.2 fun h => by
        rw [h, map_zero] at hκ
        exact lt_irrefl _ hκ
      have hcont : Continuous fun x => fderiv ℝ ψ x e :=
        (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
      obtain ⟨r, hr, hrb⟩ := Metric.continuous_iff.1 hcont p (fderiv ℝ ψ p e / 2) (by linarith)
      have hlow : ∀ x, dist x p < r → fderiv ℝ ψ p e / 2 < fderiv ℝ ψ x e := fun x hx => by
        have := hrb x hx
        rw [Real.dist_eq, abs_lt] at this
        linarith [this.1]
      set κ := fderiv ℝ ψ p e with hκdef
      refine ⟨Metric.ball p (r / 2) ∩ {x | |ψ x| < κ * r / (4 * ‖e‖)},
        Filter.inter_mem (Metric.ball_mem_nhds p (by linarith))
          ((isOpen_lt (continuous_abs.comp hψc) continuous_const).mem_nhds
            (show |ψ p| < κ * r / (4 * ‖e‖) by
              rw [heq, abs_zero]; exact div_pos (mul_pos hκ hr) (by positivity))),
        2 * ‖e‖ / κ, fun w hw hwD => ?_⟩
      obtain ⟨hwb, hwψ⟩ := hw
      have hwψ' : |ψ w| < κ * r / (4 * ‖e‖) := hwψ
      have hwn : ψ w < 0 := by rw [hD'] at hwD; exact hwD
      have habs : 0 < |ψ w| := abs_pos.2 hwn.ne
      set t1 := 2 * |ψ w| / κ with ht1
      have ht1p : 0 < t1 := div_pos (by linarith) hκ
      have ht1L : t1 * ‖e‖ < r / 2 := by
        rw [ht1, div_mul_eq_mul_div, div_lt_iff₀ hκ]
        have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * ‖e‖)).1 hwψ'
        nlinarith
      have hder : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ψ (w + t • e)) (fderiv ℝ ψ (w + t • e) e) t := by
        intro t
        have h1 : HasDerivAt (fun t : ℝ => w + t • e) e t := by
          simpa using ((hasDerivAt_id t).smul_const e).const_add w
        exact (hψd (w + t • e)).hasFDerivAt.comp_hasDerivAt t h1
      have hpos : 0 ≤ ψ (w + t1 • e) := by
        obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => ψ (w + t • e))
          (fun t => fderiv ℝ ψ (w + t • e) e) ht1p
          (hψc.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
          (fun t _ => hder t)
        have hξr : dist (w + ξ • e) p < r := by
          have h1 : dist (w + ξ • e) w = ξ * ‖e‖ := by
            rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
              abs_of_pos hξ.1]
          have h2 : ξ * ‖e‖ < t1 * ‖e‖ := mul_lt_mul_of_pos_right hξ.2 hL
          have h3 := Metric.mem_ball.1 hwb
          linarith [dist_triangle (w + ξ • e) w p]
        have h1 := hlow _ hξr
        rw [hξeq, lt_div_iff₀ (by linarith)] at h1
        simp only [zero_smul, add_zero, sub_zero] at h1
        have : κ / 2 * t1 = -ψ w := by
          rw [ht1, abs_of_neg hwn]
          field_simp
        linarith
      have hout : w + t1 • e ∈ D'ᶜ := by
        rw [hD']
        exact fun h => (not_lt.2 hpos) h
      calc Metric.infDist w D'ᶜ ≤ dist w (w + t1 • e) := Metric.infDist_le_dist_of_mem hout
        _ = t1 * ‖e‖ := by
          rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_pos ht1p]
        _ = 2 * ‖e‖ / κ * |ψ w| := by
          rw [ht1]
          field_simp
  choose! N hN C hC using hloc
  obtain ⟨t, htc, ht⟩ := hc.elim_nhds_subcover N hN
  refine ⟨M * ∑ p ∈ t, |C p|, fun w hw => ?_⟩
  obtain ⟨p, hpt, hwp⟩ := Set.mem_iUnion₂.1 (ht (subset_closure hw))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM w hw)
  have h2 : Metric.infDist w D'ᶜ ≤ (∑ p ∈ t, |C p|) * |ψ w| :=
    (hC p (htc p hpt) w hwp hw).trans (mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans (Finset.single_le_sum (fun z _ => abs_nonneg (C z)) hpt))
      (abs_nonneg _))
  calc |f w| ≤ M * Metric.infDist w D'ᶜ := hstep1 w hw
    _ ≤ M * ((∑ p ∈ t, |C p|) * |ψ w|) := mul_le_mul_of_nonneg_left h2 hM0
    _ = M * (∑ p ∈ t, |C p|) * |ψ w| := by ring

/-- Green helper (G8): the divergence theorem with vanishing boundary values,
`∫_{D'} ∂_i Φ^i = 0` for `Φ ∈ C¹(D')` with integrable divergence and `|Φ| = O(|ψ|)`.
Cutoff `η_ε = smoothTransition(-ψ/ε - 1)`, integration by parts
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`, and dominated convergence (the cutoff
term is bounded by `‖smoothTransition'‖_∞ ‖∇ψ‖_∞ · 2C` on the strip `{-2ε ≤ ψ ≤ -ε}`). -/
theorem s05_gr_div_zero {D' : Set ℂ} {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hD' : D' = {w | ψ w < 0}) (hc : IsCompact (closure D')) {Φ : Fin 2 → ℂ → ℝ}
    (hΦ : ∀ i, ContDiffOn ℝ 1 (Φ i) D')
    (hint : IntegrableOn (fun w => fderiv ℝ (Φ 0) w 1 + fderiv ℝ (Φ 1) w I) D')
    (hC : ∃ C, ∀ i, ∀ w ∈ D', |Φ i w| ≤ C * |ψ w|) :
    ∫ w in D', (fderiv ℝ (Φ 0) w 1 + fderiv ℝ (Φ 1) w I) = 0 := by
  obtain ⟨C, hC⟩ := hC
  have hψc : Continuous ψ := hψ.continuous
  have hψ1 : ContDiff ℝ 1 ψ := by simpa using contDiff_infty.1 hψ 1
  have hψd : ∀ x, DifferentiableAt ℝ ψ x := fun x => hψ1.differentiable (by norm_num) x
  have hDo : IsOpen D' := hD' ▸ isOpen_lt hψc continuous_const
  have hDm : MeasurableSet D' := hDo.measurableSet
  have hmem : ∀ {x}, x ∈ D' ↔ ψ x < 0 := fun {x} => by rw [hD']; rfl
  have hfin : volume D' ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono subset_closure) hc.measure_lt_top).ne
  haveI : IsFiniteMeasure (volume.restrict D') :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hfin⟩
  have hΦd : ∀ i, ∀ x ∈ D', DifferentiableAt ℝ (Φ i) x := fun i x hx =>
    ((hΦ i).differentiableOn (by norm_num) x hx).differentiableAt (hDo.mem_nhds hx)
  -- bounds: `‖dψ‖ ≤ K` on `closure D'`, `|smoothTransition'| ≤ B`
  obtain ⟨K, hK⟩ := hc.exists_bound_of_continuousOn
    (hψ1.continuous_fderiv (by simp)).continuousOn
  have hst1 : ContDiff ℝ 1 Real.smoothTransition := by
    exact_mod_cast (Real.smoothTransition.contDiff (n := 1))
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hst1.continuous_deriv le_rfl).continuousOn
  have hB0 : ∀ s, s ∉ Set.Icc (0 : ℝ) 1 → deriv Real.smoothTransition s = 0 := by
    intro s hs
    rcases not_and_or.1 hs with h | h
    · have e : Real.smoothTransition =ᶠ[𝓝 s] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds (not_le.1 h)] with y hy
        exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
      rw [e.deriv_eq, deriv_const]
    · have e : Real.smoothTransition =ᶠ[𝓝 s] fun _ => 1 := by
        filter_upwards [Ioi_mem_nhds (not_le.1 h)] with y hy
        exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
      rw [e.deriv_eq, deriv_const]
  have hBs : ∀ s, |deriv Real.smoothTransition s| ≤ |B| := by
    intro s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
    · exact (by simpa [Real.norm_eq_abs] using hB s hs : |deriv Real.smoothTransition s| ≤ B).trans
        (le_abs_self _)
    · rw [hB0 s hs, abs_zero]; exact abs_nonneg _
  -- the cutoffs `η ε = smoothTransition (-ψ/ε - 1)`
  obtain ⟨η, hη⟩ : ∃ η : ℝ → ℂ → ℝ,
      η = fun ε y => Real.smoothTransition (-ε⁻¹ * ψ y - 1) := ⟨_, rfl⟩
  have hηv : ∀ ε y, η ε y = Real.smoothTransition (-ε⁻¹ * ψ y - 1) := fun ε y => by rw [hη]
  have hηc : ∀ ε, ContDiff ℝ 1 (η ε) := fun ε => by
    rw [hη]
    exact hst1.comp ((contDiff_const.mul hψ1).sub contDiff_const)
  have hηf : ∀ ε x, HasFDerivAt (η ε)
      (deriv Real.smoothTransition (-ε⁻¹ * ψ x - 1) • ((-ε⁻¹) • fderiv ℝ ψ x)) x := by
    intro ε x
    rw [hη]
    exact (hst1.differentiable (by norm_num) _).hasDerivAt.comp_hasFDerivAt x
      (((hψd x).hasFDerivAt.const_mul (-ε⁻¹)).sub_const 1)
  have hηd : ∀ ε x v, fderiv ℝ (η ε) x v =
      deriv Real.smoothTransition (-ε⁻¹ * ψ x - 1) * (-ε⁻¹ * fderiv ℝ ψ x v) := by
    intro ε x v
    rw [(hηf ε x).fderiv]
    simp only [smul_apply, smul_eq_mul]
  have hη01 : ∀ ε y, |η ε y| ≤ 1 := fun ε y => by
    rw [hηv, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  -- `η ε = 0` on `{ψ > -ε}`
  have hη0 : ∀ ε > 0, ∀ y, -ε < ψ y → η ε y = 0 := by
    intro ε hε y hy
    rw [hηv]
    apply Real.smoothTransition.zero_of_nonpos
    have e : ε * (-ε⁻¹ * ψ y - 1) = -ψ y - ε := by field_simp
    by_contra h
    nlinarith [mul_pos hε (not_le.1 h)]
  -- the cut-off fields are `C¹` with compact support
  have hGc : ∀ ε > 0, ∀ i, ContDiff ℝ 1 (fun y => η ε y * Φ i y) := by
    intro ε hε i
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ D'
    · exact (hηc ε).contDiffAt.mul ((hΦ i).contDiffAt (hDo.mem_nhds hx))
    · have hx0 : 0 ≤ ψ x := not_lt.1 fun h => hx (hmem.2 h)
      refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_const hψc).mem_nhds
        (show -ε < ψ x by linarith)] with y hy
      rw [hη0 ε hε y hy, zero_mul]
  have hGs : ∀ ε > 0, ∀ i, HasCompactSupport (fun y => η ε y * Φ i y) := by
    intro ε hε i
    refine HasCompactSupport.intro hc fun x hx => ?_
    have hx0 : 0 ≤ ψ x := not_lt.1 fun h => hx (subset_closure (hmem.2 h))
    rw [hη0 ε hε x (by linarith), zero_mul]
  -- `∫ ∂_v (η Φ_i) = 0`
  have hzero : ∀ ε > 0, ∀ i (v : ℂ), ∫ x, fderiv ℝ (fun y => η ε y * Φ i y) x v = 0 := by
    intro ε hε i v
    have hG := hGc ε hε i
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun y => η ε y * Φ i y) (g := fun _ => (1 : ℝ)) (v := v)
      (by simpa using ((hG.continuous_fderiv (by simp)).clm_apply
        continuous_const).integrable_of_hasCompactSupport ((hGs ε hε i).fderiv_apply (𝕜 := ℝ) v))
      (by simp)
      (by simpa using hG.continuous.integrable_of_hasCompactSupport (hGs ε hε i))
      (fun x _ => hG.differentiable (by norm_num) x) (fun x _ => differentiableAt_const _)
    simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, mul_zero,
      MeasureTheory.integral_zero, mul_one] at h
    linarith
  -- the derivative of `η Φ_i` on `D'` and off `D'`
  have hexp : ∀ ε, ∀ i, ∀ x ∈ D', ∀ v, fderiv ℝ (fun y => η ε y * Φ i y) x v =
      η ε x * fderiv ℝ (Φ i) x v + Φ i x * fderiv ℝ (η ε) x v := by
    intro ε i x hx v
    rw [fderiv_fun_mul ((hηc ε).differentiable (by norm_num) x) (hΦd i x hx)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hoff : ∀ ε > 0, ∀ i, ∀ x ∉ D', fderiv ℝ (fun y => η ε y * Φ i y) x = 0 := by
    intro ε hε i x hx
    have hx0 : 0 ≤ ψ x := not_lt.1 fun h => hx (hmem.2 h)
    have e : (fun y => η ε y * Φ i y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const hψc).mem_nhds
        (show -ε < ψ x by linarith)] with y hy
      rw [hη0 ε hε y hy, zero_mul]
    rw [e.fderiv_eq]
    simp
  -- the two pieces on `D'`
  set dv : ℂ → ℝ := fun w => fderiv ℝ (Φ 0) w 1 + fderiv ℝ (Φ 1) w I with hdv
  have hA : ∀ ε, IntegrableOn (fun x => η ε x * dv x) D' := fun ε =>
    Integrable.bdd_mul (c := 1) hint (hηc ε).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hη01 ε y)
  have hAR : ∀ ε > 0, IntegrableOn (fun x => η ε x * dv x +
      (Φ 0 x * fderiv ℝ (η ε) x 1 + Φ 1 x * fderiv ℝ (η ε) x I)) D' ∧
      ∫ x in D', (η ε x * dv x + (Φ 0 x * fderiv ℝ (η ε) x 1 + Φ 1 x * fderiv ℝ (η ε) x I)) = 0 := by
    intro ε hε
    have hi : ∀ i (v : ℂ), Integrable (fun x => fderiv ℝ (fun y => η ε y * Φ i y) x v) :=
      fun i v => ((hGc ε hε i).continuous_fderiv (by simp) |>.clm_apply
        continuous_const).integrable_of_hasCompactSupport ((hGs ε hε i).fderiv_apply (𝕜 := ℝ) v)
    have heq : EqOn (fun x => fderiv ℝ (fun y => η ε y * Φ 0 y) x 1 +
        fderiv ℝ (fun y => η ε y * Φ 1 y) x I)
        (fun x => η ε x * dv x + (Φ 0 x * fderiv ℝ (η ε) x 1 + Φ 1 x * fderiv ℝ (η ε) x I))
        D' := by
      intro x hx
      simp only [hexp ε 0 x hx, hexp ε 1 x hx, hdv]
      ring
    refine ⟨((hi 0 1).add (hi 1 I)).integrableOn.congr_fun heq hDm, ?_⟩
    rw [← setIntegral_congr_fun hDm heq, setIntegral_eq_integral_of_forall_compl_eq_zero
      fun x hx => by simp [hoff ε hε 0 x hx, hoff ε hε 1 x hx],
      integral_add (hi 0 1) (hi 1 I), hzero ε hε 0 1, hzero ε hε 1 I, add_zero]
  -- the cut-off term is bounded uniformly in `ε`
  have hterm : ∀ ε > 0, ∀ i, ∀ x ∈ D', ∀ v : ℂ, ‖v‖ = 1 →
      |Φ i x * fderiv ℝ (η ε) x v| ≤ 2 * |C| * |B| * |K| := by
    intro ε hε i x hx v hv
    have hε0 : ε ≠ 0 := hε.ne'
    have hxn : ψ x < 0 := hmem.1 hx
    rw [hηd]
    by_cases hs : -ε⁻¹ * ψ x - 1 ∈ Set.Icc (0 : ℝ) 1
    · have e : ε * (-ε⁻¹ * ψ x - 1) = -ψ x - ε := by field_simp
      have hψ2 : |ψ x| ≤ 2 * ε := by
        rw [abs_of_neg hxn]
        nlinarith [mul_le_mul_of_nonneg_left hs.2 hε.le]
      have h1 : |Φ i x| ≤ |C| * (2 * ε) :=
        (hC i x hx).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hψ2 (abs_nonneg _)))
      have h3 : |fderiv ℝ ψ x v| ≤ |K| := by
        have := (fderiv ℝ ψ x).le_opNorm v
        rw [hv, mul_one, Real.norm_eq_abs] at this
        exact this.trans ((hK x (subset_closure hx)).trans (le_abs_self _))
      rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_inv, abs_of_pos hε]
      have h4 := mul_le_mul h1 (mul_le_mul (hBs (-ε⁻¹ * ψ x - 1)) (mul_le_mul_of_nonneg_left h3
        (inv_nonneg.2 hε.le)) (mul_nonneg (inv_nonneg.2 hε.le) (abs_nonneg _)) (abs_nonneg _))
        (mul_nonneg (abs_nonneg _) (mul_nonneg (inv_nonneg.2 hε.le) (abs_nonneg _)))
        (mul_nonneg (abs_nonneg _) (by linarith))
      calc _ ≤ |C| * (2 * ε) * (|B| * (ε⁻¹ * |K|)) := h4
        _ = 2 * |C| * |B| * |K| := by field_simp
    · rw [hB0 _ hs, zero_mul, mul_zero, abs_zero]
      positivity
  -- pointwise limits: for `ε < -ψ x / 2` the cutoff is `1` with derivative `0` at `x`
  have hlimit : ∀ x ∈ D', ∀ ε > 0, ε < -ψ x / 2 →
      η ε x = 1 ∧ ∀ v, fderiv ℝ (η ε) x v = 0 := by
    intro x hx ε hε hlt
    have e : ε * (-ε⁻¹ * ψ x - 1) = -ψ x - ε := by field_simp
    have h1 : 1 < -ε⁻¹ * ψ x - 1 := by
      by_contra h
      nlinarith [mul_le_mul_of_nonneg_left (not_lt.1 h) hε.le]
    refine ⟨by rw [hηv]; exact Real.smoothTransition.one_of_one_le h1.le, fun v => ?_⟩
    rw [hηd, hB0 _ fun h => absurd h.2 (not_le.2 h1), zero_mul]
  set εn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεn
  have hεpos : ∀ n, 0 < εn n := fun n => by positivity
  have hεlim : Tendsto εn atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hev : ∀ x ∈ D', ∀ᶠ n in atTop, εn n < -ψ x / 2 := fun x hx =>
    (tendsto_order.1 hεlim).2 _ (by linarith [hmem.1 hx])
  have hlimA : Tendsto (fun n => ∫ x in D', η (εn n) x * dv x) atTop (𝓝 (∫ x in D', dv x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖dv x‖)
      (fun n => (hA (εn n)).aestronglyMeasurable) hint.norm (fun n => ?_) ?_
    · refine Filter.Eventually.of_forall fun y => ?_
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by rw [Real.norm_eq_abs]; exact hη01 _ y)
    · refine (ae_restrict_iff' hDm).2 (Filter.Eventually.of_forall fun x hx => ?_)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x hx] with n hn
      rw [(hlimit x hx (εn n) (hεpos n) hn).1, one_mul]
  have hR : ∀ n, IntegrableOn (fun x => Φ 0 x * fderiv ℝ (η (εn n)) x 1 +
      Φ 1 x * fderiv ℝ (η (εn n)) x I) D' := fun n => by
    have := ((hAR (εn n) (hεpos n)).1).sub (hA (εn n))
    refine this.congr_fun (fun x _ => ?_) hDm
    simp only [Pi.sub_apply]
    ring
  have hlimR : Tendsto (fun n => ∫ x in D', (Φ 0 x * fderiv ℝ (η (εn n)) x 1 +
      Φ 1 x * fderiv ℝ (η (εn n)) x I)) atTop (𝓝 (∫ x in D', (0 : ℝ))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 2 * (2 * |C| * |B| * |K|))
      (fun n => (hR n).aestronglyMeasurable) (integrable_const _) (fun n => ?_) ?_
    · refine (ae_restrict_iff' hDm).2 (Filter.Eventually.of_forall fun x hx => ?_)
      rw [Real.norm_eq_abs]
      have h1 := hterm (εn n) (hεpos n) 0 x hx 1 (by simp)
      have h2 := hterm (εn n) (hεpos n) 1 x hx I (by simp)
      exact (abs_add_le _ _).trans (by linarith)
    · refine (ae_restrict_iff' hDm).2 (Filter.Eventually.of_forall fun x hx => ?_)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x hx] with n hn
      have h := (hlimit x hx (εn n) (hεpos n) hn).2
      rw [h 1, h I, mul_zero, mul_zero, add_zero]
  have hsplit : ∀ n, ∫ x in D', (Φ 0 x * fderiv ℝ (η (εn n)) x 1 +
      Φ 1 x * fderiv ℝ (η (εn n)) x I) = -∫ x in D', η (εn n) x * dv x := by
    intro n
    have h := (hAR (εn n) (hεpos n)).2
    rw [integral_add (hA (εn n)) (hR n)] at h
    linarith
  simp only [hsplit, MeasureTheory.integral_zero] at hlimR
  have := tendsto_nhds_unique hlimA (by simpa using hlimR.neg)
  simpa [hdv] using this

/-- Green helper (G9): the coefficients of `𝓛*` and `∇_j a^{ij}` are continuous on `U`. -/
theorem s05_gr_coeff_cont {Ω U : Set ℂ} {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ}
    {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ} (hU : IsOpen U)
    (hl : ContDiffOn ℝ ∞ (poincareDensity Ω) U) (hpos : ∀ w ∈ U, 0 < poincareDensity Ω w)
    (hop : IsSmoothOp U aUp bUp c) :
    ContinuousOn (adjCoeffC Ω aUp bUp c) U ∧ (∀ i, ContinuousOn (fun w => adjCoeffB Ω aUp bUp w i) U) ∧
      (∀ i, ContinuousOn (fun w => rhoDivA Ω aUp w i) U) ∧ ContinuousOn (logDensityGrad Ω) U := by
  obtain ⟨ha, hb, hc, -⟩ := hop
  have hfst : ContDiffOn ℝ ∞ (fun p : ℂ × (Fin 1 → ℂ) => p.1) (U ×ˢ univ) := contDiffOn_fst
  have hm : MapsTo (fun p : ℂ × (Fin 1 → ℂ) => p.1) (U ×ˢ univ) U := fun p hp => hp.1
  have hB : ContDiffOn ℝ ∞ (fun p : ℂ × (Fin 1 → ℂ) => lowerB Ω bUp p.1 p.2) (U ×ˢ univ) := by
    have hcv : ∀ i : Fin 2,
        ContDiffOn ℝ ∞ (fun p : ℂ × (Fin 1 → ℂ) => cvec (p.2 0) i) (U ×ˢ univ) :=
      fun i => ((contDiff_apply ℝ (fun _ => ℝ) i).comp (s05_cvec_contDiff.comp
        ((contDiff_apply ℝ (fun _ => ℂ) 0).comp contDiff_snd))).contDiffOn
    simp only [lowerB, dotProduct]
    exact ((hl.comp hfst hm).pow 2).mul
      (ContDiffOn.sum fun i _ => ((hb i).comp hfst hm).mul (hcv i))
  have h1A := s05_covDeriv_smooth hU hl hpos (s05_lowerA_smooth hl ha)
  have h2A := s05_covDeriv_smooth hU hl hpos h1A
  have h1B := s05_covDeriv_smooth hU hl hpos hB
  have hsl : ∀ {k : ℕ} {T : TensorField k},
      ContDiffOn ℝ ∞ (fun p : ℂ × (Fin k → ℂ) => T p.1 p.2) (U ×ˢ univ) → ∀ v : Fin k → ℂ,
        ContinuousOn (fun x => T x v) U := fun hT v =>
    (hT.comp (contDiffOn_id.prodMk contDiffOn_const) fun x hx => ⟨hx, mem_univ _⟩).continuousOn
  have hρ : ∀ k : ℕ, ContinuousOn (fun x => poincareDensity Ω x ^ k) U := fun k =>
    hl.continuousOn.pow k
  have hne : ∀ k : ℕ, ∀ x ∈ U, poincareDensity Ω x ^ k ≠ 0 := fun k x hx =>
    pow_ne_zero _ (hpos x hx).ne'
  have hDA : ∀ i, ContinuousOn (fun w => rhoDivA Ω aUp w i) U := by
    intro i
    show ContinuousOn (fun w => (∑ j : Fin 2,
      rhoCovDeriv Ω (lowerA Ω aUp) w ![frameVec j, frameVec i, frameVec j]) /
        poincareDensity Ω w ^ 4) U
    exact (continuousOn_finsetSum _ fun j _ => hsl h1A _).div (hρ 4) (hne 4)
  have hDD : ContinuousOn (rhoDDiv Ω aUp) U := by
    show ContinuousOn (fun w => (∑ i : Fin 2, ∑ j : Fin 2,
      rhoCovDeriv Ω (rhoCovDeriv Ω (lowerA Ω aUp)) w
        ![frameVec j, frameVec i, frameVec i, frameVec j]) / poincareDensity Ω w ^ 4) U
    exact (continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
      hsl h2A _).div (hρ 4) (hne 4)
  have hDB : ContinuousOn (rhoDivB Ω bUp) U := by
    show ContinuousOn (fun w => (∑ i : Fin 2,
      rhoCovDeriv Ω (lowerB Ω bUp) w ![frameVec i, frameVec i]) / poincareDensity Ω w ^ 2) U
    exact (continuousOn_finsetSum _ fun i _ => hsl h1B _).div (hρ 2) (hne 2)
  refine ⟨?_, fun i => ?_, hDA, (s05_logDensityGrad_smooth hU hl hpos).continuousOn⟩
  · show ContinuousOn (fun w => c w - rhoDDiv Ω aUp w + rhoDivB Ω bUp w) U
    exact (hc.continuousOn.sub hDD).add hDB
  · have e : (fun w => adjCoeffB Ω aUp bUp w i) = fun w => 2 * rhoDivA Ω aUp w i - bUp w i := by
      funext w
      simp [adjCoeffB, nsmul_eq_mul]
    rw [e]
    exact (continuousOn_const.mul (hDA i)).sub (hb i).continuousOn

/-- Green helper (G10): for `u ∈ C²(\overline{D'})`, `D' ⋐ D`, both `𝓛u` and `𝓛*u` are bounded
on `D'` (G6 for `∇u, ∇²u`, G9 and compactness for the coefficients).  Needed for the
integrability of both sides of (5.8): otherwise one Bochner integral is a junk `0`. -/
theorem s05_gr_ops_bdd {Ω D D' : Set ℂ} {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ}
    {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ} (hD : IsOpen D)
    (hl : ContDiffOn ℝ ∞ (poincareDensity Ω) D) (hpos : ∀ w ∈ D, 0 < poincareDensity Ω w)
    (hop : IsSmoothOp D aUp bUp c) (hD' : IsSmoothRelCompactIn D' D) {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ 2 u (closure D')) :
    ∃ M, ∀ w ∈ D', |ellOp Ω aUp bUp c u w| ≤ M ∧ |ellOpAdj Ω aUp bUp c u w| ≤ M := by
  obtain ⟨hDo, hKc, hKD, -⟩ := hD'
  obtain ⟨hcC', hcB', -, hG⟩ := s05_gr_coeff_cont hD hl hpos hop
  obtain ⟨ha, hb, hc, -⟩ := hop
  have hsub : D' ⊆ closure D' := subset_closure
  have hbd : ∀ {g : ℂ → ℝ}, ContinuousOn g D → ∃ C, ∀ x ∈ D', |g x| ≤ C := by
    intro g hg
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hg.mono hKD)
    exact ⟨C, fun x hx => by simpa [Real.norm_eq_abs] using hC x (hsub hx)⟩
  have hfr : ∀ i : Fin 2, ‖frameVec i‖ = 1 := by
    intro i; fin_cases i <;> simp [frameVec]
  choose Ca hCa using fun i j => hbd (ha i j).continuousOn
  choose Cb hCb using fun i => hbd (hb i).continuousOn
  obtain ⟨Cc, hCc⟩ := hbd hc.continuousOn
  choose Cb' hCb' using fun i => hbd (hcB' i)
  obtain ⟨Cc', hCc'⟩ := hbd hcC'
  -- the Christoffel symbols on the frame are bounded
  have hΓc : ∀ X Y : ℂ, ContinuousOn (fun w => rhoChristoffel Ω w X Y) D := by
    intro X Y
    have h1 : ContinuousOn (fun w => conj (logDensityGrad Ω w)) D :=
      Complex.continuous_conj.comp_continuousOn hG
    have hre : ∀ Z : ℂ,
        ContinuousOn (fun w => (((conj (logDensityGrad Ω w) * Z).re : ℝ) : ℂ)) D :=
      fun Z => Complex.continuous_ofReal.comp_continuousOn
        (Complex.continuous_re.comp_continuousOn (h1.mul continuousOn_const))
    show ContinuousOn (fun w => (((conj (logDensityGrad Ω w) * X).re : ℝ) : ℂ) * Y +
      (((conj (logDensityGrad Ω w) * Y).re : ℝ) : ℂ) * X -
        (((conj X * Y).re : ℝ) : ℂ) * logDensityGrad Ω w) D
    exact (((hre X).mul continuousOn_const).add ((hre Y).mul continuousOn_const)).sub
      (continuousOn_const.mul hG)
  have hΓb : ∀ i j : Fin 2, ∃ C, ∀ w ∈ D',
      ‖rhoChristoffel Ω w (frameVec i) (frameVec j)‖ ≤ C := by
    intro i j
    obtain ⟨C, hC⟩ :=
      hKc.exists_bound_of_continuousOn ((hΓc (frameVec i) (frameVec j)).mono hKD)
    exact ⟨C, fun w hw => hC w (hsub hw)⟩
  choose CΓ hCΓ using hΓb
  -- `u`, `∇u`, `∇²u` are bounded on `D'` (G6)
  have hu' : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) u (closure D') := by exact_mod_cast hu
  obtain ⟨C0, hC0⟩ := s05_gr_bdd hDo hKc hu' (m := 0) (by norm_num)
  obtain ⟨C1, hC1⟩ := s05_gr_bdd hDo hKc hu' (m := 1) (by norm_num)
  obtain ⟨C2, hC2⟩ := s05_gr_bdd hDo hKc hu' (m := 2) le_rfl
  have hu0 : ∀ w ∈ D', |u w| ≤ C0 := fun w hw => by
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hC0 w hw
  have hu1 : ∀ w ∈ D', ‖fderiv ℝ u w‖ ≤ C1 := fun w hw => by
    simpa using hC1 w hw
  have hu2 : ∀ w ∈ D', ‖fderiv ℝ (fderiv ℝ u) w‖ ≤ C2 := fun w hw => by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact hC2 w hw
  have hH : ∀ w ∈ D', ∀ i j,
      |rhoHess Ω u w ![frameVec i, frameVec j]| ≤ C2 + C1 * CΓ i j := by
    intro w hw i j
    have hn : closure D' ∈ 𝓝 w := Filter.mem_of_superset (hDo.mem_nhds hw) hsub
    have hdd : DifferentiableAt ℝ (fderiv ℝ u) w :=
      ((hu.contDiffAt hn).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have e : fderiv ℝ (fun x => fderiv ℝ u x (frameVec j)) w (frameVec i) =
        fderiv ℝ (fderiv ℝ u) w (frameVec i) (frameVec j) := by
      have h := fderiv_clm_apply (c := fderiv ℝ u) (u := fun _ : ℂ => frameVec j) hdd
        (differentiableAt_const _)
      beta_reduce at h
      rw [h]
      simp
    rw [s05_rhoHess_eq, e]
    have t1 : |fderiv ℝ (fderiv ℝ u) w (frameVec i) (frameVec j)| ≤ C2 := by
      have := (fderiv ℝ (fderiv ℝ u) w).le_opNorm₂ (frameVec i) (frameVec j)
      rw [hfr, hfr, mul_one, mul_one, Real.norm_eq_abs] at this
      exact this.trans (hu2 w hw)
    have t2 : |fderiv ℝ u w (rhoChristoffel Ω w (frameVec i) (frameVec j))| ≤ C1 * CΓ i j := by
      have := (fderiv ℝ u w).le_opNorm (rhoChristoffel Ω w (frameVec i) (frameVec j))
      rw [Real.norm_eq_abs] at this
      exact this.trans (mul_le_mul (hu1 w hw) (hCΓ i j w hw) (norm_nonneg _)
        ((norm_nonneg _).trans (hu1 w hw)))
    rw [abs_le] at t1 t2 ⊢
    constructor <;> linarith [t1.1, t1.2, t2.1, t2.2]
  have hmb : ∀ x y X Y : ℝ, |x| ≤ X → |y| ≤ Y → |x * y| ≤ X * Y := fun x y X Y hx hy => by
    rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)
  -- a bound for `𝓛` with any bounded lower order coefficients
  have hgen : ∀ (b' : ℂ → Fin 2 → ℝ) (c' : ℂ → ℝ) (B : Fin 2 → ℝ) (C : ℝ),
      (∀ i, ∀ w ∈ D', |b' w i| ≤ B i) → (∀ w ∈ D', |c' w| ≤ C) → ∀ w ∈ D',
        |ellOp Ω aUp b' c' u w| ≤ C * C0 +
          (∑ i : Fin 2, ∑ j : Fin 2, Ca i j * (C2 + C1 * CΓ i j)) + ∑ i : Fin 2, B i * C1 := by
    intro b' c' B C hB hC w hw
    have a1 := abs_le.1 (hmb _ _ _ _ (hC w hw) (hu0 w hw))
    have a2 := fun i j => abs_le.1 (hmb _ _ _ _ (hCa i j w hw) (hH w hw i j))
    have a3 : ∀ i, -(B i * C1) ≤ b' w i * fderiv ℝ u w (frameVec i) ∧
        b' w i * fderiv ℝ u w (frameVec i) ≤ B i * C1 := fun i => abs_le.1
      (hmb _ _ _ _ (hB i w hw) (by
        have := (fderiv ℝ u w).le_opNorm (frameVec i)
        rw [hfr, mul_one, Real.norm_eq_abs] at this
        exact this.trans (hu1 w hw)))
    simp only [ellOp, Fin.sum_univ_two]
    rw [abs_le]
    constructor <;> linarith [a1.1, a1.2, (a2 0 0).1, (a2 0 0).2, (a2 0 1).1, (a2 0 1).2,
      (a2 1 0).1, (a2 1 0).2, (a2 1 1).1, (a2 1 1).2, (a3 0).1, (a3 0).2, (a3 1).1, (a3 1).2]
  have hA := hgen bUp c Cb Cc hCb hCc
  have hA' := hgen (adjCoeffB Ω aUp bUp) (adjCoeffC Ω aUp bUp c) Cb' Cc' hCb' hCc'
  exact ⟨max _ _, fun w hw => ⟨(hA w hw).trans (le_max_left _ _),
    (hA' w hw).trans (le_max_right _ _)⟩⟩

/-- **(5.8)** (`eq:green-formula`, sec05-upper.tex:150).  If `𝓛` has smooth symmetric coefficients
on `D`, `D' ⋐ D` has smooth boundary and `u, z ∈ C²(\overline{D'})` vanish on `∂D'`, then
`∫_{D'} z 𝓛u dâ = ∫_{D'} u 𝓛*z dâ`. -/
theorem eq_green_formula : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (D : Set ℂ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsOpen D → D ⊆ Ω → IsSmoothOp D aUp bUp c → ∀ D' : Set ℂ, IsSmoothRelCompactIn D' D →
      ∀ u z : ℂ → ℝ, ContDiffOn ℝ 2 u (closure D') → ContDiffOn ℝ 2 z (closure D') →
        (∀ w ∈ frontier D', u w = 0 ∧ z w = 0) →
          ∫ w in D', z w * ellOp Ω aUp bUp c u w ∂hypArea Ω =
            ∫ w in D', u w * ellOpAdj Ω aUp bUp c z w ∂hypArea Ω := by
  intro Ω Ωs hJ D aUp bUp c hD hDΩ hop D' hD' u z hu hz h0
  obtain ⟨-, hl, hpos⟩ := s05_density_smooth hJ
  have hlD := hl.mono hDΩ
  have hposD : ∀ w ∈ D, 0 < poincareDensity Ω w := fun w hw => hpos w (hDΩ hw)
  have hD'0 := hD'
  obtain ⟨hDo, hKc, hKD, ψ, hψ, hψD, hnd⟩ := hD'
  have hsub : D' ⊆ closure D' := subset_closure
  have hD'D : D' ⊆ D := hsub.trans hKD
  have hDm : MeasurableSet D' := hDo.measurableSet
  have hfin : volume D' ≠ ⊤ := (lt_of_le_of_lt (measure_mono hsub) hKc.measure_lt_top).ne
  haveI : IsFiniteMeasure (volume.restrict D') :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hfin⟩
  -- `dâ = λ² dA` on `D' ⊆ Ω`
  have hchg : ∀ F : ℂ → ℝ, ∫ w in D', F w ∂hypArea Ω =
      ∫ w in D', poincareDensity Ω w ^ 2 * F w := by
    intro F
    have hc : ContinuousOn (fun w => ENNReal.ofReal (poincareDensity Ω w ^ 2)) D' :=
      ENNReal.continuous_ofReal.comp_continuousOn
        ((hlD.continuousOn.mono hD'D).pow 2)
    rw [hypArea, setIntegral_withDensity_eq_setIntegral_toReal_smul₀ (hc.aemeasurable hDm)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) F hDm,
      Measure.restrict_restrict hDm, Set.inter_eq_left.2 (hD'D.trans hDΩ)]
    refine setIntegral_congr_fun hDm fun w _ => ?_
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (sq_nonneg (poincareDensity Ω w))]
  rw [hchg, hchg]
  -- the data restricted to `D'`
  have hopD' : IsSmoothOp D' aUp bUp c := ⟨fun i j => (hop.1 i j).mono hD'D,
    fun i => (hop.2.1 i).mono hD'D, hop.2.2.1.mono hD'D, fun w hw => hop.2.2.2 w (hD'D hw)⟩
  have hlD' := hlD.mono hD'D
  have hposD' : ∀ w ∈ D', 0 < poincareDensity Ω w := fun w hw => hposD w (hD'D hw)
  have huD := hu.mono hsub
  have hzD := hz.mono hsub
  have hρd : ∀ w ∈ D', DifferentiableAt ℝ (poincareDensity Ω) w := fun w hw =>
    (hlD'.contDiffAt (hDo.mem_nhds hw)).differentiableAt (by simp)
  -- smoothness of the field `V` on `D'`
  have hinf1 : ∀ {g : ℂ → ℝ}, ContDiffOn ℝ ∞ g D' → ContDiffOn ℝ 1 g D' := fun hg => by
    simpa using contDiffOn_infty.1 hg 1
  have hfd : ∀ {f : ℂ → ℝ}, ContDiffOn ℝ 2 f D' → ∀ e : ℂ,
      ContDiffOn ℝ 1 (fun x => fderiv ℝ f x e) D' := fun hf e =>
    (hf.fderiv_of_isOpen hDo (by norm_num)).clm_apply contDiffOn_const
  have ha1 : ∀ i j, ContDiffOn ℝ 1 (fun x => aUp x i j) D' := fun i j => hinf1 (hopD'.1 i j)
  have hb1 : ∀ i, ContDiffOn ℝ 1 (fun x => bUp x i) D' := fun i => hinf1 (hopD'.2.1 i)
  have hDA : ∀ i, ContDiffOn ℝ ∞ (fun x => rhoDivA Ω aUp x i) D' := by
    intro i
    have h1A := s05_covDeriv_smooth hDo hlD' hposD' (s05_lowerA_smooth hlD' hopD'.1)
    have hsl : ∀ {k : ℕ} {T : TensorField k},
        ContDiffOn ℝ ∞ (fun p : ℂ × (Fin k → ℂ) => T p.1 p.2) (D' ×ˢ univ) → ∀ v : Fin k → ℂ,
          ContDiffOn ℝ ∞ (fun x => T x v) D' := fun hT v =>
      hT.comp (contDiffOn_id.prodMk contDiffOn_const) fun x hx => ⟨hx, mem_univ _⟩
    show ContDiffOn ℝ ∞ (fun x => (∑ j : Fin 2,
      rhoCovDeriv Ω (lowerA Ω aUp) x ![frameVec j, frameVec i, frameVec j]) /
        poincareDensity Ω x ^ 4) D'
    exact (ContDiffOn.sum fun j _ => hsl h1A _).div (hlD'.pow 4) fun x hx =>
      pow_ne_zero _ (hposD' x hx).ne'
  have hu1 : ContDiffOn ℝ 1 u D' := huD.of_le (by norm_num)
  have hz1 : ContDiffOn ℝ 1 z D' := hzD.of_le (by norm_num)
  set V : ℂ → Fin 2 → ℝ := fun x i =>
    z x * ∑ j : Fin 2, aUp x i j * fderiv ℝ u x (frameVec j) -
      u x * ∑ j : Fin 2, aUp x i j * fderiv ℝ z x (frameVec j) -
      u x * z x * rhoDivA Ω aUp x i + u x * z x * bUp x i with hV
  have hV1 : ∀ i, ContDiffOn ℝ 1 (fun x => V x i) D' := by
    intro i
    simp only [hV, Fin.sum_univ_two]
    exact (((hz1.mul (((ha1 i 0).mul (hfd huD _)).add ((ha1 i 1).mul (hfd huD _)))).sub
      (hu1.mul (((ha1 i 0).mul (hfd hzD _)).add ((ha1 i 1).mul (hfd hzD _))))).sub
        ((hu1.mul hz1).mul (hinf1 (hDA i)))).add ((hu1.mul hz1).mul (hb1 i))
  set Φ : Fin 2 → ℂ → ℝ := fun i x => poincareDensity Ω x ^ 2 * V x i with hΦdef
  have hΦ : ∀ i, ContDiffOn ℝ 1 (Φ i) D' := fun i => ((hinf1 hlD').pow 2).mul (hV1 i)
  -- pointwise: `λ²(z 𝓛u - u 𝓛*z) = -∂_i Φ^i`
  have hpt : ∀ w ∈ D', poincareDensity Ω w ^ 2 * (z w * ellOp Ω aUp bUp c u w) -
      poincareDensity Ω w ^ 2 * (u w * ellOpAdj Ω aUp bUp c z w) =
        -(fderiv ℝ (Φ 0) w 1 + fderiv ℝ (Φ 1) w I) := by
    intro w hw
    have h5 : z w * ellOp Ω aUp bUp c u w - u w * ellOpAdj Ω aUp bUp c z w =
        -rhoDivB Ω V w := s05_gr_pointwise hDo hlD' hposD' hopD' huD hzD hw
    have hVd : ∀ i, DifferentiableAt ℝ (fun x => V x i) w := fun i =>
      ((hV1 i).differentiableOn (by norm_num) w hw).differentiableAt (hDo.mem_nhds hw)
    have h1 := s05_gr_divB_eucl hVd (hρd w hw) (hposD' w hw)
    rw [← mul_sub, h5, mul_neg, h1, Fin.sum_univ_two]
    rfl
  -- bounds on `closure D'`
  have hbd : ∀ {g : ℂ → ℝ}, ContinuousOn g D → ∃ C, ∀ x ∈ D', |g x| ≤ C := by
    intro g hg
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hg.mono hKD)
    exact ⟨C, fun x hx => by simpa [Real.norm_eq_abs] using hC x (hsub hx)⟩
  obtain ⟨R, hR⟩ := hbd (g := fun x => poincareDensity Ω x ^ 2) (hlD.continuousOn.pow 2)
  obtain ⟨hcC', hcB', hcDA, -⟩ := s05_gr_coeff_cont hD hlD hposD hop
  have hfr : ∀ i : Fin 2, ‖frameVec i‖ = 1 := by
    intro i; fin_cases i <;> simp [frameVec]
  have hu' : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) u (closure D') := by exact_mod_cast hu
  have hz' : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) z (closure D') := by exact_mod_cast hz
  obtain ⟨U0, hU0⟩ := s05_gr_bdd hDo hKc hu' (m := 0) (by norm_num)
  obtain ⟨Z0, hZ0⟩ := s05_gr_bdd hDo hKc hz' (m := 0) (by norm_num)
  obtain ⟨U1, hU1⟩ := s05_gr_bdd hDo hKc hu' (m := 1) (by norm_num)
  obtain ⟨Z1, hZ1⟩ := s05_gr_bdd hDo hKc hz' (m := 1) (by norm_num)
  have hz0 : ∀ w ∈ D', |z w| ≤ Z0 := fun w hw => by
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hZ0 w hw
  have hdu : ∀ w ∈ D', ‖fderiv ℝ u w‖ ≤ U1 := fun w hw => by simpa using hU1 w hw
  have hdz : ∀ w ∈ D', ‖fderiv ℝ z w‖ ≤ Z1 := fun w hw => by simpa using hZ1 w hw
  -- `u, z = O(|ψ|)` (G7)
  have hdiffD : ∀ {f : ℂ → ℝ}, ContDiffOn ℝ 2 f D' → ∀ w ∈ D', DifferentiableAt ℝ f w :=
    fun hf w hw => (hf.differentiableOn (by norm_num) w hw).differentiableAt (hDo.mem_nhds hw)
  obtain ⟨Cu, hCu⟩ := s05_gr_vanish_le hψ hψD hnd hKc hu.continuousOn (hdiffD huD)
    ⟨U1, hdu⟩ fun w hw => (h0 w hw).1
  obtain ⟨Cz, hCz⟩ := s05_gr_vanish_le hψ hψD hnd hKc hz.continuousOn (hdiffD hzD)
    ⟨Z1, hdz⟩ fun w hw => (h0 w hw).2
  have hmb : ∀ x y X Y : ℝ, |x| ≤ X → |y| ≤ Y → |x * y| ≤ X * Y := fun x y X Y hx hy => by
    rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)
  -- `|Φ| = O(|ψ|)`
  have hgradb : ∀ {f : ℂ → ℝ} {F : ℝ}, (∀ w ∈ D', ‖fderiv ℝ f w‖ ≤ F) → ∀ i,
      ∃ P, ∀ w ∈ D', |∑ j : Fin 2, aUp w i j * fderiv ℝ f w (frameVec j)| ≤ P := by
    intro f F hF i
    obtain ⟨A0, hA0⟩ := hbd (hop.1 i 0).continuousOn
    obtain ⟨A1, hA1⟩ := hbd (hop.1 i 1).continuousOn
    have he : ∀ w ∈ D', ∀ j, |fderiv ℝ f w (frameVec j)| ≤ F := fun w hw j => by
      have := (fderiv ℝ f w).le_opNorm (frameVec j)
      rw [hfr, mul_one, Real.norm_eq_abs] at this
      exact this.trans (hF w hw)
    refine ⟨A0 * F + A1 * F, fun w hw => ?_⟩
    rw [Fin.sum_univ_two]
    exact (abs_add_le _ _).trans (add_le_add (hmb _ _ _ _ (hA0 w hw) (he w hw 0))
      (hmb _ _ _ _ (hA1 w hw) (he w hw 1)))
  have hCi : ∀ i, ∃ C, ∀ w ∈ D', |Φ i w| ≤ C * |ψ w| := by
    intro i
    obtain ⟨P1, hP1⟩ := hgradb hdu i
    obtain ⟨P2, hP2⟩ := hgradb hdz i
    obtain ⟨Q1, hQ1⟩ := hbd (hcDA i)
    obtain ⟨Q2, hQ2⟩ := hbd (hop.2.1 i).continuousOn
    refine ⟨R * (Cz * P1 + Cu * P2 + Cu * Z0 * Q1 + Cu * Z0 * Q2), fun w hw => ?_⟩
    have hψ0 := abs_nonneg (ψ w)
    have t1 := abs_le.1 (hmb _ _ _ _ (hCz w hw) (hP1 w hw))
    have t2 := abs_le.1 (hmb _ _ _ _ (hCu w hw) (hP2 w hw))
    have t3 := abs_le.1 (hmb _ _ _ _ (hmb _ _ _ _ (hCu w hw) (hz0 w hw)) (hQ1 w hw))
    have t4 := abs_le.1 (hmb _ _ _ _ (hmb _ _ _ _ (hCu w hw) (hz0 w hw)) (hQ2 w hw))
    have hVb : |V w i| ≤ (Cz * P1 + Cu * P2 + Cu * Z0 * Q1 + Cu * Z0 * Q2) * |ψ w| := by
      simp only [hV]
      rw [abs_le]
      constructor <;> linarith [t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]
    calc |Φ i w| = |poincareDensity Ω w ^ 2 * V w i| := rfl
      _ ≤ R * ((Cz * P1 + Cu * P2 + Cu * Z0 * Q1 + Cu * Z0 * Q2) * |ψ w|) :=
        hmb _ _ _ _ (hR w hw) hVb
      _ = _ := by ring
  choose Ci hCi using hCi
  have hCmax : ∀ i, Ci i ≤ |Ci 0| + |Ci 1| :=
    Fin.forall_fin_two.2 ⟨by linarith [le_abs_self (Ci 0), abs_nonneg (Ci 1)],
      by linarith [le_abs_self (Ci 1), abs_nonneg (Ci 0)]⟩
  have hC : ∃ C, ∀ i, ∀ w ∈ D', |Φ i w| ≤ C * |ψ w| :=
    ⟨|Ci 0| + |Ci 1|, fun i w hw => (hCi i w hw).trans
      (mul_le_mul_of_nonneg_right (hCmax i) (abs_nonneg _))⟩
  -- the divergence is integrable on `D'` (G10)
  obtain ⟨Mu, hMu⟩ := s05_gr_ops_bdd hD hlD hposD hop hD'0 hu
  obtain ⟨Mz, hMz⟩ := s05_gr_ops_bdd hD hlD hposD hop hD'0 hz
  obtain ⟨U0', hU0'⟩ : ∃ U0', ∀ w ∈ D', |u w| ≤ U0' := ⟨U0, fun w hw => by
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hU0 w hw⟩
  have hint : IntegrableOn (fun w => fderiv ℝ (Φ 0) w 1 + fderiv ℝ (Φ 1) w I) D' := by
    have hcont : ContinuousOn (fun w => fderiv ℝ (Φ 0) w 1 + fderiv ℝ (Φ 1) w I) D' :=
      (((hΦ 0).continuousOn_fderiv_of_isOpen hDo le_rfl).clm_apply continuousOn_const).add
        (((hΦ 1).continuousOn_fderiv_of_isOpen hDo le_rfl).clm_apply continuousOn_const)
    refine Integrable.of_bound (hcont.aestronglyMeasurable hDm) (R * (Z0 * Mu) + R * (U0' * Mz))
      ((ae_restrict_iff' hDm).2 (Filter.Eventually.of_forall fun w hw => ?_))
    have e := hpt w hw
    have t1 := abs_le.1 (hmb _ _ _ _ (hR w hw) (hmb _ _ _ _ (hz0 w hw) (hMu w hw).1))
    have t2 := abs_le.1 (hmb _ _ _ _ (hR w hw) (hmb _ _ _ _ (hU0' w hw) (hMz w hw).2))
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [t1.1, t1.2, t2.1, t2.2]
  have hzero := s05_gr_div_zero hψ hψD hKc hΦ hint hC
  -- conclusion (if one side is not integrable, neither is the other and both are `0`)
  by_cases hI : IntegrableOn (fun w => poincareDensity Ω w ^ 2 *
    (z w * ellOp Ω aUp bUp c u w)) D'
  · have hI2 : IntegrableOn (fun w => poincareDensity Ω w ^ 2 *
        (u w * ellOpAdj Ω aUp bUp c z w)) D' :=
      (hI.add hint).congr_fun (fun w hw => by simp only [Pi.add_apply, Pi.sub_apply]; linarith [hpt w hw]) hDm
    rw [← sub_eq_zero, ← integral_sub hI hI2, setIntegral_congr_fun hDm hpt, MeasureTheory.integral_neg,
      hzero, neg_zero]
  · have hI2 : ¬ IntegrableOn (fun w => poincareDensity Ω w ^ 2 *
        (u w * ellOpAdj Ω aUp bUp c z w)) D' := fun h =>
      hI ((h.sub hint).congr_fun (fun w hw => by simp only [Pi.add_apply, Pi.sub_apply]; linarith [hpt w hw]) hDm)
    rw [integral_undef hI, integral_undef hI2]

/-- Helper (P2): the covariant derivative of a constant function vanishes. -/
theorem s05_rhoCovDeriv_scalar_const (Ω : Set ℂ) (a : ℝ) :
    rhoCovDeriv Ω (scalarField fun _ => a) = fun _ _ => 0 := by
  funext w v
  simp [rhoCovDeriv, scalarField]

/-- Helper (P2): the covariant derivative of the zero tensor vanishes. -/
theorem s05_rhoCovDeriv_zero (Ω : Set ℂ) (k : ℕ) :
    rhoCovDeriv Ω (fun _ _ => (0 : ℝ) : TensorField k) = fun _ _ => 0 := by
  funext w v
  simp [rhoCovDeriv]

/-- Helper (P2): the Hessian of a constant function vanishes. -/
theorem s05_rhoHess_const (Ω : Set ℂ) (a : ℝ) : rhoHess Ω (fun _ => a) = fun _ _ => 0 := by
  funext w v
  simp only [rhoHess, rhoIterCovDeriv, s05_rhoCovDeriv_scalar_const, s05_rhoCovDeriv_zero]

/-- Helper (P2): `𝓛1 = c`. -/
theorem s05_ellOp_const_one (Ω : Set ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ) (w : ℂ) : ellOp Ω aUp bUp c (fun _ => 1) w = c w := by
  simp [ellOp, s05_rhoHess_const]

/-- Helper (P2): an `ε'`-admissible operator has `|c - 2| ≤ ε'` on `D`. -/
theorem s05_admissible_c_bound {Ω D : Set ℂ} {ε' : ℝ} {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ}
    {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ} (h : IsAdmissibleOp Ω D ε' aUp bUp c) :
    ∀ w ∈ D, |c w - 2| ≤ ε' := by
  obtain ⟨hε, -, -, -, -, hn⟩ := h
  intro w hw
  have h3 : rhoCjNorm Ω 0 (scalarField fun w => c w - 2) D ≤ ENNReal.ofReal ε' :=
    le_trans le_add_self hn
  have h4 : ENNReal.ofReal (rhoTensorNorm Ω (rhoIterCovDeriv Ω 0 (scalarField fun w => c w - 2)) w)
      ≤ rhoCjNorm Ω 0 (scalarField fun w => c w - 2) D := by
    unfold rhoCjNorm
    exact le_iSup₂_of_le 0 le_rfl (le_iSup₂_of_le w hw le_rfl)
  have h5 : rhoTensorNorm Ω (rhoIterCovDeriv Ω 0 (scalarField fun w => c w - 2)) w =
      |c w - 2| := by
    simp [rhoTensorNorm, rhoIterCovDeriv, scalarField, Real.sqrt_sq_eq_abs]
  rw [← h5]
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).1 (h4.trans h3)

/-- Helper (P2): Cauchy–Schwarz, `|∑ f g| ≤ √(∑ f²) √(∑ g²)`. -/
theorem s05_abs_sum_mul_le {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    |∑ i, f i * g i| ≤ Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, g i ^ 2) :=
  (Real.abs_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)).trans_eq
    (Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _) _)

/-- Helper (P2): the Hilbert–Schmidt sum of a `2`-tensor in frame components. -/
theorem s05_hs_two (T : TensorField 2) (w : ℂ) :
    ∑ idx : Fin 2 → Fin 2, (T w fun m => frameVec (idx m)) ^ 2 =
      ∑ p : Fin 2 × Fin 2, (T w ![frameVec p.1, frameVec p.2]) ^ 2 := by
  rw [← (finTwoArrowEquiv (Fin 2)).symm.sum_comp]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 2
  funext m
  fin_cases m <;> rfl

/-- Helper (P2): the Hilbert–Schmidt sum of a `1`-tensor in frame components. -/
theorem s05_hs_one (T : TensorField 1) (w : ℂ) :
    ∑ idx : Fin 1 → Fin 2, (T w fun m => frameVec (idx m)) ^ 2 =
      ∑ i : Fin 2, (T w ![frameVec i]) ^ 2 := by
  rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  funext m
  fin_cases m
  rfl

/-- Helper (P2): the scalar inequality behind `s05_ellOp_err`. -/
theorem s05_err_real {L X E1 E2 nM nH nB ng : ℝ} (hL : 0 < L)
    (hX : X * L ^ 4 = -(E1 + L ^ 2 * E2)) (hA : |E1| ≤ L ^ 2 * nM * (L ^ 2 * nH))
    (hB : |E2| ≤ L ^ 1 * nB * (L ^ 1 * ng)) : |X| ≤ nM * nH + nB * ng := by
  have h2 : 0 < L ^ 2 := by positivity
  have h4 : 0 < L ^ 4 := by positivity
  have key : |X| * L ^ 4 ≤ (nM * nH + nB * ng) * L ^ 4 :=
    calc |X| * L ^ 4 = |X * L ^ 4| := by rw [abs_mul, abs_of_pos h4]
      _ = |E1 + L ^ 2 * E2| := by rw [hX, abs_neg]
      _ ≤ |E1| + L ^ 2 * |E2| := by
        refine (abs_add_le _ _).trans_eq ?_
        rw [abs_mul, abs_of_pos h2]
      _ ≤ L ^ 2 * nM * (L ^ 2 * nH) + L ^ 2 * (L ^ 1 * nB * (L ^ 1 * ng)) := by gcongr
      _ = (nM * nH + nB * ng) * L ^ 4 := by ring
  exact le_of_mul_le_mul_right key h4

/-- Helper (P2): the frame components of `ρ`. -/
theorem s05_metric_frame (Ω : Set ℂ) (w : ℂ) :
    rhoMetricT Ω w ![frameVec 0, frameVec 0] = poincareDensity Ω w ^ 2 ∧
      rhoMetricT Ω w ![frameVec 0, frameVec 1] = 0 ∧
      rhoMetricT Ω w ![frameVec 1, frameVec 0] = 0 ∧
      rhoMetricT Ω w ![frameVec 1, frameVec 1] = poincareDensity Ω w ^ 2 := by
  simp [rhoMetricT, frameVec]

/-- Helper (P2): `|𝓛u - (c u - Δ_ρ u)| ≤ ‖a♭ - ρ‖ ‖∇²u‖ + ‖b♭‖ ‖∇u‖` pointwise. -/
theorem s05_ellOp_err {Ω : Set ℂ} (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ)
    (c u : ℂ → ℝ) {w : ℂ} (hl : 0 < poincareDensity Ω w) :
    |ellOp Ω aUp bUp c u w - (c w * u w - rhoLaplacian Ω u w)| ≤
      rhoTensorNorm Ω (lowerA Ω aUp - rhoMetricT Ω) w * rhoTensorNorm Ω (rhoHess Ω u) w +
        rhoTensorNorm Ω (lowerB Ω bUp) w * rhoTensorNorm Ω (rhoCovDeriv Ω (scalarField u)) w := by
  have hA := s05_abs_sum_mul_le
    (fun p : Fin 2 × Fin 2 => (lowerA Ω aUp - rhoMetricT Ω) w ![frameVec p.1, frameVec p.2])
    (fun p => rhoHess Ω u w ![frameVec p.1, frameVec p.2])
  have hB := s05_abs_sum_mul_le (fun i : Fin 2 => lowerB Ω bUp w ![frameVec i])
    (fun i => rhoCovDeriv Ω (scalarField u) w ![frameVec i])
  beta_reduce at hA hB
  rw [← s05_hs_two, ← s05_hs_two (rhoHess Ω u), s05_sqrt_hs _ hl,
    s05_sqrt_hs (k := 2) (rhoHess Ω u) hl] at hA
  rw [← s05_hs_one, ← s05_hs_one (rhoCovDeriv Ω (scalarField u)), s05_sqrt_hs _ hl,
    s05_sqrt_hs (k := 1) (rhoCovDeriv Ω (scalarField u)) hl] at hB
  refine s05_err_real hl ?_ hA hB
  obtain ⟨m00, m01, m10, m11⟩ := s05_metric_frame Ω w
  have hg : ∀ i : Fin 2, rhoCovDeriv Ω (scalarField u) w ![frameVec i] =
      fderiv ℝ u w (frameVec i) := fun i => by rw [s05_covDeriv_scalar]; rfl
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Pi.sub_apply, s05_lowerA_frame, m00, m01,
    m10, m11, s05_lowerB_frame, hg, ellOp, rhoLaplacian]
  field_simp
  ring

/-- Helper (P2): the real derivative of a holomorphic function. -/
theorem s05_hasFDerivAt_holo {g : ℂ → ℂ} {x : ℂ} (h : DifferentiableAt ℂ g x) :
    HasFDerivAt g ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv g x)).restrictScalars ℝ)
      x :=
  h.hasDerivAt.hasFDerivAt.restrictScalars ℝ

/-- Helper (P2): for `K = 1 - |ψ|²` with `ψ : Ω → 𝔻` holomorphic and `λ = 2|ψ'|/(1 - |ψ|²)`:
`dK(Y) = -2 Re(Y ψ' ψ̄)` and `∇²K(X, Y) = -2|ψ'|² Re(Y X̄) + 4 Re(ψ̄² ψ'² X Y)/(1 - |ψ|²)`. -/
theorem s05_kernel_derivs {Ω : Set ℂ} {K : ℂ → ℝ} {ψ : ℂ → ℂ} (hΩ : IsOpen Ω)
    (hψ : DifferentiableOn ℂ ψ Ω) (h1 : ∀ x ∈ Ω, ‖ψ x‖ < 1) (h0 : ∀ x ∈ Ω, deriv ψ x ≠ 0)
    (hK : ∀ x ∈ Ω, K x = 1 - ‖ψ x‖ ^ 2)
    (hl : ∀ x ∈ Ω, poincareDensity Ω x = 2 * ‖deriv ψ x‖ / (1 - ‖ψ x‖ ^ 2)) {w : ℂ}
    (hw : w ∈ Ω) :
    (∀ Y, fderiv ℝ K w Y = -2 * (Y * deriv ψ w * conj (ψ w)).re) ∧
    ∀ X Y, rhoHess Ω K w ![X, Y] = -2 * ‖deriv ψ w‖ ^ 2 * (Y * conj X).re +
      4 / (1 - ‖ψ w‖ ^ 2) * (conj (ψ w) ^ 2 * deriv ψ w ^ 2 * X * Y).re := by
  have hdψ : ∀ x ∈ Ω, HasFDerivAt ψ ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
      (deriv ψ x)).restrictScalars ℝ) x := fun x hx =>
    s05_hasFDerivAt_holo (hψ.differentiableAt (hΩ.mem_nhds hx))
  have hdψ' := s05_hasFDerivAt_holo ((hψ.deriv hΩ).differentiableAt (hΩ.mem_nhds hw))
  have hk : 0 < 1 - ‖ψ w‖ ^ 2 := by nlinarith [h1 w hw, norm_nonneg (ψ w)]
  have hα : deriv ψ w ≠ 0 := h0 w hw
  -- first derivative of `K` on `Ω`
  have hKd : ∀ x ∈ Ω, ∀ Y, fderiv ℝ K x Y = -(2 * inner ℝ (ψ x) (Y * deriv ψ x)) := by
    intro x hx Y
    have hE : K =ᶠ[𝓝 x] fun y => 1 - ‖ψ y‖ ^ 2 := eventuallyEq_of_mem (hΩ.mem_nhds hx) hK
    rw [(((hasFDerivAt_const (1 : ℝ) x).sub (hdψ x hx).norm_sq).congr_of_eventuallyEq hE).fderiv]
    simp
    ring
  -- second derivative
  have hD2 : ∀ X Y, fderiv ℝ (fun x => fderiv ℝ K x Y) w X =
      -(2 * (inner ℝ (ψ w) (Y * (X * deriv (deriv ψ) w)) +
        inner ℝ (X * deriv ψ w) (Y * deriv ψ w))) := by
    intro X Y
    have hE : (fun x => fderiv ℝ K x Y) =ᶠ[𝓝 w]
        fun x => -(2 * inner ℝ (ψ x) (Y * deriv ψ x)) :=
      eventuallyEq_of_mem (hΩ.mem_nhds hw) fun x hx => hKd x hx Y
    rw [((((hdψ w hw).inner ℝ (hdψ'.const_mul Y)).const_mul 2).neg.congr_of_eventuallyEq
      hE).fderiv]
    simp [fderivInnerCLM_apply]
  -- derivative of `log λ`
  have hE3 : (fun x => Real.log (poincareDensity Ω x)) =ᶠ[𝓝 w] fun x =>
      Real.log 2 + 2⁻¹ * Real.log (‖deriv ψ x‖ ^ 2) - Real.log (1 - ‖ψ x‖ ^ 2) := by
    filter_upwards [hΩ.mem_nhds hw] with x hx
    have hkx : 0 < 1 - ‖ψ x‖ ^ 2 := by nlinarith [h1 x hx, norm_nonneg (ψ x)]
    have hax : 0 < ‖deriv ψ x‖ := norm_pos_iff.2 (h0 x hx)
    rw [hl x hx, Real.log_div (by positivity) hkx.ne', Real.log_mul two_ne_zero hax.ne',
      Real.log_pow]
    push_cast
    ring
  have hG := ((((hdψ'.norm_sq).log (pow_ne_zero 2 (norm_ne_zero_iff.2 hα))).const_mul
    (2⁻¹ : ℝ)).const_add (Real.log 2)).sub
    (((hasFDerivAt_const (1 : ℝ) w).sub (hdψ w hw).norm_sq).log hk.ne')
  have hLG : ∀ X, fderiv ℝ (fun x => Real.log (poincareDensity Ω x)) w X =
      2⁻¹ * ((‖deriv ψ w‖ ^ 2)⁻¹ * (2 * inner ℝ (deriv ψ w) (X * deriv (deriv ψ) w))) -
        (1 - ‖ψ w‖ ^ 2)⁻¹ * -(2 * inner ℝ (ψ w) (X * deriv ψ w)) := by
    intro X
    rw [(hG.congr_of_eventuallyEq hE3).fderiv]
    simp
    ring
  refine ⟨fun Y => by rw [hKd w hw]; simp, fun X Y => ?_⟩
  rw [s05_rhoHess_eq, hD2, hKd w hw]
  simp only [rhoChristoffel, logDensityGrad, hLG]
  have hn : ‖deriv ψ w‖ ^ 2 = (deriv ψ w).re ^ 2 + (deriv ψ w).im ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]; ring
  have hz : ‖ψ w‖ ^ 2 = (ψ w).re ^ 2 + (ψ w).im ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]; ring
  have hn0 : (deriv ψ w).re ^ 2 + (deriv ψ w).im ^ 2 ≠ 0 := by
    rw [← hn]; exact pow_ne_zero 2 (norm_ne_zero_iff.2 hα)
  have hk0 : 1 - ((ψ w).re ^ 2 + (ψ w).im ^ 2) ≠ 0 := by rw [← hz]; exact hk.ne'
  rw [hn, hz]
  simp only [Complex.inner, mul_re, mul_im, add_re, add_im, sub_re, sub_im, conj_re, conj_im,
    ofReal_re, ofReal_im, I_re, I_im, one_re, one_im, pow_two]
  field_simp
  ring

/-- Helper (P2): the pointwise conclusions of Lemma 5.3 (a) from the formulas of
`s05_kernel_derivs`. -/
theorem s05_kernel_frame {Ω : Set ℂ} {K : ℂ → ℝ} {w z α : ℂ} (hz : ‖z‖ < 1) (hα : α ≠ 0)
    (hKw : K w = 1 - ‖z‖ ^ 2) (hl : poincareDensity Ω w = 2 * ‖α‖ / (1 - ‖z‖ ^ 2))
    (hd : ∀ Y, fderiv ℝ K w Y = -2 * (Y * α * conj z).re)
    (hH : ∀ X Y, rhoHess Ω K w ![X, Y] = -2 * ‖α‖ ^ 2 * (Y * conj X).re +
      4 / (1 - ‖z‖ ^ 2) * (conj z ^ 2 * α ^ 2 * X * Y).re) :
    rhoLaplacian Ω K w = -(K w) ^ 2 ∧
      rhoTensorNorm Ω (rhoCovDeriv Ω (scalarField K)) w ≤ K w ∧
      rhoTensorNorm Ω (rhoHess Ω K) w ≤ 2 * K w := by
  have hk : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have ha : 0 < ‖α‖ := norm_pos_iff.2 hα
  have hL : 0 < poincareDensity Ω w := by rw [hl]; positivity
  have hn : ‖α‖ ^ 2 = α.re ^ 2 + α.im ^ 2 := by rw [Complex.sq_norm, normSq_apply]; ring
  have hz2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, normSq_apply]; ring
  have hZ : z.re ^ 2 + z.im ^ 2 < 1 := by rw [← hz2]; nlinarith [norm_nonneg z]
  have hA0 : 0 ≤ α.re ^ 2 + α.im ^ 2 := by positivity
  have f0 : frameVec 0 = 1 := rfl
  have f1 : frameVec 1 = I := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [rhoLaplacian, Fin.sum_univ_two, hH, hKw, hl, f0, f1]
    simp only [mul_re, mul_im, conj_re, conj_im, one_re, one_im, I_re, I_im, pow_two]
    field_simp
    ring
  · show rhoTensorNorm Ω (k := 1) (rhoCovDeriv Ω (scalarField K)) w ≤ K w
    have hg : ∀ i : Fin 2, rhoCovDeriv Ω (scalarField K) w ![frameVec i] =
        fderiv ℝ K w (frameVec i) := fun i => by rw [s05_covDeriv_scalar]; rfl
    unfold rhoTensorNorm
    rw [s05_hs_one, div_le_iff₀ (pow_pos hL 1)]
    simp only [Fin.sum_univ_two, hg, hd, f0, f1]
    rw [hKw, hl, pow_one, show (1 - ‖z‖ ^ 2) * (2 * ‖α‖ / (1 - ‖z‖ ^ 2)) = 2 * ‖α‖ by
      field_simp]
    refine (Real.sqrt_le_left (by positivity)).2 ?_
    rw [show (2 * ‖α‖) ^ 2 = 2 ^ 2 * ‖α‖ ^ 2 by ring, hn]
    simp only [mul_re, mul_im, conj_re, conj_im, one_re, one_im, I_re, I_im]
    calc _ = 4 * (α.re ^ 2 + α.im ^ 2) * (z.re ^ 2 + z.im ^ 2) := by ring
      _ ≤ 2 ^ 2 * (α.re ^ 2 + α.im ^ 2) := by nlinarith [mul_le_mul_of_nonneg_left hZ.le hA0]
  · show rhoTensorNorm Ω (k := 2) (rhoHess Ω K) w ≤ 2 * K w
    unfold rhoTensorNorm
    rw [s05_hs_two, div_le_iff₀ (pow_pos hL 2)]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, hH, f0, f1]
    rw [hKw, hl, show 2 * (1 - ‖z‖ ^ 2) * (2 * ‖α‖ / (1 - ‖z‖ ^ 2)) ^ 2 =
      2 * ‖α‖ ^ 2 * (4 / (1 - ‖z‖ ^ 2)) by field_simp; ring]
    have ht : 4 ≤ 4 / (1 - ‖z‖ ^ 2) := by
      rw [le_div_iff₀ hk]; nlinarith [norm_nonneg z]
    generalize 4 / (1 - ‖z‖ ^ 2) = t at ht ⊢
    refine (Real.sqrt_le_left (by positivity)).2 ?_
    rw [hn]
    simp only [mul_re, mul_im, conj_re, conj_im, one_re, one_im, I_re, I_im, pow_two]
    have hZ2 : (z.re * z.re + z.im * z.im) ^ 2 ≤ 1 := by nlinarith
    have ht2 : 16 ≤ t ^ 2 := by nlinarith
    set A := α.re * α.re + α.im * α.im with hAdef
    calc _ = 8 * A ^ 2 + 2 * t ^ 2 * ((z.re * z.re + z.im * z.im) ^ 2 * A ^ 2) := by
          rw [hAdef]; ring
      _ ≤ (2 * A * t) * (2 * A * t) := by
          nlinarith [mul_le_mul_of_nonneg_left hZ2 (mul_nonneg (sq_nonneg t) (sq_nonneg A)),
            mul_le_mul_of_nonneg_left ht2 (sq_nonneg A)]

/-- Helper (P2): a Riemann map `ψ : Ω → 𝔻` with `ψ(p) = 0` gives `k_p = 1 - |ψ|²` and
`λ = 2|ψ'|/(1 - |ψ|²)` on `Ω`. -/
theorem s05_kernel_riemann {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {p : ℂ} (hp : p ∈ Ω) :
    ∃ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ Ω ∧ (∀ x ∈ Ω, ‖ψ x‖ < 1) ∧ (∀ x ∈ Ω, deriv ψ x ≠ 0) ∧
      (∀ x ∈ Ω, intrKernel Ω p x = 1 - ‖ψ x‖ ^ 2) ∧
      ∀ x ∈ Ω, poincareDensity Ω x = 2 * ‖deriv ψ x‖ / (1 - ‖ψ x‖ ^ 2) := by
  have hΩ := s05_jordan_isOpen hJ
  obtain ⟨φ, hφ⟩ := s05_jordan_riemann hJ
  have ha : ‖φ p‖ < 1 := mem_ball_zero_iff.mp (hφ.mapsTo hp)
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℂ → ℂ, ψ = blaschke (φ p) ∘ φ := ⟨_, rfl⟩
  have hψ : IsConformalOnto ψ Ω unitDisc := hψdef ▸ (isConformalOnto_blaschke ha).comp hφ
  have hf := hψ.symm hΩ
  obtain ⟨f, hfdef⟩ : ∃ f : ℂ → ℂ, f = Function.invFunOn ψ Ω := ⟨_, rfl⟩
  rw [← hfdef] at hf
  have hmap : ∀ x ∈ Ω, ψ x ∈ unitDisc := fun x hx => hψ.mapsTo hx
  have hfψ : ∀ x ∈ Ω, f (ψ x) = x := fun x hx => hfdef ▸ hψ.2.1.leftInvOn_invFunOn hx
  have hd : ∀ x ∈ Ω, deriv ψ x ≠ 0 := fun x hx => deriv_ne_zero_of_injOn hΩ hψ.1 hψ.2.1 hx
  have hf0 : f 0 = p := by
    have h0 : ψ p = 0 := by rw [hψdef]; exact blaschke_self _
    rw [← h0]; exact hfψ p hp
  refine ⟨ψ, hψ.1, fun x hx => mem_ball_zero_iff.mp (hmap x hx), hd, fun x hx => ?_,
    fun x hx => ?_⟩
  · have hk := s02_intrKernel_eq hf (a := 0) (mem_ball_self one_pos) (hmap x hx)
    rw [hf0, hfψ x hx] at hk
    rw [hk]
    simp
  · rw [s05_density_eq hΩ hψ hx, ← hfdef]
    have hfd : DifferentiableAt ℂ f (ψ x) :=
      hf.1.differentiableAt (isOpen_ball.mem_nhds (hmap x hx))
    have hc := hfd.hasDerivAt.comp x (hψ.1.differentiableAt (hΩ.mem_nhds hx)).hasDerivAt
    have hid : HasDerivAt (f ∘ ψ) 1 x := (hasDerivAt_id x).congr_of_eventuallyEq
      (eventuallyEq_of_mem (hΩ.mem_nhds hx) fun y hy => hfψ y hy)
    have h1 := congrArg norm (hc.unique hid)
    rw [norm_mul, norm_one] at h1
    have hn : ‖deriv ψ x‖ ≠ 0 := norm_ne_zero_iff.2 (hd x hx)
    rw [eq_inv_of_mul_eq_one_left h1]
    field_simp

/-- **Lemma 5.3 (a)** (`lem:test-functions`, sec05-upper.tex:158), `C₀ = 11`.  For `p ∈ Ω` and
`k = k_p`: `Δ_ρ k = -k²`, `|∇k| ≤ k`, `|∇²k| ≤ 2k` on `Ω`, and
`(2 - C₀ε') k ≤ 𝓛* k ≤ (3 + C₀ε') k` on `D` (5.9) for `𝓛` `ε'`-admissible on `D`. -/
theorem lem_test_functions_a : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (D : Set ℂ) (ε' : ℝ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsAdmissibleOp Ω D ε' aUp bUp c → ∀ p ∈ Ω,
      (∀ w ∈ Ω, rhoLaplacian Ω (intrKernel Ω p) w = -(intrKernel Ω p w) ^ 2 ∧
        rhoTensorNorm Ω (rhoCovDeriv Ω (scalarField (intrKernel Ω p))) w ≤ intrKernel Ω p w ∧
        rhoTensorNorm Ω (rhoHess Ω (intrKernel Ω p)) w ≤ 2 * intrKernel Ω p w) ∧
      ∀ w ∈ D, (2 - 11 * ε') * intrKernel Ω p w ≤ ellOpAdj Ω aUp bUp c (intrKernel Ω p) w ∧
        ellOpAdj Ω aUp bUp c (intrKernel Ω p) w ≤ (3 + 11 * ε') * intrKernel Ω p w := by
  intro Ω Ωs hJ D ε' aUp bUp c h p hp
  have hΩ := s05_jordan_isOpen hJ
  obtain ⟨ψ, hψ, h1, h0, hK, hl⟩ := s05_kernel_riemann hJ hp
  have hpt : ∀ w ∈ Ω, rhoLaplacian Ω (intrKernel Ω p) w = -(intrKernel Ω p w) ^ 2 ∧
      rhoTensorNorm Ω (rhoCovDeriv Ω (scalarField (intrKernel Ω p))) w ≤ intrKernel Ω p w ∧
      rhoTensorNorm Ω (rhoHess Ω (intrKernel Ω p)) w ≤ 2 * intrKernel Ω p w := fun w hw =>
    have hD := s05_kernel_derivs hΩ hψ h1 h0 hK hl hw
    s05_kernel_frame (h1 w hw) (h0 w hw) (hK w hw) (hl w hw) hD.1 hD.2
  refine ⟨hpt, fun w hw => ?_⟩
  have hwΩ : w ∈ Ω := h.2.2.2.1 hw
  obtain ⟨-, -, hpos⟩ := s05_density_smooth hJ
  have hposD : ∀ x ∈ D, 0 < poincareDensity Ω x := fun x hx => hpos x (h.2.2.2.1 hx)
  obtain ⟨hΔ, hg, hH⟩ := hpt w hwΩ
  obtain ⟨hcs, hbs⟩ := (eq_adjoint Ω Ωs hJ D ε' aUp bUp c h).2 w hw
  have hA := s05_adm_point h hposD (i := 0) (i' := 0) (by norm_num) (by norm_num) hw
  have hnn : ∀ {k : ℕ} (T : TensorField k), 0 ≤ rhoTensorNorm Ω T w := fun T =>
    div_nonneg (Real.sqrt_nonneg _) (pow_nonneg (hposD w hw).le _)
  have hA' : rhoTensorNorm Ω (lowerA Ω aUp - rhoMetricT Ω) w ≤ ε' := by
    have := hnn (rhoIterCovDeriv Ω 0 (lowerB Ω bUp))
    have := abs_nonneg (c w - 2)
    exact (show rhoTensorNorm Ω (rhoIterCovDeriv Ω 0 (lowerA Ω aUp - rhoMetricT Ω)) w ≤ ε' by
      linarith)
  have herr := s05_ellOp_err aUp (adjCoeffB Ω aUp bUp) (adjCoeffC Ω aUp bUp c)
    (intrKernel Ω p) (hposD w hw)
  rw [hΔ] at herr
  have hk0 : 0 < intrKernel Ω p w := by
    rw [hK w hwΩ]; nlinarith [h1 w hwΩ, norm_nonneg (ψ w)]
  have hk1 : intrKernel Ω p w ≤ 1 := by rw [hK w hwΩ]; nlinarith [norm_nonneg (ψ w)]
  have e1 := mul_le_mul hA' hH (hnn _) (hnn _ |>.trans hA')
  have e2 := mul_le_mul hbs hg (hnn _) (by linarith [hnn (lowerB Ω (adjCoeffB Ω aUp bUp))])
  have e3 := mul_le_mul_of_nonneg_right (abs_le.1 hcs).1 hk0.le
  have e4 := mul_le_mul_of_nonneg_right (abs_le.1 hcs).2 hk0.le
  have e5 : intrKernel Ω p w ^ 2 ≤ intrKernel Ω p w := by nlinarith
  have herr' := abs_le.1 herr
  unfold ellOpAdj
  constructor <;> nlinarith [sq_nonneg (intrKernel Ω p w)]

/-- Helper (P2): trace and Hilbert–Schmidt sum of a `2`-tensor of the form
`T(X, Y) = a Re(Y X̄) + b Re(Q X Y)`. -/
theorem s05_frame_quad (T : TensorField 2) (w : ℂ) (a b : ℝ) (Q : ℂ)
    (h : ∀ X Y, T w ![X, Y] = a * (Y * conj X).re + b * (Q * X * Y).re) :
    ∑ i : Fin 2, T w ![frameVec i, frameVec i] = 2 * a ∧
      ∑ p : Fin 2 × Fin 2, (T w ![frameVec p.1, frameVec p.2]) ^ 2 =
        2 * a ^ 2 + 2 * b ^ 2 * ‖Q‖ ^ 2 := by
  have f0 : frameVec 0 = 1 := rfl
  have f1 : frameVec 1 = I := rfl
  rw [Complex.sq_norm, normSq_apply]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, h, f0, f1, mul_re, mul_im, conj_re, conj_im,
    one_re, one_im, I_re, I_im]
  constructor <;> ring

/-- Helper (P2): chain rule for `∇²(G ∘ u) = G''(u) du ⊗ du + G'(u) ∇²u`. -/
theorem s05_rhoHess_comp {Ω : Set ℂ} {u : ℂ → ℝ} {G G' G'' : ℝ → ℝ} {w : ℂ}
    (hu : ∀ᶠ x in 𝓝 w, DifferentiableAt ℝ u x)
    (hu2 : ∀ Y, DifferentiableAt ℝ (fun x => fderiv ℝ u x Y) w)
    (hG : ∀ᶠ x in 𝓝 w, HasDerivAt G (G' (u x)) (u x)) (hG' : HasDerivAt G' (G'' (u w)) (u w)) :
    (∀ Y, fderiv ℝ (G ∘ u) w Y = G' (u w) * fderiv ℝ u w Y) ∧
    ∀ X Y, rhoHess Ω (G ∘ u) w ![X, Y] =
      G'' (u w) * fderiv ℝ u w X * fderiv ℝ u w Y + G' (u w) * rhoHess Ω u w ![X, Y] := by
  have hd : ∀ᶠ x in 𝓝 w, ∀ Y, fderiv ℝ (G ∘ u) x Y = G' (u x) * fderiv ℝ u x Y := by
    filter_upwards [hu, hG] with x hx hGx
    intro Y
    rw [(hGx.comp_hasFDerivAt x hx.hasFDerivAt).fderiv]
    simp
  refine ⟨hd.self_of_nhds, fun X Y => ?_⟩
  have hE : (fun x => fderiv ℝ (G ∘ u) x Y) =ᶠ[𝓝 w] fun x => G' (u x) * fderiv ℝ u x Y :=
    hd.mono fun x hx => hx Y
  have hGu : HasFDerivAt (fun x => G' (u x)) (G'' (u w) • fderiv ℝ u w) w :=
    hG'.comp_hasFDerivAt w hu.self_of_nhds.hasFDerivAt
  rw [s05_rhoHess_eq, s05_rhoHess_eq,
    ((hGu.mul (hu2 Y).hasFDerivAt).congr_of_eventuallyEq hE).fderiv, hd.self_of_nhds]
  simp
  ring

/-- Helper (P2): `d_ρ(x, ℓ) = d_ρ(ℓ, x) ≥ 0` for every `x` (off `Ω` both are `sInf ∅ = 0`). -/
theorem s05_tfb_dist {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {ℓ : ℂ} (hℓ : ℓ ∈ Ω) (x : ℂ) :
    poincareDist Ω x ℓ = poincareDist Ω ℓ x ∧ 0 ≤ poincareDist Ω ℓ x := by
  have hΩ := s02_jordanPair_riemannMap hJ
  by_cases hx : x ∈ Ω
  · exact ⟨s02_poincareDist_comm hΩ hx hℓ, s02_poincareDist_nonneg hΩ hℓ hx⟩
  have e1 : {d : ℝ | ∃ (f : ℂ → ℂ) (a z : ℂ), IsConformalOnto f unitDisc Ω ∧ a ∈ unitDisc ∧
      z ∈ unitDisc ∧ f a = x ∧ f z = ℓ ∧ d = diskDist a z} = ∅ := by
    ext d
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨f, a, z, hf, ha, -, hfa, -⟩
    exact hx (hfa ▸ hf.mapsTo ha)
  have e2 : {d : ℝ | ∃ (f : ℂ → ℂ) (a z : ℂ), IsConformalOnto f unitDisc Ω ∧ a ∈ unitDisc ∧
      z ∈ unitDisc ∧ f a = ℓ ∧ f z = x ∧ d = diskDist a z} = ∅ := by
    ext d
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨f, a, z, hf, -, hz, -, hfz, -⟩
    exact hx (hfz ▸ hf.mapsTo hz)
  unfold poincareDist
  rw [e1, e2, Real.sInf_empty]
  exact ⟨rfl, le_rfl⟩

/-- Helper (P2): `e^{-3d/2} = ((1 - √(1 - k))/√k)³` for `k = sech²(d/2)`, `d ≥ 0`. -/
theorem s05_tfb_G_eq {d : ℝ} (hd : 0 ≤ d) :
    ((1 - √(1 - ((Real.cosh (d / 2))⁻¹) ^ 2)) / √(((Real.cosh (d / 2))⁻¹) ^ 2)) ^ 3 =
      Real.exp (-(3 / 2) * d) := by
  have hc := Real.cosh_pos (d / 2)
  have hsh : 0 ≤ Real.sinh (d / 2) := Real.sinh_nonneg_iff.2 (by linarith)
  have e1 : 1 - ((Real.cosh (d / 2))⁻¹) ^ 2 = (Real.sinh (d / 2) / Real.cosh (d / 2)) ^ 2 := by
    field_simp
    rw [Real.cosh_sq]
    ring
  rw [Real.sqrt_sq (inv_nonneg.2 hc.le), e1, Real.sqrt_sq (div_nonneg hsh hc.le)]
  have e2 : (1 - Real.sinh (d / 2) / Real.cosh (d / 2)) / (Real.cosh (d / 2))⁻¹ =
      Real.exp (-(d / 2)) := by
    rw [← Real.cosh_sub_sinh]
    field_simp
  rw [e2, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Helper (P2): `G(k) = ((1 - √(1-k))/√k)³` has `G'(k) = 3G(k)/(2√(1-k) k)` on `(0, 1)`. -/
theorem s05_tfb_G1 {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    HasDerivAt (fun k => ((1 - √(1 - k)) / √k) ^ 3)
      (3 * ((1 - √(1 - t)) / √t) ^ 3 / (2 * √(1 - t) * t)) t := by
  have hr0 : 0 < 1 - t := by linarith
  have hr : HasDerivAt (fun k => √(1 - k)) (-1 / (2 * √(1 - t))) t :=
    ((hasDerivAt_id' t).const_sub 1).sqrt hr0.ne'
  have hs : HasDerivAt (fun k => √k) (1 / (2 * √t)) t := (hasDerivAt_id' t).sqrt h0.ne'
  have hE := (((hasDerivAt_const t (1 : ℝ)).sub hr).div hs (Real.sqrt_pos.2 h0).ne').pow 3
  convert hE using 1
  simp only [Pi.sub_apply, Pi.div_apply, Nat.cast_ofNat]
  have hR := Real.sqrt_pos.2 hr0
  have hS := Real.sqrt_pos.2 h0
  have hR2 := Real.sq_sqrt hr0.le
  have hS2 := Real.sq_sqrt h0.le
  generalize √(1 - t) = R at hR hR2 ⊢
  generalize √t = S at hS hS2 ⊢
  have hRS : R ^ 2 + S ^ 2 = 1 := by linarith
  have hS0 : S ≠ 0 := hS.ne'
  have hR0 : R ≠ 0 := hR.ne'
  rw [← hS2]
  field_simp
  have hinv : S⁻¹ ^ 2 * S ^ 2 = 1 := by field_simp
  linear_combination (R + 2 * R * S ^ 2 - 3 * R ^ 2 - R ^ 2 * S ^ 2 + 3 * R ^ 3 - R ^ 4 - S ^ 2) *
    hinv + (2 * R - R ^ 2 - 1) * hRS

/-- Helper (P2): `G'(k) = 3G(k)/(2rk)` (`r = √(1-k)`) has derivative
`G''(k) = 3G(k)(1 + 3r - 3r²)/(4r³k²)` on `(0, 1)`. -/
theorem s05_tfb_G2 {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    HasDerivAt (fun k => 3 * ((1 - √(1 - k)) / √k) ^ 3 / (2 * √(1 - k) * k))
      (3 * ((1 - √(1 - t)) / √t) ^ 3 * (1 + 3 * √(1 - t) - 3 * √(1 - t) ^ 2) /
        (4 * √(1 - t) ^ 3 * t ^ 2)) t := by
  have hr0 : 0 < 1 - t := by linarith
  have hr : HasDerivAt (fun k => √(1 - k)) (-1 / (2 * √(1 - t))) t :=
    ((hasDerivAt_id' t).const_sub 1).sqrt hr0.ne'
  have hR := Real.sqrt_pos.2 hr0
  have hD := ((s05_tfb_G1 h0 h1).const_mul 3).div ((hr.const_mul 2).mul (hasDerivAt_id' t))
    (mul_pos (mul_pos two_pos hR) h0).ne'
  convert hD using 1
  simp only [Pi.mul_apply]
  have hR2 := Real.sq_sqrt hr0.le
  generalize ((1 - √(1 - t)) / √t) ^ 3 = g
  generalize √(1 - t) = R at hR hR2 ⊢
  have ht : t = 1 - R ^ 2 := by linarith
  subst ht
  field_simp
  ring

/-- Helper (P2): the bounds `Δ_ρφ ≤ (3/4)φ`, `‖∇φ‖ ≤ (3/2)φ`, `‖∇²φ‖ ≤ 4φ` for `φ = G ∘ k_ℓ` from
the frame formulas (`r = |z| ≥ 1/2`, `k = 1 - r²`, `p₁ = G'(k)`, `p₂ = G''(k)`). -/
theorem s05_tfb_frame {Ω : Set ℂ} {Φ : ℂ → ℝ} {w z α : ℂ} {φ p1 p2 : ℝ} (hα : α ≠ 0)
    (hz1 : ‖z‖ < 1) (hz2 : 1 / 2 ≤ ‖z‖) (hφ : 0 < φ)
    (hp1 : 2 * ‖z‖ * (1 - ‖z‖ ^ 2) * p1 = 3 * φ)
    (hp2 : 4 * ‖z‖ ^ 3 * (1 - ‖z‖ ^ 2) ^ 2 * p2 = 3 * φ * (1 + 3 * ‖z‖ - 3 * ‖z‖ ^ 2))
    (hl : poincareDensity Ω w = 2 * ‖α‖ / (1 - ‖z‖ ^ 2))
    (hd : ∀ Y, fderiv ℝ Φ w Y = p1 * (-2 * (Y * α * conj z).re))
    (hH : ∀ X Y, rhoHess Ω Φ w ![X, Y] =
      p2 * (-2 * (X * α * conj z).re) * (-2 * (Y * α * conj z).re) +
        p1 * (-2 * ‖α‖ ^ 2 * (Y * conj X).re +
          4 / (1 - ‖z‖ ^ 2) * (conj z ^ 2 * α ^ 2 * X * Y).re)) :
    rhoLaplacian Ω Φ w ≤ 3 / 4 * φ ∧
      rhoTensorNorm Ω (rhoCovDeriv Ω (scalarField Φ)) w ≤ 3 / 2 * φ ∧
      rhoTensorNorm Ω (rhoHess Ω Φ) w ≤ 4 * φ := by
  have hk : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have ha : 0 < ‖α‖ := norm_pos_iff.2 hα
  have hr : 0 < ‖z‖ := by linarith
  have hL : 0 < poincareDensity Ω w := by rw [hl]; positivity
  have hp1pos : 0 < p1 :=
    pos_of_mul_pos_right (hp1 ▸ (by positivity : (0 : ℝ) < 3 * φ)) (by positivity)
  have hn : ‖α‖ ^ 2 = α.re ^ 2 + α.im ^ 2 := by rw [Complex.sq_norm, normSq_apply]; ring
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, normSq_apply]; ring
  have f0 : frameVec 0 = 1 := rfl
  have f1 : frameVec 1 = I := rfl
  have hq := s05_frame_quad (rhoHess Ω Φ) w (2 * p2 * ‖α‖ ^ 2 * ‖z‖ ^ 2 - 2 * p1 * ‖α‖ ^ 2)
    (2 * p2 + 4 * p1 / (1 - ‖z‖ ^ 2)) (conj z ^ 2 * α ^ 2) fun X Y => by
      rw [hH, hn, hz]
      simp only [mul_re, mul_im, conj_re, conj_im, pow_two]
      ring
  -- `L = Δ_ρφ` and the half-difference `M` of the eigenvalues of `∇²φ`
  obtain ⟨L, hLdef⟩ : ∃ L, L = (1 - ‖z‖ ^ 2) ^ 2 * (p2 * ‖z‖ ^ 2 - p1) := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = ((1 - ‖z‖ ^ 2) ^ 2 * p2 * ‖z‖ ^ 2 +
      2 * (1 - ‖z‖ ^ 2) * p1 * ‖z‖ ^ 2) / 2 := ⟨_, rfl⟩
  have hLr : 4 * ‖z‖ * L = 3 * φ * (3 * ‖z‖ - 1 - ‖z‖ ^ 2) := by
    rw [hLdef]; linear_combination hp2 - 2 * (1 - ‖z‖ ^ 2) * hp1
  have hMr : 8 * ‖z‖ * M = 3 * φ * (1 + 3 * ‖z‖ + ‖z‖ ^ 2) := by
    rw [hMdef]; linear_combination hp2 + 4 * ‖z‖ ^ 2 * hp1
  have h4r : 0 < 4 * ‖z‖ := by positivity
  have h8r : 0 < 8 * ‖z‖ := by positivity
  have hL1 : L ≤ 3 / 4 * φ := by
    refine le_of_mul_le_mul_left ?_ h4r
    rw [hLr]
    nlinarith [mul_nonneg hφ.le (sq_nonneg (‖z‖ - 1))]
  have hL0 : 0 ≤ L := by
    refine le_of_mul_le_mul_left ?_ h4r
    rw [hLr, mul_zero]
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ ‖z‖ - 1 / 2) (by linarith : (0 : ℝ) ≤ 5 / 2 - ‖z‖)
    exact mul_nonneg (by positivity) (by nlinarith)
  have hM0 : 0 ≤ M := by
    refine le_of_mul_le_mul_left ?_ h8r
    rw [hMr, mul_zero]
    positivity
  have hM1 : M ≤ 33 / 16 * φ := by
    refine le_of_mul_le_mul_left ?_ h8r
    rw [hMr]
    nlinarith [mul_nonneg hφ.le (mul_nonneg (by linarith : (0 : ℝ) ≤ ‖z‖ - 1 / 2)
      (by linarith : (0 : ℝ) ≤ 2 - ‖z‖))]
  have eA : 2 * p2 * ‖α‖ ^ 2 * ‖z‖ ^ 2 - 2 * p1 * ‖α‖ ^ 2 = poincareDensity Ω w ^ 2 * L / 2 := by
    rw [hl, hLdef]; field_simp
  have eB : (2 * p2 + 4 * p1 / (1 - ‖z‖ ^ 2)) * (‖z‖ ^ 2 * ‖α‖ ^ 2) =
      poincareDensity Ω w ^ 2 * M := by
    rw [hl, hMdef]; field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [rhoLaplacian, hq.1, show 2 * (2 * p2 * ‖α‖ ^ 2 * ‖z‖ ^ 2 - 2 * p1 * ‖α‖ ^ 2) =
      poincareDensity Ω w ^ 2 * L by rw [eA]; ring, mul_div_cancel_left₀ _ (by positivity)]
    exact hL1
  · show rhoTensorNorm Ω (k := 1) (rhoCovDeriv Ω (scalarField Φ)) w ≤ 3 / 2 * φ
    have hg : ∀ i : Fin 2, rhoCovDeriv Ω (scalarField Φ) w ![frameVec i] =
        fderiv ℝ Φ w (frameVec i) := fun i => by rw [s05_covDeriv_scalar]; rfl
    unfold rhoTensorNorm
    rw [s05_hs_one, div_le_iff₀ (pow_pos hL 1)]
    simp only [Fin.sum_univ_two, hg, hd, f0, f1]
    rw [pow_one, show 3 / 2 * φ * poincareDensity Ω w = 2 * ‖z‖ * p1 * ‖α‖ by
      rw [hl, show φ = 2 * ‖z‖ * (1 - ‖z‖ ^ 2) * p1 / 3 by linarith]; field_simp]
    refine (Real.sqrt_le_left (by positivity)).2 (le_of_eq ?_)
    rw [show (2 * ‖z‖ * p1 * ‖α‖) ^ 2 = 4 * p1 ^ 2 * ‖α‖ ^ 2 * ‖z‖ ^ 2 by ring, hn, hz]
    simp only [mul_re, mul_im, conj_re, conj_im, one_re, one_im, I_re, I_im]
    ring
  · show rhoTensorNorm Ω (k := 2) (rhoHess Ω Φ) w ≤ 4 * φ
    unfold rhoTensorNorm
    rw [s05_hs_two, hq.2, div_le_iff₀ (pow_pos hL 2)]
    refine (Real.sqrt_le_left (by positivity)).2 ?_
    have hP : ‖conj z ^ 2 * α ^ 2‖ = ‖z‖ ^ 2 * ‖α‖ ^ 2 := by
      rw [norm_mul, norm_pow, norm_pow, Complex.norm_conj]
    rw [hP, show ∀ A B q : ℝ, 2 * A ^ 2 + 2 * B ^ 2 * q ^ 2 = 2 * A ^ 2 + 2 * (B * q) ^ 2 by
      intros; ring, eA, eB]
    have h1' := pow_le_pow_left₀ hL0 hL1 2
    have h2' := pow_le_pow_left₀ hM0 hM1 2
    have hb : L ^ 2 / 2 + 2 * M ^ 2 ≤ 16 * φ ^ 2 := by
      linarith [show (3 / 4 * φ) ^ 2 = 9 / 16 * φ ^ 2 by ring,
        show (33 / 16 * φ) ^ 2 = 1089 / 256 * φ ^ 2 by ring, sq_nonneg φ]
    calc _ = (poincareDensity Ω w ^ 2) ^ 2 * (L ^ 2 / 2 + 2 * M ^ 2) := by ring
      _ ≤ (poincareDensity Ω w ^ 2) ^ 2 * (16 * φ ^ 2) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring

/-- **Lemma 5.3 (b)** (`lem:test-functions`, sec05-upper.tex:166).  For `ℓ ∈ Ω`, `β = 3/2` and
`φ_ℓ = e^{-β d_ρ(·, ℓ)}`: on `D ∩ {d_ρ(·, ℓ) > 2}`, `|∇φ_ℓ| ≤ βφ_ℓ`, `|∇²φ_ℓ| ≤ 4φ_ℓ` and
`𝓛φ_ℓ ≥ (5/4 - C₀ε') φ_ℓ ≥ φ_ℓ` (5.10).  [REPAIR, see `FALSE_w2.md`: the last inequality needs
`C₀ε' ≤ 1/4`, which `ε' ≤ 1/8` does not give; it is stated under that hypothesis (in the paper's
application `C₀ε' ≤ 1/8`).] -/
theorem lem_test_functions_b : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (D : Set ℂ) (ε' : ℝ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsAdmissibleOp Ω D ε' aUp bUp c → ∀ ℓ ∈ Ω, ∀ w ∈ D, 2 < poincareDist Ω w ℓ →
      rhoTensorNorm Ω (rhoCovDeriv Ω (scalarField fun x =>
          Real.exp (-(3 / 2) * poincareDist Ω x ℓ))) w ≤
          3 / 2 * Real.exp (-(3 / 2) * poincareDist Ω w ℓ) ∧
      rhoTensorNorm Ω (rhoHess Ω fun x => Real.exp (-(3 / 2) * poincareDist Ω x ℓ)) w ≤
          4 * Real.exp (-(3 / 2) * poincareDist Ω w ℓ) ∧
      (5 / 4 - 11 * ε') * Real.exp (-(3 / 2) * poincareDist Ω w ℓ) ≤
          ellOp Ω aUp bUp c (fun x => Real.exp (-(3 / 2) * poincareDist Ω x ℓ)) w ∧
      (11 * ε' ≤ 1 / 4 → Real.exp (-(3 / 2) * poincareDist Ω w ℓ) ≤
          (5 / 4 - 11 * ε') * Real.exp (-(3 / 2) * poincareDist Ω w ℓ)) := by
  intro Ω Ωs hJ D ε' aUp bUp c h ℓ hℓ w hw hd2
  have hΩ := s05_jordan_isOpen hJ
  have hwΩ : w ∈ Ω := h.2.2.2.1 hw
  obtain ⟨ψ, hψ, h1, h0, hK, hl⟩ := s05_kernel_riemann hJ hℓ
  -- `φ_ℓ = G ∘ k_ℓ` with `G(k) = ((1 - √(1-k))/√k)³`
  have hΦ : (fun x => Real.exp (-(3 / 2) * poincareDist Ω x ℓ)) =
      (fun k => ((1 - √(1 - k)) / √k) ^ 3) ∘ intrKernel Ω ℓ := by
    funext x
    obtain ⟨hs, hn⟩ := s05_tfb_dist hJ hℓ x
    simp only [Function.comp, intrKernel]
    rw [hs, s05_tfb_G_eq hn]
  have hKpos : ∀ x ∈ Ω, 0 < intrKernel Ω ℓ x := fun x hx => by
    rw [hK x hx]; nlinarith [h1 x hx, norm_nonneg (ψ x)]
  have hKs : ContDiffOn ℝ ∞ (intrKernel Ω ℓ) Ω :=
    (contDiffOn_const.sub (((hψ.contDiffOn hΩ).restrict_scalars ℝ).norm_sq ℝ)).congr hK
  -- `d_ρ(w, ℓ) > 2` gives `k_ℓ(w) ≤ 3/4`, i.e. `|ψ(w)| ≥ 1/2`
  have hK34 : intrKernel Ω ℓ w ≤ 3 / 4 := by
    rw [intrKernel, ← (s05_tfb_dist hJ hℓ w).1]
    have hc : 6 / 5 ≤ Real.cosh (poincareDist Ω w ℓ / 2) := by
      rw [Real.cosh_eq]
      have := Real.exp_le_exp.2 (show (1 : ℝ) ≤ poincareDist Ω w ℓ / 2 by linarith)
      have := Real.exp_one_gt_d9
      have := Real.exp_pos (-(poincareDist Ω w ℓ / 2))
      linarith
    rw [inv_pow]
    calc (Real.cosh (poincareDist Ω w ℓ / 2) ^ 2)⁻¹ ≤ (36 / 25)⁻¹ :=
          inv_anti₀ (by norm_num) (by nlinarith)
      _ ≤ 3 / 4 := by norm_num
  have hkw := hK w hwΩ
  have hz1 := h1 w hwΩ
  have hz2 : 1 / 2 ≤ ‖ψ w‖ := by nlinarith [norm_nonneg (ψ w)]
  have hKw0 := hKpos w hwΩ
  have hKw1 : intrKernel Ω ℓ w < 1 := by linarith
  have hr : √(1 - intrKernel Ω ℓ w) = ‖ψ w‖ := by
    rw [hkw, sub_sub_cancel, Real.sqrt_sq (norm_nonneg _)]
  have hKc : ContinuousAt (intrKernel Ω ℓ) w := hKs.continuousOn.continuousAt (hΩ.mem_nhds hwΩ)
  have hc := s05_rhoHess_comp (Ω := Ω) (u := intrKernel Ω ℓ)
    (G := fun k => ((1 - √(1 - k)) / √k) ^ 3)
    (G' := fun k => 3 * ((1 - √(1 - k)) / √k) ^ 3 / (2 * √(1 - k) * k))
    (G'' := fun k => 3 * ((1 - √(1 - k)) / √k) ^ 3 * (1 + 3 * √(1 - k) - 3 * √(1 - k) ^ 2) /
      (4 * √(1 - k) ^ 3 * k ^ 2))
    (Filter.mem_of_superset (hΩ.mem_nhds hwΩ) fun x hx =>
      (hKs.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp))
    (fun Y => (((hKs.contDiffAt (hΩ.mem_nhds hwΩ)).fderiv_right (m := ∞)
      (le_of_eq ENat.coe_top_add_one)).differentiableAt (by simp)).clm_apply
        (differentiableAt_const Y))
    (by
      filter_upwards [hΩ.mem_nhds hwΩ, hKc.eventually_lt continuousAt_const hKw1] with x hx hx1
      exact s05_tfb_G1 (hKpos x hx) hx1)
    (s05_tfb_G2 hKw0 hKw1)
  have hD := s05_kernel_derivs hΩ hψ h1 h0 hK hl hwΩ
  have hkpos : 0 < 1 - ‖ψ w‖ ^ 2 := by rw [← hkw]; exact hKw0
  have hRpos : 0 < √(1 - ‖ψ w‖ ^ 2) := Real.sqrt_pos.2 hkpos
  have hφpos : 0 < ((1 - √(1 - intrKernel Ω ℓ w)) / √(intrKernel Ω ℓ w)) ^ 3 := by
    rw [hr]
    exact pow_pos (div_pos (by linarith) (Real.sqrt_pos.2 hKw0)) 3
  have hfr := s05_tfb_frame (Φ := (fun k => ((1 - √(1 - k)) / √k) ^ 3) ∘ intrKernel Ω ℓ)
    (h0 w hwΩ) hz1 hz2 hφpos
    (p1 := 3 * ((1 - √(1 - intrKernel Ω ℓ w)) / √(intrKernel Ω ℓ w)) ^ 3 /
      (2 * √(1 - intrKernel Ω ℓ w) * intrKernel Ω ℓ w))
    (p2 := 3 * ((1 - √(1 - intrKernel Ω ℓ w)) / √(intrKernel Ω ℓ w)) ^ 3 *
      (1 + 3 * √(1 - intrKernel Ω ℓ w) - 3 * √(1 - intrKernel Ω ℓ w) ^ 2) /
      (4 * √(1 - intrKernel Ω ℓ w) ^ 3 * intrKernel Ω ℓ w ^ 2))
    (by rw [hr, hkw]; field_simp) (by rw [hr, hkw]; field_simp) (hl w hwΩ)
    (fun Y => by rw [hc.1, hD.1]) (fun X Y => by rw [hc.2, hD.1, hD.1, hD.2])
  obtain ⟨hΔ, hgN, hHN⟩ := hfr
  have hφw : Real.exp (-(3 / 2) * poincareDist Ω w ℓ) =
      ((1 - √(1 - intrKernel Ω ℓ w)) / √(intrKernel Ω ℓ w)) ^ 3 := congrFun hΦ w
  rw [hΦ, hφw]
  generalize hφdef : ((1 - √(1 - intrKernel Ω ℓ w)) / √(intrKernel Ω ℓ w)) ^ 3 = φ at hφpos hΔ hgN hHN
  refine ⟨hgN, hHN, ?_, fun _ => by nlinarith⟩
  obtain ⟨-, -, hpos⟩ := s05_density_smooth hJ
  have hposD : ∀ x ∈ D, 0 < poincareDensity Ω x := fun x hx => hpos x (h.2.2.2.1 hx)
  have hnn : ∀ {k : ℕ} (T : TensorField k), 0 ≤ rhoTensorNorm Ω T w := fun T =>
    div_nonneg (Real.sqrt_nonneg _) (pow_nonneg (hposD w hw).le _)
  have hA : rhoTensorNorm Ω (lowerA Ω aUp - rhoMetricT Ω) w +
      rhoTensorNorm Ω (lowerB Ω bUp) w + |c w - 2| ≤ ε' :=
    s05_adm_point h hposD (i := 0) (i' := 0) (by norm_num) (by norm_num) hw
  have hε := h.1
  have hnA := hnn (lowerA Ω aUp - rhoMetricT Ω)
  have hnB := hnn (lowerB Ω bUp)
  have hnH := hnn (rhoHess Ω ((fun k => ((1 - √(1 - k)) / √k) ^ 3) ∘ intrKernel Ω ℓ))
  have hng := hnn (rhoCovDeriv Ω (scalarField
    ((fun k => ((1 - √(1 - k)) / √k) ^ 3) ∘ intrKernel Ω ℓ)))
  have habs := abs_nonneg (c w - 2)
  have hc1 := (abs_le.1 (show |c w - 2| ≤ ε' by linarith)).1
  have e1 := s05_ellOp_err aUp bUp c ((fun k => ((1 - √(1 - k)) / √k) ^ 3) ∘ intrKernel Ω ℓ)
    (hposD w hw)
  rw [show ((fun k => ((1 - √(1 - k)) / √k) ^ 3) ∘ intrKernel Ω ℓ) w = φ from hφdef] at e1
  have q1 := mul_le_mul (show rhoTensorNorm Ω (lowerA Ω aUp - rhoMetricT Ω) w ≤ ε' by linarith)
    hHN hnH hε.le
  have q2 := mul_le_mul (show rhoTensorNorm Ω (lowerB Ω bUp) w ≤ ε' by linarith) hgN hng hε.le
  have q3 := mul_le_mul_of_nonneg_right hc1 hφpos.le
  have q4 := mul_pos hε hφpos
  have e1' := (abs_le.1 e1).1
  nlinarith

/-- Helper (P2): the bounds `Δ_ρΨ ≤ (3/4)Ψ`, `‖∇Ψ‖ ≤ Ψ/2`, `‖∇²Ψ‖ ≤ Ψ` for `Ψ = cosh(d_ρ/2)`
from its frame formulas (`s = Ψ(w) = (1 - |z|²)^{-1/2}`). -/
theorem s05_cosh_frame {Ω : Set ℂ} {Ψ : ℂ → ℝ} {w z α : ℂ} {s : ℝ} (hα : α ≠ 0)
    (hs : 0 < s) (hsk : s ^ 2 * (1 - ‖z‖ ^ 2) = 1)
    (hl : poincareDensity Ω w = 2 * ‖α‖ / (1 - ‖z‖ ^ 2))
    (hd : ∀ Y, fderiv ℝ Ψ w Y = s ^ 3 * (Y * α * conj z).re)
    (hH : ∀ X Y, rhoHess Ω Ψ w ![X, Y] =
      ‖α‖ ^ 2 * s ^ 3 * (1 + 3 / 2 * s ^ 2 * ‖z‖ ^ 2) * (Y * conj X).re +
        -(s ^ 5 / 2) * (conj z ^ 2 * α ^ 2 * X * Y).re) :
    rhoLaplacian Ω Ψ w ≤ 3 / 4 * s ∧
      rhoTensorNorm Ω (rhoCovDeriv Ω (scalarField Ψ)) w ≤ s / 2 ∧
      rhoTensorNorm Ω (rhoHess Ω Ψ) w ≤ s := by
  have hk : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have ha : 0 < ‖α‖ := norm_pos_iff.2 hα
  have hl' : poincareDensity Ω w = 2 * ‖α‖ * s ^ 2 := by
    rw [hl, div_eq_iff hk.ne']
    linear_combination (-(2 * ‖α‖)) * hsk
  have hL : 0 < poincareDensity Ω w := by rw [hl']; positivity
  have hZ0 : 0 ≤ ‖z‖ ^ 2 := by positivity
  have hs1 : 1 ≤ s ^ 2 := by nlinarith
  have hq := s05_frame_quad (rhoHess Ω Ψ) w _ _ _ hH
  have f0 : frameVec 0 = 1 := rfl
  have f1 : frameVec 1 = I := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [rhoLaplacian, hq.1, hl', div_le_iff₀ (by positivity)]
    have e : 3 / 4 * s * (2 * ‖α‖ * s ^ 2) ^ 2 -
        2 * (‖α‖ ^ 2 * s ^ 3 * (1 + 3 / 2 * s ^ 2 * ‖z‖ ^ 2)) = ‖α‖ ^ 2 * s ^ 3 := by
      linear_combination (3 * ‖α‖ ^ 2 * s ^ 3) * hsk
    nlinarith [pow_pos ha 2, pow_pos hs 3]
  · show rhoTensorNorm Ω (k := 1) (rhoCovDeriv Ω (scalarField Ψ)) w ≤ s / 2
    have hg : ∀ i : Fin 2, rhoCovDeriv Ω (scalarField Ψ) w ![frameVec i] =
        fderiv ℝ Ψ w (frameVec i) := fun i => by rw [s05_covDeriv_scalar]; rfl
    unfold rhoTensorNorm
    rw [s05_hs_one, div_le_iff₀ (pow_pos hL 1)]
    simp only [Fin.sum_univ_two, hg, hd, f0, f1]
    rw [hl', pow_one, show s / 2 * (2 * ‖α‖ * s ^ 2) = ‖α‖ * s ^ 3 by ring]
    refine (Real.sqrt_le_left (by positivity)).2 ?_
    have hn : ‖α‖ ^ 2 = α.re ^ 2 + α.im ^ 2 := by rw [Complex.sq_norm, normSq_apply]; ring
    have hz2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, normSq_apply]; ring
    have hZ : z.re ^ 2 + z.im ^ 2 ≤ 1 := by rw [← hz2]; linarith
    rw [show (‖α‖ * s ^ 3) ^ 2 = (s ^ 3) ^ 2 * ‖α‖ ^ 2 by ring, hn]
    simp only [mul_re, mul_im, conj_re, conj_im, one_re, one_im, I_re, I_im]
    calc _ = (s ^ 3) ^ 2 * (α.re ^ 2 + α.im ^ 2) * (z.re ^ 2 + z.im ^ 2) := by ring
      _ ≤ (s ^ 3) ^ 2 * (α.re ^ 2 + α.im ^ 2) * 1 := by gcongr
      _ = _ := by ring
  · show rhoTensorNorm Ω (k := 2) (rhoHess Ω Ψ) w ≤ s
    unfold rhoTensorNorm
    rw [s05_hs_two, hq.2, div_le_iff₀ (pow_pos hL 2), hl']
    refine (Real.sqrt_le_left (by positivity)).2 ?_
    have hP : ‖conj z ^ 2 * α ^ 2‖ = ‖z‖ ^ 2 * ‖α‖ ^ 2 := by
      rw [norm_mul, norm_pow, norm_pow, Complex.norm_conj]
    rw [hP]
    have h1 : 1 + 3 / 2 * s ^ 2 * ‖z‖ ^ 2 ≤ 5 / 2 * s ^ 2 := by nlinarith
    have h2 : (1 + 3 / 2 * s ^ 2 * ‖z‖ ^ 2) ^ 2 ≤ (5 / 2 * s ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h3 : (‖z‖ ^ 2) ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * (‖α‖ ^ 2) ^ 2 * s ^ 6),
      mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ (‖α‖ ^ 2) ^ 2 * s ^ 10 / 2),
      (by positivity : (0 : ℝ) ≤ (‖α‖ ^ 2) ^ 2 * s ^ 10)]

/-- Helper (P2): the sublevel sets of `cosh(d_ρ(o, ·)/2)` in `Ω` are compact. -/
theorem s05_cosh_proper {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {o : ℂ} (ho : o ∈ Ω) (M : ℝ) :
    IsCompact {x | x ∈ Ω ∧ Real.cosh (poincareDist Ω o x / 2) ≤ M} := by
  have hΩ := s05_jordan_isOpen hJ
  obtain ⟨φ, hφ⟩ := s05_jordan_riemann hJ
  have ha : ‖φ o‖ < 1 := mem_ball_zero_iff.mp (hφ.mapsTo ho)
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℂ → ℂ, ψ = blaschke (φ o) ∘ φ := ⟨_, rfl⟩
  have hψ : IsConformalOnto ψ Ω unitDisc := hψdef ▸ (isConformalOnto_blaschke ha).comp hφ
  have hf := hψ.symm hΩ
  obtain ⟨f, hfdef⟩ : ∃ f : ℂ → ℂ, f = Function.invFunOn ψ Ω := ⟨_, rfl⟩
  rw [← hfdef] at hf
  have hfψ : ∀ x ∈ Ω, f (ψ x) = x := fun x hx => hfdef ▸ hψ.2.1.leftInvOn_invFunOn hx
  have hψf : ∀ z ∈ unitDisc, ψ (f z) = z := fun z hz => by
    have hz' : z ∈ ψ '' Ω := by rw [hψ.2.2]; exact hz
    rw [hfdef]; exact Function.invFunOn_eq hz'
  have hf0 : f 0 = o := by
    have h0 : ψ o = 0 := by rw [hψdef]; exact blaschke_self _
    rw [← h0]; exact hfψ o ho
  -- `cosh(d(o, f z)/2) = (1 - |z|²)^{-1/2}`
  have hc : ∀ z ∈ unitDisc, Real.cosh (poincareDist Ω o (f z) / 2) =
      (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ := by
    intro z hz
    have hk := s02_intrKernel_eq hf (a := 0) (mem_ball_self one_pos) hz
    rw [hf0] at hk
    simp only [norm_zero, map_zero, zero_mul, sub_zero, norm_one, one_pow, div_one, one_mul,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hk
    rw [← hk, intrKernel, Real.sqrt_sq (inv_nonneg.2 (Real.cosh_pos _).le), inv_inv]
  by_cases hM : 0 < M
  · have hT : IsCompact {z : ℂ | (M⁻¹) ^ 2 ≤ 1 - ‖z‖ ^ 2} := by
      refine Metric.isCompact_of_isClosed_isBounded
        (isClosed_le continuous_const (continuous_const.sub (continuous_norm.pow 2))) ?_
      refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset fun z hz => ?_
      have : ‖z‖ ^ 2 ≤ 1 := by have := sq_nonneg M⁻¹; simp only [mem_ofPred_eq] at hz; linarith
      exact mem_closedBall_zero_iff.2 (by nlinarith [norm_nonneg z])
    have hTD : {z : ℂ | (M⁻¹) ^ 2 ≤ 1 - ‖z‖ ^ 2} ⊆ unitDisc := fun z hz => by
      have : 0 < (M⁻¹) ^ 2 := by positivity
      simp only [mem_ofPred_eq] at hz
      refine mem_ball_zero_iff.2 ?_
      nlinarith [norm_nonneg z]
    have hiff : ∀ z ∈ unitDisc, (Real.sqrt (1 - ‖z‖ ^ 2))⁻¹ ≤ M ↔ (M⁻¹) ^ 2 ≤ 1 - ‖z‖ ^ 2 := by
      intro z hz
      have hq : 0 < 1 - ‖z‖ ^ 2 := by
        have := mem_ball_zero_iff.mp hz; nlinarith [norm_nonneg z]
      rw [inv_le_comm₀ (Real.sqrt_pos.2 hq) hM, Real.le_sqrt (inv_nonneg.2 hM.le) hq.le]
    have hEq : {x | x ∈ Ω ∧ Real.cosh (poincareDist Ω o x / 2) ≤ M} =
        f '' {z : ℂ | (M⁻¹) ^ 2 ≤ 1 - ‖z‖ ^ 2} := by
      ext x
      constructor
      · rintro ⟨hx, hle⟩
        have hzD : ψ x ∈ unitDisc := hψ.mapsTo hx
        refine ⟨ψ x, ?_, hfψ x hx⟩
        rw [mem_ofPred_eq, ← hiff _ hzD, ← hc _ hzD, hfψ x hx]
        exact hle
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hf.mapsTo (hTD hz), by rw [hc _ (hTD hz), hiff _ (hTD hz)]; exact hz⟩
    rw [hEq]
    exact hT.image_of_continuousOn (hf.1.continuousOn.mono hTD)
  · have hEq : {x | x ∈ Ω ∧ Real.cosh (poincareDist Ω o x / 2) ≤ M} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
      intro _
      linarith [Real.one_le_cosh (poincareDist Ω o x / 2)]
    rw [hEq]
    exact isCompact_empty

/-- **Lemma 5.3 (c)** (`lem:test-functions`, sec05-upper.tex:172).  For `o ∈ Ω`,
`Ψ_o = cosh(d_ρ(o, ·)/2)` is smooth and proper on `Ω`, and `𝓛Ψ_o > 0`, `𝓛*Ψ_o > 0` on `D`. -/
theorem lem_test_functions_c : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (D : Set ℂ) (ε' : ℝ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsAdmissibleOp Ω D ε' aUp bUp c → ∀ o ∈ Ω,
      ContDiffOn ℝ ∞ (fun x => Real.cosh (poincareDist Ω o x / 2)) Ω ∧
      (∀ M : ℝ, IsCompact {x | x ∈ Ω ∧ Real.cosh (poincareDist Ω o x / 2) ≤ M}) ∧
      ∀ w ∈ D, 0 < ellOp Ω aUp bUp c (fun x => Real.cosh (poincareDist Ω o x / 2)) w ∧
        0 < ellOpAdj Ω aUp bUp c (fun x => Real.cosh (poincareDist Ω o x / 2)) w := by
  intro Ω Ωs hJ D ε' aUp bUp c h o ho
  have hΩ := s05_jordan_isOpen hJ
  obtain ⟨ψ, hψ, h1, h0, hK, hl⟩ := s05_kernel_riemann hJ ho
  have hΨ : (fun x => Real.cosh (poincareDist Ω o x / 2)) =
      (fun t => (Real.sqrt t)⁻¹) ∘ intrKernel Ω o := by
    funext x
    simp only [Function.comp, intrKernel]
    rw [Real.sqrt_sq (inv_nonneg.2 (Real.cosh_pos _).le), inv_inv]
  have hKpos : ∀ x ∈ Ω, 0 < intrKernel Ω o x := fun x hx => by
    rw [hK x hx]; nlinarith [h1 x hx, norm_nonneg (ψ x)]
  have hKs : ContDiffOn ℝ ∞ (intrKernel Ω o) Ω :=
    (contDiffOn_const.sub (((hψ.contDiffOn hΩ).restrict_scalars ℝ).norm_sq ℝ)).congr hK
  refine ⟨?_, s05_cosh_proper hJ ho, fun w hw => ?_⟩
  · rw [hΨ]
    exact (hKs.sqrt fun x hx => (hKpos x hx).ne').inv fun x hx =>
      (Real.sqrt_pos.2 (hKpos x hx)).ne'
  have hwΩ : w ∈ Ω := h.2.2.2.1 hw
  have hD := s05_kernel_derivs hΩ hψ h1 h0 hK hl hwΩ
  -- the one-variable function `G(t) = t^{-1/2}`
  have hGd : ∀ t : ℝ, 0 < t → HasDerivAt (fun t => (Real.sqrt t)⁻¹)
      (-2⁻¹ * ((Real.sqrt t)⁻¹) ^ 3) t := fun t ht => by
    have hs := Real.sqrt_pos.2 ht
    convert (Real.hasDerivAt_sqrt ht.ne').inv hs.ne' using 1
    field_simp
  have hG'd : ∀ t : ℝ, 0 < t → HasDerivAt (fun t => -2⁻¹ * ((Real.sqrt t)⁻¹) ^ 3)
      (3 / 4 * ((Real.sqrt t)⁻¹) ^ 5) t := fun t ht => by
    convert ((hGd t ht).pow 3).const_mul (-2⁻¹ : ℝ) using 1
    push_cast
    ring
  have hc := s05_rhoHess_comp (Ω := Ω) (G'' := fun t => 3 / 4 * ((Real.sqrt t)⁻¹) ^ 5)
    (Filter.mem_of_superset (hΩ.mem_nhds hwΩ) fun x hx =>
      (hKs.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp))
    (fun Y => (((hKs.contDiffAt (hΩ.mem_nhds hwΩ)).fderiv_right (m := ∞)
      (le_of_eq ENat.coe_top_add_one)).differentiableAt (by simp)).clm_apply
        (differentiableAt_const Y))
    (Filter.mem_of_superset (hΩ.mem_nhds hwΩ) fun x hx => hGd _ (hKpos x hx))
    (hG'd _ (hKpos w hwΩ))
  have hkw := hK w hwΩ
  have hk : 0 < 1 - ‖ψ w‖ ^ 2 := by rw [← hkw]; exact hKpos w hwΩ
  have hs : 0 < (Real.sqrt (1 - ‖ψ w‖ ^ 2))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hk)
  have hs2 : ((Real.sqrt (1 - ‖ψ w‖ ^ 2))⁻¹) ^ 2 = (1 - ‖ψ w‖ ^ 2)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hk.le]
  have hsk : ((Real.sqrt (1 - ‖ψ w‖ ^ 2))⁻¹) ^ 2 * (1 - ‖ψ w‖ ^ 2) = 1 := by
    rw [hs2, inv_mul_cancel₀ hk.ne']
  have hfr := s05_cosh_frame (Ψ := (fun t => (Real.sqrt t)⁻¹) ∘ intrKernel Ω o)
    (h0 w hwΩ) hs hsk (hl w hwΩ) (fun Y => by rw [hc.1, hkw, hD.1]; ring) (fun X Y => by
      rw [hc.2, hkw, hD.1, hD.1, hD.2, show 4 / (1 - ‖ψ w‖ ^ 2) =
        4 * ((Real.sqrt (1 - ‖ψ w‖ ^ 2))⁻¹) ^ 2 by rw [hs2]; ring]
      have hn : ‖deriv ψ w‖ ^ 2 = (deriv ψ w).re ^ 2 + (deriv ψ w).im ^ 2 := by
        rw [Complex.sq_norm, normSq_apply]; ring
      have hz : ‖ψ w‖ ^ 2 = (ψ w).re ^ 2 + (ψ w).im ^ 2 := by
        rw [Complex.sq_norm, normSq_apply]; ring
      generalize (Real.sqrt (1 - ‖ψ w‖ ^ 2))⁻¹ = s
      rw [hn, hz]
      simp only [mul_re, mul_im, conj_re, conj_im, pow_two]
      ring)
  obtain ⟨hΔ, hgN, hHN⟩ := hfr
  set s := (Real.sqrt (1 - ‖ψ w‖ ^ 2))⁻¹ with hsdef
  have hΨw : ((fun t => (Real.sqrt t)⁻¹) ∘ intrKernel Ω o) w = s := by
    show (Real.sqrt (intrKernel Ω o w))⁻¹ = s
    rw [hkw]
  obtain ⟨-, -, hpos⟩ := s05_density_smooth hJ
  have hposD : ∀ x ∈ D, 0 < poincareDensity Ω x := fun x hx => hpos x (h.2.2.2.1 hx)
  have hnn : ∀ {k : ℕ} (T : TensorField k), 0 ≤ rhoTensorNorm Ω T w := fun T =>
    div_nonneg (Real.sqrt_nonneg _) (pow_nonneg (hposD w hw).le _)
  have hA : rhoTensorNorm Ω (lowerA Ω aUp - rhoMetricT Ω) w +
      rhoTensorNorm Ω (lowerB Ω bUp) w + |c w - 2| ≤ ε' :=
    s05_adm_point h hposD (i := 0) (i' := 0) (by norm_num) (by norm_num) hw
  obtain ⟨hcs, hbs⟩ := (eq_adjoint Ω Ωs hJ D ε' aUp bUp c h).2 w hw
  have hε := h.1
  have hε8 := h.2.1
  have hnA := hnn (lowerA Ω aUp - rhoMetricT Ω)
  have hnB := hnn (lowerB Ω bUp)
  have hnB' := hnn (lowerB Ω (adjCoeffB Ω aUp bUp))
  have hnH := hnn (rhoHess Ω ((fun t => (Real.sqrt t)⁻¹) ∘ intrKernel Ω o))
  have hng := hnn (rhoCovDeriv Ω (scalarField ((fun t => (Real.sqrt t)⁻¹) ∘ intrKernel Ω o)))
  have habs := abs_nonneg (c w - 2)
  have hc1 := (abs_le.1 (show |c w - 2| ≤ ε' by linarith)).1
  have hc2 := (abs_le.1 hcs).1
  have e1 := s05_ellOp_err aUp bUp c ((fun t => (Real.sqrt t)⁻¹) ∘ intrKernel Ω o) (hposD w hw)
  have e2 := s05_ellOp_err aUp (adjCoeffB Ω aUp bUp) (adjCoeffC Ω aUp bUp c)
    ((fun t => (Real.sqrt t)⁻¹) ∘ intrKernel Ω o) (hposD w hw)
  rw [hΨw] at e1 e2
  have p1 := mul_le_mul (show rhoTensorNorm Ω (lowerA Ω aUp - rhoMetricT Ω) w ≤ ε' by linarith)
    hHN hnH hε.le
  have p2 := mul_le_mul (show rhoTensorNorm Ω (lowerB Ω bUp) w ≤ ε' by linarith) hgN hng hε.le
  have p3 := mul_le_mul hbs hgN hng (by linarith)
  have p4 := mul_le_mul_of_nonneg_right hc1 hs.le
  have p5 := mul_le_mul_of_nonneg_right hc2 hs.le
  have p6 := mul_le_mul_of_nonneg_right hε8 hs.le
  have e1' := (abs_le.1 e1).1
  have e2' := (abs_le.1 e2).1
  rw [hΨ]
  unfold ellOpAdj
  constructor <;> nlinarith

/-- **Lemma 5.3 (d)** (`lem:test-functions`, sec05-upper.tex:174).  `𝓛1 = c > 0` and
`𝓛*1 = c* > 0` on `D`. -/
theorem lem_test_functions_d : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (D : Set ℂ) (ε' : ℝ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsAdmissibleOp Ω D ε' aUp bUp c → ∀ w ∈ D,
      ellOp Ω aUp bUp c (fun _ => 1) w = c w ∧ 0 < c w ∧
        ellOpAdj Ω aUp bUp c (fun _ => 1) w = adjCoeffC Ω aUp bUp c w ∧
        0 < adjCoeffC Ω aUp bUp c w := by
  intro Ω Ωs hJ D ε' aUp bUp c hadm w hw
  have hc := s05_admissible_c_bound hadm w hw
  have hcs := ((eq_adjoint Ω Ωs hJ D ε' aUp bUp c hadm).2 w hw).1
  obtain ⟨-, hε8, -⟩ := hadm
  refine ⟨s05_ellOp_const_one Ω aUp bUp c w, ?_,
    s05_ellOp_const_one Ω aUp (adjCoeffB Ω aUp bUp) (adjCoeffC Ω aUp bUp c) w, ?_⟩
  · have := (abs_le.1 hc).1
    linarith
  · have := (abs_le.1 hcs).1
    linarith

/-- Helper (P2): `∇²u(X, Y) = D²u(X)(Y) - du(Γ(X, Y))`. -/
theorem s05_hess_D2 {Ω : Set ℂ} {u : ℂ → ℝ} {w : ℂ} (hu : DifferentiableAt ℝ (fderiv ℝ u) w)
    (X Y : ℂ) :
    rhoHess Ω u w ![X, Y] =
      fderiv ℝ (fderiv ℝ u) w X Y - fderiv ℝ u w (rhoChristoffel Ω w X Y) := by
  rw [s05_rhoHess_eq, fderiv_clm_apply hu (differentiableAt_const Y)]
  simp

/-- Helper (P2): first and second derivatives of `f - s g` for `C²` functions. -/
theorem s05_D2_sub {f g : ℂ → ℝ} {w : ℂ} (hf : ContDiffAt ℝ 2 f w) (hg : ContDiffAt ℝ 2 g w)
    (s : ℝ) :
    DifferentiableAt ℝ (fderiv ℝ f) w ∧ DifferentiableAt ℝ (fderiv ℝ g) w ∧
      DifferentiableAt ℝ (fderiv ℝ (fun x => f x - s * g x)) w ∧
      fderiv ℝ (fun x => f x - s * g x) w = fderiv ℝ f w - s • fderiv ℝ g w ∧
      fderiv ℝ (fderiv ℝ (fun x => f x - s * g x)) w =
        fderiv ℝ (fderiv ℝ f) w - s • fderiv ℝ (fderiv ℝ g) w := by
  have h1 : ∀ {h : ℂ → ℝ}, ContDiffAt ℝ 2 h w → DifferentiableAt ℝ (fderiv ℝ h) w := fun hh =>
    (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hev : fderiv ℝ (fun x => f x - s * g x) =ᶠ[𝓝 w]
      fun x => fderiv ℝ f x - s • fderiv ℝ g x := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with x hfx hgx
    have hgd : DifferentiableAt ℝ g x := hgx.differentiableAt (by simp)
    rw [fderiv_fun_sub (hfx.differentiableAt (by simp)) (hgd.const_mul s), fderiv_const_mul hgd]
  refine ⟨h1 hf, h1 hg, h1 (hf.sub (contDiffAt_const.mul hg)), hev.eq_of_nhds, ?_⟩
  rw [hev.fderiv_eq, fderiv_fun_sub (h1 hf)
    (show DifferentiableAt ℝ (fun y => s • fderiv ℝ g y) w from (h1 hg).const_smul s),
    fderiv_fun_const_smul (h1 hg)]

/-- Helper (P2): `𝓛(f - s g) = 𝓛f - s 𝓛g` at a point where `f, g` are `C²`. -/
theorem s05_ellOp_sub {Ω : Set ℂ} (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (B : ℂ → Fin 2 → ℝ)
    (C : ℂ → ℝ) {f g : ℂ → ℝ} {w : ℂ} (hf : ContDiffAt ℝ 2 f w) (hg : ContDiffAt ℝ 2 g w)
    (s : ℝ) :
    ellOp Ω aUp B C (fun x => f x - s * g x) w =
      ellOp Ω aUp B C f w - s * ellOp Ω aUp B C g w := by
  obtain ⟨df, dg, dd, e1, e2⟩ := s05_D2_sub hf hg s
  simp only [ellOp, s05_hess_D2 df, s05_hess_D2 dg, s05_hess_D2 dd, e1, e2, Fin.sum_univ_two,
    sub_apply, smul_apply, smul_eq_mul]
  ring

/-- Helper (P2): at a local maximum of a `C²` function, `D²u(V, V) ≤ 0`. -/
theorem s05_second_nonpos {u : ℂ → ℝ} {x : ℂ} (hu : ContDiffAt ℝ 2 u x) (hm : IsLocalMax u x)
    (V : ℂ) : fderiv ℝ (fderiv ℝ u) x V V ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have h1 : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun t => u (x + t • V) := ⟨_, rfl⟩
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • V) V t := fun t => by
    simpa only [one_smul] using ((hasDerivAt_id' t).smul_const V).const_add x
  have hc : Tendsto (fun t : ℝ => x + t • V) (𝓝 0) (𝓝 x) := by
    simpa only [zero_smul, add_zero] using (hline 0).continuousAt.tendsto
  have hd : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt g (fderiv ℝ u (x + t • V) V) t := by
    filter_upwards [hc.eventually (hu.eventually (by simp))] with t ht
    rw [hg]
    exact (ht.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hline t)
  have hdd : HasDerivAt (fun t : ℝ => fderiv ℝ u (x + t • V) V)
      (fderiv ℝ (fderiv ℝ u) x V V) 0 := by
    have := (h1.hasFDerivAt.clm_apply (hasFDerivAt_const V x)).comp_hasDerivAt_of_eq 0
      (hline 0) (by simp)
    exact this.congr_deriv (by simp)
  have hD : deriv g =ᶠ[𝓝 0] fun t => fderiv ℝ u (x + t • V) V := by
    filter_upwards [hd] with t ht
    exact ht.deriv
  have hd0 : deriv g 0 = 0 := by
    rw [hD.eq_of_nhds]
    simp [hm.fderiv_eq_zero]
  have hdd0 : deriv (deriv g) 0 = fderiv ℝ (fderiv ℝ u) x V V := by
    rw [hD.deriv_eq]
    exact hdd.deriv
  have hmin := isLocalMin_of_deriv_deriv_pos (f := g) (by rw [hdd0]; exact hpos) hd0
    hd.self_of_nhds.continuousAt
  have hmax : IsLocalMax g 0 := by
    filter_upwards [hc.eventually hm] with t ht
    simp only [hg]
    simpa using ht
  have hconst : g =ᶠ[𝓝 0] fun _ => g 0 := by
    filter_upwards [hmin, hmax] with t h1 h2
    exact le_antisymm h2 h1
  have h0 : deriv (deriv g) 0 = 0 := by
    rw [hconst.deriv.deriv_eq]
    simp
  rw [hdd0] at h0
  linarith

/-- Helper (P2): `∑ a^{ij} H_{ij} ≤ 0` for `a` symmetric positive definite and `H` a negative
semidefinite quadratic form. -/
theorem s05_trace_nonpos {a : Matrix (Fin 2) (Fin 2) ℝ} {H : Fin 2 → Fin 2 → ℝ}
    (ha : 0 < a 0 0) (hs : a 0 1 = a 1 0) (hd : a 0 1 ^ 2 ≤ a 0 0 * a 1 1)
    (hq : ∀ x y : ℝ, x * x * H 0 0 + x * y * H 0 1 + y * x * H 1 0 + y * y * H 1 1 ≤ 0) :
    ∑ i : Fin 2, ∑ j : Fin 2, a i j * H i j ≤ 0 := by
  have h1 := hq (a 0 0) (a 0 1)
  have h2 : H 1 1 ≤ 0 := by have := hq 0 1; linarith
  simp only [Fin.sum_univ_two]
  rw [← hs]
  have h3 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hd) h2
  nlinarith

/-- Helper (P2): at a positive interior local maximum of a `C²` function, `𝓛u > 0` when `a` is
positive definite. -/
theorem s05_ellOp_max_pos {Ω : Set ℂ} {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {B : ℂ → Fin 2 → ℝ}
    {C : ℂ → ℝ} {u : ℂ → ℝ} {x : ℂ} (hu : ContDiffAt ℝ 2 u x) (hm : IsLocalMax u x)
    (ha : 0 < aUp x 0 0) (hs : aUp x 0 1 = aUp x 1 0)
    (hd : aUp x 0 1 ^ 2 ≤ aUp x 0 0 * aUp x 1 1) (hc : 0 < C x * u x) :
    0 < ellOp Ω aUp B C u x := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have ht := s05_trace_nonpos (a := aUp x)
    (H := fun i j => fderiv ℝ (fderiv ℝ u) x (frameVec i) (frameVec j)) ha hs hd fun p q => by
      have := s05_second_nonpos hu hm (p • frameVec 0 + q • frameVec 1)
      simp only [map_add, map_smul, add_apply,
        smul_apply, smul_eq_mul] at this
      linarith
  simp only [ellOp, s05_hess_D2 h1, hm.fderiv_eq_zero, zero_apply, sub_zero,
    mul_zero, Finset.sum_const_zero] at ht ⊢
  linarith

/-- Helper (P2): an `ε'`-admissible `a^{ij}` is symmetric positive definite on `D`. -/
theorem s05_adm_psd {Ω D : Set ℂ} {ε' : ℝ} {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ}
    {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ} (h : IsAdmissibleOp Ω D ε' aUp bUp c)
    (hpos : ∀ w ∈ D, 0 < poincareDensity Ω w) {w : ℂ} (hw : w ∈ D) :
    0 < aUp w 0 0 ∧ aUp w 0 1 = aUp w 1 0 ∧ aUp w 0 1 ^ 2 ≤ aUp w 0 0 * aUp w 1 1 := by
  have hl := hpos w hw
  have hA := s05_adm_point h hpos (i := 0) (i' := 0) (by norm_num) (by norm_num) hw
  have hnB : 0 ≤ rhoTensorNorm Ω (rhoIterCovDeriv Ω 0 (lowerB Ω bUp)) w :=
    div_nonneg (Real.sqrt_nonneg _) (pow_nonneg hl.le _)
  have hN : rhoTensorNorm Ω (lowerA Ω aUp - rhoMetricT Ω) w ≤ 1 / 8 := by
    have := abs_nonneg (c w - 2)
    have := h.2.1
    change rhoTensorNorm Ω (lowerA Ω aUp - rhoMetricT Ω) w + _ + _ ≤ ε' at hA
    linarith
  have hsym : aUp w 0 1 = aUp w 1 0 := by
    have := congrFun (congrFun (h.2.2.2.2.1.2.2.2 w hw) 1) 0
    simpa [Matrix.transpose_apply] using this
  have hS := s05_sqrt_hs (k := 2) (lowerA Ω aUp - rhoMetricT Ω) hl
  rw [s05_hs_two] at hS
  obtain ⟨m00, m01, m10, m11⟩ := s05_metric_frame Ω w
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Pi.sub_apply, s05_lowerA_frame, m00, m01,
    m10, m11] at hS
  set L := poincareDensity Ω w with hLdef
  set P := L ^ 2 with hP
  have hP0 : 0 < P := by positivity
  have hL4 : L ^ 4 = P * P := by rw [hP]; ring
  rw [hL4] at hS
  have hX : (P * P * aUp w 0 0 - P) ^ 2 + (P * P * aUp w 0 1 - 0) ^ 2 +
      ((P * P * aUp w 1 0 - 0) ^ 2 + (P * P * aUp w 1 1 - P) ^ 2) ≤ (P * (1 / 8)) ^ 2 := by
    have hnn : 0 ≤ (P * P * aUp w 0 0 - P) ^ 2 + (P * P * aUp w 0 1 - 0) ^ 2 +
        ((P * P * aUp w 1 0 - 0) ^ 2 + (P * P * aUp w 1 1 - P) ^ 2) :=
      add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (add_nonneg (sq_nonneg _) (sq_nonneg _))
    rw [← Real.sq_sqrt hnn, hS]
    exact pow_le_pow_left₀ (by rw [← hS]; exact Real.sqrt_nonneg _)
      (mul_le_mul_of_nonneg_left hN hP0.le) 2
  rw [← hsym] at hX ⊢
  have hY : (P * aUp w 0 0 - 1) ^ 2 + 2 * (P * aUp w 0 1) ^ 2 + (P * aUp w 1 1 - 1) ^ 2 ≤
      1 / 64 := by
    have hPP : 0 < P ^ 2 := by positivity
    refine le_of_mul_le_mul_left ?_ hPP
    nlinarith
  have h00 : 7 / 8 ≤ P * aUp w 0 0 := by nlinarith [sq_nonneg (P * aUp w 1 1 - 1)]
  have h11 : 7 / 8 ≤ P * aUp w 1 1 := by nlinarith [sq_nonneg (P * aUp w 0 0 - 1)]
  have h01 : (P * aUp w 0 1) ^ 2 ≤ 1 / 64 := by nlinarith [sq_nonneg (P * aUp w 0 0 - 1)]
  refine ⟨?_, rfl, ?_⟩
  · by_contra hn
    push Not at hn
    nlinarith
  · have hPP : 0 < P ^ 2 := by positivity
    refine le_of_mul_le_mul_left ?_ hPP
    nlinarith

/-- W-PDE1 stage P0 helper (P0-1): `𝓛` in Euclidean non-divergence form in the frame `(1, i)`,
`𝓛u = cu - a^{ij}∂ᵢ∂ⱼu - B̃^k∂ₖu` with `B̃^k = b^k - a^{ij}Γ^k_{ij}` (from `s05_rhoHess_eq`; no
regularity of `u` is needed, both sides use the same `fderiv`). -/
theorem s05_ell_nondiv (Ω : Set ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ)
    (c u : ℂ → ℝ) (w : ℂ) :
    ellOp Ω aUp bUp c u w = c w * u w -
      ∑ i : Fin 2, ∑ j : Fin 2, aUp w i j *
        fderiv ℝ (fun x => fderiv ℝ u x (frameVec j)) w (frameVec i) -
      ∑ k : Fin 2, (bUp w k - ∑ i : Fin 2, ∑ j : Fin 2,
          aUp w i j * cvec (rhoChristoffel Ω w (frameVec i) (frameVec j)) k) *
        fderiv ℝ u w (frameVec k) := by
  have hv : ∀ i j : Fin 2, fderiv ℝ u w (rhoChristoffel Ω w (frameVec i) (frameVec j)) =
      ∑ k : Fin 2, cvec (rhoChristoffel Ω w (frameVec i) (frameVec j)) k *
        fderiv ℝ u w (frameVec k) := by
    intro i j
    set v := rhoChristoffel Ω w (frameVec i) (frameVec j)
    have hvv : v = (cvec v 0) • frameVec 0 + (cvec v 1) • frameVec 1 := by
      apply Complex.ext <;> simp [cvec, frameVec]
    conv_lhs => rw [hvv]
    simp only [map_add, map_smul, smul_eq_mul, Fin.sum_univ_two]
  simp only [ellOp, s05_rhoHess_eq, hv, Fin.sum_univ_two]
  ring

/-- W-PDE1 stage P0 helper (P0-2): `ρ²𝓛` in Euclidean divergence form,
`ρ²𝓛u = -∂ᵢ(Ãⁱʲ∂ⱼu) + βʲ∂ⱼu + ρ²cu` with `Ã = ρ²a`, `βʲ = ∂ᵢÃⁱʲ - ρ²B̃ʲ`, at points of `D` where
`u` is `C²`. -/
theorem s05_ell_div {Ω Ωs D : Set ℂ} (hJ : IsJordanPair Ω Ωs) {ε' : ℝ}
    {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ}
    (h : IsAdmissibleOp Ω D ε' aUp bUp c) {u : ℂ → ℝ} {w : ℂ} (hw : w ∈ D)
    (hu : ContDiffAt ℝ 2 u w) :
    poincareDensity Ω w ^ 2 * ellOp Ω aUp bUp c u w =
      -∑ i : Fin 2, fderiv ℝ (fun x => ∑ j : Fin 2,
          poincareDensity Ω x ^ 2 * aUp x i j * fderiv ℝ u x (frameVec j)) w (frameVec i) +
      ∑ j : Fin 2, (∑ i : Fin 2,
          fderiv ℝ (fun x => poincareDensity Ω x ^ 2 * aUp x i j) w (frameVec i) -
          poincareDensity Ω w ^ 2 * (bUp w j - ∑ i : Fin 2, ∑ k : Fin 2,
            aUp w i k * cvec (rhoChristoffel Ω w (frameVec i) (frameVec k)) j)) *
        fderiv ℝ u w (frameVec j) +
      poincareDensity Ω w ^ 2 * c w * u w := by
  have hD : IsOpen D := h.2.2.1
  have hρ := ((s05_density_smooth hJ).2.1).mono h.2.2.2.1
  have hA : ∀ i j : Fin 2, DifferentiableAt ℝ (fun x => poincareDensity Ω x ^ 2 * aUp x i j) w :=
    fun i j => (((hρ.pow 2).mul (h.2.2.2.2.1.1 i j)).contDiffAt
      (hD.mem_nhds hw)).differentiableAt (by simp)
  have hg : ∀ j : Fin 2, DifferentiableAt ℝ (fun x => fderiv ℝ u x (frameVec j)) w :=
    fun j => ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)
  have key : ∀ i : Fin 2, fderiv ℝ (fun x => ∑ j : Fin 2,
      poincareDensity Ω x ^ 2 * aUp x i j * fderiv ℝ u x (frameVec j)) w =
      ∑ j : Fin 2, ((poincareDensity Ω w ^ 2 * aUp w i j) •
          fderiv ℝ (fun x => fderiv ℝ u x (frameVec j)) w +
        fderiv ℝ u w (frameVec j) •
          fderiv ℝ (fun x => poincareDensity Ω x ^ 2 * aUp x i j) w) := fun i =>
    (HasFDerivAt.fun_sum fun j _ => (hA i j).hasFDerivAt.fun_mul (hg j).hasFDerivAt).fderiv
  simp only [key]
  simp only [add_apply, smul_apply, smul_eq_mul, s05_ell_nondiv, Fin.sum_univ_two]
  ring

/-- W-PDE1 stage P0 helper: a quadratic form with Hilbert–Schmidt norm `≤ ε'` is bounded by
`ε'|ξ|²` (Cauchy–Schwarz in `ℝ⁴`). -/
theorem s05_ell_quad_le {ε' m00 m01 m10 m11 x0 x1 : ℝ} (hε : 0 ≤ ε')
    (hS : m00 ^ 2 + m01 ^ 2 + m10 ^ 2 + m11 ^ 2 ≤ ε' ^ 2) :
    |m00 * x0 * x0 + m01 * x0 * x1 + m10 * x1 * x0 + m11 * x1 * x1| ≤
      ε' * (x0 * x0 + x1 * x1) := by
  have hcs : (m00 * x0 * x0 + m01 * x0 * x1 + m10 * x1 * x0 + m11 * x1 * x1) ^ 2 ≤
      (m00 ^ 2 + m01 ^ 2 + m10 ^ 2 + m11 ^ 2) *
        ((x0 * x0) ^ 2 + (x0 * x1) ^ 2 + (x1 * x0) ^ 2 + (x1 * x1) ^ 2) := by
    nlinarith [sq_nonneg (m00 * (x0 * x1) - m01 * (x0 * x0)),
      sq_nonneg (m00 * (x1 * x0) - m10 * (x0 * x0)), sq_nonneg (m00 * (x1 * x1) - m11 * (x0 * x0)),
      sq_nonneg (m01 * (x1 * x0) - m10 * (x0 * x1)), sq_nonneg (m01 * (x1 * x1) - m11 * (x0 * x1)),
      sq_nonneg (m10 * (x1 * x1) - m11 * (x1 * x0))]
  have hV : (x0 * x0) ^ 2 + (x0 * x1) ^ 2 + (x1 * x0) ^ 2 + (x1 * x1) ^ 2 =
      (x0 * x0 + x1 * x1) ^ 2 := by ring
  have hb : 0 ≤ ε' * (x0 * x0 + x1 * x1) :=
    mul_nonneg hε (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
  have h2 : (m00 * x0 * x0 + m01 * x0 * x1 + m10 * x1 * x0 + m11 * x1 * x1) ^ 2 ≤
      (ε' * (x0 * x0 + x1 * x1)) ^ 2 := by
    rw [mul_pow]
    exact hcs.trans (by rw [hV]; exact mul_le_mul_of_nonneg_right hS (sq_nonneg _))
  calc _ ≤ Real.sqrt ((ε' * (x0 * x0 + x1 * x1)) ^ 2) := Real.abs_le_sqrt h2
    _ = _ := Real.sqrt_sq hb

/-- W-PDE1 stage P0 deliverable (P0-3): the divergence-form data of an `ε'`-admissible `𝓛` on `D`.
`Ã = ρ²a` is symmetric with `|Ãξ·ξ - |ξ|²| ≤ ε'|ξ|²`, `β` is smooth (no size bound is needed: the
`c ≥ 0` existence theorem allows any bounded drift), and `γ = ρ²c ≥ (15/8)ρ²`. -/
theorem s05_ell_package : ∀ {Ω Ωs D : Set ℂ},
    IsJordanPair Ω Ωs → ∀ {ε' : ℝ} {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {bUp : ℂ → Fin 2 → ℝ}
    {c : ℂ → ℝ}, IsAdmissibleOp Ω D ε' aUp bUp c →
    ∃ (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (β : ℂ → Fin 2 → ℝ) (γ : ℂ → ℝ),
      (∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) D) ∧ (∀ j, ContDiffOn ℝ ∞ (fun x => β x j) D) ∧
      ContDiffOn ℝ ∞ γ D ∧ (∀ w ∈ D, (A w)ᵀ = A w) ∧
      (∀ w ∈ D, ∀ ξ : Fin 2 → ℝ, |ξ ⬝ᵥ (A w *ᵥ ξ) - ξ ⬝ᵥ ξ| ≤ ε' * (ξ ⬝ᵥ ξ)) ∧
      (∀ w ∈ D, 15 / 8 * poincareDensity Ω w ^ 2 ≤ γ w) ∧
      ∀ u : ℂ → ℝ, ∀ w ∈ D, ContDiffAt ℝ 2 u w →
        poincareDensity Ω w ^ 2 * ellOp Ω aUp bUp c u w =
          -∑ i : Fin 2, fderiv ℝ (fun x => ∑ j : Fin 2, A x i j * fderiv ℝ u x (frameVec j))
              w (frameVec i) +
            ∑ j : Fin 2, β w j * fderiv ℝ u w (frameVec j) + γ w * u w := by
  intro Ω Ωs D hJ ε' aUp bUp c h
  have hD : IsOpen D := h.2.2.1
  have hDΩ : D ⊆ Ω := h.2.2.2.1
  obtain ⟨ha, hb, hc, hsym⟩ := h.2.2.2.2.1
  have hρ := ((s05_density_smooth hJ).2.1).mono hDΩ
  have hpos : ∀ w ∈ D, 0 < poincareDensity Ω w := fun w hw =>
    (s05_density_smooth hJ).2.2 w (hDΩ hw)
  have hAij : ∀ i j : Fin 2,
      ContDiffOn ℝ ∞ (fun x => poincareDensity Ω x ^ 2 * aUp x i j) D :=
    fun i j => (hρ.pow 2).mul (ha i j)
  have hG := s05_logDensityGrad_smooth hD hρ hpos
  have hΓ : ∀ i k j : Fin 2, ContDiffOn ℝ ∞
      (fun x => cvec (rhoChristoffel Ω x (frameVec i) (frameVec k)) j) D := by
    intro i k j
    have h0 := s05_christoffel_smooth hG contDiffOn_id (Set.mapsTo_id D)
      (contDiffOn_const (c := frameVec i)) (contDiffOn_const (c := frameVec k))
    fin_cases j
    · exact (reCLM.contDiff.comp_contDiffOn h0).congr fun x _ => by simp [cvec]
    · exact (imCLM.contDiff.comp_contDiffOn h0).congr fun x _ => by simp [cvec]
  have hnn : ∀ w ∈ D, ∀ {k : ℕ} (T : TensorField k), 0 ≤ rhoTensorNorm Ω T w := fun w hw _ T =>
    div_nonneg (Real.sqrt_nonneg _) (pow_nonneg (hpos w hw).le _)
  refine ⟨fun x => poincareDensity Ω x ^ 2 • aUp x,
    fun x j => ∑ i : Fin 2, fderiv ℝ (fun y => poincareDensity Ω y ^ 2 * aUp y i j) x (frameVec i) -
      poincareDensity Ω x ^ 2 * (bUp x j - ∑ i : Fin 2, ∑ k : Fin 2,
        aUp x i k * cvec (rhoChristoffel Ω x (frameVec i) (frameVec k)) j),
    fun x => poincareDensity Ω x ^ 2 * c x, ?_, ?_, (hρ.pow 2).mul hc, ?_, ?_, ?_, ?_⟩
  · intro i j
    simpa only [Matrix.smul_apply, smul_eq_mul] using hAij i j
  · intro j
    exact (ContDiffOn.sum fun i _ => ((hAij i j).fderiv_of_isOpen hD (m := ∞)
      (le_of_eq ENat.coe_top_add_one)).clm_apply contDiffOn_const).sub ((hρ.pow 2).mul
      ((hb j).sub (ContDiffOn.sum fun i _ => ContDiffOn.sum fun k _ => (ha i k).mul (hΓ i k j))))
  · intro w hw
    rw [Matrix.transpose_smul, hsym w hw]
  · intro w hw ξ
    have hl := hpos w hw
    have hp := s05_adm_point h hpos (i := 0) (i' := 0) (by norm_num) (by norm_num) hw
    have hN : rhoTensorNorm Ω (lowerA Ω aUp - rhoMetricT Ω) w ≤ ε' := by
      change rhoTensorNorm Ω (lowerA Ω aUp - rhoMetricT Ω) w + _ + _ ≤ ε' at hp
      have := abs_nonneg (c w - 2)
      have := hnn w hw (rhoIterCovDeriv Ω 0 (lowerB Ω bUp))
      linarith
    have hS := s05_sqrt_hs (k := 2) (lowerA Ω aUp - rhoMetricT Ω) hl
    rw [s05_hs_two] at hS
    obtain ⟨m00, m01, m10, m11⟩ := s05_metric_frame Ω w
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Pi.sub_apply, s05_lowerA_frame, m00, m01,
      m10, m11] at hS
    set L := poincareDensity Ω w with hLdef
    set P := L ^ 2 with hP
    have hP0 : 0 < P := by positivity
    have hL4 : L ^ 4 = P * P := by rw [hP]; ring
    rw [hL4] at hS
    have hX : (P * P * aUp w 0 0 - P) ^ 2 + (P * P * aUp w 0 1 - 0) ^ 2 +
        ((P * P * aUp w 1 0 - 0) ^ 2 + (P * P * aUp w 1 1 - P) ^ 2) ≤ (P * ε') ^ 2 := by
      have hnn' : 0 ≤ (P * P * aUp w 0 0 - P) ^ 2 + (P * P * aUp w 0 1 - 0) ^ 2 +
          ((P * P * aUp w 1 0 - 0) ^ 2 + (P * P * aUp w 1 1 - P) ^ 2) :=
        add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
          (add_nonneg (sq_nonneg _) (sq_nonneg _))
      rw [← Real.sq_sqrt hnn', hS]
      exact pow_le_pow_left₀ (by rw [← hS]; exact Real.sqrt_nonneg _)
        (mul_le_mul_of_nonneg_left hN hP0.le) 2
    have hY : (P * aUp w 0 0 - 1) ^ 2 + (P * aUp w 0 1) ^ 2 + (P * aUp w 1 0) ^ 2 +
        (P * aUp w 1 1 - 1) ^ 2 ≤ ε' ^ 2 := by
      have hPP : 0 < P ^ 2 := by positivity
      refine le_of_mul_le_mul_left ?_ hPP
      nlinarith
    have key := s05_ell_quad_le (x0 := ξ 0) (x1 := ξ 1) h.1.le
      (by simpa only [sub_zero] using hY)
    have e1 : ξ ⬝ᵥ ((P • aUp w) *ᵥ ξ) - ξ ⬝ᵥ ξ = (P * aUp w 0 0 - 1) * ξ 0 * ξ 0 +
        P * aUp w 0 1 * ξ 0 * ξ 1 + P * aUp w 1 0 * ξ 1 * ξ 0 +
        (P * aUp w 1 1 - 1) * ξ 1 * ξ 1 := by
      simp only [dotProduct, mulVec, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
      ring
    have e2 : ξ ⬝ᵥ ξ = ξ 0 * ξ 0 + ξ 1 * ξ 1 := by
      simp only [dotProduct, Fin.sum_univ_two]
    rw [e1, e2]
    exact key
  · intro w hw
    have hp := s05_adm_point h hpos (i := 0) (i' := 0) (by norm_num) (by norm_num) hw
    have h1 := hnn w hw (rhoIterCovDeriv Ω 0 (lowerA Ω aUp - rhoMetricT Ω))
    have h2 := hnn w hw (rhoIterCovDeriv Ω 0 (lowerB Ω bUp))
    have he := h.2.1
    have hc2 : 15 / 8 ≤ c w := by
      have := neg_abs_le (c w - 2)
      linarith
    have := mul_le_mul_of_nonneg_left hc2 (sq_nonneg (poincareDensity Ω w))
    linarith
  · intro u w hw hu
    simpa only [Matrix.smul_apply, smul_eq_mul] using s05_ell_div hJ h hw hu

/-- W-PDE2 B1 (bridge `ℂ ≃ ℝ²`, shared with W-PDE1 P6): the divergence-form data of an
`ε'`-admissible `𝓛` on `D`, transported to `ℝ²` by `e = Complex.orthonormalBasisOneI.repr`.
On `e(D)`: `A` is smooth, symmetric and `ε'`-close to `I`, `β`, `γ` and `ρ² ∘ e⁻¹` are smooth,
`γ ≥ 0`, `ρ > 0`, and for every `g` that is `C²` at `x ∈ e(D)`,
`ρ²·𝓛(g ∘ e) = -∂ᵢ(Aⁱʲ∂ⱼg) + βʲ∂ⱼg + γ g` at `e⁻¹ x`, in the exact form of the conclusions of
`pde_weak_sol_smooth_interior` / `pde_classical`. -/
theorem s05_pde_bridge : ∀ {Ω Ωs D : Set ℂ},
    IsJordanPair Ω Ωs → ∀ {ε' : ℝ} {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {bUp : ℂ → Fin 2 → ℝ}
    {c : ℂ → ℝ}, IsAdmissibleOp Ω D ε' aUp bUp c →
    ∃ (A : EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ)
      (β : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (γ : EuclideanSpace ℝ (Fin 2) → ℝ),
      (∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) (Complex.orthonormalBasisOneI.repr '' D)) ∧
      ContDiffOn ℝ ∞ β (Complex.orthonormalBasisOneI.repr '' D) ∧
      ContDiffOn ℝ ∞ γ (Complex.orthonormalBasisOneI.repr '' D) ∧
      ContDiffOn ℝ ∞ (fun x => poincareDensity Ω (Complex.orthonormalBasisOneI.repr.symm x) ^ 2)
        (Complex.orthonormalBasisOneI.repr '' D) ∧
      (∀ x ∈ Complex.orthonormalBasisOneI.repr '' D, (A x)ᵀ = A x) ∧
      (∀ x ∈ Complex.orthonormalBasisOneI.repr '' D, ∀ ξ : Fin 2 → ℝ,
        |ξ ⬝ᵥ (A x *ᵥ ξ) - ξ ⬝ᵥ ξ| ≤ ε' * (ξ ⬝ᵥ ξ)) ∧
      (∀ x ∈ Complex.orthonormalBasisOneI.repr '' D, 0 ≤ γ x) ∧
      (∀ x ∈ Complex.orthonormalBasisOneI.repr '' D,
        0 < poincareDensity Ω (Complex.orthonormalBasisOneI.repr.symm x)) ∧
      ∀ g : EuclideanSpace ℝ (Fin 2) → ℝ, ∀ x ∈ Complex.orthonormalBasisOneI.repr '' D,
        ContDiffAt ℝ 2 g x →
          poincareDensity Ω (Complex.orthonormalBasisOneI.repr.symm x) ^ 2 *
              ellOp Ω aUp bUp c (fun z => g (Complex.orthonormalBasisOneI.repr z))
                (Complex.orthonormalBasisOneI.repr.symm x) =
            -(∑ i : Fin 2, fderiv ℝ (fun y => ∑ j : Fin 2, A y i j * fderiv ℝ g y
                (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) +
              ∑ j : Fin 2, β x j * fderiv ℝ g x (EuclideanSpace.single j 1) + γ x * g x := by
  intro Ω Ωs D hJ ε' aUp bUp c h
  set e := Complex.orthonormalBasisOneI.repr with he
  have hD : IsOpen D := h.2.2.1
  have hDΩ : D ⊆ Ω := h.2.2.2.1
  have heD : IsOpen (e '' D) := e.toHomeomorph.isOpenMap _ hD
  have hmem : ∀ x ∈ e '' D, e.symm x ∈ D := by
    rintro _ ⟨w, hw, rfl⟩
    simpa using hw
  have hsm : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℂ → F},
      ContDiffOn ℝ ∞ f D → ContDiffOn ℝ ∞ (fun x => f (e.symm x)) (e '' D) :=
    fun hf => pde_contDiffOn_comp_symm hf
  obtain ⟨A0, β0, γ0, hA0, hβ0, hγ0, hsym, hell, hγ, hid⟩ := s05_ell_package hJ h
  have hρ := ((s05_density_smooth hJ).2.1).mono hDΩ
  have hpos : ∀ w ∈ D, 0 < poincareDensity Ω w := fun w hw =>
    (s05_density_smooth hJ).2.2 w (hDΩ hw)
  have hβv : ContDiffOn ℝ ∞ β0 D := contDiffOn_pi.2 hβ0
  refine ⟨fun x => A0 (e.symm x), fun x => (EuclideanSpace.equiv (Fin 2) ℝ).symm (β0 (e.symm x)),
    fun x => γ0 (e.symm x), fun i j => hsm (hA0 i j),
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp_contDiffOn (hsm hβv), hsm hγ0,
    hsm (hρ.pow 2), fun x hx => hsym _ (hmem x hx), fun x hx => hell _ (hmem x hx),
    fun x hx => ?_, fun x hx => hpos _ (hmem x hx), ?_⟩
  · have := hγ _ (hmem x hx)
    have := hpos _ (hmem x hx)
    nlinarith
  intro g x hx hg
  set w := e.symm x with hw
  have hwD : w ∈ D := hmem x hx
  have hex : e w = x := by simp [hw]
  have hgu : ContDiffAt ℝ 2 (fun z => g (e z)) w := by
    rw [← hex] at hg
    exact hg.comp w e.contDiff.contDiffAt
  have hid' := hid (fun z => g (e z)) w hwD hgu
  rw [hid']
  -- `g` is differentiable near `x`, hence `fun z => g (e z)` has frame derivatives
  -- `fderiv g (e z) (single j 1)` near `w`
  have hgd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y :=
    (hg.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hgd' : ∀ᶠ z in 𝓝 w, DifferentiableAt ℝ g (e z) := by
    have hc : Tendsto e (𝓝 w) (𝓝 x) := hex ▸ e.continuous.continuousAt
    exact hc.eventually hgd
  have hfr : ∀ᶠ z in 𝓝 w, ∀ j : Fin 2,
      fderiv ℝ (fun z => g (e z)) z (frameVec j) = fderiv ℝ g (e z) (EuclideanSpace.single j 1) :=
    hgd'.mono fun z hz j => pde_fderiv_comp hz j
  have hfrw : ∀ j : Fin 2,
      fderiv ℝ (fun z => g (e z)) w (frameVec j) = fderiv ℝ g x (EuclideanSpace.single j 1) := by
    intro j
    rw [hfr.self_of_nhds j, hex]
  -- the flux components
  have hflux : ∀ i : Fin 2, (fun z => ∑ j : Fin 2, A0 z i j * fderiv ℝ (fun z => g (e z)) z
      (frameVec j)) =ᶠ[𝓝 w] fun z => (fun y => ∑ j : Fin 2, A0 (e.symm y) i j * fderiv ℝ g y
        (EuclideanSpace.single j 1)) (e z) := by
    intro i
    filter_upwards [hfr] with z hz
    simp only [hz, LinearIsometryEquiv.symm_apply_apply]
  have hxD : e '' D ∈ 𝓝 x := heD.mem_nhds hx
  have hfd : ∀ i : Fin 2, DifferentiableAt ℝ (fun y => ∑ j : Fin 2, A0 (e.symm y) i j *
      fderiv ℝ g y (EuclideanSpace.single j 1)) x := by
    intro i
    have hg1 : ContDiffAt ℝ 1 (fderiv ℝ g) x := hg.fderiv_right (m := 1) (by norm_num)
    have hj : ∀ j : Fin 2, DifferentiableAt ℝ (fun y => A0 (e.symm y) i j *
        fderiv ℝ g y (EuclideanSpace.single j 1)) x := fun j =>
      (((hsm (hA0 i j)).contDiffAt hxD).differentiableAt (by simp)).mul
        ((hg1.clm_apply contDiffAt_const).differentiableAt (by norm_num))
    simp only [Fin.sum_univ_two]
    exact (hj 0).add (hj 1)
  have hdiv : ∀ i : Fin 2, fderiv ℝ (fun z => ∑ j : Fin 2, A0 z i j *
      fderiv ℝ (fun z => g (e z)) z (frameVec j)) w (frameVec i) =
        fderiv ℝ (fun y => ∑ j : Fin 2, A0 (e.symm y) i j * fderiv ℝ g y
          (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) := by
    intro i
    rw [(hflux i).fderiv_eq]
    have := pde_fderiv_comp (z := w) (hex.symm ▸ hfd i) i
    rw [this, hex]
  simp only [hdiv, hfrw, hex]
  rfl

/-- Helper (P2): the maximum principle behind Lemma 5.4, for `𝓛 = c - a^{ij}∇_i∇_j - B^i∇_i`
with `C > 0` and `𝓛Ψ_o > 0` for all `o ∈ Ω`. -/
theorem s05_cmp_core {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {D : Set ℂ} {ε' : ℝ}
    {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ}
    (h : IsAdmissibleOp Ω D ε' aUp bUp c) {B : ℂ → Fin 2 → ℝ} {C : ℂ → ℝ}
    (hC : ∀ w ∈ D, 0 < C w)
    (hΨ : ∀ o ∈ Ω, ∀ w ∈ D,
      0 < ellOp Ω aUp B C (fun x => Real.cosh (poincareDist Ω o x / 2)) w)
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ 2 v D) (hb : BddAbove (v '' D))
    (hbd : ∀ wb ∈ frontier D ∩ Ω, ∀ δ : ℝ, 0 < δ → ∀ᶠ w in 𝓝[D] wb, v w ≤ δ)
    (hL : ∀ w ∈ D, ellOp Ω aUp B C v w ≤ 0) : ∀ w ∈ D, v w ≤ 0 := by
  intro w0 hw0
  by_contra hneg
  push Not at hneg
  have hΩ := s05_jordan_isOpen hJ
  have hDo : IsOpen D := h.2.2.1
  have hDΩ : D ⊆ Ω := h.2.2.2.1
  obtain ⟨-, -, hpos⟩ := s05_density_smooth hJ
  have hposD : ∀ x ∈ D, 0 < poincareDensity Ω x := fun x hx => hpos x (hDΩ hx)
  have hw0Ω := hDΩ hw0
  obtain ⟨Ψ, hΨe⟩ : ∃ Ψ : ℂ → ℝ, Ψ = fun x => Real.cosh (poincareDist Ω w0 x / 2) := ⟨_, rfl⟩
  have hΨx : ∀ x, Ψ x = Real.cosh (poincareDist Ω w0 x / 2) := fun x => by rw [hΨe]
  obtain ⟨hΨs, hΨc, -⟩ := lem_test_functions_c Ω Ωs hJ D ε' aUp bUp c h w0 hw0Ω
  rw [← hΨe] at hΨs
  have hΨL : ∀ x ∈ D, 0 < ellOp Ω aUp B C Ψ x := fun x hx => by
    rw [hΨe]; exact hΨ w0 hw0Ω x hx
  have hΨ1 : ∀ x, 1 ≤ Ψ x := fun x => by rw [hΨx]; exact Real.one_le_cosh _
  obtain ⟨M, hM⟩ := hb
  have hvM : ∀ x ∈ D, v x ≤ M := fun x hx => hM ⟨x, hx, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = v w0 / (2 * Ψ w0) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact div_pos hneg (by linarith [hΨ1 w0])
  obtain ⟨u, hu⟩ : ∃ u : ℂ → ℝ, u = fun x => v x - δ * Ψ x := ⟨_, rfl⟩
  have hux : ∀ x, u x = v x - δ * Ψ x := fun x => by rw [hu]
  have hu0 : u w0 = v w0 / 2 := by
    have := (zero_lt_one.trans_le (hΨ1 w0)).ne'
    rw [hux, hδ]
    field_simp
    ring
  have huv : ∀ x, u x < v x := fun x => by
    rw [hux]; nlinarith [hΨ1 x]
  -- the superlevel set `E = {u ≥ v(w0)/2}` is compact
  have hK := hΨc (M / δ)
  have hEK : {x | x ∈ D ∧ v w0 / 2 ≤ u x} ⊆
      {x | x ∈ Ω ∧ Real.cosh (poincareDist Ω w0 x / 2) ≤ M / δ} := by
    rintro x ⟨hx, hux'⟩
    refine ⟨hDΩ hx, ?_⟩
    rw [← hΨx, le_div_iff₀ hδ0]
    have := hvM x hx
    rw [hux] at hux'
    nlinarith
  have huc : ContinuousOn u D := by
    rw [hu]
    exact hv.continuousOn.sub (continuousOn_const.mul (hΨs.continuousOn.mono hDΩ))
  have hED : {x | x ∈ D ∧ v w0 / 2 ≤ u x} ⊆ D := fun y hy => hy.1
  have hEc : IsClosed {x | x ∈ D ∧ v w0 / 2 ≤ u x} := by
    refine isClosed_of_closure_subset fun x hx => ?_
    have hxΩ : x ∈ Ω := (hK.isClosed.closure_subset_iff.2 hEK hx).1
    by_cases hxD : x ∈ D
    · refine ⟨hxD, ?_⟩
      by_contra hlt
      push Not at hlt
      have hev : ∀ᶠ y in 𝓝 x, u y < v w0 / 2 :=
        Filter.Tendsto.eventually (huc.continuousAt (hDo.mem_nhds hxD)) (gt_mem_nhds hlt)
      obtain ⟨y, hy1, hy2⟩ := ((mem_closure_iff_frequently.1 hx).and_eventually hev).exists
      exact absurd hy1.2 (not_le.2 hy2)
    · have hxf : x ∈ frontier D := by
        rw [hDo.frontier_eq]
        exact ⟨closure_mono hED hx, hxD⟩
      have hev := hbd x ⟨hxf, hxΩ⟩ (v w0 / 4) (by linarith)
      rw [eventually_nhdsWithin_iff] at hev
      obtain ⟨y, hy1, hy2⟩ := ((mem_closure_iff_frequently.1 hx).and_eventually hev).exists
      have := hy2 hy1.1
      have := hy1.2
      have := huv y
      linarith
  have hEcpt := hK.of_isClosed_subset hEc hEK
  obtain ⟨xs, hxs, hmax⟩ := hEcpt.exists_isMaxOn ⟨w0, hw0, hu0.ge⟩ (huc.mono hED)
  have hloc : IsLocalMax u xs := by
    filter_upwards [hDo.mem_nhds hxs.1] with y hy
    by_cases hyE : v w0 / 2 ≤ u y
    · exact isMaxOn_iff.1 hmax y ⟨hy, hyE⟩
    · push Not at hyE
      exact (hyE.trans_le hxs.2).le
  -- the second-order test at the interior maximum
  have hvx : ContDiffAt ℝ 2 v xs := hv.contDiffAt (hDo.mem_nhds hxs.1)
  have hΨx2 : ContDiffAt ℝ 2 Ψ xs := (hΨs.contDiffAt (hΩ.mem_nhds (hDΩ hxs.1))).of_le (by simp)
  obtain ⟨p1, p2, p3⟩ := s05_adm_psd h hposD hxs.1
  have hpos' := s05_ellOp_max_pos (Ω := Ω) (B := B) (C := C) (u := u)
    (by rw [hu]; exact hvx.sub (contDiffAt_const.mul hΨx2)) hloc p1 p2 p3
    (mul_pos (hC xs hxs.1) (by linarith [hxs.2]))
  rw [hu, s05_ellOp_sub aUp B C hvx hΨx2 δ] at hpos'
  have := hL xs hxs.1
  have := mul_pos hδ0 (hΨL xs hxs.1)
  linarith

/-- **Lemma 5.4** (Comparison principle, `lem:comparison`, sec05-upper.tex:208).  Let `𝓛` be
`ε'`-admissible on the open set `D ⊆ Ω`, `v ∈ C²(D)` bounded above with `𝓛v ≤ 0` in `D` and
`limsup_{D ∋ w → w_b} v(w) ≤ 0` for every `w_b ∈ ∂D ∩ Ω`.  Then `v ≤ 0` in `D`.  The same holds
with `𝓛*` in place of `𝓛` (second conjunct). -/
theorem lem_comparison : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (D : Set ℂ) (ε' : ℝ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsAdmissibleOp Ω D ε' aUp bUp c → ∀ v : ℂ → ℝ, ContDiffOn ℝ 2 v D → BddAbove (v '' D) →
      (∀ wb ∈ frontier D ∩ Ω, ∀ δ : ℝ, 0 < δ → ∀ᶠ w in 𝓝[D] wb, v w ≤ δ) →
        ((∀ w ∈ D, ellOp Ω aUp bUp c v w ≤ 0) → ∀ w ∈ D, v w ≤ 0) ∧
        ((∀ w ∈ D, ellOpAdj Ω aUp bUp c v w ≤ 0) → ∀ w ∈ D, v w ≤ 0) := by
  intro Ω Ωs hJ D ε' aUp bUp c h v hv hb hbd
  refine ⟨s05_cmp_core hJ h
      (fun w hw => (lem_test_functions_d Ω Ωs hJ D ε' aUp bUp c h w hw).2.1)
      (fun o ho w hw => ((lem_test_functions_c Ω Ωs hJ D ε' aUp bUp c h o ho).2.2 w hw).1)
      hv hb hbd,
    s05_cmp_core hJ h (B := adjCoeffB Ω aUp bUp) (C := adjCoeffC Ω aUp bUp c)
      (fun w hw => (lem_test_functions_d Ω Ωs hJ D ε' aUp bUp c h w hw).2.2.2)
      (fun o ho w hw => ((lem_test_functions_c Ω Ωs hJ D ε' aUp bUp c h o ho).2.2 w hw).2)
      hv hb hbd⟩

/-- W-PDE1 P6 helper: `ellOp` is affine in the lower-order coefficients,
`𝓛'u = 𝓛u + (c' - c)u - (b' - b)^k ∂ₖu` (from `s05_ell_nondiv`; no regularity of `u` needed). -/
theorem s05_p6_lin (Ω : Set ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp bUp' : ℂ → Fin 2 → ℝ)
    (c c' u : ℂ → ℝ) (w : ℂ) :
    ellOp Ω aUp bUp' c' u w = ellOp Ω aUp bUp c u w + (c' w - c w) * u w -
      ∑ k : Fin 2, (bUp' w k - bUp w k) * fderiv ℝ u w (frameVec k) := by
  rw [s05_ell_nondiv, s05_ell_nondiv]
  simp only [Fin.sum_univ_two]
  ring

/-- W-PDE1 P6 helper: for an `ε'`-admissible `𝓛` on `D`, the adjoint coefficients `b*`, `c*` are
smooth on `D` (`b* = 2∇_j a^{ij} - b`, `c* = c - ∇_j∇_i a^{ij} + ∇_i b^i`). -/
theorem s05_p6_adj_smooth {Ω Ωs D : Set ℂ} (hJ : IsJordanPair Ω Ωs) {ε' : ℝ}
    {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ}
    (h : IsAdmissibleOp Ω D ε' aUp bUp c) :
    (∀ i, ContDiffOn ℝ ∞ (fun w => adjCoeffB Ω aUp bUp w i) D) ∧
      ContDiffOn ℝ ∞ (adjCoeffC Ω aUp bUp c) D := by
  -- the `C^∞` analogue of `s05_gr_coeff_cont`
  have hU : IsOpen D := h.2.2.1
  have hl := ((s05_density_smooth hJ).2.1).mono h.2.2.2.1
  have hpos : ∀ w ∈ D, 0 < poincareDensity Ω w := fun w hw =>
    (s05_density_smooth hJ).2.2 w (h.2.2.2.1 hw)
  obtain ⟨ha, hb, hc, -⟩ := h.2.2.2.2.1
  have hfst : ContDiffOn ℝ ∞ (fun p : ℂ × (Fin 1 → ℂ) => p.1) (D ×ˢ univ) := contDiffOn_fst
  have hm : MapsTo (fun p : ℂ × (Fin 1 → ℂ) => p.1) (D ×ˢ univ) D := fun p hp => hp.1
  have hB : ContDiffOn ℝ ∞ (fun p : ℂ × (Fin 1 → ℂ) => lowerB Ω bUp p.1 p.2) (D ×ˢ univ) := by
    have hcv : ∀ i : Fin 2,
        ContDiffOn ℝ ∞ (fun p : ℂ × (Fin 1 → ℂ) => cvec (p.2 0) i) (D ×ˢ univ) :=
      fun i => ((contDiff_apply ℝ (fun _ => ℝ) i).comp (s05_cvec_contDiff.comp
        ((contDiff_apply ℝ (fun _ => ℂ) 0).comp contDiff_snd))).contDiffOn
    simp only [lowerB, dotProduct]
    exact ((hl.comp hfst hm).pow 2).mul
      (ContDiffOn.sum fun i _ => ((hb i).comp hfst hm).mul (hcv i))
  have h1A := s05_covDeriv_smooth hU hl hpos (s05_lowerA_smooth hl ha)
  have h2A := s05_covDeriv_smooth hU hl hpos h1A
  have h1B := s05_covDeriv_smooth hU hl hpos hB
  have hsl : ∀ {k : ℕ} {T : TensorField k},
      ContDiffOn ℝ ∞ (fun p : ℂ × (Fin k → ℂ) => T p.1 p.2) (D ×ˢ univ) → ∀ v : Fin k → ℂ,
        ContDiffOn ℝ ∞ (fun x => T x v) D := fun hT v =>
    hT.comp (contDiffOn_id.prodMk contDiffOn_const) fun x hx => ⟨hx, mem_univ _⟩
  have hne : ∀ k : ℕ, ∀ x ∈ D, poincareDensity Ω x ^ k ≠ 0 := fun k x hx =>
    pow_ne_zero _ (hpos x hx).ne'
  have hDA : ∀ i, ContDiffOn ℝ ∞ (fun w => rhoDivA Ω aUp w i) D := by
    intro i
    show ContDiffOn ℝ ∞ (fun w => (∑ j : Fin 2,
      rhoCovDeriv Ω (lowerA Ω aUp) w ![frameVec j, frameVec i, frameVec j]) /
        poincareDensity Ω w ^ 4) D
    exact (ContDiffOn.sum fun j _ => hsl h1A _).div (hl.pow 4) (hne 4)
  have hDD : ContDiffOn ℝ ∞ (rhoDDiv Ω aUp) D := by
    show ContDiffOn ℝ ∞ (fun w => (∑ i : Fin 2, ∑ j : Fin 2,
      rhoCovDeriv Ω (rhoCovDeriv Ω (lowerA Ω aUp)) w
        ![frameVec j, frameVec i, frameVec i, frameVec j]) / poincareDensity Ω w ^ 4) D
    exact (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => hsl h2A _).div (hl.pow 4) (hne 4)
  have hDB : ContDiffOn ℝ ∞ (rhoDivB Ω bUp) D := by
    show ContDiffOn ℝ ∞ (fun w => (∑ i : Fin 2,
      rhoCovDeriv Ω (lowerB Ω bUp) w ![frameVec i, frameVec i]) / poincareDensity Ω w ^ 2) D
    exact (ContDiffOn.sum fun i _ => hsl h1B _).div (hl.pow 2) (hne 2)
  refine ⟨fun i => ?_, ?_⟩
  · have e : (fun w => adjCoeffB Ω aUp bUp w i) = fun w => 2 * rhoDivA Ω aUp w i - bUp w i := by
      funext w
      simp [adjCoeffB, nsmul_eq_mul]
    rw [e]
    exact (contDiffOn_const.mul (hDA i)).sub (hb i)
  · show ContDiffOn ℝ ∞ (fun w => c w - rhoDDiv Ω aUp w + rhoDivB Ω bUp w) D
    exact (hc.sub hDD).add hDB

/-- W-PDE1 P6 helper: the Euclidean divergence-form expression
`-∂ᵢ(Aⁱʲ∂ⱼg) + βʲ∂ⱼg + γ g` at `x` only depends on `g` near `x`: it is unchanged when `g` is
replaced by `g'` agreeing with it on an open set containing `x`. -/
theorem s05_p6_div_congr {A : EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ}
    {β : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)} {γ : EuclideanSpace ℝ (Fin 2) → ℝ}
    {g g' : EuclideanSpace ℝ (Fin 2) → ℝ} {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : IsOpen S)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ S) (h : EqOn g g' S) :
    -(∑ i : Fin 2, fderiv ℝ (fun y => ∑ j : Fin 2, A y i j * fderiv ℝ g y
        (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) +
      ∑ j : Fin 2, β x j * fderiv ℝ g x (EuclideanSpace.single j 1) + γ x * g x =
    -(∑ i : Fin 2, fderiv ℝ (fun y => ∑ j : Fin 2, A y i j * fderiv ℝ g' y
        (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) +
      ∑ j : Fin 2, β x j * fderiv ℝ g' x (EuclideanSpace.single j 1) + γ x * g' x := by
  have h1 : ∀ y ∈ S, fderiv ℝ g y = fderiv ℝ g' y := fun y hy =>
    (h.eventuallyEq_of_mem (hS.mem_nhds hy)).fderiv_eq
  have h2 : ∀ i : Fin 2, fderiv ℝ (fun y => ∑ j : Fin 2, A y i j * fderiv ℝ g y
      (EuclideanSpace.single j 1)) x = fderiv ℝ (fun y => ∑ j : Fin 2, A y i j * fderiv ℝ g' y
      (EuclideanSpace.single j 1)) x := fun i =>
    Filter.EventuallyEq.fderiv_eq (Filter.mem_of_superset (hS.mem_nhds hx) fun y hy => by
      simp only [mem_ofPred_eq, h1 y hy])
  simp only [h2, h1 x hx, h hx]

/-- W-PDE1 P6 core (Dirichlet solvability from the `ℝ²` data): let `D ⊆ ℂ` be open and
`D' ⋐ D` smooth.  Let `A`, `β`, `γ`, `ρ2` be smooth on `e(D)` (`e = Complex.orthonormalBasisOneI.repr`),
`A` `ε'`-close to `I` (`ε' < 1`), `γ ≥ 0`, `ρ2 > 0`, and let `L` satisfy
`ρ2 · L(g ∘ e) = -∂ᵢ(Aⁱʲ∂ⱼg) + βʲ∂ⱼg + γ g` at `e⁻¹ x` for every `x ∈ e(D)` and `g` `C²` at `x`
(the shape of `s05_pde_bridge`).  Then for every `F` smooth on `D` there is `u ∈ C^∞(\overline{D'})`
with `L u = F` in `D'` and `u = 0` on `∂D'`.  (P2 `pde_weak_exists_unique` with data `ρ2 · F ∘ e⁻¹`,
P3 `pde_weak_sol_smooth_interior`, P5 `pde_closure_smooth` on `U = e(D'')`, `D' ⋐ D'' ⋐ D`.) -/
theorem s05_p6_core {D D' : Set ℂ} (hD : IsOpen D) (hD' : IsSmoothRelCompactIn D' D)
    {ε' : ℝ} (hε0 : 0 ≤ ε') (hε : ε' < 1)
    {A : EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ}
    {β : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {γ ρ2 : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) (Complex.orthonormalBasisOneI.repr '' D))
    (hβ : ContDiffOn ℝ ∞ β (Complex.orthonormalBasisOneI.repr '' D))
    (hγ : ContDiffOn ℝ ∞ γ (Complex.orthonormalBasisOneI.repr '' D))
    (hρ : ContDiffOn ℝ ∞ ρ2 (Complex.orthonormalBasisOneI.repr '' D))
    (hell : ∀ x ∈ Complex.orthonormalBasisOneI.repr '' D, ∀ ξ : Fin 2 → ℝ,
      |ξ ⬝ᵥ (A x *ᵥ ξ) - ξ ⬝ᵥ ξ| ≤ ε' * (ξ ⬝ᵥ ξ))
    (hγ0 : ∀ x ∈ Complex.orthonormalBasisOneI.repr '' D, 0 ≤ γ x)
    (hρ0 : ∀ x ∈ Complex.orthonormalBasisOneI.repr '' D, 0 < ρ2 x)
    {L : (ℂ → ℝ) → ℂ → ℝ}
    (hL : ∀ g : EuclideanSpace ℝ (Fin 2) → ℝ, ∀ x ∈ Complex.orthonormalBasisOneI.repr '' D,
      ContDiffAt ℝ 2 g x →
        ρ2 x * L (fun z => g (Complex.orthonormalBasisOneI.repr z))
            (Complex.orthonormalBasisOneI.repr.symm x) =
          -(∑ i : Fin 2, fderiv ℝ (fun y => ∑ j : Fin 2, A y i j * fderiv ℝ g y
              (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) +
            ∑ j : Fin 2, β x j * fderiv ℝ g x (EuclideanSpace.single j 1) + γ x * g x)
    {F : ℂ → ℝ} (hF : ContDiffOn ℝ ∞ F D) :
    ∃ u : ℂ → ℝ, ContDiffOn ℝ ∞ u (closure D') ∧ (∀ w ∈ D', L u w = F w) ∧
      ∀ w ∈ frontier D', u w = 0 := by
  -- The Dirichlet problem is solved on `e(D')` (`H¹₀(e(D'))`, zero values on `∂e(D') = e(∂D')`);
  -- `e(D'')`, `D' ⋐ D'' ⋐ D`, only provides the open neighbourhood `U ⊇ closure e(D')` on which
  -- the coefficients are smooth and uniformly elliptic, as P5 requires.
  obtain ⟨hD'o, hD'c, hD'D, ψ, hψ, hD'ψ, hψ0⟩ := hD'
  obtain ⟨D'', hD''o, hKD'', hD''D, hD''c⟩ :=
    exists_open_between_and_isCompact_closure hD'c hD hD'D
  obtain ⟨hE'o, hE'b, hE'cl⟩ := pde_e_image hD'o hD'c
  obtain ⟨hE''o, hE''b, hE''cl⟩ := pde_e_image hD''o hD''c
  set e := Complex.orthonormalBasisOneI.repr with he
  set ΩE : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2)) := ⟨e '' D', hE'o⟩ with hΩE
  set UE : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2)) := ⟨e '' D'', hE''o⟩ with hUE
  have hsub : closure (e '' D') ⊆ e '' D'' := by
    rw [hE'cl]
    exact image_mono hKD''
  have hsubU : closure (e '' D'') ⊆ e '' D := by
    rw [hE''cl]
    exact image_mono hD''D
  have hU_D : e '' D'' ⊆ e '' D := subset_closure.trans hsubU
  have hcl_D : closure (e '' D') ⊆ e '' D := hsub.trans hU_D
  have hE_D : e '' D' ⊆ e '' D := subset_closure.trans hcl_D
  have hcpt : IsCompact (closure (e '' D')) := by
    rw [hE'cl]
    exact hD'c.image e.continuous
  -- the boundary function `ψ ∘ e⁻¹`
  have hψE : ContDiff ℝ ∞ (fun x => ψ (e.symm x)) := hψ.comp e.symm.contDiff
  have hΩψ : e '' D' = {x | ψ (e.symm x) < 0} := by
    rw [e.image_eq_preimage_symm, hD'ψ]
    rfl
  have hψE0 : ∀ x, ψ (e.symm x) = 0 → fderiv ℝ (fun x => ψ (e.symm x)) x ≠ 0 := by
    intro x h0 hz
    apply hψ0 _ h0
    have h1 : fderiv ℝ (fun x => ψ (e.symm x)) x = (fderiv ℝ ψ (e.symm x)).comp
        (e.symm.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ) :=
      (e.symm.toContinuousLinearEquiv).comp_right_fderiv (f := ψ) (x := x)
    ext v
    have h2 := congrArg (fun T => T (e v)) (h1.symm.trans hz)
    simpa using h2
  -- uniform ellipticity on `U = e(D'')`
  obtain ⟨Lam, hellU, -⟩ := pde_uniformlyEllipticOn (Ω := UE) hE''b hε
    (fun i j => (hA i j).continuousOn.mono hsubU) (fun x hx => hell x (hU_D hx))
  -- the data `ρ2 · F ∘ e⁻¹ ∈ L²(e(D'))`
  set FE : EuclideanSpace ℝ (Fin 2) → ℝ := fun x => ρ2 x * F (e.symm x) with hFE
  have hFEs : ContDiffOn ℝ ∞ FE (e '' D) := hρ.mul (pde_contDiffOn_comp_symm hF)
  have hmeas : MeasurableSet (e '' D') := hE'o.measurableSet
  have : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (e '' D')) :=
    isFiniteMeasure_restrict.2 hE'b.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn (hFEs.continuousOn.mono hcl_D)
  have hmem : MemLp FE 2 ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (e '' D')) :=
    MemLp.of_bound ((hFEs.continuousOn.mono hE_D).aestronglyMeasurable hmeas) C
      ((ae_restrict_iff' hmeas).2 (ae_of_all _ fun x hx => hC x (subset_closure hx)))
  -- P2: the weak solution; P5: smooth up to the boundary; P3: the equation inside
  obtain ⟨uw, huw, -⟩ := pde_weak_exists_unique (Ω := ΩE) hE'b hε0 hε (A := A) (β := β)
    (γ := γ) (fun i j => (hA i j).continuousOn.mono hcl_D) (hβ.continuousOn.mono hcl_D)
    (hγ.continuousOn.mono hcl_D) (fun x hx => hell x (hE_D hx)) (fun x hx => hγ0 x (hE_D hx))
    (hmem.toLp FE)
  obtain ⟨g, hg, hug, hg0⟩ := pde_closure_smooth (Ω := ΩE) (U := UE) hcpt hsub hψE hΩψ hψE0
    hellU (fun i j => (hA i j).mono hU_D) (hβ.mono hU_D) (hγ.mono hU_D) (hFEs.mono hU_D)
    (hmem.toLp FE) hmem.coeFn_toLp huw
  obtain ⟨g', hg', hug', hpw⟩ := pde_weak_sol_smooth_interior (Ω := ΩE) hE'b hε0 hε
    (fun i j => (hA i j).continuousOn.mono hcl_D) (hβ.continuousOn.mono hcl_D)
    (hγ.continuousOn.mono hcl_D) (fun x hx => hell x (hE_D hx)) (fun x hx => hγ0 x (hE_D hx))
    (fun i j => (hA i j).mono hE_D) (hβ.mono hE_D) (hγ.mono hE_D) (hFEs.mono hE_D)
    (hmem.toLp FE) hmem.coeFn_toLp huw
  -- the two representatives agree on the open set `e(D')`
  have hgg : EqOn g g' (e '' D') :=
    Measure.eqOn_open_of_ae_eq (hug.symm.trans hug') hE'o (hg.continuousOn.mono subset_closure)
      hg'.continuousOn
  -- pull back: `u = g ∘ e`
  refine ⟨fun z => g (e z), ?_, ?_, ?_⟩
  · refine hg.comp e.contDiff.contDiffOn ?_
    intro z hz
    show e z ∈ closure (e '' D')
    rw [hE'cl]
    exact mem_image_of_mem e hz
  · intro w hw
    have hx : e w ∈ e '' D' := mem_image_of_mem e hw
    have hxD : e w ∈ e '' D := hE_D hx
    have hgc : ContDiffAt ℝ 2 g (e w) :=
      (hg.contDiffAt (mem_of_superset (hE'o.mem_nhds hx) subset_closure)).of_le
        (by simp)
    have h1 := hL g (e w) hxD hgc
    rw [s05_p6_div_congr hE'o hx hgg, hpw (e w) hx, LinearIsometryEquiv.symm_apply_apply] at h1
    simp only [hFE, LinearIsometryEquiv.symm_apply_apply] at h1
    exact mul_left_cancel₀ (hρ0 (e w) hxD).ne' h1
  · intro w hw
    have hfr : frontier (e '' D') = e '' frontier D' := (e.toHomeomorph.image_frontier D').symm
    exact hg0 (e w) (show e w ∈ frontier (e '' D') by rw [hfr]; exact mem_image_of_mem e hw)

/-- W-PDE1 D0 (Dirichlet solvability, GT 6.14/6.19): for `𝓛` `ε'`-admissible on `D` and a smooth
relatively compact `D' ⋐ D`, the Dirichlet problem `𝓛 u = F` in `D'`, `u = 0` on `∂D'`, has a
solution `u ∈ C^∞(\overline{D'})` for every `F` smooth on `D`.  The non-adjoint twin of
`s05_dual_dirichlet_sol`; closed by W-PDE1 P5/P6.  Users: w6 W-PDE2 (the Dirichlet solutions
along a smooth exhaustion in `prop_dirichlet_a`).  Frozen stub. -/
theorem s05_dirichlet_sol : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (D : Set ℂ) (ε' : ℝ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsAdmissibleOp Ω D ε' aUp bUp c → ∀ D' : Set ℂ, IsSmoothRelCompactIn D' D →
      ∀ F : ℂ → ℝ, ContDiffOn ℝ ∞ F D →
        ∃ u : ℂ → ℝ, IsDirichletSol Ω aUp bUp c D' F u := by
  intro Ω Ωs hJ D ε' aUp bUp c h D' hD' F hF
  obtain ⟨A, β, γ, hA, hβ, hγ, hρ, -, hell, hγ0, hρ0, hid⟩ := s05_pde_bridge hJ h
  exact s05_p6_core (L := ellOp Ω aUp bUp c) h.2.2.1 hD' h.1.le (by linarith [h.2.1]) hA hβ hγ
    hρ hell hγ0 (fun x hx => pow_pos (hρ0 x hx) 2) hid hF

/-- W-PDE1 D1 (dual Dirichlet solvability, GT 6.14/6.19): for `𝓛` `ε'`-admissible on `D` and a
smooth relatively compact `D' ⋐ D`, the adjoint Dirichlet problem `𝓛* z = κ` in `D'`, `z = 0` on
`∂D'`, has a solution `z ∈ C^∞(\overline{D'})` for every `κ` smooth on `D`.  (`ellOpAdj` is
`ellOp` with the coefficients `adjCoeffB`, `adjCoeffC`.)  Users: w6 W-AMBUP (S09 W4) and the
`zₙ` of `prop_dirichlet_b`/(5.13) in `prop_dirichlet_c`.  Frozen stub (W1_IFACE_w6.md D1). -/
theorem s05_dual_dirichlet_sol : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (D : Set ℂ) (ε' : ℝ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsAdmissibleOp Ω D ε' aUp bUp c → ∀ D' : Set ℂ, IsSmoothRelCompactIn D' D →
      ∀ κ : ℂ → ℝ, ContDiffOn ℝ ∞ κ D →
        ∃ z : ℂ → ℝ, IsDirichletSol Ω aUp (adjCoeffB Ω aUp bUp) (adjCoeffC Ω aUp bUp c) D' κ z := by
  intro Ω Ωs hJ D ε' aUp bUp c h D' hD' κ hκ
  obtain ⟨A, β, γ, hA, hβ, hγ, hρ, -, hell, hγ0, hρ0, hid⟩ := s05_pde_bridge hJ h
  obtain ⟨hbs, hcs⟩ := s05_p6_adj_smooth hJ h
  set e := Complex.orthonormalBasisOneI.repr with he
  have hmem : ∀ x ∈ e '' D, e.symm x ∈ D := by
    rintro _ ⟨w, hw, rfl⟩
    simpa using hw
  -- `γ = ρ² c` on `e(D)`: the identity at the constant `1`
  have hγc : ∀ x ∈ e '' D, γ x = poincareDensity Ω (e.symm x) ^ 2 * c (e.symm x) := by
    intro x hx
    have h1 := hid (fun _ => 1) x hx contDiffAt_const
    beta_reduce at h1
    rw [s05_ellOp_const_one] at h1
    simp only [fderiv_fun_const, Pi.zero_apply, zero_apply,
      mul_zero, Finset.sum_const_zero, neg_zero, zero_add, mul_one] at h1
    exact h1.symm
  -- the adjoint data: `β* = β - ρ² (b* - b) ∘ e⁻¹`, `γ* = ρ² c* ∘ e⁻¹`
  set bd : ℂ → Fin 2 → ℝ := fun w k => adjCoeffB Ω aUp bUp w k - bUp w k with hbd
  have hbdv : ContDiffOn ℝ ∞ bd D := contDiffOn_pi.2 fun k => (hbs k).sub (h.2.2.2.2.1.2.1 k)
  refine s05_p6_core (L := ellOp Ω aUp (adjCoeffB Ω aUp bUp) (adjCoeffC Ω aUp bUp c))
    (β := fun x => β x - poincareDensity Ω (e.symm x) ^ 2 •
      (EuclideanSpace.equiv (Fin 2) ℝ).symm (bd (e.symm x)))
    (γ := fun x => poincareDensity Ω (e.symm x) ^ 2 * adjCoeffC Ω aUp bUp c (e.symm x))
    h.2.2.1 hD' h.1.le (by linarith [h.2.1]) hA ?_ ?_ hρ hell ?_
    (fun x hx => pow_pos (hρ0 x hx) 2) ?_ hκ
  · exact hβ.sub (hρ.smul ((EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp_contDiffOn
      (pde_contDiffOn_comp_symm hbdv)))
  · exact hρ.mul (pde_contDiffOn_comp_symm hcs)
  · intro x hx
    have := (lem_test_functions_d Ω Ωs hJ D ε' aUp bUp c h _ (hmem x hx)).2.2.2
    positivity
  · intro g x hx hg
    simp only [← he]
    have hex : e (e.symm x) = x := by simp
    have hd : DifferentiableAt ℝ g (e (e.symm x)) := by
      rw [hex]
      exact hg.differentiableAt (by norm_num)
    have hfr : ∀ j : Fin 2, fderiv ℝ (fun z => g (e z)) (e.symm x) (frameVec j) =
        fderiv ℝ g x (EuclideanSpace.single j 1) := fun j => by
      rw [pde_fderiv_comp hd, hex]
    rw [s05_p6_lin Ω aUp bUp (adjCoeffB Ω aUp bUp) c (adjCoeffC Ω aUp bUp c), mul_sub, mul_add,
      hid g x hx hg]
    simp only [hfr, hex, hγc x hx, Fin.sum_univ_two, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, hbd]
    simp only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply]
    ring

/-- W-EXH (E1): a smooth cut-off `g ≥ 0` with `{g > 0} = D` and decay `g (1 + ‖x‖²) ≤ 1`
(`g = f/(1 + ‖x‖²)`, `f` from `IsOpen.exists_contDiff_support_eq`). -/
theorem s05_ex_cutoff {D : Set ℂ} (hD : IsOpen D) :
    ∃ g : ℂ → ℝ, ContDiff ℝ ∞ g ∧ (∀ x, 0 ≤ g x) ∧ (∀ x, g x * (1 + ‖x‖ ^ 2) ≤ 1) ∧
      ∀ x, 0 < g x ↔ x ∈ D := by
  obtain ⟨f, hfs, hf, hfr⟩ := hD.exists_contDiff_support_eq (n := ⊤)
  have hpos : ∀ x : ℂ, 0 < 1 + ‖x‖ ^ 2 := fun x => by positivity
  have hf01 : ∀ x, f x ∈ Icc (0 : ℝ) 1 := fun x => hfr (mem_range_self x)
  refine ⟨fun x => f x / (1 + ‖x‖ ^ 2), ?_, fun x => div_nonneg (hf01 x).1 (hpos x).le,
    fun x => ?_, fun x => ?_⟩
  · exact hf.div (contDiff_const.add (contDiff_norm_sq ℝ)) fun x => (hpos x).ne'
  · rw [div_mul_cancel₀ _ (hpos x).ne']
    exact (hf01 x).2
  · rw [div_pos_iff_of_pos_right (hpos x), ← hfs, Function.mem_support]
    exact ⟨fun h => h.ne', fun h => lt_of_le_of_ne (hf01 x).1 (Ne.symm h)⟩

/-- W-EXH (E2): the gradient `Φ` of `h = 1/g` on `D`, `dh_x(v) = Re(conj (Φ x) · v)`, is smooth
on `D`. -/
theorem s05_ex_grad {D : Set ℂ} (hD : IsOpen D) {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hpos : ∀ x ∈ D, 0 < g x) :
    ∃ Φ : ℂ → ℂ, ContDiffOn ℝ ∞ Φ D ∧
      ∀ x ∈ D, ∀ v : ℂ, fderiv ℝ (fun y => (g y)⁻¹) x v = (conj (Φ x) * v).re := by
  -- `k = 1/g` is smooth on `D`, hence so is `fderiv k`
  have hk : ContDiffOn ℝ ∞ (fun y => (g y)⁻¹) D := hg.contDiffOn.inv fun x hx => (hpos x hx).ne'
  have hdk : ContDiffOn ℝ ∞ (fderiv ℝ (fun y => (g y)⁻¹)) D :=
    hk.fderiv_of_isOpen hD (by simp)
  refine ⟨fun x => ((fderiv ℝ (fun y => (g y)⁻¹) x 1 : ℝ) : ℂ) +
    ((fderiv ℝ (fun y => (g y)⁻¹) x I : ℝ) : ℂ) * I, ?_, fun x _ v => ?_⟩
  · have h1 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ (fun y => (g y)⁻¹) x 1) D :=
      hdk.clm_apply contDiffOn_const
    have h2 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ (fun y => (g y)⁻¹) x I) D :=
      hdk.clm_apply contDiffOn_const
    exact (ofRealCLM.contDiff.comp_contDiffOn h1).add
      ((ofRealCLM.contDiff.comp_contDiffOn h2).mul contDiffOn_const)
  · -- `v = v.re • 1 + v.im • I`
    have hv : v = v.re • (1 : ℂ) + v.im • I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring

/-- W-EXH (E3, easy Sard for `Φ : D → ℂ`): some `a` is a regular value of `Φ` on `D`
(`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`). -/
theorem s05_ex_sard {D : Set ℂ} (hD : IsOpen D) {Φ : ℂ → ℂ} (hΦ : ContDiffOn ℝ ∞ Φ D) :
    ∃ a : ℂ, ∀ x ∈ D, Φ x = a → (fderiv ℝ Φ x).det ≠ 0 := by
  -- the singular set `S` of `Φ` in `D` has a null image (equidimensional easy Sard)
  set S := {x | x ∈ D ∧ (fderiv ℝ Φ x).det = 0} with hS
  have hder : ∀ x ∈ S, HasFDerivWithinAt Φ (fderiv ℝ Φ x) S x := fun x hx =>
    (((hΦ.differentiableOn (by simp)) x hx.1).differentiableAt
      (hD.mem_nhds hx.1)).hasFDerivAt.hasFDerivWithinAt
  have hnull : volume (Φ '' S) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume hder fun x hx => hx.2
  have hne : Φ '' S ≠ univ := by
    intro h
    rw [h] at hnull
    exact isOpen_univ.measure_ne_zero volume univ_nonempty hnull
  obtain ⟨a, ha⟩ := (ne_univ_iff_exists_notMem _).1 hne
  refine ⟨a, fun x hx hxa hdet => ha ⟨x, ⟨hx, hdet⟩, hxa⟩⟩

/-- W-EXH (E4): where `dΦ_x` is invertible, `x` is isolated in `Φ⁻¹(a)` (inverse function
theorem). -/
theorem s05_ex_isolated {D : Set ℂ} (hD : IsOpen D) {Φ : ℂ → ℂ} (hΦ : ContDiffOn ℝ ∞ Φ D) {a x : ℂ}
    (hx : x ∈ D) (hdet : (fderiv ℝ Φ x).det ≠ 0) : ∀ᶠ y in 𝓝[≠] x, Φ y ≠ a := by
  have hdiff : DifferentiableAt ℝ Φ x :=
    ((hΦ.differentiableOn (by simp)) x hx).differentiableAt (hD.mem_nhds hx)
  by_cases hxa : Φ x = a
  · -- `dΦ_x` is invertible, so `Φ y ≠ Φ x` for `y ≠ x` near `x`
    set e := ((fderiv ℝ Φ x : ℂ →ₗ[ℝ] ℂ).equivOfDetNeZero hdet).toContinuousLinearEquiv with he
    have hanti : AntilipschitzWith ‖(e.symm : ℂ →L[ℝ] ℂ)‖₊ (fderiv ℝ Φ x) := by
      refine ContinuousLinearMap.antilipschitz_of_bound _ fun z => ?_
      have hz : (e.symm : ℂ →L[ℝ] ℂ) (fderiv ℝ Φ x z) = z := e.symm_apply_apply z
      calc ‖z‖ = ‖(e.symm : ℂ →L[ℝ] ℂ) (fderiv ℝ Φ x z)‖ := by rw [hz]
        _ ≤ ‖(e.symm : ℂ →L[ℝ] ℂ)‖ * ‖fderiv ℝ Φ x z‖ := ContinuousLinearMap.le_opNorm _ _
        _ = _ := rfl
    rw [← hxa]
    exact hdiff.hasFDerivAt.eventually_ne ⟨_, hanti⟩
  · exact nhdsWithin_le_nhds (hdiff.continuousAt.eventually_ne hxa)

/-- W-EXH (E5): if `Φ⁻¹(a) ∩ D` is discrete, the values of `H` on it are countable, so there are
levels `c_n ∈ (n, n+1)`, strictly increasing, avoiding them. -/
theorem s05_ex_levels {D : Set ℂ} {Φ : ℂ → ℂ} {a : ℂ} {H : ℂ → ℝ}
    (hiso : ∀ x ∈ D, Φ x = a → ∀ᶠ y in 𝓝[≠] x, Φ y ≠ a) :
    ∃ c : ℕ → ℝ, StrictMono c ∧ (∀ n : ℕ, (n : ℝ) < c n) ∧
      ∀ n, ∀ x ∈ D, Φ x = a → H x ≠ c n := by
  -- `Z = Φ⁻¹(a) ∩ D` is discrete, hence countable (`ℂ` is hereditarily Lindelöf)
  set Z := {x | x ∈ D ∧ Φ x = a} with hZ
  have hdisc : IsDiscrete Z := by
    rw [isDiscrete_iff_nhdsNE]
    intro x hx
    rw [← disjoint_iff, disjoint_principal_right]
    filter_upwards [hiso x hx.1 hx.2] with y hy hyZ
    exact hy hyZ.2
  have hcnt : (H '' Z).Countable :=
    ((HereditarilyLindelofSpace.isLindelof Z).countable_of_isDiscrete hdisc).image H
  have hex : ∀ n : ℕ, ∃ t ∈ (H '' Z)ᶜ, t ∈ Ioo (n : ℝ) (n + 1) := fun n =>
    (hcnt.dense_compl ℝ).exists_between (by linarith)
  choose c hcZ hcI using hex
  refine ⟨c, strictMono_nat_of_lt_succ fun n => (hcI n).2.trans ?_, fun n => (hcI n).1,
    fun n x hx hxa hHx => hcZ n ⟨x, ⟨hx, hxa⟩, hHx⟩⟩
  have := (hcI (n + 1)).1
  push_cast at this
  exact this

/-- W-EXH (E6): `ψ = 1 - g (c + Re(conj a · x))` is smooth, `{ψ ≤ 0}` is compact and inside `D`,
and `{ψ < 0}`, `{ψ ≤ 0}` are the sublevel sets `{h_a < c}`, `{h_a ≤ c}` of
`h_a = 1/g - Re(conj a · x)` on `D`. -/
theorem s05_ex_level {D : Set ℂ} {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hg0 : ∀ x, 0 ≤ g x)
    (hgd : ∀ x, g x * (1 + ‖x‖ ^ 2) ≤ 1) (hgD : ∀ x, 0 < g x ↔ x ∈ D) (a : ℂ) (c : ℝ) :
    ContDiff ℝ ∞ (fun x => 1 - g x * (c + (conj a * x).re)) ∧
      IsCompact {x | 1 - g x * (c + (conj a * x).re) ≤ 0} ∧
      {x | 1 - g x * (c + (conj a * x).re) ≤ 0} ⊆ D ∧
      {x | 1 - g x * (c + (conj a * x).re) < 0} = {x | x ∈ D ∧ (g x)⁻¹ - (conj a * x).re < c} ∧
      {x | 1 - g x * (c + (conj a * x).re) ≤ 0} = {x | x ∈ D ∧ (g x)⁻¹ - (conj a * x).re ≤ c} := by
  have hR : ContDiff ℝ ∞ (fun x : ℂ => (conj a * x).re) :=
    reCLM.contDiff.comp (contDiff_const.mul contDiff_id)
  have hsm : ContDiff ℝ ∞ (fun x => 1 - g x * (c + (conj a * x).re)) :=
    contDiff_const.sub (hg.mul (contDiff_const.add hR))
  have hRle : ∀ x : ℂ, (conj a * x).re ≤ ‖a‖ * ‖x‖ := fun x =>
    (Complex.re_le_norm _).trans (by rw [norm_mul, Complex.norm_conj])
  -- off `D`, `g = 0` and `ψ = 1`
  have hoff : ∀ x, 1 - g x * (c + (conj a * x).re) ≤ 0 → x ∈ D := by
    intro x hx
    by_contra hn
    have h0 : g x = 0 := le_antisymm (not_lt.1 fun h => hn ((hgD x).1 h)) (hg0 x)
    rw [h0] at hx
    norm_num at hx
  -- boundedness: `‖x‖ ≤ |c| + ‖a‖ + 1` on `{ψ ≤ 0}`
  have hbd : {x | 1 - g x * (c + (conj a * x).re) ≤ 0} ⊆ closedBall 0 (|c| + ‖a‖ + 1) := by
    intro x hx
    have hx' : 1 - g x * (c + (conj a * x).re) ≤ 0 := hx
    rw [mem_closedBall, dist_zero_right]
    by_contra ht
    push Not at ht
    have t0 := norm_nonneg x
    have a0 := norm_nonneg a
    have hc := le_abs_self c
    have hc0 := abs_nonneg c
    have h2 := hg0 x
    -- `1 ≤ g (c + R) ≤ g (|c| + ‖a‖ t)` and `|c| + ‖a‖ t + (1 + t) ≤ 1 + t²`
    have h4 : g x * (c + (conj a * x).re) ≤ g x * (|c| + ‖a‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (by linarith [hRle x]) h2
    have h5 : |c| + ‖a‖ * ‖x‖ + (1 + ‖x‖) ≤ 1 + ‖x‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left ht.le t0,
        mul_nonneg (by linarith : (0 : ℝ) ≤ ‖x‖ - 1) hc0]
    have h6 : g x * (1 + ‖x‖) ≤ 0 := by
      nlinarith [mul_le_mul_of_nonneg_left h5 h2, hgd x]
    have h7 : g x * (1 + ‖x‖) = 0 := le_antisymm h6 (mul_nonneg h2 (by positivity))
    have h8 : g x = 0 := (mul_eq_zero.1 h7).resolve_right (by positivity)
    rw [h8] at hx'
    norm_num at hx'
  -- on `D`: `ψ = g (h_a - c)` with `g > 0`
  have hkey : ∀ x ∈ D, ((g x)⁻¹ - (conj a * x).re < c ↔ 1 - g x * (c + (conj a * x).re) < 0) ∧
      ((g x)⁻¹ - (conj a * x).re ≤ c ↔ 1 - g x * (c + (conj a * x).re) ≤ 0) := by
    intro x hx
    have hp := (hgD x).2 hx
    have hi : g x * (g x)⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
    · nlinarith [mul_lt_mul_of_pos_left h hp]
    · by_contra hn
      push Not at hn
      nlinarith [mul_le_mul_of_nonneg_left hn hp.le]
    · nlinarith [mul_le_mul_of_nonneg_left h hp.le]
    · by_contra hn
      push Not at hn
      nlinarith [mul_lt_mul_of_pos_left hn hp]
  refine ⟨hsm, (isCompact_closedBall 0 _).of_isClosed_subset
    (isClosed_le hsm.continuous continuous_const) hbd, fun x hx => hoff x hx, ?_, ?_⟩
  · ext x
    simp only [mem_ofPred_eq]
    exact ⟨fun h => ⟨hoff x h.le, ((hkey x (hoff x h.le)).1).2 h⟩,
      fun h => ((hkey x h.1).1).1 h.2⟩
  · ext x
    simp only [mem_ofPred_eq]
    exact ⟨fun h => ⟨hoff x h, ((hkey x (hoff x h)).2).2 h⟩, fun h => ((hkey x h.1).2).1 h.2⟩

/-- W-EXH (E7): `ψ = 1 - g (c + Re(conj a · x))` is regular on `{ψ = 0}` when `c` is not a
critical value of `h_a` (there `dψ = g dh_a`). -/
theorem s05_ex_regular {D : Set ℂ} {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hg0 : ∀ x, 0 ≤ g x)
    (hgD : ∀ x, 0 < g x ↔ x ∈ D) {Φ : ℂ → ℂ}
    (hΦ : ∀ x ∈ D, ∀ v : ℂ, fderiv ℝ (fun y => (g y)⁻¹) x v = (conj (Φ x) * v).re) (a : ℂ) (c : ℝ)
    (hc : ∀ x ∈ D, Φ x = a → (g x)⁻¹ - (conj a * x).re ≠ c) :
    ∀ w, 1 - g w * (c + (conj a * w).re) = 0 →
      fderiv ℝ (fun x => 1 - g x * (c + (conj a * x).re)) w ≠ 0 := by
  intro w hw
  have hgw : 0 < g w := by
    rcases (hg0 w).lt_or_eq with h | h
    · exact h
    · rw [← h] at hw
      norm_num at hw
  have hwD : w ∈ D := (hgD w).1 hgw
  have hgdw : DifferentiableAt ℝ g w := hg.differentiable (by simp) w
  have hG : HasFDerivAt g (fderiv ℝ g w) w := hgdw.hasFDerivAt
  have hI : HasFDerivAt (fun y => (g y)⁻¹) (fderiv ℝ (fun y => (g y)⁻¹) w) w :=
    (hgdw.inv hgw.ne').hasFDerivAt
  have hL : HasFDerivAt (fun y : ℂ => (conj a * y).re)
      (reCLM.comp ((conj a) • ContinuousLinearMap.id ℝ ℂ)) w :=
    (reCLM.comp ((conj a) • ContinuousLinearMap.id ℝ ℂ)).hasFDerivAt
  -- `k = h_a - c`, with `k w = 0` on the level
  have hk := (hI.sub hL).sub_const c
  have hkw : (g w)⁻¹ - (conj a * w).re - c = 0 := by
    have hi : g w * (g w)⁻¹ = 1 := mul_inv_cancel₀ hgw.ne'
    have h1 : g w * ((g w)⁻¹ - (conj a * w).re - c) = 0 := by
      rw [mul_sub, mul_sub, hi]
      linarith
    exact (mul_eq_zero.1 h1).resolve_left hgw.ne'
  -- near `w`, `ψ = g k`
  have hev : (fun x => 1 - g x * (c + (conj a * x).re)) =ᶠ[𝓝 w]
      fun y => g y * ((g y)⁻¹ - (conj a * y).re - c) := by
    filter_upwards [continuousAt_const.eventually_lt hg.continuous.continuousAt hgw] with y hy
    rw [mul_sub, mul_sub, mul_inv_cancel₀ hy.ne']
    ring
  have hfd := ((hG.mul hk).congr_of_eventuallyEq hev).fderiv
  intro hzero
  rw [hfd] at hzero
  have h1 := congrArg (fun T : ℂ →L[ℝ] ℝ => T (Φ w - a)) hzero
  simp only [_root_.add_apply, _root_.smul_apply, _root_.sub_apply, Pi.sub_apply, smul_eq_mul,
    hkw, zero_mul, add_zero, hΦ w hwD, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    reCLM_apply] at h1
  -- `Re(conj Φ z) - Re(conj a z) = |z|²` for `z = Φ w - a`
  have h2 : (conj (Φ w) * (Φ w - a)).re - (conj a * (Φ w - a)).re = Complex.normSq (Φ w - a) := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
      Complex.normSq_apply]
    ring
  rw [h2] at h1
  have h3 : Φ w = a :=
    sub_eq_zero.1 (Complex.normSq_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hgw.ne'))
  exact hc w hwD h3 (by linarith)

/-- W-EXH (frozen stub, the only isolation point of the wall): every open `D ⊆ ℂ` has a smooth
exhaustion `D₁ ⋐ D₂ ⋐ ⋯` by smooth relatively compact open sets (regular sublevel sets of smooth
proper functions; sec05-upper.tex proof of `prop:dirichlet`, via Sard).  Users: `prop_dirichlet_b`
(through `s05_weighted_dirichlet`) and `s05_dinv_nonneg`. -/
theorem s05_smooth_exhaustion : ∀ D : Set ℂ, IsOpen D → ∃ Dn : ℕ → Set ℂ, IsSmoothExhaustion D Dn := by
  intro D hD
  obtain ⟨g, hg, hg0, hgd, hgD⟩ := s05_ex_cutoff hD
  obtain ⟨Φ, hΦ, hdΦ⟩ := s05_ex_grad hD hg fun x hx => (hgD x).2 hx
  obtain ⟨a, ha⟩ := s05_ex_sard hD hΦ
  obtain ⟨c, hcm, hcn, hc⟩ := s05_ex_levels (D := D) (Φ := Φ) (a := a)
    (H := fun x => (g x)⁻¹ - (conj a * x).re)
    fun x hx _ => s05_ex_isolated hD hΦ hx (ha x hx ‹_›)
  have hL := fun n => s05_ex_level hg hg0 hgd hgD a (c n)
  -- `closure {ψₙ < 0} ⊆ {ψₙ ≤ 0}`
  have hcl : ∀ n, closure {x | 1 - g x * (c n + (conj a * x).re) < 0} ⊆
      {x | 1 - g x * (c n + (conj a * x).re) ≤ 0} := fun n =>
    closure_minimal (fun x hx => le_of_lt (show 1 - g x * (c n + (conj a * x).re) < 0 from hx))
      (isClosed_le (hL n).1.continuous continuous_const)
  unfold IsSmoothExhaustion IsSmoothRelCompactIn
  refine ⟨fun n => {x | 1 - g x * (c n + (conj a * x).re) < 0}, fun n => ?_, fun n => ?_, ?_⟩
  · -- `IsSmoothRelCompactIn`: open, compact closure, closure in `D`, a regular defining function
    obtain ⟨hsm, hK, hKD, -, -⟩ := hL n
    exact ⟨isOpen_lt hsm.continuous continuous_const, hK.of_isClosed_subset isClosed_closure (hcl n), (hcl n).trans hKD,
      fun x => 1 - g x * (c n + (conj a * x).re), hsm, rfl,
      s05_ex_regular hg hg0 hgD hdΦ a (c n) (hc n)⟩
  · -- nesting: `closure {h_a < cₙ} ⊆ {h_a ≤ cₙ} ⊆ {h_a < cₙ₊₁}`
    refine (hcl n).trans ?_
    beta_reduce
    rw [(hL n).2.2.2.2, (hL (n + 1)).2.2.2.1]
    exact fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 (hcm (Nat.lt_succ_self n))⟩
  · -- the union is `D`
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      exact (hL n).2.2.1 (le_of_lt (show 1 - g x * (c n + (conj a * x).re) < 0 from hn))
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt ((g x)⁻¹ - (conj a * x).re)
      refine ⟨n, ?_⟩
      have h1 : x ∈ {x | x ∈ D ∧ (g x)⁻¹ - (conj a * x).re < c n} := ⟨hx, hn.trans (hcn n)⟩
      rw [← (hL n).2.2.2.1] at h1
      exact h1

/-- W4 helper: `ε'`-admissibility passes to open subsets. -/
theorem s05_wd_admissible_mono {Ω D D' : Set ℂ} {ε' : ℝ} {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ}
    {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ} (h : IsAdmissibleOp Ω D ε' aUp bUp c) (hD' : IsOpen D')
    (hsub : D' ⊆ D) : IsAdmissibleOp Ω D' ε' aUp bUp c := by
  unfold IsAdmissibleOp IsSmoothOp at h ⊢
  obtain ⟨h1, h2, -, hDΩ, ⟨ha, hb, hc, hs⟩, hn⟩ := h
  refine ⟨h1, h2, hD', hsub.trans hDΩ, ⟨fun i j => (ha i j).mono hsub, fun i => (hb i).mono hsub,
    hc.mono hsub, fun w hw => hs w (hsub hw)⟩, le_trans ?_ hn⟩
  have hm : ∀ (k j : ℕ) (T : TensorField k), rhoCjNorm Ω j T D' ≤ rhoCjNorm Ω j T D :=
    fun k j T => iSup₂_mono fun i _ => biSup_mono fun w hw => hsub hw
  exact add_le_add (add_le_add (hm _ _ _) (hm _ _ _)) (hm _ _ _)

/-- W4 helper: a function continuous on `closure D'` and `≤ 0` on `∂D'` satisfies the boundary
hypothesis of `lem_comparison`. -/
theorem s05_wd_bdry {Ω D' : Set ℂ} {v : ℂ → ℝ} (hv : ContinuousOn v (closure D'))
    (hb : ∀ w ∈ frontier D', v w ≤ 0) :
    ∀ wb ∈ frontier D' ∩ Ω, ∀ δ : ℝ, 0 < δ → ∀ᶠ w in 𝓝[D'] wb, v w ≤ δ := by
  intro wb hwb δ hδ
  have hc := hv wb (frontier_subset_closure hwb.1)
  have h1 : ∀ᶠ w in 𝓝[closure D'] wb, v w < δ :=
    Filter.Tendsto.eventually hc (gt_mem_nhds (by linarith [hb wb hwb.1]))
  exact Filter.Eventually.mono (nhdsWithin_mono wb subset_closure h1) fun w hw => hw.le

/-- W4 helper: a function continuous on a compact `closure D'` is bounded above on `D'`. -/
theorem s05_wd_bdd {D' : Set ℂ} {v : ℂ → ℝ} (hK : IsCompact (closure D'))
    (hv : ContinuousOn v (closure D')) : BddAbove (v '' D') := by
  exact BddAbove.mono (image_mono subset_closure) (hK.bddAbove_image hv)

/-- W4 helper: a function continuous on a compact `closure D' ⊆ Ω` is `dâ`-integrable on `D'`. -/
theorem s05_wd_integrableOn {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {D' : Set ℂ}
    (hK : IsCompact (closure D')) (hKΩ : closure D' ⊆ Ω) {g : ℂ → ℝ}
    (hg : ContinuousOn g (closure D')) : IntegrableOn g D' (hypArea Ω) := by
  have hKm : MeasurableSet (closure D') := isClosed_closure.measurableSet
  obtain ⟨-, hl, -⟩ := s05_density_smooth hJ
  obtain ⟨Cl, hCl⟩ := hK.exists_bound_of_continuousOn ((hl.continuousOn.mono hKΩ).pow 2)
  have hfin : hypArea Ω (closure D') ≠ ⊤ := by
    unfold hypArea
    rw [withDensity_apply _ hKm, Measure.restrict_restrict hKm, inter_eq_left.mpr hKΩ]
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := Cl)) (hK.measure_lt_top (μ := volume)).ne) ?_
    calc ∫⁻ w in closure D', ENNReal.ofReal (poincareDensity Ω w ^ 2)
        ≤ ∫⁻ w in closure D', ENNReal.ofReal Cl :=
          setLIntegral_mono' hKm fun w hw =>
            ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hCl w hw))
      _ = ENNReal.ofReal Cl * volume (closure D') := setLIntegral_const _ _
  have : IsFiniteMeasure ((hypArea Ω).restrict (closure D')) := isFiniteMeasure_restrict.mpr hfin
  obtain ⟨Cg, hCg⟩ := hK.exists_bound_of_continuousOn hg
  have hI : IntegrableOn g (closure D') (hypArea Ω) :=
    Integrable.of_bound (hg.aestronglyMeasurable hKm) Cg (ae_restrict_of_forall_mem hKm hCg)
  exact hI.mono_set subset_closure

/-- W4 helper (Fatou): if `1_{Dₙ} fₙ → g` on `D` and `∫_{Dₙ} fₙ⁺ ≤ B` for all `n`, then
`∫_D g⁺ ≤ B`. -/
theorem s05_wd_fatou {μ : Measure ℂ} {D : Set ℂ} (hD : IsOpen D) {Dn : ℕ → Set ℂ}
    (hDn : ∀ n, IsOpen (Dn n)) (hsub : ∀ n, Dn n ⊆ D) {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ}
    (hf : ∀ n, ContinuousOn (f n) (Dn n))
    (hg : ∀ w ∈ D, Tendsto (fun n => (Dn n).indicator (f n) w) atTop (𝓝 (g w))) {B : ℝ≥0∞}
    (hB : ∀ n, ∫⁻ w in Dn n, ENNReal.ofReal (f n w) ∂μ ≤ B) :
    ∫⁻ w in D, ENNReal.ofReal (g w) ∂μ ≤ B := by
  -- `hsub` is not needed: the bound only uses `Dₙ` through `hf`, `hg`, `hB` (the statement stays
  -- true without it).
  have _h := hsub
  -- measurability of `(1_{Dₙ} fₙ)⁺` comes from the continuity of `fₙ` on the open `Dₙ`
  have hm : ∀ n, AEMeasurable (fun w => ENNReal.ofReal ((Dn n).indicator (f n) w)) (μ.restrict D) :=
    fun n => ENNReal.measurable_ofReal.comp_aemeasurable
      ((aemeasurable_indicator_iff (hDn n).measurableSet).mpr
        ((hf n).aemeasurable (hDn n).measurableSet)).restrict
  have hDm : MeasurableSet D := hD.measurableSet
  calc ∫⁻ w in D, ENNReal.ofReal (g w) ∂μ
      = ∫⁻ w in D, liminf (fun n => ENNReal.ofReal ((Dn n).indicator (f n) w)) atTop ∂μ := by
        refine setLIntegral_congr_fun hDm fun w hw => ?_
        exact (((ENNReal.continuous_ofReal.tendsto _).comp (hg w hw)).liminf_eq).symm
    _ ≤ liminf (fun n => ∫⁻ w in D, ENNReal.ofReal ((Dn n).indicator (f n) w) ∂μ) atTop :=
        lintegral_liminf_le' hm
    _ ≤ B := by
        refine liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
        calc ∫⁻ w in D, ENNReal.ofReal ((Dn n).indicator (f n) w) ∂μ
            ≤ ∫⁻ w, ENNReal.ofReal ((Dn n).indicator (f n) w) ∂μ := setLIntegral_le_lintegral _ _
          _ = ∫⁻ w, (Dn n).indicator (fun x => ENNReal.ofReal (f n x)) w ∂μ := by
              refine lintegral_congr fun w => ?_
              by_cases hw : w ∈ Dn n <;> simp [hw]
          _ = ∫⁻ w in Dn n, ENNReal.ofReal (f n w) ∂μ := lintegral_indicator (hDn n).measurableSet _
          _ ≤ B := hB n

/-- W-PDE2 A helper: a Dirichlet solution is `C²` at the points of the open `D'`, `C²` on `D'`
and continuous on `closure D'`. -/
theorem s05_dp_a_sol_reg {Ω D' : Set ℂ} {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ}
    {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ} {F u : ℂ → ℝ} (hD' : IsOpen D')
    (hu : IsDirichletSol Ω aUp bUp c D' F u) :
    (∀ x ∈ D', ContDiffAt ℝ 2 u x) ∧ ContDiffOn ℝ 2 u D' ∧ ContinuousOn u (closure D') :=
  ⟨fun x hx => ((hu.1.mono subset_closure).contDiffAt (hD'.mem_nhds hx)).of_le (by simp),
    (hu.1.mono subset_closure).of_le (by simp), hu.1.continuousOn⟩

/-- W-PDE2 A helper: `𝓛(f - s) = 𝓛f - s c` at a point where `f` is `C²`. -/
theorem s05_dp_a_ellOp_sub_const {Ω : Set ℂ} (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ) {f : ℂ → ℝ} {w : ℂ} (hf : ContDiffAt ℝ 2 f w) (s : ℝ) :
    ellOp Ω aUp bUp c (fun x => f x - s) w = ellOp Ω aUp bUp c f w - s * c w := by
  have h := s05_ellOp_sub (Ω := Ω) aUp bUp c hf (contDiffAt_const (c := (1 : ℝ))) s
  rw [s05_ellOp_const_one] at h
  simpa only [mul_one] using h

/-- W-PDE2 A helper: `𝓛(-u) = -𝓛u` at a point where `u` is `C²`. -/
theorem s05_dp_a_ellOp_neg {Ω : Set ℂ} (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ) {u : ℂ → ℝ} {w : ℂ} (hu : ContDiffAt ℝ 2 u w) :
    ellOp Ω aUp bUp c (fun x => -u x) w = -ellOp Ω aUp bUp c u w := by
  have h0 : ellOp Ω aUp bUp c (fun _ => (0 : ℝ)) w = 0 := by
    have h := s05_dp_a_ellOp_sub_const (Ω := Ω) aUp bUp c (f := fun _ => (1 : ℝ)) (w := w)
      contDiffAt_const 1
    rw [s05_ellOp_const_one] at h
    simpa only [sub_self, one_mul] using h
  have h := s05_ellOp_sub (Ω := Ω) aUp bUp c (f := fun _ => (0 : ℝ)) (w := w) contDiffAt_const hu 1
  rw [h0] at h
  simpa only [zero_sub, one_mul] using h

/-- W-PDE2 A helper (comparison on `D' ⋐ D`): a function `C²` on `D'`, continuous on
`closure D'`, with `𝓛v ≤ 0` in `D'` and `v ≤ 0` on `∂D'` is `≤ 0` on `closure D'`
(`lem_comparison` on `D'`). -/
theorem s05_dp_a_cmp {Ω Ωs D D' : Set ℂ} (hJ : IsJordanPair Ω Ωs) {ε' : ℝ}
    {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ}
    (h : IsAdmissibleOp Ω D ε' aUp bUp c) (hD' : IsSmoothRelCompactIn D' D) {v : ℂ → ℝ}
    (hv2 : ContDiffOn ℝ 2 v D') (hvc : ContinuousOn v (closure D'))
    (hL : ∀ w ∈ D', ellOp Ω aUp bUp c v w ≤ 0) (hb : ∀ w ∈ frontier D', v w ≤ 0) :
    ∀ w ∈ closure D', v w ≤ 0 := by
  obtain ⟨hD'o, hK, hcl, -⟩ := hD'
  have h' := s05_wd_admissible_mono h hD'o (subset_closure.trans hcl)
  have hin := (lem_comparison Ω Ωs hJ D' ε' aUp bUp c h' v hv2 (s05_wd_bdd hK hvc)
    (s05_wd_bdry hvc hb)).1 hL
  intro w hw
  by_cases hwD : w ∈ D'
  · exact hin w hwD
  · exact hb w (by rw [hD'o.frontier_eq]; exact ⟨hw, hwD⟩)

/-- W-PDE2 A helper: for `F ≥ 0` on `D`, a Dirichlet solution on `D' ⋐ D` is `≥ 0` on
`closure D'` (comparison of `-u` with `0`). -/
theorem s05_dp_a_nonneg {Ω Ωs D D' : Set ℂ} (hJ : IsJordanPair Ω Ωs) {ε' : ℝ}
    {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ}
    (h : IsAdmissibleOp Ω D ε' aUp bUp c) {F u : ℂ → ℝ} (hF : ∀ w ∈ D, 0 ≤ F w)
    (hD' : IsSmoothRelCompactIn D' D) (hu : IsDirichletSol Ω aUp bUp c D' F u) :
    ∀ w ∈ closure D', 0 ≤ u w := by
  obtain ⟨hua, hu2, huc⟩ := s05_dp_a_sol_reg hD'.1 hu
  have hsub : D' ⊆ D := subset_closure.trans hD'.2.2.1
  have hL : ∀ x ∈ D', ellOp Ω aUp bUp c (fun y => -u y) x ≤ 0 := by
    intro x hx
    rw [s05_dp_a_ellOp_neg aUp bUp c (hua x hx), hu.2.1 x hx]
    linarith [hF x (hsub hx)]
  have hle := s05_dp_a_cmp hJ h hD' hu2.neg huc.neg hL fun x hx => by
    show -u x ≤ 0
    rw [hu.2.2 x hx, neg_zero]
  intro w hw
  have := hle w hw
  beta_reduce at this
  linarith

/-- W-PDE2 A1: a Dirichlet solution with `0 ≤ F ≤ M` satisfies `0 ≤ u ≤ M/(2 - ε')` on the
closure (comparison with `0` and with the constant `M/(2 - ε')`, `c ≥ 2 - ε'`). -/
theorem s05_dp_bounds : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (D : Set ℂ) (ε' : ℝ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsAdmissibleOp Ω D ε' aUp bUp c → ∀ (F : ℂ → ℝ) (M : ℝ), (∀ w ∈ D, 0 ≤ F w ∧ F w ≤ M) →
      ∀ D' : Set ℂ, IsSmoothRelCompactIn D' D → ∀ u : ℂ → ℝ,
        IsDirichletSol Ω aUp bUp c D' F u → ∀ w ∈ closure D', 0 ≤ u w ∧ u w ≤ M / (2 - ε') := by
  intro Ω Ωs hJ D ε' aUp bUp c h F M hFM D' hD' u hu
  have hsub : D' ⊆ D := subset_closure.trans hD'.2.2.1
  have hnn := s05_dp_a_nonneg hJ h (fun w hw => (hFM w hw).1) hD' hu
  obtain ⟨hua, hu2, huc⟩ := s05_dp_a_sol_reg hD'.1 hu
  have hε : 0 < 2 - ε' := by linarith [h.1, h.2.1]
  intro w hw
  refine ⟨hnn w hw, ?_⟩
  -- `M ≥ 0`: `w ∈ closure D' ⊆ D`, where `0 ≤ F ≤ M`
  have hM : 0 ≤ M := (hFM w (hD'.2.2.1 hw)).1.trans (hFM w (hD'.2.2.1 hw)).2
  set K := M / (2 - ε') with hK
  have hK0 : 0 ≤ K := div_nonneg hM hε.le
  have hKc : K * (2 - ε') = M := by rw [hK, div_mul_cancel₀ M hε.ne']
  -- `𝓛(u - K) = F - K c ≤ M - K (2 - ε') = 0`
  have hL : ∀ x ∈ D', ellOp Ω aUp bUp c (fun y => u y - K) x ≤ 0 := by
    intro x hx
    rw [s05_dp_a_ellOp_sub_const aUp bUp c (hua x hx), hu.2.1 x hx]
    have hc := abs_le.1 (s05_admissible_c_bound h x (hsub hx))
    have : K * (2 - ε') ≤ K * c x := mul_le_mul_of_nonneg_left (by linarith [hc.1]) hK0
    linarith [(hFM x (hsub hx)).2]
  have hle := s05_dp_a_cmp hJ h hD' (hu2.sub contDiffOn_const) (huc.sub continuousOn_const) hL
    fun x hx => by
      show u x - K ≤ 0
      rw [hu.2.2 x hx]
      linarith
  have := hle w hw
  beta_reduce at this
  linarith

/-- W-PDE2 A2: for `F ≥ 0`, Dirichlet solutions increase with the domain. -/
theorem s05_dp_mono : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (D : Set ℂ) (ε' : ℝ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsAdmissibleOp Ω D ε' aUp bUp c → ∀ F : ℂ → ℝ, (∀ w ∈ D, 0 ≤ F w) →
      ∀ D' D'' : Set ℂ, IsSmoothRelCompactIn D' D → IsSmoothRelCompactIn D'' D →
        closure D' ⊆ D'' → ∀ u' u'' : ℂ → ℝ, IsDirichletSol Ω aUp bUp c D' F u' →
          IsDirichletSol Ω aUp bUp c D'' F u'' → ∀ w ∈ D', u' w ≤ u'' w := by
  intro Ω Ωs hJ D ε' aUp bUp c h F hF D' D'' hD' hD'' hcl u' u'' hu' hu''
  obtain ⟨hua', hu2', huc'⟩ := s05_dp_a_sol_reg hD'.1 hu'
  obtain ⟨hua'', -, -⟩ := s05_dp_a_sol_reg hD''.1 hu''
  have hnn := s05_dp_a_nonneg hJ h hF hD'' hu''
  have hcl'' : closure D' ⊆ closure D'' := hcl.trans subset_closure
  have hc'' : ContDiffOn ℝ 2 u'' D' := (hu''.1.mono (subset_closure.trans hcl'')).of_le (by simp)
  -- `𝓛(u' - u'') = F - F = 0` in `D'`, and `u' - u'' = -u'' ≤ 0` on `∂D'`
  have hL : ∀ x ∈ D', ellOp Ω aUp bUp c (fun y => u' y - 1 * u'' y) x ≤ 0 := by
    intro x hx
    rw [s05_ellOp_sub aUp bUp c (hua' x hx) (hua'' x (hcl (subset_closure hx))) 1,
      hu'.2.1 x hx, hu''.2.1 x (hcl (subset_closure hx))]
    linarith
  have hle := s05_dp_a_cmp hJ h hD' (hu2'.sub (contDiffOn_const.mul hc''))
    (huc'.sub (continuousOn_const.mul (hu''.1.continuousOn.mono hcl''))) hL fun x hx => by
      show u' x - 1 * u'' x ≤ 0
      rw [hu'.2.2 x hx]
      linarith [hnn x (hcl'' (frontier_subset_closure hx))]
  intro w hw
  have := hle w (subset_closure hw)
  beta_reduce at this
  linarith

/-- W-PDE2 A3: every member of a smooth exhaustion is absorbed by some member of any other. -/
theorem s05_dp_absorb {D : Set ℂ} {Dn Dm : ℕ → Set ℂ} (hn : IsSmoothExhaustion D Dn)
    (hm : IsSmoothExhaustion D Dm) (n : ℕ) : ∃ m, closure (Dn n) ⊆ Dm m := by
  have hmono : Monotone Dm := monotone_nat_of_le_succ fun m => subset_closure.trans (hm.2.1 m)
  have hcov : closure (Dn n) ⊆ ⋃ m, Dm m := by
    rw [hm.2.2]
    exact (hn.1 n).2.2.1
  exact (hn.1 n).2.1.elim_directed_cover Dm (fun m => (hm.1 m).1) hcov hmono.directed_le

/-- W-PDE2 A4: along a smooth exhaustion, the Dirichlet solutions extended by `0` increase to
their supremum, which lies in `[0, M/(2 - ε')]`. -/
theorem s05_dp_tendsto : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (D : Set ℂ) (ε' : ℝ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsAdmissibleOp Ω D ε' aUp bUp c → ∀ (F : ℂ → ℝ) (M : ℝ), (∀ w ∈ D, 0 ≤ F w ∧ F w ≤ M) →
      ∀ Dn : ℕ → Set ℂ, IsSmoothExhaustion D Dn → ∀ un : ℕ → ℂ → ℝ,
        (∀ n, IsDirichletSol Ω aUp bUp c (Dn n) F (un n)) → ∀ w ∈ D,
          Monotone (fun n => (Dn n).indicator (un n) w) ∧
          Tendsto (fun n => (Dn n).indicator (un n) w) atTop
            (𝓝 (⨆ n, (Dn n).indicator (un n) w)) ∧
          0 ≤ ⨆ n, (Dn n).indicator (un n) w ∧ ⨆ n, (Dn n).indicator (un n) w ≤ M / (2 - ε') := by
  intro Ω Ωs hJ D ε' aUp bUp c h F M hFM Dn hDn un hun w hw
  have hε : 0 < 2 - ε' := by linarith [h.1, h.2.1]
  have hK0 : 0 ≤ M / (2 - ε') := div_nonneg ((hFM w hw).1.trans (hFM w hw).2) hε.le
  have hF0 : ∀ x ∈ D, 0 ≤ F x := fun x hx => (hFM x hx).1
  have hnn : ∀ n, 0 ≤ (Dn n).indicator (un n) w := by
    intro n
    by_cases hx : w ∈ Dn n
    · rw [indicator_of_mem hx]
      exact s05_dp_a_nonneg hJ h hF0 (hDn.1 n) (hun n) w (subset_closure hx)
    · rw [indicator_of_notMem hx]
  have hle : ∀ n, (Dn n).indicator (un n) w ≤ M / (2 - ε') := by
    intro n
    by_cases hx : w ∈ Dn n
    · rw [indicator_of_mem hx]
      exact (s05_dp_bounds Ω Ωs hJ D ε' aUp bUp c h F M hFM (Dn n) (hDn.1 n) (un n) (hun n) w
        (subset_closure hx)).2
    · rw [indicator_of_notMem hx]
      exact hK0
  have hmono : Monotone fun n => (Dn n).indicator (un n) w := by
    refine monotone_nat_of_le_succ fun n => ?_
    show (Dn n).indicator (un n) w ≤ (Dn (n + 1)).indicator (un (n + 1)) w
    by_cases hx : w ∈ Dn n
    · rw [indicator_of_mem hx, indicator_of_mem (hDn.2.1 n (subset_closure hx))]
      exact s05_dp_mono Ω Ωs hJ D ε' aUp bUp c h F hF0 (Dn n) (Dn (n + 1)) (hDn.1 n)
        (hDn.1 (n + 1)) (hDn.2.1 n) (un n) (un (n + 1)) (hun n) (hun (n + 1)) w hx
    · rw [indicator_of_notMem hx]
      exact hnn (n + 1)
  have hbdd : BddAbove (range fun n => (Dn n).indicator (un n) w) :=
    ⟨_, forall_mem_range.2 hle⟩
  exact ⟨hmono, tendsto_atTop_ciSup hmono hbdd, (hnn 0).trans (le_ciSup hbdd 0), ciSup_le hle⟩

/-- W-PDE2 A5: the limit does not depend on the exhaustion or on the family of solutions. -/
theorem s05_dp_indep : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (D : Set ℂ) (ε' : ℝ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsAdmissibleOp Ω D ε' aUp bUp c → ∀ (F : ℂ → ℝ) (M : ℝ), (∀ w ∈ D, 0 ≤ F w ∧ F w ≤ M) →
      ∀ Dn Dm : ℕ → Set ℂ, IsSmoothExhaustion D Dn → IsSmoothExhaustion D Dm →
        ∀ un um : ℕ → ℂ → ℝ, (∀ n, IsDirichletSol Ω aUp bUp c (Dn n) F (un n)) →
          (∀ m, IsDirichletSol Ω aUp bUp c (Dm m) F (um m)) → ∀ w ∈ D,
            ⨆ n, (Dn n).indicator (un n) w = ⨆ m, (Dm m).indicator (um m) w := by
  intro Ω Ωs hJ D ε' aUp bUp c h F M hFM Dn Dm hDn hDm un um hun hum w hw
  have hF0 : ∀ x ∈ D, 0 ≤ F x := fun x hx => (hFM x hx).1
  -- each term along one exhaustion is dominated by a term along the other (`s05_dp_absorb`)
  have key : ∀ (An Bm : ℕ → Set ℂ), IsSmoothExhaustion D An → IsSmoothExhaustion D Bm →
      ∀ (vn vm : ℕ → ℂ → ℝ), (∀ n, IsDirichletSol Ω aUp bUp c (An n) F (vn n)) →
        (∀ m, IsDirichletSol Ω aUp bUp c (Bm m) F (vm m)) →
          ⨆ n, (An n).indicator (vn n) w ≤ ⨆ m, (Bm m).indicator (vm m) w := by
    intro An Bm hA hB vn vm hvn hvm
    have hT := s05_dp_tendsto Ω Ωs hJ D ε' aUp bUp c h F M hFM Bm hB vm hvm w hw
    have hbdd : BddAbove (range fun m => (Bm m).indicator (vm m) w) :=
      ⟨_, forall_mem_range.2 fun m => hT.1.ge_of_tendsto hT.2.1 m⟩
    refine ciSup_le fun n => ?_
    obtain ⟨m, hm⟩ := s05_dp_absorb hA hB n
    refine le_trans ?_ (le_ciSup hbdd m)
    show (An n).indicator (vn n) w ≤ (Bm m).indicator (vm m) w
    by_cases hx : w ∈ An n
    · rw [indicator_of_mem hx, indicator_of_mem (hm (subset_closure hx))]
      exact s05_dp_mono Ω Ωs hJ D ε' aUp bUp c h F hF0 (An n) (Bm m) (hA.1 n) (hB.1 m) hm
        (vn n) (vm m) (hvn n) (hvm m) w hx
    · rw [indicator_of_notMem hx]
      by_cases hy : w ∈ Bm m
      · rw [indicator_of_mem hy]
        exact s05_dp_a_nonneg hJ h hF0 (hB.1 m) (hvm m) w (subset_closure hy)
      · rw [indicator_of_notMem hy]
  exact le_antisymm (key Dn Dm hDn hDm un um hun hum) (key Dm Dn hDm hDn um un hum hun)

/-- W-PDE2 B2 helper (classical ⇒ weak against test functions): with smooth coefficients on `Ω₁`, a
function `G ∈ H¹(Ω₁)` with smooth value `g` and gradient `∇g`, where `g` solves
`-∂ᵢ(Aⁱʲ∂ⱼg) + βʲ∂ⱼg + γ g = f` on `Ω₁`, satisfies `a(G, φ) = ∫ f φ` for every `φ ∈ 𝓓(Ω₁)`. -/
theorem s05_dp_b2_test {Ω₁ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))} {A : (EuclideanSpace ℝ (Fin 2)) → Matrix (Fin 2) (Fin 2) ℝ}
    {β : (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2))} {γ f g : (EuclideanSpace ℝ (Fin 2)) → ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) Ω₁) (hg : ContDiffOn ℝ ∞ g Ω₁)
    (hf : ContinuousOn f Ω₁)
    (heq : ∀ x ∈ (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))),
      -(∑ i : Fin 2, fderiv ℝ (fun y => ∑ j : Fin 2, A y i j * fderiv ℝ g y
          (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) +
        ∑ j : Fin 2, β x j * fderiv ℝ g x (EuclideanSpace.single j 1) + γ x * g x = f x)
    (G : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)
    (hvG : TauCeti.W1p.value G =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₁] g)
    (hgG : TauCeti.W1p.gradient G =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₁] gradient g)
    (φ : TestFunction Ω₁ ℝ ⊤) :
    TauCeti.PDE.energyFormH1 A β γ G (TauCeti.W1p.ofTestFunctionₗ volume Ω₁ 2 φ) =
      ∫ x in (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))), f x * (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x := by
  have hΩ : IsOpen (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))) := Ω₁.isOpen
  have hms : MeasurableSet (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))) := hΩ.measurableSet
  have hg1 : ContDiffOn ℝ ∞ (fderiv ℝ g) Ω₁ :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).1 hg).2
  have hdg : ∀ j : Fin 2,
      ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y (EuclideanSpace.single j 1)) Ω₁ := fun j =>
    hg1.clm_apply contDiffOn_const
  -- the conormal components `qᵢ = Σⱼ Aⁱʲ ∂ⱼg`, smooth on `Ω₁`
  obtain ⟨q, hq_def⟩ : ∃ q : Fin 2 → (EuclideanSpace ℝ (Fin 2)) → ℝ,
      q = fun i y => ∑ j : Fin 2, A y i j * fderiv ℝ g y (EuclideanSpace.single j 1) := ⟨_, rfl⟩
  have hq : ∀ i, ContDiffOn ℝ ∞ (q i) Ω₁ := fun i => by
    rw [hq_def]
    exact ContDiffOn.sum fun j _ => (hA i j).mul (hdg j)
  have hqd : ∀ i, ∀ x ∈ (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))), DifferentiableAt ℝ (q i) x := fun i x hx =>
    ((hq i).differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hx)
  have hD : ∀ i, ContinuousOn (fun y => fderiv ℝ (q i) y (EuclideanSpace.single i 1)) Ω₁ :=
    fun i => (((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).1 (hq i)).2.clm_apply
      contDiffOn_const).continuousOn
  have hqweak : ∀ i, TauCeti.HasWeakLineDerivOn volume Ω₁ (q i)
      (fun x => fderiv ℝ (q i) x (EuclideanSpace.single i 1)) (EuclideanSpace.single i 1) :=
    fun i => TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt
      ((hq i).continuousOn.locallyIntegrableOn hms) ((hD i).locallyIntegrableOn hms)
      fun x hx => (hqd i x hx).hasFDerivAt.hasLineDerivAt _
  obtain ⟨Ds, hDs_def⟩ : ∃ Ds : (EuclideanSpace ℝ (Fin 2)) → ℝ,
      Ds = fun y => ∑ i : Fin 2, fderiv ℝ (q i) y (EuclideanSpace.single i 1) := ⟨_, rfl⟩
  have hDs : ContinuousOn Ds Ω₁ := by
    rw [hDs_def]
    exact continuousOn_finsetSum _ fun i _ => hD i
  have hφ0 : ∀ x, x ∉ (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))) → (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (φ.tsupport_subset h)
  have hdφ0 : ∀ x, x ∉ (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))) → fderiv ℝ (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x = 0 := fun x hx =>
    fderiv_of_notMem_tsupport ℝ fun h => hx (φ.tsupport_subset h)
  have hφd : ∀ x v, lineDeriv ℝ (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x v = fderiv ℝ (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x v := fun x _ =>
    (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv
  have hc : ∀ (h : (EuclideanSpace ℝ (Fin 2)) → ℝ) (x : (EuclideanSpace ℝ (Fin 2))) (i : Fin 2),
      gradient h x i = fderiv ℝ h x (EuclideanSpace.single i 1) := fun h x i => by
    rw [← inner_gradient_left, EuclideanSpace.inner_single_right]
    simp
  -- the energy density, rewritten with the equation on `Ω₁`
  have hpt : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₁,
      TauCeti.PDE.energyIntegrand (A x) (β x) (γ x) (TauCeti.PDE.jetField G x)
        (TauCeti.PDE.jetField (TauCeti.W1p.ofTestFunctionₗ volume Ω₁ 2 φ) x) =
      ∑ i : Fin 2, fderiv ℝ (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x (EuclideanSpace.single i 1) * q i x +
        (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x * (f x + Ds x) := by
    filter_upwards [TauCeti.W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := 2) φ,
      TauCeti.gradientTestFunctionLp_apply_ae (mu := volume) 2 φ, hvG, hgG,
      ae_restrict_mem hms] with x hv hgr hvg hgg hx
    rw [TauCeti.PDE.energyIntegrand_apply, TauCeti.PDE.jetField_apply,
      TauCeti.PDE.jetField_apply, TauCeti.W1p.gradient_ofTestFunctionₗ, hgr, hv, hvg, hgg,
      TauCeti.PDE.driftForm_apply, TauCeti.PDE.massForm_apply,
      TauCeti.PDE.matrixBilinearForm_apply]
    have h := heq x hx
    simp only [dotProduct, mulVec, Fin.sum_univ_two, hc, PiLp.inner_apply, RCLike.inner_apply,
      conj_trivial, hDs_def, hq_def] at h ⊢
    linear_combination (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x * h
  rw [TauCeti.PDE.energyFormH1_def, MeasureTheory.integral_congr_ae hpt,
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hdφ0 x hx, hφ0 x hx]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hφ0 x hx])]
  -- integrate the conormal components by parts
  have hint : ∀ i : Fin 2, Integrable
      (fun x => fderiv ℝ (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x (EuclideanSpace.single i 1) * q i x) := fun i => by
    simpa only [smul_eq_mul, hφd] using TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn
      (hqweak i).locallyIntegrableOn φ (EuclideanSpace.single i 1)
  have hint' : ∀ i : Fin 2, Integrable
      (fun x => (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x * fderiv ℝ (q i) x (EuclideanSpace.single i 1)) := fun i => by
    simpa only [smul_eq_mul] using
      TauCeti.integrable_smul_of_locallyIntegrableOn ((hD i).locallyIntegrableOn hms) φ
  have hibp : ∀ i : Fin 2,
      ∫ x, fderiv ℝ (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x (EuclideanSpace.single i 1) * q i x =
        -∫ x, (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x * fderiv ℝ (q i) x (EuclideanSpace.single i 1) := fun i => by
    simpa only [smul_eq_mul, hφd] using
      (hqweak i).integral_lineDeriv_smul_eq_neg_integral_smul φ
  have hiD := TauCeti.integrable_smul_of_locallyIntegrableOn
    (hDs.locallyIntegrableOn (μ := volume) hms) φ
  have hif := TauCeti.integrable_smul_of_locallyIntegrableOn
    (hf.locallyIntegrableOn (μ := volume) hms) φ
  simp only [smul_eq_mul] at hiD hif
  have hsum : ∀ x, ∑ i : Fin 2, (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x * fderiv ℝ (q i) x (EuclideanSpace.single i 1) =
      (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x * Ds x := fun x => by
    rw [hDs_def, Finset.mul_sum]
  have hS : ∫ x, ∑ i : Fin 2, fderiv ℝ (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x (EuclideanSpace.single i 1) * q i x =
      -∫ x, (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x * Ds x := by
    rw [MeasureTheory.integral_finsetSum _ fun i _ => hint i]
    simp only [hibp, Finset.sum_neg_distrib]
    rw [← MeasureTheory.integral_finsetSum _ fun i _ => hint' i]
    simp only [hsum]
  have hM : ∫ x, (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x * (f x + Ds x) =
      (∫ x, (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x * f x) + ∫ x, (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x * Ds x := by
    simp only [mul_add]
    exact MeasureTheory.integral_add hif hiD
  have hiFD : Integrable (fun x => (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x * (f x + Ds x)) := by
    simp only [mul_add]
    exact hif.add hiD
  rw [MeasureTheory.integral_add (integrable_finsetSum _ fun i _ => hint i) hiFD, hS, hM]
  have hfc : ∫ x, f x * (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x = ∫ x, (φ : (EuclideanSpace ℝ (Fin 2)) → ℝ) x * f x :=
    MeasureTheory.integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  rw [hfc]
  ring

/-- W-PDE2 B2 helper (the source term as an energy form): if `O ∈ H¹(Ω₁)` has value `1`, then
`a_{0,0,f}(O, w) = ∫ f w`. -/
theorem s05_dp_b2_one {Ω₁ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))} {f : (EuclideanSpace ℝ (Fin 2)) → ℝ}
    (O : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)
    (hvO : TauCeti.W1p.value O =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₁] fun _ => (1 : ℝ))
    (w : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2) :
    TauCeti.PDE.energyFormH1 (fun _ => (0 : Matrix (Fin 2) (Fin 2) ℝ)) (fun _ => (0 : (EuclideanSpace ℝ (Fin 2)))) f O w =
      ∫ x in (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))), f x * TauCeti.W1p.value w x := by
  rw [TauCeti.PDE.energyFormH1_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hvO] with x hx
  rw [TauCeti.PDE.energyIntegrand_apply, TauCeti.PDE.jetField_apply,
    TauCeti.PDE.jetField_apply, TauCeti.PDE.driftForm_apply, TauCeti.PDE.massForm_apply,
    TauCeti.PDE.matrixBilinearForm_apply, hx]
  simp

/-- W-PDE2 B2 (classical ⇒ weak): a function `g` smooth on an open `V ⊇ closure Ω₁` (compact)
solving `-∂ᵢ(Aⁱʲ∂ⱼg) + βʲ∂ⱼg + γ g = f` pointwise on `Ω₁` (the form of `pde_classical` /
`s05_pde_bridge`) is an `H¹(Ω₁)` function with classical value and gradient, solving the weak
equation `a(G, v) = ∫ f v` for every `v ∈ H¹₀(Ω₁)` (full energy form, drift and mass included). -/
theorem s05_dp_b2_weak {Ω₁ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))}
    (hΩ₁ : IsCompact (closure (Ω₁ : Set (EuclideanSpace ℝ (Fin 2)))))
    {V : Set (EuclideanSpace ℝ (Fin 2))} (hV : IsOpen V)
    (hΩV : closure (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ V)
    {A : EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ}
    {β : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {γ f g : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) V) (hβ : ContDiffOn ℝ ∞ β V)
    (hγ : ContDiffOn ℝ ∞ γ V) (hg : ContDiffOn ℝ ∞ g V)
    (hf : ContinuousOn f (closure (Ω₁ : Set (EuclideanSpace ℝ (Fin 2)))))
    (heq : ∀ x ∈ (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))),
      -(∑ i : Fin 2, fderiv ℝ (fun y => ∑ j : Fin 2, A y i j * fderiv ℝ g y
          (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) +
        ∑ j : Fin 2, β x j * fderiv ℝ g x (EuclideanSpace.single j 1) + γ x * g x = f x) :
    ∃ G : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2,
      TauCeti.W1p.value G =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₁] g ∧
      TauCeti.W1p.gradient G =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₁]
        gradient g ∧
      ∀ v : TauCeti.W1p0 (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2,
        TauCeti.PDE.energyFormH1 A β γ G
            (v : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2) =
          ∫ x in (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))), f x *
            TauCeti.W1p.value (v : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2) x := by
  have hsub : (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ V := subset_closure.trans hΩV
  -- `G` and the constant `O = 1` in `H¹(Ω₁)`
  -- (`obtain` on these existentials times out at `whnf`; `Exists.elim` does not)
  refine (TauCeti.W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
    (Omega := Ω₁) (p := 2) hV (hg.of_le (by simp)) hΩ₁ subset_closure hΩV).elim
    fun G hG => ?_
  have hvG := hG.1
  have hgG := hG.2
  refine (TauCeti.W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
    (Omega := Ω₁) (p := 2) (u := fun _ => (1 : ℝ)) hV contDiffOn_const hΩ₁ subset_closure
    hΩV).elim fun O hO => ?_
  have hvO := hO.1
  refine ⟨G, hvG, hgG, ?_⟩
  -- both sides are continuous in `v`: bounded coefficients on the compact `closure Ω₁`
  have hAc : ContinuousOn A (closure (Ω₁ : Set (EuclideanSpace ℝ (Fin 2)))) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hA i j).continuousOn.mono hΩV
  have hc1 := TauCeti.PDE.memLp_energyIntegrand_of_continuousOn (mu := volume) hΩ₁ hAc
    (hβ.continuousOn.mono hΩV) (hγ.continuousOn.mono hΩV)
  have hc2 := TauCeti.PDE.memLp_energyIntegrand_of_continuousOn (mu := volume)
    (a := fun _ => (0 : Matrix (Fin 2) (Fin 2) ℝ)) (b := fun _ => (0 : (EuclideanSpace ℝ (Fin 2)))) hΩ₁
    continuousOn_const continuousOn_const hf
  have hcl : IsClosed {w : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2 |
      TauCeti.PDE.energyFormH1 A β γ G w =
        TauCeti.PDE.energyFormH1 (fun _ => (0 : Matrix (Fin 2) (Fin 2) ℝ)) (fun _ => (0 : (EuclideanSpace ℝ (Fin 2))))
          f O w} :=
    isClosed_eq ((TauCeti.PDE.energyFormH1L hc1 G).continuous.congr fun w =>
        TauCeti.PDE.energyFormH1L_apply hc1 G w)
      ((TauCeti.PDE.energyFormH1L hc2 O).continuous.congr fun w =>
        TauCeti.PDE.energyFormH1L_apply hc2 O w)
  -- the identity holds on test functions, hence on their closure `H¹₀(Ω₁)`
  have hS := TauCeti.w1p0Submodule_subset_of_isClosed hcl fun φ => by
    show TauCeti.PDE.energyFormH1 A β γ G (TauCeti.W1p.ofTestFunctionₗ volume Ω₁ 2 φ) =
      TauCeti.PDE.energyFormH1 (fun _ => (0 : Matrix (Fin 2) (Fin 2) ℝ)) (fun _ => (0 : (EuclideanSpace ℝ (Fin 2))))
        f O (TauCeti.W1p.ofTestFunctionₗ volume Ω₁ 2 φ)
    rw [s05_dp_b2_test (fun i j => (hA i j).mono hsub) (hg.mono hsub) (hf.mono subset_closure)
      heq G hvG hgG φ, s05_dp_b2_one O hvO]
    exact MeasureTheory.integral_congr_ae ((TauCeti.W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := 2)
      φ).mono fun x hx => by simp only [hx])
  intro v
  rw [← s05_dp_b2_one O hvO]
  exact hS v.2

/-- W-PDE2 B2' (full ⇒ split): with coefficients continuous on the compact `closure Ω₁`, the full
weak equation `a(U, v) = ∫ f v` is the split weak equation of `pde_Hk_loc` / `pde_classical`,
`a₀(U, v) = ∫ (f - ⟪β, ∇U⟫ - γ U) v` with `a₀` the principal part. -/
theorem s05_dp_b2_split {Ω₁ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))}
    (hΩ₁ : IsCompact (closure (Ω₁ : Set (EuclideanSpace ℝ (Fin 2)))))
    {A : EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ}
    {β : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {γ f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hA : ContinuousOn A (closure (Ω₁ : Set (EuclideanSpace ℝ (Fin 2)))))
    (hβ : ContinuousOn β (closure (Ω₁ : Set (EuclideanSpace ℝ (Fin 2)))))
    (hγ : ContinuousOn γ (closure (Ω₁ : Set (EuclideanSpace ℝ (Fin 2)))))
    (hf : ContinuousOn f (closure (Ω₁ : Set (EuclideanSpace ℝ (Fin 2)))))
    {U : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2}
    (hU : ∀ v : TauCeti.W1p0 (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2,
      TauCeti.PDE.energyFormH1 A β γ U
          (v : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2) =
        ∫ x in (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))), f x *
          TauCeti.W1p.value (v : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2) x) :
    ∀ v : TauCeti.W1p0 (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2,
      TauCeti.PDE.energyFormH1 A 0 0 U
          (v : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2) =
        ∫ x in (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))), (f x - inner ℝ (β x) (TauCeti.W1p.gradient U x) -
          γ x * TauCeti.W1p.value U x) *
            TauCeti.W1p.value (v : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2) x := by
  intro v
  let : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℝ))
  have hms : MeasurableSet (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))) := Ω₁.isOpen.measurableSet
  have hsub : (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ closure Ω₁ := subset_closure
  have hAe : ∀ i j, ContinuousOn (fun x => A x i j)
      (closure (Ω₁ : Set (EuclideanSpace ℝ (Fin 2)))) := fun i j =>
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hA)
  obtain ⟨K, hK0⟩ := hΩ₁.exists_bound_of_continuousOn (f := fun x => ∑ i, ∑ j, |A x i j|)
    (continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => (hAe i j).abs)
  have hK : ∀ x ∈ closure (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))),
      ‖TauCeti.PDE.matrixBilinearForm (A x)‖ ≤ K := by
    intro x hx
    have h2 := hK0 x hx
    rw [Real.norm_of_nonneg (by positivity)] at h2
    exact (TauCeti.PDE.norm_matrixBilinearForm_le_sum_abs (A x)).trans h2
  obtain ⟨B, hB⟩ := hΩ₁.exists_bound_of_continuousOn hβ
  obtain ⟨G, hG⟩ := hΩ₁.exists_bound_of_continuousOn hγ
  obtain ⟨Mf, hMf⟩ := hΩ₁.exists_bound_of_continuousOn hf
  have hβm := (hβ.mono hsub).aestronglyMeasurable (μ := volume) hms
  have hγm := (hγ.mono hsub).aestronglyMeasurable (μ := volume) hms
  have hβb : ∀ x ∈ (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))), ‖β x‖ ≤ B := fun x hx => hB x (hsub hx)
  have hγb : ∀ x ∈ (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))), |γ x| ≤ G := fun x hx => by
    simpa [Real.norm_eq_abs] using hG x (hsub hx)
  have e := hU v
  rw [pde_energy_split (TauCeti.PDE.continuous_matrixBilinearForm.comp_aestronglyMeasurable
      ((hA.mono hsub).aestronglyMeasurable hms)) hβm hγm
    (fun x hx => hK x (hsub hx)) hβb hγb] at e
  have : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₁) :=
    isFiniteMeasure_restrict.2
      (lt_of_le_of_lt (measure_mono subset_closure) hΩ₁.measure_lt_top).ne
  -- `f v` is integrable: `f` is bounded and `v ∈ L² ⊆ L¹` on a set of finite measure
  have hfv : Integrable (fun x => f x *
      TauCeti.W1p.value (v : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2) x)
      ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₁) :=
    ((Lp.memLp _).integrable one_le_two).bdd_mul ((hf.mono hsub).aestronglyMeasurable hms)
      (c := Mf) ((ae_restrict_mem hms).mono fun x hx => hMf x (hsub hx))
  -- the drift and mass terms are integrable since `β`, `γ` are bounded on `Ω₁`
  have hL := TauCeti.PDE.integrable_energyIntegrand_jetField
    (TauCeti.PDE.memLp_energyIntegrand_of_bounds (a := fun _ => 0) (Lam := 0) le_rfl
      aestronglyMeasurable_const hβm hγm (fun _ _ _ _ => by simp) hβb
      (fun x hx => by simpa [Real.norm_eq_abs] using hγb x hx))
    U (v : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)
  have hdv : Integrable (fun x => (inner ℝ (β x) (TauCeti.W1p.gradient U x) +
      γ x * TauCeti.W1p.value U x) *
        TauCeti.W1p.value (v : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2) x)
      ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₁) := by
    refine hL.congr (ae_of_all _ fun x => ?_)
    simp [TauCeti.PDE.energyIntegrand_apply, TauCeti.PDE.matrixBilinearForm_apply]
    ring
  rw [eq_sub_of_add_eq e, ← MeasureTheory.integral_sub hfv hdv]
  refine MeasureTheory.integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  ring

/-- W-PDE2 B3 helper (pointwise Young absorption): if `q ≥ λ G²`, `|m| ≤ Λ M G`, `|b| ≤ B G`,
`c ≥ 0`, `0 ≤ p ≤ 1`, `K₁ λ = 4 Λ² M²` and `K₂ λ = B²`, then the energy density of `p² u` (gradient
`p² g + 2 p u ∇ψ`) dominates `λ/2 · p² G² - (K₁ + K₂) u²`. -/
theorem s05_dp_b3_young {lam Lam M B K₁ K₂ p u G q m b c : ℝ} (hl : 0 < lam) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hq : lam * G ^ 2 ≤ q) (hm : |m| ≤ Lam * M * G) (hb : |b| ≤ B * G)
    (hc : 0 ≤ c) (hK₁ : K₁ * lam = 4 * Lam ^ 2 * M ^ 2) (hK₂ : K₂ * lam = B ^ 2) :
    lam / 2 * (p ^ 2 * G ^ 2) ≤
      p * (p * q + u * m) + p * u * m + b * (p * (p * u)) + c * u * (p * (p * u)) +
        (K₁ + K₂) * u ^ 2 := by
  have hu2 : |u| ^ 2 = u ^ 2 := sq_abs u
  have hpu : 0 ≤ p * |u| := mul_nonneg hp0 (abs_nonneg u)
  -- `2 p |u| Λ M G ≤ λ/4 p² G² + K₁ u²`
  have h1 : 0 ≤ lam / 4 * (p ^ 2 * G ^ 2) + K₁ * u ^ 2 - 2 * (p * |u|) * (Lam * M * G) := by
    have e : lam * (lam / 4 * (p ^ 2 * G ^ 2) + K₁ * u ^ 2 - 2 * (p * |u|) * (Lam * M * G)) =
        (lam / 2 * p * G - 2 * Lam * M * |u|) ^ 2 := by
      linear_combination u ^ 2 * hK₁ - 4 * Lam ^ 2 * M ^ 2 * hu2
    exact (mul_nonneg_iff_of_pos_left hl).1 (by rw [e]; exact sq_nonneg _)
  -- `p |u| B G ≤ λ/4 p² G² + K₂ u²`
  have h2 : 0 ≤ lam / 4 * (p ^ 2 * G ^ 2) + K₂ * u ^ 2 - (p * |u|) * (B * G) := by
    have e : lam * (lam / 4 * (p ^ 2 * G ^ 2) + K₂ * u ^ 2 - (p * |u|) * (B * G)) =
        (lam / 2 * p * G - B * |u|) ^ 2 := by
      linear_combination u ^ 2 * hK₂ - B ^ 2 * hu2
    exact (mul_nonneg_iff_of_pos_left hl).1 (by rw [e]; exact sq_nonneg _)
  have hq' : lam * (p ^ 2 * G ^ 2) ≤ p ^ 2 * q :=
    calc lam * (p ^ 2 * G ^ 2) = p ^ 2 * (lam * G ^ 2) := by ring
      _ ≤ p ^ 2 * q := mul_le_mul_of_nonneg_left hq (sq_nonneg p)
  have hm' : -(2 * (p * |u|) * (Lam * M * G)) ≤ 2 * p * u * m := by
    have h : |2 * p * u * m| ≤ 2 * (p * |u|) * (Lam * M * G) := by
      rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_nonneg hp0]
      have := mul_le_mul_of_nonneg_left hm (mul_nonneg zero_le_two hpu)
      linarith
    exact (neg_le_neg h).trans (neg_abs_le _)
  have hb' : -((p * |u|) * (B * G)) ≤ b * (p * (p * u)) := by
    have hBG : 0 ≤ B * G := (abs_nonneg b).trans hb
    have hpp : p * (p * |u|) ≤ p * |u| :=
      calc p * (p * |u|) ≤ 1 * (p * |u|) := mul_le_mul_of_nonneg_right hp1 hpu
        _ = p * |u| := one_mul _
    have h : |b * (p * (p * u))| ≤ (p * |u|) * (B * G) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hp0]
      calc |b| * (p * (p * |u|)) ≤ (B * G) * (p * (p * |u|)) :=
            mul_le_mul_of_nonneg_right hb (mul_nonneg hp0 hpu)
        _ ≤ (B * G) * (p * |u|) := mul_le_mul_of_nonneg_left hpp hBG
        _ = (p * |u|) * (B * G) := by ring
    exact (neg_le_neg h).trans (neg_abs_le _)
  have hc' : 0 ≤ c * u * (p * (p * u)) := by
    have e : c * u * (p * (p * u)) = c * (p * u) ^ 2 := by ring
    rw [e]
    exact mul_nonneg hc (sq_nonneg _)
  have hs : p * (p * q + u * m) + p * u * m = p ^ 2 * q + 2 * p * u * m := by ring
  linarith [h1, h2, hq', hm', hb', hc']

/-- W-PDE2 B3 helper: with coefficients continuous on the compact `closure Ω₂`, the energy density
of two `H¹(Ω₂)` functions is integrable on `Ω₂`. -/
theorem s05_dp_b3_int {Ω₂ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))}
    (hΩ₂ : IsCompact (closure (Ω₂ : Set (EuclideanSpace ℝ (Fin 2)))))
    {A : EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ}
    {β : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {γ : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hA : ContinuousOn A (closure (Ω₂ : Set (EuclideanSpace ℝ (Fin 2)))))
    (hβ : ContinuousOn β (closure (Ω₂ : Set (EuclideanSpace ℝ (Fin 2)))))
    (hγ : ContinuousOn γ (closure (Ω₂ : Set (EuclideanSpace ℝ (Fin 2)))))
    (U w : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₂ 2) :
    Integrable (fun x => TauCeti.PDE.energyIntegrand (A x) (β x) (γ x) (TauCeti.PDE.jetField U x)
      (TauCeti.PDE.jetField w x)) ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₂) :=
  TauCeti.PDE.integrable_energyIntegrand_jetField
    (TauCeti.PDE.memLp_energyIntegrand_of_continuousOn hΩ₂ hA hβ hγ) U w

/-- W-PDE2 B3 helper: for a continuous `ψ` with `0 ≤ ψ ≤ 1`, `ψ² ‖∇U‖²` is integrable on `Ω₂`. -/
theorem s05_dp_b3_pg {Ω₂ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))}
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} (hψ : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψ1 : ∀ x, ψ x ≤ 1) (U : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₂ 2) :
    Integrable (fun x => ψ x ^ 2 * ‖TauCeti.W1p.gradient U x‖ ^ 2)
      ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₂) :=
  (TauCeti.W1p.integrable_norm_gradient_sq U).bdd_mul (hψ.pow 2).aestronglyMeasurable
    (c := 1) (Filter.Eventually.of_forall fun x => by
      show ‖ψ x ^ 2‖ ≤ 1
      rw [Real.norm_of_nonneg (pow_nonneg (hψ0 x) 2)]
      exact pow_le_one₀ (hψ0 x) (hψ1 x))

/-- W-PDE2 B3 helper (the Caccioppoli test function): for a smooth cutoff `ψ` compactly supported in
`Ω₂` with `|ψ|, ‖∇ψ‖ ≤ M` on `Ω₂`, `w = ψ (ψ U)` lies in `H¹₀(Ω₂)`, with value `ψ (ψ U)` and
gradient `ψ (ψ ∇U + U ∇ψ) + ψ U ∇ψ`. (Stated existentially so that callers never see the
`contDiffSMul` term, whose definitional unfolding makes elaboration time out.) -/
theorem s05_dp_b3_test {Ω₂ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))}
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} (hψ : ContDiff ℝ ∞ ψ) {M : ℝ} (hM0 : 0 ≤ M)
    (hψM : ∀ x ∈ (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))), |ψ x| ≤ M)
    (hgM : ∀ x ∈ (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))), ‖gradient ψ x‖ ≤ M)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))))
    (U : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₂ 2) :
    ∃ w : TauCeti.W1p0 (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₂ 2,
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₂,
        TauCeti.W1p.value (w : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₂ 2) x =
          ψ x * (ψ x * TauCeti.W1p.value U x)) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₂,
        TauCeti.W1p.gradient
            (w : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₂ 2) x =
          ψ x • (ψ x • TauCeti.W1p.gradient U x + TauCeti.W1p.value U x • gradient ψ x) +
            (ψ x * TauCeti.W1p.value U x) • gradient ψ x := by
  have hv1 := TauCeti.W1p.value_contDiffSMul_ae hψ hM0 hψM hgM U
  have hg1 := TauCeti.W1p.gradient_contDiffSMul_ae hψ hM0 hψM hgM U
  have hv := TauCeti.W1p.value_contDiffSMul_ae hψ hM0 hψM hgM
    (TauCeti.W1p.contDiffSMul ψ hψ hM0 hψM hgM U)
  have hg := TauCeti.W1p.gradient_contDiffSMul_ae hψ hM0 hψM hgM
    (TauCeti.W1p.contDiffSMul ψ hψ hM0 hψM hgM U)
  have hw0 := TauCeti.W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by simp) hψ hM0
    hψM hgM hψc hψs (TauCeti.W1p.contDiffSMul ψ hψ hM0 hψM hgM U)
  refine ⟨⟨TauCeti.W1p.contDiffSMul ψ hψ hM0 hψM hgM
    (TauCeti.W1p.contDiffSMul ψ hψ hM0 hψM hgM U), hw0⟩, ?_, ?_⟩
  · -- reduce `⟨w, _⟩.val` syntactically (a defeq check would unfold `contDiffSMul`)
    dsimp only
    filter_upwards [hv, hv1] with x h h1
    rw [h, h1, smul_eq_mul, smul_eq_mul]
  · dsimp only
    filter_upwards [hg, hg1, hv1] with x h h1 h2
    rw [h, h1, h2, smul_eq_mul]

/-- W-PDE2 B3 helper (pointwise Young absorption on `Ω₂`): if `w` has value `ψ (ψ U)` and gradient
`ψ (ψ ∇U + U ∇ψ) + ψ U ∇ψ`, with `0 ≤ ψ ≤ 1`, `‖∇ψ‖ ≤ M`, `‖β‖ ≤ B` and `γ ≥ 0`, then a.e. on `Ω₂`
the energy density of `(U, w)` plus `(K₁ + K₂) U²` dominates `λ/2 · ψ² ‖∇U‖²`. -/
theorem s05_dp_b3_pt {Ω₂ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))}
    {A : EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ}
    {β : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {γ : EuclideanSpace ℝ (Fin 2) → ℝ} {lam Lam M B K₁ K₂ : ℝ}
    {ψ : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hell : TauCeti.PDE.UniformlyEllipticOn (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))) A lam Lam)
    (hγ0 : ∀ x ∈ (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))), 0 ≤ γ x)
    (hψ0 : ∀ x, 0 ≤ ψ x) (hψ1 : ∀ x, ψ x ≤ 1) (hgM : ∀ x, ‖gradient ψ x‖ ≤ M)
    (hB : ∀ x ∈ (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))), ‖β x‖ ≤ B)
    (hK₁ : K₁ * lam = 4 * Lam ^ 2 * M ^ 2) (hK₂ : K₂ * lam = B ^ 2)
    (U w : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₂ 2)
    (hvae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₂,
      TauCeti.W1p.value w x = ψ x * (ψ x * TauCeti.W1p.value U x))
    (hgae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₂,
      TauCeti.W1p.gradient w x =
        ψ x • (ψ x • TauCeti.W1p.gradient U x + TauCeti.W1p.value U x • gradient ψ x) +
          (ψ x * TauCeti.W1p.value U x) • gradient ψ x) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₂,
      lam / 2 * (ψ x ^ 2 * ‖TauCeti.W1p.gradient U x‖ ^ 2) ≤
        TauCeti.PDE.energyIntegrand (A x) (β x) (γ x) (TauCeti.PDE.jetField U x)
          (TauCeti.PDE.jetField w x) +
          (K₁ + K₂) * TauCeti.W1p.value U x ^ 2 := by
  obtain ⟨hl, hlL, hell'⟩ := hell
  have hL0 : 0 ≤ Lam := hl.le.trans hlL
  have hms : MeasurableSet (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))) := Ω₂.isOpen.measurableSet
  filter_upwards [hvae, hgae, ae_restrict_mem hms] with x hv hg hx
  rw [TauCeti.PDE.energyIntegrand_apply, TauCeti.PDE.jetField_apply,
    TauCeti.PDE.jetField_apply]
  simp only [hv, hg, map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul, TauCeti.PDE.driftForm_apply,
    TauCeti.PDE.massForm_apply]
  have hq := (hell' hx).1 (TauCeti.W1p.gradient U x)
  rw [← TauCeti.PDE.matrixBilinearForm_self] at hq
  have hm : |TauCeti.PDE.matrixBilinearForm (A x) (gradient ψ x) (TauCeti.W1p.gradient U x)| ≤
      Lam * M * ‖TauCeti.W1p.gradient U x‖ := by
    rw [TauCeti.PDE.matrixBilinearForm_apply]
    exact ((hell' hx).2 _ _).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hgM x) hL0) (norm_nonneg _))
  have hb : |inner ℝ (β x) (TauCeti.W1p.gradient U x)| ≤ B * ‖TauCeti.W1p.gradient U x‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hB x hx) (norm_nonneg _))
  refine (s05_dp_b3_young (u := TauCeti.W1p.value U x) hl (hψ0 x) (hψ1 x) hq hm hb
    (hγ0 x hx) hK₁ hK₂).trans (le_of_eq ?_)
  ring

/-- W-PDE2 B3 helper (integrating the absorption): if `λ/2 · f ≤ g + K h` a.e. and `∫ g = 0`,
then `∫ f ≤ 2/λ · K · ∫ h`. -/
theorem s05_dp_b3_X {μ : Measure (EuclideanSpace ℝ (Fin 2))}
    {f g h : EuclideanSpace ℝ (Fin 2) → ℝ} {lam K : ℝ} (hl : 0 < lam)
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ)
    (hpt : ∀ᵐ x ∂μ, lam / 2 * f x ≤ g x + K * h x) (e : ∫ x, g x ∂μ = 0) :
    ∫ x, f x ∂μ ≤ 2 / lam * K * ∫ x, h x ∂μ := by
  have hI : ∫ x, lam / 2 * f x ∂μ ≤ ∫ x, (g x + K * h x) ∂μ :=
    MeasureTheory.integral_mono_ae (hf.const_mul (lam / 2)) (hg.add (hh.const_mul K)) hpt
  rw [MeasureTheory.integral_add hg (hh.const_mul _), e, zero_add, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul] at hI
  calc ∫ x, f x ∂μ = 2 / lam * (lam / 2 * ∫ x, f x ∂μ) := by field_simp
    _ ≤ 2 / lam * (K * ∫ x, h x ∂μ) :=
        mul_le_mul_of_nonneg_left hI (div_nonneg zero_le_two hl.le)
    _ = _ := by ring

/-- W-PDE2 B3 helper (the `H¹(Ω₁)` norm of the restriction): if `ψ = 1` on `Ω₁`, `0 ≤ ψ ≤ 1` and
`∫_{Ω₂} ψ² ‖∇U‖² ≤ C' ∫_{Ω₂} U²`, then `‖U|_{Ω₁}‖² ≤ (1 + C') ∫_{Ω₂} U²`. -/
theorem s05_dp_b3_fin {Ω₁ Ω₂ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))}
    (hle : Ω₁ ≤ Ω₂) {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} (hψ : Continuous ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) (hψ1 : ∀ x, ψ x ≤ 1)
    (hψone : ∀ x ∈ (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))), ψ x = 1)
    (U : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₂ 2) {C' : ℝ}
    (hX : ∫ x in (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))),
        ψ x ^ 2 * ‖TauCeti.W1p.gradient U x‖ ^ 2 ≤
      C' * ∫ x in (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))), TauCeti.W1p.value U x ^ 2) :
    ‖TauCeti.W1p.restrictL hle U‖ ^ 2 ≤
      (1 + C') * ∫ x in (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))), TauCeti.W1p.value U x ^ 2 := by
  have hU2 := TauCeti.W1p.integrable_value_sq U
  have hpg := s05_dp_b3_pg (Ω₂ := Ω₂) hψ hψ0 hψ1 U
  have hr := TauCeti.W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq
    (TauCeti.W1p.restrictL hle U)
  rw [← TauCeti.W1p.integral_value_sq_eq_norm_value_sq,
    ← TauCeti.W1p.integral_norm_gradient_sq_eq_norm_gradient_sq] at hr
  have hv1 : ∫ x in (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))),
        TauCeti.W1p.value (TauCeti.W1p.restrictL hle U) x ^ 2 =
      ∫ x in (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))), TauCeti.W1p.value U x ^ 2 :=
    MeasureTheory.integral_congr_ae ((TauCeti.W1p.value_restrictL_ae hle U).mono fun x hx => by
      dsimp only; rw [hx])
  have hg1 : ∫ x in (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))),
        ‖TauCeti.W1p.gradient (TauCeti.W1p.restrictL hle U) x‖ ^ 2 =
      ∫ x in (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))),
        ψ x ^ 2 * ‖TauCeti.W1p.gradient U x‖ ^ 2 := by
    rw [show ∫ x in (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))),
          ‖TauCeti.W1p.gradient (TauCeti.W1p.restrictL hle U) x‖ ^ 2 =
        ∫ x in (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))), ‖TauCeti.W1p.gradient U x‖ ^ 2 from
      MeasureTheory.integral_congr_ae ((TauCeti.W1p.gradient_restrictL_ae hle U).mono fun x hx => by
        dsimp only; rw [hx])]
    refine setIntegral_congr_fun Ω₁.isOpen.measurableSet fun x hx => ?_
    simp only [hψone x hx, one_pow, one_mul]
  have hΩ12 : (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))) ≤ᵐ[volume] (Ω₂ : Set _) :=
    (show (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Ω₂ from fun x hx => hle hx).eventuallyLE
  have hm1 := setIntegral_mono_set hU2 (ae_of_all _ fun x => sq_nonneg _) hΩ12
  have hm2 := setIntegral_mono_set hpg
    (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hΩ12
  rw [hr, hv1, hg1]
  have hC : (1 + C') *
        ∫ x in (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))), TauCeti.W1p.value U x ^ 2 =
      (∫ x in (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))), TauCeti.W1p.value U x ^ 2) +
        C' * ∫ x in (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))), TauCeti.W1p.value U x ^ 2 := by ring
  rw [hC]
  linarith

/-- W-PDE2 B3 (Caccioppoli): for coefficients continuous on the compact `closure Ω₂`, uniformly
elliptic on `Ω₂` with `γ ≥ 0`, and `closure Ω₁ ⊆ Ω₂`, every weak solution `U ∈ H¹(Ω₂)` of the
homogeneous equation satisfies `‖U|_{Ω₁}‖²_{H¹(Ω₁)} ≤ C ∫_{Ω₂} U²`, with `C` independent of `U`.
Proof: test with `ψ²U`, `ψ` a cutoff equal to `1` on `closure Ω₁`. -/
theorem s05_dp_b3_cacc {Ω₁ Ω₂ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))}
    (hle : Ω₁ ≤ Ω₂) (h12 : closure (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Ω₂)
    (hΩ₂ : IsCompact (closure (Ω₂ : Set (EuclideanSpace ℝ (Fin 2)))))
    {A : EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ}
    {β : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {γ : EuclideanSpace ℝ (Fin 2) → ℝ} {lam Lam : ℝ}
    (hA : ContinuousOn A (closure (Ω₂ : Set (EuclideanSpace ℝ (Fin 2)))))
    (hβ : ContinuousOn β (closure (Ω₂ : Set (EuclideanSpace ℝ (Fin 2)))))
    (hγ : ContinuousOn γ (closure (Ω₂ : Set (EuclideanSpace ℝ (Fin 2)))))
    (hell : TauCeti.PDE.UniformlyEllipticOn (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))) A lam Lam)
    (hγ0 : ∀ x ∈ (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))), 0 ≤ γ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₂ 2,
      (∀ v : TauCeti.W1p0 (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₂ 2,
        TauCeti.PDE.energyFormH1 A β γ U
          (v : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₂ 2) = 0) →
      ‖TauCeti.W1p.restrictL hle U‖ ^ 2 ≤
        C * ∫ x in (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))), TauCeti.W1p.value U x ^ 2 := by
  obtain ⟨hl, hlL, hell'⟩ := hell
  have hL0 : 0 ≤ Lam := hl.le.trans hlL
  have hl0 : lam ≠ 0 := hl.ne'
  have hms : MeasurableSet (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))) := Ω₂.isOpen.measurableSet
  have hsub : (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ closure Ω₂ := subset_closure
  have hK1 : IsCompact (closure (Ω₁ : Set (EuclideanSpace ℝ (Fin 2)))) :=
    hΩ₂.of_isClosed_subset isClosed_closure (h12.trans subset_closure)
  -- a cutoff `ψ`, equal to `1` near `closure Ω₁`, compactly supported in `Ω₂`
  obtain ⟨ψ, M, hψ, hψr, hψ1, hψc, hψs, hM0, hψM, hgM⟩ :=
    hK1.exists_contDiff_cutoff_with_bounds Ω₂.isOpen h12
  have hψ0 : ∀ x, 0 ≤ ψ x := fun x => (hψr (mem_range_self x)).1
  have hψ1' : ∀ x, ψ x ≤ 1 := fun x => (hψr (mem_range_self x)).2
  have hψone : ∀ x ∈ (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))), ψ x = 1 := fun x hx =>
    interior_subset (hψ1 (subset_closure hx))
  obtain ⟨B, hB⟩ := hΩ₂.exists_bound_of_continuousOn hβ
  -- the constants of the Young absorption: `K₁ = 4 Λ² M² / λ`, `K₂ = ‖β‖²_∞ / λ`
  obtain ⟨K₁, hK₁d⟩ : ∃ K : ℝ, K = 4 * Lam ^ 2 * M ^ 2 / lam := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂d⟩ : ∃ K : ℝ, K = B ^ 2 / lam := ⟨_, rfl⟩
  have hK₁ : K₁ * lam = 4 * Lam ^ 2 * M ^ 2 := by rw [hK₁d, div_mul_cancel₀ _ hl0]
  have hK₂ : K₂ * lam = B ^ 2 := by rw [hK₂d, div_mul_cancel₀ _ hl0]
  have hK0 : 0 ≤ K₁ + K₂ := by
    rw [hK₁d, hK₂d]
    exact add_nonneg (div_nonneg (by positivity) hl.le) (div_nonneg (sq_nonneg _) hl.le)
  refine ⟨1 + 2 / lam * (K₁ + K₂),
    add_nonneg zero_le_one (mul_nonneg (div_nonneg zero_le_two hl.le) hK0), ?_⟩
  intro U hU
  -- the test function `w = ψ (ψ U) ∈ H¹₀(Ω₂)`
  -- (`obtain`/`rcases` here time out at `whnf`; `Exists.elim` does not)
  have hT := s05_dp_b3_test hψ hM0 (fun x _ => hψM x) (fun x _ => hgM x) hψc hψs U
  refine hT.elim fun v hv => ?_
  have hvae := hv.1
  have hgae := hv.2
  have e := hU v
  rw [TauCeti.PDE.energyFormH1_def] at e
  have hint := s05_dp_b3_int hΩ₂ hA hβ hγ U v
  have hU2 := TauCeti.W1p.integrable_value_sq U
  have hpg := s05_dp_b3_pg (Ω₂ := Ω₂) hψ.continuous hψ0 hψ1' U
  -- pointwise Young absorption on `Ω₂`
  have hpt := s05_dp_b3_pt (A := A) (β := β) (γ := γ) ⟨hl, hlL, hell'⟩ hγ0 hψ0 hψ1'
    (fun x => hgM x) (fun x hx => hB x (hsub hx)) hK₁ hK₂ U _ hvae hgae
  have hX := s05_dp_b3_X hl hpg hint hU2 hpt e
  -- the `H¹(Ω₁)` norm of the restriction
  exact s05_dp_b3_fin hle hψ.continuous hψ0 hψ1' hψone U hX

/-- W-PDE2 B4 helper: an `H¹` weak solution of the homogeneous equation has a representative
smooth on `Ω₁`. -/
theorem s05_dp_hom_rep {Ω₁ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))} (hc : IsCompact (closure (Ω₁ : Set (EuclideanSpace ℝ (Fin 2)))))
    {A : (EuclideanSpace ℝ (Fin 2)) → Matrix (Fin 2) (Fin 2) ℝ} {β : (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2))} {γ : (EuclideanSpace ℝ (Fin 2)) → ℝ} {lam Lam : ℝ}
    (hell : TauCeti.PDE.UniformlyEllipticOn (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))) A lam Lam)
    (hAc : ContinuousOn A (closure Ω₁)) (hβc : ContinuousOn β (closure Ω₁))
    (hγc : ContinuousOn γ (closure Ω₁)) (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) Ω₁)
    (hβ : ContDiffOn ℝ ∞ β Ω₁) (hγ : ContDiffOn ℝ ∞ γ Ω₁) {U : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)}
    (hU : ∀ v : (TauCeti.W1p0 (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2), TauCeti.PDE.energyFormH1 A β γ U (v : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)) = 0) :
    ∃ g : (EuclideanSpace ℝ (Fin 2)) → ℝ, ContDiffOn ℝ ∞ g Ω₁ ∧
      (TauCeti.W1p.value U : (EuclideanSpace ℝ (Fin 2)) → ℝ) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₁] g := by
  have hs := s05_dp_b2_split (f := fun _ => (0 : ℝ)) hc hAc hβc hγc continuousOn_const
    fun v => by rw [hU v]; simp
  have hk : ∀ (k : ℕ) (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))), IsCompact (closure (V : Set (EuclideanSpace ℝ (Fin 2)))) →
      closure (V : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Ω₁ → ∃ w : TauCeti.Wkp (volume : Measure (EuclideanSpace ℝ (Fin 2))) V 2 (k + 1),
        (TauCeti.Wkp.value (k + 1) w : (EuclideanSpace ℝ (Fin 2)) → ℝ) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict V]
          TauCeti.W1p.value U := fun k V hV hVΩ =>
    pde_Hk_loc hell hA hβ hγ (F := fun _ => (0 : ℝ)) contDiffOn_const hs k hV hVΩ
  refine pde_smooth_rep fun k V hV hVΩ => ?_
  cases k with
  | zero =>
    obtain ⟨w, hw⟩ := hk 0 V hV hVΩ
    refine ⟨TauCeti.Wkp.lowerOrder 0 w, ?_⟩
    rw [← TauCeti.Wkp.value_succ]
    exact hw
  | succ k =>
    exact hk k V hV hVΩ

/-- W-PDE2 B5 helper (closed graph theorem): a linear map from a Banach space to `C(K, ℝ)`,
`K` compact, with sequentially closed graph is bounded, pointwise on `K`. -/
theorem s05_dp_cg_core {W K : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {S : Submodule ℝ W} (hS : IsClosed (S : Set W)) [TopologicalSpace K] [CompactSpace K]
    (f : S → C(K, ℝ))
    (hadd : ∀ U V, f (U + V) = f U + f V) (hsmul : ∀ (a : ℝ) U, f (a • U) = a • f U)
    (hcl : ∀ (u : ℕ → S) (U : S) (g : C(K, ℝ)), Tendsto u atTop (𝓝 U) →
      Tendsto (fun n => f (u n)) atTop (𝓝 g) → f U = g) :
    ∃ C : ℝ, ∀ U x, |f U x| ≤ C * ‖U‖ := by
  have : CompleteSpace S := hS.completeSpace_coe
  let T : S →ₗ[ℝ] C(K, ℝ) := ⟨⟨f, hadd⟩, hsmul⟩
  have hgraph : IsClosed (T.graph : Set (S × C(K, ℝ))) := by
    refine isSeqClosed_iff_isClosed.mp fun {p} {q} hp hpq => ?_
    simp only [SetLike.mem_coe, LinearMap.mem_graph_iff] at hp ⊢
    have h1 : Tendsto (fun n => (p n).1) atTop (𝓝 q.1) := (continuous_fst.tendsto _).comp hpq
    have h2 : Tendsto (fun n => (p n).2) atTop (𝓝 q.2) := (continuous_snd.tendsto _).comp hpq
    exact (hcl _ _ _ h1 (h2.congr fun n => hp n)).symm
  refine ⟨‖ContinuousLinearMap.ofIsClosedGraph hgraph‖, fun U x => ?_⟩
  have hb := (ContinuousLinearMap.ofIsClosedGraph hgraph U).norm_coe_le_norm x
  have hn := (ContinuousLinearMap.ofIsClosedGraph hgraph).le_opNorm U
  rw [ContinuousLinearMap.coeFn_ofIsClosedGraph] at hb hn
  rw [← Real.norm_eq_abs]
  exact hb.trans hn

/-- W-PDE2 B5 helper: the `H¹` weak solutions of the homogeneous equation form a closed
submodule. -/
theorem s05_dp_solspace {Ω₁ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))} (hc : IsCompact (closure (Ω₁ : Set (EuclideanSpace ℝ (Fin 2)))))
    {A : (EuclideanSpace ℝ (Fin 2)) → Matrix (Fin 2) (Fin 2) ℝ} {β : (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2))} {γ : (EuclideanSpace ℝ (Fin 2)) → ℝ}
    (hAc : ContinuousOn A (closure Ω₁)) (hβc : ContinuousOn β (closure Ω₁))
    (hγc : ContinuousOn γ (closure Ω₁)) :
    ∃ S : Submodule ℝ (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2), IsClosed (S : Set (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)) ∧
      ∀ U, U ∈ S ↔ ∀ v : (TauCeti.W1p0 (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2), TauCeti.PDE.energyFormH1 A β γ U (v : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)) = 0 := by
  have hcoeff := TauCeti.PDE.memLp_energyIntegrand_of_continuousOn (mu := volume) hc hAc hβc hγc
  have hEc : ∀ v : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2), Continuous fun U : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2) => TauCeti.PDE.energyFormH1 A β γ U v := fun v => by
    have := (TauCeti.PDE.energyFormH1L (mu := volume) (Omega := Ω₁) hcoeff).continuous.clm_apply
      (continuous_const (y := v))
    simpa only [TauCeti.PDE.energyFormH1L_apply] using this
  -- the space of weak solutions: a closed submodule
  obtain ⟨S, hmemS⟩ : ∃ S : Submodule ℝ (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2),
      ∀ U, U ∈ S ↔ ∀ v : (TauCeti.W1p0 (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2), TauCeti.PDE.energyFormH1 A β γ U (v : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)) = 0 :=
    ⟨{ carrier := {U | ∀ v : (TauCeti.W1p0 (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2), TauCeti.PDE.energyFormH1 A β γ U (v : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)) = 0}
       add_mem' := fun {U V} hU hV v => by
         simp only [Set.mem_ofPred_eq] at hU hV ⊢
         rw [TauCeti.PDE.energyFormH1_add_left hcoeff U (v : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)) V, hU v, hV v, add_zero]
       zero_mem' := fun v => TauCeti.PDE.energyFormH1_zero_left A β γ _
       smul_mem' := fun c U hU v => by
         simp only [Set.mem_ofPred_eq] at hU ⊢
         rw [TauCeti.PDE.energyFormH1_smul_left, hU v, mul_zero] },
      fun U => Iff.rfl⟩
  have hSc : IsClosed (S : Set (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)) := by
    have : (S : Set (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)) = ⋂ v : (TauCeti.W1p0 (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2), {U : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2) | TauCeti.PDE.energyFormH1 A β γ U (v : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)) = 0} := by
      ext U
      simp only [SetLike.mem_coe, hmemS, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [this]
    exact isClosed_iInter fun v => isClosed_eq (hEc _) continuous_const
  exact ⟨S, hSc, hmemS⟩

/-- W-PDE2 B5 helper: continuous representatives on `Ω₁` of elements of `H¹(Ω₁)` depend
linearly on the element. -/
theorem s05_dp_rep_lin {Ω₁ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))} {S : Submodule ℝ (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)}
    (rep : S → (EuclideanSpace ℝ (Fin 2)) → ℝ) (hrc : ∀ U, ContinuousOn (rep U) Ω₁)
    (hra : ∀ U : S, (TauCeti.W1p.value U.1 : (EuclideanSpace ℝ (Fin 2)) → ℝ) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₁] rep U) :
    (∀ U V : S, EqOn (rep (U + V)) (fun x => rep U x + rep V x) Ω₁) ∧
      ∀ (a : ℝ) (U : S), EqOn (rep (a • U)) (fun x => a * rep U x) Ω₁ := by
  refine ⟨fun U V => ?_, fun a U => ?_⟩
  · have h1 : (TauCeti.W1p.value (U + V).1 : (EuclideanSpace ℝ (Fin 2)) → ℝ) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₁]
        fun x => rep U x + rep V x := by
      have := TauCeti.W1p.value_add_ae (mu := volume) U.1 V.1
      filter_upwards [this, hra U, hra V] with y hy h1 h2
      rw [Submodule.coe_add, hy, Pi.add_apply, h1, h2]
    exact Measure.eqOn_open_of_ae_eq ((hra (U + V)).symm.trans h1) Ω₁.isOpen (hrc (U + V))
      ((hrc U).add (hrc V))
  · have h1 : (TauCeti.W1p.value (a • U).1 : (EuclideanSpace ℝ (Fin 2)) → ℝ) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₁]
        fun x => a * rep U x := by
      have := TauCeti.W1p.value_smul_ae (mu := volume) a U.1
      filter_upwards [this, hra U] with y hy h1
      rw [Submodule.coe_smul, hy, Pi.smul_apply, h1, smul_eq_mul]
    exact Measure.eqOn_open_of_ae_eq ((hra (a • U)).symm.trans h1) Ω₁.isOpen (hrc (a • U))
      ((hrc U).const_smul a)

/-- W-PDE2 B5 helper: the restriction of continuous representatives to a compact `K ⊆ Ω₁` has
sequentially closed graph `H¹(Ω₁) → C(K)`. -/
theorem s05_dp_rep_graph {Ω₁ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))} {S : Submodule ℝ (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)}
    (rep : S → (EuclideanSpace ℝ (Fin 2)) → ℝ) (hrc : ∀ U, ContinuousOn (rep U) Ω₁)
    (hra : ∀ U : S, (TauCeti.W1p.value U.1 : (EuclideanSpace ℝ (Fin 2)) → ℝ) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₁] rep U)
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hKc : IsCompact K) (hK : K ⊆ Ω₁) (hKi : K ⊆ closure (interior K))
    (f : S → C(K, ℝ)) (hf : ∀ U x, f U x = rep U x) (p : ℕ → S) (q₁ : S) (q₂ : C(K, ℝ))
    (h1 : Tendsto p atTop (𝓝 q₁)) (h2 : Tendsto (fun n => f (p n)) atTop (𝓝 q₂)) :
    f q₁ = q₂ := by
  classical
  have h3 : Tendsto (fun n => TauCeti.W1p.value (p n).1) atTop
      (𝓝 (TauCeti.W1p.value q₁.1)) :=
    ((TauCeti.W1p.valueL (mu := volume) (Omega := Ω₁) (p := 2)).continuous.comp
      continuous_subtype_val).continuousAt.tendsto.comp h1
  obtain ⟨ns, hns_mono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp h3).exists_seq_tendsto_ae
  have h4 : ∀ x : K, Tendsto (fun n => rep (p (ns n)) x) atTop (𝓝 (q₂ x)) := by
    intro x
    have := ((continuous_eval_const x).tendsto _).comp h2
    exact (this.comp hns_mono.tendsto_atTop).congr fun n => hf _ _
  have h5 : (fun x => if hx : x ∈ K then q₂ ⟨x, hx⟩ else 0)
      =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict K] rep q₁ := by
    have hae := ae_all_iff.2 fun n => hra (p (ns n))
    have hae' := (ae_restrict_of_ae_restrict_of_subset hK (hae.and (hns.and (hra q₁))))
    filter_upwards [hae', ae_restrict_mem (hKc.isClosed.measurableSet)]
      with x ⟨hx1, hx2, hx3⟩ hxK
    rw [dite_eq_left hxK, ← hx3]
    refine tendsto_nhds_unique (h4 ⟨x, hxK⟩) ?_
    exact hx2.congr fun n => hx1 n
  have h6 := Measure.eqOn_of_ae_eq h5 (by
    refine continuousOn_iff_continuous_domRestrict.2 ?_
    convert q₂.continuous using 1
    ext x
    simp [x.2]) ((hrc q₁).mono hK) hKi
  ext x
  have := h6 x.2
  simp only [dite_eq_left x.2] at this
  rw [hf, ← this]

/-- W-PDE2 B5 helper: on a compact `K ⊆ Ω₁`, continuous representatives of a closed subspace of
`H¹(Ω₁)` are bounded by `C ‖U‖_{H¹}` (closed graph theorem). -/
theorem s05_dp_cg_rep {Ω₁ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))} {S : Submodule ℝ (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)}
    (hSc : IsClosed (S : Set (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2))) (rep : S → (EuclideanSpace ℝ (Fin 2)) → ℝ) (hrc : ∀ U, ContinuousOn (rep U) Ω₁)
    (hra : ∀ U : S, (TauCeti.W1p.value U.1 : (EuclideanSpace ℝ (Fin 2)) → ℝ) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₁] rep U)
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hKc : IsCompact K) (hK : K ⊆ Ω₁) (hKi : K ⊆ closure (interior K)) :
    ∃ C : ℝ, ∀ U : S, ∀ x ∈ K, |rep U x| ≤ C * ‖U‖ := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  obtain ⟨hadd, hsmul⟩ := s05_dp_rep_lin rep hrc hra
  let Tf : S → C(K, ℝ) := fun U => ⟨fun x => rep U x, ((hrc U).mono hK).domRestrict⟩
  obtain ⟨C, hC⟩ := s05_dp_cg_core hSc Tf
    (fun U V => ContinuousMap.ext fun x => hadd U V (hK x.2))
    (fun a U => ContinuousMap.ext fun x => hsmul a U (hK x.2))
    (s05_dp_rep_graph rep hrc hra hKc hK hKi Tf fun _ _ => rfl)
  exact ⟨C, fun U x hx => hC U ⟨x, hx⟩⟩

/-- W-PDE2 B5 (interior sup bound by the closed graph theorem): on a ball `closedBall z r ⊆ Ω₁`,
every continuous representative `g` of an `H¹` weak solution `U` of the homogeneous equation
`-∂ᵢ(Aⁱʲ∂ⱼU) + βʲ∂ⱼU + γU = 0` satisfies `|g| ≤ C ‖U‖_{H¹}`, with `C` independent of `U`. -/
theorem s05_dp_cg {Ω₁ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))} (hc : IsCompact (closure (Ω₁ : Set (EuclideanSpace ℝ (Fin 2)))))
    {A : (EuclideanSpace ℝ (Fin 2)) → Matrix (Fin 2) (Fin 2) ℝ} {β : (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2))} {γ : (EuclideanSpace ℝ (Fin 2)) → ℝ} {lam Lam : ℝ}
    (hell : TauCeti.PDE.UniformlyEllipticOn (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))) A lam Lam)
    (hAc : ContinuousOn A (closure Ω₁)) (hβc : ContinuousOn β (closure Ω₁))
    (hγc : ContinuousOn γ (closure Ω₁)) (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) Ω₁)
    (hβ : ContDiffOn ℝ ∞ β Ω₁) (hγ : ContDiffOn ℝ ∞ γ Ω₁) {z : (EuclideanSpace ℝ (Fin 2))} {r : ℝ} (hr : 0 < r)
    (hK : closedBall z r ⊆ Ω₁) :
    ∃ C : ℝ, ∀ U : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2),
      (∀ v : (TauCeti.W1p0 (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2),
        TauCeti.PDE.energyFormH1 A β γ U (v : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2) = 0) →
      ∀ g : (EuclideanSpace ℝ (Fin 2)) → ℝ, ContinuousOn g (closedBall z r) →
        (TauCeti.W1p.value U : (EuclideanSpace ℝ (Fin 2)) → ℝ) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict (closedBall z r)] g →
          ∀ x ∈ closedBall z r, |g x| ≤ C * ‖U‖ := by
  classical
  obtain ⟨S, hSc, hmemS⟩ := s05_dp_solspace hc hAc hβc hγc
  have hrep : ∀ U : S, ∃ g : (EuclideanSpace ℝ (Fin 2)) → ℝ, ContDiffOn ℝ ∞ g Ω₁ ∧
      (TauCeti.W1p.value U.1 : (EuclideanSpace ℝ (Fin 2)) → ℝ) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₁] g := fun U =>
    s05_dp_hom_rep hc hell hAc hβc hγc hA hβ hγ ((hmemS U.1).1 U.2)
  choose rep hrs hra using hrep
  have hKi : closedBall z r ⊆ closure (interior (closedBall z r)) := by
    rw [interior_closedBall z hr.ne', closure_ball z hr.ne']
  obtain ⟨C, hC⟩ := s05_dp_cg_rep hSc rep (fun U => (hrs U).continuousOn) hra
    (isCompact_closedBall z r) hK hKi
  refine ⟨C, fun U hU g hg hUg x hx => ?_⟩
  have hUS : U ∈ S := (hmemS U).2 hU
  have hgr : EqOn g (rep ⟨U, hUS⟩) (closedBall z r) := Measure.eqOn_of_ae_eq
    (hUg.symm.trans (ae_restrict_of_ae_restrict_of_subset hK (hra ⟨U, hUS⟩))) hg
      ((hrs ⟨U, hUS⟩).continuousOn.mono hK) hKi
  calc |g x| = |rep ⟨U, hUS⟩ x| := by rw [hgr hx]
    _ ≤ C * ‖(⟨U, hUS⟩ : S)‖ := hC _ x hx
    _ = C * ‖U‖ := by rw [← Submodule.norm_coe]

/-- W-PDE2 B6 helper: bounded continuous functions converging pointwise on a set of finite
measure converge in `L²` there, and their pairwise `L²` distances are controlled. -/
theorem s05_dp_l2_tendsto {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : MeasurableSet S) (hSf : volume S ≠ ⊤)
    {g : ℕ → (EuclideanSpace ℝ (Fin 2)) → ℝ} {g₀ : (EuclideanSpace ℝ (Fin 2)) → ℝ} {K : ℝ} (hgc : ∀ n, ContinuousOn (g n) S)
    (hb : ∀ n, ∀ x ∈ S, |g n x| ≤ K)
    (hl : ∀ x ∈ S, Tendsto (fun n => g n x) atTop (𝓝 (g₀ x))) :
    Tendsto (fun n => ∫ x in S, (g n x - g₀ x) ^ 2) atTop (𝓝 0) ∧
      ∀ n m, ∫ x in S, (g n x - g m x) ^ 2 ≤
        2 * (∫ x in S, (g n x - g₀ x) ^ 2) + 2 * ∫ x in S, (g m x - g₀ x) ^ 2 := by
  have : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hSf.lt_top⟩
  have hm : ∀ n, AEStronglyMeasurable (g n) ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict S) := fun n =>
    (hgc n).aestronglyMeasurable hS
  have hm0 : AEStronglyMeasurable g₀ ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict S) :=
    aestronglyMeasurable_of_tendsto_ae atTop hm
      ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall hl))
  have hb0 : ∀ x ∈ S, |g₀ x| ≤ K := fun x hx =>
    le_of_tendsto' (hl x hx).abs fun n => hb n x hx
  have hsq : ∀ n, ∀ x ∈ S, ‖(g n x - g₀ x) ^ 2‖ ≤ (2 * K) ^ 2 := by
    intro n x hx
    rw [Real.norm_eq_abs, abs_pow]
    have h1 := hb n x hx
    have h2 := hb0 x hx
    have h3 : |g n x - g₀ x| ≤ 2 * K := (abs_sub _ _).trans (by linarith)
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  have hmeas : ∀ n, AEStronglyMeasurable (fun x => (g n x - g₀ x) ^ 2)
      ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict S) := fun n => ((hm n).sub hm0).pow 2
  have hint : ∀ n, Integrable (fun x => (g n x - g₀ x) ^ 2) ((volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict S) :=
    fun n => Integrable.of_bound (hmeas n) ((2 * K) ^ 2)
      ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall (hsq n)))
  refine ⟨?_, fun n m => ?_⟩
  · have := tendsto_integral_of_dominated_convergence (F := fun n x => (g n x - g₀ x) ^ 2)
      (f := fun _ => (0 : ℝ)) (fun _ => (2 * K) ^ 2) hmeas (integrable_const _)
      (fun n => (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall (hsq n)))
      ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun x hx => by
        simpa using ((hl x hx).sub_const (g₀ x)).pow 2))
    simpa using this
  · have e1 : ∫ x in S, 2 * (g n x - g₀ x) ^ 2 = 2 * ∫ x in S, (g n x - g₀ x) ^ 2 :=
      integral_const_mul _ _
    have e2 : ∫ x in S, 2 * (g m x - g₀ x) ^ 2 = 2 * ∫ x in S, (g m x - g₀ x) ^ 2 :=
      integral_const_mul _ _
    rw [← e1, ← e2, ← integral_add ((hint n).const_mul 2) ((hint m).const_mul 2)]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (((hint n).const_mul 2).add ((hint m).const_mul 2)) (Filter.Eventually.of_forall fun x => ?_)
    show (g n x - g m x) ^ 2 ≤ 2 * (g n x - g₀ x) ^ 2 + 2 * (g m x - g₀ x) ^ 2
    nlinarith [sq_nonneg (g n x + g m x - 2 * g₀ x)]

/-- W-PDE2 B6 helper: a sequence whose squared distances are bounded by `C (2aₙ + 2aₘ)` with
`aₙ → 0` is Cauchy. -/
theorem s05_dp_cauchy {W : Type*} [NormedAddCommGroup W] {G : ℕ → W} {a : ℕ → ℝ} {C : ℝ}
    (ha : Tendsto a atTop (𝓝 0)) (hC : 0 ≤ C)
    (hG : ∀ n m, ‖G n - G m‖ ^ 2 ≤ C * (2 * a n + 2 * a m)) : CauchySeq G := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < ε ^ 2 / (4 * (C + 1)) := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ha _ hδ
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  have h2 := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at h1 h2
  have h3 : 2 * a n + 2 * a N ≤ 4 * (ε ^ 2 / (4 * (C + 1))) := by
    linarith [(abs_lt.1 h1).2, (abs_lt.1 h2).2]
  have h4 : (C + 1) * (4 * (ε ^ 2 / (4 * (C + 1)))) = ε ^ 2 := by
    field_simp
  have h5 : C * (2 * a n + 2 * a N) < ε ^ 2 := by
    calc C * (2 * a n + 2 * a N) ≤ C * (4 * (ε ^ 2 / (4 * (C + 1)))) :=
          mul_le_mul_of_nonneg_left h3 hC
      _ < (C + 1) * (4 * (ε ^ 2 / (4 * (C + 1)))) := by nlinarith
      _ = ε ^ 2 := h4
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le ((hG n N).trans_lt h5)

/-- W-PDE2 B6 helper: an `H¹` limit of weak solutions of `a(U, v) = ∫ f v` is a weak solution. -/
theorem s05_dp_weak_lim {Ω₁ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))} (hc : IsCompact (closure (Ω₁ : Set (EuclideanSpace ℝ (Fin 2)))))
    {A : (EuclideanSpace ℝ (Fin 2)) → Matrix (Fin 2) (Fin 2) ℝ} {β : (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2))} {γ f : (EuclideanSpace ℝ (Fin 2)) → ℝ}
    (hAc : ContinuousOn A (closure Ω₁)) (hβc : ContinuousOn β (closure Ω₁))
    (hγc : ContinuousOn γ (closure Ω₁)) {G : ℕ → (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)} {U : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)} (hGU : Tendsto G atTop (𝓝 U))
    (hG : ∀ n, ∀ v : (TauCeti.W1p0 (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2), TauCeti.PDE.energyFormH1 A β γ (G n) (v : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)) =
      ∫ x in (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))), f x * TauCeti.W1p.value (v : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)) x) :
    ∀ v : (TauCeti.W1p0 (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2), TauCeti.PDE.energyFormH1 A β γ U (v : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)) =
      ∫ x in (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))), f x * TauCeti.W1p.value (v : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)) x := by
  have hcoeff := TauCeti.PDE.memLp_energyIntegrand_of_continuousOn (mu := volume) hc hAc hβc hγc
  intro v
  have hEc : Continuous fun U : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2) => TauCeti.PDE.energyFormH1 A β γ U (v : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)) := by
    have := (TauCeti.PDE.energyFormH1L (mu := volume) (Omega := Ω₁) hcoeff).continuous.clm_apply
      (continuous_const (y := (v : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2))))
    simpa only [TauCeti.PDE.energyFormH1L_apply] using this
  exact tendsto_nhds_unique ((hEc.tendsto U).comp hGU)
    (tendsto_const_nhds.congr fun n => (hG n v).symm)

/-- W-PDE2 B6 helper: an `H¹` weak solution of `a(U, v) = ∫ f v` with smooth data has a smooth
representative, which solves the equation classically. -/
theorem s05_dp_sol_rep {Ω₁ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))} (hc : IsCompact (closure (Ω₁ : Set (EuclideanSpace ℝ (Fin 2)))))
    {A : (EuclideanSpace ℝ (Fin 2)) → Matrix (Fin 2) (Fin 2) ℝ} {β : (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2))} {γ f : (EuclideanSpace ℝ (Fin 2)) → ℝ} {lam Lam : ℝ}
    (hell : TauCeti.PDE.UniformlyEllipticOn (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))) A lam Lam)
    (hAc : ContinuousOn A (closure Ω₁)) (hβc : ContinuousOn β (closure Ω₁))
    (hγc : ContinuousOn γ (closure Ω₁)) (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) Ω₁)
    (hβ : ContDiffOn ℝ ∞ β Ω₁) (hγ : ContDiffOn ℝ ∞ γ Ω₁) (hfc : ContinuousOn f (closure Ω₁))
    (hf : ContDiffOn ℝ ∞ f Ω₁) {U : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)}
    (hU : ∀ v : (TauCeti.W1p0 (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2), TauCeti.PDE.energyFormH1 A β γ U (v : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)) =
      ∫ x in (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))), f x * TauCeti.W1p.value (v : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)) x) :
    ∃ g : (EuclideanSpace ℝ (Fin 2)) → ℝ, ContDiffOn ℝ ∞ g Ω₁ ∧
      (TauCeti.W1p.value U : (EuclideanSpace ℝ (Fin 2)) → ℝ) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₁] g ∧
      ∀ x ∈ (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))),
        -(∑ i : Fin 2, fderiv ℝ (fun y => ∑ j : Fin 2, A y i j * fderiv ℝ g y
            (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) +
          ∑ j : Fin 2, β x j * fderiv ℝ g x (EuclideanSpace.single j 1) + γ x * g x = f x := by
  have hs := s05_dp_b2_split hc hAc hβc hγc hfc hU
  have hk : ∀ (k : ℕ) (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))), IsCompact (closure (V : Set (EuclideanSpace ℝ (Fin 2)))) →
      closure (V : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Ω₁ → ∃ w : TauCeti.Wkp (volume : Measure (EuclideanSpace ℝ (Fin 2))) V 2 (k + 1),
        (TauCeti.Wkp.value (k + 1) w : (EuclideanSpace ℝ (Fin 2)) → ℝ) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict V]
          TauCeti.W1p.value U := fun k V hV hVΩ =>
    pde_Hk_loc hell hA hβ hγ hf hs k hV hVΩ
  obtain ⟨g, hg, hug⟩ := pde_smooth_rep (Ω := Ω₁) (u := TauCeti.W1p.value U) fun k V hV hVΩ => by
    cases k with
    | zero =>
      obtain ⟨w, hw⟩ := hk 0 V hV hVΩ
      refine ⟨TauCeti.Wkp.lowerOrder 0 w, ?_⟩
      rw [← TauCeti.Wkp.value_succ]
      exact hw
    | succ k => exact hk k V hV hVΩ
  exact ⟨g, hg, hug, pde_classical hA hβ hγ hf hs hg hug⟩

/-- W-PDE2 B6 helper: if `Gₙ → U` in `H¹` are weak solutions of the same equation with
continuous representatives `gₙ`, `g`, then `gₙ → g` pointwise on any ball `⊆ Ω₁` (B5). -/
theorem s05_dp_ident {Ω₁ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))} (hc : IsCompact (closure (Ω₁ : Set (EuclideanSpace ℝ (Fin 2)))))
    {A : (EuclideanSpace ℝ (Fin 2)) → Matrix (Fin 2) (Fin 2) ℝ} {β : (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2))} {γ f : (EuclideanSpace ℝ (Fin 2)) → ℝ} {lam Lam : ℝ}
    (hell : TauCeti.PDE.UniformlyEllipticOn (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))) A lam Lam)
    (hAc : ContinuousOn A (closure Ω₁)) (hβc : ContinuousOn β (closure Ω₁))
    (hγc : ContinuousOn γ (closure Ω₁)) (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) Ω₁)
    (hβ : ContDiffOn ℝ ∞ β Ω₁) (hγ : ContDiffOn ℝ ∞ γ Ω₁) {z : (EuclideanSpace ℝ (Fin 2))} {r : ℝ} (hr : 0 < r)
    (hK : closedBall z r ⊆ Ω₁) {G : ℕ → (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)} {U : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)} (hGU : Tendsto G atTop (𝓝 U))
    (hG : ∀ n, ∀ v : (TauCeti.W1p0 (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2), TauCeti.PDE.energyFormH1 A β γ (G n) (v : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)) =
      ∫ x in (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))), f x * TauCeti.W1p.value (v : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)) x)
    (hU : ∀ v : (TauCeti.W1p0 (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2), TauCeti.PDE.energyFormH1 A β γ U (v : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)) =
      ∫ x in (Ω₁ : Set (EuclideanSpace ℝ (Fin 2))), f x * TauCeti.W1p.value (v : (TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₁ 2)) x)
    {g : ℕ → (EuclideanSpace ℝ (Fin 2)) → ℝ} (hgc : ∀ n, ContinuousOn (g n) Ω₁)
    (hGg : ∀ n, (TauCeti.W1p.value (G n) : (EuclideanSpace ℝ (Fin 2)) → ℝ) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₁] g n)
    {g' : (EuclideanSpace ℝ (Fin 2)) → ℝ} (hgc' : ContinuousOn g' Ω₁)
    (hUg : (TauCeti.W1p.value U : (EuclideanSpace ℝ (Fin 2)) → ℝ) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₁] g') :
    ∀ x ∈ closedBall z r, Tendsto (fun n => g n x) atTop (𝓝 (g' x)) := by
  have hcoeff := TauCeti.PDE.memLp_energyIntegrand_of_continuousOn (mu := volume) hc hAc hβc hγc
  obtain ⟨C, hC⟩ := s05_dp_cg hc hell hAc hβc hγc hA hβ hγ hr hK
  intro x hx
  have hb : ∀ n, |g n x - g' x| ≤ C * ‖G n - U‖ := fun n => by
    refine hC (G n - U) (fun v => ?_) (fun y => g n y - g' y) (((hgc n).sub hgc').mono hK) ?_ x hx
    · rw [TauCeti.PDE.energyFormH1_sub_left hcoeff, hG n v, hU v, sub_self]
    · exact ae_restrict_of_ae_restrict_of_subset hK
        ((TauCeti.W1p.value_sub_ae _ _).trans ((hGg n).sub hUg))
  have h0 : Tendsto (fun n => C * ‖G n - U‖) atTop (𝓝 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hGU).const_mul C
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => by rw [Real.norm_eq_abs]; exact hb n) h0

/-- W-PDE2 B6 helper: two `H¹` functions with the same representative agree after
restriction. -/
theorem s05_dp_restrict_eq {Ω₂ Ω₃ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))} (hle : Ω₂ ≤ Ω₃)
    {G : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₃ 2} {G' : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₂ 2}
    {g : (EuclideanSpace ℝ (Fin 2)) → ℝ} (hG : (TauCeti.W1p.value G : (EuclideanSpace ℝ (Fin 2)) → ℝ) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₃] g)
    (hG' : (TauCeti.W1p.value G' : (EuclideanSpace ℝ (Fin 2)) → ℝ) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₂] g) :
    TauCeti.W1p.restrictL hle G = G' := by
  have h1 : (TauCeti.W1p.value G : (EuclideanSpace ℝ (Fin 2)) → ℝ) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₂] g :=
    ae_restrict_of_ae_restrict_of_subset (fun x hx => hle hx) hG
  exact TauCeti.W1p.ext_value (Lp.ext ((TauCeti.W1p.value_restrictL_ae hle G).trans
    (h1.trans hG'.symm)))

/-- W-PDE2 B6 helper (Caccioppoli + `L²` convergence): weak solutions `Gₙ ∈ H¹(Ω₃)` of the same
equation whose representatives converge boundedly pointwise restrict to a Cauchy sequence in
`H¹(Ω₂)`, `Ω₂ ⋐ Ω₃`. -/
theorem s05_dp_h1_cauchy {Ω₂ Ω₃ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))} (hle : Ω₂ ≤ Ω₃)
    (h23 : closure (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Ω₃) (hc3 : IsCompact (closure (Ω₃ : Set (EuclideanSpace ℝ (Fin 2)))))
    {A : (EuclideanSpace ℝ (Fin 2)) → Matrix (Fin 2) (Fin 2) ℝ} {β : (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2))} {γ f : (EuclideanSpace ℝ (Fin 2)) → ℝ} {lam Lam : ℝ}
    (hAc : ContinuousOn A (closure Ω₃)) (hβc : ContinuousOn β (closure Ω₃))
    (hγc : ContinuousOn γ (closure Ω₃))
    (hell : TauCeti.PDE.UniformlyEllipticOn (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))) A lam Lam)
    (hγ0 : ∀ x ∈ (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))), 0 ≤ γ x) {G : ℕ → TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₃ 2}
    (hG : ∀ n, ∀ v : TauCeti.W1p0 (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₃ 2,
      TauCeti.PDE.energyFormH1 A β γ (G n) (v : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₃ 2) =
        ∫ x in (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))), f x * TauCeti.W1p.value (v : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₃ 2) x)
    {G' : ℕ → TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₂ 2}
    (hGG' : ∀ n, TauCeti.W1p.restrictL hle (G n) = G' n) {g : ℕ → (EuclideanSpace ℝ (Fin 2)) → ℝ} {g₀ : (EuclideanSpace ℝ (Fin 2)) → ℝ} {K : ℝ}
    (hgc : ∀ n, ContinuousOn (g n) Ω₃) (hb : ∀ n, ∀ x ∈ (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))), |g n x| ≤ K)
    (hl : ∀ x ∈ (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))), Tendsto (fun n => g n x) atTop (𝓝 (g₀ x)))
    (hGg : ∀ n, (TauCeti.W1p.value (G n) : (EuclideanSpace ℝ (Fin 2)) → ℝ) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₃] g n) :
    CauchySeq G' := by
  obtain ⟨C, hC0, hC⟩ := s05_dp_b3_cacc hle h23 hc3 hAc hβc hγc hell hγ0
  have hcoeff := TauCeti.PDE.memLp_energyIntegrand_of_continuousOn (mu := volume) hc3 hAc hβc hγc
  have hms : MeasurableSet (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))) := Ω₃.isOpen.measurableSet
  have hfin : volume (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))) ≠ ⊤ :=
    ((measure_mono subset_closure).trans_lt hc3.measure_lt_top).ne
  obtain ⟨ha, hle2⟩ := s05_dp_l2_tendsto hms hfin hgc hb hl
  refine s05_dp_cauchy ha hC0 fun n m => ?_
  have h1 := hC (G n - G m) fun v => by
    rw [TauCeti.PDE.energyFormH1_sub_left hcoeff, hG n v, hG m v, sub_self]
  rw [map_sub, hGG', hGG'] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left (le_of_eq_of_le ?_ (hle2 n m)) hC0)
  refine integral_congr_ae ?_
  filter_upwards [TauCeti.W1p.value_sub_ae (G n) (G m), hGg n, hGg m] with x hx h1 h2
  rw [hx, Pi.sub_apply, h1, h2]

/-- W-PDE2 B6 core (Euclidean): smooth classical solutions `gₙ` of
`-∂ᵢ(Aⁱʲ∂ⱼg) + βʲ∂ⱼg + γg = f` on `V ⊇ closure Ω₃`, bounded and converging pointwise to `g₀` on
`Ω₃`, have a limit that agrees on a ball `closedBall z r ⊆ Ω₂` with a smooth classical solution
on `Ω₂ ⋐ Ω₃`. -/
theorem s05_dp_core {Ω₂ Ω₃ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))} (hle : Ω₂ ≤ Ω₃)
    (h23 : closure (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Ω₃) (hc3 : IsCompact (closure (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))))) {V : Set (EuclideanSpace ℝ (Fin 2))}
    (hV : IsOpen V) (h3V : closure (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ V)
    {A : (EuclideanSpace ℝ (Fin 2)) → Matrix (Fin 2) (Fin 2) ℝ} {β : (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2))} {γ f : (EuclideanSpace ℝ (Fin 2)) → ℝ} {lam Lam : ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) V) (hβ : ContDiffOn ℝ ∞ β V)
    (hγ : ContDiffOn ℝ ∞ γ V) (hf : ContDiffOn ℝ ∞ f V)
    (hell : TauCeti.PDE.UniformlyEllipticOn (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))) A lam Lam)
    (hγ0 : ∀ x ∈ (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))), 0 ≤ γ x) {g : ℕ → (EuclideanSpace ℝ (Fin 2)) → ℝ} (hg : ∀ n, ContDiffOn ℝ ∞ (g n) V)
    (heq : ∀ n, ∀ x ∈ (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))),
      -(∑ i : Fin 2, fderiv ℝ (fun y => ∑ j : Fin 2, A y i j * fderiv ℝ (g n) y
          (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) +
        ∑ j : Fin 2, β x j * fderiv ℝ (g n) x (EuclideanSpace.single j 1) + γ x * g n x = f x)
    {g₀ : (EuclideanSpace ℝ (Fin 2)) → ℝ} {K : ℝ} (hb : ∀ n, ∀ x ∈ (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))), |g n x| ≤ K)
    (hl : ∀ x ∈ (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))), Tendsto (fun n => g n x) atTop (𝓝 (g₀ x)))
    {z : (EuclideanSpace ℝ (Fin 2))} {r : ℝ} (hr : 0 < r) (hK : closedBall z r ⊆ Ω₂) :
    ∃ g' : (EuclideanSpace ℝ (Fin 2)) → ℝ, ContDiffOn ℝ ∞ g' Ω₂ ∧
      (∀ x ∈ (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))),
        -(∑ i : Fin 2, fderiv ℝ (fun y => ∑ j : Fin 2, A y i j * fderiv ℝ g' y
            (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) +
          ∑ j : Fin 2, β x j * fderiv ℝ g' x (EuclideanSpace.single j 1) + γ x * g' x = f x) ∧
      EqOn g' g₀ (closedBall z r) := by
  have h2V : closure (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ V := h23.trans (subset_closure.trans h3V)
  have hc2 : IsCompact (closure (Ω₂ : Set (EuclideanSpace ℝ (Fin 2)))) :=
    hc3.of_isClosed_subset isClosed_closure (h23.trans subset_closure)
  have hs2 : (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ V := subset_closure.trans h2V
  have hs3 : (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ V := subset_closure.trans h3V
  have hAc : ContinuousOn A V :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hA i j).continuousOn
  have hell2 : TauCeti.PDE.UniformlyEllipticOn (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))) A lam Lam := by
    have h := hell
    unfold TauCeti.PDE.UniformlyEllipticOn at h ⊢
    exact ⟨h.1, h.2.1, fun x hx => h.2.2 (hle hx)⟩
  -- weak solutions on `Ω₃` and on `Ω₂`
  have hW3 := fun n => s05_dp_b2_weak hc3 hV h3V hA hβ hγ (hg n) (hf.continuousOn.mono h3V)
    (heq n)
  choose G hGv _hGgr hGw using hW3
  have hW2 := fun n => s05_dp_b2_weak hc2 hV h2V hA hβ hγ (hg n) (hf.continuousOn.mono h2V)
    fun x hx => heq n x (hle hx)
  choose G' hG'v _hG'gr hG'w using hW2
  have hGG' : ∀ n, TauCeti.W1p.restrictL hle (G n) = G' n := fun n =>
    s05_dp_restrict_eq hle (hGv n) (hG'v n)
  have hcs := s05_dp_h1_cauchy hle h23 hc3 (hAc.mono h3V) (hβ.continuousOn.mono h3V)
    (hγ.continuousOn.mono h3V) hell hγ0 hGw hGG' (fun n => (hg n).continuousOn.mono hs3) hb hl hGv
  obtain ⟨U, hU⟩ := cauchySeq_tendsto_of_complete hcs
  have hUw := s05_dp_weak_lim hc2 (hAc.mono h2V) (hβ.continuousOn.mono h2V)
    (hγ.continuousOn.mono h2V) hU hG'w
  obtain ⟨g', hg', hUg', hL'⟩ := s05_dp_sol_rep hc2 hell2 (hAc.mono h2V)
    (hβ.continuousOn.mono h2V) (hγ.continuousOn.mono h2V) (fun i j => (hA i j).mono hs2)
    (hβ.mono hs2) (hγ.mono hs2) (hf.continuousOn.mono h2V) (hf.mono hs2) hUw
  refine ⟨g', hg', hL', fun x hx => ?_⟩
  have ht := s05_dp_ident hc2 hell2 (hAc.mono h2V) (hβ.continuousOn.mono h2V)
    (hγ.continuousOn.mono h2V) (fun i j => (hA i j).mono hs2) (hβ.mono hs2) (hγ.mono hs2) hr hK
    hU hG'w hUw (fun n => (hg n).continuousOn.mono hs2) hG'v hg'.continuousOn hUg' x hx
  exact tendsto_nhds_unique ht (hl x (hle (hK hx)))

/-- W-PDE2 B6 helper: the pointwise `L² → L^∞` bound from the Caccioppoli and closed-graph
constants. -/
theorem s05_dp_sup_pt {Ω₂ Ω₃ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))} (hle : Ω₂ ≤ Ω₃) {C₃ C₅ : ℝ}
    {G : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₃ 2} {G' : TauCeti.W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) Ω₂ 2}
    (hGG' : TauCeti.W1p.restrictL hle G = G')
    (h1 : ‖TauCeti.W1p.restrictL hle G‖ ^ 2 ≤
      C₃ * ∫ y in (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))), TauCeti.W1p.value G y ^ 2)
    {g : (EuclideanSpace ℝ (Fin 2)) → ℝ} (hGv : (TauCeti.W1p.value G : (EuclideanSpace ℝ (Fin 2)) → ℝ) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2))).restrict Ω₃] g)
    {x : (EuclideanSpace ℝ (Fin 2))} (h2 : |g x| ≤ C₅ * ‖G'‖) :
    g x ^ 2 ≤ C₅ ^ 2 * C₃ * ∫ y in (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))), g y ^ 2 := by
  have hint : ∫ y in (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))), TauCeti.W1p.value G y ^ 2 = ∫ y in (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))), g y ^ 2 :=
    integral_congr_ae (hGv.mono fun y hy => congrArg (· ^ 2) hy)
  subst hGG'
  calc g x ^ 2 = |g x| ^ 2 := (sq_abs _).symm
    _ ≤ (C₅ * ‖TauCeti.W1p.restrictL hle G‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    _ = C₅ ^ 2 * ‖TauCeti.W1p.restrictL hle G‖ ^ 2 := by ring
    _ ≤ C₅ ^ 2 * (C₃ * ∫ y in (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))), TauCeti.W1p.value G y ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = C₅ ^ 2 * C₃ * ∫ y in (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))), g y ^ 2 := by rw [hint]; ring

/-- W-PDE2 B6 helper (Euclidean `L² → L^∞` estimate): smooth solutions of `L g = 0` on `Ω₃`
satisfy `g(x)² ≤ C ∫_{Ω₃} g²` on `closedBall z r ⊆ Ω₂ ⋐ Ω₃`. -/
theorem s05_dp_sup_euc {Ω₂ Ω₃ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))} (hle : Ω₂ ≤ Ω₃)
    (h23 : closure (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Ω₃) (hc3 : IsCompact (closure (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))))) {V : Set (EuclideanSpace ℝ (Fin 2))}
    (hV : IsOpen V) (h3V : closure (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ V)
    {A : (EuclideanSpace ℝ (Fin 2)) → Matrix (Fin 2) (Fin 2) ℝ} {β : (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2))} {γ : (EuclideanSpace ℝ (Fin 2)) → ℝ} {lam Lam : ℝ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) V) (hβ : ContDiffOn ℝ ∞ β V)
    (hγ : ContDiffOn ℝ ∞ γ V)
    (hell : TauCeti.PDE.UniformlyEllipticOn (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))) A lam Lam)
    (hγ0 : ∀ x ∈ (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))), 0 ≤ γ x) {z : (EuclideanSpace ℝ (Fin 2))} {r : ℝ} (hr : 0 < r)
    (hK : closedBall z r ⊆ Ω₂) :
    ∃ C : ℝ, ∀ g : (EuclideanSpace ℝ (Fin 2)) → ℝ, ContDiffOn ℝ ∞ g V →
      (∀ x ∈ (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))),
        -(∑ i : Fin 2, fderiv ℝ (fun y => ∑ j : Fin 2, A y i j * fderiv ℝ g y
            (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) +
          ∑ j : Fin 2, β x j * fderiv ℝ g x (EuclideanSpace.single j 1) + γ x * g x = 0) →
      ∀ x ∈ closedBall z r, g x ^ 2 ≤ C * ∫ y in (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))), g y ^ 2 := by
  have h2V : closure (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ V := h23.trans (subset_closure.trans h3V)
  have hc2 : IsCompact (closure (Ω₂ : Set (EuclideanSpace ℝ (Fin 2)))) :=
    hc3.of_isClosed_subset isClosed_closure (h23.trans subset_closure)
  have hs2 : (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ V := subset_closure.trans h2V
  have hAc : ContinuousOn A V :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hA i j).continuousOn
  have hell2 : TauCeti.PDE.UniformlyEllipticOn (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))) A lam Lam := by
    have h := hell
    unfold TauCeti.PDE.UniformlyEllipticOn at h ⊢
    exact ⟨h.1, h.2.1, fun x hx => h.2.2 (hle hx)⟩
  obtain ⟨C₃, -, hC₃⟩ := s05_dp_b3_cacc hle h23 hc3 (hAc.mono h3V) (hβ.continuousOn.mono h3V)
    (hγ.continuousOn.mono h3V) hell hγ0
  obtain ⟨C₅, hC₅⟩ := s05_dp_cg hc2 hell2 (hAc.mono h2V) (hβ.continuousOn.mono h2V)
    (hγ.continuousOn.mono h2V) (fun i j => (hA i j).mono hs2) (hβ.mono hs2) (hγ.mono hs2) hr hK
  refine ⟨C₅ ^ 2 * C₃, fun g hg heq x hx => ?_⟩
  obtain ⟨G, hGv, -, hGw⟩ := s05_dp_b2_weak (f := fun _ => (0 : ℝ)) hc3 hV h3V hA hβ hγ hg
    continuousOn_const heq
  obtain ⟨G', hG'v, -, hG'w⟩ := s05_dp_b2_weak (f := fun _ => (0 : ℝ)) hc2 hV h2V hA hβ hγ hg
    continuousOn_const fun y hy => heq y (hle hy)
  exact s05_dp_sup_pt hle (s05_dp_restrict_eq hle hGv hG'v)
    (hC₃ G fun v => by rw [hGw v]; simp) hGv
    (hC₅ G' (fun v => by rw [hG'w v]; simp) g (hg.continuousOn.mono (hK.trans hs2))
      (ae_restrict_of_ae_restrict_of_subset hK hG'v) x hx)

/-- W-PDE2 B6 helper: `e` transports `∫_{B(w,s)} h²`. -/
theorem s05_dp_int_transport (w : ℂ) (s : ℝ) (hh : ℂ → ℝ) :
    ∫ y in ball (Complex.orthonormalBasisOneI.repr w) s,
        hh (Complex.orthonormalBasisOneI.repr.symm y) ^ 2 = ∫ z in ball w s, hh z ^ 2 := by
  set e := Complex.orthonormalBasisOneI.repr with he
  have h3 := pde_e_measurePreserving.setIntegral_image_emb
    (e.toHomeomorph.measurableEmbedding : MeasurableEmbedding e)
    (fun y => hh (e.symm y) ^ 2) (ball w s)
  rw [LinearIsometryEquiv.image_ball] at h3
  refine h3.trans (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_))
  exact congrArg (fun t => hh t ^ 2) (e.symm_apply_apply z)

/-- W-PDE2 B3+B5 (interior `L² → L^∞` estimate): for `closedBall w (4r) ⊆ D` there is `C` with
`h(x)² ≤ C ∫_{B(w,3r)} h²` on `closedBall w r` for every `h` smooth on `B(w, 4r)` with `𝓛h = 0`
there.  (Caccioppoli, then the closed graph theorem on the closed space of local weak solutions
in `H¹`, whose elements are smooth by P3.) -/
theorem s05_dp_sup_L2 : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (D : Set ℂ) (ε' : ℝ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsAdmissibleOp Ω D ε' aUp bUp c → ∀ (w : ℂ) (r : ℝ), 0 < r → closedBall w (4 * r) ⊆ D →
      ∃ C : ℝ, ∀ h : ℂ → ℝ, ContDiffOn ℝ ∞ h (ball w (4 * r)) →
        (∀ x ∈ ball w (4 * r), ellOp Ω aUp bUp c h x = 0) →
          ∀ x ∈ closedBall w r, h x ^ 2 ≤ C * ∫ y in ball w (3 * r), h y ^ 2 := by
  intro Ω Ωs hJ D ε' aUp bUp c h w r hr hcb
  obtain ⟨A, β, γ, hA, hβ, hγ, -, -, hell, hγ0, hpos, hid⟩ := s05_pde_bridge hJ h
  set e := Complex.orthonormalBasisOneI.repr with he
  have hsb : ∀ {x : EuclideanSpace ℝ (Fin 2)} {s : ℝ}, x ∈ ball (e w) s → e.symm x ∈ ball w s := by
    intro x s hx
    rw [mem_ball] at hx ⊢
    have := e.symm.isometry.dist_eq x (e w)
    rw [LinearIsometryEquiv.symm_apply_apply] at this
    rwa [this]
  have hVD : ball (e w) (4 * r) ⊆ e '' D := fun x hx =>
    ⟨e.symm x, hcb (ball_subset_closedBall (hsb hx)), e.apply_symm_apply x⟩
  set Ω₃ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2)) := ⟨ball (e w) (3 * r), isOpen_ball⟩
  set Ω₂ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2)) := ⟨ball (e w) (2 * r), isOpen_ball⟩
  have hc3e : closure (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))) = closedBall (e w) (3 * r) :=
    closure_ball _ (by positivity)
  have hc2e : closure (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))) = closedBall (e w) (2 * r) :=
    closure_ball _ (by positivity)
  have h3V : closure (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ ball (e w) (4 * r) := by
    rw [hc3e]; exact closedBall_subset_ball (by linarith)
  have h34 : (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ ball (e w) (4 * r) :=
    subset_closure.trans h3V
  have hle : Ω₂ ≤ Ω₃ := SetLike.coe_subset_coe.1 (ball_subset_ball (by linarith))
  have h23 : closure (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Ω₃ := by
    rw [hc2e]; exact closedBall_subset_ball (by linarith)
  have hc3 : IsCompact (closure (Ω₃ : Set (EuclideanSpace ℝ (Fin 2)))) := by
    rw [hc3e]; exact isCompact_closedBall _ _
  have hK : closedBall (e w) r ⊆ Ω₂ := closedBall_subset_ball (by linarith)
  obtain ⟨Lam, hellU, -⟩ := pde_uniformlyEllipticOn (Ω := Ω₃) isBounded_ball
    (by linarith [h.2.1] : ε' < 1)
    (fun i j => ((hA i j).continuousOn.mono (h3V.trans hVD)))
    (fun x hx => hell x (hVD (h34 hx)))
  obtain ⟨C, hC⟩ := s05_dp_sup_euc hle h23 hc3 isOpen_ball h3V (fun i j => (hA i j).mono hVD)
    (hβ.mono hVD) (hγ.mono hVD) hellU (fun x hx => hγ0 x (hVD (h34 hx))) hr hK
  refine ⟨C, fun hh hhs hL x hx => ?_⟩
  have hg : ContDiffOn ℝ ∞ (fun y => hh (e.symm y)) (ball (e w) (4 * r)) :=
    (pde_contDiffOn_comp_symm hhs).mono fun y hy => ⟨e.symm y, hsb hy, e.apply_symm_apply y⟩
  have hex : e x ∈ closedBall (e w) r := by
    rw [mem_closedBall, LinearIsometryEquiv.dist_map]; exact hx
  have h1 := hC (fun y => hh (e.symm y)) hg (fun y hy => by
    have h1 := hid (fun y => hh (e.symm y)) y (hVD (h34 hy))
      ((hg.contDiffAt (isOpen_ball.mem_nhds (h34 hy))).of_le (by simp))
    have hcomp : (fun z => hh (e.symm (e z))) = hh := funext fun z => by
      simp only [LinearIsometryEquiv.symm_apply_apply]
    rw [hcomp, hL _ (hsb (h34 hy)), mul_zero] at h1
    exact h1.symm) (e x) hex
  have hT := s05_dp_int_transport w (3 * r) hh
  simp only [LinearIsometryEquiv.symm_apply_apply] at h1
  rw [← hT]
  exact h1

/-- W-PDE2 B6 helper: a smooth exhaustion of `D` absorbs every compact subset of `D`. -/
theorem s05_dp_absorb_compact {D : Set ℂ} {Dn : ℕ → Set ℂ} (hn : IsSmoothExhaustion D Dn)
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ D) : ∃ N, ∀ n ≥ N, K ⊆ Dn n := by
  have hmono : Monotone Dn := monotone_nat_of_le_succ fun n => subset_closure.trans (hn.2.1 n)
  obtain ⟨N, hN⟩ := hK.elim_directed_cover Dn (fun n => (hn.1 n).1)
    (by rw [hn.2.2]; exact hKD) hmono.directed_le
  exact ⟨N, fun n hn' => hN.trans (hmono hn')⟩

/-- W-PDE2 B6 helper: `𝓛u(w)` depends only on the germ of `u` at `w`. -/
theorem s05_dp_ellOp_congr {Ω : Set ℂ} (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ) {f g : ℂ → ℝ} {w : ℂ} (h : f =ᶠ[𝓝 w] g) :
    ellOp Ω aUp bUp c f w = ellOp Ω aUp bUp c g w := by
  have h1 : fderiv ℝ f =ᶠ[𝓝 w] fderiv ℝ g := h.fderiv
  have h2 : ∀ Y : ℂ, (fun x => fderiv ℝ f x Y) =ᶠ[𝓝 w] fun x => fderiv ℝ g x Y := fun Y => by
    filter_upwards [h1] with x hx
    rw [hx]
  have h3 : ∀ Y X : ℂ, fderiv ℝ (fun x => fderiv ℝ f x Y) w X =
      fderiv ℝ (fun x => fderiv ℝ g x Y) w X := fun Y X => by
    rw [(h2 Y).fderiv_eq]
  simp only [ellOp, s05_rhoHess_eq, h3, h1.eq_of_nhds, h.eq_of_nhds]

/-- W-PDE2 B6 helper (local step): near each `w ∈ D`, the limit `G` of the Dirichlet solutions
agrees with a smooth `φ` with `𝓛φ(w) = F(w)`. Data: `closedBall w (4r) ⊆ Dn n` for `n ≥ N`. -/
theorem s05_dp_local_aux {Ω Ωs D : Set ℂ} (hJ : IsJordanPair Ω Ωs) {ε' : ℝ}
    {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ}
    (h : IsAdmissibleOp Ω D ε' aUp bUp c) {F : ℂ → ℝ} {M : ℝ} (hF : ContDiffOn ℝ ∞ F D)
    (hFM : ∀ w ∈ D, 0 ≤ F w ∧ F w ≤ M) {Dn : ℕ → Set ℂ} (hDn : IsSmoothExhaustion D Dn)
    {un : ℕ → ℂ → ℝ} (hun : ∀ n, IsDirichletSol Ω aUp bUp c (Dn n) F (un n)) {w : ℂ}
    (hw : w ∈ D) {r : ℝ} (hr : 0 < r) (hcb : closedBall w (4 * r) ⊆ D) {N : ℕ}
    (hN : ∀ n ≥ N, closedBall w (4 * r) ⊆ Dn n) :
    ∃ φ : ℂ → ℝ, ContDiffOn ℝ ∞ φ (ball w r) ∧
      EqOn (fun w => ⨆ n, (Dn n).indicator (un n) w) φ (ball w r) ∧
      ellOp Ω aUp bUp c φ w = F w := by
  obtain ⟨A, β, γ, hA, hβ, hγ, hρ, -, hell, hγ0, hpos, hid⟩ := s05_pde_bridge hJ h
  set e := Complex.orthonormalBasisOneI.repr with he
  have hsb : ∀ {x : EuclideanSpace ℝ (Fin 2)} {s : ℝ}, x ∈ ball (e w) s → e.symm x ∈ ball w s := by
    intro x s hx
    rw [mem_ball] at hx ⊢
    have := e.symm.isometry.dist_eq x (e w)
    rw [LinearIsometryEquiv.symm_apply_apply] at this
    rwa [this]
  have hbn : ∀ n, ball w (4 * r) ⊆ Dn (n + N) := fun n =>
    ball_subset_closedBall.trans (hN _ (by omega))
  set V := ball (e w) (4 * r) with hV
  have hVD : V ⊆ e '' D := fun x hx =>
    ⟨e.symm x, hcb (ball_subset_closedBall (hsb hx)), e.apply_symm_apply x⟩
  set g : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ := fun n x => un (n + N) (e.symm x) with hgdef
  set g₀ : EuclideanSpace ℝ (Fin 2) → ℝ := fun x => ⨆ n, (Dn n).indicator (un n) (e.symm x)
    with hg₀
  set f : EuclideanSpace ℝ (Fin 2) → ℝ := fun x =>
    poincareDensity Ω (e.symm x) ^ 2 * F (e.symm x) with hfdef
  have hg : ∀ n, ContDiffOn ℝ ∞ (g n) V := fun n =>
    (pde_contDiffOn_comp_symm (hun (n + N)).1).mono fun x hx =>
      ⟨e.symm x, subset_closure (hbn n (hsb hx)), e.apply_symm_apply x⟩
  have hf : ContDiffOn ℝ ∞ f V := (hρ.mono hVD).mul ((pde_contDiffOn_comp_symm hF).mono hVD)
  set Ω₃ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2)) := ⟨ball (e w) (3 * r), isOpen_ball⟩
  set Ω₂ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2)) := ⟨ball (e w) (2 * r), isOpen_ball⟩
  have hc3e : closure (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))) = closedBall (e w) (3 * r) :=
    closure_ball _ (by positivity)
  have hc2e : closure (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))) = closedBall (e w) (2 * r) :=
    closure_ball _ (by positivity)
  have h3V : closure (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ V := by
    rw [hc3e]; exact closedBall_subset_ball (by linarith)
  have h34 : (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ V := subset_closure.trans h3V
  have heq : ∀ n, ∀ x ∈ (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))),
      -(∑ i : Fin 2, fderiv ℝ (fun y => ∑ j : Fin 2, A y i j * fderiv ℝ (g n) y
          (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) +
        ∑ j : Fin 2, β x j * fderiv ℝ (g n) x (EuclideanSpace.single j 1) + γ x * g n x =
          f x := by
    intro n x hx
    have hx4 : x ∈ V := h34 hx
    have hgc : ContDiffAt ℝ 2 (g n) x :=
      ((hg n).contDiffAt (isOpen_ball.mem_nhds hx4)).of_le (by simp)
    have h1 := hid (g n) x (hVD hx4) hgc
    have hcomp : (fun z => g n (e z)) = un (n + N) := funext fun z => by
      simp only [hgdef, LinearIsometryEquiv.symm_apply_apply]
    rw [hcomp, (hun (n + N)).2.1 _ (hbn n (hsb hx4))] at h1
    exact h1.symm
  have hb : ∀ n, ∀ x ∈ (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))), |g n x| ≤ M / (2 - ε') := by
    intro n x hx
    obtain ⟨h0, h1⟩ := s05_dp_bounds Ω Ωs hJ D ε' aUp bUp c h F M hFM (Dn (n + N))
      (hDn.1 _) (un (n + N)) (hun _) (e.symm x) (subset_closure (hbn n (hsb (h34 hx))))
    rw [abs_of_nonneg h0]
    exact h1
  have hl : ∀ x ∈ (Ω₃ : Set (EuclideanSpace ℝ (Fin 2))),
      Tendsto (fun n => g n x) atTop (𝓝 (g₀ x)) := by
    intro x hx
    have hxD := hbn 0 (hsb (h34 hx))
    have h1 := (s05_dp_tendsto Ω Ωs hJ D ε' aUp bUp c h F M hFM Dn hDn un hun (e.symm x)
      (hcb (ball_subset_closedBall (hsb (h34 hx))))).2.1
    refine ((tendsto_add_atTop_iff_nat N).2 h1).congr fun n => ?_
    exact Set.indicator_of_mem (hbn n (hsb (h34 hx))) _
  obtain ⟨Lam, hellU, -⟩ := pde_uniformlyEllipticOn (Ω := Ω₃) isBounded_ball
    (by linarith [h.2.1] : ε' < 1)
    (fun i j => ((hA i j).continuousOn.mono (h3V.trans hVD)))
    (fun x hx => hell x (hVD (h34 hx)))
  have hle : Ω₂ ≤ Ω₃ := SetLike.coe_subset_coe.1 (ball_subset_ball (by linarith))
  have h23 : closure (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Ω₃ := by
    rw [hc2e]; exact closedBall_subset_ball (by linarith)
  have hc3 : IsCompact (closure (Ω₃ : Set (EuclideanSpace ℝ (Fin 2)))) := by
    rw [hc3e]; exact isCompact_closedBall _ _
  have hK : closedBall (e w) r ⊆ Ω₂ := closedBall_subset_ball (by linarith)
  obtain ⟨g', hg', hL', hEq⟩ := s05_dp_core hle h23 hc3 isOpen_ball h3V
    (fun i j => (hA i j).mono hVD) (hβ.mono hVD) (hγ.mono hVD) hf hellU
    (fun x hx => hγ0 x (hVD (h34 hx))) hg heq hb hl hr hK
  have hmap : ∀ z ∈ ball w r, e z ∈ ball (e w) r := fun z hz => by
    rw [mem_ball, LinearIsometryEquiv.dist_map]; exact hz
  refine ⟨fun z => g' (e z), hg'.comp e.contDiff.contDiffOn fun z hz =>
    ball_subset_ball (by linarith) (hmap z hz), fun z hz => ?_, ?_⟩
  · have := hEq (ball_subset_closedBall (hmap z hz))
    simp only [hg₀, LinearIsometryEquiv.symm_apply_apply] at this
    exact this.symm
  · have hw2 : e w ∈ (Ω₂ : Set (EuclideanSpace ℝ (Fin 2))) := mem_ball_self (by linarith)
    have hwD : e w ∈ e '' D := ⟨w, hw, rfl⟩
    have h1 := hid g' (e w) hwD
      ((hg'.contDiffAt (Ω₂.isOpen.mem_nhds hw2)).of_le (by simp))
    rw [hL' _ hw2] at h1
    simp only [hfdef, LinearIsometryEquiv.symm_apply_apply] at h1
    have hp : poincareDensity Ω w ≠ 0 := by
      have := hpos _ hwD
      simp only [LinearIsometryEquiv.symm_apply_apply] at this
      exact this.ne'
    exact mul_left_cancel₀ (pow_ne_zero 2 hp) h1

/-- W-PDE2 B6: the limit along a smooth exhaustion is smooth on `D` and solves `𝓛G = F`. -/
theorem s05_dp_limit : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (D : Set ℂ) (ε' : ℝ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsAdmissibleOp Ω D ε' aUp bUp c → ∀ (F : ℂ → ℝ) (M : ℝ), ContDiffOn ℝ ∞ F D →
      (∀ w ∈ D, 0 ≤ F w ∧ F w ≤ M) → ∀ Dn : ℕ → Set ℂ, IsSmoothExhaustion D Dn →
        ∀ un : ℕ → ℂ → ℝ, (∀ n, IsDirichletSol Ω aUp bUp c (Dn n) F (un n)) →
          ContDiffOn ℝ ∞ (fun w => ⨆ n, (Dn n).indicator (un n) w) D ∧
          ∀ w ∈ D, ellOp Ω aUp bUp c (fun w => ⨆ n, (Dn n).indicator (un n) w) w = F w := by
  intro Ω Ωs hJ D ε' aUp bUp c h F M hF hFM Dn hDn un hun
  have hloc : ∀ w ∈ D, ∃ r > 0, ∃ φ : ℂ → ℝ, ContDiffOn ℝ ∞ φ (ball w r) ∧
      EqOn (fun w => ⨆ n, (Dn n).indicator (un n) w) φ (ball w r) ∧
      ellOp Ω aUp bUp c φ w = F w := by
    intro w hw
    obtain ⟨R, hR, hRD⟩ := Metric.isOpen_iff.1 h.2.2.1 w hw
    have hr : 0 < R / 8 := by positivity
    have hcb : closedBall w (4 * (R / 8)) ⊆ D :=
      (closedBall_subset_ball (by linarith)).trans hRD
    obtain ⟨N, hN⟩ := s05_dp_absorb_compact hDn (isCompact_closedBall w _) hcb
    exact ⟨R / 8, hr, s05_dp_local_aux hJ h hF hFM hDn hun hw hr hcb hN⟩
  refine ⟨contDiffOn_of_locally_contDiffOn fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨r, hr, φ, hφ, hEq, -⟩ := hloc w hw
    exact ⟨ball w r, isOpen_ball, mem_ball_self hr,
      (hφ.congr fun z hz => hEq hz).mono inter_subset_right⟩
  · obtain ⟨r, hr, φ, -, hEq, hL⟩ := hloc w hw
    rw [s05_dp_ellOp_congr aUp bUp c (hEq.eventuallyEq_of_mem (ball_mem_nhds w hr)), hL]

/-- W-PDE2 C1: one smooth exhaustion with Dirichlet solutions yields the Dirichlet inverse
`𝒢_D F`, with `0 ≤ 𝒢_D F ≤ M/(2 - ε')` (the second conjunct of `prop_dirichlet_a`). -/
theorem s05_dp_inverse : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (D : Set ℂ) (ε' : ℝ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsAdmissibleOp Ω D ε' aUp bUp c → ∀ (F : ℂ → ℝ) (M : ℝ), ContDiffOn ℝ ∞ F D →
      (∀ w ∈ D, 0 ≤ F w ∧ F w ≤ M) → ∀ Dn : ℕ → Set ℂ, IsSmoothExhaustion D Dn →
        ∀ un : ℕ → ℂ → ℝ, (∀ n, IsDirichletSol Ω aUp bUp c (Dn n) F (un n)) →
          ∃ G : ℂ → ℝ, IsDirichletInverse Ω aUp bUp c D F G ∧
            ∀ w ∈ D, 0 ≤ G w ∧ G w ≤ M / (2 - ε') := by
  intro Ω Ωs hJ D ε' aUp bUp c h F M hF hFM Dn hDn un hun
  obtain ⟨hs, hL⟩ := s05_dp_limit Ω Ωs hJ D ε' aUp bUp c h F M hF hFM Dn hDn un hun
  refine ⟨fun w => ⨆ n, (Dn n).indicator (un n) w,
    ⟨hs.of_le (by simp), hL, fun Dm hDm um hum w hw => ?_⟩, fun w hw => ?_⟩
  · obtain ⟨hmo, ht, -, -⟩ :=
      s05_dp_tendsto Ω Ωs hJ D ε' aUp bUp c h F M hFM Dm hDm um hum w hw
    refine ⟨hmo, ?_⟩
    rw [show (fun w => ⨆ n, (Dn n).indicator (un n) w) w = ⨆ m, (Dm m).indicator (um m) w from
      s05_dp_indep Ω Ωs hJ D ε' aUp bUp c h F M hFM Dn Dm hDn hDm un um hun hum w hw]
    exact ht
  · obtain ⟨-, -, h0, hK⟩ := s05_dp_tendsto Ω Ωs hJ D ε' aUp bUp c h F M hFM Dn hDn un hun w hw
    exact ⟨h0, hK⟩

/-- **Proposition 5.5 (a)** (Dirichlet inverse, `prop:dirichlet`, sec05-upper.tex:240).  Let `𝓛`
be `ε'`-admissible on the open set `D`, `F` smooth on `D` with `0 ≤ F ≤ M`.  There is
`𝒢_D F ∈ C²(D)` with `𝓛(𝒢_D F) = F` and `0 ≤ 𝒢_D F ≤ M/(2-ε')`; it is the increasing limit of the
solutions of the Dirichlet problems on any smooth exhaustion of `D` (which exist), and does not
depend on the exhaustion. -/
theorem prop_dirichlet_a : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (D : Set ℂ) (ε' : ℝ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsAdmissibleOp Ω D ε' aUp bUp c → ∀ (F : ℂ → ℝ) (M : ℝ), ContDiffOn ℝ ∞ F D →
      (∀ w ∈ D, 0 ≤ F w ∧ F w ≤ M) →
        (∀ Dn : ℕ → Set ℂ, IsSmoothExhaustion D Dn →
          ∃ un : ℕ → ℂ → ℝ, ∀ n, IsDirichletSol Ω aUp bUp c (Dn n) F (un n)) ∧
        ∃ G : ℂ → ℝ, IsDirichletInverse Ω aUp bUp c D F G ∧
          ∀ w ∈ D, 0 ≤ G w ∧ G w ≤ M / (2 - ε') := by
  intro Ω Ωs hJ D ε' aUp bUp c h F M hF hFM
  have hsol : ∀ Dn : ℕ → Set ℂ, IsSmoothExhaustion D Dn →
      ∃ un : ℕ → ℂ → ℝ, ∀ n, IsDirichletSol Ω aUp bUp c (Dn n) F (un n) := fun Dn hDn =>
    ⟨fun n => (s05_dirichlet_sol Ω Ωs hJ D ε' aUp bUp c h (Dn n) (hDn.1 n) F hF).choose,
      fun n => (s05_dirichlet_sol Ω Ωs hJ D ε' aUp bUp c h (Dn n) (hDn.1 n) F hF).choose_spec⟩
  refine ⟨hsol, ?_⟩
  obtain ⟨Dn, hDn⟩ := s05_smooth_exhaustion D h.2.2.1
  obtain ⟨un, hun⟩ := hsol Dn hDn
  exact s05_dp_inverse Ω Ωs hJ D ε' aUp bUp c h F M hF hFM Dn hDn un hun

/-- **W4** (`lem:weighted-dirichlet`, sec09-ambient.tex; the proof of Proposition 5.5 (b) with `k_p`
replaced by `κ`).  Let `𝓛` be `ε'`-admissible on `D`, `F` smooth with `0 ≤ F ≤ M` on `D`, and
`G = 𝒢_D F`.  If `κ > 0` is smooth on `D` with `𝓛*κ ≥ aκ` on `D` for some `a > 0`, then
`∫_D κ 𝒢_D F dâ ≤ a⁻¹ ∫_D κ F dâ`, as extended integrals. -/
theorem s05_weighted_dirichlet : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (D : Set ℂ) (ε' : ℝ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsAdmissibleOp Ω D ε' aUp bUp c → ∀ (F : ℂ → ℝ) (M : ℝ), ContDiffOn ℝ ∞ F D →
      (∀ w ∈ D, 0 ≤ F w ∧ F w ≤ M) → ∀ G : ℂ → ℝ, IsDirichletInverse Ω aUp bUp c D F G →
        ∀ (κ : ℂ → ℝ) (a : ℝ), 0 < a → ContDiffOn ℝ ∞ κ D → (∀ w ∈ D, 0 < κ w) →
          (∀ w ∈ D, a * κ w ≤ ellOpAdj Ω aUp bUp c κ w) →
            ∫⁻ w in D, ENNReal.ofReal (κ w * G w) ∂hypArea Ω ≤
              ENNReal.ofReal (1 / a) * ∫⁻ w in D, ENNReal.ofReal (κ w * F w) ∂hypArea Ω := by
  intro Ω Ωs hJ D ε' aUp bUp c h F M hF hFM G hG κ a ha hκ hκp hκa
  have hDo : IsOpen D := h.2.2.1
  have hDΩ : D ⊆ Ω := h.2.2.2.1
  have hop : IsSmoothOp D aUp bUp c := h.2.2.2.2.1
  obtain ⟨Dn, hE⟩ := s05_smooth_exhaustion D hDo
  obtain ⟨un, hun⟩ := (prop_dirichlet_a Ω Ωs hJ D ε' aUp bUp c h F M hF hFM).1 Dn hE
  have hlim := hG.2.2 Dn hE un hun
  refine s05_wd_fatou (μ := hypArea Ω) (f := fun n w => κ w * un n w) hDo (fun n => (hE.1 n).1)
    (fun n => subset_closure.trans (hE.1 n).2.2.1) (fun n => ?_) (fun w hw => ?_) (fun n => ?_)
  · exact (hκ.continuousOn.mono (subset_closure.trans (hE.1 n).2.2.1)).mul
      ((hun n).1.continuousOn.mono subset_closure)
  · show Tendsto (fun n => (Dn n).indicator (fun x => κ x * un n x) w) atTop (𝓝 (κ w * G w))
    simp only [indicator_mul_right]
    exact ((hlim w hw).2).const_mul (κ w)
  -- the bound on `Dₙ`
  obtain ⟨hDo', hKc, hKD, -⟩ := hE.1 n
  have hsub : Dn n ⊆ D := subset_closure.trans hKD
  have hm : MeasurableSet (Dn n) := hDo'.measurableSet
  have hadm := s05_wd_admissible_mono h hDo' hsub
  obtain ⟨z, hz⟩ := s05_dual_dirichlet_sol Ω Ωs hJ D ε' aUp bUp c h (Dn n) (hE.1 n) κ hκ
  have hzA : ∀ w ∈ Dn n, ellOpAdj Ω aUp bUp c z w = κ w := hz.2.1
  have hu := hun n
  have hκc : ContDiffOn ℝ ∞ κ (closure (Dn n)) := hκ.mono hKD
  have hFc : ContDiffOn ℝ ∞ F (closure (Dn n)) := hF.mono hKD
  have hcd : ∀ v : ℂ → ℝ, ContDiffOn ℝ ∞ v (closure (Dn n)) → ∀ w ∈ Dn n, ContDiffAt ℝ 2 v w :=
    fun v hv w hw => ((hv.mono subset_closure).contDiffAt (hDo'.mem_nhds hw)).of_le (by simp)
  have hlin : ∀ f g : ℂ → ℝ, ContDiffOn ℝ ∞ f (closure (Dn n)) →
      ContDiffOn ℝ ∞ g (closure (Dn n)) → ∀ s : ℝ,
        ContinuousOn (fun x => f x - s * g x) (closure (Dn n)) ∧
          ContDiffOn ℝ 2 (fun x => f x - s * g x) (Dn n) := by
    intro f g hf hg s
    have e : ContDiffOn ℝ ∞ (fun x => f x - s * g x) (closure (Dn n)) :=
      hf.sub (contDiffOn_const.mul hg)
    exact ⟨e.continuousOn, (e.mono subset_closure).of_le (by simp)⟩
  -- the two comparison principles on `Dₙ` for `f - s g`
  have hcmp : ∀ f g : ℂ → ℝ, ContDiffOn ℝ ∞ f (closure (Dn n)) →
      ContDiffOn ℝ ∞ g (closure (Dn n)) → ∀ s : ℝ,
        (∀ w ∈ frontier (Dn n), f w - s * g w ≤ 0) →
          ((∀ w ∈ Dn n, ellOp Ω aUp bUp c f w - s * ellOp Ω aUp bUp c g w ≤ 0) →
              ∀ w ∈ Dn n, f w - s * g w ≤ 0) ∧
            ((∀ w ∈ Dn n, ellOpAdj Ω aUp bUp c f w - s * ellOpAdj Ω aUp bUp c g w ≤ 0) →
              ∀ w ∈ Dn n, f w - s * g w ≤ 0) := by
    intro f g hf hg s hb
    obtain ⟨hv0, hv2⟩ := hlin f g hf hg s
    have hC := lem_comparison Ω Ωs hJ (Dn n) ε' aUp bUp c hadm (fun x => f x - s * g x) hv2
      (s05_wd_bdd hKc hv0) (s05_wd_bdry hv0 hb)
    refine ⟨fun hL => hC.1 fun w hw => ?_, fun hL => hC.2 fun w hw => ?_⟩
    · rw [s05_ellOp_sub aUp bUp c (hcd f hf w hw) (hcd g hg w hw) s]
      exact hL w hw
    · have e : ellOpAdj Ω aUp bUp c (fun x => f x - s * g x) w =
          ellOpAdj Ω aUp bUp c f w - s * ellOpAdj Ω aUp bUp c g w :=
        s05_ellOp_sub aUp _ _ (hcd f hf w hw) (hcd g hg w hw) s
      rw [e]
      exact hL w hw
  -- `u_n ≥ 0`, `z ≥ 0`, `z ≤ κ/a` on `Dₙ`
  have hu0 : ∀ w ∈ Dn n, 0 ≤ un n w := by
    intro w hw
    have := (hcmp (un n) (un n) hu.1 hu.1 2 (fun x hx => by rw [hu.2.2 x hx]; norm_num)).1
      (fun x hx => by rw [hu.2.1 x hx]; linarith [(hFM x (hsub hx)).1]) w hw
    linarith
  have hz0 : ∀ w ∈ Dn n, 0 ≤ z w := by
    intro w hw
    have := (hcmp z z hz.1 hz.1 2 (fun x hx => by rw [hz.2.2 x hx]; norm_num)).2
      (fun x hx => by rw [hzA x hx]; linarith [hκp x (hsub hx)]) w hw
    linarith
  have hzκ : ∀ w ∈ Dn n, z w ≤ 1 / a * κ w := by
    intro w hw
    have := (hcmp z κ hz.1 hκc (1 / a) (fun x hx => by
        rw [hz.2.2 x hx, zero_sub, neg_nonpos]
        exact (mul_pos (one_div_pos.mpr ha) (hκp x (hKD (frontier_subset_closure hx)))).le)).2
      (fun x hx => by
        rw [hzA x hx]
        have h1 := hκa x (hsub hx)
        have h2 : κ x ≤ 1 / a * ellOpAdj Ω aUp bUp c κ x := by
          rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ha]
          linarith
        linarith) w hw
    linarith
  -- Green's formula on `Dₙ`
  have hgr := eq_green_formula Ω Ωs hJ D aUp bUp c hDo hDΩ hop (Dn n) (hE.1 n) (un n) z
    (hu.1.of_le (by simp)) (hz.1.of_le (by simp)) (fun w hw => ⟨hu.2.2 w hw, hz.2.2 w hw⟩)
  have hgr' : ∫ w in Dn n, κ w * un n w ∂hypArea Ω = ∫ w in Dn n, z w * F w ∂hypArea Ω := by
    rw [setIntegral_congr_fun hm (fun w hw => by
        show κ w * un n w = un n w * ellOpAdj Ω aUp bUp c z w
        rw [hzA w hw, mul_comm]),
      ← hgr, setIntegral_congr_fun hm (fun w hw => by
        show z w * ellOp Ω aUp bUp c (un n) w = z w * F w
        rw [hu.2.1 w hw])]
  have hKΩ : closure (Dn n) ⊆ Ω := hKD.trans hDΩ
  have hI1 : IntegrableOn (fun w => κ w * un n w) (Dn n) (hypArea Ω) :=
    s05_wd_integrableOn hJ hKc hKΩ (hκc.continuousOn.mul hu.1.continuousOn)
  have hI2 : IntegrableOn (fun w => z w * F w) (Dn n) (hypArea Ω) :=
    s05_wd_integrableOn hJ hKc hKΩ (hz.1.continuousOn.mul hFc.continuousOn)
  calc ∫⁻ w in Dn n, ENNReal.ofReal (κ w * un n w) ∂hypArea Ω
      = ENNReal.ofReal (∫ w in Dn n, κ w * un n w ∂hypArea Ω) :=
        (ofReal_integral_eq_lintegral_ofReal hI1 (ae_restrict_of_forall_mem hm fun w hw =>
          mul_nonneg (hκp w (hsub hw)).le (hu0 w hw))).symm
    _ = ENNReal.ofReal (∫ w in Dn n, z w * F w ∂hypArea Ω) := by rw [hgr']
    _ = ∫⁻ w in Dn n, ENNReal.ofReal (z w * F w) ∂hypArea Ω :=
        ofReal_integral_eq_lintegral_ofReal hI2 (ae_restrict_of_forall_mem hm fun w hw =>
          mul_nonneg (hz0 w hw) (hFM w (hsub hw)).1)
    _ ≤ ∫⁻ w in Dn n, ENNReal.ofReal (1 / a) * ENNReal.ofReal (κ w * F w) ∂hypArea Ω := by
        refine setLIntegral_mono' hm fun w hw => ?_
        rw [← ENNReal.ofReal_mul (one_div_pos.mpr ha).le]
        refine ENNReal.ofReal_le_ofReal ?_
        calc z w * F w ≤ 1 / a * κ w * F w :=
              mul_le_mul_of_nonneg_right (hzκ w hw) (hFM w (hsub hw)).1
          _ = 1 / a * (κ w * F w) := by ring
    _ = ENNReal.ofReal (1 / a) * ∫⁻ w in Dn n, ENNReal.ofReal (κ w * F w) ∂hypArea Ω :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (1 / a) * ∫⁻ w in D, ENNReal.ofReal (κ w * F w) ∂hypArea Ω := by
        gcongr

/-- W4 helper (for `prop_dirichlet_b`): `k_p` is smooth on `Ω`. -/
theorem s05_wd_kernel_smooth {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {p : ℂ} (hp : p ∈ Ω) :
    ContDiffOn ℝ ∞ (intrKernel Ω p) Ω := by
  have hΩ := s05_jordan_isOpen hJ
  obtain ⟨ψ, hψ, -, -, hK, -⟩ := s05_kernel_riemann hJ hp
  have h1 : ContDiffOn ℝ ∞ ψ Ω := (hψ.contDiffOn hΩ).restrict_scalars ℝ
  have h2 : ContDiffOn ℝ ∞ (fun x => 1 - ‖ψ x‖ ^ 2) Ω :=
    contDiffOn_const.sub ((contDiff_norm_sq ℝ).comp_contDiffOn h1)
  exact h2.congr fun x hx => hK x hx

/-- W4 helper (for `prop_dirichlet_b`): `k_p > 0`. -/
theorem s05_wd_kernel_pos (Ω : Set ℂ) (p w : ℂ) : 0 < intrKernel Ω p w := by
  show 0 < ((Real.cosh (poincareDist Ω p w / 2))⁻¹) ^ 2
  exact pow_pos (inv_pos.mpr (Real.cosh_pos _)) 2

/-- **Proposition 5.5 (b)** (`prop:dirichlet`, sec05-upper.tex:248).  With `a₀ = 2 - C₀ε'`,
`∫_D k_p 𝒢_D F dâ ≤ a₀⁻¹ ∫_D k_p F dâ` (5.12) for every `p ∈ Ω`, as extended integrals. -/
theorem prop_dirichlet_b : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (D : Set ℂ) (ε' : ℝ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsAdmissibleOp Ω D ε' aUp bUp c → ∀ (F : ℂ → ℝ) (M : ℝ), ContDiffOn ℝ ∞ F D →
      (∀ w ∈ D, 0 ≤ F w ∧ F w ≤ M) → ∀ G : ℂ → ℝ, IsDirichletInverse Ω aUp bUp c D F G →
        ∀ p ∈ Ω, ∫⁻ w in D, ENNReal.ofReal (intrKernel Ω p w * G w) ∂hypArea Ω ≤
          ENNReal.ofReal (1 / (2 - 11 * ε')) *
            ∫⁻ w in D, ENNReal.ofReal (intrKernel Ω p w * F w) ∂hypArea Ω := by
  intro Ω Ωs hJ D ε' aUp bUp c h F M hF hFM G hG p hp
  have ha : 0 < 2 - 11 * ε' := by linarith [h.2.1]
  exact s05_weighted_dirichlet Ω Ωs hJ D ε' aUp bUp c h F M hF hFM G hG (intrKernel Ω p) _ ha
    ((s05_wd_kernel_smooth hJ hp).mono h.2.2.2.1) (fun w _ => s05_wd_kernel_pos Ω p w)
    (fun w hw => ((lem_test_functions_a Ω Ωs hJ D ε' aUp bUp c h p hp).2 w hw).1)

/-- (c) helper: a compact subset of `D` lies in a single set of a smooth exhaustion of `D`. -/
theorem s05_dc_cover {D : Set ℂ} {Dn : ℕ → Set ℂ} (hE : IsSmoothExhaustion D Dn) {K : Set ℂ}
    (hK : IsCompact K) (hKD : K ⊆ D) : ∃ n, K ⊆ Dn n := by
  obtain ⟨hS, hcl, hU⟩ := hE
  have hmono : Monotone Dn := monotone_nat_of_le_succ fun n => subset_closure.trans (hcl n)
  exact hK.elim_directed_cover Dn (fun n => (hS n).1) (hKD.trans hU.ge) hmono.directed_le

/-- (c) helper (uniqueness): a bounded `C²` solution of `𝓛u = F` on `Ω` equals `𝒢_Ω F`. -/
theorem s05_dc_unique {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {ε' : ℝ}
    {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ}
    (h : IsAdmissibleOp Ω Ω ε' aUp bUp c) {F : ℂ → ℝ} {M : ℝ} (hF : ContDiffOn ℝ ∞ F Ω)
    (hFM : ∀ w ∈ Ω, 0 ≤ F w ∧ F w ≤ M) {G : ℂ → ℝ} (hG : IsDirichletInverse Ω aUp bUp c Ω F G)
    {u : ℂ → ℝ} (hu : ContDiffOn ℝ 2 u Ω) (hub : ∃ B : ℝ, ∀ w ∈ Ω, |u w| ≤ B)
    (hLu : ∀ w ∈ Ω, ellOp Ω aUp bUp c u w = F w) : ∀ w ∈ Ω, u w = G w := by
  have hΩ := s05_jordan_isOpen hJ
  obtain ⟨Dn, hE⟩ := s05_smooth_exhaustion Ω hΩ
  have hA := prop_dirichlet_a Ω Ωs hJ Ω ε' aUp bUp c h F M hF hFM
  obtain ⟨un, hun⟩ := hA.1 Dn hE
  obtain ⟨G', hG', hG'b⟩ := hA.2
  -- `G` and the `G'` of `prop_dirichlet_a` are limits of the same Dirichlet solutions
  have hGb : ∀ x ∈ Ω, 0 ≤ G x ∧ G x ≤ M / (2 - ε') := by
    intro x hx
    rw [tendsto_nhds_unique (hG.2.2 Dn hE un hun x hx).2 (hG'.2.2 Dn hE un hun x hx).2]
    exact hG'b x hx
  -- the boundary hypothesis of `lem_comparison` on `D = Ω` is vacuous: `∂Ω ∩ Ω = ∅`
  have hfr : ∀ v : ℂ → ℝ, ∀ wb ∈ frontier Ω ∩ Ω, ∀ δ : ℝ, 0 < δ → ∀ᶠ w in 𝓝[Ω] wb, v w ≤ δ := by
    intro v wb hwb
    have h1 := hwb.1
    rw [hΩ.frontier_eq] at h1
    exact absurd hwb.2 h1.2
  -- comparison on `Ω` for `f - g` with `𝓛f = 𝓛g`, given an upper bound `C` of `f - g`
  have hcmp : ∀ f g : ℂ → ℝ, ContDiffOn ℝ 2 f Ω → ContDiffOn ℝ 2 g Ω →
      (∀ x ∈ Ω, ellOp Ω aUp bUp c f x = ellOp Ω aUp bUp c g x) → ∀ C : ℝ,
        (∀ x ∈ Ω, f x - g x ≤ C) → ∀ x ∈ Ω, f x ≤ g x := by
    intro f g hf hg hL C hC x hx
    have hv : ContDiffOn ℝ 2 (fun y => f y - 1 * g y) Ω := hf.sub (contDiffOn_const.mul hg)
    have hbd : BddAbove ((fun y => f y - 1 * g y) '' Ω) := by
      refine ⟨C, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      have := hC y hy
      show f y - 1 * g y ≤ C
      linarith
    have h1 : f x - 1 * g x ≤ 0 :=
      (lem_comparison Ω Ωs hJ Ω ε' aUp bUp c h _ hv hbd (hfr _)).1 (fun y hy => by
        rw [s05_ellOp_sub aUp bUp c (hf.contDiffAt (hΩ.mem_nhds hy))
          (hg.contDiffAt (hΩ.mem_nhds hy)) 1, hL y hy]
        linarith) x hx
    linarith
  have hL : ∀ x ∈ Ω, ellOp Ω aUp bUp c u x = ellOp Ω aUp bUp c G x := fun x hx => by
    rw [hLu x hx, hG.2.1 x hx]
  -- `BddAbove` of `±(u - G)` needs both bounds: `|u| ≤ B` and `0 ≤ G ≤ M/(2-ε')`
  obtain ⟨B, hB⟩ := hub
  intro w hw
  have h1 := hcmp u G hu hG.1 hL B (fun x hx => by
    linarith [(abs_le.mp (hB x hx)).2, (hGb x hx).1]) w hw
  have h2 := hcmp G u hG.1 hu (fun x hx => (hL x hx).symm) (M / (2 - ε') + B) (fun x hx => by
    linarith [(abs_le.mp (hB x hx)).1, (hGb x hx).2]) w hw
  exact le_antisymm h1 h2

/-- (c) helper ((5.13) on one set): if `D' ⋐ Ω` is smooth, `u` solves the Dirichlet problem
`𝓛u = F` on `D'` with `u ≤ G` there, and `k_p ≤ s` on `∂D'` (`s ≥ 0`), then
`∫_{D'} (k_p - s)⁺ F / (3 + C₀ε') dâ ≤ ∫_Ω k_p G dâ` (comparison for `𝓛*` against the dual
Dirichlet solution `z` of `𝓛*z = k_p`, and Green's formula). -/
theorem s05_dc_set {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {ε' : ℝ}
    {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ}
    (h : IsAdmissibleOp Ω Ω ε' aUp bUp c) {F : ℂ → ℝ} (hF : ContDiffOn ℝ ∞ F Ω)
    (hF0 : ∀ w ∈ Ω, 0 ≤ F w) {G : ℂ → ℝ} {D' : Set ℂ} (hD' : IsSmoothRelCompactIn D' Ω)
    {u : ℂ → ℝ} (hu : IsDirichletSol Ω aUp bUp c D' F u) (huG : ∀ w ∈ D', u w ≤ G w)
    {p : ℂ} (hp : p ∈ Ω) {s : ℝ} (hs : 0 ≤ s)
    (hfr : ∀ w ∈ frontier D', intrKernel Ω p w ≤ s) :
    ∫⁻ w in D', ENNReal.ofReal (1 / (3 + 11 * ε') * (max (intrKernel Ω p w - s) 0 * F w))
        ∂hypArea Ω ≤
      ∫⁻ w in Ω, ENNReal.ofReal (intrKernel Ω p w * G w) ∂hypArea Ω := by
  have hΩ := s05_jordan_isOpen hJ
  have hop : IsSmoothOp Ω aUp bUp c := h.2.2.2.2.1
  have hDo' : IsOpen D' := hD'.1
  have hKc : IsCompact (closure D') := hD'.2.1
  have hKD : closure D' ⊆ Ω := hD'.2.2.1
  have hsub : D' ⊆ Ω := subset_closure.trans hKD
  have hm : MeasurableSet D' := hDo'.measurableSet
  have hadm := s05_wd_admissible_mono h hDo' hsub
  have hk := s05_wd_kernel_smooth hJ hp
  have hkp : ∀ w, 0 < intrKernel Ω p w := s05_wd_kernel_pos Ω p
  have ha : 0 < 3 + 11 * ε' := by linarith [h.1]
  obtain ⟨z, hz⟩ := s05_dual_dirichlet_sol Ω Ωs hJ Ω ε' aUp bUp c h D' hD' (intrKernel Ω p) hk
  have hzA : ∀ w ∈ D', ellOpAdj Ω aUp bUp c z w = intrKernel Ω p w := hz.2.1
  have hkc : ContDiffOn ℝ ∞ (intrKernel Ω p) (closure D') := hk.mono hKD
  have hFc : ContDiffOn ℝ ∞ F (closure D') := hF.mono hKD
  have hcd : ∀ v : ℂ → ℝ, ContDiffOn ℝ ∞ v (closure D') → ∀ w ∈ D', ContDiffAt ℝ 2 v w :=
    fun v hv w hw => ((hv.mono subset_closure).contDiffAt (hDo'.mem_nhds hw)).of_le (by simp)
  have hlin : ∀ f g : ℂ → ℝ, ContDiffOn ℝ ∞ f (closure D') →
      ContDiffOn ℝ ∞ g (closure D') → ∀ s : ℝ,
        ContinuousOn (fun x => f x - s * g x) (closure D') ∧
          ContDiffOn ℝ 2 (fun x => f x - s * g x) D' := by
    intro f g hf hg s
    have e : ContDiffOn ℝ ∞ (fun x => f x - s * g x) (closure D') :=
      hf.sub (contDiffOn_const.mul hg)
    exact ⟨e.continuousOn, (e.mono subset_closure).of_le (by simp)⟩
  -- the two comparison principles on `D'` for `f - t g` (as in `s05_weighted_dirichlet`)
  have hcmp : ∀ f g : ℂ → ℝ, ContDiffOn ℝ ∞ f (closure D') →
      ContDiffOn ℝ ∞ g (closure D') → ∀ t : ℝ,
        (∀ w ∈ frontier D', f w - t * g w ≤ 0) →
          ((∀ w ∈ D', ellOp Ω aUp bUp c f w - t * ellOp Ω aUp bUp c g w ≤ 0) →
              ∀ w ∈ D', f w - t * g w ≤ 0) ∧
            ((∀ w ∈ D', ellOpAdj Ω aUp bUp c f w - t * ellOpAdj Ω aUp bUp c g w ≤ 0) →
              ∀ w ∈ D', f w - t * g w ≤ 0) := by
    intro f g hf hg t hb
    obtain ⟨hv0, hv2⟩ := hlin f g hf hg t
    have hC := lem_comparison Ω Ωs hJ D' ε' aUp bUp c hadm (fun x => f x - t * g x) hv2
      (s05_wd_bdd hKc hv0) (s05_wd_bdry hv0 hb)
    refine ⟨fun hL => hC.1 fun w hw => ?_, fun hL => hC.2 fun w hw => ?_⟩
    · rw [s05_ellOp_sub aUp bUp c (hcd f hf w hw) (hcd g hg w hw) t]
      exact hL w hw
    · have e : ellOpAdj Ω aUp bUp c (fun x => f x - t * g x) w =
          ellOpAdj Ω aUp bUp c f w - t * ellOpAdj Ω aUp bUp c g w :=
        s05_ellOp_sub aUp _ _ (hcd f hf w hw) (hcd g hg w hw) t
      rw [e]
      exact hL w hw
  -- `u ≥ 0`, `z ≥ 0` on `D'`
  have hu0 : ∀ w ∈ D', 0 ≤ u w := by
    intro w hw
    have := (hcmp u u hu.1 hu.1 2 (fun x hx => by rw [hu.2.2 x hx]; norm_num)).1
      (fun x hx => by rw [hu.2.1 x hx]; linarith [hF0 x (hsub hx)]) w hw
    linarith
  have hz0 : ∀ w ∈ D', 0 ≤ z w := by
    intro w hw
    have := (hcmp z z hz.1 hz.1 2 (fun x hx => by rw [hz.2.2 x hx]; norm_num)).2
      (fun x hx => by rw [hzA x hx]; linarith [hkp x]) w hw
    linarith
  -- `k_p - s ≤ (3 + C₀ε') z` on `D'`: `𝓛*(k_p - s - (3 + C₀ε') z) ≤ -s c* ≤ 0`, `≤ 0` on `∂D'`
  have hzk : ∀ w ∈ D', intrKernel Ω p w - s * 1 - (3 + 11 * ε') * z w ≤ 0 := by
    refine (hcmp (fun x => intrKernel Ω p x - s * 1) z
      (hkc.sub (contDiffOn_const.mul contDiffOn_const)) hz.1 (3 + 11 * ε')
      (fun x hx => ?_)).2 (fun x hx => ?_)
    · show intrKernel Ω p x - s * 1 - (3 + 11 * ε') * z x ≤ 0
      rw [hz.2.2 x hx, mul_zero, sub_zero]
      linarith [hfr x hx]
    · have hxΩ := hsub hx
      have e1 : ellOpAdj Ω aUp bUp c (fun y => intrKernel Ω p y - s * 1) x =
          ellOpAdj Ω aUp bUp c (intrKernel Ω p) x -
            s * ellOpAdj Ω aUp bUp c (fun _ => (1 : ℝ)) x :=
        s05_ellOp_sub aUp _ _ (hcd _ hkc x hx) contDiffAt_const s
      have e2 : ellOpAdj Ω aUp bUp c (fun _ => (1 : ℝ)) x = adjCoeffC Ω aUp bUp c x :=
        s05_ellOp_const_one Ω aUp _ _ x
      rw [e1, e2, hzA x hx]
      have h1 := ((lem_test_functions_a Ω Ωs hJ Ω ε' aUp bUp c h p hp).2 x hxΩ).2
      have h2 := abs_le.mp ((eq_adjoint Ω Ωs hJ Ω ε' aUp bUp c h).2 x hxΩ).1
      have h3 : 0 ≤ s * adjCoeffC Ω aUp bUp c x :=
        mul_nonneg hs (by linarith [h2.1, h.2.1, h.1])
      linarith
  -- pointwise: `(3 + C₀ε')⁻¹ (k_p - s)⁺ F ≤ z F`
  have hpt : ∀ w ∈ D',
      1 / (3 + 11 * ε') * (max (intrKernel Ω p w - s) 0 * F w) ≤ z w * F w := by
    intro w hw
    have hm1 : max (intrKernel Ω p w - s) 0 ≤ (3 + 11 * ε') * z w :=
      max_le (by linarith [hzk w hw]) (mul_nonneg ha.le (hz0 w hw))
    have hm2 : 1 / (3 + 11 * ε') * max (intrKernel Ω p w - s) 0 ≤ z w := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ ha]
      linarith
    calc 1 / (3 + 11 * ε') * (max (intrKernel Ω p w - s) 0 * F w)
        = 1 / (3 + 11 * ε') * max (intrKernel Ω p w - s) 0 * F w := by ring
      _ ≤ z w * F w := mul_le_mul_of_nonneg_right hm2 (hF0 w (hsub hw))
  -- Green's formula on `D'`: `∫ k_p u = ∫ z F`
  have hgr := eq_green_formula Ω Ωs hJ Ω aUp bUp c hΩ subset_rfl hop D' hD' u z
    (hu.1.of_le (by simp)) (hz.1.of_le (by simp)) (fun w hw => ⟨hu.2.2 w hw, hz.2.2 w hw⟩)
  have hgr' : ∫ w in D', intrKernel Ω p w * u w ∂hypArea Ω =
      ∫ w in D', z w * F w ∂hypArea Ω := by
    rw [setIntegral_congr_fun hm (fun w hw => by
        show intrKernel Ω p w * u w = u w * ellOpAdj Ω aUp bUp c z w
        rw [hzA w hw, mul_comm]),
      ← hgr, setIntegral_congr_fun hm (fun w hw => by
        show z w * ellOp Ω aUp bUp c u w = z w * F w
        rw [hu.2.1 w hw])]
  have hI1 : IntegrableOn (fun w => intrKernel Ω p w * u w) D' (hypArea Ω) :=
    s05_wd_integrableOn hJ hKc hKD (hkc.continuousOn.mul hu.1.continuousOn)
  have hI2 : IntegrableOn (fun w => z w * F w) D' (hypArea Ω) :=
    s05_wd_integrableOn hJ hKc hKD (hz.1.continuousOn.mul hFc.continuousOn)
  calc ∫⁻ w in D', ENNReal.ofReal (1 / (3 + 11 * ε') * (max (intrKernel Ω p w - s) 0 * F w))
        ∂hypArea Ω
      ≤ ∫⁻ w in D', ENNReal.ofReal (z w * F w) ∂hypArea Ω :=
        setLIntegral_mono' hm fun w hw => ENNReal.ofReal_le_ofReal (hpt w hw)
    _ = ENNReal.ofReal (∫ w in D', z w * F w ∂hypArea Ω) :=
        (ofReal_integral_eq_lintegral_ofReal hI2 (ae_restrict_of_forall_mem hm fun w hw =>
          mul_nonneg (hz0 w hw) (hF0 w (hsub hw)))).symm
    _ = ENNReal.ofReal (∫ w in D', intrKernel Ω p w * u w ∂hypArea Ω) := by rw [hgr']
    _ = ∫⁻ w in D', ENNReal.ofReal (intrKernel Ω p w * u w) ∂hypArea Ω :=
        ofReal_integral_eq_lintegral_ofReal hI1 (ae_restrict_of_forall_mem hm fun w hw =>
          mul_nonneg (hkp w).le (hu0 w hw))
    _ ≤ ∫⁻ w in D', ENNReal.ofReal (intrKernel Ω p w * G w) ∂hypArea Ω :=
        setLIntegral_mono' hm fun w hw => ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (huG w hw) (hkp w).le)
    _ ≤ ∫⁻ w in Ω, ENNReal.ofReal (intrKernel Ω p w * G w) ∂hypArea Ω := lintegral_mono_set hsub

/-- (c) helper: the lower bound (5.13), `∫_Ω k_p 𝒢_Ω F dâ ≥ (3 + C₀ε')⁻¹ ∫_Ω k_p F dâ`. -/
theorem s05_dc_lower {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {ε' : ℝ}
    {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ}
    (h : IsAdmissibleOp Ω Ω ε' aUp bUp c) {F : ℂ → ℝ} {M : ℝ} (hF : ContDiffOn ℝ ∞ F Ω)
    (hFM : ∀ w ∈ Ω, 0 ≤ F w ∧ F w ≤ M) {G : ℂ → ℝ} (hG : IsDirichletInverse Ω aUp bUp c Ω F G)
    {p : ℂ} (hp : p ∈ Ω) :
    ENNReal.ofReal (1 / (3 + 11 * ε')) *
        ∫⁻ w in Ω, ENNReal.ofReal (intrKernel Ω p w * F w) ∂hypArea Ω ≤
      ∫⁻ w in Ω, ENNReal.ofReal (intrKernel Ω p w * G w) ∂hypArea Ω := by
  have hΩ := s05_jordan_isOpen hJ
  have hk := s05_wd_kernel_smooth hJ hp
  have hkp : ∀ w, 0 < intrKernel Ω p w := s05_wd_kernel_pos Ω p
  have ha : 0 < 3 + 11 * ε' := by linarith [h.1]
  obtain ⟨Dn, hE⟩ := s05_smooth_exhaustion Ω hΩ
  obtain ⟨un, hun⟩ := (prop_dirichlet_a Ω Ωs hJ Ω ε' aUp bUp c h F M hF hFM).1 Dn hE
  have hlim := hG.2.2 Dn hE un hun
  have hDΩ : ∀ n, Dn n ⊆ Ω := fun n => subset_closure.trans (hE.1 n).2.2.1
  -- `uₙ ≤ G` on `Dₙ` (the Dirichlet solutions increase to `G`)
  have huG : ∀ n, ∀ w ∈ Dn n, un n w ≤ G w := by
    intro n w hw
    have h1 : (Dn n).indicator (un n) w ≤ G w :=
      (hlim w (hDΩ n hw)).1.ge_of_tendsto (hlim w (hDΩ n hw)).2 n
    rwa [indicator_of_mem hw] at h1
  -- `{cosh(d_ρ(p,·)/2) ≤ m + 2} ⊆ D_{N m}`
  choose N hN using fun m : ℕ =>
    s05_dc_cover hE (s05_cosh_proper hJ hp ((m : ℝ) + 2)) (fun x hx => hx.1)
  -- hence `k_p ≤ (m + 2)⁻²` on `∂D_{N m}`
  have hfr : ∀ m : ℕ, ∀ w ∈ frontier (Dn (N m)), intrKernel Ω p w ≤ (((m : ℝ) + 2)⁻¹) ^ 2 := by
    intro m w hw
    have hwΩ : w ∈ Ω := (hE.1 (N m)).2.2.1 (frontier_subset_closure hw)
    have hw' := hw
    rw [(hE.1 (N m)).1.frontier_eq] at hw'
    have hlt : (m : ℝ) + 2 < Real.cosh (poincareDist Ω p w / 2) := by
      by_contra hle
      exact hw'.2 (hN m ⟨hwΩ, not_lt.mp hle⟩)
    show ((Real.cosh (poincareDist Ω p w / 2))⁻¹) ^ 2 ≤ (((m : ℝ) + 2)⁻¹) ^ 2
    exact pow_le_pow_left₀ (inv_nonneg.mpr (Real.cosh_pos _).le)
      (inv_anti₀ (by positivity) hlt.le) 2
  have hs : Tendsto (fun m : ℕ => (((m : ℝ) + 2)⁻¹) ^ 2) atTop (𝓝 0) := by
    have h0 : Tendsto (fun m : ℕ => ((m : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    simpa using h0.pow 2
  calc ENNReal.ofReal (1 / (3 + 11 * ε')) *
        ∫⁻ w in Ω, ENNReal.ofReal (intrKernel Ω p w * F w) ∂hypArea Ω
      = ∫⁻ w in Ω, ENNReal.ofReal (1 / (3 + 11 * ε') * (intrKernel Ω p w * F w)) ∂hypArea Ω := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun w => ?_
        rw [ENNReal.ofReal_mul (one_div_pos.mpr ha).le]
    _ ≤ ∫⁻ w in Ω, ENNReal.ofReal (intrKernel Ω p w * G w) ∂hypArea Ω := by
        refine s05_wd_fatou (μ := hypArea Ω) (Dn := fun m => Dn (N m))
          (f := fun m w => 1 / (3 + 11 * ε') *
            (max (intrKernel Ω p w - (((m : ℝ) + 2)⁻¹) ^ 2) 0 * F w))
          (g := fun w => 1 / (3 + 11 * ε') * (intrKernel Ω p w * F w)) hΩ
          (fun m => (hE.1 (N m)).1) (fun m => hDΩ (N m)) (fun m => ?_) (fun w hw => ?_)
          (fun m => ?_)
        · have h1 : ContinuousOn (fun w => intrKernel Ω p w - (((m : ℝ) + 2)⁻¹) ^ 2) Ω :=
            hk.continuousOn.sub continuousOn_const
          have h2 : ContinuousOn (fun w => max (intrKernel Ω p w - (((m : ℝ) + 2)⁻¹) ^ 2) 0) Ω :=
            ContinuousOn.sup h1 continuousOn_const
          exact (continuousOn_const.mul (h2.mul hF.continuousOn)).mono (hDΩ (N m))
        · -- eventually `w ∈ D_{N m}`, and `(k_p - (m+2)⁻²)⁺ → k_p`
          have hev : ∀ᶠ m : ℕ in atTop, w ∈ Dn (N m) := by
            filter_upwards [(tendsto_atTop_add_const_right _ 2
              tendsto_natCast_atTop_atTop).eventually_ge_atTop
                (Real.cosh (poincareDist Ω p w / 2))] with m hm
            exact hN m ⟨hw, hm⟩
          have hT : Tendsto (fun m : ℕ => 1 / (3 + 11 * ε') *
              (max (intrKernel Ω p w - (((m : ℝ) + 2)⁻¹) ^ 2) 0 * F w)) atTop
              (𝓝 (1 / (3 + 11 * ε') * (max (intrKernel Ω p w - 0) 0 * F w))) :=
            (((tendsto_const_nhds.sub hs).max tendsto_const_nhds).mul
              tendsto_const_nhds).const_mul _
          rw [sub_zero, max_eq_left (hkp w).le] at hT
          refine hT.congr' ?_
          filter_upwards [hev] with m hm
          rw [indicator_of_mem hm]
        · exact s05_dc_set hJ h hF (fun w hw => (hFM w hw).1) (hE.1 (N m)) (hun (N m))
            (huG (N m)) hp (by positivity) (hfr m)

/-- **Proposition 5.5 (c)** (`prop:dirichlet`, sec05-upper.tex:252).  If `D = Ω`, every bounded
`u ∈ C²(Ω)` with `𝓛u = F` equals `𝒢_Ω F`, and
`∫_Ω k_p 𝒢_Ω F dâ ≥ (3 + C₀ε')⁻¹ ∫_Ω k_p F dâ` (5.13). -/
theorem prop_dirichlet_c : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (ε' : ℝ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsAdmissibleOp Ω Ω ε' aUp bUp c → ∀ (F : ℂ → ℝ) (M : ℝ), ContDiffOn ℝ ∞ F Ω →
      (∀ w ∈ Ω, 0 ≤ F w ∧ F w ≤ M) → ∀ G : ℂ → ℝ, IsDirichletInverse Ω aUp bUp c Ω F G →
        (∀ u : ℂ → ℝ, ContDiffOn ℝ 2 u Ω → (∃ B : ℝ, ∀ w ∈ Ω, |u w| ≤ B) →
          (∀ w ∈ Ω, ellOp Ω aUp bUp c u w = F w) → ∀ w ∈ Ω, u w = G w) ∧
        ∀ p ∈ Ω, ENNReal.ofReal (1 / (3 + 11 * ε')) *
            ∫⁻ w in Ω, ENNReal.ofReal (intrKernel Ω p w * F w) ∂hypArea Ω ≤
          ∫⁻ w in Ω, ENNReal.ofReal (intrKernel Ω p w * G w) ∂hypArea Ω := by
  intro Ω Ωs hJ ε' aUp bUp c h F M hF hFM G hG
  exact ⟨fun u hu hub hLu => s05_dc_unique hJ h hF hFM hG hu hub hLu,
    fun p hp => s05_dc_lower hJ h hF hFM hG hp⟩

/-- Reproduction helper (R1): pulling the hyperbolic area of `Ω` back through a Riemann map
`f : 𝔻 → Ω` (`f^* dâ_Ω = (2/(1-|z|²))² dA` by `eq_lambda_f`).  Inequality form, so no
measurability of `φ` is needed. -/
theorem s05_rp_pullback_le {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (φ : ℂ → ℝ≥0∞) :
    ∫⁻ w, φ w ∂hypArea Ω ≤
      ∫⁻ z in unitDisc, φ (f z) * ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2) := by
  classical
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hDo : IsOpen unitDisc := isOpen_ball
  set F : ℂ → ℂ := unitDisc.piecewise f 0 with hFdef
  have hFm : Measurable F :=
    hf.1.continuousOn.measurable_piecewise continuousOn_const hD
  have hFeq : ∀ z ∈ unitDisc, F z = f z := fun z hz => by simp [hFdef, hz]
  set c : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2) with hcdef
  have hcm : Measurable c := by
    simp only [hcdef]
    fun_prop
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
  have hmeas : hypArea Ω = ((volume.restrict unitDisc).withDensity c).map F := by
    ext t ht
    have hpre : MeasurableSet (F ⁻¹' t ∩ unitDisc) := (hFm ht).inter hD
    rw [Measure.map_apply hFm ht, withDensity_apply _ (hFm ht), Measure.restrict_restrict (hFm ht),
      hypArea, withDensity_apply _ ht, Measure.restrict_restrict ht, hset t]
    have hder : ∀ x ∈ F ⁻¹' t ∩ unitDisc, HasFDerivWithinAt f
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f x)).restrictScalars ℝ)
        (F ⁻¹' t ∩ unitDisc) x := by
      intro x hx
      exact ((hf.1.differentiableAt (hDo.mem_nhds hx.2)).hasDerivAt.hasFDerivAt.restrictScalars
        ℝ).hasFDerivWithinAt
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hpre hder
      (hf.2.1.mono inter_subset_right)]
    refine setLIntegral_congr_fun hpre (fun x hx => ?_)
    rw [s02_pullback_det, abs_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    simp only [hcdef]
    congr 1
    rw [← eq_lambda_f hf hx.2]
    ring
  rw [hmeas]
  refine (lintegral_map_le _ hFm.aemeasurable).trans ?_
  refine (lintegral_withDensity_le_lintegral_mul _ hcm _).trans_eq ?_
  refine setLIntegral_congr_fun hD (fun z hz => ?_)
  simp only [Pi.mul_apply, hFeq z hz, hcdef, mul_comm]

/-- Reproduction helper (R2): `e^{-βd} ≤ (sech²(d/2))^β` for `d, β ≥ 0`
(`(e^{d/2} + e^{-d/2})² ≤ 4e^d`). -/
theorem s05_rp_exp_le_kernel {d β : ℝ} (hd : 0 ≤ d) (hβ : 0 ≤ β) :
    Real.exp (-β * d) ≤ ((Real.cosh (d / 2))⁻¹ ^ 2) ^ β := by
  have hcu : Real.cosh (d / 2) ≤ Real.exp (d / 2) := by
    rw [Real.cosh_eq]
    have : Real.exp (-(d / 2)) ≤ Real.exp (d / 2) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hsq : Real.cosh (d / 2) ^ 2 ≤ Real.exp d :=
    calc Real.cosh (d / 2) ^ 2 ≤ Real.exp (d / 2) ^ 2 :=
          pow_le_pow_left₀ (Real.cosh_pos _).le hcu 2
      _ = Real.exp d := by rw [sq, ← Real.exp_add]; ring_nf
  have h1 : Real.exp (-d) ≤ (Real.cosh (d / 2))⁻¹ ^ 2 := by
    rw [Real.exp_neg, inv_pow]
    exact inv_anti₀ (pow_pos (Real.cosh_pos _) 2) hsq
  rw [show -β * d = -d * β by ring, Real.exp_mul]
  exact Real.rpow_le_rpow (Real.exp_pos _).le h1 hβ

/-- Reproduction helper (R3): `∫_{-π}^{π} |1 - ā r e^{iθ}|⁻² dθ = 2π/(1 - |a|²r²)` (the Poisson
formula `DiffContOnCl.circleAverage_poissonKernel_smul` for `1` at `w = r²a`). -/
theorem s05_rp_circle {a : ℂ} (ha : ‖a‖ < 1) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∫⁻ θ in Ioo (-π) π,
        ENNReal.ofReal (1 / ‖1 - conj a * Complex.polarCoord.symm (r, θ)‖ ^ 2) =
      ENNReal.ofReal (2 * π / (1 - ‖a‖ ^ 2 * r ^ 2)) := by
  have hcm : ∀ θ : ℝ, Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
    intro θ
    rw [Complex.polarCoord_symm_apply, circleMap_zero, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
  have hn : ∀ θ, ‖circleMap 0 r θ‖ = r := fun θ => by
    rw [norm_circleMap_zero, abs_of_pos hr0]
  have ha0 := norm_nonneg a
  have hra : ‖a‖ * r < 1 := by nlinarith
  have hden : ∀ θ, 0 < ‖1 - conj a * circleMap 0 r θ‖ := by
    intro θ
    refine norm_pos_iff.mpr fun h => ?_
    have h1 : conj a * circleMap 0 r θ = 1 := by linear_combination -h
    have h2 := congrArg norm h1
    rw [norm_mul, Complex.norm_conj, hn, norm_one] at h2
    linarith
  have hq : 0 < 1 - ‖a‖ ^ 2 * r ^ 2 := by
    have h := mul_nonneg ha0 hr0.le
    nlinarith
  set G : ℝ → ℝ := fun θ => 1 / ‖1 - conj a * circleMap 0 r θ‖ ^ 2 with hGdef
  have hGc : Continuous G :=
    continuous_const.div ((continuous_const.sub (continuous_const.mul
      (continuous_circleMap 0 r))).norm.pow 2) (fun θ => (pow_pos (hden θ) 2).ne')
  have hP : ∀ θ, poissonKernel 0 ((r : ℂ) ^ 2 * a) (circleMap 0 r θ) =
      (1 - ‖a‖ ^ 2 * r ^ 2) * G θ := by
    intro θ
    rw [poissonKernel_def]
    simp only [sub_zero, hGdef]
    have hzz : circleMap 0 r θ * conj (circleMap 0 r θ) = (r : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
      push_cast
      ring
    have hfac : circleMap 0 r θ - (r : ℂ) ^ 2 * a =
        circleMap 0 r θ * conj (1 - conj a * circleMap 0 r θ) := by
      rw [map_sub, map_one, map_mul, Complex.conj_conj, ← hzz]
      ring
    have hnorm : ‖circleMap 0 r θ - (r : ℂ) ^ 2 * a‖ = r * ‖1 - conj a * circleMap 0 r θ‖ := by
      rw [hfac, norm_mul, Complex.norm_conj, hn]
    have hd := (hden θ).ne'
    rw [hnorm, hn, norm_mul, norm_pow, Complex.norm_of_nonneg hr0.le]
    field_simp
  have hw : (r : ℂ) ^ 2 * a ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, norm_mul, norm_pow, Complex.norm_of_nonneg hr0.le]
    nlinarith
  have hpois := DiffContOnCl.circleAverage_poissonKernel_smul (f := fun _ : ℂ => (1 : ℂ))
    (c := 0) (R := r) diffContOnCl_const hw
  rw [Real.circleAverage_def] at hpois
  simp only [Pi.smul_apply', hP, Complex.real_smul, mul_one] at hpois
  rw [intervalIntegral.integral_ofReal] at hpois
  have h3 : (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, (1 - ‖a‖ ^ 2 * r ^ 2) * G θ = 1 := by
    exact_mod_cast hpois
  rw [intervalIntegral.integral_const_mul] at h3
  have hI : ∫ θ in (0 : ℝ)..2 * π, G θ = 2 * π / (1 - ‖a‖ ^ 2 * r ^ 2) := by
    have hpi := Real.pi_pos
    have h4 := congrArg (fun x => 2 * π * x) h3
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul, mul_one] at h4
    rw [eq_div_iff hq.ne', mul_comm]
    exact h4
  have hGp : Function.Periodic G (2 * π) := fun θ => by
    simp only [hGdef, periodic_circleMap 0 r θ]
  have hI' : ∫ θ in -π..π, G θ = 2 * π / (1 - ‖a‖ ^ 2 * r ^ 2) := by
    have h := hGp.intervalIntegral_add_eq (-π) 0
    rw [show -π + 2 * π = π by ring, zero_add] at h
    rw [h, hI]
  simp_rw [hcm]
  change ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (G θ) = _
  rw [← ofReal_integral_eq_lintegral_ofReal (hGc.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    (ae_of_all _ fun θ => by simp only [Pi.zero_apply, hGdef]; positivity),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    hI']

/-- Reproduction helper (R4): `∫₀¹ r (1-r²)^{β-2} dr ≤ 1/(2(β-1))` for `β > 1`
(antiderivative `-(1-r²)^{β-1}/(2(β-1))`, improper at `1` when `β < 2`). -/
theorem s05_rp_radial {β : ℝ} (hβ : 1 < β) :
    ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r * (1 - r ^ 2) ^ (β - 2)) ≤
      ENNReal.ofReal (1 / (2 * (β - 1))) := by
  have hβ1 : 0 < β - 1 := by linarith
  set g : ℝ → ℝ := fun r => -((1 - r ^ 2) ^ (β - 1) / (2 * (β - 1))) with hgdef
  have hgc : ContinuousOn g (Icc 0 1) := by
    have : Continuous g := by
      simp only [hgdef]
      exact (((Real.continuous_rpow_const hβ1.le).comp
        (continuous_const.sub (continuous_id.pow 2))).div_const _).neg
    exact this.continuousOn
  have hder : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g (x * (1 - x ^ 2) ^ (β - 2)) x := by
    intro x hx
    have hx2 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have h1 : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_sub 1
    have h2 := (h1.rpow_const (p := β - 1) (Or.inl hx2.ne')).div_const (2 * (β - 1)) |>.neg
    convert h2 using 1
    rw [show β - 1 - 1 = β - 2 by ring]
    field_simp
  have hnn : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ x * (1 - x ^ 2) ^ (β - 2) := by
    intro x hx
    have hx2 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    exact mul_nonneg hx.1.le (Real.rpow_nonneg hx2.le _)
  have hint := integrableOn_deriv_of_nonneg hgc hder hnn
  have hval : ∫ x in (0 : ℝ)..1, x * (1 - x ^ 2) ^ (β - 2) = 1 / (2 * (β - 1)) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hgc hder
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hint)]
    simp only [hgdef]
    rw [show (1 : ℝ) - 1 ^ 2 = 0 by norm_num, Real.zero_rpow hβ1.ne']
    norm_num
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.mono_set Ioo_subset_Ioc_self)
    ((ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ hnn)),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, hval]

/-- Reproduction helper (R5): the disc form of Lemma 5.6 with `ℓ = 0`, `p = a`:
`∫_𝔻 k_a(z) (1-|z|²)^β (2/(1-|z|²))² dA ≤ 4π/(β-1) · (1-|a|²)` (Euclidean polar coordinates,
R3 in `θ` with `(1-r²)/(1-|a|²r²) ≤ 1`, then R4). -/
theorem s05_rp_disc {a : ℂ} (ha : ‖a‖ < 1) {β : ℝ} (hβ : 1 < β) :
    ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖1 - conj a * z‖ ^ 2 *
        (1 - ‖z‖ ^ 2) ^ β) * ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2) ≤
      ENNReal.ofReal (4 * π / (β - 1) * (1 - ‖a‖ ^ 2)) := by
  have hβ1 : 0 < β - 1 := by linarith
  have ha0 := norm_nonneg a
  have hA : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith
  set H : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal ((1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) /
      ‖1 - conj a * z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ β) * ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2)
    with hHdef
  set B : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (8 * π * (1 - ‖a‖ ^ 2)) *
      ENNReal.ofReal (r * (1 - r ^ 2) ^ (β - 2)) with hBdef
  -- the `θ`-integral at radius `r`
  have hrad : ∀ r ∈ Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π,
      ENNReal.ofReal r • unitDisc.indicator H (Complex.polarCoord.symm (r, θ)) ≤
        (Ioo (0 : ℝ) 1).indicator B r := by
    intro r hr0
    have hr0' : 0 < r := hr0
    by_cases hr1 : r < 1
    · have hmem : ∀ θ : ℝ, Complex.polarCoord.symm (r, θ) ∈ unitDisc := fun θ =>
        mem_ball_zero_iff.mpr (by rw [Complex.norm_polarCoord_symm, abs_of_pos hr0']; exact hr1)
      have hs : 0 < 1 - r ^ 2 := by nlinarith
      set C : ℝ := r * (1 - ‖a‖ ^ 2) * (1 - r ^ 2) * (1 - r ^ 2) ^ β * (2 / (1 - r ^ 2)) ^ 2
        with hCdef
      have hC0 : 0 ≤ C := by
        have := Real.rpow_nonneg hs.le β
        positivity
      have hpt : ∀ θ : ℝ, ENNReal.ofReal r • unitDisc.indicator H (Complex.polarCoord.symm (r, θ))
          = ENNReal.ofReal C * ENNReal.ofReal
              (1 / ‖1 - conj a * Complex.polarCoord.symm (r, θ)‖ ^ 2) := by
        intro θ
        rw [indicator_of_mem (hmem θ), smul_eq_mul]
        simp only [hHdef, Complex.norm_polarCoord_symm, abs_of_pos hr0']
        have hk : 0 ≤ (1 - ‖a‖ ^ 2) * (1 - r ^ 2) /
            ‖1 - conj a * Complex.polarCoord.symm (r, θ)‖ ^ 2 * (1 - r ^ 2) ^ β := by
          have := Real.rpow_nonneg hs.le β
          positivity
        rw [← ENNReal.ofReal_mul hk, ← ENNReal.ofReal_mul hr0'.le, ← ENNReal.ofReal_mul hC0]
        congr 1
        simp only [hCdef]
        ring
      simp_rw [hpt]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, s05_rp_circle ha hr0' hr1,
        ← ENNReal.ofReal_mul hC0, indicator_of_mem (show r ∈ Ioo (0 : ℝ) 1 from ⟨hr0', hr1⟩)]
      simp only [hBdef]
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hq : 1 - r ^ 2 ≤ 1 - ‖a‖ ^ 2 * r ^ 2 := by nlinarith
      have hq0 : 0 < 1 - ‖a‖ ^ 2 * r ^ 2 := by linarith
      have hT := Real.rpow_nonneg hs.le (β - 2)
      have e : (1 - r ^ 2) ^ β = (1 - r ^ 2) ^ (β - 2) * (1 - r ^ 2) ^ 2 := by
        have e0 : (1 - r ^ 2) ^ β = (1 - r ^ 2) ^ ((β - 2) + 2) := by norm_num
        rw [e0, Real.rpow_add hs, Real.rpow_two]
      have hsplit : C * (2 * π / (1 - ‖a‖ ^ 2 * r ^ 2)) =
          8 * π * (1 - ‖a‖ ^ 2) * (r * (1 - r ^ 2) ^ (β - 2)) *
            ((1 - r ^ 2) / (1 - ‖a‖ ^ 2 * r ^ 2)) := by
        simp only [hCdef]
        rw [e]
        field_simp
        ring
      rw [hsplit]
      exact mul_le_of_le_one_right (by positivity) ((div_le_one hq0).mpr hq)
    · have hnot : ∀ θ : ℝ, Complex.polarCoord.symm (r, θ) ∉ unitDisc := fun θ h => by
        have h' := mem_ball_zero_iff.mp h
        rw [Complex.norm_polarCoord_symm, abs_of_pos hr0'] at h'
        exact hr1 h'
      simp only [indicator_of_notMem (hnot _), smul_zero, lintegral_zero]
      exact bot_le
  calc ∫⁻ z in unitDisc, H z
      = ∫⁻ z, unitDisc.indicator H z := (lintegral_indicator measurableSet_ball H).symm
    _ = ∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 • unitDisc.indicator H (Complex.polarCoord.symm p) :=
        (Complex.lintegral_comp_polarCoord_symm _).symm
    _ ≤ ∫⁻ r in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal r • unitDisc.indicator H (Complex.polarCoord.symm (r, θ)) := by
        rw [Complex.polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict]
        exact lintegral_prod_le _
    _ ≤ ∫⁻ r in Ioi (0 : ℝ), (Ioo (0 : ℝ) 1).indicator B r := setLIntegral_mono' measurableSet_Ioi hrad
    _ = ∫⁻ r in Ioo (0 : ℝ) 1, B r := by
        rw [setLIntegral_indicator measurableSet_Ioo, inter_eq_left.mpr Ioo_subset_Ioi_self]
    _ ≤ ENNReal.ofReal (8 * π * (1 - ‖a‖ ^ 2)) * ENNReal.ofReal (1 / (2 * (β - 1))) := by
        simp only [hBdef]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact mul_le_mul' le_rfl (s05_rp_radial hβ)
    _ = ENNReal.ofReal (4 * π / (β - 1) * (1 - ‖a‖ ^ 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring

/-- **Lemma 5.6** (Reproduction of the kernel, `lem:reproduction`, sec05-upper.tex:324).  For
`β > 1` and `p, ℓ ∈ Ω`, `∫_Ω k_p(x) e^{-β d_ρ(x, ℓ)} dâ(x) ≤ 4πβ/(β-1) · k_p(ℓ)` (5.14). -/
theorem lem_reproduction : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ β : ℝ, 1 < β →
    ∀ p ∈ Ω, ∀ ℓ ∈ Ω,
      ∫⁻ x, ENNReal.ofReal (intrKernel Ω p x * Real.exp (-β * poincareDist Ω x ℓ)) ∂hypArea Ω ≤
        ENNReal.ofReal (4 * π * β / (β - 1) * intrKernel Ω p ℓ) := by
  intro Ω Ωs hJ β hβ p hp ℓ hℓ
  have hΩ := s02_jordanPair_riemannMap hJ
  obtain ⟨f, hf, hf0⟩ := s02_riemannMap_at hJ hℓ
  obtain ⟨a, ha, rfl⟩ : p ∈ f '' unitDisc := by rw [hf.2.2]; exact hp
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hkℓ : intrKernel Ω (f a) ℓ = 1 - ‖a‖ ^ 2 := by
    rw [← hf0, s02_intrKernel_eq hf ha h0]
    simp
  have hβ1 : 0 < β - 1 := by linarith
  calc ∫⁻ x, ENNReal.ofReal (intrKernel Ω (f a) x * Real.exp (-β * poincareDist Ω x ℓ))
          ∂hypArea Ω
      ≤ ∫⁻ z in unitDisc, ENNReal.ofReal (intrKernel Ω (f a) (f z) *
          Real.exp (-β * poincareDist Ω (f z) ℓ)) *
            ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2) := s05_rp_pullback_le hf _
    _ ≤ ∫⁻ z in unitDisc, ENNReal.ofReal ((1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) /
          ‖1 - conj a * z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ β) *
            ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2) := by
      refine setLIntegral_mono' measurableSet_ball (fun z hz => ?_)
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      have hfz : f z ∈ Ω := hf.2.2 ▸ mem_image_of_mem f hz
      rw [s02_intrKernel_eq hf ha hz]
      have hk0 : 0 ≤ (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖1 - conj a * z‖ ^ 2 := by
        have : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
        have : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
        positivity
      refine mul_le_mul_of_nonneg_left ?_ hk0
      have hd0 : 0 ≤ poincareDist Ω (f z) ℓ := s02_poincareDist_nonneg hΩ hfz hℓ
      have hk : (Real.cosh (poincareDist Ω (f z) ℓ / 2))⁻¹ ^ 2 = 1 - ‖z‖ ^ 2 := by
        have h := s02_intrKernel_eq hf h0 hz
        rw [hf0] at h
        unfold intrKernel at h
        rw [s02_poincareDist_comm hΩ hfz hℓ, h]
        simp
      have h := s05_rp_exp_le_kernel hd0 (by linarith : (0 : ℝ) ≤ β)
      rwa [hk] at h
    _ ≤ ENNReal.ofReal (4 * π / (β - 1) * (1 - ‖a‖ ^ 2)) := s05_rp_disc ha1 hβ
    _ ≤ ENNReal.ofReal (4 * π * β / (β - 1) * intrKernel Ω (f a) ℓ) := by
      rw [hkℓ]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by nlinarith [norm_nonneg a]))
      exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) hβ1.le

/-- Graph-operator helper (GO1): the metric `g_τ` of the equidistant surface in closed form,
from Lemma 5.2 (a) and the closed form of its right-hand side.  With `α = (cosh²τ + s²e^{2τ})λ²`,
`β = 2 cosh τ e^τ` and `S = S(f⁻¹)(x)`:
`g_τ = [[α + β Re S, -β Im S], [-β Im S, α - β Re S]]` in the frame `(1, i)`. -/
theorem s05_go_metric {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {x : ℂ} (hx : x ∈ Ω) (hs : schwarzNorm Ω x ≠ 1) (τ : ℝ) :
    graphMetric Ω x τ =
      !![(Real.cosh τ ^ 2 + schwarzNorm Ω x ^ 2 * Real.exp τ ^ 2) * poincareDensity Ω x ^ 2 +
            2 * Real.cosh τ * Real.exp τ * (schwarzian (Function.invFunOn f unitDisc) x).re,
          -(2 * Real.cosh τ * Real.exp τ * (schwarzian (Function.invFunOn f unitDisc) x).im);
        -(2 * Real.cosh τ * Real.exp τ * (schwarzian (Function.invFunOn f unitDisc) x).im),
          (Real.cosh τ ^ 2 + schwarzNorm Ω x ^ 2 * Real.exp τ ^ 2) * poincareDensity Ω x ^ 2 -
            2 * Real.cosh τ * Real.exp τ * (schwarzian (Function.invFunOn f unitDisc) x).re] := by
  have hS := lem_shape_a Ω Ωs hJ x hx hs τ
  ext i j
  have key := hS.2.2 (frameVec i) (frameVec j)
  simp only [graphMetric, Matrix.of_apply]
  rw [key, s05_sa_rhs hf hx hs τ]
  fin_cases i <;> fin_cases j <;>
    simp [frameVec, Complex.mul_re, Complex.mul_im]
  ring

/-- Graph-operator helper (GO2): `g_0 = I`. -/
theorem s05_go_metric_zero {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {x : ℂ} (hx : x ∈ Ω)
    (hs : schwarzNorm Ω x ≠ 1) : graphMetric Ω x 0 = fffMat Ω x := by
  ext i j
  have key := (lem_shape_a Ω Ωs hJ x hx hs 0).2.2 (frameVec i) (frameVec j)
  simp only [graphMetric, fffMat, Matrix.of_apply]
  rw [key]
  simp

/-- Graph-operator helper (GO3): `det g_τ = λ⁴ (cosh²τ - s² e^{2τ})²`. -/
theorem s05_go_det {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {x : ℂ} (hx : x ∈ Ω)
    (hs : schwarzNorm Ω x ≠ 1) (τ : ℝ) :
    (graphMetric Ω x τ).det =
      poincareDensity Ω x ^ 4 * (Real.cosh τ ^ 2 - schwarzNorm Ω x ^ 2 * Real.exp τ ^ 2) ^ 2 := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hx
  have hS : ‖schwarzian (Function.invFunOn f unitDisc) x‖ =
      schwarzNorm Ω x * poincareDensity Ω x ^ 2 := by
    rw [eq_def_s hf hx]
    field_simp
  have hn : (schwarzian (Function.invFunOn f unitDisc) x).re *
        (schwarzian (Function.invFunOn f unitDisc) x).re +
      (schwarzian (Function.invFunOn f unitDisc) x).im *
        (schwarzian (Function.invFunOn f unitDisc) x).im =
      (schwarzNorm Ω x * poincareDensity Ω x ^ 2) ^ 2 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, hS]
  rw [s05_go_metric hJ hf hx hs τ, Matrix.det_fin_two_of]
  linear_combination (-(2 * Real.cosh τ * Real.exp τ) ^ 2) * hn

/-- Graph-operator helper (GO4): on an open `U ⊆ Ω` with `s < 1`, every entry of `g_τ(x)` is
jointly `C^∞` in `(x, τ)`. -/
theorem s05_go_metric_contDiff {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {U : Set ℂ}
    (hU : IsOpen U) (hUΩ : U ⊆ Ω) (hUs : ∀ x ∈ U, schwarzNorm Ω x < 1) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => graphMetric Ω p.1 p.2 i j) (U ×ˢ univ) := by
  -- The openness of `U` is not needed here; it is kept for a uniform interface.
  have _hU := hU
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  have hmaps : MapsTo (fun p : ℂ × ℝ => p.1) (U ×ˢ univ) Ω := fun p hp => hUΩ hp.1
  have hl : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => poincareDensity Ω p.1) (U ×ˢ univ) :=
    (s02_contDiffOn_poincareDensity hf).comp contDiff_fst.contDiffOn hmaps
  have hS : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => schwarzian (Function.invFunOn f unitDisc) p.1) (U ×ˢ univ) :=
    (s02_contDiffOn_invFun hf).2.2.2.comp contDiff_fst.contDiffOn hmaps
  have hR : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => (schwarzian (Function.invFunOn f unitDisc) p.1).re) (U ×ˢ univ) :=
    (Complex.reCLM.contDiff.comp_contDiffOn hS).congr (fun p _ => by simp)
  have hI : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => (schwarzian (Function.invFunOn f unitDisc) p.1).im) (U ×ˢ univ) :=
    (Complex.imCLM.contDiff.comp_contDiffOn hS).congr (fun p _ => by simp)
  have hl0 : ∀ p ∈ U ×ˢ (univ : Set ℝ), poincareDensity Ω p.1 ≠ 0 :=
    fun p hp => (s02_poincareDensity_pos ⟨f, hf⟩ (hUΩ hp.1)).ne'
  have hs2 : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => schwarzNorm Ω p.1 ^ 2) (U ×ˢ univ) := by
    refine ((hR.mul hR).add (hI.mul hI)).div (hl.pow 4) (fun p hp => pow_ne_zero 4 (hl0 p hp))
      |>.congr (fun p hp => ?_)
    have hl' := hl0 p hp
    rw [eq_def_s hf (hUΩ hp.1), div_pow, Complex.sq_norm, Complex.normSq_apply]
    simp only [Pi.div_apply]
    ring
  have hc : ContDiff ℝ ∞ (fun p : ℂ × ℝ => Real.cosh p.2) :=
    Real.contDiff_cosh.comp contDiff_snd
  have he : ContDiff ℝ ∞ (fun p : ℂ × ℝ => Real.exp p.2) :=
    Real.contDiff_exp.comp contDiff_snd
  have hA : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => (Real.cosh p.2 ^ 2 + schwarzNorm Ω p.1 ^ 2 *
      Real.exp p.2 ^ 2) * poincareDensity Ω p.1 ^ 2) (U ×ˢ univ) :=
    ((hc.contDiffOn.pow 2).add (hs2.mul (he.contDiffOn.pow 2))).mul (hl.pow 2)
  have hB : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => 2 * Real.cosh p.2 * Real.exp p.2) (U ×ˢ univ) :=
    ((contDiffOn_const.mul hc.contDiffOn).mul he.contDiffOn)
  have key : ∀ p ∈ U ×ˢ (univ : Set ℝ), graphMetric Ω p.1 p.2 =
      !![(Real.cosh p.2 ^ 2 + schwarzNorm Ω p.1 ^ 2 * Real.exp p.2 ^ 2) *
            poincareDensity Ω p.1 ^ 2 + 2 * Real.cosh p.2 * Real.exp p.2 * (schwarzian (Function.invFunOn f unitDisc) p.1).re,
          -(2 * Real.cosh p.2 * Real.exp p.2 * (schwarzian (Function.invFunOn f unitDisc) p.1).im);
        -(2 * Real.cosh p.2 * Real.exp p.2 * (schwarzian (Function.invFunOn f unitDisc) p.1).im),
          (Real.cosh p.2 ^ 2 + schwarzNorm Ω p.1 ^ 2 * Real.exp p.2 ^ 2) *
            poincareDensity Ω p.1 ^ 2 - 2 * Real.cosh p.2 * Real.exp p.2 * (schwarzian (Function.invFunOn f unitDisc) p.1).re] :=
    fun p hp => s05_go_metric hJ hf (hUΩ hp.1) (hUs p.1 hp.1).ne p.2
  fin_cases i <;> fin_cases j
  · exact (hA.add (hB.mul hR)).congr (fun p hp => by rw [key p hp]; simp)
  · exact (hB.mul hI).neg.congr (fun p hp => by rw [key p hp]; simp)
  · exact (hB.mul hI).neg.congr (fun p hp => by rw [key p hp]; simp)
  · exact (hA.sub (hB.mul hR)).congr (fun p hp => by rw [key p hp]; simp)

/-- Graph-operator helper (GO5): `|B|²_I = tr B² = (2s² + 2s⁴)/(1 - s²)²`, from Lemma 5.2 (b)
(`tr B = 2s²/(1-s²)`, `det B = -s²/(1-s²)`). -/
theorem s05_go_trace_sq {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {x : ℂ} (hx : x ∈ Ω)
    (hs : schwarzNorm Ω x ≠ 1) :
    (shapeMat Ω x * shapeMat Ω x).trace =
      (2 * schwarzNorm Ω x ^ 2 + 2 * schwarzNorm Ω x ^ 4) / (1 - schwarzNorm Ω x ^ 2) ^ 2 := by
  obtain ⟨_, h2, h3⟩ := lem_shape_b Ω Ωs hJ x hx hs
  have hs0 := (eq_nehari (s02_jordanPair_riemannMap hJ) hx).1
  set s := schwarzNorm Ω x
  have hd : 1 - s ^ 2 ≠ 0 := by
    intro h
    have : (s - 1) * (s + 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h' | h'
    · exact hs (by linarith)
    · linarith
  unfold meanCurv at h2
  rw [Matrix.trace_fin_two] at h2
  rw [Matrix.det_fin_two] at h3
  have e : (shapeMat Ω x * shapeMat Ω x).trace =
      (shapeMat Ω x 0 0 + shapeMat Ω x 1 1) ^ 2 -
        2 * (shapeMat Ω x 0 0 * shapeMat Ω x 1 1 - shapeMat Ω x 0 1 * shapeMat Ω x 1 0) := by
    simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have htr : shapeMat Ω x 0 0 + shapeMat Ω x 1 1 = 2 * (s ^ 2 / (1 - s ^ 2)) := by linarith
  have hdet : shapeMat Ω x 0 0 * shapeMat Ω x 1 1 - shapeMat Ω x 0 1 * shapeMat Ω x 1 0 =
      -(s ^ 2 / (1 - s ^ 2)) := by linarith
  rw [e, htr, hdet]
  field_simp
  ring

/-- Graph-operator helper (GO6): on `G₀ = goodSet Ω Ωs η R` with `R ≥ 0`, `s < η` (`w` is its own
witness in `ς(X(w), R)`; the set is bounded by Nehari). -/
theorem s05_go_s_lt {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {η R : ℝ} (hR : 0 ≤ R) {w : ℂ}
    (hw : w ∈ goodSet Ω Ωs η R) : schwarzNorm Ω w < η := by
  obtain ⟨hwΩ, hlt⟩ := hw
  have hΩ := s02_jordanPair_riemannMap hJ
  have hΩs := s02_jordanPair_riemannMap (s02_jordanPair_symm hJ)
  have hU : epstein Ω w ∈ UHS := by
    have h := lem_normal_b hΩ hwΩ
    rw [← h.2.2]
    exact h.1 0
  have hmem : epstein Ω w ∈ hball (epstein Ω w) R := by
    refine ⟨hU, ?_⟩
    have : coshDist (epstein Ω w) (epstein Ω w) = 1 := by simp [coshDist]
    simp only [hdist, this, Real.arcosh_zero]
    exact hR
  have hbdd : BddAbove ({r | ∃ w' ∈ Ω, epstein Ω w' ∈ hball (epstein Ω w) R ∧
      r = schwarzNorm Ω w'} ∪ {r | ∃ z ∈ Ωs, epstein Ωs z ∈ hball (epstein Ω w) R ∧
      r = schwarzNorm Ωs z}) := by
    refine ⟨3 / 2, ?_⟩
    rintro r (⟨w', hw', -, rfl⟩ | ⟨z, hz, -, rfl⟩)
    · exact (eq_nehari hΩ hw').2
    · exact (eq_nehari hΩs hz).2
  have hle : schwarzNorm Ω w ≤ varsigma Ω Ωs (epstein Ω w) R :=
    le_csSup hbdd (Or.inl ⟨w, hwΩ, hmem, rfl⟩)
  linarith

/-- Graph-operator helper (GO7): `goodSet Ω Ωs η 0` is open (properness, Lemma 2.7, on both sides:
the witnesses `w'`, `z*` of `ς(X(w), 0)` satisfy `Φ_{X(w)}(w') = 1`, so they stay in a compact set
and the supremum is attained and upper semicontinuous). -/
theorem s05_go_isOpen {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) (η : ℝ) :
    IsOpen (goodSet Ω Ωs η 0) := by
  have hΩ := s02_jordanPair_riemannMap hJ
  have hJs := s02_jordanPair_symm hJ
  have hΩs := s02_jordanPair_riemannMap hJs
  obtain ⟨f, hf⟩ := hΩ
  obtain ⟨fs, hfs⟩ := hΩs
  have hΩo : IsOpen Ω := s05_jordan_isOpen hJ
  -- `B(P, 0) = {P}` on `ℍ³`
  have hpt : ∀ P Q : ℂ × ℝ, P ∈ UHS → Q ∈ hball P 0 → Q = P := by
    intro P Q hP hQ
    obtain ⟨hQU, hQd⟩ := hQ
    have h1 : (0 : ℝ) < P.2 := hP
    have h2 : (0 : ℝ) < Q.2 := hQU
    have hden : 0 < 2 * P.2 * Q.2 := by positivity
    have hnn : 0 ≤ (‖P.1 - Q.1‖ ^ 2 + (P.2 - Q.2) ^ 2) / (2 * P.2 * Q.2) := by positivity
    have hge : 1 ≤ coshDist P Q := by unfold coshDist; linarith
    have hz : Real.arcosh (coshDist P Q) = 0 := le_antisymm hQd (Real.arcosh_nonneg hge)
    have hc := (Real.arcosh_eq_zero_iff hge).1 hz
    unfold coshDist at hc
    have hq : (‖P.1 - Q.1‖ ^ 2 + (P.2 - Q.2) ^ 2) / (2 * P.2 * Q.2) = 0 := by linarith
    rw [div_eq_zero_iff] at hq
    rcases hq with hq | hq
    · have ha : ‖P.1 - Q.1‖ ^ 2 = 0 := by
        nlinarith [sq_nonneg ‖P.1 - Q.1‖, sq_nonneg (P.2 - Q.2)]
      have hb : (P.2 - Q.2) ^ 2 = 0 := by
        nlinarith [sq_nonneg ‖P.1 - Q.1‖, sq_nonneg (P.2 - Q.2)]
      rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at ha
      rw [sq_eq_zero_iff, sub_eq_zero] at hb
      exact Prod.ext ha.symm hb.symm
    · exact absurd hq hden.ne'
  have hself : ∀ x ∈ UHS, x ∈ hball x 0 := by
    intro x hx
    refine ⟨hx, ?_⟩
    have h1 : coshDist x x = 1 := by simp [coshDist]
    have h2 : hdist x x = 0 := by simp only [hdist, h1, Real.arcosh_zero]
    exact h2.le
  have hbdd : ∀ x : ℂ × ℝ, BddAbove ({r | ∃ w' ∈ Ω, epstein Ω w' ∈ hball x 0 ∧
      r = schwarzNorm Ω w'} ∪ {r | ∃ z ∈ Ωs, epstein Ωs z ∈ hball x 0 ∧
      r = schwarzNorm Ωs z}) := by
    intro x
    refine ⟨3 / 2, ?_⟩
    rintro r (⟨w', hw', -, rfl⟩ | ⟨z, hz, -, rfl⟩)
    · exact (eq_nehari ⟨f, hf⟩ hw').2
    · exact (eq_nehari ⟨fs, hfs⟩ hz).2
  -- `X` and `s` are continuous on `Ω`, and likewise on `Ω*`
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
  -- `Φ_{X(w')}(w') = 1`
  have hphi : ∀ w' ∈ Ω, horoPhi Ω (epstein Ω w') w' ≤ 1 := by
    intro w' hw'
    have h := lem_normal_b ⟨f, hf⟩ hw'
    have h1 := s02_horoPhi_normalGeod Ω w' (s02_poincareDensity_pos ⟨f, hf⟩ hw') 0
    rw [h.2.2, Real.exp_zero] at h1
    exact h1.le
  have hphis : ∀ z ∈ Ωs, horoPhi Ωs (epstein Ωs z) z ≤ 1 := by
    intro z hz
    have h := lem_normal_b ⟨fs, hfs⟩ hz
    have h1 := s02_horoPhi_normalGeod Ωs z (s02_poincareDensity_pos ⟨fs, hfs⟩ hz) 0
    rw [h.2.2, Real.exp_zero] at h1
    exact h1.le
  rw [isOpen_iff_forall_mem_open]
  intro w0 hw0
  obtain ⟨hw0Ω, hlt⟩ := hw0
  have hq0U : epstein Ω w0 ∈ UHS := by
    have h := lem_normal_b ⟨f, hf⟩ hw0Ω
    rw [← h.2.2]
    exact h.1 0
  have hq0 : (0 : ℝ) < (epstein Ω w0).2 := hq0U
  obtain ⟨η', hη'1, hη'2⟩ := exists_between hlt
  have hς0 : 0 ≤ varsigma Ω Ωs (epstein Ω w0) 0 := by
    refine Real.sSup_nonneg ?_
    rintro r (⟨w', hw', -, rfl⟩ | ⟨z, hz, -, rfl⟩)
    · exact (eq_nehari ⟨f, hf⟩ hw').1
    · exact (eq_nehari ⟨fs, hfs⟩ hz).1
  -- the compact set `𝒬 = closedBall X(w₀) (ξ₀/2) ⊆ ℍ³`
  have h𝒬U : closedBall (epstein Ω w0) ((epstein Ω w0).2 / 2) ⊆ UHS := by
    intro q hq
    have h0 := mem_closedBall.1 hq
    rw [Prod.dist_eq] at h0
    have h1 : dist q.2 (epstein Ω w0).2 ≤ (epstein Ω w0).2 / 2 := (le_max_right _ _).trans h0
    rw [Real.dist_eq] at h1
    have h2 := (abs_le.1 h1).1
    show (0 : ℝ) < q.2
    linarith
  have h𝒬c := isCompact_closedBall (epstein Ω w0) ((epstein Ω w0).2 / 2)
  obtain ⟨K', hK'c, hK'Ω, hK'⟩ := lem_proper_compact hJ h𝒬c h𝒬U 1
  obtain ⟨K'', hK''c, hK''Ω, hK''⟩ := lem_proper_compact hJs h𝒬c h𝒬U 1
  -- the compact sets of parameters with `s ≥ η'`, and their (closed) images
  have hBc : IsCompact (K' ∩ schwarzNorm Ω ⁻¹' Ici η') :=
    hK'c.of_isClosed_subset ((hsC.mono hK'Ω).preimage_isClosed_of_isClosed hK'c.isClosed
      isClosed_Ici) inter_subset_left
  have hBcs : IsCompact (K'' ∩ schwarzNorm Ωs ⁻¹' Ici η') :=
    hK''c.of_isClosed_subset ((hsCs.mono hK''Ω).preimage_isClosed_of_isClosed hK''c.isClosed
      isClosed_Ici) inter_subset_left
  have hXB : IsClosed (epstein Ω '' (K' ∩ schwarzNorm Ω ⁻¹' Ici η')) :=
    (hBc.image_of_continuousOn (hXC.mono fun b hb => hK'Ω hb.1)).isClosed
  have hXBs : IsClosed (epstein Ωs '' (K'' ∩ schwarzNorm Ωs ⁻¹' Ici η')) :=
    (hBcs.image_of_continuousOn (hXCs.mono fun b hb => hK''Ω hb.1)).isClosed
  have hq0B : epstein Ω w0 ∉ epstein Ω '' (K' ∩ schwarzNorm Ω ⁻¹' Ici η') := by
    rintro ⟨b, hb, hbq⟩
    have hbΩ := hK'Ω hb.1
    have hm : epstein Ω b ∈ hball (epstein Ω w0) 0 := by rw [hbq]; exact hself _ hq0U
    have h1 : schwarzNorm Ω b ≤ varsigma Ω Ωs (epstein Ω w0) 0 :=
      le_csSup (hbdd _) (Or.inl ⟨b, hbΩ, hm, rfl⟩)
    have h2 : η' ≤ schwarzNorm Ω b := hb.2
    linarith
  have hq0Bs : epstein Ω w0 ∉ epstein Ωs '' (K'' ∩ schwarzNorm Ωs ⁻¹' Ici η') := by
    rintro ⟨b, hb, hbq⟩
    have hbΩ := hK''Ω hb.1
    have hm : epstein Ωs b ∈ hball (epstein Ω w0) 0 := by rw [hbq]; exact hself _ hq0U
    have h1 : schwarzNorm Ωs b ≤ varsigma Ω Ωs (epstein Ω w0) 0 :=
      le_csSup (hbdd _) (Or.inr ⟨b, hbΩ, hm, rfl⟩)
    have h2 : η' ≤ schwarzNorm Ωs b := hb.2
    linarith
  refine ⟨Ω ∩ epstein Ω ⁻¹' (ball (epstein Ω w0) ((epstein Ω w0).2 / 2) ∩
    (epstein Ω '' (K' ∩ schwarzNorm Ω ⁻¹' Ici η'))ᶜ ∩
    (epstein Ωs '' (K'' ∩ schwarzNorm Ωs ⁻¹' Ici η'))ᶜ), ?_,
    hXC.isOpen_inter_preimage hΩo ((isOpen_ball.inter hXB.isOpen_compl).inter hXBs.isOpen_compl),
    ⟨hw0Ω, ⟨mem_ball_self (half_pos hq0), hq0B⟩, hq0Bs⟩⟩
  rintro w ⟨hwΩ, ⟨hwb, hwB⟩, hwBs⟩
  have hw𝒬 : epstein Ω w ∈ closedBall (epstein Ω w0) ((epstein Ω w0).2 / 2) :=
    ball_subset_closedBall hwb
  have hXwU : epstein Ω w ∈ UHS := h𝒬U hw𝒬
  refine ⟨hwΩ, ?_⟩
  have hle : varsigma Ω Ωs (epstein Ω w) 0 ≤ η' := by
    refine Real.sSup_le ?_ (hς0.trans hη'1.le)
    rintro r (⟨w', hw'Ω, hw'm, rfl⟩ | ⟨z, hzΩ, hzm, rfl⟩)
    · have heq := hpt _ _ hXwU hw'm
      have hK : w' ∈ K' := hK' ⟨hw'Ω, epstein Ω w', by rw [heq]; exact hw𝒬, hphi w' hw'Ω⟩
      by_contra hcon
      exact hwB ⟨w', ⟨hK, (not_le.1 hcon).le⟩, heq⟩
    · have heq := hpt _ _ hXwU hzm
      have hK : z ∈ K'' := hK'' ⟨hzΩ, epstein Ωs z, by rw [heq]; exact hw𝒬, hphis z hzΩ⟩
      by_contra hcon
      exact hwBs ⟨z, ⟨hK, (not_le.1 hcon).le⟩, heq⟩
  linarith

/-- Graph-operator helper (GO8): `∇(θu) = θ ∇u`. -/
theorem s05_go_grad_smul {u : ℂ → ℝ} {x : ℂ} (hu : DifferentiableAt ℝ u x) (θ : ℝ) :
    gradCoords (θ • u) x = θ • gradCoords u x := by
  funext j
  simp only [gradCoords, fderiv_const_smul hu θ, FunLike.coe_smul, Pi.smul_apply]

/-- Graph-operator helper (GO9): the `τ`-part of `D𝒬(0)[u]`.  `W(θu)` is even in `θ`, and
`(log √det g_τ)''(0) = (2 - 6s²)/(1 - s²)² = 2 - tr B²`, so
`d/dθ|₀ [∂_τ(√det g_τ / W(θu))/√det g_τ]_{τ = θu(w)} = (2 - 6s²)/(1 - s²)² · u(w)`. -/
theorem s05_go_tau_part {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {u : ℂ → ℝ} {w : ℂ}
    (hw : w ∈ Ω) (hs : schwarzNorm Ω w < 1) (hu : DifferentiableAt ℝ u w) :
    HasDerivAt (fun θ : ℝ => deriv (fun τ => graphSdet Ω w τ / graphW Ω (θ • u) w τ) (θ * u w) /
        graphSdet Ω w (θ * u w))
      ((2 - 6 * schwarzNorm Ω w ^ 2) / (1 - schwarzNorm Ω w ^ 2) ^ 2 * u w) 0 := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hw
  have hs0 := (eq_nehari ⟨f, hf⟩ hw).1
  obtain ⟨l, hldef⟩ : ∃ l, l = poincareDensity Ω w := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s, s = schwarzNorm Ω w := ⟨_, rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a, a = u w := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v, v = gradCoords u w := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R, R = (schwarzian (Function.invFunOn f unitDisc) w).re := ⟨_, rfl⟩
  obtain ⟨I', hIdef⟩ : ∃ I', I' = (schwarzian (Function.invFunOn f unitDisc) w).im := ⟨_, rfl⟩
  rw [← hldef] at hl
  have hs' : s < 1 := by rw [hsdef]; exact hs
  have hs0' : 0 ≤ s := by rw [hsdef]; exact hs0
  rw [← hsdef, ← hadef]
  have hs2 : s ^ 2 < 1 := by nlinarith
  have hd : 1 - s ^ 2 ≠ 0 := by linarith
  -- `P = cosh² - s² e^{2τ}` and its derivatives
  obtain ⟨P, hP⟩ : ∃ P : ℝ → ℝ,
      P = fun τ => Real.cosh τ * Real.cosh τ - s ^ 2 * (Real.exp τ * Real.exp τ) := ⟨_, rfl⟩
  obtain ⟨P1, hP1⟩ : ∃ P1 : ℝ → ℝ,
      P1 = fun τ => 2 * (Real.cosh τ * Real.sinh τ) - s ^ 2 * (2 * (Real.exp τ * Real.exp τ)) :=
    ⟨_, rfl⟩
  have hPd : ∀ τ, HasDerivAt P (P1 τ) τ := by
    intro τ
    rw [hP, hP1]
    convert ((Real.hasDerivAt_cosh τ).mul (Real.hasDerivAt_cosh τ)).sub
      (((Real.hasDerivAt_exp τ).mul (Real.hasDerivAt_exp τ)).const_mul (s ^ 2)) using 1
    ring
  have hP1d : ∀ τ, HasDerivAt P1 (2 * (Real.sinh τ * Real.sinh τ + Real.cosh τ * Real.cosh τ) -
      s ^ 2 * (4 * (Real.exp τ * Real.exp τ))) τ := by
    intro τ
    rw [hP1]
    convert (((Real.hasDerivAt_cosh τ).mul (Real.hasDerivAt_sinh τ)).const_mul 2).sub
      ((((Real.hasDerivAt_exp τ).mul (Real.hasDerivAt_exp τ)).const_mul 2).const_mul (s ^ 2))
      using 1
    ring
  have hP0 : P 0 = 1 - s ^ 2 := by rw [hP]; simp
  have hP10 : P1 0 = -(2 * s ^ 2) := by rw [hP1]; simp; ring
  have hPc : Continuous P := by
    rw [hP]
    exact (Real.continuous_cosh.mul Real.continuous_cosh).sub
      (continuous_const.mul (Real.continuous_exp.mul Real.continuous_exp))
  set V := {τ : ℝ | 0 < P τ} with hVdef
  have hV : IsOpen V := isOpen_lt continuous_const hPc
  have h0V : (0 : ℝ) ∈ V := by
    show 0 < P 0
    rw [hP0]
    linarith
  -- the metric along the normal geodesic
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ → ℝ,
      A = fun τ => (Real.cosh τ ^ 2 + s ^ 2 * Real.exp τ ^ 2) * l ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ → ℝ, B = fun τ => 2 * Real.cosh τ * Real.exp τ := ⟨_, rfl⟩
  have hg : ∀ τ, graphMetric Ω w τ =
      !![A τ + B τ * R, -(B τ * I'); -(B τ * I'), A τ - B τ * R] := by
    intro τ
    rw [s05_go_metric hJ hf hw hs.ne τ, ← hsdef, ← hldef, ← hRdef, ← hIdef, hAdef, hBdef]
  have hdet : ∀ τ, (graphMetric Ω w τ).det = l ^ 4 * P τ ^ 2 := by
    intro τ
    rw [s05_go_det hJ hw hs.ne τ, ← hsdef, ← hldef, hP]
    ring
  -- `q(τ) = ∇u · g_τ⁻¹ ∇u`
  obtain ⟨q, hq⟩ : ∃ q : ℝ → ℝ, q = fun τ => v ⬝ᵥ ((graphMetric Ω w τ)⁻¹ *ᵥ v) := ⟨_, rfl⟩
  obtain ⟨Qp, hQp⟩ : ∃ Qp : ℝ → ℝ, Qp = fun τ =>
      v 0 * ((A τ - B τ * R) * v 0 - (-(B τ * I')) * v 1) +
        v 1 * (-(-(B τ * I')) * v 0 + (A τ + B τ * R) * v 1) := ⟨_, rfl⟩
  have hqf : ∀ τ, q τ = (l ^ 4 * P τ ^ 2)⁻¹ * Qp τ := by
    intro τ
    rw [hq, hQp]
    simp only
    rw [Matrix.inv_def, hdet τ, hg τ, Matrix.adjugate_fin_two_of, Ring.inverse_eq_inv']
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have hAc : ContDiff ℝ 2 A := by
    rw [hAdef]
    exact ((Real.contDiff_cosh.pow 2).add (contDiff_const.mul (Real.contDiff_exp.pow 2))).mul
      contDiff_const
  have hBc : ContDiff ℝ 2 B := by
    rw [hBdef]
    exact (contDiff_const.mul Real.contDiff_cosh).mul Real.contDiff_exp
  have hPc2 : ContDiff ℝ 2 P := by
    rw [hP]
    exact (Real.contDiff_cosh.mul Real.contDiff_cosh).sub
      (contDiff_const.mul (Real.contDiff_exp.mul Real.contDiff_exp))
  have hQc : ContDiff ℝ 2 Qp := by
    rw [hQp]
    fun_prop
  have hqC : ContDiffOn ℝ 2 q V := by
    refine (((contDiffOn_const.mul (hPc2.contDiffOn.pow 2)).inv fun τ hτ => ?_).mul
      hQc.contDiffOn).congr fun τ _ => hqf τ
    exact mul_ne_zero (pow_ne_zero 4 hl.ne') (pow_ne_zero 2 (ne_of_gt hτ))
  have hqd : ∀ τ ∈ V, HasDerivAt q (deriv q τ) τ := fun τ hτ =>
    ((hqC.differentiableOn (by norm_num)) τ hτ).differentiableAt (hV.mem_nhds hτ) |>.hasDerivAt
  have hdq2 : HasDerivAt (deriv q) (deriv (deriv q) 0) 0 :=
    (((hqC.deriv_of_isOpen hV (m := 1) (by norm_num)).differentiableOn (by norm_num)) 0
      h0V).differentiableAt (hV.mem_nhds h0V) |>.hasDerivAt
  -- `g_τ` data along the slice `θ`
  have hW : ∀ θ τ, graphW Ω (θ • u) w τ = √(1 + θ ^ 2 * q τ) := by
    intro θ τ
    simp only [graphW, s05_go_grad_smul hu θ, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hq, hvdef]
    congr 1
    ring
  have hSd : ∀ τ, graphSdet Ω w τ = l ^ 2 * |P τ| := by
    intro τ
    rw [graphSdet, hdet τ, show l ^ 4 * P τ ^ 2 = (l ^ 2 * P τ) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < l ^ 2)]
  have hF : ∀ θ τ, τ ∈ V → 0 < 1 + θ ^ 2 * q τ →
      deriv (fun τ' => graphSdet Ω w τ' / graphW Ω (θ • u) w τ') τ =
        (l ^ 2 * P1 τ * √(1 + θ ^ 2 * q τ) -
            l ^ 2 * P τ * (θ ^ 2 * deriv q τ / (2 * √(1 + θ ^ 2 * q τ)))) /
          √(1 + θ ^ 2 * q τ) ^ 2 := by
    intro θ τ hτ hpos
    have hD := ((hPd τ).const_mul (l ^ 2)).div
      ((((hqd τ hτ).const_mul (θ ^ 2)).const_add 1).sqrt hpos.ne')
      (Real.sqrt_pos.mpr hpos).ne'
    refine (hD.congr_of_eventuallyEq ?_).deriv
    filter_upwards [hV.mem_nhds hτ] with τ' hτ'
    rw [hSd, hW, abs_of_pos hτ']
    rfl
  -- the slice function near `θ = 0`
  have hPa : HasDerivAt (fun θ => P (θ * a)) (P1 0 * a) 0 :=
    (hPd 0).comp_of_eq 0 (hasDerivAt_mul_const a) (by simp)
  have hP1a : HasDerivAt (fun θ => P1 (θ * a)) ((2 * (Real.sinh 0 * Real.sinh 0 +
      Real.cosh 0 * Real.cosh 0) - s ^ 2 * (4 * (Real.exp 0 * Real.exp 0))) * a) 0 :=
    (hP1d 0).comp_of_eq 0 (hasDerivAt_mul_const a) (by simp)
  have hqa : HasDerivAt (fun θ => q (θ * a)) (deriv q 0 * a) 0 :=
    (hqd 0 h0V).comp_of_eq 0 (hasDerivAt_mul_const a) (by simp)
  have hdqa : HasDerivAt (fun θ => deriv q (θ * a)) (deriv (deriv q) 0 * a) 0 :=
    hdq2.comp_of_eq 0 (hasDerivAt_mul_const a) (by simp)
  have hWin := ((hasDerivAt_pow 2 (0 : ℝ)).mul hqa).const_add 1
  have hWs := hWin.sqrt (by simp)
  have hNum := ((hP1a.const_mul (l ^ 2)).mul hWs).sub ((hPa.const_mul (l ^ 2)).mul
    (((hasDerivAt_pow 2 (0 : ℝ)).mul hdqa).div (hWs.const_mul 2) (by simp)))
  have hE := (hNum.div (hWs.pow 2) (by simp)).div (hPa.const_mul (l ^ 2))
    (by rw [zero_mul, hP0]; exact mul_ne_zero (pow_ne_zero 2 hl.ne') hd)
  have hev1 : ∀ᶠ θ in 𝓝 (0 : ℝ), θ * a ∈ V :=
    (hPa.continuousAt.eventually (Ioi_mem_nhds (by show 0 < P (0 * a); rw [zero_mul, hP0]; linarith)))
  have hev2 : ∀ᶠ θ in 𝓝 (0 : ℝ), 0 < 1 + θ ^ 2 * q (θ * a) :=
    (hWin.continuousAt.eventually (Ioi_mem_nhds (by simp)))
  refine (hE.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [zero_mul, hP0, hP10, Real.sinh_zero, Real.cosh_zero, Real.exp_zero]
    simp [hP0, hP10]
    field_simp
    ring
  · filter_upwards [hev1, hev2] with θ h1 h2
    rw [hF θ (θ * a) h1 h2, hSd, abs_of_pos h1]
    simp only [Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.pow_apply]

/-- Graph-operator helper (GO10): the flux part of `D𝒬(0)[u]` is `Δ_I u`.  The flux of `θu` is
`θ k(θ, ·)` with `k` jointly `C^1` near `(0, w)`, and `k(0, ·) = √det I · I⁻¹∇u` near `w` (GO2). -/
theorem s05_go_flux_part {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {U : Set ℂ} (hU : IsOpen U)
    (hUΩ : U ⊆ Ω) (hUs : ∀ x ∈ U, schwarzNorm Ω x < 1) {u : ℂ → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    {w : ℂ} (hw : w ∈ U) :
    HasDerivAt (fun θ : ℝ =>
        (∑ i : Fin 2, fderiv ℝ (fun x => graphFlux Ω (θ • u) (θ * u w) x i) w (frameVec i)) /
          graphSdet Ω w (θ * u w))
      (fffLaplacian Ω u w) 0 := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  have hwΩ := hUΩ hw
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hwΩ
  have hs1 := hUs w hw
  have hs0 := (eq_nehari ⟨f, hf⟩ hwΩ).1
  have h1s : 0 < 1 - schwarzNorm Ω w ^ 2 := by nlinarith
  obtain ⟨a, hadef⟩ : ∃ a, a = u w := ⟨_, rfl⟩
  rw [← hadef]
  have hinf : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hdiff : ∀ x ∈ U, DifferentiableAt ℝ u x := fun x hx =>
    ((hu.differentiableOn (by simp)) x hx).differentiableAt (hU.mem_nhds hx)
  -- the inverse of a `2 × 2` matrix applied to a vector
  have hinv : ∀ (M : Matrix (Fin 2) (Fin 2) ℝ) (y : Fin 2 → ℝ) (i : Fin 2), (M⁻¹ *ᵥ y) i =
      (M 0 0 * M 1 1 - M 0 1 * M 1 0)⁻¹ *
        ![M 1 1 * y 0 - M 0 1 * y 1, -(M 1 0) * y 0 + M 0 0 * y 1] i := by
    intro M y i
    rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv', ← Matrix.det_fin_two]
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  -- the data as functions of `p = (θ, x)`, with `τ = θ u(w)`
  obtain ⟨G, hG⟩ : ∃ G : Fin 2 → Fin 2 → ℝ × ℂ → ℝ,
      ∀ j k p, G j k p = graphMetric Ω p.2 (p.1 * a) j k :=
    ⟨fun j k p => graphMetric Ω p.2 (p.1 * a) j k, fun _ _ _ => rfl⟩
  have hGC : ∀ j k, ContDiffAt ℝ 1 (G j k) (0, w) := by
    intro j k
    have h1 := (s05_go_metric_contDiff hJ hU hUΩ hUs j k).contDiffAt
      (prod_mem_nhds (hU.mem_nhds hw) (univ_mem : (univ : Set ℝ) ∈ 𝓝 ((0 : ℝ) * a)))
    have h2 : ContDiffAt ℝ ∞ (fun p : ℝ × ℂ => (p.2, p.1 * a)) (0, w) :=
      contDiffAt_snd.prodMk (contDiffAt_fst.mul contDiffAt_const)
    have h3 := (h1.comp (0, w) h2).of_le hinf
    exact h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => hG j k p)
  obtain ⟨Gr, hGr⟩ : ∃ Gr : Fin 2 → ℝ × ℂ → ℝ, ∀ j p, Gr j p = gradCoords u p.2 j :=
    ⟨fun j p => gradCoords u p.2 j, fun _ _ => rfl⟩
  have hGrC : ∀ j, ContDiffAt ℝ 1 (Gr j) (0, w) := by
    intro j
    have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ u y) U :=
      hu.fderiv_of_isOpen hU (WithTop.coe_le_coe.2 (le_top : (1 + 1 : ℕ∞) ≤ ⊤) :
        ((1 + 1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
    have h2 : ContDiffAt ℝ 1 (fun x => fderiv ℝ u x (frameVec j)) w :=
      (h1.contDiffAt (hU.mem_nhds hw)).clm_apply contDiffAt_const
    have h3 := h2.comp (0, w) (contDiffAt_snd : ContDiffAt ℝ 1 (Prod.snd : ℝ × ℂ → ℂ) (0, w))
    exact h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => hGr j p)
  obtain ⟨dt, hdt⟩ : ∃ dt : ℝ × ℂ → ℝ, ∀ p, dt p = G 0 0 p * G 1 1 p - G 0 1 p * G 1 0 p :=
    ⟨fun p => G 0 0 p * G 1 1 p - G 0 1 p * G 1 0 p, fun _ => rfl⟩
  have hdtC : ContDiffAt ℝ 1 dt (0, w) :=
    (((hGC 0 0).mul (hGC 1 1)).sub ((hGC 0 1).mul (hGC 1 0))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hdt)
  have hdt0 : dt (0, w) = (graphMetric Ω w 0).det := by
    rw [hdt, Matrix.det_fin_two]
    simp only [hG, zero_mul]
  have hdtpos : 0 < dt (0, w) := by
    rw [hdt0, s05_go_det hJ hwΩ hs1.ne 0, Real.cosh_zero, Real.exp_zero]
    have h1s' : 0 < (1 : ℝ) ^ 2 - schwarzNorm Ω w ^ 2 * 1 ^ 2 := by simpa using h1s
    exact mul_pos (pow_pos hl 4) (pow_pos h1s' 2)
  obtain ⟨mv, hmv⟩ : ∃ mv : Fin 2 → ℝ × ℂ → ℝ,
      ∀ i p, mv i p = ((graphMetric Ω p.2 (p.1 * a))⁻¹ *ᵥ gradCoords u p.2) i :=
    ⟨fun i p => ((graphMetric Ω p.2 (p.1 * a))⁻¹ *ᵥ gradCoords u p.2) i, fun _ _ => rfl⟩
  have hmvC : ∀ i, ContDiffAt ℝ 1 (mv i) (0, w) := by
    intro i
    have hinvC := hdtC.inv hdtpos.ne'
    fin_cases i
    · exact (hinvC.mul (((hGC 1 1).mul (hGrC 0)).sub ((hGC 0 1).mul (hGrC 1)))).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun p => by simp [hmv, hinv, hdt, hG, hGr])
    · exact (hinvC.mul (((hGC 1 0).mul (hGrC 0)).neg.add ((hGC 0 0).mul (hGrC 1)))).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun p => by simp [hmv, hinv, hdt, hG, hGr])
  obtain ⟨qq, hqq⟩ : ∃ qq : ℝ × ℂ → ℝ, ∀ p,
      qq p = gradCoords u p.2 ⬝ᵥ ((graphMetric Ω p.2 (p.1 * a))⁻¹ *ᵥ gradCoords u p.2) :=
    ⟨fun p => gradCoords u p.2 ⬝ᵥ ((graphMetric Ω p.2 (p.1 * a))⁻¹ *ᵥ gradCoords u p.2),
      fun _ => rfl⟩
  have hqqC : ContDiffAt ℝ 1 qq (0, w) :=
    (((hGrC 0).mul (hmvC 0)).add ((hGrC 1).mul (hmvC 1))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun p => by
        simp [hqq, hGr, hmv, dotProduct, Fin.sum_univ_two])
  have hSdC : ContDiffAt ℝ 1 (fun p : ℝ × ℂ => graphSdet Ω p.2 (p.1 * a)) (0, w) :=
    (hdtC.sqrt hdtpos.ne').congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => by
      simp only [graphSdet, hdt, hG, Matrix.det_fin_two])
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Fin 2 → ℝ × ℂ → ℝ,
      ∀ i p, Φ i p = graphSdet Ω p.2 (p.1 * a) * mv i p / √(1 + p.1 ^ 2 * qq p) :=
    ⟨fun i p => graphSdet Ω p.2 (p.1 * a) * mv i p / √(1 + p.1 ^ 2 * qq p), fun _ _ => rfl⟩
  have hΦC : ∀ i, ContDiffAt ℝ 1 (Φ i) (0, w) := fun i =>
    ((hSdC.mul (hmvC i)).div
      ((contDiffAt_const (c := (1 : ℝ))).add ((contDiffAt_fst.pow 2).mul hqqC) |>.sqrt
        (by simp)) (by simp)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun p => hΦ i p)
  -- the flux of `θu` is `θ Φ(θ, ·)` on `U`
  have hflux : ∀ θ : ℝ, ∀ x ∈ U, ∀ i, graphFlux Ω (θ • u) (θ * a) x i = θ * Φ i (θ, x) := by
    intro θ x hx i
    have e : ∀ X : ℝ, θ * (θ * X) = θ ^ 2 * X := fun X => by ring
    rw [hΦ]
    simp only [graphFlux, graphW, s05_go_grad_smul (hdiff x hx) θ, Matrix.mulVec_smul,
      Pi.smul_apply, smul_dotProduct, dotProduct_smul, smul_eq_mul, hmv, hqq, e]
    ring
  -- `k(θ) = Σ_i ∂_i Φ_i(θ, ·)(w) / √det g_{θ u(w)}`
  obtain ⟨k, hk⟩ : ∃ k : ℝ → ℝ, ∀ θ, k θ =
      (fderiv ℝ (fun x => Φ 0 (θ, x)) w (frameVec 0) +
        fderiv ℝ (fun x => Φ 1 (θ, x)) w (frameVec 1)) / graphSdet Ω w (θ * a) :=
    ⟨fun θ => (fderiv ℝ (fun x => Φ 0 (θ, x)) w (frameVec 0) +
        fderiv ℝ (fun x => Φ 1 (θ, x)) w (frameVec 1)) / graphSdet Ω w (θ * a), fun _ => rfl⟩
  have hfdC : ∀ i, ContinuousAt (fun θ => fderiv ℝ (fun x => Φ i (θ, x)) w (frameVec i)) 0 := by
    intro i
    have h := ContDiffAt.fderiv (f := fun θ x => Φ i (θ, x)) (g := fun _ : ℝ => w) (m := 0)
      (hΦC i) contDiffAt_const (by simp)
    exact (h.clm_apply contDiffAt_const).continuousAt
  have hSd0 : 0 < graphSdet Ω w (0 * a) := by
    rw [zero_mul, graphSdet, ← hdt0]
    exact Real.sqrt_pos.mpr hdtpos
  have hSdw : ContinuousAt (fun θ : ℝ => graphSdet Ω w (θ * a)) 0 := by
    have hc : ContinuousAt (fun θ : ℝ => (θ, w)) 0 :=
      (continuous_id.prodMk continuous_const).continuousAt
    have h := ContinuousAt.comp (x := (0 : ℝ)) (f := fun θ : ℝ => (θ, w)) hSdC.continuousAt hc
    exact h
  have hkC : ContinuousAt k 0 :=
    (((hfdC 0).add (hfdC 1)).div hSdw hSd0.ne').congr
      (Filter.Eventually.of_forall fun θ => (hk θ).symm)
  -- `k(0) = Δ_I u(w)`
  have hfd0 : ∀ i, fderiv ℝ (fun x => Φ i (0, x)) w =
      fderiv ℝ (fun x => Real.sqrt (fffMat Ω x).det * ((fffMat Ω x)⁻¹ *ᵥ gradCoords u x) i) w := by
    intro i
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [hU.mem_nhds hw] with x hx
    simp [hΦ, hmv, graphSdet, s05_go_metric_zero hJ (hUΩ hx) (hUs x hx).ne]
  have hk0 : k 0 = fffLaplacian Ω u w := by
    rw [hk, fffLaplacian, Fin.sum_univ_two, hfd0 0, hfd0 1, zero_mul, graphSdet,
      s05_go_metric_zero hJ hwΩ hs1.ne]
  -- the flux part is `θ k(θ)` near `θ = 0`
  have hev : ∀ᶠ θ in 𝓝 (0 : ℝ), ∀ i, ContDiffAt ℝ 1 (Φ i) (θ, w) := by
    refine Filter.eventually_all.2 fun i => ?_
    exact ((continuous_id.prodMk continuous_const).tendsto' (0 : ℝ) (0, w) rfl).eventually
      ((hΦC i).eventually (by simp))
  have hevEq : (fun θ : ℝ =>
      (∑ i : Fin 2, fderiv ℝ (fun x => graphFlux Ω (θ • u) (θ * a) x i) w (frameVec i)) /
        graphSdet Ω w (θ * a)) =ᶠ[𝓝 0] fun θ => θ * k θ := by
    filter_upwards [hev] with θ hθ
    have e : ∀ i, fderiv ℝ (fun x => graphFlux Ω (θ • u) (θ * a) x i) w =
        θ • fderiv ℝ (fun x => Φ i (θ, x)) w := by
      intro i
      have hloc : (fun x => graphFlux Ω (θ • u) (θ * a) x i) =ᶠ[𝓝 w]
          fun x => θ * Φ i (θ, x) := by
        filter_upwards [hU.mem_nhds hw] with x hx using hflux θ x hx i
      have hdΦ : DifferentiableAt ℝ (fun x => Φ i (θ, x)) w :=
        ((hθ i).comp w (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
      rw [hloc.fderiv_eq, fderiv_const_mul hdΦ θ]
    rw [Fin.sum_univ_two, e 0, e 1, hk]
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hkd : HasDerivAt (fun θ => θ * k θ) (k 0) 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    refine Tendsto.congr' ?_ (hkC.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    simp only [slope_def_field]
    rw [zero_mul, sub_zero, sub_zero, mul_div_cancel_left₀ _ hθ]
  rw [← hk0]
  exact hkd.congr_of_eventuallyEq hevEq

/-- Graph-operator helper (GO11), the general form of Lemma 5.7 (d): on any open `U ⊆ Ω` with
`s < 1`, `D𝒬(0)[u] = (2 - tr B²) u - Δ_I u` for `u ∈ C^∞(U)`.  (No goodness or tube hypothesis;
reusable at the `(η, R)` of Lemma 4.2.) -/
theorem s05_go_deriv {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {U : Set ℂ} (hU : IsOpen U)
    (hUΩ : U ⊆ Ω) (hUs : ∀ x ∈ U, schwarzNorm Ω x < 1) {u : ℂ → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    {w : ℂ} (hw : w ∈ U) :
    graphQDeriv Ω 0 u w =
      (2 - (shapeMat Ω w * shapeMat Ω w).trace) * u w - fffLaplacian Ω u w := by
  have hwΩ := hUΩ hw
  have hs := hUs w hw
  have hs0 := (eq_nehari (s02_jordanPair_riemannMap hJ) hwΩ).1
  have hd : 1 - schwarzNorm Ω w ^ 2 ≠ 0 := by nlinarith
  have hdiff : DifferentiableAt ℝ u w :=
    ((hu.differentiableOn (by simp)) w hw).differentiableAt (hU.mem_nhds hw)
  have hQ : ∀ θ : ℝ, graphQ Ω (0 + θ • u) w =
      2 * (schwarzNorm Ω w ^ 2 / (1 - schwarzNorm Ω w ^ 2)) +
        (deriv (fun τ => graphSdet Ω w τ / graphW Ω (θ • u) w τ) (θ * u w) /
            graphSdet Ω w (θ * u w) -
          (∑ i : Fin 2, fderiv ℝ (fun x => graphFlux Ω (θ • u) (θ * u w) x i) w (frameVec i)) /
            graphSdet Ω w (θ * u w)) := by
    intro θ
    rw [zero_add]
    simp only [graphQ, meanCurvUp, Pi.smul_apply, smul_eq_mul]
    ring
  have hD := ((s05_go_tau_part hJ hwΩ hs hdiff).sub
    (s05_go_flux_part hJ hU hUΩ hUs hu hw)).const_add
      (2 * (schwarzNorm Ω w ^ 2 / (1 - schwarzNorm Ω w ^ 2)))
  rw [graphQDeriv, (hD.congr_of_eventuallyEq (Filter.Eventually.of_forall hQ)).deriv,
    s05_go_trace_sq hJ hwΩ hs.ne]
  congr 1
  field_simp
  ring

/-! ## §5.4 The exact graph operator

Context (sec05-upper.tex:358): Lemma 4.2 is applied with `m = 8`, `T = D_K + 2`, `L = R₀ + 10`,
giving `η(ε, K)`, `R(ε, K)` with `η < ε`; `G₀ = goodSet Ω Ωs η R`, `t = slabTop`, `N = slabMap`. -/

/-- B1 helper (ML0): `g_τ = M(τ, λ, S)`, GO1 (`s05_go_metric`) with `s = ‖S‖/λ²` (`eq_def_s`). -/
theorem s05_ml_metric {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {x : ℂ} (hx : x ∈ Ω) (hs : schwarzNorm Ω x ≠ 1) (τ : ℝ) :
    graphMetric Ω x τ =
      !![(Real.cosh τ ^ 2 + (‖schwarzian (Function.invFunOn f unitDisc) x‖ /
              poincareDensity Ω x ^ 2) ^ 2 * Real.exp τ ^ 2) * poincareDensity Ω x ^ 2 +
            2 * Real.cosh τ * Real.exp τ * (schwarzian (Function.invFunOn f unitDisc) x).re,
          -(2 * Real.cosh τ * Real.exp τ * (schwarzian (Function.invFunOn f unitDisc) x).im);
        -(2 * Real.cosh τ * Real.exp τ * (schwarzian (Function.invFunOn f unitDisc) x).im),
          (Real.cosh τ ^ 2 + (‖schwarzian (Function.invFunOn f unitDisc) x‖ /
              poincareDensity Ω x ^ 2) ^ 2 * Real.exp τ ^ 2) * poincareDensity Ω x ^ 2 -
            2 * Real.cosh τ * Real.exp τ * (schwarzian (Function.invFunOn f unitDisc) x).re] := by
  rw [s05_go_metric hJ hf hx hs τ, eq_def_s hf hx]

/-- B1 helper (ML0'): the jet domain `O = {0 < λ, ‖S‖ e^τ < λ² cosh τ}` is open. -/
theorem s05_ml_open :
    IsOpen {J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) |
      0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1} := by
  have h1 : IsOpen {J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) |
      0 < J.2.1} := isOpen_lt continuous_const (by fun_prop)
  have h2 : IsOpen {J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) |
      ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1} :=
    isOpen_lt (by fun_prop) (by fun_prop)
  exact h1.inter h2

/-- B1 helper (ML1a): for `M = [[A + B r, -B m], [-B m, A - B r]]` with `A > 0` and
`det M = A² - B²(r² + m²) > 0`, the adjugate form `p · adj(M) p` is `≥ 0`. -/
theorem s05_ml_quad_nonneg {A B r m p0 p1 : ℝ} (hA : 0 < A)
    (hD : 0 < A ^ 2 - B ^ 2 * (r ^ 2 + m ^ 2)) :
    0 ≤ p0 * ((A - B * r) * p0 + B * m * p1) + p1 * (B * m * p0 + (A + B * r) * p1) := by
  have h1 : 0 < A - B * r := by
    by_contra h
    have h := not_lt.mp h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg h (show 0 ≤ A + B * r by linarith),
      sq_nonneg (B * m)]
  have key : (A - B * r) *
      (p0 * ((A - B * r) * p0 + B * m * p1) + p1 * (B * m * p0 + (A + B * r) * p1)) =
      ((A - B * r) * p0 + B * m * p1) ^ 2 + (A ^ 2 - B ^ 2 * (r ^ 2 + m ^ 2)) * p1 ^ 2 := by
    ring
  have h2 : 0 ≤ (A - B * r) *
      (p0 * ((A - B * r) * p0 + B * m * p1) + p1 * (B * m * p0 + (A + B * r) * p1)) := by
    rw [key]
    exact add_nonneg (sq_nonneg _) (mul_nonneg hD.le (sq_nonneg _))
  exact (mul_nonneg_iff_of_pos_left h1).mp h2

/-- B1 helper (ML1): the jet formula.  There is a universal `Ψ`, smooth on `O`, with
`H_up(u)(w) = Ψ(u w, λ w, S w, Dλ w, DS w, Du w, D²u w)` whenever the jet lies in `O`. -/
theorem s05_ml_jet :
    ∃ Ψ : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) → ℝ,
      ContDiffOn ℝ ∞ Ψ {J | 0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1} ∧
      ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω →
      ∀ U : Set ℂ, IsOpen U → U ⊆ Ω → (∀ x ∈ U, schwarzNorm Ω x < 1) →
      ∀ u : ℂ → ℝ, ContDiffOn ℝ 2 u U → ∀ w ∈ U,
        (u w, poincareDensity Ω w, schwarzian (Function.invFunOn f unitDisc) w,
            fun i => fderiv ℝ (poincareDensity Ω) w (frameVec i),
            fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) w (frameVec i),
            fun i => fderiv ℝ u w (frameVec i),
            fun i j => fderiv ℝ (fderiv ℝ u) w (frameVec i) (frameVec j)) ∈
          {J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) |
            0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1} →
        meanCurvUp Ω u w =
          Ψ (u w, poincareDensity Ω w, schwarzian (Function.invFunOn f unitDisc) w,
            fun i => fderiv ℝ (poincareDensity Ω) w (frameVec i),
            fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) w (frameVec i),
            fun i => fderiv ℝ u w (frameVec i),
            fun i j => fderiv ℝ (fderiv ℝ u) w (frameVec i) (frameVec j)) := by
  -- the metric `M(τ, λ, S)` and the integrands on `K = ℝ × ℝ × ℂ × ℝ²`, `k = (τ, λ, S, p)`
  obtain ⟨A, hA⟩ : ∃ A : ℝ × ℝ × ℂ × (Fin 2 → ℝ) → ℝ, ∀ k, A k =
      (Real.cosh k.1 ^ 2 + (k.2.2.1.re ^ 2 + k.2.2.1.im ^ 2) / k.2.1 ^ 4 * Real.exp k.1 ^ 2) *
        k.2.1 ^ 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ × ℝ × ℂ × (Fin 2 → ℝ) → ℝ, ∀ k,
      B k = 2 * Real.cosh k.1 * Real.exp k.1 := ⟨_, fun _ => rfl⟩
  obtain ⟨Mf, hMf⟩ : ∃ Mf : ℝ × ℝ × ℂ × (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ, ∀ k, Mf k =
      !![A k + B k * k.2.2.1.re, -(B k * k.2.2.1.im);
        -(B k * k.2.2.1.im), A k - B k * k.2.2.1.re] := ⟨_, fun _ => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ × ℝ × ℂ × (Fin 2 → ℝ) → ℝ, ∀ k, D k =
      A k ^ 2 - B k ^ 2 * (k.2.2.1.re ^ 2 + k.2.2.1.im ^ 2) := ⟨_, fun _ => rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Fin 2 → ℝ × ℝ × ℂ × (Fin 2 → ℝ) → ℝ, ∀ i k, N i k =
      ![(A k - B k * k.2.2.1.re) * k.2.2.2 0 + B k * k.2.2.1.im * k.2.2.2 1,
        B k * k.2.2.1.im * k.2.2.2 0 + (A k + B k * k.2.2.1.re) * k.2.2.2 1] i :=
    ⟨_, fun _ _ => rfl⟩
  have hdet : ∀ k, (Mf k).det = D k := by
    intro k
    rw [hMf, Matrix.det_fin_two_of, hD]
    ring
  have hinvk : ∀ k i, ((Mf k)⁻¹ *ᵥ k.2.2.2) i = (D k)⁻¹ * N i k := by
    intro k i
    rw [Matrix.inv_def, Ring.inverse_eq_inv', hdet, Matrix.adjugate_fin_two, hMf, hN]
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  have hq : ∀ k, k.2.2.2 ⬝ᵥ ((Mf k)⁻¹ *ᵥ k.2.2.2) =
      (D k)⁻¹ * (k.2.2.2 0 * N 0 k + k.2.2.2 1 * N 1 k) := by
    intro k
    rw [dotProduct, Fin.sum_univ_two, hinvk, hinvk]
    ring
  -- positivity on `O' = {0 < λ, ‖S‖ e^τ < λ² cosh τ}`
  have hOk : ∀ k : ℝ × ℝ × ℂ × (Fin 2 → ℝ), 0 < k.2.1 →
      ‖k.2.2.1‖ * Real.exp k.1 < k.2.1 ^ 2 * Real.cosh k.1 → 0 < A k ∧ 0 < D k := by
    intro k hl hlt
    have hc := Real.cosh_pos k.1
    have hn : ‖k.2.2.1‖ ^ 2 = k.2.2.1.re ^ 2 + k.2.2.1.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have h2 : (‖k.2.2.1‖ * Real.exp k.1) ^ 2 < (k.2.1 ^ 2 * Real.cosh k.1) ^ 2 :=
      pow_lt_pow_left₀ hlt (by positivity) two_ne_zero
    have hAe : A k = Real.cosh k.1 ^ 2 * k.2.1 ^ 2 +
        (k.2.2.1.re ^ 2 + k.2.2.1.im ^ 2) * Real.exp k.1 ^ 2 / k.2.1 ^ 2 := by
      rw [hA]
      field_simp
    have hDe : D k = (Real.cosh k.1 ^ 2 * k.2.1 ^ 2 -
        (k.2.2.1.re ^ 2 + k.2.2.1.im ^ 2) * Real.exp k.1 ^ 2 / k.2.1 ^ 2) ^ 2 := by
      rw [hD, hAe, hB]
      field_simp
      ring
    have hpos : 0 < Real.cosh k.1 ^ 2 * k.2.1 ^ 2 -
        (k.2.2.1.re ^ 2 + k.2.2.1.im ^ 2) * Real.exp k.1 ^ 2 / k.2.1 ^ 2 := by
      rw [sub_pos, div_lt_iff₀ (by positivity), ← hn]
      nlinarith [h2]
    refine ⟨?_, ?_⟩
    · have h3 := mul_pos (pow_pos hc 2) (pow_pos hl 2)
      have h4 : 0 ≤ (k.2.2.1.re ^ 2 + k.2.2.1.im ^ 2) * Real.exp k.1 ^ 2 / k.2.1 ^ 2 := by
        positivity
      rw [hAe]
      linarith
    · rw [hDe]
      exact pow_pos hpos 2
  -- smoothness of the pieces
  have cτ : ContDiff ℝ ∞ (fun k : ℝ × ℝ × ℂ × (Fin 2 → ℝ) => k.1) := contDiff_fst
  have cl : ContDiff ℝ ∞ (fun k : ℝ × ℝ × ℂ × (Fin 2 → ℝ) => k.2.1) := contDiff_snd.fst
  have cS : ContDiff ℝ ∞ (fun k : ℝ × ℝ × ℂ × (Fin 2 → ℝ) => k.2.2.1) := contDiff_snd.snd.fst
  have cr : ContDiff ℝ ∞ (fun k : ℝ × ℝ × ℂ × (Fin 2 → ℝ) => k.2.2.1.re) :=
    Complex.reCLM.contDiff.comp cS
  have cm : ContDiff ℝ ∞ (fun k : ℝ × ℝ × ℂ × (Fin 2 → ℝ) => k.2.2.1.im) :=
    Complex.imCLM.contDiff.comp cS
  have cp : ∀ j : Fin 2, ContDiff ℝ ∞ (fun k : ℝ × ℝ × ℂ × (Fin 2 → ℝ) => k.2.2.2 j) :=
    fun j => by fun_prop
  have cc : ContDiff ℝ ∞ (fun k : ℝ × ℝ × ℂ × (Fin 2 → ℝ) => Real.cosh k.1) :=
    Real.contDiff_cosh.comp cτ
  have ce : ContDiff ℝ ∞ (fun k : ℝ × ℝ × ℂ × (Fin 2 → ℝ) => Real.exp k.1) :=
    Real.contDiff_exp.comp cτ
  have hBC : ContDiff ℝ ∞ B := by
    rw [show B = _ from funext hB]
    exact (contDiff_const.mul cc).mul ce
  have hAC : ∀ k : ℝ × ℝ × ℂ × (Fin 2 → ℝ), k.2.1 ≠ 0 → ContDiffAt ℝ ∞ A k := by
    intro k hk
    exact (((cc.pow 2).contDiffAt.add ((((cr.pow 2).add (cm.pow 2)).contDiffAt.div
      (cl.pow 4).contDiffAt (pow_ne_zero 4 hk)).mul (ce.pow 2).contDiffAt)).mul
        (cl.pow 2).contDiffAt).congr_of_eventuallyEq (Filter.Eventually.of_forall hA)
  have hNC : ∀ (i : Fin 2) (k : ℝ × ℝ × ℂ × (Fin 2 → ℝ)), k.2.1 ≠ 0 →
      ContDiffAt ℝ ∞ (N i) k := by
    intro i k hk
    have h0 := (((hAC k hk).sub (hBC.mul cr).contDiffAt).mul (cp 0).contDiffAt).add
      ((hBC.mul cm).mul (cp 1)).contDiffAt
    have h1 := ((hBC.mul cm).mul (cp 0)).contDiffAt.add
      (((hAC k hk).add (hBC.mul cr).contDiffAt).mul (cp 1).contDiffAt)
    fin_cases i
    · exact h0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun k' => by simp [hN])
    · exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun k' => by simp [hN])
  obtain ⟨O', hO'⟩ : ∃ O' : Set (ℝ × ℝ × ℂ × (Fin 2 → ℝ)),
      O' = {k | 0 < k.2.1 ∧ ‖k.2.2.1‖ * Real.exp k.1 < k.2.1 ^ 2 * Real.cosh k.1} := ⟨_, rfl⟩
  have hO'o : IsOpen O' := by
    have h1 : IsOpen {k : ℝ × ℝ × ℂ × (Fin 2 → ℝ) | 0 < k.2.1} :=
      isOpen_lt continuous_const (by fun_prop)
    have h2 : IsOpen {k : ℝ × ℝ × ℂ × (Fin 2 → ℝ) |
        ‖k.2.2.1‖ * Real.exp k.1 < k.2.1 ^ 2 * Real.cosh k.1} :=
      isOpen_lt (by fun_prop) (by fun_prop)
    rw [hO']
    exact h1.inter h2
  obtain ⟨sd, hsd⟩ : ∃ sd : ℝ × ℝ × ℂ × (Fin 2 → ℝ) → ℝ, ∀ k, sd k = √(Mf k).det :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Wf, hWf⟩ : ∃ Wf : ℝ × ℝ × ℂ × (Fin 2 → ℝ) → ℝ, ∀ k,
      Wf k = √(1 + k.2.2.2 ⬝ᵥ ((Mf k)⁻¹ *ᵥ k.2.2.2)) := ⟨_, fun _ => rfl⟩
  obtain ⟨G0, hG0⟩ : ∃ G0 : ℝ × ℝ × ℂ × (Fin 2 → ℝ) → ℝ, ∀ k, G0 k = sd k / Wf k :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Fin 2 → ℝ × ℝ × ℂ × (Fin 2 → ℝ) → ℝ, ∀ i k,
      F i k = sd k * ((Mf k)⁻¹ *ᵥ k.2.2.2) i / Wf k := ⟨_, fun _ _ => rfl⟩
  have hsmooth : ∀ k ∈ O', k.2.1 ≠ 0 ∧ ContDiffAt ℝ ∞ D k ∧ 0 < D k ∧ ContDiffAt ℝ ∞ sd k ∧
      0 < sd k ∧ ContDiffAt ℝ ∞ Wf k ∧ 0 < Wf k := by
    intro k hk
    rw [hO'] at hk
    obtain ⟨hl, hlt⟩ := hk
    obtain ⟨hA0, hD0⟩ := hOk k hl hlt
    have hDC : ContDiffAt ℝ ∞ D k :=
      (((hAC k hl.ne').pow 2).sub ((hBC.pow 2).contDiffAt.mul
        ((cr.pow 2).add (cm.pow 2)).contDiffAt)).congr_of_eventuallyEq
          (Filter.Eventually.of_forall hD)
    have hQ0 : 0 ≤ k.2.2.2 0 * N 0 k + k.2.2.2 1 * N 1 k := by
      have := s05_ml_quad_nonneg (r := k.2.2.1.re) (m := k.2.2.1.im) (B := B k)
        (p0 := k.2.2.2 0) (p1 := k.2.2.2 1) hA0 (by rw [← hD]; exact hD0)
      simpa [hN] using this
    have hW0 : 0 < 1 + (D k)⁻¹ * (k.2.2.2 0 * N 0 k + k.2.2.2 1 * N 1 k) := by
      have := mul_nonneg (inv_nonneg.2 hD0.le) hQ0
      linarith
    refine ⟨hl.ne', hDC, hD0, (hDC.sqrt hD0.ne').congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun k' => by rw [hsd, hdet]), ?_, ?_, ?_⟩
    · rw [hsd, hdet]
      exact Real.sqrt_pos.2 hD0
    · exact ((contDiffAt_const.add ((hDC.inv hD0.ne').mul (((cp 0).contDiffAt.mul
        (hNC 0 k hl.ne')).add ((cp 1).contDiffAt.mul (hNC 1 k hl.ne'))))).sqrt
          hW0.ne').congr_of_eventuallyEq (Filter.Eventually.of_forall fun k' => by rw [hWf, hq]; rfl)
    · rw [hWf, hq]
      exact Real.sqrt_pos.2 hW0
  have hG0on : ContDiffOn ℝ ∞ G0 O' := fun k hk => by
    obtain ⟨-, -, -, h1, -, h3, h4⟩ := hsmooth k hk
    exact ((h1.div h3 h4.ne').congr_of_eventuallyEq
      (Filter.Eventually.of_forall hG0)).contDiffWithinAt
  have hFon : ∀ i, ContDiffOn ℝ ∞ (F i) O' := fun i k hk => by
    obtain ⟨hl, hDC, hD0, h1, -, h3, h4⟩ := hsmooth k hk
    exact (((h1.mul ((hDC.inv hD0.ne').mul (hNC i k hl))).div h3 h4.ne').congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun k' => by rw [hF, hinvk]; rfl)).contDiffWithinAt
  have hsdon : ContDiffOn ℝ ∞ sd O' := fun k hk => (hsmooth k hk).2.2.2.1.contDiffWithinAt
  -- the universal `Ψ`
  set O := {J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) |
    0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1} with hOdef
  have hκC : ContDiff ℝ ∞ (fun J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) ×
      (Fin 2 → Fin 2 → ℝ) => ((J.1, J.2.1, J.2.2.1, J.2.2.2.2.2.1) :
        ℝ × ℝ × ℂ × (Fin 2 → ℝ))) := by fun_prop
  have hmaps : MapsTo (fun J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) ×
      (Fin 2 → Fin 2 → ℝ) => ((J.1, J.2.1, J.2.2.1, J.2.2.2.2.2.1) :
        ℝ × ℝ × ℂ × (Fin 2 → ℝ))) O O' := by
    intro J hJ
    rw [hO']
    exact hJ
  have hsdO := hsdon.comp hκC.contDiffOn hmaps
  have hne : ∀ J ∈ O, sd (J.1, J.2.1, J.2.2.1, J.2.2.2.2.2.1) ≠ 0 := fun J hJ =>
    (hsmooth _ (hmaps hJ)).2.2.2.2.1.ne'
  have hG0O := ((hG0on.fderiv_of_isOpen hO'o (m := ∞) (le_of_eq ENat.coe_top_add_one)).comp
    hκC.contDiffOn hmaps).clm_apply
      (contDiffOn_const (c := ((1 : ℝ), (0 : ℝ × ℂ × (Fin 2 → ℝ)))))
  have hFO : ∀ i : Fin 2, ContDiffOn ℝ ∞ (fun J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) ×
      (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) => fderiv ℝ (F i) (J.1, J.2.1, J.2.2.1, J.2.2.2.2.2.1)
        ((0 : ℝ), J.2.2.2.1 i, J.2.2.2.2.1 i, J.2.2.2.2.2.2 i)) O := fun i =>
    (((hFon i).fderiv_of_isOpen hO'o (m := ∞) (le_of_eq ENat.coe_top_add_one)).comp
      hκC.contDiffOn hmaps).clm_apply
        (by fun_prop : ContDiff ℝ ∞ (fun J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) ×
          (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) =>
            ((0 : ℝ), J.2.2.2.1 i, J.2.2.2.2.1 i, J.2.2.2.2.2.2 i))).contDiffOn
  refine ⟨fun J => -(1 / 2) *
    (fderiv ℝ G0 (J.1, J.2.1, J.2.2.1, J.2.2.2.2.2.1) ((1 : ℝ), (0 : ℝ × ℂ × (Fin 2 → ℝ))) /
        sd (J.1, J.2.1, J.2.2.1, J.2.2.2.2.2.1) -
      (∑ i : Fin 2, fderiv ℝ (F i) (J.1, J.2.1, J.2.2.1, J.2.2.2.2.2.1)
        ((0 : ℝ), J.2.2.2.1 i, J.2.2.2.2.1 i, J.2.2.2.2.2.2 i)) /
        sd (J.1, J.2.1, J.2.2.1, J.2.2.2.2.2.1)),
    contDiffOn_const.mul ((hG0O.div hsdO hne).sub
      ((ContDiffOn.sum fun i _ => hFO i).div hsdO hne)), ?_⟩
  intro Ω Ωs hJ f hf U hU hUΩ hUs u hu w hw hO
  have hΩo : IsOpen Ω := s05_jordan_isOpen hJ
  have hwΩ := hUΩ hw
  have hmet : ∀ x ∈ U, ∀ (τ : ℝ) (p : Fin 2 → ℝ), graphMetric Ω x τ =
      Mf (τ, poincareDensity Ω x, schwarzian (Function.invFunOn f unitDisc) x, p) := by
    intro x hx τ p
    have e : (‖schwarzian (Function.invFunOn f unitDisc) x‖ / poincareDensity Ω x ^ 2) ^ 2 =
        ((schwarzian (Function.invFunOn f unitDisc) x).re ^ 2 +
          (schwarzian (Function.invFunOn f unitDisc) x).im ^ 2) / poincareDensity Ω x ^ 4 := by
      rw [div_pow, Complex.sq_norm, Complex.normSq_apply, ← pow_mul]
      ring
    rw [s05_ml_metric hJ hf (hUΩ hx) (hUs x hx).ne τ, e, hMf, hA, hB]
  have hSd : ∀ x ∈ U, ∀ (τ : ℝ) (p : Fin 2 → ℝ), graphSdet Ω x τ =
      sd (τ, poincareDensity Ω x, schwarzian (Function.invFunOn f unitDisc) x, p) := by
    intro x hx τ p
    rw [graphSdet, hmet x hx τ p]
    exact (hsd _).symm
  have hWw : ∀ x ∈ U, ∀ τ : ℝ, graphW Ω u x τ =
      Wf (τ, poincareDensity Ω x, schwarzian (Function.invFunOn f unitDisc) x, gradCoords u x) := by
    intro x hx τ
    rw [graphW, hmet x hx τ (gradCoords u x)]
    exact (hWf (τ, poincareDensity Ω x, schwarzian (Function.invFunOn f unitDisc) x,
      gradCoords u x)).symm
  have hFl : ∀ x ∈ U, ∀ (τ : ℝ) (i : Fin 2), graphFlux Ω u τ x i =
      F i (τ, poincareDensity Ω x, schwarzian (Function.invFunOn f unitDisc) x, gradCoords u x) := by
    intro x hx τ i
    simp only [graphFlux]
    rw [hSd x hx τ (gradCoords u x), hmet x hx τ (gradCoords u x), hWw x hx τ]
    exact (hF i (τ, poincareDensity Ω x, schwarzian (Function.invFunOn f unitDisc) x,
      gradCoords u x)).symm
  have hκO : ((u w, poincareDensity Ω w, schwarzian (Function.invFunOn f unitDisc) w,
      gradCoords u w) : ℝ × ℝ × ℂ × (Fin 2 → ℝ)) ∈ O' := by
    rw [hO']
    exact hO
  -- the `τ`-part
  have hderiv : deriv (fun τ => graphSdet Ω w τ / graphW Ω u w τ) (u w) =
      fderiv ℝ G0 (u w, poincareDensity Ω w, schwarzian (Function.invFunOn f unitDisc) w,
        gradCoords u w) ((1 : ℝ), (0 : ℝ × ℂ × (Fin 2 → ℝ))) := by
    have e : (fun τ => graphSdet Ω w τ / graphW Ω u w τ) = fun τ => G0 (τ, poincareDensity Ω w,
        schwarzian (Function.invFunOn f unitDisc) w, gradCoords u w) := by
      funext τ
      rw [hSd w hw τ (gradCoords u w), hWw w hw τ, hG0]
    have hG0d := (((hG0on _ hκO).contDiffAt (hO'o.mem_nhds hκO)).differentiableAt
      (by simp)).hasFDerivAt
    rw [e]
    exact (hG0d.comp_hasDerivAt (u w) ((hasDerivAt_id' (u w)).prodMk
      (hasDerivAt_const (u w) _))).deriv
  -- the flux part
  have hlC : ContDiffAt ℝ ∞ (poincareDensity Ω) w :=
    (s02_contDiffOn_poincareDensity hf).contDiffAt (hΩo.mem_nhds hwΩ)
  have hSC : ContDiffAt ℝ ∞ (schwarzian (Function.invFunOn f unitDisc)) w :=
    (s02_contDiffOn_invFun hf).2.2.2.contDiffAt (hΩo.mem_nhds hwΩ)
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) w :=
    ((hu.contDiffAt (hU.mem_nhds hw)).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)
  have hγ := (hasFDerivAt_const (u w) w).prodMk ((hlC.differentiableAt (by simp)).hasFDerivAt.prodMk
    ((hSC.differentiableAt (by simp)).hasFDerivAt.prodMk (hasFDerivAt_pi.2 fun j : Fin 2 =>
      hdu.hasFDerivAt.clm_apply (hasFDerivAt_const (frameVec j) w))))
  have hflux : ∀ i : Fin 2, fderiv ℝ (fun x => graphFlux Ω u (u w) x i) w (frameVec i) =
      fderiv ℝ (F i) (u w, poincareDensity Ω w, schwarzian (Function.invFunOn f unitDisc) w,
        gradCoords u w) ((0 : ℝ), fderiv ℝ (poincareDensity Ω) w (frameVec i),
          fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) w (frameVec i),
          fun j => fderiv ℝ (fderiv ℝ u) w (frameVec i) (frameVec j)) := by
    intro i
    have hFd := ((((hFon i) _ hκO).contDiffAt (hO'o.mem_nhds hκO)).differentiableAt
      (by simp)).hasFDerivAt
    have h' := (hFd.comp w hγ).congr_of_eventuallyEq (f₁ := fun x => graphFlux Ω u (u w) x i)
      (by filter_upwards [hU.mem_nhds hw] with x hx; exact hFl x hx (u w) i)
    rw [h'.fderiv]
    simp
  rw [meanCurvUp, hderiv, Finset.sum_congr rfl fun i _ => hflux i,
    hSd w hw (u w) (gradCoords u w)]
  rfl

/-- B1 helper (ML2): linearization.  For any `Ψ` as in `s05_ml_jet` (on a fixed `Ω, f, U`),
`D𝒬(v)[u](w) = -2 DΨ(J(v, w))[(u w, 0, 0, 0, 0, Du w, D²u w)]`. -/
theorem s05_ml_lin {Ω : Set ℂ} {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    {Ψ : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) → ℝ}
    (hΨ : ContDiffOn ℝ ∞ Ψ
      {J | 0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1})
    (hjet : ∀ u : ℂ → ℝ, ContDiffOn ℝ 2 u U → ∀ w ∈ U,
      (u w, poincareDensity Ω w, schwarzian (Function.invFunOn f unitDisc) w,
          fun i => fderiv ℝ (poincareDensity Ω) w (frameVec i),
          fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) w (frameVec i),
          fun i => fderiv ℝ u w (frameVec i),
          fun i j => fderiv ℝ (fderiv ℝ u) w (frameVec i) (frameVec j)) ∈
        {J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) |
          0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1} →
      meanCurvUp Ω u w =
        Ψ (u w, poincareDensity Ω w, schwarzian (Function.invFunOn f unitDisc) w,
          fun i => fderiv ℝ (poincareDensity Ω) w (frameVec i),
          fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) w (frameVec i),
          fun i => fderiv ℝ u w (frameVec i),
          fun i j => fderiv ℝ (fderiv ℝ u) w (frameVec i) (frameVec j)))
    {v u : ℂ → ℝ} (hv : ContDiffOn ℝ 2 v U) (hu : ContDiffOn ℝ 2 u U) {w : ℂ} (hw : w ∈ U)
    (hO : (v w, poincareDensity Ω w, schwarzian (Function.invFunOn f unitDisc) w,
          fun i => fderiv ℝ (poincareDensity Ω) w (frameVec i),
          fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) w (frameVec i),
          fun i => fderiv ℝ v w (frameVec i),
          fun i j => fderiv ℝ (fderiv ℝ v) w (frameVec i) (frameVec j)) ∈
        {J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) |
          0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1}) :
    graphQDeriv Ω v u w =
      -2 * fderiv ℝ Ψ
        (v w, poincareDensity Ω w, schwarzian (Function.invFunOn f unitDisc) w,
          fun i => fderiv ℝ (poincareDensity Ω) w (frameVec i),
          fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) w (frameVec i),
          fun i => fderiv ℝ v w (frameVec i),
          fun i j => fderiv ℝ (fderiv ℝ v) w (frameVec i) (frameVec j))
        ((u w, (0 : ℝ), (0 : ℂ), (0 : Fin 2 → ℝ), (0 : Fin 2 → ℂ), fun i => fderiv ℝ u w (frameVec i),
          fun i j => fderiv ℝ (fderiv ℝ u) w (frameVec i) (frameVec j)) :
          ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ)) := by
  have hOo := s05_ml_open
  have hvd : ∀ x ∈ U, DifferentiableAt ℝ v x := fun x hx =>
    ((hv.differentiableOn (by simp)) x hx).differentiableAt (hU.mem_nhds hx)
  have hud : ∀ x ∈ U, DifferentiableAt ℝ u x := fun x hx =>
    ((hu.differentiableOn (by simp)) x hx).differentiableAt (hU.mem_nhds hx)
  have hdv : DifferentiableAt ℝ (fderiv ℝ v) w :=
    ((hv.contDiffAt (hU.mem_nhds hw)).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) w :=
    ((hu.contDiffAt (hU.mem_nhds hw)).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)
  set J0 : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) :=
    (v w, poincareDensity Ω w, schwarzian (Function.invFunOn f unitDisc) w,
      fun i => fderiv ℝ (poincareDensity Ω) w (frameVec i),
      fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) w (frameVec i),
      fun i => fderiv ℝ v w (frameVec i),
      fun i j => fderiv ℝ (fderiv ℝ v) w (frameVec i) (frameVec j)) with hJ0
  set d : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) :=
    (u w, (0 : ℝ), (0 : ℂ), (0 : Fin 2 → ℝ), (0 : Fin 2 → ℂ), fun i => fderiv ℝ u w (frameVec i),
      fun i j => fderiv ℝ (fderiv ℝ u) w (frameVec i) (frameVec j)) with hd
  -- the jet of `v + θ u` is the line `J0 + θ d`
  have hjeq : ∀ θ : ℝ, ((((v + θ • u) w, poincareDensity Ω w,
      schwarzian (Function.invFunOn f unitDisc) w,
      fun i => fderiv ℝ (poincareDensity Ω) w (frameVec i),
      fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) w (frameVec i),
      fun i => fderiv ℝ (v + θ • u) w (frameVec i),
      fun i j => fderiv ℝ (fderiv ℝ (v + θ • u)) w (frameVec i) (frameVec j))) :
        ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ)) =
      J0 + θ • d := by
    intro θ
    have h6 : fderiv ℝ (v + θ • u) w = fderiv ℝ v w + θ • fderiv ℝ u w :=
      ((hvd w hw).hasFDerivAt.add ((hud w hw).hasFDerivAt.const_smul θ)).fderiv
    have h7 : fderiv ℝ (fderiv ℝ (v + θ • u)) w =
        fderiv ℝ (fderiv ℝ v) w + θ • fderiv ℝ (fderiv ℝ u) w := by
      refine ((hdv.hasFDerivAt.add (hdu.hasFDerivAt.const_smul θ)).congr_of_eventuallyEq
        ?_).fderiv
      filter_upwards [hU.mem_nhds hw] with x hx
      exact ((hvd x hx).hasFDerivAt.add ((hud x hx).hasFDerivAt.const_smul θ)).fderiv
    rw [hJ0, hd, h6, h7]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_
      (Prod.ext ?_ ?_)))))
    all_goals first
      | (simp; done)
      | (funext i; simp; done)
      | (funext i j; simp)
  have hJ0O : J0 ∈ {J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) |
      0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1} := hO
  have hline : HasDerivAt (fun θ : ℝ => J0 + θ • d) d 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const d).const_add J0
  have hev : ∀ᶠ θ in 𝓝 (0 : ℝ), J0 + θ • d ∈
      {J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) |
        0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1} :=
    hline.continuousAt.eventually_mem (hOo.mem_nhds (by rw [zero_smul, add_zero]; exact hJ0O))
  have hΨd : HasFDerivAt Ψ (fderiv ℝ Ψ J0) J0 :=
    ((hΨ.contDiffAt (hOo.mem_nhds hJ0O)).differentiableAt (by simp)).hasFDerivAt
  have hD := ((hΨd.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)).const_sub
    (schwarzNorm Ω w ^ 2 / (1 - schwarzNorm Ω w ^ 2))).const_mul 2
  have hEq : (fun θ : ℝ => graphQ Ω (v + θ • u) w) =ᶠ[𝓝 0] fun θ =>
      2 * (schwarzNorm Ω w ^ 2 / (1 - schwarzNorm Ω w ^ 2) - Ψ (J0 + θ • d)) := by
    filter_upwards [hev] with θ hθ
    have hsm : ContDiffOn ℝ 2 (v + θ • u) U := hv.add (hu.const_smul θ)
    have h := hjet (v + θ • u) hsm w hw (by rw [hjeq θ]; exact hθ)
    rw [graphQ, h, hjeq θ]
  rw [graphQDeriv, (hD.congr_of_eventuallyEq hEq).deriv]
  ring

/-- B1 helper (ML3a): `∇φ = ∇λ/λ`, `φ = log λ`, in jet form. -/
theorem s05_ml_logGrad {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {w : ℂ}
    (hw : w ∈ Ω) :
    logDensityGrad Ω w =
      (((fderiv ℝ (poincareDensity Ω) w 1 : ℝ) : ℂ) +
          ((fderiv ℝ (poincareDensity Ω) w I : ℝ) : ℂ) * I) / ((poincareDensity Ω w : ℝ) : ℂ) := by
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hw
  have hd : DifferentiableAt ℝ (poincareDensity Ω) w :=
    ((s02_contDiffOn_poincareDensity hf).contDiffAt (hΩo.mem_nhds hw)).differentiableAt (by simp)
  rw [logDensityGrad, fderiv.log hd hl.ne']
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- B1 helper (ML3b): `D²u(X, Y) = ∇²u(X, Y) + Du(Γ(X, Y))` (`s05_rhoHess_eq`). -/
theorem s05_ml_hess (Ω : Set ℂ) {u : ℂ → ℝ} {w : ℂ} (hu : ContDiffAt ℝ 2 u w) (X Y : ℂ) :
    fderiv ℝ (fderiv ℝ u) w X Y =
      rhoHess Ω u w ![X, Y] + fderiv ℝ u w (rhoChristoffel Ω w X Y) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) w :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have e : fderiv ℝ (fun x => fderiv ℝ u x Y) w X = fderiv ℝ (fderiv ℝ u) w X Y := by
    rw [fderiv_clm_apply hd (differentiableAt_const Y)]
    simp
  rw [s05_rhoHess_eq, e]
  ring

/-- **B1 (W-MC-lin), frozen target.**  The linearization `D𝒬(v)[u]` at a general `v` is the
operator `ellOp` with symmetric coefficients `Φa, Φb, Φc` of the jet `J(v, w)`, universal (not
depending on `Ω`, `f`, `v`) and smooth on `O`. -/
theorem s05_ml_rep :
    ∃ (Φa : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) →
          Matrix (Fin 2) (Fin 2) ℝ)
      (Φb : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) →
          Fin 2 → ℝ)
      (Φc : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) → ℝ),
      (∀ i j, ContDiffOn ℝ ∞ (fun J => Φa J i j)
        {J | 0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1}) ∧
      (∀ i, ContDiffOn ℝ ∞ (fun J => Φb J i)
        {J | 0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1}) ∧
      ContDiffOn ℝ ∞ Φc
        {J | 0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1} ∧
      (∀ J, (Φa J)ᵀ = Φa J) ∧
      ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω →
      ∀ U : Set ℂ, IsOpen U → U ⊆ Ω → (∀ x ∈ U, schwarzNorm Ω x < 1) →
      ∀ v u : ℂ → ℝ, ContDiffOn ℝ 2 v U → ContDiffOn ℝ 2 u U → ∀ w ∈ U,
        (v w, poincareDensity Ω w, schwarzian (Function.invFunOn f unitDisc) w,
            fun i => fderiv ℝ (poincareDensity Ω) w (frameVec i),
            fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) w (frameVec i),
            fun i => fderiv ℝ v w (frameVec i),
            fun i j => fderiv ℝ (fderiv ℝ v) w (frameVec i) (frameVec j)) ∈
          {J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) |
            0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1} →
        graphQDeriv Ω v u w =
          ellOp Ω
            (fun _ => Φa (v w, poincareDensity Ω w, schwarzian (Function.invFunOn f unitDisc) w,
              fun i => fderiv ℝ (poincareDensity Ω) w (frameVec i),
              fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) w (frameVec i),
              fun i => fderiv ℝ v w (frameVec i),
              fun i j => fderiv ℝ (fderiv ℝ v) w (frameVec i) (frameVec j)))
            (fun _ => Φb (v w, poincareDensity Ω w, schwarzian (Function.invFunOn f unitDisc) w,
              fun i => fderiv ℝ (poincareDensity Ω) w (frameVec i),
              fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) w (frameVec i),
              fun i => fderiv ℝ v w (frameVec i),
              fun i j => fderiv ℝ (fderiv ℝ v) w (frameVec i) (frameVec j)))
            (fun _ => Φc (v w, poincareDensity Ω w, schwarzian (Function.invFunOn f unitDisc) w,
              fun i => fderiv ℝ (poincareDensity Ω) w (frameVec i),
              fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) w (frameVec i),
              fun i => fderiv ℝ v w (frameVec i),
              fun i j => fderiv ℝ (fderiv ℝ v) w (frameVec i) (frameVec j)))
            u w := by
  obtain ⟨Ψ, hΨ, hjet⟩ := s05_ml_jet
  have hOo := s05_ml_open
  have hΨ' := hΨ.fderiv_of_isOpen hOo (m := ∞) (le_of_eq ENat.coe_top_add_one)
  -- the coordinate directions of the jet space
  obtain ⟨eτ, heτ⟩ : ∃ eτ : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) ×
      (Fin 2 → Fin 2 → ℝ), eτ = ((1 : ℝ), (0 : ℝ), (0 : ℂ), (0 : Fin 2 → ℝ), (0 : Fin 2 → ℂ),
        (0 : Fin 2 → ℝ), (0 : Fin 2 → Fin 2 → ℝ)) := ⟨_, rfl⟩
  obtain ⟨ep, hep⟩ : ∃ ep : Fin 2 → ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) ×
      (Fin 2 → Fin 2 → ℝ), ∀ k, ep k = ((0 : ℝ), (0 : ℝ), (0 : ℂ), (0 : Fin 2 → ℝ),
        (0 : Fin 2 → ℂ), (Pi.single k (1 : ℝ) : Fin 2 → ℝ), (0 : Fin 2 → Fin 2 → ℝ)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨eH, heH⟩ : ∃ eH : Fin 2 → Fin 2 → ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) ×
      (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ), ∀ i j, eH i j = ((0 : ℝ), (0 : ℝ), (0 : ℂ),
        (0 : Fin 2 → ℝ), (0 : Fin 2 → ℂ), (0 : Fin 2 → ℝ),
        (Pi.single i (Pi.single j (1 : ℝ)) : Fin 2 → Fin 2 → ℝ)) := ⟨_, fun _ _ => rfl⟩
  have hC : ∀ e : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ),
      ContDiffOn ℝ ∞ (fun J => fderiv ℝ Ψ J e)
        {J | 0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1} := fun e =>
    hΨ'.clm_apply contDiffOn_const
  have hgC : ∀ i : Fin 2, ContDiffOn ℝ ∞
      (fun J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) =>
        J.2.2.2.1 i / J.2.1)
      {J | 0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1} := fun i =>
    (by fun_prop : ContDiff ℝ ∞ fun J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) ×
      (Fin 2 → Fin 2 → ℝ) => J.2.2.2.1 i).contDiffOn.div
      (by fun_prop : ContDiff ℝ ∞ fun J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) ×
        (Fin 2 → Fin 2 → ℝ) => J.2.1).contDiffOn (fun J hJ => hJ.1.ne')
  -- `a = 2 sym ∂_{D²}Ψ`, `b = 2 ∂_{Du}Ψ + Σ a^{ij} Γ_{ij}`, `c = -2 ∂_τΨ`
  refine ⟨fun J => Matrix.of fun i j => fderiv ℝ Ψ J (eH i j) + fderiv ℝ Ψ J (eH j i),
    fun J k => 2 * fderiv ℝ Ψ J (ep k) + ∑ i : Fin 2, ∑ j : Fin 2,
      (fderiv ℝ Ψ J (eH i j) + fderiv ℝ Ψ J (eH j i)) *
        (J.2.2.2.1 i / J.2.1 * (if j = k then 1 else 0) +
          J.2.2.2.1 j / J.2.1 * (if i = k then 1 else 0) -
          (if i = j then 1 else 0) * (J.2.2.2.1 k / J.2.1)),
    fun J => -2 * fderiv ℝ Ψ J eτ, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [Matrix.of_apply]
    exact (hC _).add (hC _)
  · intro k
    exact (contDiffOn_const.mul (hC _)).add (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
      ((hC _).add (hC _)).mul ((((hgC i).mul contDiffOn_const).add
        ((hgC j).mul contDiffOn_const)).sub (contDiffOn_const.mul (hgC k))))
  · exact contDiffOn_const.mul (hC _)
  · intro J
    ext i j
    simp [add_comm]
  intro Ω Ωs hJ f hf U hU hUΩ hUs v u hv hu w hw hO
  rw [s05_ml_lin hU hΨ (hjet Ω Ωs hJ f hf U hU hUΩ hUs) hv hu hw hO]
  have hwΩ := hUΩ hw
  have huC : ContDiffAt ℝ 2 u w := hu.contDiffAt (hU.mem_nhds hw)
  have hsym := huC.isSymmSndFDerivAt (by simp)
  -- the direction `(u, 0, 0, 0, 0, Du, D²u)` in coordinates
  have hdec : ((u w, (0 : ℝ), (0 : ℂ), (0 : Fin 2 → ℝ), (0 : Fin 2 → ℂ),
      fun i => fderiv ℝ u w (frameVec i),
      fun i j => fderiv ℝ (fderiv ℝ u) w (frameVec i) (frameVec j)) :
        ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ)) =
      u w • eτ + ∑ k : Fin 2, fderiv ℝ u w (frameVec k) • ep k +
        ∑ i : Fin 2, ∑ j : Fin 2, fderiv ℝ (fderiv ℝ u) w (frameVec i) (frameVec j) • eH i j := by
    simp only [heτ, hep, heH]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_
      (Prod.ext ?_ ?_)))))
    all_goals first
      | (simp [Fin.sum_univ_two]; done)
      | (funext i; fin_cases i <;> simp [Fin.sum_univ_two]; done)
      | (funext i j; fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two])
  -- `∇²u = D²u - Du(Γ)` with `Γ` from `Dλ/λ`
  have hG : logDensityGrad Ω w =
      ((fderiv ℝ (poincareDensity Ω) w 1 / poincareDensity Ω w : ℝ) : ℂ) +
        ((fderiv ℝ (poincareDensity Ω) w I / poincareDensity Ω w : ℝ) : ℂ) * I := by
    rw [s05_ml_logGrad hf hwΩ]
    push_cast
    ring
  have hDu : ∀ z : ℂ, fderiv ℝ u w z = z.re * fderiv ℝ u w 1 + z.im * fderiv ℝ u w I := by
    intro z
    have hz : z = z.re • (1 : ℂ) + z.im • I := by apply Complex.ext <;> simp
    conv_lhs => rw [hz]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hH : ∀ i j : Fin 2, rhoHess Ω u w ![frameVec i, frameVec j] =
      fderiv ℝ (fderiv ℝ u) w (frameVec i) (frameVec j) - ∑ k : Fin 2,
        (fderiv ℝ (poincareDensity Ω) w (frameVec i) / poincareDensity Ω w *
            (if j = k then 1 else 0) +
          fderiv ℝ (poincareDensity Ω) w (frameVec j) / poincareDensity Ω w *
            (if i = k then 1 else 0) -
          (if i = j then 1 else 0) *
            (fderiv ℝ (poincareDensity Ω) w (frameVec k) / poincareDensity Ω w)) *
          fderiv ℝ u w (frameVec k) := by
    intro i j
    rw [s05_ml_hess Ω huC (frameVec i) (frameVec j), hDu]
    fin_cases i <;> fin_cases j <;>
      simp [rhoChristoffel, hG, frameVec, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]
  rw [hdec]
  simp only [map_add, map_smul, smul_eq_mul, ellOp, Fin.sum_univ_two, Matrix.of_apply,
    hH]
  rw [hsym (frameVec 1) (frameVec 0)]
  simp
  ring

/-- **B1, uniform form on `G₀`** (for Lemma 5.7 (b)): for every `η ≤ η₀`, `R ≥ R₁`, the family
`D𝒬(θ t)`, `θ ∈ (-1/2, 3/2)`, `t = slabTop`, is `ellOp` with symmetric coefficients jointly smooth
in `(θ, w)` on `(-1/2, 3/2) × G₀` (from `s05_ml_rep`, `s04_sl_eq_def_N_unif`, `s05_go_s_lt`). -/
theorem s05_ml_family : ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ R₁ : ℝ, ∀ η R : ℝ, 0 < η → η ≤ η₀ → R₁ ≤ R →
      ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
        ∃ (a : ℝ × ℂ → Matrix (Fin 2) (Fin 2) ℝ) (b : ℝ × ℂ → Fin 2 → ℝ) (c : ℝ × ℂ → ℝ),
          (∀ i j, ContDiffOn ℝ ∞ (fun p => a p i j)
            (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ goodSet Ω Ωs η R)) ∧
          (∀ i, ContDiffOn ℝ ∞ (fun p => b p i)
            (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ goodSet Ω Ωs η R)) ∧
          ContDiffOn ℝ ∞ c (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ goodSet Ω Ωs η R) ∧
          (∀ p, (a p)ᵀ = a p) ∧
          ∀ θ ∈ Ioo (-1 / 2 : ℝ) (3 / 2), ∀ D : Set ℂ, IsOpen D → D ⊆ goodSet Ω Ωs η R →
            ∀ u : ℂ → ℝ, ContDiffOn ℝ 2 u D → ∀ w ∈ D,
              graphQDeriv Ω (θ • slabTop Ω Ωs) u w =
                ellOp Ω (fun x => a (θ, x)) (fun x => b (θ, x)) (fun x => c (θ, x)) u w := by
  intro K hK ε hε hε4
  obtain ⟨η₀, hη₀, R₁, hN⟩ := s04_sl_eq_def_N_unif K hK ε hε hε4
  obtain ⟨Φa, Φb, Φc, hΦa, hΦb, hΦc, hsymm, hrep⟩ := s05_ml_rep
  refine ⟨min η₀ (1 / 4), lt_min hη₀ (by norm_num), max R₁ 0, ?_⟩
  intro η R hη hηle hR Ω Ωs hK' hL
  have hJ := s03_b0_jordanPair hK'
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  have hΩo : IsOpen Ω := s05_jordan_isOpen hJ
  obtain ⟨hGo, htC, -, hslab⟩ :=
    hN η R hη (hηle.trans (min_le_left _ _)) ((le_max_left _ _).trans hR) Ω Ωs hK' hL
  have hGΩ : goodSet Ω Ωs η R ⊆ Ω := fun x hx => hx.1
  have hR0 : 0 ≤ R := (le_max_right _ _).trans hR
  have hsη : ∀ x ∈ goodSet Ω Ωs η R, schwarzNorm Ω x < 1 / 4 := fun x hx =>
    (s05_go_s_lt hJ hR0 hx).trans_le (hηle.trans (min_le_right _ _))
  -- the jet of `θ t` at `x`, as a function of `p = (θ, x)`
  obtain ⟨jm, hjm⟩ : ∃ jm : ℝ × ℂ → ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) ×
      (Fin 2 → Fin 2 → ℝ), ∀ p, jm p =
        (p.1 * slabTop Ω Ωs p.2, poincareDensity Ω p.2,
          schwarzian (Function.invFunOn f unitDisc) p.2,
          fun i => fderiv ℝ (poincareDensity Ω) p.2 (frameVec i),
          fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) p.2 (frameVec i),
          fun i => p.1 * fderiv ℝ (slabTop Ω Ωs) p.2 (frameVec i),
          fun i j => p.1 * fderiv ℝ (fderiv ℝ (slabTop Ω Ωs)) p.2 (frameVec i) (frameVec j)) :=
    ⟨fun p => (p.1 * slabTop Ω Ωs p.2, poincareDensity Ω p.2,
      schwarzian (Function.invFunOn f unitDisc) p.2,
      fun i => fderiv ℝ (poincareDensity Ω) p.2 (frameVec i),
      fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) p.2 (frameVec i),
      fun i => p.1 * fderiv ℝ (slabTop Ω Ωs) p.2 (frameVec i),
      fun i j => p.1 * fderiv ℝ (fderiv ℝ (slabTop Ω Ωs)) p.2 (frameVec i) (frameVec j)),
      fun _ => rfl⟩
  have hlamC := s02_contDiffOn_poincareDensity hf
  have hSC := (s02_contDiffOn_invFun hf).2.2.2
  have hlam' := hlamC.fderiv_of_isOpen hΩo (m := ∞) (le_of_eq ENat.coe_top_add_one)
  have hS' := hSC.fderiv_of_isOpen hΩo (m := ∞) (le_of_eq ENat.coe_top_add_one)
  have ht' := htC.fderiv_of_isOpen hGo (m := ∞) (le_of_eq ENat.coe_top_add_one)
  have ht'' := ht'.fderiv_of_isOpen hGo (m := ∞) (le_of_eq ENat.coe_top_add_one)
  have hmG : MapsTo (fun p : ℝ × ℂ => p.2) (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ goodSet Ω Ωs η R)
      (goodSet Ω Ωs η R) := fun p hp => hp.2
  have hmΩ : MapsTo (fun p : ℝ × ℂ => p.2) (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ goodSet Ω Ωs η R) Ω :=
    fun p hp => hGΩ hp.2
  have hsn : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => p.2)
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ goodSet Ω Ωs η R) := contDiff_snd.contDiffOn
  have hfs : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => p.1)
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ goodSet Ω Ωs η R) := contDiff_fst.contDiffOn
  have hjmC : ContDiffOn ℝ ∞ jm (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ goodSet Ω Ωs η R) := by
    have c4 : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => fun i : Fin 2 =>
        fderiv ℝ (poincareDensity Ω) p.2 (frameVec i)) (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ goodSet Ω Ωs η R) :=
      contDiffOn_pi' fun i => (hlam'.comp hsn hmΩ).clm_apply (contDiffOn_const (c := frameVec i))
    have c5 : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => fun i : Fin 2 =>
        fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) p.2 (frameVec i)) (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ goodSet Ω Ωs η R) :=
      contDiffOn_pi' fun i => (hS'.comp hsn hmΩ).clm_apply (contDiffOn_const (c := frameVec i))
    have c6 : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => fun i : Fin 2 =>
        p.1 * fderiv ℝ (slabTop Ω Ωs) p.2 (frameVec i)) (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ goodSet Ω Ωs η R) :=
      contDiffOn_pi' fun i =>
        hfs.mul ((ht'.comp hsn hmG).clm_apply (contDiffOn_const (c := frameVec i)))
    have c7 : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => fun i j : Fin 2 =>
        p.1 * fderiv ℝ (fderiv ℝ (slabTop Ω Ωs)) p.2 (frameVec i) (frameVec j)) (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ goodSet Ω Ωs η R) :=
      contDiffOn_pi' fun i => contDiffOn_pi' fun j => hfs.mul
        (((ht''.comp hsn hmG).clm_apply (contDiffOn_const (c := frameVec i))).clm_apply
          (contDiffOn_const (c := frameVec j)))
    have h := (hfs.mul (htC.comp hsn hmG)).prodMk ((hlamC.comp hsn hmΩ).prodMk
      ((hSC.comp hsn hmΩ).prodMk (c4.prodMk (c5.prodMk (c6.prodMk c7)))))
    exact h.congr fun p _ => hjm p
  -- the jet stays in `O`: `|θ t| < 3/8`, `s < 1/4`, so `s e^{θt} < 1 ≤ cosh(θt)`
  have hmapsO : MapsTo jm (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ goodSet Ω Ωs η R)
      {J | 0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1} := by
    intro p hp
    obtain ⟨hθ, hx⟩ := hp
    have hl := s02_poincareDensity_pos ⟨f, hf⟩ (hGΩ hx)
    obtain ⟨-, ht0, htε, -⟩ := hslab p.2 hx
    have hs0 := (eq_nehari ⟨f, hf⟩ (hGΩ hx)).1
    have hs := hsη p.2 hx
    have hnorm : ‖schwarzian (Function.invFunOn f unitDisc) p.2‖ =
        schwarzNorm Ω p.2 * poincareDensity Ω p.2 ^ 2 := by
      rw [eq_def_s hf (hGΩ hx)]
      field_simp
    have hθt : p.1 * slabTop Ω Ωs p.2 < 1 := by
      nlinarith [mul_pos (sub_pos.2 hθ.2) ht0, hθ.1]
    have he : Real.exp (p.1 * slabTop Ω Ωs p.2) < 3 := by
      have h1 := Real.exp_lt_exp.2 hθt
      have h2 := Real.exp_one_lt_d9
      norm_num at h2
      linarith
    have hc := Real.one_le_cosh (p.1 * slabTop Ω Ωs p.2)
    have hse : schwarzNorm Ω p.2 * Real.exp (p.1 * slabTop Ω Ωs p.2) < 1 := by
      nlinarith [mul_pos (sub_pos.2 hs) (Real.exp_pos (p.1 * slabTop Ω Ωs p.2))]
    have hl2 : 0 < poincareDensity Ω p.2 ^ 2 := by positivity
    rw [hjm]
    refine ⟨hl, ?_⟩
    show ‖schwarzian (Function.invFunOn f unitDisc) p.2‖ * Real.exp (p.1 * slabTop Ω Ωs p.2) <
      poincareDensity Ω p.2 ^ 2 * Real.cosh (p.1 * slabTop Ω Ωs p.2)
    rw [hnorm]
    nlinarith [mul_lt_mul_of_pos_left hse hl2, mul_le_mul_of_nonneg_left hc hl2.le]
  refine ⟨fun p => Φa (jm p), fun p => Φb (jm p), fun p => Φc (jm p),
    fun i j => (hΦa i j).comp hjmC hmapsO, fun i => (hΦb i).comp hjmC hmapsO,
    hΦc.comp hjmC hmapsO, fun p => hsymm _, ?_⟩
  intro θ hθ D hDo hDG u hu w hwD
  have hw := hDG hwD
  have htd : ∀ x ∈ goodSet Ω Ωs η R, DifferentiableAt ℝ (slabTop Ω Ωs) x := fun x hx =>
    ((htC.differentiableOn (by simp)) x hx).differentiableAt (hGo.mem_nhds hx)
  have hdt : DifferentiableAt ℝ (fderiv ℝ (slabTop Ω Ωs)) w :=
    ((htC.contDiffAt (hGo.mem_nhds hw)).fderiv_right (m := ∞)
      (le_of_eq ENat.coe_top_add_one)).differentiableAt (by simp)
  have h6 : fderiv ℝ (θ • slabTop Ω Ωs) w = θ • fderiv ℝ (slabTop Ω Ωs) w :=
    ((htd w hw).hasFDerivAt.const_smul θ).fderiv
  have h7 : fderiv ℝ (fderiv ℝ (θ • slabTop Ω Ωs)) w =
      θ • fderiv ℝ (fderiv ℝ (slabTop Ω Ωs)) w := by
    refine ((hdt.hasFDerivAt.const_smul θ).congr_of_eventuallyEq ?_).fderiv
    filter_upwards [hGo.mem_nhds hw] with x hx
    exact ((htd x hx).hasFDerivAt.const_smul θ).fderiv
  have hjθ : (((θ • slabTop Ω Ωs) w, poincareDensity Ω w,
      schwarzian (Function.invFunOn f unitDisc) w,
      fun i => fderiv ℝ (poincareDensity Ω) w (frameVec i),
      fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) w (frameVec i),
      fun i => fderiv ℝ (θ • slabTop Ω Ωs) w (frameVec i),
      fun i j => fderiv ℝ (fderiv ℝ (θ • slabTop Ω Ωs)) w (frameVec i) (frameVec j)) :
        ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ)) =
      jm (θ, w) := by
    rw [hjm, h6, h7]
    rfl
  have hmem := hmapsO (show (θ, w) ∈ Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ goodSet Ω Ωs η R from ⟨hθ, hw⟩)
  rw [hrep Ω Ωs hJ f hf D hDo (hDG.trans hGΩ) (fun x hx => (hsη x (hDG hx)).trans (by norm_num))
    (θ • slabTop Ω Ωs) u (((htC.mono hDG).const_smul θ).of_le (by simp)) hu w hwD
    (by rw [hjθ]; exact hmem), hjθ]
  rfl

/-- Helper (P2): `d_𝔻(0, z) = log((1 + |z|)/(1 - |z|))`. -/
theorem s05_diskDist_zero {z : ℂ} (hz : ‖z‖ < 1) : diskDist 0 z = logRatio ‖z‖ := by
  set r := ‖z‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg z
  have h1 : 0 < 1 - r ^ 2 := by nlinarith
  have hc : diskCoshDist 0 z = (1 + r ^ 2) / (1 - r ^ 2) := by
    rw [diskCoshDist, zero_sub, norm_neg, norm_zero, ← hr]
    field_simp
    ring
  have hsq : ((1 + r ^ 2) / (1 - r ^ 2)) ^ 2 - 1 = (2 * r / (1 - r ^ 2)) ^ 2 := by
    field_simp
    ring
  rw [diskDist, hc, Real.arcosh, hsq, Real.sqrt_sq (by positivity),
    logRatio_eq (by linarith) (by nlinarith)]
  congr 1
  have h2 : (1 : ℝ) - r ≠ 0 := by nlinarith
  field_simp
  ring

/-- `logRatio s < ε` for `0 ≤ s < (e^ε - 1)/(e^ε + 1)`. -/
theorem s05_logRatio_lt {s ε : ℝ} (hs0 : 0 ≤ s) (hs : s < (Real.exp ε - 1) / (Real.exp ε + 1)) :
    logRatio s < ε := by
  have he := Real.exp_pos ε
  rw [lt_div_iff₀ (by positivity)] at hs
  have hs1 : s < 1 := by nlinarith
  change Real.log (1 + s) - Real.log (1 - s) < ε
  have h1 : 1 + s < Real.exp ε * (1 - s) := by nlinarith
  have h := Real.log_lt_log (by positivity) h1
  rw [Real.log_mul he.ne' (by linarith : (0 : ℝ) < 1 - s).ne', Real.log_exp] at h
  linarith

/-- Continuity of `d_ρ` at the diagonal: for `w ∈ Ω` and `ε > 0`, every `w'` near `w` lies in
`Ω` with `d_ρ(w, w') < ε`. -/
theorem s05_poincareDist_eventually_lt {Ω : Set ℂ}
    (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {w : ℂ} (hw : w ∈ Ω) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w' in 𝓝 w, w' ∈ Ω ∧ poincareDist Ω w w' < ε := by
  obtain ⟨g, hg⟩ := hΩ
  obtain ⟨p, hp, rfl⟩ : w ∈ g '' unitDisc := by rw [hg.2.2]; exact hw
  obtain ⟨hf, hf0, -⟩ := s02_disc_recenter hg hp
  rw [← hf0]
  generalize g ∘ blaschke (-p) = f at hf
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have he1 : 1 < Real.exp ε := by linarith [Real.add_one_lt_exp hε.ne']
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (Real.exp ε - 1) / (Real.exp ε + 1) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact div_pos (by linarith) (by linarith)
  have hr1 : r < 1 := by rw [hr, div_lt_one (by linarith)]; linarith
  have hsub : ball (0 : ℂ) r ⊆ unitDisc := ball_subset_ball hr1.le
  have hopen : IsOpen (f '' ball 0 r) := by
    have han : AnalyticOnNhd ℂ f unitDisc := hf.1.analyticOnNhd isOpen_ball
    rcases han.is_constant_or_isOpen (convex_ball (0 : ℂ) 1).isPreconnected with ⟨c, hc⟩ | ho
    · exfalso
      have h12 : (1 / 2 : ℂ) ∈ unitDisc := by
        rw [unitDisc, mem_ball_zero_iff]; norm_num
      have := hf.2.1 h0 h12 ((hc 0 h0).trans (hc _ h12).symm)
      norm_num at this
    · exact ho _ hsub isOpen_ball
  filter_upwards [hopen.mem_nhds (mem_image_of_mem f (mem_ball_self hr0))] with w' hw'
  obtain ⟨z, hz, rfl⟩ := hw'
  have hzD := hsub hz
  refine ⟨hf.2.2 ▸ mem_image_of_mem f hzD, ?_⟩
  rw [subsec_poincare_dist hf h0 hzD, s05_diskDist_zero (mem_ball_zero_iff.mp hzD)]
  exact s05_logRatio_lt (norm_nonneg z) (hr ▸ mem_ball_zero_iff.mp hz)

/-! ## W-MC (a) (w6): `𝒬(t) = 2σ` on `G₀`, via the graph surface in Fermi coordinates
(M1–M7, see `collaboration/WMC_A_IFACE_w6.md`). -/

/-! ## New defs (approved, W-MC (a) D1) -/

/-- (W-MC (a), def D1) The mean curvature `½ tr(I⁻¹ IIᵀ)` of a map `Φ : ℂ → ℍ³` with
normal field `ν`, by the formulas of `fffMat`, `secondFFMat`, `meanCurv`. -/
def immMeanCurv (Φ ν : ℂ → ℂ × ℝ) (w : ℂ) : ℝ :=
  ((Matrix.of fun i j : Fin 2 =>
        hypInner (Φ w) (fderiv ℝ Φ w (frameVec i)) (fderiv ℝ Φ w (frameVec j)))⁻¹ *
      (Matrix.of fun i j : Fin 2 =>
        hypInner (Φ w)
          (-(fderiv ℝ ν w (frameVec i) +
            hypChristoffel (Φ w) (fderiv ℝ Φ w (frameVec i)) (ν w)))
          (fderiv ℝ Φ w (frameVec j)))ᵀ).trace / 2

/-- (W-MC (a), def D1) The upward unit normal field `n = (-g_τ⁻¹ ∇u, 1)/W` of the graph of
`u` in Fermi coordinates `p = (x, τ)` (the field behind `graphFlux`, `graphW`). -/
def mcNormal (Ω : Set ℂ) (u : ℂ → ℝ) (p : ℂ × ℝ) : ℂ × ℝ :=
  (ofCvec fun i => -((graphMetric Ω p.1 p.2)⁻¹ *ᵥ gradCoords u p.1) i / graphW Ω u p.1 p.2,
    1 / graphW Ω u p.1 p.2)

/-! ## M1: congruence, metric compatibility (A0, A1) -/

/-- M1: `meanCurv` is `immMeanCurv` of `(X, ν)`. -/
theorem s05_mc_meanCurv_eq (Ω : Set ℂ) (w : ℂ) :
    meanCurv Ω w = immMeanCurv (epstein Ω) (normalVec Ω) w := by
  rfl

/-- M1: `H_up(u)(w)` only depends on the germ of `u` at `w`. -/
theorem s05_mc_congr (Ω : Set ℂ) {u u' : ℂ → ℝ} {w : ℂ} (h : u =ᶠ[𝓝 w] u') :
    meanCurvUp Ω u w = meanCurvUp Ω u' w := by
  have h0 : u w = u' w := h.eq_of_nhds
  have hg : ∀ᶠ x in 𝓝 w, gradCoords u x = gradCoords u' x := by
    filter_upwards [h.eventuallyEq_nhds] with x hx
    funext j
    simp only [gradCoords, hx.fderiv_eq]
  have hW : ∀ τ, graphW Ω u w τ = graphW Ω u' w τ := fun τ => by
    simp only [graphW, hg.self_of_nhds]
  have hF : ∀ τ i, fderiv ℝ (fun x => graphFlux Ω u τ x i) w =
      fderiv ℝ (fun x => graphFlux Ω u' τ x i) w := by
    intro τ i
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hg] with x hx
    simp only [graphFlux, graphW, hx]
  unfold meanCurvUp
  rw [h0]
  simp only [hW, hF]

/-- M1: `immMeanCurv` only depends on the germs of `Φ` and `ν`. -/
theorem s05_mc_imm_congr {Φ Φ' ν ν' : ℂ → ℂ × ℝ} {w : ℂ} (hΦ : Φ =ᶠ[𝓝 w] Φ')
    (hν : ν =ᶠ[𝓝 w] ν') : immMeanCurv Φ ν w = immMeanCurv Φ' ν' w := by
  unfold immMeanCurv
  rw [hΦ.fderiv_eq, hν.fderiv_eq, hΦ.eq_of_nhds, hν.eq_of_nhds]

/-- M1: `hypChristoffel` is symmetric. -/
theorem s05_mc_hypChr_symm (q U V : ℂ × ℝ) : hypChristoffel q U V = hypChristoffel q V U := by
  have e : (conj U.1 * V.1).re = (conj V.1 * U.1).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  unfold hypChristoffel
  rw [e, add_comm ((-(U.2 / q.2)) • V), mul_comm U.2 V.2]

/-- M1 (A1): metric compatibility of `hypChristoffel` along a map `E`:
`d⟨V, W⟩_E(Z) = ⟨∇_Z V, W⟩ + ⟨V, ∇_Z W⟩`, `∇_Z V = dV(Z) + Γ_E(dE Z, V)`. -/
theorem s05_mc_compat {E V W : ℂ × ℝ → ℂ × ℝ} {p : ℂ × ℝ} (hE : DifferentiableAt ℝ E p)
    (hV : DifferentiableAt ℝ V p) (hW : DifferentiableAt ℝ W p) (hq : 0 < (E p).2)
    (Z : ℂ × ℝ) :
    fderiv ℝ (fun p' => hypInner (E p') (V p') (W p')) p Z =
      hypInner (E p) (fderiv ℝ V p Z + hypChristoffel (E p) (fderiv ℝ E p Z) (V p)) (W p) +
        hypInner (E p) (V p) (fderiv ℝ W p Z + hypChristoffel (E p) (fderiv ℝ E p Z) (W p)) := by
  have cmp : ∀ (L : ℂ × ℝ →L[ℝ] ℝ) {F : ℂ × ℝ → ℂ × ℝ}, DifferentiableAt ℝ F p →
      HasFDerivAt (fun p' => L (F p')) (L.comp (fderiv ℝ F p)) p :=
    fun L F hF => L.hasFDerivAt.comp p hF.hasFDerivAt
  have hq2 : (E p).2 ^ 2 ≠ 0 := by positivity
  have hinv := (hasFDerivAt_inv hq2).comp p ((cmp (ContinuousLinearMap.snd ℝ ℂ ℝ) hE).pow 2)
  have hnum := (((cmp (reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)) hV).fun_mul
      (cmp (reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)) hW)).add
    ((cmp (imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)) hV).fun_mul
      (cmp (imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)) hW))).add
    ((cmp (ContinuousLinearMap.snd ℝ ℂ ℝ) hV).fun_mul (cmp (ContinuousLinearMap.snd ℝ ℂ ℝ) hW))
  have h := hnum.fun_mul hinv
  have e : (fun p' => hypInner (E p') (V p') (W p')) =ᶠ[𝓝 p] fun p' =>
      ((reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)) (V p') *
            (reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)) (W p') +
          (imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)) (V p') *
            (imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)) (W p') +
          (ContinuousLinearMap.snd ℝ ℂ ℝ) (V p') * (ContinuousLinearMap.snd ℝ ℂ ℝ) (W p')) *
        ((fun x : ℝ => x⁻¹) ∘ fun p' => (ContinuousLinearMap.snd ℝ ℂ ℝ) (E p') ^ 2) p' :=
    Filter.Eventually.of_forall fun p' => by
      simp only [hypInner, Function.comp, ContinuousLinearMap.comp_apply, reCLM_apply, imCLM_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Complex.mul_re,
        Complex.conj_re, Complex.conj_im, div_eq_mul_inv]
      ring
  rw [(h.congr_of_eventuallyEq e).fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, reCLM_apply, imCLM_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', Function.comp, smul_eq_mul,
    ContinuousLinearMap.toSpanSingleton_apply,
    nsmul_eq_mul, Pi.add_apply]
  have hq0 : (E p).2 ≠ 0 := hq.ne'
  generalize fderiv ℝ V p Z = dV
  generalize fderiv ℝ W p Z = dW
  generalize fderiv ℝ E p Z = dE
  generalize V p = A
  generalize W p = Bv
  generalize E p = Q at hq0 ⊢
  unfold hypInner hypChristoffel
  obtain ⟨⟨a1, a2⟩, a3⟩ := A
  obtain ⟨⟨b1, b2⟩, b3⟩ := Bv
  obtain ⟨⟨c1, c2⟩, c3⟩ := dV
  obtain ⟨⟨d1, d2⟩, d3⟩ := dW
  obtain ⟨⟨e1, e2⟩, e3⟩ := dE
  obtain ⟨q1, q2⟩ := Q
  simp only at hq0
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    smul_eq_mul, Complex.zero_re, Complex.zero_im]
  field_simp
  ring

/-! ## M2: the Fermi frame (A2) -/

/-- M2 helper: `hypInner q` is symmetric. -/
theorem s05_mc_2_hi_symm (q a b : ℂ × ℝ) : hypInner q a b = hypInner q b a := by
  unfold hypInner
  congr 1
  rw [mul_comm b.2, ← Complex.conj_re (b.1 * conj a.1), map_mul, Complex.conj_conj, mul_comm]

/-- M2 helper: `hypInner q` is additive in the first slot. -/
theorem s05_mc_2_hi_add (q a a' b : ℂ × ℝ) :
    hypInner q (a + a') b = hypInner q a b + hypInner q a' b := by
  unfold hypInner
  simp only [Prod.fst_add, Prod.snd_add, add_mul, Complex.add_re]
  ring

/-- M2 helper: `hypInner q` is homogeneous in the first slot. -/
theorem s05_mc_2_hi_smul (q a b : ℂ × ℝ) (c : ℝ) :
    hypInner q (c • a) b = c * hypInner q a b := by
  unfold hypInner
  simp only [Prod.smul_fst, Prod.smul_snd, Complex.real_smul, smul_eq_mul, mul_assoc,
    Complex.re_ofReal_mul]
  ring

/-- M2 helper: `hypInner q` is additive in the second slot. -/
theorem s05_mc_2_hi_add_r (q a b b' : ℂ × ℝ) :
    hypInner q a (b + b') = hypInner q a b + hypInner q a b' := by
  rw [s05_mc_2_hi_symm, s05_mc_2_hi_add, s05_mc_2_hi_symm q b, s05_mc_2_hi_symm q b']

/-- M2 helper: `hypInner q` is homogeneous in the second slot. -/
theorem s05_mc_2_hi_smul_r (q a b : ℂ × ℝ) (c : ℝ) :
    hypInner q a (c • b) = c * hypInner q a b := by
  rw [s05_mc_2_hi_symm, s05_mc_2_hi_smul, s05_mc_2_hi_symm]

/-- M2 helper: `E = normalMap Ω` is `C^∞` at every `(x, τ)`, `x ∈ Ω`. -/
theorem s05_mc_2_nm_cd {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {x : ℂ} (hx : x ∈ Ω) (τ : ℝ) :
    ContDiffAt ℝ ∞ (normalMap Ω) (x, τ) := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  exact (s04_tb_nm_smooth hf).contDiffAt
    (((hf.isOpen isOpen_ball).prod isOpen_univ).mem_nhds ⟨hx, mem_univ _⟩)

/-- M2: `dE_{(x,τ)}(a, α) = d_x E(·, τ) a + α ∂_τ E(x, τ)`. -/
theorem s05_mc_dE {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {x : ℂ} (hx : x ∈ Ω) (τ : ℝ)
    (a : ℂ) (α : ℝ) :
    fderiv ℝ (normalMap Ω) (x, τ) (a, α) =
      fderiv ℝ (fun x' => normalGeod Ω x' τ) x a + α • deriv (fun τ' => normalGeod Ω x τ') τ := by
  have hd : DifferentiableAt ℝ (normalMap Ω) (x, τ) :=
    (s05_mc_2_nm_cd hJ hx τ).differentiableAt (by simp)
  have h1' := hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x τ)
  have h1 : HasFDerivAt (fun x' => normalGeod Ω x' τ)
      ((fderiv ℝ (normalMap Ω) (x, τ)).comp (ContinuousLinearMap.inl ℝ ℂ ℝ)) x := h1'
  have h2 : HasDerivAt (fun τ' => normalGeod Ω x τ') (fderiv ℝ (normalMap Ω) (x, τ) (0, 1)) τ :=
    hd.hasFDerivAt.comp_hasDerivAt τ ((hasDerivAt_const τ x).prodMk (hasDerivAt_id τ))
  rw [h1.fderiv, h2.deriv]
  have e : ((a, α) : ℂ × ℝ) = (a, 0) + α • ((0 : ℂ), (1 : ℝ)) := by
    ext <;> simp
  rw [e, map_add, map_smul]
  rfl

/-- M2: `ḡ = diag(g_τ, 1)` (`lem_shape_a`). -/
theorem s05_mc_gbar {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {x : ℂ} (hx : x ∈ Ω)
    (hs : schwarzNorm Ω x ≠ 1) (τ : ℝ) (a b : ℂ) (α β : ℝ) :
    hypInner (normalMap Ω (x, τ)) (fderiv ℝ (normalMap Ω) (x, τ) (a, α))
        (fderiv ℝ (normalMap Ω) (x, τ) (b, β)) =
      cvec a ⬝ᵥ (graphMetric Ω x τ *ᵥ cvec b) + α * β := by
  obtain ⟨hu, ho, -⟩ := lem_shape_a Ω Ωs hJ x hx hs τ
  have hG : ∀ i j, graphMetric Ω x τ i j =
      hypInner (normalGeod Ω x τ) (fderiv ℝ (fun x' => normalGeod Ω x' τ) x (frameVec i))
        (fderiv ℝ (fun x' => normalGeod Ω x' τ) x (frameVec j)) := fun i j => rfl
  rw [s05_mc_dE hJ hx, s05_mc_dE hJ hx]
  change hypInner (normalGeod Ω x τ) _ _ = _
  generalize fderiv ℝ (fun x' => normalGeod Ω x' τ) x = L at ho hG ⊢
  generalize deriv (fun τ' => normalGeod Ω x τ') τ = D at hu ho ⊢
  generalize normalGeod Ω x τ = q at hu ho hG ⊢
  have hLv : ∀ v : ℂ, L v = v.re • L 1 + v.im • L I := fun v => by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    apply Complex.ext <;> simp
  have hoD : ∀ v, hypInner q (L v) D = 0 := fun v => by rw [s05_mc_2_hi_symm, ho]
  rw [hLv a, hLv b]
  simp only [s05_mc_2_hi_add, s05_mc_2_hi_add_r, s05_mc_2_hi_smul, s05_mc_2_hi_smul_r, ho, hoD,
    hu, dotProduct, Matrix.mulVec, Fin.sum_univ_two, cvec, hG, frameVec, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- M2 helper: the derivative of `p ↦ ḡ_p(X, Y)` for constant `X, Y` (`s05_mc_compat`). -/
theorem s05_mc_2_dg {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {x : ℂ} (hx : x ∈ Ω) (τ : ℝ)
    (X Y Z : ℂ × ℝ) :
    fderiv ℝ (fun p : ℂ × ℝ => hypInner (normalMap Ω p) (fderiv ℝ (normalMap Ω) p X)
        (fderiv ℝ (normalMap Ω) p Y)) (x, τ) Z =
      hypInner (normalMap Ω (x, τ))
          (fderiv ℝ (fderiv ℝ (normalMap Ω)) (x, τ) Z X +
            hypChristoffel (normalMap Ω (x, τ)) (fderiv ℝ (normalMap Ω) (x, τ) Z)
              (fderiv ℝ (normalMap Ω) (x, τ) X))
          (fderiv ℝ (normalMap Ω) (x, τ) Y) +
        hypInner (normalMap Ω (x, τ)) (fderiv ℝ (normalMap Ω) (x, τ) X)
          (fderiv ℝ (fderiv ℝ (normalMap Ω)) (x, τ) Z Y +
            hypChristoffel (normalMap Ω (x, τ)) (fderiv ℝ (normalMap Ω) (x, τ) Z)
              (fderiv ℝ (normalMap Ω) (x, τ) Y)) := by
  have hE := s05_mc_2_nm_cd hJ hx τ
  have hD : HasFDerivAt (fderiv ℝ (normalMap Ω)) (fderiv ℝ (fderiv ℝ (normalMap Ω)) (x, τ))
      (x, τ) :=
    ((hE.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hV : ∀ X : ℂ × ℝ, HasFDerivAt (fun p => fderiv ℝ (normalMap Ω) p X)
      ((fderiv ℝ (fderiv ℝ (normalMap Ω)) (x, τ)).flip X) (x, τ) := fun X => by
    have := hD.clm_apply (hasFDerivAt_const X (x, τ))
    simpa using this
  have hq : 0 < (normalMap Ω (x, τ)).2 := by
    obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
    exact (lem_normal_b ⟨f, hf⟩ hx).1 τ
  rw [s05_mc_compat (hE.differentiableAt (by simp)) (hV X).differentiableAt
    (hV Y).differentiableAt hq Z, (hV X).fderiv, (hV Y).fderiv]
  rfl

/-- M2 helper: `det g_τ > 0` for `s < 1/4`, `τ < 1` (`s05_go_det`). -/
theorem s05_mc_2_det_pos {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {x : ℂ} (hx : x ∈ Ω)
    (hs : schwarzNorm Ω x < 1 / 4) {τ : ℝ} (hτ : τ < 1) : 0 < (graphMetric Ω x τ).det := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hx
  have hs0 : 0 ≤ schwarzNorm Ω x := (eq_nehari ⟨f, hf⟩ hx).1
  rw [s05_go_det hJ hx (by linarith) τ]
  have he : Real.exp τ < 4 :=
    (Real.exp_lt_exp.mpr hτ).trans (Real.exp_one_lt_d9.trans (by norm_num))
  have hc : 1 ≤ Real.cosh τ := Real.one_le_cosh τ
  have hep := Real.exp_pos τ
  have h1 : schwarzNorm Ω x * Real.exp τ < Real.cosh τ := by nlinarith
  have h2 : 0 < Real.cosh τ ^ 2 - schwarzNorm Ω x ^ 2 * Real.exp τ ^ 2 := by
    nlinarith [mul_nonneg hs0 hep.le]
  positivity

/-- M2: the contraction identity `tr_ḡ K(·, Z) = ∂_Z log √det g_τ`, `K(X, Y) = D²E(X, Y) +
Γ(dE X, dE Y)` (Jacobi's formula for `2 × 2`, `ḡ_{a3}` constant). -/
theorem s05_mc_contract {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {U : Set ℂ} (hU : IsOpen U)
    (hUΩ : U ⊆ Ω) (hUs : ∀ y ∈ U, schwarzNorm Ω y < 1 / 4) {x : ℂ} (hx : x ∈ U) {τ : ℝ}
    (hτ : τ < 1) (Z : ℂ × ℝ) :
    (∑ i : Fin 2, ∑ j : Fin 2, (graphMetric Ω x τ)⁻¹ i j *
        hypInner (normalMap Ω (x, τ))
          (fderiv ℝ (fderiv ℝ (normalMap Ω)) (x, τ) (frameVec i, 0) Z +
            hypChristoffel (normalMap Ω (x, τ)) (fderiv ℝ (normalMap Ω) (x, τ) (frameVec i, 0))
              (fderiv ℝ (normalMap Ω) (x, τ) Z))
          (fderiv ℝ (normalMap Ω) (x, τ) (frameVec j, 0))) +
      hypInner (normalMap Ω (x, τ))
        (fderiv ℝ (fderiv ℝ (normalMap Ω)) (x, τ) (0, 1) Z +
          hypChristoffel (normalMap Ω (x, τ)) (fderiv ℝ (normalMap Ω) (x, τ) (0, 1))
            (fderiv ℝ (normalMap Ω) (x, τ) Z))
        (fderiv ℝ (normalMap Ω) (x, τ) (0, 1)) =
      fderiv ℝ (fun p : ℂ × ℝ => graphSdet Ω p.1 p.2) (x, τ) Z / graphSdet Ω x τ := by
  have hxΩ := hUΩ hx
  have hE := s05_mc_2_nm_cd hJ hxΩ τ
  have hsym : IsSymmSndFDerivAt ℝ (normalMap Ω) (x, τ) := hE.isSymmSndFDerivAt (by simp)
  have hnhds : U ×ˢ (univ : Set ℝ) ∈ 𝓝 (x, τ) := (hU.prod isOpen_univ).mem_nhds ⟨hx, mem_univ _⟩
  -- `ḡ_{ij} = g_{ij}`, `ḡ_{33} = 1` near `(x, τ)`
  have hgE : ∀ i j : Fin 2, (fun p : ℂ × ℝ => hypInner (normalMap Ω p)
      (fderiv ℝ (normalMap Ω) p (frameVec i, 0)) (fderiv ℝ (normalMap Ω) p (frameVec j, 0))) =ᶠ[𝓝 (x, τ)]
        fun p => graphMetric Ω p.1 p.2 i j := by
    intro i j
    filter_upwards [hnhds] with p hp
    obtain ⟨p1, p2⟩ := p
    rw [s05_mc_dE hJ (hUΩ hp.1), s05_mc_dE hJ (hUΩ hp.1)]
    simp only [zero_smul, add_zero]
    rfl
  have h33 : (fun p : ℂ × ℝ => hypInner (normalMap Ω p) (fderiv ℝ (normalMap Ω) p (0, 1))
      (fderiv ℝ (normalMap Ω) p (0, 1))) =ᶠ[𝓝 (x, τ)] fun _ => (1 : ℝ) := by
    filter_upwards [hnhds] with p hp
    obtain ⟨p1, p2⟩ := p
    rw [s05_mc_gbar hJ (hUΩ hp.1) (by linarith [hUs p1 hp.1]) p2]
    simp [cvec]
  have dij : ∀ i j : Fin 2, fderiv ℝ (fun p : ℂ × ℝ => graphMetric Ω p.1 p.2 i j) (x, τ) Z =
      hypInner (normalMap Ω (x, τ))
          (fderiv ℝ (fderiv ℝ (normalMap Ω)) (x, τ) Z (frameVec i, 0) +
            hypChristoffel (normalMap Ω (x, τ)) (fderiv ℝ (normalMap Ω) (x, τ) Z)
              (fderiv ℝ (normalMap Ω) (x, τ) (frameVec i, 0)))
          (fderiv ℝ (normalMap Ω) (x, τ) (frameVec j, 0)) +
        hypInner (normalMap Ω (x, τ))
          (fderiv ℝ (fderiv ℝ (normalMap Ω)) (x, τ) Z (frameVec j, 0) +
            hypChristoffel (normalMap Ω (x, τ)) (fderiv ℝ (normalMap Ω) (x, τ) Z)
              (fderiv ℝ (normalMap Ω) (x, τ) (frameVec j, 0)))
          (fderiv ℝ (normalMap Ω) (x, τ) (frameVec i, 0)) := by
    intro i j
    rw [← (hgE i j).fderiv_eq, s05_mc_2_dg hJ hxΩ τ, s05_mc_2_hi_symm _ (fderiv ℝ _ _ _)]
  have d33 : 0 = 2 * hypInner (normalMap Ω (x, τ))
      (fderiv ℝ (fderiv ℝ (normalMap Ω)) (x, τ) Z (0, 1) +
        hypChristoffel (normalMap Ω (x, τ)) (fderiv ℝ (normalMap Ω) (x, τ) Z)
          (fderiv ℝ (normalMap Ω) (x, τ) (0, 1)))
      (fderiv ℝ (normalMap Ω) (x, τ) (0, 1)) := by
    have h := s05_mc_2_dg hJ hxΩ τ (0, 1) (0, 1) Z
    rw [h33.fderiv_eq, fderiv_const_apply, s05_mc_2_hi_symm _ (fderiv ℝ _ _ _)] at h
    simp only [zero_apply] at h
    linarith
  -- symmetry `K(X, Z) = K(Z, X)`
  have hK : ∀ X : ℂ × ℝ, fderiv ℝ (fderiv ℝ (normalMap Ω)) (x, τ) X Z +
      hypChristoffel (normalMap Ω (x, τ)) (fderiv ℝ (normalMap Ω) (x, τ) X)
        (fderiv ℝ (normalMap Ω) (x, τ) Z) =
      fderiv ℝ (fderiv ℝ (normalMap Ω)) (x, τ) Z X +
        hypChristoffel (normalMap Ω (x, τ)) (fderiv ℝ (normalMap Ω) (x, τ) Z)
          (fderiv ℝ (normalMap Ω) (x, τ) X) := fun X => by
    rw [hsym X Z, s05_mc_hypChr_symm]
  simp only [hK]
  -- Jacobi
  have hgd : ∀ i j : Fin 2, HasFDerivAt (fun p : ℂ × ℝ => graphMetric Ω p.1 p.2 i j)
      (fderiv ℝ (fun p : ℂ × ℝ => graphMetric Ω p.1 p.2 i j) (x, τ)) (x, τ) := fun i j =>
    (((s05_go_metric_contDiff hJ hU hUΩ (fun y hy => (hUs y hy).trans (by norm_num)) i j).contDiffAt
      hnhds).differentiableAt (by simp)).hasFDerivAt
  have hdet := s05_mc_2_det_pos hJ hxΩ (hUs x hx) hτ
  rw [Matrix.det_fin_two] at hdet
  have hsq := (((hgd 0 0).fun_mul (hgd 1 1)).fun_sub ((hgd 0 1).fun_mul (hgd 1 0))).sqrt hdet.ne'
  have e : (fun p : ℂ × ℝ => graphSdet Ω p.1 p.2) = fun p =>
      √(graphMetric Ω p.1 p.2 0 0 * graphMetric Ω p.1 p.2 1 1 -
        graphMetric Ω p.1 p.2 0 1 * graphMetric Ω p.1 p.2 1 0) :=
    funext fun p => by rw [graphSdet, Matrix.det_fin_two]
  rw [e, hsq.fderiv]
  simp only [smul_apply, add_apply, sub_apply, smul_eq_mul, dij]
  have hsy : graphMetric Ω x τ 1 0 = graphMetric Ω x τ 0 1 := s05_mc_2_hi_symm _ _ _
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv', Matrix.det_fin_two]
  simp only [Fin.sum_univ_two, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val',
    smul_eq_mul, graphSdet, Matrix.det_fin_two]
  rw [hsy] at hdet ⊢
  generalize graphMetric Ω x τ 0 0 = g00 at hdet ⊢
  generalize graphMetric Ω x τ 0 1 = g01 at hdet ⊢
  generalize graphMetric Ω x τ 1 1 = g11 at hdet ⊢
  have hr := Real.sq_sqrt hdet.le
  have hr0 := Real.sqrt_pos.mpr hdet
  generalize √(g00 * g11 - g01 * g01) = r at hr hr0 ⊢
  rw [← hr]
  have k33 := d33
  generalize hypInner (normalMap Ω (x, τ))
      (fderiv ℝ (fderiv ℝ (normalMap Ω)) (x, τ) Z (0, 1) +
        hypChristoffel (normalMap Ω (x, τ)) (fderiv ℝ (normalMap Ω) (x, τ) Z)
          (fderiv ℝ (normalMap Ω) (x, τ) (0, 1)))
      (fderiv ℝ (normalMap Ω) (x, τ) (0, 1)) = k at k33 ⊢
  obtain rfl : k = 0 := by linarith
  field_simp
  ring

/-! ## M3: the unit upper normal field (A3, first half) -/

/-- M3 helper: the inverse of a `2 × 2` matrix, entrywise. -/
theorem s05_mc_3_inv (A : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    A⁻¹ i j = (A 0 0 * A 1 1 - A 0 1 * A 1 0)⁻¹ * !![A 1 1, -A 0 1; -A 1 0, A 0 0] i j := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv', Matrix.det_fin_two]
  rfl

/-- M3 helper: `g_τ` is symmetric. -/
theorem s05_mc_3_symm (Ω : Set ℂ) (x : ℂ) (τ : ℝ) :
    graphMetric Ω x τ 1 0 = graphMetric Ω x τ 0 1 :=
  s05_mc_2_hi_symm _ _ _

/-- M3 helper: the diagonal entries of `g_τ` are `≥ 0`. -/
theorem s05_mc_3_diag (Ω : Set ℂ) (x : ℂ) (τ : ℝ) (i : Fin 2) : 0 ≤ graphMetric Ω x τ i i := by
  change 0 ≤ hypInner _ _ _
  unfold hypInner
  apply div_nonneg _ (sq_nonneg _)
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (fderiv ℝ (fun x' => normalGeod Ω x' τ) x (frameVec i)).1.re,
    sq_nonneg (fderiv ℝ (fun x' => normalGeod Ω x' τ) x (frameVec i)).1.im,
    sq_nonneg (fderiv ℝ (fun x' => normalGeod Ω x' τ) x (frameVec i)).2]

/-- M3 helper: `q · g_τ⁻¹ q ≥ 0` when `det g_τ > 0`. -/
theorem s05_mc_3_quad (Ω : Set ℂ) (x : ℂ) (τ : ℝ) (hdet : 0 < (graphMetric Ω x τ).det)
    (q : Fin 2 → ℝ) : 0 ≤ q ⬝ᵥ ((graphMetric Ω x τ)⁻¹ *ᵥ q) := by
  rw [Matrix.det_fin_two, s05_mc_3_symm] at hdet
  have h0 := s05_mc_3_diag Ω x τ 0
  have h1 := s05_mc_3_diag Ω x τ 1
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, s05_mc_3_inv, s05_mc_3_symm,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val']
  generalize graphMetric Ω x τ 0 0 = a at *
  generalize graphMetric Ω x τ 0 1 = b at *
  generalize graphMetric Ω x τ 1 1 = c at *
  have ha : 0 < a := by
    rcases h0.lt_or_eq with h | h
    · exact h
    · subst h; nlinarith [sq_nonneg b]
  have key : 0 ≤ c * q 0 ^ 2 - 2 * b * q 0 * q 1 + a * q 1 ^ 2 := by
    nlinarith [sq_nonneg (a * q 1 - b * q 0), sq_nonneg (q 0)]
  have e : q 0 * ((a * c - b * b)⁻¹ * c * q 0 + (a * c - b * b)⁻¹ * -b * q 1) +
      q 1 * ((a * c - b * b)⁻¹ * -b * q 0 + (a * c - b * b)⁻¹ * a * q 1) =
      (c * q 0 ^ 2 - 2 * b * q 0 * q 1 + a * q 1 ^ 2) / (a * c - b * b) := by
    field_simp
    ring
  rw [e]
  exact div_nonneg key hdet.le

/-- M3: joint smoothness on `U × (-∞, 1)` (`s < 1/4` there, so `det g_τ > 0`). -/
theorem s05_mc_smooth {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {U : Set ℂ} (hU : IsOpen U)
    (hUΩ : U ⊆ Ω) (hUs : ∀ y ∈ U, schwarzNorm Ω y < 1 / 4) {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => graphSdet Ω p.1 p.2) (U ×ˢ Iio 1) ∧
      ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => graphW Ω u p.1 p.2) (U ×ˢ Iio 1) ∧
      (∀ i, ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => graphFlux Ω u p.2 p.1 i) (U ×ˢ Iio 1)) ∧
      ContDiffOn ℝ ∞ (mcNormal Ω u) (U ×ˢ Iio 1) := by
  have hUs1 : ∀ y ∈ U, schwarzNorm Ω y < 1 := fun y hy => (hUs y hy).trans (by norm_num)
  have hD : U ×ˢ Iio (1 : ℝ) ⊆ U ×ˢ univ := prod_mono le_rfl (subset_univ _)
  have hg : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => graphMetric Ω p.1 p.2 i j) (U ×ˢ Iio 1) :=
    fun i j => (s05_go_metric_contDiff hJ hU hUΩ hUs1 i j).mono hD
  have hdp : ∀ p ∈ U ×ˢ Iio (1 : ℝ), 0 < (graphMetric Ω p.1 p.2).det := fun p hp =>
    s05_mc_2_det_pos hJ (hUΩ hp.1) (hUs _ hp.1) hp.2
  have hdc : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => graphMetric Ω p.1 p.2 0 0 * graphMetric Ω p.1 p.2 1 1 -
      graphMetric Ω p.1 p.2 0 1 * graphMetric Ω p.1 p.2 1 0) (U ×ˢ Iio 1) :=
    ((hg 0 0).mul (hg 1 1)).sub ((hg 0 1).mul (hg 1 0))
  have hsd : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => graphSdet Ω p.1 p.2) (U ×ˢ Iio 1) := by
    have e : (fun p : ℂ × ℝ => graphSdet Ω p.1 p.2) = fun p => √(graphMetric Ω p.1 p.2 0 0 *
        graphMetric Ω p.1 p.2 1 1 - graphMetric Ω p.1 p.2 0 1 * graphMetric Ω p.1 p.2 1 0) :=
      funext fun p => by rw [graphSdet, Matrix.det_fin_two]
    rw [e]
    exact hdc.sqrt fun p hp => by have := hdp p hp; rw [Matrix.det_fin_two] at this; exact this.ne'
  have hinv : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => (graphMetric Ω p.1 p.2)⁻¹ i j)
      (U ×ˢ Iio 1) := by
    have hi := hdc.inv fun p hp => by
      have := hdp p hp; rw [Matrix.det_fin_two] at this; exact this.ne'
    intro i j
    simp only [s05_mc_3_inv]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val'] <;>
      first
        | exact hi.mul (hg _ _)
        | exact hi.mul (hg _ _).neg
  have hgr : ∀ j, ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => gradCoords u p.1 j) (U ×ˢ Iio 1) := by
    intro j
    have hdu : ContDiffOn ℝ ∞ (fderiv ℝ u) U := hu.fderiv_of_isOpen hU (by simp)
    have hst : MapsTo (Prod.fst : ℂ × ℝ → ℂ) (U ×ˢ Iio (1 : ℝ)) U := fun p hp => hp.1
    exact (hdu.clm_apply contDiffOn_const).comp contDiff_fst.contDiffOn hst
  have hmv : ∀ i, ContDiffOn ℝ ∞ (fun p : ℂ × ℝ =>
      ((graphMetric Ω p.1 p.2)⁻¹ *ᵥ gradCoords u p.1) i) (U ×ˢ Iio 1) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact ((hinv i 0).mul (hgr 0)).add ((hinv i 1).mul (hgr 1))
  have hW : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => graphW Ω u p.1 p.2) (U ×ˢ Iio 1) := by
    have hq : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => 1 + gradCoords u p.1 ⬝ᵥ
        ((graphMetric Ω p.1 p.2)⁻¹ *ᵥ gradCoords u p.1)) (U ×ˢ Iio 1) := by
      simp only [dotProduct, Fin.sum_univ_two]
      exact contDiffOn_const.add (((hgr 0).mul (hmv 0)).add ((hgr 1).mul (hmv 1)))
    exact hq.sqrt fun p hp => by
      have := s05_mc_3_quad Ω p.1 p.2 (hdp p hp) (gradCoords u p.1)
      positivity
  have hWne : ∀ p ∈ U ×ˢ Iio (1 : ℝ), graphW Ω u p.1 p.2 ≠ 0 := fun p hp => by
    have := s05_mc_3_quad Ω p.1 p.2 (hdp p hp) (gradCoords u p.1)
    unfold graphW
    positivity
  refine ⟨hsd, hW, fun i => ?_, ?_⟩
  · exact (hsd.mul (hmv i)).div hW hWne
  · have e : mcNormal Ω u = fun p => (Complex.equivRealProdCLM.symm
        (-((graphMetric Ω p.1 p.2)⁻¹ *ᵥ gradCoords u p.1) 0 / graphW Ω u p.1 p.2,
          -((graphMetric Ω p.1 p.2)⁻¹ *ᵥ gradCoords u p.1) 1 / graphW Ω u p.1 p.2),
        1 / graphW Ω u p.1 p.2) := by
      funext p
      refine Prod.ext ?_ rfl
      apply Complex.ext <;> simp [mcNormal, ofCvec]
    rw [e]
    refine ContDiffOn.prodMk ?_ (contDiffOn_const.div hW hWne)
    exact Complex.equivRealProdCLM.symm.contDiff.comp_contDiffOn
      (((hmv 0).neg.div hW hWne).prodMk ((hmv 1).neg.div hW hWne))

/-- M3 helper: `cvec ∘ ofCvec = id`. -/
theorem s05_mc_3_cvec_ofCvec (c : Fin 2 → ℝ) : cvec (ofCvec c) = c := by
  funext i
  fin_cases i <;> rfl

/-- M3 helper: `g_τ` is symmetric as a matrix. -/
theorem s05_mc_3_transpose (Ω : Set ℂ) (x : ℂ) (τ : ℝ) :
    (graphMetric Ω x τ)ᵀ = graphMetric Ω x τ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, s05_mc_3_symm]

/-- M3 helper: `g_τ (g_τ⁻¹ q) = q` when `det g_τ > 0`, and `W² = 1 + q · g_τ⁻¹ q`, `W > 0`. -/
theorem s05_mc_3_W {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {x : ℂ} (hx : x ∈ Ω)
    (hs : schwarzNorm Ω x < 1 / 4) {τ : ℝ} (hτ : τ < 1) (u : ℂ → ℝ) :
    graphMetric Ω x τ *ᵥ ((graphMetric Ω x τ)⁻¹ *ᵥ gradCoords u x) = gradCoords u x ∧
      graphW Ω u x τ ^ 2 = 1 + gradCoords u x ⬝ᵥ ((graphMetric Ω x τ)⁻¹ *ᵥ gradCoords u x) ∧
      0 < graphW Ω u x τ := by
  have hdet := s05_mc_2_det_pos hJ hx hs hτ
  have hq := s05_mc_3_quad Ω x τ hdet (gradCoords u x)
  refine ⟨?_, Real.sq_sqrt (by positivity), Real.sqrt_pos.mpr (by positivity)⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet.ne'),
    Matrix.one_mulVec]

/-- M3: `ḡ(n, n) = 1`. -/
theorem s05_mc_unit {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {U : Set ℂ}
    (hUΩ : U ⊆ Ω) (hUs : ∀ y ∈ U, schwarzNorm Ω y < 1 / 4) (u : ℂ → ℝ) {p : ℂ × ℝ}
    (hp : p ∈ U ×ˢ Iio 1) :
    hypInner (normalMap Ω p) (fderiv ℝ (normalMap Ω) p (mcNormal Ω u p))
      (fderiv ℝ (normalMap Ω) p (mcNormal Ω u p)) = 1 := by
  obtain ⟨x, τ⟩ := p
  obtain ⟨hx, hτ⟩ := hp
  have hxΩ := hUΩ hx
  obtain ⟨hgg, hW2, hW0⟩ := s05_mc_3_W hJ hxΩ (hUs x hx) hτ u
  change hypInner (normalMap Ω (x, τ)) (fderiv ℝ (normalMap Ω) (x, τ) (ofCvec _, _))
    (fderiv ℝ (normalMap Ω) (x, τ) (ofCvec _, _)) = 1
  rw [s05_mc_gbar hJ hxΩ (by linarith [hUs x hx]) τ, s05_mc_3_cvec_ofCvec]
  generalize (graphMetric Ω x τ)⁻¹ *ᵥ gradCoords u x = v at hgg hW2
  generalize graphW Ω u x τ = W at hW2 hW0
  have hc : (fun i => -v i / W) = (-(1 / W)) • v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hc, Matrix.mulVec_smul, hgg, dotProduct_smul, smul_dotProduct, dotProduct_comm v,
    smul_eq_mul, smul_eq_mul]
  field_simp
  nlinarith [hW2]

/-- M3: on the graph, `n ⊥_ḡ (v, du(v))`. -/
theorem s05_mc_normal {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {U : Set ℂ}
    (hUΩ : U ⊆ Ω) (hUs : ∀ y ∈ U, schwarzNorm Ω y < 1 / 4) (u : ℂ → ℝ) {x : ℂ} (hx : x ∈ U)
    (hux : u x < 1) (v : ℂ) :
    hypInner (normalMap Ω (x, u x)) (fderiv ℝ (normalMap Ω) (x, u x) (mcNormal Ω u (x, u x)))
      (fderiv ℝ (normalMap Ω) (x, u x) (v, fderiv ℝ u x v)) = 0 := by
  have hxΩ := hUΩ hx
  obtain ⟨hgg, -, hW0⟩ := s05_mc_3_W hJ hxΩ (hUs x hx) hux u
  change hypInner (normalMap Ω (x, u x)) (fderiv ℝ (normalMap Ω) (x, u x) (ofCvec _, _)) _ = 0
  rw [s05_mc_gbar hJ hxΩ (by linarith [hUs x hx]) (u x), s05_mc_3_cvec_ofCvec]
  have hdu : fderiv ℝ u x v = gradCoords u x ⬝ᵥ cvec v := by
    have e : v = v.re • (1 : ℂ) + v.im • I := by apply Complex.ext <;> simp
    conv_lhs => rw [e]
    rw [map_add, map_smul, map_smul]
    simp [dotProduct, Fin.sum_univ_two, gradCoords, cvec, frameVec]
    ring
  rw [hdu]
  have hT := s05_mc_3_transpose Ω x (u x)
  generalize graphMetric Ω x (u x) = g at hgg hT
  generalize (g)⁻¹ *ᵥ gradCoords u x = w at hgg
  generalize graphW Ω u x (u x) = W at hW0
  have hc : (fun i => -w i / W) = (-(1 / W)) • w := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hvm : w ᵥ* g = g *ᵥ w := by rw [← Matrix.mulVec_transpose, hT]
  rw [hc, smul_dotProduct, Matrix.dotProduct_mulVec, hvm, hgg, smul_eq_mul]
  field_simp
  ring

/-- M3: `B(n, n) = ⟨∇_n V, V⟩ = ½ ∂_n ḡ(n, n) = 0`, `V = dE · n`. -/
theorem s05_mc_Bnn {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {U : Set ℂ} (hU : IsOpen U)
    (hUΩ : U ⊆ Ω) (hUs : ∀ y ∈ U, schwarzNorm Ω y < 1 / 4) {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) {p : ℂ × ℝ} (hp : p ∈ U ×ˢ Iio 1) :
    hypInner (normalMap Ω p)
        (fderiv ℝ (fun p' => fderiv ℝ (normalMap Ω) p' (mcNormal Ω u p')) p (mcNormal Ω u p) +
          hypChristoffel (normalMap Ω p) (fderiv ℝ (normalMap Ω) p (mcNormal Ω u p))
            (fderiv ℝ (normalMap Ω) p (mcNormal Ω u p)))
        (fderiv ℝ (normalMap Ω) p (mcNormal Ω u p)) = 0 := by
  have hDo : IsOpen (U ×ˢ Iio (1 : ℝ)) := hU.prod isOpen_Iio
  have hn : DifferentiableAt ℝ (mcNormal Ω u) p :=
    (((s05_mc_smooth hJ hU hUΩ hUs hu).2.2.2.contDiffAt (hDo.mem_nhds hp)).differentiableAt
      (by simp))
  obtain ⟨x, τ⟩ := p
  have hE := s05_mc_2_nm_cd hJ (hUΩ hp.1) τ
  have hD : HasFDerivAt (fderiv ℝ (normalMap Ω)) (fderiv ℝ (fderiv ℝ (normalMap Ω)) (x, τ))
      (x, τ) :=
    ((hE.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hV : DifferentiableAt ℝ (fun p' => fderiv ℝ (normalMap Ω) p' (mcNormal Ω u p')) (x, τ) :=
    (hD.clm_apply hn.hasFDerivAt).differentiableAt
  have hq : 0 < (normalMap Ω (x, τ)).2 := by
    obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
    exact (lem_normal_b ⟨f, hf⟩ (hUΩ hp.1)).1 τ
  have hc : (fun p' => hypInner (normalMap Ω p') (fderiv ℝ (normalMap Ω) p' (mcNormal Ω u p'))
      (fderiv ℝ (normalMap Ω) p' (mcNormal Ω u p'))) =ᶠ[𝓝 (x, τ)] fun _ => (1 : ℝ) := by
    filter_upwards [hDo.mem_nhds hp] with p' hp'
    exact s05_mc_unit hJ hUΩ hUs u hp'
  have h := s05_mc_compat (hE.differentiableAt (by simp)) hV hV hq (mcNormal Ω u (x, τ))
  rw [hc.fderiv_eq, fderiv_const_apply, zero_apply, s05_mc_2_hi_symm (normalMap Ω (x, τ))
    (fderiv ℝ (normalMap Ω) (x, τ) (mcNormal Ω u (x, τ)))] at h
  linarith

/-! ## M4: the divergence identity (A3, second half) -/

/-- M4 helper: `Σ_{ij} g^{ij} ⟨c_i, g e_j⟩ = Σ_i (c_i)_i` for a symmetric invertible `2 × 2`
matrix `g`. -/
theorem s05_mc_4_trace (g : Matrix (Fin 2) (Fin 2) ℝ) (hg : g 1 0 = g 0 1) (hdet : 0 < g.det)
    (c : Fin 2 → Fin 2 → ℝ) :
    ∑ i : Fin 2, ∑ j : Fin 2, g⁻¹ i j * (c i ⬝ᵥ (g *ᵥ cvec (frameVec j))) =
      ∑ i : Fin 2, c i i := by
  rw [Matrix.det_fin_two] at hdet
  simp only [Fin.sum_univ_two, s05_mc_3_inv, dotProduct, Matrix.mulVec, cvec, frameVec, hg,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val', Complex.one_re,
    Complex.one_im, Complex.I_re, Complex.I_im]
  rw [hg] at hdet
  have hd : g 1 1 * g 0 0 - g 0 1 ^ 2 ≠ 0 := by nlinarith
  field_simp
  linear_combination (c 0 0 + c 1 1) * mul_inv_cancel₀ hd

/-- M4 helper: a linear form on `ℂ × ℝ` in the frame `(e₁, e₂, e₃)`. -/
theorem s05_mc_4_dec (l : ℂ × ℝ →L[ℝ] ℝ) (P : ℂ × ℝ) :
    l P = cvec P.1 0 * l (frameVec 0, 0) + cvec P.1 1 * l (frameVec 1, 0) + P.2 * l (0, 1) := by
  have e : P = cvec P.1 0 • ((frameVec 0, 0) : ℂ × ℝ) + cvec P.1 1 • ((frameVec 1, 0) : ℂ × ℝ) +
      P.2 • (((0 : ℂ), (1 : ℝ)) : ℂ × ℝ) := by
    obtain ⟨a, α⟩ := P
    refine Prod.ext (Complex.ext ?_ ?_) ?_ <;> simp [cvec, frameVec]
  conv_lhs => rw [e]
  simp only [map_add, map_smul, smul_eq_mul]

/-- M4: `tr_ḡ B = (1/√g) ∂_a(√g n^a) = -2 H_up(u)(w)` at `p₀ = (w, u w)`, where
`B(X, Y) = ⟨∇_X V, dE Y⟩`, `V = dE · n`. -/
theorem s05_mc_div {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {U : Set ℂ} (hU : IsOpen U)
    (hUΩ : U ⊆ Ω) (hUs : ∀ y ∈ U, schwarzNorm Ω y < 1 / 4) {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) {w : ℂ} (hw : w ∈ U) (huw : u w < 1) :
    (∑ i : Fin 2, ∑ j : Fin 2, (graphMetric Ω w (u w))⁻¹ i j *
        hypInner (normalMap Ω (w, u w))
          (fderiv ℝ (fun p' => fderiv ℝ (normalMap Ω) p' (mcNormal Ω u p')) (w, u w)
              (frameVec i, 0) +
            hypChristoffel (normalMap Ω (w, u w))
              (fderiv ℝ (normalMap Ω) (w, u w) (frameVec i, 0))
              (fderiv ℝ (normalMap Ω) (w, u w) (mcNormal Ω u (w, u w))))
          (fderiv ℝ (normalMap Ω) (w, u w) (frameVec j, 0))) +
      hypInner (normalMap Ω (w, u w))
        (fderiv ℝ (fun p' => fderiv ℝ (normalMap Ω) p' (mcNormal Ω u p')) (w, u w) (0, 1) +
          hypChristoffel (normalMap Ω (w, u w)) (fderiv ℝ (normalMap Ω) (w, u w) (0, 1))
            (fderiv ℝ (normalMap Ω) (w, u w) (mcNormal Ω u (w, u w))))
        (fderiv ℝ (normalMap Ω) (w, u w) (0, 1)) =
      -2 * meanCurvUp Ω u w := by
  have hwΩ := hUΩ hw
  have hdet := s05_mc_2_det_pos hJ hwΩ (hUs w hw) huw
  have hDo : IsOpen (U ×ˢ Iio (1 : ℝ)) := hU.prod isOpen_Iio
  have hp₀ : (w, u w) ∈ U ×ˢ Iio (1 : ℝ) := ⟨hw, huw⟩
  obtain ⟨hσs, -, -, hns⟩ := s05_mc_smooth hJ hU hUΩ hUs hu
  have hσ : HasFDerivAt (fun p : ℂ × ℝ => graphSdet Ω p.1 p.2)
      (fderiv ℝ (fun p : ℂ × ℝ => graphSdet Ω p.1 p.2) (w, u w)) (w, u w) :=
    ((hσs.contDiffAt (hDo.mem_nhds hp₀)).differentiableAt (by simp)).hasFDerivAt
  have hn : HasFDerivAt (mcNormal Ω u) (fderiv ℝ (mcNormal Ω u) (w, u w)) (w, u w) :=
    ((hns.contDiffAt (hDo.mem_nhds hp₀)).differentiableAt (by simp)).hasFDerivAt
  have hE := s05_mc_2_nm_cd hJ hwΩ (u w)
  have hD : HasFDerivAt (fderiv ℝ (normalMap Ω)) (fderiv ℝ (fderiv ℝ (normalMap Ω)) (w, u w))
      (w, u w) :=
    ((hE.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hV : ∀ X, fderiv ℝ (fun p' => fderiv ℝ (normalMap Ω) p' (mcNormal Ω u p')) (w, u w) X =
      fderiv ℝ (fderiv ℝ (normalMap Ω)) (w, u w) X (mcNormal Ω u (w, u w)) +
        fderiv ℝ (normalMap Ω) (w, u w) (fderiv ℝ (mcNormal Ω u) (w, u w) X) := fun X => by
    rw [(hD.clm_apply hn).fderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
    exact add_comm _ _
  -- split `B = K(·, n) + ḡ(dn ·, ·)`
  have hB : ∀ X Y : ℂ × ℝ, hypInner (normalMap Ω (w, u w))
      (fderiv ℝ (fun p' => fderiv ℝ (normalMap Ω) p' (mcNormal Ω u p')) (w, u w) X +
        hypChristoffel (normalMap Ω (w, u w)) (fderiv ℝ (normalMap Ω) (w, u w) X)
          (fderiv ℝ (normalMap Ω) (w, u w) (mcNormal Ω u (w, u w))))
      (fderiv ℝ (normalMap Ω) (w, u w) Y) =
      hypInner (normalMap Ω (w, u w))
        (fderiv ℝ (fderiv ℝ (normalMap Ω)) (w, u w) X (mcNormal Ω u (w, u w)) +
          hypChristoffel (normalMap Ω (w, u w)) (fderiv ℝ (normalMap Ω) (w, u w) X)
            (fderiv ℝ (normalMap Ω) (w, u w) (mcNormal Ω u (w, u w))))
        (fderiv ℝ (normalMap Ω) (w, u w) Y) +
      hypInner (normalMap Ω (w, u w))
        (fderiv ℝ (normalMap Ω) (w, u w) (fderiv ℝ (mcNormal Ω u) (w, u w) X))
        (fderiv ℝ (normalMap Ω) (w, u w) Y) := fun X Y => by
    rw [hV, add_right_comm, s05_mc_2_hi_add]
  have hG : ∀ (P : ℂ × ℝ) (b : ℂ) (β : ℝ), hypInner (normalMap Ω (w, u w))
      (fderiv ℝ (normalMap Ω) (w, u w) P) (fderiv ℝ (normalMap Ω) (w, u w) (b, β)) =
      cvec P.1 ⬝ᵥ (graphMetric Ω w (u w) *ᵥ cvec b) + P.2 * β := fun P b β => by
    obtain ⟨a, α⟩ := P
    exact s05_mc_gbar hJ hwΩ (by linarith [hUs w hw]) (u w) a b α β
  have hc0 : cvec (0 : ℂ) = 0 := by
    funext i
    fin_cases i <;> simp [cvec]
  simp only [hB, mul_add, Finset.sum_add_distrib]
  rw [add_add_add_comm, s05_mc_contract hJ hU hUΩ hUs hw huw]
  simp only [hG, mul_zero, add_zero, mul_one, hc0, Matrix.mulVec_zero, dotProduct_zero, zero_add]
  rw [s05_mc_4_trace _ (s05_mc_3_symm Ω w (u w)) hdet
    (fun i => cvec (fderiv ℝ (mcNormal Ω u) (w, u w) (frameVec i, 0)).1)]
  -- the right-hand side: product rule for `√g n^a`
  obtain ⟨L, hL⟩ : ∃ L : Fin 2 → ℂ × ℝ →L[ℝ] ℝ, ∀ i P, L i P = cvec P.1 i :=
    ⟨![Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ),
      Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)],
      fun i P => by fin_cases i <;> simp [cvec]⟩
  have hgf : ∀ i x τ, graphFlux Ω u τ x i =
      -(graphSdet Ω x τ * L i (mcNormal Ω u (x, τ))) := by
    intro i x τ
    simp only [hL, graphFlux, mcNormal, s05_mc_3_cvec_ofCvec]
    ring
  have hsw : ∀ τ, graphSdet Ω w τ / graphW Ω u w τ =
      graphSdet Ω w τ * (ContinuousLinearMap.snd ℝ ℂ ℝ) (mcNormal Ω u (w, τ)) := fun τ => by
    simp only [mcNormal, ContinuousLinearMap.coe_snd']
    ring
  have hA : deriv (fun τ => graphSdet Ω w τ / graphW Ω u w τ) (u w) =
      graphSdet Ω w (u w) * (fderiv ℝ (mcNormal Ω u) (w, u w) (0, 1)).2 +
        (mcNormal Ω u (w, u w)).2 *
          fderiv ℝ (fun p : ℂ × ℝ => graphSdet Ω p.1 p.2) (w, u w) (0, 1) := by
    have h3 := hσ.fun_mul ((ContinuousLinearMap.snd ℝ ℂ ℝ).hasFDerivAt.comp (w, u w) hn)
    have h' := h3.comp_hasDerivAt (u w) ((hasDerivAt_const (u w) w).prodMk (hasDerivAt_id (u w)))
    have e : (fun τ => graphSdet Ω w τ / graphW Ω u w τ) =
        (fun p : ℂ × ℝ => graphSdet Ω p.1 p.2 *
          ((ContinuousLinearMap.snd ℝ ℂ ℝ) ∘ mcNormal Ω u) p) ∘ fun τ => (w, τ) := funext hsw
    rw [e, h'.deriv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, Function.comp_apply,
      ContinuousLinearMap.coe_snd', smul_eq_mul]
  have hS : ∀ i, fderiv ℝ (fun x => graphFlux Ω u (u w) x i) w (frameVec i) =
      -(graphSdet Ω w (u w) * L i (fderiv ℝ (mcNormal Ω u) (w, u w) (frameVec i, 0)) +
        L i (mcNormal Ω u (w, u w)) *
          fderiv ℝ (fun p : ℂ × ℝ => graphSdet Ω p.1 p.2) (w, u w) (frameVec i, 0)) := by
    intro i
    have h3 := (hσ.fun_mul ((L i).hasFDerivAt.comp (w, u w) hn)).fun_neg
    have h' := h3.comp w (hasFDerivAt_prodMk_left (𝕜 := ℝ) w (u w))
    have e : (fun x => graphFlux Ω u (u w) x i) =
        (fun p : ℂ × ℝ => -(graphSdet Ω p.1 p.2 * ((L i) ∘ mcNormal Ω u) p)) ∘
          fun x => (x, u w) := by
      funext x
      exact hgf i x (u w)
    rw [e, h'.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, neg_apply,
      add_apply, smul_apply, Function.comp_apply, smul_eq_mul]
  rw [meanCurvUp, hA]
  simp only [hS]
  have hσ0 : 0 < graphSdet Ω w (u w) := Real.sqrt_pos.mpr hdet
  rw [s05_mc_4_dec (fderiv ℝ (fun p : ℂ × ℝ => graphSdet Ω p.1 p.2) (w, u w))
    (mcNormal Ω u (w, u w))]
  simp only [Fin.sum_univ_two, hL]
  field_simp
  ring

/-! ## M6a, M6b: reparametrization, sign of the normal, orientation (A5, A6; by w4) -/

/-! ## M6a: reparametrization and the sign of the normal (A5) -/

/-- M6a helper: `hypInner q` is linear in its first vector. -/
theorem s05_mc_6a_hi_left (q X Y Z : ℂ × ℝ) (a b : ℝ) :
    hypInner q (a • X + b • Y) Z = a * hypInner q X Z + b * hypInner q Y Z := by
  unfold hypInner
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Complex.real_smul, add_mul, Complex.add_re, Complex.re_ofReal_mul, mul_assoc]
  ring

/-- M6a helper: `hypInner q` is linear in its second vector. -/
theorem s05_mc_6a_hi_right (q X Y Z : ℂ × ℝ) (a b : ℝ) :
    hypInner q Z (a • X + b • Y) = a * hypInner q Z X + b * hypInner q Z Y := by
  unfold hypInner
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Complex.real_smul, map_add, mul_add, Complex.add_re, Complex.conj_ofReal, map_mul]
  rw [mul_left_comm Z.1 (a : ℂ), mul_left_comm Z.1 (b : ℂ), Complex.re_ofReal_mul,
    Complex.re_ofReal_mul]
  ring

/-- M6a helper: `hypInner q (-X) Y = -hypInner q X Y`. -/
theorem s05_mc_6a_hi_neg (q X Y : ℂ × ℝ) : hypInner q (-X) Y = -hypInner q X Y := by
  unfold hypInner
  simp only [Prod.fst_neg, Prod.snd_neg, neg_mul, Complex.neg_re]
  ring

/-- M6a helper: `hypChristoffel q` is linear in its first vector. -/
theorem s05_mc_6a_chr_left (q X Y V : ℂ × ℝ) (a b : ℝ) :
    hypChristoffel q (a • X + b • Y) V = a • hypChristoffel q X V + b • hypChristoffel q Y V := by
  unfold hypChristoffel
  ext
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Complex.real_smul, map_add, map_mul, Complex.conj_ofReal, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, mul_zero, zero_mul]
    ring
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Complex.real_smul, map_add, map_mul, Complex.conj_ofReal,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, zero_mul]
    ring

/-- M6a helper: `hypChristoffel q U (-V) = -hypChristoffel q U V`. -/
theorem s05_mc_6a_chr_neg (q U V : ℂ × ℝ) : hypChristoffel q U (-V) = -hypChristoffel q U V := by
  unfold hypChristoffel
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_neg,
      Prod.snd_neg, Complex.real_smul, mul_neg, Complex.neg_re,
      Complex.ofReal_neg, neg_div, neg_neg, Complex.mul_re,
      Prod.fst_add]
    ring
  · simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_neg,
      Prod.snd_neg, smul_eq_mul, mul_neg, Complex.neg_re, neg_div, neg_neg]
    ring

/-- M6a helper: `v = Re v • frameVec 0 + Im v • frameVec 1`. -/
theorem s05_mc_6a_frame (v : ℂ) : v = v.re • frameVec 0 + v.im • frameVec 1 := by
  show v = v.re • (1 : ℂ) + v.im • I
  apply Complex.ext <;> simp

/-- M6a helper: the Gram matrix of a bilinear `β` pulled back by `T` is `Pᵀ M P`, with `P` the
matrix of `T` in the frame `(1, i)`. -/
theorem s05_mc_6a_gram (β : ℂ → ℂ → ℝ)
    (hl : ∀ (a b : ℝ) (X Y Z : ℂ), β (a • X + b • Y) Z = a * β X Z + b * β Y Z)
    (hr : ∀ (a b : ℝ) (X Y Z : ℂ), β Z (a • X + b • Y) = a * β Z X + b * β Z Y)
    (T : ℂ →L[ℝ] ℂ) :
    (Matrix.of fun i j : Fin 2 => β (T (frameVec i)) (T (frameVec j))) =
      (Matrix.of fun k i : Fin 2 => cvec (T (frameVec i)) k)ᵀ *
        (Matrix.of fun k l : Fin 2 => β (frameVec k) (frameVec l)) *
          (Matrix.of fun k i : Fin 2 => cvec (T (frameVec i)) k) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  rw [s05_mc_6a_frame (T (frameVec i)), s05_mc_6a_frame (T (frameVec j)), hl, hr, hr]
  simp only [cvec, Matrix.cons_val_zero, Matrix.cons_val_one, ← s05_mc_6a_frame]
  ring

/-- M6a helper: an injective real-linear `T : ℂ → ℂ` has invertible frame matrix. -/
theorem s05_mc_6a_det_ne {T : ℂ →L[ℝ] ℂ} (hT : Function.Injective T) :
    (Matrix.of fun k i : Fin 2 => cvec (T (frameVec i)) k).det ≠ 0 := by
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hT0 : T (c 0 • frameVec 0 + c 1 • frameVec 1) = 0 := by
    rw [map_add, map_smul, map_smul]
    have e0 := congrFun hc 0
    have e1 := congrFun hc 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, cvec,
      Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at e0 e1
    apply Complex.ext
    · simp only [Complex.add_re, Complex.real_smul, Complex.re_ofReal_mul, Complex.zero_re]
      linarith
    · simp only [Complex.add_im, Complex.real_smul, Complex.im_ofReal_mul, Complex.zero_im]
      linarith
  have hv := hT (hT0.trans (map_zero T).symm)
  apply hc0
  funext k
  have h0' : (c 0 • frameVec 0 + c 1 • frameVec 1 : ℂ) = 0 := hv
  have hre := congrArg Complex.re h0'
  have him := congrArg Complex.im h0'
  simp only [frameVec, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.I_re,
    Complex.I_im, Complex.zero_re, Complex.zero_im] at hre him
  fin_cases k
  · simp only [Fin.zero_eta, Pi.zero_apply]
    linarith
  · simp only [Fin.mk_one, Pi.zero_apply]
    linarith

/-- M6a helper: `tr((PᵀAP)⁻¹ (PᵀBP)ᵀ) = tr(A⁻¹ Bᵀ)` for invertible `P`. -/
theorem s05_mc_6a_trace_conj (P A B : Matrix (Fin 2) (Fin 2) ℝ) (hP : P.det ≠ 0) :
    ((Pᵀ * A * P)⁻¹ * (Pᵀ * B * P)ᵀ).trace = (A⁻¹ * Bᵀ).trace := by
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  have hut : IsUnit Pᵀ.det := by rwa [Matrix.det_transpose]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  have e : P⁻¹ * (A⁻¹ * Pᵀ⁻¹) * (Pᵀ * (Bᵀ * P)) = P⁻¹ * (A⁻¹ * Bᵀ) * P := by
    rw [show P⁻¹ * (A⁻¹ * Pᵀ⁻¹) * (Pᵀ * (Bᵀ * P)) = P⁻¹ * A⁻¹ * (Pᵀ⁻¹ * Pᵀ) * Bᵀ * P by
      simp only [Matrix.mul_assoc], Matrix.nonsing_inv_mul _ hut, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

/-- M6a: if `Φ = Ψ ∘ N` and `ν = -μ ∘ N` near `w` with `dN_w` injective and `I_Φ` nondegenerate,
then `immMeanCurv Φ ν w = -immMeanCurv Ψ μ (N w)`. -/
theorem s05_mc_reparam {Φ Ψ ν μ : ℂ → ℂ × ℝ} {N : ℂ → ℂ} {w : ℂ}
    (hΦ : Φ =ᶠ[𝓝 w] Ψ ∘ N) (hν : ν =ᶠ[𝓝 w] fun x => -μ (N x))
    (hN : DifferentiableAt ℝ N w) (hΨ : DifferentiableAt ℝ Ψ (N w))
    (hμ : DifferentiableAt ℝ μ (N w)) (hinj : Function.Injective (fderiv ℝ N w))
    (hI : (Matrix.of fun i j : Fin 2 =>
        hypInner (Φ w) (fderiv ℝ Φ w (frameVec i)) (fderiv ℝ Φ w (frameVec j))).det ≠ 0) :
    immMeanCurv Φ ν w = -immMeanCurv Ψ μ (N w) := by
  -- `hI` is not needed: the trace identity only uses that `dN_w` is invertible (the junk
  -- inverse `0` of a singular Gram matrix is transported consistently); the statement stays
  -- true without it.
  have _h := hI
  rw [s05_mc_imm_congr hΦ hν]
  set T := fderiv ℝ N w
  set L := fderiv ℝ Ψ (N w)
  set M := fderiv ℝ μ (N w)
  set q := Ψ (N w)
  have hdΦ : fderiv ℝ (Ψ ∘ N) w = L.comp T := fderiv_comp w hΨ hN
  have hdν : fderiv ℝ (fun x => -μ (N x)) w = -(M.comp T) :=
    ((hμ.hasFDerivAt.comp w hN.hasFDerivAt).neg).fderiv
  set P := Matrix.of fun k i : Fin 2 => cvec (T (frameVec i)) k
  have hP := s05_mc_6a_det_ne hinj
  have hIg := s05_mc_6a_gram (fun v v' => hypInner q (L v) (L v'))
    (fun a b X Y Z => by simp only [map_add, map_smul]; exact s05_mc_6a_hi_left _ _ _ _ _ _)
    (fun a b X Y Z => by simp only [map_add, map_smul]; exact s05_mc_6a_hi_right _ _ _ _ _ _) T
  have hIIg := s05_mc_6a_gram
    (fun v v' => hypInner q (-(M v + hypChristoffel q (L v) (μ (N w)))) (L v'))
    (fun a b X Y Z => by
      simp only [map_add, map_smul, s05_mc_6a_chr_left]
      rw [show -(a • M X + b • M Y + (a • hypChristoffel q (L X) (μ (N w)) +
          b • hypChristoffel q (L Y) (μ (N w)))) =
          a • (-(M X + hypChristoffel q (L X) (μ (N w)))) +
            b • (-(M Y + hypChristoffel q (L Y) (μ (N w)))) by
        simp only [smul_neg, smul_add]; abel]
      exact s05_mc_6a_hi_left _ _ _ _ _ _)
    (fun a b X Y Z => by simp only [map_add, map_smul]; exact s05_mc_6a_hi_right _ _ _ _ _ _) T
  have hIΦ : (Matrix.of fun i j : Fin 2 =>
      hypInner ((Ψ ∘ N) w) (fderiv ℝ (Ψ ∘ N) w (frameVec i))
        (fderiv ℝ (Ψ ∘ N) w (frameVec j))) =
      Pᵀ * (Matrix.of fun k l : Fin 2 => hypInner q (L (frameVec k)) (L (frameVec l))) * P := by
    rw [← hIg, hdΦ]
    rfl
  have hIIΦ : (Matrix.of fun i j : Fin 2 =>
      hypInner ((Ψ ∘ N) w)
        (-(fderiv ℝ (fun x => -μ (N x)) w (frameVec i) +
          hypChristoffel ((Ψ ∘ N) w) (fderiv ℝ (Ψ ∘ N) w (frameVec i)) (-μ (N w))))
        (fderiv ℝ (Ψ ∘ N) w (frameVec j))) =
      Pᵀ * (-(Matrix.of fun k l : Fin 2 =>
        hypInner q (-(M (frameVec k) + hypChristoffel q (L (frameVec k)) (μ (N w))))
          (L (frameVec l)))) * P := by
    rw [Matrix.mul_neg, Matrix.neg_mul, ← hIIg, hdν, hdΦ]
    ext i j
    simp only [Matrix.of_apply, Matrix.neg_apply, _root_.neg_apply,
      ContinuousLinearMap.comp_apply, Function.comp_apply, s05_mc_6a_chr_neg]
    rw [show -(-M (T (frameVec i)) + -hypChristoffel q (L (T (frameVec i))) (μ (N w))) =
        -(-(M (T (frameVec i)) + hypChristoffel q (L (T (frameVec i))) (μ (N w)))) by abel,
      s05_mc_6a_hi_neg]
  unfold immMeanCurv
  rw [hIΦ, hIIΦ, Matrix.mul_neg, Matrix.neg_mul, Matrix.transpose_neg, Matrix.mul_neg,
    Matrix.trace_neg, s05_mc_6a_trace_conj P _ _ hP, neg_div]

/-- M6a: two `hypInner`-unit vectors orthogonal to two independent vectors agree up to sign. -/
theorem s05_mc_normal_pm {q a b n₁ n₂ : ℂ × ℝ} (hq : 0 < q.2)
    (hab : hypInner q a a * hypInner q b b - hypInner q a b ^ 2 ≠ 0)
    (h₁ : hypInner q n₁ n₁ = 1) (h₂ : hypInner q n₂ n₂ = 1)
    (h₁a : hypInner q n₁ a = 0) (h₁b : hypInner q n₁ b = 0)
    (h₂a : hypInner q n₂ a = 0) (h₂b : hypInner q n₂ b = 0) : n₁ = n₂ ∨ n₁ = -n₂ := by
  have hq2 : q.2 ^ 2 ≠ 0 := by positivity
  unfold hypInner at hab h₁ h₂ h₁a h₁b h₂a h₂b
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add]
    at hab h₁ h₂ h₁a h₁b h₂a h₂b
  rw [div_eq_zero_iff, or_iff_left hq2] at h₁a h₁b h₂a h₂b
  rw [div_eq_one_iff_eq hq2] at h₁ h₂
  -- Euclidean coordinates
  set a1 := a.1.re
  set a2 := a.1.im
  set a3 := a.2
  set b1 := b.1.re
  set b2 := b.1.im
  set b3 := b.2
  -- the cross product `c = a × b` and `D = |c|²`
  set c1 := a2 * b3 - a3 * b2
  set c2 := a3 * b1 - a1 * b3
  set c3 := a1 * b2 - a2 * b1
  set D := c1 ^ 2 + c2 ^ 2 + c3 ^ 2
  have hD : D ≠ 0 := by
    intro h0
    apply hab
    have : (a1 * a1 + a2 * a2 + a3 * a3) * (b1 * b1 + b2 * b2 + b3 * b3) -
        (a1 * b1 + a2 * b2 + a3 * b3) ^ 2 = D := by ring
    rw [div_mul_div_comm, div_pow, ← pow_mul]
    rw [show (a.1.re * a.1.re + a.1.im * a.1.im + a.2 * a.2) *
        (b.1.re * b.1.re + b.1.im * b.1.im + b.2 * b.2) / (q.2 ^ 2 * q.2 ^ 2) -
        (a.1.re * b.1.re + a.1.im * b.1.im + a.2 * b.2) ^ 2 / q.2 ^ (2 * 2) =
        D / q.2 ^ 4 by rw [← this]; ring, h0, zero_div]
  -- every vector orthogonal to `a, b` is a multiple of `c`
  have key : ∀ n : ℂ × ℝ, n.1.re * a1 + n.1.im * a2 + n.2 * a3 = 0 →
      n.1.re * b1 + n.1.im * b2 + n.2 * b3 = 0 →
      D * n.1.re = (n.1.re * c1 + n.1.im * c2 + n.2 * c3) * c1 ∧
        D * n.1.im = (n.1.re * c1 + n.1.im * c2 + n.2 * c3) * c2 ∧
          D * n.2 = (n.1.re * c1 + n.1.im * c2 + n.2 * c3) * c3 := by
    intro n ha hb
    refine ⟨?_, ?_, ?_⟩
    · linear_combination -(c2 * b3 - c3 * b2) * ha + (c2 * a3 - c3 * a2) * hb
    · linear_combination -(c3 * b1 - c1 * b3) * ha + (c3 * a1 - c1 * a3) * hb
    · linear_combination -(c1 * b2 - c2 * b1) * ha + (c1 * a2 - c2 * a1) * hb
  obtain ⟨k1, k2, k3⟩ := key n₁ (by linarith) (by linarith)
  obtain ⟨l1, l2, l3⟩ := key n₂ (by linarith) (by linarith)
  set s := n₁.1.re * c1 + n₁.1.im * c2 + n₁.2 * c3
  set t := n₂.1.re * c1 + n₂.1.im * c2 + n₂.2 * c3
  have hn : n₁.1.re * n₁.1.re + n₁.1.im * n₁.1.im + n₁.2 * n₁.2 =
      n₂.1.re * n₂.1.re + n₂.1.im * n₂.1.im + n₂.2 * n₂.2 := by linarith
  have hst : D * (s ^ 2 - t ^ 2) = 0 := by
    have e1 : D ^ 2 * (n₁.1.re * n₁.1.re + n₁.1.im * n₁.1.im + n₁.2 * n₁.2) = s ^ 2 * D := by
      linear_combination (D * n₁.1.re + s * c1) * k1 + (D * n₁.1.im + s * c2) * k2 +
        (D * n₁.2 + s * c3) * k3
    have e2 : D ^ 2 * (n₂.1.re * n₂.1.re + n₂.1.im * n₂.1.im + n₂.2 * n₂.2) = t ^ 2 * D := by
      linear_combination (D * n₂.1.re + t * c1) * l1 + (D * n₂.1.im + t * c2) * l2 +
        (D * n₂.2 + t * c3) * l3
    linear_combination e2 - e1 + D ^ 2 * hn
  have hst' : (s - t) * (s + t) = 0 := by
    have := (mul_eq_zero.mp hst).resolve_left hD
    linear_combination this
  rcases mul_eq_zero.mp hst' with h | h
  · left
    have hs : s = t := by linarith
    refine Prod.ext (Complex.ext ?_ ?_) ?_
    · exact mul_left_cancel₀ hD (by rw [k1, l1, hs])
    · exact mul_left_cancel₀ hD (by rw [k2, l2, hs])
    · exact mul_left_cancel₀ hD (by rw [k3, l3, hs])
  · right
    have hs : s = -t := by linarith
    refine Prod.ext (Complex.ext ?_ ?_) ?_
    · exact mul_left_cancel₀ hD (by
        rw [k1, Prod.fst_neg, Complex.neg_re, mul_neg, l1, hs]; ring)
    · exact mul_left_cancel₀ hD (by
        rw [k2, Prod.fst_neg, Complex.neg_im, mul_neg, l2, hs]; ring)
    · exact mul_left_cancel₀ hD (by rw [k3, Prod.snd_neg, mul_neg, l3, hs]; ring)

/-- M6a helper: the two components of a Jordan pair are open. -/
theorem s05_mc_6a_isOpen {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) : IsOpen Ω := by
  obtain ⟨F, hF, -⟩ := hJ
  exact hF ▸ F.isOpenMap _ isOpen_upperHalf

/-- M6a: `ν*` is a unit normal of `X*` (`lem_shape_a` at `τ = 0`, `E(·, 0) = X`). -/
theorem s05_mc_nu_normal {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {z : ℂ} (hz : z ∈ Ω)
    (hs : schwarzNorm Ω z ≠ 1) :
    hypInner (epstein Ω z) (normalVec Ω z) (normalVec Ω z) = 1 ∧
      ∀ v : ℂ, hypInner (epstein Ω z) (normalVec Ω z) (fderiv ℝ (epstein Ω) z v) = 0 := by
  have hΩ := s02_jordanPair_riemannMap hJ
  have hl := s02_poincareDensity_pos hΩ hz
  have h := lem_shape_a Ω Ωs hJ z hz hs 0
  rw [s02_normalGeod_zero Ω z hl] at h
  have hev : (fun x => normalGeod Ω x 0) =ᶠ[𝓝 z] epstein Ω := by
    filter_upwards [(s05_mc_6a_isOpen hJ).mem_nhds hz] with x hx
    exact s02_normalGeod_zero Ω x (s02_poincareDensity_pos hΩ hx)
  refine ⟨h.1, fun v => ?_⟩
  have h2 := h.2.1 v
  rwa [hev.fderiv_eq] at h2

/-! ## M6b: orientation (A6) -/

/-- M6b helper: `q ↦ Φ_q(z)` is differentiable on `ℍ³` with
`dΦ_q(z)(Y) = λ Re(conj(q₁ - z) Y₁)/q₂ + λ (q₂² - |q₁ - z|²) Y₂/(2 q₂²)`. -/
theorem s05_mc_6b_horo_fderiv (Ω : Set ℂ) (z : ℂ) {q : ℂ × ℝ} (hq : 0 < q.2) :
    DifferentiableAt ℝ (fun q' => horoPhi Ω q' z) q ∧ ∀ Y : ℂ × ℝ,
      fderiv ℝ (fun q' => horoPhi Ω q' z) q Y =
        poincareDensity Ω z * (conj (q.1 - z) * Y.1).re / q.2 +
          poincareDensity Ω z * (q.2 ^ 2 - ‖q.1 - z‖ ^ 2) * Y.2 / (2 * q.2 ^ 2) := by
  set l := poincareDensity Ω z
  have hfun : (fun q' => horoPhi Ω q' z) = fun q' : ℂ × ℝ =>
      l * (‖q'.1 - z‖ ^ 2 + q'.2 * q'.2) * (2 * q'.2)⁻¹ := by
    funext q'
    show l * (‖q'.1 - z‖ ^ 2 + q'.2 ^ 2) / (2 * q'.2) = _
    rw [div_eq_mul_inv, sq q'.2]
  have h1 : HasFDerivAt (fun q' : ℂ × ℝ => q'.1 - z) (ContinuousLinearMap.fst ℝ ℂ ℝ) q :=
    (hasFDerivAt_fst).sub_const z
  have h2 := h1.norm_sq
  have h3 : HasFDerivAt (fun q' : ℂ × ℝ => q'.2 * q'.2)
      (q.2 • ContinuousLinearMap.snd ℝ ℂ ℝ + q.2 • ContinuousLinearMap.snd ℝ ℂ ℝ) q :=
    (hasFDerivAt_snd).mul hasFDerivAt_snd
  have h4 : HasFDerivAt (fun q' : ℂ × ℝ => 2 * q'.2) ((2 : ℝ) • ContinuousLinearMap.snd ℝ ℂ ℝ) q :=
    (hasFDerivAt_snd).const_mul 2
  have h5 := (hasFDerivAt_inv (show 2 * q.2 ≠ 0 by positivity)).comp q h4
  have h6 := HasFDerivAt.mul (HasFDerivAt.const_mul (HasFDerivAt.add h2 h3) l) h5
  have h7 : HasFDerivAt
      (fun q' : ℂ × ℝ => l * (‖q'.1 - z‖ ^ 2 + q'.2 * q'.2) * (2 * q'.2)⁻¹) _ q := h6
  rw [hfun]
  refine ⟨h7.differentiableAt, fun Y => ?_⟩
  rw [h7.fderiv]
  simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
    Pi.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', innerSL_apply_apply,
    smul_eq_mul, ContinuousLinearMap.toSpanSingleton_apply, Complex.inner]
  have hq0 : q.2 ≠ 0 := hq.ne'
  rw [mul_comm Y.1]
  field_simp
  ring

/-- M6b: the hyperbolic gradient of `q ↦ Φ_q(z)` at `X(z)` is `ν(z)`. -/
theorem s05_mc_horo_grad {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {z : ℂ}
    (hz : z ∈ Ω) (Y : ℂ × ℝ) :
    fderiv ℝ (fun q => horoPhi Ω q z) (epstein Ω z) Y =
      hypInner (epstein Ω z) (normalVec Ω z) Y := by
  have hl := s02_poincareDensity_pos hΩ hz
  have hX := s02_normalGeod_zero Ω z hl
  have hpos := s02_normalGeod_pos Ω z hl 0
  rw [hX] at hpos
  rw [(s05_mc_6b_horo_fderiv Ω z hpos).2 Y]
  have hν : normalVec Ω z = _ := (s02_hasDerivAt_normalGeod Ω z hl).deriv
  rw [hν, ← hX]
  unfold normalGeod hypInner
  rw [neg_zero, Real.exp_zero, mul_one]
  generalize poincareDensity Ω z = l at hl ⊢
  generalize logDensityDz Ω z = A
  have hD : 0 < ‖A‖ ^ 2 + (l / 2) ^ 2 := by positivity
  have hD' : ((‖A‖ ^ 2 + (l / 2) ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  simp only [add_sub_cancel_left, map_div₀, Complex.conj_conj, Complex.conj_ofReal,
    norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hD.le]
  simp only [div_mul_eq_mul_div, Complex.div_ofReal_re, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  generalize ‖A‖ ^ 2 + (l / 2) ^ 2 = D at hD hD' ⊢
  have hl0 : l ≠ 0 := hl.ne'
  have hD0 : D ≠ 0 := hD.ne'
  field_simp
  ring

/-- M6b: `ν*(N v)` points back along the normal geodesic: `⟨ν*(N v), ∂_τ E(v, t v)⟩ ≤ 0`, from
`E(v, τ) ∉ U*` for `0 ≤ τ < t v` (`lem_tube` (iv)) and `Φ*_{X*(z)}(z) = 1`. -/
theorem s05_mc_orient {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {v z : ℂ} (hv : v ∈ Ω)
    (hz : z ∈ Ωs) {t : ℝ} (ht : 0 < t) (hX : epstein Ωs z = normalGeod Ω v t)
    (hout : ∀ τ ∈ Ico 0 t, normalGeod Ω v τ ∉ horoUnion Ωs) :
    hypInner (epstein Ωs z) (normalVec Ωs z) (deriv (fun τ => normalGeod Ω v τ) t) ≤ 0 := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  have hΩs := s02_jordanPair_riemannMap (s02_jordanPair_symm hJ)
  have hls := s02_poincareDensity_pos hΩs hz
  -- the normal geodesic is differentiable at `t`
  have hO : IsOpen (Ω ×ˢ (univ : Set ℝ)) := (s05_mc_6a_isOpen hJ).prod isOpen_univ
  have hE : DifferentiableAt ℝ (normalMap Ω) (v, t) :=
    ((s04_tb_nm_smooth hf).contDiffAt (hO.mem_nhds ⟨hv, trivial⟩)).differentiableAt
      (by simp)
  have hγ : HasDerivAt (fun τ => normalGeod Ω v τ) (deriv (fun τ => normalGeod Ω v τ) t) t := by
    have := hE.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t v).prodMk (hasDerivAt_id t))
    exact this.differentiableAt.hasDerivAt
  -- `φ(τ) = Φ*_{E(v,τ)}(z)` and its derivative at `t`
  have hq : 0 < (epstein Ωs z).2 := by
    have := s02_normalGeod_pos Ωs z hls 0
    rwa [s02_normalGeod_zero Ωs z hls] at this
  have hψ := (s05_mc_6b_horo_fderiv Ωs z hq).1
  rw [hX] at hψ
  have hφ := hψ.hasFDerivAt.comp_hasDerivAt t hγ
  rw [← s05_mc_horo_grad hΩs hz, hX]
  -- `φ(t) = 1 < φ(τ)` for `τ ∈ [0, t)`
  have hφt : horoPhi Ωs (normalGeod Ω v t) z = 1 := by
    rw [← hX, ← s02_normalGeod_zero Ωs z hls, s02_horoPhi_normalGeod Ωs z hls 0, Real.exp_zero]
  have hgt : ∀ τ ∈ Ico 0 t, 1 < horoPhi Ωs (normalGeod Ω v τ) z := by
    intro τ hτ
    by_contra hle
    apply hout τ hτ
    exact mem_iUnion₂.mpr ⟨z, hz, (lem_normal_b ⟨f, hf⟩ hv).1 τ, not_lt.mp hle⟩
  have hs := hasDerivAt_iff_tendsto_slope.mp hφ
  have hs' := hs.mono_left (nhdsLT_le_nhdsNE t)
  refine le_of_tendsto hs' ?_
  filter_upwards [Ioo_mem_nhdsLT ht] with τ hτ
  rw [slope_def_field]
  simp only [Function.comp_apply]
  rw [hφt]
  exact (div_neg_of_pos_of_neg (by linarith [hgt τ ⟨hτ.1.le, hτ.2⟩]) (by linarith [hτ.2])).le

/-! ## M5: the graph surface (A4) -/

/-- M5 helper: a bilinear `B` on `ℂ × ℝ` in the frame `(e₁, e₂, e₃)`. -/
theorem s05_mc_5_rep (B : ℂ × ℝ → ℂ × ℝ → ℝ) (hB₁ : ∀ Y, IsLinearMap ℝ fun X => B X Y)
    (hB₂ : ∀ X, IsLinearMap ℝ (B X)) :
    ∃ b : Fin 3 → Fin 3 → ℝ, ∀ X Y : ℂ × ℝ, B X Y =
      ∑ a : Fin 3, ∑ c : Fin 3, ![X.1.re, X.1.im, X.2] a * ![Y.1.re, Y.1.im, Y.2] c * b a c := by
  have e : ∀ X : ℂ × ℝ, X = X.1.re • (((1 : ℂ), (0 : ℝ)) : ℂ × ℝ) + X.1.im • ((I, 0) : ℂ × ℝ) +
      X.2 • (((0 : ℂ), (1 : ℝ)) : ℂ × ℝ) := by
    rintro ⟨a, α⟩
    refine Prod.ext (Complex.ext ?_ ?_) ?_ <;> simp
  have h1 : ∀ X Y, B X Y = X.1.re * B ((1 : ℂ), (0 : ℝ)) Y + X.1.im * B (I, 0) Y +
      X.2 * B ((0 : ℂ), (1 : ℝ)) Y := by
    intro X Y
    conv_lhs => rw [e X]
    rw [(hB₁ Y).map_add, (hB₁ Y).map_add, (hB₁ Y).map_smul, (hB₁ Y).map_smul,
      (hB₁ Y).map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  have h2 : ∀ X Y, B X Y = Y.1.re * B X ((1 : ℂ), (0 : ℝ)) + Y.1.im * B X (I, 0) +
      Y.2 * B X ((0 : ℂ), (1 : ℝ)) := by
    intro X Y
    conv_lhs => rw [e Y]
    rw [(hB₂ X).map_add, (hB₂ X).map_add, (hB₂ X).map_smul, (hB₂ X).map_smul,
      (hB₂ X).map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  refine ⟨fun a c => B (![((1 : ℂ), (0 : ℝ)), (I, 0), (0, 1)] a)
    (![((1 : ℂ), (0 : ℝ)), (I, 0), (0, 1)] c), fun X Y => ?_⟩
  rw [h1 X Y, h2 ((1 : ℂ), (0 : ℝ)) Y, h2 (I, 0) Y, h2 ((0 : ℂ), (1 : ℝ)) Y]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

/-- M5: `2 × 2` trace algebra (Sherman–Morrison): for a bilinear `B` on `ℂ × ℝ`, the trace over
the basis `t_k = (e_k, q_k)`, `n` equals the trace over `(e₁, e₂, e₃)` w.r.t. `diag(g, 1)`. -/
theorem s05_mc_trace_alg (g : Matrix (Fin 2) (Fin 2) ℝ) (hg : gᵀ = g) (hg0 : 0 < g 0 0)
    (hdet : 0 < g.det) (q : Fin 2 → ℝ) (B : ℂ × ℝ → ℂ × ℝ → ℝ)
    (hB₁ : ∀ Y, IsLinearMap ℝ fun X => B X Y) (hB₂ : ∀ X, IsLinearMap ℝ (B X)) :
    (∑ k : Fin 2, ∑ l : Fin 2, (Matrix.of fun k l : Fin 2 => g k l + q k * q l)⁻¹ k l *
        B (frameVec k, q k) (frameVec l, q l)) +
      B (ofCvec (fun i => -(g⁻¹ *ᵥ q) i / Real.sqrt (1 + q ⬝ᵥ (g⁻¹ *ᵥ q))),
          1 / Real.sqrt (1 + q ⬝ᵥ (g⁻¹ *ᵥ q)))
        (ofCvec (fun i => -(g⁻¹ *ᵥ q) i / Real.sqrt (1 + q ⬝ᵥ (g⁻¹ *ᵥ q))),
          1 / Real.sqrt (1 + q ⬝ᵥ (g⁻¹ *ᵥ q))) =
      (∑ i : Fin 2, ∑ j : Fin 2, g⁻¹ i j * B (frameVec i, 0) (frameVec j, 0)) + B (0, 1) (0, 1) := by
  obtain ⟨b, hb⟩ := s05_mc_5_rep B hB₁ hB₂
  have hg10 : g 1 0 = g 0 1 := by
    have := congrFun (congrFun hg 0) 1
    simpa using this
  rw [Matrix.det_fin_two, hg10] at hdet
  -- `Q = q · g⁻¹ q ≥ 0` and `W⁻² = det g / det (g + q qᵀ)`
  have hQ : q ⬝ᵥ (g⁻¹ *ᵥ q) = (g 1 1 * q 0 ^ 2 - 2 * g 0 1 * q 0 * q 1 + g 0 0 * q 1 ^ 2) /
      (g 0 0 * g 1 1 - g 0 1 ^ 2) := by
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, s05_mc_3_inv, hg10, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val']
    field_simp
    ring
  have hnum : 0 ≤ g 1 1 * q 0 ^ 2 - 2 * g 0 1 * q 0 * q 1 + g 0 0 * q 1 ^ 2 := by
    have : 0 ≤ g 0 0 * (g 1 1 * q 0 ^ 2 - 2 * g 0 1 * q 0 * q 1 + g 0 0 * q 1 ^ 2) := by
      nlinarith [sq_nonneg (g 0 0 * q 1 - g 0 1 * q 0), sq_nonneg (q 0)]
    exact (mul_nonneg_iff_of_pos_left hg0).mp this
  have hd1 : g 0 0 * g 1 1 - g 0 1 * g 0 1 ≠ 0 := hdet.ne'
  have hdM : (g 0 0 + q 0 * q 0) * (g 1 1 + q 1 * q 1) - (g 0 1 + q 0 * q 1) * (g 0 1 + q 1 * q 0)
      ≠ 0 := by
    nlinarith
  have hQ0 : 0 ≤ q ⬝ᵥ (g⁻¹ *ᵥ q) := by
    rw [hQ]
    exact div_nonneg hnum (by nlinarith)
  -- `n = W⁻¹ ñ`
  have hBn : B (ofCvec (fun i => -(g⁻¹ *ᵥ q) i / Real.sqrt (1 + q ⬝ᵥ (g⁻¹ *ᵥ q))),
          1 / Real.sqrt (1 + q ⬝ᵥ (g⁻¹ *ᵥ q)))
        (ofCvec (fun i => -(g⁻¹ *ᵥ q) i / Real.sqrt (1 + q ⬝ᵥ (g⁻¹ *ᵥ q))),
          1 / Real.sqrt (1 + q ⬝ᵥ (g⁻¹ *ᵥ q))) =
      (1 / Real.sqrt (1 + q ⬝ᵥ (g⁻¹ *ᵥ q))) * (1 / Real.sqrt (1 + q ⬝ᵥ (g⁻¹ *ᵥ q))) *
        B (ofCvec fun i => -(g⁻¹ *ᵥ q) i, 1) (ofCvec fun i => -(g⁻¹ *ᵥ q) i, 1) := by
    rw [hb, hb]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, ofCvec]
    ring
  have hW : (1 / Real.sqrt (1 + q ⬝ᵥ (g⁻¹ *ᵥ q))) * (1 / Real.sqrt (1 + q ⬝ᵥ (g⁻¹ *ᵥ q))) =
      (g 0 0 * g 1 1 - g 0 1 * g 0 1) /
        ((g 0 0 + q 0 * q 0) * (g 1 1 + q 1 * q 1) - (g 0 1 + q 0 * q 1) * (g 0 1 + q 1 * q 0)) := by
    have hd2 : g 0 0 * g 1 1 - g 0 1 ^ 2 ≠ 0 := by nlinarith
    have hd3 : g 0 0 * g 1 1 - g 0 1 ^ 2 +
        (g 1 1 * q 0 ^ 2 - 2 * g 0 1 * q 0 * q 1 + g 0 0 * q 1 ^ 2) ≠ 0 := by nlinarith
    rw [div_mul_div_comm, one_mul, ← sq, Real.sq_sqrt (by linarith), hQ, one_add_div hd2,
      one_div_div, div_eq_div_iff hd3 hdM]
    ring
  rw [hBn, hW]
  simp only [hb, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ofCvec, frameVec, s05_mc_3_inv,
    Matrix.of_apply, hg10, Matrix.mulVec, dotProduct, Matrix.cons_val', Matrix.cons_val_fin_one,
    Matrix.empty_val', Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    Complex.zero_re, Complex.zero_im]
  generalize hδ : g 0 0 * g 1 1 - g 0 1 * g 0 1 = δ at hd1 ⊢
  generalize hμ : (g 0 0 + q 0 * q 0) * (g 1 1 + q 1 * q 1) -
    (g 0 1 + q 0 * q 1) * (g 0 1 + q 1 * q 0) = μ at hdM ⊢
  field_simp
  subst hδ hμ
  ring

/-- M5 (A4): the graph surface `Φ = E(·, u ·)` with normal `V(·, u ·)` has mean curvature
`H_up(u)` (`secondFF` convention). -/
theorem s05_mc_surface {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {U : Set ℂ} (hU : IsOpen U)
    (hUΩ : U ⊆ Ω) (hUs : ∀ y ∈ U, schwarzNorm Ω y < 1 / 4) {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) {w : ℂ} (hw : w ∈ U) (huw : u w < 1) :
    immMeanCurv (fun x => normalMap Ω (x, u x))
        (fun x => fderiv ℝ (normalMap Ω) (x, u x) (mcNormal Ω u (x, u x))) w =
      meanCurvUp Ω u w := by
  have hwΩ := hUΩ hw
  have hdet := s05_mc_2_det_pos hJ hwΩ (hUs w hw) huw
  have hDo : IsOpen (U ×ˢ Iio (1 : ℝ)) := hU.prod isOpen_Iio
  have hp₀ : (w, u w) ∈ U ×ˢ Iio (1 : ℝ) := ⟨hw, huw⟩
  have hn : HasFDerivAt (mcNormal Ω u) (fderiv ℝ (mcNormal Ω u) (w, u w)) (w, u w) :=
    (((s05_mc_smooth hJ hU hUΩ hUs hu).2.2.2.contDiffAt (hDo.mem_nhds hp₀)).differentiableAt
      (by simp)).hasFDerivAt
  have hE := s05_mc_2_nm_cd hJ hwΩ (u w)
  have hEd : HasFDerivAt (normalMap Ω) (fderiv ℝ (normalMap Ω) (w, u w)) (w, u w) :=
    (hE.differentiableAt (by simp)).hasFDerivAt
  have hD : HasFDerivAt (fderiv ℝ (normalMap Ω)) (fderiv ℝ (fderiv ℝ (normalMap Ω)) (w, u w))
      (w, u w) :=
    ((hE.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hVd : HasFDerivAt (fun p' => fderiv ℝ (normalMap Ω) p' (mcNormal Ω u p'))
      (fderiv ℝ (fun p' => fderiv ℝ (normalMap Ω) p' (mcNormal Ω u p')) (w, u w)) (w, u w) :=
    (hD.clm_apply hn).differentiableAt.hasFDerivAt
  have hu' : HasFDerivAt u (fderiv ℝ u w) w :=
    ((hu.contDiffAt (hU.mem_nhds hw)).differentiableAt (by simp)).hasFDerivAt
  have hγ : HasFDerivAt (fun x => (x, u x)) ((ContinuousLinearMap.id ℝ ℂ).prod (fderiv ℝ u w))
      w := (hasFDerivAt_id w).prodMk hu'
  -- `dΦ e_k = dE t_k`, `dν e_k = dV t_k`, `t_k = (e_k, u_k)`
  have hΦ : ∀ k : Fin 2, fderiv ℝ (fun x => normalMap Ω (x, u x)) w (frameVec k) =
      fderiv ℝ (normalMap Ω) (w, u w) (frameVec k, gradCoords u w k) := fun k => by
    have h' := hEd.comp w hγ
    have h : HasFDerivAt (fun x => normalMap Ω (x, u x))
        ((fderiv ℝ (normalMap Ω) (w, u w)).comp
          ((ContinuousLinearMap.id ℝ ℂ).prod (fderiv ℝ u w))) w := h'
    rw [h.fderiv]
    rfl
  have hν : ∀ k : Fin 2,
      fderiv ℝ (fun x => fderiv ℝ (normalMap Ω) (x, u x) (mcNormal Ω u (x, u x))) w (frameVec k) =
        fderiv ℝ (fun p' => fderiv ℝ (normalMap Ω) p' (mcNormal Ω u p')) (w, u w)
          (frameVec k, gradCoords u w k) := fun k => by
    have h' := hVd.comp w hγ
    have h : HasFDerivAt (fun x => fderiv ℝ (normalMap Ω) (x, u x) (mcNormal Ω u (x, u x)))
        ((fderiv ℝ (fun p' => fderiv ℝ (normalMap Ω) p' (mcNormal Ω u p')) (w, u w)).comp
          ((ContinuousLinearMap.id ℝ ℂ).prod (fderiv ℝ u w))) w := h'
    rw [h.fderiv]
    rfl
  -- the bilinear form `B(X, Y) = ⟨∇_X V, dE Y⟩`
  obtain ⟨B, hBdef⟩ : ∃ B : ℂ × ℝ → ℂ × ℝ → ℝ, ∀ X Y, B X Y =
      hypInner (normalMap Ω (w, u w))
        (fderiv ℝ (fun p' => fderiv ℝ (normalMap Ω) p' (mcNormal Ω u p')) (w, u w) X +
          hypChristoffel (normalMap Ω (w, u w)) (fderiv ℝ (normalMap Ω) (w, u w) X)
            (fderiv ℝ (normalMap Ω) (w, u w) (mcNormal Ω u (w, u w))))
        (fderiv ℝ (normalMap Ω) (w, u w) Y) := ⟨_, fun _ _ => rfl⟩
  have hl : ∀ (a b : ℝ) (X X' Y : ℂ × ℝ), B (a • X + b • X') Y = a * B X Y + b * B X' Y := by
    intro a b X X' Y
    simp only [hBdef, map_add, map_smul, s05_mc_6a_chr_left]
    rw [show ∀ P P' Q Q' : ℂ × ℝ, a • P + b • P' + (a • Q + b • Q') = a • (P + Q) + b • (P' + Q')
      from fun P P' Q Q' => by module, s05_mc_6a_hi_left]
  have hr : ∀ (a b : ℝ) (X Y Y' : ℂ × ℝ), B X (a • Y + b • Y') = a * B X Y + b * B X Y' := by
    intro a b X Y Y'
    simp only [hBdef, map_add, map_smul, s05_mc_6a_hi_right]
  have hB₁ : ∀ Y, IsLinearMap ℝ fun X => B X Y := fun Y =>
    ⟨fun x y => by simpa using hl 1 1 x y Y, fun c x => by simpa using hl c 0 x 0 Y⟩
  have hB₂ : ∀ X, IsLinearMap ℝ (B X) := fun X =>
    ⟨fun x y => by simpa using hr 1 1 X x y, fun c x => by simpa using hr c 0 X x 0⟩
  -- the trace identity, `B(n, n) = 0` and `tr_ḡ B = -2 H_up`
  have hg0 : 0 < graphMetric Ω w (u w) 0 0 := by
    have h0 := s05_mc_3_diag Ω w (u w) 0
    have h1 := s05_mc_3_diag Ω w (u w) 1
    have hd := hdet
    rw [Matrix.det_fin_two] at hd
    rcases h0.lt_or_eq with h | h
    · exact h
    · rw [← h, s05_mc_3_symm] at hd
      nlinarith [sq_nonneg (graphMetric Ω w (u w) 0 1)]
  have ht := s05_mc_trace_alg _ (s05_mc_3_transpose Ω w (u w)) hg0 hdet (gradCoords u w) B hB₁ hB₂
  have hBn := s05_mc_Bnn hJ hU hUΩ hUs hu hp₀
  rw [← hBdef] at hBn
  simp only [mcNormal, graphW] at hBn
  rw [hBn, add_zero] at ht
  have hdiv := s05_mc_div hJ hU hUΩ hUs hu hw huw
  simp only [← hBdef] at hdiv
  -- `I = g + q qᵀ`, `II = -B(t_k, t_l)`
  have hI : (Matrix.of fun i j : Fin 2 => hypInner (normalMap Ω (w, u w))
      (fderiv ℝ (normalMap Ω) (w, u w) (frameVec i, gradCoords u w i))
      (fderiv ℝ (normalMap Ω) (w, u w) (frameVec j, gradCoords u w j))) =
      Matrix.of fun k l : Fin 2 =>
        graphMetric Ω w (u w) k l + gradCoords u w k * gradCoords u w l := by
    ext i j
    simp only [Matrix.of_apply]
    rw [s05_mc_gbar hJ hwΩ (by linarith [hUs w hw])]
    congr 1
    fin_cases i <;> fin_cases j <;>
      simp [cvec, frameVec, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  unfold immMeanCurv
  simp only [hΦ, hν, hI, ← hBdef, s05_mc_6a_hi_neg]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.of_apply, Fin.sum_univ_two] at ht hdiv ⊢
  linear_combination (-1 / 2 : ℝ) * ht + (-1 / 2 : ℝ) * hdiv

/-! ## M7: assembly (A7, COMBINE) -/

/-- M7 helper: `g_τ(e₁, e₁) > 0` for `s < 1/4`, `τ < 1`. -/
theorem s05_mc_7_g00 {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {x : ℂ} (hx : x ∈ Ω)
    (hs : schwarzNorm Ω x < 1 / 4) {τ : ℝ} (hτ : τ < 1) : 0 < graphMetric Ω x τ 0 0 := by
  have hd := s05_mc_2_det_pos hJ hx hs hτ
  rw [Matrix.det_fin_two, s05_mc_3_symm] at hd
  rcases (s05_mc_3_diag Ω x τ 0).lt_or_eq with h | h
  · exact h
  · rw [← h] at hd
    nlinarith [sq_nonneg (graphMetric Ω x τ 0 1)]

/-- M7 helper: `dΦ_x v = dE(v, du_x v)` for the graph surface `Φ = E(·, u ·)`. -/
theorem s05_mc_7_dPhi {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {U : Set ℂ} (hU : IsOpen U)
    (hUΩ : U ⊆ Ω) {u : ℂ → ℝ} (hu : ContDiffOn ℝ ∞ u U) {x : ℂ} (hx : x ∈ U) (v : ℂ) :
    fderiv ℝ (fun y => normalMap Ω (y, u y)) x v =
      fderiv ℝ (normalMap Ω) (x, u x) (v, fderiv ℝ u x v) := by
  have hEd : HasFDerivAt (normalMap Ω) (fderiv ℝ (normalMap Ω) (x, u x)) (x, u x) :=
    ((s05_mc_2_nm_cd hJ (hUΩ hx) (u x)).differentiableAt (by simp)).hasFDerivAt
  have hu' : HasFDerivAt u (fderiv ℝ u x) x :=
    ((hu.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hγ : HasFDerivAt (fun y => (y, u y)) ((ContinuousLinearMap.id ℝ ℂ).prod (fderiv ℝ u x))
      x := (hasFDerivAt_id x).prodMk hu'
  have h' := hEd.comp x hγ
  have h : HasFDerivAt (fun y => normalMap Ω (y, u y))
      ((fderiv ℝ (normalMap Ω) (x, u x)).comp
        ((ContinuousLinearMap.id ℝ ℂ).prod (fderiv ℝ u x))) x := h'
  rw [h.fderiv]
  rfl

/-- M7 helper: the first fundamental form of the graph surface is positive definite. -/
theorem s05_mc_7_fff {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {U : Set ℂ} (hU : IsOpen U)
    (hUΩ : U ⊆ Ω) (hUs : ∀ y ∈ U, schwarzNorm Ω y < 1 / 4) {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) {x : ℂ} (hx : x ∈ U) (hux : u x < 1) :
    0 < hypInner (normalMap Ω (x, u x))
          (fderiv ℝ (fun y => normalMap Ω (y, u y)) x (frameVec 0))
          (fderiv ℝ (fun y => normalMap Ω (y, u y)) x (frameVec 0)) *
        hypInner (normalMap Ω (x, u x))
          (fderiv ℝ (fun y => normalMap Ω (y, u y)) x (frameVec 1))
          (fderiv ℝ (fun y => normalMap Ω (y, u y)) x (frameVec 1)) -
      hypInner (normalMap Ω (x, u x))
          (fderiv ℝ (fun y => normalMap Ω (y, u y)) x (frameVec 0))
          (fderiv ℝ (fun y => normalMap Ω (y, u y)) x (frameVec 1)) ^ 2 := by
  have hxΩ := hUΩ hx
  have hdet := s05_mc_2_det_pos hJ hxΩ (hUs x hx) hux
  have hg0 := s05_mc_7_g00 hJ hxΩ (hUs x hx) hux
  rw [Matrix.det_fin_two, s05_mc_3_symm] at hdet
  simp only [s05_mc_7_dPhi hJ hU hUΩ hu hx, s05_mc_gbar hJ hxΩ (by linarith [hUs x hx])]
  simp only [cvec, frameVec, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.one_re, Complex.one_im, Complex.I_re,
    Complex.I_im, s05_mc_3_symm]
  generalize graphMetric Ω x (u x) 0 0 = a at hdet hg0 ⊢
  generalize graphMetric Ω x (u x) 0 1 = c at hdet ⊢
  generalize graphMetric Ω x (u x) 1 1 = d at hdet ⊢
  generalize fderiv ℝ u x 1 = y₀
  generalize fderiv ℝ u x I = y₁
  have hnum : 0 ≤ d * y₀ ^ 2 - 2 * c * y₀ * y₁ + a * y₁ ^ 2 := by
    have : 0 ≤ a * (d * y₀ ^ 2 - 2 * c * y₀ * y₁ + a * y₁ ^ 2) := by
      nlinarith [sq_nonneg (a * y₁ - c * y₀), sq_nonneg y₀]
    exact (mul_nonneg_iff_of_pos_left hg0).mp this
  nlinarith [hnum, hdet]

/-- M7 helper: `ν` is differentiable on `Ω` (`ν(z) = dE_{(z,0)}(0, 1)`). -/
theorem s05_mc_7_nv_diff {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {z : ℂ} (hz : z ∈ Ω) :
    DifferentiableAt ℝ (normalVec Ω) z := by
  have hev : normalVec Ω =ᶠ[𝓝 z] fun y => fderiv ℝ (normalMap Ω) (y, 0) ((0 : ℂ), (1 : ℝ)) := by
    filter_upwards [(s05_mc_6a_isOpen hJ).mem_nhds hz] with y hy
    rw [s05_mc_dE hJ hy]
    simp [normalVec]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have hD := ((s05_mc_2_nm_cd hJ hz 0).fderiv_right (m := 1) (by simp)).differentiableAt
    (by simp)
  have hc : DifferentiableAt ℝ (fun y : ℂ => (y, (0 : ℝ))) z :=
    differentiableAt_id.prodMk (differentiableAt_const _)
  exact (hD.comp z hc).clm_apply (differentiableAt_const _)

/-- M7: uniform form (for COMBINE with (b), (c)): `𝒬(t) = 2σ` on `G₀` for all `η ≤ η₀`,
`R ≥ R₁`. -/
theorem s05_mc_main : ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ R₁ : ℝ, ∀ η R : ℝ, 0 < η → η ≤ η₀ → R₁ ≤ R →
      ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
        ∀ w ∈ goodSet Ω Ωs η R, graphQ Ω (slabTop Ω Ωs) w = 2 * sigmaSrc Ω Ωs w := by
  intro K hK ε hε hε'
  obtain ⟨η₀, hη₀, R₁, h⟩ := s04_sl_tube_unif K 1 1 6 ε 0 hK one_pos one_pos le_rfl hε hε' le_rfl
  refine ⟨min η₀ (1 / 4), lt_min hη₀ (by norm_num), max R₁ 0,
    fun η R hη hηle hR Ω Ωs hp hnl w hw => ?_⟩
  have hJ := s03_b0_jordanPair hp
  have hJs := s02_jordanPair_symm hJ
  have hΩ := s02_jordanPair_riemannMap hJ
  have hΩs := s02_jordanPair_riemannMap hJs
  have hR0 : 0 ≤ R := (le_max_right _ _).trans hR
  obtain ⟨-, ⟨⟨-, hinj, -, -⟩, -⟩, t, N, htS, hNE, hNmap, -, ht, hset, hiv, hv, -, -⟩ :=
    h η R hη (hηle.trans (min_le_left _ _)) ((le_max_left _ _).trans hR) Ω Ωs hp hnl w hw
  have hwΩ : w ∈ Ω := hw.1
  have hsid := s04_sl_slab_id hp (by linarith) hinj hNmap ht hset fun v hv => (hiv v hv).1
  have hball : ∀ᶠ x in 𝓝 w, x ∈ rhoClosedBall Ω w 1 :=
    (s05_poincareDist_eventually_lt hΩ hwΩ one_pos).mono fun x hx => ⟨hx.1, hx.2.le⟩
  have hw1 : w ∈ rhoClosedBall Ω w 1 := hball.self_of_nhds
  -- the open set `U = G₀ ∩ V_t`, where `t` is smooth and `s < 1/4`
  obtain ⟨Vt, hVt, hVtS, htC⟩ := htS
  obtain ⟨⟨VN, hVN, hVNS, hNC⟩, -, hNinj, -⟩ := hNE
  have hU : IsOpen (goodSet Ω Ωs η R ∩ Vt) := (s04_sl_good_open hp η R).inter hVt
  have hUΩ : goodSet Ω Ωs η R ∩ Vt ⊆ Ω := fun x hx => hx.1.1
  have hUs : ∀ y ∈ goodSet Ω Ωs η R ∩ Vt, schwarzNorm Ω y < 1 / 4 := fun y hy =>
    (s05_go_s_lt hJ hR0 hy.1).trans_le (hηle.trans (min_le_right _ _))
  have hu : ContDiffOn ℝ ∞ t (goodSet Ω Ωs η R ∩ Vt) := htC.mono inter_subset_right
  have hwU : w ∈ goodSet Ω Ωs η R ∩ Vt := ⟨hw, hVtS hw1⟩
  have hNd : ∀ x ∈ rhoClosedBall Ω w 1, DifferentiableAt ℝ N x := fun x hx =>
    (hNC.contDiffAt (hVN.mem_nhds (hVNS hx))).differentiableAt (by simp)
  have hΦev : ∀ x ∈ rhoClosedBall Ω w 1, normalMap Ω (x, t x) = epstein Ωs (N x) := fun x hx =>
    (ht x hx).2.2.symm
  have hss : ∀ x ∈ rhoClosedBall Ω w 1, schwarzNorm Ωs (N x) < 1 / 4 := fun x hx =>
    ((hv x hx).2 (N x) ⟨hNmap hx, by rw [s04_tb_dist_self hΩs (hNmap hx)]; norm_num⟩).trans hε'
  -- the normal of the graph is `-ν* ∘ N` (M6a `normal_pm` + M6b orientation)
  have hν : ∀ x ∈ goodSet Ω Ωs η R ∩ Vt, x ∈ rhoClosedBall Ω w 1 →
      (∀ᶠ y in 𝓝 x, y ∈ rhoClosedBall Ω w 1) →
      fderiv ℝ (normalMap Ω) (x, t x) (mcNormal Ω t (x, t x)) = -normalVec Ωs (N x) := by
    intro x hxU hxB hxnb
    have hxΩ := hUΩ hxU
    have hNx := hNmap hxB
    obtain ⟨htx0, htxε, hX⟩ := ht x hxB
    have htx1 : t x < 1 := by linarith
    have hq : 0 < (normalMap Ω (x, t x)).2 := (lem_normal_b hΩ hxΩ).1 (t x)
    have hXq : epstein Ωs (N x) = normalMap Ω (x, t x) := hX
    obtain ⟨hn₂, hn₂o⟩ := s05_mc_nu_normal hJs hNx (by linarith [hss x hxB])
    rw [hXq] at hn₂ hn₂o
    have hdΦ : ∀ v, fderiv ℝ (fun y => normalMap Ω (y, t y)) x v =
        fderiv ℝ (epstein Ωs) (N x) (fderiv ℝ N x v) := fun v => by
      have hev : (fun y => normalMap Ω (y, t y)) =ᶠ[𝓝 x] epstein Ωs ∘ N :=
        hxnb.mono fun y hy => hΦev y hy
      rw [hev.fderiv_eq, fderiv_comp x (s02_epstein_differentiableAt hΩs hNx) (hNd x hxB)]
      rfl
    have hn₁o : ∀ v, hypInner (normalMap Ω (x, t x))
        (fderiv ℝ (normalMap Ω) (x, t x) (mcNormal Ω t (x, t x)))
        (fderiv ℝ (fun y => normalMap Ω (y, t y)) x v) = 0 := fun v => by
      rw [s05_mc_7_dPhi hJ hU hUΩ hu hxU]
      exact s05_mc_normal hJ hUΩ hUs t hxU htx1 v
    have hn₂o' : ∀ v, hypInner (normalMap Ω (x, t x)) (normalVec Ωs (N x))
        (fderiv ℝ (fun y => normalMap Ω (y, t y)) x v) = 0 := fun v => by
      rw [hdΦ]
      exact hn₂o _
    have hab := s05_mc_7_fff hJ hU hUΩ hUs hu hxU htx1
    rcases s05_mc_normal_pm hq hab.ne' (s05_mc_unit hJ hUΩ hUs t ⟨hxU, htx1⟩) hn₂
        (hn₁o _) (hn₁o _) (hn₂o' _) (hn₂o' _) with h | h
    · -- `⟨ν_Φ, ∂_τ E⟩ = 1/W > 0` but `⟨ν*, ∂_τ E⟩ ≤ 0`
      exfalso
      have ho := s05_mc_orient hJ hxΩ hNx htx0 hX (hiv x hxB).1
      have hτ : deriv (fun τ => normalGeod Ω x τ) (t x) =
          fderiv ℝ (normalMap Ω) (x, t x) ((0 : ℂ), (1 : ℝ)) := by
        rw [s05_mc_dE hJ hxΩ]
        simp
      rw [hτ, hXq, ← h, s05_mc_gbar hJ hxΩ (by linarith [hUs x hxU])] at ho
      have hW : 0 < graphW Ω t x (t x) := (s05_mc_3_W hJ hxΩ (hUs x hxU) htx1 t).2.2
      have hc0 : cvec (0 : ℂ) = 0 := by
        funext i
        fin_cases i <;> simp [cvec]
      simp only [hc0, Matrix.mulVec_zero, dotProduct_zero, zero_add, mul_one, mcNormal] at ho
      have : 0 < 1 / graphW Ω t x (t x) := by positivity
      linarith
    · exact h
  have hνev : (fun x => fderiv ℝ (normalMap Ω) (x, t x) (mcNormal Ω t (x, t x))) =ᶠ[𝓝 w]
      fun x => -normalVec Ωs (N x) := by
    filter_upwards [hU.mem_nhds hwU, hball, eventually_eventually_nhds.mpr hball]
      with x hxU hxB hxnb
    exact hν x hxU hxB hxnb
  -- `H_up(t)(w) = immMeanCurv Φ ν_Φ = -H*(N w)`
  have hNw := hNmap hw1
  have hsurf := s05_mc_surface hJ hU hUΩ hUs hu hwU (by linarith [(ht w hw1).2.1])
  have hI : (Matrix.of fun i j : Fin 2 =>
      hypInner ((fun x => normalMap Ω (x, t x)) w)
        (fderiv ℝ (fun x => normalMap Ω (x, t x)) w (frameVec i))
        (fderiv ℝ (fun x => normalMap Ω (x, t x)) w (frameVec j))).det ≠ 0 := by
    have hf := s05_mc_7_fff hJ hU hUΩ hUs hu hwU (by linarith [(ht w hw1).2.1])
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply]
    rw [s05_mc_2_hi_symm _ (fderiv ℝ (fun x => normalMap Ω (x, t x)) w (frameVec 1))
      (fderiv ℝ (fun x => normalMap Ω (x, t x)) w (frameVec 0))]
    apply ne_of_gt
    nlinarith [hf]
  have hrep := s05_mc_reparam (Ψ := epstein Ωs) (μ := normalVec Ωs)
    (hball.mono fun x hx => hΦev x hx) hνev (hNd w hw1)
    (s02_epstein_differentiableAt hΩs hNw) (s05_mc_7_nv_diff hJs hNw) (hNinj w hw1) hI
  rw [← s05_mc_meanCurv_eq,
    (lem_shape_b Ωs Ω hJs (N w) hNw (by linarith [hss w hw1])).2.1, hsurf] at hrep
  rw [graphQ, sigmaSrc, s05_mc_congr Ω (hball.mono fun x hx => (hsid x hx).1), (hsid w hw1).2,
    hrep]
  ring

/-- **Lemma 5.7 (a)** (`lem:graph-operator`, sec05-upper.tex:393).  `𝒬(t) = 2σ` on `G₀`. -/
theorem lem_graph_operator_a : ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ η : ℝ, 0 < η ∧ η < ε ∧ ∃ R : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
      ¬ IsLinePair Ω Ωs → ∀ w ∈ goodSet Ω Ωs η R,
        graphQ Ω (slabTop Ω Ωs) w = 2 * sigmaSrc Ω Ωs w := by
  intro K hK ε hε hε'
  obtain ⟨η₀, hη₀, R₁, h⟩ := s05_mc_main K hK ε hε hε'
  refine ⟨min η₀ (ε / 2), lt_min hη₀ (by linarith), (min_le_right _ _).trans_lt (by linarith),
    max R₁ 0, fun Ω Ωs hp hnl w hw => ?_⟩
  exact h _ _ (lt_min hη₀ (by linarith)) (min_le_left _ _) (le_max_left _ _) Ω Ωs hp hnl w hw

/-- (b) helper (GB1): a `θ`-integral over `[0, 1]` of a function jointly smooth on
`(-1/2, 3/2) × G` is smooth on `G` (TauCeti `contDiffOn_integral_smul_of_contDiffOn`). -/
theorem s05_gb_smooth {G : Set ℂ} (hG : IsOpen G) {F : ℝ × ℂ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ G)) :
    ContDiffOn ℝ ∞ (fun w => ∫ θ in (0 : ℝ)..1, F (θ, w)) G := by
  have hW : IsOpen (G ×ˢ Ioo (-1 / 2 : ℝ) (3 / 2)) := hG.prod isOpen_Ioo
  have hF' : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => F (p.2, p.1)) (G ×ˢ Ioo (-1 / 2 : ℝ) (3 / 2)) :=
    hF.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn fun p hp => ⟨hp.2, hp.1⟩
  have hι : Continuous fun y : unitInterval => (y : ℝ) := continuous_subtype_val
  have h := TauCeti.contDiffOn_integral_smul_of_contDiffOn (μ := (volume : Measure unitInterval))
    (g := fun _ => (1 : ℝ)) (integrable_const _) hι hW hF' hG fun x hx y =>
      ⟨hx, by linarith [y.2.1], by linarith [y.2.2]⟩
  refine h.congr fun x _ => ?_
  simp only [one_smul]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  exact (integral_subtype measurableSet_Icc (fun θ => F (θ, x))).symm

/-- (b) helper (GB2): `∫₀¹ ellOp(a_θ, b_θ, c_θ) u w dθ = ellOp(∫a, ∫b, ∫c) u w` (`ellOp` at `w` is
linear in the values of the coefficients at `w`). -/
theorem s05_gb_ellOp_integral (Ω : Set ℂ) {a : ℝ × ℂ → Matrix (Fin 2) (Fin 2) ℝ}
    {b : ℝ × ℂ → Fin 2 → ℝ} {c : ℝ × ℂ → ℝ} (u : ℂ → ℝ) {w : ℂ}
    (ha : ∀ i j, IntervalIntegrable (fun θ => a (θ, w) i j) volume 0 1)
    (hb : ∀ i, IntervalIntegrable (fun θ => b (θ, w) i) volume 0 1)
    (hc : IntervalIntegrable (fun θ => c (θ, w)) volume 0 1) :
    ∫ θ in (0 : ℝ)..1, ellOp Ω (fun x => a (θ, x)) (fun x => b (θ, x)) (fun x => c (θ, x)) u w =
      ellOp Ω (fun x => Matrix.of fun i j => ∫ θ in (0 : ℝ)..1, a (θ, x) i j)
        (fun x i => ∫ θ in (0 : ℝ)..1, b (θ, x) i) (fun x => ∫ θ in (0 : ℝ)..1, c (θ, x)) u w := by
  have hA : ∀ i j, IntervalIntegrable
      (fun θ => a (θ, w) i j * rhoHess Ω u w ![frameVec i, frameVec j]) volume 0 1 :=
    fun i j => (ha i j).mul_const _
  have hB : ∀ i, IntervalIntegrable (fun θ => b (θ, w) i * fderiv ℝ u w (frameVec i)) volume 0 1 :=
    fun i => (hb i).mul_const _
  have hC : IntervalIntegrable (fun θ => c (θ, w) * u w) volume 0 1 := hc.mul_const _
  simp only [ellOp, Fin.sum_univ_two, Matrix.of_apply]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_sub, intervalIntegral.integral_add,
    intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add]
  · simp only [intervalIntegral.integral_mul_const]
  all_goals repeat' first | exact hC | exact hA _ _ | exact hB _ | apply IntervalIntegrable.add |
    apply IntervalIntegrable.neg

/-- (b) helper (GB3): `𝒬(0) = 0`.  The zero graph is `Σ`: `W = 1`, the flux vanishes, and
`√det g_τ = λ²(cosh²τ - s² e^{2τ})` (`s05_ml_metric`), so
`H_up(0) = -½ ∂_τ log √det g_τ |₀ = s²/(1 - s²)`. -/
theorem s05_gb_Q0 {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {w : ℂ} (hw : w ∈ Ω)
    (hs : schwarzNorm Ω w < 1) : graphQ Ω 0 w = 0 := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hw
  have hs0 := (eq_nehari ⟨f, hf⟩ hw).1
  have hmet : ∀ τ : ℝ, graphMetric Ω w τ =
      !![(Real.cosh τ ^ 2 + schwarzNorm Ω w ^ 2 * Real.exp τ ^ 2) * poincareDensity Ω w ^ 2 +
            2 * Real.cosh τ * Real.exp τ * (schwarzian (Function.invFunOn f unitDisc) w).re,
          -(2 * Real.cosh τ * Real.exp τ * (schwarzian (Function.invFunOn f unitDisc) w).im);
        -(2 * Real.cosh τ * Real.exp τ * (schwarzian (Function.invFunOn f unitDisc) w).im),
          (Real.cosh τ ^ 2 + schwarzNorm Ω w ^ 2 * Real.exp τ ^ 2) * poincareDensity Ω w ^ 2 -
            2 * Real.cosh τ * Real.exp τ * (schwarzian (Function.invFunOn f unitDisc) w).re] := by
    intro τ
    rw [s05_ml_metric hJ hf hw hs.ne τ, ← eq_def_s hf hw]
  have hnorm : (schwarzian (Function.invFunOn f unitDisc) w).re ^ 2 +
      (schwarzian (Function.invFunOn f unitDisc) w).im ^ 2 =
        (schwarzNorm Ω w * poincareDensity Ω w ^ 2) ^ 2 := by
    have h1 : ‖schwarzian (Function.invFunOn f unitDisc) w‖ =
        schwarzNorm Ω w * poincareDensity Ω w ^ 2 := by
      rw [eq_def_s hf hw]
      field_simp
    rw [← h1, Complex.sq_norm, Complex.normSq_apply]
    ring
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ, ∀ τ, h τ = poincareDensity Ω w ^ 2 *
      (Real.cosh τ * Real.cosh τ - schwarzNorm Ω w ^ 2 * (Real.exp τ * Real.exp τ)) :=
    ⟨_, fun _ => rfl⟩
  have hfun : h = fun τ => poincareDensity Ω w ^ 2 *
      (Real.cosh τ * Real.cosh τ - schwarzNorm Ω w ^ 2 * (Real.exp τ * Real.exp τ)) := funext hh
  have hdet : ∀ τ, (graphMetric Ω w τ).det = h τ ^ 2 := by
    intro τ
    rw [hmet τ, Matrix.det_fin_two_of, hh]
    linear_combination (-(2 * Real.cosh τ * Real.exp τ) ^ 2) * hnorm
  have hs2 : schwarzNorm Ω w ^ 2 < 1 := by nlinarith
  have hh0 : 0 < h 0 := by
    rw [hh]
    simp only [Real.cosh_zero, Real.exp_zero, mul_one]
    have := pow_pos hl 2
    nlinarith
  have hhc : Continuous h := by
    rw [hfun]
    fun_prop
  have hW : ∀ τ, graphW Ω (0 : ℂ → ℝ) w τ = 1 := by
    intro τ
    simp [graphW, gradCoords]
  have hF : ∀ τ x i, graphFlux Ω (0 : ℂ → ℝ) τ x i = 0 := by
    intro τ x i
    have h0 : gradCoords (0 : ℂ → ℝ) x = 0 := by
      funext j
      simp [gradCoords]
    simp [graphFlux, h0]
  have hev : (fun τ => graphSdet Ω w τ / graphW Ω (0 : ℂ → ℝ) w τ) =ᶠ[𝓝 0] h := by
    filter_upwards [hhc.continuousAt.eventually (lt_mem_nhds hh0)] with τ hτ
    rw [hW, div_one, graphSdet, hdet, Real.sqrt_sq hτ.le]
  have hhd := (((Real.hasDerivAt_cosh 0).mul (Real.hasDerivAt_cosh 0)).sub
    (((Real.hasDerivAt_exp 0).mul (Real.hasDerivAt_exp 0)).const_mul
      (schwarzNorm Ω w ^ 2))).const_mul (poincareDensity Ω w ^ 2)
  have hd : deriv (fun τ => graphSdet Ω w τ / graphW Ω (0 : ℂ → ℝ) w τ) 0 =
      -2 * schwarzNorm Ω w ^ 2 * poincareDensity Ω w ^ 2 := by
    rw [hev.deriv_eq, hfun]
    refine hhd.deriv.trans ?_
    simp only [Real.cosh_zero, Real.sinh_zero, Real.exp_zero]
    ring
  have hS0 : graphSdet Ω w 0 = poincareDensity Ω w ^ 2 * (1 - schwarzNorm Ω w ^ 2) := by
    rw [graphSdet, hdet, Real.sqrt_sq hh0.le, hh]
    simp
  have hflux : ∀ i : Fin 2, fderiv ℝ (fun x => graphFlux Ω (0 : ℂ → ℝ) 0 x i) w (frameVec i) = 0 := by
    intro i
    simp [hF]
  have hmc : meanCurvUp Ω 0 w = schwarzNorm Ω w ^ 2 / (1 - schwarzNorm Ω w ^ 2) := by
    simp only [meanCurvUp, Pi.zero_apply, hflux, Finset.sum_const_zero, hd, hS0]
    have h1 : (1 - schwarzNorm Ω w ^ 2) ≠ 0 := by linarith
    have h2 : poincareDensity Ω w ≠ 0 := hl.ne'
    field_simp
    ring
  rw [graphQ, hmc]
  ring

/-- (b) helper (GB4): along `θ ↦ θ t`, `d/dθ 𝒬(θ t)(w) = D𝒬(θ t)[t](w)` for `θ ∈ (-1/2, 3/2)`
(B1 jet formula `s05_ml_jet` + `s05_ml_lin`; the jet of `θ t` stays in `O` since `|θ t| < 3/8`,
`s < 1/4`). -/
theorem s05_gb_path {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {G : Set ℂ} (hG : IsOpen G)
    (hGΩ : G ⊆ Ω) (hs : ∀ x ∈ G, schwarzNorm Ω x < 1 / 4) {t : ℂ → ℝ}
    (ht : ContDiffOn ℝ ∞ t G) (ht0 : ∀ x ∈ G, 0 < t x ∧ t x < 1 / 4) {w : ℂ} (hw : w ∈ G)
    {θ : ℝ} (hθ : θ ∈ Ioo (-1 / 2 : ℝ) (3 / 2)) :
    HasDerivAt (fun s : ℝ => graphQ Ω (s • t) w) (graphQDeriv Ω (θ • t) t w) θ := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  obtain ⟨Ψ, hΨ, hjet⟩ := s05_ml_jet
  have hOo := s05_ml_open
  have hwΩ := hGΩ hw
  have htd : ∀ x ∈ G, DifferentiableAt ℝ t x := fun x hx =>
    ((ht.differentiableOn (by simp)) x hx).differentiableAt (hG.mem_nhds hx)
  have hdt : DifferentiableAt ℝ (fderiv ℝ t) w :=
    ((ht.contDiffAt (hG.mem_nhds hw)).fderiv_right (m := ∞)
      (le_of_eq ENat.coe_top_add_one)).differentiableAt (by simp)
  set A : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) :=
    ((0 : ℝ), poincareDensity Ω w, schwarzian (Function.invFunOn f unitDisc) w,
      fun i => fderiv ℝ (poincareDensity Ω) w (frameVec i),
      fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) w (frameVec i),
      (0 : Fin 2 → ℝ), (0 : Fin 2 → Fin 2 → ℝ)) with hA
  set d : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) :=
    (t w, (0 : ℝ), (0 : ℂ), (0 : Fin 2 → ℝ), (0 : Fin 2 → ℂ), fun i => fderiv ℝ t w (frameVec i),
      fun i j => fderiv ℝ (fderiv ℝ t) w (frameVec i) (frameVec j)) with hd
  -- the jet of `σ t` is the line `A + σ d`
  have hjeq : ∀ σ : ℝ, ((((σ • t) w, poincareDensity Ω w,
      schwarzian (Function.invFunOn f unitDisc) w,
      fun i => fderiv ℝ (poincareDensity Ω) w (frameVec i),
      fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) w (frameVec i),
      fun i => fderiv ℝ (σ • t) w (frameVec i),
      fun i j => fderiv ℝ (fderiv ℝ (σ • t)) w (frameVec i) (frameVec j))) :
        ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ)) =
      A + σ • d := by
    intro σ
    have h6 : fderiv ℝ (σ • t) w = σ • fderiv ℝ t w :=
      ((htd w hw).hasFDerivAt.const_smul σ).fderiv
    have h7 : fderiv ℝ (fderiv ℝ (σ • t)) w = σ • fderiv ℝ (fderiv ℝ t) w := by
      refine ((hdt.hasFDerivAt.const_smul σ).congr_of_eventuallyEq ?_).fderiv
      filter_upwards [hG.mem_nhds hw] with x hx
      exact ((htd x hx).hasFDerivAt.const_smul σ).fderiv
    rw [hA, hd, h6, h7]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_
      (Prod.ext ?_ ?_)))))
    all_goals first
      | (simp; done)
      | (funext i; simp; done)
      | (funext i j; simp)
  -- the line stays in `O` for `σ ∈ (-1/2, 3/2)`: `|σ t| < 3/8`, `s < 1/4`
  have hmem : ∀ σ ∈ Ioo (-1 / 2 : ℝ) (3 / 2), A + σ • d ∈
      {J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) |
        0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1} := by
    intro σ hσ
    have hl := s02_poincareDensity_pos ⟨f, hf⟩ hwΩ
    obtain ⟨ht0w, ht1w⟩ := ht0 w hw
    have hs0 := (eq_nehari ⟨f, hf⟩ hwΩ).1
    have hsw := hs w hw
    have hnorm : ‖schwarzian (Function.invFunOn f unitDisc) w‖ =
        schwarzNorm Ω w * poincareDensity Ω w ^ 2 := by
      rw [eq_def_s hf hwΩ]
      field_simp
    have hθt : σ * t w < 1 := by nlinarith [mul_lt_mul_of_pos_right hσ.2 ht0w]
    have he : Real.exp (σ * t w) < 3 := by
      have h1 := Real.exp_lt_exp.2 hθt
      have h2 := Real.exp_one_lt_d9
      norm_num at h2
      linarith
    have hc := Real.one_le_cosh (σ * t w)
    have hse : schwarzNorm Ω w * Real.exp (σ * t w) < 1 := by
      nlinarith [mul_le_mul_of_nonneg_left he.le hs0]
    have hl2 : 0 < poincareDensity Ω w ^ 2 := by positivity
    have e1 : (A + σ • d).1 = σ * t w := by simp [hA, hd]
    have e2 : (A + σ • d).2.1 = poincareDensity Ω w := by simp [hA, hd]
    have e3 : (A + σ • d).2.2.1 = schwarzian (Function.invFunOn f unitDisc) w := by simp [hA, hd]
    refine ⟨by rw [e2]; exact hl, ?_⟩
    show ‖(A + σ • d).2.2.1‖ * Real.exp (A + σ • d).1 <
      (A + σ • d).2.1 ^ 2 * Real.cosh (A + σ • d).1
    rw [e1, e2, e3, hnorm]
    nlinarith [mul_lt_mul_of_pos_left hse hl2, mul_le_mul_of_nonneg_left hc hl2.le]
  -- `𝒬(σ t)(w) = 2(H - Ψ(A + σ d))` near `θ`
  set g : ℝ → ℝ := fun σ => graphQ Ω (σ • t) w with hg
  have hev : g =ᶠ[𝓝 θ] fun σ =>
      2 * (schwarzNorm Ω w ^ 2 / (1 - schwarzNorm Ω w ^ 2) - Ψ (A + σ • d)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with σ hσ
    have hu : ContDiffOn ℝ 2 (σ • t) G := (ht.const_smul σ).of_le (by simp)
    have h := hjet Ω Ωs hJ f hf G hG hGΩ (fun x hx => (hs x hx).trans (by norm_num)) (σ • t) hu
      w hw (by rw [hjeq σ]; exact hmem σ hσ)
    simp only [hg, graphQ]
    rw [h, hjeq σ]
  have hline : HasDerivAt (fun σ : ℝ => A + σ • d) d θ := by
    simpa using ((hasDerivAt_id' θ).smul_const d).const_add A
  have hΨd : DifferentiableAt ℝ Ψ (A + θ • d) :=
    (hΨ.contDiffAt (hOo.mem_nhds (hmem θ hθ))).differentiableAt (by simp)
  have hk := ((hΨd.hasFDerivAt.comp_hasDerivAt θ hline).const_sub
    (schwarzNorm Ω w ^ 2 / (1 - schwarzNorm Ω w ^ 2))).const_mul 2
  have hgd : DifferentiableAt ℝ g θ := hk.differentiableAt.congr_of_eventuallyEq hev
  have hderiv : graphQDeriv Ω (θ • t) t w = deriv g θ := by
    have e : (fun s : ℝ => graphQ Ω (θ • t + s • t) w) = fun s => g (s + θ) := by
      funext s
      simp only [hg]
      rw [add_smul, add_comm]
    rw [graphQDeriv, e, deriv_comp_add_const, zero_add]
  rw [hderiv]
  exact hgd.hasDerivAt

/-- GO-b (w1): Lemma 5.7 (b) uniformly, with `D`-independent coefficients representing `𝓛` on
every open `D ⊆ G₀` for `C²` functions. -/
theorem s05_gb_unif : ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < ε ∧ ∃ R₁ : ℝ, ∀ η R : ℝ, 0 < η → η ≤ η₀ → R₁ ≤ R →
      ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
        ∃ (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
          IsSmoothOp (goodSet Ω Ωs η R) aUp bUp c ∧
          (∀ D : Set ℂ, IsOpen D → D ⊆ goodSet Ω Ωs η R → ∀ u : ℂ → ℝ, ContDiffOn ℝ 2 u D →
            ∀ w ∈ D, graphOp Ω Ωs u w = ellOp Ω aUp bUp c u w) ∧
          ∀ w ∈ goodSet Ω Ωs η R, graphOp Ω Ωs (slabTop Ω Ωs) w = 2 * sigmaSrc Ω Ωs w := by
  intro K hK ε hε hε4
  obtain ⟨ηf, hηf, Rf, hfam⟩ := s05_ml_family K hK ε hε hε4
  obtain ⟨ηa, hηa, hηaε, Ra, hA⟩ := lem_graph_operator_a K hK ε hε hε4
  obtain ⟨ηN, hηN, RN, hN⟩ := s04_sl_eq_def_N_unif K hK ε hε hε4
  refine ⟨min (min ηf ηa) ηN, lt_min (lt_min hηf hηa) hηN,
    (min_le_left _ _).trans_lt ((min_le_right _ _).trans_lt hηaε), max (max Rf Ra) (max RN 0), ?_⟩
  intro η R hη hηle hR Ω Ωs hp hnl
  have hηf' : η ≤ ηf := hηle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hηa' : η ≤ ηa := hηle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hηN' : η ≤ ηN := hηle.trans (min_le_right _ _)
  have hRf : Rf ≤ R := (le_max_left _ _).trans ((le_max_left _ _).trans hR)
  have hRa : Ra ≤ R := (le_max_right _ _).trans ((le_max_left _ _).trans hR)
  have hRN : RN ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hR0 : 0 ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hR)
  obtain ⟨a, b, c, ha, hb, hc, hsym, hrep⟩ := hfam η R hη hηf' hRf Ω Ωs hp hnl
  obtain ⟨hGo, htC, -, hslab⟩ := hN η R hη hηN' hRN Ω Ωs hp hnl
  have hJ := s03_b0_jordanPair hp
  have hGΩ : goodSet Ω Ωs η R ⊆ Ω := fun x hx => hx.1
  have hsG : ∀ x ∈ goodSet Ω Ωs η R, schwarzNorm Ω x < 1 / 4 := fun x hx =>
    (s05_go_s_lt hJ hR0 hx).trans (by linarith)
  have hIoo : ∀ θ ∈ uIcc (0 : ℝ) 1, θ ∈ Ioo (-1 / 2 : ℝ) (3 / 2) := by
    intro θ hθ
    rw [uIcc_of_le zero_le_one] at hθ
    exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hcF : ∀ F : ℝ × ℂ → ℝ, ContDiffOn ℝ ∞ F (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ goodSet Ω Ωs η R) →
      ∀ w ∈ goodSet Ω Ωs η R, ContinuousOn (fun θ => F (θ, w)) (uIcc (0 : ℝ) 1) :=
    fun F hF w hw => hF.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      fun θ hθ => ⟨hIoo θ hθ, hw⟩
  have hII : ∀ F : ℝ × ℂ → ℝ, ContDiffOn ℝ ∞ F (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ goodSet Ω Ωs η R) →
      ∀ w ∈ goodSet Ω Ωs η R, IntervalIntegrable (fun θ => F (θ, w)) volume 0 1 :=
    fun F hF w hw => (hcF F hF w hw).intervalIntegrable
  refine ⟨fun w => Matrix.of fun i j => ∫ θ in (0 : ℝ)..1, a (θ, w) i j,
    fun w i => ∫ θ in (0 : ℝ)..1, b (θ, w) i, fun w => ∫ θ in (0 : ℝ)..1, c (θ, w),
    ⟨fun i j => by simpa only [Matrix.of_apply] using s05_gb_smooth hGo (ha i j),
      fun i => s05_gb_smooth hGo (hb i), s05_gb_smooth hGo hc, fun w _ => ?_⟩, ?_, ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have h := congrFun (congrFun (hsym (θ, w)) i) j
    simpa [Matrix.transpose_apply] using h
  · intro D hDo hDG u hu w hwD
    have hw := hDG hwD
    rw [graphOp]
    refine (intervalIntegral.integral_congr fun θ hθ => ?_).trans
      (s05_gb_ellOp_integral Ω u (fun i j => hII _ (ha i j) w hw) (fun i => hII _ (hb i) w hw)
        (hII _ hc w hw))
    exact hrep θ (hIoo θ hθ) D hDo hDG u hu w hwD
  · intro w hw
    have hwa : w ∈ goodSet Ω Ωs ηa Ra := s04_sl_good_mono hp hw hηa' hRa
    have ht2 : ContDiffOn ℝ 2 (slabTop Ω Ωs) (goodSet Ω Ωs η R) := htC.of_le (by simp)
    have hI : ∫ θ in (0 : ℝ)..1, graphQDeriv Ω (θ • slabTop Ω Ωs) (slabTop Ω Ωs) w =
        ∫ θ in (0 : ℝ)..1, ellOp Ω (fun x => a (θ, x)) (fun x => b (θ, x)) (fun x => c (θ, x))
          (slabTop Ω Ωs) w :=
      intervalIntegral.integral_congr fun θ hθ =>
        hrep θ (hIoo θ hθ) _ hGo subset_rfl _ ht2 w hw
    have hint : IntervalIntegrable (fun θ => ellOp Ω (fun x => a (θ, x)) (fun x => b (θ, x))
        (fun x => c (θ, x)) (slabTop Ω Ωs) w) volume 0 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      simp only [ellOp, Fin.sum_univ_two]
      exact (((hcF _ hc w hw).mul continuousOn_const).sub
        ((((hcF _ (ha 0 0) w hw).mul continuousOn_const).add
          ((hcF _ (ha 0 1) w hw).mul continuousOn_const)).add
          (((hcF _ (ha 1 0) w hw).mul continuousOn_const).add
            ((hcF _ (ha 1 1) w hw).mul continuousOn_const)))).sub
        (((hcF _ (hb 0) w hw).mul continuousOn_const).add
          ((hcF _ (hb 1) w hw).mul continuousOn_const))
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => graphQ Ω (s • slabTop Ω Ωs) w) (fun θ hθ => by
        have h := s05_gb_path hJ hGo hGΩ hsG htC
          (fun x hx => ⟨(hslab x hx).2.1, (hslab x hx).2.2.1.trans hε4⟩) hw (hIoo θ hθ)
        rwa [hrep θ (hIoo θ hθ) _ hGo subset_rfl _ ht2 w hw] at h) hint
    rw [graphOp, hI, hftc]
    simp only [one_smul, zero_smul]
    rw [hA Ω Ωs hp hnl w hwa, s05_gb_Q0 hJ (hGΩ hw) ((hsG w hw).trans (by norm_num)), sub_zero]

/-- **Lemma 5.7 (b)** (`lem:graph-operator`, sec05-upper.tex:394).  `𝓛u = ∫₀¹ D𝒬(θt)[u] dθ` is a
linear second-order operator of the form (5.2) with smooth coefficients on `G₀`, and `𝓛t = 2σ` on
`G₀` (5.15) (`eq:exact`). -/
theorem lem_graph_operator_b : ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ η : ℝ, 0 < η ∧ η < ε ∧ ∃ R : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
      ¬ IsLinePair Ω Ωs →
        (∃ (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
          RepresentsOp Ω (goodSet Ω Ωs η R) (graphOp Ω Ωs) aUp bUp c) ∧
        ∀ w ∈ goodSet Ω Ωs η R, graphOp Ω Ωs (slabTop Ω Ωs) w = 2 * sigmaSrc Ω Ωs w := by
  intro K hK ε hε hε4
  obtain ⟨η₀, hη₀, hη₀ε, R₁, hU⟩ := s05_gb_unif K hK ε hε hε4
  obtain ⟨η₂, hη₂, R₂, hN⟩ := s04_sl_eq_def_N_unif K hK ε hε hε4
  refine ⟨min η₀ η₂, lt_min hη₀ hη₂, (min_le_left _ _).trans_lt hη₀ε, max R₁ R₂, ?_⟩
  intro Ω Ωs hp hnl
  obtain ⟨aUp, bUp, c, hsm, hrep, hex⟩ := hU (min η₀ η₂) (max R₁ R₂) (lt_min hη₀ hη₂)
    (min_le_left _ _) (le_max_left _ _) Ω Ωs hp hnl
  have hGo := (hN (min η₀ η₂) (max R₁ R₂) (lt_min hη₀ hη₂) (min_le_right _ _)
    (le_max_right _ _) Ω Ωs hp hnl).1
  exact ⟨⟨aUp, bUp, c, hsm, fun u hu w hw =>
    hrep _ hGo subset_rfl u (hu.of_le (by simp)) w hw⟩, hex⟩


/-- (c) helper: `ellOp` at a point through the Euclidean jet of a `C²` function
(`s05_ml_hess`). -/
theorem s05_gc_ellOp_jet (Ω : Set ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ)
    (c : ℂ → ℝ) {u : ℂ → ℝ} {w : ℂ} (hu : ContDiffAt ℝ 2 u w) :
    ellOp Ω aUp bUp c u w = c w * u w -
      ∑ i : Fin 2, ∑ j : Fin 2, aUp w i j * (fderiv ℝ (fderiv ℝ u) w (frameVec i) (frameVec j) -
        fderiv ℝ u w (rhoChristoffel Ω w (frameVec i) (frameVec j))) -
      ∑ i : Fin 2, bUp w i * fderiv ℝ u w (frameVec i) := by
  simp only [ellOp, s05_ml_hess Ω hu, add_sub_cancel_right]

/-- (c) helper: the affine test function `x ↦ L (x - w)`. -/
theorem s05_gc_lin (L : ℂ →L[ℝ] ℝ) (w : ℂ) :
    ContDiff ℝ ∞ (fun x => L (x - w)) ∧ fderiv ℝ (fun x => L (x - w)) = fun _ => L := by
  refine ⟨L.contDiff.comp (contDiff_id.sub contDiff_const), funext fun x => ?_⟩
  have hd : HasFDerivAt (fun x => L (x - w)) L x :=
    (L.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const w)).congr_fderiv (by simp)
  exact hd.fderiv

/-- (c) helper: the quadratic test function `x ↦ L (x - w) M (x - w)`. -/
theorem s05_gc_prod (L M : ℂ →L[ℝ] ℝ) (w : ℂ) :
    ContDiff ℝ ∞ (fun x => L (x - w) * M (x - w)) ∧
      fderiv ℝ (fun x => L (x - w) * M (x - w)) w = 0 ∧
      ∀ X Y : ℂ, fderiv ℝ (fderiv ℝ fun x => L (x - w) * M (x - w)) w X Y =
        L X * M Y + M X * L Y := by
  have hf : ∀ (N : ℂ →L[ℝ] ℝ) (x : ℂ), HasFDerivAt (fun x => N (x - w)) N x := fun N x =>
    (N.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const w)).congr_fderiv (by simp)
  have hD : fderiv ℝ (fun x => L (x - w) * M (x - w)) =
      fun x => L (x - w) • M + M (x - w) • L :=
    funext fun x => ((hf L x).mul (hf M x)).fderiv
  have h2 : HasFDerivAt (fun x => L (x - w) • M + M (x - w) • L) (L.smulRight M + M.smulRight L)
      w := ((hf L w).smul_const M).add ((hf M w).smul_const L)
  refine ⟨((s05_gc_lin L w).1).mul (s05_gc_lin M w).1, by rw [hD]; simp, fun X Y => ?_⟩
  rw [hD, h2.fderiv]
  simp [smul_eq_mul]

/-- (c) helper: iterated covariant derivatives on an open `D` only see the tensor on `D`
(`s05_covDeriv_congr`). -/
theorem s05_gc_iter_congr {Ω D : Set ℂ} (hD : IsOpen D) (i : ℕ) :
    ∀ {k : ℕ} {T T' : TensorField k}, (∀ x ∈ D, T x = T' x) →
      ∀ x ∈ D, rhoIterCovDeriv Ω i T x = rhoIterCovDeriv Ω i T' x := by
  induction i with
  | zero => intro k T T' h x hx; exact h x hx
  | succ i ih =>
    intro k T T' h x hx
    funext v
    simp only [rhoIterCovDeriv]
    rw [ih (fun y hy => s05_covDeriv_congr (Filter.mem_of_superset (hD.mem_nhds hy) h)) x hx]

/-- (c) helper: `‖T‖_{C^j(D)}` on an open `D` only sees `T` on `D`. -/
theorem s05_gc_cjnorm_congr {Ω D : Set ℂ} (hD : IsOpen D) {k : ℕ} {T T' : TensorField k}
    (h : ∀ x ∈ D, T x = T' x) (j : ℕ) : rhoCjNorm Ω j T D = rhoCjNorm Ω j T' D := by
  unfold rhoCjNorm
  refine iSup_congr fun i => iSup_congr fun _ => iSup_congr fun x => iSup_congr fun hx => ?_
  unfold rhoTensorNorm
  rw [s05_gc_iter_congr hD i h x hx]

/-- (c) helper (C0): a representation is unique.  If `ellOp(a, b, c)` and `ellOp(a', b', c')`
agree on all smooth functions at the points of `D` and `a, a'` are symmetric there, then the
coefficients agree on `D` (test with `1`, the coordinates and their products centred at `w`;
`s05_ml_hess`). -/
theorem s05_gc_unique {Ω D : Set ℂ} {a a' : ℂ → Matrix (Fin 2) (Fin 2) ℝ}
    {b b' : ℂ → Fin 2 → ℝ} {c c' : ℂ → ℝ} (ha : ∀ w ∈ D, (a w)ᵀ = a w)
    (ha' : ∀ w ∈ D, (a' w)ᵀ = a' w)
    (h : ∀ u : ℂ → ℝ, ContDiff ℝ ∞ u → ∀ w ∈ D, ellOp Ω a b c u w = ellOp Ω a' b' c' u w) :
    ∀ w ∈ D, a w = a' w ∧ b w = b' w ∧ c w = c' w := by
  intro w hw
  have hjet : ∀ u : ℂ → ℝ, ContDiff ℝ ∞ u → ContDiffAt ℝ 2 u w := fun u hu =>
    hu.contDiffAt.of_le (by simp)
  -- `u = 1`
  have hc : c w = c' w := by
    have h1 : fderiv ℝ (fun _ : ℂ => (1 : ℝ)) = 0 := fderiv_const 1
    have h2 : fderiv ℝ (fderiv ℝ fun _ : ℂ => (1 : ℝ)) w = 0 := by
      rw [h1]; exact fderiv_const_apply _
    have hu1 : ContDiff ℝ ∞ fun _ : ℂ => (1 : ℝ) := contDiff_const
    have E := h _ hu1 w hw
    rw [s05_gc_ellOp_jet Ω a b c (hjet _ hu1), s05_gc_ellOp_jet Ω a' b' c' (hjet _ hu1), h2,
      h1] at E
    simpa using E
  -- `u = L (x - w) M (x - w)`
  have hq : ∀ L M : ℂ →L[ℝ] ℝ, ∑ i : Fin 2, ∑ j : Fin 2, a w i j *
      (L (frameVec i) * M (frameVec j) + M (frameVec i) * L (frameVec j)) =
      ∑ i : Fin 2, ∑ j : Fin 2, a' w i j *
      (L (frameVec i) * M (frameVec j) + M (frameVec i) * L (frameVec j)) := by
    intro L M
    obtain ⟨hu, h1, h2⟩ := s05_gc_prod L M w
    have E := h _ hu w hw
    rw [s05_gc_ellOp_jet Ω a b c (hjet _ hu), s05_gc_ellOp_jet Ω a' b' c' (hjet _ hu), h1] at E
    simp only [h2, sub_self, map_zero, mul_zero, zero_apply, sub_zero,
      zero_sub, Finset.sum_const_zero] at E
    linarith
  have q00 := hq Complex.reCLM Complex.reCLM
  have q11 := hq Complex.imCLM Complex.imCLM
  have q01 := hq Complex.reCLM Complex.imCLM
  simp [Fin.sum_univ_two, frameVec] at q00 q11 q01
  have s := congrFun (congrFun (ha w hw) 0) 1
  have s' := congrFun (congrFun (ha' w hw) 0) 1
  simp only [Matrix.transpose_apply] at s s'
  have hA : a w = a' w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  -- `u = L (x - w)`
  have hl : ∀ L : ℂ →L[ℝ] ℝ, ∑ i : Fin 2, b w i * L (frameVec i) =
      ∑ i : Fin 2, b' w i * L (frameVec i) := by
    intro L
    obtain ⟨hu, h1⟩ := s05_gc_lin L w
    have h2 : fderiv ℝ (fderiv ℝ fun x => L (x - w)) w = 0 := by
      rw [h1]; exact fderiv_const_apply _
    have E := h _ hu w hw
    rw [s05_gc_ellOp_jet Ω a b c (hjet _ hu), s05_gc_ellOp_jet Ω a' b' c' (hjet _ hu), h2, h1,
      hA] at E
    simp only [sub_self, map_zero, mul_zero, zero_apply] at E
    linarith
  have l0 := hl Complex.reCLM
  have l1 := hl Complex.imCLM
  simp [Fin.sum_univ_two, frameVec] at l0 l1
  refine ⟨hA, ?_, hc⟩
  ext i
  fin_cases i <;> simp <;> linarith

/-- (c) helper: the admissibility norms over an open `D` only depend on the coefficients on `D`
(`s05_covDeriv_congr`, iterated). -/
theorem s05_gc_cjcongr {Ω D : Set ℂ} (hD : IsOpen D) {a a' : ℂ → Matrix (Fin 2) (Fin 2) ℝ}
    {b b' : ℂ → Fin 2 → ℝ} {c c' : ℂ → ℝ}
    (h : ∀ w ∈ D, a w = a' w ∧ b w = b' w ∧ c w = c' w) :
    rhoCjNorm Ω 2 (lowerA Ω a - rhoMetricT Ω) D + rhoCjNorm Ω 1 (lowerB Ω b) D +
        rhoCjNorm Ω 0 (scalarField fun w => c w - 2) D =
      rhoCjNorm Ω 2 (lowerA Ω a' - rhoMetricT Ω) D + rhoCjNorm Ω 1 (lowerB Ω b') D +
        rhoCjNorm Ω 0 (scalarField fun w => c' w - 2) D := by
  have hA : ∀ x ∈ D, (lowerA Ω a - rhoMetricT Ω) x = (lowerA Ω a' - rhoMetricT Ω) x :=
    fun x hx => by
      funext v
      simp only [Pi.sub_apply, lowerA, (h x hx).1]
  have hB : ∀ x ∈ D, lowerB Ω b x = lowerB Ω b' x := fun x hx => by
    funext v
    simp only [lowerB, (h x hx).2.1]
  have hC : ∀ x ∈ D, (scalarField fun w => c w - 2) x = (scalarField fun w => c' w - 2) x :=
    fun x hx => by
      funext v
      simp only [scalarField, (h x hx).2.2]
  rw [s05_gc_cjnorm_congr hD hA, s05_gc_cjnorm_congr hD hB, s05_gc_cjnorm_congr hD hC]

/-- (c) phase 2, CN helper: `(k • M)⁻¹ = k⁻¹ • M⁻¹` for `k ≠ 0` (both sides `0` if `M` is
singular). -/
theorem s05_gcn_invsmul {k : ℝ} (hk : k ≠ 0) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (k • M)⁻¹ = k⁻¹ • M⁻¹ := by
  by_cases h : IsUnit M.det
  · have e := Matrix.inv_smul' (A := M) (Units.mk0 k hk) h
    simpa [Units.smul_def] using e
  · have h' : ¬ IsUnit (k • M).det := by
      rw [isUnit_iff_ne_zero, not_not] at h
      rw [Matrix.det_smul, isUnit_iff_ne_zero, h, mul_zero, not_not]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h',
      smul_zero]

/-- (c) phase 2, CN helper: `s04_tn_fd` in the direction `v` itself. -/
theorem s05_gcn_fd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {c : ℝ} (hc : 0 < c)
    (b : ℂ) (g : ℂ → F) (x v : ℂ) :
    fderiv ℝ (fun z => g ((c : ℂ)⁻¹ * (z - b))) ((c : ℂ) * x + b) v = c⁻¹ • fderiv ℝ g x v := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  calc fderiv ℝ (fun z => g ((c : ℂ)⁻¹ * (z - b))) ((c : ℂ) * x + b) v
      = fderiv ℝ (fun z => g ((c : ℂ)⁻¹ * (z - b))) ((c : ℂ) * x + b)
          ((c : ℂ) * (((c⁻¹ : ℝ) : ℂ) * v)) := by
        rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hc', one_mul]
    _ = fderiv ℝ g x (((c⁻¹ : ℝ) : ℂ) * v) := s04_tn_fd hc b g x _
    _ = c⁻¹ • fderiv ℝ g x v := by rw [← Complex.real_smul, ContinuousLinearMap.map_smul]

/-- (c) phase 2, CN helper: the metric of the equidistant surfaces scales as
`g_τ^{A Ω}(A y) = c⁻² g_τ^Ω(y)` (`s04_tg_geod`, `s04_tn_hypInner`). -/
theorem s05_gcn_metric {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {c : ℝ}
    (hc : 0 < c) (b : ℂ) {y : ℂ} (hy : y ∈ Ω) (τ : ℝ) :
    graphMetric ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * y + b) τ =
      ((c ^ 2)⁻¹ : ℝ) • graphMetric Ω y τ := by
  have hΩo : IsOpen Ω := by
    obtain ⟨f, hf⟩ := hΩ
    exact hf.isOpen isOpen_ball
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hev : (fun x => normalGeod ((fun z => (c : ℂ) * z + b) '' Ω) x τ) =ᶠ[𝓝 ((c : ℂ) * y + b)]
      fun x => c • normalGeod Ω ((c : ℂ)⁻¹ * (x - b)) τ + ((b, 0) : ℂ × ℝ) := by
    filter_upwards [(s04_tn_open hΩo hc' b).mem_nhds (Set.mem_image_of_mem _ hy)] with x hx
    obtain ⟨x0, hx0, rfl⟩ := hx
    have e : (c : ℂ)⁻¹ * ((c : ℂ) * x0 + b - b) = x0 := by
      rw [add_sub_cancel_right, inv_mul_cancel_left₀ hc']
    rw [e, s04_tg_geod hΩ hc b hx0 τ]
    refine Prod.ext ?_ ?_ <;> simp [Complex.real_smul]
  have hfd : ∀ i : Fin 2, fderiv ℝ (fun x => normalGeod ((fun z => (c : ℂ) * z + b) '' Ω) x τ)
      ((c : ℂ) * y + b) (frameVec i) = fderiv ℝ (fun x => normalGeod Ω x τ) y (frameVec i) := by
    intro i
    have := invertibleOfNonzero hc.ne'
    rw [hev.fderiv_eq, fderiv_add_const,
      show (fun x => c • normalGeod Ω ((c : ℂ)⁻¹ * (x - b)) τ) =
        c • fun x => normalGeod Ω ((c : ℂ)⁻¹ * (x - b)) τ from rfl,
      fderiv_const_smul_of_invertible, smul_apply]
    have h := s05_gcn_fd hc b (fun x => normalGeod Ω x τ) y (frameVec i)
    rw [h, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  ext i j
  simp only [graphMetric, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hfd,
    s04_tg_geod hΩ hc b hy τ]
  rw [s04_tn_hypInner, div_eq_inv_mul]

/-- (c) phase 2, CN helper: the gradient of `v ∘ A⁻¹` (`v'` agreeing with it on an open set). -/
theorem s05_gcn_grad {c : ℝ} (hc : 0 < c) (b : ℂ) {U : Set ℂ} (hU : IsOpen U) {v v' : ℂ → ℝ}
    (hv : ∀ z ∈ U, v' z = v ((z - b) / c)) {y : ℂ} (hy : (c : ℂ) * y + b ∈ U) :
    gradCoords v' ((c : ℂ) * y + b) = c⁻¹ • gradCoords v y := by
  have hev : v' =ᶠ[𝓝 ((c : ℂ) * y + b)] fun z => v ((c : ℂ)⁻¹ * (z - b)) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    rw [hv z hz, div_eq_inv_mul]
  funext i
  simp only [gradCoords, Pi.smul_apply]
  rw [hev.fderiv_eq]
  exact s05_gcn_fd hc b v y (frameVec i)

/-- (c) phase 2, CN helper: `√det g_τ` scales by `c⁻²`. -/
theorem s05_gcn_sdet {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {c : ℝ}
    (hc : 0 < c) (b : ℂ) {y : ℂ} (hy : y ∈ Ω) (τ : ℝ) :
    graphSdet ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * y + b) τ =
      (c ^ 2)⁻¹ * graphSdet Ω y τ := by
  simp only [graphSdet]
  rw [s05_gcn_metric hΩ hc b hy τ, Matrix.det_smul, Fintype.card_fin,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- (c) phase 2, CN helper: `W` is invariant. -/
theorem s05_gcn_W {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {c : ℝ}
    (hc : 0 < c) (b : ℂ) {v v' : ℂ → ℝ}
    (hv : ∀ z ∈ (fun z => (c : ℂ) * z + b) '' Ω, v' z = v ((z - b) / c)) {y : ℂ} (hy : y ∈ Ω)
    (τ : ℝ) : graphW ((fun z => (c : ℂ) * z + b) '' Ω) v' ((c : ℂ) * y + b) τ = graphW Ω v y τ := by
  have hΩo : IsOpen Ω := by
    obtain ⟨f, hf⟩ := hΩ
    exact hf.isOpen isOpen_ball
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  simp only [graphW]
  rw [s05_gcn_metric hΩ hc b hy τ, s05_gcn_invsmul (by positivity : (0 : ℝ) < (c ^ 2)⁻¹).ne',
    s05_gcn_grad hc b (s04_tn_open hΩo hc' b) hv (Set.mem_image_of_mem _ hy)]
  simp only [inv_inv, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  congr 2
  field_simp

/-- (c) phase 2, CN helper: the flux scales by `c⁻¹`. -/
theorem s05_gcn_flux {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {c : ℝ}
    (hc : 0 < c) (b : ℂ) {v v' : ℂ → ℝ}
    (hv : ∀ z ∈ (fun z => (c : ℂ) * z + b) '' Ω, v' z = v ((z - b) / c)) {y : ℂ} (hy : y ∈ Ω)
    (τ : ℝ) (i : Fin 2) :
    graphFlux ((fun z => (c : ℂ) * z + b) '' Ω) v' τ ((c : ℂ) * y + b) i =
      c⁻¹ * graphFlux Ω v τ y i := by
  have hΩo : IsOpen Ω := by
    obtain ⟨f, hf⟩ := hΩ
    exact hf.isOpen isOpen_ball
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  simp only [graphFlux]
  rw [s05_gcn_W hΩ hc b hv hy τ, s05_gcn_sdet hΩ hc b hy τ, s05_gcn_metric hΩ hc b hy τ,
    s05_gcn_invsmul (by positivity : (0 : ℝ) < (c ^ 2)⁻¹).ne',
    s05_gcn_grad hc b (s04_tn_open hΩo hc' b) hv (Set.mem_image_of_mem _ hy)]
  simp only [inv_inv, Matrix.smul_mulVec, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- (c) phase 2, CN helper: `H_up` is invariant under `A`. -/
theorem s05_gcn_meanCurv {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {c : ℝ}
    (hc : 0 < c) (b : ℂ) {v v' : ℂ → ℝ}
    (hv : ∀ z ∈ (fun z => (c : ℂ) * z + b) '' Ω, v' z = v ((z - b) / c)) {y : ℂ} (hy : y ∈ Ω) :
    meanCurvUp ((fun z => (c : ℂ) * z + b) '' Ω) v' ((c : ℂ) * y + b) = meanCurvUp Ω v y := by
  have hΩo : IsOpen Ω := by
    obtain ⟨f, hf⟩ := hΩ
    exact hf.isOpen isOpen_ball
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hU := s04_tn_open hΩo hc' b
  have hvy : v' ((c : ℂ) * y + b) = v y := by
    rw [hv _ (Set.mem_image_of_mem _ hy), add_sub_cancel_right, mul_div_cancel_left₀ _ hc']
  have hτ : (fun τ => graphSdet ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * y + b) τ /
      graphW ((fun z => (c : ℂ) * z + b) '' Ω) v' ((c : ℂ) * y + b) τ) =
      fun τ => (c ^ 2)⁻¹ * (graphSdet Ω y τ / graphW Ω v y τ) := by
    funext τ
    rw [s05_gcn_sdet hΩ hc b hy τ, s05_gcn_W hΩ hc b hv hy τ, mul_div_assoc]
  have hfl : ∀ i : Fin 2, fderiv ℝ (fun x => graphFlux ((fun z => (c : ℂ) * z + b) '' Ω) v' (v y)
      x i) ((c : ℂ) * y + b) (frameVec i) =
      c⁻¹ * (c⁻¹ * fderiv ℝ (fun x => graphFlux Ω v (v y) x i) y (frameVec i)) := by
    intro i
    have hev : (fun x => graphFlux ((fun z => (c : ℂ) * z + b) '' Ω) v' (v y) x i) =ᶠ[𝓝 ((c : ℂ) * y + b)]
        fun x => c⁻¹ * graphFlux Ω v (v y) ((c : ℂ)⁻¹ * (x - b)) i := by
      filter_upwards [hU.mem_nhds (Set.mem_image_of_mem _ hy)] with x hx
      obtain ⟨x0, hx0, rfl⟩ := hx
      rw [s05_gcn_flux hΩ hc b hv hx0 (v y) i, add_sub_cancel_right, inv_mul_cancel_left₀ hc']
    rw [hev.fderiv_eq, s04_tn_fdmul]
    have h := s05_gcn_fd hc b (fun x => graphFlux Ω v (v y) x i) y (frameVec i)
    simp only [smul_eq_mul] at h
    rw [h]
  unfold meanCurvUp
  rw [hvy, hτ, deriv_const_mul_field, Fin.sum_univ_two, Fin.sum_univ_two, hfl 0, hfl 1,
    s05_gcn_sdet hΩ hc b hy]
  by_cases hS : graphSdet Ω y (v y) = 0
  · simp [hS]
  · have hc0 : c ≠ 0 := hc.ne'
    field_simp

/-- (c) phase 2, CN helper: `𝒬` is invariant under `A`. -/
theorem s05_gcn_graphQ {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {c : ℝ}
    (hc : 0 < c) (b : ℂ) {v v' : ℂ → ℝ}
    (hv : ∀ z ∈ (fun z => (c : ℂ) * z + b) '' Ω, v' z = v ((z - b) / c)) {y : ℂ} (hy : y ∈ Ω) :
    graphQ ((fun z => (c : ℂ) * z + b) '' Ω) v' ((c : ℂ) * y + b) = graphQ Ω v y := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  unfold graphQ
  rw [s05_gcn_meanCurv hΩ hc b hv hy, (subsec_poincare_natural_affine hΩ hc' hy).2]

/-- (c) phase 2, CN: the graph operator is natural under a real similarity `A z = c z + b`:
`𝓛_{AΩ}(u ∘ A⁻¹)(A x) = 𝓛_Ω(u)(x)` for every function `u` (`meanCurvUp` via `s04_tg_geod`, the
`schwarzNorm` invariance, `slabTop` via `s04_tg_slabnat`). -/
theorem s05_gcn_graphOp {K : ℝ} {Ω Ωs : Set ℂ} (hp : IsKQuasiPair Ω Ωs K) {c : ℝ} (hc : 0 < c)
    (b : ℂ) (u : ℂ → ℝ) {x : ℂ} (hx : x ∈ Ω) :
    graphOp ((fun z => (c : ℂ) * z + b) '' Ω) ((fun z => (c : ℂ) * z + b) '' Ωs)
        (fun z => u ((z - b) / c)) ((c : ℂ) * x + b) = graphOp Ω Ωs u x := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap (s03_b0_jordanPair hp)
  have hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω := ⟨f, hf⟩
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  unfold graphOp graphQDeriv
  refine intervalIntegral.integral_congr fun θ _ => ?_
  congr 1
  funext s
  refine s05_gcn_graphQ hΩ hc b ?_ hx
  intro z hz
  obtain ⟨z0, hz0, rfl⟩ := hz
  have e : ((c : ℂ) * z0 + b - b) / c = z0 := by
    rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hc']
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e, s04_tg_slabnat hp hc b hz0]

/-- (c) phase 2, CN: `ellOp` is natural under a real similarity `A z = c z + b`, the coefficients
transforming as `a' = c² a ∘ A⁻¹`, `b' = c b ∘ A⁻¹`, `c' = c ∘ A⁻¹` (`s04_tn_iter`, `s04_tn_fd`). -/
theorem s05_gcn_ellOp {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {c : ℝ}
    (hc : 0 < c) (b : ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ)
    (cf : ℂ → ℝ) (u : ℂ → ℝ) {x : ℂ} (hx : x ∈ Ω) :
    ellOp ((fun z => (c : ℂ) * z + b) '' Ω) (fun z => c ^ 2 • aUp ((z - b) / c))
        (fun z => c • bUp ((z - b) / c)) (fun z => cf ((z - b) / c)) (fun z => u ((z - b) / c))
        ((c : ℂ) * x + b) = ellOp Ω aUp bUp cf u x := by
  obtain ⟨f, hf⟩ := hΩ
  have hΩo : IsOpen Ω := hf.isOpen isOpen_ball
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hA : ∀ y : ℂ, ((c : ℂ) * y + b - b) / c = y := fun y => by
    rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hc']
  have hcc : ∀ v : ℂ, (c : ℂ) * (((c⁻¹ : ℝ) : ℂ) * v) = v := fun v => by
    rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hc', one_mul]
  have hu' : (fun z => u ((z - b) / c)) = fun z => u ((c : ℂ)⁻¹ * (z - b)) := by
    funext z
    rw [div_eq_inv_mul]
  have hfd : ∀ v : ℂ, fderiv ℝ (fun z => u ((z - b) / c)) ((c : ℂ) * x + b) v =
      c⁻¹ * fderiv ℝ u x v := by
    intro v
    calc fderiv ℝ (fun z => u ((z - b) / c)) ((c : ℂ) * x + b) v
        = fderiv ℝ (fun z => u ((c : ℂ)⁻¹ * (z - b))) ((c : ℂ) * x + b)
            ((c : ℂ) * (((c⁻¹ : ℝ) : ℂ) * v)) := by rw [hu', hcc]
      _ = fderiv ℝ u x (((c⁻¹ : ℝ) : ℂ) * v) := s04_tn_fd hc b u x _
      _ = c⁻¹ * fderiv ℝ u x v := by
        rw [← Complex.real_smul, ContinuousLinearMap.map_smul, smul_eq_mul]
  have hhom : ∀ (y : ℂ) (w : Fin (0 + 2) → ℂ) (i : Fin (0 + 2)) (a : ℝ),
      rhoIterCovDeriv Ω 2 (scalarField u) y (Function.update w i ((a : ℂ) * w i)) =
        a * rhoIterCovDeriv Ω 2 (scalarField u) y w :=
    fun y w i a => s04_tn_hom Ω (fun _ _ i _ => i.elim0) 2 y w i a
  have hrel : ∀ y ∈ Ω, ∀ w : Fin 0 → ℂ,
      scalarField (fun z => u ((z - b) / c)) ((c : ℂ) * y + b) (fun i => (c : ℂ) * w i) =
        scalarField u y w := fun y _ w => by
    simp only [scalarField, hA]
  have hgrad := fun y (hy : y ∈ Ω) => (s04_tn_lambda ⟨f, hf⟩ hc b hy).2
  have hH : ∀ i j : Fin 2, rhoHess ((fun z => (c : ℂ) * z + b) '' Ω) (fun z => u ((z - b) / c))
      ((c : ℂ) * x + b) ![frameVec i, frameVec j] =
        c⁻¹ ^ 2 * rhoHess Ω u x ![frameVec i, frameVec j] := by
    intro i j
    have e : (fun l => (c : ℂ) * (((c⁻¹ : ℝ) : ℂ) * ![frameVec i, frameVec j] l)) =
        ![frameVec i, frameVec j] := funext fun l => hcc _
    calc rhoHess ((fun z => (c : ℂ) * z + b) '' Ω) (fun z => u ((z - b) / c))
          ((c : ℂ) * x + b) ![frameVec i, frameVec j]
        = rhoIterCovDeriv ((fun z => (c : ℂ) * z + b) '' Ω) 2
            (scalarField fun z => u ((z - b) / c)) ((c : ℂ) * x + b)
            (fun l => (c : ℂ) * (((c⁻¹ : ℝ) : ℂ) * ![frameVec i, frameVec j] l)) := by
          rw [e]
          rfl
      _ = rhoIterCovDeriv Ω 2 (scalarField u) x
            (fun l => ((c⁻¹ : ℝ) : ℂ) * ![frameVec i, frameVec j] l) :=
          s04_tn_iter hΩo hc hrel hgrad 2 x hx _
      _ = c⁻¹ ^ 2 * rhoHess Ω u x ![frameVec i, frameVec j] :=
          s04_tn_allslot (hhom x) c⁻¹ _
  simp only [ellOp, hA, hH, hfd, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two]
  field_simp

/-- (c) phase 2, CM helper: `Γ(e₁, e₁) + Γ(e₂, e₂) = 0` for a conformal metric. -/
theorem s05_gcm_christ_trace (Ω : Set ℂ) (w : ℂ) :
    rhoChristoffel Ω w (frameVec 0) (frameVec 0) + rhoChristoffel Ω w (frameVec 1) (frameVec 1) =
      0 := by
  apply Complex.ext <;> simp [rhoChristoffel, frameVec]

/-- (c) phase 2, CM helper: a half-plane and its complementary half-plane form a Jordan pair. -/
theorem s05_gcm_jordan {α : ℂ} (hα : α ≠ 0) (β : ℂ) :
    IsJordanPair {z | 0 < (α * z + β).im} {z | (α * z + β).im < 0} := by
  refine ⟨((Homeomorph.mulLeft₀ α hα).trans (Homeomorph.addRight β)).symm, ?_, ?_⟩ <;>
    rw [Homeomorph.image_symm] <;> rfl

/-- (c) phase 2, CM helper: where the Schwarzian vanishes, `I = ρ`, i.e. `fffMat = λ² · 1`
(`s04_td_fffeq`). -/
theorem s05_gcm_fff {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {y : ℂ}
    (hy : y ∈ Ω) (hS : schwarzian (Function.invFunOn f unitDisc) y = 0) :
    fffMat Ω y = (poincareDensity Ω y ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  have h := s04_td_fffeq hf hy ![frameVec i, frameVec j]
  rw [hS] at h
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    zero_mul, Complex.zero_re, mul_zero, add_zero, Pi.sub_apply] at h
  have h' := sub_eq_zero.1 h
  simp only [fffMat, Matrix.of_apply, h', rhoMetricT, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [frameVec]

/-- (c) phase 2, CM helper: where the Schwarzian vanishes, `B = 0` (`s04_td_shapeeq`). -/
theorem s05_gcm_shape {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {x : ℂ}
    (hx : x ∈ Ω) (hS : schwarzian (Function.invFunOn f unitDisc) x = 0) : shapeMat Ω x = 0 := by
  have hl := s02_poincareDensity_pos ⟨f, hf⟩ hx
  ext i j
  have h := s04_td_shapeeq hf hx (by rw [hS, norm_zero, zero_pow two_ne_zero]; positivity)
    ![frameVec j, frameVec i]
  rw [hS] at h
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    zero_mul, Complex.zero_re, sub_zero, div_one, shapeT] at h
  have h2 := (mul_eq_zero.1 h).resolve_left (by positivity)
  fin_cases i <;> fin_cases j <;>
    simpa [cvec, frameVec, mulVec, dotProduct, Fin.sum_univ_two] using h2

/-- (c) phase 2, CM helper: on an open set where the Schwarzian vanishes, `Δ_I = Δ_ρ`. -/
theorem s05_gcm_lap {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) (hΩo : IsOpen Ω)
    (hS : ∀ y ∈ Ω, schwarzian (Function.invFunOn f unitDisc) y = 0) (u : ℂ → ℝ) {x : ℂ}
    (hx : x ∈ Ω) : fffLaplacian Ω u x = rhoLaplacian Ω u x := by
  have hsd : ∀ y ∈ Ω, Real.sqrt (fffMat Ω y).det = poincareDensity Ω y ^ 2 := by
    intro y hy
    rw [s05_gcm_fff hf hy (hS y hy), Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one,
      ← pow_mul, show 2 * 2 = 2 * 2 from rfl, pow_mul, Real.sqrt_sq (by positivity)]
  have hev : ∀ i : Fin 2, (fun y => Real.sqrt (fffMat Ω y).det *
      ((fffMat Ω y)⁻¹ *ᵥ gradCoords u y) i) =ᶠ[𝓝 x] fun y => fderiv ℝ u y (frameVec i) := by
    intro i
    filter_upwards [hΩo.mem_nhds hx] with y hy
    have hl := s02_poincareDensity_pos ⟨f, hf⟩ hy
    have hinv : (fffMat Ω y)⁻¹ =
        (poincareDensity Ω y ^ 2)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      refine Matrix.inv_eq_left_inv ?_
      rw [s05_gcm_fff hf hy (hS y hy), Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
        inv_mul_cancel₀ (by positivity), one_smul]
    rw [hsd y hy, hinv, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    rfl
  unfold fffLaplacian rhoLaplacian
  rw [hsd x hx, Fin.sum_univ_two, Fin.sum_univ_two, (hev 0).fderiv_eq, (hev 1).fderiv_eq,
    s05_rhoHess_eq, s05_rhoHess_eq]
  have h0 := congrArg (fderiv ℝ u x) (s05_gcm_christ_trace Ω x)
  rw [map_add, map_zero] at h0
  congr 1
  linarith

/-- (c) phase 2, CM: the model values.  For any coefficient functions `Φ` with the property of
`s05_ml_rep`, at the jet `(0, λ, 0, Dλ, 0, 0, 0)` of `v = 0` on a half-plane (where `S ≡ 0`):
`Φ = (λ⁻² I, 0, 2)`, i.e. `D𝒬(0) = 2 - Δ_ρ` (`s05_go_deriv` with `B = 0`, `I = ρ`; C0 on `{x}`). -/
theorem s05_gcm_model
    {Φa : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) →
      Matrix (Fin 2) (Fin 2) ℝ}
    {Φb : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) →
      Fin 2 → ℝ}
    {Φc : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) → ℝ}
    (hsym : ∀ J, (Φa J)ᵀ = Φa J)
    (hrep : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω →
      ∀ U : Set ℂ, IsOpen U → U ⊆ Ω → (∀ x ∈ U, schwarzNorm Ω x < 1) →
      ∀ v u : ℂ → ℝ, ContDiffOn ℝ 2 v U → ContDiffOn ℝ 2 u U → ∀ w ∈ U,
        (v w, poincareDensity Ω w, schwarzian (Function.invFunOn f unitDisc) w,
            fun i => fderiv ℝ (poincareDensity Ω) w (frameVec i),
            fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) w (frameVec i),
            fun i => fderiv ℝ v w (frameVec i),
            fun i j => fderiv ℝ (fderiv ℝ v) w (frameVec i) (frameVec j)) ∈
          {J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) |
            0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1} →
        graphQDeriv Ω v u w =
          ellOp Ω
            (fun _ => Φa (v w, poincareDensity Ω w, schwarzian (Function.invFunOn f unitDisc) w,
              fun i => fderiv ℝ (poincareDensity Ω) w (frameVec i),
              fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) w (frameVec i),
              fun i => fderiv ℝ v w (frameVec i),
              fun i j => fderiv ℝ (fderiv ℝ v) w (frameVec i) (frameVec j)))
            (fun _ => Φb (v w, poincareDensity Ω w, schwarzian (Function.invFunOn f unitDisc) w,
              fun i => fderiv ℝ (poincareDensity Ω) w (frameVec i),
              fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) w (frameVec i),
              fun i => fderiv ℝ v w (frameVec i),
              fun i j => fderiv ℝ (fderiv ℝ v) w (frameVec i) (frameVec j)))
            (fun _ => Φc (v w, poincareDensity Ω w, schwarzian (Function.invFunOn f unitDisc) w,
              fun i => fderiv ℝ (poincareDensity Ω) w (frameVec i),
              fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) w (frameVec i),
              fun i => fderiv ℝ v w (frameVec i),
              fun i j => fderiv ℝ (fderiv ℝ v) w (frameVec i) (frameVec j)))
            u w)
    {α β : ℂ} (hα : α ≠ 0) {x : ℂ} (hx : 0 < (α * x + β).im) :
    Φa ((0 : ℝ), poincareDensity {z | 0 < (α * z + β).im} x, (0 : ℂ),
        fun i => fderiv ℝ (poincareDensity {z | 0 < (α * z + β).im}) x (frameVec i),
        (0 : Fin 2 → ℂ), (0 : Fin 2 → ℝ), (0 : Fin 2 → Fin 2 → ℝ)) =
        (poincareDensity {z | 0 < (α * z + β).im} x ^ 2)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      Φb ((0 : ℝ), poincareDensity {z | 0 < (α * z + β).im} x, (0 : ℂ),
        fun i => fderiv ℝ (poincareDensity {z | 0 < (α * z + β).im}) x (frameVec i),
        (0 : Fin 2 → ℂ), (0 : Fin 2 → ℝ), (0 : Fin 2 → Fin 2 → ℝ)) = 0 ∧
      Φc ((0 : ℝ), poincareDensity {z | 0 < (α * z + β).im} x, (0 : ℂ),
        fun i => fderiv ℝ (poincareDensity {z | 0 < (α * z + β).im}) x (frameVec i),
        (0 : Fin 2 → ℂ), (0 : Fin 2 → ℝ), (0 : Fin 2 → Fin 2 → ℝ)) = 2 := by
  set D : Set ℂ := {z | 0 < (α * z + β).im} with hDdef
  have hJ : IsJordanPair D {z | (α * z + β).im < 0} := s05_gcm_jordan hα β
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  have hDo : IsOpen D := s05_jordan_isOpen hJ
  have hs0 : ∀ y ∈ D, schwarzNorm D y = 0 :=
    (s02_halfplane α β hα 1 (Or.inl rfl) D fun z => by rw [one_mul]; exact Iff.rfl).1
  have hs1 : ∀ y ∈ D, schwarzNorm D y < 1 := fun y hy => by rw [hs0 y hy]; norm_num
  have hpos : ∀ y ∈ D, 0 < poincareDensity D y := fun y hy => s02_poincareDensity_pos ⟨f, hf⟩ hy
  have hS : ∀ y ∈ D, schwarzian (Function.invFunOn f unitDisc) y = 0 := by
    intro y hy
    have h := eq_def_s hf hy
    rw [hs0 y hy] at h
    have hl := hpos y hy
    rcases div_eq_zero_iff.1 h.symm with h3 | h3
    · exact norm_eq_zero.1 h3
    · exact absurd h3 (by positivity)
  have hDS : fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) x = 0 := by
    have hev : schwarzian (Function.invFunOn f unitDisc) =ᶠ[𝓝 x] fun _ => (0 : ℂ) :=
      Filter.mem_of_superset (hDo.mem_nhds hx) fun y hy => hS y hy
    rw [hev.fderiv_eq]
    exact fderiv_const_apply _
  have h0 : fderiv ℝ (0 : ℂ → ℝ) = 0 := fderiv_const 0
  have h1 : fderiv ℝ (fderiv ℝ (0 : ℂ → ℝ)) = 0 := by
    rw [h0]
    exact fderiv_const 0
  have hjet : ((0 : ℂ → ℝ) x, poincareDensity D x, schwarzian (Function.invFunOn f unitDisc) x,
      (fun i => fderiv ℝ (poincareDensity D) x (frameVec i)),
      (fun i => fderiv ℝ (schwarzian (Function.invFunOn f unitDisc)) x (frameVec i)),
      (fun i => fderiv ℝ (0 : ℂ → ℝ) x (frameVec i)),
      fun i j => fderiv ℝ (fderiv ℝ (0 : ℂ → ℝ)) x (frameVec i) (frameVec j)) =
      ((0 : ℝ), poincareDensity D x, (0 : ℂ),
        (fun i => fderiv ℝ (poincareDensity D) x (frameVec i)),
        (0 : Fin 2 → ℂ), (0 : Fin 2 → ℝ), (0 : Fin 2 → Fin 2 → ℝ)) := by
    rw [h1, h0, hDS, hS x hx]
    rfl
  have hO : ((0 : ℝ), poincareDensity D x, (0 : ℂ),
        (fun i => fderiv ℝ (poincareDensity D) x (frameVec i)),
        (0 : Fin 2 → ℂ), (0 : Fin 2 → ℝ), (0 : Fin 2 → Fin 2 → ℝ)) ∈
      {J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) |
        0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1} := by
    have hl := hpos x hx
    refine ⟨hl, ?_⟩
    simp only [norm_zero, zero_mul, Real.cosh_zero, mul_one]
    positivity
  have hshape := s05_gcm_shape hf hx (hS x hx)
  have hmodel : ∀ u : ℂ → ℝ, ContDiff ℝ ∞ u → ∀ w ∈ ({x} : Set ℂ),
      ellOp D (fun _ => Φa ((0 : ℝ), poincareDensity D x, (0 : ℂ),
          (fun i => fderiv ℝ (poincareDensity D) x (frameVec i)),
          (0 : Fin 2 → ℂ), (0 : Fin 2 → ℝ), (0 : Fin 2 → Fin 2 → ℝ)))
        (fun _ => Φb ((0 : ℝ), poincareDensity D x, (0 : ℂ),
          (fun i => fderiv ℝ (poincareDensity D) x (frameVec i)),
          (0 : Fin 2 → ℂ), (0 : Fin 2 → ℝ), (0 : Fin 2 → Fin 2 → ℝ)))
        (fun _ => Φc ((0 : ℝ), poincareDensity D x, (0 : ℂ),
          (fun i => fderiv ℝ (poincareDensity D) x (frameVec i)),
          (0 : Fin 2 → ℂ), (0 : Fin 2 → ℝ), (0 : Fin 2 → Fin 2 → ℝ))) u w =
      ellOp D (fun _ => (poincareDensity D x ^ 2)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (fun _ => 0) (fun _ => 2) u w := by
    intro u hu w hw
    rw [Set.mem_singleton_iff.1 hw]
    have hr := hrep D {z | (α * z + β).im < 0} hJ f hf D hDo subset_rfl hs1 0 u
      contDiffOn_const (hu.contDiffOn.of_le (by simp)) x hx (by rw [hjet]; exact hO)
    rw [hjet] at hr
    rw [← hr, s05_go_deriv hJ hDo subset_rfl hs1 hu.contDiffOn hx, hshape,
      s05_gcm_lap hf hDo hS u hx]
    have hl := hpos x hx
    simp only [ellOp, rhoLaplacian, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply,
      Pi.zero_apply, zero_mul, sub_zero, Matrix.trace_zero, smul_eq_mul]
    simp
    field_simp
  obtain ⟨ha, hb, hc⟩ := s05_gc_unique (fun _ _ => hsym _)
    (fun _ _ => by rw [Matrix.transpose_smul, Matrix.transpose_one]) hmodel x rfl
  exact ⟨ha, hb, hc⟩

/-- (c) phase 2, CC helper: differentiation under `∫₀¹ dθ` for a map smooth on
`(-1/2, 3/2) × U`. -/
theorem s05_gcc_hasfd {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set ℂ}
    (hU : IsOpen U) {G : ℝ × ℂ → E} (hG : ContDiffOn ℝ ∞ G (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U))
    {w : ℂ} (hw : w ∈ U) :
    HasFDerivAt (fun x => ∫ θ in (0 : ℝ)..1, G (θ, x))
      (∫ θ in (0 : ℝ)..1, (fderiv ℝ G (θ, w)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ)) w := by
  have hP : IsOpen (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U) := isOpen_Ioo.prod hU
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU w hw
  have hcb : closedBall w (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  have hI : Icc (0 : ℝ) 1 ⊆ Ioo (-1 / 2 : ℝ) (3 / 2) := Icc_subset_Ioo (by norm_num) (by norm_num)
  have hKP : Icc (0 : ℝ) 1 ×ˢ closedBall w (r / 2) ⊆ Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U :=
    prod_mono hI hcb
  have hd : ContinuousOn (fun p => (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ ℝ ℂ))
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U) :=
    (hG.continuousOn_fderiv_of_isOpen hP (by simp)).clm_comp continuousOn_const
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall w (r / 2))).exists_bound_of_continuousOn
    (hd.mono hKP)
  have hIoc : ∀ θ ∈ Set.uIoc (0 : ℝ) 1, θ ∈ Icc (0 : ℝ) 1 := fun θ hθ => by
    rw [Set.uIoc_of_le zero_le_one] at hθ
    exact Ioc_subset_Icc_self hθ
  have hcont : ∀ x ∈ U, ContinuousOn (fun θ => G (θ, x)) (Icc 0 1) := fun x hx =>
    hG.continuousOn.comp (Continuous.continuousOn (by fun_prop)) fun θ hθ => ⟨hI hθ, hx⟩
  have hcw : ContinuousOn (fun θ => (fderiv ℝ G (θ, w)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ))
      (Icc 0 1) :=
    hd.comp (Continuous.continuousOn (by fun_prop)) fun θ hθ => ⟨hI hθ, hw⟩
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x θ => G (θ, x))
    (F' := fun x θ => (fderiv ℝ G (θ, x)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ))
    (bound := fun _ => C) (closedBall_mem_nhds w (half_pos hr)) ?_ ?_ ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [hU.mem_nhds hw] with x hx
    exact ((hcont x hx).mono hIoc).aestronglyMeasurable measurableSet_uIoc
  · exact (hcont w hw).intervalIntegrable_of_Icc zero_le_one
  · exact (hcw.mono hIoc).aestronglyMeasurable measurableSet_uIoc
  · exact Filter.Eventually.of_forall fun θ hθ x hx => hC (θ, x) ⟨hIoc θ hθ, hx⟩
  · refine Filter.Eventually.of_forall fun θ hθ x hx => ?_
    have hdiff : DifferentiableAt ℝ G (θ, x) :=
      (hG.differentiableOn (by simp)).differentiableAt (hP.mem_nhds (hKP ⟨hIoc θ hθ, hx⟩))
    exact hdiff.hasFDerivAt.comp x (hasFDerivAt_prodMk_right θ x)

/-- (c) phase 2, CC helper: locally uniform convergence on `(-1/2, 3/2) × U` passes to
`∫₀¹ dθ`. -/
theorem s05_gcc_c0 {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set ℂ}
    (hU : IsOpen U) {G : ℕ → ℝ × ℂ → E} {Gl : ℝ × ℂ → E}
    (h1 : ∀ᶠ n in atTop, ContinuousOn (G n) (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U))
    (h2 : ContinuousOn Gl (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U))
    (h3 : TendstoLocallyUniformlyOn G Gl atTop (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U)) :
    TendstoLocallyUniformlyOn (fun n w => ∫ θ in (0 : ℝ)..1, G n (θ, w))
      (fun w => ∫ θ in (0 : ℝ)..1, Gl (θ, w)) atTop U := by
  have hP : IsOpen (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U) := isOpen_Ioo.prod hU
  have hI : Icc (0 : ℝ) 1 ⊆ Ioo (-1 / 2 : ℝ) (3 / 2) := Icc_subset_Ioo (by norm_num) (by norm_num)
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  have hKP : Icc (0 : ℝ) 1 ×ˢ K ⊆ Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U := prod_mono hI hKU
  have hu := (tendstoLocallyUniformlyOn_iff_forall_isCompact hP).1 h3 _ hKP
    (isCompact_Icc.prod hK)
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  filter_upwards [hu (ε / 2) (by positivity), h1] with n hn hc
  intro w hw
  have hcL : ContinuousOn (fun θ => Gl (θ, w)) (Icc 0 1) :=
    h2.comp (Continuous.continuousOn (by fun_prop)) fun θ hθ => hKP ⟨hθ, hw⟩
  have hcn : ContinuousOn (fun θ => G n (θ, w)) (Icc 0 1) :=
    hc.comp (Continuous.continuousOn (by fun_prop)) fun θ hθ => hKP ⟨hθ, hw⟩
  have hb : ∀ θ ∈ Set.uIoc (0 : ℝ) 1, ‖Gl (θ, w) - G n (θ, w)‖ ≤ ε / 2 := by
    intro θ hθ
    rw [Set.uIoc_of_le zero_le_one] at hθ
    rw [← dist_eq_norm]
    exact (hn (θ, w) ⟨Ioc_subset_Icc_self hθ, hw⟩).le
  rw [dist_eq_norm, ← intervalIntegral.integral_sub (hcL.intervalIntegrable_of_Icc zero_le_one)
    (hcn.intervalIntegrable_of_Icc zero_le_one)]
  calc ‖∫ θ in (0 : ℝ)..1, (Gl (θ, w) - G n (θ, w))‖ ≤ ε / 2 * |1 - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hb
    _ < ε := by norm_num; linarith

/-- (c) phase 2, CC helper: `w ↦ ∫₀¹ G(θ, w) dθ` is `C^m` on `U` for `G` smooth on
`(-1/2, 3/2) × U`, for every target space. -/
theorem s05_gcc_smooth {U : Set ℂ} (hU : IsOpen U) (m : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : ℝ × ℂ → E),
      ContDiffOn ℝ ∞ G (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U) →
      ContDiffOn ℝ m (fun w => ∫ θ in (0 : ℝ)..1, G (θ, w)) U := by
  have hP : IsOpen (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U) := isOpen_Ioo.prod hU
  induction m with
  | zero =>
    intro E _ _ G hG
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun w hw => (s05_gcc_hasfd hU hG hw).continuousAt.continuousWithinAt
  | succ m ih =>
    intro E _ _ G hG
    have hd := s04_tc_clm hP
      ((ContinuousLinearMap.compL ℝ ℂ (ℝ × ℂ) E).flip (ContinuousLinearMap.inr ℝ ℝ ℂ))
      (s04_tc_fderiv hP (s04_tc_const hG))
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun w hw => (s05_gcc_hasfd hU hG hw).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    exact (ih (ℂ →L[ℝ] E) _ hd.2.1).congr fun w hw => (s05_gcc_hasfd hU hG hw).fderiv

/-- (c) phase 2, CC helper: the order-`i` part of `s05_gcc_int`, for every target space. -/
theorem s05_gcc_int_ord {U : Set ℂ} (hU : IsOpen U) (i : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : ℕ → ℝ × ℂ → E)
      (Gl : ℝ × ℂ → E),
      ((∀ᶠ n in atTop, ContDiffOn ℝ ∞ (G n) (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U)) ∧
        ContDiffOn ℝ ∞ Gl (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U) ∧
        ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (G n))
          (iteratedFDeriv ℝ i Gl) atTop (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U)) →
      TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ i (fun w => ∫ θ in (0 : ℝ)..1, G n (θ, w)))
        (iteratedFDeriv ℝ i (fun w => ∫ θ in (0 : ℝ)..1, Gl (θ, w))) atTop U := by
  have hP : IsOpen (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U) := isOpen_Ioo.prod hU
  induction i with
  | zero =>
    intro E _ _ G Gl hG
    obtain ⟨h1, h2, h3⟩ := hG
    have h0 := s05_gcc_c0 hU (h1.mono fun n hn => hn.continuousOn) h2.continuousOn
      (s04_tc_zero (h3 0))
    have hT := (continuousMultilinearCurryFin0 ℝ ℂ E).symm.isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn h0
    refine (hT.congr fun n y _ => ?_).congr_right fun y _ => ?_ <;>
      simp [iteratedFDeriv_zero_eq_comp]
  | succ i ih =>
    intro E _ _ G Gl hG
    obtain ⟨h1, h2, h3⟩ := hG
    have hd := s04_tc_clm hP
      ((ContinuousLinearMap.compL ℝ ℂ (ℝ × ℂ) E).flip (ContinuousLinearMap.inr ℝ ℝ ℂ))
      (s04_tc_fderiv hP ⟨h1, h2, h3⟩)
    have hI := ih (ℂ →L[ℝ] E) _ _ hd
    have hev := s04_tc_evcongr hI
      (h1.mono fun n hn => s04_tc_eqOn hU (fun w hw => (s05_gcc_hasfd hU hn hw).fderiv.symm) i)
      (s04_tc_eqOn hU (fun w hw => (s05_gcc_hasfd hU h2 hw).fderiv.symm) i)
    have hT := (continuousMultilinearCurryRightEquiv' ℝ i ℂ E).symm.isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn hev
    refine (hT.congr fun n y _ => ?_).congr_right fun y _ => ?_ <;>
      simp [iteratedFDeriv_succ_eq_comp_right]

/-- (c) phase 2, CC: `C^∞_loc` convergence passes to `θ`-integrals over `[0, 1]`
(`[0,1] × K` is a compact subset of `(-1/2, 3/2) × U`; differentiation under the integral). -/
theorem s05_gcc_int {U : Set ℂ} (hU : IsOpen U) {F : ℕ → ℝ × ℂ → ℝ} {FL : ℝ × ℂ → ℝ}
    (hF : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (F n) (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U)) ∧
      ContDiffOn ℝ ∞ FL (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U) ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (F n))
        (iteratedFDeriv ℝ i FL) atTop (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U)) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fun w => ∫ θ in (0 : ℝ)..1, F n (θ, w)) U) ∧
      ContDiffOn ℝ ∞ (fun w => ∫ θ in (0 : ℝ)..1, FL (θ, w)) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ i (fun w => ∫ θ in (0 : ℝ)..1, F n (θ, w)))
        (iteratedFDeriv ℝ i (fun w => ∫ θ in (0 : ℝ)..1, FL (θ, w))) atTop U := by
  obtain ⟨h1, h2, h3⟩ := hF
  exact ⟨h1.mono fun n hn => contDiffOn_infty.2 fun m => s05_gcc_smooth hU m ℝ (F n) hn,
    contDiffOn_infty.2 fun m => s05_gcc_smooth hU m ℝ FL h2,
    fun i => s05_gcc_int_ord hU i ℝ F FL ⟨h1, h2, h3⟩⟩

/-- (c) phase 2, CC helper: `C^∞_loc` convergence restricts to a subset. -/
theorem s05_gcc_mono {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] {W U : Set X} (hUW : U ⊆ W) {f : ℕ → X → Y} {fL : X → Y}
    (h : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) W) ∧ ContDiffOn ℝ ∞ fL W ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (f n))
        (iteratedFDeriv ℝ i fL) atTop W) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) U) ∧ ContDiffOn ℝ ∞ fL U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (f n))
        (iteratedFDeriv ℝ i fL) atTop U :=
  ⟨h.1.mono fun _ hn => hn.mono hUW, h.2.1.mono hUW, fun i => (h.2.2 i).mono hUW⟩

/-- (c) phase 2, CC helper: `C^∞_loc` convergence on `U` lifts to `(-1/2, 3/2) × U` through the
second coordinate. -/
theorem s05_gcc_snd {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {U : Set ℂ}
    (hU : IsOpen U) {f : ℕ → ℂ → X} {fL : ℂ → X}
    (h : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) U) ∧ ContDiffOn ℝ ∞ fL U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (f n))
        (iteratedFDeriv ℝ i fL) atTop U) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => f n p.2) (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U)) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => fL p.2) (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U) ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (fun p : ℝ × ℂ => f n p.2))
        (iteratedFDeriv ℝ i (fun p : ℝ × ℂ => fL p.2)) atTop (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U) :=
  s04_tc_comp (isOpen_Ioo.prod hU) hU h (s04_tc_const contDiffOn_snd)
    (Filter.Eventually.of_forall fun _ _ hp => hp.2) fun _ hp => hp.2

/-- (c) phase 2, CC helper: first and second derivatives of `a • f` for `f` smooth on an open
set. -/
theorem s05_gcc_dsmul {V : Set ℂ} (hV : IsOpen V) {f : ℂ → ℝ} (hf : ContDiffOn ℝ ∞ f V) (a : ℝ)
    {x : ℂ} (hx : x ∈ V) :
    fderiv ℝ (a • f) x = a • fderiv ℝ f x ∧
      fderiv ℝ (fderiv ℝ (a • f)) x = a • fderiv ℝ (fderiv ℝ f) x := by
  have hd : ∀ y ∈ V, fderiv ℝ (a • f) y = a • fderiv ℝ f y := fun y hy =>
    fderiv_const_smul ((hf.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hy)) a
  refine ⟨hd x hx, ?_⟩
  have hev : fderiv ℝ (a • f) =ᶠ[𝓝 x] fun y => a • fderiv ℝ f y :=
    Filter.mem_of_superset (hV.mem_nhds hx) fun y hy => hd y hy
  rw [hev.fderiv_eq]
  exact fderiv_const_smul
    (((hf.fderiv_of_isOpen (m := ∞) hV (by simp)).differentiableOn (by simp)).differentiableAt
      (hV.mem_nhds hx)) a

/-- (c) phase 2, CC helper: the scalar inequality behind `J_n ∈ O`. -/
theorem s05_gcc_ineq {m θ t l s : ℝ} (hm : 0 < m) (hθ : |θ| < 3 / 2) (ht : |t| < 1)
    (hl : m / 2 < l) (hs : 0 ≤ s) (hsm : s * Real.exp 2 < m ^ 2 / 4) :
    0 < l ∧ s * Real.exp (θ * t) < l ^ 2 * Real.cosh (θ * t) := by
  have hl0 : 0 < l := by linarith
  refine ⟨hl0, ?_⟩
  have h1 : θ * t ≤ 2 := by
    have h2 : |θ| * |t| ≤ 3 / 2 * 1 := mul_le_mul hθ.le ht.le (abs_nonneg _) (by norm_num)
    rw [← abs_mul] at h2
    linarith [le_abs_self (θ * t)]
  have h3 : s * Real.exp (θ * t) ≤ s * Real.exp 2 :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) hs
  have h4 : m ^ 2 / 4 < l ^ 2 := by nlinarith
  have h5 : l ^ 2 ≤ l ^ 2 * Real.cosh (θ * t) :=
    le_mul_of_one_le_right (by positivity) (Real.one_le_cosh _)
  linarith

/-- (c) phase 2, CC helper: the jet domain `O` is open. -/
theorem s05_gcc_isOpenO :
    IsOpen {J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) |
      0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1} := by
  show IsOpen
    ({J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) |
      0 < J.2.1} ∩
    {J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) |
      ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1})
  exact (isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt (by fun_prop) (by fun_prop))

/-- (c) phase 2, CC: in normalized coordinates the jets `J_n(θ, x)` of `θ t_n` (`t_n → 0` in
`C^∞_loc`, `s04_tg_slabconv`) eventually lie in `O` and converge to `J_L(x) = (0, λ_L, 0, Dλ_L, 0,
0, 0)` (flat limit), so `F ∘ J_n → F ∘ J_L` in `C^∞_loc` for every `F` smooth on `O`
(`s04_td_lambda`, `s04_td_q`, `s04_tc_fderiv`, `s04_tc_comp`). -/
theorem s05_gcc_jet {Ω' : ℕ → Set ℂ} {g : ℕ → ℂ → ℂ} {gL : ℂ → ℂ}
    (hg : ∀ n, IsConformalOnto (g n) unitDisc (Ω' n) ∧ g n 0 = 0)
    (hgL : IsConformalOnto gL unitDisc (gL '' unitDisc)) (hgL0 : gL 0 = 0)
    (hconv : TendstoLocallyUniformlyOn g gL atTop unitDisc)
    (hker : ∀ S : Set ℂ, IsCompact S → S ⊆ gL '' unitDisc → ∀ᶠ n in atTop, S ⊆ Ω' n)
    (hflat : ∀ x ∈ gL '' unitDisc, schwarzian (Function.invFunOn gL unitDisc) x = 0)
    {U V : Set ℂ} (hU : IsOpen U) (hUc : IsCompact (closure U)) (hV : IsOpen V)
    (hUV : closure U ⊆ V) (hVD : V ⊆ gL '' unitDisc) {t : ℕ → ℂ → ℝ}
    (ht : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (t n) V) ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (t n))
        (iteratedFDeriv ℝ i (fun _ : ℂ => (0 : ℝ))) atTop V)
    {F : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) → ℝ}
    (hF : ContDiffOn ℝ ∞ F
      {J | 0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1}) :
    (∀ᶠ n in atTop, ∀ p ∈ Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U,
      ((p.1 • t n) p.2, poincareDensity (Ω' n) p.2,
          schwarzian (Function.invFunOn (g n) unitDisc) p.2,
          fun i => fderiv ℝ (poincareDensity (Ω' n)) p.2 (frameVec i),
          fun i => fderiv ℝ (schwarzian (Function.invFunOn (g n) unitDisc)) p.2 (frameVec i),
          fun i => fderiv ℝ (p.1 • t n) p.2 (frameVec i),
          fun i j => fderiv ℝ (fderiv ℝ (p.1 • t n)) p.2 (frameVec i) (frameVec j)) ∈
        {J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) |
          0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1}) ∧
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fun p : ℝ × ℂ =>
        F ((p.1 • t n) p.2, poincareDensity (Ω' n) p.2,
          schwarzian (Function.invFunOn (g n) unitDisc) p.2,
          fun i => fderiv ℝ (poincareDensity (Ω' n)) p.2 (frameVec i),
          fun i => fderiv ℝ (schwarzian (Function.invFunOn (g n) unitDisc)) p.2 (frameVec i),
          fun i => fderiv ℝ (p.1 • t n) p.2 (frameVec i),
          fun i j => fderiv ℝ (fderiv ℝ (p.1 • t n)) p.2 (frameVec i) (frameVec j)))
        (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U)) ∧
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ =>
        F ((0 : ℝ), poincareDensity (gL '' unitDisc) p.2, (0 : ℂ),
          fun i => fderiv ℝ (poincareDensity (gL '' unitDisc)) p.2 (frameVec i),
          (0 : Fin 2 → ℂ), (0 : Fin 2 → ℝ), (0 : Fin 2 → Fin 2 → ℝ)))
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U) ∧
    ∀ i : ℕ, TendstoLocallyUniformlyOn
      (fun n => iteratedFDeriv ℝ i (fun p : ℝ × ℂ =>
        F ((p.1 • t n) p.2, poincareDensity (Ω' n) p.2,
          schwarzian (Function.invFunOn (g n) unitDisc) p.2,
          fun i => fderiv ℝ (poincareDensity (Ω' n)) p.2 (frameVec i),
          fun i => fderiv ℝ (schwarzian (Function.invFunOn (g n) unitDisc)) p.2 (frameVec i),
          fun i => fderiv ℝ (p.1 • t n) p.2 (frameVec i),
          fun i j => fderiv ℝ (fderiv ℝ (p.1 • t n)) p.2 (frameVec i) (frameVec j))))
      (iteratedFDeriv ℝ i (fun p : ℝ × ℂ =>
        F ((0 : ℝ), poincareDensity (gL '' unitDisc) p.2, (0 : ℂ),
          fun i => fderiv ℝ (poincareDensity (gL '' unitDisc)) p.2 (frameVec i),
          (0 : Fin 2 → ℂ), (0 : Fin 2 → ℝ), (0 : Fin 2 → Fin 2 → ℝ))))
      atTop (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U) := by
  have hP : IsOpen (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U) := isOpen_Ioo.prod hU
  obtain ⟨W, hW, hUW, hWV, hWc⟩ := exists_open_between_and_isCompact_closure hUc hV hUV
  have hWD : closure W ⊆ gL '' unitDisc := hWV.trans hVD
  have hUW' : U ⊆ W := subset_closure.trans hUW
  have hUV' : U ⊆ V := hUW'.trans (subset_closure.trans hWV)
  have ht' : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (t n) V) ∧ ContDiffOn ℝ ∞ (fun _ : ℂ => (0 : ℝ)) V ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (t n))
        (iteratedFDeriv ℝ i (fun _ : ℂ => (0 : ℝ))) atTop V := ⟨ht.1, contDiffOn_const, ht.2⟩
  have hl := s04_td_lambda hg hgL hgL0 hconv hker hW hWc hWD
  have hq := s04_td_q hg hgL hgL0 hconv hker hW hWc hWD
  have hlU := s05_gcc_mono hUW' hl
  have hqU := s05_gcc_mono hUW' hq
  have htU := s05_gcc_mono hUV' ht'
  have hDt := s04_tc_fderiv hU htU
  -- the seven components on `(-1/2, 3/2) × U`
  have cl := s05_gcc_snd hU hlU
  have cS := s05_gcc_snd hU hqU
  have cDl := s05_gcc_snd hU (s04_tc_clm hU
    (ContinuousLinearMap.pi fun i : Fin 2 => ContinuousLinearMap.apply ℝ ℝ (frameVec i))
    (s04_tc_fderiv hU hlU))
  have cDS := s05_gcc_snd hU (s04_tc_clm hU
    (ContinuousLinearMap.pi fun i : Fin 2 => ContinuousLinearMap.apply ℝ ℂ (frameVec i))
    (s04_tc_fderiv hU hqU))
  have cDt := s05_gcc_snd hU (s04_tc_clm hU
    (ContinuousLinearMap.pi fun i : Fin 2 => ContinuousLinearMap.apply ℝ ℝ (frameVec i)) hDt)
  have cDDt := s05_gcc_snd hU (s04_tc_clm hU
    (ContinuousLinearMap.pi fun i : Fin 2 => ContinuousLinearMap.pi fun j : Fin 2 =>
      (ContinuousLinearMap.apply ℝ ℝ (frameVec j)).comp
        (ContinuousLinearMap.apply ℝ (ℂ →L[ℝ] ℝ) (frameVec i)))
    (s04_tc_fderiv hU hDt))
  have cθ := s04_tc_const (U := Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U) (f := fun p : ℝ × ℂ => p.1)
    contDiffOn_fst
  have c1 := s04_tc_bilin hP (ContinuousLinearMap.mul ℝ ℝ) cθ (s05_gcc_snd hU htU)
  have c6 := s04_tc_bilin hP
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) cθ cDt
  have c7 := s04_tc_bilin hP
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ))
    cθ cDDt
  have hJ := s04_tc_pair hP c1 (s04_tc_pair hP cl (s04_tc_pair hP cS
    (s04_tc_pair hP cDl (s04_tc_pair hP cDS (s04_tc_pair hP c6 c7)))))
  -- the limit Schwarzian and its derivative vanish on `U`
  have hS0 : ∀ x ∈ U, schwarzian (Function.invFunOn gL unitDisc) x = 0 ∧
      fderiv ℝ (schwarzian (Function.invFunOn gL unitDisc)) x = 0 := by
    intro x hx
    have hWD' : W ⊆ gL '' unitDisc := subset_closure.trans hWD
    refine ⟨hflat x (hWD' (hUW' hx)), ?_⟩
    have hev : schwarzian (Function.invFunOn gL unitDisc) =ᶠ[𝓝 x] fun _ => (0 : ℂ) :=
      Filter.mem_of_superset (hW.mem_nhds (hUW' hx)) fun y hy => hflat y (hWD' hy)
    rw [hev.fderiv_eq]
    exact fderiv_const_apply _
  -- `J_n ∈ O` eventually, uniformly on `(-1/2, 3/2) × U`
  obtain ⟨m, hm, hmle⟩ := hUc.exists_forall_le' (hl.2.1.continuousOn.mono hUW) (a := 0)
    fun x hx => s02_poincareDensity_pos ⟨gL, hgL⟩ (hWD (subset_closure (hUW hx)))
  have ul := s04_tc_unif hW hl hUc hUW
  have uS := s04_tc_unif hW hq hUc hUW
  have ut := s04_tc_unif hV ht' hUc hUV
  rw [Metric.tendstoUniformlyOn_iff] at ul uS ut
  have hM : 0 < m ^ 2 / 4 / Real.exp 2 := by positivity
  have hmaps : ∀ᶠ n in atTop, MapsTo (fun p : ℝ × ℂ =>
      ((p.1 • t n) p.2, poincareDensity (Ω' n) p.2,
          schwarzian (Function.invFunOn (g n) unitDisc) p.2,
          fun i => fderiv ℝ (poincareDensity (Ω' n)) p.2 (frameVec i),
          fun i => fderiv ℝ (schwarzian (Function.invFunOn (g n) unitDisc)) p.2 (frameVec i),
          fun i => fderiv ℝ (p.1 • t n) p.2 (frameVec i),
          fun i j => fderiv ℝ (fderiv ℝ (p.1 • t n)) p.2 (frameVec i) (frameVec j)))
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U)
      {J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) |
        0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1} := by
    filter_upwards [ul (m / 2) (by positivity), uS _ hM, ut 1 one_pos] with n hln hSn htn
    intro p hp
    have hx : p.2 ∈ closure U := subset_closure hp.2
    have hxD : p.2 ∈ gL '' unitDisc := hWD (subset_closure (hUW hx))
    have e1 := hln p.2 hx
    have e2 := hSn p.2 hx
    have e3 := htn p.2 hx
    rw [hflat _ hxD, dist_zero_left] at e2
    have e3' : |t n p.2| < 1 := by simpa [Real.dist_eq] using e3
    have e1' : m / 2 < poincareDensity (Ω' n) p.2 := by
      have h0 := hmle p.2 hx
      rw [Real.dist_eq] at e1
      linarith [(abs_sub_lt_iff.1 e1).1]
    have hθ : |p.1| < 3 / 2 := abs_lt.2 ⟨by linarith [hp.1.1], hp.1.2⟩
    exact s05_gcc_ineq hm hθ e3' e1' (norm_nonneg _)
      ((lt_div_iff₀ (Real.exp_pos 2)).1 e2)
  have hmapsL : MapsTo (fun p : ℝ × ℂ =>
      ((0 : ℝ), poincareDensity (gL '' unitDisc) p.2, (0 : ℂ),
          fun i => fderiv ℝ (poincareDensity (gL '' unitDisc)) p.2 (frameVec i),
          (0 : Fin 2 → ℂ), (0 : Fin 2 → ℝ), (0 : Fin 2 → Fin 2 → ℝ)))
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U)
      {J : ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) |
        0 < J.2.1 ∧ ‖J.2.2.1‖ * Real.exp J.1 < J.2.1 ^ 2 * Real.cosh J.1} := by
    intro p hp
    have hl0 := s02_poincareDensity_pos ⟨gL, hgL⟩ (hVD (hUV' hp.2))
    refine ⟨hl0, ?_⟩
    simp only [norm_zero, zero_mul, Real.cosh_zero, mul_one]
    positivity
  refine ⟨hmaps, s04_tc_comp hP s05_gcc_isOpenO (s04_tc_const hF)
    (s04_tc_congr hP hJ ?_ ?_) hmaps hmapsL⟩
  · filter_upwards [ht.1] with n hn
    intro p hp
    obtain ⟨e1, e2⟩ := s05_gcc_dsmul hV hn p.1 (hUV' hp.2)
    simp only [e1, e2]
    rfl
  · intro p hp
    obtain ⟨h0, h1⟩ := hS0 p.2 hp.2
    simp only [h0, h1]
    simp
    exact ⟨rfl, (smul_zero p.1).symm, (smul_zero p.1).symm⟩

/-- (c) phase 2, seq helper: `Re(conj(c u) (c v)) = c² Re(conj u v)` for real `c`. -/
theorem s05_gcs_reconj (c : ℝ) (u v : ℂ) :
    (conj ((c : ℂ) * u) * ((c : ℂ) * v)).re = c ^ 2 * (conj u * v).re := by
  rw [map_mul, Complex.conj_ofReal,
    show (c : ℂ) * conj u * ((c : ℂ) * v) = ((c ^ 2 : ℝ) : ℂ) * (conj u * v) by push_cast; ring,
    Complex.re_ofReal_mul]

/-- (c) phase 2, seq helper: `a♭ - ρ` is real-homogeneous in each slot. -/
theorem s05_gcs_homA (Ω : Set ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (x : ℂ) (u : Fin 2 → ℂ)
    (i : Fin 2) (r : ℝ) :
    (lowerA Ω aUp - rhoMetricT Ω) x (Function.update u i ((r : ℂ) * u i)) =
      r * (lowerA Ω aUp - rhoMetricT Ω) x u := by
  have h1 : ∀ v w : ℂ, (conj ((r : ℂ) * v) * w).re = r * (conj v * w).re := fun v w => by
    rw [map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
  have h2 : ∀ v w : ℂ, (conj v * ((r : ℂ) * w)).re = r * (conj v * w).re := fun v w => by
    rw [mul_left_comm, Complex.re_ofReal_mul]
  fin_cases i <;>
    simp [lowerA, rhoMetricT, s04_tn_cvec, h2, Matrix.mulVec_smul] <;>
    ring

/-- (c) phase 2, seq helper: `b♭` is real-homogeneous. -/
theorem s05_gcs_homB (Ω : Set ℂ) (bUp : ℂ → Fin 2 → ℝ) (x : ℂ) (u : Fin 1 → ℂ) (i : Fin 1)
    (r : ℝ) : lowerB Ω bUp x (Function.update u i ((r : ℂ) * u i)) = r * lowerB Ω bUp x u := by
  obtain rfl : i = 0 := Subsingleton.elim i 0
  simp only [lowerB, Function.update_self, s04_tn_cvec, dotProduct_smul, smul_eq_mul]
  ring

/-- (c) phase 2, seq helper: the deviation norms at a point are invariant under a real similarity
`A z = c z + b`, the coefficients transforming as in `s05_gcn_ellOp` (`s04_tn_cj`). -/
theorem s05_gcs_tr {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {c : ℝ}
    (hc : 0 < c) (b : ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ)
    (cf : ℂ → ℝ) {x : ℂ} (hx : x ∈ Ω) :
    rhoCjNorm ((fun z => (c : ℂ) * z + b) '' Ω) 2
        (lowerA ((fun z => (c : ℂ) * z + b) '' Ω) (fun z => c ^ 2 • aUp ((z - b) / c)) -
          rhoMetricT ((fun z => (c : ℂ) * z + b) '' Ω)) {(c : ℂ) * x + b} +
      rhoCjNorm ((fun z => (c : ℂ) * z + b) '' Ω) 1
        (lowerB ((fun z => (c : ℂ) * z + b) '' Ω) (fun z => c • bUp ((z - b) / c)))
        {(c : ℂ) * x + b} +
      rhoCjNorm ((fun z => (c : ℂ) * z + b) '' Ω) 0
        (scalarField fun w => cf ((w - b) / c) - 2) {(c : ℂ) * x + b} =
    rhoCjNorm Ω 2 (lowerA Ω aUp - rhoMetricT Ω) {x} + rhoCjNorm Ω 1 (lowerB Ω bUp) {x} +
      rhoCjNorm Ω 0 (scalarField fun w => cf w - 2) {x} := by
  have hΩo : IsOpen Ω := by
    obtain ⟨f, hf⟩ := hΩ
    exact hf.isOpen isOpen_ball
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hA : ∀ y : ℂ, ((c : ℂ) * y + b - b) / c = y := fun y => by
    rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hc']
  have hl := fun y (hy : y ∈ Ω) => s04_tn_lambda hΩ hc b hy
  have hE : {x} ⊆ Ω := Set.singleton_subset_iff.2 hx
  have hrA : ∀ y ∈ Ω, ∀ u : Fin 2 → ℂ,
      (lowerA ((fun z => (c : ℂ) * z + b) '' Ω) (fun z => c ^ 2 • aUp ((z - b) / c)) -
          rhoMetricT ((fun z => (c : ℂ) * z + b) '' Ω)) ((c : ℂ) * y + b)
          (fun i => (c : ℂ) * u i) = (lowerA Ω aUp - rhoMetricT Ω) y u := by
    intro y hy u
    have hly : poincareDensity ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * y + b) =
        poincareDensity Ω y / c := eq_div_of_mul_eq hc.ne' (hl y hy).1
    simp only [Pi.sub_apply, lowerA, rhoMetricT, hA, hly, s04_tn_cvec, s05_gcs_reconj,
      Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    field_simp
  have hrB : ∀ y ∈ Ω, ∀ u : Fin 1 → ℂ,
      lowerB ((fun z => (c : ℂ) * z + b) '' Ω) (fun z => c • bUp ((z - b) / c))
          ((c : ℂ) * y + b) (fun i => (c : ℂ) * u i) = lowerB Ω bUp y u := by
    intro y hy u
    have hly : poincareDensity ((fun z => (c : ℂ) * z + b) '' Ω) ((c : ℂ) * y + b) =
        poincareDensity Ω y / c := eq_div_of_mul_eq hc.ne' (hl y hy).1
    simp only [lowerB, hA, hly, s04_tn_cvec, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    field_simp
  have hrC : ∀ y ∈ Ω, ∀ u : Fin 0 → ℂ,
      scalarField (fun w => cf ((w - b) / c) - 2) ((c : ℂ) * y + b) (fun i => (c : ℂ) * u i) =
        scalarField (fun w => cf w - 2) y u := fun y _ u => by
    simp only [scalarField, hA]
  have himg : (fun z => (c : ℂ) * z + b) '' {x} = {(c : ℂ) * x + b} := Set.image_singleton
  rw [← himg,
    s04_tn_cj hΩo hc hrA (fun y hy => (hl y hy).2) (fun y hy => (hl y hy).1)
      (s05_gcs_homA Ω aUp) 2 hE,
    s04_tn_cj hΩo hc hrB (fun y hy => (hl y hy).2) (fun y hy => (hl y hy).1)
      (s05_gcs_homB Ω bUp) 1 hE,
    s04_tn_cj hΩo hc hrC (fun y hy => (hl y hy).2) (fun y hy => (hl y hy).1)
      (fun _ _ i _ => i.elim0) 0 hE]

/-- (c) phase 2, seq helper: a representation of `𝓛` on `D` transports to `A(D)` with the
coefficients of `s05_gcn_ellOp`. -/
theorem s05_gcs_reptr {K : ℝ} {Ω Ωs D : Set ℂ} (hp : IsKQuasiPair Ω Ωs K) (hDΩ : D ⊆ Ω)
    {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {bUp : ℂ → Fin 2 → ℝ} {cf : ℂ → ℝ}
    (hrep : RepresentsOp Ω D (graphOp Ω Ωs) aUp bUp cf) {c : ℝ} (hc : 0 < c) (b : ℂ)
    (u : ℂ → ℝ) (hu : ContDiff ℝ ∞ u) {x : ℂ} (hx : x ∈ D) :
    graphOp ((fun z => (c : ℂ) * z + b) '' Ω) ((fun z => (c : ℂ) * z + b) '' Ωs) u
        ((c : ℂ) * x + b) =
      ellOp ((fun z => (c : ℂ) * z + b) '' Ω) (fun z => c ^ 2 • aUp ((z - b) / c))
        (fun z => c • bUp ((z - b) / c)) (fun z => cf ((z - b) / c)) u ((c : ℂ) * x + b) := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap (s03_b0_jordanPair hp)
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hv : ∀ z, u ((c : ℂ) * ((z - b) / c) + b) = u z := fun z => by
    rw [mul_div_cancel₀ _ hc', sub_add_cancel]
  have hvs : ContDiff ℝ ∞ (fun y => u ((c : ℂ) * y + b)) := hu.comp (by fun_prop)
  have h1 := s05_gcn_graphOp hp hc b (fun y => u ((c : ℂ) * y + b)) (hDΩ hx)
  have h2 := s05_gcn_ellOp ⟨f, hf⟩ hc b aUp bUp cf (fun y => u ((c : ℂ) * y + b)) (hDΩ hx)
  simp only [hv] at h1 h2
  rw [h1, h2]
  exact hrep.2 _ hvs.contDiffOn x hx

/-- (c) phase 2, seq helper: the image of a Jordan pair under `A z = c z + b` is a Jordan pair. -/
theorem s05_gcs_jordan {Ω Ωs : Set ℂ} (h : IsJordanPair Ω Ωs) {c : ℝ} (hc : 0 < c) (b : ℂ) :
    IsJordanPair ((fun z => (c : ℂ) * z + b) '' Ω) ((fun z => (c : ℂ) * z + b) '' Ωs) := by
  obtain ⟨F, h1, h2⟩ := h
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have he : ⇑(F.trans ((Homeomorph.mulLeft₀ (c : ℂ) hc').trans (Homeomorph.addRight b))) =
      (fun z => (c : ℂ) * z + b) ∘ F := by
    funext z
    rfl
  refine ⟨F.trans ((Homeomorph.mulLeft₀ (c : ℂ) hc').trans (Homeomorph.addRight b)), ?_, ?_⟩ <;>
    rw [he, Set.image_comp]
  · rw [h1]
  · rw [h2]

/-- (c) phase 2, seq helper: `A z = c z + b` is an open map. -/
theorem s05_gcs_openimg {c : ℝ} (hc : 0 < c) (b : ℂ) {s : Set ℂ} (hs : IsOpen s) :
    IsOpen ((fun z => (c : ℂ) * z + b) '' s) := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have he : ⇑((Homeomorph.mulLeft₀ (c : ℂ) hc').trans (Homeomorph.addRight b)) =
      fun z => (c : ℂ) * z + b := by
    funext z
    rfl
  have h := ((Homeomorph.mulLeft₀ (c : ℂ) hc').trans (Homeomorph.addRight b)).isOpenMap s hs
  rwa [he] at h

/-- (c) phase 2, seq helper: `θ`-averages of symmetric matrices are symmetric. -/
theorem s05_gcs_sym {T : Type} (Φ : T → Matrix (Fin 2) (Fin 2) ℝ) (hΦ : ∀ J, (Φ J)ᵀ = Φ J)
    (X : ℝ → T) :
    (Matrix.of fun i j => ∫ θ in (0 : ℝ)..1, Φ (X θ) i j)ᵀ =
      Matrix.of fun i j => ∫ θ in (0 : ℝ)..1, Φ (X θ) i j := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  congr 1
  funext θ
  rw [← Matrix.transpose_apply (Φ (X θ)) i j, hΦ]

/-- (c) phase 2, seq helper: a function smooth on `(-1/2, 3/2) × U` is integrable in `θ` over
`[0, 1]` at every `x ∈ U`. -/
theorem s05_gcs_ii {U : Set ℂ} {F : ℝ × ℂ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ U)) {x : ℂ} (hx : x ∈ U) :
    IntervalIntegrable (fun θ => F (θ, x)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le zero_le_one]
  exact ContinuousOn.comp (g := F) hF.continuousOn (Continuous.continuousOn (by fun_prop))
    fun θ hθ => ⟨⟨by linarith [hθ.1], by linarith [hθ.2]⟩, hx⟩

/-- (c) phase 2, gcs_lim helper: a `C^∞_loc` triple on `U` lifts to `U × (Fin k → ℂ)`
(composition with the first projection, `s04_tc_comp`). -/
theorem s05_gcsl_lift {U : Set ℂ} (hU : IsOpen U) (k : ℕ) {f : ℕ → ℂ → ℝ} {fL : ℂ → ℝ}
    (hf : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) U) ∧ ContDiffOn ℝ ∞ fL U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (f n))
        (iteratedFDeriv ℝ i fL) atTop U) :
    (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fun p : ℂ × (Fin k → ℂ) => f n p.1) (U ×ˢ univ)) ∧
      ContDiffOn ℝ ∞ (fun p : ℂ × (Fin k → ℂ) => fL p.1) (U ×ˢ univ) ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ i (fun p : ℂ × (Fin k → ℂ) => f n p.1))
        (iteratedFDeriv ℝ i (fun p : ℂ × (Fin k → ℂ) => fL p.1)) atTop (U ×ˢ univ) :=
  s04_tc_comp (hU.prod isOpen_univ) hU hf (s04_tc_const contDiffOn_fst)
    (Eventually.of_forall fun _ _ hp => hp.1) fun _ hp => hp.1

/-- (c) phase 2, gcs_lim helper: if a tensor field converges to `0` jointly on `U × (Fin k → ℂ)`
in `C^∞_loc`, its `C^j` norm at `0 ∈ U` is eventually below any `δ > 0` (`s04_tw_iter`,
`s04_tw_cj` on the compact `{0}`, `s04_tw_zero`). -/
theorem s05_gcsl_cj {Ω' : ℕ → Set ℂ} {ΩL U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U) {k : ℕ}
    {T : ℕ → TensorField k}
    (hT : (∀ᶠ n in atTop, ContDiffOn ℝ ∞
        (fun p : ℂ × (Fin k → ℂ) => T n p.1 p.2) (U ×ˢ univ)) ∧
      ContDiffOn ℝ ∞ (fun p : ℂ × (Fin k → ℂ) => (0 : TensorField k) p.1 p.2) (U ×ˢ univ) ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn
        (fun n => iteratedFDeriv ℝ i (fun p : ℂ × (Fin k → ℂ) => T n p.1 p.2))
        (iteratedFDeriv ℝ i (fun p : ℂ × (Fin k → ℂ) => (0 : TensorField k) p.1 p.2)) atTop
        (U ×ˢ univ))
    (hlam : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (poincareDensity (Ω' n)) U) ∧
      ContDiffOn ℝ ∞ (poincareDensity ΩL) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (poincareDensity (Ω' n)))
        (iteratedFDeriv ℝ i (poincareDensity ΩL)) atTop U)
    (hG : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (logDensityGrad (Ω' n)) U) ∧
      ContDiffOn ℝ ∞ (logDensityGrad ΩL) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (logDensityGrad (Ω' n)))
        (iteratedFDeriv ℝ i (logDensityGrad ΩL)) atTop U)
    (hpos : ∀ x ∈ U, 0 < poincareDensity ΩL x) (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, rhoCjNorm (Ω' n) j (T n) {0} ≤ ENNReal.ofReal δ := by
  refine s04_tw_cj hU isCompact_singleton (singleton_subset_iff.2 h0) (TL := 0)
    (fun i => s04_tw_iter hU hT hG i) hlam hpos j fun i _ x _ => ?_
  show Real.sqrt (∑ idx : Fin (k + i) → Fin 2,
      (rhoIterCovDeriv ΩL i (0 : TensorField k) x fun l => frameVec (idx l)) ^ 2) /
    poincareDensity ΩL x ^ (k + i) < δ
  simp only [s04_tw_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, Real.sqrt_zero, zero_div]
  exact hδ

/-- (c) phase 2, gcs_lim helper: `a♭ - ρ` in coordinates. -/
theorem s05_gcsl_eqA (Ω : Set ℂ) (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (x : ℂ) (v : Fin 2 → ℂ) :
    (lowerA Ω A - rhoMetricT Ω) x v =
      poincareDensity Ω x ^ 4 * ((v 0).re * (A x 0 0 * (v 1).re + A x 0 1 * (v 1).im) +
        (v 0).im * (A x 1 0 * (v 1).re + A x 1 1 * (v 1).im)) -
      poincareDensity Ω x ^ 2 * ((v 0).re * (v 1).re + (v 0).im * (v 1).im) := by
  show poincareDensity Ω x ^ 4 * (cvec (v 0) ⬝ᵥ (A x *ᵥ cvec (v 1))) -
    poincareDensity Ω x ^ 2 * (conj (v 0) * v 1).re = _
  simp [cvec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- (c) phase 2, gcs_lim helper: `b♭` in coordinates. -/
theorem s05_gcsl_eqB (Ω : Set ℂ) (B : ℂ → Fin 2 → ℝ) (x : ℂ) (v : Fin 1 → ℂ) :
    lowerB Ω B x v = poincareDensity Ω x ^ 2 * (B x 0 * (v 0).re + B x 1 * (v 0).im) := by
  show poincareDensity Ω x ^ 2 * (B x ⬝ᵥ cvec (v 0)) = _
  simp [cvec, dotProduct, Fin.sum_univ_two]

/-- (c) phase 2, seq helper (block A, frozen for w5): `C^∞_loc` convergence near `0` of the
coefficient fields to the model `(λ_L⁻² I, 0, 2)` makes the three deviation norms at `{0}`
eventually `≤ δ/3` (`s04_tw_iter`, `s04_tw_cj`, `s04_tw_zero`). -/
theorem s05_gcs_lim {Ω' : ℕ → Set ℂ} {ΩL U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    {A : ℕ → ℂ → Matrix (Fin 2) (Fin 2) ℝ} {B : ℕ → ℂ → Fin 2 → ℝ} {C : ℕ → ℂ → ℝ}
    (hlam : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (poincareDensity (Ω' n)) U) ∧
      ContDiffOn ℝ ∞ (poincareDensity ΩL) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (poincareDensity (Ω' n)))
        (iteratedFDeriv ℝ i (poincareDensity ΩL)) atTop U)
    (hG : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (logDensityGrad (Ω' n)) U) ∧
      ContDiffOn ℝ ∞ (logDensityGrad ΩL) U ∧
      ∀ i : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ i (logDensityGrad (Ω' n)))
        (iteratedFDeriv ℝ i (logDensityGrad ΩL)) atTop U)
    (hpos : ∀ x ∈ U, 0 < poincareDensity ΩL x)
    (hA : ∀ i j : Fin 2, (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fun x => A n x i j) U) ∧
      ContDiffOn ℝ ∞
        (fun x => ((poincareDensity ΩL x ^ 2)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j) U ∧
      ∀ l : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ l (fun x => A n x i j))
        (iteratedFDeriv ℝ l
          (fun x => ((poincareDensity ΩL x ^ 2)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j))
        atTop U)
    (hB : ∀ i : Fin 2, (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fun x => B n x i) U) ∧
      ContDiffOn ℝ ∞ (fun _ : ℂ => (0 : ℝ)) U ∧
      ∀ l : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ l (fun x => B n x i))
        (iteratedFDeriv ℝ l (fun _ : ℂ => (0 : ℝ))) atTop U)
    (hC : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (C n) U) ∧ ContDiffOn ℝ ∞ (fun _ : ℂ => (2 : ℝ)) U ∧
      ∀ l : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ l (C n))
        (iteratedFDeriv ℝ l (fun _ : ℂ => (2 : ℝ))) atTop U)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      rhoCjNorm (Ω' n) 2 (lowerA (Ω' n) (A n) - rhoMetricT (Ω' n)) {0} ≤ ENNReal.ofReal (δ / 3) ∧
        rhoCjNorm (Ω' n) 1 (lowerB (Ω' n) (B n)) {0} ≤ ENNReal.ofReal (δ / 3) ∧
        rhoCjNorm (Ω' n) 0 (scalarField fun x => C n x - 2) {0} ≤ ENNReal.ofReal (δ / 3) := by
  have hU2 : IsOpen (U ×ˢ (univ : Set (Fin 2 → ℂ))) := hU.prod isOpen_univ
  have hU1 : IsOpen (U ×ˢ (univ : Set (Fin 1 → ℂ))) := hU.prod isOpen_univ
  have hU0 : IsOpen (U ×ˢ (univ : Set (Fin 0 → ℂ))) := hU.prod isOpen_univ
  have hre : ContDiff ℝ ∞ Complex.re := Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ Complex.im := Complex.imCLM.contDiff
  have hδ3 : 0 < δ / 3 := by positivity
  -- `a♭ - ρ → 0`
  have hv2 := s04_tc_const (U := U ×ˢ (univ : Set (Fin 2 → ℂ)))
    (f := fun p : ℂ × (Fin 2 → ℂ) => p.2) contDiffOn_snd
  have hinA := s04_tc_pair hU2 (s05_gcsl_lift hU 2 hlam) (s04_tc_pair hU2
    (s05_gcsl_lift hU 2 (hA 0 0)) (s04_tc_pair hU2 (s05_gcsl_lift hU 2 (hA 0 1))
      (s04_tc_pair hU2 (s05_gcsl_lift hU 2 (hA 1 0))
        (s04_tc_pair hU2 (s05_gcsl_lift hU 2 (hA 1 1)) hv2))))
  have hΨA : ContDiff ℝ ∞ (fun x : ℝ × ℝ × ℝ × ℝ × ℝ × (Fin 2 → ℂ) =>
      x.1 ^ 4 * ((x.2.2.2.2.2 0).re * (x.2.1 * (x.2.2.2.2.2 1).re +
        x.2.2.1 * (x.2.2.2.2.2 1).im) + (x.2.2.2.2.2 0).im * (x.2.2.2.1 * (x.2.2.2.2.2 1).re +
          x.2.2.2.2.1 * (x.2.2.2.2.2 1).im)) -
        x.1 ^ 2 * ((x.2.2.2.2.2 0).re * (x.2.2.2.2.2 1).re +
          (x.2.2.2.2.2 0).im * (x.2.2.2.2.2 1).im)) := by
    fun_prop
  have hTA := s04_tc_congr hU2 (s04_tc_comp hU2 isOpen_univ (s04_tc_const hΨA.contDiffOn) hinA
      (Eventually.of_forall fun _ _ _ => mem_univ _) fun _ _ => mem_univ _)
    (f := fun n p => (lowerA (Ω' n) (A n) - rhoMetricT (Ω' n)) p.1 p.2)
    (fL := fun p => (0 : TensorField 2) p.1 p.2)
    (Eventually.of_forall fun n p _ => s05_gcsl_eqA (Ω' n) (A n) p.1 p.2) fun p hp => by
      have hl := (hpos p.1 hp.1).ne'
      show (0 : ℝ) = _
      simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      simp
      field_simp
      ring
  -- `b♭ → 0`
  have hv1 := s04_tc_const (U := U ×ˢ (univ : Set (Fin 1 → ℂ)))
    (f := fun p : ℂ × (Fin 1 → ℂ) => p.2) contDiffOn_snd
  have hinB := s04_tc_pair hU1 (s05_gcsl_lift hU 1 hlam) (s04_tc_pair hU1
    (s05_gcsl_lift hU 1 (hB 0)) (s04_tc_pair hU1 (s05_gcsl_lift hU 1 (hB 1)) hv1))
  have hΨB : ContDiff ℝ ∞ (fun x : ℝ × ℝ × ℝ × (Fin 1 → ℂ) =>
      x.1 ^ 2 * (x.2.1 * (x.2.2.2 0).re + x.2.2.1 * (x.2.2.2 0).im)) := by
    fun_prop
  have hTB := s04_tc_congr hU1 (s04_tc_comp hU1 isOpen_univ (s04_tc_const hΨB.contDiffOn) hinB
      (Eventually.of_forall fun _ _ _ => mem_univ _) fun _ _ => mem_univ _)
    (f := fun n p => lowerB (Ω' n) (B n) p.1 p.2)
    (fL := fun p => (0 : TensorField 1) p.1 p.2)
    (Eventually.of_forall fun n p _ => s05_gcsl_eqB (Ω' n) (B n) p.1 p.2) fun p _ => by
      show (0 : ℝ) = _
      simp
  -- `c - 2 → 0`
  have hΨC : ContDiff ℝ ∞ (fun x : ℝ => x - 2) := contDiff_id.sub contDiff_const
  have hTC := s04_tc_congr hU0 (s04_tc_comp hU0 isOpen_univ (s04_tc_const hΨC.contDiffOn)
      (s05_gcsl_lift hU 0 hC) (Eventually.of_forall fun _ _ _ => mem_univ _)
      fun _ _ => mem_univ _)
    (f := fun n p => scalarField (fun x => C n x - 2) p.1 p.2)
    (fL := fun p => (0 : TensorField 0) p.1 p.2)
    (Eventually.of_forall fun n p _ => rfl) fun p _ => by
      show (0 : ℝ) = 2 - 2
      ring
  filter_upwards [s05_gcsl_cj hU h0 (T := fun n => lowerA (Ω' n) (A n) - rhoMetricT (Ω' n)) hTA
      hlam hG hpos 2 hδ3, s05_gcsl_cj hU h0 (T := fun n => lowerB (Ω' n) (B n)) hTB hlam hG hpos
      1 hδ3, s05_gcsl_cj hU h0 (T := fun n => scalarField fun x => C n x - 2) hTC hlam hG hpos 0
      hδ3] with n h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- (c) phase 2, seq helper: the normalized core.  Along a normalized sequence (`s04_tg_seq`) with
flat limit (`s04_tp_flat`), the deviation norms at `w n` are eventually `≤ δ`: near `0` every
representation agrees with the `θ`-averaged universal coefficients of `s05_ml_rep`
(`s05_gc_unique`), which converge to the model `(λ_L⁻² I, 0, 2)` (`s05_gcc_jet`, `s05_gcc_int`,
`s05_gcm_model`). -/
theorem s05_gcs_norm {K : ℝ} {Ω Ωs : ℕ → Set ℂ} {w : ℕ → ℂ} {η R : ℕ → ℝ}
    (hpair : ∀ n, IsKQuasiPair (Ω n) (Ωs n) K) (hnl : ∀ n, ¬ IsLinePair (Ω n) (Ωs n))
    (hgood : ∀ n, w n ∈ goodSet (Ω n) (Ωs n) (η n) (R n))
    (hη : Tendsto η atTop (𝓝 0)) (hR : Tendsto R atTop atTop)
    {aUp : ℕ → ℂ → Matrix (Fin 2) (Fin 2) ℝ} {bUp : ℕ → ℂ → Fin 2 → ℝ} {cf : ℕ → ℂ → ℝ}
    (hrep : ∀ n, RepresentsOp (Ω n) (goodSet (Ω n) (Ωs n) (η n) (R n)) (graphOp (Ω n) (Ωs n))
      (aUp n) (bUp n) (cf n))
    {c : ℕ → ℝ} {b : ℕ → ℂ} {y₁ : ℂ} {g gs : ℕ → ℂ → ℂ} {gL gsL : ℂ → ℂ} {α β : ℂ}
    (hcb : ∀ n, 0 < c n ∧ (c n : ℂ) * w n + b n = 0)
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
    (hflat : ∀ x ∈ gL '' unitDisc, schwarzian (Function.invFunOn gL unitDisc) x = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      rhoCjNorm (Ω n) 2 (lowerA (Ω n) (aUp n) - rhoMetricT (Ω n)) {w n} +
          rhoCjNorm (Ω n) 1 (lowerB (Ω n) (bUp n)) {w n} +
          rhoCjNorm (Ω n) 0 (scalarField fun x => cf n x - 2) {w n} ≤ ENNReal.ofReal δ := by
  obtain ⟨Φa, Φb, Φc, hΦa, hΦb, hΦc, hΦs, hΦ⟩ := s05_ml_rep
  -- the balls `U = B(0, r/3) ⋐ V = B(0, r/2) ⋐ D_L`
  have hDo : IsOpen (gL '' unitDisc) := by
    rw [hD]
    exact isOpen_lt continuous_const (by fun_prop)
  obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.1 hDo 0 ⟨0, by simp [unitDisc], hgL0⟩
  have hUcl : closure (ball (0 : ℂ) (r / 3)) = closedBall 0 (r / 3) :=
    closure_ball 0 (by positivity)
  have hVcl : closure (ball (0 : ℂ) (r / 2)) = closedBall 0 (r / 2) :=
    closure_ball 0 (by positivity)
  have hUc : IsCompact (closure (ball (0 : ℂ) (r / 3))) := by
    rw [hUcl]
    exact isCompact_closedBall 0 _
  have hVc : IsCompact (closure (ball (0 : ℂ) (r / 2))) := by
    rw [hVcl]
    exact isCompact_closedBall 0 _
  have hUV : closure (ball (0 : ℂ) (r / 3)) ⊆ ball 0 (r / 2) := by
    rw [hUcl]
    exact closedBall_subset_ball (by linarith)
  have hVD' : closure (ball (0 : ℂ) (r / 2)) ⊆ gL '' unitDisc := by
    rw [hVcl]
    exact (closedBall_subset_ball (by linarith)).trans hrD
  have hVD : ball (0 : ℂ) (r / 2) ⊆ gL '' unitDisc := subset_closure.trans hVD'
  have hUD : closure (ball (0 : ℂ) (r / 3)) ⊆ gL '' unitDisc := hUV.trans hVD
  have h0U : (0 : ℂ) ∈ ball (0 : ℂ) (r / 3) := mem_ball_self (by positivity)
  have hpos : ∀ x ∈ ball (0 : ℂ) (r / 3), 0 < poincareDensity (gL '' unitDisc) x :=
    fun x hx => s02_poincareDensity_pos ⟨gL, hgL⟩ (hUD (subset_closure hx))
  -- `t_n → 0` on `V`; the jets and the averaged coefficients
  have hsl := s04_tg_slabconv hpair hnl (fun n => (hcb n).1) hg hgL hgL0 hconv hker hgs hgsL
    hgsL0 hsconv hsker hα hD hDs isOpen_ball hVc hVD'
  have ht := And.intro hsl.1 hsl.2.2
  have hjA := fun i j => s05_gcc_jet hg hgL hgL0 hconv hker hflat isOpen_ball hUc isOpen_ball hUV
    hVD ht (hΦa i j)
  have hjB := fun i => s05_gcc_jet hg hgL hgL0 hconv hker hflat isOpen_ball hUc isOpen_ball hUV
    hVD ht (hΦb i)
  have hjC := s05_gcc_jet hg hgL hgL0 hconv hker hflat isOpen_ball hUc isOpen_ball hUV hVD ht hΦc
  let Jn : ℕ → ℝ × ℂ → ℝ × ℝ × ℂ × (Fin 2 → ℝ) × (Fin 2 → ℂ) × (Fin 2 → ℝ) ×
      (Fin 2 → Fin 2 → ℝ) := fun n p =>
    ((p.1 • slabTop ((fun z => (c n : ℂ) * z + b n) '' Ω n)
        ((fun z => (c n : ℂ) * z + b n) '' Ωs n)) p.2,
      poincareDensity ((fun z => (c n : ℂ) * z + b n) '' Ω n) p.2,
      schwarzian (Function.invFunOn (g n) unitDisc) p.2,
      fun i => fderiv ℝ (poincareDensity ((fun z => (c n : ℂ) * z + b n) '' Ω n)) p.2
        (frameVec i),
      fun i => fderiv ℝ (schwarzian (Function.invFunOn (g n) unitDisc)) p.2 (frameVec i),
      fun i => fderiv ℝ (p.1 • slabTop ((fun z => (c n : ℂ) * z + b n) '' Ω n)
        ((fun z => (c n : ℂ) * z + b n) '' Ωs n)) p.2 (frameVec i),
      fun i j => fderiv ℝ (fderiv ℝ (p.1 • slabTop ((fun z => (c n : ℂ) * z + b n) '' Ω n)
        ((fun z => (c n : ℂ) * z + b n) '' Ωs n))) p.2 (frameVec i) (frameVec j))
  let Aco : ℕ → ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun n y =>
    Matrix.of fun i j => ∫ θ in (0 : ℝ)..1, Φa (Jn n (θ, y)) i j
  let Bco : ℕ → ℂ → Fin 2 → ℝ := fun n y i => ∫ θ in (0 : ℝ)..1, Φb (Jn n (θ, y)) i
  let Cco : ℕ → ℂ → ℝ := fun n y => ∫ θ in (0 : ℝ)..1, Φc (Jn n (θ, y))
  -- the model limits
  have hm := fun x (hx : x ∈ gL '' unitDisc) => s05_gcm_model hΦs hΦ hα (x := x)
    (by rw [hD] at hx; exact hx)
  rw [← hD] at hm
  have hcA : ∀ i j : Fin 2,
      (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fun x => Aco n x i j) (ball 0 (r / 3))) ∧
      ContDiffOn ℝ ∞ (fun x => ((poincareDensity (gL '' unitDisc) x ^ 2)⁻¹ •
        (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j) (ball 0 (r / 3)) ∧
      ∀ l : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ l (fun x => Aco n x i j))
        (iteratedFDeriv ℝ l (fun x => ((poincareDensity (gL '' unitDisc) x ^ 2)⁻¹ •
          (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j)) atTop (ball 0 (r / 3)) := fun i j =>
    s04_tc_congr isOpen_ball (s05_gcc_int isOpen_ball (hjA i j).2)
      (Filter.Eventually.of_forall fun n x _ => rfl) fun x hx => by
        simp only [intervalIntegral.integral_const, sub_zero, one_smul,
          (hm x (hUD (subset_closure hx))).1]
  have hcB : ∀ i : Fin 2,
      (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fun x => Bco n x i) (ball 0 (r / 3))) ∧
      ContDiffOn ℝ ∞ (fun _ : ℂ => (0 : ℝ)) (ball 0 (r / 3)) ∧
      ∀ l : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ l (fun x => Bco n x i))
        (iteratedFDeriv ℝ l (fun _ : ℂ => (0 : ℝ))) atTop (ball 0 (r / 3)) := fun i =>
    s04_tc_congr isOpen_ball (s05_gcc_int isOpen_ball (hjB i).2)
      (Filter.Eventually.of_forall fun n x _ => rfl) fun x hx => by
        simp only [intervalIntegral.integral_const, sub_zero, one_smul,
          (hm x (hUD (subset_closure hx))).2.1, Pi.zero_apply]
  have hcC : (∀ᶠ n in atTop, ContDiffOn ℝ ∞ (Cco n) (ball 0 (r / 3))) ∧
      ContDiffOn ℝ ∞ (fun _ : ℂ => (2 : ℝ)) (ball 0 (r / 3)) ∧
      ∀ l : ℕ, TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℝ l (Cco n))
        (iteratedFDeriv ℝ l (fun _ : ℂ => (2 : ℝ))) atTop (ball 0 (r / 3)) :=
    s04_tc_congr isOpen_ball (s05_gcc_int isOpen_ball hjC.2)
      (Filter.Eventually.of_forall fun n x _ => rfl) fun x hx => by
        simp only [intervalIntegral.integral_const, sub_zero, one_smul,
          (hm x (hUD (subset_closure hx))).2.2]
  have hlim := s05_gcs_lim isOpen_ball h0U
    (s04_td_lambda hg hgL hgL0 hconv hker isOpen_ball hUc hUD)
    (s04_td_grad hg hgL hgL0 hconv hker isOpen_ball hUc hUD) hpos hcA hcB hcC hδ
  -- eventually: the representation near `0` and the identification of the coefficients
  have eA : ∀ᶠ n in atTop, ∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => Φa (Jn n p) i j)
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ ball 0 (r / 3)) :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hjA i j).2.1
  have eB : ∀ᶠ n in atTop, ∀ i : Fin 2, ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => Φb (Jn n p) i)
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ ball 0 (r / 3)) :=
    Filter.eventually_all.2 fun i => (hjB i).2.1
  have eC : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => Φc (Jn n p))
      (Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ ball 0 (r / 3)) := hjC.2.1
  filter_upwards [hjC.1, eA, eB, eC, ht.1, hη.eventually (gt_mem_nhds one_pos),
    hR.eventually_ge_atTop 0, hlim] with n hO hFa hFb hFc htn hηn hRn hl
  obtain ⟨hcn, hcw⟩ := hcb n
  have hc' : (c n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hcn.ne'
  have hAy : ∀ y : ℂ, ((c n : ℂ) * y + b n - b n) / c n = y := fun y => by
    rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hc']
  have hΩn := s02_jordanPair_riemannMap (s03_b0_jordanPair (hpair n))
  set N : Set ℂ := ((fun z => (c n : ℂ) * z + b n) '' goodSet (Ω n) (Ωs n) (η n) (R n)) ∩
    ball 0 (r / 3) with hN
  have hNo : IsOpen N :=
    (s05_gcs_openimg hcn (b n) (s04_sl_good_open (hpair n) (η n) (R n))).inter isOpen_ball
  have h0N : (0 : ℂ) ∈ N := ⟨⟨w n, hgood n, hcw⟩, h0U⟩
  have hNU : N ⊆ ball (0 : ℂ) (r / 3) := inter_subset_right
  have hNΩ : N ⊆ (fun z => (c n : ℂ) * z + b n) '' Ω n :=
    fun z hz => by
      obtain ⟨⟨y, hy, rfl⟩, -⟩ := hz
      exact ⟨y, hy.1, rfl⟩
  have hNs : ∀ z ∈ N, schwarzNorm ((fun z => (c n : ℂ) * z + b n) '' Ω n) z < 1 := by
    rintro z ⟨⟨y, hy, rfl⟩, -⟩
    rw [(subsec_poincare_natural_affine hΩn hc' hy.1).2]
    have h1 : coshDist (epstein (Ω n) y) (epstein (Ω n) y) = 1 := by simp [coshDist]
    have h2 : hdist (epstein (Ω n) y) (epstein (Ω n) y) = 0 := by
      simp only [hdist, h1, Real.arcosh_zero]
    exact ((s04_tb_good_s (hpair n) hy).1 y hy.1 (by rw [h2]; exact hRn)).trans hηn
  have hrepn : ∀ u : ℂ → ℝ, ContDiff ℝ ∞ u → ∀ x ∈ N,
      graphOp ((fun z => (c n : ℂ) * z + b n) '' Ω n) ((fun z => (c n : ℂ) * z + b n) '' Ωs n)
          u x =
        ellOp ((fun z => (c n : ℂ) * z + b n) '' Ω n) (Aco n) (Bco n) (Cco n) u x := by
    intro u hu x hx
    have hxU : x ∈ ball (0 : ℂ) (r / 3) := hNU hx
    unfold graphOp
    refine (intervalIntegral.integral_congr fun θ hθ => ?_).trans
      (s05_gb_ellOp_integral _ (a := fun p => Φa (Jn n p)) (b := fun p => Φb (Jn n p))
        (c := fun p => Φc (Jn n p)) u (fun i j => s05_gcs_ii (hFa i j) hxU)
        (fun i => s05_gcs_ii (hFb i) hxU) (s05_gcs_ii hFc hxU))
    rw [Set.uIcc_of_le zero_le_one] at hθ
    exact hΦ _ _ (s05_gcs_jordan (s03_b0_jordanPair (hpair n)) hcn (b n)) (g n) (hg n).1 N hNo
      hNΩ hNs (θ • slabTop ((fun z => (c n : ℂ) * z + b n) '' Ω n)
        ((fun z => (c n : ℂ) * z + b n) '' Ωs n)) u
      (((htn.mono (hNU.trans (subset_closure.trans hUV))).const_smul θ).of_le (by simp))
      (hu.contDiffOn.of_le (by simp)) x hx
      (hO (θ, x) ⟨⟨by linarith [hθ.1], by linarith [hθ.2]⟩, hxU⟩)
  have hid : ∀ z ∈ N, c n ^ 2 • aUp n ((z - b n) / c n) = Aco n z ∧
      c n • bUp n ((z - b n) / c n) = Bco n z ∧ cf n ((z - b n) / c n) = Cco n z :=
    s05_gc_unique (D := N) (a := fun z => c n ^ 2 • aUp n ((z - b n) / c n)) (a' := Aco n)
      (b := fun z => c n • bUp n ((z - b n) / c n)) (b' := Bco n)
      (c := fun z => cf n ((z - b n) / c n)) (c' := Cco n)
      (fun z hz => by
        obtain ⟨⟨y, hy, rfl⟩, -⟩ := hz
        simp only [Matrix.transpose_smul, hAy, (hrep n).1.2.2.2 y hy])
      (fun z _ => s05_gcs_sym Φa hΦs _)
      (fun u hu z hz => by
        have hz' := hz.1
        obtain ⟨y, hy, rfl⟩ := hz'
        exact (s05_gcs_reptr (hpair n)
          (fun y (h : y ∈ goodSet (Ω n) (Ωs n) (η n) (R n)) => h.1) (hrep n) hcn (b n) u hu hy).symm.trans
          (hrepn u hu _ hz))
  have hsub : {(0 : ℂ)} ⊆ N := singleton_subset_iff.2 h0N
  have htr := s05_gcs_tr hΩn hcn (b n) (aUp n) (bUp n) (cf n) (hgood n).1
  rw [hcw] at htr
  rw [← htr]
  refine le_trans (add_le_add (add_le_add
    ((s04_tg_cjlocal _ hNo hsub ?_ 2).trans_le hl.1)
    ((s04_tg_cjlocal _ hNo hsub ?_ 1).trans_le hl.2.1))
    ((s04_tg_cjlocal _ hNo hsub ?_ 0).trans_le hl.2.2)) (le_of_eq ?_)
  · intro z hz v
    simp only [Pi.sub_apply, lowerA, (hid z hz).1]
  · intro z hz v
    simp only [lowerB, (hid z hz).2.1]
  · intro z hz v
    simp only [scalarField, (hid z hz).2.2]
  · rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring

/-- (c) phase 2, sequence form of the core: along `(η n, R n)`-good points `w n` with `η n → 0`,
`R n → ∞`, for every representation of `𝓛_n` on `G₀(η n, R n)`, the deviation norms at `w n`
tend to `0`. -/
theorem s05_gcs_seq {K : ℝ} (hK : 1 ≤ K) {Ω Ωs : ℕ → Set ℂ} {w : ℕ → ℂ} {η R : ℕ → ℝ}
    (hpair : ∀ n, IsKQuasiPair (Ω n) (Ωs n) K) (hnl : ∀ n, ¬ IsLinePair (Ω n) (Ωs n))
    (hgood : ∀ n, w n ∈ goodSet (Ω n) (Ωs n) (η n) (R n))
    (hη : Tendsto η atTop (𝓝 0)) (hR : Tendsto R atTop atTop)
    {aUp : ℕ → ℂ → Matrix (Fin 2) (Fin 2) ℝ} {bUp : ℕ → ℂ → Fin 2 → ℝ} {c : ℕ → ℂ → ℝ}
    (hrep : ∀ n, RepresentsOp (Ω n) (goodSet (Ω n) (Ωs n) (η n) (R n)) (graphOp (Ω n) (Ωs n))
      (aUp n) (bUp n) (c n))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      rhoCjNorm (Ω n) 2 (lowerA (Ω n) (aUp n) - rhoMetricT (Ω n)) {w n} +
          rhoCjNorm (Ω n) 1 (lowerB (Ω n) (bUp n)) {w n} +
          rhoCjNorm (Ω n) 0 (scalarField fun x => c n x - 2) {w n} ≤ ENNReal.ofReal δ := by
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨ψ, hψ, hψP⟩ := Filter.extraction_of_frequently_atTop hcon
  have hη' : Tendsto (fun n => η (ψ n)) atTop (𝓝 0) := hη.comp hψ.tendsto_atTop
  have hR' : Tendsto (fun n => R (ψ n)) atTop atTop := hR.comp hψ.tendsto_atTop
  obtain ⟨φ, hφ, cc, bb, y₁, g, gs, gL, gsL, α, β, hcb, hg, hgL, hgL0, hconv, hker, hgs, hgsL,
    hgsL0, hsconv, hsker, hα, hD, hDs⟩ :=
    s04_tg_seq hK (fun n => hpair (ψ n)) (fun n => hnl (ψ n)) (fun n => hgood (ψ n)) hη' hR'
  have hflat := s04_tp_flat hK (fun n => hpair (ψ n)) (fun n => hnl (ψ n))
    (fun n => hgood (ψ n)) hη' hR' hφ hcb hg hgL hconv
  obtain ⟨n, hn⟩ := (s05_gcs_norm (Ω := fun n => Ω (ψ (φ n))) (Ωs := fun n => Ωs (ψ (φ n)))
    (w := fun n => w (ψ (φ n))) (η := fun n => η (ψ (φ n))) (R := fun n => R (ψ (φ n)))
    (fun n => hpair (ψ (φ n))) (fun n => hnl (ψ (φ n))) (fun n => hgood (ψ (φ n)))
    (hη'.comp hφ.tendsto_atTop) (hR'.comp hφ.tendsto_atTop) (fun n => hrep (ψ (φ n))) hcb hg
    hgL hgL0 hconv hker hgs hgsL hgsL0 hsconv hsker hα hD hDs hflat hδ).exists
  exact hψP (φ n) hn

/-- CS helper: `rhoCjNorm` on `E` is bounded by any common bound of its values on the singletons
`{w}`, `w ∈ E` (it is a pointwise supremum). -/
theorem s05_gcx_le_pt {Ω E : Set ℂ} {k : ℕ} (j : ℕ) (T : TensorField k) {x : ℝ≥0∞}
    (h : ∀ w ∈ E, rhoCjNorm Ω j T {w} ≤ x) : rhoCjNorm Ω j T E ≤ x := by
  unfold rhoCjNorm at h ⊢
  refine iSup_le fun i => iSup_le fun hi => iSup_le fun w => iSup_le fun hw => ?_
  refine le_trans ?_ (h w hw)
  exact le_iSup_of_le i (le_iSup_of_le hi (le_iSup_of_le w (le_iSup_of_le (mem_singleton w) le_rfl)))

/-- CS helper: if a sum of three `rhoCjNorm`s on `E` exceeds `δ`, then the same sum on some
singleton `{w}`, `w ∈ E`, exceeds `δ / 3`. -/
theorem s05_gcx_pick {Ω E : Set ℂ} {k₁ k₂ k₃ : ℕ} (j₁ j₂ j₃ : ℕ) (T₁ : TensorField k₁)
    (T₂ : TensorField k₂) (T₃ : TensorField k₃) {δ : ℝ} (hδ : 0 < δ)
    (h : ENNReal.ofReal δ < rhoCjNorm Ω j₁ T₁ E + rhoCjNorm Ω j₂ T₂ E + rhoCjNorm Ω j₃ T₃ E) :
    ∃ w ∈ E, ENNReal.ofReal (δ / 3) <
      rhoCjNorm Ω j₁ T₁ {w} + rhoCjNorm Ω j₂ T₂ {w} + rhoCjNorm Ω j₃ T₃ {w} := by
  by_contra hc
  push Not at hc
  have h1 : rhoCjNorm Ω j₁ T₁ E ≤ ENNReal.ofReal (δ / 3) :=
    s05_gcx_le_pt j₁ T₁ fun w hw => le_trans (le_trans le_self_add le_self_add) (hc w hw)
  have h2 : rhoCjNorm Ω j₂ T₂ E ≤ ENNReal.ofReal (δ / 3) :=
    s05_gcx_le_pt j₂ T₂ fun w hw => le_trans (le_trans le_add_self le_self_add) (hc w hw)
  have h3 : rhoCjNorm Ω j₃ T₃ E ≤ ENNReal.ofReal (δ / 3) :=
    s05_gcx_le_pt j₃ T₃ fun w hw => le_trans le_add_self (hc w hw)
  have heq : ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) =
      ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  exact absurd h (not_lt.2 (le_trans (add_le_add (add_le_add h1 h2) h3) heq.le))

/-- (c) core (phase 2, compactness route; SCOUT_w1_C §2 CS/CN/CC/CM): for every `δ > 0`, on
`G₀(η, R)` with `η` small and `R` large, every representation of `𝓛` has
`‖a♭ - ρ‖_{C²} + ‖b♭‖_{C¹} + ‖c - 2‖_{C⁰} ≤ δ`. -/
theorem s05_gc_core : ∀ K : ℝ, 1 ≤ K → ∀ δ : ℝ, 0 < δ →
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ R₁ : ℝ, ∀ η R : ℝ, 0 < η → η ≤ η₀ → R₁ ≤ R →
      ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
        ∀ (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
          RepresentsOp Ω (goodSet Ω Ωs η R) (graphOp Ω Ωs) aUp bUp c →
            rhoCjNorm Ω 2 (lowerA Ω aUp - rhoMetricT Ω) (goodSet Ω Ωs η R) +
                rhoCjNorm Ω 1 (lowerB Ω bUp) (goodSet Ω Ωs η R) +
                rhoCjNorm Ω 0 (scalarField fun w => c w - 2) (goodSet Ω Ωs η R) ≤
              ENNReal.ofReal δ := by
  intro K hK δ hδ
  by_contra hcon
  push Not at hcon
  -- a counterexample sequence along `η₀ = 1/(n+1)`, `R₁ = n`
  have hseq := fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity) (n : ℝ)
  choose η R hη0 hη1 hR1 Ω Ωs hpair hnl aUp bUp c hrep hgt using hseq
  -- a single point of `G₀` carrying a third of the excess
  have hpt := fun n : ℕ => s05_gcx_pick 2 1 0 (lowerA (Ω n) (aUp n) - rhoMetricT (Ω n))
    (lowerB (Ω n) (bUp n)) (scalarField fun x => c n x - 2) hδ (hgt n)
  choose w hwg hwgt using hpt
  have hη : Tendsto η atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (hη0 n).le) hη1
  have hR : Tendsto R atTop atTop := tendsto_atTop_mono hR1 tendsto_natCast_atTop_atTop
  obtain ⟨n, hn⟩ :=
    (s05_gcs_seq hK hpair hnl hwg hη hR hrep (δ := δ / 3) (by positivity)).exists
  exact absurd hn (not_le.2 (hwgt n))

/-- GO-c: Lemma 5.7 (c) uniformly, for the chosen coefficients on every open `D ⊆ G₀` (needs the
uniqueness of coefficients of a representation on an open set, "C0"). -/
theorem s05_gc_unif : ∃ C₁ ε₁ : ℝ, 0 < ε₁ ∧ ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε →
    ε < 1 / 4 → ε ≤ ε₁ → ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ R₁ : ℝ, ∀ η R : ℝ, 0 < η → η ≤ η₀ → R₁ ≤ R →
      ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
        ∀ D : Set ℂ, IsOpen D → D ⊆ goodSet Ω Ωs η R →
          RepresentsOp Ω D (graphOp Ω Ωs) (graphCoeffs Ω Ωs D).1 (graphCoeffs Ω Ωs D).2.1
              (graphCoeffs Ω Ωs D).2.2 ∧
            (∀ u : ℂ → ℝ, ContDiffOn ℝ 2 u D → ∀ w ∈ D, graphOp Ω Ωs u w =
              ellOp Ω (graphCoeffs Ω Ωs D).1 (graphCoeffs Ω Ωs D).2.1 (graphCoeffs Ω Ωs D).2.2 u w) ∧
            IsAdmissibleOp Ω D (C₁ * ε) (graphCoeffs Ω Ωs D).1 (graphCoeffs Ω Ωs D).2.1
              (graphCoeffs Ω Ωs D).2.2 := by
  refine ⟨1, 1 / 8, by norm_num, fun K hK ε hε hε4 hε8 => ?_⟩
  obtain ⟨ηb, hηb, -, Rb, hB⟩ := s05_gb_unif K hK ε hε hε4
  obtain ⟨ηc, hηc, Rc, hC⟩ := s05_gc_core K hK ε hε
  obtain ⟨ηN, hηN, RN, hN⟩ := s04_sl_eq_def_N_unif K hK ε hε hε4
  refine ⟨min (min ηb ηc) ηN, lt_min (lt_min hηb hηc) hηN, max (max Rb Rc) RN, ?_⟩
  intro η R hη hηle hR Ω Ωs hp hnl D hDo hDG
  have hηb' : η ≤ ηb := hηle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hηc' : η ≤ ηc := hηle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hηN' : η ≤ ηN := hηle.trans (min_le_right _ _)
  have hRb : Rb ≤ R := (le_max_left _ _).trans ((le_max_left _ _).trans hR)
  have hRc : Rc ≤ R := (le_max_right _ _).trans ((le_max_left _ _).trans hR)
  have hRN : RN ≤ R := (le_max_right _ _).trans hR
  obtain ⟨a, b, c, hsm, hrep, -⟩ := hB η R hη hηb' hRb Ω Ωs hp hnl
  have hGo := (hN η R hη hηN' hRN Ω Ωs hp hnl).1
  have hrepD : RepresentsOp Ω D (graphOp Ω Ωs) a b c :=
    ⟨⟨fun i j => (hsm.1 i j).mono hDG, fun i => (hsm.2.1 i).mono hDG, hsm.2.2.1.mono hDG,
      fun w hw => hsm.2.2.2 w (hDG hw)⟩,
      fun u hu w hw => hrep D hDo hDG u (hu.of_le (by simp)) w hw⟩
  have hex : ∃ abc : (ℂ → Matrix (Fin 2) (Fin 2) ℝ) × (ℂ → Fin 2 → ℝ) × (ℂ → ℝ),
      RepresentsOp Ω D (graphOp Ω Ωs) abc.1 abc.2.1 abc.2.2 := ⟨(a, b, c), hrepD⟩
  have hgc : RepresentsOp Ω D (graphOp Ω Ωs) (graphCoeffs Ω Ωs D).1 (graphCoeffs Ω Ωs D).2.1
      (graphCoeffs Ω Ωs D).2.2 := by
    unfold graphCoeffs
    split_ifs
    exact hex.choose_spec
  have hagree := s05_gc_unique hgc.1.2.2.2 hrepD.1.2.2.2 fun u hu w hw =>
    (hgc.2 u hu.contDiffOn w hw).symm.trans (hrepD.2 u hu.contDiffOn w hw)
  refine ⟨hgc, fun u hu w hw => ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hagree w hw
    rw [hrep D hDo hDG u hu w hw]
    simp only [ellOp, h1, h2, h3]
  · refine ⟨by linarith, by linarith, hDo, fun x hx => (hDG hx).1, hgc.1, ?_⟩
    rw [s05_gc_cjcongr hDo hagree, one_mul]
    have hcore := hC η R hη hηc' hRc Ω Ωs hp hnl a b c
      ⟨hsm, fun u hu w hw => hrep _ hGo subset_rfl u (hu.of_le (by simp)) w hw⟩
    refine le_trans (add_le_add (add_le_add ?_ ?_) ?_) hcore
    · exact s04_tb_cj_mono Ω _ le_rfl hDG
    · exact s04_tb_cj_mono Ω _ le_rfl hDG
    · exact s04_tb_cj_mono Ω _ le_rfl hDG

/-- **Lemma 5.7 (c)** (`lem:graph-operator`, sec05-upper.tex:403).  There are absolute constants
`C₁` and `ε₁ > 0` such that, if `ε ≤ ε₁`, then `𝓛` is `C₁ε`-admissible on `G₀` (stated for every
smooth coefficient representation of `𝓛` on `G₀`; it is unique). -/
theorem lem_graph_operator_c : ∃ C₁ ε₁ : ℝ, 0 < ε₁ ∧ ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε →
    ε < 1 / 4 → ε ≤ ε₁ → ∃ η : ℝ, 0 < η ∧ η < ε ∧ ∃ R : ℝ, ∀ Ω Ωs : Set ℂ,
      IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
        ∀ (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
          RepresentsOp Ω (goodSet Ω Ωs η R) (graphOp Ω Ωs) aUp bUp c →
            IsAdmissibleOp Ω (goodSet Ω Ωs η R) (C₁ * ε) aUp bUp c := by
  obtain ⟨C₁, ε₁, hε₁, hU⟩ := s05_gc_unif
  refine ⟨C₁, ε₁, hε₁, fun K hK ε hε hε4 hεε₁ => ?_⟩
  obtain ⟨η₀, hη₀, R₁, hU'⟩ := hU K hK ε hε hε4 hεε₁
  obtain ⟨η₂, hη₂, R₂, hN⟩ := s04_sl_eq_def_N_unif K hK ε hε hε4
  have hη : 0 < min (min η₀ η₂) (ε / 2) := lt_min (lt_min hη₀ hη₂) (half_pos hε)
  refine ⟨min (min η₀ η₂) (ε / 2), hη, (min_le_right _ _).trans_lt (half_lt_self hε),
    max R₁ R₂, ?_⟩
  intro Ω Ωs hp hnl aUp bUp c hrep
  have hGo := (hN _ (max R₁ R₂) hη ((min_le_left _ _).trans (min_le_right _ _))
    (le_max_right _ _) Ω Ωs hp hnl).1
  obtain ⟨h1, -, h3⟩ := hU' _ (max R₁ R₂) hη ((min_le_left _ _).trans (min_le_left _ _))
    (le_max_left _ _) Ω Ωs hp hnl _ hGo subset_rfl
  have hagree := s05_gc_unique h1.1.2.2.2 hrep.1.2.2.2 fun u hu w hw =>
    (h1.2 u hu.contDiffOn w hw).symm.trans (hrep.2 u hu.contDiffOn w hw)
  refine ⟨h3.1, h3.2.1, h3.2.2.1, h3.2.2.2.1, hrep.1, ?_⟩
  rw [← s05_gc_cjcongr hGo hagree]
  exact h3.2.2.2.2.2

/-- **Lemma 5.7 (d)** (`lem:graph-operator`, sec05-upper.tex:405).
`D𝒬(0)[u] = (2 - |B|²_I) u - Δ_I u`, with `|B|²_I = tr B²`. -/
theorem lem_graph_operator_d : ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ η : ℝ, 0 < η ∧ η < ε ∧ ∃ R : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
      ¬ IsLinePair Ω Ωs → ∀ u : ℂ → ℝ, ContDiffOn ℝ ∞ u (goodSet Ω Ωs η R) →
        ∀ w ∈ goodSet Ω Ωs η R,
          graphQDeriv Ω 0 u w =
            (2 - (shapeMat Ω w * shapeMat Ω w).trace) * u w - fffLaplacian Ω u w := by
  intro K _ ε hε hε'
  refine ⟨ε / 2, by linarith, by linarith, 0, ?_⟩
  intro Ω Ωs hQ _ u hu w hw
  have hJ := s03_b0_jordanPair hQ
  refine s05_go_deriv hJ (s05_go_isOpen hJ (ε / 2)) (fun x hx => hx.1) (fun x hx => ?_) hu hw
  have := s05_go_s_lt hJ le_rfl hx
  linarith

/-! ## §5.5 The bad set and the good domain -/

/-- `cosh d(q, q') ≥ 1` on `ℍ³`. -/
theorem s05_dd_coshDist_ge {q q' : ℂ × ℝ} (hq : q ∈ UHS) (hq' : q' ∈ UHS) :
    1 ≤ coshDist q q' := by
  have h2 : 0 < q.2 := hq
  have h2' : 0 < q'.2 := hq'
  unfold coshDist
  have : 0 ≤ (‖q.1 - q'.1‖ ^ 2 + (q.2 - q'.2) ^ 2) / (2 * q.2 * q'.2) := by positivity
  linarith

/-- `B(P, r) ⊆ B̄(P.1, ρ) × [P.2/(2c), 2c P.2]` with `c = cosh r`, `ρ² = 4c(c-1)P.2²`. -/
theorem s05_dd_hball_box {P q : ℂ × ℝ} (hP : P ∈ UHS) {r : ℝ} (hq : q ∈ hball P r) :
    q ∈ closedBall P.1 (Real.sqrt (4 * Real.cosh r * (Real.cosh r - 1) * P.2 ^ 2)) ×ˢ
      Icc (P.2 / (2 * Real.cosh r)) (2 * Real.cosh r * P.2) := by
  obtain ⟨hqU, hd⟩ := hq
  have hP2 : 0 < P.2 := hP
  have hq2 : 0 < q.2 := hqU
  obtain ⟨c, hc⟩ : ∃ c, c = Real.cosh r := ⟨_, rfl⟩
  rw [← hc]
  have hc1 : 1 ≤ c := hc ▸ Real.one_le_cosh r
  have h1 := s05_dd_coshDist_ge hP hqU
  have hcd : coshDist P q ≤ c := by
    rw [← Real.cosh_arcosh h1, hc]
    refine Real.cosh_le_cosh.mpr ?_
    rw [abs_of_nonneg (Real.arcosh_nonneg h1)]
    exact le_trans (show Real.arcosh (coshDist P q) ≤ r from hd) (le_abs_self r)
  have hN : ‖P.1 - q.1‖ ^ 2 + (P.2 - q.2) ^ 2 ≤ (c - 1) * (2 * P.2 * q.2) := by
    have hcd' : (‖P.1 - q.1‖ ^ 2 + (P.2 - q.2) ^ 2) / (2 * P.2 * q.2) ≤ c - 1 := by
      have : coshDist P q = 1 + (‖P.1 - q.1‖ ^ 2 + (P.2 - q.2) ^ 2) / (2 * P.2 * q.2) := rfl
      linarith
    rwa [div_le_iff₀ (by positivity)] at hcd'
  have hn0 := sq_nonneg (‖P.1 - q.1‖)
  have hup : q.2 ≤ 2 * c * P.2 := by nlinarith
  have hlo : P.2 ≤ 2 * c * q.2 := by nlinarith
  refine ⟨?_, ?_, hup⟩
  · rw [mem_closedBall, Complex.dist_eq, norm_sub_rev]
    have hsq : ‖P.1 - q.1‖ ^ 2 ≤ 4 * c * (c - 1) * P.2 ^ 2 := by
      have : (c - 1) * (2 * P.2 * q.2) ≤ (c - 1) * (2 * P.2 * (2 * c * P.2)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
      nlinarith [sq_nonneg (P.2 - q.2)]
    have := Real.abs_le_sqrt hsq
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  · rw [div_le_iff₀ (by positivity)]
    linarith

/-- Near the diagonal of `ℍ³`, `cosh d < cosh 1`. -/
theorem s05_dd_near_diag {x : ℂ × ℝ} (hx : x ∈ UHS) :
    ∃ V ∈ 𝓝 x, ∀ b ∈ V, ∀ b' ∈ V, coshDist b b' < Real.cosh 1 := by
  have hx2 : 0 < x.2 := hx
  have hcont : ContinuousAt (fun p : (ℂ × ℝ) × (ℂ × ℝ) => coshDist p.1 p.2) (x, x) := by
    unfold coshDist
    refine continuousAt_const.add (ContinuousAt.div (by fun_prop) (by fun_prop) ?_)
    show 2 * x.2 * x.2 ≠ 0
    positivity
  have hx1 : coshDist x x < Real.cosh 1 := by
    have : coshDist x x = 1 := by unfold coshDist; simp
    rw [this]
    exact Real.one_lt_cosh.mpr one_ne_zero
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp (hcont (Iio_mem_nhds hx1))
  refine ⟨u ∩ v, inter_mem hu hv, fun b hb b' hb' => ?_⟩
  have hm := huv (mk_mem_prod hb.1 hb'.2)
  simpa only [mem_preimage, mem_Iio] using hm

/-- A `1`-separated subset of `ℍ³` meets every closed hyperbolic ball `B(P, r)` in a finite set. -/
theorem s05_dd_sep_finite {S : Set (ℂ × ℝ)} (hSU : S ⊆ UHS)
    (hS : ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → 1 ≤ hdist b b') {P : ℂ × ℝ} (hP : P ∈ UHS) (r : ℝ) :
    (S ∩ hball P r).Finite := by
  have hP2 : 0 < P.2 := hP
  have hc0 : 0 < Real.cosh r := Real.cosh_pos r
  have hKb : IsCompact (closedBall P.1 (Real.sqrt (4 * Real.cosh r * (Real.cosh r - 1) * P.2 ^ 2)) ×ˢ
      Icc (P.2 / (2 * Real.cosh r)) (2 * Real.cosh r * P.2)) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  by_contra hinf
  obtain ⟨x, hxK, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf hKb
    (fun q hq => s05_dd_hball_box hP hq.2)
  have hxU : x ∈ UHS := by
    have h1 : P.2 / (2 * Real.cosh r) ≤ x.2 := (mem_prod.mp hxK).2.1
    have h2 : 0 < P.2 / (2 * Real.cosh r) := by positivity
    show 0 < x.2
    linarith
  obtain ⟨V, hV, hVV⟩ := s05_dd_near_diag hxU
  obtain ⟨b, ⟨hbV, hbS⟩, hbx⟩ := accPt_iff_nhds.mp hacc _ hV
  obtain ⟨b', ⟨⟨hb'V, hb'b⟩, hb'S⟩, -⟩ :=
    accPt_iff_nhds.mp hacc _ (inter_mem hV (isOpen_compl_singleton.mem_nhds hbx.symm))
  have hlt := hVV b hbV b' hb'V
  have hsep := hS b hbS.1 b' hb'S.1 (Ne.symm hb'b)
  have h1 := s05_dd_coshDist_ge (hSU hbS.1) (hSU hb'S.1)
  have : Real.cosh 1 ≤ coshDist b b' := by
    rw [← Real.cosh_arcosh h1]
    refine Real.cosh_le_cosh.mpr ?_
    rw [abs_of_nonneg zero_le_one, abs_of_nonneg (Real.arcosh_nonneg h1)]
    exact hsep
  linarith

/-- Packing helper: closed hyperbolic balls `B(P, r)` are Borel. -/
theorem s05_pk_hball_meas (P : ℂ × ℝ) (r : ℝ) : MeasurableSet (hball P r) := by
  have hU : MeasurableSet UHS := measurableSet_lt measurable_const measurable_snd
  have hc : Measurable (coshDist P) := by
    unfold coshDist
    fun_prop
  have ha : Measurable Real.arcosh := by
    unfold Real.arcosh
    fun_prop
  exact hU.inter (measurableSet_le (show Measurable fun Q => hdist P Q from ha.comp hc)
    measurable_const)

/-- Packing helper: `vol B(P, r) ≤ 64π cosh⁶ r` (the box of `s05_dd_hball_box`). -/
theorem s05_pk_hvol_le {P : ℂ × ℝ} (hP : P ∈ UHS) (r : ℝ) :
    hvol (hball P r) ≤ ENNReal.ofReal (64 * π * Real.cosh r ^ 6) := by
  have hP2 : 0 < P.2 := hP
  set c := Real.cosh r with hc
  have hc1 : 1 ≤ c := Real.one_le_cosh r
  set ξ := P.2 with hξ
  set B := closedBall P.1 (2 * c * ξ) ×ˢ Icc (ξ / (2 * c)) (2 * c * ξ) with hB
  have hBm : MeasurableSet B := measurableSet_closedBall.prod measurableSet_Icc
  have hsub : hball P r ⊆ B := by
    intro q hq
    have h := s05_dd_hball_box hP hq
    rw [← hc] at h
    refine ⟨?_, h.2⟩
    refine closedBall_subset_closedBall ?_ h.1
    rw [show 2 * c * ξ = √((2 * c * ξ) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hden : ∀ q ∈ B, ENNReal.ofReal ((q.2 ^ 3)⁻¹) ≤ ENNReal.ofReal ((2 * c / ξ) ^ 3) := by
    intro q hq
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ξ / (2 * c) ≤ q.2 := hq.2.1
    have h0 : 0 < ξ / (2 * c) := by positivity
    rw [show (2 * c / ξ) ^ 3 = ((ξ / (2 * c)) ^ 3)⁻¹ by field_simp]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h0.le h1 3)
  have hvolB : volume B ≤ ENNReal.ofReal ((2 * c * ξ) ^ 2 * π * (2 * c * ξ)) := by
    rw [hB, Measure.volume_eq_prod, Measure.prod_prod, Complex.volume_closedBall,
      Real.volume_Icc]
    have hpi : ((NNReal.pi : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal π := by
      rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
    rw [hpi, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : 2 * c * ξ - ξ / (2 * c) ≤ 2 * c * ξ := by
      have : 0 ≤ ξ / (2 * c) := by positivity
      linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  calc hvol (hball P r) ≤ hvol B := measure_mono hsub
    _ = ∫⁻ q in B, ENNReal.ofReal ((q.2 ^ 3)⁻¹) ∂(volume.restrict UHS) := by
        rw [hvol, withDensity_apply _ hBm]
    _ ≤ ∫⁻ q in B, ENNReal.ofReal ((q.2 ^ 3)⁻¹) ∂volume := by
        rw [Measure.restrict_restrict hBm]
        exact lintegral_mono' (Measure.restrict_mono inter_subset_left le_rfl) le_rfl
    _ ≤ ∫⁻ _q in B, ENNReal.ofReal ((2 * c / ξ) ^ 3) ∂volume := setLIntegral_mono' hBm hden
    _ = ENNReal.ofReal ((2 * c / ξ) ^ 3) * volume B := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal ((2 * c / ξ) ^ 3) * ENNReal.ofReal ((2 * c * ξ) ^ 2 * π * (2 * c * ξ)) :=
        by gcongr
    _ = ENNReal.ofReal (64 * π * c ^ 6) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring

/-- Packing helper: `vol B(P, r) ≥ 2π r³/27` for `0 < r ≤ 1` (a box of half-side `r P.2/2`
around `P`). -/
theorem s05_pk_hvol_ge {P : ℂ × ℝ} (hP : P ∈ UHS) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ENNReal.ofReal (2 * π * r ^ 3 / 27) ≤ hvol (hball P r) := by
  have hP2 : 0 < P.2 := hP
  set ξ := P.2 with hξ
  set δ := r / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 2 := by linarith
  set B := closedBall P.1 (δ * ξ) ×ˢ Icc (ξ - δ * ξ) (ξ + δ * ξ) with hB
  have hBm : MeasurableSet B := measurableSet_closedBall.prod measurableSet_Icc
  have hlow : ∀ q ∈ B, ξ / 2 ≤ q.2 := by
    intro q hq
    have := hq.2.1
    nlinarith
  have hBU : B ⊆ UHS := fun q hq => show 0 < q.2 by linarith [hlow q hq, half_pos hP2]
  have hsub : B ⊆ hball P r := by
    intro q hq
    have hq2 : 0 < q.2 := hBU hq
    refine ⟨hq2, (s03_hdist_le_sqrt hP2 hq2).trans ?_⟩
    have h1 : ‖P.1 - q.1‖ ≤ δ * ξ := by
      rw [← dist_eq_norm, dist_comm]
      exact hq.1
    have h2 : |ξ - q.2| ≤ δ * ξ := by
      rw [abs_le]
      constructor <;> linarith [hq.2.1, hq.2.2]
    have hn : ‖P.1 - q.1‖ ^ 2 + (ξ - q.2) ^ 2 ≤ 2 * (δ * ξ) ^ 2 := by
      have a1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have a2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
      rw [sq_abs] at a2
      linarith
    have hd : (‖P.1 - q.1‖ ^ 2 + (ξ - q.2) ^ 2) / (ξ * q.2) ≤ r ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have := hlow q hq
      have h3 : ξ * (ξ / 2) ≤ ξ * q.2 := mul_le_mul_of_nonneg_left this hP2.le
      have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg r)
      rw [hδ] at hn
      nlinarith
    calc √((‖P.1 - q.1‖ ^ 2 + (ξ - q.2) ^ 2) / (ξ * q.2)) ≤ √(r ^ 2) :=
          Real.sqrt_le_sqrt hd
      _ = r := Real.sqrt_sq hr0.le
  have hden : ∀ q ∈ B, ENNReal.ofReal (8 / (27 * ξ ^ 3)) ≤ ENNReal.ofReal ((q.2 ^ 3)⁻¹) := by
    intro q hq
    refine ENNReal.ofReal_le_ofReal ?_
    have hq2 : 0 < q.2 := hBU hq
    have hup : q.2 ≤ 3 * ξ / 2 := by nlinarith [hq.2.2, mul_le_mul_of_nonneg_right hδ1 hP2.le]
    rw [show 8 / (27 * ξ ^ 3) = ((3 * ξ / 2) ^ 3)⁻¹ by field_simp; ring]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hq2.le hup 3)
  have hvolB : volume B = ENNReal.ofReal ((δ * ξ) ^ 2 * π * (2 * (δ * ξ))) := by
    rw [hB, Measure.volume_eq_prod, Measure.prod_prod, Complex.volume_closedBall,
      Real.volume_Icc]
    have hpi : ((NNReal.pi : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal π := by
      rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
    rw [hpi, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  calc ENNReal.ofReal (2 * π * r ^ 3 / 27)
        = ENNReal.ofReal (8 / (27 * ξ ^ 3)) * volume B := by
          rw [hvolB, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hδ]
          field_simp
          ring
    _ = ∫⁻ _q in B, ENNReal.ofReal (8 / (27 * ξ ^ 3)) ∂volume := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ q in B, ENNReal.ofReal ((q.2 ^ 3)⁻¹) ∂volume := setLIntegral_mono' hBm hden
    _ = ∫⁻ q in B, ENNReal.ofReal ((q.2 ^ 3)⁻¹) ∂(volume.restrict UHS) := by
        rw [Measure.restrict_restrict hBm, inter_eq_left.mpr hBU]
    _ = hvol B := by rw [hvol, withDensity_apply _ hBm]
    _ ≤ hvol (hball P r) := measure_mono hsub

/-- Packing helper (bounded overlap): a `1`-separated subset of `ℍ³` has at most
`23328 cosh⁶(ρ + 1/3)` points in a closed ball `B(X, ρ)` (disjoint balls `B(b, 1/3)` inside
`B(X, ρ + 1/3)`). -/
theorem s05_pk_ncard_le {S : Set (ℂ × ℝ)} (hSU : S ⊆ UHS)
    (hS : ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → 1 ≤ hdist b b') {X : ℂ × ℝ} (hX : X ∈ UHS) (ρ : ℝ) :
    ((S ∩ hball X ρ).ncard : ℝ) ≤ 23328 * Real.cosh (ρ + 1 / 3) ^ 6 := by
  have hF := s05_dd_sep_finite hSU hS hX ρ
  set F := hF.toFinset with hFdef
  have hmem : ∀ b ∈ F, b ∈ S ∧ b ∈ hball X ρ := fun b hb => (hF.mem_toFinset.mp hb)
  have hdisj : (F : Set (ℂ × ℝ)).PairwiseDisjoint fun b => hball b (1 / 3) := by
    intro b hb b' hb' hne
    refine Set.disjoint_left.mpr fun q hq hq' => ?_
    have hbS := (hmem b hb).1
    have hb'S := (hmem b' hb').1
    have t := s02_hdist_triangle (hSU hbS) hq.1 (hSU hb'S)
    rw [s02_hdist_comm q b'] at t
    have := hS b hbS b' hb'S hne
    linarith [hq.2, hq'.2]
  have hU : (⋃ b ∈ F, hball b (1 / 3)) ⊆ hball X (ρ + 1 / 3) := by
    intro q hq
    simp only [mem_iUnion] at hq
    obtain ⟨b, hb, hqb⟩ := hq
    obtain ⟨hbS, hbX⟩ := hmem b hb
    refine ⟨hqb.1, ?_⟩
    have t := s02_hdist_triangle hX (hSU hbS) hqb.1
    linarith [hbX.2, hqb.2]
  have hsum : (F.card : ℝ≥0∞) * ENNReal.ofReal (2 * π * (1 / 3) ^ 3 / 27) ≤
      ENNReal.ofReal (64 * π * Real.cosh (ρ + 1 / 3) ^ 6) := by
    calc (F.card : ℝ≥0∞) * ENNReal.ofReal (2 * π * (1 / 3) ^ 3 / 27)
          = ∑ _b ∈ F, ENNReal.ofReal (2 * π * (1 / 3) ^ 3 / 27) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ b ∈ F, hvol (hball b (1 / 3)) := Finset.sum_le_sum fun b hb =>
            s05_pk_hvol_ge (hSU (hmem b hb).1) (by norm_num) (by norm_num)
      _ = hvol (⋃ b ∈ F, hball b (1 / 3)) :=
            (measure_biUnion_finset hdisj fun b _ => s05_pk_hball_meas b _).symm
      _ ≤ hvol (hball X (ρ + 1 / 3)) := measure_mono hU
      _ ≤ _ := s05_pk_hvol_le hX _
  rw [show (F.card : ℝ≥0∞) = ENNReal.ofReal (F.card : ℝ) from (ENNReal.ofReal_natCast _).symm,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hsum
  rw [Set.ncard_eq_toFinset_card (S ∩ hball X ρ) hF]
  have hpi := Real.pi_pos
  have h2 : (F.card : ℝ) * π ≤ 23328 * Real.cosh (ρ + 1 / 3) ^ 6 * π := by
    norm_num at hsum ⊢
    linarith
  exact le_of_mul_le_mul_right h2 hpi

/-- Packing helper, multiplicity form: if every `b ∈ S` with `x ∈ T b` lies in `B(X, ρ)`, then
`∑_{b ∈ S} 1_{T b}(x) g(x) ≤ 23328 cosh⁶(ρ + 1/3) g(x)`. -/
theorem s05_pk_tsum_le {α : Type*} {S : Set (ℂ × ℝ)} (hSU : S ⊆ UHS)
    (hS : ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → 1 ≤ hdist b b') {X : ℂ × ℝ} (hX : X ∈ UHS) (ρ : ℝ)
    (T : ℂ × ℝ → Set α) (g : α → ℝ≥0∞) (x : α) (hT : ∀ b ∈ S, x ∈ T b → hdist X b ≤ ρ) :
    ∑' b : S, (T b).indicator g x ≤
      ENNReal.ofReal (23328 * Real.cosh (ρ + 1 / 3) ^ 6) * g x := by
  have hF := s05_dd_sep_finite hSU hS hX ρ
  set A := S ∩ hball X ρ with hA
  have h1 : ∀ b : S, (T b).indicator g x ≤ A.indicator 1 (b : ℂ × ℝ) * g x := by
    intro b
    by_cases hx : x ∈ T b
    · rw [indicator_of_mem hx,
        indicator_of_mem (show (b : ℂ × ℝ) ∈ A from ⟨b.2, hSU b.2, hT b b.2 hx⟩)]
      simp
    · rw [indicator_of_notMem hx]
      exact bot_le
  have h2 : ∑' b : S, A.indicator (1 : ℂ × ℝ → ℝ≥0∞) (b : ℂ × ℝ) ≤
      ∑' b : ℂ × ℝ, A.indicator (1 : ℂ × ℝ → ℝ≥0∞) b :=
    tsum_comp_le_tsum_of_injective Subtype.val_injective _
  have h3 : ∑' b : ℂ × ℝ, A.indicator (1 : ℂ × ℝ → ℝ≥0∞) b = (A.ncard : ℝ≥0∞) := by
    rw [tsum_eq_sum (s := hF.toFinset) (fun b hb => indicator_of_notMem
      (fun h => hb (hF.mem_toFinset.mpr h)) _)]
    rw [Finset.sum_congr rfl (fun b hb => indicator_of_mem (hF.mem_toFinset.mp hb) _),
      Set.ncard_eq_toFinset_card A hF]
    simp
  have h4 : (A.ncard : ℝ≥0∞) ≤ ENNReal.ofReal (23328 * Real.cosh (ρ + 1 / 3) ^ 6) := by
    rw [show (A.ncard : ℝ≥0∞) = ENNReal.ofReal (A.ncard : ℝ) from (ENNReal.ofReal_natCast _).symm]
    exact ENNReal.ofReal_le_ofReal (s05_pk_ncard_le hSU hS hX ρ)
  calc ∑' b : S, (T b).indicator g x ≤ ∑' b : S, A.indicator 1 (b : ℂ × ℝ) * g x :=
        tsum_le_tsum h1
    _ = (∑' b : S, A.indicator (1 : ℂ × ℝ → ℝ≥0∞) (b : ℂ × ℝ)) * g x := ENNReal.tsum_mul_right
    _ ≤ _ := by gcongr; exact h2.trans (h3.le.trans h4)

/-- `c < d_ρ(p, w)` persists for `w'` near `w`. -/
theorem s05_dd_dist_gt {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {p w : ℂ}
    (hp : p ∈ Ω) (hw : w ∈ Ω) {c : ℝ} (h : c < poincareDist Ω p w) :
    ∀ᶠ w' in 𝓝 w, c < poincareDist Ω p w' := by
  filter_upwards [s05_poincareDist_eventually_lt hΩ hw (sub_pos.mpr h)] with w' hw'
  have ht := s02_poincareDist_triangle hΩ hp hw'.1 hw
  rw [s02_poincareDist_comm hΩ hw'.1 hw] at ht
  linarith [hw'.2]

/-- **(5.16)** (`eq:def-D`, sec05-upper.tex:496).  `D` is open (by local finiteness of the balls
`\overline{B_ρ}(ℓᵢ, 2)`, which is also stated: every compact subset of `Ω` meets only finitely many
of them, and their union is closed in `Ω`: `closure (⋃ …) ∩ Ω ⊆ ⋃ …`; statement change
approved 2026-11-04, closedness in `ℂ` fails when the `ℓᵢ` accumulate at `∂Ω`). -/
theorem eq_def_D : ∀ K : ℝ, 1 ≤ K → ∀ η R : ℝ, 0 < η → 0 < R → ∀ Ω Ωs : Set ℂ,
    IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs → ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab →
      ∀ (S : Set (ℂ × ℝ)) (ℓ : ℂ × ℝ → ℂ), IsBadNet Ω Ωs lab η R S ℓ →
        (∀ Kc : Set ℂ, IsCompact Kc → Kc ⊆ Ω →
          {b | b ∈ S ∧ (Kc ∩ rhoClosedBall Ω (ℓ b) 2).Nonempty}.Finite) ∧
        closure (⋃ b ∈ S, rhoClosedBall Ω (ℓ b) 2) ∩ Ω ⊆ ⋃ b ∈ S, rhoClosedBall Ω (ℓ b) 2 ∧
        IsOpen (goodDomainD Ω Ωs η R S ℓ) := by
  intro K _ η R _ _ Ω Ωs h hnl lab hlab S ℓ hS
  have hΩ := s02_jordanPair_riemannMap (s03_b0_jordanPair h)
  have hΩo : IsOpen Ω := (s03_b0_basic h).1
  obtain ⟨D, hD⟩ := lem_width K
  have hsep := (prop_separation_b (s03_b0_jordanPair h) hnl).2
  obtain ⟨hw1, -, hw3⟩ := hD Ω Ωs h hnl
  have hDg : ∀ q ∈ gap Ω Ωs, hdistSet q (horoUnion Ω) ≤ max D 0 := fun q hq =>
    (hw1 q hq).1.trans (le_max_left _ _)
  have hDs : ∀ ws ∈ Ωs, hdistSet (epstein Ωs ws) (horoUnion Ω) ≤ max D 0 := fun ws hws =>
    (hw3 ws hws).trans (le_max_left _ _)
  have hpt : ∀ {q : ℂ × ℝ} {ℓ' : ℂ}, IsLabelledPt Ω Ωs lab q ℓ' →
      ℓ' ∈ Ω ∧ q ∈ UHS ∧ hdist q (epstein Ω ℓ') ≤ max D 0 := fun hq =>
    s03_qik_pt h hnl hsep hlab (le_max_right D 0) hDg hDs hq
  have hlabS : ∀ b ∈ S, IsLabelledPt Ω Ωs lab b (ℓ b) := by
    intro b hb
    rcases hS.2.2.2 b hb with ⟨h1, h2⟩ | ⟨⟨z, hz, hzb⟩, h2⟩
    · exact Or.inl ⟨h1, h2.symm⟩
    · exact Or.inr (Or.inl ⟨z, hz, hzb.symm, h2⟩)
  have hbadU : ∀ y ∈ badSet Ω Ωs η R, y ∈ UHS := by
    intro y hy
    rcases hy.1 with ⟨u, hu, rfl⟩ | ⟨z, hz, rfl⟩
    · exact (hpt (ℓ' := u) (Or.inl ⟨hu, rfl⟩)).2.1
    · exact (hpt (ℓ' := lab (epstein Ωs z)) (Or.inr (Or.inl ⟨z, hz, rfl, rfl⟩))).2.1
  have hXU : ∀ w ∈ Ω, epstein Ω w ∈ UHS := fun w hw => (hpt (ℓ' := w) (Or.inl ⟨hw, rfl⟩)).2.1
  have hSU : S ⊆ UHS := fun b hb => (hpt (hlabS b hb)).2.1
  have hup := (s03_qi_upper K Ω Ωs h hnl).1
  -- local finiteness: a ball `B̄_ρ(ℓ_b, 2)` meeting `Kc` forces `d(X(u), b) ≤ D + 15/2` for one of
  -- finitely many centres `u ∈ Kc`
  have hfin : ∀ Kc : Set ℂ, IsCompact Kc → Kc ⊆ Ω →
      {b | b ∈ S ∧ (Kc ∩ rhoClosedBall Ω (ℓ b) 2).Nonempty}.Finite := by
    intro Kc hKc hKΩ
    obtain ⟨t, htK, hcov⟩ := hKc.elim_nhds_subcover
      (fun u => {w' | w' ∈ Ω ∧ poincareDist Ω u w' < 1})
      (fun u hu => s05_poincareDist_eventually_lt hΩ (hKΩ hu) one_pos)
    refine (t.finite_toSet.biUnion fun u hu =>
      s05_dd_sep_finite hSU hS.2.1 (hXU u (hKΩ (htK u hu))) (max D 0 + 15 / 2)).subset ?_
    rintro b ⟨hbS, w, hwK, hwΩ', hwb⟩
    obtain ⟨u, hut, hwu⟩ := mem_iUnion₂.mp (hcov hwK)
    obtain ⟨hℓ, hbU, hbd⟩ := hpt (hlabS b hbS)
    have huΩ := hKΩ (htK u hut)
    refine mem_iUnion₂.mpr ⟨u, hut, hbS, hbU, ?_⟩
    have e1 := hup u huΩ w hwΩ'
    have e2 := hup w hwΩ' (ℓ b) hℓ
    rw [s02_poincareDist_comm hΩ hwΩ' hℓ] at e2
    have t1 := s02_hdist_triangle (hXU u huΩ) (hXU w hwΩ') hbU
    have t2 := s02_hdist_triangle (hXU w hwΩ') (hXU _ hℓ) hbU
    rw [s02_hdist_comm b] at hbd
    linarith [hwu.2, hwb, le_max_left D 0]
  -- each `B̄_ρ(ℓ_b, 2)` is closed in `Ω`
  have hclos1 : ∀ b ∈ S, ∀ w ∈ Ω, w ∈ closure (rhoClosedBall Ω (ℓ b) 2) →
      w ∈ rhoClosedBall Ω (ℓ b) 2 := by
    intro b hb w hw hcl
    refine ⟨hw, not_lt.mp fun hlt => ?_⟩
    obtain ⟨w', hw'1, hw'2⟩ :=
      mem_closure_iff_nhds.mp hcl _ (s05_dd_dist_gt hΩ (hpt (hlabS b hb)).1 hw hlt)
    exact absurd hw'2.2 (not_le.mpr hw'1)
  -- a compact neighbourhood `B̄(w, ε/2) ⊆ Ω`
  have hnb : ∀ w ∈ Ω, ∃ ε > 0, closedBall w ε ⊆ Ω := fun w hw => by
    obtain ⟨ε, hε, hεΩ⟩ := Metric.mem_nhds_iff.mp (hΩo.mem_nhds hw)
    exact ⟨ε / 2, by linarith, (closedBall_subset_ball (by linarith)).trans hεΩ⟩
  refine ⟨hfin, ?_, ?_⟩
  · rintro w ⟨hcl, hw⟩
    obtain ⟨ε, hε, hKc⟩ := hnb w hw
    set F := {b | b ∈ S ∧ (closedBall w ε ∩ rhoClosedBall Ω (ℓ b) 2).Nonempty} with hFdef
    have hF : F.Finite := hfin _ (isCompact_closedBall w ε) hKc
    have hsub : ball w ε ∩ ⋃ b ∈ S, rhoClosedBall Ω (ℓ b) 2 ⊆
        ⋃ b ∈ F, rhoClosedBall Ω (ℓ b) 2 := by
      rintro x ⟨hxB, hxU⟩
      obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp hxU
      exact mem_iUnion₂.mpr ⟨b, ⟨hb, x, ball_subset_closedBall hxB, hxb⟩, hxb⟩
    have hw' : w ∈ closure (⋃ b ∈ F, rhoClosedBall Ω (ℓ b) 2) :=
      closure_mono hsub (isOpen_ball.inter_closure ⟨mem_ball_self hε, hcl⟩)
    rw [hF.closure_biUnion] at hw'
    obtain ⟨b, hbF, hwb⟩ := mem_iUnion₂.mp hw'
    exact mem_iUnion₂.mpr ⟨b, hbF.1, hclos1 b hbF.1 w hw hwb⟩
  · rw [isOpen_iff_mem_nhds]
    rintro w ⟨hw, hbad, hall⟩
    obtain ⟨ε, hε, hKc⟩ := hnb w hw
    set F := {b | b ∈ S ∧ (closedBall w ε ∩ rhoClosedBall Ω (ℓ b) 2).Nonempty} with hFdef
    have hF : F.Finite := hfin _ (isCompact_closedBall w ε) hKc
    -- the finitely many balls near `w`
    have hA : ∀ᶠ w' in 𝓝 w, ∀ b ∈ F, 2 < poincareDist Ω w' (ℓ b) := by
      rw [eventually_all_finite hF]
      intro b hb
      have hℓ := (hpt (hlabS b hb.1)).1
      have h2 := hall b hb.1
      rw [s02_poincareDist_comm hΩ hw hℓ] at h2
      filter_upwards [s05_dd_dist_gt hΩ hℓ hw h2, hΩo.mem_nhds hw] with w' hw' hw'Ω
      rwa [s02_poincareDist_comm hΩ hw'Ω hℓ]
    -- the distance to `𝔅`, by the upper bound of Proposition 3.6
    obtain ⟨r, -, hr2, hr⟩ := ENNReal.lt_iff_exists_real_btwn.mp hbad
    have hr2' : 2 < r := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg zero_le_two).mp hr2
    filter_upwards [hA, s05_poincareDist_eventually_lt hΩ hw (by linarith : 0 < (r - 2) / 3),
      closedBall_mem_nhds w hε] with w' hw'A hw'B hw'K
    refine ⟨hw'B.1, ?_, fun b hb => ?_⟩
    · have hlow : ENNReal.ofReal (r - 5 / 2 * poincareDist Ω w w') ≤
          hsetDist (epstein Ω w') (badSet Ω Ωs η R) := by
        unfold hsetDist at hr ⊢
        refine le_iInf₂ fun y hy => ENNReal.ofReal_le_ofReal ?_
        have hry : r < hdist (epstein Ω w) y :=
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).mp (hr.trans_le (iInf₂_le y hy))
        have t := s02_hdist_triangle (hXU w hw) (hXU w' hw'B.1) (hbadU y hy)
        linarith [hup w hw w' hw'B.1]
      refine lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith [hw'B.2])).mpr ?_) hlow
      linarith [hw'B.2]
    · by_cases hbF : b ∈ F
      · exact hw'A b hbF
      · have hℓ := (hpt (hlabS b hb)).1
        refine not_le.mp fun hle => hbF ⟨hb, w', hw'K, hw'B.1, ?_⟩
        rwa [s02_poincareDist_comm hΩ hℓ hw'B.1]

/-- `d_𝔻(0, z) ≤ R` forces `|z| ≤ (e^R - 1)/(e^R + 1)`. -/
theorem s05_ga_radius {z : ℂ} (hz : ‖z‖ < 1) {R : ℝ} (h : logRatio ‖z‖ ≤ R) :
    ‖z‖ ≤ (Real.exp R - 1) / (Real.exp R + 1) := by
  change Real.log (1 + ‖z‖) - Real.log (1 - ‖z‖) ≤ R at h
  have h1 : 0 < 1 - ‖z‖ := by linarith
  have h2 : 0 < 1 + ‖z‖ := by linarith [norm_nonneg z]
  have h3 : Real.log (1 + ‖z‖) ≤ R + Real.log (1 - ‖z‖) := by linarith
  rw [Real.log_le_iff_le_exp h2, Real.exp_add, Real.exp_log h1] at h3
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- `z ↦ s(f(z)) = |S_f(z)|(1-|z|²)²/4` is continuous on `𝔻` for a Riemann map `f`. -/
theorem s05_ga_schw_cont {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) :
    ContinuousOn (fun z => ‖schwarzian f z‖ * (1 - ‖z‖ ^ 2) ^ 2 / 4) unitDisc := by
  have hA : ∀ z ∈ unitDisc, AnalyticAt ℂ f z := fun z hz =>
    hf.1.analyticAt (isOpen_ball.mem_nhds hz)
  have hS : ContinuousOn (schwarzian f) unitDisc := by
    intro z hz
    have h1 : ContinuousAt (schwarzianHol f) z :=
      (analyticAt_schwarzianHol (hA z hz)
        (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz)).continuousAt
    have h2 : schwarzianHol f =ᶠ[𝓝 z] schwarzian f := by
      filter_upwards [isOpen_ball.mem_nhds hz] with z' hz'
      exact (schwarzian_of_analyticAt (hA z' hz')).symm
    exact (h1.congr h2).continuousWithinAt
  exact ((hS.norm).mul ((continuousOn_const.sub (continuous_norm.continuousOn.pow 2)).pow 2)).div_const 4

/-- One side of Lemma 5.8(a), `G₁ ⊆ G₀`: if `s < η` at every `w'` with `X(w') ∈ B(x, R)`, then
`s ≤ η'` there for one `η' < η`.  The set of such `w'` is relatively compact (`X` is proper by
the lower bound of Proposition 3.6), `s` is continuous, and the upper bound keeps `B(x, R)`
closed under limits, so the supremum is attained. -/
theorem s05_ga_side {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {A B : ℝ}
    (hA : 0 ≤ A)
    (hl : ∀ w ∈ Ω, ∀ w' ∈ Ω, poincareDist Ω w w' ≤ A * hdist (epstein Ω w) (epstein Ω w') + B)
    (hu : ∀ w ∈ Ω, ∀ w' ∈ Ω, hdist (epstein Ω w) (epstein Ω w') ≤ 5 / 2 * poincareDist Ω w w')
    (hXU : ∀ w ∈ Ω, epstein Ω w ∈ UHS) {x : ℂ × ℝ} (hx : x ∈ UHS) {R η : ℝ} (hη : 0 < η)
    (hs : ∀ w' ∈ Ω, epstein Ω w' ∈ hball x R → schwarzNorm Ω w' < η) :
    ∃ η' < η, ∀ w' ∈ Ω, epstein Ω w' ∈ hball x R → schwarzNorm Ω w' ≤ η' := by
  by_cases hT : ∃ w0 ∈ Ω, epstein Ω w0 ∈ hball x R
  swap
  · exact ⟨η / 2, by linarith, fun w' hw' hX => (hT ⟨w', hw', hX⟩).elim⟩
  obtain ⟨w0, hw0, hX0⟩ := hT
  obtain ⟨f, hf, hfw0⟩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω ∧ f 0 = w0 := by
    obtain ⟨f0, hf0⟩ := hΩ
    obtain ⟨p, hp, rfl⟩ : w0 ∈ f0 '' unitDisc := by rw [hf0.2.2]; exact hw0
    obtain ⟨h1, h2, -⟩ := s02_disc_recenter hf0 hp
    exact ⟨_, h1, h2⟩
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hfm : ∀ z ∈ unitDisc, f z ∈ Ω := fun z hz => hf.2.2 ▸ mem_image_of_mem f hz
  obtain ⟨R', hR'⟩ : ∃ R' : ℝ, R' = max (A * (2 * R) + B) 0 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (Real.exp R' - 1) / (Real.exp R' + 1) := ⟨_, rfl⟩
  have he : 0 < Real.exp R' := Real.exp_pos R'
  have ht1 : t < 1 := by rw [ht, div_lt_one (by linarith)]; linarith
  have ht0 : 0 ≤ t := by
    rw [ht]
    have : 1 ≤ Real.exp R' := Real.one_le_exp (by rw [hR']; exact le_max_right _ _)
    exact div_nonneg (by linarith) (by linarith)
  have hsub : closedBall (0 : ℂ) t ⊆ unitDisc := closedBall_subset_ball ht1
  -- every `w'` with `X(w') ∈ B(x, R)` is `f(z)` with `|z| ≤ t`
  have hrad : ∀ z ∈ unitDisc, epstein Ω (f z) ∈ hball x R → z ∈ closedBall (0 : ℂ) t := by
    intro z hz hX
    have hd : hdist (epstein Ω w0) (epstein Ω (f z)) ≤ 2 * R := by
      have tr := s02_hdist_triangle (hXU w0 hw0) hx hX.1
      rw [s02_hdist_comm (epstein Ω w0) x] at tr
      linarith [hX0.2, hX.2]
    have hq := hl w0 hw0 (f z) (hfm z hz)
    rw [← hfw0, subsec_poincare_dist hf h0 hz, s05_diskDist_zero (mem_ball_zero_iff.mp hz)] at hq
    have hqR : logRatio ‖z‖ ≤ R' := by
      rw [hR']
      refine le_trans hq (le_trans ?_ (le_max_left _ _))
      rw [← hfw0] at hd
      nlinarith [mul_le_mul_of_nonneg_left hd hA]
    rw [mem_closedBall_zero_iff, ht]
    exact s05_ga_radius (mem_ball_zero_iff.mp hz) hqR
  set Z := {z | z ∈ closedBall (0 : ℂ) t ∧ epstein Ω (f z) ∈ hball x R} with hZdef
  have hZc : closure Z ⊆ closedBall (0 : ℂ) t :=
    closure_minimal (fun z hz => hz.1) isClosed_closedBall
  have hKc : IsCompact (closure Z) := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hZc
  have h0Z : (0 : ℂ) ∈ closure Z :=
    subset_closure ⟨mem_closedBall_self ht0, by rw [hfw0]; exact hX0⟩
  set g : ℂ → ℝ := fun z => ‖schwarzian f z‖ * (1 - ‖z‖ ^ 2) ^ 2 / 4 with hgdef
  obtain ⟨zs, hzsZ, hmax⟩ :=
    hKc.exists_isMaxOn ⟨0, h0Z⟩ ((s05_ga_schw_cont hf).mono (hZc.trans hsub))
  have hzs : zs ∈ unitDisc := hsub (hZc hzsZ)
  -- the maximizer still has `X(f zs) ∈ B(x, R)`
  have hXs : epstein Ω (f zs) ∈ hball x R := by
    refine ⟨hXU _ (hfm zs hzs), not_lt.mp fun hlt => ?_⟩
    set δ := (hdist x (epstein Ω (f zs)) - R) / 5 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    have hnb : f ⁻¹' {w' | w' ∈ Ω ∧ poincareDist Ω (f zs) w' < δ} ∈ 𝓝 zs :=
      (hf.1.continuousOn.continuousAt (isOpen_ball.mem_nhds hzs))
        (s05_poincareDist_eventually_lt ⟨f, hf⟩ (hfm zs hzs) hδ0)
    obtain ⟨z, ⟨hzΩ, hzd⟩, hzZ⟩ := mem_closure_iff_nhds.mp hzsZ _ hnb
    have hzD := hsub hzZ.1
    have tr := s02_hdist_triangle hx (hzZ.2.1) (hXU _ (hfm zs hzs))
    have hup := hu (f z) (hfm z hzD) (f zs) (hfm zs hzs)
    rw [s02_poincareDist_comm ⟨f, hf⟩ (hfm z hzD) (hfm zs hzs)] at hup
    linarith [hzZ.2.2]
  refine ⟨g zs, ?_, fun w' hw' hX => ?_⟩
  · have := hs _ (hfm zs hzs) hXs
    rwa [eq_s_disk hf hzs] at this
  · obtain ⟨z, hz, rfl⟩ : w' ∈ f '' unitDisc := by rw [hf.2.2]; exact hw'
    rw [eq_s_disk hf hz]
    exact hmax (subset_closure ⟨hrad z hz hX, hX⟩)

/-- **Lemma 5.8 (a)** (`lem:good-domain`, sec05-upper.tex:506).
`\overline{D} ∩ Ω ⊆ G₁ ⊆ G₀`. -/
theorem lem_good_domain_a : ∀ K : ℝ, 1 ≤ K → ∀ η R : ℝ, 0 < η → 0 < R → ∀ Ω Ωs : Set ℂ,
    IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs → ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab →
      ∀ (S : Set (ℂ × ℝ)) (ℓ : ℂ × ℝ → ℂ), IsBadNet Ω Ωs lab η R S ℓ →
        closure (goodDomainD Ω Ωs η R S ℓ) ∩ Ω ⊆ goodSetG1 Ω Ωs η R ∧
          goodSetG1 Ω Ωs η R ⊆ goodSet Ω Ωs η R := by
  intro K _ η R hη _ Ω Ωs h hnl lab _ S ℓ _
  have hΩ := s02_jordanPair_riemannMap (s03_b0_jordanPair h)
  have hΩs := s02_jordanPair_riemannMap (s03_b0_jordanPair (s03_qce_swap h))
  have hXU : ∀ w ∈ Ω, epstein Ω w ∈ UHS := fun w hw =>
    (lem_normal_b hΩ hw).2.2 ▸ (lem_normal_b hΩ hw).1 0
  have hXUs : ∀ z ∈ Ωs, epstein Ωs z ∈ UHS := fun z hz =>
    (lem_normal_b hΩs hz).2.2 ▸ (lem_normal_b hΩs hz).1 0
  have hbadU : ∀ y ∈ badSet Ω Ωs η R, y ∈ UHS := by
    intro y hy
    rcases hy.1 with ⟨u, hu, rfl⟩ | ⟨z, hz, rfl⟩
    · exact hXU u hu
    · exact hXUs z hz
  obtain ⟨A, B, hA, hl⟩ := s03_qi_lower K
  have hup := s03_qi_upper K Ω Ωs h hnl
  refine ⟨?_, ?_⟩
  · -- `\overline D ∩ Ω ⊆ G₁`: `d(X(·), 𝔅)` moves by at most `5/2 d_ρ`
    rintro w ⟨hcl, hw⟩
    obtain ⟨w', ⟨hw'Ω, hd⟩, hw'D⟩ := mem_closure_iff_nhds.mp hcl _
      (s05_poincareDist_eventually_lt hΩ hw (by norm_num : (0 : ℝ) < 1 / 5))
    obtain ⟨-, hbad, -⟩ := hw'D
    refine ⟨hw, ?_⟩
    have hlow : ENNReal.ofReal (2 - 5 / 2 * poincareDist Ω w w') ≤
        hsetDist (epstein Ω w) (badSet Ω Ωs η R) := by
      unfold hsetDist at hbad ⊢
      refine le_iInf₂ fun y hy => ENNReal.ofReal_le_ofReal ?_
      have hy2 : 2 < hdist (epstein Ω w') y :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg zero_le_two).mp (hbad.trans_le (iInf₂_le y hy))
      have t := s02_hdist_triangle (hXU w' hw'Ω) (hXU w hw) (hbadU y hy)
      rw [s02_hdist_comm (epstein Ω w') (epstein Ω w)] at t
      linarith [hup.1 w hw w' hw'Ω]
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)) hlow
  · -- `G₁ ⊆ G₀`: `d(X(w), A) > R`, then compactness on each side
    rintro w ⟨hw, hG⟩
    have hXw := hXU w hw
    have hfar : ∀ a ∈ curvASet Ω Ωs η, R < hdist (epstein Ω w) a := by
      intro a ha
      by_contra hle
      rw [not_lt] at hle
      have hB : epstein Ω w ∈ badSet Ω Ωs η R := by
        refine ⟨Or.inl ⟨w, hw, rfl⟩, ?_⟩
        show hsetDist (epstein Ω w) (curvASet Ω Ωs η) ≤ ENNReal.ofReal R
        unfold hsetDist
        exact (iInf₂_le a ha).trans (ENNReal.ofReal_le_ofReal hle)
      have h0 : hsetDist (epstein Ω w) (badSet Ω Ωs η R) ≤ ENNReal.ofReal 0 := by
        unfold hsetDist
        refine (iInf₂_le _ hB).trans (ENNReal.ofReal_le_ofReal ?_)
        show Real.arcosh (coshDist (epstein Ω w) (epstein Ω w)) ≤ 0
        have : coshDist (epstein Ω w) (epstein Ω w) = 1 := by unfold coshDist; simp
        rw [this, Real.arcosh_zero]
      have := hG.trans_le h0
      rw [ENNReal.ofReal_zero] at this
      exact absurd this (not_lt.mpr bot_le)
    have hs1 : ∀ w' ∈ Ω, epstein Ω w' ∈ hball (epstein Ω w) R → schwarzNorm Ω w' < η :=
      fun w' hw' hX => by
        by_contra hge
        rw [not_lt] at hge
        have := hfar _ (Or.inl ⟨w', hw', hge, rfl⟩)
        linarith [hX.2]
    have hs2 : ∀ z ∈ Ωs, epstein Ωs z ∈ hball (epstein Ω w) R → schwarzNorm Ωs z < η :=
      fun z hz hX => by
        by_contra hge
        rw [not_lt] at hge
        have := hfar _ (Or.inr ⟨z, hz, hge, rfl⟩)
        linarith [hX.2]
    obtain ⟨η1, hη1, h1⟩ := s05_ga_side hΩ hA (hl Ω Ωs h) hup.1 hXU hXw hη hs1
    obtain ⟨η2, hη2, h2⟩ := s05_ga_side hΩs hA (hl Ωs Ω (s03_qce_swap h)) hup.2 hXUs hXw hη hs2
    refine ⟨hw, ?_⟩
    unfold varsigma
    refine lt_of_le_of_lt (Real.sSup_le ?_ (le_max_right _ 0)) (max_lt (max_lt hη1 hη2) hη)
    rintro r (⟨w', hw', hX, rfl⟩ | ⟨z, hz, hX, rfl⟩)
    · exact (h1 w' hw' hX).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (h2 z hz hX).trans ((le_max_right _ _).trans (le_max_left _ _))

/-- **Lemma 5.8 (b)** (`lem:good-domain`, sec05-upper.tex:507).  For every `w_b ∈ ∂D ∩ Ω` there
is `i` with `d_ρ(w_b, ℓᵢ) ≤ R_b := max{2, Q_K(3)}`; `R_b ≥ 2` depends only on `K`. -/
theorem lem_good_domain_b : ∀ K : ℝ, 1 ≤ K → ∃ Rb : ℝ, 2 ≤ Rb ∧ ∀ η R : ℝ, 0 < η → 0 < R →
    ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs → ∀ lab : ℂ × ℝ → ℂ,
      IsLabel Ω lab → ∀ (S : Set (ℂ × ℝ)) (ℓ : ℂ × ℝ → ℂ), IsBadNet Ω Ωs lab η R S ℓ →
        ∀ wb ∈ frontier (goodDomainD Ω Ωs η R S ℓ) ∩ Ω, ∃ b ∈ S, poincareDist Ω wb (ℓ b) ≤ Rb := by
  intro K _
  obtain ⟨A, B, hA, hl⟩ := s03_qi_lower K
  obtain ⟨D, hD⟩ := lem_width K
  refine ⟨max 3 (A * (4 + 2 * max D 0) + B + 1), le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro η R _ _ Ω Ωs h hnl lab hlab S ℓ hS wb hwb
  obtain ⟨hfr, hwbΩ⟩ := hwb
  have hΩ := s02_jordanPair_riemannMap (s03_b0_jordanPair h)
  have hsep := (prop_separation_b (s03_b0_jordanPair h) hnl).2
  obtain ⟨hw1, -, hw3⟩ := hD Ω Ωs h hnl
  have hDg : ∀ q ∈ gap Ω Ωs, hdistSet q (horoUnion Ω) ≤ max D 0 := fun q hq =>
    (hw1 q hq).1.trans (le_max_left _ _)
  have hDs : ∀ ws ∈ Ωs, hdistSet (epstein Ωs ws) (horoUnion Ω) ≤ max D 0 := fun ws hws =>
    (hw3 ws hws).trans (le_max_left _ _)
  have hpt : ∀ {q : ℂ × ℝ} {ℓ' : ℂ}, IsLabelledPt Ω Ωs lab q ℓ' →
      ℓ' ∈ Ω ∧ q ∈ UHS ∧ hdist q (epstein Ω ℓ') ≤ max D 0 := fun hq =>
    s03_qik_pt h hnl hsep hlab (le_max_right D 0) hDg hDs hq
  have hlabS : ∀ b ∈ S, IsLabelledPt Ω Ωs lab b (ℓ b) := by
    intro b hb
    rcases hS.2.2.2 b hb with ⟨h1, h2⟩ | ⟨⟨z, hz, hzb⟩, h2⟩
    · exact Or.inl ⟨h1, h2.symm⟩
    · exact Or.inr (Or.inl ⟨z, hz, hzb.symm, h2⟩)
  have hbadU : ∀ y ∈ badSet Ω Ωs η R, y ∈ UHS := by
    intro y hy
    rcases hy.1 with ⟨u, hu, rfl⟩ | ⟨z, hz, rfl⟩
    · exact (hpt (ℓ' := u) (Or.inl ⟨hu, rfl⟩)).2.1
    · exact (hpt (ℓ' := lab (epstein Ωs z)) (Or.inr (Or.inl ⟨z, hz, rfl, rfl⟩))).2.1
  -- A point `w'` outside `D` with `d_ρ(w_b, w') < 1`.
  have hcl : wb ∈ closure (goodDomainD Ω Ωs η R S ℓ)ᶜ := by
    rw [closure_compl]; exact hfr.2
  obtain ⟨w', ⟨hw'Ω, hd1⟩, hw'D⟩ :=
    mem_closure_iff_nhds.mp hcl _ (s05_poincareDist_eventually_lt hΩ hwbΩ one_pos)
  have hXw' : IsLabelledPt Ω Ωs lab (epstein Ω w') w' := Or.inl ⟨hw'Ω, rfl⟩
  have key : ∃ b ∈ S, ℓ b ∈ Ω ∧
      poincareDist Ω w' (ℓ b) ≤ max 2 (A * (4 + 2 * max D 0) + B) := by
    by_cases hA2 : ENNReal.ofReal 2 < hsetDist (epstein Ω w') (badSet Ω Ωs η R)
    · have hn : ¬ ∀ b ∈ S, 2 < poincareDist Ω w' (ℓ b) := fun hall => hw'D ⟨hw'Ω, hA2, hall⟩
      push Not at hn
      obtain ⟨b, hb, hb2⟩ := hn
      exact ⟨b, hb, (hpt (hlabS b hb)).1, hb2.trans (le_max_left _ _)⟩
    · push Not at hA2
      have h3 : hsetDist (epstein Ω w') (badSet Ω Ωs η R) < ENNReal.ofReal 3 :=
        lt_of_le_of_lt hA2 ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num))
      unfold hsetDist at h3
      rw [iInf_lt_iff] at h3
      obtain ⟨y, hy⟩ := h3
      rw [iInf_lt_iff] at hy
      obtain ⟨hyb, hy3⟩ := hy
      have hy3' := (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mp hy3
      obtain ⟨b, hb, hyb1⟩ := hS.2.2.1 y hyb
      have tr := s02_hdist_triangle (hpt hXw').2.1 (hbadU y hyb) (hbadU b (hS.1 hb))
      have hq := s03_qik_pair h hnl hsep hA (hl Ω Ωs h) (le_max_right D 0) hDg hDs hlab hXw'
        (hlabS b hb) (r := 4) (by linarith)
      exact ⟨b, hb, (hpt (hlabS b hb)).1, hq.trans (le_max_right _ _)⟩
  obtain ⟨b, hb, hℓ, hd⟩ := key
  refine ⟨b, hb, ?_⟩
  have tr := s02_poincareDist_triangle hΩ hwbΩ hw'Ω hℓ
  have hm : max 2 (A * (4 + 2 * max D 0) + B) + 1 ≤ max 3 (A * (4 + 2 * max D 0) + B + 1) := by
    rcases le_total 2 (A * (4 + 2 * max D 0) + B) with hc | hc
    · rw [max_eq_right hc]; exact le_max_right _ _
    · rw [max_eq_left hc]; norm_num
  linarith

/-! ## §5.6 Counting the bad net -/

/-- Helper (P2): `M_{-a}` is the Möbius map `(w + a)/(ā w + 1)`. -/
theorem s05_blaschke_neg_eq (a : ℂ) :
    blaschke (-a) = fun w => (1 * w + a) / (conj a * w + 1) := by
  funext w
  simp only [blaschke, map_neg]
  congr 1 <;> ring

/-- Helper (P2): `|M_{-a}'(ζ)| (1 - |ζ|²) = 1 - |M_{-a}(ζ)|²`. -/
theorem s05_norm_deriv_blaschke_neg {a ζ : ℂ} (ha : ‖a‖ < 1) (hζ : ‖ζ‖ < 1) :
    ‖deriv (blaschke (-a)) ζ‖ * (1 - ‖ζ‖ ^ 2) = 1 - ‖blaschke (-a) ζ‖ ^ 2 := by
  have ha' : ‖-a‖ < 1 := by rwa [norm_neg]
  rw [(hasDerivAt_blaschke ha' hζ).deriv]
  have hden := blaschke_den_ne_zero ha' hζ
  have hkey := one_sub_normSq_blaschke ha' hζ
  have hna : normSq a < 1 := normSq_lt_one_iff.mpr ha
  have hmul : (1 : ℂ) - -a * conj (-a) = ((1 - normSq a : ℝ) : ℂ) := by
    rw [map_neg, neg_mul_neg, mul_conj]
    push_cast
    ring
  rw [hmul, norm_div, norm_pow, Complex.norm_of_nonneg (by linarith)]
  rw [← normSq_eq_norm_sq ζ, ← normSq_eq_norm_sq (blaschke (-a) ζ), hkey, normSq_neg]
  have hD : 0 < normSq (1 - conj (-a) * ζ) := normSq_pos.mpr hden
  have hD' : ‖(1 : ℂ) - conj (-a) * ζ‖ ^ 2 = normSq (1 - conj (-a) * ζ) :=
    (normSq_eq_norm_sq _).symm
  rw [hD']
  field_simp

/-- Helper (P2): Möbius invariance of `|S F|(1 - |ζ|²)²` under the disc automorphism `M_{-a}`. -/
theorem s05_schwarz_invariant {F : ℂ → ℂ} {Ω : Set ℂ} (hF : IsConformalOnto F unitDisc Ω)
    {a ζ : ℂ} (ha : ‖a‖ < 1) (hζ : ‖ζ‖ < 1) :
    ‖schwarzian (F ∘ blaschke (-a)) ζ‖ * (1 - ‖ζ‖ ^ 2) ^ 2 =
      ‖schwarzian F (blaschke (-a) ζ)‖ * (1 - ‖blaschke (-a) ζ‖ ^ 2) ^ 2 := by
  have ha' : ‖-a‖ < 1 := by rwa [norm_neg]
  have hT := isConformalOnto_blaschke ha'
  have hζm : ζ ∈ unitDisc := mem_ball_zero_iff.mpr hζ
  have hTζ : blaschke (-a) ζ ∈ unitDisc := mem_ball_zero_iff.mpr (blaschke_mem_unitDisc ha' hζ)
  have hTa : AnalyticAt ℂ (blaschke (-a)) ζ := hT.1.analyticAt (isOpen_ball.mem_nhds hζm)
  have hTd : deriv (blaschke (-a)) ζ ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hT.1 hT.2.1 hζm
  have hFa : AnalyticAt ℂ F (blaschke (-a) ζ) := hF.1.analyticAt (isOpen_ball.mem_nhds hTζ)
  have hFd : deriv F (blaschke (-a) ζ) ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hF.1 hF.2.1 hTζ
  have hS0 : schwarzian (blaschke (-a)) ζ = 0 := by
    rw [s05_blaschke_neg_eq]
    refine schwarzian_mobius ?_ ζ
    have := LiZhongQC.one_sub_mul_conj_ne_zero ha
    simpa [mul_comm] using this
  rw [eq19_1_chain_rule hTa hTd hFa hFd, hS0, add_zero, norm_mul, norm_pow]
  rw [← s05_norm_deriv_blaschke_neg ha hζ]
  ring

/-- Helper (P2): Cauchy estimate `|(S F)'(0)| ≤ 64/3` for a conformal `F : 𝔻 → Ω`. -/
theorem s05_norm_deriv_schwarzian_zero {F : ℂ → ℂ} {Ω : Set ℂ}
    (hF : IsConformalOnto F unitDisc Ω) : ‖deriv (schwarzian F) 0‖ ≤ 64 / 3 := by
  have hS : DifferentiableOn ℂ (schwarzian F) unitDisc :=
    schwarzian_holomorphic isOpen_ball (isLocUnivMero_of_isConformalOnto isOpen_ball hF)
  have hU := lehto_isUnivMero_of_isConformalOnto hF
  have hcl : DiffContOnCl ℂ (schwarzian F) (ball (0 : ℂ) (1 / 2)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ (by norm_num)]
    exact hS.mono (closedBall_subset_ball (by norm_num))
  have hbd : ∀ z ∈ sphere (0 : ℂ) (1 / 2), ‖schwarzian F z‖ ≤ 32 / 3 := by
    intro z hz
    have hz' : ‖z‖ = 1 / 2 := by simpa using hz
    have hzD : z ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hz']; norm_num)
    have := thm19_2_nehari hU hzD
    rw [hz'] at this
    nlinarith [norm_nonneg (schwarzian F z)]
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num) hcl hbd
  linarith [show (32 / 3 : ℝ) / (1 / 2) = 64 / 3 by norm_num]

/-- Helper (P2): a one-sided fencing estimate. If, at every `x ∈ [0, r)`, the increments of `f`
to the right are dominated by those of a function `Φ` differentiable at `x` with
`|Φ'(x)| ≤ M · 2/(1 - x²)`, then `f r ≤ f 0 + M log((1+r)/(1-r))`. -/
theorem s05_fence {f : ℝ → ℝ} {r M : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf : ContinuousOn f (Icc 0 r))
    (hloc : ∀ x ∈ Ico 0 r, ∃ (Φ : ℝ → ℂ) (Φ' : ℂ), HasDerivAt Φ Φ' x ∧
      ‖Φ'‖ ≤ M * (2 / (1 - x ^ 2)) ∧ ∀ z ∈ Ioo x 1, f z - f x ≤ ‖Φ z - Φ x‖) :
    f r ≤ f 0 + M * logRatio r := by
  have hL : 0 ≤ logRatio r := by
    rw [logRatio]
    have : Real.log (1 - r) ≤ Real.log (1 + r) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε := δ / (logRatio r + 1) with hε
  have hε0 : 0 < ε := div_pos hδ (by linarith)
  have hlog : ∀ x ∈ Icc (0 : ℝ) r, HasDerivAt logRatio (2 / (1 - x ^ 2)) x := fun x hx =>
    hasDerivAt_logRatio (by linarith [hx.1]) (by linarith [hx.2])
  have key := image_le_of_liminf_slope_right_lt_deriv_boundary' (a := 0) (b := r) hf
    (f' := fun x => M * (2 / (1 - x ^ 2)))
    (B := fun x => f 0 + (M + ε) * logRatio x + ε)
    (B' := fun x => (M + ε) * (2 / (1 - x ^ 2))) ?_ ?_ ?_ ?_ ?_ (right_mem_Icc.mpr hr0)
  · have : (M + ε) * logRatio r + ε = M * logRatio r + δ := by
      rw [hε]
      field_simp
      ring
    have key' : f r ≤ f 0 + (M + ε) * logRatio r + ε := key
    linarith
  · intro x hx ρ hρ
    obtain ⟨Φ, Φ', hΦ, hΦ', hinc⟩ := hloc x hx
    have hx1 : x < 1 := by linarith [hx.2]
    have ht : Tendsto (fun z => ‖slope Φ x z‖) (𝓝[>] x) (𝓝 ‖Φ'‖) :=
      ((hasDerivAt_iff_tendsto_slope.mp hΦ).mono_left
        (nhdsWithin_mono _ fun z hz => ne_of_gt hz)).norm
    have hev : ∀ᶠ z in 𝓝[>] x, ‖slope Φ x z‖ < ρ := ht.eventually (gt_mem_nhds (by linarith))
    have hI : ∀ᶠ z in 𝓝[>] x, z ∈ Ioo x 1 := Ioo_mem_nhdsGT hx1
    refine (hev.and hI).mono (fun z hz => ?_) |>.frequently
    obtain ⟨hz1, hz2⟩ := hz
    have hzx : 0 < z - x := sub_pos.mpr hz2.1
    rw [slope_def_field]
    rw [slope_def_module, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hzx] at hz1
    calc (f z - f x) / (z - x) ≤ ‖Φ z - Φ x‖ / (z - x) :=
          div_le_div_of_nonneg_right (hinc z hz2) hzx.le
      _ = (z - x)⁻¹ * ‖Φ z - Φ x‖ := by ring
      _ < ρ := hz1
  · show f 0 ≤ f 0 + (M + ε) * logRatio 0 + ε
    rw [logRatio_zero]
    linarith
  · intro x hx
    exact ((((hlog x hx).const_mul (M + ε)).const_add (f 0)).add_const ε).continuousAt.continuousWithinAt
  · intro x hx
    have := ((hlog x (Ico_subset_Icc_self hx)).const_mul (M + ε)).const_add (f 0)
    exact (this.add_const ε).hasDerivWithinAt
  · intro x hx _
    have h1 : 0 < 2 / (1 - x ^ 2) := by
      have : x < 1 := by linarith [hx.2]
      have : 0 ≤ x := hx.1
      apply div_pos (by norm_num)
      nlinarith
    nlinarith

/-- Helper (P2): along the ray `t ↦ t u`, near `t = x` the function `¼|S F|(1 - |·|²)²` is the
modulus of a function differentiable at `x` with derivative of modulus `≤ (8/3)·2/(1 - x²)`
(recentre at `x u` by a disc automorphism and use the Cauchy estimate). -/
theorem s05_local_phi {F : ℂ → ℂ} {Ω : Set ℂ} (hF : IsConformalOnto F unitDisc Ω) {u : ℂ}
    (hu : ‖u‖ = 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∃ (Φ : ℝ → ℂ) (Φ' : ℂ), HasDerivAt Φ Φ' x ∧ ‖Φ'‖ ≤ 8 / 3 * (2 / (1 - x ^ 2)) ∧
      ∀ z ∈ Ioo (-1 : ℝ) 1,
        ‖schwarzian F ((z : ℂ) * u)‖ * (1 - ‖(z : ℂ) * u‖ ^ 2) ^ 2 / 4 = ‖Φ z‖ := by
  set a : ℂ := (x : ℂ) * u with ha_def
  have ha : ‖a‖ = x := by
    rw [ha_def, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
  have ha1 : ‖a‖ < 1 := by rw [ha]; exact hx1
  have hna : ‖-a‖ < 1 := by rwa [norm_neg]
  set G := F ∘ blaschke (-a) with hG_def
  have hG : IsConformalOnto G unitDisc Ω := hF.comp (isConformalOnto_blaschke hna)
  set ψ : ℝ → ℂ := fun t => blaschke a ((t : ℂ) * u) with hψ_def
  have hpath : HasDerivAt (fun t : ℝ => (t : ℂ) * u) u x := by
    simpa using ((hasDerivAt_id x).ofReal_comp).mul_const u
  have hb : HasDerivAt (blaschke a) ((1 - a * conj a) / (1 - conj a * a) ^ 2) ((x : ℂ) * u) :=
    hasDerivAt_blaschke ha1 ha1
  have hψ : HasDerivAt ψ ((1 - a * conj a) / (1 - conj a * a) ^ 2 * u) x :=
    HasDerivAt.comp (h₂ := blaschke a) x hb hpath
  have hψx : ψ x = 0 := blaschke_self a
  have hSd : DifferentiableAt ℂ (schwarzian G) 0 :=
    (schwarzian_holomorphic isOpen_ball
      (isLocUnivMero_of_isConformalOnto isOpen_ball hG)).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self one_pos))
  have h1 : HasDerivAt (fun t => schwarzian G (ψ t))
      (deriv (schwarzian G) 0 * ((1 - a * conj a) / (1 - conj a * a) ^ 2 * u)) x := by
    have h : HasDerivAt (schwarzian G) (deriv (schwarzian G) 0) (ψ x) := by
      rw [hψx]
      exact hSd.hasDerivAt
    exact h.comp x hψ
  have h2 : HasDerivAt (fun t => (((1 - ‖ψ t‖ ^ 2) ^ 2 : ℝ) : ℂ)) 0 x := by
    have hn := hψ.norm_sq
    rw [hψx, inner_zero_left, mul_zero] at hn
    have := ((hn.const_sub 1).pow 2).ofReal_comp
    simpa using this
  have hΦ := (h1.mul h2).div_const 4
  refine ⟨fun t => schwarzian G (ψ t) * (((1 - ‖ψ t‖ ^ 2) ^ 2 : ℝ) : ℂ) / 4, _, hΦ, ?_, ?_⟩
  · have hnorm : ‖(1 - a * conj a) / (1 - conj a * a) ^ 2 * u‖ = 1 / (1 - x ^ 2) := by
      rw [mul_comm (conj a) a, mul_conj, normSq_eq_norm_sq, ha, norm_mul, hu, mul_one, norm_div,
        norm_pow]
      have h3 : (1 : ℂ) - ((x ^ 2 : ℝ) : ℂ) = ((1 - x ^ 2 : ℝ) : ℂ) := by push_cast; ring
      have h4 : 0 < 1 - x ^ 2 := by nlinarith
      rw [h3, Complex.norm_of_nonneg h4.le]
      field_simp
    rw [hψx]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
      one_pow, Complex.ofReal_one, mul_one, mul_zero, add_zero]
    rw [norm_div, norm_mul, hnorm, Complex.norm_ofNat]
    have hD := s05_norm_deriv_schwarzian_zero hG
    have h4 : 0 < 1 / (1 - x ^ 2) := by
      have : 0 < 1 - x ^ 2 := by nlinarith
      positivity
    rw [show 8 / 3 * (2 / (1 - x ^ 2)) = 64 / 3 * (1 / (1 - x ^ 2)) / 4 by ring]
    gcongr
  · intro z hz
    have hz1 : ‖(z : ℂ) * u‖ < 1 := by
      rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact abs_lt.mpr hz
    have hψz : ‖ψ z‖ < 1 := blaschke_mem_unitDisc ha1 hz1
    have hinv := s05_schwarz_invariant hF ha1 hψz
    rw [blaschke_neg_blaschke ha1 hz1] at hinv
    have hn : ‖(((1 - ‖ψ z‖ ^ 2) ^ 2 : ℝ) : ℂ)‖ = (1 - ‖ψ z‖ ^ 2) ^ 2 :=
      Complex.norm_of_nonneg (sq_nonneg _)
    rw [← hinv]
    conv_rhs => rw [norm_div, norm_mul, hn, Complex.norm_ofNat]

/-- Helper (P2): on the disc, `¼|S F|(1 - |·|²)²` is `8/3`-Lipschitz from `0` for `d_𝔻`. -/
theorem s05_schwarz_lip_disk {F : ℂ → ℂ} {Ω : Set ℂ} (hF : IsConformalOnto F unitDisc Ω)
    {z : ℂ} (hz : ‖z‖ < 1) :
    |‖schwarzian F z‖ * (1 - ‖z‖ ^ 2) ^ 2 / 4 - ‖schwarzian F 0‖ * (1 - ‖(0 : ℂ)‖ ^ 2) ^ 2 / 4| ≤
      8 / 3 * diskDist 0 z := by
  obtain ⟨u, hu, hzu⟩ : ∃ u : ℂ, ‖u‖ = 1 ∧ z = (‖z‖ : ℂ) * u := by
    by_cases h : z = 0
    · exact ⟨1, by simp, by simp [h]⟩
    · have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h)
      refine ⟨z / ‖z‖, ?_, ?_⟩
      · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
          div_self (norm_ne_zero_iff.mpr h)]
      · field_simp
  set r := ‖z‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg z
  have hS : DifferentiableOn ℂ (schwarzian F) unitDisc :=
    schwarzian_holomorphic isOpen_ball (isLocUnivMero_of_isConformalOnto isOpen_ball hF)
  set f : ℝ → ℝ := fun t => ‖schwarzian F ((t : ℂ) * u)‖ * (1 - ‖(t : ℂ) * u‖ ^ 2) ^ 2 / 4
    with hf_def
  have hp : Continuous fun t : ℝ => (t : ℂ) * u := Complex.continuous_ofReal.mul continuous_const
  have hmaps : MapsTo (fun t : ℝ => (t : ℂ) * u) (Icc 0 r) unitDisc := by
    intro t ht
    refine mem_ball_zero_iff.mpr ?_
    rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact lt_of_le_of_lt ht.2 hz
  have hcont : ContinuousOn f (Icc 0 r) :=
    (((hS.continuousOn.comp hp.continuousOn hmaps).norm.mul
      ((continuous_const.sub (hp.norm.pow 2)).pow 2).continuousOn)).div_const 4
  have hloc : ∀ x ∈ Ico 0 r, ∃ (Φ : ℝ → ℂ) (Φ' : ℂ), HasDerivAt Φ Φ' x ∧
      ‖Φ'‖ ≤ 8 / 3 * (2 / (1 - x ^ 2)) ∧ ∀ z ∈ Ioo (-1 : ℝ) 1, f z = ‖Φ z‖ := by
    intro x hx
    exact s05_local_phi hF hu hx.1 (by linarith [hx.2])
  have hup := s05_fence (f := f) hr0 hz hcont fun x hx => by
    obtain ⟨Φ, Φ', hΦ, hΦ', hid⟩ := hloc x hx
    refine ⟨Φ, Φ', hΦ, hΦ', fun t ht => ?_⟩
    have hx' : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have ht' : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1, ht.1], ht.2⟩
    rw [hid t ht', hid x hx']
    exact norm_sub_norm_le _ _
  have hdown := s05_fence (f := fun t => -f t) hr0 hz hcont.neg fun x hx => by
    obtain ⟨Φ, Φ', hΦ, hΦ', hid⟩ := hloc x hx
    refine ⟨Φ, Φ', hΦ, hΦ', fun t ht => ?_⟩
    have hx' : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have ht' : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1, ht.1], ht.2⟩
    rw [hid t ht', hid x hx', norm_sub_rev]
    linarith [norm_sub_norm_le (Φ x) (Φ t)]
  have hfr : f r = ‖schwarzian F z‖ * (1 - ‖z‖ ^ 2) ^ 2 / 4 := by
    simp only [hf_def]
    rw [← hzu]
  have hf0 : f 0 = ‖schwarzian F 0‖ * (1 - ‖(0 : ℂ)‖ ^ 2) ^ 2 / 4 := by
    simp [hf_def]
  rw [s05_diskDist_zero hz, ← hfr, ← hf0, abs_sub_le_iff]
  constructor <;> linarith

/-- Helper (P2): `|s(w) - s(w')| ≤ (8/3) d_ρ(w, w')` on any domain `Ω` (both sides vanish when
there is no conformal map `𝔻 → Ω`). -/
theorem s05_s_lipschitz_gen (Ω : Set ℂ) : ∀ w ∈ Ω, ∀ w' ∈ Ω,
    |schwarzNorm Ω w - schwarzNorm Ω w'| ≤ 8 / 3 * poincareDist Ω w w' := by
  by_cases h : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω
  · obtain ⟨f₀, hf₀⟩ := h
    intro w hw w' hw'
    rw [← hf₀.2.2] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
    have hF : IsConformalOnto (f₀ ∘ blaschke (-a)) unitDisc Ω :=
      hf₀.comp (isConformalOnto_blaschke (by rwa [norm_neg]))
    have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
    have hF0 : (f₀ ∘ blaschke (-a)) 0 = f₀ a := by simp [blaschke_neg_zero]
    rw [← hF.2.2] at hw'
    obtain ⟨z, hz, rfl⟩ := hw'
    rw [← hF0, eq_s_disk hF h0, eq_s_disk hF hz, subsec_poincare_dist hF h0 hz, abs_sub_comm]
    exact s05_schwarz_lip_disk hF (mem_ball_zero_iff.mp hz)
  · intro w _ w' _
    have hs : ∀ v, schwarzNorm Ω v = 0 := by
      intro v
      have he : {r : ℝ | ∃ (f : ℂ → ℂ) (z : ℂ), IsConformalOnto f unitDisc Ω ∧ z ∈ unitDisc ∧
          f z = v ∧ r = ‖schwarzian f z‖ * (1 - ‖z‖ ^ 2) ^ 2 / 4} = ∅ := by
        ext r
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨f, z, hf, -⟩
        exact h ⟨f, hf⟩
      rw [schwarzNorm, he, Real.sSup_empty]
    have hd : poincareDist Ω w w' = 0 := by
      have he : {d : ℝ | ∃ (f : ℂ → ℂ) (a z : ℂ), IsConformalOnto f unitDisc Ω ∧ a ∈ unitDisc ∧
          z ∈ unitDisc ∧ f a = w ∧ f z = w' ∧ d = diskDist a z} = ∅ := by
        ext d
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨f, a, z, hf, -⟩
        exact h ⟨f, hf⟩
      rw [poincareDist, he, Real.sInf_empty]
    rw [hs, hs, hd]
    simp

/-- **Lemma 5.9** (`lem:s-lipschitz`, sec05-upper.tex:535).
`|s(w) - s(w')| ≤ (8/3) d_ρ(w, w')` on `Ω`, and likewise for `s*` on `Ω*`. -/
theorem lem_s_lipschitz : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs →
    (∀ w ∈ Ω, ∀ w' ∈ Ω, |schwarzNorm Ω w - schwarzNorm Ω w'| ≤ 8 / 3 * poincareDist Ω w w') ∧
    ∀ z ∈ Ωs, ∀ z' ∈ Ωs,
      |schwarzNorm Ωs z - schwarzNorm Ωs z'| ≤ 8 / 3 * poincareDist Ωs z z' := by
  intro Ω Ωs _
  exact ⟨s05_s_lipschitz_gen Ω, s05_s_lipschitz_gen Ωs⟩

/-- Counting helper: `∑ᵢ ∫ gᵢ dμ ≤ ∫ ∑ᵢ gᵢ dμ` for `ℝ≥0∞`-valued functions, with no
measurability assumption (finite sums by `le_lintegral_add`, then the supremum). -/
theorem s05_ct_tsum_lintegral_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (g : ι → α → ℝ≥0∞) : ∑' i, ∫⁻ x, g i x ∂μ ≤ ∫⁻ x, ∑' i, g i x ∂μ := by
  classical
  rw [tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have hfin : ∑ i ∈ s, ∫⁻ x, g i x ∂μ ≤ ∫⁻ x, ∑ i ∈ s, g i x ∂μ := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      calc ∫⁻ x, g a x ∂μ + ∑ i ∈ s, ∫⁻ x, g i x ∂μ
          ≤ ∫⁻ x, g a x ∂μ + ∫⁻ x, ∑ i ∈ s, g i x ∂μ := add_le_add le_rfl ih
        _ ≤ ∫⁻ x, (g a x + ∑ i ∈ s, g i x) ∂μ := le_lintegral_add _ _
        _ = ∫⁻ x, ∑ i ∈ insert a s, g i x ∂μ := by
            congr 1
            ext x
            rw [Finset.sum_insert ha]
  exact hfin.trans (lintegral_mono fun x => sum_le_tsum s)

/-- Counting helper: a point of `𝔅` is at distance `< R + 1` from some point of `A`. -/
theorem s05_ct_near_A {Ω Ωs : Set ℂ} {η R : ℝ} (hR : 0 ≤ R) {x : ℂ × ℝ}
    (hx : x ∈ badSet Ω Ωs η R) : ∃ a ∈ curvASet Ω Ωs η, hdist x a < R + 1 := by
  have h : hsetDist x (curvASet Ω Ωs η) ≤ ENNReal.ofReal R := hx.2
  have hlt : hsetDist x (curvASet Ω Ωs η) < ENNReal.ofReal (R + 1) :=
    h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
  unfold hsetDist at hlt
  obtain ⟨a, hlt⟩ := iInf_lt_iff.mp hlt
  obtain ⟨ha, hlt⟩ := iInf_lt_iff.mp hlt
  exact ⟨a, ha, (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp hlt⟩

/-- Counting helper: the `ρ`-ball `{w ∈ Ω : d_ρ(z, w) < r}` is Borel. -/
theorem s05_ct_ball_meas {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {z : ℂ} (hz : z ∈ Ω) (r : ℝ) :
    MeasurableSet {w | w ∈ Ω ∧ poincareDist Ω z w < r} := by
  have hΩ := s02_jordanPair_riemannMap hJ
  have hΩm : MeasurableSet Ω := (s05_jordan_isOpen hJ).measurableSet
  have hk := s03_sc_meas hΩ hz
  have heq : {w | w ∈ Ω ∧ poincareDist Ω z w < r} =
      Ω ∩ {w | 0 < r ∧ ((Real.cosh (r / 2))⁻¹) ^ 2 < intrKernel Ω z w} := by
    ext w
    refine ⟨fun ⟨hw, hd⟩ => ?_, fun ⟨hw, hr, hlt⟩ => ?_⟩
    · have hd0 := s02_poincareDist_nonneg hΩ hz hw
      refine ⟨hw, by linarith, ?_⟩
      have hc1 : 0 < Real.cosh (poincareDist Ω z w / 2) := Real.cosh_pos _
      have hc2 : 0 < Real.cosh (r / 2) := Real.cosh_pos _
      rw [intrKernel, pow_lt_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero,
        inv_lt_inv₀ hc2 hc1, Real.cosh_lt_cosh, abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith)]
      linarith
    · have hd0 := s02_poincareDist_nonneg hΩ hz hw
      refine ⟨hw, ?_⟩
      have hc1 : 0 < Real.cosh (poincareDist Ω z w / 2) := Real.cosh_pos _
      have hc2 : 0 < Real.cosh (r / 2) := Real.cosh_pos _
      rw [intrKernel, pow_lt_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero,
        inv_lt_inv₀ hc2 hc1, Real.cosh_lt_cosh, abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith)] at hlt
      linarith
  rw [heq]
  exact hΩm.inter ((MeasurableSet.const (0 < r)).inter (measurableSet_lt measurable_const hk))

/-- Counting helper (sec05:557–563): if `s(z) ≥ η` with `0 < η < 1/4` and `r_η = 3η/16`, then
`s ≥ η/2` on `P = B_ρ(z, r_η)`, so `a · η²π r_η²/16 ≤ ∫_P g dm_Ω` whenever `a ≤ g` on `P`
(pull back to `𝔻` by `eq_pullback_mass_a`; `P ⊇ f(D(0, r_η/4))` for `f(0) = z`). -/
theorem s05_ct_mass_lower {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {z : ℂ} (hz : z ∈ Ω)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1 / 4) (hs : η ≤ schwarzNorm Ω z) {g : ℂ → ℝ≥0∞}
    {a : ℝ≥0∞} (hg : ∀ w ∈ Ω, poincareDist Ω z w < 3 * η / 16 → a ≤ g w) :
    a * ENNReal.ofReal (η ^ 2 * π * (3 * η / 16) ^ 2 / 16) ≤
      ∫⁻ w, {w | w ∈ Ω ∧ poincareDist Ω z w < 3 * η / 16}.indicator g w ∂curvMass Ω := by
  obtain ⟨f, hf, hf0⟩ := s02_riemannMap_at hJ hz
  set r := 3 * η / 16 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by linarith
  set P := {w | w ∈ Ω ∧ poincareDist Ω z w < r} with hP
  have hPm : MeasurableSet P := s05_ct_ball_meas hJ hz r
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  -- the disc `D(0, r/4)` maps into `P`, where `s ≥ η/2`
  have hball : ∀ u ∈ ball (0 : ℂ) (r / 4), u ∈ unitDisc ∧ f u ∈ P ∧
      η ^ 2 ≤ ‖schwarzian f u‖ ^ 2 * (1 - ‖u‖ ^ 2) ^ 2 / 4 := by
    intro u hu
    have hu' : ‖u‖ < r / 4 := mem_ball_zero_iff.mp hu
    have hu1 : ‖u‖ < 1 := by linarith
    have huD : u ∈ unitDisc := mem_ball_zero_iff.mpr hu1
    have hfu : f u ∈ Ω := by
      rw [← hf.2.2]
      exact mem_image_of_mem f huD
    have hlt : r / 4 ≤ (Real.exp r - 1) / (Real.exp r + 1) := by
      rw [le_div_iff₀ (by positivity)]
      have h1 := Real.add_one_le_exp r
      have h2 : Real.exp r ≤ 3 :=
        (Real.exp_le_exp.mpr hr1).trans (Real.exp_one_lt_d9.le.trans (by norm_num))
      nlinarith
    have hd : poincareDist Ω z (f u) < r := by
      rw [← hf0, subsec_poincare_dist hf h0D huD, s05_diskDist_zero hu1]
      exact s05_logRatio_lt (norm_nonneg u) (hu'.trans_le hlt)
    have hsu : η / 2 ≤ schwarzNorm Ω (f u) := by
      have := s05_s_lipschitz_gen Ω z hz (f u) hfu
      rw [abs_le] at this
      linarith [this.2]
    refine ⟨huD, ⟨hfu, hd⟩, ?_⟩
    have hS := eq_s_disk hf huD
    have ht0 : 0 < 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
    have ht1 : 1 - ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
    have hσ := norm_nonneg (schwarzian f u)
    have h5 : 2 * η ≤ ‖schwarzian f u‖ * (1 - ‖u‖ ^ 2) := by
      have := mul_le_mul_of_nonneg_left ht1 (mul_nonneg hσ ht0.le)
      nlinarith
    nlinarith [mul_le_mul h5 h5 (by positivity) (by positivity)]
  have hpi : ((NNReal.pi : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal π := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  have hmass : ENNReal.ofReal (η ^ 2 * π * r ^ 2 / 16) ≤ curvMass Ω P := by
    rw [← lintegral_indicator_one hPm,
      eq_pullback_mass_a hf (φ := P.indicator 1) (measurable_one.indicator hPm)]
    calc ENNReal.ofReal (η ^ 2 * π * r ^ 2 / 16)
          = ENNReal.ofReal (η ^ 2) * volume (ball (0 : ℂ) (r / 4)) := by
            rw [Complex.volume_ball, hpi, ← ENNReal.ofReal_pow (by positivity),
              ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
      _ = ∫⁻ _u in ball (0 : ℂ) (r / 4), ENNReal.ofReal (η ^ 2) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ u in ball (0 : ℂ) (r / 4), P.indicator 1 (f u) *
            ENNReal.ofReal (‖schwarzian f u‖ ^ 2 * (1 - ‖u‖ ^ 2) ^ 2 / 4) := by
            refine setLIntegral_mono' measurableSet_ball fun u hu => ?_
            obtain ⟨-, hfu, hle⟩ := hball u hu
            rw [indicator_of_mem hfu, Pi.one_apply, one_mul]
            exact ENNReal.ofReal_le_ofReal hle
      _ ≤ ∫⁻ u in unitDisc, P.indicator 1 (f u) *
            ENNReal.ofReal (‖schwarzian f u‖ ^ 2 * (1 - ‖u‖ ^ 2) ^ 2 / 4) :=
            lintegral_mono' (Measure.restrict_mono (fun u hu => (hball u hu).1) le_rfl) le_rfl
  calc a * ENNReal.ofReal (η ^ 2 * π * r ^ 2 / 16) ≤ a * curvMass Ω P := by gcongr
    _ = ∫⁻ w, P.indicator (fun _ => a) w ∂curvMass Ω := (lintegral_indicator_const hPm a).symm
    _ ≤ ∫⁻ w, P.indicator g w ∂curvMass Ω := by
        refine lintegral_mono fun w => ?_
        by_cases hw : w ∈ P
        · rw [indicator_of_mem hw, indicator_of_mem hw]
          exact hg w hw.1 hw.2
        · rw [indicator_of_notMem hw, indicator_of_notMem hw]

/-- **Lemma 5.10** (`lem:counting`, sec05-upper.tex:555).  If `𝔅 ≠ ∅`, then for every `p ∈ Ω`,
`∑ᵢ k_p(ℓᵢ) ≤ C(K) K_{H,2}(p)` (5.17).  (In the paper `η < ε < 1/4` and `R` are the constants
fixed in §5.4; the statement is made for all such `η` and all `R > 0`, the constant depending on
`K, η, R`.) -/
theorem lem_counting : ∀ K : ℝ, 1 ≤ K → ∀ η R : ℝ, 0 < η → η < 1 / 4 → 0 < R →
    ∃ C : ℝ≥0, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab → ∀ (S : Set (ℂ × ℝ)) (ℓ : ℂ × ℝ → ℂ),
        IsBadNet Ω Ωs lab η R S ℓ → (badSet Ω Ωs η R).Nonempty → ∀ p ∈ Ω,
          ∑' b : S, ENNReal.ofReal (intrKernel Ω p (ℓ b)) ≤ (C : ℝ≥0∞) * KH2 Ω Ωs lab p := by
  intro K _ η R hη hη1 hR
  obtain ⟨A, B, D, hQK⟩ := prop_qi_QK K
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = A * (R + 4 + 2 * D) + B := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = η ^ 2 * π * (3 * η / 16) ^ 2 / 16 := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = 23328 * Real.cosh (R + 4 + 1 / 3) ^ 6 := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; positivity
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  refine ⟨Real.toNNReal (N * Real.exp Q / m), ?_⟩
  -- the hypothesis `𝔅 ≠ ∅` is not needed: for `S = ∅` the sum is `0`
  intro Ω Ωs h hnl lab hlab S ℓ hS _ p hp
  have hJ := s03_b0_jordanPair h
  have hJs := s03_b0_jordanPair (s03_qce_swap h)
  have hΩ := s02_jordanPair_riemannMap hJ
  have hΩs := s02_jordanPair_riemannMap hJs
  obtain ⟨-, hDg, hDs, hlabd⟩ := hQK Ω Ωs h hnl
  have hsep := (prop_separation_b hJ hnl).2
  have hDg' : ∀ q ∈ gap Ω Ωs, hdistSet q (horoUnion Ω) ≤ max D 0 := fun q hq =>
    (hDg q hq).trans (le_max_left _ _)
  have hDs' : ∀ ws ∈ Ωs, hdistSet (epstein Ωs ws) (horoUnion Ω) ≤ max D 0 := fun ws hws =>
    (hDs ws hws).trans (le_max_left _ _)
  have hpt : ∀ {q : ℂ × ℝ} {ℓ' : ℂ}, IsLabelledPt Ω Ωs lab q ℓ' →
      ℓ' ∈ Ω ∧ q ∈ UHS ∧ hdist q (epstein Ω ℓ') ≤ max D 0 := fun hq =>
    s03_qik_pt h hnl hsep hlab (le_max_right D 0) hDg' hDs' hq
  have hlabS : ∀ b ∈ S, IsLabelledPt Ω Ωs lab b (ℓ b) := by
    intro b hb
    rcases hS.2.2.2 b hb with ⟨h1, h2⟩ | ⟨⟨z, hz, hzb⟩, h2⟩
    · exact Or.inl ⟨h1, h2.symm⟩
    · exact Or.inr (Or.inl ⟨z, hz, hzb.symm, h2⟩)
  have hXU : ∀ w ∈ Ω, epstein Ω w ∈ UHS := fun w hw => (hpt (ℓ' := w) (Or.inl ⟨hw, rfl⟩)).2.1
  have hXsU : ∀ z ∈ Ωs, epstein Ωs z ∈ UHS := fun z hz =>
    (hpt (ℓ' := lab (epstein Ωs z)) (Or.inr (Or.inl ⟨z, hz, rfl, rfl⟩))).2.1
  have hRΩ : ∀ z ∈ Ωs, lab (epstein Ωs z) ∈ Ω := fun z hz =>
    (hpt (ℓ' := lab (epstein Ωs z)) (Or.inr (Or.inl ⟨z, hz, rfl, rfl⟩))).1
  have hSU : S ⊆ UHS := fun b hb => (hpt (hlabS b hb)).2.1
  have hup := s03_qi_upper K Ω Ωs h hnl
  have hk0 : ∀ w, 0 ≤ intrKernel Ω p w := fun w => sq_nonneg _
  -- (2.17) `eq:kernel-lip`: `e^{-Q} k_p(w₁) ≤ k_p(w₂)` when `d_ρ(w₁, w₂) ≤ Q`
  have hkt : ∀ w₁ w₂, w₁ ∈ Ω → w₂ ∈ Ω → poincareDist Ω w₁ w₂ ≤ Q →
      ENNReal.ofReal (Real.exp (-Q) * intrKernel Ω p w₁) ≤ ENNReal.ofReal (intrKernel Ω p w₂) := by
    intro w₁ w₂ h1 h2 hd
    refine ENNReal.ofReal_le_ofReal ?_
    have hl := eq_kernel_lip_b hΩ hp h1 h2
    have he : Real.exp (poincareDist Ω w₁ w₂) ≤ Real.exp Q := Real.exp_le_exp.mpr hd
    calc Real.exp (-Q) * intrKernel Ω p w₁
        ≤ Real.exp (-Q) * (Real.exp Q * intrKernel Ω p w₂) :=
          mul_le_mul_of_nonneg_left (hl.trans (mul_le_mul_of_nonneg_right he (hk0 _)))
            (Real.exp_pos _).le
      _ = intrKernel Ω p w₂ := by rw [← mul_assoc, ← Real.exp_add]; simp
  have hconst : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x =
      ENNReal.ofReal (Real.exp Q / m) * (ENNReal.ofReal (Real.exp (-Q) * x) * ENNReal.ofReal m) := by
    intro x hx
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.exp_neg]
    field_simp
  -- one net point `b`: the sets `P_b ⊆ Ω`, `P*_b ⊆ Ω*` of the paper (one of them empty)
  have hb : ∀ b ∈ S, ∃ Pw Pz : Set ℂ,
      ENNReal.ofReal (intrKernel Ω p (ℓ b)) ≤ ENNReal.ofReal (Real.exp Q / m) *
        ((∫⁻ w, Pw.indicator (fun w => ENNReal.ofReal (intrKernel Ω p w)) w ∂curvMass Ω) +
          ∫⁻ z, Pz.indicator (fun z => ENNReal.ofReal (intrKernel Ω p (lab (epstein Ωs z)))) z
            ∂curvMass Ωs) ∧
      (∀ w ∈ Pw, w ∈ Ω ∧ hdist (epstein Ω w) b ≤ R + 4) ∧
      (∀ z ∈ Pz, z ∈ Ωs ∧ hdist (epstein Ωs z) b ≤ R + 4) := by
    intro b hbS
    have hbU := hSU hbS
    have hℓ := (hpt (hlabS b hbS)).1
    obtain ⟨a, ha, hba⟩ := s05_ct_near_A hR.le (hS.1 hbS)
    rcases ha with ⟨z, hz, hsz, rfl⟩ | ⟨z, hz, hsz, rfl⟩
    · have hdw : ∀ w ∈ Ω, poincareDist Ω z w < 3 * η / 16 →
          hdist (epstein Ω w) b ≤ R + 4 := by
        intro w hw hd
        have t := s02_hdist_triangle (hXU w hw) (hXU z hz) hbU
        have h1 := hup.1 w hw z hz
        rw [s02_poincareDist_comm hΩ hw hz] at h1
        rw [s02_hdist_comm (epstein Ω z) b] at t
        linarith
      have hmass := s05_ct_mass_lower hJ hz hη hη1 hsz
        (g := fun w => ENNReal.ofReal (intrKernel Ω p w))
        (a := ENNReal.ofReal (Real.exp (-Q) * intrKernel Ω p (ℓ b))) (fun w hw hd => by
          refine hkt (ℓ b) w hℓ hw ?_
          rw [hQ]
          refine hlabd lab hlab b (epstein Ω w) (ℓ b) w (R + 4) (hlabS b hbS)
            (Or.inl ⟨hw, rfl⟩) ?_
          rw [s02_hdist_comm]
          exact hdw w hw hd)
      rw [← hm] at hmass
      refine ⟨{w | w ∈ Ω ∧ poincareDist Ω z w < 3 * η / 16}, ∅, ?_,
        fun w hw => ⟨hw.1, hdw w hw.1 hw.2⟩, fun _ h => absurd h (notMem_empty _)⟩
      calc ENNReal.ofReal (intrKernel Ω p (ℓ b))
          = ENNReal.ofReal (Real.exp Q / m) *
              (ENNReal.ofReal (Real.exp (-Q) * intrKernel Ω p (ℓ b)) * ENNReal.ofReal m) :=
            hconst _ (hk0 _)
        _ ≤ ENNReal.ofReal (Real.exp Q / m) * ∫⁻ w, {w | w ∈ Ω ∧ poincareDist Ω z w < 3 * η / 16}.indicator
              (fun w => ENNReal.ofReal (intrKernel Ω p w)) w ∂curvMass Ω := mul_le_mul' le_rfl hmass
        _ ≤ _ := mul_le_mul' le_rfl le_self_add
    · have hdz : ∀ z' ∈ Ωs, poincareDist Ωs z z' < 3 * η / 16 →
          hdist (epstein Ωs z') b ≤ R + 4 := by
        intro z' hz' hd
        have t := s02_hdist_triangle (hXsU z' hz') (hXsU z hz) hbU
        have h1 := hup.2 z' hz' z hz
        rw [s02_poincareDist_comm hΩs hz' hz] at h1
        rw [s02_hdist_comm (epstein Ωs z) b] at t
        linarith
      have hmass := s05_ct_mass_lower hJs hz hη hη1 hsz
        (g := fun z' => ENNReal.ofReal (intrKernel Ω p (lab (epstein Ωs z'))))
        (a := ENNReal.ofReal (Real.exp (-Q) * intrKernel Ω p (ℓ b))) (fun z' hz' hd => by
          refine hkt (ℓ b) _ hℓ (hRΩ z' hz') ?_
          rw [hQ]
          refine hlabd lab hlab b (epstein Ωs z') (ℓ b) (lab (epstein Ωs z')) (R + 4)
            (hlabS b hbS) (Or.inr (Or.inl ⟨z', hz', rfl, rfl⟩)) ?_
          rw [s02_hdist_comm]
          exact hdz z' hz' hd)
      rw [← hm] at hmass
      refine ⟨∅, {z' | z' ∈ Ωs ∧ poincareDist Ωs z z' < 3 * η / 16}, ?_,
        fun _ h => absurd h (notMem_empty _), fun z' hz' => ⟨hz'.1, hdz z' hz'.1 hz'.2⟩⟩
      calc ENNReal.ofReal (intrKernel Ω p (ℓ b))
          = ENNReal.ofReal (Real.exp Q / m) *
              (ENNReal.ofReal (Real.exp (-Q) * intrKernel Ω p (ℓ b)) * ENNReal.ofReal m) :=
            hconst _ (hk0 _)
        _ ≤ ENNReal.ofReal (Real.exp Q / m) * ∫⁻ z', {z' | z' ∈ Ωs ∧ poincareDist Ωs z z' < 3 * η / 16}.indicator
              (fun z => ENNReal.ofReal (intrKernel Ω p (lab (epstein Ωs z)))) z' ∂curvMass Ωs :=
            mul_le_mul' le_rfl hmass
        _ ≤ _ := mul_le_mul' le_rfl le_add_self
  choose! Pw Pz hPk hPw hPz using hb
  -- multiplicity (packing in `ℍ³`, `s05_pk_tsum_le`)
  have hI : ∀ w, ∑' b : S, (Pw b).indicator (fun w => ENNReal.ofReal (intrKernel Ω p w)) w ≤
      ENNReal.ofReal N * ENNReal.ofReal (intrKernel Ω p w) := by
    intro w
    by_cases hw : w ∈ Ω
    · rw [hN]
      exact s05_pk_tsum_le hSU hS.2.1 (hXU w hw) (R + 4) Pw _ w
        (fun b hb hwb => (hPw b hb w hwb).2)
    · have h0 : ∀ b : S, (Pw b).indicator (fun w => ENNReal.ofReal (intrKernel Ω p w)) w = 0 :=
        fun b => indicator_of_notMem (fun h' => hw (hPw b b.2 w h').1) _
      simp only [h0, tsum_zero, zero_le]
  have hJ' : ∀ z, ∑' b : S, (Pz b).indicator
      (fun z => ENNReal.ofReal (intrKernel Ω p (lab (epstein Ωs z)))) z ≤
      ENNReal.ofReal N * ENNReal.ofReal (intrKernel Ω p (lab (epstein Ωs z))) := by
    intro z
    by_cases hz : z ∈ Ωs
    · rw [hN]
      exact s05_pk_tsum_le hSU hS.2.1 (hXsU z hz) (R + 4) Pz _ z
        (fun b hb hzb => (hPz b hb z hzb).2)
    · have h0 : ∀ b : S, (Pz b).indicator
          (fun z => ENNReal.ofReal (intrKernel Ω p (lab (epstein Ωs z)))) z = 0 :=
        fun b => indicator_of_notMem (fun h' => hz (hPz b b.2 z h').1) _
      simp only [h0, tsum_zero, zero_le]
  -- summing over the net (Tonelli without measurability, `s05_ct_tsum_lintegral_le`)
  show _ ≤ ENNReal.ofReal (N * Real.exp Q / m) * (KH Ω p + Kst Ω Ωs lab p)
  calc ∑' b : S, ENNReal.ofReal (intrKernel Ω p (ℓ b))
      ≤ ∑' b : S, ENNReal.ofReal (Real.exp Q / m) *
          ((∫⁻ w, (Pw b).indicator (fun w => ENNReal.ofReal (intrKernel Ω p w)) w ∂curvMass Ω) +
            ∫⁻ z, (Pz b).indicator
              (fun z => ENNReal.ofReal (intrKernel Ω p (lab (epstein Ωs z)))) z ∂curvMass Ωs) :=
        tsum_le_tsum fun b => hPk b b.2
    _ = ENNReal.ofReal (Real.exp Q / m) *
          ((∑' b : S, ∫⁻ w, (Pw b).indicator
              (fun w => ENNReal.ofReal (intrKernel Ω p w)) w ∂curvMass Ω) +
            ∑' b : S, ∫⁻ z, (Pz b).indicator
              (fun z => ENNReal.ofReal (intrKernel Ω p (lab (epstein Ωs z)))) z ∂curvMass Ωs) := by
        rw [ENNReal.tsum_mul_left, tsum_add]
    _ ≤ ENNReal.ofReal (Real.exp Q / m) *
          ((∫⁻ w, ENNReal.ofReal N * ENNReal.ofReal (intrKernel Ω p w) ∂curvMass Ω) +
            ∫⁻ z, ENNReal.ofReal N * ENNReal.ofReal (intrKernel Ω p (lab (epstein Ωs z)))
              ∂curvMass Ωs) := by
        gcongr
        · exact (s05_ct_tsum_lintegral_le _ _).trans (lintegral_mono hI)
        · exact (s05_ct_tsum_lintegral_le _ _).trans (lintegral_mono hJ')
    _ = ENNReal.ofReal (N * Real.exp Q / m) * (KH Ω p + Kst Ω Ωs lab p) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_add, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring


/-! ## §5.7 The slabs and the bad region -/

/-- Theorem-6.1 helper (TL2): a `1`-separated subset of `ℍ³` is countable (it meets each
`B(P, n)` in a finite set, `s05_dd_sep_finite`). -/
theorem s06_tl_countable {S : Set (ℂ × ℝ)} (hSU : S ⊆ UHS)
    (hS : ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → 1 ≤ hdist b b') : S.Countable := by
  have hP₀ : ((0 : ℂ), (1 : ℝ)) ∈ UHS := show (0 : ℝ) < 1 from one_pos
  refine (countable_iUnion fun n : ℕ => (s05_dd_sep_finite hSU hS hP₀ n).countable).mono
    fun q hq => ?_
  exact mem_iUnion.2 ⟨⌈hdist ((0 : ℂ), (1 : ℝ)) q⌉₊, hq, hSU hq, Nat.le_ceil _⟩

/-! ## §5.7 The slab identity and the bad region (interface SRB, w3)

`s05_sr_unif`: the slab identity in uniform form (every `η ≤ η₀`, `R ≥ R₁`), from
`s04_sl_cor_coverage_unif`, `lem_good_domain_a` (`D ⊆ G₁ ⊆ G₀`) and `lem_normal_b`
(`τ = d(X(w), E(w, τ))`).  `s05_br_*`: the net is countable by `s06_tl_countable`
(moved here from S06, directly above); a gap point with label outside `D` lies in
`B(Bᵢ, R₂)`, `R₂ = 2D_K + 5`, where `k_p(w(q)) ≤ e^Q k_p(ℓᵢ)` (`prop_qi_QK`, `eq_kernel_lip_b`);
`s05_br_unif` is Lemma 5.11 in uniform form (`lintegral_iUnion_le`, `s05_pk_hvol_le`). -/

/-- SR1 (uniform slab identity): for all `η ≤ η₀`, `R ≥ R₁`, `𝒮_D = 𝒩 ∩ w⁻¹(D)` and
`(w, τ) ↦ E(w, τ)` is injective on `{w ∈ D, 0 < τ < t(w)}`. -/
theorem s05_sr_unif : ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ η R : ℝ, 0 < η → η ≤ η₀ → R₁ ≤ R →
      ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
      ¬ IsLinePair Ω Ωs → ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab →
        ∀ (S : Set (ℂ × ℝ)) (ℓ : ℂ × ℝ → ℂ), IsBadNet Ω Ωs lab η R S ℓ →
          slabRegion Ω Ωs (goodDomainD Ω Ωs η R S ℓ) =
              gap Ω Ωs ∩ lab ⁻¹' goodDomainD Ω Ωs η R S ℓ ∧
            InjOn (normalMap Ω) {x | x.1 ∈ goodDomainD Ω Ωs η R S ℓ ∧ 0 < x.2 ∧
              x.2 < slabTop Ω Ωs x.1} := by
  intro K hK ε hε hε'
  obtain ⟨η₀, hη₀, R₁, hcov⟩ := s04_sl_cor_coverage_unif K hK ε hε hε'
  refine ⟨η₀, hη₀, max R₁ 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun η R hη hηle hR Ω Ωs hp hnl lab hlab S ℓ hnet => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_right _ _)) hR
  obtain ⟨hc1, hc2⟩ := hcov η R hη hηle ((le_max_left _ _).trans hR) Ω Ωs hp hnl lab hlab
  obtain ⟨hDG1, hG1G0⟩ := lem_good_domain_a K hK η R hη hR0 Ω Ωs hp hnl lab hlab S ℓ hnet
  have hDG : ∀ w ∈ goodDomainD Ω Ωs η R S ℓ, IsGoodParam Ω Ωs η R w := fun w hw =>
    hG1G0 (hDG1 ⟨subset_closure hw, hw.1⟩)
  have hΩ := s02_jordanPair_riemannMap (s03_b0_jordanPair hp)
  refine ⟨?_, ?_⟩
  · ext q
    constructor
    · rintro ⟨w, hw, τ, h0, h1, rfl⟩
      obtain ⟨hg, hl⟩ := hc2 w (hDG w hw) τ ⟨h0, h1⟩
      refine ⟨hg, ?_⟩
      show lab (normalGeod Ω w τ) ∈ goodDomainD Ω Ωs η R S ℓ
      rw [hl]
      exact hw
    · rintro ⟨hq, hqD⟩
      obtain ⟨τ, h0, h1, hq'⟩ := hc1 q hq (hDG _ hqD)
      exact ⟨lab q, hqD, τ, h0, h1, hq'⟩
  · rintro ⟨w, τ⟩ ⟨hw, h0, h1⟩ ⟨w', τ'⟩ ⟨hw', h0', h1'⟩ heq
    change normalGeod Ω w τ = normalGeod Ω w' τ' at heq
    have hww : w = w' := by
      have a := (hc2 w (hDG w hw) τ ⟨h0, h1⟩).2
      have b := (hc2 w' (hDG w' hw') τ' ⟨h0', h1'⟩).2
      rw [heq] at a
      exact a.symm.trans b
    subst hww
    have hnb := lem_normal_b hΩ (hDG w hw).1
    have hd := hnb.2.1 τ τ'
    rw [heq, hnb.2.1 τ' τ', sub_self, abs_zero] at hd
    have h0'' : τ - τ' = 0 := abs_eq_zero.1 hd.symm
    refine Prod.ext rfl ?_
    show τ = τ'
    linarith

/-- BR2 (cover and kernel comparison): a gap point whose label is not in `D` lies in some
`B(Bᵢ, R₂)`; and `k_p(w(q)) ≤ e^Q k_p(ℓᵢ)` for gap points `q ∈ B(Bᵢ, R₂)`. -/
theorem s05_br_cover : ∀ K : ℝ, 1 ≤ K → ∃ R₂ Q : ℝ, ∀ η R : ℝ, 0 < η → 0 < R →
    ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs → ∀ lab : ℂ × ℝ → ℂ,
      IsLabel Ω lab → ∀ (S : Set (ℂ × ℝ)) (ℓ : ℂ × ℝ → ℂ), IsBadNet Ω Ωs lab η R S ℓ →
        (∀ q ∈ gap Ω Ωs, lab q ∉ goodDomainD Ω Ωs η R S ℓ → ∃ b ∈ S, q ∈ hball b R₂) ∧
        ∀ p ∈ Ω, ∀ b ∈ S, ∀ q ∈ gap Ω Ωs, q ∈ hball b R₂ →
          intrKernel Ω p (lab q) ≤ Real.exp Q * intrKernel Ω p (ℓ b) := by
  intro K _
  obtain ⟨A, B, Dk, hQK⟩ := prop_qi_QK K
  refine ⟨2 * max Dk 0 + 5, A * (2 * max Dk 0 + 5 + 2 * Dk) + B,
    fun η R _ _ Ω Ωs h hnl lab hlab S ℓ hS => ?_⟩
  have hJ := s03_b0_jordanPair h
  have hΩ := s02_jordanPair_riemannMap hJ
  have hΩs := s02_jordanPair_riemannMap (s03_b0_jordanPair (s03_qce_swap h))
  obtain ⟨-, hDg, hDs, hlabd⟩ := hQK Ω Ωs h hnl
  have hsep := (prop_separation_b hJ hnl).2
  have hD0 : 0 ≤ max Dk 0 := le_max_right _ _
  have hpt : ∀ {q : ℂ × ℝ} {ℓ' : ℂ}, IsLabelledPt Ω Ωs lab q ℓ' →
      ℓ' ∈ Ω ∧ q ∈ UHS ∧ hdist q (epstein Ω ℓ') ≤ max Dk 0 := fun hq =>
    s03_qik_pt h hnl hsep hlab hD0 (fun q hq => (hDg q hq).trans (le_max_left _ _))
      (fun ws hws => (hDs ws hws).trans (le_max_left _ _)) hq
  have hlabS : ∀ b ∈ S, IsLabelledPt Ω Ωs lab b (ℓ b) := by
    intro b hb
    rcases hS.2.2.2 b hb with ⟨h1, h2⟩ | ⟨⟨z, hz, hzb⟩, h2⟩
    · exact Or.inl ⟨h1, h2.symm⟩
    · exact Or.inr (Or.inl ⟨z, hz, hzb.symm, h2⟩)
  have hup := (s03_qi_upper K Ω Ωs h hnl).1
  refine ⟨fun q hq hqD => ?_, fun p hp b hb q hq hqb => ?_⟩
  · obtain ⟨hwΩ, hqU, hqX⟩ := hpt (Or.inr (Or.inr ⟨hq, rfl⟩) : IsLabelledPt Ω Ωs lab q (lab q))
    have hXU : epstein Ω (lab q) ∈ UHS := s04_tb_ep_uhs hΩ hwΩ
    have hcase : ¬ ENNReal.ofReal 2 < hsetDist (epstein Ω (lab q)) (badSet Ω Ωs η R) ∨
        ∃ b ∈ S, poincareDist Ω (lab q) (ℓ b) ≤ 2 := by
      by_cases h2 : ENNReal.ofReal 2 < hsetDist (epstein Ω (lab q)) (badSet Ω Ωs η R)
      · by_cases h3 : ∃ b ∈ S, poincareDist Ω (lab q) (ℓ b) ≤ 2
        · exact Or.inr h3
        · exact absurd ⟨hwΩ, h2, fun b hb => not_le.1 fun h => h3 ⟨b, hb, h⟩⟩ hqD
      · exact Or.inl h2
    rcases hcase with h2 | ⟨b, hb, hdb⟩
    · have hlt : hsetDist (epstein Ω (lab q)) (badSet Ω Ωs η R) < ENNReal.ofReal 3 :=
        lt_of_le_of_lt (not_lt.1 h2) ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num))
      simp only [hsetDist, iInf_lt_iff] at hlt
      obtain ⟨x, hx, hxlt⟩ := hlt
      have hx3 : hdist (epstein Ω (lab q)) x < 3 :=
        (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).1 hxlt
      have hxU : x ∈ UHS := by
        rcases hx.1 with ⟨w', hw', rfl⟩ | ⟨z, hz, rfl⟩
        · exact s04_tb_ep_uhs hΩ hw'
        · exact s04_tb_ep_uhs hΩs hz
      obtain ⟨b, hb, hxb⟩ := hS.2.2.1 x hx
      have hbU : b ∈ UHS := (hpt (hlabS b hb)).2.1
      refine ⟨b, hb, hqU, ?_⟩
      rw [s02_hdist_comm]
      have t1 := s02_hdist_triangle hqU hXU hbU
      have t2 := s02_hdist_triangle hXU hxU hbU
      linarith
    · have hbU : b ∈ UHS := (hpt (hlabS b hb)).2.1
      have hℓΩ : ℓ b ∈ Ω := (hpt (hlabS b hb)).1
      have hXb : epstein Ω (ℓ b) ∈ UHS := s04_tb_ep_uhs hΩ hℓΩ
      have h1 := hup _ hwΩ _ hℓΩ
      have h2' := (hpt (hlabS b hb)).2.2
      rw [s02_hdist_comm] at h2'
      refine ⟨b, hb, hqU, ?_⟩
      rw [s02_hdist_comm]
      have t1 := s02_hdist_triangle hqU hXU hbU
      have t2 := s02_hdist_triangle hXU hXb hbU
      linarith
  · have hq' : IsLabelledPt Ω Ωs lab q (lab q) := Or.inr (Or.inr ⟨hq, rfl⟩)
    have hqq := hlabd lab hlab q b (lab q) (ℓ b) (2 * max Dk 0 + 5) hq' (hlabS b hb)
      (by rw [s02_hdist_comm]; exact hqb.2)
    have hk := eq_kernel_lip_b hΩ hp (hpt hq').1 (hpt (hlabS b hb)).1
    exact hk.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hqq) (sq_nonneg _))

/-- BR3: Lemma 5.11 in uniform form (every `η ≤ η₀`, `R ≥ R₁`; `C` depends on `K` only). -/
theorem s05_br_unif : ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ≥0, ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ η R : ℝ, 0 < η → η ≤ η₀ → R₁ ≤ R →
      ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
      ¬ IsLinePair Ω Ωs → ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab →
        ∀ (S : Set (ℂ × ℝ)) (ℓ : ℂ × ℝ → ℂ), IsBadNet Ω Ωs lab η R S ℓ →
          ((badSet Ω Ωs η R).Nonempty → ∀ p ∈ Ω,
            ∫⁻ q in gap Ω Ωs \ slabRegion Ω Ωs (goodDomainD Ω Ωs η R S ℓ),
                ENNReal.ofReal (intrKernel Ω p (lab q)) ∂hvol ≤
              (C : ℝ≥0∞) * ∑' b : S, ENNReal.ofReal (intrKernel Ω p (ℓ b))) ∧
          (badSet Ω Ωs η R = ∅ → goodDomainD Ω Ωs η R S ℓ = Ω ∧
            gap Ω Ωs \ slabRegion Ω Ωs (goodDomainD Ω Ωs η R S ℓ) = ∅) := by
  intro K hK
  obtain ⟨R₂, Q, hcov⟩ := s05_br_cover K hK
  refine ⟨Real.toNNReal (Real.exp Q * (64 * π * Real.cosh R₂ ^ 6)), fun ε hε hε' => ?_⟩
  obtain ⟨η₀, hη₀, R₁, hR₁, hsr⟩ := s05_sr_unif K hK ε hε hε'
  refine ⟨η₀, hη₀, R₁, hR₁, fun η R hη hηle hR Ω Ωs hp hnl lab hlab S ℓ hS => ?_⟩
  have hR0 : 0 < R := hR₁.trans_le hR
  obtain ⟨hc1, hc2⟩ := hcov η R hη hR0 Ω Ωs hp hnl lab hlab S ℓ hS
  have hseq := (hsr η R hη hηle hR Ω Ωs hp hnl lab hlab S ℓ hS).1
  have hJ := s03_b0_jordanPair hp
  have hΩ := s02_jordanPair_riemannMap hJ
  have hΩs := s02_jordanPair_riemannMap (s03_b0_jordanPair (s03_qce_swap hp))
  have hlabΩ : ∀ q ∈ gap Ω Ωs, lab q ∈ Ω := fun q hq =>
    (hlab.2 q ⟨hq.1, fun h => hq.2 (Or.inl h)⟩).1
  refine ⟨fun _ p hp => ?_, fun hbad => ?_⟩
  · have hSU : S ⊆ UHS := by
      intro b hb
      rcases (hS.1 hb).1 with ⟨w', hw', rfl⟩ | ⟨z, hz, rfl⟩
      · exact s04_tb_ep_uhs hΩ hw'
      · exact s04_tb_ep_uhs hΩs hz
    have : Countable S := (s06_tl_countable hSU hS.2.1).to_subtype
    set f : ℂ × ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal (intrKernel Ω p (lab q)) with hf
    have hfm : Measurable f :=
      ENNReal.measurable_ofReal.comp ((s03_sc_meas hΩ hp).comp hlab.1)
    set c : S → ℝ≥0∞ := fun b => ENNReal.ofReal (Real.exp Q * intrKernel Ω p (ℓ b)) with hc
    set T : S → Set (ℂ × ℝ) := fun b => hball b R₂ ∩ {q | f q ≤ c b} with hT
    have hTm : ∀ b, MeasurableSet (T b) := fun b =>
      (s05_pk_hball_meas _ R₂).inter (measurableSet_le hfm measurable_const)
    have hdiff : gap Ω Ωs \ slabRegion Ω Ωs (goodDomainD Ω Ωs η R S ℓ) ⊆ ⋃ b, T b := by
      intro q hq
      have hqD : lab q ∉ goodDomainD Ω Ωs η R S ℓ := fun h => hq.2 (hseq ▸ ⟨hq.1, h⟩)
      obtain ⟨b, hb, hqb⟩ := hc1 q hq.1 hqD
      exact mem_iUnion.2 ⟨⟨b, hb⟩, hqb,
        ENNReal.ofReal_le_ofReal (hc2 p hp b hb q hq.1 hqb)⟩
    have hk0 : ∀ w, 0 ≤ intrKernel Ω p w := fun w => sq_nonneg _
    calc ∫⁻ q in gap Ω Ωs \ slabRegion Ω Ωs (goodDomainD Ω Ωs η R S ℓ), f q ∂hvol
        ≤ ∫⁻ q in ⋃ b, T b, f q ∂hvol := lintegral_mono_set hdiff
      _ ≤ ∑' b, ∫⁻ q in T b, f q ∂hvol := lintegral_iUnion_le _ _
      _ ≤ ∑' b : S, ENNReal.ofReal (Real.exp Q * (64 * π * Real.cosh R₂ ^ 6)) *
            ENNReal.ofReal (intrKernel Ω p (ℓ b)) := by
          refine tsum_le_tsum fun b => ?_
          have hbU : (b : ℂ × ℝ) ∈ UHS := hSU b.2
          calc ∫⁻ q in T b, f q ∂hvol ≤ ∫⁻ _ in T b, c b ∂hvol :=
                setLIntegral_mono' (hTm b) fun q hq => hq.2
            _ = c b * hvol (T b) := setLIntegral_const _ _
            _ ≤ c b * ENNReal.ofReal (64 * π * Real.cosh R₂ ^ 6) := by
                gcongr
                exact (measure_mono inter_subset_left).trans (s05_pk_hvol_le hbU R₂)
            _ = _ := by
                rw [hc]
                simp only
                rw [← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos Q).le (hk0 _)),
                  ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Real.exp Q * (64 * π * Real.cosh R₂ ^ 6))]
                congr 1
                ring
      _ = _ := ENNReal.tsum_mul_left
  · have hS0 : S = ∅ := subset_empty_iff.1 (hbad ▸ hS.1)
    have hDΩ : goodDomainD Ω Ωs η R S ℓ = Ω := by
      ext w
      refine ⟨fun hw => hw.1, fun hw => ⟨hw, ?_, fun b hb => ?_⟩⟩
      · rw [hbad]
        simp [hsetDist]
      · rw [hS0] at hb
        simp at hb
    refine ⟨hDΩ, sdiff_eq_empty.2 fun q hq => ?_⟩
    rw [hseq, hDΩ]
    exact ⟨hq, hlabΩ q hq⟩

/-- **The slab identity** (sec05-upper.tex:597–610).  `𝒮_D = 𝒩 ∩ w⁻¹(D)` for every label, and
`(w, τ) ↦ E(w, τ)` is injective on `{(w, τ) : w ∈ D, 0 < τ < t(w)}`. -/
theorem slab_region_eq : ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ η : ℝ, 0 < η ∧ η < ε ∧ ∃ R : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
      ¬ IsLinePair Ω Ωs → ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab →
        ∀ (S : Set (ℂ × ℝ)) (ℓ : ℂ × ℝ → ℂ), IsBadNet Ω Ωs lab η R S ℓ →
          slabRegion Ω Ωs (goodDomainD Ω Ωs η R S ℓ) =
              gap Ω Ωs ∩ lab ⁻¹' goodDomainD Ω Ωs η R S ℓ ∧
            InjOn (normalMap Ω) {x | x.1 ∈ goodDomainD Ω Ωs η R S ℓ ∧ 0 < x.2 ∧
              x.2 < slabTop Ω Ωs x.1} := by
  intro K hK ε hε hε'
  obtain ⟨η₀, hη₀, R₁, -, h⟩ := s05_sr_unif K hK ε hε hε'
  have hm : 0 < min η₀ (ε / 2) := lt_min hη₀ (by linarith)
  exact ⟨min η₀ (ε / 2), hm, (min_le_right _ _).trans_lt (by linarith), R₁,
    h _ R₁ hm (min_le_left _ _) le_rfl⟩

/-- **Lemma 5.11** (`lem:bad-region`, sec05-upper.tex:612).  If `𝔅 ≠ ∅`, then for every `p ∈ Ω`,
`∫_{𝒩 ∖ 𝒮_D} k_p(w(q)) dvol(q) ≤ C(K) ∑ᵢ k_p(ℓᵢ)` (5.18).  If `𝔅 = ∅`, then `D = Ω` and
`𝒩 ∖ 𝒮_D = ∅`. -/
theorem lem_bad_region : ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ≥0, ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ η : ℝ, 0 < η ∧ η < ε ∧ ∃ R : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
      ¬ IsLinePair Ω Ωs → ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab →
        ∀ (S : Set (ℂ × ℝ)) (ℓ : ℂ × ℝ → ℂ), IsBadNet Ω Ωs lab η R S ℓ →
          ((badSet Ω Ωs η R).Nonempty → ∀ p ∈ Ω,
            ∫⁻ q in gap Ω Ωs \ slabRegion Ω Ωs (goodDomainD Ω Ωs η R S ℓ),
                ENNReal.ofReal (intrKernel Ω p (lab q)) ∂hvol ≤
              (C : ℝ≥0∞) * ∑' b : S, ENNReal.ofReal (intrKernel Ω p (ℓ b))) ∧
          (badSet Ω Ωs η R = ∅ → goodDomainD Ω Ωs η R S ℓ = Ω ∧
            gap Ω Ωs \ slabRegion Ω Ωs (goodDomainD Ω Ωs η R S ℓ) = ∅) := by
  intro K hK
  obtain ⟨C, h⟩ := s05_br_unif K hK
  refine ⟨C, fun ε hε hε' => ?_⟩
  obtain ⟨η₀, hη₀, R₁, -, h'⟩ := h ε hε hε'
  have hm : 0 < min η₀ (ε / 2) := lt_min hη₀ (by linarith)
  exact ⟨min η₀ (ε / 2), hm, (min_le_right _ _).trans_lt (by linarith), R₁,
    h' _ R₁ hm (min_le_left _ _) le_rfl⟩

/-! ## §5.8 The barrier

Context: `ε` is fixed so small that `C₀ C₁ ε ≤ 1/8` (sec05-upper.tex:458); this is rendered as
"for all `ε ∈ (0, ε₀]`" for some `ε₀ > 0`.  `C_b = ε e^{β R_b}`, `β = 3/2`, with `R_b` from
Lemma 5.8 (b); `𝓛 = graphOp`. -/

/-! ## §5.8 (interface EBTB, w3): the barrier and the bound for `t`, uniformly in `(η, R)`

`s05_tu_sigma` (moved here from the TU draft: `eq_t_bound` needs it): `σ` is smooth on `G₀` with
`0 ≤ σ ≤ 2/3`.  `s05_eb_dom`: if `∑ᵢ k_p(ℓᵢ) < ∞`, the terms `e^{-β d_ρ(·, ℓᵢ)}` are dominated
near every point of `Ω` by a summable sequence (`e^{-βd} ≤ e^{-d} ≤ e^{d_ρ(p, ·)} k_p(ℓᵢ)`,
`eq_kernel_exp`, triangle inequality).  `s05_eb_phi`: Euclidean first and second derivative bounds
`≤ M φ_ℓ` for `φ_ℓ = e^{-β d_ρ(·, ℓ)}` where `d_ρ(·, ℓ) > 2`, locally uniformly in `ℓ` (from
`lem_test_functions_b` and local bounds on `λ`, `∇ log λ`).  `s05_eb_series`: a series of `C²`
functions whose values and first two derivatives are locally dominated by a summable sequence is
`C²`, and `𝓛` commutes with the sum.  `s05_eb_unif`: (5.20)–(5.21) for all `η ≤ η₀`, `R ≥ R₁`
(`𝓛b ≥ b` by `lem_test_functions_b` with `11 C₁ε ≤ 1/4`; the boundary inequality by
`lem_good_domain_b`, `b(w_b) ≥ ε > t(w_b)`).  `s05_dinv_nonneg`: a Dirichlet inverse of a
nonnegative source is nonnegative.  `s05_tb_unif`: (5.22) for all `η ≤ η₀`, `R ≥ R₁` and every
nonnegative Dirichlet inverse (`lem_comparison` applied to `t - b - G`). -/

/-- TU2 helper: `s²` is `C^∞` on `Ω`. -/
theorem s05_tu_s2 {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) :
    ContDiffOn ℝ ∞ (fun z => schwarzNorm Ω z ^ 2) Ω := by
  have hl : ContDiffOn ℝ ∞ (poincareDensity Ω) Ω := s02_contDiffOn_poincareDensity hf
  have hS : ContDiffOn ℝ ∞ (schwarzian (Function.invFunOn f unitDisc)) Ω :=
    (s02_contDiffOn_invFun hf).2.2.2
  have hR : ContDiffOn ℝ ∞ (fun z => (schwarzian (Function.invFunOn f unitDisc) z).re) Ω :=
    (Complex.reCLM.contDiff.comp_contDiffOn hS).congr (fun z _ => by simp)
  have hI : ContDiffOn ℝ ∞ (fun z => (schwarzian (Function.invFunOn f unitDisc) z).im) Ω :=
    (Complex.imCLM.contDiff.comp_contDiffOn hS).congr (fun z _ => by simp)
  have hl0 : ∀ z ∈ Ω, poincareDensity Ω z ≠ 0 :=
    fun z hz => (s02_poincareDensity_pos ⟨f, hf⟩ hz).ne'
  refine ((hR.mul hR).add (hI.mul hI)).div (hl.pow 4) (fun z hz => pow_ne_zero 4 (hl0 z hz))
    |>.congr (fun z hz => ?_)
  have hl' := hl0 z hz
  rw [eq_def_s hf hz, div_pow, Complex.sq_norm, Complex.normSq_apply]
  simp only [Pi.div_apply]
  ring

/-- TU2 helper: `x²/(1-x²) ∈ [0, 1/3]` for `0 ≤ x ≤ 1/2`. -/
theorem s05_tu_hbd {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    0 ≤ x ^ 2 / (1 - x ^ 2) ∧ x ^ 2 / (1 - x ^ 2) ≤ 1 / 3 := by
  have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
  have hd : 0 < 1 - x ^ 2 := by linarith
  refine ⟨div_nonneg (sq_nonneg _) hd.le, ?_⟩
  rw [div_le_iff₀ hd]
  linarith

/-- TU2: `σ` is smooth on `G₀` with `0 ≤ σ ≤ 2/3` (`s, s* ∘ N < 1/2`). -/
theorem s05_tu_sigma : ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ R₁ : ℝ, ∀ η R : ℝ, 0 < η → η ≤ η₀ → R₁ ≤ R →
      ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
        ContDiffOn ℝ ∞ (sigmaSrc Ω Ωs) (goodSet Ω Ωs η R) ∧
          ∀ w ∈ goodSet Ω Ωs η R, 0 ≤ sigmaSrc Ω Ωs w ∧ sigmaSrc Ω Ωs w ≤ 2 / 3 := by
  intro K hK ε hε hε'
  obtain ⟨η₁, hη₁, R₂, hNu⟩ := s04_sl_eq_def_N_unif K hK ε hε hε'
  refine ⟨min η₁ (1 / 2), lt_min hη₁ (by norm_num), max R₂ 1,
    fun η R hη hηle hR Ω Ωs hp hnl => ?_⟩
  have hη1 : η ≤ η₁ := hηle.trans (min_le_left _ _)
  have hη2 : η ≤ 1 / 2 := hηle.trans (min_le_right _ _)
  have hR2 : R₂ ≤ R := (le_max_left _ _).trans hR
  have hR1 : 1 ≤ R := (le_max_right _ _).trans hR
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap (s03_b0_jordanPair hp)
  obtain ⟨fs, hfs⟩ := s02_jordanPair_riemannMap (s03_b0_jordanPair (s03_qce_swap hp))
  obtain ⟨-, -, hNC, hNg⟩ := hNu η R hη hη1 hR2 Ω Ωs hp hnl
  have hs0 : ∀ (U : Set ℂ) (z : ℂ), 0 ≤ schwarzNorm U z := fun U z => Real.sSup_nonneg (fun r hr => by
    obtain ⟨f, z, -, -, -, rfl⟩ := hr
    positivity)
  -- both Schwarzian norms are `< η ≤ 1/2` on `G₀`
  have hlt : ∀ w ∈ goodSet Ω Ωs η R,
      schwarzNorm Ω w < η ∧ schwarzNorm Ωs (slabMap Ω Ωs w) < η := by
    intro w hw
    have hg := s04_tb_good_s hp hw
    have hnb := lem_normal_b ⟨f, hf⟩ hw.1
    obtain ⟨hNΩs, ht0, htε, hE⟩ := hNg w hw
    refine ⟨hg.1 w hw.1 (by
      rw [← hnb.2.2, hnb.2.1, sub_self, abs_zero]
      linarith), hg.2 _ hNΩs (by
      rw [hE, ← hnb.2.2, hnb.2.1, zero_sub, abs_neg, abs_of_pos ht0]
      linarith)⟩
  have hGΩ : goodSet Ω Ωs η R ⊆ Ω := fun w hw => hw.1
  have hmaps : MapsTo (slabMap Ω Ωs) (goodSet Ω Ωs η R) Ωs := fun w hw => (hNg w hw).1
  have hA : ContDiffOn ℝ ∞ (fun z => schwarzNorm Ω z ^ 2) (goodSet Ω Ωs η R) :=
    (s05_tu_s2 hf).mono hGΩ
  have hB : ContDiffOn ℝ ∞ (fun z => schwarzNorm Ωs (slabMap Ω Ωs z) ^ 2) (goodSet Ω Ωs η R) :=
    (s05_tu_s2 hfs).comp hNC hmaps
  refine ⟨?_, fun w hw => ?_⟩
  · have hAd : ∀ w ∈ goodSet Ω Ωs η R, 1 - schwarzNorm Ω w ^ 2 ≠ 0 := by
      intro w hw
      have h := (hlt w hw).1
      have := hs0 Ω w
      nlinarith
    have hBd : ∀ w ∈ goodSet Ω Ωs η R, 1 - schwarzNorm Ωs (slabMap Ω Ωs w) ^ 2 ≠ 0 := by
      intro w hw
      have h := (hlt w hw).2
      have := hs0 Ωs (slabMap Ω Ωs w)
      nlinarith
    refine ((hA.div (contDiffOn_const.sub hA) hAd).add
      (hB.div (contDiffOn_const.sub hB) hBd)).congr (fun w _ => ?_)
    rfl
  · obtain ⟨h1, h2⟩ := hlt w hw
    obtain ⟨a0, a1⟩ := s05_tu_hbd (hs0 Ω w) (by linarith)
    obtain ⟨b0, b1⟩ := s05_tu_hbd (hs0 Ωs (slabMap Ω Ωs w)) (by linarith)
    show 0 ≤ schwarzNorm Ω w ^ 2 / (1 - schwarzNorm Ω w ^ 2) +
        schwarzNorm Ωs (slabMap Ω Ωs w) ^ 2 / (1 - schwarzNorm Ωs (slabMap Ω Ωs w) ^ 2) ∧
      schwarzNorm Ω w ^ 2 / (1 - schwarzNorm Ω w ^ 2) +
        schwarzNorm Ωs (slabMap Ω Ωs w) ^ 2 / (1 - schwarzNorm Ωs (slabMap Ω Ωs w) ^ 2) ≤ 2 / 3
    constructor <;> linarith

/-- EB1 (domination): if `∑ᵢ k_p(ℓᵢ) < ∞`, every point of `Ω` has a ball in `Ω` on which
`e^{-β d_ρ(·, ℓᵢ)}` is bounded by a summable sequence. -/
theorem s05_eb_dom {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {S : Set (ℂ × ℝ)}
    {ℓ : ℂ × ℝ → ℂ} (hℓ : ∀ b ∈ S, ℓ b ∈ Ω) {p : ℂ} (hp : p ∈ Ω)
    (hfin : ∑' b : S, ENNReal.ofReal (intrKernel Ω p (ℓ b)) ≠ ⊤) :
    ∀ w ∈ Ω, ∃ r : ℝ, 0 < r ∧ ball w r ⊆ Ω ∧ ∃ u : S → ℝ, Summable u ∧
      ∀ b : S, ∀ x ∈ ball w r, Real.exp (-(3 / 2) * poincareDist Ω x (ℓ b)) ≤ u b := by
  intro w hw
  have hΩ := s02_jordanPair_riemannMap hJ
  obtain ⟨r, hr, hball⟩ :=
    Metric.eventually_nhds_iff_ball.mp (s05_poincareDist_eventually_lt hΩ hw one_pos)
  have hk : ∀ b : S, (ENNReal.ofReal (intrKernel Ω p (ℓ b))).toReal = intrKernel Ω p (ℓ b) :=
    fun b => ENNReal.toReal_ofReal (by unfold intrKernel; positivity)
  refine ⟨r, hr, fun y hy => (hball y hy).1,
    fun b => Real.exp (poincareDist Ω p w + 1) * intrKernel Ω p (ℓ b),
    ((ENNReal.summable_toReal hfin).congr hk).mul_left _, ?_⟩
  intro b x hx
  obtain ⟨hxΩ, hwx⟩ := hball x hx
  have hℓb := hℓ b b.2
  have d0 := s02_poincareDist_nonneg hΩ hxΩ hℓb
  have t1 := s02_poincareDist_triangle hΩ hp hxΩ hℓb
  have t2 := s02_poincareDist_triangle hΩ hp hw hxΩ
  have hke := (eq_kernel_exp (s02_poincareDist_nonneg hΩ hp hℓb)).1
  calc Real.exp (-(3 / 2) * poincareDist Ω x (ℓ b))
      ≤ Real.exp (poincareDist Ω p x + -poincareDist Ω p (ℓ b)) :=
        Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (poincareDist Ω p x) * Real.exp (-poincareDist Ω p (ℓ b)) := Real.exp_add _ _
    _ ≤ Real.exp (poincareDist Ω p w + 1) * intrKernel Ω p (ℓ b) :=
        mul_le_mul (Real.exp_le_exp.2 (by linarith)) hke (Real.exp_pos _).le (Real.exp_pos _).le

/-- EB2 helper: the operator norm of a real linear form on `ℂ` through the frame `1, i`. -/
theorem s05_eb_norm1 (L : ℂ →L[ℝ] ℝ) : ‖L‖ ≤ |L 1| + |L I| := by
  refine L.opNorm_le_bound (by positivity) fun z => ?_
  have hz : z = z.re • (1 : ℂ) + z.im • I := by
    apply Complex.ext <;> simp
  have e : L z = z.re * L 1 + z.im * L I := by
    conv_lhs => rw [hz]
    simp only [map_add, map_smul, smul_eq_mul]
  calc ‖L z‖ = |z.re * L 1 + z.im * L I| := by rw [e, Real.norm_eq_abs]
    _ ≤ |z.re| * |L 1| + |z.im| * |L I| := by rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ ‖z‖ * |L 1| + ‖z‖ * |L I| :=
        add_le_add (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (abs_nonneg _))
          (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (abs_nonneg _))
    _ = (|L 1| + |L I|) * ‖z‖ := by ring

/-- EB2 helper: the operator norm of a real bilinear form on `ℂ` through the frame `1, i`. -/
theorem s05_eb_norm2 (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :
    ‖B‖ ≤ |B 1 1| + |B 1 I| + |B I 1| + |B I I| := by
  refine B.opNorm_le_bound (by positivity) fun z => ?_
  have hz : z = z.re • (1 : ℂ) + z.im • I := by
    apply Complex.ext <;> simp
  have e : ∀ Y, B z Y = z.re * B 1 Y + z.im * B I Y := fun Y => by
    conv_lhs => rw [hz]
    simp only [map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul]
  have hb : ∀ Y, |B z Y| ≤ ‖z‖ * (|B 1 Y| + |B I Y|) := fun Y => by
    rw [e, mul_add]
    calc |z.re * B 1 Y + z.im * B I Y| ≤ |z.re| * |B 1 Y| + |z.im| * |B I Y| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ ‖z‖ * |B 1 Y| + ‖z‖ * |B I Y| :=
          add_le_add (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (abs_nonneg _))
            (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (abs_nonneg _))
  calc ‖B z‖ ≤ |B z 1| + |B z I| := s05_eb_norm1 (B z)
    _ ≤ ‖z‖ * (|B 1 1| + |B I 1|) + ‖z‖ * (|B 1 I| + |B I I|) := add_le_add (hb 1) (hb I)
    _ = (|B 1 1| + |B 1 I| + |B I 1| + |B I I|) * ‖z‖ := by ring

/-- EB2 helper: `‖Γ(X, Y)‖ ≤ 3 ‖∇ log λ‖ ‖X‖ ‖Y‖`. -/
theorem s05_eb_christoffel_le (Ω : Set ℂ) (w X Y : ℂ) :
    ‖rhoChristoffel Ω w X Y‖ ≤ 3 * ‖logDensityGrad Ω w‖ * ‖X‖ * ‖Y‖ := by
  have h1 : ∀ A B C : ℂ, ‖(((conj A * B).re : ℝ) : ℂ) * C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ := fun A B C => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc |(conj A * B).re| ≤ ‖conj A * B‖ := Complex.abs_re_le_norm _
      _ = ‖A‖ * ‖B‖ := by rw [norm_mul, Complex.norm_conj]
  unfold rhoChristoffel
  calc _ ≤ ‖(((conj (logDensityGrad Ω w) * X).re : ℝ) : ℂ) * Y +
        (((conj (logDensityGrad Ω w) * Y).re : ℝ) : ℂ) * X‖ +
        ‖(((conj X * Y).re : ℝ) : ℂ) * logDensityGrad Ω w‖ := norm_sub_le _ _
    _ ≤ ‖(((conj (logDensityGrad Ω w) * X).re : ℝ) : ℂ) * Y‖ +
        ‖(((conj (logDensityGrad Ω w) * Y).re : ℝ) : ℂ) * X‖ +
        ‖(((conj X * Y).re : ℝ) : ℂ) * logDensityGrad Ω w‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖logDensityGrad Ω w‖ * ‖X‖ * ‖Y‖ + ‖logDensityGrad Ω w‖ * ‖Y‖ * ‖X‖ +
        ‖X‖ * ‖Y‖ * ‖logDensityGrad Ω w‖ := add_le_add (add_le_add (h1 _ _ _) (h1 _ _ _)) (h1 _ _ _)
    _ = _ := by ring

/-- EB2 (derivative bounds of `φ_ℓ = e^{-β d_ρ(·, ℓ)}`): near every point of `D`, uniformly in
`ℓ`, `φ_ℓ` is `C²` where `d_ρ(·, ℓ) > 2`, with Euclidean derivative bounds `‖Dφ_ℓ‖, ‖D²φ_ℓ‖ ≤ Mφ_ℓ`. -/
theorem s05_eb_phi {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {D : Set ℂ} {ε' : ℝ}
    {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ}
    (hadm : IsAdmissibleOp Ω D ε' aUp bUp c) :
    ∀ w ∈ D, ∃ r : ℝ, 0 < r ∧ ball w r ⊆ D ∧ ∃ M : ℝ, ∀ ℓ ∈ Ω, ∀ x ∈ ball w r,
      2 < poincareDist Ω x ℓ →
        ContDiffAt ℝ 2 (fun y => Real.exp (-(3 / 2) * poincareDist Ω y ℓ)) x ∧
        ‖fderiv ℝ (fun y => Real.exp (-(3 / 2) * poincareDist Ω y ℓ)) x‖ ≤
          M * Real.exp (-(3 / 2) * poincareDist Ω x ℓ) ∧
        ‖fderiv ℝ (fderiv ℝ (fun y => Real.exp (-(3 / 2) * poincareDist Ω y ℓ))) x‖ ≤
          M * Real.exp (-(3 / 2) * poincareDist Ω x ℓ) := by
  intro w hw
  have hΩo := s05_jordan_isOpen hJ
  have hDΩ : D ⊆ Ω := hadm.2.2.2.1
  have hDo : IsOpen D := hadm.2.2.1
  obtain ⟨-, hls, hlpos⟩ := s05_density_smooth hJ
  have hgs := s05_logDensityGrad_smooth hΩo hls hlpos
  have hwΩ := hDΩ hw
  have hlc : ContinuousAt (poincareDensity Ω) w :=
    hls.continuousOn.continuousAt (hΩo.mem_nhds hwΩ)
  have hgc : ContinuousAt (logDensityGrad Ω) w :=
    hgs.continuousOn.continuousAt (hΩo.mem_nhds hwΩ)
  have hev : ∀ᶠ x in 𝓝 w, x ∈ D ∧ poincareDensity Ω x < poincareDensity Ω w + 1 ∧
      ‖logDensityGrad Ω x‖ < ‖logDensityGrad Ω w‖ + 1 :=
    (show ∀ᶠ x in 𝓝 w, x ∈ D from hDo.mem_nhds hw).and ((hlc.eventually_lt continuousAt_const (lt_add_one _)).and
      (hgc.norm.eventually_lt continuousAt_const (lt_add_one _)))
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set Λ := poincareDensity Ω w + 1 with hΛdef
  set Γ₀ := ‖logDensityGrad Ω w‖ + 1 with hΓdef
  have hΛ0 : 0 < Λ := by linarith [hlpos w hwΩ]
  have hΓ0 : 0 < Γ₀ := by positivity
  refine ⟨r, hr, fun x hx => (hb x hx).1, 3 * Λ + 4 * (4 * Λ ^ 2 + 9 * Λ * Γ₀), ?_⟩
  intro ℓ hℓ x hx hd2
  obtain ⟨hxD, hlx, hgx⟩ := hb x hx
  have hxΩ := hDΩ hxD
  set φ : ℂ → ℝ := fun y => Real.exp (-(3 / 2) * poincareDist Ω y ℓ) with hφdef
  -- smoothness: `φ = G ∘ k_ℓ` with `G(k) = ((1 - √(1-k))/√k)³` and `0 < k_ℓ(x) ≤ 3/4`
  obtain ⟨ψ, hψ, h1, -, hK, -⟩ := s05_kernel_riemann hJ hℓ
  have hΦ : φ = (fun k => ((1 - √(1 - k)) / √k) ^ 3) ∘ intrKernel Ω ℓ := by
    funext y
    obtain ⟨hs, hn⟩ := s05_tfb_dist hJ hℓ y
    simp only [hφdef, Function.comp, intrKernel]
    rw [hs, s05_tfb_G_eq hn]
  have hKs : ContDiffOn ℝ ∞ (intrKernel Ω ℓ) Ω :=
    (contDiffOn_const.sub (((hψ.contDiffOn hΩo).restrict_scalars ℝ).norm_sq ℝ)).congr hK
  have hK0 : 0 < intrKernel Ω ℓ x := by
    rw [hK x hxΩ]; nlinarith [h1 x hxΩ, norm_nonneg (ψ x)]
  have hK34 : intrKernel Ω ℓ x ≤ 3 / 4 := by
    rw [intrKernel, ← (s05_tfb_dist hJ hℓ x).1]
    have hc : 6 / 5 ≤ Real.cosh (poincareDist Ω x ℓ / 2) := by
      rw [Real.cosh_eq]
      have := Real.exp_le_exp.2 (show (1 : ℝ) ≤ poincareDist Ω x ℓ / 2 by linarith)
      have := Real.exp_one_gt_d9
      have := Real.exp_pos (-(poincareDist Ω x ℓ / 2))
      linarith
    rw [inv_pow]
    calc (Real.cosh (poincareDist Ω x ℓ / 2) ^ 2)⁻¹ ≤ (36 / 25)⁻¹ :=
          inv_anti₀ (by norm_num) (by nlinarith)
      _ ≤ 3 / 4 := by norm_num
  have hK1 : 1 - intrKernel Ω ℓ x ≠ 0 := by linarith
  have hG : ContDiffAt ℝ 2 (fun k : ℝ => ((1 - √(1 - k)) / √k) ^ 3) (intrKernel Ω ℓ x) :=
    ((contDiffAt_const.sub ((contDiffAt_const.sub contDiffAt_id).sqrt hK1)).div (contDiffAt_id.sqrt hK0.ne')
      (Real.sqrt_pos.2 hK0).ne').pow 3
  have hC : ContDiffAt ℝ 2 φ x := by
    rw [hΦ]
    exact hG.comp x ((hKs.contDiffAt (hΩo.mem_nhds hxΩ)).of_le (by simp))
  refine ⟨hC, ?_⟩
  -- the `ρ`-bounds of Lemma 5.3 (b), read in the frame
  obtain ⟨hn1, hn2, -⟩ := lem_test_functions_b Ω Ωs hJ D ε' aUp bUp c hadm ℓ hℓ x hxD hd2
  have hl0 := hlpos x hxΩ
  have hφ0 : 0 < φ x := Real.exp_pos _
  have f0 : frameVec 0 = 1 := rfl
  have f1 : frameVec 1 = I := rfl
  have c1 : ∀ j : Fin 2, |fderiv ℝ φ x (frameVec j)| ≤ 3 / 2 * φ x * poincareDensity Ω x := by
    intro j
    unfold rhoTensorNorm at hn1
    rw [div_le_iff₀ (pow_pos hl0 _), pow_one] at hn1
    refine le_trans (Real.abs_le_sqrt ?_) hn1
    have := Finset.single_le_sum (f := fun idx : Fin (0 + 1) → Fin 2 =>
        (rhoCovDeriv Ω (scalarField φ) x fun i => frameVec (idx i)) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ (fun _ => j))
    convert this using 2
    simp [rhoCovDeriv, scalarField]
  have c2 : ∀ i j : Fin 2, |rhoHess Ω φ x ![frameVec i, frameVec j]| ≤
      4 * φ x * poincareDensity Ω x ^ 2 := by
    intro i j
    unfold rhoTensorNorm at hn2
    rw [div_le_iff₀ (pow_pos hl0 _)] at hn2
    refine le_trans (Real.abs_le_sqrt ?_) hn2
    have hidx : ![frameVec i, frameVec j] = fun k => frameVec ((![i, j] : Fin (0 + 2) → Fin 2) k) := by
      funext k; fin_cases k <;> rfl
    rw [hidx]
    exact Finset.single_le_sum (f := fun idx : Fin (0 + 2) → Fin 2 =>
        (rhoHess Ω φ x fun i => frameVec (idx i)) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
  have hlΛ : poincareDensity Ω x ≤ Λ := hlx.le
  have hl2 : poincareDensity Ω x ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hl0.le hlΛ 2
  -- first derivative
  have hD1 : ‖fderiv ℝ φ x‖ ≤ 3 * Λ * φ x := by
    have a0 := c1 0
    have a1 := c1 1
    rw [f0] at a0
    rw [f1] at a1
    calc ‖fderiv ℝ φ x‖ ≤ |fderiv ℝ φ x 1| + |fderiv ℝ φ x I| := s05_eb_norm1 _
      _ ≤ 3 / 2 * φ x * poincareDensity Ω x + 3 / 2 * φ x * poincareDensity Ω x := add_le_add a0 a1
      _ ≤ 3 * Λ * φ x := by nlinarith
  -- second derivative, through `D²φ = ∇²φ + Dφ(Γ)`
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hC.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have c3 : ∀ i j : Fin 2, |fderiv ℝ (fderiv ℝ φ) x (frameVec i) (frameVec j)| ≤
      (4 * Λ ^ 2 + 9 * Λ * Γ₀) * φ x := by
    intro i j
    have e := s05_hess_D2 (Ω := Ω) hd (frameVec i) (frameVec j)
    have hfv : ∀ k : Fin 2, ‖frameVec k‖ = 1 := Fin.forall_fin_two.2 ⟨by simp [f0], by simp [f1]⟩
    have hΓ : ‖rhoChristoffel Ω x (frameVec i) (frameVec j)‖ ≤ 3 * Γ₀ := by
      have := s05_eb_christoffel_le Ω x (frameVec i) (frameVec j)
      rw [hfv, hfv, mul_one, mul_one] at this
      linarith
    have hL : |fderiv ℝ φ x (rhoChristoffel Ω x (frameVec i) (frameVec j))| ≤
        3 * Λ * φ x * (3 * Γ₀) := by
      rw [← Real.norm_eq_abs]
      calc _ ≤ ‖fderiv ℝ φ x‖ * ‖rhoChristoffel Ω x (frameVec i) (frameVec j)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 3 * Λ * φ x * (3 * Γ₀) :=
            mul_le_mul hD1 hΓ (norm_nonneg _) (by positivity)
    have hH := c2 i j
    calc |fderiv ℝ (fderiv ℝ φ) x (frameVec i) (frameVec j)|
        = |rhoHess Ω φ x ![frameVec i, frameVec j] +
            fderiv ℝ φ x (rhoChristoffel Ω x (frameVec i) (frameVec j))| := by
          rw [e]; ring_nf
      _ ≤ |rhoHess Ω φ x ![frameVec i, frameVec j]| +
            |fderiv ℝ φ x (rhoChristoffel Ω x (frameVec i) (frameVec j))| := abs_add_le _ _
      _ ≤ 4 * φ x * Λ ^ 2 + 3 * Λ * φ x * (3 * Γ₀) := by nlinarith
      _ = (4 * Λ ^ 2 + 9 * Λ * Γ₀) * φ x := by ring
  have hD2 : ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ 4 * (4 * Λ ^ 2 + 9 * Λ * Γ₀) * φ x := by
    have b00 := c3 0 0
    have b01 := c3 0 1
    have b10 := c3 1 0
    have b11 := c3 1 1
    rw [f0] at b00 b01 b10
    rw [f1] at b01 b10 b11
    calc _ ≤ _ := s05_eb_norm2 _
      _ ≤ _ := add_le_add (add_le_add (add_le_add b00 b01) b10) b11
      _ = _ := by ring
  have hM1 : 0 ≤ 4 * (4 * Λ ^ 2 + 9 * Λ * Γ₀) := by positivity
  refine ⟨hD1.trans ?_, hD2.trans ?_⟩
  · nlinarith
  · nlinarith

/-- EB3 (series of `C²` functions): if the values and the first two derivatives of `fᵢ` are
dominated near every point of the open set `D` by a summable sequence, then `∑ᵢ fᵢ` is `C²` on
`D`, and `𝓛(∑ᵢ fᵢ) = ∑ᵢ 𝓛fᵢ` there (a summable series) for every operator of the form (5.2). -/
theorem s05_eb_series {ι : Type*} {f : ι → ℂ → ℝ} {D : Set ℂ} (hD : IsOpen D)
    (hf : ∀ i, ∀ x ∈ D, ContDiffAt ℝ 2 (f i) x)
    (hbd : ∀ w ∈ D, ∃ r : ℝ, 0 < r ∧ ball w r ⊆ D ∧ ∃ u : ι → ℝ, Summable u ∧
      ∀ i, ∀ x ∈ ball w r, |f i x| ≤ u i ∧ ‖fderiv ℝ (f i) x‖ ≤ u i ∧
        ‖fderiv ℝ (fderiv ℝ (f i)) x‖ ≤ u i) :
    ContDiffOn ℝ 2 (fun x => ∑' i, f i x) D ∧
      ∀ (Ω : Set ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
        ∀ w ∈ D, Summable (fun i => ellOp Ω aUp bUp c (f i) w) ∧
          ellOp Ω aUp bUp c (fun x => ∑' i, f i x) w = ∑' i, ellOp Ω aUp bUp c (f i) w := by
  have hfd : ∀ i, ∀ x ∈ D, ContDiffAt ℝ 1 (fderiv ℝ (f i)) x := fun i x hx =>
    (hf i x hx).fderiv_right (by norm_num)
  have hfdd : ∀ i, ∀ x ∈ D, ContinuousAt (fderiv ℝ (fderiv ℝ (f i))) x := fun i x hx =>
    ((hfd i x hx).fderiv_right (m := 0) (by norm_num)).continuousAt
  have hD1 : ∀ x ∈ D, HasFDerivAt (fun y => ∑' i, f i y) (∑' i, fderiv ℝ (f i) x) x := by
    intro x hx
    obtain ⟨r, hr, hrD, u, hu, hb⟩ := hbd x hx
    exact hasFDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball x r).isPreconnected
      (fun i y hy => ((hf i y (hrD hy)).differentiableAt (by norm_num)).hasFDerivAt)
      (fun i y hy => (hb i y hy).2.1) (mem_ball_self hr)
      (Summable.of_norm_bounded hu fun i => by
        rw [Real.norm_eq_abs]; exact (hb i x (mem_ball_self hr)).1) (mem_ball_self hr)
  have hD2 : ∀ x ∈ D, HasFDerivAt (fun y => ∑' i, fderiv ℝ (f i) y)
      (∑' i, fderiv ℝ (fderiv ℝ (f i)) x) x := by
    intro x hx
    obtain ⟨r, hr, hrD, u, hu, hb⟩ := hbd x hx
    have hdf : ∀ i, ∀ y ∈ ball x r, DifferentiableAt ℝ (fderiv ℝ (f i)) y := fun i y hy =>
      (hfd i y (hrD hy)).differentiableAt (by norm_num)
    exact hasFDerivAt_tsum_of_isPreconnected (f := fun i => fderiv ℝ (f i))
      (f' := fun i y => fderiv ℝ (fderiv ℝ (f i)) y) hu isOpen_ball
      (convex_ball x r).isPreconnected (fun i y hy => (hdf i y hy).hasFDerivAt)
      (fun i y hy => (hb i y hy).2.2) (mem_ball_self hr)
      (Summable.of_norm_bounded hu fun i => (hb i x (mem_ball_self hr)).2.1) (mem_ball_self hr)
  have hDF : ∀ x ∈ D, fderiv ℝ (fun y => ∑' i, f i y) x = ∑' i, fderiv ℝ (f i) x :=
    fun x hx => (hD1 x hx).fderiv
  have hD2' : ∀ x ∈ D, HasFDerivAt (fderiv ℝ (fun y => ∑' i, f i y))
      (∑' i, fderiv ℝ (fderiv ℝ (f i)) x) x := fun x hx =>
    (hD2 x hx).congr_of_eventuallyEq (Filter.eventually_of_mem (hD.mem_nhds hx) hDF)
  have hcont : ContinuousOn (fun x => ∑' i, fderiv ℝ (fderiv ℝ (f i)) x) D := by
    intro x hx
    obtain ⟨r, hr, hrD, u, hu, hb⟩ := hbd x hx
    have h := continuousOn_tsum (f := fun i y => fderiv ℝ (fderiv ℝ (f i)) y) (fun i y hy => (hfdd i y (hrD hy)).continuousWithinAt) hu
      (fun i y hy => (hb i y hy).2.2)
    exact (h.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))).continuousWithinAt
  refine ⟨?_, ?_⟩
  · rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hD]
    refine ⟨fun x hx => (hD1 x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hD]
    refine ⟨fun x hx => (hD2' x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact hcont.congr fun x hx => (hD2' x hx).fderiv
  · intro Ω aUp bUp c w hw
    obtain ⟨r, hr, -, u, hu, hb⟩ := hbd w hw
    have hw0 : w ∈ ball w r := mem_ball_self hr
    have s0 : Summable fun i => f i w := Summable.of_norm_bounded hu fun i => by
      rw [Real.norm_eq_abs]; exact (hb i w hw0).1
    have s1 : Summable fun i => fderiv ℝ (f i) w :=
      Summable.of_norm_bounded hu fun i => (hb i w hw0).2.1
    have s2 : Summable fun i => fderiv ℝ (fderiv ℝ (f i)) w :=
      Summable.of_norm_bounded (f := fun i => fderiv ℝ (fderiv ℝ (f i)) w) hu
        fun i => (hb i w hw0).2.2
    have hL : ∀ X, HasSum (fun i => fderiv ℝ (f i) w X) ((∑' i, fderiv ℝ (f i) w) X) := fun X =>
      (ContinuousLinearMap.apply ℝ ℝ X).hasSum s1.hasSum
    have hH : ∀ X Y, HasSum (fun i => fderiv ℝ (fderiv ℝ (f i)) w X Y)
        ((∑' i, fderiv ℝ (fderiv ℝ (f i)) w) X Y) := fun X Y =>
      (ContinuousLinearMap.apply ℝ ℝ Y).hasSum
        ((ContinuousLinearMap.apply ℝ (ℂ →L[ℝ] ℝ) X).hasSum s2.hasSum)
    have eF : ellOp Ω aUp bUp c (fun x => ∑' i, f i x) w =
        c w * (∑' i, f i w) - ∑ j : Fin 2, ∑ k : Fin 2, aUp w j k *
          ((∑' i, fderiv ℝ (fderiv ℝ (f i)) w) (frameVec j) (frameVec k) -
            (∑' i, fderiv ℝ (f i) w) (rhoChristoffel Ω w (frameVec j) (frameVec k))) -
          ∑ j : Fin 2, bUp w j * (∑' i, fderiv ℝ (f i) w) (frameVec j) := by
      simp only [ellOp, s05_hess_D2 (hD2' w hw).differentiableAt, (hD2' w hw).fderiv, hDF w hw]
    have ei : ∀ i, ellOp Ω aUp bUp c (f i) w =
        c w * f i w - ∑ j : Fin 2, ∑ k : Fin 2, aUp w j k *
          (fderiv ℝ (fderiv ℝ (f i)) w (frameVec j) (frameVec k) -
            fderiv ℝ (f i) w (rhoChristoffel Ω w (frameVec j) (frameVec k))) -
          ∑ j : Fin 2, bUp w j * fderiv ℝ (f i) w (frameVec j) := fun i => by
      simp only [ellOp, s05_hess_D2 ((hfd i w hw).differentiableAt (by norm_num))]
    have hs : HasSum (fun i => ellOp Ω aUp bUp c (f i) w)
        (ellOp Ω aUp bUp c (fun x => ∑' i, f i x) w) := by
      rw [eF]
      simp only [ei]
      exact ((s0.hasSum.mul_left (c w)).sub (hasSum_sum fun j _ => hasSum_sum fun k _ =>
        ((hH _ _).sub (hL _)).mul_left _)).sub (hasSum_sum fun j _ => (hL _).mul_left _)
    exact ⟨hs.summable, hs.tsum_eq.symm⟩

/-- EB4 helper: the labels of a bad net lie in `Ω`. -/
theorem s05_eb_label_mem {K : ℝ} {Ω Ωs : Set ℂ} (h : IsKQuasiPair Ω Ωs K)
    (hnl : ¬ IsLinePair Ω Ωs) {lab : ℂ × ℝ → ℂ} (hlab : IsLabel Ω lab) {η R : ℝ}
    {S : Set (ℂ × ℝ)} {ℓ : ℂ × ℝ → ℂ} (hS : IsBadNet Ω Ωs lab η R S ℓ) : ∀ b ∈ S, ℓ b ∈ Ω := by
  obtain ⟨A, B, Dk, hQK⟩ := prop_qi_QK K
  have hJ := s03_b0_jordanPair h
  obtain ⟨-, hDg, hDs, -⟩ := hQK Ω Ωs h hnl
  have hsep := (prop_separation_b hJ hnl).2
  intro b hb
  have hpt : IsLabelledPt Ω Ωs lab b (ℓ b) := by
    rcases hS.2.2.2 b hb with ⟨h1, h2⟩ | ⟨⟨z, hz, hzb⟩, h2⟩
    · exact Or.inl ⟨h1, h2.symm⟩
    · exact Or.inr (Or.inl ⟨z, hz, hzb.symm, h2⟩)
  exact (s03_qik_pt h hnl hsep hlab (le_max_right Dk 0)
    (fun q hq => (hDg q hq).trans (le_max_left _ _))
    (fun ws hws => (hDs ws hws).trans (le_max_left _ _)) hpt).1

/-- EB4 helper: `d_ρ(·, ℓ)` is continuous on `Ω`. -/
theorem s05_eb_dist_cont {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    {ℓ x : ℂ} (hℓ : ℓ ∈ Ω) (hx : x ∈ Ω) : ContinuousAt (fun y => poincareDist Ω y ℓ) x := by
  rw [Metric.continuousAt_iff']
  intro δ hδ
  filter_upwards [s05_poincareDist_eventually_lt hΩ hx hδ] with y hy
  obtain ⟨hyΩ, hxy⟩ := hy
  have t1 := s02_poincareDist_triangle hΩ hyΩ hx hℓ
  have t2 := s02_poincareDist_triangle hΩ hx hyΩ hℓ
  have hc := s02_poincareDist_comm hΩ hyΩ hx
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

/-- EB4 helper: `𝓛(s g) = s 𝓛g` for `g ∈ C²`. -/
theorem s05_eb_ellOp_smul {Ω : Set ℂ} (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (B : ℂ → Fin 2 → ℝ)
    (C : ℂ → ℝ) {g : ℂ → ℝ} {w : ℂ} (hg : ContDiffAt ℝ 2 g w) (s : ℝ) :
    ellOp Ω aUp B C (fun x => s * g x) w = s * ellOp Ω aUp B C g w := by
  have h := s05_ellOp_sub (Ω := Ω) aUp B C (f := fun _ => (0 : ℝ)) contDiffAt_const hg (-s)
  have h0 : ellOp Ω aUp B C (fun _ => (0 : ℝ)) w = 0 := by
    have hd : DifferentiableAt ℝ (fderiv ℝ (fun _ : ℂ => (0 : ℝ))) w := by simp
    simp [ellOp, s05_hess_D2 hd]
  have e : ellOp Ω aUp B C (fun x => s * g x) w =
      ellOp Ω aUp B C (fun x => (fun _ : ℂ => (0 : ℝ)) x - -s * g x) w := by
    simp only [zero_sub, neg_mul, neg_neg]
  rw [e, h, h0]
  ring

/-- EB (uniform (5.20)–(5.21)): `eq_barrier` for all `η ≤ η₀`, `R ≥ R₁`. -/
theorem s05_eb_unif : ∀ K : ℝ, 1 ≤ K → ∃ Rb : ℝ, 2 ≤ Rb ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε →
    ε ≤ ε₀ → ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < ε ∧ ∃ R₁ : ℝ, ∀ η R : ℝ, 0 < η → η ≤ η₀ → R₁ ≤ R →
      ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
      ¬ IsLinePair Ω Ωs → ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab →
        ∀ (S : Set (ℂ × ℝ)) (ℓ : ℂ × ℝ → ℂ), IsBadNet Ω Ωs lab η R S ℓ →
          (badSet Ω Ωs η R).Nonempty → ∀ p ∈ Ω, KH2 Ω Ωs lab p < ⊤ →
            ContDiffOn ℝ 2 (barrierFn Ω S ℓ (ε * Real.exp (3 / 2 * Rb)))
                (goodDomainD Ω Ωs η R S ℓ) ∧
            (∀ w ∈ goodDomainD Ω Ωs η R S ℓ,
              0 ≤ barrierFn Ω S ℓ (ε * Real.exp (3 / 2 * Rb)) w ∧
              barrierFn Ω S ℓ (ε * Real.exp (3 / 2 * Rb)) w ≤
                graphOp Ω Ωs (barrierFn Ω S ℓ (ε * Real.exp (3 / 2 * Rb))) w) ∧
            ∀ wb ∈ frontier (goodDomainD Ω Ωs η R S ℓ) ∩ Ω,
              Tendsto (fun w => slabTop Ω Ωs w - barrierFn Ω S ℓ (ε * Real.exp (3 / 2 * Rb)) w)
                  (𝓝[goodDomainD Ω Ωs η R S ℓ] wb)
                  (𝓝 (slabTop Ω Ωs wb - barrierFn Ω S ℓ (ε * Real.exp (3 / 2 * Rb)) wb)) ∧
                slabTop Ω Ωs wb - barrierFn Ω S ℓ (ε * Real.exp (3 / 2 * Rb)) wb < 0 := by
  intro K hK
  obtain ⟨Rb, hRb, hgd⟩ := lem_good_domain_b K hK
  obtain ⟨C₁, ε₁, hε₁, hgc⟩ := s05_gc_unif
  have hC0 : 0 < 44 * (|C₁| + 1) := by positivity
  refine ⟨Rb, hRb, min ε₁ (min (1 / 8) (1 / (44 * (|C₁| + 1)))),
    lt_min hε₁ (lt_min (by norm_num) (by positivity)), fun ε hε hεε => ?_⟩
  have hε1 : ε ≤ ε₁ := hεε.trans (min_le_left _ _)
  have hε4 : ε < 1 / 4 :=
    lt_of_le_of_lt (hεε.trans ((min_le_right _ _).trans (min_le_left _ _))) (by norm_num)
  have hεC : ε ≤ 1 / (44 * (|C₁| + 1)) := hεε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h11 : 11 * (C₁ * ε) ≤ 1 / 4 := by
    rw [le_div_iff₀ hC0] at hεC
    have := le_abs_self C₁
    nlinarith
  obtain ⟨η₂, hη₂, R₂, hR₂⟩ := hgc K hK ε hε hε4 hε1
  obtain ⟨η₃, hη₃, R₃, hN⟩ := s04_sl_eq_def_N_unif K hK ε hε hε4
  refine ⟨min (min η₂ η₃) (ε / 2), lt_min (lt_min hη₂ hη₃) (by linarith),
    lt_of_le_of_lt (min_le_right _ _) (by linarith), max (max R₂ R₃) 1, ?_⟩
  intro η R hη hηη₀ hR₁R Ω Ωs hQ hnl lab hlab S ℓ hS hne p hp hfin
  have hηη₂ : η ≤ η₂ := hηη₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hηη₃ : η ≤ η₃ := hηη₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hη4 : η < 1 / 4 := by linarith [hηη₀.trans (min_le_right _ _)]
  have hR₂R : R₂ ≤ R := ((le_max_left _ _).trans (le_max_left _ _)).trans hR₁R
  have hR₃R : R₃ ≤ R := ((le_max_right _ _).trans (le_max_left _ _)).trans hR₁R
  have hR0 : 0 < R := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hR₁R)
  have hJ := s03_b0_jordanPair hQ
  have hΩ := s02_jordanPair_riemannMap hJ
  have hDo : IsOpen (goodDomainD Ω Ωs η R S ℓ) :=
    (eq_def_D K hK η R hη hR0 Ω Ωs hQ hnl lab hlab S ℓ hS).2.2
  have hDG := lem_good_domain_a K hK η R hη hR0 Ω Ωs hQ hnl lab hlab S ℓ hS
  have hDsub : goodDomainD Ω Ωs η R S ℓ ⊆ goodSet Ω Ωs η R := fun w hw =>
    hDG.2 (hDG.1 ⟨subset_closure hw, hw.1⟩)
  obtain ⟨-, hrep2, hadm⟩ := hR₂ η R hη hηη₂ hR₂R Ω Ωs hQ hnl _ hDo hDsub
  obtain ⟨hGo, htC, -, htN⟩ := hN η R hη hηη₃ hR₃R Ω Ωs hQ hnl
  obtain ⟨Cc, hCc⟩ := lem_counting K hK η R hη hη4 hR0
  have hsf : ∑' b : S, ENNReal.ofReal (intrKernel Ω p (ℓ b)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin.ne)
      (hCc Ω Ωs hQ hnl lab hlab S ℓ hS hne p hp)
  have hℓ := s05_eb_label_mem hQ hnl hlab hS
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, ε * Real.exp (3 / 2 * Rb) = Cb := ⟨_, rfl⟩
  rw [hCb]
  have hCb0 : 0 < Cb := hCb ▸ mul_pos hε (Real.exp_pos _)
  have hDΩ : goodDomainD Ω Ωs η R S ℓ ⊆ Ω := hadm.2.2.2.1
  have hdom := s05_eb_dom hJ hℓ hp hsf
  have hphi := s05_eb_phi hJ hadm
  have hd2 : ∀ x ∈ goodDomainD Ω Ωs η R S ℓ, ∀ b : S, 2 < poincareDist Ω x (ℓ b) :=
    fun x hx b => hx.2.2 b b.2
  have hf : ∀ b : S, ∀ x ∈ goodDomainD Ω Ωs η R S ℓ,
      ContDiffAt ℝ 2 (fun y => Real.exp (-(3 / 2) * poincareDist Ω y (ℓ b))) x := by
    intro b x hx
    obtain ⟨r, hr, -, M, hM⟩ := hphi x hx
    exact (hM (ℓ b) (hℓ b b.2) x (mem_ball_self hr) (hd2 x hx b)).1
  have hbd : ∀ w ∈ goodDomainD Ω Ωs η R S ℓ, ∃ r : ℝ, 0 < r ∧
      ball w r ⊆ goodDomainD Ω Ωs η R S ℓ ∧ ∃ u : S → ℝ, Summable u ∧
      ∀ b : S, ∀ x ∈ ball w r, |Real.exp (-(3 / 2) * poincareDist Ω x (ℓ b))| ≤ u b ∧
        ‖fderiv ℝ (fun y => Real.exp (-(3 / 2) * poincareDist Ω y (ℓ b))) x‖ ≤ u b ∧
        ‖fderiv ℝ (fderiv ℝ (fun y => Real.exp (-(3 / 2) * poincareDist Ω y (ℓ b)))) x‖ ≤
          u b := by
    intro w hw
    obtain ⟨r₁, hr₁, hr₁D, M, hM⟩ := hphi w hw
    obtain ⟨r₂, hr₂, -, u, hu, hub⟩ := hdom w (hDΩ hw)
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂, (ball_subset_ball (min_le_left _ _)).trans hr₁D,
      fun b => max M 1 * u b, hu.mul_left _, ?_⟩
    intro b x hx
    have hx1 : x ∈ ball w r₁ := ball_subset_ball (min_le_left _ _) hx
    have hx2 : x ∈ ball w r₂ := ball_subset_ball (min_le_right _ _) hx
    obtain ⟨-, h1, h2⟩ := hM (ℓ b) (hℓ b b.2) x hx1 (hd2 x (hr₁D hx1) b)
    have hu1 := hub b x hx2
    have hφ0 : 0 < Real.exp (-(3 / 2) * poincareDist Ω x (ℓ b)) := Real.exp_pos _
    have hM1 : M ≤ max M 1 := le_max_left _ _
    have h1M : 1 ≤ max M 1 := le_max_right _ _
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_of_pos hφ0]; nlinarith
    · nlinarith [norm_nonneg (fderiv ℝ (fun y => Real.exp (-(3 / 2) * poincareDist Ω y (ℓ b))) x)]
    · nlinarith [norm_nonneg
        (fderiv ℝ (fderiv ℝ (fun y => Real.exp (-(3 / 2) * poincareDist Ω y (ℓ b)))) x)]
  obtain ⟨hC2, hL⟩ := s05_eb_series
    (f := fun (b : S) (x : ℂ) => Real.exp (-(3 / 2) * poincareDist Ω x (ℓ b))) hDo hf hbd
  have hC2' : ContDiffOn ℝ 2 (fun x => ∑' b : S, Real.exp (-(3 / 2) * poincareDist Ω x (ℓ b)))
      (goodDomainD Ω Ωs η R S ℓ) := hC2
  have hbC : ContDiffOn ℝ 2 (barrierFn Ω S ℓ Cb) (goodDomainD Ω Ωs η R S ℓ) :=
    contDiffOn_const.mul hC2'
  refine ⟨hbC, fun w hw => ?_, fun wb hwb => ?_⟩
  · obtain ⟨r, hr, -, u, hu, hub⟩ := hdom w (hDΩ hw)
    have hsφ : Summable fun b : S => Real.exp (-(3 / 2) * poincareDist Ω w (ℓ b)) :=
      Summable.of_nonneg_of_le (fun b => (Real.exp_pos _).le)
        (fun b => hub b w (mem_ball_self hr)) hu
    obtain ⟨hsL, heL⟩ := hL Ω (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).1
      (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).2.1
      (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).2.2 w hw
    have hterm : ∀ b : S, Real.exp (-(3 / 2) * poincareDist Ω w (ℓ b)) ≤
        ellOp Ω (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).1
          (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).2.1
          (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).2.2
          (fun x => Real.exp (-(3 / 2) * poincareDist Ω x (ℓ b))) w := fun b => by
      obtain ⟨-, -, h3, h4⟩ := lem_test_functions_b Ω Ωs hJ _ (C₁ * ε) _ _ _ hadm (ℓ b)
        (hℓ b b.2) w hw (hd2 w hw b)
      exact (h4 h11).trans h3
    have hsum := hsφ.tsum_le_tsum hterm hsL
    have hrep := hrep2 (barrierFn Ω S ℓ Cb) hbC w hw
    have hsm := s05_eb_ellOp_smul (Ω := Ω) (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).1
      (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).2.1
      (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).2.2
      (hC2'.contDiffAt (hDo.mem_nhds hw)) Cb
    refine ⟨mul_nonneg hCb0.le (tsum_nonneg fun b => (Real.exp_pos _).le), ?_⟩
    calc barrierFn Ω S ℓ Cb w
        = Cb * ∑' b : S, Real.exp (-(3 / 2) * poincareDist Ω w (ℓ b)) := rfl
      _ ≤ Cb * ∑' b : S, ellOp Ω (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).1
          (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).2.1
          (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).2.2
          (fun x => Real.exp (-(3 / 2) * poincareDist Ω x (ℓ b))) w :=
          mul_le_mul_of_nonneg_left hsum hCb0.le
      _ = Cb * ellOp Ω (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).1
          (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).2.1
          (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).2.2
          (fun x => ∑' b : S, Real.exp (-(3 / 2) * poincareDist Ω x (ℓ b))) w :=
          (congrArg (fun t => Cb * t) heL).symm
      _ = graphOp Ω Ωs (barrierFn Ω S ℓ Cb) w := hsm.symm.trans hrep.symm
  · have hwbΩ : wb ∈ Ω := hwb.2
    have hwbG : wb ∈ goodSet Ω Ωs η R := hDG.2 (hDG.1 ⟨frontier_subset_closure hwb.1, hwb.2⟩)
    have htc : ContinuousAt (slabTop Ω Ωs) wb :=
      htC.continuousOn.continuousAt (hGo.mem_nhds hwbG)
    obtain ⟨r, hr, hrΩ, u, hu, hub⟩ := hdom wb hwbΩ
    have hcont : ContinuousOn
        (fun x => ∑' b : S, Real.exp (-(3 / 2) * poincareDist Ω x (ℓ b))) (ball wb r) :=
      continuousOn_tsum (fun b x hx =>
          ((continuousAt_const.mul (s05_eb_dist_cont hΩ (hℓ b b.2) (hrΩ hx))).rexp).continuousWithinAt)
        hu (fun b x hx => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hub b x hx)
    have hbc : ContinuousAt (barrierFn Ω S ℓ Cb) wb :=
      continuousAt_const.mul (hcont.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr)))
    refine ⟨((htc.sub hbc).tendsto).mono_left nhdsWithin_le_nhds, ?_⟩
    obtain ⟨b0, hb0, hdb⟩ := hgd η R hη hR0 Ω Ωs hQ hnl lab hlab S ℓ hS wb hwb
    have hsφ : Summable fun b : S => Real.exp (-(3 / 2) * poincareDist Ω wb (ℓ b)) :=
      Summable.of_nonneg_of_le (fun b => (Real.exp_pos _).le)
        (fun b => hub b wb (mem_ball_self hr)) hu
    have hone : Real.exp (-(3 / 2) * poincareDist Ω wb (ℓ b0)) ≤
        ∑' b : S, Real.exp (-(3 / 2) * poincareDist Ω wb (ℓ b)) :=
      hsφ.le_tsum ⟨b0, hb0⟩ (fun _ _ => (Real.exp_pos _).le)
    have hle : Real.exp (-(3 / 2) * Rb) ≤ Real.exp (-(3 / 2) * poincareDist Ω wb (ℓ b0)) :=
      Real.exp_le_exp.2 (by linarith)
    have hge : ε ≤ barrierFn Ω S ℓ Cb wb := by
      calc ε = Cb * Real.exp (-(3 / 2) * Rb) := by
            rw [← hCb, mul_assoc, ← Real.exp_add, show 3 / 2 * Rb + -(3 / 2) * Rb = 0 by ring,
              Real.exp_zero, mul_one]
        _ ≤ Cb * ∑' b : S, Real.exp (-(3 / 2) * poincareDist Ω wb (ℓ b)) :=
            mul_le_mul_of_nonneg_left (hle.trans hone) hCb0.le
        _ = barrierFn Ω S ℓ Cb wb := rfl
    have htε := (htN wb hwbG).2.2.1
    linarith

/-- TB1 helper: admissibility restricts to open subsets. -/
theorem s05_tb_adm_mono {Ω D D' : Set ℂ} {ε' : ℝ} {aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ}
    {bUp : ℂ → Fin 2 → ℝ} {c : ℂ → ℝ} (h : IsAdmissibleOp Ω D ε' aUp bUp c) (hD' : IsOpen D')
    (hD'D : D' ⊆ D) : IsAdmissibleOp Ω D' ε' aUp bUp c := by
  obtain ⟨h1, h2, -, hDΩ, ⟨ha, hb, hc, hs⟩, hn⟩ := h
  have m : ∀ {k : ℕ} (j : ℕ) (T : TensorField k), rhoCjNorm Ω j T D' ≤ rhoCjNorm Ω j T D := by
    intro k j T
    unfold rhoCjNorm
    exact iSup_mono fun i => iSup_mono fun _ => biSup_mono fun w hw => hD'D hw
  refine ⟨h1, h2, hD', hD'D.trans hDΩ, ⟨fun i j => (ha i j).mono hD'D, fun i => (hb i).mono hD'D,
    hc.mono hD'D, fun w hw => hs w (hD'D hw)⟩, le_trans ?_ hn⟩
  exact add_le_add (add_le_add (m _ _) (m _ _)) (m _ _)

/-- TB1 helper: `𝓛0 = 0`. -/
theorem s05_tb_ellOp_zero (Ω : Set ℂ) (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (B : ℂ → Fin 2 → ℝ)
    (C : ℂ → ℝ) (w : ℂ) : ellOp Ω aUp B C (fun _ => (0 : ℝ)) w = 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ (fun _ : ℂ => (0 : ℝ))) w := by simp
  simp [ellOp, s05_hess_D2 hd]

/-- TB1 (nonnegativity of the Dirichlet inverse): if `𝓛` is admissible on `D` and `F ≥ 0`, every
`𝒢_D F` is `≥ 0` on `D` (the Dirichlet solutions on a smooth exhaustion are `≥ 0` by
`lem_comparison`, and increase to `𝒢_D F`). -/
theorem s05_dinv_nonneg : ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ∀ (D : Set ℂ) (ε' : ℝ)
    (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
    IsAdmissibleOp Ω D ε' aUp bUp c → ∀ (F : ℂ → ℝ) (M : ℝ), ContDiffOn ℝ ∞ F D →
      (∀ w ∈ D, 0 ≤ F w ∧ F w ≤ M) → ∀ G : ℂ → ℝ, IsDirichletInverse Ω aUp bUp c D F G →
        ∀ w ∈ D, 0 ≤ G w := by
  intro Ω Ωs hJ D ε' aUp bUp c hadm F M hF hFb G hG w hw
  obtain ⟨Dn, hDn⟩ := s05_smooth_exhaustion D hadm.2.2.1
  obtain ⟨un, hun⟩ := (prop_dirichlet_a Ω Ωs hJ D ε' aUp bUp c hadm F M hF hFb).1 Dn hDn
  -- the Dirichlet solutions are `≥ 0` (comparison applied to `-uₙ`)
  have hnn : ∀ n, ∀ x ∈ Dn n, 0 ≤ un n x := by
    intro n
    obtain ⟨hDo, hcpt, hcl, -⟩ := hDn.1 n
    have hsub : Dn n ⊆ D := subset_closure.trans hcl
    obtain ⟨hu, hL, hbd⟩ := hun n
    have hadm' := s05_tb_adm_mono hadm hDo hsub
    have hu2 : ContDiffOn ℝ 2 (fun x => -1 * un n x) (Dn n) :=
      ((hu.mono subset_closure).of_le (by simp)).const_smul (-1 : ℝ)
    have hcont : ContinuousOn (fun x => -1 * un n x) (closure (Dn n)) :=
      (hu.continuousOn.const_smul (-1 : ℝ))
    have hB : BddAbove ((fun x => -1 * un n x) '' Dn n) :=
      ((hcpt.image_of_continuousOn hcont).bddAbove).mono (image_mono subset_closure)
    have hF' : ∀ wb ∈ frontier (Dn n) ∩ Ω, ∀ δ : ℝ, 0 < δ →
        ∀ᶠ x in 𝓝[Dn n] wb, -1 * un n x ≤ δ := by
      intro wb hwb δ hδ
      have hwc : wb ∈ closure (Dn n) := frontier_subset_closure hwb.1
      have ht : Tendsto (fun x => -1 * un n x) (𝓝[Dn n] wb) (𝓝 (-1 * un n wb)) :=
        (hcont wb hwc).mono_left (nhdsWithin_mono wb subset_closure)
      have h0 : -1 * un n wb = 0 := by rw [hbd wb hwb.1]; ring
      rw [h0] at ht
      filter_upwards [ht.eventually (gt_mem_nhds hδ)] with x hx
      exact hx.le
    have hLv : ∀ x ∈ Dn n, ellOp Ω aUp bUp c (fun y => -1 * un n y) x ≤ 0 := by
      intro x hx
      rw [s05_eb_ellOp_smul aUp bUp c
        (((hu.mono subset_closure).contDiffAt (hDo.mem_nhds hx)).of_le (by simp)) (-1), hL x hx]
      linarith [(hFb x (hsub hx)).1]
    intro x hx
    have := (lem_comparison Ω Ωs hJ (Dn n) ε' aUp bUp c hadm' _ hu2 hB hF').1 hLv x hx
    linarith
  obtain ⟨-, hlim⟩ := hG.2.2 Dn hDn un hun w hw
  refine ge_of_tendsto' hlim fun n => ?_
  by_cases hwn : w ∈ Dn n
  · rw [indicator_of_mem hwn]; exact hnn n w hwn
  · rw [indicator_of_notMem hwn]

open Classical in
/-- TB (uniform (5.22)): `eq_t_bound` for all `η ≤ η₀`, `R ≥ R₁`, and every nonnegative
Dirichlet inverse `G` of `2σ`. -/
theorem s05_tb_unif : ∀ K : ℝ, 1 ≤ K → ∃ Rb : ℝ, 2 ≤ Rb ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε →
    ε ≤ ε₀ → ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < ε ∧ ∃ R₁ : ℝ, ∀ η R : ℝ, 0 < η → η ≤ η₀ → R₁ ≤ R →
      ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
      ¬ IsLinePair Ω Ωs → ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab →
        ∀ (S : Set (ℂ × ℝ)) (ℓ : ℂ × ℝ → ℂ), IsBadNet Ω Ωs lab η R S ℓ →
          ∀ p ∈ Ω, KH2 Ω Ωs lab p < ⊤ →
            ∀ G : ℂ → ℝ, IsDirichletInverse Ω (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).1
                (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).2.1
                (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).2.2
                (goodDomainD Ω Ωs η R S ℓ) (fun w => 2 * sigmaSrc Ω Ωs w) G →
              (∀ w ∈ goodDomainD Ω Ωs η R S ℓ, 0 ≤ G w) →
              ∀ w ∈ goodDomainD Ω Ωs η R S ℓ, slabTop Ω Ωs w ≤
                (if (badSet Ω Ωs η R).Nonempty then
                  barrierFn Ω S ℓ (ε * Real.exp (3 / 2 * Rb)) w else 0) + G w := by
  intro K hK
  obtain ⟨Rb, hRb, ε₀, hε₀, heb⟩ := s05_eb_unif K hK
  obtain ⟨C₁, ε₁, hε₁, hgc⟩ := s05_gc_unif
  refine ⟨Rb, hRb, min ε₀ (min ε₁ (1 / 8)), lt_min hε₀ (lt_min hε₁ (by norm_num)),
    fun ε hε hεε => ?_⟩
  have hε0 : ε ≤ ε₀ := hεε.trans (min_le_left _ _)
  have hε1 : ε ≤ ε₁ := hεε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε4 : ε < 1 / 4 := lt_of_le_of_lt (hεε.trans ((min_le_right _ _).trans (min_le_right _ _)))
    (by norm_num)
  obtain ⟨η₁, hη₁, hη₁ε, R₁, heb'⟩ := heb ε hε hε0
  obtain ⟨η₂, hη₂, R₂, hR₂⟩ := hgc K hK ε hε hε4 hε1
  obtain ⟨ηb, hηb, -, Rgb, hgb⟩ := s05_gb_unif K hK ε hε hε4
  obtain ⟨η₃, hη₃, R₃, hN⟩ := s04_sl_eq_def_N_unif K hK ε hε hε4
  refine ⟨min (min η₁ η₂) (min ηb η₃), lt_min (lt_min hη₁ hη₂) (lt_min hηb hη₃),
    lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) hη₁ε,
    max (max R₁ R₂) (max (max Rgb R₃) 1), ?_⟩
  intro η R hη hηη₀ hR₁R Ω Ωs hQ hnl lab hlab S ℓ hS p hp hfin G hG hG0 w hw
  have hηη₁ : η ≤ η₁ := hηη₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hηη₂ : η ≤ η₂ := hηη₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hηηb : η ≤ ηb := hηη₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηη₃ : η ≤ η₃ := hηη₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hR1 : R₁ ≤ R := ((le_max_left _ _).trans (le_max_left _ _)).trans hR₁R
  have hR2 : R₂ ≤ R := ((le_max_right _ _).trans (le_max_left _ _)).trans hR₁R
  have hRgb : Rgb ≤ R :=
    (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hR₁R
  have hR3 : R₃ ≤ R :=
    (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hR₁R
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (((le_max_right _ _).trans (le_max_right _ _)).trans hR₁R)
  have hJ := s03_b0_jordanPair hQ
  have hDo : IsOpen (goodDomainD Ω Ωs η R S ℓ) :=
    (eq_def_D K hK η R hη hR0 Ω Ωs hQ hnl lab hlab S ℓ hS).2.2
  have hDG := lem_good_domain_a K hK η R hη hR0 Ω Ωs hQ hnl lab hlab S ℓ hS
  have hDsub : goodDomainD Ω Ωs η R S ℓ ⊆ goodSet Ω Ωs η R := fun w hw =>
    hDG.2 (hDG.1 ⟨subset_closure hw, hw.1⟩)
  obtain ⟨-, hrep2, hadm⟩ := hR₂ η R hη hηη₂ hR2 Ω Ωs hQ hnl _ hDo hDsub
  obtain ⟨hGo, htC, -, htN⟩ := hN η R hη hηη₃ hR3 Ω Ωs hQ hnl
  obtain ⟨-, -, -, -, -, h2σ⟩ := hgb η R hη hηηb hRgb Ω Ωs hQ hnl
  have htC2 : ContDiffOn ℝ 2 (slabTop Ω Ωs) (goodDomainD Ω Ωs η R S ℓ) :=
    (htC.mono hDsub).of_le (by simp)
  obtain ⟨bf, hbf⟩ : ∃ bf : ℂ → ℝ, bf = fun x => if (badSet Ω Ωs η R).Nonempty then
      barrierFn Ω S ℓ (ε * Real.exp (3 / 2 * Rb)) x else 0 := ⟨_, rfl⟩
  -- the barrier term: `C²`, `≥ 0`, `𝓛b ≥ 0`, and `t - b < 0` near every finite boundary point
  have hpk : ContDiffOn ℝ 2 bf (goodDomainD Ω Ωs η R S ℓ) ∧
      (∀ x ∈ goodDomainD Ω Ωs η R S ℓ, 0 ≤ bf x ∧
        0 ≤ ellOp Ω (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).1
          (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).2.1
          (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).2.2 bf x) ∧
      ∀ wb ∈ frontier (goodDomainD Ω Ωs η R S ℓ) ∩ Ω,
        ∀ᶠ x in 𝓝[goodDomainD Ω Ωs η R S ℓ] wb, slabTop Ω Ωs x - bf x < 0 := by
    by_cases hne : (badSet Ω Ωs η R).Nonempty
    · have hb : bf = barrierFn Ω S ℓ (ε * Real.exp (3 / 2 * Rb)) :=
        hbf.trans (funext fun x => ite_eq_left hne)
      rw [hb]
      obtain ⟨e1, e2, e3⟩ := heb' η R hη hηη₁ hR1 Ω Ωs hQ hnl lab hlab S ℓ hS hne p hp hfin
      refine ⟨e1, fun x hx => ⟨(e2 x hx).1, ?_⟩, fun wb hwb => ?_⟩
      · rw [← hrep2 _ e1 x hx]
        exact (e2 x hx).1.trans (e2 x hx).2
      · exact (e3 wb hwb).1.eventually (gt_mem_nhds (e3 wb hwb).2)
    · have hb : bf = fun _ => 0 := hbf.trans (funext fun x => ite_eq_right hne)
      rw [hb]
      refine ⟨contDiffOn_const, fun x _ => ⟨le_rfl, (s05_tb_ellOp_zero _ _ _ _ _).symm.le⟩,
        fun wb hwb => ?_⟩
      -- `𝔅 = ∅`: then `D = Ω` is open, so it has no boundary point in `Ω`
      have hS0 : badSet Ω Ωs η R = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hwbD : wb ∈ goodDomainD Ω Ωs η R S ℓ := by
        refine ⟨hwb.2, by rw [hS0]; simp [hsetDist], fun b hb => ?_⟩
        have := hS.1 hb
        rw [hS0] at this
        simp at this
      have hfr := hwb.1
      rw [hDo.frontier_eq] at hfr
      exact absurd hwbD hfr.2
  obtain ⟨hbC, hbL, hbF⟩ := hpk
  -- comparison for `v = (t - b) - G`
  have hvC : ContDiffOn ℝ 2 (fun x => (slabTop Ω Ωs x - 1 * bf x) - 1 * G x)
      (goodDomainD Ω Ωs η R S ℓ) :=
    (htC2.sub (contDiffOn_const.mul hbC)).sub (contDiffOn_const.mul hG.1)
  have hvB : BddAbove ((fun x => (slabTop Ω Ωs x - 1 * bf x) - 1 * G x) ''
      goodDomainD Ω Ωs η R S ℓ) := by
    refine ⟨ε, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have := (htN x (hDsub hx)).2.2.1
    have := (hbL x hx).1
    have := hG0 x hx
    simp only
    linarith
  have hvF : ∀ wb ∈ frontier (goodDomainD Ω Ωs η R S ℓ) ∩ Ω, ∀ δ : ℝ, 0 < δ →
      ∀ᶠ x in 𝓝[goodDomainD Ω Ωs η R S ℓ] wb, (slabTop Ω Ωs x - 1 * bf x) - 1 * G x ≤ δ := by
    intro wb hwb δ hδ
    filter_upwards [hbF wb hwb, self_mem_nhdsWithin] with x hx hxD
    have := hG0 x hxD
    linarith
  have hvL : ∀ x ∈ goodDomainD Ω Ωs η R S ℓ,
      ellOp Ω (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).1
        (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).2.1
        (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).2.2
        (fun x => (slabTop Ω Ωs x - 1 * bf x) - 1 * G x) x ≤ 0 := by
    intro x hx
    have hxn := hDo.mem_nhds hx
    have ht : ContDiffAt ℝ 2 (slabTop Ω Ωs) x := htC2.contDiffAt hxn
    have hb2 : ContDiffAt ℝ 2 bf x := hbC.contDiffAt hxn
    have hG2 : ContDiffAt ℝ 2 G x := hG.1.contDiffAt hxn
    rw [s05_ellOp_sub _ _ _ (ht.sub (contDiffAt_const.mul hb2)) hG2 1,
      s05_ellOp_sub _ _ _ ht hb2 1, ← hrep2 _ htC2 x hx, h2σ x (hDsub hx), hG.2.1 x hx]
    linarith [(hbL x hx).2]
  have hcmp := (lem_comparison Ω Ωs hJ _ (C₁ * ε) _ _ _ hadm _ hvC hvB hvF).1 hvL w hw
  have hbw : bf w = if (badSet Ω Ωs η R).Nonempty then
      barrierFn Ω S ℓ (ε * Real.exp (3 / 2 * Rb)) w else 0 := by rw [hbf]
  have hcmp' : (slabTop Ω Ωs w - 1 * bf w) - 1 * G w ≤ 0 := hcmp
  linarith

/-- **(5.20)–(5.21)** (`eq:barrier-L`, `eq:barrier-boundary`, sec05-upper.tex:651–659).  Assume
`K_{H,2}(p) < ∞` and `𝔅 ≠ ∅`.  Then `b ∈ C²(D)`, `𝓛b ≥ b ≥ 0` on `D`, and for every
`w_b ∈ ∂D ∩ Ω`, `t - b` is continuous at `w_b` along `D` with `t(w_b) - b(w_b) < 0`. -/
theorem eq_barrier : ∀ K : ℝ, 1 ≤ K → ∃ Rb : ℝ, 2 ≤ Rb ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε →
    ε ≤ ε₀ → ∃ η : ℝ, 0 < η ∧ η < ε ∧ ∃ R : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
      ¬ IsLinePair Ω Ωs → ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab →
        ∀ (S : Set (ℂ × ℝ)) (ℓ : ℂ × ℝ → ℂ), IsBadNet Ω Ωs lab η R S ℓ →
          (badSet Ω Ωs η R).Nonempty → ∀ p ∈ Ω, KH2 Ω Ωs lab p < ⊤ →
            ContDiffOn ℝ 2 (barrierFn Ω S ℓ (ε * Real.exp (3 / 2 * Rb)))
                (goodDomainD Ω Ωs η R S ℓ) ∧
            (∀ w ∈ goodDomainD Ω Ωs η R S ℓ,
              0 ≤ barrierFn Ω S ℓ (ε * Real.exp (3 / 2 * Rb)) w ∧
              barrierFn Ω S ℓ (ε * Real.exp (3 / 2 * Rb)) w ≤
                graphOp Ω Ωs (barrierFn Ω S ℓ (ε * Real.exp (3 / 2 * Rb))) w) ∧
            ∀ wb ∈ frontier (goodDomainD Ω Ωs η R S ℓ) ∩ Ω,
              Tendsto (fun w => slabTop Ω Ωs w - barrierFn Ω S ℓ (ε * Real.exp (3 / 2 * Rb)) w)
                  (𝓝[goodDomainD Ω Ωs η R S ℓ] wb)
                  (𝓝 (slabTop Ω Ωs wb - barrierFn Ω S ℓ (ε * Real.exp (3 / 2 * Rb)) wb)) ∧
                slabTop Ω Ωs wb - barrierFn Ω S ℓ (ε * Real.exp (3 / 2 * Rb)) wb < 0 := by
  intro K hK
  obtain ⟨Rb, hRb, ε₀, hε₀, h⟩ := s05_eb_unif K hK
  refine ⟨Rb, hRb, ε₀, hε₀, fun ε hε hεε => ?_⟩
  obtain ⟨η₀, hη₀, hη₀ε, R₁, hR⟩ := h ε hε hεε
  exact ⟨η₀, hη₀, hη₀ε, R₁, hR η₀ R₁ hη₀ le_rfl le_rfl⟩

open Classical in
/-- **(5.22)** (`eq:t-bound`, sec05-upper.tex:678).  Assume `K_{H,2}(p) < ∞`.  On `D`,
`t ≤ b + 𝒢_D(2σ)`, where `𝒢_D` is the Dirichlet inverse of `𝓛` on `D` (`b = 0` if `𝔅 = ∅`). -/
theorem eq_t_bound : ∀ K : ℝ, 1 ≤ K → ∃ Rb : ℝ, 2 ≤ Rb ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε →
    ε ≤ ε₀ → ∃ η : ℝ, 0 < η ∧ η < ε ∧ ∃ R : ℝ, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
      ¬ IsLinePair Ω Ωs → ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab →
        ∀ (S : Set (ℂ × ℝ)) (ℓ : ℂ × ℝ → ℂ), IsBadNet Ω Ωs lab η R S ℓ →
          ∀ p ∈ Ω, KH2 Ω Ωs lab p < ⊤ →
            ∀ G : ℂ → ℝ, IsDirichletInverse Ω (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).1
                (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).2.1
                (graphCoeffs Ω Ωs (goodDomainD Ω Ωs η R S ℓ)).2.2
                (goodDomainD Ω Ωs η R S ℓ) (fun w => 2 * sigmaSrc Ω Ωs w) G →
              ∀ w ∈ goodDomainD Ω Ωs η R S ℓ, slabTop Ω Ωs w ≤
                (if (badSet Ω Ωs η R).Nonempty then
                  barrierFn Ω S ℓ (ε * Real.exp (3 / 2 * Rb)) w else 0) + G w := by
  intro K hK
  obtain ⟨Rb, hRb, ε₀, hε₀, h⟩ := s05_tb_unif K hK
  obtain ⟨C₁, ε₁, hε₁, hgc⟩ := s05_gc_unif
  refine ⟨Rb, hRb, min ε₀ (min ε₁ (1 / 8)), lt_min hε₀ (lt_min hε₁ (by norm_num)),
    fun ε hε hεε => ?_⟩
  have hε0 : ε ≤ ε₀ := hεε.trans (min_le_left _ _)
  have hε1 : ε ≤ ε₁ := hεε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε4 : ε < 1 / 4 := lt_of_le_of_lt (hεε.trans ((min_le_right _ _).trans (min_le_right _ _)))
    (by norm_num)
  obtain ⟨η₀, hη₀, hη₀ε, R₁, hR⟩ := h ε hε hε0
  obtain ⟨η₂, hη₂, R₂, hR₂⟩ := hgc K hK ε hε hε4 hε1
  obtain ⟨η₃, hη₃, R₃, hR₃⟩ := s05_tu_sigma K hK ε hε hε4
  set η := min η₀ (min η₂ η₃) with hηdef
  set R := max R₁ (max R₂ (max R₃ 1)) with hRdef
  have hη : 0 < η := lt_min hη₀ (lt_min hη₂ hη₃)
  have hηη₀ : η ≤ η₀ := min_le_left _ _
  have hηη₂ : η ≤ η₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hηη₃ : η ≤ η₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hR₁R : R₁ ≤ R := le_max_left _ _
  have hR₂R : R₂ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hR₃R : R₃ ≤ R := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hR0 : 0 < R := lt_of_lt_of_le one_pos
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
  refine ⟨η, hη, lt_of_le_of_lt hηη₀ hη₀ε, R, ?_⟩
  intro Ω Ωs hQ hnl lab hlab S ℓ hS p hp hfin G hG
  have hJ := s03_b0_jordanPair hQ
  have hDo := (eq_def_D K hK η R hη hR0 Ω Ωs hQ hnl lab hlab S ℓ hS).2.2
  have hDG := lem_good_domain_a K hK η R hη hR0 Ω Ωs hQ hnl lab hlab S ℓ hS
  have hDsub : goodDomainD Ω Ωs η R S ℓ ⊆ goodSet Ω Ωs η R := fun w hw =>
    hDG.2 (hDG.1 ⟨subset_closure hw, hw.1⟩)
  have hadm := (hR₂ η R hη hηη₂ hR₂R Ω Ωs hQ hnl _ hDo hDsub).2.2
  have hσ := hR₃ η R hη hηη₃ hR₃R Ω Ωs hQ hnl
  have hG0 := s05_dinv_nonneg Ω Ωs hJ _ _ _ _ _ hadm (fun w => 2 * sigmaSrc Ω Ωs w) (4 / 3)
    ((hσ.1.mono hDsub).const_smul (2 : ℝ))
    (fun w hw => ⟨by linarith [(hσ.2 w (hDsub hw)).1], by linarith [(hσ.2 w (hDsub hw)).2]⟩) G hG
  exact hR η R hη hηη₀ hR₁R Ω Ωs hQ hnl lab hlab S ℓ hS p hp hfin G hG hG0

/-! ## §5.9 Theorem 5.1 (`thm_upper`)

Moved here from the top of §5 (its proof uses the whole section).  The Jacobian of the normal map
`E` (MV1, MV2) is moved here from S06.  TU1: a bad net exists; TU4: the barrier integral;
TU3: the slab volume, by the change of variables along `E`. -/

/-- Mass–volume helper (MV1): `E(w, τ) = normalGeod Ω w τ` is jointly differentiable at every
`(w, τ) ∈ Ω × ℝ`, with derivative `(v, r) ↦ d_wE(·, τ) v + r ∂_τE(w, τ)`. -/
theorem s06_mv_hasFDerivAt {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {w : ℂ} (hw : w ∈ Ω) (τ : ℝ) :
    HasFDerivAt (fun p : ℂ × ℝ => normalGeod Ω p.1 p.2)
      ((fderiv ℝ (fun x => normalGeod Ω x τ) w).coprod
        ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv (fun τ' => normalGeod Ω w τ') τ))) (w, τ) := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  have hΩo : IsOpen Ω := s05_jordan_isOpen hJ
  have hl0 : 0 < poincareDensity Ω w := s02_poincareDensity_pos ⟨f, hf⟩ hw
  have hl1 : DifferentiableAt ℝ (fun p : ℂ × ℝ => poincareDensity Ω p.1) (w, τ) := by
    have h := (((s02_contDiffOn_poincareDensity hf).contDiffAt (hΩo.mem_nhds hw)).differentiableAt
      (by simp)).comp (w, τ) (differentiableAt_fst : DifferentiableAt ℝ (Prod.fst : ℂ × ℝ → ℂ) (w, τ))
    exact h
  have hA1 : DifferentiableAt ℝ (fun p : ℂ × ℝ => logDensityDz Ω p.1) (w, τ) := by
    have h := (((s02_contDiffOn_logDensityDz hf).contDiffAt (hΩo.mem_nhds hw)).differentiableAt
      (by simp)).comp (w, τ) (differentiableAt_fst : DifferentiableAt ℝ (Prod.fst : ℂ × ℝ → ℂ) (w, τ))
    exact h
  have hconj : DifferentiableAt ℝ (fun p : ℂ × ℝ => conj (logDensityDz Ω p.1)) (w, τ) :=
    (Complex.conjCLE.differentiableAt.comp (w, τ) hA1).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun p => by simp)
  have hdiv : ∀ {a b : ℂ × ℝ → ℝ}, DifferentiableAt ℝ a (w, τ) → DifferentiableAt ℝ b (w, τ) →
      b (w, τ) ≠ 0 → DifferentiableAt ℝ (fun p => a p / b p) (w, τ) := fun ha hb hb0 => by
    have h := ha.mul (hb.inv hb0)
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => by
      simp only [Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv])
  have hdivC : ∀ {a b : ℂ × ℝ → ℂ}, DifferentiableAt ℝ a (w, τ) → DifferentiableAt ℝ b (w, τ) →
      b (w, τ) ≠ 0 → DifferentiableAt ℝ (fun p => a p / b p) (w, τ) := fun ha hb hb0 => by
    have h := ha.mul (hb.inv hb0)
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => by
      simp only [Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv])
  have he : DifferentiableAt ℝ (fun p : ℂ × ℝ => Real.exp (-p.2)) (w, τ) :=
    (differentiableAt_snd : DifferentiableAt ℝ (Prod.snd : ℂ × ℝ → ℝ) (w, τ)).neg.exp
  have hh : DifferentiableAt ℝ
      (fun p : ℂ × ℝ => poincareDensity Ω p.1 * Real.exp (-p.2) / 2) (w, τ) :=
    hdiv (hl1.mul he) (differentiableAt_const 2) two_ne_zero
  have hden : DifferentiableAt ℝ (fun p : ℂ × ℝ => ‖logDensityDz Ω p.1‖ ^ 2 +
      (poincareDensity Ω p.1 * Real.exp (-p.2) / 2) ^ 2) (w, τ) :=
    (hA1.norm_sq (𝕜 := ℝ)).add (hh.pow 2)
  have hden0 : ‖logDensityDz Ω w‖ ^ 2 + (poincareDensity Ω w * Real.exp (-τ) / 2) ^ 2 ≠ 0 :=
    (add_pos_of_nonneg_of_pos (sq_nonneg _)
      (pow_pos (div_pos (mul_pos hl0 (Real.exp_pos _)) two_pos) 2)).ne'
  have hofr : DifferentiableAt ℝ (fun p : ℂ × ℝ => ((‖logDensityDz Ω p.1‖ ^ 2 +
      (poincareDensity Ω p.1 * Real.exp (-p.2) / 2) ^ 2 : ℝ) : ℂ)) (w, τ) :=
    (Complex.ofRealCLM.differentiableAt.comp (w, τ) hden).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun p => by simp)
  have hD : DifferentiableAt ℝ (fun p : ℂ × ℝ => normalGeod Ω p.1 p.2) (w, τ) := by
    unfold normalGeod
    exact ((differentiableAt_fst : DifferentiableAt ℝ (Prod.fst : ℂ × ℝ → ℂ) (w, τ)).add
      (hdivC hconj hofr (by exact_mod_cast hden0))).prodMk (hdiv hh hden hden0)
  -- the two partial derivatives
  have h1 : ∀ v : ℂ, fderiv ℝ (fun x => normalGeod Ω x τ) w v =
      fderiv ℝ (fun p : ℂ × ℝ => normalGeod Ω p.1 p.2) (w, τ) (v, 0) := by
    intro v
    have hg : HasFDerivAt (fun x : ℂ => (x, τ)) ((ContinuousLinearMap.id ℝ ℂ).prod 0) w :=
      (hasFDerivAt_id w).prodMk (hasFDerivAt_const τ w)
    have h := (hD.hasFDerivAt.comp w hg).fderiv
    rw [show (fun x => normalGeod Ω x τ) =
      (fun p : ℂ × ℝ => normalGeod Ω p.1 p.2) ∘ (fun x : ℂ => (x, τ)) from rfl, h]
    simp
  have h2 : deriv (fun τ' => normalGeod Ω w τ') τ =
      fderiv ℝ (fun p : ℂ × ℝ => normalGeod Ω p.1 p.2) (w, τ) (0, 1) := by
    have hg : HasDerivAt (fun t : ℝ => (w, t)) ((0 : ℂ), (1 : ℝ)) τ :=
      (hasDerivAt_const τ w).prodMk (hasDerivAt_id τ)
    have h := (hD.hasFDerivAt.comp_hasDerivAt τ hg).deriv
    exact h
  convert hD.hasFDerivAt using 1
  rw [← ContinuousLinearMap.coprod_comp_inl_inr
    (fderiv ℝ (fun p : ℂ × ℝ => normalGeod Ω p.1 p.2) (w, τ))]
  congr 1
  · refine ContinuousLinearMap.ext fun v => ?_
    rw [h1 v]
    simp
  · refine ContinuousLinearMap.ext fun r => ?_
    rw [ContinuousLinearMap.smulRight_apply, h2, ← map_smul]
    simp

/-- Mass–volume helper (MV2): the Euclidean Jacobian of `E`.  By Lemma 5.2 (a) the hyperbolic Gram
matrix of `(d_wE 1, d_wE i, ∂_τE)` is `diag(g_τ, 1)`, and `det g_τ = λ⁴(cosh²τ - s²e^{2τ})²`, so
`|det DE| = ξ³ λ² |cosh²τ - s² e^{2τ}|` with `ξ = E(w, τ)₂`. -/
theorem s06_mv_det {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {w : ℂ} (hw : w ∈ Ω)
    (hs : schwarzNorm Ω w ≠ 1) (τ : ℝ) :
    |((fderiv ℝ (fun x => normalGeod Ω x τ) w).coprod
        ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv (fun τ' => normalGeod Ω w τ') τ))).det| =
      (normalGeod Ω w τ).2 ^ 3 * (poincareDensity Ω w ^ 2 *
        |Real.cosh τ ^ 2 - schwarzNorm Ω w ^ 2 * Real.exp τ ^ 2|) := by
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  have hl0 : 0 < poincareDensity Ω w := s02_poincareDensity_pos ⟨f, hf⟩ hw
  obtain ⟨hdd, hdo, -⟩ := lem_shape_a Ω Ωs hJ w hw hs τ
  have hG := s05_go_det hJ hw hs τ
  have hq0 : 0 < (normalGeod Ω w τ).2 := s02_normalGeod_pos Ω w hl0 τ
  set q := normalGeod Ω w τ with hq
  set L1 := fderiv ℝ (fun x => normalGeod Ω x τ) w with hL1
  set d := deriv (fun τ' => normalGeod Ω w τ') τ with hd
  set L := L1.coprod ((1 : ℝ →L[ℝ] ℝ).smulRight d) with hL
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin 2 ⊕ Fin 1) ℝ (ℂ × ℝ),
      b = Complex.basisOneI.prod (Module.Basis.singleton (Fin 1) ℝ) := ⟨_, rfl⟩
  have hsym : ∀ a c : ℂ × ℝ, hypInner q a c = hypInner q c a := fun a c => by
    unfold hypInner
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  -- the Euclidean inner product of coordinates is `ξ²` times the hyperbolic one
  have hsum : ∀ u u' : ℂ × ℝ, ∑ k, b.repr u k * b.repr u' k = q.2 ^ 2 * hypInner q u u' := by
    intro u u'
    rw [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_one, hb]
    simp only [Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
      Complex.coe_basisOneI_repr, Module.Basis.singleton_repr]
    unfold hypInner
    rw [mul_div_cancel₀ _ (pow_ne_zero 2 hq0.ne')]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    simp
  have hb1 : ∀ i, b (Sum.inl i) = (frameVec i, 0) := fun i => by
    rw [hb]
    refine Prod.ext ?_ ?_
    · rw [Module.Basis.prod_apply_inl_fst, Complex.coe_basisOneI]
      rfl
    · exact Module.Basis.prod_apply_inl_snd _ _ i
  have hb2 : ∀ i, b (Sum.inr i) = (0, 1) := fun i => by
    rw [hb]
    refine Prod.ext ?_ ?_
    · exact Module.Basis.prod_apply_inr_fst _ _ i
    · rw [Module.Basis.prod_apply_inr_snd, Module.Basis.singleton_apply]
  have hLv : ∀ v : ℂ, L (v, 0) = L1 v := fun v => by simp [hL]
  have hLr : L (0, 1) = d := by simp [hL]
  -- the Gram matrix `MᵀM = ξ² diag(g_τ, 1)`
  have hMtM : (LinearMap.toMatrix b b (L : ℂ × ℝ →ₗ[ℝ] ℂ × ℝ)).transpose *
      LinearMap.toMatrix b b (L : ℂ × ℝ →ₗ[ℝ] ℂ × ℝ) =
      q.2 ^ 2 • Matrix.of (fun i j => hypInner q (L (b i)) (L (b j))) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, LinearMap.toMatrix_apply,
      Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ContinuousLinearMap.coe_coe]
    exact hsum _ _
  have hH : Matrix.of (fun i j => hypInner q (L (b i)) (L (b j))) =
      Matrix.fromBlocks (graphMetric Ω w τ) 0 0 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp only [Matrix.of_apply, Matrix.fromBlocks_apply₁₁, hb1, hLv]
      rfl
    · simp only [Matrix.of_apply, Matrix.fromBlocks_apply₁₂, hb1, hb2, hLv, hLr, Matrix.zero_apply]
      rw [hsym]
      exact hdo _
    · simp only [Matrix.of_apply, Matrix.fromBlocks_apply₂₁, hb1, hb2, hLv, hLr, Matrix.zero_apply]
      exact hdo _
    · simp only [Matrix.of_apply, Matrix.fromBlocks_apply₂₂, hb2, hLr]
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      exact hdd
  have hdet : L.det ^ 2 = q.2 ^ 6 * (poincareDensity Ω w ^ 4 *
      (Real.cosh τ ^ 2 - schwarzNorm Ω w ^ 2 * Real.exp τ ^ 2) ^ 2) := by
    have h1 := LinearMap.det_toMatrix b (L : ℂ × ℝ →ₗ[ℝ] ℂ × ℝ)
    calc L.det ^ 2 = ((LinearMap.toMatrix b b (L : ℂ × ℝ →ₗ[ℝ] ℂ × ℝ)).transpose *
          LinearMap.toMatrix b b (L : ℂ × ℝ →ₗ[ℝ] ℂ × ℝ)).det := by
          rw [Matrix.det_mul, Matrix.det_transpose, h1, sq]
      _ = _ := by
          rw [hMtM, hH, Matrix.det_smul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, hG]
          simp only [Fintype.card_sum, Fintype.card_fin, mul_one]
          ring
  have hrhs : 0 ≤ q.2 ^ 3 * (poincareDensity Ω w ^ 2 *
      |Real.cosh τ ^ 2 - schwarzNorm Ω w ^ 2 * Real.exp τ ^ 2|) := by positivity
  refine (pow_left_inj₀ (abs_nonneg _) hrhs two_ne_zero).1 ?_
  rw [sq_abs, hdet, mul_pow, mul_pow, sq_abs]
  ring

/-- TU1: a bad net exists (Zorn: maximal `1`-separated subset of `𝔅`; labels by choice). -/
theorem s05_tu_net {K : ℝ} {Ω Ωs : Set ℂ} (hp : IsKQuasiPair Ω Ωs K) (hnl : ¬ IsLinePair Ω Ωs)
    {lab : ℂ × ℝ → ℂ} (hlab : IsLabel Ω lab) (η R : ℝ) :
    ∃ (S : Set (ℂ × ℝ)) (ℓ : ℂ × ℝ → ℂ), IsBadNet Ω Ωs lab η R S ℓ := by
  -- The pair hypotheses and `IsLabel` are not needed: any `lab` serves as the `Σ*` label.
  have _hp := hp
  have _hnl := hnl
  have _hlab := hlab
  classical
  obtain ⟨m, hm⟩ := zorn_subset {S : Set (ℂ × ℝ) | S ⊆ badSet Ω Ωs η R ∧
      ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → 1 ≤ hdist b b'} fun c hc hch => by
    refine ⟨⋃₀ c, ⟨sUnion_subset fun s hs => (hc hs).1, ?_⟩, fun s hs => subset_sUnion_of_mem hs⟩
    intro b hb b' hb' hne
    obtain ⟨s, hs, hbs⟩ := hb
    obtain ⟨s', hs', hbs'⟩ := hb'
    rcases hch.total hs hs' with h | h
    · exact (hc hs').2 b (h hbs) b' hbs' hne
    · exact (hc hs).2 b hbs b' (h hbs') hne
  refine ⟨m, fun b => if h : b ∈ epstein Ω '' Ω then h.choose else lab b,
    hm.1.1, hm.1.2, fun x hx => ?_, fun b hb => ?_⟩
  · by_contra hcon
    push Not at hcon
    -- maximality: otherwise `x` could be added to the net
    have hins : insert x m ∈ {S : Set (ℂ × ℝ) | S ⊆ badSet Ω Ωs η R ∧
        ∀ b ∈ S, ∀ b' ∈ S, b ≠ b' → 1 ≤ hdist b b'} := by
      refine ⟨insert_subset hx hm.1.1, ?_⟩
      intro b hb b' hb' hne
      rcases hb with hb | hb <;> rcases hb' with hb' | hb'
      · exact absurd (hb.trans hb'.symm) hne
      · rw [hb]
        exact hcon b' hb'
      · rw [hb', s02_hdist_comm]
        exact hcon b hb
      · exact hm.1.2 b hb b' hb' hne
    have hxm : x ∈ m := hm.2 hins (subset_insert x m) (mem_insert x m)
    have hlt := hcon x hxm
    have hc : coshDist x x = 1 := by simp [coshDist]
    have h0 : hdist x x = 0 := by simp only [hdist, hc, Real.arcosh_zero]
    linarith
  · by_cases h : b ∈ epstein Ω '' Ω
    · left
      simp only [h, ↓reduceDIte]
      exact h.choose_spec
    · right
      have hb' := (hm.1.1 hb).1
      rcases hb' with hb' | hb'
      · exact absurd hb' h
      · refine ⟨hb', ?_⟩
        simp only [h, ↓reduceDIte]

/-- TU4 (barrier integral): `∫_D k_p b dâ ≤ 12π C_b ∑ᵢ k_p(ℓᵢ)` (Tonelli + Lemma 5.6, `β = 3/2`). -/
theorem s05_tu_barrier_int {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {S : Set (ℂ × ℝ)}
    (hSc : S.Countable) {ℓ : ℂ × ℝ → ℂ} (hℓ : ∀ b ∈ S, ℓ b ∈ Ω) {Cb : ℝ} (hCb : 0 ≤ Cb)
    {D : Set ℂ} (hD : MeasurableSet D) {p : ℂ} (hp : p ∈ Ω) :
    ∫⁻ w in D, ENNReal.ofReal (intrKernel Ω p w * barrierFn Ω S ℓ Cb w) ∂hypArea Ω ≤
      ENNReal.ofReal (12 * π * Cb) * ∑' b : S, ENNReal.ofReal (intrKernel Ω p (ℓ b)) := by
  -- The measurability of `D` is not needed: the integral over `D` is bounded by the one over `ℂ`.
  have _hD := hD
  have := hSc.to_subtype
  have hΩ := s02_jordanPair_riemannMap hJ
  obtain ⟨f, hf⟩ := hΩ
  have hΩm : MeasurableSet Ω := (hf.isOpen isOpen_ball).measurableSet
  have hmeas : ∀ b : S, AEMeasurable (fun x => ENNReal.ofReal (intrKernel Ω p x *
      Real.exp (-(3 / 2) * poincareDist Ω x (ℓ b)))) (hypArea Ω) := by
    intro b
    have hc : ContinuousOn (fun x => poincareDist Ω x (ℓ b)) Ω :=
      fun x hx => (s05_eb_dist_cont ⟨f, hf⟩ (hℓ b b.2) hx).continuousWithinAt
    have he : ContinuousOn (fun x => Real.exp (-(3 / 2) * poincareDist Ω x (ℓ b))) Ω :=
      Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hc)
    exact (((s03_sc_meas ⟨f, hf⟩ hp).aemeasurable.mul (he.aemeasurable hΩm)).ennreal_ofReal).mono_ac
      (withDensity_absolutelyContinuous _ _ : hypArea Ω ≪ volume.restrict Ω)
  have hpt : ∀ x, ENNReal.ofReal (intrKernel Ω p x * barrierFn Ω S ℓ Cb x) ≤
      ENNReal.ofReal Cb * ∑' b : S, ENNReal.ofReal (intrKernel Ω p x *
        Real.exp (-(3 / 2) * poincareDist Ω x (ℓ b))) := by
    intro x
    have hk : 0 ≤ intrKernel Ω p x := sq_nonneg _
    by_cases hs : Summable (fun b : S => Real.exp (-(3 / 2) * poincareDist Ω x (ℓ b)))
    · have h1 : intrKernel Ω p x * barrierFn Ω S ℓ Cb x =
          Cb * ∑' b : S, intrKernel Ω p x * Real.exp (-(3 / 2) * poincareDist Ω x (ℓ b)) := by
        show intrKernel Ω p x * (Cb * ∑' b : S, Real.exp (-(3 / 2) * poincareDist Ω x (ℓ b))) = _
        rw [tsum_mul_left]
        ring
      rw [h1, ENNReal.ofReal_mul hCb, ENNReal.ofReal_tsum_of_nonneg
        (fun b => mul_nonneg hk (Real.exp_pos _).le) (hs.mul_left _)]
    · have h0 : barrierFn Ω S ℓ Cb x = 0 := by
        show Cb * ∑' b : S, Real.exp (-(3 / 2) * poincareDist Ω x (ℓ b)) = 0
        rw [tsum_eq_zero_of_not_summable hs, mul_zero]
      rw [h0, mul_zero, ENNReal.ofReal_zero]
      exact zero_le
  have h12 : (0 : ℝ) ≤ 12 * π := by positivity
  calc ∫⁻ w in D, ENNReal.ofReal (intrKernel Ω p w * barrierFn Ω S ℓ Cb w) ∂hypArea Ω
      ≤ ∫⁻ w, ENNReal.ofReal (intrKernel Ω p w * barrierFn Ω S ℓ Cb w) ∂hypArea Ω :=
        setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ w, ENNReal.ofReal Cb * ∑' b : S, ENNReal.ofReal (intrKernel Ω p w *
          Real.exp (-(3 / 2) * poincareDist Ω w (ℓ b))) ∂hypArea Ω := lintegral_mono hpt
    _ = ENNReal.ofReal Cb * ∑' b : S, ∫⁻ w, ENNReal.ofReal (intrKernel Ω p w *
          Real.exp (-(3 / 2) * poincareDist Ω w (ℓ b))) ∂hypArea Ω := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_tsum hmeas]
    _ ≤ ENNReal.ofReal Cb * ∑' b : S, ENNReal.ofReal (12 * π * intrKernel Ω p (ℓ b)) := by
        gcongr with b
        have hr := lem_reproduction Ω Ωs hJ (3 / 2) (by norm_num) p hp (ℓ b) (hℓ b b.2)
        have hc : 4 * π * (3 / 2 : ℝ) / (3 / 2 - 1) = 12 * π := by ring
        rw [hc] at hr
        exact hr
    _ = ENNReal.ofReal (12 * π * Cb) * ∑' b : S, ENNReal.ofReal (intrKernel Ω p (ℓ b)) := by
        simp_rw [ENNReal.ofReal_mul h12]
        rw [ENNReal.tsum_mul_left]
        ring

/-- TU3 helper: `k_p = sech²(d_ρ(p, ·)/2)` is continuous on `Ω`. -/
theorem s05_tu_kernel_cont {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω) {p : ℂ}
    (hp : p ∈ Ω) : ContinuousOn (intrKernel Ω p) Ω := by
  have hdc : ContinuousOn (fun x => poincareDist Ω x p) Ω :=
    fun x hx => (s05_eb_dist_cont hΩ hp hx).continuousWithinAt
  have hk : ContinuousOn (fun x => ((Real.cosh (poincareDist Ω x p / 2))⁻¹) ^ 2) Ω :=
    ((Real.continuous_cosh.comp_continuousOn (hdc.div_const 2)).inv₀
      (fun x _ => (Real.cosh_pos _).ne')).pow 2
  refine hk.congr fun x hx => ?_
  show ((Real.cosh (poincareDist Ω p x / 2))⁻¹) ^ 2 = _
  rw [s02_poincareDist_comm hΩ hp hx]

/-- TU3 helper: for `0 ≤ s ≤ 1/2` and `0 ≤ τ < 1/4`, `|cosh²τ - s² e^{2τ}| ≤ 2`
(`e^τ ≤ 1/(1-τ) < 4/3`, so `cosh τ ≤ 4/3`). -/
theorem s05_tu_jac_le {s τ : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) (hτ0 : 0 ≤ τ) (hτ : τ < 1 / 4) :
    |Real.cosh τ ^ 2 - s ^ 2 * Real.exp τ ^ 2| ≤ 2 := by
  have he0 : 0 < Real.exp τ := Real.exp_pos τ
  have he : Real.exp τ ≤ 4 / 3 := by
    refine (Real.exp_bound_div_one_sub_of_interval hτ0 (by linarith)).trans ?_
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hm : Real.exp (-τ) ≤ Real.exp τ := Real.exp_le_exp.2 (by linarith)
  have hc0 : 0 < Real.cosh τ := Real.cosh_pos τ
  have hc : Real.cosh τ ≤ 4 / 3 := by
    rw [Real.cosh_eq]
    linarith
  have hs2 : s ^ 2 ≤ 1 / 4 := by nlinarith
  have he2 : Real.exp τ ^ 2 ≤ 16 / 9 := by nlinarith
  have hc2 : Real.cosh τ ^ 2 ≤ 16 / 9 := by nlinarith
  have hse : s ^ 2 * Real.exp τ ^ 2 ≤ 1 / 4 * (16 / 9) :=
    mul_le_mul hs2 he2 (sq_nonneg _) (by norm_num)
  have hse0 : 0 ≤ s ^ 2 * Real.exp τ ^ 2 := by positivity
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (Real.cosh τ)]

/-- TU3 (slab volume): `∫_{𝒮_D} k_p(w(q)) dvol ≤ 2 ∫_D k_p t dâ` for open `D ⊆ G₀`
(change of variables through `(w, τ) ↦ E(w, τ)`, `E^* dvol = J dτ dvol_I`, `J ≤ 2`). -/
theorem s05_tu_slab_vol : ∀ K : ℝ, 1 ≤ K → ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ R₁ : ℝ, ∀ η R : ℝ, 0 < η → η ≤ η₀ → R₁ ≤ R →
      ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K → ¬ IsLinePair Ω Ωs →
      ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab → ∀ D : Set ℂ, IsOpen D → D ⊆ goodSet Ω Ωs η R →
        ∀ p ∈ Ω,
          ∫⁻ q in slabRegion Ω Ωs D, ENNReal.ofReal (intrKernel Ω p (lab q)) ∂hvol ≤
            2 * ∫⁻ w in D, ENNReal.ofReal (intrKernel Ω p w * slabTop Ω Ωs w) ∂hypArea Ω := by
  intro K hK ε hε hε'
  obtain ⟨η₁, hη₁, R₂, hcov⟩ := s04_sl_cor_coverage_unif K hK ε hε hε'
  obtain ⟨η₂, hη₂, R₃, hNu⟩ := s04_sl_eq_def_N_unif K hK ε hε hε'
  refine ⟨min (min η₁ η₂) (1 / 2), lt_min (lt_min hη₁ hη₂) (by norm_num), max (max R₂ R₃) 1,
    fun η R hη hηle hR Ω Ωs hpair hnl lab hlab D hDo hDG p hpΩ => ?_⟩
  have hη1 : η ≤ η₁ := hηle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hη2 : η ≤ η₂ := hηle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hη3 : η ≤ 1 / 2 := hηle.trans (min_le_right _ _)
  have hR2 : R₂ ≤ R := ((le_max_left _ _).trans (le_max_left _ _)).trans hR
  have hR3 : R₃ ≤ R := ((le_max_right _ _).trans (le_max_left _ _)).trans hR
  have hR1 : 1 ≤ R := (le_max_right _ _).trans hR
  obtain ⟨-, hc2⟩ := hcov η R hη hη1 hR2 Ω Ωs hpair hnl lab hlab
  obtain ⟨-, htC, -, hNg⟩ := hNu η R hη hη2 hR3 Ω Ωs hpair hnl
  have hJ := s03_b0_jordanPair hpair
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  have hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω := ⟨f, hf⟩
  have hΩm : MeasurableSet Ω := (s05_jordan_isOpen hJ).measurableSet
  have hDΩ : D ⊆ Ω := fun w hw => (hDG hw).1
  have hDm : MeasurableSet D := hDo.measurableSet
  have hs0 : ∀ (U : Set ℂ) (z : ℂ), 0 ≤ schwarzNorm U z := fun U z => Real.sSup_nonneg (fun r hr => by
    obtain ⟨f, z, -, -, -, rfl⟩ := hr
    positivity)
  have hsη : ∀ w ∈ D, schwarzNorm Ω w < η := fun w hw => s05_go_s_lt hJ (by linarith) (hDG hw)
  have htε : ∀ w ∈ D, slabTop Ω Ωs w < ε := fun w hw => (hNg w (hDG hw)).2.2.1
  -- the parameter domain `A = {(w, τ) : w ∈ D, 0 < τ < t(w)}`
  obtain ⟨A, hA⟩ : ∃ A : Set (ℂ × ℝ),
      A = {x | x.1 ∈ D ∧ 0 < x.2 ∧ x.2 < slabTop Ω Ωs x.1} := ⟨_, rfl⟩
  have hmemA : ∀ x, x ∈ A ↔ x.1 ∈ D ∧ 0 < x.2 ∧ x.2 < slabTop Ω Ωs x.1 := fun x => by
    rw [hA]
    rfl
  have hAo : IsOpen A := by
    have htD : ContinuousOn (fun x : ℂ × ℝ => slabTop Ω Ωs x.1 - x.2) (D ×ˢ univ) :=
      ((htC.continuousOn.mono hDG).comp continuousOn_fst
        (fun x (hx : x ∈ D ×ˢ (univ : Set ℝ)) => hx.1)).sub continuousOn_snd
    have he : A = (D ×ˢ univ ∩ (fun x : ℂ × ℝ => slabTop Ω Ωs x.1 - x.2) ⁻¹' Ioi 0) ∩
        Prod.snd ⁻¹' Ioi 0 := by
      ext x
      rw [hmemA]
      simp only [mem_inter_iff, mem_prod, mem_univ, and_true, mem_preimage, mem_Ioi, sub_pos]
      tauto
    rw [he]
    exact (htD.isOpen_inter_preimage (hDo.prod isOpen_univ) isOpen_Ioi).inter
      (isOpen_Ioi.preimage continuous_snd)
  have hAm : MeasurableSet A := hAo.measurableSet
  have hAΩ : MapsTo Prod.fst A Ω := fun x hx => hDΩ ((hmemA x).1 hx).1
  have hslab : slabRegion Ω Ωs D = (fun x : ℂ × ℝ => normalGeod Ω x.1 x.2) '' A := by
    ext q
    constructor
    · rintro ⟨w, hw, τ, h0, h1, rfl⟩
      exact ⟨(w, τ), (hmemA _).2 ⟨hw, h0, h1⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hw, h0, h1⟩ := (hmemA x).1 hx
      exact ⟨x.1, hw, x.2, h0, h1, rfl⟩
  -- `E` is injective on `A`: the label recovers `w`, the arclength recovers `τ`
  have hinj : InjOn (fun x : ℂ × ℝ => normalGeod Ω x.1 x.2) A := by
    intro x hx x' hx' heq
    obtain ⟨hw, h0, h1⟩ := (hmemA x).1 hx
    obtain ⟨hw', h0', h1'⟩ := (hmemA x').1 hx'
    change normalGeod Ω x.1 x.2 = normalGeod Ω x'.1 x'.2 at heq
    have hww : x.1 = x'.1 := by
      have a := (hc2 x.1 (hDG hw) x.2 ⟨h0, h1⟩).2
      have b := (hc2 x'.1 (hDG hw') x'.2 ⟨h0', h1'⟩).2
      rw [heq] at a
      exact a.symm.trans b
    have hnb := lem_normal_b hΩ (hDΩ hw)
    have hd := hnb.2.1 x.2 x'.2
    rw [heq, ← hww, hnb.2.1 x'.2 x'.2, sub_self, abs_zero] at hd
    have h0'' : x.2 - x'.2 = 0 := abs_eq_zero.1 hd.symm
    exact Prod.ext hww (by linarith)
  have hder : ∀ x ∈ A, HasFDerivWithinAt (fun x : ℂ × ℝ => normalGeod Ω x.1 x.2)
      ((fderiv ℝ (fun y => normalGeod Ω y x.2) x.1).coprod
        ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv (fun τ' => normalGeod Ω x.1 τ') x.2))) A x :=
    fun x hx => (s06_mv_hasFDerivAt hJ (hAΩ hx) x.2).hasFDerivWithinAt
  have hEAm : MeasurableSet ((fun x : ℂ × ℝ => normalGeod Ω x.1 x.2) '' A) :=
    measurable_image_of_fderivWithin hAm hder hinj
  have hsubU : (fun x : ℂ × ℝ => normalGeod Ω x.1 x.2) '' A ⊆ UHS := by
    rintro _ ⟨x, hx, rfl⟩
    exact s02_normalGeod_pos Ω x.1 (s02_poincareDensity_pos hΩ (hAΩ hx)) x.2
  -- continuity of `λ` and of `k_p` on `Ω`
  have hlC : ContinuousOn (poincareDensity Ω) Ω := (s02_contDiffOn_poincareDensity hf).continuousOn
  have hkC : ContinuousOn (intrKernel Ω p) Ω := s05_tu_kernel_cont hΩ hpΩ
  -- the right-hand side as a Lebesgue integral
  have hRHS : ∫⁻ w in D, ENNReal.ofReal (intrKernel Ω p w * slabTop Ω Ωs w) ∂hypArea Ω =
      ∫⁻ w in D, ENNReal.ofReal (poincareDensity Ω w ^ 2) *
        ENNReal.ofReal (intrKernel Ω p w * slabTop Ω Ωs w) := by
    have hm1 : AEMeasurable (fun w => ENNReal.ofReal (poincareDensity Ω w ^ 2))
        ((volume.restrict Ω).restrict D) :=
      (ENNReal.measurable_ofReal.comp_aemeasurable ((hlC.pow 2).aemeasurable hΩm)).mono_measure
        Measure.restrict_le_self
    unfold hypArea
    rw [restrict_withDensity hDm, lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hm1
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), Measure.restrict_restrict hDm,
      inter_eq_left.2 hDΩ]
    simp only [Pi.mul_apply]
  -- the left-hand side by the change of variables along `E`
  have hρm : Measurable (fun q : ℂ × ℝ => ENNReal.ofReal ((q.2 ^ 3)⁻¹)) :=
    ENNReal.measurable_ofReal.comp ((measurable_snd.pow_const 3).inv)
  have : (volume : Measure (ℂ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  rw [hRHS, hslab]
  unfold hvol
  rw [restrict_withDensity hEAm, lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _
      hρm.aemeasurable (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    Measure.restrict_restrict hEAm, inter_eq_left.2 hsubU,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hAm hder hinj]
  simp only [Pi.mul_apply]
  have hF : AEMeasurable (fun x : ℂ × ℝ =>
      ENNReal.ofReal (2 * poincareDensity Ω x.1 ^ 2 * intrKernel Ω p x.1)) (volume.restrict A) := by
    have hc : ContinuousOn (fun x : ℂ × ℝ => 2 * poincareDensity Ω x.1 ^ 2 * intrKernel Ω p x.1) A :=
      (continuousOn_const.mul ((hlC.comp continuousOn_fst hAΩ).pow 2)).mul
        (hkC.comp continuousOn_fst hAΩ)
    exact ENNReal.measurable_ofReal.comp_aemeasurable (hc.aemeasurable hAm)
  have hF' := (aemeasurable_indicator_iff hAm).2 hF
  rw [Measure.volume_eq_prod] at hF'
  calc _ ≤ ∫⁻ x in A, ENNReal.ofReal (2 * poincareDensity Ω x.1 ^ 2 * intrKernel Ω p x.1) := by
        refine setLIntegral_mono' hAm fun x hx => ?_
        obtain ⟨hw, h0, h1⟩ := (hmemA x).1 hx
        have hwΩ := hDΩ hw
        have hl0 := s02_poincareDensity_pos hΩ hwΩ
        have hξ : 0 < (normalGeod Ω x.1 x.2).2 := s02_normalGeod_pos Ω x.1 hl0 x.2
        have hs1 : schwarzNorm Ω x.1 < 1 := by linarith [hsη x.1 hw]
        have hdet := s06_mv_det hJ hwΩ hs1.ne x.2
        have hlb := (hc2 x.1 (hDG hw) x.2 ⟨h0, h1⟩).2
        have hcj := s05_tu_jac_le (hs0 Ω x.1) (by linarith [hsη x.1 hw]) h0.le
          (by linarith [htε x.1 hw])
        have hk : 0 ≤ intrKernel Ω p x.1 := sq_nonneg _
        rw [hlb, ← ENNReal.ofReal_mul (inv_nonneg.2 (pow_pos hξ 3).le),
          ← ENNReal.ofReal_mul (abs_nonneg _), hdet]
        refine ENNReal.ofReal_le_ofReal ?_
        have hξ3 : (normalGeod Ω x.1 x.2).2 ^ 3 ≠ 0 := (pow_pos hξ 3).ne'
        set ξ := (normalGeod Ω x.1 x.2).2
        set L := poincareDensity Ω x.1
        set c := |Real.cosh x.2 ^ 2 - schwarzNorm Ω x.1 ^ 2 * Real.exp x.2 ^ 2|
        calc ξ ^ 3 * (L ^ 2 * c) * ((ξ ^ 3)⁻¹ * intrKernel Ω p x.1)
            = L ^ 2 * c * intrKernel Ω p x.1 := by field_simp
          _ ≤ L ^ 2 * 2 * intrKernel Ω p x.1 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcj (sq_nonneg _)) hk
          _ = 2 * L ^ 2 * intrKernel Ω p x.1 := by ring
    -- Tonelli over the fibres `τ ∈ (0, t(w))`
    _ = ∫⁻ w in D, ENNReal.ofReal (2 * poincareDensity Ω w ^ 2 * intrKernel Ω p w) *
          ENNReal.ofReal (slabTop Ω Ωs w) := by
        rw [← lintegral_indicator hAm, ← lintegral_indicator hDm, Measure.volume_eq_prod,
          lintegral_prod _ hF']
        refine lintegral_congr fun w => ?_
        by_cases hw : w ∈ D
        · rw [indicator_of_mem hw]
          refine (lintegral_congr (g := (Ioo 0 (slabTop Ω Ωs w)).indicator fun _ =>
            ENNReal.ofReal (2 * poincareDensity Ω w ^ 2 * intrKernel Ω p w)) fun τ => ?_).trans ?_
          · classical
            simp only [indicator_apply, hmemA, mem_Ioo, hw, true_and]
          · rw [lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo, sub_zero]
        · rw [indicator_of_notMem hw]
          exact (lintegral_congr (g := fun _ => 0) fun τ =>
            indicator_of_notMem (fun h => hw ((hmemA _).1 h).1) _).trans lintegral_zero
    _ = 2 * ∫⁻ w in D, ENNReal.ofReal (poincareDensity Ω w ^ 2) *
          ENNReal.ofReal (intrKernel Ω p w * slabTop Ω Ωs w) := by
        rw [← lintegral_const_mul' 2 _ (by norm_num)]
        refine setLIntegral_congr_fun hDm fun w _ => ?_
        have hk : 0 ≤ intrKernel Ω p w := sq_nonneg _
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (sq_nonneg _),
          show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-- **Theorem 5.1** (`thm:upper`, sec05-upper.tex:7).  For every `K ≥ 1` there is `C(K) < ∞` such
that for every `K`-quasicircle, every label and every `p ∈ Ω`, `K_V(p) ≤ C(K) K_{H,2}(p)` (5.1). -/
theorem thm_upper : ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ≥0, ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs K →
    ∀ lab : ℂ × ℝ → ℂ, IsLabel Ω lab → ∀ p ∈ Ω,
      KV Ω Ωs lab p ≤ (C : ℝ≥0∞) * KH2 Ω Ωs lab p := by
  intro K hK
  classical
  -- the constants: `ε`, then a common `(η, R)` for all uniform pieces
  obtain ⟨Cbad, hbr⟩ := s05_br_unif K hK
  obtain ⟨C₁, ε₁, hε₁, hgc⟩ := s05_gc_unif
  obtain ⟨Rb, -, ε₀, hε₀, htb⟩ := s05_tb_unif K hK
  set ε : ℝ := min (min ε₀ ε₁) (1 / 20) with hεdef
  have hε : 0 < ε := lt_min (lt_min hε₀ hε₁) (by norm_num)
  have hεε₀ : ε ≤ ε₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hεε₁ : ε ≤ ε₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hε20 : ε ≤ 1 / 20 := min_le_right _ _
  have hε4 : ε < 1 / 4 := by linarith
  have hε10 : 10 * ε < 1 := by linarith
  obtain ⟨η₁, hη₁, -, R₁, htbu⟩ := htb ε hε hεε₀
  obtain ⟨η₂, hη₂, R₂, -, hbru⟩ := hbr ε hε hε4
  obtain ⟨η₃, hη₃, R₃, hgcu⟩ := hgc K hK ε hε hε4 hεε₁
  obtain ⟨η₄, hη₄, R₄, hsig⟩ := s05_tu_sigma K hK ε hε hε4
  obtain ⟨η₅, hη₅, R₅, hsv⟩ := s05_tu_slab_vol K hK ε hε hε4
  obtain ⟨η₆, hη₆, R₆, hsrc⟩ := s04_src_unif K hK ε hε hε4 hε10
  set η : ℝ := min (min (min η₁ η₂) (min η₃ η₄)) (min (min η₅ η₆) (1 / 8)) with hηdef
  set R : ℝ := max (max (max R₁ R₂) (max R₃ R₄)) (max (max R₅ R₆) 1) with hRdef
  have hη : 0 < η := lt_min (lt_min (lt_min hη₁ hη₂) (lt_min hη₃ hη₄))
    (lt_min (lt_min hη₅ hη₆) (by norm_num))
  have hη1 : η ≤ η₁ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hη2 : η ≤ η₂ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hη3 : η ≤ η₃ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη4 : η ≤ η₄ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hη5 : η ≤ η₅ := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hη6 : η ≤ η₆ := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hη8 : η ≤ 1 / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hR1 : R₁ ≤ R := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)
  have hR2 : R₂ ≤ R := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)
  have hR3 : R₃ ≤ R := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
  have hR4 : R₄ ≤ R := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
  have hR5 : R₅ ≤ R := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hR6 : R₆ ≤ R := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hR0 : 0 < R := lt_of_lt_of_le one_pos ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨Ccnt, hcnt⟩ := lem_counting K hK η R hη (by linarith) hR0
  set Cb : ℝ := ε * Real.exp (3 / 2 * Rb) with hCbdef
  have hCb : 0 ≤ Cb := mul_nonneg hε.le (Real.exp_pos _).le
  set a : ℝ≥0∞ := ENNReal.ofReal (12 * π * Cb) * Ccnt with hadef
  set b : ℝ≥0∞ := ENNReal.ofReal (1 / (2 - 11 * (C₁ * ε))) *
    (2 * ENNReal.ofReal (4 / 3 * ((1 - 10 * ε) ^ 2)⁻¹)) with hbdef
  set c : ℝ≥0∞ := (Cbad : ℝ≥0∞) * Ccnt with hcdef
  set Cen : ℝ≥0∞ := 2 * (a + b) + c + 1 with hCendef
  have hCen : Cen ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num)
      (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (by norm_num)
          ENNReal.ofReal_ne_top)⟩), ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top⟩,
      ENNReal.one_ne_top⟩
  have hC0 : Cen ≠ 0 := (lt_of_lt_of_le zero_lt_one (le_add_self : (1 : ℝ≥0∞) ≤ _)).ne'
  refine ⟨Cen.toNNReal, fun Ω Ωs hpair lab hlab p hp => ?_⟩
  rw [ENNReal.coe_toNNReal hCen]
  -- the easy cases: a line pair (`K_V = 0`), and `K_{H,2} = ∞`
  by_cases hl : IsLinePair Ω Ωs
  · rw [(def_intrinsic_circle hl lab p (0, 1)).2.2.2.1]
    exact zero_le
  by_cases htop : KH2 Ω Ωs lab p = ⊤
  · rw [htop, ENNReal.mul_top hC0]
    exact le_top
  have hKt : KH2 Ω Ωs lab p < ⊤ := lt_top_iff_ne_top.2 htop
  -- the bad net, the good domain `D`, and its properties
  obtain ⟨S, ℓ, hnet⟩ := s05_tu_net hpair hl hlab η R
  set D := goodDomainD Ω Ωs η R S ℓ with hDdef
  have hJ := s03_b0_jordanPair hpair
  have hΩ := s02_jordanPair_riemannMap hJ
  have hΩs := s02_jordanPair_riemannMap (s03_b0_jordanPair (s03_qce_swap hpair))
  have hDo : IsOpen D := (eq_def_D K hK η R hη hR0 Ω Ωs hpair hl lab hlab S ℓ hnet).2.2
  have hDm : MeasurableSet D := hDo.measurableSet
  have hDΩ : D ⊆ Ω := fun w hw => hw.1
  have hDG : D ⊆ goodSet Ω Ωs η R := fun w hw =>
    (lem_good_domain_a K hK η R hη hR0 Ω Ωs hpair hl lab hlab S ℓ hnet).2
      ((lem_good_domain_a K hK η R hη hR0 Ω Ωs hpair hl lab hlab S ℓ hnet).1
        ⟨subset_closure hw, hw.1⟩)
  have hSc : S.Countable := by
    refine s06_tl_countable (fun x hx => ?_) hnet.2.1
    rcases (hnet.1 hx).1 with ⟨w, hw, rfl⟩ | ⟨z, hz, rfl⟩
    · exact s04_tb_ep_uhs hΩ hw
    · exact s04_tb_ep_uhs hΩs hz
  have hℓ : ∀ b ∈ S, ℓ b ∈ Ω := s05_eb_label_mem hpair hl hlab hnet
  have hkC : ContinuousOn (intrKernel Ω p) Ω := s05_tu_kernel_cont hΩ hp
  have hk : ∀ w, 0 ≤ intrKernel Ω p w := fun w => sq_nonneg _
  -- the Dirichlet inverse `G = 𝒢_D(2σ)`
  obtain ⟨-, -, hadm⟩ := hgcu η R hη hη3 hR3 Ω Ωs hpair hl D hDo hDG
  obtain ⟨hσC, hσb⟩ := hsig η R hη hη4 hR4 Ω Ωs hpair hl
  have hF : ContDiffOn ℝ ∞ (fun w => 2 * sigmaSrc Ω Ωs w) D := (hσC.mono hDG).const_smul (2 : ℝ)
  have hFb : ∀ w ∈ D, 0 ≤ 2 * sigmaSrc Ω Ωs w ∧ 2 * sigmaSrc Ω Ωs w ≤ 4 / 3 := fun w hw =>
    ⟨by linarith [(hσb w (hDG hw)).1], by linarith [(hσb w (hDG hw)).2]⟩
  obtain ⟨-, G, hG, hGb⟩ := prop_dirichlet_a Ω Ωs hJ D (C₁ * ε) _ _ _ hadm
    (fun w => 2 * sigmaSrc Ω Ωs w) (4 / 3) hF hFb
  have hG0 : ∀ w ∈ D, 0 ≤ G w := fun w hw => (hGb w hw).1
  have htG := htbu η R hη hη1 hR1 Ω Ωs hpair hl lab hlab S ℓ hnet p hp hKt G hG hG0
  have hb0 : ∀ w, 0 ≤ (if (badSet Ω Ωs η R).Nonempty then barrierFn Ω S ℓ Cb w else 0) := by
    intro w
    split_ifs
    · exact mul_nonneg hCb (tsum_nonneg fun _ => (Real.exp_pos _).le)
    · exact le_rfl
  have hac : (hypArea Ω).restrict D ≪ volume.restrict D :=
    ((withDensity_absolutelyContinuous _ _ : hypArea Ω ≪ volume.restrict Ω).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)).restrict D
  have hGm : AEMeasurable (fun w => ENNReal.ofReal (intrKernel Ω p w * G w))
      ((hypArea Ω).restrict D) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (((hkC.mono hDΩ).mul hG.1.continuousOn).aemeasurable hDm)).mono_ac hac
  -- (1) `K_V ≤ ∫_{𝒮_D} + ∫_{𝒩 \ 𝒮_D}`
  have h1 : KV Ω Ωs lab p ≤
      ∫⁻ q in slabRegion Ω Ωs D, ENNReal.ofReal (intrKernel Ω p (lab q)) ∂hvol +
        ∫⁻ q in gap Ω Ωs \ slabRegion Ω Ωs D, ENNReal.ofReal (intrKernel Ω p (lab q)) ∂hvol := by
    have hsub : gap Ω Ωs ⊆ slabRegion Ω Ωs D ∪ (gap Ω Ωs \ slabRegion Ω Ωs D) := by
      intro q hq
      by_cases hqs : q ∈ slabRegion Ω Ωs D
      · exact Or.inl hqs
      · exact Or.inr ⟨hq, hqs⟩
    exact (lintegral_mono_set hsub).trans (lintegral_union_le _ _ _)
  -- (2) the slab: `∫_{𝒮_D} ≤ 2 ∫_D k t ≤ 2 (∫_D k b + ∫_D k G)`
  have h2 : ∫⁻ w in D, ENNReal.ofReal (intrKernel Ω p w * slabTop Ω Ωs w) ∂hypArea Ω ≤
      ∫⁻ w in D, ENNReal.ofReal (intrKernel Ω p w *
          (if (badSet Ω Ωs η R).Nonempty then barrierFn Ω S ℓ Cb w else 0)) ∂hypArea Ω +
        ∫⁻ w in D, ENNReal.ofReal (intrKernel Ω p w * G w) ∂hypArea Ω := by
    rw [← lintegral_add_right' _ hGm]
    refine setLIntegral_mono' hDm fun w hw => ?_
    rw [← ENNReal.ofReal_add (mul_nonneg (hk w) (hb0 w)) (mul_nonneg (hk w) (hG0 w hw)), ← mul_add]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (htG w hw) (hk w))
  -- (3) the barrier: `∫_D k b ≤ 12π C_b ∑ᵢ k(ℓᵢ) ≤ 12π C_b C_cnt K_{H,2}`
  have h3 : ∫⁻ w in D, ENNReal.ofReal (intrKernel Ω p w *
      (if (badSet Ω Ωs η R).Nonempty then barrierFn Ω S ℓ Cb w else 0)) ∂hypArea Ω ≤
        a * KH2 Ω Ωs lab p := by
    by_cases hB : (badSet Ω Ωs η R).Nonempty
    · simp only [hB, ↓reduceIte]
      calc _ ≤ ENNReal.ofReal (12 * π * Cb) * ∑' b : S, ENNReal.ofReal (intrKernel Ω p (ℓ b)) :=
            s05_tu_barrier_int hJ hSc hℓ hCb hDm hp
        _ ≤ ENNReal.ofReal (12 * π * Cb) * ((Ccnt : ℝ≥0∞) * KH2 Ω Ωs lab p) := by
            gcongr
            exact hcnt Ω Ωs hpair hl lab hlab S ℓ hnet hB p hp
        _ = a * KH2 Ω Ωs lab p := (mul_assoc _ _ _).symm
    · simp only [hB, ↓reduceIte, mul_zero, ENNReal.ofReal_zero, lintegral_zero]
      exact zero_le
  -- (4) the Dirichlet part: `∫_D k G ≤ (2 - 11C₁ε)⁻¹ ∫_D k 2σ ≤ … K_{H,2}`
  have h4 : ∫⁻ w in D, ENNReal.ofReal (intrKernel Ω p w * G w) ∂hypArea Ω ≤ b * KH2 Ω Ωs lab p := by
    calc _ ≤ ENNReal.ofReal (1 / (2 - 11 * (C₁ * ε))) *
          ∫⁻ w in D, ENNReal.ofReal (intrKernel Ω p w * (2 * sigmaSrc Ω Ωs w)) ∂hypArea Ω :=
          prop_dirichlet_b Ω Ωs hJ D (C₁ * ε) _ _ _ hadm _ (4 / 3) hF hFb G hG p hp
      _ = ENNReal.ofReal (1 / (2 - 11 * (C₁ * ε))) *
          (2 * ∫⁻ w in D, ENNReal.ofReal (intrKernel Ω p w * sigmaSrc Ω Ωs w) ∂hypArea Ω) := by
          rw [← lintegral_const_mul' 2 _ (by norm_num)]
          congr 1
          refine lintegral_congr fun w => ?_
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (1 / (2 - 11 * (C₁ * ε))) *
          (2 * (ENNReal.ofReal (4 / 3 * ((1 - 10 * ε) ^ 2)⁻¹) * KH2 Ω Ωs lab p)) := by
          gcongr
          exact (hsrc η R hη hη6 hR6 Ω Ωs hpair hl lab hlab D hDG hDm p hp).2.2
      _ = b * KH2 Ω Ωs lab p := by
          rw [hbdef]
          ring
  -- (5) the bad region: `∫_{𝒩 \ 𝒮_D} ≤ C_bad ∑ᵢ k(ℓᵢ) ≤ C_bad C_cnt K_{H,2}`
  have h5 : ∫⁻ q in gap Ω Ωs \ slabRegion Ω Ωs D, ENNReal.ofReal (intrKernel Ω p (lab q)) ∂hvol ≤
      c * KH2 Ω Ωs lab p := by
    obtain ⟨hbn, hbe⟩ := hbru η R hη hη2 hR2 Ω Ωs hpair hl lab hlab S ℓ hnet
    by_cases hB : (badSet Ω Ωs η R).Nonempty
    · calc _ ≤ (Cbad : ℝ≥0∞) * ∑' b : S, ENNReal.ofReal (intrKernel Ω p (ℓ b)) := hbn hB p hp
        _ ≤ (Cbad : ℝ≥0∞) * ((Ccnt : ℝ≥0∞) * KH2 Ω Ωs lab p) := by
            gcongr
            exact hcnt Ω Ωs hpair hl lab hlab S ℓ hnet hB p hp
        _ = c * KH2 Ω Ωs lab p := (mul_assoc _ _ _).symm
    · rw [(hbe (not_nonempty_iff_eq_empty.1 hB)).2, Measure.restrict_empty, lintegral_zero_measure]
      exact zero_le
  -- (6) assembly
  calc KV Ω Ωs lab p
      ≤ 2 * (a * KH2 Ω Ωs lab p + b * KH2 Ω Ωs lab p) + c * KH2 Ω Ωs lab p := by
        refine h1.trans (add_le_add ?_ h5)
        refine (hsv η R hη hη5 hR5 Ω Ωs hpair hl lab hlab D hDo hDG p hp).trans ?_
        gcongr
        exact h2.trans (add_le_add h3 h4)
    _ = (2 * (a + b) + c) * KH2 Ω Ωs lab p := by ring
    _ ≤ Cen * KH2 Ω Ωs lab p := by
        gcongr
        exact le_self_add

end EpsteinVMO
