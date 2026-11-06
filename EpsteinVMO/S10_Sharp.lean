import EpsteinVMO.Defs
import EpsteinVMO.S05_Upper
import EpsteinVMO.S09_Ambient
import TakhtajanTeo.Ch1.AhlforsWeillCompleted
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.DistributionalLaplacian
import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl
import TauCeti.Analysis.InnerProductSpace.Harmonic.Reflection
import TauCeti.Analysis.InnerProductSpace.Harmonic.Analytic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry
import TauCeti.Analysis.Sobolev.Trace.IntegrationByParts

/-!
# §10 Small Schwarzian norms: local positivity and rigidity (Theorems C and D)

Source: `sec10-sharp.tex`.  Curves are Jordan curves through `∞`, given as pairs `(Ω, Ωs)`
(`Defs.lean`, Convention 2.1); "`Γ` is a circle" is `IsLinePair Ω Ωs`.

## Modelling choices

* `sup_Ω s < c` is `SchwarzSupLt Ω c` (`∃ c' < c, s ≤ c'` on `Ω`); a bare `sSup` in `ℝ` would be `0`
  for an unbounded set.
* The hyperbolic plane `S ≅ ℍ²` of §10.2 is the disk model `(𝔻, 4|dz|²/(1-|z|²)²)`: distance
  `diskDist`, area `diskHypArea`, Laplacian `hypLaplacianDisk = ((1-|z|²)/2)² Δ_E`.
* A totally geodesic plane `Π ⊂ ℍ³` with its intrinsic geometry is an isometric embedding
  `ι : 𝔻 → ℍ³` (`IsPlaneEmbedding`); the image of an isometric embedding of `ℍ²` is totally
  geodesic, and every such plane arises this way.  `κ_Π ∘ ι = k_P ∘ ι`.
* The thickness `t`, the map `N`, its area Jacobian `J_N`, the normal map `E` and the source `σ`
  are §4's `slabTop`, `slabMap`, `jacN`, `normalMap`, `sigmaSrc` (`S04_Tube`).
* `𝓛` is §5's `graphOp` on `D = Ω`, with coefficients `graphCoeffs Ω Ωs Ω`; `𝓛*` is `ellOpAdj` with
  the same coefficients; `𝒢_Ω`, `𝒢*_Ω`, `𝒢⁰_Ω` are `dirichletInv` (`𝓛₀ = 2 - Δ_ρ` has coefficients
  `a = ρ⁻² I`, `b = 0`, `c = 2`).  `u = 𝒢*_Ω κ` and `v = 𝒢⁰_Ω κ` enter as `∀ u, u = … → …`.
  `dirichletInv` is a choice (`0` if no Dirichlet inverse exists); under the hypotheses used here
  existence is `prop_dirichlet_a`, so `dirichletInv` is a genuine Dirichlet inverse (some
  conclusions, e.g. `lem_duality` (b), would also hold for the junk value `0`; none is proved
  through it).
  `lem:model-lower` (a), (c) are stated for the explicit convolution `𝔊 * κ`, which is `v` by (b).
* Constants of §4–§5 (`ε₀`, `η(ε)`, `C_J`, `C₂`, `C₃`) are quantified existentially in each
  statement, in the order of the paper (absolute constants first, then `ε`, then `η(ε)`, then the
  curve).  Since every hypothesis `sup s < η` is monotone in `η`, the existentials of different
  statements can be combined by taking minima.

## Not formalized here (deferred, report to the leader)

* `lem:curve-comparison`: needs the `ρ`-exponential map, `dX`, and geodesics of the tangent plane
  `Π_p`; it is an internal step of `lem:model-lower` (c), which is stated.
* `rem:global`: heuristic comparison with external notions (Weil–Petersson renormalized volume,
  Liouville action, convex cocompact manifolds) that the paper does not define.
* `rem:sharp-constants` (ii), (iii): (ii) is `thm_plane_ratio_c` + `rem_linear_model_sharp`;
  (iii) is informal ("not explicit").
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff

noncomputable section

namespace EpsteinVMO

open LiZhongQC

/-! ## Section-local definitions -/

/-- `sup_Ω s < c`: the Schwarzian norm of `Ω` is bounded on `Ω` by some `c' < c`. -/
def SchwarzSupLt (Ω : Set ℂ) (c : ℝ) : Prop :=
  ∃ c' < c, ∀ w ∈ Ω, schwarzNorm Ω w ≤ c'

/-- The Legendre function of the second kind of degree one, `Q₁(x) = x artanh(1/x) - 1` (10.1),
for `x > 1`. -/
def legendreQ1 (x : ℝ) : ℝ := x * Real.artanh (1 / x) - 1

/-- The resolvent kernel `𝔊(r) = Q₁(cosh r)/(2π)` of `2 - Δ` on `ℍ²`. -/
def resolventG (r : ℝ) : ℝ := legendreQ1 (Real.cosh r) / (2 * π)

/-- `ϑ(Λ) = ∫_Λ^∞ 𝔊(r) 2π tanh r dr`. -/
def resolventTail (Λ : ℝ) : ℝ := ∫ r in Ioi Λ, resolventG r * (2 * π * Real.tanh r)

/-- The hyperbolic area `4 dA/(1-|z|²)²` of the disk model. -/
def diskHypArea : Measure ℂ :=
  (volume.restrict unitDisc).withDensity fun z => ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2)

/-- The Laplace–Beltrami operator of the disk model, `Δ_ρ φ = ((1-|z|²)/2)² Δ_E φ`. -/
def hypLaplacianDisk (φ : ℂ → ℝ) (z : ℂ) : ℝ :=
  ((1 - ‖z‖ ^ 2) / 2) ^ 2 * Laplacian.laplacian φ z

/-- `(𝔊 * φ)(a) = ∫_𝔻 𝔊(d(a,b)) φ(b) dâ(b)` in the disk model. -/
def resolventConvDisk (φ : ℂ → ℝ) (a : ℂ) : ℝ≥0∞ :=
  ∫⁻ b, ENNReal.ofReal (resolventG (diskDist a b) * φ b) ∂diskHypArea

/-- `(𝔊 * φ)(p) = ∫_Ω 𝔊(d_ρ(p,w)) φ(w) dâ(w)` on a simply connected domain `Ω`. -/
def resolventConv (Ω : Set ℂ) (φ : ℂ → ℝ) (p : ℂ) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal (resolventG (poincareDist Ω p w) * φ w) ∂hypArea Ω

/-- The disk automorphism `z ↦ (z + a)/(1 + ā z)`, sending `0` to `a`. -/
def diskMob (a z : ℂ) : ℂ := (z + a) / (1 + conj a * z)

/-- The mean `m_r(a)` of `φ` over the hyperbolic circle of radius `r` about `a` (w.r.t. arclength):
the circle is the image of `|z| = tanh(r/2)` under `diskMob a`, and arclength is proportional to
the angle. -/
def circleMean (φ : ℂ → ℝ) (a : ℂ) (r : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
    φ (diskMob a ((Real.tanh (r / 2) : ℂ) * Complex.exp ((θ : ℂ) * I)))

/-- `ι` is an isometric embedding of the disk model of `ℍ²` into `ℍ³`; its image is a totally
geodesic plane `Π`, with `ι` an isometry of `𝔻` onto `Π`. -/
def IsPlaneEmbedding (ι : ℂ → ℂ × ℝ) : Prop :=
  MapsTo ι unitDisc UHS ∧ ∀ a ∈ unitDisc, ∀ b ∈ unitDisc, hdist (ι a) (ι b) = diskDist a b

/-- Data of the linearized model (Remark 10.6): a plane `ι`, a centre `P`, a smooth bounded source
`σ ≥ 0` and a bounded `C²` solution `t` of `(2 - Δ) t = 2σ` on the plane. -/
def IsLinearModelData (ι : ℂ → ℂ × ℝ) (P : ℂ × ℝ) (σ t : ℂ → ℝ) : Prop :=
  IsPlaneEmbedding ι ∧ P ∈ UHS ∧ ContDiffOn ℝ ∞ σ unitDisc ∧ (∀ z ∈ unitDisc, 0 ≤ σ z) ∧
    (∃ M : ℝ, ∀ z ∈ unitDisc, σ z ≤ M) ∧ ContDiffOn ℝ 2 t unitDisc ∧
    (∃ M : ℝ, ∀ z ∈ unitDisc, |t z| ≤ M) ∧
    ∀ z ∈ unitDisc, 2 * t z - hypLaplacianDisk t z = 2 * σ z

/-- The parameter slab `𝒮̃ = {(w, τ) ∈ Ω × ℝ : 0 < τ < t(w)}`. -/
def gapSlab (Ω : Set ℂ) (t : ℂ → ℝ) : Set (ℂ × ℝ) := {p | p.1 ∈ Ω ∧ 0 < p.2 ∧ p.2 < t p.1}

/-- The kernel transform `𝒯μ(P) = ∫ k_P dμ` (§10.7). -/
def kernelTransform (μ : Measure (ℂ × ℝ)) (P : ℂ × ℝ) : ℝ≥0∞ :=
  ∫⁻ q, ENNReal.ofReal (ambKernel P q) ∂μ

/-! ## §10.1 Statements -/

/-- **Theorem 10.1 (Theorem C)**, `thm:sharp`, `sec10-sharp.tex:17`.  For every `δ > 0` there is
`s_δ > 0` such that for every Jordan curve that is not a circle with `sup_Ω s < s_δ` and
`sup_{Ω*} s* < s_δ` (10.2), and every `P ∈ ℍ³`: (a) `H(P) > 0` and
`(2(1-log 2) - δ) H(P) ≤ V(P) ≤ (1+δ) H(P)` (10.3); (b) if `H(P) < ∞` then `V(P) < ∞` and
`(3/2 - 2 log 2 - δ) H(P) ≤ Ren(P) ≤ (1/2 + δ) H(P)` (10.4). -/
theorem thm_sharp :
    ∀ δ : ℝ, 0 < δ → ∃ sδ : ℝ, 0 < sδ ∧
      ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ¬ IsLinePair Ω Ωs →
        SchwarzSupLt Ω sδ → SchwarzSupLt Ωs sδ → ∀ P ∈ UHS,
          (0 < ambH Ω Ωs P ∧
            ENNReal.ofReal (2 * (1 - Real.log 2) - δ) * ambH Ω Ωs P ≤ ambV Ω Ωs P ∧
            ambV Ω Ωs P ≤ ENNReal.ofReal (1 + δ) * ambH Ω Ωs P) ∧
          (ambH Ω Ωs P < ⊤ → ambV Ω Ωs P < ⊤ ∧
            (((3 / 2 - 2 * Real.log 2 - δ) * (ambH Ω Ωs P).toReal : ℝ) : EReal) ≤ ren Ω Ωs P ∧
            ren Ω Ωs P ≤ (((1 / 2 + δ) * (ambH Ω Ωs P).toReal : ℝ) : EReal)) := by
  sorry

/-- **Theorem C** (introduction), `sec01-intro.tex:265`; it is Theorem 10.1 (`thm_sharp`). -/
theorem thm_C :
    ∀ δ : ℝ, 0 < δ → ∃ sδ : ℝ, 0 < sδ ∧
      ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ¬ IsLinePair Ω Ωs →
        SchwarzSupLt Ω sδ → SchwarzSupLt Ωs sδ → ∀ P ∈ UHS,
          0 < ambH Ω Ωs P ∧
            ENNReal.ofReal (2 * (1 - Real.log 2) - δ) * ambH Ω Ωs P ≤ ambV Ω Ωs P ∧
            ambV Ω Ωs P ≤ ENNReal.ofReal (1 + δ) * ambH Ω Ωs P ∧
          (ambH Ω Ωs P < ⊤ → ambV Ω Ωs P < ⊤ ∧
            (((3 / 2 - 2 * Real.log 2 - δ) * (ambH Ω Ωs P).toReal : ℝ) : EReal) ≤ ren Ω Ωs P ∧
            ren Ω Ωs P ≤ (((1 / 2 + δ) * (ambH Ω Ωs P).toReal : ℝ) : EReal)) := by
  sorry

/-- **Remark 10.2 (i)**, `rem:sharp-constants`, `sec10-sharp.tex:44`: `3/2 - 2 log 2 > 0`. -/
theorem rem_sharp_constants_i : 0 < 3 / 2 - 2 * Real.log 2 := by
  have := Real.log_two_lt_d9
  norm_num at this ⊢
  linarith

/-- `k_P(Q) ≤ e^{d(P,P')} k_{P'}(Q)` for every `Q` of height `≥ 0`.  The branch `Q.2 = 0` is
closed through junk values (both kernels are `1`, since `coshDist = 1 + a/0 = 1`); for the Epstein
points of a Jordan domain it never occurs, as `λ_Ω > 0` on `Ω` (`s02_poincareDensity_pos`). -/
theorem s10_kernel_shift (P P' Q : ℂ × ℝ) (hP : P ∈ UHS) (hP' : P' ∈ UHS) (hQ : 0 ≤ Q.2) :
    ambKernel P Q ≤ Real.exp (hdist P P') * ambKernel P' Q := by
  rcases hQ.lt_or_eq with h | h
  · exact (lem_ambient_kernel_e P Q Q P' hP h h hP').2.2.1
  · have hd : 0 ≤ hdist P P' := Real.arcosh_nonneg (s09_one_le_coshDist P P' hP hP')
    have e : ∀ R : ℂ × ℝ, ambKernel R Q = 1 := by
      intro R
      show ((Real.cosh (Real.arcosh
        (1 + (‖R.1 - Q.1‖ ^ 2 + (R.2 - Q.2) ^ 2) / (2 * R.2 * Q.2)) / 2))⁻¹) ^ 2 = 1
      rw [← h]
      simp
    rw [e P, e P', mul_one]
    exact Real.one_le_exp hd

/-- The height of the Epstein point is `≥ 0` (`λ_Ω ≥ 0`). -/
theorem s10_epstein_snd_nonneg (Ω : Set ℂ) (w : ℂ) : 0 ≤ (epstein Ω w).2 := by
  have hl : 0 ≤ poincareDensity Ω w := by
    show 0 ≤ 2 / sSup {r : ℝ | ∃ g : ℂ → ℂ, DifferentiableOn ℂ g unitDisc ∧
      MapsTo g unitDisc Ω ∧ g 0 = w ∧ r = ‖deriv g 0‖}
    refine div_nonneg (by norm_num) (Real.sSup_nonneg fun x hx => ?_)
    obtain ⟨g, -, -, -, rfl⟩ := hx
    exact norm_nonneg _
  show 0 ≤ 2 * poincareDensity Ω w / (poincareDensity Ω w ^ 2 + 4 * ‖logDensityDz Ω w‖ ^ 2)
  positivity

/-- The `ℝ≥0∞` form of `s10_kernel_shift`. -/
theorem s10_kernel_shift_ennreal (P P' Q : ℂ × ℝ) (hP : P ∈ UHS) (hP' : P' ∈ UHS)
    (hQ : 0 ≤ Q.2) :
    ENNReal.ofReal (ambKernel P Q) ≤
      ENNReal.ofReal (Real.exp (hdist P P')) * ENNReal.ofReal (ambKernel P' Q) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal (s10_kernel_shift P P' Q hP hP' hQ)

/-- Proof of `rem_H_finite_a`. -/
theorem s10_rem_H_finite_a (Ω Ωs : Set ℂ) (P P' : ℂ × ℝ) (hP : P ∈ UHS) (hP' : P' ∈ UHS) :
    ambH Ω Ωs P ≤ ENNReal.ofReal (Real.exp (hdist P P')) * ambH Ω Ωs P' := by
  show (∫⁻ w, ENNReal.ofReal (ambKernel P (epstein Ω w)) ∂curvMass Ω) +
      (∫⁻ z, ENNReal.ofReal (ambKernel P (epstein Ωs z)) ∂curvMass Ωs) ≤
    ENNReal.ofReal (Real.exp (hdist P P')) *
      ((∫⁻ w, ENNReal.ofReal (ambKernel P' (epstein Ω w)) ∂curvMass Ω) +
        ∫⁻ z, ENNReal.ofReal (ambKernel P' (epstein Ωs z)) ∂curvMass Ωs)
  rw [mul_add, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact add_le_add
    (lintegral_mono fun w => s10_kernel_shift_ennreal P P' _ hP hP' (s10_epstein_snd_nonneg Ω w))
    (lintegral_mono fun z => s10_kernel_shift_ennreal P P' _ hP hP' (s10_epstein_snd_nonneg Ωs z))

/-- Proof of `rem_H_finite_b`. -/
theorem s10_rem_H_finite_b (Ω Ωs : Set ℂ) (P P' : ℂ × ℝ) (hP : P ∈ UHS) (hP' : P' ∈ UHS) :
    ambV Ω Ωs P ≤ ENNReal.ofReal (Real.exp (hdist P P')) * ambV Ω Ωs P' := by
  show (∫⁻ q in gap Ω Ωs, ENNReal.ofReal (ambKernel P q) ∂hvol) ≤
    ENNReal.ofReal (Real.exp (hdist P P')) * ∫⁻ q in gap Ω Ωs, ENNReal.ofReal (ambKernel P' q) ∂hvol
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  have hU : MeasurableSet UHS := measurableSet_lt measurable_const measurable_snd
  have h1 : ∀ᵐ q ∂hvol, q ∈ UHS := by
    show ∀ᵐ q ∂((volume.restrict UHS).withDensity fun q => ENNReal.ofReal ((q.2 ^ 3)⁻¹)), q ∈ UHS
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hU)
  filter_upwards [ae_restrict_of_ae h1] with q hq
  exact s10_kernel_shift_ennreal P P' q hP hP' (show 0 < q.2 from hq).le

/-- **Remark 10.3**, `rem:H-finite`, `sec10-sharp.tex:61`: `H(P) ≤ e^{d(P,P')} H(P')`. -/
theorem rem_H_finite_a (Ω Ωs : Set ℂ) (hJ : IsJordanPair Ω Ωs) (P P' : ℂ × ℝ) (hP : P ∈ UHS)
    (hP' : P' ∈ UHS) :
    ambH Ω Ωs P ≤ ENNReal.ofReal (Real.exp (hdist P P')) * ambH Ω Ωs P' := by
  -- `hJ` is not needed: the bound is pointwise in the kernel; the statement stays true without it.
  have _hJ := hJ
  exact s10_rem_H_finite_a Ω Ωs P P' hP hP'

/-- **Remark 10.3**, `rem:H-finite`, `sec10-sharp.tex:61`: `V(P) ≤ e^{d(P,P')} V(P')`. -/
theorem rem_H_finite_b (Ω Ωs : Set ℂ) (hJ : IsJordanPair Ω Ωs) (P P' : ℂ × ℝ) (hP : P ∈ UHS)
    (hP' : P' ∈ UHS) :
    ambV Ω Ωs P ≤ ENNReal.ofReal (Real.exp (hdist P P')) * ambV Ω Ωs P' := by
  -- `hJ` is not needed: the bound is pointwise in the kernel; the statement stays true without it.
  have _hJ := hJ
  exact s10_rem_H_finite_b Ω Ωs P P' hP hP'

/-- Proof of `rem_H_finite_c`. -/
theorem s10_rem_H_finite_c (Ω : Set ℂ) (f : ℂ → ℂ) (hf : IsConformalOnto f unitDisc Ω) :
    KH Ω (f 0) = (1 / 4 : ℝ≥0∞) *
      ∫⁻ z in unitDisc, ENNReal.ofReal (‖schwarzian f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) := by
  classical
  set g := Function.invFunOn f unitDisc with hgdef
  have hfc : ContinuousOn f unitDisc := hf.1.continuousOn
  have hH : IsHomeomorphOnto f unitDisc (f '' unitDisc) :=
    qcl_f_isHomeomorphOnto_of_injOn isOpen_ball hfc hf.2.1
  have hgc : ContinuousOn g Ω := by
    rw [hgdef, ← hf.2.2]
    exact hH.2.2.2
  have hΩm : MeasurableSet Ω := by
    rw [← hf.2.2]
    exact measurableSet_ball.image_of_continuousOn_injOn hfc hf.2.1
  have hleft : ∀ z ∈ unitDisc, g (f z) = z := fun z hz => hf.2.1.leftInvOn_invFunOn hz
  set ψ : ℂ → ℝ≥0∞ := Ω.piecewise (fun w => ENNReal.ofReal (1 - ‖g w‖ ^ 2)) 0 with hψdef
  have hψm : Measurable ψ := by
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const hΩm
    exact ENNReal.continuous_ofReal.comp_continuousOn
      (continuousOn_const.sub ((continuous_norm.comp_continuousOn hgc).pow 2))
  have hψf : ∀ z ∈ unitDisc, ψ (f z) = ENNReal.ofReal (1 - ‖z‖ ^ 2) := by
    intro z hz
    have hfz : f z ∈ Ω := hf.2.2 ▸ mem_image_of_mem f hz
    simp only [hψdef, Set.piecewise_eq_of_mem _ _ _ hfz, hleft z hz]
  have hK : ∀ w ∈ Ω, ENNReal.ofReal (intrKernel Ω (f 0) w) = ψ w := by
    intro w hw
    rw [← hf.2.2] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
    rw [hψf z hz, s02_intrKernel_eq hf h0 hz]
    simp
  have hae : ∀ᵐ w ∂curvMass Ω, ENNReal.ofReal (intrKernel Ω (f 0) w) = ψ w := by
    have h1 : ∀ᵐ w ∂(volume.restrict Ω), w ∈ Ω := ae_restrict_mem hΩm
    have h2 : ∀ᵐ w ∂curvMass Ω, w ∈ Ω := (withDensity_absolutelyContinuous _ _).ae_le h1
    filter_upwards [h2] with w hw
    exact hK w hw
  show ∫⁻ w, ENNReal.ofReal (intrKernel Ω (f 0) w) ∂curvMass Ω = _
  rw [lintegral_congr_ae hae, eq_pullback_mass_a hf hψm,
    ← lintegral_const_mul' _ _ (by norm_num : (1 / 4 : ℝ≥0∞) ≠ ⊤)]
  refine setLIntegral_congr_fun measurableSet_ball (fun z hz => ?_)
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hr : (0 : ℝ) ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have h4 : (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  rw [hψf z hz, ← ENNReal.ofReal_mul hr, h4, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-- **Remark 10.3**, `rem:H-finite`, `sec10-sharp.tex:70`: for a conformal `f : 𝔻 → Ω`,
`K_H(f(0)) = ¼ ∫_𝔻 |Sf(z)|² (1-|z|²)³ dA(z)`. -/
theorem rem_H_finite_c (Ω : Set ℂ) (f : ℂ → ℂ) (hf : IsConformalOnto f unitDisc Ω) :
    KH Ω (f 0) = (1 / 4 : ℝ≥0∞) *
      ∫⁻ z in unitDisc, ENNReal.ofReal (‖schwarzian f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 3) := by
  exact s10_rem_H_finite_c Ω f hf

/-- Part 1 of `thm_rigidity`: `H < ∞` everywhere (Remark 10.3) and `Ren ≠ -∞`.  The Jordan
hypothesis is not needed. -/
theorem s10_rigidity_part1 (Ω Ωs : Set ℂ) (P₀ : ℂ × ℝ) (hP₀ : P₀ ∈ UHS)
    (hH : ambH Ω Ωs P₀ < ⊤) : ∀ P ∈ UHS, ambH Ω Ωs P < ⊤ ∧ ren Ω Ωs P ≠ ⊥ := by
  intro P hP
  have hHP : ambH Ω Ωs P < ⊤ :=
    lt_of_le_of_lt (s10_rem_H_finite_a Ω Ωs P P₀ hP hP₀)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hH)
  refine ⟨hHP, ?_⟩
  show (ambV Ω Ωs P : EReal) - ((ambH Ω Ωs P / 2 : ℝ≥0∞) : EReal) ≠ ⊥
  rw [sub_eq_add_neg]
  intro h
  rcases EReal.add_eq_bot_iff.1 h with h | h
  · exact EReal.coe_ennreal_ne_bot _ h
  · have h2 := EReal.coe_ennreal_eq_top_iff.1 (EReal.neg_eq_bot_iff.1 h)
    exact ENNReal.div_ne_top hHP.ne two_ne_zero h2

/-- Part 3 of `thm_rigidity`: for a circle, `V ≡ H ≡ Ren ≡ 0` (from S09 `thm_ambient_circle`). -/
theorem s10_rigidity_part3 (Ω Ωs : Set ℂ) (hJ : IsJordanPair Ω Ωs) :
    IsLinePair Ω Ωs → ∀ P ∈ UHS, ambV Ω Ωs P = 0 ∧ ambH Ω Ωs P = 0 ∧ ren Ω Ωs P = 0 := by
  -- `hJ` is not needed: `thm_ambient_circle` uses only the line-pair hypothesis.
  have _hJ := hJ
  intro hL P hP
  obtain ⟨hH, hV⟩ := thm_ambient_circle Ω Ωs hL P hP
  refine ⟨hV, hH, ?_⟩
  show (ambV Ω Ωs P : EReal) - ((ambH Ω Ωs P / 2 : ℝ≥0∞) : EReal) = 0
  rw [hV, hH]
  simp

/-- **Remark 10.5**, `rem:rigidity-scope`, `sec10-sharp.tex:88` (also Remark 10.2 (i)): if
`0 < δ < 3/2 - 2 log 2`, then under the hypotheses of Theorem 10.1, `Ren(P) > 0` at every `P` with
`H(P) < ∞`. -/
theorem rem_rigidity_scope :
    ∀ δ : ℝ, 0 < δ → δ < 3 / 2 - 2 * Real.log 2 → ∃ sδ : ℝ, 0 < sδ ∧
      ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ¬ IsLinePair Ω Ωs →
        SchwarzSupLt Ω sδ → SchwarzSupLt Ωs sδ → ∀ P ∈ UHS, ambH Ω Ωs P < ⊤ →
          0 < ren Ω Ωs P := by
  sorry

/-! ## §10.2 The resolvent kernel of the hyperbolic plane -/

/-- `artanh u = ∑ u^{2k+1}/(2k+1)` for `|u| < 1`. -/
theorem s10_hasSum_artanh {u : ℝ} (hu : |u| < 1) :
    HasSum (fun k : ℕ => u ^ (2 * k + 1) / (2 * k + 1)) (Real.artanh u) := by
  have h1 : u ∈ Icc (-1 : ℝ) 1 := by
    rw [abs_lt] at hu; exact ⟨hu.1.le, hu.2.le⟩
  have hp : 0 < 1 + u := by rw [abs_lt] at hu; linarith
  have hm : 0 < 1 - u := by rw [abs_lt] at hu; linarith
  rw [Real.artanh_eq_half_log h1, Real.log_div hp.ne' hm.ne']
  convert (Real.hasSum_log_sub_log_of_abs_lt_one hu).mul_left (1 / 2) using 1
  funext k
  ring

/-- For `x > 1`, `artanh (1/x) = ½ (log (x+1) - log (x-1))`. -/
theorem s10_artanh_inv {x : ℝ} (hx : 1 < x) :
    Real.artanh (1 / x) = 1 / 2 * (Real.log (x + 1) - Real.log (x - 1)) := by
  have hx0 : 0 < x := by linarith
  have h1 : 1 / x ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · have : 0 < 1 / x := by positivity
      linarith
    · rw [div_le_one hx0]; linarith
  rw [Real.artanh_eq_half_log h1]
  have e : (1 + 1 / x) / (1 - 1 / x) = (x + 1) / (x - 1) := by
    field_simp
  rw [e, Real.log_div (by linarith) (by linarith)]

theorem s10_abs_inv_lt_one {x : ℝ} (hx : 1 < x) : |1 / x| < 1 := by
  have hx0 : 0 < x := by linarith
  rw [abs_of_pos (by positivity), div_lt_one hx0]; exact hx

/-- `x artanh(1/x) = ∑ x^{-2k}/(2k+1)`. -/
theorem s10_hasSum_x_artanh {x : ℝ} (hx : 1 < x) :
    HasSum (fun k : ℕ => (x ^ (2 * k))⁻¹ / (2 * k + 1)) (x * Real.artanh (1 / x)) := by
  have hx0 : x ≠ 0 := by positivity
  convert (s10_hasSum_artanh (s10_abs_inv_lt_one hx)).mul_left x using 1
  funext k
  rw [pow_succ, one_div, inv_pow]
  field_simp

theorem s10_hasSum_Q1 {x : ℝ} (hx : 1 < x) :
    HasSum (fun j : ℕ => (x ^ (2 * (j + 1)))⁻¹ / (2 * (j + 1 : ℝ) + 1)) (legendreQ1 x) := by
  have h := s10_hasSum_x_artanh hx
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.sum_range_one, pow_zero, Nat.cast_zero, mul_zero, zero_add, inv_one,
    div_one] at h
  convert h using 2
  · push_cast; ring_nf
  · rfl

theorem s10_eq_Q1 (x : ℝ) (hx : 1 < x) :
    legendreQ1 x = x / 2 * Real.log ((x + 1) / (x - 1)) - 1 ∧
      HasSum (fun j : ℕ => (x ^ (2 * (j + 1)))⁻¹ / (2 * (j + 1 : ℝ) + 1)) (legendreQ1 x) := by
  refine ⟨?_, s10_hasSum_Q1 hx⟩
  rw [legendreQ1, s10_artanh_inv hx, Real.log_div (by linarith) (by linarith)]
  ring

/-- `d/dx artanh(1/x) = -1/(x²-1)` for `x > 1`. -/
theorem s10_hasDerivAt_artanh_inv {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun y => Real.artanh (1 / y)) (-1 / (x ^ 2 - 1)) x := by
  have h1 : HasDerivAt (fun y => Real.log (y + 1)) (1 / (x + 1)) x := by
    have := ((hasDerivAt_id x).add_const 1).log (by simp; linarith)
    simpa using this
  have h2 : HasDerivAt (fun y => Real.log (y - 1)) (1 / (x - 1)) x := by
    have := ((hasDerivAt_id x).sub_const 1).log (by simp; linarith)
    simpa using this
  have h3 := (h1.sub h2).const_mul (1 / 2 : ℝ)
  have heq : (fun y => Real.artanh (1 / y)) =ᶠ[𝓝 x]
      fun y => 1 / 2 * (Real.log (y + 1) - Real.log (y - 1)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy using s10_artanh_inv hy
  refine (h3.congr_of_eventuallyEq heq).congr_deriv ?_
  have : x + 1 ≠ 0 := by linarith
  have : x - 1 ≠ 0 := by linarith
  have : x ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  ring

theorem s10_hasDerivAt_Q1 {x : ℝ} (hx : 1 < x) :
    HasDerivAt legendreQ1 (Real.artanh (1 / x) - x / (x ^ 2 - 1)) x := by
  have h := ((hasDerivAt_id x).mul (s10_hasDerivAt_artanh_inv hx)).sub_const 1
  refine h.congr_deriv ?_
  simp only [id]
  ring

theorem s10_deriv_Q1_eventually {x : ℝ} (hx : 1 < x) :
    deriv legendreQ1 =ᶠ[𝓝 x] fun y => Real.artanh (1 / y) - y / (y ^ 2 - 1) := by
  filter_upwards [Ioi_mem_nhds hx] with y hy using (s10_hasDerivAt_Q1 hy).deriv

theorem s10_hasDerivAt_deriv_Q1 {x : ℝ} (hx : 1 < x) :
    HasDerivAt (deriv legendreQ1) (2 / (x ^ 2 - 1) ^ 2) x := by
  have hd : HasDerivAt (fun y : ℝ => y ^ 2 - 1) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).sub_const 1
  have hne : x ^ 2 - 1 ≠ 0 := by nlinarith
  have h := (s10_hasDerivAt_artanh_inv hx).sub ((hasDerivAt_id x).div hd hne)
  refine (h.congr_of_eventuallyEq (s10_deriv_Q1_eventually hx)).congr_deriv ?_
  simp only [id]
  field_simp
  ring

theorem s10_lem_plane_green_a (x : ℝ) (hx : 1 < x) :
    0 < legendreQ1 x ∧
      HasDerivAt legendreQ1 (Real.artanh (1 / x) - x / (x ^ 2 - 1)) x ∧
      HasSum (fun j : ℕ => -((2 * (j + 1 : ℝ)) / (2 * (j + 1 : ℝ) + 1) * (x ^ (2 * (j + 1) + 1))⁻¹))
        (Real.artanh (1 / x) - x / (x ^ 2 - 1)) ∧
      HasDerivAt (deriv legendreQ1) (2 / (x ^ 2 - 1) ^ 2) x ∧
      (1 - x ^ 2) * deriv (deriv legendreQ1) x - 2 * x * deriv legendreQ1 x +
        2 * legendreQ1 x = 0 := by
  have hx0 : 0 < x := by linarith
  have hne : x ^ 2 - 1 ≠ 0 := by nlinarith
  refine ⟨?_, s10_hasDerivAt_Q1 hx, ?_, s10_hasDerivAt_deriv_Q1 hx, ?_⟩
  · have h := le_hasSum (s10_hasSum_Q1 hx) 0 (fun j _ => by positivity)
    have : 0 < (x ^ (2 * (0 + 1)))⁻¹ / (2 * ((0 : ℕ) + 1 : ℝ) + 1) := by positivity
    linarith
  · -- `x/(x²-1) = ∑ x^{-(2k+1)}`
    have hr0 : 0 ≤ (x ^ 2)⁻¹ := by positivity
    have hr1 : (x ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
    have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left x⁻¹
    have hgeo : x⁻¹ * (1 - (x ^ 2)⁻¹)⁻¹ = x / (x ^ 2 - 1) := by
      field_simp
    rw [hgeo] at hg
    have ha := s10_hasSum_artanh (s10_abs_inv_lt_one hx)
    have hs := ha.sub hg
    rw [← hasSum_nat_add_iff' 1] at hs
    simp only [Finset.sum_range_one] at hs
    have e0 : (1 / x) ^ (2 * 0 + 1) / (2 * ((0 : ℕ) : ℝ) + 1) - x⁻¹ * ((x ^ 2)⁻¹) ^ 0 = 0 := by
      simp
    rw [e0, sub_zero] at hs
    convert hs using 1
    funext j
    have hx0' : x ≠ 0 := hx0.ne'
    simp only [one_div, inv_pow, ← pow_mul]
    push_cast
    field_simp
    ring
  · rw [(s10_hasDerivAt_deriv_Q1 hx).deriv, (s10_hasDerivAt_Q1 hx).deriv, legendreQ1]
    field_simp
    ring

/-- `u ≤ artanh u ≤ u + u³/(3(1-u²))` for `0 ≤ u < 1`. -/
theorem s10_artanh_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    u ≤ Real.artanh u ∧ Real.artanh u ≤ u + u ^ 3 / (3 * (1 - u ^ 2)) := by
  have hu : |u| < 1 := by rw [abs_of_nonneg hu0]; exact hu1
  have ha := s10_hasSum_artanh hu
  refine ⟨?_, ?_⟩
  · have := le_hasSum ha 0 (fun j _ => by positivity)
    simpa using this
  · have hs := ha
    rw [← hasSum_nat_add_iff' 1] at hs
    simp only [Finset.sum_range_one] at hs
    have hr0 : 0 ≤ u ^ 2 := by positivity
    have hr1 : u ^ 2 < 1 := by nlinarith
    have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (u ^ 3 / 3)
    have hle := hasSum_le (fun k => ?_) hs hg
    · have e : u ^ 3 / 3 * (1 - u ^ 2)⁻¹ = u ^ 3 / (3 * (1 - u ^ 2)) := by
        field_simp
      simp at hle
      rw [e] at hle
      linarith
    · have hk : (3 : ℝ) ≤ 2 * ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith [k.cast_nonneg (α := ℝ)]
      have e : u ^ 3 / 3 * (u ^ 2) ^ k = u ^ (2 * (k + 1) + 1) / 3 := by ring
      rw [e]
      exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hk

theorem s10_hasDerivAt_resolventG {r : ℝ} (hr : 0 < r) :
    HasDerivAt resolventG ((Real.artanh (1 / Real.cosh r) -
      Real.cosh r / (Real.cosh r ^ 2 - 1)) * Real.sinh r / (2 * π)) r := by
  have hc : 1 < Real.cosh r := Real.one_lt_cosh.mpr hr.ne'
  have h := ((s10_hasDerivAt_Q1 hc).comp r (Real.hasDerivAt_cosh r)).div_const (2 * π)
  exact h

theorem s10_two_pi_sinh_deriv {r : ℝ} (hr : 0 < r) :
    2 * π * Real.sinh r * deriv resolventG r =
      Real.sinh r ^ 2 * Real.artanh ((Real.cosh r)⁻¹) - Real.cosh r := by
  rw [(s10_hasDerivAt_resolventG hr).deriv, Real.cosh_sq, one_div]
  have hs : Real.sinh r ≠ 0 := (Real.sinh_pos_iff.mpr hr).ne'
  have : Real.sinh r ^ 2 + 1 - 1 = Real.sinh r ^ 2 := by ring
  rw [this]
  field_simp

theorem s10_lem_plane_green_d (r : ℝ) (hr : 0 < r) :
    -(Real.cosh r)⁻¹ ≤ 2 * π * Real.sinh r * deriv resolventG r ∧
      2 * π * Real.sinh r * deriv resolventG r ≤ -(2 / 3 * (Real.cosh r)⁻¹) := by
  rw [s10_two_pi_sinh_deriv hr]
  set c := Real.cosh r with hc_def
  have hc : 1 < c := Real.one_lt_cosh.mpr hr.ne'
  have hc0 : 0 < c := by linarith
  have hsq : Real.sinh r ^ 2 = c ^ 2 - 1 := by rw [hc_def, Real.cosh_sq]; ring
  rw [hsq]
  have hu0 : 0 ≤ c⁻¹ := by positivity
  have hu1 : c⁻¹ < 1 := inv_lt_one_of_one_lt₀ hc
  obtain ⟨hlo, hhi⟩ := s10_artanh_bounds hu0 hu1
  have hp : 0 ≤ c ^ 2 - 1 := by nlinarith
  have hlo' := mul_le_mul_of_nonneg_left hlo hp
  have hhi' := mul_le_mul_of_nonneg_left hhi hp
  have e1 : (c ^ 2 - 1) * c⁻¹ - c = -c⁻¹ := by field_simp; ring
  have hne : c ^ 2 - 1 ≠ 0 := by nlinarith
  have hne' : 1 - c⁻¹ ^ 2 ≠ 0 := by
    have : c⁻¹ ^ 2 < 1 := by nlinarith
    linarith
  have e2 : (c ^ 2 - 1) * (c⁻¹ + c⁻¹ ^ 3 / (3 * (1 - c⁻¹ ^ 2))) - c = -(2 / 3 * c⁻¹) := by
    field_simp
    ring
  constructor <;> linarith

theorem s10_lem_plane_green_e :
    (∀ x : ℝ, 1 < x → legendreQ1 x ≤ 1 / (3 * (x ^ 2 - 1))) ∧
      StrictAntiOn (fun r => resolventG r / Real.cosh r) (Ioi 0) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · have hr0 : 0 ≤ (x ^ 2)⁻¹ := by positivity
    have hr1 : (x ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
    have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left ((x ^ 2)⁻¹ / 3)
    have hle := hasSum_le (fun j => ?_) (s10_hasSum_Q1 hx) hg
    · have hne : x ^ 2 - 1 ≠ 0 := by nlinarith
      have hx0 : x ≠ 0 := by positivity
      have e : (x ^ 2)⁻¹ / 3 * (1 - (x ^ 2)⁻¹)⁻¹ = 1 / (3 * (x ^ 2 - 1)) := by
        field_simp
      rw [e] at hle
      exact hle
    · have hk : (3 : ℝ) ≤ 2 * ((j : ℝ) + 1) + 1 := by linarith [j.cast_nonneg (α := ℝ)]
      have e : (x ^ 2)⁻¹ / 3 * ((x ^ 2)⁻¹) ^ j = (x ^ (2 * (j + 1)))⁻¹ / 3 := by
        simp only [inv_pow, ← pow_mul]; field_simp; ring
      rw [e]
      exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hk
  · intro a ha b hb hab
    simp only [mem_Ioi] at ha hb
    have hca : 1 < Real.cosh a := Real.one_lt_cosh.mpr ha.ne'
    have hcab : Real.cosh a < Real.cosh b := by
      rw [Real.cosh_lt_cosh, abs_of_pos ha, abs_of_pos hb]; exact hab
    set x := Real.cosh a
    set y := Real.cosh b
    have hx0 : 0 < x := by linarith
    have hy : 1 < y := by linarith
    have hsx := (s10_hasSum_Q1 hca).div_const x
    have hsy := (s10_hasSum_Q1 hy).div_const y
    have hlt : legendreQ1 y / y < legendreQ1 x / x := by
      refine hasSum_lt (f := fun j : ℕ => (y ^ (2 * (j + 1)))⁻¹ / (2 * (j + 1 : ℝ) + 1) / y)
        (g := fun j : ℕ => (x ^ (2 * (j + 1)))⁻¹ / (2 * (j + 1 : ℝ) + 1) / x)
        (i := 0) (fun j => ?_) ?_ hsy hsx
      · beta_reduce
        gcongr
      · gcongr
    show legendreQ1 y / (2 * π) / y < legendreQ1 x / (2 * π) / x
    rw [div_right_comm, div_right_comm (legendreQ1 x)]
    exact div_lt_div_of_pos_right hlt (by positivity)

/-- `sinh t / t → 1` as `t → 0⁺`. -/
theorem s10_sinh_div_tendsto :
    Tendsto (fun t : ℝ => Real.sinh t / t) (𝓝[>] 0) (𝓝 1) := by
  have h := (Real.hasDerivAt_sinh 0).tendsto_slope_zero_right
  simp only [zero_add, Real.sinh_zero, sub_zero, Real.cosh_zero, smul_eq_mul] at h
  refine h.congr' ?_
  filter_upwards with t
  rw [div_eq_inv_mul]

/-- `cosh r - 1 = r²/2 · (sinh(r/2)/(r/2))²`. -/
theorem s10_cosh_sub_one {r : ℝ} (hr : r ≠ 0) :
    Real.cosh r - 1 = r ^ 2 / 2 * (Real.sinh (r / 2) / (r / 2)) ^ 2 := by
  have h := Real.cosh_two_mul (r / 2)
  rw [show 2 * (r / 2) = r by ring] at h
  rw [h, Real.cosh_sq]
  field_simp
  ring

theorem s10_log_cosh_sub_one {r : ℝ} (hr : 0 < r) :
    Real.log (Real.cosh r - 1) =
      2 * Real.log r + 2 * Real.log (Real.sinh (r / 2) / (r / 2)) - Real.log 2 := by
  have hS : 0 < Real.sinh (r / 2) / (r / 2) :=
    div_pos (Real.sinh_pos_iff.mpr (by linarith)) (by linarith)
  rw [s10_cosh_sub_one hr.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_div (by positivity) two_ne_zero, Real.log_pow, Real.log_pow]
  push_cast
  ring

theorem s10_sinh_half_div_tendsto :
    Tendsto (fun r : ℝ => Real.sinh (r / 2) / (r / 2)) (𝓝[>] 0) (𝓝 1) := by
  have h2 : Tendsto (fun r : ℝ => r / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := ((continuous_id.div_const (2 : ℝ)).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      exact (by positivity : (0 : ℝ) < r / 2)
  exact s10_sinh_div_tendsto.comp h2

theorem s10_cosh_tendsto : Tendsto (fun r : ℝ => Real.cosh r) (𝓝[>] 0) (𝓝 1) := by
  have := (Real.continuous_cosh.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa using this

theorem s10_lem_plane_green_c :
    Tendsto (fun r => 2 * π * resolventG r + Real.log r) (𝓝[>] 0) (𝓝 (Real.log 2 - 1)) ∧
      (∀ r : ℝ, 0 < r → 2 * π * Real.sinh r * deriv resolventG r =
        Real.sinh r ^ 2 * Real.artanh ((Real.cosh r)⁻¹) - Real.cosh r) ∧
      Tendsto (fun r => 2 * π * Real.sinh r * deriv resolventG r) (𝓝[>] 0) (𝓝 (-1)) := by
  have hS := s10_sinh_half_div_tendsto
  have hc := s10_cosh_tendsto
  have hlogS : Tendsto (fun r : ℝ => Real.log (Real.sinh (r / 2) / (r / 2))) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuousAt_log one_ne_zero).tendsto).comp hS
    rw [Real.log_one] at this
    exact this
  have hlogc1 : Tendsto (fun r : ℝ => Real.log (Real.cosh r + 1)) (𝓝[>] 0) (𝓝 (Real.log 2)) := by
    have := ((Real.continuousAt_log (by norm_num : (1 : ℝ) + 1 ≠ 0)).tendsto).comp
      (hc.add_const 1)
    rw [show (1 : ℝ) + 1 = 2 by norm_num] at this
    exact this
  have hrl : Tendsto (fun r : ℝ => Real.log r * r ^ (2 : ℝ)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_log_mul_rpow_nhdsGT_zero two_pos
  refine ⟨?_, fun r hr => s10_two_pi_sinh_deriv hr, ?_⟩
  · have hlim := ((((hc.div_const 2).mul hlogc1).add ((hc.div_const 2).mul_const
      (Real.log 2))).sub (hc.mul hlogS)).sub_const 1 |>.sub (((hS.pow 2).div_const 2).mul hrl)
    have e : 1 / 2 * Real.log 2 + 1 / 2 * Real.log 2 - 1 * 0 - 1 - 1 ^ 2 / 2 * 0 =
        Real.log 2 - 1 := by ring
    rw [e] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    have hc1 : 1 < Real.cosh r := Real.one_lt_cosh.mpr hr.ne'
    have hq := (s10_eq_Q1 (Real.cosh r) hc1).1
    have hG : 2 * π * resolventG r = legendreQ1 (Real.cosh r) := by
      simp only [resolventG]
      field_simp
    rw [hG, hq, Real.log_div (x := Real.cosh r + 1) (y := Real.cosh r - 1) (by linarith)
      (by linarith), s10_log_cosh_sub_one hr,
      Real.rpow_two]
    have hrS : (Real.sinh (r / 2) / (r / 2)) ^ 2 / 2 * (Real.log r * r ^ 2) =
        (Real.cosh r - 1) * Real.log r := by
      rw [s10_cosh_sub_one hr.ne']
      ring
    rw [hrS]
    ring
  · have hT := s10_sinh_div_tendsto
    have hsh : Tendsto (fun r : ℝ => Real.sinh r ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have := ((Real.continuous_sinh.tendsto 0).pow 2).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    have hlim := (((((hsh.div_const 2).mul hlogc1).sub ((hT.pow 2).mul hrl)).sub
      (hsh.mul hlogS)).add ((hsh.div_const 2).mul_const (Real.log 2))).sub hc
    have e : 0 / 2 * Real.log 2 - 1 ^ 2 * 0 - 0 * 0 + 0 / 2 * Real.log 2 - 1 = -1 := by ring
    rw [e] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    have hc1 : 1 < Real.cosh r := Real.one_lt_cosh.mpr hr.ne'
    rw [s10_two_pi_sinh_deriv hr, ← one_div, s10_artanh_inv hc1, s10_log_cosh_sub_one hr,
      Real.rpow_two]
    have e2 : (Real.sinh r / r) ^ 2 * (Real.log r * r ^ 2) = Real.sinh r ^ 2 * Real.log r := by
      field_simp
    rw [e2]
    ring


/-- **(10.1)**, `eq:Q1`, `sec10-sharp.tex:115`: for `x > 1`,
`Q₁(x) = (x/2) log((x+1)/(x-1)) - 1 = ∑_{j ≥ 1} x^{-2j}/(2j+1)`. -/
theorem eq_Q1 (x : ℝ) (hx : 1 < x) :
    legendreQ1 x = x / 2 * Real.log ((x + 1) / (x - 1)) - 1 ∧
      HasSum (fun j : ℕ => (x ^ (2 * (j + 1)))⁻¹ / (2 * (j + 1 : ℝ) + 1)) (legendreQ1 x) := by
  exact s10_eq_Q1 x hx

/-- **Lemma 10.6 (a)**, `lem:plane-green`, `sec10-sharp.tex:134`: `Q₁ > 0` on `(1, ∞)`,
`Q₁' = artanh(1/x) - x/(x²-1) = -∑ (2j/(2j+1)) x^{-2j-1}`, `Q₁'' = 2/(x²-1)²`, and Legendre's
equation `(1-x²)Q₁'' - 2xQ₁' + 2Q₁ = 0`. -/
theorem lem_plane_green_a (x : ℝ) (hx : 1 < x) :
    0 < legendreQ1 x ∧
      HasDerivAt legendreQ1 (Real.artanh (1 / x) - x / (x ^ 2 - 1)) x ∧
      HasSum (fun j : ℕ => -((2 * (j + 1 : ℝ)) / (2 * (j + 1 : ℝ) + 1) * (x ^ (2 * (j + 1) + 1))⁻¹))
        (Real.artanh (1 / x) - x / (x ^ 2 - 1)) ∧
      HasDerivAt (deriv legendreQ1) (2 / (x ^ 2 - 1) ^ 2) x ∧
      (1 - x ^ 2) * deriv (deriv legendreQ1) x - 2 * x * deriv legendreQ1 x +
        2 * legendreQ1 x = 0 := by
  exact s10_lem_plane_green_a x hx

/-- For `f` of class `C²` at `z`, the second directional derivative `D²f(z)[v, v]` is the second
derivative at `0` of the restriction `t ↦ f(z + t v)`. -/
theorem s10_fderiv_fderiv_line {f : ℂ → ℝ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) (v : ℂ) :
    fderiv ℝ (fderiv ℝ f) z v v = deriv (deriv fun t : ℝ => f (z + t • v)) 0 := by
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => z + s • v) v t := fun t => by
    have h := ((hasDerivAt_id t).smul_const v).const_add z
    rw [one_smul] at h
    exact h
  have hcont : Tendsto (fun t : ℝ => z + t • v) (𝓝 0) (𝓝 z) := by
    have h := (hline 0).continuousAt.tendsto
    rw [zero_smul, add_zero] at h
    exact h
  have hev : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ f w :=
    (hf.eventually (by decide)).mono fun w hw => hw.differentiableAt two_ne_zero
  have hd2 : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have h1 : deriv (fun t : ℝ => f (z + t • v)) =ᶠ[𝓝 0]
      fun t => fderiv ℝ f (z + t • v) v := by
    filter_upwards [hcont.eventually hev] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hline t)).deriv
  rw [h1.deriv_eq]
  have hz : (fun s : ℝ => z + s • v) 0 = z := by
    show z + (0 : ℝ) • v = z
    rw [zero_smul, add_zero]
  have hd2' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) ((fun s : ℝ => z + s • v) 0) := by
    rw [hz]
    exact hd2.hasFDerivAt
  have hc : HasDerivAt (fun t : ℝ => fderiv ℝ f (z + t • v)) (fderiv ℝ (fderiv ℝ f) z v) 0 :=
    HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => z + s • v) (0 : ℝ) hd2' (hline 0)
  have h2 : HasDerivAt (fun t : ℝ => fderiv ℝ f (z + t • v) v)
      (fderiv ℝ (fderiv ℝ f) z v v + fderiv ℝ f (z + (0 : ℝ) • v) 0) 0 :=
    hc.clm_apply (hasDerivAt_const (0 : ℝ) v)
  rw [map_zero, add_zero] at h2
  exact h2.deriv.symm

/-- The 1D chain rule of order two: `(F ∘ q)''(0) = F''(q 0) q'(0)² + F'(q 0) q''(0)`. -/
theorem s10_deriv_deriv_comp {F q q' : ℝ → ℝ} {q2 : ℝ} (hF : ContDiffOn ℝ 2 F (Ioi 1))
    (hq0 : 1 < q 0) (hq : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt q (q' t) t) (hq2 : HasDerivAt q' q2 0) :
    deriv (deriv fun t => F (q t)) 0 =
      deriv (deriv F) (q 0) * q' 0 ^ 2 + deriv F (q 0) * q2 := by
  have hFat : ∀ x : ℝ, 1 < x → ContDiffAt ℝ 2 F x := fun x hx =>
    hF.contDiffAt (Ioi_mem_nhds hx)
  have hqc : ContinuousAt q 0 := (hq.self_of_nhds).continuousAt
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 1 < q t := hqc.eventually (Ioi_mem_nhds hq0)
  have h1 : deriv (fun t => F (q t)) =ᶠ[𝓝 0] fun t => deriv F (q t) * q' t := by
    filter_upwards [hq, hev] with t ht hqt
    have hd : DifferentiableAt ℝ F (q t) := (hFat _ hqt).differentiableAt two_ne_zero
    exact (hd.hasDerivAt.comp t ht).deriv
  rw [h1.deriv_eq]
  have hdF : DifferentiableAt ℝ (deriv F) (q 0) := by
    have h := (hFat _ hq0).fderiv_right (m := 1) le_rfl
    have h' : ContDiffAt ℝ 1 (fun x => fderiv ℝ F x 1) (q 0) := h.clm_apply contDiffAt_const
    simp only [fderiv_eq_smul_deriv, one_smul] at h'
    exact h'.differentiableAt one_ne_zero
  have h2 : HasDerivAt (fun t => deriv F (q t) * q' t)
      (deriv (deriv F) (q 0) * q' 0 * q' 0 + deriv F (q 0) * q2) 0 :=
    (hdF.hasDerivAt.comp 0 hq.self_of_nhds).mul hq2
  rw [h2.deriv]
  ring

/-- `q(t) = 1 + 2((α - t v₁)² + (β - t v₂)²)/(A(1 - (x + t v₁)² - (y + t v₂)²))` has explicit first
and second derivatives at `0`. -/
theorem s10_quad_ratio_deriv (α β x y v₁ v₂ A : ℝ) (hA : A ≠ 0) (hB : 1 - x ^ 2 - y ^ 2 ≠ 0) :
    ∃ q' : ℝ → ℝ, (∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (fun t => 1 + 2 * ((α - t * v₁) ^ 2 +
        (β - t * v₂) ^ 2) / (A * (1 - (x + t * v₁) ^ 2 - (y + t * v₂) ^ 2))) (q' t) t) ∧
      q' 0 = 2 * ((-2 * (α * v₁ + β * v₂)) * (1 - x ^ 2 - y ^ 2) -
        (α ^ 2 + β ^ 2) * (-2 * (x * v₁ + y * v₂))) / (A * (1 - x ^ 2 - y ^ 2) ^ 2) ∧
      HasDerivAt q' (2 * (((2 * (v₁ ^ 2 + v₂ ^ 2)) * (1 - x ^ 2 - y ^ 2) -
          (α ^ 2 + β ^ 2) * (-2 * (v₁ ^ 2 + v₂ ^ 2))) * (1 - x ^ 2 - y ^ 2) -
        2 * (-2 * (x * v₁ + y * v₂)) * ((-2 * (α * v₁ + β * v₂)) * (1 - x ^ 2 - y ^ 2) -
          (α ^ 2 + β ^ 2) * (-2 * (x * v₁ + y * v₂)))) / (A * (1 - x ^ 2 - y ^ 2) ^ 3)) 0 := by
  set N : ℝ → ℝ := fun t => (α - t * v₁) ^ 2 + (β - t * v₂) ^ 2 with hN
  set B : ℝ → ℝ := fun t => 1 - (x + t * v₁) ^ 2 - (y + t * v₂) ^ 2 with hBdef
  set N' : ℝ → ℝ := fun t => -2 * v₁ * (α - t * v₁) - 2 * v₂ * (β - t * v₂) with hN'
  set B' : ℝ → ℝ := fun t => -2 * v₁ * (x + t * v₁) - 2 * v₂ * (y + t * v₂) with hB'
  have dN : ∀ t, HasDerivAt N (N' t) t := fun t => by
    have h := (((hasDerivAt_id t).mul_const v₁).const_sub α).pow 2 |>.add
      ((((hasDerivAt_id t).mul_const v₂).const_sub β).pow 2)
    convert h using 1
    · funext s
      simp only [hN, id, Pi.add_apply, Pi.pow_apply]
    · simp only [hN', id]
      norm_num
      try ring
  have dB : ∀ t, HasDerivAt B (B' t) t := fun t => by
    have h := ((((hasDerivAt_id t).mul_const v₁).const_add x).pow 2).const_sub 1 |>.sub
      ((((hasDerivAt_id t).mul_const v₂).const_add y).pow 2)
    convert h using 1
    · funext s
      simp only [hBdef, id, Pi.sub_apply, Pi.pow_apply]
    · simp only [hB', id]
      norm_num
      try ring
  have dN' : HasDerivAt N' (2 * (v₁ ^ 2 + v₂ ^ 2)) 0 := by
    have h := ((((hasDerivAt_id (0 : ℝ)).mul_const v₁).const_sub α).const_mul (-2 * v₁)).sub
      ((((hasDerivAt_id (0 : ℝ)).mul_const v₂).const_sub β).const_mul (2 * v₂))
    convert h using 1
    · funext t
      simp only [hN', id, Pi.sub_apply]
    · ring
  have dB' : HasDerivAt B' (-2 * (v₁ ^ 2 + v₂ ^ 2)) 0 := by
    have h := ((((hasDerivAt_id (0 : ℝ)).mul_const v₁).const_add x).const_mul (-2 * v₁)).sub
      ((((hasDerivAt_id (0 : ℝ)).mul_const v₂).const_add y).const_mul (2 * v₂))
    convert h using 1
    · funext t
      simp only [hB', id, Pi.sub_apply]
    · ring
  have hB0 : B 0 = 1 - x ^ 2 - y ^ 2 := by simp [hBdef]
  have hBc : ContinuousAt B 0 := (dB 0).continuousAt
  have hBev : ∀ᶠ t in 𝓝 (0 : ℝ), B t ≠ 0 :=
    hBc.eventually_ne (by rw [hB0]; exact hB)
  refine ⟨fun t => 2 * (N' t * B t - N t * B' t) / (A * B t ^ 2), ?_, ?_, ?_⟩
  · filter_upwards [hBev] with t ht
    have h := ((dN t).const_mul 2).div ((dB t).const_mul A) (mul_ne_zero hA ht)
    have h' := h.const_add 1
    convert h' using 1
    field_simp
  · norm_num [hN, hBdef, hN', hB']
    try ring
  · have hB0' : B 0 ≠ 0 := by rw [hB0]; exact hB
    have h := ((((dN'.mul (dB 0)).sub ((dN 0).mul dB')).const_mul 2).div
      (((dB 0).pow 2).const_mul A) (mul_ne_zero hA (pow_ne_zero 2 hB0')))
    refine h.congr_deriv ?_
    simp only [hN, hBdef, hN', hB', zero_mul, add_zero, sub_zero]
    norm_num
    rw [div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero hA (pow_ne_zero 2 hB)))
      (mul_ne_zero hA (pow_ne_zero 3 hB))]
    ring

theorem s10_diskCoshDist_line (p z v : ℂ) (t : ℝ) :
    diskCoshDist p (z + t • v) = 1 + 2 * ((p.re - z.re - t * v.re) ^ 2 +
      (p.im - z.im - t * v.im) ^ 2) / ((1 - ‖p‖ ^ 2) *
        (1 - (z.re + t * v.re) ^ 2 - (z.im + t * v.im) ^ 2)) := by
  unfold diskCoshDist
  simp only [Complex.sq_norm]
  simp only [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
  simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

/-- The second derivative of `t ↦ F(cosh d(p, z + t v))` at `0`, in coordinates. -/
theorem s10_line_second_deriv {F : ℝ → ℝ} (hF : ContDiffOn ℝ 2 F (Ioi 1)) {p z : ℂ}
    (hp : ‖p‖ < 1) (hz : ‖z‖ < 1) (hX : 1 < diskCoshDist p z) (v : ℂ) :
    deriv (deriv fun t : ℝ => F (diskCoshDist p (z + t • v))) 0 =
      deriv (deriv F) (diskCoshDist p z) * (2 * ((-2 * ((p.re - z.re) * v.re + (p.im - z.im) * v.im)) * (1 - z.re ^ 2 - z.im ^ 2) -
        ((p.re - z.re) ^ 2 + (p.im - z.im) ^ 2) * (-2 * (z.re * v.re + z.im * v.im))) / ((1 - ‖p‖ ^ 2) * (1 - z.re ^ 2 - z.im ^ 2) ^ 2)) ^ 2 +
        deriv F (diskCoshDist p z) * (2 * (((2 * (v.re ^ 2 + v.im ^ 2)) * (1 - z.re ^ 2 - z.im ^ 2) -
          ((p.re - z.re) ^ 2 + (p.im - z.im) ^ 2) * (-2 * (v.re ^ 2 + v.im ^ 2))) * (1 - z.re ^ 2 - z.im ^ 2) -
        2 * (-2 * (z.re * v.re + z.im * v.im)) * ((-2 * ((p.re - z.re) * v.re + (p.im - z.im) * v.im)) * (1 - z.re ^ 2 - z.im ^ 2) -
          ((p.re - z.re) ^ 2 + (p.im - z.im) ^ 2) * (-2 * (z.re * v.re + z.im * v.im)))) / ((1 - ‖p‖ ^ 2) * (1 - z.re ^ 2 - z.im ^ 2) ^ 3)) := by
  have hA : 1 - ‖p‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg p]
  have hz2 : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hB : 1 - z.re ^ 2 - z.im ^ 2 ≠ 0 := by nlinarith [norm_nonneg z]
  obtain ⟨q', hq, h0, h2⟩ := s10_quad_ratio_deriv (p.re - z.re) (p.im - z.im) z.re z.im v.re v.im
    (1 - ‖p‖ ^ 2) hA hB
  have hq0 := s10_diskCoshDist_line p z v 0
  rw [zero_smul, add_zero] at hq0
  have hfun : (fun t : ℝ => F (diskCoshDist p (z + t • v))) = fun t => F (1 + 2 * ((p.re - z.re -
      t * v.re) ^ 2 + (p.im - z.im - t * v.im) ^ 2) / ((1 - ‖p‖ ^ 2) *
        (1 - (z.re + t * v.re) ^ 2 - (z.im + t * v.im) ^ 2))) :=
    funext fun t => by rw [s10_diskCoshDist_line]
  have hc := s10_deriv_deriv_comp hF (by rw [← hq0]; exact hX) hq h2
  beta_reduce at hc
  rw [h0, ← hq0] at hc
  rw [hfun, hc]

/-- The algebraic identity behind Lemma 10.6 (b): `(B/2)² Σ_v (F'' q_v'² + F' q_v'') =
(X² - 1) F'' + 2X F'` with `X = cosh d(p, z)`, `B = 1 - |z|²`. -/
theorem s10_disk_lap_alg (p z : ℂ) (F1 F2 : ℝ) (hA : 1 - ‖p‖ ^ 2 ≠ 0)
    (hB : 1 - z.re ^ 2 - z.im ^ 2 ≠ 0) :
    ((1 - ‖z‖ ^ 2) / 2) ^ 2 * ((F2 * (2 * ((-2 * ((p.re - z.re) * (1 : ℂ).re + (p.im - z.im) * (1 : ℂ).im)) * (1 - z.re ^ 2 - z.im ^ 2) -
        ((p.re - z.re) ^ 2 + (p.im - z.im) ^ 2) * (-2 * (z.re * (1 : ℂ).re + z.im * (1 : ℂ).im))) / ((1 - ‖p‖ ^ 2) * (1 - z.re ^ 2 - z.im ^ 2) ^ 2)) ^ 2 + F1 * (2 * (((2 * ((1 : ℂ).re ^ 2 + (1 : ℂ).im ^ 2)) * (1 - z.re ^ 2 - z.im ^ 2) -
          ((p.re - z.re) ^ 2 + (p.im - z.im) ^ 2) * (-2 * ((1 : ℂ).re ^ 2 + (1 : ℂ).im ^ 2))) * (1 - z.re ^ 2 - z.im ^ 2) -
        2 * (-2 * (z.re * (1 : ℂ).re + z.im * (1 : ℂ).im)) * ((-2 * ((p.re - z.re) * (1 : ℂ).re + (p.im - z.im) * (1 : ℂ).im)) * (1 - z.re ^ 2 - z.im ^ 2) -
          ((p.re - z.re) ^ 2 + (p.im - z.im) ^ 2) * (-2 * (z.re * (1 : ℂ).re + z.im * (1 : ℂ).im)))) / ((1 - ‖p‖ ^ 2) * (1 - z.re ^ 2 - z.im ^ 2) ^ 3))) +
      (F2 * (2 * ((-2 * ((p.re - z.re) * (I : ℂ).re + (p.im - z.im) * (I : ℂ).im)) * (1 - z.re ^ 2 - z.im ^ 2) -
        ((p.re - z.re) ^ 2 + (p.im - z.im) ^ 2) * (-2 * (z.re * (I : ℂ).re + z.im * (I : ℂ).im))) / ((1 - ‖p‖ ^ 2) * (1 - z.re ^ 2 - z.im ^ 2) ^ 2)) ^ 2 + F1 * (2 * (((2 * ((I : ℂ).re ^ 2 + (I : ℂ).im ^ 2)) * (1 - z.re ^ 2 - z.im ^ 2) -
          ((p.re - z.re) ^ 2 + (p.im - z.im) ^ 2) * (-2 * ((I : ℂ).re ^ 2 + (I : ℂ).im ^ 2))) * (1 - z.re ^ 2 - z.im ^ 2) -
        2 * (-2 * (z.re * (I : ℂ).re + z.im * (I : ℂ).im)) * ((-2 * ((p.re - z.re) * (I : ℂ).re + (p.im - z.im) * (I : ℂ).im)) * (1 - z.re ^ 2 - z.im ^ 2) -
          ((p.re - z.re) ^ 2 + (p.im - z.im) ^ 2) * (-2 * (z.re * (I : ℂ).re + z.im * (I : ℂ).im)))) / ((1 - ‖p‖ ^ 2) * (1 - z.re ^ 2 - z.im ^ 2) ^ 3)))) =
      (diskCoshDist p z ^ 2 - 1) * F2 + 2 * diskCoshDist p z * F1 := by
  have hz2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hp2 : ‖p‖ ^ 2 = p.re ^ 2 + p.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hXe : diskCoshDist p z = 1 + 2 * ((p.re - z.re) ^ 2 + (p.im - z.im) ^ 2) /
      ((1 - ‖p‖ ^ 2) * (1 - z.re ^ 2 - z.im ^ 2)) := by
    show 1 + 2 * ‖p - z‖ ^ 2 / ((1 - ‖p‖ ^ 2) * (1 - ‖z‖ ^ 2)) = _
    rw [Complex.sq_norm (p - z), Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hz2]
    ring
  rw [hXe, hz2]
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  rw [hp2] at hA ⊢
  generalize p.re = pr at hA ⊢
  generalize p.im = pi at hA ⊢
  generalize z.re = x at hB ⊢
  generalize z.im = y at hB ⊢
  set N := (pr - x) ^ 2 + (pi - y) ^ 2 with hN
  set A := 1 - (pr ^ 2 + pi ^ 2) with hAd
  set B := 1 - x ^ 2 - y ^ 2 with hBd
  have k1 : ((1 - (x ^ 2 + y ^ 2)) / 2) ^ 2 * ((4 * (x * N - (pr - x) * B) / (A * B ^ 2)) ^ 2 +
      (4 * (y * N - (pi - y) * B) / (A * B ^ 2)) ^ 2) = (1 + 2 * N / (A * B)) ^ 2 - 1 := by
    field_simp
    simp only [hAd, hBd, hN]
    ring
  have k2 : ((1 - (x ^ 2 + y ^ 2)) / 2) ^ 2 * ((8 * (B + N) * B +
      16 * (N * (x ^ 2 + y ^ 2) - (x * (pr - x) + y * (pi - y)) * B)) / (A * B ^ 3)) =
      2 * (1 + 2 * N / (A * B)) := by
    field_simp
    simp only [hAd, hBd, hN]
    ring
  linear_combination F2 * k1 + F1 * k2

/-- Proof of `lem_plane_green_b`. -/
theorem s10_lem_plane_green_b (F : ℝ → ℝ) (hF : ContDiffOn ℝ 2 F (Ioi 1)) (p : ℂ)
    (hp : p ∈ unitDisc) (z : ℂ) (hz : z ∈ unitDisc) (hzp : z ≠ p) :
    hypLaplacianDisk (fun z => F (diskCoshDist p z)) z =
      (diskCoshDist p z ^ 2 - 1) * deriv (deriv F) (diskCoshDist p z) +
        2 * diskCoshDist p z * deriv F (diskCoshDist p z) := by
  have hp' : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hA : 0 < 1 - ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
  have hB : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hpz : 0 < ‖p - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hzp))
  have hX : 1 < diskCoshDist p z := by
    show 1 < 1 + 2 * ‖p - z‖ ^ 2 / ((1 - ‖p‖ ^ 2) * (1 - ‖z‖ ^ 2))
    have : 0 < 2 * ‖p - z‖ ^ 2 / ((1 - ‖p‖ ^ 2) * (1 - ‖z‖ ^ 2)) := by positivity
    linarith
  have hh : ContDiffAt ℝ 2 (diskCoshDist p) z := by
    have h1 : ContDiffAt ℝ 2 (fun w : ℂ => ‖p - w‖ ^ 2) z :=
      (contDiff_norm_sq ℝ).contDiffAt.comp z (contDiffAt_const.sub contDiffAt_id)
    have h2 : ContDiffAt ℝ 2 (fun w : ℂ => ‖w‖ ^ 2) z := (contDiff_norm_sq ℝ).contDiffAt
    exact contDiffAt_const.add ((contDiffAt_const.mul h1).div
      (contDiffAt_const.mul (contDiffAt_const.sub h2)) (by positivity))
  have hfC : ContDiffAt ℝ 2 (fun z => F (diskCoshDist p z)) z :=
    (hF.contDiffAt (Ioi_mem_nhds hX)).comp z hh
  show ((1 - ‖z‖ ^ 2) / 2) ^ 2 * Laplacian.laplacian (fun z => F (diskCoshDist p z)) z = _
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  beta_reduce
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [s10_fderiv_fderiv_line hfC 1, s10_fderiv_fderiv_line hfC I,
    s10_line_second_deriv hF hp' hz' hX 1, s10_line_second_deriv hF hp' hz' hX I]
  have hB' : 1 - z.re ^ 2 - z.im ^ 2 ≠ 0 := by
    have : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    linarith
  exact s10_disk_lap_alg p z _ _ hA.ne' hB'

/-- `Δ_ρ` at `z` only depends on the germ of `φ` at `z`. -/
theorem s10_hypLaplacianDisk_congr {φ ψ : ℂ → ℝ} {z : ℂ} (h : φ =ᶠ[𝓝 z] ψ) :
    hypLaplacianDisk φ z = hypLaplacianDisk ψ z := by
  show ((1 - ‖z‖ ^ 2) / 2) ^ 2 * Laplacian.laplacian φ z =
    ((1 - ‖z‖ ^ 2) / 2) ^ 2 * Laplacian.laplacian ψ z
  rw [(InnerProductSpace.laplacian_congr_nhds h).eq_of_nhds]

/-- On `𝔻 × 𝔻`, `diskCoshDist ≥ 1`. -/
theorem s10_one_le_diskCoshDist {p w : ℂ} (hp : p ∈ unitDisc) (hw : w ∈ unitDisc) :
    1 ≤ diskCoshDist p w := by
  have hp' : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
  have hw' : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hA : 0 < 1 - ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
  have hB : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  show 1 ≤ 1 + 2 * ‖p - w‖ ^ 2 / ((1 - ‖p‖ ^ 2) * (1 - ‖w‖ ^ 2))
  have : 0 ≤ 2 * ‖p - w‖ ^ 2 / ((1 - ‖p‖ ^ 2) * (1 - ‖w‖ ^ 2)) := by positivity
  linarith

/-- On `𝔻`, `cosh d(p, ·) = diskCoshDist p` near any point of `𝔻`. -/
theorem s10_cosh_diskDist_eventually {p z : ℂ} (hp : p ∈ unitDisc) (hz : z ∈ unitDisc) :
    (fun w => Real.cosh (diskDist p w)) =ᶠ[𝓝 z] fun w => diskCoshDist p w := by
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact Real.cosh_arcosh (s10_one_le_diskCoshDist hp hw)

/-- `Q₁` is `C²` on `(1, ∞)`. -/
theorem s10_legendreQ1_contDiffOn : ContDiffOn ℝ 2 legendreQ1 (Ioi 1) := by
  have h : ContDiffOn ℝ 2
      (fun x : ℝ => x * (1 / 2 * (Real.log (x + 1) - Real.log (x - 1))) - 1) (Ioi 1) := by
    refine (contDiffOn_id.mul (contDiffOn_const.mul ?_)).sub contDiffOn_const
    refine ((contDiffOn_id.add contDiffOn_const).log ?_).sub
      ((contDiffOn_id.sub contDiffOn_const).log ?_)
    · intro x hx
      have : (1 : ℝ) < x := hx
      simp only [id]
      linarith
    · intro x hx
      have : (1 : ℝ) < x := hx
      simp only [id]
      linarith
  refine h.congr ?_
  intro x hx
  show x * Real.artanh (1 / x) - 1 = _
  rw [s10_artanh_inv hx]

/-- Proof of `lem_plane_green_b'`. -/
theorem s10_lem_plane_green_b' (p : ℂ) (hp : p ∈ unitDisc) (z : ℂ) (hz : z ∈ unitDisc)
    (hzp : z ≠ p) :
    2 * resolventG (diskDist p z) - hypLaplacianDisk (fun z => resolventG (diskDist p z)) z = 0 ∧
      2 * Real.cosh (diskDist p z) -
        hypLaplacianDisk (fun z => Real.cosh (diskDist p z)) z = 0 := by
  have hX1 : 1 ≤ diskCoshDist p z := s10_one_le_diskCoshDist hp hz
  have hc : Real.cosh (diskDist p z) = diskCoshDist p z := Real.cosh_arcosh hX1
  have hp' : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hA : 0 < 1 - ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
  have hB : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hpz : 0 < ‖p - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hzp))
  have hX : 1 < diskCoshDist p z := by
    show 1 < 1 + 2 * ‖p - z‖ ^ 2 / ((1 - ‖p‖ ^ 2) * (1 - ‖z‖ ^ 2))
    have : 0 < 2 * ‖p - z‖ ^ 2 / ((1 - ‖p‖ ^ 2) * (1 - ‖z‖ ^ 2)) := by positivity
    linarith
  have hev := s10_cosh_diskDist_eventually hp hz
  constructor
  · have hev' : (fun w => resolventG (diskDist p w)) =ᶠ[𝓝 z]
        fun w => (fun x => legendreQ1 x / (2 * π)) (diskCoshDist p w) := by
      filter_upwards [hev] with w hw
      show legendreQ1 (Real.cosh (diskDist p w)) / (2 * π) = _
      rw [hw]
    have hF : ContDiffOn ℝ 2 (fun x => legendreQ1 x / (2 * π)) (Ioi 1) :=
      s10_legendreQ1_contDiffOn.div_const _
    rw [s10_hypLaplacianDisk_congr hev', s10_lem_plane_green_b _ hF p hp z hz hzp]
    have hd : deriv (fun x => legendreQ1 x / (2 * π)) = fun x => deriv legendreQ1 x / (2 * π) := by
      funext x
      exact deriv_div_const _
    rw [hd, deriv_div_const]
    have hL := (s10_lem_plane_green_a _ hX).2.2.2.2
    show 2 * (legendreQ1 (Real.cosh (diskDist p z)) / (2 * π)) - _ = 0
    rw [hc]
    have hπ : (2 * π) ≠ 0 := by positivity
    field_simp
    linear_combination hL
  · have hb : hypLaplacianDisk (fun w => diskCoshDist p w) z =
        (diskCoshDist p z ^ 2 - 1) * deriv (deriv id) (diskCoshDist p z) +
          2 * diskCoshDist p z * deriv id (diskCoshDist p z) :=
      s10_lem_plane_green_b id contDiffOn_id p hp z hz hzp
    rw [s10_hypLaplacianDisk_congr hev, hb]
    have h1 : deriv (id : ℝ → ℝ) = fun _ => 1 := funext deriv_id
    rw [hc, h1, deriv_const]
    ring

/-- **Lemma 10.6 (b)**, `lem:plane-green`, `sec10-sharp.tex:141`: for `F ∈ C²((1,∞))` and
`φ = F(cosh d(p, ·))`, `Δφ = ((x²-1)F''(x) + 2xF'(x))|_{x = cosh d(p,·)}` off `p`. -/
theorem lem_plane_green_b (F : ℝ → ℝ) (hF : ContDiffOn ℝ 2 F (Ioi 1)) (p : ℂ) (hp : p ∈ unitDisc)
    (z : ℂ) (hz : z ∈ unitDisc) (hzp : z ≠ p) :
    hypLaplacianDisk (fun z => F (diskCoshDist p z)) z =
      (diskCoshDist p z ^ 2 - 1) * deriv (deriv F) (diskCoshDist p z) +
        2 * diskCoshDist p z * deriv F (diskCoshDist p z) := by
  exact s10_lem_plane_green_b F hF p hp z hz hzp

/-- **Lemma 10.6 (b)**, `lem:plane-green`, `sec10-sharp.tex:144`: `(2 - Δ) 𝔊(r) = 0` and
`(2 - Δ) cosh r = 0` on `S ∖ {p}`, `r = d(p, ·)`. -/
theorem lem_plane_green_b' (p : ℂ) (hp : p ∈ unitDisc) (z : ℂ) (hz : z ∈ unitDisc) (hzp : z ≠ p) :
    2 * resolventG (diskDist p z) - hypLaplacianDisk (fun z => resolventG (diskDist p z)) z = 0 ∧
      2 * Real.cosh (diskDist p z) -
        hypLaplacianDisk (fun z => Real.cosh (diskDist p z)) z = 0 := by
  exact s10_lem_plane_green_b' p hp z hz hzp

/-- **Lemma 10.6 (c)**, `lem:plane-green`, `sec10-sharp.tex:146`: as `r ↓ 0`,
`2π𝔊(r) = -log r + log 2 - 1 + o(1)`; `2π sinh r 𝔊'(r) = sinh² r artanh(sech r) - cosh r → -1`. -/
theorem lem_plane_green_c :
    Tendsto (fun r => 2 * π * resolventG r + Real.log r) (𝓝[>] 0) (𝓝 (Real.log 2 - 1)) ∧
      (∀ r : ℝ, 0 < r → 2 * π * Real.sinh r * deriv resolventG r =
        Real.sinh r ^ 2 * Real.artanh ((Real.cosh r)⁻¹) - Real.cosh r) ∧
      Tendsto (fun r => 2 * π * Real.sinh r * deriv resolventG r) (𝓝[>] 0) (𝓝 (-1)) := by
  exact s10_lem_plane_green_c

/-- **Lemma 10.6 (d)**, `lem:plane-green`, `sec10-sharp.tex:150`:
`-sech r ≤ 2π sinh r 𝔊'(r) ≤ -(2/3) sech r`. -/
theorem lem_plane_green_d (r : ℝ) (hr : 0 < r) :
    -(Real.cosh r)⁻¹ ≤ 2 * π * Real.sinh r * deriv resolventG r ∧
      2 * π * Real.sinh r * deriv resolventG r ≤ -(2 / 3 * (Real.cosh r)⁻¹) := by
  exact s10_lem_plane_green_d r hr

/-- **Lemma 10.6 (e)**, `lem:plane-green`, `sec10-sharp.tex:151`: `Q₁(x) ≤ 1/(3(x²-1))`, and
`𝔊(r)/cosh r` is strictly decreasing on `(0, ∞)`. -/
theorem lem_plane_green_e :
    (∀ x : ℝ, 1 < x → legendreQ1 x ≤ 1 / (3 * (x ^ 2 - 1))) ∧
      StrictAntiOn (fun r => resolventG r / Real.cosh r) (Ioi 0) := by
  exact s10_lem_plane_green_e

theorem s10_tendsto_cosh_atTop : Tendsto Real.cosh atTop atTop := by
  refine tendsto_atTop_mono (fun x => ?_)
    (Real.tendsto_exp_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  rw [Real.cosh_eq]
  have := Real.exp_pos (-x)
  linarith

theorem s10_resolventG_pos {r : ℝ} (hr : 0 < r) : 0 < resolventG r := by
  have hc : 1 < Real.cosh r := Real.one_lt_cosh.mpr hr.ne'
  have := (s10_lem_plane_green_a _ hc).1
  show 0 < legendreQ1 (Real.cosh r) / (2 * π)
  positivity

/-- A primitive of `𝔊(r) 2π sinh r` on `(0, ∞)`: `((cosh² r - 1) artanh(sech r) - cosh r)/2`. -/
theorem s10_hasDerivAt_prim_sinh {r : ℝ} (hr : 0 < r) :
    HasDerivAt
      (fun r => ((Real.cosh r ^ 2 - 1) * Real.artanh (1 / Real.cosh r) - Real.cosh r) / 2)
      (resolventG r * (2 * π * Real.sinh r)) r := by
  have hc : 1 < Real.cosh r := Real.one_lt_cosh.mpr hr.ne'
  have hF : HasDerivAt (fun x => ((x ^ 2 - 1) * Real.artanh (1 / x) - x) / 2)
      (legendreQ1 (Real.cosh r)) (Real.cosh r) := by
    have h := ((((hasDerivAt_pow 2 (Real.cosh r)).sub_const 1).mul
      (s10_hasDerivAt_artanh_inv hc)).sub (hasDerivAt_id _)).div_const 2
    refine h.congr_deriv ?_
    have hne : Real.cosh r ^ 2 - 1 ≠ 0 := by nlinarith
    show _ = Real.cosh r * Real.artanh (1 / Real.cosh r) - 1
    field_simp
    ring
  have h := hF.comp r (Real.hasDerivAt_cosh r)
  refine h.congr_deriv ?_
  show legendreQ1 (Real.cosh r) * Real.sinh r =
    legendreQ1 (Real.cosh r) / (2 * π) * (2 * π * Real.sinh r)
  field_simp

/-- A primitive of `Q₁(x)/x` on `(1, ∞)`: `((x+1)log(x+1) - (x-1)log(x-1))/2 - log x`. -/
theorem s10_hasDerivAt_prim_tanh_x {x : ℝ} (hx : 1 < x) :
    HasDerivAt
      (fun x => ((x + 1) * Real.log (x + 1) - (x - 1) * Real.log (x - 1)) / 2 - Real.log x)
      (legendreQ1 x / x) x := by
  have hx0 : x ≠ 0 := by positivity
  have h1 : x + 1 ≠ 0 := by linarith
  have h2 : x - 1 ≠ 0 := by linarith
  have hp := ((hasDerivAt_id x).add_const 1).mul (((hasDerivAt_id x).add_const 1).log h1)
  have hm := ((hasDerivAt_id x).sub_const 1).mul (((hasDerivAt_id x).sub_const 1).log h2)
  have h := ((hp.sub hm).div_const 2).sub ((hasDerivAt_id x).log hx0)
  refine h.congr_deriv ?_
  show _ = (x * Real.artanh (1 / x) - 1) / x
  rw [s10_artanh_inv hx]
  simp only [id]
  field_simp
  ring

theorem s10_hasDerivAt_prim_tanh {r : ℝ} (hr : 0 < r) :
    HasDerivAt
      (fun r => ((Real.cosh r + 1) * Real.log (Real.cosh r + 1) -
        (Real.cosh r - 1) * Real.log (Real.cosh r - 1)) / 2 - Real.log (Real.cosh r))
      (resolventG r * (2 * π * Real.tanh r)) r := by
  have hc : 1 < Real.cosh r := Real.one_lt_cosh.mpr hr.ne'
  have h := (s10_hasDerivAt_prim_tanh_x hc).comp r (Real.hasDerivAt_cosh r)
  refine h.congr_deriv ?_
  have hc0 : Real.cosh r ≠ 0 := (Real.cosh_pos r).ne'
  show legendreQ1 (Real.cosh r) / Real.cosh r * Real.sinh r =
    legendreQ1 (Real.cosh r) / (2 * π) * (2 * π * Real.tanh r)
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

theorem s10_continuous_prim_tanh :
    Continuous (fun r => ((Real.cosh r + 1) * Real.log (Real.cosh r + 1) -
      (Real.cosh r - 1) * Real.log (Real.cosh r - 1)) / 2 - Real.log (Real.cosh r)) :=
  (((Real.continuous_mul_log.comp (Real.continuous_cosh.add continuous_const)).sub
    (Real.continuous_mul_log.comp (Real.continuous_cosh.sub continuous_const))).div_const 2).sub
    (Real.continuous_cosh.log fun r => (Real.cosh_pos r).ne')

theorem s10_tendsto_prim_tanh_x :
    Tendsto (fun x => ((x + 1) * Real.log (x + 1) - (x - 1) * Real.log (x - 1)) / 2 -
      Real.log x) atTop (𝓝 1) := by
  have hsq : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have hinv : Tendsto (fun x : ℝ => (x ^ 2)⁻¹) atTop (𝓝 0) := hsq.inv_tendsto_atTop
  have hlog : Tendsto (fun x : ℝ => Real.log (1 - (x ^ 2)⁻¹)) atTop (𝓝 0) := by
    have := ((Real.continuousAt_log (by norm_num : (1 : ℝ) - 0 ≠ 0)).tendsto).comp
      (hinv.const_sub 1)
    rw [sub_zero, Real.log_one] at this
    exact this
  have hden : Tendsto (fun x : ℝ => 3 * (x ^ 2 - 1)) atTop atTop :=
    (tendsto_atTop_add_const_right _ (-1) hsq).const_mul_atTop (by norm_num : (0 : ℝ) < 3)
      |>.congr fun x => by ring
  have hup : Tendsto (fun x : ℝ => 1 / (3 * (x ^ 2 - 1))) atTop (𝓝 0) := by
    have := hden.inv_tendsto_atTop
    simp only [one_div]
    exact this
  have hQ : Tendsto legendreQ1 atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 1] with x hx
      exact (s10_lem_plane_green_a x hx).1.le
    · filter_upwards [eventually_gt_atTop 1] with x hx
      exact s10_lem_plane_green_e.1 x hx
  have hlim := (hQ.add_const 1).add (hlog.div_const 2)
  rw [zero_add, zero_div, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hx0 : 0 < x := by linarith
  have h1 : 0 < x + 1 := by linarith
  have h2 : 0 < x - 1 := by linarith
  have hq : legendreQ1 x = x * (1 / 2 * (Real.log (x + 1) - Real.log (x - 1))) - 1 := by
    rw [← s10_artanh_inv hx]
    rfl
  have hl : Real.log (1 - (x ^ 2)⁻¹) = Real.log (x + 1) + Real.log (x - 1) - 2 * Real.log x := by
    have e : 1 - (x ^ 2)⁻¹ = (x + 1) * (x - 1) / x ^ 2 := by
      field_simp
      ring
    rw [e, Real.log_div (by positivity) (by positivity), Real.log_mul h1.ne' h2.ne',
      Real.log_pow]
    push_cast
    ring
  rw [hq, hl]
  ring

theorem s10_lem_plane_green_f :
    IntegrableOn (fun r => resolventG r * (2 * π * Real.sinh r)) (Ioi 0) ∧
      ∫ r in Ioi (0 : ℝ), resolventG r * (2 * π * Real.sinh r) = 1 / 2 ∧
      IntegrableOn (fun r => resolventG r * (2 * π * Real.tanh r)) (Ioi 0) ∧
      ∫ r in Ioi (0 : ℝ), resolventG r * (2 * π * Real.tanh r) = 1 - Real.log 2 ∧
      AntitoneOn resolventTail (Ioi 0) ∧ Tendsto resolventTail atTop (𝓝 0) := by
  set g : ℝ → ℝ := fun r =>
    ((Real.cosh r ^ 2 - 1) * Real.artanh (1 / Real.cosh r) - Real.cosh r) / 2 with hg_def
  set k : ℝ → ℝ := fun r => ((Real.cosh r + 1) * Real.log (Real.cosh r + 1) -
    (Real.cosh r - 1) * Real.log (Real.cosh r - 1)) / 2 - Real.log (Real.cosh r) with hk_def
  -- `2 g = 2π sinh r 𝔊'(r)` for `r > 0`
  have hg2 : ∀ r : ℝ, 0 < r → g r = 2 * π * Real.sinh r * deriv resolventG r / 2 := by
    intro r hr
    rw [s10_two_pi_sinh_deriv hr, Real.sinh_sq, ← one_div]
  have hg0 : g 0 = -1 / 2 := by simp [hg_def]
  have hgcont : ContinuousWithinAt g (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, hg0]
    have h3 := s10_lem_plane_green_c.2.2.div_const 2
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    exact (hg2 r hr).symm
  have hglim : Tendsto g atTop (𝓝 0) := by
    have hlow : Tendsto (fun r => -(Real.cosh r)⁻¹ / 2) atTop (𝓝 0) := by
      have := (s10_tendsto_cosh_atTop.inv_tendsto_atTop.neg).div_const 2
      rwa [neg_zero, zero_div] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with r hr
      rw [hg2 r hr]
      linarith [(s10_lem_plane_green_d r hr).1]
    · filter_upwards [eventually_gt_atTop 0] with r hr
      rw [hg2 r hr]
      have := (s10_lem_plane_green_d r hr).2
      have : 0 ≤ (Real.cosh r)⁻¹ := by positivity
      linarith
  have hpos1 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ resolventG r * (2 * π * Real.sinh r) := by
    intro r (hr : 0 < r)
    have := s10_resolventG_pos hr
    have := Real.sinh_pos_iff.mpr hr
    positivity
  have hpos2 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ resolventG r * (2 * π * Real.tanh r) := by
    intro r (hr : 0 < r)
    have := s10_resolventG_pos hr
    have := Real.sinh_pos_iff.mpr hr
    have := Real.cosh_pos r
    rw [Real.tanh_eq_sinh_div_cosh]
    positivity
  have hd1 : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt g (resolventG r * (2 * π * Real.sinh r)) r :=
    fun r hr => s10_hasDerivAt_prim_sinh hr
  have hd2 : ∀ a : ℝ, 0 ≤ a → ∀ r ∈ Ioi a, HasDerivAt k (resolventG r * (2 * π * Real.tanh r)) r :=
    fun a ha r (hr : a < r) => s10_hasDerivAt_prim_tanh (by linarith)
  have hklim : Tendsto k atTop (𝓝 1) := s10_tendsto_prim_tanh_x.comp s10_tendsto_cosh_atTop
  have hkcont : ∀ a : ℝ, ContinuousWithinAt k (Ici a) a :=
    fun a => s10_continuous_prim_tanh.continuousWithinAt
  have hk0 : k 0 = Real.log 2 := by
    simp only [hk_def, Real.cosh_zero, sub_self, zero_mul, sub_zero, Real.log_one]
    norm_num
  have htail : ∀ a : ℝ, 0 ≤ a → resolventTail a = 1 - k a := fun a ha =>
    integral_Ioi_of_hasDerivAt_of_nonneg (hkcont a) (hd2 a ha)
      (fun r (hr : a < r) => hpos2 r (show (0 : ℝ) < r by linarith)) hklim
  have hint2 : IntegrableOn (fun r => resolventG r * (2 * π * Real.tanh r)) (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg (hkcont 0) (hd2 0 le_rfl) hpos2 hklim
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hgcont hd1 hpos1 hglim, ?_, hint2, ?_, ?_, ?_⟩
  · rw [integral_Ioi_of_hasDerivAt_of_nonneg hgcont hd1 hpos1 hglim, hg0]
    norm_num
  · have := htail 0 le_rfl
    rw [hk0] at this
    exact this
  · intro a (ha : 0 < a) b (hb : 0 < b) hab
    refine setIntegral_mono_set (hint2.mono_set (Ioi_subset_Ioi ha.le)) ?_
      (Ioi_subset_Ioi hab).eventuallyLE
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r (hr : a < r)
    exact hpos2 r (show (0 : ℝ) < r by linarith)
  · have := hklim.const_sub 1
    rw [sub_self] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with a ha
    exact (htail a ha).symm

/-- **Lemma 10.6 (f)**, `lem:plane-green`, `sec10-sharp.tex:153`:
`∫₀^∞ 𝔊(r) 2π sinh r dr = 1/2`, `∫₀^∞ 𝔊(r) 2π tanh r dr = 1 - log 2`, and `ϑ(Λ) ↓ 0`. -/
theorem lem_plane_green_f :
    IntegrableOn (fun r => resolventG r * (2 * π * Real.sinh r)) (Ioi 0) ∧
      ∫ r in Ioi (0 : ℝ), resolventG r * (2 * π * Real.sinh r) = 1 / 2 ∧
      IntegrableOn (fun r => resolventG r * (2 * π * Real.tanh r)) (Ioi 0) ∧
      ∫ r in Ioi (0 : ℝ), resolventG r * (2 * π * Real.tanh r) = 1 - Real.log 2 ∧
      AntitoneOn resolventTail (Ioi 0) ∧ Tendsto resolventTail atTop (𝓝 0) := by
  exact s10_lem_plane_green_f

/-- `thm:plane-ratio` helper: the disk automorphism `diskMob a` maps `𝔻` to itself and preserves
`cosh d_𝔻`. -/
theorem s10_pr_mob {a : ℂ} (ha : a ∈ unitDisc) :
    MapsTo (diskMob a) unitDisc unitDisc ∧ ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      diskCoshDist (diskMob a z) (diskMob a w) = diskCoshDist z w := by
  have ha' : ‖-a‖ < 1 := by rw [norm_neg]; exact mem_ball_zero_iff.mp ha
  have he : ∀ z, diskMob a z = blaschke (-a) z := fun z => by
    show (z + a) / (1 + conj a * z) = (z - -a) / (1 - conj (-a) * z)
    rw [map_neg, sub_neg_eq_add, neg_mul, sub_neg_eq_add]
  refine ⟨fun z hz => ?_, fun z hz w hw => ?_⟩
  · rw [he]
    exact mem_ball_zero_iff.mpr (blaschke_mem_unitDisc ha' (mem_ball_zero_iff.mp hz))
  · rw [he, he]
    exact s02_diskCoshDist_blaschke ha' (mem_ball_zero_iff.mp hz) (mem_ball_zero_iff.mp hw)

/-- `thm:plane-ratio` (b) helper: the hyperbolic area of the disk is invariant under the disk
automorphism `diskMob c`. -/
theorem s10_prb_area_mob {c : ℂ} (hc : c ∈ unitDisc) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, g (diskMob c z) ∂diskHypArea = ∫⁻ b, g b ∂diskHypArea := by
  have hc1 : ‖c‖ < 1 := mem_ball_zero_iff.mp hc
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have he : diskMob c = blaschke (-c) := funext fun z => by
    show (z + c) / (1 + conj c * z) = (z - -c) / (1 - conj (-c) * z)
    rw [map_neg, sub_neg_eq_add, neg_mul, sub_neg_eq_add]
  have hfm : Measurable (blaschke (-c)) := by
    rw [s05_blaschke_neg_eq]
    fun_prop
  have hd : Measurable fun z : ℂ => ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2) := by fun_prop
  have hconf := isConformalOnto_blaschke (show ‖-c‖ < 1 by rw [norm_neg]; exact hc1)
  show ∫⁻ z, g (diskMob c z) ∂(volume.restrict unitDisc).withDensity
      (fun z => ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2)) =
    ∫⁻ b, g b ∂(volume.restrict unitDisc).withDensity
      (fun z => ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2))
  have hgf : Measurable fun z => g (blaschke (-c) z) := hg.comp hfm
  rw [he, lintegral_withDensity_eq_lintegral_mul _ hd hgf,
    lintegral_withDensity_eq_lintegral_mul _ hd hg]
  have hder : ∀ x ∈ unitDisc, HasFDerivWithinAt (blaschke (-c))
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv (blaschke (-c)) x)).restrictScalars
        ℝ) unitDisc x := by
    intro x hx
    exact ((hconf.1.differentiableAt (isOpen_ball.mem_nhds hx)).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt
  conv_rhs => rw [← hconf.2.2]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hD hder hconf.2.1]
  refine setLIntegral_congr_fun hD (fun x hx => ?_)
  have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
  have hj := s05_norm_deriv_blaschke_neg hc1 hx1
  have hfx := blaschke_mem_unitDisc (show ‖-c‖ < 1 by rw [norm_neg]; exact hc1) hx1
  have h1x : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  have h1f : 0 < 1 - ‖blaschke (-c) x‖ ^ 2 := by nlinarith [norm_nonneg (blaschke (-c) x)]
  have hdn : 0 < ‖deriv (blaschke (-c)) x‖ := by
    by_contra h0
    have : ‖deriv (blaschke (-c)) x‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
    rw [this, zero_mul] at hj
    linarith
  simp only [Pi.mul_apply]
  rw [s02_pullback_det, abs_of_nonneg (by positivity), ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [← hj]
  field_simp

/-- `thm:plane-ratio` (b) helper: Euclidean polar coordinates on the unit disk,
`∫_𝔻 F dA = ∫₀¹ ρ ∫_{-π}^{π} F(ρ e^{iθ}) dθ dρ` (for a Borel `F ≥ 0`). -/
theorem s10_prb_polar_disk {F : ℂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z in unitDisc, F z = ∫⁻ ρ in Ioo (0 : ℝ) 1, ENNReal.ofReal ρ *
      ∫⁻ θ in Ioo (-π) π, F ((ρ : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
  have hsymm : ∀ p : ℝ × ℝ, Complex.polarCoord.symm p =
      (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I) := fun p => by
    rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
  have hnorm : ∀ x y : ℝ, 0 < x → ‖(x : ℂ) * Complex.exp ((y : ℂ) * I)‖ = x := fun x y hx => by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx]
  have hD : MeasurableSet unitDisc := measurableSet_ball
  rw [← lintegral_indicator hD, ← Complex.lintegral_comp_polarCoord_symm,
    polarCoord_target]
  simp_rw [hsymm, smul_eq_mul]
  rw [Measure.volume_eq_prod, setLIntegral_prod]
  swap
  · refine Measurable.aemeasurable ?_
    refine (ENNReal.measurable_ofReal.comp measurable_fst).mul ?_
    exact (hF.indicator hD).comp (by fun_prop)
  have hI : Ioo (0 : ℝ) 1 = Iio 1 ∩ Ioi 0 := by rw [inter_comm]; rfl
  rw [hI, ← Measure.restrict_restrict measurableSet_Iio, ← lintegral_indicator measurableSet_Iio]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  by_cases hx1 : x < 1
  · rw [indicator_of_mem (show x ∈ Iio 1 from hx1), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun y => ?_)
    rw [indicator_of_mem (show (x : ℂ) * Complex.exp ((y : ℂ) * I) ∈ unitDisc from
      mem_ball_zero_iff.mpr (by rw [hnorm x y hx0]; exact hx1))]
  · rw [indicator_of_notMem (show x ∉ Iio 1 from hx1)]
    refine (lintegral_congr (fun y => ?_)).trans lintegral_zero
    rw [indicator_of_notMem (show (x : ℂ) * Complex.exp ((y : ℂ) * I) ∉ unitDisc from
      fun h => hx1 (by rw [← hnorm x y hx0]; exact mem_ball_zero_iff.mp h)), mul_zero]

/-- `thm:plane-ratio` (b) helper: geodesic polar coordinates about `0` for the hyperbolic area,
`dâ = sinh s ds dθ` with `z = tanh(s/2) e^{iθ}`. -/
theorem s10_prb_polar {ψ : ℂ → ℝ≥0∞} (hψ : Measurable ψ) :
    ∫⁻ z, ψ z ∂diskHypArea = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.sinh s) *
      ∫⁻ θ in Ioo (-π) π, ψ ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
  have hd : Measurable fun z : ℂ => ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2) := by fun_prop
  have hnorm : ∀ x y : ℝ, 0 < x → ‖(x : ℂ) * Complex.exp ((y : ℂ) * I)‖ = x := fun x y hx => by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx]
  show ∫⁻ z, ψ z ∂(volume.restrict unitDisc).withDensity
    (fun z => ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ hd hψ, s10_prb_polar_disk (hd.mul hψ)]
  have hin : ∀ ρ ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal ρ * ∫⁻ θ in Ioo (-π) π,
      ((fun z : ℂ => ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2)) * ψ)
        ((ρ : ℂ) * Complex.exp ((θ : ℂ) * I)) =
      ENNReal.ofReal ρ * (ENNReal.ofReal ((2 / (1 - ρ ^ 2)) ^ 2) *
        ∫⁻ θ in Ioo (-π) π, ψ ((ρ : ℂ) * Complex.exp ((θ : ℂ) * I))) := by
    intro ρ hρ
    congr 1
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun θ => ?_)
    simp only [Pi.mul_apply, hnorm ρ θ hρ.1]
  rw [setLIntegral_congr_fun measurableSet_Ioo hin]
  have himg : (fun s : ℝ => Real.tanh (s / 2)) '' Ioi 0 = Ioo 0 1 := by
    ext ρ
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs' : (0 : ℝ) < s := hs
      refine ⟨?_, Real.tanh_lt_one _⟩
      show 0 < Real.tanh (s / 2)
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
    · intro hρ
      refine ⟨2 * Real.artanh ρ, ?_, ?_⟩
      · have := Real.artanh_pos hρ
        show (0 : ℝ) < 2 * Real.artanh ρ
        linarith
      · show Real.tanh (2 * Real.artanh ρ / 2) = ρ
        rw [mul_div_cancel_left₀ _ two_ne_zero]
        exact Real.tanh_artanh ⟨by linarith [hρ.1], hρ.2⟩
  have hder : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun s : ℝ => Real.tanh (s / 2))
      ((1 - Real.tanh (s / 2) ^ 2) / 2) (Ioi 0) s := by
    intro s _
    have h := (s03_geo_hasDerivAt_tanh (s / 2)).comp s ((hasDerivAt_id' s).div_const 2)
    refine (h.congr_deriv ?_).hasDerivWithinAt
    ring
  have hinj : InjOn (fun s : ℝ => Real.tanh (s / 2)) (Ioi 0) := by
    intro x _ y _ hxy
    have := Real.tanh_injective hxy
    linarith
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hinj]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have hs' : (0 : ℝ) < s := hs
  obtain ⟨t, ht⟩ : ∃ t, t = Real.tanh (s / 2) := ⟨_, rfl⟩
  have ht0 : 0 < t := by
    rw [ht, Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
  have ht1 : t < 1 := ht ▸ Real.tanh_lt_one _
  have h1t : 0 < 1 - t ^ 2 := by nlinarith
  have hsinh : Real.sinh s = 2 * t / (1 - t ^ 2) := by rw [ht]; exact (s03_geo_cosh_tanh s).2
  simp only [← ht]
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _),
    ← ENNReal.ofReal_mul (by positivity), hsinh, abs_of_pos (by positivity)]
  congr 2
  field_simp

/-- `thm:plane-ratio` (b) helper: `diskMob c` is the Blaschke factor `M_{-c}`. -/
theorem s10_prb_mob_eq (c : ℂ) : diskMob c = blaschke (-c) := funext fun z => by
  show (z + c) / (1 + conj c * z) = (z - -c) / (1 - conj (-c) * z)
  rw [map_neg, sub_neg_eq_add, neg_mul, sub_neg_eq_add]

/-- `thm:plane-ratio` (b) helper: `𝔊` is Borel measurable. -/
theorem s10_prb_meas_G : Measurable resolventG := by
  have hA : Measurable Real.artanh := by
    show Measurable fun x : ℝ => Real.log √((1 + x) / (1 - x))
    fun_prop
  show Measurable fun r => (Real.cosh r * Real.artanh (1 / Real.cosh r) - 1) / (2 * π)
  fun_prop

/-- `thm:plane-ratio` (b) helper: `z ↦ d_𝔻(0, z)` is Borel measurable. -/
theorem s10_prb_meas_dist : Measurable fun z : ℂ => diskDist 0 z := by
  show Measurable fun z : ℂ => Real.log (diskCoshDist 0 z + √(diskCoshDist 0 z ^ 2 - 1))
  unfold diskCoshDist
  fun_prop

/-- `thm:plane-ratio` (b) helper: `tanh` is continuous. -/
theorem s10_prb_continuous_tanh : Continuous Real.tanh := by
  rw [show Real.tanh = fun x => Real.sinh x / Real.cosh x from
    funext fun x => Real.tanh_eq_sinh_div_cosh x]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')

/-- `lem:plane-green` (g) helper: for any real bilinear form `B` on `ℂ`,
`B(c, c) + B(ic, ic) = |c|² (B(1, 1) + B(i, i))`. -/
theorem s10_pgg_d2_conformal (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (c : ℂ) :
    B c c + B (c * I) (c * I) = ‖c‖ ^ 2 * (B 1 1 + B I I) := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℝ, c = a • (1 : ℂ) + b • I :=
    ⟨c.re, c.im, by apply Complex.ext <;> simp⟩
  have h1 : (a • (1 : ℂ) + b • I) * I = (-b) • (1 : ℂ) + a • I := by
    apply Complex.ext <;> simp
  have h2 : ‖a • (1 : ℂ) + b • I‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [h1, h2]
  simp only [map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul]
  ring

/-- `lem:plane-green` (g) helper: second derivative of `v ∘ φ` for `φ` holomorphic,
`D²(v ∘ φ)(z)(h, k) = D²v(φ z)(φ'h, φ'k) + Dv(φ z)(φ'' h k)`. -/
theorem s10_pgg_d2_holo {v : ℂ → ℝ} {φ : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hv : ContDiffOn ℝ 2 v V) (hφ : DifferentiableOn ℂ φ U) (hUV : MapsTo φ U V) {z : ℂ}
    (hz : z ∈ U) (h k : ℂ) :
    fderiv ℝ (fderiv ℝ (fun y => v (φ y))) z h k =
      fderiv ℝ (fderiv ℝ v) (φ z) (deriv φ z * h) (deriv φ z * k) +
        fderiv ℝ v (φ z) (deriv (deriv φ) z * h * k) := by
  have hreal : ∀ {g : ℂ → ℂ} {y : ℂ}, DifferentiableAt ℂ g y →
      HasFDerivAt g (ContinuousLinearMap.mul ℝ ℂ (deriv g y)) y := by
    intro g y hg
    have h := hg.hasDerivAt.hasFDerivAt.restrictScalars ℝ
    convert h using 1
    refine ContinuousLinearMap.ext fun w => ?_
    simp [mul_comm]
  have hφd : ∀ y ∈ U, HasFDerivAt φ (ContinuousLinearMap.mul ℝ ℂ (deriv φ y)) y := fun y hy =>
    hreal (hφ.differentiableAt (hU.mem_nhds hy))
  have hφ2 : HasFDerivAt (deriv φ) (ContinuousLinearMap.mul ℝ ℂ (deriv (deriv φ) z)) z :=
    hreal ((hφ.deriv hU).differentiableAt (hU.mem_nhds hz))
  have hvw : ∀ w ∈ V, ContDiffAt ℝ 2 v w := fun w hw => hv.contDiffAt (hV.mem_nhds hw)
  have hF : fderiv ℝ (fun y => v (φ y)) =ᶠ[𝓝 z]
      fun y => (fderiv ℝ v (φ y)).comp (ContinuousLinearMap.mul ℝ ℂ (deriv φ y)) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact (((hvw _ (hUV hy)).differentiableAt two_ne_zero).hasFDerivAt.comp y (hφd y hy)).fderiv
  have hD2 : HasFDerivAt (fderiv ℝ v) (fderiv ℝ (fderiv ℝ v) (φ z)) (φ z) :=
    (((hvw _ (hUV hz)).fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).hasFDerivAt
  have hA : HasFDerivAt (fun y => fderiv ℝ v (φ y))
      ((fderiv ℝ (fderiv ℝ v) (φ z)).comp (ContinuousLinearMap.mul ℝ ℂ (deriv φ z))) z :=
    hD2.comp z (hφd z hz)
  have hL : HasFDerivAt (fun y => ContinuousLinearMap.mul ℝ ℂ (deriv φ y))
      ((ContinuousLinearMap.mul ℝ ℂ).comp (ContinuousLinearMap.mul ℝ ℂ (deriv (deriv φ) z))) z :=
    (ContinuousLinearMap.mul ℝ ℂ).hasFDerivAt.comp z hφ2
  rw [hF.fderiv_eq, (hA.clm_comp hL).fderiv]
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply']
  rw [add_comm]

/-- `lem:plane-green` (g) helper (conformal chain rule): for `φ` holomorphic on an open
`U` with `φ(U) ⊆ V` and `v ∈ C²(V)`, `Δ(v ∘ φ) = |φ'|² (Δv) ∘ φ` on `U`. -/
theorem s10_pgg_lap_holo {v : ℂ → ℝ} {φ : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hv : ContDiffOn ℝ 2 v V) (hφ : DifferentiableOn ℂ φ U) (hUV : MapsTo φ U V) :
    ContDiffOn ℝ 2 (fun y => v (φ y)) U ∧ ∀ z ∈ U,
      Laplacian.laplacian (fun y => v (φ y)) z = ‖deriv φ z‖ ^ 2 * Laplacian.laplacian v (φ z) := by
  refine ⟨hv.comp ((hφ.contDiffOn hU).restrict_scalars ℝ) hUV, fun z hz => ?_⟩
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  beta_reduce
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply,
    iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [s10_pgg_d2_holo hU hV hv hφ hUV hz, s10_pgg_d2_holo hU hV hv hφ hUV hz]
  have hc := s10_pgg_d2_conformal (fderiv ℝ (fderiv ℝ v) (φ z)) (deriv φ z)
  have hI : deriv (deriv φ) z * I * I = -(deriv (deriv φ) z * 1 * 1) := by
    rw [mul_assoc, I_mul_I]
    ring
  rw [hI, map_neg, mul_one, mul_one]
  linear_combination hc

/-- `lem:plane-green` (g) helper (G0): the hyperbolic Laplacian commutes with the disk automorphism
`diskMob p` (conformal chain rule `Δ(v ∘ φ) = |φ'|² (Δv) ∘ φ` and `|φ'|(1-|z|²) = 1-|φ z|²`). -/
theorem s10_pgg_lap_mob {v : ℂ → ℝ} (hv : ContDiffOn ℝ 2 v unitDisc) {p : ℂ} (hp : p ∈ unitDisc) :
    ContDiffOn ℝ 2 (fun z => v (diskMob p z)) unitDisc ∧ ∀ z ∈ unitDisc,
      hypLaplacianDisk (fun z => v (diskMob p z)) z = hypLaplacianDisk v (diskMob p z) := by
  have hp' : ‖-p‖ < 1 := by rw [norm_neg]; exact mem_ball_zero_iff.mp hp
  have hU : IsOpen unitDisc := isOpen_ball
  have hd : DifferentiableOn ℂ (diskMob p) unitDisc := fun z hz => by
    rw [s10_prb_mob_eq]
    exact (hasDerivAt_blaschke hp'
      (mem_ball_zero_iff.mp hz)).differentiableAt.differentiableWithinAt
  obtain ⟨hC, hL⟩ := s10_pgg_lap_holo hU hU hv hd (s10_pr_mob hp).1
  refine ⟨hC, fun z hz => ?_⟩
  show ((1 - ‖z‖ ^ 2) / 2) ^ 2 * Laplacian.laplacian (fun z => v (diskMob p z)) z =
    ((1 - ‖diskMob p z‖ ^ 2) / 2) ^ 2 * Laplacian.laplacian v (diskMob p z)
  rw [hL z hz]
  have hk := s05_norm_deriv_blaschke_neg (mem_ball_zero_iff.mp hp) (mem_ball_zero_iff.mp hz)
  rw [← s10_prb_mob_eq] at hk
  rw [← hk]
  ring

/-- `lem:plane-green` (g) helper: for `v ∈ C²(𝔻)`, the Euclidean Laplacian `Δv` is
continuous on `𝔻`. -/
theorem s10_pgg_laplacian_cont {v : ℂ → ℝ} (hv : ContDiffOn ℝ 2 v unitDisc) :
    ContinuousOn (Laplacian.laplacian v) unitDisc := by
  have hU : IsOpen unitDisc := isOpen_ball
  have h2 : ContinuousOn (fun z => iteratedFDeriv ℝ 2 v z) unitDisc :=
    (hv.continuousOn_iteratedFDerivWithin (m := 2) le_rfl hU.uniqueDiffOn).congr fun z hz =>
      (iteratedFDerivWithin_of_isOpen 2 hU hz).symm
  have hc : ContinuousOn (fun z =>
      iteratedFDeriv ℝ 2 v z ![1, 1] + iteratedFDeriv ℝ 2 v z ![I, I]) unitDisc :=
    ((continuous_eval_const _).comp_continuousOn h2).add
      ((continuous_eval_const _).comp_continuousOn h2)
  refine hc.congr fun z _ => ?_
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]

/-- `lem:plane-green` (g) helper (differentiation under `∫₀^{2π}`): if `G, G'` are
continuous on `(a, b) × ℝ` and `∂ₓG = G'`, then `x ↦ ∫₀^{2π} G(x, θ) dθ` has derivative
`∫₀^{2π} G'(r, θ) dθ` at `r ∈ (a, b)`. -/
theorem s10_pgg_param_deriv {G G' : ℝ × ℝ → ℝ} {a b r : ℝ}
    (hG : ContinuousOn G (Ioo a b ×ˢ univ)) (hG' : ContinuousOn G' (Ioo a b ×ˢ univ))
    (hd : ∀ x ∈ Ioo a b, ∀ θ : ℝ, HasDerivAt (fun x => G (x, θ)) (G' (x, θ)) x)
    (hr : r ∈ Ioo a b) :
    HasDerivAt (fun x => ∫ θ in (0 : ℝ)..(2 * π), G (x, θ))
      (∫ θ in (0 : ℝ)..(2 * π), G' (r, θ)) r := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_Ioo r hr
  have hsub : closedBall r (ε / 2) ⊆ Ioo a b :=
    (closedBall_subset_ball (half_lt_self hε)).trans hball
  have hθc : ∀ {H : ℝ × ℝ → ℝ}, ContinuousOn H (Ioo a b ×ˢ univ) → ∀ x ∈ Ioo a b,
      Continuous fun θ : ℝ => H (x, θ) := fun hH x hx =>
    hH.comp_continuous (by fun_prop) (fun θ => ⟨hx, mem_univ θ⟩)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall r (ε / 2)).prod
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * π)))).exists_bound_of_continuousOn
      (hG'.mono (prod_mono hsub (subset_univ _)))
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := 2 * π) (F := fun x θ => G (x, θ)) (F' := fun x θ => G' (x, θ))
    (bound := fun _ => C) (s := ball r (ε / 2)) (ball_mem_nhds r (half_pos hε)) ?_
    ((hθc hG r hr).intervalIntegrable 0 (2 * π)) (hθc hG' r hr).aestronglyMeasurable ?_
    intervalIntegrable_const ?_
  · exact h.2
  · filter_upwards [Ioo_mem_nhds hr.1 hr.2] with x hx
    exact (hθc hG x hx).aestronglyMeasurable
  · refine ae_of_all _ fun t ht x hx => hC (x, t) ⟨ball_subset_closedBall hx, ?_⟩
    rw [uIoc_of_le Real.two_pi_pos.le] at ht
    exact Ioc_subset_Icc_self ht
  · exact ae_of_all _ fun t _ x hx => hd x (hsub (ball_subset_closedBall hx)) t

/-- `lem:plane-green` (g) helper: if `G` is continuous on `(a, b) × ℝ`, then
`x ↦ ∫₀^{2π} G(x, θ) dθ` is continuous at every `r ∈ (a, b)`. -/
theorem s10_pgg_param_contAt {G : ℝ × ℝ → ℝ} {a b r : ℝ} (hG : ContinuousOn G (Ioo a b ×ˢ univ))
    (hr : r ∈ Ioo a b) :
    ContinuousAt (fun r => ∫ θ in (0 : ℝ)..(2 * π), G (r, θ)) r := by
  have hc : Continuous fun p : ℝ × ℝ => G (max ((a + r) / 2) (min ((r + b) / 2) p.1), p.2) :=
    hG.comp_continuous ((continuous_const.max (continuous_const.min continuous_fst)).prodMk
      continuous_snd) (fun p => ⟨⟨lt_of_lt_of_le (by linarith [hr.1]) (le_max_left _ _),
        max_lt (by linarith [hr.1, hr.2]) (lt_of_le_of_lt (min_le_left _ _)
          (by linarith [hr.2]))⟩, mem_univ _⟩)
  have h := (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (f := fun x θ => G (max ((a + r) / 2) (min ((r + b) / 2) x), θ)) hc 0 (2 * π)).continuousAt
      (x := r)
  refine h.congr ?_
  filter_upwards [Ioo_mem_nhds (show (a + r) / 2 < r by linarith [hr.1])
    (show r < (r + b) / 2 by linarith [hr.2])] with x hx
  have hm : max ((a + r) / 2) (min ((r + b) / 2) x) = x := by
    rw [min_eq_right hx.2.le, max_eq_right hx.1.le]
  simp only [hm]

/-- `lem:plane-green` (g) helper (polar Laplacian, integrated over a circle): for
`u ∈ C²(𝔻)` and `r ∈ (0, 1)`, `∫ ∂²ᵣu = ∫ Δu - (∫ ∂ᵣu)/r` over `|z| = r`. -/
theorem s10_pgg_euclid_id {u : ℂ → ℝ} (hu : ContDiffOn ℝ 2 u unitDisc) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    (∫ θ in (0 : ℝ)..(2 * π), Laplacian.laplacian u ((r : ℂ) * Complex.exp ((θ : ℂ) * I))) -
        (∫ θ in (0 : ℝ)..(2 * π), fderiv ℝ u ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
          (Complex.exp ((θ : ℂ) * I))) / r =
      ∫ θ in (0 : ℝ)..(2 * π), fderiv ℝ (fderiv ℝ u) ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
        (Complex.exp ((θ : ℂ) * I)) (Complex.exp ((θ : ℂ) * I)) := by
  have hU : IsOpen unitDisc := isOpen_ball
  have hnorm : ∀ θ : ℝ, ‖Complex.exp ((θ : ℂ) * I)‖ = 1 := fun θ => Complex.norm_exp_ofReal_mul_I θ
  have hP : ∀ θ : ℝ, (r : ℂ) * Complex.exp ((θ : ℂ) * I) ∈ unitDisc := by
    intro θ
    show _ ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, norm_mul, hnorm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr.1]
    exact hr.2
  have hat : ∀ z ∈ unitDisc, ContDiffAt ℝ 2 u z := fun z hz => hu.contDiffAt (hU.mem_nhds hz)
  have hD2at : ∀ z ∈ unitDisc, HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) z) z := fun z hz =>
    (((hat z hz).fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).hasFDerivAt
  have hD1c : ContinuousOn (fderiv ℝ u) unitDisc :=
    hu.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hD2c : ContinuousOn (fderiv ℝ (fderiv ℝ u)) unitDisc :=
    (hu.fderiv_of_isOpen hU (m := 1) le_rfl).continuousOn_fderiv_of_isOpen hU le_rfl
  have hcw : Continuous fun θ : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * I) := by fun_prop
  have hcE : Continuous fun θ : ℝ => Complex.exp ((θ : ℂ) * I) := by fun_prop
  have hB : Continuous fun θ : ℝ => fderiv ℝ (fderiv ℝ u) ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
    hD2c.comp_continuous hcw hP
  have hX : Continuous fun θ : ℝ => fderiv ℝ (fderiv ℝ u) ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
      (Complex.exp ((θ : ℂ) * I)) (Complex.exp ((θ : ℂ) * I)) := (hB.clm_apply hcE).clm_apply hcE
  have hY : Continuous fun θ : ℝ => fderiv ℝ (fderiv ℝ u) ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
      (Complex.exp ((θ : ℂ) * I) * I) (Complex.exp ((θ : ℂ) * I) * I) :=
    (hB.clm_apply (hcE.mul continuous_const)).clm_apply (hcE.mul continuous_const)
  have hZ : Continuous fun θ : ℝ => fderiv ℝ u ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
      (Complex.exp ((θ : ℂ) * I)) := (hD1c.comp_continuous hcw hP).clm_apply hcE
  -- `Δu = u_xx + u_yy` rotated to the frame `(e^{iθ}, i e^{iθ})`
  have hlap : ∀ θ : ℝ, Laplacian.laplacian u ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) =
      fderiv ℝ (fderiv ℝ u) ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
        (Complex.exp ((θ : ℂ) * I)) (Complex.exp ((θ : ℂ) * I)) +
      fderiv ℝ (fderiv ℝ u) ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
        (Complex.exp ((θ : ℂ) * I) * I) (Complex.exp ((θ : ℂ) * I) * I) := by
    intro θ
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
    beta_reduce
    rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [s10_pgg_d2_conformal, hnorm, one_pow, one_mul]
  -- `∫₀^{2π} ∂²_θ u(r e^{iθ}) dθ = 0`
  have hEd : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => Complex.exp ((θ : ℂ) * I))
      (Complex.exp ((θ : ℂ) * I) * I) θ := fun θ => by
    simpa using ((hasDerivAt_id θ).ofReal_comp.mul_const I).cexp
  have hw : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * I))
      ((r : ℂ) * (Complex.exp ((θ : ℂ) * I) * I)) θ := fun θ => (hEd θ).const_mul (r : ℂ)
  have hf : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => fderiv ℝ u ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
      ((r : ℂ) * Complex.exp ((θ : ℂ) * I) * I))
      (fderiv ℝ (fderiv ℝ u) ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
          ((r : ℂ) * (Complex.exp ((θ : ℂ) * I) * I)) ((r : ℂ) * Complex.exp ((θ : ℂ) * I) * I) +
        fderiv ℝ u ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
          ((r : ℂ) * (Complex.exp ((θ : ℂ) * I) * I) * I)) θ := fun θ => by
    have hA : HasFDerivAt (fderiv ℝ u)
        (fderiv ℝ (fderiv ℝ u) ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))
        ((fun θ : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * I)) θ) := hD2at _ (hP θ)
    have hB := HasFDerivAt.comp_hasDerivAt (f := fun θ : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * I))
      θ hA (hw θ)
    exact hB.clm_apply ((hw θ).mul_const I)
  have hf' : ∀ θ : ℝ,
      fderiv ℝ (fderiv ℝ u) ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
          ((r : ℂ) * (Complex.exp ((θ : ℂ) * I) * I)) ((r : ℂ) * Complex.exp ((θ : ℂ) * I) * I) +
        fderiv ℝ u ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
          ((r : ℂ) * (Complex.exp ((θ : ℂ) * I) * I) * I) =
      r ^ 2 * fderiv ℝ (fderiv ℝ u) ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
          (Complex.exp ((θ : ℂ) * I) * I) (Complex.exp ((θ : ℂ) * I) * I) -
        r * fderiv ℝ u ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) (Complex.exp ((θ : ℂ) * I)) := by
    intro θ
    have h1 : (r : ℂ) * (Complex.exp ((θ : ℂ) * I) * I) = r • (Complex.exp ((θ : ℂ) * I) * I) := by
      rw [Complex.real_smul]
    have h2 : (r : ℂ) * Complex.exp ((θ : ℂ) * I) * I = r • (Complex.exp ((θ : ℂ) * I) * I) := by
      rw [Complex.real_smul, mul_assoc]
    have h3 : (r : ℂ) * (Complex.exp ((θ : ℂ) * I) * I) * I = (-r) • Complex.exp ((θ : ℂ) * I) := by
      rw [Complex.real_smul, mul_assoc, mul_assoc, I_mul_I]
      push_cast
      ring
    rw [h3, h1, h2]
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hper : ∫ θ in (0 : ℝ)..(2 * π), (r ^ 2 * fderiv ℝ (fderiv ℝ u)
      ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
        (Complex.exp ((θ : ℂ) * I) * I) (Complex.exp ((θ : ℂ) * I) * I) -
      r * fderiv ℝ u ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) (Complex.exp ((θ : ℂ) * I))) = 0 := by
    have hint : IntervalIntegrable (fun θ : ℝ => r ^ 2 * fderiv ℝ (fderiv ℝ u)
        ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
          (Complex.exp ((θ : ℂ) * I) * I) (Complex.exp ((θ : ℂ) * I) * I) -
        r * fderiv ℝ u ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) (Complex.exp ((θ : ℂ) * I)))
        volume 0 (2 * π) :=
      ((continuous_const.mul hY).sub (continuous_const.mul hZ)).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => by rw [← hf' θ]; exact hf θ)
      hint]
    have hE2 : Complex.exp (((2 * π : ℝ) : ℂ) * I) = Complex.exp (((0 : ℝ) : ℂ) * I) := by
      rw [ofReal_zero, zero_mul, Complex.exp_zero]
      push_cast
      exact Complex.exp_two_pi_mul_I
    rw [hE2, sub_self]
  have hr0 : r ≠ 0 := hr.1.ne'
  have hYi : IntervalIntegrable (fun θ : ℝ => r ^ 2 * fderiv ℝ (fderiv ℝ u)
      ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
        (Complex.exp ((θ : ℂ) * I) * I) (Complex.exp ((θ : ℂ) * I) * I)) volume 0 (2 * π) :=
    (continuous_const.mul hY).intervalIntegrable _ _
  have hZi : IntervalIntegrable (fun θ : ℝ => r * fderiv ℝ u ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
      (Complex.exp ((θ : ℂ) * I))) volume 0 (2 * π) :=
    (continuous_const.mul hZ).intervalIntegrable _ _
  have hYZ : ∫ θ in (0 : ℝ)..(2 * π), fderiv ℝ (fderiv ℝ u) ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
      (Complex.exp ((θ : ℂ) * I) * I) (Complex.exp ((θ : ℂ) * I) * I) =
      (∫ θ in (0 : ℝ)..(2 * π), fderiv ℝ u ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
        (Complex.exp ((θ : ℂ) * I))) / r := by
    rw [intervalIntegral.integral_sub hYi hZi, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hper
    rw [eq_div_iff hr0]
    apply mul_left_cancel₀ hr0
    linear_combination hper
  rw [intervalIntegral.integral_congr (fun θ _ => hlap θ),
    intervalIntegral.integral_add (hX.intervalIntegrable _ _) (hY.intervalIntegrable _ _), hYZ]
  ring

/-- `lem:plane-green` (g) helper (G1, Euclidean circle means): for `u ∈ C²(𝔻)` and
`A(r) = ∫₀^{2π} u(r e^{iθ}) dθ`, `A'' + A'/r = ∫₀^{2π} Δu(r e^{iθ}) dθ` on `(0, 1)`, `A' → 0` and
`A → 2π u(0)` as `r ↓ 0`. -/
theorem s10_pgg_euclid_ode {u : ℂ → ℝ} (hu : ContDiffOn ℝ 2 u unitDisc) :
    ∃ A' : ℝ → ℝ,
      (∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt
        (fun r : ℝ => ∫ θ in (0 : ℝ)..(2 * π), u ((r : ℂ) * Complex.exp ((θ : ℂ) * I))) (A' r) r) ∧
      (∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt A'
        ((∫ θ in (0 : ℝ)..(2 * π), Laplacian.laplacian u ((r : ℂ) * Complex.exp ((θ : ℂ) * I))) -
          A' r / r) r) ∧
      Tendsto A' (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun r : ℝ => ∫ θ in (0 : ℝ)..(2 * π), u ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))
        (𝓝[>] 0) (𝓝 (2 * π * u 0)) := by
  have hU : IsOpen unitDisc := isOpen_ball
  have hP : ∀ {r : ℝ}, r ∈ Ioo (-1 : ℝ) 1 → ∀ θ : ℝ,
      (r : ℂ) * Complex.exp ((θ : ℂ) * I) ∈ unitDisc := by
    intro r hr θ
    show _ ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_lt]
    exact hr
  have hat : ∀ z ∈ unitDisc, ContDiffAt ℝ 2 u z := fun z hz => hu.contDiffAt (hU.mem_nhds hz)
  have hD2at : ∀ z ∈ unitDisc, HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) z) z := fun z hz =>
    (((hat z hz).fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).hasFDerivAt
  have hD1c : ContinuousOn (fderiv ℝ u) unitDisc :=
    hu.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hD2c : ContinuousOn (fderiv ℝ (fderiv ℝ u)) unitDisc :=
    (hu.fderiv_of_isOpen hU (m := 1) le_rfl).continuousOn_fderiv_of_isOpen hU le_rfl
  have hcP : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I) := by fun_prop
  have hcE : Continuous fun p : ℝ × ℝ => Complex.exp ((p.2 : ℂ) * I) := by fun_prop
  have hmaps : MapsTo (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I))
      (Ioo (-1) 1 ×ˢ univ) unitDisc := fun p hp => hP hp.1 p.2
  have hG0 : ContinuousOn (fun p : ℝ × ℝ => u ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I)))
      (Ioo (-1) 1 ×ˢ univ) := hu.continuousOn.comp hcP.continuousOn hmaps
  have hG1 : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ u ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I))
      (Complex.exp ((p.2 : ℂ) * I))) (Ioo (-1) 1 ×ˢ univ) :=
    (hD1c.comp hcP.continuousOn hmaps).clm_apply hcE.continuousOn
  have hG2 : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (fderiv ℝ u)
      ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I)) (Complex.exp ((p.2 : ℂ) * I))
        (Complex.exp ((p.2 : ℂ) * I))) (Ioo (-1) 1 ×ˢ univ) :=
    ((hD2c.comp hcP.continuousOn hmaps).clm_apply hcE.continuousOn).clm_apply hcE.continuousOn
  have hline : ∀ r θ : ℝ, HasDerivAt (fun x : ℝ => (x : ℂ) * Complex.exp ((θ : ℂ) * I))
      (Complex.exp ((θ : ℂ) * I)) r := fun r θ => by
    simpa using (hasDerivAt_id r).ofReal_comp.mul_const (Complex.exp ((θ : ℂ) * I))
  have hd0 : ∀ x ∈ Ioo (-1 : ℝ) 1, ∀ θ : ℝ,
      HasDerivAt (fun x : ℝ => u ((x : ℂ) * Complex.exp ((θ : ℂ) * I)))
        (fderiv ℝ u ((x : ℂ) * Complex.exp ((θ : ℂ) * I)) (Complex.exp ((θ : ℂ) * I))) x :=
    fun x hx θ => by
      have hA : HasFDerivAt u (fderiv ℝ u ((x : ℂ) * Complex.exp ((θ : ℂ) * I)))
          ((fun x : ℝ => (x : ℂ) * Complex.exp ((θ : ℂ) * I)) x) :=
        ((hat _ (hP hx θ)).differentiableAt two_ne_zero).hasFDerivAt
      exact HasFDerivAt.comp_hasDerivAt (f := fun x : ℝ => (x : ℂ) * Complex.exp ((θ : ℂ) * I))
        x hA (hline x θ)
  have hd1 : ∀ x ∈ Ioo (-1 : ℝ) 1, ∀ θ : ℝ,
      HasDerivAt (fun x : ℝ => fderiv ℝ u ((x : ℂ) * Complex.exp ((θ : ℂ) * I))
        (Complex.exp ((θ : ℂ) * I)))
        (fderiv ℝ (fderiv ℝ u) ((x : ℂ) * Complex.exp ((θ : ℂ) * I)) (Complex.exp ((θ : ℂ) * I))
          (Complex.exp ((θ : ℂ) * I))) x := fun x hx θ => by
    have hA : HasFDerivAt (fderiv ℝ u)
        (fderiv ℝ (fderiv ℝ u) ((x : ℂ) * Complex.exp ((θ : ℂ) * I)))
        ((fun x : ℝ => (x : ℂ) * Complex.exp ((θ : ℂ) * I)) x) := hD2at _ (hP hx θ)
    have hB := HasFDerivAt.comp_hasDerivAt (f := fun x : ℝ => (x : ℂ) * Complex.exp ((θ : ℂ) * I))
      x hA (hline x θ)
    have h := hB.clm_apply (hasDerivAt_const x (Complex.exp ((θ : ℂ) * I)))
    rw [map_zero, add_zero] at h
    exact h
  have hI : ∀ {r : ℝ}, r ∈ Ioo (0 : ℝ) 1 → r ∈ Ioo (-1 : ℝ) 1 := fun hr =>
    ⟨by linarith [hr.1], hr.2⟩
  have h0 : ∀ θ : ℝ, ((0 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I) = 0 := fun θ => by
    rw [ofReal_zero, zero_mul]
  refine ⟨fun r => ∫ θ in (0 : ℝ)..(2 * π), fderiv ℝ u ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
    (Complex.exp ((θ : ℂ) * I)), fun r hr => s10_pgg_param_deriv hG0 hG1 hd0 (hI hr),
    fun r hr => ?_, ?_, ?_⟩
  · rw [s10_pgg_euclid_id hu hr]
    exact s10_pgg_param_deriv hG1 hG2 hd1 (hI hr)
  · have h := (s10_pgg_param_contAt hG1 (show (0 : ℝ) ∈ Ioo (-1) 1 by norm_num)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    dsimp only at h
    convert h using 2
    simp only [h0]
    rw [ContinuousLinearMap.intervalIntegral_comp_comm _
      ((by fun_prop : Continuous fun θ : ℝ => Complex.exp ((θ : ℂ) * I)).intervalIntegrable _ _)]
    have hint : ∫ θ in (0 : ℝ)..(2 * π), Complex.exp ((θ : ℂ) * I) = 0 := by
      have h := integral_exp_mul_complex (a := 0) (b := 2 * π) I_ne_zero
      simp only [mul_comm I] at h
      rw [h]
      push_cast
      rw [zero_mul, Complex.exp_zero, Complex.exp_two_pi_mul_I, sub_self, zero_div]
    rw [hint, map_zero]
  · have h := (s10_pgg_param_contAt hG0 (show (0 : ℝ) ∈ Ioo (-1) 1 by norm_num)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    dsimp only at h
    convert h using 2
    simp only [h0, intervalIntegral.integral_const, sub_zero, smul_eq_mul]

/-- `lem:plane-green` (g) helper (G2, hyperbolic circle means about `0`): `m(s) = m_s(0)` of
`u ∈ C²(𝔻)` satisfies `m'' + coth s m' = 2m - W` with `W(s) = m_s((2 - Δ)u)(0)` continuous, and
`m' → 0`, `m → u(0)` as `s ↓ 0`. -/
theorem s10_pgg_mean_ode {u : ℂ → ℝ} (hu : ContDiffOn ℝ 2 u unitDisc) :
    ∃ M' : ℝ → ℝ,
      (∀ s : ℝ, 0 < s → HasDerivAt (fun s => circleMean u 0 s) (M' s) s) ∧
      (∀ s : ℝ, 0 < s → HasDerivAt M' (2 * circleMean u 0 s -
        circleMean (fun z => 2 * u z - hypLaplacianDisk u z) 0 s -
          Real.cosh s / Real.sinh s * M' s) s) ∧
      ContinuousOn (fun s => circleMean (fun z => 2 * u z - hypLaplacianDisk u z) 0 s) (Ioi 0) ∧
      Tendsto M' (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun s => circleMean u 0 s) (𝓝[>] 0) (𝓝 (u 0)) := by
  obtain ⟨A', hA1, hA2, hA'0, hA0⟩ := s10_pgg_euclid_ode hu
  have hm0 : ∀ z, diskMob 0 z = z := fun z => by
    show (z + 0) / (1 + conj 0 * z) = z
    simp
  have hcm : ∀ (φ : ℂ → ℝ) (s : ℝ), circleMean φ 0 s = (2 * π)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * π), φ ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
    fun φ s => by
      unfold circleMean
      simp only [hm0]
  have hρ : ∀ s : ℝ, 0 < s → Real.tanh (s / 2) ∈ Ioo (0 : ℝ) 1 := fun s hs =>
    ⟨by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _),
      Real.tanh_lt_one _⟩
  have hρd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Real.tanh (s / 2))
      ((1 - Real.tanh (s / 2) ^ 2) / 2) s := fun s => by
    have h2 : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) s := (hasDerivAt_id' s).div_const 2
    have h := HasDerivAt.comp (h := fun s : ℝ => s / 2) s (s03_geo_hasDerivAt_tanh (s / 2)) h2
    refine h.congr_deriv ?_
    ring
  have hI : ∀ {r : ℝ}, r ∈ Ioo (0 : ℝ) 1 → r ∈ Ioo (-1 : ℝ) 1 := fun hr =>
    ⟨by linarith [hr.1], hr.2⟩
  have hP : ∀ {r : ℝ}, r ∈ Ioo (-1 : ℝ) 1 → ∀ θ : ℝ,
      (r : ℂ) * Complex.exp ((θ : ℂ) * I) ∈ unitDisc := by
    intro r hr θ
    show _ ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_lt]
    exact hr
  have hLc := s10_pgg_laplacian_cont hu
  have hcP : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I) := by fun_prop
  have hGL : ContinuousOn (fun p : ℝ × ℝ =>
      Laplacian.laplacian u ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I))) (Ioo (-1) 1 ×ˢ univ) :=
    hLc.comp hcP.continuousOn fun p hp => hP hp.1 p.2
  have hqc : Continuous fun s : ℝ => (1 - Real.tanh (s / 2) ^ 2) / 2 :=
    (continuous_const.sub ((s10_prb_continuous_tanh.comp (continuous_id.div_const 2)).pow
      2)).div_const 2
  have hq : ∀ s : ℝ, HasDerivAt (fun s : ℝ => (1 - Real.tanh (s / 2) ^ 2) / 2)
      (-Real.tanh (s / 2) * ((1 - Real.tanh (s / 2) ^ 2) / 2)) s := fun s => by
    have h := (((hρd s).pow 2).const_sub 1).div_const 2
    refine h.congr_deriv ?_
    norm_num
    ring
  -- `W = m_s((2 - Δ_ρ) u)` in terms of the Euclidean circle integrals at radius `tanh(s/2)`
  have hW : ∀ s : ℝ, 0 < s → circleMean (fun z => 2 * u z - hypLaplacianDisk u z) 0 s =
      2 * circleMean u 0 s - (2 * π)⁻¹ * (((1 - Real.tanh (s / 2) ^ 2) / 2) ^ 2 *
        ∫ θ in (0 : ℝ)..(2 * π), Laplacian.laplacian u
          ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I))) := by
    intro s hs
    have hρs := hρ s hs
    have hn : ∀ θ : ℝ, ‖(Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I)‖ = Real.tanh (s / 2) :=
      fun θ => by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hρs.1]
    have hcw : Continuous fun θ : ℝ => (Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I) := by
      fun_prop
    have hiu : IntervalIntegrable (fun θ : ℝ => 2 * u ((Real.tanh (s / 2) : ℂ) *
        Complex.exp ((θ : ℂ) * I))) volume 0 (2 * π) :=
      (continuous_const.mul (hu.continuousOn.comp_continuous hcw
        (hP (hI hρs)))).intervalIntegrable _ _
    have hiL : IntervalIntegrable (fun θ : ℝ => ((1 - Real.tanh (s / 2) ^ 2) / 2) ^ 2 *
        Laplacian.laplacian u ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I))) volume 0
        (2 * π) :=
      (continuous_const.mul (hLc.comp_continuous hcw (hP (hI hρs)))).intervalIntegrable _ _
    rw [hcm, hcm]
    simp only [hypLaplacianDisk, hn]
    rw [intervalIntegral.integral_sub hiu hiL, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    ring
  refine ⟨fun s => (2 * π)⁻¹ * (A' (Real.tanh (s / 2)) * ((1 - Real.tanh (s / 2) ^ 2) / 2)),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have h := (HasDerivAt.comp (h := fun s : ℝ => Real.tanh (s / 2)) s
      (hA1 _ (hρ s hs)) (hρd s)).const_mul (2 * π)⁻¹
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun t => hcm u t)
  · intro s hs
    have hρs := hρ s hs
    have h := ((HasDerivAt.comp (h := fun s : ℝ => Real.tanh (s / 2)) s
      (hA2 _ hρs) (hρd s)).mul (hq s)).const_mul (2 * π)⁻¹
    refine h.congr_deriv ?_
    simp only [Function.comp_apply]
    rw [hW s hs, hcm u s]
    obtain ⟨hch, hsh⟩ := s03_geo_cosh_tanh s
    rw [hch, hsh]
    have h0 := hρs.1
    have h1 : 0 < 1 - Real.tanh (s / 2) ^ 2 := by nlinarith [hρs.2]
    generalize (∫ θ in (0 : ℝ)..(2 * π), Laplacian.laplacian u
      ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I))) = L
    generalize (∫ θ in (0 : ℝ)..(2 * π), u
      ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I))) = B
    generalize A' (Real.tanh (s / 2)) = c
    generalize Real.tanh (s / 2) = ρ at h0 h1 ⊢
    field_simp
    ring
  · intro s hs
    have hρs := hρ s hs
    have hLt : ContinuousAt (fun s : ℝ => ∫ θ in (0 : ℝ)..(2 * π), Laplacian.laplacian u
        ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I))) s :=
      ContinuousAt.comp (f := fun s : ℝ => Real.tanh (s / 2)) (x := s)
        (s10_pgg_param_contAt hGL (hI hρs)) (hρd s).continuousAt
    have hmc : ContinuousAt (fun s => circleMean u 0 s) s := by
      have h := (HasDerivAt.comp (h := fun s : ℝ => Real.tanh (s / 2)) s
        (hA1 _ hρs) (hρd s)).const_mul (2 * π)⁻¹
      exact (h.congr_of_eventuallyEq (Eventually.of_forall fun t => hcm u t)).continuousAt
    have hc : ContinuousAt (fun s : ℝ => 2 * circleMean u 0 s - (2 * π)⁻¹ *
        (((1 - Real.tanh (s / 2) ^ 2) / 2) ^ 2 * ∫ θ in (0 : ℝ)..(2 * π), Laplacian.laplacian u
          ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I)))) s :=
      (continuousAt_const.mul hmc).sub (continuousAt_const.mul
        ((hqc.continuousAt.pow 2).mul hLt))
    refine (hc.congr ?_).continuousWithinAt
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact (hW t ht).symm
  · have hρt : Tendsto (fun s : ℝ => Real.tanh (s / 2)) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun s hs =>
        (hρ s hs).1⟩
      have h := ((hρd 0).continuousAt.tendsto).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      rwa [zero_div, Real.tanh_zero] at h
    have h := ((hA'0.comp hρt).mul
      (hqc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))).const_mul
        (2 * π)⁻¹
    rw [zero_mul, mul_zero] at h
    exact h
  · have hρt : Tendsto (fun s : ℝ => Real.tanh (s / 2)) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun s hs =>
        (hρ s hs).1⟩
      have h := ((hρd 0).continuousAt.tendsto).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      rwa [zero_div, Real.tanh_zero] at h
    have h := (hA0.comp hρt).const_mul (2 * π)⁻¹
    rw [show (2 * π)⁻¹ * (2 * π * u 0) = u 0 by field_simp] at h
    exact h.congr fun s => (hcm u s).symm

/-- `lem:plane-green` (g) helper: `(2π sinh s 𝔊'(s))' = 2 𝔊(s) 2π sinh s` on `(0, ∞)`. -/
theorem s10_pgg_P_deriv {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s => 2 * π * Real.sinh s * deriv resolventG s)
      (2 * (resolventG s * (2 * π * Real.sinh s))) s := by
  have h := (s10_hasDerivAt_prim_sinh hs).const_mul 2
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with r hr
  rw [s10_two_pi_sinh_deriv hr, Real.cosh_sq, one_div]
  ring

/-- `lem:plane-green` (g) helper: `𝔊(s) 2π sinh s → 0` as `s ↓ 0`. -/
theorem s10_pgg_G_zero :
    Tendsto (fun s => resolventG s * (2 * π * Real.sinh s)) (𝓝[>] 0) (𝓝 0) := by
  have hsinh : Tendsto Real.sinh (𝓝[>] 0) (𝓝 0) := by
    have h := Real.continuous_sinh.tendsto 0
    rw [Real.sinh_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hT1 := lem_plane_green_c.1.mul hsinh
  have hlog : Tendsto (fun s => Real.log s * s) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos
  have hslope : Tendsto (fun s : ℝ => s⁻¹ * Real.sinh s) (𝓝[>] 0) (𝓝 1) := by
    simpa using (Real.hasDerivAt_sinh 0).tendsto_slope_zero_right
  have hT2 : Tendsto (fun s => Real.log s * Real.sinh s) (𝓝[>] 0) (𝓝 0) := by
    have h := hlog.mul hslope
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [mul_assoc, ← mul_assoc s, mul_inv_cancel₀ (ne_of_gt hs), one_mul]
  have h := hT1.sub hT2
  rw [mul_zero, sub_zero] at h
  refine h.congr fun s => ?_
  ring

/-- `lem:plane-green` (g) helper: `𝔊 2π cosh`, `𝔊 2π sinh` and `2π sinh 𝔊'` tend to `0`
as `s → ∞`. -/
theorem s10_pgg_G_atTop :
    Tendsto (fun s => resolventG s * (2 * π * Real.cosh s)) atTop (𝓝 0) ∧
      Tendsto (fun s => resolventG s * (2 * π * Real.sinh s)) atTop (𝓝 0) ∧
      Tendsto (fun s => 2 * π * Real.sinh s * deriv resolventG s) atTop (𝓝 0) := by
  have hinv : Tendsto (fun s => (Real.cosh s)⁻¹) atTop (𝓝 0) :=
    s10_tendsto_cosh_atTop.inv_tendsto_atTop
  have hc : Tendsto (fun s => resolventG s * (2 * π * Real.cosh s)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with s hs
      exact mul_nonneg (s10_resolventG_pos hs).le (mul_pos Real.two_pi_pos (Real.cosh_pos s)).le
    · filter_upwards [s10_tendsto_cosh_atTop.eventually_ge_atTop 2] with s hs
      have hQ := lem_plane_green_e.1 _ (by linarith : 1 < Real.cosh s)
      show legendreQ1 (Real.cosh s) / (2 * π) * (2 * π * Real.cosh s) ≤ (Real.cosh s)⁻¹
      generalize Real.cosh s = x at hQ hs ⊢
      have h3 : 0 < 3 * (x ^ 2 - 1) := by nlinarith
      have e1 : legendreQ1 x / (2 * π) * (2 * π * x) = legendreQ1 x * x := by
        have := Real.pi_pos
        field_simp
      rw [e1]
      calc legendreQ1 x * x ≤ 1 / (3 * (x ^ 2 - 1)) * x :=
            mul_le_mul_of_nonneg_right hQ (by linarith)
        _ ≤ x⁻¹ := by
          rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ h3, inv_mul_eq_div,
            le_div_iff₀ (by linarith)]
          nlinarith
  refine ⟨hc, ?_, ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with s hs
      exact mul_nonneg (s10_resolventG_pos hs).le
        (mul_pos Real.two_pi_pos (Real.sinh_pos_iff.mpr hs)).le
    · filter_upwards [eventually_gt_atTop 0] with s hs
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.sinh_lt_cosh (x := s)).le Real.two_pi_pos.le)
        (s10_resolventG_pos hs).le
  · have hn := hinv.neg
    rw [neg_zero] at hn
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hn tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with s hs
      exact (lem_plane_green_d s hs).1
    · filter_upwards [eventually_gt_atTop 0] with s hs
      have := inv_pos.mpr (Real.cosh_pos s)
      linarith [(lem_plane_green_d s hs).2]

/-- `lem:plane-green` (g) helper (G3, bounded uniqueness for the radial ODE, by the Wronskian with
`𝔊`): a bounded solution of `y'' + coth s y' = 2y - g` with `g ≥ 0` continuous, `y' → 0` and
`y → y₀` at `0`, is `y₀ = ∫₀^∞ 𝔊(s) 2π sinh s g(s) ds`. -/
theorem s10_pgg_wronskian {y y' g : ℝ → ℝ} {y₀ : ℝ}
    (hy : ∀ s : ℝ, 0 < s → HasDerivAt y (y' s) s)
    (hy' : ∀ s : ℝ, 0 < s → HasDerivAt y' (2 * y s - g s - Real.cosh s / Real.sinh s * y' s) s)
    (hgc : ContinuousOn g (Ioi 0)) (hg : ∀ s : ℝ, 0 < s → 0 ≤ g s)
    (hb : ∃ M : ℝ, ∀ s : ℝ, 0 < s → |y s| ≤ M)
    (h0 : Tendsto y (𝓝[>] 0) (𝓝 y₀)) (h0' : Tendsto y' (𝓝[>] 0) (𝓝 0)) :
    IntegrableOn (fun s => resolventG s * (2 * π * Real.sinh s) * g s) (Ioi 0) ∧
      y₀ = ∫ s in Ioi (0 : ℝ), resolventG s * (2 * π * Real.sinh s) * g s := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨K, hK⟩ : ∃ K : ℝ → ℝ, K = fun s => resolventG s * (2 * π * Real.sinh s) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ → ℝ, P = fun s => 2 * π * Real.sinh s * deriv resolventG s :=
    ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ → ℝ, R = fun s => 2 * P s + resolventG s * (2 * π * Real.cosh s) :=
    ⟨_, rfl⟩
  -- the Wronskian `W = 2π sinh (𝔊 y' - 𝔊' y)`, with `W' = -𝔊 2π sinh g`
  obtain ⟨W, hW⟩ : ∃ W : ℝ → ℝ, W = fun s => K s * y' s - P s * y s := ⟨_, rfl⟩
  have hf : (fun s => resolventG s * (2 * π * Real.sinh s) * g s) = fun s => K s * g s := by
    rw [hK]
  rw [hf]
  have hGd : ∀ s : ℝ, 0 < s → HasDerivAt resolventG (deriv resolventG s) s := fun s hs =>
    (s10_hasDerivAt_resolventG hs).differentiableAt.hasDerivAt
  have hcd : ∀ s : ℝ, HasDerivAt (fun s => 2 * π * Real.sinh s) (2 * π * Real.cosh s) s :=
    fun s => (Real.hasDerivAt_sinh s).const_mul (2 * π)
  have hKd : ∀ s : ℝ, 0 < s → HasDerivAt K (P s + resolventG s * (2 * π * Real.cosh s)) s :=
    fun s hs => by
      rw [hK, hP]
      exact ((hGd s hs).mul (hcd s)).congr_deriv (by ring)
  have hPd : ∀ s : ℝ, 0 < s → HasDerivAt P (2 * K s) s := fun s hs => by
    rw [hP, hK]
    exact s10_pgg_P_deriv hs
  have hWd : ∀ s : ℝ, 0 < s → HasDerivAt W (-(K s * g s)) s := fun s hs => by
    have h := ((hKd s hs).mul (hy' s hs)).sub ((hPd s hs).mul (hy s hs))
    rw [hW]
    refine h.congr_deriv ?_
    rw [hK]
    beta_reduce
    have hsh : Real.sinh s ≠ 0 := (Real.sinh_pos_iff.mpr hs).ne'
    field_simp
    ring
  have hpos : ∀ {a b x : ℝ}, 0 < a → 0 < b → x ∈ uIcc a b → 0 < x := fun ha hb hx =>
    lt_of_lt_of_le (lt_min ha hb) hx.1
  have hKc : ContinuousOn K (Ioi 0) := fun s hs => (hKd s hs).continuousAt.continuousWithinAt
  have hfc : ContinuousOn (fun s => K s * g s) (Ioi 0) := hKc.mul hgc
  have hint : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable (fun s => K s * g s) volume a b :=
    fun a b ha hb => (hfc.mono fun x hx => hpos ha hb hx).intervalIntegrable
  have hFTC : ∀ a b : ℝ, 0 < a → 0 < b → ∫ s in a..b, K s * g s = W a - W b := by
    intro a b ha hb
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := W)
      (f' := fun s => -(K s * g s)) (fun x hx => hWd x (hpos ha hb hx)) (hint a b ha hb).neg
    rw [intervalIntegral.integral_neg] at h
    linarith
  have hfnn : ∀ s : ℝ, 0 < s → 0 ≤ K s * g s := fun s hs => by
    refine mul_nonneg ?_ (hg s hs)
    rw [hK]
    exact (mul_pos (s10_resolventG_pos hs) (mul_pos Real.two_pi_pos
      (Real.sinh_pos_iff.mpr hs))).le
  have hanti : ∀ a b : ℝ, 0 < a → a ≤ b → W b ≤ W a := by
    intro a b ha hab
    have h := hFTC a b ha (ha.trans_le hab)
    have hnn : 0 ≤ ∫ s in a..b, K s * g s :=
      intervalIntegral.integral_nonneg hab fun s hs => hfnn s (ha.trans_le hs.1)
    linarith
  -- `W → y₀` at `0`
  have hW0 : Tendsto W (𝓝[>] 0) (𝓝 y₀) := by
    have h := (s10_pgg_G_zero.mul h0').sub (lem_plane_green_c.2.2.mul h0)
    have e : (0 : ℝ) * 0 - -1 * y₀ = y₀ := by ring
    rw [e] at h
    rw [hW, hK, hP]
    exact h
  -- `W → 0` at `∞`: `W = (K y)' - R y` with `K, R → 0`, and `W` is antitone
  obtain ⟨hcI, hKI, hPI⟩ := s10_pgg_G_atTop
  have hV : ∀ s : ℝ, 0 < s → HasDerivAt (fun s => K s * y s) (W s + R s * y s) s := fun s hs => by
    refine ((hKd s hs).mul (hy s hs)).congr_deriv ?_
    rw [hW, hR]
    ring
  have hRI : Tendsto (fun s => R s * y s) atTop (𝓝 0) := by
    have hR0 : Tendsto R atTop (𝓝 0) := by
      have h := (hPI.const_mul 2).add hcI
      rw [mul_zero, add_zero] at h
      rw [hR, hP]
      exact h
    have hb0 : Tendsto (fun s => ‖R s‖ * M) atTop (𝓝 0) := by
      simpa using hR0.norm.mul_const M
    refine squeeze_zero_norm' ?_ hb0
    filter_upwards [eventually_gt_atTop 0] with s hs
    rw [norm_mul, Real.norm_eq_abs (y s)]
    exact mul_le_mul_of_nonneg_left (hM s hs) (norm_nonneg _)
  have hVI : Tendsto (fun s => K s * y s) atTop (𝓝 0) := by
    have hb0 : Tendsto (fun s => ‖K s‖ * M) atTop (𝓝 0) := by
      rw [hK]
      simpa using hKI.norm.mul_const M
    refine squeeze_zero_norm' ?_ hb0
    filter_upwards [eventually_gt_atTop 0] with s hs
    rw [norm_mul, Real.norm_eq_abs (y s)]
    exact mul_le_mul_of_nonneg_left (hM s hs) (norm_nonneg _)
  have hWc : ContinuousOn W (Ioi 0) := fun s hs => (hWd s hs).continuousAt.continuousWithinAt
  have hRyc : ContinuousOn (fun s => R s * y s) (Ioi 0) := fun s hs => by
    have hRc : ContinuousAt R s := by
      rw [hR]
      exact (continuousAt_const.mul (hPd s hs).continuousAt).add
        ((hGd s hs).continuousAt.mul (continuousAt_const.mul Real.continuous_cosh.continuousAt))
    exact (hRc.mul (hy s hs).continuousAt).continuousWithinAt
  have hIcc : ∀ b : ℝ, 0 < b → uIcc b (b + 1) ⊆ Ioi 0 := fun b hb x hx =>
    hpos hb (by linarith) hx
  have havg : ∀ b : ℝ, 0 < b → ∫ s in b..b + 1, W s =
      K (b + 1) * y (b + 1) - K b * y b - ∫ s in b..b + 1, R s * y s := by
    intro b hb
    have hWi := (hWc.mono (hIcc b hb)).intervalIntegrable (μ := volume)
    have hRi := (hRyc.mono (hIcc b hb)).intervalIntegrable (μ := volume)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => K s * y s)
      (fun x hx => hV x (hIcc b hb hx)) (hWi.add hRi)
    rw [intervalIntegral.integral_add hWi hRi] at h
    linarith
  have hbound : ∀ b : ℝ, 0 < b →
      W (b + 1) ≤ ∫ s in b..b + 1, W s ∧ ∫ s in b..b + 1, W s ≤ W b := by
    intro b hb
    have hWi := (hWc.mono (hIcc b hb)).intervalIntegrable (μ := volume)
    constructor
    · have h := intervalIntegral.integral_mono_on (show b ≤ b + 1 by linarith)
        intervalIntegrable_const hWi fun x hx => hanti x (b + 1) (hb.trans_le hx.1) hx.2
      simpa using h
    · have h := intervalIntegral.integral_mono_on (show b ≤ b + 1 by linarith)
        hWi intervalIntegrable_const fun x hx => hanti b x hb hx.1
      simpa using h
  have hWinf : Tendsto W atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨B1, hB1⟩ := Metric.tendsto_atTop.mp hVI (ε / 4) (by positivity)
    obtain ⟨B2, hB2⟩ := Metric.tendsto_atTop.mp hRI (ε / 4) (by positivity)
    have key : ∀ b : ℝ, max (max B1 B2) 1 ≤ b → |∫ s in b..b + 1, W s| ≤ 3 * ε / 4 := by
      intro b hb
      have hb1 : B1 ≤ b := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hb
      have hb2 : B2 ≤ b := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hb
      have hbpos : 0 < b := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hb)
      rw [havg b hbpos]
      have e1 := hB1 (b + 1) (by linarith)
      have e2 := hB1 b hb1
      rw [Real.dist_eq, sub_zero] at e1 e2
      have e3 := intervalIntegral.norm_integral_le_of_norm_le_const (a := b) (b := b + 1)
        (C := ε / 4) (f := fun s => R s * y s) fun x hx => by
          rw [uIoc_of_le (by linarith)] at hx
          have h := hB2 x (by linarith [hx.1])
          rw [Real.dist_eq, sub_zero] at h
          rw [Real.norm_eq_abs]
          exact h.le
      rw [Real.norm_eq_abs, show b + 1 - b = 1 by ring, abs_one, mul_one] at e3
      have := abs_lt.mp e1
      have := abs_lt.mp e2
      have := abs_le.mp e3
      rw [abs_le]
      constructor <;> linarith
    refine ⟨max (max B1 B2) 1 + 1, fun n hn => ?_⟩
    have hn1 : (1 : ℝ) ≤ max (max B1 B2) 1 := le_max_right _ _
    rw [Real.dist_eq, sub_zero, abs_lt]
    have h1 := key (n - 1) (by linarith)
    have h2 := key n (by linarith)
    have hb1 := hbound (n - 1) (by linarith)
    have hb2 := hbound n (by linarith)
    rw [sub_add_cancel] at hb1 h1
    have := abs_le.mp h1
    have := abs_le.mp h2
    constructor <;> linarith [hb1.1, hb2.2]
  have hWle : ∀ s : ℝ, 0 < s → W s ≤ y₀ := fun s hs =>
    ge_of_tendsto hW0 (by
      filter_upwards [Ioo_mem_nhdsGT hs] with t ht
      exact hanti t s ht.1 ht.2.le)
  -- tails `∫_a^∞ = W a`, then `a ↓ 0`
  have htail : ∀ a : ℝ, 0 < a →
      IntegrableOn (fun s => K s * g s) (Ioi a) ∧ ∫ s in Ioi a, K s * g s = W a := by
    intro a ha
    have hlim : Tendsto (fun i => W a - W i) atTop (𝓝 (W a)) := by
      simpa using tendsto_const_nhds.sub hWinf
    have hev : ∀ᶠ i in atTop, W a - W i = ∫ x in a..i, ‖K x * g x‖ := by
      filter_upwards [eventually_ge_atTop a] with i hi
      rw [← hFTC a i ha (ha.trans_le hi)]
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le hi] at hx
      exact (Real.norm_of_nonneg (hfnn x (ha.trans_le hx.1))).symm
    have hio : ∀ i : ℝ, IntegrableOn (fun s => K s * g s) (Ioc a i) := fun i =>
      ((hfc.mono fun x (hx : x ∈ Icc a i) => ha.trans_le hx.1).integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
    have hI := integrableOn_Ioi_of_intervalIntegral_norm_tendsto (W a) a hio tendsto_id
      (hlim.congr' hev)
    refine ⟨hI, tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi a hI tendsto_id) ?_⟩
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop a] with i hi
    exact (hFTC a i ha (ha.trans_le hi)).symm
  have hapos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hcover := aecover_Ioi_of_Ioi (μ := volume) (A := (0 : ℝ))
    (a := fun n : ℕ => 1 / ((n : ℝ) + 1)) tendsto_one_div_add_atTop_nhds_zero_nat
  have hrestr : ∀ n : ℕ, (volume.restrict (Ioi (0 : ℝ))).restrict (Ioi (1 / ((n : ℝ) + 1))) =
      volume.restrict (Ioi (1 / ((n : ℝ) + 1))) := fun n => by
    rw [Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, sup_of_le_left (hapos n).le]
  have hInt : IntegrableOn (fun s => K s * g s) (Ioi 0) := by
    refine hcover.integrable_of_integral_norm_bounded y₀ (fun n => ?_)
      (Eventually.of_forall fun n => ?_)
    · show Integrable _ ((volume.restrict (Ioi (0 : ℝ))).restrict _)
      rw [hrestr]
      exact (htail _ (hapos n)).1
    · show ∫ x, ‖K x * g x‖ ∂((volume.restrict (Ioi (0 : ℝ))).restrict _) ≤ y₀
      rw [hrestr, setIntegral_congr_fun measurableSet_Ioi
        (fun x hx => Real.norm_of_nonneg (hfnn x ((hapos n).trans hx))), (htail _ (hapos n)).2]
      exact hWle _ (hapos n)
  refine ⟨hInt, (hcover.integral_eq_of_tendsto y₀ hInt ?_).symm⟩
  have ha0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hapos⟩
  refine (hW0.comp ha0).congr fun n => ?_
  show W (1 / ((n : ℝ) + 1)) =
    ∫ x, K x * g x ∂((volume.restrict (Ioi (0 : ℝ))).restrict (Ioi (1 / ((n : ℝ) + 1))))
  rw [hrestr]
  exact (htail _ (hapos n)).2.symm

/-- `lem:plane-green` (g) helper (G4, polar representation of `𝔊 * w`): for `w ≥ 0` continuous on
`𝔻`, `(𝔊 * w)(p) = ∫₀^∞ 𝔊(s) 2π sinh s m_s(w)(p) ds`. -/
theorem s10_pgg_rep {w : ℂ → ℝ} (hw : ContinuousOn w unitDisc) (hw0 : ∀ z ∈ unitDisc, 0 ≤ w z)
    {p : ℂ} (hp : p ∈ unitDisc) :
    ∫⁻ q, ENNReal.ofReal (resolventG (diskDist p q) * w q) ∂diskHypArea =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (resolventG s * (2 * π * Real.sinh s) *
        circleMean (fun z => w (diskMob p z)) 0 s) := by
  have hp1 : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
  have hp' : ‖-p‖ < 1 := by rw [norm_neg]; exact hp1
  have hnp : -p ∈ unitDisc := mem_ball_zero_iff.mpr hp'
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hD : MeasurableSet unitDisc := measurableSet_ball
  classical
  obtain ⟨w', hw'⟩ : ∃ w' : ℂ → ℝ, w' = unitDisc.piecewise w 0 := ⟨_, rfl⟩
  have hw'm : Measurable w' := by
    rw [hw']
    exact hw.measurable_piecewise continuousOn_const hD
  have hw'e : ∀ z ∈ unitDisc, w' z = w z := fun z hz => by
    rw [hw']
    exact piecewise_eq_of_mem _ _ _ hz
  have hmobm : Measurable (diskMob p) := by
    rw [s10_prb_mob_eq, s05_blaschke_neg_eq]
    fun_prop
  have hdc : ContinuousOn (diskMob p) unitDisc := fun z hz => by
    rw [s10_prb_mob_eq]
    exact (hasDerivAt_blaschke hp' (mem_ball_zero_iff.mp hz)).continuousAt.continuousWithinAt
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ → ℝ≥0∞, ψ = fun z =>
      ENNReal.ofReal (resolventG (diskDist 0 z) * w' (diskMob p z)) := ⟨_, rfl⟩
  have hψm : Measurable ψ := by
    rw [hψ]
    exact ENNReal.measurable_ofReal.comp
      ((s10_prb_meas_G.comp s10_prb_meas_dist).mul (hw'm.comp hmobm))
  have hstep : ∫⁻ q, ENNReal.ofReal (resolventG (diskDist p q) * w q) ∂diskHypArea =
      ∫⁻ b, ψ (diskMob (-p) b) ∂diskHypArea := by
    refine lintegral_congr_ae ?_
    have hae : ∀ᵐ b ∂diskHypArea, b ∈ unitDisc := by
      show ∀ᵐ b ∂(volume.restrict unitDisc).withDensity
        (fun z => ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2)), b ∈ unitDisc
      exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_ball)
    filter_upwards [hae] with b hb
    have hz : diskMob (-p) b ∈ unitDisc := (s10_pr_mob hnp).1 hb
    have hbz : diskMob p (diskMob (-p) b) = b := by
      rw [s10_prb_mob_eq, s10_prb_mob_eq, neg_neg]
      exact blaschke_neg_blaschke hp1 (mem_ball_zero_iff.mp hb)
    have hd0 : diskMob p 0 = p := by simp [diskMob]
    have hdist : diskDist p b = diskDist 0 (diskMob (-p) b) := by
      have h := (s10_pr_mob hp).2 0 h0 _ hz
      rw [hd0, hbz] at h
      show Real.arcosh (diskCoshDist p b) = Real.arcosh (diskCoshDist 0 (diskMob (-p) b))
      rw [h]
    rw [hψ]
    beta_reduce
    rw [hbz, hw'e b hb, hdist]
  rw [hstep, s10_prb_area_mob hnp hψm, s10_prb_polar hψm]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have hs' : (0 : ℝ) < s := hs
  obtain ⟨t, ht⟩ : ∃ t, t = Real.tanh (s / 2) := ⟨_, rfl⟩
  have ht0 : 0 < t := by
    rw [ht, Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
  have ht1 : t < 1 := ht ▸ Real.tanh_lt_one _
  have hnorm : ∀ θ : ℝ, ‖(t : ℂ) * Complex.exp ((θ : ℂ) * I)‖ = t := fun θ => by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht0]
  have hmem : ∀ θ : ℝ, (t : ℂ) * Complex.exp ((θ : ℂ) * I) ∈ unitDisc := fun θ =>
    mem_ball_zero_iff.mpr (by rw [hnorm θ]; exact ht1)
  have hdd : ∀ θ : ℝ, diskDist 0 ((t : ℂ) * Complex.exp ((θ : ℂ) * I)) = s := fun θ => by
    show Real.arcosh (1 + 2 * ‖0 - (t : ℂ) * Complex.exp ((θ : ℂ) * I)‖ ^ 2 /
      ((1 - ‖(0 : ℂ)‖ ^ 2) * (1 - ‖(t : ℂ) * Complex.exp ((θ : ℂ) * I)‖ ^ 2))) = s
    rw [zero_sub, norm_neg, hnorm θ, norm_zero]
    have hc : 1 + 2 * t ^ 2 / ((1 - 0 ^ 2) * (1 - t ^ 2)) = Real.cosh s := by
      have h1t : 0 < 1 - t ^ 2 := by nlinarith
      rw [(s03_geo_cosh_tanh s).1, ← ht]
      field_simp
      ring
    rw [hc, Real.arcosh_cosh hs'.le]
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun θ : ℝ =>
      resolventG s * w (diskMob p ((t : ℂ) * Complex.exp ((θ : ℂ) * I))) := ⟨_, rfl⟩
  have hfc : Continuous f := by
    rw [hf]
    exact continuous_const.mul ((hw.comp hdc (s10_pr_mob hp).1).comp_continuous
      (by fun_prop) hmem)
  have hfn : ∀ θ, 0 ≤ f θ := fun θ => by
    rw [hf]
    exact mul_nonneg (s10_resolventG_pos hs').le (hw0 _ ((s10_pr_mob hp).1 (hmem θ)))
  have hE : ∀ θ : ℝ, Complex.exp (((θ + 2 * π : ℝ) : ℂ) * I) = Complex.exp ((θ : ℂ) * I) :=
    fun θ => by
      rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_ofNat,
        Complex.exp_two_pi_mul_I, mul_one]
  have hper : Function.Periodic f (2 * π) := fun θ => by
    rw [hf]
    beta_reduce
    rw [hE]
  have hin : ∫⁻ θ in Ioo (-π) π, ψ ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I)) =
      ENNReal.ofReal (∫ θ in (0 : ℝ)..(2 * π), f θ) := by
    rw [← ht]
    have h1 : ∫⁻ θ in Ioo (-π) π, ψ ((t : ℂ) * Complex.exp ((θ : ℂ) * I)) =
        ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (f θ) := by
      refine lintegral_congr (fun θ => ?_)
      rw [hψ, hf]
      beta_reduce
      rw [hdd θ, hw'e _ ((s10_pr_mob hp).1 (hmem θ))]
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal
      ((hfc.integrableOn_Icc).mono_set Ioo_subset_Icc_self) (Eventually.of_forall hfn)]
    congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le
      (by linarith [Real.pi_pos])]
    have hp := hper.intervalIntegral_add_eq (-π) 0
    rw [show -π + 2 * π = π by ring, zero_add] at hp
    exact hp
  have hm0 : ∀ z, diskMob 0 z = z := fun z => by
    show (z + 0) / (1 + conj 0 * z) = z
    simp
  have hmean : circleMean (fun z => w (diskMob p z)) 0 s =
      (2 * π)⁻¹ * ((resolventG s)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), f θ) := by
    unfold circleMean
    simp only [hm0]
    rw [← ht, hf, intervalIntegral.integral_const_mul,
      inv_mul_cancel_left₀ (s10_resolventG_pos hs').ne']
  rw [hin, hmean, ← ENNReal.ofReal_mul (Real.sinh_pos_iff.mpr hs').le]
  congr 1
  have := (s10_resolventG_pos hs').ne'
  have := Real.pi_pos
  field_simp

/-- `lem:plane-green` (g) helper: for `v ∈ C²(𝔻)`, `Δ_ρ v` is continuous on `𝔻`. -/
theorem s10_pgg_lap_cont {v : ℂ → ℝ} (hv : ContDiffOn ℝ 2 v unitDisc) :
    ContinuousOn (hypLaplacianDisk v) unitDisc := by
  exact ((by fun_prop : Continuous fun z : ℂ => ((1 - ‖z‖ ^ 2) / 2) ^ 2).continuousOn.mul
      (s10_pgg_laplacian_cont hv)).congr fun _ _ => rfl

/-- **Lemma 10.6 (g)**, `lem:plane-green`, `sec10-sharp.tex:160`, (10.5): a bounded `v ∈ C²(S)`
with `w = (2 - Δ)v ≥ 0` is `v = 𝔊 * w`. -/
theorem lem_plane_green_g (v : ℂ → ℝ) (hv : ContDiffOn ℝ 2 v unitDisc)
    (hvb : ∃ M : ℝ, ∀ z ∈ unitDisc, |v z| ≤ M)
    (hw : ∀ z ∈ unitDisc, 0 ≤ 2 * v z - hypLaplacianDisk v z) (p : ℂ) (hp : p ∈ unitDisc) :
    0 ≤ v p ∧ ENNReal.ofReal (v p) =
      ∫⁻ q, ENNReal.ofReal (resolventG (diskDist p q) * (2 * v q - hypLaplacianDisk v q))
        ∂diskHypArea := by
  obtain ⟨hu, hlap⟩ := s10_pgg_lap_mob hv hp
  obtain ⟨M', hd1, hd2, hgc, hl', hl⟩ := s10_pgg_mean_ode hu
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hd0 : diskMob p 0 = p := by simp [diskMob]
  have hz : ∀ s θ : ℝ,
      diskMob 0 ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I)) ∈ unitDisc := fun s θ =>
    (s10_pr_mob h0).1 (mem_ball_zero_iff.mpr (by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_tanh_lt_one _))
  have hW : ∀ s : ℝ, circleMean (fun z => 2 * v (diskMob p z) -
      hypLaplacianDisk (fun z => v (diskMob p z)) z) 0 s =
      circleMean (fun z => 2 * v (diskMob p z) - hypLaplacianDisk v (diskMob p z)) 0 s := by
    intro s
    unfold circleMean
    congr 1
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only
    rw [hlap _ (hz s θ)]
  have hgnn : ∀ s : ℝ, 0 < s → 0 ≤ circleMean (fun z => 2 * v (diskMob p z) -
      hypLaplacianDisk v (diskMob p z)) 0 s := by
    intro s _
    unfold circleMean
    refine mul_nonneg (inv_nonneg.mpr Real.two_pi_pos.le) ?_
    refine intervalIntegral.integral_nonneg Real.two_pi_pos.le (fun θ _ => ?_)
    exact hw _ ((s10_pr_mob hp).1 (hz s θ))
  have hbd : ∃ M : ℝ, ∀ s : ℝ, 0 < s → |circleMean (fun z => v (diskMob p z)) 0 s| ≤ M := by
    obtain ⟨M, hM⟩ := hvb
    refine ⟨M, fun s _ => ?_⟩
    unfold circleMean
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
      (C := M) (f := fun θ : ℝ => v (diskMob p (diskMob 0
        ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I)))))
      (fun θ _ => by rw [Real.norm_eq_abs]; exact hM _ ((s10_pr_mob hp).1 (hz s θ)))
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos Real.two_pi_pos] at hle
    rw [abs_mul, abs_of_pos (inv_pos.mpr Real.two_pi_pos)]
    calc (2 * π)⁻¹ * |∫ θ in (0 : ℝ)..(2 * π), v (diskMob p (diskMob 0
          ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I))))|
        ≤ (2 * π)⁻¹ * (M * (2 * π)) :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr Real.two_pi_pos.le)
      _ = M := by field_simp
  obtain ⟨hint, heq⟩ := s10_pgg_wronskian (y := fun s => circleMean (fun z => v (diskMob p z)) 0 s)
    (g := fun s => circleMean (fun z => 2 * v (diskMob p z) - hypLaplacianDisk v (diskMob p z)) 0 s)
    hd1 (fun s hs => by have := hd2 s hs; rwa [hW s] at this)
    (by simpa only [hW] using hgc) hgnn hbd hl hl'
  rw [hd0] at heq
  have hwc : ContinuousOn (fun z => 2 * v z - hypLaplacianDisk v z) unitDisc :=
    (continuousOn_const.mul hv.continuousOn).sub (s10_pgg_lap_cont hv)
  have hnn : 0 ≤ ∫ s in Ioi (0 : ℝ), resolventG s * (2 * π * Real.sinh s) *
      circleMean (fun z => 2 * v (diskMob p z) - hypLaplacianDisk v (diskMob p z)) 0 s := by
    refine setIntegral_nonneg measurableSet_Ioi (fun s hs => ?_)
    exact mul_nonneg (mul_pos (s10_resolventG_pos hs)
      (mul_pos Real.two_pi_pos (Real.sinh_pos_iff.mpr hs))).le (hgnn s hs)
  refine ⟨heq ▸ hnn, ?_⟩
  rw [s10_pgg_rep hwc hw hp, heq, ofReal_integral_eq_lintegral_ofReal hint]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact mul_nonneg (mul_pos (s10_resolventG_pos hs)
    (mul_pos Real.two_pi_pos (Real.sinh_pos_iff.mpr hs))).le (hgnn s hs)

/-! ## §10.3 The planar model -/

/-- `thm:plane-ratio` helper: a plane embedding preserves `cosh d`. -/
theorem s10_pr_cosh {ι : ℂ → ℂ × ℝ} (hι : IsPlaneEmbedding ι) :
    ∀ a ∈ unitDisc, ∀ b ∈ unitDisc, coshDist (ι a) (ι b) = diskCoshDist a b := by
  intro a ha b hb
  have h := congrArg Real.cosh (hι.2 a ha b hb)
  unfold hdist diskDist at h
  rwa [Real.cosh_arcosh (s09_one_le_coshDist _ _ (hι.1 ha) (hι.1 hb)),
    Real.cosh_arcosh (s10_one_le_diskCoshDist ha hb)] at h

/-- `thm:plane-ratio` helper: a Lorentz vector that is null and orthogonal to a unit timelike
vector is zero. -/
theorem s10_pr_null {d₀ d₁ d₂ d₃ t₀ t₁ t₂ t₃ : ℝ} (ht : t₀ ^ 2 - t₁ ^ 2 - t₂ ^ 2 - t₃ ^ 2 = 1)
    (ho : d₀ * t₀ - d₁ * t₁ - d₂ * t₂ - d₃ * t₃ = 0)
    (hn : d₀ * d₀ - d₁ * d₁ - d₂ * d₂ - d₃ * d₃ = 0) :
    d₀ = 0 ∧ d₁ = 0 ∧ d₂ = 0 ∧ d₃ = 0 := by
  have cs : (d₁ * t₁ + d₂ * t₂ + d₃ * t₃) ^ 2 ≤
      (d₁ ^ 2 + d₂ ^ 2 + d₃ ^ 2) * (t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2) := by
    nlinarith [sq_nonneg (d₁ * t₂ - d₂ * t₁), sq_nonneg (d₁ * t₃ - d₃ * t₁),
      sq_nonneg (d₂ * t₃ - d₃ * t₂)]
  have e1 : d₀ * t₀ = d₁ * t₁ + d₂ * t₂ + d₃ * t₃ := by linarith
  have e2 : t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2 = t₀ ^ 2 - 1 := by linarith
  have e3 : d₁ ^ 2 + d₂ ^ 2 + d₃ ^ 2 = d₀ ^ 2 := by linear_combination -hn
  have h0 : d₀ ^ 2 ≤ 0 := by
    have : (d₀ * t₀) ^ 2 ≤ d₀ ^ 2 * (t₀ ^ 2 - 1) := by rw [e1, ← e2, ← e3]; exact cs
    nlinarith
  have hd0 : d₀ = 0 := (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h0 (sq_nonneg _))
  have hs : d₁ ^ 2 + d₂ ^ 2 + d₃ ^ 2 = 0 := by rw [e3, hd0]; ring
  refine ⟨hd0, ?_, ?_, ?_⟩ <;> refine (pow_eq_zero_iff two_ne_zero).mp ?_ <;>
    nlinarith [sq_nonneg d₁, sq_nonneg d₂, sq_nonneg d₃]

/-- `thm:plane-ratio` helper (Gram rigidity, Lorentz coordinates): if `g = (g₀, …, g₃) : S → ℝ^{3,1}`
has the same Lorentz Gram matrix as `y = (y₀, y₁, y₂) : S → ℝ^{2,1}`, and `y` takes the values
`(1,0,0)`, `(5/3,4/3,0)`, `(5/3,0,4/3)` at three points of `S`, then every linear functional
`⟨v, g(·)⟩` is of the form `⟨u, y(·)⟩`. -/
theorem s10_pr_gram {S : Set ℂ} (g₀ g₁ g₂ g₃ y₀ y₁ y₂ : ℂ → ℝ) {b₀ b₁ b₂ : ℂ} (h₀ : b₀ ∈ S)
    (h₁ : b₁ ∈ S) (h₂ : b₂ ∈ S) (hy₀ : y₀ b₀ = 1 ∧ y₁ b₀ = 0 ∧ y₂ b₀ = 0)
    (hy₁ : y₀ b₁ = 5 / 3 ∧ y₁ b₁ = 4 / 3 ∧ y₂ b₁ = 0)
    (hy₂ : y₀ b₂ = 5 / 3 ∧ y₁ b₂ = 0 ∧ y₂ b₂ = 4 / 3)
    (hG : ∀ a ∈ S, ∀ b ∈ S, g₀ a * g₀ b - g₁ a * g₁ b - g₂ a * g₂ b - g₃ a * g₃ b =
      y₀ a * y₀ b - y₁ a * y₁ b - y₂ a * y₂ b) (v₀ v₁ v₂ v₃ : ℝ) :
    ∃ u₀ u₁ u₂ : ℝ, ∀ b ∈ S, v₀ * g₀ b - v₁ * g₁ b - v₂ * g₂ b - v₃ * g₃ b =
      u₀ * y₀ b - u₁ * y₁ b - u₂ * y₂ b := by
  obtain ⟨a00, a01, a02⟩ := hy₀
  obtain ⟨a10, a11, a12⟩ := hy₁
  obtain ⟨a20, a21, a22⟩ := hy₂
  have F00 := hG b₀ h₀ b₀ h₀
  have F01 := hG b₀ h₀ b₁ h₁
  have F02 := hG b₀ h₀ b₂ h₂
  have F10 := hG b₁ h₁ b₀ h₀
  have F11 := hG b₁ h₁ b₁ h₁
  have F12 := hG b₁ h₁ b₂ h₂
  have F20 := hG b₂ h₂ b₀ h₀
  have F21 := hG b₂ h₂ b₁ h₁
  have F22 := hG b₂ h₂ b₂ h₂
  simp only [a00, a01, a02, a10, a11, a12, a20, a21, a22] at F00 F01 F02 F10 F11 F12 F20 F21 F22
  refine ⟨v₀ * g₀ b₀ - v₁ * g₁ b₀ - v₂ * g₂ b₀ - v₃ * g₃ b₀,
    5 / 4 * (v₀ * g₀ b₀ - v₁ * g₁ b₀ - v₂ * g₂ b₀ - v₃ * g₃ b₀) -
      3 / 4 * (v₀ * g₀ b₁ - v₁ * g₁ b₁ - v₂ * g₂ b₁ - v₃ * g₃ b₁),
    5 / 4 * (v₀ * g₀ b₀ - v₁ * g₁ b₀ - v₂ * g₂ b₀ - v₃ * g₃ b₀) -
      3 / 4 * (v₀ * g₀ b₂ - v₁ * g₁ b₂ - v₂ * g₂ b₂ - v₃ * g₃ b₂), fun b hb => ?_⟩
  have E0 := hG b hb b₀ h₀
  have E1 := hG b hb b₁ h₁
  have E2 := hG b hb b₂ h₂
  have Eb := hG b hb b hb
  simp only [a00, a01, a02, a10, a11, a12, a20, a21, a22] at E0 E1 E2
  obtain ⟨d0, hd0⟩ : ∃ d, d = g₀ b - ((y₀ b - 5 / 4 * (y₁ b + y₂ b)) * g₀ b₀ +
      3 / 4 * y₁ b * g₀ b₁ + 3 / 4 * y₂ b * g₀ b₂) := ⟨_, rfl⟩
  obtain ⟨d1, hd1⟩ : ∃ d, d = g₁ b - ((y₀ b - 5 / 4 * (y₁ b + y₂ b)) * g₁ b₀ +
      3 / 4 * y₁ b * g₁ b₁ + 3 / 4 * y₂ b * g₁ b₂) := ⟨_, rfl⟩
  obtain ⟨d2, hd2⟩ : ∃ d, d = g₂ b - ((y₀ b - 5 / 4 * (y₁ b + y₂ b)) * g₂ b₀ +
      3 / 4 * y₁ b * g₂ b₁ + 3 / 4 * y₂ b * g₂ b₂) := ⟨_, rfl⟩
  obtain ⟨d3, hd3⟩ : ∃ d, d = g₃ b - ((y₀ b - 5 / 4 * (y₁ b + y₂ b)) * g₃ b₀ +
      3 / 4 * y₁ b * g₃ b₁ + 3 / 4 * y₂ b * g₃ b₂) := ⟨_, rfl⟩
  have o0 : d0 * g₀ b₀ - d1 * g₁ b₀ - d2 * g₂ b₀ - d3 * g₃ b₀ = 0 := by
    linear_combination E0 - (y₀ b - 5 / 4 * (y₁ b + y₂ b)) * F00 - 3 / 4 * y₁ b * F10 -
      3 / 4 * y₂ b * F20 + g₀ b₀ * hd0 - g₁ b₀ * hd1 - g₂ b₀ * hd2 - g₃ b₀ * hd3
  have o1 : d0 * g₀ b₁ - d1 * g₁ b₁ - d2 * g₂ b₁ - d3 * g₃ b₁ = 0 := by
    linear_combination E1 - (y₀ b - 5 / 4 * (y₁ b + y₂ b)) * F01 - 3 / 4 * y₁ b * F11 -
      3 / 4 * y₂ b * F21 + g₀ b₁ * hd0 - g₁ b₁ * hd1 - g₂ b₁ * hd2 - g₃ b₁ * hd3
  have o2 : d0 * g₀ b₂ - d1 * g₁ b₂ - d2 * g₂ b₂ - d3 * g₃ b₂ = 0 := by
    linear_combination E2 - (y₀ b - 5 / 4 * (y₁ b + y₂ b)) * F02 - 3 / 4 * y₁ b * F12 -
      3 / 4 * y₂ b * F22 + g₀ b₂ * hd0 - g₁ b₂ * hd1 - g₂ b₂ * hd2 - g₃ b₂ * hd3
  have ob : d0 * g₀ b - d1 * g₁ b - d2 * g₂ b - d3 * g₃ b = 0 := by
    linear_combination Eb - (y₀ b - 5 / 4 * (y₁ b + y₂ b)) * E0 - 3 / 4 * y₁ b * E1 -
      3 / 4 * y₂ b * E2 + g₀ b * hd0 - g₁ b * hd1 - g₂ b * hd2 - g₃ b * hd3
  have dd : d0 * d0 - d1 * d1 - d2 * d2 - d3 * d3 = 0 := by
    linear_combination ob - (y₀ b - 5 / 4 * (y₁ b + y₂ b)) * o0 - 3 / 4 * y₁ b * o1 -
      3 / 4 * y₂ b * o2 + d0 * hd0 - d1 * hd1 - d2 * hd2 - d3 * hd3
  obtain ⟨z0, z1, z2, z3⟩ := s10_pr_null (by linear_combination F00) o0 dd
  linear_combination v₀ * (z0 - hd0) - v₁ * (z1 - hd1) - v₂ * (z2 - hd2) - v₃ * (z3 - hd3)

/-- `thm:plane-ratio` helper (rigidity): for an isometric `G : 𝔻 → ℍ³` and `P ∈ ℍ³`,
`b ↦ cosh d(P, G b)` is a Lorentz-linear function of the hyperboloid point of `b`. -/
theorem s10_pr_rigid {G : ℂ → ℂ × ℝ} (hG : MapsTo G unitDisc UHS)
    (hiso : ∀ a ∈ unitDisc, ∀ b ∈ unitDisc, coshDist (G a) (G b) = diskCoshDist a b)
    (P : ℂ × ℝ) (hP : P ∈ UHS) :
    ∃ u₀ u₁ u₂ : ℝ, ∀ b ∈ unitDisc, coshDist P (G b) * (1 - ‖b‖ ^ 2) =
      u₀ * (1 + ‖b‖ ^ 2) - 2 * u₁ * b.re - 2 * u₂ * b.im := by
  have h2 : ∀ w : ℂ, ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := fun w => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hX : ∀ Q Q' : ℂ × ℝ, 0 < Q.2 → 0 < Q'.2 → coshDist Q Q' =
      (‖Q.1‖ ^ 2 + Q.2 ^ 2 + 1) / (2 * Q.2) * ((‖Q'.1‖ ^ 2 + Q'.2 ^ 2 + 1) / (2 * Q'.2)) -
      (‖Q.1‖ ^ 2 + Q.2 ^ 2 - 1) / (2 * Q.2) * ((‖Q'.1‖ ^ 2 + Q'.2 ^ 2 - 1) / (2 * Q'.2)) -
      Q.1.re / Q.2 * (Q'.1.re / Q'.2) - Q.1.im / Q.2 * (Q'.1.im / Q'.2) := by
    intro Q Q' hQ hQ'
    have hQ0 := hQ.ne'
    have hQ0' := hQ'.ne'
    unfold coshDist
    have h1 : ‖Q.1 - Q'.1‖ ^ 2 = (Q.1.re - Q'.1.re) ^ 2 + (Q.1.im - Q'.1.im) ^ 2 := by
      rw [h2, Complex.sub_re, Complex.sub_im]
    rw [h1, h2 Q.1, h2 Q'.1]
    field_simp
    ring
  have hY : ∀ a b : ℂ, ‖a‖ < 1 → ‖b‖ < 1 → diskCoshDist a b =
      (1 + ‖a‖ ^ 2) / (1 - ‖a‖ ^ 2) * ((1 + ‖b‖ ^ 2) / (1 - ‖b‖ ^ 2)) -
      2 * a.re / (1 - ‖a‖ ^ 2) * (2 * b.re / (1 - ‖b‖ ^ 2)) -
      2 * a.im / (1 - ‖a‖ ^ 2) * (2 * b.im / (1 - ‖b‖ ^ 2)) := by
    intro a b ha hb
    have ha2 : 1 - (a.re ^ 2 + a.im ^ 2) ≠ 0 := by
      rw [← h2]; nlinarith [norm_nonneg a]
    have hb2 : 1 - (b.re ^ 2 + b.im ^ 2) ≠ 0 := by
      rw [← h2]; nlinarith [norm_nonneg b]
    unfold diskCoshDist
    have h1 : ‖a - b‖ ^ 2 = (a.re - b.re) ^ 2 + (a.im - b.im) ^ 2 := by
      rw [h2, Complex.sub_re, Complex.sub_im]
    rw [h1, h2 a, h2 b]
    field_simp
    ring
  have hm0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hm1 : (1 / 2 : ℂ) ∈ unitDisc := mem_ball_zero_iff.mpr (by norm_num)
  have hm2 : (I / 2 : ℂ) ∈ unitDisc := mem_ball_zero_iff.mpr (by norm_num)
  obtain ⟨u₀, u₁, u₂, hu⟩ := s10_pr_gram (S := unitDisc)
    (fun b => (‖(G b).1‖ ^ 2 + (G b).2 ^ 2 + 1) / (2 * (G b).2))
    (fun b => (‖(G b).1‖ ^ 2 + (G b).2 ^ 2 - 1) / (2 * (G b).2))
    (fun b => (G b).1.re / (G b).2) (fun b => (G b).1.im / (G b).2)
    (fun b => (1 + ‖b‖ ^ 2) / (1 - ‖b‖ ^ 2)) (fun b => 2 * b.re / (1 - ‖b‖ ^ 2))
    (fun b => 2 * b.im / (1 - ‖b‖ ^ 2)) hm0 hm1 hm2 (by norm_num) (by norm_num) (by norm_num)
    (fun a ha b hb => by
      have h := hiso a ha b hb
      rw [hX _ _ (hG ha) (hG hb),
        hY a b (mem_ball_zero_iff.mp ha) (mem_ball_zero_iff.mp hb)] at h
      exact h)
    ((‖P.1‖ ^ 2 + P.2 ^ 2 + 1) / (2 * P.2)) ((‖P.1‖ ^ 2 + P.2 ^ 2 - 1) / (2 * P.2))
    (P.1.re / P.2) (P.1.im / P.2)
  refine ⟨u₀, u₁, u₂, fun b hb => ?_⟩
  have h := hu b hb
  beta_reduce at h
  have hb2 : 1 - ‖b‖ ^ 2 ≠ 0 := by
    have := mem_ball_zero_iff.mp hb
    nlinarith [norm_nonneg b]
  rw [hX P (G b) hP (hG hb), h]
  field_simp

/-- `thm:plane-ratio` helper: a Lorentz-linear function positive on `𝔻` has a future causal
coefficient vector. -/
theorem s10_pr_causal {f : ℂ → ℝ} {u₀ u₁ u₂ : ℝ} (hf : ∀ b ∈ unitDisc, 0 < f b)
    (hu : ∀ b ∈ unitDisc, f b * (1 - ‖b‖ ^ 2) =
      u₀ * (1 + ‖b‖ ^ 2) - 2 * u₁ * b.re - 2 * u₂ * b.im) :
    0 < u₀ ∧ u₁ ^ 2 + u₂ ^ 2 ≤ u₀ ^ 2 := by
  have hm0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have h0 := hu 0 hm0
  norm_num at h0
  have hu₀ : 0 < u₀ := by have := hf 0 hm0; linarith
  refine ⟨hu₀, ?_⟩
  by_contra hlt
  push Not at hlt
  have hS : 0 < u₁ ^ 2 + u₂ ^ 2 := by nlinarith
  obtain ⟨b, hbdef⟩ : ∃ b : ℂ, b = ((u₀ / (u₁ ^ 2 + u₂ ^ 2) : ℝ) : ℂ) * (u₁ + u₂ * I) :=
    ⟨_, rfl⟩
  have hre : b.re = u₀ / (u₁ ^ 2 + u₂ ^ 2) * u₁ := by rw [hbdef, Complex.re_ofReal_mul]; simp
  have him : b.im = u₀ / (u₁ ^ 2 + u₂ ^ 2) * u₂ := by rw [hbdef, Complex.im_ofReal_mul]; simp
  have hn : ‖b‖ ^ 2 = u₀ ^ 2 / (u₁ ^ 2 + u₂ ^ 2) := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    field_simp
  have hn1 : u₀ ^ 2 / (u₁ ^ 2 + u₂ ^ 2) < 1 := (div_lt_one hS).mpr hlt
  have hb : b ∈ unitDisc := mem_ball_zero_iff.mpr (by nlinarith [norm_nonneg b])
  have h1 := hu b hb
  have h2 := hf b hb
  rw [hn, hre, him] at h1
  have h3 : 0 < f b * (1 - u₀ ^ 2 / (u₁ ^ 2 + u₂ ^ 2)) := mul_pos h2 (by linarith)
  have h4 : u₀ * (1 + u₀ ^ 2 / (u₁ ^ 2 + u₂ ^ 2)) - 2 * u₁ * (u₀ / (u₁ ^ 2 + u₂ ^ 2) * u₁) -
      2 * u₂ * (u₀ / (u₁ ^ 2 + u₂ ^ 2) * u₂) = u₀ * (u₀ ^ 2 / (u₁ ^ 2 + u₂ ^ 2) - 1) := by
    field_simp
    ring
  have h5 : u₀ * (u₀ ^ 2 / (u₁ ^ 2 + u₂ ^ 2) - 1) < 0 :=
    mul_neg_of_pos_of_neg hu₀ (by linarith)
  linarith

/-- `thm:plane-ratio` helper (exact Poisson mean, from Mathlib's Poisson formula):
`∫₀^{2π} dθ/(A - p cos θ - q sin θ) = 2π/√(A² - p² - q²)`. -/
theorem s10_pr_poisson {A p q : ℝ} (hA : 0 < A) (h : p ^ 2 + q ^ 2 < A ^ 2) :
    ∫ θ in (0 : ℝ)..(2 * π), (A - p * Real.cos θ - q * Real.sin θ)⁻¹ =
      2 * π / √(A ^ 2 - p ^ 2 - q ^ 2) := by
  have hQ : 0 < A ^ 2 - p ^ 2 - q ^ 2 := by linarith
  obtain ⟨D, hD⟩ : ∃ D, D = √(A ^ 2 - p ^ 2 - q ^ 2) := ⟨_, rfl⟩
  rw [← hD]
  have hD0 : 0 < D := hD ▸ Real.sqrt_pos.mpr hQ
  have hD2 : D ^ 2 = A ^ 2 - p ^ 2 - q ^ 2 := hD ▸ Real.sq_sqrt hQ.le
  have hAD : 0 < A + D := by linarith
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (((A + D)⁻¹ : ℝ) : ℂ) * (p + q * I) := ⟨_, rfl⟩
  have hwre : w.re = p / (A + D) := by
    rw [hw, Complex.re_ofReal_mul]; simp [div_eq_inv_mul]
  have hwim : w.im = q / (A + D) := by
    rw [hw, Complex.im_ofReal_mul]; simp [div_eq_inv_mul]
  have hwn : ‖w‖ ^ 2 = (A - D) / (A + D) := by
    rw [Complex.sq_norm, Complex.normSq_apply, hwre, hwim, div_mul_div_comm, div_mul_div_comm,
      ← add_div, show p * p + q * q = (A - D) * (A + D) by linear_combination hD2,
      mul_div_mul_right _ _ hAD.ne']
  have hw1 : w ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    have : ‖w‖ ^ 2 < 1 := by rw [hwn, div_lt_one hAD]; linarith
    nlinarith [norm_nonneg w]
  have hker : ∀ θ : ℝ, poissonKernel 0 w (circleMap 0 1 θ) =
      D * (A - p * Real.cos θ - q * Real.sin θ)⁻¹ := by
    intro θ
    have hcs := Real.cos_sq_add_sin_sq θ
    have hden : 0 < A - p * Real.cos θ - q * Real.sin θ := by
      have h1 : (p * Real.cos θ + q * Real.sin θ) ^ 2 < A ^ 2 := by
        nlinarith [sq_nonneg (p * Real.sin θ - q * Real.cos θ)]
      have := (abs_lt.mp (abs_lt_of_sq_lt_sq h1 hA.le)).2
      linarith
    rw [poissonKernel_def, circleMap_zero]
    simp only [sub_zero, Complex.ofReal_one, one_mul]
    rw [Complex.norm_exp_ofReal_mul_I, hwn]
    have e : ‖Complex.exp (θ * I) - w‖ ^ 2 =
        ((Real.cos θ * (A + D) - p) ^ 2 + (Real.sin θ * (A + D) - q) ^ 2) / (A + D) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, hwre, hwim]
      field_simp
    have e2 : (Real.cos θ * (A + D) - p) ^ 2 + (Real.sin θ * (A + D) - q) ^ 2 =
        2 * (A - p * Real.cos θ - q * Real.sin θ) * (A + D) := by
      linear_combination (A + D) ^ 2 * hcs + hD2
    rw [e, e2]
    field_simp
    ring
  have hP := DiffContOnCl.circleAverage_poissonKernel_smul (f := fun _ : ℂ => (1 : ℂ))
    (c := 0) (R := 1) diffContOnCl_const hw1
  rw [Real.circleAverage_def] at hP
  have hint : ∫ θ in (0 : ℝ)..(2 * π),
      (poissonKernel 0 w • fun _ : ℂ => (1 : ℂ)) (circleMap 0 1 θ) =
      ((∫ θ in (0 : ℝ)..(2 * π), D * (A - p * Real.cos θ - q * Real.sin θ)⁻¹ : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [Pi.smul_apply', Complex.real_smul, mul_one, hker θ]
  rw [hint, Complex.real_smul, ← Complex.ofReal_mul, Complex.ofReal_eq_one,
    intervalIntegral.integral_const_mul] at hP
  have := Real.pi_pos
  rw [eq_div_iff hD0.ne']
  field_simp at hP
  simp only [one_div] at hP
  rw [mul_comm]
  exact hP

/-- `thm:plane-ratio` helper: the final inequalities, with `t = tanh(r/2)` and the circle mean
`2(1-t²)/√(A² - p² - q²)`. -/
theorem s10_pr_ineq {t u₀ u₁ u₂ : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hu₀ : 0 < u₀)
    (hus : u₁ ^ 2 + u₂ ^ 2 ≤ u₀ ^ 2) :
    2 / (1 + u₀) / ((1 + t ^ 2) / (1 - t ^ 2)) <
        2 * (1 - t ^ 2) / √((1 - t ^ 2 + u₀ * (1 + t ^ 2)) ^ 2 - (2 * t * u₁) ^ 2 -
          (2 * t * u₂) ^ 2) ∧
      2 * (1 - t ^ 2) / √((1 - t ^ 2 + u₀ * (1 + t ^ 2)) ^ 2 - (2 * t * u₁) ^ 2 -
          (2 * t * u₂) ^ 2) < 2 / (1 + u₀) ∧
      (2 * t * u₁) ^ 2 + (2 * t * u₂) ^ 2 < (1 - t ^ 2 + u₀ * (1 + t ^ 2)) ^ 2 ∧
      0 < 1 - t ^ 2 + u₀ * (1 + t ^ 2) := by
  have h1t : 0 < 1 - t ^ 2 := by nlinarith
  have h1u : 0 < 1 + u₀ := by linarith
  have h1t2 : 0 < 1 + t ^ 2 := by positivity
  have hA : 0 < 1 - t ^ 2 + u₀ * (1 + t ^ 2) := by
    have : 0 < u₀ * (1 + t ^ 2) := by positivity
    linarith
  have hA2 : 2 * t * u₀ < 1 - t ^ 2 + u₀ * (1 + t ^ 2) := by
    nlinarith [mul_nonneg hu₀.le (sq_nonneg (1 - t))]
  have hpq : (2 * t * u₁) ^ 2 + (2 * t * u₂) ^ 2 < (1 - t ^ 2 + u₀ * (1 + t ^ 2)) ^ 2 := by
    have h1 : (2 * t * u₁) ^ 2 + (2 * t * u₂) ^ 2 ≤ (2 * t * u₀) ^ 2 := by
      have : 0 ≤ 4 * t ^ 2 * (u₀ ^ 2 - u₁ ^ 2 - u₂ ^ 2) := mul_nonneg (by positivity) (by linarith)
      nlinarith
    have h2 : (2 * t * u₀) ^ 2 < (1 - t ^ 2 + u₀ * (1 + t ^ 2)) ^ 2 := by
      have : 0 ≤ 2 * t * u₀ := by positivity
      nlinarith
    linarith
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (1 - t ^ 2 + u₀ * (1 + t ^ 2)) ^ 2 - (2 * t * u₁) ^ 2 -
      (2 * t * u₂) ^ 2 := ⟨_, rfl⟩
  rw [← hQ]
  have hQ0 : 0 < Q := by rw [hQ]; linarith
  have hsq : 0 < √Q := Real.sqrt_pos.mpr hQ0
  have hsA : √Q ≤ 1 - t ^ 2 + u₀ * (1 + t ^ 2) :=
    (Real.sqrt_le_sqrt (show Q ≤ (1 - t ^ 2 + u₀ * (1 + t ^ 2)) ^ 2 by
      rw [hQ]; nlinarith [sq_nonneg (2 * t * u₁), sq_nonneg (2 * t * u₂)])).trans_eq
      (Real.sqrt_sq hA.le)
  have hlow' : (1 - t ^ 2) * (1 + u₀) < √Q := by
    rw [Real.lt_sqrt (mul_nonneg h1t.le h1u.le)]
    have e : Q - ((1 - t ^ 2) * (1 + u₀)) ^ 2 =
        4 * t ^ 2 * (u₀ ^ 2 - u₁ ^ 2 - u₂ ^ 2) + 4 * t ^ 2 * u₀ * (1 - t ^ 2) := by
      rw [hQ]; ring
    have : 0 < 4 * t ^ 2 * u₀ * (1 - t ^ 2) := mul_pos (by positivity) h1t
    have : 0 ≤ 4 * t ^ 2 * (u₀ ^ 2 - u₁ ^ 2 - u₂ ^ 2) := mul_nonneg (by positivity) (by linarith)
    linarith
  refine ⟨?_, ?_, hpq, hA⟩
  · rw [show 2 / (1 + u₀) / ((1 + t ^ 2) / (1 - t ^ 2)) =
        2 * (1 - t ^ 2) / ((1 + u₀) * (1 + t ^ 2)) by field_simp]
    refine div_lt_div_of_pos_left (mul_pos two_pos h1t) hsq ?_
    nlinarith
  · rw [div_lt_div_iff₀ hsq h1u]
    nlinarith

/-- **Theorem 10.7 (a)**, `thm:plane-ratio`, `sec10-sharp.tex:283`, (10.6): for a totally geodesic
plane `Π`, `P ∈ ℍ³`, `q ∈ Π` and `r > 0`, `κ_Π(q)/cosh r < m_r(q) < κ_Π(q)`. -/
theorem thm_plane_ratio_a (ι : ℂ → ℂ × ℝ) (hι : IsPlaneEmbedding ι) (P : ℂ × ℝ) (hP : P ∈ UHS)
    (a : ℂ) (ha : a ∈ unitDisc) (r : ℝ) (hr : 0 < r) :
    ambKernel P (ι a) / Real.cosh r < circleMean (fun b => ambKernel P (ι b)) a r ∧
      circleMean (fun b => ambKernel P (ι b)) a r < ambKernel P (ι a) := by
  obtain ⟨hmap, hmob⟩ := s10_pr_mob ha
  have hiso := s10_pr_cosh hι
  have hG : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      coshDist (ι (diskMob a z)) (ι (diskMob a w)) = diskCoshDist z w := fun z hz w hw => by
    rw [hiso _ (hmap hz) _ (hmap hw), hmob z hz w hw]
  have hUHS : ∀ b ∈ unitDisc, ι (diskMob a b) ∈ UHS := fun b hb => hι.1 (hmap hb)
  obtain ⟨u₀, u₁, u₂, hu⟩ := s10_pr_rigid (G := fun b => ι (diskMob a b)) hUHS hG P hP
  have hone : ∀ b ∈ unitDisc, 1 ≤ coshDist P (ι (diskMob a b)) := fun b hb =>
    s09_one_le_coshDist P _ hP (hUHS b hb)
  obtain ⟨hu₀, hus⟩ := s10_pr_causal (f := fun b => coshDist P (ι (diskMob a b)))
    (fun b hb => by have := hone b hb; linarith) hu
  set t := Real.tanh (r / 2) with ht
  have ht0 : 0 < t := by
    rw [ht, Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
  have ht1 : t < 1 := Real.tanh_lt_one _
  have h1t : 0 < 1 - t ^ 2 := by nlinarith
  obtain ⟨hlow, hup, hpq, hA⟩ := s10_pr_ineq ht0 ht1 hu₀ hus
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hd0 : diskMob a 0 = a := by simp [diskMob]
  have hc : ambKernel P (ι a) = 2 / (1 + u₀) := by
    have h := hu 0 h0
    simp only [hd0, norm_zero, Complex.zero_re, Complex.zero_im] at h
    rw [s09_ambKernel_eq_inv P _ (s09_one_le_coshDist P _ hP (hι.1 ha))]
    congr 2
    linarith
  have hk : ∀ θ : ℝ, ambKernel P (ι (diskMob a ((t : ℂ) * Complex.exp ((θ : ℂ) * I)))) =
      2 * (1 - t ^ 2) * (1 - t ^ 2 + u₀ * (1 + t ^ 2) - 2 * t * u₁ * Real.cos θ -
        2 * t * u₂ * Real.sin θ)⁻¹ := by
    intro θ
    set b : ℂ := (t : ℂ) * Complex.exp ((θ : ℂ) * I) with hbdef
    have hbn : ‖b‖ = t := by
      rw [hbdef, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos ht0]
    have hbre : b.re = t * Real.cos θ := by
      rw [hbdef, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    have hbim : b.im = t * Real.sin θ := by
      rw [hbdef, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
    have hb : b ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hbn]; exact ht1)
    have hf := hu b hb
    simp only [hbn, hbre, hbim] at hf
    have hcd := hone b hb
    rw [s09_ambKernel_eq_inv P _ hcd]
    rw [show 1 - t ^ 2 + u₀ * (1 + t ^ 2) - 2 * t * u₁ * Real.cos θ - 2 * t * u₂ * Real.sin θ =
        (1 - t ^ 2) * (1 + coshDist P (ι (diskMob a b))) by linear_combination -hf]
    have : 0 < 1 + coshDist P (ι (diskMob a b)) := by linarith
    field_simp
  have hmean : circleMean (fun b => ambKernel P (ι b)) a r =
      2 * (1 - t ^ 2) / √((1 - t ^ 2 + u₀ * (1 + t ^ 2)) ^ 2 - (2 * t * u₁) ^ 2 -
        (2 * t * u₂) ^ 2) := by
    show (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
      ambKernel P (ι (diskMob a ((t : ℂ) * Complex.exp ((θ : ℂ) * I)))) = _
    rw [intervalIntegral.integral_congr (fun θ _ => hk θ), intervalIntegral.integral_const_mul]
    have hP' := s10_pr_poisson (p := 2 * t * u₁) (q := 2 * t * u₂) hA hpq
    rw [hP']
    have := Real.pi_pos
    field_simp
  rw [hmean, hc, (s03_geo_cosh_tanh r).1]
  exact ⟨hlow, hup⟩

/-- `thm:plane-ratio` (b) helper: in the coordinate `z ↦ diskMob a z`, `κ_Π` is
`2(1-|z|²)/(1-|z|² + u₀(1+|z|²) - 2u₁ Re z - 2u₂ Im z)` with positive denominator on `𝔻`. -/
theorem s10_prb_kernel {ι : ℂ → ℂ × ℝ} (hι : IsPlaneEmbedding ι) {P : ℂ × ℝ} (hP : P ∈ UHS)
    {a : ℂ} (ha : a ∈ unitDisc) :
    ∃ u₀ u₁ u₂ : ℝ, 0 < u₀ ∧ u₁ ^ 2 + u₂ ^ 2 ≤ u₀ ^ 2 ∧ ∀ z ∈ unitDisc,
      0 < 1 - ‖z‖ ^ 2 + u₀ * (1 + ‖z‖ ^ 2) - 2 * u₁ * z.re - 2 * u₂ * z.im ∧
      ambKernel P (ι (diskMob a z)) = 2 * (1 - ‖z‖ ^ 2) /
        (1 - ‖z‖ ^ 2 + u₀ * (1 + ‖z‖ ^ 2) - 2 * u₁ * z.re - 2 * u₂ * z.im) := by
  obtain ⟨hmap, hmob⟩ := s10_pr_mob ha
  have hiso := s10_pr_cosh hι
  have hG : ∀ z ∈ unitDisc, ∀ w ∈ unitDisc,
      coshDist (ι (diskMob a z)) (ι (diskMob a w)) = diskCoshDist z w := fun z hz w hw => by
    rw [hiso _ (hmap hz) _ (hmap hw), hmob z hz w hw]
  have hUHS : ∀ b ∈ unitDisc, ι (diskMob a b) ∈ UHS := fun b hb => hι.1 (hmap hb)
  obtain ⟨u₀, u₁, u₂, hu⟩ := s10_pr_rigid (G := fun b => ι (diskMob a b)) hUHS hG P hP
  have hone : ∀ b ∈ unitDisc, 1 ≤ coshDist P (ι (diskMob a b)) := fun b hb =>
    s09_one_le_coshDist P _ hP (hUHS b hb)
  obtain ⟨hu₀, hus⟩ := s10_pr_causal (f := fun b => coshDist P (ι (diskMob a b)))
    (fun b hb => by have := hone b hb; linarith) hu
  refine ⟨u₀, u₁, u₂, hu₀, hus, fun z hz => ?_⟩
  have hf := hu z hz
  have hcd := hone z hz
  have h1z : 0 < 1 - ‖z‖ ^ 2 := by
    have := mem_ball_zero_iff.mp hz
    nlinarith [norm_nonneg z]
  have hD : 1 - ‖z‖ ^ 2 + u₀ * (1 + ‖z‖ ^ 2) - 2 * u₁ * z.re - 2 * u₂ * z.im =
      (1 - ‖z‖ ^ 2) * (1 + coshDist P (ι (diskMob a z))) := by
    linear_combination -hf
  have hpos : 0 < (1 - ‖z‖ ^ 2) * (1 + coshDist P (ι (diskMob a z))) :=
    mul_pos h1z (by linarith)
  refine ⟨hD ▸ hpos, ?_⟩
  rw [s09_ambKernel_eq_inv P _ hcd, hD]
  have : 0 < 1 + coshDist P (ι (diskMob a z)) := by linarith
  field_simp

/-- `thm:plane-ratio` (b) helper: the circle mean `s ↦ m_s(a)` of `κ_Π` is continuous. -/
theorem s10_prb_mean_cont {ι : ℂ → ℂ × ℝ} (hι : IsPlaneEmbedding ι) {P : ℂ × ℝ} (hP : P ∈ UHS)
    {a : ℂ} (ha : a ∈ unitDisc) :
    Continuous fun s => circleMean (fun b => ambKernel P (ι b)) a s := by
  obtain ⟨u₀, u₁, u₂, -, -, hk⟩ := s10_prb_kernel hι hP ha
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ × ℝ → ℂ, Z = fun p =>
      (Real.tanh (p.1 / 2) : ℂ) * Complex.exp ((p.2 : ℂ) * I) := ⟨_, rfl⟩
  have hZc : Continuous Z := by
    rw [hZ]
    have := s10_prb_continuous_tanh
    fun_prop
  have hZd : ∀ p, Z p ∈ unitDisc := fun p => by
    rw [hZ]
    show (Real.tanh (p.1 / 2) : ℂ) * Complex.exp ((p.2 : ℂ) * I) ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    exact Real.abs_tanh_lt_one _
  have hcont : Continuous fun p : ℝ × ℝ => 2 * (1 - ‖Z p‖ ^ 2) /
      (1 - ‖Z p‖ ^ 2 + u₀ * (1 + ‖Z p‖ ^ 2) - 2 * u₁ * (Z p).re - 2 * u₂ * (Z p).im) := by
    refine Continuous.div (by fun_prop) (by fun_prop) (fun p => (hk _ (hZd p)).1.ne')
  have heq : (fun s => circleMean (fun b => ambKernel P (ι b)) a s) = fun s =>
      (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), 2 * (1 - ‖Z (s, θ)‖ ^ 2) /
        (1 - ‖Z (s, θ)‖ ^ 2 + u₀ * (1 + ‖Z (s, θ)‖ ^ 2) - 2 * u₁ * (Z (s, θ)).re -
          2 * u₂ * (Z (s, θ)).im) := by
    funext s
    show (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
      ambKernel P (ι (diskMob a ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I)))) = _
    congr 1
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    have h := (hk _ (hZd (s, θ))).2
    rw [hZ] at h
    simp only at h
    rw [h, hZ]
  rw [heq]
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont _ _)

/-- `thm:plane-ratio` (b) helper (polar representation of `𝔊 * κ_Π`):
`(𝔊 * κ_Π)(a) = ∫₀^∞ 𝔊(s) 2π sinh s m_s(a) ds`. -/
theorem s10_prb_rep {ι : ℂ → ℂ × ℝ} (hι : IsPlaneEmbedding ι) {P : ℂ × ℝ} (hP : P ∈ UHS)
    {a : ℂ} (ha : a ∈ unitDisc) :
    resolventConvDisk (fun b => ambKernel P (ι b)) a =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (resolventG s * (2 * π * Real.sinh s) *
        circleMean (fun b => ambKernel P (ι b)) a s) := by
  obtain ⟨u₀, u₁, u₂, -, -, hk⟩ := s10_prb_kernel hι hP ha
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have hna : -a ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [norm_neg]; exact ha1)
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  obtain ⟨Kf, hKf⟩ : ∃ Kf : ℂ → ℝ, Kf = fun z => 2 * (1 - ‖z‖ ^ 2) /
      (1 - ‖z‖ ^ 2 + u₀ * (1 + ‖z‖ ^ 2) - 2 * u₁ * z.re - 2 * u₂ * z.im) := ⟨_, rfl⟩
  have hKm : Measurable Kf := by rw [hKf]; fun_prop
  have hKe : ∀ z ∈ unitDisc, ambKernel P (ι (diskMob a z)) = Kf z := fun z hz => by
    rw [hKf]; exact (hk z hz).2
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ → ℝ≥0∞, ψ = fun z =>
      ENNReal.ofReal (resolventG (diskDist 0 z) * Kf z) := ⟨_, rfl⟩
  have hψm : Measurable ψ := by
    rw [hψ]
    have := s10_prb_meas_G.comp s10_prb_meas_dist
    exact ENNReal.measurable_ofReal.comp (this.mul hKm)
  have hstep : resolventConvDisk (fun b => ambKernel P (ι b)) a =
      ∫⁻ b, ψ (diskMob (-a) b) ∂diskHypArea := by
    show ∫⁻ b, ENNReal.ofReal (resolventG (diskDist a b) * ambKernel P (ι b)) ∂diskHypArea = _
    refine lintegral_congr_ae ?_
    have hae : ∀ᵐ b ∂diskHypArea, b ∈ unitDisc := by
      show ∀ᵐ b ∂(volume.restrict unitDisc).withDensity
        (fun z => ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2)), b ∈ unitDisc
      exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_ball)
    filter_upwards [hae] with b hb
    have hz : diskMob (-a) b ∈ unitDisc := (s10_pr_mob hna).1 hb
    have hbz : diskMob a (diskMob (-a) b) = b := by
      rw [s10_prb_mob_eq, s10_prb_mob_eq, neg_neg]
      exact blaschke_neg_blaschke ha1 (mem_ball_zero_iff.mp hb)
    have hd0 : diskMob a 0 = a := by simp [diskMob]
    have hdist : diskDist a b = diskDist 0 (diskMob (-a) b) := by
      have h := (s10_pr_mob ha).2 0 h0 _ hz
      rw [hd0, hbz] at h
      show Real.arcosh (diskCoshDist a b) = Real.arcosh (diskCoshDist 0 (diskMob (-a) b))
      rw [h]
    rw [hψ]
    beta_reduce
    rw [hdist, ← hKe _ hz, hbz]
  rw [hstep, s10_prb_area_mob hna hψm, s10_prb_polar hψm]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have hs' : (0 : ℝ) < s := hs
  obtain ⟨t, ht⟩ : ∃ t, t = Real.tanh (s / 2) := ⟨_, rfl⟩
  have ht0 : 0 < t := by
    rw [ht, Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
  have ht1 : t < 1 := ht ▸ Real.tanh_lt_one _
  have h1t : 0 < 1 - t ^ 2 := by nlinarith
  have hnorm : ∀ θ : ℝ, ‖(t : ℂ) * Complex.exp ((θ : ℂ) * I)‖ = t := fun θ => by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht0]
  have hmem : ∀ θ : ℝ, (t : ℂ) * Complex.exp ((θ : ℂ) * I) ∈ unitDisc := fun θ =>
    mem_ball_zero_iff.mpr (by rw [hnorm θ]; exact ht1)
  have hdd : ∀ θ : ℝ, diskDist 0 ((t : ℂ) * Complex.exp ((θ : ℂ) * I)) = s := fun θ => by
    show Real.arcosh (1 + 2 * ‖0 - (t : ℂ) * Complex.exp ((θ : ℂ) * I)‖ ^ 2 /
      ((1 - ‖(0 : ℂ)‖ ^ 2) * (1 - ‖(t : ℂ) * Complex.exp ((θ : ℂ) * I)‖ ^ 2))) = s
    rw [zero_sub, norm_neg, hnorm θ, norm_zero]
    have hc : 1 + 2 * t ^ 2 / ((1 - 0 ^ 2) * (1 - t ^ 2)) = Real.cosh s := by
      rw [(s03_geo_cosh_tanh s).1, ← ht]
      field_simp
      ring
    rw [hc, Real.arcosh_cosh hs'.le]
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun θ : ℝ => resolventG s * Kf ((t : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
    ⟨_, rfl⟩
  have hfc : Continuous f := by
    rw [hf, hKf]
    refine continuous_const.mul (Continuous.div (by fun_prop) (by fun_prop) (fun θ => ?_))
    exact (hk _ (hmem θ)).1.ne'
  have hfn : ∀ θ, 0 ≤ f θ := fun θ => by
    rw [hf]
    refine mul_nonneg (s10_resolventG_pos hs').le ?_
    have h := (hk _ (hmem θ)).1
    rw [hKf]
    beta_reduce
    rw [hnorm θ] at h ⊢
    exact div_nonneg (by linarith) h.le
  have hper : Function.Periodic f (2 * π) := fun θ => by
    rw [hf]
    simp only
    congr 3
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.exp_two_pi_mul_I, mul_one]
  have hin : ∫⁻ θ in Ioo (-π) π, ψ ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I)) =
      ENNReal.ofReal (∫ θ in (0 : ℝ)..(2 * π), f θ) := by
    rw [← ht]
    have h1 : ∫⁻ θ in Ioo (-π) π, ψ ((t : ℂ) * Complex.exp ((θ : ℂ) * I)) =
        ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (f θ) := by
      refine lintegral_congr (fun θ => ?_)
      rw [hψ, hf]
      simp only
      rw [hdd θ]
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal
      ((hfc.integrableOn_Icc).mono_set Ioo_subset_Icc_self) (Eventually.of_forall hfn)]
    congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le
      (by linarith [Real.pi_pos])]
    have hp := hper.intervalIntegral_add_eq (-π) 0
    rw [show -π + 2 * π = π by ring, zero_add] at hp
    exact hp
  have hmean : circleMean (fun b => ambKernel P (ι b)) a s =
      (2 * π)⁻¹ * ((resolventG s)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), f θ) := by
    show (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
      ambKernel P (ι (diskMob a ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I)))) = _
    rw [← ht, hf, intervalIntegral.integral_const_mul,
      inv_mul_cancel_left₀ (s10_resolventG_pos hs').ne']
    congr 1
    exact intervalIntegral.integral_congr (fun θ _ => hKe _ (hmem θ))
  rw [hin, hmean, ← ENNReal.ofReal_mul (Real.sinh_pos_iff.mpr hs').le]
  congr 1
  have := (s10_resolventG_pos hs').ne'
  have := Real.pi_pos
  field_simp

/-- `thm:plane-ratio` (b) helper: if `κ/cosh s < m(s) < κ` for `s > 0`, then
`(1 - log 2) κ < ∫₀^∞ 𝔊(s) 2π sinh s m(s) ds < κ/2` (by `lem_plane_green_f`). -/
theorem s10_prb_cmp {m : ℝ → ℝ} (hm : Continuous m) {κ : ℝ} (hκ : 0 < κ)
    (h : ∀ s : ℝ, 0 < s → κ / Real.cosh s < m s ∧ m s < κ) :
    ENNReal.ofReal ((1 - Real.log 2) * κ) <
        ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (resolventG s * (2 * π * Real.sinh s) * m s) ∧
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (resolventG s * (2 * π * Real.sinh s) * m s) <
        ENNReal.ofReal (κ / 2) := by
  obtain ⟨hi1, hv1, hi2, hv2, -, -⟩ := lem_plane_green_f
  have hμ : volume.restrict (Ioi (0 : ℝ)) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioi]
    exact ENNReal.top_ne_zero
  have hw : ∀ s : ℝ, 0 < s → 0 < resolventG s * (2 * π * Real.sinh s) := fun s hs =>
    mul_pos (s10_resolventG_pos hs) (mul_pos Real.two_pi_pos (Real.sinh_pos_iff.mpr hs))
  have hmeas : Measurable fun s => ENNReal.ofReal (resolventG s * (2 * π * Real.sinh s) * m s) := by
    have := s10_prb_meas_G
    have := hm.measurable
    fun_prop
  have hup : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (resolventG s * (2 * π * Real.sinh s) * κ) =
      ENNReal.ofReal (κ / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hi1.mul_const κ), integral_mul_const, hv1]
    · ring_nf
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact (mul_pos (hw s hs) hκ).le
  have hlow : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (resolventG s * (2 * π * Real.tanh s) * κ) =
      ENNReal.ofReal ((1 - Real.log 2) * κ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hi2.mul_const κ), integral_mul_const, hv2]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : (0 : ℝ) < s := hs
    have : 0 < Real.tanh s := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr hs') (Real.cosh_pos _)
    exact (mul_pos (mul_pos (s10_resolventG_pos hs') (mul_pos Real.two_pi_pos this)) hκ).le
  constructor
  · rw [← hlow]
    refine lintegral_strict_mono hμ hmeas.aemeasurable (by rw [hlow]; exact ENNReal.ofReal_ne_top) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : (0 : ℝ) < s := hs
    have hc := Real.cosh_pos s
    have h1 := (h s hs').1
    have hpos : 0 < resolventG s * (2 * π * Real.sinh s) * m s :=
      mul_pos (hw s hs') (lt_trans (div_pos hκ hc) h1)
    rw [ENNReal.ofReal_lt_ofReal_iff hpos, Real.tanh_eq_sinh_div_cosh,
      show resolventG s * (2 * π * (Real.sinh s / Real.cosh s)) * κ =
        resolventG s * (2 * π * Real.sinh s) * (κ / Real.cosh s) by field_simp]
    exact mul_lt_mul_of_pos_left h1 (hw s hs')
  · rw [← hup]
    have hm2 : Measurable fun s => ENNReal.ofReal (resolventG s * (2 * π * Real.sinh s) * κ) := by
      have := s10_prb_meas_G
      fun_prop
    refine lintegral_strict_mono hμ hm2.aemeasurable ?_ ?_
    · refine ne_top_of_le_ne_top (b := ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (resolventG s * (2 * π * Real.sinh s) * κ)) (by rw [hup]; exact
          ENNReal.ofReal_ne_top) ?_
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (h s hs).2.le (hw s hs).le)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      rw [ENNReal.ofReal_lt_ofReal_iff (mul_pos (hw s hs) hκ)]
      exact mul_lt_mul_of_pos_left (h s hs).2 (hw s hs)

/-- **Theorem 10.7 (b)**, `thm:plane-ratio`, `sec10-sharp.tex:290`: on `Π`,
`(1 - log 2) κ_Π < 𝔊 * κ_Π < ½ κ_Π`. -/
theorem thm_plane_ratio_b (ι : ℂ → ℂ × ℝ) (hι : IsPlaneEmbedding ι) (P : ℂ × ℝ) (hP : P ∈ UHS)
    (a : ℂ) (ha : a ∈ unitDisc) :
    ENNReal.ofReal ((1 - Real.log 2) * ambKernel P (ι a)) <
        resolventConvDisk (fun b => ambKernel P (ι b)) a ∧
      resolventConvDisk (fun b => ambKernel P (ι b)) a <
        ENNReal.ofReal (ambKernel P (ι a) / 2) := by
  have hκ : 0 < ambKernel P (ι a) := by
    unfold ambKernel
    have := Real.cosh_pos (hdist P (ι a) / 2)
    positivity
  rw [s10_prb_rep hι hP ha]
  exact s10_prb_cmp (s10_prb_mean_cont hι hP ha) hκ
    (fun s hs => thm_plane_ratio_a ι hι P hP a ha s hs)

/-- `thm:plane-ratio` (c) helper: by (b), every ratio `(𝔊 * κ_Π)(q)/κ_Π(q)` lies strictly between
`1 - log 2` and `1/2`. -/
theorem s10_prc_bounds {ι : ℂ → ℂ × ℝ} (hι : IsPlaneEmbedding ι) {P : ℂ × ℝ} (hP : P ∈ UHS)
    {a : ℂ} (ha : a ∈ unitDisc) :
    1 - Real.log 2 < (resolventConvDisk (fun b => ambKernel P (ι b)) a).toReal / ambKernel P (ι a) ∧
      (resolventConvDisk (fun b => ambKernel P (ι b)) a).toReal / ambKernel P (ι a) < 1 / 2 := by
  obtain ⟨hlo, hhi⟩ := thm_plane_ratio_b ι hι P hP a ha
  have hκ : 0 < ambKernel P (ι a) := by
    unfold ambKernel
    have := Real.cosh_pos (hdist P (ι a) / 2)
    positivity
  have hfin : resolventConvDisk (fun b => ambKernel P (ι b)) a ≠ ⊤ := ne_top_of_lt hhi
  have hl2 : 0 ≤ 1 - Real.log 2 := by linarith [Real.log_two_lt_d9]
  constructor
  · rw [lt_div_iff₀ hκ]
    exact (ENNReal.ofReal_lt_iff_lt_toReal (mul_nonneg hl2 hκ.le) hfin).mp hlo
  · rw [div_lt_iff₀ hκ]
    have := ENNReal.toReal_lt_of_lt_ofReal hhi
    linarith

/-- `thm:plane-ratio` (c) helper: the hemisphere `|w|² + ξ² = 1` as a plane embedding,
`z ↦ (2z/(1+|z|²), (1-|z|²)/(1+|z|²))`. -/
theorem s10_prc_embed :
    IsPlaneEmbedding fun z : ℂ =>
      ((((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * z, (1 - ‖z‖ ^ 2) / (1 + ‖z‖ ^ 2)) : ℂ × ℝ) := by
  have h2 : ∀ w : ℂ, ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := fun w => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  refine ⟨fun z hz => ?_, fun a ha b hb => ?_⟩
  · have := mem_ball_zero_iff.mp hz
    show 0 < (1 - ‖z‖ ^ 2) / (1 + ‖z‖ ^ 2)
    exact div_pos (by nlinarith [norm_nonneg z]) (by positivity)
  · show Real.arcosh (coshDist _ _) = Real.arcosh (diskCoshDist a b)
    congr 1
    have ha1 := mem_ball_zero_iff.mp ha
    have hb1 := mem_ball_zero_iff.mp hb
    have ha2 : 1 - (a.re ^ 2 + a.im ^ 2) ≠ 0 := by rw [← h2]; nlinarith [norm_nonneg a]
    have hb2 : 1 - (b.re ^ 2 + b.im ^ 2) ≠ 0 := by rw [← h2]; nlinarith [norm_nonneg b]
    have ha3 : 1 + (a.re ^ 2 + a.im ^ 2) ≠ 0 := by positivity
    have hb3 : 1 + (b.re ^ 2 + b.im ^ 2) ≠ 0 := by positivity
    unfold coshDist diskCoshDist
    simp only [h2, Complex.sub_re, Complex.sub_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    field_simp
    ring

/-- `thm:plane-ratio` (c) helper (Bochner form of `s10_prb_rep`):
`(𝔊 * κ_Π)(q)/κ_Π(q) = ∫₀^∞ 𝔊(s) 2π sinh s m_s(q)/κ_Π(q) ds`. -/
theorem s10_prc_ratio {ι : ℂ → ℂ × ℝ} (hι : IsPlaneEmbedding ι) {P : ℂ × ℝ} (hP : P ∈ UHS)
    {a : ℂ} (ha : a ∈ unitDisc) :
    (resolventConvDisk (fun b => ambKernel P (ι b)) a).toReal / ambKernel P (ι a) =
      ∫ s in Ioi (0 : ℝ), resolventG s * (2 * π * Real.sinh s) *
        (circleMean (fun b => ambKernel P (ι b)) a s / ambKernel P (ι a)) := by
  have hκ : 0 < ambKernel P (ι a) := by
    unfold ambKernel
    have := Real.cosh_pos (hdist P (ι a) / 2)
    positivity
  have hmc := s10_prb_mean_cont hι hP ha
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun s => resolventG s * (2 * π * Real.sinh s) *
      circleMean (fun b => ambKernel P (ι b)) a s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : (0 : ℝ) < s := hs
    have hm := (thm_plane_ratio_a ι hι P hP a ha s hs').1
    have : 0 < ambKernel P (ι a) / Real.cosh s := div_pos hκ (Real.cosh_pos s)
    exact mul_nonneg (mul_pos (s10_resolventG_pos hs')
      (mul_pos Real.two_pi_pos (Real.sinh_pos_iff.mpr hs'))).le (by linarith)
  have hmeas : AEStronglyMeasurable (fun s => resolventG s * (2 * π * Real.sinh s) *
      circleMean (fun b => ambKernel P (ι b)) a s) (volume.restrict (Ioi (0 : ℝ))) := by
    have := s10_prb_meas_G
    have := hmc.measurable
    exact (by fun_prop : Measurable fun s => resolventG s * (2 * π * Real.sinh s) *
      circleMean (fun b => ambKernel P (ι b)) a s).aestronglyMeasurable
  rw [s10_prb_rep hι hP ha, ← integral_eq_lintegral_of_nonneg_ae hnn hmeas, ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
  simp only [mul_div_assoc]

/-- `thm:plane-ratio` (c) helper (dominated convergence): if `0 ≤ g_n ≤ 1` on `(0, ∞)` and
`g_n → g₀` pointwise, then `∫₀^∞ 𝔊 2π sinh g_n → ∫₀^∞ 𝔊 2π sinh g₀`. -/
theorem s10_prc_dct {β : Type*} {l : Filter β} [l.IsCountablyGenerated] {g : β → ℝ → ℝ}
    {g₀ : ℝ → ℝ} (hm : ∀ᶠ n in l, Measurable (g n))
    (hb : ∀ᶠ n in l, ∀ s : ℝ, 0 < s → 0 ≤ g n s ∧ g n s ≤ 1)
    (hl : ∀ s : ℝ, 0 < s → Tendsto (fun n => g n s) l (𝓝 (g₀ s))) :
    Tendsto (fun n => ∫ s in Ioi (0 : ℝ), resolventG s * (2 * π * Real.sinh s) * g n s) l
      (𝓝 (∫ s in Ioi (0 : ℝ), resolventG s * (2 * π * Real.sinh s) * g₀ s)) := by
  obtain ⟨hi1, -⟩ := lem_plane_green_f
  have hw : ∀ s : ℝ, 0 < s → 0 < resolventG s * (2 * π * Real.sinh s) := fun s hs =>
    mul_pos (s10_resolventG_pos hs) (mul_pos Real.two_pi_pos (Real.sinh_pos_iff.mpr hs))
  refine tendsto_integral_filter_of_dominated_convergence
    (fun s => resolventG s * (2 * π * Real.sinh s)) ?_ ?_ hi1 ?_
  · filter_upwards [hm] with n hn
    have := s10_prb_meas_G
    exact (by fun_prop : Measurable fun s => resolventG s * (2 * π * Real.sinh s) * g n s
      ).aestronglyMeasurable
  · filter_upwards [hb] with n hn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw s hs).le (hn s hs).1)]
    exact mul_le_of_le_one_right (hw s hs).le (hn s hs).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hl s hs).const_mul _

/-- `thm:plane-ratio` (c) helper: for the hemisphere embedding and `P = (0, e^d)`,
`cosh d(P, ι₀ z) = cosh d (1+|z|²)/(1-|z|²)`. -/
theorem s10_prc_coshDist_normal (d : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    coshDist ((0 : ℂ), Real.exp d)
        ((((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * z, (1 - ‖z‖ ^ 2) / (1 + ‖z‖ ^ 2)) : ℂ × ℝ) =
      Real.cosh d * ((1 + ‖z‖ ^ 2) / (1 - ‖z‖ ^ 2)) := by
  have h1 : 1 - ‖z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z]
  have h3 : 0 < 1 + ‖z‖ ^ 2 := by positivity
  have he := Real.exp_pos d
  unfold coshDist
  simp only [zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos two_pos h3)]
  rw [Real.cosh_eq, Real.exp_neg]
  field_simp
  ring

/-- `thm:plane-ratio` (c) helper: `κ_P(ι₀ z) = 2/(1 + cosh d (1+|z|²)/(1-|z|²))` for
`P = (0, e^d)`. -/
theorem s10_prc_kernel_normal (d : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    ambKernel ((0 : ℂ), Real.exp d)
        ((((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * z, (1 - ‖z‖ ^ 2) / (1 + ‖z‖ ^ 2)) : ℂ × ℝ) =
      2 / (1 + Real.cosh d * ((1 + ‖z‖ ^ 2) / (1 - ‖z‖ ^ 2))) := by
  rw [s09_ambKernel_eq_inv _ _ (s09_one_le_coshDist _ _ (Real.exp_pos d)
    (s10_prc_embed.1 (mem_ball_zero_iff.mpr hz))), s10_prc_coshDist_normal d hz]

/-- `thm:plane-ratio` (c) helper (infimum): for the hemisphere, `q = 0` and `P = (0, e^d)` on the
normal through `q`, the ratio tends to `1 - log 2` as `d → ∞` (`m_s/κ = (1+cosh d)/(1+cosh d cosh s)`,
dominated convergence). -/
theorem s10_prc_inf :
    Tendsto (fun d : ℝ =>
      (resolventConvDisk (fun b => ambKernel ((0 : ℂ), Real.exp d)
        ((((2 / (1 + ‖b‖ ^ 2) : ℝ) : ℂ) * b, (1 - ‖b‖ ^ 2) / (1 + ‖b‖ ^ 2)) : ℂ × ℝ)) 0).toReal /
        ambKernel ((0 : ℂ), Real.exp d) ((0 : ℂ), (1 : ℝ))) atTop (𝓝 (1 - Real.log 2)) := by
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  obtain ⟨-, -, -, hv2, -, -⟩ := lem_plane_green_f
  have hlim : ∫ s in Ioi (0 : ℝ), resolventG s * (2 * π * Real.sinh s) * (Real.cosh s)⁻¹ =
      1 - Real.log 2 := by
    rw [← hv2]
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    rw [Real.tanh_eq_sinh_div_cosh]
    ring
  have hval : ∀ d : ℝ, (resolventConvDisk (fun b => ambKernel ((0 : ℂ), Real.exp d)
        ((((2 / (1 + ‖b‖ ^ 2) : ℝ) : ℂ) * b, (1 - ‖b‖ ^ 2) / (1 + ‖b‖ ^ 2)) : ℂ × ℝ)) 0).toReal /
        ambKernel ((0 : ℂ), Real.exp d) ((0 : ℂ), (1 : ℝ)) =
      ∫ s in Ioi (0 : ℝ), resolventG s * (2 * π * Real.sinh s) *
        ((1 + Real.cosh d) / (1 + Real.cosh d * Real.cosh s)) := by
    intro d
    have hP : ((0 : ℂ), Real.exp d) ∈ UHS := Real.exp_pos d
    rw [show ((0 : ℂ), (1 : ℝ)) = ((((2 / (1 + ‖(0 : ℂ)‖ ^ 2) : ℝ) : ℂ) * 0,
      (1 - ‖(0 : ℂ)‖ ^ 2) / (1 + ‖(0 : ℂ)‖ ^ 2)) : ℂ × ℝ) by simp,
      s10_prc_ratio s10_prc_embed hP h0]
    refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    have hs' : (0 : ℝ) < s := hs
    have ht0 : 0 < Real.tanh (s / 2) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
    have hnorm : ∀ θ : ℝ, ‖(Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I)‖ =
        Real.tanh (s / 2) := fun θ => by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht0]
    have hdm : ∀ z : ℂ, diskMob 0 z = z := fun z => by simp [diskMob]
    have hm : circleMean (fun b => ambKernel ((0 : ℂ), Real.exp d)
        ((((2 / (1 + ‖b‖ ^ 2) : ℝ) : ℂ) * b, (1 - ‖b‖ ^ 2) / (1 + ‖b‖ ^ 2)) : ℂ × ℝ)) 0 s =
        2 / (1 + Real.cosh d * Real.cosh s) := by
      unfold circleMean
      rw [intervalIntegral.integral_congr (g := fun _ => 2 / (1 + Real.cosh d * Real.cosh s))
        (fun θ _ => ?_)]
      · rw [intervalIntegral.integral_const, smul_eq_mul]
        have := Real.pi_pos
        field_simp
        ring
      · beta_reduce
        rw [hdm, s10_prc_kernel_normal d (by rw [hnorm θ]; exact Real.tanh_lt_one _), hnorm θ,
          (s03_geo_cosh_tanh s).1]
    have hk0 := s10_prc_kernel_normal d (z := 0) (by simp)
    rw [hm, hk0]
    simp only [norm_zero]
    have := Real.cosh_pos d
    have := Real.cosh_pos s
    field_simp
    ring
  refine (tendsto_congr hval).mpr ?_
  rw [← hlim]
  refine s10_prc_dct (g := fun d s => (1 + Real.cosh d) / (1 + Real.cosh d * Real.cosh s))
    (g₀ := fun s => (Real.cosh s)⁻¹) (Eventually.of_forall fun d => by fun_prop)
    (Eventually.of_forall fun d s _ => ?_) (fun s _ => ?_)
  · have hc := Real.one_le_cosh d
    have hcs := Real.one_le_cosh s
    have hp : 0 < 1 + Real.cosh d * Real.cosh s := by positivity
    refine ⟨div_nonneg (by linarith) hp.le, (div_le_one hp).mpr ?_⟩
    nlinarith
  · have hc : Tendsto (fun d : ℝ => (Real.cosh d)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp s10_tendsto_cosh_atTop
    have h := (hc.add_const 1).div (hc.add_const (Real.cosh s))
      (by rw [zero_add]; exact (Real.cosh_pos s).ne')
    rw [zero_add, zero_add, one_div] at h
    refine h.congr (fun d => ?_)
    show ((Real.cosh d)⁻¹ + 1) / ((Real.cosh d)⁻¹ + Real.cosh s) =
      (1 + Real.cosh d) / (1 + Real.cosh d * Real.cosh s)
    have := Real.cosh_pos d
    have := Real.cosh_pos s
    field_simp

/-- `thm:plane-ratio` (c) helper (supremum): for the hemisphere, `P = (0, 1)` (the image of `0`) and
`q = ρ ∈ (0, 1)`, the ratio tends to `1/2` as `ρ → 1` (`m_s/κ → 1` pointwise, dominated
convergence). -/
theorem s10_prc_sup :
    Tendsto (fun ρ : ℝ =>
      (resolventConvDisk (fun b => ambKernel ((0 : ℂ), (1 : ℝ))
        ((((2 / (1 + ‖b‖ ^ 2) : ℝ) : ℂ) * b, (1 - ‖b‖ ^ 2) / (1 + ‖b‖ ^ 2)) : ℂ × ℝ)) ρ).toReal /
        ambKernel ((0 : ℂ), (1 : ℝ))
          ((((2 / (1 + ‖(ρ : ℂ)‖ ^ 2) : ℝ) : ℂ) * ρ, (1 - ‖(ρ : ℂ)‖ ^ 2) / (1 + ‖(ρ : ℂ)‖ ^ 2)) :
            ℂ × ℝ)) (𝓝[<] 1) (𝓝 (1 / 2)) := by
  obtain ⟨-, hv1, -⟩ := lem_plane_green_f
  have hlim : ∫ s in Ioi (0 : ℝ), resolventG s * (2 * π * Real.sinh s) * 1 = 1 / 2 := by
    simp only [mul_one]
    exact hv1
  have hK1 : ∀ z : ℂ, ‖z‖ < 1 → ambKernel ((0 : ℂ), (1 : ℝ))
      ((((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * z, (1 - ‖z‖ ^ 2) / (1 + ‖z‖ ^ 2)) : ℂ × ℝ) =
      2 / (1 + (1 + ‖z‖ ^ 2) / (1 - ‖z‖ ^ 2)) := fun z hz => by
    have h := s10_prc_kernel_normal 0 hz
    rwa [Real.exp_zero, Real.cosh_zero, one_mul] at h
  have hval : ∀ ρ ∈ Ioo (0 : ℝ) 1,
      (resolventConvDisk (fun b => ambKernel ((0 : ℂ), (1 : ℝ))
        ((((2 / (1 + ‖b‖ ^ 2) : ℝ) : ℂ) * b, (1 - ‖b‖ ^ 2) / (1 + ‖b‖ ^ 2)) : ℂ × ℝ)) ρ).toReal /
        ambKernel ((0 : ℂ), (1 : ℝ))
          ((((2 / (1 + ‖(ρ : ℂ)‖ ^ 2) : ℝ) : ℂ) * ρ, (1 - ‖(ρ : ℂ)‖ ^ 2) / (1 + ‖(ρ : ℂ)‖ ^ 2)) :
            ℂ × ℝ) =
      ∫ s in Ioi (0 : ℝ), resolventG s * (2 * π * Real.sinh s) *
        ((1 - Real.tanh (s / 2) ^ 2) / (1 - ρ ^ 2 * Real.tanh (s / 2) ^ 2)) := by
    intro ρ hρ
    have hP : ((0 : ℂ), (1 : ℝ)) ∈ UHS := show (0 : ℝ) < 1 from one_pos
    have hρn : ‖(ρ : ℂ)‖ = ρ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ.1]
    have hρd : (ρ : ℂ) ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hρn]; exact hρ.2)
    have hnρ : -(ρ : ℂ) ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [norm_neg, hρn]; exact hρ.2)
    rw [s10_prc_ratio s10_prc_embed hP hρd]
    refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    have hs' : (0 : ℝ) < s := hs
    congr 1
    obtain ⟨t, ht⟩ : ∃ t, t = Real.tanh (s / 2) := ⟨_, rfl⟩
    have ht0 : 0 < t := by
      rw [ht, Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
    have ht1 : t < 1 := ht ▸ Real.tanh_lt_one _
    have h1t : 0 < 1 - t ^ 2 := by nlinarith
    have h1ρ : 0 < 1 - ρ ^ 2 := by nlinarith [hρ.1, hρ.2]
    have hρt : ρ * t < 1 := by nlinarith [hρ.1, hρ.2]
    have hρt0 : 0 < ρ * t := mul_pos hρ.1 ht0
    have h1ρt : 0 < 1 - ρ ^ 2 * t ^ 2 := by nlinarith
    have hnorm : ∀ θ : ℝ, ‖(t : ℂ) * Complex.exp ((θ : ℂ) * I)‖ = t := fun θ => by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht0]
    have hd0 : diskMob (ρ : ℂ) (-(ρ : ℂ)) = 0 := by simp [diskMob]
    have hpt : ∀ θ : ℝ, ambKernel ((0 : ℂ), (1 : ℝ))
        ((((2 / (1 + ‖diskMob (ρ : ℂ) ((t : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ^ 2) : ℝ) : ℂ) *
          diskMob (ρ : ℂ) ((t : ℂ) * Complex.exp ((θ : ℂ) * I)),
          (1 - ‖diskMob (ρ : ℂ) ((t : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ^ 2) /
            (1 + ‖diskMob (ρ : ℂ) ((t : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ^ 2)) : ℂ × ℝ) =
        (1 - ρ ^ 2) * (1 - t ^ 2) *
          (1 + ρ ^ 2 * t ^ 2 - (-(2 * ρ * t)) * Real.cos θ - 0 * Real.sin θ)⁻¹ := by
      intro θ
      set z : ℂ := (t : ℂ) * Complex.exp ((θ : ℂ) * I) with hz
      have hzd : z ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [hnorm θ]; exact ht1)
      have hwd := (s10_pr_mob hρd).1 hzd
      have hw1 := mem_ball_zero_iff.mp hwd
      have hinv := (s10_pr_mob hρd).2 _ hnρ _ hzd
      rw [hd0] at hinv
      have hwc : (1 + ‖diskMob (ρ : ℂ) z‖ ^ 2) / (1 - ‖diskMob (ρ : ℂ) z‖ ^ 2) =
          diskCoshDist 0 (diskMob (ρ : ℂ) z) := by
        have : 1 - ‖diskMob (ρ : ℂ) z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg (diskMob (ρ : ℂ) z)]
        unfold diskCoshDist
        rw [zero_sub, norm_neg, norm_zero]
        field_simp
        ring
      have hzre : z.re = t * Real.cos θ := by
        rw [hz, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
      have hzim : z.im = t * Real.sin θ := by
        rw [hz, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
      have hsq : ‖-(ρ : ℂ) - z‖ ^ 2 = t ^ 2 + 2 * ρ * t * Real.cos θ + ρ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.neg_re,
          Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, hzre, hzim]
        linear_combination t ^ 2 * Real.cos_sq_add_sin_sq θ
      have hcos := Real.neg_one_le_cos θ
      have hA : 0 < 1 + ρ ^ 2 * t ^ 2 - (-(2 * ρ * t)) * Real.cos θ - 0 * Real.sin θ := by
        have h2 : (0 : ℝ) ≤ 2 * ρ * t := by linarith [hρt0]
        nlinarith [mul_le_mul_of_nonneg_left hcos h2, sq_pos_of_pos (sub_pos.mpr hρt)]
      have hA1 : 0 < 1 + ρ * t * Real.cos θ * 2 + ρ ^ 2 * t ^ 2 := by linarith
      have hA2 : 0 < 2 + ρ * t * Real.cos θ * 4 + ρ ^ 2 * t ^ 2 * 2 := by linarith
      rw [hK1 _ hw1, hwc, hinv]
      unfold diskCoshDist
      rw [hsq, norm_neg, hρn, hnorm θ]
      field_simp
      rw [div_eq_div_iff (ne_of_gt (by nlinarith [hA1])) (ne_of_gt (by nlinarith [hA1]))]
      ring
    have hpq : (-(2 * ρ * t)) ^ 2 + 0 ^ 2 < (1 + ρ ^ 2 * t ^ 2) ^ 2 := by nlinarith
    have hpois := s10_pr_poisson (A := 1 + ρ ^ 2 * t ^ 2) (by positivity) hpq
    rw [show (1 + ρ ^ 2 * t ^ 2) ^ 2 - (-(2 * ρ * t)) ^ 2 - 0 ^ 2 = (1 - ρ ^ 2 * t ^ 2) ^ 2 by ring,
      Real.sqrt_sq h1ρt.le] at hpois
    have hm : circleMean (fun b => ambKernel ((0 : ℂ), (1 : ℝ))
        ((((2 / (1 + ‖b‖ ^ 2) : ℝ) : ℂ) * b, (1 - ‖b‖ ^ 2) / (1 + ‖b‖ ^ 2)) : ℂ × ℝ)) ρ s =
        (1 - ρ ^ 2) * (1 - t ^ 2) / (1 - ρ ^ 2 * t ^ 2) := by
      unfold circleMean
      rw [← ht, intervalIntegral.integral_congr (fun θ _ => hpt θ),
        intervalIntegral.integral_const_mul, hpois]
      have := Real.pi_pos
      field_simp
    rw [hm, ← ht, hK1 _ (by rw [hρn]; exact hρ.2), hρn]
    field_simp
    ring
  refine (tendsto_congr' (f₂ := fun ρ : ℝ => ∫ s in Ioi (0 : ℝ), resolventG s *
    (2 * π * Real.sinh s) * ((1 - Real.tanh (s / 2) ^ 2) / (1 - ρ ^ 2 * Real.tanh (s / 2) ^ 2))) ?_).mpr ?_
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with ρ hρ
    exact hval ρ hρ
  rw [← hlim]
  have htc := s10_prb_continuous_tanh
  refine s10_prc_dct
    (g := fun ρ s => (1 - Real.tanh (s / 2) ^ 2) / (1 - ρ ^ 2 * Real.tanh (s / 2) ^ 2))
    (g₀ := fun _ => 1) (Eventually.of_forall fun ρ => ?_) ?_ (fun s hs => ?_)
  · have := htc.measurable
    fun_prop
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with ρ hρ
    intro s hs
    have ht0 : 0 < Real.tanh (s / 2) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
    have ht1 := Real.tanh_lt_one (s / 2)
    have hρ2 : ρ ^ 2 < 1 := by nlinarith [hρ.1, hρ.2]
    have hp : 0 < 1 - ρ ^ 2 * Real.tanh (s / 2) ^ 2 := by nlinarith
    refine ⟨div_nonneg (by nlinarith) hp.le, (div_le_one hp).mpr ?_⟩
    nlinarith [sq_nonneg (Real.tanh (s / 2)), hρ.1]
  · have ht0 : 0 < Real.tanh (s / 2) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
    have ht1 := Real.tanh_lt_one (s / 2)
    have hne : 1 - Real.tanh (s / 2) ^ 2 ≠ 0 := by nlinarith
    have hcont : Continuous fun ρ : ℝ => 1 - ρ ^ 2 * Real.tanh (s / 2) ^ 2 := by fun_prop
    have h1 := hcont.tendsto 1
    simp only [one_pow, one_mul] at h1
    have h2 := (tendsto_const_nhds (x := 1 - Real.tanh (s / 2) ^ 2)).div h1 hne
    rw [div_self hne] at h2
    exact tendsto_nhdsWithin_of_tendsto_nhds h2

/-- **Theorem 10.7 (c)**, `thm:plane-ratio`, `sec10-sharp.tex:294`: the constants of (b) are
optimal: over all planes, centres `P` and points `q ∈ Π`, the ratio `(𝔊 * κ_Π)(q)/κ_Π(q)` has
infimum `1 - log 2` and supremum `1/2`. -/
theorem thm_plane_ratio_c :
    IsGLB {x : ℝ | ∃ (ι : ℂ → ℂ × ℝ) (P : ℂ × ℝ) (a : ℂ), IsPlaneEmbedding ι ∧ P ∈ UHS ∧
        a ∈ unitDisc ∧
        x = (resolventConvDisk (fun b => ambKernel P (ι b)) a).toReal / ambKernel P (ι a)}
        (1 - Real.log 2) ∧
      IsLUB {x : ℝ | ∃ (ι : ℂ → ℂ × ℝ) (P : ℂ × ℝ) (a : ℂ), IsPlaneEmbedding ι ∧ P ∈ UHS ∧
        a ∈ unitDisc ∧
        x = (resolventConvDisk (fun b => ambKernel P (ι b)) a).toReal / ambKernel P (ι a)}
        (1 / 2) := by
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hι₀0 : ((((2 / (1 + ‖(0 : ℂ)‖ ^ 2) : ℝ) : ℂ) * 0, (1 - ‖(0 : ℂ)‖ ^ 2) / (1 + ‖(0 : ℂ)‖ ^ 2)) :
      ℂ × ℝ) = ((0 : ℂ), (1 : ℝ)) := by simp
  refine ⟨⟨?_, fun c hc => ?_⟩, ⟨?_, fun c hc => ?_⟩⟩
  · rintro x ⟨ι, P, a, hι, hP, ha, rfl⟩
    exact (s10_prc_bounds hι hP ha).1.le
  · refine ge_of_tendsto s10_prc_inf (Eventually.of_forall fun d => hc ?_)
    refine ⟨_, ((0 : ℂ), Real.exp d), 0, s10_prc_embed, Real.exp_pos d, h0, ?_⟩
    rw [hι₀0]
  · rintro x ⟨ι, P, a, hι, hP, ha, rfl⟩
    exact (s10_prc_bounds hι hP ha).2.le
  · refine le_of_tendsto s10_prc_sup ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with ρ hρ
    refine hc ⟨_, ((0 : ℂ), (1 : ℝ)), (ρ : ℂ), s10_prc_embed, (show (0 : ℝ) < 1 from one_pos), ?_, rfl⟩
    show (ρ : ℂ) ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ.1]
    exact hρ.2

/-- `rem:linear-model` helper: for `a, b ≥ 0`, `a⁺ (g b)⁺ = b⁺ (g a)⁺` (both sides vanish when
`g < 0`). Needed because `𝔊(0) = Q₁(1)/(2π) < 0` is a junk value (`artanh 1 = 0`), so
`ofReal (𝔊 d * σ)` cannot be split as a product on the diagonal. -/
theorem s10_rlm_ofReal_swap {a b g : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal a * ENNReal.ofReal (g * b) = ENNReal.ofReal b * ENNReal.ofReal (g * a) := by
  by_cases hg : 0 ≤ g
  · rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb]
    congr 1
    ring
  · have hg' : g ≤ 0 := (lt_of_not_ge hg).le
    rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hg' hb),
      ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hg' ha), mul_zero, mul_zero]

/-- `rem:linear-model` helper: on a plane `Π = ι(𝔻)`, `b ↦ κ_Π(b) = k_P(ι b)` is continuous on
`𝔻` (closed form of `s10_prb_kernel` at `a = 0`). -/
theorem s10_rlm_kernel_cont {ι : ℂ → ℂ × ℝ} (hι : IsPlaneEmbedding ι) {P : ℂ × ℝ} (hP : P ∈ UHS) :
    ContinuousOn (fun b => ambKernel P (ι b)) unitDisc := by
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  obtain ⟨u₀, u₁, u₂, -, -, hk⟩ := s10_prb_kernel hι hP h0
  have hm0 : ∀ z, diskMob 0 z = z := fun z => by
    show (z + 0) / (1 + conj 0 * z) = z
    simp
  have hc : ContinuousOn (fun z : ℂ => 2 * (1 - ‖z‖ ^ 2) /
      (1 - ‖z‖ ^ 2 + u₀ * (1 + ‖z‖ ^ 2) - 2 * u₁ * z.re - 2 * u₂ * z.im)) unitDisc :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => (hk z hz).1.ne'
  refine hc.congr fun z hz => ?_
  have h := (hk z hz).2
  rw [hm0] at h
  exact h

/-- `rem:linear-model` helper (Tonelli and the symmetry of `𝔊(d(z, q))`): for `κ, σ ≥ 0`
continuous on `𝔻`, `∫ κ (𝔊 * σ) = ∫ σ (𝔊 * κ)`. -/
theorem s10_rlm_fubini {κ σ : ℂ → ℝ} (hκ : ContinuousOn κ unitDisc) (hκ0 : ∀ z ∈ unitDisc, 0 ≤ κ z)
    (hσ : ContinuousOn σ unitDisc) (hσ0 : ∀ z ∈ unitDisc, 0 ≤ σ z) :
    ∫⁻ z, ENNReal.ofReal (κ z) * ∫⁻ q, ENNReal.ofReal (resolventG (diskDist z q) * σ q)
        ∂diskHypArea ∂diskHypArea =
      ∫⁻ q, ENNReal.ofReal (σ q) * resolventConvDisk κ q ∂diskHypArea := by
  classical
  have hD : MeasurableSet unitDisc := measurableSet_ball
  obtain ⟨κm, hκm⟩ : ∃ κm : ℂ → ℝ, κm = unitDisc.piecewise κ 0 := ⟨_, rfl⟩
  obtain ⟨σm, hσm⟩ : ∃ σm : ℂ → ℝ, σm = unitDisc.piecewise σ 0 := ⟨_, rfl⟩
  have hκmm : Measurable κm := by
    rw [hκm]
    exact hκ.measurable_piecewise continuousOn_const hD
  have hσmm : Measurable σm := by
    rw [hσm]
    exact hσ.measurable_piecewise continuousOn_const hD
  have hκe : ∀ z ∈ unitDisc, κm z = κ z := fun z hz => by
    rw [hκm]
    exact piecewise_eq_of_mem _ _ _ hz
  have hσe : ∀ z ∈ unitDisc, σm z = σ z := fun z hz => by
    rw [hσm]
    exact piecewise_eq_of_mem _ _ _ hz
  have hae : ∀ᵐ z ∂diskHypArea, z ∈ unitDisc := by
    show ∀ᵐ z ∂(volume.restrict unitDisc).withDensity
      (fun z => ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2)), z ∈ unitDisc
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_ball)
  have hdm : Measurable fun p : ℂ × ℂ => diskDist p.1 p.2 := by
    show Measurable fun p : ℂ × ℂ =>
      Real.log (diskCoshDist p.1 p.2 + √(diskCoshDist p.1 p.2 ^ 2 - 1))
    unfold diskCoshDist
    fun_prop
  obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ → ℝ≥0∞, F = fun z q =>
      ENNReal.ofReal (κm z) * ENNReal.ofReal (resolventG (diskDist z q) * σm q) := ⟨_, rfl⟩
  have hFm : Measurable (Function.uncurry F) := by
    rw [hF]
    exact (ENNReal.measurable_ofReal.comp (hκmm.comp measurable_fst)).mul
      (ENNReal.measurable_ofReal.comp ((s10_prb_meas_G.comp hdm).mul
        (hσmm.comp measurable_snd)))
  have hL : ∫⁻ z, ENNReal.ofReal (κ z) * ∫⁻ q, ENNReal.ofReal (resolventG (diskDist z q) * σ q)
      ∂diskHypArea ∂diskHypArea = ∫⁻ z, ∫⁻ q, F z q ∂diskHypArea ∂diskHypArea := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with z hz
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with q hq
    rw [hF]
    beta_reduce
    rw [hκe z hz, hσe q hq]
  have hR : ∫⁻ q, ENNReal.ofReal (σ q) * resolventConvDisk κ q ∂diskHypArea =
      ∫⁻ q, ∫⁻ z, F z q ∂diskHypArea ∂diskHypArea := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with q hq
    unfold resolventConvDisk
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with z hz
    rw [hF]
    beta_reduce
    rw [hκe z hz, hσe q hq, s02_diskDist_comm hq hz]
    exact (s10_rlm_ofReal_swap (hκ0 z hz) (hσ0 q hq)).symm
  have : SFinite diskHypArea := by
    show SFinite ((volume.restrict unitDisc).withDensity
      (fun z => ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2)))
    infer_instance
  rw [hL, hR]
  exact lintegral_lintegral_swap hFm.aemeasurable

/-- **Remark 10.8**, `rem:linear-model`, `sec10-sharp.tex:361`: in the linearized model
`(2 - Δ) t = 2σ` on a plane `Π`, `∫ κ_Π t = 2 ∫ σ (𝔊 * κ_Π)` and
`2(1 - log 2) ∫ κ_Π σ ≤ ∫ κ_Π t ≤ ∫ κ_Π σ`. -/
theorem rem_linear_model (ι : ℂ → ℂ × ℝ) (P : ℂ × ℝ) (σ t : ℂ → ℝ)
    (hd : IsLinearModelData ι P σ t) :
    ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * t z) ∂diskHypArea =
        2 * ∫⁻ z, ENNReal.ofReal (σ z) * resolventConvDisk (fun b => ambKernel P (ι b)) z
          ∂diskHypArea ∧
      ENNReal.ofReal (2 * (1 - Real.log 2)) *
          ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * σ z) ∂diskHypArea ≤
        ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * t z) ∂diskHypArea ∧
      ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * t z) ∂diskHypArea ≤
        ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * σ z) ∂diskHypArea := by
  obtain ⟨hι, hP, hσs, hσ0, -, ht, htb, heq⟩ := hd
  have hκ0 : ∀ z, 0 < ambKernel P (ι z) := fun z => by
    unfold ambKernel
    have := Real.cosh_pos (hdist P (ι z) / 2)
    positivity
  have hσc : ContinuousOn σ unitDisc := hσs.continuousOn
  have hae : ∀ᵐ z ∂diskHypArea, z ∈ unitDisc := by
    show ∀ᵐ z ∂(volume.restrict unitDisc).withDensity
      (fun z => ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2)), z ∈ unitDisc
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_ball)
  have hg : ∀ p ∈ unitDisc, ENNReal.ofReal (t p) =
      ∫⁻ q, ENNReal.ofReal (resolventG (diskDist p q) * (2 * σ q)) ∂diskHypArea := by
    intro p hp
    have h := (lem_plane_green_g t ht htb (fun z hz => by rw [heq z hz]; linarith [hσ0 z hz])
      p hp).2
    rw [h]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with q hq
    rw [heq q hq]
  have h1 : ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * t z) ∂diskHypArea =
      2 * ∫⁻ z, ENNReal.ofReal (σ z) * resolventConvDisk (fun b => ambKernel P (ι b)) z
        ∂diskHypArea := by
    calc ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * t z) ∂diskHypArea
        = ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z)) *
            ∫⁻ q, ENNReal.ofReal (resolventG (diskDist z q) * (2 * σ q)) ∂diskHypArea
              ∂diskHypArea := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with z hz
          rw [ENNReal.ofReal_mul (hκ0 z).le, hg z hz]
      _ = ∫⁻ q, ENNReal.ofReal (2 * σ q) * resolventConvDisk (fun b => ambKernel P (ι b)) q
            ∂diskHypArea :=
          s10_rlm_fubini (s10_rlm_kernel_cont hι hP) (fun z _ => (hκ0 z).le)
            (continuousOn_const.mul hσc) (fun z hz => by linarith [hσ0 z hz])
      _ = 2 * ∫⁻ z, ENNReal.ofReal (σ z) * resolventConvDisk (fun b => ambKernel P (ι b)) z
            ∂diskHypArea := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
          refine lintegral_congr fun q => ?_
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_assoc]
  refine ⟨h1, ?_, ?_⟩
  · rw [h1, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with q hq
    have hlo := (thm_plane_ratio_b ι hι P hP q hq).1
    have hl2 : 0 ≤ 1 - Real.log 2 := by linarith [Real.log_two_lt_d9]
    calc ENNReal.ofReal (2 * (1 - Real.log 2)) * ENNReal.ofReal (ambKernel P (ι q) * σ q)
        = 2 * (ENNReal.ofReal (σ q) * ENNReal.ofReal ((1 - Real.log 2) * ambKernel P (ι q))) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (hσ0 q hq),
            ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
      _ ≤ 2 * (ENNReal.ofReal (σ q) * resolventConvDisk (fun b => ambKernel P (ι b)) q) := by
          gcongr
  · rw [h1, ← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with q hq
    have hhi := (thm_plane_ratio_b ι hι P hP q hq).2
    calc 2 * (ENNReal.ofReal (σ q) * resolventConvDisk (fun b => ambKernel P (ι b)) q)
        ≤ 2 * (ENNReal.ofReal (σ q) * ENNReal.ofReal (ambKernel P (ι q) / 2)) := by
          gcongr
      _ = ENNReal.ofReal (ambKernel P (ι q) * σ q) := by
          rw [← ENNReal.ofReal_mul (hσ0 q hq), ← ENNReal.ofReal_ofNat 2,
            ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring

/-- `rem:linear-model` (sharpness) helper (S1, the radial ODE): for
`F(x) = ∑_{j<n} x^{-(2j+2)}/(2j+3)`, with `F' = F₁`, `F₁' = F₂`,
`(x² - 1) F₂ + 2x F₁ = 2F - 2n x^{-(2n+2)}` (telescoping). -/
theorem s10_rls_ode (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => ∑ j ∈ Finset.range n, (x ^ (2 * j + 2))⁻¹ / (2 * (j : ℝ) + 3))
      (∑ j ∈ Finset.range n, -((2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3)) * (x ^ (2 * j + 3))⁻¹) x ∧
    HasDerivAt (fun x : ℝ =>
        ∑ j ∈ Finset.range n, -((2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3)) * (x ^ (2 * j + 3))⁻¹)
      (∑ j ∈ Finset.range n, (2 * (j : ℝ) + 2) * (x ^ (2 * j + 4))⁻¹) x ∧
    (x ^ 2 - 1) * (∑ j ∈ Finset.range n, (2 * (j : ℝ) + 2) * (x ^ (2 * j + 4))⁻¹) +
        2 * x * (∑ j ∈ Finset.range n,
          -((2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3)) * (x ^ (2 * j + 3))⁻¹) =
      2 * (∑ j ∈ Finset.range n, (x ^ (2 * j + 2))⁻¹ / (2 * (j : ℝ) + 3)) -
        2 * n * (x ^ (2 * n + 2))⁻¹ := by
  have hx0 : x ≠ 0 := hx.ne'
  have hinv : ∀ k : ℕ, HasDerivAt (fun x : ℝ => (x ^ (k + 1))⁻¹) (-((k : ℝ) + 1) * (x ^ (k + 2))⁻¹) x :=
    fun k => by
      have h := (hasDerivAt_pow (k + 1) x).inv (pow_ne_zero _ hx0)
      refine h.congr_deriv ?_
      rw [Nat.add_sub_cancel]
      push_cast
      field_simp
      ring
  refine ⟨?_, ?_, ?_⟩
  · refine HasDerivAt.fun_sum fun j _ => ?_
    have h := (hinv (2 * j + 1)).div_const (2 * (j : ℝ) + 3)
    refine h.congr_deriv ?_
    push_cast
    ring
  · refine HasDerivAt.fun_sum fun j _ => ?_
    have h := (hinv (2 * j + 2)).const_mul (-((2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3)))
    have h3 : (2 * (j : ℝ) + 3) ≠ 0 := by positivity
    refine h.congr_deriv ?_
    push_cast
    field_simp
    ring
  · induction n with
    | zero => simp
    | succ n ih =>
      simp only [Finset.sum_range_succ]
      have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
      push_cast
      have e4 : x ^ (2 * n + 4) = x ^ (2 * n + 2) * x ^ 2 := by ring
      have e3 : x ^ (2 * n + 3) = x ^ (2 * n + 2) * x := by ring
      have e2 : x ^ (2 * (n + 1) + 2) = x ^ (2 * n + 2) * x ^ 2 := by ring
      rw [e4, e3, e2]
      have hp : x ^ (2 * n + 2) ≠ 0 := pow_ne_zero _ hx0
      have key : (x ^ 2 - 1) * ((2 * (n : ℝ) + 2) * (x ^ (2 * n + 2) * x ^ 2)⁻¹) +
          2 * x * (-((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3)) * (x ^ (2 * n + 2) * x)⁻¹) =
          2 * ((x ^ (2 * n + 2))⁻¹ / (2 * (n : ℝ) + 3)) - 2 * ((n : ℝ) + 1) *
            (x ^ (2 * n + 2) * x ^ 2)⁻¹ + 2 * n * (x ^ (2 * n + 2))⁻¹ := by
        field_simp
        ring
      linear_combination ih + key

/-- `rem:linear-model` (sharpness) helper (S2, radial Laplacian about `0`, including the
centre): if `F' = F₁`, `F₁' = F₂` on `(0, ∞)` with `F₂` continuous, then `F(cosh d(0, ·))` is `C²`
on `𝔻` and `Δ_ρ F(x) = (x² - 1) F₂(x) + 2x F₁(x)`, `x = cosh d(0, ·)` (off `0` by Lemma 10.6 (b),
at `0` by continuity). -/
theorem s10_rls_lap {F F₁ F₂ : ℝ → ℝ} (h₁ : ∀ x : ℝ, 0 < x → HasDerivAt F (F₁ x) x)
    (h₂ : ∀ x : ℝ, 0 < x → HasDerivAt F₁ (F₂ x) x) (hc : ContinuousOn F₂ (Ioi 0)) :
    ContDiffOn ℝ 2 (fun z => F (diskCoshDist 0 z)) unitDisc ∧ ∀ z ∈ unitDisc,
      hypLaplacianDisk (fun z => F (diskCoshDist 0 z)) z =
        (diskCoshDist 0 z ^ 2 - 1) * F₂ (diskCoshDist 0 z) +
          2 * diskCoshDist 0 z * F₁ (diskCoshDist 0 z) := by
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hO : IsOpen (Ioi (0 : ℝ)) := isOpen_Ioi
  have hd1 : ∀ x ∈ Ioi (0 : ℝ), deriv F x = F₁ x := fun x hx => (h₁ x hx).deriv
  have hd2 : ∀ x ∈ Ioi (0 : ℝ), deriv (deriv F) x = F₂ x := fun x hx => by
    have hev : deriv F =ᶠ[𝓝 x] F₁ := by
      filter_upwards [hO.mem_nhds hx] with y hy
      exact hd1 y hy
    rw [hev.deriv_eq]
    exact (h₂ x hx).deriv
  have hF₁ : ContDiffOn ℝ 1 F₁ (Ioi 0) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hO]
    refine ⟨fun x hx => (h₂ x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (contDiffOn_zero.mpr hc).congr fun x hx => (h₂ x hx).deriv
  have hF : ContDiffOn ℝ 2 F (Ioi 0) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hO]
    exact ⟨fun x hx => (h₁ x hx).differentiableAt.differentiableWithinAt, by simp,
      hF₁.congr hd1⟩
  have hX : ContDiffOn ℝ 2 (diskCoshDist 0) unitDisc := by
    have hden : ∀ z ∈ unitDisc, (1 - ‖(0 : ℂ)‖ ^ 2) * (1 - ‖z‖ ^ 2) ≠ 0 := fun z hz => by
      have := mem_ball_zero_iff.mp hz
      rw [norm_zero]
      have : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      positivity
    have hn : ContDiff ℝ 2 fun z : ℂ => ‖z‖ ^ 2 := contDiff_norm_sq ℝ
    have hn' : ContDiff ℝ 2 fun z : ℂ => ‖0 - z‖ ^ 2 :=
      (contDiff_norm_sq ℝ).comp (contDiff_const.sub contDiff_id)
    show ContDiffOn ℝ 2 (fun z : ℂ => 1 + 2 * ‖0 - z‖ ^ 2 / ((1 - ‖(0 : ℂ)‖ ^ 2) * (1 - ‖z‖ ^ 2)))
      unitDisc
    exact contDiffOn_const.add ((contDiffOn_const.mul hn'.contDiffOn).div
      (contDiffOn_const.mul (contDiffOn_const.sub hn.contDiffOn)) hden)
  have hX1 : ∀ z ∈ unitDisc, 1 ≤ diskCoshDist 0 z := fun z hz => s10_one_le_diskCoshDist h0 hz
  have hXp : MapsTo (diskCoshDist 0) unitDisc (Ioi 0) := fun z hz =>
    show 0 < diskCoshDist 0 z by linarith [hX1 z hz]
  have hC : ContDiffOn ℝ 2 (fun z => F (diskCoshDist 0 z)) unitDisc := hF.comp hX hXp
  refine ⟨hC, ?_⟩
  have hoff : ∀ z ∈ unitDisc, z ≠ 0 → hypLaplacianDisk (fun z => F (diskCoshDist 0 z)) z =
      (diskCoshDist 0 z ^ 2 - 1) * F₂ (diskCoshDist 0 z) +
        2 * diskCoshDist 0 z * F₁ (diskCoshDist 0 z) := fun z hz hz0 => by
    rw [lem_plane_green_b F (hF.mono (Ioi_subset_Ioi zero_le_one)) 0 h0 z hz hz0,
      hd2 _ (hXp hz), hd1 _ (hXp hz)]
  intro z hz
  by_cases hz0 : z ≠ 0
  · exact hoff z hz hz0
  · have hz0' : z = 0 := not_not.mp hz0
    subst hz0'
    have hD : unitDisc ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds h0
    have hL := ((s10_pgg_lap_cont hC).continuousAt hD).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    have hXc : ContinuousAt (diskCoshDist 0) 0 := hX.continuousOn.continuousAt hD
    have hX0 : 0 < diskCoshDist 0 0 := hXp h0
    have hF₁c : ContinuousAt F₁ (diskCoshDist 0 0) :=
      hF₁.continuousOn.continuousAt (hO.mem_nhds hX0)
    have hF₂c : ContinuousAt F₂ (diskCoshDist 0 0) := hc.continuousAt (hO.mem_nhds hX0)
    have hR : ContinuousAt (fun z => (diskCoshDist 0 z ^ 2 - 1) * F₂ (diskCoshDist 0 z) +
        2 * diskCoshDist 0 z * F₁ (diskCoshDist 0 z)) 0 :=
      ((hXc.pow 2).sub continuousAt_const).mul (hF₂c.comp hXc) |>.add
        ((continuousAt_const.mul hXc).mul (hF₁c.comp hXc))
    have hR' := hR.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    refine tendsto_nhds_unique hL (hR'.congr' ?_)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hD] with w hw0 hwD
    exact (hoff w hwD hw0).symm

/-- `rem:linear-model` (sharpness) helper (S3, the explicit family): with `x = cosh d(0, ·)`,
`t_n = ∑_{j<n} x^{-(2j+2)}/(2j+3)` and `σ_n = n x^{-(2n+2)}` are linear-model data on every
plane. -/
theorem s10_rls_data (n : ℕ) {ι : ℂ → ℂ × ℝ} (hι : IsPlaneEmbedding ι) {P : ℂ × ℝ}
    (hP : P ∈ UHS) :
    IsLinearModelData ι P (fun z => (n : ℝ) * (diskCoshDist 0 z ^ (2 * n + 2))⁻¹)
      (fun z => ∑ j ∈ Finset.range n, (diskCoshDist 0 z ^ (2 * j + 2))⁻¹ / (2 * (j : ℝ) + 3)) := by
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hX1 : ∀ z ∈ unitDisc, 1 ≤ diskCoshDist 0 z := fun z hz => s10_one_le_diskCoshDist h0 hz
  have hX : ContDiffOn ℝ ∞ (diskCoshDist 0) unitDisc := by
    have hden : ∀ z ∈ unitDisc, (1 - ‖(0 : ℂ)‖ ^ 2) * (1 - ‖z‖ ^ 2) ≠ 0 := fun z hz => by
      have := mem_ball_zero_iff.mp hz
      rw [norm_zero]
      have : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      positivity
    have hn : ContDiff ℝ ∞ fun z : ℂ => ‖z‖ ^ 2 := contDiff_norm_sq ℝ
    have hn' : ContDiff ℝ ∞ fun z : ℂ => ‖0 - z‖ ^ 2 :=
      (contDiff_norm_sq ℝ).comp (contDiff_const.sub contDiff_id)
    show ContDiffOn ℝ ∞ (fun z : ℂ => 1 + 2 * ‖0 - z‖ ^ 2 / ((1 - ‖(0 : ℂ)‖ ^ 2) * (1 - ‖z‖ ^ 2)))
      unitDisc
    exact contDiffOn_const.add ((contDiffOn_const.mul hn'.contDiffOn).div
      (contDiffOn_const.mul (contDiffOn_const.sub hn.contDiffOn)) hden)
  have hinv1 : ∀ z ∈ unitDisc, ∀ k : ℕ, 0 < (diskCoshDist 0 z ^ k)⁻¹ ∧
      (diskCoshDist 0 z ^ k)⁻¹ ≤ 1 := fun z hz k => by
    have h1 := one_le_pow₀ (n := k) (hX1 z hz)
    exact ⟨inv_pos.mpr (by linarith), inv_le_one_of_one_le₀ h1⟩
  obtain ⟨hC, hL⟩ := s10_rls_lap (fun x hx => (s10_rls_ode n hx).1) (fun x hx => (s10_rls_ode n hx).2.1)
    (continuousOn_finsetSum _ fun j _ => continuousOn_const.mul
      ((continuous_pow _).continuousOn.inv₀ fun x hx => pow_ne_zero _ (ne_of_gt hx)))
  refine ⟨hι, hP, ?_, fun z hz => ?_, ⟨n, fun z hz => ?_⟩, hC, ⟨n, fun z hz => ?_⟩, fun z hz => ?_⟩
  · exact contDiffOn_const.mul ((hX.pow _).inv fun z hz => pow_ne_zero _ (by linarith [hX1 z hz]))
  · exact mul_nonneg (Nat.cast_nonneg n) (hinv1 z hz _).1.le
  · have := (hinv1 z hz (2 * n + 2)).2
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  · have hterm : ∀ j ∈ Finset.range n, 0 ≤ (diskCoshDist 0 z ^ (2 * j + 2))⁻¹ / (2 * (j : ℝ) + 3) ∧
        (diskCoshDist 0 z ^ (2 * j + 2))⁻¹ / (2 * (j : ℝ) + 3) ≤ 1 := fun j _ => by
      have h := hinv1 z hz (2 * j + 2)
      have h3 : (1 : ℝ) ≤ 2 * (j : ℝ) + 3 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
      refine ⟨div_nonneg h.1.le (by linarith), ?_⟩
      rw [div_le_one (by linarith)]
      linarith [h.2]
    rw [abs_of_nonneg (Finset.sum_nonneg fun j hj => (hterm j hj).1)]
    calc ∑ j ∈ Finset.range n, (diskCoshDist 0 z ^ (2 * j + 2))⁻¹ / (2 * (j : ℝ) + 3)
        ≤ ∑ j ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun j hj => (hterm j hj).2
      _ = n := by simp
  · rw [hL z hz]
    have hid := (s10_rls_ode n (show 0 < diskCoshDist 0 z by linarith [hX1 z hz])).2.2
    linear_combination -hid

/-- `rem:linear-model` (sharpness) helper (S4, concentration): for `0 < κ ≤ 1` continuous on `𝔻`
and `0 < δ < 1`, the weights `κ σ_n` concentrate on `|z| < δ`: for some `n`, their total mass is
positive and finite and the mass of `|z| ≥ δ` is at most `η` times it. -/
theorem s10_rls_conc {κ : ℂ → ℝ} (hκ : ContinuousOn κ unitDisc) (hκ0 : ∀ z ∈ unitDisc, 0 < κ z)
    (hκ1 : ∀ z, κ z ≤ 1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {η : ℝ} (hη : 0 < η) :
    ∃ n : ℕ,
      0 < ∫⁻ z, ENNReal.ofReal (κ z * ((n : ℝ) * (diskCoshDist 0 z ^ (2 * n + 2))⁻¹))
        ∂diskHypArea ∧
      ∫⁻ z, ENNReal.ofReal (κ z * ((n : ℝ) * (diskCoshDist 0 z ^ (2 * n + 2))⁻¹))
        ∂diskHypArea < ⊤ ∧
      ∫⁻ z, (ball (0 : ℂ) δ)ᶜ.indicator
          (fun z => ENNReal.ofReal (κ z * ((n : ℝ) * (diskCoshDist 0 z ^ (2 * n + 2))⁻¹))) z
          ∂diskHypArea ≤
        ENNReal.ofReal η * ∫⁻ z, ENNReal.ofReal (κ z * ((n : ℝ) * (diskCoshDist 0 z ^ (2 * n + 2))⁻¹))
          ∂diskHypArea := by
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hX1 : ∀ z ∈ unitDisc, 1 ≤ diskCoshDist 0 z := fun z hz => s10_one_le_diskCoshDist h0 hz
  have hXf : ∀ z, diskCoshDist 0 z = 1 + 2 * ‖z‖ ^ 2 / (1 - ‖z‖ ^ 2) := fun z => by
    show 1 + 2 * ‖0 - z‖ ^ 2 / ((1 - ‖(0 : ℂ)‖ ^ 2) * (1 - ‖z‖ ^ 2)) = _
    simp only [zero_sub, norm_neg, norm_zero]
    ring
  have hmono : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v < 1 → 2 * u / (1 - u) ≤ 2 * v / (1 - v) :=
    fun u v hu huv hv => by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = δ / 2 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hrδ : r < δ := by rw [hr]; linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 + 2 * δ ^ 2 / (1 - δ ^ 2) := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = 1 + 2 * r ^ 2 / (1 - r ^ 2) := ⟨_, rfl⟩
  have hδ2 : δ ^ 2 < 1 := by nlinarith
  have hr2 : r ^ 2 < δ ^ 2 := by nlinarith
  have hc'1 : 1 ≤ c' := by
    rw [hc']
    have : 0 ≤ 2 * r ^ 2 / (1 - r ^ 2) := div_nonneg (by positivity) (by linarith)
    linarith
  have hcc : c' < c := by
    rw [hc, hc', add_lt_add_iff_left, div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hc0 : 0 < c := by linarith
  have hc'0 : 0 < c' := by linarith
  -- `x ≥ c` off `ball 0 δ`, `x ≤ c'` on `ball 0 r`
  have hXc : ∀ z ∈ unitDisc, z ∉ ball (0 : ℂ) δ → c ≤ diskCoshDist 0 z := fun z hz hzb => by
    have h1 : δ ≤ ‖z‖ := by
      rw [mem_ball_zero_iff, not_lt] at hzb
      exact hzb
    have h2 := mem_ball_zero_iff.mp hz
    rw [hXf, hc, add_le_add_iff_left]
    exact hmono _ _ (sq_nonneg δ) (pow_le_pow_left₀ hδ.le h1 2) (by nlinarith [norm_nonneg z])
  have hXc' : ∀ z ∈ ball (0 : ℂ) r, diskCoshDist 0 z ≤ c' := fun z hz => by
    have h1 := mem_ball_zero_iff.mp hz
    rw [hXf, hc', add_le_add_iff_left]
    exact hmono _ _ (sq_nonneg _) (pow_le_pow_left₀ (norm_nonneg z) h1.le 2) (by linarith)
  have hsub : ball (0 : ℂ) r ⊆ unitDisc := ball_subset_ball (by linarith)
  -- the minimum `k` of `κ` on `closedBall 0 r`
  have hcsub : closedBall (0 : ℂ) r ⊆ unitDisc := closedBall_subset_ball (by linarith)
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_closedBall (0 : ℂ) r).exists_isMinOn
    (nonempty_closedBall.mpr hr0.le) (hκ.mono hcsub)
  obtain ⟨k, hk⟩ : ∃ k, k = κ z₀ := ⟨_, rfl⟩
  have hk0 : 0 < k := hk ▸ hκ0 z₀ (hcsub hz₀)
  have hkle : ∀ z ∈ ball (0 : ℂ) r, k ≤ κ z := fun z hz =>
    hk ▸ hmin (ball_subset_closedBall hz)
  have hae : ∀ᵐ z ∂diskHypArea, z ∈ unitDisc := by
    show ∀ᵐ z ∂(volume.restrict unitDisc).withDensity
      (fun z => ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2)), z ∈ unitDisc
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_ball)
  -- `A = ∫ x⁻² dâ < ∞`
  obtain ⟨A, hA⟩ : ∃ A, A = ∫⁻ z, ENNReal.ofReal ((diskCoshDist 0 z ^ 2)⁻¹) ∂diskHypArea :=
    ⟨_, rfl⟩
  have hAfin : A ≠ ⊤ := by
    have hm : Measurable fun z => ENNReal.ofReal ((diskCoshDist 0 z ^ 2)⁻¹) := by
      unfold diskCoshDist
      fun_prop
    have hd : Measurable fun z : ℂ => ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2) := by fun_prop
    have h := lintegral_withDensity_eq_lintegral_mul (volume.restrict unitDisc) hd hm
    have hle : ∫⁻ z, ENNReal.ofReal ((diskCoshDist 0 z ^ 2)⁻¹) ∂diskHypArea ≤
        ∫⁻ _ in unitDisc, ENNReal.ofReal 4 := by
      show ∫⁻ z, ENNReal.ofReal ((diskCoshDist 0 z ^ 2)⁻¹) ∂(volume.restrict unitDisc).withDensity
        (fun z => ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2)) ≤ _
      rw [h]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem hD] with z hz
      have h2 := mem_ball_zero_iff.mp hz
      have hu : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      simp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hXf]
      have e : (2 / (1 - ‖z‖ ^ 2)) ^ 2 * ((1 + 2 * ‖z‖ ^ 2 / (1 - ‖z‖ ^ 2)) ^ 2)⁻¹ =
          4 / (1 + ‖z‖ ^ 2) ^ 2 := by
        field_simp
        ring
      rw [e, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (‖z‖ ^ 2), norm_nonneg z]
    rw [hA]
    refine ne_top_of_le_ne_top ?_ hle
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  -- `V = â(ball 0 r)`, `0 < V < ∞`
  obtain ⟨V, hV⟩ : ∃ V, V = diskHypArea (ball (0 : ℂ) r) := ⟨_, rfl⟩
  have hVpos : V ≠ 0 := by
    have hV' : V = ∫⁻ z in ball (0 : ℂ) r, ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2)
        ∂(volume.restrict unitDisc) := by
      rw [hV]
      exact withDensity_apply _ measurableSet_ball
    rw [hV', Measure.restrict_restrict measurableSet_ball, inter_eq_left.mpr hsub]
    refine (lt_of_lt_of_le (Metric.measure_ball_pos volume (0 : ℂ) hr0) ?_).ne'
    calc volume (ball (0 : ℂ) r) = ∫⁻ _ in ball (0 : ℂ) r, 1 := (setLIntegral_one _).symm
      _ ≤ _ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        have h2 := mem_ball_zero_iff.mp (hsub hz)
        have hu : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
        have hu1 : 1 - ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
        rw [← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_pow, le_div_iff₀ (by positivity)]
        nlinarith
  have hVfin : V ≠ ⊤ := by
    have hle : V ≤ ENNReal.ofReal (c' ^ 2) * A := by
      rw [hV, hA, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_indicator_one measurableSet_ball]
      refine lintegral_mono_ae ?_
      filter_upwards [hae] with z hz
      by_cases hzb : z ∈ ball (0 : ℂ) r
      · rw [indicator_of_mem hzb, Pi.one_apply, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := hX1 z hz
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
        exact pow_le_pow_left₀ (by linarith) (hXc' z hzb) 2
      · rw [indicator_of_notMem hzb]
        exact zero_le
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin) hle
  have hV0 : 0 < V.toReal := ENNReal.toReal_pos hVpos hVfin
  -- choice of `n`
  have hq0 : 0 ≤ (c' / c) ^ 2 := sq_nonneg _
  have hq1 : (c' / c) ^ 2 < 1 :=
    pow_lt_one₀ (div_nonneg hc'0.le hc0.le) ((div_lt_one hc0).mpr hcc) (by norm_num)
  have ht : Tendsto (fun n : ℕ => c' ^ 2 * ((c' / c) ^ 2) ^ n * A.toReal) atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (c' ^ 2)).mul_const
      A.toReal
    rwa [mul_zero, zero_mul] at h
  obtain ⟨n, hn1, hn⟩ := ((eventually_ge_atTop 1).and
    (ht.eventually (gt_mem_nhds (show (0 : ℝ) < η * k * V.toReal by positivity)))).exists
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  refine ⟨n, ?_⟩
  -- lower bound `I ≥ n k c'^{-(2n+2)} V`
  have hlow : ENNReal.ofReal (n * k * (c' ^ (2 * n + 2))⁻¹) * V ≤
      ∫⁻ z, ENNReal.ofReal (κ z * ((n : ℝ) * (diskCoshDist 0 z ^ (2 * n + 2))⁻¹)) ∂diskHypArea := by
    rw [hV, ← lintegral_indicator_const measurableSet_ball]
    refine lintegral_mono fun z => ?_
    by_cases hzb : z ∈ ball (0 : ℂ) r
    · rw [indicator_of_mem hzb]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := hX1 z (hsub hzb)
      have hinv : (c' ^ (2 * n + 2))⁻¹ ≤ (diskCoshDist 0 z ^ (2 * n + 2))⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (hXc' z hzb) _)
      have hk' := hkle z hzb
      have hp : 0 ≤ (c' ^ (2 * n + 2))⁻¹ := by positivity
      calc (n : ℝ) * k * (c' ^ (2 * n + 2))⁻¹ = (n : ℝ) * (k * (c' ^ (2 * n + 2))⁻¹) := by ring
        _ ≤ (n : ℝ) * (κ z * (diskCoshDist 0 z ^ (2 * n + 2))⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hk' hinv hp (by linarith)) hn0.le
        _ = κ z * ((n : ℝ) * (diskCoshDist 0 z ^ (2 * n + 2))⁻¹) := by ring
    · rw [indicator_of_notMem hzb]
      exact zero_le
  have hIpos : 0 < ∫⁻ z, ENNReal.ofReal (κ z * ((n : ℝ) * (diskCoshDist 0 z ^ (2 * n + 2))⁻¹))
      ∂diskHypArea :=
    lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' hVpos) hlow
  refine ⟨hIpos, ?_, ?_⟩
  · -- `I ≤ n A`
    have hle : ∫⁻ z, ENNReal.ofReal (κ z * ((n : ℝ) * (diskCoshDist 0 z ^ (2 * n + 2))⁻¹))
        ∂diskHypArea ≤ ENNReal.ofReal n * A := by
      rw [hA, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      filter_upwards [hae] with z hz
      rw [← ENNReal.ofReal_mul hn0.le]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := hX1 z hz
      have hinv : (diskCoshDist 0 z ^ (2 * n + 2))⁻¹ ≤ (diskCoshDist 0 z ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 (by omega))
      calc κ z * ((n : ℝ) * (diskCoshDist 0 z ^ (2 * n + 2))⁻¹)
          ≤ 1 * ((n : ℝ) * (diskCoshDist 0 z ^ (2 * n + 2))⁻¹) :=
            mul_le_mul_of_nonneg_right (hκ1 z) (by positivity)
        _ ≤ (n : ℝ) * (diskCoshDist 0 z ^ 2)⁻¹ := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_left hinv hn0.le
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hAfin.lt_top)
  · -- the mass off `ball 0 δ`
    have hup : ∫⁻ z, (ball (0 : ℂ) δ)ᶜ.indicator
        (fun z => ENNReal.ofReal (κ z * ((n : ℝ) * (diskCoshDist 0 z ^ (2 * n + 2))⁻¹))) z
        ∂diskHypArea ≤ ENNReal.ofReal (n * (c ^ (2 * n))⁻¹) * A := by
      rw [hA, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      filter_upwards [hae] with z hz
      by_cases hzb : z ∈ ball (0 : ℂ) δ
      · rw [indicator_of_notMem (notMem_compl_iff.mpr hzb)]
        exact zero_le
      · rw [indicator_of_mem hzb, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := hX1 z hz
        have hcz := hXc z hz hzb
        have hpow : c ^ (2 * n) * diskCoshDist 0 z ^ 2 ≤ diskCoshDist 0 z ^ (2 * n + 2) := by
          rw [pow_add]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0.le hcz _) (by positivity)
        have hinv : (diskCoshDist 0 z ^ (2 * n + 2))⁻¹ ≤
            (c ^ (2 * n))⁻¹ * (diskCoshDist 0 z ^ 2)⁻¹ := by
          rw [← mul_inv]
          exact inv_anti₀ (by positivity) hpow
        calc κ z * ((n : ℝ) * (diskCoshDist 0 z ^ (2 * n + 2))⁻¹)
            ≤ 1 * ((n : ℝ) * (diskCoshDist 0 z ^ (2 * n + 2))⁻¹) :=
              mul_le_mul_of_nonneg_right (hκ1 z) (by positivity)
          _ ≤ (n : ℝ) * ((c ^ (2 * n))⁻¹ * (diskCoshDist 0 z ^ 2)⁻¹) := by
              rw [one_mul]
              exact mul_le_mul_of_nonneg_left hinv hn0.le
          _ = (n : ℝ) * (c ^ (2 * n))⁻¹ * (diskCoshDist 0 z ^ 2)⁻¹ := by ring
    refine hup.trans (le_trans ?_ (mul_le_mul_right hlow _))
    have e : (c ^ (2 * n))⁻¹ = c' ^ 2 * ((c' / c) ^ 2) ^ n * (c' ^ (2 * n + 2))⁻¹ := by
      rw [div_pow, div_pow, ← pow_mul, ← pow_mul]
      field_simp
      ring
    have hreal : (n : ℝ) * (c ^ (2 * n))⁻¹ * A.toReal ≤
        η * ((n : ℝ) * k * (c' ^ (2 * n + 2))⁻¹ * V.toReal) := by
      rw [e]
      have hp : 0 ≤ (n : ℝ) * (c' ^ (2 * n + 2))⁻¹ := by positivity
      calc (n : ℝ) * (c' ^ 2 * ((c' / c) ^ 2) ^ n * (c' ^ (2 * n + 2))⁻¹) * A.toReal
          = ((n : ℝ) * (c' ^ (2 * n + 2))⁻¹) * (c' ^ 2 * ((c' / c) ^ 2) ^ n * A.toReal) := by ring
        _ ≤ ((n : ℝ) * (c' ^ (2 * n + 2))⁻¹) * (η * k * V.toReal) :=
            mul_le_mul_of_nonneg_left hn.le hp
        _ = η * ((n : ℝ) * k * (c' ^ (2 * n + 2))⁻¹ * V.toReal) := by ring
    rw [← ENNReal.ofReal_toReal hAfin, ← ENNReal.ofReal_toReal hVfin,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hη.le]
    exact ENNReal.ofReal_le_ofReal hreal

/-- `rem:linear-model` (sharpness) helper (S5): the ratio `(𝔊 * κ_Π)(q)/κ_Π(q)` is continuous at
`q = 0` (dominated convergence in the polar representation `s10_prb_rep`). -/
theorem s10_rls_cont {ι : ℂ → ℂ × ℝ} (hι : IsPlaneEmbedding ι) {P : ℂ × ℝ} (hP : P ∈ UHS) :
    Tendsto (fun q => (resolventConvDisk (fun b => ambKernel P (ι b)) q).toReal / ambKernel P (ι q))
      (𝓝 0) (𝓝 ((resolventConvDisk (fun b => ambKernel P (ι b)) 0).toReal / ambKernel P (ι 0))) := by
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hD : unitDisc ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds h0
  have hKc := s10_rlm_kernel_cont hι hP
  have hκ0 : ambKernel P (ι 0) ≠ 0 := by
    unfold ambKernel
    have := Real.cosh_pos (hdist P (ι 0) / 2)
    positivity
  have hκ1 : ∀ Q, 0 ≤ ambKernel P Q ∧ ambKernel P Q ≤ 1 := fun Q => by
    unfold ambKernel
    have h1 := Real.one_le_cosh (hdist P Q / 2)
    have h2 : (Real.cosh (hdist P Q / 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    have h3 : 0 ≤ (Real.cosh (hdist P Q / 2))⁻¹ := by positivity
    exact ⟨by positivity, pow_le_one₀ h3 h2⟩
  have hfin : resolventConvDisk (fun b => ambKernel P (ι b)) 0 ≠ ⊤ :=
    ne_top_of_lt (thm_plane_ratio_b ι hι P hP 0 h0).2
  have hw : ∀ s : ℝ, 0 < s → ∀ θ : ℝ,
      (Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I) ∈ unitDisc := fun s hs θ => by
    have ht0 : 0 < Real.tanh (s / 2) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
    refine mem_ball_zero_iff.mpr ?_
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht0]
    exact Real.tanh_lt_one _
  have hdc : ∀ q ∈ unitDisc, ContinuousOn (diskMob q) unitDisc := fun q hq z hz => by
    have hq' : ‖-q‖ < 1 := by rw [norm_neg]; exact mem_ball_zero_iff.mp hq
    rw [s10_prb_mob_eq]
    exact (hasDerivAt_blaschke hq' (mem_ball_zero_iff.mp hz)).continuousAt.continuousWithinAt
  -- continuity of the circle means in the centre
  have hmc : ∀ s : ℝ, 0 < s → ContinuousAt (fun q => circleMean (fun b => ambKernel P (ι b)) q s) 0 :=
    fun s hs => by
      unfold circleMean
      refine continuousAt_const.mul (intervalIntegral.continuousAt_of_dominated_interval
        (bound := fun _ => 1) ?_ ?_ intervalIntegrable_const ?_)
      · filter_upwards [hD] with q hq
        exact ((hKc.comp (hdc q hq) (s10_pr_mob hq).1).comp_continuous (by fun_prop)
          (hw s hs)).aestronglyMeasurable
      · filter_upwards [hD] with q hq
        refine Eventually.of_forall fun θ _ => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (hκ1 _).1]
        exact (hκ1 _).2
      · refine Eventually.of_forall fun θ _ => ?_
        have hm0 : diskMob 0 ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I)) =
            (Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I) := by
          show (_ + 0) / (1 + conj 0 * _) = _
          simp
        have hq : ContinuousAt (fun q : ℂ =>
            diskMob q ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I))) 0 := by
          show ContinuousAt (fun q : ℂ => ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I) + q) /
            (1 + conj q * ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I)))) 0
          exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)
        exact ContinuousAt.comp_of_eq (hKc.continuousAt (isOpen_ball.mem_nhds (hw s hs θ))) hq hm0
  have hconv : Tendsto (fun q => resolventConvDisk (fun b => ambKernel P (ι b)) q) (𝓝 0)
      (𝓝 (resolventConvDisk (fun b => ambKernel P (ι b)) 0)) := by
    have hrep : (fun q => ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (resolventG s * (2 * π * Real.sinh s) *
        circleMean (fun b => ambKernel P (ι b)) q s)) =ᶠ[𝓝 0]
        fun q => resolventConvDisk (fun b => ambKernel P (ι b)) q := by
      filter_upwards [hD] with q hq
      exact (s10_prb_rep hι hP hq).symm
    rw [s10_prb_rep hι hP h0]
    refine (tendsto_congr' hrep).mp (tendsto_lintegral_filter_of_dominated_convergence
      (fun s => ENNReal.ofReal (resolventG s * (2 * π * Real.sinh s))) ?_ ?_ ?_ ?_)
    · filter_upwards [hD] with q hq
      exact ENNReal.measurable_ofReal.comp ((s10_prb_meas_G.mul
        (by fun_prop : Continuous fun s : ℝ => 2 * π * Real.sinh s).measurable).mul
          (s10_prb_mean_cont hι hP hq).measurable)
    · filter_upwards [hD] with q hq
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs' : (0 : ℝ) < s := hs
      refine ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right
        (mul_pos (s10_resolventG_pos hs') (by have := Real.sinh_pos_iff.mpr hs'; positivity)).le ?_)
      unfold circleMean
      by_cases hi : IntervalIntegrable (fun θ : ℝ => ambKernel P (ι (diskMob q
          ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I))))) volume 0 (2 * π)
      · have hle := intervalIntegral.integral_mono_on (by positivity) hi
          (intervalIntegrable_const (c := (1 : ℝ))) (fun θ _ => (hκ1 _).2)
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at hle
        calc (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ambKernel P (ι (diskMob q
              ((Real.tanh (s / 2) : ℂ) * Complex.exp ((θ : ℂ) * I))))
            ≤ (2 * π)⁻¹ * (2 * π) := mul_le_mul_of_nonneg_left hle (by positivity)
          _ = 1 := inv_mul_cancel₀ (by positivity)
      · rw [intervalIntegral.integral_undef hi, mul_zero]
        exact zero_le_one
    · exact (lem_plane_green_f.1.setLIntegral_lt_top).ne
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact ENNReal.tendsto_ofReal (tendsto_const_nhds.mul (hmc s hs).tendsto)
  exact ((ENNReal.tendsto_toReal hfin).comp hconv).div
    (hKc.continuousAt hD).tendsto hκ0

/-- `rem:linear-model` (sharpness) helper (S6, recentring): `ι ∘ diskMob c` is again a plane
embedding, and its `𝔊 * κ_Π` at `0` is that of `ι` at `c`. -/
theorem s10_rls_recenter {ι : ℂ → ℂ × ℝ} (hι : IsPlaneEmbedding ι) (P : ℂ × ℝ) (hP : P ∈ UHS)
    {c : ℂ} (hc : c ∈ unitDisc) :
    IsPlaneEmbedding (fun z => ι (diskMob c z)) ∧
      resolventConvDisk (fun b => ambKernel P (ι (diskMob c b))) 0 =
        resolventConvDisk (fun b => ambKernel P (ι b)) c := by
  obtain ⟨hmap, hmob⟩ := s10_pr_mob hc
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hd0 : diskMob c 0 = c := by simp [diskMob]
  refine ⟨⟨fun z hz => hι.1 (hmap hz), fun a ha b hb => ?_⟩, ?_⟩
  · show hdist (ι (diskMob c a)) (ι (diskMob c b)) = diskDist a b
    rw [hι.2 _ (hmap ha) _ (hmap hb)]
    show Real.arcosh (diskCoshDist (diskMob c a) (diskMob c b)) = Real.arcosh (diskCoshDist a b)
    rw [hmob a ha b hb]
  classical
  have hD : MeasurableSet unitDisc := measurableSet_ball
  obtain ⟨κm, hκm⟩ : ∃ κm : ℂ → ℝ, κm = unitDisc.piecewise (fun b => ambKernel P (ι b)) 0 :=
    ⟨_, rfl⟩
  have hκmm : Measurable κm := by
    rw [hκm]
    exact (s10_rlm_kernel_cont hι hP).measurable_piecewise continuousOn_const hD
  have hκe : ∀ z ∈ unitDisc, κm z = ambKernel P (ι z) := fun z hz => by
    rw [hκm]
    exact piecewise_eq_of_mem _ _ _ hz
  have hae : ∀ᵐ z ∂diskHypArea, z ∈ unitDisc := by
    show ∀ᵐ z ∂(volume.restrict unitDisc).withDensity
      (fun z => ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2)), z ∈ unitDisc
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_ball)
  have hdm : Measurable fun b : ℂ => diskDist c b := by
    show Measurable fun b : ℂ => Real.log (diskCoshDist c b + √(diskCoshDist c b ^ 2 - 1))
    unfold diskCoshDist
    fun_prop
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℝ≥0∞, g = fun b => ENNReal.ofReal (resolventG (diskDist c b) * κm b) :=
    ⟨_, rfl⟩
  have hgm : Measurable g := by
    rw [hg]
    exact ENNReal.measurable_ofReal.comp ((s10_prb_meas_G.comp hdm).mul hκmm)
  unfold resolventConvDisk
  calc ∫⁻ b, ENNReal.ofReal (resolventG (diskDist 0 b) * ambKernel P (ι (diskMob c b))) ∂diskHypArea
      = ∫⁻ b, g (diskMob c b) ∂diskHypArea := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with b hb
        rw [hg]
        beta_reduce
        rw [hκe _ (hmap hb)]
        have h := hmob 0 h0 b hb
        rw [hd0] at h
        have hdd : diskDist c (diskMob c b) = diskDist 0 b := by
          show Real.arcosh (diskCoshDist c (diskMob c b)) = Real.arcosh (diskCoshDist 0 b)
          rw [h]
        rw [hdd]
    _ = ∫⁻ b, g b ∂diskHypArea := s10_prb_area_mob hc hgm
    _ = ∫⁻ b, ENNReal.ofReal (resolventG (diskDist c b) * ambKernel P (ι b)) ∂diskHypArea := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with b hb
        rw [hg]
        beta_reduce
        rw [hκe b hb]

/-- `rem:linear-model` (sharpness) helper (S7): on a fixed plane with `R₀ = (𝔊 * κ_Π)(0)/κ_Π(0)`,
the linear model attains every ratio `∫ κ_Π t / ∫ κ_Π σ` within `ε` of `2 R₀` (sources
concentrating at `0`, by S3–S5 and Remark 10.8). -/
theorem s10_rls_main {ι : ℂ → ℂ × ℝ} (hι : IsPlaneEmbedding ι) {P : ℂ × ℝ} (hP : P ∈ UHS)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ σ t : ℂ → ℝ, IsLinearModelData ι P σ t ∧
      0 < ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * σ z) ∂diskHypArea ∧
      ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * σ z) ∂diskHypArea < ⊤ ∧
      ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * t z) ∂diskHypArea ≤
        ENNReal.ofReal (2 * ((resolventConvDisk (fun b => ambKernel P (ι b)) 0).toReal /
          ambKernel P (ι 0)) + ε) * ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * σ z) ∂diskHypArea ∧
      ENNReal.ofReal (2 * ((resolventConvDisk (fun b => ambKernel P (ι b)) 0).toReal /
          ambKernel P (ι 0)) - ε) * ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * σ z) ∂diskHypArea ≤
        ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * t z) ∂diskHypArea := by
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, R₀ = (resolventConvDisk (fun b => ambKernel P (ι b)) 0).toReal /
      ambKernel P (ι 0) := ⟨_, rfl⟩
  rw [← hR₀]
  have hRb := s10_prc_bounds hι hP h0
  rw [← hR₀] at hRb
  have hκ0 : ∀ z, 0 < ambKernel P (ι z) := fun z => by
    unfold ambKernel
    have := Real.cosh_pos (hdist P (ι z) / 2)
    positivity
  have hκ1 : ∀ z, ambKernel P (ι z) ≤ 1 := fun z => by
    unfold ambKernel
    have h1 := Real.one_le_cosh (hdist P (ι z) / 2)
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ h1)
  -- the ratio is within `ε/4` of `R₀` on a ball `B = ball 0 δ`
  have hε4 : 0 < ε / 4 := by linarith
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.eventually_nhds_iff.mp
    ((s10_rls_cont hι hP).eventually (Metric.ball_mem_nhds _ hε4))
  rw [← hR₀] at hball
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min δ₀ (1 / 2) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min hδ₀ (by norm_num)
  have hδ1 : δ < 1 := by rw [hδ]; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hBsub : ball (0 : ℂ) δ ⊆ unitDisc := ball_subset_ball hδ1.le
  have hconv : ∀ q ∈ unitDisc, resolventConvDisk (fun b => ambKernel P (ι b)) q =
      ENNReal.ofReal ((resolventConvDisk (fun b => ambKernel P (ι b)) q).toReal /
        ambKernel P (ι q) * ambKernel P (ι q)) := fun q hq => by
    rw [div_mul_cancel₀ _ (hκ0 q).ne', ENNReal.ofReal_toReal
      (ne_top_of_lt (thm_plane_ratio_b ι hι P hP q hq).2)]
  have hnear : ∀ q ∈ ball (0 : ℂ) δ,
      |(resolventConvDisk (fun b => ambKernel P (ι b)) q).toReal / ambKernel P (ι q) - R₀| <
        ε / 4 := fun q hq => by
    have h := hball (lt_of_lt_of_le (mem_ball.mp hq) (by rw [hδ]; exact min_le_left _ _))
    rw [Real.dist_eq] at h
    exact h
  -- concentration
  obtain ⟨n, hIpos, hIfin, hJ⟩ := s10_rls_conc (κ := fun b => ambKernel P (ι b))
    (s10_rlm_kernel_cont hι hP) (fun z _ => hκ0 z) hκ1 hδ0 hδ1 hε4
  obtain ⟨σ, hσ⟩ : ∃ σ : ℂ → ℝ, σ = fun z => (n : ℝ) * (diskCoshDist 0 z ^ (2 * n + 2))⁻¹ :=
    ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℂ → ℝ, t = fun z =>
      ∑ j ∈ Finset.range n, (diskCoshDist 0 z ^ (2 * j + 2))⁻¹ / (2 * (j : ℝ) + 3) := ⟨_, rfl⟩
  have hdat : IsLinearModelData ι P σ t := by
    rw [hσ, ht]
    exact s10_rls_data n hι hP
  have hσ0 : ∀ z ∈ unitDisc, 0 ≤ σ z := hdat.2.2.2.1
  obtain ⟨I, hI⟩ : ∃ I, I = ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * σ z) ∂diskHypArea :=
    ⟨_, rfl⟩
  have hIe : ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * ((n : ℝ) *
      (diskCoshDist 0 z ^ (2 * n + 2))⁻¹)) ∂diskHypArea = I := by
    rw [hI, hσ]
  have hJe : ∫⁻ z in (ball (0 : ℂ) δ)ᶜ, ENNReal.ofReal (ambKernel P (ι z) * σ z) ∂diskHypArea ≤
      ENNReal.ofReal (ε / 4) * I := by
    rw [← lintegral_indicator measurableSet_ball.compl, ← hIe, hσ]
    exact hJ
  rw [hIe] at hIpos hIfin
  refine ⟨σ, t, hdat, hI ▸ hIpos, hI ▸ hIfin, ?_⟩
  rw [← hI]
  have hae : ∀ᵐ z ∂diskHypArea, z ∈ unitDisc := by
    show ∀ᵐ z ∂(volume.restrict unitDisc).withDensity
      (fun z => ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2)), z ∈ unitDisc
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_ball)
  have hT := (rem_linear_model ι P σ t hdat).1
  rw [hT]
  -- split `2 ∫ σ (𝔊 * κ)` over `B` and its complement
  have hsplit := lintegral_add_compl (μ := diskHypArea)
    (fun z => ENNReal.ofReal (σ z) * resolventConvDisk (fun b => ambKernel P (ι b)) z)
    (measurableSet_ball (x := (0 : ℂ)) (ε := δ))
  have hBle : ∫⁻ z in ball (0 : ℂ) δ, ENNReal.ofReal (ambKernel P (ι z) * σ z) ∂diskHypArea ≤ I := by
    rw [hI]
    exact setLIntegral_le_lintegral _ _
  have hBc : ∀ x : ℝ, 0 ≤ x → ∀ q ∈ unitDisc,
      2 * (ENNReal.ofReal (σ q) * ENNReal.ofReal (x * ambKernel P (ι q))) =
        ENNReal.ofReal (2 * x) * ENNReal.ofReal (ambKernel P (ι q) * σ q) := fun x hx q hq => by
    rw [← ENNReal.ofReal_mul (hσ0 q hq), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  constructor
  · -- upper bound
    have hup1 : 2 * ∫⁻ z in ball (0 : ℂ) δ, ENNReal.ofReal (σ z) *
        resolventConvDisk (fun b => ambKernel P (ι b)) z ∂diskHypArea ≤
        ENNReal.ofReal (2 * (R₀ + ε / 4)) * I := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
      refine le_trans ?_ (mul_le_mul_of_nonneg_left hBle zero_le)
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with q hq
      have hqD := hBsub hq
      have hx : 0 ≤ R₀ + ε / 4 := by linarith [hRb.1, Real.log_two_lt_d9]
      have hc := hconv q hqD
      have h := hnear q hq
      generalize (resolventConvDisk (fun b => ambKernel P (ι b)) q).toReal / ambKernel P (ι q) = Rq
        at hc h
      rw [← hBc _ hx q hqD, hc]
      have hk := (hκ0 q).le
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (ENNReal.ofReal_le_ofReal (by nlinarith [abs_lt.mp h])) zero_le) zero_le
    have hup2 : 2 * ∫⁻ z in (ball (0 : ℂ) δ)ᶜ, ENNReal.ofReal (σ z) *
        resolventConvDisk (fun b => ambKernel P (ι b)) z ∂diskHypArea ≤
        ∫⁻ z in (ball (0 : ℂ) δ)ᶜ, ENNReal.ofReal (ambKernel P (ι z) * σ z) ∂diskHypArea := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_of_ae hae] with q hq
      have hhi := (thm_plane_ratio_b ι hι P hP q hq).2
      calc 2 * (ENNReal.ofReal (σ q) * resolventConvDisk (fun b => ambKernel P (ι b)) q)
          ≤ 2 * (ENNReal.ofReal (σ q) * ENNReal.ofReal (1 / 2 * ambKernel P (ι q))) := by
            rw [one_div_mul_eq_div]
            gcongr
        _ = ENNReal.ofReal (ambKernel P (ι q) * σ q) := by
            rw [hBc _ (by norm_num) q hq]
            norm_num
    rw [← hsplit, mul_add]
    calc 2 * ∫⁻ z in ball (0 : ℂ) δ, ENNReal.ofReal (σ z) *
          resolventConvDisk (fun b => ambKernel P (ι b)) z ∂diskHypArea +
        2 * ∫⁻ z in (ball (0 : ℂ) δ)ᶜ, ENNReal.ofReal (σ z) *
          resolventConvDisk (fun b => ambKernel P (ι b)) z ∂diskHypArea
        ≤ ENNReal.ofReal (2 * (R₀ + ε / 4)) * I + ENNReal.ofReal (ε / 4) * I :=
          add_le_add hup1 (hup2.trans hJe)
      _ = ENNReal.ofReal (2 * (R₀ + ε / 4) + ε / 4) * I := by
          rw [← add_mul, ENNReal.ofReal_add (by linarith [hRb.1, Real.log_two_lt_d9]) hε4.le]
      _ ≤ ENNReal.ofReal (2 * R₀ + ε) * I :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by linarith)) zero_le
  · -- lower bound
    by_cases ha : 2 * R₀ - ε ≤ 0
    · rw [ENNReal.ofReal_of_nonpos ha, zero_mul]
      exact zero_le
    have ha' : 0 < 2 * R₀ - ε := lt_of_not_ge ha
    have hb : 0 ≤ R₀ - ε / 4 := by linarith
    have hlo1 : ENNReal.ofReal (2 * (R₀ - ε / 4)) *
        ∫⁻ z in ball (0 : ℂ) δ, ENNReal.ofReal (ambKernel P (ι z) * σ z) ∂diskHypArea ≤
        2 * ∫⁻ z in ball (0 : ℂ) δ, ENNReal.ofReal (σ z) *
          resolventConvDisk (fun b => ambKernel P (ι b)) z ∂diskHypArea := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with q hq
      have hqD := hBsub hq
      have hc := hconv q hqD
      have h := hnear q hq
      generalize (resolventConvDisk (fun b => ambKernel P (ι b)) q).toReal / ambKernel P (ι q) = Rq
        at hc h
      rw [← hBc _ hb q hqD, hc]
      have hk := (hκ0 q).le
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (ENNReal.ofReal_le_ofReal (by nlinarith [abs_lt.mp h])) zero_le) zero_le
    have hfinB : ∫⁻ z in ball (0 : ℂ) δ, ENNReal.ofReal (ambKernel P (ι z) * σ z) ∂diskHypArea ≠ ⊤ :=
      ne_top_of_le_ne_top hIfin.ne hBle
    have hfinC : ∫⁻ z in (ball (0 : ℂ) δ)ᶜ, ENNReal.ofReal (ambKernel P (ι z) * σ z)
        ∂diskHypArea ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIfin.ne) hJe
    have hIsum := lintegral_add_compl (μ := diskHypArea)
      (fun z => ENNReal.ofReal (ambKernel P (ι z) * σ z)) (measurableSet_ball (x := (0 : ℂ)) (ε := δ))
    rw [← hI] at hIsum
    -- real bookkeeping
    have hJr : (∫⁻ z in (ball (0 : ℂ) δ)ᶜ, ENNReal.ofReal (ambKernel P (ι z) * σ z)
        ∂diskHypArea).toReal ≤ ε / 4 * I.toReal := by
      have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIfin.ne) hJe
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε4.le] at h
    have hIr : I.toReal = (∫⁻ z in ball (0 : ℂ) δ, ENNReal.ofReal (ambKernel P (ι z) * σ z)
        ∂diskHypArea).toReal + (∫⁻ z in (ball (0 : ℂ) δ)ᶜ, ENNReal.ofReal (ambKernel P (ι z) * σ z)
        ∂diskHypArea).toReal := by
      rw [← hIsum, ENNReal.toReal_add hfinB hfinC]
    have hI0 : 0 ≤ I.toReal := ENNReal.toReal_nonneg
    have hkey : ENNReal.ofReal (2 * R₀ - ε) * I ≤ ENNReal.ofReal (2 * (R₀ - ε / 4)) *
        ∫⁻ z in ball (0 : ℂ) δ, ENNReal.ofReal (ambKernel P (ι z) * σ z) ∂diskHypArea := by
      rw [← ENNReal.ofReal_toReal hIfin.ne, ← ENNReal.ofReal_toReal hfinB,
        ← ENNReal.ofReal_mul ha'.le, ← ENNReal.ofReal_mul (by linarith)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hR1 := hRb.2
      have hb' : 0 ≤ 2 * (R₀ - ε / 4) := by linarith
      have hB' : (∫⁻ z in ball (0 : ℂ) δ, ENNReal.ofReal (ambKernel P (ι z) * σ z)
          ∂diskHypArea).toReal = I.toReal - (∫⁻ z in (ball (0 : ℂ) δ)ᶜ,
            ENNReal.ofReal (ambKernel P (ι z) * σ z) ∂diskHypArea).toReal := by linarith
      rw [hB']
      have h1 := mul_le_mul_of_nonneg_left hJr hb'
      have h2 : 0 ≤ ε / 4 * I.toReal * (2 - 2 * R₀ + ε / 2) :=
        mul_nonneg (mul_nonneg hε4.le hI0) (by linarith)
      nlinarith
    rw [← hsplit, mul_add]
    exact le_trans hkey (le_trans hlo1 le_self_add)

/-- **Remark 10.8**, `rem:linear-model`, `sec10-sharp.tex:379`: neither constant `2(1 - log 2)`
nor `1` can be improved within the linearized model. -/
theorem rem_linear_model_sharp (ε : ℝ) (hε : 0 < ε) :
    (∃ (ι : ℂ → ℂ × ℝ) (P : ℂ × ℝ) (σ t : ℂ → ℝ), IsLinearModelData ι P σ t ∧
      0 < ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * σ z) ∂diskHypArea ∧
      ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * σ z) ∂diskHypArea < ⊤ ∧
      ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * t z) ∂diskHypArea ≤
        ENNReal.ofReal (2 * (1 - Real.log 2) + ε) *
          ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * σ z) ∂diskHypArea) ∧
    (∃ (ι : ℂ → ℂ × ℝ) (P : ℂ × ℝ) (σ t : ℂ → ℝ), IsLinearModelData ι P σ t ∧
      0 < ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * σ z) ∂diskHypArea ∧
      ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * σ z) ∂diskHypArea < ⊤ ∧
      ENNReal.ofReal (1 - ε) * ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * σ z) ∂diskHypArea ≤
        ∫⁻ z, ENNReal.ofReal (ambKernel P (ι z) * t z) ∂diskHypArea) := by
  have hε2 : 0 < ε / 2 := by linarith
  have hι₀0 : ((((2 / (1 + ‖(0 : ℂ)‖ ^ 2) : ℝ) : ℂ) * 0, (1 - ‖(0 : ℂ)‖ ^ 2) / (1 + ‖(0 : ℂ)‖ ^ 2)) :
      ℂ × ℝ) = ((0 : ℂ), (1 : ℝ)) := by simp
  refine ⟨?_, ?_⟩
  · obtain ⟨d, hd⟩ := (s10_prc_inf.eventually
      (gt_mem_nhds (show 1 - Real.log 2 < 1 - Real.log 2 + ε / 4 by linarith))).exists
    obtain ⟨σ, t, hdat, hpos, hfin, hup, -⟩ :=
      s10_rls_main s10_prc_embed (show ((0 : ℂ), Real.exp d) ∈ UHS from Real.exp_pos d) hε2
    refine ⟨_, _, σ, t, hdat, hpos, hfin, hup.trans ?_⟩
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    rw [hι₀0]
    linarith
  · obtain ⟨ρ, hρ, hρ1⟩ := ((s10_prc_sup.eventually
      (lt_mem_nhds (show 1 / 2 - ε / 4 < 1 / 2 by linarith))).and
        (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num))).exists
    have hρD : (ρ : ℂ) ∈ unitDisc := by
      show (ρ : ℂ) ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ1.1]
      exact hρ1.2
    have hP1 : ((0 : ℂ), (1 : ℝ)) ∈ UHS := (show (0 : ℝ) < 1 from one_pos)
    obtain ⟨hι', hconv⟩ := s10_rls_recenter s10_prc_embed ((0 : ℂ), (1 : ℝ)) hP1 hρD
    obtain ⟨σ, t, hdat, hpos, hfin, -, hlo⟩ := s10_rls_main hι' hP1 hε2
    refine ⟨_, _, σ, t, hdat, hpos, hfin, le_trans ?_ hlo⟩
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    have hd0 : diskMob (ρ : ℂ) 0 = ρ := by simp [diskMob]
    rw [hconv, hd0]
    linarith

/-! ## §10.4 Global structure for small Schwarzian norms -/

/-- `lem:aw` helper (A): for a Riemann map `f : 𝔻 → Ω` with `s ≤ k/2` on `Ω`, the Schwarzian
`φ = S_f ∈ A∞(𝔻)` (Takhtajan–Teo) has `‖φ‖ ≤ 2k`. -/
theorem s10_aw_phi {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {k : ℝ} (hk : 0 ≤ k)
    (hs : ∀ w ∈ Ω, schwarzNorm Ω w ≤ k / 2) :
    (∀ z ∈ unitDisc, TakhtajanTeo.AInf.toFun (TakhtajanTeo.toAInf unitDisc (schwarzianHol f)) z =
      schwarzianHol f z) ∧ ‖TakhtajanTeo.toAInf unitDisc (schwarzianHol f)‖ ≤ 2 * k := by
  have hfa : ∀ z ∈ unitDisc, AnalyticAt ℂ f z := fun z hz =>
    hf.1.analyticAt (isOpen_ball.mem_nhds hz)
  refine TakhtajanTeo.toAInf_disc_spec_of_bound (by linarith) ?_ ?_
  · intro z hz
    exact (analyticAt_schwarzianHol (hfa z hz)
      (deriv_ne_zero_of_injOn isOpen_ball hf.1 hf.2.1 hz)).differentiableAt.differentiableWithinAt
  · intro z hz
    have hfz : f z ∈ Ω := hf.2.2 ▸ mem_image_of_mem f hz
    have hbdd : BddAbove {r : ℝ | ∃ (g : ℂ → ℂ) (y : ℂ), IsConformalOnto g unitDisc Ω ∧
        y ∈ unitDisc ∧ g y = f z ∧ r = ‖schwarzian g y‖ * (1 - ‖y‖ ^ 2) ^ 2 / 4} := by
      refine ⟨6 / 4, ?_⟩
      rintro r ⟨g, y, hg, hy, -, rfl⟩
      have := knr_holomorphic_bound hg.1 hg.2.1 hy
      linarith
    have hle : ‖schwarzian f z‖ * (1 - ‖z‖ ^ 2) ^ 2 / 4 ≤ schwarzNorm Ω (f z) := by
      unfold schwarzNorm
      exact le_csSup hbdd ⟨f, z, hf, hz, rfl, rfl⟩
    have h2 := hs (f z) hfz
    rw [schwarzian_of_analyticAt (hfa z hz)] at hle
    linarith

/-- `lem:aw` helper (Möbius uniqueness): two univalent maps of `𝔻` with the same Schwarzian differ
by a Möbius map, as maps into `ℂ̂` (Theorem 19.1; `f` finite rules out a pole of the Möbius map). -/
theorem s10_aw_mob {f g : ℂ → ℂ} {Ω : Set ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (hg : DifferentiableOn ℂ g unitDisc) (hgi : InjOn g unitDisc)
    (hS : ∀ z ∈ unitDisc, schwarzianHol f z = schwarzianHol g z) :
    ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ ∀ z ∈ unitDisc, (f z : ExtPlane) = mobiusExt a b c d (g z) := by
  have hD : IsOpen unitDisc := isOpen_ball
  have hDc : IsConnected unitDisc := (convex_ball (0 : ℂ) 1).isConnected ⟨0, mem_ball_self one_pos⟩
  have hgc : IsConformalOnto g unitDisc (g '' unitDisc) := ⟨hg, hgi, rfl⟩
  have hfa : ∀ z ∈ unitDisc, AnalyticAt ℂ f z := fun z hz => hf.1.analyticAt (hD.mem_nhds hz)
  have hga : ∀ z ∈ unitDisc, AnalyticAt ℂ g z := fun z hz => hg.analyticAt (hD.mem_nhds hz)
  obtain ⟨a, b, c, d, hdet, hfg⟩ := thm19_1_unique hD hDc (isLocUnivMero_of_isConformalOnto hD hf)
    (isLocUnivMero_of_isConformalOnto hD hgc) (fun z hz => by
      rw [schwarzian_of_analyticAt (hfa z hz), schwarzian_of_analyticAt (hga z hz)]
      exact hS z hz)
  refine ⟨a, b, c, d, hdet, fun z hz => ?_⟩
  by_cases hden : c * g z + d = 0
  · -- impossible: `f` is finite at `z`, while `(a g + b)/(c g + d)` tends to `∞` there
    exfalso
    have hc : c ≠ 0 := by
      rintro rfl
      apply hdet
      have hd : d = 0 := by simpa using hden
      rw [hd]
      ring
    have hzo : unitDisc ∈ 𝓝 z := hD.mem_nhds hz
    have hgt : Tendsto g (𝓝[≠] z) (𝓝[≠] (g z)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((hga z hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hzo] with y hy hyD
      exact fun h => hy (hgi hyD hz h)
    have h1 := (tendsto_mobiusFn_pole hdet hden).comp hgt
    have heq : (mobiusFn a b c d ∘ g) =ᶠ[𝓝[≠] z] f := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hzo] with y hy hyD
      have hne : c * g y + d ≠ 0 := by
        intro h0
        apply hy
        apply hgi hyD hz
        have h3 : c * (g y - g z) = 0 := by linear_combination h0 - hden
        exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hc)
      exact (hfg y hyD (hfa y hyD) (hga y hyD) hne).symm
    have h2 : Tendsto f (𝓝[≠] z) (Bornology.cobounded ℂ) := h1.congr' heq
    have h3 : Tendsto f (𝓝[≠] z) (𝓝 (f z)) :=
      (hfa z hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact not_tendsto_atTop_of_tendsto_nhds h3.norm (tendsto_norm_cobounded_atTop.comp h2)
  · rw [mobiusExt_coe hden, hfg z hz (hfa z hz) (hga z hz) hden]
    rfl

/-- `lem:aw` helper (B, C): Ahlfors–Weill.  For a Riemann map `f : 𝔻 → Ω` with `s ≤ k/2` on `Ω`
(`0 < k < 1`), there are a `(1+k)/(1-k)`-q.c. homeomorphism `W` of `ℂ` and a Möbius map `M` with
`f = M ∘ W` on `𝔻`: `W` is the normalized solution for `Λ(S_f)` (`‖Λ(S_f)‖ ≤ k`), whose Schwarzian
on `𝔻` is `S_f` (Takhtajan–Teo `ahlfors_weill`). -/
theorem s10_aw_W {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) {k : ℝ} (hk0 : 0 < k)
    (hk1 : k < 1) (hs : ∀ w ∈ Ω, schwarzNorm Ω w ≤ k / 2) :
    ∃ (W : ℂ → ℂ) (a b c d : ℂ), IsKQC W univ ((1 + k) / (1 - k)) ∧ W '' univ = univ ∧
      a * d - b * c ≠ 0 ∧ ∀ z ∈ unitDisc, (f z : ExtPlane) = mobiusExt a b c d (W z) := by
  set φ := TakhtajanTeo.toAInf unitDisc (schwarzianHol f) with hφdef
  obtain ⟨hφf, hφn⟩ := s10_aw_phi hf hk0.le hs
  obtain ⟨hμ, hbers⟩ := TakhtajanTeo.ahlfors_weill (φ := φ) (by linarith)
  set μ := TakhtajanTeo.Lambda φ with hμdef
  have hμk : ‖μ‖ ≤ k := by
    have := TakhtajanTeo.Lambda_norm_le φ
    linarith
  have hBP : TakhtajanTeo.bersPhi μ = φ := by
    have h := TakhtajanTeo.bers_Phi ⟨μ, hμ⟩
    rw [hbers] at h
    exact h.symm
  obtain ⟨hSB, -⟩ := TakhtajanTeo.bersPhi_spec hμ
  obtain ⟨hB, -⟩ := TakhtajanTeo.wB_spec hμ
  obtain ⟨M, hM, V, hV, hfinite, -, -, -, -, -, -⟩ := hB
  obtain ⟨a', b', c', d', hdet', rfl⟩ := hM
  obtain ⟨W, -, hWK, hWu⟩ := TakhtajanTeo.extB_normalized_plane_exists hμ
  have hVW : V = W := hWu V hV
  have hVK0 : IsKQC V univ ((1 + ‖μ‖) / (1 - ‖μ‖)) := by
    rw [hVW]
    exact hWK
  have hVK : IsKQC V univ ((1 + k) / (1 - k)) := by
    refine hVK0.mono ?_
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [norm_nonneg μ]
  have hVh : DifferentiableOn ℂ V unitDisc := TakhtajanTeo.extB_solution_holomorphic hV
  have hVi : InjOn V unitDisc := hVK.2.2.1.2.1.mono (subset_univ _)
  have hden : ∀ z ∈ unitDisc, c' * V z + d' ≠ 0 := by
    intro z hz he
    have hfin := (hfinite z).symm.trans (TakhtajanTeo.wB_disc_eq_fB hμ hz)
    rw [mobiusExt_coe_of_eq_zero he] at hfin
    exact OnePoint.infty_ne_coe _ hfin
  have hSV : ∀ z ∈ unitDisc, schwarzianHol f z = schwarzianHol V z := by
    intro z hz
    have hVa : AnalyticAt ℂ V z := hVh.analyticAt (isOpen_ball.mem_nhds hz)
    have hVd : deriv V z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hVh hVi hz
    have hMa : AnalyticAt ℂ (fun w => (a' * V w + b') / (c' * V w + d')) z :=
      ((analyticAt_const.mul hVa).add analyticAt_const).div
        ((analyticAt_const.mul hVa).add analyticAt_const) (hden z hz)
    have heq : TakhtajanTeo.fB μ =ᶠ[𝓝 z] fun w => (a' * V w + b') / (c' * V w + d') := by
      filter_upwards [isOpen_ball.mem_nhds hz] with y hy
      have h := (hfinite y).symm.trans (TakhtajanTeo.wB_disc_eq_fB hμ hy)
      rw [mobiusExt_coe (hden y hy)] at h
      exact (OnePoint.coe_injective h).symm
    rw [← hφf z hz, ← hφdef, ← hBP, hSB z hz, schwarzianHol_congr heq, ← schwarzian_of_analyticAt hMa,
      schwarzian_mobius_comp_analytic hVa hVd hdet', schwarzian_of_analyticAt hVa]
  obtain ⟨a, b, c, d, hdet, hfV⟩ := s10_aw_mob hf hVh hVi hSV
  exact ⟨V, a, b, c, d, hVK, hV.2.1, hdet, hfV⟩

/-- `lem:aw` helper: if `f = M ∘ W` on `𝔻` (`M(w) = (aw+b)/(cw+d)`) and `Ω = f(𝔻)` is unbounded, the
pole `W⁻¹(-d/c)` of `M ∘ W` is a point `p` of the unit circle (`c ≠ 0`), and `f = M ∘ W` in `ℂ` on `𝔻`. -/
theorem s10_aw_pole {W f : ℂ → ℂ} {Ω : Set ℂ} {K : ℝ} (hW : IsKQC W univ K) (hWs : W '' univ = univ)
    {a b c d : ℂ} (hdet : a * d - b * c ≠ 0)
    (hN : ∀ z ∈ unitDisc, (f z : ExtPlane) = mobiusExt a b c d (W z)) (hf : f '' unitDisc = Ω)
    (hu : ∀ (x : ℂ) (R : ℝ), ∃ w ∈ Ω, R < ‖w - x‖) :
    c ≠ 0 ∧ ∃ p : ℂ, ‖p‖ = 1 ∧ c * W p + d = 0 ∧
      ∀ z ∈ unitDisc, c * W z + d ≠ 0 ∧ f z = (a * W z + b) / (c * W z + d) := by
  have hz : ∀ z ∈ unitDisc, c * W z + d ≠ 0 ∧ f z = (a * W z + b) / (c * W z + d) := by
    intro z hz
    have h := hN z hz
    by_cases h0 : c * W z + d = 0
    · rw [mobiusExt_coe_of_eq_zero h0] at h
      exact absurd h (OnePoint.coe_ne_infty _)
    · rw [mobiusExt_coe h0] at h
      exact ⟨h0, OnePoint.coe_injective h⟩
  have hWc : Continuous W := by
    obtain ⟨e, he⟩ := t1_homeomorph hW hWs
    rw [← he]
    exact e.continuous
  -- a pole in the closed disc: otherwise `M ∘ W` is bounded on it, and so is `Ω`
  obtain ⟨p, hp1, hpW⟩ : ∃ p ∈ closedBall (0 : ℂ) 1, c * W p + d = 0 := by
    by_contra hcon
    push Not at hcon
    have hcont : ContinuousOn (fun y => (a * W y + b) / (c * W y + d)) (closedBall (0 : ℂ) 1) :=
      ((continuous_const.mul hWc).add continuous_const).continuousOn.div
        ((continuous_const.mul hWc).add continuous_const).continuousOn hcon
    obtain ⟨C, hC⟩ :=
      ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn hcont).isBounded.exists_norm_le
    obtain ⟨w, hw, hwC⟩ := hu 0 C
    obtain ⟨y, hy, rfl⟩ : w ∈ f '' unitDisc := hf ▸ hw
    have h1 := hC _ ⟨y, ball_subset_closedBall hy, (hz y hy).2.symm⟩
    rw [sub_zero] at hwC
    linarith
  have hc : c ≠ 0 := by
    rintro rfl
    apply hdet
    have hd : d = 0 := by simpa using hpW
    rw [hd]
    ring
  refine ⟨hc, p, ?_, hpW, hz⟩
  refine le_antisymm (mem_closedBall_zero_iff.mp hp1) (not_lt.mp fun hlt => ?_)
  exact (hz p (mem_ball_zero_iff.mpr hlt)).1 hpW

/-- `lem:aw` helper (D): from `f = M ∘ W` on `𝔻` with the pole `p ∈ ∂𝔻` of `M ∘ W`, a `K`-q.c.
homeomorphism `F` of `ℂ` with `F(ℍ) = f(𝔻)`.  `F = A ∘ G ∘ ψ` with `G` the Cayley conjugate of
`E = W ∘ m`, `m(y) = p(y + 1 + i)`, `ψ(z) = z + 1 + i` and `A` affine; `F(cayleyInv u) = f(p u)`. -/
theorem s10_aw_conj {W f : ℂ → ℂ} {Ω : Set ℂ} {K : ℝ} (hW : IsKQC W univ K) (hWs : W '' univ = univ)
    {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) (hc : c ≠ 0) {p : ℂ} (hp : ‖p‖ = 1)
    (hpW : c * W p + d = 0)
    (hN : ∀ z ∈ unitDisc, c * W z + d ≠ 0 ∧ f z = (a * W z + b) / (c * W z + d))
    (hf : f '' unitDisc = Ω) :
    ∃ F : ℂ → ℂ, IsKQC F univ K ∧ F '' univ = univ ∧ F '' upperHalf = Ω := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hp
    exact zero_ne_one hp
  -- `E = W ∘ m`
  set m : ℂ → ℂ := fun y => p * (y + 1 + I) with hmdef
  have hms : m '' univ = univ := image_univ_of_surjective fun w =>
    ⟨p⁻¹ * w - 1 - I, by
      show p * (p⁻¹ * w - 1 - I + 1 + I) = w
      rw [show p⁻¹ * w - 1 - I + 1 + I = p⁻¹ * w by ring, mul_inv_cancel_left₀ hp0]⟩
  have hmc : IsConformalOnto m univ univ := by
    refine ⟨?_, fun x _ y _ h => ?_, hms⟩
    · exact ((differentiable_const _).mul
        ((differentiable_id.add_const _).add_const _)).differentiableOn
    · have h1 := mul_left_cancel₀ hp0 h
      linear_combination h1
  have hE : IsKQC (W ∘ m) univ (1 * K) :=
    thm7_1_comp (isKQC_one_of_conformal isOpen_univ hmc) hW (subset_univ _)
  rw [one_mul] at hE
  have hEs : (W ∘ m) '' univ = univ := by rw [image_comp, hms, hWs]
  set G : ℂ → ℂ := fun ζ => ((W ∘ m) (-I + 2 * I * (1 - ζ)⁻¹) - (W ∘ m) (-I))⁻¹ with hGdef
  have hGh : IsHomeomorphOnto G univ univ := b4_qc_conj_isHomeomorphOnto hE hEs
  have hG : IsKQC G univ K := b4_isKQC_univ_of_punctured hGh (b4_qc_conj_isKQC hE)
  -- the affine maps `ψ` and `A`
  set ψ : ℂ → ℂ := fun z => z + 1 + I with hψdef
  have hψs : ψ '' univ = univ := image_univ_of_surjective fun w =>
    ⟨w - 1 - I, by simp only [hψdef]; ring⟩
  have hψc : IsConformalOnto ψ univ univ := by
    refine ⟨?_, fun x _ y _ h => ?_, hψs⟩
    · exact ((differentiable_id.add_const _).add_const _).differentiableOn
    · have h1 : x + 1 + I = y + 1 + I := h
      linear_combination h1
  set β : ℂ := (b * c - a * d) / c ^ 2 with hβdef
  have hβ : β ≠ 0 := div_ne_zero (fun h => hdet (by linear_combination -h)) (pow_ne_zero 2 hc)
  set A : ℂ → ℂ := fun u => a / c + β * u with hAdef
  have hAs : A '' univ = univ := image_univ_of_surjective fun w =>
    ⟨(w - a / c) / β, by simp only [hAdef]; field_simp; ring⟩
  have hAc : IsConformalOnto A univ univ := by
    refine ⟨?_, fun x _ y _ h => ?_, hAs⟩
    · exact ((differentiable_const _).add ((differentiable_const _).mul differentiable_id)).differentiableOn
    · have h1 : a / c + β * x = a / c + β * y := h
      exact mul_left_cancel₀ hβ (add_left_cancel h1)
  have hF0 := thm7_1_comp (thm7_1_comp (isKQC_one_of_conformal isOpen_univ hψc) hG (subset_univ _))
    (isKQC_one_of_conformal isOpen_univ hAc) (subset_univ _)
  rw [one_mul, mul_one] at hF0
  -- `F (cayleyInv u) = f (p u)` on `𝔻`
  have hkey : ∀ u ∈ unitDisc, (A ∘ (G ∘ ψ)) (cayleyInv u) = f (p * u) := by
    intro u hu
    have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
    have h1u : (1 : ℂ) - u ≠ 0 := cayleyInv_den_ne_zero hu1
    have hI : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
    have hpu : p * u ∈ unitDisc := mem_ball_zero_iff.mpr (by rw [norm_mul, hp, one_mul]; exact hu1)
    obtain ⟨hden, hfpu⟩ := hN (p * u) hpu
    have h2 : (1 : ℂ) - (I * (1 + u) / (1 - u) + 1 + I) = -(2 * I) / (1 - u) := by
      field_simp
      ring
    have hin : -I + 2 * I * (1 - (I * (1 + u) / (1 - u) + 1 + I))⁻¹ = u - 1 - I := by
      rw [h2, inv_div]
      field_simp
      ring
    have hm1 : m (u - 1 - I) = p * u := by simp only [hmdef]; ring
    have hm2 : m (-I) = p := by simp only [hmdef]; ring
    show a / c + β * (W (m (-I + 2 * I * (1 - (I * (1 + u) / (1 - u) + 1 + I))⁻¹)) -
      W (m (-I)))⁻¹ = f (p * u)
    rw [hin, hm1, hm2, hfpu]
    have hd : d = -(c * W p) := by linear_combination hpW
    have hX : W (p * u) - W p ≠ 0 := by
      intro h0
      apply hden
      linear_combination c * h0 + hpW
    have hcd : c * W (p * u) + d = c * (W (p * u) - W p) := by linear_combination hpW
    rw [hcd, hβdef, hd]
    field_simp
    ring
  have hrot : (fun u => p * u) '' unitDisc = unitDisc := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact mem_ball_zero_iff.mpr (by rw [norm_mul, hp, one_mul]; exact mem_ball_zero_iff.mp hu)
    · intro hw
      refine ⟨p⁻¹ * w, mem_ball_zero_iff.mpr ?_, mul_inv_cancel_left₀ hp0 w⟩
      rw [norm_mul, norm_inv, hp, inv_one, one_mul]
      exact mem_ball_zero_iff.mp hw
  refine ⟨A ∘ (G ∘ ψ), hF0, ?_, ?_⟩
  · rw [image_comp, image_comp, hψs, hGh.2.2.1, hAs]
  · calc (A ∘ (G ∘ ψ)) '' upperHalf = (A ∘ (G ∘ ψ)) '' (cayleyInv '' unitDisc) := by
          rw [s02_cayleyInv_conformal.2.2]
      _ = (fun u => f (p * u)) '' unitDisc := by
          rw [← image_comp]
          exact image_congr fun u hu => hkey u hu
      _ = f '' ((fun u => p * u) '' unitDisc) := by rw [image_image]
      _ = Ω := by rw [hrot, hf]

/-- `lem:aw` helper: a homeomorphism `e` of `ℂ` maps `𝕃` onto the complement of the closure of
`e(ℍ)`. -/
theorem s10_aw_lower (e : ℂ ≃ₜ ℂ) : e '' lowerHalf = (closure (e '' upperHalf))ᶜ := by
  have h : lowerHalf = (closure upperHalf)ᶜ := by
    show {z : ℂ | z.im < 0} = (closure {z : ℂ | 0 < z.im})ᶜ
    rw [Complex.closure_setOfPred_lt_im]
    ext z
    simp only [mem_ofPred_eq, mem_compl_iff, not_le]
  rw [h, ← e.image_closure, image_compl_eq e.bijective]

/-- **Lemma 10.9**, `lem:aw`, `sec10-sharp.tex:390` (Ahlfors–Weill): if `sup_Ω s ≤ k/2` with
`0 < k < 1`, then `Γ` is a `K`-quasicircle with `K = (1+k)/(1-k)`. -/
theorem lem_aw (Ω Ωs : Set ℂ) (hJ : IsJordanPair Ω Ωs) (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1)
    (hs : ∀ w ∈ Ω, schwarzNorm Ω w ≤ k / 2) :
    IsKQuasiPair Ω Ωs ((1 + k) / (1 - k)) := by
  -- Ahlfors–Weill: `f = M ∘ W` on `𝔻` (`s10_aw_W`), then the Cayley conjugation of `W` (`s10_aw_conj`);
  -- `F(𝕃) = Ω*` since both `F` and the Jordan pair's homeomorphism map `ℍ` onto `Ω`.
  obtain ⟨f, hf⟩ := s02_jordanPair_riemannMap hJ
  obtain ⟨W, a, b, c, d, hW, hWs, hdet, hN⟩ := s10_aw_W hf hk0 hk1 hs
  obtain ⟨hc, p, hp, hpW, hz⟩ := s10_aw_pole hW hWs hdet hN hf.2.2 (s02_jordanPair_unbounded hJ).1
  obtain ⟨F, hF, hFs, hFU⟩ := s10_aw_conj hW hWs hdet hc hp hpW hz hf.2.2
  refine ⟨F, hF, hFs, hFU, ?_⟩
  obtain ⟨e, rfl⟩ := t1_homeomorph hF hFs
  obtain ⟨H, hHU, hHL⟩ := hJ
  rw [s10_aw_lower e, ← hHL, s10_aw_lower H, hFU, hHU]

/-- **Lemma 10.9**, `lem:aw`, `sec10-sharp.tex:392`: if `sup_Ω s ≤ 1/4`, `Γ` is a 3-quasicircle. -/
theorem lem_aw_three (Ω Ωs : Set ℂ) (hJ : IsJordanPair Ω Ωs)
    (hs : ∀ w ∈ Ω, schwarzNorm Ω w ≤ 1 / 4) :
    IsKQuasiPair Ω Ωs 3 := by
  -- `k = 1/2`
  have h := lem_aw Ω Ωs hJ (1 / 2) (by norm_num) (by norm_num)
    (fun w hw => (hs w hw).trans (by norm_num))
  have e : (1 + 1 / 2 : ℝ) / (1 - 1 / 2) = 3 := by norm_num
  rwa [e] at h

/-- Helper for `prop_global_graph`: under `sup_Ω s < η` and `sup_{Ω*} s* < η`, every `w ∈ Ω` is
`(η', R)`-good for every `η' ≥ η` and every `R` (`ς(x, R) ≤ max(sup s, sup s*) < η`).  Hence
every lemma of §4–§5 stated for good parameters applies on all of `Ω`, each with its own
constants `(η_i, R_i)`. -/
theorem s10_pgg_good {Ω Ωs : Set ℂ} {η η' : ℝ} (hη : η ≤ η') (h : SchwarzSupLt Ω η)
    (hs : SchwarzSupLt Ωs η) (R : ℝ) : Ω ⊆ goodSet Ω Ωs η' R := by
  intro w hw
  obtain ⟨c₁, hc₁, h₁⟩ := h
  obtain ⟨c₂, hc₂, h₂⟩ := hs
  have hsn : ∀ (U : Set ℂ) (x : ℂ), 0 ≤ schwarzNorm U x := fun U x =>
    Real.sSup_nonneg (by rintro r ⟨f, z, -, -, -, rfl⟩; positivity)
  have h0 : 0 ≤ max c₁ c₂ := ((hsn Ω w).trans (h₁ w hw)).trans (le_max_left _ _)
  have hle : varsigma Ω Ωs (epstein Ω w) R ≤ max c₁ c₂ := by
    refine Real.sSup_le ?_ h0
    rintro r (⟨w', hw', -, rfl⟩ | ⟨z, hz, -, rfl⟩)
    · exact (h₁ w' hw').trans (le_max_left _ _)
    · exact (h₂ z hz).trans (le_max_right _ _)
  exact ⟨hw, hle.trans_lt ((max_lt hc₁ hc₂).trans_le hη)⟩

/-- Helper for `prop_global_graph` (a), (c): `t` and `N` are smooth on `Ω`, `0 < t < ε`,
`X*(N w) = E(w, t w)`, and `N` maps `Ω` injectively into `Ω*` (`s04_sl_eq_def_N_unif`,
`s04_sl_prop_RN_unif`, `s10_pgg_good`). -/
theorem s10_pgg_N : ∀ ε : ℝ, 0 < ε → ε < 1 / 4 → ∃ η₀ : ℝ, 0 < η₀ ∧
    ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs 3 → ¬ IsLinePair Ω Ωs →
      SchwarzSupLt Ω η → SchwarzSupLt Ωs η →
      ContDiffOn ℝ ∞ (slabTop Ω Ωs) Ω ∧ ContDiffOn ℝ ∞ (slabMap Ω Ωs) Ω ∧
        (∀ w ∈ Ω, 0 < slabTop Ω Ωs w ∧ slabTop Ω Ωs w < ε) ∧
        (∀ w ∈ Ω, epstein Ωs (slabMap Ω Ωs w) = normalGeod Ω w (slabTop Ω Ωs w)) ∧
        MapsTo (slabMap Ω Ωs) Ω Ωs ∧ InjOn (slabMap Ω Ωs) Ω := by
  intro ε hε hε4
  obtain ⟨η₁, hη₁, R₁, hN⟩ := s04_sl_eq_def_N_unif 3 (by norm_num) ε hε hε4
  obtain ⟨M, hM⟩ := s04_sl_prop_RN_unif 3 (by norm_num)
  obtain ⟨η₂, hη₂, R₂, hR⟩ := hM ε hε hε4
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun η hη hηle Ω Ωs hq hnl hs hss => ?_⟩
  have hG := s10_pgg_good le_rfl hs hss (max R₁ R₂)
  obtain ⟨-, htC, hNC, hpt⟩ :=
    hN η (max R₁ R₂) hη (hηle.trans (min_le_left _ _)) (le_max_left _ _) Ω Ωs hq hnl
  obtain ⟨lab, hlab, -⟩ := lem_borel_label (s03_b0_jordanPair hq) hnl
  obtain ⟨-, hinj, -⟩ :=
    hR η (max R₁ R₂) hη (hηle.trans (min_le_right _ _)) (le_max_right _ _) Ω Ωs hq hnl lab hlab
  exact ⟨htC.mono hG, hNC.mono hG, fun w hw => ⟨(hpt w (hG hw)).2.1, (hpt w (hG hw)).2.2.1⟩,
    fun w hw => (hpt w (hG hw)).2.2.2, fun w hw => (hpt w (hG hw)).1, hinj.mono hG⟩

/-- Helper for `prop_global_graph` (b): `𝒮̃` is open, and `E` maps it injectively onto the gap
(the bad set is empty, so `D = Ω`: `s05_sr_unif`, `s05_br_unif` with the empty net). -/
theorem s10_pgg_slab : ∀ ε : ℝ, 0 < ε → ε < 1 / 4 → ∃ η₀ : ℝ, 0 < η₀ ∧
    ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs 3 → ¬ IsLinePair Ω Ωs →
      SchwarzSupLt Ω η → SchwarzSupLt Ωs η →
      IsOpen (gapSlab Ω (slabTop Ω Ωs)) ∧ InjOn (normalMap Ω) (gapSlab Ω (slabTop Ω Ωs)) ∧
        normalMap Ω '' gapSlab Ω (slabTop Ω Ωs) = gap Ω Ωs := by
  intro ε hε hε4
  obtain ⟨η₁, hη₁, hN⟩ := s10_pgg_N ε hε hε4
  obtain ⟨η₂, hη₂, R₂, -, hsr⟩ := s05_sr_unif 3 (by norm_num) ε hε hε4
  obtain ⟨C, hbr⟩ := s05_br_unif 3 (by norm_num)
  obtain ⟨η₃, hη₃, R₃, -, hbr'⟩ := hbr ε hε hε4
  refine ⟨min η₁ (min η₂ η₃), lt_min hη₁ (lt_min hη₂ hη₃),
    fun η hη hηle Ω Ωs hq hnl hs hss => ?_⟩
  have hJ := s03_b0_jordanPair hq
  have hΩo : IsOpen Ω := (s05_density_smooth hJ).1
  obtain ⟨lab, hlab, -⟩ := lem_borel_label hJ hnl
  obtain ⟨htC, -, -, -, -, -⟩ := hN η hη (hηle.trans (min_le_left _ _)) Ω Ωs hq hnl hs hss
  -- the bad set is empty: `s < η` on `Ω` and `s* < η` on `Ω*`
  have hA : curvASet Ω Ωs η = ∅ := by
    obtain ⟨c₁, hc₁, h₁⟩ := hs
    obtain ⟨c₂, hc₂, h₂⟩ := hss
    refine eq_empty_iff_forall_notMem.2 ?_
    rintro x (⟨w, hw, hle, -⟩ | ⟨z, hz, hle, -⟩)
    · linarith [h₁ w hw]
    · linarith [h₂ z hz]
  have hB : badSet Ω Ωs η (max R₂ R₃) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 ?_
    rintro x ⟨-, hx⟩
    have hx' : hsetDist x (curvASet Ω Ωs η) ≤ ENNReal.ofReal (max R₂ R₃) := hx
    rw [hA] at hx'
    simp [hsetDist] at hx'
  have hnet : IsBadNet Ω Ωs lab η (max R₂ R₃) ∅ (fun _ => 0) := by
    refine ⟨empty_subset _, fun b hb => by simp at hb, fun x hx => ?_, fun b hb => by simp at hb⟩
    rw [hB] at hx
    simp at hx
  obtain ⟨hreg, hinj⟩ := hsr η (max R₂ R₃) hη ((hηle.trans (min_le_right _ _)).trans
    (min_le_left _ _)) (le_max_left _ _) Ω Ωs hq hnl lab hlab ∅ _ hnet
  obtain ⟨hD, hdiff⟩ := (hbr' η (max R₂ R₃) hη ((hηle.trans (min_le_right _ _)).trans
    (min_le_right _ _)) (le_max_right _ _) Ω Ωs hq hnl lab hlab ∅ _ hnet).2 hB
  rw [hD] at hreg hinj hdiff
  refine ⟨?_, hinj, ?_⟩
  · -- `𝒮̃ = Ω × ℝ ∩ {0 < τ, 0 < t(w) - τ}`
    have hc : ContinuousOn (fun p : ℂ × ℝ => (p.2, slabTop Ω Ωs p.1 - p.2))
        (Prod.fst ⁻¹' Ω) :=
      continuousOn_snd.prodMk ((htC.continuousOn.comp continuousOn_fst fun _ hp => hp).sub
        continuousOn_snd)
    have ho := hc.isOpen_inter_preimage (hΩo.preimage continuous_fst)
      ((isOpen_Ioi (a := (0 : ℝ))).prod (isOpen_Ioi (a := (0 : ℝ))))
    convert ho using 1
    ext p
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, sub_pos.2 h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, sub_pos.1 h3⟩
  · ext q
    constructor
    · rintro ⟨p, ⟨hp1, hp2, hp3⟩, rfl⟩
      have hm : normalMap Ω p ∈ slabRegion Ω Ωs Ω := ⟨p.1, hp1, p.2, hp2, hp3, rfl⟩
      rw [hreg] at hm
      exact hm.1
    · intro hq'
      have hm : q ∈ slabRegion Ω Ωs Ω := by
        by_contra hc
        have h' : q ∈ gap Ω Ωs \ slabRegion Ω Ωs Ω := ⟨hq', hc⟩
        rw [hdiff] at h'
        simp at h'
      obtain ⟨w, hw, τ, h1, h2, rfl⟩ := hm
      exact ⟨(w, τ), ⟨hw, h1, h2⟩, rfl⟩

/-- Helper for `prop_global_graph` (b): the differential of `E` is invertible on `𝒮̃`
(`s04_sl_tube_unif` (ii): `E` is an immersion on `\overline{B_ρ(w, 2)} × [-2, 3]`). -/
theorem s10_pgg_det : ∀ ε : ℝ, 0 < ε → ε < 1 / 4 → ∃ η₀ : ℝ, 0 < η₀ ∧
    ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs 3 → ¬ IsLinePair Ω Ωs →
      SchwarzSupLt Ω η → SchwarzSupLt Ωs η →
      ∀ p ∈ gapSlab Ω (slabTop Ω Ωs),
        LinearMap.det (fderiv ℝ (normalMap Ω) p : (ℂ × ℝ) →ₗ[ℝ] (ℂ × ℝ)) ≠ 0 := by
  intro ε hε hε4
  obtain ⟨η₁, hη₁, hN⟩ := s10_pgg_N ε hε hε4
  obtain ⟨η₂, hη₂, R₂, htube⟩ := s04_sl_tube_unif 3 1 1 6 ε 0 (by norm_num) one_pos one_pos le_rfl
    hε hε4 le_rfl
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun η hη hηle Ω Ωs hq hnl hs hss p hp => ?_⟩
  obtain ⟨-, -, ht, -, -, -⟩ := hN η hη (hηle.trans (min_le_left _ _)) Ω Ωs hq hnl hs hss
  obtain ⟨hp1, hp2, hp3⟩ := hp
  have hg := s10_pgg_good le_rfl hs hss R₂ hp1
  obtain ⟨-, ⟨⟨-, -, himm, -⟩, -⟩, -⟩ :=
    htube η R₂ hη (hηle.trans (min_le_right _ _)) le_rfl Ω Ωs hq hnl p.1 hg
  have hd0 : poincareDist Ω p.1 p.1 = 0 :=
    s04_tb_dist_self (s02_jordanPair_riemannMap (s03_b0_jordanPair hq)) hp1
  have hmem : p ∈ rhoClosedBall Ω p.1 (1 + 1) ×ˢ Icc (-2 : ℝ) (1 + 2) := by
    refine ⟨⟨hp1, by rw [hd0]; norm_num⟩, ?_, ?_⟩
    · linarith
    · linarith [(ht p.1 hp1).2]
  have hinj : Function.Injective
      ((fderiv ℝ (normalMap Ω) p : (ℂ × ℝ) →L[ℝ] (ℂ × ℝ)) : (ℂ × ℝ) →ₗ[ℝ] (ℂ × ℝ)) :=
    himm p hmem
  exact isUnit_iff_ne_zero.1 ((LinearMap.isUnit_iff_isUnit_det _).1
    ((LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot.2 hinj)))

/-- Helper for `prop_global_graph` (c): `N` maps `Ω` onto `Ω*`.  For `z* ∈ Ω*`, `q = X*(z*)` is
not in `U` (`prop_separation_b`), `q = E(w, τ)` with `w = w(q)` and `0 < τ ≤ D₃`
(`lem_nearest`, `lem_width`), so `z* = N_loc(v)` by `lem_tube` (iii); `N w` is also in the image
of `N_loc`, and injectivity of `E` on the tube (`lem_tube` (ii)) gives `z* = N w`. -/
theorem s10_pgg_surj : ∀ ε : ℝ, 0 < ε → ε < 1 / 4 → ∃ η₀ : ℝ, 0 < η₀ ∧
    ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs 3 → ¬ IsLinePair Ω Ωs →
      SchwarzSupLt Ω η → SchwarzSupLt Ωs η → SurjOn (slabMap Ω Ωs) Ω Ωs := by
  intro ε hε hε4
  obtain ⟨η₁, hη₁, hN⟩ := s10_pgg_N ε hε hε4
  obtain ⟨D, hD⟩ := lem_width 3
  have hT : 0 < max D 0 + 1 := by positivity
  obtain ⟨η₂, hη₂, R₂, htube⟩ := s04_sl_tube_unif 3 1 (max D 0 + 1) 6 ε 0 (by norm_num) one_pos
    hT le_rfl hε hε4 le_rfl
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun η hη hηle Ω Ωs hq hnl hs hss z hz => ?_⟩
  obtain ⟨-, -, ht, hX, hmaps, -⟩ := hN η hη (hηle.trans (min_le_left _ _)) Ω Ωs hq hnl hs hss
  have hJ := s03_b0_jordanPair hq
  have hJs := s03_b0_jordanPair (s03_qce_swap hq)
  obtain ⟨lab, hlab, -⟩ := lem_borel_label hJ hnl
  -- `q = X*(z*) ∈ U*`, hence `q ∉ U`
  have hqs : epstein Ωs z ∈ horoUnion Ωs := s03_qik_mem (s02_jordanPair_riemannMap hJs) hz
  have hqU : epstein Ωs z ∈ UHS := by
    obtain ⟨z', -, hz'⟩ := mem_iUnion₂.1 hqs
    exact hz'.1
  have hqn : epstein Ωs z ∉ horoUnion Ω := fun h =>
    eq_empty_iff_forall_notMem.1 (prop_separation_b hJ hnl).2 _ ⟨h, hqs⟩
  obtain ⟨hlw, hmin⟩ := hlab.2 _ ⟨hqU, hqn⟩
  obtain ⟨hqE, hτ, -, -⟩ := lem_nearest hJ hnl hqU hqn hlw hmin
  have hτD : hdistSet (epstein Ωs z) (horoUnion Ω) ≤ D := (hD Ω Ωs hq hnl).2.2 z hz
  -- the tube at the label `w = w(q)`
  have hg := s10_pgg_good le_rfl hs hss R₂ hlw
  obtain ⟨-, ⟨⟨-, hEinj, -, -⟩, -⟩, tl, Nl, -, -, -, -, htl, hset, -⟩ :=
    htube η R₂ hη (hηle.trans (min_le_right _ _)) le_rfl Ω Ωs hq hnl _ hg
  have hd0 : poincareDist Ω (lab (epstein Ωs z)) (lab (epstein Ωs z)) = 0 :=
    s04_tb_dist_self (s02_jordanPair_riemannMap hJ) hlw
  have hw0 : lab (epstein Ωs z) ∈ rhoClosedBall Ω (lab (epstein Ωs z)) 1 :=
    ⟨hlw, by rw [hd0]; norm_num⟩
  have hDm : 0 ≤ max D 0 := le_max_right _ _
  have hsub : ∀ v ∈ rhoClosedBall Ω (lab (epstein Ωs z)) 1, ∀ s : ℝ, -1 ≤ s →
      s ≤ max D 0 + 1 + 1 → (v, s) ∈ rhoClosedBall Ω (lab (epstein Ωs z)) (1 + 1) ×ˢ
        Icc (-2 : ℝ) (max D 0 + 1 + 2) := by
    intro v hv s hs1 hs2
    exact ⟨⟨hv.1, by linarith [hv.2]⟩, by linarith, by linarith⟩
  -- `z* = N_loc(v)` and `N(w) = N_loc(v')` (`lem_tube` (iii))
  have hz1 : z ∈ Nl '' rhoClosedBall Ω (lab (epstein Ωs z)) 1 := by
    rw [← hset]
    refine ⟨hz, (lab (epstein Ωs z), hdistSet (epstein Ωs z) (horoUnion Ω)),
      ⟨hw0, by linarith, by linarith [le_max_left D 0]⟩, hqE.symm⟩
  have hN1 : slabMap Ω Ωs (lab (epstein Ωs z)) ∈ Nl '' rhoClosedBall Ω (lab (epstein Ωs z)) 1 := by
    rw [← hset]
    refine ⟨hmaps hlw, (lab (epstein Ωs z), slabTop Ω Ωs (lab (epstein Ωs z))),
      ⟨hw0, by linarith [(ht _ hlw).1], by linarith [(ht _ hlw).2]⟩, (hX _ hlw).symm⟩
  obtain ⟨v, hv, hvz⟩ := hz1
  obtain ⟨v', hv', hv'N⟩ := hN1
  -- injectivity of `E` on the tube (`lem_tube` (ii)) identifies `v = w = v'`
  have h1 : v = lab (epstein Ωs z) := by
    have he := hEinj (hsub v hv (tl v) (by linarith [(htl v hv).1])
      (by linarith [(htl v hv).2.1])) (hsub _ hw0 (hdistSet (epstein Ωs z) (horoUnion Ω))
        (by linarith) (by linarith [le_max_left D 0]))
      (show normalGeod Ω v (tl v) = normalGeod Ω (lab (epstein Ωs z))
        (hdistSet (epstein Ωs z) (horoUnion Ω)) by rw [← (htl v hv).2.2, hvz]; exact hqE)
    exact congrArg Prod.fst he
  have h2 : v' = lab (epstein Ωs z) := by
    have he := hEinj (hsub v' hv' (tl v') (by linarith [(htl v' hv').1])
      (by linarith [(htl v' hv').2.1])) (hsub _ hw0 (slabTop Ω Ωs (lab (epstein Ωs z)))
        (by linarith [(ht _ hlw).1]) (by linarith [(ht _ hlw).2]))
      (show normalGeod Ω v' (tl v') = normalGeod Ω (lab (epstein Ωs z))
        (slabTop Ω Ωs (lab (epstein Ωs z))) by rw [← (htl v' hv').2.2, hv'N]; exact hX _ hlw)
    exact congrArg Prod.fst he
  refine ⟨lab (epstein Ωs z), hlw, ?_⟩
  rw [← hv'N, ← hvz, h1, h2]

/-- Helper for `prop_global_graph` (c): the Jacobian bounds (`lem_jacobian`, with `C_J ≥ 0`
derived from the singular value bounds at any point). -/
theorem s10_pgg_jac : ∃ CJ : ℝ, 0 ≤ CJ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 4 → ∃ η₀ : ℝ, 0 < η₀ ∧
    ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ Ω Ωs : Set ℂ, IsKQuasiPair Ω Ωs 3 → ¬ IsLinePair Ω Ωs →
      SchwarzSupLt Ω η → SchwarzSupLt Ωs η →
      ∀ w ∈ Ω, (CJ * ε ≤ 1 → (1 - CJ * ε) ^ 2 ≤ jacN Ω Ωs w) ∧
        jacN Ω Ωs w ≤ (1 + CJ * ε) ^ 2 := by
  obtain ⟨C, hC⟩ := lem_jacobian
  refine ⟨max C 0, le_max_right _ _, fun ε hε hε4 => ?_⟩
  obtain ⟨η₁, hη₁, R₁, hJc⟩ := hC 3 (by norm_num) ε hε hε4
  refine ⟨η₁, hη₁, fun η hη hηle Ω Ωs hq hnl hs hss w hw => ?_⟩
  obtain ⟨hsv, hlo, hup⟩ := hJc Ω Ωs hq hnl w (s10_pgg_good hηle hs hss R₁ hw)
  have hl : 0 < poincareDensity Ω w :=
    s02_poincareDensity_pos (s02_jordanPair_riemannMap (s03_b0_jordanPair hq)) hw
  -- `C ≥ 0`: the singular value bounds at `v = 1` give `(1 - Cε)λ ≤ (1 + Cε)λ`
  have hC0 : 0 ≤ C := by
    obtain ⟨h1, h2⟩ := hsv 1
    have h3 := h1.trans h2
    rw [norm_one, mul_one] at h3
    by_contra hneg
    have h4 : C * (ε * poincareDensity Ω w) < 0 :=
      mul_neg_of_neg_of_pos (not_le.1 hneg) (mul_pos hε hl)
    nlinarith
  rw [max_eq_left hC0]
  exact ⟨hlo, hup⟩

/-- **Proposition 10.11 (a)–(c)**, `prop:global-graph`, `sec10-sharp.tex:462` (constants of
Convention 10.10 quantified existentially; parts (d), (e) are `prop_global_graph_de`).
For `ε ∈ (0, ε₀]` there is `η = η(ε) ∈ (0, ε)` such that for every Jordan curve that is not a
circle with `sup_Ω s < η` and `sup_{Ω*} s* < η`:
(a) `Γ` is a 3-quasicircle, and the thickness `t = slabTop` and the map `N = slabMap` of §4 are
smooth on `Ω`, with `t : Ω → (0, ε)` and `X*(N(w)) = E(w, t(w))` (4.x);
(b) `𝒮̃ = {(w,τ) : 0 < τ < t(w)}` is open and `E` maps it diffeomorphically (injective, with
invertible differential) onto the gap;
(c) `N` is a bijection `Ω → Ω*` with `(1 - C_J ε)² ≤ J_N ≤ (1 + C_J ε)²` (`J_N = jacN`). -/
theorem prop_global_graph :
    ∃ ε₀ CJ : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 4 ∧ 0 ≤ CJ ∧ CJ * ε₀ ≤ 1 / 2 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ η : ℝ, 0 < η ∧ η < ε ∧
        ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ¬ IsLinePair Ω Ωs →
          SchwarzSupLt Ω η → SchwarzSupLt Ωs η →
          IsKQuasiPair Ω Ωs 3 ∧
            ContDiffOn ℝ ∞ (slabTop Ω Ωs) Ω ∧ ContDiffOn ℝ ∞ (slabMap Ω Ωs) Ω ∧
            (∀ w ∈ Ω, 0 < slabTop Ω Ωs w ∧ slabTop Ω Ωs w < ε) ∧
            (∀ w ∈ Ω, epstein Ωs (slabMap Ω Ωs w) = normalGeod Ω w (slabTop Ω Ωs w)) ∧
            IsOpen (gapSlab Ω (slabTop Ω Ωs)) ∧
            InjOn (normalMap Ω) (gapSlab Ω (slabTop Ω Ωs)) ∧
            normalMap Ω '' gapSlab Ω (slabTop Ω Ωs) = gap Ω Ωs ∧
            (∀ p ∈ gapSlab Ω (slabTop Ω Ωs),
              LinearMap.det (fderiv ℝ (normalMap Ω) p : (ℂ × ℝ) →ₗ[ℝ] (ℂ × ℝ)) ≠ 0) ∧
            BijOn (slabMap Ω Ωs) Ω Ωs ∧
            ∀ w ∈ Ω, (1 - CJ * ε) ^ 2 ≤ jacN Ω Ωs w ∧ jacN Ω Ωs w ≤ (1 + CJ * ε) ^ 2 := by
  -- `ε₀ = min (1/8) (1/(2(C_J+1)))`; `η` is the minimum of the helpers' `η₀` and `ε/2`.
  obtain ⟨CJ, hCJ, hjac⟩ := s10_pgg_jac
  have hc : 0 < 2 * (CJ + 1) := by positivity
  refine ⟨min (1 / 8) (1 / (2 * (CJ + 1))), CJ, lt_min (by norm_num) (by positivity),
    (min_le_left _ _).trans_lt (by norm_num), hCJ, ?_, fun ε hε hεle => ?_⟩
  · calc CJ * min (1 / 8) (1 / (2 * (CJ + 1))) ≤ CJ * (1 / (2 * (CJ + 1))) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hCJ
      _ ≤ 1 / 2 := by
          rw [mul_one_div, div_le_iff₀ hc]
          linarith
  have hε8 : ε ≤ 1 / 8 := hεle.trans (min_le_left _ _)
  have hε4 : ε < 1 / 4 := by linarith
  have hCε : CJ * ε ≤ 1 := by
    have h1 : CJ * ε ≤ CJ * (1 / (2 * (CJ + 1))) :=
      mul_le_mul_of_nonneg_left (hεle.trans (min_le_right _ _)) hCJ
    have h2 : CJ * (1 / (2 * (CJ + 1))) ≤ 1 := by
      rw [mul_one_div, div_le_iff₀ hc]
      linarith
    linarith
  obtain ⟨η₁, hη₁, hN⟩ := s10_pgg_N ε hε hε4
  obtain ⟨η₂, hη₂, hS⟩ := s10_pgg_slab ε hε hε4
  obtain ⟨η₃, hη₃, hD⟩ := s10_pgg_det ε hε hε4
  obtain ⟨η₄, hη₄, hU⟩ := s10_pgg_surj ε hε hε4
  obtain ⟨η₅, hη₅, hJc⟩ := hjac ε hε hε4
  have hη : 0 < min (min (min η₁ η₂) (min η₃ η₄)) (min η₅ (ε / 2)) :=
    lt_min (lt_min (lt_min hη₁ hη₂) (lt_min hη₃ hη₄)) (lt_min hη₅ (by linarith))
  have hη2 : min (min (min η₁ η₂) (min η₃ η₄)) (min η₅ (ε / 2)) ≤ ε / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨_, hη, by linarith, fun Ω Ωs hJ hnl hs hss => ?_⟩
  have hq : IsKQuasiPair Ω Ωs 3 := by
    refine lem_aw_three Ω Ωs hJ fun w hw => ?_
    obtain ⟨c', hc', hcw⟩ := hs
    linarith [hcw w hw]
  have e1 : min (min (min η₁ η₂) (min η₃ η₄)) (min η₅ (ε / 2)) ≤ η₁ :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have e2 : min (min (min η₁ η₂) (min η₃ η₄)) (min η₅ (ε / 2)) ≤ η₂ :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have e3 : min (min (min η₁ η₂) (min η₃ η₄)) (min η₅ (ε / 2)) ≤ η₃ :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have e4 : min (min (min η₁ η₂) (min η₃ η₄)) (min η₅ (ε / 2)) ≤ η₄ :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have e5 : min (min (min η₁ η₂) (min η₃ η₄)) (min η₅ (ε / 2)) ≤ η₅ :=
    (min_le_right _ _).trans (min_le_left _ _)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hN _ hη e1 Ω Ωs hq hnl hs hss
  obtain ⟨h7, h8, h9⟩ := hS _ hη e2 Ω Ωs hq hnl hs hss
  exact ⟨hq, h1, h2, h3, h4, h7, h8, h9, hD _ hη e3 Ω Ωs hq hnl hs hss,
    ⟨h5, h6, hU _ hη e4 Ω Ωs hq hnl hs hss⟩, fun w hw =>
      ⟨(hJc _ hη e5 Ω Ωs hq hnl hs hss w hw).1 hCε, (hJc _ hη e5 Ω Ωs hq hnl hs hss w hw).2⟩⟩

/-- **Proposition 10.11 (d), (e)** and the goodness claim of (a), `prop:global-graph`,
`sec10-sharp.tex:470` (constants of Convention 10.10 quantified existentially, `ε' = C₁ε`).
Under the hypotheses of (a)–(c): every `w ∈ Ω` is `(η(ε), R(ε))`-good;
(d) `𝓛` (with coefficients `(a, b, c) = graphCoeffs Ω Ωs Ω`) is `ε'`-admissible on `Ω`, and
`𝓛t = 2σ` on `Ω`; `σ` is smooth with `0 ≤ σ ≤ 2/3`, and `t = 𝒢_Ω(2σ)`;
(e) the formal adjoint `𝓛*` is `10ε'`-admissible on `Ω`. -/
theorem prop_global_graph_de :
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 4 ∧ 0 ≤ C₁ ∧ 10 * (C₁ * ε₀) ≤ 1 / 8 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ η : ℝ, 0 < η ∧ η < ε ∧ ∃ R : ℝ, 0 < R ∧
        ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ¬ IsLinePair Ω Ωs →
          SchwarzSupLt Ω η → SchwarzSupLt Ωs η →
          ∀ (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
            graphCoeffs Ω Ωs Ω = (aUp, bUp, c) →
            Ω ⊆ goodSet Ω Ωs η R ∧
            RepresentsOp Ω Ω (graphOp Ω Ωs) aUp bUp c ∧
            IsAdmissibleOp Ω Ω (C₁ * ε) aUp bUp c ∧
            (∀ w ∈ Ω, graphOp Ω Ωs (slabTop Ω Ωs) w = 2 * sigmaSrc Ω Ωs w) ∧
            ContDiffOn ℝ ∞ (sigmaSrc Ω Ωs) Ω ∧
            (∀ w ∈ Ω, 0 ≤ sigmaSrc Ω Ωs w ∧ sigmaSrc Ω Ωs w ≤ 2 / 3) ∧
            IsDirichletInverse Ω aUp bUp c Ω (fun w => 2 * sigmaSrc Ω Ωs w) (slabTop Ω Ωs) ∧
            IsAdmissibleOp Ω Ω (10 * (C₁ * ε)) aUp (adjCoeffB Ω aUp bUp)
              (adjCoeffC Ω aUp bUp c) := by
  sorry

/-! ## §10.4' Duality and the two bounds for the adjoint solution -/

/-- **Lemma 10.12**, `lem:duality`, `sec10-sharp.tex:563`.  In the setting of
`prop:global-graph`, with `κ = k_P ∘ X` and `u = 𝒢*_Ω κ` (the Dirichlet inverse of `𝓛*` on `Ω`):
(a) `∫_Ω κ t dâ = 2 ∫_Ω σ u dâ` in `[0, ∞]`;
(b) `0 ≤ u ≤ κ/(2 - C₂ε)` on `Ω`. -/
theorem lem_duality :
    ∃ ε₀ C₂ : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 4 ∧ 0 ≤ C₂ ∧ C₂ * ε₀ ≤ 1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ η : ℝ, 0 < η ∧ η < ε ∧
        ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ¬ IsLinePair Ω Ωs →
          SchwarzSupLt Ω η → SchwarzSupLt Ωs η →
          ∀ (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
            graphCoeffs Ω Ωs Ω = (aUp, bUp, c) → ∀ P ∈ UHS, ∀ u : ℂ → ℝ,
            u = dirichletInv Ω aUp (adjCoeffB Ω aUp bUp) (adjCoeffC Ω aUp bUp c) Ω
              (fun w => ambKernel P (epstein Ω w)) →
            (∫⁻ w, ENNReal.ofReal (ambKernel P (epstein Ω w) * slabTop Ω Ωs w) ∂hypArea Ω) =
                2 * ∫⁻ w, ENNReal.ofReal (sigmaSrc Ω Ωs w * u w) ∂hypArea Ω ∧
              ∀ w ∈ Ω, 0 ≤ u w ∧ u w ≤ ambKernel P (epstein Ω w) / (2 - C₂ * ε) := by
  sorry

/-! ## §10.5 The model lower bound -/

/-- Helper for `lem_model_lower_b`: `𝓛₀ = 2 - Δ_ρ` is the operator with coefficients
`a = λ⁻² 1`, `b = 0`, `c = 2`. -/
theorem s10_mlb_ellOp0 (Ω : Set ℂ) (u : ℂ → ℝ) (w : ℂ) :
    ellOp Ω (fun w => (poincareDensity Ω w ^ 2)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 (fun _ => 2)
      u w = 2 * u w - rhoLaplacian Ω u w := by
  unfold ellOp rhoLaplacian
  simp only [Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul,
    Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_one, mul_zero, add_zero, zero_add,
    sub_zero]
  ring

/-- Helper for `lem_model_lower_b`: `𝓛₀` is `ε'`-admissible on `Ω` for every `ε' ∈ (0, 1/8]`
(`a♭ = ρ` exactly, `b = 0`, `c = 2`, so the defect norm is `0`). -/
theorem s10_mlb_adm {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {ε' : ℝ} (h0 : 0 < ε')
    (h1 : ε' ≤ 1 / 8) :
    IsAdmissibleOp Ω Ω ε' (fun w => (poincareDensity Ω w ^ 2)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      0 (fun _ => 2) := by
  obtain ⟨hΩ, hρs, hρp⟩ := s05_density_smooth hJ
  have hz : ∀ j k : ℕ, rhoIterCovDeriv Ω j (0 : TensorField k) = 0 := by
    intro j
    induction j with
    | zero => intro k; rfl
    | succ j ih =>
      intro k
      have h0 : rhoCovDeriv Ω (0 : TensorField k) = 0 := by
        funext w v
        simp [rhoCovDeriv]
      funext w v
      show rhoIterCovDeriv Ω j (rhoCovDeriv Ω (0 : TensorField k)) w _ = 0
      rw [h0, ih]
      rfl
  have hn : ∀ (j k : ℕ) (E : Set ℂ), rhoCjNorm Ω j (0 : TensorField k) E = 0 := by
    intro j k E
    unfold rhoCjNorm
    simp [hz, rhoTensorNorm]
  have hA : lowerA Ω (fun w => (poincareDensity Ω w ^ 2)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) -
      rhoMetricT Ω = 0 := by
    funext w v
    simp only [Pi.sub_apply, Pi.zero_apply, lowerA, rhoMetricT, cvec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    by_cases hρ : poincareDensity Ω w = 0
    · simp [hρ]
    · field_simp
      ring
  have hB : lowerB Ω (0 : ℂ → Fin 2 → ℝ) = 0 := by
    funext w v
    simp [lowerB]
  have hC : (scalarField fun w => (fun _ : ℂ => (2 : ℝ)) w - 2) = 0 := by
    funext w v
    simp [scalarField]
  refine ⟨h0, h1, hΩ, subset_rfl, ⟨fun i j => ?_, fun i => ?_, contDiffOn_const, fun w _ => ?_⟩,
    ?_⟩
  · simp only [Matrix.smul_apply, smul_eq_mul]
    exact ((hρs.pow 2).inv fun w hw => pow_ne_zero 2 (hρp w hw).ne').mul contDiffOn_const
  · simp only [Pi.zero_apply]
    exact contDiffOn_const
  · rw [Matrix.transpose_smul, Matrix.transpose_one]
  · rw [hA, hB, hC, hn, hn, hn]
    simp

/-- Helper for `lem_model_lower_b`: conformal invariance of `Δ_ρ`; for a Riemann map
`f : 𝔻 → Ω` and `u ∈ C²(Ω)`, `u ∘ f ∈ C²(𝔻)` and `Δ_𝔻 (u ∘ f) = (Δ_ρ u) ∘ f`
(`s10_mlb_rhoLap`, `s10_pgg_lap_holo`, `eq_lambda_f`). -/
theorem s10_mlb_lap_conf {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) {u : ℂ → ℝ} (hu : ContDiffOn ℝ 2 u Ω) :
    ContDiffOn ℝ 2 (fun z => u (f z)) unitDisc ∧ ∀ z ∈ unitDisc,
      hypLaplacianDisk (fun z => u (f z)) z = rhoLaplacian Ω u (f z) := by
  have hmap : MapsTo f unitDisc Ω := fun z hz => hf.2.2 ▸ mem_image_of_mem f hz
  obtain ⟨h2, hl⟩ := s10_pgg_lap_holo isOpen_ball hΩ hu hf.1 hmap
  refine ⟨h2, fun z hz => ?_⟩
  rw [s10_mlb_rhoLap Ω hΩ hu (hmap hz)]
  show ((1 - ‖z‖ ^ 2) / 2) ^ 2 * Laplacian.laplacian (fun y => u (f y)) z = _
  rw [hl z hz]
  have he := eq_lambda_f hf hz
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hr : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hρ : poincareDensity Ω (f z) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at he
    exact (by positivity : (0 : ℝ) < 2 / (1 - ‖z‖ ^ 2)).ne he
  have hd : ‖deriv f z‖ = 2 / (1 - ‖z‖ ^ 2) / poincareDensity Ω (f z) := by
    rw [← he, mul_div_cancel_left₀ _ hρ]
  rw [hd]
  field_simp

/-- Helper for `lem_model_lower_b`: a Riemann map `f : 𝔻 → Ω` pushes `dâ_𝔻` to `dâ_Ω`,
`∫ φ dâ_Ω = ∫ φ ∘ f dâ_𝔻` for every `φ` (as `s07_pullback_mass_any` for `dm_Ω`). -/
theorem s10_mlb_area {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (φ : ℂ → ℝ≥0∞) :
    ∫⁻ w, φ w ∂hypArea Ω = ∫⁻ z, φ (f z) ∂diskHypArea := by
  have hD : MeasurableSet unitDisc := measurableSet_ball
  have hDo : IsOpen unitDisc := isOpen_ball
  obtain ⟨G, hGm, hGf⟩ := s07_measurable_leftInv hf.1.continuousOn hf.2.1
  have hΩm : MeasurableSet Ω := by
    rw [← hf.2.2]
    exact hD.image_of_continuousOn_injOn hf.1.continuousOn hf.2.1
  set h : ℂ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2 / ‖deriv f z‖ ^ 2) with hhdef
  have hhm : Measurable h := by
    have h2 : Measurable (deriv f) := measurable_deriv f
    simp only [hhdef]
    fun_prop
  have hdf : ∀ z ∈ unitDisc, ENNReal.ofReal (poincareDensity Ω (f z) ^ 2) = h z := by
    intro z hz
    have he := eq_lambda_f hf hz
    have hn : ‖deriv f z‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (deriv_ne_zero_of_injOn hDo hf.1 hf.2.1 hz)
    simp only [hhdef]
    rw [← he, mul_pow, mul_div_cancel_right₀ _ (pow_ne_zero 2 hn)]
  have hdm : AEMeasurable (fun w => ENNReal.ofReal (poincareDensity Ω w ^ 2))
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
  have hdisk : Measurable fun z : ℂ => ENNReal.ofReal ((2 / (1 - ‖z‖ ^ 2)) ^ 2) := by fun_prop
  rw [hypArea, lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hdm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), hres,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hD hder hf.2.1, diskHypArea,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ hdisk
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine setLIntegral_congr_fun hD (fun z hz => ?_)
  have he := eq_lambda_f hf hz
  simp only [Pi.mul_apply]
  rw [s02_pullback_det, ← mul_assoc, abs_of_nonneg (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← he]
  congr 2
  ring

/-- Helper for `lem_model_lower_b`: `κ = k_P ∘ X` is smooth on `Ω` with `0 ≤ κ ≤ 1`. -/
theorem s10_mlb_kappa {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {P : ℂ × ℝ} (hP : P ∈ UHS) :
    ContDiffOn ℝ ∞ (fun w => ambKernel P (epstein Ω w)) Ω ∧
      ∀ w ∈ Ω, 0 ≤ ambKernel P (epstein Ω w) ∧ ambKernel P (epstein Ω w) ≤ 1 := by
  have hk : ∀ Q, 0 ≤ ambKernel P Q ∧ ambKernel P Q ≤ 1 := fun Q => by
    unfold ambKernel
    have h1 := Real.one_le_cosh (hdist P Q / 2)
    have h2 : (Real.cosh (hdist P Q / 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    have h3 : 0 ≤ (Real.cosh (hdist P Q / 2))⁻¹ := by positivity
    exact ⟨by positivity, pow_le_one₀ h3 h2⟩
  refine ⟨fun w hw => ?_, fun w _ => hk _⟩
  obtain ⟨f, hf, -⟩ := s02_riemannMap_at hJ hw
  have hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω := ⟨f, hf⟩
  have hmap : MapsTo (epstein Ω) Ω UHS := fun x hx => by
    have h1 := (s02_ep_position hΩ hx).1
    have hρ := (s05_density_smooth hJ).2.2 x hx
    show 0 < (epstein Ω x).2
    exact lt_of_lt_of_le (by positivity) h1
  exact ((s09_contDiffOn_ambKernel P hP).comp (lem_fff_smooth hΩ) hmap) w hw

/-- Helper for `lem_model_lower_b` (`lem_plane_green_g` on `Ω`): a bounded `u ∈ C²(Ω)` with
`F = 2u - Δ_ρ u ≥ 0` is `u = 𝔊 * F` (pull back by a Riemann map `f` with `f 0 = p`). -/
theorem s10_mlb_rep {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ 2 u Ω) (hub : ∃ M : ℝ, ∀ w ∈ Ω, |u w| ≤ M) {F : ℂ → ℝ}
    (hF : ∀ w ∈ Ω, 2 * u w - rhoLaplacian Ω u w = F w) (hF0 : ∀ w ∈ Ω, 0 ≤ F w)
    {p : ℂ} (hp : p ∈ Ω) :
    ENNReal.ofReal (u p) = resolventConv Ω F p := by
  obtain ⟨hΩ, -, -⟩ := s05_density_smooth hJ
  obtain ⟨f, hf, hf0⟩ := s02_riemannMap_at hJ hp
  obtain ⟨h2, hl⟩ := s10_mlb_lap_conf hΩ hf hu
  have hmap : ∀ z ∈ unitDisc, f z ∈ Ω := fun z hz => hf.2.2 ▸ mem_image_of_mem f hz
  obtain ⟨M, hM⟩ := hub
  have hF' : ∀ z ∈ unitDisc,
      2 * u (f z) - hypLaplacianDisk (fun z => u (f z)) z = F (f z) := fun z hz => by
    rw [hl z hz]
    exact hF _ (hmap z hz)
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hg := (lem_plane_green_g (fun z => u (f z)) h2 ⟨M, fun z hz => hM _ (hmap z hz)⟩
    (fun z hz => by rw [hF' z hz]; exact hF0 _ (hmap z hz)) 0 h0).2
  simp only [hf0] at hg
  rw [hg, resolventConv,
    s10_mlb_area hf (fun w => ENNReal.ofReal (resolventG (poincareDist Ω p w) * F w))]
  have hae : ∀ᵐ z ∂diskHypArea, z ∈ unitDisc :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_ball)
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with z hz
  rw [hF' z hz, ← hf0, subsec_poincare_dist hf h0 hz]

/-- **Lemma 10.15 (a)**, `lem:model-lower`, `sec10-sharp.tex:667`, for `v = 𝔊 * κ` (which is
`v = 𝒢⁰_Ω κ` by part (b)), `κ = k_P ∘ X`: `0 ≤ v ≤ κ/(2 - C₂ε) ≤ κ`. -/
theorem lem_model_lower_a :
    ∃ C₂ ε₀ : ℝ, 0 ≤ C₂ ∧ 0 < ε₀ ∧ ε₀ < 1 / 4 ∧ C₂ * ε₀ ≤ 1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ η : ℝ, 0 < η ∧ η < ε ∧
        ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ¬ IsLinePair Ω Ωs →
          SchwarzSupLt Ω η → SchwarzSupLt Ωs η → ∀ P ∈ UHS, ∀ p ∈ Ω,
            resolventConv Ω (fun w => ambKernel P (epstein Ω w)) p ≤
              ENNReal.ofReal (ambKernel P (epstein Ω p) / (2 - C₂ * ε)) := by
  -- `Δ_ρ κ ≤ -κ² + C₂ s κ` (`lem:ambient-adjoint` (b)) gives `2κ - Δ_ρ κ ≥ (2 - C₂ε)κ ≥ 0`, and
  -- `κ = 𝔊 * (2κ - Δ_ρ κ)` (`s10_mlb_rep`); the bounds on `Ωs` and `¬ IsLinePair` are not needed
  obtain ⟨C₂, hC₂, hlap⟩ := s09_au_lap
  have hε₀ : 1 / (8 * (C₂ + 1)) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hCε₀ : C₂ * (1 / (8 * (C₂ + 1))) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]
    nlinarith
  refine ⟨C₂, 1 / (8 * (C₂ + 1)), hC₂, by positivity, by linarith, hCε₀,
    fun ε hε hεle => ⟨ε / 2, by linarith, by linarith,
      fun Ω Ωs hJ _ hS _ P hP p hp => ?_⟩⟩
  obtain ⟨c', hc', hsc⟩ := hS
  obtain ⟨hκs, hκb⟩ := s10_mlb_kappa hJ hP
  have hCε : C₂ * ε ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hεle hC₂) hCε₀
  have hc : 0 < 2 - C₂ * ε := by linarith
  have hF : ∀ w ∈ Ω, (2 - C₂ * ε) * ambKernel P (epstein Ω w) ≤
      2 * ambKernel P (epstein Ω w) -
        rhoLaplacian Ω (fun x => ambKernel P (epstein Ω x)) w := by
    intro w hw
    have hs : schwarzNorm Ω w ≤ ε / 2 := (hsc w hw).trans hc'.le
    have h1 := hlap Ω Ωs hJ P hP w hw (by linarith)
    have h2 := (hκb w hw).1
    nlinarith [mul_nonneg (mul_nonneg hC₂ (by linarith : (0 : ℝ) ≤ ε - schwarzNorm Ω w)) h2,
      sq_nonneg (ambKernel P (epstein Ω w))]
  have hrep := s10_mlb_rep hJ (hκs.of_le (by norm_cast))
    ⟨1, fun w hw => by rw [abs_of_nonneg (hκb w hw).1]; exact (hκb w hw).2⟩ (fun w _ => rfl)
    (fun w hw => le_trans (mul_nonneg hc.le (hκb w hw).1) (hF w hw)) hp
  have hΩm : MeasurableSet Ω := (s05_density_smooth hJ).1.measurableSet
  have hae : ∀ᵐ w ∂hypArea Ω, w ∈ Ω :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩm)
  have hmul : ENNReal.ofReal (2 - C₂ * ε) *
      resolventConv Ω (fun w => ambKernel P (epstein Ω w)) p ≤
        ENNReal.ofReal (ambKernel P (epstein Ω p)) := by
    rw [hrep, resolventConv, resolventConv, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with w hw
    rw [← ENNReal.ofReal_mul hc.le]
    by_cases hG : 0 ≤ resolventG (poincareDist Ω p w)
    · refine ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_left (hF w hw) hG
      nlinarith
    · rw [ENNReal.ofReal_of_nonpos]
      · exact bot_le
      · exact mul_nonpos_of_nonneg_of_nonpos hc.le
          (mul_nonpos_of_nonpos_of_nonneg (not_le.mp hG).le (hκb w hw).1)
  rw [ENNReal.ofReal_div_of_pos hc, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hc))
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact hmul

/-- **Lemma 10.15 (b)**, `lem:model-lower`, `sec10-sharp.tex:670`: `v = 𝒢⁰_Ω κ` (the Dirichlet
inverse of `𝓛₀ = 2 - Δ_ρ` on `Ω`, `κ = k_P ∘ X`) is `v(p) = ∫_Ω 𝔊(d_ρ(p, w)) κ(w) dâ(w)`. -/
theorem lem_model_lower_b :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 4 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ η : ℝ, 0 < η ∧ η < ε ∧
        ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ¬ IsLinePair Ω Ωs →
          SchwarzSupLt Ω η → SchwarzSupLt Ωs η → ∀ P ∈ UHS, ∀ v : ℂ → ℝ,
            v = dirichletInv Ω (fun w => (poincareDensity Ω w ^ 2)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
              0 (fun _ => 2) Ω (fun w => ambKernel P (epstein Ω w)) →
            ∀ p ∈ Ω, ENNReal.ofReal (v p) = resolventConv Ω (fun w => ambKernel P (epstein Ω w)) p := by
  -- `ε`, `η` and the Schwarzian bounds are not needed: (b) holds for every Jordan domain
  refine ⟨1 / 8, by norm_num, by norm_num, fun ε hε _ => ⟨ε / 2, by linarith, by linarith,
    fun Ω Ωs hJ _ _ _ P hP v hv p hp => ?_⟩⟩
  obtain ⟨hκs, hκb⟩ := s10_mlb_kappa hJ hP
  have hadm := s10_mlb_adm hJ (ε' := 1 / 8) (by norm_num) le_rfl
  obtain ⟨-, G₀, hG₀, hG₀b⟩ := prop_dirichlet_a Ω Ωs hJ Ω (1 / 8) _ 0 (fun _ => 2) hadm _ 1 hκs hκb
  have hvG : IsDirichletInverse Ω
      (fun w => (poincareDensity Ω w ^ 2)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 (fun _ => 2) Ω
      (fun w => ambKernel P (epstein Ω w)) v := by
    rw [hv]
    unfold dirichletInv
    split_ifs with h
    · exact h.choose_spec
    · exact absurd ⟨G₀, hG₀⟩ h
  -- uniqueness of bounded solutions (`prop_dirichlet_c`): the chosen inverse is `G₀`
  have heq := (prop_dirichlet_c Ω Ωs hJ (1 / 8) _ 0 (fun _ => 2) hadm _ 1 hκs hκb v hvG).1 G₀
    hG₀.1 ⟨1 / (2 - 1 / 8), fun w hw => by
      rw [abs_of_nonneg (hG₀b w hw).1]
      exact (hG₀b w hw).2⟩ hG₀.2.1
  refine s10_mlb_rep hJ hvG.1 ⟨1 / (2 - 1 / 8), fun w hw => ?_⟩ (fun w hw => ?_)
    (fun w hw => (hκb w hw).1) hp
  · rw [← heq w hw, abs_of_nonneg (hG₀b w hw).1]
    exact (hG₀b w hw).2
  · rw [← s10_mlb_ellOp0]
    exact hvG.2.1 w hw

/-- **Lemma 10.15 (c)**, `lem:model-lower`, `sec10-sharp.tex:675`, for `v = 𝔊 * κ`,
`κ = k_P ∘ X`: for every `Λ > 0` and `p ∈ Ω`,
`v(p) ≥ e^{-C_Λ ε} (1-ε)/(1+ε) (1 - log 2 - ϑ(Λ)) κ(p)` with `C_Λ = (4 + C₃) e^{3Λ}`. -/
theorem lem_model_lower_c :
    ∃ C₃ ε₀ : ℝ, 0 ≤ C₃ ∧ 0 < ε₀ ∧ ε₀ < 1 / 4 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ η : ℝ, 0 < η ∧ η < ε ∧
        ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ¬ IsLinePair Ω Ωs →
          SchwarzSupLt Ω η → SchwarzSupLt Ωs η → ∀ P ∈ UHS, ∀ Λ : ℝ, 0 < Λ → ∀ p ∈ Ω,
            ENNReal.ofReal (Real.exp (-((4 + C₃) * Real.exp (3 * Λ) * ε)) * ((1 - ε) / (1 + ε)) *
                (1 - Real.log 2 - resolventTail Λ) * ambKernel P (epstein Ω p)) ≤
              resolventConv Ω (fun w => ambKernel P (epstein Ω w)) p := by
  sorry

/-- **Lemma 10.16**, `lem:schauder`, `sec10-sharp.tex:724`.  In the setting of `lem:duality`, with
`v = 𝒢⁰_Ω κ`: there is an absolute `C₄` with `|∇v| + |∇²v| ≤ C₄κ` on `Ω`; consequently, with
`β_ε = (5 + 4C₄)C₁ε`, `𝓛*v ≤ (1 + β_ε)κ` and `u ≥ v/(1 + β_ε)` on `Ω`. -/
theorem lem_schauder :
    ∃ ε₀ C₁ C₄ : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 4 ∧ 0 ≤ C₁ ∧ 0 ≤ C₄ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ η : ℝ, 0 < η ∧ η < ε ∧
        ∀ Ω Ωs : Set ℂ, IsJordanPair Ω Ωs → ¬ IsLinePair Ω Ωs →
          SchwarzSupLt Ω η → SchwarzSupLt Ωs η →
          ∀ (aUp : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bUp : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
            graphCoeffs Ω Ωs Ω = (aUp, bUp, c) → ∀ P ∈ UHS, ∀ u v : ℂ → ℝ,
            u = dirichletInv Ω aUp (adjCoeffB Ω aUp bUp) (adjCoeffC Ω aUp bUp c) Ω
              (fun w => ambKernel P (epstein Ω w)) →
            v = dirichletInv Ω (fun w => (poincareDensity Ω w ^ 2)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
              0 (fun _ => 2) Ω (fun w => ambKernel P (epstein Ω w)) →
            (∀ w ∈ Ω, rhoTensorNorm Ω (rhoCovDeriv Ω (scalarField v)) w +
                rhoTensorNorm Ω (rhoHess Ω v) w ≤ C₄ * ambKernel P (epstein Ω w)) ∧
              (∀ w ∈ Ω, ellOpAdj Ω aUp bUp c v w ≤
                (1 + (5 + 4 * C₄) * C₁ * ε) * ambKernel P (epstein Ω w)) ∧
              ∀ w ∈ Ω, v w / (1 + (5 + 4 * C₄) * C₁ * ε) ≤ u w := by
  sorry

/-! ## §10.7 Injectivity of the kernel transform -/

/-- `sec10-sharp.tex:904`: `V = 𝒯(vol|_𝒩)`. -/
theorem ambV_eq_kernelTransform (Ω Ωs : Set ℂ) (P : ℂ × ℝ) :
    ambV Ω Ωs P = kernelTransform (hvol.restrict (gap Ω Ωs)) P := by
  rfl

/-- Helper for `thm_injective`: `‖Z‖² = Z₀² + Z₁² + Z₂² + Z₃²` in `ℝ⁴`. -/
theorem s10_inj_nsq (Z : EuclideanSpace ℝ (Fin 4)) :
    ‖Z‖ ^ 2 = Z 0 ^ 2 + Z 1 ^ 2 + Z 2 ^ 2 + Z 3 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_four]
  simp only [Real.norm_eq_abs, sq_abs]

/-- Helper for `thm_injective`: a measure carried by `UHS` is a.e. on `UHS`. -/
theorem s10_inj_ae (μ : Measure (ℂ × ℝ)) (hμ : μ UHSᶜ = 0) : ∀ᵐ q ∂μ, q ∈ UHS :=
  ae_iff.mpr hμ

/-- Helper for `thm_injective`: the lift `ι(W, ξ) = (Re W, Im W, -ξ, 0)` is continuous. -/
theorem s10_inj_cont :
    Continuous fun q : ℂ × ℝ => (!₂[q.1.re, q.1.im, -q.2, 0] : EuclideanSpace ℝ (Fin 4)) := by
  fun_prop

/-- Helper for `thm_injective`: `Z ↦ (Z₀ + i Z₁, -Z₂)` is a continuous left inverse of `ι`. -/
theorem s10_inj_linv :
    Continuous (fun Z : EuclideanSpace ℝ (Fin 4) => ((Z 0 : ℂ) + (Z 1 : ℂ) * Complex.I, -Z 2)) ∧
      ∀ q : ℂ × ℝ, (fun Z : EuclideanSpace ℝ (Fin 4) => ((Z 0 : ℂ) + (Z 1 : ℂ) * Complex.I, -Z 2))
        (!₂[q.1.re, q.1.im, -q.2, 0]) = q := by
  refine ⟨by fun_prop, fun q => ?_⟩
  simp [Complex.re_add_im]

/-- Helper for `thm_injective` (J1, `sec10-sharp.tex:930`): `𝒯μ(P) ≤ e^{d(P, P₀)} 𝒯μ(P₀)`
(`lem_ambient_kernel_e`), so `𝒯μ` is finite on `ℍ³` once it is finite at one point. -/
theorem s10_inj_finite (μ : Measure (ℂ × ℝ)) (hμ : μ UHSᶜ = 0) (P₀ : ℂ × ℝ) (hP₀ : P₀ ∈ UHS)
    (h : kernelTransform μ P₀ < ⊤) : ∀ P ∈ UHS, kernelTransform μ P < ⊤ := by
  intro P hP
  calc kernelTransform μ P = ∫⁻ q, ENNReal.ofReal (ambKernel P q) ∂μ := rfl
    _ ≤ ∫⁻ q, ENNReal.ofReal (Real.exp (hdist P P₀)) * ENNReal.ofReal (ambKernel P₀ q) ∂μ := by
        refine lintegral_mono_ae ((s10_inj_ae μ hμ).mono fun q hq => ?_)
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        exact ENNReal.ofReal_le_ofReal (lem_ambient_kernel_e P q q P₀ hP hq hq hP₀).2.2.1
    _ = ENNReal.ofReal (Real.exp (hdist P P₀)) * kernelTransform μ P₀ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

/-- Helper for `thm_injective` (J1, the lift mass (10.29) `eq:lift-mass`):
`∫ ξ / (1 + |W|² + ξ²) dμ ≤ ½ 𝒯μ(j) < ∞`, by the half-space formula of `k_j`. -/
theorem s10_inj_mass (μ : Measure (ℂ × ℝ)) (hμ : μ UHSᶜ = 0)
    (h : ∀ P ∈ UHS, kernelTransform μ P < ⊤) :
    ∫⁻ q, ENNReal.ofReal (q.2 / (1 + ‖q.1‖ ^ 2 + q.2 ^ 2)) ∂μ < ⊤ := by
  have hj : ((0 : ℂ), (1 : ℝ)) ∈ UHS := show (0 : ℝ) < 1 from one_pos
  calc ∫⁻ q, ENNReal.ofReal (q.2 / (1 + ‖q.1‖ ^ 2 + q.2 ^ 2)) ∂μ
      ≤ ∫⁻ q, ENNReal.ofReal (1 / 2) * ENNReal.ofReal (ambKernel ((0 : ℂ), (1 : ℝ)) q) ∂μ := by
        refine lintegral_mono_ae ((s10_inj_ae μ hμ).mono fun q hq => ?_)
        have hq' : 0 < q.2 := hq
        rw [← ENNReal.ofReal_mul (by norm_num), s09_ambKernel_eq _ q hj hq]
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [sub_zero]
        have hB : 0 < ‖q.1‖ ^ 2 + (q.2 + 1) ^ 2 := by positivity
        have hBA : ‖q.1‖ ^ 2 + (q.2 + 1) ^ 2 ≤ 2 * (1 + ‖q.1‖ ^ 2 + q.2 ^ 2) := by
          nlinarith [sq_nonneg (q.2 - 1), sq_nonneg ‖q.1‖]
        calc q.2 / (1 + ‖q.1‖ ^ 2 + q.2 ^ 2)
            = 2 * q.2 / (2 * (1 + ‖q.1‖ ^ 2 + q.2 ^ 2)) := by
              rw [mul_div_mul_left _ _ two_ne_zero]
          _ ≤ 2 * q.2 / (‖q.1‖ ^ 2 + (q.2 + 1) ^ 2) :=
              div_le_div_of_nonneg_left (by positivity) hB hBA
          _ = 1 / 2 * (4 * q.2 * 1 / (‖q.1‖ ^ 2 + (q.2 + 1) ^ 2)) := by ring
    _ = ENNReal.ofReal (1 / 2) * kernelTransform μ ((0 : ℂ), (1 : ℝ)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (h _ hj)

/-- Helper for `thm_injective` (J2, Step 2(ii)): for `P = (x₀, ξ₀) ∈ ℍ³`,
`𝒯μ(P) = 4ξ₀ 𝒰(x₀, ξ₀, 0)`, where `𝒰(Z) = ∫ ξ |Z - ι(W, ξ)|⁻² dμ` and
`ι(W, ξ) = (Re W, Im W, -ξ, 0) ∈ ℝ⁴` (`lem_ambient_kernel_a`). -/
theorem s10_inj_eval (μ : Measure (ℂ × ℝ)) (hμ : μ UHSᶜ = 0) (P : ℂ × ℝ) (hP : P ∈ UHS)
    (U : EuclideanSpace ℝ (Fin 4) → ℝ≥0∞)
    (hU : ∀ Z, U Z = ∫⁻ q, ENNReal.ofReal (q.2 / ‖Z - !₂[q.1.re, q.1.im, -q.2, 0]‖ ^ 2) ∂μ) :
    kernelTransform μ P = ENNReal.ofReal (4 * P.2) * U !₂[P.1.re, P.1.im, P.2, 0] := by
  have hP' : 0 < P.2 := hP
  rw [hU, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ((s10_inj_ae μ hμ).mono fun q hq => ?_)
  have hq' : 0 < q.2 := hq
  dsimp only
  rw [← ENNReal.ofReal_mul (by positivity), ((lem_ambient_kernel_a P hP).2 q hq).2.2]
  have hN : ‖(!₂[P.1.re, P.1.im, P.2, 0] : EuclideanSpace ℝ (Fin 4)) -
      !₂[q.1.re, q.1.im, -q.2, 0]‖ ^ 2 = ‖q.1 - P.1‖ ^ 2 + (q.2 + P.2) ^ 2 := by
    rw [s10_inj_nsq, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [hN]
  congr 1
  ring

/-- Helper for `thm_injective` (J3, Step 2(iii)): `∫_{|Z| < ρ} |Z - y|⁻² dZ ≤ C_ρ (1 + |y|²)⁻¹` in
`ℝ⁴`, uniformly in `y`. -/
theorem s10_inj_loc (ρ : ℝ) (hρ : 0 < ρ) : ∃ C : ℝ≥0, ∀ y : EuclideanSpace ℝ (Fin 4),
    ∫⁻ Z in ball 0 ρ, ENNReal.ofReal ((‖Z - y‖ ^ 2)⁻¹) ≤
      (C : ℝ≥0∞) * ENNReal.ofReal ((1 + ‖y‖ ^ 2)⁻¹) := by
  obtain ⟨g, hg⟩ : ∃ g : EuclideanSpace ℝ (Fin 4) → ℝ≥0∞,
      g = fun Z => ENNReal.ofReal ((‖Z‖ ^ 2)⁻¹) := ⟨_, rfl⟩
  -- `|Z|⁻²` is integrable near `0` in `ℝ⁴`
  have hI : ∫⁻ Z in ball 0 (3 * ρ), g Z < ⊤ := by
    have hint : IntegrableOn (fun Z : EuclideanSpace ℝ (Fin 4) => (‖Z‖ ^ 2)⁻¹)
        (ball 0 (3 * ρ)) volume := by
      refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := 2)
        (by norm_num [finrank_euclideanSpace]) (by norm_num [finrank_euclideanSpace])
        (Eventually.of_forall fun Z => ?_)
        (continuous_norm.pow 2).measurable.inv.aestronglyMeasurable
      rw [one_mul, Real.rpow_neg (norm_nonneg Z), Real.rpow_two, norm_inv, norm_pow, norm_norm]
    rw [hg]
    exact Integrable.lintegral_lt_top hint
  obtain ⟨A, hA⟩ : ∃ A : ℝ≥0∞, A = (∫⁻ Z in ball 0 (3 * ρ), g Z) * ENNReal.ofReal (1 + 4 * ρ ^ 2) :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ≥0∞, B = volume (ball (0 : EuclideanSpace ℝ (Fin 4)) ρ) *
      ENNReal.ofReal (4 * (1 + (4 * ρ ^ 2)⁻¹)) := ⟨_, rfl⟩
  have hAt : A ≠ ⊤ := by rw [hA]; exact ENNReal.mul_ne_top hI.ne ENNReal.ofReal_ne_top
  have hBt : B ≠ ⊤ := by rw [hB]; exact ENNReal.mul_ne_top measure_ball_lt_top.ne ENNReal.ofReal_ne_top
  refine ⟨(A + B).toNNReal, fun y => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.add_ne_top.mpr ⟨hAt, hBt⟩)]
  have hy0 : 0 < 1 + ‖y‖ ^ 2 := by positivity
  rcases lt_or_ge ‖y‖ (2 * ρ) with hy | hy
  · -- `|y| < 2ρ`: `B(0, ρ) ⊆ B(y, 3ρ)` and translation invariance
    have h1 : 1 ≤ ENNReal.ofReal (1 + 4 * ρ ^ 2) * ENNReal.ofReal ((1 + ‖y‖ ^ 2)⁻¹) := by
      rw [← ENNReal.ofReal_mul (by positivity), ENNReal.one_le_ofReal, ← div_eq_mul_inv,
        one_le_div hy0]
      have : ‖y‖ ^ 2 < (2 * ρ) ^ 2 := pow_lt_pow_left₀ hy (norm_nonneg y) two_ne_zero
      nlinarith
    calc ∫⁻ Z in ball 0 ρ, ENNReal.ofReal ((‖Z - y‖ ^ 2)⁻¹)
        ≤ ∫⁻ Z in ball y (3 * ρ), ENNReal.ofReal ((‖Z - y‖ ^ 2)⁻¹) := by
          refine lintegral_mono_set fun Z hZ => ?_
          rw [mem_ball_zero_iff] at hZ
          rw [mem_ball, dist_eq_norm]
          linarith [norm_sub_le Z y]
      _ = ∫⁻ Z in ball 0 (3 * ρ), g Z := by
          rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball,
            ← lintegral_sub_right_eq_self (fun Z => (ball (0 : EuclideanSpace ℝ (Fin 4)) (3 * ρ)).indicator g Z) y]
          refine lintegral_congr fun Z => ?_
          by_cases hZ : ‖Z - y‖ < 3 * ρ
          · simp [Metric.mem_ball, dist_eq_norm, hg, hZ]
          · simp [Metric.mem_ball, dist_eq_norm, hg, hZ]
      _ = (∫⁻ Z in ball 0 (3 * ρ), g Z) * 1 := (mul_one _).symm
      _ ≤ (∫⁻ Z in ball 0 (3 * ρ), g Z) *
            (ENNReal.ofReal (1 + 4 * ρ ^ 2) * ENNReal.ofReal ((1 + ‖y‖ ^ 2)⁻¹)) :=
          by gcongr
      _ = A * ENNReal.ofReal ((1 + ‖y‖ ^ 2)⁻¹) := by rw [hA, mul_assoc]
      _ ≤ (A + B) * ENNReal.ofReal ((1 + ‖y‖ ^ 2)⁻¹) := by gcongr; exact le_self_add
  · -- `|y| ≥ 2ρ`: `|Z - y| ≥ |y|/2` on `B(0, ρ)`
    have hy2 : 0 < ‖y‖ := by linarith
    have hq : 1 ≤ ‖y‖ ^ 2 * (4 * ρ ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, one_le_div (by positivity)]
      nlinarith
    have key : (‖y‖ ^ 2)⁻¹ ≤ (1 + (4 * ρ ^ 2)⁻¹) * (1 + ‖y‖ ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) hy0]
      nlinarith
    calc ∫⁻ Z in ball 0 ρ, ENNReal.ofReal ((‖Z - y‖ ^ 2)⁻¹)
        ≤ ∫⁻ _ in ball (0 : EuclideanSpace ℝ (Fin 4)) ρ, ENNReal.ofReal (4 * (‖y‖ ^ 2)⁻¹) := by
          refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).mpr
            (Eventually.of_forall fun Z hZ => ENNReal.ofReal_le_ofReal ?_))
          rw [mem_ball_zero_iff] at hZ
          have h3 : ‖y‖ / 2 ≤ ‖Z - y‖ := by
            have := norm_sub_norm_le y Z
            rw [norm_sub_rev y Z] at this
            linarith
          calc (‖Z - y‖ ^ 2)⁻¹ ≤ ((‖y‖ / 2) ^ 2)⁻¹ :=
                inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h3 2)
            _ = 4 * (‖y‖ ^ 2)⁻¹ := by rw [div_pow, inv_div]; ring
      _ = volume (ball (0 : EuclideanSpace ℝ (Fin 4)) ρ) * ENNReal.ofReal (4 * (‖y‖ ^ 2)⁻¹) := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ volume (ball (0 : EuclideanSpace ℝ (Fin 4)) ρ) *
            (ENNReal.ofReal (4 * (1 + (4 * ρ ^ 2)⁻¹)) * ENNReal.ofReal ((1 + ‖y‖ ^ 2)⁻¹)) := by
          gcongr _ * ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          calc 4 * (‖y‖ ^ 2)⁻¹ ≤ 4 * ((1 + (4 * ρ ^ 2)⁻¹) * (1 + ‖y‖ ^ 2)⁻¹) :=
                mul_le_mul_of_nonneg_left key (by norm_num)
            _ = 4 * (1 + (4 * ρ ^ 2)⁻¹) * (1 + ‖y‖ ^ 2)⁻¹ := by ring
      _ = B * ENNReal.ofReal ((1 + ‖y‖ ^ 2)⁻¹) := by rw [hB, mul_assoc]
      _ ≤ (A + B) * ENNReal.ofReal ((1 + ‖y‖ ^ 2)⁻¹) := by gcongr; exact le_add_self

/-- Helper for `thm_injective` (J4): in `ℝ⁴`, `|x|⁻² = 4π² G₄(x)` with `G₄` the Newtonian kernel
(`vol B⁴ = π²/2`). -/
theorem s10_inj_g_kernel (x : EuclideanSpace ℝ (Fin 4)) :
    (‖x‖ ^ 2)⁻¹ = 4 * π ^ 2 * TauCeti.newtonianKernel 4 x := by
  have hv : volume.real (ball (0 : EuclideanSpace ℝ (Fin 4)) 1) = π ^ 2 / 2 := by
    have hΓ : Real.Gamma ((4 : ℝ) / 2 + 1) = 2 := by
      rw [show (4 : ℝ) / 2 + 1 = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
      norm_num
    have hs : Real.sqrt π ^ 4 = π ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt Real.pi_pos.le]
    rw [measureReal_def, EuclideanSpace.volume_ball, Fintype.card_fin, ENNReal.ofReal_one, one_pow,
      one_mul, ENNReal.toReal_ofReal (by positivity)]
    push_cast
    rw [hΓ, hs]
  rw [TauCeti.newtonianKernel_def, hv]
  have he : (2 : ℝ) - ((4 : ℕ) : ℝ) = -(2 : ℕ) := by norm_num
  rw [he, Real.rpow_neg (norm_nonneg x), Real.rpow_natCast]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- Helper for `thm_injective` (J4): `∫ Δφ(Z) |Z - a|⁻² dZ = -4π² φ(a)` for `φ ∈ C²_c(ℝ⁴)`
(`TauCeti.integral_laplacian_mul_newtonianKernel_sub`). -/
theorem s10_inj_g_pole (φ : EuclideanSpace ℝ (Fin 4) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (a : EuclideanSpace ℝ (Fin 4)) :
    ∫ Z, Laplacian.laplacian φ Z * (‖Z - a‖ ^ 2)⁻¹ = -(4 * π ^ 2) * φ a := by
  have h := TauCeti.integral_laplacian_mul_newtonianKernel_sub (by norm_num : 3 ≤ 4) hφ hc a
  calc ∫ Z, Laplacian.laplacian φ Z * (‖Z - a‖ ^ 2)⁻¹
      = ∫ Z, 4 * π ^ 2 * (Laplacian.laplacian φ Z * TauCeti.newtonianKernel 4 (Z - a)) := by
        refine integral_congr_ae (Eventually.of_forall fun Z => ?_)
        dsimp only
        rw [s10_inj_g_kernel]
        ring
    _ = -(4 * π ^ 2) * φ a := by
        rw [integral_const_mul, h]
        ring

/-- Helper for `thm_injective` (J4): `ofReal (ξ/D) · ofReal (D/N) = ofReal (ξ/N)` for `D > 0`,
`N ≥ 0`. -/
theorem s10_inj_g_ofReal {ξ D N : ℝ} (hD : 0 < D) (hN : 0 ≤ N) :
    ENNReal.ofReal (ξ / D) * ENNReal.ofReal (D / N) = ENNReal.ofReal (ξ / N) := by
  rcases le_or_gt 0 ξ with h | h
  · rw [← ENNReal.ofReal_mul (div_nonneg h hD.le)]
    congr 1
    rcases eq_or_ne N 0 with hN0 | hN0
    · simp [hN0]
    · field_simp
  · rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg h.le hD.le), zero_mul,
      ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg h.le hN)]

/-- Helper for `thm_injective` (J4): `‖ι(W, ξ)‖² = |W|² + ξ²`. -/
theorem s10_inj_g_niota (q : ℂ × ℝ) :
    ‖(!₂[q.1.re, q.1.im, -q.2, 0] : EuclideanSpace ℝ (Fin 4))‖ ^ 2 = ‖q.1‖ ^ 2 + q.2 ^ 2 := by
  rw [s10_inj_nsq, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- Helper for `thm_injective` (J5): `Π₋ = {(W, t, 0) : t ≤ 0}` is closed in `ℝ⁴`. -/
theorem s10_inj_h_closed :
    IsClosed {Z : EuclideanSpace ℝ (Fin 4) | Z 3 = 0 ∧ Z 2 ≤ 0} :=
  (isClosed_eq (show Continuous fun Z : EuclideanSpace ℝ (Fin 4) => Z 3 by fun_prop)
    continuous_const).inter
      (isClosed_le (show Continuous fun Z : EuclideanSpace ℝ (Fin 4) => Z 2 by fun_prop)
        continuous_const)

/-- Helper for `thm_injective` (J5): `ι(W, ξ) ∈ Π₋` for `ξ ≥ 0`. -/
theorem s10_inj_h_mem (q : ℂ × ℝ) (hq : 0 ≤ q.2) :
    (!₂[q.1.re, q.1.im, -q.2, 0] : EuclideanSpace ℝ (Fin 4)) ∈
      {Z : EuclideanSpace ℝ (Fin 4) | Z 3 = 0 ∧ Z 2 ≤ 0} := by
  refine ⟨by simp, ?_⟩
  simp
  exact hq

/-- Helper for `thm_injective` (J5): near `Z₀ ∉ Π₋`, `ξ/|Z - ι(W, ξ)|² ≤ C ξ/(1 + |W|² + ξ²)`
for `ξ ≥ 0`. -/
theorem s10_inj_h_bound (Z₀ : EuclideanSpace ℝ (Fin 4)) (hZ₀ : ¬ (Z₀ 3 = 0 ∧ Z₀ 2 ≤ 0)) :
    ∃ C r : ℝ, 0 < r ∧ ∀ Z ∈ ball Z₀ r, ∀ q : ℂ × ℝ, 0 ≤ q.2 →
      0 < ‖Z - !₂[q.1.re, q.1.im, -q.2, 0]‖ ∧
      q.2 / ‖Z - !₂[q.1.re, q.1.im, -q.2, 0]‖ ^ 2 ≤ C * (q.2 / (1 + ‖q.1‖ ^ 2 + q.2 ^ 2)) := by
  have hne : ({Z : EuclideanSpace ℝ (Fin 4) | Z 3 = 0 ∧ Z 2 ≤ 0}).Nonempty := ⟨0, by simp⟩
  have hd := (s10_inj_h_closed.notMem_iff_infDist_pos hne).mp hZ₀
  obtain ⟨d, hdd⟩ : ∃ d, d = infDist Z₀ {Z : EuclideanSpace ℝ (Fin 4) | Z 3 = 0 ∧ Z 2 ≤ 0} :=
    ⟨_, rfl⟩
  rw [← hdd] at hd
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ‖Z₀‖ + d := ⟨_, rfl⟩
  refine ⟨2 + (1 + 2 * R ^ 2) * 4 / d ^ 2, d / 2, by positivity, fun Z hZ q hq => ?_⟩
  obtain ⟨y, hy⟩ : ∃ y : EuclideanSpace ℝ (Fin 4), y = !₂[q.1.re, q.1.im, -q.2, 0] := ⟨_, rfl⟩
  rw [← hy]
  have hyS := s10_inj_h_mem q hq
  rw [← hy] at hyS
  have hZ' : dist Z Z₀ < d / 2 := hZ
  have h1 : d ≤ dist Z₀ y := hdd ▸ infDist_le_dist_of_mem hyS
  have h2 : d / 2 ≤ ‖Z - y‖ := by
    rw [← dist_eq_norm]
    linarith [dist_triangle Z₀ Z y, dist_comm Z Z₀]
  have h3 : ‖y‖ ≤ ‖Z - y‖ + R := by
    have : ‖Z‖ ≤ ‖Z₀‖ + d := by
      have := norm_le_norm_add_norm_sub' Z Z₀
      rw [← dist_eq_norm] at this
      linarith
    have := norm_sub_norm_le y Z
    rw [norm_sub_rev] at this
    linarith
  have hny : ‖y‖ ^ 2 = ‖q.1‖ ^ 2 + q.2 ^ 2 := by rw [hy, s10_inj_g_niota]
  have hN : 0 < ‖Z - y‖ := by linarith
  refine ⟨hN, ?_⟩
  have hD : 0 < 1 + ‖q.1‖ ^ 2 + q.2 ^ 2 := by positivity
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hD]
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have key : 1 + ‖q.1‖ ^ 2 + q.2 ^ 2 ≤ (2 + (1 + 2 * R ^ 2) * 4 / d ^ 2) * ‖Z - y‖ ^ 2 := by
    have hDy : 1 + ‖q.1‖ ^ 2 + q.2 ^ 2 = 1 + ‖y‖ ^ 2 := by rw [hny]; ring
    rw [hDy]
    have e1 : ‖y‖ ^ 2 ≤ 2 * ‖Z - y‖ ^ 2 + 2 * R ^ 2 := by
      nlinarith [norm_nonneg y, sq_nonneg (‖Z - y‖ - R)]
    have e2 : 1 + 2 * R ^ 2 ≤ (1 + 2 * R ^ 2) * 4 / d ^ 2 * ‖Z - y‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : d ^ 2 ≤ 4 * ‖Z - y‖ ^ 2 := by nlinarith
      nlinarith [sq_nonneg R]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left key hq]

/-- Helper for `thm_injective` (J6): on `ℝ × ℝ³`, a `C¹` function on `U` vanishing on
`U ∩ {0} × ℝ³` has, after extension by zero off `H = {t > 0}`, the weak gradient `1_H ∇F` on `U`
(the divergence theorem on `H`, the boundary term vanishing). -/
theorem s10_inj_u_bridge {U : TopologicalSpace.Opens (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 3)))}
    {F : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 3)) → ℝ} (hF : ContDiffOn ℝ 1 F U)
    (h0 : ∀ x ∈ U, (WithLp.ofLp x).1 = 0 → F x = 0) :
    TauCeti.HasWeakFDerivOn volume U
      ((TauCeti.normalHalfSpace (E := EuclideanSpace ℝ (Fin 3)) 0 : Set _).indicator F)
      fun x => innerSL ℝ
        ((TauCeti.normalHalfSpace (E := EuclideanSpace ℝ (Fin 3)) 0 : Set _).indicator
          (gradient F) x) := by
  set H := (TauCeti.normalHalfSpace (E := EuclideanSpace ℝ (Fin 3)) 0 :
    Set (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 3)))) with hHdef
  have hHm : MeasurableSet H := (TauCeti.normalHalfSpace 0).isOpen.measurableSet
  refine TauCeti.hasWeakFDerivOn_iff.2 fun v => ?_
  have hcF : ContinuousOn F U := hF.continuousOn
  have hcD : ContinuousOn (fun x => fderiv ℝ F x v) U :=
    (hF.continuousOn_fderiv_of_isOpen U.isOpen le_rfl).clm_apply continuousOn_const
  have hG : (fun x => innerSL ℝ (H.indicator (gradient F) x) v) =
      H.indicator (fun x => fderiv ℝ F x v) := by
    funext x
    by_cases hx : x ∈ H
    · rw [indicator_of_mem hx, indicator_of_mem hx, innerSL_apply_apply, ← toDual_gradient,
        InnerProductSpace.toDual_apply_apply]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
      simp
  rw [hG]
  have hli : ∀ g : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 3)) → ℝ, ContinuousOn g U →
      LocallyIntegrableOn (H.indicator g) U volume := by
    intro g hg
    refine (locallyIntegrableOn_iff U.isOpen.isLocallyClosed).2 fun k hk hkc => ?_
    exact ((hg.mono hk).integrableOn_compact hkc).indicator hHm
  refine (TauCeti.hasWeakLineDerivOn_iff (hli F hcF) (hli _ hcD)).2 fun φ hφ hφc hφU => ?_
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hφd : Differentiable ℝ φ := hφ1.differentiable one_ne_zero
  have e1 : (fun x => lineDeriv ℝ φ x v • H.indicator F x) =
      H.indicator (fun x => fderiv ℝ φ x v * F x) := by
    funext x
    rw [(hφd x).lineDeriv_eq_fderiv, smul_eq_mul]
    by_cases hx : x ∈ H
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
  have e2 : (fun x => φ x • H.indicator (fun x => fderiv ℝ F x v) x) =
      H.indicator (fun x => φ x * fderiv ℝ F x v) := by
    funext x
    rw [smul_eq_mul]
    by_cases hx : x ∈ H
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
  rw [e1, e2, integral_indicator hHm, integral_indicator hHm]
  -- the product `g = φ F` is a compactly supported `C¹` function on the whole space
  have hφ0 : ∀ x, x ∉ U → x ∉ tsupport φ := fun x hx h => hx (hφU h)
  have hg : ContDiff ℝ 1 (fun x => φ x * F x) := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ U
    · exact (hφ1.contDiffAt).mul (hF.contDiffAt (U.isOpen.mem_nhds hx))
    · have he : (fun x => φ x * F x) =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
        ((notMem_tsupport_iff_eventuallyEq.1 (hφ0 x hx)).mono fun y hy => by
          show φ y * F y = 0
          rw [show φ y = 0 from hy, zero_mul])
      exact contDiffAt_const.congr_of_eventuallyEq he
  have hgc : HasCompactSupport (fun x => φ x * F x) := hφc.mul_right
  have hdiv := TauCeti.setIntegral_normalHalfSpace_fderiv_apply hg hgc 0 v
  have hbd : ∀ y : EuclideanSpace ℝ (Fin 3), φ (WithLp.toLp 2 (0, y)) * F (WithLp.toLp 2 (0, y)) = 0 := by
    intro y
    by_cases hy : WithLp.toLp 2 ((0 : ℝ), y) ∈ U
    · rw [h0 _ hy (by simp), mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport (hφ0 _ hy), zero_mul]
  simp only [hbd, integral_zero, mul_zero, neg_zero] at hdiv
  have hfd : ∀ x, fderiv ℝ (fun x => φ x * F x) x v =
      fderiv ℝ φ x v * F x + φ x * fderiv ℝ F x v := by
    intro x
    by_cases hx : x ∈ U
    · have hd : HasFDerivAt (fun x => φ x * F x) _ x := (hφd x).hasFDerivAt.mul
        ((hF.differentiableOn one_ne_zero).differentiableAt (U.isOpen.mem_nhds hx)).hasFDerivAt
      rw [hd.fderiv]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    · have hxg : x ∉ tsupport (fun x => φ x * F x) := fun h => hφ0 x hx
        (tsupport_mul_subset_left h)
      rw [fderiv_of_notMem_tsupport ℝ hxg, fderiv_of_notMem_tsupport ℝ (hφ0 x hx),
        image_eq_zero_of_notMem_tsupport (hφ0 x hx)]
      simp
  simp only [hfd] at hdiv
  have hK : IsCompact (tsupport φ) := hφc.isCompact
  have I1 : Integrable (fun x => fderiv ℝ φ x v * F x) := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport φ) ?_ fun x hx => ?_
    · exact ContinuousOn.integrableOn_compact hK
        (((hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn.mul
          (hcF.mono hφU))
    · rw [fderiv_of_notMem_tsupport ℝ hx]
      simp
  have I2 : Integrable (fun x => φ x * fderiv ℝ F x v) := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport φ) ?_ fun x hx => ?_
    · exact ContinuousOn.integrableOn_compact hK (hφ.continuous.continuousOn.mul (hcD.mono hφU))
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  rw [integral_add I1.integrableOn I2.integrableOn] at hdiv
  linarith

/-- Helper for `thm_injective` (J6, Schwarz reflection): on `ℝ × ℝ³`, a function harmonic on a
reflection-invariant connected open `U` meeting `{t > 0}`, even under `t ↦ -t` and vanishing on
`U ∩ {t = 0}`, vanishes on `U`. -/
theorem s10_inj_u_core {U : TopologicalSpace.Opens (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 3)))}
    {F : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 3)) → ℝ} (hF : InnerProductSpace.HarmonicOnNhd F U)
    (hU : MapsTo (TauCeti.normalReflection (EuclideanSpace ℝ (Fin 3)) 0) U U)
    (hUc : IsPreconnected (U : Set (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 3)))))
    (hne : ((U : Set (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 3)))) ∩
      TauCeti.normalHalfSpace (E := EuclideanSpace ℝ (Fin 3)) 0).Nonempty)
    (heven : ∀ x ∈ U, F (TauCeti.normalReflection (EuclideanSpace ℝ (Fin 3)) 0 x) = F x)
    (h0 : ∀ x ∈ U, (WithLp.ofLp x).1 = 0 → F x = 0) :
    ∀ x ∈ U, F x = 0 := by
  set H := TauCeti.normalHalfSpace (E := EuclideanSpace ℝ (Fin 3)) 0 with hHdef
  have hbr := s10_inj_u_bridge (hF.contDiffOn.of_le one_le_two) h0
  have hUH : ((U ⊓ H : TopologicalSpace.Opens _) : Set (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 3)))) =
      (U : Set _) ∩ H := TopologicalSpace.Opens.coe_inf U H
  have hharm : TauCeti.WeaklyHarmonicOn volume (U ⊓ H) ((H : Set _).indicator F) := by
    refine (InnerProductSpace.HarmonicOnNhd.weaklyHarmonicOn
      (hF.mono (fun x hx => by rw [hUH] at hx; exact hx.1))).congr_ae ?_
    refine (ae_restrict_iff' (U ⊓ H).isOpen.measurableSet).2 (Eventually.of_forall fun x hx => ?_)
    rw [hUH] at hx
    exact (indicator_of_mem hx.2 F).symm
  obtain ⟨h, hh, hodd, hwh, -⟩ := hharm.exists_harmonicOnNhd_ae_eq_of_inf_normalHalfSpace hU hbr
    (Eventually.of_forall fun x hx => indicator_of_notMem hx _)
    (Eventually.of_forall fun x hx => indicator_of_notMem hx _)
  have hwF : (H : Set _).indicator F =ᵐ[volume.restrict (U ⊓ H : TopologicalSpace.Opens _)] F :=
    (ae_restrict_iff' (U ⊓ H).isOpen.measurableSet).2 (Eventually.of_forall fun x hx => by
      rw [hUH] at hx
      exact indicator_of_mem hx.2 F)
  have hFh : EqOn F h ((U ⊓ H : TopologicalSpace.Opens _) : Set _) :=
    Measure.eqOn_open_of_ae_eq (hwF.symm.trans hwh) (U ⊓ H).isOpen
      (hF.continuousOn.mono (fun x hx => by rw [hUH] at hx; exact hx.1))
      (hh.continuousOn.mono (fun x hx => by rw [hUH] at hx; exact hx.1))
  obtain ⟨x₀, hx₀⟩ := hne
  have hx₀' : x₀ ∈ ((U ⊓ H : TopologicalSpace.Opens _) : Set _) := by rw [hUH]; exact hx₀
  have hev : F =ᶠ[𝓝 x₀] h := Filter.eventually_of_mem ((U ⊓ H).isOpen.mem_nhds hx₀') hFh
  have hall : EqOn F h U :=
    hF.analyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hh.analyticOnNhd hUc hx₀.1 hev
  intro x hx
  have e1 := heven x hx
  rw [hall (hU hx), hodd x hx, ← hall hx] at e1
  linarith

/-- Helper for `thm_injective` (J6): `ℝ⁴ ∖ Π₋` is preconnected (the union of the half-spaces
`{Z₂ > 0}`, `{Z₃ > 0}` and `{Z₃ < 0}`). -/
theorem s10_inj_u_conn : IsPreconnected {Z : EuclideanSpace ℝ (Fin 4) | ¬ (Z 3 = 0 ∧ Z 2 ≤ 0)} := by
  have hl : ∀ i : Fin 4, IsLinearMap ℝ fun Z : EuclideanSpace ℝ (Fin 4) => Z i :=
    fun i => ⟨fun x y => by simp, fun c x => by simp⟩
  have hA := (convex_halfSpace_gt (hl 2) 0).isPreconnected
  have hB := (convex_halfSpace_gt (hl 3) 0).isPreconnected
  have hC := (convex_halfSpace_lt (hl 3) 0).isPreconnected
  have hAB := hA.union !₂[0, 0, 1, 1] (by simp) (by simp) hB
  have hABC := hAB.union !₂[0, 0, 1, -1] (Or.inl (by simp)) (by simp) hC
  convert hABC using 1
  refine Set.ext fun Z => ⟨fun h => ?_, fun h => ?_⟩
  · rcases lt_trichotomy (Z 3) 0 with h3 | h3 | h3
    · exact Or.inr h3
    · exact Or.inl (Or.inl (lt_of_not_ge fun h2 => h ⟨h3, h2⟩))
    · exact Or.inl (Or.inr h3)
  · rintro ⟨h3, h2⟩
    rcases h with (h | h) | h
    · exact absurd h (not_lt.2 h2)
    · exact absurd (show 0 < Z 3 from h) (by rw [h3]; exact lt_irrefl 0)
    · exact absurd (show Z 3 < 0 from h) (by rw [h3]; exact lt_irrefl 0)

/-- Helper for `thm_injective` (J6): the isometry `ℝ × ℝ³ ≅ ℝ⁴`, `(t, y) ↦ (y₀, y₁, y₂, t)`. -/
theorem s10_inj_u_iso :
    ∃ e : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 3)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4),
      ∀ x, e x = !₂[(WithLp.ofLp x).2 0, (WithLp.ofLp x).2 1, (WithLp.ofLp x).2 2,
        (WithLp.ofLp x).1] := by
  let A : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 3)) →ₗ[ℝ] EuclideanSpace ℝ (Fin 4) :=
    { toFun := fun x => !₂[(WithLp.ofLp x).2 0, (WithLp.ofLp x).2 1, (WithLp.ofLp x).2 2,
        (WithLp.ofLp x).1]
      map_add' := fun x y => by
        ext i
        fin_cases i <;> simp
      map_smul' := fun c x => by
        ext i
        fin_cases i <;> simp }
  have hA : ∀ x, ‖A x‖ = ‖x‖ := by
    intro x
    have h1 : ‖A x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [s10_inj_nsq, WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_eq,
        Real.sq_sqrt (by positivity), Fin.sum_univ_three]
      simp [A, Real.norm_eq_abs, sq_abs]
      ring
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
  let L : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 3)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) := ⟨A, hA⟩
  have hs : Function.Surjective L := fun Z =>
    ⟨WithLp.toLp 2 (Z 3, !₂[Z 0, Z 1, Z 2]), by
      ext i
      fin_cases i <;> simp [L, A]⟩
  exact ⟨LinearIsometryEquiv.ofSurjective L hs, fun x => rfl⟩

/-- Helper for `thm_injective` (J4, Step 4): `∫ 𝒰 Δφ dZ = -4π² ∫ φ(ι(W, ξ)) ξ dμ` for `φ ∈ C²_c(ℝ⁴)`
(Fubini by `s10_inj_loc`, and `-Δ(|Z|⁻²/(4π²)) = δ₀` [GT (2.12), (2.17)]). -/
theorem s10_inj_green (μ : Measure (ℂ × ℝ)) (hμ : μ UHSᶜ = 0)
    (hm : ∫⁻ q, ENNReal.ofReal (q.2 / (1 + ‖q.1‖ ^ 2 + q.2 ^ 2)) ∂μ < ⊤)
    (U : EuclideanSpace ℝ (Fin 4) → ℝ≥0∞)
    (hU : ∀ Z, U Z = ∫⁻ q, ENNReal.ofReal (q.2 / ‖Z - !₂[q.1.re, q.1.im, -q.2, 0]‖ ^ 2) ∂μ)
    (φ : EuclideanSpace ℝ (Fin 4) → ℝ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    ∫ Z, Laplacian.laplacian φ Z * (U Z).toReal =
      -(4 * π ^ 2) * ∫ q, φ !₂[q.1.re, q.1.im, -q.2, 0] * q.2 ∂μ := by
  have hD : ∀ q : ℂ × ℝ, 0 < 1 + ‖q.1‖ ^ 2 + q.2 ^ 2 := fun q => by positivity
  -- the finite measure `ν = ξ/(1 + |q|²) μ`
  have hwm : Measurable fun q : ℂ × ℝ => ENNReal.ofReal (q.2 / (1 + ‖q.1‖ ^ 2 + q.2 ^ 2)) :=
    ENNReal.measurable_ofReal.comp (measurable_snd.div (Continuous.measurable (by fun_prop)))
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (ℂ × ℝ), ν = μ.withDensity fun q =>
      ENNReal.ofReal (q.2 / (1 + ‖q.1‖ ^ 2 + q.2 ^ 2)) := ⟨_, rfl⟩
  have hνf : IsFiniteMeasure ν := by
    rw [hν]
    exact isFiniteMeasure_withDensity hm.ne
  have hkm : Measurable fun p : EuclideanSpace ℝ (Fin 4) × (ℂ × ℝ) =>
      (1 + ‖p.2.1‖ ^ 2 + p.2.2 ^ 2) / ‖p.1 - !₂[p.2.1.re, p.2.1.im, -p.2.2, 0]‖ ^ 2 :=
    (Continuous.measurable (by fun_prop)).div (Continuous.measurable (by fun_prop))
  have hkm' : ∀ Z : EuclideanSpace ℝ (Fin 4), Measurable fun q : ℂ × ℝ =>
      (1 + ‖q.1‖ ^ 2 + q.2 ^ 2) / ‖Z - !₂[q.1.re, q.1.im, -q.2, 0]‖ ^ 2 :=
    fun Z => (Continuous.measurable (by fun_prop)).div (Continuous.measurable (by fun_prop))
  -- (a) `𝒰` against `ν`
  have hUν : ∀ Z, U Z = ∫⁻ q, ENNReal.ofReal
      ((1 + ‖q.1‖ ^ 2 + q.2 ^ 2) / ‖Z - !₂[q.1.re, q.1.im, -q.2, 0]‖ ^ 2) ∂ν := by
    intro Z
    rw [hU, hν, lintegral_withDensity_eq_lintegral_mul _ hwm (hkm' Z).ennreal_ofReal]
    refine lintegral_congr fun q => ?_
    exact (s10_inj_g_ofReal (hD q) (sq_nonneg _)).symm
  -- (b) the right side against `ν`
  have hR : ∫ q, φ !₂[q.1.re, q.1.im, -q.2, 0] * (1 + ‖q.1‖ ^ 2 + q.2 ^ 2) ∂ν =
      ∫ q, φ !₂[q.1.re, q.1.im, -q.2, 0] * q.2 ∂μ := by
    rw [hν, integral_withDensity_eq_integral_toReal_smul hwm
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae ((s10_inj_ae μ hμ).mono fun q hq => ?_)
    have hq' : 0 < q.2 := hq
    dsimp only
    rw [ENNReal.toReal_ofReal (div_nonneg hq'.le (hD q).le), smul_eq_mul]
    field_simp
  -- (c) bounds: `supp Δφ ⊆ B(0, ρ)` and `|Δφ| ≤ M`
  have hΔc : Continuous (Laplacian.laplacian φ) := hφ.continuous_laplacian
  have hts : tsupport (Laplacian.laplacian φ) ⊆ tsupport φ := TauCeti.tsupport_laplacian_subset φ
  obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_ball (0 : EuclideanSpace ℝ (Fin 4))
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = max r 1 := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by
    rw [hρ]
    exact lt_max_of_lt_right one_pos
  have hrρ : r ≤ ρ := by
    rw [hρ]
    exact le_max_left _ _
  have hsub : tsupport (Laplacian.laplacian φ) ⊆ ball 0 ρ :=
    hts.trans (hr.trans (ball_subset_ball hrρ))
  obtain ⟨M, hM⟩ := hΔc.bounded_above_of_compact_support
    (hc.mono' ((subset_tsupport _).trans hts))
  obtain ⟨C, hC⟩ := s10_inj_loc ρ hρ0
  -- (d) integrability on `volume × ν`
  have hFm : Measurable fun p : EuclideanSpace ℝ (Fin 4) × (ℂ × ℝ) =>
      Laplacian.laplacian φ p.1 *
        ((1 + ‖p.2.1‖ ^ 2 + p.2.2 ^ 2) / ‖p.1 - !₂[p.2.1.re, p.2.1.im, -p.2.2, 0]‖ ^ 2) :=
    (hΔc.measurable.comp measurable_fst).mul hkm
  have hinner : ∀ q : ℂ × ℝ, ∫⁻ Z, ‖Laplacian.laplacian φ Z *
      ((1 + ‖q.1‖ ^ 2 + q.2 ^ 2) / ‖Z - !₂[q.1.re, q.1.im, -q.2, 0]‖ ^ 2)‖ₑ ≤
        ENNReal.ofReal (max M 0) * C := by
    intro q
    obtain ⟨y, hy⟩ : ∃ y : EuclideanSpace ℝ (Fin 4), y = !₂[q.1.re, q.1.im, -q.2, 0] := ⟨_, rfl⟩
    have hDy : 1 + ‖q.1‖ ^ 2 + q.2 ^ 2 = 1 + ‖y‖ ^ 2 := by rw [hy, s10_inj_g_niota]; ring
    rw [← hy, hDy]
    have hy0 : (1 + ‖y‖ ^ 2) ≠ 0 := by positivity
    calc ∫⁻ Z, ‖Laplacian.laplacian φ Z * ((1 + ‖y‖ ^ 2) / ‖Z - y‖ ^ 2)‖ₑ
        ≤ ∫⁻ Z, (ball (0 : EuclideanSpace ℝ (Fin 4)) ρ).indicator (fun Z =>
            ENNReal.ofReal (max M 0) * ENNReal.ofReal (1 + ‖y‖ ^ 2) *
              ENNReal.ofReal ((‖Z - y‖ ^ 2)⁻¹)) Z := by
          refine lintegral_mono fun Z => ?_
          by_cases hZ : Z ∈ ball (0 : EuclideanSpace ℝ (Fin 4)) ρ
          · rw [indicator_of_mem hZ, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul
              (le_max_right _ _), ← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + ‖y‖ ^ 2) / ‖Z - y‖ ^ 2),
              div_eq_mul_inv, ← mul_assoc]
            have h1 : |Laplacian.laplacian φ Z| ≤ max M 0 := by
              have h2 := hM Z
              rw [Real.norm_eq_abs] at h2
              exact h2.trans (le_max_left _ _)
            gcongr
          · rw [indicator_of_notMem hZ, image_eq_zero_of_notMem_tsupport (fun h => hZ (hsub h)),
              zero_mul, enorm_zero]
      _ = ENNReal.ofReal (max M 0) * ENNReal.ofReal (1 + ‖y‖ ^ 2) *
            ∫⁻ Z in ball 0 ρ, ENNReal.ofReal ((‖Z - y‖ ^ 2)⁻¹) := by
          rw [lintegral_indicator measurableSet_ball, lintegral_const_mul']
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (max M 0) * ENNReal.ofReal (1 + ‖y‖ ^ 2) *
            ((C : ℝ≥0∞) * ENNReal.ofReal ((1 + ‖y‖ ^ 2)⁻¹)) := by
          gcongr
          exact hC y
      _ = ENNReal.ofReal (max M 0) * C := by
          rw [mul_comm (C : ℝ≥0∞), ← mul_assoc, mul_assoc (ENNReal.ofReal (max M 0)),
            ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ hy0,
            ENNReal.ofReal_one, mul_one]
  have hF : Integrable (Function.uncurry fun (Z : EuclideanSpace ℝ (Fin 4)) (q : ℂ × ℝ) =>
      Laplacian.laplacian φ Z *
        ((1 + ‖q.1‖ ^ 2 + q.2 ^ 2) / ‖Z - !₂[q.1.re, q.1.im, -q.2, 0]‖ ^ 2)) (volume.prod ν) := by
    refine ⟨hFm.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr ?_⟩
    calc ∫⁻ p, ‖Function.uncurry (fun (Z : EuclideanSpace ℝ (Fin 4)) (q : ℂ × ℝ) =>
          Laplacian.laplacian φ Z *
            ((1 + ‖q.1‖ ^ 2 + q.2 ^ 2) / ‖Z - !₂[q.1.re, q.1.im, -q.2, 0]‖ ^ 2)) p‖ₑ
            ∂(volume.prod ν)
        = ∫⁻ q, ∫⁻ Z, ‖Laplacian.laplacian φ Z *
          ((1 + ‖q.1‖ ^ 2 + q.2 ^ 2) / ‖Z - !₂[q.1.re, q.1.im, -q.2, 0]‖ ^ 2)‖ₑ ∂volume ∂ν :=
          lintegral_prod_symm _ hFm.enorm.aemeasurable
      _ ≤ ∫⁻ _, ENNReal.ofReal (max M 0) * C ∂ν := lintegral_mono hinner
      _ < ⊤ := by
          rw [lintegral_const]
          exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top)
            (measure_lt_top _ _)
  -- (e) assembly
  calc ∫ Z, Laplacian.laplacian φ Z * (U Z).toReal
      = ∫ Z, ∫ q, Laplacian.laplacian φ Z *
          ((1 + ‖q.1‖ ^ 2 + q.2 ^ 2) / ‖Z - !₂[q.1.re, q.1.im, -q.2, 0]‖ ^ 2) ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun Z => ?_)
        dsimp only
        rw [hUν Z, ← integral_eq_lintegral_of_nonneg_ae
          (Eventually.of_forall fun q => by positivity) (hkm' Z).aestronglyMeasurable,
          integral_const_mul]
    _ = ∫ q, ∫ Z, Laplacian.laplacian φ Z *
          ((1 + ‖q.1‖ ^ 2 + q.2 ^ 2) / ‖Z - !₂[q.1.re, q.1.im, -q.2, 0]‖ ^ 2) ∂volume ∂ν :=
        integral_integral_swap hF
    _ = ∫ q, -(4 * π ^ 2) * (φ !₂[q.1.re, q.1.im, -q.2, 0] * (1 + ‖q.1‖ ^ 2 + q.2 ^ 2)) ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun q => ?_)
        dsimp only
        calc ∫ Z, Laplacian.laplacian φ Z *
              ((1 + ‖q.1‖ ^ 2 + q.2 ^ 2) / ‖Z - !₂[q.1.re, q.1.im, -q.2, 0]‖ ^ 2)
            = ∫ Z, (1 + ‖q.1‖ ^ 2 + q.2 ^ 2) * (Laplacian.laplacian φ Z *
                (‖Z - !₂[q.1.re, q.1.im, -q.2, 0]‖ ^ 2)⁻¹) := by
              refine integral_congr_ae (Eventually.of_forall fun Z => ?_)
              dsimp only
              rw [div_eq_mul_inv]
              ring
          _ = _ := by
              rw [integral_const_mul, s10_inj_g_pole φ hφ hc]
              ring
    _ = -(4 * π ^ 2) * ∫ q, φ !₂[q.1.re, q.1.im, -q.2, 0] * q.2 ∂μ := by
        rw [integral_const_mul, hR]

/-- Helper for `thm_injective` (J5, Step 2(i)): `𝒰` is harmonic on `ℝ⁴ ∖ Π₋`,
`Π₋ = {(W, t, 0) : t ≤ 0}` (continuity by dominated convergence, weak harmonicity by
`s10_inj_green`, and Weyl's lemma). -/
theorem s10_inj_harm (μ : Measure (ℂ × ℝ)) (hμ : μ UHSᶜ = 0)
    (hm : ∫⁻ q, ENNReal.ofReal (q.2 / (1 + ‖q.1‖ ^ 2 + q.2 ^ 2)) ∂μ < ⊤)
    (U : EuclideanSpace ℝ (Fin 4) → ℝ≥0∞)
    (hU : ∀ Z, U Z = ∫⁻ q, ENNReal.ofReal (q.2 / ‖Z - !₂[q.1.re, q.1.im, -q.2, 0]‖ ^ 2) ∂μ) :
    InnerProductSpace.HarmonicOnNhd (fun Z => (U Z).toReal) {Z | ¬ (Z 3 = 0 ∧ Z 2 ≤ 0)} := by
  have hkm : ∀ Z : EuclideanSpace ℝ (Fin 4), Measurable fun q : ℂ × ℝ =>
      q.2 / ‖Z - !₂[q.1.re, q.1.im, -q.2, 0]‖ ^ 2 :=
    fun Z => measurable_snd.div (Continuous.measurable (by fun_prop))
  have hk : (fun Z => (U Z).toReal) =
      fun Z => ∫ q, q.2 / ‖Z - !₂[q.1.re, q.1.im, -q.2, 0]‖ ^ 2 ∂μ := by
    funext Z
    rw [hU, integral_eq_lintegral_of_nonneg_ae ((s10_inj_ae μ hμ).mono fun q hq =>
      div_nonneg (le_of_lt hq) (sq_nonneg _)) (hkm Z).aestronglyMeasurable]
  have hwi : Integrable (fun q : ℂ × ℝ => q.2 / (1 + ‖q.1‖ ^ 2 + q.2 ^ 2)) μ :=
    ⟨(measurable_snd.div (Continuous.measurable (by fun_prop))).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal ((s10_inj_ae μ hμ).mono fun q hq =>
        div_nonneg (le_of_lt hq) (by positivity))).mpr hm⟩
  -- continuity off `Π₋`
  have hcont : ContinuousOn (fun Z => (U Z).toReal) {Z | ¬ (Z 3 = 0 ∧ Z 2 ≤ 0)} := by
    intro Z₀ hZ₀
    refine ContinuousAt.continuousWithinAt ?_
    rw [hk]
    obtain ⟨C, r, hr, hb⟩ := s10_inj_h_bound Z₀ hZ₀
    refine continuousAt_of_dominated (bound := fun q => C * (q.2 / (1 + ‖q.1‖ ^ 2 + q.2 ^ 2)))
      (Eventually.of_forall fun Z => (hkm Z).aestronglyMeasurable) ?_ (hwi.const_mul C) ?_
    · filter_upwards [ball_mem_nhds Z₀ hr] with Z hZ
      filter_upwards [s10_inj_ae μ hμ] with q hq
      have hq' : 0 < q.2 := hq
      rw [Real.norm_of_nonneg (div_nonneg hq'.le (sq_nonneg _))]
      exact (hb Z hZ q hq'.le).2
    · filter_upwards [s10_inj_ae μ hμ] with q hq
      have hq' : 0 < q.2 := hq
      have hN := (hb Z₀ (mem_ball_self hr) q hq'.le).1
      exact continuousAt_const.div (by fun_prop) (pow_ne_zero 2 hN.ne')
  -- weak harmonicity and Weyl's lemma
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 4)),
      (Ω : Set (EuclideanSpace ℝ (Fin 4))) = {Z | ¬ (Z 3 = 0 ∧ Z 2 ≤ 0)} :=
    ⟨⟨_, s10_inj_h_closed.isOpen_compl⟩, rfl⟩
  rw [← hΩ] at hcont ⊢
  refine (TauCeti.harmonicOnNhd_iff_weaklyHarmonicOn (μ := volume) hcont).mpr
    (TauCeti.weaklyHarmonicOn_iff.mpr ⟨hcont.locallyIntegrableOn Ω.isOpen.measurableSet,
      fun φ => ?_⟩)
  simp only [smul_eq_mul]
  rw [s10_inj_green μ hμ hm U hU φ (φ.contDiff.of_le (WithTop.coe_le_coe.mpr le_top)) φ.hasCompactSupport]
  have h0 : ∫ q, φ !₂[q.1.re, q.1.im, -q.2, 0] * q.2 ∂μ = 0 := by
    refine integral_eq_zero_of_ae ((s10_inj_ae μ hμ).mono fun q hq => ?_)
    have hq' : 0 < q.2 := hq
    have hn : (!₂[q.1.re, q.1.im, -q.2, 0] : EuclideanSpace ℝ (Fin 4)) ∉
        (Ω : Set (EuclideanSpace ℝ (Fin 4))) := by
      rw [hΩ]
      exact fun h => h (s10_inj_h_mem q hq'.le)
    show φ !₂[q.1.re, q.1.im, -q.2, 0] * q.2 = 0
    rw [image_eq_zero_of_notMem_tsupport (fun h => hn (φ.tsupport_subset h)), zero_mul]
  rw [h0, mul_zero]

/-- Helper for `thm_injective` (Step 3): `𝒰` is even in the last coordinate `a`. -/
theorem s10_inj_even (μ : Measure (ℂ × ℝ)) (U : EuclideanSpace ℝ (Fin 4) → ℝ≥0∞)
    (hU : ∀ Z, U Z = ∫⁻ q, ENNReal.ofReal (q.2 / ‖Z - !₂[q.1.re, q.1.im, -q.2, 0]‖ ^ 2) ∂μ)
    (Z : EuclideanSpace ℝ (Fin 4)) : U !₂[Z 0, Z 1, Z 2, -Z 3] = U Z := by
  rw [hU, hU]
  refine lintegral_congr fun q => ?_
  rw [s10_inj_nsq, s10_inj_nsq]
  simp

/-- Helper for `thm_injective` (J6, Step 3, unique continuation): a function harmonic on
`ℝ⁴ ∖ Π₋`, even in `a`, and vanishing on `O × {0}` for a nonempty open `O ⊆ ℍ³`, vanishes on
`ℝ⁴ ∖ Π₋` (Schwarz reflection, real-analyticity [GT §2.4], connectedness of `ℝ⁴ ∖ Π₋`). -/
theorem s10_inj_uc (f : EuclideanSpace ℝ (Fin 4) → ℝ)
    (hf : InnerProductSpace.HarmonicOnNhd f {Z | ¬ (Z 3 = 0 ∧ Z 2 ≤ 0)})
    (heven : ∀ Z, f !₂[Z 0, Z 1, Z 2, -Z 3] = f Z) (O : Set (ℂ × ℝ)) (hO : IsOpen O)
    (hOne : O.Nonempty) (hOU : O ⊆ UHS) (h0 : ∀ P ∈ O, f !₂[P.1.re, P.1.im, P.2, 0] = 0) :
    ∀ Z, ¬ (Z 3 = 0 ∧ Z 2 ≤ 0) → f Z = 0 := by
  obtain ⟨P₁, hP₁⟩ := hOne
  have hP2 : 0 < P₁.2 := hOU hP₁
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hO P₁ hP₁
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = min ε P₁.2 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := hδ ▸ lt_min hε hP2
  have hδε : δ ≤ ε := hδ ▸ min_le_left _ _
  have hδP : δ ≤ P₁.2 := hδ ▸ min_le_right _ _
  obtain ⟨e, he⟩ := s10_inj_u_iso
  obtain ⟨c, hc⟩ : ∃ c : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 3)),
      c = WithLp.toLp 2 (0, !₂[P₁.1.re, P₁.1.im, P₁.2]) := ⟨_, rfl⟩
  have he0 : ∀ x, e x 0 = (WithLp.ofLp x).2 0 := fun x => by rw [he]; simp
  have he1 : ∀ x, e x 1 = (WithLp.ofLp x).2 1 := fun x => by rw [he]; simp
  have he2 : ∀ x, e x 2 = (WithLp.ofLp x).2 2 := fun x => by rw [he]; simp
  have he3 : ∀ x, e x 3 = (WithLp.ofLp x).1 := fun x => by rw [he]; simp
  have hd2 : ∀ x, dist x c ^ 2 = (e x 0 - P₁.1.re) ^ 2 + (e x 1 - P₁.1.im) ^ 2 +
      (e x 2 - P₁.2) ^ 2 + e x 3 ^ 2 := by
    intro x
    rw [← e.dist_map, dist_eq_norm, s10_inj_nsq]
    simp only [PiLp.sub_apply]
    rw [he0 c, he1 c, he2 c, he3 c, hc]
    simp
  have hUΩ : ∀ x ∈ ball c δ, e x ∈ {Z : EuclideanSpace ℝ (Fin 4) | ¬ (Z 3 = 0 ∧ Z 2 ≤ 0)} := by
    intro x hx h
    have h1 := hd2 x
    have h2 : dist x c < δ := hx
    have h3 : dist x c ^ 2 < δ ^ 2 := pow_lt_pow_left₀ h2 dist_nonneg two_ne_zero
    nlinarith [h.2, sq_nonneg (e x 0 - P₁.1.re), sq_nonneg (e x 1 - P₁.1.im), sq_nonneg (e x 3)]
  obtain ⟨U, hU⟩ : ∃ U : TopologicalSpace.Opens (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 3))),
      (U : Set _) = ball c δ := ⟨⟨_, isOpen_ball⟩, rfl⟩
  have hρ : ∀ x, TauCeti.normalReflection (EuclideanSpace ℝ (Fin 3)) 0 x =
      WithLp.toLp 2 (-(WithLp.ofLp x).1, (WithLp.ofLp x).2) := fun x => by
    rw [TauCeti.normalReflection_apply]
    simp
  have hρc : TauCeti.normalReflection (EuclideanSpace ℝ (Fin 3)) 0 c = c := by
    rw [hρ, hc]
    simp
  have hρm : MapsTo (TauCeti.normalReflection (EuclideanSpace ℝ (Fin 3)) 0) U U := by
    intro x hx
    rw [hU] at hx ⊢
    show dist _ c < δ
    rw [← hρc, AffineIsometryEquiv.dist_map]
    exact hx
  have hcore := s10_inj_u_core (U := U) (F := f ∘ e)
    (((TauCeti.harmonicOnNhd_comp_linearIsometryEquiv_right_iff e).2 hf).mono
      fun x hx => hUΩ x (hU ▸ hx))
    hρm (by rw [hU]; exact (convex_ball c δ).isPreconnected)
    ⟨WithLp.toLp 2 (δ / 2, (WithLp.ofLp c).2), by
      rw [hU]
      show dist _ c < δ
      refine lt_of_pow_lt_pow_left₀ 2 hδ0.le ?_
      rw [hd2, he0, he1, he2, he3, hc]
      simp
      nlinarith,
     (TauCeti.mem_normalHalfSpace 0 _).2 (by simp; positivity)⟩
    (fun x hx => by
      show f (e _) = f (e x)
      have h1 : e (TauCeti.normalReflection (EuclideanSpace ℝ (Fin 3)) 0 x) =
          !₂[e x 0, e x 1, e x 2, -e x 3] := by
        rw [he, hρ, he0, he1, he2, he3]
      rw [h1]
      exact heven (e x))
    (fun x hx hx1 => by
      show f (e x) = 0
      have hx' : x ∈ ball c δ := hU ▸ hx
      have h1 := hd2 x
      have h2 : dist x c ^ 2 < δ ^ 2 := pow_lt_pow_left₀ hx' dist_nonneg two_ne_zero
      have h3 : e x 3 = 0 := by rw [he3, hx1]
      have hPO : ((⟨e x 0, e x 1⟩ : ℂ), e x 2) ∈ O := by
        refine hεO ?_
        show dist _ _ < ε
        rw [Prod.dist_eq, max_lt_iff, Complex.dist_eq_re_im, Real.dist_eq]
        refine ⟨(Real.sqrt_lt' hε).2 ?_, abs_lt.2 ⟨?_, ?_⟩⟩
        · simp only
          nlinarith [sq_nonneg (e x 2 - P₁.2), sq_nonneg (e x 3)]
        · nlinarith [sq_nonneg (e x 0 - P₁.1.re), sq_nonneg (e x 1 - P₁.1.im), sq_nonneg (e x 3)]
        · nlinarith [sq_nonneg (e x 0 - P₁.1.re), sq_nonneg (e x 1 - P₁.1.im), sq_nonneg (e x 3)]
      have h4 := h0 _ hPO
      have h5 : (!₂[(⟨e x 0, e x 1⟩ : ℂ).re, (⟨e x 0, e x 1⟩ : ℂ).im, e x 2, 0] :
          EuclideanSpace ℝ (Fin 4)) = e x := by
        ext i
        fin_cases i <;> simp [h3]
      rw [h5] at h4
      exact h4)
  have hball : ∀ W ∈ ball (e c) δ, f W = 0 := by
    intro W hW
    have hx : e.symm W ∈ U := by
      show e.symm W ∈ (U : Set _)
      rw [hU]
      show dist (e.symm W) c < δ
      rw [← e.dist_map, e.apply_symm_apply]
      exact hW
    have h1 := hcore _ hx
    simpa using h1
  have hev : f =ᶠ[𝓝 (e c)] 0 := Filter.eventually_of_mem (ball_mem_nhds _ hδ0) hball
  exact fun Z hZ => hf.analyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero s10_inj_u_conn
    (hUΩ c (mem_ball_self hδ0)) hev hZ

/-- Helper for `thm_injective` (Step 4): the hyperplane `{a = 0}` of `ℝ⁴` is Lebesgue-null. -/
theorem s10_inj_null : volume {Z : EuclideanSpace ℝ (Fin 4) | Z 3 = 0} = 0 := by
  have hs : {Z : EuclideanSpace ℝ (Fin 4) | Z 3 = 0} =
      ↑(LinearMap.ker (EuclideanSpace.projₗ (𝕜 := ℝ) (3 : Fin 4))) := by
    ext Z
    simp
  rw [hs]
  refine Measure.addHaar_submodule volume _ fun htop => ?_
  have h1 : EuclideanSpace.single (3 : Fin 4) (1 : ℝ) ∈
      LinearMap.ker (EuclideanSpace.projₗ (𝕜 := ℝ) (3 : Fin 4)) := by
    rw [htop]
    exact Submodule.mem_top
  simp at h1

/-- Helper for `thm_injective` (J7): the lifted measure `ν = ι_*(ξ μ)` is locally finite
(`s10_inj_mass`). -/
theorem s10_inj_locfin (μ : Measure (ℂ × ℝ)) (hμ : μ UHSᶜ = 0)
    (hm : ∫⁻ q, ENNReal.ofReal (q.2 / (1 + ‖q.1‖ ^ 2 + q.2 ^ 2)) ∂μ < ⊤) :
    IsLocallyFiniteMeasure ((μ.withDensity fun q => ENNReal.ofReal q.2).map
      fun q : ℂ × ℝ => (!₂[q.1.re, q.1.im, -q.2, 0] : EuclideanSpace ℝ (Fin 4))) := by
  refine ⟨fun x => ⟨ball 0 (‖x‖ + 1), isOpen_ball.mem_nhds (by simp), ?_⟩⟩
  rw [Measure.map_apply s10_inj_cont.measurable measurableSet_ball,
    withDensity_apply _ (s10_inj_cont.measurable measurableSet_ball)]
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ‖x‖ + 1 := ⟨_, rfl⟩
  rw [← hR]
  calc ∫⁻ q in (fun q : ℂ × ℝ => (!₂[q.1.re, q.1.im, -q.2, 0] : EuclideanSpace ℝ (Fin 4))) ⁻¹'
        ball 0 R, ENNReal.ofReal q.2 ∂μ
      ≤ ∫⁻ q, ENNReal.ofReal (1 + R ^ 2) *
          ENNReal.ofReal (q.2 / (1 + ‖q.1‖ ^ 2 + q.2 ^ 2)) ∂μ := by
        rw [← lintegral_indicator (s10_inj_cont.measurable measurableSet_ball)]
        refine lintegral_mono_ae ((s10_inj_ae μ hμ).mono fun q hq => ?_)
        have hq' : 0 < q.2 := hq
        by_cases hb : q ∈ (fun q : ℂ × ℝ => (!₂[q.1.re, q.1.im, -q.2, 0] :
            EuclideanSpace ℝ (Fin 4))) ⁻¹' ball 0 R
        · rw [indicator_of_mem hb, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hb' : ‖(!₂[q.1.re, q.1.im, -q.2, 0] : EuclideanSpace ℝ (Fin 4))‖ < R := by
            simpa using hb
          have hn : ‖(!₂[q.1.re, q.1.im, -q.2, 0] : EuclideanSpace ℝ (Fin 4))‖ ^ 2 =
              ‖q.1‖ ^ 2 + q.2 ^ 2 := by
            rw [s10_inj_nsq, Complex.sq_norm, Complex.normSq_apply]
            simp
            ring
          have hR2 : ‖q.1‖ ^ 2 + q.2 ^ 2 ≤ R ^ 2 := by
            rw [← hn]
            exact pow_le_pow_left₀ (norm_nonneg _) hb'.le 2
          have hD : 0 < 1 + ‖q.1‖ ^ 2 + q.2 ^ 2 := by positivity
          rw [mul_div_assoc', le_div_iff₀ hD]
          nlinarith
        · rw [indicator_of_notMem hb]
          exact zero_le
    _ = ENNReal.ofReal (1 + R ^ 2) * ∫⁻ q, ENNReal.ofReal (q.2 / (1 + ‖q.1‖ ^ 2 + q.2 ^ 2)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hm

/-- Helper for `thm_injective` (J7): `∫ φ dν = ∫ φ(ι(W, ξ)) ξ dμ` for `φ ∈ C_c(ℝ⁴)`. -/
theorem s10_inj_integral (μ : Measure (ℂ × ℝ)) (hμ : μ UHSᶜ = 0)
    (hm : ∫⁻ q, ENNReal.ofReal (q.2 / (1 + ‖q.1‖ ^ 2 + q.2 ^ 2)) ∂μ < ⊤)
    (φ : EuclideanSpace ℝ (Fin 4) → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    ∫ Z, φ Z ∂((μ.withDensity fun q => ENNReal.ofReal q.2).map
        fun q : ℂ × ℝ => (!₂[q.1.re, q.1.im, -q.2, 0] : EuclideanSpace ℝ (Fin 4))) =
      ∫ q, φ !₂[q.1.re, q.1.im, -q.2, 0] * q.2 ∂μ := by
  -- the identity holds without the mass bound and the compact support (both sides are Bochner
  -- integrals of the same function, possibly both `0`)
  have _hm := hm
  have _hc := hc
  rw [integral_map s10_inj_cont.measurable.aemeasurable hφ.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ((s10_inj_ae μ hμ).mono fun q hq => ?_)
  have hq' : 0 < q.2 := hq
  dsimp only
  rw [ENNReal.toReal_ofReal hq'.le, smul_eq_mul, mul_comm]

/-- Helper for `thm_injective` (J7, Step 4): locally finite Borel measures on `ℝ⁴` with equal
integrals of every `φ ∈ C^∞_c(ℝ⁴)` are equal (mollification and Riesz uniqueness). -/
theorem s10_inj_ext (ν₁ ν₂ : Measure (EuclideanSpace ℝ (Fin 4))) [IsLocallyFiniteMeasure ν₁]
    [IsLocallyFiniteMeasure ν₂]
    (h : ∀ φ : EuclideanSpace ℝ (Fin 4) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ Z, φ Z ∂ν₁ = ∫ Z, φ Z ∂ν₂) :
    ν₁ = ν₂ := by
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
  have hfc : Continuous f := f.continuous
  have hfs : HasCompactSupport f := f.hasCompactSupport
  obtain ⟨M, hM⟩ := hfc.bounded_above_of_compact_support hfs
  -- mollifiers `F n = ρₙ ⋆ f`, `supp ρₙ = B(0, 1/(n+1))`
  have hφ : ∀ n : ℕ, 0 < 1 / (2 * ((n : ℝ) + 1)) ∧ 1 / (2 * ((n : ℝ) + 1)) < 1 / ((n : ℝ) + 1) :=
    fun n => ⟨by positivity, one_div_lt_one_div_of_lt (by positivity) (by linarith [n.cast_nonneg (α := ℝ)])⟩
  obtain ⟨φ, hφr⟩ : ∃ φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin 4)),
      ∀ n, (φ n).rOut = 1 / ((n : ℝ) + 1) :=
    ⟨fun n => ⟨_, _, (hφ n).1, (hφ n).2⟩, fun _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℕ → EuclideanSpace ℝ (Fin 4) → ℝ,
      F = fun n => convolution ((φ n).normed volume) (⇑f) (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    ⟨_, rfl⟩
  have hFc : ∀ n, ContDiff ℝ ∞ (F n) := fun n => by
    rw [hF]
    exact (φ n).hasCompactSupport_normed.contDiff_convolution_left _ (φ n).contDiff_normed
      hfc.locallyIntegrable
  obtain ⟨R, hR⟩ := hfs.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin 4))
  obtain ⟨K, hK⟩ : ∃ K : Set (EuclideanSpace ℝ (Fin 4)), K = closedBall 0 (R + 1) := ⟨_, rfl⟩
  have hKc : IsCompact K := by rw [hK]; exact isCompact_closedBall 0 _
  have hFs : ∀ n x, x ∉ K → F n x = 0 := by
    intro n x hx
    by_contra hne
    have hx' : x ∈ Function.support (F n) := hne
    rw [hF] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) hx'
    refine hx ?_
    rw [(φ n).support_normed_eq, hφr, mem_ball, dist_zero_right] at ha
    have hb' := hR (subset_tsupport _ hb)
    rw [mem_closedBall, dist_zero_right] at hb'
    have ha1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [n.cast_nonneg (α := ℝ)]
    rw [hK, mem_closedBall, dist_zero_right]
    linarith [norm_add_le a b]
  have hFcs : ∀ n, HasCompactSupport (F n) := fun n => HasCompactSupport.intro hKc (hFs n)
  have hFb : ∀ n x, ‖F n x‖ ≤ 3 * M := by
    intro n x
    have hd : dist (F n x) (f x) ≤ 2 * M := by
      rw [hF]
      exact (φ n).dist_normed_convolution_le hfc.aestronglyMeasurable fun x' _ =>
        (dist_le_norm_add_norm _ _).trans (by linarith [hM x', hM x])
    rw [dist_eq_norm] at hd
    linarith [norm_sub_norm_le (F n x) (f x), hM x]
  have hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
    intro x
    rw [hF]
    refine ContDiffBump.convolution_tendsto_right_of_continuous ?_ hfc x
    simp only [hφr]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- dominated convergence for each locally finite measure
  have hT : ∀ ν : Measure (EuclideanSpace ℝ (Fin 4)), IsLocallyFiniteMeasure ν →
      Tendsto (fun n => ∫ x, F n x ∂ν) atTop (𝓝 (∫ x, f x ∂ν)) := by
    intro ν _
    refine tendsto_integral_of_dominated_convergence (K.indicator fun _ => 3 * M)
      (fun n => (hFc n).continuous.aestronglyMeasurable) ?_ (fun n => ?_)
      (Eventually.of_forall hlim)
    · exact (integrableOn_const hKc.measure_lt_top.ne).integrable_indicator hKc.measurableSet
    · refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx]
        exact hFb n x
      · rw [indicator_of_notMem hx, hFs n x hx, norm_zero]
  have h1 := hT ν₁ inferInstance
  have hfun : (fun n => ∫ x, F n x ∂ν₁) = fun n => ∫ x, F n x ∂ν₂ :=
    funext fun n => h _ (hFc n) (hFcs n)
  rw [hfun] at h1
  exact tendsto_nhds_unique h1 (hT ν₂ inferInstance)

/-- Helper for `thm_injective` (J7, the pull-back): `ι` is a closed embedding and `ξ > 0` on
`ℍ³`, so `ι_*(ξ μ⁺) = ι_*(ξ μ⁻)` gives `μ⁺ = μ⁻`. -/
theorem s10_inj_pullback (μp μm : Measure (ℂ × ℝ)) (hp : μp UHSᶜ = 0) (hm : μm UHSᶜ = 0)
    (h : (μp.withDensity fun q => ENNReal.ofReal q.2).map
        (fun q : ℂ × ℝ => (!₂[q.1.re, q.1.im, -q.2, 0] : EuclideanSpace ℝ (Fin 4))) =
      (μm.withDensity fun q => ENNReal.ofReal q.2).map
        fun q : ℂ × ℝ => (!₂[q.1.re, q.1.im, -q.2, 0] : EuclideanSpace ℝ (Fin 4))) :
    μp = μm := by
  obtain ⟨hgc, hgι⟩ := s10_inj_linv
  -- `ι` has a measurable left inverse, so `ξ μ⁺ = ξ μ⁻`
  have hw : ∀ ν : Measure (ℂ × ℝ),
      ((ν.withDensity fun q => ENNReal.ofReal q.2).map
        (fun q : ℂ × ℝ => (!₂[q.1.re, q.1.im, -q.2, 0] : EuclideanSpace ℝ (Fin 4)))).map
        (fun Z : EuclideanSpace ℝ (Fin 4) => ((Z 0 : ℂ) + (Z 1 : ℂ) * Complex.I, -Z 2)) =
      ν.withDensity fun q => ENNReal.ofReal q.2 := by
    intro ν
    rw [Measure.map_map hgc.measurable s10_inj_cont.measurable]
    have hid : ((fun Z : EuclideanSpace ℝ (Fin 4) => ((Z 0 : ℂ) + (Z 1 : ℂ) * Complex.I, -Z 2)) ∘
        fun q : ℂ × ℝ => (!₂[q.1.re, q.1.im, -q.2, 0] : EuclideanSpace ℝ (Fin 4))) = id :=
      funext hgι
    rw [hid, Measure.map_id]
  have hξ : (μp.withDensity fun q => ENNReal.ofReal q.2) =
      μm.withDensity fun q => ENNReal.ofReal q.2 := by
    rw [← hw μp, ← hw μm, h]
  -- `ξ > 0` on `ℍ³`: divide by `ξ`
  have hf : Measurable fun q : ℂ × ℝ => ENNReal.ofReal q.2 := by fun_prop
  have hg : Measurable fun q : ℂ × ℝ => (ENNReal.ofReal q.2)⁻¹ := by fun_prop
  have hback : ∀ ν : Measure (ℂ × ℝ), ν UHSᶜ = 0 →
      (ν.withDensity fun q => ENNReal.ofReal q.2).withDensity
        (fun q => (ENNReal.ofReal q.2)⁻¹) = ν := by
    intro ν hν
    rw [← withDensity_mul ν hf hg]
    refine (withDensity_congr_ae ((s10_inj_ae ν hν).mono fun q hq => ?_)).trans withDensity_one
    have hq' : 0 < q.2 := hq
    exact ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hq').ne' ENNReal.ofReal_ne_top
  rw [← hback μp hp, ← hback μm hm, hξ]

/-- **Theorem 10.17**, `thm:injective`, `sec10-sharp.tex:906`: positive Borel measures `μ⁺, μ⁻` on
`ℍ³` with `𝒯μ^±(P₀) < ∞` for some `P₀`, and `𝒯μ⁺ = 𝒯μ⁻` on a nonempty open set, are equal. -/
theorem thm_injective (μp μm : Measure (ℂ × ℝ)) (hp : μp UHSᶜ = 0) (hm : μm UHSᶜ = 0)
    (P₀ : ℂ × ℝ) (hP₀ : P₀ ∈ UHS) (h₁ : kernelTransform μp P₀ < ⊤)
    (h₂ : kernelTransform μm P₀ < ⊤) (O : Set (ℂ × ℝ)) (hO : IsOpen O) (hOne : O.Nonempty)
    (hOU : O ⊆ UHS) (heq : ∀ P ∈ O, kernelTransform μp P = kernelTransform μm P) :
    μp = μm := by
  have hfp := s10_inj_finite μp hp P₀ hP₀ h₁
  have hfm := s10_inj_finite μm hm P₀ hP₀ h₂
  have hmp := s10_inj_mass μp hp hfp
  have hmm := s10_inj_mass μm hm hfm
  obtain ⟨Up, hUp⟩ : ∃ U : EuclideanSpace ℝ (Fin 4) → ℝ≥0∞, ∀ Z, U Z =
      ∫⁻ q, ENNReal.ofReal (q.2 / ‖Z - !₂[q.1.re, q.1.im, -q.2, 0]‖ ^ 2) ∂μp := ⟨_, fun _ => rfl⟩
  obtain ⟨Um, hUm⟩ : ∃ U : EuclideanSpace ℝ (Fin 4) → ℝ≥0∞, ∀ Z, U Z =
      ∫⁻ q, ENNReal.ofReal (q.2 / ‖Z - !₂[q.1.re, q.1.im, -q.2, 0]‖ ^ 2) ∂μm := ⟨_, fun _ => rfl⟩
  -- Step 3: `𝒰⁺ - 𝒰⁻` is harmonic off `Π₋`, even in `a`, and zero on `O × {0}`, so zero off `Π₋`
  have hV := s10_inj_uc (fun Z => (Up Z).toReal - (Um Z).toReal)
    ((s10_inj_harm μp hp hmp Up hUp).sub (s10_inj_harm μm hm hmm Um hUm))
    (fun Z => by simp only [s10_inj_even μp Up hUp Z, s10_inj_even μm Um hUm Z])
    O hO hOne hOU (fun P hP => by
      have h1 := s10_inj_eval μp hp P (hOU hP) Up hUp
      have h2 := s10_inj_eval μm hm P (hOU hP) Um hUm
      have h4 : ENNReal.ofReal (4 * P.2) ≠ 0 := by
        have h5 : (0 : ℝ) < P.2 := hOU hP
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        linarith
      have h6 := (ENNReal.mul_right_inj h4 ENNReal.ofReal_ne_top).mp
        (h1.symm.trans ((heq P hP).trans h2))
      simp only [h6, sub_self])
  -- Step 4: `𝒰⁺ = 𝒰⁻` a.e., hence `∫ φ ∘ ι ξ dμ⁺ = ∫ φ ∘ ι ξ dμ⁻`
  have hae : ∀ᵐ Z ∂(volume : Measure (EuclideanSpace ℝ (Fin 4))),
      (Up Z).toReal = (Um Z).toReal := by
    refine ae_iff.mpr (measure_mono_null (fun Z hZ => ?_) s10_inj_null)
    by_contra h3
    exact hZ (sub_eq_zero.mp (hV Z fun h => h3 h.1))
  have hint : ∀ φ : EuclideanSpace ℝ (Fin 4) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ q, φ !₂[q.1.re, q.1.im, -q.2, 0] * q.2 ∂μp =
        ∫ q, φ !₂[q.1.re, q.1.im, -q.2, 0] * q.2 ∂μm := by
    intro φ hφ hc
    have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
    have e1 := s10_inj_green μp hp hmp Up hUp φ h2 hc
    have e2 := s10_inj_green μm hm hmm Um hUm φ h2 hc
    have e3 : ∫ Z, Laplacian.laplacian φ Z * (Up Z).toReal =
        ∫ Z, Laplacian.laplacian φ Z * (Um Z).toReal :=
      integral_congr_ae (hae.mono fun Z hZ => by simp only [hZ])
    have hπ : -(4 * π ^ 2) ≠ 0 := neg_ne_zero.mpr (by positivity)
    exact mul_left_cancel₀ hπ (e1.symm.trans (e3.trans e2))
  -- the lifted measures agree, and pull back
  have := s10_inj_locfin μp hp hmp
  have := s10_inj_locfin μm hm hmm
  refine s10_inj_pullback μp μm hp hm (s10_inj_ext _ _ fun φ hφ hc => ?_)
  rw [s10_inj_integral μp hp hmp φ hφ.continuous hc, s10_inj_integral μm hm hmm φ hφ.continuous hc]
  exact hint φ hφ hc

/-! ## §10.8 Proof of Theorem 10.4, part 2 (`subsec:proof-D`, `sec10-sharp.tex:1004`) -/

/-- Helper for `s10_rigidity_part2`: the gap `𝒩 = ℍ³ ∖ (U ∪ U*)` of a Jordan pair is open
(`lem_proper_closed` on both sides). -/
theorem s10_rp2_gap_open {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) : IsOpen (gap Ω Ωs) := by
  have h1 := lem_proper_closed hJ
  have h2 := lem_proper_closed (s02_jordanPair_symm hJ)
  have e : gap Ω Ωs = UHS ∩ ((closure (horoUnion Ω))ᶜ ∩ (closure (horoUnion Ωs))ᶜ) := by
    ext q
    show q ∈ UHS \ (horoUnion Ω ∪ horoUnion Ωs) ↔ _
    constructor
    · rintro ⟨hq, hq'⟩
      refine ⟨hq, fun hc => hq' (Or.inl ?_), fun hc => hq' (Or.inr ?_)⟩
      · rw [← h1]
        exact ⟨hc, hq⟩
      · rw [← h2]
        exact ⟨hc, hq⟩
    · rintro ⟨hq, hc1, hc2⟩
      refine ⟨hq, ?_⟩
      rintro (h | h)
      · exact hc1 (subset_closure h)
      · exact hc2 (subset_closure h)
  rw [e]
  exact s09_isOpen_UHS.inter (isClosed_closure.isOpen_compl.inter isClosed_closure.isOpen_compl)

/-- Helper for `s10_rigidity_part2`: `X(w) = E(w, 0)` lies on its own horoball `B_w`, so
`X(Ω) ⊆ U` (the Epstein surface does not meet the gap). -/
theorem s10_rp2_epstein_mem {Ω : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    {w : ℂ} (hw : w ∈ Ω) : epstein Ω w ∈ horoUnion Ω := by
  have hl := s02_poincareDensity_pos hΩ hw
  show epstein Ω w ∈ ⋃ w' ∈ Ω, horoball Ω w'
  refine mem_iUnion₂.mpr ⟨w, hw, ?_⟩
  show epstein Ω w ∈ UHS ∧ horoPhi Ω (epstein Ω w) w ≤ 1
  rw [← s02_normalGeod_zero Ω w hl]
  exact ⟨s02_normalGeod_pos Ω w hl 0, by rw [s02_horoPhi_normalGeod Ω w hl 0, Real.exp_zero]⟩

/-- Helper for `s10_rigidity_part2`: `Ren(P) = 0` with `H(P) < ∞` means `V(P) = H(P)/2`. -/
theorem s10_rp2_ren {Ω Ωs : Set ℂ} {P : ℂ × ℝ} (hH : ambH Ω Ωs P < ⊤) (h : ren Ω Ωs P = 0) :
    ambV Ω Ωs P = ambH Ω Ωs P / 2 := by
  have hb : ambH Ω Ωs P / 2 ≠ ⊤ := ENNReal.div_ne_top hH.ne two_ne_zero
  have h' : (ambV Ω Ωs P : EReal) - ((ambH Ω Ωs P / 2 : ℝ≥0∞) : EReal) = 0 := h
  rw [← EReal.coe_ennreal_toReal hb] at h'
  rcases eq_or_ne (ambV Ω Ωs P) ⊤ with hV | hV
  · rw [hV, EReal.coe_ennreal_top, EReal.top_sub_coe] at h'
    exact absurd h' EReal.top_ne_zero
  · rw [← EReal.coe_ennreal_toReal hV, ← EReal.coe_sub, EReal.coe_eq_zero, sub_eq_zero] at h'
    exact (ENNReal.toReal_eq_toReal_iff' hV hb).mp h'

/-- Helper for `s10_rigidity_part2`: `H = 𝒯μ_H` for `μ_H = X_*(s² dâ) + X*_*(s*² dâ*)`. -/
theorem s10_rp2_TH {Ω Ωs : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    (hΩs : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ωs) (P : ℂ × ℝ) :
    kernelTransform ((curvMass Ω).map (epstein Ω) + (curvMass Ωs).map (epstein Ωs)) P =
      ambH Ω Ωs P := by
  have hm := (s09_bx_measurable_ambKernel P).ennreal_ofReal
  show ∫⁻ q, ENNReal.ofReal (ambKernel P q) ∂((curvMass Ω).map (epstein Ω) +
    (curvMass Ωs).map (epstein Ωs)) = _
  rw [lintegral_add_measure, lintegral_map' hm.aemeasurable (s09_bx_epstein_aemeas hΩ),
    lintegral_map' hm.aemeasurable (s09_bx_epstein_aemeas hΩs)]
  rfl

/-- Helper for `s10_rigidity_part2`: `μ_H` is carried by `ℍ³`. -/
theorem s10_rp2_muH_UHS {Ω Ωs : Set ℂ} (hΩ : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω)
    (hΩs : ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ωs) :
    ((curvMass Ω).map (epstein Ω) + (curvMass Ωs).map (epstein Ωs)) UHSᶜ = 0 := by
  have hc : MeasurableSet UHSᶜ := s09_isOpen_UHS.measurableSet.compl
  have h1 : curvMass Ω (epstein Ω ⁻¹' UHSᶜ) = 0 := ae_iff.mp (s09_bx_epstein_ae_UHS hΩ)
  have h2 : curvMass Ωs (epstein Ωs ⁻¹' UHSᶜ) = 0 := ae_iff.mp (s09_bx_epstein_ae_UHS hΩs)
  rw [Measure.add_apply, Measure.map_apply_of_aemeasurable (s09_bx_epstein_aemeas hΩ) hc,
    Measure.map_apply_of_aemeasurable (s09_bx_epstein_aemeas hΩs) hc, h1, h2, add_zero]

/-- Helper for `s10_rigidity_part2`: `μ_H(𝒩) = 0`, since `μ_H` is carried by `Σ ∪ Σ*` and
`Σ = X(Ω) ⊆ U`, `Σ* ⊆ U*` (`s10_rp2_epstein_mem`). -/
theorem s10_rp2_muH_gap {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) :
    ((curvMass Ω).map (epstein Ω) + (curvMass Ωs).map (epstein Ωs)) (gap Ω Ωs) = 0 := by
  have hΩ := s02_jordanPair_riemannMap hJ
  have hΩs := s02_jordanPair_riemannMap (s02_jordanPair_symm hJ)
  have hg := (s10_rp2_gap_open hJ).measurableSet
  have hnull : ∀ {Ω' : Set ℂ}, (∃ f : ℂ → ℂ, IsConformalOnto f unitDisc Ω') →
      curvMass Ω' Ω'ᶜ = 0 := by
    intro Ω' hΩ'
    have ho : IsOpen Ω' := by
      obtain ⟨f, hf⟩ := hΩ'
      exact hf.isOpen isOpen_ball
    refine s09_bx_curvMass_ac Ω' ?_
    rw [Measure.restrict_apply ho.measurableSet.compl, compl_inter_self, measure_empty]
  have e1 : curvMass Ω (epstein Ω ⁻¹' gap Ω Ωs) = 0 := by
    refine measure_mono_null ?_ (hnull hΩ)
    intro w hw hwΩ
    have hw' : epstein Ω w ∈ UHS \ (horoUnion Ω ∪ horoUnion Ωs) := hw
    exact hw'.2 (Or.inl (s10_rp2_epstein_mem hΩ hwΩ))
  have e2 : curvMass Ωs (epstein Ωs ⁻¹' gap Ω Ωs) = 0 := by
    refine measure_mono_null ?_ (hnull hΩs)
    intro w hw hwΩ
    have hw' : epstein Ωs w ∈ UHS \ (horoUnion Ω ∪ horoUnion Ωs) := hw
    exact hw'.2 (Or.inr (s10_rp2_epstein_mem hΩs hwΩ))
  rw [Measure.add_apply, Measure.map_apply_of_aemeasurable (s09_bx_epstein_aemeas hΩ) hg,
    Measure.map_apply_of_aemeasurable (s09_bx_epstein_aemeas hΩs) hg, e1, e2, add_zero]

/-- Helper for `s10_rigidity_part2` (`sec10-sharp.tex:1038`, "`s ≡ 0` on `Ω`"): if the
curvature mass `s² dâ` of `Ω = f(𝔻)` vanishes, then `S_f ≡ 0` on `𝔻` (`s²λ²` is continuous on
`Ω`, `λ > 0`, and (2.4) `eq_s_disk`). -/
theorem s10_rp2_schwarz_zero {Ω : Set ℂ} {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω)
    (h0 : curvMass Ω = 0) : ∀ z ∈ unitDisc, schwarzianHol f z = 0 := by
  intro z₀ hz₀
  by_contra hne
  have hD : IsOpen unitDisc := isOpen_ball
  have hfa : ∀ z ∈ unitDisc, AnalyticAt ℂ f z := fun z hz => hf.1.analyticAt (hD.mem_nhds hz)
  have hd0 : ∀ z ∈ unitDisc, deriv f z ≠ 0 := fun z hz => deriv_ne_zero_of_injOn hD hf.1 hf.2.1 hz
  -- `S_f` and `f'` are continuous at `z₀`
  have h1 : AnalyticAt ℂ (deriv f) z₀ := (hfa z₀ hz₀).deriv
  have h2 : AnalyticAt ℂ (deriv (deriv f)) z₀ := h1.deriv
  have hq : AnalyticAt ℂ (fun w => deriv (deriv f) w / deriv f w) z₀ := h2.div h1 (hd0 z₀ hz₀)
  have hSc : ContinuousAt (schwarzianHol f) z₀ := by
    show ContinuousAt (fun z => deriv (fun w => deriv (deriv f) w / deriv f w) z -
      (1 / 2) * (deriv (deriv f) z / deriv f z) ^ 2) z₀
    exact hq.deriv.continuousAt.sub (continuousAt_const.mul (hq.continuousAt.pow 2))
  -- `g(z) = (s²λ²)(f z) = |S_f(z)|² (1-|z|²)² / (4|f'(z)|²)` is continuous and positive at `z₀`
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℝ,
      g = fun z => ‖schwarzianHol f z‖ ^ 2 * (1 - ‖z‖ ^ 2) ^ 2 / (4 * ‖deriv f z‖ ^ 2) :=
    ⟨_, rfl⟩
  have hgc : ContinuousAt g z₀ := by
    rw [hg]
    exact ((hSc.norm.pow 2).mul ((continuousAt_const.sub
      (continuous_norm.continuousAt.pow 2)).pow 2)).div
      (continuousAt_const.mul (h1.continuousAt.norm.pow 2))
      (mul_ne_zero four_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hd0 z₀ hz₀))))
  have hr1 : (0 : ℝ) < 1 - ‖z₀‖ ^ 2 := by
    have := mem_ball_zero_iff.mp hz₀
    nlinarith [norm_nonneg z₀]
  have hg0 : 0 < g z₀ := by
    simp only [hg]
    exact div_pos (mul_pos (pow_pos (norm_pos_iff.mpr hne) 2) (pow_pos hr1 2))
      (mul_pos four_pos (pow_pos (norm_pos_iff.mpr (hd0 z₀ hz₀)) 2))
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ball z₀ r ⊆ unitDisc ∩ {z | g z₀ / 2 < g z} :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem (hD.mem_nhds hz₀)
      (hgc.eventually (lt_mem_nhds (half_lt_self hg0))))
  have hBD : ball z₀ r ⊆ unitDisc := fun z hz => (hball hz).1
  -- `V = f(B(z₀, r))` is open, nonempty, inside `Ω`, and `s²λ² ≥ g(z₀)/2` on it
  have hVo : IsOpen (f '' ball z₀ r) :=
    (show IsConformalOnto f (ball z₀ r) (f '' ball z₀ r) from
      ⟨hf.1.mono hBD, hf.2.1.mono hBD, rfl⟩).isOpen isOpen_ball
  have hVΩ : f '' ball z₀ r ⊆ Ω := by
    rw [← hf.2.2]
    exact image_mono hBD
  have hVpos : 0 < volume (f '' ball z₀ r) :=
    hVo.measure_pos volume ⟨f z₀, mem_image_of_mem f (mem_ball_self hr)⟩
  have hρ : ∀ w ∈ f '' ball z₀ r, ENNReal.ofReal (g z₀ / 2) ≤
      ENNReal.ofReal (schwarzNorm Ω w ^ 2 * poincareDensity Ω w ^ 2) := by
    rintro w ⟨z, hz, rfl⟩
    refine ENNReal.ofReal_le_ofReal ?_
    have hzD := hBD hz
    have hp := s02_pullback_density hf hzD
    rw [schwarzian_of_analyticAt (hfa z hzD)] at hp
    have hn : 0 < 4 * ‖deriv f z‖ ^ 2 :=
      mul_pos four_pos (pow_pos (norm_pos_iff.mpr (hd0 z hzD)) 2)
    have e : g z = schwarzNorm Ω (f z) ^ 2 * poincareDensity Ω (f z) ^ 2 := by
      simp only [hg]
      rw [div_eq_iff hn.ne']
      linear_combination (-4) * hp
    have hlt : g z₀ / 2 < g z := (hball hz).2
    rw [← e]
    exact hlt.le
  have hm : MeasurableSet (f '' ball z₀ r) := hVo.measurableSet
  have hpos : 0 < curvMass Ω (f '' ball z₀ r) := by
    show 0 < ((volume.restrict Ω).withDensity fun w =>
      ENNReal.ofReal (schwarzNorm Ω w ^ 2 * poincareDensity Ω w ^ 2)) (f '' ball z₀ r)
    rw [withDensity_apply _ hm]
    calc (0 : ℝ≥0∞) < ENNReal.ofReal (g z₀ / 2) * volume (f '' ball z₀ r) :=
          ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (half_pos hg0)).ne' hVpos.ne'
      _ = ∫⁻ w in f '' ball z₀ r, ENNReal.ofReal (g z₀ / 2) ∂(volume.restrict Ω) := by
          rw [setLIntegral_const, Measure.restrict_apply hm, inter_eq_left.mpr hVΩ]
      _ ≤ _ := setLIntegral_mono' hm hρ
  rw [h0, Measure.coe_zero, Pi.zero_apply] at hpos
  exact lt_irrefl _ hpos

/-- Helper for `s10_rigidity_part2`: `S_{id} = 0`. -/
theorem s10_rp2_schwarzianHol_id (z : ℂ) : schwarzianHol id z = 0 := by
  show deriv (fun w => deriv (deriv id) w / deriv id w) z -
    (1 / 2) * (deriv (deriv id) z / deriv id z) ^ 2 = 0
  simp [deriv_id']

/-- Helper for `s10_rigidity_part2` (Step 5 of `thm:sharp`, `sec10-sharp.tex:889`): the image of
`𝔻` under a Möbius map `z ↦ (az+b)/(cz+d)` whose pole `p = -d/c` lies on `∂𝔻` is an open
half-plane `{0 < Im(αw + β)}`. -/
theorem s10_rp2_half {f : ℂ → ℂ} {Ω : Set ℂ} (hf : f '' unitDisc = Ω) {a b c d : ℂ}
    (hdet : a * d - b * c ≠ 0) (hc : c ≠ 0) {p : ℂ} (hp : ‖p‖ = 1) (hpole : c * p + d = 0)
    (hfz : ∀ z ∈ unitDisc, c * z + d ≠ 0 ∧ f z = (a * z + b) / (c * z + d)) :
    ∃ α β : ℂ, α ≠ 0 ∧ ∀ w, w ∈ Ω ↔ 0 < (α * w + β).im := by
  have hnd : Complex.normSq d = Complex.normSq c := by
    rw [show d = -(c * p) by linear_combination hpole, Complex.normSq_neg, Complex.normSq_mul,
      Complex.normSq_eq_norm_sq p, hp]
    ring
  -- `w ∈ Ω ↔ |dw - b| < |a - cw|` (`z = (dw - b)/(a - cw)` inverts the Möbius map)
  have hchar : ∀ w, w ∈ Ω ↔ ‖d * w - b‖ < ‖a - c * w‖ := by
    intro w
    rw [← hf]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hne, hfz'⟩ := hfz z hz
      rw [hfz']
      have e1 : d * ((a * z + b) / (c * z + d)) - b = (a * d - b * c) * z / (c * z + d) := by
        rw [eq_div_iff hne, sub_mul, mul_assoc, div_mul_cancel₀ _ hne]
        ring
      have e2 : a - c * ((a * z + b) / (c * z + d)) = (a * d - b * c) / (c * z + d) := by
        rw [eq_div_iff hne, sub_mul, mul_assoc, div_mul_cancel₀ _ hne]
        ring
      rw [e1, e2, norm_div, norm_div, norm_mul,
        div_lt_div_iff_of_pos_right (norm_pos_iff.mpr hne)]
      calc ‖a * d - b * c‖ * ‖z‖ < ‖a * d - b * c‖ * 1 :=
            mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hz) (norm_pos_iff.mpr hdet)
        _ = _ := mul_one _
    · intro hlt
      have hne : a - c * w ≠ 0 := by
        intro h
        rw [h, norm_zero] at hlt
        exact absurd hlt (not_lt.mpr (norm_nonneg _))
      have hz : (d * w - b) / (a - c * w) ∈ unitDisc := by
        refine mem_ball_zero_iff.mpr ?_
        rw [norm_div]
        exact (div_lt_one (norm_pos_iff.mpr hne)).mpr hlt
      refine ⟨_, hz, ?_⟩
      rw [(hfz _ hz).2]
      have e : c * ((d * w - b) / (a - c * w)) + d = (a * d - b * c) / (a - c * w) := by
        rw [eq_div_iff hne, add_mul, mul_assoc, div_mul_cancel₀ _ hne]
        ring
      rw [e, div_eq_iff (div_ne_zero hdet hne), mul_div_assoc', mul_div_assoc',
        div_add' _ _ _ hne, div_left_inj' hne]
      ring
  -- `|a - cw|² - |dw - b|² = Im(αw + β)`, linear in `w` since `|d| = |c|`
  obtain ⟨α, hα⟩ : ∃ α : ℂ, α = -2 * I * (c * conj a - d * conj b) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℂ, β = I * ((Complex.normSq a - Complex.normSq b : ℝ) : ℂ) := ⟨_, rfl⟩
  have key : ∀ w, Complex.normSq (a - c * w) - Complex.normSq (d * w - b) = (α * w + β).im := by
    intro w
    rw [Complex.normSq_apply, Complex.normSq_apply] at hnd
    rw [hα, hβ]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.add_im, Complex.I_re, Complex.I_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
      Complex.neg_im]
    norm_num
    linear_combination (-(w.re * w.re + w.im * w.im)) * hnd
  have hchar' : ∀ w, w ∈ Ω ↔ 0 < (α * w + β).im := by
    intro w
    rw [hchar, ← pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero,
      Complex.sq_norm, Complex.sq_norm, ← sub_pos, key w]
  refine ⟨α, β, ?_, hchar'⟩
  -- `α = 0` would make `Ω` empty or all of `ℂ`; but `f 0 ∈ Ω` and `a/c ∉ Ω`
  intro hα0
  have h0 : f 0 ∈ Ω := hf ▸ mem_image_of_mem f (mem_ball_self one_pos)
  have hac : a / c ∈ Ω := by
    rw [hchar']
    have := (hchar' (f 0)).mp h0
    rw [hα0, zero_mul, zero_add] at this ⊢
    exact this
  have := (hchar (a / c)).mp hac
  rw [mul_div_cancel₀ a hc, sub_self, norm_zero] at this
  exact absurd this (not_lt.mpr (norm_nonneg _))

/-- Helper for `s10_rigidity_part2`: if `Ω` is an open half-plane `{0 < Im(αw + β)}` of a Jordan
pair through `∞`, then `Ω* = {Im(αw + β) < 0}` and `Γ` is a circle (the closure argument of
`s02_teo_eq_line`). -/
theorem s10_rp2_half_line {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {α β : ℂ} (hα : α ≠ 0)
    (hΩ : ∀ w, w ∈ Ω ↔ 0 < (α * w + β).im) : IsLinePair Ω Ωs := by
  have hd := s02_jordanPair_disjoint hJ
  have hΩso : IsOpen Ωs := by
    obtain ⟨F, -, hFΩs⟩ := hJ
    rw [← hFΩs]
    exact F.isOpenMap _ (isOpen_lt Complex.continuous_im continuous_const)
  have hcont : Continuous fun w : ℂ => (α * w + β).im :=
    Complex.continuous_im.comp ((continuous_const.mul continuous_id).add continuous_const)
  have hn : 0 < ‖α‖ := norm_pos_iff.mpr hα
  refine ⟨α, β, hα, Set.ext hΩ, ?_⟩
  ext w
  show w ∈ Ωs ↔ (α * w + β).im < 0
  constructor
  · intro hw
    by_contra hge
    push Not at hge
    obtain ⟨ε, hε, hεb⟩ := Metric.isOpen_iff.mp hΩso w hw
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ε / (2 * ‖α‖) := ⟨_, rfl⟩
    have hr0 : 0 < r := by rw [hr]; positivity
    have hw' : w + (r : ℂ) * (I * conj α) ∈ Ωs := by
      refine hεb ?_
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_I,
        one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, Complex.norm_conj, hr]
      rw [show ε / (2 * ‖α‖) * ‖α‖ = ε / 2 by field_simp]
      linarith
    have hwΩ : w + (r : ℂ) * (I * conj α) ∈ Ω := by
      rw [hΩ]
      have e : α * (w + (r : ℂ) * (I * conj α)) + β =
          (α * w + β) + (r : ℂ) * I * (α * conj α) := by ring
      rw [e, Complex.mul_conj, Complex.add_im]
      have e2 : ((r : ℂ) * I * (Complex.normSq α : ℂ)).im = r * Complex.normSq α := by simp
      rw [e2]
      have : 0 < Complex.normSq α := Complex.normSq_pos.mpr hα
      nlinarith
    exact Set.disjoint_left.mp hd hwΩ hw'
  · intro hlt
    by_contra hw
    have hwΩ : w ∉ Ω := fun h => by
      have := (hΩ w).mp h
      linarith
    have hcl := s02_jordanPair_closure hJ hwΩ hw
    have hsub : closure Ω ⊆ {w | 0 ≤ (α * w + β).im} :=
      closure_minimal (fun x hx => le_of_lt ((hΩ x).mp hx)) (isClosed_le continuous_const hcont)
    have := hsub hcl
    simp only [mem_ofPred_eq] at this
    linarith

/-- Helper for `s10_rigidity_part2` (Step 5 of `thm:sharp`, `sec10-sharp.tex:889`): if `S_f ≡ 0`
for a Riemann map `f : 𝔻 → Ω` of a Jordan pair through `∞`, then `Γ` is a circle: `f` is Möbius
(`s10_aw_mob` with `g = id`), its pole lies on `∂𝔻` as `Ω` is unbounded (`s10_aw_pole`), so `Ω`
is a half-plane (`s10_rp2_half`, `s10_rp2_half_line`). -/
theorem s10_rp2_line {Ω Ωs : Set ℂ} (hJ : IsJordanPair Ω Ωs) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) (hS : ∀ z ∈ unitDisc, schwarzianHol f z = 0) :
    IsLinePair Ω Ωs := by
  have hid : ∀ z ∈ unitDisc, schwarzianHol f z = schwarzianHol id z := fun z hz => by
    rw [hS z hz, s10_rp2_schwarzianHol_id]
  obtain ⟨a, b, c, d, hdet, hN⟩ := s10_aw_mob hf differentiableOn_id (injOn_id _) hid
  have hW : IsKQC id univ 1 :=
    isKQC_one_of_conformal isOpen_univ ⟨differentiableOn_id, injOn_id _, image_id _⟩
  obtain ⟨hc, p, hp, hpole, hfz⟩ :=
    s10_aw_pole hW (image_id _) hdet hN hf.2.2 (s02_jordanPair_unbounded hJ).1
  obtain ⟨α, β, hα, hΩ⟩ := s10_rp2_half hf.2.2 hdet hc hp hpole hfz
  exact s10_rp2_half_line hJ hα hΩ

/-- Part 2 of `thm_rigidity`: `Ren` vanishes on a nonempty open set iff `Γ` is a circle.  `⇒`:
`thm_injective` gives `vol|_𝒩 = ½ μ_H`, so `μ_H = 0` and `s ≡ 0` (§10.8); `⇐`: part 3. -/
theorem s10_rigidity_part2 (Ω Ωs : Set ℂ) (hJ : IsJordanPair Ω Ωs) (P₀ : ℂ × ℝ) (hP₀ : P₀ ∈ UHS)
    (hH : ambH Ω Ωs P₀ < ⊤) :
    (∃ O : Set (ℂ × ℝ), IsOpen O ∧ O.Nonempty ∧ O ⊆ UHS ∧ ∀ P ∈ O, ren Ω Ωs P = 0) ↔
      IsLinePair Ω Ωs := by
  have hfin := s10_rigidity_part1 Ω Ωs P₀ hP₀ hH
  have hHP : ∀ P ∈ UHS, ambH Ω Ωs P < ⊤ := fun P hP => (hfin P hP).1
  constructor
  · rintro ⟨O, hO, hOne, hOU, hren⟩
    have hΩ := s02_jordanPair_riemannMap hJ
    have hΩs := s02_jordanPair_riemannMap (s02_jordanPair_symm hJ)
    obtain ⟨P₁, hP₁⟩ := hOne
    obtain ⟨μH, hμH⟩ : ∃ μH : Measure (ℂ × ℝ),
        μH = (curvMass Ω).map (epstein Ω) + (curvMass Ωs).map (epstein Ωs) := ⟨_, rfl⟩
    -- `μ⁺ = vol|_𝒩` and `μ⁻ = ½ μ_H`, with `𝒯μ⁺ = V` and `𝒯μ⁻ = ½ H`
    have hTp : ∀ P, kernelTransform (hvol.restrict (gap Ω Ωs)) P = ambV Ω Ωs P := fun P => rfl
    have hTm : ∀ P, kernelTransform ((1 / 2 : ℝ≥0∞) • μH) P = ambH Ω Ωs P / 2 := by
      intro P
      show ∫⁻ q, ENNReal.ofReal (ambKernel P q) ∂((1 / 2 : ℝ≥0∞) • μH) = _
      rw [lintegral_smul_measure]
      change (1 / 2 : ℝ≥0∞) * kernelTransform μH P = _
      rw [hμH, s10_rp2_TH hΩ hΩs P]
      simp only [ENNReal.div_eq_inv_mul, mul_one]
    have hp : hvol.restrict (gap Ω Ωs) UHSᶜ = 0 := by
      rw [Measure.restrict_apply s09_isOpen_UHS.measurableSet.compl]
      refine measure_mono_null (t := ∅) ?_ measure_empty
      rintro q ⟨hq1, hq2⟩
      exact hq1 (show q ∈ UHS \ (horoUnion Ω ∪ horoUnion Ωs) from hq2).1
    have hm : ((1 / 2 : ℝ≥0∞) • μH) UHSᶜ = 0 := by
      rw [Measure.smul_apply, hμH, s10_rp2_muH_UHS hΩ hΩs, smul_zero]
    have hlt : ambH Ω Ωs P₁ / 2 < ⊤ := ENNReal.div_lt_top (hHP P₁ (hOU hP₁)).ne two_ne_zero
    have h₁ : kernelTransform (hvol.restrict (gap Ω Ωs)) P₁ < ⊤ := by
      rw [hTp, s10_rp2_ren (hHP P₁ (hOU hP₁)) (hren P₁ hP₁)]
      exact hlt
    have h₂ : kernelTransform ((1 / 2 : ℝ≥0∞) • μH) P₁ < ⊤ := by
      rw [hTm]
      exact hlt
    have heq : ∀ P ∈ O, kernelTransform (hvol.restrict (gap Ω Ωs)) P =
        kernelTransform ((1 / 2 : ℝ≥0∞) • μH) P := by
      intro P hP
      rw [hTp, hTm]
      exact s10_rp2_ren (hHP P (hOU hP)) (hren P hP)
    have hinj := thm_injective _ _ hp hm P₁ (hOU hP₁) h₁ h₂ O hO ⟨P₁, hP₁⟩ hOU heq
    -- `vol(𝒩) = μ⁺(𝒩) = μ⁻(𝒩) = 0`, so `μ⁻ = μ⁺ = 0` and `∫ s² dâ = 0`
    have hg0 : ((1 / 2 : ℝ≥0∞) • μH) (gap Ω Ωs) = 0 := by
      rw [Measure.smul_apply, hμH, s10_rp2_muH_gap hJ, smul_zero]
    have hvg : hvol (gap Ω Ωs) = 0 := by
      have h := congrArg (fun μ : Measure (ℂ × ℝ) => μ (gap Ω Ωs)) hinj
      simp only [Measure.restrict_apply_self] at h
      rw [h, hg0]
    have hμ0 : (1 / 2 : ℝ≥0∞) • μH = 0 := by
      rw [← hinj]
      exact Measure.restrict_eq_zero.mpr hvg
    have hu : ((1 / 2 : ℝ≥0∞) • μH) univ = 0 := by
      rw [hμ0]
      simp
    rw [Measure.smul_apply, smul_eq_mul, hμH, Measure.add_apply,
      Measure.map_apply_of_aemeasurable (s09_bx_epstein_aemeas hΩ) MeasurableSet.univ,
      preimage_univ] at hu
    have hc : curvMass Ω = 0 :=
      Measure.measure_univ_eq_zero.mp (add_eq_zero.mp ((mul_eq_zero.mp hu).resolve_left
        (by norm_num))).1
    obtain ⟨f, hf⟩ := hΩ
    exact s10_rp2_line hJ hf (s10_rp2_schwarz_zero hf hc)
  · intro hL
    refine ⟨UHS, s09_isOpen_UHS, ⟨((0 : ℂ), (1 : ℝ)), show (0 : ℝ) < 1 from one_pos⟩, subset_rfl,
      fun P hP => (s10_rigidity_part3 Ω Ωs hJ hL P hP).2.2⟩

/-- **Theorem 10.4 (Theorem D)**, `thm:rigidity`, `sec10-sharp.tex:76`.  For a Jordan curve with
`H(P₀) < ∞` for some `P₀`: `H < ∞` everywhere, so `Ren` is defined with values in `(-∞, ∞]`;
`Ren` vanishes identically on a nonempty open set iff `Γ` is a circle; and then
`V ≡ H ≡ Ren ≡ 0`. -/
theorem thm_rigidity (Ω Ωs : Set ℂ) (hJ : IsJordanPair Ω Ωs) (P₀ : ℂ × ℝ) (hP₀ : P₀ ∈ UHS)
    (hH : ambH Ω Ωs P₀ < ⊤) :
    (∀ P ∈ UHS, ambH Ω Ωs P < ⊤ ∧ ren Ω Ωs P ≠ ⊥) ∧
    ((∃ O : Set (ℂ × ℝ), IsOpen O ∧ O.Nonempty ∧ O ⊆ UHS ∧ ∀ P ∈ O, ren Ω Ωs P = 0) ↔
      IsLinePair Ω Ωs) ∧
    (IsLinePair Ω Ωs → ∀ P ∈ UHS, ambV Ω Ωs P = 0 ∧ ambH Ω Ωs P = 0 ∧ ren Ω Ωs P = 0) := by
  exact ⟨s10_rigidity_part1 Ω Ωs P₀ hP₀ hH, s10_rigidity_part2 Ω Ωs hJ P₀ hP₀ hH,
    s10_rigidity_part3 Ω Ωs hJ⟩

/-- **Theorem D** (introduction), `sec01-intro.tex:299`; it is Theorem 10.4 (`thm_rigidity`). -/
theorem thm_D (Ω Ωs : Set ℂ) (hJ : IsJordanPair Ω Ωs) (P₀ : ℂ × ℝ) (hP₀ : P₀ ∈ UHS)
    (hH : ambH Ω Ωs P₀ < ⊤) :
    (∀ P ∈ UHS, ambH Ω Ωs P < ⊤ ∧ ren Ω Ωs P ≠ ⊥) ∧
    ((∃ O : Set (ℂ × ℝ), IsOpen O ∧ O.Nonempty ∧ O ⊆ UHS ∧ ∀ P ∈ O, ren Ω Ωs P = 0) ↔
      IsLinePair Ω Ωs) := by
  exact ⟨(thm_rigidity Ω Ωs hJ P₀ hP₀ hH).1, (thm_rigidity Ω Ωs hJ P₀ hP₀ hH).2.1⟩

end EpsteinVMO
